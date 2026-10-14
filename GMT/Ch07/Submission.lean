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

/-- **The covector `w₁♭ ∧ ⋯ ∧ wₙ♭`** (Simon Ch. 6, 1.1 with 1.4): for every `w : Fin n → ℝᴾ`
some `n`-covector `β` on `ℝᴾ` has `β(u₁, …, uₙ) = det (⟨u_a, w_b⟩)_{a,b}`.  With the row map
`p_w x = (⟨x, w_b⟩)_b`, linear since `⟨·, ·⟩` is linear in its first argument, `β⁰ = det ∘ p_w`
is alternating, and the Leibniz formula with Cauchy–Schwarz gives
`|β⁰(u)| ≤ n! ∏_b ‖w_b‖ ∏_a ‖u_a‖`, so `β⁰` is continuous. -/
theorem Submission.cbr_ci_pw_pu_inner_det_covector : ∀ (P n : ℕ) (w : Fin n → Euclid P), ∃ β : Covector (Euclid P) n, ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (w b)) := by
  intro P n w
  -- Step 1: the row map `p_w x = (⟨x, w_b⟩)_b` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x b => inner ℝ x (w b)
      map_add' := fun x y => by
        funext b
        simp [inner_add_left]
      map_smul' := fun c x => by
        funext b
        simp [real_inner_smul_left] }
  -- Step 2: `β⁰ = det ∘ p_w` is alternating, and `β⁰(u) = det (⟨u_a, w_b⟩)_{a,b}`
  let β₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  have hβ₀ : ∀ u : Fin n → Euclid P,
      β₀ u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (w b)) := fun u => rfl
  -- Step 3: the Leibniz formula, `|sign σ| = 1`, Cauchy–Schwarz, reindexing along `σ` and
  -- `n!` permutations give `|β⁰(u)| ≤ (n! ∏_b ‖w_b‖) ∏_a ‖u_a‖`
  have hbound : ∀ u : Fin n → Euclid P,
      ‖β₀ u‖ ≤ ((n.factorial : ℝ) * ∏ b, ‖w b‖) * ∏ a, ‖u a‖ := by
    intro u
    rw [hβ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ i, Matrix.of (fun a b => inner ℝ (u a) (w b)) (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ i, Matrix.of (fun a b => inner ℝ (u a) (w b)) (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), (∏ a, ‖u a‖) * ∏ b, ‖w b‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ i, Matrix.of (fun a b => inner ℝ (u a) (w b)) (σ i) i| =
              ∏ i, |inner ℝ (u (σ i)) (w i)| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          calc |Equiv.Perm.sign σ • ∏ i, Matrix.of (fun a b => inner ℝ (u a) (w b)) (σ i) i|
              = ∏ i, |inner ℝ (u (σ i)) (w i)| := hσ
            _ ≤ ∏ i, ‖u (σ i)‖ * ‖w i‖ := by
                gcongr with i
                exact abs_real_inner_le_norm (u (σ i)) (w i)
            _ = (∏ i, ‖u (σ i)‖) * ∏ i, ‖w i‖ := Finset.prod_mul_distrib
            _ = (∏ a, ‖u a‖) * ∏ b, ‖w b‖ := by
                rw [Equiv.prod_comp σ fun a => ‖u a‖]
      _ = ((n.factorial : ℝ) * ∏ b, ‖w b‖) * ∏ a, ‖u a‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  -- Step 4: `β = β⁰.mkContinuous (n! ∏_b ‖w_b‖)` is an `n`-covector with the values of `β⁰`
  exact ⟨β₀.mkContinuous _ hbound, hβ₀⟩
/-- Orthonormal frames `x`, `y` in `ℝᴾ` with `det(⟨x a, w b⟩) = det(⟨y a, w b⟩)` for every frame
`w` satisfy `span y ⊆ span x`.  For each `i` the residual `e = y i - ∑ j, ⟨x j, y i⟩ • x j` is
orthogonal to every `x a`.  Test the hypothesis on `w = update y i e`: `(⟨x a, w b⟩)` has zero
column `i`, while `(⟨y a, w b⟩)` is the identity with column `i` replaced by `(⟨y a, e⟩)ₐ`, of
determinant `⟨y i, e⟩` by Cramer's rule.  Hence `⟨y i, e⟩ = 0`, so `⟨e, e⟩ = 0`, `e = 0` and
`y i ∈ span x`. -/
theorem Submission.cbr_ci_pw_pu_span_le_of_inner_det_eq : ∀ (P n : ℕ) (x y : Fin n → Euclid P), Orthonormal ℝ x → Orthonormal ℝ y → (∀ w : Fin n → Euclid P, Matrix.det (Matrix.of fun a b => inner ℝ (x a) (w b)) = Matrix.det (Matrix.of fun a b => inner ℝ (y a) (w b))) → Submodule.span ℝ (Set.range y) ≤ Submodule.span ℝ (Set.range x) := by
  intro P n x y hx hy hdet
  -- step 1: it suffices to show `y i ∈ span x` for every index `i`
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  -- step 2: the residual `e = y i - ∑ j, ⟨x j, y i⟩ • x j` is orthogonal to every `x a`
  obtain ⟨e, he⟩ : ∃ e : Euclid P, e = y i - ∑ j, inner ℝ (x j) (y i) • x j := ⟨_, rfl⟩
  have hxe : ∀ a, inner ℝ (x a) e = 0 := fun a => by
    rw [he, inner_sub_right, hx.inner_right_fintype, sub_self]
  -- step 3: test the hypothesis on the frame `w = update y i e`
  -- (a) column `i` of `(⟨x a, w b⟩)` vanishes, so its determinant is `0`
  have hxdet : Matrix.det (Matrix.of fun a b => inner ℝ (x a) (update y i e b)) = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero i fun a => by
      rw [Matrix.of_apply, update_self, hxe a]
  -- (b) `(⟨y a, w b⟩)` is the identity matrix with column `i` replaced by `(⟨y a, e⟩)ₐ`,
  -- so by Cramer's rule its determinant is `⟨y i, e⟩`
  have hydet : Matrix.det (Matrix.of fun a b => inner ℝ (y a) (update y i e b)) =
      inner ℝ (y i) e := by
    have hG : (Matrix.of fun a b => inner ℝ (y a) (update y i e b)) =
        (1 : Matrix (Fin n) (Fin n) ℝ).updateCol i fun a => inner ℝ (y a) e := by
      ext a b
      rw [Matrix.of_apply, Matrix.updateCol_apply]
      by_cases hb : b = i
      · rw [hb, update_self, ite_eq_left rfl]
      · rw [update_of_ne hb, ite_eq_right hb, Matrix.one_apply, orthonormal_iff_ite.mp hy]
    rw [hG, ← Matrix.cramer_apply, Matrix.cramer_one, Module.End.one_apply]
  -- (c) the hypothesis gives `⟨y i, e⟩ = 0`
  have hye : inner ℝ (y i) e = 0 := by
    rw [← hydet, ← hdet, hxdet]
  -- step 4: `⟨e, e⟩ = ⟨y i, e⟩ - ∑ j, ⟨x j, y i⟩ ⟨x j, e⟩ = 0`, so `e = 0`
  have hee : inner ℝ e e = 0 := by
    calc inner ℝ e e = inner ℝ (y i - ∑ j, inner ℝ (x j) (y i) • x j) e := by rw [← he]
      _ = 0 := by
        rw [inner_sub_left, sum_inner, hye]
        simp only [real_inner_smul_left, hxe, mul_zero, Finset.sum_const_zero, sub_zero]
  have hyi : y i = ∑ j, inner ℝ (x j) (y i) • x j := by
    rw [← sub_eq_zero, ← he]
    exact inner_self_eq_zero.mp hee
  -- step 5: `y i` is a linear combination of the `x j`, hence lies in `span x`
  rw [SetLike.mem_coe, hyi]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
/-- **Subsequence criterion for an approximate tangent plane** (Simon Ch. 3, Definition 1.4).
If `dim Q = n` and every sequence `λᵢ ↓ 0` (`λᵢ > 0`) has a subsequence along which
`∫_{η_{a,λ} M} f dHⁿ → ∫_Q f dHⁿ` for all `f ∈ C_c(ℝᴾ)`, then `TₐM = Q`.  The filter `𝓝[>] 0` is
countably generated, so convergence along it may be tested on sequences `r_j → 0⁺`; such a
sequence is positive from some `j₀` on, and the hypothesis applied to `λᵢ = r_{i+j₀}` yields the
subsequence `k ↦ φ(k) + j₀` of `r`. -/
theorem Submission.dmcbr_ci_pw_approxTangent_of_subseq : ∀ (P n : ℕ) (M : Set (Euclid P)) (a : Euclid P) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → (∀ lams : ℕ → ℝ, (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M, f y ∂μHE[n]) atTop (𝓝 (∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]))) → HasApproximateTangentSpaceAt n M a Q := by
  intro P n M a Q hQ hsub
  -- Step 1: `dim Q = n` is given; fix `f ∈ C_c(ℝᴾ)`
  refine ⟨hQ, fun f => ?_⟩
  -- Step 2: `𝓝[>] 0` is countably generated, so it suffices to treat sequences `r_j → 0⁺`
  refine tendsto_of_subseq_tendsto fun r hr => ?_
  -- Step 3: `r_j > 0` for `j ≥ j₀`, and `r_j → 0` in `ℝ`
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hr.eventually self_mem_nhdsWithin)
  have hpos : ∀ i, 0 < r (i + j₀) := fun i => hj₀ (i + j₀) (Nat.le_add_left j₀ i)
  have hlim : Tendsto (fun i => r (i + j₀)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat j₀).2 (tendsto_nhds_of_tendsto_nhdsWithin hr)
  -- Step 4: the hypothesis for `λᵢ = r_{i+j₀}` gives `φ`, applied to `f`
  obtain ⟨φ, -, hφ⟩ := hsub (fun i => r (i + j₀)) hpos hlim
  -- Step 5: `k ↦ φ(k) + j₀` is the required subsequence of `r`
  exact ⟨fun k => φ k + j₀, hφ f f.continuous f.hasCompactSupport⟩
/-- **Lower density of the weight of a constant-orientation cycle with the integer slice
property.**  Let `C = θ₀ ζ₀ ν` (`θ₀ > 0`, `|ζ₀(β)| ≤ |β|`) be a cycle with `M_W(C) = θ₀ ν(W)`
and the integer slice property, and assume the lower density bound `LD_{η₀}`.  Then
`(θ₀ • ν, ζ₀)` is an admissible representation of `C`, so `LD_{η₀}` gives
`η₀ ≤ liminf_{r↓0} θ₀ ν(B_r(y))/(ωₙrⁿ)` for `θ₀ • ν`-a.e., hence `ν`-a.e., `y`; pulling the
finite constant `θ₀` out of the `liminf` gives `η₀/θ₀ ≤ liminf_{r↓0} ν(B_r(y))/(ωₙrⁿ)`. -/
theorem Submission.dmcbr_ci_pw_blowup_lower_density : ∀ (P d : ℕ) (η₀ θ₀ : ℝ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ (C' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)), C'.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C'.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C' ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C' ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C').boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → 0 < θ₀ → C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = ENNReal.ofReal θ₀ * ν W) → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ y, θ₀ * ζ₀ ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂ν) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ᵐ y ∂ν, ENNReal.ofReal (η₀ / θ₀) ≤ liminf (fun r : ℝ => ν (ball y r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) := by
  intro P d η₀ θ₀ ν ζ₀ C hLD hθ₀ hCb hνK hmass hζ₀ hrep hISP
  -- Step 1: `c = ofReal θ₀` is nonzero and finite, with `c.toReal = θ₀`
  set c : ℝ≥0∞ := ENNReal.ofReal θ₀ with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hθ₀
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcθ : c.toReal = θ₀ := ENNReal.toReal_ofReal hθ₀.le
  -- Step 2: `LD_{η₀}` for `C` with the measure `c • ν` and the constant field `ζ₀`
  have hLDc := hLD C (c • ν) (fun _ => ζ₀) hCb
    (fun K hK => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hctop.lt_top (hνK K hK))
    (fun W hW => by rw [hmass W hW, Measure.smul_apply, smul_eq_mul])
    aestronglyMeasurable_const
    (ae_of_all _ fun _ => hζ₀)
    (fun ω => by
      rw [hrep ω, integral_smul_measure, integral_const_mul, hcθ, smul_eq_mul])
    hISP
  -- Step 3: `ν ≪ c • ν`, so the bound holds `ν`-a.e.
  filter_upwards [(Measure.absolutelyContinuous_smul hc0).ae_le hLDc] with y hy
  -- Step 4: `(c • ν)(B_r(y)) / D(r) = c · (ν(B_r(y)) / D(r))`, and `c` leaves the `liminf`
  have hscale : (fun r : ℝ => (c • ν) (ball y r) /
      (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) =
      fun r : ℝ => c * (ν (ball y r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) := by
    funext r
    rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  rw [hscale, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top hc0 hctop] at hy
  -- Step 5: `ofReal (η₀ / θ₀) = ofReal η₀ / c ≤ liminf_{r↓0} ν(B_r(y)) / D(r)`
  rw [ENNReal.ofReal_div_of_pos hθ₀]
  exact ENNReal.div_le_of_le_mul' hy
/-- **Weights at least one with total at most one force a single plane through the origin.**
If `αᵢ ≥ 1` for every `i`, `∑ᵢ αᵢ ≤ 1`, `w_{i₀} = 0` for some `i₀` and
`ν = ∑ᵢ αᵢ m⌞{y : y - wᵢ ∈ V}`, then `ν = m⌞V`.  Two distinct indices `i ≠ i₀` would give
`2 ≤ αᵢ + α_{i₀} ≤ ∑ⱼ αⱼ ≤ 1`, so `i₀` is the only index; hence `α_{i₀} = ∑ⱼ αⱼ = 1` and the sum
collapses to `ofReal 1 • m⌞{y : y - 0 ∈ V} = m⌞V`. -/
theorem Submission.dmcbr_ci_pw_single_plane_of_unit_weights : ∀ (P N : ℕ) (m ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (w : Fin N → Euclid P) (α : Fin N → ℝ), (∀ i, 1 ≤ α i) → ∑ i, α i ≤ 1 → (∃ i, w i = 0) → ν = ∑ i, ENNReal.ofReal (α i) • m.restrict {y : Euclid P | y - w i ∈ V} → ν = m.restrict (V : Set (Euclid P)) := by
  intro P N m ν V w α hα hsum hw hν
  -- Step 1: an index `i₀` with `w i₀ = 0`
  obtain ⟨i₀, hi₀⟩ := hw
  -- Step 2: every index is `i₀`: for `i ≠ i₀`, `αᵢ + α_{i₀} = ∑_{j ∈ {i, i₀}} αⱼ ≤ ∑ⱼ αⱼ ≤ 1`
  -- (all `αⱼ ≥ 1 ≥ 0`), contradicting `αᵢ + α_{i₀} ≥ 2`
  have hall : ∀ i, i = i₀ := by
    intro i
    by_contra hne
    have hpair : ∑ j ∈ ({i, i₀} : Finset (Fin N)), α j ≤ ∑ j, α j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j _ _ => zero_le_one.trans (hα j)
    rw [Finset.sum_pair hne] at hpair
    linarith [hα i, hα i₀]
  -- Step 3: every sum over the indices is its `i₀`-term, so `∑ⱼ αⱼ = α_{i₀}` and `α_{i₀} = 1`
  have hα₀ : α i₀ = 1 := by
    rw [Finset.sum_eq_single i₀ (fun j _ hj => absurd (hall j) hj)
      fun h => absurd (Finset.mem_univ i₀) h] at hsum
    exact le_antisymm hsum (hα i₀)
  -- Step 4: `ν = ofReal α_{i₀} • m⌞{y | y - w i₀ ∈ V} = 1 • m⌞{y | y - 0 ∈ V} = m⌞V`
  rw [hν, Finset.sum_eq_single i₀ (fun j _ hj => absurd (hall j) hj)
    fun h => absurd (Finset.mem_univ i₀) h, hα₀, hi₀, ENNReal.ofReal_one, one_smul]
  simp only [sub_zero, SetLike.setOfPred_mem_eq]
/-- **The operator norm of an `n`-covector is at most `Pⁿ` times its Euclidean coefficient norm**
(fact (F1) in the proof of `Submission.dmcbr_ci_blowup_limit`; `|·|_E` is `covectorEuclideanNorm`).
Let `e` be the standard basis of `ℝᴾ`.  Each coefficient satisfies
`|α(e_{J(0)}, …, e_{J(n−1)})| ≤ |α|_E`: it vanishes if `J` repeats an index, and otherwise
`I = J ∘ σ` with `σ = Tuple.sort J` is strictly increasing, `α(e ∘ I) = sgn σ · α(e ∘ J)`, and
`α(e ∘ I)²` is one of the summands of `|α|_E²`.  Expanding every `v_k` in `e` gives
`α(v) = Σ_J (Π_k v_k(J k)) α(e ∘ J)` over the `Pⁿ` maps `J : Fin n → Fin P`; with
`|v_k(i)| ≤ ‖v_k‖` this gives `|α(v)| ≤ Pⁿ |α|_E Π_k ‖v_k‖`, hence `‖α‖ ≤ Pⁿ |α|_E`. -/
theorem Submission.dmcbr_ci_bl_covector_opNorm_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ‖α‖ ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
  intro P n α
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Step 1: `|α(e_{J(0)}, …, e_{J(n−1)})| ≤ |α|_E` for every `J : Fin n → Fin P`
  have hcoef : ∀ J : Fin n → Fin P, |α (fun k => e (J k))| ≤ covectorEuclideanNorm α := by
    intro J
    by_cases hJ : Injective J
    · -- `I = J ∘ σ` with `σ = Tuple.sort J` is strictly increasing, `α(e ∘ I) = sgn σ · α(e ∘ J)`
      set σ := Tuple.sort J
      have hI : StrictMono (J ∘ σ) :=
        (Tuple.monotone_sort J).strictMono_of_injective (hJ.comp σ.injective)
      have hperm : α ((fun k => e (J k)) ∘ σ) = Equiv.Perm.sign σ • α (fun k => e (J k)) :=
        α.toAlternatingMap.map_perm (fun k => e (J k)) σ
      have habs : |α (fun k => e (J k))| = |α (fun k => e ((J ∘ σ) k))| := by
        change _ = |α ((fun k => e (J k)) ∘ σ)|
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      -- `α(e ∘ I)²` is one of the nonnegative summands of `|α|_E²`
      rw [habs]
      unfold covectorEuclideanNorm
      refine Real.abs_le_sqrt (le_trans (le_of_eq ?_)
        (Finset.single_le_sum (fun I _ => ?_) (Finset.mem_univ (J ∘ σ))))
      · rw [ite_eq_left hI]
      · positivity
    · -- a repeated index: `α(e ∘ J) = 0` by alternation
      have h0 : α (fun k => e (J k)) = 0 :=
        α.map_eq_zero_of_not_injective _ fun h => hJ (Injective.of_comp (f := ⇑e) h)
      rw [h0, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  refine α.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg P) n)
    (covectorEuclideanNorm_nonneg α)) fun v => ?_
  -- Step 2: `α(v) = Σ_J (Π_k v_k(J k)) α(e ∘ J)` by multilinearity
  have hexp : α v = ∑ J : Fin n → Fin P, (∏ k, v k (J k)) * α (fun k => e (J k)) := by
    conv_lhs => rw [show v = fun k => ∑ i, v k i • e i from
      funext fun k => (e.sum_repr (v k)).symm]
    rw [α.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← smul_eq_mul]
    exact α.map_smul_univ (fun k => v k (J k)) (fun k => e (J k))
  -- Step 3: each term is at most `(Π_k ‖v_k‖) |α|_E`, and there are `P ^ n` terms
  rw [hexp, Real.norm_eq_abs]
  calc |∑ J : Fin n → Fin P, (∏ k, v k (J k)) * α (fun k => e (J k))|
      ≤ ∑ J : Fin n → Fin P, |(∏ k, v k (J k)) * α (fun k => e (J k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J : Fin n → Fin P, (∏ k, ‖v k‖) * covectorEuclideanNorm α := by
        refine Finset.sum_le_sum fun J _ => ?_
        rw [abs_mul, Finset.abs_prod]
        refine mul_le_mul (Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => ?_)
          (hcoef J) (abs_nonneg _) (Finset.prod_nonneg fun k _ => norm_nonneg _)
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (v k) (J k)
    _ = (P : ℝ) ^ n * covectorEuclideanNorm α * ∏ k, ‖v k‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        simp only [Fintype.card_fin]
        push_cast
        ring
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

/-- **Dilations of currents in `ℝᴾ` exist and agree with the blow-up `η_{a,λ#}`** (Simon Ch. 3,
1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413).  Call
`X' ∈ 𝒟ₘ(ℝᴾ)` a dilation of `X` if `X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`, `η = η_{a,λ}`.
Since `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`, so `η_{a,λ#}X ∈ 𝒟ₘ(η(ℝᴾ))` restricts to `ℝᴾ`.  (i) This
restriction is a dilation of `X`; (ii) every dilation `X'` of `X` agrees with `η_{a,λ#}X`:
`X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω₁ ∈ 𝒟ᵐ(η(ℝᴾ))` has the underlying form of `ω`.  Both follow
from `Submission.dtc_blowUp_testForm_corr` with `U = ℝᴾ`. -/
theorem Submission.cbr_cidc_dilation_exists_eq_blowUp : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ (ω : TestFormOn (univ : Set (Euclid P)) m) (ω₁ : TestFormOn (dilation a lam '' (univ : Set (Euclid P))) m), (ω₁ : DifferentialForm (Euclid P) m) = (ω : DifferentialForm (Euclid P) m) → X' ω = blowUp X a lam hlam.ne' ω₁ := by
  intro P m a lam hlam
  obtain ⟨hA, -, hC⟩ := Submission.dtc_blowUp_testForm_corr P m univ a lam hlam
  -- Step 1: `η` maps `ℝᴾ` onto `ℝᴾ`, since `η(a + λy) = y`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by
      simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']⟩
  refine ⟨fun X => ?_, fun X X' hX' ω ω₁ hω => ?_⟩
  · -- Step 2, (i): the restriction of `η_{a,λ#}X` to `ℝᴾ` is a dilation of `X`, by part (c).
    refine ⟨(blowUp X a lam hlam.ne').restrictDomain hsurj, fun ω ω' hωω' => ?_⟩
    rw [GeometricCurrentOn.restrictDomain_apply]
    exact hC X _ ω' (by simpa using hωω')
  · -- Steps 3–4, (ii): part (a) gives `ω' = ω₁ ∘ η = ω ∘ η`, and part (c) and the dilation
    -- property give `η_{a,λ#}X(ω₁) = λ⁻ᵐ X(ω') = X'(ω)`.
    obtain ⟨ω', hω'⟩ := hA ω₁
    rw [hC X ω₁ ω' hω', hX' ω ω' (fun y => by rw [hω', hω])]
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

/-- **Dilations commute with the boundary** (Simon 6.2.3, chapter-06.txt line 216, and
6.2.24(1), line 414, for `η = η_{a,λ}`, `λ > 0`; the dilations of the closure theorem 6.8.2):
if `X'(ω) = λ^{-(m+1)} X(ω ∘ η)` on `𝒟^{m+1}(ℝᴾ)`, then `∂X'(ω) = λ⁻ᵐ ∂X(ω ∘ η)` on `𝒟ᵐ(ℝᴾ)`.

`η` maps `ℝᴾ` onto itself, so `ω` is also a test form `ω₁` in `η(ℝᴾ)`, and `dω`, `dω₁` have the
same underlying form.  Hence
`∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`
(`cbr_cidc_dilation_exists_eq_blowUp`, `dtc_blowUp_algebra` (iv), `dtc_blowUp_testForm_corr` (c)). -/
theorem Submission.cbr_cidc_dilation_boundary : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω' := by
  intro P m a lam hlam X X' hX ω ω' hω
  -- Step 1: `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and `ω` is a test form `ω₁` in `η(ℝᴾ)`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  let ω₁ : TestFormOn (dilation a lam '' univ) m := testFormOnInclusion hsurj m ω
  -- Step 2: `X'(dω) = η_#X(dω₁)`, as `dω₁` and `dω` are the same form.
  have h1 := (Submission.cbr_cidc_dilation_exists_eq_blowUp P (m + 1) a lam hlam).2 X X' hX
    (exteriorDerivativeTestOn univ m ω) (exteriorDerivativeTestOn _ m ω₁) rfl
  -- Steps 2–3: `∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁)`.
  rw [GeometricCurrentOn.boundary_apply, h1, ← GeometricCurrentOn.boundary_apply,
    (Submission.dtc_blowUp_algebra P univ a lam hlam).2.2.2 m X]
  -- Step 4: `η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`, as `ω' = ω ∘ η = ω₁ ∘ η`.
  exact (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).2.2 X.boundary ω₁ ω' hω

/-- **A dilation of an integer multiplicity current is integer multiplicity** (item (3) of the
dilation calculus for `η = η_{a,λ}`, `λ > 0`: Simon Ch. 6, 3.3–3.9 for the push-forward 6.2.23,
as used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  If `R = (M, θ, ξ)`
represents `X` in `ℝᴾ`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
(`dtc_blowUp_imrep`).  As `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`: `R'` is also a triple in `ℝᴾ` (a compact
`K ⊆ ℝᴾ` lies in `η(ℝᴾ)`), and `X'(ω) = η_{a,λ#}X(ω) = R'(ω)` for every test form `ω` on `ℝᴾ`
(`cbr_cidc_dilation_exists_eq_blowUp`). -/
theorem Submission.cbr_cidc_dilation_isIntegerMultiplicity : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X' := by
  intro P m a lam hlam X X' hX hXim
  obtain ⟨R, hR⟩ := hXim
  -- `η = η_{a,λ}` is onto, `η(a + λy) = y`, so `ℝᴾ ⊆ η(ℝᴾ)`
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  -- `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
  obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P m univ X a lam hlam R hR
  -- the same triple in `ℝᴾ`: of its conditions only local integrability involves the domain
  refine ⟨{ carrier := R'.carrier
            mult := R'.mult
            orient := R'.orient
            measurableSet_carrier := R'.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := R'.rectifiable
            measurable_mult := R'.measurable_mult
            mult_pos := R'.mult_pos
            locallyIntegrable_mult := fun K hK _ =>
              R'.locallyIntegrable_mult K hK ((subset_univ K).trans hsurj)
            aestronglyMeasurable_orient := R'.aestronglyMeasurable_orient
            orients := R'.orients }, ?_⟩
  -- `X'(ω) = η_{a,λ#}X(ω) = R'(ω)`, with `ω` regarded as a test form in `η(ℝᴾ)`
  intro ω
  rw [(Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX ω
    (testFormOnInclusion hsurj m ω) rfl, hR' (testFormOnInclusion hsurj m ω)]
  rfl

/-- **Integral representations under the dilation `η = η_{a,λ}`, `λ > 0`** (Simon 6.2.7 and
Remark 6.2.24(2), chapter-06.txt lines 271 and 414–419, for `f = η`; `η` as in Ch. 3, 1.4,
chapter-03.txt line 85).  If `X'` is a dilation of `X` (`X'(ω) = λ⁻ᵐ X(ω')` whenever
`ω' = ω ∘ η`) and `X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`, then
`X'(ω) = ∫ ⟨ω(y), ξ(a + λy)⟩ d(λ⁻ᵐ η_*μ)(y)`: take `ω' = ω ∘ η`, change variables `y = η(x)`
(`η` is a homeomorphism, hence a measurable embedding) and use `a + λη(x) = x`. -/
theorem Submission.cbr_cidc_dilation_integral_rep : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) := by
  intro P m a lam hlam X X' μ ξ hX hrep ω
  have hne : lam ≠ 0 := hlam.ne'
  -- `η = η_{a,λ}` (`y ↦ −λ⁻¹a + λ⁻¹y`) and `ι(z) = a + λz` are mutually inverse.
  have hηι : ∀ y, dilation a lam (a + lam • y) = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ x, a + lam • dilation a lam x = x := by
    intro x
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  -- Step 1: `η` maps `ℝᴾ` onto itself, so `ω ∈ 𝒟ᵐ(η(ℝᴾ))`, and the accepted
  -- `dtc_blowUp_testForm_corr` (a) gives `ω' ∈ 𝒟ᵐ(ℝᴾ)` with `ω' = ω ∘ η`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ :=
    fun y _ => ⟨a + lam • y, mem_univ _, hηι y⟩
  obtain ⟨ω', hω'⟩ :=
    (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).1 (testFormOnInclusion hsurj m ω)
  -- Step 2: `X'(ω) = λ⁻ᵐ X(ω') = λ⁻ᵐ ∫ ⟨ω'(x), ξ(x)⟩ dμ(x)`.
  rw [hX ω ω' (fun y => by simpa using hω' y), hrep ω']
  -- Step 3: `η` is a homeomorphism, hence a measurable embedding, so
  -- `∫ g d(η_*μ) = ∫ g ∘ η dμ` for every `g` (no integrability needed).
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have hη : ⇑η = dilation a lam := by
    funext y
    simp [η, dilation, dilationCLM]
  have hemb : MeasurableEmbedding (dilation a lam) := hη ▸ η.measurableEmbedding
  -- Steps 4–5: `∫ g d(c • ν) = c.toReal * ∫ g dν` with `(ofReal λ⁻ᵐ).toReal = λ⁻ᵐ`; for
  -- `g(y) = ⟨ω(y), ξ(a + λy)⟩`, `g(η(x)) = ⟨ω'(x), ξ(x)⟩` because `a + λη(x) = x`.
  rw [integral_smul_measure, hemb.integral_map, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hιη x, hω' x, testFormOnInclusion_coe]
/-- **Mass scaling for dilations: `M_{η(W)}(X') = λ⁻ᵐ M_W(X)`** for `η = η_{a,λ}`, `λ > 0`, a
dilation `X' ∈ 𝒟ₘ(ℝᴾ)` of `X ∈ 𝒟ₘ(ℝᴾ)` (`X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`) and every
`W ⊆ ℝᴾ` (item (5) of the dilation calculus for the integer-multiplicity criterion for cycles;
`η_{x,λ}` of Simon Ch. 3, 1.4, chapter-03.txt line 85; mass `M_W` of 6.2.5, chapter-06.txt
lines 221–233, with the Euclidean coefficient norm).  `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and
`𝒟ᵐ(ℝᴾ)`, `𝒟ᵐ(η(ℝᴾ))` consist of the same forms, with the same admissible forms for `M_{η(W)}`.
By `Submission.cbr_cidc_dilation_exists_eq_blowUp`, `X'(ω) = η_{a,λ#}X(ω)` on equal forms, so
`M_{η(W)}(X') = M_{η(W)}(η_{a,λ#}X)`, which is `λ⁻ᵐ M_W(X)` by
`Submission.dtc_blowUp_massOn_image`. -/
theorem Submission.cbr_cidc_dilation_massOn_image : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W := by
  intro P m a lam hlam X X' hX W
  -- `η = η_{a,λ}` is onto (`η(a + λy) = y`), so `ℝᴾ` and `η(ℝᴾ)` have the same test forms.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  have hsub : dilation a lam '' (univ : Set (Euclid P)) ⊆ univ := subset_univ _
  -- `X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω` and `ω₁` have the same underlying form.
  have hblow := (Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX
  refine Eq.trans ?_ (Submission.dtc_blowUp_massOn_image P m univ X a lam hlam W)
  -- The admissible forms for `M_{η(W)}(X')` and `M_{η(W)}(η_{a,λ#}X)` are the same forms, on
  -- which `X'` and `η_{a,λ#}X` agree.
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨testFormOnInclusion hsurj m φ, hφ,
      congrArg ENNReal.ofReal (hblow φ (testFormOnInclusion hsurj m φ) rfl).symm⟩
  · rintro ⟨φ₁, hφ₁, rfl⟩
    exact ⟨testFormOnInclusion hsub m φ₁, hφ₁,
      congrArg ENNReal.ofReal (hblow (testFormOnInclusion hsub m φ₁) φ₁ rfl)⟩

/-- **Dilation calculus for currents in `ℝᴾ`** (Simon Ch. 6, 2.23 for the similarity
`η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`; used to rescale cycles in the proof that cycles with
the integer slice property are integer multiplicity).  Call `X' ∈ 𝒟ₘ(ℝᴾ)` a dilation of `X` if
`X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`.  (1) Since `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`, and the
restriction of `η_{a,λ#}X ∈ 𝒟ₘ(η(ℝᴾ))` to `ℝᴾ` is a dilation of `X` by part (c) of
`Submission.dtc_blowUp_testForm_corr`.  (2)–(5) are `Submission.cbr_cidc_dilation_boundary`,
`Submission.cbr_cidc_dilation_isIntegerMultiplicity`, `Submission.cbr_cidc_dilation_integral_rep`
and `Submission.cbr_cidc_dilation_massOn_image`; (6) is part (i) of
`Submission.dtc_hausdorff_dilation`. -/
theorem Submission.cbr_ci_dilation_calculus : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω') ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X') ∧ (∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ)) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W) ∧ (∀ A : Set (Euclid P), μHE[m] (dilation a lam '' A) = ENNReal.ofReal (lam⁻¹ ^ m) * μHE[m] A) := by
  intro P m a lam hlam
  refine ⟨fun X => ?_, Submission.cbr_cidc_dilation_boundary P m a lam hlam,
    Submission.cbr_cidc_dilation_isIntegerMultiplicity P m a lam hlam,
    Submission.cbr_cidc_dilation_integral_rep P m a lam hlam,
    Submission.cbr_cidc_dilation_massOn_image P m a lam hlam,
    (Submission.dtc_hausdorff_dilation P m a lam hlam).1⟩
  -- (1) `η` maps `ℝᴾ` onto `ℝᴾ`, as `η(a + λy) = y`; so `η_{a,λ#}X` restricts to `ℝᴾ`, and the
  -- restriction is a dilation of `X` by part (c) of the test-form correspondence.
  obtain ⟨-, -, hC⟩ := Submission.dtc_blowUp_testForm_corr P m univ a lam hlam
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by
      simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']⟩
  refine ⟨(blowUp X a lam hlam.ne').restrictDomain hsurj, fun ω ω' hωω' => ?_⟩
  rw [GeometricCurrentOn.restrictDomain_apply]
  exact hC X _ ω' (by simpa using hωω')
/-- **Dilation calculus for currents in `ℝᴾ`** for `η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`
(`η_{x,λ}` of Simon Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt
lines 403–413; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).
`X' ∈ 𝒟ₘ(ℝᴾ)` is a dilation of `X` if `X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`.
(1) every `X` has a dilation, `η_{a,λ#}X` (`cbr_cidc_dilation_exists_eq_blowUp`); (2) `∂X'` is a
dilation of `∂X` (`cbr_cidc_dilation_boundary`); (3) a dilation of an integer multiplicity
current is integer multiplicity (`cbr_cidc_dilation_isIntegerMultiplicity`); (4) if
`X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` then `X'(ω) = ∫ ⟨ω(y), ξ(a + λy)⟩ d(λ⁻ᵐ η_*μ)(y)`
(`cbr_cidc_dilation_integral_rep`); (5) `M_{η(W)}(X') = λ⁻ᵐ M_W(X)`
(`cbr_cidc_dilation_massOn_image`); (6) `Hᵐ(η(A)) = λ⁻ᵐ Hᵐ(A)` (`dtc_hausdorff_dilation` (i)). -/
theorem Submission.dmcbr_ci_dilation_calculus : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω') ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X') ∧ (∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ)) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W) ∧ (∀ A : Set (Euclid P), μHE[m] (dilation a lam '' A) = ENNReal.ofReal (lam⁻¹ ^ m) * μHE[m] A) := by
  intro P m a lam hlam
  exact ⟨(Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).1,
    Submission.cbr_cidc_dilation_boundary P m a lam hlam,
    Submission.cbr_cidc_dilation_isIntegerMultiplicity P m a lam hlam,
    Submission.cbr_cidc_dilation_integral_rep P m a lam hlam,
    Submission.cbr_cidc_dilation_massOn_image P m a lam hlam,
    (Submission.dtc_hausdorff_dilation P m a lam hlam).1⟩
/-- Restricted representing integrals are determined by the represented current (closure theorem,
Simon Ch. 6, 8.2–8.3, as used for 7.2.4): if `∫ ⟨ω, ξ₁⟩ dμ₁ = ∫ ⟨ω, ξ₂⟩ dμ₂ + ∫ ⟨ω, ξ₃⟩ dμ₃` for
every `ω ∈ 𝒟ᵏ(U)`, the same identity holds for the integrals over every Borel set `B`.  For fixed
`ω` the integrands are integrable (bounded by `|ω|`, which vanishes off the compact `spt ω ⊆ U`).
Testing the hypothesis with `gω`, `g` smooth, and letting `g = (1 - f)ʲ ↓ 𝟙_F` (`f` smooth,
`0 ≤ f ≤ 1`, with support `ℝᴾ \ F`) gives the identity on closed sets `F` by dominated
convergence; Dynkin's π-λ theorem extends it to all Borel sets. -/
theorem Submission.cbr_setIntegral_eq_of_integral_eq : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃ := by
  intro P k U μ₁ μ₂ μ₃ ξ₁ ξ₂ ξ₃ _hU hμ₁ hμ₂ hμ₃ hξ₁ hξ₂ hξ₃ hb₁ hb₂ hb₃ heq B ω hB
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := ω.property.1.1
  have hwc : HasCompactSupport w := ω.property.1.2
  have hwU : tsupport w ⊆ U := ω.property.2
  -- Step 1: `x ↦ ξ x (w x)` is integrable: it vanishes off the compact set `tsupport w ⊆ U` and
  -- is bounded by `sup |w|`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖covectorEuclideanNorm (w x)‖ ≤ C := by
    refine Continuous.bounded_above_of_compact_support ?_
      (hwc.comp_left (g := fun α : Covector (Euclid P) k => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P k))
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    exact Continuous.if_const _ ((hws.continuous.eval_const _).pow 2) continuous_const
  have hint : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k),
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) →
      Integrable (fun x => ξ x (w x)) μ := by
    intro μ ξ hμ hξ hb
    have hsupp : support (fun x => ξ x (w x)) ⊆ tsupport w := by
      intro x hx
      by_contra hxw
      exact hx (by simp [image_eq_zero_of_notMem_tsupport hxw])
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    refine Measure.integrableOn_of_bounded (M := C) (hμ _ hwc hwU).ne
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξ
        hws.continuous.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_of_ae hb] with x hx
    rw [Real.norm_eq_abs]
    exact (hx (w x)).trans ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC x))
  have hi₁ := hint μ₁ ξ₁ hμ₁ hξ₁ hb₁
  have hi₂ := hint μ₂ ξ₂ hμ₂ hξ₂ hb₂
  have hi₃ := hint μ₃ ξ₃ hμ₃ hξ₃ hb₃
  -- Step 2: testing the hypothesis with the test form `g • w`, `g` smooth.
  have hmul : ∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∫ x, g x * ξ₁ x (w x) ∂μ₁ = ∫ x, g x * ξ₂ x (w x) ∂μ₂ + ∫ x, g x * ξ₃ x (w x) ∂μ₃ := by
    intro g hg
    have hmem : (fun x => g x • w x) ∈ testFormOnSubmodule U k :=
      ⟨⟨hg.smul hws, hwc.mono' ((subset_tsupport _).trans (tsupport_smul_subset_right g w))⟩,
        (tsupport_smul_subset_right g w).trans hwU⟩
    simpa only [Submodule.coe_mk, map_smul, smul_eq_mul] using heq ⟨fun x => g x • w x, hmem⟩
  -- Step 3: closed sets, by smooth approximation of the indicator and dominated convergence.
  have hclosed : ∀ F : Set (Euclid P), IsClosed F →
      ∫ x in F, ξ₁ x (w x) ∂μ₁ = ∫ x in F, ξ₂ x (w x) ∂μ₂ + ∫ x in F, ξ₃ x (w x) ∂μ₃ := by
    intro F hF
    obtain ⟨f, hfs, hfd, hfr⟩ := hF.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
    have hgd : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (1 - f x) ^ n) :=
      fun n => (contDiff_const.sub hfd).pow n
    have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x => hfr ⟨x, rfl⟩
    have hgb : ∀ (n : ℕ) x, ‖(1 - f x) ^ n‖ ≤ 1 := by
      intro n x
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hf01 x).2])]
      exact pow_le_one₀ (by linarith [(hf01 x).2]) (by linarith [(hf01 x).1])
    have hlim : ∀ (μ : Measure (Euclid P)) (h : Euclid P → ℝ), Integrable h μ →
        Tendsto (fun n : ℕ => ∫ x, (1 - f x) ^ n * h x ∂μ) atTop (𝓝 (∫ x in F, h x ∂μ)) := by
      intro μ h hh
      rw [← integral_indicator hF.measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun n => ?_) hh.norm
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · exact (hgd n).continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hgb n x)
      · by_cases hx : x ∈ F
        · have hfx : f x = 0 := Function.notMem_support.mp (by rw [hfs]; exact fun h => h hx)
          simp [hfx, hx]
        · have hfx : f x ≠ 0 := Function.mem_support.mp (by rw [hfs]; exact hx)
          have hpos : 0 < f x := lt_of_le_of_ne (hf01 x).1 (Ne.symm hfx)
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - f x)
            (by linarith [(hf01 x).2]) (by linarith)).mul_const (h x)
          simpa [hx] using this
    exact tendsto_nhds_unique (hlim μ₁ _ hi₁)
      (((hlim μ₂ _ hi₂).add (hlim μ₃ _ hi₃)).congr fun n => (hmul _ (hgd n)).symm)
  -- Step 4: Dynkin's π-λ theorem extends the identity from closed sets to all Borel sets.
  have hall : ∀ (t : Set (Euclid P)) (_ : MeasurableSet t),
      ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃ := by
    refine MeasurableSpace.induction_on_inter (s := {s | IsClosed s})
      (C := fun t _ =>
        ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃)
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      (by simp) (fun t ht => hclosed t ht) (fun t htm ht => ?_) (fun f hfd hfm hf => ?_)
    · have e₁ := integral_add_compl htm hi₁
      have e₂ := integral_add_compl htm hi₂
      have e₃ := integral_add_compl htm hi₃
      have e := heq ω
      linarith
    · exact (hasSum_integral_iUnion hfm hfd hi₁.integrableOn).unique
        (((hasSum_integral_iUnion hfm hfd hi₂.integrableOn).add
          (hasSum_integral_iUnion hfm hfd hi₃.integrableOn)).congr_fun fun n => hf n)
  exact hall B hB
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
/-- **Integrability and zeroth-order bound of the pairing `∫_E ⟨ω, ξ⟩ dμ`** (Simon 6.2.4–6.2.5,
`μ⌞E ∧ ξ` as a current; used for restrictions of currents in the slicing argument of 7.2.4).
If `|⟨α, ξ(x)⟩| ≤ |α|` for every `n`-covector `α` and `μ`-a.e. `x`, and the continuous form
`ω` vanishes off a measurable `K` with `μ(K) < ∞` and `|ω| ≤ ε`, then `|ξ(ω)| ≤ ε 1_K`
`μ`-a.e., so `ξ(ω)` is `μ⌞E`-integrable and `|∫_E ξ(ω) dμ| ≤ ε μ(K ∩ E) ≤ ε μ(K)`. -/
theorem Submission.cmcs_rc_pairing_integrable_abs_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E K : Set (Euclid P)) (ω : DifferentialForm (Euclid P) n) (ε : ℝ), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Continuous ω → MeasurableSet K → μ K < ∞ → (∀ x, x ∉ K → ω x = 0) → (∀ x, covectorEuclideanNorm (ω x) ≤ ε) → Integrable (fun x => ξ x (ω x)) (μ.restrict E) ∧ |∫ x in E, ξ x (ω x) ∂μ| ≤ ε * (μ K).toReal := by
  intro P n μ ξ E K ω ε hξm hξb hω hK hμK hzero hε
  -- Step 1: `ε ≥ 0`
  have hε0 : 0 ≤ ε := (covectorEuclideanNorm_nonneg _).trans (hε 0)
  -- Step 2: `F x = ξ x (ω x)` is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => ξ x (ω x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n)
      (F := ℝ)).continuous.comp_aestronglyMeasurable₂ (g := fun Λ α => Λ α) hξm
      hω.aestronglyMeasurable
  -- Step 3: `‖F x‖ ≤ K.indicator ε x` a.e.
  have hbd : ∀ᵐ x ∂μ, ‖ξ x (ω x)‖ ≤ K.indicator (fun _ => ε) x := by
    filter_upwards [hξb] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]
      exact (hx (ω x)).trans (hε x)
    · rw [indicator_of_notMem hxK, hzero x hxK, map_zero, norm_zero]
  -- Step 4: the dominating function is integrable
  have hg : Integrable (K.indicator (fun _ => ε)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  -- Step 5: integrability of `F`, then on `μ.restrict E`
  have hint : Integrable (fun x => ξ x (ω x)) μ := hg.mono' hmeas hbd
  refine ⟨hint.restrict, ?_⟩
  -- Step 6: `‖∫_E F‖ ≤ ∫_E g = ν.real K * ε`
  have h1 : ‖∫ x in E, ξ x (ω x) ∂μ‖ ≤ ∫ x in E, K.indicator (fun _ => ε) x ∂μ :=
    norm_integral_le_of_norm_le hg.restrict (ae_restrict_of_ae hbd)
  rw [integral_indicator_const ε hK, smul_eq_mul] at h1
  -- Step 7: `ν K = μ (K ∩ E) ≤ μ K`, multiply by `ε ≥ 0`
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  rw [measureReal_def, Measure.restrict_apply hK]
  exact ENNReal.toReal_mono hμK.ne (measure_mono inter_subset_left)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- **Restriction of a measure-represented current** (Simon Ch. 6, 2.9:
`T ⌞ A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`), for an arbitrary pair `(μ, ξ)` and an arbitrary set `E`: if `μ` is
finite on compact subsets of `U` and `ξ` is `μ`-a.e. strongly measurable with
`|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for `μ`-a.e. `x`, then
`ω ↦ ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` is a current in `U`.  By `rsd_mw_tfa_norm_props`, `|α| ≤ C ‖α‖`.
For `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, `cmcs_rc_pairing_integrable_abs_le` then
gives integrability on `μ ⌞ E` and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`.  The functional is linear
(`integral_add`, `integral_const_mul`), and `cmcs_rc_order_zero_current` turns the order-zero
bound into Simon's sequential continuity. -/
theorem Submission.cmcs_restrict_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
  intro P n U μ ξ E hμK hξm hξb
  -- Step 1: `|α| ≤ C ‖α‖` for every `n`-covector `α`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Steps 2 and 4: for `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, the pairing is
  -- `μ ⌞ E`-integrable and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`
  have hpair : ∀ (ω : TestFormOn U n) (K : Set (Euclid P)) (M : ℝ), IsCompact K → K ⊆ U →
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K →
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) ∧
        |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| ≤ C * M * (μ K).toReal := by
    intro ω K M hK hKU hsupp hM
    exact Submission.cmcs_rc_pairing_integrable_abs_le P n μ ξ E K
      (ω : DifferentialForm (Euclid P) n) (C * M) hξm hξb ω.property.1.1.continuous
      hK.measurableSet (hμK K hK hKU)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))
      (fun x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0))
  -- Step 2: every test form is admissible, with `K = tsupport ω` and `M = sup ‖ω‖ < ∞`
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) := by
    intro ω
    obtain ⟨M, hM⟩ := ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
    exact (hpair ω _ M ω.property.1.2 ω.property.2 subset_rfl hM).1
  -- Step 3: `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω₁) (hint ω₂)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Steps 4 and 5: the order-zero bound with `c_K = C μ(K)` makes `L` a current
  obtain ⟨S, hS⟩ := Submission.cmcs_rc_order_zero_current P n U L fun K hK hKU =>
    ⟨C * (μ K).toReal, fun ω M hsupp hM => by
      calc |L ω| = |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| := rfl
        _ ≤ C * M * (μ K).toReal := (hpair ω K M hK hKU hsupp hM).2
        _ = C * (μ K).toReal * M := by ring⟩
  exact ⟨S, hS⟩
/-- **Level splitting of a test form** (a step in the proof of Simon Ch. 6, 4.8,
`spt ⟨T, f, t₊⟩ ⊆ spt T ∩ {f = t}`).  If `tsupport η` misses the level set `{f = t}` of a
continuous `f`, then `η = η₁ + η₂` with test forms `η₁ = χ η` supported in `{f < t}` and
`η₂ = (1 - χ) η` supported in `{t < f}`.  Here `χ` is a smooth Urysohn function equal to `1` on
`K₋ = tsupport η ∩ {f ≤ t}` and to `0` on `K₊ = tsupport η ∩ {t ≤ f}`; these closed sets are
disjoint, with `K₋ ⊆ {f < t}` and `K₊ ⊆ {t < f}`, because `tsupport η` misses `{f = t}`. -/
theorem Submission.cmcs_ss_testForm_level_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (f : Euclid P → ℝ) (t : ℝ) (η : TestFormOn U n), Continuous f → Disjoint (tsupport (η : DifferentialForm (Euclid P) n)) {x | f x = t} → ∃ η₁ η₂ : TestFormOn U n, η = η₁ + η₂ ∧ tsupport (η₁ : DifferentialForm (Euclid P) n) ⊆ {x | f x < t} ∧ tsupport (η₂ : DifferentialForm (Euclid P) n) ⊆ {x | t < f x} := by
  intro P n U f t η hf hη
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := η.property
  set e : DifferentialForm (Euclid P) n := (η : DifferentialForm (Euclid P) n)
  -- the closed halves `K₋ = K ∩ {f ≤ t}` and `K₊ = K ∩ {t ≤ f}` of `K = tsupport η` are
  -- disjoint, since `K` misses `{f = t}`
  have hKl : IsClosed (tsupport e ∩ {x | f x ≤ t}) :=
    (isClosed_tsupport e).inter (isClosed_le hf continuous_const)
  have hKu : IsClosed (tsupport e ∩ {x | t ≤ f x}) :=
    (isClosed_tsupport e).inter (isClosed_le continuous_const hf)
  have hd : Disjoint (tsupport e ∩ {x | t ≤ f x}) (tsupport e ∩ {x | f x ≤ t}) :=
    Set.disjoint_left.2 fun x hxu hxl => Set.disjoint_left.1 hη hxu.1 (le_antisymm hxl.2 hxu.2)
  -- a smooth `χ` with `χ = 0` on `K₊` and `χ = 1` on `K₋`
  obtain ⟨χ, hχ, -, hχ₀, hχ₁⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hKu hKl hd
  -- `χ η` and `(1 - χ) η` are test forms in `U`, with sum `η`
  have h₁ : (fun x => χ x • e x) ∈ TestFormOn U n :=
    ⟨⟨hχ.smul hsmooth, hcpt.smul_left (f := χ)⟩, (tsupport_smul_subset_right χ e).trans hU⟩
  have h₂ : (fun x => (1 - χ x) • e x) ∈ TestFormOn U n :=
    ⟨⟨(contDiff_const.sub hχ).smul hsmooth, hcpt.smul_left (f := fun x => 1 - χ x)⟩,
      (tsupport_smul_subset_right (fun x => 1 - χ x) e).trans hU⟩
  refine ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext (funext fun x => ?_), ?_, ?_⟩
  · change e x = χ x • e x + (1 - χ x) • e x
    rw [← add_smul, add_sub_cancel, one_smul]
  · -- `support (χ η) ⊆ K₋`, a closed subset of `{f < t}`
    have hs : support (fun x => χ x • e x) ⊆ tsupport e ∩ {x | f x ≤ t} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show f x ≤ t from le_of_not_ge fun h => ?_⟩
      exact left_ne_zero_of_smul hx ((hχ₀ x).1 ⟨he, h⟩)
    exact (closure_minimal hs hKl).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h
  · -- `support ((1 - χ) η) ⊆ K₊`, a closed subset of `{t < f}`
    have hs : support (fun x => (1 - χ x) • e x) ⊆ tsupport e ∩ {x | t ≤ f x} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show t ≤ f x from le_of_not_ge fun h => left_ne_zero_of_smul hx ?_⟩
      rw [(hχ₁ x).1 ⟨he, h⟩, sub_self]
    exact (closure_minimal hs hKu).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h.symm
/-- Restriction commutes with the boundary on forms supported in the restricting set (Simon 6.4.6,
used for 4.8): let `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`, and let `A = T⌞S`,
`B = (∂T)⌞S` be given by the same integrals over `S`.  Then `∂A(θ) = B(θ)` whenever
`spt θ ⊆ S`.  Off `S` both `θ` and `dθ` vanish (`spt dθ ⊆ spt θ`), so both integrals over `S`
are integrals over `ℝᴾ`, and `∂A(θ) = A(dθ) = T(dθ) = ∂T(θ) = B(θ)`. -/
theorem Submission.cmcs_ss_boundary_eq_of_tsupport_subset : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, tsupport (θ : DifferentialForm (Euclid P) k) ⊆ S → A.boundary θ = B θ := by
  intro P k U T μ μ' ξ ξ' S A B hT hbT hA hB θ hθ
  -- `θ` and `dθ` vanish off `S`, as `spt dθ ⊆ spt θ ⊆ S`
  have hθ0 : ∀ x, x ∉ S → (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hθ h)
  have hdθ0 : ∀ x, x ∉ S → exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (hθ (tsupport_exteriorDerivative_subset _ h))
  -- so, `ξ x` and `ξ' x` being linear, both integrals over `S` are integrals over `ℝᴾ`
  have hAT : ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ =
      ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hdθ0 x hx, map_zero]
  have hBT : ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' =
      ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hθ0 x hx, map_zero]
  -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ = ∫ ⟨dθ, ξ⟩ dμ = T(dθ) = ∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`
  -- `= ∫_S ⟨θ, ξ'⟩ dμ' = B(θ)`
  calc A.boundary θ = A (exteriorDerivativeTestOn U k θ) := GeometricCurrentOn.boundary_apply A θ
    _ = ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hA _
    _ = ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hAT
    _ = T (exteriorDerivativeTestOn U k θ) := (hT (exteriorDerivativeTestOn U k θ)).symm
    _ = T.boundary θ := (GeometricCurrentOn.boundary_apply T θ).symm
    _ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hbT θ
    _ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hBT.symm
    _ = B θ := (hB θ).symm
/-- Simon Ch. 6, 4.6–4.8 (support of the slice `∂(T⌞S) − (∂T)⌞S`, `S = {f < t}`): if
`A(ω) = ∫_S ⟨ω, ξ⟩ dμ` and `B(θ) = ∫_S ⟨θ, ξ'⟩ dμ'`, then `∂A(θ) = A(dθ) = 0` and `B(θ) = 0`
whenever `spt θ` misses `S`, because `θ` and `dθ` (`spt dθ ⊆ spt θ`) vanish on `S`. -/
theorem Submission.cmcs_ss_boundary_vanish_of_disjoint : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, Disjoint (tsupport (θ : DifferentialForm (Euclid P) k)) S → A.boundary θ = 0 ∧ B θ = 0 := by
  intro P k U μ μ' ξ ξ' S A B hA hB θ hθ
  -- `θ` vanishes on `S`, and so does `dθ`, as `tsupport dθ ⊆ tsupport θ`
  have hθS : ∀ x ∈ S, (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hθ.notMem_of_mem_right hx)
  have hdθS : ∀ x ∈ S, exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' =>
      hθ.notMem_of_mem_right hx (tsupport_exteriorDerivative_subset _ hx')
  refine ⟨?_, ?_⟩
  · -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ`
    rw [GeometricCurrentOn.boundary_apply, hA]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    change ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) = 0
    rw [hdθS x hx, map_zero]
  · rw [hB]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hθS x hx, map_zero]

/-- **Simon Ch. 6, 4.8** (support of a slice): if `T = ξ μ` and `∂T = ξ' μ'` in `U`,
`A = T ⌞ {f < t}` and `B = (∂T) ⌞ {f < t}` (`f` continuous), then `∂A(η) = B(η)` for every
`η ∈ 𝒟ᵏ(U)` whose support misses the level set `{f = t}`; i.e. the slice `∂A − B` lives on
`{f = t}`.  Split `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {f > t}`
(`cmcs_ss_testForm_level_split`).  Below the level `∂A(η₁) = ∂T(η₁) = B(η₁)`
(`cmcs_ss_boundary_eq_of_tsupport_subset`); above it `∂A(η₂) = 0 = B(η₂)`
(`cmcs_ss_boundary_vanish_of_disjoint`), as `{f > t}` misses `{f < t}`.  Conclude by linearity
of `∂A` and `B`. -/
theorem Submission.cmcs_slice_support : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), Continuous f → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ η : TestFormOn U k, Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → A.boundary η = B η := by
  intro P k U T μ μ' ξ ξ' f t A B hf hT hbT hA hB η hη
  -- `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {t < f}`
  obtain ⟨η₁, η₂, rfl, h₁, h₂⟩ := Submission.cmcs_ss_testForm_level_split P k U f t η hf hη
  -- below the level: `∂A(η₁) = ∂T(η₁) = B(η₁)`
  have e₁ : A.boundary η₁ = B η₁ :=
    Submission.cmcs_ss_boundary_eq_of_tsupport_subset P k U T μ μ' ξ ξ' {x | f x < t} A B
      hT hbT hA hB η₁ h₁
  -- above the level: `∂A(η₂) = 0 = B(η₂)`, since `spt η₂ ⊆ {t < f}` misses `{f < t}`
  obtain ⟨e₂, e₂'⟩ := Submission.cmcs_ss_boundary_vanish_of_disjoint P k U μ μ' ξ ξ'
    {x | f x < t} A B hA hB η₂ (Set.disjoint_left.2 fun x hx hx' =>
      lt_asymm (show t < f x from h₂ hx) (show f x < t from hx'))
  -- `∂A` and `B` are linear
  rw [A.boundary.toCurrent.map_add, B.toCurrent.map_add, e₁, e₂, e₂']
/-- Integrability of the pairing `x ↦ ⟨ω(x), ξ(x)⟩`: if `μ` is finite on compact subsets of `U`,
`ξ` is `μ`-a.e. strongly measurable with `|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for
`μ`-a.e. `x`, and `ω ∈ 𝒟ⁿ(U)`, then `x ↦ ⟨ω(x), ξ(x)⟩` is `μ`-integrable.  The coefficient norm
`|ω(x)|` is continuous with compact support, hence bounded by some `M`, so the pairing is
dominated by `M` times the indicator of `spt ω`, which is integrable as `μ(spt ω) < ∞`. -/
theorem Submission.cmcs_smp_pairing_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (ω : TestFormOn U n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ := by
  intro P n U μ ξ ω hμ hξm hξ
  obtain ⟨w, ⟨hws, hwcs⟩, hwU⟩ := ω
  change Integrable (fun x => ξ x (w x)) μ
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous with compact support, hence bounded by some `M`
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  -- `(Λ, α) ↦ Λ α` is continuous, so the pairing is a.e. strongly measurable
  have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hmeas : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    hev.comp_aestronglyMeasurable₂ hξm hwc.aestronglyMeasurable
  -- domination by `M` times the indicator of `spt w`, integrable as `μ(spt w) < ∞`
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    (integrableOn_const (hμ _ hwcs hwU).ne)) hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs]
  by_cases hxK : x ∈ tsupport w
  · rw [indicator_of_mem hxK]
    exact (hx (w x)).trans ((Real.le_norm_self _).trans (hM x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    simp
/-- **Dominated convergence for level cut-offs** (step 5 of the slice mass bound in the proof of
Simon 7.2.4, cut-offs `g_h` of the level set `{f < t}`).  If `F` is `μ`-integrable, `f` is
measurable and, for `0 < h < 1`, `g_h` is a.e. strongly measurable with `|g_h| ≤ C`, `g_h = 1` on
`{f ≤ t − h}` and `g_h = 0` on `{t ≤ f}`, then `∫ g_h F dμ → ∫_{f < t} F dμ` as `h → 0+`.
Along `𝓝[>] 0` eventually `0 < h < 1`, so `|g_h F| ≤ C|F|` (integrable); for each `x`,
`g_h(x)F(x)` is eventually `1_{f<t}(x)F(x)` (for `h < min (t − f x) 1` if `f x < t`, for all
`h ∈ (0, 1)` if `t ≤ f x`); dominated convergence along the countably generated `𝓝[>] 0`. -/
theorem Submission.cmcs_smp_cutoff_integral_tendsto : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F f : Euclid P → ℝ) (t C : ℝ) (g : ℝ → Euclid P → ℝ), Integrable F μ → Measurable f → (∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) μ) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, |g h x| ≤ C) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, f x ≤ t - h → g h x = 1) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, t ≤ f x → g h x = 0) → Tendsto (fun h : ℝ => ∫ x, g h x * F x ∂μ) (𝓝[>] 0) (𝓝 (∫ x in {x | f x < t}, F x ∂μ)) := by
  intro P μ F f t C g hF hf hgm hgC hg1 hg0
  -- Step 2: eventually along `𝓝[>] 0`, `h ∈ (0, 1)`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- Step 1: `{f < t}` is measurable, so the limit is `∫ 1_{f<t} F dμ`
  have hs : MeasurableSet {x | f x < t} := measurableSet_lt hf measurable_const
  rw [← integral_indicator hs]
  -- Step 6: dominated convergence with the integrable bound `C‖F‖`
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖) ?_ ?_ ?_ ?_
  · -- Step 3: `g_h F` is a.e. strongly measurable for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    exact (hgm h hh.1 hh.2).mul hF.aestronglyMeasurable
  · -- Step 4: `|g_h F| ≤ C|F|` for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgC h hh.1 hh.2 x) (norm_nonneg _)
  · exact hF.norm.const_mul C
  · -- Step 5: `g_h(x)F(x)` is eventually equal to `1_{f<t}(x)F(x)`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : f x < t
    · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
      have hpos : 0 < min (t - f x) 1 := lt_min (by linarith) one_pos
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with h hh
      obtain ⟨h0, h1⟩ := hh
      have h1' : h < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have h2 : h < t - f x := lt_of_lt_of_le h1 (min_le_left _ _)
      rw [hg1 h h0 h1' x (by linarith), one_mul]
    · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with h hh
      rw [hg0 h hh.1 hh.2 x (not_lt.1 hx), zero_mul]
/-- **Simon Ch. 6, 4.9** (end of its proof, p. 158, where `b ↓ a` and then `ε ↓ 0`): if
`Φ(h) → z` as `h ↓ 0` and `|Φ(h)| ≤ L / (h (1 − h/2)) · v(h)` for `0 < h < 1`, then
`z ≤ L · liminf_{h ↓ 0} h⁻¹ v(h)` in `[0, ∞]`.  For `r > 1` eventually `(1 − h/2)⁻¹ < r`, so
`|z| = liminf |Φ(h)| ≤ r · L · liminf h⁻¹ v(h)`; then let `r ↓ 1`. -/
theorem Submission.cmcs_smp_liminf_bound : ∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0) := by
  intro L z Φ v hΦ hb
  set X := (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)
  -- step 1: `(0, 1) ∈ 𝓝[>] 0`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- step 2: `ofReal |Φ h| → ofReal |z|`
  have hlimΦ : Tendsto (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |z|)) :=
    ENNReal.tendsto_ofReal hΦ.abs
  -- step 3: `ofReal z ≤ ofReal r * X` for every `r > 1`
  have key : ∀ r : ℝ, 1 < r → ENNReal.ofReal z ≤ ENNReal.ofReal r * X := by
    intro r hr
    -- 3a: `(1 - h / 2)⁻¹ → 1`, so eventually `(1 - h / 2)⁻¹ < r`
    have hcont : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝 0) (𝓝 (1 - 0 / 2)⁻¹) :=
        (tendsto_const_nhds.sub (tendsto_id.div_const 2)).inv₀ (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hevr : ∀ᶠ h in 𝓝[>] (0 : ℝ), (1 - h / 2)⁻¹ < r := hcont.eventually (gt_mem_nhds hr)
    calc ENNReal.ofReal z ≤ ENNReal.ofReal |z| := ENNReal.ofReal_le_ofReal (le_abs_self z)
      _ = liminf (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) := hlimΦ.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)))
            (𝓝[>] 0) := by
          -- 3b, 3c: the eventual pointwise bound and monotonicity of `liminf`
          refine liminf_le_liminf ?_
          filter_upwards [hev, hevr] with h ⟨h0, h1⟩ hhr
          have h2 : 0 < 1 - h / 2 := by linarith
          have heq : (L : ℝ) / (h * (1 - h / 2)) = (1 - h / 2)⁻¹ * ((L : ℝ) * h⁻¹) := by
            field_simp
          calc ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h :=
                hb h h0 h1
            _ = ENNReal.ofReal (1 - h / 2)⁻¹ * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                rw [heq, ENNReal.ofReal_mul (inv_nonneg.2 h2.le),
                  ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
                ring
            _ ≤ ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                gcongr
      _ = ENNReal.ofReal r * X := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  -- step 4: let `r ↓ 1`
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have htend : Tendsto (fun r : ℝ => ENNReal.ofReal r * X) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * X)) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds) (Or.inr hXtop)
    simpa using ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun r hr => key r hr)
/-- Strip estimate (Simon Ch. 6, 4.11: the bound for the right side `R` of 4.11): if `‖Dg‖ ≤ c`,
`Dg` vanishes off `S`, `spt η ⊆ W` and `|η| ≤ 1`, then `∫⁻ ‖Dg‖ |η| dμ ≤ c μ(W ∩ S)`.  The
integrand is dominated by `c 𝟙_{W ∩ S}`: on `W \ S` it vanishes because `Dg = 0`, off `W` because
`η = 0`.  No measurability is needed, as `∫⁻ c 𝟙_A dμ ≤ c μ(A)` for every set `A`. -/
theorem Submission.cmcs_smp_strip_lintegral_le : ∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S) := by
  intro P k μ g η W S c hc hS hW hη
  -- the integrand is dominated by the indicator of `W ∩ S` with value `ofReal c`
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_indicator_const_le (W ∩ S) (ENNReal.ofReal c))
  show ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ≤
    (W ∩ S).indicator (fun _ => ENNReal.ofReal c) x
  by_cases hx : x ∈ W ∩ S
  · rw [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal
      ((mul_le_of_le_one_right (norm_nonneg _) (hη x)).trans (hc x))
  · rw [indicator_of_notMem hx]
    -- off `W ∩ S` a factor vanishes: `Dg(x) = 0` on `W \ S` and `η(x) = 0` off `W`
    have h0 : ‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x) = 0 := by
      by_cases hxW : x ∈ W
      · obtain hD | hD := eq_or_ne (fderiv ℝ g x) 0
        · rw [hD, norm_zero, zero_mul]
        · exact absurd ⟨hxW, hS x hD⟩ hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxW (hW h)
        rw [hηx, covectorEuclideanNorm_zero, mul_zero]
    rw [h0, ENNReal.ofReal_zero]
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
/-- **Orthonormal basis adapted to a linear functional** (used for the wedge-norm bound
`|β ∧ γ| ≤ ‖β‖ |γ|`, Simon 6.1): for a continuous linear functional `β` on `ℝᴾ` and `i₀ : Fin P`
there is an orthonormal basis `f` of `ℝᴾ` with `β(f_{i₀}) = ‖β‖` and `β(f_i) = 0` for `i ≠ i₀`.
Write `β = ⟨b, ·⟩` (Riesz, `‖b‖ = ‖β‖`).  If `b = 0`, the standard basis `e` works.  Otherwise the
reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ`, `u = ‖b‖⁻¹ b`, maps `e_{i₀}` to `u`, and `f = R ∘ e` has
`β(f_i) = ‖b‖ ⟨R e_{i₀}, R e_i⟩ = ‖b‖ ⟨e_{i₀}, e_i⟩`. -/
theorem Submission.cmcs_wn_adapted_orthonormalBasis : ∀ (P : ℕ) (β : Euclid P →L[ℝ] ℝ) (i₀ : Fin P), ∃ f : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, β (f i) = if i = i₀ then ‖β‖ else 0 := by
  intro P β i₀
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Riesz representative: `β x = ⟪b, x⟫` and `‖b‖ = ‖β‖`
  set b : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm β with hb
  have hβb : ∀ x, β x = inner ℝ b x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hnorm : ‖b‖ = ‖β‖ := by
    rw [hb, LinearIsometryEquiv.norm_map]
  by_cases hb0 : b = 0
  · -- `β = 0`: the standard basis works
    refine ⟨e, fun i => ?_⟩
    have h0 : ‖β‖ = 0 := by rw [← hnorm, hb0, norm_zero]
    rw [hβb, hb0, inner_zero_left, h0, ite_self]
  · -- `u = ‖b‖⁻¹ b` is a unit vector and `b = ‖b‖ u`
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    set u : Euclid P := ‖b‖⁻¹ • b with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
    have hbu : b = ‖b‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
    -- the reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ` maps `e_{i₀}` to `u`
    have he : ‖e i₀‖ = 1 := e.orthonormal.1 i₀
    set R := (ℝ ∙ (e i₀ - u))ᗮ.reflection
    have hR : R (e i₀) = u := Submodule.reflection_sub (he.trans hu.symm)
    -- `f = R ∘ e`: `β(f_i) = ‖b‖ ⟪R e_{i₀}, R e_i⟫ = ‖β‖ ⟪e_{i₀}, e_i⟫`
    refine ⟨e.map R, fun i => ?_⟩
    rw [OrthonormalBasis.map_apply, hβb, hbu, real_inner_smul_left, ← hR,
      LinearIsometryEquiv.inner_map_map, hnorm, orthonormal_iff_ite.mp e.orthonormal i₀ i]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi.symm, ite_eq_left hi, mul_one]
    · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, mul_zero]
/-- **`β ∧ γ` on tuples of a family adapted to `β`** (Simon 6.1.1–1.3; step 4 of the proof of
`|β ∧ γ| ≤ ‖β‖ |γ|`): if `β(v_a) = c` for `a = i₀` and `β(v_a) = 0` otherwise, then for every
`j : Fin (k + 1) → Fin P`, `(β ∧ γ)(v_{j(0)}, …, v_{j(k)})² ≤ c² Σ_{i, j(i) = i₀} γ(v ∘ ĵᵢ)²`,
where `ĵᵢ = i.removeNth j` deletes the `i`-th entry of `j`.  By definition
`(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`.  A repeated index in `j` makes `v ∘ j`
non-injective, so the left side vanishes (alternation); otherwise at most one `i₁` has
`j(i₁) = i₀`, only `i₁` contributes to either side, and `((−1)^{i₁})² = 1`. -/
theorem Submission.cmcs_wn_tuple_sq_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k) (v : Fin P → Euclid P) (i₀ : Fin P) (c : ℝ), Function.Injective v → (∀ i : Fin P, β (v i) = if i = i₀ then c else 0) → ∀ j : Fin (k + 1) → Fin P, (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ) (fun m => v (j m))) ^ 2 ≤ c ^ 2 * ∑ i : Fin (k + 1), if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0 := by
  intro P k β γ v i₀ c _hv hβ j
  classical
  -- the right side is `c²` times a sum of squares and zeros
  have hRHS : 0 ≤ c ^ 2 * ∑ i : Fin (k + 1),
      (if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0) :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  by_cases hj : Injective j
  · -- `(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`, with `β(v_{j(i)}) = c [j(i) = i₀]`
    have hexp : ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
        (fun m => v (j m)) = ∑ i : Fin (k + 1),
          (-1 : ℝ) ^ (i : ℕ) *
            ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, hβ (j i)]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [hexp]
    by_cases hex : ∃ i₁, j i₁ = i₀
    · -- `j` is injective, so `i₁` is the only index with `j(i₁) = i₀`
      obtain ⟨i₁, hi₁⟩ := hex
      have huniq : ∀ i, i ≠ i₁ → j i ≠ i₀ := fun i hi h => hi (hj (h.trans hi₁.symm))
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by rw [ite_eq_right (huniq i hi)]; ring)
          (fun h => absurd (Finset.mem_univ i₁) h),
        Finset.sum_eq_single i₁ (fun i _ hi => ite_eq_right (huniq i hi))
          (fun h => absurd (Finset.mem_univ i₁) h),
        ite_eq_left hi₁, ite_eq_left hi₁]
      have hsign : ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      refine le_of_eq ?_
      calc ((-1 : ℝ) ^ (i₁ : ℕ) * (c * γ (fun m => v (i₁.removeNth j m)))) ^ 2
          = ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 * (c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2) := by
            ring
        _ = c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2 := by rw [hsign, one_mul]
    · -- no index hits `i₀`: every term vanishes
      have h0 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
          ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ite_eq_right fun h => hex ⟨i, h⟩]; ring
      rw [h0]
      simpa using hRHS
  · -- a repeated index makes `v ∘ j` non-injective, and `β ∧ γ` is alternating
    have hvj : ¬ Injective (fun m => v (j m)) := fun h => hj (Injective.of_comp (f := v) h)
    rw [ContinuousAlternatingMap.map_eq_zero_of_not_injective _ _ hvj]
    simpa using hRHS
/-- **Fibres of `j ↦ removeNth i j`** (the counting step of the bound `|β ∧ γ| ≤ ‖β‖ |γ|` for the
Euclidean norm of covectors, Simon Ch. 6, 1.1–1.3, 1.15): for `i₀ : Fin P` and
`F : (Fin k → Fin P) → ℝ`,
`Σ_{j : Fin (k+1) → Fin P} Σ_i [j i = i₀] F(removeNth i j) = (k + 1) Σ_{j' : Fin k → Fin P} F j'`.
For fixed `i`, `j ↦ (j i, removeNth i j)` is a bijection onto `Fin P × (Fin k → Fin P)`
(`Fin.insertNthEquiv`), so only `j i = i₀` survives and each of the `k + 1` indices `i`
contributes `Σ_{j'} F j'`. -/
theorem Submission.cmcs_wn_removeNth_fiber_sum : ∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j' := by
  intro k P i₀ F
  rw [Finset.sum_comm]
  -- for fixed `i`, reindex along `j ↦ (j i, removeNth i j)`; only `j i = i₀` survives
  have hfib : ∀ i : Fin (k + 1),
      ∑ j : Fin (k + 1) → Fin P, (if j i = i₀ then F (i.removeNth j) else 0) =
        ∑ j' : Fin k → Fin P, F j' := by
    intro i
    rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin P) i).symm
      (fun j => if j i = i₀ then F (i.removeNth j) else 0)
      (fun p => if p.1 = i₀ then F p.2 else 0) fun _ => rfl,
      Fintype.sum_prod_type, Fintype.sum_eq_single i₀]
    · simp
    · intro x hx
      simp [hx]
  -- each of the `k + 1` indices `i` contributes `Σ_{j'} F j'`
  rw [Finset.sum_congr rfl fun i _ => hfib i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add_one]
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

/-- **`|β ∧ γ| ≤ ‖β‖ |γ|`** (Simon 6.1.1–1.3 and 1.15): for a linear functional `β` and a
`k`-covector `γ` on `ℝᴾ`, the Euclidean coefficient norm of the `(k+1)`-covector
`β ∧ γ = alternatizeUncurryFin (β.smulRight γ)` is at most `‖β‖ |γ|`.  Take an orthonormal basis
`f` with `β(fᵢ) = ‖β‖ [i = i₀]`; then `(β ∧ γ)(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²`.
Summing over `j`, each `j' : Fin k → Fin P` arises as `i.removeNth j` with `j i = i₀` for exactly
`k + 1` pairs `(i, j)`, so `(k+1)! |β ∧ γ|² ≤ ‖β‖² (k+1) k! |γ|²` by
`regcomp_covector_sq_sum_orthonormalBasis` in degrees `k + 1` and `k`.  For `P = 0` there are no
coordinate tuples and `|β ∧ γ| = 0`. -/
theorem Submission.cmcs_wedge_norm_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ := by
  intro P k β γ
  classical
  set ω := ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
  have hrhs : 0 ≤ ‖β‖ * covectorEuclideanNorm γ :=
    mul_nonneg (norm_nonneg β) (covectorEuclideanNorm_nonneg γ)
  rcases Nat.eq_zero_or_pos P with hP | hP
  · -- `P = 0`: there is no tuple `Fin (k + 1) → Fin 0`, so `|ω| = 0`
    subst hP
    have h0 : covectorEuclideanNorm ω = 0 := by
      simp [covectorEuclideanNorm]
    rw [h0]
    exact hrhs
  · -- an orthonormal basis `f` with `β(fᵢ) = ‖β‖ [i = i₀]`
    set i₀ : Fin P := ⟨0, hP⟩
    obtain ⟨f, hf⟩ := Submission.cmcs_wn_adapted_orthonormalBasis P β i₀
    -- `ω(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²` for every `j`
    have hle : ∑ j : Fin (k + 1) → Fin P, (ω (fun m => f (j m))) ^ 2 ≤
        ∑ j : Fin (k + 1) → Fin P, ‖β‖ ^ 2 * ∑ i : Fin (k + 1),
          (if j i = i₀ then (γ (fun m => f (i.removeNth j m))) ^ 2 else 0) :=
      Finset.sum_le_sum fun j _ => Submission.cmcs_wn_tuple_sq_le P k β γ f i₀ ‖β‖
        f.orthonormal.linearIndependent.injective hf j
    -- count the fibres of `j ↦ i.removeNth j`, then `Σ_j α(f ∘ j)² = m! |α|²` for `m = k + 1, k`
    rw [← Finset.mul_sum,
      Submission.cmcs_wn_removeNth_fiber_sum k P i₀ (fun j' => (γ (fun m => f (j' m))) ^ 2),
      Submission.regcomp_covector_sq_sum_orthonormalBasis P (k + 1) ω f,
      Submission.regcomp_covector_sq_sum_orthonormalBasis P k γ f] at hle
    -- cancel `(k+1)! = (k+1) k! > 0`
    have hpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hsq : covectorEuclideanNorm ω ^ 2 ≤ (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm ω ^ 2
          ≤ ‖β‖ ^ 2 * (((k : ℝ) + 1) * ((k.factorial : ℝ) * covectorEuclideanNorm γ ^ 2)) := hle
        _ = ((k + 1).factorial : ℝ) * (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
          push_cast [Nat.factorial_succ]
          ring
    exact (sq_le_sq₀ (covectorEuclideanNorm_nonneg ω) hrhs).mp hsq

/-- **Simon Ch. 6, 4.11 (p. 158), the estimate of the cutoff defect**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')` with `|⟨α, ξ⟩| ≤ |α|` `μ`-a.e.: for a `C^∞` function `g`
and `η ∈ 𝒟ᵏ(U)`, `|∫ g ⟨dη, ξ⟩ dμ − ∫ g ⟨η, ξ'⟩ dμ'| ≤ ∫ |Dg| |η| dμ` in `[0, ∞]`.  The left side
is `|T(g dη) − ∂T(gη)| = |T(dg ∧ η)| = |∫ ⟨dg ∧ η, ξ⟩ dμ|` (`cmcs_cd_defect_identity`, with
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`), which is at most `∫ |⟨dg ∧ η, ξ⟩| dμ` whether
or not the integrand is integrable; and `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|` `μ`-a.e. by the bound
on `ξ` and `cmcs_wedge_norm_le`. -/
theorem Submission.cmcs_cutoff_defect_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ENNReal.ofReal |∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ'| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((η : DifferentialForm (Euclid P) k) x)) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hξ hT hbT hg
  -- Simon 4.11: `T(g dη) − ∂T(gη) = −T(dg ∧ η) = −∫ ⟨dg ∧ η, ξ⟩ dμ`
  rw [Submission.cmcs_cd_defect_identity P k U T μ μ' ξ ξ' g η hT hbT hg, abs_neg,
    ← Real.enorm_eq_ofReal_abs]
  -- `‖∫ G dμ‖ₑ ≤ ∫⁻ ‖G‖ₑ dμ` for every `G`, integrable or not; then bound `G` `μ`-a.e.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hξ] with x hx
  -- `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|`
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((hx _).trans (Submission.cmcs_wedge_norm_le P k _ _))
/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- **A unit covector attaining `1` on an orthonormal frame** (Simon (6.1.1); step 1(b) of the
mass formula, Remark 6.3.2(3)): every orthonormal `τ₁, …, τₙ` in `ℝᴾ` admits an `n`-covector `β`
with `|β|_E = 1` and `β(τ) = 1`.  Take the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors
`⟨τᵢ, ·⟩`, so `β(τ) = det 1 = 1`.  Extend `τ` to an orthonormal basis `f` of `ℝᴾ` with
`f ∘ ι = τ`, `ι = Fin.castLE`.  Then `β(f ∘ j) = sgn π` if `j = ι ∘ π` for a permutation `π`,
and `β(f ∘ j) = 0` otherwise (a zero column, or a repeated vector), so `Σ_j β(f ∘ j)² = n!`;
`regcomp_covector_sq_sum_orthonormalBasis` turns this into `n! = n! |β|_E²`. -/
theorem Submission.regcomp_exists_covector_eval_orthonormal_eq_one : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1 := by
  intro P n τ hτ
  classical
  -- Step 1: the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors `⟨τᵢ, ·⟩` (Simon (6.1.1))
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n, ∀ v : Fin n → Euclid P,
      β v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => (innerSL ℝ (τ i) : Euclid P →L[ℝ] ℝ).toLinearMap
    let g : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hg : ∀ v, g v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      intro v
      rw [← Matrix.det_transpose]
      show Matrix.det (Matrix.of fun a b => L (v a) b) = _
      congr 1
    have hcont : Continuous fun v : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i k
      exact Continuous.inner (f := fun _ => τ i) (g := fun v : Fin n → Euclid P => v k)
        continuous_const (continuous_apply k)
    refine ⟨{ g with cont := ?_ }, hg⟩
    have : (g : (Fin n → Euclid P) → ℝ) =
        fun v => Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := funext hg
    simpa [this] using hcont
  -- Step 2: by orthonormality `(⟨τᵢ, τ_k⟩) = 1`, so `β(τ) = det 1 = 1`
  have hβτ : β τ = 1 := by
    have hone : (Matrix.of fun i k => inner ℝ (τ i) (τ k) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i k
      rw [Matrix.of_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.mp hτ i k
    rw [hβ, hone, Matrix.det_one]
  -- Step 3: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 4: `β(f ∘ j)² = 1` if `j = ι ∘ π` for a permutation `π`, and `0` otherwise
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), β (fun k => f (Φ π k)) ^ 2 = 1 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : β (τ ∘ π) = Equiv.Perm.sign π • β τ := β.toAlternatingMap.map_perm τ π
    rw [h1, h2, hβτ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hzero : ∀ j : Fin n → Fin P, j ∉ Finset.univ.image Φ → β (fun k => f (j k)) ^ 2 = 0 := by
    intro j hj
    have hj' : ∀ π, Φ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
    rw [sq_eq_zero_iff]
    by_cases hr : ∀ k, j k ∈ range ι
    · -- `j = ι ∘ ρ` with `ρ` not a permutation, hence not injective: `f ∘ j` repeats a vector
      choose ρ hρ using hr
      have hρ' : ¬ Injective ρ := fun hinj =>
        hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
      refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
      exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
    · -- some `j k₀ ∉ range ι`: column `k₀` of `(⟨τᵢ, f (j k)⟩)` vanishes
      obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
      rw [hβ]
      refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
      rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
  have hsum : ∑ j : Fin n → Fin P, β (fun k => f (j k)) ^ 2 = n.factorial := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) fun j _ hj => hzero j hj,
      Finset.sum_image fun π _ π' _ h => hΦ h]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- Step 5: `n! = n! |β|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`, so `|β|_E = 1`
  have hsq := Submission.regcomp_covector_sq_sum_orthonormalBasis P n β f
  rw [hsum] at hsq
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine ⟨β, (pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β) two_ne_zero).mp ?_, hβτ⟩
  exact mul_left_cancel₀ hfac (by rw [← hsq, mul_one])
/-- `Hⁿ(Q ∩ B_ρ(y)) = ωₙρⁿ` for an `n`-dimensional linear subspace `Q` of `ℝᴾ`, `y ∈ Q` and
`ρ > 0` (used in the proof of Simon 7.3.3(1), p. 191, for the density of the planes of a
2-dimensional minimizing cone).  The inclusion `Q → ℝᴾ` is an isometry, so `Q ∩ B_ρ(y)` has the
measure of the ball `B_ρ(y)` of `Q`; on `Q`, `μHE[n]` is the volume, Haar scaling gives
`vol(B_ρ(y)) = ρⁿ vol(B_1(0))`, and orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume, so
`vol(B_1(0)) = ωₙ`. -/
theorem Submission.idtp_tdc_subspace_ball_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (y : Euclid P) (ρ : ℝ), Module.finrank ℝ Q = n → y ∈ Q → 0 < ρ → μHE[n] ((Q : Set (Euclid P)) ∩ ball y ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) := by
  intro P n Q y ρ hn hy hρ
  subst hn
  -- the inclusion `Q → ℝᴾ` is an isometry with range `Q`; `B_ρ(y)` pulls back to the ball of `Q`
  have hball : μHE[Module.finrank ℝ Q] ((Q : Set (Euclid P)) ∩ ball y ρ) =
      μHE[Module.finrank ℝ Q] (ball (⟨y, hy⟩ : Q) ρ) := by
    rw [← isometry_subtype_coe.preimage_ball (⟨y, hy⟩ : Q) ρ,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage, Subtype.range_coe, Set.inter_comm]
  -- orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume and map `B_1(0)` onto `B_1(0)`
  have hunit := (stdOrthonormalBasis ℝ Q).measurePreserving_repr.measure_preimage
    (measurableSet_ball (x := (0 : Euclid (Module.finrank ℝ Q))) (ε := 1)).nullMeasurableSet
  rw [LinearIsometryEquiv.preimage_ball, map_zero] at hunit
  -- `μHE[n] = volume` on `Q`, then Haar scaling of balls
  rw [hball, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, hunit, mul_comm]
  rfl
/-- **Exterior derivative of a function times a constant covector** (used for the boundary weak
derivatives in the graph-cycle regularity step of Simon 7.4.3).  If `a : ℝᴾ → ℝ` is
differentiable at `x` and `β` is a fixed `m`-covector, then
`d(a β)(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ Da(x)wᵢ · β(w₀, …, ŵᵢ, …, w_m)`, i.e. `d(a β) = da ∧ β`:
each term of the alternating sum differentiates `y ↦ a(y) β(w₀, …, ŵᵢ, …, w_m)`. -/
theorem Submission.dgcr_bwd_extDeriv_smul_const : ∀ (P m : ℕ) (a : Euclid P → ℝ) (β : Covector (Euclid P) m) (x : Euclid P) (w : Fin (m + 1) → Euclid P), DifferentiableAt ℝ a x → exteriorDerivative (fun y => a y • β) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ a x (w i) * β (i.removeNth w)) := by
  intro P m a β x w ha
  rw [exteriorDerivative_apply (ha.smul_const β) w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (fun y => (a y • β) (i.removeNth w)) = fun y => a y * β (i.removeNth w) := by
    funext y
    simp [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [h1, fderiv_mul_const ha]
  simp [zsmul_eq_mul, mul_comm]
/-- **Translation invariance on smooth tests** (steps 1–3 of the translation argument): if `ν` is
finite on compact sets and `∫ Dφ(y)[v] dν(y) = 0` for every `φ ∈ C_c^∞(ℝᴾ)`, then
`∫ φ(v + y) dν(y) = ∫ φ dν` for every `φ ∈ C_c^∞(ℝᴾ)`.  `F(s) = ∫ φ(y + sv) dν(y)` is
differentiable with `F'(s₀) = ∫ Dφ(y + s₀v)[v] dν(y)` (differentiation under the integral sign;
for `|s − s₀| < 1` the derivative is dominated by `C‖v‖ 1_{K₀}`, `K₀ = B̄_{R + (|s₀| + 1)‖v‖}(0)`,
`tsupport φ ⊆ B̄_R(0)`, `‖Dφ‖ ≤ C`), and `F'(s₀) = 0` by the hypothesis applied to the translate
`φ(· + s₀v)`.  So `F` is constant and `F(1) = F(0)`. -/
theorem Submission.cbr_ci_cp_tr_smooth_translate_integral_eq : ∀ (P : ℕ) (ν : Measure (Euclid P)) (v : Euclid P), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, φ (v + y) ∂ν = ∫ y, φ y ∂ν := by
  intro P ν v hν hD φ hφ hφs
  -- step 1: `ν` is finite on compact sets
  have hνK : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  -- step 2: `Dφ` is continuous, vanishes off `tsupport φ` and is bounded by `C`;
  -- `tsupport φ ⊆ B̄_R(0)`
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support (hφs.fderiv ℝ)
  obtain ⟨R, hR⟩ := hφs.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  -- step 5: `F(s) = ∫ φ(y + s v) dν` has derivative `∫ Dφ(y + s v)[v] dν` at every `s₀`
  have hF : ∀ s₀ : ℝ, HasDerivAt (fun s : ℝ => ∫ y, φ (y + s • v) ∂ν)
      (∫ y, fderiv ℝ φ (y + s₀ • v) v ∂ν) s₀ := by
    intro s₀
    have hK₀ : IsCompact (closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)) :=
      isCompact_closedBall _ _
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun (s : ℝ) (y : Euclid P) => φ (y + s • v))
      (F' := fun (s : ℝ) (y : Euclid P) => fderiv ℝ φ (y + s • v) v)
      (bound := (closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)).indicator fun _ => C * ‖v‖)
      (ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
    · -- (a) `y ↦ φ(y + s v)` is continuous
      exact Eventually.of_forall fun s =>
        (hφ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · -- (b) `y ↦ φ(y + s₀ v)` is continuous with compact support
      exact (hφ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (hφs.comp_homeomorph (Homeomorph.addRight (s₀ • v)))
    · -- (c) `y ↦ Dφ(y + s₀ v)[v]` is continuous
      exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (hφc.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    · -- (d) the domination `|Dφ(y + s v)[v]| ≤ C ‖v‖ 1_{K₀}(y)` for `|s - s₀| < 1`
      refine Eventually.of_forall fun y s hs => ?_
      by_cases hy : y ∈ closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)
      · rw [indicator_of_mem hy]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        -- step 4: `y ∉ K₀` forces `y + s v ∉ tsupport φ`
        have hys : y + s • v ∉ tsupport φ := by
          intro h
          apply hy
          have h1 := hR h
          rw [mem_closedBall_zero_iff] at h1 ⊢
          rw [mem_ball, Real.dist_eq] at hs
          have hs' : |s| ≤ |s₀| + 1 := by
            linarith [abs_sub_abs_le_abs_sub s s₀]
          calc ‖y‖ = ‖(y + s • v) - s • v‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖y + s • v‖ + ‖s • v‖ := norm_sub_le _ _
            _ = ‖y + s • v‖ + |s| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ R + (|s₀| + 1) * ‖v‖ :=
              add_le_add h1 (mul_le_mul_of_nonneg_right hs' (norm_nonneg _))
        rw [fderiv_of_notMem_tsupport ℝ hys]
        simp
    · -- (e) `C ‖v‖ 1_{K₀}` is integrable since `ν(K₀) < ∞`
      exact IntegrableOn.integrable_indicator (integrableOn_const hK₀.measure_lt_top.ne)
        measurableSet_closedBall
    · -- (f) chain rule for `s ↦ φ(y + s v)`
      refine Eventually.of_forall fun y s _ => ?_
      have h1 : HasDerivAt (fun s : ℝ => y + s • v) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add y
      exact (hφd (y + s • v)).hasFDerivAt.comp_hasDerivAt s h1
  -- step 6: `F' ≡ 0`, by the hypothesis applied to the translate `φ(· + s₀ v)`
  have hF0 : ∀ s₀ : ℝ, ∫ y, fderiv ℝ φ (y + s₀ • v) v ∂ν = 0 := by
    intro s₀
    have h := hD (fun y => φ (y + s₀ • v)) (hφ.comp (contDiff_id.add contDiff_const))
      (hφs.comp_homeomorph (Homeomorph.addRight (s₀ • v)))
    simpa only [fderiv_comp_add_right] using h
  -- step 7: `F` is constant, so `F(1) = F(0)`
  have h := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => by rw [(hF s).deriv, hF0 s]) 1 0
  simpa [add_comm] using h
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Smooth cut-off between two levels of a Lipschitz function** (Simon Ch. 6, proof of 4.9, with
`f^{(σ)}` in place of `f`).  If `f : ℝᴾ → ℝ` is `L`-Lipschitz, `t ∈ ℝ` and `0 < h < 1`, there is a
`C^∞` function `g` with `|g| ≤ 2`, `‖Dg‖ ≤ L/(h(1 − h/2))`, `g = 1` on `{f ≤ t − h}`, `g = 0` on
`{f ≥ t}` and `Dg = 0` off the strip `{t − h < f < t}`.  With `δ = h²/4` and
`w = h − 2δ = h(1 − h/2)`, the clamp `G = max 0 (min 1 ((t − δ − f)/w))` is `(L/w)`-Lipschitz,
`G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`; `g` is its smoothing at scale
`σ = δ/(2(L + 1))` (`cmcs_lipschitz_smoothing`), so `|g − G| ≤ Lσ/w ≤ 1`.  As `2Lσ < δ`, `G` is
constant on `B_{2σ}(x)` when `f x ≤ t − h` or `t ≤ f x`; by locality `g` is then constant on
`B_σ(x)`, so `Dg(x) = 0`. -/
theorem Submission.cmcs_level_cutoff : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (t h : ℝ), LipschitzWith L f → 0 < h → h < 1 → ∃ g : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧ (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧ (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
  intro P f L t h hf h0 h1
  -- parameters `δ = h²/4`, `w = h − 2δ = h(1 − h/2)` and `σ = δ/(2(L + 1))`, so `2Lσ < δ`
  set δ : ℝ := h ^ 2 / 4 with hδ
  set w : ℝ := h * (1 - h / 2) with hw
  have hw0 : 0 < w := mul_pos h0 (by linarith)
  have hδ0 : 0 < δ := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set σ : ℝ := δ / (2 * ((L : ℝ) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have h2Lσ : 2 * (L : ℝ) * σ < δ := by
    rw [hσ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the clamped profile `G = max 0 (min 1 ((t − δ − f)/w))`: `(L/w)`-Lipschitz, `|G| ≤ 1`,
  -- `G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`
  set G : Euclid P → ℝ := fun x => max 0 (min 1 ((t - δ - f x) / w)) with hGdef
  set K : NNReal := L * Real.toNNReal w⁻¹ with hK
  have hKr : (K : ℝ) = L / w := by
    rw [hK, NNReal.coe_mul, Real.coe_toNNReal _ (inv_pos.2 hw0).le, div_eq_mul_inv]
  have hG : LipschitzWith K G := by
    have hlin : LipschitzWith K fun x => (t - δ - f x) / w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hxy := hf.dist_le_mul x y
      rw [Real.dist_eq] at hxy
      rw [Real.dist_eq, hKr, show (t - δ - f x) / w - (t - δ - f y) / w = (f y - f x) / w by ring,
        abs_div, abs_of_pos hw0, abs_sub_comm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxy hw0.le
    exact (hlin.const_min 1).const_max 0
  have hG01 : ∀ y, |G y| ≤ 1 := by
    intro y
    simp only [hGdef]
    rw [abs_le]
    exact ⟨by linarith [le_max_left 0 (min 1 ((t - δ - f y) / w))],
      max_le zero_le_one (min_le_left _ _)⟩
  have hG1 : ∀ y, f y < t - h + δ → G y = 1 := by
    intro y hy
    have : 1 ≤ (t - δ - f y) / w := by rw [le_div_iff₀ hw0]; linarith
    simp [hGdef, min_eq_left this]
  have hG0 : ∀ y, t - δ < f y → G y = 0 := by
    intro y hy
    have : (t - δ - f y) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
    simp only [hGdef]
    exact max_eq_left ((min_le_right _ _).trans this)
  -- smoothing of `G` at scale `σ`
  obtain ⟨g, hgs, hgd, hga, hgl⟩ := Submission.cmcs_lipschitz_smoothing P G K σ hG hσ0
  -- plateaus: if `G = c` on `B_{2σ}(x)`, then `g = c` on `B_σ(x)`, so `g x = c` and `Dg(x) = 0`
  have hnear : ∀ x, ∀ c : ℝ, (∀ y ∈ ball x (2 * σ), G y = c) → g x = c ∧ fderiv ℝ g x = 0 := by
    intro x c hc
    have hball : ∀ x' ∈ ball x σ, g x' = c := fun x' hx' => hgl x' c fun y hy => hc y (by
      rw [mem_ball] at hx' hy ⊢
      linarith [dist_triangle y x' x])
    have hev : g =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (ball_mem_nhds x hσ0) hball
    exact ⟨hball x (mem_ball_self hσ0), hev.fderiv_eq.trans (fderiv_const_apply c)⟩
  -- on `B_{2σ}(x)`, `|f y − f x| ≤ L |y − x| < 2Lσ < δ`
  have hclose : ∀ x, ∀ y ∈ ball x (2 * σ), |f y - f x| < δ := by
    intro x y hy
    have hd := hf.dist_le_mul y x
    rw [Real.dist_eq] at hd
    rw [mem_ball] at hy
    have : (L : ℝ) * dist y x ≤ L * (2 * σ) := mul_le_mul_of_nonneg_left hy.le hL0
    linarith
  have hlow : ∀ x, f x ≤ t - h → g x = 1 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 1 fun y hy => hG1 y (by linarith [(abs_lt.1 (hclose x y hy)).2])
  have hup : ∀ x, t ≤ f x → g x = 0 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 0 fun y hy => hG0 y (by linarith [(abs_lt.1 (hclose x y hy)).1])
  refine ⟨g, hgs, fun x => ?_, fun x => (hgd x).trans_eq hKr, fun x hx => ?_,
    fun x hx => (hlow x hx).1, fun x hx => (hup x hx).1⟩
  · -- `|g| ≤ |G| + Kσ ≤ 2`, as `Kσ = Lδ/(2(L + 1)w) ≤ 1` (`δ ≤ 2w`)
    have hKσ : (K : ℝ) * σ ≤ 1 := by
      rw [hKr, hσ, div_mul_div_comm, div_le_one (by positivity)]
      have hδw : δ ≤ 2 * w := by rw [hδ, hw]; nlinarith
      nlinarith
    linarith [abs_sub_abs_le_abs_sub (g x) (G x), hga x, hG01 x]
  · -- `Dg = 0` on both plateaus, so `Dg(x) ≠ 0` forces `t − h < f x < t`
    by_contra hcon
    rcases not_and_or.1 hcon with hc | hc
    · exact hx (hlow x (not_lt.1 hc)).2
    · exact hx (hup x (not_lt.1 hc)).2

/-- **Mass of a slice, pointwise in `t`** (Simon 6.4.9, proved as in 6.4.11): let `T = ξ μ`,
`∂T = ξ' μ'` with `|ξ|, |ξ'| ≤ 1`, let `f` be `L`-Lipschitz, and let `A = T ⌞ {f < t}`,
`B = (∂T) ⌞ {f < t}`.  Then `M_W(∂A − B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})`.
For an admissible `η` and `h ∈ (0, 1)`, the smooth cut-off `g_h` of `cmcs_level_cutoff` gives
`Φ_h = ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'` with `|Φ_h| ≤ ∫ |Dg_h| |η| dμ ≤ c_h μ(W ∩ S_h)`,
`c_h = L / (h(1 − h/2))`, `S_h = {t − h < f < t}` (`cmcs_cutoff_defect_bound`,
`cmcs_smp_strip_lintegral_le`); `Φ_h → (∂A − B)(η)` by dominated convergence
(`cmcs_smp_cutoff_integral_tendsto`), and `cmcs_smp_liminf_bound` passes to the liminf. -/
theorem Submission.cmcs_slice_mass_pointwise : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro P k U T μ μ' ξ ξ' f L t A B W hμ hμ' hξm hξm' hξ hξ' hT hbT hf hA hB
  -- Step 3: a cut-off `g h` for every `h ∈ (0, 1)` (junk value `0` for other `h`).
  have hcut : ∀ h : ℝ, ∃ g : Euclid P → ℝ, 0 < h → h < 1 →
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧
        (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧
        (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧
        (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
    intro h
    by_cases hh : 0 < h ∧ h < 1
    · obtain ⟨g, hg⟩ := Submission.cmcs_level_cutoff P f L t h hf hh.1 hh.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨0, fun h0 h1 => (hh ⟨h0, h1⟩).elim⟩
  choose g hg using hcut
  -- Step 1: it suffices to bound `ofReal ((∂A − B) η)` for one admissible `η`.
  apply sSup_le
  rintro r ⟨η, ⟨hηW, hη1⟩, rfl⟩
  have hZ : (A.boundary - B) η =
      (∫ x in {x | f x < t}, ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' := by
    change A (exteriorDerivativeTestOn U k η) - B η = _
    rw [hA, hB]
    rfl
  -- Step 2: `F = ξ(dη)` is `μ`-integrable and `F' = ξ'(η)` is `μ'`-integrable.
  have hF : Integrable
      (fun x => ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x)) μ :=
    Submission.cmcs_smp_pairing_integrable P (k + 1) U μ ξ (exteriorDerivativeTestOn U k η)
      hμ hξm hξ
  have hF' : Integrable (fun x => ξ' x ((η : DifferentialForm (Euclid P) k) x)) μ' :=
    Submission.cmcs_smp_pairing_integrable P k U μ' ξ' η hμ' hξm' hξ'
  -- Step 5: `Φ h → (∂A − B)(η)` as `h ↓ 0`, by dominated convergence for each integral.
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : ∀ ν : Measure (Euclid P), ∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) ν :=
    fun _ h h0 h1 => (hg h h0 h1).1.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun h : ℝ =>
      (∫ x, g h x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x, g h x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ')
      (𝓝[>] 0) (𝓝 ((A.boundary - B) η)) := by
    rw [hZ]
    exact (Submission.cmcs_smp_cutoff_integral_tendsto P μ _ f t 2 g hF hfm (hgm μ)
      (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
      (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2)).sub
      (Submission.cmcs_smp_cutoff_integral_tendsto P μ' _ f t 2 g hF' hfm (hgm μ')
        (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
        (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2))
  -- Steps 4 and 6: `ofReal |Φ h| ≤ ofReal (L / (h (1 − h/2))) μ(W ∩ S_h)` for `h ∈ (0, 1)`,
  -- then pass to the liminf.
  refine Submission.cmcs_smp_liminf_bound L ((A.boundary - B) η) _
    (fun h => μ (W ∩ {x | t - h < f x ∧ f x < t})) hlim fun h h0 h1 => ?_
  obtain ⟨hgs, -, hgd, hgS, -, -⟩ := hg h h0 h1
  exact (Submission.cmcs_cutoff_defect_bound P k U T μ μ' ξ ξ' (g h) η hξ hT hbT hgs).trans
    (Submission.cmcs_smp_strip_lintegral_le P k μ (g h) (η : DifferentialForm (Euclid P) k) W
      {x | t - h < f x ∧ f x < t} _ hgd hgS hηW hη1)
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **Simon Ch. 6, 4.6–4.10 (slicing by a Lipschitz function, pp. 157–158)**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')`: `A_t = T ⌞ {f < t}` and `B_t = (∂T) ⌞ {f < t}` (2.9, taken
through the given representations) are currents in `U`, and the slice `⟨T, f, t₋⟩ = ∂A_t − B_t`
(4.6) vanishes on forms supported off `{f = t}` (4.8), has
`M_W(⟨T, f, t₋⟩) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (4.9), and
`∫⁻_{(a,b)} M_W(⟨T, f, t₋⟩) dt ≤ L · μ(W ∩ {a < f < b})` (4.10).  `A_t`, `B_t` are chosen by
`cmcs_restrict_current`; 4.8 is `cmcs_slice_support` (`f` is continuous); 4.9 is
`cmcs_slice_mass_pointwise`; 4.10 is `cmcs_slice_mass_integral` applied to `t ↦ M_W(∂A_t − B_t)`
and the bound 4.9 (`f` is measurable, `W` open hence measurable). -/
theorem Submission.cmc_slice_mass_bounds : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b})) := by
  intro P k U T μ μ' ξ ξ' f L _hU hμ hμ' hξm hξm' hξ hξ' hT hbT hf
  -- `A t = T ⌞ {f < t}` and `B t = (∂T) ⌞ {f < t}` (Simon 2.9)
  choose A hA using fun t : ℝ =>
    Submission.cmcs_restrict_current P (k + 1) U μ ξ {x | f x < t} hμ hξm hξ
  choose B hB using fun t : ℝ =>
    Submission.cmcs_restrict_current P k U μ' ξ' {x | f x < t} hμ' hξm' hξ'
  -- Simon 4.9, for every `W` and `t`
  have hpt : ∀ (W : Set (Euclid P)) (t : ℝ), ((A t).boundary - B t).massOn W ≤
      (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
        μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := fun W t =>
    Submission.cmcs_slice_mass_pointwise P k U T μ μ' ξ ξ' f L t (A t) (B t) W hμ hμ' hξm hξm'
      hξ hξ' hT hbT hf (hA t) (hB t)
  refine ⟨A, B, hA, hB, fun t η hη => ?_, fun W t _ => hpt W t, fun W a b hW => ?_⟩
  · -- Simon 4.8
    exact Submission.cmcs_slice_support P k U T μ μ' ξ ξ' f t (A t) (B t) hf.continuous hT hbT
      (hA t) (hB t) η hη
  · -- Simon 4.10, from 4.9 on `(a, b)`
    exact Submission.cmcs_slice_mass_integral P μ f W L
      (fun t => ((A t).boundary - B t).massOn W) a b hf.continuous.measurable hW.measurableSet
      fun t _ => hpt W t

/-- **The dilated pair `(λ⁻ᵐ η_#μ, ξ(a + λ·))`** (Simon Ch. 6, 2.23 for the similarity
`η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`; used to rescale cycles with the integer slice
property).  `η` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`, hence a measurable
embedding with `η⁻¹(K)` compact for compact `K`, and `a + λη(x) = x`.  So `μ₂ = λ⁻ᵐ η_#μ` is
finite on compact sets, `ξ₂ = ξ(a + λ·)` is `μ₂`-a.e. strongly measurable with `|⟨α, ξ₂⟩| ≤ |α|`
`μ₂`-a.e., and `∫_S ⟨ω, ξ₂⟩ dμ₂ = λ⁻ᵐ ∫_{η⁻¹(S)} ⟨ω ∘ η, ξ⟩ dμ` for every set `S` and every form
`ω` (change of variables along the measurable embedding `η`). -/
theorem Submission.cbr_ci_dsp_pushforward_pair : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), 0 < lam → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) K < ∞) ∧ AEStronglyMeasurable (fun y => ξ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) ∧ (∀ᵐ y ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ), ∀ α : Covector (Euclid P) m, |ξ (a + lam • y) α| ≤ covectorEuclideanNorm α) ∧ ∀ (S : Set (Euclid P)) (ω : DifferentialForm (Euclid P) m), ∫ y in S, ξ (a + lam • y) (ω y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) = lam⁻¹ ^ m * ∫ x in dilation a lam ⁻¹' S, ξ x (ω (dilation a lam x)) ∂μ := by
  intro P m a lam μ ξ hlam hμ hξm hξ
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{a,λ}` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`.
  set e : Euclid P ≃ₜ Euclid P :=
    (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have he : (e : Euclid P → Euclid P) = dilation a lam := by
    funext y
    simp [e, dilation, dilationCLM]
  have hη : MeasurableEmbedding (dilation a lam) := he ▸ e.measurableEmbedding
  -- Step 2: the inverse identity `a + λη(x) = x`.
  have hinv : ∀ x, a + lam • dilation a lam x = x := fun x => by
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  refine ⟨fun K hK => ?_, ?_, ?_, fun S ω => ?_⟩
  · -- (a)
    rw [Measure.smul_apply, hη.map_apply, smul_eq_mul]
    have hKc : IsCompact (dilation a lam ⁻¹' K) := by
      rw [← he]
      exact e.isCompact_preimage.mpr hK
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμ _ hKc)
  · -- (b)
    refine AEStronglyMeasurable.smul_measure ?_ _
    rw [hη.aestronglyMeasurable_map_iff]
    have hcomp : (fun y => ξ (a + lam • y)) ∘ dilation a lam = ξ := funext fun x => by
      simp [hinv]
    rw [hcomp]
    exact hξm
  · -- (c)
    refine Measure.ae_smul_measure ?_ _
    rw [hη.ae_map_iff]
    filter_upwards [hξ] with x hx
    simpa [hinv] using hx
  · -- (d)
    rw [Measure.restrict_smul, integral_smul_measure, hη.setIntegral_map,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp only [hinv]
/-- **Composition with a dilation preserves test forms on `ℝᴾ`** (Simon Ch. 3, 1.4,
chapter-03.txt line 85; `η^#ω` in 6.2.23, chapter-06.txt lines 403–413; used for the dilations
`η_{a,λ#}` in the proof of 7.3.1, chapter-07.txt lines 329–337).  For `λ > 0` and
`η = η_{a,λ}`, `η(y) = −λ⁻¹a + λ⁻¹y`, every `φ ∈ 𝒟ᵐ(ℝᴾ)` gives `φ' = φ ∘ η ∈ 𝒟ᵐ(ℝᴾ)`:
`φ ∘ η` is `C^∞` because `η` is a constant plus the linear map `dilationCLM P λ`; it has compact
support because `η` is a homeomorphism (`y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`), so
`tsupport (φ ∘ η) = η⁻¹(tsupport φ)` is compact; and `tsupport (φ ∘ η) ⊆ ℝᴾ` is trivial. -/
theorem Submission.cbr_ci_dsp_testForm_comp_dilation : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ φ : TestFormOn (univ : Set (Euclid P)) m, ∃ φ' : TestFormOn (univ : Set (Euclid P)) m, ∀ y : Euclid P, (φ' : DifferentialForm (Euclid P) m) y = (φ : DifferentialForm (Euclid P) m) (dilation a lam y) := by
  intro P m a lam hlam φ
  -- Step 2: `η = η_{a,λ}` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`.
  let e : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have he : ⇑e = dilation a lam := by
    funext y
    simp [e, dilation, dilationCLM]
  obtain ⟨⟨hsmooth, hcompact⟩, -⟩ := φ.property
  -- Step 4: `φ' := φ ∘ η`, with `φ'(y) = φ(η(y))` by definition.
  refine ⟨⟨fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y), ?_⟩, fun y => rfl⟩
  change IsTestForm (fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y)) ∧
    tsupport (fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y)) ⊆ univ
  -- Step 1: `η = (−λ⁻¹a) + dilationCLM P λ` is `C^∞`, so `φ ∘ η` is `C^∞`; Step 3: `⊆ univ`.
  refine ⟨⟨hsmooth.comp (contDiff_const.add (dilationCLM P lam).contDiff), ?_⟩, subset_univ _⟩
  -- Step 2: `φ ∘ e` has compact support, and `e = η`.
  have h := hcompact.comp_homeomorph e
  rwa [he] at h

/-- **Integer multiplicity slice boundaries of a cycle** (the slicing step of Simon 7.2.4, via
Ch. 6, 4.6–4.10 and the integer slice property).  Let `X ∈ 𝒟_{d+1}(ℝᴾ)`, `∂X = 0`, be represented by
`(μX, ξX)` and have the integer slice property.  As `∂X = 0`, the zero measure with the zero field
represents `∂X` admissibly.  (SL) for `X`, `(μX, ξX)`, `(0, 0)` and an `L`-Lipschitz `g` gives
`A_t = X ⌞ {g < t}` and `B_t = (∂X) ⌞ {g < t}`, and `B_t = 0` since it integrates against the zero
measure.  The integer slice property with the same data makes `∂A_t − B_t = ∂A_t` integer
multiplicity for `L¹`-a.e. `t`. -/
theorem Submission.cbr_ci_dsp_cycle_slice_boundary_im : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μX : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)), X.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) (d + 1), |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ (g : Euclid P → ℝ) (L : NNReal), LipschitzWith L g → ∀ᵐ t ∂(volume : Measure ℝ), ∃ A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | g x < t}, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) ∧ IsIntegerMultiplicity A.boundary := by
  intro hSL P d X μX ξX hX hμX hξXm hξX hXrep hISP g L hg
  -- Step 1: the zero measure with the zero field represents `∂X = 0` admissibly.
  have h0K : ∀ K : Set (Euclid P), IsCompact K → (0 : Measure (Euclid P)) K < ∞ :=
    fun K _ => by simp
  have h0m : AEStronglyMeasurable (fun _ : Euclid P => (0 : MultiVector P d))
      (0 : Measure (Euclid P)) :=
    aestronglyMeasurable_zero_measure _
  have h0b : ∀ᵐ x ∂(0 : Measure (Euclid P)), ∀ α : Covector (Euclid P) d,
      |(fun _ : Euclid P => (0 : MultiVector P d)) x α| ≤ covectorEuclideanNorm α := by
    simp
  have h0rep : ∀ η : TestFormOn (univ : Set (Euclid P)) d, X.boundary η =
      ∫ x, (fun _ : Euclid P => (0 : MultiVector P d)) x ((η : DifferentialForm (Euclid P) d) x)
        ∂(0 : Measure (Euclid P)) := by
    intro η
    rw [hX]
    simp
  -- Step 2: (SL) gives `A t = X ⌞ {g < t}` and `B t = (∂X) ⌞ {g < t}` through `(0, 0)`.
  obtain ⟨A, B, hA, hB, -⟩ := hSL P d univ X μX 0 ξX (fun _ => 0) g L isOpen_univ
    (fun K hK _ => hμX K hK) (fun K hK _ => h0K K hK) hξXm h0m hξX h0b hXrep h0rep hg
  -- Step 4: the integer slice property of `X` with the same data, for a.e. `t`.
  filter_upwards [hISP μX 0 ξX (fun _ => 0) hμX h0K hξXm h0m hξX h0b hXrep h0rep g L hg]
    with t ht
  refine ⟨A t, hA t, ?_⟩
  -- Steps 3 and 6: `B t = 0`, so `∂A t − B t = ∂A t`.
  have hsub : (A t).boundary - B t = (A t).boundary := by
    ext η
    change (A t).boundary η - B t η = (A t).boundary η
    rw [hB t η]
    simp
  -- Step 5: `∂A t − B t` is integer multiplicity.
  have h := ht (A t) (B t) (hA t) (hB t)
  rwa [hsub] at h

/-- Dilation invariance of the integer slice property (ISP), step 2 of the proof that a cycle with
the ISP is integer multiplicity.  Let `η = dilation a lam` and let `X'` be the dilation of the cycle
`X` with admissible representation `(μ_X, ξ_X)`.  Then `∂X' = 0` and `(λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))`
is an admissible representation of `X'`.  Fix admissible representations `(μ, ξ)` of `X'`,
`(μ', ξ')` of `∂X'` and an `L`-Lipschitz `f`.  By (SL) and the ISP of `X`, the slice `A_X(t)` of `X`
by `{f ∘ η < t}` has integer multiplicity boundary for a.e. `t`.  For such `t`, (RU) and the change
of variables `η` show that every slice `A` of `X'` by `{f < t}` is the dilation of `A_X(t)`, and
(RU) with `∂X' = 0` shows that the boundary slice `B` vanishes.  Hence `∂A − B = ∂A` is the dilation
of `∂A_X(t)`, which is integer multiplicity. -/
theorem Submission.cbr_ci_dilation_slice_property : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (P d : ℕ) (a : Euclid P) (lam : ℝ) (X X' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μX : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)), 0 < lam → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y = (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (d + 1) * X ω') → X.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) (d + 1), |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X' ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X').boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) := by
  have hpush := Submission.cbr_ci_dsp_pushforward_pair
  have hcomp := Submission.cbr_ci_dsp_testForm_comp_dilation
  have hcyc := Submission.cbr_ci_dsp_cycle_slice_boundary_im
  have hdc := Submission.cbr_ci_dilation_calculus
  intro SL RU P d a lam X X' μX ξX hlam hdil hXbd hμXK hξXm hξXb hXrep hISP
    μ μ' ξ ξ' hμK hμ'K hξm hξ'm hξb hξ'b hrep hbrep f L hf
  -- Step 1: `(λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))` is an admissible representation of `X'`
  obtain ⟨hμ₂K, hξ₂m, hξ₂b, hchg⟩ := hpush P (d + 1) a lam μX ξX hlam hμXK hξXm hξXb
  obtain ⟨-, hbd, him, -, -, -⟩ := hdc P d a lam hlam
  obtain ⟨-, -, -, hrepd, -, -⟩ := hdc P (d + 1) a lam hlam
  -- Step 2: `∂X' = 0`, testing `∂X` against `φ ∘ η`
  have hX'bd : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, X'.boundary φ = 0 := by
    intro φ
    obtain ⟨φ', hφ'⟩ := hcomp P d a lam hlam φ
    rw [hbd X X' hdil φ φ' hφ', hXbd, GeometricCurrentOn.zero_apply, mul_zero]
  -- Step 3: the slices `A_X(t)` of `X` by `{f ∘ η < t}` have integer multiplicity boundary
  -- for a.e. `t`
  have hηL : LipschitzWith ‖lam⁻¹‖₊ (dilation a lam) := by
    refine LipschitzWith.of_dist_le_mul fun x y => le_of_eq ?_
    simp [dilation, dilationCLM, dist_smul₀]
  filter_upwards [hcyc SL P d X μX ξX hXbd hμXK hξXm hξXb hXrep hISP (f ∘ dilation a lam)
    (L * ‖lam⁻¹‖₊) (hf.comp hηL)] with t ht
  obtain ⟨AX, hAX, hAXim⟩ := ht
  intro A B hA hB
  have hft : MeasurableSet {x | f x < t} :=
    measurableSet_lt hf.continuous.measurable measurable_const
  -- Step 4: by (RU), `A` is also the slice of the representation of Step 1
  have hRU1 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ =
        ∫ y in {x | f x < t}, ξX (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y)
          ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) := by
    intro ω
    have h := RU P (d + 1) univ μ
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) 0 ξ
      (fun y => ξX (a + lam • y)) (fun _ => 0) isOpen_univ (fun K hK _ => hμK K hK)
      (fun K hK _ => hμ₂K K hK) (fun K _ _ => by simp) hξm hξ₂m aestronglyMeasurable_const
      hξb hξ₂b (by simp)
      (fun ω => by rw [← hrep ω, hrepd X X' μX ξX hdil hXrep ω, integral_zero_measure, add_zero])
      {x | f x < t} ω hft
    simpa only [Measure.restrict_zero, integral_zero_measure, add_zero] using h
  -- Step 5: change of variables by `η`: `A` is the dilation of `A_X(t)`
  have hAdil : ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1),
      (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y =
        (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) →
      A ω = lam⁻¹ ^ (d + 1) * AX ω' := by
    intro ω ω' hω'
    rw [hA ω, hRU1 ω, hchg {x | f x < t} (ω : DifferentialForm (Euclid P) (d + 1)), hAX ω']
    simp only [hω']
    rfl
  -- Step 6: by (RU) and `∂X' = 0`, the boundary slice `B` vanishes
  have hB0 : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, B φ = 0 := by
    intro φ
    have h := RU P d univ μ' 0 0 ξ' (fun _ => 0) (fun _ => 0) isOpen_univ
      (fun K hK _ => hμ'K K hK) (fun K _ _ => by simp) (fun K _ _ => by simp) hξ'm
      aestronglyMeasurable_const aestronglyMeasurable_const hξ'b (by simp) (by simp)
      (fun φ => by rw [← hbrep φ, hX'bd φ, integral_zero_measure, add_zero])
      {x | f x < t} φ hft
    rw [hB φ, h, Measure.restrict_zero, integral_zero_measure, add_zero]
  -- Step 7: `∂A − B = ∂A` is the dilation of the integer multiplicity `∂A_X(t)`
  have hsub : A.boundary - B = A.boundary := by
    refine GeometricCurrentOn.ext fun φ => ?_
    show A.boundary φ - B φ = A.boundary φ
    rw [hB0 φ, sub_zero]
  rw [hsub]
  exact him AX.boundary A.boundary (hbd AX A hAdil) hAXim
/-- **Dilation invariance of the integer slice property** (step 2 of the proof that a cycle with
the integer slice property is integer multiplicity, for the closure theorem Simon Ch. 6, 8.2,
whose proof slices the blow-ups `η_{x,λⱼ#}T` (8.2 (7), (8)); slices as in Ch. 6, 4.6–4.10;
dilations `η_{a,λ#}` as in Ch. 6, 2.23).  Let `η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`,
`n = d + 1`, and let `X'` be the dilation of the cycle `X ∈ 𝒟ₙ(ℝᴾ)` with admissible
representation `(μ_X, ξ_X)`.  By the dilation calculus
(`Submission.dmcbr_ci_dilation_calculus`), `∂X' = 0` and `(λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))` is an
admissible representation of `X'` (`Submission.cbr_ci_dsp_pushforward_pair`).  Fix admissible
representations `(μ, ξ)` of `X'`, `(μ', ξ')` of `∂X'` and an `L`-Lipschitz `f`.  By (SL) and the
integer slice property of `X` (`Submission.cbr_ci_dsp_cycle_slice_boundary_im`), the slice `A_X(t)`
of `X` by `{f ∘ η < t}` has integer multiplicity boundary for a.e. `t`.  For such `t`, (RU) and the
change of variables along `η` make every slice `A` of `X'` by `{f < t}` the dilation of `A_X(t)`,
and (RU) with `∂X' = 0` makes the boundary slice `B` vanish.  Hence `∂A − B = ∂A` is the dilation
of `∂A_X(t)`, which is integer multiplicity. -/
theorem Submission.dmcbr_ci_dilation_slice_property : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (P d : ℕ) (a : Euclid P) (lam : ℝ) (X X' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μX : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)), 0 < lam → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y = (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (d + 1) * X ω') → X.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) (d + 1), |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X' ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X').boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) := by
  have hdc := Submission.dmcbr_ci_dilation_calculus
  have hpush := Submission.cbr_ci_dsp_pushforward_pair
  have hcomp := Submission.cbr_ci_dsp_testForm_comp_dilation
  have hcyc := Submission.cbr_ci_dsp_cycle_slice_boundary_im
  intro SL RU P d a lam X X' μX ξX hlam hdil hXbd hμXK hξXm hξXb hXrep hISP
    μ μ' ξ ξ' hμK hμ'K hξm hξ'm hξb hξ'b hrep hbrep f L hf
  -- Steps 1 and 3: `(μ₂, ξ₂) = (λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))` is an admissible representation of
  -- `X'` (the push-forward pair and the dilation calculus (4))
  obtain ⟨hμ₂K, hξ₂m, hξ₂b, hchg⟩ := hpush P (d + 1) a lam μX ξX hlam hμXK hξXm hξXb
  obtain ⟨-, hbd, him, -, -, -⟩ := hdc P d a lam hlam
  obtain ⟨-, -, -, hrepd, -, -⟩ := hdc P (d + 1) a lam hlam
  -- Step 2: `∂X' = 0`, by the dilation calculus (2) applied to `(φ, φ ∘ η)`
  have hX'bd : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, X'.boundary φ = 0 := by
    intro φ
    obtain ⟨φ', hφ'⟩ := hcomp P d a lam hlam φ
    rw [hbd X X' hdil φ φ' hφ', hXbd, GeometricCurrentOn.zero_apply, mul_zero]
  -- Steps 5 and 6: `g = f ∘ η` is `Lλ⁻¹`-Lipschitz, and by (SL) and the ISP of `X` (with the
  -- representations `(μ_X, ξ_X)` and `(0, 0)` of `X` and `∂X = 0`) the slices `A_X(t)` of `X` by
  -- `{g < t}` have integer multiplicity boundary for `t` outside an `L¹`-null set
  have hηL : LipschitzWith ‖lam⁻¹‖₊ (dilation a lam) := by
    refine LipschitzWith.of_dist_le_mul fun x y => le_of_eq ?_
    simp [dilation, dilationCLM, dist_smul₀]
  filter_upwards [hcyc SL P d X μX ξX hXbd hμXK hξXm hξXb hXrep hISP (f ∘ dilation a lam)
    (L * ‖lam⁻¹‖₊) (hf.comp hηL)] with t ht
  obtain ⟨AX, hAX, hAXim⟩ := ht
  -- Step 4: slices `A` of `X'` and `B` of `∂X'` by `{f < t}`
  intro A B hA hB
  have hft : MeasurableSet {x | f x < t} :=
    measurableSet_lt hf.continuous.measurable measurable_const
  -- Step 7: (RU) with `(μ, ξ)`, `(μ₂, ξ₂)`, `(0, 0)` and the Borel set `{f < t}`: `A` is also
  -- the slice of `(μ₂, ξ₂)`
  have hRU1 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ =
        ∫ y in {x | f x < t}, ξX (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y)
          ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) := by
    intro ω
    have h := RU P (d + 1) univ μ
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) 0 ξ
      (fun y => ξX (a + lam • y)) (fun _ => 0) isOpen_univ (fun K hK _ => hμK K hK)
      (fun K hK _ => hμ₂K K hK) (fun K _ _ => by simp) hξm hξ₂m aestronglyMeasurable_const
      hξb hξ₂b (by simp)
      (fun ω => by rw [← hrep ω, hrepd X X' μX ξX hdil hXrep ω, integral_zero_measure, add_zero])
      {x | f x < t} ω hft
    simpa only [Measure.restrict_zero, integral_zero_measure, add_zero] using h
  -- Step 7, change of variables along `η`: `A` is the dilation of `A_X(t)`
  have hAdil : ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1),
      (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y =
        (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) →
      A ω = lam⁻¹ ^ (d + 1) * AX ω' := by
    intro ω ω' hω'
    rw [hA ω, hRU1 ω, hchg {x | f x < t} (ω : DifferentialForm (Euclid P) (d + 1)), hAX ω']
    simp only [hω']
    rfl
  -- Step 8: (RU) with `(μ', ξ')`, `(0, 0)`, `(0, 0)`, `∂X' = 0` and `{f < t}`: `B = 0`
  have hB0 : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, B φ = 0 := by
    intro φ
    have h := RU P d univ μ' 0 0 ξ' (fun _ => 0) (fun _ => 0) isOpen_univ
      (fun K hK _ => hμ'K K hK) (fun K _ _ => by simp) (fun K _ _ => by simp) hξ'm
      aestronglyMeasurable_const aestronglyMeasurable_const hξ'b (by simp) (by simp)
      (fun φ => by rw [← hbrep φ, hX'bd φ, integral_zero_measure, add_zero])
      {x | f x < t} φ hft
    rw [hB φ, h, Measure.restrict_zero, integral_zero_measure, add_zero]
  -- Step 9: `∂A − B = ∂A` is the dilation of the integer multiplicity current `∂A_X(t)`
  -- (the dilation calculus (2) and (3))
  have hsub : A.boundary - B = A.boundary := by
    refine GeometricCurrentOn.ext fun φ => ?_
    show A.boundary φ - B φ = A.boundary φ
    rw [hB0 φ, sub_zero]
  rw [hsub]
  exact him AX.boundary A.boundary (hbd AX A hAdil) hAXim
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

/-- **`Hⁿ` and the measure `θ Hⁿ⌞M` under the blow-up map `η = η_{a,λ}`, `λ > 0`** (step 2 of the
blow-up argument in the integer-multiplicity criterion for cycles; `η_{x,λ}(y) = λ⁻¹(y − x)` and
the change of variables for `η_{x,λ#}` as in the proof of Simon Ch. 6, 8.1, chapter-06.txt
lines 2230–2238).  `η = blowUpMap a λ` is the contract's `dilation a λ`, `D(y) = −λ⁻¹a + λ⁻¹y`,
an affine homeomorphism with inverse `x ↦ a + λx`; so (i) `η(M) = D(M)` is Borel.
`Hⁿ(D(s)) = λ⁻ⁿ Hⁿ(s)` for every `s`, as `D(s)` is the translate by `−λ⁻¹a` of `λ⁻¹s`.  For Borel
`B` this gives (ii): `Hⁿ(B ∩ D(M)) = Hⁿ(D(D⁻¹B ∩ M)) = λ⁻ⁿ Hⁿ(D⁻¹B ∩ M)`.  (iii) follows from
(ii): pull `λ⁻ⁿ` out of `withDensity` and transport the density along `D`, as
`θ(a + λD(x)) = θ(x)`. -/
theorem Submission.cbr_ci_bl_blowUp_restrict_scaling : ∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (a : Euclid P) (lam : ℝ), MeasurableSet M → Measurable θ → 0 < lam → MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) ∧ μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) = ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) ∧ ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) ((μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x))) = (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)).withDensity (fun y => ENNReal.ofReal (θ (a + lam • y))) := by
  intro P n M θ a lam hM _ hlam
  -- Step 1: `η = blowUpMap a λ` is `D = dilation a λ`, `y ↦ −λ⁻¹a + λ⁻¹y`, an affine
  -- homeomorphism with inverse `x ↦ a + λx`
  have hηD : Poincare.SimonGMT.Chapter03.blowUpMap a lam = dilation a lam := by
    funext y
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      _root_.smul_apply, ContinuousLinearMap.id_apply, smul_sub]
    abel
  have hDc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • a)))) : Euclid P → Euclid P) = dilation a lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation a lam) := by
    rw [← hDc]
    exact Homeomorph.measurableEmbedding _
  have hιD : ∀ x, a + lam • dilation a lam x = x := fun x => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  -- Step 2: `Hⁿ(D(s)) = λ⁻ⁿ Hⁿ(s)`: `D(s)` is the translate by `−λ⁻¹a` of `λ⁻¹s`
  have himage : ∀ s : Set (Euclid P),
      μHE[n] (dilation a lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro s
    have hs : dilation a lam '' s =
        (fun z => -(lam⁻¹ • a) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • a))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  -- Step 3, (ii): on Borel `B`, `Hⁿ(B ∩ D(M)) = Hⁿ(D(D⁻¹B ∩ M)) = λ⁻ⁿ Hⁿ(D⁻¹B ∩ M)`
  have hrestrict : μHE[n].restrict (dilation a lam '' M) =
      ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.smul_apply, hme.map_apply,
      Measure.restrict_apply (hme.measurable hB), smul_eq_mul, ← himage,
      Set.image_preimage_inter]
  rw [hηD]
  refine ⟨hme.measurableSet_image.mpr hM, hrestrict, ?_⟩
  -- Step 4, (iii): pull out the scalar and transport the density along `D`, using
  -- `θ(a + λD(x)) = θ(x)`
  rw [hrestrict, withDensity_smul_measure]
  congr 1
  ext B hB
  rw [hme.map_apply, withDensity_apply _ (hme.measurable hB), withDensity_apply _ hB,
    hme.restrict_map, hme.lintegral_map]
  simp only [hιD]
/-- **Normalised mass and deviation identities for one blow-up of `Hⁿ⌞M`** (steps 2–4 of the
blow-up argument in White's proof that cycles with the integer slice property are integer
multiplicity, at a single scale `λ > 0`).  Let `ν = Hⁿ⌞η(M)`, `η = blowUpMap a λ`,
`D = dilation a λ`, `c = λ⁻ⁿ`, `V(r) = ωₙ rⁿ`, and assume `ν = c D_#(Hⁿ⌞M)`.  `D(y) = λ⁻¹(y − a)`
is an affine homeomorphism (so a measurable embedding) with `a + λD(x) = x`, and
`D⁻¹(B̄_R(0)) = B̄_{λR}(a)`, `D⁻¹(B_R(0)) = B_{λR}(a)`.  Hence `ν(S) = c Hⁿ(M ∩ D⁻¹S)` for Borel `S`
and `∫⁻_{B̄_R(0)} g dν = c ∫⁻_{M ∩ B̄_{λR}(a)} g ∘ D dHⁿ`, while `c = V(R)/V(λR)` for `R > 0` as
`0 < ωₙ < ∞`. -/
theorem Submission.dmcbr_ci_bl_scale_identities : ∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n) (a : Euclid P) (lam : ℝ), 0 < lam → μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) = ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) → (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) univ = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] M ∧ ∀ R : ℝ, 0 < R → (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) (closedBall 0 R) = unitBallVolume n * ENNReal.ofReal (R ^ n) * (μHE[n] (M ∩ closedBall a (lam * R)) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) ∧ (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) (ball 0 R) = unitBallVolume n * ENNReal.ofReal (R ^ n) * (μHE[n] (M ∩ ball a (lam * R)) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) ∧ ∫⁻ y in closedBall (0 : Euclid P) R, ‖θ (a + lam • y) • ζ (a + lam • y) - θ a • ζ a‖ₑ ∂(μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) = unitBallVolume n * ENNReal.ofReal (R ^ n) * ((∫⁻ x in M ∩ closedBall a (lam * R), ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) := by
  intro P n M θ ζ a lam hlam hH
  -- Step 1: `D = dilation a λ`, `y ↦ −λ⁻¹a + λ⁻¹y = λ⁻¹(y − a)`, is an affine homeomorphism,
  -- hence a measurable embedding, and `a + λD(x) = x`
  have hDc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • a)))) : Euclid P → Euclid P) = dilation a lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation a lam) := by
    rw [← hDc]
    exact Homeomorph.measurableEmbedding _
  have hιD : ∀ x, a + lam • dilation a lam x = x := fun x => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  -- Step 2: `‖D(y)‖ = λ⁻¹ dist(y, a)`, so `D⁻¹(B̄_R(0)) = B̄_{λR}(a)` and
  -- `D⁻¹(B_R(0)) = B_{λR}(a)`
  have hnorm : ∀ y, ‖dilation a lam y‖ = lam⁻¹ * dist y a := fun y => by
    have hDy : dilation a lam y = lam⁻¹ • (y - a) := by
      simp only [dilation, dilationCLM, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_sub]
      abel
    rw [hDy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le), dist_eq_norm]
  have hpre_cb : ∀ R : ℝ, dilation a lam ⁻¹' closedBall 0 R = closedBall a (lam * R) :=
    fun R => by
      ext y
      simp only [Set.mem_preimage, mem_closedBall, dist_zero_right, hnorm, inv_mul_le_iff₀ hlam]
  have hpre_b : ∀ R : ℝ, dilation a lam ⁻¹' ball 0 R = ball a (lam * R) := fun R => by
    ext y
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, hnorm, inv_mul_lt_iff₀ hlam]
  -- Step 3: `ν(S) = c Hⁿ(M ∩ D⁻¹S)` for Borel `S`
  have hmass : ∀ S : Set (Euclid P), MeasurableSet S →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) S =
        ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] (M ∩ dilation a lam ⁻¹' S) := by
    intro S hS
    rw [hH, Measure.smul_apply, hme.map_apply, Measure.restrict_apply (hme.measurable hS),
      smul_eq_mul, Set.inter_comm]
  -- Step 4: `c = V(R)/V(λR)` for `R > 0` (`0 < ωₙ < ∞`), so `c X = V(R) (X / V(λR))`
  have hkey : ∀ R : ℝ, 0 < R → ∀ X : ℝ≥0∞, ENNReal.ofReal (lam⁻¹ ^ n) * X =
      unitBallVolume n * ENNReal.ofReal (R ^ n) *
        (X / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) := by
    intro R hR X
    have hA : ENNReal.ofReal (R ^ n) =
        ENNReal.ofReal (lam⁻¹ ^ n) * ENNReal.ofReal ((lam * R) ^ n) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hlam.le) n), ← mul_pow, ← mul_assoc,
        inv_mul_cancel₀ hlam.ne', one_mul]
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    have hV0 : unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos (mul_pos hlam hR) n)).ne'
    have hVtop : unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    rw [hA, mul_left_comm (unitBallVolume n), mul_assoc, ENNReal.mul_div_cancel hV0 hVtop]
  refine ⟨?_, fun R hR => ⟨?_, ?_, ?_⟩⟩
  -- (i): `S = ℝᴾ`
  · rw [hmass univ MeasurableSet.univ, Set.preimage_univ, Set.inter_univ]
  -- (ii), (iii): `S = B̄_R(0)`, `S = B_R(0)`
  · rw [hmass _ measurableSet_closedBall, hpre_cb, hkey R hR]
  · rw [hmass _ measurableSet_ball, hpre_b, hkey R hR]
  -- (iv): `∫⁻_{B̄_R(0)} g dν = c ∫⁻_{M ∩ B̄_{λR}(a)} g ∘ D dHⁿ`, and
  -- `g(D(x)) = ‖θ(x)ζ(x) − θ(a)ζ(a)‖ₑ`
  · rw [hH, Measure.restrict_smul, lintegral_smul_measure, hme.restrict_map, hme.lintegral_map,
      Measure.restrict_restrict (hme.measurable measurableSet_closedBall), hpre_cb,
      Set.inter_comm, smul_eq_mul, ← hkey R hR]
    simp only [hιD]

/-- **One blow-up scale of a cycle `Γ = μ ∧ ζ` with `μ = θ Hⁿ⌞M`** (step 2 of the blow-up argument
in the integer-multiplicity criterion for cycles: the blow-ups `η_{a,λ#}Γ` and the change of
variables `y = a + λz`, as in the proof of Simon Ch. 6, 8.1, chapter-06.txt lines 2230–2245).
Let `D = η_{a,λ}` (`dilation a λ`, which equals `blowUpMap a λ`), `c = λ^{-n}` and
`μ' = c D_#μ`, and let `Γ'` satisfy the dilation identities (h2), (h4), (h5) for `∂`, the
representation and `M_W`.  `D` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`, with `a + λD(x) = x`,
and `Submission.cbr_ci_bl_blowUp_restrict_scaling` gives that `η(M)` is Borel and
`μ' = θ(a + λ·) Hⁿ⌞η(M)`.  Then `Γ(ω) = ∫ ⟨ω, ζ⟩ dμ`, as `θ > 0` on `M`;
`∂Γ'(ω) = λ^{-d} ∂Γ(ω ∘ D) = 0`; `μ'(K) ≤ c μ(ℝᴾ) < ∞`;
`M_W(Γ') = c M_{D⁻¹W}(Γ) = c μ(D⁻¹W) = μ'(W)` for open `W`;
`Γ'(ω) = ∫ ⟨ω(y), ζ(a + λy)⟩ dμ'(y)` by (h4); `μ'(η(M)ᶜ) = c μ(Mᶜ) = 0`; and rewriting through
the density of `μ'` gives `Γ'(ω) = ∫_{η(M)} θ(a + λy) ⟨ω(y), ζ(a + λy)⟩ dHⁿ(y)`. -/
theorem Submission.dmcbr_ci_bl_blowup_scale : ∀ (P d : ℕ) (Γ Γ' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P (d + 1)) (a : Euclid P) (lam : ℝ), 0 < lam → Γ.boundary = 0 → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[(d + 1)].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μHE[(d + 1)]) → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) d, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) d) y = (ω : DifferentialForm (Euclid P) d) (dilation a lam y)) → Γ'.boundary ω = lam⁻¹ ^ d * Γ.boundary ω') → ((∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) → (∀ W : Set (Euclid P), Γ'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ (d + 1)) * Γ.massOn W) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ Γ'.boundary = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → Γ'.massOn W = (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) W) ∧ AEStronglyMeasurable (fun y => ζ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) ∧ (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)ᶜ = 0 ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, (θ (a + lam • y) • ζ (a + lam • y)) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M))) := by
  intro P d Γ Γ' μ M θ ζ a lam hlam hΓb hμfin hmass hM hθ hζ hμ hθpos hΓrep h2 h4 h5
  -- Step 1: `D = dilation a λ` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`; it equals
  -- `η = blowUpMap a λ`, is smooth, and `a + λη(x) = x`
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation a lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • a))), by funext y; simp [dilation, dilationCLM]⟩
  have hDme : MeasurableEmbedding (dilation a lam) := by
    rw [← he]
    exact e.measurableEmbedding
  have hDcont : Continuous (dilation a lam) := by
    rw [← he]
    exact e.continuous
  have hDsurj : Surjective (dilation a lam) := by
    rw [← he]
    exact e.surjective
  have hDinj : Injective (dilation a lam) := by
    rw [← he]
    exact e.injective
  have hDsmooth : ∀ k : WithTop ℕ∞, ContDiff ℝ k (dilation a lam) := fun _ =>
    contDiff_const.add (dilationCLM P lam).contDiff
  have hDη : dilation a lam = Poincare.SimonGMT.Chapter03.blowUpMap a lam := by
    funext y
    simp only [dilation, dilationCLM, Poincare.SimonGMT.Chapter03.blowUpMap, _root_.smul_apply,
      ContinuousLinearMap.id_apply, smul_sub, neg_add_eq_sub]
  have hηinv : ∀ x, a + lam • Poincare.SimonGMT.Chapter03.blowUpMap a lam x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hlam.ne', add_sub_cancel]
  -- `η(M)` is Borel and `μ' = c D_#μ = (Hⁿ⌞η(M)) ⌞ θ(a + λ·)` (sibling `blowup_measure`)
  obtain ⟨hηM, -, hμ'⟩ :=
    Submission.cbr_ci_bl_blowUp_restrict_scaling P (d + 1) M θ a lam hM hθ hlam
  rw [← hμ] at hμ'
  have hμ'apply : ∀ s : Set (Euclid P),
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) s =
        ENNReal.ofReal (lam⁻¹ ^ (d + 1)) * μ (dilation a lam ⁻¹' s) := fun s => by
    rw [Measure.smul_apply, hDme.map_apply, smul_eq_mul]
  -- Step 2 (P0): `Γ(ω) = ∫ ζ(ω) dμ`, since `(ofReal θ).toReal = θ` on `M`
  have hP0 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ := by
    intro ω
    rw [hΓrep ω, hμ, integral_withDensity_eq_integral_toReal_smul hθ.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun hM fun x hx => ?_
    simp only [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
  -- Step 3 (P7): `∂Γ'(ω) = λ^{-d} ∂Γ(ω ∘ D) = 0`, `ω ∘ D` being a test form
  have hP7 : Γ'.boundary = 0 := by
    refine GeometricCurrentOn.ext fun ω => ?_
    have hcpt : HasCompactSupport ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) := by
      rw [← he]
      exact ω.property.1.2.comp_homeomorph e
    have hmem : (ω : DifferentialForm (Euclid P) d) ∘ dilation a lam ∈
        testFormOnSubmodule (univ : Set (Euclid P)) d := by
      show IsTestForm ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) ∧
        tsupport ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) ⊆ univ
      exact ⟨⟨ω.property.1.1.comp (hDsmooth _), hcpt⟩, subset_univ _⟩
    rw [h2 ω ⟨_, hmem⟩ fun _ => rfl, hΓb]
    simp only [GeometricCurrentOn.zero_apply, mul_zero]
  -- Step 4 (P1): `μ'(K) = c μ(D⁻¹K) ≤ c μ(ℝᴾ) < ∞`
  have hP1 : ∀ K : Set (Euclid P), IsCompact K →
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) K < ∞ := fun K _ => by
    rw [hμ'apply]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono (subset_univ _)).trans_lt hμfin)
  -- Step 5 (P2): `M_W(Γ') = M_{D(D⁻¹W)}(Γ') = c M_{D⁻¹W}(Γ) = c μ(D⁻¹W) = μ'(W)`
  have hP2 : ∀ W : Set (Euclid P), IsOpen W →
      Γ'.massOn W = (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) W := by
    intro W hW
    rw [hμ'apply, ← hmass _ (hW.preimage hDcont), ← h5, image_preimage_eq W hDsurj]
  -- Step 6 (P3): `y ↦ a + λy` is measurable, so `y ↦ ζ(a + λy)` is strongly measurable
  have hAmeas : Measurable fun y : Euclid P => a + lam • y :=
    (continuous_const.add (continuous_const_smul lam)).measurable
  -- Step 7 (P5): `(h4)` applied to (P0)
  have hP5 := h4 hP0
  -- Step 8 (P6): `μ'(η(M)ᶜ) = c μ((D⁻¹(D(M)))ᶜ) = c μ(Mᶜ) = 0`
  have hμMc : μ Mᶜ = 0 := by
    rw [hμ]
    exact withDensity_absolutelyContinuous _ _
      (by rw [Measure.restrict_apply' hM, compl_inter_self, measure_empty])
  have hP6 : (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)
      (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)ᶜ = 0 := by
    rw [hμ'apply, preimage_compl, ← hDη, hDinj.preimage_image, hμMc, mul_zero]
  -- Step 9 (P8): rewrite (P5) through `μ' = (Hⁿ⌞η(M)) ⌞ θ(a + λ·)`; for `y = η(x)`, `x ∈ M`,
  -- `a + λy = x` and `(ofReal θ(x)).toReal = θ(x)`
  have hθA : Measurable fun y : Euclid P => ENNReal.ofReal (θ (a + lam • y)) :=
    (hθ.comp hAmeas).ennreal_ofReal
  have hP8 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω =
      ∫ y, (θ (a + lam • y) • ζ (a + lam • y)) ((ω : DifferentialForm (Euclid P) (d + 1)) y)
        ∂(μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) := by
    intro ω
    rw [hP5 ω, hμ', integral_withDensity_eq_integral_toReal_smul hθA
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun hηM fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [hηinv x, ENNReal.toReal_ofReal (hθpos x hx).le, _root_.smul_apply]
  exact ⟨hP0, hP7, hP1, hP2, (hζ.comp_measurable hAmeas).aestronglyMeasurable, hP5, hP6, hP8⟩

/-- **Two-sided density bounds at a good point of `μ = θ Hⁿ⌞M`** (step 1 of the blow-up argument
in the integer multiplicity criterion for cycles; Simon 6.2.8, 7.3.1; `|·|_E` is
`covectorEuclideanNorm`).  Put `θ₀ = θ(a) > 0`, `τ = θζ`, `τ₀ = τ(a)`, `V(r) = ωₙ rⁿ` and
`o(r) = ∫_{M ∩ B̄_r(a)} ‖τ − τ₀‖ dHⁿ`.  (F2) For `x ∈ M` choose `β` with `|β|_E ≤ 1` and
`⟨β, ζ(x)⟩ = 1`, and put `δ = τ(x) − τ₀`.  Then `⟨β, δ⟩ = θ(x) − θ₀ ⟨β, ζ(a)⟩ ≥ θ(x) − θ₀` and
`⟨β, δ⟩ ≤ ‖δ‖ ‖β‖ ≤ Pⁿ ‖δ‖`, as `‖β‖ ≤ Pⁿ |β|_E` (`Submission.dmcbr_ci_bl_covector_opNorm_le`);
so `θ(x) ≤ θ₀ + Pⁿ ‖τ(x) − τ₀‖`.  Integrating (F2) over `M ∩ B_r(a) ⊆ M ∩ B̄_r(a)` gives
`μ(B_r(a)) ≤ θ₀ Hⁿ(M ∩ B_r(a)) + Pⁿ o(r)`.  For small `r`, the lower density bound gives
`μ(B_r(a)) ≥ (η₁/2) V(r)`, `o(r)/V(r) → 0` gives `Pⁿ o(r) ≤ (η₁/4) V(r)` and the upper density
bound gives `Hⁿ(M ∩ B̄_r(a)) ≤ 2 V(r)`.  Cancelling the finite `(η₁/4) V(r)` and dividing by
`θ₀` yields `Hⁿ(M ∩ B_r(a)) ≥ (η₁/(4θ₀)) V(r)`. -/
theorem Submission.dmcbr_ci_bl_density_bounds : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n) (a : Euclid P) (η₁ : ℝ), MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) → a ∈ M → 0 < η₁ → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => μ (ball a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) → limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ENNReal.ofReal (η₁ / (4 * θ a)) * (unitBallVolume n * ENNReal.ofReal (r ^ n)) ≤ μHE[n] (M ∩ ball a r) ∧ μHE[n] (M ∩ closedBall a r) ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n)) := by
  intro P n μ M θ ζ a η₁ hM _ _ hμ hθ hζ hβ ha hη₁ hL hU hD
  have hθa : 0 < θ a := hθ a ha
  have hPn : (0 : ℝ) ≤ (P : ℝ) ^ n := by positivity
  -- `K = ofReal(Pⁿ)` is finite
  have hK : ENNReal.ofReal ((P : ℝ) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Step 1: `V(r) = ωₙ rⁿ` is nonzero for `r > 0` and always finite
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hV0 : ∀ r : ℝ, 0 < r → unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 := fun r hr =>
    mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne'
  have hVt : ∀ r : ℝ, unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ ∞ := fun r =>
    ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top
  -- Step 2 (F2): `θ(x) ≤ θ(a) + Pⁿ ‖θ(x)ζ(x) − θ(a)ζ(a)‖` on `M`, read in `[0, ∞]`
  have hF2 : ∀ x ∈ M, ENNReal.ofReal (θ x) ≤
      ENNReal.ofReal (θ a) + ENNReal.ofReal ((P : ℝ) ^ n) * ‖θ x • ζ x - θ a • ζ a‖ₑ := by
    intro x hx
    obtain ⟨β, hβ1, hζβ⟩ := hβ x hx
    set δ : MultiVector P n := θ x • ζ x - θ a • ζ a with hδ
    -- (a) `⟨β, δ⟩ = θ(x) − θ(a) ⟨β, ζ(a)⟩`
    have hδβ : δ β = θ x - θ a * ζ a β := by
      rw [hδ, _root_.sub_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
        hζβ, mul_one]
    -- (b) `θ(a) ⟨β, ζ(a)⟩ ≤ θ(a)`, as `⟨β, ζ(a)⟩ ≤ |β|_E ≤ 1`
    have hζaβ : θ a * ζ a β ≤ θ a :=
      mul_le_of_le_one_right hθa.le ((le_abs_self _).trans ((hζ a β).trans hβ1))
    -- (c) `‖β‖ ≤ Pⁿ |β|_E ≤ Pⁿ`
    have hβP : ‖β‖ ≤ (P : ℝ) ^ n :=
      (Submission.dmcbr_ci_bl_covector_opNorm_le P n β).trans (mul_le_of_le_one_right hPn hβ1)
    -- (d) `⟨β, δ⟩ ≤ ‖δ‖ ‖β‖ ≤ Pⁿ ‖δ‖`
    have hδle : δ β ≤ (P : ℝ) ^ n * ‖δ‖ :=
      calc δ β ≤ ‖δ β‖ := Real.le_norm_self _
        _ ≤ ‖δ‖ * ‖β‖ := δ.le_opNorm β
        _ ≤ ‖δ‖ * (P : ℝ) ^ n := mul_le_mul_of_nonneg_left hβP (norm_nonneg δ)
        _ = (P : ℝ) ^ n * ‖δ‖ := mul_comm _ _
    -- (e) `θ(x) ≤ θ(a) + Pⁿ ‖δ‖`; (f) pass to `[0, ∞]`
    have hθx : θ x ≤ θ a + (P : ℝ) ^ n * ‖δ‖ := by linarith
    calc ENNReal.ofReal (θ x) ≤ ENNReal.ofReal (θ a + (P : ℝ) ^ n * ‖δ‖) :=
          ENNReal.ofReal_le_ofReal hθx
      _ = ENNReal.ofReal (θ a) + ENNReal.ofReal ((P : ℝ) ^ n) * ‖δ‖ₑ := by
          rw [ENNReal.ofReal_add hθa.le (mul_nonneg hPn (norm_nonneg δ)), ENNReal.ofReal_mul hPn,
            ofReal_norm δ]
  -- Step 3: `μ(B_r(a)) ≤ θ(a) Hⁿ(M ∩ B_r(a)) + Pⁿ o(r)`, integrating (F2) over `M ∩ B_r(a)`
  have hmass : ∀ r : ℝ, μ (ball a r) ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) +
      ENNReal.ofReal ((P : ℝ) ^ n) *
        ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] := by
    intro r
    have hμB : μ (ball a r) = ∫⁻ x in M ∩ ball a r, ENNReal.ofReal (θ x) ∂μHE[n] := by
      rw [hμ, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
        inter_comm]
    rw [hμB]
    calc ∫⁻ x in M ∩ ball a r, ENNReal.ofReal (θ x) ∂μHE[n]
        ≤ ∫⁻ x in M ∩ ball a r, (ENNReal.ofReal (θ a) +
            ENNReal.ofReal ((P : ℝ) ^ n) * ‖θ x • ζ x - θ a • ζ a‖ₑ) ∂μHE[n] :=
          setLIntegral_mono' (hM.inter measurableSet_ball) fun x hx => hF2 x hx.1
      _ = ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) + ENNReal.ofReal ((P : ℝ) ^ n) *
            ∫⁻ x in M ∩ ball a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ hK]
      _ ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) + ENNReal.ofReal ((P : ℝ) ^ n) *
            ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] := by
          gcongr ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) + ENNReal.ofReal ((P : ℝ) ^ n) * ?_
          exact lintegral_mono_set (inter_subset_inter_right M ball_subset_closedBall)
  -- Step 4: (a) `ofReal (η₁/2) < μ(B_r(a)) / V(r)` eventually, by (L)
  have hea : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (η₁ / 2) < μ (ball a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) :=
    eventually_lt_of_lt_liminf
      (((ENNReal.ofReal_lt_ofReal_iff hη₁).2 (half_lt_self hη₁)).trans_le hL)
  -- (b) `Pⁿ o(r) / V(r) < ofReal (η₁/4)` eventually, since `Pⁿ o(r) / V(r) → Pⁿ · 0 = 0` by (D)
  have heb : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((P : ℝ) ^ n) *
      ((∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) /
        (unitBallVolume n * ENNReal.ofReal (r ^ n))) < ENNReal.ofReal (η₁ / 4) := by
    have hK0 := ENNReal.Tendsto.const_mul hD (Or.inr hK)
    rw [mul_zero] at hK0
    exact (tendsto_order.1 hK0).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  -- (c) `Hⁿ(M ∩ B̄_r(a)) / V(r) < 2` eventually, by (U)
  have hec : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < 2 :=
    eventually_lt_of_limsup_lt (hU.trans_lt ENNReal.one_lt_two)
  -- all three hold on some interval `(0, r₀)`
  obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hea.and (heb.and hec))
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  obtain ⟨ha', hb', hc'⟩ := hsub ⟨hr, hrr₀⟩
  set V := unitBallVolume n * ENNReal.ofReal (r ^ n)
  -- Step 5: clearing denominators; this already gives `Hⁿ(M ∩ B̄_r(a)) ≤ 2 V(r)`
  have hmV : ENNReal.ofReal (η₁ / 2) * V ≤ μ (ball a r) :=
    ((ENNReal.lt_div_iff_mul_lt (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 ha').le
  have hoV : ENNReal.ofReal ((P : ℝ) ^ n) *
      ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] ≤
        ENNReal.ofReal (η₁ / 4) * V := by
    rw [← mul_div_assoc] at hb'
    exact ((ENNReal.div_lt_iff (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 hb').le
  refine ⟨?_, ((ENNReal.div_lt_iff (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 hc').le⟩
  -- Step 6: split `ofReal (η₁/2) V` into two quarters and cancel the finite quarter
  have hq4 : 0 ≤ η₁ / 4 := by positivity
  have hsplit : ENNReal.ofReal (η₁ / 2) * V =
      ENNReal.ofReal (η₁ / 4) * V + ENNReal.ofReal (η₁ / 4) * V := by
    rw [show η₁ / 2 = η₁ / 4 + η₁ / 4 by ring, ENNReal.ofReal_add hq4 hq4, add_mul]
  have hq : ENNReal.ofReal (η₁ / 4) * V ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) := by
    have hfin : ENNReal.ofReal (η₁ / 4) * V ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hVt r)
    refine (ENNReal.add_le_add_iff_right hfin).1 ?_
    calc ENNReal.ofReal (η₁ / 4) * V + ENNReal.ofReal (η₁ / 4) * V
        = ENNReal.ofReal (η₁ / 2) * V := hsplit.symm
      _ ≤ μ (ball a r) := hmV
      _ ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) + ENNReal.ofReal ((P : ℝ) ^ n) *
            ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] := hmass r
      _ ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) + ENNReal.ofReal (η₁ / 4) * V := by
          gcongr
  -- Step 7: divide by `ofReal θ(a) ∈ (0, ∞)`
  have hθ0 : ENNReal.ofReal (θ a) ≠ 0 := (ENNReal.ofReal_pos.2 hθa).ne'
  have heq : ENNReal.ofReal (η₁ / (4 * θ a)) =
      (ENNReal.ofReal (θ a))⁻¹ * ENNReal.ofReal (η₁ / 4) := by
    rw [← ENNReal.ofReal_inv_of_pos hθa, ← ENNReal.ofReal_mul (inv_nonneg.2 hθa.le)]
    congr 1
    field_simp
  calc ENNReal.ofReal (η₁ / (4 * θ a)) * V
      = (ENNReal.ofReal (θ a))⁻¹ * (ENNReal.ofReal (η₁ / 4) * V) := by rw [heq, mul_assoc]
    _ ≤ (ENNReal.ofReal (θ a))⁻¹ * (ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r)) := by gcongr
    _ = μHE[n] (M ∩ ball a r) := ENNReal.inv_mul_cancel_left hθ0 ENNReal.ofReal_ne_top
/-- **Transfer of right-limits at `0` to a positive null sequence, times a finite constant**
(the limit arguments of steps 4 and 7 of the blow-up limit).  Let `f, h : ℝ → [0, ∞]`,
`C ≠ ∞`, and `sᵢ > 0` with `sᵢ → 0`.  Since every `sᵢ` lies in `(0, ∞)`, `s → 0` along
`𝓝[>] 0`.  (i) If `limsup_{r → 0⁺} f(r) ≤ 1`: as `C ≠ ∞`,
`limsup C f(sᵢ) = C limsup f(sᵢ)`, so it suffices that `limsup f(sᵢ) ≤ 1`.  For every `c > 1`,
eventually `f(r) < c` along `𝓝[>] 0`, hence eventually `f(sᵢ) ≤ c` and `limsup f(sᵢ) ≤ c`;
density of `[0, ∞]` gives `limsup f(sᵢ) ≤ 1`.  (ii) If `h(r) → 0` as `r → 0⁺`, then
`h(sᵢ) → 0` by composition, and `C h(sᵢ) → C · 0 = 0` as `C ≠ ∞`. -/
theorem Submission.dmcbr_ci_bl_null_seq_transfer : ∀ (f h : ℝ → ℝ≥0∞) (C : ℝ≥0∞) (s : ℕ → ℝ), C ≠ ∞ → (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) → (limsup f (𝓝[>] 0) ≤ 1 → limsup (fun i => C * f (s i)) atTop ≤ C) ∧ (Tendsto h (𝓝[>] 0) (𝓝 0) → Tendsto (fun i => C * h (s i)) atTop (𝓝 0)) := by
  intro f h C s hC hs hs0
  -- Step 1: `s → 0` along `𝓝[>] 0`
  have hs' : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall hs⟩
  refine ⟨fun hf => ?_, fun hh => ?_⟩
  · -- Step 2: `limsup C f(sᵢ) = C limsup f(sᵢ)`, so it suffices that `limsup f(sᵢ) ≤ 1`
    rw [ENNReal.limsup_const_mul_of_ne_top hC]
    refine mul_le_of_le_one_right' ?_
    -- Step 3: `limsup f(sᵢ) ≤ c` for every `c > 1`, hence `limsup f(sᵢ) ≤ 1`
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have hfc : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r < c := eventually_lt_of_limsup_lt (hf.trans_lt hc)
    exact limsup_le_of_le (h := (hs'.eventually hfc).mono fun i hi => hi.le)
  · -- Step 4: `h(sᵢ) → 0`, so `C h(sᵢ) → C · 0 = 0`
    have hCh := ENNReal.Tendsto.const_mul (hh.comp hs') (Or.inr hC)
    rwa [mul_zero] at hCh
/-- **Uniform bounds on compact sets** (step 3 of the blow-up limit argument in the
integer-multiplicity criterion for cycles: `supᵢ νᵢ(K) < ∞` for compact `K`).  If every `νᵢ` is
a finite measure on `ℝᴾ` and, for every `R > 0`, `νᵢ(B̄_R(0)) ≤ B < ∞` for all large `i`, then
`supᵢ νᵢ(K) < ∞` for every compact `K`.  `K` is bounded, so `K ⊆ B̄_R(0)` with `R = max(R₀, 1)`;
the indices `i ≥ N` are bounded by `B`, and the finitely many `i < N` by
`S = ∑_{j<N} νⱼ(ℝᴾ) < ∞`.  Hence `supᵢ νᵢ(K) ≤ max(B, S) < ∞`. -/
theorem Submission.dmcbr_ci_bl_compact_sup_bound : ∀ (P : ℕ) (ν : ℕ → Measure (Euclid P)), (∀ i, ν i univ < ∞) → (∀ R : ℝ, 0 < R → ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ᶠ i in atTop, ν i (closedBall 0 R) ≤ B) → ∀ K : Set (Euclid P), IsCompact K → ⨆ i, ν i K < ∞ := by
  intro P ν hfin hball K hK
  -- Step 1: `K ⊆ B̄_R(0)` with `R = max(R₀, 1) > 0`
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  have hKR : K ⊆ closedBall 0 (max R₀ 1) :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  -- Step 2: `νᵢ(B̄_R(0)) ≤ B` for all `i ≥ N`
  obtain ⟨B, hB, hev⟩ := hball (max R₀ 1) (one_pos.trans_le (le_max_right _ _))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- Step 3: `S = ∑_{j<N} νⱼ(ℝᴾ) < ∞`
  have hS : ∑ j ∈ Finset.range N, ν j univ < ∞ := ENNReal.sum_lt_top.2 fun j _ => hfin j
  -- Steps 4 and 5: `νᵢ(K) ≤ max(B, S)` for every `i`
  refine (iSup_le fun i => ?_).trans_lt (max_lt hB hS)
  rcases le_or_gt N i with hi | hi
  · exact le_max_of_le_left ((measure_mono hKR).trans (hN i hi))
  · exact le_max_of_le_right ((measure_mono (subset_univ K)).trans
      (Finset.single_le_sum (f := fun j => ν j univ) (fun _ _ => zero_le)
        (Finset.mem_range.2 hi)))
/-- **Pairing error for a non-constant multivector field** (the error estimate of steps 4 and 10
of the proof of `Submission.dmcbr_ci_blowup_limit`, for a single measure).  Let `w` be a
continuous covector field with `‖w‖ ≤ A` that vanishes outside `B̄_R = closedBall 0 R`, and
suppose `E = A ∫_{B̄_R} ‖τ − ζ₀‖ dν'` is finite.  The error `g(x) = ⟨w(x), τ(x) − ζ₀⟩` is a.e.
strongly measurable, being the continuous evaluation of `τ − ζ₀` at `w`.  By `le_opENorm`, and
since `w = 0` off `B̄_R`, `‖g(x)‖ ≤ 1_{B̄_R}(x) A ‖τ(x) − ζ₀‖`.  Hence `∫ ‖g‖ dν' ≤ E < ∞` and
`g` is integrable.  As `⟨w, τ⟩ = ⟨w, ζ₀⟩ + g`, the difference of the two integrals is
`∫ g dν'`, and `|∫ g dν'| ≤ ∫ ‖g‖ dν' ≤ E`. -/
theorem Submission.dmcbr_ci_bl_pairing_error_le : ∀ (P n : ℕ) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n) (A R : ℝ), AEStronglyMeasurable τ ν' → Continuous w → (∀ x, ‖w x‖ ≤ A) → (∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0) → Integrable (fun x => ζ₀ (w x)) ν' → ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' ≠ ∞ → |∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν'| ≤ (ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν').toReal := by
  intro P n ν' τ ζ₀ w A R hτ hw hwA hw0 hζ hE
  -- the error integrand `g(x) = ⟨w(x), τ(x) − ζ₀⟩`
  set g : Euclid P → ℝ := fun x => (τ x - ζ₀) (w x) with hg
  -- Step 1: `g` is a.e. strongly measurable (continuous evaluation of `τ − ζ₀` at `w`)
  have hgm : AEStronglyMeasurable g ν' :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : MultiVector P n) v => L v)
      isBoundedBilinearMap_apply.continuous (hτ.sub aestronglyMeasurable_const)
      hw.aestronglyMeasurable
  -- Step 2: `‖g(x)‖ₑ ≤ 1_{B̄_R}(x) A ‖τ(x) − ζ₀‖ₑ`
  have hpt : ∀ x, ‖g x‖ₑ ≤
      (closedBall (0 : Euclid P) R).indicator (fun x => ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : Euclid P) R
    · rw [indicator_of_mem hx, mul_comm]
      calc ‖g x‖ₑ ≤ ‖τ x - ζ₀‖ₑ * ‖w x‖ₑ := (τ x - ζ₀).le_opENorm (w x)
        _ ≤ ‖τ x - ζ₀‖ₑ * ENNReal.ofReal A := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hwA x)
    · rw [indicator_of_notMem hx, hg]
      simp [hw0 x hx]
  -- Step 3: `∫⁻ ‖g‖ₑ ≤ A ∫⁻_{B̄_R} ‖τ − ζ₀‖ₑ = E < ∞`
  have hlint : ∫⁻ x, ‖g x‖ₑ ∂ν' ≤
      ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' := by
    calc ∫⁻ x, ‖g x‖ₑ ∂ν'
        ≤ ∫⁻ x, (closedBall (0 : Euclid P) R).indicator
            (fun x => ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ) x ∂ν' := lintegral_mono hpt
      _ = ∫⁻ x in closedBall (0 : Euclid P) R, ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ ∂ν' :=
          lintegral_indicator measurableSet_closedBall _
      _ = ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 4: `g` is integrable
  have hgi : Integrable g ν' := ⟨hgm, hasFiniteIntegral_iff_enorm.2 (hlint.trans_lt hE.lt_top)⟩
  -- Step 5: `⟨w, τ⟩ = ⟨w, ζ₀⟩ + g`, so the difference of the integrals is `∫ g`
  have hint : ∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν' = ∫ x, g x ∂ν' := by
    have hsplit : (fun x => τ x (w x)) = fun x => ζ₀ (w x) + g x := by
      funext x
      simp [hg]
    rw [hsplit, integral_add hζ hgi, add_sub_cancel_left]
  -- Step 6: `|∫ g| ≤ (∫⁻ ‖g‖ₑ).toReal ≤ E.toReal`
  rw [hint, ← Real.norm_eq_abs, ← toReal_enorm]
  calc (‖∫ x, g x ∂ν'‖ₑ).toReal ≤ (∫⁻ x, ‖g x‖ₑ ∂ν').toReal :=
        ENNReal.toReal_mono (hlint.trans_lt hE.lt_top).ne (enorm_integral_le_lintegral_enorm _)
    _ ≤ _ := ENNReal.toReal_mono hE hlint

/-- **Pairings with a compactly supported covector field converge** (steps 4 and 6 of the proof
of `Submission.dmcbr_ci_blowup_limit`, for a single form `w`).  Let `νₖ, ν` be measures on `ℝᴾ`,
each `νₖ` finite on compact sets, with `∫ f dνₖ → ∫ f dν` for every continuous compactly
supported `f`, and let `τₖ : ℝᴾ → Λₙ` be `νₖ`-a.e. strongly measurable with
`δₖ(R) = ∫_{B̄_R(0)} ‖τₖ − ζ₀‖ dνₖ → 0` for every `R > 0`.  Then `∫ ⟨w, τₖ⟩ dνₖ → ∫ ⟨w, ζ₀⟩ dν`
for every continuous compactly supported `w : ℝᴾ → Λⁿ`.  Take `A ≥ ‖w‖` and `R > 0` with `w = 0`
off `B̄_R(0)`.  Then `f = ⟨w, ζ₀⟩` is continuous with compact support, hence `νₖ`-integrable.
Since `eₖ = A δₖ(R) → 0`, eventually `eₖ < ∞`, and `Submission.dmcbr_ci_bl_pairing_error_le`
gives `|∫ ⟨w, τₖ⟩ dνₖ − ∫ f dνₖ| ≤ eₖ → 0`; finally `∫ f dνₖ → ∫ f dν` by hypothesis. -/
theorem Submission.dmcbr_ci_bl_pairing_tendsto : ∀ (P n : ℕ) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (τs : ℕ → Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → νs k K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(νs k)) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ k, AEStronglyMeasurable (τs k) (νs k)) → (∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0)) → Continuous w → HasCompactSupport w → Tendsto (fun k => ∫ x, τs k x (w x) ∂(νs k)) atTop (𝓝 (∫ x, ζ₀ (w x) ∂ν)) := by
  intro P n νs ν τs ζ₀ w hνK hconv hτ hδ hw hwc
  -- Step 1: a bound `‖w‖ ≤ A` and a radius `R > 0` with `w = 0` off `B̄_R(0)`
  obtain ⟨A, hA⟩ := hw.bounded_above_of_compact_support hwc
  obtain ⟨R₀, hR₀⟩ := hwc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  obtain ⟨R, hR, hwR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport w ⊆ closedBall (0 : Euclid P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left R₀ 1))⟩
  have hw0 : ∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxw => hx (hwR hxw)
  -- Step 2: `f = ⟨w, ζ₀⟩` is continuous with compact support, hence `νₖ`-integrable
  have hfc : Continuous fun x => ζ₀ (w x) := ζ₀.continuous.comp hw
  have hfs : HasCompactSupport fun x => ζ₀ (w x) := hwc.comp_left (map_zero ζ₀)
  have hfi : ∀ k, Integrable (fun x => ζ₀ (w x)) (νs k) := fun k => by
    have : IsFiniteMeasureOnCompacts (νs k) := ⟨fun K hK => hνK k K hK⟩
    exact hfc.integrable_of_hasCompactSupport hfs
  -- Step 3: `eₖ = A δₖ(R) → 0`, so eventually `eₖ < 1` (hence `eₖ ≠ ∞`), and `eₖ.toReal → 0`
  have he : Tendsto (fun k => ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal A) (hδ R hR) (Or.inr ENNReal.ofReal_ne_top)
  have he1 : ∀ᶠ k in atTop, ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k) < 1 :=
    (tendsto_order.1 he).2 1 one_pos
  have heR : Tendsto (fun k => (ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  -- Step 4: `dₖ = ∫ ⟨w, τₖ⟩ dνₖ − ∫ f dνₖ` has `|dₖ| ≤ eₖ.toReal` once `eₖ < 1`, so `dₖ → 0`
  have hd : Tendsto (fun k => ∫ x, τs k x (w x) ∂(νs k) - ∫ x, ζ₀ (w x) ∂(νs k)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ heR
    filter_upwards [he1] with k hk
    rw [Real.norm_eq_abs]
    exact Submission.dmcbr_ci_bl_pairing_error_le P n (νs k) (τs k) ζ₀ w A R (hτ k) hw hA hw0
      (hfi k) (ne_top_of_lt hk)
  -- Step 5: `∫ ⟨w, τₖ⟩ dνₖ = dₖ + ∫ f dνₖ → 0 + ∫ f dν`
  have hsum := hd.add (hconv (fun x => ζ₀ (w x)) hfc hfs)
  rw [zero_add] at hsum
  exact hsum.congr fun k => sub_add_cancel _ _
/-- **Local mass of a current represented by a field near a constant multivector** (Simon 6.2.5;
the first half of step 10 of the blow-up limit in the integer-multiplicity criterion for cycles;
`|·|_E` is `covectorEuclideanNorm`).  Suppose `ν'` is finite on compact sets, `s, B ≥ 0`,
`|⟨α, ζ₀⟩| ≤ s |α|_E` and `‖α‖ ≤ B |α|_E` for every `α`, and `X(ω) = ∫ ⟨ω(x), τ(x)⟩ dν'(x)` for
every test form `ω`.  Then `M_G(X) ≤ s ν'(G) + E` for every open `G ⊆ B̄_R(0)`, where
`E = B ∫_{B̄_R(0)} ‖τ - ζ₀‖ dν'`.  Here `ν'(G) ≤ ν'(B̄_R(0)) < ∞`.  Fix an admissible `ω` and
assume `E < ∞`.  Then `w = ω` is continuous, vanishes off `G ⊆ B̄_R(0)`, and `‖w‖ ≤ B |w|_E ≤ B`,
and `⟨w, ζ₀⟩` is continuous with compact support, hence integrable.
`Submission.dmcbr_ci_bl_pairing_error_le` gives `X(ω) ≤ ∫ ⟨w, ζ₀⟩ dν' + E`, and `⟨w, ζ₀⟩ ≤ s 1_G`
pointwise gives `∫ ⟨w, ζ₀⟩ dν' ≤ s ν'(G)`. -/
theorem Submission.dmcbr_ci_bl_massOn_le : ∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) n) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (s B R : ℝ) (G : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν' K < ∞) → AEStronglyMeasurable τ ν' → 0 ≤ s → (∀ α : Covector (Euclid P) n, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → 0 ≤ B → (∀ α : Covector (Euclid P) n, ‖α‖ ≤ B * covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, X ω = ∫ x, τ x ((ω : DifferentialForm (Euclid P) n) x) ∂ν') → IsOpen G → G ⊆ closedBall (0 : Euclid P) R → X.massOn G ≤ ENNReal.ofReal s * ν' G + ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' := by
  intro P n X ν' τ ζ₀ s B R G hν'K hτ hs hζ₀ hB hBα hX hG hGR
  -- Step 1: `ν'(G) ≤ ν'(B̄_R(0)) < ∞`
  have hνG : ν' G ≠ ∞ :=
    ((measure_mono hGR).trans_lt (hν'K _ (isCompact_closedBall (0 : Euclid P) R))).ne
  -- Step 2: it suffices to bound `ofReal (X ω)` for each admissible `ω`; trivial if `E = ∞`
  refine sSup_le ?_
  rintro r ⟨ω, ⟨hωG, hω1⟩, rfl⟩
  set E := ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν'
  rcases eq_or_ne E ∞ with hEtop | hEtop
  · rw [hEtop, add_top]
    exact le_top
  -- Step 3: `w = ω` is continuous, vanishes off `G ⊆ B̄_R(0)`, and `‖w‖ ≤ B |w|_E ≤ B`
  have hωt : IsTestForm (ω : DifferentialForm (Euclid P) n) := ω.2.1
  have hXω := hX ω
  generalize (ω : DifferentialForm (Euclid P) n) = w at hωG hω1 hωt hXω
  have hwc : Continuous w := hωt.1.continuous
  have hwG : ∀ x, x ∉ G → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hωG hx')
  have hwR : ∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0 := fun x hx =>
    hwG x fun hxG => hx (hGR hxG)
  have hwB : ∀ x, ‖w x‖ ≤ B := fun x =>
    (hBα (w x)).trans ((mul_le_mul_of_nonneg_left (hω1 x) hB).trans_eq (mul_one B))
  -- `⟨w, ζ₀⟩` is continuous with compact support, hence `ν'`-integrable
  have hfi : Integrable (fun x => ζ₀ (w x)) ν' := by
    have : IsFiniteMeasureOnCompacts ν' := ⟨fun K hK => hν'K K hK⟩
    exact (ζ₀.continuous.comp hwc).integrable_of_hasCompactSupport
      (hωt.2.comp_left (map_zero ζ₀))
  -- Step 4: the pairing error estimate gives `X(ω) ≤ ∫ ⟨w, ζ₀⟩ dν' + E`
  have herr : |∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν'| ≤ E.toReal :=
    Submission.dmcbr_ci_bl_pairing_error_le P n ν' τ ζ₀ w B R hτ hwc hwB hwR hfi hEtop
  have hXle : X ω ≤ ∫ x, ζ₀ (w x) ∂ν' + E.toReal := by
    rw [hXω]
    linarith [(abs_sub_le_iff.1 herr).1]
  -- Step 5: `⟨w, ζ₀⟩ ≤ s 1_G` pointwise, so `∫ ⟨w, ζ₀⟩ dν' ≤ s ν'(G)`
  have hf_le : ∀ x, ζ₀ (w x) ≤ G.indicator (fun _ => s) x := by
    intro x
    by_cases hx : x ∈ G
    · rw [indicator_of_mem hx]
      calc ζ₀ (w x) ≤ |ζ₀ (w x)| := le_abs_self _
        _ ≤ s * covectorEuclideanNorm (w x) := hζ₀ _
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left (hω1 x) hs
        _ = s := mul_one s
    · rw [indicator_of_notMem hx, hwG x hx, map_zero]
  have hmain : ∫ x, ζ₀ (w x) ∂ν' ≤ s * ν'.real G :=
    calc ∫ x, ζ₀ (w x) ∂ν' ≤ ∫ x, G.indicator (fun _ => s) x ∂ν' :=
          integral_mono hfi
            ((integrable_indicator_iff hG.measurableSet).2 (integrableOn_const hνG)) hf_le
      _ = ν'.real G * s := by rw [integral_indicator_const _ hG.measurableSet, smul_eq_mul]
      _ = s * ν'.real G := mul_comm _ _
  -- Step 6: `ofReal (X ω) ≤ ofReal (s ν'(G)) + ofReal E = ofReal s * ν'(G) + E` in `[0, ∞]`
  calc ENNReal.ofReal (X ω) ≤ ENNReal.ofReal (s * ν'.real G + E.toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (s * ν'.real G) + ENNReal.ofReal E.toReal := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal s * ν' G + E := by
        rw [ENNReal.ofReal_mul hs, measureReal_def, ENNReal.ofReal_toReal hνG,
          ENNReal.ofReal_toReal hEtop]
/-- **A `limsup` bound through closed thickenings of a compact set** (the second half of step 10
of the blow-up limit in the integer-multiplicity criterion for cycles, there with `aₖ = μₖ(K)` and
`c = θ(a)`).  Write `K_r = cthickening r K`.  For `r > 0`, `K_r` is compact, so
`limsupₖ c νₖ(K_r) = c limsupₖ νₖ(K_r) ≤ c ν(K_r)` (`c ≠ ∞`); as `vₖ → 0`, the bound
`aₖ ≤ c νₖ(K_r) + vₖ` gives `limsupₖ aₖ ≤ c ν(K_r)`.  `K` is closed and `ν(K_1) < ∞`, so
`ν(K_r) → ν(K)` as `r ↓ 0`, and `limsupₖ aₖ ≤ c ν(K)`. -/
theorem Submission.dmcbr_ci_bl_limsup_le_of_cthickening : ∀ (P : ℕ) (a : ℕ → ℝ≥0∞) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (c : ℝ≥0∞) (K : Set (Euclid P)), IsCompact K → c ≠ ∞ → (∀ K' : Set (Euclid P), IsCompact K' → ν K' < ∞) → (∀ K' : Set (Euclid P), IsCompact K' → limsup (fun k => νs k K') atTop ≤ ν K') → (∀ r : ℝ, 0 < r → ∃ v : ℕ → ℝ≥0∞, Tendsto v atTop (𝓝 0) ∧ ∀ k, a k ≤ c * νs k (cthickening r K) + v k) → limsup a atTop ≤ c * ν K := by
  intro P a νs ν c K hK hc hνK hlim hbound
  -- Steps 1–2: `limsupₖ aₖ ≤ c ν(K_r)` for every `r > 0`
  have hr_le : ∀ r : ℝ, 0 < r → limsup a atTop ≤ c * ν (cthickening r K) := by
    intro r hr
    obtain ⟨v, hv, hav⟩ := hbound r hr
    -- Step 1: `limsupₖ c νₖ(K_r) = c limsupₖ νₖ(K_r) ≤ c ν(K_r)`, `K_r` being compact
    have hmain : limsup (fun k => c * νs k (cthickening r K)) atTop ≤
        c * ν (cthickening r K) := by
      rw [ENNReal.limsup_const_mul_of_ne_top hc]
      gcongr
      exact hlim _ hK.cthickening
    -- Step 2: for `d > c ν(K_r)` pick `c ν(K_r) < b < d`; eventually `c νₖ(K_r) < b` and
    -- `vₖ < d − b`, hence `aₖ ≤ b + (d − b) = d`
    refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
    obtain ⟨b, hb, hbd⟩ := exists_between hd
    have h₁ : ∀ᶠ k in atTop, c * νs k (cthickening r K) < b :=
      eventually_lt_of_limsup_lt (hmain.trans_lt hb)
    have h₂ : ∀ᶠ k in atTop, v k < d - b := (tendsto_order.1 hv).2 _ (tsub_pos_of_lt hbd)
    refine limsup_le_of_le (h := ?_)
    filter_upwards [h₁, h₂] with k hk₁ hk₂
    calc a k ≤ c * νs k (cthickening r K) + v k := hav k
      _ ≤ b + (d - b) := add_le_add hk₁.le hk₂.le
      _ = d := add_tsub_cancel_of_le hbd.le
  -- Step 3: `K` is closed and `ν(K_1) < ∞`, so `ν(K_r) → ν(K)` and `c ν(K_r) → c ν(K)` as `r ↓ 0`
  have hfin : ∃ R > 0, ν (cthickening R K) ≠ ∞ := ⟨1, one_pos, (hνK _ hK.cthickening).ne⟩
  have hνr : Tendsto (fun r => ν (cthickening r K)) (𝓝 0) (𝓝 (ν K)) :=
    tendsto_measure_cthickening_of_isClosed hfin hK.isClosed
  have htend : Tendsto (fun r => c * ν (cthickening r K)) (𝓝[>] 0) (𝓝 (c * ν K)) :=
    (ENNReal.Tendsto.const_mul hνr (Or.inr hc)).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hr_le)

/-- **Blow-ups of a represented cycle at a good point converge to a constant-orientation cycle
with the integer slice property** (steps 4–5 of the integer-multiplicity criterion for cycles;
blow-ups `η_{a,λ#}` as in Simon 7.3, change of variables as in the proof of Simon Ch. 6, 8.1).
Put `τ = θζ`, `θ₀ = θ(a) > 0`, `τ₀ = θ₀ ζ(a)`, `ηᵢ = η_{a,λᵢ}`, `Nᵢ = ηᵢ(M)` and `νᵢ = Hⁿ⌞Nᵢ`.
`dmcbr_ci_bl_density_bounds` gives `(η₁/(4θ₀)) ωₙrⁿ ≤ Hⁿ(M ∩ B_r(a))` and
`Hⁿ(M ∩ B̄_r(a)) ≤ 2ωₙrⁿ` for `0 < r < r₀`.  The dilations `Γ'ᵢ` of `Γ` by `ηᵢ`
(`dmcbr_ci_dilation_calculus`) are cycles with the admissible representations
`(λᵢ⁻ⁿ ηᵢ#μ, ζ(a + λᵢ ·))`, and `Γ'ᵢ(ω) = ∫_{Nᵢ} ⟨ω(y), τ(a + λᵢy)⟩ dHⁿ(y)`
(`dmcbr_ci_bl_blowup_scale`).  By `cbr_ci_bl_blowUp_restrict_scaling` and
`dmcbr_ci_bl_scale_identities`, `νᵢ(B̄_R(0)) = ωₙRⁿ · Hⁿ(M ∩ B̄_{λᵢR}(a))/(ωₙ(λᵢR)ⁿ) ≤ 2ωₙRⁿ` once
`λᵢR < r₀`; so `supᵢ νᵢ(K) < ∞` (`dmcbr_ci_bl_compact_sup_bound`), and (T1) gives `φ` and `ν` with
`ν_{φ(k)} → ν`.  `C(ω) = ∫ ⟨ω, τ₀⟩ dν` is a current (`cmcs_restrict_current`).  The Lebesgue point
hypothesis, transferred along `λ_{φ(k)}R ↓ 0` (`dmcbr_ci_bl_null_seq_transfer`), gives
`∫_{B̄_R(0)} ‖τ(a + λ_{φ(k)}y) − τ₀‖ dν_{φ(k)} → 0`, hence `Γ_k = Γ'_{φ(k)} ⇀ C`
(`dmcbr_ci_bl_pairing_tendsto`).  The open-set liminf and compact-set limsup of (T1), with the
upper density and the density lower bound, give `ν(B_R(0)) ≤ ωₙRⁿ` and `ν(B_r(0)) > 0`;
`∂C(ψ) = lim ∂Γ_k(ψ) = 0`; `M_W(C) = θ₀ ν(W)` by `cbr_ci_const_vector_massOn`.  On `G = K_r`,
`μ_k(K) ≤ M_G(Γ_k) ≤ θ₀ ν_{φ(k)}(K̄_r) + Pⁿ ∫_{B̄_R(0)} ‖τ(a + λ_{φ(k)}y) − τ₀‖ dν_{φ(k)}`
(`dmcbr_ci_bl_massOn_le`, `dmcbr_ci_bl_covector_opNorm_le`), so
`limsup_k μ_k(K) ≤ θ₀ ν(K)` (`dmcbr_ci_bl_limsup_le_of_cthickening`).  Finally every `Γ_k` has the
integer slice property (`dmcbr_ci_dilation_slice_property`), and
`M_W(Γ_k) + M_W(∂Γ_k) = μ_k(W) ≤ μ_k(closure W)` is bounded in `k` (`dmcbr_ci_bl_compact_sup_bound`
again), so SLIM gives the integer slice property of `C`. -/
theorem Submission.dmcbr_ci_blowup_limit : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (P d : ℕ), (∀ (Xs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ i, (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Xs i ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Xs i).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → ⨆ i, ((Xs i).massOn W + (Xs i).boundary.massOn W) < ∞) → WeaklyConvergesOn Xs X → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → ∀ (Γ : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P (d + 1)) (a : Euclid P) (η₁ : ℝ) (lams : ℕ → ℝ), Γ.boundary = 0 → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Γ).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → MeasurableSet M → μHE[(d + 1)] M < ∞ → Measurable θ → StronglyMeasurable ζ → μ = (μHE[(d + 1)].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ (x : Euclid P) (α : Covector (Euclid P) (d + 1)), |ζ x α| ≤ covectorEuclideanNorm α) → (∀ x ∈ M, ∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μHE[(d + 1)]) → a ∈ M → 0 < η₁ → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => μ (ball a r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) → limsup (fun r : ℝ => μHE[(d + 1)] (M ∩ closedBall a r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[(d + 1)]) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) (𝓝 0) → (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (ν : Measure (Euclid P)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (Γs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P (d + 1)), StrictMono φ ∧ (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) ∧ (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1))) ∧ (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ y, θ a * ζ a ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂ν) ∧ C.boundary = 0 ∧ (∀ W : Set (Euclid P), IsOpen W → C.massOn W = ENNReal.ofReal (θ a) * ν W) ∧ (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) ∧ WeaklyConvergesOn Γs C ∧ (∀ k, (Γs k).boundary = 0) ∧ (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → μs k K < ∞) ∧ (∀ (k : ℕ) (W : Set (Euclid P)), IsOpen W → (Γs k).massOn W = μs k W) ∧ (∀ k, AEStronglyMeasurable (ξs k) (μs k)) ∧ (∀ k, ∀ᵐ x ∂(μs k), ∀ α : Covector (Euclid P) (d + 1), |ξs k x α| ≤ covectorEuclideanNorm α) ∧ (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)), Γs k ω = ∫ x, ξs k x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(μs k)) ∧ (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μs k K) atTop ≤ ENNReal.ofReal (θ a) * ν K) ∧ (∀ k, μs k (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)ᶜ = 0) ∧ (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μHE[(d + 1)] (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M ∩ K)) atTop ≤ ν K) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M, f y ∂μHE[(d + 1)]) atTop (𝓝 (∫ y, f y ∂ν))) := by
  intro hSL hRU hCT P d hSLIM Γ μ M θ ζ a η₁ lams hΓb hΓisp hμfin hΓmass hM hMfin hθ hζ hμ hθpos
    hζb hζβ hΓrep haM hη₁ hlow hup hosc hlpos hlim
  obtain ⟨hT1, -, -⟩ := hCT
  -- Step 0: `θ₀ = θ(a) > 0`, the constant multivector `τ₀ = θ₀ ζ(a)` with `|⟨α, τ₀⟩| ≤ θ₀ |α|`,
  -- `0 < ωₙ < ∞`, and `μ` is finite on compact sets
  have hθ₀ : 0 < θ a := hθpos a haM
  obtain ⟨β, hβ1, hβ⟩ := hζβ a haM
  have hτ₀b : ∀ α : Covector (Euclid P) (d + 1),
      |(θ a • ζ a) α| ≤ θ a * covectorEuclideanNorm α := by
    intro α
    rw [_root_.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hθ₀]
    exact mul_le_mul_of_nonneg_left (hζb a α) hθ₀.le
  have hω0 : unitBallVolume (d + 1) ≠ 0 :=
    (measure_ball_pos volume (0 : Euclid (d + 1)) one_pos).ne'
  have hωtop : unitBallVolume (d + 1) ≠ ∞ := by
    show volume (ball (0 : Euclid (d + 1)) 1) ≠ ∞
    exact measure_ball_lt_top.ne
  have hμK : ∀ K : Set (Euclid P), IsCompact K → μ K < ∞ :=
    fun K _ => (measure_mono (subset_univ K)).trans_lt hμfin
  -- Step 1: density bounds at `a`, for `0 < r < r₀`
  obtain ⟨r₀, hr₀, hdens⟩ := Submission.dmcbr_ci_bl_density_bounds P (d + 1) μ M θ ζ a η₁ hM hθ hζ
    hμ hθpos hζb hζβ haM hη₁ hlow hup hosc
  -- Step 2: the blow-ups `Γ'ᵢ`, dilations of `Γ` by `ηᵢ = η_{a,λᵢ}`, with their representations
  choose Γ' hΓ' using fun i =>
    (Submission.dmcbr_ci_dilation_calculus P (d + 1) a (lams i) (hlpos i)).1 Γ
  have hbs := fun i => Submission.dmcbr_ci_bl_blowup_scale P d Γ (Γ' i) μ M θ ζ a (lams i)
    (hlpos i) hΓb hμfin hΓmass hM hθ hζ hμ hθpos hΓrep
    ((Submission.dmcbr_ci_dilation_calculus P d a (lams i) (hlpos i)).2.1 Γ (Γ' i) (hΓ' i))
    ((Submission.dmcbr_ci_dilation_calculus P (d + 1) a (lams i) (hlpos i)).2.2.2.1 Γ (Γ' i) μ ζ
      (hΓ' i))
    ((Submission.dmcbr_ci_dilation_calculus P (d + 1) a (lams i) (hlpos i)).2.2.2.2.1 Γ (Γ' i)
      (hΓ' i))
  have hΓμ := (hbs 0).1
  -- `νᵢ = Hⁿ⌞ηᵢ(M)` and its scale identities
  have hsc := fun i => Submission.dmcbr_ci_bl_scale_identities P (d + 1) M θ ζ a (lams i)
    (hlpos i)
    (Submission.cbr_ci_bl_blowUp_restrict_scaling P (d + 1) M θ a (lams i) hM hθ (hlpos i)).2.1
  have hνi_univ : ∀ i, (μHE[(d + 1)].restrict
      (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M)) univ < ∞ := fun i => by
    rw [(hsc i).1]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMfin
  -- Step 3: uniform bounds, `νᵢ(B̄_R(0)) ≤ 2 ωₙ Rⁿ` once `λᵢ R < r₀`, so `supᵢ νᵢ(K) < ∞`
  have hevR : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, lams i * R < r₀ := fun R _ => by
    have h := hlim.mul_const R
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds hr₀)
  have hsup := Submission.dmcbr_ci_bl_compact_sup_bound P
    (fun i => μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M))
    hνi_univ fun R hR => ⟨unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1)) * 2,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hωtop.lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofNat_lt_top,
      (hevR R hR).mono fun i hi => by
        rw [((hsc i).2 R hR).1]
        gcongr
        exact ENNReal.div_le_of_le_mul (hdens _ (mul_pos (hlpos i) hR) hi).2⟩
  -- Step 5: compactness (T1) gives `ν_{φ(k)} → ν`
  obtain ⟨φ, ν, hφ, -, hνK, hνf, hνlimsup, hνliminf⟩ := hT1 P univ
    (fun i => μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M))
    isOpen_univ fun K hK _ => hsup K hK
  have hνK' : ∀ K : Set (Euclid P), IsCompact K → ν K < ∞ := fun K hK => hνK K hK (subset_univ K)
  have hνf' : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂(μHE[(d + 1)].restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))) atTop (𝓝 (∫ x, f x ∂ν)) :=
    fun f hf hfc => hνf f hf hfc (subset_univ _)
  have hνsK : ∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → (μHE[(d + 1)].restrict
      (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) K < ∞ :=
    fun k K _ => (measure_mono (subset_univ K)).trans_lt (hνi_univ (φ k))
  have hs0 : ∀ R : ℝ, Tendsto (fun k => lams (φ k) * R) atTop (𝓝 0) := fun R => by
    simpa using (hlim.comp hφ.tendsto_atTop).mul_const R
  -- the blown-up field `τ(a + λy) = θ(a + λy) ζ(a + λy)` is measurable
  have hτm : ∀ k, AEStronglyMeasurable
      (fun y => θ (a + lams (φ k) • y) • ζ (a + lams (φ k) • y))
      (μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) := by
    intro k
    have hg : Measurable fun y : Euclid P => a + lams (φ k) • y :=
      (continuous_const.add (continuous_const_smul _)).measurable
    exact ((hθ.comp hg).stronglyMeasurable.smul (hζ.comp_measurable hg)).aestronglyMeasurable
  -- Step 4: the null-sequence transfer of the upper density and Lebesgue point hypotheses
  have htr := fun (c : ℝ≥0∞) (s : ℕ → ℝ) => Submission.dmcbr_ci_bl_null_seq_transfer
    (fun r : ℝ => μHE[(d + 1)] (M ∩ closedBall a r) /
      (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1))))
    (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[(d + 1)]) /
      (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) c s
  have hcR : ∀ R : ℝ, unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1)) ≠ ∞ :=
    fun R => ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  -- `∫_{B̄_R(0)} ‖τ(a + λ_{φ(k)} y) − τ₀‖ dν_{φ(k)} → 0`
  have hosc' : ∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ y in closedBall (0 : Euclid P) R,
      ‖θ (a + lams (φ k) • y) • ζ (a + lams (φ k) • y) - θ a • ζ a‖ₑ ∂(μHE[(d + 1)].restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))) atTop (𝓝 0) := by
    intro R hR
    refine ((htr _ (fun k => lams (φ k) * R) (hcR R) (fun k => mul_pos (hlpos _) hR)
      (hs0 R)).2 hosc).congr fun k => ?_
    exact (((hsc (φ k)).2 R hR).2.2).symm
  -- Step 6: the limit current `C(ω) = ∫ ⟨ω, θ₀ ζ(a)⟩ dν`, and `Γ_k ⇀ C`
  obtain ⟨C, hC⟩ := Submission.cmcs_restrict_current P (d + 1) univ (ENNReal.ofReal (θ a) • ν)
    (fun _ => ζ a) univ (fun K hK _ => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hνK' K hK))
    aestronglyMeasurable_const (Eventually.of_forall fun _ α => hζb a α)
  have hCν : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      C ω = ∫ y, θ a * ζ a ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂ν := by
    intro ω
    rw [hC ω, Measure.restrict_univ, integral_smul_measure, ENNReal.toReal_ofReal hθ₀.le,
      smul_eq_mul, integral_const_mul]
  have hweak : WeaklyConvergesOn (fun k => Γ' (φ k)) C := by
    intro ω
    have h := Submission.dmcbr_ci_bl_pairing_tendsto P (d + 1)
      (fun k => μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))
      ν (fun k y => θ (a + lams (φ k) • y) • ζ (a + lams (φ k) • y)) (θ a • ζ a)
      (ω : DifferentialForm (Euclid P) (d + 1)) hνsK hνf' hτm hosc' ω.property.1.1.continuous
      ω.property.1.2
    have hlimit : ∫ x, (θ a • ζ a) ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂ν = C ω := by
      simp only [hCν ω, _root_.smul_apply, smul_eq_mul]
    rw [← hlimit]
    exact h.congr fun k => ((hbs (φ k)).2.2.2.2.2.2.2 ω).symm
  -- Step 7: `ν(B_R(0)) ≤ ωₙ Rⁿ` and `ν(B_r(0)) > 0`
  have hνball : ∀ R : ℝ, 0 < R →
      ν (ball 0 R) ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1)) := by
    intro R hR
    calc ν (ball 0 R)
        ≤ liminf (fun k => (μHE[(d + 1)].restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) (ball 0 R)) atTop :=
          hνliminf _ isOpen_ball (subset_univ _)
      _ ≤ liminf (fun k => (μHE[(d + 1)].restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) (closedBall 0 R)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => measure_mono ball_subset_closedBall)
      _ ≤ limsup (fun k => (μHE[(d + 1)].restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) (closedBall 0 R)) atTop :=
          liminf_le_limsup
      _ = limsup (fun k => unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1)) *
            (μHE[(d + 1)] (M ∩ closedBall a (lams (φ k) * R)) /
              (unitBallVolume (d + 1) * ENNReal.ofReal ((lams (φ k) * R) ^ (d + 1))))) atTop := by
          congr 1
          funext k
          exact ((hsc (φ k)).2 R hR).1
      _ ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1)) :=
          (htr _ (fun k => lams (φ k) * R) (hcR R) (fun k => mul_pos (hlpos _) hR) (hs0 R)).1 hup
  have hνpos : ∀ r : ℝ, 0 < r → 0 < ν (ball 0 r) := by
    intro r hr
    have hr2 : 0 < r / 2 := half_pos hr
    have hev : ∀ᶠ k in atTop, lams (φ k) * (r / 2) < r₀ :=
      hφ.tendsto_atTop.eventually (hevR (r / 2) hr2)
    calc 0 < unitBallVolume (d + 1) * ENNReal.ofReal ((r / 2) ^ (d + 1)) *
          ENNReal.ofReal (η₁ / (4 * θ a)) :=
          ENNReal.mul_pos (ENNReal.mul_pos hω0 (ENNReal.ofReal_pos.2 (pow_pos hr2 _)).ne').ne'
            (ENNReal.ofReal_pos.2 (div_pos hη₁ (by positivity))).ne'
      _ ≤ limsup (fun k => (μHE[(d + 1)].restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))
              (closedBall 0 (r / 2))) atTop := by
          refine le_limsup_of_frequently_le (hev.mono fun k hk => ?_).frequently
          have hlr : 0 < lams (φ k) * (r / 2) := mul_pos (hlpos _) hr2
          calc unitBallVolume (d + 1) * ENNReal.ofReal ((r / 2) ^ (d + 1)) *
                ENNReal.ofReal (η₁ / (4 * θ a))
              ≤ unitBallVolume (d + 1) * ENNReal.ofReal ((r / 2) ^ (d + 1)) *
                (μHE[(d + 1)] (M ∩ ball a (lams (φ k) * (r / 2))) /
                  (unitBallVolume (d + 1) *
                    ENNReal.ofReal ((lams (φ k) * (r / 2)) ^ (d + 1)))) := by
                gcongr
                rw [ENNReal.le_div_iff_mul_le
                  (Or.inl (ENNReal.mul_pos hω0 (ENNReal.ofReal_pos.2 (pow_pos hlr _)).ne').ne')
                  (Or.inl (hcR _))]
                exact (hdens _ hlr hk).1
            _ = (μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))
                  (ball 0 (r / 2)) := (((hsc (φ k)).2 (r / 2) hr2).2.1).symm
            _ ≤ _ := measure_mono ball_subset_closedBall
      _ ≤ ν (closedBall 0 (r / 2)) := hνlimsup _ (isCompact_closedBall 0 (r / 2)) (subset_univ _)
      _ ≤ ν (ball 0 r) := measure_mono (closedBall_subset_ball (by linarith))
  -- Step 8: `∂C = 0`, as `∂C(ψ) = lim ∂Γ_k(ψ) = 0`
  have hCb : C.boundary = 0 := by
    apply GeometricCurrentOn.ext
    intro ψ
    have h : Tendsto (fun k => (Γ' (φ k)).boundary ψ) atTop (𝓝 (C.boundary ψ)) :=
      hweak.boundary ψ
    have h0 : ∀ k, (Γ' (φ k)).boundary ψ = 0 := fun k => by simp [(hbs (φ k)).2.1]
    simp only [h0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- Step 9: `M_W(C) = θ₀ ν(W)`
  have hCmass : ∀ W : Set (Euclid P), IsOpen W → C.massOn W = ENNReal.ofReal (θ a) * ν W :=
    Submission.cbr_ci_const_vector_massOn P (d + 1) ν (θ a • ζ a) (θ a) C hνK' hτ₀b
      ⟨β, hβ1, by rw [_root_.smul_apply, hβ, smul_eq_mul, mul_one]⟩
      fun ω => by simp only [hCν ω, _root_.smul_apply, smul_eq_mul]
  -- Step 10: `limsup_k μ_k(K) ≤ θ₀ ν(K)`, comparing `Γ_k` with the constant `τ₀` on `G = K_r`
  have hμlimsup : ∀ K : Set (Euclid P), IsCompact K →
      limsup (fun k => (ENNReal.ofReal ((lams (φ k))⁻¹ ^ (d + 1)) •
        Measure.map (dilation a (lams (φ k))) μ) K) atTop ≤ ENNReal.ofReal (θ a) * ν K := by
    intro K hK
    refine Submission.dmcbr_ci_bl_limsup_le_of_cthickening P _
      (fun k => μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M))
      ν (ENNReal.ofReal (θ a)) K hK ENNReal.ofReal_ne_top hνK'
      (fun K' hK' => hνlimsup K' hK' (subset_univ K')) fun r hr => ?_
    obtain ⟨R, hR0, hR⟩ := (hK.isBounded.cthickening (δ := r)).subset_closedBall_lt 0 0
    refine ⟨fun k => ENNReal.ofReal ((P : ℝ) ^ (d + 1)) * ∫⁻ y in closedBall (0 : Euclid P) R,
      ‖θ (a + lams (φ k) • y) • ζ (a + lams (φ k) • y) - θ a • ζ a‖ₑ ∂(μHE[(d + 1)].restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)), ?_, fun k => ?_⟩
    · have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((P : ℝ) ^ (d + 1)))
        (hosc' R hR0) (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h
    · have h1 := Submission.dmcbr_ci_bl_massOn_le P (d + 1) (Γ' (φ k)) _ _ (θ a • ζ a) (θ a)
        ((P : ℝ) ^ (d + 1)) R (thickening r K) (hνsK k) (hτm k) hθ₀.le hτ₀b (by positivity)
        (Submission.dmcbr_ci_bl_covector_opNorm_le P (d + 1)) ((hbs (φ k)).2.2.2.2.2.2.2)
        isOpen_thickening ((thickening_subset_cthickening r K).trans hR)
      rw [(hbs (φ k)).2.2.2.1 _ isOpen_thickening] at h1
      calc _ ≤ (ENNReal.ofReal ((lams (φ k))⁻¹ ^ (d + 1)) •
            Measure.map (dilation a (lams (φ k))) μ) (thickening r K) :=
            measure_mono (self_subset_thickening hr K)
        _ ≤ _ := h1
        _ ≤ _ := by
            gcongr
            exact thickening_subset_cthickening r K
  -- Step 11: every `Γ_k` has the integer slice property (dilation), hence so does `C` (SLIM)
  have hΓsisp := fun k => Submission.dmcbr_ci_dilation_slice_property hSL hRU P d a (lams (φ k)) Γ
    (Γ' (φ k)) μ ζ (hlpos _) (hΓ' (φ k)) hΓb hμK hζ.aestronglyMeasurable
    (Eventually.of_forall fun x α => hζb x α) hΓμ hΓisp
  have hμs_univ : ∀ k, (ENNReal.ofReal ((lams (φ k))⁻¹ ^ (d + 1)) •
      Measure.map (dilation a (lams (φ k))) μ) univ < ∞ := fun k => by
    have hD : Measurable (dilation a (lams (φ k))) := by
      unfold dilation
      exact (continuous_const.add (dilationCLM P _).continuous).measurable
    rw [Measure.smul_apply, Measure.map_apply hD MeasurableSet.univ, preimage_univ, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμfin
  have hμsup := Submission.dmcbr_ci_bl_compact_sup_bound P
    (fun k => ENNReal.ofReal ((lams (φ k))⁻¹ ^ (d + 1)) • Measure.map (dilation a (lams (φ k))) μ)
    hμs_univ fun R _ => ⟨ENNReal.ofReal (θ a) * ν (closedBall 0 R) + 1,
      ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (hνK' _ (isCompact_closedBall 0 R)), ENNReal.one_lt_top⟩,
      (eventually_lt_of_limsup_lt ((hμlimsup _ (isCompact_closedBall 0 R)).trans_lt
        (ENNReal.lt_add_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (hνK' _ (isCompact_closedBall 0 R)).ne) one_ne_zero))).mono fun k hk => hk.le⟩
  have hzero : ∀ W : Set (Euclid P),
      (0 : GeometricCurrentOn (univ : Set (Euclid P)) d).massOn W = 0 := by
    intro W
    refine le_antisymm (sSup_le ?_) zero_le
    rintro r ⟨ω, -, rfl⟩
    simp
  have hCisp := hSLIM (fun k => Γ' (φ k)) C hΓsisp (fun W hW hWc => by
      refine lt_of_le_of_lt (iSup_mono fun k => ?_) (hμsup _ hWc.1)
      rw [(hbs (φ k)).2.1, hzero, add_zero, (hbs (φ k)).2.2.2.1 W hW]
      exact measure_mono subset_closure) hweak
  -- Step 12: assemble
  refine ⟨φ, ν, C, fun k => Γ' (φ k),
    fun k => ENNReal.ofReal ((lams (φ k))⁻¹ ^ (d + 1)) • Measure.map (dilation a (lams (φ k))) μ,
    fun k y => ζ (a + lams (φ k) • y), hφ, hνK', hνball, hνpos, hCν, hCb, hCmass, hCisp, hweak,
    fun k => (hbs (φ k)).2.1, fun k => (hbs (φ k)).2.2.1, fun k => (hbs (φ k)).2.2.2.1,
    fun k => (hbs (φ k)).2.2.2.2.1, fun k => Eventually.of_forall fun y α => hζb _ α,
    fun k => (hbs (φ k)).2.2.2.2.2.1, hμlimsup, fun k => (hbs (φ k)).2.2.2.2.2.2.1,
    fun K hK => ?_, hνf'⟩
  calc limsup (fun k => μHE[(d + 1)]
        (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M ∩ K)) atTop
      = limsup (fun k => (μHE[(d + 1)].restrict
          (Poincare.SimonGMT.Chapter03.blowUpMap a (lams (φ k)) '' M)) K) atTop := by
        congr 1
        funext k
        rw [Measure.restrict_apply hK.measurableSet, inter_comm]
    _ ≤ ν K := hνlimsup K hK (subset_univ K)

/-- **Smooth approximation of `g ∈ C_c(ℝᴾ)`** (steps 4–5 of the translation-invariance proof):
mollify, `u_k = ρ_k ⋆ g` with `ρ_k` the normalized mollifier of radius `1/(k+1)`.  Each `u_k` is
`C^∞` (smooth compactly supported kernel against a locally integrable `g`), vanishes off
`K = B̄_{R₀+1}(0)` where `tsupport g ⊆ B̄_{R₀}(0)`, and the averaging estimate
`dist_convolution_le` gives `|u_k| ≤ M = sup ‖g‖` and, by continuity of `g`, `u_k(x) → g(x)`. -/
theorem Submission.cbr_ci_cp_tr_smooth_approx_of_continuous : ∀ (P : ℕ) (g : Euclid P → ℝ), Continuous g → HasCompactSupport g → ∃ (K : Set (Euclid P)) (C : ℝ) (u : ℕ → Euclid P → ℝ), IsCompact K ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) ∧ (∀ k x, x ∉ K → u k x = 0) ∧ (∀ k x, |u k x| ≤ C) ∧ ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (g x)) := by
  intro P g hg hgc
  -- mollifiers `ρ k ≥ 0`, `∫ ρ k = 1`, supported in `B_{1/(k+1)}(0)`
  choose ρ hρs hρc hρn hρi hρb using fun k : ℕ =>
    Submission.dgcr_stc_exists_normalized_mollifier P (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  -- `tsupport g ⊆ B̄_{R₀}(0)` and `‖g‖ ≤ M`
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hgm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  refine ⟨closedBall 0 (R₀ + 1), M,
    fun k => convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    isCompact_closedBall 0 (R₀ + 1),
    fun k => (hρc k).contDiff_convolution_left _ (hρs k) hg.locallyIntegrable, ?_, ?_, ?_⟩
  · -- vanishing off `K = B̄_{R₀+1}(0)`
    intro k x hx
    show convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0
    rw [convolution_def]
    have h0 : ∀ t, ContinuousLinearMap.lsmul ℝ ℝ (ρ k t) (g (x - t)) = 0 := by
      intro t
      by_cases ht : ρ k t = 0
      · simp [ht]
      · have ht' : ‖t‖ < 1 / ((k : ℝ) + 1) := mem_ball_zero_iff.1 (hρb k ht)
        have hk : 1 / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hxt : x - t ∉ tsupport g := by
          intro hmem
          have h1 : ‖x - t‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hR₀ hmem)
          apply hx
          rw [mem_closedBall_zero_iff]
          calc ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
            _ ≤ R₀ + 1 := by linarith
        simp [image_eq_zero_of_notMem_tsupport hxt]
    simp only [h0, integral_zero]
  · -- uniform bound `|u k| ≤ M`
    intro k x
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ))
      ((norm_nonneg _).trans (hM 0)) (hρb k) (hρn k) (hρi k) hgm
      (fun y _ => by rw [dist_zero_right]; exact hM y)
    rw [Real.dist_eq, sub_zero] at h
    exact h
  · -- pointwise convergence `u k x → g x`
    intro x
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hgδ⟩ := Metric.continuous_iff.1 hg x (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun k hk => ?_⟩
    have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hk
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (half_pos hε).le (hρb k) (hρn k) (hρi k) hgm
      (fun y hy => (hgδ y ((mem_ball.1 hy).trans_le hkN |>.trans hN)).le)
    exact h.trans_lt (half_lt_self hε)

/-- **Smooth test functions determine measures finite on compacts** (steps 6–7 of the
translation-invariance argument): if `μ, ν` on `ℝᴾ` are finite on compact sets and
`∫ φ dμ = ∫ φ dν` for every `C^∞` `φ` with compact support, then `μ = ν`.  Both measures are
locally finite, hence regular on the `σ`-compact metric space `ℝᴾ`, so by Riesz uniqueness it
suffices to compare `∫ f` for `f ∈ C_c(ℝᴾ, ℝ)`.  Approximate `f` by `C^∞` functions `uₖ`
vanishing off a compact `K`, with `|uₖ| ≤ C` and `uₖ → f` pointwise
(`cbr_ci_cp_tr_smooth_approx_of_continuous`): then `∫ uₖ dμ = ∫ uₖ dν`, and dominated
convergence with the bound `C·1_K` gives `∫ uₖ dμ → ∫ f dμ` and `∫ uₖ dν → ∫ f dν`. -/
theorem Submission.cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq : ∀ (P : ℕ) (μ ν : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, φ y ∂μ = ∫ y, φ y ∂ν) → μ = ν := by
  intro P μ ν hμ hν hφ
  -- step 1: `μ, ν` are finite on compacts, hence locally finite and regular on `ℝᴾ`
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ K hK⟩
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  -- step 2: by Riesz uniqueness it suffices to compare `∫ f` for `f ∈ C_c(ℝᴾ, ℝ)`
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  -- step 3: `C^∞` approximants `uₖ → f`, vanishing off a compact `K`, with `|uₖ| ≤ C`
  obtain ⟨K, C, u, hK, hu, huK, huC, hlim⟩ :=
    Submission.cbr_ci_cp_tr_smooth_approx_of_continuous P f f.continuous f.hasCompactSupport
  -- step 5: dominated convergence with the bound `C·1_K`, for `m = μ` and `m = ν`
  have hdom : ∀ m : Measure (Euclid P), m K < ∞ →
      Tendsto (fun k => ∫ x, u k x ∂m) atTop (𝓝 (∫ x, f x ∂m)) := fun m hm =>
    tendsto_integral_of_dominated_convergence (K.indicator fun _ => C)
      (fun k => (hu k).continuous.aestronglyMeasurable)
      ((integrableOn_const hm.ne).integrable_indicator hK.measurableSet)
      (fun k => Eventually.of_forall fun x => by
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx, Real.norm_eq_abs]
          exact huC k x
        · rw [indicator_of_notMem hx, huK k x hx, norm_zero])
      (Eventually.of_forall hlim)
  -- step 4: each `uₖ` is a `C^∞` test function, so `∫ uₖ dμ = ∫ uₖ dν`
  have heq : (fun k => ∫ x, u k x ∂μ) = fun k => ∫ x, u k x ∂ν :=
    funext fun k => hφ (u k) (hu k) (HasCompactSupport.intro hK (huK k))
  -- step 6: limits in `ℝ` are unique
  have hlimμ := hdom μ (hμ K hK)
  rw [heq] at hlimμ
  exact tendsto_nhds_unique hlimμ (hdom ν (hν K hK))

/-- **Translation invariance from vanishing directional derivatives** (step 2 of the
constant-planes argument): if `ν` on `ℝᴾ` is finite on compact sets and `∫ Dφ(y)[v] dν(y) = 0`
for every `C^∞` `φ` with compact support, then `ν(τ⁻¹A) = ν(A)` for every Borel `A`, where
`τ(x) = v + x`.  `τ` is a homeomorphism, so `τ_#ν` is finite on compact sets
(`τ_#ν(K) = ν(τ⁻¹K)`, `τ⁻¹K = K − v` compact) and `∫ φ d(τ_#ν) = ∫ φ(v + y) dν(y)`, which is
`∫ φ dν` for `φ ∈ C_c^∞(ℝᴾ)` (`cbr_ci_cp_tr_smooth_translate_integral_eq`).  Hence `τ_#ν = ν`
(`cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq`), and `ν(τ⁻¹A) = τ_#ν(A) = ν(A)`. -/
theorem Submission.cbr_ci_cp_translation_invariant_of_fderiv : ∀ (P : ℕ) (ν : Measure (Euclid P)) (v : Euclid P), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A := by
  intro P ν v hν hD A hA
  -- `τ(x) = v + x` is a homeomorphism of `ℝᴾ`, hence a measurable embedding
  have hτ : MeasurableEmbedding (fun x : Euclid P => v + x) :=
    (Homeomorph.addLeft v).measurableEmbedding
  -- steps 4–7: `τ_#ν = ν`, both being finite on compacts with equal `C_c^∞` integrals
  have hμ : Measure.map (fun x : Euclid P => v + x) ν = ν := by
    refine Submission.cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq P
      (Measure.map (fun x : Euclid P => v + x) ν) ν (fun K hK => ?_) hν (fun φ hφ hφs => ?_)
    · -- `τ_#ν(K) = ν(τ⁻¹K) < ∞`, `τ⁻¹K = K − v` being compact
      rw [hτ.map_apply]
      exact hν _ ((Homeomorph.addLeft v).isCompact_preimage.2 hK)
    · -- steps 1–3: `∫ φ d(τ_#ν) = ∫ φ(v + y) dν(y) = ∫ φ dν` for `φ ∈ C_c^∞(ℝᴾ)`
      rw [hτ.integral_map]
      exact Submission.cbr_ci_cp_tr_smooth_translate_integral_eq P ν v hν hD φ hφ hφs
  -- step 8: `ν(τ⁻¹A) = τ_#ν(A) = ν(A)` for Borel `A`
  rw [← Measure.map_apply hτ.measurable hA, hμ]

/-- **Riesz vector of the wedge functional `w ↦ ζ₀(w♭ ∧ α)`** (used in the constant tangent plane
step of the compactness theorem, Simon 7.2.4).  For `ζ₀ ∈ Λ_{d+1}(ℝᴾ)` and a fixed `d`-covector
`α` there is `v ∈ ℝᴾ` with `ζ₀(γ) = ⟨v, w⟩` whenever `γ = w♭ ∧ α`, i.e.
`γ(u₀, …, u_d) = Σᵢ (−1)ⁱ ⟨w, uᵢ⟩ α(u₀, …, ûᵢ, …, u_d)`: such a `γ` is `d(⟨w, ·⟩ α)(0)`, which
is linear in `w`, and `v` is the Riesz representative of `w ↦ ζ₀(w♭ ∧ α)`. -/
theorem Submission.cbr_ci_cp_dir_wedge_riesz_vector : ∀ (P d : ℕ) (ζ₀ : MultiVector P (d + 1)) (α : Covector (Euclid P) d), ∃ v : Euclid P, ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = inner ℝ v w := by
  intro P d ζ₀ α
  set W : Euclid P → Covector (Euclid P) (d + 1) :=
    fun w => exteriorDerivative (fun y => inner ℝ w y • α) 0 with hW
  have hWf : ∀ (w : Euclid P) (u : Fin (d + 1) → Euclid P), W w u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u)) := by
    intro w u
    have hd : DifferentiableAt ℝ (fun y => inner ℝ w y) (0 : Euclid P) :=
      (innerSL ℝ w).differentiableAt
    rw [hW, Submission.dgcr_bwd_extDeriv_smul_const P d (fun y => inner ℝ w y) α 0 u hd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : fderiv ℝ (fun y => inner ℝ w y) (0 : Euclid P) = innerSL ℝ w :=
      (innerSL ℝ w).fderiv
    rw [hf, innerSL_apply_apply]
  have huniq : ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → γ = W w := by
    intro w γ hγ
    ext u
    rw [hγ u, hWf w u]
  have hadd : ∀ w w' : Euclid P, W (w + w') = W w + W w' := by
    intro w w'
    ext u
    rw [ContinuousAlternatingMap.add_apply, hWf, hWf, hWf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_add_left]
    ring
  have hsmul : ∀ (c : ℝ) (w : Euclid P), W (c • w) = c • W w := by
    intro c w
    ext u
    rw [ContinuousAlternatingMap.smul_apply, hWf, hWf, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left]
    ring
  let ℓ : Euclid P →ₗ[ℝ] ℝ :=
    { toFun := fun w => ζ₀ (W w)
      map_add' := by
        intro w w'
        simp only [hadd, map_add]
      map_smul' := by
        intro c w
        simp only [hsmul, map_smul, smul_eq_mul, RingHom.id_apply] }
  refine ⟨(InnerProductSpace.toDual ℝ (Euclid P)).symm (LinearMap.toContinuousLinearMap ℓ), ?_⟩
  intro w γ hγ
  rw [InnerProductSpace.toDual_symm_apply, huniq w γ hγ]
  rfl
/-- **Vanishing of `∫ Dφ[v] dν` on a set of directions extends to its span** (the linearity step
of the constant-planes argument for the closure and boundary rectifiability in the compactness
theorem).  If `ν` is finite on compact sets and `φ : ℝᴾ → ℝ` is `C^∞` with compact support, then
each `y ↦ Dφ(y)[v]` is continuous with compact support, hence `ν`-integrable, so
`v ↦ ∫ Dφ(y)[v] dν(y)` is linear; if it vanishes on `S`, it vanishes on `span S`. -/
theorem Submission.cbr_ci_cp_dir_integral_fderiv_span : ∀ (P : ℕ) (ν : Measure (Euclid P)) (φ : Euclid P → ℝ) (S : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ v ∈ S, ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ v ∈ Submodule.span ℝ S, ∫ y, fderiv ℝ φ y v ∂ν = 0 := by
  intro P ν φ S hν hφ hφc hS
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  have hint : ∀ v, Integrable (fun y => fderiv ℝ φ y v) ν := by
    intro v
    have hc : Continuous (fun y => fderiv ℝ φ y v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hc.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) v)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    rw [integral_add (hint x) (hint y), hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [map_smul, smul_eq_mul]
    rw [integral_const_mul, hx, mul_zero]
/-- **Testing a cycle condition on `φ α`** (used for the constant-plane step of White's
tangent-plane argument in the closure theorem behind Simon 7.2.4).  If `∫ ζ₀(dψ(y)) dν(y) = 0`
for every test `d`-form `ψ`, and `ζ₀(w♭ ∧ α) = v · w` for every `w`, where
`(w♭ ∧ α)(u₀, …, u_d) = Σᵢ (−1)ⁱ (w · uᵢ) α(u₀, …, ûᵢ, …, u_d)`, then `∫ Dφ(y)v dν(y) = 0`
for every compactly supported `C^∞` function `φ`: `φ α` is a test form with
`d(φ α)(y) = ∇φ(y)♭ ∧ α`, so `ζ₀(d(φ α)(y)) = v · ∇φ(y) = Dφ(y)v`. -/
theorem Submission.cbr_ci_cp_dir_cycle_fderiv_integral_zero : ∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (α : Covector (Euclid P) d) (v : Euclid P) (φ : Euclid P → ℝ), (∀ ψ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (ψ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → (∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = inner ℝ v w) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0 := by
  intro P d ν ζ₀ α v φ hcyc hv hφ hφc
  have hmem : (fun y => φ y • α : DifferentialForm (Euclid P) d) ∈
      TestFormOn (univ : Set (Euclid P)) d :=
    ⟨⟨hφ.smul contDiff_const, hφc.smul_right⟩, subset_univ _⟩
  have h := hcyc ⟨_, hmem⟩
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hd : DifferentiableAt ℝ φ y := (hφ.differentiable (by simp)) y
  set g : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm (fderiv ℝ φ y) with hg
  have hγ : ∀ u : Fin (d + 1) → Euclid P, exteriorDerivative (fun y => φ y • α) y u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ g (u i) * α (i.removeNth u)) := by
    intro u
    rw [Submission.dgcr_bwd_extDeriv_smul_const P d φ α y u hd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hg, InnerProductSpace.toDual_symm_apply]
  have hz := hv g _ hγ
  show fderiv ℝ φ y v = ζ₀ (exteriorDerivative (fun y => φ y • α) y)
  rw [hz, real_inner_comm, hg, InnerProductSpace.toDual_symm_apply]

/-- **Translation directions of a constant-orientation cycle** (the vectors `v_α` of the
tangent-plane step in the closure and boundary rectifiability part of Simon 7.2.4).  Let `ν` be a
Borel measure on `ℝᴾ`, finite on compact sets, and `ζ₀ ∈ Λ_{d+1}(ℝᴾ)` with `∫ ⟨dφ, ζ₀⟩ dν = 0` for
every test `d`-form `φ`.  For a `d`-covector `α` let `v_α` represent `w ↦ ⟨w♭ ∧ α, ζ₀⟩`, where
`(w♭ ∧ α)(u₀, …, u_d) = Σᵢ (−1)ⁱ ⟨w, uᵢ⟩ α(u₀, …, ûᵢ, …, u_d)`.  Then `V = span{v_α}` satisfies
`∫ Dψ[v] dν = 0` for `v ∈ V` and `ψ ∈ C_c^∞(ℝᴾ)` (test the cycle condition on `ψα`, using
`d(ψα) = (∇ψ)♭ ∧ α`), and `⟨w♭ ∧ α, ζ₀⟩ = ⟨v_α, w⟩ = 0` for `w ∈ Vᗮ`. -/
theorem Submission.cbr_ci_cp_wedge_annihilator_subspace : ∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → ∃ V : Submodule ℝ (Euclid P), (∀ v ∈ V, ∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) ∧ ∀ w ∈ Vᗮ, ∀ (α : Covector (Euclid P) d) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = 0 := by
  intro P d ν ζ₀ hν hcyc
  choose v hv using Submission.cbr_ci_cp_dir_wedge_riesz_vector P d ζ₀
  refine ⟨Submodule.span ℝ (range v), fun u hu φ hφ hφc => ?_, fun w hw α γ hγ => ?_⟩
  · refine Submission.cbr_ci_cp_dir_integral_fderiv_span P ν φ (range v) hν hφ hφc ?_ u hu
    rintro _ ⟨α, rfl⟩
    exact Submission.cbr_ci_cp_dir_cycle_fderiv_integral_zero P d ν ζ₀ α (v α) φ hcyc (hv α)
      hφ hφc
  · rw [hv α w γ hγ]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_range_self α)) hw
/-- **An orthonormal basis of `ℝᴾ` adapted to a subspace `V`** (used to show that an `n`-vector
annihilating every `w♭ ∧ α` with `w ⊥ V` only sees `β ∘ p_V`): each basis vector lies in `V` or in
`Vᗮ`.  `V` and `Vᗮ` are orthogonal, and a vector orthogonal to `V + Vᗮ` lies in `Vᗮ ∩ Vᗮᗮ = 0`, so
`ℝᴾ` is the internal orthogonal direct sum of `V` and `Vᗮ`.  Concatenating orthonormal bases of
`V` and `Vᗮ` and re-indexing by `Fin P` (`finrank ℝ ℝᴾ = P`) gives the basis. -/
theorem Submission.cbr_ci_cp_pr_adapted_orthonormalBasis : ∀ (P : ℕ) (V : Submodule ℝ (Euclid P)), ∃ e : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, e i ∈ V ∨ e i ∈ Vᗮ := by
  intro P V
  -- Step 1: `b ↦ cond b V Vᗮ` is an orthogonal family of subspaces
  have hW' : OrthogonalFamily ℝ (fun b : Bool => ↥(cond b V Vᗮ))
      fun b => (cond b V Vᗮ).subtypeₗᵢ :=
    V.orthogonalFamily_self
  -- Step 2: it is internal, since `(V ⊔ Vᗮ)ᗮ ≤ Vᗮ ⊓ Vᗮᗮ = ⊥`
  have hW : DirectSum.IsInternal fun b : Bool => cond b V Vᗮ := by
    rw [hW'.isInternal_iff, Submodule.eq_bot_iff]
    intro x hx
    have h1 : x ∈ Vᗮ :=
      Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) true) hx
    have h2 : x ∈ Vᗮᗮ :=
      Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) false) hx
    exact Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint Vᗮ) x h1 h2
  -- Step 3: the orthonormal basis subordinate to this decomposition, indexed by `Fin P`; its
  -- `i`-th vector lies in the summand `cond b V Vᗮ` for some `b : Bool`
  refine ⟨hW.subordinateOrthonormalBasis finrank_euclideanSpace_fin hW', fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace_fin i hW'
  revert hmem
  generalize hW.subordinateOrthonormalBasisIndex finrank_euclideanSpace_fin i hW' = b
  cases b
  · intro hmem
    exact Or.inr hmem
  · intro hmem
    exact Or.inl hmem
/-- The determinant `n`-covector of `g₀, …, g_{n-1} ∈ ℝᴾ`: `u ↦ det(⟨g_b, u_a⟩)_{a,b}`, with
`⟨g_b, u_a⟩` in row `a` and column `b` (for an orthonormal basis `e'`, the dual covectors `e'^I`
of the projection reduction in White's proof that limits are integer multiplicity, Simon 6.3.11).
Row `a` is `L u_a` for the linear map `L x = (⟨g_b, x⟩)_b`, so this is the row determinant
`detRowAlternating` composed with `L`, an alternating `n`-linear map.  It is continuous, the
determinant being a polynomial in the continuous entries `⟨g_b, u_a⟩`.  For `n = 0` it is the
constant `1`. -/
theorem Submission.cbr_ci_cp_pr_inner_det_covector : ∀ (P n : ℕ) (g : Fin n → Euclid P), ∃ γ : Covector (Euclid P) n, ∀ u : Fin n → Euclid P, γ u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
  intro P n g
  -- the alternating map `u ↦ D(L u₀, …, L u_{n-1})`, `D` the row determinant
  let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ :=
    Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun b => innerₛₗ ℝ (g b))
  have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := fun _ => rfl
  -- continuity: a polynomial in the continuous entries `⟨g_b, u_a⟩`
  have hc : Continuous fun u : Fin n → Euclid P =>
      Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
    fun_prop
  exact ⟨⟨⟨f.toMultilinearMap, hc.congr fun u => (hf u).symm⟩, f.map_eq_zero_of_eq'⟩, hf⟩

/-- Laplace expansion of a determinant covector along column `k`.  If the `(d + 1)`-covector `γ`
is `u ↦ det (⟨g b, u a⟩)_{a b}`, then `γ u = ∑ᵢ (-1)ⁱ ⟨g k, u i⟩ α (u₀, …, ûᵢ, …, u_d)` with
`α = (-1)ᵏ γ'`, where `γ'` is the `d`-covector `v ↦ det (⟨g (k.succAbove b), v a⟩)_{a b}` of the
tuple `g` with `g k` deleted (`cbr_ci_cp_pr_inner_det_covector`): the `(i, k)` minor of
`(⟨g b, u a⟩)_{a b}` is that matrix for `v = i.removeNth u`. -/
theorem Submission.cbr_ci_cp_pr_det_covector_laplace : ∀ (P d : ℕ) (g : Fin (d + 1) → Euclid P) (k : Fin (d + 1)) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a))) → ∃ α : Covector (Euclid P) d, ∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ (g k) (u i) * α (i.removeNth u)) := by
  intro P d g k γ hγ
  -- Step 1: the minor covector `γ'` of `g` with its `k`-th entry deleted, and `α = (-1)ᵏ γ'`.
  obtain ⟨γ', hγ'⟩ := Submission.cbr_ci_cp_pr_inner_det_covector P d (fun b => g (k.succAbove b))
  refine ⟨((-1 : ℝ) ^ (k : ℕ)) • γ', fun u => ?_⟩
  -- Step 2: Laplace expansion of `det (⟨g b, u a⟩)_{a b}` along column `k`.
  rw [hγ u, Matrix.det_succ_column _ k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousAlternatingMap.smul_apply, hγ' (i.removeNth u), smul_eq_mul]
  -- Step 3: the `(i, k)` minor is the matrix of `i.removeNth u` against `g ∘ k.succAbove`.
  have hsub : (Matrix.of fun a b => inner ℝ (g b) (u a)).submatrix i.succAbove k.succAbove =
      Matrix.of fun a b => inner ℝ (g (k.succAbove b)) (i.removeNth u a) := by
    ext a b
    simp [Fin.removeNth]
  -- Step 4: `(-1) ^ (i + k) = (-1) ^ i * (-1) ^ k`.
  rw [hsub, Matrix.of_apply, pow_add]
  ring
/-- `n! · β(u) = ∑_I β(e_I) · det(⟨e_{I(b)}, u_a⟩)_{a,b}` for an `n`-covector `β` on `ℝᴾ`, an
orthonormal basis `e` of `ℝᴾ` and `u ∈ (ℝᴾ)ⁿ`, the sum running over all index maps
`I : Fin n → Fin P` (the expansion of `β` in the basis dual to `e`, used for the projection
reduction of constant plane currents in the integer multiplicity part of Simon 7.2.4, Remark
7.2.5(1)).  Expanding every argument in the basis `e` gives
`β(v) = ∑_I (∏_a ⟨e_{I(a)}, v_a⟩) β(e_I)`; as `β` is alternating,
`n! · β(u) = ∑_σ sign(σ) β(u ∘ σ)`; the Leibniz formula collects the sums over `σ` into the
determinants. -/
theorem Submission.cbr_ci_cp_pr_factorial_mul_eq_sum_det : ∀ (P n : ℕ) (e : OrthonormalBasis (Fin P) ℝ (Euclid P)) (β : Covector (Euclid P) n) (u : Fin n → Euclid P), (n.factorial : ℝ) * β u = ∑ I : Fin n → Fin P, β (fun a => e (I a)) * Matrix.det (Matrix.of fun a b => inner ℝ (e (I b)) (u a)) := by
  intro P n e β u
  classical
  -- multilinear expansion of `β` in the orthonormal basis `e`
  have hexp : ∀ v : Fin n → Euclid P, β v =
      ∑ I : Fin n → Fin P, (∏ a, inner ℝ (e (I a)) (v a)) * β (fun a => e (I a)) := by
    intro v
    have hv : v = fun a => ∑ m, inner ℝ (e m) (v a) • e m := by
      funext a
      exact (e.sum_repr' (v a)).symm
    conv_lhs => rw [hv]
    rw [β.map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [β.map_smul_univ (fun a => inner ℝ (e (I a)) (v a)) (fun a => e (I a)), smul_eq_mul]
  -- alternation: `sign(σ) β(u ∘ σ) = sign(σ)² β(u) = β(u)`, and there are `n!` permutations
  have halt : (n.factorial : ℝ) * β u =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) := by
    have : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) = β u := by
      intro σ
      rw [show β (u ∘ σ) = Equiv.Perm.sign σ • β u from β.toAlternatingMap.map_perm u σ]
      rw [Units.smul_def, zsmul_eq_mul, ← mul_assoc]
      have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      rw [hs, one_mul]
    rw [Finset.sum_congr rfl fun σ _ => this σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [halt]
  -- expand only `β (u ∘ σ)` (the right side of `hexp` contains `β` again), then swap the sums
  have h2 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) =
      ∑ I : Fin n → Fin P, (Equiv.Perm.sign σ : ℝ) *
        ((∏ a, inner ℝ (e (I a)) ((u ∘ σ) a)) * β (fun a => e (I a))) := by
    intro σ
    rw [hexp (u ∘ σ), Finset.mul_sum]
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  -- for fixed `I`, the sum over `σ` is the Leibniz formula for the determinant
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, Function.comp_apply]
  ring

/-- Projection reduction for the constant-planes step of the cycle case of closure and boundary
rectifiability: if an `n`-vector `ζ` (`n = d + 1`) vanishes on every `n`-covector `w♭ ∧ α` with
`w ∈ Vᗮ` and `α` a `d`-covector, then `ζ(β) = ζ(β ∘ p_V)` for every `n`-covector `β`, where `p_V`
is the orthogonal projection onto `V`.  Take an orthonormal basis `e` of `ℝᴾ` with each `eᵢ` in
`V` or in `Vᗮ` (subordinate to `ℝᴾ = V ⊕ Vᗮ`) and the covectors `e^I(u) = det(⟨e_{I b}, u_a⟩)`,
`I : Fin n → Fin P` (`cbr_ci_cp_pr_inner_det_covector`), so that `n! β = ∑_I β(e_I) e^I`
(`cbr_ci_cp_pr_factorial_mul_eq_sum_det`).  If `e_{I k} ∈ Vᗮ` for some `k`, Laplace expansion along
column `k` writes `e^I = e_{I k}♭ ∧ α` (`cbr_ci_cp_pr_det_covector_laplace`), so `ζ(e^I) = 0`;
otherwise `p_V e_{I b} = e_{I b}` for every `b`, and `β ∘ p_V` has the same coefficient `β(e_I)`. -/
theorem Submission.cbr_ci_cp_eval_comp_starProjection_eq : ∀ (P d : ℕ) (ζ : MultiVector P (d + 1)) (V : Submodule ℝ (Euclid P)), (∀ w ∈ Vᗮ, ∀ (α : Covector (Euclid P) d) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ γ = 0) → ∀ β : Covector (Euclid P) (d + 1), ζ β = ζ (β.compContinuousLinearMap V.starProjection) := by
  have hdet := Submission.cbr_ci_cp_pr_inner_det_covector
  have hlap := Submission.cbr_ci_cp_pr_det_covector_laplace
  have hexp := Submission.cbr_ci_cp_pr_factorial_mul_eq_sum_det
  intro P d ζ V hζ β
  -- Step 1: an orthonormal basis of `ℝᴾ` subordinate to `ℝᴾ = V ⊕ Vᗮ`
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i, e i ∈ V ∨ e i ∈ Vᗮ := by
    have hV' := V.orthogonalFamily_self
    have hint : DirectSum.IsInternal (fun b : Bool => cond b V Vᗮ) := by
      refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV'.independent ?_
      rw [iSup_bool_eq]
      exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
    refine ⟨hint.subordinateOrthonormalBasis finrank_euclideanSpace_fin hV', fun i => ?_⟩
    have hi := hint.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace_fin i hV'
    revert hi
    cases hint.subordinateOrthonormalBasisIndex finrank_euclideanSpace_fin i hV'
    · exact Or.inr
    · exact Or.inl
  -- Step 2: the determinant covectors `e^I(u) = det(⟨e_{I b}, u_a⟩)`
  choose γ hγ using fun I : Fin (d + 1) → Fin P => hdet P (d + 1) fun b => e (I b)
  -- Step 3: `(d+1)! ζ(β') = ∑_I β'(e_I) ζ(e^I)` for every `(d+1)`-covector `β'`
  have hsum : ∀ β' : Covector (Euclid P) (d + 1), ((d + 1).factorial : ℝ) * ζ β' =
      ∑ I : Fin (d + 1) → Fin P, β' (fun a => e (I a)) * ζ (γ I) := by
    intro β'
    have hcov : ((d + 1).factorial : ℝ) • β' =
        ∑ I : Fin (d + 1) → Fin P, β' (fun a => e (I a)) • γ I := by
      ext u
      rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply, smul_eq_mul,
        hexp P (d + 1) e β' u]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hγ]
    have := congrArg ζ hcov
    rw [map_smul, map_sum, smul_eq_mul] at this
    rw [this]
    simp only [map_smul, smul_eq_mul]
  -- Step 4: `ζ(e^I) = 0` if some `e_{I k} ∈ Vᗮ` (Laplace expansion along column `k`)
  have hkill : ∀ (I : Fin (d + 1) → Fin P) (k : Fin (d + 1)), e (I k) ∈ Vᗮ → ζ (γ I) = 0 := by
    intro I k hk
    obtain ⟨α, hα⟩ := hlap P d (fun b => e (I b)) k (γ I) (hγ I)
    exact hζ (e (I k)) hk α (γ I) hα
  -- Step 5: `β ∘ p_V` and `β` agree on `e_I` if every `e_{I b} ∈ V`
  have hcoef : ∀ I : Fin (d + 1) → Fin P, (∀ b, e (I b) ∈ V) →
      β.compContinuousLinearMap V.starProjection (fun a => e (I a)) = β (fun a => e (I a)) := by
    intro I hI
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext a
    exact Submodule.starProjection_eq_self_iff.mpr (hI a)
  -- Step 6: compare the two expansions term by term
  have hfact : ((d + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ hfact
  rw [hsum β, hsum (β.compContinuousLinearMap V.starProjection)]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : ∀ b, e (I b) ∈ V
  · rw [hcoef I hI]
  · obtain ⟨k, hk⟩ := not_forall.mp hI
    rw [hkill I k ((he (I k)).resolve_left hk), mul_zero, mul_zero]
/-- `(2M+1)^r` lattice points of a subspace `V ⊆ ℝᴾ` of dimension `r`, pairwise at distance
`≥ 2` and of norm `≤ 2M√r` (the packing step of the growth bound for the dimension of `V`).
For an orthonormal basis `e` of `V`, `c ↦ Σⱼ cⱼ eⱼ` is a linear isometry `ℓ²(ℝʳ) ≃ V`; take
`u_k = 2 Σⱼ kⱼ eⱼ` for `k` in the box `([−M, M] ∩ ℤ)ʳ`.  Distinct integer vectors differ by
`≥ 1` in some coordinate, so `‖u_k − u_l‖ ≥ 2`, and `‖u_k‖² = Σⱼ (2kⱼ)² ≤ r(2M)²`. -/
theorem Submission.cbr_ci_cp_gd_subspace_lattice_packing : ∀ (P : ℕ) (V : Submodule ℝ (Euclid P)) (M : ℕ), ∃ S : Finset (Euclid P), S.card = (2 * M + 1) ^ Module.finrank ℝ V ∧ (∀ x ∈ S, x ∈ V) ∧ (∀ x ∈ S, ‖x‖ ≤ 2 * M * Real.sqrt (Module.finrank ℝ V)) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y) := by
  intro P V M
  classical
  -- orthonormal coordinates `e.repr.symm : ℓ²(ℝʳ) ≃ₗᵢ V` and the points `u_k = e.repr.symm (2k)`
  let e := stdOrthonormalBasis ℝ V
  let c : (Fin (Module.finrank ℝ V) → ℤ) → EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    fun k => WithLp.toLp 2 fun j => 2 * (k j : ℝ)
  let u : (Fin (Module.finrank ℝ V) → ℤ) → Euclid P := fun k => (e.repr.symm (c k) : Euclid P)
  have hnorm : ∀ k, ‖u k‖ = ‖c k‖ := fun k => by
    simp only [u, Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  have hdist : ∀ k l, dist (u k) (u l) = dist (c k) (c l) := fun k l => by
    simp only [dist_eq_norm, u, ← Submodule.coe_sub, ← map_sub, Submodule.norm_coe,
      LinearIsometryEquiv.norm_map]
  -- distinct integer vectors give points at distance `≥ 2`
  have hsep : ∀ k l, k ≠ l → 2 ≤ dist (u k) (u l) := by
    intro k l hkl
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
    have h1 : (1 : ℝ) ≤ |(k j : ℝ) - l j| := by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hj)
    calc (2 : ℝ) ≤ dist (c k j) (c l j) := by
          simp only [c, Real.dist_eq, ← mul_sub, abs_mul, abs_two]
          linarith
      _ ≤ dist (c k) (c l) := PiLp.dist_apply_le _ _ _
      _ = dist (u k) (u l) := (hdist k l).symm
  have hinj : Function.Injective u := fun k l hkl => by
    by_contra h
    have := hsep k l h
    rw [hkl, dist_self] at this
    norm_num at this
  -- the box `Λ_M = ([−M, M] ∩ ℤ)ʳ`
  refine ⟨(Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M).image u, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Fintype.card_piFinset, Int.card_Icc,
      Fin.prod_const]
    congr 1
    omega
  · simp only [Finset.mem_image]
    rintro x ⟨k, -, rfl⟩
    exact (e.repr.symm (c k)).2
  · simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
    rintro x ⟨k, hk, rfl⟩
    rw [hnorm]
    have hM : (0 : ℝ) ≤ 2 * M * Real.sqrt (Module.finrank ℝ V) := by positivity
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hM two_ne_zero).mp ?_
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    calc ∑ j, ‖c k j‖ ^ 2 ≤ ∑ _j : Fin (Module.finrank ℝ V), (2 * (M : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have hkj : -(M : ℝ) ≤ k j ∧ (k j : ℝ) ≤ M :=
            ⟨by exact_mod_cast (hk j).1, by exact_mod_cast (hk j).2⟩
          simp only [c]
          nlinarith [hkj.1, hkj.2]
      _ = (2 * M) ^ 2 * Module.finrank ℝ V := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  · simp only [Finset.mem_image]
    rintro x ⟨k, -, rfl⟩ y ⟨l, -, rfl⟩ hxy
    exact hsep k l fun h => hxy (h ▸ rfl)
/-- Packing count for unit balls translated along a subspace `V` (used in the proof of Simon 7.2.4,
p. 184, to show that a measure with `ν(B_R(0)) ≤ C Rⁿ` that is invariant under the translations of
`V` has `dim V ≤ n`): if `ν` is invariant under translation by every `v ∈ V`, and `S ⊆ V` is finite
with `‖x‖ ≤ ρ` for `x ∈ S` and `dist x y ≥ 2` for distinct `x, y ∈ S`, then
`#S · ν(B_1(0)) ≤ ν(B_{ρ+1}(0))`.  Each `B_1(x) = {y : -x + y ∈ B_1(0)}` has measure `ν(B_1(0))`
(as `-x ∈ V`), and these balls are pairwise disjoint (triangle inequality) and lie in
`B_{ρ+1}(0)`. -/
theorem Submission.cbr_ci_cp_gd_translated_ball_count : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (S : Finset (Euclid P)) (ρ : ℝ), (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → (∀ x ∈ S, x ∈ V) → (∀ x ∈ S, ‖x‖ ≤ ρ) → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y) → (S.card : ℝ≥0∞) * ν (ball 0 1) ≤ ν (ball 0 (ρ + 1)) := by
  intro P ν V S ρ hinv hSV hSρ hsep
  -- equal mass: `B_1(x)` is the preimage of `B_1(0)` under `y ↦ -x + y`, and `-x ∈ V`
  have hmass : ∀ x ∈ S, ν (ball x 1) = ν (ball 0 1) := by
    intro x hx
    have hpre : (fun y => -x + y) ⁻¹' ball (0 : Euclid P) 1 = ball x 1 := by
      ext y
      simp only [mem_preimage, mem_ball_iff_norm, sub_zero, neg_add_eq_sub]
    rw [← hpre]
    exact hinv (-x) (V.neg_mem (hSV x hx)) _ measurableSet_ball
  -- disjointness: a common point `z` would give `2 ≤ dist x y ≤ dist z x + dist z y < 2`
  have hdisj : (S : Set (Euclid P)).PairwiseDisjoint fun x => ball x 1 := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr fun z hzx hzy => ?_
    rw [mem_ball] at hzx hzy
    linarith [hsep x hx y hy hxy, dist_triangle_left x y z]
  -- containment: `‖z‖ ≤ ‖x‖ + ‖z - x‖ < ρ + 1`
  have hsub : (⋃ x ∈ S, ball x 1) ⊆ ball (0 : Euclid P) (ρ + 1) := by
    refine iUnion₂_subset fun x hx z hz => ?_
    rw [mem_ball_iff_norm] at hz
    rw [mem_ball_zero_iff]
    linarith [hSρ x hx, norm_le_norm_add_norm_sub' z x]
  -- counting: `#S · ν(B_1(0)) = Σ_{x ∈ S} ν(B_1(x)) = ν(⋃_{x ∈ S} B_1(x)) ≤ ν(B_{ρ+1}(0))`
  calc (S.card : ℝ≥0∞) * ν (ball 0 1) = ∑ x ∈ S, ν (ball x 1) := by
        rw [Finset.sum_congr rfl hmass, Finset.sum_const, nsmul_eq_mul]
    _ = ν (⋃ x ∈ S, ball x 1) :=
        (measure_biUnion_finset hdisj fun x _ => measurableSet_ball).symm
    _ ≤ ν (ball 0 (ρ + 1)) := measure_mono hsub
/-- Final step of the growth-forces-dimension argument in the proof of Simon 7.2.4 (packing
`(2M+1)ʳ` disjoint unit balls of an `r`-plane into `B_{3M√r}(0)`): if `a > 0` and
`a·Mʳ ≤ b·Mⁿ` for every integer `M ≥ 1`, then `r ≤ n`.  Otherwise `n + 1 ≤ r`; the Archimedean
property gives `N > b/a`, and `M = N + 1` has `a·M > b`, while
`a·M·Mⁿ = a·Mⁿ⁺¹ ≤ a·Mʳ ≤ b·Mⁿ` gives `a·M ≤ b` after cancelling `Mⁿ > 0`. -/
theorem Submission.cbr_ci_cp_gd_le_of_pow_bound : ∀ (r n : ℕ) (a b : ℝ), 0 < a → (∀ M : ℕ, 1 ≤ M → a * (M : ℝ) ^ r ≤ b * (M : ℝ) ^ n) → r ≤ n := by
  intro r n a b ha h
  -- suppose `n + 1 ≤ r`
  by_contra hrn
  have hr : n + 1 ≤ r := Nat.lt_iff_add_one_le.mp (not_le.mp hrn)
  -- Archimedean choice `N > b / a`; `M := N + 1 ≥ 1` has `a * M > b`
  obtain ⟨N, hN⟩ := exists_nat_gt (b / a)
  have hM : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hbM : b < ((N + 1 : ℕ) : ℝ) * a := by
    rw [← div_lt_iff₀ ha]
    push_cast
    linarith
  -- `a * M * Mⁿ = a * Mⁿ⁺¹ ≤ a * Mʳ ≤ b * Mⁿ`, then cancel `Mⁿ > 0`
  have hle : a * ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ n ≤ b * ((N + 1 : ℕ) : ℝ) ^ n :=
    calc a * ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ n = a * ((N + 1 : ℕ) : ℝ) ^ (n + 1) := by
          ring
      _ ≤ a * ((N + 1 : ℕ) : ℝ) ^ r := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM hr) ha.le
      _ ≤ b * ((N + 1 : ℕ) : ℝ) ^ n := h (N + 1) (Nat.le_add_left 1 N)
  have hMa := le_of_mul_le_mul_right hle (pow_pos (zero_lt_one.trans_le hM) n)
  linarith

/-- **Growth forces `dim V ≤ n`** (step 4 of the constant-planes argument, with `ωₙ` replaced by an
arbitrary finite constant `C`).  Let `r = dim V` and `m₀ = ν(B₁(0))`, so `0 < m₀ ≤ C < ∞` (growth at
`R = 1`).  Fix `M ≥ 1`.  The sibling `lattice_packing` gives `(2M+1)ʳ` points of `V` of norm
`≤ 2M√r` with pairwise distances `≥ 2`; by the sibling `ball_count` (translation invariance and
disjointness of their unit balls) and the growth bound at `R = 2M√r + 1`,
`(2M+1)ʳ m₀ ≤ ν(B_{2M√r+1}(0)) ≤ C (2M√r+1)ⁿ`.  As `M ≤ 2M+1` and `2M√r + 1 ≤ (2√r+1)M`, this gives
`m₀ Mʳ ≤ C (2√r+1)ⁿ Mⁿ` for every `M ≥ 1`, and the sibling `pow_bound` yields `r ≤ n`. -/
theorem Submission.cbr_ci_cp_finrank_le_of_growth : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (C : ℝ≥0∞), C ≠ ∞ → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ C * ENNReal.ofReal (R ^ n)) → 0 < ν (ball 0 1) → Module.finrank ℝ V ≤ n := by
  intro P n ν V C hC hinv hgrowth hpos
  -- Step 1: `m₀ = ν(B₁(0))` is finite, by the growth bound at `R = 1`
  have hfin : ν (ball 0 1) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hgrowth 1 one_pos)
  -- Step 2: by the sibling `pow_bound` it suffices that `m₀ Mʳ ≤ C (2√r+1)ⁿ Mⁿ` for all `M ≥ 1`
  refine Submission.cbr_ci_cp_gd_le_of_pow_bound (Module.finrank ℝ V) n (ν (ball 0 1)).toReal
    (C.toReal * (2 * Real.sqrt (Module.finrank ℝ V) + 1) ^ n)
    (ENNReal.toReal_pos hpos.ne' hfin) fun M hM => ?_
  -- Step 3: `(2M+1)ʳ` points of `V` of norm `≤ 2M√r`, pairwise `2`-separated (`lattice_packing`)
  obtain ⟨S, hcard, hSV, hSnorm, hSsep⟩ := Submission.cbr_ci_cp_gd_subspace_lattice_packing P V M
  -- Step 4: `(2M+1)ʳ m₀ ≤ ν(B_{2M√r+1}(0)) ≤ C (2M√r+1)ⁿ` (`ball_count`, then growth)
  have hρ : 0 ≤ 2 * (M : ℝ) * Real.sqrt (Module.finrank ℝ V) := by positivity
  have hle := (Submission.cbr_ci_cp_gd_translated_ball_count P ν V S _ hinv hSV hSnorm hSsep).trans
    (hgrowth (2 * M * Real.sqrt (Module.finrank ℝ V) + 1) (by linarith))
  have hpow : 0 ≤ (2 * (M : ℝ) * Real.sqrt (Module.finrank ℝ V) + 1) ^ n := by positivity
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpow, hcard,
    ENNReal.toReal_natCast] at hreal
  push_cast at hreal
  -- Step 5: `Mʳ ≤ (2M+1)ʳ` and `2M√r + 1 ≤ (2√r+1)M`, since `M ≥ 1`
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : (M : ℝ) ^ Module.finrank ℝ V ≤ (2 * M + 1) ^ Module.finrank ℝ V :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : (2 * M * Real.sqrt (Module.finrank ℝ V) + 1) ^ n ≤
      (2 * Real.sqrt (Module.finrank ℝ V) + 1) ^ n * (M : ℝ) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [Real.sqrt_nonneg (Module.finrank ℝ V : ℝ)]) _
  calc (ν (ball 0 1)).toReal * (M : ℝ) ^ Module.finrank ℝ V
      ≤ (2 * M + 1) ^ Module.finrank ℝ V * (ν (ball 0 1)).toReal := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right h1 ENNReal.toReal_nonneg
    _ ≤ C.toReal * (2 * M * Real.sqrt (Module.finrank ℝ V) + 1) ^ n := hreal
    _ ≤ C.toReal * ((2 * Real.sqrt (Module.finrank ℝ V) + 1) ^ n * (M : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left h2 ENNReal.toReal_nonneg
    _ = C.toReal * (2 * Real.sqrt (Module.finrank ℝ V) + 1) ^ n * (M : ℝ) ^ n := by ring

/-- **Covectors vanish through a rank-deficient projection** (Simon Ch. 6, §1): if
`dim V < n`, then `β ∘ p_V = 0` for every `n`-covector `β` on `ℝᴾ`, `p_V` the orthogonal
projection onto `V`.  For any `u₁, …, uₙ` the `n` vectors `p_V u₁, …, p_V uₙ` lie in `V`, so they
are linearly dependent, and the alternating form `β` vanishes on a linearly dependent family. -/
theorem Submission.cbr_ci_cp_comp_starProjection_eq_zero_of_finrank_lt : ∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V < n → ∀ β : Covector (Euclid P) n, β.compContinuousLinearMap V.starProjection = 0 := by
  intro P n V hlt β
  -- Step 1: it suffices that `β(p_V u₁, …, p_V uₙ) = 0` for every family `u`
  ext u
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.coe_zero,
    Pi.zero_apply]
  -- Step 2: an alternating form vanishes on a family that is not linearly independent
  apply β.toAlternatingMap.map_linearDependent
  -- Step 3: `p_V ∘ u = V.subtype ∘ v` with `vᵢ := p_V uᵢ ∈ V`; were it independent, so would be
  -- the `n` vectors `vᵢ` of `V`, giving `n ≤ dim V < n`
  intro hli
  have hli' : LinearIndependent ℝ (fun i => V.orthogonalProjectionOnto (u i)) := by
    apply LinearIndependent.of_comp V.subtype
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega
/-- **An orthonormal frame spanning a subspace** (Simon 6.1.1; the frame `τ` of
`IsUnitOrientationOf`): an `n`-dimensional subspace `V` of `ℝᴾ` is `span{v₀, …, vₙ₋₁}` for an
orthonormal `v : Fin n → ℝᴾ`.  Reindex the orthonormal basis `stdOrthonormalBasis ℝ V` along
`finrank ℝ V = n` to `b : Fin n → V` and put `vᵢ = ↑bᵢ`; the inclusion `V → ℝᴾ` is a linear
isometry, so `v` is orthonormal, and `span (range v)` is the image of `span (range b) = ⊤` under
the inclusion, i.e. `V`. -/
theorem Submission.cbr_ci_cp_exists_orthonormal_frame_of_finrank_eq : ∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → ∃ v : Fin n → Euclid P, Orthonormal ℝ v ∧ Submodule.span ℝ (Set.range v) = V := by
  intro P n V hV
  -- Step 1: an orthonormal basis `b` of `V` indexed by `Fin n`
  let b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  refine ⟨fun i => (b i : Euclid P), ?_, ?_⟩
  · -- Step 2: `vᵢ = ↑bᵢ` is orthonormal, the inclusion `V.subtypeₗᵢ` being a linear isometry
    exact b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  · -- Step 3: `span (range v) = map V.subtype (span (range b)) = map V.subtype ⊤ = V`
    have hrange : Set.range (fun i => (b i : Euclid P)) = (V.subtype) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
/-- **Reversing an orthonormal frame by negating its first vector** (Simon 6.1; the sign in
`ζ = ±v₀ ∧ ⋯ ∧ v_d`): for orthonormal `v₀, …, v_d` in `ℝᴾ`, `w = (-v₀, v₁, …, v_d)` is
orthonormal with the same span, and `β(w) = -β(v)` for every `(d+1)`-covector `β`.  With the
signs `c = (-1, 1, …, 1)`, `wᵢ = cᵢ vᵢ` and `cᵢ² = 1`, so `⟨wᵢ, wⱼ⟩ = cᵢcⱼ⟨vᵢ, vⱼ⟩ = δᵢⱼ` and
`vᵢ = cᵢ wᵢ`; `β` is linear in its first slot. -/
theorem Submission.cbr_ci_cp_exists_orthonormal_frame_eval_neg : ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∃ w : Fin (d + 1) → Euclid P, Orthonormal ℝ w ∧ Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) ∧ ∀ β : Covector (Euclid P) (d + 1), β w = -β v := by
  intro P d v hv
  -- Step 1: the signs `c = (-1, 1, …, 1)`, with `cᵢ cᵢ = 1` and `w = (cᵢ • vᵢ)ᵢ`
  let c : Fin (d + 1) → ℝ := Function.update (fun _ => (1 : ℝ)) 0 (-1)
  have hc : ∀ i, c i * c i = 1 := by
    intro i
    by_cases h : i = 0
    · subst h; simp [c]
    · simp [c, h]
  have hw : (fun i => c i • v i) = Function.update v 0 (-v 0) := by
    funext i
    by_cases h : i = 0
    · subst h; simp [c]
    · simp [c, h]
  refine ⟨Function.update v 0 (-v 0), ?_, ?_, ?_⟩
  · -- Step 2: `⟨wᵢ, wⱼ⟩ = cᵢ cⱼ ⟨vᵢ, vⱼ⟩ = δᵢⱼ`
    rw [← hw]
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right, hv i j]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, mul_one]
      exact hc i
    · simp only [hij, ↓reduceIte, mul_zero]
  · -- Step 3: `wᵢ = cᵢ • vᵢ` and `vᵢ = cᵢ • wᵢ`, so the two spans contain each other
    rw [← hw]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h : v i = c i • (c i • v i) := by
        rw [smul_smul, hc i, one_smul]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · -- Step 4: `β` is linear in slot `0`: `β(update v 0 ((-1) • v₀)) = (-1) • β(v)`
    intro β
    have h := β.map_update_smul v 0 (-1 : ℝ) (v 0)
    rw [neg_one_smul, Function.update_eq_self] at h
    rw [h, neg_one_smul]
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- **Normalisation of a constant unit `n`-vector** (step 5 of the constant-planes lemma in the
proof of the closure theorem, Simon Ch. 6, 3.11, used for 7.2.4; Simon (6.1.1), (6.1.15)): let
`ζ₀ ∈ Λₙ(ℝᴾ)`, `n = d + 1`, satisfy `|ζ₀(β)| ≤ |β|_E` for every `n`-covector `β`, `ζ₀(β₁) = 1` for
some `β₁` with `|β₁|_E ≤ 1`, and `ζ₀(β) = ζ₀(β ∘ p_V)` for a subspace `V` with `dim V ≤ n`.  Then
`dim V = n` and `ζ₀(β) = β(v₀, …, v_d)` for an orthonormal frame `v` of `V`.  If `dim V < n` then
`β₁ ∘ p_V = 0`, so `ζ₀(β₁) = 0`.  Otherwise let `v` be an orthonormal frame of `V` and `β₂` a
covector with `|β₂|_E = 1`, `β₂(v) = 1`.  As every `p_V u_j` lies in `V = span v`,
`β(p_V u) = det(⟨v_i, p_V u_j⟩) β(v) = β(v) β₂(p_V u)`, so `ζ₀(β) = β(v) s` with `s = ζ₀(β₂)`.
Then `|s| ≤ |β₂|_E = 1` and `1 = |β₁(v)| |s| ≤ |s|`, as `|β₁(v)| ≤ |β₁|_E ≤ 1`; so `s = ±1`, and for
`s = −1` the frame with `v₀` negated works. -/
theorem Submission.cbr_ci_cp_eval_eq_orthonormal_frame : ∀ (P d : ℕ) (ζ₀ : MultiVector P (d + 1)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V ≤ d + 1 → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = 1) → (∀ β : Covector (Euclid P) (d + 1), ζ₀ β = ζ₀ (β.compContinuousLinearMap V.starProjection)) → Module.finrank ℝ V = d + 1 ∧ ∃ v : Fin (d + 1) → Euclid P, Orthonormal ℝ v ∧ Submodule.span ℝ (Set.range v) = V ∧ ∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v := by
  intro P d ζ₀ V hdim hle hβ₁ hproj
  obtain ⟨β₁, hβ₁, hζβ₁⟩ := hβ₁
  -- Step 1: `dim V = d + 1`; otherwise `β₁ ∘ p_V = 0` and `1 = ζ₀(β₁) = ζ₀(β₁ ∘ p_V) = ζ₀(0) = 0`
  have hrank : Module.finrank ℝ V = d + 1 := by
    refine le_antisymm hdim (not_lt.mp fun hlt => ?_)
    have h0 : ζ₀ β₁ = 0 := by
      rw [hproj β₁,
        Submission.cbr_ci_cp_comp_starProjection_eq_zero_of_finrank_lt P (d + 1) V hlt β₁,
        map_zero]
    rw [hζβ₁] at h0
    exact one_ne_zero h0
  -- Step 2: an orthonormal frame `v` of `V`
  obtain ⟨v, hv, hspan⟩ :=
    Submission.cbr_ci_cp_exists_orthonormal_frame_of_finrank_eq P (d + 1) V hrank
  -- Step 4: a covector `β₂` with `|β₂|_E = 1` and `β₂(v) = 1`
  obtain ⟨β₂, hβ₂, hβ₂v⟩ :=
    Submission.regcomp_exists_covector_eval_orthonormal_eq_one P (d + 1) v hv
  -- Step 3: `p_V u_j ∈ V = span v`, so `β(p_V u) = det(⟨v_i, p_V u_j⟩) β(v) = β(v) β₂(p_V u)`
  have hcomp : ∀ β : Covector (Euclid P) (d + 1),
      β.compContinuousLinearMap V.starProjection =
        β v • β₂.compContinuousLinearMap V.starProjection := by
    intro β
    ext u
    have hmem : ∀ j, (V.starProjection ∘ u) j ∈ Submodule.span ℝ (Set.range v) := fun j => by
      rw [hspan]
      exact V.starProjection_apply_mem (u j)
    rw [ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      Submission.dgoj_covector_eq_det_mul_of_mem_span P (d + 1) v _ hv hmem β,
      Submission.dgoj_covector_eq_det_mul_of_mem_span P (d + 1) v _ hv hmem β₂, hβ₂v,
      smul_eq_mul]
    ring
  -- Step 4: `ζ₀(β) = ζ₀(β ∘ p_V) = β(v) ζ₀(β₂ ∘ p_V) = β(v) s` with `s = ζ₀(β₂)`
  have hζ : ∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v * ζ₀ β₂ := by
    intro β
    rw [hproj β, hcomp β, map_smul, ← hproj β₂, smul_eq_mul]
  -- Step 5: `|s| ≤ |β₂|_E = 1`
  have hs₁ : |ζ₀ β₂| ≤ 1 := (hle β₂).trans_eq hβ₂
  -- Step 6: `1 = |β₁(v)| |s| ≤ |s|`, as `|β₁(v)| ≤ |β₁|_E ≤ 1`
  have hs₂ : 1 ≤ |ζ₀ β₂| := by
    have hβ₁v : |β₁ v| ≤ 1 :=
      (Submission.regcomp_covector_eval_orthonormal_le P (d + 1) β₁ v hv).trans hβ₁
    calc (1 : ℝ) = |β₁ v| * |ζ₀ β₂| := by rw [← abs_mul, ← hζ β₁, hζβ₁, abs_one]
      _ ≤ 1 * |ζ₀ β₂| := mul_le_mul_of_nonneg_right hβ₁v (abs_nonneg _)
      _ = |ζ₀ β₂| := one_mul _
  -- Step 7: `s = ±1`; for `s = −1` negate `v₀`
  refine ⟨hrank, ?_⟩
  rcases (abs_eq zero_le_one).mp (le_antisymm hs₁ hs₂) with hs | hs
  · exact ⟨v, hv, hspan, fun β => by rw [hζ β, hs, mul_one]⟩
  · obtain ⟨w, hw, hwspan, hwβ⟩ := Submission.cbr_ci_cp_exists_orthonormal_frame_eval_neg P d v hv
    exact ⟨w, hw, hwspan.trans hspan, fun β => by rw [hζ β, hs, hwβ β, mul_neg_one]⟩

/-- A measure `m` on `ℝᴾ` carried by an `n`-dimensional linear subspace `V`, finite on compact
sets and invariant under the translations by `V`, is a constant multiple of `Hⁿ⌞V` (used for the
product structure of translation invariant measures in the integer multiplicity part of Simon
7.2.4, Remark 7.2.5(1)).  The orthogonal projection `π : ℝᴾ → V` pushes `m` forward to a
translation invariant measure on `V`, finite on compact sets, hence `c • vol_V` by uniqueness of
Haar measure.  As `m` is carried by `V`, it is the image of `π_# m` under the inclusion
`V → ℝᴾ`, an isometry, and `μHE[n] = vol_V` on `V`. -/
theorem Submission.cbr_ci_cp_prod_subspace_haar : ∀ (P n : ℕ) (m : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → m (V : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → m K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → m ((fun x => v + x) ⁻¹' A) = m A) → ∃ c : ℝ≥0∞, m = c • (μHE[n]).restrict (V : Set (Euclid P)) := by
  intro P n m V hn hVc hcpt hinv
  subst hn
  -- the orthogonal projection `π` onto `V` fixes `V` pointwise
  have hπ : ∀ x ∈ V, ((V.orthogonalProjectionOnto x : V) : Euclid P) = x := fun x hx => by
    simpa using congrArg Subtype.val (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩)
  have hπm : Measurable V.orthogonalProjectionOnto :=
    V.orthogonalProjectionOnto.continuous.measurable
  -- invariance of `m` under the translations by `V`, as an identity of measures
  have htr : ∀ v ∈ V, m.map (fun x => v + x) = m := fun v hv => by
    ext A hA
    rw [Measure.map_apply (measurable_const_add v) hA, hinv v hv A hA]
  -- `m' = π_# m` is translation invariant on `V`, as `(g + ·) ∘ π = π ∘ (g + ·)` for `g ∈ V`
  set m' : Measure V := m.map V.orthogonalProjectionOnto with hm'
  have hinv' : m'.IsAddLeftInvariant := ⟨fun g => by
    have hcomm : (fun x : V => g + x) ∘ V.orthogonalProjectionOnto =
        V.orthogonalProjectionOnto ∘ (fun x => (g : Euclid P) + x) := by
      funext x; simp
    rw [hm', Measure.map_map (measurable_const_add g) hπm, hcomm,
      ← Measure.map_map hπm (measurable_const_add _), htr _ g.2]⟩
  -- `m'` is finite on compact sets, as `π⁻¹ K ⊆ ι K ∪ Vᶜ` and `m Vᶜ = 0`
  have hfin' : IsFiniteMeasureOnCompacts m' := ⟨fun K hK => by
    rw [hm', Measure.map_apply hπm hK.isClosed.measurableSet]
    calc m (V.orthogonalProjectionOnto ⁻¹' K)
        ≤ m (Subtype.val '' K ∪ (V : Set (Euclid P))ᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hxV : x ∈ V
          · exact Or.inl ⟨_, hx, hπ x hxV⟩
          · exact Or.inr hxV
      _ ≤ m (Subtype.val '' K) + m (V : Set (Euclid P))ᶜ := measure_union_le _ _
      _ < ∞ := by
          rw [hVc, add_zero]
          exact hcpt _ (hK.image continuous_subtype_val)⟩
  -- uniqueness of Haar measure on `V`
  obtain ⟨c, hc⟩ : ∃ c : NNReal, m' = c • (volume : Measure V) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul m' volume⟩
  -- `m = ι_# m'` for the inclusion `ι : V → ℝᴾ`, as `ι ∘ π = id` on `V`, which carries `m`
  have hm : m = m'.map Subtype.val := by
    rw [hm', Measure.map_map continuous_subtype_val.measurable hπm]
    conv_lhs => rw [← Measure.map_id (μ := m)]
    refine Measure.map_congr (measure_mono_null (fun x hx => ?_) hVc)
    exact fun hxV => hx (hπ x hxV).symm
  -- `ι_# vol_V = Hⁿ⌞V`, as `μHE[n] = vol_V` on `V` and `ι` is an isometry with range `V`
  have hvol : (volume : Measure V).map Subtype.val =
      (μHE[Module.finrank ℝ V]).restrict (V : Set (Euclid P)) := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      isometry_subtype_coe.map_euclideanHausdorffMeasure, Subtype.range_coe]
  refine ⟨c, ?_⟩
  rw [hm, hc, Measure.map_smul _ continuous_subtype_val.aemeasurable, hvol,
    Measure.coe_nnreal_smul]

/-- Let `ν` be a measure on `ℝᴾ`, finite on compact sets and invariant under the translations by
an `n`-dimensional linear subspace `V`, and let `p`, `q` be the orthogonal projections onto `V`
and `Vᗮ`.  Then `ν(p⁻¹ A ∩ q⁻¹ B) = σ(B) Hⁿ(A ∩ V)` for all Borel `A`, `B`, for a measure `σ`
carried by `Vᗮ` and finite on compact sets (used for the product structure of translation
invariant measures in the integer multiplicity part of Simon 7.2.4, Remark 7.2.5(1)).  Take
`σ = ωₙ⁻¹ q_#(ν⌞p⁻¹ B_1(0))`.  For bounded `B`, `p_#(ν⌞q⁻¹ B)` is carried by `V`, finite on
compact sets and invariant under the translations by `V`, hence equal to `c Hⁿ⌞V`; evaluating at
`B_1(0)`, where `Hⁿ(V ∩ B_1(0)) = ωₙ`, gives `c = σ(B)`.  Exhausting `B` by the bounded sets
`B ∩ B_j(0)` gives the general case. -/
theorem Submission.cbr_ci_cp_prod_rectangle_formula : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → ∃ σ : Measure (Euclid P), σ (Vᗮ : Set (Euclid P))ᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) ∧ ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ (V : Set (Euclid P))) := by
  intro P n ν V hn hcpt hinv
  -- `p = V.starProjection` and `q = Vᗮ.starProjection` are continuous linear, hence measurable
  have hpm : Measurable V.starProjection := V.starProjection.continuous.measurable
  have hqm : Measurable Vᗮ.starProjection := Vᗮ.starProjection.continuous.measurable
  -- for `v ∈ V`, `p (v + y) = v + p y` and `q (v + y) = q y`
  have hpv : ∀ v ∈ V, ∀ y, V.starProjection (v + y) = v + V.starProjection y := fun v hv y => by
    rw [map_add, Submodule.starProjection_eq_self_iff.2 hv]
  have hqv : ∀ v ∈ V, ∀ y, Vᗮ.starProjection (v + y) = Vᗮ.starProjection y := fun v hv y => by
    rw [map_add, Submodule.starProjection_orthogonal_apply_eq_zero hv, zero_add]
  -- boxes `{y : p y ∈ E, q y ∈ F}` with `E`, `F` bounded lie in a compact ball, as `y = p y + q y`
  have hbox : ∀ E F : Set (Euclid P), Bornology.IsBounded E → Bornology.IsBounded F →
      ν (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' F) < ∞ := by
    intro E F hE hF
    obtain ⟨R, hR⟩ := hE.subset_closedBall 0
    obtain ⟨S, hS⟩ := hF.subset_closedBall 0
    refine lt_of_le_of_lt (measure_mono fun y hy => ?_) (hcpt _ (isCompact_closedBall 0 (R + S)))
    rw [mem_closedBall_zero_iff, ← V.starProjection_add_starProjection_orthogonal y]
    exact (norm_add_le _ _).trans
      (add_le_add (mem_closedBall_zero_iff.1 (hR hy.1)) (mem_closedBall_zero_iff.1 (hS hy.2)))
  -- `Hⁿ(B_1(0) ∩ V) = ωₙ`, and `0 < ωₙ < ∞`
  have hω : μHE[n] (ball (0 : Euclid P) 1 ∩ V) = unitBallVolume n := by
    rw [Set.inter_comm, Submission.idtp_tdc_subspace_ball_measure P n V 0 1 hn V.zero_mem one_pos]
    simp
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- `σ = ωₙ⁻¹ q_#(ν⌞p⁻¹ B_1(0))`, so `σ(B) = ωₙ⁻¹ ν(q⁻¹ B ∩ p⁻¹ B_1(0))` for Borel `B`
  obtain ⟨σ, hσB⟩ : ∃ σ : Measure (Euclid P), ∀ B, MeasurableSet B → σ B =
      (unitBallVolume n)⁻¹ * ν (Vᗮ.starProjection ⁻¹' B ∩ V.starProjection ⁻¹' ball 0 1) :=
    ⟨(unitBallVolume n)⁻¹ • (ν.restrict (V.starProjection ⁻¹' ball 0 1)).map Vᗮ.starProjection,
      fun B hB => by
        rw [Measure.smul_apply, Measure.map_apply hqm hB, Measure.restrict_apply (hqm hB),
          smul_eq_mul]⟩
  -- the rectangle formula for bounded Borel `B`
  have hbdd : ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → Bornology.IsBounded B →
      ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ V) := by
    intro A B hA hB hBb
    -- `m = p_#(ν⌞q⁻¹ B)`, with `m(E) = ν(p⁻¹ E ∩ q⁻¹ B)` for Borel `E`
    obtain ⟨m, hmE⟩ : ∃ m : Measure (Euclid P), ∀ E, MeasurableSet E →
        m E = ν (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' B) :=
      ⟨(ν.restrict (Vᗮ.starProjection ⁻¹' B)).map V.starProjection, fun E hE => by
        rw [Measure.map_apply hpm hE, Measure.restrict_apply (hpm hE)]⟩
    -- `m` is carried by `V`, as `p y ∈ V`
    have hmV : m (V : Set (Euclid P))ᶜ = 0 := by
      rw [hmE _ (Submodule.closed_of_finiteDimensional V).measurableSet.compl]
      exact measure_mono_null (fun y hy => absurd (V.starProjection_apply_mem y) hy.1) measure_empty
    -- `m` is finite on compact sets, as compact sets are bounded
    have hmcpt : ∀ K : Set (Euclid P), IsCompact K → m K < ∞ := fun K hK => by
      rw [hmE K hK.isClosed.measurableSet]
      exact hbox K B hK.isBounded hBb
    -- `m` is invariant under the translations by `V`, as `ν` is
    have hminv : ∀ v ∈ V, ∀ E : Set (Euclid P), MeasurableSet E →
        m ((fun x => v + x) ⁻¹' E) = m E := by
      intro v hv E hE
      have hpre : V.starProjection ⁻¹' ((fun x => v + x) ⁻¹' E) ∩ Vᗮ.starProjection ⁻¹' B =
          (fun x => v + x) ⁻¹' (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' B) := by
        ext y
        simp only [mem_inter_iff, mem_preimage, hpv v hv, hqv v hv]
      rw [hmE _ (hE.preimage (measurable_const_add v)), hmE E hE, hpre,
        hinv v hv _ ((hpm hE).inter (hqm hB))]
    -- `m = c • Hⁿ⌞V`; evaluating at `B_1(0)` gives `c = σ(B)`
    obtain ⟨c, hc⟩ := Submission.cbr_ci_cp_prod_subspace_haar P n m V hn hmV hmcpt hminv
    have hball : ν (V.starProjection ⁻¹' ball 0 1 ∩ Vᗮ.starProjection ⁻¹' B) =
        unitBallVolume n * c := by
      rw [← hmE (ball 0 1) measurableSet_ball, hc, Measure.smul_apply,
        Measure.restrict_apply measurableSet_ball, hω, smul_eq_mul, mul_comm]
    have hσc : σ B = c := by
      rw [hσB B hB, Set.inter_comm, hball, ENNReal.inv_mul_cancel_left hω0 hωtop]
    rw [← hmE A hA, hc, Measure.smul_apply, Measure.restrict_apply hA, hσc, smul_eq_mul]
  refine ⟨σ, ?_, fun K hK => ?_, fun A B hA hB => ?_⟩
  · -- `σ` is carried by `Vᗮ`, as `q y ∈ Vᗮ`
    rw [hσB _ V.isClosed_orthogonal.measurableSet.compl,
      measure_mono_null (fun y hy => absurd (Vᗮ.starProjection_apply_mem y) hy.1) measure_empty,
      mul_zero]
  · -- `σ` is finite on compact sets, as compact sets are bounded and `ωₙ ≠ 0`
    rw [hσB K hK.isClosed.measurableSet, Set.inter_comm]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hω0))
      (hbox _ _ isBounded_ball hK.isBounded)
  · -- exhaust `B` by the bounded sets `B ∩ B_j(0)`, by continuity from below for `ν` and `σ`
    have hmono : Monotone fun j : ℕ => B ∩ ball (0 : Euclid P) j := fun i j hij =>
      inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
    have hU : ⋃ j : ℕ, B ∩ ball (0 : Euclid P) j = B := by
      rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
    have hmono' : Monotone fun j : ℕ =>
        V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' (B ∩ ball (0 : Euclid P) j) :=
      fun i j hij => inter_subset_inter_right _ (preimage_mono (hmono hij))
    have hνU := hmono'.measure_iUnion (μ := ν)
    have hσU := hmono.measure_iUnion (μ := σ)
    rw [← inter_iUnion, ← preimage_iUnion, hU] at hνU
    rw [hU] at hσU
    rw [hνU, hσU, ENNReal.iSup_mul]
    exact iSup_congr fun j => hbdd A _ hA (hB.inter measurableSet_ball)
      (isBounded_ball.subset inter_subset_right)
/-- If `σ` is carried by `Vᗮ` and finite on compact sets, and `ν` has the rectangle values
`ν(p⁻¹(A) ∩ q⁻¹(B)) = σ(B) Hⁿ(A ∩ V)` for Borel `A`, `B` (`p`, `q` the orthogonal projections onto
the `n`-dimensional subspace `V` and onto `Vᗮ`), then `ν(A) = ∫_V σ({y : t + y ∈ A}) dHⁿ(t)`, i.e.
`ν` is the image of `(Hⁿ⌞V) ⊗ σ` under `(t, y) ↦ t + y` (used, via the closure theorem, in the
proof of Simon 7.2.4).  The rectangles form a π-system generating the Borel sets (`y = p y + q y`),
the image measure takes the same values on them because `σ` is carried by `Vᗮ`, and the rectangles
over the balls `B_{j+1}(0)` cover `ℝᴾ` and have finite `ν`-measure, so the two measures agree. -/
theorem Submission.cbr_ci_cp_prod_of_rectangles : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) → (∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ (V : Set (Euclid P)))) → ∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n] := by
  intro P n ν σ V hn hσ hσfin hrect A hA
  -- `σ` is finite on compact sets, hence locally finite and σ-finite on `ℝᴾ`
  have : IsFiniteMeasureOnCompacts σ := ⟨hσfin⟩
  have hp : Measurable V.starProjection := V.starProjection.continuous.measurable
  have hq : Measurable Vᗮ.starProjection := Vᗮ.starProjection.continuous.measurable
  have hV : MeasurableSet (V : Set (Euclid P)) := V.closed_of_finiteDimensional.measurableSet
  -- the candidate `λ = s_#((Hⁿ⌞V) ⊗ σ)` with `s(t, y) = t + y`
  have hs : Measurable fun z : Euclid P × Euclid P => z.1 + z.2 := measurable_fst.add measurable_snd
  have hlam : ∀ A : Set (Euclid P), MeasurableSet A →
      ((μHE[n].restrict (V : Set (Euclid P))).prod σ).map (fun z => z.1 + z.2) A =
        ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n] := by
    intro A hA
    rw [Measure.map_apply hs hA, Measure.prod_apply (hs hA)]
    rfl
  rw [← hlam A hA]
  congr 1
  -- rectangles `p⁻¹(A) ∩ q⁻¹(B)` form a π-system generating the Borel σ-algebra
  let C : Set (Set (Euclid P)) := {S | ∃ A B : Set (Euclid P), MeasurableSet A ∧ MeasurableSet B ∧
    S = V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B}
  have hgen : (inferInstance : MeasurableSpace (Euclid P)) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · have hp' : Measurable[MeasurableSpace.generateFrom C] V.starProjection := fun A hA =>
        MeasurableSpace.measurableSet_generateFrom ⟨A, univ, hA, MeasurableSet.univ, by
          rw [preimage_univ, inter_univ]⟩
      have hq' : Measurable[MeasurableSpace.generateFrom C] Vᗮ.starProjection := fun B hB =>
        MeasurableSpace.measurableSet_generateFrom ⟨univ, B, MeasurableSet.univ, hB, by
          rw [preimage_univ, univ_inter]⟩
      have hid := @Measurable.add _ _ _ _ (MeasurableSpace.generateFrom C)
        (fun y => V.starProjection y) (fun y => Vᗮ.starProjection y) _ hp' hq'
      have hfun : ((fun y => V.starProjection y) + fun y => Vᗮ.starProjection y) = id :=
        funext V.starProjection_add_starProjection_orthogonal
      rw [hfun] at hid
      exact fun S hS => hid hS
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      exact (hp hA).inter (hq hB)
  have hpi : IsPiSystem C := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by
      rw [preimage_inter, preimage_inter, inter_inter_inter_comm]⟩
  -- the rectangles `p⁻¹(B_{j+1}(0)) ∩ q⁻¹(B_{j+1}(0))` cover `ℝᴾ` and have finite `ν`-measure
  refine Measure.ext_of_generateFrom_of_iUnion C
    (fun j : ℕ => V.starProjection ⁻¹' ball 0 (j + 1) ∩ Vᗮ.starProjection ⁻¹' ball 0 (j + 1))
    hgen hpi ?_ ?_ ?_ ?_
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (max ‖V.starProjection y‖ ‖Vᗮ.starProjection y‖)
    exact ⟨j, mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt (hj.trans (lt_add_one _))),
      mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt (hj.trans (lt_add_one _)))⟩
  · exact fun j => ⟨_, _, measurableSet_ball, measurableSet_ball, rfl⟩
  · intro j
    rw [hrect _ _ measurableSet_ball measurableSet_ball, inter_comm,
      Submission.idtp_tdc_subspace_ball_measure P n V 0 (j + 1) hn V.zero_mem (by positivity)]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne
      (ENNReal.mul_ne_top (measure_ball_lt_top (μ := volume)).ne ENNReal.ofReal_ne_top)
  -- `ν` and `λ` agree on rectangles because `σ` is carried by `Vᗮ`
  · rintro _ ⟨A, B, hA, hB, rfl⟩
    rw [hrect A B hA hB, hlam _ ((hp hA).inter (hq hB))]
    have key : EqOn (fun t => σ ((fun y => t + y) ⁻¹'
        (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B))) (A.indicator fun _ => σ B) V := by
      intro t ht
      have hsec : ∀ y ∈ (Vᗮ : Set (Euclid P)),
          V.starProjection (t + y) = t ∧ Vᗮ.starProjection (t + y) = y := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [map_add, V.starProjection_eq_self_iff.mpr ht,
            V.starProjection_apply_eq_zero_iff.mpr hy, add_zero]
        · rw [map_add, V.starProjection_orthogonal_apply_eq_zero ht,
            Vᗮ.starProjection_eq_self_iff.mpr hy, zero_add]
      simp only
      rw [← measure_inter_conull hσ]
      by_cases htA : t ∈ A
      · rw [indicator_of_mem htA, ← measure_inter_conull (s := B) hσ]
        congr 1
        ext y
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨⟨-, hyB⟩, hy⟩
          rw [(hsec y hy).2] at hyB
          exact ⟨hyB, hy⟩
        · rintro ⟨hyB, hy⟩
          rw [(hsec y hy).1, (hsec y hy).2]
          exact ⟨⟨htA, hyB⟩, hy⟩
      · rw [indicator_of_notMem htA]
        convert measure_empty (μ := σ)
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨⟨hyA, -⟩, hy⟩
        exact htA ((hsec y hy).1 ▸ hyA)
    rw [setLIntegral_congr_fun hV key, lintegral_indicator_const hA, Measure.restrict_apply hA]

/-- A measure `ν` on `ℝᴾ`, finite on compact sets and invariant under the translations by an
`n`-dimensional linear subspace `V`, is the image of `(Hⁿ⌞V) ⊗ σ` under `(t, y) ↦ t + y` for a
measure `σ` carried by `V^⊥` and finite on compact sets (used for the product structure of
translation invariant measures in the integer multiplicity part of Simon 7.2.4, Remark
7.2.5(1)).  With `p = V.starProjection` and `q = Vᗮ.starProjection`, uniqueness of Haar measure
on `V` gives such a `σ` with `ν(p⁻¹(A) ∩ q⁻¹(B)) = σ(B)·Hⁿ(A ∩ V)` for Borel `A`, `B`; the image
of `(Hⁿ⌞V) ⊗ σ` under addition has the same values on these rectangles, which form a generating
π-system covered by countably many rectangles of finite measure, so it equals `ν`. -/
theorem Submission.cbr_ci_cp_invariant_measure_product : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → ∃ σ : Measure (Euclid P), σ (Vᗮ : Set (Euclid P))ᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) ∧ ∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n] := by
  intro P n ν V hn hcpt hinv
  -- the transverse measure `σ` on `V^⊥` and the rectangle formula (Haar uniqueness on `V`)
  obtain ⟨σ, hσV, hσcpt, hrect⟩ :=
    Submission.cbr_ci_cp_prod_rectangle_formula P n ν V hn hcpt hinv
  -- `ν` agrees with the image of `(Hⁿ⌞V) ⊗ σ` on rectangles, hence on all Borel sets
  exact ⟨σ, hσV, hσcpt, Submission.cbr_ci_cp_prod_of_rectangles P n ν σ V hn hσV hσcpt hrect⟩

/-- `ν(B_r(x)) ≤ ωₙrⁿ σ(B_r(x − p_V x))` when `ν(A) = ∫_V σ({y : t + y ∈ A}) dHⁿ(t)` for a
subspace `V` with `dim V = n` and a measure `σ` carried by `Vᗮ`.  Write `x = p₀ + q₀` with
`p₀ = p_V x ∈ V` and `q₀ = x − p_V x ∈ Vᗮ`.  For `t ∈ V` and `z ∈ Vᗮ`, Pythagoras gives
`|t + z − x|² = |t − p₀|² + |z − q₀|²`, so `t + z ∈ B_r(x)` forces `t ∈ B_r(p₀)` and
`z ∈ B_r(q₀)`.  Hence `σ({y : t + y ∈ B_r(x)}) ≤ 1_{B_r(p₀)}(t) σ(B_r(q₀))`, and integrating over
`V` gives `ν(B_r(x)) ≤ σ(B_r(q₀)) Hⁿ(V ∩ B_r(p₀)) = ωₙrⁿ σ(B_r(q₀))`. -/
theorem Submission.cbr_ci_cp_atm_ball_le_transversal_ball : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → ∀ (x : Euclid P) (r : ℝ), 0 < r → ν (ball x r) ≤ unitBallVolume n * ENNReal.ofReal (r ^ n) * σ (ball (x - V.starProjection x) r) := by
  intro P n ν σ V hn hσ hν x r hr
  -- `x = p₀ + q₀` with `p₀ = p_V x ∈ V` and `q₀ = x − p₀ ∈ Vᗮ`
  set p₀ := V.starProjection x
  have hp₀ : p₀ ∈ V := V.starProjection_apply_mem x
  have hq₀ : x - p₀ ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
  -- Pythagoras: for `t ∈ V` and `z ∈ Vᗮ`, `t + z ∈ B_r(x)` forces `t ∈ B_r(p₀)`, `z ∈ B_r(q₀)`
  have hpyth : ∀ t ∈ V, ∀ z ∈ Vᗮ, t + z ∈ ball x r →
      t ∈ ball p₀ r ∧ z ∈ ball (x - p₀) r := by
    intro t ht z hz htz
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real
      (V.inner_right_of_mem_orthogonal (V.sub_mem ht hp₀) (Vᗮ.sub_mem hz hq₀))
    rw [show t - p₀ + (z - (x - p₀)) = t + z - x by abel] at hpy
    simp only [mem_ball, dist_eq_norm] at htz ⊢
    have hlt : ‖t + z - x‖ * ‖t + z - x‖ < r * r := mul_self_lt_mul_self (norm_nonneg _) htz
    constructor
    · exact (mul_self_lt_mul_self_iff (norm_nonneg _) hr.le).2
        (by linarith [mul_self_nonneg ‖z - (x - p₀)‖])
    · exact (mul_self_lt_mul_self_iff (norm_nonneg _) hr.le).2
        (by linarith [mul_self_nonneg ‖t - p₀‖])
  -- `σ` is carried by `Vᗮ`, so `σ({y : t + y ∈ B_r(x)}) ≤ 1_{B_r(p₀)}(t) σ(B_r(q₀))` on `V`
  have hslice : ∀ t ∈ (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' ball x r) ≤
      (ball p₀ r).indicator (fun _ => σ (ball (x - p₀) r)) t := by
    intro t ht
    rw [← measure_inter_conull (s := (fun y => t + y) ⁻¹' ball x r) hσ]
    by_cases htp : t ∈ ball p₀ r
    · rw [indicator_of_mem htp]
      exact measure_mono fun z hz => (hpyth t ht z hz.2 hz.1).2
    · have hempty : (fun y => t + y) ⁻¹' ball x r ∩ (Vᗮ : Set (Euclid P)) = ∅ :=
        eq_empty_of_forall_notMem fun z hz => htp (hpyth t ht z hz.2 hz.1).1
      rw [indicator_of_notMem htp, hempty, measure_empty]
  -- integrate over `V` and use `Hⁿ(V ∩ B_r(p₀)) = ωₙrⁿ`
  calc ν (ball x r)
      = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' ball x r) ∂μHE[n] :=
        hν _ measurableSet_ball
    _ ≤ ∫⁻ t in (V : Set (Euclid P)),
          (ball p₀ r).indicator (fun _ => σ (ball (x - p₀) r)) t ∂μHE[n] :=
        setLIntegral_mono' V.closed_of_finiteDimensional.measurableSet hslice
    _ = σ (ball (x - p₀) r) * μHE[n] ((V : Set (Euclid P)) ∩ ball p₀ r) := by
        rw [lintegral_indicator_const measurableSet_ball, Measure.restrict_apply measurableSet_ball,
          inter_comm]
    _ = unitBallVolume n * ENNReal.ofReal (r ^ n) * σ (ball (x - p₀) r) := by
        rw [Submission.idtp_tdc_subspace_ball_measure P n V p₀ r hn hp₀ hr, mul_comm]
/-- If `σ` is finite on compact sets and `f(r) ≤ ωₙrⁿσ(B_r(z))` for every `r > 0`, then
`liminf_{r↓0} f(r)/(ωₙrⁿ) ≤ σ({z})` (used in the closure step of the proof of Simon 7.2.4,
p. 184, to show that the transversal measure of a measure invariant along a plane is atomic).
For `r > 0`, `f(r)/(ωₙrⁿ) ≤ σ(B_r(z))` in `[0, ∞]`; and `σ(B_r(z)) → σ({z})` as `r ↓ 0` by
continuity from above, the balls decreasing to `{z}` and `σ(B_1(z)) ≤ σ(B̄_1(z)) < ∞`. -/
theorem Submission.cbr_ci_cp_atm_liminf_density_le_atom : ∀ (P n : ℕ) (σ : Measure (Euclid P)) (z : Euclid P) (f : ℝ → ℝ≥0∞), (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) → (∀ r : ℝ, 0 < r → f r ≤ unitBallVolume n * ENNReal.ofReal (r ^ n) * σ (ball z r)) → liminf (fun r : ℝ => f r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ σ {z} := by
  intro P n σ z f hσ hf
  -- the balls `B_r(z)` decrease to `{z}` as `r ↓ 0`
  have hinter : (⋂ r > (0 : ℝ), ball z r) = {z} := by
    ext y
    simp only [mem_iInter, mem_ball, mem_singleton_iff]
    refine ⟨fun hy => ?_, fun hy r hr => by rwa [hy, dist_self]⟩
    by_contra hne
    exact lt_irrefl _ (hy (dist y z) (dist_pos.2 hne))
  -- continuity from above, with `σ(B_1(z)) ≤ σ(B̄_1(z)) < ∞`
  have hlim : Tendsto (fun r : ℝ => σ (ball z r)) (𝓝[>] 0) (𝓝 (σ {z})) := by
    rw [← hinter]
    exact tendsto_measure_biInter_gt (fun r _ => measurableSet_ball.nullMeasurableSet)
      (fun i j _ hij => ball_subset_ball hij)
      ⟨1, one_pos, ((measure_mono ball_subset_closedBall).trans_lt
        (hσ _ (isCompact_closedBall z 1))).ne⟩
  -- `f(r)/(ωₙrⁿ) ≤ σ(B_r(z))` for `r > 0`, then monotonicity of `liminf`
  calc liminf (fun r : ℝ => f r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)
      ≤ liminf (fun r : ℝ => σ (ball z r)) (𝓝[>] 0) :=
        liminf_le_liminf (eventually_mem_nhdsWithin.mono fun r hr =>
          ENNReal.div_le_of_le_mul' (hf r hr))
    _ = σ {z} := hlim.liminf_eq
/-- If `ν(A) = ∫_V σ(A − t) dHⁿ(t)` for Borel `A`, where `V` is an `n`-dimensional subspace of
`ℝᴾ` and `σ` is carried by `Vᗮ`, and `x − p_V x ∈ Z` for `ν`-a.e. `x` with `Z` Borel, then
`σ(ℝᴾ ∖ Z) = 0` (used for the translation-invariant blow-up measures in B. White's proof of the
closure theorem, part of Simon 7.2.4).  The Borel set `E = {y : y − p_V y ∉ Z}` is `ν`-null and
invariant under translation by `V`, so `0 = ν(E) = σ(E) Hⁿ(V)`;
`Hⁿ(V) ≥ Hⁿ(V ∩ B_1(0)) = ωₙ > 0` gives `σ(E) = 0`, and `ℝᴾ ∖ Z ⊆ E ∪ (ℝᴾ ∖ Vᗮ)` because
`p_V w = 0` for `w ∈ Vᗮ`. -/
theorem Submission.cbr_ci_cp_atm_transversal_carried : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)), Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → MeasurableSet Z → (∀ᵐ x ∂ν, x - V.starProjection x ∈ Z) → σ Zᶜ = 0 := by
  intro P n ν σ V Z hn hσ hD hZ hae
  -- `E = {y : y − p_V y ∉ Z}` is Borel and `ν`-null
  set E : Set (Euclid P) := (fun y => y - V.starProjection y) ⁻¹' Zᶜ with hE_def
  have hE : MeasurableSet E := (continuous_id.sub V.starProjection.continuous).measurable hZ.compl
  have hνE : ν E = 0 := ae_iff.mp hae
  -- `p_V (t + y) = t + p_V y` for `t ∈ V`, so `E` is invariant under translation by `V`
  -- and the product formula gives `ν(E) = σ(E) Hⁿ(V)`
  have hprod : ν E = σ E * μHE[n] (V : Set (Euclid P)) := by
    rw [hD E hE, ← setLIntegral_const]
    refine setLIntegral_congr_fun V.closed_of_finiteDimensional.measurableSet fun t ht => ?_
    congr 1
    ext y
    simp [hE_def, Submodule.starProjection_eq_self_iff.mpr ht]
  -- `Hⁿ(V) ≥ Hⁿ(V ∩ B_1(0)) = ωₙ > 0`
  have hV : μHE[n] (V : Set (Euclid P)) ≠ 0 := by
    have hball := Submission.idtp_tdc_subspace_ball_measure P n V 0 1 hn V.zero_mem one_pos
    rw [one_pow, ENNReal.ofReal_one, mul_one] at hball
    have hω : 0 < unitBallVolume n := measure_ball_pos volume (0 : Euclid n) one_pos
    refine (hω.trans_le ?_).ne'
    rw [← hball]
    exact measure_mono Set.inter_subset_left
  have hσE : σ E = 0 := by
    rw [hνE, eq_comm, mul_eq_zero] at hprod
    exact hprod.resolve_right hV
  -- `ℝᴾ ∖ Z ⊆ E ∪ (ℝᴾ ∖ Vᗮ)`, since `p_V w = 0` for `w ∈ Vᗮ`
  refine measure_mono_null (fun w hw => ?_) (measure_union_null hσE hσ)
  by_cases hw' : w ∈ Vᗮ
  · left
    show w - V.starProjection w ∈ Zᶜ
    rwa [(V.starProjection_apply_eq_zero_iff).mpr hw', sub_zero]
  · exact Or.inr hw'
/-- A measure `ν` on `ℝᴾ` with `ν(A) = ∫⁻_{t ∈ V} σ({y : t + y ∈ A}) dHⁿ(t)` for Borel `A`, whose
transversal measure `σ` is carried by a countable set `Z`, is the countable sum of weighted parallel
planes `ν = Σ_{w ∈ Z} σ({w}) Hⁿ⌞(w + V)` (a step of the proof of Simon 7.2.4, for cycles with a
constant orientation).  `σ` is the sum of its atoms on `Z`; inserting this into the product
formula, monotone convergence exchanges sum and integral, and the translation by `w` is an isometry
carrying `{t : t + w ∈ A} ∩ V` onto `A ∩ (w + V)`, under which `Hⁿ` is invariant. -/
theorem Submission.cbr_ci_cp_atm_sum_planes_of_carried : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)), Z.Countable → σ Zᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → ν = Measure.sum (fun w : Z => σ {(w : Euclid P)} • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) := by
  intro P n ν σ V Z hZ hσ hν
  have := hZ.to_subtype
  -- `σ` is carried by the countable set `Z`, hence is the sum of its atoms there
  have hatom : ∀ S : Set (Euclid P), MeasurableSet S →
      σ S = ∑' w : Z, S.indicator (fun x => σ {x}) (w : Euclid P) := by
    intro S hS
    have hSZ : S ∩ Z = ⋃ w : Z, S ∩ {(w : Euclid P)} := by
      ext y
      simp
    rw [← measure_inter_conull hσ, hSZ, measure_iUnion]
    · congr 1
      ext w
      by_cases hw : (w : Euclid P) ∈ S
      · simp [hw]
      · simp [hw]
    · intro w w' hww'
      exact Disjoint.mono inter_subset_right inter_subset_right
        (disjoint_singleton.2 (Subtype.coe_injective.ne hww'))
    · exact fun w => hS.inter (measurableSet_singleton _)
  ext A hA
  rw [hν A hA, Measure.sum_apply _ hA]
  calc ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]
      = ∫⁻ t in (V : Set (Euclid P)), ∑' w : Z,
          ((fun t => t + (w : Euclid P)) ⁻¹' A).indicator (fun _ => σ {(w : Euclid P)}) t ∂μHE[n] := by
        refine lintegral_congr fun t => ?_
        rw [hatom _ (measurable_const_add t hA)]
        refine tsum_congr fun w => ?_
        by_cases hw : t + (w : Euclid P) ∈ A
        · rw [indicator_of_mem (show (w : Euclid P) ∈ (fun y => t + y) ⁻¹' A from hw),
            indicator_of_mem (show t ∈ (fun t => t + (w : Euclid P)) ⁻¹' A from hw)]
        · rw [indicator_of_notMem (show (w : Euclid P) ∉ (fun y => t + y) ⁻¹' A from hw),
            indicator_of_notMem (show t ∉ (fun t => t + (w : Euclid P)) ⁻¹' A from hw)]
    -- monotone convergence for the countable sum, then integrate the indicators
    _ = ∑' w : Z, σ {(w : Euclid P)} *
          (μHE[n]).restrict (V : Set (Euclid P)) ((fun t => t + (w : Euclid P)) ⁻¹' A) := by
        rw [lintegral_tsum fun w : Z => (measurable_const.indicator
          (measurable_add_const (w : Euclid P) hA)).aemeasurable]
        simp only [lintegral_indicator_const (measurable_add_const _ hA)]
    _ = ∑' w : Z, (σ {(w : Euclid P)} • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) A := by
        congr 1
        ext w
        rw [Measure.restrict_apply (measurable_add_const _ hA), Measure.smul_apply, smul_eq_mul,
          Measure.restrict_apply hA]
        congr 1
        -- the translation by `w` is an isometry carrying `{t : t + w ∈ A} ∩ V` onto `A ∩ (w + V)`
        have hpre : (fun t => t + (w : Euclid P)) ⁻¹' (A ∩ {y : Euclid P | y - w ∈ V}) =
            (fun t => t + (w : Euclid P)) ⁻¹' A ∩ V := by
          ext t
          simp
        rw [← hpre, (isometry_add_right (w : Euclid P)).euclideanHausdorffMeasure_preimage,
          (add_right_surjective (w : Euclid P)).range_eq, inter_univ]

/-- **A transversal measure with lower density `≥ c` is atomic** (B. White's tangent-plane proof of
the closure theorem used for Simon 7.2.4: a cycle with constant orientation is a sum of parallel
planes).  Let `V ⊆ ℝᴾ` be an `n`-dimensional subspace, `σ` a measure carried by `Vᗮ` and finite on
compact sets, and `ν(A) = ∫_V σ({y : t + y ∈ A}) dHⁿ(t)` for Borel `A`.  If
`ofReal c ≤ liminf_{r ↓ 0} ν(B_r(y))/(ωₙrⁿ)` for `ν`-a.e. `y`, then
`ν = Σ_{w ∈ Z} σ({w}) Hⁿ⌞(w + V)` for the set `Z ⊆ Vᗮ` of atoms of `σ` of mass `≥ c`.
`Z ∩ B̄_j(0)` is finite, since infinitely many atoms of mass `≥ c` have infinite `σ`-measure while
`σ(B̄_j(0)) < ∞`; so `Z` is countable.  For `x ∈ ℝᴾ`, `ν(B_r(x)) ≤ ωₙrⁿσ(B_r(x − p x))`
(`p` the projection onto `V`), so the lower density of `ν` at `x` is at most `σ({x − p x})`;
hence `x − p x ∈ Z` for `ν`-a.e. `x`, `σ` is carried by `Z`, and `ν` is the sum of the planes. -/
theorem Submission.cbr_ci_cp_atomic_transversal : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (c : ℝ), 0 < c → Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → (∀ᵐ y ∂ν, ENNReal.ofReal c ≤ liminf (fun r : ℝ => ν (ball y r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → ∃ Z : Set (Euclid P), Z.Countable ∧ Z ⊆ (Vᗮ : Set (Euclid P)) ∧ (∀ w ∈ Z, ENNReal.ofReal c ≤ σ {w}) ∧ ν = Measure.sum (fun w : Z => σ {(w : Euclid P)} • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) := by
  intro P n ν σ V c hc hn hσV hσK hD hdens
  -- `Z`: the atoms of `σ` in `Vᗮ` of mass at least `c`
  set Z : Set (Euclid P) := {w | w ∈ (Vᗮ : Set (Euclid P)) ∧ ENNReal.ofReal c ≤ σ {w}}
  -- `Z ∩ B̄_j(0)` is finite: infinitely many atoms of mass `≥ c` would have infinite measure
  have hZc : Z.Countable := by
    rw [← iUnion_inter_closedBall_nat Z (0 : Euclid P)]
    refine countable_iUnion fun j => Set.Finite.countable ?_
    by_contra hinf
    have hlt : σ (Z ∩ closedBall (0 : Euclid P) j) < ∞ :=
      (measure_mono inter_subset_right).trans_lt (hσK _ (isCompact_closedBall _ _))
    exact hlt.ne (Set.Infinite.meas_eq_top hinf
      ⟨ENNReal.ofReal c, (ENNReal.ofReal_pos.2 hc).ne', fun w hw => hw.1.2⟩)
  -- `ν`-a.e. `x`: the density bound and `ν(B_r(x)) ≤ ωₙrⁿσ(B_r(x − p x))` give `x − p x ∈ Z`
  have hae : ∀ᵐ x ∂ν, x - V.starProjection x ∈ Z := by
    filter_upwards [hdens] with x hx
    exact ⟨V.sub_starProjection_mem_orthogonal x, hx.trans
      (Submission.cbr_ci_cp_atm_liminf_density_le_atom P n σ (x - V.starProjection x)
        (fun r => ν (ball x r)) hσK
        (Submission.cbr_ci_cp_atm_ball_le_transversal_ball P n ν σ V hn hσV hD x))⟩
  -- `σ` is carried by the countable set `Z`, so `ν` is the sum of the planes `w + V`, `w ∈ Z`
  have hσZ : σ Zᶜ = 0 :=
    Submission.cbr_ci_cp_atm_transversal_carried P n ν σ V Z hn hσV hD hZc.measurableSet hae
  exact ⟨Z, hZc, fun w hw => hw.1, fun w hw => hw.2,
    Submission.cbr_ci_cp_atm_sum_planes_of_carried P n ν σ V Z hZc hσZ hD⟩

/-- `Hⁿ({y : y - w ∈ V} ∩ B_R(0)) = ωₙ(√(R² - ‖w‖²))ⁿ` for an `n`-dimensional linear subspace `V`
of `ℝᴾ`, an offset `w ∈ V^⊥` and `‖w‖ < R` (a plane in a ball, used in the proof of Simon 7.2.4,
p. 184, for measures carried by finitely many parallel `n`-planes).  Put `ρ = √(R² - ‖w‖²) > 0`.
By Pythagoras `‖t + w‖² = ‖t‖² + ‖w‖²` for `t ∈ V`, so the translation `t ↦ t + w`, an isometry,
maps `V ∩ B_ρ(0)` onto the set; isometry invariance of `μHE[n]` and the subspace-ball formula
`Hⁿ(V ∩ B_ρ(0)) = ωₙρⁿ` conclude. -/
theorem Submission.cbr_ci_cp_fp_offset_plane_ball_measure : ∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)) (w : Euclid P) (R : ℝ), Module.finrank ℝ V = n → w ∈ Vᗮ → ‖w‖ < R → μHE[n] ({y : Euclid P | y - w ∈ V} ∩ ball 0 R) = unitBallVolume n * ENNReal.ofReal (Real.sqrt (R ^ 2 - ‖w‖ ^ 2) ^ n) := by
  intro P n V w R hn hw hR
  -- the radius `ρ = √(R² - ‖w‖²)` is positive and `ρ² = R² - ‖w‖²`
  have hpos : 0 < R ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hρ : 0 < Real.sqrt (R ^ 2 - ‖w‖ ^ 2) := Real.sqrt_pos.2 hpos
  have hρsq : Real.sqrt (R ^ 2 - ‖w‖ ^ 2) ^ 2 = R ^ 2 - ‖w‖ ^ 2 := Real.sq_sqrt hpos.le
  -- Pythagoras: `‖t + w‖² = ‖t‖² + ‖w‖²` for `t ∈ V`, as `w ⊥ V`
  have hpyth : ∀ t ∈ V, ‖t + w‖ ^ 2 = ‖t‖ ^ 2 + ‖w‖ ^ 2 := fun t ht => by
    rw [sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_real (Submodule.inner_right_of_mem_orthogonal ht hw)
  -- the translation `t ↦ t + w` maps `V ∩ B_ρ(0)` onto `{y | y - w ∈ V} ∩ B_R(0)`
  have himage : (fun t => t + w) '' ((V : Set (Euclid P)) ∩ ball 0 (Real.sqrt (R ^ 2 - ‖w‖ ^ 2))) =
      {y : Euclid P | y - w ∈ V} ∩ ball 0 R := by
    ext y
    simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe, mem_ball_zero_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ⟨ht, htρ⟩, rfl⟩
      refine ⟨by simpa using ht, ?_⟩
      have h := hpyth t ht
      nlinarith [norm_nonneg t, norm_nonneg w, norm_nonneg (t + w)]
    · rintro ⟨hy, hyR⟩
      refine ⟨y - w, ⟨hy, ?_⟩, sub_add_cancel y w⟩
      have h := hpyth (y - w) hy
      rw [sub_add_cancel] at h
      nlinarith [norm_nonneg (y - w), norm_nonneg y]
  -- isometry invariance of `μHE[n]`, then the subspace-ball formula with centre `0 ∈ V`
  rw [← himage, (isometry_add_right w).euclideanHausdorffMeasure_image]
  exact Submission.idtp_tdc_subspace_ball_measure P n V 0 _ hn V.zero_mem hρ

/-- Weighted parallel `n`-planes with at most Euclidean volume growth have total weight `≤ 1`.
Let `V ⊆ ℝᴾ` be an `n`-dimensional subspace, `Z ⊆ V^⊥` and `a : ℝᴾ → [0, ∞]`.  If
`ν = Σ_{w ∈ Z} a(w) Hⁿ⌞{y : y − w ∈ V}` satisfies `ν(B_R(0)) ≤ ωₙRⁿ` for every `R > 0`, then
`Σ_{w ∈ Z} a(w) ≤ 1`.  For a finite set `s` of offsets put `M = Σ_{z ∈ s} ‖z‖` and let `R > M`.
Each plane `z + V` meets `B_R(0)` in an `n`-ball of radius `√(R² − ‖z‖²) ≥ R − M`, so
`ωₙ(R − M)ⁿ Σ_{z ∈ s} a(z) ≤ ν(B_R(0)) ≤ ωₙRⁿ`, i.e. `Σ_{z ∈ s} a(z) ≤ (R / (R − M))ⁿ`; let
`R → ∞`. -/
theorem Submission.cbr_ci_cp_fp_tsum_weight_le_one : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)) (a : Euclid P → ℝ≥0∞), Module.finrank ℝ V = n → Z ⊆ (Vᗮ : Set (Euclid P)) → ν = Measure.sum (fun w : Z => a w • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) → ∑' w : Z, a w ≤ 1 := by
  intro P n ν V Z a hn hZ hν hνR
  -- `0 < ωₙ < ∞`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- `ν(B_R(0)) = Σ_{z ∈ Z} a(z) Hⁿ({y : y − z ∈ V} ∩ B_R(0))`
  have hball : ∀ R : ℝ, ν (ball 0 R) =
      ∑' z : Z, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
    intro R
    rw [hν, Measure.sum_apply _ measurableSet_ball]
    refine tsum_congr fun z => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_ball, inter_comm]
  -- it suffices to bound every finite partial sum; `M` bounds the offsets in `s`
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  obtain ⟨M, hM, hzM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ s, ‖(z : Euclid P)‖ ≤ M :=
    ⟨∑ z ∈ s, ‖(z : Euclid P)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun z hz =>
      Finset.single_le_sum (f := fun z : Z => ‖(z : Euclid P)‖) (fun _ _ => norm_nonneg _) hz⟩
  -- for `R > M`: `Σ_{z ∈ s} a(z) ≤ (R / (R − M))ⁿ`
  have key : ∀ R : ℝ, M < R → ∑ z ∈ s, a z ≤ ENNReal.ofReal ((R / (R - M)) ^ n) := by
    intro R hR
    have hRM : 0 < R - M := sub_pos.mpr hR
    -- each plane meets `B_R(0)` in an `n`-ball of radius `√(R² − ‖z‖²) ≥ R − M`
    have hplane : ∀ z ∈ s, unitBallVolume n * ENNReal.ofReal ((R - M) ^ n) ≤
        μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
      intro z hz
      have hzR := hzM z hz
      have hr : R - M ≤ Real.sqrt (R ^ 2 - ‖(z : Euclid P)‖ ^ 2) := by
        refine Real.le_sqrt_of_sq_le ?_
        nlinarith [mul_nonneg hRM.le hM, mul_nonneg (sub_nonneg.mpr hzR) hM,
          mul_nonneg (sub_nonneg.mpr hzR) (norm_nonneg (z : Euclid P))]
      rw [Submission.cbr_ci_cp_fp_offset_plane_ball_measure P n V z R hn (hZ z.2)
        (hzR.trans_lt hR)]
      gcongr
    have hsum : unitBallVolume n * ((∑ z ∈ s, a z) * ENNReal.ofReal ((R - M) ^ n)) ≤
        unitBallVolume n * ENNReal.ofReal (R ^ n) :=
      calc unitBallVolume n * ((∑ z ∈ s, a z) * ENNReal.ofReal ((R - M) ^ n))
          = ∑ z ∈ s, a z * (unitBallVolume n * ENNReal.ofReal ((R - M) ^ n)) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => mul_left_comm _ _ _
        _ ≤ ∑ z ∈ s, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
            gcongr with z hz
            exact hplane z hz
        _ ≤ ∑' z : Z, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) :=
            ENNReal.sum_le_tsum s
        _ = ν (ball 0 R) := (hball R).symm
        _ ≤ unitBallVolume n * ENNReal.ofReal (R ^ n) := hνR R (hM.trans_lt hR)
    have hpow : 0 < (R - M) ^ n := pow_pos hRM n
    rwa [ENNReal.mul_le_mul_iff_right hω0 hωtop,
      ← ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hpow).ne')
        (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_div_of_pos hpow, ← div_pow] at hsum
  -- `(R / (R − M))ⁿ → 1` as `R → ∞`
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal ((R / (R - M)) ^ n)) atTop (𝓝 1) := by
    have hsub : Tendsto (fun R : ℝ => R - M) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b + M, fun R hR => by linarith⟩
    have h1 : Tendsto (fun R : ℝ => 1 + M / (R - M)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsub)
    have h2 : Tendsto (fun R : ℝ => R / (R - M)) atTop (𝓝 1) :=
      h1.congr' ((eventually_gt_atTop M).mono fun R hR => by
        rw [← same_add_div (sub_pos.mpr hR).ne', sub_add_cancel])
    simpa using ENNReal.tendsto_ofReal (h2.pow n)
  exact ge_of_tendsto hlim ((eventually_gt_atTop M).mono key)
/-- A finite sum `ν = ∑ᵢ (αᵢ)₊ Hⁿ⌞(wᵢ + V)` of planes parallel to `V`, with offsets `wᵢ ∈ Vᗮ`,
that charges every ball `B_r(0)` has a plane through `0`: some `wᵢ = 0` (used in the proof that
the limit in Simon 7.2.4 is integer multiplicity, Remark 7.2.5(1)).  Otherwise pick
`0 < r < ‖wᵢ‖` for all `i`; for `y ∈ wᵢ + V`, Pythagoras gives `‖y‖² = ‖y - wᵢ‖² + ‖wᵢ‖² > r²`,
so every plane misses `B_r(0)` and `ν(B_r(0)) = 0`. -/
theorem Submission.cbr_ci_cp_fp_exists_offset_eq_zero : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), (∀ i, w i ∈ Vᗮ) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ V} → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → ∃ i, w i = 0 := by
  intro P n ν V N w α hw hν hpos
  by_contra hne
  -- a radius `0 < r < ‖w i‖` for each of the finitely many offsets `w i ≠ 0`
  obtain ⟨r, hr, hrw⟩ : ∃ r : ℝ, 0 < r ∧ ∀ i, r < ‖w i‖ :=
    ((eventually_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0).and
      (eventually_all.2 fun i => nhdsWithin_le_nhds
        (eventually_lt_nhds (norm_pos_iff.2 fun hi => hne ⟨i, hi⟩)))).exists
  -- by Pythagoras (`w i ∈ Vᗮ`), every plane `{y | y - w i ∈ V}` misses `B_r(0)`
  have hmiss : ∀ i, ball (0 : Euclid P) r ∩ {y : Euclid P | y - w i ∈ V} = ∅ := by
    intro i
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hy, ht⟩ => ?_
    rw [mem_ball_zero_iff] at hy
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real
      (Submodule.inner_right_of_mem_orthogonal (show y - w i ∈ V from ht) (hw i))
    rw [sub_add_cancel] at hpyth
    have hlt : ‖y‖ < ‖w i‖ := hy.trans (hrw i)
    nlinarith [norm_nonneg y, mul_self_nonneg ‖y - w i‖]
  -- hence `ν(B_r(0)) = 0`, contradicting the positivity hypothesis
  have hzero : ν (ball 0 r) = 0 := by
    rw [hν, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_ball, hmiss i, measure_empty,
      smul_zero]
  exact (hpos r hr).ne' hzero

/-- Let `ν = Σ_{w ∈ Z} a(w) Hⁿ⌞{y : y − w ∈ V}` be a sum of parallel translates of the `n`-plane
`V`, with offsets `Z ⊆ V^⊥` and weights `a(w) ≥ c > 0`.  If `ν(B_R(0)) ≤ ωₙRⁿ` for all `R > 0`
and `ν(B_r(0)) > 0` for all `r > 0`, then `ν = Σᵢ αᵢ Hⁿ⌞{y : y − wᵢ ∈ V}` for finitely many
distinct `wᵢ ∈ V^⊥` and `αᵢ ≥ c` with `Σᵢ αᵢ ≤ 1` and some `wᵢ = 0` (the constant-plane step
of the closure argument for Simon 7.2.4).  The growth bound gives `Σ_{w ∈ Z} a(w) ≤ 1`, so `Z`
is finite; enumerating `Z` gives the finite sum, and positivity near `0` forces a plane through
`0`. -/
theorem Submission.cbr_ci_cp_finite_parallel_planes : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)) (a : Euclid P → ℝ≥0∞) (c : ℝ), 0 < c → Module.finrank ℝ V = n → Z ⊆ (Vᗮ : Set (Euclid P)) → (∀ w ∈ Z, ENNReal.ofReal c ≤ a w) → ν = Measure.sum (fun w : Z => a w • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → ∃ (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), Injective w ∧ (∀ i, w i ∈ Vᗮ) ∧ (∀ i, c ≤ α i) ∧ ∑ i, α i ≤ 1 ∧ (∃ i, w i = 0) ∧ ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ V} := by
  intro P n ν V Z a c hc hn hZ ha hν hgrowth hpos
  -- the total weight is at most `1`
  have htsum : ∑' w : Z, a w ≤ 1 :=
    Submission.cbr_ci_cp_fp_tsum_weight_le_one P n ν V Z a hn hZ hν hgrowth
  -- every weight is at least `ofReal c ≠ 0`, so `Z` is finite
  have hZfin : Finite Z := by
    by_contra hinf
    have : Infinite Z := not_finite_iff_infinite.1 hinf
    have hle : ∑' _ : Z, ENNReal.ofReal c ≤ ∑' w : Z, a w :=
      ENNReal.tsum_le_tsum fun w => ha w w.2
    rw [ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.2 hc).ne'] at hle
    exact ENNReal.one_ne_top (top_le_iff.1 (hle.trans htsum))
  have : Fintype Z := Fintype.ofFinite Z
  -- every weight is finite
  have hfin : ∀ w : Z, a w ≠ ∞ := fun w =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum w).trans htsum)
  -- enumerate `Z` as `w₁, …, w_N` and put `αᵢ := a(wᵢ)`
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card Z) ≃ Z) := ⟨(Fintype.equivFin Z).symm⟩
  have hw : ∀ i, (e i : Euclid P) ∈ Vᗮ := fun i => hZ (e i).2
  have hνsum : ν = ∑ i, ENNReal.ofReal (a (e i)).toReal •
      (μHE[n]).restrict {y : Euclid P | y - (e i : Euclid P) ∈ V} := by
    rw [hν, Measure.sum_fintype, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [ENNReal.ofReal_toReal (hfin (e i))]
  refine ⟨Fintype.card Z, fun i => e i, fun i => (a (e i)).toReal,
    Subtype.val_injective.comp e.injective, hw,
    fun i => (ENNReal.ofReal_le_iff_le_toReal (hfin (e i))).1 (ha _ (e i).2), ?_,
    Submission.cbr_ci_cp_fp_exists_offset_eq_zero P n ν V (Fintype.card Z) (fun i => e i)
      (fun i => (a (e i)).toReal) hw hνsum hpos, hνsum⟩
  -- `Σᵢ αᵢ = (Σ_{w ∈ Z} a(w)).toReal ≤ 1`
  rw [tsum_fintype] at htsum
  rw [← ENNReal.toReal_sum fun i _ => hfin (e i), e.sum_comp (fun w : Z => a w)]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top htsum).trans_eq ENNReal.toReal_one

/-- **A cycle with constant unit `n`-vector, Euclidean growth and positive lower density is a
finite sum of parallel `n`-planes** (`n = d + 1`; the constant-plane step of the closure theorem
behind Simon 7.2.4, Ch. 6, 3.11).  The cycle condition `∫ ζ₀(dφ) dν = 0` makes `ν` invariant under
translations along a subspace `V` such that `ζ₀(β) = ζ₀(β ∘ p_V)`; the growth bound forces
`dim V ≤ n`, and the normalisation of `ζ₀` then gives `dim V = n` and `ζ₀(β) = β(v)` for an
orthonormal basis `v` of `V`.  Haar uniqueness along `V` writes `ν = (Hⁿ⌞V) ⊗ σ`, the lower density
bound makes `σ` purely atomic with atoms `≥ c`, and the growth bound together with `ν(B_r(0)) > 0`
leaves finitely many planes `V + wᵢ`, `wᵢ ⊥ V`, with total weight `≤ 1`, one of them through `0`. -/
theorem Submission.dmcbr_ci_constant_cycle_planes : ∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (c : ℝ), 0 < c → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = 1) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1))) → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → (∀ᵐ y ∂ν, ENNReal.ofReal c ≤ liminf (fun r : ℝ => ν (ball y r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → ∃ (v : Fin (d + 1) → Euclid P) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), Orthonormal ℝ v ∧ (∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v) ∧ Injective w ∧ (∀ (i : Fin N) (j : Fin (d + 1)), inner ℝ (w i) (v j) = 0) ∧ (∀ i, c ≤ α i) ∧ ∑ i, α i ≤ 1 ∧ (∃ i, w i = 0) ∧ ν = ∑ i, ENNReal.ofReal (α i) • (μHE[(d + 1)]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)} := by
  intro P d ν ζ₀ c hc hfin hnorm hone hcycle hgrowth hpos hdens
  -- the cycle condition: `ν` is invariant under translations along `V`, and `ζ₀` only sees `V`
  obtain ⟨V, hVder, hVann⟩ :=
    Submission.cbr_ci_cp_wedge_annihilator_subspace P d ν ζ₀ hfin hcycle
  have htrans : ∀ u ∈ V, ∀ A : Set (Euclid P), MeasurableSet A →
      ν ((fun x => u + x) ⁻¹' A) = ν A := fun u hu =>
    Submission.cbr_ci_cp_translation_invariant_of_fderiv P ν u hfin (hVder u hu)
  have hproj : ∀ β : Covector (Euclid P) (d + 1),
      ζ₀ β = ζ₀ (β.compContinuousLinearMap V.starProjection) :=
    Submission.cbr_ci_cp_eval_comp_starProjection_eq P d ζ₀ V hVann
  -- the growth bound gives `dim V ≤ n`; the normalisation of `ζ₀` gives `dim V = n`, `ζ₀ = β ↦ β(v)`
  have hωtop : unitBallVolume (d + 1) ≠ ∞ := measure_ball_lt_top.ne
  have hle : Module.finrank ℝ V ≤ d + 1 :=
    Submission.cbr_ci_cp_finrank_le_of_growth P (d + 1) ν V (unitBallVolume (d + 1)) hωtop htrans
      hgrowth (hpos 1 one_pos)
  obtain ⟨hrank, v, hv, hspan, hζ⟩ :=
    Submission.cbr_ci_cp_eval_eq_orthonormal_frame P d ζ₀ V hle hnorm hone hproj
  -- `ν = (Hⁿ⌞V) ⊗ σ` with `σ` carried by countably many atoms `w ∈ V^⊥` of mass `≥ c`
  obtain ⟨σ, hσV, hσfin, hνσ⟩ :=
    Submission.cbr_ci_cp_invariant_measure_product P (d + 1) ν V hrank hfin htrans
  obtain ⟨Z, -, hZ, hZc, hνZ⟩ :=
    Submission.cbr_ci_cp_atomic_transversal P (d + 1) ν σ V c hc hrank hσV hσfin hνσ hdens
  -- finitely many planes, of total weight `≤ 1`, one of them through `0`
  obtain ⟨N, w, α, hinj, hw, hαc, hαsum, hw0, hνw⟩ :=
    Submission.cbr_ci_cp_finite_parallel_planes P (d + 1) ν V Z (fun z => σ {z}) c hc hrank hZ hZc
      hνZ hgrowth hpos
  refine ⟨v, N, w, α, hv, hζ, hinj, fun i j => ?_, hαc, hαsum, hw0, ?_⟩
  · have hvj : v j ∈ V := hspan ▸ Submodule.subset_span (mem_range_self j)
    exact Submodule.inner_left_of_mem_orthogonal hvj (hw i)
  · rw [hspan]
    exact hνw

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
