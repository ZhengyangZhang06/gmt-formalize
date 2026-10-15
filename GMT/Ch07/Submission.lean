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

/-- **Simon Ch. 6, 2.5** (fact (F1) in the proof of Ch. 6, 7.2): `M_G(A − B) ≤ M_G(A) + M_G(B)`.
`M_G(A − B)` is the supremum of `(A − B)(ω)` over the forms `ω ∈ 𝒟ⁿ(U)` admissible for `M_G`
(`spt ω ⊆ G`, `|ω| ≤ 1`).  For such `ω` the form `−ω` is admissible as well, since it has the
same support and pointwise coefficient norm.  As `(A − B)(ω) = A(ω) + B(−ω)` and `ofReal` is
subadditive, `(A − B)(ω)` is bounded by `M_G(A) + M_G(B)`. -/
theorem Submission.cmc_fc_tb_massOn_sub_le : ∀ (P n : ℕ) (U G : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).massOn G ≤ A.massOn G + B.massOn G := by
  intro P n U G A B
  -- Step 1: `M_G(A − B)` is a supremum, so fix an admissible `ω`
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  -- Step 2: `−ω` is admissible (same support, same coefficient norm)
  have hnω : -ω ∈ massAdmissibleOn U n G := by
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
  -- Step 3: `(A − B)(ω) = A(ω) + B(−ω)`
  have hAB : (A - B) ω = A ω + B (-ω) := by
    change A.toCurrent ω - B.toCurrent ω = A.toCurrent ω + B.toCurrent (-ω)
    rw [map_neg B.toCurrent ω, sub_eq_add_neg]
  -- Steps 4–5: subadditivity of `ofReal`, and each admissible value is bounded by the mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hAB]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hnω)
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2
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
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
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
/-- **A mass-summable series of currents converges to a current** (Simon Ch. 6, 3.13; the series
`R^{(ℓ)} = Σ_{r ≥ ℓ} R_r` in the proof of 7.2).  Let `s = Σ_r M(X_r) < ∞`.  If `|ω(x)| ≤ c` for
all `x`, then `|X_r(ω)| ≤ c M(X_r)`, so `Σ_r X_r(ω)` converges absolutely and
`|Σ_r X_r(ω)| ≤ c s`.  Its sum `Y(ω)` is linear in `ω` by uniqueness of sums.  Since
`|ω(x)| ≤ C ‖ω(x)‖`, `Y` has order `0`, so it is a current.  An admissible `ω` has `c = 1`, so
`Y(ω) ≤ s` and `M(Y) ≤ s`. -/
theorem Submission.dimred_mbl_fc_series_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass := by
  intro P n U X hs
  -- Step 1: every `M(X_r)` is finite and `Σ_r M(X_r)` has real sum `s`
  have hfin : ∀ r, (X r).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hs
  have hsum : HasSum (fun r => ((X r).mass).toReal) (∑' r, (X r).mass).toReal := by
    rw [ENNReal.tsum_toReal_eq hfin]
    exact (ENNReal.summable_toReal hs).hasSum
  -- Step 2: if `|ω(x)| ≤ c` for all `x`, then `Σ_r X_r(ω)` converges and `|Σ_r X_r(ω)| ≤ c s`
  have hbound : ∀ (ω : TestFormOn U n) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      Summable (fun r => X r ω) ∧ |∑' r, X r ω| ≤ c * (∑' r, (X r).mass).toReal := by
    intro ω c hc
    have h : ∀ r, ‖X r ω‖ ≤ c * ((X r).mass).toReal := fun r => by
      rw [Real.norm_eq_abs]
      exact Submission.cmr_abs_apply_le_massOn P n U U (X r) ω c (hfin r) ω.property.2 hc
    exact ⟨(hsum.mul_left c).summable.of_norm_bounded h,
      by simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded (hsum.mul_left c) h⟩
  -- Step 3: `|ω(x)| ≤ C ‖ω(x)‖`, and `‖ω(x)‖` is bounded since `ω` has compact support
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  have hnorm : ∀ (ω : TestFormOn U n) (M : ℝ),
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ C * M :=
    fun ω M hM x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0)
  have hsummable : ∀ ω : TestFormOn U n, Summable (fun r => X r ω) := by
    intro ω
    obtain ⟨M, hM⟩ := (ContDiff.continuous ω.property.1.1).bounded_above_of_compact_support
      ω.property.1.2
    exact (hbound ω _ (hnorm ω M hM)).1
  -- Step 4: `L(ω) = Σ_r X_r(ω)` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑' r, X r ω
      map_add' := fun ω ω' => by
        simp only [map_add]
        exact (hsummable ω).tsum_add (hsummable ω')
      map_smul' := fun t ω => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  -- Step 5: `|L(ω)| ≤ C s M` whenever `‖ω(x)‖ ≤ M`, so `L` is a current `Y`
  obtain ⟨Y, hY⟩ := Submission.cmcs_rc_order_zero_current P n U L fun _ _ _ =>
    ⟨C * (∑' r, (X r).mass).toReal, fun ω M _ hM => by
      calc |L ω| = |∑' r, X r ω| := rfl
        _ ≤ C * M * (∑' r, (X r).mass).toReal := (hbound ω _ (hnorm ω M hM)).2
        _ = C * (∑' r, (X r).mass).toReal * M := by ring⟩
  refine ⟨Y, fun ω => ?_, ?_⟩
  · rw [hY ω]
    exact (hsummable ω).hasSum
  -- Step 6: an admissible `ω` has `c = 1`, so `Y(ω) ≤ s` and `M(Y) ≤ s`
  · apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (Y ω) ≤ _
    rw [hY ω]
    apply ENNReal.ofReal_le_of_le_toReal
    have h := (hbound ω 1 hω.2).2
    rw [one_mul] at h
    exact (le_abs_self _).trans h
/-- Helly selection with no concentration on left intervals (the compactness ingredient of the
choice of the slicing level in the proof of Simon 6.7.2, "an argument as in 6.7(2) of Ch. 2"): if
`μⱼ([a, b]) ≤ Λ < ∞`, then along a subsequence `φ` and off a countable set `N`, every
`s ∈ (a, b) \ N` and `ε > 0` admit `δ > 0` with `μ_{φ j}([s - δ, s]) ≤ ε` for all large `j`.
By Tychonoff, `μ_{φ j}([a, d]) → G(d)` for every rational `d ∈ (a, b)`; `N` is the discontinuity
set of the nondecreasing `G̃(t) = sup ({0} ∪ {G(d) : d < t})`, and `[s - δ, s] ⊆ [a, d₂] \ [a, d₁]`
for rationals `d₁ < s - δ`, `s < d₂` with `G(d₂) - G(d₁) < ε`. -/
theorem Submission.cmc_fc_gs_helly_no_concentration : ∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∃ (φ : ℕ → ℕ) (N : Set ℝ), StrictMono φ ∧ N.Countable ∧ ∀ s ∈ Ioo a b, s ∉ N → ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μ (φ j) (Icc (s - δ) s) ≤ ε := by
  intro μ a b Λ hΛ hμ
  -- `μⱼ([a, x]) ≤ μⱼ([a, b]) ≤ Λ < ∞` for `x ≤ b`
  have hle : ∀ j x, x ≤ b → μ j (Icc a x) ≤ Λ := fun j x hx =>
    (measure_mono (Icc_subset_Icc_right hx)).trans (hμ j)
  have hfin : ∀ j x, x ≤ b → μ j (Icc a x) ≠ ∞ := fun j x hx =>
    ((hle j x hx).trans_lt hΛ.lt_top).ne
  -- Helly selection: `d ↦ μⱼ([a, d])` lies in the compact box `∏_{d ∈ ℚ ∩ (a, b)} [0, Λ]` of
  -- the first countable space `ℝ^(ℚ ∩ (a, b))`
  have hK : IsCompact (univ.pi fun _ : {q : ℚ // (q : ℝ) ∈ Ioo a b} => Icc (0 : ℝ) Λ.toReal) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨G, hGK, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun j d => (μ j (Icc a (d.1 : ℝ))).toReal)
    fun j d _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hΛ (hle j _ d.2.2.le)⟩
  have hGd : ∀ d : {q : ℚ // (q : ℝ) ∈ Ioo a b},
      Tendsto (fun j => (μ (φ j) (Icc a (d.1 : ℝ))).toReal) atTop (𝓝 (G d)) :=
    tendsto_pi_nhds.1 hlim
  -- `G` is nondecreasing
  have hGmono : ∀ d d' : {q : ℚ // (q : ℝ) ∈ Ioo a b}, (d.1 : ℝ) ≤ d'.1 → G d ≤ G d' :=
    fun d d' h => le_of_tendsto_of_tendsto' (hGd d) (hGd d') fun j =>
      ENNReal.toReal_mono (hfin _ _ d'.2.2.le) (measure_mono (Icc_subset_Icc_right h))
  -- `G̃(t) = sup ({0} ∪ {G(d) : d < t})`
  obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ → ℝ, ∀ t, Gt t = sSup (insert 0 (G '' {d | (d.1 : ℝ) < t})) :=
    ⟨_, fun _ => rfl⟩
  have hbdd : ∀ t, BddAbove (insert 0 (G '' {d | (d.1 : ℝ) < t})) := fun t =>
    ⟨Λ.toReal, by
      rintro x (rfl | ⟨d, -, rfl⟩)
      exacts [ENNReal.toReal_nonneg, (hGK d (mem_univ d)).2]⟩
  -- (α) `G(d) ≤ G̃(t)` if `d < t`; (β) `G̃(t) ≤ G(d)` if `t < d`
  have hα : ∀ d t, (d.1 : ℝ) < t → G d ≤ Gt t := fun d t h => by
    rw [hGt]
    exact le_csSup (hbdd t) (mem_insert_of_mem _ ⟨d, h, rfl⟩)
  have hβ : ∀ d t, t < (d.1 : ℝ) → Gt t ≤ G d := fun d t h => by
    rw [hGt]
    refine csSup_le (insert_nonempty _ _) ?_
    rintro x (rfl | ⟨d', hd', rfl⟩)
    exacts [(hGK d (mem_univ d)).1, hGmono d' d (lt_trans hd' h).le]
  have hmono : Monotone Gt := fun t t' h => by
    rw [hGt, hGt]
    exact csSup_le_csSup (hbdd t') (insert_nonempty _ _)
      (insert_subset_insert (image_mono fun d hd => lt_of_lt_of_le hd h))
  -- `N` is the countable set of discontinuities of the monotone `G̃`
  refine ⟨φ, {t | ¬ContinuousAt Gt t}, hφ, hmono.countable_not_continuousAt, ?_⟩
  intro s hs hsN ε hε
  have hcont : ContinuousAt Gt s := by
    by_contra h
    exact hsN h
  rcases eq_or_ne ε ∞ with rfl | hε'
  · exact ⟨1, one_pos, Eventually.of_forall fun _ => le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε'
  obtain ⟨η₀, hη₀, hcη⟩ := Metric.continuousAt_iff.1 hcont (ε.toReal / 2) (half_pos he)
  -- `δ = η = min (η₀ / 3, (s - a) / 3, (b - s) / 2)`
  obtain ⟨hsa, hsb⟩ := hs
  set η := min (η₀ / 3) (min ((s - a) / 3) ((b - s) / 2))
  have h1 : η ≤ η₀ / 3 := min_le_left _ _
  have h2 : η ≤ (s - a) / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : η ≤ (b - s) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hη : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  -- rationals `d₁ ∈ (s - 2η, s - η)` and `d₂ ∈ (s, s + η)`, both in `(a, b)`
  obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn (show s - 2 * η < s - η by linarith)
  obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn (show s < s + η by linarith)
  have hd₁ : (q₁ : ℝ) ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hd₂ : (q₂ : ℝ) ∈ Ioo a b := ⟨by linarith, by linarith⟩
  -- `G(d₂) - G(d₁) ≤ G̃(s + η) - G̃(s - 2η) < ε`
  have hup := @hcη (s + η) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hdown := @hcη (s - 2 * η) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at hup hdown
  have hlt : G ⟨q₂, hd₂⟩ - G ⟨q₁, hd₁⟩ < ε.toReal := by
    have := hα ⟨q₂, hd₂⟩ (s + η) hq₂'
    have := hβ ⟨q₁, hd₁⟩ (s - 2 * η) hq₁
    linarith [hup.2, hdown.1]
  -- `μ_{φ j}([s - η, s]) ≤ μ_{φ j}([a, d₂] \ [a, d₁])`, which tends to `G(d₂) - G(d₁) < ε`
  refine ⟨η, hη, (((hGd ⟨q₂, hd₂⟩).sub (hGd ⟨q₁, hd₁⟩)).eventually_lt_const hlt).mono
    fun j hj => ?_⟩
  have hsub : Icc (s - η) s ⊆ Icc a (q₂ : ℝ) \ Icc a (q₁ : ℝ) := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨⟨by linarith, by linarith⟩, fun hx => by linarith [hx.2]⟩
  calc μ (φ j) (Icc (s - η) s) ≤ μ (φ j) (Icc a (q₂ : ℝ) \ Icc a (q₁ : ℝ)) := measure_mono hsub
    _ = μ (φ j) (Icc a (q₂ : ℝ)) - μ (φ j) (Icc a (q₁ : ℝ)) :=
      measure_sdiff (Icc_subset_Icc_right (by linarith)) measurableSet_Icc.nullMeasurableSet
        (hfin _ _ hd₁.2.le)
    _ = ENNReal.ofReal ((μ (φ j) (Icc a (q₂ : ℝ))).toReal - (μ (φ j) (Icc a (q₁ : ℝ))).toReal) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin _ _ hd₂.2.le),
        ENNReal.ofReal_toReal (hfin _ _ hd₁.2.le)]
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hj.le
    _ = ε := ENNReal.ofReal_toReal hε'
/-- **Simon 7.2.4, proof** (choice of a good slice; Tonelli for the sliding window): for an
s-finite measure `ν` on `ℝ` and `h ∈ ℝ`, `t ↦ ν((t − h, t))` is measurable and
`∫ ν((t − h, t)) dt = h₊ · ν(ℝ)`, where `h₊ = max h 0`.  The set
`E = {(t, x) : t − h < x < t}` is measurable, its `t`-sections are `(t − h, t)` and its
`x`-sections are `(x, x + h)`; computing `(L¹ ⊗ ν)(E)` in both orders gives the identity. -/
theorem Submission.cmc_fc_gs_aqf_window_lintegral : ∀ (ν : Measure ℝ) [SFinite ν] (h : ℝ), Measurable (fun t : ℝ => ν (Ioo (t - h) t)) ∧ ∫⁻ t, ν (Ioo (t - h) t) ∂volume = ENNReal.ofReal h * ν univ := by
  intro ν _ h
  -- the window set `E = {(t, x) : t - h < x < t}` and its two families of sections
  set E : Set (ℝ × ℝ) := {p | p.1 - h < p.2} ∩ {p | p.2 < p.1} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt (measurable_fst.sub_const h) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hsec : ∀ t : ℝ, Prod.mk t ⁻¹' E = Ioo (t - h) t := fun t => rfl
  have hsec' : ∀ x : ℝ, (fun t => (t, x)) ⁻¹' E = Ioo x (x + h) := by
    intro x
    ext t
    simp only [hE, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  refine ⟨?_, ?_⟩
  · simpa only [hsec] using measurable_measure_prodMk_left (ν := ν) hEm
  · -- Tonelli in both orders for `L¹ ⊗ ν` on `E`, then `L¹((x, x + h)) = h₊`
    calc ∫⁻ t, ν (Ioo (t - h) t) ∂volume = (volume.prod ν) E := by
          rw [Measure.prod_apply hEm]
          simp only [hsec]
      _ = ∫⁻ x, volume (Ioo x (x + h)) ∂ν := by
          rw [Measure.prod_apply_symm hEm]
          simp only [hsec']
      _ = ENNReal.ofReal h * ν univ := by
          simp only [Real.volume_Ioo, add_sub_cancel_left, lintegral_const]

/-- **Double Fatou for left window quotients.**  If `ν_j(ℝ) ≤ Λ < ∞` for all `j`, then for
a.e. `t`, `liminf_j liminf_n Q_{j,n}(t) < ∞`, where `Q_{j,n}(t) = (n + 1) ν_j((t - 1/(n+1), t))`.
By the window lemma `∫⁻ Q_{j,n} = (n + 1) · (1/(n+1)) · ν_j(ℝ) = ν_j(ℝ) ≤ Λ`; Fatou's lemma in
`n` and then in `j` bounds the integral of the iterated `liminf` by `Λ`, and a measurable
`[0, ∞]`-valued function with finite integral is finite a.e. -/
theorem Submission.cmc_fc_gs_aqf_ae_seq_liminf_finite : ∀ (ν : ℕ → Measure ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, ν j univ ≤ Λ) → ∀ᵐ t ∂(volume : Measure ℝ), liminf (fun j => liminf (fun n : ℕ => ((n : ℝ≥0∞) + 1) * ν j (Ioo (t - 1 / ((n : ℝ) + 1)) t)) atTop) atTop ≠ ∞ := by
  intro ν Λ hΛ hν
  -- each `ν j` has total mass at most `Λ < ∞`, so it is finite (hence s-finite)
  have hfin : ∀ j, IsFiniteMeasure (ν j) := fun j => ⟨(hν j).trans_lt hΛ.lt_top⟩
  -- the window quotients `Q j n t = (n + 1) ν_j((t - 1/(n+1), t))` are measurable
  set Q : ℕ → ℕ → ℝ → ℝ≥0∞ := fun j n t =>
    ((n : ℝ≥0∞) + 1) * ν j (Ioo (t - 1 / ((n : ℝ) + 1)) t)
  have hQm : ∀ j n, Measurable (Q j n) := fun j n =>
    (Submission.cmc_fc_gs_aqf_window_lintegral (ν j) (1 / ((n : ℝ) + 1))).1.const_mul _
  -- `(n + 1) · ofReal (1/(n+1)) = 1`
  have hnorm : ∀ n : ℕ, ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) = 1 := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [one_div, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_add n.cast_nonneg zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  -- `∫⁻ Q j n = ν_j(ℝ)` by the window lemma
  have hQint : ∀ j n, ∫⁻ t, Q j n t = ν j univ := by
    intro j n
    obtain ⟨hm, hint⟩ := Submission.cmc_fc_gs_aqf_window_lintegral (ν j) (1 / ((n : ℝ) + 1))
    show ∫⁻ t, ((n : ℝ≥0∞) + 1) * ν j (Ioo (t - 1 / ((n : ℝ) + 1)) t) = ν j univ
    rw [lintegral_const_mul _ hm, hint, ← mul_assoc, hnorm, one_mul]
  -- first Fatou: `∫⁻ liminf_n Q j n ≤ liminf_n ν_j(ℝ) = ν_j(ℝ) ≤ Λ`
  have hqm : ∀ j, Measurable fun t => liminf (fun n => Q j n t) atTop :=
    fun j => Measurable.liminf (hQm j)
  have hqint : ∀ j, ∫⁻ t, liminf (fun n => Q j n t) atTop ≤ Λ := by
    intro j
    calc ∫⁻ t, liminf (fun n => Q j n t) atTop
        ≤ liminf (fun n => ∫⁻ t, Q j n t) atTop := lintegral_liminf_le (hQm j)
      _ = ν j univ := by simp_rw [hQint j]; exact liminf_const _
      _ ≤ Λ := hν j
  -- second Fatou: `∫⁻ liminf_j liminf_n Q j n ≤ liminf_j Λ = Λ`
  have hFm : Measurable fun t => liminf (fun j => liminf (fun n => Q j n t) atTop) atTop :=
    Measurable.liminf hqm
  have hFint : ∫⁻ t, liminf (fun j => liminf (fun n => Q j n t) atTop) atTop ≤ Λ :=
    calc ∫⁻ t, liminf (fun j => liminf (fun n => Q j n t) atTop) atTop
        ≤ liminf (fun j => ∫⁻ t, liminf (fun n => Q j n t) atTop) atTop := lintegral_liminf_le hqm
      _ ≤ liminf (fun _ : ℕ => Λ) atTop := liminf_le_liminf (Eventually.of_forall hqint)
      _ = Λ := liminf_const Λ
  -- a measurable function with finite integral is finite a.e.
  filter_upwards [ae_lt_top hFm (ne_top_of_le_ne_top hΛ hFint)] with t ht
  exact ht.ne
/-- **Simon 7.2.4, good slices** (comparison of difference quotients): for `a < t < b`,
`liminf_{h ↓ 0} h⁻¹ μ((t − h, t)) ≤ liminf_n (n + 1) (μ⌞[a, b])((t − 1/(n + 1), t))`.  Along
`hₙ = 1/(n + 1) → 0⁺` the liminf can only grow; once `hₙ < t − a` the window `(t − hₙ, t)` lies in
`[a, b]`, where `μ⌞[a, b]` agrees with `μ`, and `ofReal hₙ⁻¹ = n + 1`. -/
theorem Submission.cmc_fc_gs_aqf_liminf_le_seq : ∀ (μ : Measure ℝ) (a b t : ℝ), t ∈ Ioo a b → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (Ioo (t - h) t)) (𝓝[>] 0) ≤ liminf (fun n : ℕ => ((n : ℝ≥0∞) + 1) * (μ.restrict (Icc a b)) (Ioo (t - 1 / ((n : ℝ) + 1)) t)) atTop := by
  intro μ a b t ht
  -- `hₙ = 1/(n + 1) → 0` through positive values
  have hv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  refine (hv.liminf_le_liminf_comp
    (u := fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (Ioo (t - h) t))).trans_eq (liminf_congr ?_)
  -- eventually `hₙ < t − a`, so the window lies in `[a, b]`
  filter_upwards [(tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _
    (sub_pos.2 ht.1)] with n hn
  have hsub : Ioo (t - 1 / ((n : ℝ) + 1)) t ⊆ Icc a b := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩
  simp only [Function.comp_apply]
  rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 hsub, one_div, inv_inv,
    ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- **Simon 7.2.4, good slices** (a.e. finiteness of the lower difference quotients): if
`μ_j([a, b]) ≤ Λ < ∞` for all `j`, then for a.e. `t ∈ (a, b)`,
`liminf_j liminf_{h ↓ 0} h⁻¹ μ_j((t − h, t)) < ∞`.  The restrictions `ν_j = μ_j⌞[a, b]` have
total mass `μ_j([a, b]) ≤ Λ`, so by double Fatou `liminf_j liminf_n (n + 1) ν_j((t − hₙ, t))`,
`hₙ = 1/(n + 1)`, is finite for a.e. `t`; for `a < t < b` it dominates the quotient above. -/
theorem Submission.dimred_mbl_fc_gs_ae_quotient_finite : ∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ j (Ioo (t - h) t)) (𝓝[>] 0)) atTop ≠ ∞ := by
  intro μ a b Λ hΛ hμ
  -- the restrictions `ν_j = μ_j⌞[a, b]` have total mass `μ_j([a, b]) ≤ Λ`
  have hν : ∀ j, (μ j).restrict (Icc a b) univ ≤ Λ := fun j => by
    rw [Measure.restrict_apply_univ]
    exact hμ j
  -- double Fatou for `ν_j`, then `S_j(t) ≤ q_j(t)` on `(a, b)` and monotonicity of `liminf_j`
  filter_upwards [Submission.cmc_fc_gs_aqf_ae_seq_liminf_finite
    (fun j => (μ j).restrict (Icc a b)) Λ hΛ hν] with t ht hta
  exact ne_top_of_le_ne_top ht (liminf_le_liminf (Eventually.of_forall fun j =>
    Submission.cmc_fc_gs_aqf_liminf_le_seq (μ j) a b t hta))

/-- **Choice of a good slicing level** for the flat convergence of the moving blow-ups (Simon
Ch. 6, proof of Theorem 7.2, chapter-06.txt line 2090: "by 4.5(1),(2) and an argument as in
6.7(2) of Ch. 2").  If `μⱼ([a, b]) ≤ Λ < ∞`, there are `s ∈ (a, b)`, a subsequence `φ` and
`C < ∞` such that every lower left difference quotient `liminf_{h↓0} h⁻¹ μ_{φ(j)}((s − h, s))` is
`≤ C` and, for every `ε > 0`, eventually `μ_{φ(j)}([s − δ, s]) ≤ ε` for some `δ > 0`.  Helly
selection gives `φ₁` and a countable set `N` off which no mass concentrates from the left along
`φ₁`; Tonelli and Fatou, applied to `μ ∘ φ₁`, give
`L(t) := liminf_j liminf_{h↓0} h⁻¹ μ_{φ₁(j)}((t − h, t)) < ∞` for a.e. `t ∈ (a, b)`.  As `(a, b)`
has positive Lebesgue measure and `N` is null, some `s ∈ (a, b) ∖ N` has `L(s) < ∞`; the
quotients at `s` are `< L(s) + 1 =: C` for infinitely many `j`, which gives a second extraction
`φ₂`, and `φ := φ₁ ∘ φ₂`. -/
theorem Submission.dimred_mbl_fc_good_slice : ∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), a < b → Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∃ (s : ℝ) (φ : ℕ → ℕ) (C : ℝ≥0∞), a < s ∧ s < b ∧ StrictMono φ ∧ C ≠ ∞ ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (φ j) (Ioo (s - h) s)) (𝓝[>] 0) ≤ C) ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μ (φ j) (Icc (s - δ) s) ≤ ε := by
  intro μ a b Λ hab hΛ hμ
  -- Steps 0–3: Helly selection; off the countable set `N` no mass concentrates along `φ₁`
  obtain ⟨φ₁, N, hφ₁, hN, hconc⟩ := Submission.cmc_fc_gs_helly_no_concentration μ a b Λ hΛ hμ
  -- Step 4: Tonelli and Fatou for the subsequence `μ ∘ φ₁`, which is still bounded by `Λ`
  have hfin := Submission.dimred_mbl_fc_gs_ae_quotient_finite (fun j => μ (φ₁ j)) a b Λ hΛ
    fun j => hμ (φ₁ j)
  -- Step 5: `(a, b)` is not Lebesgue-null and `N` is, so a good level `s ∈ (a, b) ∖ N` exists
  have hab' : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have := ae_restrict_neBot.2 hab'
  obtain ⟨s, hs, hsN, hL⟩ := ((ae_restrict_mem (s := Ioo a b) measurableSet_Ioo).and
    (ae_restrict_of_ae ((hN.ae_notMem volume).and hfin))).exists
  -- Step 6: the quotients at `s` are `< L + 1` infinitely often; extract `φ₂` along them
  obtain ⟨φ₂, hφ₂, hlt⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt (by isBoundedDefault) (ENNReal.lt_add_right (hL hs) one_ne_zero))
  refine ⟨s, φ₁ ∘ φ₂, _, hs.1, hs.2, hφ₁.comp hφ₂,
    ENNReal.add_ne_top.2 ⟨hL hs, ENNReal.one_ne_top⟩, fun k => (hlt k).le, fun ε hε => ?_⟩
  -- Steps 7–8: the `δ` of Helly selection works along `φ₁ ∘ φ₂`, since `φ₂ → ∞`
  obtain ⟨δ, hδ, hev⟩ := hconc s hs hsN ε hε
  exact ⟨δ, hδ, hφ₂.tendsto_atTop.eventually hev⟩
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
/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors
(alternating maps agreeing on distinct basis vectors are equal), so
`Φ α = (α(e ∘ I))_{I : Fin n → Fin P}` is an injective linear map into the finite-dimensional
space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.lcn_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `Φ α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `Φ α = Φ β` makes `α` and `β` agree on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective Φ fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then for every
`n`-covector `α`, `⟨α, ξ⟩ = 0` `Hⁿ`-a.e. on `M ∩ W`.  Let `ν = Hⁿ⌞(M ∩ closure W)`; then
`f = θ ⟨α, ξ⟩` is `ν`-integrable (`lcn_mult_mul_orient_apply_integrableOn`, `closure W` being a
compact subset of `U`).  For smooth `g` with compact support in `W`, `ω = g α` is a test form in
`U` supported in `W`, so `0 = T(ω) = ∫_M θ ⟨g α, ξ⟩ dHⁿ = ∫ g f dν` (`g = 0` off `W`).  The
fundamental lemma of the calculus of variations on `W` gives `f = 0` `ν`-a.e. on `W`; as
`Hⁿ⌞(M ∩ W) ≤ ν` and `θ > 0` on `M`, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. -/
theorem Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW α
  -- `f = θ ⟨α, ξ⟩` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
  have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ closure W)) :=
    Submission.lcn_mult_mul_orient_apply_integrableOn P n U (closure W) R hWc hWU α
  -- fundamental lemma on the open set `W`: `f = 0` `ν`-a.e. on `W`
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ closure W)), x ∈ W →
      (R.mult x : ℝ) * R.orient x α = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
    -- `ω = g α` is a test form in `U` supported in `W`, so `T(ω) = 0`
    have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
    have hω : (fun x => g x • α) ∈ TestFormOn U n :=
      ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
    calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[n].restrict (R.carrier ∩ closure W))
        = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          congr 1
          funext x
          rw [map_smul, smul_eq_mul, smul_eq_mul]
          ring
      -- `g = 0` off `closure W`, so the integral over `M` is the integral over `M ∩ closure W`
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
            inter_subset_left fun x hx => ?_).symm
          have hgx : g x = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩
          rw [hgx, zero_smul, map_zero, mul_zero]
      _ = T ⟨_, hω⟩ := (hRT ⟨_, hω⟩).symm
      _ = 0 := hTW ⟨_, hω⟩ hωW
  -- pass to `Hⁿ⌞(M ∩ W) ≤ ν` and cancel `θ > 0` on `M`
  have hle : μHE[n].restrict (R.carrier ∩ W) ≤ μHE[n].restrict (R.carrier ∩ closure W) :=
    Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
  filter_upwards [ae_mono hle hae,
    ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)] with x hx hxMW
  have hθ : (R.mult x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne'
  exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left hθ

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then
`Hⁿ(M ∩ W) = 0`.  `Λⁿ` is finite-dimensional (`lcn_covector_finiteDimensional`); for each `α` of
a basis, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. (`lcn_orient_apply_ae_eq_zero_of_vanishesOn`), so
`ξ = 0` `Hⁿ⌞(M ∩ W)`-a.e.  But `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, hence nonzero
(`imsupp_unit_orientation_ne_zero_norm_le_one`), so `Hⁿ⌞(M ∩ W) = 0`. -/
theorem Submission.imrep_carrier_inter_null_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μHE[n] (R.carrier ∩ W) = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ`
  have := Submission.lcn_covector_finiteDimensional P n
  let b := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `⟨αₖ, ξ⟩ = 0` for every `k`, `Hⁿ⌞(M ∩ W)`-a.e.
  have h0 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ k, R.orient x (b k) = 0 :=
    ae_all_iff.mpr fun k =>
      Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWc hWU hTW (b k)
  -- `ξ ≠ 0` `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ W)`-a.e.
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x ≠ 0 := by
    refine ae_mono (Measure.restrict_mono inter_subset_left le_rfl) ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a functional on `Λⁿ` vanishing on a basis is zero, so `Hⁿ⌞(M ∩ W)`-a.e. `x` is impossible
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), False := by
    filter_upwards [h0, h1] with x hx hne
    exact hne (ContinuousLinearMap.coe_injective (b.ext fun k => hx k))
  exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` in `U`, then `Hⁿ(M ∖ spt T) = 0`, i.e.
`μ_T(U ∖ spt T) = 0`.  As `M ⊆ U` and `spt T = U ∖ Z`, `M ∖ spt T ⊆ M ∩ Z`, where the zero region
`Z = ⋃ 𝒲` is the union of the open `W ⊂⊂ U` on which `T` vanishes.  `ℝᴾ` is second countable, so
`Z = ⋃_{W ∈ 𝒮} W` for a countable `𝒮 ⊆ 𝒲`; each `Hⁿ(M ∩ W) = 0`
(`imrep_carrier_inter_null_of_vanishesOn`), and countable subadditivity concludes. -/
theorem Submission.imrep_carrier_sdiff_support_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
  intro P n U T R _ hRT
  -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
  obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- `M ∖ spt T ⊆ ⋃_{W ∈ 𝒮} M ∩ W`: a point of `M ⊆ U` outside `spt T = U ∖ Z` lies in `Z`
  have hsub : R.carrier \ T.support ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
    rintro x ⟨hxM, hxS⟩
    have hxZ : x ∈ ⋃₀ 𝒮 := by
      rw [h𝒮]
      by_contra hxZ
      exact hxS (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
    exact mem_biUnion hW ⟨hxM, hxW⟩
  -- `Hⁿ(M ∩ W) = 0` for each of the countably many `W ∈ 𝒮`
  refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
  obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
  exact Submission.imrep_carrier_inter_null_of_vanishesOn P n U W T R hRT hWo hWc hWU hTW
/-- **Simon Ch. 3, 1.4**: approximate tangent planes are local and do not see `Hⁿ`-null
modifications.  If `M' ⊆ M`, `V` is open, `x ∈ V` and `Hⁿ((M \ M') ∩ V) = 0`, then an
approximate tangent plane of `M` at `x` is one of `M'`.  Given `f ∈ C_c(ℝᴾ)`, take
`B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`.  For `0 < r < s / L` the parts of `η_{x,r}(M)` and
`η_{x,r}(M')` in `B_L(0)` differ inside `η_{x,r}((M \ M') ∩ V)`, which is `Hⁿ`-null because
`η_{x,r}` is Lipschitz.  So the blow-up integrals agree for small `r` and have the same limit. -/
theorem Submission.dtc_approxTangent_of_null_diff : ∀ (P n : ℕ) (M M' V : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), M' ⊆ M → IsOpen V → x ∈ V → μHE[n] ((M \ M') ∩ V) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' V x Q hMM' hV hxV hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV x hxV
  obtain ⟨L, hL, hfL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  -- the blow-up integrals of `M` and `M'` agree for `0 < r < s / L`, so they have the same limit
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
  have hr0 : 0 < r := hr.1
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη]
  -- `f` vanishes off `B_L(0)`, so every set integral may be cut to `B_L(0)`
  have hfB : ∀ y, y ∉ ball (0 : Euclid P) L → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfL h)
  have hcut : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) L ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hfB).symm
  -- `η_{x,r}` is `r⁻¹`-Lipschitz, so it maps the `Hⁿ`-null set `(M \ M') ∩ V` to a null set
  have hnullimg : μHE[n] ((fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V)) = 0 := by
    have hlip : LipschitzWith ‖r⁻¹‖₊ (fun y : Euclid P => r⁻¹ • (y - x)) :=
      LipschitzWith.of_dist_le_mul fun a b =>
        le_of_eq (by rw [dist_smul₀, dist_sub_right, coe_nnnorm])
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul] at hnull ⊢
    have hH : μH[(n : ℝ)] ((M \ M') ∩ V) = 0 := by
      simpa [Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n] using hnull
    have hle := hlip.hausdorffMeasure_image_le (Nat.cast_nonneg n) ((M \ M') ∩ V)
    rw [hH, mul_zero, nonpos_iff_eq_zero] at hle
    rw [hle, mul_zero]
  -- in `B_L(0)`, `η_{x,r}(M)` and `η_{x,r}(M')` differ inside `η_{x,r}((M \ M') ∩ V)`
  have hsub : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) \
      (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M') ⊆
      (fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V) := by
    rintro y ⟨⟨hyB, ⟨z, hz, rfl⟩⟩, hy'⟩
    refine ⟨z, ⟨⟨hz, fun hz' => hy' ⟨hyB, z, hz', rfl⟩⟩, hsV ?_⟩, rfl⟩
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
      inv_mul_lt_iff₀ hr0] at hyB
    have hrL := (lt_div_iff₀ hL).mp hr.2
    rw [mem_ball, dist_eq_norm]
    linarith
  -- hence the two parts are `Hⁿ`-a.e. equal (`M' ⊆ M` gives the other inclusion)
  have hae : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M' : Set (Euclid P))
      =ᵐ[μHE[n]] (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.mpr (inter_subset_inter_right _ (image_mono hMM'))]
      exact measure_empty
    · exact measure_mono_null hsub hnullimg
  rw [hcut, hcut ((fun y : Euclid P => r⁻¹ • (y - x)) '' M'), Measure.restrict_congr_set hae]

/-- **Simon Ch. 6, 3.1 and 2.16** (with Ch. 3, 1.4): if `T = τ(M, θ, ξ)` is integer multiplicity
in `U` and `V ⊆ U` is open, then `T⌞V = τ(M ∩ V, θ, ξ)` is integer multiplicity in `V`.  The
restricted triple inherits measurability, rectifiability, positivity and local integrability from
`(M, θ, ξ)`.  At `Hⁿ`-a.e. `x ∈ M ∩ V` the approximate tangent space of `M` is also that of
`M ∩ V`, as the removed set `M ∖ (M ∩ V)` misses the open set `V ∋ x`
(`dtc_approxTangent_of_null_diff`).  A test form supported in `V` vanishes on `M ∖ V`, so its
integrals over `M` and over `M ∩ V` agree.  Openness of `U` is not used. -/
theorem Submission.dtc_restrictDomain_isIntegerMultiplicity : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n), IsOpen V → IsIntegerMultiplicity T → IsIntegerMultiplicity (T.restrictDomain hVU) := by
  rintro P n U V hVU T hV ⟨R, hR⟩
  -- Step 1: `M ∩ V` is Borel
  have hMV : MeasurableSet (R.carrier ∩ V) := R.measurableSet_carrier.inter hV.measurableSet
  -- the restricted triple `R' = (M ∩ V, θ, ξ)` in `V`
  let R' : IMRep V n :=
    { carrier := R.carrier ∩ V
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := hMV
      -- Step 2: `M ∩ V ⊆ V`
      carrier_subset := inter_subset_right
      -- Step 3: a subset of a countably `n`-rectifiable set is countably `n`-rectifiable
      rectifiable := R.rectifiable.mono inter_subset_left
      -- Step 4: `θ` is measurable, and positive on `M ∩ V ⊆ M`
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- Step 5: for compact `K ⊆ V`, `(M ∩ V) ∩ K = M ∩ K` and `K ⊆ V ⊆ U`
      locallyIntegrable_mult := fun K hK hKV => by
        rw [inter_assoc, inter_eq_right.2 hKV]
        exact R.locallyIntegrable_mult K hK (hKV.trans hVU)
      -- Step 6: `Hⁿ⌞(M ∩ V) ≤ Hⁿ⌞M`
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
      -- Step 7: at `Hⁿ⌞(M ∩ V)`-a.e. `x`, the plane `Q` oriented by `ξ(x)` stays the approximate
      -- tangent space, since `(M ∖ (M ∩ V)) ∩ V = ∅`
      orients := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          (inter_subset_left : R.carrier ∩ V ⊆ R.carrier) R.orients, ae_restrict_mem hMV]
          with x hx hxMV
        obtain ⟨Q, hQ, hξQ⟩ := hx
        have hnull : μHE[n] ((R.carrier \ (R.carrier ∩ V)) ∩ V) = 0 := by
          rw [sdiff_self_inter, sdiff_inter_self, measure_empty]
        exact ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier (R.carrier ∩ V) V x Q
          inter_subset_left hV hxMV.2 hnull hQ, hξQ⟩ }
  -- Step 8: `T⌞V(ω) = T(ιω) = ∫_M θ⟨ω, ξ⟩ dHⁿ = ∫_{M ∩ V} θ⟨ω, ξ⟩ dHⁿ`, as `ω = 0` off `V`
  refine ⟨R', fun ω => ?_⟩
  rw [GeometricCurrentOn.restrictDomain_apply, hR, testFormOnInclusion_coe]
  change ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n] =
    ∫ x in R.carrier ∩ V, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
    inter_subset_left fun x hx => ?_
  have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) n) :=
    fun h => hx.2 ⟨hx.1, ω.property.2 h⟩
  rw [image_eq_zero_of_notMem_tsupport hxω, map_zero, mul_zero]
/-- **An integer multiplicity triple essentially carried by a compact set moves to any domain
containing it** (step 6.6 of the localization in the proof of Simon 7.3.1; Simon 6.3.1,
chapter-06.txt lines 733–753).  If `R = (M, θ, ξ)` is an `IMRep` in `V`, `K ⊆ V ∩ U` is compact
and `Hⁿ(M \ K) = 0`, then `(M ∩ K, θ, ξ)` is an `IMRep` in `U` with the same action: `M ∩ K` and
`M` differ by the `Hⁿ`-null set `M \ K`, so `Hⁿ⌞(M ∩ K) = Hⁿ⌞M`; `∫_{M ∩ K} θ dHⁿ < ∞` since
`K ⊆ V` is compact; and `M ∩ K` has the approximate tangent planes of `M`
(`dtc_approxTangent_of_null_diff` with the open set `ℝᴾ`). -/
theorem Submission.dtc_imrep_of_null_off_compact : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (R : IMRep V n), IsCompact K → K ⊆ V → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → ∃ R' : IMRep U n, R'.carrier ⊆ K ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action ω := by
  intro P n U V K R hK hKV hKU hnull
  have hsub : R.carrier ∩ K ⊆ R.carrier := inter_subset_left
  have hdiff : R.carrier \ (R.carrier ∩ K) = R.carrier \ K := Set.sdiff_self_inter
  -- `M ∩ K =ᵐ M`: `(M ∩ K) \ M = ∅` and `M \ (M ∩ K) = M \ K` is `Hⁿ`-null.
  have hrestr : μHE[n].restrict (R.carrier ∩ K) = μHE[n].restrict R.carrier := by
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, hdiff ▸ hnull⟩)
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  refine ⟨
    { carrier := R.carrier ∩ K
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hK.isClosed.measurableSet
      carrier_subset := inter_subset_right.trans hKU
      rectifiable := R.rectifiable.mono hsub
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- `∫_{(M ∩ K) ∩ C} θ ≤ ∫_{M ∩ K} θ < ∞`, using only that `K ⊆ V` is compact.
      locallyIntegrable_mult := fun _ _ _ => ne_top_of_le_ne_top
        (R.locallyIntegrable_mult K hK hKV) (lintegral_mono_set inter_subset_left)
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hsub le_rfl)
      -- a.e. on `M ∩ K`, the plane `Q` oriented by `ξ(x)` is also `Tₓ(M ∩ K)`.
      orients := (ae_restrict_of_ae_restrict_of_subset hsub R.orients).mono
        fun x ⟨Q, hQ, hξ⟩ => ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier
          (R.carrier ∩ K) univ x Q hsub isOpen_univ (mem_univ x)
          (by rw [inter_univ, hdiff]; exact hnull) hQ, hξ⟩ },
    inter_subset_right, fun ω => ?_⟩
  -- the actions are integrals of the same function against the same measure
  change ∫ x in R.carrier ∩ K, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] =
    ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]
  rw [hrestr]
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

/-- **Extension by zero** (steps 6.2–6.6 of the localization in the proof of Simon 7.3.1).  Let
`V ⊆ U` be open, `K ⊆ V` compact and `X = τ(M, θ, ξ) ∈ 𝒟ₙ(V)` with `Hⁿ(M \ K) = 0`.  Move the
representation to `U` with carrier in `K` and let `Y ∈ 𝒟ₙ(U)` be the current it defines.  Then
`Y⌞V = X`; `Y` kills every form whose support misses `K`, so `spt Y = K \ Z_Y` is a compact subset
of `K`; and if `∂X = 0`, then for a cutoff `χ ∈ C^∞_c(V)` equal to `1` near `K` we get
`∂Y(ω) = Y(dω) = X(d(χω)) = ∂X(χω) = 0`, since `d(χω) = dω` near the carrier. -/
theorem Submission.dtc_extend_by_zero : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (hVU : V ⊆ U) (X : GeometricCurrentOn V n) (R : IMRep V n), IsOpen U → IsOpen V → IsCompact K → K ⊆ V → R.Represents X → μHE[n] (R.carrier \ K) = 0 → ∃ Y : GeometricCurrentOn U n, Y.restrictDomain hVU = X ∧ Y.support ⊆ K ∧ IsCompact Y.support ∧ (BoundaryVanishes X → BoundaryVanishes Y) ∧ IsIntegerMultiplicity Y := by
  intro P n U V K hVU X R hU hV hK hKV hRX hnull
  -- Step 1: move `R` to `U`, with carrier in `K` and the same action
  obtain ⟨R', hR'K, hR'R⟩ :=
    Submission.dtc_imrep_of_null_off_compact P n U V K R hK hKV (hKV.trans hVU) hnull
  -- Step 2: `Y = τ(R')`, which is integer multiplicity
  obtain ⟨Y, hY⟩ := Submission.dtc_imrep_current P n U R'
  -- Step 4: `Y` vanishes on forms whose support misses `K`
  have hvan : ∀ ω : TestFormOn U n,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω, IMRep.action]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.mp hω (hR'K hx)), map_zero,
      mul_zero]
  -- Step 5: `spt Y ⊆ K`; a point of `U \ K` has a ball `W ⊂⊂ U \ K` on which `Y` vanishes
  have hspt : Y.support ⊆ K := by
    rintro q ⟨hqU, hqZ⟩
    by_contra hqK
    obtain ⟨r, hr, hrUK⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) q ⟨hqU, hqK⟩
    have hcl : closure (ball q (r / 2)) ⊆ ball q r :=
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hr))
    refine hqZ (mem_sUnion.mpr ⟨ball q (r / 2), ⟨isOpen_ball,
      (isCompact_closedBall q (r / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall,
      hcl.trans (hrUK.trans sdiff_subset), fun ω hω => hvan ω ?_⟩, mem_ball_self (half_pos hr)⟩)
    exact disjoint_sdiff_left.mono_left (hω.trans (subset_closure.trans (hcl.trans hrUK)))
  -- Step 6: `spt Y = K \ Z_Y` is compact
  have hcpt : IsCompact Y.support := by
    have heq : Y.support = K \ Y.zeroRegion :=
      Subset.antisymm (fun x hx => ⟨hspt hx, hx.2⟩) fun x hx => ⟨hVU (hKV hx.1), hx.2⟩
    rw [heq]
    exact hK.diff Y.isOpen_zeroRegion
  -- Step 3: `Y⌞V = X`, since `R'` and `R` have the same action
  have hres : Y.restrictDomain hVU = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply, hY (testFormOnInclusion hVU n ω),
      testFormOnInclusion_coe, hR'R, hRX ω]
  refine ⟨Y, hres, hspt, hcpt, ?_, ⟨R', hY⟩⟩
  -- Step 7: `∂X = 0 → ∂Y = 0` (trivial in degree `0`)
  rcases n with _ | m
  · exact fun _ => trivial
  intro hX
  change X.boundary = 0 at hX
  change Y.boundary = 0
  -- Step 7.1: a cutoff `χ ∈ C^∞_c(V)` equal to `1` on an open set `O ⊇ K`
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Euclid P)) (n := ⊤) hK.isClosed
    ((self_subset_thickening hδ K).trans (thickening_subset_interior_cthickening δ K))
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχsupp : tsupport χ ⊆ cthickening δ K :=
    closure_minimal (fun x hx => by_contra fun h => hx (hχ0 x h)) isClosed_cthickening
  have hχc : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hχsupp
  obtain ⟨O, hO, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  -- Step 7.2: `χω ∈ 𝒟^m(V)` for `ω ∈ 𝒟^m(U)`
  have hcut : ∀ ω : TestFormOn U m,
      (fun x => χ x • (ω : DifferentialForm (Euclid P) m) x) ∈ testFormOnSubmodule V m :=
    fun ω => ⟨⟨hχs.smul ω.property.1.1, hχc.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans (hχsupp.trans hδV)⟩
  -- Step 7.4: `∂Y(ω) = R'(dω) = R'(d(χω)) = R(d(χω)) = X(d(χω)) = ∂X(χω) = 0`
  ext ω
  rw [GeometricCurrentOn.zero_apply, GeometricCurrentOn.boundary_apply,
    hY (exteriorDerivativeTestOn U m ω)]
  have hd : R'.action (exteriorDerivativeTestOn U m ω : DifferentialForm (Euclid P) (m + 1)) =
      R'.action (exteriorDerivativeTestOn V m ⟨_, hcut ω⟩ :
        DifferentialForm (Euclid P) (m + 1)) := by
    unfold IMRep.action
    refine setIntegral_congr_fun R'.measurableSet_carrier fun x hx => ?_
    -- Step 7.3: `χω = ω` near `x ∈ M' ⊆ K ⊆ O`, so `d(χω)(x) = dω(x)`
    have hloc : (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) =ᶠ[𝓝 x]
        (ω : DifferentialForm (Euclid P) m) :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds (hKO (hR'K hx))) fun y hy => by
        rw [show χ y = 1 from hOχ hy, one_smul]
    show (R'.mult x : ℝ) * R'.orient x (extDeriv (ω : DifferentialForm (Euclid P) m) x) =
      (R'.mult x : ℝ) * R'.orient x
        (extDeriv (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) x)
    rw [hloc.extDeriv_eq]
  rw [hd, hR'R, ← hRX, ← GeometricCurrentOn.boundary_apply, hX, GeometricCurrentOn.zero_apply]
/-- **Mass localization for a current vanishing away from a compact set** (Simon 7.2.4, proof,
step 4(a)).  Let `C ⊆ V` with `C` compact and `V` open, and let `X ∈ 𝒟ₖ(U)` kill every
`ω ∈ 𝒟ᵏ(U)` with `spt ω ∩ C = ∅`.  Then `M_G(X) ≤ M_V(X)` for every `G`.  Choose a smooth
`χ : ℝᴾ → [0, 1]` with `χ = 1` on an open `N ⊇ C` and `spt χ ⊆ V`.  For `ω` admissible
for `M_G`, `(1 − χ)ω` vanishes on `N`, so `X(ω) = X(χω)`, and `χω` is admissible for `M_V`
because `|χω| = χ|ω| ≤ 1`. -/
theorem Submission.lcmp_massOn_le_of_vanish_off_compact : ∀ (P k : ℕ) (U V C : Set (Euclid P)) (X : GeometricCurrentOn U k), IsCompact C → IsOpen V → C ⊆ V → (∀ ω : TestFormOn U k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) C → X ω = 0) → ∀ G : Set (Euclid P), X.massOn G ≤ X.massOn V := by
  intro P k U V C X hC hV hCV hvan G
  -- Step 4: `|cα| = |c| |α|` for the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
        ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        ring
      · simp
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  -- Step 1: if `C = ∅` then `X = 0`, so `M_G(X) = 0`
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine sSup_le ?_
    rintro r ⟨ω, -, rfl⟩
    show ENNReal.ofReal (X ω) ≤ X.massOn V
    rw [hvan ω (disjoint_empty _), ENNReal.ofReal_zero]
    exact zero_le
  -- Step 2: `C ⊆ V' = {dist(·, C) < δ/2}` with `closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hV'o : IsOpen (thickening (δ / 2) C) := isOpen_thickening
  -- Step 3: `χ = τ(2g/a)`, where `{g ≠ 0} = V'`, `a = min_C g > 0`, `τ` the smooth transition
  obtain ⟨g, hgsupp, hgsmooth, hgrange⟩ := hV'o.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgrange ⟨x, rfl⟩).1
  have hgpos : ∀ x ∈ C, 0 < g x := by
    intro x hx
    have hxs : x ∈ support g := by
      rw [hgsupp]
      exact self_subset_thickening (half_pos hδ) C hx
    exact lt_of_le_of_ne (hgnn x) (Ne.symm hxs)
  obtain ⟨x₀, hx₀C, hx₀min⟩ := hC.exists_isMinOn hCne hgsmooth.continuous.continuousOn
  set a := g x₀
  have ha : 0 < a := hgpos x₀ hx₀C
  set χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 * g x / a)
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hgsmooth).div_const a)
  -- `χ = 1` on the open set `N = {g > a/2} ⊇ C`
  set N : Set (Euclid P) := {x | a / 2 < g x}
  have hNo : IsOpen N := isOpen_lt continuous_const hgsmooth.continuous
  have hCN : C ⊆ N := fun x hx => by
    have h1 : a ≤ g x := hx₀min hx
    show a / 2 < g x
    linarith
  have hχN : ∀ x ∈ N, χ x = 1 := fun x hx => by
    apply Real.smoothTransition.one_of_one_le
    have hx' : a / 2 < g x := hx
    rw [le_div_iff₀ ha]
    linarith
  -- `χ = 0` where `g = 0`, so `spt χ ⊆ closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  have hχsupp : support χ ⊆ thickening (δ / 2) C := by
    intro x hx
    by_contra h
    rw [← hgsupp, mem_support, not_not] at h
    apply hx
    show Real.smoothTransition (2 * g x / a) = 0
    rw [h, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hclχ : tsupport χ ⊆ cthickening (δ / 2) C :=
    (closure_mono hχsupp).trans (closure_thickening_subset_cthickening _ _)
  have htχ : tsupport χ ⊆ V :=
    hclχ.trans ((cthickening_mono (half_le_self hδ.le) C).trans hδV)
  -- Step 5: for `ω` admissible for `M_G`, `ω₁ = χω ∈ 𝒟ᵏ(U)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ X.massOn V
  have hωt : IsTestForm (ω : DifferentialForm (Euclid P) k) := ω.property.1
  obtain ⟨ω₁f, hω₁f⟩ : ∃ g : DifferentialForm (Euclid P) k,
      g = fun x => χ x • (ω : DifferentialForm (Euclid P) k) x := ⟨_, rfl⟩
  have hω₁smooth : IsSmoothForm ω₁f := by
    rw [hω₁f]
    exact hχsmooth.smul hωt.1
  have hω₁supp : tsupport ω₁f ⊆ tsupport (ω : DifferentialForm (Euclid P) k) := by
    rw [hω₁f]
    exact tsupport_smul_subset_right _ _
  have hω₁suppχ : tsupport ω₁f ⊆ tsupport χ := by
    rw [hω₁f]
    exact tsupport_smul_subset_left _ _
  have hω₁cpt : HasCompactSupport ω₁f :=
    IsCompact.of_isClosed_subset hωt.2 (isClosed_tsupport _) hω₁supp
  let ω₁ : TestFormOn U k := ⟨ω₁f, ⟨hω₁smooth, hω₁cpt⟩, hω₁supp.trans ω.property.2⟩
  -- Step 6: `ω₂ = ω − ω₁` vanishes on `N ⊇ C`, so `spt ω₂ ∩ C = ∅` and `X(ω₂) = 0`
  have hω₂van : X (ω - ω₁) = 0 := by
    apply hvan
    rw [Set.disjoint_left]
    intro x hx hxC
    have hzero : ∀ y ∈ N, ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y = 0 := by
      intro y hy
      have hco : ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y =
          (ω : DifferentialForm (Euclid P) k) y - ω₁f y := rfl
      rw [hco, hω₁f]
      beta_reduce
      rw [hχN y hy, one_smul, sub_self]
    have hxN : x ∈ N := hCN hxC
    have hnot : x ∉ tsupport ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hNo.mem_nhds hxN] with y hy
      exact hzero y hy
    exact hnot hx
  have hsplit : X ω = X ω₁ := by
    have : X (ω - ω₁) = X ω - X ω₁ := map_sub X.toCurrent ω ω₁
    linarith
  -- Step 5 (cont.): `spt ω₁ ⊆ spt χ ⊆ V` and `|ω₁(x)| = χ(x) |ω(x)| ≤ 1`
  have hadm : ω₁ ∈ massAdmissibleOn U k V := by
    refine ⟨hω₁suppχ.trans htχ, fun x => ?_⟩
    have hco : (ω₁ : DifferentialForm (Euclid P) k) x =
        χ x • (ω : DifferentialForm (Euclid P) k) x := by
      show ω₁f x = _
      rw [hω₁f]
    rw [hco, hsmul]
    have h0 : 0 ≤ χ x := Real.smoothTransition.nonneg _
    have h1 : χ x ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg h0]
    have h2 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
    have h3 := hω.2 x
    nlinarith
  -- Step 7: `ofReal X(ω) = ofReal X(ω₁) ≤ M_V(X)`; take the supremum over `ω`
  rw [hsplit]
  exact X.le_massOn hadm
/-- **Simon 6.2.5, 6.2.16** (mass across a change of domain).  If `W ⊆ V ⊆ U`, and
`S ∈ 𝒟ₙ(U)`, `S' ∈ 𝒟ₙ(V)` agree on every `ω ∈ 𝒟ⁿ(V)` with `spt ω ⊆ W`, then
`M_W(S) = M_W(S')`.  A form admissible for `M_W` has `spt ω ⊆ W ⊆ V`, so the admissible forms in
`U` and in `V` are the same underlying forms, related by `testFormOnInclusion`; the two suprema
therefore range over the same values. -/
theorem Submission.dtc_massOn_eq_of_agreeOn : ∀ (P n : ℕ) (U V W : Set (Euclid P)) (hVU : V ⊆ U) (S : GeometricCurrentOn U n) (S' : GeometricCurrentOn V n), W ⊆ V → (∀ ω : TestFormOn V n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → S (testFormOnInclusion hVU n ω) = S' ω) → S.massOn W = S'.massOn W := by
  intro P n U V W hVU S S' hWV hagree
  -- both masses are suprema of `ofReal (T ω)` over admissible forms: compare the value sets
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · -- an admissible `ω ∈ 𝒟ⁿ(U)` has `spt ω ⊆ W ⊆ V`, so it is an admissible `ω' ∈ 𝒟ⁿ(V)`
    rintro ⟨ω, hω, rfl⟩
    let ω' : TestFormOn V n := ⟨ω, ω.property.1, hω.1.trans hWV⟩
    have hincl : testFormOnInclusion hVU n ω' = ω := Subtype.ext rfl
    refine ⟨ω', hω, ?_⟩
    dsimp only
    rw [← hagree ω' hω.1, hincl]
  · -- an admissible `ω' ∈ 𝒟ⁿ(V)` is admissible in `U` after inclusion
    rintro ⟨ω', hω', rfl⟩
    refine ⟨testFormOnInclusion hVU n ω', hω', ?_⟩
    dsimp only
    rw [hagree ω' hω'.1]
/-- **Extension of a compactly supported integer multiplicity current to `ℝᴾ`** (Simon 7.3.1,
proof, step 3(c); 6.2.5, 6.2.11).  Let `X = τ(M, θ, ξ) ∈ 𝒟ₘ₊₁(U)`, `U` open, with `spt X ⊆ K`,
`K ⊆ U` compact.  Then `Hᵐ⁺¹(M \ K) ≤ Hᵐ⁺¹(M \ spt X) = 0`
(`imrep_carrier_sdiff_support_null`), so extension by zero (`dtc_extend_by_zero`) gives an
integer multiplicity `Y ∈ 𝒟ₘ₊₁(ℝᴾ)` with `Y⌞U = X` and `spt Y ⊆ K`.  `Y` and `∂Y` kill every
form whose support misses `K` (`dtc_vanish_off_support`; `spt dω ⊆ spt ω`), so their masses
are attained in `U` (`lcmp_massOn_le_of_vanish_off_compact`), where they agree with `X` and `∂X`
(`dtc_massOn_eq_of_agreeOn`; `d` commutes with the inclusion `𝒟(U) ⊆ 𝒟(ℝᴾ)`):
`M(Y) ≤ M_U(Y) = M_U(X) = M(X)` and `M(∂Y) ≤ M_U(∂Y) = M_U(∂X) = M(∂X)`. -/
theorem Submission.dimred_mbl_fc_extend_to_univ : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P m : ℕ) (U K : Set (Euclid P)) (X : GeometricCurrentOn U (m + 1)), IsOpen U → IsCompact K → K ⊆ U → IsIntegerMultiplicity X → X.support ⊆ K → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass := by
  rintro - - P m U K X hU hK hKU ⟨R, hRX⟩ hXK
  -- Step 1: `Hᵐ⁺¹(M \ K) = 0`, since `M \ K ⊆ M \ spt X`
  have hnull : μHE[m + 1] (R.carrier \ K) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hXK)
      (Submission.imrep_carrier_sdiff_support_null P (m + 1) U X R hU hRX)
  -- Step 2: extend `X` by zero to an integer multiplicity `Y ∈ 𝒟ₘ₊₁(ℝᴾ)` with `spt Y ⊆ K`
  obtain ⟨Y, hres, hspt, -, -, hIM⟩ := Submission.dtc_extend_by_zero P (m + 1) univ U K
    (subset_univ U) X R isOpen_univ hU hK hKU hRX hnull
  -- Step 3: `Y` and `∂Y` kill every form whose support misses `K ⊇ spt Y`
  have hvan : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → Y ω = 0 :=
    fun ω hω => Submission.dtc_vanish_off_support P (m + 1) univ Y ω (hω.mono_right hspt)
  have hvan' : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) K → Y.boundary ω = 0 :=
    fun ω hω => hvan _ (hω.mono_left (tsupport_exteriorDerivative_subset _))
  refine ⟨Y, hIM, hres, hspt, ?_, ?_⟩
  -- Step 4: `M(Y) ≤ M_U(Y) = M_U(X) = M(X)`
  · calc Y.mass ≤ Y.massOn U :=
          Submission.lcmp_massOn_le_of_vanish_off_compact P (m + 1) univ U K Y hK hU hKU hvan univ
      _ = X.mass := Submission.dtc_massOn_eq_of_agreeOn P (m + 1) univ U U (subset_univ U) Y X
          subset_rfl fun ω _ => by rw [← hres, GeometricCurrentOn.restrictDomain_apply]
  -- Step 5: `M(∂Y) ≤ M_U(∂Y) = M_U(∂X) = M(∂X)`, as `d` commutes with `𝒟ᵐ(U) ⊆ 𝒟ᵐ(ℝᴾ)`
  · calc Y.boundary.mass ≤ Y.boundary.massOn U :=
          Submission.lcmp_massOn_le_of_vanish_off_compact P m univ U K Y.boundary hK hU hKU hvan'
            univ
      _ = X.boundary.mass := Submission.dtc_massOn_eq_of_agreeOn P m univ U U (subset_univ U)
          Y.boundary X.boundary subset_rfl fun ω _ => by
            rw [← hres, GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply,
              GeometricCurrentOn.restrictDomain_apply]
            rfl

/-- **Simon Ch. 6, 7.2, (1)–(3)** (total boundedness in `U`), from the deformation theorem (DF),
boundary rectifiability (BR), restriction (IR) and differences (IS) of integer multiplicity
currents and the mass formula (ME).  Let `c ≥ 1` be the constant of (DF), choose `ρ > 0` with
`2cρΛ < η` and let `𝒬` be the restrictions `Q̂|_U` of the finite family `𝒬̂` of (DF) for
`(ρ, K, Λ)`.  Extend `X` to `Y` on `ℝᴾ` with `Y|_U = X`, `spt Y ⊆ K`, `M(Y) ≤ M(X)` and
`M(∂Y) ≤ M(∂X)` (`dimred_mbl_fc_extend_to_univ`), and deform it: `Y − Q̂ − Ŝ = ∂R̂`.  As
`M(∂R̂) ≤ M(Y) + M(Q̂) + M(Ŝ) < ∞` (`cmc_fc_tb_massOn_sub_le`), (BR) makes `∂R̂` integer
multiplicity, hence so is `Ŝ = (Y − Q̂) − ∂R̂` by (IS).  Restriction to `U` keeps integer
multiplicity (`dtc_restrictDomain_isIntegerMultiplicity`) and the identity `X − Q − S = ∂R`, and
does not increase mass (`dtc_massOn_eq_of_agreeOn`): `M(R) + M(S) ≤ M(R̂) + M(Ŝ) ≤ 2cρΛ ≤ η`. -/
theorem Submission.dimred_mbl_fc_total_bounded : (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → (∀ (P d : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P m : ℕ) (U K : Set (Euclid P)) (Λ : NNReal) (η : ℝ≥0∞), IsOpen U → IsCompact K → K ⊆ U → 0 < η → ∃ 𝒬 : Set (GeometricCurrentOn U (m + 1)), 𝒬.Finite ∧ ∀ X : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity X → X.support ⊆ K → X.mass ≤ Λ → X.boundary.mass ≤ Λ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X - Q - S = R.boundary ∧ R.mass + S.mass ≤ η := by
  intro DF BR IR IS ME P m U K Λ η hU hK hKU hη
  -- Step 1: the constant `c ≥ 1` of (DF) and a scale `ρ = r > 0` with `r · 2cΛ < η`
  obtain ⟨c, -, hDF⟩ := DF P m
  obtain ⟨r, hr, hrη⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 2 * (c : ℝ≥0∞) * Λ)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)
      ENNReal.coe_ne_top) hη.ne'
  have hρη : (c : ℝ≥0∞) * ENNReal.ofReal r * Λ + c * ENNReal.ofReal r * Λ ≤ η := by
    rw [ENNReal.ofReal_coe_nnreal]
    calc (c : ℝ≥0∞) * r * Λ + c * r * Λ = r * (2 * c * Λ) := by ring
      _ ≤ η := hrη.le
  -- Step 2: the finite family `𝒬̂` of (DF) for `(ρ, K, Λ)`; `𝒬` is its image under `Z ↦ Z|_U`
  obtain ⟨𝒬h, h𝒬h, hdef⟩ := hDF r K Λ (NNReal.coe_pos.mpr hr) hK
  refine ⟨(fun Z => Z.restrictDomain (subset_univ U)) '' 𝒬h, h𝒬h.image _, ?_⟩
  -- (F2), mass part: `M(Z|_U) = M_U(Z) ≤ M(Z)`
  have hres : ∀ (d : ℕ) (Z : GeometricCurrentOn (univ : Set (Euclid P)) d),
      (Z.restrictDomain (subset_univ U)).mass ≤ Z.mass := fun d Z =>
    (Submission.dtc_massOn_eq_of_agreeOn P d univ U U (subset_univ U) Z
      (Z.restrictDomain (subset_univ U)) subset_rfl fun _ _ => rfl).symm.le.trans
      (Z.massOn_mono (subset_univ U))
  intro X hX hXK hXm hXb
  -- Step 3: extend `X` to `Y` on `ℝᴾ` (`M(Y), M(∂Y) ≤ Λ`) and deform: `Y − Q̂ − Ŝ = ∂R̂`
  obtain ⟨Y, hY, rfl, hYK, hYm, hYb⟩ :=
    Submission.dimred_mbl_fc_extend_to_univ IR ME P m U K X hU hK hKU hX hXK
  have hYΛ : Y.mass ≤ Λ := hYm.trans hXm
  have hYbΛ : Y.boundary.mass ≤ Λ := hYb.trans hXb
  obtain ⟨Qh, hQh, Rh, Sh, hQhIM, -, hRhIM, hYQS, -, hQhm, -, hRhm, hShm, -, -⟩ :=
    hdef Y hY hYK hYΛ (hYbΛ.trans_lt ENNReal.coe_lt_top)
  -- Step 4: `M(∂R̂) = M(Y − Q̂ − Ŝ) ≤ M(Y) + M(Q̂) + M(Ŝ) < ∞`, so `∂R̂` is integer
  -- multiplicity by (BR) in `ℝᴾ`, as `M_W(∂R̂) ≤ M(∂R̂)` for every `W`
  have hbR : Rh.boundary.mass < ∞ := by
    rw [← hYQS]
    calc (Y - Qh - Sh).mass ≤ (Y - Qh).mass + Sh.mass :=
          Submission.cmc_fc_tb_massOn_sub_le P (m + 1) univ univ (Y - Qh) Sh
      _ ≤ Y.mass + Qh.mass + Sh.mass := by
          gcongr
          exact Submission.cmc_fc_tb_massOn_sub_le P (m + 1) univ univ Y Qh
      _ ≤ Λ + c * Λ + c * ENNReal.ofReal r * Λ := by
          gcongr
          exacts [hQhm.trans (by gcongr), hShm.trans (by gcongr)]
      _ < ∞ := by
          rw [ENNReal.ofReal_coe_nnreal]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top,
            ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top⟩,
            ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)
              ENNReal.coe_lt_top⟩
  have hbRIM : IsIntegerMultiplicity Rh.boundary :=
    BR P (m + 1) univ Rh isOpen_univ hRhIM fun W _ _ =>
      (Rh.boundary.massOn_mono (subset_univ W)).trans_lt hbR
  -- `Ŝ = (Y − Q̂) − ∂R̂` (evaluate `Y − Q̂ − Ŝ = ∂R̂` at each `ω`), integer multiplicity by (IS)
  have hSh : Sh = Y - Qh - Rh.boundary := by
    ext ω
    have h := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) => T ω) hYQS
    change Y ω - Qh ω - Sh ω = Rh.boundary ω at h
    change Sh ω = Y ω - Qh ω - Rh.boundary ω
    linarith
  have hShIM : IsIntegerMultiplicity Sh := by
    rw [hSh]
    exact IS P (m + 1) univ (Y - Qh) Rh.boundary isOpen_univ
      (IS P (m + 1) univ Y Qh isOpen_univ hY hQhIM) hbRIM
  -- Step 5: `Q := Q̂|_U ∈ 𝒬`, `R := R̂|_U` and `S := Ŝ|_U`; `R`, `S` are integer multiplicity (F2)
  refine ⟨Qh.restrictDomain (subset_univ U), mem_image_of_mem _ hQh,
    Rh.restrictDomain (subset_univ U), Sh.restrictDomain (subset_univ U),
    Submission.dtc_restrictDomain_isIntegerMultiplicity P (m + 2) univ U (subset_univ U) Rh hU
      hRhIM,
    Submission.dtc_restrictDomain_isIntegerMultiplicity P (m + 1) univ U (subset_univ U) Sh hU
      hShIM, ?_, ?_⟩
  · -- `(X − Q − S)(ω) = (Y − Q̂ − Ŝ)(ιω) = ∂R̂(ιω) = R̂(ι dω) = ∂R(ω)` with `X = Y|_U`, since
    -- `ι` commutes with `d` on the underlying forms
    ext ω
    exact congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) =>
      T (testFormOnInclusion (subset_univ U) (m + 1) ω)) hYQS
  · -- Step 6: `M(R) + M(S) ≤ M(R̂) + M(Ŝ) ≤ cρM(Y) + cρM(∂Y) ≤ 2cρΛ ≤ η`
    calc (Rh.restrictDomain (subset_univ U)).mass + (Sh.restrictDomain (subset_univ U)).mass
        ≤ Rh.mass + Sh.mass := add_le_add (hres _ Rh) (hres _ Sh)
      _ ≤ c * ENNReal.ofReal r * Y.mass + c * ENNReal.ofReal r * Y.boundary.mass :=
          add_le_add hRhm hShm
      _ ≤ c * ENNReal.ofReal r * Λ + c * ENNReal.ofReal r * Λ := by gcongr
      _ ≤ η := hρη
  -- Step 3: `(A − B)(ω) = A(ω) − B(ω) = A(ω) + B(−ω)`, by linearity of `B`
  have hsplit : (A - B) ω = A ω + B (-ω) := by
    have hB : B (-ω) = -B ω := B.toCurrent.map_neg ω
    change A ω - B ω = A ω + B (-ω)
    rw [hB, sub_eq_add_neg]
  -- Steps 4–5: `ofReal` is subadditive, and each term is bounded by the corresponding mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hneg)

/-- **Close pairs** (Simon Ch. 6, 7.2, step 2 of the proof).  Assume differences of integer
multiplicity currents in an open `U` are integer multiplicity.  If `Y − Q − S₁ = ∂R₁` and
`Z − Q − S₂ = ∂R₂` in `U` with `R₁, S₁, R₂, S₂` integer multiplicity, then `R = R₁ − R₂` and
`S = S₁ − S₂` are integer multiplicity, `Y − Z − S = ∂R` (the common `Q` cancels), and
`M(R) + M(S) ≤ (M(R₁) + M(S₁)) + (M(R₂) + M(S₂))` by `M(A − B) ≤ M(A) + M(B)`. -/
theorem Submission.cmc_fc_cs_close_of_common_center : (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P m : ℕ) (U : Set (Euclid P)) (Y Z Q S₁ S₂ : GeometricCurrentOn U (m + 1)) (R₁ R₂ : GeometricCurrentOn U (m + 2)), IsOpen U → IsIntegerMultiplicity R₁ → IsIntegerMultiplicity S₁ → IsIntegerMultiplicity R₂ → IsIntegerMultiplicity S₂ → Y - Q - S₁ = R₁.boundary → Z - Q - S₂ = R₂.boundary → ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ Y - Z - S = R.boundary ∧ R.mass + S.mass ≤ (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass) := by
  intro hIS P m U Y Z Q S₁ S₂ R₁ R₂ hU hR₁ hS₁ hR₂ hS₂ h₁ h₂
  -- `R = R₁ − R₂` and `S = S₁ − S₂` are integer multiplicity by (IS)
  refine ⟨R₁ - R₂, S₁ - S₂, hIS P (m + 2) U R₁ R₂ hU hR₁ hR₂, hIS P (m + 1) U S₁ S₂ hU hS₁ hS₂,
    ?_, ?_⟩
  · -- evaluate both hypotheses at `ω`, using `∂T(ω) = T(dω)`; the `Q(ω)` terms cancel
    ext ω
    have e₁ : Y ω - Q ω - S₁ ω = R₁ (exteriorDerivativeTestOn U (m + 1) ω) :=
      congrArg (fun T : GeometricCurrentOn U (m + 1) => T ω) h₁
    have e₂ : Z ω - Q ω - S₂ ω = R₂ (exteriorDerivativeTestOn U (m + 1) ω) :=
      congrArg (fun T : GeometricCurrentOn U (m + 1) => T ω) h₂
    change Y ω - Z ω - (S₁ ω - S₂ ω) =
      R₁ (exteriorDerivativeTestOn U (m + 1) ω) - R₂ (exteriorDerivativeTestOn U (m + 1) ω)
    linarith
  · -- `M(R₁ − R₂) ≤ M(R₁) + M(R₂)` and `M(S₁ − S₂) ≤ M(S₁) + M(S₂)`, with `M = M_U`
    calc (R₁ - R₂).mass + (S₁ - S₂).mass
        ≤ (R₁.mass + R₂.mass) + (S₁.mass + S₂.mass) :=
          add_le_add (Submission.cmc_fc_cs_massOn_sub_le P (m + 2) U U R₁ R₂)
            (Submission.cmc_fc_cs_massOn_sub_le P (m + 1) U U S₁ S₂)
      _ = (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass) := add_add_add_comm _ _ _ _
/-- **Diagonal extraction** (Simon Ch. 6, proof of 7.2, chapter-06.txt lines 2101–2105:
"apply (1) with `ε = 1, 1/2, 1/4` etc. to extract a subsequence `{T_{j_r}}` …
`d(T_{j_{r+1}}, T_{j_r}) < 2^{-r}`", with `2^{-r}`-closeness replaced by an arbitrary relation
`C r`).  If, for each `r`, every infinite `I ⊆ ℕ` contains an infinite `J ⊆ I` all of whose pairs
are `C r`-related, then some strictly increasing `φ` has `C r (φ (r + 1)) (φ r)` for every `r`.
Refining `I₀ = ℕ` gives nested infinite sets `I_{r+1} ⊆ I_r` with `I_{r+1}` pairwise
`C r`-related; an increasing choice `φ(r) ∈ I_{r+1}` puts both `φ(r)` and `φ(r + 1)` in
`I_{r+1}`. -/
theorem Submission.cmc_fc_cs_diagonal_subseq : ∀ (C : ℕ → ℕ → ℕ → Prop), (∀ (r : ℕ) (I : Set ℕ), I.Infinite → ∃ J ⊆ I, J.Infinite ∧ ∀ j ∈ J, ∀ l ∈ J, C r j l) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, C r (φ (r + 1)) (φ r) := by
  intro C hC
  -- Step 1: refinements `F(r, I) ⊆ I`, infinite, with all pairs in relation `C r`
  choose F hFsub hFinf hFC using hC
  -- Step 2: nested infinite index sets `I₀ = ℕ`, `I_{r+1} = F(r, I_r)`
  let I : ℕ → {s : Set ℕ // s.Infinite} := fun r =>
    Nat.rec ⟨univ, infinite_univ⟩ (fun r s => ⟨F r s.1 s.2, hFinf r s.1 s.2⟩) r
  have hsub : ∀ r, (I (r + 1)).1 ⊆ (I r).1 := fun r => hFsub r (I r).1 (I r).2
  have hpair : ∀ r, ∀ j ∈ (I (r + 1)).1, ∀ l ∈ (I (r + 1)).1, C r j l :=
    fun r => hFC r (I r).1 (I r).2
  -- Step 3: `I_{r+1}` is unbounded: `g(r, a) ∈ I_{r+1}` and `a < g(r, a)`
  choose g hgI hglt using fun r : ℕ => (I (r + 1)).2.exists_gt
  -- Step 4: diagonal choice `φ(0) = g(0, 0)`, `φ(r + 1) = g(r + 1, φ(r)) ∈ I_{r+2}`
  let φ : ℕ → ℕ := fun r => Nat.rec (g 0 0) (fun r a => g (r + 1) a) r
  have hφI : ∀ r, φ r ∈ (I (r + 1)).1 := by
    intro r
    cases r with
    | zero => exact hgI 0 0
    | succ r => exact hgI (r + 1) (φ r)
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun r => hglt (r + 1) (φ r)
  -- Step 5: `φ(r + 1) ∈ I_{r+2} ⊆ I_{r+1}` and `φ(r) ∈ I_{r+1} = F(r, I_r)`
  exact ⟨φ, hφ, fun r => hpair r _ (hsub (r + 1) (hφI (r + 1))) _ (hφI r)⟩

/-- **Cauchy subsequence** (Simon Ch. 6, proof of 7.2, chapter-06.txt lines 2101–2105: "apply (1)
with `ε = 1, 1/2, 1/4` etc. to extract a subsequence `{T_{j_r}}` … `d(T_{j_{r+1}}, T_{j_r}) <
2^{-r}`").  Assume differences of integer multiplicity currents in an open `U` are integer
multiplicity, and that for every `η > 0` each `X_j` is within `η` of a member `Q` of one finite
family `𝒬`: `X_j − Q − S = ∂R` with `R, S` integer multiplicity and `M(R) + M(S) ≤ η`.  Then a
subsequence has consecutive terms `2^{-r}`-close.  For `η = 2^{-(r+1)}` and an infinite `I ⊆ ℕ`,
one `q ∈ 𝒬` is the chosen member for infinitely many `j ∈ I` (pigeonhole); any two of these are
`2 · 2^{-(r+1)} = 2^{-r}`-close by the common-center estimate, and the diagonal extraction
finishes. -/
theorem Submission.dimred_mbl_fc_cauchy_subseq : (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ η : ℝ≥0∞, 0 < η → ∃ 𝒬 : Set (GeometricCurrentOn U (m + 1)), 𝒬.Finite ∧ ∀ j, ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X j - Q - S = R.boundary ∧ R.mass + S.mass ≤ η) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X (φ (r + 1)) - X (φ r) - S = R.boundary ∧ R.mass + S.mass ≤ (2⁻¹ : ℝ≥0∞) ^ r := by
  intro hIS P m U X hU hX
  -- Steps 4–5: diagonal extraction for the relation "`X_j`, `X_l` are `2^{-r}`-close"
  refine Submission.cmc_fc_cs_diagonal_subseq (fun r j l =>
    ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X j - X l - S = R.boundary ∧
        R.mass + S.mass ≤ (2⁻¹ : ℝ≥0∞) ^ r) ?_
  intro r I hI
  -- Step 3: the hypothesis with `η = 2^{-(r+1)}`; choose `Q_j ∈ 𝒬` and `R_j, S_j` for each `j`
  obtain ⟨𝒬, h𝒬, hdec⟩ := hX ((2⁻¹ : ℝ≥0∞) ^ (r + 1))
    (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
  choose Q hQ R S hR hS hRS hmass using hdec
  -- pigeonhole: `I` is covered by the finitely many fibers `{j ∈ I | Q_j = q}`, `q ∈ 𝒬`
  obtain ⟨q, -, hq⟩ : ∃ q ∈ 𝒬, {j | j ∈ I ∧ Q j = q}.Infinite := by
    by_contra! hfin
    exact hI ((h𝒬.biUnion fun q hq => hfin q hq).subset fun j hj => mem_biUnion (hQ j) ⟨hj, rfl⟩)
  refine ⟨{j | j ∈ I ∧ Q j = q}, fun j hj => hj.1, hq, ?_⟩
  -- Step 2: two indices with the common center `q` are `2 · 2^{-(r+1)} = 2^{-r}`-close
  rintro j ⟨-, hj⟩ l ⟨-, hl⟩
  obtain ⟨R', S', hR', hS', hb, hm⟩ := Submission.cmc_fc_cs_close_of_common_center hIS P m U
    (X j) (X l) q (S j) (S l) (R j) (R l) hU (hR j) (hS j) (hR l) (hS l) (hj ▸ hRS j)
    (hl ▸ hRS l)
  refine ⟨R', S', hR', hS', hb, hm.trans ?_⟩
  calc (R j).mass + (S j).mass + ((R l).mass + (S l).mass)
      ≤ (2⁻¹ : ℝ≥0∞) ^ (r + 1) + (2⁻¹ : ℝ≥0∞) ^ (r + 1) := add_le_add (hmass j) (hmass l)
    _ = (2⁻¹ : ℝ≥0∞) ^ r := by rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
