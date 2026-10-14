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

/-- Integer median of an integer-valued function of bounded variation on the open unit cube
(the BV facts used in Simon 6.5.1, (26)–(33)): the Poincaré inequality, the bound on the median
and the boundary estimate.  The proof works with translations: for a smooth `ψ` supported in an
open `S` whose segments `S + [0, 1] h` stay in the cube, the field `(∫₀¹ ψ(· - τh) dτ) h` is
admissible, which bounds `∫ (u(x + h) - u(x)) ψ(x) dx`; a duality argument (smooth cut-offs and
inner regularity) turns this into an `L¹` bound for translation differences.  Integrating over
`h` gives the Poincaré inequality, the least integer `β` with `|{u ≤ β}| ≥ 1/2` is a median, and
difference quotients of `G` together with slab estimates near the faces give the boundary bound. -/
theorem Submission.dtc_bc_lc_fd_dfm_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  /- Step 1: duality.  If `|∫ f ψ| ≤ B` for all smooth `ψ` with compact support in the open set
  `S` and `|ψ| ≤ 1`, then `∫_S |f| ≤ 2 B`: smooth cut-offs give `|∫_K f| ≤ B` for compact
  `K ⊆ S`, inner regularity extends this to measurable subsets, and we split `S` by the sign of
  `f`. -/
  have hdual : ∀ (f : Euclid (m + 1) → ℝ) (S : Set (Euclid (m + 1))) (B : ℝ), Integrable f →
      Measurable f → IsOpen S → volume S ≠ ⊤ →
      (∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
        (∀ x, |ψ x| ≤ 1) → |∫ x, f x * ψ x| ≤ B) → ∫ x in S, |f x| ≤ 2 * B := by
    intro f S B hf hfm hSo hSfin hB
    have H1 : ∀ K, IsCompact K → K ⊆ S → |∫ x in K, f x| ≤ B := by
      intro K hK hKS
      obtain ⟨δ, hδ, hδS⟩ := hK.exists_cthickening_subset_open hSo hKS
      have hr : ∀ k : ℕ, 0 < δ / (k + 2) := fun k => by positivity
      have hrδ : ∀ k : ℕ, δ / (k + 2) ≤ δ := fun k =>
        div_le_self hδ.le (by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)])
      choose ψ hψsm hψr hψs hψ1 using fun k : ℕ =>
        exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (isOpen_thickening : IsOpen (thickening (δ / (k + 2)) K))
          hK.isClosed (self_subset_thickening (hr k) K)
      have htsupp : ∀ k, tsupport (ψ k) ⊆ cthickening (δ / (k + 2)) K := fun k => by
        rw [tsupport, hψs k]; exact closure_thickening_subset_cthickening _ _
      have hψabs : ∀ k x, |ψ k x| ≤ 1 := fun k x => by
        have := hψr k (mem_range_self x)
        rw [abs_le]; exact ⟨by linarith only [this.1], this.2⟩
      have hbd : ∀ k, |∫ x, f x * ψ k x| ≤ B := fun k => hB (ψ k) (hψsm k)
          ((hK.cthickening).of_isClosed_subset (isClosed_tsupport _) (htsupp k))
          ((htsupp k).trans ((cthickening_mono (hrδ k) K).trans hδS)) (hψabs k)
      have hlim : Tendsto (fun k => ∫ x, f x * ψ k x) atTop (𝓝 (∫ x, K.indicator f x)) := by
        refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
          (fun k => hf.aestronglyMeasurable.mul (hψsm k).continuous.aestronglyMeasurable) hf.abs
          (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hψabs k x)
        · by_cases hx : x ∈ K
          · rw [indicator_of_mem hx]
            have : ∀ k, ψ k x = 1 := fun k => (hψ1 k x).1 hx
            simp only [this, mul_one, tendsto_const_nhds]
          · rw [indicator_of_notMem hx]
            obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hx
            have hev : ∀ᶠ k : ℕ in atTop, ψ k x = 0 := by
              obtain ⟨k₀, hk₀⟩ := exists_nat_gt (δ / ε)
              filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
              have hxt : x ∉ thickening (δ / (k + 2)) K := by
                intro hxt
                obtain ⟨y, hyK, hxy⟩ := mem_thickening_iff.1 hxt
                have hk2 : (k₀:ℝ) ≤ k := by exact_mod_cast hk
                have hk' : δ < ε * ((k:ℝ) + 2) := by
                  rw [div_lt_iff₀ hε] at hk₀
                  have := mul_le_mul_of_nonneg_right hk2 hε.le
                  linarith only [hk₀, this, hε]
                have : δ / (k + 2) < ε := by
                  rw [div_lt_iff₀ (by positivity)]; linarith only [hk']
                exact hball (mem_ball.2 (by rw [dist_comm]; linarith only [hxy, this])) hyK
              rw [← hψs k] at hxt
              exact notMem_support.1 hxt
            exact tendsto_const_nhds.congr' (by
              filter_upwards [hev] with k hk; rw [hk, mul_zero])
      rw [integral_indicator hK.isClosed.measurableSet] at hlim
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have H2 : ∀ T, MeasurableSet T → T ⊆ S → |∫ x in T, f x| ≤ B := by
      intro T hT hTS
      have hTfin : volume T ≠ ⊤ := ne_top_of_le_ne_top hSfin (measure_mono hTS)
      have : ∀ j : ℕ, ∃ K ⊆ T, IsCompact K ∧ volume T < volume K + ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
        fun j => hT.exists_isCompact_lt_add hTfin
          (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      choose K hKT hKc hKlt using this
      have hdiff : Tendsto (fun j => volume (T \ K j)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) (fun _ => bot_le)
          (fun j => ?_)
        rw [Function.comp_apply, measure_sdiff (hKT j)
          (hKc j).isClosed.measurableSet.nullMeasurableSet
          (ne_top_of_le_ne_top hTfin (measure_mono (hKT j)))]
        exact tsub_le_iff_left.2 (hKlt j).le
      have hconv := hf.tendsto_setIntegral_nhds_zero hdiff
      have hle : ∀ j, |∫ x in T, f x| ≤ B + |∫ x in T \ K j, f x| := fun j => by
        rw [← union_sdiff_cancel (hKT j), setIntegral_union disjoint_sdiff_right
          (hT.diff (hKc j).isClosed.measurableSet) hf.integrableOn hf.integrableOn,
          union_sdiff_cancel (hKT j)]
        have := H1 (K j) (hKc j) ((hKT j).trans hTS)
        exact (abs_add_le _ _).trans (by linarith only [this])
      have hconv' : Tendsto (fun j => B + |∫ x in T \ K j, f x|) atTop (𝓝 (B + |0|)) :=
        tendsto_const_nhds.add ((continuous_abs.tendsto 0).comp hconv)
      rw [abs_zero, add_zero] at hconv'
      exact ge_of_tendsto' hconv' hle
    have hP : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hfm
    have hSm := hSo.measurableSet
    have e : ∫ x in S, |f x| =
        (∫ x in S ∩ {x | 0 ≤ f x}, f x) - ∫ x in S \ {x | 0 ≤ f x}, f x := by
      rw [← integral_inter_add_sdiff hP hf.abs.integrableOn, sub_eq_add_neg, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun (hSm.inter hP) (fun x hx => abs_of_nonneg hx.2)
      · exact setIntegral_congr_fun (hSm.diff hP) (fun x hx => abs_of_neg (not_le.1 hx.2))
    rw [e]
    have h1 := H2 _ (hSm.inter hP) inter_subset_left
    have h2 := H2 _ (hSm.diff hP) sdiff_subset
    linarith only [h1, h2, le_abs_self (∫ x in S ∩ {x | 0 ≤ f x}, f x),
      neg_abs_le (∫ x in S \ {x | 0 ≤ f x}, f x)]
  /- Step 2: the segment average `Ψ z = ∫₀¹ ψ (z - τ h) dτ` of a smooth compactly supported `ψ`
  is smooth, and its derivative in the direction `h` is `ψ z - ψ (z - h)`. -/
  have hΨd : ∀ (h : Euclid (m + 1)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ z, HasFDerivAt (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h))
        (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) z := by
    intro h F _ _ _ ψ hψ hψc z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hψc.fderiv ℝ)
    have hsc : Continuous fun τ : ℝ => τ • h := continuous_id.smul continuous_const
    have hcont : ∀ x : Euclid (m + 1), Continuous fun τ : ℝ => ψ (x - τ • h) := fun x =>
      hψ.continuous.comp (continuous_const.sub hsc)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioc (0:ℝ) 1)) (F := fun x τ => ψ (x - τ • h))
      (F' := fun x τ => fderiv ℝ ψ (x - τ • h)) (bound := fun _ => C) (s := univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
    · exact (hcont z).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ((hdc.comp (continuous_const.sub hsc)).stronglyMeasurable
        (h := secondCountableTopologyEither_of_left ℝ _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun τ x _ => hC _
    · exact integrableOn_const (by simp)
    · refine Filter.Eventually.of_forall fun τ x _ => ?_
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x - τ • h)) (x - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (τ • h))
      rwa [ContinuousLinearMap.comp_id] at h2
  have hΨs : ∀ (h : Euclid (m + 1)) (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ContDiff ℝ k (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) := by
    intro h k
    induction k with
    | zero =>
      intro F _ _ _ ψ hψ hψc
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
        (hΨd h F ψ hψ hψc z).continuousAt)
    | succ k ih =>
      intro F _ _ _ ψ hψ hψc
      have hfd : fderiv ℝ (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) =
          fun z => ∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h) :=
        funext fun z => (hΨd h F ψ hψ hψc z).fderiv
      refine contDiff_succ_iff_fderiv.2 ⟨fun z => (hΨd h F ψ hψ hψc z).differentiableAt,
        fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
      rw [hfd]
      exact ih (Euclid (m + 1) →L[ℝ] F) (fderiv ℝ ψ) (contDiff_infty_iff_fderiv.1 hψ).2
        (hψc.fderiv ℝ)
  have hΨh : ∀ (h : Euclid (m + 1)) (ψ : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ∀ z, (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) h = ψ z - ψ (z - h) := by
    intro h ψ hψ z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    have hLc : Continuous fun τ : ℝ => fderiv ℝ ψ (z - τ • h) :=
      hdc.comp (continuous_const.sub (continuous_id.smul continuous_const))
    rw [ContinuousLinearMap.integral_apply (hLc.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (z - τ • h))
        (-(fderiv ℝ ψ (z - τ • h) h)) τ := by
      intro τ _
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (z - τ • h)) (z - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 : HasDerivAt (fun τ : ℝ => z - τ • h) (-h) τ := by
        have := ((hasDerivAt_id τ).smul_const h).const_sub z
        rwa [one_smul] at this
      have := h1.comp_hasDerivAt τ h2
      rwa [map_neg] at this
    have hint : IntervalIntegrable (fun τ : ℝ => -(fderiv ℝ ψ (z - τ • h) h)) volume 0 1 :=
      (((ContinuousLinearMap.apply ℝ ℝ h).continuous.comp hLc).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg, one_smul, zero_smul, sub_zero] at this
    linarith only [this]
  /- Step 3: the constants: `R` bounds the diameter of the cube, `CP` is the Poincaré constant. -/
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = m + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR_def]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨CP, hCP_def⟩ : ∃ CP : ℝ,
      CP = 4 * R * (volume (closedBall (0 : Euclid (m + 1)) R)).toReal := ⟨_, rfl⟩
  have hCP : 0 ≤ CP := by rw [hCP_def]; positivity
  refine ⟨CP + (m + 1) * (10 + 4 * CP) + 1, by positivity, ?_⟩
  intro u V hint huQ hV
  set Q := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} with hQ_def
  /- Step 4: the cube, `V ≥ 0`, and a measurable version `ub` of `u 1_Q`. -/
  have hQo : IsOpen Q := by
    have : Q = ⋂ i, {y : Euclid (m + 1) | 0 < y i ∧ y i < 1} := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQvol : volume Q = 1 := by
    have : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (0:ℝ) 1) := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Ioo]
    rw [this, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hQfin : volume Q ≠ ⊤ := by rw [hQvol]; exact ENNReal.one_ne_top
  have hV0 : 0 ≤ V := by
    have := hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using this
  obtain ⟨ub, hub_meas, hub_int, hub_zero, hub_ae⟩ : ∃ ub : Euclid (m + 1) → ℝ, Measurable ub ∧
      Integrable ub ∧ (∀ y ∉ Q, ub y = 0) ∧ ∀ᵐ y ∂(volume.restrict Q), ub y = u y := by
    refine ⟨Q.indicator (huQ.aestronglyMeasurable.mk u),
      huQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hQm, ?_,
      fun y hy => indicator_of_notMem hy _, ?_⟩
    · rw [integrable_indicator_iff hQm]
      exact huQ.congr huQ.aestronglyMeasurable.ae_eq_mk
    · filter_upwards [huQ.aestronglyMeasurable.ae_eq_mk, ae_restrict_mem hQm] with y hy hyQ
      rw [indicator_of_mem hyQ, ← hy]
  /- Step 5: the weak translation estimate.  If `S` is open, `S + [0, 1] h ⊆ Q`, and every line
  parallel to `h` meets `S` in parameter length `≤ lam`, then the field
  `g = (lam ‖h‖)⁻¹ Ψ h` is admissible and `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`. -/
  have hweak : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam → h ≠ 0 →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      (∀ x, |ψ x| ≤ 1) → -∫ x, (ub (x + h) - ub x) * ψ x ≤ lam * ‖h‖ * V := by
    intro S h lam hSo hseg hlam hh0 hmult ψ hψ hψc hψS hψ1
    have hA : 0 < lam * ‖h‖ := mul_pos hlam (norm_pos_iff.2 hh0)
    obtain ⟨Ψ, hΨ_def⟩ : ∃ Ψ : Euclid (m + 1) → ℝ,
        Ψ = fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Euclid (m + 1) → Euclid (m + 1),
        g = fun z => ((lam * ‖h‖)⁻¹ * Ψ z) • h := ⟨_, rfl⟩
    have hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
      rw [hΨ_def]; exact contDiff_infty.2 fun k => hΨs h k ℝ ψ hψ hψc
    have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := by
      rw [hg_def]; exact (contDiff_const.mul hΨsm).smul contDiff_const
    -- `g` is supported in the compact set `spt ψ + [0, 1] h ⊆ Q`
    obtain ⟨K, hK_def⟩ : ∃ K : Set (Euclid (m + 1)),
        K = (fun p : Euclid (m + 1) × ℝ => p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0:ℝ) 1) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := by
      rw [hK_def]
      exact (hψc.isCompact.prod isCompact_Icc).image
        (continuous_fst.add (continuous_snd.smul continuous_const))
    have hKQ : K ⊆ Q := by
      rw [hK_def]
      rintro _ ⟨⟨x, τ⟩, ⟨hx, hτ⟩, rfl⟩
      exact hseg x (hψS hx) τ hτ
    have hgK : ∀ z ∉ K, g z = 0 := by
      intro z hz
      have : Ψ z = 0 := by
        rw [hΨ_def]
        refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
        by_contra hne
        refine hz (hK_def ▸ ⟨⟨z - τ • h, τ⟩, ⟨subset_tsupport _ hne, Ioc_subset_Icc_self hτ⟩, ?_⟩)
        exact sub_add_cancel z (τ • h)
      rw [hg_def]; simp only [this, mul_zero, zero_smul]
    have hgc : HasCompactSupport g := HasCompactSupport.intro hKc hgK
    have hgQ : tsupport g ⊆ Q := (closure_minimal (fun z hz => by
      by_contra hzK; exact hz (hgK z hzK)) hKc.isClosed).trans hKQ
    -- `|Ψ| ≤ lam`, hence `‖g‖ ≤ 1`
    have hΨb : ∀ z, |Ψ z| ≤ lam := by
      intro z
      have hmeas : MeasurableSet {τ : ℝ | z - τ • h ∈ S} :=
        (hSo.preimage (continuous_const.sub (continuous_id.smul continuous_const))).measurableSet
      rw [hΨ_def]
      calc |∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)| = ‖∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)‖ := rfl
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, ‖ψ (z - τ • h)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
            ((integrable_indicator_iff hmeas).2 (integrable_const (1:ℝ)).integrableOn) ?_
          refine Filter.Eventually.of_forall fun τ => ?_
          show ‖ψ (z - τ • h)‖ ≤ {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ
          by_cases hτ : z - τ • h ∈ S
          · rw [indicator_of_mem (show τ ∈ {τ : ℝ | z - τ • h ∈ S} from hτ), Pi.one_apply]
            exact hψ1 (z - τ • h)
          · rw [indicator_of_notMem (show τ ∉ {τ : ℝ | z - τ • h ∈ S} from hτ),
              image_eq_zero_of_notMem_tsupport (fun h' => hτ (hψS h')), norm_zero]
        _ = (volume.restrict (Ioc (0:ℝ) 1)).real {τ : ℝ | z - τ • h ∈ S} :=
          integral_indicator_one hmeas
        _ ≤ lam := by
          rw [Measure.real, Measure.restrict_apply hmeas]
          exact ENNReal.toReal_le_of_le_ofReal hlam.le (hmult z)
    have hgb : ∀ z, ‖g z‖ ≤ 1 := by
      intro z
      rw [hg_def, norm_smul, norm_mul, norm_inv, Real.norm_of_nonneg hA.le, Real.norm_eq_abs]
      calc (lam * ‖h‖)⁻¹ * |Ψ z| * ‖h‖ ≤ (lam * ‖h‖)⁻¹ * lam * ‖h‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΨb z) (inv_nonneg.2 hA.le))
              (norm_nonneg h)
        _ = 1 := by rw [mul_assoc, inv_mul_cancel₀ hA.ne']
    -- `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`
    have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z) =
        (lam * ‖h‖)⁻¹ * (ψ z - ψ (z - h)) := by
      intro z
      have hd : HasFDerivAt g (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
          fderiv ℝ ψ (z - τ • h)).smulRight h) z := by
        rw [hg_def, hΨ_def]
        exact ((hΨd h ℝ ψ hψ hψc z).const_mul (lam * ‖h‖)⁻¹).smul_const h
      rw [hd.fderiv]
      refine (LinearMap.trace_smulRight (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
        fderiv ℝ ψ (z - τ • h) : Euclid (m + 1) →L[ℝ] ℝ) : Euclid (m + 1) →ₗ[ℝ] ℝ) h).trans ?_
      rw [ContinuousLinearMap.coe_coe, smul_apply, hΨh h ψ hψ z, smul_eq_mul]
    -- the hypothesis applied to `g`
    have hψb : ∀ x, ‖ψ x‖ ≤ 1 := hψ1
    have hint1 : Integrable fun x => ub x * ψ x :=
      hub_int.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hψb)
    have hint2 : Integrable fun x => ub x * ψ (x - h) :=
      hub_int.mul_bdd (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hψb _)
    have hint3 : Integrable fun x => ub (x + h) * ψ x :=
      (hub_int.comp_add_right h).mul_bdd hψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hψb)
    have key := hV g hgsm hgc hgQ hgb
    have e1 : ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
        (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
      calc ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)
          = ∫ y in Q, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) := by
            refine integral_congr_ae ?_
            filter_upwards [hub_ae] with y hy
            rw [htr y, hy]
        _ = ∫ y, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
              rw [hub_zero y hy, zero_mul]
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ y, ub y * ψ (y - h)) := by
            rw [← integral_sub hint1 hint2, ← integral_const_mul]
            congr 1; funext y; ring
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ x, ub (x + h) * ψ x) := by
            congr 2
            rw [← integral_add_right_eq_self (fun y => ub y * ψ (y - h)) h]
            simp only [add_sub_cancel_right]
        _ = (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
            rw [← integral_sub hint1 hint3, ← integral_neg]
            congr 2; funext x; ring
    rw [e1] at key
    have := mul_le_mul_of_nonneg_left key hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  /- Step 6: the `L¹` translation estimate `∫_S |ub (x + h) - ub x| ≤ 2 lam ‖h‖ V`. -/
  have hGEN : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∫ x in S, |ub (x + h) - ub x| ≤ 2 * (lam * ‖h‖ * V) := by
    intro S h lam hSo hseg hlam hmult
    by_cases hh : h = 0
    · subst hh; simp
    have hSQ : S ⊆ Q := fun x hx => by
      have := hseg x hx 0 ⟨le_rfl, zero_le_one⟩; rwa [zero_smul, add_zero] at this
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hSQ)
    refine hdual (fun x => ub (x + h) - ub x) S (lam * ‖h‖ * V)
      ((hub_int.comp_add_right h).sub hub_int)
      ((hub_meas.comp (measurable_add_const h)).sub hub_meas) hSo hSfin ?_
    intro ψ hψ hψc hψS hψ1
    have h1 := hweak S h lam hSo hseg hlam hh hmult ψ hψ hψc hψS hψ1
    have h2 := hweak S h lam hSo hseg hlam hh hmult (-ψ) hψ.neg hψc.neg
      (by rwa [tsupport_neg]) (fun x => by rw [Pi.neg_apply, abs_neg]; exact hψ1 x)
    have e2 : ∫ x, (ub (x + h) - ub x) * (-ψ) x = -∫ x, (ub (x + h) - ub x) * ψ x := by
      rw [← integral_neg]; congr 1; funext x; rw [Pi.neg_apply]; ring
    rw [e2] at h2
    rw [abs_le]; constructor <;> linarith only [h1, h2]
  clear hweak hdual hΨh hΨs hΨd
  /- Step 7: the Poincaré inequality.  Translating `y = x + h` and swapping the integrals,
  `∫_Q ∫_Q |ub y - ub x| ≤ ∫_{‖h‖ ≤ R} 2 ‖h‖ V dh`. -/
  have hnormle : ∀ v : Euclid (m + 1), (∀ i, |v i| ≤ 1) → ‖v‖ ≤ R := by
    intro v hv
    have h1 : ‖v‖ ^ 2 ≤ R := by
      rw [EuclideanSpace.norm_sq_eq, hR_def]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1:ℝ) := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_le_one_iff_abs_le_one _).2 (hv i)
        _ = m + 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
              Nat.cast_add, Nat.cast_one]
    exact (sq_le_sq₀ (norm_nonneg v) hR.le).1 (h1.trans (le_self_pow₀ hR1 two_ne_zero))
  have hnorm : ∀ x h : Euclid (m + 1), x ∈ Q → x + h ∈ Q → ‖h‖ ≤ R := fun x h hx hxh =>
    hnormle h fun i => by
      have h1 := hx i; have h2 := hxh i
      rw [PiLp.add_apply] at h2
      rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hnormQ : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy =>
    hnormle y fun i => abs_le.2 ⟨by linarith only [(hy i).1], (hy i).2.le⟩
  have hsegA : ∀ h : Euclid (m + 1), ∀ x ∈ (fun x => x + h) ⁻¹' Q ∩ Q,
      ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q := by
    rintro h x ⟨hxh, hx⟩ τ ⟨hτ0, hτ1⟩ i
    have h1 := hx i; have h2 := hxh i
    rw [PiLp.add_apply] at h2
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases le_total 0 (h i) with hhi | hhi
    · have p1 := mul_nonneg hτ0 hhi
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) hhi
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
    · have p1 := mul_nonneg hτ0 (neg_nonneg.2 hhi)
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) (neg_nonneg.2 hhi)
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
  have hAo : ∀ h : Euclid (m + 1), IsOpen ((fun x => x + h) ⁻¹' Q ∩ Q) := fun h =>
    (hQo.preimage (continuous_id.add continuous_const)).inter hQo
  have hTR : ∀ h : Euclid (m + 1),
      ∫ x in (fun x => x + h) ⁻¹' Q ∩ Q, |ub (x + h) - ub x| ≤ 2 * (‖h‖ * V) := by
    intro h
    have := hGEN _ h 1 (hAo h) (hsegA h) one_pos (fun z => by
      rw [ENNReal.ofReal_one]
      exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one]))
    rwa [one_mul] at this
  have hJ : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| ≤
      ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) := by
    have hΦ : (Function.uncurry fun x h : Euclid (m + 1) =>
          Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) =
        {p : Euclid (m + 1) × Euclid (m + 1) | p.2 + p.1 ∈ Q}.indicator
          (fun p => ENNReal.ofReal |ub (p.2 + p.1) - ub p.1|) := by
      funext ⟨x, h⟩
      simp only [Function.uncurry_apply_pair, Set.indicator_apply, mem_ofPred_eq]
    have hΦm : Measurable (Function.uncurry fun x h : Euclid (m + 1) =>
        Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) := by
      rw [hΦ]
      exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        ((hub_meas.comp (measurable_snd.add measurable_fst)).sub
          (hub_meas.comp measurable_fst)))).indicator
        (hQm.preimage (measurable_snd.add measurable_fst))
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x|
        = ∫⁻ x in Q, ∫⁻ h, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_indicator hQm, lintegral_add_right_eq_self]
      _ = ∫⁻ h, ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) :=
          lintegral_lintegral_swap hΦm.aemeasurable
      _ ≤ ∫⁻ h, (closedBall (0 : Euclid (m + 1)) R).indicator
            (fun _ => ENNReal.ofReal (2 * (R * V))) h := by
          refine lintegral_mono fun h => ?_
          have hAm := (hAo h).measurableSet
          have e1 : ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) =
              ∫⁻ x in (fun x => x + h) ⁻¹' Q ∩ Q, ENNReal.ofReal |ub (x + h) - ub x| := by
            rw [← Measure.restrict_restrict (hQm.preimage (measurable_add_const h)),
              ← lintegral_indicator (hQm.preimage (measurable_add_const h))]
            refine lintegral_congr fun x => ?_
            rw [add_comm h x]
            by_cases hx : x + h ∈ Q
            · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x => x + h) ⁻¹' Q from hx)]
            · rw [indicator_of_notMem hx,
                indicator_of_notMem (show x ∉ (fun x => x + h) ⁻¹' Q from hx)]
          have hint : IntegrableOn (fun x => |ub (x + h) - ub x|) ((fun x => x + h) ⁻¹' Q ∩ Q) :=
            ((hub_int.comp_add_right h).sub hub_int).abs.integrableOn
          rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => abs_nonneg _)]
          by_cases hh : h ∈ closedBall (0 : Euclid (m + 1)) R
          · rw [indicator_of_mem hh]
            refine ENNReal.ofReal_le_ofReal ((hTR h).trans ?_)
            have : ‖h‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hh
            have := mul_le_mul_of_nonneg_right this hV0
            linarith only [this]
          · rw [indicator_of_notMem hh]
            have hempty : (fun x => x + h) ⁻¹' Q ∩ Q = ∅ := by
              refine Set.eq_empty_of_forall_notMem fun x hx => hh ?_
              rw [mem_closedBall, dist_zero_right]; exact hnorm x h hx.2 hx.1
            rw [hempty, Measure.restrict_empty, integral_zero_measure, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) :=
          lintegral_indicator_const measurableSet_closedBall _
  clear hsegA hAo hnormle
  /- Step 8: the integer median `β`: the least integer with `|{ub ≤ β} ∩ Q| ≥ 1/2`. -/
  have hμprob : IsProbabilityMeasure (volume.restrict Q) :=
    isProbabilityMeasure_iff.2 (by rw [Measure.restrict_apply_univ, hQvol])
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∫ y in Q, |ub y| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM_def ▸ integral_nonneg fun y => abs_nonneg _
  have hmarkov : ∀ ε : ℝ, ε * (volume.restrict Q).real {y | ε ≤ |ub y|} ≤ M := fun ε =>
    hM_def ▸ mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hub_int.integrableOn.abs ε
  have hmeasle : ∀ c : ℝ, MeasurableSet {y | ub y ≤ c} := fun c =>
    measurableSet_le hub_meas measurable_const
  have hmeasge : ∀ c : ℝ, MeasurableSet {y | c ≤ ub y} := fun c =>
    measurableSet_le measurable_const hub_meas
  have hlow : ∀ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} → -(2 * M) ≤ k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (volume.restrict Q).real {y | ub y ≤ k} ≤
        (volume.restrict Q).real {y | -(k:ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y (hy : ub y ≤ k) => by
        show -(k:ℝ) ≤ |ub y|; linarith only [hy, neg_abs_le (ub y)])
    have h3 := mul_le_mul_of_nonneg_left (hk.trans h1)
      (by linarith only [hlt, hM0] : (0:ℝ) ≤ -(k:ℝ))
    linarith only [hmarkov (-(k:ℝ)), h3, hlt]
  have hex : ∃ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} := by
    refine ⟨⌊2 * M⌋ + 1, ?_⟩
    have hk₀ : 2 * M < ((⌊2 * M⌋ + 1 : ℤ) : ℝ) := by
      rw [Int.cast_add, Int.cast_one]; exact Int.lt_floor_add_one _
    have h2 : (volume.restrict Q).real {y | ub y ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y hy => by
        rw [mem_compl_iff, mem_ofPred_eq, not_le] at hy
        exact hy.le.trans (le_abs_self _))
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    by_contra h4
    rw [not_le] at h4
    have h5 := mul_le_mul_of_nonneg_left (show 1/2 ≤ (volume.restrict Q).real
      {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} by linarith only [h2, h3, h4])
      (by linarith only [hk₀, hM0] : (0:ℝ) ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    linarith only [h5, hmarkov ((⌊2 * M⌋ + 1 : ℤ) : ℝ), hk₀]
  obtain ⟨β, hβP, hβmin⟩ := Int.exists_least_of_bdd ⟨⌊-(2 * M)⌋, fun k hk =>
    Int.cast_le.1 ((Int.floor_le _).trans (hlow k hk))⟩ hex
  have hβge : 1/2 ≤ (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
    have hβ1 : ¬ (1/2 ≤ (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}) := fun h => by
      have := hβmin (β - 1) h; omega
    rw [not_le] at hβ1
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((β - 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    have h4 : (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
      rw [measureReal_def, measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hub_ae] with y hy
      intro hy'
      obtain ⟨z, hz⟩ := hint y
      rw [mem_compl_iff, mem_ofPred_eq, not_le, hy, hz] at hy'
      show (β:ℝ) ≤ ub y
      rw [hy, hz]
      have : β - 1 < z := by exact_mod_cast hy'
      exact_mod_cast (show β ≤ z by omega)
    linarith only [h3, h4, hβ1]
  have hβabs : |(β:ℝ)| ≤ 2 * M := by
    rcases le_or_gt 0 (β:ℝ) with h0 | h0
    · rw [abs_of_nonneg h0]
      have h2 : (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} ≤
          (volume.restrict Q).real {y | (β:ℝ) ≤ |ub y|} :=
        measureReal_mono fun y (hy : (β:ℝ) ≤ ub y) => hy.trans (le_abs_self _)
      linarith only [mul_le_mul_of_nonneg_left (hβge.trans h2) h0, hmarkov β]
    · rw [abs_of_neg h0]; linarith only [hlow β hβP]
  have hhalf : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → 1/2 ≤ (volume.restrict Q).real s →
      (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) := by
    intro s hs h
    rw [← Measure.restrict_apply hs, ← ofReal_measureReal (measure_ne_top _ _)]
    calc (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hhalf1 := hhalf _ (hmeasle β) hβP
  have hhalf2 := hhalf _ (hmeasge β) hβge
  -- `|ub x - β| ≤ 2 ∫_Q |ub y - ub x| dy`, since `β` is a median
  have hpt : ∀ x, ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
    intro x
    have hhalf' : ∀ a : ℝ≥0∞, a = 2 * (a * (1/2)) := fun a => by
      rw [one_div, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        mul_one]
    have hgm : Measurable fun y => ENNReal.ofReal |ub y - ub x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hub_meas.sub measurable_const))
    have key : ∀ s : Set (Euclid (m + 1)), (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) →
        (∀ y ∈ s, |ub x - β| ≤ |ub y - ub x|) →
        ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
      intro s hs hle
      rw [hhalf' (ENNReal.ofReal |ub x - β|)]
      refine mul_le_mul_right ?_ 2
      calc ENNReal.ofReal |ub x - β| * (1/2) ≤ ENNReal.ofReal |ub x - β| * volume (s ∩ Q) :=
            mul_le_mul_right hs _
        _ = ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub x - β| := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub y - ub x| :=
            setLIntegral_mono hgm fun y hy => ENNReal.ofReal_le_ofReal (hle y hy.1)
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono_set inter_subset_right
    rcases le_total (β:ℝ) (ub x) with hx | hx
    · refine key _ hhalf1 fun y (hy : ub y ≤ β) => ?_
      rw [abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm]
      exact (by linarith only [hy] : ub x - β ≤ ub x - ub y).trans (le_abs_self _)
    · refine key _ hhalf2 fun y (hy : (β:ℝ) ≤ ub y) => ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx)]
      exact (by linarith only [hy] : β - ub x ≤ ub y - ub x).trans (le_abs_self _)
  have hP1 : ∫ y in Q, |ub y - β| ≤ CP * V := by
    have hlin : ∫⁻ x in Q, ENNReal.ofReal |ub x - β| ≤
        2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R)) := by
      calc ∫⁻ x in Q, ENNReal.ofReal |ub x - β|
          ≤ ∫⁻ x in Q, 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono hpt
        _ = 2 * ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| :=
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
        _ ≤ _ := mul_le_mul_right hJ 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => |ub y - (β:ℝ)|)
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (continuous_abs.measurable.comp (hub_meas.sub measurable_const)).aestronglyMeasurable]
    calc (∫⁻ x in Q, ENNReal.ofReal |ub x - β|).toReal
        ≤ (2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne)) hlin
      _ = CP * V := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofNat, hCP_def]; ring
  have hβM : |(β:ℝ)| ≤ 2 * ∫ y in Q, |u y| := by
    have : ∫ y in Q, |u y| = M := by
      rw [hM_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hβabs
  clear hpt hhalf hhalf1 hhalf2 hlow hex hβmin hβge hβP hβabs hmarkov hJ hmeasle hmeasge hμprob
    hM0 hM_def hint
  /- Step 9: slabs `{y ∈ Q | a < y i < a + s}`.  Translating along `e i` compares the integrals
  of `|ub - β|` over two slabs of width `s` up to `2 s V`; averaging over the `N` slabs of width
  `1/N` bounds a boundary slab by `(∫_Q |ub - β| + 2 V) / N`. -/
  have hcoord : ∀ (i j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
      (x + t • EuclideanSpace.single i (1:ℝ)) j = if j = i then x j + t else x j := by
    intro i j x t
    by_cases hj : j = i <;> simp [hj]
  have hslabo : ∀ (i : Fin (m + 1)) (a s : ℝ),
      IsOpen {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := by
    intro i a s
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact hQo.inter ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
  have hslab : ∀ (i : Fin (m + 1)) (s a a' : ℝ), 0 < s → 0 ≤ a → a + s ≤ 1 → 0 ≤ a' →
      a' + s ≤ 1 →
      ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s}, |ub y - β| ≤
        (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s}, |ub y - β|) +
          2 * (s * V) := by
    intro i s a a' hs ha has ha' has'
    rcases eq_or_ne a a' with haa | haa
    · subst haa; linarith only [mul_nonneg hs.le hV0]
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = a' - a := ⟨_, rfl⟩
    have ht : t ≠ 0 := by rw [ht_def]; exact sub_ne_zero.2 (Ne.symm haa)
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (r : ℝ),
        (x + r • e) j = if j = i then x j + r else x j := by
      subst he_def; exact fun j x r => hcoord i j x r
    obtain ⟨S, hS_def⟩ : ∃ S : Set (Euclid (m + 1)),
        S = {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := ⟨_, rfl⟩
    obtain ⟨S', hS'_def⟩ : ∃ S' : Set (Euclid (m + 1)),
        S' = {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s} := ⟨_, rfl⟩
    rw [← hS_def, ← hS'_def]
    have hSo : IsOpen S := hS_def ▸ hslabo i a s
    have hSm : MeasurableSet S := hSo.measurableSet
    have hS'm : MeasurableSet S' := (hS'_def ▸ hslabo i a' s).measurableSet
    have hSfin : volume S ≠ ⊤ := by
      refine ne_top_of_le_ne_top hQfin (measure_mono fun y hy => ?_)
      rw [hS_def] at hy; exact hy.1
    have hnh : ‖t • e‖ = |t| := by
      rw [he_def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hmem : ∀ x, x ∈ S ↔ x + t • e ∈ S' := by
      intro x
      rw [hS_def, hS'_def]
      show (x ∈ Q ∧ a < x i ∧ x i < a + s) ↔
        (x + t • e ∈ Q ∧ a' < (x + t • e) i ∧ (x + t • e) i < a' + s)
      rw [hce, ite_eq_left rfl]
      constructor
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        rw [hce]; split_ifs with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha', has']
        · exact hxQ j
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        have := hxQ j
        rw [hce] at this
        split_ifs at this with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha, has]
        · exact this
    have hgen := hGEN S (t • e) (s / |t|) hSo (by
        rintro x hx τ ⟨hτ0, hτ1⟩ j
        rw [hS_def] at hx
        obtain ⟨hxQ, h1, h2⟩ := hx
        rw [smul_smul, hce]
        split_ifs with hj
        · subst hj
          have e1 : τ * t = τ * a' - τ * a := by rw [ht_def]; ring
          have p1 := mul_nonneg (sub_nonneg.2 hτ1) ha
          have p2 := mul_nonneg hτ0 ha'
          have p3 := mul_nonneg (sub_nonneg.2 hτ1) (by linarith only [has] : (0:ℝ) ≤ 1 - a - s)
          have p4 := mul_nonneg hτ0 (by linarith only [has'] : (0:ℝ) ≤ 1 - a' - s)
          constructor <;> linarith only [h1, h2, e1, p1, p2, p3, p4]
        · exact hxQ j) (div_pos hs (abs_pos.2 ht)) (fun z => by
        have hsub : {τ : ℝ | z - τ • (t • e) ∈ S} ∩ Ioc (0:ℝ) 1 ⊆
            (fun τ => t * τ) ⁻¹' Ioo (z i - a - s) (z i - a) := by
          rintro τ ⟨hτ, -⟩
          rw [mem_ofPred_eq, hS_def] at hτ
          have h1 := hτ.2
          have hzi : (z - τ • (t • e)) i = z i - τ * t := by
            rw [smul_smul, sub_eq_add_neg, ← neg_smul, hce, ite_eq_left rfl, ← sub_eq_add_neg]
          rw [hzi] at h1
          rw [mem_preimage, mem_Ioo, mul_comm]
          exact ⟨by linarith only [h1.2], by linarith only [h1.1]⟩
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [Real.volume_preimage_mul_left ht, Real.volume_Ioo, ← ENNReal.ofReal_mul (abs_nonneg _),
          abs_inv, show z i - a - (z i - a - s) = s by ring, div_eq_inv_mul])
    rw [hnh, div_mul_cancel₀ s (abs_ne_zero.2 ht)] at hgen
    have htrans : ∫ x in S, |ub (x + t • e) - β| = ∫ y in S', |ub y - β| := by
      rw [← integral_indicator hSm, ← integral_indicator hS'm,
        ← integral_add_right_eq_self (fun y => S'.indicator (fun y => |ub y - β|) y) (t • e)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hi1 : IntegrableOn (fun x => |ub (x + t • e) - β|) S :=
      ((hub_int.comp_add_right (t • e)).integrableOn.sub (integrableOn_const hSfin)).abs
    have hi2 : IntegrableOn (fun x => |ub (x + t • e) - ub x|) S :=
      ((hub_int.comp_add_right (t • e)).sub hub_int).abs.integrableOn
    calc ∫ y in S, |ub y - β|
        ≤ ∫ x in S, (|ub (x + t • e) - ub x| + |ub (x + t • e) - β|) := by
          refine setIntegral_mono_on ((hub_int.integrableOn.sub (integrableOn_const hSfin)).abs)
            (hi2.add hi1) hSm fun x _ => ?_
          have := abs_sub_le (ub x) (ub (x + t • e)) β
          rwa [abs_sub_comm (ub x) (ub (x + t • e))] at this
      _ = (∫ x in S, |ub (x + t • e) - ub x|) + ∫ x in S, |ub (x + t • e) - β| :=
          integral_add hi2 hi1
      _ ≤ (∫ y in S', |ub y - β|) + 2 * (s * V) := by rw [htrans]; linarith only [hgen]
  have hstrip : ∀ (i : Fin (m + 1)) (N : ℕ), 1 ≤ N → ∀ a : ℝ, 0 ≤ a → a + 1 / N ≤ 1 →
      (N:ℝ) * ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
        (∫ y in Q, |ub y - β|) + 2 * V := by
    intro i N hN a ha haN
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have hk : ∀ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
          (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N},
            |ub y - β|) + 2 * (1 / N * V) := fun k hk =>
      hslab i (1 / N) a (k / N) (one_div_pos.2 hNpos) ha haN
        (div_nonneg (Nat.cast_nonneg k) hNpos.le)
        (by rw [← add_div, div_le_one hNpos]
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hk))
    have hsum := Finset.sum_le_sum hk
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hsum
    have hdisj : (↑(Finset.range N) : Set ℕ).Pairwise (Disjoint on fun k : ℕ =>
        {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}) := by
      intro k _ k' _ hkk'
      rw [Function.onFun, Set.disjoint_left]
      rintro y ⟨_, h1, h2⟩ ⟨_, h1', h2'⟩
      rcases lt_or_gt_of_ne hkk' with hlt | hlt
      · have : (k:ℝ) / N + 1 / N ≤ k' / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2, h1']
      · have : (k':ℝ) / N + 1 / N ≤ k / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2', h1]
    have hint : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hunion : ∑ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}, |ub y - β|
          ≤ ∫ y in Q, |ub y - β| := by
      rw [← integral_biUnion_finset (Finset.range N) (fun k _ => (hslabo i _ _).measurableSet)
        hdisj (fun k _ => hint.mono_set (fun y hy => hy.1))]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_
      refine LE.le.eventuallySubset ?_
      intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨k, _, hy⟩ := hy
      exact hy.1
    have : (N:ℝ) * (2 * (1 / N * V)) = 2 * V := by
      rw [mul_left_comm, ← mul_assoc (N:ℝ), mul_one_div_cancel hNpos.ne', one_mul]
    linarith only [hsum, hunion, this]
  clear hslab hGEN
  /- Step 10: difference quotients.  For `F` continuous with `|F| ≤ 1` and `s = 1/(2N)`,
  `∫_Q (ub - β) (F (· + s e) - F) / s` is the integral of `F` against the difference
  `w (· - s e) - w` of `w = (ub - β) 1_Q`, which is controlled by a translation estimate and the
  two boundary slabs. -/
  have hDQ : ∀ (i : Fin (m + 1)) (F : Euclid (m + 1) → ℝ), Continuous F → (∀ y, |F y| ≤ 1) →
      ∀ N : ℕ, 1 ≤ N →
      |∫ y in Q, (ub y - β) * ((2 * N : ℝ) *
        (F (y + (2 * N : ℝ)⁻¹ • EuclideanSpace.single i (1:ℝ)) - F y))|
        ≤ 10 * V + 4 * ∫ y in Q, |ub y - β| := by
    intro i F hFc hF1 N hN
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
        (x + t • e) j = if j = i then x j + t else x j := by
      subst he_def; exact fun j x t => hcoord i j x t
    have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 * N := ⟨_, rfl⟩
    rw [← he_def, ← hc_def]
    have hc : 0 < c := hc_def ▸ mul_pos two_pos hNpos
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = c⁻¹ := ⟨_, rfl⟩
    rw [← hs_def]
    have hs : 0 < s := hs_def ▸ inv_pos.2 hc
    have hcs : c * s = 1 := hs_def ▸ mul_inv_cancel₀ hc.ne'
    have hsN : s < 1 / N := by
      rw [hs_def, hc_def, one_div]
      exact inv_strictAnti₀ hNpos (by linarith only [hNpos])
    have hcm : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)),
        (x - s • e) j = if j = i then x j - s else x j := by
      intro j x
      rw [sub_eq_add_neg, ← neg_smul, hce, ← sub_eq_add_neg]
    obtain ⟨wb, hwb_def⟩ : ∃ wb : Euclid (m + 1) → ℝ, wb = Q.indicator fun y => ub y - β :=
      ⟨_, rfl⟩
    have hwb_int : Integrable wb := hwb_def ▸
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).integrable_indicator hQm
    have hFb : ∀ y, ‖F y‖ ≤ 1 := hF1
    have hi1 : Integrable fun y => wb y * F (y + s • e) :=
      hwb_int.mul_bdd (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => hFb _)
    have hi2 : Integrable fun y => wb y * F y :=
      hwb_int.mul_bdd hFc.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
    have hi3 : Integrable fun x => wb (x - s • e) * F x :=
      (hwb_int.comp_sub_right (s • e)).mul_bdd hFc.aestronglyMeasurable
        (Filter.Eventually.of_forall hFb)
    have e1 : ∫ y in Q, (ub y - β) * (c * (F (y + s • e) - F y)) =
        c * ∫ x, (wb (x - s • e) - wb x) * F x := by
      rw [← integral_indicator hQm]
      have : ∀ y, Q.indicator (fun y => (ub y - β) * (c * (F (y + s • e) - F y))) y =
          c * (wb y * F (y + s • e) - wb y * F y) := fun y => by
        rw [indicator_mul_left, ← hwb_def]; ring
      simp only [this]
      rw [integral_const_mul, integral_sub hi1 hi2,
        ← integral_sub_right_eq_self (fun y => wb y * F (y + s • e)) (s • e)]
      simp only [sub_add_cancel]
      rw [← integral_sub hi3 hi2]
      simp only [sub_mul]
    -- the pointwise bound: interior differences and the two boundary slabs
    obtain ⟨A, hA_def⟩ : ∃ A : Set (Euclid (m + 1)), A = (fun x => x + s • e) ⁻¹' Q ∩ Q :=
      ⟨_, rfl⟩
    obtain ⟨S0, hS0_def⟩ : ∃ S0 : Set (Euclid (m + 1)),
        S0 = {y : Euclid (m + 1) | y ∈ Q ∧ (0:ℝ) < y i ∧ y i < 0 + 1 / N} := ⟨_, rfl⟩
    obtain ⟨S1, hS1_def⟩ : ∃ S1 : Set (Euclid (m + 1)),
        S1 = {y : Euclid (m + 1) | y ∈ Q ∧ (1 - 1 / N : ℝ) < y i ∧ y i < (1 - 1 / N) + 1 / N} :=
      ⟨_, rfl⟩
    have hAm : MeasurableSet A := hA_def ▸ (hQm.preimage (measurable_add_const _)).inter hQm
    have hS0m : MeasurableSet S0 := hS0_def ▸ (hslabo i _ _).measurableSet
    have hS1m : MeasurableSet S1 := hS1_def ▸ (hslabo i _ _).measurableSet
    have hpt : ∀ x, |wb (x - s • e) - wb x| ≤
        A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) +
          S0.indicator (fun y => |ub y - β|) x +
          S1.indicator (fun y => |ub y - β|) (x - s • e) := by
      intro x
      have n1 := indicator_nonneg (fun z _ => abs_nonneg (ub (z + s • e) - ub z)) (x - s • e)
        (s := A)
      have n2 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) x (s := S0)
      have n3 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) (x - s • e) (s := S1)
      rw [hwb_def]
      by_cases hx : x ∈ Q <;> by_cases hxs : x - s • e ∈ Q
      · have hA : x - s • e ∈ A := by rw [hA_def]; exact ⟨by rwa [mem_preimage, sub_add_cancel], hxs⟩
        rw [indicator_of_mem hx, indicator_of_mem hxs, indicator_of_mem hA, sub_add_cancel,
          show ub (x - s • e) - (β:ℝ) - (ub x - β) = -(ub x - ub (x - s • e)) by ring, abs_neg]
        linarith only [n2, n3]
      · have hS0 : x ∈ S0 := by
          rw [hS0_def]
          refine ⟨hx, (hx i).1, ?_⟩
          by_contra hge
          rw [not_lt] at hge
          apply hxs
          intro j
          rw [hcm]
          split_ifs with hj
          · subst hj; constructor <;> linarith only [(hx j).2, hge, hsN, hs]
          · exact hx j
        rw [indicator_of_mem hx, indicator_of_notMem hxs, indicator_of_mem hS0, zero_sub, abs_neg]
        linarith only [n1, n3]
      · have hS1 : x - s • e ∈ S1 := by
          rw [hS1_def]
          refine ⟨hxs, ?_, ?_⟩
          · by_contra hle
            rw [not_lt, hcm, ite_eq_left rfl] at hle
            apply hx
            intro j
            have := hxs j
            rw [hcm] at this
            split_ifs at this with hj
            · subst hj; constructor <;> linarith only [this.1, hle, hsN, hs]
            · exact this
          · have := (hxs i).2; linarith only [this]
        rw [indicator_of_notMem hx, indicator_of_mem hxs, indicator_of_mem hS1, sub_zero]
        linarith only [n1, n2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hxs, sub_zero, abs_zero]
        linarith only [n1, n2, n3]
    -- integrate the three terms
    have hg1 : Integrable fun z => |ub (z + s • e) - ub z| :=
      ((hub_int.comp_add_right _).sub hub_int).abs
    have hg2 : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hT1i : Integrable fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) :=
      (hg1.indicator hAm).comp_sub_right (s • e)
    have hT2i : Integrable (S0.indicator fun y => |ub y - β|) :=
      (hg2.mono_set (fun y hy => by rw [hS0_def] at hy; exact hy.1)).integrable_indicator hS0m
    have hT3i : Integrable fun x => S1.indicator (fun y => |ub y - β|) (x - s • e) :=
      ((hg2.mono_set (fun y hy => by rw [hS1_def] at hy; exact hy.1)).integrable_indicator
        hS1m).comp_sub_right (s • e)
    have hI1 : ∫ x, A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) ≤ 2 * (s * V) := by
      rw [integral_sub_right_eq_self (fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) x)
        (s • e), integral_indicator hAm, hA_def]
      have := hTR (s • e)
      rwa [norm_smul, hne, mul_one, Real.norm_of_nonneg hs.le] at this
    have hI3 : ∫ x, S1.indicator (fun y => |ub y - β|) (x - s • e) = ∫ y in S1, |ub y - β| := by
      rw [integral_sub_right_eq_self (fun x => S1.indicator (fun y => |ub y - β|) x) (s • e),
        integral_indicator hS1m]
    have hb2 : (N:ℝ) * ∫ y in S0, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS0_def ▸
      hstrip i N hN 0 le_rfl (by rw [zero_add, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
    have hb3 : (N:ℝ) * ∫ y in S1, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS1_def ▸
      hstrip i N hN (1 - 1 / N) (by rw [sub_nonneg, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
        (by rw [sub_add_cancel])
    have hmain : ∫ x, |wb (x - s • e) - wb x| ≤
        2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β| := by
      refine (integral_mono ((hwb_int.comp_sub_right _).sub hwb_int).abs
        ((hT1i.add hT2i).add hT3i) hpt).trans ?_
      rw [integral_add' (hT1i.add hT2i) hT3i, integral_add' hT1i hT2i, integral_indicator hS0m, hI3]
      linarith only [hI1]
    have hbound : |∫ x, (wb (x - s • e) - wb x) * F x| ≤ ∫ x, |wb (x - s • e) - wb x| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hwb_int.comp_sub_right _).sub hwb_int).abs
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x)
    rw [e1, abs_mul, abs_of_pos hc]
    have h5 := mul_le_mul_of_nonneg_left (hbound.trans hmain) hc.le
    have h6 : c * (2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β|) =
        2 * (c * s) * V + 2 * ((N:ℝ) * ∫ y in S0, |ub y - β|) +
          2 * ((N:ℝ) * ∫ y in S1, |ub y - β|) := by
      rw [hc_def]; ring
    rw [h6, hcs] at h5
    linarith only [h5, hb2, hb3]
  clear hstrip hslabo hcoord hTR
  /- Step 11: the boundary estimate (3): write `div G = ∑ᵢ ∂ᵢ Gᵢ` and pass to the limit in the
  difference quotients by dominated convergence. -/
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ y in Q, |ub y - β| := ⟨_, rfl⟩
  rw [← hI_def] at hDQ hP1
  have hwi : IntegrableOn (fun y => ub y - β) Q :=
    hub_int.integrableOn.sub (integrableOn_const hQfin)
  have h3 : ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) →
      |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (m + 1) * (10 * V + 4 * I) := by
    intro G hG hG1
    have hG1' : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
    have hdG : Continuous (fderiv ℝ G) := hG1'.continuous_fderiv one_ne_zero
    have hGd : ∀ y, HasFDerivAt G (fderiv ℝ G y) y := fun y =>
      (hG1'.differentiable one_ne_zero y).hasFDerivAt
    have hterm : ∀ i : Fin (m + 1),
        |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| ≤
          10 * V + 4 * I := by
      intro i
      obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
      rw [← he_def]
      have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
      obtain ⟨Fi, hFi_def⟩ : ∃ Fi : Euclid (m + 1) → ℝ, Fi = fun y => G y i := ⟨_, rfl⟩
      have hFid : ∀ y, HasFDerivAt Fi ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y)) y :=
        fun y => by
          rw [hFi_def]; exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y (hGd y)
      have hFic : Continuous Fi := by
        rw [hFi_def]; exact (EuclideanSpace.proj i).continuous.comp hG.continuous
      have hFi1 : ∀ y, |Fi y| ≤ 1 := fun y => by
        rw [hFi_def, ← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (G y) i).trans (hG1 y)
      have hdFc : Continuous fun y => (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y) :=
        continuous_const.clm_comp hdG
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) (R + 1)).exists_bound_of_continuousOn
        hdFc.continuousOn
      have hC' : ∀ y ∈ closedBall (0 : Euclid (m + 1)) (R + 1), ‖fderiv ℝ Fi y‖ ≤ C :=
        fun y hy => by rw [(hFid y).fderiv]; exact hC y hy
      have hmvt : ∀ y ∈ Q, ∀ t : ℝ, 0 < t → |Fi (y + t • e) - Fi y| ≤ C * t ∨ 1 < t := by
        intro y hy t ht0
        rcases le_or_gt t 1 with ht1 | ht1
        · left
          have hny := hnormQ y hy
          have hyK : y ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]; linarith only [hny]
          have hyK' : y + t • e ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le]
            linarith only [hny, ht1]
          have := (convex_closedBall (0 : Euclid (m + 1)) (R + 1)).norm_image_sub_le_of_norm_fderiv_le
            (fun z _ => (hFid z).differentiableAt) hC' hyK hyK'
          rwa [add_sub_cancel_left, norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le,
            Real.norm_eq_abs] at this
        · right; exact ht1
      obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun N => 2 * ((N + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have hcpos : ∀ N, 0 < c N := fun N => by
        rw [hc_def]; exact mul_pos two_pos (Nat.cast_pos.2 N.succ_pos)
      have hc1 : ∀ N, ¬ 1 < (c N)⁻¹ := fun N => by
        rw [not_lt, inv_le_one₀ (hcpos N), hc_def]
        have : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.one_le_cast.2 N.succ_pos
        linarith only [this]
      have hctend : Tendsto (fun N => ‖c N‖) atTop atTop := by
        have : (fun N => ‖c N‖) = fun N : ℕ => 2 * ((N + 1 : ℕ) : ℝ) := by
          funext N; rw [Real.norm_of_nonneg (hcpos N).le, hc_def]
        rw [this]
        exact Tendsto.const_mul_atTop two_pos
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hlim : Tendsto
          (fun N => ∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y)))
          atTop (𝓝 (∫ y in Q, (ub y - β) * (fderiv ℝ G y e) i)) := by
        refine tendsto_integral_of_dominated_convergence (fun y => |ub y - β| * C) (fun N => ?_)
          (hwi.abs.mul_const C) (fun N => ?_) ?_
        · exact (hub_meas.sub measurable_const).aestronglyMeasurable.mul
            (continuous_const.mul ((hFic.comp (continuous_id.add continuous_const)).sub
              hFic)).aestronglyMeasurable
        · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun y hy => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hcpos N)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (hmvt y hy (c N)⁻¹ (inv_pos.2 (hcpos N))).resolve_right (hc1 N)
          calc c N * |Fi (y + (c N)⁻¹ • e) - Fi y| ≤ c N * (C * (c N)⁻¹) :=
                mul_le_mul_of_nonneg_left this (hcpos N).le
            _ = C := by rw [mul_comm C, ← mul_assoc, mul_inv_cancel₀ (hcpos N).ne', one_mul]
        · refine Filter.Eventually.of_forall fun y => ?_
          have := (hFid y).lim e hctend
          simp only [smul_eq_mul] at this
          exact this.const_mul _
      have hbd : ∀ N, |∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y))| ≤
          10 * V + 4 * I := fun N => by
        have := hDQ i Fi hFic hFi1 (N + 1) (by omega)
        rwa [← he_def, show (2 * ((N + 1 : ℕ) : ℝ)) = c N by rw [hc_def]] at this
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∑ i, (fderiv ℝ G y (EuclideanSpace.single i 1)) i := by
      intro y
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis]
      simp [Matrix.trace, LinearMap.toMatrix_apply]
    have hint_i : ∀ i : Fin (m + 1), Integrable
        (fun y => (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i) (volume.restrict Q) := by
      intro i
      have hcont : Continuous fun y => (fderiv ℝ G y (EuclideanSpace.single i 1)) i :=
        (EuclideanSpace.proj i).continuous.comp (hdG.clm_apply continuous_const)
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) R).exists_bound_of_continuousOn
        hcont.continuousOn
      refine hwi.mul_bdd hcont.aestronglyMeasurable ((ae_restrict_iff' hQm).2
        (Filter.Eventually.of_forall fun y hy => hC y ?_))
      rw [mem_closedBall, dist_zero_right]; exact hnormQ y hy
    calc |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)|
        = |∑ i, ∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| := by
          rw [← integral_finsetSum _ fun i _ => hint_i i]
          congr 2; funext y
          rw [htr y, Finset.mul_sum]
      _ ≤ ∑ i, |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), (10 * V + 4 * I) := Finset.sum_le_sum fun i _ => hterm i
      _ = (m + 1) * (10 * V + 4 * I) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
            Nat.cast_one]
  /- Conclusion. -/
  have hm0 : (0:ℝ) ≤ m + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
  have hcV : CP * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have := mul_nonneg hm0 (by linarith only [hCP] : (0:ℝ) ≤ 10 + 4 * CP)
    linarith only [this]
  refine ⟨β, ?_, hβM, ?_⟩
  · have : ∫ y in Q, |u y - β| = I := by
      rw [hI_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hP1.trans hcV
  · intro G hG hG1
    have : ∫ y in Q, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
      integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]
    refine (h3 G hG hG1).trans ?_
    have h1 : (m + 1) * (10 * V + 4 * I) ≤ (m + 1) * (10 * V + 4 * (CP * V)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP1]) hm0
    have h2 : (m + 1) * (10 * V + 4 * (CP * V)) = (m + 1) * (10 + 4 * CP) * V := by ring
    have h4 : (m + 1) * (10 + 4 * CP) * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V :=
      mul_le_mul_of_nonneg_right (by linarith only [hCP]) hV0
    linarith only [h1, h2, h4]
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
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

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
