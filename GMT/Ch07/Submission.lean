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

/-- **Radial tangency from a constant density ratio** (Simon Ch. 4, 3.6 with `H = 0` and centre
`0`, as used in the proof of 7.4.5).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in `ℝᴾ`
and `μ = θ Hⁿ⌞M`.  If `v(M, θ)` is stationary in `ℝᴾ`, `x ↦ p_{TₓM}` is `μ`-measurable and
`μ(B̄_ρ(0)) = ρⁿ μ(B̄_1(0))` for every `ρ > 0`, then `p_{TₓM}(x) = x` for `μ`-a.e. `x`.

For `n = 0` all balls have the same mass, so `μ` is carried by `{0}`.  For `n ≥ 1` the ball masses
fix the image of `μ` under `x ↦ ‖x‖` as `μ(B̄_1) n tⁿ⁻¹ dt` on `(0, ∞)`.  Testing stationarity
with `X(x) = η(‖x‖²) x`, `η' = −max(r² − ·, 0)`, whose tangential divergence is
`n η(‖x‖²) + 2 η'(‖x‖²) ‖pₓ x‖²` (4.3.2), and subtracting `∫ (n η(‖x‖²) + 2 η'(‖x‖²) ‖x‖²) dμ = 0`
gives `∫ max(r² − ‖x‖², 0) ‖x − pₓ x‖² dμ = 0` for every `r > 0`: the defect term of the
monotonicity identity 4.3.6 vanishes. -/
theorem Submission.stationary_imrep_radial_tangency_of_ball_ratio : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ ρ : ℝ, 0 < ρ → R.measure (closedBall (0 : Euclid P) ρ) = ENNReal.ofReal (ρ ^ n) * R.measure (closedBall (0 : Euclid P) 1)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x := by
  intro P n R hstat hproj hratio
  -- Step 1: `μ = θ Hⁿ⌞M` is finite on compact sets.
  have hfin : IsFiniteMeasureOnCompacts R.measure := by
    refine ⟨fun K hK => ?_⟩
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult K hK (subset_univ K))
  have hball_fin : ∀ r : ℝ, R.measure (closedBall (0 : Euclid P) r) ≠ ∞ :=
    fun r => (isCompact_closedBall 0 r).measure_lt_top.ne
  have hc : R.measure (closedBall (0 : Euclid P) 1) ≠ ∞ := hball_fin 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: all balls have the same mass, so `μ` is carried by the origin.
    have hann : ∀ j : ℕ, R.measure (closedBall (0 : Euclid P) ((j : ℝ) + 1) \
        closedBall 0 (1 / ((j : ℝ) + 1))) = 0 := by
      intro j
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hsub : closedBall (0 : Euclid P) (1 / ((j : ℝ) + 1)) ⊆
          closedBall 0 ((j : ℝ) + 1) := by
        refine closedBall_subset_closedBall ?_
        rw [div_le_iff₀ hj]
        nlinarith
      rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet (hball_fin _),
        hratio _ hj, hratio (1 / ((j : ℝ) + 1)) (by positivity)]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hann)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    obtain ⟨j, hj⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj1 : ‖x‖ < (j : ℝ) + 1 := by
      have := le_max_left ‖x‖ (1 / ‖x‖)
      linarith
    have hj2 : 1 / ((j : ℝ) + 1) < ‖x‖ := by
      have h3 := le_max_right ‖x‖ (1 / ‖x‖)
      rw [div_lt_iff₀ hjpos]
      have h4 : 1 / ‖x‖ < (j : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hxpos] at h4
      linarith
    refine mem_iUnion.2 ⟨j, ?_⟩
    simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le]
    exact ⟨hj1.le, hj2⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
    -- Step 2: `Tₓ = approxTangentPlane` is an `n`-plane for `μ`-a.e. `x` (`R.orients`).
    have hrank : ∀ᵐ x ∂R.measure,
        Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier x) = m + 1 := by
      have hac : R.measure ≪ μHE[m + 1].restrict R.carrier :=
        withDensity_absolutelyContinuous _ _
      refine hac.ae_le ?_
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, hQ, -⟩ := hx
      have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier x Q := ⟨Q, hQ⟩
      rw [approxTangentPlane, dite_eq_left h]
      exact h.choose_spec.finrank_eq
    -- The origin is not an atom: `μ{0} ≤ μ(B̄_ε) = εⁿ μ(B̄₁) → 0`.
    have hzero : R.measure {0} = 0 := by
      have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (m + 1)) *
          R.measure (closedBall (0 : Euclid P) 1)) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun ε : ℝ => ε ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
          have h : Tendsto (fun ε : ℝ => ε ^ (m + 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (m + 1))) :=
            (continuous_pow (m + 1)).tendsto 0
          rw [zero_pow (Nat.succ_ne_zero m)] at h
          exact h.mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
      refine nonpos_iff_eq_zero.1 (ge_of_tendsto hlim ?_)
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [← hratio ε hε]
      exact measure_mono (singleton_subset_iff.2 (mem_closedBall_self (le_of_lt hε)))
    -- Ball masses for every real radius.
    have hcdf : ∀ t : ℝ, R.measure (closedBall (0 : Euclid P) t) =
        R.measure (closedBall (0 : Euclid P) 1) * ENNReal.ofReal (max t 0 ^ (m + 1)) := by
      intro t
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · rw [closedBall_eq_empty.2 ht, measure_empty, max_eq_right ht.le]
        simp
      · rw [closedBall_zero, hzero]
        simp
      · rw [hratio t ht, max_eq_left ht.le, mul_comm]
    -- Step 5 (radial form): the image of `μ` under `x ↦ ‖x‖` is `μ(B̄₁) · n tⁿ⁻¹ dt` on `(0, ∞)`.
    set ν : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal (((m : ℝ) + 1) * t ^ m)) with hν
    have hνIoc : ∀ a b : ℝ, a < b → ν (Ioc a b) =
        ENNReal.ofReal (max b 0 ^ (m + 1)) - ENNReal.ofReal (max a 0 ^ (m + 1)) := by
      intro a b hab
      rw [hν, withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        Ioc_inter_Ioi]
      rcases le_or_gt b (max a 0) with hba | hab'
      · have hb0 : b ≤ 0 := by
          rcases le_total a 0 with ha | ha
          · rwa [max_eq_right ha] at hba
          · rw [max_eq_left ha] at hba
            exact absurd hab (not_lt.2 hba)
        rw [Ioc_eq_empty (not_lt.2 hba), Measure.restrict_empty, lintegral_zero_measure,
          max_eq_right hb0, max_eq_right (hab.le.trans hb0)]
        simp
      · have ha0 : 0 ≤ max a 0 := le_max_right _ _
        rw [max_eq_left (ha0.trans hab'.le)]
        have hcont : Continuous fun t : ℝ => ((m : ℝ) + 1) * t ^ m := by fun_prop
        rw [← ofReal_integral_eq_lintegral_ofReal
            (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht =>
              mul_nonneg (by positivity) (pow_nonneg (ha0.trans ht.1.le) m))),
          ← intervalIntegral.integral_of_le hab'.le,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => t ^ (m + 1))
            (fun t _ => by simpa using hasDerivAt_pow (m + 1) t) (hcont.intervalIntegrable _ _),
          ENNReal.ofReal_sub _ (pow_nonneg ha0 _)]
    have hmap : R.measure.map (fun x : Euclid P => ‖x‖) =
        R.measure (closedBall (0 : Euclid P) 1) • ν := by
      refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
      · rw [Measure.map_apply continuous_norm.measurable measurableSet_Ioc]
        refine ne_top_of_le_ne_top (hball_fin b) (measure_mono fun x hx => ?_)
        simpa using hx.2
      · have hpre : (fun x : Euclid P => ‖x‖) ⁻¹' Ioc a b = closedBall 0 b \ closedBall 0 a := by
          ext x
          simp [and_comm]
        rw [Measure.map_apply continuous_norm.measurable measurableSet_Ioc, Measure.smul_apply,
          smul_eq_mul, hνIoc a b hab, hpre,
          measure_sdiff (closedBall_subset_closedBall hab.le)
            measurableSet_closedBall.nullMeasurableSet (hball_fin a),
          hcdf b, hcdf a, ENNReal.mul_sub (fun _ _ => hc)]
    -- Steps 3–6 at the radius `r`: `∫ max(r² − ‖x‖², 0) (‖x‖² − ‖pₓ x‖²) dμ = 0`.
    have key : ∀ r : ℝ, 0 < r → ∀ᵐ x ∂R.measure, max (r ^ 2 - ‖x‖ ^ 2) 0 *
        (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) = 0 := by
      intro r hr
      -- The profile `g(s) = max(r² − s, 0) ≥ 0` and its primitive `η(s) = ∫ₛ^{r²} g`, `η' = −g`.
      obtain ⟨η, hη_deriv, hη_zero⟩ : ∃ η : ℝ → ℝ,
          (∀ s, HasDerivAt η (-max (r ^ 2 - s) 0) s) ∧ ∀ s, r ^ 2 ≤ s → η s = 0 := by
        have hgc : Continuous fun u : ℝ => max (r ^ 2 - u) 0 := by fun_prop
        refine ⟨fun s => ∫ u in s..r ^ 2, max (r ^ 2 - u) 0, fun s => ?_, fun s hs => ?_⟩
        · exact intervalIntegral.integral_hasDerivAt_left (hgc.intervalIntegrable _ _)
            (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
        · show ∫ u in s..r ^ 2, max (r ^ 2 - u) 0 = 0
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
          · simp
          · rw [uIcc_of_ge hs] at hu
            exact max_eq_right (by linarith [hu.1])
      have hηc : Continuous η := continuous_iff_continuousAt.2 fun s => (hη_deriv s).continuousAt
      have hη_C1 : ContDiff ℝ 1 η := by
        have hderiv : deriv η = fun s => -max (r ^ 2 - s) 0 :=
          funext fun s => (hη_deriv s).deriv
        exact contDiff_one_iff_deriv.2
          ⟨fun s => (hη_deriv s).differentiableAt, by rw [hderiv]; fun_prop⟩
      -- Functions vanishing off `B̄_r(0)` have compact support.
      have hcs : ∀ f : Euclid P → ℝ, (∀ x : Euclid P, r < ‖x‖ → f x = 0) →
          HasCompactSupport f := by
        intro f hf
        refine (isCompact_closedBall (0 : Euclid P) r).of_isClosed_subset (isClosed_tsupport _) ?_
        refine closure_minimal (fun x hx => ?_) isClosed_closedBall
        by_contra hxr
        exact hx (hf x (by simpa using hxr))
      have hη_out : ∀ x : Euclid P, r < ‖x‖ →
          η (‖x‖ ^ 2) = 0 ∧ max (r ^ 2 - ‖x‖ ^ 2) 0 = 0 :=
        fun x hx => ⟨hη_zero _ (by nlinarith [norm_nonneg x]),
          max_eq_right (by nlinarith [norm_nonneg x])⟩
      -- The radial test field `X(x) = η(‖x‖²) x` (`C¹`, supported in `B̄_r(0)`).
      have hX_C1 : ContDiff ℝ 1 (fun x : Euclid P => η (‖x‖ ^ 2) • x) :=
        (hη_C1.comp (contDiff_norm_sq ℝ)).smul contDiff_id
      have hX_cs : HasCompactSupport (fun x : Euclid P => η (‖x‖ ^ 2) • x) := by
        refine (isCompact_closedBall (0 : Euclid P) r).of_isClosed_subset (isClosed_tsupport _) ?_
        refine closure_minimal (fun x hx => ?_) isClosed_closedBall
        by_contra hxr
        exact hx (by simp [(hη_out x (by simpa using hxr)).1])
      have hX_fderiv : ∀ x : Euclid P, HasFDerivAt (fun x : Euclid P => η (‖x‖ ^ 2) • x)
          (η (‖x‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) • (innerSL ℝ x).smulRight x) x := by
        intro x
        have hsq := (hasFDerivAt_id x).norm_sq
        have hηComp := (hη_deriv (‖x‖ ^ 2)).comp_hasFDerivAt x hsq
        refine (hηComp.smul (hasFDerivAt_id x)).congr_fderiv
          (ContinuousLinearMap.ext fun w => ?_)
        simp [mul_smul]
        module
      -- Simon 4.3.2: `div_M X = n η(‖x‖²) − 2 g(‖x‖²) ‖pₓ x‖²` wherever `dim Tₓ = n`.
      have hdiv : ∀ x : Euclid P,
          Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier x) = m + 1 →
          tangentialDivergence (m + 1) R.carrier (fun x : Euclid P => η (‖x‖ ^ 2) • x) x =
            ((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
              ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 := by
        intro x hx
        set T := approxTangentPlane (m + 1) R.carrier x
        rw [tangentialDivergence, (hX_fderiv x).fderiv, LinearMap.trace_comp_comm']
        have hcomp : ((η (‖x‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) • (innerSL ℝ x).smulRight x).toLinearMap ∘ₗ
              T.starProjection.toLinearMap) =
            η (‖x‖ ^ 2) • T.starProjection.toLinearMap +
              (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) •
                ((innerSL ℝ x).toLinearMap ∘ₗ T.starProjection.toLinearMap).smulRight x := by
          ext w
          simp
        have htr : LinearMap.trace ℝ (Euclid P) T.starProjection.toLinearMap =
            (m : ℝ) + 1 := by
          rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
            LinearMap.trace_comp_comm']
          have hid : T.orthogonalProjectionOnto.toLinearMap ∘ₗ T.subtypeL.toLinearMap =
              LinearMap.id := by
            ext y
            simp
          rw [hid, LinearMap.trace_id, hx]
          push_cast
          ring
        have hinner : inner ℝ x (T.starProjection x) = ‖T.starProjection x‖ ^ 2 := by
          rw [← T.inner_starProjection_left_eq_right x x]
          simpa using T.re_inner_starProjection_eq_normSq x
        rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htr]
        simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
          innerSL_apply_apply, smul_eq_mul, hinner]
        ring
      -- Steps 3–4: stationarity, rewritten as an integral against `μ`.
      have hstatX : ∫ x, tangentialDivergence (m + 1) R.carrier
          (fun x : Euclid P => η (‖x‖ ^ 2) • x) x ∂R.measure = 0 := by
        have hden : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
          funext x
          simp
        have hmeas : Measurable fun x => (R.mult x : NNReal) :=
          measurable_from_nat.comp R.measurable_mult
        rw [IMRep.measure, hden, integral_withDensity_eq_integral_smul hmeas,
          ← hstat _ hX_C1 hX_cs, IMRep.firstVariation]
        congr 1
      have hstat' : ∫ x, (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
          ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) ∂R.measure = 0 := by
        refine (integral_congr_ae ?_).trans hstatX
        filter_upwards [hrank] with x hx
        exact (hdiv x hx).symm
      -- Step 6: by Step 5 the same integral with `‖x‖²` in place of `‖pₓ x‖²` is
      -- `μ(B̄₁) ∫₀^r (d/dt)(n tⁿ η(t²)) dt = 0`.
      have hhom : ∫ x, (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2)
          ∂R.measure = 0 := by
        set G : ℝ → ℝ := fun t =>
          ((m : ℝ) + 1) * η (t ^ 2) + 2 * -max (r ^ 2 - t ^ 2) 0 * t ^ 2 with hG
        have hGc : Continuous G := by fun_prop
        change ∫ x, G ‖x‖ ∂R.measure = 0
        rw [← integral_map continuous_norm.aemeasurable hGc.aestronglyMeasurable, hmap,
          integral_smul_measure]
        suffices h : ∫ t, G t ∂ν = 0 by rw [h, smul_zero]
        have hd : (fun t : ℝ => ENNReal.ofReal (((m : ℝ) + 1) * t ^ m)) =
            fun t => ((Real.toNNReal (((m : ℝ) + 1) * t ^ m) : NNReal) : ℝ≥0∞) := rfl
        rw [hν, hd, integral_withDensity_eq_integral_smul (by fun_prop)]
        have hF : ∀ t, HasDerivAt (fun t : ℝ => ((m : ℝ) + 1) * (t ^ (m + 1) * η (t ^ 2)))
            (((m : ℝ) + 1) * t ^ m * G t) t := by
          intro t
          have h3 := ((hasDerivAt_pow (m + 1) t).mul
            ((hη_deriv (t ^ 2)).comp t (hasDerivAt_pow 2 t))).const_mul ((m : ℝ) + 1)
          refine h3.congr_deriv ?_
          simp only [hG, Function.comp_apply]
          push_cast
          ring
        rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Ioc_subset_Ioi_self : Ioc (0 : ℝ) r ⊆ Ioi 0) fun t ht => ?_]
        · rw [setIntegral_congr_fun measurableSet_Ioc
            (g := fun t => ((m : ℝ) + 1) * t ^ m * G t) fun t ht => ?_,
            ← intervalIntegral.integral_of_le hr.le,
            intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
              ((by fun_prop : Continuous fun t : ℝ =>
                ((m : ℝ) + 1) * t ^ m * G t).intervalIntegrable _ _)]
          · simp [hη_zero (r ^ 2) le_rfl]
          · simp only [NNReal.smul_def, smul_eq_mul]
            rw [Real.coe_toNNReal _ (mul_nonneg (by positivity) (pow_nonneg ht.1.le m))]
        · have hrt : r < t := by
            simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht
            exact ht.2 ht.1
          have hG0 : G t = 0 := by
            simp only [hG, hη_zero (t ^ 2) (by nlinarith),
              max_eq_right (by nlinarith : r ^ 2 - t ^ 2 ≤ 0)]
            ring
          simp [hG0]
      -- Subtracting, `∫ g(‖x‖²) (‖x‖² − ‖pₓ x‖²) dμ = 0` with a nonnegative integrand.
      have hpx_meas : AEMeasurable
          (fun x => ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) R.measure :=
        ((ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
          (hproj.prodMk aemeasurable_id)).norm).pow_const 2
      have hint1 : Integrable (fun x : Euclid P => ((m : ℝ) + 1) * η (‖x‖ ^ 2) +
          2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2) R.measure := by
        refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx => ?_)
        simp [(hη_out x hx).1, (hη_out x hx).2]
      have hint2 : Integrable (fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2))
          R.measure := by
        refine Integrable.mono' (g := fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2)
          ?_ ?_ (ae_of_all _ fun x => ?_)
        · refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx => ?_)
          simp [(hη_out x hx).2]
        · exact (by fun_prop : Continuous fun x : Euclid P =>
            max (r ^ 2 - ‖x‖ ^ 2) 0).aestronglyMeasurable.mul
              ((by fun_prop : Continuous fun x : Euclid P => ‖x‖ ^ 2).aestronglyMeasurable.sub
                hpx_meas.aestronglyMeasurable)
        · have h2 : ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ x) 2
          have h3 : 0 ≤ ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 := by
            positivity
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sub_nonneg.2 h2))]
          exact mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      have hsplit : (fun x : Euclid P => ((m : ℝ) + 1) * η (‖x‖ ^ 2) +
          2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
            ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) =
          fun x => (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2) +
            2 * (max (r ^ 2 - ‖x‖ ^ 2) 0 *
              (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2)) := by
        funext x
        ring
      rw [hsplit, integral_add hint1 (hint2.const_mul 2), hhom, zero_add, integral_const_mul]
        at hstat'
      have h0 : ∫ x, max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2)
            ∂R.measure = 0 := by
        linarith
      have hnn : 0 ≤ᵐ[R.measure] fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) :=
        ae_of_all _ fun x => mul_nonneg (le_max_right _ _) (sub_nonneg.2
          (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ x) 2))
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint2).1 h0] with x hx
      exact hx
    -- Step 7: exhaust `ℝᴾ` by the balls `B_{k+1}(0)`; then `‖x − pₓ x‖² = ‖x‖² − ‖pₓ x‖² = 0`.
    have hall : ∀ᵐ x ∂R.measure, ∀ k : ℕ, max (((k : ℝ) + 1) ^ 2 - ‖x‖ ^ 2) 0 *
        (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) = 0 :=
      ae_all_iff.2 fun k => key _ (by positivity)
    filter_upwards [hall] with x hx
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    have hpos : 0 < max (((k : ℝ) + 1) ^ 2 - ‖x‖ ^ 2) 0 :=
      lt_max_of_lt_left (by nlinarith [norm_nonneg x])
    have hq := (mul_eq_zero.1 (hx k)).resolve_left hpos.ne'
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x
      (approxTangentPlane (m + 1) R.carrier x)
    rw [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply] at hpy
    have h0 : ‖x - (approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 = 0 := by
      linarith
    exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
