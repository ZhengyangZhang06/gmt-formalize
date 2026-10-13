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

/-- **Orthogonal frame adapted to an `n`-plane** (Step 0 of the graph first-variation estimate in
the tilt-excess step of Allard's theorem, used for Simon 7.4.3).  Let `T ⊆ ℝⁿ⁺ᵏ` have dimension
`n`, let `ι : ℝⁿ → ℝⁿ⁺ᵏ`, `ι' : ℝᵏ → ℝⁿ⁺ᵏ` be linear isometries with orthogonal ranges and
`ι(ℝⁿ) ⊆ T`, and let `P : ℝⁿ⁺ᵏ → ℝⁿ` satisfy `P ∘ ι = id` and `P ∘ ι' = 0`.  Then `range ι = T`
(both have dimension `n`), so `ι'w ∈ Tᗮ`, and `range ι' = Tᗮ` (both have dimension `k`).  Every
`y` splits as `y = p_T y + (y − p_T y) = ιu + ι'w` with `Py = u`.  This gives `⟪ιu', y⟫ = ⟪u', Py⟫`,
`p_T y = ι(Py)`, Pythagoras `|y|² = |Py|² + |y − p_T y|²`, and `|Py| ≤ |y|`. -/
theorem Submission.dorag_tes_gv_adapted_frame : ∀ (n k : ℕ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y)) ∧ (∀ y, T.starProjection y = ι (P y)) ∧ (∀ w, ι' w ∈ Tᗮ) ∧ (∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2) ∧ (∀ y, ‖P y‖ ≤ ‖y‖) := by
  intro n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `range ι ⊆ T`, and both have dimension `n`, so `range ι = T`
  have hrange : LinearMap.range ι.toLinearMap = T := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact hιT v
    · rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin, hT]
  -- (c): `ι'w` is orthogonal to every `ιv`, hence to `T`
  have hι'T : ∀ w, ι' w ∈ Tᗮ := by
    intro w
    rw [← hrange, Submodule.mem_orthogonal]
    rintro _ ⟨v, rfl⟩
    exact hιι' v w
  -- `range ι' ⊆ Tᗮ`, and both have dimension `(n + k) − n = k`, so `range ι' = Tᗮ`
  have hrange' : LinearMap.range ι'.toLinearMap = Tᗮ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨w, rfl⟩
      exact hι'T w
    · have h := Submodule.finrank_add_finrank_orthogonal T
      rw [finrank_euclideanSpace_fin, hT] at h
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
      omega
  -- `y = p_T y + (y − p_T y) = ιu + ι'w`
  have hdecomp : ∀ y, ∃ u w, y = ι u + ι' w := by
    intro y
    obtain ⟨u, hu⟩ : T.starProjection y ∈ LinearMap.range ι.toLinearMap :=
      hrange ▸ T.starProjection_apply_mem y
    obtain ⟨w, hw⟩ : y - T.starProjection y ∈ LinearMap.range ι'.toLinearMap :=
      hrange' ▸ T.sub_starProjection_mem_orthogonal y
    rw [LinearIsometry.coe_toLinearMap] at hu hw
    exact ⟨u, w, by rw [hu, hw, add_sub_cancel]⟩
  -- `P(ιu + ι'w) = u`
  have hP : ∀ u w, P (ι u + ι' w) = u := fun u w => by rw [map_add, hPι, hPι', add_zero]
  -- (a): `⟪ιu, ιu₀ + ι'w⟫ = ⟪u, u₀⟫ = ⟪u, P(ιu₀ + ι'w)⟫`
  have hadj : ∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y) := by
    intro u y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, inner_add_right, hιι', add_zero, LinearIsometry.inner_map_map]
  -- (b): `p_T(ιu₀ + ι'w) = ιu₀ + 0 = ι(P(ιu₀ + ι'w))`
  have hpT : ∀ y, T.starProjection y = ι (P y) := by
    intro y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, map_add, Submodule.starProjection_eq_self_iff.mpr (hιT u₀),
      (T.starProjection_apply_eq_zero_iff).mpr (hι'T w), add_zero]
  -- (d): Pythagoras for `y = p_T y + (y − p_T y)`, with `|p_T y| = |ι(Py)| = |Py|`
  have hpyth : ∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2 := by
    intro y
    have h0 : inner ℝ (T.starProjection y) (y - T.starProjection y) = 0 := by
      rw [real_inner_comm]
      exact T.starProjection_inner_eq_zero y _ (T.starProjection_apply_mem y)
    have h1 : ‖T.starProjection y‖ = ‖P y‖ := by rw [hpT, LinearIsometry.norm_map]
    have h2 := norm_add_sq_real (T.starProjection y) (y - T.starProjection y)
    rw [add_sub_cancel, h0, h1] at h2
    linarith
  -- (e): `|Py|² ≤ |y|²` by (d)
  have hPle : ∀ y, ‖P y‖ ≤ ‖y‖ := by
    intro y
    have h : ‖P y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hpyth y]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  exact ⟨hadj, hpT, hι'T, hpyth, hPle⟩

/-- **Graph-plane estimates at one point** (Simon Ch. 5, proof of 4.5, (7), (9), (10),
`chapter-05.txt` lines 833–872).  `Q = {ιw + ι'(Lw)}` is the graph plane of `L`, `‖L‖ ≤ 1`, over
`T = ι(ℝⁿ)`, and (Q1), (Q2) are the tilt bounds `|⟨p_Q a, b⟩ − ⟨a, b⟩| ≤ t|a||b|` on `T` and
`|p_Q e|² ≤ t|e|²` on `Tᗮ`.  Let `α` be the Riesz vector of `λ = proj_j ∘ L`.  Every
`q = ιw + ι'(Lw) ∈ Q` has `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩`, so `p_Q(ι'ε_j) = p_Q(ια)` ((7)).  Hence
`⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t`, and (Q1) with `a = b = ια` gives
`‖λ‖² = |ια|² ≤ t + t|ια|² ≤ 2t`.  For `m` with Riesz vector `β`, `⟨ιβ, y⟩ = ⟨β, Py⟩`
(`dorag_tes_gv_adapted_frame`) gives `m(P p_Q(ι'ε_j)) = ⟨p_Q(ια), ιβ⟩`, Parseval gives
`Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`, and (Q1) bounds the difference by `t‖λ‖‖m‖ ≤ t‖m‖`. -/
theorem Submission.dorag_tes_gv_graph_plane_pointwise : ∀ (n k : ℕ) (T Q : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (L : Euclid n →L[ℝ] Euclid k) (j : Fin k) (t : ℝ), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → Q = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ L.toLinearMap) → ‖L‖ ≤ 1 → 0 ≤ t → (∀ a b : Euclid (n + k), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ t * ‖a‖ * ‖b‖) → (∀ e : Euclid (n + k), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ t * ‖e‖ ^ 2) → ‖(EuclideanSpace.proj j).comp L‖ ^ 2 ≤ 2 * t ∧ ∀ m : Euclid n →L[ℝ] ℝ, |m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) - ∑ i : Fin n, ((EuclideanSpace.proj j).comp L) (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤ t * ‖m‖ := by
  intro n k T Q ι ι' P L j t hT hιι' hιT hPι hPι' hQ hL ht hQ1 hQ2
  obtain ⟨hadj, -, hι'T, -, -⟩ :=
    Submission.dorag_tes_gv_adapted_frame n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `λ = proj_j ∘ L` has `|λw| = |(Lw)_j| ≤ |Lw| ≤ |w|`, so `‖λ‖ ≤ 1`
  have hlamj : ∀ w, (EuclideanSpace.proj j).comp L w = L w j := fun w => rfl
  have hlam1 : ‖(EuclideanSpace.proj j).comp L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    calc ‖(EuclideanSpace.proj j).comp L w‖ = ‖L w j‖ := by rw [hlamj]
      _ ≤ ‖L w‖ := PiLp.norm_apply_le (L w) j
      _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg w)
  generalize (EuclideanSpace.proj j).comp L = lam at hlam1 hlamj ⊢
  -- Riesz vectors: `⟨γ, w⟩ = μ w` and `|ιγ| = ‖μ‖`
  have riesz : ∀ μ : Euclid n →L[ℝ] ℝ,
      ∃ γ : Euclid n, (∀ w, inner ℝ γ w = μ w) ∧ ‖ι γ‖ = ‖μ‖ := fun μ =>
    ⟨(InnerProductSpace.toDual ℝ (Euclid n)).symm μ, fun _ => InnerProductSpace.toDual_symm_apply,
      by rw [ι.norm_map, LinearIsometryEquiv.norm_map]⟩
  obtain ⟨α, hα, ha⟩ := riesz lam
  -- (7): `ι'ε_j − ια ⊥ Q`, since `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩` for `q = ιw + ι'(Lw)`
  have hgraph : Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))) =
      Q.starProjection (ι α) := by
    have hperp : ι' (EuclideanSpace.single j (1 : ℝ)) - ι α ∈ Qᗮ := by
      rw [Submodule.mem_orthogonal]
      intro q hq
      rw [hQ] at hq
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hq
      have h1 : inner ℝ (ι w) (ι' (EuclideanSpace.single j (1 : ℝ))) = 0 := hιι' _ _
      have h2 : inner ℝ (ι' (L w)) (ι' (EuclideanSpace.single j (1 : ℝ))) = lam w := by
        rw [LinearIsometry.inner_map_map, EuclideanSpace.inner_single_right, hlamj]
        simp
      have h3 : inner ℝ (ι w) (ι α) = lam w := by
        rw [LinearIsometry.inner_map_map, real_inner_comm, hα]
      have h4 : inner ℝ (ι' (L w)) (ι α) = 0 := by
        rw [real_inner_comm]
        exact hιι' _ _
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toLinearMap, ContinuousLinearMap.coe_coe]
      rw [inner_sub_right, inner_add_left, inner_add_left, h1, h2, h3, h4]
      ring
    have h0 := (Submodule.starProjection_apply_eq_zero_iff (K := Q)).2 hperp
    rwa [map_sub, sub_eq_zero] at h0
  -- (9): `⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t` by (Q2)
  have hpa : inner ℝ (Q.starProjection (ι α)) (ι α) = ‖Q.starProjection (ι α)‖ ^ 2 := by
    have h := Submodule.starProjection_inner_eq_zero (K := Q) (ι α) _
      (Q.starProjection_apply_mem (ι α))
    rw [inner_sub_left, sub_eq_zero] at h
    rw [real_inner_comm, h, real_inner_self_eq_norm_sq]
  have hpa_le : ‖Q.starProjection (ι α)‖ ^ 2 ≤ t := by
    have h := hQ2 _ (hι'T (EuclideanSpace.single j (1 : ℝ)))
    have he : ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
    rwa [he, one_pow, mul_one, hgraph] at h
  refine ⟨?_, fun m => ?_⟩
  · -- (Q1) with `a = b = ια`: `|ια|² ≤ |p_Q(ια)|² + t|ια|² ≤ t + t`
    have h := hQ1 (ι α) (ι α) (hιT α) (hιT α)
    rw [hpa, real_inner_self_eq_norm_sq, ha] at h
    have hsq : ‖lam‖ * ‖lam‖ ≤ 1 := by nlinarith [norm_nonneg lam]
    nlinarith [(abs_le.1 h).1, mul_le_mul_of_nonneg_left hsq ht]
  · -- (10): with `β` the Riesz vector of `m`, `m(P y) = ⟨β, P y⟩ = ⟨ιβ, y⟩`
    obtain ⟨β, hβ, hb⟩ := riesz m
    have hmP : m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) =
        inner ℝ (Q.starProjection (ι α)) (ι β) := by
      rw [← hβ, ← hadj, hgraph, real_inner_comm]
    -- Parseval in the basis `(eᵢ)`: `Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`
    have hsum : ∑ i : Fin n, lam (EuclideanSpace.single i (1 : ℝ)) *
        m (EuclideanSpace.single i (1 : ℝ)) = inner ℝ (ι α) (ι β) := by
      rw [LinearIsometry.inner_map_map,
        ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner α β]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, hα, real_inner_comm, hβ]
    rw [hmP, hsum]
    calc |inner ℝ (Q.starProjection (ι α)) (ι β) - inner ℝ (ι α) (ι β)|
        ≤ t * ‖ι α‖ * ‖ι β‖ := hQ1 _ _ (hιT α) (hιT β)
      _ = t * ‖lam‖ * ‖m‖ := by rw [ha, hb]
      _ ≤ t * 1 * ‖m‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam1 ht) (norm_nonneg m)
      _ = t * ‖m‖ := by rw [mul_one]
/-- First variation of a vertical field (Simon Ch. 4, 2.2–2.3): for differentiable `ζ` and a
fixed `e`, `D(ζe)(x) = Dζ(x)(·) e`, so `p_x ∘ D(ζe)(x)` is the rank-one map `y ↦ Dζ(x)(y) p_x e`
and `div_M(ζe)(x) = Dζ(x)(p_x e)`.  As `μ_V = (Hⁿ⌞M).withDensity θ` with `θ` measurable and
finite, `δV(ζe) = ∫_M θ Dζ(x)(p_x e) dHⁿ = ∫ Dζ(x)(p_x e) dμ_V`, with no integrability needed. -/
theorem Submission.dorag_tes_gv_vertical_field_first_variation : ∀ (m n : ℕ) (U : Set (Euclid m)) (R : IMRep U n) (ζ : Euclid m → ℝ) (e : Euclid m), Differentiable ℝ ζ → R.firstVariation (fun x => ζ x • e) = ∫ x, fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure := by
  intro m n U R ζ e hζ
  -- `div_M(ζe)(x) = trace(p_x ∘ Dζ(x).smulRight e) = trace(Dζ(x).smulRight (p_x e)) = Dζ(x)(p_x e)`
  have hdiv : ∀ x, tangentialDivergence n R.carrier (fun x => ζ x • e) x =
      fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) := by
    intro x
    unfold tangentialDivergence
    rw [fderiv_smul_const (hζ x) e]
    have hrank : (approxTangentPlane n R.carrier x).starProjection.toLinearMap ∘ₗ
        ((fderiv ℝ ζ x).smulRight e).toLinearMap =
        (fderiv ℝ ζ x).toLinearMap.smulRight
          ((approxTangentPlane n R.carrier x).starProjection e) := by
      ext y
      simp [map_smul]
    rw [hrank, LinearMap.trace_smulRight]
    rfl
  -- `μ_V = (Hⁿ⌞M).withDensity θ`, `θ` measurable and finite: `∫ g dμ_V = ∫_M θ g dHⁿ` for all `g`
  unfold IMRep.firstVariation IMRep.measure
  have hmeas : Measurable fun x => ((R.mult x : ℕ) : ℝ≥0∞) :=
    measurable_from_nat.comp R.measurable_mult
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun x => by simp)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hdiv x, ENNReal.toReal_natCast, smul_eq_mul]
/-- **Cutoff extension along a projection** (Steps 3.1–3.3 of the graph first-variation estimate):
if `n ≥ 1`, `ζ ∈ C¹(ℝⁿ)` has `tsupport ζ ⊆ B̆_{r/2}(0)` and `‖Dζ‖ ≤ G`, then
`ψ = (ζ ∘ φ) h₀`, `φ(x) = P(x − ξ)`, with `h₀` the `ContDiffBump` at `ξ` of radii `7r/8 < r`, is
`C¹` with compact support in `B_r(ξ)` and `|ψ| ≤ Gr/2` (`ζ` is `G`-Lipschitz and vanishes on the
sphere `|v| = r/2`).  If `|x − ξ|² ≤ |φ(x)|² + r²/16`, then `Dψ(x) = Dζ(φ(x)) ∘ P`: for
`|φ(x)| < r/2` we get `|x − ξ| < 7r/8`, so `h₀ = 1` near `x`; for `|φ(x)| ≥ r/2` both sides
vanish, `φ(x)` lying outside `tsupport ζ`. -/
theorem Submission.dorag_tes_gv_cutoff_extension : ∀ (n m : ℕ), 0 < n → ∀ (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ), 0 < r → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ∃ ψ : Euclid m → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ closedBall ξ r ∧ (∀ x, |ψ x| ≤ G * (r / 2)) ∧ ∀ x, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 → fderiv ℝ ψ x = (fderiv ℝ ζ (P (x - ξ))).comp P := by
  intro n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hζdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- `ζ` is `G`-Lipschitz and vanishes outside `B̆_{r/2}(0)`
  have hζlip : ∀ v w, |ζ v - ζ w| ≤ G * ‖v - w‖ := by
    intro v w
    simpa [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hζdiff x) (fun x _ => hζG x) (mem_univ w) (mem_univ v)
  have hζs' : ∀ v, r / 2 ≤ ‖v‖ → v ∉ tsupport ζ := by
    intro v hv h
    have := hζs h
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- `|ζ v| ≤ G r/2`: compare `v` with `w = v + (r/2 − |v|) u` on the sphere `|w| = r/2`
  have hζsup : ∀ v, |ζ v| ≤ G * (r / 2) := by
    intro v
    by_cases hv : r / 2 ≤ ‖v‖
    · rw [image_eq_zero_of_notMem_tsupport (hζs' v hv), abs_zero]
      positivity
    · replace hv := not_le.mp hv
      obtain ⟨u, hu1, hu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ ‖v + (r / 2 - ‖v‖) • u‖ = r / 2 := by
        by_cases hv0 : v = 0
        · refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by simp, ?_⟩
          subst hv0
          simp [norm_smul, abs_of_pos hr]
        · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne'], ?_⟩
          have : v + (r / 2 - ‖v‖) • (‖v‖⁻¹ • v) = ((r / 2) / ‖v‖) • v := by
            rw [smul_smul, ← one_smul ℝ v, smul_smul, ← add_smul, one_smul]
            congr 1
            field_simp
            ring
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
            div_mul_cancel₀ _ hvpos.ne']
      have hw : ζ (v + (r / 2 - ‖v‖) • u) = 0 := image_eq_zero_of_notMem_tsupport (hζs' _ hu.ge)
      calc |ζ v| = |ζ v - ζ (v + (r / 2 - ‖v‖) • u)| := by rw [hw, sub_zero]
        _ ≤ G * ‖v - (v + (r / 2 - ‖v‖) • u)‖ := hζlip _ _
        _ = G * (r / 2 - ‖v‖) := by
            rw [sub_add_cancel_left, norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs,
              abs_of_pos (by linarith)]
        _ ≤ G * (r / 2) := by gcongr; linarith [norm_nonneg v]
  -- `ψ = (ζ ∘ φ) h₀`, `φ(y) = P(y − ξ)`
  let h0 : ContDiffBump ξ := ⟨7 * r / 8, r, by positivity, by linarith⟩
  have hφd : ∀ x, HasFDerivAt (fun y : Euclid m => P (y - ξ)) P x := by
    intro x
    have h := P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const ξ)
    rwa [ContinuousLinearMap.comp_id] at h
  have hφc : Continuous (fun y : Euclid m => P (y - ξ)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  refine ⟨fun x => ζ (P (x - ξ)) * h0 x, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hζ.comp (P.contDiff.comp (contDiff_id.sub contDiff_const))).mul h0.contDiff
  · exact HasCompactSupport.mul_left (f := fun x => ζ (P (x - ξ))) h0.hasCompactSupport
  · exact tsupport_mul_subset_right.trans h0.tsupport_eq.subset
  · intro x
    rw [abs_mul, abs_of_nonneg h0.nonneg]
    calc |ζ (P (x - ξ))| * h0 x ≤ G * (r / 2) * 1 :=
          mul_le_mul (hζsup _) h0.le_one h0.nonneg (by positivity)
      _ = G * (r / 2) := mul_one _
  · intro x hx
    by_cases hφ : ‖P (x - ξ)‖ < r / 2
    · -- `|x − ξ|² < r²/4 + r²/16 < (7r/8)²`, so `h₀ = 1` near `x` and the chain rule applies
      have hx' : ‖x - ξ‖ < 7 * r / 8 := by
        have h1 : ‖x - ξ‖ ^ 2 < (7 * r / 8) ^ 2 := by nlinarith [norm_nonneg (P (x - ξ))]
        nlinarith [norm_nonneg (x - ξ)]
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun y => ζ (P (y - ξ)) := by
        filter_upwards [h0.eventuallyEq_one_of_mem_ball (show x ∈ ball ξ (7 * r / 8) by
          rwa [mem_ball, dist_eq_norm])] with y hy
        rw [hy, Pi.one_apply, mul_one]
      rw [hev.fderiv_eq]
      exact ((hζdiff _).hasFDerivAt.comp x (hφd x)).fderiv
    · -- `φ = P(· − ξ)` maps a neighbourhood of `x` outside `tsupport ζ`: both sides vanish
      have hns := hζs' _ (not_lt.mp hφ)
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [((isClosed_tsupport ζ).isOpen_compl.preimage hφc).mem_nhds hns] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      rw [hev.fderiv_eq, fderiv_of_notMem_tsupport ℝ hns]
      simp

/-- **First-variation bound for vertical cutoff fields** (Simon Ch. 5, proof of 4.5: the
first-variation identity (6) tested with the vertical field `X = ζ̃ e`).  Let `R` satisfy
`δV(X) = −∫ X · H dμ` for `X ∈ C¹_c` with `spt X ⊆ W ⊆ U`, where `|H| ≤ κ`, `μ = μ_V`, and
`x ↦ p_{TₓM}` is `μ`-measurable.  Let `B_r(ξ) ⊆ W`, `|Py| ≤ |y|`, and
`|x − ξ|² ≤ |P(x − ξ)|² + r²/16` on `spt μ ∩ B_r(ξ)`.  If `ζ ∈ C¹_c(ℝⁿ)`,
`spt ζ ⊆ B̆ⁿ_{r/2}(0)`, `‖Dζ‖ ≤ G` and `|e| ≤ 1`, then `u(x) = Dζ(P(x − ξ))(P(p_{TₓM} e))` is
`μ`-integrable on `B_r(ξ)` and `|∫_{B_r(ξ)} u dμ| ≤ G (κr/2) μ(B_r(ξ))`.
Proof: extend `ζ` to the cutoff `ψ` of `dorag_tes_gv_cutoff_extension`, test with `X = ψ e`,
compute `δV(X) = ∫ Dψ(p_{TₓM} e) dμ` by `dorag_tes_gv_vertical_field_first_variation`, localize
to `B_r(ξ)` (where `Dψ = Dζ(P(· − ξ)) ∘ P` on the conull set `spt μ`), and bound
`|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`. -/
theorem Submission.dorag_tes_gv_vertical_variation_bound : ∀ (n m : ℕ), 0 < n → ∀ (U W : Set (Euclid m)) (R : IMRep U n) (H : Euclid m → Euclid m) (κ : ℝ) (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ) (e : Euclid m), W ⊆ U → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid m → Euclid m, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → (∀ y, ‖P y‖ ≤ ‖y‖) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ‖e‖ ≤ 1 → IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure ∧ ENNReal.ofReal |∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure| ≤ ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
  intro n m hn U W R H κ ξ r P ζ G e hWU hHκ hFV hp hr hBW hPle hspt hζ hζc hζs hζG he
  -- Step 1: `G, κ ≥ 0`.
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `μ(B_r(ξ)) < ∞`, since `B_r(ξ)` is a compact subset of `U`.
  have hfin : R.measure (closedBall ξ r) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall ξ r) (hBW.trans hWU)
  -- Step 3: the cutoff `ψ` extending `ζ ∘ P(· − ξ)`.
  obtain ⟨ψ, hψ, hψc, hψs, hψb, hψd⟩ :=
    Submission.dorag_tes_gv_cutoff_extension n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hψ0 : ∀ x, x ∉ closedBall ξ r → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hψs h)
  -- Step 4: `X = ψ e` is an admissible test field.
  have hX : ContDiff ℝ 1 (fun x => ψ x • e) := hψ.smul contDiff_const
  have hXc : HasCompactSupport (fun x => ψ x • e) := hψc.smul_right
  have hXs : tsupport (fun x => ψ x • e) ⊆ W :=
    (tsupport_smul_subset_left _ _).trans (hψs.trans hBW)
  have hfv : R.firstVariation (fun x => ψ x • e) =
      -∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure := hFV _ hX hXc hXs
  -- Step 5: `δV(ψ e) = ∫ Dψ(x)(p_{TₓM} e) dμ`.
  rw [Submission.dorag_tes_gv_vertical_field_first_variation m n U R ψ e
    (hψ.differentiable one_ne_zero)] at hfv
  -- Step 6: localization to `B_r(ξ)`, where `Dψ = Dζ(P(· − ξ)) ∘ P` on `spt μ`.
  have hloc : ∫ x, fderiv ℝ ψ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure =
      ∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall ξ r)]
    · refine setIntegral_congr_ae measurableSet_closedBall ?_
      filter_upwards [Measure.support_mem_ae (μ := R.measure)] with x hxs hxB
      rw [hψd x (hspt x ⟨hxs, hxB⟩), ContinuousLinearMap.comp_apply]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hψs h)), zero_apply]
  -- Step 8: `|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`, hence the bound on `∫ ψ e · H dμ`.
  have hpt : ∀ x, ‖inner ℝ (ψ x • e) (H x)‖ ≤
      (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x := by
    intro x
    by_cases hx : x ∈ closedBall ξ r
    · rw [indicator_of_mem hx, real_inner_smul_left, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have heH : |inner ℝ e (H x)| ≤ κ :=
        calc |inner ℝ e (H x)| ≤ ‖e‖ * ‖H x‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * κ := mul_le_mul he (hHκ x) (norm_nonneg _) zero_le_one
          _ = κ := one_mul κ
      exact mul_le_mul (hψb x) heH (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem hx, hψ0 x hx, zero_smul, inner_zero_left, norm_zero]
  have hbd : |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure| ≤
      G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure‖
        ≤ ∫ x, (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x ∂R.measure :=
          norm_integral_le_of_norm_le
            ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin))
            (Eventually.of_forall hpt)
      _ = G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
  -- Step 10: `u` is a.e. strongly measurable and bounded by `G`, hence integrable on `B_r(ξ)`.
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) R.measure := by
    have hDζ : Continuous fun x : Euclid m => fderiv ℝ ζ (P (x - ξ)) :=
      (hζ.continuous_fderiv one_ne_zero).comp
        (P.continuous.comp (continuous_id.sub continuous_const))
    exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hDζ.aestronglyMeasurable.prodMk
        (P.continuous.comp_aestronglyMeasurable (hp.apply_continuousLinearMap e)))
  have hint : IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure := by
    refine Measure.integrableOn_of_bounded (M := G) hfin hmeas (Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))‖
        ≤ ‖fderiv ℝ ζ (P (x - ξ))‖ *
            ‖P ((approxTangentPlane n R.carrier x).starProjection e)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ G * 1 := mul_le_mul (hζG _)
          ((hPle _).trans ((Submodule.norm_starProjection_apply_le _ _).trans he))
          (norm_nonneg _) hG
      _ = G := mul_one G
  -- Steps 7 and 9: `∫_{B_r(ξ)} u dμ = −∫ ψ e · H dμ`, then pass to `ℝ≥0∞`.
  refine ⟨hint, ?_⟩
  rw [← hloc, hfv, abs_neg]
  calc ENNReal.ofReal |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure|
      ≤ ENNReal.ofReal (G * (κ * r / 2 * R.measure.real (closedBall ξ r))) :=
        ENNReal.ofReal_le_ofReal (hbd.trans_eq (by ring))
    _ = ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
        rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_mul (by positivity), ofReal_measureReal hfin]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
