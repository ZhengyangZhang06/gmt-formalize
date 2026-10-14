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

/-- **Simon Ch. 2, (4.18)–(4.20)** (tangential divergence in an orthonormal frame): if `τ₁, …, τₙ`
is an orthonormal basis of `Q`, then `trace(p_Q ∘ B) = Σₐ τₐ · Bτₐ`.  The orthogonality
characterization of the projection gives `p_Q z = Σₐ (τₐ · z) τₐ`, so `p_Q ∘ B` is the sum of the
rank-one maps `z ↦ (τₐ · Bz) τₐ`, and the trace of `z ↦ ℓ(z) v` is `ℓ(v)`. -/
theorem Submission.fvmb_trace_starProjection_comp_eq_sum_inner : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (τ : Fin n → Euclid P) (B : Euclid P →L[ℝ] Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ B.toLinearMap) = ∑ a, inner ℝ (τ a) (B (τ a)) := by
  intro P n Q τ B hτ hQ
  -- `p_Q z = Σₐ ⟪τₐ, z⟫ τₐ`: the right side lies in `Q` and `z` minus it is orthogonal to `Q`
  have hproj : ∀ z : Euclid P, Q.starProjection z = ∑ a, inner ℝ (τ a) z • τ a := by
    intro z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [← hQ]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · intro q hq
      rw [← hQ] at hq
      induction hq using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        rw [inner_sub_left, hτ.inner_left_fintype, real_inner_comm]
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  -- `p_Q ∘ B = Σₐ (z ↦ ⟪τₐ, Bz⟫ τₐ)`
  have hdecomp : Q.starProjection.toLinearMap ∘ₗ B.toLinearMap =
      ∑ a, ((innerₛₗ ℝ (τ a)) ∘ₗ B.toLinearMap).smulRight (τ a) := by
    ext z
    simp [hproj]
  -- `trace (z ↦ ℓ(z) v) = ℓ(v)` (`LinearMap.trace_smulRight`), summed over `a`
  rw [hdecomp, map_sum]
  simp
/-- **Angle-parametrized unit curve** (step 6 of the parent proof).  Differentiating
`⟨γ, γ⟩ = ‖γ‖² ≡ 1` gives `⟨γ, γ′⟩ = 0`.  With `A = ⟨γ, u⟩ > 0` and `B = ⟨γ, e⟩`, the quotient
and chain rules differentiate `arctan (B / A) ≡ α` to `(1 + (B / A)²)⁻¹ (B′ A − B A′) / A² = 1`,
i.e. `A B′ − B A′ = A² + B²`; the right side is positive, so `γ′ ≠ 0`. -/
theorem Submission.idtp_ccd_scsp_angle_curve : ∀ (P : ℕ) (u e : Euclid P) (s : ℝ) (γ : ℝ → Euclid P), ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → ∀ α ∈ Ioo (-s) s, inner ℝ (γ α) (deriv γ α) = 0 ∧ inner ℝ (γ α) u * inner ℝ (deriv γ α) e - inner ℝ (γ α) e * inner ℝ (deriv γ α) u = inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 ∧ deriv γ α ≠ 0 := by
  intro P u e s γ hγ hprop α hα
  -- `(-s, s)` is a neighbourhood of `α` on which `γ` is differentiable
  have hI : Ioo (-s) s ∈ 𝓝 α := Ioo_mem_nhds hα.1 hα.2
  have hd : HasDerivAt γ (deriv γ α) α :=
    ((hγ.differentiableOn one_ne_zero).differentiableAt hI).hasDerivAt
  -- orthogonality: `⟨γ, γ⟩ = ‖γ‖² ≡ 1` near `α`, so its derivative `2 ⟨γ, γ′⟩` vanishes
  have hn1 : (fun t => inner ℝ (γ t) (γ t)) =ᶠ[𝓝 α] fun _ => (1 : ℝ) := by
    filter_upwards [hI] with t ht
    rw [real_inner_self_eq_norm_sq, (hprop t ht).1, one_pow]
  have h0 := (hd.inner ℝ hd).unique ((hasDerivAt_const α (1 : ℝ)).congr_of_eventuallyEq hn1)
  rw [real_inner_comm (γ α) (deriv γ α)] at h0
  have horth : inner ℝ (γ α) (deriv γ α) = 0 := by linarith
  -- the angle: `A = ⟨γ, u⟩`, `B = ⟨γ, e⟩` and `arctan (B / A) ≡ id` near `α`
  have hA : 0 < inner ℝ (γ α) u := (hprop α hα).2.1
  have hAd : HasDerivAt (fun t => inner ℝ (γ t) u) (inner ℝ (deriv γ α) u) α := by
    simpa using hd.inner ℝ (hasDerivAt_const α u)
  have hBd : HasDerivAt (fun t => inner ℝ (γ t) e) (inner ℝ (deriv γ α) e) α := by
    simpa using hd.inner ℝ (hasDerivAt_const α e)
  have hid : (fun t => Real.arctan (((fun t => inner ℝ (γ t) e) / fun t => inner ℝ (γ t) u) t))
      =ᶠ[𝓝 α] fun t => t := by
    filter_upwards [hI] with t ht
    exact (hprop t ht).2.2
  have h1 := ((hBd.div hAd hA.ne').arctan).unique ((hasDerivAt_id' α).congr_of_eventuallyEq hid)
  simp only [Pi.div_apply] at h1
  -- clearing `(1 + (B / A)²) A² = A² + B² > 0` from `h1` gives the angle identity
  have hpos : 0 < inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 := by positivity
  have hkey : inner ℝ (γ α) u * inner ℝ (deriv γ α) e - inner ℝ (γ α) e * inner ℝ (deriv γ α) u =
      inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 := by
    field_simp at h1
    linarith
  -- non-degeneracy: `γ′ = 0` would make the left side `0`
  refine ⟨horth, hkey, fun h => ?_⟩
  rw [h, inner_zero_left, inner_zero_left, mul_zero, mul_zero, sub_zero] at hkey
  exact hpos.ne' hkey.symm
/-- **Area formula for an injective immersion, Gram form** (Simon Ch. 2, 3.1–3.5; step (1b)
of the chart divergence formula in the proof of Simon 7.5.2).  Let `G : ℝᵐ → ℝᴾ` be
differentiable with injective derivative at every point of the Borel set `F` and injective on `F`.
With `eᵢ` the standard basis of `ℝᵐ`, every `h : ℝᴾ → ℝ` has
`∫_{G(F)} h dHᵐ = ∫_F √det(⟨DG(v)eᵢ, DG(v)eⱼ⟩) h(G(v)) dv`.

Linear case (Simon 3.1): an injective linear `B` factors as `ι ∘ C` with `ι` an isometry of `ℝᵐ`
onto `range B`, so `Hᵐ(B S) = |det C| Lᵐ(S)`, and the Gram matrix of `B` is `CᵀC`.  The
approximation argument for 3.2: on countably many Borel pieces of `F`, `G` and (a.e.) `DG` are
`η`-close to an injective linear map, so the Lipschitz bound for `Hᵐ` puts `Hᵐ(G t)` and `∫_t J`
within a factor `(1 + 2η)^{2m}` of each other for Borel `t ⊆ F`.  Letting `η → 0` gives
`Hᵐ(G t) = ∫_t J`, and the integral identity follows as for
`integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem Submission.codim1_lur_cd_injective_area_formula_gram : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (F : Set (Euclid m)), MeasurableSet F → (∀ v ∈ F, DifferentiableAt ℝ G v) → (∀ v ∈ F, Function.Injective (fderiv ℝ G v)) → InjOn G F → ∀ h : Euclid P → ℝ, ∫ w in G '' F, h w ∂μHE[m] = ∫ v in F, Real.sqrt (Matrix.det (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G v (EuclideanSpace.single i 1)) (fderiv ℝ G v (EuclideanSpace.single j 1)))) * h (G v) := by
  intro P m G F hF hG hreg hinj h
  -- `Jf B = √det(⟨B eᵢ, B eⱼ⟩)`, the Gram Jacobian of a linear map `B : ℝᵐ → ℝᴾ`
  set Jf : (Euclid m →L[ℝ] Euclid P) → ℝ := fun B => Real.sqrt (Matrix.det (Matrix.of
    fun i j : Fin m => inner ℝ (B (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1))))
  -- (1) Linear area formula: `B = ι ∘ C` with `ι` an isometry onto `range B`, so
  -- `Hᵐ(B S) = Lᵐ(C S) = |det C| Lᵐ(S)`, and `⟨B eᵢ, B eⱼ⟩ = ⟨C eᵢ, C eⱼ⟩ = (CᵀC)ᵢⱼ`.
  have hlin : ∀ B : Euclid m →L[ℝ] Euclid P, Injective B → ∀ S : Set (Euclid m),
      μHE[m] (B '' S) = ENNReal.ofReal (Jf B) * volume S := by
    intro B hB S
    have hW : Module.finrank ℝ (LinearMap.range (B : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hB, finrank_euclideanSpace_fin]
    set b := (stdOrthonormalBasis ℝ (LinearMap.range (B : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hW)
    set C : Euclid m →ₗ[ℝ] Euclid m :=
      b.repr.toLinearMap ∘ₗ (B : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hBC : ∀ x, B x = (b.repr.symm (C x) : Euclid P) := fun x => by simp [C]
    have hι : Isometry fun y => (b.repr.symm y : Euclid P) :=
      isometry_subtype_coe.comp b.repr.symm.isometry
    have hgram : Jf B = |LinearMap.det C| := by
      set e := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      have hM : (Matrix.of fun i j : Fin m => inner ℝ (B (EuclideanSpace.single i 1))
          (B (EuclideanSpace.single j 1))) =
          (LinearMap.toMatrix e e C).transpose * LinearMap.toMatrix e e C := by
        ext i j
        rw [Matrix.of_apply, hBC, hBC, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map,
          Matrix.mul_apply]
        simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, e,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, PiLp.inner_apply,
          RCLike.inner_apply, conj_trivial]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      show Real.sqrt _ = _
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← sq,
        Real.sqrt_sq_eq_abs]
    rw [show B '' S = (fun y => (b.repr.symm y : Euclid P)) '' (C '' S) by
        rw [image_image]; exact image_congr fun x _ => hBC x,
      hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_image_linearMap, hgram]
  -- (2) Lipschitz comparison: if `‖f x - f y‖ ≤ K ‖g x - g y‖` on `S` and `g` is injective
  -- there, then `Hᵐ(f S) ≤ Kᵐ Hᵐ(g S)` (the Lipschitz bound for `f ∘ g⁻¹` on `g S`).
  have hcmp : ∀ (f g : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn g S →
      (∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ K * ‖g x - g y‖) →
      μHE[m] (f '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (g '' S) := by
    intro f g S K hg hfg
    have hθ : ∀ x ∈ S, f (invFunOn g S (g x)) = f x := fun x hx => by
      rw [hg.leftInvOn_invFunOn hx]
    have hlip : LipschitzOnWith K (f ∘ invFunOn g S) (g '' S) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [comp_apply, comp_apply, hθ x hx, hθ y hy, dist_eq_norm, dist_eq_norm]
      exact hfg x hx y hy
    have himg : f '' S = (f ∘ invFunOn g S) '' (g '' S) := by
      rw [image_image]; exact image_congr fun x hx => (hθ x hx).symm
    have key := hlip.hausdorffMeasure_image_le (d := (m : ℝ)) m.cast_nonneg
    rw [ENNReal.rpow_natCast] at key
    rw [himg, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
    exact mul_le_mul_right key _
  -- (3) Jacobian comparison for injective linear maps: (1) and (2) on the unit ball.
  have hjcmp : ∀ (B₁ B₂ : Euclid m →L[ℝ] Euclid P) (K : NNReal), Injective B₁ → Injective B₂ →
      (∀ z, ‖B₁ z‖ ≤ K * ‖B₂ z‖) →
      ENNReal.ofReal (Jf B₁) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf B₂) := by
    intro B₁ B₂ K h₁ h₂ hB
    have key := hcmp B₁ B₂ (ball 0 1) K h₂.injOn fun x _ y _ => by
      rw [← map_sub, ← map_sub]; exact hB _
    rw [hlin B₁ h₁, hlin B₂ h₂, ← mul_assoc] at key
    exact (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume 0 one_pos).ne'
      measure_ball_lt_top.ne).1 key
  -- (4) If `G` is `δ`-approximated by `A` on `S`, then `‖DG(v) - A‖ ≤ δ` at a.e. `v ∈ S`
  -- (at Lebesgue density points; the argument of `ApproximatesLinearOn.norm_fderiv_sub_le`).
  have hdcl : ∀ (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal) (S : Set (Euclid m)), S ⊆ F →
      MeasurableSet S → ApproximatesLinearOn G A S δ →
      ∀ᵐ v ∂(volume.restrict S), ‖fderiv ℝ G v - A‖ ≤ δ := by
    open scoped Pointwise in
    intro A δ S hSF hS hA
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid m)) S,
      ae_restrict_mem hS] with x hx xs
    refine ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(fderiv ℝ G x - A) z‖ ≤
        (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε)
          (𝓝[>] 0) (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ G x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (S ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume S x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0, ball x ρ ∩ S ⊆
        {y | ‖G y - G x - (fderiv ℝ G x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1
        ((hG x (hSF xs)).hasFDerivAt.hasFDerivWithinAt (s := S)).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ :=
      nhdsWithin_le_nhds
        (eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos))
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (S ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ G x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ G x - A) a‖ = ‖(fderiv ℝ G x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖G y - G x - A (y - x) - (G y - G x - (fderiv ℝ G x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖G y - G x - A (y - x)‖ + ‖G y - G x - (fderiv ℝ G x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hA _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ G x - A) z‖ = ‖(fderiv ℝ G x - A) a + (fderiv ℝ G x - A) (z - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(fderiv ℝ G x - A) a‖ + ‖(fderiv ℝ G x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (5) A lower bound `‖z‖ ≤ c(A) ‖A z‖` for injective `A`.
  have hmod : ∀ A : Euclid m →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ z, ‖z‖ ≤ c * ‖A z‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨c, cpos, hc⟩ := (A : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.2 hA)
      exact ⟨c, cpos, fun _ z => by simpa using hc.le_mul_dist z 0⟩
    · exact ⟨1, one_pos, fun h' => absurd h' hA⟩
  choose c cpos hc using hmod
  have hcont : ContinuousOn G F := fun v hv => (hG v hv).continuousAt.continuousWithinAt
  -- (6) For `0 < η ≤ 1/2` and `K = 1 + 2η`, partition a Borel `t ⊆ F` into pieces on which `G`
  -- and (a.e.) `DG` are `η`-close to an injective `A`; then (1)–(3) give two-sided bounds.
  have hpiece : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ t ⊆ F, MeasurableSet t →
      μHE[m] (G '' t) ≤ (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 *
        ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) ∧
      ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤
        (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 * μHE[m] (G '' t) := by
    intro η ηpos ηle t htF ht
    set K : NNReal := (1 + 2 * η).toNNReal
    have hKr : (K : ℝ) = 1 + 2 * η := Real.coe_toNNReal _ (by linarith)
    have hrel : ∀ u w : Euclid P, ‖u - w‖ ≤ η * ‖w‖ → ‖u‖ ≤ K * ‖w‖ ∧ ‖w‖ ≤ K * ‖u‖ := by
      intro u w huw
      have h1 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := norm_le_insert' u w
      have h2 : ‖w‖ ≤ ‖u‖ + ‖u - w‖ := by simpa [norm_sub_rev] using norm_le_insert' w u
      have h3 : (1 - η) * ‖w‖ ≤ ‖u‖ := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 + 2 * η)
      have h5 : 0 ≤ η * (1 - 2 * η) * ‖w‖ :=
        mul_nonneg (mul_nonneg ηpos.le (by linarith)) (norm_nonneg w)
      rw [hKr]
      constructor <;> nlinarith [norm_nonneg u, norm_nonneg w, mul_nonneg ηpos.le (norm_nonneg w)]
    rcases t.eq_empty_or_nonempty with rfl | tne
    · simp
    obtain ⟨T, A, Tdisj, Tmeas, tT, Tappr, TA⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G t (fderiv ℝ G)
        (fun v hv => (hG v (htF hv)).hasFDerivAt.hasFDerivWithinAt)
        (fun B => η.toNNReal / c B) (fun B => (div_pos (Real.toNNReal_pos.2 ηpos) (cpos B)).ne')
    have Ainj : ∀ n, Injective (A n) := fun n => by
      obtain ⟨y, yt, hy⟩ := TA tne n
      rw [hy]; exact hreg y (htF yt)
    have hpc : ∀ n, μHE[m] (G '' (t ∩ T n)) ≤ ((K : ℝ≥0∞) ^ m) ^ 2 *
          ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) ∧
        ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤
          ((K : ℝ≥0∞) ^ m) ^ 2 * μHE[m] (G '' (t ∩ T n)) := by
      intro n
      have hSF : t ∩ T n ⊆ F := inter_subset_left.trans htF
      have hS : MeasurableSet (t ∩ T n) := ht.inter (Tmeas n)
      have hcpos : (0 : ℝ) < c (A n) := cpos (A n)
      have hc0 : (c (A n) : ℝ) ≠ 0 := hcpos.ne'
      have happ : ∀ x ∈ t ∩ T n, ∀ y ∈ t ∩ T n,
          ‖(G x - G y) - (A n x - A n y)‖ ≤ η * ‖A n x - A n y‖ := by
        intro x hx y hy
        have h1 := Tappr n x hx y hy
        rw [NNReal.coe_div, Real.coe_toNNReal _ ηpos.le] at h1
        have h2 := hc (A n) (Ainj n) (x - y)
        rw [← map_sub]
        calc ‖G x - G y - A n (x - y)‖ ≤ η / c (A n) * ‖x - y‖ := h1
          _ ≤ η / c (A n) * (c (A n) * ‖A n (x - y)‖) := by gcongr
          _ = η * ‖A n (x - y)‖ := by field_simp
      have hder : ∀ᵐ v ∂(volume.restrict (t ∩ T n)), ∀ z,
          ‖fderiv ℝ G v z - A n z‖ ≤ η * ‖A n z‖ := by
        filter_upwards [hdcl (A n) _ (t ∩ T n) hSF hS (Tappr n)] with v hv z
        rw [NNReal.coe_div, Real.coe_toNNReal _ ηpos.le] at hv
        have h2 := hc (A n) (Ainj n) z
        calc ‖fderiv ℝ G v z - A n z‖ = ‖(fderiv ℝ G v - A n) z‖ := rfl
          _ ≤ ‖fderiv ℝ G v - A n‖ * ‖z‖ := (fderiv ℝ G v - A n).le_opNorm z
          _ ≤ η / c (A n) * ‖z‖ := by gcongr
          _ ≤ η / c (A n) * (c (A n) * ‖A n z‖) := by gcongr
          _ = η * ‖A n z‖ := by field_simp
      have hJ : ∀ᵐ v ∂(volume.restrict (t ∩ T n)),
          ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (A n)) ∧
          ENNReal.ofReal (Jf (A n)) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
        filter_upwards [hder, ae_restrict_mem hS] with v hv hvS
        exact ⟨hjcmp _ _ K (hreg v (hSF hvS)) (Ainj n) fun z => (hrel _ _ (hv z)).1,
          hjcmp _ _ K (Ainj n) (hreg v (hSF hvS)) fun z => (hrel _ _ (hv z)).2⟩
      have hup := hcmp G (A n) (t ∩ T n) K (Ainj n).injOn
        fun x hx y hy => (hrel _ _ (happ x hx y hy)).1
      have hlo := hcmp (A n) G (t ∩ T n) K (hinj.mono hSF)
        fun x hx y hy => (hrel _ _ (happ x hx y hy)).2
      rw [hlin (A n) (Ainj n), ← setLIntegral_const] at hup hlo
      have hKtop : (K : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
      constructor
      · calc μHE[m] (G '' (t ∩ T n))
            ≤ (K : ℝ≥0∞) ^ m * ∫⁻ _ in t ∩ T n, ENNReal.ofReal (Jf (A n)) := hup
          _ ≤ (K : ℝ≥0∞) ^ m * ∫⁻ v in t ∩ T n, (K : ℝ≥0∞) ^ m *
                ENNReal.ofReal (Jf (fderiv ℝ G v)) :=
            mul_le_mul_right (lintegral_mono_ae (hJ.mono fun v hv => hv.2)) _
          _ = _ := by rw [lintegral_const_mul' _ _ hKtop, ← mul_assoc, sq]
      · calc ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v))
            ≤ ∫⁻ _ in t ∩ T n, (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (A n)) :=
            lintegral_mono_ae (hJ.mono fun v hv => hv.1)
          _ = (K : ℝ≥0∞) ^ m * ∫⁻ _ in t ∩ T n, ENNReal.ofReal (Jf (A n)) :=
            lintegral_const_mul' _ _ hKtop
          _ ≤ (K : ℝ≥0∞) ^ m * ((K : ℝ≥0∞) ^ m * μHE[m] (G '' (t ∩ T n))) :=
            mul_le_mul_right hlo _
          _ = _ := by rw [← mul_assoc, sq]
    have hdisj : Pairwise (Disjoint on fun n => t ∩ T n) := fun i j hij =>
      Disjoint.mono inter_subset_right inter_subset_right (Tdisj hij)
    have hunion : t = ⋃ n, t ∩ T n := by rw [← inter_iUnion, inter_eq_left.2 tT]
    have hX : μHE[m] (G '' t) = ∑' n, μHE[m] (G '' (t ∩ T n)) := by
      rw [show G '' t = ⋃ n, G '' (t ∩ T n) by rw [← image_iUnion, ← hunion]]
      exact measure_iUnion (fun i j hij => Disjoint.image (hdisj hij) (hinj.mono htF)
          inter_subset_left inter_subset_left)
        fun n => (ht.inter (Tmeas n)).image_of_continuousOn_injOn
          (hcont.mono (inter_subset_left.trans htF)) (hinj.mono (inter_subset_left.trans htF))
    have hY : ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) =
        ∑' n, ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
      conv_lhs => rw [hunion]
      exact lintegral_iUnion (fun n => ht.inter (Tmeas n)) hdisj _
    rw [hX, hY, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    exact ⟨ENNReal.tsum_le_tsum fun n => (hpc n).1, ENNReal.tsum_le_tsum fun n => (hpc n).2⟩
  -- (7) Letting `η → 0`: `Hᵐ(G t) = ∫_t J` for every Borel `t ⊆ F`.
  have hmeas : ∀ t ⊆ F, MeasurableSet t →
      μHE[m] (G '' t) = ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
    intro t htF ht
    have hlim : Tendsto (fun η : ℝ => (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2) (𝓝[>] 0)
        (𝓝 1) := by
      have hc : Continuous fun η : ℝ => ((1 + 2 * η).toNNReal ^ m) ^ 2 :=
        ((continuous_real_toNNReal.comp (by fun_prop)).pow m).pow 2
      simpa using ENNReal.tendsto_coe.2 ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 / 2 :=
      Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
    have hlim' : ∀ X : ℝ≥0∞, Tendsto (fun η : ℝ => (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 * X)
        (𝓝[>] 0) (𝓝 X) := fun X => by
      simpa using ENNReal.Tendsto.mul_const hlim (Or.inl one_ne_zero)
    apply le_antisymm
    · refine ge_of_tendsto (hlim' _) ?_
      filter_upwards [hev] with η hη
      exact (hpiece η hη.1 hη.2 t htF ht).1
    · refine ge_of_tendsto (hlim' _) ?_
      filter_upwards [hev] with η hη
      exact (hpiece η hη.1 hη.2 t htF ht).2
  -- (8) From the measure identity to the integral identity, as in
  -- `integral_image_eq_integral_abs_det_fderiv_smul`: `G|_F` is a measurable embedding.
  have hJm : Measurable fun v => Jf (fderiv ℝ G v) := by
    have : Continuous Jf := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_matrix fun i j => ?_))
      exact (continuous_id.clm_apply continuous_const).inner
        (continuous_id.clm_apply continuous_const)
    exact this.measurable.comp (measurable_fderiv ℝ G)
  have hemb : MeasurableEmbedding (F.domRestrict G) :=
    { injective := injOn_iff_injective.1 hinj
      measurable := (continuousOn_iff_continuous_domRestrict.1 hcont).measurable
      measurableSet_image' := fun s hs => by
        rw [domRestrict_eq, image_comp]
        exact (hF.subtype_image hs).image_of_continuousOn_injOn
          (hcont.mono (Subtype.coe_image_subset F s)) (hinj.mono (Subtype.coe_image_subset F s)) }
  have hmap : Measure.map (F.domRestrict G) (Measure.comap Subtype.val
      (volume.withDensity fun v => ENNReal.ofReal (Jf (fderiv ℝ G v)))) =
      μHE[m].restrict (G '' F) := by
    ext u hu
    have hpre : MeasurableSet (F.domRestrict G ⁻¹' u) := hemb.measurable hu
    have hset : Subtype.val '' (F.domRestrict G ⁻¹' u) = F ∩ G ⁻¹' u :=
      Subtype.image_preimage_coe F (G ⁻¹' u)
    have htm : MeasurableSet (F ∩ G ⁻¹' u) := hset ▸ hF.subtype_image hpre
    rw [Measure.map_apply hemb.measurable hu,
      Measure.comap_apply _ Subtype.val_injective (fun _ hs => hF.subtype_image hs) _ hpre, hset,
      withDensity_apply _ htm, Measure.restrict_apply hu, ← hmeas _ inter_subset_left htm,
      image_inter_preimage, inter_comm]
  rw [← hmap, hemb.integral_map]
  simp only [domRestrict_apply, ← comp_apply (f := h), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hF).integral_map, map_comap_subtype_coe hF,
    setIntegral_withDensity_eq_setIntegral_smul₀ hJm.real_toNNReal.aemeasurable _ hF]
  refine setIntegral_congr_fun hF fun v _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rfl
/-- **The cone parametrization `G(t, α) = tγ(α)` is an injective immersion** (the regularity
hypotheses of the area formula, Simon Ch. 2, §3, for a piece of a cone over a unit curve; this is
used to show that 2-dimensional area minimizing cones are unions of planes in the proof of
Simon 7.3.3(1), p. 191).  Let `γ` be `C¹` and injective on `I = (-s, s)` with `‖γ‖ = 1`,
`γ ⊥ γ'` and `γ' ≠ 0` there, and let `R = (r₀ - s, r₀ + s) × I`, so `t > r₀ - s > 0` on `R`.
Taking norms in `tγ(α) = t'γ(α')` gives `t = t'`, so `G` is injective on `R`.  By the product rule
`DG(t, α)(a, b) = aγ(α) + tbγ'(α)`, which is injective: pairing with `γ(α)` forces `a = 0`, and
then `tbγ'(α) = 0` forces `b = 0`. -/
theorem Submission.idtp_ccd_scsp_ca_cone_map_regular : ∀ (P : ℕ) (r₀ s : ℝ) (γ : ℝ → Euclid P), 0 < s → s < r₀ → ContDiffOn ℝ 1 γ (Ioo (-s) s) → InjOn γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ inner ℝ (γ α) (deriv γ α) = 0 ∧ deriv γ α ≠ 0) → InjOn (fun q : ℝ × ℝ => q.1 • γ q.2) (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s) ∧ ∀ z ∈ Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s, DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1 • γ q.2) z ∧ Injective (fderiv ℝ (fun q : ℝ × ℝ => q.1 • γ q.2) z) ∧ fderiv ℝ (fun q : ℝ × ℝ => q.1 • γ q.2) z (1, 0) = γ z.2 ∧ fderiv ℝ (fun q : ℝ × ℝ => q.1 • γ q.2) z (0, 1) = z.1 • deriv γ z.2 := by
  intro P r₀ s γ _ hsr hγ hinj hcurve
  -- (1) `t > r₀ - s > 0` on the box
  have hpos : ∀ t ∈ Ioo (r₀ - s) (r₀ + s), 0 < t := fun t ht => by linarith [ht.1]
  refine ⟨?_, ?_⟩
  · -- (2) taking norms gives `t = t'`; cancelling `t ≠ 0` and injectivity of `γ` give `α = α'`
    rintro ⟨t, α⟩ ⟨ht, hα⟩ ⟨t', α'⟩ ⟨ht', hα'⟩ heq
    simp only at ht hα ht' hα' heq
    have hnorm := congrArg norm heq
    rw [norm_smul, norm_smul, (hcurve α hα).1, (hcurve α' hα').1, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hpos t ht), abs_of_pos (hpos t' ht'), mul_one, mul_one]
      at hnorm
    subst hnorm
    rw [hinj hα hα' (smul_right_injective _ (hpos t ht).ne' heq)]
  · rintro ⟨t, α⟩ ⟨ht, hα⟩
    simp only at ht hα ⊢
    obtain ⟨hnorm, horth, hne⟩ := hcurve α hα
    -- (3) `γ` is differentiable at `α`, being `C¹` on the open interval `I`
    have hdγ : HasDerivAt γ (deriv γ α) α :=
      ((hγ.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds hα.1 hα.2)).hasDerivAt
    -- (4) product and chain rules: `DG(t, α)(a, b) = t b γ'(α) + a γ(α)`
    have h1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, α) :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (γ ∘ Prod.snd) ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv γ α)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (t, α) :=
      hdγ.hasFDerivAt.comp (t, α) hasFDerivAt_snd
    have hD : HasFDerivAt (fun q : ℝ × ℝ => q.1 • γ q.2) (t • ((ContinuousLinearMap.smulRight
        (1 : ℝ →L[ℝ] ℝ) (deriv γ α)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (γ α)) (t, α) :=
      h1.smul h2
    -- (5) `DG(1, 0) = γ(α)` and `DG(0, 1) = tγ'(α)`
    rw [hD.fderiv]
    refine ⟨hD.differentiableAt, ?_, by simp, by simp⟩
    -- (6) pairing `DG(a, b) = 0` with `γ(α)` gives `a = 0`; then `t b γ'(α) = 0` gives `b = 0`
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', one_apply_eq_self] at hab
    have ha : a = 0 := by
      have := congrArg (fun v => inner ℝ (γ α) v) hab
      simpa [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm, horth]
        using this
    subst ha
    simp only [zero_smul, add_zero, smul_smul, smul_eq_zero, hne, or_false, mul_eq_zero,
      (hpos t ht).ne', false_or] at hab
    exact Prod.mk_eq_zero.2 ⟨rfl, hab⟩

/-- **Area formula for an injective immersion of a subset of `ℝ × ℝ`** (Simon Ch. 2, 3.1–3.5
with `m = 2`; used for the area of the cone parametrization `(t, α) ↦ t γ(α)`).  Let
`G : ℝ × ℝ → ℝᴾ` be differentiable with injective derivative at every point of the measurable
set `R` and injective on `R`, and write `∂₁G = DG(1, 0)`, `∂₂G = DG(0, 1)`.  Every
`h : ℝᴾ → ℝ` has `∫_{G(R)} h dH² = ∫_R (‖∂₁G‖²‖∂₂G‖² − ⟨∂₁G, ∂₂G⟩²)^{1/2} h(G(q)) dq`.

Transport along the volume-preserving coordinate equivalence `e : ℝ² ≃ ℝ × ℝ`,
`e w = (w₀, w₁)`: apply the Gram form of the area formula to `G ∘ e` on `e⁻¹(R)`, expand the
`2 × 2` Gram determinant, and pull the integral back to `R`. -/
theorem Submission.idtp_ccd_scsp_ca_prod_area_formula : ∀ (P : ℕ) (G : ℝ × ℝ → Euclid P) (R : Set (ℝ × ℝ)) (h : Euclid P → ℝ), MeasurableSet R → (∀ q ∈ R, DifferentiableAt ℝ G q) → (∀ q ∈ R, Injective (fderiv ℝ G q)) → InjOn G R → ∫ x in G '' R, h x ∂μHE[2] = ∫ q in R, Real.sqrt (‖fderiv ℝ G q (1, 0)‖ ^ 2 * ‖fderiv ℝ G q (0, 1)‖ ^ 2 - inner ℝ (fderiv ℝ G q (1, 0)) (fderiv ℝ G q (0, 1)) ^ 2) * h (G q) := by
  intro P G R h hR hG hreg hinj
  -- (1) `e : ℝ² ≃ ℝ × ℝ`, `e w = (w₀, w₁)`, preserves Lebesgue measure
  let e : Euclid 2 ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have he : ∀ w, e w = (w 0, w 1) := fun w => rfl
  have hmp : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  -- (2) `D(G ∘ e)(w) = DG(e w) ∘ e`, so `G ∘ e` satisfies the Gram area formula on `e⁻¹(R)`,
  -- and `(G ∘ e)(e⁻¹(R)) = G(R)` since `e` is onto
  have hfd : ∀ w, fderiv ℝ (G ∘ e) w = (fderiv ℝ G (e w)).comp (e : Euclid 2 →L[ℝ] ℝ × ℝ) :=
    fun w => e.comp_right_fderiv
  have key := Submission.codim1_lur_cd_injective_area_formula_gram P 2 (G ∘ e) (e ⁻¹' R)
    (e.continuous.measurable hR) (fun w hw => (hG (e w) hw).comp w e.differentiableAt)
    (fun w hw => by rw [hfd]; exact (hreg (e w) hw).comp e.injective)
    (fun w hw w' hw' heq => e.injective (hinj hw hw' heq)) h
  rw [Set.image_comp, Set.image_preimage_eq R e.surjective] at key
  rw [key]
  -- (3) `e e₀ = (1, 0)`, `e e₁ = (0, 1)`, so the `2 × 2` Gram determinant at `w` is
  -- `‖∂₁G‖²‖∂₂G‖² − ⟨∂₁G, ∂₂G⟩²` at `e w`
  have h0 : e (EuclideanSpace.single 0 1) = (1, 0) := by rw [he]; simp
  have h1 : e (EuclideanSpace.single 1 1) = (0, 1) := by rw [he]; simp
  let Ψ : ℝ × ℝ → ℝ := fun q => Real.sqrt (‖fderiv ℝ G q (1, 0)‖ ^ 2 *
    ‖fderiv ℝ G q (0, 1)‖ ^ 2 - inner ℝ (fderiv ℝ G q (1, 0)) (fderiv ℝ G q (0, 1)) ^ 2) * h (G q)
  have hpt : ∀ w : Euclid 2, Real.sqrt (Matrix.det (Matrix.of fun i j : Fin 2 =>
      inner ℝ (fderiv ℝ (G ∘ e) w (EuclideanSpace.single i 1))
        (fderiv ℝ (G ∘ e) w (EuclideanSpace.single j 1)))) * h ((G ∘ e) w) = Ψ (e w) := by
    intro w
    simp only [Ψ, hfd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, h0, h1,
      Matrix.det_fin_two, Matrix.of_apply, Function.comp_apply, real_inner_self_eq_norm_sq,
      real_inner_comm (fderiv ℝ G (e w) (1, 0))]
    ring_nf
  -- (4) pull the integral back from `e⁻¹(R)` to `R`
  simp_rw [hpt]
  exact hmp.setIntegral_preimage_emb hemb Ψ R

/-- **Smooth cutoff near a compact set** (step 3 of the parent proof).  Take `δ > 0` with
`cthickening δ K ⊆ N`.  The smooth Urysohn lemma for the closed set `cthickening (δ / 4) K`
inside the open set `thickening (δ / 2) K` gives a `C¹` function `ζ` with
`support ζ = thickening (δ / 2) K` and `ζ = 1` exactly on `cthickening (δ / 4) K`.  Then
`tsupport ζ ⊆ cthickening (δ / 2) K ⊆ N` is a closed subset of a compact set, and
`V = thickening (δ / 4) K` is an open plateau around `K`. -/
theorem Submission.idtp_ccd_scsp_tf_cutoff : ∀ (P : ℕ) (K N : Set (Euclid P)), IsCompact K → IsOpen N → K ⊆ N → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ N ∧ ∃ V : Set (Euclid P), IsOpen V ∧ K ⊆ V ∧ ∀ y ∈ V, ζ y = 1 := by
  intro P K N hK hN hKN
  -- a margin: `cthickening δ K ⊆ N` for some `δ > 0`
  obtain ⟨δ, hδ, hδN⟩ := hK.exists_cthickening_subset_open hN hKN
  -- smooth Urysohn: `ζ = 1` exactly on `cthickening (δ / 4) K`, `support ζ = thickening (δ / 2) K`
  obtain ⟨ζ, hζ, -, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
    (isOpen_thickening (δ := δ / 2) (E := K)) (isClosed_cthickening (δ := δ / 4) (E := K))
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
  have hts : tsupport ζ ⊆ cthickening (δ / 2) K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening _ _
  -- the plateau `V = thickening (δ / 4) K ⊆ cthickening (δ / 4) K`
  refine ⟨ζ, by exact_mod_cast hζ, ?_, ?_, thickening (δ / 4) K, isOpen_thickening,
    self_subset_thickening (by positivity) K,
    fun y hy => (hone y).1 (thickening_subset_cthickening _ _ hy)⟩
  -- `tsupport ζ` is closed inside the compact set `cthickening (δ / 2) K` (`Euclid P` is proper)
  · exact hK.cthickening.of_isClosed_subset (isClosed_tsupport ζ) hts
  · exact hts.trans ((cthickening_mono (by linarith) K).trans hδN)
/-- **Tangential derivative of the angle–radius profile** (steps 1 and 6(iii) of the parent
proof).  With `a = ⟨x, u⟩ > 0` and `b = ⟨x, e⟩`, the inverse and product rules differentiate
`q = ⟨·, e⟩ / ⟨·, u⟩` to `h ↦ a⁻¹ ⟨h, e⟩ − b (a²)⁻¹ ⟨h, u⟩`, and the chain rule multiplies this
by `(1 + (b / a)²)⁻¹ = a² / (a² + b²)` for `arctan ∘ q`.  The norm `‖y‖ = √(‖y‖²)` has derivative
`h ↦ ⟨x, h⟩ / ‖x‖`, which vanishes for `⟨x, h⟩ = 0`, so the product rule leaves only the angular
term.  `C¹` regularity follows from `a ≠ 0` and `x ≠ 0`. -/
theorem Submission.idtp_ccd_scsp_tf_profile_deriv : ∀ (P : ℕ) (u e x : Euclid P) (φ lam : ℝ → ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 lam → 0 < inner ℝ x u → ContDiffAt ℝ 1 (fun y : Euclid P => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖) x ∧ ∀ h : Euclid P, inner ℝ x h = 0 → fderiv ℝ (fun y : Euclid P => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖) x h = deriv φ (Real.arctan (inner ℝ x e / inner ℝ x u)) * lam ‖x‖ * ((inner ℝ x u * inner ℝ h e - inner ℝ x e * inner ℝ h u) / (inner ℝ x u ^ 2 + inner ℝ x e ^ 2)) := by
  intro P u e x φ lam hφ hlam hxu
  -- non-degeneracy: `a = ⟨x, u⟩ ≠ 0`, hence `x ≠ 0`
  have ha : inner ℝ x u ≠ 0 := hxu.ne'
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hxu
  refine ⟨?_, fun h hh => ?_⟩
  · -- `C¹`: a quotient with nonvanishing denominator, `arctan`, and the norm away from `0`
    have hq : ContDiffAt ℝ 1 (fun y : Euclid P => inner ℝ y e / inner ℝ y u) x :=
      (contDiffAt_id.inner ℝ contDiffAt_const).div (contDiffAt_id.inner ℝ contDiffAt_const) ha
    exact (hφ.contDiffAt.comp x hq.arctan).mul (hlam.contDiffAt.comp x (contDiffAt_norm ℝ hx))
  · -- the linear coordinates `y ↦ ⟨y, z⟩` are `innerSL ℝ z`
    have hlin : ∀ z : Euclid P, HasFDerivAt (fun y : Euclid P => inner ℝ y z) (innerSL ℝ z) x := by
      intro z
      have hz : (fun y : Euclid P => inner ℝ y z) = innerSL ℝ z := by
        funext y
        rw [innerSL_apply_apply, real_inner_comm]
      rw [hz]
      exact (innerSL ℝ z).hasFDerivAt
    -- the quotient `q = ⟨·, e⟩ · ⟨·, u⟩⁻¹`
    have hinv : HasFDerivAt (fun y : Euclid P => (inner ℝ y u)⁻¹)
        ((-(inner ℝ x u ^ 2)⁻¹) • innerSL ℝ u) x :=
      (hasDerivAt_inv ha).comp_hasFDerivAt x (hlin u)
    have hq : HasFDerivAt (fun y : Euclid P => inner ℝ y e / inner ℝ y u)
        (inner ℝ x e • ((-(inner ℝ x u ^ 2)⁻¹) • innerSL ℝ u) +
          (inner ℝ x u)⁻¹ • innerSL ℝ e) x := by
      simp only [div_eq_mul_inv]
      exact (hlin e).fun_mul hinv
    -- the angle `arctan ∘ q` and the outer profile `φ`
    have hΦ := (hφ.differentiable one_ne_zero
      (Real.arctan (inner ℝ x e / inner ℝ x u))).hasDerivAt.comp_hasFDerivAt x hq.arctan
    -- the norm `‖y‖ = √(‖y‖²)` and the radial profile `lam`
    have hN : HasFDerivAt (fun y : Euclid P => ‖y‖)
        ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x := by
      have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
        (pow_ne_zero 2 (norm_ne_zero_iff.2 hx))
      have hfun : (fun y : Euclid P => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
        funext y
        exact Real.sqrt_sq (norm_nonneg y)
      rwa [hfun] at hs
    have hL := (hlam.differentiable one_ne_zero ‖x‖).hasDerivAt.comp_hasFDerivAt x hN
    -- the product rule; the radial term `⟨x, h⟩ / ‖x‖` vanishes since `⟨x, h⟩ = 0`
    have hF : HasFDerivAt
        (fun y : Euclid P => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖) _ x :=
      hΦ.fun_mul hL
    rw [hF.fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply, hh,
      smul_zero, mul_zero, zero_add]
    -- clearing `1 + (b / a)² = (a² + b²) / a²` with `a ≠ 0`
    rw [real_inner_comm h u, real_inner_comm h e]
    field_simp
    ring
/-- **Tangential divergence of the rotation field** (steps 4–5 of the parent proof).  With the
skew map `A y = ⟨y, u⟩ e − ⟨y, e⟩ u`, the field is `X = g • A`, so the product rule gives
`DX(x) h = g(x) A h + (Dg(x) h) A x` at `x = t v`.  The frame formula in the orthonormal frame
`(v, w)` of `Q` gives `tr(p_Q ∘ DX(x)) = ⟨v, DX(x) v⟩ + ⟨w, DX(x) w⟩`; skewness `⟨z, A z⟩ = 0`
and `A x = t A v` leave only `(Dg(x) w) t ⟨w, A v⟩`. -/
theorem Submission.idtp_ccd_scsp_tf_rotation_trace : ∀ (P : ℕ) (u e v w : Euclid P) (Q : Submodule ℝ (Euclid P)) (g : Euclid P → ℝ) (t : ℝ), Orthonormal ℝ ![v, w] → Submodule.span ℝ (Set.range ![v, w]) = Q → DifferentiableAt ℝ g (t • v) → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y : Euclid P => g y • (inner ℝ y u • e - inner ℝ y e • u)) (t • v)).toLinearMap) = fderiv ℝ g (t • v) w * (t * (inner ℝ v u * inner ℝ w e - inner ℝ v e * inner ℝ w u)) := by
  intro P u e v w Q g t hτ hQ hg
  -- the skew continuous linear map `A y = ⟪y, u⟫ e - ⟪y, e⟫ u`, so that `X = g • A`
  obtain ⟨A, hA⟩ : ∃ A : Euclid P →L[ℝ] Euclid P,
      ∀ y, A y = inner ℝ y u • e - inner ℝ y e • u :=
    ⟨(innerSL ℝ u).smulRight e - (innerSL ℝ e).smulRight u, fun y => by simp [real_inner_comm]⟩
  have hX : (fun y : Euclid P => g y • (inner ℝ y u • e - inner ℝ y e • u)) =
      fun y => g y • A y := by
    funext y
    rw [hA]
  -- product rule: `DX(x) = g(x) A + Dg(x) ⊗ A x`
  have hD : HasFDerivAt (fun y : Euclid P => g y • A y)
      (g (t • v) • A + (fderiv ℝ g (t • v)).smulRight (A (t • v))) (t • v) :=
    hg.hasFDerivAt.smul A.hasFDerivAt
  -- frame formula in the orthonormal frame `(v, w)` of `Q`, then expand the two diagonal entries
  rw [Submission.fvmb_trace_starProjection_comp_eq_sum_inner P 2 Q ![v, w] _ hτ hQ, hX, hD.fderiv]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hA, inner_add_right, inner_sub_right, inner_smul_right,
    real_inner_smul_left]
  ring

/-- **Test field on the cone over `γ`** (steps 7–8 of the parent proof).  Let
`A y = ⟨y, u⟩ e − ⟨y, e⟩ u`, `F y = φ(arctan(⟨y, e⟩ / ⟨y, u⟩)) λ(‖y‖)`, and let `ζ` be a `C¹`
cutoff with compact support in `N` and `ζ ≡ 1` near the compact set
`K₀ = {t γ(α) : t ∈ spt λ, α ∈ spt φ} ⊆ N`; then `X = F ζ A`.  In the orthonormal frame
`(γ, τ = γ′/‖γ′‖)` of `T(t γ)` the trace is `D(F ζ)(t γ) τ · t ⟨A γ, τ⟩`, where
`D(F ζ)(t γ) τ = DF(t γ) τ` (`ζ ≡ 1` near `K₀`, while off `K₀` both `F(t γ)` and `DF(t γ) τ`
vanish) and `⟨A γ, γ′⟩ = ⟨γ, u⟩² + ⟨γ, e⟩²`. -/
theorem Submission.idtp_ccd_scsp_test_field : ∀ (P : ℕ) (u e : Euclid P) (r₀ s : ℝ) (N : Set (Euclid P)) (γ : ℝ → Euclid P) (T : Euclid P → Submodule ℝ (Euclid P)) (lam φ : ℝ → ℝ), ‖u‖ = 1 → ‖e‖ = 1 → inner ℝ u e = 0 → 0 < s → s < r₀ → IsOpen N → (∀ x ∈ N, 0 < inner ℝ x u) → ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → (∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, t • γ α ∈ N ∧ T (t • γ α) = Submodule.span ℝ {γ α, deriv γ α}) → ContDiff ℝ 1 lam → HasCompactSupport lam → tsupport lam ⊆ Ioo (r₀ - s) (r₀ + s) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ioo (-s) s → ∃ X : Euclid P → Euclid P, ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ N ∧ ∀ t ∈ Ioo (r₀ - s) (r₀ + s), ∀ α ∈ Ioo (-s) s, LinearMap.trace ℝ (Euclid P) ((T (t • γ α)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X (t • γ α)).toLinearMap) = lam t * deriv φ α * ((inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2) / ‖deriv γ α‖ ^ 2) := by
  intro P u e r₀ s N γ T lam φ _ _ _ _ hsr hN hNu hγ hγp hTN hlam hlamc hlams hφ hφc hφs
  -- `K₀ = {t γ(α) : t ∈ tsupport λ, α ∈ tsupport φ}` is a compact subset of `N`
  have hK₀ : IsCompact ((fun p : ℝ × ℝ => p.1 • γ p.2) '' (tsupport lam ×ˢ tsupport φ)) :=
    (hlamc.isCompact.prod hφc.isCompact).image_of_continuousOn
      (continuousOn_fst.smul (hγ.continuousOn.comp continuousOn_snd fun p hp => hφs hp.2))
  have hK₀N : (fun p : ℝ × ℝ => p.1 • γ p.2) '' (tsupport lam ×ˢ tsupport φ) ⊆ N := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hTN p.1 (hlams hp.1) p.2 (hφs hp.2)).1
  -- a `C¹` cutoff `ζ` with compact support in `N` and `ζ ≡ 1` on an open `V ⊇ K₀`
  obtain ⟨ζ, hζ, hζc, hζN, V, hVo, hKV, hζV⟩ :=
    Submission.idtp_ccd_scsp_tf_cutoff P _ N hK₀ hN hK₀N
  -- the profile `F(y) = φ(arctan(⟨y, e⟩ / ⟨y, u⟩)) λ(‖y‖)` and the coefficient `g = F ζ`
  obtain ⟨F, hFdef⟩ : ∃ F : Euclid P → ℝ,
      F = fun y => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖ := ⟨_, rfl⟩
  have hF : ∀ x : Euclid P, 0 < inner ℝ x u → ContDiffAt ℝ 1 F x ∧ ∀ h : Euclid P,
      inner ℝ x h = 0 → fderiv ℝ F x h = deriv φ (Real.arctan (inner ℝ x e / inner ℝ x u)) *
        lam ‖x‖ * ((inner ℝ x u * inner ℝ h e - inner ℝ x e * inner ℝ h u) /
          (inner ℝ x u ^ 2 + inner ℝ x e ^ 2)) := by
    intro x hx
    rw [hFdef]
    exact Submission.idtp_ccd_scsp_tf_profile_deriv P u e x φ lam hφ hlam hx
  obtain ⟨g, hgdef⟩ : ∃ g : Euclid P → ℝ, g = fun y => F y * ζ y := ⟨_, rfl⟩
  -- `g` is `C¹`: both factors are `C¹` near points of `N ⊆ {⟨·, u⟩ > 0}`, and `g` vanishes near
  -- every point off `tsupport ζ ⊆ N`
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ N
    · rw [hgdef]
      exact (hF y (hNu y hy)).1.mul hζ.contDiffAt
    · have h0 : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h => hy (hζN h)] with z hz
        simp [hgdef, hz]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hXζ : support (fun y => g y • (inner ℝ y u • e - inner ℝ y e • u)) ⊆ support ζ := by
    intro y hy
    rw [mem_support] at hy ⊢
    intro h
    apply hy
    simp [hgdef, h]
  -- the field `X(y) = g(y) (⟨y, u⟩ e - ⟨y, e⟩ u)`
  refine ⟨fun y => g y • (inner ℝ y u • e - inner ℝ y e • u), ?_, hζc.mono hXζ,
    (closure_mono hXζ).trans hζN, ?_⟩
  · exact hg.smul (((contDiff_id.inner ℝ contDiff_const).smul contDiff_const).sub
      ((contDiff_id.inner ℝ contDiff_const).smul contDiff_const))
  intro t ht α hα
  obtain ⟨-, hTx⟩ := hTN t ht α hα
  obtain ⟨hγ1, hγu, hγarc⟩ := hγp α hα
  obtain ⟨horth, hkey, hne⟩ := Submission.idtp_ccd_scsp_angle_curve P u e s γ hγ hγp α hα
  have ht0 : 0 < t := by linarith [ht.1]
  have hc : 0 < ‖deriv γ α‖ := norm_pos_iff.mpr hne
  -- the orthonormal frame `(γ(α), τ)` of `T(t γ(α))`, `τ = γ′(α) / ‖γ′(α)‖`
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclid P, τ = ‖deriv γ α‖⁻¹ • deriv γ α := ⟨_, rfl⟩
  have hτ1 : ‖τ‖ = 1 := by
    rw [hτ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
  have hγτ : inner ℝ (γ α) τ = 0 := by
    rw [hτ, real_inner_smul_right, horth, mul_zero]
  have hon : Orthonormal ℝ ![γ α, τ] := by
    simp [orthonormal_vecCons_iff, hγ1, hτ1, hγτ]
  have hspan : Submodule.span ℝ (Set.range ![γ α, τ]) = T (t • γ α) := by
    rw [hTx, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.span_insert, Submodule.span_insert, hτ,
      Submodule.span_singleton_smul_eq (inv_pos.mpr hc).ne'.isUnit]
  refine (Submission.idtp_ccd_scsp_tf_rotation_trace P u e (γ α) τ (T (t • γ α)) g t hon hspan
    (hg.differentiable one_ne_zero _)).trans ?_
  -- the point `x = t γ(α)`: `⟨x, u⟩ > 0`, `‖x‖ = t`, `arctan(⟨x, e⟩ / ⟨x, u⟩) = α`, `x ⊥ τ`
  have hxu : 0 < inner ℝ (t • γ α) u := by
    rw [real_inner_smul_left]
    positivity
  have hnx : ‖t • γ α‖ = t := by
    rw [norm_smul, hγ1, mul_one, Real.norm_of_nonneg ht0.le]
  have hfx : Real.arctan (inner ℝ (t • γ α) e / inner ℝ (t • γ α) u) = α := by
    rw [real_inner_smul_left, real_inner_smul_left, mul_div_mul_left _ _ ht0.ne', hγarc]
  have hxτ : inner ℝ (t • γ α) τ = 0 := by
    rw [real_inner_smul_left, hγτ, mul_zero]
  obtain ⟨hFx, hDFx⟩ := hF (t • γ α) hxu
  have hDF := hDFx τ hxτ
  rw [hfx, hnx] at hDF
  -- `Dg(x) τ = DF(x) τ`: if `x ∈ V` then `ζ ≡ 1` near `x`; otherwise `(t, α)` lies outside
  -- `tsupport λ × tsupport φ`, so `F(x) = 0` and `DF(x) τ = 0`
  have hDg : fderiv ℝ g (t • γ α) τ = fderiv ℝ F (t • γ α) τ := by
    by_cases hxV : t • γ α ∈ V
    · have hgF : g =ᶠ[𝓝 (t • γ α)] F := by
        filter_upwards [hVo.mem_nhds hxV] with y hy
        simp only [hgdef, hζV y hy, mul_one]
      rw [hgF.fderiv_eq]
    · have hnot : lam t = 0 ∨ (φ α = 0 ∧ deriv φ α = 0) := by
        by_cases hlt : t ∈ tsupport lam
        · have hαφ : α ∉ tsupport φ := fun h => hxV (hKV ⟨(t, α), ⟨hlt, h⟩, rfl⟩)
          exact Or.inr ⟨image_eq_zero_of_notMem_tsupport hαφ,
            notMem_support.mp fun h => hαφ (support_deriv_subset h)⟩
        · exact Or.inl (image_eq_zero_of_notMem_tsupport hlt)
      have hF0 : F (t • γ α) = 0 := by
        simp only [hFdef]
        rw [hfx, hnx]
        rcases hnot with h | h
        · rw [h, mul_zero]
        · rw [h.1, zero_mul]
      have hDF0 : fderiv ℝ F (t • γ α) τ = 0 := by
        rw [hDF]
        rcases hnot with h | h
        · rw [h, mul_zero, zero_mul]
        · rw [h.2, zero_mul, zero_mul]
      rw [hgdef, fderiv_fun_mul (hFx.differentiableAt one_ne_zero)
        (hζ.differentiable one_ne_zero _)]
      simp [hF0, hDF0]
  rw [hDg, hDF, hτ]
  simp only [real_inner_smul_left]
  set A := inner ℝ (γ α) u
  set B := inner ℝ (γ α) e
  set a := inner ℝ (deriv γ α) u
  set b := inner ℝ (deriv γ α) e
  set c := ‖deriv γ α‖
  have hq : 0 < A ^ 2 + B ^ 2 := by positivity
  rw [show t * A * (c⁻¹ * b) - t * B * (c⁻¹ * a) = t * c⁻¹ * (A ^ 2 + B ^ 2) by
      rw [← hkey]; ring,
    show A * (c⁻¹ * b) - B * (c⁻¹ * a) = c⁻¹ * (A ^ 2 + B ^ 2) by rw [← hkey]; ring,
    show (t * A) ^ 2 + (t * B) ^ 2 = t ^ 2 * (A ^ 2 + B ^ 2) by ring]
  field_simp

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

/-- **Area formula on the cone sheet** (step 9 of the parent proof; Simon Ch. 2, §3).  On
`R = (r₀ − s, r₀ + s) × (−s, s)` the sibling `cone_map` shows that `G(t, α) = t γ(α)` is injective
on `R` with injective derivative, `∂₁G = γ(α)` and `∂₂G = t γ′(α)`.  The sibling `prod_area` then
gives `∫_{G(R)} h dH² = ∫_R √(‖∂₁G‖² ‖∂₂G‖² − ⟨∂₁G, ∂₂G⟩²) h(G)`.  Since `‖γ‖ = 1`, `⟨γ, γ′⟩ = 0`
and `t > r₀ − s > 0`, the radicand is `(t ‖γ′(α)‖)²`, so the Jacobian is `t ‖γ′(α)‖`. -/
theorem Submission.idtp_ccd_scsp_cone_area : ∀ (P : ℕ) (r₀ s : ℝ) (γ : ℝ → Euclid P) (h : Euclid P → ℝ), 0 < s → s < r₀ → ContDiffOn ℝ 1 γ (Ioo (-s) s) → InjOn γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ inner ℝ (γ α) (deriv γ α) = 0 ∧ deriv γ α ≠ 0) → ∫ x in (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s), h x ∂μHE[2] = ∫ q in Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s, q.1 * ‖deriv γ q.2‖ * h (q.1 • γ q.2) := by
  intro P r₀ s γ h hs hsr hγ hγinj hγ'
  obtain ⟨hinj, hreg⟩ :=
    Submission.idtp_ccd_scsp_ca_cone_map_regular P r₀ s γ hs hsr hγ hγinj hγ'
  have hR : MeasurableSet (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine (Submission.idtp_ccd_scsp_ca_prod_area_formula P (fun q : ℝ × ℝ => q.1 • γ q.2) _ h hR
    (fun z hz => (hreg z hz).1) (fun z hz => (hreg z hz).2.1) hinj).trans
    (setIntegral_congr_fun hR fun z hz => ?_)
  -- `∂₁G = γ(α)` and `∂₂G = t γ′(α)`, with `‖γ(α)‖ = 1`, `⟨γ(α), γ′(α)⟩ = 0` and `t > 0`
  obtain ⟨-, -, h10, h01⟩ := hreg z hz
  obtain ⟨hnorm, horth, -⟩ := hγ' z.2 hz.2
  have hz1 : 0 < z.1 := by linarith [hz.1.1]
  have hJ : (1 : ℝ) ^ 2 * (z.1 * ‖deriv γ z.2‖) ^ 2 - (z.1 * 0) ^ 2 =
      (z.1 * ‖deriv γ z.2‖) ^ 2 := by ring
  rw [h10, h01, hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hz1, real_inner_smul_right, horth,
    hJ, Real.sqrt_sq (mul_nonneg hz1.le (norm_nonneg _))]

end GMT.Ch07
