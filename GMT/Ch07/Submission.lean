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

/-! ## Smoothness of `C¹` weak solutions of `Δu = div G(Du)` with small gradient

DAG node `…smooth_regularity-a1.quasilinear_smooth-a1` (Simon Ch. 5, end of the proof of
Theorem 7.1: "standard elliptic theory implies `u ∈ C^{q+2,α}`").  Notation: the weak-form
integrand is `∑ⱼ ⟨A eⱼ, Dζ eⱼ⟩`; `C^{l,α}_loc(Ω)` is the class of `codim1_hcp_sr_holder_algebra`.

The interior `C^{1,α}` estimate enters `codim1_hcp_sr_qs_of_c1alpha` as the hypothesis `hc1`, in
the form of the natural-language statement of the `c1alpha_estimate` node
(`∫ ‖F - c‖² ≤ ε₁ ∫ ‖Dw - (Dw)_ρ‖² + Kρ^{2α} ∫ ‖Dw‖² + Kρ^{m+2α}`): the frozen Lean type of
`codim1_hcp_sr_c1alpha_estimate` writes this bound without parentheses, and since the body of
`∫ x in s, _` extends over `+`, Lean reads it as
`ε₁ * ∫ z, (‖Dw z - (Dw)_ρ‖² + Kρ^{2α} * ∫ z', (‖Dw z'‖² + Kρ^{m+2α}))`, which step 2 cannot
supply on small balls. -/

/-- The weak-form integrand `∑ⱼ ⟨A eⱼ, Dζ eⱼ⟩` vanishes off `tsupport ζ`. -/
theorem Submission.codim1_hcp_sr_qs_pair_eq_zero {m k : ℕ}
    (A : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k) {y : Euclid m}
    (hy : y ∉ tsupport ζ) :
    ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) = 0 := by
  have h : fderiv ℝ ζ y = 0 := notMem_support.mp fun h => hy (support_fderiv_subset ℝ h)
  simp [h]

/-- A weak-form integral over a set containing `tsupport ζ` is an integral over `ℝᵐ`. -/
theorem Submission.codim1_hcp_sr_qs_setIntegral_pair {m k : ℕ}
    (A : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k) {S : Set (Euclid m)}
    (hS : tsupport ζ ⊆ S) :
    ∫ y in S, ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
      ∫ y, ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy =>
    Submission.codim1_hcp_sr_qs_pair_eq_zero A ζ fun h => hy (hS h)

/-- The weak-form integrand is integrable when `A` is continuous on `tsupport ζ`. -/
theorem Submission.codim1_hcp_sr_qs_integrable_pair {m k : ℕ}
    {A : Euclid m → (Euclid m →L[ℝ] Euclid k)} {ζ : Euclid m → Euclid k}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hA : ContinuousOn A (tsupport ζ)) :
    Integrable fun y => ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
  have hD : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hcont : ContinuousOn (fun y => ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (tsupport ζ) :=
    continuousOn_finsetSum _ fun j _ =>
      (hA.clm_apply continuousOn_const).inner (hD.continuousOn.clm_apply continuousOn_const)
  exact (hcont.integrableOn_compact hζc.isCompact).integrable_of_forall_notMem_eq_zero
    fun _ hy => Submission.codim1_hcp_sr_qs_pair_eq_zero A ζ hy

/-- Weak-form integrals only see `A` on `tsupport ζ`. -/
theorem Submission.codim1_hcp_sr_qs_integral_pair_congr {m k : ℕ}
    {A A' : Euclid m → (Euclid m →L[ℝ] Euclid k)} {ζ : Euclid m → Euclid k}
    (h : ∀ y ∈ tsupport ζ, A y = A' y) :
    ∫ y, ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
      ∫ y, ∑ j : Fin m, inner ℝ (A' y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
  congr 1
  funext y
  by_cases hy : y ∈ tsupport ζ
  · rw [h y hy]
  · rw [Submission.codim1_hcp_sr_qs_pair_eq_zero A ζ hy,
      Submission.codim1_hcp_sr_qs_pair_eq_zero A' ζ hy]

/-- The weak-form integrand is linear in its first slot: scalars. -/
theorem Submission.codim1_hcp_sr_qs_pair_smul {m k : ℕ} (c : ℝ)
    (A L : Euclid m →L[ℝ] Euclid k) :
    ∑ j : Fin m, inner ℝ ((c • A) (EuclideanSpace.single j (1 : ℝ)))
        (L (EuclideanSpace.single j (1 : ℝ))) =
      c * ∑ j : Fin m, inner ℝ (A (EuclideanSpace.single j (1 : ℝ)))
        (L (EuclideanSpace.single j (1 : ℝ))) := by
  simp [real_inner_smul_left, Finset.mul_sum]

/-- The weak-form integrand is linear in its first slot: differences. -/
theorem Submission.codim1_hcp_sr_qs_pair_sub {m k : ℕ} (A B L : Euclid m →L[ℝ] Euclid k) :
    ∑ j : Fin m, inner ℝ ((A - B) (EuclideanSpace.single j (1 : ℝ)))
        (L (EuclideanSpace.single j (1 : ℝ))) =
      ∑ j : Fin m, inner ℝ (A (EuclideanSpace.single j (1 : ℝ)))
          (L (EuclideanSpace.single j (1 : ℝ))) -
        ∑ j : Fin m, inner ℝ (B (EuclideanSpace.single j (1 : ℝ)))
          (L (EuclideanSpace.single j (1 : ℝ))) := by
  simp [inner_sub_left, Finset.sum_sub_distrib]

/-- `|∑ⱼ ⟨A eⱼ, L eⱼ⟩| ≤ m ‖A‖ ‖L‖`. -/
theorem Submission.codim1_hcp_sr_qs_norm_pair_le {m k : ℕ} (A L : Euclid m →L[ℝ] Euclid k) :
    ‖∑ j : Fin m, inner ℝ (A (EuclideanSpace.single j (1 : ℝ)))
        (L (EuclideanSpace.single j (1 : ℝ)))‖ ≤ m * (‖A‖ * ‖L‖) := by
  calc _ ≤ ∑ j : Fin m, ‖inner ℝ (A (EuclideanSpace.single j (1 : ℝ)))
          (L (EuclideanSpace.single j (1 : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖A‖ * ‖L‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have he : ‖(EuclideanSpace.single j (1 : ℝ) : Euclid m)‖ = 1 := by simp
        calc _ ≤ ‖A (EuclideanSpace.single j (1 : ℝ))‖ * ‖L (EuclideanSpace.single j (1 : ℝ))‖ :=
              norm_inner_le_norm _ _
          _ ≤ (‖A‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euclid m)‖) *
                (‖L‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euclid m)‖) :=
              mul_le_mul (A.le_opNorm _) (L.le_opNorm _) (norm_nonneg _) (by positivity)
          _ = ‖A‖ * ‖L‖ := by rw [he, mul_one, mul_one]
    _ = m * (‖A‖ * ‖L‖) := by simp

/-- An average of a function bounded by `M` on `s` is bounded by `M`. -/
theorem Submission.codim1_hcp_sr_qs_norm_average_le {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Euclid m → F} {s : Set (Euclid m)} {M : ℝ} (hM : 0 ≤ M)
    (hs : volume s < ∞) (hf : ∀ y ∈ s, ‖f y‖ ≤ M) : ‖⨍ y in s, f y‖ ≤ M := by
  rw [setAverage_eq, norm_smul]
  have h1 := norm_setIntegral_le_of_norm_le_const hs hf
  rcases eq_or_ne (volume.real s) 0 with h0 | h0
  · simp [h0, hM]
  · have hpos : 0 < volume.real s := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc (volume.real s)⁻¹ * ‖∫ y in s, f y‖ ≤ (volume.real s)⁻¹ * (M * volume.real s) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
      _ = M := by field_simp

/-- Integrating a pointwise bound `f ≤ a g + b h` over `s`. -/
theorem Submission.codim1_hcp_sr_qs_setIntegral_le {m : ℕ} {f g h : Euclid m → ℝ}
    {s : Set (Euclid m)} {a b : ℝ} (hs : MeasurableSet s) (hf : IntegrableOn f s)
    (hg : IntegrableOn g s) (hh : IntegrableOn h s) (hfgh : ∀ y ∈ s, f y ≤ a * g y + b * h y) :
    ∫ y in s, f y ≤ a * (∫ y in s, g y) + b * ∫ y in s, h y := by
  have hg' : IntegrableOn (fun y => a * g y) s := Integrable.const_mul hg a
  have hh' : IntegrableOn (fun y => b * h y) s := Integrable.const_mul hh b
  calc ∫ y in s, f y ≤ ∫ y in s, (a * g y + b * h y) :=
        setIntegral_mono_on hf (Integrable.add hg' hh') hs hfgh
    _ = a * (∫ y in s, g y) + b * ∫ y in s, h y := by
        rw [integral_add hg' hh', integral_const_mul, integral_const_mul]

/-- Translating a whole-space weak identity `Δ·P = div Q` (tested against maps supported in `Ω`)
by `a`, subtracting, and scaling: the difference-quotient identity of step 2(b). -/
theorem Submission.codim1_hcp_sr_qs_weak_shift {m k : ℕ} {Ω : Set (Euclid m)}
    {P Q : Euclid m → (Euclid m →L[ℝ] Euclid k)}
    (hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (P y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (Q y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
    (hP : ContinuousOn P Ω) (hQ : ContinuousOn Q Ω) (a : Euclid m) (c : ℝ)
    {ζ : Euclid m → Euclid k} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    (hsupp : ∀ y ∈ tsupport ζ, y ∈ Ω ∧ y + a ∈ Ω) :
    ∫ y, ∑ j : Fin m, inner ℝ ((c • (P (y + a) - P y)) (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
      ∫ y, ∑ j : Fin m, inner ℝ ((c • (Q (y + a) - Q y)) (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
  -- the test map `ζ(· - a)` is admissible
  have hζ' : ContDiff ℝ 1 fun y => ζ (y + -a) := hζ.comp (contDiff_id.add contDiff_const)
  have hζ'c : HasCompactSupport fun y => ζ (y + -a) :=
    hζc.comp_homeomorph (Homeomorph.addRight (-a))
  have hζ'Ω : tsupport (fun y => ζ (y + -a)) ⊆ Ω := by
    intro y hy
    have hy' : y + -a ∈ tsupport ζ :=
      tsupport_comp_subset_preimage ζ (f := fun y => y + -a) (continuous_add_const (-a)) hy
    simpa using (hsupp _ hy').2
  -- change of variables `y ↦ y + a`
  have hshift : ∀ A : Euclid m → (Euclid m →L[ℝ] Euclid k),
      ∫ y, ∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ (fun y => ζ (y + -a)) y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (A (y + a) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
    intro A
    rw [← integral_add_right_eq_self (μ := volume) (fun y => ∑ j : Fin m,
      inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ (fun y => ζ (y + -a)) y (EuclideanSpace.single j (1 : ℝ)))) a]
    congr 1
    funext y
    rw [fderiv_comp_add_right, add_neg_cancel_right]
  have h1 := hweak _ hζ' hζ'c hζ'Ω
  rw [hshift P, hshift Q] at h1
  have h2 := hweak ζ hζ hζc fun y hy => (hsupp y hy).1
  have hPa : Integrable fun y => ∑ j : Fin m, inner ℝ (P (y + a) (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
    Submission.codim1_hcp_sr_qs_integrable_pair hζ hζc
      (hP.comp (continuous_add_const a).continuousOn fun y hy => (hsupp y hy).2)
  have hP0 : Integrable fun y => ∑ j : Fin m, inner ℝ (P y (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
    Submission.codim1_hcp_sr_qs_integrable_pair hζ hζc (hP.mono fun y hy => (hsupp y hy).1)
  have hQa : Integrable fun y => ∑ j : Fin m, inner ℝ (Q (y + a) (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
    Submission.codim1_hcp_sr_qs_integrable_pair hζ hζc
      (hQ.comp (continuous_add_const a).continuousOn fun y hy => (hsupp y hy).2)
  have hQ0 : Integrable fun y => ∑ j : Fin m, inner ℝ (Q y (EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
    Submission.codim1_hcp_sr_qs_integrable_pair hζ hζc (hQ.mono fun y hy => (hsupp y hy).1)
  have hlin : ∀ A B : Euclid m → (Euclid m →L[ℝ] Euclid k),
      ∫ y, ∑ j : Fin m, inner ℝ ((c • (A y - B y)) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, c * (∑ j : Fin m, inner ℝ (A y (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) -
          ∑ j : Fin m, inner ℝ (B y (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) := by
    intro A B
    congr 1
    funext y
    rw [Submission.codim1_hcp_sr_qs_pair_smul, Submission.codim1_hcp_sr_qs_pair_sub]
  rw [hlin (fun y => P (y + a)) P, hlin (fun y => Q (y + a)) Q, integral_const_mul,
    integral_const_mul, integral_sub hPa hP0, integral_sub hQa hQ0, h1, h2]

/-- Choice of `ε₀`: on the ball of radius `3ε₀`, `‖DG‖ ≤ Λ` and `DG` is Lipschitz. -/
theorem Submission.codim1_hcp_sr_qs_constants {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : E → E} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hDG0 : fderiv ℝ G 0 = 0)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Λ₂ : ℝ, 0 ≤ Λ₂ ∧ (∀ p : E, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ) ∧
      ∀ p q : E, ‖p‖ ≤ 3 * ε₀ → ‖q‖ ≤ 3 * ε₀ →
        ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ Λ₂ * ‖p - q‖ := by
  have hDG : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.mp hDG.continuous 0 Λ hΛ
  obtain ⟨K, t, ht, hK⟩ :=
    ((hDG.contDiffAt (x := (0 : E))).of_le (by exact_mod_cast le_top)).exists_lipschitzOnWith
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.mem_nhds_iff.mp ht
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  refine ⟨min δ₁ δ₂ / 6, by positivity, K, K.2, fun p hp => ?_, fun p q hp hq => ?_⟩
  · have h := h₁ p (by rw [dist_zero_right]; linarith [min_le_left δ₁ δ₂])
    rw [dist_eq_norm, hDG0, sub_zero] at h
    exact h.le
  · have hp' : p ∈ t := h₂ (by rw [mem_ball_zero_iff]; linarith [min_le_right δ₁ δ₂])
    have hq' : q ∈ t := h₂ (by rw [mem_ball_zero_iff]; linarith [min_le_right δ₁ δ₂])
    have h := hK.dist_le_mul p hp' q hq'
    rwa [dist_eq_norm, dist_eq_norm] at h

/-- Mean value inequality for `G` on the ball of radius `r` where `‖DG‖ ≤ Λ`. -/
theorem Submission.codim1_hcp_sr_qs_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : E → E} (hGd : Differentiable ℝ G) {r Λ : ℝ}
    (hb : ∀ p : E, ‖p‖ ≤ r → ‖fderiv ℝ G p‖ ≤ Λ) {p q : E} (hp : ‖p‖ ≤ r) (hq : ‖q‖ ≤ r) :
    ‖G p - G q‖ ≤ Λ * ‖p - q‖ :=
  (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_fderiv_le (fun z _ => hGd z)
    (fun z hz => hb z (mem_closedBall_zero_iff.mp hz)) (mem_closedBall_zero_iff.mpr hq)
    (mem_closedBall_zero_iff.mpr hp)

/-- Second differences of `G`: `‖(G(p+D) - G p) - (G(q+D) - G q)‖ ≤ Λ₂ ‖D‖ ‖p - q‖`. -/
theorem Submission.codim1_hcp_sr_qs_second_diff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : E → E} (hGd : Differentiable ℝ G) {r ε Λ₂ : ℝ}
    (hlip : ∀ p q : E, ‖p‖ ≤ r → ‖q‖ ≤ r → ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ Λ₂ * ‖p - q‖)
    {p q D : E} (hp : ‖p‖ ≤ ε) (hq : ‖q‖ ≤ ε) (hD : ε + ‖D‖ ≤ r) :
    ‖(G (p + D) - G p) - (G (q + D) - G q)‖ ≤ Λ₂ * ‖D‖ * ‖p - q‖ := by
  have hφ : ∀ s : E, HasFDerivAt (fun s => G (s + D) - G s)
      (fderiv ℝ G (s + D) - fderiv ℝ G s) s := fun s =>
    ((hasFDerivAt_comp_add_right D).mpr (hGd (s + D)).hasFDerivAt).sub (hGd s).hasFDerivAt
  have h := (convex_closedBall (0 : E) ε).norm_image_sub_le_of_norm_fderiv_le
    (f := fun s => G (s + D) - G s) (C := Λ₂ * ‖D‖)
    (fun s _ => (hφ s).differentiableAt)
    (fun s hs => by
      rw [(hφ s).fderiv]
      have hs' := mem_closedBall_zero_iff.mp hs
      have hr : ‖s + D‖ ≤ r := (norm_add_le _ _).trans (by linarith)
      have hr' : ‖s‖ ≤ r := by linarith [norm_nonneg D]
      calc _ ≤ Λ₂ * ‖s + D - s‖ := hlip _ _ hr hr'
        _ = Λ₂ * ‖D‖ := by rw [add_sub_cancel_left])
    (mem_closedBall_zero_iff.mpr hq) (mem_closedBall_zero_iff.mpr hp)
  exact h

/-- The Campanato-type hypothesis of the `C^{1,α}` estimate, from a pointwise bound
`‖F - c‖² ≤ a ‖Dw - (Dw)_ρ‖² + b ‖Dw‖²` with `a ≤ ε`, `b ≤ Kρ^{2α}`. -/
theorem Submission.codim1_hcp_sr_qs_campanato {m k : ℕ} {w : Euclid m → Euclid k}
    {F : Euclid m → (Euclid m →L[ℝ] Euclid k)} {z : Euclid m} {ρ ε K α a b : ℝ}
    {c : Euclid m →L[ℝ] Euclid k} (hρ : 0 < ρ) (hK : 0 ≤ K) (ha : a ≤ ε)
    (hb : b ≤ K * ρ ^ (2 * α))
    (hF : ContinuousOn F (closedBall z ρ)) (hw : ContinuousOn (fderiv ℝ w) (closedBall z ρ))
    (hpt : ∀ y ∈ ball z ρ, ‖F y - c‖ ^ 2 ≤
      a * ‖fderiv ℝ w y - ⨍ z' in ball z ρ, fderiv ℝ w z'‖ ^ 2 + b * ‖fderiv ℝ w y‖ ^ 2) :
    ∫ y in ball z ρ, ‖F y - c‖ ^ 2 ≤
      ε * (∫ y in ball z ρ, ‖fderiv ℝ w y - ⨍ z' in ball z ρ, fderiv ℝ w z'‖ ^ 2) +
        K * ρ ^ (2 * α) * (∫ y in ball z ρ, ‖fderiv ℝ w y‖ ^ 2) + K * ρ ^ ((m : ℝ) + 2 * α) := by
  have hint : ∀ f : Euclid m → ℝ, ContinuousOn f (closedBall z ρ) → IntegrableOn f (ball z ρ) :=
    fun f hf => (hf.integrableOn_compact (isCompact_closedBall z ρ)).mono_set ball_subset_closedBall
  have h := Submission.codim1_hcp_sr_qs_setIntegral_le (a := a) (b := b) measurableSet_ball
    (hint (fun y => ‖F y - c‖ ^ 2) ((hF.sub continuousOn_const).norm.pow 2))
    (hint (fun y => ‖fderiv ℝ w y - ⨍ z' in ball z ρ, fderiv ℝ w z'‖ ^ 2)
      ((hw.sub continuousOn_const).norm.pow 2))
    (hint (fun y => ‖fderiv ℝ w y‖ ^ 2) (hw.norm.pow 2)) hpt
  have hg0 : 0 ≤ ∫ y in ball z ρ, ‖fderiv ℝ w y - ⨍ z' in ball z ρ, fderiv ℝ w z'‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have hh0 : 0 ≤ ∫ y in ball z ρ, ‖fderiv ℝ w y‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h3 : 0 ≤ K * ρ ^ ((m : ℝ) + 2 * α) := mul_nonneg hK (Real.rpow_nonneg hρ.le _)
  nlinarith [mul_le_mul_of_nonneg_right ha hg0, mul_le_mul_of_nonneg_right hb hh0]

/-- Dominated convergence for weak-form integrals along `t → 0`, `t ≠ 0`. -/
theorem Submission.codim1_hcp_sr_qs_tendsto_integral_pair {m k : ℕ}
    {A : ℝ → Euclid m → (Euclid m →L[ℝ] Euclid k)} {A₀ : Euclid m → (Euclid m →L[ℝ] Euclid k)}
    {ζ : Euclid m → Euclid k} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) {M : ℝ}
    (hcont : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ContinuousOn (A t) (tsupport ζ))
    (hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ y ∈ tsupport ζ, ‖A t y‖ ≤ M)
    (hlim : ∀ y ∈ tsupport ζ, Tendsto (fun t => A t y) (𝓝[≠] 0) (𝓝 (A₀ y))) :
    Tendsto (fun t => ∫ y, ∑ j : Fin m, inner ℝ (A t y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (𝓝[≠] 0)
      (𝓝 (∫ y, ∑ j : Fin m, inner ℝ (A₀ y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))) := by
  obtain ⟨Mζ, hMζ⟩ := hζc.isCompact.exists_bound_of_continuousOn
    (hζ.continuous_fderiv one_ne_zero).continuousOn
  refine tendsto_integral_filter_of_dominated_convergence
    ((tsupport ζ).indicator fun _ => (m : ℝ) * (M * Mζ)) ?_ ?_ ?_ ?_
  · exact hcont.mono fun t ht =>
      (Submission.codim1_hcp_sr_qs_integrable_pair hζ hζc ht).aestronglyMeasurable
  · refine hbound.mono fun t ht => Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport ζ
    · rw [indicator_of_mem hy]
      refine (Submission.codim1_hcp_sr_qs_norm_pair_le _ _).trans ?_
      have hM : 0 ≤ M := (norm_nonneg _).trans (ht y hy)
      exact mul_le_mul_of_nonneg_left (mul_le_mul (ht y hy) (hMζ y hy) (norm_nonneg _) hM)
        (Nat.cast_nonneg m)
    · rw [indicator_of_notMem hy, Submission.codim1_hcp_sr_qs_pair_eq_zero _ ζ hy, norm_zero]
  · exact (integrable_indicator_iff (isClosed_tsupport ζ).measurableSet).mpr
      (integrableOn_const hζc.isCompact.measure_lt_top.ne)
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport ζ
    · have hc : Continuous fun L : Euclid m →L[ℝ] Euclid k => ∑ j : Fin m,
          inner ℝ (L (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
        continuous_finsetSum _ fun j _ =>
          (continuous_id.clm_apply continuous_const).inner continuous_const
      exact (hc.tendsto _).comp (hlim y hy)
    · simp only [Submission.codim1_hcp_sr_qs_pair_eq_zero _ ζ hy]
      exact tendsto_const_nhds

/-- `‖Dⁱ⁰ f y - Dⁱ⁰ f z‖ = ‖f y - f z‖` (zeroth iterated derivative). -/
theorem Submission.codim1_hcp_sr_qs_norm_iteratedFDeriv_zero_sub {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (y z : E) :
    ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 f z‖ = ‖f y - f z‖ := by
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Step 1 of the parent proof: `Du` is `α`-Hölder on `B_{R/4}(x)` whenever `B_R(x) ⊆ Ω`
(the `C^{1,α}` estimate applied to `w = u - u(x)`, `F = G ∘ Du`, `c = G((Du)_{z,ρ})`). -/
theorem Submission.codim1_hcp_sr_qs_step1 {m k : ℕ}
    {G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)} (hGd : Differentiable ℝ G)
    (hG0 : G 0 = 0) {α ε₁ Λ ε₀ : ℝ} (hΛ1 : Λ ≤ ε₁) (hΛ2 : Λ ^ 2 ≤ ε₁) (hε₀ : 0 < ε₀)
    (hb : ∀ p : Euclid m →L[ℝ] Euclid k, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ)
    (hD : ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k)
      (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) →
      ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) →
      (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) →
      (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R →
        ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤
          ε₁ * (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2) +
            K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) +
              K * ρ ^ ((m : ℝ) + 2 * α)) →
      (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball x₀ R →
        ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
          ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
      (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧
        ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4),
          ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α)
    {Ω : Set (Euclid m)} {u : Euclid m → Euclid k} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hDu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀)
    (hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
    {x : Euclid m} {R : ℝ} (hR : 0 < R) (hRΩ : ball x R ⊆ Ω) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ y ∈ ball x (R / 4), ∀ y' ∈ ball x (R / 4),
      ‖fderiv ℝ u y - fderiv ℝ u y'‖ ≤ C₁ * ‖y - y'‖ ^ α := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hD (ε₀ * R) R (by positivity) hR
  have hw : fderiv ℝ (fun y => u y - u x) = fderiv ℝ u := funext fun y => fderiv_sub_const _
  have hDuc : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hud : ∀ y ∈ Ω, DifferentiableAt ℝ u y := fun y hy =>
    (hu.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
  have hb' : ∀ y ∈ Ω, ‖fderiv ℝ u y‖ ≤ 3 * ε₀ := fun y hy => by linarith [hDu y hy]
  have key := hC₁ x (fun y => u y - u x) (fun y => G (fderiv ℝ u y))
    ((hu.mono hRΩ).sub contDiffOn_const) (hGd.continuous.comp_continuousOn (hDuc.mono hRΩ))
    (fun y hy => by
      have h := (convex_ball x R).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u)
        (C := ε₀) (fun z hz => hud z (hRΩ hz)) (fun z hz => hDu z (hRΩ hz)) (mem_ball_self hR) hy
      calc ‖u y - u x‖ ≤ ε₀ * ‖y - x‖ := h
        _ ≤ ε₀ * R := by
          gcongr
          rw [← dist_eq_norm]
          exact (mem_ball.mp hy).le)
    (fun y hy => by
      show ‖G (fderiv ℝ u y)‖ ≤ ε₁ * ‖fderiv ℝ (fun y => u y - u x) y‖ + ε₀ * R
      rw [hw]
      have h := Submission.codim1_hcp_sr_qs_norm_sub_le hGd hb (hb' y (hRΩ hy))
        (q := 0) (by rw [norm_zero]; positivity)
      rw [hG0, sub_zero, sub_zero] at h
      have h1 := norm_nonneg (fderiv ℝ u y)
      have h2 : 0 ≤ ε₀ * R := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hΛ1 h1])
    (fun z ρ hρ hzρ => by
      have hzΩ : closedBall z ρ ⊆ Ω := hzρ.trans hRΩ
      have hav : ‖⨍ z' in ball z ρ, fderiv ℝ u z'‖ ≤ ε₀ :=
        Submission.codim1_hcp_sr_qs_norm_average_le hε₀.le measure_ball_lt_top
          fun y hy => hDu y (hzΩ (ball_subset_closedBall hy))
      refine ⟨G (⨍ z' in ball z ρ, fderiv ℝ u z'), ?_⟩
      rw [hw]
      refine Submission.codim1_hcp_sr_qs_campanato (a := Λ ^ 2) (b := 0) hρ (by positivity) hΛ2
        (by positivity) (hGd.continuous.comp_continuousOn (hDuc.mono hzΩ)) (hDuc.mono hzΩ)
        fun y hy => ?_
      have h := Submission.codim1_hcp_sr_qs_norm_sub_le hGd hb
        (hb' y (hzΩ (ball_subset_closedBall hy)))
        (by linarith : ‖⨍ z' in ball z ρ, fderiv ℝ u z'‖ ≤ 3 * ε₀)
      rw [zero_mul, add_zero, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2)
    (fun ζ hζ hζc hζs => by
      rw [Submission.codim1_hcp_sr_qs_setIntegral_pair _ ζ hζs,
        Submission.codim1_hcp_sr_qs_setIntegral_pair (fun y => G (fderiv ℝ u y)) ζ hζs, hw]
      exact hweak ζ hζ hζc (hζs.trans hRΩ))
  refine ⟨C₁, hC₁0, fun y hy y' hy' => ?_⟩
  have h := key.2 y hy y' hy'
  rwa [hw] at h

/-- The pointwise estimate of step 2(c,d): with `p = Du(y)`, `p' = Du(y + tv)`, `q = Du(z)` and
`c = t⁻¹(G(q + t a) - G(q))`, `‖t⁻¹(G p' - G p) - c‖² ≤ 2Λ² ‖A - a‖² + 2Λ₂² H² ‖A‖²` where
`A = t⁻¹(p' - p)` and `‖p - q‖ ≤ H` (two mean value inequalities). -/
theorem Submission.codim1_hcp_sr_qs_dq_pointwise {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : E → E} (hGd : Differentiable ℝ G) {ε₀ Λ Λ₂ H t : ℝ} (hΛ₂ : 0 ≤ Λ₂)
    (ht : t ≠ 0) (hb : ∀ p : E, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ)
    (hlip : ∀ p q : E, ‖p‖ ≤ 3 * ε₀ → ‖q‖ ≤ 3 * ε₀ →
      ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ Λ₂ * ‖p - q‖)
    {p q p' a : E} (hp : ‖p‖ ≤ ε₀) (hq : ‖q‖ ≤ ε₀) (hp' : ‖p'‖ ≤ ε₀) (ha : ‖t • a‖ ≤ 2 * ε₀)
    (hpq : ‖p - q‖ ≤ H) :
    ‖t⁻¹ • (G p' - G p) - t⁻¹ • (G (q + t • a) - G q)‖ ^ 2 ≤
      2 * Λ ^ 2 * ‖t⁻¹ • (p' - p) - a‖ ^ 2 + 2 * Λ₂ ^ 2 * H ^ 2 * ‖t⁻¹ • (p' - p)‖ ^ 2 := by
  obtain ⟨D, rfl⟩ : ∃ D, p' = p + D := ⟨p' - p, (add_sub_cancel _ _).symm⟩
  rw [add_sub_cancel_left]
  have hDn : ‖D‖ ≤ 2 * ε₀ := by
    have h1 : ‖D‖ ≤ ‖p + D‖ + ‖p‖ := by
      calc ‖D‖ = ‖(p + D) - p‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖p + D‖ + ‖p‖ := norm_sub_le _ _
    linarith
  have htA : t • (t⁻¹ • D) = D := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hnD : ‖D‖ = |t| * ‖t⁻¹ • D‖ := by
    conv_lhs => rw [← htA]
    rw [norm_smul, Real.norm_eq_abs]
  have hnDa : ‖D - t • a‖ = |t| * ‖t⁻¹ • D - a‖ := by
    conv_lhs => rw [← htA]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have hε₀ : 0 ≤ ε₀ := (norm_nonneg p).trans hp
  have hs1 := Submission.codim1_hcp_sr_qs_second_diff hGd hlip hp hq (D := D) (by linarith)
  have hs2 := Submission.codim1_hcp_sr_qs_norm_sub_le hGd hb (p := q + D) (q := q + t • a)
    ((norm_add_le _ _).trans (by linarith)) ((norm_add_le _ _).trans (by linarith))
  rw [add_sub_add_left_eq_sub] at hs2
  have hsplit : t⁻¹ • (G (p + D) - G p) - t⁻¹ • (G (q + t • a) - G q) =
      t⁻¹ • (((G (p + D) - G p) - (G (q + D) - G q)) + (G (q + D) - G (q + t • a))) := by
    rw [← smul_sub]
    congr 1
    abel
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hX : ‖t⁻¹ • (G (p + D) - G p) - t⁻¹ • (G (q + t • a) - G q)‖ ≤
      Λ₂ * H * ‖t⁻¹ • D‖ + Λ * ‖t⁻¹ • D - a‖ := by
    rw [hsplit, norm_smul, norm_inv, Real.norm_eq_abs]
    have hsum := (norm_add_le _ _).trans (add_le_add hs1 hs2)
    rw [hnD, hnDa] at hsum
    have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hb 0 (by rw [norm_zero]; linarith))
    calc |t|⁻¹ * ‖((G (p + D) - G p) - (G (q + D) - G q)) + (G (q + D) - G (q + t • a))‖
        ≤ |t|⁻¹ * (Λ₂ * (|t| * ‖t⁻¹ • D‖) * ‖p - q‖ + Λ * (|t| * ‖t⁻¹ • D - a‖)) := by
          gcongr
      _ = Λ₂ * ‖t⁻¹ • D‖ * ‖p - q‖ + Λ * ‖t⁻¹ • D - a‖ := by
          field_simp
      _ ≤ Λ₂ * ‖t⁻¹ • D‖ * H + Λ * ‖t⁻¹ • D - a‖ := by gcongr
      _ = Λ₂ * H * ‖t⁻¹ • D‖ + Λ * ‖t⁻¹ • D - a‖ := by ring
  have hX2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
  nlinarith [sq_nonneg (Λ₂ * H * ‖t⁻¹ • D‖ - Λ * ‖t⁻¹ • D - a‖)]

/-- Step 2 of the parent proof: from the `α`-Hölder bound of `Du` on `B_{R/4}(x)` (step 1), the
difference quotients `w_t = t⁻¹(u(· + tv) - u)` satisfy uniform `C^{1,α}` bounds on `B_{R/32}(x)`
(the `C^{1,α}` estimate on `B_{R/8}(x)`), so by `codim1_hcp_sr_difference_quotient` `Du` is `C¹`
on `B_{R/64}(x)` with `α`-Hölder derivative. -/
theorem Submission.codim1_hcp_sr_qs_step2 {m k : ℕ} (hm : 1 ≤ m)
    {G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)} (hGd : Differentiable ℝ G)
    {α ε₁ Λ Λ₂ ε₀ : ℝ} (hα : 0 < α) (hΛ1 : Λ ≤ ε₁) (hΛ2 : 2 * Λ ^ 2 ≤ ε₁) (hΛ₂ : 0 ≤ Λ₂)
    (hε₀ : 0 < ε₀) (hb : ∀ p : Euclid m →L[ℝ] Euclid k, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ)
    (hlip : ∀ p q : Euclid m →L[ℝ] Euclid k, ‖p‖ ≤ 3 * ε₀ → ‖q‖ ≤ 3 * ε₀ →
      ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ Λ₂ * ‖p - q‖)
    (hD : ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k)
      (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) →
      ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) →
      (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) →
      (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R →
        ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤
          ε₁ * (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2) +
            K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) +
              K * ρ ^ ((m : ℝ) + 2 * α)) →
      (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball x₀ R →
        ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
          ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
      (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧
        ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4),
          ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α)
    {Ω : Set (Euclid m)} {u : Euclid m → Euclid k} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hDu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀)
    (hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
    {x : Euclid m} {R : ℝ} (hR : 0 < R) (hRΩ : ball x R ⊆ Ω) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ y ∈ ball x (R / 4), ∀ y' ∈ ball x (R / 4),
      ‖fderiv ℝ u y - fderiv ℝ u y'‖ ≤ C₁ * ‖y - y'‖ ^ α) :
    ContDiffOn ℝ 1 (fderiv ℝ u) (ball x (R / 64)) ∧ ∃ C₂ : ℝ, ∀ y ∈ ball x (R / 64),
      ∀ y' ∈ ball x (R / 64),
        ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) y'‖ ≤ C₂ * ‖y - y'‖ ^ α := by
  have hK0 : 0 ≤ max ε₀ (2 * Λ₂ ^ 2 * C₁ ^ 2) := le_max_of_le_left hε₀.le
  obtain ⟨C₂, -, hC₂⟩ := hD (max ε₀ (2 * Λ₂ ^ 2 * C₁ ^ 2)) (R / 8) hK0 (by positivity)
  have hDuc : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hud : ∀ y ∈ Ω, DifferentiableAt ℝ u y := fun y hy =>
    (hu.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
  have hb' : ∀ y ∈ Ω, ‖fderiv ℝ u y‖ ≤ 3 * ε₀ := fun y hy => by linarith [hDu y hy]
  -- for `|t| < R/16`, `‖v‖ = 1` and `y ∈ B_{R/8}(x)`, both `y` and `y + tv` lie in `B_R(x)`
  have hgeo : ∀ v : Euclid m, ‖v‖ = 1 → ∀ t : ℝ, |t| < R / 16 → ∀ y ∈ ball x (R / 8),
      y ∈ ball x R ∧ y + t • v ∈ ball x R := by
    intro v hv t ht y hy
    rw [mem_ball] at hy
    refine ⟨mem_ball.mpr (by linarith), mem_ball.mpr ?_⟩
    calc dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
      _ = |t| + dist y x := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
      _ < R := by linarith
  have key : ∀ v : Euclid m, ‖v‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < R / 16 →
      (∀ y ∈ ball x (R / 8 / 4), ‖t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y)‖ ≤ C₂) ∧
      ∀ y ∈ ball x (R / 8 / 4), ∀ y' ∈ ball x (R / 8 / 4),
        ‖t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y) -
          t⁻¹ • (fderiv ℝ u (y' + t • v) - fderiv ℝ u y')‖ ≤ C₂ * ‖y - y'‖ ^ α := by
    intro v hv t ht htR
    have hg := hgeo v hv t htR
    have htpos : 0 < |t| := abs_pos.mpr ht
    have hwd : ∀ y ∈ ball x (R / 8), HasFDerivAt (fun y => t⁻¹ • (u (y + t • v) - u y))
        (t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y)) y := by
      intro y hy
      have h1 : HasFDerivAt (fun y => u (y + t • v)) (fderiv ℝ u (y + t • v)) y :=
        (hasFDerivAt_comp_add_right (t • v)).mpr (hud _ (hRΩ (hg y hy).2)).hasFDerivAt
      exact (h1.sub (hud y (hRΩ (hg y hy).1)).hasFDerivAt).const_smul t⁻¹
    have hwf : ∀ y ∈ ball x (R / 8), fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) y =
        t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y) := fun y hy => (hwd y hy).fderiv
    have hAc : ContinuousOn (fun y => t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y))
        (ball x (R / 8)) :=
      ((hDuc.comp (continuous_add_const _).continuousOn fun y hy => hRΩ (hg y hy).2).sub
        (hDuc.mono fun y hy => hRΩ (hg y hy).1)).const_smul t⁻¹
    have hwc : ContinuousOn (fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)))
        (ball x (R / 8)) := hAc.congr hwf
    have hFc : ContinuousOn (fun y => t⁻¹ • (G (fderiv ℝ u (y + t • v)) - G (fderiv ℝ u y)))
        (ball x (R / 8)) :=
      ((hGd.continuous.comp_continuousOn (hDuc.comp (continuous_add_const _).continuousOn
        fun y hy => hRΩ (hg y hy).2)).sub (hGd.continuous.comp_continuousOn
          (hDuc.mono fun y hy => hRΩ (hg y hy).1))).const_smul t⁻¹
    -- `‖D w_t‖ ≤ 2ε₀/|t|`
    have hAb : ∀ y ∈ ball x (R / 8),
        ‖fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) y‖ ≤ |t|⁻¹ * (2 * ε₀) := by
      intro y hy
      rw [hwf y hy, norm_smul, norm_inv, Real.norm_eq_abs]
      gcongr
      calc _ ≤ ‖fderiv ℝ u (y + t • v)‖ + ‖fderiv ℝ u y‖ := norm_sub_le _ _
        _ ≤ ε₀ + ε₀ := add_le_add (hDu _ (hRΩ (hg y hy).2)) (hDu _ (hRΩ (hg y hy).1))
        _ = 2 * ε₀ := by ring
    obtain ⟨h1, h2⟩ := hC₂ x (fun y => t⁻¹ • (u (y + t • v) - u y))
      (fun y => t⁻¹ • (G (fderiv ℝ u (y + t • v)) - G (fderiv ℝ u y)))
      (((hu.comp (contDiff_id.add contDiff_const).contDiffOn fun y hy => hRΩ (hg y hy).2).sub
        (hu.mono fun y hy => hRΩ (hg y hy).1)).const_smul t⁻¹)
      hFc
      (fun y hy => by
        have h := (convex_ball x R).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u)
          (C := ε₀) (fun z hz => hud z (hRΩ hz)) (fun z hz => hDu z (hRΩ hz)) (hg y hy).1
          (hg y hy).2
        show ‖t⁻¹ • (u (y + t • v) - u y)‖ ≤ max ε₀ (2 * Λ₂ ^ 2 * C₁ ^ 2)
        rw [norm_smul, norm_inv, Real.norm_eq_abs]
        calc |t|⁻¹ * ‖u (y + t • v) - u y‖ ≤ |t|⁻¹ * (ε₀ * ‖y + t • v - y‖) := by gcongr
          _ = ε₀ := by
            rw [add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
            field_simp
          _ ≤ max ε₀ (2 * Λ₂ ^ 2 * C₁ ^ 2) := le_max_left _ _)
      (fun y hy => by
        show ‖t⁻¹ • (G (fderiv ℝ u (y + t • v)) - G (fderiv ℝ u y))‖ ≤
          ε₁ * ‖fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) y‖ + max ε₀ (2 * Λ₂ ^ 2 * C₁ ^ 2)
        rw [hwf y hy, norm_smul, norm_smul]
        have h := Submission.codim1_hcp_sr_qs_norm_sub_le hGd hb (hb' _ (hRΩ (hg y hy).2))
          (hb' _ (hRΩ (hg y hy).1))
        have h0 := norm_nonneg (fderiv ℝ u (y + t • v) - fderiv ℝ u y)
        have h0' := norm_nonneg t⁻¹
        have hΛ : 0 ≤ Λ := (norm_nonneg (fderiv ℝ G 0)).trans (hb 0 (by rw [norm_zero]; linarith))
        calc ‖t⁻¹‖ * ‖G (fderiv ℝ u (y + t • v)) - G (fderiv ℝ u y)‖
            ≤ ‖t⁻¹‖ * (Λ * ‖fderiv ℝ u (y + t • v) - fderiv ℝ u y‖) := by gcongr
          _ ≤ ε₁ * (‖t⁻¹‖ * ‖fderiv ℝ u (y + t • v) - fderiv ℝ u y‖) := by
            nlinarith [mul_nonneg h0' h0]
          _ ≤ _ := le_add_of_nonneg_right hK0)
      (fun z ρ hρ hzρ => by
        have hzρ' : ∀ y ∈ closedBall z ρ, y ∈ ball x (R / 8) := fun y hy => hzρ hy
        have hz8 : z ∈ ball x (R / 8) := hzρ' z (mem_closedBall_self hρ.le)
        have hav : ‖⨍ z' in ball z ρ, fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) z'‖ ≤
            |t|⁻¹ * (2 * ε₀) :=
          Submission.codim1_hcp_sr_qs_norm_average_le (by positivity) measure_ball_lt_top
            fun y hy => hAb y (hzρ' y (ball_subset_closedBall hy))
        have hta : ‖t • ⨍ z' in ball z ρ, fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) z'‖ ≤
            2 * ε₀ := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |t| * ‖⨍ z' in ball z ρ, fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) z'‖
              ≤ |t| * (|t|⁻¹ * (2 * ε₀)) := by gcongr
            _ = 2 * ε₀ := by field_simp
        refine ⟨t⁻¹ • (G (fderiv ℝ u z +
            t • ⨍ z' in ball z ρ, fderiv ℝ (fun y => t⁻¹ • (u (y + t • v) - u y)) z') -
          G (fderiv ℝ u z)), ?_⟩
        refine Submission.codim1_hcp_sr_qs_campanato (a := 2 * Λ ^ 2)
          (b := 2 * Λ₂ ^ 2 * C₁ ^ 2 * ρ ^ (2 * α)) hρ hK0 hΛ2
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
          (hFc.mono fun y hy => hzρ' y hy) (hwc.mono fun y hy => hzρ' y hy) fun y hy => ?_
        have hy8 : y ∈ ball x (R / 8) := hzρ' y (ball_subset_closedBall hy)
        have hpq : ‖fderiv ℝ u y - fderiv ℝ u z‖ ≤ C₁ * ρ ^ α := by
          have hy4 : y ∈ ball x (R / 4) := ball_subset_ball (by linarith) hy8
          have hz4 : z ∈ ball x (R / 4) := ball_subset_ball (by linarith) hz8
          calc ‖fderiv ℝ u y - fderiv ℝ u z‖ ≤ C₁ * ‖y - z‖ ^ α := hC₁ y hy4 z hz4
            _ ≤ C₁ * ρ ^ α := by
              gcongr
              rw [← dist_eq_norm]
              exact (mem_ball.mp hy).le
        have hρα : ρ ^ (2 * α) = (ρ ^ α) ^ 2 := by
          rw [mul_comm, Real.rpow_mul hρ.le, Real.rpow_two]
        have h := Submission.codim1_hcp_sr_qs_dq_pointwise hGd hΛ₂ ht hb hlip
          (hDu y (hRΩ (hg y hy8).1)) (hDu z (hRΩ (hg z hz8).1)) (hDu _ (hRΩ (hg y hy8).2)) hta hpq
        rw [hwf y hy8]
        refine h.trans_eq ?_
        rw [hρα]
        ring)
      (fun ζ hζ hζc hζs => by
        rw [Submission.codim1_hcp_sr_qs_setIntegral_pair _ ζ hζs,
          Submission.codim1_hcp_sr_qs_setIntegral_pair
            (fun y => t⁻¹ • (G (fderiv ℝ u (y + t • v)) - G (fderiv ℝ u y))) ζ hζs,
          Submission.codim1_hcp_sr_qs_integral_pair_congr
            (A' := fun y => t⁻¹ • (fderiv ℝ u (y + t • v) - fderiv ℝ u y))
            fun y hy => hwf y (hζs hy)]
        exact Submission.codim1_hcp_sr_qs_weak_shift hweak hDuc
          (hGd.continuous.comp_continuousOn hDuc) (t • v) t⁻¹ hζ hζc
          fun y hy => ⟨hRΩ (hg y (hζs hy)).1, hRΩ (hg y (hζs hy)).2⟩)
    refine ⟨fun y hy => ?_, fun y hy y' hy' => ?_⟩
    · have hy8 : y ∈ ball x (R / 8) := ball_subset_ball (by linarith) hy
      rw [← hwf y hy8]
      exact h1 y hy
    · have hy8 : y ∈ ball x (R / 8) := ball_subset_ball (by linarith) hy
      have hy8' : y' ∈ ball x (R / 8) := ball_subset_ball (by linarith) hy'
      rw [← hwf y hy8, ← hwf y' hy8']
      exact h2 y hy y' hy'
  have hsub : ball x (R / 64) ⊆ ball x (R / 8 / 4) := ball_subset_ball (by linarith)
  obtain ⟨h1, -, h3⟩ := Submission.codim1_hcp_sr_difference_quotient m k α hm hα (fderiv ℝ u) x
    (R / 64) (R / 64) C₂ (by positivity) (by positivity)
    (hDuc.mono ((ball_subset_ball (by linarith)).trans hRΩ))
    fun v hv t ht htR => ⟨fun y hy => (key v hv t ht (by linarith)).1 y (hsub hy),
      fun y hy y' hy' => (key v hv t ht (by linarith)).2 y (hsub hy) y' (hsub hy')⟩
  exact ⟨h1, C₂, h3⟩

/-- Step 3(a) of the parent proof: if `Du` is `C¹` on `Ω`, the weak equation can be differentiated
in a unit direction `e`: `Δ(D²u e) = div(DG(Du)[D²u e])` weakly (difference quotients
`t⁻¹(Du(· + te) - Du)` and dominated convergence as `t → 0`). -/
theorem Submission.codim1_hcp_sr_qs_diff_eq {m k : ℕ}
    {G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)} (hGd : Differentiable ℝ G)
    {Λ ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hb : ∀ p : Euclid m →L[ℝ] Euclid k, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ)
    {Ω : Set (Euclid m)} {u : Euclid m → Euclid k} (hΩ : IsOpen Ω)
    (hDu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω) (hDu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀)
    (hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
    {e : Euclid m} (he : ‖e‖ = 1) {ζ : Euclid m → Euclid k} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) (hζΩ : tsupport ζ ⊆ Ω) :
    ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ (fderiv ℝ u) y e (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
      ∫ y, ∑ j : Fin m, inner ℝ
        (fderiv ℝ G (fderiv ℝ u y) (fderiv ℝ (fderiv ℝ u) y e) (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hζc.isCompact.exists_cthickening_subset_open hΩ hζΩ
  have hDuc : ContinuousOn (fderiv ℝ u) Ω := hDu1.continuousOn
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ u)) Ω :=
    hDu1.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hKc : IsCompact (cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ u))
    (hD2c.mono hδΩ)
  have hDud : ∀ y ∈ Ω, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) y := fun y hy =>
    ((hDu1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)).hasFDerivAt
  have hball : ∀ y ∈ tsupport ζ, closedBall y δ ⊆ Ω := fun y hy =>
    (closedBall_subset_cthickening hy δ).trans hδΩ
  have hnear : ∀ (y : Euclid m) (t : ℝ), |t| ≤ δ → y + t • e ∈ closedBall y δ := by
    intro y t ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs]
    exact ht
  have hinc : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t| ≤ δ →
      ‖fderiv ℝ u (y + t • e) - fderiv ℝ u y‖ ≤ M₂ * |t| := by
    intro y hy t ht
    have h := (convex_closedBall y δ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ u) (C := M₂) (fun z hz => (hDud z (hball y hy hz)).differentiableAt)
      (fun z hz => hM₂ z (closedBall_subset_cthickening hy δ hz)) (mem_closedBall_self hδ.le)
      (hnear y t ht)
    rwa [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs] at h
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ |t| < δ := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := eventually_mem_nhdsWithin
    have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < δ := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      simpa [Real.dist_eq] using ht
    exact h1.and h2
  have hΛ : 0 ≤ Λ := (norm_nonneg (fderiv ℝ G 0)).trans (hb 0 (by rw [norm_zero]; linarith))
  have hline : ∀ y : Euclid m, HasDerivAt (fun t : ℝ => y + t • e) e 0 := fun y => by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
  have hT := Submission.codim1_hcp_sr_qs_tendsto_integral_pair
    (A := fun t y => t⁻¹ • (fderiv ℝ u (y + t • e) - fderiv ℝ u y))
    (A₀ := fun y => fderiv ℝ (fderiv ℝ u) y e) hζ hζc (M := M₂)
    (hev.mono fun t ht =>
      ((hDuc.comp (continuous_add_const _).continuousOn
        fun y hy => hball y hy (hnear y t ht.2.le)).sub (hDuc.mono hζΩ)).const_smul t⁻¹)
    (hev.mono fun t ht y hy => by
      have htpos : 0 < |t| := abs_pos.mpr ht.1
      show ‖t⁻¹ • (fderiv ℝ u (y + t • e) - fderiv ℝ u y)‖ ≤ M₂
      rw [norm_smul, norm_inv, Real.norm_eq_abs]
      calc |t|⁻¹ * ‖fderiv ℝ u (y + t • e) - fderiv ℝ u y‖ ≤ |t|⁻¹ * (M₂ * |t|) := by
            gcongr
            exact hinc y hy t ht.2.le
        _ = M₂ := by field_simp)
    (fun y hy => by
      have h := ((hDud y (hζΩ hy)).comp_hasDerivAt_of_eq (0 : ℝ) (hline y)
        (by simp)).tendsto_slope_zero
      simpa using h)
  have hS := Submission.codim1_hcp_sr_qs_tendsto_integral_pair
    (A := fun t y => t⁻¹ • (G (fderiv ℝ u (y + t • e)) - G (fderiv ℝ u y)))
    (A₀ := fun y => fderiv ℝ G (fderiv ℝ u y) (fderiv ℝ (fderiv ℝ u) y e)) hζ hζc
    (M := Λ * M₂)
    (hev.mono fun t ht =>
      ((hGd.continuous.comp_continuousOn (hDuc.comp (continuous_add_const _).continuousOn
        fun y hy => hball y hy (hnear y t ht.2.le))).sub
          (hGd.continuous.comp_continuousOn (hDuc.mono hζΩ))).const_smul t⁻¹)
    (hev.mono fun t ht y hy => by
      have htpos : 0 < |t| := abs_pos.mpr ht.1
      have hyΩ := hζΩ hy
      have hy' := hball y hy (hnear y t ht.2.le)
      have h := Submission.codim1_hcp_sr_qs_norm_sub_le hGd hb
        (p := fderiv ℝ u (y + t • e)) (q := fderiv ℝ u y) (by linarith [hDu _ hy'])
        (by linarith [hDu _ hyΩ])
      show ‖t⁻¹ • (G (fderiv ℝ u (y + t • e)) - G (fderiv ℝ u y))‖ ≤ Λ * M₂
      rw [norm_smul, norm_inv, Real.norm_eq_abs]
      calc |t|⁻¹ * ‖G (fderiv ℝ u (y + t • e)) - G (fderiv ℝ u y)‖
          ≤ |t|⁻¹ * (Λ * (M₂ * |t|)) := by
            gcongr
            exact h.trans (by gcongr; exact hinc y hy t ht.2.le)
        _ = Λ * M₂ := by field_simp)
    (fun y hy => by
      have h := (((hGd (fderiv ℝ u y)).hasFDerivAt.comp y (hDud y (hζΩ hy))).comp_hasDerivAt_of_eq
        (0 : ℝ) (hline y) (by simp)).tendsto_slope_zero
      simpa using h)
  refine tendsto_nhds_unique_of_eventuallyEq hT hS (hev.mono fun t ht => ?_)
  exact Submission.codim1_hcp_sr_qs_weak_shift hweak hDuc (hGd.continuous.comp_continuousOn hDuc)
    (t • e) t⁻¹ hζ hζc fun y hy => ⟨hζΩ hy, hball y hy (hnear y t ht.2.le)⟩

/-- `Du(y) = ∑ₛ λₛ(Du(y) eₛ)`, `λₛ(b)(a) = ⟨a, eₛ⟩ b`. -/
theorem Submission.codim1_hcp_sr_qs_clm_decomp {m k : ℕ} (L : Euclid m →L[ℝ] Euclid k) :
    L = ∑ s : Fin m, ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k)
      (EuclideanSpace.proj s) (L (EuclideanSpace.single s (1 : ℝ))) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [sum_apply]
  simp only [ContinuousLinearMap.smulRightL_apply_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  rfl

/-- Step 3 of the parent proof: if `Du ∈ C^{l,α}_loc(Ω)` with `l ≥ 1`, then
`Du ∈ C^{l+1,α}_loc(Ω)`: each `∂ₛu = Du(·) eₛ` solves `Δ∂ₛu = div(DG(Du)[D∂ₛu])` weakly
(step 3(a)), so `codim1_hcp_sr_linear_bootstrap` applies with `B = DG ∘ Du ∈ C^{l,α}_loc`
(`codim1_hcp_sr_holder_algebra`), and `Du = ∑ₛ λₛ(∂ₛu)`. -/
theorem Submission.codim1_hcp_sr_qs_bootstrap {m k : ℕ}
    {G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {α εL Λ ε₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hΛL : Λ ≤ εL) (hε₀ : 0 ≤ ε₀)
    (hb : ∀ p : Euclid m →L[ℝ] Euclid k, ‖p‖ ≤ 3 * ε₀ → ‖fderiv ℝ G p‖ ≤ Λ)
    (hL : ∀ (Ω : Set (Euclid m)) (l : ℕ) (w : Euclid m → Euclid k)
      (B : Euclid m → ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k)))
      (g : Euclid m → (Euclid m →L[ℝ] Euclid k)), IsOpen Ω → ContDiffOn ℝ 1 w Ω →
      (∀ x ∈ Ω, ‖B x‖ ≤ εL) →
      (ContDiffOn ℝ l B Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ,
        ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ l B y - iteratedFDeriv ℝ l B z‖ ≤ C * ‖y - z‖ ^ α) →
      (ContDiffOn ℝ l g Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ,
        ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ l g y - iteratedFDeriv ℝ l g z‖ ≤ C * ‖y - z‖ ^ α) →
      (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
        ∫ x in Ω, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
          ∫ x in Ω, ∑ j : Fin m, inner ℝ ((B x (fderiv ℝ w x) + g x)
            (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
      (ContDiffOn ℝ (l + 1) w Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ,
        ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ (l + 1) w y - iteratedFDeriv ℝ (l + 1) w z‖ ≤ C * ‖y - z‖ ^ α))
    {Ω : Set (Euclid m)} {u : Euclid m → Euclid k} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hDu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀)
    (hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
    (l : ℕ) (hl : 1 ≤ l)
    (hQ : ContDiffOn ℝ l (fderiv ℝ u) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ,
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        ‖iteratedFDeriv ℝ l (fderiv ℝ u) y - iteratedFDeriv ℝ l (fderiv ℝ u) z‖ ≤
          C * ‖y - z‖ ^ α) :
    ContDiffOn ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ u) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        ‖iteratedFDeriv ℝ (l + 1) (fderiv ℝ u) y - iteratedFDeriv ℝ (l + 1) (fderiv ℝ u) z‖ ≤
          C * ‖y - z‖ ^ α := by
  have hHA := Submission.codim1_hcp_sr_holder_algebra m α Ω hΩ hα0 hα1
  have hDu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hQ.1.of_le (by exact_mod_cast hl)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hDG : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  -- `u` is `C²` on `Ω`, so its second derivative is symmetric
  have hu2 : ContDiffOn ℝ 2 u Ω := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hΩ).2
      ⟨hu.differentiableOn one_ne_zero, fun h => absurd h (by simp), hDu1⟩
    rwa [one_add_one_eq_two] at h
  have hsymm : ∀ y ∈ Ω, ∀ a b : Euclid m,
      fderiv ℝ (fderiv ℝ u) y a b = fderiv ℝ (fderiv ℝ u) y b a := fun y hy a b =>
    (hu2.contDiffAt (hΩ.mem_nhds hy)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField]) a b
  -- `D(∂ₛu) = D²u eₛ` on `Ω`
  have hvderiv : ∀ (s : Fin m), ∀ y ∈ Ω,
      fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) y =
        fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single s (1 : ℝ)) := by
    intro s y hy
    have hd : DifferentiableAt ℝ (fderiv ℝ u) y :=
      (hDu1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
    rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add]
    refine ContinuousLinearMap.ext fun a => ?_
    rw [ContinuousLinearMap.flip_apply, hsymm y hy]
  -- coefficients `B = DG ∘ Du ∈ C^{l,α}_loc` and `g = 0`
  have hB := (hHA l).2.2.2.1 (Euclid m →L[ℝ] Euclid k)
    ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k)) (fderiv ℝ G) (fderiv ℝ u) hDG hQ
  have h0 := (hHA l).1 (Euclid m →L[ℝ] Euclid k) 0
  -- each `∂ₛu` is in `C^{l+1,α}_loc`
  have hv : ∀ s : Fin m,
      ContDiffOn ℝ ((l + 1 : ℕ) : WithTop ℕ∞)
          (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) Ω ∧
        ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ (l + 1) (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) y -
            iteratedFDeriv ℝ (l + 1)
              (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) z‖ ≤
            C * ‖y - z‖ ^ α := by
    intro s
    have hweak_s : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Ω →
        ∫ x in Ω, ∑ j : Fin m, inner ℝ
            (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x
              (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
          ∫ x in Ω, ∑ j : Fin m, inner ℝ ((fderiv ℝ G (fderiv ℝ u x)
              (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x) +
                (0 : Euclid m →L[ℝ] Euclid k)) (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) := by
      intro ζ hζ hζc hζΩ
      rw [Submission.codim1_hcp_sr_qs_setIntegral_pair
          (fun x => fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x) ζ hζΩ,
        Submission.codim1_hcp_sr_qs_setIntegral_pair
          (fun x => fderiv ℝ G (fderiv ℝ u x)
            (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x) + 0) ζ hζΩ,
        Submission.codim1_hcp_sr_qs_integral_pair_congr
          (A := fun x => fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x)
          (A' := fun y => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single s (1 : ℝ)))
          fun y hy => hvderiv s y (hζΩ hy),
        Submission.codim1_hcp_sr_qs_integral_pair_congr
          (A := fun x => fderiv ℝ G (fderiv ℝ u x)
            (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) x) + 0)
          (A' := fun y => fderiv ℝ G (fderiv ℝ u y)
            (fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single s (1 : ℝ))))
          fun y hy => by rw [hvderiv s y (hζΩ hy), add_zero]]
      exact Submission.codim1_hcp_sr_qs_diff_eq hGd hε₀ hb hΩ hDu1 hDu hweak (by simp) hζ hζc hζΩ
    have h := hL Ω l (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))
      (fun y => fderiv ℝ G (fderiv ℝ u y)) (fun _ => 0) hΩ (hDu1.clm_apply contDiffOn_const)
      (fun y hy => (hb _ (by linarith [hDu y hy])).trans hΛL) hB h0 hweak_s
    rwa [← Nat.cast_add_one] at h
  -- `Du = ∑ₛ λₛ(∂ₛu)` is in `C^{l+1,α}_loc`
  have hterm : ∀ s : Fin m,
      ContDiffOn ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun y => ContinuousLinearMap.smulRightL ℝ
        (Euclid m) (Euclid k) (EuclideanSpace.proj s)
          (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) Ω ∧
        ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ (l + 1) (fun y => ContinuousLinearMap.smulRightL ℝ
              (Euclid m) (Euclid k) (EuclideanSpace.proj s)
                (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) y -
            iteratedFDeriv ℝ (l + 1) (fun y => ContinuousLinearMap.smulRightL ℝ
              (Euclid m) (Euclid k) (EuclideanSpace.proj s)
                (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) z‖ ≤ C * ‖y - z‖ ^ α :=
    fun s => (hHA (l + 1)).2.2.2.1 (Euclid k) (Euclid m →L[ℝ] Euclid k)
      (ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s))
      (fun y => fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))
      (ContinuousLinearMap.contDiff _) (hv s)
  have hsum : ∀ S : Finset (Fin m),
      ContDiffOn ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun y => ∑ s ∈ S,
        ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
          (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) Ω ∧
        ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ (l + 1) (fun y => ∑ s ∈ S,
              ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
                (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) y -
            iteratedFDeriv ℝ (l + 1) (fun y => ∑ s ∈ S,
              ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
                (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) z‖ ≤ C * ‖y - z‖ ^ α := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have heq : (fun y : Euclid m => ∑ s ∈ (∅ : Finset (Fin m)),
          ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
            (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ)))) =
          fun _ => (0 : Euclid m →L[ℝ] Euclid k) := funext fun y => Finset.sum_empty
      rw [heq]
      exact (hHA (l + 1)).1 _ 0
    | insert s S hs ih =>
      have heq : (fun y : Euclid m => ∑ t ∈ insert s S,
          ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj t)
            (fderiv ℝ u y (EuclideanSpace.single t (1 : ℝ)))) =
          fun y => ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
              (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) + ∑ t ∈ S,
            ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj t)
              (fderiv ℝ u y (EuclideanSpace.single t (1 : ℝ))) :=
        funext fun y => Finset.sum_insert hs
      rw [heq]
      exact (hHA (l + 1)).2.1 _ _ _ (hterm s) ih
  have hdecomp : fderiv ℝ u = fun y => ∑ s : Fin m,
      ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k) (EuclideanSpace.proj s)
        (fderiv ℝ u y (EuclideanSpace.single s (1 : ℝ))) :=
    funext fun y => Submission.codim1_hcp_sr_qs_clm_decomp (fderiv ℝ u y)
  rw [hdecomp]
  exact hsum Finset.univ

/-- The argument of `codim1_hcp_sr_quasilinear_smooth` (Simon Ch. 5, end of the proof of
Theorem 7.1: Schauder theory for `Δu = div G(Du)`), with the interior `C^{1,α}` estimate supplied
as the hypothesis `hc1`, stated as in the natural-language statement of the `c1alpha_estimate`
node: `∫‖F - c‖² ≤ ε₁ ∫‖Dw - (Dw)_ρ‖² + Kρ^{2α} ∫‖Dw‖² + Kρ^{m+2α}`.  The other three
prerequisites are used directly.  Steps: choice of `ε₀` (`codim1_hcp_sr_qs_constants`); `C^{1,α}`
(`codim1_hcp_sr_qs_step1`); `C^{2,α}` by difference quotients (`codim1_hcp_sr_qs_step2`);
bootstrap (`codim1_hcp_sr_qs_bootstrap`). -/
theorem Submission.codim1_hcp_sr_qs_of_c1alpha
    (hc1 : ∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K R : ℝ, 0 ≤ K →
      0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k)
        (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) →
        ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) →
        (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) →
        (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R →
          ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤
            ε₁ * (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2) +
              K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) +
                K * ρ ^ ((m : ℝ) + 2 * α)) →
        (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ ball x₀ R →
          ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
            ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
        (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧
          ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4),
            ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α) :
    ∀ (m k : ℕ) (G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)), 1 ≤ m → ContDiff ℝ (⊤ : ℕ∞) G → G 0 = 0 → fderiv ℝ G 0 = 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (Ω : Set (Euclid m)) (u : Euclid m → Euclid k), IsOpen Ω → ContDiffOn ℝ 1 u Ω → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω → ∫ x in Ω, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in Ω, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → ∀ r : ℕ, ContDiffOn ℝ r u Ω := by
  intro m k G hm hG hG0 hDG0
  have hα0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨εD, hεD, hD⟩ := hc1 m k (1 / 2) hm hα0 hα1
  obtain ⟨εL, hεL, hL⟩ := Submission.codim1_hcp_sr_linear_bootstrap m k (1 / 2) hm hα0 hα1
  -- Step 0: constants
  have hΛ0 : 0 < min εL (min 1 (εD / 2)) := lt_min hεL (lt_min one_pos (half_pos hεD))
  have hΛL : min εL (min 1 (εD / 2)) ≤ εL := min_le_left _ _
  have hΛ1 : min εL (min 1 (εD / 2)) ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hΛD2 : min εL (min 1 (εD / 2)) ≤ εD / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hΛD : min εL (min 1 (εD / 2)) ≤ εD := by linarith
  have hΛsq : 2 * min εL (min 1 (εD / 2)) ^ 2 ≤ εD := by nlinarith
  have hΛsq' : min εL (min 1 (εD / 2)) ^ 2 ≤ εD := by nlinarith
  obtain ⟨ε₀, hε₀, Λ₂, hΛ₂, hb, hlip⟩ := Submission.codim1_hcp_sr_qs_constants hG hDG0 hΛ0
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  refine ⟨ε₀, hε₀, fun Ω u hΩ hu hDu hweakΩ => ?_⟩
  -- the weak equation, written over `ℝᵐ`
  have hweak : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := fun ζ hζ hζc hζΩ => by
    have h := hweakΩ ζ hζ hζc hζΩ
    rwa [Submission.codim1_hcp_sr_qs_setIntegral_pair (fderiv ℝ u) ζ hζΩ,
      Submission.codim1_hcp_sr_qs_setIntegral_pair (fun y => G (fderiv ℝ u y)) ζ hζΩ] at h
  -- Steps 1 and 2: `Du` is locally `C^{1,1/2}`
  have hloc : ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧
      ContDiffOn ℝ 1 (fderiv ℝ u) (ball x ρ) ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤ C * ‖y - z‖ ^ (1 / 2 : ℝ) := by
    intro x hx
    obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
    obtain ⟨C₁, hC₁0, hC₁⟩ := Submission.codim1_hcp_sr_qs_step1 hGd hG0 hΛD hΛsq' hε₀ hb hD
      hΩ hu hDu hweak hR hRΩ
    obtain ⟨h1, C₂, h2⟩ := Submission.codim1_hcp_sr_qs_step2 hm hGd hα0 hΛD hΛsq hΛ₂ hε₀ hb
      hlip hD hΩ hu hDu hweak hR hRΩ hC₁0 hC₁
    exact ⟨R / 64, by positivity, (ball_subset_ball (by linarith)).trans hRΩ, h1, C₂, h2⟩
  have hDu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := contDiffOn_of_locally_contDiffOn fun x hx => by
    obtain ⟨ρ, hρ, -, h1, -⟩ := hloc x hx
    exact ⟨ball x ρ, isOpen_ball, mem_ball_self hρ, h1.mono inter_subset_right⟩
  have hHA := Submission.codim1_hcp_sr_holder_algebra m (1 / 2) Ω hΩ hα0 (by norm_num)
  -- `Du ∈ C^{1,1/2}_loc(Ω)`
  have hH0c : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun x => fderiv ℝ (fderiv ℝ u) x) Ω := by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hDu1.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hH0h : ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ,
      ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ 0 (fun x => fderiv ℝ (fderiv ℝ u) x) y -
        iteratedFDeriv ℝ 0 (fun x => fderiv ℝ (fderiv ℝ u) x) z‖ ≤ C * ‖y - z‖ ^ (1 / 2 : ℝ) := by
    intro x hx
    obtain ⟨ρ, hρ, hρΩ, -, C, hC⟩ := hloc x hx
    refine ⟨ρ, hρ, hρΩ, C, fun y hy z hz => ?_⟩
    rw [Submission.codim1_hcp_sr_qs_norm_iteratedFDeriv_zero_sub]
    exact hC y hy z hz
  have hQ1 := ((hHA 0).2.2.2.2.2 (Euclid m →L[ℝ] Euclid k) (fderiv ℝ u) hDu1).mpr ⟨hH0c, hH0h⟩
  have e01 : ((0 : ℕ) : WithTop ℕ∞) + 1 = ((1 : ℕ) : WithTop ℕ∞) := by norm_num
  rw [e01] at hQ1
  -- Step 3: bootstrap
  have hQ : ∀ l : ℕ, 1 ≤ l → ContDiffOn ℝ (l : WithTop ℕ∞) (fderiv ℝ u) Ω ∧ ∀ x ∈ Ω,
      ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        ‖iteratedFDeriv ℝ l (fderiv ℝ u) y - iteratedFDeriv ℝ l (fderiv ℝ u) z‖ ≤
          C * ‖y - z‖ ^ (1 / 2 : ℝ) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => exact hQ1
    | succ l hl ih =>
      exact Submission.codim1_hcp_sr_qs_bootstrap hG hα0 (by norm_num) hΛL hε₀.le hb hL hΩ hu
        hDu hweak l hl ih
  -- Step 4: conclusion
  intro r
  have h := (hQ (r + 1) (by omega)).1
  have h2 : ContDiffOn ℝ (((r + 1 : ℕ) : WithTop ℕ∞) + 1) u Ω :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).2
      ⟨hu.differentiableOn one_ne_zero, fun h => absurd h (WithTop.natCast_ne_top _), h⟩
  refine h2.of_le ?_
  norm_cast
  omega

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
