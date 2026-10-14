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

/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
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
/-- **Coordinate expansion of a `k`-covector** (the pointwise identity behind
`H^#ω(u)(e) = Σ_I ω_I(H(u)) det D(H^I)(u)`): for `f ∈ Λᵏ(ℝ^{N'})` and `u ∈ (ℝ^{N'})ᵏ`,
`k! f(u) = Σ_I f(e'_{I 0}, …, e'_{I (k-1)}) det (u_b (I c))_{c,b}`, the sum over all maps
`I : Fin k → Fin N'`.  Expand each `u_b = Σ_i u_b(i) e'_i` and use multilinearity; for each
permutation `σ` reindex `J = I ∘ σ` and use `f (v ∘ σ) = sign σ • f v`; average over the `k!`
permutations and recognize the Leibniz formula for the determinant. -/
theorem Submission.dor_lmb_fcd_jwc_covector_det_expansion : ∀ (N' k : ℕ) (f : Covector (Euclid N') k) (u : Fin k → Euclid N'), (k.factorial : ℝ) * f u = ∑ I : Fin k → Fin N', f (fun c => EuclideanSpace.single (I c) (1 : ℝ)) * Matrix.det (Matrix.of fun c b => u b (I c)) := by
  intro N' k f u
  set e : Fin N' → Euclid N' := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- step 1: multilinear expansion in the standard basis
  have h1 : f u = ∑ J : Fin k → Fin N', (∏ b, u b (J b)) * f (fun b => e (J b)) := by
    have hu : u = fun b => ∑ i, u b i • e i := by
      funext b
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N') ℝ).sum_repr (u b)]
      simp [he]
    conv_lhs => rw [hu]
    rw [show f (fun b => ∑ i, u b i • e i) = f.toMultilinearMap (fun b => ∑ i, u b i • e i) from rfl,
      MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp [smul_eq_mul]
  -- step 2: reindex by a permutation `σ`, using alternation
  have h2 : ∀ σ : Equiv.Perm (Fin k), f u = ∑ I : Fin k → Fin N',
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) := by
    intro σ
    rw [h1]
    rw [← Equiv.sum_comp ((σ.symm).arrowCongr (Equiv.refl (Fin N')))]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hperm : f (fun b => e (I (σ b))) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * f (fun c => e (I c)) := by
      have := f.toAlternatingMap.map_perm (fun c => e (I c)) σ
      simp only [Function.comp_def] at this
      rw [show f (fun b => e (I (σ b))) = f.toAlternatingMap (fun b => e (I (σ b))) from rfl, this,
        Units.smul_def, zsmul_eq_mul]
      rfl
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm, Function.comp_apply]
    rw [hperm]
    ring
  -- step 3: average over `σ` and recognize the Leibniz formula
  have h3 : (k.factorial : ℝ) * f u = ∑ σ : Equiv.Perm (Fin k), f u := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [h3]
  calc ∑ σ : Equiv.Perm (Fin k), f u
      = ∑ σ : Equiv.Perm (Fin k), ∑ I : Fin k → Fin N',
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_congr rfl fun σ _ => h2 σ
    _ = ∑ I : Fin k → Fin N', ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_comm
    _ = _ := ?_
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp only [Matrix.of_apply, he]
  ring
/-- **Jacobian minors of Lipschitz maps are measurable and bounded** (the integrands in the weak
continuity of Jacobian minors): if `g₀, …, g_{r-1}` are `L`-Lipschitz on `ℝᵏ` and
`V₀, …, V_{r-1} ∈ ℝᵏ`, then `D(x) = det (Dg_c(x) V_b)_{c,b}` is measurable and
`|D(x)| ≤ r! (L ∑_b ‖V_b‖)ʳ` for every `x`, where `Dg(x) = fderiv ℝ g x` (`0` where `g` is not
differentiable).  Each entry `x ↦ Dg_c(x) V_b` is measurable (`measurable_fderiv_apply_const`)
and bounded by `‖Dg_c(x)‖ ‖V_b‖ ≤ L ‖V_b‖ ≤ L ∑_b ‖V_b‖` (`norm_fderiv_le_of_lipschitz`); by the
Leibniz formula `D` is a signed sum of `r!` products of `r` entries, which gives both claims.
(`Matrix.det_le` is outside the import closure, so the bound is done by hand.) -/
theorem Submission.dor_lmb_fcd_jwc_minor_measurable_bound : ∀ (k r : ℕ) (L : NNReal) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k), (∀ c, LipschitzWith L (g c)) → Measurable (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) ∧ ∀ x, |Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))| ≤ (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
  intro k r L g V hg
  -- Leibniz formula: `D(x) = ∑_σ sign σ ∏_b Dg_{σ b}(x) V_b`
  have hdet : ∀ x, Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
    fun x => Matrix.det_apply' _
  refine ⟨?_, fun x => ?_⟩
  · -- steps 1–2: the entries are measurable, hence so is the signed sum of their products
    have hm : Measurable fun x => ∑ σ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
      Finset.measurable_sum _ fun σ _ => measurable_const.mul
        (Finset.measurable_prod _ fun b _ => measurable_fderiv_apply_const ℝ (g (σ b)) (V b))
    simpa only [hdet] using hm
  · -- step 3: every entry is bounded by `s = L ∑_b ‖V_b‖`
    have hent : ∀ c b, |fderiv ℝ (g c) x (V b)| ≤ (L : ℝ) * ∑ b, ‖V b‖ := by
      intro c b
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (g c) x (V b)‖ ≤ ‖fderiv ℝ (g c) x‖ * ‖V b‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖V b‖ :=
            mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hg c)) (norm_nonneg _)
        _ ≤ L * ∑ b, ‖V b‖ := by
            gcongr
            exact Finset.single_le_sum (f := fun b => ‖V b‖) (fun b _ => norm_nonneg _)
              (Finset.mem_univ b)
    -- step 4: the triangle inequality and `|sign σ| = 1` give `|D(x)| ≤ ∑_σ sʳ = r! sʳ`
    rw [hdet]
    calc |∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)|
        ≤ ∑ σ : Equiv.Perm (Fin r),
            |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm (Fin r), ∏ b, |fderiv ℝ (g (σ b)) x (V b)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [abs_mul, Finset.abs_prod]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), ∏ _b : Fin r, (L : ℝ) * ∑ b, ‖V b‖ := by
          gcongr with σ _ b _
          exact hent (σ b) b
      _ = (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
          rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- **Derivative of the mollification of a Lipschitz function**: for an `L`-Lipschitz `f` and a
`C¹` kernel `ρ` with compact support, `D(ρ ⋆ f)(x) v = ∫ ρ(t) Df(x − t) v dt`.  Differentiating
under the integral (`HasCompactSupport.hasFDerivAt_convolution_left`) gives
`D(ρ ⋆ f)(x) v = ∫ Dρ(t) v · f(x − t) dt`.  With `t = x − s` and the reflected kernel
`h(s) = ρ(x − s)` (`C¹` with compact support, hence Lipschitz, and `∂_{−v} h(s) = Dρ(x − s) v`)
the two sides become `∫ ∂_{−v} h · f` and `∫ h · Df(·) v`; they agree by integration by parts for
Lipschitz functions (`LipschitzWith.integral_lineDeriv_mul_eq`: `∫ ∂_v f · h = ∫ ∂_{−v} h · f`)
and Rademacher (`∂_v f = Df · v` a.e.). -/
theorem Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq : ∀ (k : ℕ) (L : NNReal) (f ρ : Euclid k → ℝ), LipschitzWith L f → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x v : Euclid k, fderiv ℝ (fun y => ∫ t, ρ t * f (y - t)) x v = ∫ t, ρ t * fderiv ℝ f (x - t) v := by
  intro k L f ρ hf hρ hρs x v
  have hconv : (fun y => ∫ t, ρ t * f (y - t)) =
      convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; simp [convolution_def]
  have hD := hρs.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    hf.continuous.locallyIntegrable x
  have hint := (hρs.fderiv (𝕜 := ℝ)).convolutionExists_left (μ := (volume : Measure (Euclid k)))
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euclid k)) (hρ.continuous_fderiv (by norm_num))
    (hf.continuous.locallyIntegrable (μ := (volume : Measure (Euclid k)))) x
  rw [hconv, hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- change of variables `t ↦ x - t` on both sides
  rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t v * f (x - t)) (μ := volume) x,
    ← integral_sub_left_eq_self (fun t => ρ t * fderiv ℝ f (x - t) v) (μ := volume) x]
  simp only [sub_sub_cancel]
  -- integration by parts against `h(s) = ρ(x - s)`
  set h : Euclid k → ℝ := fun s => ρ (x - s) with hh
  have hhC1 : ContDiff ℝ 1 h := hρ.comp (contDiff_const.sub contDiff_id)
  have hhs : HasCompactSupport h := hρs.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hhL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhs hhC1 (by norm_num)
  have hibp := hf.integral_lineDeriv_mul_eq (μ := volume) hhL hhs v
  have hlh : ∀ s, lineDeriv ℝ h s (-v) = fderiv ℝ ρ (x - s) v := by
    intro s
    rw [(hhC1.differentiable (by norm_num) s).lineDeriv_eq_fderiv]
    have h1 : HasFDerivAt h (-(fderiv ℝ ρ (x - s))) s := by
      have := (hρ.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s
        ((hasFDerivAt_const x s).sub (hasFDerivAt_id s))
      simpa [hh, Function.comp_def] using this
    rw [h1.fderiv]
    simp
  -- Rademacher: `∂_v f = Df · v` almost everywhere
  have hlf : ∀ᵐ s ∂(volume : Measure (Euclid k)), lineDeriv ℝ f s v = fderiv ℝ f s v := by
    filter_upwards [hf.ae_differentiableAt] with s hs
    exact hs.lineDeriv_eq_fderiv
  simp only [hlh] at hibp
  rw [← hibp]
  refine integral_congr_ae ?_
  filter_upwards [hlf] with s hs
  rw [hs, hh]
  ring
/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dor_lmb_fcd_jwc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  intro k L f hf
  -- step 1: bumps `φ n` with `rIn = 1/(n+2)`, `rOut = 2/(n+2)`, normalized to `ρ n = φ n / ∫ φ n`
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Euclid k) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by have := hpos n; positivity,
      div_lt_div_of_pos_right (by norm_num) (hpos n)⟩
  have hrOut : ∀ n, (φ n).rOut = 2 * (φ n).rIn := fun n => by
    show 2 / ((n : ℝ) + 2) = 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  -- `|B(x, r)| = r ^ d * c` with `c = |B(0, 1)| > 0`
  set d := Module.finrank ℝ (Euclid k)
  set c := (volume : Measure (Euclid k)).real (closedBall 0 1)
  have hcpos : 0 < c := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne
  have hvol : ∀ (x : Euclid k) (r : ℝ), 0 ≤ r →
      (volume : Measure (Euclid k)).real (closedBall x r) = r ^ d * c :=
    fun x r hr => Measure.addHaar_real_closedBall' _ x hr
  -- `φ n = 1` on `B(0, rIn)` and `φ n ≥ 0`, so `∫ φ n ≥ |B(0, rIn)| = rIn ^ d * c > 0`
  have hφint : ∀ n, Integrable (φ n) (volume : Measure (Euclid k)) := fun n =>
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hIge : ∀ n, (φ n).rIn ^ d * c ≤ ∫ x, φ n x := by
    intro n
    rw [← hvol 0 _ (φ n).rIn_pos.le]
    calc (volume : Measure (Euclid k)).real (closedBall 0 (φ n).rIn)
        = ∫ x in closedBall (0 : Euclid k) (φ n).rIn, φ n x := by
          rw [setIntegral_congr_fun measurableSet_closedBall
            (fun x hx => (φ n).one_of_mem_closedBall hx), setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x, φ n x :=
          setIntegral_le_integral (hφint n) (Eventually.of_forall fun x => (φ n).nonneg)
  have hIpos : ∀ n, 0 < ∫ x, φ n x := fun n =>
    (mul_pos (pow_pos (φ n).rIn_pos d) hcpos).trans_le (hIge n)
  set ρ : ℕ → Euclid k → ℝ := fun n x => φ n x / ∫ y, φ n y with hρ
  have hρc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous.div_const _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    (φ n).hasCompactSupport.comp_left (g := fun t : ℝ => t / ∫ y, φ n y) (zero_div _)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => div_nonneg (φ n).nonneg (hIpos n).le
  have hρint : ∀ n, ∫ x, ρ n x = 1 := fun n => by
    show ∫ x, φ n x / ∫ y, φ n y = 1
    rw [integral_div, div_self (hIpos n).ne']
  have hρsupp : ∀ n, support (ρ n) ⊆ ball 0 (φ n).rOut := fun n x hx => by
    rw [← (φ n).support_eq, mem_support]
    intro h0
    exact (mem_support.1 hx) (by simp [hρ, h0])
  have hρle : ∀ n x, ρ n x ≤ 1 / ((φ n).rIn ^ d * c) := fun n x =>
    calc ρ n x = φ n x / ∫ y, φ n y := rfl
      _ ≤ 1 / ∫ y, φ n y := div_le_div_of_nonneg_right (φ n).le_one (hIpos n).le
      _ ≤ 1 / ((φ n).rIn ^ d * c) :=
          one_div_le_one_div_of_le (mul_pos (pow_pos (φ n).rIn_pos d) hcpos) (hIge n)
  -- `f_n = ρ n ⋆ f`
  set fs : ℕ → Euclid k → ℝ := fun n x => ∫ t, ρ n t * f (x - t) with hfs
  have hconv : ∀ n, fs n = convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro n; funext x; simp [hfs, convolution_def]
  have hrOut0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [φ] using this
  refine ⟨fs, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · -- step 2: `ρ n ⋆ f` is smooth
    rw [hconv]
    exact (hρs n).contDiff_convolution_left _ (hρc n) hf.continuous.locallyIntegrable
  · -- step 3: `ρ n ⋆ f` is `L`-Lipschitz
    exact Submission.cmcs_ls_mollify_lipschitz k (ρ n) f L (hρcont n) (hρs n) (hρ0 n) (hρint n) hf
  · -- step 4: `|f_n x - f x| ≤ L * rOut` for all `x`, and `rOut → 0`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hrOut0.const_mul (L : ℝ)).eventually (gt_mem_nhds (by simpa using hε))]
      with n hn x
    have hdist := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := f x) (g := f)
      (by positivity : (0 : ℝ) ≤ L * (φ n).rOut) (hρsupp n) (hρ0 n) (hρint n)
      hf.continuous.aestronglyMeasurable (fun y hy => by
        calc dist (f y) (f x) ≤ L * dist y x := hf.dist_le_mul y x
          _ ≤ L * (φ n).rOut := by gcongr; exact (mem_ball.1 hy).le)
    rw [← hconv] at hdist
    rw [dist_comm]
    exact lt_of_le_of_lt hdist hn
  · -- step 5: `Df_n(x) v = ∫ ρ n t * Df(x - t) v dt`
    have hB1 : ∀ n x v, fderiv ℝ (fs n) x v = ∫ t, ρ n t * fderiv ℝ f (x - t) v := fun n x v =>
      Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
    have hδ : Tendsto (fun n => (φ n).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hrOut0, Eventually.of_forall fun n => (φ n).rOut_pos⟩
    -- steps 6-7: for each basis vector `e_i`, `Df_n(x) e_i → Df(x) e_i` for a.e. `x`
    have hDi : ∀ i : Fin k, ∀ᵐ x ∂(volume : Measure (Euclid k)),
        Tendsto (fun n => fderiv ℝ (fs n) x (EuclideanSpace.single i (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
      intro i
      set g : Euclid k → ℝ := fun s => fderiv ℝ f s (EuclideanSpace.single i (1 : ℝ)) with hg
      have hloc : LocallyIntegrable g (volume : Measure (Euclid k)) := by
        refine (locallyIntegrable_const ((L : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)).mono
          ((measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs (_ * _), abs_of_nonneg (by positivity)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      -- Lebesgue differentiation: `⨍_{B(x, r)} |g - g x| → 0` as `r → 0`, for a.e. `x`
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1]
        with x hx
      have havg := hx (fun _ => x) (fun n => (φ n).rOut) hδ
        (Eventually.of_forall fun n => mem_closedBall_self (by simpa using (φ n).rOut_pos.le))
      -- `0 ≤ ρ n (x - ·) ≤ 2 ^ d / |B(x, rOut)|`, supported in `B(x, rOut)`, with integral `1`
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub ((2 : ℝ) ^ d) havg
        (g := fun n y => ρ n (x - y))
        (Eventually.of_forall fun n => hloc.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun n => by
          rw [integral_sub_left_eq_self (ρ n) volume x, hρint n])
        (Eventually.of_forall fun n y hy => by
          have hy' : x - y ∈ ball (0 : Euclid k) (φ n).rOut := hρsupp n hy
          rw [mem_ball, dist_zero_right] at hy'
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hy'.le)
        (Eventually.of_forall fun n y => by
          rw [abs_of_nonneg (hρ0 n _), hvol x _ (φ n).rOut_pos.le, hrOut n]
          calc ρ n (x - y) ≤ 1 / ((φ n).rIn ^ d * c) := hρle n _
            _ = 2 ^ d / ((2 * (φ n).rIn) ^ d * c) := by
              rw [mul_pow]
              field_simp)
      refine key.congr fun n => ?_
      rw [hB1, ← integral_sub_left_eq_self (fun y => ρ n (x - y) • g y) volume x]
      simp only [sub_sub_cancel, smul_eq_mul, hg]
    filter_upwards [ae_all_iff.2 hDi] with x hx
    -- step 8: `‖T‖ ≤ ∑ᵢ |T eᵢ|`, so convergence on the basis gives convergence in norm
    have hbound : ∀ T : Euclid k →L[ℝ] ℝ, ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun i _ => norm_nonneg _)
        fun w => ?_
      have hw : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w]
        simp
      calc ‖T w‖ = ‖∑ i, w i • T (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hw]
            simp [map_sum, map_smul]
        _ ≤ ∑ i, ‖w i • T (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by simp
        _ ≤ ∑ i, ‖w‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
            gcongr with i
            exact PiLp.norm_apply_le w i
        _ = (∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖) * ‖w‖ := by
            rw [Finset.sum_mul]; simp [mul_comm]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbound _) ?_
    have : Tendsto (fun n => ∑ i : Fin k, ‖(fderiv ℝ (fs n) x - fderiv ℝ f x)
        (EuclideanSpace.single i (1 : ℝ))‖) atTop (𝓝 (∑ i : Fin k, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hx i)
      simpa using this
    simpa using this
/-- **The Piola identity** (the Jacobian minors are null Lagrangians): for `C²` functions
`g₀, …, g_{r-1}` on `ℝᵏ` and directions `V₀, …, V_r`, the minors
`M_b(y) = det (Dg_c(y) V_{s_b(b')})_{c,b'}` (`s_b = Fin.succAbove b`, so `V_b` is deleted) satisfy
`∑_b (-1)^b DM_b(x) V_b = 0`.  With `G = (g₀, …, g_{r-1})` and the constant determinant form
`θ = dy⁰ ∧ ⋯ ∧ dy^{r-1}` one has `M_b(y) = (G^*θ)(y)(V ∘ s_b)`, so the left side is
`d(G^*θ)(x)(V)`, and `d(G^*θ) = G^*(dθ) = 0` by the naturality of `d` (which is where the symmetry
of `D²G` enters). -/
theorem Submission.dor_lmb_fcd_jwc_piola_identity : ∀ (k r : ℕ) (g : Fin r → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (x : Euclid k), (∀ c, ContDiff ℝ 2 (g c)) → ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c) y (V (b.succAbove b')))) x (V b) = 0 := by
  intro k r g V x hg
  -- Step 1: the map `G = (g₀, …, g_{r-1}) : ℝᵏ → ℝʳ` is `C²`, and `(DG(y) w)_c = Dg_c(y) w`
  set e : (Fin r → ℝ) ≃L[ℝ] Euclid r := (EuclideanSpace.equiv (Fin r) ℝ).symm with he
  set G : Euclid k → Euclid r := fun y => e (fun c => g c y) with hG
  have hGc : ContDiff ℝ 2 G := e.contDiff.comp (contDiff_pi.2 hg)
  have hGd : ∀ y w (c : Fin r), fderiv ℝ G y w c = fderiv ℝ (g c) y w := by
    intro y w c
    have hpi : HasFDerivAt (fun y => fun c => g c y)
        (ContinuousLinearMap.pi fun c => fderiv ℝ (g c) y) y :=
      hasFDerivAt_pi.2 fun c => ((hg c).differentiable (by norm_num) y).hasFDerivAt
    have h := e.hasFDerivAt.comp y hpi
    rw [show G = e ∘ (fun y => fun c => g c y) from rfl, h.fderiv]
    simp [he]
  -- Step 2: the constant determinant form `Θ ≡ θ`, `θ(w) = det (w_b(c))_{c,b}`
  obtain ⟨θ, hθ⟩ := Submission.cmr_cc_det_covector_exists r r id
  set Θ : Euclid r → Covector (Euclid r) r := fun _ => θ with hΘ
  -- Step 3: `dΘ = 0`, since `DΘ = 0` and the alternatization is linear
  have hdΘ : extDeriv Θ (G x) = 0 := by
    simp [extDeriv, hΘ, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  -- Step 4: naturality of `d` gives `d(G^*Θ)(x) = (dΘ)(G x) ∘ DG(x) = 0`
  have hpull := extDeriv_pullback (ω := Θ) (f := G) (x := x) (r := 2) (differentiableAt_const θ)
    hGc.contDiffAt (by simp)
  rw [hdΘ] at hpull
  -- Step 5: the coordinate formula `d(G^*Θ)(x)(V) = ∑_b (-1)^b D[(G^*Θ)(·)(V ∘ s_b)](x) V_b`
  have hβd : DifferentiableAt ℝ (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)) x :=
    (differentiableAt_const θ).continuousAlternatingMapCompContinuousLinearMap
      ((hGc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  have happ := extDeriv_apply hβd V
  rw [hpull] at happ
  -- Step 6: `(G^*Θ)(y)(V ∘ s_b) = M_b(y)` by Steps 1 and 2
  have hβ : ∀ i : Fin (r + 1), (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)
      (i.removeNth V)) = fun y => Matrix.det (Matrix.of fun (c b' : Fin r) =>
        fderiv ℝ (g c) y (V (i.succAbove b'))) := by
    intro i
    funext y
    simp only [hΘ, ContinuousAlternatingMap.compContinuousLinearMap_apply, hθ]
    congr 1
    ext c b'
    simp [Matrix.of_apply, Fin.removeNth, hGd]
  -- Step 7: hence `0 = d(G^*Θ)(x)(V) = ∑_b (-1)^b DM_b(x) V_b`
  simp only [hβ] at happ
  rw [eq_comm] at happ
  simpa [zsmul_eq_mul] using happ

/-- **Integration by parts for Jacobian minors** (formula (∗) of the weak continuity of Jacobian
minors, for `C²` maps): for `C²` functions `g₀, …, g_r` on `ℝᵏ`, directions `V₀, …, V_r` and a
compactly supported `C¹` function `ψ`, with `A = (Dg_c V_b)_{c,b}` and `M_b` the minor of `A`
without row `0` and column `b`, `∫ ψ det A = −Σ_b (−1)^b ∫ (Dψ V_b) g₀ M_b`.  Laplace expansion
along row `0`, the product rule for `F_b = ψ g₀ M_b` and the Piola identity
`Σ_b (−1)^b ∂_{V_b} M_b = 0` give `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
pointwise, and `∫ ∂_W F = 0` for every compactly supported `C¹` function `F` (integration by
parts of the Lipschitz functions `1` and `F`). -/
theorem Submission.dor_lmb_fcd_jwc_smooth_minor_ibp : ∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r g V ψ hg hψ hψs
  -- Step 2: the entries `Dg_c(·)W` are `C¹` (`g_c` is `C²`), hence so is every determinant of
  -- such entries (Leibniz formula), in particular every minor `M_b`
  have hdetC1 : ∀ {m : ℕ} (A : Euclid k → Fin m → Fin m → ℝ),
      (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      ContDiff ℝ 1 (fun x => Matrix.det (Matrix.of (A x))) := by
    intro m A hA
    have hLeib : (fun x => Matrix.det (Matrix.of (A x))) =
        fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A x (σ i) i := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [hLeib]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA _ _)
  have hentry : ∀ c (W : Euclid k), ContDiff ℝ 1 (fun x => fderiv ℝ (g c) x W) := fun c W =>
    ((hg c).fderiv_right (by norm_num)).clm_apply contDiff_const
  set M : Fin (r + 1) → Euclid k → ℝ := fun b x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
    fderiv ℝ (g c.succ) x (V (b.succAbove b')))
  have hMC1 : ∀ b, ContDiff ℝ 1 (M b) := fun b =>
    hdetC1 (fun x c b' => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) fun c b' => hentry _ _
  -- `F_b = ψ g₀ M_b` is `C¹` with compact support
  have hFC1 : ∀ b, ContDiff ℝ 1 (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψ.mul ((hg 0).of_le (by norm_num))).mul (hMC1 b)
  have hFs : ∀ b, HasCompactSupport (fun y => ψ y * g 0 y * M b y) := fun b =>
    hψs.mul_right.mul_right
  -- Step 3: product rule for `∂_{V_b} F_b`
  have hdiff : ∀ b x, fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) =
      fderiv ℝ ψ x (V b) * g 0 x * M b x + ψ x * fderiv ℝ (g 0) x (V b) * M b x +
        ψ x * g 0 x * fderiv ℝ (M b) x (V b) := by
    intro b x
    have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
    have hgd : DifferentiableAt ℝ (g 0) x := (hg 0).differentiable (by norm_num) x
    have hMd : DifferentiableAt ℝ (M b) x := (hMC1 b).differentiable (by norm_num) x
    have h : HasFDerivAt (fun y => ψ y * g 0 y * M b y) _ x :=
      (hψd.hasFDerivAt.mul hgd.hasFDerivAt).mul hMd.hasFDerivAt
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  -- Steps 1, 4, 5: Laplace expansion along row `0` and the Piola identity give, pointwise,
  -- `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
  have hpt : ∀ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) := by
    intro x
    have hp : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) = 0 :=
      Submission.dor_lmb_fcd_jwc_piola_identity k r (fun c => g c.succ) V x fun c => hg c.succ
    simp_rw [hdiff]
    have halg : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x +
          ψ x * fderiv ℝ (g 0) x (V b) * M b x + ψ x * g 0 x * fderiv ℝ (M b) x (V b)) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) =
        ψ x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (g 0) x (V b) * M b x +
          ψ x * g 0 x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [halg, hp, mul_zero, add_zero, Matrix.det_succ_row_zero]
    rfl
  -- Step 6: `∫ ∂_W F = 0` for `C¹` compactly supported `F` (integration by parts of the
  -- Lipschitz functions `1` and `F`)
  have hIBP0 : ∀ F : Euclid k → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ∀ W,
      ∫ x, fderiv ℝ F x W = 0 := by
    intro F hF hFs W
    obtain ⟨C, hFL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hF (by norm_num)
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid k)))
      (LipschitzWith.const (1 : ℝ)) hFL hFs (-W)
    have h0 : ∀ x : Euclid k, lineDeriv ℝ (fun _ : Euclid k => (1 : ℝ)) x (-W) = 0 := by
      intro x
      rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
      simp
    have h1 : ∀ x, lineDeriv ℝ F x W = fderiv ℝ F x W := fun x =>
      (hF.differentiable (by norm_num) x).lineDeriv_eq_fderiv
    simp only [h0, zero_mul, integral_zero, neg_neg, mul_one, h1] at h
    exact h.symm
  -- Step 7: every term is continuous with compact support, hence integrable; integrate
  have hi1 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b)) := fun b =>
    ((((hFC1 b).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hFs b).fderiv_apply ℝ (V b))).const_mul _
  have hi2 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      (fderiv ℝ ψ x (V b) * g 0 x * M b x)) := fun b =>
    (((((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hg 0).continuous).mul (hMC1 b).continuous).integrable_of_hasCompactSupport
      ((hψs.fderiv_apply ℝ (V b)).mul_right.mul_right)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun b _ => hi1 b)
      (integrable_finsetSum _ fun b _ => hi2 b),
    integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b]
  have hz : ∑ b : Fin (r + 1), ∫ x, (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [integral_const_mul, hIBP0 _ (hFC1 b) (hFs b) _, mul_zero]
  rw [hz, zero_sub]
  simp only [integral_const_mul]
  rfl

/-- **Integration by parts for Jacobian minors of Lipschitz maps** (the step "`(∗)` holds for
Lipschitz `v`" in the weak continuity of Jacobian minors): for `L`-Lipschitz `g₀, …, g_r` on `ℝᵏ`,
vectors `V₀, …, V_r` and `ψ ∈ C¹_c(ℝᵏ)`,
`∫ ψ det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, where `A = (Dg_c V_b)_{c,b}` and `M_b` is the minor
`det (Dg_{c+1} V_{s_b(b')})_{c,b'}`, `s_b = b.succAbove`.  Mollify every `g_c`: `C^∞`, `L`-Lipschitz
`g^n_c → g_c` uniformly with `Dg^n_c → Dg_c` a.e.  The identity holds for every `n` (smooth case);
the determinants converge a.e. and are bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, resp.
`r! (L Σ_b' ‖V_{s_b(b')}‖)^r`, so both sides converge by dominated convergence (on the right with
`|g^n_0| ≤ |g_0| + 1` for large `n`), and the limits agree. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp : ∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r L g V ψ hg hψ hψs
  -- step 1: smooth `L`-Lipschitz approximants `fs c n` of every component `g c`
  choose fs hfs_smooth hfs_lip hfs_unif hfs_ae using
    fun c => Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx k L (g c) (hg c)
  -- step 2: the identity for the smooth maps `fs · n`
  have hid := fun n => Submission.dor_lmb_fcd_jwc_smooth_minor_ibp k r (fun c => fs c n) V ψ
    (fun c => (hfs_smooth c n).of_le (by simp)) hψ hψs
  -- step 3: off a null set all derivatives converge, hence so do the entries and determinants
  have hae : ∀ᵐ x ∂(volume : Measure (Euclid k)), ∀ c,
      Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x)) := ae_all_iff.2 hfs_ae
  have hdet_lim : ∀ {m : ℕ} (σ : Fin m → Fin (r + 1)) (W : Fin m → Euclid k) (x : Euclid k),
      (∀ c, Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x))) →
      Tendsto (fun n => Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b)))) := by
    intro m σ W x hx
    have hM : Tendsto (fun n => (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b))) := by
      refine tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun b => ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (W b)).continuous.tendsto _).comp (hx (σ c))
    exact ((continuous_id.matrix_det).tendsto _).comp hM
  -- step 4: the bound `B` of the full determinants and the integrability of `ψ`
  set B : ℝ := ((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1)
  have hψc : Continuous ψ := hψ.continuous
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  -- step 5: the left side converges, dominated by `B |ψ|`
  have hL : Tendsto
      (fun n => ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (fs c n) x (V b)))
      atTop (𝓝 (∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => B * ‖ψ x‖) (fun n => ?_)
      (hψi.norm.const_mul B) (fun n => Eventually.of_forall fun x => ?_) ?_
    · exact hψc.aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
          (fun c => hfs_lip c n)).1.aestronglyMeasurable
    · have h := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
        (fun c => hfs_lip c n)).2 x
      rw [norm_mul, Real.norm_eq_abs (Matrix.det _), mul_comm]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · filter_upwards [hae] with x hx
      exact tendsto_const_nhds.mul (hdet_lim id V x hx)
  -- step 6: each term of the right side converges, dominated by `Br |∂_{V_b}ψ| (|g 0| + 1)`
  have hR : ∀ b : Fin (r + 1), Tendsto (fun n => ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x *
      Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) := by
    intro b
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) := hψs.fderiv_apply (𝕜 := ℝ) (V b)
    have hwi : Integrable (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1))) := by
      refine Integrable.const_mul ?_ _
      exact Continuous.integrable_of_hasCompactSupport
        (hdψc.norm.mul ((hg 0).continuous.norm.add continuous_const)) hdψs.norm.mul_right
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)))
      (Eventually.of_forall fun n => ?_) ?_ hwi ?_
    · exact (hdψc.mul (hfs_smooth 0 n).continuous).aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
          (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).1.aestronglyMeasurable
    · -- `|fs 0 n| ≤ |g 0| + 1` once `fs 0 n` is uniformly `1`-close to `g 0`
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hfs_unif 0) 1 one_pos).exists_forall_of_atTop
      refine eventually_atTop.2 ⟨N, fun n hn => Eventually.of_forall fun x => ?_⟩
      have h1 : ‖fs 0 n x‖ ≤ ‖g 0 x‖ + 1 := by
        have := hN n hn x
        rw [dist_comm, dist_eq_norm] at this
        have := norm_le_insert' (fs 0 n x) (g 0 x)
        linarith
      have h2 := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
        (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).2 x
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Matrix.det _)]
      calc ‖fderiv ℝ ψ x (V b)‖ * ‖fs 0 n x‖ * |Matrix.det _|
          ≤ ‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1) * Br := by gcongr
        _ = Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)) := by ring
    · filter_upwards [hae] with x hx
      refine (tendsto_const_nhds.mul ((hfs_unif 0).tendsto_at x)).mul ?_
      exact hdet_lim Fin.succ (fun b' => V (b.succAbove b')) x hx
  have hRall : Tendsto (fun n => -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) *
      ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (-∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) :=
    Tendsto.neg (tendsto_finsetSum _ fun b _ => (hR b).const_mul _)
  -- step 7: both sides of step 2 agree for every `n`, so their limits agree
  exact tendsto_nhds_unique hL (hRall.congr fun n => (hid n).symm)
/-- **Weak-* convergence against `L¹` test functions** (density step of the weak continuity of
Jacobian minors): if `|F_j|, |F| ≤ C` and `∫ ψ F_j → ∫ ψ F` for every `C^∞` compactly supported
`ψ`, then `∫ φ F_j → ∫ φ F` for every integrable `φ`.  `C_c^∞` is dense in `L¹`: by
`MemLp.induction_dense` it suffices to approximate `c 1_s` with `μ(s) < ∞`; regularity gives
`K ⊆ s ⊆ U`, `K` compact, `U` open, `μ(U \ K)` small, and `c χ` works for a smooth Urysohn
function `χ` (`χ = 1` exactly on `K`, `support χ = U ∩ B_R(0)`).  (Mathlib's
`MemLp.exist_eLpNorm_sub_le` is outside the import closure.)  For `ε > 0` take such `ψ` with
`∫ |φ − ψ| ≤ η = ε/(4C + 1)`; then `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for large
`j`. -/
theorem Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade : ∀ (k : ℕ) (C : ℝ) (Fs : ℕ → Euclid k → ℝ) (F : Euclid k → ℝ), (∀ j, AEStronglyMeasurable (Fs j) (volume : Measure (Euclid k))) → AEStronglyMeasurable F (volume : Measure (Euclid k)) → (∀ j x, |Fs j x| ≤ C) → (∀ x, |F x| ≤ C) → (∀ ψ : Euclid k → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → Tendsto (fun j => ∫ x, ψ x * Fs j x) atTop (𝓝 (∫ x, ψ x * F x))) → ∀ φ : Euclid k → ℝ, Integrable φ → Tendsto (fun j => ∫ x, φ x * Fs j x) atTop (𝓝 (∫ x, φ x * F x)) := by
  intro k C Fs F hFs hF hFsb hFb hconv φ hφ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  -- step 1: `C_c^∞` is dense in `L¹`; by `MemLp.induction_dense` only `c 1_s` needs approximating
  have hdense : ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ ψ : Euclid k → ℝ,
      eLpNorm (φ - ψ) 1 (volume : Measure (Euclid k)) ≤ ε ∧
        (ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ) := by
    intro ε hε
    refine MemLp.induction_dense ENNReal.one_ne_top
      (fun g => ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) ?_ ?_
      (memLp_one_iff_integrable.2 hφ) hε
    · intro c s hs hμs ε' hε'
      -- `K ⊆ s ⊆ U` with `μ(U \ s), μ(s \ K) < δ/2`, `δ = ε'/‖c‖`
      set δ : ℝ≥0∞ := ε' / ‖c‖ₑ with hδ
      have hδ0 : δ ≠ 0 := by
        rw [hδ, Ne, ENNReal.div_eq_zero_iff, not_or]
        exact ⟨hε', enorm_ne_top⟩
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ0).ne'
      obtain ⟨K, hKs, hKc, hK⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hδ2
      obtain ⟨U, hsU, hUo, -, hU⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hδ2
      -- smooth Urysohn function `χ`: `χ = 1` on `K`, `support χ = U ∩ B_R(0)`, `0 ≤ χ ≤ 1`
      obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : Euclid k)
      obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
        (hUo.inter isOpen_ball) hKc.isClosed (subset_inter (hKs.trans hsU) hR)
      have hχc : HasCompactSupport χ := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid k) R) (fun x hx => ?_)
        rw [← notMem_support, hχs]
        exact fun h => hx (ball_subset_closedBall h.2)
      refine ⟨fun x => c * χ x, ?_, contDiff_const.mul hχd, hχc.mul_left⟩
      -- `|c χ − c 1_s| ≤ |c| 1_{U \ K}`, so `‖c χ − c 1_s‖₁ ≤ ‖c‖ μ(U \ K) ≤ ‖c‖ δ ≤ ε'`
      have hle : ∀ x, ‖((fun x => c * χ x) - s.indicator fun _ => c) x‖ ≤
          ‖(U \ K).indicator (fun _ => c) x‖ := by
        intro x
        obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        by_cases hxK : x ∈ K
        · rw [(hχ1 x).1 hxK, indicator_of_mem (hKs hxK)]
          simp
        by_cases hxU : x ∈ U
        · rw [indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
          by_cases hxs : x ∈ s
          · rw [indicator_of_mem hxs, show c * χ x - c = c * (χ x - 1) by ring, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
          · rw [indicator_of_notMem hxs, sub_zero, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
        · have hχ0 : χ x = 0 := by
            rw [← notMem_support, hχs]
            exact fun h => hxU h.1
          rw [hχ0, indicator_of_notMem (fun h => hxU (hsU h))]
          simp
      calc eLpNorm ((fun x => c * χ x) - s.indicator fun _ => c) 1 volume
          ≤ eLpNorm ((U \ K).indicator fun _ => c) 1 volume :=
            eLpNorm_mono (((contDiff_const.mul hχd).continuous.aestronglyMeasurable).sub
              (aestronglyMeasurable_const.indicator hs)) hle
        _ = ‖c‖ₑ * volume (U \ K) := by
          rw [eLpNorm_indicator_const (hUo.measurableSet.diff hKc.isClosed.measurableSet).nullMeasurableSet
            one_ne_zero ENNReal.one_ne_top]
          simp
        _ ≤ ‖c‖ₑ * δ := by
          gcongr
          calc volume (U \ K) ≤ volume ((U \ s) ∪ (s \ K)) := by
                refine measure_mono fun x hx => ?_
                by_cases hxs : x ∈ s
                · exact Or.inr ⟨hxs, hx.2⟩
                · exact Or.inl ⟨hx.1, hxs⟩
            _ ≤ volume (U \ s) + volume (s \ K) := measure_union_le _ _
            _ ≤ δ / 2 + δ / 2 := add_le_add hU.le hK.le
            _ = δ := ENNReal.add_halves δ
        _ ≤ ε' := ENNReal.mul_div_le
    · rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
      exact ⟨hf1.add hg1, hf2.add hg2⟩
  -- step 2: `|∫ θ G| ≤ C ∫ |θ|` for integrable `θ` and `|G| ≤ C`
  have hint : ∀ θ : Euclid k → ℝ, Integrable θ → ∀ G : Euclid k → ℝ,
      AEStronglyMeasurable G (volume : Measure (Euclid k)) → (∀ x, |G x| ≤ C) →
      Integrable (fun x => θ x * G x) ∧ |∫ x, θ x * G x| ≤ C * ∫ x, ‖θ x‖ := by
    intro θ hθ G hG hGb
    refine ⟨hθ.mul_bdd hG (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x), ?_⟩
    calc |∫ x, θ x * G x| = ‖∫ x, θ x * G x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C * ‖θ x‖ := by
          refine norm_integral_le_of_norm_le (hθ.norm.const_mul C) (Eventually.of_forall fun x => ?_)
          rw [norm_mul, Real.norm_eq_abs (G x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
      _ = C * ∫ x, ‖θ x‖ := integral_const_mul _ _
  -- step 3: `ψ ∈ C_c^∞` with `∫ |φ − ψ| ≤ η = ε/(4C + 1)`, and `N` from the convergence on `ψ`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * C + 1) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ, hψε, hψs, hψc⟩ := hdense (ENNReal.ofReal_pos.2 hηpos).ne'
  have hψi : Integrable ψ := hψs.continuous.integrable_of_hasCompactSupport hψc
  have hdiff : ∫ x, ‖(φ - ψ) x‖ ≤ η := by
    have h1 := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Euclid k)))
      (hφ.sub hψi).aestronglyMeasurable
    rw [h1, ← eLpNorm_one_eq_lintegral_enorm]
    · exact ENNReal.toReal_le_of_le_ofReal hηpos.le hψε
    · exact (hφ.sub hψi).aestronglyMeasurable
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv ψ hψs hψc) (ε / 2) (by positivity)
  -- step 4: three-term estimate `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for `j ≥ N`
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hint (φ - ψ) (hφ.sub hψi) (Fs j) (hFs j) (hFsb j)
  have h2 := hint (φ - ψ) (hφ.sub hψi) F hF hFb
  have h3 := hint ψ hψi (Fs j) (hFs j) (hFsb j)
  have h4 := hint ψ hψi F hF hFb
  have e1 : ∫ x, φ x * Fs j x = (∫ x, (φ - ψ) x * Fs j x) + ∫ x, ψ x * Fs j x := by
    rw [← integral_add h1.1 h3.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have e2 : ∫ x, φ x * F x = (∫ x, (φ - ψ) x * F x) + ∫ x, ψ x * F x := by
    rw [← integral_add h2.1 h4.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have hNj := hN j hj
  rw [Real.dist_eq] at hNj ⊢
  rw [e1, e2]
  have hCη : C * η < ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hA := h1.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have hB := h2.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have key : ∀ a1 b1 a2 b2 : ℝ, |(a1 + b1) - (a2 + b2)| ≤ |a1| + |a2| + |b1 - b2| := by
    intro a1 b1 a2 b2
    calc |(a1 + b1) - (a2 + b2)| = |(a1 - a2) + (b1 - b2)| := by ring_nf
      _ ≤ |a1 - a2| + |b1 - b2| := abs_add_le _ _
      _ ≤ |a1| + |a2| + |b1 - b2| := by
          have := abs_sub a1 a2
          linarith
  have := key (∫ x, (φ - ψ) x * Fs j x) (∫ x, ψ x * Fs j x) (∫ x, (φ - ψ) x * F x) (∫ x, ψ x * F x)
  linarith

/-- **Weak continuity of Jacobian minors** (null Lagrangians; Reshetnyak 1967, Ball 1977): if the
`L`-Lipschitz `gʲ_c` converge uniformly to the `L`-Lipschitz `g_c` on `ℝᵏ` (`c < r`), then
`∫ φ det(Dgʲ_c V_b) → ∫ φ det(Dg_c V_b)` for every `φ ∈ L¹`.  Induction on `r`; for `r = 0` both
determinants are `1`.  For `r + 1` the minors are measurable and bounded by
`(r+1)! (L Σ_b ‖V_b‖)^{r+1}`, so by the weak-* to `L¹` upgrade it suffices to take `φ = ψ ∈ C^∞_c`.
Integration by parts in the first row writes `∫ ψ det(Dg_c V_b)` as
`−Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, `M_b` the minor of the rows `c ≥ 1` and the columns `≠ b`.
Split `gʲ₀ = (gʲ₀ − g₀) + g₀`: the first part is at most
`r! (L Σ_{b'} ‖V_{b'}‖)^r sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`, and the second converges by the
induction hypothesis with the continuous compactly supported weight `∂_{V_b}ψ · g₀`. -/
theorem Submission.dor_lmb_fcd_jwc_minor_weak_continuity : ∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
  intro k r
  induction r with
  | zero =>
    -- the empty determinant is `1`
    intro L gs g V φ hφ hgs hg hU
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro L gs g V φ hφ hgs hg hU
    -- Step 2: the minors are bounded, so it suffices to test against `ψ ∈ C^∞_c`
    have hb := fun (G : Fin (r + 1) → Euclid k → ℝ) (hG : ∀ c, LipschitzWith L (G c)) =>
      Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L G V hG
    refine Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade k
      (((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1))
      (fun j x => Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b)))
      (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))
      (fun j => (hb (gs j) (hgs j)).1.aestronglyMeasurable) (hb g hg).1.aestronglyMeasurable
      (fun j => (hb (gs j) (hgs j)).2) (hb g hg).2 ?_ φ hφ
    intro ψ hψ hψs
    -- Step 3: integrate by parts in the first row
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hIBPj := fun j =>
      Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L (gs j) V ψ (hgs j) hψ1 hψs
    have hIBP := Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L g V ψ hg hψ1 hψs
    simp only [hIBPj, hIBP]
    refine Tendsto.neg (tendsto_finsetSum _ fun b _ => Tendsto.const_mul _ ?_)
    -- the minors `Mʲ_b`, `M_b` and their bound
    set Mj : ℕ → Euclid k → ℝ := fun j x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (gs j c.succ) x (V (b.succAbove b'))) with hMj
    set M : Euclid k → ℝ := fun x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (g c.succ) x (V (b.succAbove b'))) with hM
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r with hBr
    have hbr := fun j => Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L
      (fun c => gs j c.succ) (fun b' => V (b.succAbove b')) (fun c => hgs j c.succ)
    -- Step 4: the weight `θ_b = ∂_{V_b}ψ · g₀` is continuous with compact support
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Euclid k →L[ℝ] ℝ => T (V b)) (by simp)
    have hdψi : Integrable (fun x => fderiv ℝ ψ x (V b)) :=
      hdψc.integrable_of_hasCompactSupport hdψs
    have hθi : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x) :=
      (hdψc.mul (hg 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
    -- Step 6: the induction hypothesis with the weight `θ_b`
    have hih := ih L (fun j c => gs j c.succ) (fun c => g c.succ) (fun b' => V (b.succAbove b'))
      (fun x => fderiv ℝ ψ x (V b) * g 0 x) hθi (fun j c => hgs j c.succ) (fun c => hg c.succ)
      (fun c => hU c.succ)
    -- Step 5: `|∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b| ≤ Br sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`
    have herr : Tendsto (fun j => ∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set K : ℝ := Br * (∫ x, ‖fderiv ℝ ψ x (V b)‖) + 1 with hK
      have hBr0 : 0 ≤ Br := by positivity
      have hK0 : 0 < K := by
        have : 0 ≤ ∫ x, ‖fderiv ℝ ψ x (V b)‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      have hδ : 0 < ε / (2 * K) := by positivity
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hU 0) (ε / (2 * K)) hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have hbd : ∀ x, ‖fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ ≤
          (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ := by
        intro x
        have h1 : |gs j 0 x - g 0 x| ≤ ε / (2 * K) := by
          have := hN j hj x
          rw [dist_comm, Real.dist_eq] at this
          exact this.le
        have h2 : |Mj j x| ≤ Br := (hbr j).2 x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |fderiv ℝ ψ x (V b)| * |gs j 0 x - g 0 x| * |Mj j x|
            ≤ |fderiv ℝ ψ x (V b)| * (ε / (2 * K)) * Br := by gcongr
          _ = (ε / (2 * K) * Br) * |fderiv ℝ ψ x (V b)| := by ring
      calc |∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x|
          = ‖∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ :=
            norm_integral_le_of_norm_le (hdψi.norm.const_mul _) (Eventually.of_forall hbd)
        _ = (ε / (2 * K)) * (Br * ∫ x, ‖fderiv ℝ ψ x (V b)‖) := by
            rw [integral_const_mul]; ring
        _ ≤ (ε / (2 * K)) * K := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    -- Step 7: `∫ ∂_{V_b}ψ gʲ₀ Mʲ_b = ∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b + ∫ θ_b Mʲ_b → 0 + ∫ θ_b M_b`
    have hsum := herr.add hih
    rw [zero_add] at hsum
    refine hsum.congr' (Eventually.of_forall fun j => ?_)
    have i2 : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x * Mj j x) := by
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact h1.congr (Eventually.of_forall fun x => by simp only; ring)
    have i1 : Integrable (fun x => fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) := by
      have hgj : Integrable (fun x => fderiv ℝ ψ x (V b) * gs j 0 x) :=
        (hdψc.mul (hgs j 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * gs j 0 x)) :=
        Integrable.bdd_mul (c := Br) hgj (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      have h2 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact (h1.sub h2).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    simp only
    rw [← integral_add i1 i2]
    congr 1
    funext x
    ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
