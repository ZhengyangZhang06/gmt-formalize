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
/-- **Pull-back by the coordinates of an orthonormal frame preserves `|·|_E`** (orthogonal
invariance of the Euclidean coefficient norm of Simon 6.1.2, 6.1.5): if `v₁, …, vₙ` are orthonormal
in `ℝᴾ` and `pL x = (⟨v₁, x⟩, …, ⟨vₙ, x⟩)`, then `|γ ∘ pL|_E = |γ|_E` for every `l`-covector `γ`
on `ℝⁿ`.  Extend `v` to an orthonormal basis `f` of `ℝᴾ` with `f ∘ ι = v`, `ι = Fin.castLE`; then
`pL (f (ι i)) = eᵢ` and `pL f_m = 0` for `m ∉ range ι`.  So `(γ ∘ pL)(f ∘ j)` vanishes unless
`j = ι ∘ j'`, where it is `γ(e ∘ j')`, and `Σ_j (γ ∘ pL)(f ∘ j)² = Σ_{j'} γ(e ∘ j')²`; by
`regcomp_covector_sq_sum_orthonormalBasis` these are `l! |γ ∘ pL|_E²` and `l! |γ|_E²`. -/
theorem Submission.cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq : ∀ (P n : ℕ) (v : Fin n → Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → ∀ (l : ℕ) (γ : Covector (Euclid n) l), covectorEuclideanNorm (γ.compContinuousLinearMap pL) = covectorEuclideanNorm γ := by
  intro P n v pL hv hpL l γ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = v k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hv.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let w : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then v ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hws : Orthonormal ℝ (s.domRestrict w) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hwe : s.domRestrict w = v ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [w, e, hi]
    rw [hwe]
    exact hv.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hws
  have hfι : ∀ k, f (ι k) = v k := by
    intro k
    rw [hf (ι k) k.2]
    simp [w, ι]
  -- Step 2: `pL (f (ι i)) = eᵢ`, and `pL (f m) = 0` for `m ∉ range ι`
  have hpLι : ∀ i, pL (f (ι i)) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    intro i
    ext k
    rw [hpL, hfι, (orthonormal_iff_ite.mp hv) k i, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
  have hpL0 : ∀ m ∉ Set.range ι, pL (f m) = 0 := by
    intro m hm
    ext k
    rw [hpL, ← hfι, (orthonormal_iff_ite.mp f.orthonormal) (ι k) m,
      ite_eq_right fun h => hm ⟨k, h⟩, PiLp.zero_apply]
  -- Step 3: `Σ_{j'} γ(e ∘ j')² = Σ_j (γ ∘ pL)(f ∘ j)²` through the injection `j' ↦ ι ∘ j'`
  let Φ : (Fin l → Fin n) → (Fin l → Fin P) := fun j' => ι ∘ j'
  have hΦ : Injective Φ := fun a b h => funext fun k => hι (congrFun h k)
  have hsum : ∑ j' : Fin l → Fin n, (γ (fun k => EuclideanSpace.basisFun (Fin n) ℝ (j' k))) ^ 2 =
      ∑ j : Fin l → Fin P, (γ.compContinuousLinearMap pL (fun k => f (j k))) ^ 2 := by
    refine Fintype.sum_of_injective Φ hΦ _ _ ?_ ?_
    · -- a tuple `j ∉ range Φ` has a slot `k` with `j k ∉ range ι`, where `pL (f (j k)) = 0`
      intro j hj
      obtain ⟨k, hk⟩ : ∃ k, j k ∉ Set.range ι := by
        by_contra! hcon
        choose j' hj' using hcon
        exact hj ⟨j', funext hj'⟩
      have h0 : γ.compContinuousLinearMap pL (fun k => f (j k)) = 0 :=
        γ.map_coord_zero (m := pL ∘ fun k => f (j k)) k (hpL0 (j k) hk)
      rw [h0, sq, mul_zero]
    · intro j'
      have he : (pL ∘ fun k => f (Φ j' k)) = fun k => EuclideanSpace.basisFun (Fin n) ℝ (j' k) :=
        funext fun k => hpLι (j' k)
      show _ = (γ (pL ∘ fun k => f (Φ j' k))) ^ 2
      rw [he]
  -- Step 4: both sums are `l!`-multiples of the squared norms; cancel `l! ≠ 0`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis n l γ (EuclideanSpace.basisFun (Fin n) ℝ),
    Submission.regcomp_covector_sq_sum_orthonormalBasis P l _ f] at hsum
  have hsq : covectorEuclideanNorm (γ.compContinuousLinearMap pL) ^ 2 =
      covectorEuclideanNorm γ ^ 2 :=
    (mul_left_cancel₀ (Nat.cast_ne_zero.mpr l.factorial_ne_zero) hsum).symm
  exact (sq_eq_sq₀ (covectorEuclideanNorm_nonneg _) (covectorEuclideanNorm_nonneg _)).mp hsq

/-- **Covector bounds for an orthonormal frame and its coordinate map** (consequences (O1), (O3) of
the orthogonal invariance (O) of the coefficient norm in White's projection argument; Simon Ch. 6,
1.15 and Remark 2.6(a)): let `v₁, …, vₙ` be orthonormal in `ℝᴾ` and
`pL x = (⟨v₁, x⟩, …, ⟨vₙ, x⟩)`.  (a) `|β(v)| ≤ |β|_E` for every `n`-covector `β` on `ℝᴾ`
(`regcomp_covector_eval_orthonormal_le` with `τ = v`).  (b) For every `l`-covector `γ` on `ℝⁿ`,
`|γ ∘ pL|_E = |γ|_E` (`cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq`), in particular
`|γ ∘ pL|_E ≤ |γ|_E`. -/
theorem Submission.cbr_ci_pw_orthonormal_covector_bounds : ∀ (P n : ℕ) (v : Fin n → Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → (∀ β : Covector (Euclid P) n, |β v| ≤ covectorEuclideanNorm β) ∧ ∀ (l : ℕ) (γ : Covector (Euclid n) l), covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ := by
  intro P n v pL hv hpL
  -- (a) is evaluation on the orthonormal frame `v`; (b) weakens the equality `|γ ∘ pL|_E = |γ|_E`
  exact ⟨fun β => Submission.regcomp_covector_eval_orthonormal_le P n β v hv,
    fun l γ => (Submission.cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq P n v pL hv hpL l γ).le⟩
/-- `Hⁿ` on an affine `n`-plane is carried to Lebesgue measure by orthonormal coordinates: if `v` is
orthonormal and `pL x = (⟨v₁, x⟩, …, ⟨vₙ, x⟩)`, then `pL_#(Hⁿ⌞(w + span v)) = Lⁿ` on `ℝⁿ`.  The
plane is the range of the isometry `ι z = w + Σᵢ (zᵢ − ⟨vᵢ, w⟩) vᵢ`, and `pL ∘ ι = id`, so
`pL_#(Hⁿ⌞(w + span v)) = pL_# ι_# Hⁿ = Hⁿ = Lⁿ` (`Isometry.map_euclideanHausdorffMeasure`,
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). -/
theorem Submission.cbr_ci_pw_plane_map_volume : ∀ (P n : ℕ) (v : Fin n → Euclid P) (w : Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → Measure.map pL ((μHE[n]).restrict {y : Euclid P | y - w ∈ Submodule.span ℝ (Set.range v)}) = (volume : Measure (Euclid n)) := by
  intro P n v w pL hv hpL
  obtain ⟨ι, hι⟩ : ∃ ι : Euclid n → Euclid P,
      ∀ z, ι z = w + ∑ i, (z i - inner ℝ (v i) w) • v i := ⟨_, fun _ => rfl⟩
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun z z' => ?_
    have hsub : ι z - ι z' = ∑ i, (z i - z' i) • v i := by
      simp only [hι, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← sub_smul,
        sub_sub_sub_cancel_right]
    rw [dist_eq_norm, dist_eq_norm, hsub]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [← real_inner_self_eq_norm_sq, hv.inner_sum, EuclideanSpace.real_norm_sq_eq]
    simp [sq]
  have hcomp : ⇑pL ∘ ι = id := by
    funext z
    refine PiLp.ext fun k => ?_
    rw [comp_apply, hpL, hι, inner_add_right, hv.inner_right_fintype, id]
    ring
  have hrange : range ι = {y : Euclid P | y - w ∈ Submodule.span ℝ (Set.range v)} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      rw [mem_ofPred_eq, hι, add_sub_cancel_left]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy
      have hcoef : ∀ i, pL y i - inner ℝ (v i) w = c i := by
        intro i
        rw [hpL, ← inner_sub_right, ← hc, hv.inner_right_fintype]
      refine ⟨pL y, ?_⟩
      simp only [hι, hcoef, hc, add_sub_cancel]
  rw [← hrange, ← hiso.map_euclideanHausdorffMeasure,
    Measure.map_map pL.measurable hiso.continuous.measurable, hcomp, Measure.map_id,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
/-- One of finitely many parallel `n`-planes `Πᵢ = {y | y − wᵢ ∈ span v}` (`v` orthonormal, the
`wᵢ ⊥ span v` pairwise distinct) is isolated in `ν = Σᵢ αᵢ Hⁿ⌞Πᵢ` by the `1`-Lipschitz
`g(x) = ‖Q(x − w_{i₀})‖`, `Q y = y − Σⱼ ⟨vⱼ, y⟩ vⱼ`: `g = ‖wⱼ − w_{i₀}‖` on `Πⱼ`, so `g = 0` on
`Π_{i₀}` and `g ≥ 3δ` on the other planes.  Since `x − w_{i₀} = Σⱼ (pL x)ⱼ vⱼ + Q(x − w_{i₀})`,
the closed sets `{g ≤ t} ∩ pL⁻¹(B̄_r)` are bounded, hence compact. -/
theorem Submission.cbr_ci_pw_isolate_plane : ∀ (P n N : ℕ) (v : Fin n → Euclid P) (w : Fin N → Euclid P) (α : Fin N → ℝ) (ν : Measure (Euclid P)) (pL : Euclid P →L[ℝ] Euclid n) (i₀ : Fin N), Orthonormal ℝ v → Injective w → (∀ (i : Fin N) (j : Fin n), inner ℝ (w i) (v j) = 0) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)} → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → ∃ (g : Euclid P → ℝ) (δ : ℝ), 0 < δ ∧ LipschitzWith 1 g ∧ (∀ y : Euclid P, y - w i₀ ∈ Submodule.span ℝ (Set.range v) → g y = 0) ∧ ν.restrict {x | g x < 3 * δ} = ENNReal.ofReal (α i₀) • (μHE[n]).restrict {y : Euclid P | y - w i₀ ∈ Submodule.span ℝ (Set.range v)} ∧ ∀ t r : ℝ, IsCompact ({x | g x ≤ t} ∩ pL ⁻¹' closedBall 0 r) := by
  intro P n N v w α ν pL i₀ hv hw hwv hν hpL
  -- `Q` is the orthogonal projection onto `(span v)ᗮ`.
  let Q : Euclid P →L[ℝ] Euclid P :=
    ContinuousLinearMap.id ℝ (Euclid P) - ∑ j, (innerSL ℝ (v j)).smulRight (v j)
  have hQ : ∀ y, Q y = y - ∑ j, inner ℝ (v j) y • v j := fun y => by
    simp [Q, innerSL_apply_apply]
  have hQv : ∀ y k, inner ℝ (Q y) (v k) = 0 := fun y k => by
    rw [hQ, inner_sub_left, hv.inner_left_fintype, real_inner_comm]
    simp
  have hQle : ∀ y, ‖Q y‖ ≤ ‖y‖ := fun y => by
    have h1 : inner ℝ (Q y) (Q y) = inner ℝ (Q y) y := by
      nth_rewrite 2 [hQ y]
      rw [inner_sub_right, inner_sum]
      simp [inner_smul_right, hQv]
    have h2 : ‖Q y‖ ^ 2 ≤ ‖Q y‖ * ‖y‖ := by
      rw [← real_inner_self_eq_norm_sq, h1]
      exact real_inner_le_norm _ _
    nlinarith [norm_nonneg (Q y), norm_nonneg y]
  have hQK : ∀ k ∈ Submodule.span ℝ (Set.range v), Q k = 0 := fun k hk => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hk
    rw [hQ]
    simp [hv.inner_right_fintype]
  have hQperp : ∀ u, (∀ j, inner ℝ u (v j) = 0) → Q u = u := fun u hu => by
    have hu' : ∀ j, inner ℝ (v j) u = 0 := fun j => by rw [real_inner_comm]; exact hu j
    rw [hQ]
    simp [hu']
  let g : Euclid P → ℝ := fun x => ‖Q (x - w i₀)‖
  have hLip : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun x y => by
    show dist ‖Q (x - w i₀)‖ ‖Q (y - w i₀)‖ ≤ (1 : NNReal) * dist x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    calc |‖Q (x - w i₀)‖ - ‖Q (y - w i₀)‖| ≤ ‖Q (x - w i₀) - Q (y - w i₀)‖ :=
          abs_norm_sub_norm_le _ _
      _ = ‖Q (x - y)‖ := by rw [← map_sub, sub_sub_sub_cancel_right]
      _ ≤ ‖x - y‖ := hQle _
  have hgcont : Continuous g := hLip.continuous
  have hplane : ∀ j y, y - w j ∈ Submodule.span ℝ (Set.range v) → g y = ‖w j - w i₀‖ :=
    fun j y hy => by
      have hsplit : y - w i₀ = (y - w j) + (w j - w i₀) := by abel
      show ‖Q (y - w i₀)‖ = ‖w j - w i₀‖
      rw [hsplit, map_add, hQK _ hy, zero_add, hQperp]
      intro k
      rw [inner_sub_left, hwv, hwv, sub_zero]
  have hzero : ∀ y, y - w i₀ ∈ Submodule.span ℝ (Set.range v) → g y = 0 := fun y hy => by
    rw [hplane i₀ y hy, sub_self, norm_zero]
  obtain ⟨m, hmpos, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ j, j ≠ i₀ → m ≤ ‖w j - w i₀‖ := by
    let c : Fin N → ℝ := fun j => if j = i₀ then 1 else ‖w j - w i₀‖
    refine ⟨Finset.univ.inf' ⟨i₀, Finset.mem_univ _⟩ c,
      (Finset.lt_inf'_iff _).2 fun j _ => ?_, fun j hj => ?_⟩
    · by_cases hj : j = i₀
      · simp [c, hj]
      · simp only [c, hj, ite_false]
        exact norm_pos_iff.2 (sub_ne_zero.2 fun h => hj (hw h))
    · have h1 := Finset.inf'_le c (Finset.mem_univ j)
      have h2 : c j = ‖w j - w i₀‖ := by simp only [c, hj, ite_false]
      linarith
  refine ⟨g, m / 3, div_pos hmpos (by norm_num), hLip, hzero, ?_, ?_⟩
  · have h3 : (3 : ℝ) * (m / 3) = m := by ring
    rw [h3]
    have hS : MeasurableSet {x | g x < m} := measurableSet_lt hgcont.measurable measurable_const
    rw [hν]
    ext B hB
    rw [Measure.restrict_apply hB, Measure.finsetSum_apply, Finset.sum_eq_single i₀]
    · rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply (hB.inter hS),
        Measure.restrict_apply hB]
      congr 2
      ext x
      constructor
      · rintro ⟨⟨hxB, _⟩, hx⟩
        exact ⟨hxB, hx⟩
      · rintro ⟨hxB, hx⟩
        exact ⟨⟨hxB, show g x < m by rw [hzero x hx]; exact hmpos⟩, hx⟩
    · intro j _ hj
      rw [Measure.smul_apply, Measure.restrict_apply (hB.inter hS)]
      have hempty : B ∩ {x | g x < m} ∩ {y | y - w j ∈ Submodule.span ℝ (Set.range v)} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x ⟨⟨_, hxm⟩, hx⟩ => ?_
        have hxm' : g x < m := hxm
        rw [hplane j x hx] at hxm'
        exact absurd hxm' (not_lt.2 (hmle j hj))
      rw [hempty, measure_empty, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · intro t r
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le hgcont continuous_const).inter
        (Metric.isClosed_closedBall.preimage pL.continuous)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨‖w i₀‖ + n * r + t, fun x hx => ?_⟩
      obtain ⟨hxg, hxr⟩ := hx
      have hxg' : ‖Q (x - w i₀)‖ ≤ t := hxg
      rw [Set.mem_preimage, mem_closedBall_zero_iff] at hxr
      rw [mem_closedBall_zero_iff]
      have hdecomp : x = w i₀ + ∑ j, inner ℝ (v j) (x - w i₀) • v j + Q (x - w i₀) := by
        rw [hQ]
        abel
      have hsum : ‖∑ j, inner ℝ (v j) (x - w i₀) • v j‖ ≤ n * r := by
        calc ‖∑ j, inner ℝ (v j) (x - w i₀) • v j‖
            ≤ ∑ j, ‖inner ℝ (v j) (x - w i₀) • v j‖ := norm_sum_le _ _
          _ = ∑ j, ‖pL x j‖ := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_smul, hv.1 j, mul_one, inner_sub_right, real_inner_comm (w i₀) (v j),
                hwv, sub_zero, hpL]
          _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum fun j _ => (PiLp.norm_apply_le _ j).trans hxr
          _ = n * r := by simp
      calc ‖x‖ = ‖w i₀ + ∑ j, inner ℝ (v j) (x - w i₀) • v j + Q (x - w i₀)‖ := by
            rw [← hdecomp]
        _ ≤ ‖w i₀‖ + ‖∑ j, inner ℝ (v j) (x - w i₀) • v j‖ + ‖Q (x - w i₀)‖ := norm_add₃_le
        _ ≤ ‖w i₀‖ + n * r + t := by gcongr
/-- Slicing weakly convergent cycles at a good level (a step of White's projection argument that
a limit of cycles has weight `≥ 1`, towards Simon 7.2.4).  Assume the slicing lemma `(SL)`, the
convergence of slices `(T2)` and the majorant lemma `(MM)`.  Let `g` be `L`-Lipschitz, `G` open, `a < b`, `Γₖ ⇀ X` with
`∂Γₖ = 0`, `Γₖ(ω) = ∫ ⟨ω, ξₖ⟩ dμₖ`, `X(ω) = ∫ ⟨ω, ξ_X⟩ dμ_X`, `limsupₖ μₖ(K) ≤ μ_c(K)` for compact
`K`, `μ_c{g = s} = 0` for `s ∈ (a, b)` and `liminfₖ μₖ(G ∩ {a < g < b}) = 0`.  Then there are
`t ∈ (a, b)` and a subsequence `φ` such that the slices `Zₖ = Γ_{φ(k)}⌞{g < t}` satisfy
`M_G(∂Zₖ) < ∞`, `M_G(∂Zₖ) → 0` and `Zₖ(ω) → ∫_{g<t} ⟨ω, ξ_X⟩ dμ_X`. -/
theorem Submission.cbr_ci_pw_good_level_slices : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) → (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop) → ∀ (P d : ℕ) (Γs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P (d + 1)) (μX μc : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)) (g : Euclid P → ℝ) (L : NNReal) (G : Set (Euclid P)) (a b : ℝ), LipschitzWith L g → IsOpen G → a < b → WeaklyConvergesOn Γs X → (∀ k, (Γs k).boundary = 0) → (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → μs k K < ∞) → (∀ k, AEStronglyMeasurable (ξs k) (μs k)) → (∀ k, ∀ᵐ x ∂(μs k), ∀ β : Covector (Euclid P) (d + 1), |ξs k x β| ≤ covectorEuclideanNorm β) → (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)), Γs k ω = ∫ x, ξs k x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(μs k)) → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ β : Covector (Euclid P) (d + 1), |ξX x β| ≤ covectorEuclideanNorm β) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → μc K < ∞) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μs k K) atTop ≤ μc K) → (∀ t ∈ Ioo a b, μc {x | g x = t} = 0) → (∀ k, μs k (G ∩ {x | a < g x ∧ g x < b}) < ∞) → liminf (fun k => μs k (G ∩ {x | a < g x ∧ g x < b})) atTop = 0 → ∃ t ∈ Ioo a b, ∃ (φ : ℕ → ℕ) (Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), StrictMono φ ∧ (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)), Z k ω = ∫ x in {x | g x < t}, ξs (φ k) x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(μs (φ k))) ∧ (∀ k, (Z k).boundary.massOn G < ∞) ∧ Tendsto (fun k => (Z k).boundary.massOn G) atTop (𝓝 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (∫ x in {x | g x < t}, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX)) := by
  intro SL T2 MM P d Γs X μs ξs μX μc ξX g L G a b hg hG hab hconv hbd hμs hξs hξsb hΓs hμX
    hξX hξXb hX hμc hlimsup hlevel hfin hliminf
  -- Slice every `Γₖ` by `g` with `(SL)`; `∂Γₖ = 0` is represented by the zero measure.
  have hslice := fun k => SL P d univ (Γs k) (μs k) 0 (ξs k) (fun _ => 0) g L isOpen_univ
    (fun K hK _ => hμs k K hK) (fun K _ _ => by simp) (hξs k) aestronglyMeasurable_const
    (hξsb k) (by simp) (hΓs k) (fun η => by simp [hbd k]) hg
  choose A B hA hB hAB hmass hint using hslice
  -- The slices `Bₖ(s)` of `∂Γₖ = 0` vanish, so `∂Aₖ(s) - Bₖ(s) = ∂Aₖ(s)`.
  have hsub : ∀ k s, (A k s).boundary - B k s = (A k s).boundary := by
    intro k s
    ext η
    change (A k s).boundary η - B k s η = (A k s).boundary η
    rw [hB k s η]
    simp
  -- `(MM)` gives a majorant with zero integral over `(a, b)`, hence a level `t ∈ (a, b)` with
  -- `liminfₖ M_G(∂Aₖ(t)) = 0`.
  obtain ⟨w, hwm, hwae, hwint⟩ := MM P μs g G a b L
    (fun k s => ((A k s).boundary - B k s).massOn G) hg.continuous hfin
    (fun k s _ => hmass k G s hG)
  rw [hliminf, mul_zero, nonpos_iff_eq_zero, lintegral_eq_zero_iff hwm] at hwint
  have hne : (volume : Measure ℝ) (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.2 hab
  obtain ⟨t, ht, hlt, hw0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
    ((ae_restrict_of_ae hwae).and hwint)
  have h0 : liminf (fun k => ((A k t).boundary - B k t).massOn G) atTop ≤ 0 :=
    (hlt ht).trans_eq hw0
  -- A subsequence with `M_G(∂A_{φ(k)}(t)) < 1/k`.
  have hfreq : ∀ m : ℕ, ∃ᶠ k in atTop, ((A k t).boundary - B k t).massOn G < (m : ℝ≥0∞)⁻¹ :=
    fun m => frequently_lt_of_liminf_lt (by isBoundedDefault)
      (h0.trans_lt (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m)))
  obtain ⟨φ, hφ, hφlt⟩ := extraction_forall_of_frequently hfreq
  have hZ : ∀ k, (A (φ k) t).boundary.massOn G < (k : ℝ≥0∞)⁻¹ := fun k => by
    simpa only [hsub] using hφlt k
  refine ⟨t, ht, φ, fun k => A (φ k) t, hφ, fun k ω => hA (φ k) t ω,
    fun k => (hZ k).trans_le le_top,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) (fun k => (hZ k).le), fun ω => ?_⟩
  -- `(T2)` along the subsequence: `Γ_{φ(k)} ⇀ X` and `limsupₖ μ_{φ(k)} ≤ limsupₖ μₖ ≤ μ_c`.
  have hT2 := T2 P (d + 1) univ (fun k => Γs (φ k)) X (fun k => μs (φ k)) (fun k => ξs (φ k)) μX
    μc ξX g t isOpen_univ hg.continuous (fun ω => (hconv ω).comp hφ.tendsto_atTop)
    (fun j K hK _ => hμs (φ j) K hK) (fun j => hξs (φ j)) (fun j => hξsb (φ j))
    (fun j ω => hΓs (φ j) ω) (fun K hK _ => hμX K hK) hξX hξXb hX (fun K hK _ => hμc K hK)
    (fun K hK _ => (hφ.tendsto_atTop.limsup_comp_le_limsup (u := fun k => μs k K)).trans
      (hlimsup K hK))
    (hlevel t ht) ω
  exact Tendsto.congr (fun k => (hA (φ k) t ω).symm) hT2

/-- **Smooth cutoff around a compact set** (the cutoff (N4) of White's projection argument): for
`K` compact and `O` open in `ℝᴾ` with `K ⊆ O` there are `χ ∈ C^∞_c(ℝᴾ)` with `tsupport χ ⊆ O`
and `0 ≤ χ ≤ 1`, and an open `O' ⊇ K` with `χ = 1` on `O'`.  Choose `δ > 0` with
`cthickening δ K ⊆ O`; the smooth Urysohn lemma gives `χ` with `support χ = thickening δ K` and
`χ = 1` exactly on `cthickening (δ/2) K`.  Then `tsupport χ ⊆ cthickening δ K ⊆ O`, a compact
set, and `O' = thickening (δ/2) K`. -/
theorem Submission.cbr_ci_pw_proj_smooth_cutoff : ∀ (P : ℕ) (K O : Set (Euclid P)), IsCompact K → IsOpen O → K ⊆ O → ∃ (χ : Euclid P → ℝ) (O' : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen O' ∧ K ⊆ O' ∧ ∀ x ∈ O', χ x = 1 := by
  intro P K O hK hO hKO
  -- Step 1: `cthickening δ K ⊆ O` for some `δ > 0`; put `r = δ/2`
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hr : 0 < δ / 2 := half_pos hδ
  -- Steps 2-3: smooth Urysohn for the closed `cthickening r K` inside the open `thickening δ K`
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K))
      (isClosed_cthickening (δ := δ / 2) (E := K))
      (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  -- Step 4: `tsupport χ = closure (thickening δ K) ⊆ cthickening δ K`
  have hts : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening δ K
  -- Steps 5-7: compact support inside the compact `cthickening δ K`, the bounds `0 ≤ χ ≤ 1`, and
  -- `χ = 1` on `O' = thickening r K ⊆ cthickening r K`
  refine ⟨χ, thickening (δ / 2) K, hχ, ?_, hts.trans hδO, fun x => ?_, isOpen_thickening,
    self_subset_thickening hr K, fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
  · exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport χ) hts
  · exact hrange (mem_range_self x)

/-- **Cut-off extension of a pulled-back form** (the forms `χ · p^#ω`, `χ · p^#γ` of the projection
argument).  Let `γ` be a smooth `l`-form on `ℝᵐ`, `p : ℝᴾ → ℝᵐ` continuous linear with
`(p^#γ)(x) = γ(p x) ∘ p`, and `S, O ⊆ ℝᴾ` with `O` open and `K = S ∩ p⁻¹(spt γ)` compact, `K ⊆ O`.
A smooth cut-off `χ` (`spt χ ⊆ O`, `0 ≤ χ ≤ 1`, `χ = 1` on an open `O' ⊇ K`) gives the test form
`γ' = χ · p^#γ` on `ℝᴾ` with `spt γ' ⊆ O` and `|γ'| = χ |p^#γ| ≤ |p^#γ|`; on `S`, `γ' = p^#γ`, since
`p^#γ` vanishes at points of `S` off `O'`.  At `x ∈ S ∩ O'`, `γ' = p^#γ` near `x`, so
`dγ'(x) = d(p^#γ)(x) = p^#(dγ)(x)` by locality and naturality of `d`; at `x ∈ S \ O'`, `γ'` vanishes
near `x` and `γ` near `p x`, so both sides are `0`. -/
theorem Submission.cbr_ci_pw_proj_pullback_extension : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S O : Set (Euclid P)) (γ : DifferentialForm (Euclid m) l), ContDiff ℝ (⊤ : ℕ∞) γ → IsOpen O → IsCompact (S ∩ pL ⁻¹' tsupport γ) → S ∩ pL ⁻¹' tsupport γ ⊆ O → ∃ γ' : TestFormOn (univ : Set (Euclid P)) l, tsupport (γ' : DifferentialForm (Euclid P) l) ⊆ O ∧ (∀ x, covectorEuclideanNorm ((γ' : DifferentialForm (Euclid P) l) x) ≤ covectorEuclideanNorm ((γ (pL x)).compContinuousLinearMap pL)) ∧ (∀ x ∈ S, (γ' : DifferentialForm (Euclid P) l) x = (γ (pL x)).compContinuousLinearMap pL) ∧ ∀ x ∈ S, exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x = (exteriorDerivative γ (pL x)).compContinuousLinearMap pL := by
  intro P m l pL S O γ hγ hO hK hKO
  -- Step 1: a smooth cut-off `χ`, `spt χ ⊆ O`, `0 ≤ χ ≤ 1`, `χ = 1` on an open `O' ⊇ K`
  obtain ⟨χ, O', hχ, hχc, hχO, hχ01, hO', hKO', hχ1⟩ :=
    Submission.cbr_ci_pw_proj_smooth_cutoff P _ O hK hO hKO
  -- Step 2: `β = p^#γ = Λ ∘ γ ∘ pL` is smooth, `Λ α = α ∘ pL` being continuous linear
  set β : DifferentialForm (Euclid P) l := fun x => (γ (pL x)).compContinuousLinearMap pL
    with hβdef
  have hβ : ContDiff ℝ (⊤ : ℕ∞) β := by
    have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ) pL).contDiff
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) |>.comp (hγ.comp pL.contDiff)
    simpa [Function.comp_def] using this
  -- Step 3: `β x = 0` whenever `pL x ∉ spt γ`
  have hβ0 : ∀ x, pL x ∉ tsupport γ → β x = 0 := by
    intro x hx
    ext v
    simp [hβdef, image_eq_zero_of_notMem_tsupport hx]
  -- Step 4: `γ' = χ • β` is a test form on `ℝᴾ` with `spt γ' ⊆ spt χ ⊆ O`
  set g : DifferentialForm (Euclid P) l := fun x => χ x • β x with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul hβ
  have hgc : HasCompactSupport g := hχc.smul_right
  have hgs : tsupport g ⊆ tsupport χ := tsupport_smul_subset_left _ _
  let γ' : TestFormOn (univ : Set (Euclid P)) l := ⟨g, ⟨⟨hg, hgc⟩, subset_univ _⟩⟩
  -- Step 5: the coefficient norm is absolutely homogeneous, `|c • α| = |c| |α|`
  have hscale : ∀ (c : ℝ) (α : Covector (Euclid P) l),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have : (∑ I : Fin l → Fin P, if StrictMono I then
          ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin l → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs <;> simp [mul_pow]
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  refine ⟨γ', hgs.trans hχO, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  -- Step 6 (b): `|χ x • β x| = χ x |β x| ≤ |β x|`
  · change covectorEuclideanNorm (χ x • β x) ≤ covectorEuclideanNorm (β x)
    rw [hscale, abs_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2
  -- Step 7 (c): `χ = 1` on `O'`, and `β x = 0` at `x ∈ S \ O'`, since `K ⊆ O'`
  · change χ x • β x = β x
    by_cases hxO' : x ∈ O'
    · rw [hχ1 x hxO', one_smul]
    · have : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
      rw [hβ0 x this, smul_zero]
  -- Step 8 (d) on `O'`: `g = β` near `x`, so `dg(x) = dβ(x) = p^#(dγ)(x)` by naturality of `d`
  · change extDeriv g x = (extDeriv γ (pL x)).compContinuousLinearMap pL
    by_cases hxO' : x ∈ O'
    · have hev : g =ᶠ[𝓝 x] β := by
        filter_upwards [hO'.mem_nhds hxO'] with y hy
        simp [hgdef, hχ1 y hy]
      rw [hev.extDeriv_eq]
      have hpb := extDeriv_pullback (x := x) (ω := γ) (f := ⇑pL) (r := ((⊤ : ℕ∞) : WithTop ℕ∞))
        ((hγ.differentiable (by simp)).differentiableAt) pL.contDiff.contDiffAt (by simp)
      simpa [ContinuousLinearMap.fderiv] using hpb
    -- Step 9 (d) off `O'`: `g` vanishes near `x` and `γ` near `pL x`, so both sides are `0`
    · have hxK : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
      have hopen : IsOpen ((tsupport γ)ᶜ) := (isClosed_tsupport γ).isOpen_compl
      have hev : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [(hopen.preimage pL.continuous).mem_nhds hxK] with y hy
        simp [hgdef, hβ0 y hy]
      have hev' : γ =ᶠ[𝓝 (pL x)] 0 := by
        filter_upwards [hopen.mem_nhds hxK] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [hev.extDeriv_eq, hev'.extDeriv_eq]
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
/-- **Integral estimate for the projected current** (integrability and the estimate of step 3 in
White's projection argument, from (N2) and (N3)): let `F ⊆ S` be measurable with `S ∩ pL⁻¹(K)`
compact, `μ` finite on compact sets, `ξ` `μ`-a.e. strongly measurable with `|⟨β, ξ(x)⟩| ≤ |β|_E`
`μ`-a.e., and `|γ ∘ pL|_E ≤ |γ|_E` for every `l`-covector `γ` on `ℝᵐ`.  With
`C = √#(Fin l → Fin m)`, so that `|α|_E ≤ C ‖α‖` (`le_opNorm` on unit basis vectors), and
`c = C μ(S ∩ pL⁻¹(K))`: for every continuous `l`-form `ω` on `ℝᵐ` vanishing off `K` with
`‖ω‖ ≤ M`, `|⟨ω(pL x) ∘ pL, ξ(x)⟩| ≤ C M 1_{S ∩ pL⁻¹(K)}(x)` for `μ⌞F`-a.e. `x`, so the integrand
is `μ⌞F`-integrable and `|∫_F ⟨ω(pL x) ∘ pL, ξ(x)⟩ dμ| ≤ C M μ(F ∩ S ∩ pL⁻¹(K)) ≤ c M`. -/
theorem Submission.cbr_ci_pw_proj_integral_estimate : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S F : Set (Euclid P)) (K : Set (Euclid m)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → IsCompact (S ∩ pL ⁻¹' K) → (∀ K' : Set (Euclid P), IsCompact K' → μ K' < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ω : DifferentialForm (Euclid m) l) (M : ℝ), Continuous ω → (∀ y, y ∉ K → ω y = 0) → (∀ y, ‖ω y‖ ≤ M) → Integrable (fun x => ξ x ((ω (pL x)).compContinuousLinearMap pL)) (μ.restrict F) ∧ |∫ x in F, ξ x ((ω (pL x)).compContinuousLinearMap pL) ∂μ| ≤ c * M := by
  intro P m l pL S F K μ ξ hF hFS hSK hμ hξm hξb hN3
  -- Step 1 (N2): `|α|_E ≤ C ‖α‖` with `C = √#(Fin l → Fin m)`, since `|α(e_I)| ≤ ‖α‖`
  set C : ℝ := Real.sqrt (Fintype.card (Fin l → Fin m)) with hCdef
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hN2 : ∀ α : Covector (Euclid m) l, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hCdef, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc (∑ I : Fin l → Fin m, if StrictMono I then
            (α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))) ^ 2 else 0)
        ≤ ∑ _I : Fin l → Fin m, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h1 := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))
            have hprod : ∏ i, ‖EuclideanSpace.basisFun (Fin m) ℝ (I i)‖ = 1 := by
              simp
            rw [hprod, mul_one] at h1
            have h2 : |α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))| ≤ ‖α‖ := by
              simpa [Real.norm_eq_abs] using h1
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h2 2
          · positivity
      _ = (Fintype.card (Fin l → Fin m) : ℝ) * ‖α‖ ^ 2 := by simp
  -- Step 2: `A = S ∩ pL⁻¹(K)` is compact, so measurable with `μ(A) < ∞`; `c = C μ(A)`
  set μK : ℝ := (μ (S ∩ pL ⁻¹' K)).toReal with hμKdef
  have hSKm : MeasurableSet (S ∩ pL ⁻¹' K) := hSK.isClosed.measurableSet
  have hμKfin : μ (S ∩ pL ⁻¹' K) < ∞ := hμ _ hSK
  refine ⟨C * μK, mul_nonneg hC0 ENNReal.toReal_nonneg, fun ω M hω hωK hωM => ?_⟩
  -- Step 3: `M ≥ ‖ω(0)‖ ≥ 0`, and `β(x) = ω(pL x) ∘ pL` is continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hωM 0)
  set β : Euclid P → Covector (Euclid P) l := fun x => (ω (pL x)).compContinuousLinearMap pL
    with hβdef
  have hβc : Continuous β := by
    have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ)
      pL).continuous.comp (hω.comp pL.continuous)
    simpa [Function.comp_def] using this
  -- Step 4: `x ↦ ξ(x)(β(x))` is the continuous evaluation of `(ξ, β)`, so a.e. strongly measurable
  have hΦm : AEStronglyMeasurable (fun x => ξ x (β x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) l)
      (F := ℝ)).continuous.comp_aestronglyMeasurable (hξm.prodMk hβc.aestronglyMeasurable)
  -- Step 5: `|ξ(x)(β(x))| ≤ g(x) = C M 1_A(x)` for `μ⌞F`-a.e. `x`
  set g : Euclid P → ℝ := (S ∩ pL ⁻¹' K).indicator (fun _ => C * M) with hgdef
  have hb : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (β x)‖ ≤ g x := by
    filter_upwards [ae_restrict_mem hF, ae_restrict_of_ae hξb] with x hxF hx
    by_cases hxK : pL x ∈ K
    · rw [hgdef, indicator_of_mem (show x ∈ S ∩ pL ⁻¹' K from ⟨hFS hxF, hxK⟩), Real.norm_eq_abs]
      calc |ξ x (β x)| ≤ covectorEuclideanNorm (β x) := hx _
        _ ≤ covectorEuclideanNorm (ω (pL x)) := hN3 _
        _ ≤ C * ‖ω (pL x)‖ := hN2 _
        _ ≤ C * M := mul_le_mul_of_nonneg_left (hωM _) hC0
    · have h0 : ω (pL x) = 0 := hωK _ hxK
      have hβ0 : β x = 0 := by
        ext v
        simp [hβdef, h0]
      rw [hgdef, indicator_of_notMem (fun h => hxK h.2), hβ0, map_zero, norm_zero]
  -- Step 6: `g` is `μ⌞F`-integrable since `μ(A ∩ F) ≤ μ(A) < ∞`; domination gives integrability
  have hgint : Integrable g (μ.restrict F) := by
    rw [hgdef, integrable_indicator_iff hSKm]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hSKm]
    exact (lt_of_le_of_lt (measure_mono inter_subset_left) hμKfin).ne
  refine ⟨Integrable.mono' hgint hΦm.restrict hb, ?_⟩
  -- Step 7: `|∫_F ξ(β)| ≤ ∫ g d(μ⌞F) = C M μ(A ∩ F) ≤ C M μ(A) = c M`
  have hle := norm_integral_le_of_norm_le hgint hb
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  rw [hgdef, integral_indicator hSKm, setIntegral_const, smul_eq_mul]
  have hle2 : (μ.restrict F).real (S ∩ pL ⁻¹' K) ≤ μK := by
    rw [Measure.real, Measure.restrict_apply hSKm, hμKdef]
    exact ENNReal.toReal_mono hμKfin.ne (measure_mono inter_subset_left)
  have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0
  calc (μ.restrict F).real (S ∩ pL ⁻¹' K) * (C * M) ≤ μK * (C * M) :=
        mul_le_mul_of_nonneg_right hle2 hCM
    _ = C * μK * M := by ring

/-- **The pulled-back integral is a current** (projection step): for `ω ∈ 𝒟ˡ(U)` put
`Y(ω) = ∫_F ⟨ω(pL x) ∘ pL, ξ(x)⟩ dμ(x)`.  By `integral_estimate` with `K = spt ω` every integrand
is `μ⌞F`-integrable, so `Y` is linear; if `ωⱼ → 0` in `𝒟ˡ(U)` with all supports in a compact
`K ⊆ U`, the same estimate gives `|Y(ωⱼ)| ≤ c · sup ‖ωⱼ‖ → 0`, so `Y ∈ 𝒟ₗ(U)` (Simon 6.2.1). -/
theorem Submission.cbr_ci_pw_proj_integral_current : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ Y : GeometricCurrentOn U l, ∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ := by
  intro P m l pL U S F μ ξ hF hFS hcpt hμ hξm hξb hN3
  -- every integrand is `μ⌞F`-integrable: `integral_estimate` with `K = spt ω`, `M = sup ‖ω‖`
  have hint : ∀ ω : TestFormOn U l, Integrable (fun x => ξ x
      (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)) (μ.restrict F) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid m) l) := ω.property.1.1.continuous
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid m) l)) := ω.property.1.2
    obtain ⟨c, -, hc⟩ := Submission.cbr_ci_pw_proj_integral_estimate P m l pL S F
      (tsupport (ω : DifferentialForm (Euclid m) l)) μ ξ hF hFS (hcpt _ hK ω.property.2) hμ hξm
      hξb hN3
    obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
    exact (hc _ M hωc (fun y hy => image_eq_zero_of_notMem_tsupport hy) hM).1
  -- `Y` is linear: `ω ↦ ⟨ω(pL x) ∘ pL, ξ(x)⟩` is linear for each `x`
  let T : CurrentOn U l :=
    { toFun := fun ω => ∫ x in F, ξ x
        (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ
      map_add' := fun ω η => by
        rw [← integral_add (hint ω) (hint η)]
        congr 1
        funext x
        rw [← map_add]
        congr 1
      map_smul' := fun c ω => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext x
        rw [← smul_eq_mul, ← map_smul]
        congr 1 }
  refine ⟨⟨T, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  -- continuity: the supports lie in one compact `K ⊆ U` and `ωⱼ → 0` uniformly on `K`
  obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
  obtain ⟨c, hc0, hc⟩ := Submission.cbr_ci_pw_proj_integral_estimate P m l pL S F K μ ξ hF hFS
    (hcpt K hK hKU) hμ hξm hξb hN3
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (c + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  -- `‖ωₙ(y)‖ ≤ ε / (c + 1)` everywhere: on `K` by uniform convergence, off `K` `ωₙ(y) = 0`
  have hbd : ∀ y, ‖(ωs n : DifferentialForm (Euclid m) l) y‖ ≤ ε / (c + 1) := by
    intro y
    by_cases hy : y ∈ K
    · have := hN n hn y hy
      simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
        norm_iteratedFDeriv_zero] at this
      exact this.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)), norm_zero]
      exact hδ.le
  have hωc : Continuous (ωs n : DifferentialForm (Euclid m) l) := (ωs n).property.1.1.continuous
  have := (hc _ _ hωc (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)))
    hbd).2
  rw [Real.dist_eq, sub_zero]
  calc |T (ωs n)| ≤ c * (ε / (c + 1)) := this
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
/-- **Mass bound for a projected current** (Simon (6.2.5); the mass estimate in White's projection
argument): let `U ⊆ ℝᵐ` be open, `pL : ℝᴾ → ℝᵐ` linear with `|γ ∘ pL|_E ≤ |γ|_E` for every
`l`-covector `γ` on `ℝᵐ`, `|⟨β, ξ(x)⟩| ≤ |β|_E` for `μ`-a.e. `x`, and
`Y(ω) = ∫_F ⟨ω(pL x) ∘ pL, ξ(x)⟩ dμ(x)` for `ω ∈ 𝒟ˡ(U)`.  Then `M_U(Y) ≤ μ(F ∩ pL⁻¹(U))`.  For an
admissible `ω` the integrand has absolute value `≤ |ω(pL x)|_E ≤ 1`, and it vanishes when
`pL x ∉ U ⊇ spt ω`; so `Y(ω) ≤ ‖∫_F ·‖ₑ ≤ ∫⁻_F ‖·‖ₑ ≤ ∫⁻_F 1_{pL⁻¹(U)} = μ(F ∩ pL⁻¹(U))`.  The
estimate runs in `ℝ≥0∞`, so it needs neither integrability nor measurability of `F`. -/
theorem Submission.cbr_ci_pw_proj_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l) (Y : GeometricCurrentOn U l), IsOpen U → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ) → Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) := by
  intro P m l pL U F μ ξ Y hU hξb hN3 hY
  -- `pL⁻¹(U)` is open, hence measurable
  have hUm : MeasurableSet (pL ⁻¹' U) := (hU.preimage pL.continuous).measurableSet
  -- Step 1: it suffices to bound `ofReal (Y ω)` for each admissible `ω`
  apply sSup_le
  rintro r ⟨ω, ⟨-, hω1⟩, rfl⟩
  show ENNReal.ofReal (Y ω) ≤ _
  rw [hY ω]
  -- Step 2: `‖Φ_ω‖ₑ ≤ 1_{pL⁻¹(U)}` a.e. on `F`; off `pL⁻¹(U)`, `ω (pL x) = 0` as `tsupport ω ⊆ U`
  have hpt : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ≤ (pL ⁻¹' U).indicator 1 x := by
    filter_upwards [ae_restrict_of_ae hξb] with x hx
    by_cases hxU : pL x ∈ U
    · rw [indicator_of_mem (show x ∈ pL ⁻¹' U from hxU), Pi.one_apply, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hx _).trans ((hN3 _).trans (hω1 _)))
    · have h0 : (ω : DifferentialForm (Euclid m) l) (pL x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
      have hβ0 : ((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL = 0 := by
        ext v
        simp [h0]
      rw [hβ0, map_zero, enorm_zero]
      exact zero_le
  -- Step 3: `ofReal (Y ω) ≤ ‖∫_F Φ_ω‖ₑ ≤ ∫⁻_F ‖Φ_ω‖ₑ ≤ ∫⁻_F 1_{pL⁻¹(U)} = μ(F ∩ pL⁻¹(U))`
  calc ENNReal.ofReal (∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ)
      ≤ ‖∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in F, ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in F, (pL ⁻¹' U).indicator 1 x ∂μ := lintegral_mono_ae hpt
    _ = μ (F ∩ pL ⁻¹' U) := by
        rw [lintegral_indicator_one hUm, Measure.restrict_apply hUm, inter_comm]

/-- **Boundary mass under projection** (projection step of the closure argument used for
Simon 7.2.4, Remark 7.2.5(1)).  Write `p = pL` and `(p^#ω)(x) = ω(p x) ∘ p`.  Let
`Y(ω) = ∫_F ξ(p^#ω) dμ` in `U` and `Z(ω) = ∫_F ξ(ω) dμ` in `ℝᴾ`, where `F ⊆ S` is measurable,
`S ∩ p⁻¹(K)` is compact for compact `K ⊆ U`, and `|γ ∘ p| ≤ |γ|` for `l`-covectors `γ`.  Then
`M_W(∂Y) ≤ M_{p⁻¹(W)}(∂Z)` for every open `W`: each `γ` admissible for `M_W(∂Y)` has a cut-off
pull-back `γ'` (`cbr_ci_pw_proj_pullback_extension`) that is admissible for `M_{p⁻¹(W)}(∂Z)`
and satisfies `dγ' = p^#(dγ)` on `S`, so `∂Y(γ) = ∂Z(γ')`. -/
theorem Submission.cbr_ci_pw_proj_boundary_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (l + 1)) (Y : GeometricCurrentOn U (l + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (l + 1)), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U (l + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) (l + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (l + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (l + 1)) x) ∂μ) → ∀ W : Set (Euclid m), IsOpen W → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W) := by
  intro P m l pL U S F μ ξ Y Z hF hFS hcpt hN3 hY hZ W hW
  -- Step 1: it suffices to bound `∂Y(γ)` for every `γ` admissible for `M_W(∂Y)`
  apply sSup_le
  rintro r ⟨γ, ⟨hγW, hγ1⟩, rfl⟩
  show ENNReal.ofReal (Y.boundary γ) ≤ _
  -- Steps 2–3: `S ∩ p⁻¹(spt γ)` is a compact subset of the open set `p⁻¹(W)`, so `p^#γ` has a
  -- cut-off `γ' ∈ 𝒟ˡ(ℝᴾ)` supported in `p⁻¹(W)`
  have hK : IsCompact (S ∩ pL ⁻¹' tsupport (γ : DifferentialForm (Euclid m) l)) :=
    hcpt _ γ.property.1.2 γ.property.2
  obtain ⟨γ', hγ'O, hγ'n, -, hγ'd⟩ := Submission.cbr_ci_pw_proj_pullback_extension P m l pL S
    (pL ⁻¹' W) (γ : DifferentialForm (Euclid m) l) γ.property.1.1 (hW.preimage pL.continuous) hK
    (fun x hx => hγW hx.2)
  -- Step 4: `|γ'(x)| ≤ |γ(p x) ∘ p| ≤ |γ(p x)| ≤ 1`, so `γ'` is admissible for `M_{p⁻¹(W)}(∂Z)`
  have hadm : γ' ∈ massAdmissibleOn (univ : Set (Euclid P)) l (pL ⁻¹' W) :=
    ⟨hγ'O, fun x => (hγ'n x).trans ((hN3 _).trans (hγ1 _))⟩
  -- Step 5: `∂Y(γ) = ∫_F ξ(p^#(dγ)) dμ = ∫_F ξ(dγ') dμ = ∂Z(γ')`, since `F ⊆ S`
  have heq : Y.boundary γ = Z.boundary γ' := by
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hY, hZ]
    apply setIntegral_congr_fun hF
    intro x hx
    change ξ x ((exteriorDerivative (γ : DifferentialForm (Euclid m) l)
        (pL x)).compContinuousLinearMap pL) =
      ξ x (exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x)
    rw [hγ'd x (hFS hx)]
  -- Step 6: `ofReal (∂Y(γ)) = ofReal (∂Z(γ')) ≤ M_{p⁻¹(W)}(∂Z)`
  rw [heq]
  exact Z.boundary.le_massOn hadm

/-- Projected current for the weight bound `α_{i₀} ≥ 1` in the proof of **Simon 7.2.4**
(steps 5–7 of that bound, with `Yₖ = p_#(Γₖ⌞{g < t})` written as an integral).  Let `v` be
orthonormal in `ℝᴾ`, `pL x = (⟨vᵢ, x⟩)ᵢ`, and `Z(ω) = ∫_F ⟨ω(x), ξ(x)⟩ dμ(x)` in `ℝᴾ`, where
`|⟨β, ξ⟩| ≤ |β|` a.e., `F ⊆ S` and `S ∩ pL⁻¹K` is compact for compact `K ⊆ U`.  Then
`Y(ω) := ∫_F ⟨ω(pL x) ∘ pL, ξ(x)⟩ dμ(x)` is a current in `U` with `M_U(Y) ≤ μ(F ∩ pL⁻¹U)` and
`M_W(∂Y) ≤ M_{pL⁻¹W}(∂Z)` for open `W ⊆ U`, and each pull-back `p^#ω` agrees on `S` with a test
form on `ℝᴾ`.  The covector bound `|γ ∘ pL| ≤ |γ|` (in degrees `d + 1` and `d`) is
`cbr_ci_pw_orthonormal_covector_bounds`; the four conclusions are `cbr_ci_pw_proj_integral_current`,
`cbr_ci_pw_proj_mass_le`, `cbr_ci_pw_proj_boundary_mass_le` and
`cbr_ci_pw_proj_pullback_extension` (with `O = ℝᴾ`). -/
theorem Submission.cbr_ci_pw_projected_current : ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P) (pL : Euclid P →L[ℝ] Euclid (d + 1)) (U : Set (Euclid (d + 1))) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin (d + 1)), pL x i = inner ℝ (v i) x) → IsOpen U → MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid (d + 1)), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) (d + 1), |ξ x β| ≤ covectorEuclideanNorm β) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∃ Y : GeometricCurrentOn U (d + 1), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) ∧ Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) ∧ (∀ W : Set (Euclid (d + 1)), IsOpen W → W ⊆ U → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W)) ∧ ∀ ω : TestFormOn U (d + 1), ∃ ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), ∀ x ∈ S, (ω' : DifferentialForm (Euclid P) (d + 1)) x = ((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL := by
  intro P d v pL U S F μ ξ Z hv hpL hU hF hFS hcpt hμ hξm hξb hZ
  -- (N3): `|γ ∘ pL| ≤ |γ|` for covectors of every degree on `ℝⁿ`, `n = d + 1`.
  have hN3 := (Submission.cbr_ci_pw_orthonormal_covector_bounds P (d + 1) v pL hv hpL).2
  -- Steps 1–3: `Y` is a current in `U`, given by the integral formula (i).
  obtain ⟨Y, hY⟩ := Submission.cbr_ci_pw_proj_integral_current P (d + 1) (d + 1) pL U S F μ ξ
    hF hFS hcpt hμ hξm hξb (hN3 (d + 1))
  -- Step 4 gives (ii) and step 6 gives (iii).
  refine ⟨Y, hY,
    Submission.cbr_ci_pw_proj_mass_le P (d + 1) (d + 1) pL U F μ ξ Y hU hξb (hN3 (d + 1)) hY,
    fun W hW _ => Submission.cbr_ci_pw_proj_boundary_mass_le P (d + 1) d pL U S F μ ξ Y Z hF hFS
      hcpt (hN3 d) hY hZ W hW, fun ω => ?_⟩
  -- Step 5, (iv): cut off `p^#ω` near the compact set `S ∩ pL⁻¹(spt ω)`.
  obtain ⟨ω', -, -, hω', -⟩ := Submission.cbr_ci_pw_proj_pullback_extension P (d + 1) (d + 1) pL
    S univ (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) ω.property.1.1 isOpen_univ
    (hcpt _ ω.property.1.2 ω.property.2) (subset_univ _)
  exact ⟨ω', hω'⟩
/-- **A continuous determinant `n`-covector on `ℝⁿ`**: some `δ ∈ Λⁿ(ℝⁿ)` (a continuous
alternating `n`-form) has `δ(e₁, …, eₙ) = 1` for the standard basis `eᵢ`.  Take the volume form
`ω` of the orientation of the standard orthonormal basis `B`; Hadamard's inequality
`|ω(v)| ≤ ∏ᵢ ‖vᵢ‖` makes it continuous, and `ω = det_B` gives `δ(e₁, …, eₙ) = det_B(B) = 1`. -/
theorem Submission.dgoj_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
  intro n
  have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
  refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
  · rw [one_mul, Real.norm_eq_abs]
    exact o.abs_volumeForm_apply_le m
  · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
    have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
      funext i; simp [b]
    rw [h, Module.Basis.det_self]
/-- **Top-degree covectors of `ℝⁿ`**: if `δ ∈ Λⁿ(ℝⁿ)` has `δ(e₁, …, eₙ) = 1` for the standard
basis `eᵢ`, then its Euclidean coefficient norm is `1` and `α = α(e₁, …, eₙ) • δ` for every
`α ∈ Λⁿ(ℝⁿ)` (Simon 6.1: `Λⁿ(ℝⁿ) = ℝ · dx¹ ∧ ⋯ ∧ dxⁿ`).  Every top-degree form is
`β = β(e) • det_b` for the standard basis `b` (`AlternatingMap.eq_smul_basis_det`), and the
identity is the only strictly increasing `Fin n → Fin n`, so the coefficient sum defining
`covectorEuclideanNorm δ` has the single term `δ(e)² = 1`. -/
theorem Submission.cbr_ci_pw_td_top_covector_spans : ∀ (n : ℕ) (δ : Covector (Euclid n) n), δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 → covectorEuclideanNorm δ = 1 ∧ ∀ α : Covector (Euclid n) n, α = α (fun i => EuclideanSpace.single i (1 : ℝ)) • δ := by
  intro n δ hδ
  classical
  let b : Module.Basis (Fin n) ℝ (Euclid n) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hbe : (⇑b : Fin n → Euclid n) = fun i => EuclideanSpace.single i (1 : ℝ) := by
    funext i; simp [b]
  have key : ∀ (β : Covector (Euclid n) n) (v : Fin n → Euclid n),
      β v = β (fun i => EuclideanSpace.single i (1 : ℝ)) * b.det v := by
    intro β v
    have := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det b β.toAlternatingMap)
    simpa [hbe] using this
  refine ⟨?_, ?_⟩
  · have hmono : ∀ I : Fin n → Fin n, StrictMono I → I = id := by
      intro I hI
      have hsurj : Surjective I := Finite.injective_iff_surjective.1 hI.injective
      exact (hI.range_inj_of_wellFoundedLT strictMono_id).1 (by rw [hsurj.range_eq, range_id])
    have he : (fun i => EuclideanSpace.basisFun (Fin n) ℝ (id i)) = fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (id : Fin n → Fin n)]
    · simp only [strictMono_id, ↓reduceIte, he, hδ, one_pow, Real.sqrt_one]
    · intro I _ hI
      have hI' : ¬ StrictMono I := fun h => hI (hmono I h)
      simp only [hI', ↓reduceIte]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro α
    ext v
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, key α v, key δ v, hδ, one_mul]
/-- **Density of a bounded field against a finite measure `μ ≪ Lⁿ`** (Radon–Nikodym, Simon
1.3.24): if `μ(ℝⁿ) < ∞`, `μ ≪ Lⁿ` and `|h| ≤ 1` `μ`-a.e., then `u = ρ h̃`, with `ρ = dμ/dLⁿ` and
`h̃` a strongly measurable representative of `h`, is Lebesgue integrable, `∫ |u| dy ≤ μ(ℝⁿ)`, and
`∫ g h dμ = ∫ u g dy` for every `g`.  Here `μ = Lⁿ⌞ρ` because the singular part of `μ` vanishes. -/
theorem Submission.cbr_ci_pw_td_finite_ac_density : ∀ (n : ℕ) (μ : Measure (Euclid n)) (h : Euclid n → ℝ), μ univ < ∞ → μ ≪ volume → AEStronglyMeasurable h μ → (∀ᵐ y ∂μ, |h y| ≤ 1) → ∃ u : Euclid n → ℝ, Integrable u ∧ ∫ y, |u y| ≤ (μ univ).toReal ∧ ∀ g : Euclid n → ℝ, ∫ y, g y * h y ∂μ = ∫ y, u y * g y := by
  intro n μ h hfin hac hhm hhb
  have : IsFiniteMeasure μ := ⟨hfin⟩
  set ρ : Euclid n → ℝ≥0∞ := μ.rnDeriv volume with hρ
  have hρm : Measurable ρ := Measure.measurable_rnDeriv μ volume
  have hρfin : ∀ᵐ y ∂(volume : Measure (Euclid n)), ρ y < ∞ := Measure.rnDeriv_lt_top μ volume
  have hμeq : μ = (volume : Measure (Euclid n)).withDensity ρ := by
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add μ volume]
    rw [Measure.singularPart_eq_zero_of_ac hac, zero_add]
  let h' := hhm.mk h
  have hh'm : StronglyMeasurable h' := hhm.stronglyMeasurable_mk
  have hhh' : h =ᵐ[μ] h' := hhm.ae_eq_mk
  have hint : Integrable (fun y => (ρ y).toReal) :=
    integrable_toReal_of_lintegral_ne_top hρm.aemeasurable (Measure.lintegral_rnDeriv_lt_top μ volume).ne
  have h1 : ∀ᵐ y ∂μ, |h' y| ≤ 1 := (hhb.and hhh').mono fun y hy => hy.2 ▸ hy.1
  rw [hμeq, ae_withDensity_iff hρm] at h1
  have hbound : ∀ᵐ y ∂(volume : Measure (Euclid n)), ‖(ρ y).toReal * h' y‖ ≤ (ρ y).toReal := by
    filter_upwards [h1] with y hy
    by_cases h0 : ρ y = 0
    · simp [h0]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hy h0)
  have hu : Integrable (fun y => (ρ y).toReal * h' y) :=
    hint.mono' ((ENNReal.measurable_toReal.comp hρm).stronglyMeasurable.mul hh'm).aestronglyMeasurable hbound
  refine ⟨fun y => (ρ y).toReal * h' y, hu, ?_, ?_⟩
  · have hlin : ∫⁻ y, ρ y = μ univ := by
      conv_rhs => rw [hμeq]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫ y, |(ρ y).toReal * h' y| ≤ ∫ y, (ρ y).toReal :=
          integral_mono_ae hu.abs hint (hbound.mono fun y hy => by simpa [Real.norm_eq_abs] using hy)
      _ = (∫⁻ y, ρ y).toReal := integral_toReal hρm.aemeasurable hρfin
      _ = (μ univ).toReal := by rw [hlin]
  · intro g
    calc ∫ y, g y * h y ∂μ = ∫ y, g y * h' y ∂μ :=
          integral_congr_ae (hhh'.mono fun y hy => by simp only [hy])
      _ = ∫ y, g y * h' y ∂((volume : Measure (Euclid n)).withDensity ρ) := by rw [← hμeq]
      _ = ∫ y, (ρ y).toReal • (g y * h' y) :=
          integral_withDensity_eq_integral_toReal_smul hρm hρfin _
      _ = ∫ y, (ρ y).toReal * h' y * g y := by
          congr 1; funext y; rw [smul_eq_mul]; ring

/-- **Top-dimensional currents with finite mass and locally finite boundary mass have `L¹`
densities.**  Assume the mass representation (REP).  If `U ⊆ ℝⁿ` is open (`n = d + 1`),
`Y ∈ 𝒟ₙ(U)`, `M_U(Y) < ∞` and `M_W(∂Y) < ∞` for `W ⊂⊂ U`, then `Y(ω) = ∫_U u ω(e) dy` for an
integrable `u` with `∫_U |u| ≤ M_U(Y)`, `e = (e₁, …, eₙ)` the standard basis.  (REP) gives
`(μ, ξ)`; the boundary bound gives `μ ≪ Hⁿ = Lⁿ`, and `μ(ℝⁿ) ≤ μ(U) + μ(Uᶜ) = M_U(Y)`.  For
`δ = dy` (`δ(e) = 1`) every top covector is `λ = λ(e) δ`, so `ξ(ω) = ω(e) ξ(δ)`; the density of
`μ` against the field `ξ(δ)`, `|ξ(δ)| ≤ |δ| = 1`, is the required `u`. -/
theorem Submission.cbr_ci_pw_top_current_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (d : ℕ) (U : Set (Euclid (d + 1))) (Y : GeometricCurrentOn U (d + 1)), IsOpen U → Y.massOn U < ∞ → (∀ W : Set (Euclid (d + 1)), IsOpen W → CompactlyContained W U → Y.boundary.massOn W < ∞) → ∃ u : Euclid (d + 1) → ℝ, IntegrableOn u U ∧ ENNReal.ofReal (∫ y in U, |u y|) ≤ Y.massOn U ∧ ∀ ω : TestFormOn U (d + 1), Y ω = ∫ y in U, u y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro REP d U Y hU hYU hbd
  have hloc : ∀ W : Set (Euclid (d + 1)), IsOpen W → CompactlyContained W U → Y.massOn W < ∞ :=
    fun W _ hW => lt_of_le_of_lt (Y.massOn_mono (subset_closure.trans hW.2)) hYU
  obtain ⟨μ, ξ, hμU, -, hμW, hξm, hξb, hrep, hnull⟩ := REP (d + 1) (d + 1) U Y hU hloc
  have hnull' : ∀ E : Set (Euclid (d + 1)), μHE[d + 1] E = 0 → μ E = 0 := hnull hbd
  have hμuniv : μ univ ≤ Y.massOn U := by
    calc μ univ ≤ μ U + μ Uᶜ := by
          rw [← union_compl_self U]; exact measure_union_le _ _
      _ = Y.massOn U := by rw [hμU, add_zero, hμW U hU]
  have hμfin : μ univ < ∞ := lt_of_le_of_lt hμuniv hYU
  have hac : μ ≪ volume := by
    intro E hE
    apply hnull' E
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hE
  obtain ⟨δ, hδ⟩ := Submission.dgoj_exists_det_covector (d + 1)
  obtain ⟨hδn, hspan⟩ := Submission.cbr_ci_pw_td_top_covector_spans (d + 1) δ hδ
  set h : Euclid (d + 1) → ℝ := fun y => ξ y δ
  have hhm : AEStronglyMeasurable h μ :=
    (ContinuousLinearMap.apply ℝ ℝ δ).continuous.comp_aestronglyMeasurable hξm
  have hhb : ∀ᵐ y ∂μ, |h y| ≤ 1 :=
    Eventually.of_forall fun y => (hξb y δ).trans hδn.le
  obtain ⟨u, hui, hul1, hug⟩ :=
    Submission.cbr_ci_pw_td_finite_ac_density (d + 1) μ h hμfin hac hhm hhb
  refine ⟨u, hui.integrableOn, ?_, ?_⟩
  · apply ENNReal.ofReal_le_of_le_toReal
    calc ∫ y in U, |u y| ≤ ∫ y, |u y| :=
          setIntegral_le_integral hui.abs (Eventually.of_forall fun y => abs_nonneg _)
      _ ≤ (μ univ).toReal := hul1
      _ ≤ (Y.massOn U).toReal := ENNReal.toReal_mono hYU.ne hμuniv
  · intro ω
    rw [hrep ω]
    have hpt : ∀ y, ξ y ((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y) =
        (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y
          (fun i => EuclideanSpace.single i (1 : ℝ)) * h y := by
      intro y
      conv_lhs => rw [hspan ((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y)]
      rw [map_smul, smul_eq_mul]
    simp_rw [hpt]
    rw [hug]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hy' : y ∉ tsupport (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) :=
      fun h' => hy (ω.2.2 h')
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp
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

/-- Smooth cutoffs converging pointwise to the indicator of an open set (used to recover the
measure of an open set from the integrals of `C_c^∞` test functions by dominated convergence): for
open `V ⊆ ℝⁿ` there are smooth compactly supported `bⱼ : ℝⁿ → [0, 1]` with `spt bⱼ ⊆ V` and
`bⱼ → 𝟙_V` pointwise.  The compact sets `Kⱼ = {y : dist(y, ℝⁿ \ V) ≥ 1/(j+1)} ∩ B̄(0, j)` lie in
`V` and exhaust it; for `rⱼ > 0` with the closed `2rⱼ`-neighbourhood of `Kⱼ` inside `V`, the
smooth Urysohn lemma gives `bⱼ` with support the open `2rⱼ`-neighbourhood of `Kⱼ` and equal to `1`
exactly on the closed `rⱼ`-neighbourhood. -/
theorem Submission.cbr_ci_pw_noi_smooth_cutoff_seq : ∀ (n : ℕ) (V : Set (Euclid n)), IsOpen V → ∃ b : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (b j)) ∧ (∀ j, HasCompactSupport (b j)) ∧ (∀ j, tsupport (b j) ⊆ V) ∧ (∀ j y, 0 ≤ b j y ∧ b j y ≤ 1) ∧ ∀ y, Tendsto (fun j => b j y) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) y)) := by
  intro n V hV
  -- Step 1: the compact exhaustion `Kⱼ = {y : infEDist y Vᶜ ≥ 1/(j+1)} ∩ B̄(0, j)` of `V`.
  set K : ℕ → Set (Euclid n) := fun j =>
    {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ} ∩ closedBall 0 j
  have hKc : ∀ j, IsCompact (K j) := fun j =>
    (isCompact_closedBall 0 (j : ℝ)).inter_left (isClosed_le continuous_const continuous_infEDist)
  have hKV : ∀ j, K j ⊆ V := by
    intro j y hy
    by_contra hyV
    have h1 : ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := hy.1
    rw [infEDist_zero_of_mem hyV] at h1
    exact (ENNReal.inv_pos.mpr (by simp)).ne' (le_antisymm h1 bot_le)
  have hKev : ∀ y ∈ V, ∀ᶠ j in atTop, y ∈ K j := by
    intro y hy
    have hpos : 0 < infEDist y Vᶜ := by
      rw [infEDist_pos_iff_notMem_closure, hV.isClosed_compl.closure_eq]
      exact fun h => h hy
    have h1 : ∀ᶠ j : ℕ in atTop, ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := by
      have ht : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by simp
      filter_upwards [ht.eventually (gt_mem_nhds hpos)] with j hj using hj.le
    have h2 : ∀ᶠ j : ℕ in atTop, y ∈ closedBall (0 : Euclid n) j := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [mem_closedBall, dist_zero_right]
      exact hN.trans (by exact_mod_cast hj)
    filter_upwards [h1, h2] with j hj1 hj2 using ⟨hj1, hj2⟩
  -- Step 2: radii `rⱼ > 0` with `cthickening (2 rⱼ) Kⱼ ⊆ V`.
  have hr : ∀ j, ∃ r : ℝ, 0 < r ∧ cthickening (2 * r) (K j) ⊆ V := by
    intro j
    obtain ⟨δ, hδ, hsub⟩ := (hKc j).exists_cthickening_subset_open hV (hKV j)
    exact ⟨δ / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  choose r hr0 hrV using hr
  -- Step 3: smooth Urysohn functions, `1` exactly on `cthickening rⱼ Kⱼ`, with support
  -- `thickening (2 rⱼ) Kⱼ`.
  have hb : ∀ j, ∃ f : Euclid n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      support f = thickening (2 * r j) (K j) ∧ ∀ x, x ∈ cthickening (r j) (K j) ↔ f x = 1 :=
    fun j => exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening
      (cthickening_subset_thickening' (by linarith [hr0 j]) (by linarith [hr0 j]) _)
  choose b hbsmooth hbrange hbsupp hbone using hb
  have htsupp : ∀ j, tsupport (b j) ⊆ cthickening (2 * r j) (K j) := by
    intro j
    rw [tsupport, hbsupp]
    exact closure_thickening_subset_cthickening _ _
  refine ⟨b, hbsmooth,
    fun j => (hKc j).cthickening.of_isClosed_subset (isClosed_tsupport _) (htsupp j),
    fun j => (htsupp j).trans (hrV j), fun j y => hbrange j ⟨y, rfl⟩, fun y => ?_⟩
  -- Step 4: `bⱼ y = 1` for large `j` if `y ∈ V`, and `bⱼ y = 0` for all `j` if `y ∉ V`.
  by_cases hy : y ∈ V
  · rw [indicator_of_mem hy]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hKev y hy] with j hj
    exact ((hbone j y).mp (self_subset_cthickening _ hj)).symm
  · rw [indicator_of_notMem hy]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
    by_contra hne
    exact hy ((htsupp j).trans (hrV j) (subset_tsupport _ (Ne.symm hne)))

/-- Finite Borel measures on `ℝⁿ` are determined on an open set `U` by their integrals of smooth
functions with compact support in `U`: if `∫ b dμ = ∫ b dν` for every `C^∞` function `b` with
compact support and `spt b ⊆ U`, then `μ⌞U = ν⌞U`.  For open `O`, smooth cutoffs `bⱼ → 𝟙_{O ∩ U}`
with `0 ≤ bⱼ ≤ 1` and dominated convergence give `μ(O ∩ U) = ν(O ∩ U)`; the open sets form a
π-system generating the Borel σ-algebra. -/
theorem Submission.cbr_ci_pw_noi_restrict_eq_of_smooth_test : ∀ (n : ℕ) (U : Set (Euclid n)) (μ ν : Measure (Euclid n)), IsOpen U → IsFiniteMeasure μ → IsFiniteMeasure ν → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y, b y ∂μ = ∫ y, b y ∂ν) → μ.restrict U = ν.restrict U := by
  intro n U μ ν hU hμ hν htest
  -- Step 1: `μ` and `ν` agree on `O ∩ U` for every open `O`, by testing with smooth cutoffs
  -- `bⱼ → 𝟙_{O ∩ U}` and dominated convergence (bound `1`, integrable as the measures are finite).
  have hopen : ∀ O : Set (Euclid n), IsOpen O → μ (O ∩ U) = ν (O ∩ U) := by
    intro O hO
    obtain ⟨b, hbs, hbc, hbt, hb01, hblim⟩ :=
      Submission.cbr_ci_pw_noi_smooth_cutoff_seq n (O ∩ U) (hO.inter hU)
    have hlim : ∀ ρ : Measure (Euclid n), IsFiniteMeasure ρ →
        Tendsto (fun j => ∫ y, b j y ∂ρ) atTop (𝓝 (ρ.real (O ∩ U))) := by
      intro ρ hρ
      rw [← integral_indicator_one (hO.inter hU).measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun j => (hbs j).continuous.aestronglyMeasurable) (integrable_const 1)
        (fun j => Eventually.of_forall fun y => ?_) (Eventually.of_forall hblim)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hb01 j y).1, (hb01 j y).2]
    have heq : ∀ j, ∫ y, b j y ∂μ = ∫ y, b j y ∂ν := fun j =>
      htest (b j) (hbs j) (hbc j) ((hbt j).trans inter_subset_right)
    have h₁ := hlim μ hμ
    have h₂ := hlim ν hν
    simp_rw [heq] at h₁
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (tendsto_nhds_unique h₁ h₂)
  -- Step 2: `μ⌞U` and `ν⌞U` agree on the π-system of open sets, which generates the Borel
  -- σ-algebra, and on `univ`; finite measures agreeing there are equal.
  refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
  · intro s (hs : IsOpen s)
    rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
    exact hopen s hs
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    simpa using hopen univ isOpen_univ

/-- A smooth-test identity between a density and a push-forward holds on Borel subsets of `U`
(closure theorem argument, Simon Ch. 6, as used for 7.2.4): if `∫_U b u dLⁿ = ∫ (b ∘ q) h dσ` for
every smooth `b` with compact support in `U`, then `∫_B u dLⁿ = ∫_{q⁻¹ B} h dσ` for every Borel
`B ⊆ U`.  The finite measures `μ₁ = u⁺ Lⁿ⌞U + q_♯(h⁻ σ)` and `μ₂ = u⁻ Lⁿ⌞U + q_♯(h⁺ σ)` have the
same integral against every such `b`, hence agree on `U`; evaluating them on `B` and splitting `u`
and `h` into positive and negative parts gives the identity. -/
theorem Submission.cbr_ci_pw_noi_setIntegral_eq_preimage : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ), IsOpen U → Measurable q → IntegrableOn u U → Integrable h σ → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → ∫ y in B, u y = ∫ x in q ⁻¹' B, h x ∂σ := by
  intro P n U u σ q h hU hq hu hh htest B hB hBU
  -- Step 1: the finite measures `λ± = u± Lⁿ⌞U` and `m± = q_♯(h± σ)`.
  set lp : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (u y)
    with hlp
  set lm : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (-u y)
    with hlm
  set mp : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (h x)).map q with hmp
  set mm : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (-h x)).map q with hmm
  have hlpf : IsFiniteMeasure lp := isFiniteMeasure_withDensity_ofReal hu.2
  have hlmf : IsFiniteMeasure lm := isFiniteMeasure_withDensity_ofReal hu.neg.2
  have hmpf : IsFiniteMeasure mp := by
    have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (h x)) :=
      isFiniteMeasure_withDensity_ofReal hh.2
    exact Measure.isFiniteMeasure_map _ _
  have hmmf : IsFiniteMeasure mm := by
    have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (-h x)) :=
      isFiniteMeasure_withDensity_ofReal hh.neg.2
    exact Measure.isFiniteMeasure_map _ _
  -- Step 2: integrals of a function `b` against `λ±` and `m±`.
  have hlam : ∀ (f : Euclid n → ℝ) (b : Euclid n → ℝ), IntegrableOn f U →
      ∫ y, b y ∂((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) =
        ∫ y in U, max (f y) 0 * b y := by
    intro f b hf
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hpush : ∀ (g : Euclid P → ℝ) (b : Euclid n → ℝ), Integrable g σ → Continuous b →
      ∫ y, b y ∂((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) =
        ∫ x, max (g x) 0 * b (q x) ∂σ := by
    intro g b hg hb
    rw [integral_map hq.aemeasurable hb.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  -- Step 3: `λ₊ + m₋` and `λ₋ + m₊` have the same integral against every test function, since
  -- `u = u⁺ - u⁻`, `h = h⁺ - h⁻` and `∫_U b u = ∫ (b ∘ q) h dσ`.
  have hkey : ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U →
      ∫ y, b y ∂(lp + mm) = ∫ y, b y ∂(lm + mp) := by
    intro b hb hbc hbU
    have hbcont : Continuous b := hb.continuous
    obtain ⟨C, hC⟩ := hbcont.bounded_above_of_compact_support hbc
    have hbm : AEStronglyMeasurable b (volume.restrict U) := hbcont.aestronglyMeasurable
    have hbqm : AEStronglyMeasurable (fun x => b (q x)) σ :=
      (hbcont.measurable.comp hq).aestronglyMeasurable
    rw [integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
        (hbcont.integrable_of_hasCompactSupport hbc),
      integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
        (hbcont.integrable_of_hasCompactSupport hbc),
      hlam u b hu, hlam (fun y => -u y) b hu.neg, hpush h b hh hbcont,
      hpush (fun x => -h x) b hh.neg hbcont]
    have I1 : (∫ y in U, max (u y) 0 * b y) - ∫ y in U, max (-u y) 0 * b y =
        ∫ y in U, b y * u y := by
      have hsub := integral_sub (hu.pos_part.mul_bdd hbm (Eventually.of_forall hC))
        (hu.neg_part.mul_bdd hbm (Eventually.of_forall hC))
      refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
      simp only
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
    have I2 : ∫ x, max (h x) 0 * b (q x) ∂σ - ∫ x, max (-h x) 0 * b (q x) ∂σ =
        ∫ x, b (q x) * h x ∂σ := by
      have hsub := integral_sub (hh.pos_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
        (hh.neg_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
      refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
      simp only
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
    have := htest b hb hbc hbU
    linarith
  -- Step 4: uniqueness, so the two measures agree on the measurable subset `B` of `U`.
  have hres := Submission.cbr_ci_pw_noi_restrict_eq_of_smooth_test n U (lp + mm) (lm + mp) hU
    inferInstance inferInstance hkey
  have hBeq : (lp + mm) B = (lm + mp) B := by
    have := congrArg (fun μ : Measure (Euclid n) => μ B) hres
    simpa only [Measure.restrict_apply hB, inter_eq_left.mpr hBU] using this
  -- Step 5: `λ±(B) = ∫⁻_B (±u)⁺` and `m±(B) = ∫⁻_{q⁻¹ B} (±h)⁺ dσ`.
  have hlB : ∀ f : Euclid n → ℝ, ((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) B =
      ∫⁻ y in B, ENNReal.ofReal (f y) := by
    intro f
    rw [withDensity_apply _ hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBU]
  have hmB : ∀ g : Euclid P → ℝ, ((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) B =
      ∫⁻ x in q ⁻¹' B, ENNReal.ofReal (g x) ∂σ := by
    intro g
    rw [Measure.map_apply hq hB, withDensity_apply _ (hq hB)]
  -- Step 6: all four values are finite, so the identity of Step 4 passes to real numbers, and
  -- both set integrals are differences of positive and negative parts.
  rw [Measure.add_apply, Measure.add_apply] at hBeq
  have hreal : (lp B).toReal + (mm B).toReal = (lm B).toReal + (mp B).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hBeq]
  have hL : ∫ y in B, u y = (lp B).toReal - (lm B).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hu.mono_set hBU), hlp, hlm, hlB, hlB]
  have hR : ∫ x in q ⁻¹' B, h x ∂σ = (mp B).toReal - (mm B).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh.integrableOn, hmp, hmm, hmB, hmB]
  rw [hL, hR]
  linarith

/-- Null-off-image bound for the density `u` (step 10 of the weight-at-least-one argument): if
`∫_U b u = ∫ (b ∘ q) h dσ` for every `b ∈ C_c^∞(U)` and `σ` is carried by `A`, then `u = 0`
`Lⁿ`-a.e. on `U \ q(A)`, i.e. `Lⁿ(B ∩ {u ≠ 0}) ≤ Lⁿ(B ∩ q(A))` for measurable `B ⊆ U`.  With
`E` a measurable hull of `q(A)`, every measurable `B' ⊆ U \ E` has `σ`-null preimage `q⁻¹(B')`,
so `∫_{B'} u = ∫_{q⁻¹(B')} h dσ = 0` (`cbr_ci_pw_noi_setIntegral_eq_preimage`); hence `u = 0`
a.e. on `U \ E` and `Lⁿ(B ∩ {u ≠ 0}) ≤ Lⁿ(B ∩ E) = Lⁿ(B ∩ q(A))`. -/
theorem Submission.cbr_ci_pw_density_null_off_image : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ) (A : Set (Euclid P)), IsOpen U → Continuous q → IntegrableOn u U → σ univ < ∞ → Integrable h σ → σ Aᶜ = 0 → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → volume (B ∩ {y | u y ≠ 0}) ≤ volume (B ∩ q '' A) := by
  intro P n U u σ q h A hU hq hu _hσ hh hA htest B hB hBU
  -- the measurable hull `E` of `q '' A`
  set E : Set (Euclid n) := toMeasurable volume (q '' A) with hE
  have hUE : MeasurableSet (U \ E) := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  -- `∫_s u = 0` for measurable `s ⊆ U \ E`, because `q ⁻¹' s ⊆ Aᶜ` is `σ`-null
  have hzero : ∀ s : Set (Euclid n), MeasurableSet s → s ⊆ U \ E → ∫ y in s, u y = 0 := by
    intro s hs hsUE
    rw [Submission.cbr_ci_pw_noi_setIntegral_eq_preimage P n U u σ q h hU hq.measurable hu hh
      htest s hs (hsUE.trans sdiff_subset)]
    refine setIntegral_measure_zero _ (measure_mono_null ?_ hA)
    intro x hx hxA
    exact (hsUE hx).2 (subset_toMeasurable _ _ ⟨x, hxA, rfl⟩)
  -- hence `u = 0` a.e. on `U \ E`
  have hae : u =ᵐ[volume.restrict (U \ E)] 0 :=
    (hu.mono_set sdiff_subset).ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by
      rw [Measure.restrict_restrict hs]
      exact hzero _ (hs.inter hUE) inter_subset_right
  have hnull : volume ({y | u y ≠ 0} ∩ (U \ E)) = 0 := by
    rw [← Measure.restrict_apply' hUE]
    exact hae
  -- `B ∩ {u ≠ 0} ⊆ (B ∩ E) ∪ ({u ≠ 0} ∩ (U \ E))` and `Lⁿ(B ∩ E) = Lⁿ(B ∩ q '' A)`
  calc volume (B ∩ {y | u y ≠ 0})
      ≤ volume (B ∩ E ∪ {y | u y ≠ 0} ∩ (U \ E)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyE : y ∈ E
        · exact Or.inl ⟨hy.1, hyE⟩
        · exact Or.inr ⟨hy.2, hBU hy.1, hyE⟩
    _ ≤ volume (B ∩ E) + volume ({y | u y ≠ 0} ∩ (U \ E)) := measure_union_le _ _
    _ = volume (B ∩ q '' A) := by
        rw [hnull, add_zero, inter_comm, hE,
          Measure.measure_toMeasurable_inter_of_sFinite hB, inter_comm]
/-- **The interior-product covector `ι_z(dy)` on `ℝ^{d+1}`** (used for the `d`-form `f · ι_z(dy)`,
whose exterior derivative is `(∂_z f) dy`, in White's projection argument for the closure theorem
behind Simon 7.2.4; cf. the forms `ωⱼ` in the proof of Simon 6.2.34).  For `z ∈ ℝ^{d+1}` there is
a continuous alternating `d`-form `ε` on `ℝ^{d+1}` with `ε(e₀, …, êᵢ, …, e_d) = (−1)ⁱ zᵢ`:
`ε(u₁, …, u_d) = det [z | u₁ | ⋯ | u_d] = δ(z, u₁, …, u_d)` for the standard determinant form `δ`. -/
theorem Submission.cbr_ci_pw_ipf_coord_covector : ∀ (d : ℕ) (z : Euclid (d + 1)), ∃ ε : Covector (Euclid (d + 1)) d, ∀ i : Fin (d + 1), ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ))) = (-1 : ℝ) ^ (i : ℕ) * z i := by
  intro d z
  classical
  -- The standard basis `b l = e_l` and its determinant `δ₀ c = det (c l r)_{r,l}`.
  let b : Module.Basis (Fin (d + 1)) ℝ (Euclid (d + 1)) :=
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
  have hdet : ∀ c : Fin (d + 1) → Euclid (d + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  -- `δ₀` is continuous (entrywise continuous matrix, then `det`), so it is a covector `δ`.
  have hcont : Continuous (fun c : Fin (d + 1) → Euclid (d + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (d + 1)) (d + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  -- `ε = δ.curryLeft z`, so `ε u = det M(u)` with columns `z, u₀, …, u_{d-1}`; expand along
  -- column `0`: `det M(u) = Σ_r (−1)ʳ z_r det N_r` with minors `N_r`.
  refine ⟨δ.curryLeft z, fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, hdet, Matrix.det_succ_column_zero,
    Finset.sum_eq_single i]
  · -- `r = i`: `(N_i)_{a,k} = (e_{i.succAbove k})_{i.succAbove a} = [a = k]`, so `N_i = 1`.
    have h1 : (Matrix.of fun r l => (Matrix.vecCons z (i.removeNth fun l =>
        EuclideanSpace.single l (1 : ℝ)) : Fin (d + 1) → Euclid (d + 1)) l r).submatrix
          i.succAbove Fin.succ = 1 := by
      ext a k
      simp [Matrix.one_apply, Fin.removeNth_apply]
    rw [h1, Matrix.det_one]
    simp
  · -- `r ≠ i`: row `a₀` of `N_r`, where `r.succAbove a₀ = i`, is `(e_{i.succAbove k})_i = 0`.
    intro r _ hri
    obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq (x := i) (y := r) (Ne.symm hri)
    rw [Matrix.det_eq_zero_of_row_eq_zero a₀, mul_zero]
    intro k
    simp [Fin.removeNth_apply, ha₀]
  · intro h
    exact absurd (Finset.mem_univ i) h
/-- **Coefficient norm of the interior-product covector** (used for `ε = ι_z(dy)` in the closure
and boundary-rectifiability step of the compactness theorem, Simon 7.2.4).  If the `d`-covector `ε`
on `ℝ^{d+1}` takes the value `(−1)ⁱ zᵢ` on `(e₀, …, êᵢ, …, e_d)`, then its Euclidean coefficient
norm (Simon (6.1.15)) is `|z|`: the strictly increasing `I : Fin d → Fin (d + 1)` are exactly the
maps `i.succAbove`, so the coefficients of `ε` are the `(−1)ⁱ zᵢ`. -/
theorem Submission.cbr_ci_pw_ipf_covector_norm_eq : ∀ (d : ℕ) (z : Euclid (d + 1)) (ε : Covector (Euclid (d + 1)) d), (∀ i : Fin (d + 1), ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ))) = (-1 : ℝ) ^ (i : ℕ) * z i) → covectorEuclideanNorm ε = ‖z‖ := by
  intro d z ε hε
  have hI : ∀ I : Fin d → Fin (d + 1), StrictMono I → ∃ i : Fin (d + 1), i.succAbove = I := by
    intro I hI
    have hns : ¬Surjective I := fun h => by
      simpa using Fintype.card_le_of_surjective I h
    obtain ⟨i, hi⟩ := not_forall.mp hns
    have hcard : (Finset.univ.erase i).card = d := by simp
    refine ⟨i, ?_⟩
    rw [Finset.orderEmbOfFin_unique hcard (f := I)
        (fun k => Finset.mem_erase.2 ⟨fun h => hi ⟨k, h⟩, Finset.mem_univ _⟩) hI,
      Finset.orderEmbOfFin_unique hcard (f := i.succAbove)
        (fun k => Finset.mem_erase.2 ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩)
        (Fin.strictMono_succAbove i)]
  rw [covectorEuclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  rw [← Finset.sum_subset
      (Finset.subset_univ (Finset.univ.image fun i : Fin (d + 1) => i.succAbove)) ?_,
    Finset.sum_image fun i _ j _ h => Fin.succAbove_left_injective h]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hb : (fun k => EuclideanSpace.basisFun (Fin (d + 1)) ℝ (i.succAbove k)) =
        i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ)) := by
      funext k
      simp [Fin.removeNth]
    rw [ite_eq_left (Fin.strictMono_succAbove i), hb, hε i, Real.norm_eq_abs, sq_abs, mul_pow,
      pow_right_comm, neg_one_sq, one_pow, one_mul]
  · intro I _ hIm
    refine ite_eq_right fun hmono => ?_
    obtain ⟨i, rfl⟩ := hI I hmono
    exact hIm (Finset.mem_image_of_mem _ (Finset.mem_univ i))
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

/-- **The interior product `ι_z(dy)` as a constant `d`-form on `ℝ^{d+1}`** (the forms
`f · Σⱼ zⱼ εⱼ` in the BV estimate of the closure argument for Simon 7.2.4; cf. the forms `ωⱼ` in
the proof of Simon Ch. 6, 2.34).  For `z ∈ ℝ^{d+1}` the covector
`ε(u₁, …, u_d) = det[z | u₁ | ⋯ | u_d]` has `ε(e₀, …, êᵢ, …, e_d) = (−1)ⁱ zᵢ` and `|ε| = |z|`,
and `d(f ε) = df ∧ ε` gives
`d(f ε)(y)(e₀, …, e_d) = Σᵢ (−1)ⁱ Df(y)eᵢ · (−1)ⁱ zᵢ = Df(y)(Σᵢ zᵢ eᵢ) = Df(y) z`. -/
theorem Submission.cbr_ci_pw_interior_product_form : ∀ (d : ℕ) (z : Euclid (d + 1)), ∃ ε : Covector (Euclid (d + 1)) d, covectorEuclideanNorm ε ≤ ‖z‖ ∧ ∀ (f : Euclid (d + 1) → ℝ) (y : Euclid (d + 1)), DifferentiableAt ℝ f y → exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z := by
  intro d z
  -- steps 1–2: `ε = ι_z(dy)`, with `ε(i.removeNth e) = (−1)ⁱ zᵢ`
  obtain ⟨ε, hε⟩ := Submission.cbr_ci_pw_ipf_coord_covector d z
  -- step 3: `|ε| = ‖z‖`
  refine ⟨ε, (Submission.cbr_ci_pw_ipf_covector_norm_eq d z ε hε).le, fun f y hf => ?_⟩
  -- step 4: `d(f ε)(y)(e) = Σᵢ (−1)ⁱ Df(y)eᵢ · ε(i.removeNth e)`
  rw [Submission.dgcr_bwd_extDeriv_smul_const (d + 1) d f ε y _ hf]
  -- `(−1)ⁱ (−1)ⁱ = 1`, so the `i`-th term is `zᵢ Df(y)eᵢ`
  have hterm : ∀ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) * ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ)))) = z i * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have hsq : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hε i]
    linear_combination (z i * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) * hsq
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- `z = Σᵢ zᵢ eᵢ` and `Df(y)` is linear
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, smul_eq_mul]
/-- **Translated test functions** (mollified weights in the closure theorem behind Simon 7.2.4):
if `φ` is smooth with `tsupport φ ⊆ B_s(0)`, `s < R` and `x ∈ B̄_R(0)`, then `b(y) = φ(x − y)` is
smooth with compact support in `B_{2R}(0)` and `∫ b = ∫ φ`.  `tsupport φ` is closed in the compact
`B̄_s(0)`; `y ↦ x − y` is the homeomorphism `Homeomorph.subLeft x`, so `tsupport b` is the preimage
of `tsupport φ`, on which `‖y‖ ≤ ‖x‖ + ‖x − y‖ < R + s < 2R`; and Lebesgue measure is invariant
under `y ↦ x − y`. -/
theorem Submission.cbr_ci_pw_mu_translate_admissible : ∀ (n : ℕ) (R s : ℝ) (φ : Euclid n → ℝ) (x : Euclid n), s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → x ∈ closedBall 0 R → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (x - y)) ∧ HasCompactSupport (fun y => φ (x - y)) ∧ tsupport (fun y => φ (x - y)) ⊆ ball 0 (2 * R) ∧ ∫ y, φ (x - y) = ∫ y, φ y := by
  intro n R s φ x hsR hφ hsupp hx
  -- `φ` has compact support: `tsupport φ` is closed in the compact `closedBall 0 s`
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hsupp.trans ball_subset_closedBall)
  -- `b = φ ∘ e` for the homeomorphism `e = (x - ·)`
  have hb : (fun y => φ (x - y)) = φ ∘ Homeomorph.subLeft x := rfl
  refine ⟨hφ.comp (contDiff_const.sub contDiff_id), hb ▸ hφc.comp_homeomorph _, ?_,
    integral_sub_left_eq_self φ volume x⟩
  intro y hy
  have hxy : x - y ∈ tsupport φ := by
    rw [hb, tsupport_comp_eq_preimage] at hy
    exact hy
  have hxy' : ‖x - y‖ < s := mem_ball_zero_iff.mp (hsupp hxy)
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  rw [mem_ball_zero_iff]
  calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
    _ < 2 * R := by linarith
/-- **Mollification is Lipschitz, with constant `∝ ∫_S |v|`**: for `φ ∈ C^∞_c(ℝⁿ)` there is
`L ≥ 0` such that, for every `S ⊆ ℝⁿ`, every `v` integrable on `S` and all `x, x'`,
`|∫_S v(y)φ(x − y) dy − ∫_S v(y)φ(x' − y) dy| ≤ L (∫_S |v|) |x − x'|`.  `φ` is `C¹` with compact
support, hence `L`-Lipschitz, and bounded, so both integrands are integrable on `S` and the
difference is `|∫_S v(y)(φ(x − y) − φ(x' − y)) dy| ≤ ∫_S |v(y)| L |x − x'| dy`. -/
theorem Submission.cbr_ci_pw_mu_conv_lipschitz : ∀ (n : ℕ) (φ : Euclid n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Set (Euclid n)) (v : Euclid n → ℝ), IntegrableOn v S → ∀ x x' : Euclid n, |(∫ y in S, v y * φ (x - y)) - ∫ y in S, v y * φ (x' - y)| ≤ L * (∫ y in S, |v y|) * dist x x' := by
  intro n φ hφ hφc
  obtain ⟨C, hC⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  refine ⟨C, C.coe_nonneg, fun S v hv x x' => ?_⟩
  have hint : ∀ z : Euclid n, IntegrableOn (fun y => v y * φ (z - y)) S := fun z =>
    Integrable.mul_bdd hv
      (hφ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => hM (z - y))
  rw [← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y in S, v y * φ (x - y) - v y * φ (x' - y)‖
      ≤ ∫ y in S, |v y| * (C * dist x x') := by
        refine norm_integral_le_of_norm_le (hv.abs.mul_const _) (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        gcongr
        rw [← Real.dist_eq]
        simpa [dist_sub_right] using hC.dist_le_mul (x - y) (x' - y)
    _ = C * (∫ y in S, |v y|) * dist x x' := by
        rw [integral_mul_const]
        ring
/-- Pointwise convergence to a constant plus an eventual uniform Lipschitz bound on a compact set
gives uniform convergence (the ε/3 argument): cover `K` by finitely many `η`-balls centred in `K`,
with `max L 0 * η < ε / 3`; eventually every centre is `ε / 3`-close to `a`, and each `x ∈ K` lies
within `η` of a centre. -/
theorem Submission.cbr_ci_pw_mu_uniform_of_equilipschitz : ∀ (n : ℕ) (K : Set (Euclid n)) (F : ℕ → Euclid n → ℝ) (a L : ℝ), IsCompact K → (∀ x ∈ K, Tendsto (fun k => F k x) atTop (𝓝 a)) → (∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K, |F k x - F k x'| ≤ L * dist x x') → TendstoUniformlyOn F (fun _ => a) atTop K := by
  intro n K F a L hK hpt hL
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hM0 : 0 ≤ max L 0 := le_max_right L 0
  have hη : 0 < ε / (3 * (max L 0 + 1)) := by positivity
  have hMη : max L 0 * (ε / (3 * (max L 0 + 1))) < ε / 3 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨t, htK, ht, hcover⟩ := hK.finite_cover_balls hη
  have hnet : ∀ᶠ k in atTop, ∀ z ∈ t, |F k z - a| < ε / 3 :=
    ht.eventually_all.2 fun z hz => by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.1 (hpt z (htK hz)) (ε / 3) (by positivity)
  filter_upwards [hnet, hL] with k hk hkL x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover hx)
  have hzx : |F k z - F k x| < ε / 3 :=
    calc |F k z - F k x| ≤ L * dist z x := hkL z (htK hz) x hx
      _ ≤ max L 0 * dist z x := mul_le_mul_of_nonneg_right (le_max_left L 0) dist_nonneg
      _ ≤ max L 0 * (ε / (3 * (max L 0 + 1))) :=
        mul_le_mul_of_nonneg_left (mem_ball'.1 hxz).le hM0
      _ < ε / 3 := hMη
  rw [Real.dist_eq]
  have htri := abs_sub_le a (F k z) (F k x)
  rw [abs_sub_comm a (F k z)] at htri
  linarith [hk z hz]

/-- **Simon 7.2.4**, uniform convergence of mollified weak limits (step 11(a) of the weight
lower bound `α ≥ 1`): if the `u_k` are eventually `L¹`-bounded by `Λ` on `B_{2R}(0)` and
`∫_{B_{2R}(0)} u_k b → c ∫ b` for every test function `b` with `spt b ⊆ B_{2R}(0)`, then for a test
function `φ` with `spt φ ⊆ B_s(0)`, `s < R`, the mollifications
`w_k(x) = ∫_{B_{2R}(0)} u_k(y) φ(x − y) dy` converge to `c ∫ φ` uniformly on `B̄_R(0)`.  For
`x ∈ B̄_R(0)` the translate `φ(x − ·)` is such a test function with the same integral
(`cbr_ci_pw_mu_translate_admissible`), so `w_k(x) → c ∫ φ`; the `w_k` are eventually
`LΛ`-Lipschitz (`cbr_ci_pw_mu_conv_lipschitz`); and pointwise convergence with an eventual
uniform Lipschitz bound on the compact `B̄_R(0)` is uniform
(`cbr_ci_pw_mu_uniform_of_equilipschitz`). -/
theorem Submission.cbr_ci_pw_mollified_tendstoUniformlyOn : ∀ (n : ℕ) (R s c Λ : ℝ) (φ : Euclid n → ℝ) (u : ℕ → Euclid n → ℝ), 0 < R → 0 < s → s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ ball 0 (2 * R) → Tendsto (fun k => ∫ y in ball 0 (2 * R), u k y * b y) atTop (𝓝 (c * ∫ y, b y))) → TendstoUniformlyOn (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (fun _ => c * ∫ y, φ y) atTop (closedBall 0 R) := by
  intro n R s c Λ φ u _ _ hsR hφ hφs hu hΛ hconv
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  obtain ⟨L, hL, hLip⟩ := Submission.cbr_ci_pw_mu_conv_lipschitz n φ hφ hφc
  refine Submission.cbr_ci_pw_mu_uniform_of_equilipschitz n (closedBall 0 R)
    (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (c * ∫ y, φ y) (L * Λ)
    (isCompact_closedBall 0 R) (fun x hx => ?_) ?_
  · obtain ⟨hb, hbc, hbs, hbi⟩ :=
      Submission.cbr_ci_pw_mu_translate_admissible n R s φ x hsR hφ hφs hx
    have h := hconv (fun y => φ (x - y)) hb hbc hbs
    rwa [hbi] at h
  · filter_upwards [hΛ] with k hk x _ x' _
    exact (hLip (ball 0 (2 * R)) (u k) (hu k) x x').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hL) dist_nonneg)
/-- **Translation bound for smooth tests** (steps 1(b)–(d) of the BV estimate): let `u` be
integrable on `B = B_ρ(0) ⊆ ℝⁿ` with `|∫_B u(y) Df(y)(z) dy| ≤ V ‖z‖ K` for every smooth compactly
supported `f` with `tsupport f ⊆ B` and `|f| ≤ K`.  If `g` is smooth with compact support,
`tsupport g ⊆ B_{ρ−‖v‖}(0)` and `|g| ≤ M`, then `|∫_B u(y) (g(y + v) − g(y)) dy| ≤ V ‖v‖ M`.  By
the fundamental theorem of calculus along `τ ↦ y + τv` and Fubini on `(0, 1] × B` (dominated by
`K_D ‖v‖ |u|`, where `‖Dg‖ ≤ K_D`), the left side is `∫₀¹ ∫_B u(y) Dg(y + τv)(v) dy dτ`; for
`τ ∈ (0, 1]` the inner integral is bounded by the hypothesis applied to the translate `g(· + τv)`,
whose support stays in `B`. -/
theorem Submission.cbr_ci_pw_bv_translate_test : ∀ (n : ℕ) (ρ V M : ℝ) (u g : Euclid n → ℝ) (v : Euclid n), IntegrableOn u (ball 0 ρ) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (K : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 ρ → (∀ y, |f y| ≤ K) → |∫ y in ball 0 ρ, u y * fderiv ℝ f y z| ≤ V * ‖z‖ * K) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (ρ - ‖v‖) → (∀ y, |g y| ≤ M) → |∫ y in ball 0 ρ, u y * (g (y + v) - g y)| ≤ V * ‖v‖ * M := by
  intro n ρ V M u g v hu hvar hg hgc hgs hgb
  -- Step 1: `Dg` is continuous with compact support, hence bounded by some `K_D`
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hDcs : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  obtain ⟨KD, hKD⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 2: FTC along the segment `τ ↦ y + τv`
  have hFTC : ∀ y, g (y + v) - g y = ∫ τ in (0:ℝ)..1, fderiv ℝ g (y + τ • v) v := by
    intro y
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1,
        HasDerivAt (fun τ : ℝ => g (y + τ • v)) (fderiv ℝ g (y + τ • v) v) τ := by
      intro τ _
      have h1 : HasDerivAt (fun τ : ℝ => y + τ • v) v τ := by
        simpa using ((hasDerivAt_id τ).smul_const v).const_add y
      exact (hgd (y + τ • v)).hasFDerivAt.comp_hasDerivAt τ h1
    have hint : IntervalIntegrable (fun τ : ℝ => fderiv ℝ g (y + τ • v) v) volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact (hDc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  -- Step 3: `Φ(τ, y) = u(y) Dg(y + τv)(v)` is integrable on `(0, 1] × B`, dominated by
  -- `K_D ‖v‖ |u(y)|`
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hInt : Integrable (uncurry fun (τ : ℝ) (y : Euclid n) => u y * fderiv ℝ g (y + τ • v) v)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (ball (0 : Euclid n) ρ))) := by
    have hdom : Integrable (fun p : ℝ × Euclid n => (KD * ‖v‖) * ‖u p.2‖)
        ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (ball (0 : Euclid n) ρ))) :=
      (hu.norm.const_mul (KD * ‖v‖)).comp_snd _
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hu.aestronglyMeasurable.comp_snd).mul
        ((hDc.comp (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
          continuous_const).aestronglyMeasurable
    · simp only [uncurry, norm_mul]
      have h1 : ‖fderiv ℝ g (p.2 + p.1 • v) v‖ ≤ KD * ‖v‖ :=
        ((fderiv ℝ g (p.2 + p.1 • v)).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hKD _) (norm_nonneg v))
      calc ‖u p.2‖ * ‖fderiv ℝ g (p.2 + p.1 • v) v‖ ≤ ‖u p.2‖ * (KD * ‖v‖) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = KD * ‖v‖ * ‖u p.2‖ := by ring
  -- Step 4: Fubini, `∫_B u (g(· + v) − g) = ∫₀¹ X(τ) dτ` with `X(τ) = ∫_B u(y) Dg(y + τv)(v) dy`
  have hLHS : ∫ y in ball (0 : Euclid n) ρ, u y * (g (y + v) - g y)
      = ∫ τ in (0:ℝ)..1, ∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v := by
    simp_rw [hFTC, ← intervalIntegral.integral_const_mul]
    exact (intervalIntegral_integral_swap hInt).symm
  -- Step 5: `|X(τ)| ≤ V ‖v‖ M` for `τ ∈ (0, 1]`, by the hypothesis for `f_τ = g(· + τv)`
  have hX : ∀ τ ∈ Set.uIoc (0:ℝ) 1,
      ‖∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v‖ ≤ V * ‖v‖ * M := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    set f : Euclid n → ℝ := fun y => g (y + τ • v) with hf
    have hfs : ContDiff ℝ (⊤ : ℕ∞) f := hg.comp (contDiff_id.add contDiff_const)
    have hfc : HasCompactSupport f := hgc.comp_homeomorph (Homeomorph.addRight (τ • v))
    have hft : tsupport f ⊆ ball 0 ρ := by
      intro y hy
      have : f = g ∘ (Homeomorph.addRight (τ • v)) := rfl
      rw [this, tsupport_comp_eq_preimage] at hy
      have hy' := mem_ball_zero_iff.1 (hgs hy)
      simp only [Homeomorph.coe_addRight] at hy'
      rw [mem_ball_zero_iff]
      have h1 : ‖y‖ ≤ ‖y + τ • v‖ + ‖τ • v‖ := by
        calc ‖y‖ = ‖(y + τ • v) - τ • v‖ := by simp
          _ ≤ ‖y + τ • v‖ + ‖τ • v‖ := norm_sub_le _ _
      have h2 : ‖τ • v‖ ≤ ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
      linarith
    have hfb : ∀ y, |f y| ≤ M := fun y => hgb _
    have := hvar f v M hfs hfc hft hfb
    rw [Real.norm_eq_abs]
    simpa [hf, fderiv_comp_add_right] using this
  -- Step 6: integrate the bound of step 5 over `(0, 1]`
  rw [hLHS, ← Real.norm_eq_abs]
  calc ‖∫ τ in (0:ℝ)..1, ∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v‖
      ≤ V * ‖v‖ * M * |1 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hX
    _ = V * ‖v‖ * M := by simp
/-- **Pairing identity** (steps 1(a) and 1(c) of the BV estimate): let `S ⊆ ℝⁿ` be measurable,
`u` integrable on `S`, `φ` continuous with compact support and `∫ φ = 1`, and `g` continuous with
compact support and `g = 0` off `S`.  Then, with `w(x) = ∫_S u(y) φ(x − y) dy`,
`∫ (u − w) g = ∫ φ(z) ∫_S u(y) (g(y) − g(y + z)) dy dz`.  With `ū = 1_S u`, two applications of
Fubini (dominated by multiples of `|g(x)| |ū(y)|` and `|φ(z)| |ū(y)|`), translation invariance and
`∫ φ = 1` reduce both sides to `∫ ū g − ∫ ū(y) ∫ φ(z) g(z + y) dz dy`. -/
theorem Submission.cbr_ci_pw_bv_pairing_identity : ∀ (n : ℕ) (S : Set (Euclid n)) (φ u g : Euclid n → ℝ), MeasurableSet S → Continuous φ → HasCompactSupport φ → ∫ y, φ y = 1 → IntegrableOn u S → Continuous g → HasCompactSupport g → (∀ x, x ∉ S → g x = 0) → ∫ x, (u x - ∫ y in S, u y * φ (x - y)) * g x = ∫ z, φ z * ∫ y in S, u y * (g y - g (y + z)) := by
  intro n S φ u g hS hφ hφc hφ1 hu hg hgc hgS
  -- Step 1: `ū = 1_S u` is integrable; `φ` and `g` are integrable and bounded
  set ub : Euclid n → ℝ := S.indicator u with hub
  have hubi : Integrable ub := (integrable_indicator_iff hS).2 hu
  obtain ⟨Kφ, hKφ⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨Kg, hKg⟩ := hg.bounded_above_of_compact_support hgc
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  -- Step 2: integrals over `S` become integrals of `ū`, and `(u − w) g = ū g − w g`
  have hw : ∀ x, ∫ y in S, u y * φ (x - y) = ∫ y, ub y * φ (x - y) := by
    intro x
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hI : ∀ z, ∫ y in S, u y * (g y - g (y + z)) = ∫ y, ub y * (g y - g (y + z)) := by
    intro z
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hL : ∀ x, (u x - ∫ y in S, u y * φ (x - y)) * g x
      = ub x * g x - (∫ y, ub y * φ (x - y)) * g x := by
    intro x
    rw [hw x, sub_mul]
    congr 1
    by_cases hx : x ∈ S
    · simp [hub, Set.indicator_of_mem hx]
    · simp [hgS x hx]
  simp_rw [hL, hI]
  have hubg : Integrable (fun x => ub x * g x) :=
    hubi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hKg)
  -- Step 3: first Fubini, for `F(x, y) = ū(y) φ(x − y) g(x)`
  have hFi : Integrable (uncurry fun x y => ub y * φ (x - y) * g x) (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => Kφ * (‖g p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hgi.norm.mul_prod hubi.norm).const_mul Kφ
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hubi.aestronglyMeasurable.comp_snd).mul
        ((hφ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)).mul
        ((hg.comp continuous_fst).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 := hKφ (p.1 - p.2)
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (g p.1)
      calc ‖ub p.2‖ * ‖φ (p.1 - p.2)‖ * ‖g p.1‖ = ‖φ (p.1 - p.2)‖ * (‖g p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ Kφ * (‖g p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  -- translation invariance of Lebesgue measure: `∫ φ(x − y) g(x) dx = ∫ φ(z) g(z + y) dz`
  have htr : ∀ y, ∫ x, φ (x - y) * g x = ∫ z, φ z * g (z + y) := fun y => by
    simpa [sub_add_cancel] using integral_sub_right_eq_self
      (μ := (volume : Measure (Euclid n))) (fun z => φ z * g (z + y)) y
  have hwg : ∀ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * φ (x - y) * g x := fun x =>
    (integral_mul_const _ _).symm
  have hwgi : Integrable (fun x => (∫ y, ub y * φ (x - y)) * g x) := by
    simp_rw [hwg]; exact hFi.integral_prod_left
  have key1 : ∫ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * ∫ z, φ z * g (z + y) := by
    simp_rw [hwg]
    rw [integral_integral_swap hFi]
    congr 1; funext y
    simp_rw [mul_assoc]
    rw [integral_const_mul, htr]
  have hconv : Integrable (fun y => ub y * ∫ z, φ z * g (z + y)) := by
    refine (hFi.integral_prod_right).congr (Eventually.of_forall fun y => ?_)
    simp only [uncurry]
    simp_rw [mul_assoc]
    rw [integral_const_mul, htr]
  -- Step 4: `∫ φ(z) (g(y) − g(y + z)) dz = g(y) − ∫ φ(z) g(z + y) dz`, by `∫ φ = 1`
  have hinner : ∀ y, ∫ z, φ z * (g y - g (y + z)) = g y - ∫ z, φ z * g (z + y) := by
    intro y
    have hc : Integrable (fun z => φ z * g y) := hφi.mul_const _
    have hs : Integrable (fun z => φ z * g (z + y)) :=
      hφi.mul_bdd (hg.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun z => hKg _)
    simp_rw [mul_sub]
    rw [integral_sub hc (by simpa [add_comm] using hs), integral_mul_const, hφ1, one_mul]
    simp_rw [add_comm y]
  -- Step 5: second Fubini, for `H(z, y) = φ(z) ū(y) (g(y) − g(y + z))`
  have hHi : Integrable (uncurry fun z y => φ z * (ub y * (g y - g (y + z))))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hφi.norm.mul_prod hubi.norm).const_mul (2 * Kg)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hφ.comp continuous_fst).aestronglyMeasurable.mul
        ((hubi.aestronglyMeasurable.comp_snd).mul
          ((hg.comp continuous_snd).sub
            (hg.comp (continuous_snd.add continuous_fst))).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 : ‖g p.2 - g (p.2 + p.1)‖ ≤ 2 * Kg := by
        calc ‖g p.2 - g (p.2 + p.1)‖ ≤ ‖g p.2‖ + ‖g (p.2 + p.1)‖ := norm_sub_le _ _
          _ ≤ Kg + Kg := add_le_add (hKg _) (hKg _)
          _ = 2 * Kg := by ring
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (φ p.1)
      calc ‖φ p.1‖ * (‖ub p.2‖ * ‖g p.2 - g (p.2 + p.1)‖)
          = ‖g p.2 - g (p.2 + p.1)‖ * (‖φ p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  have key2 : ∫ z, φ z * ∫ y, ub y * (g y - g (y + z))
      = ∫ y, ub y * (g y - ∫ z, φ z * g (z + y)) := by
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hHi]
    congr 1; funext y
    have : ∀ z, φ z * (ub y * (g y - g (y + z))) = ub y * (φ z * (g y - g (y + z))) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, hinner y]
  -- Step 6: both sides equal `∫ ū g − ∫ ū(y) ∫ φ(z) g(z + y) dz dy`
  rw [integral_sub hubg hwgi, key1, key2]
  simp_rw [mul_sub]
  rw [integral_sub hubg hconv]

/-- **Pairing of `u − u ∗ φ` with a test function, for `u` of bounded variation** (Claim A of the
`BV` mollifier estimate; mollification of `BV` functions as in Simon, Ch. 2, §2).  Let `φ ≥ 0` be
smooth with `tsupport φ ⊆ B_s(0)` and `∫ φ = 1`, let `u` be integrable on `B_{2R}(0)` with
`|∫_{B_{2R}(0)} u(y) Df(y)(z) dy| ≤ V‖z‖M` for all smooth `f` with compact support in `B_{2R}(0)`
and `|f| ≤ M`, and let `2s < R`.  If `g` is smooth with compact support in `B_{R+s}(0)` and
`|g| ≤ 1`, then `|∫ (u − w) g| ≤ sV`, where `w(x) = ∫_{B_{2R}(0)} u(y) φ(x − y) dy`.  By Fubini,
`∫ (u − w) g = ∫ φ(z) I(z) dz` with `I(z) = ∫_{B_{2R}(0)} u(y) (g(y) − g(y + z)) dy`; if
`φ(z) ≠ 0` then `‖z‖ < s < R − s`, so `g` and its translate by `z` are supported in `B_{2R}(0)` and
the translation estimate gives `|I(z)| ≤ V‖z‖ ≤ sV`; integrate against `φ`. -/
theorem Submission.cbr_ci_pw_bv_smooth_test_bound : ∀ (n : ℕ) (R s V : ℝ) (φ u g : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + s) → (∀ x, |g x| ≤ 1) → |∫ x, (u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) * g x| ≤ s * V := by
  intro n R s V φ u g _hR hs h2s hV hφ hφ0 hφs hφ1 hu hvar hg hgc hgs hgb
  -- `φ` has compact support, and `g` vanishes off `B_{2R}(0)` since `R + s ≤ 2R`
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  have hgS : ∀ x, x ∉ ball (0 : Euclid n) (2 * R) → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (ball_subset_ball (by linarith) (hgs hx'))
  -- Fubini: `∫ (u - w) g = ∫ φ(z) ∫_{B_{2R}(0)} u(y) (g(y) - g(y + z)) dy dz`
  rw [Submission.cbr_ci_pw_bv_pairing_identity n (ball 0 (2 * R)) φ u g measurableSet_ball
    hφ.continuous hφc hφ1 hu hg.continuous hgc hgS]
  -- `|φ(z) I(z)| ≤ φ(z) sV`: trivial if `φ(z) = 0`, else `‖z‖ < s` and translate by `z`
  have hbound : ∀ z, ‖φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ ≤
      φ z * (s * V) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    have hzs : ‖z‖ < s := mem_ball_zero_iff.1 (hφs (subset_tsupport φ hz))
    have hT := Submission.cbr_ci_pw_bv_translate_test n (2 * R) V 1 u g z hu hvar hg hgc
      (hgs.trans (ball_subset_ball (by linarith))) hgb
    have hneg : ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z)) =
        -∫ y in ball (0 : Euclid n) (2 * R), u y * (g (y + z) - g y) := by
      rw [← integral_neg]; congr 1; funext y; ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφ0 z), hneg, abs_neg]
    refine mul_le_mul_of_nonneg_left (hT.trans ?_) (hφ0 z)
    linarith [mul_le_mul_of_nonneg_left hzs.le hV]
  -- integrate against `φ`, using `∫ φ = 1`
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  calc |∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))|
      = ‖∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, φ z * (s * V) :=
        norm_integral_le_of_norm_le (hφi.mul_const _) (Eventually.of_forall hbound)
    _ = s * V := by rw [integral_mul_const, hφ1, one_mul]
/-- **Smooth a.e. approximation of a bounded function supported in a ball** (mollification; cf.
Evans, *PDE*, App. C, Thm. 7).  If `g₀ : ℝⁿ → ℝ` is measurable, `|g₀| ≤ 1` and `g₀ = 0` off
`B_R(0)`, let `ρ = b / ∫ b` for the `ContDiffBump` `b` with radii `1/4, 1/2`,
`ψ_ε(x) = ε⁻ⁿ ρ(ε⁻¹ x)` and `θ_j = δ / (j + 2)`.  Then `G_j = g₀ ⋆ ψ_{θ_j}` is `C^∞`, vanishes
off `B̄_{R + θ_j/2}(0) ⊆ B_{R+δ}(0)`, satisfies `|G_j| ≤ ∫ ψ_{θ_j} = 1`, and `G_j(x) → g₀(x)` at
every Lebesgue point `x` of `g₀` (approximate identity with `|ψ_{θ_j}| ≤ C / Lⁿ(B_{θ_j}(x))`),
hence for `Lⁿ`-a.e. `x`. -/
theorem Submission.cbr_ci_pw_bv_smooth_ae_approx : ∀ (n : ℕ) (R δ : ℝ) (g₀ : Euclid n → ℝ), 0 < δ → Measurable g₀ → (∀ x, |g₀ x| ≤ 1) → (∀ x, R ≤ ‖x‖ → g₀ x = 0) → ∃ G : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧ (∀ j, tsupport (G j) ⊆ ball 0 (R + δ)) ∧ (∀ j x, |G j x| ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun j => G j x) atTop (𝓝 (g₀ x)) := by
  intro n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 0: g₀ is integrable
  have hg₀out : ∀ x, x ∉ ball (0 : Euclid n) R → g₀ x = 0 := fun x hx =>
    hg₀z x (by simpa [mem_ball_zero_iff] using hx)
  have hg₀i : Integrable g₀ := by
    have hon : IntegrableOn g₀ (ball (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne hg₀m.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg₀b x)
    exact (integrableOn_iff_integrable_of_support_subset
      (fun x hx => by by_contra h; exact hx (hg₀out x h))).1 hon
  -- Step 1: a normalized bump
  let b : ContDiffBump (0 : Euclid n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbi : Integrable (b : Euclid n → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  set I : ℝ := ∫ x, b x with hIdef
  have hI : 0 < I := by
    rw [hIdef, integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbi, b.support_eq]
    exact measure_ball_pos _ _ (by norm_num)
  set ρ : Euclid n → ℝ := fun x => b x / I with hρdef
  have hρc : ContDiff ℝ (⊤ : ℕ∞) ρ := b.contDiff.div_const I
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => div_nonneg b.nonneg hI.le
  have hρb : ∀ x, ρ x ≤ 1 / I := fun x => div_le_div_of_nonneg_right b.le_one hI.le
  have hρz : ∀ x, (1 / 2 : ℝ) ≤ ‖x‖ → ρ x = 0 := by
    intro x hx
    have : x ∉ support (b : Euclid n → ℝ) := by
      rw [b.support_eq, mem_ball_zero_iff]; exact not_lt.2 hx
    simp [hρdef, notMem_support.1 this]
  have hρ1 : ∫ x, ρ x = 1 := by
    simp only [hρdef]; rw [integral_div, ← hIdef, div_self hI.ne']
  -- Step 2: rescaled mollifiers
  set ψ : ℝ → Euclid n → ℝ := fun ε x => (ε ^ n)⁻¹ * ρ (ε⁻¹ • x) with hψdef
  have hψc : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (ψ ε) := fun ε =>
    contDiff_const.mul (hρc.comp (contDiff_const_smul ε⁻¹))
  have hψ0 : ∀ ε, 0 < ε → ∀ x, 0 ≤ ψ ε x := fun ε hε x =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le n)) (hρ0 _)
  have hψz : ∀ ε, 0 < ε → ∀ x, ε / 2 ≤ ‖x‖ → ψ ε x = 0 := by
    intro ε hε x hx
    have : (1 / 2 : ℝ) ≤ ‖ε⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      rw [le_inv_mul_iff₀ hε]; linarith
    simp [hψdef, hρz _ this]
  have hψb : ∀ ε, 0 < ε → ∀ x, |ψ ε x| ≤ (1 / I) / ε ^ n := by
    intro ε hε x
    rw [abs_of_nonneg (hψ0 ε hε x), hψdef]
    simp only
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hρb _) (inv_nonneg.2 (pow_nonneg hε.le n))
  have hψ1 : ∀ ε, 0 < ε → ∫ x, ψ ε x = 1 := by
    intro ε hε
    simp only [hψdef]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg _ _ hε.le,
      finrank_euclideanSpace_fin, hρ1, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero n hε.ne')]
  have hψcs : ∀ ε, 0 < ε → HasCompactSupport (ψ ε) := by
    intro ε hε
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hψz ε hε x (by linarith)
  -- Step 3: the sequence
  set θ : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hθdef
  have hθpos : ∀ j, 0 < θ j := fun j => div_pos hδ (by positivity)
  have hθlt : ∀ j, θ j < δ := fun j => by
    rw [hθdef]; simp only
    rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hG : ∀ j x, convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = ∫ y, g₀ y * ψ (θ j) (x - y) := by
    intro j x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvan : ∀ j x, R + θ j / 2 ≤ ‖x‖ →
      convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro j x hx
    rw [hG]
    have : (fun y => g₀ y * ψ (θ j) (x - y)) = fun _ => 0 := by
      funext y
      by_cases hy : R ≤ ‖y‖
      · rw [hg₀z y hy, zero_mul]
      · push Not at hy
        have h1 : θ j / 2 ≤ ‖x - y‖ := by
          have := norm_sub_norm_le x y
          linarith
        rw [hψz (θ j) (hθpos j) _ h1, mul_zero]
    rw [this, integral_zero]
  have hsupp : ∀ j, support (convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ closedBall 0 (R + θ j / 2) := by
    intro j x hx
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hx (hvan j x (not_le.1 h).le)
  refine ⟨fun j => convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hψcs (θ j) (hθpos j)).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hg₀i.locallyIntegrable (hψc (θ j))
  · intro j
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp j)
  · intro j
    refine (closure_minimal (hsupp j) isClosed_closedBall).trans (closedBall_subset_ball ?_)
    linarith [hθlt j, hθpos j]
  · intro j x
    simp only
    rw [hG]
    have hψi : Integrable (ψ (θ j)) :=
      (hψc (θ j)).continuous.integrable_of_hasCompactSupport (hψcs (θ j) (hθpos j))
    calc |∫ y, g₀ y * ψ (θ j) (x - y)| ≤ ∫ y, |g₀ y * ψ (θ j) (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, ψ (θ j) (x - y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hψi.comp_sub_left x) (Eventually.of_forall fun y => ?_)
          show |g₀ y * ψ (θ j) (x - y)| ≤ ψ (θ j) (x - y)
          rw [abs_mul, abs_of_nonneg (hψ0 _ (hθpos j) _)]
          exact mul_le_of_le_one_left (hψ0 _ (hθpos j) _) (hg₀b y)
      _ = 1 := by rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)]
  · have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) hg₀i.locallyIntegrable 1
    filter_upwards [hleb] with x hx
    have hθ0 : Tendsto θ atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [hθdef] using this.const_div_atTop δ
    have hθ : Tendsto θ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hθ0
        (Eventually.of_forall fun j => hθpos j)
    have havg := hx (fun _ => x) θ hθ
      (Eventually.of_forall fun j => mem_closedBall_self (by simpa using (hθpos j).le))
    have hB1 : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
    have key := tendsto_integral_smul_of_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) (f := g₀) (c := g₀ x)
      (a := fun j => closedBall x (θ j)) (g := fun j y => ψ (θ j) (x - y))
      ((1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1)) havg
      (Eventually.of_forall fun j => hg₀i.integrableOn)
      (by
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
        simp only
        rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)])
      (Eventually.of_forall fun j y hy => by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        by_contra h
        exact hy (hψz _ (hθpos j) _ (by linarith [hθpos j])))
      (Eventually.of_forall fun j y => by
        rw [Measure.addHaar_real_closedBall' _ _ (hθpos j).le, finrank_euclideanSpace_fin]
        have hpow : 0 < θ j ^ n := pow_pos (hθpos j) n
        calc |ψ (θ j) (x - y)| ≤ (1 / I) / θ j ^ n := hψb _ (hθpos j) _
          _ = (1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1) /
              (θ j ^ n * (volume : Measure (Euclid n)).real (closedBall 0 1)) := by
            field_simp)
    refine key.congr' (Eventually.of_forall fun j => ?_)
    simp only
    rw [hG]
    congr 1; funext y
    rw [smul_eq_mul, mul_comm]

/-- **The `L¹` norm on a ball by duality with smooth test functions** (steps 2 and 4 of the BV
estimate `∫_{B_R} |u − u ∗ φ_s| ≤ s V` in the cycle part of the proof of Simon 7.2.4): if `h` is
integrable on `B_{R+δ}(0)`, `δ > 0`, and `∫ h g ≤ C` for every smooth `g` with compact support in
`B_{R+δ}(0)` and `|g| ≤ 1`, then `∫_{B_R(0)} |h| ≤ C`.  With a Borel representative `h̃` of `h`
on `B_{R+δ}(0)` and `g₀ = 1_{B_R(0)} sgn h̃`, the admissible smooth tests `G_j → g₀` a.e. of
`smooth_ae_approx` give `∫ h G_j ≤ C`, and dominated convergence (dominant `|h|`) gives
`∫ h G_j → ∫_{B_{R+δ}(0)} h g₀ = ∫_{B_R(0)} |h|`. -/
theorem Submission.cbr_ci_pw_bv_l1_duality : ∀ (n : ℕ) (R δ C : ℝ) (h : Euclid n → ℝ), 0 < δ → IntegrableOn h (ball 0 (R + δ)) → (∀ g : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + δ) → (∀ x, |g x| ≤ 1) → ∫ x, h x * g x ≤ C) → ∫ x in ball 0 R, |h x| ≤ C := by
  intro n R δ C h hδ hh htest
  set B : Set (Euclid n) := ball 0 (R + δ) with hB
  -- Step 1: a Borel representative `h̃ = hm` of `h` on `B`
  set hm : Euclid n → ℝ := hh.aestronglyMeasurable.mk h with hhm
  have hhm_meas : Measurable hm := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : h =ᵐ[volume.restrict B] hm := hh.aestronglyMeasurable.ae_eq_mk
  -- Step 2: the sign function `g₀ = 1_{B_R(0)} sgn h̃`: Borel, `|g₀| ≤ 1`, `g₀ = 0` off `B_R(0)`
  set g₀ : Euclid n → ℝ :=
    (ball (0 : Euclid n) R).indicator (fun x => if 0 ≤ hm x then 1 else -1) with hg₀
  have hg₀m : Measurable g₀ :=
    (Measurable.ite (measurableSet_le measurable_const hhm_meas) measurable_const
      measurable_const).indicator measurableSet_ball
  have hg₀b : ∀ x, |g₀ x| ≤ 1 := by
    intro x
    simp only [hg₀, Set.indicator]
    split_ifs <;> norm_num
  have hg₀z : ∀ x, R ≤ ‖x‖ → g₀ x = 0 := by
    intro x hx
    simp only [hg₀]
    exact Set.indicator_of_notMem (by simpa [mem_ball_zero_iff] using hx) _
  -- Step 3: smooth admissible tests `G_j → g₀` a.e.
  obtain ⟨G, hGs, hGc, hGt, hGb, hGl⟩ :=
    Submission.cbr_ci_pw_bv_smooth_ae_approx n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 4: `∫_B h G_j = ∫ h G_j ≤ C`, as `G_j` vanishes off `B`
  have hle : ∀ j, ∫ x in B, h x * G j x ≤ C := by
    intro j
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hGt j hx')), mul_zero])]
    exact htest (G j) (hGs j) (hGc j) (hGt j) (hGb j)
  -- Step 5: dominated convergence on `B`, with dominant `|h|`
  have hlim : Tendsto (fun j => ∫ x in B, h x * G j x) atTop (𝓝 (∫ x in B, h x * g₀ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun j => ?_) hh.norm
      (fun j => ?_) ?_
    · exact hh.aestronglyMeasurable.mul (hGs j).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hGb j x)
    · exact (ae_restrict_of_ae hGl).mono fun x hx => tendsto_const_nhds.mul hx
  -- Step 6: `h g₀ = 1_{B_R(0)} |h|` a.e. on `B`, so `∫_B h g₀ = ∫_{B_R(0)} |h|`
  have heq : ∫ x in B, h x * g₀ x = ∫ x in ball 0 R, |h x| := by
    have hfg : (fun x => h x * g₀ x) =ᵐ[volume.restrict B]
        (ball (0 : Euclid n) R).indicator (fun x => |h x|) := by
      filter_upwards [hae] with x hx
      simp only [hg₀, Set.indicator]
      split_ifs with hxR hpos
      · rw [hx, mul_one, abs_of_nonneg hpos]
      · rw [hx, mul_neg_one, abs_of_neg (not_le.1 hpos)]
      · rw [mul_zero]
    rw [integral_congr_ae hfg, setIntegral_indicator measurableSet_ball,
      Set.inter_eq_right.2 (ball_subset_ball (by linarith : R ≤ R + δ))]
  -- Step 7: a limit of numbers `≤ C` is `≤ C`
  rw [← heq]
  exact le_of_tendsto' hlim hle
/-- **Continuity of the mollification** (the "`w` is continuous" step of the BV estimate): if `u`
is integrable on `S ⊆ ℝⁿ` and `φ` is continuous with compact support, then
`x ↦ ∫_S u(y) φ(x - y) dy` is continuous.  `φ` is bounded, `|φ| ≤ K`, so for every `x` the
integrand is dominated by the `x`-independent integrable function `|u| K`, and it is continuous in
`x` for every `y`; conclude by `continuous_of_dominated`. -/
theorem Submission.cbr_ci_pw_bv_mollify_continuous : ∀ (n : ℕ) (S : Set (Euclid n)) (φ u : Euclid n → ℝ), IntegrableOn u S → Continuous φ → HasCompactSupport φ → Continuous (fun x => ∫ y in S, u y * φ (x - y)) := by
  intro n S φ u hu hφ hφc
  -- `|φ| ≤ K`: `φ` is continuous with compact support
  obtain ⟨K, hK⟩ := hφ.bounded_above_of_compact_support hφc
  -- dominated continuity of parametric integrals, with the dominant `|u| K` integrable on `S`
  refine continuous_of_dominated (bound := fun y => ‖u y‖ * K) (fun x => ?_) (fun x => ?_)
    (hu.norm.mul_const K) (Eventually.of_forall fun y => ?_)
  · -- measurability in `y`: `u` is a.e.-strongly measurable on `S`, `y ↦ φ (x - y)` is continuous
    exact hu.aestronglyMeasurable.mul
      (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · -- domination: `|u y φ (x - y)| ≤ |u y| K`
    exact Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
  · -- continuity in `x` for each fixed `y`
    exact continuous_const.mul (hφ.comp (continuous_id.sub continuous_const))

/-- **BV estimate for mollification** (for the integer multiplicity of limits in Simon 7.2.4,
Remark 7.2.5(1); the boundary mass `M_{B_{2R}}(∂Y)` is replaced by a variation bound `V`): if `u`
is integrable on `B_{2R}(0)` and `|∫_{B_{2R}(0)} u(y) Df(y)(z) dy| ≤ V‖z‖M` for every smooth `f`
supported in `B_{2R}(0)` with `|f| ≤ M`, then `∫_{B_R(0)} |u − w| ≤ sV` for
`w(x) = ∫_{B_{2R}(0)} u(y)φ(x − y) dy`, where `φ ≥ 0` is smooth, `tsupport φ ⊆ B_s(0)`,
`∫φ = 1` and `2s < R`.  The mollification `w` is continuous (`cbr_ci_pw_bv_mollify_continuous`),
so `u − w` is integrable on `B_{R+s}(0)`; its pairings with smooth `g`, `|g| ≤ 1`,
`tsupport g ⊆ B_{R+s}(0)` are at most `sV` (`cbr_ci_pw_bv_smooth_test_bound`); `L¹` duality
(`cbr_ci_pw_bv_l1_duality` with `δ = s`) concludes. -/
theorem Submission.cbr_ci_pw_bv_mollifier_estimate : ∀ (n : ℕ) (R s V : ℝ) (φ u : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ∫ x in ball 0 R, |u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)| ≤ s * V := by
  intro n R s V φ u hR hs hsR hV hφ hφ0 hφs hφ1 hu hvar
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall 0 s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  have hw : Continuous fun x => ∫ y in ball 0 (2 * R), u y * φ (x - y) :=
    Submission.cbr_ci_pw_bv_mollify_continuous n (ball 0 (2 * R)) φ u hu hφ.continuous hφc
  have hh : IntegrableOn (fun x => u x - ∫ y in ball 0 (2 * R), u y * φ (x - y))
      (ball 0 (R + s)) :=
    (hu.mono_set (ball_subset_ball (by linarith))).fun_sub
      ((hw.continuousOn.integrableOn_compact (isCompact_closedBall 0 (R + s))).mono_set
        ball_subset_closedBall)
  exact Submission.cbr_ci_pw_bv_l1_duality n R s (s * V)
    (fun x => u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) hs hh
    fun g hg hgc hgs hg1 => (le_abs_self _).trans
      (Submission.cbr_ci_pw_bv_smooth_test_bound n R s V φ u g hR hs hsR hV hφ hφ0 hφs hφ1 hu
        hvar hg hgc hgs hg1)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
