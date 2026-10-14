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

/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)

/-- Near-isometric local parametrizations of an embedded `C¹` submanifold `M` (charts as in
Simon Ch. 2, (4.1)): for `z ∈ M` and `ε > 0` there are `χ` with `χ(0) = z` and `δ, δ' > 0` such
that `χ` is `(1 ± ε)`-bi-Lipschitz on `B_δ(0)`, `χ(B_δ(0)) ⊆ M` and `M ∩ B_{δ'}(z) ⊆ χ(B_δ(0))`.
Take a chart `ψ` with `ψ(v₀) = z`, choose `L ∈ GL(ℝⁿ)` with `Dψ(v₀) ∘ L` a linear isometry (an
orthonormal basis of `Dψ(v₀)(ℝⁿ)`) and put `χ(w) = ψ(v₀ + Lw)`; strict differentiability of `χ`
at `0` gives the two-point bounds, and continuity of the chart inverse
(`Submission.dsmc_chart_inverse_continuity`) gives the covering of `M ∩ B_{δ'}(z)`. -/
theorem Submission.dimred_rpd_near_isometric_chart : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → ∀ ε : ℝ, 0 < ε → ∃ (χ : Euclid n → Euclid P) (δ δ' : ℝ), 0 < δ ∧ 0 < δ' ∧ χ 0 = z ∧ (∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ, (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖) ∧ χ '' ball 0 δ ⊆ M ∧ M ∩ ball z δ' ⊆ χ '' ball 0 δ := by
  intro P n M z hM hz ε hε
  obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, hprop, hder⟩ := hM z hz
  obtain ⟨v₀, hv₀V, hψv₀⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hzW, hz⟩
  set A : Euclid n →L[ℝ] Euclid P := fderiv ℝ ψ v₀
  have hA : Injective A := hder v₀ hv₀V
  have hstrict : HasStrictFDerivAt ψ A v₀ :=
    (hψ.contDiffAt (hV.mem_nhds hv₀V)).hasStrictFDerivAt one_ne_zero
  -- isometric normalization
  obtain ⟨L, hLJ⟩ : ∃ L : Euclid n ≃L[ℝ] Euclid n, ∀ w, ‖A (L w)‖ = ‖w‖ := by
    let Q := LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)
    have hfin : Module.finrank ℝ Q = n := by
      rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hfin)
    let A' : Euclid n ≃ₗ[ℝ] Q := LinearEquiv.ofInjective (A : Euclid n →ₗ[ℝ] Euclid P) hA
    let L₀ : Euclid n ≃ₗ[ℝ] Euclid n := b.repr.symm.toLinearEquiv.trans A'.symm
    refine ⟨L₀.toContinuousLinearEquiv, fun w => ?_⟩
    have h1 : A' (L₀ w) = b.repr.symm w := by simp [L₀]
    have h2 : A (L₀ w) = ((A' (L₀ w) : Q) : Euclid P) := rfl
    change ‖A (L₀ w)‖ = ‖w‖
    rw [h2, h1]
    exact b.repr.symm.norm_map w
  set χ : Euclid n → Euclid P := fun w => ψ (v₀ + L w)
  have hχ0 : χ 0 = z := by simp [χ, hψv₀]
  have hχstrict : HasStrictFDerivAt χ (A.comp (L : Euclid n →L[ℝ] Euclid n)) 0 := by
    have h1 : HasStrictFDerivAt (fun w : Euclid n => v₀ + L w) (L : Euclid n →L[ℝ] Euclid n) 0 :=
      (L.hasStrictFDerivAt).const_add v₀
    have h2 : HasStrictFDerivAt ψ A (v₀ + L 0) := by simpa using hstrict
    exact h2.comp (0 : Euclid n) h1
  -- two-point estimate
  have h1 := (hasStrictFDerivAt_iff_isLittleO.1 hχstrict).bound hε
  have h2 : ∀ᶠ w in 𝓝 (0 : Euclid n), v₀ + L w ∈ V := by
    have hc : Continuous (fun w : Euclid n => v₀ + L w) := continuous_const.add L.continuous
    have : (fun w : Euclid n => v₀ + L w) 0 ∈ V := by simpa using hv₀V
    exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds this)
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.eventually_nhds_iff_ball.1 h1
  obtain ⟨δ₂, hδ₂, hball2⟩ := Metric.eventually_nhds_iff_ball.1 h2
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδV : ∀ w ∈ ball (0 : Euclid n) δ, v₀ + L w ∈ V :=
    fun w hw => hball2 w (ball_subset_ball (min_le_right _ _) hw)
  have hbil : ∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ,
      (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖ := by
    intro a ha b hb
    have hab : (a, b) ∈ ball ((0 : Euclid n), (0 : Euclid n)) δ₁ := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) ha, ball_subset_ball (min_le_left _ _) hb⟩
    have he := hball1 (a, b) hab
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at he
    have hn : ‖A (L (a - b))‖ = ‖a - b‖ := hLJ _
    have t1 := norm_sub_norm_le (χ a - χ b) (A (L (a - b)))
    have t2 := norm_sub_norm_le (A (L (a - b))) (χ a - χ b)
    rw [norm_sub_rev (A (L (a - b))) (χ a - χ b)] at t2
    constructor <;> linarith
  -- local surjectivity
  have hinvc := Submission.dsmc_chart_inverse_continuity P n V W ψ hψ.continuousOn hinj
    (by rw [himg]; exact inter_subset_left) hprop v₀ hv₀V
  set C : ℝ := ‖((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n)‖ with hCdef
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨η, hη, hηprop⟩ := hinvc (δ / (C + 1)) (div_pos hδ (by linarith))
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.isOpen_iff.1 hW z hzW
  refine ⟨χ, δ, min η r₀, hδ, lt_min hη hr₀, hχ0, hbil, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have : ψ (v₀ + L w) ∈ W ∩ M := by rw [← himg]; exact ⟨_, hδV w hw, rfl⟩
    exact this.2
  · rintro x ⟨hxM, hxb⟩
    have hxW : x ∈ W := hr₀W (ball_subset_ball (min_le_right _ _) hxb)
    obtain ⟨v', hv'V, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hxM⟩
    have hd : dist (ψ v') (ψ v₀) < η := by
      rw [hψv₀]; exact lt_of_lt_of_le (mem_ball.1 hxb) (min_le_left _ _)
    have hv' := hηprop v' hv'V hd
    refine ⟨L.symm (v' - v₀), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      calc ‖L.symm (v' - v₀)‖ ≤ C * ‖v' - v₀‖ := by
            rw [hCdef]
            exact ContinuousLinearMap.le_opNorm
              ((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n) (v' - v₀)
        _ ≤ C * (δ / (C + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← dist_eq_norm]; exact hv'.le
        _ < δ := by
            rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
            nlinarith
    · simp [χ]
/-- **Bi-Lipschitz images** (Simon Ch. 2, 1.8(i), applied to `χ` and to its inverse): if
`c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b|` on `E ⊆ ℝⁿ`, then `c₁ⁿ Lⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿ Lⁿ(E)`.
`Hⁿ = μHE[n]` is `c · μH[n]` with one constant `c` on every metric space and equals `volume` on
`ℝⁿ`; `χ` is `c₂`-Lipschitz on `E`, and it is injective there with `c₁⁻¹`-Lipschitz inverse on
`χ(E)`. -/
theorem Submission.dimred_rpd_bilipschitz_image_measure : ∀ (P n : ℕ) (χ : Euclid n → Euclid P) (E : Set (Euclid n)) (c₁ c₂ : ℝ), 0 < c₁ → 0 ≤ c₂ → (∀ a ∈ E, ∀ b ∈ E, c₁ * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ c₂ * ‖a - b‖) → ENNReal.ofReal (c₁ ^ n) * volume E ≤ μHE[n] (χ '' E) ∧ μHE[n] (χ '' E) ≤ ENNReal.ofReal (c₂ ^ n) * volume E := by
  intro P n χ E c₁ c₂ hc₁ hc₂ h
  -- `Lⁿ = Hⁿ` on `ℝⁿ`, and `Hⁿ = c · μH[n]` on every metric space
  have hvol : (volume : Measure (Euclid n)) = μHE[n] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).symm
  have hscale : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
      (μHE[n] : Measure X) S = (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) * μH[(n : ℝ)] S := by
    intro X _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · -- lower bound: `χ` is injective on `E` and its inverse on `χ(E)` is `c₁⁻¹`-Lipschitz
    have hinj : InjOn χ E := by
      intro a ha b hb hab
      have := (h a ha b hb).1
      rw [hab, sub_self, norm_zero] at this
      have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    set g := Function.invFunOn χ E
    have hleft : LeftInvOn g χ E := hinj.leftInvOn_invFunOn
    have hgL : LipschitzOnWith (Real.toNNReal c₁⁻¹) g (χ '' E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hleft ha, hleft hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le)]
      have := (h a ha b hb).1
      rw [inv_mul_eq_div, le_div_iff₀ hc₁]
      linarith
    have himg : g '' (χ '' E) = E := hleft.image_image
    have hle := hgL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [himg] at hle
    rw [hvol, hscale, hscale (χ '' E)]
    set c : ℝ≥0∞ := (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞)
    have hK : ((Real.toNNReal c₁⁻¹ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₁ ^ n)⁻¹ := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le), ← ENNReal.ofReal_pow (inv_nonneg.2 hc₁.le),
        inv_pow]
    rw [hK] at hle
    have hpos : ENNReal.ofReal (c₁ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hc₁ n)).ne'
    have hinv : ENNReal.ofReal (c₁ ^ n)⁻¹ = (ENNReal.ofReal (c₁ ^ n))⁻¹ :=
      ENNReal.ofReal_inv_of_pos (pow_pos hc₁ n)
    rw [hinv] at hle
    calc ENNReal.ofReal (c₁ ^ n) * (c * μH[(n : ℝ)] E)
        ≤ ENNReal.ofReal (c₁ ^ n) * (c * ((ENNReal.ofReal (c₁ ^ n))⁻¹ * μH[(n : ℝ)] (χ '' E))) := by
          gcongr
      _ = c * μH[(n : ℝ)] (χ '' E) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (c₁ ^ n)) c, mul_assoc,
            ← mul_assoc (ENNReal.ofReal (c₁ ^ n)), ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top,
            one_mul]
  · -- upper bound: `χ` is `c₂`-Lipschitz on `E`
    have hL : LipschitzOnWith (Real.toNNReal c₂) χ E := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc₂]
      exact (h a ha b hb).2
    have hle := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [hvol, hscale, hscale E]
    have hK : ((Real.toNNReal c₂ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₂ ^ n) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc₂,
        ← ENNReal.ofReal_pow hc₂]
    rw [hK] at hle
    calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          (ENNReal.ofReal (c₂ ^ n) * μH[(n : ℝ)] E) := by gcongr
      _ = _ := by ring

/-- **Density one on an embedded `C¹` submanifold** (the fact `Θⁿ(Hⁿ⌞M, z) = 1` behind
`Θⁿ(μ_T, z) = |m|` for `T = m[[M]]` near `z ∈ reg T`, Simon 7.4.1):
`Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` as `s ↓ 0`.  For `ε ∈ (0, 1)`, a `(1 ± ε)`-bi-Lipschitz chart `χ`
with `χ(0) = z` gives `χ(B_{s/(1+ε)}(0)) ⊆ M ∩ B_s(z) ⊆ χ(B_{s/(1−ε)}(0))` for small `s > 0`.  With
the bi-Lipschitz measure bounds (Simon Ch. 2, 1.8(i)) and `Lⁿ(B_r(0)) = ωₙrⁿ` this gives
`((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`, and both bounds tend to `1`
as `ε → 0`. -/
theorem Submission.dimred_rpd_submanifold_density_one : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → Tendsto (fun s : ℝ => μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M z hM hz
  -- `ωₙ ∈ (0, ∞)`, and `Lⁿ(B_r(0)) = rⁿωₙ` for `r > 0`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωT : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hvol : ∀ r : ℝ, 0 < r →
      volume (ball (0 : Euclid n) r) = ENNReal.ofReal (r ^ n) * unitBallVolume n := by
    intro r hr; rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin]; rfl
  -- Step 1: for `ε ∈ (0, 1)`, `((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`
  -- for all small `s > 0`
  have hbounds : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) ≤
          μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ∧
        μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ≤
          ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) := by
    intro ε hε hε1
    -- the `(1 ± ε)`-bi-Lipschitz chart `χ : B_δ(0) → M` with `χ(0) = z`, onto `M` near `z`
    obtain ⟨χ, δ, δ', hδ, hδ', hχ0, hbil, hχM, hMχ⟩ :=
      Submission.dimred_rpd_near_isometric_chart P n M z hM hz ε hε
    have h1ε : 0 < 1 - ε := by linarith
    have h1ε' : 0 < 1 + ε := by linarith
    have hs₀ : 0 < min δ' ((1 - ε) * δ) := lt_min hδ' (mul_pos h1ε hδ)
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hsδ' : s < δ' := lt_of_lt_of_le hs1 (min_le_left _ _)
    have hsδ : s < (1 - ε) * δ := lt_of_lt_of_le hs1 (min_le_right _ _)
    -- `0 < r₁ = s/(1 + ε) ≤ r₂ = s/(1 − ε) < δ`
    set r₁ := s / (1 + ε) with hr₁def
    set r₂ := s / (1 - ε) with hr₂def
    have hr₁ : 0 < r₁ := div_pos hs0 h1ε'
    have hr₂ : 0 < r₂ := div_pos hs0 h1ε
    have hr₂δ : r₂ < δ := by rw [hr₂def, div_lt_iff₀ h1ε]; linarith
    have hr₁r₂ : r₁ ≤ r₂ := div_le_div_of_nonneg_left hs0.le h1ε (by linarith)
    have hb₁ : ball (0 : Euclid n) r₁ ⊆ ball 0 δ := ball_subset_ball (by linarith)
    have hb₂ : ball (0 : Euclid n) r₂ ⊆ ball 0 δ := ball_subset_ball hr₂δ.le
    -- (a) `χ(B_{r₁}(0)) ⊆ M ∩ B_s(z)`: `|χ(w) − z| ≤ (1 + ε)|w| < (1 + ε)r₁ = s`
    have hinc₁ : χ '' ball 0 r₁ ⊆ M ∩ ball z s := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨hχM ⟨w, hb₁ hw, rfl⟩, ?_⟩
      rw [mem_ball, dist_eq_norm, ← hχ0]
      have h := (hbil w (hb₁ hw) 0 (mem_ball_self hδ)).2
      rw [sub_zero] at h
      rw [mem_ball, dist_zero_right] at hw
      calc ‖χ w - χ 0‖ ≤ (1 + ε) * ‖w‖ := h
        _ < (1 + ε) * r₁ := mul_lt_mul_of_pos_left hw h1ε'
        _ = s := by rw [hr₁def]; field_simp
    -- (b) `M ∩ B_s(z) ⊆ χ(B_{r₂}(0))`: `x = χ(w)` with `(1 − ε)|w| ≤ |x − z| < s`
    have hinc₂ : M ∩ ball z s ⊆ χ '' ball 0 r₂ := by
      rintro x ⟨hxM, hxs⟩
      obtain ⟨w, hw, rfl⟩ := hMχ ⟨hxM, ball_subset_ball hsδ'.le hxs⟩
      refine ⟨w, ?_, rfl⟩
      have h := (hbil w hw 0 (mem_ball_self hδ)).1
      rw [sub_zero] at h
      rw [mem_ball, dist_eq_norm, ← hχ0] at hxs
      rw [mem_ball, dist_zero_right, hr₂def, lt_div_iff₀ h1ε]
      nlinarith [norm_nonneg w]
    -- (c) the bi-Lipschitz measure bounds on `B_{r₁}(0), B_{r₂}(0) ⊆ B_δ(0)`
    have hlow := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₁) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₁ ha) b (hb₁ hb))).1
    have hupp := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₂) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₂ ha) b (hb₂ hb))).2
    rw [hvol r₁ hr₁] at hlow
    rw [hvol r₂ hr₂] at hupp
    have hm1 := hlow.trans (measure_mono hinc₁)
    have hm2 := (measure_mono hinc₂).trans hupp
    -- divide by `ωₙsⁿ ∈ (0, ∞)`
    have hden0 : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hs0 n)).ne'
    have hdenT : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωT ENNReal.ofReal_ne_top
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenT)]
      have e : ((1 - ε) / (1 + ε)) ^ n * s ^ n = (1 - ε) ^ n * r₁ ^ n := by
        rw [hr₁def, div_pow, div_pow]; field_simp
      calc ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) * (unitBallVolume n * ENNReal.ofReal (s ^ n))
          = ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n * s ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal ((1 - ε) ^ n * r₁ ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal ((1 - ε) ^ n) * (ENNReal.ofReal (r₁ ^ n) * unitBallVolume n) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ ≤ _ := hm1
    · rw [ENNReal.div_le_iff hden0 hdenT]
      have e : ((1 + ε) / (1 - ε)) ^ n * s ^ n = (1 + ε) ^ n * r₂ ^ n := by
        rw [hr₂def, div_pow, div_pow]; field_simp
      calc μHE[n] (M ∩ ball z s)
          ≤ ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal (r₂ ^ n) * unitBallVolume n) := hm2
        _ = ENNReal.ofReal ((1 + ε) ^ n * r₂ ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n * s ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) *
              (unitBallVolume n * ENNReal.ofReal (s ^ n)) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
  -- Step 2: both bounds tend to `1` as `ε → 0`, so `Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` (`tendsto_order`)
  have hg₁ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 - ε) / (1 + ε)) ^ n) (𝓝 0) (𝓝 (((1 - 0) / (1 + 0)) ^ n)) :=
      ((tendsto_const_nhds.sub tendsto_id).div (tendsto_const_nhds.add tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hg₂ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ n) (𝓝 0) (𝓝 (((1 + 0) / (1 - 0)) ^ n)) :=
      ((tendsto_const_nhds.add tendsto_id).div (tendsto_const_nhds.sub tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with ε h1 h2
    exact ⟨h1, h2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `a < 1`: choose `ε ∈ (0, 1)` with `a < ((1 − ε)/(1 + ε))ⁿ`
    obtain ⟨ε, hεa, hε0, hε1⟩ :=
      (((hg₁.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds ha)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_lt_of_le hεa hs.1
  · -- `1 < b`: choose `ε ∈ (0, 1)` with `((1 + ε)/(1 − ε))ⁿ < b`
    obtain ⟨ε, hεb, hε0, hε1⟩ :=
      (((hg₂.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_le_of_lt hs.2 hεb

/-- Profile for the Hardy test functions of Simon B.2, a smooth variant of the printed
`ψ = r^{1+ε} r₁^{1−n/2−2ε}` (`ε = 1/10`): with `a = 1 + ε = 11/10`, `b = 2 − m/2 − ε`,
`p(ρ) = ρᵃ / (1 + ρ^{a−b})` is smooth on `(0, ∞)`, positive, `ρ|p'(ρ)| ≤ (11/10) p(ρ)` (since
`ρp'/p = (a + bρ^{a−b}) / (1 + ρ^{a−b})` lies between `b ≥ −11/10` and `a = 11/10`),
`p(ρ) ≤ ρᵃ` and `p(ρ) ≤ ρᵇ`, i.e. `p² ≤ ρ^{−9/5} ρ⁴` and `p² ≤ ρ^{−m−1/5} ρ⁴`. -/
theorem Submission.codim1_hcp_sc_hardy_profile (m : ℕ) (hm2 : 2 ≤ m) (hm6 : m ≤ 6) :
    ∃ p p' : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ContDiffAt ℝ 1 p ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → HasDerivAt p (p' ρ) ρ) ∧ (∀ ρ : ℝ, 0 < ρ → 0 < p ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → (ρ * p' ρ) ^ 2 ≤ 121 / 100 * p ρ ^ 2) ∧
      (∀ ρ : ℝ, 0 < ρ → p ρ ^ 2 ≤ ρ ^ (-(9 / 5) : ℝ) * ρ ^ 4) ∧
      (∀ ρ : ℝ, 0 < ρ → p ρ ^ 2 ≤ ρ ^ (-(m : ℝ) - 1 / 5) * ρ ^ 4) := by
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm6' : (m : ℝ) ≤ 6 := by exact_mod_cast hm6
  set a : ℝ := 11 / 10 with ha
  set b : ℝ := 19 / 10 - (m : ℝ) / 2 with hb
  set c : ℝ := a - b with hc
  have hc0 : 0 < c := by rw [hc, ha, hb]; linarith
  -- `(ρ^e)² = ρ^{2e−4} ρ⁴`
  have hsq : ∀ ρ : ℝ, 0 < ρ → ∀ e : ℝ, (ρ ^ e) ^ 2 = ρ ^ (2 * e - 4) * ρ ^ 4 := by
    intro ρ hρ e
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_natCast ρ 4, ← Real.rpow_add hρ]
    congr 1
    push_cast
    ring
  refine ⟨fun r => r ^ a / (1 + r ^ c),
    fun r => (a * r ^ (a - 1) * (1 + r ^ c) - r ^ a * (c * r ^ (c - 1))) / (1 + r ^ c) ^ 2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    exact (Real.contDiffAt_rpow_const_of_ne hρ.ne').div
      (contDiffAt_const.add (Real.contDiffAt_rpow_const_of_ne hρ.ne')) (by positivity)
  · intro ρ hρ
    have h1 := Real.hasDerivAt_rpow_const (p := a) (Or.inl hρ.ne')
    have h2 := (Real.hasDerivAt_rpow_const (p := c) (Or.inl hρ.ne')).const_add 1
    exact h1.div h2 (by positivity)
  · intro ρ hρ
    positivity
  · intro ρ hρ
    have hX : 0 < ρ ^ a := Real.rpow_pos_of_pos hρ a
    have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
    simp only
    rw [Real.rpow_sub_one hρ.ne', Real.rpow_sub_one hρ.ne']
    set X := ρ ^ a
    set t := ρ ^ c
    have key : ρ * ((a * (X / ρ) * (1 + t) - X * (c * (t / ρ))) / (1 + t) ^ 2) =
        X / (1 + t) * ((a + b * t) / (1 + t)) := by
      rw [hc]
      field_simp
      ring
    rw [key, mul_pow]
    have hq : ((a + b * t) / (1 + t)) ^ 2 ≤ 121 / 100 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have h1 : -(11 / 10) * (1 + t) ≤ a + b * t := by rw [ha, hb]; nlinarith
      have h2 : a + b * t ≤ 11 / 10 * (1 + t) := by rw [ha, hb]; nlinarith
      nlinarith
    have := sq_nonneg (X / (1 + t))
    nlinarith
  · intro ρ hρ
    have hX : 0 ≤ ρ ^ a := Real.rpow_nonneg hρ.le a
    have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
    have hle : ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ a := div_le_self hX (by linarith)
    calc (ρ ^ a / (1 + ρ ^ c)) ^ 2 ≤ (ρ ^ a) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = ρ ^ (-(9 / 5) : ℝ) * ρ ^ 4 := by rw [hsq ρ hρ a, ha]; norm_num
  · intro ρ hρ
    have hX : 0 ≤ ρ ^ a := Real.rpow_nonneg hρ.le a
    have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
    have hle : ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ b := by
      calc ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ a / ρ ^ c := div_le_div_of_nonneg_left hX ht (by linarith)
        _ = ρ ^ b := by rw [← Real.rpow_sub hρ, hc]; ring_nf
    calc (ρ ^ a / (1 + ρ ^ c)) ^ 2 ≤ (ρ ^ b) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = ρ ^ (-(m : ℝ) - 1 / 5) * ρ ^ 4 := by rw [hsq ρ hρ b, hb]; ring_nf

/-- Piecewise-linear radial cut-off of Simon B.2 (printed `γ_ε`, here with parameter `κ ∈ (0, 1)`):
`g = 0` on `(−∞, κ/2]`, `g(ρ) = 2ρ/κ − 1` on `[κ/2, κ]`, `g = 1` on `[κ, 1/κ]`,
`g(ρ) = 2 − κρ` on `[1/κ, 2/κ]`, `g = 0` on `[2/κ, ∞)`.  It is Lipschitz with values in `[0, 1]`,
differentiable off the four break points with derivative `g'`, and `|ρ g'(ρ)| ≤ 2`. -/
theorem Submission.codim1_hcp_sc_hardy_cutoff (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ g g' : ℝ → ℝ, (∃ K, LipschitzWith K g) ∧ (∀ ρ, 0 ≤ g ρ ∧ g ρ ≤ 1) ∧
      (∀ ρ, ρ < κ / 2 ∨ 2 / κ < ρ → g ρ = 0) ∧
      (∀ ρ, ρ ≠ κ / 2 → ρ ≠ κ → ρ ≠ 1 / κ → ρ ≠ 2 / κ → HasDerivAt g (g' ρ) ρ) ∧
      Measurable g' ∧ (∀ ρ, 0 < ρ → (ρ * g' ρ) ^ 2 ≤ 4) ∧
      (∀ ρ, κ < ρ → ρ < 1 / κ → g ρ = 1 ∧ g' ρ = 0) := by
  classical
  set g : ℝ → ℝ := fun ρ => max 0 (min 1 (min (2 * ρ / κ - 1) (2 - κ * ρ))) with hg
  set g' : ℝ → ℝ := fun ρ =>
    if ρ ∈ Ioo (κ / 2) κ then 2 / κ else if ρ ∈ Ioo (1 / κ) (2 / κ) then -κ else 0 with hg'
  -- the break points are ordered: `κ/2 < κ < 1/κ < 2/κ`
  have hb1 : κ / 2 < κ := by linarith
  have hb2 : κ < 1 / κ := by rw [lt_div_iff₀ hκ0]; nlinarith
  have hb3 : 1 / κ < 2 / κ := div_lt_div_of_pos_right one_lt_two hκ0
  -- `2ρ/κ − 1` and `2 − κρ` against the break points
  have hA0 : ∀ ρ, ρ ≤ κ / 2 → 2 * ρ / κ - 1 ≤ 0 := fun ρ hρ => by
    rw [sub_nonpos, div_le_one hκ0]; linarith
  have hA0' : ∀ ρ, κ / 2 ≤ ρ → 0 ≤ 2 * ρ / κ - 1 := fun ρ hρ => by
    rw [sub_nonneg, le_div_iff₀ hκ0]; linarith
  have hA1 : ∀ ρ, ρ ≤ κ → 2 * ρ / κ - 1 ≤ 1 := fun ρ hρ => by
    rw [sub_le_iff_le_add, div_le_iff₀ hκ0]; linarith
  have hA1' : ∀ ρ, κ ≤ ρ → 1 ≤ 2 * ρ / κ - 1 := fun ρ hρ => by
    rw [le_sub_iff_add_le, le_div_iff₀ hκ0]; linarith
  have hB1 : ∀ ρ, ρ ≤ 1 / κ → 1 ≤ 2 - κ * ρ := fun ρ hρ => by
    rw [le_div_iff₀ hκ0] at hρ; linarith
  have hB1' : ∀ ρ, 1 / κ ≤ ρ → 2 - κ * ρ ≤ 1 := fun ρ hρ => by
    rw [div_le_iff₀ hκ0] at hρ; linarith
  have hB0 : ∀ ρ, ρ ≤ 2 / κ → 0 ≤ 2 - κ * ρ := fun ρ hρ => by
    rw [le_div_iff₀ hκ0] at hρ; linarith
  have hB0' : ∀ ρ, 2 / κ ≤ ρ → 2 - κ * ρ ≤ 0 := fun ρ hρ => by
    rw [div_le_iff₀ hκ0] at hρ; linarith
  -- values of `g` on the five pieces
  have hv1 : ∀ ρ, ρ ≤ κ / 2 → g ρ = 0 := fun ρ hρ =>
    max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (hA0 ρ hρ)))
  have hv2 : ∀ ρ, κ / 2 ≤ ρ → ρ ≤ κ → g ρ = 2 * ρ / κ - 1 := fun ρ hρ hρ' => by
    have h1 := hA1 ρ hρ'
    have h2 := hB1 ρ (hρ'.trans hb2.le)
    simp only [hg, min_eq_left (h1.trans h2), min_eq_right h1, max_eq_right (hA0' ρ hρ)]
  have hv3 : ∀ ρ, κ ≤ ρ → ρ ≤ 1 / κ → g ρ = 1 := fun ρ hρ hρ' => by
    have h := le_min (hA1' ρ hρ) (hB1 ρ hρ')
    simp only [hg, min_eq_left h, max_eq_right zero_le_one]
  have hv4 : ∀ ρ, 1 / κ ≤ ρ → ρ ≤ 2 / κ → g ρ = 2 - κ * ρ := fun ρ hρ hρ' => by
    have h1 := hB1' ρ hρ
    have h2 := hA1' ρ (hb2.le.trans hρ)
    simp only [hg, min_eq_right (h1.trans h2), min_eq_right h1, max_eq_right (hB0 ρ hρ')]
  have hv5 : ∀ ρ, 2 / κ ≤ ρ → g ρ = 0 := fun ρ hρ =>
    max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (hB0' ρ hρ)))
  refine ⟨g, g', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Lipschitz: `max 0 (min 1 (min ℓ₁ ℓ₂))` with `ℓ₁, ℓ₂` affine
    have hl1 : LipschitzWith (Real.toNNReal (2 / κ)) (fun ρ : ℝ => 2 * ρ / κ - 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
        show 2 * x / κ - 1 - (2 * y / κ - 1) = 2 / κ * (x - y) by ring, abs_mul,
        abs_of_pos (by positivity)]
    have hl2 : LipschitzWith (Real.toNNReal κ) (fun ρ : ℝ => 2 - κ * ρ) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.coe_toNNReal _ hκ0.le, Real.dist_eq, Real.dist_eq,
        show 2 - κ * x - (2 - κ * y) = -κ * (x - y) by ring, abs_mul, abs_neg, abs_of_pos hκ0]
    exact ⟨_, ((hl1.min hl2).const_min 1).const_max 0⟩
  · intro ρ
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · rintro ρ (hρ | hρ)
    · exact hv1 ρ hρ.le
    · exact hv5 ρ hρ.le
  · intro ρ h1 h2 h3 h4
    rcases lt_or_gt_of_ne h1 with hρ1 | hρ1
    · -- `ρ < κ/2`: `g = 0` near `ρ`
      have hev : g =ᶠ[𝓝 ρ] fun _ => 0 :=
        Filter.eventually_of_mem (Iio_mem_nhds hρ1) fun t ht => hv1 t (le_of_lt ht)
      have hval : g' ρ = 0 := by
        simp only [hg', mem_Ioo]
        rw [ite_eq_right (by intro h; linarith [h.1]), ite_eq_right (by intro h; linarith [h.1])]
      rw [hval]
      exact (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq hev
    rcases lt_or_gt_of_ne h2 with hρ2 | hρ2
    · -- `κ/2 < ρ < κ`: `g(t) = 2t/κ − 1` near `ρ`
      have hev : g =ᶠ[𝓝 ρ] fun t => 2 * t / κ - 1 :=
        Filter.eventually_of_mem (Ioo_mem_nhds hρ1 hρ2) fun t ht => hv2 t ht.1.le ht.2.le
      have hval : g' ρ = 2 / κ := by
        simp only [hg', mem_Ioo]
        rw [ite_eq_left ⟨hρ1, hρ2⟩]
      rw [hval]
      have hd : HasDerivAt (fun t : ℝ => 2 * t / κ - 1) (2 * 1 / κ) ρ :=
        (((hasDerivAt_id ρ).const_mul 2).div_const κ).sub_const 1
      rw [mul_one] at hd
      exact hd.congr_of_eventuallyEq hev
    rcases lt_or_gt_of_ne h3 with hρ3 | hρ3
    · -- `κ < ρ < 1/κ`: `g = 1` near `ρ`
      have hev : g =ᶠ[𝓝 ρ] fun _ => 1 :=
        Filter.eventually_of_mem (Ioo_mem_nhds hρ2 hρ3) fun t ht => hv3 t ht.1.le ht.2.le
      have hval : g' ρ = 0 := by
        simp only [hg', mem_Ioo]
        rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.1])]
      rw [hval]
      exact (hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq hev
    rcases lt_or_gt_of_ne h4 with hρ4 | hρ4
    · -- `1/κ < ρ < 2/κ`: `g(t) = 2 − κt` near `ρ`
      have hev : g =ᶠ[𝓝 ρ] fun t => 2 - κ * t :=
        Filter.eventually_of_mem (Ioo_mem_nhds hρ3 hρ4) fun t ht => hv4 t ht.1.le ht.2.le
      have hval : g' ρ = -κ := by
        simp only [hg', mem_Ioo]
        rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_left ⟨hρ3, hρ4⟩]
      rw [hval]
      have hd : HasDerivAt (fun t : ℝ => 2 - κ * t) (-(κ * 1)) ρ :=
        ((hasDerivAt_id ρ).const_mul κ).const_sub 2
      rw [mul_one] at hd
      exact hd.congr_of_eventuallyEq hev
    · -- `ρ > 2/κ`: `g = 0` near `ρ`
      have hev : g =ᶠ[𝓝 ρ] fun _ => 0 :=
        Filter.eventually_of_mem (Ioi_mem_nhds hρ4) fun t ht => hv5 t (le_of_lt ht)
      have hval : g' ρ = 0 := by
        simp only [hg', mem_Ioo]
        rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.2])]
      rw [hval]
      exact (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq hev
  · exact Measurable.ite measurableSet_Ioo measurable_const
      (Measurable.ite measurableSet_Ioo measurable_const measurable_const)
  · intro ρ hρ
    simp only [hg', mem_Ioo]
    split_ifs with h h'
    · have : ρ * (2 / κ) ≤ 2 := by
        rw [mul_div_assoc', div_le_iff₀ hκ0]; linarith [h.2]
      have h0 : 0 ≤ ρ * (2 / κ) := by positivity
      nlinarith
    · have : ρ * κ ≤ 2 := by
        have := h'.2; rw [lt_div_iff₀ hκ0] at this; linarith
      have h0 : 0 ≤ ρ * κ := by positivity
      nlinarith
    · norm_num
  · intro ρ hρ hρ'
    refine ⟨hv3 ρ hρ.le hρ'.le, ?_⟩
    simp only [hg', mem_Ioo]
    rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.1])]

/-- The product of two bounded Lipschitz functions on `s` is Lipschitz on `s`. -/
theorem Submission.codim1_hcp_sc_hardy_lipschitzOnWith_mul {α : Type*} [PseudoMetricSpace α]
    {f g : α → ℝ} {s : Set α} {Kf Kg : NNReal} {Bf Bg : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hBf : ∀ x ∈ s, |f x| ≤ Bf) (hBg : ∀ x ∈ s, |g x| ≤ Bg) :
    LipschitzOnWith (Real.toNNReal Bf * Kg + Real.toNNReal Bg * Kf) (fun x => f x * g x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf x hx)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg y hy)
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq] at h1 h2 ⊢
  push_cast
  rw [Real.coe_toNNReal _ hBf0, Real.coe_toNNReal _ hBg0]
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc |f x * (g x - g y) + g y * (f x - f y)| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Bf * (Kg * dist x y) + Bg * (Kf * dist x y) := by
        gcongr
        · exact hBf x hx
        · exact hBg y hy
    _ = (Bf * Kg + Bg * Kf) * dist x y := by ring

/-- **Radial test functions** (step 2 of the proof): if `x ≠ 0`, `x ∈ T_xM` and `u` has
derivative `d` at `|x|`, then `Σⱼ (δⱼ(u ∘ |·|)(x))² = d²`.  Indeed `D(u ∘ |·|)(x)v = d ⟪x, v⟫/|x|`,
`δⱼ(u ∘ |·|)(x) = D(u ∘ |·|)(x)(P_x eⱼ)` (`Submission.codim1_hcp_sc_fderivWithin_tangent_eq`),
`⟪x, P_x eⱼ⟫ = ⟪P_x x, eⱼ⟫ = xⱼ` and `Σⱼ xⱼ² = |x|²`. -/
theorem Submission.codim1_hcp_sc_hardy_radial (P : ℕ) (M : Set (Euclid P)) (x : Euclid P)
    (u : ℝ → ℝ) (d : ℝ) (hx : x ≠ 0) (hxT : x ∈ tangentSpace M x) (hu : HasDerivAt u d ‖x‖) :
    ∑ j : Fin P, (fderivWithin ℝ (fun y => u ‖y‖) M x
      ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 =
      d ^ 2 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  -- derivative of the norm at `x ≠ 0`
  have hnorm : HasFDerivAt (fun y : Euclid P => ‖y‖) ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
    have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by positivity)
    simp only [Real.sqrt_sq (norm_nonneg _)] at h1
    exact h1
  have hφ : HasFDerivWithinAt (fun y => u ‖y‖) (d • ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x))) M x :=
    (hu.comp_hasFDerivAt x hnorm).hasFDerivWithinAt
  have hPx : (Submodule.span ℝ (tangentSpace M x)).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span hxT)
  have key : ∀ j : Fin P, fderivWithin ℝ (fun y => u ‖y‖) M x
      ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) =
      d / ‖x‖ * x.ofLp j := by
    intro j
    rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hφ _
      (Submodule.starProjection_apply_mem _ _)]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    rw [← Submodule.inner_starProjection_left_eq_right, hPx, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial]
    field_simp
  simp_rw [key]
  have hs := EuclideanSpace.real_norm_sq_eq x
  calc ∑ j : Fin P, (d / ‖x‖ * x.ofLp j) ^ 2 = (d / ‖x‖) ^ 2 * ∑ j : Fin P, x.ofLp j ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = (d / ‖x‖) ^ 2 * ‖x‖ ^ 2 := by rw [hs]
    _ = d ^ 2 := by field_simp

/-- **Simon, Appendix B, end of the proof of B.2** (the extension of (3) under (4), the cut-offs
`γ_ε`, and the choice (6); `chapter-B.txt` lines 250–282).  Let `M ⊆ A₀ ≅ ℝ^{m+1}`, `2 ≤ m ≤ 6`,
be a smooth embedded hypercone (`0 ∉ M`, `tM = M`, `M̄ ⊆ M ∪ {0}`, locally `Hᵐ`-finite) with unit
normal `ν`, density one at each of its points, and the Hardy-type inequality (3)
`2∫ψ²|A|²/|x|² ≤ ∫|A|²|∇^Mψ|²` for compactly supported locally Lipschitz `ψ`.  Then
`Dν(x)v = 0` for `x ∈ M`, `v ∈ T_xM`.

Proof.  `|A|² = Σⱼ|Dν(x)(P_xeⱼ)|²` is continuous on `M`, homogeneous of degree `−2`, so
`|A|² ≤ c|x|⁻²`.  With the profile `p` (`Submission.codim1_hcp_sc_hardy_profile`), the function
`F = |A|²p(|x|)²/|x|²` is `Hᵐ`-integrable on `M` by the dyadic estimates of
`Submission.codim1_hcp_sc_cone_annuli_measure` (replacing the polar formula (5)).  Applying (3) to
`ψₙ = p(|x|)gₙ(|x|)` with the cut-offs `gₙ` of `Submission.codim1_hcp_sc_hardy_cutoff`
(`κₙ = 1/(n+2)`), using `|∇^Mψₙ|² = (p'gₙ + pgₙ')²` off the null spheres
(`Submission.codim1_hcp_sc_hardy_radial`), `(a + b)² ≤ (3/2)a² + 3b²` and `(ρp')² ≤ (11/10)²p²`,
gives `(37/200)∫gₙ²F ≤ 3∫|A|²p²gₙ'²`; dominated convergence yields `(37/200)∫_M F ≤ 0`.  Hence
`|A|² = 0` a.e. on `M`, so everywhere on `M` by continuity and density one, and finally
`Dν(x) = 0` on `T_xM`. -/
theorem Submission.codim1_hcp_sc_hardy_cone_flat : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ z ∈ M, Tendsto (fun s : ℝ => μHE[m] (M ∩ ball z s) / (unitBallVolume m * ENNReal.ofReal (s ^ m))) (𝓝[>] 0) (𝓝 1)) → (∀ ψ : Euclid P → ℝ, LocallyLipschitzOn M ψ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ψ x = 0) → 2 * (∫ x in M, ψ x ^ 2 * (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) / ‖x‖ ^ 2 ∂μHE[m]) ≤ ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * (∑ j : Fin P, (fderivWithin ℝ ψ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) → ∀ x ∈ M, ∀ v ∈ tangentSpace M x, fderiv ℝ ν x v = 0 := by
  intro P m A₀ M ν hm2 hm6 hA₀ hMA₀ h0M hMsub hcl hcone hfin hνO hν hdens hH3
  -- Step 1(a): cone facts; `M = M̄ \ {0}` is Borel
  have hM1 : IsEmbeddedSubmanifold 1 m M := hMsub 1
  have hx0 : ∀ x ∈ M, x ≠ 0 := fun x hx h => h0M (h ▸ hx)
  have hxpos : ∀ x ∈ M, 0 < ‖x‖ := fun x hx => norm_pos_iff.2 (hx0 x hx)
  have hclM : ∀ x ∈ closure M, x ≠ 0 → x ∈ M := fun x hx hx' =>
    (Set.mem_insert_iff.1 (hcl hx)).resolve_left hx'
  have hMmeas : MeasurableSet M := by
    have hMeq : M = closure M \ {0} := by
      ext x
      exact ⟨fun hx => ⟨subset_closure hx, hx0 x hx⟩, fun hx => hclM x hx.1 hx.2⟩
    rw [hMeq]
    exact isClosed_closure.measurableSet.diff (measurableSet_singleton 0)
  -- the sibling results
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hA₀ hMA₀ hM1 hν
  have hCN :=
    Submission.codim1_hcp_sc_cone_normal_homogeneous P m A₀ M ν hA₀ hMA₀ hM1 hcone hνO hν
  obtain ⟨hsph, hint_in, hint_out⟩ :=
    Submission.codim1_hcp_sc_cone_annuli_measure P m M h0M hcl hcone hfin
  obtain ⟨O, hO, hMO, hνC⟩ := hνO
  -- Step 1(b): `T_x = A₀ ∩ ν(x)^⊥` is a linear subspace
  have hspan : ∀ x ∈ M, ∀ w ∈ Submodule.span ℝ (tangentSpace M x), w ∈ tangentSpace M x := by
    intro x hx w hw
    have hT := (hNC x hx).1
    have hle : Submodule.span ℝ (tangentSpace M x) ≤ A₀ ⊓ LinearMap.ker (innerₛₗ ℝ (ν x)) := by
      rw [hT, Submodule.span_le]
      rintro v ⟨hvA, hvν⟩
      exact ⟨hvA, hvν⟩
    have hw' := hle hw
    rw [hT]
    exact ⟨hw'.1, hw'.2⟩
  -- `|A|²`, nonnegative and continuous on `M` (`P_x = Π_{A₀} − ν(x) ⊗ ν(x)`)
  set A2 : Euclid P → ℝ := fun x => ∑ j : Fin P,
    ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection
      (EuclideanSpace.single j 1))‖ ^ 2 with hA2
  have hA2nn : ∀ x, 0 ≤ A2 x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hA2cont : ContinuousOn A2 M := by
    have hD : ContinuousOn (fderiv ℝ ν) O := hνC.continuousOn_fderiv_of_isOpen hO (by simp)
    have hνc : ContinuousOn ν O := hνC.continuousOn
    have hÃ : ContinuousOn (fun y => ∑ j : Fin P, ‖fderiv ℝ ν y (A₀.starProjection
        (EuclideanSpace.single j 1) - inner ℝ (ν y) (EuclideanSpace.single j 1) • ν y)‖ ^ 2) O := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      have hinner : ContinuousOn
          (fun y => inner ℝ (ν y) (EuclideanSpace.single j (1 : ℝ) : Euclid P)) O :=
        hνc.inner continuousOn_const
      have hvec : ContinuousOn (fun y => A₀.starProjection (EuclideanSpace.single j (1 : ℝ) : Euclid P) -
          inner ℝ (ν y) (EuclideanSpace.single j (1 : ℝ) : Euclid P) • ν y) O :=
        continuousOn_const.sub (hinner.smul hνc)
      exact ((hD.clm_apply hvec).norm).pow 2
    refine (hÃ.mono hMO).congr fun x hx => ?_
    simp only [hA2, (hNC x hx).2]
  -- Step 1(d): `|A|²(tx) = t⁻²|A|²(x)`
  have hhom : ∀ x ∈ M, ∀ t : ℝ, 0 < t → A2 (t • x) = (t ^ 2)⁻¹ * A2 x := by
    intro x hx t ht
    have htx : t • x ∈ M := hcone t ht x hx
    obtain ⟨-, hνt, hD⟩ := (hCN x hx).2.2 t ht
    simp only [hA2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hP : (Submodule.span ℝ (tangentSpace M (t • x))).starProjection
        (EuclideanSpace.single j 1) = (Submodule.span ℝ (tangentSpace M x)).starProjection
        (EuclideanSpace.single j 1) := by
      rw [(hNC _ htx).2, (hNC x hx).2, hνt]
    have hv := hspan x hx _ (Submodule.starProjection_apply_mem
      (Submodule.span ℝ (tangentSpace M x)) (EuclideanSpace.single j 1))
    have h := hD _ hv
    rw [hP, ← h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos ht 2).ne', one_mul]
  -- Step 1(e): `|A|²(x) ≤ c|x|⁻²`, `c = max_{M ∩ S¹} |A|²`
  obtain ⟨cA, hcA0, hcA⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ M, A2 x ≤ c / ‖x‖ ^ 2 := by
    have hSph : IsCompact (closure M ∩ sphere (0 : Euclid P) 1) :=
      (isCompact_sphere 0 1).inter_left isClosed_closure
    have hSphM : closure M ∩ sphere (0 : Euclid P) 1 ⊆ M := fun y hy =>
      hclM y hy.1 (by rintro rfl; simp at hy)
    obtain ⟨c, hc⟩ := hSph.exists_bound_of_continuousOn (hA2cont.mono hSphM)
    refine ⟨max c 0, le_max_right _ _, fun x hx => ?_⟩
    have hr := hxpos x hx
    have hyM : ‖x‖⁻¹ • x ∈ M := hcone _ (inv_pos.2 hr) x hx
    have hy1 : ‖x‖⁻¹ • x ∈ sphere (0 : Euclid P) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hxy : ‖x‖ • (‖x‖⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hb := hc _ ⟨subset_closure hyM, hy1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hA2nn _)] at hb
    calc A2 x = A2 (‖x‖ • (‖x‖⁻¹ • x)) := by rw [hxy]
      _ = (‖x‖ ^ 2)⁻¹ * A2 (‖x‖⁻¹ • x) := hhom _ hyM _ hr
      _ ≤ (‖x‖ ^ 2)⁻¹ * max c 0 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = max c 0 / ‖x‖ ^ 2 := by rw [inv_mul_eq_div]
  -- Step 3: spheres are null
  have hae : ∀ c : ℝ, 0 < c → ∀ᵐ x ∂(μHE[m].restrict M), ‖x‖ ≠ c := by
    intro c hc
    rw [ae_restrict_iff' hMmeas]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsph c hc)] with x hx hxM hxc
    exact hx ⟨hxM, mem_sphere_zero_iff_norm.2 hxc⟩
  -- Step 4: the profile `p`
  obtain ⟨p, p', hpC, hp, hp0, hp', hpα, hpβ⟩ := Submission.codim1_hcp_sc_hardy_profile m hm2 hm6
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  -- Step 5: `F = |A|² p(r)²/r²` is integrable on `M`
  set F : Euclid P → ℝ := fun x => A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x =>
    div_nonneg (mul_nonneg (hA2nn x) (sq_nonneg _)) (sq_nonneg _)
  have hpc : ContinuousOn (fun x : Euclid P => p ‖x‖) M := fun x hx =>
    ((hp _ (hxpos x hx)).continuousAt.comp continuous_norm.continuousAt).continuousWithinAt
  have hFcont : ContinuousOn F M :=
    (hA2cont.mul (hpc.pow 2)).div (continuous_norm.continuousOn.pow 2)
      fun x hx => (pow_pos (hxpos x hx) 2).ne'
  have hFle : ∀ x ∈ M, ∀ e : ℝ, p ‖x‖ ^ 2 ≤ ‖x‖ ^ e * ‖x‖ ^ 4 → F x ≤ cA * ‖x‖ ^ e := by
    intro x hx e he
    have hr := hxpos x hx
    have hr2 : 0 < ‖x‖ ^ 2 := by positivity
    show A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 ≤ cA * ‖x‖ ^ e
    rw [div_le_iff₀ hr2]
    calc A2 x * p ‖x‖ ^ 2 ≤ (cA / ‖x‖ ^ 2) * (‖x‖ ^ e * ‖x‖ ^ 4) :=
          mul_le_mul (hcA x hx) he (sq_nonneg _) (by positivity)
      _ = cA * ‖x‖ ^ e * ‖x‖ ^ 2 := by field_simp
  have hFint : Integrable F (μHE[m].restrict M) := by
    refine ⟨hFcont.aestronglyMeasurable hMmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hFnn),
      ← lintegral_inter_add_sdiff _ M (measurableSet_ball (x := (0 : Euclid P)) (ε := 1))]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · calc ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal (F x) ∂μHE[m]
          ≤ ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal cA * ENNReal.ofReal (‖x‖ ^ (-(9 / 5) : ℝ))
              ∂μHE[m] := by
            refine setLIntegral_mono' (hMmeas.inter measurableSet_ball) fun x hx => ?_
            rw [← ENNReal.ofReal_mul hcA0]
            exact ENNReal.ofReal_le_ofReal (hFle x hx.1 _ (hpα _ (hxpos x hx.1)))
        _ = ENNReal.ofReal cA * ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal (‖x‖ ^ (-(9 / 5) : ℝ))
              ∂μHE[m] := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.2 (hint_in _ (by linarith)))
    · calc ∫⁻ x in M \ ball 0 1, ENNReal.ofReal (F x) ∂μHE[m]
          ≤ ∫⁻ x in M \ ball 0 1, ENNReal.ofReal cA * ENNReal.ofReal (‖x‖ ^ (-(m : ℝ) - 1 / 5))
              ∂μHE[m] := by
            refine setLIntegral_mono' (hMmeas.diff measurableSet_ball) fun x hx => ?_
            rw [← ENNReal.ofReal_mul hcA0]
            exact ENNReal.ofReal_le_ofReal (hFle x hx.1 _ (hpβ _ (hxpos x hx.1)))
        _ = ENNReal.ofReal cA * ∫⁻ x in M \ ball 0 1, ENNReal.ofReal (‖x‖ ^ (-(m : ℝ) - 1 / 5))
              ∂μHE[m] := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.2 (hint_out _ (by linarith)))
  -- Step 6: the cut-offs `gₙ`, `κₙ = 1/(n+2)`
  have hκ0 : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hκ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < 1 := fun n => by
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  choose g g' hgL hg01 hgsupp hgd hg'meas hg'bd hg1 using
    fun n : ℕ => Submission.codim1_hcp_sc_hardy_cutoff (1 / ((n : ℝ) + 2)) (hκ0 n) (hκ1 n)
  have hXbd : ∀ n x, ‖g n ‖x‖ ^ 2 * F x‖ ≤ F x := by
    intro n x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hFnn x))]
    have h01 := hg01 n ‖x‖
    have h1 : g n ‖x‖ ^ 2 ≤ 1 := by nlinarith [h01.1, h01.2]
    calc g n ‖x‖ ^ 2 * F x ≤ 1 * F x := mul_le_mul_of_nonneg_right h1 (hFnn x)
      _ = F x := one_mul _
  have hYbd : ∀ n, ∀ x ∈ M, ‖A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2‖ ≤ 4 * F x := by
    intro n x hx
    have hr := hxpos x hx
    have hb := hg'bd n ‖x‖ hr
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (hA2nn x) (sq_nonneg _)) (sq_nonneg _))]
    have h4 : g' n ‖x‖ ^ 2 ≤ 4 / ‖x‖ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hb]
    calc A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ≤ A2 x * p ‖x‖ ^ 2 * (4 / ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (hA2nn x) (sq_nonneg _))
      _ = 4 * F x := by simp only [hF]; ring
  have hXint : ∀ n, Integrable (fun x => g n ‖x‖ ^ 2 * F x) (μHE[m].restrict M) := by
    intro n
    obtain ⟨K, hK⟩ := hgL n
    exact hFint.mono' ((((hK.continuous.comp continuous_norm).continuousOn.pow 2).mul
      hFcont).aestronglyMeasurable hMmeas) (ae_of_all _ (hXbd n))
  have hYint : ∀ n, Integrable (fun x => A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2) (μHE[m].restrict M) := by
    intro n
    refine (hFint.const_mul 4).mono' (((hA2cont.mul (hpc.pow 2)).aestronglyMeasurable
      hMmeas).mul (((hg'meas n).comp measurable_norm).pow_const 2).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' hMmeas]
    exact ae_of_all _ (hYbd n)
  -- Step 6(c)–(e): (3) for `ψₙ = p(r)gₙ(r)` gives `(37/200)∫gₙ²F ≤ 3∫|A|²p²gₙ'²`
  have hkey : ∀ n : ℕ, 37 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) ≤
      3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
    intro n
    set κ : ℝ := 1 / ((n : ℝ) + 2) with hκ
    have hκ' : 0 < κ := hκ0 n
    obtain ⟨K, hK⟩ := hgL n
    -- (a) `ψₙ` is locally Lipschitz on `M`
    have hφL : LocallyLipschitzOn M (fun y : Euclid P => p ‖y‖ * g n ‖y‖) := by
      intro x hx
      obtain ⟨K₁, t, ht, hK₁⟩ :=
        ((hpC ‖x‖ (hxpos x hx)).comp x (contDiffAt_norm ℝ (hx0 x hx))).exists_lipschitzOnWith
      have hxt : x ∈ t := mem_of_mem_nhds ht
      refine ⟨_, t ∩ ball x 1, mem_nhdsWithin_of_mem_nhds (inter_mem ht (ball_mem_nhds x one_pos)),
        Submission.codim1_hcp_sc_hardy_lipschitzOnWith_mul (Bf := |p ‖x‖| + K₁) (Bg := 1)
          (hK₁.mono inter_subset_left) ((hK.comp lipschitzWith_one_norm).lipschitzOnWith) ?_ ?_⟩
      · intro y hy
        have h1 := hK₁.dist_le_mul y hy.1 x hxt
        have h2 : dist y x < 1 := hy.2
        rw [Real.dist_eq] at h1
        have h3 : (K₁ : ℝ) * dist y x ≤ K₁ := by
          calc (K₁ : ℝ) * dist y x ≤ K₁ * 1 := mul_le_mul_of_nonneg_left h2.le K₁.2
            _ = K₁ := mul_one _
        have h4 := abs_sub_abs_le_abs_sub (p ‖y‖) (p ‖x‖)
        simp only [Function.comp] at h1 ⊢
        linarith
      · intro y _
        have h01 := hg01 n ‖y‖
        rw [abs_of_nonneg h01.1]
        exact h01.2
    -- (b) `ψₙ` vanishes on `M` outside the compact `M̄ ∩ {κ/2 ≤ r ≤ 2/κ} ⊆ M`
    have hφsupp : ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧
        ∀ x ∈ M, x ∉ C → p ‖x‖ * g n ‖x‖ = 0 := by
      refine ⟨closure M ∩ (closedBall 0 (2 / κ) \ ball 0 (κ / 2)),
        ((isCompact_closedBall 0 _).diff isOpen_ball).inter_left isClosed_closure, ?_, ?_⟩
      · rintro x ⟨hx, -, hx2⟩
        refine hclM x hx ?_
        rintro rfl
        exact hx2 (mem_ball_self (by positivity))
      · intro x hx hxC
        have hout : ‖x‖ < κ / 2 ∨ 2 / κ < ‖x‖ := by
          rcases lt_or_ge ‖x‖ (κ / 2) with h | h
          · exact Or.inl h
          rcases lt_or_ge (2 / κ) ‖x‖ with h' | h'
          · exact Or.inr h'
          exact absurd ⟨subset_closure hx, mem_closedBall_zero_iff.2 h', fun hb => by
            rw [mem_ball_zero_iff] at hb; linarith⟩ hxC
        rw [hgsupp n ‖x‖ hout, mul_zero]
    -- (c) apply (3)
    have h3 := hH3 (fun y : Euclid P => p ‖y‖ * g n ‖y‖) hφL hφsupp
    -- (d) the right side off the null spheres `r ∈ {κ/2, κ, 1/κ, 2/κ}`
    have hbound : ∫ x in M, A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ∂μHE[m] ≤
        ∫ x in M, (363 / 200 * (g n ‖x‖ ^ 2 * F x) + 3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2))
          ∂μHE[m] := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (hA2nn x) (sq_nonneg _))
        (((hXint n).const_mul _).add ((hYint n).const_mul _)) ?_
      rw [EventuallyLE, ae_restrict_iff' hMmeas]
      refine ae_of_all _ fun x hx => ?_
      have hr := hxpos x hx
      have hpp := hp' ‖x‖ hr
      have h1 : (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ≤
          3 / 2 * (p' ‖x‖ * g n ‖x‖) ^ 2 + 3 * (p ‖x‖ * g' n ‖x‖) ^ 2 := by
        nlinarith [sq_nonneg (p' ‖x‖ * g n ‖x‖ - 2 * (p ‖x‖ * g' n ‖x‖))]
      have h2 : p' ‖x‖ ^ 2 ≤ 121 / 100 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [hpp]
      have h2' : (p' ‖x‖ * g n ‖x‖) ^ 2 ≤ 121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) := by
        calc (p' ‖x‖ * g n ‖x‖) ^ 2 = g n ‖x‖ ^ 2 * p' ‖x‖ ^ 2 := by ring
          _ ≤ g n ‖x‖ ^ 2 * (121 / 100 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = 121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) := by ring
      calc A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2
          ≤ A2 x * (3 / 2 * (121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2))) +
              3 * (p ‖x‖ * g' n ‖x‖) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (hA2nn x)
            linarith
        _ = 363 / 200 * (g n ‖x‖ ^ 2 * F x) + 3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2) := by
            simp only [hF]; ring
    have hsplit : ∫ x in M, (363 / 200 * (g n ‖x‖ ^ 2 * F x) +
          3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2)) ∂μHE[m] =
        363 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) +
          3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
      rw [integral_add ((hXint n).const_mul _) ((hYint n).const_mul _), integral_const_mul,
        integral_const_mul]
    have hineq : 2 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) ≤
        363 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) +
          3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
      calc 2 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m])
          = 2 * ∫ x in M, (p ‖x‖ * g n ‖x‖) ^ 2 * A2 x / ‖x‖ ^ 2 ∂μHE[m] := by
            congr 1
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            simp only [hF]
            ring
        _ ≤ ∫ x in M, A2 x * ∑ j : Fin P, (fderivWithin ℝ (fun y : Euclid P => p ‖y‖ * g n ‖y‖)
              M x ((Submodule.span ℝ (tangentSpace M x)).starProjection
                (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m] := h3
        _ = ∫ x in M, A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ∂μHE[m] := by
            refine integral_congr_ae ?_
            filter_upwards [hae (κ / 2) (by positivity), hae κ hκ', hae (1 / κ) (by positivity),
              hae (2 / κ) (by positivity), self_mem_ae_restrict hMmeas] with x h1 h2 h3 h4 hxM
            have hrad := Submission.codim1_hcp_sc_hardy_radial P M x (fun r => p r * g n r) _
              (hx0 x hxM) (hCN x hxM).1 ((hp _ (hxpos x hxM)).mul (hgd n _ h1 h2 h3 h4))
            exact congrArg (fun s => A2 x * s) hrad
        _ ≤ _ := hbound
        _ = _ := hsplit
    linarith
  -- Step 7: `κₙ → 0`; for `x ∈ M`, eventually `gₙ(|x|) = 1` and `gₙ'(|x|) = 0`
  have hev : ∀ x ∈ M, ∀ᶠ n : ℕ in atTop, g n ‖x‖ = 1 ∧ g' n ‖x‖ = 0 := by
    intro x hx
    have hr := hxpos x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖x‖) ‖x‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hm1 := le_max_left (1 / ‖x‖) ‖x‖
    have hm2 := le_max_right (1 / ‖x‖) ‖x‖
    have h1 : 1 / ((n : ℝ) + 2) < ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      have h : 1 / ‖x‖ < n + 2 := by linarith
      rw [div_lt_iff₀ hr] at h
      linarith
    have h2 : ‖x‖ < 1 / (1 / ((n : ℝ) + 2)) := by
      rw [one_div_one_div]
      linarith
    exact hg1 n ‖x‖ h1 h2
  have hXlim : Tendsto (fun n => ∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) atTop
      (𝓝 (∫ x in M, F x ∂μHE[m])) := by
    refine tendsto_integral_of_dominated_convergence F (fun n => (hXint n).aestronglyMeasurable)
      hFint (fun n => ae_of_all _ (hXbd n)) ?_
    rw [ae_restrict_iff' hMmeas]
    refine ae_of_all _ fun x hx => tendsto_const_nhds.congr' ?_
    filter_upwards [hev x hx] with n hn
    rw [hn.1]
    ring
  have hYlim : Tendsto (fun n => ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m]) atTop
      (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μHE[m].restrict M)
      (f := fun _ => (0 : ℝ)) (fun x => 4 * F x) (fun n => (hYint n).aestronglyMeasurable)
      (hFint.const_mul 4) (fun n => (ae_restrict_iff' hMmeas).2 (ae_of_all _ (hYbd n))) ?_
    · simpa using h
    rw [ae_restrict_iff' hMmeas]
    refine ae_of_all _ fun x hx => tendsto_const_nhds.congr' ?_
    filter_upwards [hev x hx] with n hn
    rw [hn.2]
    ring
  -- Step 8: `(37/200)∫_M F ≤ 0`, so `∫_M F = 0`
  have hJ0 : ∫ x in M, F x ∂μHE[m] = 0 := by
    have hlim := le_of_tendsto_of_tendsto' (hXlim.const_mul (37 / 200)) (hYlim.const_mul 3) hkey
    rw [mul_zero] at hlim
    have hJnn : 0 ≤ ∫ x in M, F x ∂μHE[m] := integral_nonneg hFnn
    linarith
  -- Step 9: `|A|² = 0` a.e. on `M`
  have hAE : ∀ᵐ x ∂μHE[m], x ∈ M → A2 x = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hFnn) hFint).1 hJ0
    rw [EventuallyEq, ae_restrict_iff' hMmeas] at h
    filter_upwards [h] with x hx hxM
    have hFx : A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 = 0 := hx hxM
    have hr := hxpos x hxM
    have hpx := hp0 ‖x‖ hr
    rcases div_eq_zero_iff.1 hFx with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (pow_pos hpx 2).ne'
    · exact absurd h1 (pow_pos hr 2).ne'
  -- Step 10: `|A|² ≡ 0` on `M` (continuity and density one)
  have hA2zero : ∀ x ∈ M, A2 x = 0 := by
    intro x₀ hx₀
    by_contra hne
    have hpos : 0 < A2 x₀ := lt_of_le_of_ne (hA2nn x₀) (Ne.symm hne)
    obtain ⟨δ, hδ, hδA⟩ := Metric.continuousOn_iff.1 hA2cont x₀ hx₀ (A2 x₀) hpos
    have hev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        0 < μHE[m] (M ∩ ball x₀ s) / (unitBallVolume m * ENNReal.ofReal (s ^ m)) :=
      (hdens x₀ hx₀).eventually (lt_mem_nhds zero_lt_one)
    have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < δ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)
    obtain ⟨s, hs1, hs2⟩ := (hev1.and hev2).exists
    have hnull : μHE[m] (M ∩ ball x₀ s) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hAE)
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hy.1, ?_⟩
      have hd := hδA y hy.1 (lt_trans (mem_ball.1 hy.2) hs2)
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).1
      linarith
    rw [hnull, ENNReal.zero_div] at hs1
    exact lt_irrefl 0 hs1
  -- Step 11: `Dν(x)(P_xeⱼ) = 0` for all `j`, hence `Dν(x) = 0` on `T_x`
  intro x hx v hv
  have hA2x : A2 x = 0 := hA2zero x hx
  simp only [hA2] at hA2x
  have hj : ∀ j : Fin P, fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection
      (EuclideanSpace.single j 1)) = 0 := by
    intro j
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hA2x j
      (Finset.mem_univ j)
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
  have hcomp : (fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection = 0 := by
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin P) ℝ).toBasis.ext fun j => ?_
    simp [hj j]
  have hPv : (Submodule.span ℝ (tangentSpace M x)).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span hv)
  have h := congrArg (fun L : Euclid P →L[ℝ] Euclid P => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply, hPv, zero_apply] at h
  exact h

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
