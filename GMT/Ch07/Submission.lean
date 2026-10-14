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

/-- **The mass measure of a current vanishes off its support**: assume (VO), i.e. every current
`S ∈ 𝒟ₙ(U)` kills the test forms whose support is disjoint from `spt S`.  If `X ∈ 𝒟ₖ(ℝᴾ)` and `μ`
is a measure with `M_W(X) = μ(W)` for every open `W`, then `μ(ℝᴾ \ spt X) = 0`.
`(spt X)ᶜ` is the open zero region `Z` of `X`, so `μ((spt X)ᶜ) = M_Z(X)`.  Every form admissible
for `M_Z` is supported in `Z`, away from `spt X`, so `X` kills it by (VO), and `M_Z(X) = 0`. -/
theorem Submission.dimred_mbl_dtsd_sh_measure_compl_support_eq_zero : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)), (∀ W : Set (Euclid P), IsOpen W → X.massOn W = μ W) → μ X.supportᶜ = 0 := by
  intro hVO P k X μ hμ
  -- `(spt X)ᶜ = Z`, the open zero region of `X`
  have hcompl : X.supportᶜ = X.zeroRegion := by
    ext x; simp [GeometricCurrentOn.support]
  -- `μ((spt X)ᶜ) = M_Z(X)`, the supremum of `ofReal X(ω)` over the `ω` admissible for `M_Z`
  rw [hcompl, ← hμ _ X.isOpen_zeroRegion]
  refine le_antisymm (sSup_le ?_) zero_le
  -- an admissible `ω` has `tsupport ω ⊆ Z = (spt X)ᶜ`, so `X(ω) = 0` by (VO)
  rintro _ ⟨ω, hω, rfl⟩
  have h0 : X ω = 0 := by
    apply hVO
    refine Set.disjoint_of_subset_left hω.1 ?_
    rw [← hcompl]
    exact disjoint_compl_left
  simp [h0]
/-- **Restriction of an integer multiplicity representation** (Simon Ch. 6, 3.1).  For
`R = (M, θ, ξ)` with weight `μ_R = θ Hⁿ⌞M`: (a) `μ_R ≪ Hⁿ⌞M`; (b) `ξ` is `μ_R`-a.e. strongly
measurable; (c) for Borel `E` and `R' = (M ∩ E, θ, ξ)`, `μ_{R'} = μ_R⌞E` and
`R'(ω) = ∫_E ⟨ω, ξ⟩ dμ_R` for every `n`-form `ω`. -/
theorem Submission.lcmp_imRep_measure_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.measure ≪ μHE[n].restrict R.carrier ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ (E : Set (Euclid P)) (R' : IMRep U n), MeasurableSet E → R'.carrier = R.carrier ∩ E → R'.mult = R.mult → R'.orient = R.orient → R'.measure = R.measure.restrict E ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x in E, R.orient x (ω x) ∂R.measure := by
  intro P n U R
  -- (a) a measure with a density is absolutely continuous; (b) so `ξ` is `μ_R`-measurable
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  refine ⟨hac, R.aestronglyMeasurable_orient.mono_ac hac, ?_⟩
  intro E R' hE hc hm ho
  -- (c), weights: `((Hⁿ⌞M).withDensity θ)⌞E = (Hⁿ⌞(E ∩ M)).withDensity θ = μ_{R'}`
  have hmeasEq : R'.measure = R.measure.restrict E := by
    unfold IMRep.measure
    rw [restrict_withDensity hE, Measure.restrict_restrict hE, hc, hm, inter_comm]
  refine ⟨hmeasEq, fun ω => ?_⟩
  -- (c), actions: `∫ h d(λ.withDensity θ) = ∫ θ h dλ` for the Borel density `θ : ℝᴾ → [0, ∞)`
  have hmult : (fun x => (R'.mult x : ℝ≥0∞)) = fun x => (((R'.mult x : NNReal)) : ℝ≥0∞) := by
    funext x
    simp
  have hmeas : Measurable fun x => ((R'.mult x : ℕ) : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R'.measurable_mult
  rw [← hmeasEq]
  unfold IMRep.action IMRep.measure
  rw [hmult, integral_withDensity_eq_integral_smul hmeas]
  congr 1
  funext x
  rw [ho, NNReal.smul_def, smul_eq_mul]
  norm_cast

/-- **Mass measure of a finite-mass integer multiplicity current on `ℝᴾ`** (Simon Ch. 6, proof of
5.1, (8)–(10)).  For `T = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)` with `M(T) < ∞`, the weight `μ_T = θ Hⁿ⌞M` is a
finite measure with `M_W(T) = μ_T(W)` for open `W` and `μ_T(ℝᴾ \ spt T) = 0`, `ξ` is
`μ_T`-measurable with `|ξ| ≤ 1` `μ_T`-a.e., `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T`, and every current
`ω ↦ ∫_E ⟨ω, ξ⟩ dμ_T` with `E` Borel is integer multiplicity, being `τ(M ∩ E, θ, ξ)`. -/
theorem Submission.dimred_mbl_dtsd_sh_im_mass_measure : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) n), IsIntegerMultiplicity T → T.mass < ∞ → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), IsFiniteMeasure μ ∧ AEStronglyMeasurable ξ μ ∧ (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ μ T.supportᶜ = 0 ∧ (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), MeasurableSet E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → IsIntegerMultiplicity X) := by
  intro hVO hMR hIMC P n T hT hTm
  -- `T = τ(M, θ, ξ)`; take `μ = θ Hⁿ⌞M` and the orientation `ξ`
  obtain ⟨R, hR⟩ := hT
  obtain ⟨hac, hξm, hres⟩ := Submission.lcmp_imRep_measure_restrict P n univ R
  -- (5) by (MR) in the open set `ℝᴾ`; then (1) from `μ(ℝᴾ) = M(T) < ∞`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W :=
    hMR P n univ T R isOpen_univ hR
  have hfin : IsFiniteMeasure R.measure := ⟨by rw [← hmass univ isOpen_univ]; exact hTm⟩
  -- (3) transfers from `Hⁿ⌞M` to `μ ≪ Hⁿ⌞M`; (6) is the sibling `null_off_support`
  refine ⟨R.measure, R.orient, hfin, hξm, hac.ae_le (hIMC.2.2.2 P n univ R), ?_, hmass,
    Submission.dimred_mbl_dtsd_sh_measure_compl_support_eq_zero hVO P n T R.measure hmass, ?_⟩
  · -- (4): restriction of `R` to `E = ℝᴾ`
    intro ω
    rw [hR ω, (hres univ R MeasurableSet.univ (Set.inter_univ _).symm rfl rfl).2, setIntegral_univ]
  · -- (7): `τ(M ∩ E, θ, ξ)` from (IMC)(b) represents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ`
    intro E X hE hX
    obtain ⟨A, R', -, hcar, hmult, horient⟩ := hIMC.2.1 P n univ R E isOpen_univ hE
    refine ⟨R', fun ω => ?_⟩
    rw [hX ω, (hres E R' hE hcar hmult horient).2]

/-- **A finite-mass current on `ℝᴾ` is represented by a finite measure concentrated on its
support** (Simon 6.5.1, displays (8)–(10): the measure `(μ_∂, ξ_∂)` of `∂T`).  Assume (VO) and
(REP).  If `X ∈ 𝒟_k(ℝᴾ)` has `M(X) < ∞`, then `M_W(X) ≤ M(X) < ∞` for every `W`, so (REP) with
`U = ℝᴾ` gives `μ`, `ξ` with `M_W(X) = μ(W)` for open `W`, `ξ` `μ`-a.e. strongly measurable,
`|⟨α, ξ(x)⟩| ≤ |α|` for every `x` and `X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`.  Then
`μ(ℝᴾ) = M(X) < ∞`, and `μ(ℝᴾ \ spt X) = 0` by `null_off_support`. -/
theorem Submission.dimred_mbl_dtsd_sh_finite_mass_measure : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass < ∞ → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsFiniteMeasure μ ∧ AEStronglyMeasurable ξ μ ∧ (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ W : Set (Euclid P), IsOpen W → X.massOn W = μ W) ∧ μ X.supportᶜ = 0 := by
  intro hVO hREP P k X hX
  -- (REP) with `U = ℝᴾ`: `M_W(X) ≤ M(X) < ∞` for every `W`
  obtain ⟨μ, ξ, -, -, hmass, hξm, hξb, hrep, -⟩ := hREP P k univ X isOpen_univ
    (fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX)
  -- `μ(ℝᴾ) = M_{ℝᴾ}(X) = M(X) < ∞`
  have hfin : IsFiniteMeasure μ := ⟨by rw [← hmass univ isOpen_univ]; exact hX⟩
  -- the everywhere bound holds `μ`-a.e.; `μ(ℝᴾ \ spt X) = 0` by `null_off_support`
  exact ⟨μ, ξ, hfin, hξm, Filter.Eventually.of_forall (fun x α => hξb x α), hrep, hmass,
    Submission.dimred_mbl_dtsd_sh_measure_compl_support_eq_zero hVO P k X μ hmass⟩
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

/-- **A test form has bounded Euclidean coefficient norm** (Simon Ch. 6, (1.15):
`|ω| = sup_x |ω(x)|` is finite for `ω ∈ 𝒟ⁿ(U)`).  `ω` is `C^∞`, hence continuous, with compact
support; the coefficient norm `N` is continuous (`rsd_mw_tfa_norm_props`) and `N 0 = 0`, so
`x ↦ N (ω x)` is continuous with compact support, hence bounded by some `C`, and
`c = max C 0 + 1` is a positive bound. -/
theorem Submission.cmc_fc_sc_testForm_coeff_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U n), ∃ c : ℝ, 0 < c ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c := by
  intro P n U ω
  -- Step 1: `ω` is `C^∞`, hence continuous, and has compact support
  have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  -- Step 2: `x ↦ N (ω x)` is continuous, with compact support because `N 0 = 0`
  have hcont : Continuous fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) :=
    (Submission.rsd_mw_tfa_norm_props P n).2.2.2.comp (ContDiff.continuous hsmooth)
  have hcs : HasCompactSupport fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) :=
    HasCompactSupport.comp_left (g := covectorEuclideanNorm) ω.property.1.2
      (covectorEuclideanNorm_zero P n)
  -- Step 3: a continuous compactly supported real function is bounded by some `C`
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  -- Step 4: `c = max C 0 + 1 > 0` and `N (ω x) ≤ |N (ω x)| ≤ C ≤ max C 0 < c`
  refine ⟨max C 0 + 1, by positivity, fun x => ?_⟩
  have hx := hC x
  rw [Real.norm_eq_abs] at hx
  linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)),
    le_max_left C 0]
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

/-- **Simon 6.5.1, displays (8)–(10)** (shell series): let `X ∈ 𝒟_k(ℝ^P)` be represented by a
finite measure `μ` carried by `spt X` and an a.e. strongly measurable `ξ` with `|ξ(x)(α)| ≤ |α|`,
let `d` be continuous and `r` strictly decreasing with `μ({d < r_j}) → 0`, let `A_j` be the
restriction of `X` to `{d < r_j}`, and `Y_0 = X - A_0`, `Y_{j+1} = A_j - A_{j+1}`.  Then `Y_j` is
the restriction of `X` to the half-open shell `E_j`, `Σ_j Y_j(ω) = X(ω)`,
`spt Y_j ⊆ spt X ∩ {r_j ≤ d}`, `spt A_j ⊆ spt X`, `M(Y_0) ≤ μ(ℝ^P)` and
`M(Y_{j+1}) ≤ μ({d < r_j})`.  Each `ω` is bounded, so `ξ(ω)` is `μ`-integrable; the shells are
pairwise disjoint, so `|Y_j(ω)| ≤ c_ω μ(E_j)` is summable, and the partial sums
`X(ω) - A_N(ω)` tend to `X(ω)` because `|A_N(ω)| ≤ c_ω μ({d < r_N}) → 0`. -/
theorem Submission.dimred_mbl_dtsd_sh_shell_series : (∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support)) → (∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (A Y : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (d : Euclid P → ℝ) (r : ℕ → ℝ), IsFiniteMeasure μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → μ X.supportᶜ = 0 → Continuous d → StrictAnti r → Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), A j ω = ∫ x in {x | d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = X ω - A 0 ω) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = A j ω - A (j + 1) ω) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω)) ∧ (∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (A j).support ⊆ X.support) ∧ (Y 0).mass ≤ μ univ ∧ (∀ j, (Y (j + 1)).mass ≤ μ {x | d x < r j}) := by
  intro hS hML P k X A Y μ ξ d r hμ hξm hξb hnull hd hr htend hX hA hY0 hYs
  have hdm : Measurable d := hd.measurable
  -- Step 1: the integrand `x ↦ ξ x (ω x)` is bounded, a.e. strongly measurable, integrable
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Continuous (ω : DifferentialForm (Euclid P) k) := fun ω => ω.property.1.1.continuous
  have hnormcont : Continuous (fun α : Covector (Euclid P) k => covectorEuclideanNorm α) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]; exact (continuous_eval_const _).pow 2
    · simp only [hI, ite_false]; exact continuous_const
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ c : ℝ,
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c := by
    intro ω
    obtain ⟨c, hc⟩ := (hnormcont.comp (hcont ω)).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k))
    exact ⟨c, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hc x)⟩
  have hfm : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω =>
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P k) (α : Covector (Euclid P) k) => L α)
      isBoundedBilinearMap_apply.continuous hξm (hcont ω).aestronglyMeasurable
  have hfi : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω => by
    obtain ⟨c, hc⟩ := hbound ω
    exact Integrable.of_bound (hfm ω) c
      (hξb.mono fun x hx => by rw [Real.norm_eq_abs]; exact (hx _).trans (hc x))
  -- Step 2: the shell integral formulas
  have hlt : ∀ j, MeasurableSet {x | d x < r j} := fun j => measurableSet_lt hdm measurable_const
  have hge : ∀ j, MeasurableSet {x | r j ≤ d x} := fun j => measurableSet_le measurable_const hdm
  have hY0' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro ω
    rw [hY0, hX, hA, ← integral_add_compl (hlt 0) (hfi ω)]
    have h : {x | d x < r 0}ᶜ = {x | r 0 ≤ d x} := by ext x; simp
    rw [h]; ring
  have hYs' : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j},
        ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    have hsub : {x | d x < r (j + 1)} ⊆ {x | d x < r j} :=
      fun x hx => lt_trans hx (hr (Nat.lt_succ_self j))
    have hset : {x | d x < r j} \ {x | d x < r (j + 1)} = {x | r (j + 1) ≤ d x ∧ d x < r j} := by
      ext x; simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]; exact and_comm
    rw [hYs, hA, hA, ← setIntegral_sdiff (hlt (j + 1)) (hfi ω).integrableOn hsub, hset]
  -- the shells as one family
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → Set (Euclid P), E 0 = {x | r 0 ≤ d x} ∧
      ∀ i, E (i + 1) = {x | r (i + 1) ≤ d x ∧ d x < r i} :=
    ⟨fun j => match j with
      | 0 => {x | r 0 ≤ d x}
      | i + 1 => {x | r (i + 1) ≤ d x ∧ d x < r i}, rfl, fun _ => rfl⟩
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    cases j with
    | zero => rw [hE0]; exact hge 0
    | succ i => rw [hEs]; exact (hge (i + 1)).inter (hlt i)
  have hEge : ∀ j, E j ⊆ {x | r j ≤ d x} := by
    intro j
    cases j with
    | zero => rw [hE0]
    | succ i => rw [hEs]; exact fun x hx => hx.1
  have hElt : ∀ i j, i < j → E j ⊆ {x | d x < r i} := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j =>
      rw [hEs]
      exact fun x hx => lt_of_lt_of_le hx.2 (hr.antitone (by omega))
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r i ≤ d x from hEge i hxi) (not_le.2 (hElt i j h hxj))
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r j ≤ d x from hEge j hxj) (not_le.2 (hElt j i h hxi))
  have hYE : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y j ω = ∫ x in E j, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    cases j with
    | zero => rw [hE0]; exact hY0' ω
    | succ i => rw [hEs]; exact hYs' i ω
  -- Step 3: masses (ML)
  have hmassY : ∀ j, (Y j).massOn univ ≤ μ (E j) := fun j =>
    (hML P k univ (Y j) μ ξ (E j) univ hξb (hYE j)).trans (measure_mono inter_subset_left)
  have hmassA : ∀ j, (A j).massOn univ ≤ μ {x | d x < r j} := fun j =>
    (hML P k univ (A j) μ ξ _ univ hξb (hA j)).trans (measure_mono inter_subset_left)
  -- Step 4: evaluation bound (EB + ML)
  have hEB : ∀ (Z : GeometricCurrentOn (univ : Set (Euclid P)) k) (S : Set (Euclid P))
      (ω : TestFormOn (univ : Set (Euclid P)) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c) →
      Z.massOn univ ≤ μ S → |Z ω| ≤ c * (μ S).toReal := by
    intro Z S ω c hc hZ
    have hne : Z.massOn univ ≠ ∞ := (hZ.trans_lt (measure_lt_top μ S)).ne
    have h0c : 0 ≤ c := (covectorEuclideanNorm_nonneg _).trans (hc 0)
    calc |Z ω| ≤ c * (Z.massOn univ).toReal :=
          Submission.cmr_abs_apply_le_massOn P k univ univ Z ω c hne (subset_univ _) hc
      _ ≤ c * (μ S).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ S) hZ) h0c
  -- Step 5: HasSum
  have hpart : ∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (N : ℕ),
      ∑ j ∈ Finset.range (N + 1), Y j ω = X ω - A N ω := by
    intro ω N
    induction N with
    | zero => simp [hY0]
    | succ N ih => rw [Finset.sum_range_succ, ih, hYs]; ring
  have hsum : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω) := by
    intro ω
    obtain ⟨c, hc⟩ := hbound ω
    have hsumE : ∑' j, μ (E j) ≠ ∞ := by
      rw [← measure_iUnion hdisj hEm]; exact measure_ne_top μ _
    have hsummable : Summable (fun j => Y j ω) := by
      refine Summable.of_norm_bounded ((ENNReal.summable_toReal hsumE).mul_left c) (fun j => ?_)
      rw [Real.norm_eq_abs]; exact hEB (Y j) (E j) ω c hc (hmassY j)
    rw [hsummable.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    simp only [hpart]
    have hbd : ∀ n, ‖A n ω‖ ≤ c * (μ {x | d x < r n}).toReal := fun n => by
      rw [Real.norm_eq_abs]; exact hEB (A n) _ ω c hc (hmassA n)
    have hto : Tendsto (fun n => c * (μ {x | d x < r n}).toReal) atTop (𝓝 0) := by
      have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul c
      simpa using h
    simpa using tendsto_const_nhds.sub (squeeze_zero_norm hbd hto)
  -- Step 6: supports (S(i), S(ii))
  have hae : ∀ᵐ x ∂μ, x ∈ X.support := by
    have h := measure_eq_zero_iff_ae_notMem.1 hnull
    exact h.mono fun x hx => by simpa using hx
  have hvanish : ∀ (S F : Set (Euclid P)) (ω : TestFormOn (univ : Set (Euclid P)) k),
      MeasurableSet S → S ⊆ F →
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (X.support ∩ F) →
      ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ = 0 := by
    intro S F ω hSm hSF hdisj
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hae] with x hxS hxX
    have hx : x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
      fun h => Set.disjoint_left.1 hdisj h ⟨hxX, hSF hxS⟩
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hsptY : ∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x} := by
    intro j
    refine (hS P k).1 _ _ (((hS P k).2.1 X).inter (isClosed_le continuous_const hd))
      (fun ω hω => ?_)
    rw [hYE j]
    exact hvanish (E j) _ ω (hEm j) (hEge j) hω
  have hsptA : ∀ j, (A j).support ⊆ X.support := by
    intro j
    refine (hS P k).1 _ _ ((hS P k).2.1 X) (fun ω hω => ?_)
    rw [hA j]
    exact hvanish _ univ ω (hlt j) (subset_univ _) (by rwa [inter_univ])
  refine ⟨hY0', hYs', hsum, hsptY, hsptA, (hmassY 0).trans (measure_mono (subset_univ _)),
    fun j => (hmassY (j + 1)).trans (measure_mono ?_)⟩
  rw [hEs]
  exact fun x hx => hx.2
/-- **Good slicing radii in the dyadic intervals** (Simon 6.5.1, proof of the deformation
theorem, displays (8)–(10), chapter-06.txt lines 1725–1740: a radius `ρ ∈ (σ/2, σ)` with
`M⟨T, d, ρ⟩ ≤ (c/σ) M(T_σ − T_{σ/2})`).  Assume the good-radius lemma (GR) and the bounds
`μ{d < r} ≤ C r^(m+2) M`, `μ'{d < r} ≤ C r^(m+2) M'` for `0 < r ≤ 1/4`.  With
`ρⱼ = (1/2)^(j+2) ≤ 1/4`, (GR) at `ρⱼ` and `B = C ρⱼ^(m+2) M` gives `rⱼ ∈ (ρⱼ/2, ρⱼ)` whose
lower slicing derivatives are `≤ (4/ρⱼ) C ρⱼ^(m+2) M = 4 C ρⱼ^(m+1) M` for `μ` and finite for
`μ'`.  Since `r (j+1) < (1/2)^(j+3) < r j`, `r` is strictly decreasing, and
`μ{d < rⱼ} ≤ μ{d < ρⱼ} ≤ C (1/2)^((j+2)(m+2)) M → 0` (`M ≠ ∞`; likewise for `μ'`). -/
theorem Submission.dimred_mbl_dtsd_sh_dyadic_good_radii : (∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞) → ∀ (P m : ℕ) (μ μ' : Measure (Euclid P)) (d : Euclid P → ℝ) (C : NNReal) (M M' : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable d → M ≠ ∞ → M' ≠ ∞ → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M ∧ μ' {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M') → ∃ r : ℕ → ℝ, (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ StrictAnti r ∧ (∀ j, μ {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M ∧ μ' {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M') ∧ Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) ∧ Tendsto (fun j => μ' {x | d x < r j}) atTop (𝓝 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * M) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) < ∞) := by
  intro hGR P m μ μ' d C M M' hμ hμ' hd hM hM' hdens
  -- Step 1: `ρⱼ = (1/2)^(j+2)` satisfies `0 < ρⱼ ≤ 1/4` and `ρⱼ / 2 = (1/2)^(j+3)`
  have hρpos : ∀ j : ℕ, 0 < (1 / 2 : ℝ) ^ (j + 2) := fun j => by positivity
  have hρle : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 2) ≤ 1 / 4 := fun j => by
    calc (1 / 2 : ℝ) ^ (j + 2) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hhalf : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 3) = (1 / 2 : ℝ) ^ (j + 2) / 2 := fun j => by
    rw [pow_succ]; ring
  -- Step 2: (GR) at `ρⱼ` with `Bⱼ = C ρⱼ^(m+2) M` (the density bound at `ρⱼ`); choose `rⱼ`
  have hex : ∀ j : ℕ, ∃ r ∈ Ioo ((1 / 2 : ℝ) ^ (j + 2) / 2) ((1 / 2 : ℝ) ^ (j + 2)),
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < d x ∧ d x < r}) (𝓝[>] 0) ≤
        ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
          (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * M) ∧
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < d x ∧ d x < r}) (𝓝[>] 0) < ∞ :=
    fun j => hGR P μ μ' d _ _ hμ hμ' hd (hρpos j) (hdens _ (hρpos j) (hρle j)).1
  choose r hr hlim hlim' using hex
  have hbounds : ∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2) :=
    fun j => ⟨(hhalf j).symm ▸ (hr j).1, (hr j).2⟩
  -- Step 4: `μ{d < rⱼ} ≤ μ{d < ρⱼ} ≤ C ρⱼ^(m+2) M`, and `ρⱼ^k = (1/2)^((j+2) k)`
  have hpow : ∀ j k : ℕ, ((1 / 2 : ℝ) ^ (j + 2)) ^ k = (1 / 2 : ℝ) ^ ((j + 2) * k) :=
    fun j k => (pow_mul _ _ _).symm
  have hmono : ∀ (ν : Measure (Euclid P)) (j : ℕ),
      ν {x | d x < r j} ≤ ν {x | d x < (1 / 2 : ℝ) ^ (j + 2)} := fun ν j =>
    measure_mono fun x hx => lt_trans (show d x < r j from hx) (hr j).2
  have hrμ : ∀ j, μ {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M ∧
      μ' {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M' := by
    intro j
    obtain ⟨h1, h2⟩ := hdens _ (hρpos j) (hρle j)
    rw [hpow] at h1 h2
    exact ⟨(hmono μ j).trans h1, (hmono μ' j).trans h2⟩
  -- Step 5: the bound `C (1/2)^((j+2)(m+2)) N` tends to `0` when `N ≠ ∞`
  have hgeom : Tendsto (fun j : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2)))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) atTop (𝓝 0) := by
      refine (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp ?_
      refine tendsto_atTop_mono (fun j => ?_) tendsto_id
      show j ≤ (j + 2) * (m + 2)
      nlinarith
    simpa using ENNReal.tendsto_ofReal h1
  have htend : ∀ (ν : Measure (Euclid P)) (N : ℝ≥0∞), N ≠ ∞ →
      (∀ j, ν {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * N) →
      Tendsto (fun j => ν {x | d x < r j}) atTop (𝓝 0) := by
    intro ν N hN hle
    have hg : Tendsto (fun j : ℕ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * N)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hgeom (Or.inr ENNReal.coe_ne_top))
        (a := (C : ℝ≥0∞) * 0) (b := N) (Or.inr hN)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun j => zero_le) hle
  -- Step 3: `r (j+1) < (1/2)^(j+3) < r j`, so `r` is strictly decreasing
  refine ⟨r, hbounds, strictAnti_nat_of_succ_lt fun j => ?_, hrμ,
    htend μ M hM (fun j => (hrμ j).1), htend μ' M' hM' (fun j => (hrμ j).2), fun j => ?_, hlim'⟩
  · calc r (j + 1) < (1 / 2 : ℝ) ^ (j + 1 + 2) := (hr (j + 1)).2
      _ = (1 / 2 : ℝ) ^ (j + 3) := by ring_nf
      _ < r j := (hbounds j).1
  -- Step 6: `ofReal (4/ρ) · C ofReal (ρ^(m+2)) M = 4 C ofReal (ρ^(m+1)) M` for `ρ = ρⱼ > 0`
  · refine (hlim j).trans (le_of_eq ?_)
    have hρ := hρpos j
    set ρ := (1 / 2 : ℝ) ^ (j + 2) with hρdef
    have hkey : ENNReal.ofReal (4 / ρ) * ENNReal.ofReal (ρ ^ (m + 2)) =
        4 * ENNReal.ofReal (ρ ^ (m + 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : 4 / ρ * ρ ^ (m + 2) = 4 * ρ ^ (m + 1) := by
        field_simp
        ring
      rw [this, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [← hpow j (m + 1)]
    calc ENNReal.ofReal (4 / ρ) * (C * ENNReal.ofReal (ρ ^ (m + 2)) * M)
        = C * (ENNReal.ofReal (4 / ρ) * ENNReal.ofReal (ρ ^ (m + 2))) * M := by ring
      _ = 4 * C * ENNReal.ofReal (ρ ^ (m + 1)) * M := by rw [hkey]; ring
/-- **Boundary mass of a slice of a boundary current** (Simon 6.5.1, proof of the deformation
theorem, displays (8)–(10)): assuming the slicing statement (SL), if `∂T(η) = ∫ ⟨η, ξ⟩ dμ` with
`|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x`, `f` is `L`-Lipschitz and `B(η) = ∫_{f < t} ⟨η, ξ⟩ dμ`, then
`M_W(∂B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` for open `W`.  For `m = 0`,
`M_W(∂B) = 0`; otherwise (SL) applied to `T′ = ∂T` (with `∂T′ = ∂∂T = 0`, the zero measure and
the zero orientation) gives `A′_t = B` and `B′_t = 0`, so `∂A′_t − B′_t = ∂B`. -/
theorem Submission.dimred_mbl_dtsd_sh_slice_boundaryMassOn_le : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (B : GeometricCurrentOn U m) (W : Set (Euclid P)), IsOpen U → IsOpen W → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ η : TestFormOn U m, T.boundary η = ∫ x, ξ x ((η : DifferentialForm (Euclid P) m) x) ∂μ) → LipschitzWith L f → (∀ η : TestFormOn U m, B η = ∫ x in {x | f x < t}, ξ x ((η : DifferentialForm (Euclid P) m) x) ∂μ) → boundaryMassOn B W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro hSL P m U T μ ξ f L t B W hU hW hμK hξm hξb hrep hf hB
  cases m with
  | zero => exact zero_le
  | succ k =>
    -- (SL) for `T′ = ∂T`, with `∂T′ = 0` represented by the zero measure and orientation
    obtain ⟨A', B', hA', hB', -, hmass, -⟩ := hSL P k U T.boundary μ 0 ξ 0 f L hU hμK
      (fun K _ _ => by simp) hξm (aestronglyMeasurable_zero_measure _) hξb (by simp) hrep
      (fun η => by rw [GeometricCurrentOn.boundary_boundary]; simp) hf
    have hA't : A' t = B := by
      ext η; rw [hA' t η, hB η]
    have hB't : B' t = 0 := by
      ext ζ; rw [hB' t ζ]; simp
    have hbd : (A' t).boundary - B' t = B.boundary := by
      rw [hA't, hB't]; ext ζ; show B.boundary ζ - 0 = B.boundary ζ; simp
    have h := hmass W t hW
    rw [hbd] at h
    exact h
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
  -- Step 3: `(A − B)(ω) = A(ω) − B(ω) = A(ω) + B(−ω)`, by linearity of `B`
  have hsplit : (A - B) ω = A ω + B (-ω) := by
    have hB : B (-ω) = -B ω := B.toCurrent.map_neg ω
    change A ω - B ω = A ω + B (-ω)
    rw [hB, sub_eq_add_neg]
  -- Steps 4–5: `ofReal` is subadditive, and each term is bounded by the corresponding mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hneg)

/-- **Boundary-mass calculus** (Simon (6.2.3), chapter-06.txt lines 216–220, with the convention
`∂T = 0` for `n = 0`; the boundary-mass bookkeeping of the shell decomposition in the deformation
theorem): `M_G(∂(X − Y)) ≤ M_G(∂X) + M_G(∂Y)` and `M_G(∂∂X) = 0` for every set `G`.  In positive
degree `∂(X − Y) = ∂X − ∂Y`, so the first claim is `Submission.cmc_fc_cs_massOn_sub_le`; the second
holds because `∂∂X = 0` and `M_G(0) = 0`. -/
theorem Submission.dimred_mbl_dtsd_sh_boundaryMassOn_calculus : ∀ (P m : ℕ) (U G : Set (Euclid P)), (∀ X Y : GeometricCurrentOn U m, boundaryMassOn (X - Y) G ≤ boundaryMassOn X G + boundaryMassOn Y G) ∧ ∀ X : GeometricCurrentOn U (m + 1), boundaryMassOn X.boundary G = 0 := by
  intro P m U G
  -- Step 1: `M_G(0) = 0` in every degree, since `0(ω) = 0` for each admissible `ω`
  have hzero : ∀ {k : ℕ} (G : Set (Euclid P)), (0 : GeometricCurrentOn U k).massOn G = 0 := by
    intro k G
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  cases m with
  -- Step 2: in degree `0` the boundary mass is `0` by convention
  | zero => exact ⟨fun X Y => by simp [boundaryMassOn], fun X => rfl⟩
  | succ k =>
    refine ⟨fun X Y => ?_, fun X => ?_⟩
    -- Step 3: `∂(X − Y) = ∂X − ∂Y` (both send `η` to `X(dη) − Y(dη)`), then mass subadditivity
    · show (X - Y).boundary.massOn G ≤ X.boundary.massOn G + Y.boundary.massOn G
      have h : (X - Y).boundary = X.boundary - Y.boundary := by ext ω; rfl
      rw [h]
      exact Submission.cmc_fc_cs_massOn_sub_le P k U G _ _
    -- Step 4: `∂∂X = 0`, so `M_G(∂∂X) = M_G(0) = 0`
    · show X.boundary.boundary.massOn G = 0
      rw [GeometricCurrentOn.boundary_boundary]
      exact hzero G
/-- **Support calculus** for currents in `ℝᴾ` (Simon 6.2.11): (i) if `E` is closed and `X(ω) = 0`
whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed; (iii)
`spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`.  A point lies off `spt X`
iff it has an open neighbourhood with compact closure on which `X` vanishes.  Small balls are such
neighbourhoods in the proper space `ℝᴾ`; zero neighbourhoods of `A` and `B` intersect to one of
`A − B`; and since `spt dη ⊆ spt η`, a zero neighbourhood of `A` is one of `∂A`. -/
theorem Submission.cmcsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- `B_ε(x)` is open, and its closure lies in the compact `closedBall x ε` (`ℝᴾ` is proper)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ univ := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) for `x ∉ E`, a ball around `x` inside the open set `Eᶜ` is a zero neighbourhood of `x`
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε)
      ⟨(hball x ε).1, (hball x ε).2.1, (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) `spt X = univ \ X.zeroRegion`, and the zero region is open
    intro X
    exact isClosed_univ.sdiff X.isOpen_zeroRegion
  · -- (iii) the intersection of zero neighbourhoods of `A` and `B` is one of `A − B`
    intro A B x hx
    by_contra hAB
    have hxA : x ∈ A.zeroRegion := by
      by_contra h
      exact hAB (mem_union_left _ ⟨mem_univ x, h⟩)
    have hxB : x ∈ B.zeroRegion := by
      by_contra h
      exact hAB (mem_union_right _ ⟨mem_univ x, h⟩)
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp hxA
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp hxB
    refine hx.2 (mem_sUnion_of_mem (⟨hxWA, hxWB⟩ : x ∈ WA ∩ WB) ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (mem_sUnion_of_mem
      (mem_ball_self one_pos) ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2,
        fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `∂A(η) = A(dη)` with `spt dη ⊆ spt η`: a zero neighbourhood of `A` is one of `∂A`
    intro A x hx
    refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp hxA
    refine mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)
/-- **Support calculus in `ℝᴾ`** (Simon 6.2.11, 6.2.3).  For currents in `ℝᴾ`: (i) if `E` is
closed and `X(ω) = 0` whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed;
(iii) `spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`. -/
theorem Submission.dimred_mbl_dtsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- every ball of the proper space `ℝᴾ` is open with compact closure (inside `univ`)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ (univ : Set (Euclid P)) := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  -- off the support means in the zero region
  have hzero : ∀ {m : ℕ} (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (x : Euclid P),
      x ∉ X.support → x ∈ X.zeroRegion := fun X x hx => by
    by_contra h
    exact hx ⟨mem_univ x, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) a ball around `x ∉ E` inside `Eᶜ` is a zero neighbourhood
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε) ⟨(hball x ε).1, (hball x ε).2.1,
      (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) the support is the complement of the open zero region
    intro X
    have hsupp : X.support = X.zeroRegionᶜ := by
      rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
    rw [hsupp]
    exact X.isOpen_zeroRegion.isClosed_compl
  · -- (iii) intersect zero neighbourhoods of `A` and `B`
    intro A B x hx
    by_contra hAB
    rw [mem_union, not_or] at hAB
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp (hzero A x hAB.1)
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp (hzero B x hAB.2)
    refine hx.2 (mem_sUnion_of_mem (t := WA ∩ WB) ⟨hxWA, hxWB⟩ ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    refine eq_empty_of_forall_notMem fun x hx => hx.2 (mem_sUnion_of_mem (mem_ball_self one_pos)
      ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2, fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `tsupport dη ⊆ tsupport η`, so zero neighbourhoods of `A` are ones of `∂A`
    intro A x hx
    by_contra hxA
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp (hzero A x hxA)
    refine hx.2 (mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩)
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)
/-- **Mass of a current given by integration against a measure** (Simon 6.2.5; the estimate
`∫_B ⟨ω, ξ⟩ dμ ≤ μ(B)` for `|ω| ≤ 1` used to localize in the proof of 7.2.4): if
`X(ω) = ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` for every `ω ∈ 𝒟^d(U)` and `|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x`,
then `M_V(X) ≤ μ(E ∩ V)`.  For an admissible `ω`,
`X(ω) ≤ |∫_E ⟨ω, ξ⟩ dμ| ≤ ∫_E |⟨ω, ξ⟩| dμ`; the integrand is at most `|ω| ≤ 1` on `spt ω ⊆ V` and
vanishes off `spt ω`, so `X(ω) ≤ μ(spt ω ∩ E) ≤ μ(E ∩ V)`.  The Bochner integral of a
non-integrable integrand is `0`, so no integrability assumption is needed. -/
theorem Submission.cmc_fcl_massOn_le_measure_inter : ∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V) := by
  intro P d U X μ ξ E V hξ hX
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ _
  rw [hX ω]
  -- `spt ω` is closed, hence Borel
  have hS : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) d)) :=
    (isClosed_tsupport _).measurableSet
  calc ENNReal.ofReal (∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ)
        ≤ ‖∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in E, ‖ξ x ((ω : DifferentialForm (Euclid P) d) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    -- a.e. on `E`: `|⟨ω, ξ⟩| ≤ |ω| ≤ 1` on `spt ω`, and `ω = 0` off `spt ω`
    _ ≤ ∫⁻ x in E, (tsupport (ω : DifferentialForm (Euclid P) d)).indicator 1 x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hξ] with x hx
        by_cases hxs : x ∈ tsupport (ω : DifferentialForm (Euclid P) d)
        · rw [indicator_of_mem hxs, Pi.one_apply, Real.enorm_eq_ofReal_abs]
          calc ENNReal.ofReal |ξ x ((ω : DifferentialForm (Euclid P) d) x)|
              ≤ ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) d) x)) :=
                ENNReal.ofReal_le_ofReal (hx _)
            _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hω.2 x)
            _ = 1 := ENNReal.ofReal_one
        · rw [indicator_of_notMem hxs]
          have h0 : (ω : DifferentialForm (Euclid P) d) x = 0 :=
            image_eq_zero_of_notMem_tsupport hxs
          simp [h0]
    _ = μ.restrict E (tsupport (ω : DifferentialForm (Euclid P) d)) := lintegral_indicator_one hS
    _ = μ (tsupport (ω : DifferentialForm (Euclid P) d) ∩ E) := Measure.restrict_apply hS
    _ ≤ μ (E ∩ V) := measure_mono fun x hx => ⟨hx.2, hω.1 hx.1⟩
/-- **Left slopes at a point of differentiability** (Simon Ch. 6, 4.9 and (2) in the proof of
8.2).  If `F : ℝ → ℝ` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * ofReal (F(t) - F(t - h)) ≤ ofReal (F′(t))`.  The left difference
quotients `h⁻¹ (F(t) - F(t - h))` tend to `F′(t)` as `h ↓ 0`; for `h > 0` the product above is
`ofReal` of the quotient, so it tends to `ofReal (F′(t))`, and along `𝓝[>] 0` the liminf of a
convergent function is its limit.  Monotonicity of `F` is not needed. -/
theorem Submission.cbr_smm_liminf_left_slope_le_deriv : ∀ (F : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ F t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h))) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv F t) := by
  intro F t hF
  -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
  have hlim : Tendsto (fun h : ℝ => h⁻¹ * (F t - F (t - h))) (𝓝[>] 0) (𝓝 (deriv F t)) := by
    refine (hF.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
    simp only [Function.comp_apply, smul_eq_mul]
    rw [← sub_eq_add_neg, inv_neg]
    ring
  -- for `h > 0`, `ofReal h⁻¹ * ofReal (F t - F (t - h)) = ofReal (h⁻¹ * (F t - F (t - h)))`
  have hlim' : Tendsto (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (deriv F t))) := by
    refine (ENNReal.tendsto_ofReal hlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact ENNReal.ofReal_mul (inv_nonneg.2 hh.le)
  exact hlim'.liminf_eq.le

/-- **Left slice densities at a point of differentiability of the distribution function** (Simon
Ch. 6, 4.9 and the remark after it; (10) in the proof of 5.1).  Let `μ` be a finite measure, `f`
measurable and `F(s) = μ{f < s}` (read in `ℝ`).  If `F` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * μ{t - h < f < t} ≤ ofReal (F′(t))`.  For `h > 0`,
`{t - h < f < t} ⊆ {f < t} \ {f < t - h}` and `{f < t - h} ⊆ {f < t}`, so, `μ` being finite,
`μ{t - h < f < t} ≤ ofReal (F(t) - F(t - h))`; the liminf is monotone, and the left slopes of `F`
are bounded by `F′(t)` (`Submission.cbr_smm_liminf_left_slope_le_deriv`). -/
theorem Submission.dimred_mbl_dtsd_gr_liminf_slice_le_deriv : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (t : ℝ), IsFiniteMeasure μ → Measurable f → DifferentiableAt ℝ (fun s : ℝ => (μ {x | f x < s}).toReal) t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv (fun s : ℝ => (μ {x | f x < s}).toReal) t) := by
  intro α _ μ f t hμ hf hF
  set F : ℝ → ℝ := fun s => (μ {x | f x < s}).toReal
  -- `μ{f < s} = ofReal (F s)`, since `μ` is finite
  have hA : ∀ s, μ {x | f x < s} = ENNReal.ofReal (F s) := fun s =>
    (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  refine le_trans (liminf_le_liminf ?_) (Submission.cbr_smm_liminf_left_slope_le_deriv F t hF)
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  gcongr
  -- `{t - h < f < t} ⊆ {f < t} \ {f < t - h}`, and `{f < t - h} ⊆ {f < t}` as `h > 0`
  have hsub : {x | f x < t - h} ⊆ {x | f x < t} := fun x (hx : f x < t - h) =>
    show f x < t by linarith
  calc μ {x | t - h < f x ∧ f x < t} ≤ μ ({x | f x < t} \ {x | f x < t - h}) :=
        measure_mono fun x ⟨h₁, h₂⟩ => ⟨h₂, fun h₃ : f x < t - h => lt_asymm h₁ h₃⟩
    _ = μ {x | f x < t} - μ {x | f x < t - h} :=
        measure_sdiff hsub (measurableSet_lt hf measurable_const).nullMeasurableSet
          (measure_ne_top μ _)
    _ = ENNReal.ofReal (F t) - ENNReal.ofReal (F (t - h)) := by rw [hA, hA]
    _ = ENNReal.ofReal (F t - F (t - h)) := (ENNReal.ofReal_sub _ ENNReal.toReal_nonneg).symm
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

/-- **Markov choice of a good radius off a null set** (Simon Ch. 6, proof of 5.1 (10)): if `F` is
nondecreasing, `ρ > 0` and `F(ρ) − F(ρ/2) ≤ B`, then for every Lebesgue-null `N` there is
`r ∈ (ρ/2, ρ) \ N` with `F′(r) ≤ (4/ρ) B`.  By Lebesgue's inequality `∫⁻_{(ρ/2,ρ)} F′ ≤ B`, so by
Markov's inequality `{t ∈ (ρ/2, ρ) : F′(t) > (4/ρ) B}` has measure `≤ ρ/4 < ρ/2` (if `0 < B < ∞`;
the cases `B = 0`, `B = ∞` are direct).  Hence `S = {t ∈ (ρ/2, ρ) : F′(t) ≤ (4/ρ) B}` has positive
measure, and so has `S \ N`. -/
theorem Submission.dimred_mbl_dtsd_gr_exists_deriv_le_off_null : ∀ (F : ℝ → ℝ) (ρ : ℝ) (B : ℝ≥0∞) (N : Set ℝ), Monotone F → 0 < ρ → ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ B → (volume : Measure ℝ) N = 0 → ∃ r ∈ Ioo (ρ / 2) ρ, r ∉ N ∧ ENNReal.ofReal (deriv F r) ≤ ENNReal.ofReal (4 / ρ) * B := by
  intro F ρ B N hF hρ hB hN
  -- `I = (ρ/2, ρ)`, `c = (4/ρ) B`, `g = ofReal ∘ F′`, `S = {t ∈ I : g t ≤ c}`
  set I := Ioo (ρ / 2) ρ with hI
  set c := ENNReal.ofReal (4 / ρ) * B with hc
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (deriv F t)
  set S := {t ∈ I | g t ≤ c}
  -- `|I| = ρ/2 > 0`
  have hIm : MeasurableSet I := measurableSet_Ioo
  have hIvol : volume I = ENNReal.ofReal (ρ / 2) := by
    rw [hI, Real.volume_Ioo]
    congr 1
    ring
  have hIpos : 0 < volume I := by
    rw [hIvol]
    exact ENNReal.ofReal_pos.2 (half_pos hρ)
  have h4 : ENNReal.ofReal (4 / ρ) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  -- Lebesgue's inequality: `∫⁻_I g ≤ F(ρ) − F(ρ/2) ≤ B`
  have hgm : Measurable g := (measurable_deriv F).ennreal_ofReal
  have hint : ∫⁻ t in I, g t ≤ B :=
    (Submission.cmcs_smi_lintegral_ofReal_deriv_le F (ρ / 2) ρ hF).trans hB
  have hcover : volume I ≤ volume S + volume (I \ S) :=
    calc volume I ≤ volume (S ∪ (I \ S)) := measure_mono fun t ht => by
          by_cases htS : t ∈ S
          · exact Or.inl htS
          · exact Or.inr ⟨ht, htS⟩
      _ ≤ volume S + volume (I \ S) := measure_union_le S (I \ S)
  have hSpos : 0 < volume S := by
    rcases eq_or_ne B ∞ with hBtop | hBtop
    · -- `B = ∞`: `c = ∞`, so `S = I`
      have hSI : S = I := by
        refine Subset.antisymm (fun t ht => ht.1) fun t ht => ⟨ht, ?_⟩
        rw [hc, hBtop, ENNReal.mul_top h4]
        exact le_top
      rw [hSI]
      exact hIpos
    rcases eq_or_ne B 0 with hB0 | hB0
    · -- `B = 0`: `∫⁻_I g = 0`, so `g = 0` a.e. on `I`, and `I \ S ⊆ {g ≠ 0}` is null
      have hae : g =ᵐ[volume.restrict I] 0 :=
        (lintegral_eq_zero_iff hgm).1 (le_antisymm (hint.trans hB0.le) zero_le)
      rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hIm] at hae
      have hnull : volume (I \ S) = 0 := by
        refine measure_mono_null (fun t ht => ?_) hae
        refine ⟨fun hgt => ht.2 ⟨ht.1, ?_⟩, ht.1⟩
        rw [hgt]
        exact zero_le
      rw [hnull, add_zero] at hcover
      exact hIpos.trans_le hcover
    · -- `0 < B < ∞`: Markov gives `c |E| ≤ B` for `E = {c ≤ g} ∩ I`, so `|E| ≤ ρ/4`
      have hmarkov := mul_meas_ge_le_lintegral₀ (μ := volume.restrict I) hgm.aemeasurable c
      rw [Measure.restrict_apply' hIm] at hmarkov
      have hE : volume ({t | c ≤ g t} ∩ I) ≤ ENNReal.ofReal (ρ / 4) := by
        have h1 : B * (ENNReal.ofReal (4 / ρ) * volume ({t | c ≤ g t} ∩ I)) ≤ B * 1 :=
          calc B * (ENNReal.ofReal (4 / ρ) * volume ({t | c ≤ g t} ∩ I))
              = c * volume ({t | c ≤ g t} ∩ I) := by rw [hc]; ring
            _ ≤ ∫⁻ t in I, g t := hmarkov
            _ ≤ B := hint
            _ = B * 1 := (mul_one B).symm
        rw [ENNReal.mul_le_mul_iff_right hB0 hBtop, mul_comm, ← ENNReal.le_inv_iff_mul_le,
          ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div] at h1
        exact h1
      -- `I \ S ⊆ E`, so `|I| ≤ |S| + ρ/4`; `|S| = 0` would give `ρ/2 ≤ ρ/4`
      have hsub : I \ S ⊆ {t | c ≤ g t} ∩ I := fun t ht =>
        ⟨(not_le.1 fun h => ht.2 ⟨ht.1, h⟩).le, ht.1⟩
      have hdiff : volume (I \ S) ≤ ENNReal.ofReal (ρ / 4) := (measure_mono hsub).trans hE
      refine pos_iff_ne_zero.2 fun hS0 => ?_
      have hle := hcover.trans (add_le_add hS0.le hdiff)
      rw [zero_add, hIvol, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
      linarith
  -- `|S \ N| = |S| > 0`, so some `r ∈ S` lies outside `N`
  have hSN : volume (S \ N) ≠ 0 := by
    rw [measure_sdiff_null hN]
    exact hSpos.ne'
  obtain ⟨r, ⟨hrI, hrc⟩, hrN⟩ := nonempty_of_measure_ne_zero hSN
  exact ⟨r, hrI, hrN, hrc⟩

/-- **Choice of a good slicing radius** (Simon Ch. 6, proof of 5.1, (8)–(10)).  If `μ`, `μ'` are
finite and `μ {f < ρ} ≤ B`, some `r ∈ (ρ/2, ρ)` has `liminf_{h → 0+} h⁻¹ μ {r - h < f < r} ≤
(4/ρ) B` and `liminf_{h → 0+} h⁻¹ μ' {r - h < f < r} < ∞`.  The distribution functions
`F(t) = μ {f < t}` and `G(t) = μ' {f < t}` are monotone, hence differentiable off a Lebesgue-null
set (Lebesgue's theorem).  As `F(ρ) - F(ρ/2) ≤ F(ρ) ≤ B`, Markov's inequality gives `r ∈ (ρ/2, ρ)`
off that set with `F′(r) ≤ (4/ρ) B`, and at `r` the two liminfs are at most `F′(r)` and
`G′(r) < ∞`. -/
theorem Submission.dimred_mbl_dtsd_good_radius : ∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞ := by
  intro P μ μ' f ρ B hμ hμ' hf hρ hB
  -- the distribution function `t ↦ ν {f < t}` of a finite measure `ν` is monotone
  have hmono : ∀ (ν : Measure (Euclid P)) [IsFiniteMeasure ν],
      Monotone fun s : ℝ => (ν {x | f x < s}).toReal := fun ν _ s s' hs =>
    ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono fun x (hx : f x < s) => hx.trans_le hs)
  set F := fun s : ℝ => (μ {x | f x < s}).toReal
  set G := fun s : ℝ => (μ' {x | f x < s}).toReal
  -- `F` and `G` are differentiable off a Lebesgue-null set (Lebesgue's theorem)
  have hN : volume ({t | ¬DifferentiableAt ℝ F t} ∪ {t | ¬DifferentiableAt ℝ G t}) = 0 :=
    measure_union_null (ae_iff.1 (hmono μ).ae_differentiableAt)
      (ae_iff.1 (hmono μ').ae_differentiableAt)
  -- `F(ρ) - F(ρ/2) ≤ F(ρ) = μ {f < ρ} ≤ B`
  have hFB : ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ B :=
    (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans
      ((ENNReal.ofReal_toReal (measure_ne_top μ _)).le.trans hB)
  -- Markov's inequality: some `r ∈ (ρ/2, ρ)` off the null set has `F′(r) ≤ (4/ρ) B`
  obtain ⟨r, hr, hrN, hrB⟩ :=
    Submission.dimred_mbl_dtsd_gr_exists_deriv_le_off_null F ρ B _ (hmono μ) hρ hFB hN
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hrN
  -- at `r` the slice liminfs are at most `F′(r) ≤ (4/ρ) B` and `G′(r) < ∞`
  exact ⟨r, hr,
    (Submission.dimred_mbl_dtsd_gr_liminf_slice_le_deriv _ μ f r hμ hf hrN.1).trans hrB,
    (Submission.dimred_mbl_dtsd_gr_liminf_slice_le_deriv _ μ' f r hμ' hf hrN.2).trans_lt
      ENNReal.ofReal_lt_top⟩
/-- **Lipschitz extension into `ℝᴾ`** (componentwise McShane): if `ψ : ℝᴾ → ℝᴾ` is `K`-Lipschitz
on `S`, then some `φ : ℝᴾ → ℝᴾ` is `√P K`-Lipschitz on `ℝᴾ` and agrees with `ψ` on `S`.  Each
coordinate `x ↦ ψ(x)ᵢ` is `K`-Lipschitz on `S` (`|vᵢ| ≤ |v|`), so has a `K`-Lipschitz extension
`gᵢ` (`LipschitzOnWith.extend_real`); `φ = (gᵢ)ᵢ` then satisfies
`|φ(x) − φ(y)|² = Σᵢ |gᵢ(x) − gᵢ(y)|² ≤ P K² |x − y|²`. -/
theorem Submission.dimred_mbl_dtsd_lipschitz_extension : ∀ (P : ℕ) (S : Set (Euclid P)) (ψ : Euclid P → Euclid P) (K : NNReal), LipschitzOnWith K ψ S → ∃ φ : Euclid P → Euclid P, LipschitzWith (NNReal.sqrt P * K) φ ∧ EqOn φ ψ S := by
  intro P S ψ K hψ
  -- (1) each coordinate `x ↦ ψ(x)ᵢ` is `K`-Lipschitz on `S`, since `|vᵢ| ≤ |v|`
  have hcoord : ∀ i : Fin P, LipschitzOnWith K (fun x => ψ x i) S := fun i =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
      (PiLp.dist_apply_le (ψ x) (ψ y) i).trans (hψ.dist_le_mul x hx y hy)
  -- (2) McShane: `K`-Lipschitz `gᵢ : ℝᴾ → ℝ` with `gᵢ = ψ(·)ᵢ` on `S`
  choose g hgL hgS using fun i => (hcoord i).extend_real
  -- (3) `φ(x) = (gᵢ(x))ᵢ`
  refine ⟨fun x => WithLp.toLp 2 fun i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_,
    fun x hx => ?_⟩
  · -- (4) `dist(φ x, φ y) = √(Σᵢ dist(gᵢ x, gᵢ y)²) ≤ √(P (K dist(x, y))²)`
    rw [EuclideanSpace.dist_eq]
    calc √(∑ i, dist (g i x) (g i y) ^ 2) ≤ √(∑ _i : Fin P, ((K : ℝ) * dist x y) ^ 2) := by
          gcongr with i
          exact (hgL i).dist_le_mul x y
      _ = ↑(NNReal.sqrt P * K) * dist x y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
          push_cast
          ring
  · -- (5) `φ = ψ` on `S`, coordinate by coordinate
    ext i
    exact (hgS i hx).symm
/-- **Dyadic series estimates** for the constants of the deformation theorem (Simon Ch. 6,
proof of 5.1).  If `Λⱼ ≤ c₄ 2ʲ`, then: (1) for `p ≤ q`, `a₀ ≤ A` and
`a_{j+1} ≤ C 2^{−(j+2)(q+1)} A`, `∑ⱼ (2Λⱼ)ᵖ aⱼ ≤ (2c₄)ᵖ (1 + C) A`; (2) for finite `K`, `A` and
`zⱼ ≤ K 2^{−(j+2)(p+1)} A`, `(2Λⱼ)ᵖ zⱼ → 0`.  With `ι = 2⁻¹`, `(2Λⱼ)ᵖ ≤ (2c₄)ᵖ 2^{jp}` and
`2ᵐ ιᵉ ≤ ιʳ` for `m + r ≤ e`, so the terms are dominated by geometric ones. -/
theorem Submission.dimred_mbl_dtsd_dyadic_series_bounds : ∀ (c₄ : NNReal) (Λ : ℕ → NNReal), (∀ j, (Λ j : ℝ) ≤ c₄ * 2 ^ j) → (∀ (C : NNReal) (A : ℝ≥0∞) (p q : ℕ) (a : ℕ → ℝ≥0∞), p ≤ q → a 0 ≤ A → (∀ j, a (j + 1) ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (q + 1))) * A) → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ p * a j ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * (1 + C) * A) ∧ (∀ (K A : ℝ≥0∞) (p : ℕ) (z : ℕ → ℝ≥0∞), K ≠ ∞ → A ≠ ∞ → (∀ j, z j ≤ K * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (p + 1))) * A) → Tendsto (fun j => (2 * (Λ j : ℝ≥0∞)) ^ p * z j) atTop (𝓝 0)) := by
  intro c₄ Λ hΛ
  -- `ι = 2⁻¹`: `ofReal ((1/2)ᵉ) = ιᵉ`, and `2ᵐ ιᵉ ≤ ιʳ` whenever `m + r ≤ e`
  have hι : ∀ e : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ e) = (2⁻¹ : ℝ≥0∞) ^ e := fun e => by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hι1 : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.one_half_lt_one.le
  have hshift : ∀ m r e : ℕ, m + r ≤ e →
      (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ e ≤ (2⁻¹ : ℝ≥0∞) ^ r := by
    intro m r e hle
    calc (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ e ≤ (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ (m + r) :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hι1 hle)
      _ = (2 * 2⁻¹ : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ r := by rw [pow_add, mul_pow, mul_assoc]
      _ = (2⁻¹ : ℝ≥0∞) ^ r := by
          rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
  -- Step 0: `(2Λⱼ)ᵖ ≤ (2c₄)ᵖ 2^{jp}`
  have hw : ∀ p j : ℕ, (2 * (Λ j : ℝ≥0∞)) ^ p ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) := by
    intro p j
    have h : (Λ j : ℝ≥0∞) ≤ c₄ * 2 ^ j := by
      have h' : Λ j ≤ c₄ * 2 ^ j := by exact_mod_cast hΛ j
      exact_mod_cast h'
    calc (2 * (Λ j : ℝ≥0∞)) ^ p ≤ (2 * ((c₄ : ℝ≥0∞) * 2 ^ j)) ^ p := by gcongr
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) := by rw [← mul_assoc, mul_pow, pow_mul]
  refine ⟨fun C A p q a hpq ha0 ha => ?_, fun K A p z hK hA hz => ?_⟩
  · -- Steps 1–2: the `0`-th term is `≤ (2c₄)ᵖ A`, the `(j+1)`-st is `≤ (2c₄)ᵖ C A ι^{j+2}`
    have h0 : (2 * (Λ 0 : ℝ≥0∞)) ^ p * a 0 ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A := by
      simpa using mul_le_mul' (hw p 0) ha0
    have hs : ∀ j, (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1) ≤
        (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) := by
      intro j
      have he : (j + 1) * p + (j + 2) ≤ (j + 2) * (q + 1) := by
        nlinarith [Nat.mul_le_mul_left (j + 2) hpq]
      calc (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1)
          ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ ((j + 1) * p) *
              (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (q + 1))) * A) :=
            mul_le_mul' (hw p (j + 1)) (ha j)
        _ = (2 * (c₄ : ℝ≥0∞)) ^ p * C * A *
              (2 ^ ((j + 1) * p) * (2⁻¹ : ℝ≥0∞) ^ ((j + 2) * (q + 1))) := by
            rw [hι]; ring
        _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) := by
            gcongr; exact hshift _ _ _ he
    -- Step 3: `∑ⱼ ι^{j+2} = ι² (1 − ι)⁻¹ = 2⁻¹ ≤ 1`, then sum the term bounds
    have hgeom : ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2) ≤ 1 := by
      calc ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2)
          = (2⁻¹ : ℝ≥0∞) ^ 2 * ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j := by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun j => by rw [pow_add, mul_comm]
        _ = 2⁻¹ * (2⁻¹ * 2) := by
            rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, sq, mul_assoc]
        _ ≤ 1 := by
            rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
            exact hι1
    calc ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ p * a j
        = (2 * (Λ 0 : ℝ≥0∞)) ^ p * a 0 + ∑' j, (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1) :=
          tsum_eq_zero_add' ENNReal.summable
      _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A +
            ∑' j : ℕ, (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) :=
          add_le_add h0 (ENNReal.tsum_le_tsum hs)
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * A +
            (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2) := by
          rw [ENNReal.tsum_mul_left]
      _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A + (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * 1 := by gcongr
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * (1 + C) * A := by ring
  · -- Step 4: `(2Λⱼ)ᵖ zⱼ ≤ κ ιʲ` with `κ = (2c₄)ᵖ K A < ∞`, and `κ ιʲ → 0`
    have hκ : (2 * (c₄ : ℝ≥0∞)) ^ p * K * A ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)) hK) hA
    have hb : ∀ j, (2 * (Λ j : ℝ≥0∞)) ^ p * z j ≤
        (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j := by
      intro j
      have he : j * p + j ≤ (j + 2) * (p + 1) := by nlinarith
      calc (2 * (Λ j : ℝ≥0∞)) ^ p * z j
          ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) *
              (K * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (p + 1))) * A) :=
            mul_le_mul' (hw p j) (hz j)
        _ = (2 * (c₄ : ℝ≥0∞)) ^ p * K * A *
              (2 ^ (j * p) * (2⁻¹ : ℝ≥0∞) ^ ((j + 2) * (p + 1))) := by
            rw [hι]; ring
        _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j := by
            gcongr; exact hshift _ _ _ he
    have hlim : Tendsto (fun j : ℕ => (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one) (Or.inr hκ)
      rwa [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hb

/-- **Dyadic shell decomposition** (Simon Ch. 6, proof of the deformation theorem 5.1,
displays (8)–(10), chapter-06.txt lines 1725–1740).  Let `T ∈ 𝒟ₙ(ℝᴾ)`, `n = m + 1`, be integer
multiplicity with `spt T` compact and `M(T), M(∂T) < ∞`, and let `d` be `1`-Lipschitz with
`M_{d<r}(T) ≤ C r^{m+2} M(T)` and `M_{d<r}(∂T) ≤ C r^{m+2} M(∂T)` for `0 < r ≤ 1/4`.  Represent
`T`, `∂T` by finite measures `μ_T`, `μ_∂`, slice by `d` (`A_t = T⌞{d < t}`, `B_t = (∂T)⌞{d < t}`,
`∂A_t = B_t` off `{d = t}`), choose good radii `rⱼ ∈ ((1/2)^{j+3}, (1/2)^{j+2})` and put
`W₀ = T − A_{r₀}`, `W_{j+1} = A_{rⱼ} − A_{r_{j+1}}`, `D₀ = ∂T − B_{r₀}`,
`D_{j+1} = B_{rⱼ} − B_{r_{j+1}}`, `Zⱼ = ∂A_{rⱼ} − B_{rⱼ}`.  Then `Wⱼ`, `Dⱼ` are `T`, `∂T` restricted
to the half-open shells `{d ≥ r₀}`, `{r_{j+1} ≤ d < rⱼ}`, so `Σⱼ Wⱼ = T`, each `Wⱼ` is integer
multiplicity and the density bounds give the mass estimates; `∂W₀ = D₀ − Z₀` and
`∂W_{j+1} = D_{j+1} − (Z_{j+1} − Zⱼ)` hold pointwise, and slicing `∂T` once more bounds
`M(∂B_{rⱼ})`. -/
theorem Submission.dimred_mbl_dtsd_shell_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (d : Euclid P → ℝ) (C : NNReal), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → LipschitzWith 1 d → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → T.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.mass ∧ T.boundary.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.boundary.mass) → ∃ (r : ℕ → ℝ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) ∧ (W 0).boundary = D 0 - Z 0 ∧ (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) ∧ (∀ j, IsIntegerMultiplicity (W j)) ∧ (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) ∧ (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) ∧ (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) ∧ (∀ j, (W j).support ⊆ T.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (D j).support ⊆ T.boundary.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (Z j).support ⊆ T.support ∩ {x | d x = r j}) ∧ (W 0).mass ≤ T.mass ∧ (∀ j, (W (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.mass) ∧ (D 0).mass ≤ T.boundary.mass ∧ (∀ j, (D (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.boundary.mass) ∧ (∀ j, (Z j).mass ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * T.mass) := by
  intro hVO hMR hREP hIMC hSL P m T d C hIM hTc hTm hbm hd hdens
  have hdc : Continuous d := hd.continuous
  have hdm : Measurable d := hdc.measurable
  -- Step 1: the finite mass measure `μ_T` of `T`, null off `spt T`; `T⌞E` is IM for Borel `E`
  obtain ⟨μ, ξ, hμf, hξm, hξb, hTrep, hTμ, hTnull, hIMsub⟩ :=
    Submission.dimred_mbl_dtsd_sh_im_mass_measure hVO hMR hIMC P (m + 1) T hIM hTm
  -- Step 2: a finite measure `μ_∂` representing `∂T`, null off `spt ∂T`
  obtain ⟨μ', ξ', hμ'f, hξ'm, hξ'b, hbrep, hbμ, hbnull⟩ :=
    Submission.dimred_mbl_dtsd_sh_finite_mass_measure hVO hREP P m T.boundary hbm
  -- Step 4: slice by `d`: `A_t = T⌞{d < t}`, `B_t = (∂T)⌞{d < t}`, `∂A_t = B_t` off `{d = t}`
  obtain ⟨A, B, hA, hB, hAB, hZ, -⟩ := hSL P m univ T μ μ' ξ ξ' d 1 isOpen_univ
    (fun K _ _ => measure_lt_top μ K) (fun K _ _ => measure_lt_top μ' K) hξm hξ'm hξb hξ'b
    hTrep hbrep hd
  -- Step 5: good radii `rⱼ ∈ ((1/2)^{j+3}, (1/2)^{j+2})`; `μ_T`, `μ_∂` inherit the density bounds
  obtain ⟨r, hr, hra, hrμ, hrt, hrt', hlim, hlim'⟩ :=
    Submission.dimred_mbl_dtsd_sh_dyadic_good_radii Submission.dimred_mbl_dtsd_good_radius P m μ
      μ' d C T.mass T.boundary.mass hμf hμ'f hdm hTm.ne hbm.ne fun s hs hs' => by
        have hopen : IsOpen {x | d x < s} := isOpen_lt hdc continuous_const
        rw [← hTμ _ hopen, ← hbμ _ hopen]
        exact hdens s hs hs'
  -- Step 6: the shells `Wⱼ`, `Dⱼ` and the slice errors `Zⱼ`
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      W 0 = T - A (r 0) ∧ ∀ j, W (j + 1) = A (r j) - A (r (j + 1)) :=
    ⟨fun j => Nat.casesOn j (T - A (r 0)) fun i => A (r i) - A (r (i + 1)), rfl, fun _ => rfl⟩
  obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m,
      D 0 = T.boundary - B (r 0) ∧ ∀ j, D (j + 1) = B (r j) - B (r (j + 1)) :=
    ⟨fun j => Nat.casesOn j (T.boundary - B (r 0)) fun i => B (r i) - B (r (i + 1)), rfl,
      fun _ => rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m,
      ∀ j, Z j = (A (r j)).boundary - B (r j) := ⟨_, fun _ => rfl⟩
  -- `(X − Y)(ω) = X(ω) − Y(ω)`
  have hsub : ∀ (k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω : TestFormOn (univ : Set (Euclid P)) k), (X - Y) ω = X ω - Y ω := fun _ _ _ _ => rfl
  -- Steps 7, 10, 11, 13: shell integrals, the series `Σⱼ Wⱼ = T`, supports and shell masses
  obtain ⟨hW0i, hWsi, hsum, hWspt, hAspt, hW0M, hWsM⟩ :=
    Submission.dimred_mbl_dtsd_sh_shell_series Submission.dimred_mbl_dtsd_support_calculus
      Submission.cmc_fcl_massOn_le_measure_inter P (m + 1) T (fun j => A (r j)) W μ ξ d r hμf
      hξm hξb hTnull hdc hra hrt hTrep (fun j => hA (r j)) (fun ω => by rw [hW0]; rfl)
      (fun j ω => by rw [hWs]; rfl)
  obtain ⟨-, -, -, hDspt, hBspt, hD0M, hDsM⟩ :=
    Submission.dimred_mbl_dtsd_sh_shell_series Submission.dimred_mbl_dtsd_support_calculus
      Submission.cmc_fcl_massOn_le_measure_inter P m T.boundary (fun j => B (r j)) D μ' ξ' d r
      hμ'f hξ'm hξ'b hbnull hdc hra hrt' hbrep (fun j => hB (r j)) (fun ω => by rw [hD0]; rfl)
      (fun j ω => by rw [hDs]; rfl)
  obtain ⟨hS1, hS2, hS3, -, hS5⟩ := Submission.dimred_mbl_dtsd_support_calculus P m
  have hS2' := (Submission.dimred_mbl_dtsd_support_calculus P (m + 1)).2.1
  -- Step 8: `Wⱼ = T⌞Eⱼ` for the Borel shells `Eⱼ`, so `Wⱼ` is integer multiplicity
  have hE0 : MeasurableSet {x | r 0 ≤ d x} := measurableSet_le measurable_const hdm
  have hEs : ∀ j, MeasurableSet {x | r (j + 1) ≤ d x ∧ d x < r j} := fun j =>
    (measurableSet_le measurable_const hdm).inter (measurableSet_lt hdm measurable_const)
  have hWIM : ∀ j, IsIntegerMultiplicity (W j) := by
    intro j
    cases j with
    | zero => exact hIMsub _ _ hE0 hW0i
    | succ j => exact hIMsub _ _ (hEs j) (hWsi j)
  -- Step 9: the boundary relations, pointwise
  have hW0b : (W 0).boundary = D 0 - Z 0 := by
    rw [hW0, hD0, hZd]
    ext η
    simp only [hsub, GeometricCurrentOn.boundary_apply]
    ring
  have hWsb : ∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j) := by
    intro j
    rw [hWs, hDs, hZd, hZd]
    ext η
    simp only [hsub, GeometricCurrentOn.boundary_apply]
    ring
  -- Step 10c: `spt Zⱼ ⊆ spt T ∩ {d = rⱼ}`
  have hZspt : ∀ j, (Z j).support ⊆ T.support ∩ {x | d x = r j} := by
    intro j
    rw [hZd]
    refine subset_inter ((hS3 _ _).trans (union_subset ((hS5 _).trans (hAspt j))
      ((hBspt j).trans (hS5 T)))) (hS1 _ _ (isClosed_eq hdc continuous_const) fun η hη => ?_)
    rw [hsub, hAB (r j) η hη, sub_self]
  -- Step 11: masses; `M(Zⱼ)` by the slicing estimate at the good radius `rⱼ`
  have hZM : ∀ j, (Z j).mass ≤
      4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * T.mass := by
    intro j
    have h := hZ univ (r j) isOpen_univ
    simp only [univ_inter, ENNReal.coe_one, one_mul] at h
    rw [hZd]
    exact h.trans (hlim j)
  have hDf : ∀ j, (D j).mass < ∞ := by
    intro j
    cases j with
    | zero => exact hD0M.trans_lt (measure_lt_top μ' univ)
    | succ j => exact (hDsM j).trans_lt (measure_lt_top μ' _)
  have hZf : ∀ j, (Z j).mass < ∞ := fun j => (hZM j).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top
      ENNReal.coe_lt_top) ENNReal.ofReal_lt_top) hTm)
  -- Step 12: boundary masses; slicing `∂T` a second time gives `M(∂B_{rⱼ}) < ∞`
  obtain ⟨hBsub, hBbd⟩ := Submission.dimred_mbl_dtsd_sh_boundaryMassOn_calculus P m univ univ
  have hBf : ∀ j, boundaryMassOn (B (r j)) univ < ∞ := by
    intro j
    have h := Submission.dimred_mbl_dtsd_sh_slice_boundaryMassOn_le hSL P m univ T μ' ξ' d 1
      (r j) (B (r j)) univ isOpen_univ isOpen_univ (fun K _ _ => measure_lt_top μ' K) hξ'm hξ'b
      hbrep hd (hB (r j))
    simp only [univ_inter, ENNReal.coe_one, one_mul] at h
    exact h.trans_lt (hlim' j)
  refine ⟨r, W, D, Z, hr, hsum, hW0b, hWsb, hWIM, fun j => ?_, fun j => ?_, fun j => ?_, hWspt,
    hDspt, hZspt, hW0M.trans (hTμ univ isOpen_univ).ge, fun j => (hWsM j).trans (hrμ j).1,
    hD0M.trans (hbμ univ isOpen_univ).ge, fun j => (hDsM j).trans (hrμ j).2, hZM⟩
  · -- `Wⱼ`: compact support, finite mass and finite boundary mass (Step 12a)
    refine ⟨hTc.of_isClosed_subset (hS2' _) ((hWspt j).trans inter_subset_left), ?_, ?_⟩
    · cases j with
      | zero => exact hW0M.trans_lt (measure_lt_top μ univ)
      | succ j => exact (hWsM j).trans_lt (measure_lt_top μ _)
    · cases j with
      | zero =>
        rw [hW0b]
        exact (Submission.cmc_fc_cs_massOn_sub_le P m univ univ _ _).trans_lt
          (ENNReal.add_lt_top.2 ⟨hDf 0, hZf 0⟩)
      | succ j =>
        rw [hWsb j]
        exact (Submission.cmc_fc_cs_massOn_sub_le P m univ univ _ _).trans_lt
          (ENNReal.add_lt_top.2 ⟨hDf (j + 1), (Submission.cmc_fc_cs_massOn_sub_le P m univ univ
            _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hZf (j + 1), hZf j⟩)⟩)
  · -- `Dⱼ`: `spt Dⱼ ⊆ spt ∂T ⊆ spt T`; `∂D₀ = ∂∂T − ∂B_{r₀}`, `∂D_{j+1} = ∂B_{rⱼ} − ∂B_{r_{j+1}}`
    refine ⟨hTc.of_isClosed_subset (hS2 _) ((hDspt j).trans (inter_subset_left.trans (hS5 T))),
      hDf j, ?_⟩
    cases j with
    | zero =>
      rw [hD0]
      exact (hBsub _ _).trans_lt (by rw [hBbd, zero_add]; exact hBf 0)
    | succ j =>
      rw [hDs]
      exact (hBsub _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hBf j, hBf (j + 1)⟩)
  · -- `Zⱼ`: `∂Zⱼ = ∂∂A_{rⱼ} − ∂B_{rⱼ}`
    refine ⟨hTc.of_isClosed_subset (hS2 _) ((hZspt j).trans inter_subset_left), hZf j, ?_⟩
    rw [hZd]
    exact (hBsub _ _).trans_lt (by rw [hBbd, zero_add]; exact hBf j)
/-- **Telescoping series** (Simon Ch. 6, proof of 5.1: the passage from the limits (19) to the
identity (21), chapter-06.txt lines 1792–1820): if `∑ⱼ aⱼ = s`, `a₀ = −k₀`, `aⱼ₊₁ = kⱼ − kⱼ₊₁`
and `kⱼ → 0`, then `s = 0`.  The partial sums telescope, `∑_{i ≤ N} aᵢ = −k_N`; they tend to `s`
because the series converges, and to `−0 = 0` because `k_N → 0`, so `s = 0` by uniqueness of
limits. -/
theorem Submission.cmcsdtd_hasSum_telescoping_eq_zero : ∀ (a k : ℕ → ℝ) (s : ℝ), HasSum a s → a 0 = -k 0 → (∀ j, a (j + 1) = k j - k (j + 1)) → Tendsto k atTop (𝓝 0) → s = 0 := by
  intro a k s hs h0 hsucc hk
  -- Step 1: the partial sums telescope, `∑_{i ≤ N} aᵢ = −k_N`
  have hpart : ∀ N, ∑ i ∈ Finset.range (N + 1), a i = -k N := by
    intro N
    induction N with
    | zero => simp [h0]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hsucc]
      ring
  -- Step 2: the series converges, so its partial sums `∑_{i ≤ N} aᵢ` tend to `s`
  have h1 : Tendsto (fun N => ∑ i ∈ Finset.range (N + 1), a i) atTop (𝓝 s) :=
    hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  -- Step 3: by step 1 they are `−k_N`, which tends to `−0 = 0`
  have h2 : Tendsto (fun N => ∑ i ∈ Finset.range (N + 1), a i) atTop (𝓝 0) := by
    simp_rw [hpart]
    simpa using hk.neg
  -- Step 4: limits in `ℝ` are unique
  exact tendsto_nhds_unique h1 h2

/-- **Mass controls evaluation** (Simon Ch. 6, 2.4–2.5; used in proving the deformation theorem
5.1, chapter-06.txt lines 1792–1838: mass-Cauchy deformed pieces converge weakly, (19), and the
masses of the limits are estimated as in (24)–(25)).  If `|ω(x)| ≤ c` for all `x`
(`cmc_fc_sc_testForm_coeff_bound`), then 6.2.5 with `W = U` (`cmr_abs_apply_le_massOn`) gives
`|X_j(ω)| ≤ c M(X_j)` whenever `M(X_j) < ∞`.  (i) If `M(X_j) → 0`, then `M(X_j)` is eventually
finite and `c M(X_j) → 0`, so `X_j(ω) → 0` by squeezing.  (ii) If `Σ_j M(X_j) < ∞`, every
`M(X_j)` is finite and `Σ_j X_j(ω)` converges by comparison with `Σ_j c M(X_j)`; for `ω`
admissible for `M(Y)`, `Y(ω) = Σ_j X_j(ω) ≤ Σ_j |X_j(ω)| ≤ Σ_j M(X_j)`, and the supremum over
such `ω` gives `M(Y) ≤ Σ_j M(X_j)`. -/
theorem Submission.cmcsdtd_mass_controls_eval : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), (Tendsto (fun j => (X j).mass) atTop (𝓝 0) → ∀ ω : TestFormOn U n, Tendsto (fun j => X j ω) atTop (𝓝 0)) ∧ (∑' j, (X j).mass < ∞ → (∀ ω : TestFormOn U n, Summable (fun j => X j ω)) ∧ ∀ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun j => X j ω) (Y ω)) → Y.mass ≤ ∑' j, (X j).mass) := by
  intro P n U X
  -- Step 1: `|X_j(ω)| ≤ r M(X_j)` if `M(X_j) < ∞` and `|ω(x)| ≤ r` (6.2.5 with `W = U`)
  have hEB : ∀ (ω : TestFormOn U n) (r : ℝ) (j : ℕ), (X j).mass ≠ ∞ →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) →
      |X j ω| ≤ r * (X j).mass.toReal := fun ω r j hj hr =>
    Submission.cmr_abs_apply_le_massOn P n U U (X j) ω r hj ω.property.2 hr
  refine ⟨fun hlim ω => ?_, fun hsum => ?_⟩
  · -- Step 2: (i), `M(X_j)` is eventually finite and `c M(X_j) → 0`; squeeze
    obtain ⟨c, -, hc⟩ := Submission.cmc_fc_sc_testForm_coeff_bound P n U ω
    have hfin : ∀ᶠ j in atTop, (X j).mass ≠ ∞ :=
      (hlim.eventually (gt_mem_nhds zero_lt_one)).mono fun j hj =>
        (hj.trans ENNReal.one_lt_top).ne
    have hreal : Tendsto (fun j => (X j).mass.toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
      rwa [ENNReal.toReal_zero] at h
    have hbound : Tendsto (fun j => c * (X j).mass.toReal) atTop (𝓝 0) := by
      simpa using hreal.const_mul c
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hfin] with j hj
    rw [Real.norm_eq_abs]
    exact hEB ω c j hj hc
  · -- Step 3: every `M(X_j)` is finite and `Σ_j M(X_j)` is a summable real series
    have hfin : ∀ j, (X j).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum.ne
    have hsumR : Summable fun j => (X j).mass.toReal := ENNReal.summable_toReal hsum.ne
    refine ⟨fun ω => ?_, fun Y hY => ?_⟩
    · -- Step 4: (ii)(a), comparison with `Σ_j c M(X_j)`
      obtain ⟨c, -, hc⟩ := Submission.cmc_fc_sc_testForm_coeff_bound P n U ω
      refine Summable.of_norm_bounded (hsumR.mul_left c) fun j => ?_
      rw [Real.norm_eq_abs]
      exact hEB ω c j (hfin j) hc
    · -- Step 5: (ii)(b), `Y(ω) = Σ_j X_j(ω) ≤ Σ_j |X_j(ω)| ≤ Σ_j M(X_j)` for admissible `ω`
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      have hb : ∀ j, |X j ω| ≤ (X j).mass.toReal := fun j =>
        (hEB ω 1 j (hfin j) hω.2).trans_eq (one_mul _)
      have habs : Summable fun j => |X j ω| :=
        Summable.of_nonneg_of_le (fun j => abs_nonneg _) hb hsumR
      have hle : Y ω ≤ ∑' j, (X j).mass.toReal := by
        rw [← (hY ω).tsum_eq]
        calc ∑' j, X j ω ≤ ∑' j, |X j ω| :=
              Summable.tsum_le_tsum (fun j => le_abs_self _) (hY ω).summable habs
          _ ≤ ∑' j, (X j).mass.toReal := Summable.tsum_le_tsum hb habs hsumR
      calc ENNReal.ofReal (Y ω) ≤ ENNReal.ofReal (∑' j, (X j).mass.toReal) :=
            ENNReal.ofReal_le_ofReal hle
        _ = ∑' j, (X j).mass := by
            rw [← ENNReal.tsum_toReal_eq hfin, ENNReal.ofReal_toReal hsum.ne]
/-- **Deformation of the shells** (Simon 6.5.1, proof, displays (11)–(16), (20), (22)–(23);
chapter-06.txt lines 1740–1830).  Let `push`, `homot` satisfy the properties (PF) of push-forward
and straight-line homotopy under Lipschitz maps, and let `∂W₀ = D₀ − Z₀`,
`∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`.  The homotopy formula for the homotopy `h_j` from `φ_j`
to `id`, with `push(id, W_j) = W_j`, gives `W_j − φ_{j#}W_j − h_{j#}∂W_j = ∂h_{j#}W_j`; linearity
and locality (`φ_{j+1} = φ_j` on `spt Z_j`) split `φ_{j#}∂W_j` and `h_{j#}∂W_j` into telescoping
differences.  The deformed currents are integer multiplicity, `Λ_j^k ≤ (2Λ_j)^k` gives the mass
bounds, and `|φ_j(x) + t(x − φ_j(x)) − x| = (1 − t)|φ_j(x) − x| ≤ δ` gives the supports. -/
theorem Submission.cmcsdtd_shell_deformation : ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ((∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary) → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, IsClosed X.support) → (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m, (A - B).support ⊆ A.support ∪ B.support) → ∀ (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (δ : ℝ) (L A A' : Set (Euclid P)), (W 0).boundary = D 0 - Z 0 → (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) → (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) → (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (Z j).support) → (∀ j, ∀ x ∈ (W j).support ∪ (D j).support ∪ (Z j).support, dist (φ j x) x ≤ δ) → (∀ j, ∀ x ∈ (W j).support, φ j x ∈ L) → (∀ j, (W j).support ⊆ A) → (∀ j, (D j).support ⊆ A') → W 0 - push (m + 1) (φ 0) (W 0) - (homot m (φ 0) (fun x => x) (D 0) - homot m (φ 0) (fun x => x) (Z 0)) = (homot (m + 1) (φ 0) (fun x => x) (W 0)).boundary ∧ (∀ j, W (j + 1) - push (m + 1) (φ (j + 1)) (W (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (D (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (Z (j + 1)) - homot m (φ j) (fun x => x) (Z j))) = (homot (m + 1) (φ (j + 1)) (fun x => x) (W (j + 1))).boundary) ∧ (push (m + 1) (φ 0) (W 0)).boundary = push m (φ 0) (D 0) - push m (φ 0) (Z 0) ∧ (∀ j, (push (m + 1) (φ (j + 1)) (W (j + 1))).boundary = push m (φ (j + 1)) (D (j + 1)) - (push m (φ (j + 1)) (Z (j + 1)) - push m (φ j) (Z j))) ∧ (∀ j, IsIntegerMultiplicity (push (m + 1) (φ j) (W j)) ∧ IsIntegerMultiplicity (homot (m + 1) (φ j) (fun x => x) (W j))) ∧ (∀ j, (push (m + 1) (φ j) (W j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass) ∧ (push m (φ j) (D j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass ∧ (homot m (φ j) (fun x => x) (D j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass) ∧ (push m (φ j) (Z j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass ∧ (homot m (φ j) (fun x => x) (Z j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass)) ∧ (∀ j, (push (m + 1) (φ j) (W j)).support ⊆ L ∩ cthickening δ A ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).support ⊆ cthickening δ A ∧ (push m (φ j) (D j)).support ⊆ cthickening δ A' ∧ (homot m (φ j) (fun x => x) (D j)).support ⊆ cthickening δ A') := by
  intro P m push homot hPF hSii hSiii W D Z φ Λ δ L A A' hW0 hWs hIM hWnc hDnc hZnc hLip h1 hmono
    hEq hdist hφL hWA hDA
  obtain ⟨PF1, PF2, PF3, PF4, PF5, -⟩ := hPF
  -- Step 1: `id` is `Λ_j`-Lipschitz (`1 ≤ Λ_j`) and `φ_j` is `Λ_{j+1}`-Lipschitz (`Λ_j ≤ Λ_{j+1}`)
  have hidLip : ∀ j, LipschitzWith (Λ j) (fun x : Euclid P => x) := fun j =>
    LipschitzWith.id.weaken (h1 j)
  have hφLip : ∀ j, LipschitzWith (Λ (j + 1)) (φ j) := fun j => (hLip j).weaken (hmono j)
  -- Step 2: `W_j`, `D_j`, `Z_j` are normal with compact support (for `W_j`, the boundary mass
  -- `boundaryMassOn (W j) univ` is `M(∂W_j)` by definition).
  -- Step 3: so is `Z_{j+1} − Z_j`: its support is closed and lies in `spt Z_{j+1} ∪ spt Z_j`,
  -- and `M(X − Y) ≤ M(X) + M(Y)`, with `∂(X − Y) = ∂X − ∂Y` in positive degree
  have hbmsub : ∀ (n : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) n),
      boundaryMassOn X univ < ∞ → boundaryMassOn Y univ < ∞ → boundaryMassOn (X - Y) univ < ∞ := by
    intro n X Y hX hY
    cases n with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      have e : (X - Y).boundary = X.boundary - Y.boundary := by
        ext ω
        rfl
      show (X - Y).boundary.massOn univ < ∞
      rw [e]
      exact (Submission.cmc_fc_cs_massOn_sub_le P k univ univ X.boundary Y.boundary).trans_lt
        (ENNReal.add_lt_top.2 ⟨hX, hY⟩)
  have hZd : ∀ j, IsCompact (Z (j + 1) - Z j).support ∧ (Z (j + 1) - Z j).mass < ∞ ∧
      boundaryMassOn (Z (j + 1) - Z j) univ < ∞ := by
    intro j
    obtain ⟨hc1, hm1, hb1⟩ := hZnc (j + 1)
    obtain ⟨hc0, hm0, hb0⟩ := hZnc j
    refine ⟨(hc1.union hc0).of_isClosed_subset (hSii _) (hSiii _ _), ?_, hbmsub m _ _ hb1 hb0⟩
    exact (Submission.cmc_fc_cs_massOn_sub_le P m univ univ _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨hm1, hm0⟩)
  -- Step 4: locality, as `φ_{j+1} = φ_j` on `spt Z_j`
  have hloc : ∀ j, push m (φ (j + 1)) (Z j) = push m (φ j) (Z j) ∧
      homot m (φ (j + 1)) (fun x => x) (Z j) = homot m (φ j) (fun x => x) (Z j) := fun j =>
    PF3 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (φ j) (fun x => x) (Z j) (hLip (j + 1))
      (hidLip (j + 1)) (hφLip j) (hidLip (j + 1)) (hZnc j).1 (hZnc j).2.1 (hZnc j).2.2 (hEq j)
      (fun _ _ => rfl)
  -- Step 5: linearity deforms `∂W₀ = D₀ − Z₀` and `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`
  have hlin0 := PF2 m (Λ 0) (φ 0) (fun x => x) (D 0) (Z 0) (hLip 0) (hidLip 0) (hDnc 0).1
    (hDnc 0).2.1 (hDnc 0).2.2 (hZnc 0).1 (hZnc 0).2.1 (hZnc 0).2.2
  have hlinS : ∀ j, push m (φ (j + 1)) (D (j + 1) - (Z (j + 1) - Z j)) =
        push m (φ (j + 1)) (D (j + 1)) - (push m (φ (j + 1)) (Z (j + 1)) - push m (φ j) (Z j)) ∧
      homot m (φ (j + 1)) (fun x => x) (D (j + 1) - (Z (j + 1) - Z j)) =
        homot m (φ (j + 1)) (fun x => x) (D (j + 1)) -
          (homot m (φ (j + 1)) (fun x => x) (Z (j + 1)) - homot m (φ j) (fun x => x) (Z j)) := by
    intro j
    obtain ⟨e1, e2⟩ := PF2 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (D (j + 1)) (Z (j + 1) - Z j)
      (hLip (j + 1)) (hidLip (j + 1)) (hDnc (j + 1)).1 (hDnc (j + 1)).2.1 (hDnc (j + 1)).2.2
      (hZd j).1 (hZd j).2.1 (hZd j).2.2
    obtain ⟨e3, e4⟩ := PF2 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (Z (j + 1)) (Z j)
      (hLip (j + 1)) (hidLip (j + 1)) (hZnc (j + 1)).1 (hZnc (j + 1)).2.1 (hZnc (j + 1)).2.2
      (hZnc j).1 (hZnc j).2.1 (hZnc j).2.2
    rw [e1, e3, (hloc j).1, e2, e4, (hloc j).2]
    exact ⟨rfl, rfl⟩
  -- Step 6: the homotopy formula from `φ_j` to `id` on `W_j`, where `push_{m+1}(id, W_j) = W_j`
  have hPF5 := fun j => PF5 m (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
    (hWnc j).2.1 (hWnc j).2.2
  have hPF1 : ∀ j, push (m + 1) (fun x => x) (W j) = W j := fun j =>
    PF1 (m + 1) (W j) (hWnc j).1 (hWnc j).2.1 (hWnc j).2.2
  -- Step 7: in `[0, ∞]`, `Λ_j^k ≤ (2Λ_j)^k`
  have hpow : ∀ (j k : ℕ) (M : ℝ≥0∞), (Λ j : ℝ≥0∞) ^ k * M ≤ (2 * (Λ j : ℝ≥0∞)) ^ k * M :=
    fun j k M => by
      gcongr
      exact le_mul_of_one_le_left zero_le one_le_two
  -- Step 8: `φ_j(x) + t(x − φ_j(x)) − x = (1 − t)(φ_j(x) − x)`, so the segment from `φ_j(x)` to
  -- `x` stays within `δ` of `x`
  have hseg : ∀ (j : ℕ) (S B : Set (Euclid P)), S ⊆ B → (∀ x ∈ S, dist (φ j x) x ≤ δ) →
      {y : Euclid P | ∃ x ∈ S, ∃ t ∈ Icc (0 : ℝ) 1, y = φ j x + t • (x - φ j x)} ⊆
        cthickening δ B := by
    rintro j S B hSB hd _ ⟨x, hx, t, ht, rfl⟩
    refine mem_cthickening_of_dist_le _ x δ B (hSB hx) ?_
    have e : φ j x + t • (x - φ j x) - x = (1 - t) • (φ j x - x) := by
      rw [sub_smul, one_smul, smul_sub, smul_sub]
      abel
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    calc dist (φ j x + t • (x - φ j x)) x = (1 - t) * dist (φ j x) x := by
          rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1t, dist_eq_norm]
      _ ≤ 1 * dist (φ j x) x := by gcongr; linarith [ht.1]
      _ ≤ δ := by rw [one_mul]; exact hd x hx
  refine ⟨?_, fun j => ?_, ?_, fun j => ?_, fun j => (hPF5 j).2.2 (hIM j), fun j => ?_, fun j => ?_⟩
  · -- (c1): substitute `∂W₀ = D₀ − Z₀` into the homotopy formula
    have e := (hPF5 0).2.1
    rw [hPF1 0, hW0, hlin0.2] at e
    exact e
  · -- (c2): substitute `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`
    have e := (hPF5 (j + 1)).2.1
    rw [hPF1 (j + 1), hWs j, (hlinS j).2] at e
    exact e
  · -- (c3): `∂φ_{0#}W₀ = φ_{0#}∂W₀`
    rw [(hPF5 0).1, hW0, hlin0.1]
  · -- (c4): `∂φ_{j+1#}W_{j+1} = φ_{j+1#}∂W_{j+1}`
    rw [(hPF5 (j + 1)).1, hWs j, (hlinS j).1]
  · -- (c6): mass bounds, with `|φ_j(x) − x| ≤ δ` on the supports
    have hW4 := PF4 (m + 1) (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
      (hWnc j).2.1 (hWnc j).2.2
    have hD4 := PF4 m (Λ j) (φ j) (fun x => x) (D j) (hLip j) (hidLip j) (hDnc j).1 (hDnc j).2.1
      (hDnc j).2.2
    have hZ4 := PF4 m (Λ j) (φ j) (fun x => x) (Z j) (hLip j) (hidLip j) (hZnc j).1 (hZnc j).2.1
      (hZnc j).2.2
    refine ⟨hW4.1.trans (hpow j _ _), ?_, hD4.1.trans (hpow j _ _), ?_,
      hZ4.1.trans (hpow j _ _), ?_⟩
    · rw [← mul_assoc]
      exact hW4.2.2.1 δ fun x hx => hdist j x (Or.inl (Or.inl hx))
    · rw [← mul_assoc]
      exact hD4.2.2.1 δ fun x hx => hdist j x (Or.inl (Or.inr hx))
    · rw [← mul_assoc]
      exact hZ4.2.2.1 δ fun x hx => hdist j x (Or.inr hx)
  · -- (c7): supports, via `spt φ_{j#}X ⊆ φ_j(spt X)` and Step 8
    have hW4 := PF4 (m + 1) (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
      (hWnc j).2.1 (hWnc j).2.2
    have hD4 := PF4 m (Λ j) (φ j) (fun x => x) (D j) (hLip j) (hidLip j) (hDnc j).1 (hDnc j).2.1
      (hDnc j).2.2
    refine ⟨hW4.2.1.trans ?_, hW4.2.2.2.trans (hseg j _ A (hWA j) fun x hx =>
      hdist j x (Or.inl (Or.inl hx))), hD4.2.1.trans ?_, hD4.2.2.2.trans (hseg j _ A' (hDA j)
      fun x hx => hdist j x (Or.inl (Or.inr hx)))⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hφL j x hx, mem_cthickening_of_dist_le _ x δ A (hWA j hx)
        (hdist j x (Or.inl (Or.inl hx)))⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_cthickening_of_dist_le _ x δ A' (hDA j hx) (hdist j x (Or.inl (Or.inr hx)))

/-- **Summation of the deformed shells** (Simon Ch. 6, proof of 5.1, displays (17)–(25)).  The mass
series of the pieces `V_j`, `H_j`, `Y_j`, `E′_j` are dominated by `Σ a_j`, `δ Σ a_j`, `Σ b_j`,
`δ Σ b_j < ∞`, so `(IMS)` sums `V_j`, `H_j`, `E′_j` to `Q₀`, `R₁`, `S₁`, with supports in the closed
sets `K₁`, `K₂`, `K₃`.  At a test form `ω`, (I1)–(I2) make the series of
`(W_j − V_j − E′_j)(ω) − H_j(dω)` telescope with remainder `−K_N(ω) → 0` (`M(K_N) ≤ δ c_N → 0`), so
`T − Q₀ − S₁ = ∂R₁`; likewise (I3)–(I4) give `∂Q₀(η) = Σ_j Y_j(η)` (remainder `−L′_N(η) → 0`).
Hence `M(∂Q₀) ≤ Σ_j M(Y_j)`, and `∂Q₀` vanishes on forms supported off `K₃ ⊇ spt Y_j`. -/
theorem Submission.cmcsdtd_deformed_series_sum : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) E → X ω = 0) → X.support ⊆ E) → (∀ (k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W V E' K : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (H : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (Y L' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (a b c : ℕ → ℝ≥0∞) (δ : ℝ) (K₁ K₂ K₃ : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) → W 0 - V 0 - (E' 0 - K 0) = (H 0).boundary → (∀ j, W (j + 1) - V (j + 1) - (E' (j + 1) - (K (j + 1) - K j)) = (H (j + 1)).boundary) → (V 0).boundary = Y 0 - L' 0 → (∀ j, (V (j + 1)).boundary = Y (j + 1) - (L' (j + 1) - L' j)) → (∀ j, IsIntegerMultiplicity (V j) ∧ IsIntegerMultiplicity (H j)) → (∀ j, (V j).mass ≤ a j ∧ (H j).mass ≤ ENNReal.ofReal δ * a j ∧ (Y j).mass ≤ b j ∧ (E' j).mass ≤ ENNReal.ofReal δ * b j ∧ (L' j).mass ≤ c j ∧ (K j).mass ≤ ENNReal.ofReal δ * c j) → ∑' j, a j < ∞ → ∑' j, b j < ∞ → Tendsto c atTop (𝓝 0) → IsClosed K₁ → IsClosed K₂ → IsClosed K₃ → (∀ j, (V j).support ⊆ K₁ ∧ (H j).support ⊆ K₂ ∧ (Y j).support ⊆ K₃ ∧ (E' j).support ⊆ K₃) → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ K₁ ∧ R₁.support ⊆ K₂ ∧ Q₀.boundary.support ⊆ K₃ ∧ S₁.support ⊆ K₃ ∧ Q₀.mass ≤ ∑' j, a j ∧ Q₀.boundary.mass ≤ ∑' j, b j ∧ R₁.mass ≤ ENNReal.ofReal δ * ∑' j, a j ∧ S₁.mass ≤ ENNReal.ofReal δ * ∑' j, b j := by
  intro hVO P m hSi hIMS T W V E' K H Y L' a b c δ K₁ K₂ K₃ hT h0 hs hb0 hbs hIM hmass hsa hsb
    hc hK₁ hK₂ hK₃ hspt
  -- `ME` for currents in `ℝᴾ` of degrees `m` and `m + 1`
  have hME0 := Submission.cmcsdtd_mass_controls_eval P m univ
  have hME1 := Submission.cmcsdtd_mass_controls_eval P (m + 1) univ
  -- Step 1: termwise comparison of the mass series; all four are finite since `ofReal δ < ∞`
  have hVsum : ∑' j, (V j).mass ≤ ∑' j, a j := ENNReal.tsum_le_tsum fun j => (hmass j).1
  have hHsum : ∑' j, (H j).mass ≤ ENNReal.ofReal δ * ∑' j, a j := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hmass j).2.1
  have hYsum : ∑' j, (Y j).mass ≤ ∑' j, b j := ENNReal.tsum_le_tsum fun j => (hmass j).2.2.1
  have hEsum : ∑' j, (E' j).mass ≤ ENNReal.ofReal δ * ∑' j, b j := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hmass j).2.2.2.1
  have hVfin : ∑' j, (V j).mass < ∞ := hVsum.trans_lt hsa
  have hHfin : ∑' j, (H j).mass < ∞ :=
    hHsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsa)
  have hYfin : ∑' j, (Y j).mass < ∞ := hYsum.trans_lt hsb
  have hEfin : ∑' j, (E' j).mass < ∞ :=
    hEsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsb)
  -- Step 2: `0 ≤ M(L′_j) ≤ c_j → 0` and `0 ≤ M(K_j) ≤ δ c_j → δ · 0 = 0`
  have hLlim : Tendsto (fun j => (L' j).mass) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => zero_le)
      fun j => (hmass j).2.2.2.2.1
  have hKlim : Tendsto (fun j => (K j).mass) atTop (𝓝 0) := by
    have hδc : Tendsto (fun j => ENNReal.ofReal δ * c j) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδc (fun _ => zero_le)
      fun j => (hmass j).2.2.2.2.2
  -- Step 3: `(IMS)` sums `V_j`, `H_j` (degree `(m + 1) + 1 = m + 2`) and `E′_j`
  obtain ⟨Q₀, hQs, hQm, hQspt, hQim⟩ := hIMS m V hVfin
  obtain ⟨R₁, hRs, hRm, hRspt, hRim⟩ := hIMS (m + 1) H hHfin
  obtain ⟨S₁, hSs, hSm, hSspt, -⟩ := hIMS m E' hEfin
  -- Step 4: `α_j = W_j(ω) − V_j(ω) − E′_j(ω) − H_j(dω)` sums to `(T − Q₀ − S₁)(ω) − R₁(dω)`; by
  -- (I1)–(I2), `α₀ = −K₀(ω)` and `α_{j+1} = K_j(ω) − K_{j+1}(ω)`, with `K_j(ω) → 0` (`ME` (i))
  have hid : T - Q₀ - S₁ = R₁.boundary := by
    ext ω
    have hsum := (((hT ω).sub (hQs ω)).sub (hSs ω)).sub
      (hRs (exteriorDerivativeTestOn univ (m + 1) ω))
    have hz := Submission.cmcsdtd_hasSum_telescoping_eq_zero _ (fun j => K j ω) _ hsum ?_ ?_
      ((hME1 K).1 hKlim ω)
    · change T ω - Q₀ ω - S₁ ω = R₁ (exteriorDerivativeTestOn univ (m + 1) ω)
      linarith
    · have e := congrArg (fun X => X ω) h0
      change W 0 ω - V 0 ω - (E' 0 ω - K 0 ω) = H 0 (exteriorDerivativeTestOn univ (m + 1) ω) at e
      linarith
    · intro j
      have e := congrArg (fun X => X ω) (hs j)
      change W (j + 1) ω - V (j + 1) ω - (E' (j + 1) ω - (K (j + 1) ω - K j ω)) =
        H (j + 1) (exteriorDerivativeTestOn univ (m + 1) ω) at e
      linarith
  -- Step 5: `β_j = V_j(dη) − Y_j(η)` sums to `Q₀(dη) − Σ_j Y_j(η)` (`ME` (ii)(a)); by (I3)–(I4),
  -- `β₀ = −L′₀(η)` and `β_{j+1} = L′_j(η) − L′_{j+1}(η)`, with `L′_j(η) → 0` (`ME` (i))
  have hbd : ∀ η : TestFormOn (univ : Set (Euclid P)) m,
      HasSum (fun j => Y j η) (Q₀.boundary η) := by
    intro η
    have hYs := ((hME0 Y).2 hYfin).1 η
    have hsum := (hQs (exteriorDerivativeTestOn univ m η)).sub hYs.hasSum
    have hz := Submission.cmcsdtd_hasSum_telescoping_eq_zero _ (fun j => L' j η) _ hsum ?_ ?_
      ((hME0 L').1 hLlim η)
    · have hq : Q₀.boundary η = ∑' j, Y j η := by
        change Q₀ (exteriorDerivativeTestOn univ m η) = _
        linarith
      rw [hq]
      exact hYs.hasSum
    · have e := congrArg (fun X => X η) hb0
      change V 0 (exteriorDerivativeTestOn univ m η) = Y 0 η - L' 0 η at e
      linarith
    · intro j
      have e := congrArg (fun X => X η) (hbs j)
      change V (j + 1) (exteriorDerivativeTestOn univ m η) =
        Y (j + 1) η - (L' (j + 1) η - L' j η) at e
      linarith
  -- Step 6: `M(∂Q₀) ≤ Σ_j M(Y_j) ≤ Σ_j b_j` (`ME` (ii)(b))
  have hbdm : Q₀.boundary.mass ≤ ∑' j, b j :=
    (((hME0 Y).2 hYfin).2 Q₀.boundary hbd).trans hYsum
  -- Step 7: off `K₃` every `Y_j` vanishes (`(VO)`, `spt Y_j ⊆ K₃`), hence so does `∂Q₀`; `(S-i)`
  have hbdspt : Q₀.boundary.support ⊆ K₃ := by
    refine hSi K₃ Q₀.boundary hK₃ fun η hη => ?_
    have hY0 : (fun j => Y j η) = fun _ => (0 : ℝ) := funext fun j =>
      hVO P m univ (Y j) η (hη.mono_right (hspt j).2.2.1)
    have h := hbd η
    rw [hY0] at h
    exact h.unique hasSum_zero
  -- Step 8: `spt` of a sum lies in `closure ⋃_j spt ⊆ K_i`, as `K_i` is closed
  refine ⟨Q₀, R₁, S₁, hQim fun j => (hIM j).1, hRim fun j => (hIM j).2, hid,
    hQspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).1) hK₁),
    hRspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).2.1) hK₂), hbdspt,
    hSspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).2.2.2) hK₃),
    hQm.trans hVsum, hbdm, hRm.trans hHsum, hSm.trans hEsum⟩

/-- **Deformation of a decomposed current and summation of the deformed series** (Simon Ch. 6,
proof of 5.1, displays (11)–(25), chapter-06.txt lines 1742–1838), with the homotopy taken from
`φⱼ` to the identity.  Deform each piece by `φⱼ`: `Vⱼ = push(φⱼ, Wⱼ)`, `Hⱼ = homot(φⱼ, id, Wⱼ)`,
`Yⱼ = push(φⱼ, Dⱼ)`, `E'ⱼ = homot(φⱼ, id, Dⱼ)`, `L'ⱼ = push(φⱼ, Zⱼ)`, `Kⱼ = homot(φⱼ, id, Zⱼ)`.
By `cmcsdtd_shell_deformation` ((PF) with the support calculus (ii)–(iii) of
`dimred_mbl_dtsd_support_calculus`) the homotopy formula gives
`Wⱼ − Vⱼ − (E'ⱼ − (Kⱼ − Kⱼ₋₁)) = ∂Hⱼ` and `∂Vⱼ = Yⱼ − (L'ⱼ − L'ⱼ₋₁)` (`K₋₁ = L'₋₁ = 0`), `Vⱼ` and
`Hⱼ` are integer multiplicity, `M(Vⱼ) ≤ aⱼ`, `M(Yⱼ) ≤ bⱼ`, `M(L'ⱼ) ≤ cⱼ`, `M(Hⱼ) ≤ δaⱼ`,
`M(E'ⱼ) ≤ δbⱼ`, `M(Kⱼ) ≤ δcⱼ` for `aⱼ = (2Λⱼ)^{m+1} M(Wⱼ)`, `bⱼ = (2Λⱼ)^m M(Dⱼ)`,
`cⱼ = (2Λⱼ)^m M(Zⱼ)`, and the supports lie in `L ∩ cthickening δ A`, `cthickening δ A` and
`cthickening δ A'`.  These sets are closed, `∑ aⱼ, ∑ bⱼ < ∞` and `cⱼ → 0`, so
`cmcsdtd_deformed_series_sum` ((VO), support calculus (i), (IMS)) sums the deformed series to
`Q₀ = ∑ Vⱼ`, `R₁ = ∑ Hⱼ`, `S₁ = ∑ E'ⱼ`, and the telescoping gives `T − Q₀ − S₁ = ∂R₁`. -/
theorem Submission.dimred_mbl_dtsd_telescoping_deformation : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ((∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary) → (∀ (k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (δ : ℝ) (L A A' : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) → (W 0).boundary = D 0 - Z 0 → (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) → (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) → (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (Z j).support) → (∀ j, ∀ x ∈ (W j).support ∪ (D j).support ∪ (Z j).support, dist (φ j x) x ≤ δ) → IsClosed L → (∀ j, ∀ x ∈ (W j).support, φ j x ∈ L) → (∀ j, (W j).support ⊆ A) → (∀ j, (D j).support ⊆ A') → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass < ∞ → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass < ∞ → Tendsto (fun j => (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass) atTop (𝓝 0) → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ L ∩ cthickening δ A ∧ R₁.support ⊆ cthickening δ A ∧ Q₀.boundary.support ⊆ cthickening δ A' ∧ S₁.support ⊆ cthickening δ A' ∧ Q₀.mass ≤ ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ Q₀.boundary.mass ≤ ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass ∧ R₁.mass ≤ ENNReal.ofReal δ * ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ S₁.mass ≤ ENNReal.ofReal δ * ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass := by
  intro hVO P m push homot hPF hIMS T W D Z φ Λ δ L A A' hT hW0 hWs hIM hWnc hDnc hZnc hLip h1
    hmono hEq hdist hL hφL hWA hDA hsumW hsumD hZ
  -- Step 1: support calculus in degree `m`: (i) `X` vanishing off a closed `E` has `spt X ⊆ E`,
  -- (ii) `spt X` is closed, (iii) `spt (A − B) ⊆ spt A ∪ spt B`
  obtain ⟨hS1, hS2, hS3, -, -⟩ := Submission.dimred_mbl_dtsd_support_calculus P m
  -- Step 2: the deformed shells satisfy the homotopy identities and the mass and support bounds
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := Submission.cmcsdtd_shell_deformation P m push homot hPF
    hS2 hS3 W D Z φ Λ δ L A A' hW0 hWs hIM hWnc hDnc hZnc hLip h1 hmono hEq hdist hφL hWA hDA
  -- Step 3: sum the deformed series; `L ∩ cthickening δ A`, `cthickening δ A`, `cthickening δ A'`
  -- are closed
  exact Submission.cmcsdtd_deformed_series_sum hVO P m hS1 hIMS T W
    (fun j => push (m + 1) (φ j) (W j)) (fun j => homot m (φ j) (fun x => x) (D j))
    (fun j => homot m (φ j) (fun x => x) (Z j)) (fun j => homot (m + 1) (φ j) (fun x => x) (W j))
    (fun j => push m (φ j) (D j)) (fun j => push m (φ j) (Z j))
    (fun j => (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass)
    (fun j => (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass) (fun j => (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass)
    δ (L ∩ cthickening δ A) (cthickening δ A) (cthickening δ A') hT c1 c2 c3 c4 c5 c6 hsumW
    hsumD hZ (hL.inter isClosed_cthickening) isClosed_cthickening isClosed_cthickening c7
/-- **Simon Ch. 6, 2.4–2.5 and 3.2(1)**, algebra of integer multiplicity currents.  (a) The zero
current is integer multiplicity (empty carrier).  (b) If `A = pB + qC` with `p, q ∈ ℤ`, then
`M_W(A) ≤ |p| M_W(B) + |q| M_W(C)`: `−ω` is admissible with `ω`, so `|X(ω)| ≤ M_W(X)`.  (c) If
differences of integer multiplicity currents in an open `U` are integer multiplicity, then every
finite integer combination `Y = Σᵢ mᵢSᵢ` of integer multiplicity currents is integer multiplicity
(`A + B = A − (0 − B)`), and `M_W(Y) ≤ Σᵢ |mᵢ| M_W(Sᵢ)`. -/
theorem Submission.cbr_cc_current_algebra : (∀ (P n : ℕ) (U : Set (Euclid P)), IsIntegerMultiplicity (0 : GeometricCurrentOn U n)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ), (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P), A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W) ∧ ((∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (ι : Type) (F : Finset ι) (S : ι → GeometricCurrentOn U n) (m : ι → ℤ), IsOpen U → (∀ i ∈ F, IsIntegerMultiplicity (S i)) → ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U n, Y ω = ∑ i ∈ F, (m i : ℝ) * S i ω) ∧ ∀ W : Set (Euclid P), Y.massOn W ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W) := by
  -- (a): the representation with empty carrier, zero multiplicity and zero orientation
  have hzero : ∀ (P n : ℕ) (U : Set (Euclid P)),
      IsIntegerMultiplicity (0 : GeometricCurrentOn U n) := by
    intro P n U
    refine ⟨{ carrier := ∅
              mult := fun _ => 0
              orient := fun _ => 0
              measurableSet_carrier := MeasurableSet.empty
              carrier_subset := empty_subset U
              rectifiable :=
                Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
              measurable_mult := measurable_const
              mult_pos := fun x hx => by simp at hx
              locallyIntegrable_mult := fun K _ _ => by simp
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := by simp }, ?_⟩
    intro ω
    simp [IMRep.action]
  -- `|X(ω)| ≤ M_W(X)` for admissible `ω`, since `−ω` is admissible as well
  have habs : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal |X ω| ≤ X.massOn W := by
    intro P n U X W ω hω
    rcases le_total 0 (X ω) with h | h
    · rw [abs_of_nonneg h]
      exact X.le_massOn hω
    · have hneg : -ω ∈ massAdmissibleOn U n W := by
        refine ⟨?_, fun x => ?_⟩
        · rw [Submodule.coe_neg, tsupport_neg]
          exact hω.1
        · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
          exact hω.2 x
      rw [abs_of_nonpos h, ← map_neg X.toCurrent ω]
      exact X.le_massOn hneg
  -- one term `|k| |X(ω)| ≤ |k| M_W(X)` of an integer combination
  have hterm : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (k : ℤ)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal (|(k : ℝ)| * |X ω|) ≤ (k.natAbs : ℝ≥0∞) * X.massOn W := by
    intro P n U X k W ω hω
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Int.cast_abs, ← Nat.cast_natAbs,
      ENNReal.ofReal_natCast]
    exact mul_le_mul' le_rfl (habs P n U X W ω hω)
  -- (b)
  have hmass : ∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ),
      (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P),
      A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W := by
    intro P n U A B C p q hA W
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    calc ENNReal.ofReal (A ω)
        ≤ ENNReal.ofReal (|(p : ℝ)| * |B ω| + |(q : ℝ)| * |C ω|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hA ω, ← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ = ENNReal.ofReal (|(p : ℝ)| * |B ω|) + ENNReal.ofReal (|(q : ℝ)| * |C ω|) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W :=
          add_le_add (hterm P n U B p W ω hω) (hterm P n U C q W ω hω)
  refine ⟨hzero, hmass, ?_⟩
  -- (c)
  intro hsub P n U ι F S m hU hS
  classical
  have hsubapp : ∀ (A B : GeometricCurrentOn U n) (ω : TestFormOn U n),
      (A - B) ω = A ω - B ω := fun A B ω => rfl
  -- `A − (0 − B)` is integer multiplicity, with values `A(ω) + B(ω)`
  have hadd : ∀ A B : GeometricCurrentOn U n, IsIntegerMultiplicity A →
      IsIntegerMultiplicity B →
      IsIntegerMultiplicity (A - (0 - B)) ∧ ∀ ω, (A - (0 - B)) ω = A ω + B ω := by
    intro A B hA hB
    refine ⟨hsub P n U A (0 - B) hU hA (hsub P n U 0 B hU (hzero P n U) hB), fun ω => ?_⟩
    rw [hsubapp, hsubapp, GeometricCurrentOn.zero_apply]
    ring
  -- natural multiples `k X = X + ⋯ + X`
  have hnat : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℕ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    induction k with
    | zero => exact ⟨0, hzero P n U, fun ω => by simp⟩
    | succ k ih =>
      obtain ⟨V, hV, hVω⟩ := ih
      obtain ⟨hV', hV'ω⟩ := hadd V X hV hX
      refine ⟨V - (0 - X), hV', fun ω => ?_⟩
      rw [hV'ω, hVω]
      push_cast
      ring
  -- integer multiples, `(−k) X = 0 − k X`
  have hint : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℤ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      exact ⟨V, hV, fun ω => by rw [hVω, Int.cast_natCast]⟩
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      refine ⟨0 - V, hsub P n U 0 V hU (hzero P n U) hV, fun ω => ?_⟩
      rw [hsubapp, GeometricCurrentOn.zero_apply, hVω, Int.cast_neg, Int.cast_natCast]
      ring
  -- finite integer combinations, by induction on the index set
  have hsum : ∀ G : Finset ι, (∀ i ∈ G, IsIntegerMultiplicity (S i)) →
      ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧
        ∀ ω, Y ω = ∑ i ∈ G, (m i : ℝ) * S i ω := by
    intro G
    induction G using Finset.induction_on with
    | empty => exact fun _ => ⟨0, hzero P n U, fun ω => by simp⟩
    | insert j G hj ih =>
      intro hG
      obtain ⟨Y, hY, hYω⟩ := ih fun i hi => hG i (Finset.mem_insert_of_mem hi)
      obtain ⟨V, hV, hVω⟩ := hint (S j) (hG j (Finset.mem_insert_self j G)) (m j)
      obtain ⟨hY', hY'ω⟩ := hadd Y V hY hV
      refine ⟨Y - (0 - V), hY', fun ω => ?_⟩
      rw [hY'ω, hYω, hVω, Finset.sum_insert hj]
      ring
  obtain ⟨Y, hY, hYω⟩ := hsum F hS
  refine ⟨Y, hY, hYω, fun W => ?_⟩
  -- the mass bound, from `Y(ω) ≤ Σᵢ |mᵢ| |Sᵢ(ω)|` for admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (Y ω)
      ≤ ENNReal.ofReal (∑ i ∈ F, |(m i : ℝ)| * |S i ω|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hYω]
        exact Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _
    _ = ∑ i ∈ F, ENNReal.ofReal (|(m i : ℝ)| * |S i ω|) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity
    _ ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W :=
        Finset.sum_le_sum fun i _ => hterm P n U (S i) (m i) W ω hω
/-- **Simon Ch. 6, proof of Lemma 5.4, step 5** (local finiteness of the unit cubical grid): every
`y` near `x` lies in one of the finitely many closed unit cubes `z + [0, 1]ᴾ`, `z ∈ ℤᴾ`, that
contain `x`.  In one dimension the intervals `[k, k + 1] ∋ t` with `k ∈ {⌊t⌋ − 1, ⌊t⌋}` cover the
neighbourhood `(⌊t⌋, ⌊t⌋ + 1)` of `t` if `t ∉ ℤ`, and `(t − 1, t + 1)` if `t ∈ ℤ`.  `Z` is the set
of corners in the finite product `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`; for `y` in the
intersection of the finitely many coordinate neighbourhoods the corner is chosen coordinate by
coordinate. -/
theorem Submission.dimred_mbl_dtsr_cube_cover : ∀ (P : ℕ) (x : Euclid P), ∃ Z : Finset (Fin P → ℤ), (∀ z ∈ Z, ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) ∧ ∀ᶠ y : Euclid P in 𝓝 x, ∃ z ∈ Z, ∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1 := by
  intro P x
  classical
  -- step 1: for `t ∈ ℝ`, the intervals `[k, k + 1] ∋ t` with `k ∈ {⌊t⌋ − 1, ⌊t⌋}` cover a
  -- neighbourhood of `t`
  have h1 : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, ∃ k ∈ ({⌊t⌋ - 1, ⌊t⌋} : Finset ℤ),
      ((k : ℝ) ≤ t ∧ t ≤ k + 1) ∧ (k : ℝ) ≤ s ∧ s ≤ k + 1 := by
    intro t
    have hfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have hfl' : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
    rcases hfl.lt_or_eq with hlt | heq
    · -- `t ∉ ℤ`: `[⌊t⌋, ⌊t⌋ + 1]` contains the neighbourhood `(⌊t⌋, ⌊t⌋ + 1)` of `t`
      filter_upwards [Ioo_mem_nhds hlt hfl'] with s hs
      exact ⟨⌊t⌋, by simp, ⟨hfl, hfl'.le⟩, hs.1.le, hs.2.le⟩
    · -- `t ∈ ℤ`: `[t − 1, t] ∪ [t, t + 1]` contains the neighbourhood `(t − 1, t + 1)` of `t`
      filter_upwards [Ioo_mem_nhds (sub_one_lt t) (lt_add_one t)] with s hs
      rcases le_total s t with hst | hts
      · refine ⟨⌊t⌋ - 1, by simp, ?_⟩
        push_cast
        exact ⟨⟨by linarith, by linarith⟩, by linarith [hs.1], by linarith⟩
      · exact ⟨⌊t⌋, by simp, ⟨hfl, hfl'.le⟩, by linarith, by linarith [hs.2]⟩
  -- step 2: `Z` is the set of corners in `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`
  let T : Fin P → Finset ℤ := fun i => {⌊x i⌋ - 1, ⌊x i⌋}
  refine ⟨(Fintype.piFinset T).filter fun z => ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1,
    fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
  -- step 3: pull the neighbourhoods back along the continuous coordinates `y ↦ yᵢ` and intersect
  -- the finitely many of them
  have h3 : ∀ᶠ y : Euclid P in 𝓝 x, ∀ i, ∃ k ∈ T i,
      ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ y i ∧ y i ≤ k + 1 :=
    eventually_all.mpr fun i => ((PiLp.continuous_apply 2 _ i).tendsto x).eventually (h1 (x i))
  -- step 4: choose the corner coordinate by coordinate
  filter_upwards [h3] with y hy
  choose k hkT hk using hy
  exact ⟨k, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hkT, fun i => (hk i).1⟩,
    fun i => (hk i).2⟩
/-- **At most `m + 1` coordinates lie near a cube centre** (Simon Ch. 6, Lemma 5.4, closing
Remark: the cone `K_G` through the centre `b + a` of the cube `b + C` lies in `L*(a)`).  Let
`d = dist(x, L*(a))`, where `L*(a) = {w : w_i − a_i ∈ ℤ for at least m + 2 indices i}`.  If
`m + 2` coordinates had `|x_i − b_i − a_i| < d/√(m + 2)`, moving exactly those coordinates to
`b_i + a_i` would give a point `w ∈ L*(a)` with `|x − w|² < (m + 2) · d²/(m + 2) = d²`.  This
contradicts `d ≤ |x − w|`. -/
theorem Submission.dimred_mbl_dtsr_dual_dist_count : ∀ (P m : ℕ) (a x : Euclid P) (b : Fin P → ℤ), (Finset.univ.filter (fun i => |x i - b i - a i| < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} / Real.sqrt (m + 2))).card ≤ m + 1 := by
  intro P m a x b
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Step 1: otherwise keep exactly `m + 2` coordinates within `d/√(m + 2)` of `b i + a i`
  by_contra hcon
  obtain ⟨s, hsS, hs⟩ := Finset.exists_subset_card_eq (show m + 2 ≤ _ from not_le.mp hcon)
  -- Step 2: moving them to `b i + a i` gives a point of `K_G ⊆ L*(a)`, so `d ≤ |x - w|`
  let w : Euclid P := WithLp.toLp 2 (fun i => if i ∈ s then (b i : ℝ) + a i else x i)
  have hw : ∀ i, w i = if i ∈ s then (b i : ℝ) + a i else x i := fun i => rfl
  have hwL : w ∈ L := ⟨s, hs.ge, fun i hi => ⟨b i, by rw [hw, ite_eq_left hi]; ring⟩⟩
  have hdw : infDist x L ≤ dist x w := infDist_le_dist_of_mem hwL
  -- Step 3: `|x - w|² = ∑_{i ∈ s} (x i - b i - a i)² < (m + 2) · d² / (m + 2) = d²`
  have hm : (0 : ℝ) < m + 2 := by positivity
  have hsum : ∑ i, dist (x i) (w i) ^ 2 = ∑ i ∈ s, (x i - b i - a i) ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by rw [hw, ite_eq_right hi, dist_self]; ring]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hw, ite_eq_left hi, Real.dist_eq, sq_abs]
    ring
  have hlt : ∑ i ∈ s, (x i - b i - a i) ^ 2 < ∑ i ∈ s, infDist x L ^ 2 / (m + 2) := by
    refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) fun i hi => ?_
    have hi' := (Finset.mem_filter.mp (hsS hi)).2
    rw [← sq_abs, ← Real.sq_sqrt hm.le, ← div_pow]
    exact pow_lt_pow_left₀ hi' (abs_nonneg _) two_ne_zero
  rw [Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_add, Nat.cast_two, mul_div_cancel₀ _ hm.ne'] at hlt
  -- Step 4: `d ≤ |x - w| < d`
  have hxw : dist x w < infDist x L := by
    rw [EuclideanSpace.dist_eq, hsum]
    exact (Real.sqrt_lt (Finset.sum_nonneg fun i _ => sq_nonneg _) infDist_nonneg).mpr hlt
  exact hxw.not_ge hdw
/-- **Simon Ch. 6, Lemma 5.4** (proof: the radial retraction of a face from its centre).  Let
`F = {y : b_k ≤ y_k ≤ b_k + 1 (k ∈ J), y_k = b_k (k ∉ J)}` have centre `a_F` (`b_k + a_k` on `J`,
`b_k` off `J`), and let `N(y) = max_{k ∈ J} max ((y_k − b_k − a_k)/(1 − a_k), (b_k + a_k − y_k)/a_k)`
be the gauge of `F − a_F` at `y − a_F`.  As `1/4 < a_k < 3/4`, `|y_k − b_k − a_k| ≤ N(y)` (`k ∈ J`),
`N ≤ 1` on `F` and `N` is `4`-Lipschitz.  So for `x ∈ F \ {a_F}`, `0 < N(x) ≤ 1`,
`ψ_F(x) = a_F + (x − a_F)/N(x)` lies on `∂F` (a coordinate attaining the maximum goes to `b_i` or
`b_i + 1`), `ψ_F = id` on `∂F` (there `N = 1`), and, with `w = y − a_F`, `|w| ≤ √|J|·N(y)` gives
`|ψ_F(y) − ψ_F(x)| ≤ |y − x|/N(x) + (|w|/N(y))·|N(x) − N(y)|/N(x) ≤ (1 + 4√|J|)/N(x)·|y − x|`. -/
theorem Submission.dimred_mbl_dtsr_face_radial : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (ψF : Euclid P → Euclid P), (∀ y : Euclid P, ∀ i, ψF y i = if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / J.sup' hJ (fun k => max ((y k - b k - a k) / (1 - a k)) ((b k + a k - y k) / a k)) else y i) → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → (∃ i ∈ J, x i ≠ b i + a i) → (∀ k ∈ J, |x k - b k - a k| ≤ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))) ∧ 0 < J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ∧ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ≤ 1 ∧ (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧ (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧ ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧ ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) → (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) * dist y x := by
  intro P a ha b J hJ ψF hψ x hx hne
  -- the gauge `N(u)` of `F − a_F` at `u − a_F`
  let N : Euclid P → ℝ := fun u =>
    J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
  have hψN : ∀ y : Euclid P, ∀ i, ψF y i =
      if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / N y else y i := hψ
  -- `1/4 < a_k < 3/4`
  have ha' : ∀ k, 1 / 4 < a k ∧ a k < 3 / 4 := fun k => by
    obtain ⟨h1, h2⟩ := abs_lt.mp (ha k)
    constructor <;> linarith
  -- each term of the gauge is at most `N(u)` and dominates `|u_k − b_k − a_k|`
  have hterm : ∀ u : Euclid P, ∀ k ∈ J,
      max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k) ≤ N u := fun u k hk =>
    Finset.le_sup' (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) hk
  have habs : ∀ u : Euclid P, ∀ k ∈ J, |u k - b k - a k| ≤ N u := by
    intro u k hk
    refine le_trans ?_ (hterm u k hk)
    obtain ⟨h1, h2⟩ := ha' k
    rcases le_or_gt 0 (u k - b k - a k) with ht | ht
    · rw [abs_of_nonneg ht]
      refine le_max_of_le_left ?_
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · rw [abs_of_neg ht]
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ (by linarith)]
      nlinarith
  -- `N ≤ 1` on `F`, and `N > 0` on `F` off the centre `a_F`
  have hle : ∀ u : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧
      (i ∉ J → u i = b i)) → N u ≤ 1 := by
    intro u hu
    refine Finset.sup'_le hJ _ fun k hk => ?_
    obtain ⟨h1, h2⟩ := ha' k
    obtain ⟨hu1, hu2⟩ := (hu k).1 hk
    refine max_le ?_ ?_
    · rw [div_le_one (by linarith)]; linarith
    · rw [div_le_one (by linarith)]; linarith
  have hpos : ∀ u : Euclid P, (∃ i ∈ J, u i ≠ b i + a i) → 0 < N u := by
    rintro u ⟨i, hi, hui⟩
    have h0 : u i - b i - a i ≠ 0 := fun h => hui (by linarith)
    exact (abs_pos.mpr h0).trans_le (habs u i hi)
  -- `N` is `4`-Lipschitz, as `1/(1 − a_k) < 4` and `1/a_k < 4`
  have hlip : ∀ u v : Euclid P, N u ≤ N v + 4 * dist u v := by
    intro u v
    refine Finset.sup'_le hJ _ fun k hk => ?_
    obtain ⟨h1, h2⟩ := ha' k
    have hd : |u k - v k| ≤ dist u v := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le u v k
    have hd0 : 0 ≤ dist u v := dist_nonneg
    refine max_le ?_ ?_
    · have h : (u k - b k - a k) / (1 - a k) - (v k - b k - a k) / (1 - a k) ≤ 4 * dist u v := by
        rw [← sub_div, div_le_iff₀ (by linarith)]
        nlinarith [le_abs_self (u k - v k)]
      linarith [(le_max_left _ _).trans (hterm v k hk)]
    · have h : (b k + a k - u k) / a k - (b k + a k - v k) / a k ≤ 4 * dist u v := by
        rw [← sub_div, div_le_iff₀ (by linarith)]
        nlinarith [neg_abs_le (u k - v k)]
      linarith [(le_max_right _ _).trans (hterm v k hk)]
  have hNx := hpos x hne
  show (∀ k ∈ J, |x k - b k - a k| ≤ N x) ∧ 0 < N x ∧ N x ≤ 1 ∧
    (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧
    (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧
    ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧
    ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) →
      (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / N x * dist y x
  refine ⟨habs x, hNx, hle x hx, fun i => ⟨fun hi => ?_, fun hi => ?_⟩, ?_, ?_, ?_⟩
  · -- `ψ_F(x) ∈ F`: `−a_i ≤ (x_i − b_i − a_i)/N(x) ≤ 1 − a_i`
    obtain ⟨h1, h2⟩ := ha' i
    have hp := (le_max_left _ _).trans (hterm x i hi)
    have hq := (le_max_right _ _).trans (hterm x i hi)
    rw [div_le_iff₀ (by linarith)] at hp hq
    have hlo : -a i ≤ (x i - b i - a i) / N x := by rw [le_div_iff₀ hNx]; linarith
    have hhi : (x i - b i - a i) / N x ≤ 1 - a i := by rw [div_le_iff₀ hNx]; linarith
    rw [hψN x i, ite_eq_left hi]
    constructor <;> linarith
  · rw [hψN x i, ite_eq_right hi]
    exact (hx i).2 hi
  · -- a coordinate attaining the maximum is sent to `b_i` or `b_i + 1`
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hJ
      (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
    change N x = max ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) at heq
    obtain ⟨h1, h2⟩ := ha' i
    refine ⟨i, hi, ?_⟩
    rw [hψN x i, ite_eq_left hi]
    rcases max_choice ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) with hm | hm
    · rw [hm, eq_div_iff (by linarith)] at heq
      have h : (x i - b i - a i) / N x = 1 - a i := by rw [div_eq_iff hNx.ne']; linarith
      right
      rw [h]
      ring
    · rw [hm, eq_div_iff (by linarith)] at heq
      have h : (x i - b i - a i) / N x = -a i := by rw [div_eq_iff hNx.ne']; linarith
      left
      rw [h]
      ring
  · -- on `∂F`, `N(x) = 1` and `ψ_F(x) = x`
    rintro ⟨i, hi, hbi⟩
    obtain ⟨h1, h2⟩ := ha' i
    have hN1 : N x = 1 := by
      refine le_antisymm (hle x hx) ?_
      rcases hbi with h | h
      · have h' : (b i + a i - x i) / a i = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]
          ring
        exact h'.symm.le.trans ((le_max_right _ _).trans (hterm x i hi))
      · have h' : (x i - b i - a i) / (1 - a i) = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]
          ring
        exact h'.symm.le.trans ((le_max_left _ _).trans (hterm x i hi))
    ext k
    rw [hψN x k, hN1]
    split_ifs <;> ring
  · -- the radial estimate
    intro y hy hney
    have hNy := hpos y hney
    -- `w = y − a_F` is supported on `J`, so `|w| ≤ √|J|·N(y)`
    let w : Euclid P := WithLp.toLp 2 fun k => if k ∈ J then y k - b k - a k else 0
    have hwk : ∀ k, w k = if k ∈ J then y k - b k - a k else 0 := fun k => rfl
    have hw : ‖w‖ ≤ Real.sqrt J.card * N y := by
      have hsum : ∑ k, ‖w k‖ ^ 2 ≤ J.card * N y ^ 2 :=
        calc ∑ k, ‖w k‖ ^ 2 = ∑ k ∈ J, ‖w k‖ ^ 2 :=
              (Finset.sum_subset (Finset.subset_univ J) fun k _ hk => by
                rw [hwk k, ite_eq_right hk, norm_zero]; ring).symm
          _ ≤ ∑ _k ∈ J, N y ^ 2 := Finset.sum_le_sum fun k hk => by
              rw [hwk k, ite_eq_left hk, Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (habs y k hk) 2
          _ = J.card * N y ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ k, ‖w k‖ ^ 2) ≤ Real.sqrt (J.card * N y ^ 2) := Real.sqrt_le_sqrt hsum
        _ = Real.sqrt J.card * N y := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hNy.le]
    -- `ψ_F(y) − ψ_F(x) = (y − x)/N(x) + (1/N(y) − 1/N(x))·w`
    have hdecomp : ψF y - ψF x = (1 / N x) • (y - x) + (1 / N y - 1 / N x) • w := by
      ext k
      rw [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply,
        hψN x k, hψN y k, hwk k, smul_eq_mul, smul_eq_mul]
      by_cases hk : k ∈ J
      · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
        ring
      · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, (hx k).2 hk, (hy k).2 hk]
        ring
    have hlipxy : |N x - N y| ≤ 4 * dist y x := by
      rw [abs_le]
      constructor <;> linarith [hlip x y, hlip y x, dist_comm x y]
    have hfrac : |1 / N y - 1 / N x| * N y = |N x - N y| / N x := by
      rw [div_sub_div _ _ hNy.ne' hNx.ne', abs_div, abs_of_pos (mul_pos hNy hNx)]
      field_simp
    rw [dist_eq_norm, hdecomp]
    calc ‖(1 / N x) • (y - x) + (1 / N y - 1 / N x) • w‖
        ≤ ‖(1 / N x) • (y - x)‖ + ‖(1 / N y - 1 / N x) • w‖ := norm_add_le _ _
      _ = 1 / N x * dist y x + |1 / N y - 1 / N x| * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr hNx), dist_eq_norm]
      _ ≤ 1 / N x * dist y x + |1 / N y - 1 / N x| * (Real.sqrt J.card * N y) := by gcongr
      _ = 1 / N x * dist y x + |N x - N y| / N x * Real.sqrt J.card := by rw [← hfrac]; ring
      _ ≤ 1 / N x * dist y x + 4 * dist y x / N x * Real.sqrt J.card := by gcongr
      _ = (1 + 4 * Real.sqrt J.card) / N x * dist y x := by ring

/-- **Simon Ch. 6, proof of Lemma 5.4: the composite of the face retractions** (chapter-06.txt,
lines 1508–1546).  For `a` with `|aᵢ − 1/2| < 1/4` there are maps `Ψ_k : ℝᴾ → ℝᴾ` with
`Ψ_{m+1} = id` and `Ψ_j(x) = Ψ_{j−1}(ψ_F(x))` for every `j`-face `F = F(b, J)`, `m + 2 ≤ j ≤ P`,
and `x ∈ F`, where `ψ_F` is the radial retraction of `F` from its centre `a_F` onto `∂F` (Simon's
`ψ^{(j)} := ⋃ ψ_F` and `ψ^{(m+2)} ∘ ⋯ ∘ ψ^{(j)}`; at `x = a_F` the gauge vanishes and, with
`t / 0 = 0`, `ψ_F(a_F) = a_F`).  Two distinct `j`-faces through `u` meet where `u` has a coordinate
`uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, in each of them, and there both retractions are the identity
(`dimred_mbl_dtsr_face_radial`); so the step map `φ_j` retracting along any `j`-face through `u`
is well defined, and `Ψ_k := Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`. -/
theorem Submission.dimred_mbl_dtsr_face_retraction_family : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) ∧ ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y := by
  classical
  intro P m a ha
  -- `u ∈ F(b, J)`
  let InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop := fun b J u =>
    ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)
  -- the radial retraction `R_{b,J}` of `F(b, J)` from its centre onto `∂F(b, J)` (`id` if `J = ∅`)
  let R : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Euclid P := fun b J u =>
    if hJ : J.Nonempty then
      WithLp.toLp 2 fun i => if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i
    else u
  have hR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (u : Euclid P) (i : Fin P),
      R b J u i = if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i := by
    intro b J hJ u i
    simp only [R, dite_eq_left hJ, PiLp.toLp_apply]
  -- Step 1: if two distinct faces of the same dimension contain `u`, then `u` has a coordinate
  -- `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, on the boundary of the first one
  have hbd : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → (b, J) ≠ (b', J') → ∃ i ∈ J, u i = b i ∨ u i = b i + 1 := by
    intro b b' J J' u hcard hu hu' hne
    by_cases hJJ : J = J'
    · -- same free coordinates: `bᵢ ≠ b'ᵢ` for some `i ∈ J` and `uᵢ ∈ [bᵢ, bᵢ + 1] ∩ [b'ᵢ, b'ᵢ + 1]`
      subst hJJ
      obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h : b = b' => hne (by rw [h])
      by_cases hiJ : i ∈ J
      · refine ⟨i, hiJ, ?_⟩
        obtain ⟨h1, h2⟩ := (hu i).1 hiJ
        obtain ⟨h3, h4⟩ := (hu' i).1 hiJ
        rcases lt_or_gt_of_ne hi with hlt | hlt
        · have : (b i : ℝ) + 1 ≤ b' i := by exact_mod_cast hlt
          right; linarith
        · have : (b' i : ℝ) + 1 ≤ b i := by exact_mod_cast hlt
          left; linarith
      · exact absurd (Int.cast_injective (((hu i).2 hiJ).symm.trans ((hu' i).2 hiJ))) hi
    · -- `J ⊄ J'`: for `i ∈ J \ J'` the coordinate `uᵢ = b'ᵢ ∈ [bᵢ, bᵢ + 1]` is an integer
      obtain ⟨i, hiJ, hiJ'⟩ := Finset.not_subset.mp fun hsub =>
        hJJ (Finset.eq_of_subset_of_card_le hsub hcard.ge)
      refine ⟨i, hiJ, ?_⟩
      obtain ⟨h1, h2⟩ := (hu i).1 hiJ
      rw [(hu' i).2 hiJ'] at h1 h2 ⊢
      have h1' : b i ≤ b' i := Int.cast_le.mp h1
      have h2' : b' i ≤ b i + 1 := by
        rw [← Int.cast_le (R := ℝ), Int.cast_add, Int.cast_one]
        exact h2
      rcases h1'.eq_or_lt with h | h
      · left; rw [← h]
      · right; rw [le_antisymm h2' (Int.add_one_le_of_lt h), Int.cast_add, Int.cast_one]
  -- Step 2: at such points `R_{b,J}` is the identity (`dimred_mbl_dtsr_face_radial`;
  -- `1/4 < aᵢ < 3/4` keeps `u` off the centre), so all faces of the same dimension through `u`
  -- agree
  have hfix : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P), InF b J u →
      (∃ i ∈ J, u i = b i ∨ u i = b i + 1) → R b J u = u := by
    rintro b J u hu ⟨i, hiJ, hbi⟩
    have hJ : J.Nonempty := ⟨i, hiJ⟩
    have hai := abs_lt.mp (ha i)
    have hne : ∃ i ∈ J, u i ≠ b i + a i := ⟨i, hiJ, by
      rcases hbi with h | h <;> rw [h] <;> intro h' <;> linarith [hai.1, hai.2]⟩
    exact (Submission.dimred_mbl_dtsr_face_radial P a ha b J hJ (R b J) (hR b J hJ) u hu
      hne).2.2.2.2.2.1 ⟨i, hiJ, hbi⟩
  have hcons : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → R b J u = R b' J' u := by
    intro b b' J J' u hcard hu hu'
    by_cases h : (b, J) = (b', J')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    · rw [hfix b J u hu (hbd b b' J J' u hcard hu hu' h),
        hfix b' J' u hu' (hbd b' b J' J u hcard.symm hu' hu (Ne.symm h))]
  -- Step 3: the step map `φ_j` applies the retraction of a chosen `j`-face through `u`
  let φ : ℕ → Euclid P → Euclid P := fun j u =>
    if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = j ∧ InF p.1 p.2 u then
      R h.choose.1 h.choose.2 u
    else u
  -- Step 4: `Ψ_k = id` for `k ≤ m + 1` and `Ψ_k = Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`
  let Ψ : ℕ → Euclid P → Euclid P := fun k =>
    Nat.rec (motive := fun _ => Euclid P → Euclid P) id
      (fun k Ψk => if k + 1 ≤ m + 1 then id else Ψk ∘ φ (k + 1)) k
  refine ⟨Ψ, fun x => ?_, ?_⟩
  · show (if m + 1 ≤ m + 1 then id else Ψ m ∘ φ (m + 1)) x = x
    rw [ite_eq_left le_rfl]
    rfl
  -- Step 5: for `x ∈ F(b, J)` the chosen face gives `φ_j(x) = R_{b,J}(x) = y`
  · intro j hj _ b J hJ hcard x hx y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr ((Nat.zero_lt_succ _).trans_le hj)
    have hk : ¬k + 1 ≤ m + 1 := Nat.not_le.mpr hj
    show (if k + 1 ≤ m + 1 then id else Ψ k ∘ φ (k + 1)) x = Ψ (k + 1 - 1) y
    rw [ite_eq_right hk, Nat.add_sub_cancel]
    have hex : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x :=
      ⟨(b, J), hcard, hx⟩
    show Ψ k (if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x then
      R h.choose.1 h.choose.2 x else x) = Ψ k y
    rw [dite_eq_left hex, hcons _ b _ J x (hex.choose_spec.1.trans hcard.symm) hex.choose_spec.2 hx]
    congr 1
    ext i
    rw [hR b J hJ x i, hy i]
/-- **Face-by-face Lipschitz bound for the skeleton retraction** (Simon Ch. 6, Lemma 5.4, proof
of (3), chapter-06.txt lines 1563–1640: induction over the faces, radial retractions and the chain
rule).  `F = F(b, J)` is the face `{b_i ≤ x_i ≤ b_i + 1 (i ∈ J), x_i = b_i (i ∉ J)}`, `N = N_{b,J}`
its gauge about the centre `a_F`, and `ψ_F(u) = a_F + (u − a_F)/N(u)` on `J`, `u` off `J`; the
recursion says `Ψ_j = Ψ_{j−1} ∘ ψ_F` on `F`.  With `K = 1 + 4√P` and `c = K^P`, induction on
`j ∈ [m + 2, P]` shows: if `x ∈ F` and at most `m + 1` indices `i ∈ J` have
`|x_i − b_i − a_i| < ρ` (the coordinate form of "`x` is `ρ`-far from the planes through `a_F`
fixing `m + 2` coordinates of `J`"), then `Ψ_j(x) ∈ F`, `P − m − 1` coordinates of `Ψ_j(x)` are
integers, and `|Ψ_j(y) − Ψ_j(x)| ≤ (K^{j−m−1}/ρ)|y − x|` for `y ∈ F` near `x`.  The counting
condition gives `N(x) ≥ ρ`, and it holds at `y` with radius `ρ/2` if `|y − x| < ρ/2`.  For
`j = m + 2`, `Ψ_j = ψ_F` on `F` and `Submission.dimred_mbl_dtsr_face_radial` gives the constant
`(1 + 4√j)/N(x)`.  For `j > m + 2`, `y₀ = ψ_F(x)` lies on the `(j − 1)`-faces
`F(b[i ↦ β], J ∖ {i})` with `y₀_i = β ∈ {b_i, b_i + 1}`; as `y₀ − a_F = (x − a_F)/N(x)` on `J`,
the counting condition holds at `y₀` with radius `ρ/N(x)` (the similarity after (7)), and
`ψ_F(y)` lies on one of these faces for `y` near `x`.  The chain rule cancels `N(x)`, so the bound `|y − a| ≥ 3/4` behind (6)
(an erratum for `1/4`) is not needed. -/
theorem Submission.dimred_mbl_dtsr_face_count_induction : ∀ (P m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) → (∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y) → ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 → (∀ i, (i ∈ J → (b i : ℝ) ≤ Ψ j x i ∧ Ψ j x i ≤ b i + 1) ∧ (i ∉ J → Ψ j x i = b i)) ∧ (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧ ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ J → (b i : ℝ) ≤ w i ∧ w i ≤ b i + 1) ∧ (i ∉ J → w i = b i)}] x, dist (Ψ j y) (Ψ j x) ≤ c / ρ * dist y x := by
  intro P m
  -- Step 0: `K = 1 + 4√P ≥ 1` and `c = K ^ P`
  have hK1 : (1 : ℝ) ≤ 1 + 4 * Real.sqrt P := by
    have := Real.sqrt_nonneg (P : ℝ); linarith
  refine ⟨(1 + 4 * Real.sqrt P) ^ P, by positivity, ?_⟩
  intro a ha Ψ hΨ0 hrec
  -- the face `F(b, J)`, the gauge `N_{b,J}` and the radial map `ψ_{b,J}`
  obtain ⟨InF, hInF⟩ : ∃ InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop, ∀ b J u,
      InF b J u ↔ ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i) :=
    ⟨fun b J u => ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i),
      fun _ _ _ => Iff.rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin P → ℤ) → (J : Finset (Fin P)) → J.Nonempty → Euclid P → ℝ,
      ∀ b J hJ u, N b J hJ u =
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) :=
    ⟨fun b J hJ u =>
      J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
      fun _ _ _ _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (Fin P → ℤ) → (J : Finset (Fin P)) → J.Nonempty → Euclid P → Euclid P,
      ∀ b J hJ u i, R b J hJ u i =
        if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i :=
    ⟨fun b J hJ u => WithLp.toLp 2 fun i =>
      if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i,
      fun _ _ _ _ _ => rfl⟩
  -- Step 1(c), the recursion: `Ψ_j = Ψ_{j−1} ∘ ψ_{b,J}` on `F(b, J)`
  have hrec' : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P))
      (hJ : J.Nonempty), J.card = j → ∀ u, InF b J u → Ψ j u = Ψ (j - 1) (R b J hJ u) :=
    fun j hj hjP b J hJ hc u hu =>
      hrec j hj hjP b J hJ hc u ((hInF b J u).1 hu) (R b J hJ u) (fun i => by rw [hR, hN])
  -- Step 1(d), face_radial for `ψ_{b,J}`
  have FR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (x : Euclid P), InF b J x →
      (∃ i ∈ J, x i ≠ b i + a i) →
      (∀ k ∈ J, |x k - b k - a k| ≤ N b J hJ x) ∧ 0 < N b J hJ x ∧ InF b J (R b J hJ x) ∧
      (∃ i ∈ J, R b J hJ x i = b i ∨ R b J hJ x i = b i + 1) ∧
      ∀ y, InF b J y → (∃ i ∈ J, y i ≠ b i + a i) →
        dist (R b J hJ y) (R b J hJ x) ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := by
    intro b J hJ x hx hne
    obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := Submission.dimred_mbl_dtsr_face_radial P a ha b J hJ
      (R b J hJ) (fun y i => by rw [hR, hN]) x ((hInF b J x).1 hx) hne
    rw [← hN b J hJ x] at h1 h2 h7
    exact ⟨h1, h2, (hInF b J _).2 h4, h5, fun y hy hney => h7 y ((hInF b J y).1 hy) hney⟩
  -- Step 1(a), the counting condition leaves a coordinate with `|u_i − b_i − a_i| ≥ ρ`
  have hfar : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), m + 2 ≤ J.card → ∀ (u : Euclid P) (ρ : ℝ),
      (J.filter (fun i => |u i - b i - a i| < ρ)).card ≤ m + 1 →
      ∃ i ∈ J, ρ ≤ |u i - b i - a i| := by
    intro b J hJc u ρ hcount
    by_contra h
    have h' : ∀ i ∈ J, |u i - b i - a i| < ρ := fun i hi => not_le.mp fun hle => h ⟨i, hi, hle⟩
    rw [Finset.filter_true_of_mem h'] at hcount
    omega
  have hcentre : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P) (ρ : ℝ), 0 < ρ →
      (∃ i ∈ J, ρ ≤ |u i - b i - a i|) → ∃ i ∈ J, u i ≠ b i + a i := by
    rintro b J u ρ hρ ⟨i, hi, hf⟩
    refine ⟨i, hi, fun he => ?_⟩
    have h0 : u i - b i - a i = 0 := by rw [he]; ring
    rw [h0, abs_zero] at hf
    linarith
  -- Step 1(b), the counting condition passes to `y` with `|y − x| < ρ/2`, with radius `ρ/2`
  have hnear : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (x y : Euclid P) (ρ : ℝ),
      dist y x < ρ / 2 → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      (J.filter (fun i => |y i - b i - a i| < ρ / 2)).card ≤ m + 1 := by
    intro b J x y ρ hyx hcount
    refine le_trans (Finset.card_le_card fun i hi => ?_) hcount
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have hd : |x i - y i| ≤ dist y x := by
      rw [dist_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le x y i
    calc |x i - b i - a i| = |(x i - y i) + (y i - b i - a i)| := by ring_nf
      _ ≤ |x i - y i| + |y i - b i - a i| := abs_add_le _ _
      _ < ρ := by linarith [hi.2]
  -- Claim(j), by induction on `j ≥ m + 2`
  have hclaim : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j →
      ∀ x : Euclid P, InF b J x → ∀ ρ : ℝ, 0 < ρ →
      (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      InF b J (Ψ j x) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧
      ∃ δ > 0, ∀ y : Euclid P, InF b J y → dist y x < δ →
        dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- Step 2: `j = m + 2`, where `Ψ_j = ψ_F` on `F`
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hΨ : ∀ u, InF b J u → Ψ (m + 2) u = R b J hJ u := fun u hu => by
        rw [hrec' (m + 2) le_rfl hP b J hJ hcard u hu, show m + 2 - 1 = m + 1 by omega, hΨ0]
      obtain ⟨i, hi, hfx⟩ := hfar b J (by omega) x ρ hcount
      obtain ⟨F1, -, F3, F4, F6⟩ := FR b J hJ x hx (hcentre b J x ρ hρ ⟨i, hi, hfx⟩)
      have hNρ : ρ ≤ N b J hJ x := hfx.trans (F1 i hi)
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨ x hx]; exact F3
      · -- (B): the coordinates off `J` and one boundary coordinate in `J`
        obtain ⟨i₀, hi₀, hbd⟩ := F4
        have F3' := (hInF b J _).1 F3
        refine ⟨insert i₀ (Finset.univ \ J), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hi₀]),
            Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ,
            Fintype.card_fin, hcard]
          omega
        · intro k hk
          rw [hΨ x hx]
          rcases Finset.mem_insert.mp hk with rfl | hk'
          · rcases hbd with h | h
            · exact ⟨b k, h⟩
            · exact ⟨b k + 1, by rw [h, Int.cast_add, Int.cast_one]⟩
          · exact ⟨b k, (F3' k).2 (Finset.mem_sdiff.mp hk').2⟩
      · -- (C) with `δ = ρ/2` and constant `(1 + 4√(m + 2))/N(x) ≤ K/ρ`
        refine ⟨ρ / 2, by positivity, fun y hy hyx => ?_⟩
        have hney := hcentre b J y (ρ / 2) (by positivity)
          (hfar b J (by omega) y (ρ / 2) (hnear b J x y ρ hyx hcount))
        rw [hΨ y hy, hΨ x hx]
        have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
          Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
        calc dist (R b J hJ y) (R b J hJ x)
            ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := F6 y hy hney
          _ ≤ (1 + 4 * Real.sqrt P) ^ (m + 2 - m - 1) / ρ * dist y x := by
            rw [show m + 2 - m - 1 = 1 by omega, pow_one]
            apply mul_le_mul_of_nonneg_right _ dist_nonneg
            exact div_le_div₀ (by positivity) (by linarith) hρ hNρ
    | succ j hj ih =>
      -- Step 3: `m + 3 ≤ j + 1 ≤ P`, assuming Claim(j)
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hrecj : ∀ u, InF b J u → Ψ (j + 1) u = Ψ j (R b J hJ u) := fun u hu => by
        rw [hrec' (j + 1) (by omega) hP b J hJ hcard u hu, show j + 1 - 1 = j by omega]
      obtain ⟨-, Fpos, F3, F4, F6⟩ :=
        FR b J hJ x hx (hcentre b J x ρ hρ (hfar b J (by omega) x ρ hcount))
      -- `y₀ = ψ_F(x)` satisfies `y₀ − a_F = (x − a_F)/N(x)` on `J`
      have hy₀k : ∀ k ∈ J, R b J hJ x k - b k - a k = (x k - b k - a k) / N b J hJ x := by
        intro k hk
        rw [hR, ite_eq_left hk]; ring
      have hΨx : Ψ (j + 1) x = Ψ j (R b J hJ x) := hrecj x hx
      obtain ⟨Nx, hNx⟩ : ∃ t, N b J hJ x = t := ⟨_, rfl⟩
      obtain ⟨y₀, hy₀⟩ : ∃ y, R b J hJ x = y := ⟨_, rfl⟩
      rw [hNx] at Fpos hy₀k F6
      rw [hy₀] at F3 F4 hy₀k hΨx F6
      have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
        Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
      -- (i) the faces `G_{i,β} = F(b[i ↦ β], J ∖ {i})` lie in `F` and contain the points of `F`
      -- with `i`-th coordinate `β`
      have hGsub : ∀ i' ∈ J, ∀ β : ℤ, b i' ≤ β → β ≤ b i' + 1 → ∀ u,
          InF (Function.update b i' β) (J.erase i') u → InF b J u := by
        intro i' hi' β hβ1 hβ2 u hu
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          have hu2 := (hu k).2 (Finset.notMem_erase k J)
          rw [Function.update_self] at hu2
          refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hi' h⟩
          · rw [hu2]; exact_mod_cast hβ1
          · have h2 : (β : ℝ) ≤ ((b k + 1 : ℤ) : ℝ) := Int.cast_le.mpr hβ2
            rw [hu2]; push_cast at h2; exact h2
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          obtain ⟨h1, h2⟩ := hu k
          rw [hupd, hmem] at h1 h2
          exact ⟨h1, h2⟩
      have hGmem : ∀ i' ∈ J, ∀ u, InF b J u → ∀ β : ℤ, u i' = β →
          InF (Function.update b i' β) (J.erase i') u := by
        intro i' hi' u hu β hβ
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          refine ⟨fun h => absurd h (Finset.notMem_erase k J), fun _ => ?_⟩
          rw [Function.update_self]; exact hβ
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          rw [hupd, hmem]
          exact hu k
      -- (ii) scaling: the counting condition holds at `y₀` on `G_{i,β}` with radius `ρ/N(x)`
      have hρN : 0 < ρ / Nx := div_pos hρ Fpos
      have hGcount : ∀ i' ∈ J, ∀ β : ℤ,
          ((J.erase i').filter (fun k => |y₀ k - Function.update b i' β k - a k| < ρ / Nx)).card
            ≤ m + 1 := by
        intro i' hi' β
        refine le_trans (Finset.card_le_card fun k hk => ?_) hcount
        rw [Finset.mem_filter] at hk ⊢
        obtain ⟨hki, hkJ⟩ := Finset.mem_erase.mp hk.1
        refine ⟨hkJ, ?_⟩
        have h' := hk.2
        rw [Function.update_of_ne hki, hy₀k k hkJ, abs_div, abs_of_pos Fpos] at h'
        exact (div_lt_div_iff_of_pos_right Fpos).mp h'
      have hGcard : ∀ i' ∈ J, (J.erase i').card = j := by
        intro i' hi'
        rw [Finset.card_erase_of_mem hi']; omega
      -- (iii) Claim(j) at `y₀` on every face `G_{i,β}` through `y₀`
      have hIH : ∀ i' ∈ J, ∀ β : ℤ, y₀ i' = β →
          InF (Function.update b i' β) (J.erase i') (Ψ j y₀) ∧
          (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j y₀ i = z) ∧
          ∃ δ > 0, ∀ y' : Euclid P, InF (Function.update b i' β) (J.erase i') y' →
            dist y' y₀ < δ →
            dist (Ψ j y') (Ψ j y₀) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀ :=
        fun i' hi' β hβ => ih (by omega) (Function.update b i' β) (J.erase i') (hGcard i' hi') y₀
          (hGmem i' hi' y₀ F3 β hβ) (ρ / Nx) hρN (hGcount i' hi' β)
      -- (A) and (B) from a face through `y₀`
      obtain ⟨i₁, hi₁, hbd₁⟩ := F4
      obtain ⟨β₁, hβ₁a, hβ₁b, hβ₁e⟩ : ∃ β : ℤ, b i₁ ≤ β ∧ β ≤ b i₁ + 1 ∧ y₀ i₁ = β := by
        rcases hbd₁ with h | h
        · exact ⟨b i₁, le_refl _, by omega, h⟩
        · exact ⟨b i₁ + 1, by omega, le_refl _, by rw [h, Int.cast_add, Int.cast_one]⟩
      obtain ⟨hA₁, hB₁, -⟩ := hIH i₁ hi₁ β₁ hβ₁e
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨx]; exact hGsub i₁ hi₁ β₁ hβ₁a hβ₁b _ hA₁
      · rw [hΨx]; exact hB₁
      -- (iv) near `y₀`: the bounds of (iii), and `y'_i ≠ β` whenever `y₀_i ≠ β`
      have hev : ∀ᶠ y' in 𝓝 y₀, ∀ i' ∈ J, ∀ e : Bool,
          (y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            InF (Function.update b i' (if e then b i' + 1 else b i')) (J.erase i') y' →
            dist (Ψ j y') (Ψ j y₀) ≤
              (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀) ∧
          (y₀ i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            y' i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ)) := by
        rw [Filter.eventually_all_finset]
        intro i' hi'
        rw [Filter.eventually_all]
        intro e
        by_cases hβ : y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ)
        · obtain ⟨-, -, δ', hδ', hbd⟩ := hIH i' hi' _ hβ
          filter_upwards [Metric.ball_mem_nhds y₀ hδ'] with y' hy'
          exact ⟨fun _ hG => hbd y' hG (Metric.mem_ball.mp hy'), fun h => absurd hβ h⟩
        · have hpos : 0 < |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| :=
            abs_pos.mpr (sub_ne_zero.mpr hβ)
          filter_upwards [Metric.ball_mem_nhds y₀ hpos] with y' hy'
          refine ⟨fun h => absurd h hβ, fun _ heq => ?_⟩
          have h1 : |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| ≤ dist y' y₀ := by
            rw [← heq, abs_sub_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le _ _ _
          exact absurd (Metric.mem_ball.mp hy') (not_lt.mpr h1)
      obtain ⟨η, hη, hηQ⟩ := Metric.eventually_nhds_iff.mp hev
      -- (v) `δ = min(ρ/2, η N(x)/(1 + 4√(j + 1)))`, so that `|ψ_F(y) − y₀| < η`
      refine ⟨min (ρ / 2) (η * Nx / (1 + 4 * Real.sqrt J.card)), by positivity, ?_⟩
      intro y hy hyx
      have hyx1 : dist y x < ρ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
      have hyx2 : dist y x < η * Nx / (1 + 4 * Real.sqrt J.card) :=
        lt_of_lt_of_le hyx (min_le_right _ _)
      have hney := hcentre b J y (ρ / 2) (by positivity)
        (hfar b J (by omega) y (ρ / 2) (hnear b J x y ρ hyx1 hcount))
      obtain ⟨-, -, F3y, F4y, -⟩ := FR b J hJ y hy hney
      have hd := F6 y hy hney
      have hdη : dist (R b J hJ y) y₀ < η := by
        calc dist (R b J hJ y) y₀ ≤ (1 + 4 * Real.sqrt J.card) / Nx * dist y x := hd
          _ < (1 + 4 * Real.sqrt J.card) / Nx * (η * Nx / (1 + 4 * Real.sqrt J.card)) := by
            gcongr
          _ = η := by field_simp
      -- (vi) `ψ_F(y)` lies on a face `G_{i,β}` through `y₀`; the chain rule
      obtain ⟨i₂, hi₂, hbd₂⟩ := F4y
      obtain ⟨e, he⟩ : ∃ e : Bool,
          R b J hJ y i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        rcases hbd₂ with h | h
        · exact ⟨false, by simp [h]⟩
        · exact ⟨true, by simp [h]⟩
      obtain ⟨hQ1, hQ2⟩ := hηQ hdη i₂ hi₂ e
      have hy₀β : y₀ i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        by_contra hc
        exact hQ2 hc he
      have hbound := hQ1 hy₀β (hGmem i₂ hi₂ _ F3y _ he)
      rw [hrecj y hy, hΨx]
      calc dist (Ψ j (R b J hJ y)) (Ψ j y₀)
          ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist (R b J hJ y) y₀ := hbound
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) *
              ((1 + 4 * Real.sqrt J.card) / Nx * dist y x) := by gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x := by
            field_simp
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt P) / ρ * dist y x := by
            gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j + 1 - m - 1) / ρ * dist y x := by
            rw [show j + 1 - m - 1 = (j - m - 1) + 1 by omega, pow_succ]
  -- Step 0: Claim(j) gives the theorem, since `K ^ (j − m − 1) ≤ K ^ P = c`
  intro j hj hjP b J hcard x hx ρ hρ hcount
  obtain ⟨hA, hB, δ, hδ, hC⟩ := hclaim j hj hjP b J hcard x ((hInF b J x).2 hx) ρ hρ hcount
  refine ⟨(hInF b J _).1 hA, hB, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy hyF
  calc dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x :=
        hC y ((hInF b J y).2 hyF) (Metric.mem_ball.mp hy)
    _ ≤ (1 + 4 * Real.sqrt P) ^ P / ρ * dist y x := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      apply div_le_div_of_nonneg_right _ hρ.le
      exact pow_le_pow_right₀ hK1 (by omega)
/-- **Simon Ch. 6, proof of 5.1** (tube cover of the shifted dual skeleton; the inclusion `⊆` in
the identity before display (6)).  Let `L*(a)` be the set of `w ∈ ℝᴾ` with `wᵢ - aᵢ ∈ ℤ` for at
least `m + 2` indices `i`.  If `dist(x, L*(a)) < r`, then for some injective
`e : Fin (m + 2) → Fin P` and `z ∈ ℤ^{m+2}`, `Σₖ (x_{e k} - a_{e k} - z_k)² < r²`.  Take
`w ∈ L*(a)` (nonempty, as `a ∈ L*(a)`) with `dist(x, w) < r`, let `e` enumerate `m + 2` of its
integral indices and put `z_k = w_{e k} - a_{e k}`; the sum is then
`Σₖ (x_{e k} - w_{e k})² ≤ dist(x, w)² < r²`. -/
theorem Submission.dimred_mbl_dt_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- `a ∈ L*(a)`, so `infDist x L*(a) < r` gives a point `w ∈ L*(a)` with `dist x w < r`
  have hne : L.Nonempty :=
    ⟨a, Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- `e` enumerates `m + 2` of the indices `i ∈ s`, and `z k = w (e k) - a (e k)`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- the coordinate projection along `e` does not increase length
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ fun i => (x i - w i) ^ 2
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith
/-- **Simon Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad centres are
few).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  For `g ∈ ℝᵈ` let
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` be the open Euclidean `r`-neighbourhood of
`g + ℤᵈ`.  Call `g` in the open cube `(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some
`r ∈ (0, 1/4]`.  Then the bad set has Lebesgue outer measure at most `10ᵈ/β`.
By Vitali's covering lemma (`τ = 2`) there are bad centres `b` whose sup-metric balls
`B(b, r_b)` are pairwise disjoint and such that the balls `B(b, 3r_b)` cover the bad set.  The
sets `O_{r_b}(b)` are then pairwise disjoint too, so `Σ_b β r_bᵈ ≤ 1`, and the bad set has
measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β ≤ 10ᵈ/β`. -/
theorem Submission.dimred_mbl_dt_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: every `O_r(g)` is open, a union over `z ∈ ℤᵈ` of open sets
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` there are no bad centres
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- step 3 (printed (3)): a radius `r_g ∈ (0, 1/4]` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2` and `R = 1/4`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable, the balls being open, nonempty and pairwise disjoint
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6 (printed (4), with `3` for `5`): the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    -- so `y − z` lies in both of the disjoint balls `B(b, r_b)` and `B(b', r_{b'})`
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- step 8 (summation): `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- step 9: the volume bound `Σ_b (6 r_b)ᵈ = (6ᵈ/β) S ≤ 6ᵈ/β ≤ 10ᵈ/β`
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num
/-- **Simon Ch. 6, proof of 5.1** (choice of a good centre: display (5) and the choice of
`a ∈ ⋂ⱼ pⱼ⁻¹(Gⱼ) ∩ B_{1/4}(q)`, with the open cube `Q = (1/4, 3/4)ᴾ` in place of the ball).  If
the sets `E_e ⊆ ℝᵈ` (`e : Fin d → Fin P`) have total outer measure `< (1/2)ᴾ`, then some `a ∈ Q`
has `(a_{e k})ₖ ∉ E_e` for every injective `e`.  For injective `e`, splitting the coordinates into
`range e` and its complement (Fubini) bounds the measure of `{a ∈ Q : (a_{e k})ₖ ∈ E_e}` by
`|E_e| · (1/2)^{P - d} ≤ |E_e|`; the union bound over all `e` then leaves part of `Q`, which has
volume `(1/2)ᴾ`, uncovered. -/
theorem Submission.dimred_mbl_dt_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the points of the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the centres in `Q` with a bad `e`-projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this
/-- **Simon Ch. 6, proof of 5.1** (choice of the good centre `a`; displays (6), (7)).  There is
`C`, depending only on `P` and `m`, such that for any finite measures `μ`, `μ'` on `ℝᴾ` some
centre `a` in the open cube `(1/4, 3/4)ᴾ` has `μ({x : dist(x, L*(a)) < r}) ≤ C r^{m+2} μ(ℝᴾ)` for
all `r ∈ (0, 1/4]`, and likewise for `μ'`.  Put `d = m + 2`, `K = Pᵈ` and `β = 2K·10ᵈ·2ᴾ + 1`.
For `e : Fin d → Fin P` let `E_e` be the union of the bad sets (`dimred_mbl_dt_gc_bad_set_volume`)
of the push-forwards of `μ` and `μ'` under `x ↦ (x_{e k})ₖ`.  Their volumes sum to at most
`2K·10ᵈ/β < (1/2)ᴾ`, so `dimred_mbl_dt_gc_cube_selection` gives a centre `a` all of whose
injective projections are good.  The tube cover `dimred_mbl_dt_gc_tube_cover` and finite
subadditivity then give the estimate with `C = Kβ`. -/
theorem Submission.dimred_mbl_dt_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  have c1 := Submission.dimred_mbl_dt_gc_tube_cover
  have c2 := Submission.dimred_mbl_dt_gc_bad_set_volume
  have c3 := Submission.dimred_mbl_dt_gc_cube_selection
  classical
  intro P m hPm
  -- the constants: `K = #(Fin (m + 2) → Fin P)`, `β = 2K·10^{m+2}·2ᴾ + 1` and `C = Kβ`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `x ↦ (x_{e k})ₖ` and the bad sets of the push-forwards
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  let Bad : Measure (Fin (m + 2) → ℝ) → Set (Fin (m + 2) → ℝ) := fun ρ =>
    {g | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ (m + 2)) * ρ univ <
        ρ {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}}
  let E : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
    Bad (μ.map (prj e)) ∪ Bad (μ'.map (prj e))
  have hE : ∀ e, volume (E e) ≤ 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro e
    calc volume (E e) ≤ volume (Bad (μ.map (prj e))) + volume (Bad (μ'.map (prj e))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β) :=
          add_le_add (c2 (m + 2) _ inferInstance β hβpos) (c2 (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- the bad sets have total volume `≤ 2K·10^{m+2}/β < (1/2)ᴾ`
  have hsum : ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) := by
    calc ∑ e, volume (E e) ≤ ∑ _e : Fin (m + 2) → Fin P, 2 * ENNReal.ofReal (10 ^ (m + 2) / β) :=
          Finset.sum_le_sum fun e _ => hE e
      _ = ENNReal.ofReal (2 * K * 10 ^ (m + 2) / β) := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ((1 / 2) ^ P) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), div_lt_iff₀ hβpos, hβ]
          have h2 : ((1 : ℝ) / 2) ^ P * 2 ^ P = 1 := by
            rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) < (1 / 2) ^ P := by positivity
          have h4 : ((1 : ℝ) / 2) ^ P * (2 * K * 10 ^ (m + 2) * 2 ^ P + 1) =
              2 * K * 10 ^ (m + 2) * ((1 / 2) ^ P * 2 ^ P) + (1 / 2) ^ P := by ring
          rw [h4, h2]
          linarith
  -- a centre `a` in the cube none of whose injective projections is bad
  obtain ⟨a, ha, hgood⟩ := c3 P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  -- the tube estimate for one measure `ν` all of whose projected bad sets avoid `a`
  have key : ∀ ν : Measure (Euclid P), IsFiniteMeasure ν →
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hν hνgood
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    -- the tube about `L*(a)` is covered by the cylinders `prj_e⁻¹(O_r(prj_e a))`
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := c1 P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- each cylinder has `ν`-measure at most `β r^{m+2} ν(ℝᴾ)`, as `prj_e a` is good
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hnot := hνgood e he
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hnot ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
        calc ν (T e) ≤ ν (prj e ⁻¹' O e) := measure_mono hsub
          _ ≤ (ν.map (prj e)) (O e) := Measure.le_map_apply (hprj e).aemeasurable _
          _ ≤ ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := hle
          _ = ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
              rw [Measure.map_apply (hprj e) MeasurableSet.univ, preimage_univ]
      · have : T e = ∅ := by
          ext x
          simp only [mem_empty_iff_false, iff_false]
          exact fun hx => he hx.1
        rw [this, measure_empty]
        exact bot_le
    -- finite subadditivity over the `K` maps `e`
    calc ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
          ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ ν (⋃ e, T e) := measure_mono hcover
      _ ≤ ∑ e, ν (T e) := measure_iUnion_fintype_le ν T
      _ ≤ ∑ _e : Fin (m + 2) → Fin P, ENNReal.ofReal (β * r ^ (m + 2)) * ν univ :=
          Finset.sum_le_sum fun e _ => hT e
      _ = (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            show ((Real.toNNReal (K * β) : ℝ≥0∞)) = ENNReal.ofReal (K * β) from rfl,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact ⟨key μ hμ fun e he h => hgood e he (Or.inl h),
    key μ' hμ' fun e he h => hgood e he (Or.inr h)⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Local Lipschitz bounds along a segment give the global bound (step (6a) of the proof of the
skeleton retraction, Simon Ch. 6, Lemma 5.4): if every point `x + t(y − x)`, `t ∈ [0, 1]`, has a
neighbourhood on which `|f(w) − f(x + t(y − x))| ≤ K|w − (x + t(y − x))|`, then
`|f(y) − f(x)| ≤ K|y − x|`.  By continuous induction on `[0, 1]`, every `t ∈ [0, 1]` satisfies
`|f(x + t(y − x)) − f(x)| ≤ K t |y − x|`. -/
theorem dimred_mbl_dtsr_segment_lipschitz : ∀ (P : ℕ) (f : Euclid P → Euclid P) (x y : Euclid P) (K : ℝ), 0 ≤ K → (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ w in 𝓝 (x + t • (y - x)), dist (f w) (f (x + t • (y - x))) ≤ K * dist w (x + t • (y - x))) → dist (f y) (f x) ≤ K * dist y x := by
  intro P f x y K _hK hloc
  -- Step 1: `g t = x + t(y − x)` is continuous and `|g s − g t| = |s − t| |y − x|`.
  let g : ℝ → Euclid P := fun t => x + t • (y - x)
  have hgcont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hgdist : ∀ s t : ℝ, dist (g s) (g t) = |s - t| * dist y x := by
    intro s t
    simp only [g, dist_eq_norm]
    rw [show x + s • (y - x) - (x + t • (y - x)) = (s - t) • (y - x) by rw [sub_smul]; abel,
      norm_smul, Real.norm_eq_abs]
  -- Step 2: `f ∘ g` is continuous at each `t ∈ [0, 1]`: for `s` near `t`, `g s` lies in the
  -- neighbourhood of `g t` given by `hloc`, so `|f(g s) − f(g t)| ≤ K |s − t| |y − x| → 0`.
  have hfg : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun s => f (g s)) t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * (|s - t| * dist y x) := by
      filter_upwards [(hgcont.tendsto t).eventually (hloc t ht)] with s hs
      rw [← hgdist]
      exact hs
    have hlim : Tendsto (fun s : ℝ => K * (|s - t| * dist y x)) (𝓝 t) (𝓝 0) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs.mul
        continuous_const)).tendsto' t 0 (by simp)
    exact tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun s => dist_nonneg) hev hlim)
  -- Step 3: `S = {t | |f(g t) − f(x)| ≤ K t |y − x|}` meets `[0, 1]` in a closed set, the
  -- preimage of `(−∞, 0]` under a function continuous on `[0, 1]`.
  let S : Set ℝ := {t | dist (f (g t)) (f x) ≤ K * t * dist y x}
  have hS : IsClosed (S ∩ Icc 0 1) := by
    have hcont : ContinuousOn (fun t => dist (f (g t)) (f x) - K * t * dist y x) (Icc 0 1) := by
      intro t ht
      have hd : ContinuousAt (fun s => dist (f (g s)) (f x)) t :=
        (hfg t ht).dist continuousAt_const
      have hl : Continuous fun s : ℝ => K * s * dist y x :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hd.continuousWithinAt.sub hl.continuousWithinAt
    convert hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
      using 1
    ext t
    simp only [S, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
    tauto
  -- Step 4: `0 ∈ S`, since `g 0 = x`.
  have h0 : (0 : ℝ) ∈ S := by
    show dist (f (x + (0 : ℝ) • (y - x))) (f x) ≤ K * 0 * dist y x
    simp
  -- Step 5: if `t ∈ S ∩ [0, 1)`, then `s ∈ S` for `s > t` near `t`:
  -- `|f(g s) − f(x)| ≤ K (s − t) |y − x| + K t |y − x| = K s |y − x|`.
  have hstep : ∀ t ∈ S ∩ Ico (0 : ℝ) 1, S ∈ 𝓝[>] t := by
    rintro t ⟨htS, ht⟩
    have htS' : dist (f (g t)) (f x) ≤ K * t * dist y x := htS
    have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * dist (g s) (g t) :=
      (hgcont.tendsto t).eventually (hloc t ⟨ht.1, ht.2.le⟩)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hts
    have hts' : t < s := hts
    show dist (f (g s)) (f x) ≤ K * s * dist y x
    calc dist (f (g s)) (f x) ≤ dist (f (g s)) (f (g t)) + dist (f (g t)) (f x) :=
          dist_triangle _ _ _
      _ ≤ K * dist (g s) (g t) + K * t * dist y x := add_le_add hs htS'
      _ = K * s * dist y x := by rw [hgdist, abs_of_pos (sub_pos.mpr hts')]; ring
  -- Step 6: continuous induction on `[0, 1]` gives `[0, 1] ⊆ S`.
  have hsub : Icc (0 : ℝ) 1 ⊆ S := hS.Icc_subset_of_forall_mem_nhdsWithin h0 hstep
  -- Step 7: `1 ∈ S` and `g 1 = y`.
  have h1 : dist (f (g 1)) (f x) ≤ K * 1 * dist y x := hsub ⟨zero_le_one, le_rfl⟩
  have hg1 : g 1 = y := by simp [g]
  rwa [hg1, mul_one] at h1

/-- **Retraction onto the `n`-skeleton away from the dual skeleton** (Lemma D; Simon Ch. 6,
Lemma 5.4, chapter-06.txt lines 1493–1645, with `n = m + 1`).  Let
`L*(a) = {w : w_i − a_i ∈ ℤ for at least m + 2 indices i}` and `d = dist(·, L*(a))`.  Take
`ψ = Ψ_P` (`dimred_mbl_dtsr_face_retraction_family`) and `c₀` from
`dimred_mbl_dtsr_face_count_induction`.  If `x` lies in a closed unit cube `z + [0, 1]ᴾ`
(the face `F(z, univ)`) and `d(x) > 0`, then `dimred_mbl_dtsr_dual_dist_count` gives the
counting condition with `ρ = d(x)/√(m + 2)`, and the face induction with `j = P` puts `ψ(x)` in the
same cube (so `|ψ(x) − x| ≤ √P`) and in the `n`-skeleton, and gives
`|ψ(y) − ψ(x)| ≤ (√(m + 2) c₀/d(x))|y − x|` for `y` in that cube near `x`.  The finitely many
cubes through `x` cover a neighbourhood of `x` (`dimred_mbl_dtsr_cube_cover`).  Let
`0 < r ≤ 1/4` and `d(x), d(y) ≥ r`.  If `|x − y| < r/2`, then `d > r/2` on `[x, y]` (`d` is
`1`-Lipschitz), and `dimred_mbl_dtsr_segment_lipschitz` gives the constant `2√(m + 2) c₀/r`.
Otherwise `|ψ(x) − ψ(y)| ≤ 2√P + |x − y| ≤ (4√P + 1)|x − y|/r`.  So
`c = 2√(m + 2) c₀ + 4√P + 1` works. -/
theorem dimred_mbl_dt_skeleton_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  intro P m hPm
  -- Step 0: `c₀` from the face induction and `c = 2√(m + 2) c₀ + 4√P + 1`
  obtain ⟨c₀, hc₀, hind⟩ := Submission.dimred_mbl_dtsr_face_count_induction P m
  have hsq : (0 : ℝ) < Real.sqrt (m + 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1, by positivity, ?_⟩
  intro a ha
  -- Step 1: `ψ = Ψ_P` for the composite of the face retractions; the face induction at `j = P`
  obtain ⟨Ψ, hΨ0, hΨrec⟩ := Submission.dimred_mbl_dtsr_face_retraction_family P m a ha
  have key := hind a ha Ψ hΨ0 hΨrec P (by omega) le_rfl
  set L : Set (Euclid P) := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
    ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} with hL
  -- Step 2: the closed unit cube `z + [0, 1]ᴾ` is the face `F(z, univ)`, of diameter `√P`
  have hcard : (Finset.univ : Finset (Fin P)).card = P := by simp
  have hface : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      ∀ i, (i ∈ (Finset.univ : Finset (Fin P)) → (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) ∧
        (i ∉ (Finset.univ : Finset (Fin P)) → u i = z i) :=
    fun z u hu i => ⟨fun _ => hu i, fun h => absurd (Finset.mem_univ i) h⟩
  have hdiam : ∀ (z : Fin P → ℤ) (u v : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      (∀ i, (z i : ℝ) ≤ v i ∧ v i ≤ z i + 1) → dist u v ≤ Real.sqrt P := by
    intro z u v hu hv
    rw [EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, dist (u i) (v i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : dist (u i) (v i) ≤ 1 := by
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
          have h0 : 0 ≤ dist (u i) (v i) := dist_nonneg
          nlinarith
      _ = P := by simp
  -- Step 3: on a cube through `u` with `d(u) > 0`, the face induction with
  -- `ρ = d(u)/√(m + 2)`; the counting condition is `dimred_mbl_dtsr_dual_dist_count`
  have hcube : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      0 < infDist u L →
      (∀ i, (i ∈ (Finset.univ : Finset (Fin P)) → (z i : ℝ) ≤ Ψ P u i ∧ Ψ P u i ≤ z i + 1) ∧
        (i ∉ (Finset.univ : Finset (Fin P)) → Ψ P u i = z i)) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ k : ℤ, Ψ P u i = k) ∧
      ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ (Finset.univ : Finset (Fin P)) →
          (z i : ℝ) ≤ w i ∧ w i ≤ z i + 1) ∧ (i ∉ (Finset.univ : Finset (Fin P)) → w i = z i)}] u,
        dist (Ψ P y) (Ψ P u) ≤ c₀ / (infDist u L / Real.sqrt (m + 2)) * dist y u :=
    fun z u hu hd => key z Finset.univ hcard u (hface z u hu) _ (div_pos hd hsq)
      (Submission.dimred_mbl_dtsr_dual_dist_count P m a u z)
  -- Step 4, part (i): the cube `⌊x⌋ + [0, 1]ᴾ` contains both `x` and `ψ(x)`
  have hfloor : ∀ u : Euclid P, ∀ i, ((⌊u i⌋ : ℤ) : ℝ) ≤ u i ∧ u i ≤ (⌊u i⌋ : ℤ) + 1 :=
    fun u i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have hpartI : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ P x i = z) ∧
        dist (Ψ P x) x ≤ Real.sqrt P := by
    intro x hx
    obtain ⟨hmem, hint, -⟩ := hcube (fun i => ⌊x i⌋) x (hfloor x) hx
    exact ⟨hint, hdiam _ (Ψ P x) x (fun i => (hmem i).1 (Finset.mem_univ i)) (hfloor x)⟩
  -- Step 5: `|ψ(y) − ψ(w)| ≤ (√(m + 2) c₀/d(w))|y − w|` for `y` near `w`, from the finitely
  -- many cubes through `w` (`dimred_mbl_dtsr_cube_cover`)
  have hlocal : ∀ w : Euclid P, 0 < infDist w L → ∀ᶠ y in 𝓝 w,
      dist (Ψ P y) (Ψ P w) ≤ c₀ / (infDist w L / Real.sqrt (m + 2)) * dist y w := by
    intro w hw
    obtain ⟨Z, hZ, hcov⟩ := Submission.dimred_mbl_dtsr_cube_cover P w
    have hall : ∀ z ∈ Z, ∀ᶠ y : Euclid P in 𝓝 w, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
        dist (Ψ P y) (Ψ P w) ≤ c₀ / (infDist w L / Real.sqrt (m + 2)) * dist y w := by
      intro z hz
      have h3 := (hcube z w (hZ z hz) hw).2.2
      rw [eventually_nhdsWithin_iff] at h3
      filter_upwards [h3] with y hy hyz
      exact hy (hface z y hyz)
    rw [← Finset.eventually_all] at hall
    filter_upwards [hall, hcov] with y hy hyz
    obtain ⟨z, hz, hyz⟩ := hyz
    exact hy z hz hyz
  refine ⟨Ψ P, hpartI, ?_⟩
  -- Step 6, part (ii)
  intro r hr hr4 x y hx hy
  have hc₀' : 0 ≤ 2 * Real.sqrt (m + 2) * c₀ := by positivity
  have hsP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  by_cases hxy : dist x y < r / 2
  · -- Step 6a: `|x − y| < r/2`, so `d > r/2` on `[x, y]`; the segment argument with
    -- `K = 2√(m + 2) c₀/r`
    have hK : 0 ≤ 2 * Real.sqrt (m + 2) * c₀ / r := by positivity
    have hseg := dimred_mbl_dtsr_segment_lipschitz P (Ψ P) x y
      (2 * Real.sqrt (m + 2) * c₀ / r) hK ?_
    · rw [dist_comm (Ψ P x), dist_comm x]
      calc dist (Ψ P y) (Ψ P x) ≤ 2 * Real.sqrt (m + 2) * c₀ / r * dist y x := hseg
        _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist y x := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          apply div_le_div_of_nonneg_right _ hr.le
          linarith
    · intro t ht
      have hdist : dist (x + t • (y - x)) x ≤ dist x y := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
          ← dist_eq_norm, dist_comm y x]
        exact mul_le_of_le_one_left dist_nonneg ht.2
      -- `d` is `1`-Lipschitz
      have hdw : r / 2 < infDist (x + t • (y - x)) L := by
        have h1 := infDist_le_infDist_add_dist (x := x) (y := x + t • (y - x)) (s := L)
        rw [dist_comm] at h1
        linarith
      have hwpos : 0 < infDist (x + t • (y - x)) L := by linarith
      filter_upwards [hlocal _ hwpos] with w hw
      refine hw.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [div_div_eq_mul_div, div_le_div_iff₀ hwpos hr]
      have hc0 : 0 ≤ c₀ * Real.sqrt (m + 2) := by positivity
      nlinarith
  · -- Step 6b: `|x − y| ≥ r/2`, so `|ψ(x) − ψ(y)| ≤ 2√P + |x − y| ≤ (4√P + 1)|x − y|/r`
    have hxy : r / 2 ≤ dist x y := not_lt.mp hxy
    have h1 := (hpartI x (by linarith)).2
    have h2 := (hpartI y (by linarith)).2
    have hD : 0 ≤ dist x y := dist_nonneg
    calc dist (Ψ P x) (Ψ P y) ≤ dist (Ψ P x) x + dist x y + dist y (Ψ P y) :=
          dist_triangle4 _ _ _ _
      _ ≤ 2 * Real.sqrt P + dist x y := by rw [dist_comm y]; linarith
      _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith

end Submission

end GMT.Ch07
