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

/-- **Current toolkit** in `ℝᴺ` (Simon 6.2.4–6.2.11), given that a current kills forms supported
off its support (VO) and the representation theorem (REP): (A0) `|X(ψ)| ≤ c M(X)` if `|ψ| ≤ c` on
`spt X`; (MB) `|T(ω)| ≤ C c` whenever `|ω| ≤ c` gives `M(T) ≤ C`; (LOC) `X(η) = X(η')` if `η = η'`
on an open `W ⊇ spt X`; (NCD) differences and (NCB) boundaries of currents with compact support,
finite mass and finite boundary mass are again such currents.  For (A0), (REP) gives `(μ, ξ)` with
`μ(ℝᴺ) = M(X)`, and (VO) gives `μ((spt X)ᶜ) = 0`; the rest uses mass suprema, the support calculus
and `∂∂ = 0`. -/
theorem Submission.dimred_mbl_dt_lpo_current_toolkit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) ∧ (∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η') ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → (X - Y).support ⊆ X.support ∪ Y.support ∧ IsCompact (X - Y).support ∧ (X - Y).mass < ∞ ∧ boundaryMassOn (X - Y) univ < ∞) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.boundary.mass < ∞ → X.boundary.support ⊆ X.support ∧ IsCompact X.boundary.support ∧ boundaryMassOn X.boundary univ < ∞ := by
  intro hVO hREP
  -- (MB) each admissible test form has value at most `C`, so their supremum `M(T)` is at most `C`
  have hMB : ∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ),
      (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) →
          |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C := by
    intro N k T C hT
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((hT ω 1 hω.2).trans_eq (mul_one C)))
  -- `M(A − B) ≤ M(A) + M(B)`: `(A − B)(ω) = A(ω) + B(−ω)`, and `−ω` is admissible with `ω`
  have hmass_sub : ∀ (N k : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) k),
      (A - B).mass ≤ A.mass + B.mass := by
    intro N k A B
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have hω' : -ω ∈ massAdmissibleOn univ k univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hneg : B (-ω) = -B ω := map_neg B.toCurrent ω
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by
          rw [hneg, ← sub_eq_add_neg]
          rfl
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.mass + B.mass := add_le_add (A.le_massOn hω) (B.le_massOn hω')
  refine ⟨?_, hMB, ?_, ?_, ?_⟩
  · -- (A0) represent `X` by `(μ, ξ)`; `μ` is finite, with `μ(univ) = M(X)`, and carried by `spt X`
    intro N k X ψ c hX hψ
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hrep, -⟩ := hREP N k univ X isOpen_univ
      fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact hX⟩
    -- `μ((spt X)ᶜ) = M_{(spt X)ᶜ}(X) = 0`: `X` kills the forms supported off `spt X` (VO)
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine nonpos_iff_eq_zero.mp (sSup_le ?_)
      rintro _ ⟨ω, hω, rfl⟩
      simp [hVO N k univ X ω (Set.disjoint_left.mpr fun x hx hxX => hxX.2 (hω.1 hx))]
    have hspt : ∀ᵐ x ∂μ, x ∈ X.support :=
      ae_iff.mpr (measure_mono_null (fun x hx => not_not.mp fun h => hx ⟨mem_univ x, h⟩) hZ)
    have hb : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
      filter_upwards [hspt] with x hx
      exact (Real.norm_eq_abs _).trans_le ((hξ x _).trans (hψ x hx))
    calc |X ψ| = ‖∫ x, ξ x ((ψ : DifferentialForm (Euclid N) k) x) ∂μ‖ := by
          rw [hrep ψ, Real.norm_eq_abs]
      _ ≤ c * μ.real univ := norm_integral_le_of_norm_le_const hb
      _ = c * X.mass.toReal := by rw [measureReal_def, hμ]
  · -- (LOC) `η − η'` vanishes on `W`, so `spt(η − η') ⊆ Wᶜ` misses `spt X ⊆ W`; apply (VO)
    intro N k X η η' W hW hXW hηη'
    have hsupp : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
        DifferentialForm (Euclid N) k) ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => hx (by simp [hηη' x hxW])) hW.isClosed_compl
    have hlin : X (η - η') = X η - X η' := map_sub X.toCurrent η η'
    rw [← sub_eq_zero, ← hlin]
    exact hVO N k univ X (η - η') (disjoint_compl_left.mono hsupp hXW)
  · -- (NCD) `spt(X − Y) ⊆ spt X ∪ spt Y` is closed, hence compact; masses add up, also for `∂`
    intro N k X Y hXc hXm hXb hYc hYm hYb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.1 X Y
    refine ⟨hspt, (hXc.union hYc).of_isClosed_subset
      ((Submission.cmcsd_support_calculus N k).2.1 _) hspt,
      (hmass_sub N k X Y).trans_lt (ENNReal.add_lt_top.mpr ⟨hXm, hYm⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      -- `∂(X − Y) = ∂X − ∂Y`: both send `ω` to `X(dω) − Y(dω)`
      have hb : (X - Y).boundary = X.boundary - Y.boundary := GeometricCurrentOn.ext fun ω => rfl
      show (X - Y).boundary.mass < ∞
      rw [hb]
      exact (hmass_sub N k _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hXb, hYb⟩)
  · -- (NCB) `spt ∂X ⊆ spt X` is closed, hence compact; `∂∂X = 0` has mass `0` by (MB)
    intro N k X hXc hXb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.2.2 X
    refine ⟨hspt, hXc.of_isClosed_subset ((Submission.cmcsd_support_calculus N k).2.1 _) hspt, ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      show X.boundary.boundary.mass < ∞
      rw [GeometricCurrentOn.boundary_boundary]
      exact (hMB N k 0 0 fun ω c _ => by simp).trans_lt ENNReal.ofReal_lt_top
/-- **A cut-off of the pull-back that is compatible with `d`** (Simon 6.1.13–6.1.14).  Let
`F : ℝᴺ → ℝᴺ'` be `C^∞`, `ω ∈ 𝒟ᵏ(ℝᴺ')` and `K ⊆ ℝᴺ` compact.  Then some test form `η ∈ 𝒟ᵏ(ℝᴺ)`
and open `W ⊇ K` satisfy `η = F^#ω` and `dη = F^#(dω)` on `W`.  The pull-back
`F^#ω(x) = Φ(DF(x))(ω(F x))` is `C^∞` because the precomposition `Φ(L) = (γ ↦ γ ∘ L)` is
analytic.  It satisfies `d(F^#ω) = F^#(dω)` (`extDeriv_pullback`).  Take `η = ζ · F^#ω` for a
smooth `ζ` with `support ζ = thickening 1 K` and `ζ = 1` on `cthickening (1/2) K`.  Then
`η = F^#ω` on the open set `W = thickening (1/2) K ⊇ K`, so `dη = d(F^#ω)` there. -/
theorem Submission.dimred_mbl_dt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  -- `ω` is `C^∞`
  have hωs : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid N') k) := ω.property.1.1
  -- the precomposition `Φ(L) = (γ ↦ γ ∘ L)` on `k`-covectors is analytic, hence `C^∞`
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclid N →L[ℝ] Euclid N') →
        (Euclid N' [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (Euclid N [⋀^Fin k]→L[ℝ] ℝ)) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- `DF` and `ω ∘ F` are `C^∞`, so `F^#ω = Φ(DF)(ω ∘ F)` is `C^∞`
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) :=
    (hΦ.comp hDF).clm_apply (hωs.comp hF)
  -- `d(F^#ω) = F^#(dω)` at every point
  have hpb : ∀ x, exteriorDerivative (fun y =>
      ((ω : DifferentialForm (Euclid N') k) (F y)).compContinuousLinearMap (fderiv ℝ F y)) x =
      (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
        (fderiv ℝ F x) := fun x =>
    extDeriv_pullback (hωs.differentiable (by simp)).differentiableAt hF.contDiffAt (by simp)
  -- a cut-off `ζ` with `support ζ = thickening 1 K` and `ζ = 1` exactly on `cthickening (1/2) K`
  obtain ⟨ζ, hζ, -, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := 1) (E := K)) (isClosed_cthickening (δ := 1 / 2) (E := K))
    (cthickening_subset_thickening' one_pos (by norm_num) K)
  -- `spt ζ ⊆ cthickening 1 K`, which is compact
  have hζc : HasCompactSupport ζ := by
    refine (hK.cthickening (r := 1)).of_isClosed_subset (isClosed_tsupport ζ) ?_
    show closure (support ζ) ⊆ _
    rw [hζsupp]
    exact closure_thickening_subset_cthickening 1 K
  -- `ζ = 1` on the open set `W = thickening (1/2) K ⊇ K`
  have hW : ∀ x ∈ thickening (1 / 2) K, ζ x = 1 := fun x hx =>
    (hζone x).mp (thickening_subset_cthickening _ _ hx)
  -- `η = ζ · F^#ω` is a test form, equal to `F^#ω` on `W`
  refine ⟨⟨fun x => ζ x • ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
      (fderiv ℝ F x), ⟨hζ.smul hβ, hζc.smul_right⟩, subset_univ _⟩, thickening (1 / 2) K,
    isOpen_thickening, self_subset_thickening (by norm_num) K, fun x hx => ?_, fun x hx => ?_⟩
  · show ζ x • _ = _
    rw [hW x hx, one_smul]
  · -- `η = F^#ω` near `x ∈ W`, so `dη(x) = d(F^#ω)(x) = F^#(dω)(x)`
    rw [← hpb x]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
    show ζ y • _ = _
    rw [hW y hy, one_smul]
/-- **Smooth `Λ`-Lipschitz mollifications of a `Λ`-Lipschitz map.**  For `σ = 1/(j+1)` let `φ` be
a `C^∞` bump with support `B(0, σ)` and `ρⱼ = (∫ φ)⁻¹ φ` its normalization (`ρⱼ ≥ 0`,
`∫ ρⱼ = 1`).  Then `Fⱼ = ρⱼ ⋆ F`, `Fⱼ(x) = ∫ ρⱼ(t) F(x − t) dt`, is `C^∞` (convolution with a
compactly supported smooth kernel), `Λ`-Lipschitz (an average of the `Λ`-Lipschitz translates of
`F`), and `|Fⱼ(x) − F(x)| ≤ Λσ`, since `|F(y) − F(x)| ≤ Λσ` on `B(x, σ)`. -/
theorem Submission.dimred_mbl_dt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- for each `j` a mollifier `ρ j`: `C^∞`, compactly supported, `≥ 0`, `∫ ρ j = 1`,
  -- `spt ρ j ⊆ B(0, 1/(j+1))`; it is the normalized bump `(∫ φ)⁻¹ φ`
  have hmoll : ∀ j : ℕ, ∃ ρ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ y, 0 ≤ ρ y) ∧ ∫ y, ρ y = 1 ∧ support ρ ⊆ ball 0 (1 / ((j : ℝ) + 1)) := by
    intro j
    have hσ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    let φ : ContDiffBump (0 : Euclid N) :=
      ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), half_pos hσ, half_lt_self hσ⟩
    have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    -- `∫ φ > 0`, as `φ ≥ 0` and `support φ = B(0, σ)` has positive measure
    have hφp : 0 < ∫ y, φ y := by
      rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
      exact measure_ball_pos volume 0 φ.rOut_pos
    have hsupp : support (fun y => (∫ z, φ z)⁻¹ * φ y) ⊆ support φ :=
      support_mul_subset_right _ _
    refine ⟨fun y => (∫ z, φ z)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
      φ.hasCompactSupport.mono hsupp, fun y => mul_nonneg (inv_nonneg.2 hφp.le) φ.nonneg, ?_,
      hsupp.trans φ.support_eq.subset⟩
    rw [integral_const_mul, inv_mul_cancel₀ hφp.ne']
  choose ρ hρs hρc hρn hρi hρsupp using hmoll
  -- `Fs j = ρ j ⋆ F`
  refine ⟨fun j => convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun j => ?_,
    fun j => ?_, fun j x => ?_⟩
  · -- `C^∞`: `ρ j` is `C^∞` with compact support and `F` is continuous, so locally integrable
    exact (hρc j).contDiff_convolution_left _ (hρs j) hF.continuous.locallyIntegrable
  · -- `Λ`-Lipschitz: `Fs j x - Fs j x' = ∫ ρ j t • (F (x - t) - F (x' - t)) dt`
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hint : ∀ z, Integrable (fun t => ρ j t • F (z - t)) := fun z =>
      ((hρs j).continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
        ).integrable_of_hasCompactSupport ((hρc j).smul_right (f' := fun t => F (z - t)))
    show dist (∫ t, ρ j t • F (x - t)) (∫ t, ρ j t • F (x' - t)) ≤ Λ * dist x x'
    rw [dist_eq_norm, ← integral_sub (hint x) (hint x')]
    calc ‖∫ t, ρ j t • F (x - t) - ρ j t • F (x' - t)‖
        ≤ ∫ t, ρ j t * ((Λ : ℝ) * dist x x') := by
          refine norm_integral_le_of_norm_le
            (((hρs j).continuous.integrable_of_hasCompactSupport (hρc j)).mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hρn j t), ← dist_eq_norm]
          refine mul_le_mul_of_nonneg_left ?_ (hρn j t)
          calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
            _ = Λ * dist x x' := by rw [dist_sub_right]
      _ = (Λ : ℝ) * dist x x' := by rw [integral_mul_const, hρi j, one_mul]
  · -- distance: `dist (F y) (F x) ≤ Λ / (j + 1)` on `B(x, 1/(j+1))`, and `ρ j` is a mollifier
    have hg : ∀ y ∈ ball x (1 / ((j : ℝ) + 1)), dist (F y) (F x) ≤ Λ * (1 / ((j : ℝ) + 1)) :=
      fun y hy => (hF.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg)
    calc dist (convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (F x)
        ≤ Λ * (1 / ((j : ℝ) + 1)) :=
          dist_convolution_le (by positivity) (hρsupp j) (hρn j) (hρi j)
            hF.continuous.aestronglyMeasurable hg
      _ = Λ / ((j : ℝ) + 1) := by ring
/-- **Affine homotopies `ℝ^{N+1} → ℝ^{N'}`.**  Write `ι(t, x) = (t, x₁, …, x_N)`,
`e₀ = ι(1, 0)` and `J v = ι(0, v)`.  (i) For `C^∞` maps `F, G : ℝ^N → ℝ^{N'}`, the map
`H(y) = F(tail y) + y₀ • (G(tail y) − F(tail y))` is `C^∞` with
`H(ι(t, x)) = F(x) + t • (G(x) − F(x))`.  (ii) If `H(ι(s, z)) = F(z) + s • (G(z) − F(z))` for all
`s, z`, with `F, G` differentiable at `x` and `H` differentiable at `ι(t, x)`, then the chain rule
along `s ↦ ι(s, x)` and along `z ↦ ι(t, z)` gives `DH e₀ = G(x) − F(x)` and
`DH ∘ J = DF(x) + t • (DG(x) − DF(x))`.  Since `w = w₀ • e₀ + J(tail w)` with
`|w₀|, ‖tail w‖ ≤ ‖w‖`, we get `‖DH‖ ≤ ‖G(x) − F(x)‖ + ‖DF(x) + t • (DG(x) − DF(x))‖`. -/
theorem Submission.dimred_mbl_dt_lpo_affine_homotopy : (∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ ∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ ∀ (N N' : ℕ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (t : ℝ) (x : Euclid N), DifferentiableAt ℝ F x → DifferentiableAt ℝ G x → DifferentiableAt ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) → (∀ (s : ℝ) (z : Euclid N), H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp z))) = F z + s • (G z - F z)) → fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x ∧ (∀ v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v)) ∧ ‖fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖G x - F x‖ + ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ := by
  constructor
  · intro N N' F G hF hG
    -- the coordinates `y ↦ y₀` and `y ↦ tail y = (y₁, …, y_N)` are continuous linear
    obtain ⟨p, hp⟩ : ∃ p : Euclid (N + 1) →L[ℝ] ℝ, ∀ y, p y = WithLp.ofLp y 0 :=
      ⟨EuclideanSpace.proj 0, fun y => rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : Euclid (N + 1) →L[ℝ] Euclid N,
        ∀ y, T y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
          map_add' := fun a b => rfl
          map_smul' := fun c a => rfl }, fun y => rfl⟩
    -- `H(y) = F(tail y) + y₀ • (G(tail y) − F(tail y))` is `C^∞`, and `tail ι(t, x) = x`
    refine ⟨fun y => F (T y) + p y • (G (T y) - F (T y)), ?_, fun t x => ?_⟩
    · exact (hF.comp T.contDiff).add
        (p.contDiff.smul ((hG.comp T.contDiff).sub (hF.comp T.contDiff)))
    · simp only [hp, hT, Fin.tail_cons, Fin.cons_zero, WithLp.toLp_ofLp]
  · intro N N' F G H t x hF hG hH hHFG
    -- `J v = ι(0, v)` is continuous linear
    obtain ⟨J, hJ⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
        ∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
          map_add' := fun a b => by ext i; cases i using Fin.cases <;> simp
          map_smul' := fun c a => by ext i; cases i using Fin.cases <;> simp }, fun v => rfl⟩
    set D := fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) with hD
    set A := fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x) with hA
    -- (a) chain rule along the line `s ↦ ι(s, x) = s • e₀ + J x`: `D e₀ = G(x) − F(x)`
    have he : D (EuclideanSpace.single 0 1) = G x - F x := by
      have hc : HasDerivAt
          (fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)))
          (EuclideanSpace.single 0 1) t := by
        have : (fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) =
            fun s => s • EuclideanSpace.single 0 1 + J x := by
          funext s; ext i; cases i using Fin.cases <;> simp [hJ]
        rw [this]
        simpa using ((hasDerivAt_id t).smul_const
          (EuclideanSpace.single 0 1 : Euclid (N + 1))).add_const (J x)
      have h1 := hH.hasFDerivAt.comp_hasDerivAt t hc
      have h2 : HasDerivAt (fun s : ℝ => F x + s • (G x - F x)) (G x - F x) t := by
        simpa using ((hasDerivAt_id t).smul_const (G x - F x)).const_add (F x)
      have h3 : (H ∘ fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) =
          fun s => F x + s • (G x - F x) := by
        funext s; exact hHFG s x
      rw [h3] at h1
      exact h1.unique h2
    -- (b) chain rule along the affine map `z ↦ ι(t, z) = J z + t • e₀`: `D ∘ J = A`
    have hDJ : D.comp J = A := by
      have hl : HasFDerivAt
          (fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) : Euclid (N + 1)))
          J x := by
        have : (fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) : Euclid (N + 1))) =
            fun z => J z + t • EuclideanSpace.single 0 1 := by
          funext z; ext i; cases i using Fin.cases <;> simp [hJ]
        rw [this]
        exact J.hasFDerivAt.add_const _
      have h1 := hH.hasFDerivAt.comp x hl
      have h2 := hF.hasFDerivAt.add ((hG.hasFDerivAt.sub hF.hasFDerivAt).const_smul t)
      have h3 : (H ∘ fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) :
          Euclid (N + 1))) = fun z => F z + t • (G z - F z) := by
        funext z; exact hHFG t z
      rw [h3] at h1
      exact h1.unique h2
    have hDJv : ∀ v, D (J v) = A v := fun v => by
      rw [← ContinuousLinearMap.comp_apply, hDJ]
    refine ⟨he, fun v => ?_, ?_⟩
    · rw [← hJ, hDJv, hA]
      simp
    -- (c) `w = w₀ • e₀ + J (tail w)`, so `D w = w₀ • (G(x) − F(x)) + A (tail w)`
    · refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
        fun w => ?_
      have hw : w = WithLp.ofLp w 0 • EuclideanSpace.single 0 1 +
          J (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) := by
        ext i; cases i using Fin.cases <;> simp [hJ, Fin.tail]
      have hDw : D w = WithLp.ofLp w 0 • (G x - F x) +
          A (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) := by
        rw [congrArg D hw, map_add, map_smul, he, hDJv]
      -- `|w₀| ≤ ‖w‖` and `‖tail w‖ ≤ ‖w‖`
      have h0 : |WithLp.ofLp w 0| ≤ ‖w‖ := by
        simpa using PiLp.norm_apply_le w 0
      have h1 : ‖(WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)) : Euclid N)‖ ≤ ‖w‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        apply Real.sqrt_le_sqrt
        rw [Fin.sum_univ_succ]
        exact le_add_of_nonneg_left (sq_nonneg _)
      calc ‖D w‖ ≤ ‖WithLp.ofLp w 0 • (G x - F x)‖ +
            ‖A (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)))‖ := by
            rw [hDw]; exact norm_add_le _ _
        _ ≤ |WithLp.ofLp w 0| * ‖G x - F x‖ +
            ‖A‖ * ‖(WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)) : Euclid N)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact add_le_add le_rfl (A.le_opNorm _)
        _ ≤ ‖w‖ * ‖G x - F x‖ + ‖A‖ * ‖w‖ := by gcongr
        _ = (‖G x - F x‖ + ‖A‖) * ‖w‖ := by ring

/-- **Homotopy formula for `C^∞` maps, evaluated on test forms** (Simon 6.2.25–6.2.26).  Let
`H(ι(t, x)) = F(x) + t(G(x) − F(x))` be the affine homotopy of the `C^∞` maps `F`, `G`, and let
`C` (and, in degree `k + 1`, `C'`) be currents supported in `S(X) = ι([0, 1] × spt X)` with
`∂C(β) = X(β₁) − X(β₀)` (resp. `− C'(β)`) for the slices `β_s(x)(v) = β(ι(s, x))(J v)`.  If `ηF`,
`ηG` agree with `F^#ω`, `G^#ω` near `spt X` and `θ`, `θ'` agree with `H^#(dω)`, `H^#ω` near
`S(X)`, then `X(ηG) − X(ηF) = C(θ)` (resp. `C(θ) + C'(θ')`).  A cut-off `θ''` of `H^#ω` near the
compact set `S(X)` has `dθ'' = H^#(dω)` there, so `C(θ) = ∂C(θ'')` by locality; the slices of
`θ''` at `t = 0, 1` agree with `F^#ω`, `G^#ω` near `spt X`, since `H(ι(0, ·)) = F`,
`DH(ι(0, x)) ∘ J = DF(x)`, and likewise at `t = 1` with `G`. -/
theorem Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N N' : ℕ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) H → (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (0 + 1)) (ω : TestFormOn (univ : Set (Euclid N')) 0) (ηF ηG : TestFormOn (univ : Set (Euclid N)) 0) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (0 + 1)), IsCompact X.support → C.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → (∀ β : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ C.boundary β = X η₁ - X η₀) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) 0) x = ((ω : DifferentialForm (Euclid N') 0) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) 0) x = ((ω : DifferentialForm (Euclid N') 0) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ : DifferentialForm (Euclid (N + 1)) (0 + 1)) y = (exteriorDerivative (ω : DifferentialForm (Euclid N') 0) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → X ηG - X ηF = C θ) ∧ ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)) (C' : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (ηF ηG : TestFormOn (univ : Set (Euclid N)) (k + 1)) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)) (θ' : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), IsCompact X.support → C.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → C'.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → (∀ β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ C.boundary β = X η₁ - X η₀ - C' β) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y = (exteriorDerivative (ω : DifferentialForm (Euclid N') (k + 1)) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ' : DifferentialForm (Euclid (N + 1)) (k + 1)) y = ((ω : DifferentialForm (Euclid N') (k + 1)) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → X ηG - X ηF = C θ + C' θ' := by
  intro hVO hREP N N' F G H hF hG hH hHF
  -- (LOC): a current only sees a test form on an open neighbourhood of its support
  have hLOC := (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).2.2.1
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hHd : Differentiable ℝ H := hH.differentiable (by simp)
  -- `(t, x) ↦ ι(t, x)` is continuous, so `S(A) = ι([0, 1] × A)` is compact for compact `A`
  have hι : Continuous fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
    fun_prop
  have hScpt : ∀ A : Set (Euclid N), IsCompact A →
      IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ A,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
    intro A hA
    have hS : {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ A,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} =
        (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
          Euclid (N + 1))) '' (Icc (0 : ℝ) 1 ×ˢ A) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [hS]
    exact (isCompact_Icc.prod hA).image hι
  -- near `spt X`, the slice at `t = s` of `β = H^#ω` is the pull-back by `Φ = H(ι(s, ·))`
  have hslice : ∀ (d : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) d)
      (ω : TestFormOn (univ : Set (Euclid N')) d)
      (β : TestFormOn (univ : Set (Euclid (N + 1))) d) (W'' : Set (Euclid (N + 1))) (s : ℝ)
      (Φ : Euclid N → Euclid N') (η ηΦ : TestFormOn (univ : Set (Euclid N)) d),
      s ∈ Icc (0 : ℝ) 1 → IsOpen W'' →
      {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W'' →
      (∀ y ∈ W'', (β : DifferentialForm (Euclid (N + 1)) d) y =
        ((ω : DifferentialForm (Euclid N') d) (H y)).compContinuousLinearMap (fderiv ℝ H y)) →
      (∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Φ x) →
      (∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
        (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ Φ x v) →
      (∀ (x : Euclid N) (v : Fin d → Euclid N), (η : DifferentialForm (Euclid N) d) x v =
        (β : DifferentialForm (Euclid (N + 1)) d) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        (ηΦ : DifferentialForm (Euclid N) d) x =
          ((ω : DifferentialForm (Euclid N') d) (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)) →
      X η = X ηΦ := by
    rintro d X ω β W'' s Φ η ηΦ hs hW'' hSW'' hβ hΦ hDΦ hη ⟨WΦ, hWΦ, hXWΦ, hηΦ⟩
    -- `η = ηΦ` on the open set `WΦ ∩ ι(s, ·)⁻¹(W'') ⊇ spt X`
    refine hLOC N d X η ηΦ (WΦ ∩ (fun x : Euclid N =>
        (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) ⁻¹' W'')
      (hWΦ.inter (hW''.preimage (by fun_prop)))
      (fun x hx => ⟨hXWΦ hx, (hSW'' ⟨s, hs, x, hx, rfl⟩ :
        WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) ∈ W'')⟩) ?_
    rintro x ⟨hxΦ, hxW''⟩
    rw [hηΦ x hxΦ]
    ext v
    rw [hη x v, hβ (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) hxW'']
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hΦ x]
    congr 1
    funext i
    exact hDΦ x (v i)
  -- `H(ι(0, ·)) = F`, `DH(ι(0, x)) ∘ J = DF(x)`, `H(ι(1, ·)) = G`, `DH(ι(1, x)) ∘ J = DG(x)`
  have hH0 : ∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = F x := by
    intro x
    rw [hHF]
    simp
  have hH1 : ∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = G x := by
    intro x
    rw [hHF]
    simp
  have hDH0 : ∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)))
      (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v := by
    intro x v
    rw [(Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H 0 x (hFd x) (hGd x)
      (hHd _) hHF).2.1 v]
    simp
  have hDH1 : ∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)))
      (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ G x v := by
    intro x v
    rw [(Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H 1 x (hFd x) (hGd x)
      (hHd _) hHF).2.1 v]
    simp
  refine ⟨?_, ?_⟩
  · -- degree `0`
    intro X C ω ηF ηG θ hXc hCS hbd hηF hηG hθ
    obtain ⟨Wθ, hWθ, hSWθ, hθeq⟩ := hθ
    -- a cut-off `θ''` of `H^#ω` near `S(X)`, with `dθ'' = H^#(dω)` there
    obtain ⟨θ'', W'', hW'', hSW'', hθ''eq, hdθ''eq⟩ :=
      Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N' 0 H ω _ hH (hScpt _ hXc)
    -- `C(θ) = C(dθ'') = ∂C(θ'')`, as `θ = H^#(dω) = dθ''` near `S(X) ⊇ spt C`
    have hCθ : C θ = C.boundary θ'' := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hLOC (N + 1) (0 + 1) C θ
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 θ'') (Wθ ∩ W'')
        (hWθ.inter hW'') (fun y hy => ⟨hSWθ (hCS hy), hSW'' (hCS hy)⟩) ?_
      rintro y ⟨hyθ, hy''⟩
      exact (hθeq y hyθ).trans (hdθ''eq y hy'').symm
    -- the boundary relation for `β = θ''`; its slices give `X(η₀) = X(ηF)`, `X(η₁) = X(ηG)`
    obtain ⟨η₀, η₁, hη₀, hη₁, hbdθ''⟩ := hbd θ''
    rw [hCθ, hbdθ'', hslice 0 X ω θ'' W'' 0 F η₀ ηF (left_mem_Icc.2 zero_le_one) hW'' hSW''
      hθ''eq hH0 hDH0 hη₀ hηF, hslice 0 X ω θ'' W'' 1 G η₁ ηG (right_mem_Icc.2 zero_le_one)
      hW'' hSW'' hθ''eq hH1 hDH1 hη₁ hηG]
  · -- degree `k + 1`
    intro k X C C' ω ηF ηG θ θ' hXc hCS hC'S hbd hηF hηG hθ hθ'
    obtain ⟨Wθ, hWθ, hSWθ, hθeq⟩ := hθ
    obtain ⟨Wθ', hWθ', hSWθ', hθ'eq⟩ := hθ'
    obtain ⟨θ'', W'', hW'', hSW'', hθ''eq, hdθ''eq⟩ :=
      Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N' (k + 1) H ω _ hH (hScpt _ hXc)
    have hCθ : C θ = C.boundary θ'' := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hLOC (N + 1) (k + 1 + 1) C θ
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) θ'') (Wθ ∩ W'')
        (hWθ.inter hW'') (fun y hy => ⟨hSWθ (hCS hy), hSW'' (hCS hy)⟩) ?_
      rintro y ⟨hyθ, hy''⟩
      exact (hθeq y hyθ).trans (hdθ''eq y hy'').symm
    -- `C'(θ'') = C'(θ')`, as both are `H^#ω` near `S(X) ⊇ spt C'`
    have hC'θ : C' θ'' = C' θ' := by
      refine hLOC (N + 1) (k + 1) C' θ'' θ' (W'' ∩ Wθ') (hW''.inter hWθ')
        (fun y hy => ⟨hSW'' (hC'S hy), hSWθ' (hC'S hy)⟩) ?_
      rintro y ⟨hy'', hyθ'⟩
      exact (hθ''eq y hy'').trans (hθ'eq y hyθ').symm
    obtain ⟨η₀, η₁, hη₀, hη₁, hbdθ''⟩ := hbd θ''
    rw [hCθ, hbdθ'', ← hC'θ, hslice (k + 1) X ω θ'' W'' 0 F η₀ ηF (left_mem_Icc.2 zero_le_one)
      hW'' hSW'' hθ''eq hH0 hDH0 hη₀ hηF, hslice (k + 1) X ω θ'' W'' 1 G η₁ ηG
      (right_mem_Icc.2 zero_le_one) hW'' hSW'' hθ''eq hH1 hDH1 hη₁ hηG]
    ring
/-- **Mass bound for the affine homotopy current** (Simon Ch. 6, 2.25–2.27, p. 140).  Let
`H(t, x) = F(x) + t(G(x) − F(x))` be the affine homotopy (2.26) of the `C^∞` maps `F, G`, and let
`C ∈ 𝒟_{k+1}(ℝ^{N+1})` be given by `C(ω) = ∫₀¹ X(η_t) dt`, `η_t(x)(v) = ω(t, x)(e₀, Jv)`.  If
`‖DF‖, ‖DG‖ ≤ Λ` and `|F − G| ≤ δ` on `spt X`, `|β| ≤ b` and `θ = H^#β` on `[0,1] × spt X`, then
`|C(θ)| ≤ δ Λᵏ b M(X)` (the estimate behind 2.27).  Indeed
`η_t(x) = (β(H(t, x)) ⌞ (G x − F x)) ∘ ((1 − t) DF(x) + t DG(x))`, so (L1) and (L2) give
`|η_t(x)| ≤ Λᵏ δ b` on `spt X`; the toolkit bound `|X(ψ)| ≤ c M(X)` is then integrated over
`t ∈ [0,1]`. -/
theorem Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (Λ δ b : ℝ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (β : TestFormOn (univ : Set (Euclid N')) (k + 1)) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) H → (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → X.mass < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((β : DifferentialForm (Euclid N') (k + 1)) y) ≤ b) → (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support, (θ : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((β : DifferentialForm (Euclid N') (k + 1)) (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))).compContinuousLinearMap (fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = ∫ t in (0 : ℝ)..1, X (η t)) → |C θ| ≤ δ * Λ ^ k * b * X.mass.toReal := by
  intro hVO hREP hL N N' k Λ δ b F G H X C β θ hF hG hH hHdef hXmass hΛ hδ hb hθ hC
  obtain ⟨hL1, hL2⟩ := hL
  -- (A0): `|X(ψ)| ≤ c·M(X)` whenever `|ψ| ≤ c` on `spt X`
  have hA0 := (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).1
  -- step 1: `C(θ) = ∫₀¹ X(η_t) dt` with `η_t(x)(v) = θ(ι(t,x))(e₀, Jv)`
  obtain ⟨η, hη, hCθ⟩ := hC θ
  -- steps 2–4: `|η_t(x)| ≤ Λ^k·δ·b` for `t ∈ [0,1]` and `x ∈ spt X`
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support,
      covectorEuclideanNorm ((η t : DifferentialForm (Euclid N) k) x) ≤ Λ ^ k * δ * b := by
    intro t ht x hx
    -- step 2: `DH(e₀) = G x - F x` and `DH(Jv) = A v`, `A = DF(x) + t•(DG(x) - DF(x))`
    obtain ⟨he₀, hJ, -⟩ := Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H t x
      (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)
      (hH.differentiable (by simp) _) hHdef
    -- step 3: `η_t(x) = ((β(H y)).curryLeft (G x - F x)).compContinuousLinearMap A`
    have hrep : (η t : DifferentialForm (Euclid N) k) x =
        (((β : DifferentialForm (Euclid N') (k + 1))
          (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))).curryLeft
            (G x - F x)).compContinuousLinearMap
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
      ext v
      have hJv : (fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∘
          fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) =
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) ∘ v := by
        funext i
        exact hJ (v i)
      rw [hη, hθ t ht x hx, ContinuousAlternatingMap.compContinuousLinearMap_apply, Fin.comp_cons,
        he₀, hJv]
      rfl
    -- step 4: `‖A‖ ≤ Λ`, as `A = (1 - t)•DF(x) + t•DG(x)` lies in the convex ball `‖·‖ ≤ Λ`;
    -- `‖G x - F x‖ ≤ δ` and `|β(H y)| ≤ b`; then (L1) and (L2)
    have hA : ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ≤ Λ :=
      mem_closedBall_zero_iff.mp
        ((convex_closedBall (0 : Euclid N →L[ℝ] Euclid N') Λ).add_smul_sub_mem
          (mem_closedBall_zero_iff.mpr (hΛ x hx).1) (mem_closedBall_zero_iff.mpr (hΛ x hx).2) ht)
    have hu : ‖G x - F x‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact hδ x hx
    have hAk : ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ^ k ≤ Λ ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hA k
    rw [hrep]
    refine (hL1 _ _ _ _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (hL2 _ _ _ _) (pow_nonneg (norm_nonneg _) k)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul hAk (mul_le_mul hu (hb _) (covectorEuclideanNorm_nonneg _)
      ((norm_nonneg _).trans hu)) (mul_nonneg (norm_nonneg _) (covectorEuclideanNorm_nonneg _))
      ((pow_nonneg (norm_nonneg _) k).trans hAk)
  -- step 5: (A0) for each `t ∈ [0,1]`
  have hXt : ∀ t ∈ Icc (0 : ℝ) 1, |X (η t)| ≤ Λ ^ k * δ * b * X.mass.toReal :=
    fun t ht => hA0 N k X (η t) _ hXmass (hpt t ht)
  -- step 6: the interval-integral bound on `Ι 0 1 = Ioc 0 1 ⊆ Icc 0 1`
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => X (η t)) (C := Λ ^ k * δ * b * X.mass.toReal) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [Real.norm_eq_abs]
      exact hXt t (Ioc_subset_Icc_self ht)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  rw [hCθ]
  calc |∫ t in (0 : ℝ)..1, X (η t)| ≤ Λ ^ k * δ * b * X.mass.toReal := hint
    _ = δ * Λ ^ k * b * X.mass.toReal := by ring

/-- **Lipschitz homotopy formula and homotopy mass bound** (Simon 6.2.24–6.2.25 for Lipschitz maps,
as used in the deformation theorem 6.4.1).  For `Λ`-Lipschitz `F, G : ℝᴺ → ℝᴺ'` and an
`L`-Lipschitz `H` which is the affine homotopy `H(t, x) = F x + t (G x − F x)` on `[0, 1] × spt X`,
the push-forward `lpush` characterized by smooth approximation satisfies
`G#X − F#X = ∂ H#(cyl X)` in degree `0`, `G#X − F#X − H#(cyl ∂X) = ∂ H#(cyl X)` in degree `k + 1`,
and `M(H#(cyl X)) ≤ δ (2Λ)ᵏ M(X)` when `dist(F, G) ≤ δ` on `spt X`.  Mollify `F, G` to `Fⱼ, Gⱼ`,
take the smooth affine homotopies `Hⱼ` (which converge to `H` uniformly on `[0, 1] × spt X` with
bounded derivatives), apply the smooth homotopy identity and mass bound to cut-off pull-backs, and
pass to the limit with the characterization of `lpush`. -/
theorem Submission.dimred_mbl_dt_lpo_lipschitz_homotopy : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hL lpush cyl hCHAR hC1 hC3 hC4 hC5
  obtain ⟨-, hMB, -, -, hNCB⟩ := Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP
  obtain ⟨hAH, hAHd⟩ := Submission.dimred_mbl_dt_lpo_affine_homotopy
  have hSI := Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity hVO hREP
  have hSM := Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass hVO hREP hL
  have hcut := Submission.dimred_mbl_dt_lpo_cutoff_pullback
  have hsub : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n) (ω : TestFormOn U n),
      (S - T) ω = S ω - T ω := fun _ _ _ _ _ _ => rfl
  -- `S(K) = {ι(t, x) : t ∈ [0, 1], x ∈ K}` is compact for compact `K`.
  have hScpt : ∀ (N : ℕ) (K : Set (Euclid N)), IsCompact K →
      IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
    intro N K hK
    have hc : Continuous (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) := by
      fun_prop
    convert (isCompact_Icc.prod hK).image hc using 1
    ext y
    constructor
    · rintro ⟨t, ht, x, hx, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨t, ht, x, hx, rfl⟩
  -- Steps 0–0.2: mollified maps `Fⱼ, Gⱼ`, smooth affine homotopies `Hⱼ`, uniform convergence and
  -- derivative bounds.
  have key : ∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N')
      (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K →
      (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
        H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) →
      ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧
        (∀ j (t : ℝ) (x : Euclid N),
          Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = Fs j x + t • (Gs j x - Fs j x)) ∧
        (∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ) ∧ (∀ j x, ‖fderiv ℝ (Gs j) x‖ ≤ Λ) ∧
        (∀ (j : ℕ) x, dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧
        (∀ (j : ℕ) x, dist (Gs j x) (G x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧
        TendstoUniformlyOn Fs F atTop K ∧ TendstoUniformlyOn Gs G atTop K ∧
        TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
          y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ∧
        ∀ j, ∀ y ∈ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
          y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}, ‖fderiv ℝ (Hs j) y‖ ≤ Λ' := by
    intro N N' Λ F G H K hF hG hK hHK
    obtain ⟨Fs, hFsC, hFsL, hFd⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ F hF
    obtain ⟨Gs, hGsC, hGsL, hGd⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ G hG
    choose Hs hHsC hHsid using fun j => hAH N N' (Fs j) (Gs j) (hFsC j) (hGsC j)
    obtain ⟨D₀, hD₀⟩ :=
      hK.exists_bound_of_continuousOn (hG.continuous.sub hF.continuous).continuousOn
    have hFsD : ∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ := fun j _ => norm_fderiv_le_of_lipschitz ℝ (hFsL j)
    have hGsD : ∀ j x, ‖fderiv ℝ (Gs j) x‖ ≤ Λ := fun j _ => norm_fderiv_le_of_lipschitz ℝ (hGsL j)
    have hdiv : ∀ j : ℕ, (Λ : ℝ) / ((j : ℝ) + 1) ≤ Λ := fun j =>
      div_le_self Λ.coe_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg j))
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
    refine ⟨Fs, Gs, Hs, D₀ + 5 * (Λ : ℝ), hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, hFd, hGd,
      ?_, ?_, ?_, ?_⟩
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x _
      rw [dist_comm]
      exact (hFd j x).trans_lt hj
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x _
      rw [dist_comm]
      exact (hGd j x).trans_lt hj
    · -- Step 0.1: `‖Hⱼ − H‖ ≤ Λ/(j+1)` on `S(K)`.
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj
      rintro y ⟨t, ht, x, hx, rfl⟩
      rw [hHsid j t x, hHK x hx t ht, dist_eq_norm]
      have e : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
          (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      have h1 : ‖F x - Fs j x‖ ≤ Λ / (j + 1) := by
        rw [← dist_eq_norm, dist_comm]
        exact hFd j x
      have h2 : ‖G x - Gs j x‖ ≤ Λ / (j + 1) := by
        rw [← dist_eq_norm, dist_comm]
        exact hGd j x
      rw [e]
      calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
          ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
        _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2),
            Real.norm_of_nonneg ht.1]
        _ ≤ (1 - t) * (Λ / (j + 1)) + t * (Λ / (j + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left h2 ht.1)
        _ = Λ / (j + 1) := by ring
        _ < ε := hj
    · -- Step 0.2: `‖DHⱼ‖ ≤ D₀ + 5Λ` on `S(K)`.
      intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      have hd := (hAHd N N' (Fs j) (Gs j) (Hs j) t x ((hFsC j).differentiable (by simp) x)
        ((hGsC j).differentiable (by simp) x) ((hHsC j).differentiable (by simp) _) (hHsid j)).2.2
      have a1 : ‖Gs j x - G x‖ ≤ Λ := by
        rw [← dist_eq_norm]
        exact (hGd j x).trans (hdiv j)
      have a2 : ‖F x - Fs j x‖ ≤ Λ := by
        rw [← dist_eq_norm, dist_comm]
        exact (hFd j x).trans (hdiv j)
      have a3 : ‖G x - F x‖ ≤ D₀ := hD₀ x hx
      have b1 : ‖Gs j x - Fs j x‖ ≤ 2 * Λ + D₀ := by
        have e : Gs j x - Fs j x = (Gs j x - G x) + (G x - F x) + (F x - Fs j x) := by abel
        rw [e]
        have n1 := norm_add_le (Gs j x - G x + (G x - F x)) (F x - Fs j x)
        have n2 := norm_add_le (Gs j x - G x) (G x - F x)
        linarith
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have b2 : ‖fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)‖ ≤ 3 * Λ := by
        have n1 := norm_add_le (fderiv ℝ (Fs j) x) (t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))
        have n2 : ‖t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)‖ ≤ 1 * (Λ + Λ) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul ht1 ((norm_sub_le _ _).trans (add_le_add (hGsD j x) (hFsD j x)))
            (norm_nonneg _) zero_le_one
        have n3 := hFsD j x
        linarith
      linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (10): degree `0`.
    intro N N' Λ L F G H X hF hG hH hXc hXm hHX
    have hXb : boundaryMassOn X univ < ∞ := by simp [boundaryMassOn]
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, -, -, hFU, hGU, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N 0 X hXc hXm hXb
    apply GeometricCurrentOn.ext
    intro ω
    rw [hsub, GeometricCurrentOn.boundary_apply]
    choose ηF WF hWFo hWFK hηF _ using
      fun j => hcut N N' 0 (Fs j) ω X.support (hFsC j) hXc
    choose ηG WG hWGo hWGK hηG _ using
      fun j => hcut N N' 0 (Gs j) ω X.support (hGsC j) hXc
    choose θ WH hWHo hWHK hθ _ using
      fun j => hcut (N + 1) N' (0 + 1) (Hs j) (exteriorDerivativeTestOn univ 0 ω) _ (hHsC j)
        (hScpt N X.support hXc)
    have lF : Tendsto (fun j => X (ηF j)) atTop (𝓝 (lpush N N' 0 F X ω)) :=
      hCHAR N N' 0 Λ Λ F Fs X ω ηF hF hXc hXm hXb hFsC (fun j x _ => hFsD j x) hFU
        (fun j => ⟨WF j, hWFo j, hWFK j, hηF j⟩)
    have lG : Tendsto (fun j => X (ηG j)) atTop (𝓝 (lpush N N' 0 G X ω)) :=
      hCHAR N N' 0 Λ Λ G Gs X ω ηG hG hXc hXm hXb hGsC (fun j x _ => hGsD j x) hGU
        (fun j => ⟨WG j, hWGo j, hWGK j, hηG j⟩)
    have lH : Tendsto (fun j => cyl N 0 X (θ j)) atTop
        (𝓝 (lpush (N + 1) N' (0 + 1) H (cyl N 0 X) (exteriorDerivativeTestOn univ 0 ω))) :=
      hCHAR (N + 1) N' (0 + 1) L Λ' H Hs (cyl N 0 X) (exteriorDerivativeTestOn univ 0 ω) θ hH
        hcylc (hcylm.trans_lt hXm) hcylb hHsC (fun j y hy => hHsD j y (hcylS hy))
        (hHU.mono hcylS) (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
    have hid : ∀ j, X (ηG j) - X (ηF j) = cyl N 0 X (θ j) := fun j =>
      (hSI N N' (Fs j) (Gs j) (Hs j) (hFsC j) (hGsC j) (hHsC j) (hHsid j)).1 X (cyl N 0 X) ω
        (ηF j) (ηG j) (θ j) hXc hcylS (hC4 N X hXc hXm) ⟨WF j, hWFo j, hWFK j, hηF j⟩
        ⟨WG j, hWGo j, hWGK j, hηG j⟩ ⟨WH j, hWHo j, hWHK j, hθ j⟩
    exact tendsto_nhds_unique (lG.sub lF) (lH.congr fun j => (hid j).symm)
  · -- (11): degree `k + 1`.
    intro N N' k Λ L F G H X hF hG hH hXc hXm hXbm hHX
    have hXb : boundaryMassOn X univ < ∞ := hXbm
    obtain ⟨hbS, hbc, hbb⟩ := hNCB N k X hXc hXbm
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, -, -, hFU, hGU, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N (k + 1) X hXc hXm hXb
    obtain ⟨hcbc, hcbm, hcbb, hcbS⟩ := hC1 N k X.boundary hbc hXbm hbb
    have hcbS' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hcbS hy
      exact ⟨t, ht, x, hbS hx, rfl⟩
    apply GeometricCurrentOn.ext
    intro ω
    rw [hsub, hsub, GeometricCurrentOn.boundary_apply]
    choose ηF WF hWFo hWFK hηF _ using
      fun j => hcut N N' (k + 1) (Fs j) ω X.support (hFsC j) hXc
    choose ηG WG hWGo hWGK hηG _ using
      fun j => hcut N N' (k + 1) (Gs j) ω X.support (hGsC j) hXc
    choose θ WH hWHo hWHK hθ _ using
      fun j => hcut (N + 1) N' (k + 1 + 1) (Hs j) (exteriorDerivativeTestOn univ (k + 1) ω) _
        (hHsC j) (hScpt N X.support hXc)
    choose θ' WH' hWH'o hWH'K hθ' _ using
      fun j => hcut (N + 1) N' (k + 1) (Hs j) ω _ (hHsC j) (hScpt N X.support hXc)
    have lF : Tendsto (fun j => X (ηF j)) atTop (𝓝 (lpush N N' (k + 1) F X ω)) :=
      hCHAR N N' (k + 1) Λ Λ F Fs X ω ηF hF hXc hXm hXb hFsC (fun j x _ => hFsD j x) hFU
        (fun j => ⟨WF j, hWFo j, hWFK j, hηF j⟩)
    have lG : Tendsto (fun j => X (ηG j)) atTop (𝓝 (lpush N N' (k + 1) G X ω)) :=
      hCHAR N N' (k + 1) Λ Λ G Gs X ω ηG hG hXc hXm hXb hGsC (fun j x _ => hGsD j x) hGU
        (fun j => ⟨WG j, hWGo j, hWGK j, hηG j⟩)
    have lH : Tendsto (fun j => cyl N (k + 1) X (θ j)) atTop
        (𝓝 (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)
          (exteriorDerivativeTestOn univ (k + 1) ω))) :=
      hCHAR (N + 1) N' (k + 1 + 1) L Λ' H Hs (cyl N (k + 1) X)
        (exteriorDerivativeTestOn univ (k + 1) ω) θ hH hcylc (hcylm.trans_lt hXm) hcylb hHsC
        (fun j y hy => hHsD j y (hcylS hy)) (hHU.mono hcylS)
        (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
    have lH' : Tendsto (fun j => cyl N k X.boundary (θ' j)) atTop
        (𝓝 (lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) ω)) :=
      hCHAR (N + 1) N' (k + 1) L Λ' H Hs (cyl N k X.boundary) ω θ' hH hcbc
        (hcbm.trans_lt hXbm) hcbb hHsC (fun j y hy => hHsD j y (hcbS' hy)) (hHU.mono hcbS')
        (fun j => ⟨WH' j, hWH'o j, hcbS'.trans (hWH'K j), hθ' j⟩)
    have hid : ∀ j, X (ηG j) - X (ηF j) = cyl N (k + 1) X (θ j) + cyl N k X.boundary (θ' j) :=
      fun j => (hSI N N' (Fs j) (Gs j) (Hs j) (hFsC j) (hGsC j) (hHsC j) (hHsid j)).2 k X
        (cyl N (k + 1) X) (cyl N k X.boundary) ω (ηF j) (ηG j) (θ j) (θ' j) hXc hcylS hcbS'
        (hC5 N k X hXc hXm hXbm) ⟨WF j, hWFo j, hWFK j, hηF j⟩ ⟨WG j, hWGo j, hWGK j, hηG j⟩
        ⟨WH j, hWHo j, hWHK j, hθ j⟩ ⟨WH' j, hWH'o j, hWH'K j, hθ' j⟩
    have hlim := tendsto_nhds_unique (lG.sub lF) ((lH.add lH').congr fun j => (hid j).symm)
    linarith
  · -- (12): the homotopy mass bound.
    intro N N' k Λ L F G H X δ hF hG hH hXc hXm hXb hHX hδ
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, hFd, hGd, -, -, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N k X hXc hXm hXb
    have hδp : 0 ≤ max δ 0 := le_max_right δ 0
    have h0 : Tendsto (fun j : ℕ => 2 * (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (Λ : ℝ))
    have hbound : (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤
        ENNReal.ofReal (max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal) := by
      apply hMB N' (k + 1)
      intro ω c hωc
      choose θ WH hWHo hWHK hθ _ using
        fun j => hcut (N + 1) N' (k + 1) (Hs j) ω _ (hHsC j) (hScpt N X.support hXc)
      have lH : Tendsto (fun j => cyl N k X (θ j)) atTop
          (𝓝 (lpush (N + 1) N' (k + 1) H (cyl N k X) ω)) :=
        hCHAR (N + 1) N' (k + 1) L Λ' H Hs (cyl N k X) ω θ hH hcylc (hcylm.trans_lt hXm) hcylb
          hHsC (fun j y hy => hHsD j y (hcylS hy)) (hHU.mono hcylS)
          (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
      have hj : ∀ j : ℕ, |cyl N k X (θ j)| ≤
          (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * (Λ : ℝ) ^ k * c * X.mass.toReal := by
        intro j
        refine hSM N N' k Λ (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) c (Fs j) (Gs j) (Hs j) X
          (cyl N k X) ω (θ j) (hFsC j) (hGsC j) (hHsC j) (hHsid j) hXm
          (fun x _ => ⟨hFsD j x, hGsD j x⟩) ?_ hωc ?_ (hC3 N k X hXc hXm hXb)
        · intro x hx
          have e1 := hFd j x
          have e2 := hGd j x
          have e3 := hδ x hx
          have e4 := dist_triangle4 (Fs j x) (F x) (G x) (Gs j x)
          rw [dist_comm (G x) (Gs j x)] at e4
          have e5 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) = Λ / (j + 1) + Λ / (j + 1) := by ring
          have e6 := le_max_left δ 0
          linarith
        · intro t ht x hx
          exact hθ j _ (hWHK j ⟨t, ht, x, hx, rfl⟩)
      have hlim : Tendsto (fun j : ℕ =>
          (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * (Λ : ℝ) ^ k * c * X.mass.toReal) atTop
          (𝓝 ((max δ 0 + 0) * (Λ : ℝ) ^ k * c * X.mass.toReal)) :=
        (((tendsto_const_nhds.add h0).mul_const _).mul_const _).mul_const _
      have hle := le_of_tendsto_of_tendsto' lH.abs hlim hj
      calc |lpush (N + 1) N' (k + 1) H (cyl N k X) ω|
          ≤ (max δ 0 + 0) * (Λ : ℝ) ^ k * c * X.mass.toReal := hle
        _ = max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal * c := by ring
    have hmax : ENNReal.ofReal (max δ 0) = ENNReal.ofReal δ := by
      rcases le_total 0 δ with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    have h2 : (Λ : ℝ≥0∞) ≤ 2 * (Λ : ℝ≥0∞) := le_mul_of_one_le_left (by positivity) one_le_two
    calc (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass
        ≤ ENNReal.ofReal (max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal) := hbound
      _ = ENNReal.ofReal δ * (Λ : ℝ≥0∞) ^ k * X.mass := by
        rw [ENNReal.ofReal_mul (mul_nonneg hδp (pow_nonneg Λ.coe_nonneg k)),
          ENNReal.ofReal_mul hδp, ENNReal.ofReal_toReal hXm.ne, hmax, ← NNReal.coe_pow,
          ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
      _ ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by gcongr

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
