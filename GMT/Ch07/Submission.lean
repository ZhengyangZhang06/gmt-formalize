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

/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- **Approximate tangent spaces under dilation** (Simon Ch. 3, 1.4).  For `c > 0` the blow-ups
of `c⁻¹M = {x : cx ∈ M}` at `z` are blow-ups of `M` at `cz`: `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)`, as
`(cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z)`.  Since `cr ↓ 0` as `r ↓ 0`, the limits defining `Q` as the
approximate tangent space of `M` at `cz` give the limits for `c⁻¹M` at `z`. -/
theorem Submission.approx_tangent_space_smul_preimage : ∀ (P n : ℕ) (M : Set (Euclid P)) (c : ℝ) (z : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < c → HasApproximateTangentSpaceAt n M (c • z) Q → HasApproximateTangentSpaceAt n ((fun x => c • x) ⁻¹' M) z Q := by
  intro P n M c z Q hc hT
  have hc0 : c ≠ 0 := hc.ne'
  -- `η_{cz,cr}(m) = (cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z) = η_{z,r}(c⁻¹m)`
  have hη : ∀ (r : ℝ) (m : Euclid P), Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) m =
      Poincare.SimonGMT.Chapter03.blowUpMap z r (c⁻¹ • m) := by
    intro r m
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, Poincare.SimonGMT.Chapter03.blowUpMap, mul_inv_rev,
      ← smul_smul, smul_sub c⁻¹, inv_smul_smul₀ hc0]
  -- `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)` for every `r`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap z r '' ((fun x => c • x) ⁻¹' M) =
      Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) '' M := by
    intro r
    ext y
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨c • m', hm', by rw [hη, inv_smul_smul₀ hc0]⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c⁻¹ • m, ?_, (hη r m).symm⟩
      show c • c⁻¹ • m ∈ M
      rwa [smul_inv_smul₀ hc0]
  -- `r ↦ cr` tends to `0` within `(0, ∞)`: it is continuous, vanishes at `0` and is positive
  -- for `r > 0`
  have hφ : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := (continuous_const_mul c).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  -- the limit at `cz` along `cr ↓ 0` is the limit at `z` along `r ↓ 0`
  refine ⟨hT.1, fun f => ((hT.2 f).comp hφ).congr fun r => ?_⟩
  rw [Function.comp_apply, hset r]

/-- **Dilating an integer multiplicity triple** (Simon Ch. 6, 3.1 and 2.23).  For `c > 0` and
`T x = c • x`, the triple `(T⁻¹M, θ ∘ T, ξ ∘ T)` is again integer multiplicity in `ℝᴾ`.  By the
change of variables `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M`, null sets, local integrability and
`Hⁿ⌞M`-a.e. statements transfer through the measurable embedding `T`; the maps `c⁻¹ • Fⱼ`
parametrize `T⁻¹M`, and approximate tangent spaces are dilation invariant. -/
theorem Submission.imrep_univ_smul_rescale_exists : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x) := by
  intro P n R c hc
  have hc0 : c ≠ 0 := hc.ne'
  -- `T x = c • x` is a homeomorphism of `ℝᴾ`, hence measurable and a measurable embedding
  have hT : Measurable (fun x : Euclid P => c • x) := measurable_const_smul c
  have hTemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc0).measurableEmbedding
  -- (CV): `T_#(Hⁿ⌞T⁻¹S) = c⁻ⁿ Hⁿ⌞S` and the lower-integral change of variables, for every `S`
  have hCV := Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
  -- (∗) `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M` for `M = R.carrier`
  have hstar := (hCV R.carrier).1
  refine ⟨{ carrier := (fun x : Euclid P => c • x) ⁻¹' R.carrier
            mult := fun x => R.mult (c • x)
            orient := fun x => R.orient (c • x)
            measurableSet_carrier := hT R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp hT
            mult_pos := fun x hx => R.mult_pos (c • x) hx
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl⟩
  · -- rectifiability: `T⁻¹M ⊆ T⁻¹M₀ ∪ ⋃ⱼ range (c⁻¹ • Fⱼ)` with `Hⁿ(T⁻¹M₀) = 0`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun x : Euclid P => c • x) ⁻¹' M₀, ?_, fun j w => c⁻¹ • F j w, fun j => ?_, ?_⟩
    · -- evaluate `T_#(Hⁿ⌞T⁻¹M₀) = c⁻ⁿ Hⁿ⌞M₀` on `univ`
      have h := congrArg (fun μ : Measure (Euclid P) => μ univ) (hCV M₀).1
      simp only at h
      rwa [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.smul_apply, Measure.restrict_apply_univ, hM₀, smul_zero] at h
    · -- `c⁻¹ • Fⱼ` is `‖c⁻¹‖₊ Kⱼ`-Lipschitz
      obtain ⟨K, hK⟩ := hF j
      exact ⟨‖c⁻¹‖₊ * K, (lipschitzWith_smul c⁻¹).comp hK⟩
    · -- if `c • z = Fⱼ w` then `z = c⁻¹ • Fⱼ w`
      intro z hz
      rcases hcover hz with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, w, by simp only [hw, inv_smul_smul₀ hc0]⟩)
  · -- local integrability: `T⁻¹M ∩ K = T⁻¹(M ∩ T(K))` with `T(K)` compact
    intro K hK _
    have hTK : IsCompact ((fun x : Euclid P => c • x) '' K) := hK.image (continuous_const_smul c)
    have hset : (fun x : Euclid P => c • x) ⁻¹' R.carrier ∩ K =
        (fun x : Euclid P => c • x) ⁻¹' (R.carrier ∩ (fun x : Euclid P => c • x) '' K) := by
      rw [preimage_inter, hTemb.injective.preimage_image]
    rw [hset, (hCV (R.carrier ∩ (fun x : Euclid P => c • x) '' K)).2.1 fun y => (R.mult y : ℝ≥0∞)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (R.locallyIntegrable_mult _ hTK (subset_univ _))
  · -- `ξ` is a.e.-strongly measurable for `c⁻ⁿ Hⁿ⌞M = T_#(Hⁿ⌞T⁻¹M)`; compose with `T`
    have h := R.aestronglyMeasurable_orient.smul_measure (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar] at h
    exact h.comp_aemeasurable hT.aemeasurable
  · -- the orientation statement holds `T_#(Hⁿ⌞T⁻¹M)`-a.e., i.e. at `c • z` for a.e. `z ∈ T⁻¹M`;
    -- there `Q` is also the approximate tangent space of `T⁻¹M` at `z`
    have h := Measure.ae_smul_measure R.orients (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar, hTemb.ae_map_iff] at h
    filter_upwards [h] with z ⟨Q, hQ, hξ⟩
    exact ⟨Q, Submission.approx_tangent_space_smul_preimage P n R.carrier c z Q hc hQ, hξ⟩
/-- **A cone takes equal values on dilated test forms** (Simon 7.3.1(2), via 6.2.23).
If `C ∈ 𝒟ₙ(ℝᴾ)` is a cone, `λ > 0` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)` defines a test
form with `C(ω') = C(ω)`.  As `η_{0,λ}(ℝᴾ) = ℝᴾ`, the cone property `η_{0,λ#}C = C` reads
`C(η_{0,λ}^# ω) = C(ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.cone_current_apply_dilation_pullback : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsConeCurrent C → ∀ lam : ℝ, 0 < lam → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) ∧ C ω' = C ω := by
  intro P n C hC lam hlam ω
  -- Step 1: the cone property `η_{0,λ#}C(ω) = C(ω)`.
  have hcone := hC lam hlam ω
  -- Step 2: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h] at hcone
  -- Steps 3–4: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω')` for the affine pullback `ω'` of `ω`,
  -- so `C(ω') = C(ω)`.
  refine ⟨_, fun y => ?_, hcone⟩
  -- Step 5: `ω'(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Action and weight of a dilated triple** (Simon 6.3.1 (‡) and Ch. 4, 1.1, under
`x ↦ cx`; used for the cone `C` of 7.3.1(2)).  If `c > 0` and `R' = (M', θ', ξ')` is
`R = (M, θ, ξ)` pulled back by `x ↦ cx`, i.e. `M' = {x : cx ∈ M}`, `θ'(x) = θ(cx)` and
`ξ'(x) = ξ(cx)`, then `τ(R')(ω) = τ(R)(ω_c)` with `ω_c(y) = c⁻ⁿ ω(c⁻¹y)` for every `n`-form `ω`,
and `μ_{R'}(A) = c⁻ⁿ μ_R(cA)` for every Borel `A`.  Both follow from the change of variables
`∫_{M'} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ`. -/
theorem Submission.imrep_smul_rescale_action_measure : ∀ (P n : ℕ) (R R' : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → R'.carrier = (fun x => c • x) ⁻¹' R.carrier → (∀ x, R'.mult x = R.mult (c • x)) → (∀ x, R'.orient x = R.orient (c • x)) → (∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action (fun y => (c⁻¹ ^ n) • ω (c⁻¹ • y))) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R'.measure A = ENNReal.ofReal (c⁻¹ ^ n) * R.measure ((fun x => c • x) '' A) := by
  intro P n R R' c hc hcar hmult horient
  -- `T x = cx` is a measurable embedding with `c⁻¹ (cz) = z`.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    measurableEmbedding_const_smul₀ hc.ne'
  have hinv : ∀ z : Euclid P, c⁻¹ • c • z = z := fun z => by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- Step 1: `R'.action ω = ∫_{T⁻¹M} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ` for
    -- `g(y) = θ(y) ξ(y)(ω(c⁻¹y))`.
    have hcv := (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      R.carrier).2.2 fun y => (R.mult y : ℝ) * R.orient y (ω (c⁻¹ • y))
    simp only [hinv] at hcv
    unfold IMRep.action
    rw [hcar]
    simp only [hmult, horient]
    -- Step 2: move `c⁻ⁿ` inside the integral and use the linearity of `ξ(y)`.
    rw [hcv, ← integral_const_mul]
    congr 1
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  · -- Step 3: `R'.measure A = ∫⁻_{A ∩ M'} θ(c·) dHⁿ`, and `A ∩ M' = T⁻¹(cA ∩ M)`.
    have hTA : MeasurableSet ((fun x : Euclid P => c • x) '' A) := hT.measurableSet_image.2 hA
    have hset : A ∩ R'.carrier =
        (fun x : Euclid P => c • x) ⁻¹' ((fun x : Euclid P => c • x) '' A ∩ R.carrier) := by
      rw [preimage_inter, preimage_image_eq _ hT.injective, hcar]
    unfold IMRep.measure
    rw [withDensity_apply _ hA, withDensity_apply _ hTA, Measure.restrict_restrict hA,
      Measure.restrict_restrict hTA, hset]
    simp only [hmult]
    -- Step 4: the lower-integral change of variables on `cA ∩ M`.
    exact (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      ((fun x : Euclid P => c • x) '' A ∩ R.carrier)).2.1 fun y => (R.mult y : ℝ≥0∞)
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
/-- **The weight of a cone is homogeneous of degree `n`** (proof of Simon 7.4.5,
chapter-07.txt lines 697–699, "by virtue of the fact that `C` is a cone").  If the cone `C` is
represented by `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` and `λ > 0`, then `μ(λA) = λⁿ μ(A)` for
every Borel `A`.  The dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, and
`R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·)) = C(λ⁻ⁿ ω(λ⁻¹·)) = C(ω)` as `η_{0,λ#}C = C`, so `R_λ` represents `C`.
By the uniqueness of the weight (Simon Ch. 6, 3.2(3)), `μ(A) = μ_{R_λ}(A) = λ⁻ⁿ μ(λA)`. -/
theorem Submission.cone_current_imrep_measure_smul_image : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n C R hC hR lam hlam A hA
  -- Step 1: the dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, with
  -- `R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·))` for every form `ω` and `μ_{R_λ}(A) = λ⁻ⁿ μ(λA)` for Borel `A`
  obtain ⟨Rl, hcar, hmult, horient⟩ := Submission.imrep_univ_smul_rescale_exists P n R lam hlam
  obtain ⟨haction, hmeasure⟩ :=
    Submission.imrep_smul_rescale_action_measure P n R Rl lam hlam hcar hmult horient
  -- Step 2: `R_λ` represents `C`: `C(ω) = C(ω') = R(ω') = R_λ(ω)` for `ω' = λ⁻ⁿ ω(λ⁻¹·)`
  have hRl : Rl.Represents C := by
    intro ω
    obtain ⟨ω', hω', hCω'⟩ := Submission.cone_current_apply_dilation_pullback P n C hC lam hlam ω
    rw [← hCω', hR ω', haction]
    congr 1
    funext y
    exact hω' y
  -- Step 3: the weight does not depend on the representation, so `μ_{R_λ} = μ` and
  -- `μ(A) = λ⁻ⁿ μ(λA)`
  have hA' := hmeasure A hA
  rw [Submission.imrep_measure_eq_of_represents_same_current P n univ C Rl R isOpen_univ hRl hR]
    at hA'
  -- Step 4: multiply by `λⁿ`, using `λⁿ λ⁻ⁿ = 1`
  have hpow : ENNReal.ofReal (lam ^ n) * ENNReal.ofReal (lam⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
      ENNReal.ofReal_one]
  rw [hA', ← mul_assoc, hpow, one_mul]
/-- **Integrability of the action integrand** (Simon Ch. 6, 3.1 (‡)).  For an integer
multiplicity triple `R = (C, θ, ξ)` in `U` and `ω ∈ 𝒟ⁿ(U)`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is
`Hⁿ⌞C`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal `Hⁿ`-a.e. on `C`, so
`|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by `B θ 1_{spt ω}` (`B` a bound for `‖ω‖`),
which is integrable because `spt ω` is a compact subset of `U` and `∫_{C ∩ K} θ dHⁿ < ∞` for
such `K`. -/
theorem Submission.regcomp_rim_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  set K : Set (Euclid P) := tsupport f
  /- Step 1: `ω` is continuous, bounded by some `B`, and vanishes off the compact set
  `K = spt ω ⊆ U`. -/
  have hcont : Continuous f := hsmooth.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  /- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ C`. -/
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hor⟩ := hx
    have hατ : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hor with h | h
    · rw [h]
      exact hατ
    · rw [h, norm_neg]
      exact hατ
  /- Step 3: the integrand is a.e. strongly measurable (evaluation is continuous). -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hev : AEStronglyMeasurable (fun x => R.orient x (f x)) (μHE[n].restrict R.carrier) :=
    happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable)
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (f x))
      (μHE[n].restrict R.carrier) := hθm.aestronglyMeasurable.mul hev
  /- Step 4: `B θ 1_K` is integrable, since `∫_{C ∩ K} θ dHⁿ < ∞`. -/
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => B * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul B
  /- Step 5: `|θ ⟨ω, ξ⟩| ≤ B θ 1_K` a.e. on `C`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (f x)‖ ≤ B * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (f x)).trans (hB x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring
/-- **Isolation of a ray** (steps 2–3 of the proof of `idtp_fons_odc_ray_orientation`): for a
finite set `F` of unit vectors, a unit vector `e` and `t₀ > 0`, some ball about `t₀e` meets the
open rays `{te' : t > 0}`, `e' ∈ F`, only inside `{te : t > 0}`.  The closed rays
`{se' : s ≥ 0}`, `e' ∈ F ∖ {e}`, are closed (`s ↦ se'` is an isometry of `ℝ`) and miss `t₀e`
(comparing norms in `t₀e = se'` gives `s = t₀`, hence `e' = e`); take a ball about `t₀e` avoiding
their finite union. -/
theorem Submission.idtp_fons_odc_ro_ray_isolation : ∀ (P : ℕ) (F : Finset (Euclid P)) (e : Euclid P) (t₀ : ℝ), (∀ e' ∈ F, ‖e'‖ = 1) → ‖e‖ = 1 → 0 < t₀ → ∃ δ : ℝ, 0 < δ ∧ ball (t₀ • e) δ ∩ (⋃ e' ∈ F, (fun t : ℝ => t • e') '' Ioi 0) ⊆ (fun t : ℝ => t • e) '' Ioi 0 := by
  classical
  intro P F e t₀ hF he ht₀
  -- `K`: the closed rays `{s • e' : s ≥ 0}` of the directions `e' ∈ F` other than `e`
  have hK : IsClosed (⋃ e' ∈ F.erase e, (fun t : ℝ => t • e') '' Ici 0) := by
    refine isClosed_biUnion_finset fun e' he' => ?_
    -- `s ↦ s • e'` is an isometry of `ℝ` (as `‖e'‖ = 1`), hence a closed embedding
    have hiso : Isometry fun t : ℝ => t • e' := Isometry.of_dist_eq fun s s' => by
      rw [dist_eq_norm, ← sub_smul, norm_smul, hF e' (Finset.mem_of_mem_erase he'), mul_one,
        Real.dist_eq, Real.norm_eq_abs]
    exact hiso.isClosedEmbedding.isClosedMap _ isClosed_Ici
  -- `t₀ • e ∉ K`: comparing norms in `s • e' = t₀ • e` gives `s = t₀`, hence `e' = e`
  have hx : t₀ • e ∉ ⋃ e' ∈ F.erase e, (fun t : ℝ => t • e') '' Ici 0 := by
    simp only [mem_iUnion, mem_image, mem_Ici, not_exists, not_and]
    intro e' he' s hs hse
    have hs' : s = t₀ := by
      have h := congrArg norm hse
      rwa [norm_smul, norm_smul, hF e' (Finset.mem_of_mem_erase he'), he, mul_one, mul_one,
        Real.norm_of_nonneg hs, Real.norm_of_nonneg ht₀.le] at h
    rw [hs'] at hse
    exact (Finset.mem_erase.mp he').1 (smul_right_injective _ ht₀.ne' hse)
  -- a ball about `t₀ • e` inside the open complement of `K`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hx
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨hyB, hyU⟩
  simp only [mem_iUnion, mem_image, mem_Ioi] at hyU
  obtain ⟨e'', he'', t, ht, rfl⟩ := hyU
  by_cases h : e'' = e
  · subst h
    exact ⟨t, ht, rfl⟩
  · exfalso
    refine hball hyB ?_
    simp only [mem_iUnion, mem_image, mem_Ici]
    exact ⟨e'', Finset.mem_erase.mpr ⟨h, he''⟩, t, ht.le, rfl⟩
/-- **Weighted line currents** (Simon 6.2.1).  For unit vectors `vₖ`, arbitrary parameter sets
`Iₖ ⊆ ℝ` and real weights `cₖ` (`k` in a finite type), `ω ↦ Σₖ cₖ ∫_{Iₖ} ω(pₖ + t vₖ)(vₖ) dt` is a
`1`-current in `ℝᴾ`.  Each `γₖ(t) = pₖ + t vₖ` is an isometry, hence a closed embedding, so each
integrand is continuous with compact support; a null sequence of test forms converges to `0`
uniformly on `ℝᴾ`, and dominated convergence with the indicator of the compact set `γₖ⁻¹(K)`
gives the sequential continuity of each piece. -/
theorem Submission.idtp_fons_odc_pc_line_current : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℝ), (∀ k, ‖v k‖ = 1) → ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1, ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ k, c k * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) := by
  intro P ι hι p v I c hv
  -- test forms converging to `0` in `𝒟¹(ℝᴾ)` converge to `0` uniformly on all of `ℝᴾ`
  have hunif : ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) 1, TestFormOnConverges ωs 0 →
      TendstoUniformly (fun j => (ωs j : DifferentialForm (Euclid P) 1)) 0 atTop := by
    intro ωs h
    obtain ⟨K, -, -, hsupp, -, hderiv⟩ := h
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hderiv 0) ε hε] with j hj x
    by_cases hx : x ∈ K
    · simpa [iteratedFDeriv_zero_eq_comp] using hj x hx
    · simpa [image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')] using hε
  -- integration of `1`-forms along one unit-speed line `t ↦ q + t w`, `t ∈ J`, is a current
  have hline : ∀ (q w : Euclid P) (J : Set ℝ), ‖w‖ = 1 →
      ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1,
        ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
          X ω = ∫ t in J, (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w) := by
    intro q w J hw
    have hγ : Isometry fun t : ℝ => q + t • w := by
      refine Isometry.of_dist_eq fun s t => ?_
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hw, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
    have hint (ω : TestFormOn (univ : Set (Euclid P)) 1) :
        Integrable fun t : ℝ => (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w) :=
      ((continuous_eval_const (F := Covector (Euclid P) 1) fun _ : Fin 1 => w).comp
        (ω.2.1.1.continuous.comp hγ.continuous)).integrable_of_hasCompactSupport
        ((ω.2.1.2.comp_isClosedEmbedding hγ.isClosedEmbedding).comp_left
          (g := fun α : Covector (Euclid P) 1 => α fun _ => w) rfl)
    refine ⟨⟨{ toFun := fun ω =>
                 ∫ t in J, (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w)
               map_add' := fun ω η => ?_
               map_smul' := fun a ω => ?_ }, fun ωs h => ?_⟩, fun ω => rfl⟩
    · simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
      exact integral_add (hint ω).restrict (hint η).restrict
    · simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul a _
    · -- dominated convergence, dominated by the indicator of the compact set `γ⁻¹(K)`
      have hu := hunif ωs h
      obtain ⟨K, hK, -, hsupp, -, -⟩ := h
      have hS : IsCompact ((fun t : ℝ => q + t • w) ⁻¹' K) :=
        hγ.isClosedEmbedding.isCompact_preimage hK
      have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
        (F := fun j t => (ωs j : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w))
        (f := fun _ => 0) (((fun t : ℝ => q + t • w) ⁻¹' K).indicator fun _ => 1)
        (Eventually.of_forall fun j => (hint (ωs j)).aestronglyMeasurable.restrict) ?_
        ((integrableOn_const (C := (1 : ℝ)) hS.measure_lt_top.ne).integrable_indicator
          hS.isClosed.measurableSet).restrict
        (Eventually.of_forall fun t => by
          simpa [Function.comp_def] using ((continuous_eval_const (F := Covector (Euclid P) 1)
            fun _ : Fin 1 => w).tendsto 0).comp (hu.tendsto_at (q + t • w)))
      · simpa using key
      · filter_upwards [Metric.tendstoUniformly_iff.1 hu 1 one_pos] with j hj
        refine Eventually.of_forall fun t => ?_
        by_cases ht : q + t • w ∈ K
        · rw [indicator_of_mem (show t ∈ (fun t : ℝ => q + t • w) ⁻¹' K from ht)]
          calc _ ≤ ‖(ωs j : DifferentialForm (Euclid P) 1) (q + t • w)‖ * ∏ _i : Fin 1, ‖w‖ :=
                ContinuousAlternatingMap.le_opNorm _ _
            _ ≤ 1 := by simpa [hw] using (hj (q + t • w)).le
        · rw [indicator_of_notMem (show t ∉ (fun t : ℝ => q + t • w) ⁻¹' K from ht),
            image_eq_zero_of_notMem_tsupport fun h' => ht (hsupp j h')]
          simp
  -- the weighted finite sum of the line currents
  choose X hX using fun k => hline (p k) (v k) (I k) (hv k)
  refine ⟨⟨∑ k, c k • (X k).toCurrent, fun ωs h => ?_⟩, fun ω => ?_⟩
  · simpa using tendsto_finsetSum Finset.univ fun k _ => ((X k).continuous' ωs h).const_mul (c k)
  · simp [← hX]
/-- **Simon Ch. 3, 1.4** (local flat model): a measurable `M` that coincides near `x` with the
affine plane `x + Q` has `Q` as approximate tangent space at `x`.  If `spt f ⊆ closedBall 0 R`
and `0 < ρ < r / R`, then for `y ∈ spt f` the point `x + ρ y` lies in `B_r(x)`, so
`y ∈ η_{x,ρ}(M) ↔ x + ρ y ∈ M ↔ ρ y ∈ Q ↔ y ∈ Q`; hence the blown-up integrals equal
`∫_Q f dHⁿ` for all small `ρ > 0`. -/
theorem Submission.idtp_fons_odc_pc_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r : ℝ), MeasurableSet M → Module.finrank ℝ Q = n → 0 < r → M ∩ ball x r = {y | y - x ∈ Q} ∩ ball x r → HasApproximateTangentSpaceAt n M x Q := by
  intro P n M x Q r hM hQ hr hloc
  refine ⟨hQ, fun f => ?_⟩
  -- `spt f ⊆ closedBall 0 R` with `R > 0`
  obtain ⟨R, hR0, hR⟩ :=
    f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Euclid P)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hR0)] with ρ ⟨hρ0, hρ⟩
  rw [lt_div_iff₀ hR0] at hρ
  -- `η_{x,ρ}(M) = {y | x + ρ y ∈ M}`
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' M =
      (fun y => x + ρ • y) ⁻¹' M := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ0.ne'] using hz
    · intro hy
      exact ⟨_, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ0.ne']⟩
  rw [himage, ← integral_indicator (hM.preimage (by fun_prop)),
    ← integral_indicator (Submodule.closed_of_finiteDimensional Q).measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ tsupport f
  · -- on `spt f`, `x + ρ y ∈ B_r(x)`, so `x + ρ y ∈ M ↔ ρ y ∈ Q ↔ y ∈ Q`
    have hball : x + ρ • y ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 (hR hy)) hρ0.le).trans_lt hρ
    have hiff : y ∈ (fun y => x + ρ • y) ⁻¹' M ↔ y ∈ Q := by
      have h := Set.ext_iff.1 hloc (x + ρ • y)
      simp only [mem_inter_iff, hball, and_true, mem_ofPred_eq, add_sub_cancel_left] at h
      show x + ρ • y ∈ M ↔ y ∈ Q
      rw [h, Q.smul_mem_iff hρ0.ne']
    by_cases hyQ : y ∈ Q
    · rw [indicator_of_mem hyQ, indicator_of_mem (hiff.2 hyQ)]
    · rw [indicator_of_notMem hyQ, indicator_of_notMem (mt hiff.1 hyQ)]
  · -- off `spt f` both integrands vanish
    have h0 : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    rw [indicator_apply_eq_zero.2 fun _ => h0, indicator_apply_eq_zero.2 fun _ => h0]
/-- **Near an isolated point of an open line piece, a union of line pieces is the line**
(parent step 3e).  Let `S_j = {p_j + t v_j : t ∈ I_j}` for `j` in a finite `ι`.  If
`‖v_k‖ = 1`, `I_k` is open, `S_k ⊆ M ⊆ ⋃_j S_j`, `x ∈ S_k` and `x ∉ closure S_j` for all
`j ≠ k`, then `M ∩ B_r(x) = (x + span{v_k}) ∩ B_r(x)` for some `r > 0`.  Write
`x = p_k + t₀ v_k` with `(t₀ − ε, t₀ + ε) ⊆ I_k`; finiteness of `ι` gives `δ > 0` with
`B_δ(x) ∩ S_j = ∅` for `j ≠ k`; take `r = min ε δ`.  A point `y = x + s v_k` of the ball has
`|s| = ‖y − x‖ < ε` (as `‖v_k‖ = 1`), so `y = p_k + (t₀ + s) v_k ∈ S_k ⊆ M`. -/
theorem Submission.idtp_fons_odc_pc_piece_locally_line : ∀ (P : ℕ) (ι : Type) [Finite ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (M : Set (Euclid P)) (k : ι) (x : Euclid P), ‖v k‖ = 1 → IsOpen (I k) → M ⊆ (⋃ j, (fun t : ℝ => p j + t • v j) '' I j) → (fun t : ℝ => p k + t • v k) '' I k ⊆ M → x ∈ (fun t : ℝ => p k + t • v k) '' I k → (∀ j, j ≠ k → x ∉ closure ((fun t : ℝ => p j + t • v j) '' I j)) → ∃ r : ℝ, 0 < r ∧ M ∩ ball x r = {y | y - x ∈ Submodule.span ℝ {v k}} ∩ ball x r := by
  intro P ι _ p v I M k x hv hI hM hkM hx hcl
  -- Step 1: `x = p_k + t₀ v_k` with `t₀ ∈ I_k`, and `(t₀ − ε, t₀ + ε) ⊆ I_k`
  obtain ⟨t₀, ht₀, hx⟩ := hx
  change p k + t₀ • v k = x at hx
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hI t₀ ht₀
  -- Step 2: as `ι` is finite, some `B_δ(x)` misses every piece `S_j` with `j ≠ k`
  obtain ⟨δ, hδ, hδS⟩ := Metric.eventually_nhds_iff.1 <| Filter.eventually_all.2 fun j =>
    Filter.eventually_imp_distrib_left.2 fun hj =>
      Filter.not_frequently.1 (mt mem_closure_iff_frequently.2 (hcl j hj))
  -- Step 3: `r := min ε δ`
  refine ⟨min ε δ, lt_min hε hδ, Set.ext fun y => ⟨fun hy => ⟨?_, hy.2⟩, fun hy => ⟨?_, hy.2⟩⟩⟩
  · -- (⊆): `y ∈ S_j` with `dist y x < δ` forces `j = k`, so `y − x = (t − t₀) v_k`
    obtain ⟨hyM, hyr⟩ := hy
    obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.1 (hM hyM)
    obtain rfl : j = k := by
      by_contra hj
      exact hδS ((Metric.mem_ball.1 hyr).trans_le (min_le_right _ _)) j hj ⟨t, ht, rfl⟩
    refine Submodule.mem_span_singleton.2 ⟨t - t₀, ?_⟩
    rw [← hx, sub_smul]
    dsimp only
    abel
  · -- (⊇): `y − x = s v_k` with `|s| = ‖y − x‖ < ε`, so `y = p_k + (t₀ + s) v_k ∈ S_k ⊆ M`
    obtain ⟨hy, hyr⟩ := hy
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hy
    have hsε : |s| < ε := by
      have h : ‖s • v k‖ < ε := by
        rw [hs, ← dist_eq_norm_sub]
        exact (Metric.mem_ball.1 hyr).trans_le (min_le_left _ _)
      rwa [norm_smul, hv, mul_one, Real.norm_eq_abs] at h
    refine hkM ⟨t₀ + s, hεI ?_, ?_⟩
    · rwa [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    · change p k + (t₀ + s) • v k = y
      rw [add_smul, ← add_assoc, hx, hs, add_sub_cancel]
/-- **Simon 7.3.3, proof of (2), formula (10)**: `ω₁ = 2`, and for `‖v‖ = 1` the line
`γ(t) = p + t v` is a measurable embedding with `H¹⌞γ(I) = γ_#(ℒ¹⌞I)` and `H¹(γ(I)) = ℒ¹(I)`
for every `I ⊆ ℝ`.  `γ` is an isometry, `μHE[1] = volume` on `ℝ` and `μHE[1]` is preserved by
isometries; the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`. -/
theorem Submission.idtp_fons_odc_line_hausdorff : unitBallVolume 1 = 2 ∧ ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → MeasurableEmbedding (fun t : ℝ => p + t • v) ∧ ∀ I : Set ℝ, (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => p + t • v) '' I) = Measure.map (fun t : ℝ => p + t • v) (volume.restrict I) ∧ (μHE[1] : Measure (Euclid P)) ((fun t : ℝ => p + t • v) '' I) = volume I := by
  -- `H¹ = ℒ¹` on `ℝ`, since `finrank ℝ ℝ = 1`
  have hR : (μHE[1] : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  -- `γ(t) = p + t v` is an isometry when `‖v‖ = 1`
  have hiso : ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → Isometry (fun t : ℝ => p + t • v) :=
    fun P p v hv => Isometry.of_dist_eq fun s t => by
      show dist (p + s • v) (p + t • v) = dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  refine ⟨?_, fun P p v hv => ?_⟩
  · -- `ω₁ = 2`: the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`
    set e : Euclid 1 := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have hball : ball (0 : Euclid 1) 1 = (fun t : ℝ => (0 : Euclid 1) + t • e) '' Ioo (-1) 1 := by
      ext x
      constructor
      · intro hx
        have hxe : x 0 • e = x := by
          ext i
          rw [Fin.fin_one_eq_zero i]
          simp [e]
        rw [mem_ball_zero_iff, ← hxe, norm_smul, he, mul_one, Real.norm_eq_abs] at hx
        exact ⟨x 0, abs_lt.mp hx, (zero_add _).trans hxe⟩
      · rintro ⟨t, ht, rfl⟩
        rw [mem_ball_zero_iff]
        show ‖(0 : Euclid 1) + t • e‖ < 1
        rw [zero_add, norm_smul, he, mul_one, Real.norm_eq_abs]
        exact abs_lt.mpr ht
    rw [unitBallVolume, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 1, hball,
      (hiso 1 0 e he).euclideanHausdorffMeasure_image, hR, Real.volume_Ioo]
    norm_num
  · have hemb : MeasurableEmbedding (fun t : ℝ => p + t • v) :=
      (hiso P p v hv).isClosedEmbedding.measurableEmbedding
    refine ⟨hemb, fun I => ⟨?_, ?_⟩⟩
    · -- `H¹⌞γ(I) = (H¹⌞range γ)⌞γ(I) = (γ_#ℒ¹)⌞γ(I) = γ_#(ℒ¹⌞γ⁻¹(γ(I))) = γ_#(ℒ¹⌞I)`
      rw [← Measure.restrict_restrict_of_subset (image_subset_range _ I),
        ← (hiso P p v hv).map_euclideanHausdorffMeasure, hR, hemb.restrict_map,
        hemb.injective.preimage_image]
    · rw [(hiso P p v hv).euclideanHausdorffMeasure_image, hR]
/-- **Simon, proof of 7.3.3(2), (10)** (finite rays, "open cones scale"): if `μ(λW) = λ μ(W)`
for every `λ > 0` and every open `W ⊆ ℝᴾ`, and `K` is an open cone (`cx ∈ K` whenever `c > 0`,
`x ∈ K`), then `μ(K ∩ B_r(0)) = r μ(K ∩ B_1(0))` for `r > 0`: `K ∩ B_r(0)` is the dilate
`r (K ∩ B_1(0))` of the open set `K ∩ B_1(0)` (`y ↦ r⁻¹y` and `x ↦ rx`, `|rx| = r|x|`). -/
theorem Submission.idtp_fons_odc_fr_cone_scaling : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → ∀ K : Set (Euclid P), IsOpen K → (∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K) → ∀ r : ℝ, 0 < r → μ (K ∩ ball 0 r) = ENNReal.ofReal r * μ (K ∩ ball 0 1) := by
  intro P μ hhom K hK hcone r hr
  -- `K ∩ B_r(0) = r (K ∩ B_1(0))`
  have hset : (fun x => r • x) '' (K ∩ ball 0 1) = K ∩ ball 0 r := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxK, hx1⟩, rfl⟩
      refine ⟨hcone r hr x hxK, ?_⟩
      rw [mem_ball_zero_iff] at hx1 ⊢
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      simpa using mul_lt_mul_of_pos_left hx1 hr
    · rintro ⟨hyK, hyr⟩
      refine ⟨r⁻¹ • y, ⟨hcone r⁻¹ (inv_pos.mpr hr) y hyK, ?_⟩, smul_inv_smul₀ hr.ne' y⟩
      rw [mem_ball_zero_iff] at hyr ⊢
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le, inv_mul_lt_one₀ hr]
      exact hyr
  -- homogeneity on the open set `K ∩ B_1(0)`
  rw [← hset]
  exact hhom r hr _ (hK.inter isOpen_ball)
/-- **Thin cones around separated unit directions are disjoint.**  If `|σ| = |σ'| = 1`,
`0 < ρ ≤ 1` and `2ρ ≤ |σ − σ'|`, then `⋃_{t>0} B(tσ, tρ)` and `⋃_{s>0} B(sσ', sρ)` are disjoint.
A common point `x` of `B(tσ, tρ)` and `B(sσ', sρ)` gives `|tσ − sσ'| < (t + s)ρ` by the triangle
inequality, whereas `|tσ − sσ'|² = (t − s)² + ts|σ − σ'|² ≥ (t − s)²ρ² + 4tsρ² = ((t + s)ρ)²`. -/
theorem Submission.idtp_fons_odc_fr_cone_disjoint : ∀ (P : ℕ) (σ σ' : Euclid P) (ρ : ℝ), ‖σ‖ = 1 → ‖σ'‖ = 1 → 0 < ρ → ρ ≤ 1 → 2 * ρ ≤ ‖σ - σ'‖ → Disjoint (⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) (⋃ (s : ℝ) (_ : 0 < s), ball (s • σ') (s * ρ)) := by
  intro P σ σ' ρ hσ hσ' hρ hρ1 hsep
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_iUnion, mem_ball] at hx hx'
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨s, hs, hxs⟩ := hx'
  -- triangle inequality through the common point `x`
  have hlt : ‖t • σ - s • σ'‖ < (t + s) * ρ := by
    calc ‖t • σ - s • σ'‖ = dist (t • σ) (s • σ') := (dist_eq_norm _ _).symm
      _ ≤ dist (t • σ) x + dist x (s • σ') := dist_triangle _ _ _
      _ = dist x (t • σ) + dist x (s • σ') := by rw [dist_comm (t • σ) x]
      _ < t * ρ + s * ρ := add_lt_add hxt hxs
      _ = (t + s) * ρ := by ring
  -- `|tσ − sσ'|² = (t − s)² + ts|σ − σ'|²` for unit `σ`, `σ'`
  have hid : ‖t • σ - s • σ'‖ ^ 2 = (t - s) ^ 2 + t * s * ‖σ - σ'‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, hσ, hσ', Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hs.le]
    ring
  -- hence `|tσ − sσ'|² ≥ (t − s)²ρ² + 4tsρ² = ((t + s)ρ)²`
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
  have hsep2 : 4 * ρ ^ 2 ≤ ‖σ - σ'‖ ^ 2 := by nlinarith
  have hge : ((t + s) * ρ) ^ 2 ≤ ‖t • σ - s • σ'‖ ^ 2 := by
    rw [hid]
    nlinarith [sq_nonneg (t - s), mul_pos ht hs]
  nlinarith [norm_nonneg (t • σ - s • σ')]
/-- A thin cone around a direction carrying density has mass at least `1/2` (Simon 7.3.3; the
finite-rays step for `1`-dimensional minimizing cones).  Let `μ(λW) = λ μ(W)` for `λ > 0` and open
`W`, `μ(B_1(0)) < ∞`, `|σ| = 1`, `0 < ρ < 1` and `ρ ≤ μ(B_ρ(σ))`.  The cone
`K = ⋃_{t>0} B(tσ, tρ)` is open and invariant under positive dilations, so
`μ(K ∩ B_r(0)) = r a` with `a = μ(K ∩ B_1(0)) ≤ μ(B_1(0)) < ∞`.  As `B_ρ(σ) ⊆ K ∩ B_{1+ρ}(0)` misses
`B_{1-ρ}(0)`, `ρ + (1 - ρ) a ≤ μ(B_ρ(σ)) + μ(K ∩ B_{1-ρ}(0)) ≤ μ(K ∩ B_{1+ρ}(0)) = (1 + ρ) a`, whence
`ρ ≤ 2ρa` and `1 ≤ 2a`. -/
theorem Submission.idtp_fons_odc_fr_cone_mass : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → μ (ball (0 : Euclid P) 1) ≠ ∞ → ∀ σ : Euclid P, ‖σ‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ENNReal.ofReal ρ ≤ μ (ball σ ρ) → 1 ≤ 2 * μ ((⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) ∩ ball 0 1) := by
  intro P μ hscale hfin σ hσ ρ hρ0 hρ1 hdens
  set K : Set (Euclid P) := ⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)
  -- `K` is an open cone: `|cx - (ct)σ| = c|x - tσ| < (ct)ρ`
  have hK : IsOpen K := isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_ball
  have hcone : ∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K := by
    intro c hc x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.1 hx
    refine mem_iUnion₂.2 ⟨c * t, mul_pos hc ht, ?_⟩
    rw [mem_ball, mul_smul, dist_smul₀, Real.norm_of_nonneg hc.le, mul_assoc]
    exact mul_lt_mul_of_pos_left hx hc
  -- `μ(K ∩ B_r(0)) = r μ(K ∩ B_1(0))` for `r > 0`
  have hscaleK : ∀ r : ℝ, 0 < r → μ (K ∩ ball 0 r) = ENNReal.ofReal r * μ (K ∩ ball 0 1) :=
    Submission.idtp_fons_odc_fr_cone_scaling P μ hscale K hK hcone
  -- `B_ρ(σ)` (the ball at `t = 1`) and `K ∩ B_{1-ρ}(0)` are disjoint subsets of `K ∩ B_{1+ρ}(0)`
  have hsub : ball σ ρ ∪ (K ∩ ball 0 (1 - ρ)) ⊆ K ∩ ball 0 (1 + ρ) := by
    refine union_subset (fun x hx => ⟨mem_iUnion₂.2 ⟨1, one_pos, by simpa using hx⟩, ?_⟩)
      (inter_subset_inter_right _ (ball_subset_ball (by linarith)))
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖(x - σ) + σ‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - σ‖ + ‖σ‖ := norm_add_le _ _
      _ < 1 + ρ := by rw [hσ]; linarith
  have hdisj : Disjoint (ball σ ρ) (K ∩ ball 0 (1 - ρ)) := by
    refine disjoint_left.2 fun x hx hx' => ?_
    rw [mem_ball, dist_eq_norm] at hx
    have h1 := mem_ball_zero_iff.1 hx'.2
    have h2 : ‖σ‖ ≤ ‖x - σ‖ + ‖x‖ := by
      rw [norm_sub_rev]
      calc ‖σ‖ = ‖(σ - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖σ - x‖ + ‖x‖ := norm_add_le _ _
    rw [hσ] at h2
    linarith
  -- `ρ + (1 - ρ) a ≤ μ(B_ρ(σ)) + μ(K ∩ B_{1-ρ}(0)) ≤ μ(K ∩ B_{1+ρ}(0)) = (1 + ρ) a`
  have key := measure_mono (μ := μ) hsub
  rw [measure_union hdisj (hK.inter isOpen_ball).measurableSet, hscaleK (1 - ρ) (by linarith),
    hscaleK (1 + ρ) (by linarith)] at key
  have key' := (add_le_add hdens le_rfl).trans key
  -- everything is finite, as `a ≤ μ(B_1(0)) < ∞`: pass to real numbers
  have ha : μ (K ∩ ball 0 1) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  rw [← ENNReal.ofReal_toReal ha] at key' ⊢
  set a := (μ (K ∩ ball 0 1)).toReal
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add hρ0.le (by nlinarith), ENNReal.ofReal_le_ofReal_iff (by positivity)]
    at key'
  -- `ρ ≤ 2ρa` and `ρ > 0` give `1 ≤ 2a`
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **Finitely many rays: counting bound.**  Let `μ` be a measure on `ℝᴾ` with `μ(λW) = λ μ(W)`
for `λ > 0` and open `W`, and `μ(B_1(0)) < ∞`.  If `T` is a finite set of unit vectors and, for
each `σ ∈ T`, `ρ ≤ μ(B_ρ(σ))` for all small `ρ > 0`, then `#T ≤ 2 μ(B_1(0))`.  Fix one
`ρ ∈ (0, 1)` with `ρ ≤ μ(B_ρ(σ))` for every `σ ∈ T` and `2ρ ≤ |σ − σ'|` for distinct
`σ, σ' ∈ T`.  The sets `C_σ = K_ρ(σ) ∩ B_1(0)`, `K_ρ(σ) = ⋃_{t > 0} B_{tρ}(tσ)`, are open,
pairwise disjoint (`idtp_fons_odc_fr_cone_disjoint`) and satisfy `1 ≤ 2 μ(C_σ)`
(`idtp_fons_odc_fr_cone_mass`), so `#T ≤ Σ_σ 2 μ(C_σ) = 2 μ(⋃_σ C_σ) ≤ 2 μ(B_1(0))`. -/
theorem Submission.idtp_fons_odc_fr_card_le : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → μ (ball (0 : Euclid P) 1) ≠ ∞ → ∀ T : Finset (Euclid P), (∀ σ ∈ T, ‖σ‖ = 1) → (∀ σ ∈ T, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ μ (ball σ ρ)) → (T.card : ℝ≥0∞) ≤ 2 * μ (ball 0 1) := by
  intro P μ hscale hfin T hT hdens
  -- step 1: the finitely many density bounds hold together for all small `ρ`
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ σ ∈ T, ENNReal.ofReal ρ ≤ μ (ball σ ρ) :=
    (eventually_all_finset T).2 hdens
  -- step 2: eventually `2ρ ≤ |σ − σ'|` for all distinct `σ, σ' ∈ T`
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ σ ∈ T, ∀ σ' ∈ T, σ ≠ σ' → 2 * ρ ≤ ‖σ - σ'‖ := by
    refine (eventually_all_finset T).2 fun σ _ => (eventually_all_finset T).2 fun σ' _ => ?_
    rcases eq_or_ne σ σ' with h | h
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (norm_pos_iff.2 (sub_ne_zero.2 h)))]
        with ρ hρ _
      linarith [hρ.2]
  -- step 3: `𝓝[>] 0` is proper, so a single `ρ ∈ (0, 1)` satisfies all of these
  obtain ⟨ρ, h1ρ, h2ρ, hρ⟩ := (h1.and (h2.and (Ioo_mem_nhdsGT zero_lt_one))).exists
  -- step 4: `C_σ = K_ρ(σ) ∩ B_1(0)` is open, hence Borel, and lies in `B_1(0)`
  set C : Euclid P → Set (Euclid P) :=
    fun σ => (⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) ∩ ball 0 1
  have hmeas : ∀ σ ∈ T, MeasurableSet (C σ) := fun σ _ =>
    ((isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_ball).inter isOpen_ball).measurableSet
  -- step 5: the `C_σ` are pairwise disjoint (`cone_disjoint`)
  have hdisj : (T : Set (Euclid P)).PairwiseDisjoint C := by
    intro σ hσ σ' hσ' hne
    exact (Submission.idtp_fons_odc_fr_cone_disjoint P σ σ' ρ (hT σ hσ) (hT σ' hσ') hρ.1 hρ.2.le
      (h2ρ σ hσ σ' hσ' hne)).mono inter_subset_left inter_subset_left
  -- steps 6–7: `1 ≤ 2 μ(C_σ)` (`cone_mass`), finite additivity and monotonicity
  calc (T.card : ℝ≥0∞) = ∑ σ ∈ T, 1 := by simp
    _ ≤ ∑ σ ∈ T, 2 * μ (C σ) := Finset.sum_le_sum fun σ hσ =>
        Submission.idtp_fons_odc_fr_cone_mass P μ hscale hfin σ (hT σ hσ) ρ hρ.1 hρ.2 (h1ρ σ hσ)
    _ = 2 * μ (⋃ σ ∈ T, C σ) := by rw [measure_biUnion_finset hdisj hmeas, Finset.mul_sum]
    _ ≤ 2 * μ (ball 0 1) := by
        gcongr
        exact iUnion₂_subset fun σ _ => inter_subset_right
/-- A measure on `ℝᴾ` that is `1`-homogeneous on open sets (`μ(λW) = λ μ(W)`, `λ > 0`) and finite
on `B₁(0)` has no atom at the origin.  For `r > 0`, `r • B₁(0) = B_r(0)` (`smul_ball`), so
`μ{0} ≤ μ(B_r(0)) = r μ(B₁(0))`; the right side tends to `0` as `r ↓ 0` because `μ(B₁(0)) < ∞`. -/
theorem Submission.idtp_fons_odc_fr_origin_null : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → μ (ball (0 : Euclid P) 1) ≠ ∞ → μ {0} = 0 := by
  intro P μ hscale hfin
  have h : Tendsto (fun r : ℝ => ENNReal.ofReal r * μ (ball (0 : Euclid P) 1)) (𝓝[>] 0)
      (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
        nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hfin)
  refine le_zero_iff.1 (ge_of_tendsto h ?_)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  calc μ {0} ≤ μ (ball (0 : Euclid P) r) :=
        measure_mono (singleton_subset_iff.2 (mem_ball_self hr))
    _ = ENNReal.ofReal r * μ (ball (0 : Euclid P) 1) := by
      rw [← hscale r hr _ isOpen_ball, image_smul, smul_ball hr.ne', smul_zero,
        Real.norm_of_nonneg hr.le, mul_one]

/-- **Simon, proof of 7.3.3, (10)** (finite rays).  Let `μ` on `ℝᴾ` be finite on compact sets,
`1`-homogeneous on open sets (`μ(λW) = λ μ(W)`, `λ > 0`), with `ρ ≤ μ(B_ρ(x))` for small `ρ > 0` at
every `x ∈ spt μ`.  Then `μ` is carried by finitely many open rays `{te : t > 0}`, `|e| = 1`.
A finite set of unit vectors of `spt μ` has at most `2 μ(B₁(0)) < ∞` elements, so these unit
vectors form a finite set `F`.  If `x ≠ 0` lies on no ray of `F`, then `x̂ = |x|⁻¹x ∉ spt μ`, and
`μ(B(x, |x|ε)) = |x| μ(B(x̂, ε)) = 0` for some `ε > 0`, so `x ∉ spt μ`.  Hence the complement of
the rays lies in `{0} ∪ (ℝᴾ ∖ spt μ)`, where `μ{0} = 0` and `ℝᴾ ∖ spt μ` is locally null. -/
theorem Submission.idtp_fons_odc_finite_rays : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → (∀ x : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ μ (ball x ρ)) → ∃ F : Finset (Euclid P), (∀ e ∈ F, ‖e‖ = 1) ∧ μ ((⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 := by
  intro P μ hfin hscale hdens
  -- `μ(B₁(0)) ≤ μ(closedBall(0, 1)) < ∞`
  have hB : μ (ball (0 : Euclid P) 1) ≠ ∞ :=
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall 0 1)) (measure_mono ball_subset_closedBall)
  -- `S = spt μ`
  set S : Set (Euclid P) := {x | ∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0} with hS
  -- the unit vectors of `spt μ` form a finite set: `n > 2 μ(B₁(0))` of them would contradict
  -- the cardinality bound
  have hU : {σ : Euclid P | ‖σ‖ = 1 ∧ σ ∈ S}.Finite := by
    by_contra h
    have h2 : (2 : ℝ≥0∞) * μ (ball 0 1) ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h2
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq h n
    have hT := Submission.idtp_fons_odc_fr_card_le P μ hscale hB T (fun σ hσ => (hTsub hσ).1)
      fun σ hσ => hdens σ (hTsub hσ).2
    rw [hTcard] at hT
    exact lt_irrefl _ (hT.trans_lt hn)
  refine ⟨hU.toFinset, fun e he => (hU.mem_toFinset.1 he).1, ?_⟩
  -- a point `x ≠ 0` on none of the rays lies outside `spt μ`
  have hsub : (⋃ e ∈ hU.toFinset, (fun t : ℝ => t • e) '' Ioi 0)ᶜ ⊆ {0} ∪ Sᶜ := by
    intro x hx
    by_contra hx'
    simp only [mem_union, mem_singleton_iff, mem_compl_iff, not_or, not_not] at hx'
    obtain ⟨hx0, hxS⟩ := hx'
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine hx (mem_iUnion₂.2 ⟨‖x‖⁻¹ • x, hU.mem_toFinset.2 ⟨?_, ?_⟩, ‖x‖, hn, ?_⟩)
    · rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hn).le, inv_mul_cancel₀ hn.ne']
    · -- `μ(B(x̂, ε)) = |x|⁻¹ μ(B(x, |x|ε))`: homogeneity on the open ball `B(x, |x|ε)`
      intro ε hε
      have hball : μ (ball (‖x‖⁻¹ • x) (‖x‖⁻¹ * (‖x‖ * ε))) =
          ENNReal.ofReal ‖x‖⁻¹ * μ (ball x (‖x‖ * ε)) := by
        rw [← hscale _ (inv_pos.2 hn) _ isOpen_ball, image_smul, smul_ball (inv_ne_zero hn.ne'),
          Real.norm_of_nonneg (inv_pos.2 hn).le]
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] at hball
      rw [hball]
      exact mul_ne_zero (ENNReal.ofReal_pos.2 (inv_pos.2 hn)).ne' (hxS _ (mul_pos hn hε))
    · exact smul_inv_smul₀ hn.ne' x
  -- `μ{0} = 0`, and `ℝᴾ ∖ spt μ` is null since each of its points has a null neighbourhood
  refine measure_mono_null hsub
    (measure_union_null (Submission.idtp_fons_odc_fr_origin_null P μ hscale hB) ?_)
  refine measure_null_of_locally_null _ fun x hx => ?_
  simp only [hS, mem_compl_iff, mem_ofPred_eq, not_forall, not_not, exists_prop] at hx
  obtain ⟨ε, hε, h0⟩ := hx
  exact ⟨ball x ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε), h0⟩

/-- **Simon 7.3.3, proof of (2), formula (10)**, along one ray: let `(M, θ, ξ)` be a
`1`-dimensional integer multiplicity triple in `ℝᴾ`, `‖e‖ = 1`, `γ(t) = t e`, and `ξ = ±e`
`H¹`-a.e. on `M ∩ γ(0, ∞)`.  With `β = ⟪e, ·⟫`, `g(t) = 1_M(t e) θ(t e) ⟨β, ξ(t e)⟩` is locally
integrable, a.e. integer valued on `(0, ∞)` (as `⟨β, ±e⟩ = ±1`), and
`∫_{M ∩ γ(0, ∞)} θ ⟨ω, ξ⟩ dH¹ = ∫₀^∞ g(t) ω(t e)(e) dt` for every test `1`-form `ω`: a.e. on
`M ∩ γ(0, ∞)`, `⟨ω, ξ⟩ = ⟨β, ξ⟩ ω(e)`, and `γ` carries `ℒ¹⌞I` to `H¹⌞γ(I)`. -/
theorem Submission.idtp_fons_odc_ra_single_ray : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (e : Euclid P), ‖e‖ = 1 → (∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)), R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)) → ∃ g : ℝ → ℝ, LocallyIntegrableOn g (Ioi 0) ∧ (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g t = k) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] = ∫ t in Ioi (0 : ℝ), g t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  intro P R e he hξ
  have hM := R.measurableSet_carrier
  -- `γ(t) = t e` is a measurable embedding with `H¹⌞γ(I) = γ_#(ℒ¹⌞I)`
  obtain ⟨hemb, hmap⟩ := Submission.idtp_fons_odc_line_hausdorff.2 P 0 e he
  simp only [zero_add] at hemb hmap
  replace hmap := fun I => (hmap I).1
  -- the covector `β = ⟪e, ·⟫` has `β(e) = ‖e‖² = 1`
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) 1, β (fun _ => e) = 1 :=
    ⟨ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e), by
      rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, innerSL_apply_apply,
        real_inner_self_eq_norm_sq, he, one_pow]⟩
  -- for `ξ = ±e`: `⟨β, ξ⟩ = ±1` and `⟨α, ξ⟩ = ⟨β, ξ⟩ α(e)`
  have hsign : ∀ ξ : MultiVector P 1,
      (ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨
        ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)) →
      (ξ β = 1 ∨ ξ β = -1) ∧ ∀ α : Covector (Euclid P) 1, ξ α = ξ β * α (fun _ => e) := by
    rintro ξ (rfl | rfl) <;> simp [hβ]
  refine ⟨fun t => R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e), ?_, ?_,
    fun ω => ?_⟩
  · -- on a compact `k`, `g` is integrable since `θ ⟨β, ξ⟩` is `H¹`-integrable on `M ∩ γ(k)`
    refine (locallyIntegrable_iff.2 fun k hk => ?_).locallyIntegrableOn _
    have h1 : Integrable (R.carrier.indicator fun x => (R.mult x : ℝ) * R.orient x β)
        ((μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' k)) := by
      rw [integrable_indicator_iff hM, IntegrableOn, Measure.restrict_restrict hM]
      exact Submission.lcn_mult_mul_orient_apply_integrableOn P 1 univ _ R
        (hk.image (by fun_prop)) (subset_univ _) β
    rw [hmap] at h1
    exact hemb.integrable_map_iff.1 h1
  · -- for a.e. `t > 0`, `g(t) = ±θ(t e)` if `t e ∈ M` (`ξ(t e) = ±e`) and `g(t) = 0` otherwise
    rw [← Measure.restrict_restrict hM, ae_restrict_iff' hM, hmap, hemb.ae_map_iff] at hξ
    filter_upwards [hξ] with t ht
    by_cases hx : t • e ∈ R.carrier
    · rw [indicator_of_mem hx]
      rcases (hsign _ (ht hx)).1 with h1 | h1
      · exact ⟨R.mult (t • e), by rw [h1, mul_one, Int.cast_natCast]⟩
      · exact ⟨-(R.mult (t • e) : ℤ), by rw [h1, mul_neg_one, Int.cast_neg, Int.cast_natCast]⟩
    · exact ⟨0, by rw [indicator_of_notMem hx, Int.cast_zero]⟩
  · -- `θ ⟨ω, ξ⟩ = θ ⟨β, ξ⟩ ω(e)` a.e. on `M ∩ γ(0, ∞)`; extend by `0` off `M`, pull back by `γ`
    calc ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1]
        = ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x β *
            (ω : DifferentialForm (Euclid P) 1) x (fun _ => e) ∂μHE[1] := by
          refine integral_congr_ae ?_
          filter_upwards [hξ] with x hx
          rw [(hsign _ hx).2 ((ω : DifferentialForm (Euclid P) 1) x), mul_assoc]
      _ = ∫ x in (fun t : ℝ => t • e) '' Ioi 0,
            R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) x *
              (ω : DifferentialForm (Euclid P) 1) x (fun _ => e) ∂μHE[1] := by
          rw [inter_comm, ← setIntegral_indicator hM]
          congr 1
          funext x
          exact Set.indicator_mul_left _ _ _
      _ = ∫ t in Ioi (0 : ℝ), R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e) *
            (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
          rw [hmap, hemb.integral_map]

/-- **Splitting the action along finitely many rays** (Simon Ch. 6, 3.1 (‡)).  Let
`R = (M, θ, ξ)` be a `1`-dimensional integer multiplicity triple in `ℝᴾ` and `F` a finite set of
unit vectors such that `H¹`-almost all of `M` lies on the open rays `ray(e) = {t e : t > 0}`,
`e ∈ F`.  Then `τ(M, θ, ξ)(ω) = Σ_{e ∈ F} ∫_{M ∩ ray(e)} θ ⟨ω, ξ⟩ dH¹` for every `ω ∈ 𝒟¹(ℝᴾ)`:
the pieces `M ∩ ray(e)` are Borel (`t ↦ t e` is an isometric, hence measurable, embedding of
`ℝ`), pairwise disjoint (rays of distinct unit vectors do not meet), their union is `M` up to an
`H¹`-null set, and the integrand is `H¹⌞M`-integrable. -/
theorem Submission.idtp_fons_odc_ra_action_split : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ e ∈ F, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] := by
  intro P R F hF hnull ω
  /- Step 1: the integrand `θ ⟨ω, ξ⟩` is `H¹`-integrable on `M`, hence on each `M ∩ ray(e)`. -/
  have hint : IntegrableOn
      (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x))
      R.carrier μHE[1] :=
    Submission.regcomp_rim_action_integrable P 1 univ R ω
  /- Step 2: for a unit vector `e`, `t ↦ t • e` is an isometry `ℝ → ℝᴾ`, hence a closed and
  measurable embedding, so the ray `ray(e) = (0, ∞) • e` is Borel. -/
  have hray : ∀ e ∈ F, MeasurableSet ((fun t : ℝ => t • e) '' Ioi 0) := by
    intro e he
    have hiso : Isometry (fun t : ℝ => t • e) := Isometry.of_dist_eq fun s t => by
      show dist (s • e) (t • e) = dist s t
      rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, hF e he, mul_one]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioi
  /- Step 3: rays of distinct unit vectors are disjoint: `s • e' = t • e` with `s, t > 0` gives
  `s = ‖s • e'‖ = ‖t • e‖ = t`, and then `e' = e`. -/
  have hdisj : (F : Set (Euclid P)).Pairwise
      (Disjoint on fun e => R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0) := by
    intro e he e' he' hne
    refine Set.disjoint_left.2 ?_
    rintro x ⟨-, t, ht, rfl⟩ ⟨-, s, hs, hst⟩
    have hst' : s • e' = t • e := hst
    have hts : s = t := by
      have h := congrArg norm hst'
      rwa [norm_smul, norm_smul, hF e he, hF e' he', mul_one, mul_one,
        Real.norm_of_nonneg (mem_Ioi.1 hs).le, Real.norm_of_nonneg (mem_Ioi.1 ht).le] at h
    subst hts
    exact hne (smul_right_injective (Euclid P) (mem_Ioi.1 hs).ne' hst').symm
  /- Step 4: finite additivity over the disjoint measurable pieces `M ∩ ray(e)`, `e ∈ F`. -/
  have hsplit : ∫ x in ⋃ e ∈ F, R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
      (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] =
      ∑ e ∈ F, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] :=
    integral_biUnion_finset F (fun e he => R.measurableSet_carrier.inter (hray e he)) hdisj
      fun e _ => hint.mono_set inter_subset_left
  /- Step 5: `M` and `⋃_{e ∈ F} M ∩ ray(e)` differ by a subset of the `H¹`-null set
  `M ∖ ⋃_{e ∈ F} ray(e)`. -/
  have hae : R.carrier =ᵐ[μHE[1]] ⋃ e ∈ F, R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0 := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ hnull, ?_⟩
    · rintro x ⟨hxM, hxA⟩
      refine ⟨hxM, ?_⟩
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hxA ⊢
      exact fun e he hxe => hxA e he ⟨hxM, hxe⟩
    · rw [Set.sdiff_eq_empty.2 (iUnion₂_subset fun e _ => inter_subset_left), measure_empty]
  /- Step 6: `R.action ω = ∫_M f = ∫_{⋃ M ∩ ray(e)} f = Σ_e ∫_{M ∩ ray(e)} f`. -/
  rw [IMRep.action, setIntegral_congr_set hae, hsplit]
/-- **Simon 7.3.3, proof of (2), step 4a**: for `‖u‖ = 1` and `f ≥ 0` continuous with compact
support and `f(u) > 0`, `∫_{ℝu} f dH¹ > 0`.  By `idtp_fons_odc_line_hausdorff` (`p = 0`, `v = u`,
`I = ℝ`), `H¹⌞ℝu = γ_#ℒ¹` for `γ(t) = t u`, so the integral is `∫_ℝ f(t u) dt`; `γ` is an
isometry, so `t ↦ f(t u)` is continuous, nonnegative, compactly supported and positive at `1`. -/
theorem Submission.idtp_fons_odc_ro_line_integral_pos : ∀ (P : ℕ) (u : Euclid P) (f : Euclid P → ℝ), ‖u‖ = 1 → Continuous f → HasCompactSupport f → (∀ y, 0 ≤ f y) → 0 < f u → 0 < ∫ y in (Submodule.span ℝ {u} : Set (Euclid P)), f y ∂(μHE[1] : Measure (Euclid P)) := by
  intro P u f hu hf hfc hf0 hfu
  obtain ⟨hemb, hline⟩ := Submission.idtp_fons_odc_line_hausdorff.2 P 0 u hu
  -- `γ(t) = 0 + t u` is an isometry
  have hiso : Isometry (fun t : ℝ => (0 : Euclid P) + t • u) :=
    Isometry.of_dist_eq fun s t => by
      show dist ((0 : Euclid P) + s • u) (0 + t • u) = dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  -- the line `ℝu` is `γ(ℝ)`
  have hspan : (Submodule.span ℝ {u} : Set (Euclid P)) =
      (fun t : ℝ => (0 : Euclid P) + t • u) '' univ := by
    ext y
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, image_univ, mem_range, zero_add]
  -- `∫_{ℝu} f dH¹ = ∫_ℝ f(γ t) dt`
  rw [hspan, (hline univ).1, Measure.restrict_univ, hemb.integral_map]
  exact (hf.comp hiso.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hfc.comp_isClosedEmbedding hiso.isClosedEmbedding) (fun t => hf0 _) (x := 1)
    (by simpa using hfu.ne')

/-- **Simon Ch. 3, Definition 1.4** (step 4 of `idtp_fons_odc_ray_orientation`): if near `x` the
set `M` lies on the line `x + ℝv` up to an `H¹`-null set `N`, every `1`-dimensional approximate
tangent space `Q` of `M` at `x` is `ℝv`.  As `finrank Q = 1 = finrank ℝv` it suffices to exclude a
unit vector `u ∈ Q \ ℝv`, for which `Q = ℝu`.  With `d = dist(u, ℝv) > 0` and the bump
`f = max(0, d/2 - |· - u|) ∈ C_c`, `line_integral_pos` gives `∫_Q f dH¹ > 0`.  But for
`0 < ρ < δ/(1 + d)` every `y ∈ η_{x,ρ}(M)` with `f(y) ≠ 0` has `x + ρy ∈ B_δ(x)` off the line,
so `y` lies in the `H¹`-null set `η_{x,ρ}(N)` (`η_{x,ρ}` is Lipschitz) and
`∫_{η_{x,ρ}(M)} f dH¹ = 0`; uniqueness of limits as `ρ ↓ 0` then forces `∫_Q f dH¹ = 0`. -/
theorem Submission.idtp_fons_odc_ro_tangent_line : ∀ (P : ℕ) (M N : Set (Euclid P)) (x v : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), v ≠ 0 → 0 < δ → (μHE[1] : Measure (Euclid P)) N = 0 → M ∩ ball x δ ⊆ range (fun s : ℝ => x + s • v) ∪ N → HasApproximateTangentSpaceAt 1 M x Q → Q = Submodule.span ℝ {v} := by
  intro P M N x v δ Q hv hδ hN hloc hQ
  -- `η_{x,ρ}(S) = {y | x + ρ y ∈ S}` for `ρ ≠ 0`
  have himage : ∀ (S : Set (Euclid P)) {ρ : ℝ}, ρ ≠ 0 →
      Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S = (fun y => x + ρ • y) ⁻¹' S := by
    intro S ρ hρ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ] using hz
    · intro hy
      exact ⟨_, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ]⟩
  -- `η_{x,ρ}` is `|ρ⁻¹|`-Lipschitz, so `η_{x,ρ}(N)` is `H¹`-null
  have hnull : ∀ ρ : ℝ,
      (μHE[1] : Measure (Euclid P)) (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' N) = 0 := by
    intro ρ
    have hlip : LipschitzWith ‖ρ⁻¹‖₊ (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dist_smul₀, dist_sub_right,
          coe_nnnorm, le_refl]
    refine nonpos_iff_eq_zero.1 ?_
    calc _ ≤ (‖ρ⁻¹‖₊ : ℝ≥0∞) ^ 1 * μHE[1] N :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn 1
            hlip.lipschitzOnWith
      _ = 0 := by rw [hN, mul_zero]
  -- `x + ρ y` lies on the line `x + ℝv` iff `y ∈ ℝv` (`ρ ≠ 0`)
  have hline : ∀ (y : Euclid P) {ρ : ℝ}, ρ ≠ 0 →
      (x + ρ • y ∈ range (fun s : ℝ => x + s • v) ↔ y ∈ Submodule.span ℝ {v}) := by
    intro y ρ hρ
    simp only [mem_range, add_right_inj, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨ρ⁻¹ * s, by rw [mul_smul, hs, smul_smul, inv_mul_cancel₀ hρ, one_smul]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ρ * a, mul_smul _ _ _⟩
  -- `finrank Q = 1 = finrank ℝv`, so it suffices to show `Q ≤ ℝv`
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hQ.1, finrank_span_singleton hv])
  by_contra hQL
  -- a unit vector `u ∈ Q \ ℝv`; then `Q = ℝu`
  obtain ⟨u, huQ, huL, hu⟩ : ∃ u ∈ Q, u ∉ Submodule.span ℝ {v} ∧ ‖u‖ = 1 := by
    obtain ⟨w, hwQ, hwL⟩ := IsConcreteLE.not_le_iff_exists.1 hQL
    have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 fun h => hwL (h ▸ Submodule.zero_mem _)
    refine ⟨‖w‖⁻¹ • w, Q.smul_mem _ hwQ, fun h => hwL ?_, ?_⟩
    · simpa [smul_smul, mul_inv_cancel₀ hw] using (Submodule.span ℝ {v}).smul_mem ‖w‖ h
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw]
  have hspan : Submodule.span ℝ {u} = Q :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 huQ)
      (by rw [hQ.1, finrank_span_singleton (by rintro rfl; simp at hu)])
  -- `d = dist(u, ℝv) > 0` and the bump `f = max(0, d/2 - |· - u|)`
  obtain ⟨d, hdu, hd⟩ : ∃ d, d = infDist u (Submodule.span ℝ {v} : Set (Euclid P)) ∧ 0 < d :=
    ⟨_, rfl, ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos
      ⟨0, Submodule.zero_mem _⟩).1 huL⟩
  obtain ⟨f, hf⟩ : ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∀ y, f y = max 0 (d / 2 - ‖y - u‖) :=
    ⟨⟨⟨fun y => max 0 (d / 2 - ‖y - u‖), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall u (d / 2)) fun y hy => max_eq_left (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy; linarith)⟩, fun y => rfl⟩
  -- by `line_integral_pos`, the limit `∫_Q f dH¹ = ∫_{ℝu} f dH¹` is positive
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), f y ∂(μHE[1] : Measure (Euclid P)) := by
    rw [← hspan]
    refine Submission.idtp_fons_odc_ro_line_integral_pos P u f hu (map_continuous f)
      f.hasCompactSupport (fun y => by rw [hf]; exact le_max_left _ _) ?_
    rw [hf, sub_self, norm_zero, sub_zero]
    exact lt_max_of_lt_right (half_pos hd)
  -- for `0 < ρ < δ / (1 + d)`, `f = 0` on `η_{x,ρ}(M)` off the null set `η_{x,ρ}(N)`
  have hzero : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' M,
      f y ∂(μHE[1] : Measure (Euclid P)) = 0 := by
    have h1d : (0 : ℝ) < 1 + d := by linarith
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ h1d)] with ρ ⟨hρ0, hρ⟩
    rw [lt_div_iff₀ h1d] at hρ
    refine setIntegral_eq_zero_of_ae_eq_zero (ae_iff.2 (measure_mono_null (fun y hy => ?_)
      (hnull ρ)))
    simp only [mem_ofPred_eq, not_imp] at hy
    rw [himage _ hρ0.ne'] at hy ⊢
    obtain ⟨hyM, hfy⟩ := hy
    have hyu : ‖y - u‖ < d / 2 := by
      by_contra h
      exact hfy (by rw [hf]; exact max_eq_left (by linarith [not_lt.1 h]))
    have hball : x + ρ • y ∈ ball x δ := by
      have hy1 : ‖y‖ < 1 + d := by linarith [norm_sub_norm_le y u]
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      exact (mul_lt_mul_of_pos_left hy1 hρ0).trans hρ
    rcases hloc (show x + ρ • y ∈ M ∩ ball x δ from ⟨hyM, hball⟩) with hyl | hyN
    · exfalso
      have h := infDist_le_dist_of_mem (x := u) (SetLike.mem_coe.2 ((hline y hρ0.ne').1 hyl))
      rw [← hdu, dist_comm, dist_eq_norm] at h
      linarith
    · exact hyN
  -- uniqueness of the limit as `ρ ↓ 0` contradicts `∫_Q f dH¹ > 0`
  exact hpos.ne' (tendsto_nhds_unique (hQ.2 f)
    (tendsto_const_nhds.congr' (hzero.mono fun ρ h => h.symm)))
/-- A unit orientation of the line `ℝe`, `‖e‖ = 1`, is `±e`, i.e. `ξ = ±(α ↦ α(e))` (Simon 6.1.1,
6.2.2 with `n = 1`).  An orthonormal `τ : Fin 1 → ℝᴾ` spanning `ℝe` has `τ₀ = c e` with
`|c| = ‖τ₀‖ = 1`, and `α(τ) = c α(e)` by multilinearity, so `⟨α, ξ⟩ = ±α(τ) = ±α(e)`. -/
theorem Submission.idtp_fons_odc_ro_line_orientation : ∀ (P : ℕ) (e : Euclid P) (ξ : MultiVector P 1), ‖e‖ = 1 → IsUnitOrientationOf ξ (Submodule.span ℝ {e}) → ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) := by
  intro P e ξ he ⟨τ, hτ, hspan, hξ⟩
  -- `τ 0 ∈ span (range τ) = ℝe`, so `τ 0 = c • e`
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.subset_span (Set.mem_range_self 0) : τ 0 ∈ Submodule.span ℝ {e})
  -- `1 = ‖τ 0‖ = |c| ‖e‖ = |c|`, so `c = ±1`
  have hc1 : |c| = 1 := by
    have h := hτ.1 0
    rwa [← hc, norm_smul, he, mul_one, Real.norm_eq_abs] at h
  -- `Fin 1 = {0}`, so `α τ = α (fun _ => c • e) = c * α (fun _ => e)`
  have hev : ∀ α : Covector (Euclid P) 1, α τ = c * α (fun _ => e) := by
    intro α
    have hτc : τ = fun _ => c • e := funext fun i => by rw [Subsingleton.elim i 0, hc]
    rw [hτc, α.map_smul_univ (fun _ => c) (fun _ => e)]
    simp
  rcases (abs_eq zero_le_one).mp hc1 with rfl | rfl <;> rcases hξ with hξ | hξ
  · exact Or.inl (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, one_mul, ContinuousAlternatingMap.apply_apply])
  · exact Or.inr (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, one_mul, neg_apply, ContinuousAlternatingMap.apply_apply])
  · exact Or.inr (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, neg_one_mul, neg_apply, ContinuousAlternatingMap.apply_apply])
  · exact Or.inl (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, neg_one_mul, neg_neg, ContinuousAlternatingMap.apply_apply])

/-- **Orientation along the rays of a `1`-dimensional carrier** (for Simon 7.3.3, proof of (2),
(10): `1`-dimensional minimizing cones are `m[[ℓ]]`; Ch. 3, 1.4 and Ch. 6, 3.1).  Let
`R = (M, θ, ξ)` be a `1`-dimensional integer multiplicity triple in `ℝᴾ` and `F` a finite set of
unit vectors with `H¹(M \ ⋃_{e ∈ F} ray(e)) = 0`, `ray(e) = {t e : t > 0}`.  Then for each
`e ∈ F`, `ξ(x) = ±e` for `H¹`-a.e. `x ∈ M ∩ ray(e)`: near `x = t₀ e` the other rays stay away,
so `M` lies on the line `x + ℝe` up to an `H¹`-null set, the approximate tangent line `TₓM` is
`ℝe`, and the unit orientations of `ℝe` are `±e`. -/
theorem Submission.idtp_fons_odc_ray_orientation : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ e ∈ F, ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)), R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) := by
  intro P R F hF hnull e he
  have he1 : ‖e‖ = 1 := hF e he
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he1
  -- Step 1: `ray(e)` is the image of `(0, ∞)` under the measurable embedding `t ↦ 0 + t e`
  -- (line_param), so `M ∩ ray(e)` is measurable.
  have hray : MeasurableSet ((fun t : ℝ => t • e) '' Ioi 0) := by
    have h := (Submission.idtp_fons_odc_line_hausdorff.2 P 0 e he1).1.measurableSet_image.2
      (measurableSet_Ioi (a := (0 : ℝ)))
    simpa only [zero_add] using h
  -- Step 6: `R.orients` holds a.e. on `M`, hence a.e. on `M ∩ ray(e)`, and a.e. point of
  -- `M ∩ ray(e)` is `t₀ e` with `t₀ > 0`.
  filter_upwards [ae_restrict_mem (R.measurableSet_carrier.inter hray),
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients] with x hx hxQ
  obtain ⟨-, t₀, ht₀ : 0 < t₀, hxe⟩ := hx
  simp only at hxe
  subst hxe
  obtain ⟨Q, hQ, hQo⟩ := hxQ
  -- Step 2: near `t₀ e`, every point on a ray of `F` lies on `ray(e)` (ray_isolation).
  obtain ⟨δ, hδ, hball⟩ := Submission.idtp_fons_odc_ro_ray_isolation P F e t₀ hF he1 ht₀
  -- Step 3: `M ∩ B_δ(t₀ e) ⊆ (t₀ e + ℝe) ∪ N` with `N = M \ ⋃_{e' ∈ F} ray(e')`.
  have hloc : R.carrier ∩ ball (t₀ • e) δ ⊆ range (fun s : ℝ => t₀ • e + s • e) ∪
      (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) := by
    rintro y ⟨hyM, hyB⟩
    by_cases hy : y ∈ ⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0
    · obtain ⟨t, -, rfl⟩ := hball ⟨hyB, hy⟩
      exact Or.inl ⟨t - t₀, by simp only [← add_smul, add_sub_cancel]⟩
    · exact Or.inr ⟨hyM, hy⟩
  -- Step 4: the approximate tangent line of `M` at `t₀ e` is `ℝe` (tangent_line).
  obtain rfl := Submission.idtp_fons_odc_ro_tangent_line P R.carrier _ (t₀ • e) e δ Q he0 hδ
    hnull hloc hQ
  -- Step 5: the unit orientations of `ℝe` are `±e` (line_orientation).
  exact Submission.idtp_fons_odc_ro_line_orientation P e (R.orient (t₀ • e)) he1 hQo

/-- **A `1`-dimensional current carried by finitely many rays** (Simon Ch. 7, proof of 3.3(2),
(10)).  Let `R = (M, θ, ξ)` be a `1`-dimensional integer multiplicity triple in `ℝᴾ` and `F` a
finite set of unit vectors such that `H¹`-almost all of `M` lies on the open rays
`ray(e) = {t e : t > 0}`, `e ∈ F`.  Then there are densities `g_e`, locally integrable and
a.e. integer-valued on `(0, ∞)`, with `τ(M, θ, ξ)(ω) = Σ_{e ∈ F} ∫_0^∞ g_e(t) ⟨ω(t e), e⟩ dt` for
every `ω ∈ 𝒟¹(ℝᴾ)`: `ξ = ±e` `H¹`-a.e. on `M ∩ ray(e)`, which makes the action on `M ∩ ray(e)`
such a ray integral, and these pieces split the action. -/
theorem Submission.idtp_fons_odc_ray_action : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∃ g : Euclid P → ℝ → ℝ, (∀ e ∈ F, LocallyIntegrableOn (g e) (Ioi 0)) ∧ (∀ e ∈ F, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g e t = k) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), g e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  intro P R F hF hnull
  /- Step 1: for `e ∈ F`, `ξ = ±e` `H¹`-a.e. on `M ∩ ray(e)`, so the action on `M ∩ ray(e)` is
  `∫_0^∞ g_e(t) ⟨ω(t e), e⟩ dt` for a locally integrable, a.e. integer-valued `g_e`. -/
  choose! g hloc hint hray using fun (e : Euclid P) (he : e ∈ F) =>
    Submission.idtp_fons_odc_ra_single_ray P R e (hF e he)
      (Submission.idtp_fons_odc_ray_orientation P R F hF hnull e he)
  refine ⟨g, hloc, hint, fun ω => ?_⟩
  /- Step 2: `τ(M, θ, ξ)(ω) = Σ_{e ∈ F} ∫_{M ∩ ray(e)} θ ⟨ω, ξ⟩ dH¹`, and each summand is the ray
  integral of step 1. -/
  rw [Submission.idtp_fons_odc_ra_action_split P R F hF hnull ω]
  exact Finset.sum_congr rfl fun e he => hray e he ω
/-- **Testing `∂C = 0` against `df` along rays** (Simon Ch. 6, (6.2.3) `∂T(φ) = T(dφ)`, applied to
the `0`-form of `f`).  Let `C ∈ 𝒟₁(ℝᴾ)` with `∂C = 0` be given by densities `G e` along the rays
`t ↦ te`, `e ∈ F`: `C(ω) = Σ_{e∈F} ∫_{(0,∞)} G e t · ω(te)[e] dt`.  For `f ∈ C^∞_c(ℝᴾ)` the
`0`-form `f̂(x) = f(x)` is a test form with `df̂(x)[v] = Df(x)v`, so
`0 = ∂C(f̂) = C(df̂) = Σ_{e∈F} ∫_{(0,∞)} G e t · Df(te)e dt`, and by the chain rule
`Df(te)e = (d/dt) f(te)`. -/
theorem Submission.idtp_fons_odc_rc_boundary_ray_test : ∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1), C.boundary = 0 → ∀ (F : Finset (Euclid P)) (G : Euclid P → ℝ → ℝ), (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), G e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) → ∀ f : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), G e t * deriv (fun s : ℝ => f (s • e)) t = 0 := by
  intro P C hC F G hrep f hf hfc
  -- Step 1: the test `0`-form `f̂(x) = constOfIsEmpty (f x)`.
  have hfhat : (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (f x)) ∈
      TestFormOn (univ : Set (Euclid P)) 0 :=
    ⟨⟨(ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)).contDiff.comp hf,
      hfc.comp_left (map_zero (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)))⟩,
      subset_univ _⟩
  -- Step 2: `df̂(x)[v] = Df(x)v`.
  have hd : ∀ x v : Euclid P, ((exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 ⟨_, hfhat⟩ :
      TestFormOn (univ : Set (Euclid P)) 1) : DifferentialForm (Euclid P) 1) x (fun _ => v) =
      fderiv ℝ f x v := by
    intro x v
    change extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (f x)) x
      (fun _ => v) = _
    rw [extDeriv_constOfIsEmpty, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  -- Step 3: `0 = ∂C(f̂) = C(df̂)`.
  have h0 : C (exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 ⟨_, hfhat⟩) = 0 := by
    rw [← GeometricCurrentOn.boundary_apply, hC, GeometricCurrentOn.zero_apply]
  -- Step 4: the chain rule `deriv (s ↦ f(se)) t = Df(te)e`.
  have hderiv : ∀ (e : Euclid P) (t : ℝ), deriv (fun s : ℝ => f (s • e)) t = fderiv ℝ f (t • e) e := by
    intro e t
    have hs : HasDerivAt (fun s : ℝ => s • e) e t := by
      simpa using (hasDerivAt_id t).smul_const e
    exact ((hf.differentiable (by simp) (t • e)).hasFDerivAt.comp_hasDerivAt t hs).deriv
  -- Step 5: substitute both into the ray representation of `C(df̂)`.
  have h1 := hrep (exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 ⟨_, hfhat⟩)
  simp only [hd] at h1
  simp only [hderiv]
  exact h1.symm.trans h0
/-- **A smooth cutoff that sees only one ray** (ray constancy for one-dimensional cones).
If `F` is a finite set of unit vectors, `‖e₀‖ = 1` and `ψ` is smooth with compact support in
`(0, ∞)`, then `f(x) = ψ(⟨x, e₀⟩) χ(‖x‖² − ⟨x, e₀⟩²)`, for a smooth `χ` with `χ(0) = 1` and
`χ = 0` on `[κ, ∞)` (`κ > 0` small), is smooth with compact support, `f(s e₀) = ψ(s)`, and `f`
vanishes on the open rays `{t e : t > 0}`, `e ∈ F`, `e ≠ e₀`. -/
theorem Submission.idtp_fons_odc_rc_ray_cutoff : ∀ (P : ℕ) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → ∀ e₀ : Euclid P, ‖e₀‖ = 1 → ∀ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 → ∃ f : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧ (∀ s : ℝ, f (s • e₀) = ψ s) ∧ ∀ e ∈ F, e ≠ e₀ → ∀ t : ℝ, 0 < t → f (t • e) = 0 := by
  intro P F hF e₀ he₀ ψ hψ hψc hψpos
  -- Step 1: `ψ s ≠ 0` forces `α ≤ s ≤ β`, with `0 < α`.
  obtain ⟨α, hα0, hα⟩ : ∃ α : ℝ, 0 < α ∧ ∀ s ∈ tsupport ψ, α ≤ s :=
    hψc.isCompact.exists_forall_le' continuousOn_id fun s hs => hψpos hs
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, ∀ s ∈ tsupport ψ, s ≤ β := hψc.isCompact.bddAbove
  have hψne : ∀ s : ℝ, ψ s ≠ 0 → α ≤ s ∧ s ≤ β := fun s hs =>
    ⟨hα s (subset_tsupport ψ hs), hβ s (subset_tsupport ψ hs)⟩
  -- Step 2: `0 < κ < α² (1 - ⟨e, e₀⟩²)` for the finitely many `e ∈ F` with `0 < ⟨e, e₀⟩ < 1`.
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ e ∈ F, 0 < inner ℝ e e₀ → inner ℝ e e₀ < 1 →
      κ < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := by
    have h : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ e ∈ F, 0 < inner ℝ e e₀ → inner ℝ e e₀ < 1 →
        κ < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := by
      refine (eventually_all_finset F).2 fun e _ => ?_
      by_cases hc : 0 < inner ℝ e e₀ ∧ inner ℝ e e₀ < 1
      · have hpos : 0 < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := by
          have h1 : inner ℝ e e₀ ^ 2 < 1 := by nlinarith [hc.1, hc.2]
          have h2 : 0 < α ^ 2 := by positivity
          nlinarith
        exact ((eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds).mono
          fun κ hκ _ _ => hκ
      · exact Eventually.of_forall fun κ h1 h2 => absurd ⟨h1, h2⟩ hc
    have h0 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ := self_mem_nhdsWithin
    obtain ⟨κ, hκ, hκ0⟩ := (h.and h0).exists
    exact ⟨κ, hκ0, hκ⟩
  -- Step 3: a smooth profile `χ` with `χ 0 = 1` and `χ = 0` on `[κ, ∞)`.
  obtain ⟨χ, hχ, hχ0, hχκ⟩ : ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ χ 0 = 1 ∧
      ∀ s, κ ≤ s → χ s = 0 := by
    refine ⟨fun s => Real.smoothTransition ((κ - s) / κ),
      Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const κ), ?_, ?_⟩
    · simp only [sub_zero, div_self hκ0.ne']
      exact Real.smoothTransition.one_of_one_le le_rfl
    · intro s hs
      exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hκ0.le)
  -- Step 4: `f x = ψ ⟨x, e₀⟩ * χ (‖x‖² - ⟨x, e₀⟩²)` is smooth.
  refine ⟨fun x => ψ (inner ℝ x e₀) * χ (‖x‖ ^ 2 - inner ℝ x e₀ ^ 2), ?_, ?_, ?_, ?_⟩
  · have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : Euclid P => inner ℝ x e₀ :=
      contDiff_id.inner ℝ contDiff_const
    exact (hψ.comp hL).mul (hχ.comp ((contDiff_norm_sq ℝ).sub (hL.pow 2)))
  -- Step 5: `f` vanishes outside `closedBall 0 (β + κ + 1)`.
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) (β + κ + 1)) ?_
    intro x hx
    by_contra hfx
    obtain ⟨hl, hu⟩ := hψne _ (left_ne_zero_of_mul hfx)
    have h3 : ‖x‖ ^ 2 - inner ℝ x e₀ ^ 2 < κ :=
      lt_of_not_ge fun h => right_ne_zero_of_mul hfx (hχκ _ h)
    have h4 : inner ℝ x e₀ ^ 2 ≤ β ^ 2 := by nlinarith
    have h5 : ‖x‖ ^ 2 < (β + κ + 1) ^ 2 := by nlinarith
    apply hx
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x]
  -- Step 6: values on the line `ℝ e₀`.
  · intro s
    have h1 : inner ℝ (s • e₀) e₀ = s := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he₀, one_pow, mul_one]
    have h2 : ‖s • e₀‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, he₀, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [h1, h2, sub_self, hχ0, mul_one]
  -- Step 7: vanishing on the other rays: `ψ (t c) ≠ 0` forces `0 < c < 1` and `α ≤ t`.
  · intro e he hne t ht
    have he1 : ‖e‖ = 1 := hF e he
    have h1 : inner ℝ (t • e) e₀ = t * inner ℝ e e₀ := real_inner_smul_left e e₀ t
    have h2 : ‖t • e‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, he1, mul_one, Real.norm_eq_abs, sq_abs]
    show ψ (inner ℝ (t • e) e₀) * χ (‖t • e‖ ^ 2 - inner ℝ (t • e) e₀ ^ 2) = 0
    rw [h1, h2]
    by_cases hψt : ψ (t * inner ℝ e e₀) = 0
    · rw [hψt, zero_mul]
    obtain ⟨hl, -⟩ := hψne _ hψt
    have hc0 : 0 < inner ℝ e e₀ := by
      by_contra h
      have : t * inner ℝ e e₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (not_lt.1 h)
      linarith
    have hc1 : inner ℝ e e₀ < 1 := by
      have hsub : 0 < ‖e - e₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have h3 := norm_sub_sq_real e e₀
      rw [he1, he₀] at h3
      nlinarith
    have hκ' := hκ e he hc0 hc1
    have htα : α ≤ t := by nlinarith
    have h5 : α ^ 2 ≤ t ^ 2 := by nlinarith
    have h6 : 0 < 1 - inner ℝ e e₀ ^ 2 := by nlinarith
    have h7 : α ^ 2 * (1 - inner ℝ e e₀ ^ 2) ≤ t ^ 2 * (1 - inner ℝ e e₀ ^ 2) :=
      mul_le_mul_of_nonneg_right h5 h6.le
    rw [hχκ _ (by nlinarith), mul_zero]
/-- **Fundamental theorem of calculus along a ray** (the ray computation of the Constancy
Theorem, Simon Ch. 6, 2.34, for the one-dimensional cones in the proof of 7.3.3): if `f` is
smooth with compact support on `ℝᴾ` and `|e| = 1`, then `∫_{(0,∞)} (d/dt) f(te) dt = −f(0)`.
As `e ≠ 0`, `s ↦ se` is a closed embedding `ℝ → ℝᴾ`, so `h(s) = f(se)` is `C¹` with compact
support; hence `h'` is integrable on `(0, ∞)`, `h(t) → 0` as `t → ∞`, and
`∫_{(0,∞)} h' = 0 − h(0) = −f(0)`. -/
theorem Submission.idtp_fons_odc_rc_ray_ftc : ∀ (P : ℕ) (f : Euclid P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∀ e : Euclid P, ‖e‖ = 1 → ∫ t in Ioi (0 : ℝ), deriv (fun s : ℝ => f (s • e)) t = -f 0 := by
  intro P f hf hfc e he
  -- `e ≠ 0`, so `s ↦ s • e` is a closed embedding `ℝ → ℝᴾ`
  have he0 : e ≠ 0 := ne_zero_of_norm_ne_zero (by rw [he]; exact one_ne_zero)
  -- `h(s) = f(s • e)` is `C¹`, and has compact support as `f` does
  have hh : ContDiff ℝ 1 fun s : ℝ => f (s • e) :=
    (hf.of_le (by exact_mod_cast le_top)).comp (contDiff_id.smul contDiff_const)
  have hhc : HasCompactSupport fun s : ℝ => f (s • e) :=
    hfc.comp_isClosedEmbedding (isClosedEmbedding_smul_left (𝕜 := ℝ) he0)
  -- FTC on `(0, ∞)`: `∫_{(0,∞)} h' = 0 - h(0) = -f(0)`
  rw [hhc.integral_Ioi_deriv_eq hh 0, zero_smul]
/-- **One-dimensional constancy theorem** (du Bois-Reymond; Simon Ch. 6, 2.34 for `n = 1`): if `g`
is locally integrable on `U = (0, ∞)` and `∫_U g φ' = 0` for every `C^∞` function `φ` with compact
support in `U`, then `g` is a.e. constant on `U`.  Fix a bump `b` supported in `[1/2, 3/2]`.  A
test `f` with `∫ f = 0` is the derivative of the test `Ψ(t) = ∫_0^t f`, so `∫ g f = 0`; applied
to `f = ψ − (∫ ψ / ∫ b) b` this gives `∫ ψ (g − c) = 0` with `c = ∫ g b / ∫ b`, so by the
fundamental lemma of the calculus of variations `g = c` a.e. on `U`. -/
theorem Submission.idtp_fons_odc_du_bois_reymond : ∀ g : ℝ → ℝ, LocallyIntegrableOn g (Ioi 0) → (∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 → ∫ t in Ioi (0 : ℝ), g t * deriv φ t = 0) → ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g t = c := by
  intro g hg h
  -- Step 1: a bump `b` with `b(1) = 1` and `tsupport b = [1/2, 3/2] ⊆ U`, so `∫ b > 0`
  obtain ⟨b, hb⟩ : ∃ b : ContDiffBump (1 : ℝ), b.rOut = 1 / 2 :=
    ⟨⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩, rfl⟩
  have hbs : tsupport b ⊆ Ioi 0 := by
    rw [b.tsupport_eq, hb, Real.closedBall_eq_Icc]
    exact fun x hx => show (0 : ℝ) < x by linarith [hx.1]
  have hI : 0 < ∫ t, b t :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
      b.hasCompactSupport (fun x => b.nonneg' x) (x := 1)
      (by rw [b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)]; exact one_ne_zero)
  have hbi := b.continuous.integrable_of_hasCompactSupport (μ := volume) b.hasCompactSupport
  -- Step 2: `g ψ` is integrable for continuous `ψ` with compact support in `U`
  have hint : ∀ ψ : ℝ → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 →
      Integrable (fun t => g t * ψ t) := by
    intro ψ hψ hψc hψs
    rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
    · exact (hg.integrableOn_compact_subset hψs hψc).mul_continuousOn hψ.continuousOn hψc
    · exact (support_mul_subset_right _ _).trans (subset_tsupport ψ)
  have hgb := hint b b.continuous b.hasCompactSupport hbs
  -- Step 3: a test `f` with `∫ f = 0` and `tsupport f ⊆ [α, β]` has the primitive
  -- `Ψ(t) = ∫_0^t f`, which is `C^∞` with `Ψ' = f` and vanishes off `[α, β]`
  have hprim : ∀ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ Ioi 0 → ∫ t, f t = 0 → ∃ Ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
        HasCompactSupport Ψ ∧ tsupport Ψ ⊆ Ioi 0 ∧ deriv Ψ = f := by
    intro f hf hfc hfs hf0
    obtain ⟨α, hα, hαf⟩ := hfc.isCompact.exists_forall_le' continuousOn_id fun x hx => hfs hx
    obtain ⟨β, hβ⟩ := hfc.isCompact.bddAbove
    have hderiv : ∀ t, HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f t) t :=
      fun t => (hf.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hd : deriv (fun u => ∫ x in (0 : ℝ)..u, f x) = f := funext fun t => (hderiv t).deriv
    have hvan : ∀ t ∉ Icc α β, ∫ x in (0 : ℝ)..t, f x = 0 := by
      intro t ht
      by_cases htα : t < α
      · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
          intervalIntegral.integral_zero]
        intro x hx
        refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
        rw [uIcc, mem_Icc] at hx
        exact (hαf x hxs).not_gt (hx.2.trans_lt (max_lt hα htα))
      · have hβt : β < t := not_le.1 fun h' => ht ⟨not_lt.1 htα, h'⟩
        rw [intervalIntegral.integral_of_le (hα.le.trans (not_lt.1 htα)),
          setIntegral_eq_integral_of_forall_compl_eq_zero, hf0]
        intro x hx
        exact image_eq_zero_of_notMem_tsupport fun hxs => hx ⟨hfs hxs, (hβ hxs).trans hβt.le⟩
    refine ⟨fun u => ∫ x in (0 : ℝ)..u, f x, ?_, HasCompactSupport.intro isCompact_Icc hvan,
      ?_, hd⟩
    · exact contDiff_infty_iff_deriv.2 ⟨fun t => (hderiv t).differentiableAt, by rwa [hd]⟩
    · exact (closure_minimal (support_subset_iff'.2 hvan) isClosed_Icc).trans
        fun x hx => hα.trans_le hx.1
  -- Step 4: `g` annihilates tests with zero integral: `∫ g f = ∫_U g Ψ' = 0`
  have key : ∀ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ Ioi 0 → ∫ t, f t = 0 → ∫ t, g t * f t = 0 := by
    intro f hf hfc hfs hf0
    obtain ⟨Ψ, hΨ, hΨc, hΨs, rfl⟩ := hprim f hf hfc hfs hf0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
    · exact h Ψ hΨ hΨc hΨs
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hfs h')), mul_zero]
  -- the constant `c = ∫ g b / ∫ b`
  refine ⟨(∫ t, g t * b t) / ∫ t, b t, ?_⟩
  -- Steps 6–7: by the fundamental lemma on the open set `U` and `ae_restrict_iff'`, it suffices
  -- that `∫ ψ (g − c) = 0` for every `C^∞` test `ψ` with compact support in `U`
  have hU := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun t => g t - (∫ t, g t * b t) / ∫ t, b t) (hg.sub (locallyIntegrableOn_const _)) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (hU.mono fun t ht ht' => sub_eq_zero.1 (ht ht'))
  -- Step 5: with `a = ∫ ψ / ∫ b`, the test `f = ψ − a b` has `∫ f = 0`, so Step 4 gives
  -- `0 = ∫ g f = ∫ g ψ − a ∫ g b = ∫ ψ (g − c)`
  intro ψ hψ hψc hψs
  have hψi := hψ.continuous.integrable_of_hasCompactSupport (μ := volume) hψc
  have hgψ := hint ψ hψ.continuous hψc hψs
  set a := (∫ t, ψ t) / ∫ t, b t with ha
  have hs : tsupport (fun t => ψ t - a * b t) ⊆ Ioi 0 := by
    refine (closure_minimal (support_subset_iff'.2 fun x hx => ?_)
      ((isClosed_tsupport ψ).union (isClosed_tsupport b))).trans (union_subset hψs hbs)
    simp only [mem_union, not_or] at hx
    simp [image_eq_zero_of_notMem_tsupport hx.1, image_eq_zero_of_notMem_tsupport hx.2]
  have H : ∫ t, g t * (ψ t - a * b t) = 0 :=
    key _ (hψ.sub (contDiff_const.mul b.contDiff)) (hψc.sub b.hasCompactSupport.mul_left) hs
      (by rw [integral_sub hψi (hbi.const_mul a), integral_const_mul, ha,
        div_mul_cancel₀ _ hI.ne', sub_self])
  have e1 : (fun t => g t * (ψ t - a * b t)) = fun t => g t * ψ t - a * (g t * b t) := by
    funext t; ring
  have e2 : (fun t => ψ t • (g t - (∫ t, g t * b t) / ∫ t, b t)) =
      fun t => g t * ψ t - (∫ t, g t * b t) / (∫ t, b t) * ψ t := by
    funext t; rw [smul_eq_mul]; ring
  rw [e1, integral_sub hgψ (hgb.const_mul a), integral_const_mul] at H
  rw [e2, integral_sub hgψ (hψi.const_mul _), integral_const_mul, ← H, ha]
  ring

/-- **Simon Ch. 6, 2.34 (constancy theorem) on finitely many rays.**  Let `C ∈ 𝒟₁(ℝᴾ)` with
`∂C = 0` be given on the open rays `{te : t > 0}`, `e ∈ F` (unit vectors), by densities `g_e` that
are locally integrable and a.e. integer-valued on `(0, ∞)`.  Testing `∂C = 0` with `f ∈ C^∞_c(ℝᴾ)`
gives `Σ_e ∫₀^∞ g_e(t) (d/dt) f(te) dt = 0`.  A cutoff `f` equal to `ψ ∈ C^∞_c((0, ∞))` on `ℝe₀`
and vanishing on the other open rays reduces this to `∫₀^∞ g_{e₀} ψ' = 0`, so `g_{e₀}` is a.e. a
constant (du Bois-Reymond), which is an integer `m(e₀)` by integrality.  A bump `b` with
`b(0) = 1` and `∫₀^∞ (d/dt) b(te) dt = −b(0)` then gives `Σ_e m(e) = 0`. -/
theorem Submission.idtp_fons_odc_ray_constancy : ∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1), C.boundary = 0 → ∀ F : Finset (Euclid P), (∀ e ∈ F, ‖e‖ = 1) → ∀ g : Euclid P → ℝ → ℝ, (∀ e ∈ F, LocallyIntegrableOn (g e) (Ioi 0)) → (∀ e ∈ F, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g e t = k) → (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), g e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) → ∃ m : Euclid P → ℤ, ∑ e ∈ F, m e = 0 ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  intro P C hC F hF g hg hgZ hrep
  -- (1.1) `Σ_e ∫₀^∞ g_e(t) (d/dt) f(te) dt = 0` for every `f ∈ C^∞_c(ℝᴾ)`
  have htest := Submission.idtp_fons_odc_rc_boundary_ray_test P C hC F g hrep
  -- `(0, ∞)` has positive measure, so an a.e. property on it holds at some point
  have : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioi]; exact ENNReal.top_ne_zero)
  -- each density is a.e. an integer constant on `(0, ∞)`
  have hconst : ∀ e₀ ∈ F, ∃ k : ℤ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g e₀ t = k := by
    intro e₀ he₀
    -- `∫₀^∞ g_{e₀} ψ' = 0` for every `ψ ∈ C^∞_c((0, ∞))`
    have hdbr : ∀ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioi 0 → ∫ t in Ioi (0 : ℝ), g e₀ t * deriv ψ t = 0 := by
      intro ψ hψ hψc hψs
      obtain ⟨f, hf, hfc, hfe₀, hfe⟩ :=
        Submission.idtp_fons_odc_rc_ray_cutoff P F hF e₀ (hF e₀ he₀) ψ hψ hψc hψs
      -- on the other rays `t ↦ f(te)` vanishes on the open set `(0, ∞)`, so does its derivative
      have hother : ∀ e ∈ F, e ≠ e₀ →
          ∫ t in Ioi (0 : ℝ), g e t * deriv (fun s : ℝ => f (s • e)) t = 0 := by
        intro e he hne
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        have hzero : (fun s : ℝ => f (s • e)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
          eventually_of_mem (Ioi_mem_nhds ht) fun s hs => hfe e he hne s hs
        rw [hzero.deriv_eq, deriv_const, mul_zero]
      have h := htest f hf hfc
      rw [Finset.sum_eq_single_of_mem e₀ he₀ hother,
        show (fun s : ℝ => f (s • e₀)) = ψ from funext hfe₀] at h
      exact h
    obtain ⟨c, hc⟩ := Submission.idtp_fons_odc_du_bois_reymond (g e₀) (hg e₀ he₀) hdbr
    obtain ⟨t, htc, k, hk⟩ := (hc.and (hgZ e₀ he₀)).exists
    exact ⟨k, hc.mono fun s hs => hs.trans (htc.symm.trans hk)⟩
  choose! m hm using hconst
  refine ⟨m, ?_, fun ω => ?_⟩
  · -- a bump `b ∈ C^∞_c(ℝᴾ)` with `b(0) = 1`; `∫₀^∞ (d/dt) b(te) dt = −b(0)` on each ray
    let b : ContDiffBump (0 : Euclid P) := ⟨1, 2, one_pos, one_lt_two⟩
    have hb0 : b 0 = 1 := b.eventuallyEq_one.eq_of_nhds
    have hterm : ∀ e ∈ F,
        ∫ t in Ioi (0 : ℝ), g e t * deriv (fun s : ℝ => b (s • e)) t = -(m e : ℝ) := by
      intro e he
      calc ∫ t in Ioi (0 : ℝ), g e t * deriv (fun s : ℝ => b (s • e)) t
          = ∫ t in Ioi (0 : ℝ), (m e : ℝ) * deriv (fun s : ℝ => b (s • e)) t := by
            refine integral_congr_ae ?_
            filter_upwards [hm e he] with t ht
            rw [ht]
        _ = (m e : ℝ) * -b 0 := by
            rw [integral_const_mul, Submission.idtp_fons_odc_rc_ray_ftc P b b.contDiff
              b.hasCompactSupport e (hF e he)]
        _ = -(m e : ℝ) := by rw [hb0, mul_neg, mul_one]
    have hsum : ∑ e ∈ F, -(m e : ℝ) = 0 :=
      (Finset.sum_congr rfl hterm).symm.trans (htest b b.contDiff b.hasCompactSupport)
    rw [Finset.sum_neg_distrib, neg_eq_zero] at hsum
    exact_mod_cast hsum
  · -- `g_e = m(e)` a.e. on `(0, ∞)`, and the constant comes out of the integral
    rw [hrep ω]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hm e he] with t ht
    rw [ht]

/-- **Weighted open line pieces carry an integer multiplicity triple** (Simon Ch. 6, 3.1; the
polygonal current in the proof of 7.3.3).  Let `Sₖ = γₖ(Iₖ)`, `γₖ(t) = pₖ + t vₖ` with `‖vₖ‖ = 1`
and `Iₖ` open, and let the overlaps `Sⱼ ∩ closure Sₖ` (`j ≠ k`) be `H¹`-null.  Then
`M = ⋃_{cₖ ≠ 0} Sₖ`, `θ = Σₖ |cₖ| 𝟙_{Sₖ}` and `ξ = Σₖ (cₖ 𝟙_{Sₖ} / θ) vₖ` form an `IMRep univ 1`
with `θ ξ(α) = Σₖ cₖ 𝟙_{Sₖ} α(vₖ)`.  The pieces are Borel and locally `H¹`-finite because `γₖ` is
an isometry; off the null overlap set `M` is locally the line `x + span {vₖ}`
(`idtp_fons_odc_pc_piece_locally_line`), whose approximate tangent space is `span {vₖ}`
(`idtp_fons_odc_pc_local_plane_tangent`), and there `ξ(x) = ±vₖ`. -/
theorem Submission.idtp_fons_odc_pc_imrep : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) ∧ (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) ∧ ∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k) := by
  intro P ι _ p v I c hv hI hdisj
  -- Tool (ii): `γₖ(t) = pₖ + t vₖ` is an isometry `ℝ → ℝᴾ`
  have hγ : ∀ k, Isometry (fun t : ℝ => p k + t • v k) := fun k =>
    Isometry.of_dist_eq fun s t => by
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv k, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  -- Step 1: the pieces `Sₖ = γₖ(Iₖ)` are Borel; the carrier `M = ⋃_{cₖ ≠ 0} Sₖ`
  obtain ⟨S, hSdef⟩ : ∃ S : ι → Set (Euclid P),
      ∀ k, S k = (fun t : ℝ => p k + t • v k) '' I k := ⟨_, fun _ => rfl⟩
  have hS : ∀ k, MeasurableSet (S k) := fun k => by
    rw [hSdef]
    exact (hγ k).isClosedEmbedding.measurableEmbedding.measurableSet_image.2 (hI k).measurableSet
  obtain ⟨M, hMdef⟩ : ∃ M : Set (Euclid P), M = ⋃ k, ⋃ (_ : c k ≠ 0), S k := ⟨_, rfl⟩
  have hmemM : ∀ x, x ∈ M ↔ ∃ k, c k ≠ 0 ∧ x ∈ S k := fun x => by simp [hMdef]
  have hM : MeasurableSet M :=
    hMdef ▸ MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hS k
  have hSM : ∀ k, c k ≠ 0 → S k ⊆ M := fun k hk x hx => (hmemM x).2 ⟨k, hk, hx⟩
  have hMS : M ⊆ ⋃ j, (fun t : ℝ => p j + t • v j) '' I j := fun y hy => by
    obtain ⟨j, -, hyj⟩ := (hmemM y).1 hy
    exact mem_iUnion.2 ⟨j, by rwa [← hSdef]⟩
  -- Step 2: the multiplicity `θ = Σₖ |cₖ| 𝟙_{Sₖ}` and `∫_B θ dH¹ = Σₖ |cₖ| H¹(Sₖ ∩ B)`
  obtain ⟨θ, hθdef⟩ : ∃ θ : Euclid P → ℕ,
      θ = fun x => ∑ k, (S k).indicator (fun _ => (c k).natAbs) x := ⟨_, rfl⟩
  have hθmeas : Measurable θ :=
    hθdef ▸ Finset.measurable_sum _ fun k _ => measurable_const.indicator (hS k)
  have hθlint : ∀ B, ∫⁻ x in B, (θ x : ℝ≥0∞) ∂μHE[1] =
      ∑ k, ((c k).natAbs : ℝ≥0∞) * μHE[1] (S k ∩ B) := fun B => by
    have h : ∀ x, (θ x : ℝ≥0∞) = ∑ k, (S k).indicator (fun _ => ((c k).natAbs : ℝ≥0∞)) x :=
      fun x => by
        rw [hθdef]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by by_cases hx : x ∈ S k <;> simp [hx]
    simp_rw [h]
    rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hS k)]
    exact Finset.sum_congr rfl fun k _ => by
      rw [lintegral_indicator_const (hS k), Measure.restrict_apply (hS k)]
  -- Step 3: the orientation `ξ = Σₖ (cₖ 𝟙_{Sₖ} / θ) ev_{vₖ}` is strongly measurable
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Euclid P → MultiVector P 1, ξ = fun x =>
      ∑ k, ((S k).indicator (fun _ => (c k : ℝ)) x / θ x) •
        ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := ⟨_, rfl⟩
  have hξmeas : StronglyMeasurable ξ := by
    -- instance search does not find `ContinuousAdd` for this space of continuous linear maps
    have : ContinuousAdd (MultiVector P 1) :=
      (inferInstance : IsTopologicalAddGroup (MultiVector P 1)).toContinuousAdd
    rw [hξdef]
    exact Finset.stronglyMeasurable_fun_sum _ fun k _ =>
      (((measurable_const.indicator (hS k)).div
        (measurable_from_nat.comp hθmeas)).stronglyMeasurable).smul_const _
  -- Step 4: `θ(x) ξ(x)(α) = Σₖ cₖ 𝟙_{Sₖ}(x) α(vₖ)`
  have hθξ : ∀ x (α : Covector (Euclid P) 1), (θ x : ℝ) * ξ x α =
      ∑ k, (S k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k) := by
    intro x α
    rw [hξdef]
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.apply_apply]
    rcases eq_or_ne (θ x : ℝ) 0 with h | h
    · -- `θ(x) = 0` forces every `cₖ 𝟙_{Sₖ}(x)` to vanish
      have h0 : ∀ k, (S k).indicator (fun _ => (c k : ℝ)) x = 0 := by
        intro k
        rw [Nat.cast_eq_zero, hθdef] at h
        have hk := Finset.sum_eq_zero_iff.1 h k (Finset.mem_univ k)
        rw [indicator_apply_eq_zero] at hk ⊢
        exact fun hx => by simp [Int.natAbs_eq_zero.1 (hk hx)]
      simp [h, h0]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by field_simp
  -- Step 5: `R = (M, θ, ξ)` is an integer multiplicity triple
  let R : IMRep (univ : Set (Euclid P)) 1 :=
    { carrier := M
      mult := θ
      orient := ξ
      measurableSet_carrier := hM
      carrier_subset := subset_univ M
      rectifiable := by
        -- each `Sₖ` lies in the range of the Lipschitz map `γₖ ∘ proj₀ : ℝ¹ → ℝᴾ`
        refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (countable_range S)
          (forall_mem_range.2 fun k => ?_)).mono ?_
        · rw [hSdef]
          refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_range
            ((hγ k).lipschitzWith.comp (EuclideanSpace.proj (0 : Fin 1) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).lipschitzWith)).mono ?_
          rintro _ ⟨t, -, rfl⟩
          exact ⟨EuclideanSpace.single 0 t, by simp⟩
        · intro x hx
          obtain ⟨k, -, hxk⟩ := (hmemM x).1 hx
          exact ⟨S k, mem_range_self k, hxk⟩
      measurable_mult := hθmeas
      mult_pos := fun x hx => by
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hx
        rw [hθdef]
        refine (Int.natAbs_pos.2 hk).trans_le ?_
        calc (c k).natAbs = (S k).indicator (fun _ => (c k).natAbs) x :=
              (indicator_of_mem hxk fun _ => (c k).natAbs).symm
          _ ≤ _ := Finset.single_le_sum (f := fun j => (S j).indicator (fun _ => (c j).natAbs) x)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
      locallyIntegrable_mult := fun K hK _ => by
        rw [hθlint]
        refine ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
        refine ne_top_of_le_ne_top ?_ (measure_mono (inter_subset_inter_right _ inter_subset_right))
        -- `H¹(Sₖ ∩ K) = ℒ¹(Iₖ ∩ γₖ⁻¹K) ≤ ℒ¹(γₖ⁻¹K) < ∞`, `γₖ⁻¹K` being compact
        have hvol : (μHE[1] : Measure ℝ) = volume := by
          have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
          rwa [Module.finrank_self] at h
        rw [hSdef, ← image_inter_preimage, (hγ k).euclideanHausdorffMeasure_image, hvol]
        exact ne_top_of_le_ne_top
          ((hγ k).isClosedEmbedding.isCompact_preimage hK).measure_lt_top.ne
          (measure_mono inter_subset_right)
      aestronglyMeasurable_orient := hξmeas.aestronglyMeasurable
      orients := by
        -- off the `H¹`-null overlap set, `x` lies in exactly one piece `Sₖ`, away from the others
        have hB : (μHE[1] : Measure (Euclid P))
            (⋃ j, ⋃ k, ⋃ (_ : j ≠ k), S j ∩ closure (S k)) = 0 :=
          measure_iUnion_null fun j => measure_iUnion_null fun k => measure_iUnion_null fun h => by
            rw [hSdef, hSdef]
            exact hdisj j k h
        filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hB), ae_restrict_mem hM]
          with x hxB hxM
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hxM
        have hxj : ∀ j, j ≠ k → x ∉ closure (S j) := fun j hjk h =>
          hxB (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk.symm, hxk, h⟩⟩⟩)
        have hθx : θ x = (c k).natAbs := by
          rw [hθdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => indicator_of_notMem
              (fun h => hxj j hjk (subset_closure h)) _) (fun h => (h (Finset.mem_univ k)).elim),
            indicator_of_mem hxk]
        have hξx : ξ x = ((c k : ℝ) / |(c k : ℝ)|) •
            ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := by
          rw [hξdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => by
              rw [indicator_of_notMem (fun h => hxj j hjk (subset_closure h)), zero_div, zero_smul])
            (fun h => (h (Finset.mem_univ k)).elim), indicator_of_mem hxk, hθx, Nat.cast_natAbs,
            Int.cast_abs]
        refine ⟨Submodule.span ℝ {v k}, ?_, ?_⟩
        · -- Tools (iii), (iv): near `x`, `M` is the line `x + span {vₖ}`
          obtain ⟨r, hr, hMr⟩ := Submission.idtp_fons_odc_pc_piece_locally_line P ι p v I M k x
            (hv k) (hI k) hMS (by rw [← hSdef]; exact hSM k hk) (by rw [← hSdef]; exact hxk)
            fun j hjk => by rw [← hSdef]; exact hxj j hjk
          exact Submission.idtp_fons_odc_pc_local_plane_tangent P 1 M x _ r hM
            (finrank_span_singleton (norm_ne_zero_iff.1 (by rw [hv k]; exact one_ne_zero))) hr hMr
        · -- `ξ(x) = ±vₖ` with `(vₖ)` orthonormal spanning `span {vₖ}`
          rw [hξx]
          refine ⟨fun _ => v k, ⟨fun _ => hv k, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩,
            by rw [range_const], ?_⟩
          have hck : (c k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
          rcases hck.lt_or_gt with h | h
          · exact Or.inr fun α => by simp [abs_of_neg h, div_neg, div_self hck]
          · exact Or.inl fun α => by simp [abs_of_pos h, div_self hck] }
  -- Step 6: the carrier, multiplicity and `θ ξ` formulas hold by construction
  refine ⟨R, ?_, fun x => ?_, fun x α => ?_⟩
  · show M = _
    rw [hMdef]
    simp_rw [hSdef]
  · show θ x = _
    rw [hθdef]
    simp_rw [hSdef]
  · show (θ x : ℝ) * ξ x α = _
    rw [hθξ x α]
    simp_rw [hSdef]
/-- **Simon 7.3.3, proof of (2)**, the polygonal integer multiplicity current (steps 4–5): let
`R` be a 1-dimensional integer multiplicity triple in `ℝᴾ` carried by `⋃_{cₖ ≠ 0} Sₖ`, where
`Sₖ = γₖ(Iₖ)`, `γₖ(t) = pₖ + t vₖ`, `‖vₖ‖ = 1`, with `θ = Σₖ |cₖ| 1_{Sₖ}` and
`θ ⟨α, ξ⟩ = Σₖ cₖ 1_{Sₖ} α(vₖ)`.  Then `τ(R)(ω) = Σₖ cₖ ∫_{Iₖ} ω(γₖ(t))(vₖ) dt` and
`μ_R(A) = Σₖ |cₖ| ℒ¹(Iₖ ∩ γₖ⁻¹(A))`, since `H¹⌞Sₖ = γₖ#(ℒ¹⌞Iₖ)` and `Sₖ ⊆ M` when `cₖ ≠ 0`. -/
theorem Submission.idtp_fons_odc_pc_imrep_formulas : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, MeasurableSet (I k)) → ∀ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) → (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) → (∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A) := by
  intro P ι _ p v I c hv hI R hC hmult horient
  -- `γₖ(t) = pₖ + t vₖ` is a measurable embedding, `H¹⌞γₖ(J) = γₖ#(ℒ¹⌞J)` and `H¹(γₖ(J)) = ℒ¹(J)`
  have hline := fun k => Submission.idtp_fons_odc_line_hausdorff.2 P (p k) (v k) (hv k)
  -- `Sₖ = γₖ(Iₖ)` is measurable, and `Sₖ ⊆ C` when `cₖ ≠ 0`
  have hS : ∀ k, MeasurableSet ((fun t : ℝ => p k + t • v k) '' I k) := fun k =>
    (hline k).1.measurableSet_image.mpr (hI k)
  have hSC : ∀ k, c k ≠ 0 → (fun t : ℝ => p k + t • v k) '' I k ⊆ R.carrier := fun k hk => by
    rw [hC]
    exact Set.subset_iUnion₂ (s := fun k (_ : c k ≠ 0) => (fun t : ℝ => p k + t • v k) '' I k) k hk
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- `1_{Sₖ}(x) cₖ ω(x)(vₖ)` is the indicator of `x ↦ cₖ ω(x)(vₖ)`
    have hmul : ∀ k x, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x *
        (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k) =
        ((fun t : ℝ => p k + t • v k) '' I k).indicator
          (fun x => (c k : ℝ) * (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k)) x :=
      fun k x => (Set.indicator_mul_left _ (fun _ => (c k : ℝ))
        (fun x => (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))).symm
    -- `x ↦ ω(x)(vₖ)` is continuous with compact support along `γₖ`, hence `H¹`-integrable on `Sₖ`
    have hint : ∀ k, Integrable (fun x => ((fun t : ℝ => p k + t • v k) '' I k).indicator
        (fun _ => (c k : ℝ)) x * (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))
        (μHE[1].restrict R.carrier) := by
      intro k
      have hiso : Isometry (fun t : ℝ => p k + t • v k) := Isometry.of_dist_eq fun s t => by
        show dist (p k + s • v k) (p k + t • v k) = dist s t
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv k, mul_one, Real.dist_eq,
          Real.norm_eq_abs]
      have hcont : Continuous fun t : ℝ =>
          (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) :=
        (continuous_eval_const (fun _ : Fin 1 => v k)).comp (ω.2.1.1.continuous.comp hiso.continuous)
      have hcs : HasCompactSupport fun t : ℝ =>
          (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) :=
        (ω.2.1.2.comp_isClosedEmbedding hiso.isClosedEmbedding).comp_left
          (g := fun α : Covector (Euclid P) 1 => α (fun _ => v k)) rfl
      have h1 : Integrable (fun x => (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))
          (μHE[1].restrict ((fun t : ℝ => p k + t • v k) '' I k)) := by
        rw [((hline k).2 (I k)).1, (hline k).1.integrable_map_iff]
        exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
      simp only [hmul k]
      rw [integrable_indicator_iff (hS k)]
      refine (h1.const_mul (c k : ℝ)).mono_measure ?_
      rw [Measure.restrict_restrict (hS k)]
      exact Measure.restrict_mono Set.inter_subset_left le_rfl
    show ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x)
      ∂μHE[1] = _
    simp only [horient]
    rw [integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hmul k]
    rw [integral_indicator (hS k), Measure.restrict_restrict (hS k), integral_const_mul]
    by_cases hk : c k = 0
    · simp [hk]
    · rw [Set.inter_eq_left.mpr (hSC k hk), ((hline k).2 (I k)).1, (hline k).1.integral_map]
  · -- `θ = Σₖ |cₖ| 1_{Sₖ}` as `ℝ≥0∞`-valued functions
    have hθ : ∀ x, ((R.mult x : ℕ) : ℝ≥0∞) = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator
        (fun _ => ((c k).natAbs : ℝ≥0∞)) x := by
      intro x
      rw [hmult x, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hx : x ∈ (fun t : ℝ => p k + t • v k) '' I k
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Nat.cast_zero]
    rw [IMRep.measure, withDensity_apply _ hA, Measure.restrict_restrict hA]
    simp only [hθ]
    rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hS k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lintegral_indicator_const (hS k), Measure.restrict_apply (hS k)]
    by_cases hk : c k = 0
    · simp [hk]
    · rw [Set.inter_comm A, ← Set.inter_assoc, Set.inter_eq_left.mpr (hSC k hk),
        ← Set.image_inter_preimage, ((hline k).2 _).2, ← ENNReal.ofReal_natCast, Nat.cast_natAbs,
        Int.cast_abs]

/-- **Polygonal integer multiplicity 1-currents** (Simon Ch. 6, 3.1–3.2; used for the
1-dimensional minimizing cones `S₀ = m[[ℓ]]` in the proof of 7.3.3, (10)).  Finitely many
oriented open line pieces `S_k = γ_k(I_k)`, `γ_k(t) = p_k + t v_k` (`‖v_k‖ = 1`, `I_k` open),
with integer weights `c_k` and `H¹`-null overlaps `S_j ∩ closure S_k` (`j ≠ k`), define the
current `X(ω) = Σ_k c_k ∫_{I_k} ω(γ_k t)(v_k) dt`.  It is represented by the triple
`R = (⋃_{c_k ≠ 0} S_k, Σ_k 1_{S_k}|c_k|, ξ)` with `θξ(α) = Σ_k 1_{S_k} c_k α(v_k)`, whose
mass measure is `R.measure A = Σ_k |c_k| ℒ¹(I_k ∩ γ_k⁻¹A)`. -/
theorem Submission.idtp_fons_odc_polygonal_current : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ (X : GeometricCurrentOn (univ : Set (Euclid P)) 1) (R : IMRep (univ : Set (Euclid P)) 1), R.Represents X ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A) := by
  intro P ι hι p v I c hv hI hnull
  -- Step 1: the weighted line-integral current `X`, with real weights `(c k : ℝ)`.
  obtain ⟨X, hX⟩ := Submission.idtp_fons_odc_pc_line_current P ι p v I (fun k => (c k : ℝ)) hv
  -- Steps 2–3: the triple `R = (⋃_{c_k ≠ 0} S_k, Σ_k 1_{S_k}|c_k|, ξ)`.
  obtain ⟨R, hcar, hmult, hθξ⟩ := Submission.idtp_fons_odc_pc_imrep P ι p v I c hv hI hnull
  -- Steps 4–5: the action and the mass measure of `R`.
  obtain ⟨hact, hmeas⟩ := Submission.idtp_fons_odc_pc_imrep_formulas P ι p v I c hv
    (fun k => (hI k).measurableSet) R hcar hmult hθξ
  -- `R.Represents X` is `∀ ω, X ω = R.action ω`; both sides equal the weighted sum.
  exact ⟨X, R, fun ω => (hX ω).trans (hact ω).symm, hX, hmeas⟩

/-- **Simon 7.3.3, proof of (2), (10)** (p. 193; steps 3–4 of the 1-dimensional cone
classification read backwards): if `C = Σ_{e ∈ F} m(e)[[ray(e)]]` for finitely many unit vectors
`e`, with open rays `ray(e) = {te : t > 0}`, then `C` is integer multiplicity with mass measure
`μ_C = Σ_{e ∈ F} |m(e)| H¹⌞ray(e)`.  Index the pieces of `idtp_fons_odc_polygonal_current` by `F`
(base point `0`, direction `e`, parameter interval `(0, ∞)`, weight `m(e)`).  Distinct open rays
miss each other's closed rays: `{se' : s ≥ 0}` is closed, and `te = se'` with `t > 0`, `s ≥ 0`
gives `t = s` (taking norms) and then `e = e'`; so the overlaps are empty, hence `H¹`-null. -/
theorem Submission.idtp_fons_odc_ray_current_rep : ∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → ∀ m : Euclid P → ℤ, (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.Represents C ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ e ∈ F, ENNReal.ofReal |(m e : ℝ)| * volume (Ioi (0 : ℝ) ∩ (fun t : ℝ => t • e) ⁻¹' A) := by
  intro P C F hF m hC
  -- distinct open rays `ray(e) = {te : t > 0}` miss each other's closed rays
  have hray : ∀ e e' : Euclid P, ‖e‖ = 1 → ‖e'‖ = 1 → e ≠ e' →
      ((fun t : ℝ => (0 : Euclid P) + t • e) '' Ioi 0) ∩
        closure ((fun t : ℝ => (0 : Euclid P) + t • e') '' Ioi 0) = ∅ := by
    intro e e' he he' hne
    -- `closure ray(e') ⊆ {se' : s ≥ 0}`, the image of `[0, ∞)` under the closed map `s ↦ se'`
    have hcl : closure ((fun t : ℝ => (0 : Euclid P) + t • e') '' Ioi 0) ⊆
        (fun s : ℝ => s • e') '' Ici 0 := by
      refine closure_minimal ?_ (isClosedMap_smul_left e' _ isClosed_Ici)
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, Ioi_subset_Ici_self ht, (zero_add _).symm⟩
    refine eq_empty_iff_forall_notMem.2 fun x ⟨⟨t, ht, hx⟩, hx'⟩ => ?_
    obtain ⟨s, hs, rfl⟩ := hcl hx'
    simp only [zero_add] at hx
    -- `te = se'` with `t > 0`, `s ≥ 0`: taking norms, `t = s`; cancelling `t`, `e = e'`
    have hts : t = s := by
      have h := congrArg norm hx
      rwa [norm_smul, norm_smul, he, he', mul_one, mul_one, Real.norm_of_nonneg (le_of_lt ht),
        Real.norm_of_nonneg hs] at h
    subst hts
    exact hne (smul_right_injective (Euclid P) (ne_of_gt ht) hx)
  -- the pieces `t ↦ 0 + te`, `t ∈ (0, ∞)`, with weights `m(e)`, indexed by `e ∈ F`
  obtain ⟨X, R, hRX, hX, hmeas⟩ := Submission.idtp_fons_odc_polygonal_current P F (fun _ => 0)
    (fun e => (e : Euclid P)) (fun _ => Ioi 0) (fun e => m e) (fun e => hF e e.2)
    (fun _ => isOpen_Ioi) fun j k hjk => by
      rw [hray j k (hF j j.2) (hF k k.2) fun h => hjk (Subtype.ext h), measure_empty]
  -- `C = X = τ(R)`; both formulas are the ones of the pieces, summed over `F`
  refine ⟨R, fun ω => ?_, fun A hA => ?_⟩
  · rw [← hRX ω, hC ω, hX ω, ← Finset.sum_coe_sort F]
    simp only [zero_add]
  · rw [hmeas A hA, ← Finset.sum_coe_sort F]
    simp only [zero_add]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
