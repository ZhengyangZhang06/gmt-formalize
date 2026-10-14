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

/-- **Gauss–Green measure** (Simon Ch. 2, 2.1–2.2 and Ch. 3, 4.1, with the Riesz representation
Ch. 1, 4.14): if `φ ↦ ∫_F div φ` is bounded on smooth fields with `|φ| ≤ 1` supported in each
compact `K ⊆ D`, it is `φ ↦ -∫ ⟨φ, ν⟩ dμ` on `C¹` fields compactly supported in `D`, for a measure
`μ` carried by `D`, finite on its compact subsets, and a Borel unit field `ν`.  For each coordinate
`i`, `g ↦ ±∫_F div (g eᵢ)` has positive part `f ↦ sup {±∫_F div (g eᵢ) : g smooth, 0 ≤ g ≤ f}` on
`C_c(D, ℝ≥0)` (additive by smooth approximation under a continuous ceiling), represented by
Riesz–Markov–Kakutani on the open subspace `D`; the `2(m + 1)` measures are densities against their
sum (Lebesgue decomposition), the density field is normalized and the measure pushed forward to
`ℝ^{m+1}`; `C¹` fields are reached by mollification. -/
theorem Submission.codim1_rdo_dg_gauss_green_measure : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))), IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
  intro m D F hD hF hbound
  classical
  -- the trace as a continuous linear functional and the functional `T φ = ∫_F div φ`
  obtain ⟨trc, htrc⟩ : ∃ trc : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ, ∀ A,
      trc A = LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ)), fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Euclid (m + 1) → Euclid (m + 1)) → ℝ,
      ∀ φ, T φ = ∫ y in F, trc (fderiv ℝ φ y) := ⟨_, fun _ => rfl⟩
  have hTeq : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = T φ := by
    intro φ
    rw [hT]
    simp only [htrc]
  have hbound' : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ,
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → T φ ≤ C := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound K hK hKD
    refine ⟨C, fun φ h1 h2 h3 h4 => ?_⟩
    rw [← hTeq φ]
    exact hC φ h1 h2 h3 h4
  suffices H : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ by
    obtain ⟨μ, ν, h1, h2, h3, h4, h5⟩ := H
    exact ⟨μ, ν, h1, h2, h3, h4, fun φ hφ hφc hφD => (hTeq φ).trans (h5 φ hφ hφc hφD)⟩
  -- Step 1: `T` is linear on `C¹` compactly supported fields, and locally bounded
  have hdiv_int : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun y => trc (fderiv ℝ φ y)) (volume.restrict F) := fun φ hφ hc =>
    ((trc.continuous.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_left trc.map_zero)).restrict
  have hT_add : ∀ φ ψ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → T (φ + ψ) = T φ + T ψ := by
    intro φ ψ hφ hφc hψ hψc
    simp only [hT]
    rw [← integral_add (hdiv_int φ hφ hφc) (hdiv_int ψ hψ hψc)]
    congr 1; ext y
    rw [fderiv_add (hφ.differentiable one_ne_zero y) (hψ.differentiable one_ne_zero y), map_add]
  have hT_smul : ∀ (c : ℝ) (φ : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 φ →
      T (c • φ) = c * T φ := by
    intro c φ hφ
    simp only [hT]
    rw [← integral_const_mul]
    congr 1; ext y
    rw [fderiv_const_smul (hφ.differentiable one_ne_zero y),
      map_smul, smul_eq_mul]
  have hT0 : T 0 = 0 := by simp [hT]
  have hbd : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → ∀ M : ℝ, 0 ≤ M → (∀ y, ‖φ y‖ ≤ M) → |T φ| ≤ C * M := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound' K hK hKD
    have hC0 : 0 ≤ C := by
      simpa [hT0] using hC 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
    refine ⟨C, hC0, fun φ hφ hφc hφK M hM hφM => ?_⟩
    rcases hM.eq_or_lt with rfl | hMpos
    · have : φ = 0 := funext fun y => norm_le_zero_iff.1 (hφM y)
      simp [this, hT0]
    · have hsm : ContDiff ℝ (⊤ : ℕ∞) (M⁻¹ • φ) := contDiff_const.smul hφ
      have hsK : tsupport (M⁻¹ • φ) ⊆ K :=
        (tsupport_smul_subset_right (fun _ => M⁻¹) φ).trans hφK
      have hsn : ∀ y, ‖(M⁻¹ • φ) y‖ ≤ 1 := fun y => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM)]
        calc M⁻¹ * ‖φ y‖ ≤ M⁻¹ * M := by gcongr; exact hφM y
          _ = 1 := inv_mul_cancel₀ hMpos.ne'
      have h1 := hC _ hsm (hφc.smul_left) hsK hsn
      have h2 := hC (-(M⁻¹ • φ)) hsm.neg (hφc.smul_left).neg (by rwa [tsupport_neg]) (fun y => by
        rw [Pi.neg_apply, norm_neg]; exact hsn y)
      rw [hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h1
      rw [show -(M⁻¹ • φ) = (-M⁻¹) • φ by rw [neg_smul],
        hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h2
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left h2 hM
        rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h1 hM
        rw [← mul_assoc, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
  -- compact subsets of `D` and compact supports on the subtype `D`
  have hsubK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D →
      IsCompact (Subtype.val ⁻¹' K : Set D) := fun K hK hKD =>
    Subtype.isCompact_iff.2 (by rwa [Subtype.image_preimage_coe, inter_eq_right.2 hKD])
  have hcs : ∀ (h : Euclid (m + 1) → ℝ) (K : Set (Euclid (m + 1))), IsCompact K →
      support h ⊆ K → HasCompactSupport h ∧ tsupport h ⊆ K := fun h K hK hhK =>
    ⟨hK.of_isClosed_subset (isClosed_tsupport h) (closure_minimal hhK hK.isClosed),
      closure_minimal hhK hK.isClosed⟩
  -- smooth approximation of `a` under a continuous ceiling `u` (smooth partitions of unity)
  have happrox : ∀ (u a : Euclid (m + 1) → ℝ), Continuous u → Continuous a →
      (∀ z, 0 ≤ a z ∧ a z ≤ u z) → ∀ ε : ℝ, 0 < ε →
      ∃ a' : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a' ∧
        ∀ z, 0 ≤ a' z ∧ a' z ≤ u z ∧ |a' z - a z| < ε := by
    intro u a hu ha hau ε hε
    have hloc : ∀ y : Euclid (m + 1), ∃ c : ℝ, ∀ᶠ z in 𝓝 y, c ∈ Icc 0 (u z) ∩ ball (a z) ε := by
      intro y
      refine ⟨max 0 (a y - ε / 2), ?_⟩
      have h1 : ∀ᶠ z in 𝓝 y, |a z - a y| < ε / 2 := by
        have := (ha.tendsto y).eventually (ball_mem_nhds (a y) (half_pos hε))
        filter_upwards [this] with z hz
        simpa [Real.dist_eq] using hz
      have h2 : ∀ᶠ z in 𝓝 y, max 0 (a y - ε / 2) ≤ u z := by
        by_cases hay : a y - ε / 2 ≤ 0
        · exact Eventually.of_forall fun z => by
            rw [max_eq_left hay]; exact (hau z).1.trans (hau z).2
        · rw [not_le] at hay
          have hlt : a y - ε / 2 < u y := by linarith [(hau y).2]
          have := (hu.tendsto y).eventually (lt_mem_nhds hlt)
          filter_upwards [this] with z hz
          rw [max_eq_right hay.le]; exact hz.le
      filter_upwards [h1, h2] with z hz1 hz2
      refine ⟨⟨le_max_left _ _, hz2⟩, ?_⟩
      rw [mem_ball, Real.dist_eq]
      have : |max 0 (a y - ε / 2) - a y| ≤ ε / 2 := by
        rcases le_total (a y - ε / 2) 0 with h | h
        · rw [max_eq_left h, zero_sub, abs_neg, abs_of_nonneg (hau y).1]; linarith
        · rw [max_eq_right h]; rw [show a y - ε / 2 - a y = -(ε / 2) by ring, abs_neg,
            abs_of_pos (half_pos hε)]
      calc |max 0 (a y - ε / 2) - a z| ≤ |max 0 (a y - ε / 2) - a y| + |a y - a z| :=
            abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by
          have : |a y - a z| < ε / 2 := by rw [abs_sub_comm]; exact hz1
          linarith
        _ = ε := by ring
    obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
      (modelWithCornersSelf ℝ (Euclid (m + 1))) (n := ⊤)
      (t := fun z => Icc 0 (u z) ∩ ball (a z) ε)
      (fun z => (convex_Icc _ _).inter (convex_ball _ _)) hloc
    refine ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z => ?_⟩
    have := hg z
    simp only [mem_inter_iff, mem_Icc, mem_ball, Real.dist_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- Step 2: the positive part of a locally bounded functional, via Riesz–Markov–Kakutani on `D`
  have hpos : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ : Measure D, IsFiniteMeasureOnCompacts μ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → (∀ y, 0 ≤ g y) →
          BddAbove (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) ∧
          ∫ x : D, g x ∂μ = sSup (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) := by
    intro S hSadd hSsmul hSbd
    have hS0 : S 0 = 0 := by simpa using hSsmul 0 0 contDiff_const
    -- `A u`: smooth `h`, `0 ≤ h ≤ u`, compactly supported in `D`; the functional is `sup S(A u)`
    obtain ⟨A, hA⟩ : ∃ A : (Euclid (m + 1) → ℝ) → Set (Euclid (m + 1) → ℝ), ∀ u h, h ∈ A u ↔
        (ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
          ∀ y, 0 ≤ h y ∧ h y ≤ u y) :=
      ⟨fun u => {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ u y}, fun _ _ => Iff.rfl⟩
    have hA0 : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → (0 : Euclid (m + 1) → ℝ) ∈ A u :=
      fun u hu => (hA u 0).2 ⟨contDiff_const, HasCompactSupport.zero, by simp,
        fun y => ⟨le_rfl, hu y⟩⟩
    have hAsupp : ∀ u h, h ∈ A u → support h ⊆ support u := by
      intro u h hh y hy huy
      obtain ⟨-, -, -, h4⟩ := (hA u h).1 hh
      have := h4 y
      rw [huy] at this
      exact hy (le_antisymm this.2 this.1)
    have hbddA : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → BddAbove (S '' A u) := by
      intro u hu hu0 K hK hKD huK
      obtain ⟨C, hC⟩ := hSbd K hK hKD
      obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support (hcs u K hK huK).1
      refine ⟨C * M, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨h1, h2, -, h4⟩ := (hA u h).1 hh
      refine hC h h1 h2 (hcs h K hK ((hAsupp u h hh).trans huK)).2 M
        ((norm_nonneg _).trans (hM 0)) fun y => ?_
      rw [abs_of_nonneg (h4 y).1]
      exact (h4 y).2.trans ((le_abs_self _).trans (hM y))
    have hle_sup : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ h ∈ A u, S h ≤ sSup (S '' A u) :=
      fun u hu hu0 K hK hKD huK h hh => le_csSup (hbddA u hu hu0 K hK hKD huK) ⟨h, hh, rfl⟩
    have hsup_le : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → ∀ c : ℝ,
        (∀ h ∈ A u, S h ≤ c) → sSup (S '' A u) ≤ c := fun u hu c hc =>
      csSup_le ⟨S 0, 0, hA0 u hu, rfl⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
    -- additivity
    have hadd : ∀ u₁ u₂ : Euclid (m + 1) → ℝ, Continuous u₁ → (∀ y, 0 ≤ u₁ y) →
        Continuous u₂ → (∀ y, 0 ≤ u₂ y) → ∀ K₁ K₂, IsCompact K₁ → K₁ ⊆ D → support u₁ ⊆ K₁ →
        IsCompact K₂ → K₂ ⊆ D → support u₂ ⊆ K₂ →
        sSup (S '' A (u₁ + u₂)) = sSup (S '' A u₁) + sSup (S '' A u₂) := by
      intro u₁ u₂ hu₁ hu₁0 hu₂ hu₂0 K₁ K₂ hK₁ hK₁D hu₁K hK₂ hK₂D hu₂K
      have hu0 : ∀ y, 0 ≤ (u₁ + u₂) y := fun y => add_nonneg (hu₁0 y) (hu₂0 y)
      have huK : support (u₁ + u₂) ⊆ K₁ ∪ K₂ := fun y hy => by
        by_contra hy'
        apply hy
        have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
        have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
        rw [Pi.add_apply, notMem_support.1 (fun h => hy1 (hu₁K h)),
          notMem_support.1 (fun h => hy2 (hu₂K h)), add_zero]
      have hKK : IsCompact (K₁ ∪ K₂) := hK₁.union hK₂
      have hKKD : K₁ ∪ K₂ ⊆ D := union_subset hK₁D hK₂D
      apply le_antisymm
      · apply hsup_le (u₁ + u₂) hu0
        intro g hg
        obtain ⟨hg1, hg2, hg3, hg4⟩ := (hA (u₁ + u₂) g).1 hg
        obtain ⟨C, hC⟩ := hSbd (K₁ ∪ K₂) hKK hKKD
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨δ, hδ0, hCδ⟩ : ∃ δ : ℝ, 0 < δ ∧ C * (2 * δ) ≤ ε := by
          refine ⟨ε / (2 * (|C| + 1)), div_pos hε (by positivity), ?_⟩
          have hpos' : (0 : ℝ) < |C| + 1 := by positivity
          have : C * (2 * (ε / (2 * (|C| + 1)))) = C * ε / (|C| + 1) := by
            field_simp
          rw [this, div_le_iff₀ hpos', mul_comm ε]
          exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right
            zero_le_one)) hε.le
        have ha : Continuous fun y => min (g y) (u₁ y) := hg1.continuous.min hu₁
        obtain ⟨a', ha'1, ha'2⟩ := happrox u₁ (fun y => min (g y) (u₁ y)) hu₁ ha
          (fun z => ⟨le_min (hg4 z).1 (hu₁0 z), min_le_right _ _⟩) δ hδ0
        have hb : ∀ z, 0 ≤ g z - min (g z) (u₁ z) ∧ g z - min (g z) (u₁ z) ≤ u₂ z := by
          intro z
          refine ⟨sub_nonneg.2 (min_le_left _ _), ?_⟩
          have h' : g z ≤ u₁ z + u₂ z := (hg4 z).2
          rcases le_total (g z) (u₁ z) with h | h
          · rw [min_eq_left h, sub_self]; exact hu₂0 z
          · rw [min_eq_right h]; linarith
        obtain ⟨b', hb'1, hb'2⟩ := happrox u₂ (fun y => g y - min (g y) (u₁ y)) hu₂
          (hg1.continuous.sub ha) hb δ hδ0
        have ha'K : support a' ⊆ K₁ := fun y hy => hu₁K fun h => hy (by
          have := ha'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hb'K : support b' ⊆ K₂ := fun y hy => hu₂K fun h => hy (by
          have := hb'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hcsa' := hcs a' K₁ hK₁ ha'K
        have hcsb' := hcs b' K₂ hK₂ hb'K
        have ha'A : a' ∈ A u₁ := (hA u₁ a').2 ⟨ha'1, hcsa'.1, hcsa'.2.trans hK₁D,
          fun z => ⟨(ha'2 z).1, (ha'2 z).2.1⟩⟩
        have hb'A : b' ∈ A u₂ := (hA u₂ b').2 ⟨hb'1, hcsb'.1, hcsb'.2.trans hK₂D,
          fun z => ⟨(hb'2 z).1, (hb'2 z).2.1⟩⟩
        have hgK : support g ⊆ K₁ ∪ K₂ := (hAsupp (u₁ + u₂) g hg).trans huK
        have hrK : support (g - a' - b') ⊆ K₁ ∪ K₂ := fun y hy => by
          by_contra hy'
          apply hy
          have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
          have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
          rw [Pi.sub_apply, Pi.sub_apply, notMem_support.1 (fun h => hy' (hgK h)),
            notMem_support.1 (fun h => hy1 (ha'K h)), notMem_support.1 (fun h => hy2 (hb'K h)),
            sub_zero, sub_zero]
        have hrcs := hcs (g - a' - b') (K₁ ∪ K₂) hKK hrK
        have hr1 : ContDiff ℝ (⊤ : ℕ∞) (g - a' - b') := (hg1.sub ha'1).sub hb'1
        have hrb : ∀ y, |(g - a' - b') y| ≤ 2 * δ := fun y => by
          have h1 := (ha'2 y).2.2
          have h2 := (hb'2 y).2.2
          rw [Pi.sub_apply, Pi.sub_apply]
          have e : g y - a' y - b' y =
              -((a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))) := by ring
          rw [e, abs_neg]
          calc |(a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))|
              ≤ |a' y - min (g y) (u₁ y)| + |b' y - (g y - min (g y) (u₁ y))| :=
                abs_add_le _ _
            _ ≤ 2 * δ := by linarith
        have hSr := hC (g - a' - b') hr1 hrcs.1 hrcs.2 (2 * δ) (by positivity) hrb
        have hdec : S ((a' + b') + (g - a' - b')) = S a' + S b' + S (g - a' - b') := by
          rw [hSadd (a' + b') (g - a' - b') (ha'1.add hb'1) (hcsa'.1.add hcsb'.1) hr1 hrcs.1,
            hSadd a' b' ha'1 hcsa'.1 hb'1 hcsb'.1]
        rw [show (a' + b') + (g - a' - b') = g by abel] at hdec
        have h1 := hle_sup u₁ hu₁ hu₁0 K₁ hK₁ hK₁D hu₁K a' ha'A
        have h2 := hle_sup u₂ hu₂ hu₂0 K₂ hK₂ hK₂D hu₂K b' hb'A
        linarith
      · have key : ∀ h₁ ∈ A u₁, ∀ h₂ ∈ A u₂, S h₁ + S h₂ ≤ sSup (S '' A (u₁ + u₂)) := by
          intro h₁ hh₁ h₂ hh₂
          obtain ⟨a1, a2, a3, a4⟩ := (hA u₁ h₁).1 hh₁
          obtain ⟨b1, b2, b3, b4⟩ := (hA u₂ h₂).1 hh₂
          rw [← hSadd h₁ h₂ a1 a2 b1 b2]
          have hmem : h₁ + h₂ ∈ A (u₁ + u₂) := (hA (u₁ + u₂) (h₁ + h₂)).2 ⟨a1.add b1,
            a2.add b2, (tsupport_add h₁ h₂).trans (union_subset a3 b3),
            fun y => ⟨add_nonneg (a4 y).1 (b4 y).1, add_le_add (a4 y).2 (b4 y).2⟩⟩
          exact hle_sup (u₁ + u₂) (hu₁.add hu₂) hu0 (K₁ ∪ K₂) hKK hKKD huK (h₁ + h₂) hmem
        have : sSup (S '' A u₁) ≤ sSup (S '' A (u₁ + u₂)) - sSup (S '' A u₂) := by
          apply hsup_le u₁ hu₁0
          intro h₁ hh₁
          have : sSup (S '' A u₂) ≤ sSup (S '' A (u₁ + u₂)) - S h₁ := by
            apply hsup_le u₂ hu₂0
            intro h₂ hh₂
            have := key h₁ hh₁ h₂ hh₂
            linarith
          linarith
        linarith
    -- homogeneity
    have hsmul : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ c : ℝ, 0 ≤ c →
        sSup (S '' A (c • u)) = c * sSup (S '' A u) := by
      intro u hu hu0 K hK hKD huK c hc
      have hcu0 : ∀ y, 0 ≤ (c • u) y := fun y => mul_nonneg hc (hu0 y)
      have hcuK : support (c • u) ⊆ K := (support_const_smul_subset c u).trans huK
      have hcuc : Continuous (c • u) := hu.const_smul c
      rcases hc.eq_or_lt with hc0 | hcpos
      · subst hc0
        rw [zero_mul]
        apply le_antisymm
        · apply hsup_le ((0 : ℝ) • u) hcu0
          intro h hh
          obtain ⟨-, -, -, h4⟩ := (hA ((0 : ℝ) • u) h).1 hh
          have : h = 0 := funext fun y => le_antisymm (by
            have := (h4 y).2
            rwa [Pi.smul_apply, zero_smul] at this) (h4 y).1
          rw [this, hS0]
        · have h0 := hle_sup ((0 : ℝ) • u) hcuc hcu0 K hK hKD hcuK 0 (hA0 ((0 : ℝ) • u) hcu0)
          rwa [hS0] at h0
      · apply le_antisymm
        · apply hsup_le (c • u) hcu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA (c • u) h).1 hh
          have hmem : c⁻¹ • h ∈ A u := (hA u (c⁻¹ • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c⁻¹) h2,
            (tsupport_smul_subset_right (fun _ => c⁻¹) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg (inv_nonneg.2 hc) (h4 y).1, by
                rw [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hcpos]
                have := (h4 y).2
                rwa [Pi.smul_apply, smul_eq_mul] at this⟩⟩
          have := hle_sup u hu hu0 K hK hKD huK (c⁻¹ • h) hmem
          have e : S h = c * S (c⁻¹ • h) := by
            rw [hSsmul c⁻¹ h h1, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc
        · rw [← le_div_iff₀' hcpos]
          apply hsup_le u hu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA u h).1 hh
          have hmem : c • h ∈ A (c • u) := (hA (c • u) (c • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c) h2,
            (tsupport_smul_subset_right (fun _ => c) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg hc (h4 y).1, by
                rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
                exact mul_le_mul_of_nonneg_left (h4 y).2 hc⟩⟩
          have := hle_sup (c • u) hcuc hcu0 K hK hKD hcuK (c • h) hmem
          rw [hSsmul c h h1] at this
          rw [le_div_iff₀' hcpos]
          exact this
    -- extension by zero of `f ∈ C_c(D, ℝ≥0)`; `f ↦ sup S(A (ext f))` is `ℝ≥0`-linear
    obtain ⟨ext, hext⟩ : ∃ ext : CompactlySupportedContinuousMap D NNReal →
        Euclid (m + 1) → ℝ, ∀ f y, ext f y = if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0 :=
      ⟨fun f y => if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0, fun _ _ => rfl⟩
    have hextK : ∀ f : CompactlySupportedContinuousMap D NNReal,
        IsCompact (Subtype.val '' tsupport f) ∧ Subtype.val '' tsupport f ⊆ D := fun f =>
      ⟨f.hasCompactSupport.image continuous_subtype_val, by rintro _ ⟨x, -, rfl⟩; exact x.2⟩
    have hext_supp : ∀ f : CompactlySupportedContinuousMap D NNReal,
        support (ext f) ⊆ Subtype.val '' tsupport f := by
      intro f y hy
      rw [mem_support, hext] at hy
      by_cases h : y ∈ D
      · rw [dite_eq_left h] at hy
        refine ⟨⟨y, h⟩, subset_tsupport _ ?_, rfl⟩
        intro h0
        apply hy
        rw [h0]
        rfl
      · rw [dite_eq_right h] at hy
        exact absurd rfl hy
    have hext_nonneg : ∀ f y, 0 ≤ ext f y := by
      intro f y
      rw [hext]
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl
    have hext_cont : ∀ f : CompactlySupportedContinuousMap D NNReal, Continuous (ext f) := by
      intro f
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ Subtype.val '' tsupport f
      · have hyD : y ∈ D := (hextK f).2 hy
        have hcont : ContinuousOn (ext f) D := by
          rw [continuousOn_iff_continuous_domRestrict]
          have : D.domRestrict (ext f) = fun x : D => ((f x : NNReal) : ℝ) := by
            funext x
            rw [Set.domRestrict_apply, hext, dite_eq_left x.2]
          rw [this]
          exact NNReal.continuous_coe.comp f.continuous
        exact hcont.continuousAt (hD.mem_nhds hyD)
      · have : ext f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [(hextK f).1.isClosed.isOpen_compl.mem_nhds hy] with z hz
          by_contra hne
          exact hz (hext_supp f hne)
        exact continuousAt_const.congr this.symm
    have hext_add : ∀ f g : CompactlySupportedContinuousMap D NNReal,
        ext (f + g) = ext f + ext g := by
      intro f g
      funext y
      simp only [hext, Pi.add_apply]
      split_ifs
      · simp
      · simp
    have hext_smul : ∀ (c : NNReal) (f : CompactlySupportedContinuousMap D NNReal),
        ext (c • f) = (c : ℝ) • ext f := by
      intro c f
      funext y
      simp only [hext, Pi.smul_apply]
      split_ifs
      · simp
      · simp
    have hΛ0 : ∀ f : CompactlySupportedContinuousMap D NNReal, 0 ≤ sSup (S '' A (ext f)) :=
      fun f => by
        have := hle_sup (ext f) (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2
          (hext_supp f) 0 (hA0 _ (hext_nonneg f))
        rwa [hS0] at this
    let Λn : CompactlySupportedContinuousMap D NNReal →ₗ[NNReal] NNReal :=
      { toFun := fun f => ⟨sSup (S '' A (ext f)), hΛ0 f⟩
        map_add' := fun f g => by
          apply NNReal.eq
          change sSup (S '' A (ext (f + g))) = sSup (S '' A (ext f)) + sSup (S '' A (ext g))
          rw [hext_add]
          exact hadd _ _ (hext_cont f) (hext_nonneg f) (hext_cont g) (hext_nonneg g) _ _
            (hextK f).1 (hextK f).2 (hext_supp f) (hextK g).1 (hextK g).2 (hext_supp g)
        map_smul' := fun c f => by
          apply NNReal.eq
          change sSup (S '' A (ext (c • f))) = (c : ℝ) * sSup (S '' A (ext f))
          rw [hext_smul]
          exact hsmul _ (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2 (hext_supp f)
            c c.2 }
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    refine ⟨RealRMK.rieszMeasure (CompactlySupportedContinuousMap.toRealPositiveLinear Λn),
      inferInstance, ?_⟩
    intro g hg hgc hgD hg0
    have hAg : A g = {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ g y} := by
      ext h
      exact hA g h
    rw [← hAg]
    refine ⟨hbddA g hg.continuous hg0 (tsupport g) hgc hgD (subset_tsupport g), ?_⟩
    have hgcs : HasCompactSupport (fun x : D => Real.toNNReal (g x)) := by
      refine (hsubK _ hgc hgD).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal ?_ ((isClosed_tsupport g).preimage continuous_subtype_val))
      intro x hx
      apply subset_tsupport g
      intro h0
      apply hx
      simp [h0]
    let fg : CompactlySupportedContinuousMap D NNReal :=
      ⟨⟨fun x => Real.toNNReal (g x),
        continuous_real_toNNReal.comp (hg.continuous.comp continuous_subtype_val)⟩, hgcs⟩
    have hfg : ext fg = g := by
      funext y
      rw [hext]
      by_cases h : y ∈ D
      · rw [dite_eq_left h]
        exact Real.coe_toNNReal _ (hg0 y)
      · rw [dite_eq_right h]
        exact (image_eq_zero_of_notMem_tsupport (fun h' => h (hgD h'))).symm
    calc ∫ x : D, g x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn))
        = ∫ x : D, (CompactlySupportedContinuousMap.toReal fg) x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn)) := by
          congr 1
          funext x
          rw [CompactlySupportedContinuousMap.toReal_apply]
          exact (Real.coe_toNNReal _ (hg0 x)).symm
      _ = CompactlySupportedContinuousMap.toRealPositiveLinear Λn
          (CompactlySupportedContinuousMap.toReal fg) := RealRMK.integral_rieszMeasure _ _
      _ = (Λn fg : ℝ) := by rw [CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
      _ = sSup (S '' A (ext fg)) := rfl
      _ = sSup (S '' A g) := by rw [hfg]
  -- Step 3: Jordan decomposition of a locally bounded functional on smooth functions
  have hcsD : ∀ f : Euclid (m + 1) → ℝ, HasCompactSupport f → tsupport f ⊆ D →
      HasCompactSupport (fun x : D => f x) := by
    intro f hfc hfD
    refine (hsubK _ hfc hfD).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ?_ ((isClosed_tsupport f).preimage continuous_subtype_val))
    intro x hx
    exact subset_tsupport f hx
  have hintD : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ → ∀ f : Euclid (m + 1) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ D → Integrable (fun x : D => f x) μ := by
    intro μ hμ f hf hfc hfD
    exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport (hcsD f hfc hfD)
  have hjordan : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧ IsFiniteMeasureOnCompacts μ₂ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
    intro S hSadd hSsmul hSbd
    obtain ⟨μ₁, hμ₁, h₁⟩ := hpos S hSadd hSsmul hSbd
    have hSneg : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → S (-g) = -S g :=
      fun g hg => by
        rw [show -g = (-1 : ℝ) • g by rw [neg_one_smul], hSsmul (-1) g hg, neg_one_mul]
    obtain ⟨μ₂, hμ₂, h₂⟩ := hpos (fun g => -S g)
      (fun g h hg hgc hh hhc => by rw [hSadd g h hg hgc hh hhc, neg_add])
      (fun c g hg => by rw [hSsmul c g hg, mul_neg])
      (fun K hK hKD => by
        obtain ⟨C, hC⟩ := hSbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (-g) hg.neg hgc.neg (by rwa [tsupport_neg]) M hM
          (fun y => by rw [Pi.neg_apply, abs_neg]; exact hgM y)
        rwa [hSneg g hg] at this)
    refine ⟨μ₁, μ₂, hμ₁, hμ₂, ?_⟩
    have hnn : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ D → (∀ y, 0 ≤ g y) → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro g hg hgc hgD hg0
      obtain ⟨hb₁, he₁⟩ := h₁ g hg hgc hgD hg0
      obtain ⟨hb₂, he₂⟩ := h₂ g hg hgc hgD hg0
      rw [he₁, he₂]
      set Ag := {h : Euclid (m + 1) → ℝ | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y} with hAg
      have hgA : g ∈ Ag := ⟨hg, hgc, hgD, fun y => ⟨hg0 y, le_rfl⟩⟩
      have hsubA : ∀ h ∈ Ag, g - h ∈ Ag := fun h hh =>
        ⟨hg.sub hh.1, hgc.sub hh.2.1, (tsupport_sub g h).trans (union_subset hgD hh.2.2.1),
          fun y => ⟨sub_nonneg.2 (hh.2.2.2 y).2, sub_le_self _ (hh.2.2.2 y).1⟩⟩
      have hdec : ∀ h ∈ Ag, S g = S (g - h) + S h := fun h hh => by
        rw [← hSadd (g - h) h (hg.sub hh.1) (hgc.sub hh.2.1) hh.1 hh.2.1, sub_add_cancel]
      have hne : Ag.Nonempty := ⟨g, hgA⟩
      have i1 : sSup ((fun g => -S g) '' Ag) ≤ sSup (S '' Ag) - S g := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₁ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      have i2 : sSup (S '' Ag) ≤ S g + sSup ((fun g => -S g) '' Ag) := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₂ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      linarith
    -- a general `g`: add `M χ`, with `|g| ≤ M` and a smooth cutoff `χ = 1` on `tsupport g`
    intro g hg hgc hgD
    obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hgc hD hgD
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := tsupport g)) (isClosed_tsupport g)
      (self_subset_thickening hδ _)
    have hχK : support χ ⊆ cthickening δ (tsupport g) :=
      hχs ▸ thickening_subset_cthickening δ _
    have hχcs := hcs χ (cthickening δ (tsupport g)) (IsCompact.cthickening hgc) hχK
    obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (M • χ) := contDiff_const.smul hχ
    have hψcs : HasCompactSupport (M • χ) := HasCompactSupport.smul_left (f := fun _ => M) hχcs.1
    have hψD : tsupport (M • χ) ⊆ D :=
      (tsupport_smul_subset_right (fun _ => M) χ).trans (hχcs.2.trans hδD)
    have hψ0 : ∀ y, 0 ≤ (M • χ) y := fun y => by
      rw [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hM0 (hχ01 y).1
    have hgψ0 : ∀ y, 0 ≤ (g + M • χ) y := fun y => by
      by_cases hy : y ∈ tsupport g
      · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hχ1 y).1 hy, mul_one]
        have := hM y
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (g y)]
      · rw [Pi.add_apply, image_eq_zero_of_notMem_tsupport hy, zero_add]; exact hψ0 y
    have e1 := hnn (g + M • χ) (hg.add hψ) (hgc.add hψcs)
      ((tsupport_add g (M • χ)).trans (union_subset hgD hψD)) hgψ0
    have e2 := hnn (M • χ) hψ hψcs hψD hψ0
    rw [hSadd g (M • χ) hg hgc hψ hψcs] at e1
    have i1 : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ →
        ∫ x : D, (g + M • χ) x ∂μ = ∫ x : D, g x ∂μ + ∫ x : D, (M • χ) x ∂μ := by
      intro μ hμ
      simp only [Pi.add_apply]
      exact integral_add (hintD μ hμ g hg.continuous hgc hgD)
        (hintD μ hμ (M • χ) hψ.continuous hψcs hψD)
    rw [i1 μ₁ hμ₁, i1 μ₂ hμ₂] at e1
    linarith
  -- Step 4: representation of `T` on smooth fields
  have hsm_rep : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
    -- the standard basis
    obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)),
        b = EuclideanSpace.basisFun (Fin (m + 1)) ℝ := ⟨_, rfl⟩
    have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.norm_eq_one i
    have hbinner : ∀ (x : Euclid (m + 1)) (i : Fin (m + 1)), inner ℝ x (b i) = x i := by
      intro x i; rw [hb]; exact EuclideanSpace.inner_basisFun_real _ x i
    have hbsum : ∀ x : Euclid (m + 1), ∑ i, x i • b i = x := by
      intro x; rw [hb]; exact (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x
    -- coordinate functionals
    have hcomp : ∀ i : Fin (m + 1), ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧
        IsFiniteMeasureOnCompacts μ₂ ∧ ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          HasCompactSupport g → tsupport g ⊆ D →
          T (fun y => g y • b i) = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro i
      have hsm : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ContDiff ℝ (⊤ : ℕ∞) (fun y => g y • b i) := fun g hg => hg.smul contDiff_const
      have hcs1 : ∀ g : Euclid (m + 1) → ℝ, HasCompactSupport g →
          HasCompactSupport (fun y => g y • b i) := fun g hg =>
        hg.comp_left (g := fun r : ℝ => r • b i) (zero_smul ℝ (b i))
      apply hjordan (fun g => T (fun y => g y • b i))
      · intro g h hg hgc hh hhc
        have e : (fun y => (g + h) y • b i) = (fun y => g y • b i) + (fun y => h y • b i) := by
          funext y; rw [Pi.add_apply, Pi.add_apply, add_smul]
        change T (fun y => (g + h) y • b i) = T (fun y => g y • b i) + T (fun y => h y • b i)
        rw [e, hT_add _ _ ((hsm g hg).of_le (by exact_mod_cast le_top)) (hcs1 g hgc)
          ((hsm h hh).of_le (by exact_mod_cast le_top)) (hcs1 h hhc)]
      · intro c g hg
        have e : (fun y => (c • g) y • b i) = c • (fun y => g y • b i) := by
          funext y; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]
        change T (fun y => (c • g) y • b i) = c * T (fun y => g y • b i)
        rw [e, hT_smul c _ ((hsm g hg).of_le (by exact_mod_cast le_top))]
      · intro K hK hKD
        obtain ⟨C, -, hC⟩ := hbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (fun y => g y • b i) (hsm g hg) (hcs1 g hgc)
          ((tsupport_smul_subset_left g (fun _ => b i)).trans hgK) M hM (fun y => by
            rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs]; exact hgM y)
        exact (le_abs_self _).trans this
    choose μ₁ μ₂ hμ₁ hμ₂ hrep using hcomp
    -- coordinates of a field
    have hcoord_sm : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y i) := fun φ i hφ =>
      (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hφ
    have hcoord_cs : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        HasCompactSupport φ → HasCompactSupport (fun y => φ y i) := fun φ i hφ =>
      hφ.comp_left (g := fun v : Euclid (m + 1) => v i) rfl
    have hcoord_ts : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        tsupport (fun y => φ y i) ⊆ tsupport φ := fun φ i =>
      tsupport_comp_subset (g := fun v : Euclid (m + 1) => v i) rfl φ
    have hTdecomp : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → T φ = ∑ i, T (fun y => φ y i • b i) := by
      intro φ hφ hφc
      have key : ∀ s : Finset (Fin (m + 1)),
          ContDiff ℝ 1 (∑ i ∈ s, fun y => φ y i • b i) ∧
          HasCompactSupport (∑ i ∈ s, fun y => φ y i • b i) ∧
          T (∑ i ∈ s, fun y => φ y i • b i) = ∑ i ∈ s, T (fun y => φ y i • b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          exact ⟨contDiff_const, HasCompactSupport.zero, hT0⟩
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          have h1 : ContDiff ℝ 1 (fun y => φ y j • b j) :=
            ((hcoord_sm φ j hφ).smul contDiff_const).of_le (by exact_mod_cast le_top)
          have h2 : HasCompactSupport (fun y => φ y j • b j) :=
            (hcoord_cs φ j hφc).comp_left (g := fun r : ℝ => r • b j) (zero_smul ℝ _)
          exact ⟨h1.add ih.1, h2.add ih.2.1, by rw [hT_add _ _ h1 h2 ih.1 ih.2.1, ih.2.2]⟩
      have hφeq : φ = ∑ i, fun y => φ y i • b i := by
        funext y
        rw [Finset.sum_apply]
        exact (hbsum (φ y)).symm
      conv_lhs => rw [hφeq]
      exact (key Finset.univ).2.2
    -- the dominating measure on `D`
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    obtain ⟨μD, hμD⟩ : ∃ μD : Measure D, μD = ∑ i, (μ₁ i + μ₂ i) := ⟨_, rfl⟩
    have hμDK : ∀ K : Set D, IsCompact K → μD K < ∞ := by
      intro K hK
      rw [hμD, Measure.finsetSum_apply]
      refine ENNReal.sum_lt_top.2 fun i _ => ?_
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨(hμ₁ i).lt_top_of_isCompact hK, (hμ₂ i).lt_top_of_isCompact hK⟩
    have : IsFiniteMeasureOnCompacts μD := ⟨hμDK⟩
    have hRN : ∀ ν : Measure D, IsFiniteMeasureOnCompacts ν → ν ≤ μD →
        ∃ r : D → ℝ≥0∞, Measurable r ∧ (∀ᵐ x ∂μD, r x < ∞) ∧ ν = μD.withDensity r := by
      intro ν hν hle
      have := hν
      refine ⟨ν.rnDeriv μD, Measure.measurable_rnDeriv _ _, Measure.rnDeriv_lt_top _ _, ?_⟩
      have := Measure.haveLebesgueDecomposition_add ν μD
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        zero_add] at this
    have hle₁ : ∀ i, μ₁ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_self_add
    have hle₂ : ∀ i, μ₂ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_add_self
    choose r₁ hr₁m hr₁lt hr₁ using fun i => hRN (μ₁ i) (hμ₁ i) (hle₁ i)
    choose r₂ hr₂m hr₂lt hr₂ using fun i => hRN (μ₂ i) (hμ₂ i) (hle₂ i)
    -- the density field `H`
    obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → D → ℝ, ∀ i x, c i x = (r₁ i x).toReal - (r₂ i x).toReal :=
      ⟨fun i x => (r₁ i x).toReal - (r₂ i x).toReal, fun _ _ => rfl⟩
    have hcm : ∀ i, Measurable (c i) := fun i => by
      have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
      rw [this]
      exact (hr₁m i).ennreal_toReal.sub (hr₂m i).ennreal_toReal
    obtain ⟨H, hH⟩ : ∃ H : D → Euclid (m + 1), ∀ x, H x = ∑ i, c i x • b i :=
      ⟨fun x => ∑ i, c i x • b i, fun _ => rfl⟩
    have hHm : Measurable H := by
      have : H = fun x => ∑ i, c i x • b i := funext hH
      rw [this]
      exact Finset.measurable_sum _ fun i _ => (hcm i).smul_const (b i)
    have hrepD : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = ∫ x : D, inner ℝ (φ x) (H x) ∂μD := by
      intro φ hφ hφc hφD
      rw [hTdecomp φ hφ hφc]
      have hterm : ∀ i, Integrable (fun x : D => c i x * φ x i) μD ∧
          T (fun y => φ y i • b i) = ∫ x : D, c i x * φ x i ∂μD := by
        intro i
        have hgi := hcoord_sm φ i hφ
        have hgc := hcoord_cs φ i hφc
        have hgD := (hcoord_ts φ i).trans hφD
        have I₁ := hintD (μ₁ i) (hμ₁ i) (fun y => φ y i) hgi.continuous hgc hgD
        have I₂ := hintD (μ₂ i) (hμ₂ i) (fun y => φ y i) hgi.continuous hgc hgD
        rw [hrep i (fun y => φ y i) hgi hgc hgD]
        rw [hr₁ i] at I₁ ⊢
        rw [hr₂ i] at I₂ ⊢
        have J₁ := (integrable_withDensity_iff_integrable_smul' (hr₁m i) (hr₁lt i)).1 I₁
        have J₂ := (integrable_withDensity_iff_integrable_smul' (hr₂m i) (hr₂lt i)).1 I₂
        rw [integral_withDensity_eq_integral_toReal_smul (hr₁m i) (hr₁lt i),
          integral_withDensity_eq_integral_toReal_smul (hr₂m i) (hr₂lt i), ← integral_sub J₁ J₂]
        have e : (fun x : D => c i x * φ x i) =
            fun x : D => (r₁ i x).toReal • φ x i - (r₂ i x).toReal • φ x i := by
          funext x
          rw [hc, smul_eq_mul, smul_eq_mul, sub_mul]
        rw [e]
        exact ⟨J₁.sub J₂, rfl⟩
      rw [Finset.sum_congr rfl fun i _ => (hterm i).2,
        ← integral_finsetSum _ fun i _ => (hterm i).1]
      congr 1
      funext x
      rw [hH, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, hbinner]
    -- normalization to a unit field
    obtain ⟨ν', hν'⟩ : ∃ ν' : D → Euclid (m + 1), ∀ x,
        ν' x = if H x = 0 then b 0 else ‖H x‖⁻¹ • H x :=
      ⟨fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x, fun _ => rfl⟩
    have hν'm : Measurable ν' := by
      have : ν' = fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x := funext hν'
      rw [this]
      exact Measurable.ite (measurableSet_eq_fun hHm measurable_const) measurable_const
        (hHm.norm.inv.smul hHm)
    have hν'1 : ∀ x, ‖ν' x‖ = 1 := by
      intro x
      rw [hν']
      split_ifs with h
      · exact hb1 0
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    have hHν : ∀ (v : Euclid (m + 1)) (x : D),
        (‖H x‖₊ : ℝ) • inner ℝ v (ν' x) = inner ℝ v (H x) := by
      intro v x
      rw [hν', coe_nnnorm, smul_eq_mul]
      split_ifs with h
      · rw [h, norm_zero, zero_mul, inner_zero_right]
      · rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_mul]
    obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure D,
        μ' = μD.withDensity (fun x => ((‖H x‖₊ : NNReal) : ℝ≥0∞)) := ⟨_, rfl⟩
    have hμ'K : ∀ K : Set D, IsCompact K → μ' K < ∞ := by
      intro K hK
      have hKm : MeasurableSet K := hK.measurableSet
      have hlt : ∀ (r : D → ℝ≥0∞) (ν : Measure D), Measurable r → IsFiniteMeasureOnCompacts ν →
          ν = μD.withDensity r → IntegrableOn (fun x => (r x).toReal) K μD := by
        intro r ν hr hν hνr
        apply integrable_toReal_of_lintegral_ne_top hr.aemeasurable
        rw [← withDensity_apply _ hKm, ← hνr]
        exact (hν.lt_top_of_isCompact hK).ne
      have hci : ∀ i, IntegrableOn (c i) K μD := by
        intro i
        have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
        rw [this]
        exact (hlt _ _ (hr₁m i) (hμ₁ i) (hr₁ i)).sub (hlt _ _ (hr₂m i) (hμ₂ i) (hr₂ i))
      have hHK : IntegrableOn H K μD := by
        have : H = fun x => ∑ i, c i x • b i := funext hH
        rw [this]
        exact integrable_finsetSum _ fun i _ => (hci i).smul_const (b i)
      rw [hμ', withDensity_apply _ hKm]
      exact hHK.hasFiniteIntegral
    -- push forward to `ℝ^{m+1}`
    refine ⟨Measure.map Subtype.val μ', fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.map_apply measurable_subtype_coe hD.measurableSet.compl]
      have : (Subtype.val ⁻¹' Dᶜ : Set D) = ∅ := by
        ext x
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
        exact x.2
      rw [this, measure_empty]
    · intro K hK hKD
      rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
      exact (hμ'K _ (hsubK K hK hKD)).ne
    · exact Measurable.dite hν'm.neg measurable_const hD.measurableSet
    · intro y
      by_cases hy : y ∈ D
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_left hy, norm_neg, hν'1]
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_right hy, hb1]
    · intro φ hφ hφc hφD
      rw [(MeasurableEmbedding.subtype_coe hD.measurableSet).integral_map]
      have e : (fun x : D => inner ℝ (φ x) ((fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0) x))
          = fun x : D => -inner ℝ (φ x) (ν' x) := by
        funext x
        show inner ℝ (φ x) (if hy : (x : Euclid (m + 1)) ∈ D then -ν' ⟨x, hy⟩ else b 0) =
          -inner ℝ (φ x) (ν' x)
        rw [dite_eq_left x.2, Subtype.coe_eta, inner_neg_right]
      rw [e, integral_neg, neg_neg, hrepD φ hφ hφc hφD, hμ',
        integral_withDensity_eq_integral_smul hHm.nnnorm]
      congr 1
      funext x
      rw [NNReal.smul_def]
      exact (hHν (φ x) x).symm
  obtain ⟨μ, ν, hμD, hμK, hνm, hν1, hsmooth⟩ := hsm_rep
  refine ⟨μ, ν, hμD, hμK, hνm, hν1, ?_⟩
  -- Step 5: `C¹` fields, by mollification
  -- normalized mollifiers
  have hmoll : ∀ r : ℝ, 0 < r → ∃ ρ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball 0 r := by
    intro r hr
    let B : ContDiffBump (0 : Euclid (m + 1)) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hBs : HasCompactSupport B := B.hasCompactSupport
    have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
    have hI : 0 < ∫ x, B x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
      exact measure_ball_pos volume 0 hr
    refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
      fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
    · exact (support_mul_subset_right _ _).trans B.support_eq.subset
  have hprec : ContinuousLinearMap.precompR (Euclid (m + 1))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1)) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ]
        (Euclid (m + 1) →L[ℝ] Euclid (m + 1))) := by
    ext x A v
    simp [ContinuousLinearMap.precompR]
  intro φ hφ hφc hφD
  obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hφc hD hφD
  set K' := cthickening δ (tsupport φ) with hK'
  have hK'c : IsCompact K' := IsCompact.cthickening hφc
  have hK'm : MeasurableSet K' := isClosed_cthickening.measurableSet
  -- radii
  obtain ⟨rr, hrr0, hrrδ, hrrlim⟩ : ∃ rr : ℕ → ℝ, (∀ n, 0 < rr n) ∧ (∀ n, rr n ≤ δ) ∧
      Tendsto rr atTop (𝓝 0) := by
    refine ⟨fun n => δ / ((n : ℝ) + 1), fun n => div_pos hδ (by positivity), fun n => ?_, ?_⟩
    · exact div_le_self hδ.le (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose ρ hρs hρc hρ0 hρ1 hρsupp using fun n => hmoll (rr n) (hrr0 n)
  -- mollified fields
  obtain ⟨φn, hφn⟩ : ∃ φn : ℕ → Euclid (m + 1) → Euclid (m + 1),
      ∀ n, φn n = convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨fun n => convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun _ => rfl⟩
  have hφn_sm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φn n) := fun n => by
    rw [hφn]
    exact (hρc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs n)
      hφ.continuous.locallyIntegrable
  have hφn_supp : ∀ n, support (φn n) ⊆ K' := fun n => by
    rw [hφn]
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add (hρsupp n) (subset_tsupport φ)).trans ?_
    rw [ball_add_zero]
    exact (thickening_subset_cthickening _ _).trans (cthickening_mono (hrrδ n) _)
  have hφn_cs : ∀ n, HasCompactSupport (φn n) ∧ tsupport (φn n) ⊆ K' := fun n =>
    ⟨hK'c.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hφn_supp n) hK'c.isClosed),
      closure_minimal (hφn_supp n) hK'c.isClosed⟩
  -- bounds
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M', hM'⟩ := hdφc.bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hφn_bd : ∀ n y, ‖φn n y‖ ≤ Mφ := fun n y => by
    rw [hφn, ← dist_zero_right]
    exact dist_convolution_le hMφ0 (hρsupp n) (hρ0 n) (hρ1 n)
      hφ.continuous.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hMφ x)
  have hsmall : Tendsto (fun n => support (ρ n)) atTop (𝓝 (0 : Euclid (m + 1))).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [hrrlim.eventually (gt_mem_nhds hε)] with n hn
    exact (hρsupp n).trans ((ball_subset_ball hn.le).trans hεt)
  have hφn_lim : ∀ y, Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) := fun y => by
    simp only [hφn]
    exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1) hsmall
      (Eventually.of_forall fun _ => hφ.continuous.aestronglyMeasurable)
      ((hφ.continuous.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- derivatives
  have hdφn : ∀ n y, fderiv ℝ (φn n) y =
      convolution (ρ n) (fderiv ℝ φ) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := fun n y => by
    rw [hφn, ← hprec]
    exact (hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρs n).continuous.locallyIntegrable hφ y).fderiv
  have hdφn_bd : ∀ n y, ‖fderiv ℝ (φn n) y‖ ≤ M' := fun n y => by
    rw [hdφn, ← dist_zero_right]
    exact dist_convolution_le hM'0 (hρsupp n) (hρ0 n) (hρ1 n)
      hdφc.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hM' x)
  have hdφn_lim : ∀ y, Tendsto (fun n => fderiv ℝ (φn n) y) atTop (𝓝 (fderiv ℝ φ y)) :=
    fun y => by
      simp only [hdφn]
      exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1)
        hsmall (Eventually.of_forall fun _ => hdφc.aestronglyMeasurable)
        ((hdφc.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- convergence of the left side
  have hL : Tendsto (fun n => T (φn n)) atTop (𝓝 (T φ)) := by
    simp only [hT]
    refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ => ‖trc‖ * M')
      (fun n => (trc.continuous.comp ((hφn_sm n).continuous_fderiv (by simp))).aestronglyMeasurable)
      ?_ (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · exact ((integrable_indicator_iff hK'm).2
        (integrableOn_const hK'c.measure_lt_top.ne)).restrict
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        exact (trc.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hdφn_bd n y) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        have : fderiv ℝ (φn n) y = 0 :=
          notMem_support.1 fun h => hy ((hφn_cs n).2 (support_fderiv_subset ℝ h))
        rw [this, map_zero, norm_zero]
    · exact (trc.continuous.tendsto _).comp (hdφn_lim y)
  -- convergence of the right side
  have hR : Tendsto (fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ) atTop
      (𝓝 (-∫ y, inner ℝ (φ y) (ν y) ∂μ)) := by
    refine Tendsto.neg (tendsto_integral_of_dominated_convergence (K'.indicator fun _ => Mφ)
      (fun n => (Continuous.measurable2 continuous_inner (hφn_sm n).continuous.measurable
        hνm).aestronglyMeasurable) ?_ (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_))
    · exact (integrable_indicator_iff hK'm).2
        (integrableOn_const (hμK K' hK'c hδD))
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hν1, mul_one]
        exact hφn_bd n y
      · rw [indicator_of_notMem hy]
        have : φn n y = 0 := notMem_support.1 fun h => hy (hφn_supp n h)
        rw [this, inner_zero_left, norm_zero]
    · exact (hφn_lim y).inner tendsto_const_nhds
  have hLR : (fun n => T (φn n)) = fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ := by
    funext n
    exact hsmooth (φn n) (hφn_sm n) (hφn_cs n).1 ((hφn_cs n).2.trans hδD)
  rw [hLR] at hL
  exact tendsto_nhds_unique hL hR
/-- **The ball and cone masses are Borel functions of the centre.**  This is the measurability
that Simon's proof of Ch. 3, 1.6 "⇐" does not check when it applies Egoroff's theorem to `f_k`
and `q_k`, which are built from `μ(B_ρ(x))` and `μ(X_{1/2}(P_x^⊥, x) ∩ B_ρ(x))`.  For an s-finite
`μ` on `E = ℝ^{m+1}`, a Borel `ν : E → E` and `α, q ∈ ℝ`, the maps `x ↦ μ(B̄_q(x))` and
`x ↦ μ({z : α|z - x| ≤ |⟨z - x, ν(x)⟩|} ∩ B̄_q(x))` are measurable.  Each is `x ↦ μ(S_x)` for a
measurable `S ⊆ E × E`, namely `S = A = {(x, z) : |z - x| ≤ q}` or `S = B ∩ A` with
`B = {(x, z) : α|z - x| ≤ |⟨z - x, ν(x)⟩|}`, so the section lemma of Tonelli's theorem applies. -/
theorem Submission.codim1_rdo_dg_rc_ball_cone_measurable : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (α q : ℝ), SFinite μ → Measurable ν → Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) ∧ Measurable (fun x : Euclid (m + 1) => μ ({z | α * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q)) := by
  intro m μ ν α q hμ hν
  -- `A = {(x, z) : |z - x| ≤ q}` is measurable, with sections `B̄_q(x)`
  have hA : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) | dist p.2 p.1 ≤ q} :=
    measurableSet_le (continuous_dist.comp (continuous_snd.prodMk continuous_fst)).measurable
      measurable_const
  -- `B = {(x, z) : α|z - x| ≤ |⟨z - x, ν(x)⟩|}` is measurable since `ν` is
  have hB : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) |
      α * ‖p.2 - p.1‖ ≤ |inner ℝ (p.2 - p.1) (ν p.1)|} := by
    refine measurableSet_le ?_ ?_
    · exact (continuous_const.mul (continuous_norm.comp
        (continuous_snd.sub continuous_fst))).measurable
    · exact continuous_abs.measurable.comp (Continuous.measurable2 continuous_inner
        (measurable_snd.sub measurable_fst) (hν.comp measurable_fst))
  -- for s-finite `μ`, `x ↦ μ(S_x)` is measurable for every measurable `S ⊆ E × E`
  refine ⟨?_, ?_⟩
  · have h := measurable_measure_prodMk_left (ν := μ) hA
    convert h using 2 with x
    rfl
  · have h := measurable_measure_prodMk_left (ν := μ) (hB.inter hA)
    convert h using 2 with x
    rfl

/-- **Uniform density and cone bounds on a large compact set** (Simon Ch. 3, proof of 1.6 "⇐",
(4) and (7)–(9), chapter-03.txt lines 162–213).  Let `μ` be a finite measure on `ℝ^{m+1}`,
`C(x) = {z : ¼|z − x| ≤ |⟨z − x, ν(x)⟩|}`, and suppose that for `μ`-a.e. `y`,
`μ(B̄_r(y))/(ωₘrᵐ) → 1` and `μ(C(y) ∩ B̄_r(y))/rᵐ → 0` as `r ↓ 0`.  Then for `ε, η > 0` there are
a compact `K` with `μ(Kᶜ) ≤ η` and `δ > 0` such that `(1 − ε)⁺ωₘρᵐ ≤ μ(B̄_ρ(x))` and
`μ(C(x) ∩ B̄_ρ(x)) ≤ εωₘρᵐ` for all `x ∈ K`, `0 < ρ < δ`.  Egoroff's theorem is replaced by the
Borel sets `G_k` of points where both bounds hold at every rational radius `0 < q < 1/(k + 1)`
(Borel by `codim1_rdo_dg_rc_ball_cone_measurable`): they increase to a set of full measure, so
`μ(G_kᶜ) < η/2` for some `k` by continuity from above, and inner regularity gives a compact
`K ⊆ G_k` with `μ(G_k \ K) < η/2`.  The bounds pass from rational to real radii by monotonicity
in the radius and continuity of `ρ ↦ cρᵐ`. -/
theorem Submission.codim1_rdo_dg_rc_uniform_compact : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (ε : ℝ) (η : ℝ≥0∞), IsFiniteMeasure μ → Measurable ν → 0 < ε → 0 < η → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) := by
  intro m μ ν ε η hfin hν hε hη hae
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  -- step 2: for each radius `q` both `x ↦ μ(B̄_q(x))` and `x ↦ μ(C(x) ∩ B̄_q(x))` are Borel
  have hball : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).1
  have hcone : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) =>
      μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).2
  -- monotonicity and continuity of `ρ ↦ c * ofReal (ρ ^ m)`
  have hmono : ∀ (c : ℝ≥0∞) (s t : ℝ), 0 ≤ s → s ≤ t →
      c * ENNReal.ofReal (s ^ m) ≤ c * ENNReal.ofReal (t ^ m) := by
    intro c s t hs hst
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs hst m)) c
  have hcont : ∀ c : ℝ≥0∞, c ≠ ∞ → Continuous (fun s : ℝ => c * ENNReal.ofReal (s ^ m)) :=
    fun c hc => (ENNReal.continuous_const_mul hc).comp
      (ENNReal.continuous_ofReal.comp (continuous_pow m))
  -- the argument for general constants `A`, `B` and a general family of sets `C x`
  have main : ∀ (C : Euclid (m + 1) → Set (Euclid (m + 1))) (A B : ℝ≥0∞), A ≠ ∞ → B ≠ ∞ →
      (∀ q : ℝ, Measurable (fun x => μ (C x ∩ closedBall x q))) →
      (∀ᵐ y ∂μ, ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r < r₁ →
        A * ENNReal.ofReal (r ^ m) ≤ μ (closedBall y r) ∧
          μ (C y ∩ closedBall y r) ≤ B * ENNReal.ofReal (r ^ m)) →
      ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → A * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (ρ ^ m)) := by
    intro C A B hA hB hCmeas hgood
    -- step 1: the good sets `G k`, bounds at rational radii `q < 1/(k + 1)`
    let G : ℕ → Set (Euclid (m + 1)) := fun k => {x | ∀ q : ℚ, 0 < (q : ℝ) →
      (q : ℝ) < 1 / ((k : ℝ) + 1) →
      A * ENNReal.ofReal ((q : ℝ) ^ m) ≤ μ (closedBall x q) ∧
        μ (C x ∩ closedBall x q) ≤ B * ENNReal.ofReal ((q : ℝ) ^ m)}
    -- step 2: each `G k` is Borel
    have hGmeas : ∀ k, MeasurableSet (G k) := by
      intro k
      refine Measurable.setOf (Measurable.forall fun q => ?_)
      refine Measurable.imp measurable_const (Measurable.imp measurable_const
        (Measurable.and ?_ ?_))
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (hball q))
      · exact measurableSet_setOfPred.1 (measurableSet_le (hCmeas q) measurable_const)
    -- step 3: `G` is increasing
    have hGmono : Monotone G := by
      intro k l hkl x hx q hq0 hql
      refine hx q hq0 (lt_of_lt_of_le hql ?_)
      have hkl' : (k : ℝ) ≤ l := Nat.cast_le.mpr hkl
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    -- step 4: `μ`-a.e. point lies in some `G k`
    have hGae : ∀ᵐ x ∂μ, x ∈ ⋃ k, G k := by
      filter_upwards [hgood] with y hy
      obtain ⟨r₁, hr₁, hy⟩ := hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr₁
      exact mem_iUnion.mpr ⟨k, fun q hq0 hqk => hy q hq0 (hqk.trans hk)⟩
    have hnull : μ (⋂ k, (G k)ᶜ) = 0 := by
      rw [← compl_iUnion]
      exact mem_ae_iff.mp hGae
    -- step 5: continuity from above gives `μ (G k)ᶜ < η / 2` for some `k`
    have htend : Tendsto (fun k => μ (G k)ᶜ) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) (s := fun k => (G k)ᶜ)
        (fun k => (hGmeas k).compl.nullMeasurableSet)
        (fun k l hkl => compl_subset_compl.mpr (hGmono hkl)) ⟨0, measure_ne_top μ _⟩
      rw [hnull] at this
      exact this
    have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨k, hk⟩ := (htend.eventually_lt_const hη2).exists
    -- step 6: inner regularity gives a compact `K ⊆ G k` with `μ (G k \ K) < η / 2`
    obtain ⟨K, hKG, hKc, hKμ⟩ :=
      (hGmeas k).exists_isCompact_sdiff_lt (measure_ne_top μ _) hη2.ne'
    refine ⟨K, 1 / ((k : ℝ) + 1), hKc, by positivity, ?_, ?_, ?_⟩
    · calc μ Kᶜ ≤ μ ((G k)ᶜ ∪ (G k \ K)) := by
            apply measure_mono
            intro x hx
            by_cases h : x ∈ G k
            · exact Or.inr ⟨h, hx⟩
            · exact Or.inl h
        _ ≤ μ (G k)ᶜ + μ (G k \ K) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hk.le hKμ.le
        _ = η := ENNReal.add_halves η
    -- step 7(a): lower bound at real radii, approximating `ρ` from below by rationals
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo 0 ρ, A * ENNReal.ofReal (s ^ m) ≤ μ (closedBall x ρ) := by
        intro s hs
        obtain ⟨q, hsq, hqρ⟩ := exists_rat_btwn hs.2
        have hq0 : 0 < (q : ℝ) := hs.1.trans hsq
        calc A * ENNReal.ofReal (s ^ m) ≤ A * ENNReal.ofReal ((q : ℝ) ^ m) :=
              hmono A s q hs.1.le hsq.le
          _ ≤ μ (closedBall x q) := (hxG q hq0 (hqρ.trans hρδ)).1
          _ ≤ μ (closedBall x ρ) := measure_mono (closedBall_subset_closedBall hqρ.le)
      exact le_of_tendsto (((hcont A hA).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsLT hρ) key)
    -- step 7(b): cone bound at real radii, approximating `ρ` from above by rationals
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo ρ (1 / ((k : ℝ) + 1)),
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (s ^ m) := by
        intro s hs
        obtain ⟨q, hρq, hqs⟩ := exists_rat_btwn hs.1
        have hq0 : 0 < (q : ℝ) := hρ.trans hρq
        calc μ (C x ∩ closedBall x ρ) ≤ μ (C x ∩ closedBall x q) :=
              measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hρq.le))
          _ ≤ B * ENNReal.ofReal ((q : ℝ) ^ m) := (hxG q hq0 (hqs.trans hs.2)).2
          _ ≤ B * ENNReal.ofReal (s ^ m) := hmono B q s hq0.le hqs.le
      exact ge_of_tendsto (((hcont B hB).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsGT hρδ) key)
  -- step 4 for the actual constants: where both limits hold, the bounds hold for small `r`
  have hA1 : ENNReal.ofReal (1 - ε) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  have hB0 : 0 < ENNReal.ofReal ε * unitBallVolume m :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' hω0
  refine main (fun x => {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|})
    (ENNReal.ofReal (1 - ε) * unitBallVolume m) (ENNReal.ofReal ε * unitBallVolume m)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop) hcone ?_
  filter_upwards [hae] with y hy
  obtain ⟨h1, h2⟩ := hy
  have e1 := h1.eventually_const_lt hA1
  have e2 := h2.eventually_lt_const hB0
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  refine ⟨r₁, hr₁, fun r hr0 hr1 => ?_⟩
  obtain ⟨hlow, hup⟩ := hsub ⟨hr0, hr1⟩
  have hpow0 : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr0 m)).ne'
  have hpowtop : ENNReal.ofReal (r ^ m) ≠ ∞ := ENNReal.ofReal_ne_top
  constructor
  · have := (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 hpow0))
      (Or.inl (ENNReal.mul_ne_top hωtop hpowtop))).mp hlow.le
    rw [mul_assoc]
    exact this
  · exact (ENNReal.div_le_iff hpow0 hpowtop).mp hup.le
/-- **Simon Ch. 3, proof of 1.6 "⇐", claim (10)** (cone exclusion), in codimension one: let
`μ(B̄_ρ(y)) ≥ (1 − ε) ωₘ ρᵐ` and `μ(C(y) ∩ B̄_ρ(y)) ≤ ε ωₘ ρᵐ` for `y ∈ K`, `0 < ρ < δ`, where
`C(y) = {z : |z − y| ≤ 4 |⟨z − y, ν(y)⟩|}`, and let `(1 + 16ᵐ) ε < 1`.  Then
`|⟨x' − x, v⟩| ≤ |x' − x| / 2` for `x, x' ∈ K` with `|x' − x| < δ / 2` and `|ν(x) − v| ≤ 1/16`.
Otherwise `B̄_{ρ/8}(x') ⊆ C(x) ∩ B̄_{2ρ}(x)` for `ρ = |x' − x|`, and the two bounds give
`(1 − ε) ωₘ (ρ/8)ᵐ ≤ ε ωₘ (2ρ)ᵐ`, i.e. `1 − ε ≤ 16ᵐ ε`. -/
theorem Submission.codim1_rdo_dg_rc_cone_exclusion : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (K : Set (Euclid (m + 1))) (δ ε : ℝ), (∀ y, ‖ν y‖ = 1) → 0 ≤ ε → (1 + 16 ^ m) * ε < 1 → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) → ∀ x ∈ K, ∀ x' ∈ K, ∀ v : Euclid (m + 1), ‖ν x - v‖ ≤ 1 / 16 → ‖x' - x‖ < δ / 2 → |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2 := by
  intro m μ ν K δ ε hν1 hε0 hε1 hlow hup x hx x' hx' v hv hxx'
  by_contra hcon
  push Not at hcon
  set w := x' - x with hw
  set ρ := ‖w‖ with hρ
  have hρ0 : 0 < ρ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw0 : w = 0 := norm_eq_zero.1 h.symm
      rw [hw0] at hcon
      simp at hcon
      linarith [h, hρ]
  have hδ : 0 < δ := by linarith
  -- `|⟨w, ν x⟩| > 7ρ/16`, since `|⟨w, v⟩| > ρ/2` and `|ν x - v| ≤ 1/16`
  have h2 : 7 * ρ / 16 < |inner ℝ w (ν x)| := by
    have e1 : |inner ℝ w (v - ν x)| ≤ ρ * ‖ν x - v‖ := by
      calc |inner ℝ w (v - ν x)| ≤ ‖w‖ * ‖v - ν x‖ := abs_real_inner_le_norm _ _
        _ = ρ * ‖ν x - v‖ := by rw [norm_sub_rev v (ν x)]
    have e2 : inner ℝ w v = inner ℝ w (ν x) + inner ℝ w (v - ν x) := by
      rw [inner_sub_right]; ring
    have e3 : |inner ℝ w v| ≤ |inner ℝ w (ν x)| + |inner ℝ w (v - ν x)| := by
      rw [e2]; exact abs_add_le _ _
    have e4 : ρ * ‖ν x - v‖ ≤ ρ * (1 / 16) := mul_le_mul_of_nonneg_left hv hρ0.le
    linarith
  -- `B̄_{ρ/8}(x') ⊆ C(x) ∩ B̄_{2ρ}(x)`: on the small ball `|z - x| ≤ 9ρ/8` and
  -- `|⟨z - x, ν x⟩| > 7ρ/16 - ρ/8 = 5ρ/16`
  have hsub : closedBall x' (ρ / 8) ⊆
      {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x (2 * ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hzx : z - x = w + (z - x') := by rw [hw]; abel
    have hnorm : ‖z - x‖ ≤ 9 * ρ / 8 := by
      calc ‖z - x‖ = ‖w + (z - x')‖ := by rw [hzx]
        _ ≤ ‖w‖ + ‖z - x'‖ := norm_add_le _ _
        _ ≤ ρ + ρ / 8 := by linarith
        _ = 9 * ρ / 8 := by ring
    have hin : |inner ℝ (z - x') (ν x)| ≤ ρ / 8 := by
      calc |inner ℝ (z - x') (ν x)| ≤ ‖z - x'‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
        _ = ‖z - x'‖ := by rw [hν1 x, mul_one]
        _ ≤ ρ / 8 := hz
    have hinner : inner ℝ (z - x) (ν x) = inner ℝ w (ν x) + inner ℝ (z - x') (ν x) := by
      rw [hzx, inner_add_left]
    have hbig : 5 * ρ / 16 < |inner ℝ (z - x) (ν x)| := by
      rw [hinner]
      have h' : |inner ℝ w (ν x)| ≤
          |inner ℝ w (ν x) + inner ℝ (z - x') (ν x)| + |inner ℝ (z - x') (ν x)| := by
        have := abs_sub (inner ℝ w (ν x) + inner ℝ (z - x') (ν x)) (inner ℝ (z - x') (ν x))
        simpa using this
      linarith
    refine ⟨?_, ?_⟩
    · show (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|
      linarith
    · rw [mem_closedBall, dist_eq_norm]; linarith
  -- `(1 - ε) ωₘ (ρ/8)ᵐ ≤ μ(B̄_{ρ/8}(x')) ≤ μ(C(x) ∩ B̄_{2ρ}(x)) ≤ ε ωₘ (2ρ)ᵐ`
  have hlow' := hlow x' hx' (ρ / 8) (by positivity) (by linarith)
  have hup' := hup x hx (2 * ρ) (by positivity) (by linarith)
  have hchain : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) ≤
      ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) :=
    hlow'.trans ((measure_mono hsub).trans hup')
  -- cancelling `ωₘ (ρ/8)ᵐ ∈ (0, ∞)` gives `1 - ε ≤ 16ᵐ ε`, contradicting `(1 + 16ᵐ) ε < 1`
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωt : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  set a := (unitBallVolume m).toReal with ha_def
  have ha : 0 < a := ENNReal.toReal_pos hω0 hωt
  have hωeq : unitBallVolume m = ENNReal.ofReal a := (ENNReal.ofReal_toReal hωt).symm
  have h1ε : 0 ≤ 1 - ε := by
    have : 0 ≤ (16 : ℝ) ^ m * ε := by positivity
    nlinarith
  have hL : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) =
      ENNReal.ofReal ((1 - ε) * a * (ρ / 8) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul h1ε, ← ENNReal.ofReal_mul (by positivity)]
  have hR : ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) =
      ENNReal.ofReal (ε * a * (2 * ρ) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul hε0, ← ENNReal.ofReal_mul (by positivity)]
  rw [hL, hR, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hpow : (2 * ρ) ^ m = 16 ^ m * (ρ / 8) ^ m := by
    rw [← mul_pow]; congr 1; ring
  rw [hpow] at hchain
  have hpos : 0 < a * (ρ / 8) ^ m := by positivity
  have h16 : (1 - ε) * (a * (ρ / 8) ^ m) ≤ (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by
    calc (1 - ε) * (a * (ρ / 8) ^ m) = (1 - ε) * a * (ρ / 8) ^ m := by ring
      _ ≤ ε * a * (16 ^ m * (ρ / 8) ^ m) := hchain
      _ = (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by ring
  have h17 : 1 - ε ≤ ε * 16 ^ m := le_of_mul_le_mul_right h16 hpos
  nlinarith
/-- **Simon Ch. 3, proof of 1.6 "⇐"** (Lipschitz graph step, codimension one): if `‖v‖ = 1` and
`|⟨x' − x, v⟩| ≤ ‖x' − x‖/2` on `S`, then `S` lies in a closed countably `m`-rectifiable set.
With `t(z) = ⟨z, v⟩` and `p(z) = z − t(z)v`, the hypothesis gives `|t(x') − t(x)| ≤ ‖p(x') − p(x)‖`
on `S`, so `p(x) ↦ t(x)` is 1-Lipschitz on `p(S)`; its McShane extension `τ` makes
`Γ = {z | τ(p(z)) = t(z)}` closed, and `Γ` lies in the range of the Lipschitz map
`y ↦ ι(y) + τ(ι(y))v`, where `ι : ℝᵐ ≃ v^⊥` is a linear isometry. -/
theorem Submission.codim1_rdo_dg_rc_closed_graph_cover : ∀ (m : ℕ) (v : Euclid (m + 1)) (S : Set (Euclid (m + 1))), ‖v‖ = 1 → (∀ x ∈ S, ∀ x' ∈ S, |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2) → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ S ⊆ Γ := by
  intro m v S hv hS
  -- Step 1: height `t` and orthogonal projection `p` onto `vᗮ`.
  obtain ⟨t, ht⟩ : ∃ t : Euclid (m + 1) → ℝ, ∀ z, t z = inner ℝ z v := ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Euclid (m + 1) → Euclid (m + 1), ∀ z, p z = z - t z • v :=
    ⟨_, fun _ => rfl⟩
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hpv : ∀ z, inner ℝ (p z) v = (0 : ℝ) := by
    intro z
    rw [hp, inner_sub_left, real_inner_smul_left, hvv, ht, mul_one, sub_self]
  have hpmem : ∀ z, p z ∈ (ℝ ∙ v)ᗮ := by
    intro z
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hpv z
  have hdecomp : ∀ z, p z + t z • v = z := by
    intro z
    rw [hp, sub_add_cancel]
  -- Step 2: the key inequality `|t x' - t x| ≤ ‖p x' - p x‖` on `S`.
  have key : ∀ x ∈ S, ∀ x' ∈ S, |t x' - t x| ≤ ‖p x' - p x‖ := by
    intro x hx x' hx'
    have h1 := hS x hx x' hx'
    have h2 : inner ℝ (x' - x) v = t x' - t x := by
      rw [inner_sub_left, ht, ht]
    have h3 : x' - x = (p x' - p x) + (t x' - t x) • v := by
      rw [hp, hp, sub_smul]
      abel
    have h4 : ‖x' - x‖ ≤ ‖p x' - p x‖ + |t x' - t x| := by
      calc ‖x' - x‖ = ‖(p x' - p x) + (t x' - t x) • v‖ := by rw [← h3]
        _ ≤ ‖p x' - p x‖ + ‖(t x' - t x) • v‖ := norm_add_le _ _
        _ = ‖p x' - p x‖ + |t x' - t x| := by
          rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [h2] at h1
    linarith
  -- Step 3: the height as a function of the projection, and its McShane extension.
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclid (m + 1) → ℝ, ∀ x ∈ S, τ (p x) = t x := by
    refine ⟨fun y => t (Function.invFunOn p S y), ?_⟩
    intro x hx
    have hex : ∃ a ∈ S, p a = p x := ⟨x, hx, rfl⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h := key x hx _ hmem
    rw [heq, sub_self, norm_zero] at h
    have h0 : t (Function.invFunOn p S (p x)) - t x = 0 := abs_nonpos_iff.mp h
    show t (Function.invFunOn p S (p x)) = t x
    linarith
  have hτLip : LipschitzOnWith 1 τ (p '' S) := by
    apply LipschitzOnWith.mk_one
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [hτ x hx, hτ x' hx', Real.dist_eq, dist_eq_norm]
    exact key x' hx' x hx
  obtain ⟨τ', hτ'Lip, hτ'eq⟩ := hτLip.extend_real
  -- Step 4: an isometry `ι : ℝᵐ ≃ vᗮ` and the Lipschitz graph map `F`.
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv0 : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  let ι := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m hv0).repr.symm
  let F : Euclid m → Euclid (m + 1) := fun y => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) +
    τ' ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) • v
  have hFLip : ∃ K, LipschitzWith K F := by
    have h1 : LipschitzWith (1 * 1)
        (fun y : Euclid m => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1))) :=
      (Submodule.subtypeₗᵢ (ℝ ∙ v)ᗮ).lipschitzWith.comp ι.lipschitzWith
    have hsm : LipschitzWith 1 (fun r : ℝ => r • v) := by
      apply LipschitzWith.mk_one
      intro r s
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq, Real.norm_eq_abs]
    exact ⟨_, h1.add (hsm.comp (hτ'Lip.comp h1))⟩
  obtain ⟨K, hK⟩ := hFLip
  -- Step 5: the closed graph `Γ = {z | τ' (p z) = t z}`.
  have htc : Continuous t := by
    rw [show t = fun z => inner ℝ z v from funext ht]
    fun_prop
  have hpc : Continuous p := by
    rw [show p = fun z => z - t z • v from funext hp]
    fun_prop
  refine ⟨{z | τ' (p z) = t z}, ?_, ?_, ?_⟩
  · exact isClosed_eq (hτ'Lip.continuous.comp hpc) htc
  · apply (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hK).mono
    intro z hz
    simp only [mem_ofPred_eq] at hz
    refine ⟨ι.symm ⟨p z, hpmem z⟩, ?_⟩
    simp only [F, LinearIsometryEquiv.apply_symm_apply]
    rw [hz]
    exact hdecomp z
  · intro x hx
    simp only [mem_ofPred_eq]
    rw [← hτ'eq (mem_image_of_mem p hx)]
    exact hτ x hx

/-- **Compact cover** of Simon Ch. 3, proof of Theorem 1.6 "⇐": the choice of `π₁, …, π_N` with
`E = ⋃ⱼ Eⱼ` and the selection `E ⊆ ⋃ⱼ Qⱼ(graph fⱼ)`, in codimension one, where the subspaces `πⱼ`
become unit directions `v`.  Cover the unit sphere by finitely many balls `B_{1/16}(v)` and `K` by
finitely many balls `B_{δ/4}(c)`, `c ∈ K`.  Two points of
`S_{v,c} = {x ∈ K : |ν(x) − v| < 1/16} ∩ B_{δ/4}(c)` are less than `δ/2` apart, so
`codim1_rdo_dg_rc_cone_exclusion` gives `|⟨x' − x, v⟩| ≤ ½|x' − x|` on `S_{v,c}`, and
`codim1_rdo_dg_rc_closed_graph_cover` gives a closed countably `m`-rectifiable `Γ_{v,c} ⊇ S_{v,c}`.
The finite union of the `Γ_{v,c}` contains `K`, since `|ν(x)| = 1`. -/
theorem Submission.codim1_rdo_dg_rc_compact_cover : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (K : Set (Euclid (m + 1))) (δ ε : ℝ), (∀ y, ‖ν y‖ = 1) → IsCompact K → 0 < δ → 0 ≤ ε → (1 + 16 ^ m) * ε < 1 → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ K ⊆ Γ := by
  intro m μ ν K δ ε hν1 hK hδ hε0 hε1 hlow hup
  -- step 1: a finite `1/16`-net `V` of the unit sphere
  obtain ⟨V, hVs, hVfin, hVcov⟩ :=
    (isCompact_sphere (0 : Euclid (m + 1)) 1).finite_cover_balls (e := 1 / 16) (by norm_num)
  -- step 2: a finite `δ/4`-net `C ⊆ K` of `K`
  obtain ⟨C, -, hCfin, hCcov⟩ := hK.finite_cover_balls (e := δ / 4) (by positivity)
  -- step 3: on `S_{v,c}` the cone condition holds in direction `v`, so `S_{v,c}` lies in a closed
  -- countably `m`-rectifiable `Γ_{v,c}`
  have hS : ∀ v ∈ V, ∀ c ∈ C, ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧
      {x | x ∈ K ∧ dist (ν x) v < 1 / 16} ∩ ball c (δ / 4) ⊆ Γ := by
    intro v hv c _
    have hv1 : ‖v‖ = 1 := by simpa using hVs hv
    apply Submission.codim1_rdo_dg_rc_closed_graph_cover m v _ hv1
    rintro x ⟨⟨hxK, hxv⟩, hxc⟩ x' ⟨⟨hx'K, -⟩, hx'c⟩
    apply Submission.codim1_rdo_dg_rc_cone_exclusion m μ ν K δ ε hν1 hε0 hε1 hlow hup
      x hxK x' hx'K v
    · rw [← dist_eq_norm]
      exact hxv.le
    · calc ‖x' - x‖ = dist x' x := (dist_eq_norm _ _).symm
        _ ≤ dist x' c + dist c x := dist_triangle _ _ _
        _ < δ / 4 + δ / 4 := add_lt_add (mem_ball.1 hx'c) (mem_ball'.1 hxc)
        _ = δ / 2 := by ring
  choose! Γ hΓc hΓr hΓS using hS
  -- step 4: `⋃_{v,c} Γ_{v,c}` is closed (a finite union) and countably `m`-rectifiable (a
  -- countable union)
  refine ⟨⋃ v ∈ V, ⋃ c ∈ C, Γ v c, ?_, ?_, ?_⟩
  · exact hVfin.isClosed_biUnion fun v hv => hCfin.isClosed_biUnion fun c hc => hΓc v hv c hc
  · rw [← sUnion_image2 Γ V C]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
      (hVfin.image2 Γ hCfin).countable (forall_mem_image2.2 hΓr)
  -- step 5: `x ∈ K` lies in `S_{v,c}` for a `v ∈ V` with `|ν(x) − v| < 1/16` and a `c ∈ C` with
  -- `x ∈ B_{δ/4}(c)`
  · intro x hxK
    have hνx : ν x ∈ sphere (0 : Euclid (m + 1)) 1 := by simpa using hν1 x
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 (hVcov hνx)
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hCcov hxK)
    exact mem_iUnion₂.2 ⟨v, hv, mem_iUnion₂.2 ⟨c, hc, hΓS v hv c hc ⟨⟨hxK, mem_ball.1 hxv⟩, hxc⟩⟩⟩

/-- **Halving step (★)** of Simon Ch. 3, proof of Theorem 1.6 "⇐":
`μ(ℝ^{n+ℓ} \ ⋃ⱼ Qⱼ(graph fⱼ)) ≤ ½ μ(ℝ^{n+ℓ})`, obtained there from (4) and (8).  If `Ū` is a
compact subset of `D`, then `λ = μ⌞U` is finite and, since `λ = μ` on closed balls inside the open
set `U`, inherits the a.e. density and cone limits.  `codim1_rdo_dg_rc_uniform_compact` with
`ε = 1/(2(1 + 16ᵐ))` and `η = μ(U)/2` gives a compact `K` with `λ(Kᶜ) ≤ μ(U)/2` and uniform bounds
on `K`, and `codim1_rdo_dg_rc_compact_cover` gives a closed countably `m`-rectifiable `Γ ⊇ K`; then
`μ(U \ Γ) = λ(U \ Γ) ≤ λ(Kᶜ) ≤ μ(U)/2`. -/
theorem Submission.codim1_rdo_dg_rc_halving_step : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∀ U : Set (Euclid (m + 1)), IsOpen U → IsCompact (closure U) → closure U ⊆ D → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ μ (U \ Γ) ≤ μ U / 2 := by
  intro m D μ ν hfin hν hν1 hae U hU hUc hUD
  -- step 1: `μ(U) ≤ μ(Ū) < ∞`; if `μ(U) = 0`, then `Γ = ∅` works
  have hUfin : μ U ≠ ∞ := ne_top_of_le_ne_top (hfin _ hUc hUD) (measure_mono subset_closure)
  by_cases h0 : μ U = 0
  · refine ⟨∅, isClosed_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero (by simp), ?_⟩
    simp [h0]
  -- step 2: `λ = μ⌞U` is finite and has the same limits as `μ` at every `y ∈ U`, because the two
  -- functions of `r` agree for `0 < r < r_y`, where `B_{r_y}(y) ⊆ U`
  set lam := μ.restrict U with hlam
  have : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 hUfin
  have haeL : ∀ᵐ y ∂lam,
      Tendsto (fun r : ℝ => lam (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)))
        (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r : ℝ => lam ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩
        closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with y hyU hy
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hyU
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r := by
      filter_upwards [Ioo_mem_nhdsGT hr] with s hs using hs.2
    constructor
    · refine h1.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 ((closedBall_subset_ball hs).trans hrU)]
    · refine h2.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 (inter_subset_right.trans ((closedBall_subset_ball hs).trans hrU))]
  -- step 3: `ε = 1/(2(1 + 16ᵐ)) > 0` with `(1 + 16ᵐ)ε = 1/2 < 1`, and `η = μ(U)/2 > 0`
  set ε : ℝ := 1 / (2 * (1 + 16 ^ m)) with hε
  have hεpos : 0 < ε := by positivity
  have hε1 : (1 + 16 ^ m) * ε < 1 := by
    have : (0 : ℝ) < 1 + 16 ^ m := by positivity
    rw [hε, mul_one_div, div_lt_one (by positivity)]
    linarith
  -- step 4: a compact `K` with `λ(Kᶜ) ≤ η` on which the density and cone bounds are uniform
  obtain ⟨K, δ, hK, hδ, hKc, hlow, hup⟩ := Submission.codim1_rdo_dg_rc_uniform_compact m lam ν ε
    (μ U / 2) inferInstance hν hεpos (ENNReal.half_pos h0) haeL
  -- step 5: a closed countably `m`-rectifiable `Γ ⊇ K`
  obtain ⟨Γ, hΓc, hΓr, hKΓ⟩ :=
    Submission.codim1_rdo_dg_rc_compact_cover m lam ν K δ ε hν1 hK hδ hεpos.le hε1 hlow hup
  -- step 6: `μ(U \ Γ) = λ(U \ Γ) ≤ λ(Kᶜ) ≤ μ(U)/2`, as `U \ Γ ⊆ U` and `U \ Γ ⊆ Kᶜ`
  refine ⟨Γ, hΓc, hΓr, ?_⟩
  calc μ (U \ Γ) = lam (U \ Γ) := by
        rw [hlam, Measure.restrict_apply' hU.measurableSet, inter_eq_left.2 sdiff_subset]
    _ ≤ lam Kᶜ := measure_mono fun x hx hxK => hx.2 (hKΓ hxK)
    _ ≤ μ U / 2 := hKc
/-- Iterated halving on a countable ball cover (Simon Ch. 3, proof of 1.6 "⇐", final iteration):
let `D ⊆ ℝ^{m+1}` be open, `μ(ℝ^{m+1} \ D) = 0` and `μ(K) < ∞` for compact `K ⊆ D`.  If every
open `U` with compact closure `Ū ⊆ D` has a closed countably `m`-rectifiable `Γ` with
`μ(U \ Γ) ≤ μ(U)/2`, then `μ` is carried by a Borel countably `m`-rectifiable set `R`.
For an open `W` with compact closure in `D`, applying the hypothesis to `W \ Γᵢ` gives closed
countably `m`-rectifiable sets `Γᵢ` with `μ(W \ Γᵢ) ≤ 2⁻ⁱ μ(W)`, so `μ(W \ ⋃ᵢ Γᵢ) = 0`; `D` is
covered by countably many balls `B_{r/2}(x)` with `B_r(x) ⊆ D` (Lindelöf), and `R` is the union
of the corresponding sets `⋃ᵢ Γᵢ`. -/
theorem Submission.codim1_rdo_dg_rc_of_halving : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))), IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → (∀ U : Set (Euclid (m + 1)), IsOpen U → IsCompact (closure U) → closure U ⊆ D → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ μ (U \ Γ) ≤ μ U / 2) → ∃ R : Set (Euclid (m + 1)), MeasurableSet R ∧ CountablyRectifiable m R ∧ μ Rᶜ = 0 := by
  intro m D μ hDo hDc hfin hhalf
  -- Steps 2–3: on an open set `W` with compact closure in `D`, iterate the halving hypothesis.
  have key : ∀ W : Set (Euclid (m + 1)), IsOpen W → IsCompact (closure W) → closure W ⊆ D →
      ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧ CountablyRectifiable m R' ∧
        μ (W \ R') = 0 := by
    intro W hWo hWc hWD
    have hWfin : μ W ≠ ∞ := ne_top_of_le_ne_top (hfin _ hWc hWD) (measure_mono subset_closure)
    have step : ∀ i : ℕ, ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧
        μ (W \ Γ) ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i := by
      intro i
      induction i with
      | zero =>
        refine ⟨∅, isClosed_empty,
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty, ?_⟩
        simp
      | succ i ih =>
        obtain ⟨Γ, hΓc, hΓr, hΓμ⟩ := ih
        have hUo : IsOpen (W \ Γ) := hWo.sdiff hΓc
        have hUcl : closure (W \ Γ) ⊆ closure W := closure_mono sdiff_subset
        obtain ⟨Γ', hΓ'c, hΓ'r, hΓ'μ⟩ :=
          hhalf (W \ Γ) hUo (hWc.of_isClosed_subset isClosed_closure hUcl) (hUcl.trans hWD)
        refine ⟨Γ ∪ Γ', hΓc.union hΓ'c, ?_, ?_⟩
        · rw [← sUnion_pair]
          refine Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
            (Set.toFinite _).countable ?_
          rintro S (rfl | rfl)
          · exact hΓr
          · exact hΓ'r
        · rw [← Set.sdiff_sdiff]
          calc μ ((W \ Γ) \ Γ') ≤ μ (W \ Γ) / 2 := hΓ'μ
            _ = μ (W \ Γ) * 2⁻¹ := div_eq_mul_inv _ _
            _ ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i * 2⁻¹ := by gcongr
            _ = μ W * (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by rw [pow_succ, mul_assoc]
    choose Γ hΓc hΓr hΓμ using step
    refine ⟨⋃ i, Γ i, MeasurableSet.iUnion (fun i => (hΓc i).measurableSet),
      Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion Γ hΓr, ?_⟩
    have hlim : Tendsto (fun i : ℕ => μ W * (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hWfin)
    refine nonpos_iff_eq_zero.1 ?_
    refine ge_of_tendsto' hlim (fun i => ?_)
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion Γ i))).trans (hΓμ i)
  -- Step 1: a countable cover of `D` by balls with compact closure inside `D`.
  have hr : ∀ x : Euclid (m + 1), ∃ r : ℝ, 0 < r ∧ (x ∈ D → ball x r ⊆ D) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨r, hr0, hrD⟩ := Metric.isOpen_iff.1 hDo x hx
      exact ⟨r, hr0, fun _ => hrD⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr0 hrD using hr
  let W : Euclid (m + 1) → Set (Euclid (m + 1)) := fun x => ball x (r x / 2)
  have hWcl : ∀ x ∈ D, closure (W x) ⊆ D := fun x hx =>
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self (hr0 x))).trans (hrD x hx))
  have hWcpt : ∀ x, IsCompact (closure (W x)) := fun x =>
    (isCompact_closedBall x (r x / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hR : ∀ x : Euclid (m + 1), ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧
      CountablyRectifiable m R' ∧ (x ∈ D → μ (W x \ R') = 0) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨R', h1, h2, h3⟩ := key (W x) isOpen_ball (hWcpt x) (hWcl x hx)
      exact ⟨R', h1, h2, fun _ => h3⟩
    · exact ⟨∅, MeasurableSet.empty,
        Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
        fun h => absurd h hx⟩
  choose Rx hRxm hRxr hRxμ using hR
  obtain ⟨T, hTD, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable D W (fun x _ => isOpen_ball)
  have hDcov : D ⊆ ⋃ x ∈ T, W x := by
    rw [hTU]
    intro y hy
    exact mem_biUnion hy (mem_ball_self (half_pos (hr0 y)))
  -- Step 4: glue.
  refine ⟨⋃ x ∈ T, Rx x, MeasurableSet.biUnion hTc (fun x _ => hRxm x), ?_, ?_⟩
  · rw [← sUnion_image]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image Rx)
      (by rintro S ⟨x, -, rfl⟩; exact hRxr x)
  · have hsub : (⋃ x ∈ T, Rx x)ᶜ ⊆ Dᶜ ∪ ⋃ x ∈ T, (W x \ Rx x) := by
      intro y hy
      by_cases hyD : y ∈ D
      · right
        obtain ⟨x, hxT, hyW⟩ := mem_iUnion₂.1 (hDcov hyD)
        exact mem_iUnion₂.2 ⟨x, hxT, hyW, fun hyR => hy (mem_iUnion₂.2 ⟨x, hxT, hyR⟩)⟩
      · exact Or.inl hyD
    refine measure_mono_null hsub (measure_union_null hDc ?_)
    exact (measure_biUnion_null_iff hTc).2 (fun x hx => hRxμ x (hTD hx))
/-- **`Hᵐ` of a ball in an `m`-dimensional subspace** (Simon Ch. 3, Remark 1.5(3): `Hᵐ` on an
`m`-plane is `m`-dimensional Lebesgue measure): if `Q ⊆ ℝᴺ` is a linear subspace with
`dim Q = m` and `s > 0`, then `Hᵐ(Q ∩ B_s(0)) = ωₘsᵐ`.  An orthonormal basis of `Q` gives a
linear isometry `ι : ℝᵐ → ℝᴺ` with `ι(B_s(0)) = Q ∩ B_s(0)`; `μHE[m]` is preserved by isometries
and equals `volume` on `ℝᵐ`, where `volume (B_s(0)) = sᵐωₘ`. -/
theorem Submission.codim1_rdo_dg_ftd_plane_ball_measure : ∀ (N m : ℕ) (Q : Submodule ℝ (Euclid N)), Module.finrank ℝ Q = m → ∀ s : ℝ, 0 < s → μHE[m] ((Q : Set (Euclid N)) ∩ ball 0 s) = unitBallVolume m * ENNReal.ofReal (s ^ m) := by
  intro N m Q hm s hs
  -- Step 1: the coordinates of an orthonormal basis of `Q` indexed by `Fin m` give
  -- `e : Q ≃ₗᵢ ℝᵐ`, and `ι = e⁻¹` followed by `Q ↪ ℝᴺ` is a linear isometry with values in `Q`
  let e : Q ≃ₗᵢ[ℝ] Euclid m := ((stdOrthonormalBasis ℝ Q).reindex (finCongr hm)).repr
  let ι : Euclid m →ₗᵢ[ℝ] Euclid N := Q.subtypeₗᵢ.comp e.symm.toLinearIsometry
  have hι : ∀ a, ι a = (e.symm a : Euclid N) := fun a => rfl
  -- Step 2: `ι(B_s(0)) = Q ∩ B_s(0)`
  have himage : ι '' ball 0 s = (Q : Set (Euclid N)) ∩ ball 0 s := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨by rw [hι]; exact (e.symm a).2, ?_⟩
      rw [mem_ball_zero_iff] at ha ⊢
      rwa [LinearIsometry.norm_map]
    · rintro ⟨hz, hzs⟩
      refine ⟨e ⟨z, hz⟩, ?_, by rw [hι, LinearIsometryEquiv.symm_apply_apply]⟩
      rw [mem_ball_zero_iff] at hzs ⊢
      rwa [LinearIsometryEquiv.norm_map]
  -- Steps 3–5: isometry invariance of `μHE[m]`, `μHE[m] = volume` on `ℝᵐ`, Haar scaling of balls
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos (volume : Measure (Euclid m)) 0 hs, finrank_euclideanSpace_fin,
    unitBallVolume]
  -- Step 6: commute the product
  exact mul_comm _ _
/-- **Markov bound for rescaled measures** (the measure-theoretic half of the flat-tangent
density estimate): if `f ≥ 0` is continuous with compact support, `f ≥ 1` on `A`,
`μ(B̄_{r₀}(y)) < ∞`, and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L < L'` as `r ↓ 0`, then
`μ{z : r⁻¹(z − y) ∈ A} ≤ L' rᵐ` for all small `r > 0`.  Once `r R' < r₀`, where `f = 0` off
`B̄_{R'}(0)`, the rescaled integrand is bounded and vanishes off `B̄_{r₀}(y)`, hence integrable,
and Markov's inequality at level `1` bounds the (possibly non-measurable) set by its integral. -/
theorem Submission.codim1_rdo_dg_ftd_test_upper_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → Continuous f → HasCompactSupport f → (∀ w, 0 ≤ f w) → (∀ w ∈ A, 1 ≤ f w) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L < L' → ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (L' * r ^ m) := by
  intro N m μ y f A L L' ⟨r₀, hr₀, hfin⟩ hf hfc hf0 hA hlim hLL'
  -- a radius `R' > 0` outside of which `f` vanishes, and a bound `‖f‖ ≤ C`
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R', hR'pos, hzero⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ w : Euclid N, R' < ‖w‖ → f w = 0 := by
    refine ⟨max R 1, lt_max_of_lt_right one_pos, fun w hw => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hws => ?_
    have hwR := hR hws
    rw [mem_closedBall, dist_zero_right] at hwR
    linarith [le_max_left R 1]
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  -- eventually `r < r₀ / R'` and the rescaled integral is `< L'`
  filter_upwards [hlim (Iio_mem_nhds hLL'), Ioo_mem_nhdsGT (div_pos hr₀ hR'pos)] with r hrL hr
  have hr0 : 0 < r := hr.1
  have hrR : r * R' < r₀ := (lt_div_iff₀ hR'pos).mp hr.2
  -- `z ↦ f (r⁻¹ • (z - y))` is continuous, bounded, and vanishes off `closedBall y r₀`
  have hgc : Continuous fun z => f (r⁻¹ • (z - y)) :=
    hf.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
  have hgint : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
    have hball : IntegrableOn (fun z => f (r⁻¹ • (z - y))) (closedBall y r₀) μ :=
      Measure.integrableOn_of_bounded (M := C) hfin hgc.aestronglyMeasurable
        (Eventually.of_forall fun z => hC _)
    refine integrableOn_univ.mp (hball.of_forall_sdiff_eq_zero MeasurableSet.univ fun z hz => ?_)
    have hz' : r₀ < ‖z - y‖ := by
      have hz2 := hz.2
      rwa [mem_closedBall, dist_eq_norm, not_le] at hz2
    apply hzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, lt_inv_mul_iff₀ hr0]
    linarith
  -- Markov's inequality at level `1`
  have hmarkov : μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall fun z => hf0 _)]
    calc μ {z | r⁻¹ • (z - y) ∈ A}
        ≤ μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} :=
          measure_mono fun z hz => ENNReal.one_le_ofReal.mpr (hA _ hz)
      _ = 1 * μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} := (one_mul _).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ :=
          mul_meas_ge_le_lintegral₀ hgc.measurable.ennreal_ofReal.aemeasurable 1
  refine hmarkov.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := (inv_mul_lt_iff₀ (pow_pos hr0 m)).mp hrL
  rw [mul_comm L']
  exact hint.le
/-- **Lower bound for rescaled measures from a test function** (the lower half of the
flat-tangent density estimate): if `f` is continuous, `0 ≤ f ≤ 1`, `f = 0` off `A`, and
`r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L > L'` as `r ↓ 0`, then `L' rᵐ ≤ μ{z : r⁻¹(z − y) ∈ A}` for all
small `r > 0`.  The rescaled integrand is dominated by the indicator of the (possibly
non-measurable) set, and a non-integrable integrand has Bochner integral `0`. -/
theorem Submission.codim1_rdo_dg_ftd_test_lower_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), Continuous f → (∀ w, 0 ≤ f w) → (∀ w, f w ≤ 1) → (∀ w, w ∉ A → f w = 0) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L' < L → ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (L' * r ^ m) ≤ μ {z | r⁻¹ • (z - y) ∈ A} := by
  intro N m μ y f A L L' hf hf0 hf1 hfA hlim hLL'
  -- eventually `r > 0` and the rescaled integral exceeds `L'`
  filter_upwards [hlim (Ioi_mem_nhds hLL'), self_mem_nhdsWithin] with r hrL hr
  have hint : L' * r ^ m < ∫ z, f (r⁻¹ • (z - y)) ∂μ :=
    (lt_inv_mul_iff₀' (pow_pos hr m)).mp hrL
  -- `ofReal (∫ g) ≤ ∫⁻ ofReal g`: equality if `g` is integrable, otherwise `∫ g = 0`
  have hlint : ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ := by
    by_cases hg : Integrable (fun z => f (r⁻¹ • (z - y))) μ
    · exact (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun z => hf0 _)).le
    · rw [integral_undef hg, ENNReal.ofReal_zero]
      exact zero_le
  -- `ofReal g ≤ 1_{S_r}` pointwise, and `∫⁻ 1_{S_r} dμ ≤ μ S_r` for any set `S_r`
  have hind : ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ ≤
      ∫⁻ z, {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z ∂μ := by
    refine lintegral_mono fun z => ?_
    show ENNReal.ofReal (f (r⁻¹ • (z - y))) ≤ {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z
    by_cases hz : r⁻¹ • (z - y) ∈ A
    · rw [indicator_of_mem (show z ∈ {z | r⁻¹ • (z - y) ∈ A} from hz), Pi.one_apply]
      exact ENNReal.ofReal_le_one.mpr (hf1 _)
    · rw [hfA _ hz, ENNReal.ofReal_zero]
      exact zero_le
  exact (ENNReal.ofReal_le_ofReal hint.le).trans
    (hlint.trans (hind.trans (lintegral_indicator_one_le _)))

/-- **Ball densities of a measure with a flat tangent measure** (Simon Ch. 3, Remark 1.5(3),
first assertion, for `μ` in place of `Hⁿ⌞M`): if `P = v^⊥` (`‖v‖ = 1`), `μ(B̄_{r₀}(y)) < ∞`
and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ` as `r ↓ 0` for every continuous compactly
supported `f`, then `μ(B̄_r(y))/(ωₘrᵐ) → 1` and `μ(B_r(y))/(ωₘrᵐ) → 1`.  Since
`Hᵐ(P ∩ B_s(0)) = ωₘsᵐ`, the radial cutoffs `f₊ = 1` on `B̄₁(0)`, `= 0` off `B_{1+ε}(0)`, and
`f₋ = 1` on `B̄_{1−ε}(0)`, `= 0` off `B₁(0)`, have `∫_P f₊ ≤ ωₘ(1 + ε)ᵐ` and
`∫_P f₋ ≥ ωₘ(1 − ε)ᵐ`; the Markov-type bounds for rescaled measures then give
`ωₘcrᵐ ≤ μ(B_r(y)) ≤ μ(B̄_r(y)) ≤ ωₘCrᵐ` for small `r > 0`, for any `c < 1 < C`. -/
theorem Submission.codim1_rdo_dg_ftd_ball_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ (ball y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) := by
  intro m μ y v _hm hv hr₀ hlim
  -- Step 0(a): `P = v^⊥` is an `m`-dimensional subspace of `ℝ^{m+1}`
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ (Submodule.span ℝ {v})ᗮ = m :=
    Submodule.finrank_orthogonal_span_singleton hv0
  -- Step 0(b): `ωₘ = ofReal ω` with `ω > 0`
  have hω0 : unitBallVolume m ≠ 0 := by
    rw [unitBallVolume]
    exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  obtain ⟨ω, hωpos, hωeq⟩ : ∃ ω : ℝ, 0 < ω ∧ unitBallVolume m = ENNReal.ofReal ω :=
    ⟨(unitBallVolume m).toReal, ENNReal.toReal_pos hω0 hωtop, (ENNReal.ofReal_toReal hωtop).symm⟩
  -- Step 0(c): `ν = Hᵐ⌞P` gives `B_s(0)` the measure `ω sᵐ`
  set ν : Measure (Euclid (m + 1)) :=
    μHE[m].restrict ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))) with hν
  have hνball : ∀ s : ℝ, 0 < s → ν (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [hν, Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m _ hPdim s hs, hωeq,
      ENNReal.ofReal_mul hωpos.le]
  have hνint : ∀ s : ℝ, 0 < s →
      Integrable ((ball (0 : Euclid (m + 1)) s).indicator fun _ => (1 : ℝ)) ν := by
    intro s hs
    have hfin : ν (ball 0 s) ≠ ∞ := by
      rw [hνball s hs]
      exact ENNReal.ofReal_ne_top
    exact (integrableOn_const hfin).integrable_indicator measurableSet_ball
  have hνind : ∀ s : ℝ, 0 < s →
      ∫ w, (ball (0 : Euclid (m + 1)) s).indicator (fun _ => (1 : ℝ)) w ∂ν = ω * s ^ m := by
    intro s hs
    rw [integral_indicator_const _ measurableSet_ball, measureReal_def, hνball s hs,
      ENNReal.toReal_ofReal (mul_pos hωpos (pow_pos hs m)).le, smul_eq_mul, mul_one]
  -- Step 1: comparison of `I(g) = ∫_P g dHᵐ` with plane balls
  have hle_ind : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), (∀ w, g w ≤ 1) →
      (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∀ w, g w ≤ (ball (0 : Euclid (m + 1)) b).indicator (fun _ => (1 : ℝ)) w := by
    intro b g hg1 hgb w
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) b
    · rw [indicator_of_mem hw]
      exact hg1 w
    · rw [indicator_of_notMem hw, hgb w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h))]
  have hgint : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g → (∀ w, 0 ≤ g w) →
      (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) → Integrable g ν := by
    intro b g hb hg hg0 hg1 hgb
    refine (hνint b hb).mono' hg.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
    exact hle_ind b g hg1 hgb w
  -- (U) `I(g) ≤ ω bᵐ` if `0 ≤ g ≤ 1` vanishes off `B_b(0)`
  have hplane_le : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∫ w, g w ∂ν ≤ ω * b ^ m := fun b g hb hg hg0 hg1 hgb =>
    (integral_mono (hgint b g hb hg hg0 hg1 hgb) (hνint b hb) (hle_ind b g hg1 hgb)).trans_eq
      (hνind b hb)
  -- (L) `ω aᵐ ≤ I(g)` if moreover `g ≥ 1` on `B_a(0)`
  have hplane_ge : ∀ (a b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < a → 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, ‖w‖ < a → 1 ≤ g w) →
      (∀ w, b ≤ ‖w‖ → g w = 0) → ω * a ^ m ≤ ∫ w, g w ∂ν := by
    intro a b g ha hb hg hg0 hg1 hga hgb
    refine (hνind a ha).symm.trans_le
      (integral_mono (hνint a ha) (hgint b g hb hg hg0 hg1 hgb) fun w => ?_)
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) a
    · rw [indicator_of_mem hw]
      exact hga w (mem_ball_zero_iff.mp hw)
    · rw [indicator_of_notMem hw]
      exact hg0 w
  -- Step 2: the radial cutoff `g_{a,b} = min 1 (max 0 ((b − ‖w‖)/(b − a)))`
  have hcut : ∀ a b : ℝ, a < b → ∃ g : Euclid (m + 1) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ w, 0 ≤ g w) ∧ (∀ w, g w ≤ 1) ∧ (∀ w, ‖w‖ ≤ a → g w = 1) ∧
      (∀ w, b ≤ ‖w‖ → g w = 0) := by
    intro a b hab
    have hba : 0 < b - a := sub_pos.mpr hab
    have hzero : ∀ w : Euclid (m + 1), b ≤ ‖w‖ → min 1 (max 0 ((b - ‖w‖) / (b - a))) = 0 := by
      intro w hw
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le),
        min_eq_right zero_le_one]
    refine ⟨fun w => min 1 (max 0 ((b - ‖w‖) / (b - a))), by fun_prop, ?_,
      fun w => le_min zero_le_one (le_max_left _ _), fun w => min_le_left _ _, fun w hw => ?_,
      hzero⟩
    · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) b)
        fun w hw => hzero w ?_
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
    · have h1 : 1 ≤ (b - ‖w‖) / (b - a) := by
        rw [le_div_iff₀ hba]
        linarith
      show min 1 (max 0 ((b - ‖w‖) / (b - a))) = 1
      rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  -- Step 3: `{z : r⁻¹(z − y) ∈ B̄₁(0)} = B̄_r(y)` and `{z : r⁻¹(z − y) ∈ B₁(0)} = B_r(y)`
  have hset_closed : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1} = closedBall y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1 ↔ z ∈ closedBall y r
    rw [mem_closedBall_zero_iff, mem_closedBall_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one]
  have hset_open : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1} = ball y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1 ↔ z ∈ ball y r
    rw [mem_ball_zero_iff, mem_ball_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
  -- Step 4: for `C > 1`, eventually `μ(B̄_r(y)) ≤ ω C rᵐ` (test with `f₊ = g_{1,1+ε}`)
  have hupper : ∀ C : ℝ, 1 < C →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall y r) ≤ ENNReal.ofReal (ω * C * r ^ m) := by
    intro C hC
    have hcont : Continuous fun t : ℝ => (1 + t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 + t) ^ m < C :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (gt_mem_nhds hC)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεC, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ :=
      hcut 1 (1 + ε) (lt_add_of_pos_right 1 hε0)
    have hI : ∫ w, g w ∂ν < ω * C :=
      (hplane_le (1 + ε) g (by linarith) hgc hg0 hg1 hgzero).trans_lt
        (mul_lt_mul_of_pos_left hεC hωpos)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g
      (closedBall 0 1) _ (ω * C) hr₀ hgc hgcs hg0
      (fun w hw => (hgone w (mem_closedBall_zero_iff.mp hw)).ge) (hlim g hgc hgcs) hI,
      self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_closed r hrpos] at hr
  -- Step 5: for `c < 1`, eventually `ω c rᵐ ≤ μ(B_r(y))` (test with `f₋ = g_{1−ε,1}`)
  have hlower : ∀ c : ℝ, c < 1 →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (ω * c * r ^ m) ≤ μ (ball y r) := by
    intro c hc
    have hcont : Continuous fun t : ℝ => (1 - t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c < (1 - t) ^ m :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (lt_mem_nhds hc)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεc, hε⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
    have hε0 : (0 : ℝ) < ε := hε.1
    have hε1 : ε < 1 := hε.2
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ := hcut (1 - ε) 1 (by linarith)
    have hI : ω * c < ∫ w, g w ∂ν :=
      (mul_lt_mul_of_pos_left hεc hωpos).trans_le
        (hplane_ge (1 - ε) 1 g (by linarith) one_pos hgc hg0 hg1
          (fun w hw => (hgone w hw.le).ge) hgzero)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_lower_bound (m + 1) m μ y g
      (ball 0 1) _ (ω * c) hgc hg0 hg1
      (fun w hw => hgzero w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h)))
      (hlim g hgc hgcs) hI, self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_open r hrpos] at hr
  -- Step 6: `ofReal (ω c rᵐ) / (ωₘ rᵐ) = ofReal c`
  have hratio : ∀ c : ℝ, 0 ≤ c → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) =
        ENNReal.ofReal c := by
    intro c hc r hr
    have hden0 : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
    have hdentop : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    rw [show ω * c * r ^ m = c * (ω * r ^ m) by ring, ENNReal.ofReal_mul hc,
      ENNReal.ofReal_mul hωpos.le, ← hωeq, ENNReal.mul_div_cancel_right hden0 hdentop]
  -- Step 7: squeeze between `B_r(y)` and `B̄_r(y)` in the order topology of `[0, ∞]`
  have hsqueeze : ∀ F : ℝ → Set (Euclid (m + 1)), (∀ r, ball y r ⊆ F r) →
      (∀ r, F r ⊆ closedBall y r) →
      Tendsto (fun r : ℝ => μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0)
        (𝓝 1) := by
    intro F hF1 hF2
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨c, hc0, hac, hc1⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
      filter_upwards [hlower c (ENNReal.ofReal_lt_one.mp hc1), self_mem_nhdsWithin]
        with r hr hrpos
      calc a < ENNReal.ofReal c := hac
        _ = ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          (hratio c hc0 r hrpos).symm
        _ ≤ μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          ENNReal.div_le_div_right (hr.trans (measure_mono (hF1 r))) _
    · obtain ⟨C, hC0, h1C, hCb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
      filter_upwards [hupper C (ENNReal.one_lt_ofReal.mp h1C), self_mem_nhdsWithin]
        with r hr hrpos
      calc μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))
          ≤ ENNReal.ofReal (ω * C * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
            ENNReal.div_le_div_right ((measure_mono (hF2 r)).trans hr) _
        _ = ENNReal.ofReal C := hratio C hC0 r hrpos
        _ < b := hCb
  exact ⟨hsqueeze (closedBall y) (fun _ => ball_subset_closedBall) (fun _ => subset_rfl),
    hsqueeze (ball y) (fun _ => subset_rfl) (fun _ => ball_subset_closedBall)⟩

/-- **The double cone around the normal has density zero** (Simon Ch. 3, Remark 1.5(3), second
assertion): if `‖v‖ = 1`, `P = v^⊥`, `μ(B̄_{r₀}(y)) < ∞` and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ`
as `r ↓ 0` for every continuous compactly supported `f`, then for every `α > 0`
`μ({z : α‖z − y‖ ≤ |⟨z − y, v⟩|} ∩ B̄_r(y)) / rᵐ → 0` (`m ≥ 1`).  With
`K = {w : α‖w‖ ≤ |⟨w, v⟩|} ∩ B̄₁(0)`, the test function `g = (1 − dist(·, K)/θ)⁺` is `1` on `K` and
vanishes at points of `P` outside `B_{θ(1+1/α)}(0)`, so `∫_P g dHᵐ ≤ ωₘ(θ(1 + 1/α))ᵐ`; the Markov
bound then gives `μ(cone ∩ B̄_r(y)) ≤ (ωₘ(θ(1 + 1/α))ᵐ + θ) rᵐ` for small `r`, and `θ ↓ 0`. -/
theorem Submission.codim1_rdo_dg_ftd_cone_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → ∀ α : ℝ, 0 < α → Tendsto (fun r : ℝ => μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
  intro m μ y v hm hv hfin hconv α hα
  -- Step 0: `P = v^⊥` is a closed `m`-dimensional subspace, and `(Hᵐ⌞P)(B_s(0)) = ωₘ sᵐ`
  set P : Submodule ℝ (Euclid (m + 1)) := (Submodule.span ℝ {v})ᗮ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ P = m := Submodule.finrank_orthogonal_span_singleton hv0
  have hPmeas : MeasurableSet (P : Set (Euclid (m + 1))) :=
    P.closed_of_finiteDimensional.measurableSet
  have hωfin : unitBallVolume m ≠ ∞ := measure_ball_lt_top.ne
  set ω : ℝ := (unitBallVolume m).toReal
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hωeq : unitBallVolume m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal hωfin).symm
  have hball : ∀ s : ℝ, 0 < s →
      μHE[m].restrict (P : Set (Euclid (m + 1))) (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m P hPdim s hs, hωeq,
      ← ENNReal.ofReal_mul hω0]
  -- Step 8: it suffices to bound the ratio eventually by each `ε ∈ (0, ∞)`
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact Eventually.of_forall fun r => hεtop ▸ le_top
  have ht : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  -- since `m ≥ 1`, `ωₘ(θ(1 + α⁻¹))ᵐ + θ → 0` as `θ → 0`; pick `θ > 0` with this `< ε`
  have hφ : Tendsto (fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ := by fun_prop
    have h0 := hc.tendsto 0
    rw [zero_mul, zero_pow (by omega), mul_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨θ, hθt, hθmem⟩ := ((hφ.eventually (gt_mem_nhds ht)).and self_mem_nhdsWithin).exists
  have hθ : 0 < θ := hθmem
  set ρ : ℝ := θ * (1 + α⁻¹) with hρ
  have hρpos : 0 < ρ := mul_pos hθ (add_pos one_pos (inv_pos.mpr hα))
  -- Step 1: the cone `K` in the closed unit ball contains `0`
  set K : Set (Euclid (m + 1)) := {w | α * ‖w‖ ≤ |inner ℝ w v|} ∩ closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  -- Step 2: `g = (1 − dist(·, K)/θ)⁺` is continuous, `0 ≤ g ≤ 1`, `g = 1` on `K`, and `g(w) ≠ 0`
  -- forces `dist(w, k) < θ` for some `k ∈ K`
  set g : Euclid (m + 1) → ℝ := fun w => max 0 (1 - infDist w K / θ)
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const θ))
  have hg0 : ∀ w, 0 ≤ g w := fun w => le_max_left _ _
  have hg1 : ∀ w, g w ≤ 1 := fun w =>
    max_le zero_le_one (by linarith [div_nonneg (infDist_nonneg (x := w) (s := K)) hθ.le])
  have hgK : ∀ w ∈ K, 1 ≤ g w := fun w hw =>
    le_max_of_le_right (by rw [infDist_zero_of_mem hw, zero_div, sub_zero])
  have hgne : ∀ w, g w ≠ 0 → ∃ k ∈ K, dist w k < θ := by
    intro w hw
    rw [← infDist_lt_iff hKne]
    by_contra hcon
    have h1 : 1 ≤ infDist w K / θ := by
      rw [le_div_iff₀ hθ, one_mul]
      exact not_lt.mp hcon
    exact hw (max_eq_left (by linarith))
  -- Step 3: `g` vanishes outside `B̄_{1+θ}(0)`, so it has compact support
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) (1 + θ))
      fun w hw => ?_
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hk1 : ‖k‖ ≤ 1 := mem_closedBall_zero_iff.mp hk.2
    apply hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
      _ ≤ 1 + θ := by linarith
  -- Step 4: on `P`, `g(w) ≠ 0` forces `‖w‖ < ρ = θ(1 + α⁻¹)` (Cauchy–Schwarz, `⟨w, v⟩ = 0`)
  have hgP : ∀ w ∈ P, ρ ≤ ‖w‖ → g w = 0 := by
    intro w hwP hwρ
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hwv : inner ℝ w v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hwP
    have hαk : α * ‖k‖ < θ :=
      calc α * ‖k‖ ≤ |inner ℝ k v| := hk.1
        _ = |inner ℝ (k - w) v| := by rw [inner_sub_left, hwv, sub_zero]
        _ ≤ ‖k - w‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖w - k‖ := by rw [hv, mul_one, norm_sub_rev]
        _ < θ := hwk
    have hkθ : ‖k‖ < θ * α⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ hα]
      linarith
    have hwρ' : ‖w‖ < ρ :=
      calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
        _ < θ + θ * α⁻¹ := add_lt_add hwk hkθ
        _ = ρ := by rw [hρ]; ring
    linarith
  -- Step 5: `∫_P g dHᵐ ≤ ∫_P 1_{B_ρ(0)} dHᵐ = ωₘ ρᵐ`
  have hIg : ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m] ≤ ω * ρ ^ m := by
    have hint : Integrable ((ball (0 : Euclid (m + 1)) ρ).indicator (1 : Euclid (m + 1) → ℝ))
        (μHE[m].restrict (P : Set (Euclid (m + 1)))) := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const (by rw [hball ρ hρpos]; exact ENNReal.ofReal_ne_top)
    calc ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]
        ≤ ∫ z in (P : Set (Euclid (m + 1))),
            (ball (0 : Euclid (m + 1)) ρ).indicator 1 z ∂μHE[m] := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => hg0 w) hint ?_
          rw [EventuallyLE, ae_restrict_iff' hPmeas]
          refine Eventually.of_forall fun w hwP => ?_
          by_cases hwb : w ∈ ball (0 : Euclid (m + 1)) ρ
          · rw [indicator_of_mem hwb, Pi.one_apply]
            exact hg1 w
          · rw [indicator_of_notMem hwb, hgP w hwP (by rwa [mem_ball_zero_iff, not_lt] at hwb)]
      _ = ω * ρ ^ m := by
          rw [integral_indicator_one measurableSet_ball, measureReal_def, hball ρ hρpos,
            ENNReal.toReal_ofReal (mul_nonneg hω0 (pow_nonneg hρpos.le m))]
  -- Step 6: the Markov bound for `g` and `K`, with `L' = ωₘ ρᵐ + θ`
  have hev := Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g K
    (∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]) (ω * ρ ^ m + θ) hfin hgc hgcs hg0 hgK
    (hconv g hgc hgcs) (by linarith)
  -- Steps 7–8: the cone in `B̄_r(y)` rescales into `K`, so the ratio is eventually `≤ ε`
  filter_upwards [hev, self_mem_nhdsWithin] with r hr hrmem
  have hr0 : 0 < r := hrmem
  have hincl : {z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r ⊆
      {z | r⁻¹ • (z - y) ∈ K} := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨?_, ?_⟩
    · show α * ‖r⁻¹ • (z - y)‖ ≤ |inner ℝ (r⁻¹ • (z - y)) v|
      rw [norm_smul, real_inner_smul_left, abs_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      calc α * (r⁻¹ * ‖z - y‖) = r⁻¹ * (α * ‖z - y‖) := by ring
        _ ≤ r⁻¹ * |inner ℝ (z - y) v| := mul_le_mul_of_nonneg_left hz1 (inv_nonneg.mpr hr0.le)
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0,
        inv_mul_le_iff₀ hr0, mul_one]
      rwa [mem_closedBall, dist_eq_norm] at hz2
  refine ENNReal.div_le_of_le_mul ?_
  calc μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r)
      ≤ μ {z | r⁻¹ • (z - y) ∈ K} := measure_mono hincl
    _ ≤ ENNReal.ofReal ((ω * ρ ^ m + θ) * r ^ m) := hr
    _ ≤ ENNReal.ofReal (ε.toReal * r ^ m) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hθt.le (pow_nonneg hr0.le m))
    _ = ε * ENNReal.ofReal (r ^ m) := by
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hεtop]

/-- **A flat tangent measure gives density one and the cone condition** (Simon Ch. 3,
Remark 1.5(3), applied to `μ`): if `μ(B̄_{r₀}(y)) < ∞` and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) →
∫_P f dHᵐ` as `r ↓ 0` for every continuous compactly supported `f`, where `P = (span{v})^⊥` and
`|v| = 1`, then `μ(B̄_r(y))/(ωₘrᵐ) → 1`, `μ(B_r(y))/(ωₘrᵐ) → 1`, and
`μ({z : α|z − y| ≤ |⟨z − y, v⟩|} ∩ B̄_r(y))/rᵐ → 0` for every `α > 0`.  The ball densities
sandwich `1_{B̄₁}` between continuous cut-offs; the cone test function
`(1 − dist(·, K_α)/θ)⁺` lives in `B_{θ(1+1/α)}` on `P`. -/
theorem Submission.codim1_rdo_dg_flat_tangent_density_cone : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ (ball y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ ∀ α : ℝ, 0 < α → Tendsto (fun r : ℝ => μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
  intro m μ y v hm hv hfin hconv
  -- Step 2: closed and open ball densities tend to `1`
  obtain ⟨hclosed, hopen⟩ := Submission.codim1_rdo_dg_ftd_ball_density m μ y v hm hv hfin hconv
  -- Step 3: for every `α > 0` the cone `{α|z − y| ≤ |⟨z − y, v⟩|}` has density `0`
  exact ⟨hclosed, hopen, Submission.codim1_rdo_dg_ftd_cone_density m μ y v hm hv hfin hconv⟩

/-- **Rectifiability from flat tangent measures** (Simon Ch. 3, 1.6 "⇐" in codimension one).
Let `μ` be carried by the open set `D` and finite on its compact subsets. Suppose that at
`μ`-a.e. `y` the blow-ups `r⁻ᵐ μ(y + r ·)` converge to `Hᵐ⌞ν(y)^⊥`, for a Borel unit vector
field `ν`. Then `μ` is carried by a Borel countably `m`-rectifiable set.
Almost every `y` lies in `D`, so `μ(B̄_{r/2}(y)) < ∞` for any ball `B_r(y) ⊆ D`. Hence
`flat_tangent_density` gives (5) density one and (6) `μ(X_{1/4}(ν(y), y) ∩ B̄_ρ(y)) = o(ρᵐ)`.
These are the hypotheses of the halving step (★), and iterating (★) (`of_halving`) gives `R`. -/
theorem Submission.codim1_rdo_dg_rectifiable_of_flat_tangent : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), 1 ≤ m → IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, ∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → ∃ R : Set (Euclid (m + 1)), MeasurableSet R ∧ CountablyRectifiable m R ∧ μ Rᶜ = 0 := by
  intro m D μ ν hm hD hDc hK hν hν1 hflat
  -- step 1: (5) and (6) at `μ`-a.e. `y`; such `y` lie in `D`, where `μ` is finite on small balls
  have hdens : ∀ᵐ y ∂μ,
      Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)))
        (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩
        closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hflat, mem_ae_iff.2 hDc] with y hy hyD
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hfin : μ (closedBall y (r / 2)) ≠ ∞ :=
      hK _ (isCompact_closedBall y (r / 2)) ((closedBall_subset_ball (half_lt_self hr)).trans hrD)
    obtain ⟨h5, -, h6⟩ := Submission.codim1_rdo_dg_flat_tangent_density_cone m μ y (ν y) hm
      (hν1 y) ⟨r / 2, half_pos hr, hfin⟩ hy
    exact ⟨h5, h6 (1 / 4) (by norm_num)⟩
  -- steps 2–6: the halving step (★) for open `U ⋐ D`; step 0: iterate (★) over balls in `D`
  exact Submission.codim1_rdo_dg_rc_of_halving m D μ hD hDc hK
    (Submission.codim1_rdo_dg_rc_halving_step m D μ ν hK hν hν1 hdens)
/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith

/-- **Simon Ch. 3, Lemma 1.2, "only if" part, final paragraph** (chapter-03.txt lines 61–65),
for one `C¹` map `G : ℝⁿ → ℝᴾ`: up to an `Hⁿ`-null set, `G(ℝⁿ)` is covered by the images
`G(B_{r_k}(c_k))` of countably many open balls (empty when `r_k ≤ 0`) carrying lower Lipschitz
bounds `m_k|a − b| ≤ |G a − G b|`, `m_k > 0`.
The critical image `G(C)`, `C = {x : DG(x) not injective}`, is `Hⁿ`-null.  Mathlib's partition
of `C ∩ B̄_R(0)` into pieces `T` on which `G` is `η`-close to some non-injective `A = DG(y)`
reduces this to `Hⁿ(G(T)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(T)`: for a unit `u ∈ ker A`, the compression
`D w = w + (η − 1)⟨u, w⟩u` has `det D = η`, and `|G a − G b| ≤ (‖A‖ + 1)|D a − D b|` on `T`.
For a dense sequence `e` and `(q, p) = Nat.unpair k`, the candidate ball `B_{1/(p+1)}(e_q)` is
kept, with a witness `m_k`, when it carries a lower Lipschitz bound, and replaced by `B_0 = ∅`
otherwise.  At a regular point `x`, `codim1_rdo_c1cov_local_lower_lipschitz` gives a bound on
some `B_δ(x)`; a candidate ball with `2/(p+1) < δ` and `|x − e_q| < 1/(p+1)` contains `x`, lies
in `B_δ(x)` and is kept. -/
theorem Submission.codim1_rdo_c1cov_regular_ball_cover : ∀ (P n : ℕ) (G : Euclid n → Euclid P), ContDiff ℝ 1 G → ∃ (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖G a - G b‖) ∧ μHE[n] (range G \ ⋃ k, G '' ball (c k) (r k)) = 0 := by
  intro P n G hG
  -- the critical image `G({x : DG(x) not injective})` is `Hⁿ`-null
  have hcrit : μHE[n] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    -- near a non-injective `A`, `G` shrinks `Hⁿ` by the factor `ε`
    have hloc : ∀ ε : NNReal, 0 < ε → ε ≤ 1 → ∀ A : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal,
        0 < δ ∧ (¬ Injective A → ∀ T : Set (Euclid n), ApproximatesLinearOn G A T δ →
          μHE[n] (G '' T) ≤ ε * volume T) := by
      intro ε hε hε1 A
      by_cases hA : Injective A
      · exact ⟨1, one_pos, fun h => absurd hA h⟩
      -- a unit vector `u` in the kernel of `A`
      obtain ⟨u, hu1, hAu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ A u = 0 := by
        rw [injective_iff_map_eq_zero] at hA
        push Not at hA
        obtain ⟨w, hw, hw0⟩ := hA
        refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
        · rw [map_smul, hw, smul_zero]
      set K : NNReal := ‖A‖₊ + 1 with hK
      have hK1 : 1 ≤ K := le_add_self
      have hKn : (0 : NNReal) < K ^ n := pow_pos (zero_lt_one.trans_le hK1) n
      set η : NNReal := ε / K ^ n with hη
      have hη0 : 0 < η := div_pos hε hKn
      have hη1 : (η : ℝ) ≤ 1 := by
        have : η ≤ ε := div_le_self (by positivity) (one_le_pow₀ hK1)
        exact_mod_cast this.trans hε1
      refine ⟨η, hη0, fun _ T hT => ?_⟩
      -- the compression `D w = w + (η - 1) ⟪u, w⟫ u` along `u`
      let D : Euclid n →ₗ[ℝ] Euclid n := LinearMap.id + ((η : ℝ) - 1) • (innerₛₗ ℝ u).smulRight u
      have hD : ∀ w, D w = w + (((η : ℝ) - 1) * inner ℝ u w) • u := by
        intro w
        simp [D, mul_smul]
      -- `det D = 1 + (η - 1) ‖u‖² = η` (matrix determinant lemma in the standard basis)
      have hdet : LinearMap.det D = η := by
        set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with hb
        have hM : LinearMap.toMatrix b b D =
            1 + Matrix.vecMulVec (fun i => u i) (fun j => ((η : ℝ) - 1) * u j) := by
          ext i j
          rw [LinearMap.toMatrix_apply, hD]
          simp [hb, Matrix.one_apply, Matrix.vecMulVec_apply, EuclideanSpace.inner_single_right]
          ring
        have hsum : ∑ j, u j * u j = 1 := by
          have h := real_inner_self_eq_norm_sq u
          rw [hu1, PiLp.inner_apply] at h
          simpa [sq] using h
        rw [← LinearMap.det_toMatrix b, hM, Matrix.vecMulVec_eq Unit,
          Matrix.det_one_add_replicateCol_mul_replicateRow]
        simp only [dotProduct, mul_assoc]
        rw [← Finset.mul_sum, hsum]
        ring
      -- `‖G y₁ - G y₂‖ ≤ ‖A (y₁ - y₂)‖ + η ‖y₁ - y₂‖ ≤ K ‖D (y₁ - y₂)‖` on `T`
      have hkey : ∀ y₁ ∈ T, ∀ y₂ ∈ T, ‖G y₁ - G y₂‖ ≤ K * ‖D y₁ - D y₂‖ := by
        intro y₁ h₁ y₂ h₂
        have happ : ‖G y₁ - G y₂ - A (y₁ - y₂)‖ ≤ η * ‖y₁ - y₂‖ := hT y₁ h₁ y₂ h₂
        rw [← map_sub]
        set w := y₁ - y₂
        have hAw : A w = A (D w) := by rw [hD, map_add, map_smul, hAu, smul_zero, add_zero]
        -- `‖D w‖² = ‖w‖² - (1 - η²) ⟪u, w⟫² ≥ η² ‖w‖²`
        have hnorm : (η : ℝ) * ‖w‖ ≤ ‖D w‖ := by
          have h1 : ‖D w‖ ^ 2 = ‖w‖ ^ 2 + ((η : ℝ) ^ 2 - 1) * inner ℝ u w ^ 2 := by
            rw [hD, norm_add_sq_real, inner_smul_right, norm_smul, real_inner_comm,
              Real.norm_eq_abs, hu1, mul_one, sq_abs]
            ring
          have h2 : inner ℝ u w ^ 2 ≤ ‖w‖ ^ 2 := by
            have h := abs_real_inner_le_norm u w
            rw [hu1, one_mul] at h
            exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
          have h3 : ((η : ℝ) * ‖w‖) ^ 2 ≤ ‖D w‖ ^ 2 := by
            rw [h1, mul_pow]
            have h4 : (η : ℝ) ^ 2 ≤ 1 := by nlinarith [η.coe_nonneg]
            nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
          exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3
        have hAD : ‖A (D w)‖ ≤ ‖A‖ * ‖D w‖ := A.le_opNorm _
        calc ‖G y₁ - G y₂‖ ≤ ‖A w‖ + ‖G y₁ - G y₂ - A w‖ := norm_le_insert' _ _
          _ ≤ ‖A‖ * ‖D w‖ + ‖D w‖ := by rw [hAw] at happ ⊢; linarith
          _ = K * ‖D w‖ := by simp [K]; ring
      -- `φ = G ∘ D⁻¹` is `K`-Lipschitz on `D '' T` and `G '' T ⊆ φ '' (D '' T)`
      let φ : Euclid n → Euclid P := fun z => G (Function.invFunOn D T z)
      have hφ : ∀ y ∈ T, Function.invFunOn D T (D y) ∈ T ∧ D (Function.invFunOn D T (D y)) = D y :=
        fun y hy => Function.invFunOn_pos ⟨y, hy, rfl⟩
      have hlip : LipschitzOnWith K φ (D '' T) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩
        obtain ⟨h₁', e₁⟩ := hφ y₁ h₁
        obtain ⟨h₂', e₂⟩ := hφ y₂ h₂
        have h := hkey _ h₁' _ h₂'
        rw [e₁, e₂] at h
        simpa only [dist_eq_norm] using h
      have hsub : G '' T ⊆ φ '' (D '' T) := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨D y, ⟨y, hy, rfl⟩, ?_⟩
        obtain ⟨h', e⟩ := hφ y hy
        have h := hkey _ h' _ hy
        rw [e, sub_self, norm_zero, mul_zero] at h
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
      -- `Hⁿ(G(T)) ≤ Kⁿ Hⁿ(D(T)) = Kⁿ |det D| Lⁿ(T) = ε Lⁿ(T)`
      calc μHE[n] (G '' T) ≤ μHE[n] (φ '' (D '' T)) := measure_mono hsub
        _ ≤ (K : ℝ≥0∞) ^ n * μHE[n] (D '' T) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
        _ = (K : ℝ≥0∞) ^ n * (ENNReal.ofReal |LinearMap.det D| * volume T) := by
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
        _ = ε * volume T := by
            rw [hdet, abs_of_nonneg η.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← mul_assoc,
              ← ENNReal.coe_pow, ← ENNReal.coe_mul, hη, mul_div_cancel₀ _ hKn.ne']
    -- on `C ∩ B̄_R(0)`: partition into pieces where `G` is close to some `DG(y)`, `y ∈ C`
    have hR : ∀ R : ℝ, μHE[n] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall 0 R)) = 0 := by
      intro R
      set s := {x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall (0 : Euclid n) R with hs
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' s) ≤ ε * volume (closedBall (0 : Euclid n) R) := by
        intro ε hε hε1
        rcases eq_empty_or_nonempty s with h | h
        · rw [h, image_empty, measure_empty]
          exact bot_le
        choose δ hδ using hloc ε hε hε1
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
            (fun x _ => (hG.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt) δ
            (fun A => (hδ A).1.ne')
        calc μHE[n] (G '' s) ≤ μHE[n] (⋃ k, G '' (s ∩ t k)) := by
              rw [← image_iUnion, ← inter_iUnion]
              exact measure_mono (image_mono (subset_inter Subset.rfl t_cover))
          _ ≤ ∑' k, μHE[n] (G '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R ∩ t k) := by
              refine ENNReal.tsum_le_tsum fun k => ?_
              obtain ⟨y, hy, hAy⟩ := Af' h k
              calc μHE[n] (G '' (s ∩ t k)) ≤ ε * volume (s ∩ t k) :=
                    (hδ (A k)).2 (by rw [hAy]; exact hy.1) _ (ht k)
                _ ≤ ε * volume (closedBall (0 : Euclid n) R ∩ t k) := by
                    gcongr
                    exact inter_subset_right
          _ = ε * volume (⋃ k, closedBall (0 : Euclid n) R ∩ t k) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact pairwise_disjoint_mono t_disj fun k => inter_subset_right
              · exact fun k => measurableSet_closedBall.inter (t_meas k)
          _ ≤ ε * volume (closedBall (0 : Euclid n) R) := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left
      -- let `ε → 0`
      have B : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
          (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
            (𝓝 0) (𝓝 (((0 : NNReal) : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))) :=
          ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
            (Or.inr measure_closedBall_lt_top.ne)
        simp only [zero_mul, ENNReal.coe_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      rw [← nonpos_iff_eq_zero]
      apply ge_of_tendsto B
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
      exact hbound ε hε.1 hε.2
    have h := measure_iUnion_null (μ := μHE[n]) fun k : ℕ => hR k
    rwa [← image_iUnion, iUnion_inter_closedBall_nat] at h
  classical
  -- candidate balls `B_{1/(p+1)}(e_q)`, `(q, p) = Nat.unpair k`, for a dense sequence `e`
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (Euclid n)
  let ctr : ℕ → Euclid n := fun k => e (Nat.unpair k).1
  let rad : ℕ → ℝ := fun k => 1 / ((Nat.unpair k).2 + 1 : ℝ)
  -- a candidate ball is good if `G` has a lower Lipschitz bound on it
  let good : ℕ → Prop := fun k => ∃ μ : ℝ, 0 < μ ∧
    ∀ a ∈ ball (ctr k) (rad k), ∀ b ∈ ball (ctr k) (rad k), μ * ‖a - b‖ ≤ ‖G a - G b‖
  refine ⟨ctr, fun k => if good k then rad k else 0,
    fun k => if h : good k then Exists.choose h else 1, fun k => ?_, fun k => ?_, ?_⟩
  · -- `m_k > 0`
    show 0 < if h : good k then Exists.choose h else 1
    split_ifs with h
    exacts [(Exists.choose_spec h).1, one_pos]
  · -- (i): the witness on a good ball; otherwise `B_0(c_k) = ∅`
    intro a ha b hb
    dsimp only at ha hb ⊢
    by_cases h : good k
    · rw [ite_eq_left h] at ha hb
      rw [dite_eq_left h]
      exact (Exists.choose_spec h).2 a ha b hb
    · rw [ite_eq_right h, ball_zero] at ha
      exact absurd ha (notMem_empty a)
  · -- (ii): each regular point lies in a good ball, so the remainder is in the critical image
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, fun hinj => hy ?_, rfl⟩
    obtain ⟨δ, μ, hδ, hμ, hlip⟩ :=
      Submission.codim1_rdo_c1cov_local_lower_lipschitz P n G x hG hinj
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt (half_pos hδ)
    obtain ⟨q, hq⟩ := he.exists_dist_lt x (Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((p : ℝ) + 1))
    have hk : Nat.unpair (Nat.pair q p) = (q, p) := Nat.unpair_pair q p
    -- `B_{1/(p+1)}(e_q) ⊆ B_δ(x)`, so this candidate ball is good
    have hsub : ball (ctr (Nat.pair q p)) (rad (Nat.pair q p)) ⊆ ball x δ := by
      intro a ha
      simp only [ctr, rad, hk, mem_ball] at ha ⊢
      calc dist a x ≤ dist a (e q) + dist (e q) x := dist_triangle _ _ _
        _ < 1 / ((p : ℝ) + 1) + 1 / ((p : ℝ) + 1) := add_lt_add ha (by rwa [dist_comm])
        _ < δ := by linarith
    have hgood : good (Nat.pair q p) :=
      ⟨μ, hμ, fun a ha b hb => hlip a (hsub ha) b (hsub hb)⟩
    refine mem_iUnion.2 ⟨Nat.pair q p, x, ?_, rfl⟩
    show x ∈ ball (ctr (Nat.pair q p)) (if good (Nat.pair q p) then rad (Nat.pair q p) else 0)
    rw [ite_eq_left hgood]
    simpa only [ctr, rad, hk, mem_ball] using hq
/-- **Simon Ch. 3, proof of Lemma 1.2** (properties (ii), (iii) of the pieces `g(B_r(c))`): the
image of an open ball under a `C¹` map `g : ℝⁿ → ℝᴾ` is Borel and has finite `Hⁿ`-measure.
`B_r(c) = ⋃ₜ closedBall(c, r − 1/(t+1))`, so `g(B_r(c))` is a countable union of compact sets;
`g` is Lipschitz on the compact convex `closedBall(c, r)`, so by Simon Ch. 2, 1.8(i)
`Hⁿ(g(B_r(c))) ≤ Λⁿ Lⁿ(B_r(c)) < ∞`. -/
theorem Submission.codim1_rdo_c1cov_image_ball_borel_finite : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r : ℝ), ContDiff ℝ 1 g → MeasurableSet (g '' ball c r) ∧ μHE[n] (g '' ball c r) ≠ ∞ := by
  intro P n g c r hg
  refine ⟨?_, ?_⟩
  · -- `B_r(c)` is the union of the compact balls `closedBall(c, r − 1/(t+1))`
    have hball : ball c r = ⋃ t : ℕ, closedBall c (r - 1 / ((t : ℝ) + 1)) := by
      ext y
      simp only [mem_ball, mem_iUnion, mem_closedBall]
      constructor
      · intro hy
        obtain ⟨t, ht⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
        exact ⟨t, by linarith⟩
      · rintro ⟨t, ht⟩
        have : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
        linarith
    rw [hball, image_iUnion]
    exact MeasurableSet.iUnion fun t =>
      ((isCompact_closedBall c _).image hg.continuous).isClosed.measurableSet
  · -- `g` is Lipschitz on the compact convex `closedBall c r`, hence on `ball c r`
    obtain ⟨K, hK⟩ := (hg.contDiffOn (s := closedBall c r)).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall c r) (isCompact_closedBall c r)
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hK.mono ball_subset_closedBall))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_ball_lt_top.ne
/-- Simon Ch. 3, Lemma 1.2, display (1) (corrected: `F(ℝⁿ) ⊆ E ∪ ⋃ᵢ Gᵢ(ℝⁿ)`, `Gᵢ : ℝⁿ → ℝᴾ`),
for one Lipschitz map `F : ℝⁿ → ℝᴾ`, given the scalar `C¹` approximation theorem (Simon Ch. 2,
Theorem 1.5) on `ℝⁿ` as the hypothesis.  Each coordinate `Fˡ` is `K`-Lipschitz; approximating it
with error `((i + 1)(P + 1))⁻¹` gives `C¹` maps `Gᵢ = (g_{i,l})ₗ` with `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`, so
`Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null, `Hⁿ(F(Z)) ≤ Kⁿ Lⁿ(Z) = 0` (Simon 2.1.8(i), `Hⁿ = Lⁿ` on `ℝⁿ`) and
`F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`. -/
theorem Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover : ∀ (P n : ℕ), (∀ (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) → ∀ (F : Euclid n → Euclid P) (K : NNReal), LipschitzWith K F → ∃ G : ℕ → Euclid n → Euclid P, (∀ i, ContDiff ℝ 1 (G i)) ∧ μHE[n] (range F \ ⋃ i, range (G i)) = 0 := by
  intro P n hH F K hF
  -- Step 1: the coordinates `Fˡ` of `F` are `K`-Lipschitz
  have hFl : ∀ l : Fin P, LipschitzWith K fun x => F x l := fun l =>
    LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (F x) (F y) l).trans (hF.dist_le_mul x y)
  -- Step 2: `C¹` approximation of every coordinate with error `δᵢ = ((i + 1)(P + 1))⁻¹`
  have hδ : ∀ i : ℕ, (0 : ℝ≥0∞) < (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := fun i =>
    ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) (by simp))
  choose g hg hgvol using fun (i : ℕ) (l : Fin P) => hH (fun x => F x l) K (hFl l) _ (hδ i)
  -- Step 3: `Gᵢ = (g_{i,1}, …, g_{i,P})` is `C¹`
  let G : ℕ → Euclid n → Euclid P := fun i x => WithLp.toLp 2 fun l => g i l x
  have hG : ∀ i, ContDiff ℝ 1 (G i) := fun i => (contDiff_piLp 2).2 fun l => hg i l
  -- Step 4: `{F ≠ Gᵢ} ⊆ ⋃ₗ {Fˡ ≠ g_{i,l} ∨ DFˡ ≠ Dg_{i,l}}`, so `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`
  have hsub : ∀ i, {x | F x ≠ G i x} ⊆
      ⋃ l, {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} := by
    intro i x hx
    obtain ⟨l, hl⟩ : ∃ l, F x l ≠ g i l x := by
      by_contra! h
      exact hx (PiLp.ext h)
    exact mem_iUnion.2 ⟨l, Or.inl hl⟩
  have hvol : ∀ i : ℕ, volume {x | F x ≠ G i x} ≤ ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i
    calc volume {x | F x ≠ G i x}
        ≤ ∑ l, volume {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} :=
          (measure_mono (hsub i)).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _l : Fin P, (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ :=
          Finset.sum_le_sum fun l _ => (hgvol i l).le
      _ = (P : ℝ≥0∞) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by simp
      _ ≤ ((P : ℝ≥0∞) + 1) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by gcongr; exact le_self_add
      _ = ((i : ℝ≥0∞) + 1)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_left_comm,
            ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
  -- Step 5: `Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null
  have hZ : volume (⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm (le_of_forall_gt fun ε hε => ?_) bot_le
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    calc volume (⋂ i, {x | F x ≠ G i x}) ≤ volume {x | F x ≠ G i x} := measure_mono (iInter_subset _ i)
      _ ≤ ((i : ℝ≥0∞) + 1)⁻¹ := hvol i
      _ ≤ (i : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hi
  -- Step 6: `Hⁿ(F(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`
  have hFZ : μHE[n] (F '' ⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μHE[n] (F '' ⋂ i, {x | F x ≠ G i x})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] (⋂ i, {x | F x ≠ G i x}) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- Step 7: `F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`
  refine ⟨G, hG, measure_mono_null ?_ hFZ⟩
  rintro _ ⟨⟨x, rfl⟩, hy⟩
  exact ⟨x, mem_iInter.2 fun i h => hy (mem_iUnion.2 ⟨i, x, h.symm⟩), rfl⟩
/-- **Whitney's `C¹` extension theorem** (Simon Ch. 2, 1.6; proof of Evans–Gariepy §6.5).  If
`A ⊆ ℝⁿ` is closed, `h` and `D` are continuous on `A`, and the remainder
`h y - h x - D x (y - x)` is `o(|y - x|)` uniformly for `x` in compact subsets of `A`, then some
`g ∈ C¹(ℝⁿ)` has `g = h` and `Dg = D` on `A`.  With `r x = min(1, dist(x, A)) / 100`, Vitali's
lemma selects disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `ℝⁿ \ A`;
nearby radii are comparable, so the overlap is uniformly bounded.  Rescaled bumps divided by
their locally finite sum give a partition of unity `w c` on `ℝⁿ \ A` with
`∑ ‖D(w c)(x)‖ ≤ M / r x`.  Put `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`, where
`P b x = h b + D b (x - b)` and `pr c ∈ A` is a nearest point. -/
theorem Submission.codim1_rdo_c1a_whitney_extension : ∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
  intro n A h D hA hh hD hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  -- the Whitney radius `r x = min 1 (dist x A) / 100`
  obtain ⟨r, hr⟩ : ∃ r : Euclid n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := fun x y => by
    have h₁ := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h₁
    have h₂ := (abs_sub_le_iff.mp h₁).1
    rw [hr, hr]; linarith
  -- radii of nearby centres are comparable
  have hnear : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := hrlip x c
    have h₂ := hrlip c x
    rw [dist_comm c x] at h₂
    have := hr0 x
    have := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `Aᶜ`
  obtain ⟨Z, hZA, hZdisj, hZcov⟩ : ∃ Z ⊆ Aᶜ, Z.PairwiseDisjoint (fun c => ball c (r c)) ∧
      ∀ x ∉ A, ∃ c ∈ Z, dist x c < 4 * r c := by
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      simpa only [mem_ball, dist_comm] using lt_of_not_ge hlt
    exact Set.disjoint_left.mp (hZdisj hc hd hcd) hdc (mem_ball_self (hrpos d (hZA hd)))
  -- a `1/2`-separated subset of `B̄(0, 21)` has at most `N` points
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Euclid n), s ⊆ closedBall (0 : Euclid n) 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Euclid n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hssep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Euclid n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Euclid n) ≠ (y : Euclid n) := fun e => hxy' (Subtype.ext e)
      have hd := hssep x.property y.property hne'
      have htri := dist_triangle (x : Euclid n) (c x : Euclid n) (y : Euclid n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Euclid n) (c x : Euclid n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- bounded overlap: at most `N` centres are near any `x ∉ A`
  have hover : ∀ x ∉ A, {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := hrpos x hx
    let f : Euclid n → Euclid n := fun c => (r x)⁻¹ • (c - x)
    have hf : Injective f := by
      intro c d hcd
      have e := congrArg (fun z : Euclid n => r x • z) hcd
      simpa [f, smul_smul, hrx.ne'] using e
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖f c‖ ≤ 21 := by
      intro c hc
      have hd := (hnear x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      simp only [f]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep' : (f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun e => hcd (congrArg f e)
      have hdist := hsep c hc.1 d hd.1 hcd'
      have hrad := (hnear x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        simpa only [dist_eq_norm] using hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      simp only [f]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Euclid n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep'
    exact ⟨hfin.of_finite_image hf.injOn, by rwa [Set.ncard_image_of_injective _ hf] at hcard⟩
  -- the finite set `F x` of centres near `x ∉ A`
  have hfin : ∀ x ∉ A, {c : Z | dist x c ≤ r x + 10 * r c}.Finite := by
    intro x hx
    apply ((hover x hx).1.preimage (Subtype.val_injective (p := (· ∈ Z))).injOn).subset
    intro c hc
    exact ⟨c.property, hc⟩
  have hFex : ∀ x, ∃ s : Finset Z, x ∉ A → ∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun hx' => absurd hx hx'⟩
    · exact ⟨(hfin x hx).toFinset, fun _ c => by simp⟩
  choose F hF using hFex
  have hFcard : ∀ x ∉ A, (F x).card ≤ N := by
    intro x hx
    have hsub : (F x).map (Embedding.subtype _) ⊆ (hover x hx).1.toFinset := by
      intro c hc
      simp only [Finset.mem_map, Embedding.coe_subtype] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Set.Finite.mem_toFinset]
      exact ⟨c'.property, (hF x hx c').mp hc'⟩
    calc (F x).card = ((F x).map (Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (hover x hx).1.toFinset.card := Finset.card_le_card hsub
      _ = {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard :=
          (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ N := (hover x hx).2
  -- a smooth bump `ψ = 1` on `B̄(0, 4)`, `ψ = 0` off `B(0, 8)`
  obtain ⟨ψ, hψc, hψ0, hψ1, hψin, hψout, L, hL⟩ : ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 4 → ψ x = 1) ∧
      (∀ x, 8 ≤ ‖x‖ → ψ x = 0) ∧ ∃ L : NNReal, LipschitzWith L ψ := by
    let b : ContDiffBump (0 : Euclid n) := ⟨4, 8, by norm_num, by norm_num⟩
    have hb : ContDiff ℝ 1 b := b.contDiff
    obtain ⟨L, hL⟩ := hb.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
    refine ⟨b, hb, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_, fun x hx => ?_, L, hL⟩
    · exact b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    · apply notMem_support.mp
      rw [b.support_eq]
      exact fun hxb => absurd (mem_ball_zero_iff.mp hxb) (not_lt.mpr hx)
  -- the rescaled bumps `φ c x = ψ ((x - c) / r c)`
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid n → Euclid n → ℝ, ∀ c x, φ c x = ψ ((r c)⁻¹ • (x - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφfun : ∀ c, φ c = fun x => ψ ((r c)⁻¹ • (x - c)) := fun c => funext (hφ c)
  have hφc : ∀ c, ContDiff ℝ 1 (φ c) := by
    intro c
    rw [hφfun c]
    exact hψc.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hφ0 : ∀ c x, 0 ≤ φ c x := fun c x => by rw [hφ]; exact hψ0 _
  have hφin : ∀ c x, 0 < r c → dist x c ≤ 4 * r c → φ c x = 1 := by
    intro c x hc hx
    rw [hφ]
    apply hψin
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (r c)⁻¹ * dist x c ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have hφout : ∀ c x, 0 < r c → 8 * r c ≤ dist x c → φ c x = 0 := by
    intro c x hc hx
    rw [hφ]
    apply hψout
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * dist x c := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, hBb⟩ : ∃ B : ℝ, 0 < B ∧ ∀ c, 0 < r c → ∀ x, ‖fderiv ℝ (φ c) x‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c hc x => ?_⟩
    let ρ : NNReal := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Euclid n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (φ c) := by
      rw [hφfun c]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (φ c) x‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- near `x ∉ A`, only the bumps indexed by `F x` are active
  have hφzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc
    apply hφout c y (hrpos c (hZA c.property))
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun e => hc ((hF x hx c).mpr e)
    have ht := dist_triangle x y (c : Euclid n)
    rw [dist_comm x y] at ht
    have := hr0 (c : Euclid n)
    linarith
  have hyA : ∀ x ∉ A, ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA'
    have hi := infDist_le_dist_of_mem (x := x) hyA'
    have hr' := hrd x
    rw [dist_comm x y] at hi
    linarith [hr0 x]
  -- the locally finite sum `S = ∑ φ c`
  obtain ⟨S, hS⟩ : ∃ S : Euclid n → ℝ, ∀ x, S x = ∑ᶠ c : Z, φ c x := ⟨_, fun _ => rfl⟩
  have hSnear : ∀ x ∉ A, ∀ y, dist y x < r x → S y = ∑ c ∈ F x, φ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hcF
    exact hc (hφzero x hx y hy c hcF)
  have hSev : ∀ x ∉ A, S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSnear x hx y hy
  have hSc : ∀ x ∉ A, ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (c : Z) y => φ c y) (s := F x) fun c _ => hφc c).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hSfd : ∀ x ∉ A, fderiv ℝ S x = ∑ c ∈ F x, fderiv ℝ (φ c) x := by
    intro x hx
    rw [(hSev x hx).fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (hφc c).differentiable one_ne_zero x)
  have hS1 : ∀ x ∉ A, 1 ≤ S x := by
    intro x hx
    have hrx := hrpos x hx
    rw [hSnear x hx x (by simpa using hrx)]
    obtain ⟨c, hc, hxc⟩ := hZcov x hx
    have hi : (⟨c, hc⟩ : Z) ∈ F x := by
      rw [hF x hx]
      have := hr0 c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = φ c x := (hφin c x (hrpos c (hZA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, φ c x :=
          Finset.single_le_sum (f := fun c : Z => φ c x) (fun c _ => hφ0 c x) hi
  -- the partition of unity `w c = φ c / S` on `Aᶜ`
  obtain ⟨w, hw⟩ : ∃ w : Z → Euclid n → ℝ, ∀ c x, w c x = φ c x / S x := ⟨_, fun _ _ => rfl⟩
  have hwfun : ∀ c, w c = fun x => φ c x / S x := fun c => funext (hw c)
  have hwc : ∀ c : Z, ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    rw [hwfun c]
    exact (hφc c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hw0 : ∀ c : Z, ∀ x ∉ A, 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (hφ0 c x) (le_trans zero_le_one (hS1 x hx))
  have hwzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, hφzero x hx y hy c hc, zero_div]
  have hwsum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ F x, w c y = 1 := by
    intro x hx y hy
    simp only [hw, ← Finset.sum_div, ← hSnear x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hyA x hx y hy))))
  have hwdsum : ∀ x ∉ A, ∑ c ∈ F x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hwsum x hx y hy
    have hh' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh'
    rw [fderiv_fun_sum (fun c _ => (hwc c x hx).differentiableAt one_ne_zero)] at hh'
    exact hh'
  have hwd_le : ∀ x ∉ A, ∀ c : Z,
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro x hx c
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hSi : (S x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1x
    have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ S x ^ 2 by nlinarith)
    have hb := ((hφc c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x := by
      simpa only [hwfun, div_eq_mul_inv, Function.comp_def] using hprod.fderiv
    rw [hder]
    have hb0 := hφ0 c x
    have hb1 : φ c x ≤ 1 := by rw [hφ]; exact hψ1 _
    calc ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x‖
        ≤ ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (φ c) x‖ :=
          norm_add_le _ _
      _ = φ c x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (φ c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (φ c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
  -- `∑_{c ∈ F x} ‖D w_c(x)‖ ≤ M / r x`
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∉ A, ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * B / r x := ⟨_, rfl⟩
    have hT : 0 ≤ T := by rw [hT_def]; positivity
    have hb' : ∀ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ T := by
      intro c hc
      have hcr := hrpos c (hZA c.property)
      have hlow := (hnear x c ((hF x hx c).mp hc)).1
      refine (hBb c hcr x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = T := by rw [hT_def]; ring
    have hcard : ((F x).card : ℝ) ≤ N := by exact_mod_cast hFcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSfd x hx]
      calc ‖∑ c ∈ F x, fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ F x, T := Finset.sum_le_sum hb'
        _ = ((F x).card : ℝ) * T := by simp
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ T + (N : ℝ) * T := fun c hc =>
      (hwd_le x hx c).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ F x, (T + (N : ℝ) * T) := Finset.sum_le_sum hw'
      _ = ((F x).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
  -- the affine jets `P b x = h b + D b (x - b)`
  obtain ⟨P, hP⟩ : ∃ P : Euclid n → Euclid n → ℝ, ∀ b x, P b x = h b + D b (x - b) :=
    ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ b, P b = fun x => h b + D b (x - b) := fun b => funext (hP b)
  have hPc : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    rw [hPfun b]
    exact contDiff_const.add ((D b).contDiff.comp (contDiff_id.sub contDiff_const))
  have hPd : ∀ b x, HasFDerivAt (P b) (D b) x := by
    intro b x
    have e := (((D b).hasFDerivAt (x := x)).sub_const (D b b)).const_add (h b)
    have hfun : (fun y => h b + D b (y - b)) = fun y => h b + (D b y - D b b) := by
      funext y
      rw [map_sub]
    rw [hPfun b, hfun]
    exact e
  have hPsub : ∀ a b x,
      ‖P b x - P a x‖ ≤ ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
    intro a b x
    have heq : P b x - P a x = (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
      have hx : x - a = (x - b) + (b - a) := by abel
      simp only [hP, hx, map_add, sub_apply]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))
  -- nearest points `pr x ∈ A`
  choose pr hprA hprd using fun x => hA.exists_infDist_eq_dist hne x
  have hprle : ∀ x, ∀ a ∈ A, dist x (pr x) ≤ dist x a := by
    intro x a ha
    rw [← hprd x]
    exact infDist_le_dist_of_mem ha
  have hpr2 : ∀ x, ∀ a ∈ A, dist (pr x) a ≤ 2 * dist x a := by
    intro x a ha
    have ht := dist_triangle (pr x) x a
    rw [dist_comm (pr x) x] at ht
    linarith [hprle x a ha]
  have hanc1 : ∀ x ∉ A, ∀ c : Z, c ∈ F x → dist x (pr c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hd := (hnear x c ((hF x hx c).mp hc)).2.2
    have hr' := hrd x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Euclid n)) (y := x)
    have ht := dist_triangle x (c : Euclid n) (pr c)
    rw [dist_comm (c : Euclid n) x] at hi
    rw [← hprd (c : Euclid n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have hanc2 : ∀ x ∉ A, ∀ a ∈ A, ∀ c : Z, c ∈ F x → dist (pr c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := hanc1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (pr c) x a
    rw [dist_comm (pr c) x] at ht
    linarith
  -- uniform estimates near a point of `A`
  have hloc : ∀ a ∈ A, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ η) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ η * ‖c - b‖ := by
    intro a ha η hη
    obtain ⟨r₀, hr₀, hrem₀⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left η hη
    obtain ⟨η₀, hη₀, hD₀⟩ := Metric.continuousWithinAt_iff.mp (hD a ha) η hη
    have hδ1 : min 1 (min η₀ (r₀ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η₀ (r₀ / 3)) ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hδr : min 1 (min η₀ (r₀ / 3)) ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η₀ (r₀ / 3)), lt_min one_pos (lt_min hη₀ (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      simpa only [dist_eq_norm] using (hD₀ hb (hba.trans_le hδη)).le
    · intro b hb hba c hc hca
      apply hrem₀ b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- convex combinations
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : Finset Z)
      (a : Z → ℝ) (v : Z → G) (b : ℝ), (∀ i ∈ s, 0 ≤ a i) → ∑ i ∈ s, a i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, a i • v i‖ ≤ b := by
    intro G _ _ s a v b ha hs hv
    calc ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, a i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (ha i hi)]
      _ ≤ ∑ i ∈ s, a i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (ha i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- the extension: `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid n → ℝ, ∀ x,
      g x = if x ∈ A then h x else ∑ᶠ c : Z, w c x * P (pr c) x := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgnear : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hyA x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (pr c) y = 0
    rw [hwzero x hx y hy c hc', zero_mul]
  have hgev : ∀ x ∉ A, g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgnear x hx y hy
  have hgc : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ F x, w c y * P (pr c) y) x :=
      ContDiffAt.sum (fun c _ => (hwc c x hx).mul (hPc _).contDiffAt)
    exact hs.congr_of_eventuallyEq (hgev x hx)
  have hgfd : ∀ x ∉ A, fderiv ℝ g x =
      ∑ c ∈ F x, (w c x • D (pr c) + P (pr c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(hgev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((hwc c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hPd _ x)
  -- `Dg = D` on `A`
  have hgd : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, -, hDδ, hremδ⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by simpa using hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA]
      have hr' := hremδ a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hxx : dist x x < r x := by simpa using hrpos x hxA
      have hid : g x - h a - D a (x - a) = ∑ c ∈ F x, w c x • (P (pr c) x - P a x) := by
        rw [hgnear x hxA x hxx]
        simp only [smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum x hxA x hxx, one_mul, hP a x]
        ring
      rw [hid]
      apply hconv (F x) (fun c => w c x) (fun c => P (pr c) x - P a x) _
        (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx)
      intro c hc
      have hbA := hprA (c : Euclid n)
      have hba := hanc2 x hxA a ha c hc
      have hxb : dist x (pr c) ≤ 2 * dist x a :=
        (hanc1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr c) hbA hbaδ
      have hr' := hremδ a ha haa (pr c) hbA hbaδ
      have hba' : ‖pr c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
      have hxb' : ‖x - pr c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
      calc ‖P (pr c) x - P a x‖
          ≤ ‖h (pr c) - h a - D a (pr c - a)‖ + ‖D (pr c) - D a‖ * ‖x - pr c‖ :=
            hPsub a (pr c) x
        _ ≤ (ε / 5) * ‖pr c - a‖ + (ε / 5) * ‖x - pr c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  -- `Dg` is continuous at the points of `A`
  have hgcont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by rw [hη_def]; field_simp
    have hηε : η ≤ ε / 2 := by nlinarith [mul_pos hη hM]
    obtain ⟨δ, hδ, hδ1, hDδ, hremδ⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [(hgd a ha).fderiv, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [(hgd x hxA).fderiv]
      exact (hDδ x hxA (by linarith)).trans hηε
    · have hrx := hrpos x hxA
      have hxx : dist x x < r x := by simpa using hrx
      have hbA := hprA x
      have hbaδ : dist (pr x) a < δ := by
        linarith [hpr2 x a ha, dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := by
        rw [hr x, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ F x, ‖D (pr c) - D a‖ ≤ η := by
        intro c hc
        apply hDδ _ (hprA c)
        have hi := hanc2 x hxA a ha c hc
        linarith [dist_nonneg (x := x) (y := a)]
      have hP' : ∀ c ∈ F x, ‖P (pr c) x - P (pr x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA := hprA (c : Euclid n)
        have hda := hanc2 x hxA a ha c hc
        have hdaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
        have hxd := hanc1 x hxA c hc
        have hxb : dist x (pr x) = infDist x A := (hprd x).symm
        have hdb : dist (pr c) (pr x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (pr c) x (pr x)
          rw [dist_comm (pr c) x, hxb] at ht
          linarith
        have hDd : ‖D (pr c) - D (pr x)‖ ≤ 2 * η := by
          calc ‖D (pr c) - D (pr x)‖ = ‖(D (pr c) - D a) - (D (pr x) - D a)‖ := by
                congr 1; abel
            _ ≤ ‖D (pr c) - D a‖ + ‖D (pr x) - D a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hremδ (pr x) hbA hbaδ (pr c) hdA hdaδ
        have hdb' : ‖pr c - pr x‖ ≤ 3 * infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - pr c‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
        calc ‖P (pr c) x - P (pr x) x‖
            ≤ ‖h (pr c) - h (pr x) - D (pr x) (pr c - pr x)‖ +
                ‖D (pr c) - D (pr x)‖ * ‖x - pr c‖ := hPsub (pr x) (pr c) x
          _ ≤ η * ‖pr c - pr x‖ + (2 * η) * ‖x - pr c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hsplit : fderiv ℝ g x - D a = (∑ c ∈ F x, w c x • (D (pr c) - D a)) +
          ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x := by
        rw [hgfd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hwsum x hxA x hxx, hwdsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hsplit]
      calc ‖(∑ c ∈ F x, w c x • (D (pr c) - D a)) +
            ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ F x, w c x • (D (pr c) - D a)‖ +
              ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact hconv (F x) (fun c => w c x) (fun c => D (pr c) - D a) η
                (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx) hD'
            · calc ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ F x, ‖(P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ c ∈ F x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ :=
                    (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = ε / 2 := heq
  refine ⟨g, ?_, fun a ha => hgA a ha, hgd⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (hgd x hx).differentiableAt
    · exact (hgc x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact hgcont x hx
    · exact (hgc x hx).continuousAt_fderiv one_ne_zero
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

/-- **Lusin's theorem** for `Lⁿ` with a closed set, `Lⁿ(B) = ∞` allowed (Simon Ch. 2, proof of
1.5, step 2, glued as in the infinite-measure case of Simon 1.15(2)).  On the bounded Borel shells
`S_j = {j ≤ ‖x‖ < j + 1}`, the compact form `dor_ims_lusin_measurable_continuousOn` gives compact
`K_j ⊆ B ∩ S_j` with `Lⁿ((B ∩ S_j) \ K_j) < δ_j` on which `g` is continuous, where `∑ δ_j < ε`.
As `K_j ⊆ S_j`, the family `(K_j)` is locally finite, so `C = ⋃ⱼ K_j` is closed and `g` is
continuous on `C`; and `B \ C ⊆ ⋃ⱼ (B ∩ S_j) \ K_j` has measure `< ε`. -/
theorem Submission.codim1_rdo_c1a_lusin_isClosed : ∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε := by
  intro n Y _ _ _ _ g B hg hB ε hε
  -- bounded Borel shells `S_j = {j ≤ ‖x‖ < j + 1}`, each of finite measure; `x ∈ S_⌊‖x‖⌋`
  set S : ℕ → Set (Euclid n) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSμ : ∀ j, volume (S j) ≠ ∞ := fun j =>
    ((measure_mono fun x hx => mem_closedBall_zero_iff.mpr hx.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hxS : ∀ x : Euclid n, x ∈ S ⌊‖x‖⌋₊ := fun x =>
    ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- weights `δ_j > 0` with `∑ δ_j < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- Lusin on each shell: compact `K_j ⊆ B ∩ S_j`, defect `< δ_j`, `g` continuous on `K_j`
  choose K hK hKB hKμ hKg using fun j =>
    Submission.dor_ims_lusin_measurable_continuousOn n volume (B ∩ S j) g (δ j) hg
      (hB.inter (hSm j)) (ne_top_of_le_ne_top (hSμ j) (measure_mono inter_subset_right))
      (hδ j).ne'
  -- `K_j ⊆ S_j`, so `ball x 1` meets `K_j` only for the finitely many `j < ‖x‖ + 1`
  have hlf : LocallyFinite K := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyK, hyx⟩
    refine Nat.lt_ceil.mpr ((hKB j hyK).2.1.trans_lt ?_)
    calc ‖y‖ ≤ ‖x‖ + dist y x := norm_le_norm_add_const_of_dist_le le_rfl
      _ < ‖x‖ + 1 := by linarith [mem_ball.mp hyx]
  -- hence `C = ⋃ⱼ K_j` is closed and `g` is continuous on `C`
  refine ⟨⋃ j, K j, iUnion_subset fun j => (hKB j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j => (hK j).isClosed,
    hlf.continuousOn_iUnion (fun j => (hK j).isClosed) hKg, ?_⟩
  -- `x ∈ B \ C` lies in `(B ∩ S_j) \ K_j` for `j = ⌊‖x‖⌋`
  calc volume (B \ ⋃ j, K j) ≤ volume (⋃ j, (B ∩ S j) \ K j) :=
        measure_mono fun x hx => mem_iUnion.mpr
          ⟨⌊‖x‖⌋₊, ⟨hx.1, hxS x⟩, fun hxK => hx.2 (mem_iUnion_of_mem _ hxK)⟩
    _ ≤ ∑' j, volume ((B ∩ S j) \ K j) := measure_iUnion_le _
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (hKμ j).le
    _ < ε := hδε
/-- **Egoroff's theorem** on `ℝⁿ` with a closed good set (steps 5–6 of Simon's proof of Ch. 2,
1.5).  If `C` is measurable (possibly `|C| = ∞`), `η_k` and `g` are measurable and `η_k → g`
pointwise on `C`, then for every `ε > 0` there is a closed `A ⊆ C` with `|C \ A| < ε` such that
`η_k → g` uniformly on every compact `Q ⊆ A`.  For weights `δ_j > 0` with `∑ δ_j < ε`, Egoroff on
the finite-measure sets `C ∩ B_{j+1}(0)` gives `t_j` with `|t_j| ≤ δ_j / 2`; put
`A₀ = C \ ⋃ t_j`.  Outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with excess `< δ_j / 2`,
so `A = (⋃ U_j)ᶜ ⊆ A₀` is closed and `C \ A ⊆ ⋃ (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`.  A compact
`Q ⊆ A` is bounded, so `Q ⊆ (C ∩ B_{j+1}(0)) \ t_j` for large `j`. -/
theorem Submission.codim1_rdo_c1a_egorov_isClosed : ∀ (n : ℕ) (C : Set (Euclid n)) (η : ℕ → Euclid n → ℝ) (g : Euclid n → ℝ), MeasurableSet C → (∀ k, Measurable (η k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n C η g hC hη hg hconv ε hε
  -- weights `δ_j > 0` with `∑ δ_j < ε`; every `s ∩ B_{j+1}(0)` has finite measure
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hB : ∀ (j : ℕ) (s : Set (Euclid n)), volume (s ∩ ball 0 (j + 1)) ≠ ∞ := fun j s =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Egoroff on `C_j = C ∩ B_{j+1}(0)`: `η_k → g` uniformly on `C_j \ t_j`, `|t_j| ≤ δ_j / 2`
  choose t htC htm htμ htu using fun j : ℕ =>
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hC.inter measurableSet_ball) (hB j C)
      (ae_of_all _ fun x hx => hconv x hx.1) (ENNReal.half_pos (hδ j).ne')
  -- `A₀ = C \ ⋃ t_j`; outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with small excess
  have hA₀ : MeasurableSet (C \ ⋃ j, t j) := hC.diff (MeasurableSet.iUnion htm)
  choose U hUD hUo hUf hUμ using fun j : ℕ =>
    (hA₀.compl.inter measurableSet_ball).exists_isOpen_sdiff_lt (hB j _)
      (ENNReal.half_pos (hδ j).ne').ne'
  -- the balls cover `A₀ᶜ`, so the closed set `A = (⋃ U_j)ᶜ` lies in `A₀`
  have hAA₀ : (⋃ j, U j)ᶜ ⊆ C \ ⋃ j, t j := by
    refine compl_subset_comm.1 fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨j, hUD j ⟨hx, mem_ball.2 (by linarith)⟩⟩
  refine ⟨(⋃ j, U j)ᶜ, hAA₀.trans sdiff_subset, (isOpen_iUnion hUo).isClosed_compl, ?_, ?_⟩
  -- `C \ A ⊆ ⋃_j (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`, and each piece has measure `≤ δ_j`
  · calc volume (C \ (⋃ j, U j)ᶜ)
        ≤ volume (⋃ j, (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1))))) := by
          refine measure_mono fun x ⟨hxC, hxU⟩ => ?_
          obtain ⟨j, hj⟩ := mem_iUnion.1 (not_not.1 hxU)
          by_cases hxt : x ∈ ⋃ i, t i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hxt
            exact mem_iUnion.2 ⟨i, Or.inl hi⟩
          · exact mem_iUnion.2 ⟨j, Or.inr ⟨hj, fun h => h.1 ⟨hxC, hxt⟩⟩⟩
      _ ≤ ∑' j, volume (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1)))) :=
          measure_iUnion_le _
      _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (measure_union_le _ _).trans <|
          (add_le_add (htμ j) (hUμ j).le).trans (ENNReal.add_halves _).le
      _ < ε := hδε
  -- a compact `Q ⊆ A` is bounded, so `Q ⊆ C_j \ t_j` for large `j`
  · intro Q hQ hQA
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball 0
    obtain ⟨j, hj⟩ := exists_nat_ge R
    refine (htu j).mono fun x hx => ⟨⟨(hAA₀ (hQA hx)).1, ?_⟩, fun hxt => ?_⟩
    · exact ball_subset_ball (by linarith) (hR hx)
    · exact (hAA₀ (hQA hx)).2 (mem_iUnion.2 ⟨j, hxt⟩)
/-- **Whitney's hypothesis 1.6(∗) on a large closed set** (Simon Ch. 2, proof of Theorem 1.5).
Let `f : ℝⁿ → ℝ` be `L`-Lipschitz and differentiable at every point of the closed set `C`, with
`Df` continuous on `C`.  The remainder quotient `R(x, y) = |f(y) − f(x) − Df(x)(y − x)| / |y − x|`
is at most `2L`, and `η_k(x) = sup {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}` (`0` off `C`)
tends to `0` on `C`.  Each `{η_k > t}`, `t ≥ 0`, is relatively open in `C`, so `η_k` is Borel,
and Egorov's theorem in closed form gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that
`η_k → 0` uniformly on every compact `Q ⊆ A`.  Then `R(x, y) ≤ η_k(x) < ε'` for `x ∈ Q`,
`y ∈ A`, `0 < |x − y| < 1/(k + 1)`. -/
theorem Submission.codim1_rdo_c1a_whitney_remainder : ∀ (n : ℕ) (f : Euclid n → ℝ) (L : NNReal) (C : Set (Euclid n)), LipschitzWith L f → IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ContinuousOn (fderiv ℝ f) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f L C hf hC hdiff hDf ε hε
  classical
  -- the remainder quotient `R(x, y)`, bounded by `2L` since `‖Df(x)‖ ≤ L`
  let R : Euclid n → Euclid n → ℝ := fun x y => ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖
  have hR_le : ∀ x y, R x y ≤ 2 * L := by
    intro x y
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖y - x‖ + L * ‖y - x‖ := by
          refine add_le_add ?_ ?_
          · rw [← dist_eq_norm, ← dist_eq_norm]
            exact hf.dist_le_mul y x
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      _ = 2 * L * ‖y - x‖ := by ring
  -- `η_k(x) = sup E_k(x)`, `E_k(x) = {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}`, on `C`
  let E : ℕ → Euclid n → Set ℝ := fun k x =>
    R x '' {y | y ∈ C ∧ 0 < dist y x ∧ dist y x < 1 / ((k : ℝ) + 1)}
  let η : ℕ → Euclid n → ℝ := fun k x => if x ∈ C then sSup (E k x) else 0
  have hη_nonneg : ∀ k x, 0 ≤ η k x := by
    intro k x
    by_cases hx : x ∈ C
    · simp only [η, ite_eq_left hx]
      exact Real.sSup_nonneg (by
        rintro _ ⟨y, -, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [η, ite_eq_right hx, le_refl]
  have hR_le_η : ∀ (k : ℕ) x y, x ∈ C → y ∈ C → 0 < dist y x → dist y x < 1 / ((k : ℝ) + 1) →
      R x y ≤ η k x := by
    intro k x y hx hy h0 h1
    simp only [η, ite_eq_left hx]
    exact le_csSup ⟨2 * L, by rintro _ ⟨z, -, rfl⟩; exact hR_le x z⟩ ⟨y, ⟨hy, h0, h1⟩, rfl⟩
  -- `η_k(x) → 0` for `x ∈ C`, by differentiability of `f` at `x`
  have hη_tendsto : ∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hρx⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      simp only [η, ite_eq_left hx]
      refine Real.sSup_le ?_ (half_pos he).le
      rintro _ ⟨y, ⟨-, -, h1⟩, rfl⟩
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos he).le
        (hρx (h1.trans_le ((Nat.one_div_le_one_div hk).trans hN.le)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη_nonneg k x)]
    exact hle.trans_lt (half_lt_self he)
  -- `{η_k > t}` is relatively open in the closed set `C` for `t ≥ 0`, so `η_k` is Borel
  have hη_meas : ∀ k, Measurable (η k) := by
    intro k
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · convert MeasurableSet.univ
      exact eq_univ_of_forall fun x => ht.trans_le (hη_nonneg k x)
    have hUC : η k ⁻¹' Ioi t ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : t < η k x := hx
      simp only [η, ite_eq_right hxC] at hx'
      exact absurd hx' (not_lt.mpr ht)
    have hnhds : ∀ x ∈ η k ⁻¹' Ioi t, η k ⁻¹' Ioi t ∪ Cᶜ ∈ 𝓝 x := by
      intro x hx
      have hxC := hUC hx
      have hxt : t < sSup (E k x) := by
        have hx' : t < η k x := hx
        simpa only [η, ite_eq_left hxC] using hx'
      have hne : (E k x).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Real.sSup_empty] at hxt
        exact absurd hxt (not_lt.mpr ht)
      obtain ⟨_, ⟨y, ⟨hy, h0, h1⟩, rfl⟩, hty⟩ := exists_lt_of_lt_csSup hne hxt
      -- `z ↦ R(z, y)` is continuous within `C` at `x`, as `f` and `Df|_C` are continuous
      have hsub : ContinuousWithinAt (fun z => y - z) C x :=
        continuousWithinAt_const.sub continuousWithinAt_id
      have hnum : ContinuousWithinAt (fun z => ‖f y - f z - fderiv ℝ f z (y - z)‖) C x :=
        ((continuousWithinAt_const.sub hf.continuous.continuousWithinAt).sub
          ((hDf x hxC).clm_apply hsub)).norm
      have hRy : ContinuousWithinAt (fun z => R z y) C x :=
        hnum.div hsub.norm (norm_sub_pos_iff.mpr (dist_pos.mp h0)).ne'
      have hdist : Tendsto (fun z => dist y z) (𝓝 x) (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist tendsto_id
      -- near `x`, every `z ∈ C` has `η_k(z) ≥ R(z, y) > t`
      filter_upwards [eventually_nhdsWithin_iff.mp (Filter.Tendsto.eventually_const_lt hty hRy),
        hdist.eventually_const_lt h0, hdist.eventually_lt_const h1] with z hz hz0 hz1
      by_cases hzC : z ∈ C
      · exact Or.inl ((hz hzC).trans_le (hR_le_η k z y hzC hy hz0 hz1))
      · exact Or.inr hzC
    have heq : η k ⁻¹' Ioi t = C ∩ interior (η k ⁻¹' Ioi t ∪ Cᶜ) := by
      refine Subset.antisymm
        (fun x hx => ⟨hUC hx, mem_interior_iff_mem_nhds.mpr (hnhds x hx)⟩) ?_
      rintro x ⟨hxC, hxI⟩
      rcases interior_subset hxI with hx | hx
      · exact hx
      · exact absurd hxC hx
    rw [heq]
    exact hC.measurableSet.inter isOpen_interior.measurableSet
  -- Egorov on `C`: a closed `A ⊆ C`, `Lⁿ(C \ A) < ε`, with `η_k → 0` uniformly on compact `Q ⊆ A`
  obtain ⟨A, hAC, hA, hCA, hunif⟩ := Submission.codim1_rdo_c1a_egorov_isClosed n C η
    (fun _ => 0) hC.measurableSet hη_meas measurable_const hη_tendsto ε hε
  refine ⟨A, hAC, hA, hCA, fun Q hQ hQA ε' hε' => ?_⟩
  -- `η_k < ε'` on `Q` for some `k`; take `δ = 1/(k + 1)`
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp (hunif Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx y hy hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have h0 : 0 < dist y x := dist_pos.mpr hyx
  have hηx : η k x < ε' := by
    have hkx := hk x hx
    rw [dist_comm, Real.dist_eq, sub_zero] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hR : R x y ≤ ε' :=
    (hR_le_η k x y (hAC (hQA hx)) (hAC hy) h0 (by rwa [dist_comm])).trans hηx.le
  exact (div_le_iff₀ (norm_sub_pos_iff.mpr hyx)).mp hR

/-- **`C¹` approximation** (Simon Ch. 2, Theorem 1.5).  If `f : ℝⁿ → ℝ` is `K`-Lipschitz and
`ε > 0`, there is `g ∈ C¹(ℝⁿ)` with `Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) < ε`.  By Rademacher (1.4) `f` is
differentiable on a Borel set `B` of full measure.  Lusin gives a closed `C ⊆ B` with `Df|C`
continuous and `Lⁿ(B \ C) < ε/2`; the remainder estimate gives a closed `A ⊆ C` with
`Lⁿ(C \ A) < ε/2` on which `f, Df` satisfy Whitney's condition 1.6(∗); Whitney's extension
theorem (1.6) gives `g ∈ C¹` with `g = f` and `Dg = Df` on `A`.  The exceptional set lies in
`Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.codim1_rdo_c1_approximation : ∀ (n : ℕ) (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n f K hf ε hε
  -- Rademacher: `f` is differentiable on the Borel set `B`, whose complement is null
  set B : Set (Euclid n) := {x | DifferentiableAt ℝ f x}
  have hBm : MeasurableSet B := measurableSet_of_differentiableAt ℝ f
  have hBc : volume Bᶜ = 0 := ae_iff.mp hf.ae_differentiableAt
  -- Lusin: a closed `C ⊆ B` with `Df` continuous on `C` and `Lⁿ(B \ C) < ε/2`
  obtain ⟨C, hCB, hC, hDC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed n (fderiv ℝ f) B
    (measurable_fderiv ℝ f) hBm (ε / 2) (ENNReal.half_pos hε.ne')
  -- a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` on which Whitney's condition 1.6(∗) holds
  obtain ⟨A, hAC, hA, hCA, hR⟩ := Submission.codim1_rdo_c1a_whitney_remainder n f K C hf hC
    (fun x hx => hCB hx) hDC (ε / 2) (ENNReal.half_pos hε.ne')
  -- Whitney: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`
  obtain ⟨g, hg, hgf, hDg⟩ := Submission.codim1_rdo_c1a_whitney_extension n A f (fderiv ℝ f) hA
    hf.continuous.continuousOn (hDC.mono hAC) hR
  refine ⟨g, hg, ?_⟩
  -- the exceptional set misses `A`, and `Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume (Bᶜ ∪ (B \ C) ∪ (C \ A)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · rcases hx with hfg | hfg
          · exact absurd (hgf hxA).symm hfg
          · exact absurd (hDg x hxA).fderiv.symm hfg
        by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
    _ ≤ volume (Bᶜ ∪ (B \ C)) + volume (C \ A) := measure_union_le _ _
    _ ≤ volume Bᶜ + volume (B \ C) + volume (C \ A) := by gcongr; exact measure_union_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [hBc, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε

/-- **Simon Ch. 3, Lemma 1.2, "only if"** (chapter-03.txt lines 39–65, in the lemma at lines
25–66), in quantitative form: a countably `n`-rectifiable `M ⊆ ℝᴾ` is covered, up to an
`Hⁿ`-null set, by countably many images `Nₖ = gₖ(B_{rₖ}(cₖ))` of open balls under C¹ maps
`gₖ : ℝⁿ → ℝᴾ` with lower Lipschitz bounds `mₖ|a − b| ≤ |gₖ(a) − gₖ(b)|` on the balls, each `Nₖ`
Borel with `Hⁿ(Nₖ) < ∞`.  By Definition 1.1, `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ`
Lipschitz.  The C¹ approximation theorem (Simon Ch. 2, 1.5) covers `Fⱼ(ℝⁿ)` by C¹ images
`Gⱼᵢ(ℝⁿ)` up to a null set, and `Gⱼᵢ(ℝⁿ)` is covered, up to its null critical image, by images of
balls carrying lower Lipschitz bounds.  The triples `(j, i, q)` are enumerated by applying
`Nat.unpair` twice. -/
theorem Submission.codim1_rdo_rectifiable_c1_cover : ∀ (P n : ℕ) (M : Set (Euclid P)), CountablyRectifiable n M → ∃ (g : ℕ → Euclid n → Euclid P) (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (g k)) ∧ (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖g k a - g k b‖) ∧ (∀ k, MeasurableSet (g k '' ball (c k) (r k))) ∧ (∀ k, μHE[n] (g k '' ball (c k) (r k)) ≠ ∞) ∧ μHE[n] (M \ ⋃ k, g k '' ball (c k) (r k)) = 0 := by
  intro P n M hM
  -- Step 1 (Definition 1.1): `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ` `Kⱼ`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  -- Steps 2–3: C¹ maps `Gⱼᵢ` with `Hⁿ(Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) = 0`, by the C¹ approximation theorem.
  choose G hG hFG using fun j => Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover P n
    (Submission.codim1_rdo_c1_approximation n) (F j) (K j) (hK j)
  -- Steps 4–6: balls `B_{rⱼᵢq}(cⱼᵢq)` on which `Gⱼᵢ` has lower Lipschitz constant `mⱼᵢq > 0`,
  -- whose images cover `Gⱼᵢ(ℝⁿ)` up to an `Hⁿ`-null set.
  choose c r m hm hlow hGB using fun j i => Submission.codim1_rdo_c1cov_regular_ball_cover P n
    (G j i) (hG j i)
  -- Step 7: `k ↦ (J k, I k, Q k)` maps `ℕ` onto `ℕ³` (`Nat.unpair` applied twice).
  obtain ⟨J, I, Q, hJIQ⟩ : ∃ J I Q : ℕ → ℕ, ∀ j i q, ∃ k, J k = j ∧ I k = i ∧ Q k = q :=
    ⟨fun k => k.unpair.1, fun k => k.unpair.2.unpair.1, fun k => k.unpair.2.unpair.2,
      fun j i q => ⟨Nat.pair j (Nat.pair i q), by simp⟩⟩
  -- Step 8: the pieces `Nₖ` are Borel with finite `Hⁿ`-measure.
  have hN k := Submission.codim1_rdo_c1cov_image_ball_borel_finite P n (G (J k) (I k))
    (c (J k) (I k) (Q k)) (r (J k) (I k) (Q k)) (hG (J k) (I k))
  refine ⟨fun k => G (J k) (I k), fun k => c (J k) (I k) (Q k), fun k => r (J k) (I k) (Q k),
    fun k => m (J k) (I k) (Q k), fun k => hG _ _, fun k => hm _ _ _, fun k => hlow _ _ _,
    fun k => (hN k).1, fun k => (hN k).2, ?_⟩
  -- Step 9: `M ∖ ⋃ₖ Nₖ` lies in the countable union of `Hⁿ`-null sets
  -- `M₀ ∪ ⋃ⱼ (Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) ∪ ⋃ⱼ ⋃ᵢ (Gⱼᵢ(ℝⁿ) ∖ ⋃_q Gⱼᵢ(B_{rⱼᵢq}(cⱼᵢq)))`.
  refine measure_mono_null ?_ (measure_union_null hM₀ (measure_union_null (measure_iUnion_null hFG)
    (measure_iUnion_null fun j => measure_iUnion_null (hGB j))))
  rintro y ⟨hyM, hyN⟩
  rcases hcover hyM with hy₀ | hyF
  · exact Or.inl hy₀
  obtain ⟨j, hyj⟩ := mem_iUnion.1 hyF
  by_cases hyG : y ∈ ⋃ i, range (G j i)
  · obtain ⟨i, hyi⟩ := mem_iUnion.1 hyG
    by_cases hyB : y ∈ ⋃ q, G j i '' ball (c j i q) (r j i q)
    · obtain ⟨q, hyq⟩ := mem_iUnion.1 hyB
      obtain ⟨k, rfl, rfl, rfl⟩ := hJIQ j i q
      exact absurd (mem_iUnion.2 ⟨k, hyq⟩) hyN
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨i, hyi, hyB⟩⟩))
  · exact Or.inr (Or.inl (mem_iUnion.2 ⟨j, hyj, hyG⟩))
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in an open set**
(Simon Ch. 1, 3.6 and Remark 3.7(2); chapter-01.txt lines 700–711).  If `U ⊆ ℝᴾ` is open and
`S ⊆ ℝᴾ` is Borel with `Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e.
`x ∈ U \ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B(y, r_y)` with
`B̄(y, r_y) ⊆ U` cover `U` (Lindelöf); the upper density theorem applies to each piece
`S ∩ B(y, r_y)`, of finite measure, and the piece agrees with `S` on small balls about
`x ∈ B(y, r_y)`. -/
theorem Submission.doraggt_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U` (Lindelöf).
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hrad
  obtain ⟨D, hDU, hDc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hr0 y hy)))
  -- Steps 2 and 3, the upper density theorem for each finite-measure piece `S ∩ B(y, r y)`,
  -- simultaneously for the countably many `y ∈ D`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] ((S ∩ ball y (r y)) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    refine Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball) ?_
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
  -- Step 4, near `x ∈ B(y, r y)` the piece and `S` agree.
  filter_upwards [hae] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcover hxU)
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεball)]
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]
/-- Changing a set by parts of vanishing `n`-density at `x` does not change its approximate
tangent spaces at `x` (Simon Ch. 3, Definition 1.4 and Remark 1.5(2); proof of 3.1.6).  For
`f ∈ C_c(ℝᴾ)` with `|f| ≤ C`, `f = 0` off `B̄_R(0)` and `0 < r < r₀/R`, comparing both blow-up
integrals with the one over `η_{x,r}(A ∩ B)` gives `|∫_{η_{x,r}(A)} f dHⁿ − ∫_{η_{x,r}(B)} f dHⁿ| ≤
C Hⁿ(η_{x,r}(A \ B) ∩ B̄_R(0)) + C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`, and
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`. -/
theorem Submission.doraggt_approxTangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → 0 < r₀ → μHE[n] (A ∩ closedBall x r₀) ≠ ∞ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((A \ B) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n A B x r₀ hA hB hr₀ hAfin hBfin hAB hBA
  -- Step 1: it suffices that `∫_{η_r(A)} f − ∫_{η_r(B)} f → 0` for every `f ∈ C_c`
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n A B x fun f => ?_
  -- Step 2: `|f| ≤ C`, and `f = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hzero⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
      f.hasCompactSupport.isCompact.isBounded
    exact ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))⟩
  -- Step 3: for `0 < r < r₀ / R`, `Hⁿ(η_r(S) ∩ B̄_R(0)) ≤ r⁻ⁿ Hⁿ(S ∩ B̄_{r₀}(x)) < ∞`
  have hfin : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall x r₀) ≠ ∞ → ∀ r ∈ Ioo 0 (r₀ / R),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) ≠ ∞ := by
    intro S hS r hr
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr.1).ne'))
      (ne_top_of_le_ne_top hS (measure_mono (inter_subset_inter_right _
        (closedBall_subset_closedBall ((lt_div_iff₀ hR).mp hr.2).le))))
  -- Step 4: `C Hⁿ(η_r(S) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`
  have herr : ∀ S : Set (Euclid P),
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => C *
        (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
        (𝓝[>] 0) (𝓝 0) := by
    intro S hS
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ => μHE[n] (S ∩ closedBall x ρ)) R hR hS)).const_mul C
    rw [ENNReal.toReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Function.comp_apply, Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr]
  -- Step 5: for `0 < r < r₀ / R`, compare both integrals with the one over `η_r(A ∩ B)`
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]‖ ≤
        C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A \ B) ∩
            closedBall 0 R)).toReal +
          C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩
            closedBall 0 R)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
    have hA' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) A x r R C f
      f.continuous (hA.inter hB) hA inter_subset_left hr.1 (hfin A hAfin r hr) hC hzero
    have hB' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) B x r R C f
      f.continuous (hA.inter hB) hB inter_subset_right hr.1 (hfin B hBfin r hr) hC hzero
    rw [Set.sdiff_self_inter] at hA'
    rw [Set.sdiff_inter_self_eq_sdiff] at hB'
    rw [← sub_sub_sub_cancel_right _ _
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ B), f y ∂μHE[n])]
    exact (norm_sub_le _ _).trans (add_le_add hA' hB')
  -- Step 6: squeeze
  have hlim := (herr _ hAB).add (herr _ hBA)
  rw [add_zero] at hlim
  exact squeeze_zero_norm' hle hlim

/-- **Approximate tangent planes of two locally finite sets agree a.e. on their overlap** (Simon
Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and 113–146,
stated symmetrically for two sets).  Let `W ⊆ ℝᴾ` be open and `A`, `B` Borel with `Hⁿ(A ∩ K)` and
`Hⁿ(B ∩ K)` finite for every compact `K ⊆ W`.  By the upper density theorem the densities of
`A ∖ B` and `B ∖ A` vanish at `Hⁿ`-a.e. `x ∈ W ∩ A ∩ B`; a closed ball about such `x` inside `W`
has finite measure in `A` and in `B`, so `A` and `B` have the same approximate tangent planes at
`x`. -/
theorem Submission.doraggt_ae_approxTangent_transfer : ∀ (P n : ℕ) (W A B : Set (Euclid P)), IsOpen W → MeasurableSet A → MeasurableSet B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (A ∩ K) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ W → x ∈ A → x ∈ B → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n W A B hW hA hB hAfin hBfin
  -- Step 1, the densities of `A ∖ B` and `B ∖ A` vanish `Hⁿ`-a.e. on `W` off these sets.
  have hAB := Submission.doraggt_local_density_zero P n W (A \ B) hW (hA.diff hB)
    fun K hK hKW => ne_top_of_le_ne_top (hAfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  have hBA := Submission.doraggt_local_density_zero P n W (B \ A) hW (hB.diff hA)
    fun K hK hKW => ne_top_of_le_ne_top (hBfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2, at such `x ∈ W ∩ A ∩ B`, `x ∉ A ∖ B` and `x ∉ B ∖ A`, so both densities vanish.
  filter_upwards [hAB, hBA] with x hxAB hxBA hxW hxA hxB
  -- Step 3, `B̄(x, ε/2) ⊆ B(x, ε) ⊆ W` is compact, so `A` and `B` have finite measure in it.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hsub : closedBall x (ε / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4, the approximate tangent planes of `A` and `B` at `x` agree.
  exact Submission.doraggt_approxTangent_iff_of_density_zero P n A B x (ε / 2) hA hB
    (half_pos hε) (hAfin _ (isCompact_closedBall x (ε / 2)) hsub)
    (hBfin _ (isCompact_closedBall x (ε / 2)) hsub) (hxAB hxW fun h => h.2 hxB)
    (hxBA hxW fun h => h.2 hxA)

/-- **A countably `n`-rectifiable set has approximate tangent planes `Hⁿ`-a.e.** (Simon Ch. 3,
Theorem 1.6 "⇒", chapter-03.txt lines 109–143, with Lemma 1.2 and Remark 1.3, lines 25–76).  Let
`M ⊆ ℝᴾ` be Borel and countably `n`-rectifiable with `Hⁿ(M ∩ K) < ∞` for every compact `K`.  Up to
an `Hⁿ`-null set, `M` is covered by Borel pieces `N_k = g_k(B_{r_k}(c_k))` of finite measure, with
`g_k` of class `C¹` and `m_k|a − b| ≤ |g_k(a) − g_k(b)|` on the ball (Lemma 1.2).  `N_k` has the
approximate tangent plane `Dg_k(z)(ℝⁿ)` at each `g_k(z)`, and by the upper density theorem `M` and
`N_k` have the same approximate tangent planes at `Hⁿ`-a.e. point of `M ∩ N_k`.  The countably many
exceptional null sets combine, so `T_w M` exists for `Hⁿ`-a.e. `w ∈ M`.  The pieces need not be
disjoint (Remark 1.3). -/
theorem Submission.codim1_rdo_rectifiable_ae_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ᵐ w ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M w Q := by
  intro P n M hM hrect hloc
  -- Step 1, `M` is covered up to an `Hⁿ`-null set by the `C¹` pieces `N_k = g_k(B_{r_k}(c_k))`.
  obtain ⟨g, c, r, m, hg, hm, hlow, hmeas, hfin, hnull⟩ :=
    Submission.codim1_rdo_rectifiable_c1_cover P n M hrect
  -- Step 2, `M` and `N_k` have the same approximate tangent planes `Hⁿ`-a.e. on `M ∩ N_k`.
  have hpiece : ∀ k, ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∈ (univ : Set (Euclid P)) → w ∈ M →
      w ∈ g k '' ball (c k) (r k) → ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M w Q ↔
          HasApproximateTangentSpaceAt n (g k '' ball (c k) (r k)) w Q :=
    fun k => Submission.doraggt_ae_approxTangent_transfer P n univ M (g k '' ball (c k) (r k))
      isOpen_univ hM (hmeas k) (fun K hK _ => hloc K hK)
      (fun K _ _ => ne_top_of_le_ne_top (hfin k) (measure_mono inter_subset_left))
  -- Step 3, the exceptional sets of Steps 1 and 2 form countably many `Hⁿ`-null sets.
  have hall := ae_all_iff.2 hpiece
  have hcov : ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∉ M \ ⋃ k, g k '' ball (c k) (r k) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  -- Step 4, off them, `w = g_k(z) ∈ M ∩ N_k` for some `k`, and `T_w M = T_w N_k = Dg_k(z)(ℝⁿ)`.
  rw [ae_restrict_iff' hM]
  filter_upwards [hall, hcov] with w hw hw' hwM
  have hU : w ∈ ⋃ k, g k '' ball (c k) (r k) := by
    by_contra h
    exact hw' ⟨hwM, h⟩
  obtain ⟨k, z, hz, rfl⟩ := mem_iUnion.1 hU
  exact ⟨_, (hw k (mem_univ _) hwM ⟨z, hz, rfl⟩ _).2
    (Submission.codim1_rdo_c1_piece_approxTangent P n (g k) (c k) (r k) (m k) (hg k) (hm k)
      (hlow k) z hz)⟩
/-- An approximate tangent plane forces unit `Hⁿ`-density on closed balls (Simon Ch. 3,
Remark 1.5(3), with Definition 1.4).  If `Hⁿ(M ∩ B̄_s(x)) < ∞` and `Q` is an approximate tangent
space of `M` at `x`, then `Hⁿ(M ∩ B̄_ρ(x)) / (ωₙρⁿ) → 1` as `ρ ↓ 0`.  Since
`Hⁿ(η_{x,r}(M) ∩ B̄_1(0)) = r⁻ⁿHⁿ(M ∩ B̄_r(x))` and `Hⁿ(Q ∩ B̄_t(0)) = ωₙtⁿ`, the radial cut-offs
`g_{1-ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}` in `C_c` squeeze `r⁻ⁿHⁿ(M ∩ B̄_r(x))` between blow-up integrals
whose limits lie within `ωₙ(1 ∓ ε)ⁿ`. -/
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
        (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
      rw [image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b →
      ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
        (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: back to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
/-- **Simon Ch. 1, 3.1–3.2** (densities may be computed with closed or open balls; cf. 6.2.8 and
`HasMassDensity`): if `ν(B̄_ρ(x)) / (ωₙρⁿ) → θ ∈ [0, ∞]` as `ρ ↓ 0`, then also
`ν(B_ρ(x)) / (ωₙρⁿ) → θ`.  The upper bound follows from `B_ρ(x) ⊆ B̄_ρ(x)`.  For the lower
bound, given `a < θ` pick `t ∈ (0, 1)` with `a < tⁿθ`; then `B̄_{tρ}(x) ⊆ B_ρ(x)` and
`ωₙ(tρ)ⁿ = tⁿ ωₙρⁿ` give `ν(B_ρ(x)) / (ωₙρⁿ) ≥ tⁿ · ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) > a` for small
`ρ`. -/
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
      exact hta
    -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
    filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall
/-- **Step 1 of Corollary 7.5.11** (`k ≥ 1`, Simon 7.5; Ch. 2, §4, (4.1)).  A nonempty embedded
`d`-dimensional `Cʳ` submanifold `M` of `ℝᴾ` has `d ≤ P`: for `y ∈ M` and a chart `ψ : V → W` at
`y`, `y ∈ W ∩ M = ψ(V)` gives `z ∈ V`, and the injective linear map `Dψ(z) : ℝᵈ → ℝᴾ` gives
`d = dim ℝᵈ ≤ dim ℝᴾ = P`. -/
theorem Submission.regcomp_cop_dim_le_of_embedded : ∀ (P d r : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → M.Nonempty → d ≤ P := by
  intro P d r M hM ⟨y, hy⟩
  -- a chart `ψ : V → W` of `M` at `y`
  obtain ⟨V, W, ψ, -, -, hyW, -, -, hψV, -, hDψ⟩ := hM y hy
  -- `y ∈ W ∩ M = ψ(V)`, so `y = ψ(z)` for some `z ∈ V`
  obtain ⟨z, hz, -⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  -- `Dψ(z) : ℝᵈ → ℝᴾ` is injective, so `d = dim ℝᵈ ≤ dim ℝᴾ = P`
  simpa using LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℝ ψ z : Euclid d →ₗ[ℝ] Euclid P)) (hDψ z hz)
/-- **Simon 7.5** (`T = ∂[[E]]` with `E ⊆ N`): if `(N̄ \ N) ∩ U = ∅`, `E ⊆ N` and
`T(ω) = ∫_E ⟨dω, ξN⟩ dH^{n+1}` for `ω ∈ 𝒟ⁿ(U)`, then `spt T ⊆ N`.  A point `x ∈ spt T \ N` lies
outside `N̄`, so `B_ε(x) ⊆ U \ N̄` for some `ε > 0`.  `W = B_{ε/2}(x)` is open with `W̄` compact
in `U`, and every `ω` with `spt ω ⊆ W` has `spt dω ⊆ spt ω` disjoint from `E`.  So the integrand
vanishes on `E`, `T(ω) = 0`, and `x ∈ W` lies in the zero region of `T`. -/
theorem Submission.regcomp_cop_region_support_subset : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsOpen U → (closure N \ N) ∩ U = ∅ → E ⊆ N → IsBoundaryOfRegion T E ξN → T.support ⊆ N := by
  intro P n U N E ξN T hU hN hEN hT x hx
  obtain ⟨hxU, hxZ⟩ := hx
  by_contra hxN
  -- `x ∉ N̄`, since `(N̄ \ N) ∩ U = ∅`
  have hxN' : x ∉ closure N := fun h => hN.subset ⟨⟨h, hxN⟩, hxU⟩
  -- a ball `B_ε(x) ⊆ U \ N̄`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff isClosed_closure) x ⟨hxU, hxN'⟩
  -- `W = B_{ε/2}(x)` is open, and `W̄ ⊆ B̄_{ε/2}(x)` is compact and contained in `B_ε(x) ⊆ U`
  have hcl : closure (ball x (ε / 2)) ⊆ ball x ε :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  refine hxZ ⟨ball x (ε / 2), ⟨isOpen_ball,
    (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, hcl.trans (hball.trans sdiff_subset), ?_⟩,
    mem_ball_self (half_pos hε)⟩
  -- `T` vanishes on `W`: for `spt ω ⊆ W`, `dω = 0` on `E ⊆ N`, so the integrand vanishes on `E`
  intro ω hω
  rw [hT ω]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  have hzω : z ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) := fun h =>
    (hball (ball_subset_ball (by linarith) (hω (tsupport_exteriorDerivative_subset _ h)))).2
      (subset_closure (hEN hz))
  rw [image_eq_zero_of_notMem_tsupport hzω, map_zero]
/-- **`∂[[E]]` is a cycle**: Simon 7.5.1 (`T = ∂[[E]]`, chapter-07.txt line 752) with (6.1.12)
`d²ω = 0` (chapter-06.txt line 150) and the boundary (6.2.3) `∂T(ω) = T(dω)`, `∂T = 0` if `n = 0`
(chapter-06.txt lines 216–220).  If `T(ω) = ∫_E ⟨dω, ξ_N⟩ dH^{n+1}` for every `ω ∈ 𝒟ⁿ(U)`, then
`∂T = 0` in `U`: for `n = m + 1` and `φ ∈ 𝒟ᵐ(U)`, `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξ_N⟩ dH^{m+2} = 0`,
since `d(dφ) = 0` for the smooth form `φ`.  No hypothesis on `U`, `E` or `ξ_N` is needed. -/
theorem Submission.regcomp_cop_region_boundary_vanishes : ∀ (P n : ℕ) (U E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsBoundaryOfRegion T E ξN → BoundaryVanishes T := by
  intro P n
  cases n with
  | zero =>
    -- Degree `0`: `BoundaryVanishes T` is `True` (Simon's convention `∂T = 0`, 6.2.3).
    intro U E ξN T _
    trivial
  | succ m =>
    -- Degree `m + 1`: show `∂T = 0` by testing on every `φ ∈ 𝒟ᵐ(U)`.
    intro U E ξN T hT
    show T.boundary = 0
    apply GeometricCurrentOn.ext
    intro φ
    -- `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξ_N⟩ dH^{m+2}`: (6.2.3) and the hypothesis at `dφ ∈ 𝒟^{m+1}(U)`.
    rw [GeometricCurrentOn.boundary_apply, hT (exteriorDerivativeTestOn U m φ),
      GeometricCurrentOn.zero_apply]
    -- `d(dφ) = 0` for the smooth form `φ` (6.1.12), so the integrand is `ξ_N(x)(0) = 0`.
    have hdd : exteriorDerivative ((exteriorDerivativeTestOn U m φ : TestFormOn U (m + 1)) :
        DifferentialForm (Euclid P) (m + 1)) = 0 :=
      exteriorDerivative_sq φ.property.1.1
    simp only [hdd, Pi.zero_apply, map_zero, integral_zero]

/-- **Simon 7.5.1** (`T = ∂[[E]]` in `U`, `N ∈ 𝒪`, `E ⊆ N ∩ U`; Ch. 6, 2.3 and 2.11; Ch. 2, §4).
If `U` is open, `N ∈ 𝒪` is oriented by `ξN`, `E ⊆ N ∩ U` and `T(ω) = ∫_E ⟨dω, ξN⟩ dH^{n+1}` for
`ω ∈ 𝒟ⁿ(U)`, then `n + 1 ≤ P`, `spt T ⊆ U ∩ N` and `∂T = 0` in `U`.  A chart of `N` at a point
of `N ∩ U ≠ ∅` has injective derivative `ℝ^{n+1} → ℝᴾ`, so `n + 1 ≤ P`; `spt T ⊆ U` by
definition and `spt T ⊆ N` because `(N̄ \ N) ∩ U = ∅` and `E ⊆ N`; and
`∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξN⟩ dH^{n+1} = 0`.  Minimality of `T` is not needed. -/
theorem Submission.codim1_region_support_cycle : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsOpen U → InClassO n U N ξN → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → n + 1 ≤ P ∧ T.support ⊆ U ∩ N ∧ BoundaryVanishes T := by
  intro P n U N E ξN T hU hO hE hT
  obtain ⟨hN, -, hNU, hne⟩ := hO
  refine ⟨?_, fun x hx => ⟨T.support_subset_domain hx, ?_⟩, ?_⟩
  · -- `n + 1 ≤ P`: `N` is a nonempty embedded `(n + 1)`-dimensional submanifold of `ℝᴾ`
    exact Submission.regcomp_cop_dim_le_of_embedded P (n + 1) 2 N hN (hne.mono inter_subset_left)
  · -- `spt T ⊆ N`, since `(N̄ \ N) ∩ U = ∅` and `E ⊆ N`
    exact Submission.regcomp_cop_region_support_subset P n U N E ξN T hU hNU
      (hE.trans inter_subset_left) hT hx
  · -- `∂T = 0`: `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξN⟩ dH^{n+1} = 0`
    exact Submission.regcomp_cop_region_boundary_vanishes P n U E ξN T hT
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

/-- **Simon Ch. 6, 2.5 and 3.2(3)**, upper bound: if `T(ω) = ∫_{M'} θ' ⟨ω, ξ'⟩ dHᵏ` for every
`ω` supported in `V`, with `θ' ≥ 0` and `ξ'` a unit orientation `Hᵏ`-a.e. on `M'`, then
`M_W(T) ≤ ∫_{M' ∩ W} θ' dHᵏ` for measurable `W ⊆ V`.  For admissible `ω`, `|ξ'(ω)| ≤ |ω| ≤ 1`
a.e. on `M'` and `ω = 0` off `W`, so `T(ω) ≤ |∫_{M'} θ' ξ'(ω)| ≤ ∫⁻_{M'} 1_W θ'`; no
integrability or measurability of `θ'`, `ξ'` is needed. -/
theorem Submission.codim1_oriented_rep_massOn_le_lintegral : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), (∀ x, 0 ≤ θ' x) → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), MeasurableSet W → W ⊆ V → T.massOn W ≤ ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
  intro P k U V M' T θ' ξ' hθ hξ hT W hW hWV
  obtain ⟨_, hL⟩ := Submission.dor_ims_unitOrientation_dual P k
  -- `|ξ'(x)(α)| ≤ |α|` for `Hᵏ⌞M'`-a.e. `x`
  have hgood : ∀ᵐ x ∂(μHE[k].restrict M'),
      ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α := by
    filter_upwards [hξ] with x ⟨Q, hQ⟩
    exact (hL (ξ' x) Q hQ).1
  -- it suffices to bound `T(ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  dsimp only
  rw [hT ω (hωW.trans hWV)]
  -- `|θ' ξ'(ω)| ≤ 1_W θ'` a.e. on `M'`: `ω = 0` off `W` and `|ξ'(ω)| ≤ |ω| ≤ 1`
  have hdom : ∀ᵐ x ∂(μHE[k].restrict M'),
      ‖θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ≤
        W.indicator (fun x => ENNReal.ofReal (θ' x)) x := by
    filter_upwards [hgood] with x hx
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hθ x)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc θ' x * |ξ' x ((ω : DifferentialForm (Euclid P) k) x)|
          ≤ θ' x * 1 := mul_le_mul_of_nonneg_left ((hx _).trans (hω1 x)) (hθ x)
        _ = θ' x := mul_one _
    · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h), map_zero, mul_zero,
        enorm_zero]
      exact zero_le
  -- `T(ω) ≤ |∫ g| ≤ ∫⁻ |g| ≤ ∫⁻_{M'} 1_W θ' = ∫⁻_{M' ∩ W} θ'`
  calc ENNReal.ofReal (∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k])
      ≤ ‖∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in M', ‖θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂μHE[k] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in M', W.indicator (fun x => ENNReal.ofReal (θ' x)) x ∂μHE[k] :=
        lintegral_mono_ae hdom
    _ = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
        rw [lintegral_indicator hW, Measure.restrict_restrict hW, inter_comm]
/-- **Lower mass bound for an oriented representation** (Simon Ch. 6, 2.5 and 3.2(3)).  If
`T(ω) = ∫_{M'} θ' ⟨ω, ξ'⟩ dHᵏ` for the test forms supported in `V`, with `θ' ≥ 0` measurable and
`ξ'` a.e. a unit orientation, then `I = ∫_{M' ∩ W} θ' dHᵏ ≤ M_W(T)` for every open `W ⊆ V` with
`I < ∞`.  Let `ν = θ' Hᵏ⌞M'` and let `L` be the dual map of `dor_ims_unitOrientation_dual`, so
`ν`-a.e. `|ξ'(α)| ≤ |α|`, `|L(ξ')| ≤ 1` and `ξ'(L(ξ')) = 1`.  Lusin gives a compact `K ⊆ W` of such
points with `ν(W \ K) < η` on which `L ∘ ξ'` is continuous, and the smooth unit approximation an
admissible `ω` with `|ω − L ∘ ξ'| ≤ δ = η/(I + 1)` on `K`.  Then `ξ'(ω) ≥ (1 − δ) 1_K − 1_{W \ K}`
`ν`-a.e., so `T(ω) = ∫ ξ'(ω) dν ≥ (1 − δ) ν(K) − ν(W \ K) > I − 3η`. -/
theorem Submission.codim1_oriented_rep_lintegral_le_massOn : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), V ⊆ U → Measurable θ' → (∀ x, 0 ≤ θ' x) → AEStronglyMeasurable ξ' (μHE[k].restrict M') → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≠ ∞ → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≤ T.massOn W := by
  intro P k U V M' T θ' ξ' hVU hθm hθ0 hξm hξo hT W hW hWV hI
  -- Step 1: the dual map `L` of the unit orientations
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P k
  -- Step 2: `ν = θ' Hᵏ⌞M'`, with `ν ≪ Hᵏ⌞M'`, `ν(W) = I < ∞` and `∫ g dν = ∫_{M'} θ' g dHᵏ`
  set ν : Measure (Euclid P) :=
    (μHE[k].restrict M').withDensity fun x => ENNReal.ofReal (θ' x) with hν
  have hνμ : ν ≪ μHE[k].restrict M' := withDensity_absolutelyContinuous _ _
  have hνW : ν W = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
    rw [hν, withDensity_apply _ hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
      inter_comm]
  have hνW' : ν W ≠ ∞ := hνW ▸ hI
  -- `ν`-a.e. `x` is good, and the bad points lie in a measurable `ν`-null set `Z`
  have hgood : ∀ᵐ x ∂ν, (∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) ∧
      covectorEuclideanNorm (L (ξ' x)) ≤ 1 ∧ ξ' x (L (ξ' x)) = 1 :=
    hνμ.ae_le (hξo.mono fun x ⟨Q, hQ⟩ => hL (ξ' x) Q hQ)
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hξν : AEStronglyMeasurable ξ' ν := hξm.mono_ac hνμ
  have hdens : ∀ g : Euclid P → ℝ, ∫ x, g x ∂ν = ∫ x in M', θ' x * g x ∂μHE[k] := by
    intro g
    rw [hν, integral_withDensity_eq_integral_toReal_smul hθm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hθ0 x), smul_eq_mul]
  set m : ℝ := ν.real W
  have hm0 : 0 ≤ m := measureReal_nonneg
  -- Steps 4–8: for every `η > 0` some admissible `ω` has `T(ω) > m - 3η`
  have key : ∀ η : ℝ, 0 < η →
      ∃ ω : TestFormOn U k, ω ∈ massAdmissibleOn U k W ∧ m - 3 * η < T ω := by
    intro η hη
    -- Step 4: Lusin on `W \ Z` gives a compact `K` of good points with `ν(W \ K) < η`
    obtain ⟨K, hKc, hKA, hKν, hLK⟩ := Submission.dor_ims_lusin_continuousOn P k ν (W \ Z)
      (fun x => L (ξ' x)) η (hW.measurableSet.diff hZm)
      (measure_ne_top_of_subset sdiff_subset hνW')
      (L.continuous.comp_aestronglyMeasurable hξν) hη
    have hKW : K ⊆ W := hKA.trans sdiff_subset
    have hKm : MeasurableSet K := hKc.measurableSet
    have hLK1 : ∀ x ∈ K, covectorEuclideanNorm (L (ξ' x)) ≤ 1 := by
      intro x hx
      by_contra h
      exact (hKA hx).2 (hZ fun hg => h hg.2.1)
    have hWK : ν.real (W \ K) < η := by
      refine ENNReal.toReal_lt_of_lt_ofReal ?_
      rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
    -- Step 5: an admissible `ω` with `|ω - L ∘ ξ'| ≤ δ` on `K`
    set δ : ℝ := η / (m + 1) with hδ
    have hδ0 : 0 < δ := div_pos hη (by linarith)
    obtain ⟨ω₀, hω₀, hω₀W, hω₀1, hω₀K⟩ := Submission.dor_ims_smooth_unit_approx P k K W
      (fun x => L (ξ' x)) δ hKc hW hKW hLK hLK1 hδ0
    let ω : TestFormOn U k := ⟨ω₀, hω₀, hω₀W.trans (hWV.trans hVU)⟩
    refine ⟨ω, ⟨hω₀W, hω₀1⟩, ?_⟩
    have hω₀0 : ∀ x, x ∉ W → ω₀ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W h)
    -- Step 6: `f = ξ'(ω₀)` is `ν`-integrable, as `|f| ≤ 1_W`, and `T(ω) = ∫ f dν`
    have hTω : T ω = ∫ x, ξ' x (ω₀ x) ∂ν := by
      rw [hdens]
      exact hT ω (hω₀W.trans hWV)
    have hfm : AEStronglyMeasurable (fun x => ξ' x (ω₀ x)) ν :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hξν.prodMk (ContDiff.continuous hω₀.1).aestronglyMeasurable)
    have hWi : Integrable (W.indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff hW.measurableSet).mpr (integrableOn_const hνW')
    have hfi : Integrable (fun x => ξ' x (ω₀ x)) ν := by
      refine hWi.mono' hfm (hgood.mono fun x hx => ?_)
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW, Pi.one_apply, Real.norm_eq_abs]
        exact (hx.1 _).trans (hω₀1 x)
      · rw [indicator_of_notMem hxW, hω₀0 x hxW, map_zero, norm_zero]
    -- Step 7: `f ≥ (1 - δ) 1_K - 1_{W \ K}` `ν`-a.e.
    have hKi : Integrable (K.indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff hKm).mpr (integrableOn_const (measure_ne_top_of_subset hKW hνW'))
    have hWKi : Integrable ((W \ K).indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff (hW.measurableSet.diff hKm)).mpr
        (integrableOn_const (measure_ne_top_of_subset sdiff_subset hνW'))
    have hlow : ∀ᵐ x ∂ν,
        (1 - δ) * K.indicator 1 x - (W \ K).indicator 1 x ≤ ξ' x (ω₀ x) := by
      refine hgood.mono fun x hx => ?_
      by_cases hxK : x ∈ K
      · -- `f = 1 + ξ'(ω₀ - L(ξ')) ≥ 1 - |ω₀ - L(ξ')| ≥ 1 - δ`
        rw [indicator_of_mem hxK, indicator_of_notMem fun h => h.2 hxK, Pi.one_apply, mul_one,
          sub_zero]
        have h1 : ξ' x (ω₀ x) = 1 + ξ' x (ω₀ x - L (ξ' x)) := by
          rw [map_sub, hx.2.2]
          ring
        have h2 := (hx.1 (ω₀ x - L (ξ' x))).trans (hω₀K x hxK)
        rw [h1]
        linarith [neg_abs_le (ξ' x (ω₀ x - L (ξ' x)))]
      · rw [indicator_of_notMem hxK, mul_zero, zero_sub]
        by_cases hxW : x ∈ W
        · -- `f ≥ -|ω₀| ≥ -1`
          rw [indicator_of_mem (s := W \ K) ⟨hxW, hxK⟩, Pi.one_apply]
          linarith [neg_abs_le (ξ' x (ω₀ x)), (hx.1 (ω₀ x)).trans (hω₀1 x)]
        · -- `ω₀ = 0` off `W`
          rw [indicator_of_notMem fun h => hxW h.1, hω₀0 x hxW, map_zero, neg_zero]
    -- Step 8: `T(ω) ≥ (1 - δ) ν(K) - ν(W \ K) > m - 3η`, as `δ ν(K) ≤ δ m < η`,
    -- `ν(W \ K) < η` and `ν(K) = m - ν(W \ K)`
    have hge : (1 - δ) * ν.real K - ν.real (W \ K) ≤ T ω := by
      rw [hTω, ← integral_indicator_one hKm, ← integral_indicator_one (hW.measurableSet.diff hKm),
        ← integral_const_mul, ← integral_sub (hKi.const_mul _) hWKi]
      exact integral_mono_ae ((hKi.const_mul _).sub hWKi) hfi hlow
    have hsplit : ν.real (W \ K) = m - ν.real K := measureReal_sdiff hKW hKm hνW'
    have hKle : ν.real K ≤ m := measureReal_mono hKW hνW'
    have hδm : δ * m < η := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have hδK : δ * ν.real K ≤ δ * m := mul_le_mul_of_nonneg_left hKle hδ0.le
    have hexp : (1 - δ) * ν.real K = ν.real K - δ * ν.real K := by ring
    linarith
  -- Steps 3 and 9: every `r < I` is at most `M_W(T)`, via `key` for `η = (m - r)/3`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [← hνW] at hr
  have hrm : (r : ℝ) < m := ENNReal.toReal_strict_mono hνW' hr
  obtain ⟨ω, hω, hTω⟩ := key ((m - r) / 3) (by linarith)
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ T.massOn W := T.le_massOn hω

/-- **Mass of a current given on `V` by an oriented weighted set** (Simon Ch. 6, 2.5 and 3.2(3):
`M_W(T) = ∫_{M ∩ W} θ dHᵏ` for `T = τ(M, θ, ξ)`, with a general weight `θ' ≥ 0`).  Let
`I(W) = ∫⁻_{M' ∩ W} θ' dHᵏ` for an open `W ⊆ V`.  Step 2: `|θ' ξ'(ω)| ≤ θ' 1_W` a.e. on `M'` for
every admissible `ω`, so `M_W(T) ≤ I(W)`.  Step 3: if `I(W) < ∞`, a smooth admissible form close
to `L ∘ ξ'` on a compact `K ⊆ M' ∩ W` of almost full `θ' Hᵏ`-measure gives `I(W) ≤ M_W(T)`, and
equality follows by antisymmetry. -/
theorem Submission.codim1_massOn_eq_lintegral_of_oriented_rep : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), IsOpen V → V ⊆ U → MeasurableSet M' → M' ⊆ V → Measurable θ' → (∀ x, 0 ≤ θ' x) → AEStronglyMeasurable ξ' (μHE[k].restrict M') → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → T.massOn W ≤ ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ∧ (∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≠ ∞ → T.massOn W = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k]) := by
  intro P k U V M' T θ' ξ' _hV hVU _hM' _hM'V hθ hθ0 hξ hξQ hT W hW hWV
  -- Step 2: `M_W(T) ≤ I(W)`; the open set `W` is Borel
  have hle := Submission.codim1_oriented_rep_massOn_le_lintegral P k U V M' T θ' ξ' hθ0 hξQ hT W
    hW.measurableSet hWV
  -- Step 3: `I(W) ≤ M_W(T)` when `I(W) < ∞`, hence `M_W(T) = I(W)`
  exact ⟨hle, fun hI => le_antisymm hle
    (Submission.codim1_oriented_rep_lintegral_le_massOn P k U V M' T θ' ξ' hVU hθ hθ0 hξ hξQ hT W hW
      hWV hI)⟩
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]

/-- **Countably `n`-rectifiable sets of finite measure have density one a.e.** (general fact
(G7); Simon Ch. 3, Lemma 1.2, Remark 1.3, the proof of Theorem 1.6 "⇒" and Remark 1.5(3),
chapter-03.txt lines 25–144).  Let `M ⊆ ℝᴾ` be Borel and countably `n`-rectifiable with
`Hⁿ(M) < ∞`.  Then `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞` for every compact `K`, so by Theorem 1.6 "⇒" the
approximate tangent space `T_wM` exists for `Hⁿ`-a.e. `w ∈ M`.  At such `w`, `Hⁿ(M ∩ B̄_1(w))` is
finite, so `Hⁿ(M ∩ B̄_t(w)) / (ωₙtⁿ) → 1` by Remark 1.5(3); for the measure `Hⁿ⌞M` this
closed-ball limit gives the open-ball limit `Hⁿ(M ∩ B_t(w)) / (ωₙtⁿ) → 1` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_rectifiable_ae_density_one : ∀ (P n : ℕ) (M : Set (Euclid P)), 1 ≤ n → MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → ∀ᵐ w ∂(μHE[n].restrict M), Tendsto (fun t : ℝ => μHE[n] (M ∩ ball w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M _ hM hrect hfin
  -- Step 1: `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞` for every `K`
  have hloc : ∀ K : Set (Euclid P), μHE[n] (M ∩ K) ≠ ∞ := fun K =>
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  -- Step 2 (Lemma 1.2, Remark 1.3, Theorem 1.6 "⇒"): approximate tangent spaces `Hⁿ`-a.e. on `M`
  have htan := Submission.codim1_rdo_rectifiable_ae_approxTangent P n M hM hrect fun K _ => hloc K
  -- Step 3: `Hⁿ⌞M` evaluates as `Hⁿ(M ∩ ·)`
  have hν : ∀ s : Set (Euclid P), μHE[n].restrict M s = μHE[n] (M ∩ s) := fun s => by
    rw [Measure.restrict_apply' hM, inter_comm]
  filter_upwards [htan] with w ⟨Q, hQ⟩
  -- Step 4 (Remark 1.5(3)): closed-ball density one at `w`, as `Hⁿ(M ∩ B̄_1(w)) < ∞`
  have hclosed := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M w Q 1 one_pos
    (hloc _) hQ
  -- Step 5: from closed to open balls, for the measure `Hⁿ⌞M`
  exact (Submission.rsd_tendsto_ball_density_of_closedBall P n (μHE[n].restrict M) w 1
    (hclosed.congr fun ρ => by rw [hν])).congr fun ρ => by rw [hν]

/-- **`μ = Hᵐ⌞B` with approximate tangent planes `ν(y)^⊥`** (Simon Ch. 3, 4.3, first part, given
the rectifiable density theorem (RD)).  Let `μ` be locally finite in the open set `D ⊆ ℝ^{m+1}`,
carried by `D`, with flat tangent measure `Hᵐ⌞ν(y)^⊥` at `μ`-a.e. `y`.  Then `μ = Hᵐ⌞B` for a
Borel countably `m`-rectifiable `B ⊆ D` whose approximate tangent space (Ch. 3, 1.4) at
`Hᵐ`-a.e. `y ∈ B` is `ν(y)^⊥`.  Take `B = (D ∩ R) \ N`, with `R` from
`codim1_rdo_dg_rectifiable_of_flat_tangent` and `N` a Borel `μ`-null set off which the flat
tangent exists, so `Θᵐ(μ, y) = 1` on `B` (`codim1_rdo_dg_flat_tangent_density_cone`).  A Vitali
`5r`-covering bounds `Hᵐ⌞B` locally by `μ`, and small covers give `μ ≪ Hᵐ⌞B`; (RD) gives
`Θᵐ(Hᵐ⌞B, w) = 1` a.e., so Besicovitch differentiation yields `dμ/d(Hᵐ⌞B) = 1` and `μ = Hᵐ⌞B`.
Finally `Hᵐ(η_{y,r}(A)) = r⁻ᵐ Hᵐ(A)` turns the flat tangent measure into Definition 1.4. -/
theorem Submission.codim1_rdo_dg_measure_eq_hausdorff : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), 1 ≤ m → IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, ∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → (∀ S : Set (Euclid (m + 1)), MeasurableSet S → CountablyRectifiable m S → μHE[m] S ≠ ∞ → ∀ᵐ w ∂(μHE[m].restrict S), Tendsto (fun t : ℝ => μHE[m] (S ∩ ball w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m))) (𝓝[>] 0) (𝓝 1)) → ∃ B : Set (Euclid (m + 1)), MeasurableSet B ∧ B ⊆ D ∧ CountablyRectifiable m B ∧ μ = μHE[m].restrict B ∧ ∀ᵐ y ∂(μHE[m].restrict B), HasApproximateTangentSpaceAt m B y (Submodule.span ℝ {ν y})ᗮ := by
  intro m D μ ν hm hD hμD hμK hνm hν1 hflat hRD
  -- (step 3 tool) local copy of the accepted `dorag_sn_hausdorff_le_mul_of_lower_density`
  have hcmp_gen : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
    intro N n c hc
    -- `μHE[n] = k • μH[n]` with a finite factor `k`; take `C = k · 10ⁿ / c`
    set k : NNReal :=
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)]
    refine ⟨(k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c),
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
    intro ν A O hO hAO hA
    have hdiam : ∀ (y : Euclid N) (ρ : ℝ), ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
      intro y ρ
      apply ediam_le_of_forall_dist_le
      intro z hz w hw
      rw [mem_closedBall] at hz hw
      linarith [dist_triangle_right z w y]
    -- scale `δ = 1 / (m + 1)`: a countable disjoint family of admissible balls whose 5-times
    -- enlargements cover `A`, of total cost at most `(10ⁿ/c) ν(O)`
    have step : ∀ m : ℕ, ∃ u : Set (Euclid N × ℝ), u.Countable ∧
        (∀ p ∈ u, ediam (closedBall p.1 (5 * p.2)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1))) ∧
        A ⊆ ⋃ p : u, closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2) ∧
        ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) ≤
          ENNReal.ofReal (10 ^ n / c) * ν O := by
      intro m
      set δ : ℝ := 1 / ((m : ℝ) + 1)
      have hδpos : 0 < δ := by positivity
      -- the admissible balls, as (center, radius) pairs
      set T : Set (Euclid N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧
        closedBall p.1 p.2 ⊆ O ∧ ENNReal.ofReal (c * p.2 ^ n) ≤ ν (closedBall p.1 p.2)}
      obtain ⟨u, huT, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun p => p.1)
          (fun p => p.2) δ (fun p hp => by linarith [hp.2.2.1, hp.2.1]) 5 (by norm_num)
      -- disjoint balls with nonempty interiors in the separable space `ℝᴺ`
      have hucount : u.Countable := by
        refine hudisj.countable_of_nonempty_interior fun p hp => ?_
        exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huT hp).2.1)⟩
      refine ⟨u, hucount, fun p hp => ?_, ?_, ?_⟩
      · obtain ⟨-, -, hpδ, -, -⟩ := huT hp
        refine (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        linarith
      · -- each `x ∈ A` is the center of a small admissible ball
        intro x hx
        obtain ⟨t₀, ht₀, hbound⟩ := hA x hx
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
        set r : ℝ := min (t₀ / 2) (min (ε / 2) (δ / 10))
        have hrpos : 0 < r := by positivity
        have hr₁ := min_le_left (t₀ / 2) (min (ε / 2) (δ / 10))
        have hr₂ := min_le_right (t₀ / 2) (min (ε / 2) (δ / 10))
        have hr₃ := min_le_left (ε / 2) (δ / 10)
        have hr₄ := min_le_right (ε / 2) (δ / 10)
        have hmem : (x, r) ∈ T :=
          ⟨hx, hrpos, by linarith, (closedBall_subset_ball (by linarith)).trans hball,
            hbound r hrpos (by linarith)⟩
        obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hmem
        exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_closedBall_self hrpos.le)⟩
      · calc ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
            ≤ ∑' p : u, ENNReal.ofReal (10 ^ n / c) *
                ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
              refine ENNReal.tsum_le_tsum fun p => ?_
              obtain ⟨-, hp0, -, -, hpν⟩ := huT p.2
              calc ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
                  ≤ ENNReal.ofReal (2 * (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) :=
                    ENNReal.rpow_le_rpow (hdiam _ _) (Nat.cast_nonneg n)
                _ = ENNReal.ofReal (10 ^ n / c) * ENNReal.ofReal (c * (p : Euclid N × ℝ).2 ^ n) := by
                    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
                      ← ENNReal.ofReal_mul (by positivity)]
                    congr 1
                    field_simp
                    ring
                _ ≤ ENNReal.ofReal (10 ^ n / c) *
                      ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
                    gcongr
          _ = ENNReal.ofReal (10 ^ n / c) * ν (⋃ p ∈ u, closedBall p.1 p.2) := by
              rw [ENNReal.tsum_mul_left,
                measure_biUnion hucount hudisj fun p _ => measurableSet_closedBall]
          _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
              gcongr
              exact iUnion₂_subset fun p hp => (huT hp).2.2.2.1
    choose u hucount hudiam hucov husum using step
    have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
    -- covers of mesh `1 / (m + 1) → 0`
    have main : μH[(n : ℝ)] A ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
      calc μH[(n : ℝ)] A
          ≤ liminf (fun m => ∑' p : u m,
              ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)) atTop := by
            refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) A
              (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) ?_
              (fun m p => closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2))
              (Eventually.of_forall fun m p => hudiam m p p.2) (Eventually.of_forall hucov)
            simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O :=
            liminf_le_of_frequently_le' (Frequently.of_forall husum)
    calc μHE[n] A = (k : ℝ≥0∞) * μH[(n : ℝ)] A := by
          rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
            smul_eq_mul]
      _ ≤ (k : ℝ≥0∞) * (ENNReal.ofReal (10 ^ n / c) * ν O) := by gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c) * ν O := by rw [mul_assoc]
  -- (step 4 tool) `Hⁿ`-null sets of closed-ball density-one points of `μ` are `μ`-null
  have hnull_gen : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)), (∀ x ∈ A, Tendsto (fun r : ℝ => μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 1)) → μHE[n] A = 0 → μ A = 0 := by
    intro P n μ A hdens hA
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    set C : ℝ≥0∞ := 2 * unitBallVolume n with hCdef
    have hC0 : C ≠ 0 := mul_ne_zero two_ne_zero hω0
    have hCtop : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hωtop
    -- the pieces `A_k` on which `μ` has uniform growth below radius `1/(k+1)`
    set Ak : ℕ → Set (Euclid P) := fun k => {x | x ∈ A ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / ((k : ℝ) + 1) →
      μ (closedBall x r) ≤ C * ENNReal.ofReal r ^ n} with hAkdef
    have hcover : A ⊆ ⋃ k, Ak k := by
      intro x hx
      have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < 2 :=
        (hdens x hx).eventually (gt_mem_nhds (by norm_num))
      obtain ⟨δ, hδ, hδsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h2
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine mem_iUnion.mpr ⟨k, hx, fun r hr hrk => ?_⟩
      have hq := hδsub ⟨hr, hrk.trans_lt hk⟩
      have hc0 : unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
      have hctop : unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ ∞ :=
        ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      have := ((ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop)).mp hq).le
      calc μ (closedBall x r) ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n)) := this
        _ = C * ENNReal.ofReal r ^ n := by rw [hCdef, ENNReal.ofReal_pow hr.le, mul_assoc]
    -- every `A_k` is `μ`-null
    have hnull : ∀ k, μ (Ak k) = 0 := by
      intro k
      set R : ℝ := 1 / ((k : ℝ) + 1) with hRdef
      have hR : 0 < R := by positivity
      have hHk : μH[(n : ℝ)] (Ak k) = 0 := by
        have h0 : μHE[n] (Ak k) = 0 := measure_mono_null (fun x hx => hx.1) hA
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul] at h0
        exact (mul_eq_zero.mp h0).resolve_left (by
          simpa using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
      have hdiam : ∀ s : Set (Euclid P), ediam s ≤ ENNReal.ofReal R →
          OuterMeasure.restrict (Ak k) μ.toOuterMeasure s ≤ C * ediam s ^ n := by
        intro s hs
        rw [OuterMeasure.restrict_apply, Measure.toOuterMeasure_apply]
        rcases (s ∩ Ak k).eq_empty_or_nonempty with he | ⟨x, hxs, hxA⟩
        · simp only [he, measure_empty, zero_le]
        have hsfin : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
        have hdR : (ediam s).toReal ≤ R := ENNReal.toReal_le_of_le_ofReal hR.le hs
        have hsub : s ∩ Ak k ⊆ closedBall x (ediam s).toReal := by
          intro y hy
          change dist y x ≤ (ediam s).toReal
          simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
            (ENNReal.toReal_mono hsfin (edist_le_ediam_of_mem hy.1 hxs))
        apply (measure_mono hsub).trans
        by_cases hd : 0 < (ediam s).toReal
        · simpa only [ENNReal.ofReal_toReal hsfin] using hxA.2 _ hd hdR
        · have hd0 : (ediam s).toReal = 0 := le_antisymm (not_lt.mp hd) ENNReal.toReal_nonneg
          have hed0 : ediam s = 0 := by
            rw [← ENNReal.ofReal_toReal hsfin, hd0, ENNReal.ofReal_zero]
          rw [hd0, hed0]
          -- zero radius: let the radius tend to zero in the growth bound
          have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
            tendsto_id.mono_left inf_le_left
          have hlim : Tendsto (fun r : ℝ ↦ C * (ENNReal.ofReal r) ^ n) (𝓝[>] 0)
              (𝓝 (C * (0 : ℝ≥0∞) ^ n)) := by
            simpa only [ENNReal.ofReal_zero, Function.comp_def] using
              ENNReal.Tendsto.const_mul
                (ENNReal.Tendsto.pow (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hid))
                (Or.inr hCtop)
          apply ge_of_tendsto hlim
          filter_upwards [Ioo_mem_nhdsGT hR] with r hr
          exact (measure_mono (closedBall_subset_closedBall hr.1.le)).trans
            (hxA.2 r hr.1 hr.2.le)
      have hm := OuterMeasure.le_mkMetric (fun d : ℝ≥0∞ ↦ C * d ^ n)
        (OuterMeasure.restrict (Ak k) μ.toOuterMeasure) (ENNReal.ofReal R)
        (ENNReal.ofReal_pos.mpr hR) hdiam
      have hcost : (fun d : ℝ≥0∞ ↦ C * d ^ n) = C • (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) := by
        funext d
        simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
      rw [hcost, OuterMeasure.mkMetric_smul _ hCtop hC0] at hm
      have hk := hm (Ak k)
      rw [OuterMeasure.restrict_apply, inter_self, Measure.toOuterMeasure_apply,
        smul_apply, smul_eq_mul] at hk
      have hH : OuterMeasure.mkMetric (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) (Ak k) = 0 := by
        have : (μH[(n : ℝ)] : Measure (Euclid P)).toOuterMeasure =
            OuterMeasure.mkMetric (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) := by
          rw [Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure]
        rw [← this, Measure.toOuterMeasure_apply, hHk]
      rw [hH, mul_zero] at hk
      exact le_antisymm hk zero_le
    exact measure_mono_null hcover (measure_iUnion_null hnull)
  -- (step 5 tool) (RD) on pieces `B ∩ ball` gives closed-ball density one of `Hⁿ⌞B` a.e.
  have hdens_gen : ∀ (P n : ℕ) (D B : Set (Euclid P)), IsOpen D → MeasurableSet B → B ⊆ D → CountablyRectifiable n B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μHE[n] (B ∩ K) ≠ ∞) → (∀ S : Set (Euclid P), MeasurableSet S → CountablyRectifiable n S → μHE[n] S ≠ ∞ → ∀ᵐ w ∂(μHE[n].restrict S), Tendsto (fun t : ℝ => μHE[n] (S ∩ ball w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1)) → ∀ᵐ w ∂(μHE[n].restrict B), Tendsto (fun t : ℝ => (μHE[n].restrict B) (closedBall w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
    intro P n D B hD hBm hBD hBrect hloc hRD
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    -- Step 1: open-ball density one of `Hⁿ⌞B` at `Hⁿ⌞B`-a.e. point, from (RD) on pieces
    have hopen : ∀ᵐ w ∂(μHE[n].restrict B), Tendsto (fun t : ℝ => μHE[n] (B ∩ ball w t) /
        (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
      have hrad : ∀ x : D, ∃ ε : ℝ, 0 < ε ∧ closedBall (x : Euclid P) ε ⊆ D := by
        intro x
        obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD x x.2
        exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεD⟩
      choose ε hε hεD using hrad
      obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
        (fun x : D => ball (x : Euclid P) (ε x)) (fun _ => isOpen_ball)
      have hcov : (⋃ x ∈ T, ball (x : Euclid P) (ε x)) = D := by
        rw [hT]
        apply subset_antisymm
        · exact iUnion_subset fun x => ball_subset_closedBall.trans (hεD x)
        · intro y hy
          exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hε ⟨y, hy⟩)⟩
      have hBae : ∀ᵐ w ∂(μHE[n].restrict B), w ∈ D :=
        (ae_restrict_mem hBm).mono fun w hw => hBD hw
      rw [← Measure.restrict_eq_self_of_ae_mem hBae, ← hcov,
        ae_restrict_biUnion_iff _ hTc]
      intro x _
      rw [Measure.restrict_restrict measurableSet_ball]
      have hSm : MeasurableSet (ball (x : Euclid P) (ε x) ∩ B) := measurableSet_ball.inter hBm
      have hSrect : CountablyRectifiable n (ball (x : Euclid P) (ε x) ∩ B) :=
        hBrect.mono inter_subset_right
      have hSfin : μHE[n] (ball (x : Euclid P) (ε x) ∩ B) ≠ ∞ :=
        ne_top_of_le_ne_top (hloc _ (isCompact_closedBall _ _) (hεD x))
          (measure_mono fun y hy => ⟨hy.2, ball_subset_closedBall hy.1⟩)
      filter_upwards [hRD _ hSm hSrect hSfin, ae_restrict_mem hSm] with w hw hwS
      refine hw.congr' ?_
      obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.mp isOpen_ball w hwS.1
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have hset : ball (x : Euclid P) (ε x) ∩ B ∩ ball w t = B ∩ ball w t := by
        ext y
        constructor
        · rintro ⟨⟨_, hyB⟩, hyt⟩
          exact ⟨hyB, hyt⟩
        · rintro ⟨hyB, hyt⟩
          exact ⟨⟨hδW (ball_subset_ball ht.2.le hyt), hyB⟩, hyt⟩
      rw [hset]
    -- Step 2: pass from open to closed balls by squeezing between radii `t` and `t + t²`
    filter_upwards [hopen] with w hw
    set c : ℝ → ℝ≥0∞ := fun t => unitBallVolume n * ENNReal.ofReal (t ^ n) with hcdef
    set q : ℝ → ℝ≥0∞ := fun t => μHE[n] (B ∩ ball w t) / c t with hqdef
    have hs : Tendsto (fun t : ℝ => t + t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t : ℝ => t + t ^ 2) (𝓝 0) (𝓝 (0 + 0 ^ 2)) :=
          (continuous_id.add (continuous_pow 2)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact add_pos_of_pos_of_nonneg ht (sq_nonneg t)
    have hk : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n)) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n)) (𝓝 0)
          (𝓝 (ENNReal.ofReal ((1 + 0) ^ n))) :=
        (ENNReal.continuous_ofReal.comp
          ((continuous_const.add continuous_id).pow n)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hupper : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n) * q (t + t ^ 2))
        (𝓝[>] 0) (𝓝 1) := by
      have := ENNReal.Tendsto.mul hk (Or.inl one_ne_zero) (hw.comp hs) (Or.inl one_ne_zero)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hw hupper ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show μHE[n] (B ∩ ball w t) / c t ≤ (μHE[n].restrict B) (closedBall w t) / c t
      rw [Measure.restrict_apply measurableSet_closedBall]
      have hsub : B ∩ ball w t ⊆ closedBall w t ∩ B := fun y hy =>
        ⟨ball_subset_closedBall hy.2, hy.1⟩
      exact ENNReal.div_le_div_right (measure_mono hsub) _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hk0 : ENNReal.ofReal ((1 + t) ^ n) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (pow_pos (by linarith) n)).ne'
      have hktop : ENNReal.ofReal ((1 + t) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
      have hc0 : c t ≠ 0 := mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht0 n)).ne'
      have hctop : c t ≠ ∞ := ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      have hcs : c (t + t ^ 2) = c t * ENNReal.ofReal ((1 + t) ^ n) := by
        simp only [hcdef]
        rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg ht0.le n), ← mul_pow]
        congr 3
        ring
      show (μHE[n].restrict B) (closedBall w t) / c t ≤
        ENNReal.ofReal ((1 + t) ^ n) * (μHE[n] (B ∩ ball w (t + t ^ 2)) / c (t + t ^ 2))
      rw [Measure.restrict_apply measurableSet_closedBall, hcs]
      have hsub : closedBall w t ∩ B ⊆ B ∩ ball w (t + t ^ 2) := fun y hy =>
        ⟨hy.2, closedBall_subset_ball (by nlinarith) hy.1⟩
      calc μHE[n] (closedBall w t ∩ B) / c t
          ≤ μHE[n] (B ∩ ball w (t + t ^ 2)) / c t := ENNReal.div_le_div_right (measure_mono hsub) _
        _ = ENNReal.ofReal ((1 + t) ^ n) *
            (μHE[n] (B ∩ ball w (t + t ^ 2)) / (c t * ENNReal.ofReal ((1 + t) ^ n))) := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← mul_assoc, ← mul_assoc,
            mul_comm (ENNReal.ofReal _) (c t)⁻¹, mul_assoc (c t)⁻¹,
            ENNReal.mul_inv_cancel hk0 hktop, mul_one]
  -- (step 6 tool) `μ ≪ ρ` and ball ratios `μ/ρ → 1` `ρ`-a.e. force `μ = ρ` (Besicovitch)
  have heq_gen : ∀ (P : ℕ) (D : Set (Euclid P)) (μ ρ : Measure (Euclid P)), IsOpen D → μ Dᶜ = 0 → ρ Dᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → ρ K ≠ ∞) → μ ≪ ρ → (∀ᵐ w ∂ρ, Tendsto (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t)) (𝓝[>] 0) (𝓝 1)) → μ = ρ := by
    intro P D μ ρ hD hμD hρD hμK hρK hac hratio
    -- Step 1: equality on every open ball whose closure lies in `D`
    have hlocal : ∀ c : Euclid P, ∀ s : ℝ, closedBall c s ⊆ D →
        μ.restrict (ball c s) = ρ.restrict (ball c s) := by
      intro c s hcs
      have hfinμ : μ (ball c s) ≠ ∞ := ne_top_of_le_ne_top
        (hμK _ (isCompact_closedBall c s) hcs) (measure_mono ball_subset_closedBall)
      have hfinρ : ρ (ball c s) ≠ ∞ := ne_top_of_le_ne_top
        (hρK _ (isCompact_closedBall c s) hcs) (measure_mono ball_subset_closedBall)
      have : IsFiniteMeasure (μ.restrict (ball c s)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinμ.lt_top⟩
      have : IsFiniteMeasure (ρ.restrict (ball c s)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinρ.lt_top⟩
      have hacW : μ.restrict (ball c s) ≪ ρ.restrict (ball c s) := hac.restrict _
      have hone : (μ.restrict (ball c s)).rnDeriv (ρ.restrict (ball c s))
          =ᵐ[ρ.restrict (ball c s)] 1 := by
        filter_upwards [Besicovitch.ae_tendsto_rnDeriv (μ.restrict (ball c s))
            (ρ.restrict (ball c s)), ae_restrict_mem measurableSet_ball,
            ae_restrict_of_ae hratio] with w hw hwW hwr
        obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp isOpen_ball w hwW
        have heq : (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t)) =ᶠ[𝓝[>] 0]
            (fun t : ℝ => μ.restrict (ball c s) (closedBall w t) /
              ρ.restrict (ball c s) (closedBall w t)) := by
          filter_upwards [Ioo_mem_nhdsGT hε] with t ht
          have hsub : closedBall w t ⊆ ball c s := (closedBall_subset_ball ht.2).trans hεW
          rw [Measure.restrict_apply measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub]
        exact tendsto_nhds_unique hw (hwr.congr' heq)
      calc μ.restrict (ball c s)
          = (ρ.restrict (ball c s)).withDensity
              ((μ.restrict (ball c s)).rnDeriv (ρ.restrict (ball c s))) :=
            by
              have h := Measure.singularPart_add_rnDeriv (μ.restrict (ball c s)) (ρ.restrict (ball c s))
              rw [Measure.singularPart_eq_zero_of_ac hacW, zero_add] at h
              exact h.symm
        _ = (ρ.restrict (ball c s)).withDensity 1 := withDensity_congr_ae hone
        _ = ρ.restrict (ball c s) := withDensity_one
    -- Step 2: countably many such balls cover `D`
    have hrad : ∀ x : D, ∃ ε : ℝ, 0 < ε ∧ closedBall (x : Euclid P) ε ⊆ D := by
      intro x
      obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD x x.2
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεD⟩
    choose ε hε hεD using hrad
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : D => ball (x : Euclid P) (ε x)) (fun _ => isOpen_ball)
    have hcov : (⋃ x ∈ T, ball (x : Euclid P) (ε x)) = D := by
      rw [hT]
      apply subset_antisymm
      · exact iUnion_subset fun x => ball_subset_closedBall.trans (hεD x)
      · intro y hy
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hε ⟨y, hy⟩)⟩
    have hD' : μ.restrict D = ρ.restrict D := by
      rw [← hcov]
      exact (Measure.restrict_biUnion_congr hTc).mpr fun x _ => hlocal x (ε x) (hεD x)
    have hμae : ∀ᵐ x ∂μ, x ∈ D := by
      rw [ae_iff]
      exact hμD
    have hρae : ∀ᵐ x ∂ρ, x ∈ D := by
      rw [ae_iff]
      exact hρD
    rw [← Measure.restrict_eq_self_of_ae_mem hμae, ← Measure.restrict_eq_self_of_ae_mem hρae, hD']
  -- (step 7 tool) local copy of the accepted `setIntegral_blowUpMap_image_eq_inv_pow_mul`
  have hcov_gen : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
    intro P n M x r hr f
    -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
    obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
        ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
      ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
    -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
    have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
      intro S
      have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
        rw [image_image, he]
        rfl
      rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
    -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
    have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
      ext A hA
      rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
        Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
        e.image_preimage]
    -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
    rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
      NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hr)]
  -- Step 1: the good set `G` of flat-tangent points, of full `μ`-measure
  set G : Set (Euclid (m + 1)) := {y | ∀ f : Euclid (m + 1) → ℝ, Continuous f →
    HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))}
    with hGdef
  have hGc : μ Gᶜ = 0 := hflat
  -- Step 2: rectifiable carrier `B = (D ∩ R) \ N`
  obtain ⟨R, hRm, hRrect, hRc⟩ :=
    Submission.codim1_rdo_dg_rectifiable_of_flat_tangent m D μ ν hm hD hμD hμK hνm hν1 hflat
  set N : Set (Euclid (m + 1)) := toMeasurable μ Gᶜ with hNdef
  set B : Set (Euclid (m + 1)) := (D ∩ R) \ N with hBdef
  have hBm : MeasurableSet B :=
    (hD.measurableSet.inter hRm).diff (measurableSet_toMeasurable _ _)
  have hBD : B ⊆ D := fun y hy => hy.1.1
  have hBrect : CountablyRectifiable m B := hRrect.mono fun y hy => hy.1.2
  have hBG : ∀ y ∈ B, y ∈ G := by
    intro y hy
    by_contra h
    exact hy.2 (subset_toMeasurable μ Gᶜ h)
  have hN : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact hGc
  have hμBc : μ Bᶜ = 0 := by
    have hsub : Bᶜ ⊆ Dᶜ ∪ Rᶜ ∪ N := by
      intro y hy
      by_cases hyD : y ∈ D
      · by_cases hyR : y ∈ R
        · right
          by_contra hyN
          exact hy ⟨⟨hyD, hyR⟩, hyN⟩
        · left; right; exact hyR
      · left; left; exact hyD
    exact measure_mono_null hsub (measure_union_null (measure_union_null hμD hRc) hN)
  -- Step 1 (cont.): density one of `μ` at every point of `B`
  have hdens : ∀ y ∈ B, Tendsto (fun r : ℝ => μ (closedBall y r) /
      (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) := by
    intro y hy
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD y (hBD hy)
    have hfin : ∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞ :=
      ⟨ε / 2, half_pos hε, hμK _ (isCompact_closedBall y (ε / 2))
        ((closedBall_subset_ball (half_lt_self hε)).trans hεD)⟩
    exact (Submission.codim1_rdo_dg_flat_tangent_density_cone m μ y (ν y) hm (hν1 y) hfin
      (hBG y hy)).1
  have hω0 : unitBallVolume m ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
  have hωtop : unitBallVolume m ≠ ∞ := measure_ball_lt_top.ne
  -- Step 3: local finiteness of `Hᵐ⌞B` by the density comparison
  have hω2top : unitBallVolume m / 2 ≠ ∞ := ENNReal.div_ne_top hωtop two_ne_zero
  set c : ℝ := (unitBallVolume m / 2).toReal with hcdef
  have hc : 0 < c := ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hω0, ENNReal.ofNat_ne_top⟩)
    hω2top
  obtain ⟨C, hCtop, hcmp⟩ := hcmp_gen (m + 1) m c hc
  have hlow : ∀ x ∈ B, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ENNReal.ofReal (c * t ^ m) ≤ μ (closedBall x t) := by
    intro x hx
    have h := (hdens x hx).eventually (lt_mem_nhds (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
    obtain ⟨t₀, ht₀, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h
    refine ⟨t₀, ht₀, fun t ht htt => ?_⟩
    have hq : 2⁻¹ < μ (closedBall x t) / (unitBallVolume m * ENNReal.ofReal (t ^ m)) :=
      hsub ⟨ht, htt⟩
    have hden0 : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht m)).ne'
    have hdentop : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    have hlt := (ENNReal.lt_div_iff_mul_lt (Or.inl hden0) (Or.inl hdentop)).mp hq
    calc ENNReal.ofReal (c * t ^ m) = unitBallVolume m / 2 * ENNReal.ofReal (t ^ m) := by
          rw [ENNReal.ofReal_mul hc.le, hcdef, ENNReal.ofReal_toReal hω2top]
      _ = 2⁻¹ * (unitBallVolume m * ENNReal.ofReal (t ^ m)) := by
          rw [ENNReal.div_eq_inv_mul, mul_assoc]
      _ ≤ μ (closedBall x t) := hlt.le
  have hloc : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μHE[m] (B ∩ K) ≠ ∞ := by
    intro K hK hKD
    obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
    have hle := hcmp μ (B ∩ K) (thickening δ K) isOpen_thickening
      (inter_subset_right.trans (self_subset_thickening hδ K)) (fun x hx => hlow x hx.1)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hCtop (hμK _ hK.cthickening hδD))
      (hle.trans (mul_le_mul' le_rfl (measure_mono (thickening_subset_cthickening δ K))))
  set ρ : Measure (Euclid (m + 1)) := μHE[m].restrict B with hρdef
  have hρDc : ρ Dᶜ = 0 := by
    rw [hρdef, Measure.restrict_apply hD.measurableSet.compl]
    have : Dᶜ ∩ B = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hyD hyB
      exact hyD (hBD hyB)
    rw [this, measure_empty]
  have hρK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ρ K ≠ ∞ := by
    intro K hK hKD
    rw [hρdef, Measure.restrict_apply' hBm, inter_comm]
    exact hloc K hK hKD
  -- Step 4: `μ ≪ Hᵐ⌞B`
  have hac : μ ≪ ρ := by
    intro A hA
    rw [hρdef, Measure.restrict_apply' hBm] at hA
    have h1 : μ (A ∩ B) = 0 :=
      hnull_gen (m + 1) m μ (A ∩ B)
        (fun x hx => hdens x hx.2) hA
    refine measure_mono_null (fun y hy => ?_) (measure_union_null h1 hμBc)
    by_cases hyB : y ∈ B
    · exact Or.inl ⟨hy, hyB⟩
    · exact Or.inr hyB
  -- Step 5: density one of `Hᵐ⌞B`
  have hρdens := hdens_gen (m + 1) m D B hD hBm
    hBD hBrect hloc hRD
  -- Step 6: ball ratios and identification
  have hratio : ∀ᵐ w ∂ρ, Tendsto (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t))
      (𝓝[>] 0) (𝓝 1) := by
    filter_upwards [hρdens, ae_restrict_mem hBm] with w hw hwB
    have h := ENNReal.Tendsto.div (hdens w hwB) (Or.inl one_ne_zero) hw
      (Or.inl ENNReal.one_ne_top)
    rw [ENNReal.div_self one_ne_zero ENNReal.one_ne_top] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hc0 : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht m)).ne'
    have hctop : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    show μ (closedBall w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m)) /
        (ρ (closedBall w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m))) =
      μ (closedBall w t) / ρ (closedBall w t)
    conv_lhs => rw [div_eq_mul_inv (μ (closedBall w t)), div_eq_mul_inv (ρ (closedBall w t))]
    exact ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.mpr hctop)
      (ENNReal.inv_ne_top.mpr hc0)
  have hμeq : μ = μHE[m].restrict B :=
    heq_gen (m + 1) D μ ρ hD hμD hρDc hμK hρK hac hratio
  refine ⟨B, hBm, hBD, hBrect, hμeq, ?_⟩
  -- Step 7: approximate tangent planes by scaling
  filter_upwards [ae_restrict_mem hBm] with y hy
  have hν0 : ν y ≠ 0 := by
    intro h
    have := hν1 y
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hflaty : y ∈ G := hBG y hy
  simp only [hGdef, mem_ofPred_eq] at hflaty
  rw [hμeq] at hflaty
  refine ⟨?_, fun f => ?_⟩
  · have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
    exact Submodule.finrank_orthogonal_span_singleton hν0
  · refine (hflaty f f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hcov_gen (m + 1) m B y r hr f, inv_pow]
    rfl

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
