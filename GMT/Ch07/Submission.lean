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

/-- **Simon 7.3.1** (proof of (2), local retraction onto `N`, chart step): if `W` is open, `ψ` is
continuous and injective on `V`, `ψ(V) = W ∩ N` and `ψ` is proper over `W` (`V ∩ ψ⁻¹(K)` is
compact for compact `K ⊆ W`), then `N ∩ B_ρ(ψ(v₀)) ⊆ ψ(V₀)` for some `ρ > 0`, whenever `V₀ ⊆ V`
is open and `v₀ ∈ V₀`.  Otherwise there are `yᵢ = ψ(fᵢ) ∈ N` with `fᵢ ∈ V \ V₀` and
`yᵢ → ψ(v₀)`; the `fᵢ` lie in the compact set `V ∩ ψ⁻¹({ψ(v₀)} ∪ {yᵢ})`, so a subsequence
converges to some `a ∈ V \ V₀` with `ψ(a) = ψ(v₀)`, contradicting injectivity. -/
theorem Submission.dtc_bc_lr_chart_image_nhds : ∀ (P d : ℕ) (N W : Set (Euclid P)) (V V₀ : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₀ → V₀ ⊆ V → v₀ ∈ V₀ → ∃ ρ : ℝ, 0 < ρ ∧ N ∩ ball (ψ v₀) ρ ⊆ ψ '' V₀ := by
  intro P d N W V V₀ ψ v₀ hW hψc hψi hψV hprop hV₀ hV₀V hv₀
  -- Step 1: `x := ψ v₀ ∈ W` and `B_{r_W}(x) ⊆ W`
  have hv₀V : v₀ ∈ V := hV₀V hv₀
  have hxW : ψ v₀ ∈ W := (hψV ▸ mem_image_of_mem ψ hv₀V : ψ v₀ ∈ W ∩ N).1
  obtain ⟨rW, hrW, hballW⟩ := Metric.isOpen_iff.1 hW _ hxW
  -- Step 2: otherwise pick `yᵢ ∈ N ∩ B_{min(r_W, 1/(i+1))}(x) \ ψ(V₀)`, so `yᵢ ∈ W` and `yᵢ → x`
  by_contra hcon
  have hseq : ∀ i : ℕ, ∃ y, y ∈ N ∧ dist y (ψ v₀) < min rW (1 / ((i : ℝ) + 1)) ∧ y ∉ ψ '' V₀ := by
    intro i
    obtain ⟨y, ⟨hyN, hyb⟩, hy⟩ := not_subset.1 fun h =>
      hcon ⟨min rW (1 / ((i : ℝ) + 1)), lt_min hrW (by positivity), h⟩
    exact ⟨y, hyN, hyb, hy⟩
  choose y hyN hyd hyV₀ using hseq
  have hyW : ∀ i, y i ∈ W := fun i => hballW ((hyd i).trans_le (min_le_left _ _))
  have hylim : Tendsto y atTop (𝓝 (ψ v₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun i => dist_nonneg)
      (fun i => ((hyd i).trans_le (min_le_right _ _)).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  -- Step 3: `yᵢ = ψ(fᵢ)` with `fᵢ ∈ V \ V₀`
  have hf : ∀ i, ∃ f, f ∈ V ∧ ψ f = y i := fun i => (hψV.symm ▸ ⟨hyW i, hyN i⟩ : y i ∈ ψ '' V)
  choose f hfV hfy using hf
  have hfV₀ : ∀ i, f i ∉ V₀ := fun i hi => hyV₀ i ⟨f i, hi, hfy i⟩
  -- Step 4: `K := {x} ∪ {yᵢ}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K) ∋ fᵢ` is compact
  have hKW : insert (ψ v₀) (range y) ⊆ W := by
    rintro z (rfl | ⟨i, rfl⟩)
    exacts [hxW, hyW i]
  have hfK : ∀ i, f i ∈ V ∩ ψ ⁻¹' insert (ψ v₀) (range y) := fun i =>
    ⟨hfV i, Or.inr ⟨i, (hfy i).symm⟩⟩
  -- Step 5: a subsequence `f_{φ(i)} → a ∈ V`
  obtain ⟨a, ⟨haV, -⟩, φ, hφ, hfa⟩ :=
    (hprop _ hKW hylim.isCompact_insert_range).tendsto_subseq hfK
  -- Step 6: `a ∉ V₀`, as `V₀ᶜ` is closed
  have haV₀ : a ∉ V₀ :=
    hV₀.isClosed_compl.mem_of_tendsto hfa (Eventually.of_forall fun i => hfV₀ (φ i))
  -- Step 7: `ψ(a) = x` by continuity of `ψ` on `V` and uniqueness of limits
  have h₁ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ a)) :=
    (hψc a haV).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hfa, Eventually.of_forall fun i => hfV (φ i)⟩)
  have h₂ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ v₀)) := by
    have hcomp : ψ ∘ (f ∘ φ) = y ∘ φ := funext fun i => hfy (φ i)
    rw [hcomp]
    exact hylim.comp hφ.tendsto_atTop
  -- Step 8: injectivity gives `a = v₀ ∈ V₀`, a contradiction
  exact haV₀ (hψi haV hv₀V (tendsto_nhds_unique h₁ h₂) ▸ hv₀)
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
/-- **Tangent space of a hypersurface in an `(m + 1)`-plane** (Simon Ch. 2, §4, (4.3), and
Appendix B, p. 231: `T_xM` and the unit normal `ν(x)` together span the ambient space).  Let
`M ⊆ A₀` be an embedded `C¹` `m`-submanifold, `dim A₀ = m + 1`, and let `ν(x) ∈ A₀` be a unit
vector orthogonal to `T_xM`.  Then `T_xM = A₀ ∩ ν(x)ᗮ`, and the orthogonal projection onto
`T_xM` is `w ↦ Π_{A₀}w − (ν(x)·w)ν(x)`.  A chart `ψ` with `ψ(v₀) = x` gives
`T_xM = Dψ(v₀)(ℝᵐ)`, of dimension `m`.  Difference quotients of curves in `M ⊆ A₀` lie in the
closed subspace `A₀`, so `T_xM ⊆ A₀ ∩ ν(x)ᗮ`, which has dimension `(m + 1) − 1 = m`; hence
equality.  Finally `u = Π_{A₀}w − (ν(x)·w)ν(x)` lies in `A₀ ∩ ν(x)ᗮ` and `w − u` is orthogonal
to it. -/
theorem Submission.codim1_hcp_sc_tangent_normal_complement : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → IsEmbeddedSubmanifold 1 m M → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, tangentSpace M x = {v : Euclid P | v ∈ A₀ ∧ inner ℝ (ν x) v = 0} ∧ ∀ w : Euclid P, (Submodule.span ℝ (tangentSpace M x)).starProjection w = A₀.starProjection w - inner ℝ (ν x) w • ν x := by
  intro P m A₀ M ν hdim hMA hM hν x hx
  obtain ⟨hνA, hν1, hνT⟩ := hν x hx
  -- Step 1: a chart `ψ` at `x = ψ(v₀)` gives `T_xM = Dψ(v₀)(ℝᵐ)`, a subspace of dimension `m`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, hψV, hprop, hDψ⟩ := hM x hx
  obtain ⟨v₀, hv₀, hψv₀⟩ : x ∈ ψ '' V := hψV ▸ ⟨hxW, hx⟩
  set L : Submodule ℝ (Euclid P) :=
    LinearMap.range ((fderiv ℝ ψ v₀ : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) with hL
  have hT : tangentSpace M x = (L : Set (Euclid P)) := by
    rw [← hψv₀]
    exact Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W V ψ v₀ le_rfl hV hW hψ hinj
      hψV hprop hDψ hv₀
  have hLdim : Module.finrank ℝ L = m := by
    rw [hL, LinearMap.finrank_range_of_inj (hDψ v₀ hv₀), finrank_euclideanSpace_fin]
  -- Step 2: `T_xM ⊆ A₀`, as difference quotients of curves in `M ⊆ A₀` lie in the closed `A₀`
  have hTA : ∀ v ∈ tangentSpace M x, v ∈ A₀ := by
    rintro v ⟨γ, -, hγM, hγ0, hγv⟩
    refine A₀.closed_of_finiteDimensional.mem_of_tendsto hγv.tendsto_slope ?_
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1))] with t ht
    rw [slope_def_module]
    exact A₀.smul_mem _ (A₀.sub_mem (hMA (hγM ht)) (hγ0 ▸ hMA hx))
  -- Step 3: `T_xM ⊆ H = A₀ ∩ ν(x)ᗮ`
  set H : Submodule ℝ (Euclid P) := (ℝ ∙ ν x)ᗮ ⊓ A₀ with hH
  have hmemH : ∀ v, v ∈ H ↔ v ∈ A₀ ∧ inner ℝ (ν x) v = 0 := fun v => by
    rw [hH, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right, and_comm]
  have hLH : L ≤ H := fun v hv => by
    have hvT : v ∈ tangentSpace M x := hT ▸ hv
    exact (hmemH v).2 ⟨hTA v hvT, hνT v hvT⟩
  -- Step 4: `dim H = (m + 1) - 1 = m`, since `ν(x) ∈ A₀` is a unit vector
  have hν0 : ν x ≠ 0 := by
    rintro h
    rw [h, norm_zero] at hν1
    exact zero_ne_one hν1
  have hHdim : Module.finrank ℝ H = m := by
    have h : Module.finrank ℝ (ℝ ∙ ν x) + Module.finrank ℝ H = Module.finrank ℝ A₀ :=
      Submodule.finrank_add_inf_finrank_orthogonal
        ((Submodule.span_singleton_le_iff_mem (ν x) A₀).2 hνA)
    rw [finrank_span_singleton hν0, hdim] at h
    omega
  -- Step 5: `T_xM = H`
  have hLeq : L = H := Submodule.eq_of_le_of_finrank_eq hLH (hLdim.trans hHdim.symm)
  have hspan : Submodule.span ℝ (tangentSpace M x) = H := by
    rw [hT, Submodule.span_eq, hLeq]
  refine ⟨?_, fun w => ?_⟩
  · rw [hT, hLeq]
    ext v
    exact hmemH v
  -- Step 6: `u = Πw - ⟪ν(x), w⟫ν(x)` lies in `H` and `w - u ⊥ H`
  · have hPν : inner ℝ (ν x) (A₀.starProjection w) = inner ℝ (ν x) w := by
      rw [← Submodule.inner_starProjection_left_eq_right A₀,
        Submodule.starProjection_eq_self_iff.2 hνA]
    have hνν : inner ℝ (ν x) (ν x) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hν1, one_pow]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan, hmemH]
      refine ⟨A₀.sub_mem (A₀.starProjection_apply_mem w) (A₀.smul_mem _ hνA), ?_⟩
      rw [inner_sub_right, real_inner_smul_right, hPν, hνν, mul_one, sub_self]
    · intro h hh
      rw [hspan, hmemH] at hh
      have h1 : inner ℝ (w - A₀.starProjection w) h = 0 :=
        Submodule.starProjection_inner_eq_zero w h hh.1
      rw [sub_sub_eq_add_sub, add_sub_right_comm, inner_add_left, h1, real_inner_smul_left, hh.2,
        mul_zero, zero_add]
/-- **`Cʳ` inverse function theorem with a `Cʳ` inverse on a neighbourhood** (Simon Ch. 2, 4.4;
smooth charts of the hypercone plane: `φ` maps an open `V₀ ∋ z₀` `Cʳ`-diffeomorphically onto an
open `O`).  If `φ : ℝᵈ → ℝᵈ` is `Cʳ` (`r ≥ 1`) on an open `V ∋ z₀` and `Dφ(z₀)` is injective,
there are open sets `V₀`, `O` with `z₀ ∈ V₀ ⊆ V` such that `φ : V₀ → O` is a bijection whose
inverse `χ` is `Cʳ` on `O`.  `Dφ` is continuous on `V`, so `V' = {z ∈ V : Dφ(z) injective}` is
open; the strict-derivative inverse function theorem gives an open partial homeomorphism `Φ = φ`
with `z₀ ∈ Φ.source`; take `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀` and
`χ = Φ.symm`, which is `Cʳ` at every `a ∈ O` because `Dφ(χ a)` is invertible. -/
theorem Submission.codim1_hcp_sc_local_inverse_cr : ∀ (d r : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), 1 ≤ r → IsOpen V → z₀ ∈ V → ContDiffOn ℝ r φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (χ : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ r χ O ∧ MapsTo χ O V₀ ∧ (∀ a ∈ O, φ (χ a) = a) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ χ (φ z) = z := by
  intro d r φ V z₀ hr hV hz₀ hφ hinj
  -- `r ≥ 1` as an exponent in `WithTop ℕ∞`: `1 ≤ r` and `r ≠ 0`
  have hr1 : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  -- step 1: `φ` is `Cʳ` and differentiable at every point of `V`, and `Dφ` is continuous on `V`
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV hr1
  have hdiff : ∀ z ∈ V, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hφ.contDiffAt (hV.mem_nhds hz)).differentiableAt hr0).hasFDerivAt
  -- step 2: an injective endomorphism of `ℝᵈ` is a continuous linear equivalence
  have equivOf : ∀ L : Euclid d →L[ℝ] Euclid d, Injective L →
      ∃ E : Euclid d ≃L[ℝ] Euclid d, (E : Euclid d →L[ℝ] Euclid d) = L := by
    intro L hL
    have hsurj : Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨(LinearEquiv.ofBijective (L : Euclid d →ₗ[ℝ] Euclid d)
      ⟨hL, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  -- step 3: `V' = {z ∈ V : Dφ(z) injective}` is open and contains `z₀`
  set V' := V ∩ (fderiv ℝ φ) ⁻¹' {L | Injective L}
  have hV' : IsOpen V' := hcont.isOpen_inter_preimage hV ContinuousLinearMap.isOpen_injective
  have hz₀' : z₀ ∈ V' := ⟨hz₀, hinj⟩
  -- step 4: the inverse function theorem at `z₀` gives `Φ = φ` with `z₀ ∈ Φ.source`
  obtain ⟨E₀, hE₀⟩ := equivOf _ hinj
  have hstrict : HasStrictFDerivAt φ (E₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hE₀]; exact (hφ.contDiffAt (hV.mem_nhds hz₀)).hasStrictFDerivAt hr0
  set Φ := hstrict.toOpenPartialHomeomorph φ
  have hΦcoe : ∀ z, Φ z = φ z := fun z => rfl
  -- step 5: `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀`, `χ = Φ.symm`; for `a ∈ O`,
  -- `χ a ∈ V₀` and `φ (χ a) = a`
  have hV₀ : IsOpen (Φ.source ∩ V') := Φ.open_source.inter hV'
  refine ⟨Φ.source ∩ V', Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ V'), Φ.symm, hV₀,
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV₀,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀'⟩, fun z hz => hz.2.1, ?_,
    fun a ha => ha.2, fun a ha => by rw [← hΦcoe]; exact Φ.right_inv ha.1, fun z hz => ?_⟩
  -- step 7: `χ` is `Cʳ` at every `a ∈ O`, since `Dφ(χ a)` is invertible and `φ` is `Cʳ` at `χ a`
  · intro a ha
    have hz : Φ.symm a ∈ V' := ha.2.2
    obtain ⟨E, hE⟩ := equivOf _ hz.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ.contDiffAt_symm ha.1
    · rw [hE]; exact hdiff _ hz.1
    · exact hφ.contDiffAt (hV.mem_nhds hz.1)
  -- step 6: for `z ∈ V₀`, `φ z ∈ O` and `χ (φ z) = z`
  · have h1 : Φ.symm (Φ z) = z := Φ.left_inv hz.1
    rw [← hΦcoe]
    exact ⟨⟨Φ.map_source hz.1, by rw [Set.mem_preimage, h1]; exact hz⟩, h1⟩
/-- **A linear left inverse makes a map an injective immersion** (Simon Ch. 2, §4, (4.4), where
the graph map `G(x) = (x, u(x))` has the linear left inverse `(x, y) ↦ x`; step 4 of the `C^∞`
chart construction for the hypercone plane).  Let `D ⊆ ℝᵈ` be open, `g` differentiable on `D`,
and `π : ℝᴾ → ℝᵈ` continuous linear with `π(g(a) − c) = a` for `a ∈ D`.  Then `g` is injective
on `D`, since `a = π(g(a) − c) = π(g(b) − c) = b`.  For `a ∈ D` the map `b ↦ π(g(b) − c)` has
derivative `π ∘ Dg(a)` at `a` by the chain rule, and it agrees with the identity on the
neighbourhood `D` of `a`; uniqueness of the derivative gives `π ∘ Dg(a) = id`, so `π` is a left
inverse of `Dg(a)` and `Dg(a)` is injective. -/
theorem Submission.codim1_hcp_sc_left_inverse_immersion : ∀ (P d : ℕ) (D : Set (Euclid d)) (g : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), IsOpen D → DifferentiableOn ℝ g D → (∀ a ∈ D, π (g a - c) = a) → InjOn g D ∧ ∀ a ∈ D, π ∘L fderiv ℝ g a = ContinuousLinearMap.id ℝ (Euclid d) ∧ Injective (fderiv ℝ g a) := by
  intro P d D g π c hD hg hπ
  -- Steps 2–3: `π ∘ Dg(a) = id` for every `a ∈ D`
  have hid : ∀ a ∈ D, π ∘L fderiv ℝ g a = ContinuousLinearMap.id ℝ (Euclid d) := by
    intro a ha
    -- chain rule: `b ↦ π(g(b) − c)` has derivative `π ∘ Dg(a)` at `a`
    have h₁ : HasFDerivAt (fun b => π (g b - c)) (π ∘L fderiv ℝ g a) a :=
      π.hasFDerivAt.comp a ((hg.hasFDerivAt (hD.mem_nhds ha)).sub_const c)
    -- it equals the identity on the neighbourhood `D` of `a`, so it also has derivative `id`
    have h₂ : HasFDerivAt (fun b => π (g b - c)) (ContinuousLinearMap.id ℝ (Euclid d)) a :=
      (hasFDerivAt_id a).congr_of_eventuallyEq (eventually_of_mem (hD.mem_nhds ha) hπ)
    -- uniqueness of the Fréchet derivative
    exact h₁.unique h₂
  refine ⟨fun a ha b hb hab => ?_, fun a ha => ⟨hid a ha, ?_⟩⟩
  · -- Step 1: `a = π(g(a) − c) = π(g(b) − c) = b`
    rw [← hπ a ha, hab, hπ b hb]
  · -- Step 4: `π(Dg(a) u) = u`, so `π` is a left inverse of `Dg(a)`
    exact LeftInverse.injective fun u => DFunLike.congr_fun (hid a ha) u

/-- **Simon Ch. 2, §4, Remark 4.4** (local graphical representation, using (4.2)): let `ψ` be
`Cʳ` (`r ≥ 1`), 1:1 and proper on the open set `V` with `ψ(V) = W ∩ N`, and let `π` be
continuous linear with `π ∘ Dψ(v₀)` injective.  Then `φ = π(ψ − c)` has `Dφ(v₀) = π ∘ Dψ(v₀)`,
so the inverse function theorem gives a `Cʳ` inverse `χ : D → S` of `φ` with `v₀ ∈ S ⊆ V`, and
`g = ψ ∘ χ` is `Cʳ` on `D` with `π(g(a) − c) = a` and `g(D) = ψ(S)`.  As `ψ` is open onto its
image (4.2), `ψ(S) = O ∩ N` for the open set `O = W ∩ ⋃_{v ∈ S} B_{ρ_v}(ψ(v))`.  The left
inverse `π(· − c)` makes `g` and every `Dg(a)` injective, and for compact `K ⊆ O`,
`D ∩ g⁻¹(K) = π((N ∩ K) − c)`, where `N ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact. -/
theorem Submission.codim1_hcp_sc_graph_reparam : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P) (v₀ : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → Injective (π ∘L fderiv ℝ ψ v₀) → ∃ (D : Set (Euclid d)) (O : Set (Euclid P)) (g : Euclid d → Euclid P), IsOpen D ∧ IsOpen O ∧ ψ v₀ ∈ O ∧ O ⊆ W ∧ ContDiffOn ℝ r g D ∧ InjOn g D ∧ g '' D = O ∩ N ∧ (∀ K ⊆ O, IsCompact K → IsCompact (D ∩ g ⁻¹' K)) ∧ (∀ a ∈ D, Injective (fderiv ℝ g a)) ∧ ∀ a ∈ D, π (g a - c) = a := by
  intro P d r N W V ψ π c v₀ hr hV hW hψ hinj hψV hprop hv₀ hπψ
  have hψc : ContinuousOn ψ V := hψ.continuousOn
  have hψVWN : ∀ v ∈ V, ψ v ∈ W ∩ N := fun v hv => hψV ▸ mem_image_of_mem ψ hv
  -- Step 1: `φ = π(ψ − c)` is `Cʳ` on `V`, and `Dφ(v₀) = π ∘ Dψ(v₀)` is injective
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv₀ : HasFDerivAt ψ (fderiv ℝ ψ v₀) v₀ :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv₀)).hasFDerivAt
  have hφ : ContDiffOn ℝ r (fun v => π (ψ v - c)) V :=
    π.contDiff.comp_contDiffOn (hψ.sub contDiffOn_const)
  have hDφ : fderiv ℝ (fun v => π (ψ v - c)) v₀ = π ∘L fderiv ℝ ψ v₀ :=
    (π.hasFDerivAt.comp v₀ (hψv₀.sub_const c)).fderiv
  -- Step 2: a `Cʳ` local inverse `χ : D → S` of `φ` with `v₀ ∈ S ⊆ V`; then `χ(D) = S`
  obtain ⟨S, D, χ, hS, hD, hv₀S, hSV, hχ, hχD, hφχ, hχφ⟩ :=
    Submission.codim1_hcp_sc_local_inverse_cr d r (fun v => π (ψ v - c)) V v₀ hr hV hv₀ hφ
      (hDφ ▸ hπψ)
  have hχS : χ '' D = S :=
    Subset.antisymm hχD.image_subset fun z hz => ⟨_, (hχφ z hz).1, (hχφ z hz).2⟩
  -- Step 3: `g = ψ ∘ χ` is `Cʳ` on `D`, `π(g(a) − c) = a` on `D`, and `g(D) = ψ(S)`
  have hg : ContDiffOn ℝ r (ψ ∘ χ) D := hψ.comp hχ (hχD.mono_right hSV)
  have hgπ : ∀ a ∈ D, π ((ψ ∘ χ) a - c) = a := hφχ
  have hgD : (ψ ∘ χ) '' D = ψ '' S := by rw [image_comp, hχS]
  -- Step 4: `ψ(S) = O ∩ N` for the open set `O = W ∩ ⋃_{v ∈ S} B(ψ(v), ρ_v)` (Simon 4.2)
  choose ρ hρ hρS using fun v (hv : v ∈ S) =>
    Submission.dtc_bc_lr_chart_image_nhds P d N W V S ψ v hW hψc hinj hψV hprop hS hSV hv
  set O : Set (Euclid P) := W ∩ ⋃ (v) (hv : v ∈ S), ball (ψ v) (ρ v hv)
  have hO : IsOpen O := hW.inter (isOpen_iUnion fun v => isOpen_iUnion fun hv => isOpen_ball)
  have hψO : ∀ v (hv : v ∈ S), ψ v ∈ O := fun v hv =>
    ⟨(hψVWN v (hSV hv)).1, mem_iUnion₂.2 ⟨v, hv, mem_ball_self (hρ v hv)⟩⟩
  have hSO : ψ '' S = O ∩ N := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨hψO v hv, (hψVWN v (hSV hv)).2⟩
    · rintro x ⟨⟨-, hx⟩, hxN⟩
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 hx
      exact hρS v hv ⟨hxN, hxv⟩
  -- Step 5: `g` and every `Dg(a)` are injective, as `π(· − c)` is a left inverse of `g`
  have hg1 : ContDiffOn ℝ 1 (ψ ∘ χ) D := hg.of_le (by exact_mod_cast hr)
  obtain ⟨hginj, hDg⟩ := Submission.codim1_hcp_sc_left_inverse_immersion P d D (ψ ∘ χ) π c hD
    (hg1.differentiableOn one_ne_zero) hgπ
  refine ⟨D, O, ψ ∘ χ, hD, hO, hψO v₀ hv₀S, inter_subset_left, hg, hginj, hgD.trans hSO,
    fun K hKO hK => ?_, fun a ha => (hDg a ha).2, hgπ⟩
  -- Step 6: `N ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have hKW : K ⊆ W := hKO.trans inter_subset_left
  have hNK : N ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxN, hxK⟩
      obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := hψV ▸ ⟨hKW hxK, hxN⟩
      exact ⟨v, ⟨hv, hxK⟩, rfl⟩
    · rintro _ ⟨v, ⟨hv, hvK⟩, rfl⟩
      exact ⟨(hψVWN v hv).2, hvK⟩
  have hNKc : IsCompact (N ∩ K) := by
    rw [hNK]
    exact (hprop K hKW hK).image_of_continuousOn (hψc.mono inter_subset_left)
  -- Step 7: `D ∩ g⁻¹(K) = p(N ∩ K)` with `p(x) = π(x − c)` continuous, so it is compact
  have hDK : D ∩ (ψ ∘ χ) ⁻¹' K = (fun x => π (x - c)) '' (N ∩ K) := by
    refine Subset.antisymm ?_ ?_
    · rintro a ⟨ha, haK⟩
      have haN : (ψ ∘ χ) a ∈ O ∩ N := hgD.trans hSO ▸ mem_image_of_mem (ψ ∘ χ) ha
      exact ⟨(ψ ∘ χ) a, ⟨haN.2, haK⟩, hgπ a ha⟩
    · rintro _ ⟨x, ⟨hxN, hxK⟩, rfl⟩
      obtain ⟨b, hb, rfl⟩ : x ∈ (ψ ∘ χ) '' D := hgD.trans hSO ▸ ⟨hKO hxK, hxN⟩
      show π ((ψ ∘ χ) b - c) ∈ D ∩ (ψ ∘ χ) ⁻¹' K
      rw [hgπ b hb]
      exact ⟨hb, hxK⟩
  rw [hDK]
  exact hNKc.image (π.continuous.comp (continuous_sub_right c))

/-- **Simon Ch. 2, §4, (4.1)–(4.4)**: a `C¹` local representation `G : D → W₀` of an embedded
`Cʳ` submanifold `M` (`r ≥ 1`; 1:1, proper, `G(D) = W₀ ∩ M`, `DG` injective) which is a graph
over the projection `π`, `π(G(a) − c) = a`, is `Cʳ` on `D`.  At `a₀ ∈ D`, `x₀ = G(a₀)`, take a
`Cʳ` chart `ψ'` of `M` with `ψ'(v₀) = x₀`.  By (4.3), `Dψ'(v₀)(ℝᵈ) = T_{x₀}M = DG(a₀)(ℝᵈ)`, and
`π ∘ DG(a₀) = id`, so `π ∘ Dψ'(v₀)` is injective.  Re-parametrizing `ψ'` over `π` gives a `Cʳ`
graph `g` on an open `U` with `g(U) = O ∩ M`, `x₀ ∈ O` and `π(g(a) − c) = a`; then `a₀ ∈ U`,
`g(a₀) = x₀`.  For `a` in the open set `U ∩ g⁻¹(W₀) ∋ a₀`, `g(a) ∈ W₀ ∩ M = G(D)`, and the
projection identity forces `G(a) = g(a)`, so `G` is `Cʳ` at `a₀`. -/
theorem Submission.codim1_hcp_sc_graph_contDiffOn : ∀ (P d r : ℕ) (M W₀ : Set (Euclid P)) (D : Set (Euclid d)) (G : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), 1 ≤ r → IsEmbeddedSubmanifold r d M → IsOpen D → IsOpen W₀ → ContDiffOn ℝ 1 G D → InjOn G D → G '' D = W₀ ∩ M → (∀ K ⊆ W₀, IsCompact K → IsCompact (D ∩ G ⁻¹' K)) → (∀ a ∈ D, Injective (fderiv ℝ G a)) → (∀ a ∈ D, π (G a - c) = a) → ContDiffOn ℝ r G D := by
  intro P d r M W₀ D G π c hr hM hD hW₀ hG hGinj hGD hGproper hDG hπG a₀ ha₀
  -- it suffices that `G` is `Cʳ` at `a₀ ∈ D`; `x₀ = G(a₀) ∈ W₀ ∩ M`
  refine ContDiffAt.contDiffWithinAt ?_
  have hx₀ : G a₀ ∈ W₀ ∩ M := hGD ▸ mem_image_of_mem G ha₀
  -- a `Cʳ` chart `ψ'` of `M` at `x₀`, with `ψ'(v₀) = x₀`
  obtain ⟨V', W', ψ', hV', hW', hx₀W', hψ', hψ'inj, hψ'V', hψ'proper, hDψ'⟩ := hM (G a₀) hx₀.2
  obtain ⟨v₀, hv₀, hψv₀⟩ : G a₀ ∈ ψ' '' V' := hψ'V' ▸ ⟨hx₀W', hx₀.2⟩
  -- `Dψ'(v₀)(ℝᵈ) = T_{x₀}M = DG(a₀)(ℝᵈ)`, applying (4.3) to `ψ'` (`Cʳ`) and to `G` (`C¹`)
  have hrange : Set.range (fderiv ℝ ψ' v₀) = Set.range (fderiv ℝ G a₀) := by
    rw [← Submission.chart_tangentSpace_eq_range_fderiv P d r M W' V' ψ' v₀ hr hV' hW' hψ'
        hψ'inj hψ'V' hψ'proper hDψ' hv₀, hψv₀,
      Submission.chart_tangentSpace_eq_range_fderiv P d 1 M W₀ D G a₀ le_rfl hD hW₀
        (by exact_mod_cast hG) hGinj hGD hGproper hDG ha₀]
  -- `π ∘ DG(a₀) = id`
  have hπDG : ∀ w, π (fderiv ℝ G a₀ w) = w := fun w => by
    simpa using DFunLike.congr_fun ((Submission.codim1_hcp_sc_left_inverse_immersion P d D G π c
      hD hG.differentiableOn_one hπG).2 a₀ ha₀).1 w
  -- `π ∘ Dψ'(v₀)` is injective: if `π(Dψ'(v₀)u) = 0`, write `Dψ'(v₀)u = DG(a₀)w`; then
  -- `w = π(DG(a₀)w) = 0`, so `Dψ'(v₀)u = 0` and `u = 0`
  have hπDψ' : Injective (π ∘L fderiv ℝ ψ' v₀) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => hDψ' v₀ hv₀ ?_
    obtain ⟨w, hw⟩ : fderiv ℝ ψ' v₀ u ∈ Set.range (fderiv ℝ G a₀) :=
      hrange ▸ Set.mem_range_self u
    have hw0 : w = 0 := by
      rw [← hπDG w, hw]
      simpa using hu
    rw [map_zero, ← hw, hw0, map_zero]
  -- re-parametrize `ψ'` as a `Cʳ` graph `g` over `π` on `U`, with `g(U) = O ∩ M` and `x₀ ∈ O`
  obtain ⟨U, O, g, hU, -, hx₀O, -, hg, -, hgU, -, -, hπg⟩ :=
    Submission.codim1_hcp_sc_graph_reparam P d r M W' V' ψ' π c v₀ hr hV' hW' hψ' hψ'inj hψ'V'
      hψ'proper hv₀ hπDψ'
  -- `x₀ = g(a₁)` with `a₁ ∈ U`, and `a₁ = π(g(a₁) − c) = π(G(a₀) − c) = a₀`
  rw [hψv₀] at hx₀O
  obtain ⟨a₁, ha₁, hga₁⟩ : G a₀ ∈ g '' U := hgU ▸ ⟨hx₀O, hx₀.2⟩
  have ha₁₀ : a₁ = a₀ := by rw [← hπg a₁ ha₁, hga₁, hπG a₀ ha₀]
  rw [ha₁₀] at ha₁ hga₁
  -- `G = g` on the open set `U ∩ g⁻¹(W₀) ∋ a₀`: there `g(a) ∈ W₀ ∩ M = G(D)`, say `g(a) = G(a')`,
  -- and `a' = π(G(a') − c) = π(g(a) − c) = a`
  have hGg : G =ᶠ[𝓝 a₀] g := by
    have hUg : IsOpen (U ∩ g ⁻¹' W₀) := hg.continuousOn.isOpen_inter_preimage hU hW₀
    have ha₀Ug : a₀ ∈ U ∩ g ⁻¹' W₀ := ⟨ha₁, show g a₀ ∈ W₀ from hga₁ ▸ hx₀.1⟩
    filter_upwards [hUg.mem_nhds ha₀Ug] with a ha
    obtain ⟨haU, haW₀⟩ := ha
    have hgaM : g a ∈ O ∩ M := hgU ▸ mem_image_of_mem g haU
    obtain ⟨a', ha', hGa'⟩ : g a ∈ G '' D := hGD ▸ ⟨haW₀, hgaM.2⟩
    have ha'a : a' = a := by rw [← hπG a' ha', hGa', hπg a haU]
    rw [← hGa', ha'a]
  -- `g` is `Cʳ` at `a₀` (`U` is open), and `G = g` near `a₀`
  exact (hg.contDiffAt (hU.mem_nhds ha₁)).congr_of_eventuallyEq hGg

/-- **`C^∞` charts** (Simon Ch. 2, §4, 4.1–4.4): if `M ⊆ ℝᴾ` is an embedded `Cʳ` `m`-dimensional
submanifold for every `r` (the charts may depend on `r`), then every `y ∈ M` has a `C^∞` local
representation.  Take a `C¹` chart `ψ₁` with `ψ₁(v_y) = y` and a continuous linear left inverse
`π` of the injective `Dψ₁(v_y)`.  Re-parametrizing `ψ₁` over `π` gives a `C¹` chart
`G : D → W₀ ∩ M` with `π(G(a) − y) = a`, and such a graph chart of the `C^{n+1}` submanifold `M`
is `C^{n+1}` on `D`.  So `G` is `Cⁿ` on `D` for every `n`, i.e. `C^∞`. -/
theorem Submission.codim1_hcp_smooth_charts : ∀ (P m : ℕ) (M : Set (Euclid P)), (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → ∀ y ∈ M, ∃ (V : Set (Euclid m)) (W : Set (Euclid P)) (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧ (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧ ∀ z ∈ V, Injective (fderiv ℝ ψ z) := by
  intro P m M hM y hy
  -- Step 1: a `C¹` chart `(V₁, W₁, ψ₁)` at `y`, and `v_y ∈ V₁` with `ψ₁(v_y) = y`
  obtain ⟨V₁, W₁, ψ₁, hV₁, hW₁, hyW₁, hψ₁, hinj₁, hψ₁V, hprop₁, hD₁⟩ := hM 1 y hy
  obtain ⟨vy, hvy, hψvy⟩ : y ∈ ψ₁ '' V₁ := hψ₁V ▸ ⟨hyW₁, hy⟩
  -- Step 2: a continuous linear left inverse `π` of the injective `Dψ₁(v_y)`
  obtain ⟨π₀, hπ₀⟩ := (fderiv ℝ ψ₁ vy : Euclid m →ₗ[ℝ] Euclid P).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (hD₁ vy hvy))
  set π : Euclid P →L[ℝ] Euclid m := LinearMap.toContinuousLinearMap π₀
  have hπA : π ∘L fderiv ℝ ψ₁ vy = ContinuousLinearMap.id ℝ (Euclid m) :=
    ContinuousLinearMap.ext fun v => LinearMap.congr_fun hπ₀ v
  have hπ : Injective (π ∘L fderiv ℝ ψ₁ vy) := by
    rw [hπA]
    exact fun a b hab => hab
  -- Step 3: the `C¹` graph chart `G : D → W₀ ∩ M` over `π`, with `π(G(a) − y) = a`
  obtain ⟨D, W₀, G, hD, hW₀, hyW₀, -, hG, hGinj, hGD, hGprop, hDG, hπG⟩ :=
    Submission.codim1_hcp_sc_graph_reparam P m 1 M W₁ V₁ ψ₁ π y vy le_rfl hV₁ hW₁ hψ₁ hinj₁ hψ₁V
      hprop₁ hvy hπ
  -- Step 4: `G` is `C^{n+1}` on `D` for every `n` (`M` is `C^{n+1}`), hence `C^∞`
  have hG1 : ContDiffOn ℝ 1 G D := by exact_mod_cast hG
  have hGsmooth : ContDiffOn ℝ (⊤ : ℕ∞) G D := contDiffOn_infty.2 fun n =>
    (Submission.codim1_hcp_sc_graph_contDiffOn P m (n + 1) M W₀ D G π y (Nat.le_add_left 1 n)
      (hM (n + 1)) hD hW₀ hG1 hGinj hGD hGprop hDG hπG).of_le (by exact_mod_cast Nat.le_succ n)
  exact ⟨D, W₀, G, hD, hW₀, hψvy ▸ hyW₀, hGsmooth, hGinj, hGD, hGprop, hDG⟩
/-- Step 6 of the oriented graph chart (zero-scale limit plane, Simon 7.5.8): the inverse function
theorem with a `C¹` local inverse on an open target (as used in Simon Ch. 2, §4).  If `φ` is `C¹`
on an open `V ∋ z₀` and `Dφ(z₀)` is injective, then `Dφ(z₀)` is invertible, so
`V₁ = V ∩ {z : Dφ(z) invertible}` is an open neighbourhood of `z₀`.  The inverse function theorem
restricted to `V₁` gives `φ : V₀ → O` bijective with inverse `χ`, and `χ` is `C¹` at every
`a ∈ O` because `Dφ(χ(a))` is invertible. -/
theorem Submission.codim1_zsl_gc_local_inverse : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 1 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (χ : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 1 χ O ∧ MapsTo χ O V₀ ∧ (∀ a ∈ O, φ (χ a) = a) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ χ (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  -- `Dφ(z₀)` is invertible (injective endomorphism of a finite-dimensional space)
  let L₀ : Euclid d ≃L[ℝ] Euclid d :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ φ z₀ : Euclid d →L[ℝ] Euclid d) : Euclid d →ₗ[ℝ] Euclid d)
      hinj).toContinuousLinearEquiv
  have hL₀ : (L₀ : Euclid d →L[ℝ] Euclid d) = fderiv ℝ φ z₀ := by
    ext x; rfl
  have hcd : ∀ z ∈ V, ContDiffAt ℝ 1 φ z := fun z hz => hφ.contDiffAt (hV.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV le_rfl
  -- the open set `V₁` where `Dφ` is invertible
  let V₁ : Set (Euclid d) :=
    V ∩ fderiv ℝ φ ⁻¹' range ((↑) : (Euclid d ≃L[ℝ] Euclid d) → Euclid d →L[ℝ] Euclid d)
  have hV₁ : IsOpen V₁ := hcont.isOpen_inter_preimage hV ContinuousLinearEquiv.isOpen
  have hz₀V₁ : z₀ ∈ V₁ := ⟨hz₀, L₀, hL₀⟩
  have hstrict : HasStrictFDerivAt φ (L₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hL₀]
    exact (hcd z₀ hz₀).hasStrictFDerivAt one_ne_zero
  -- the inverse function theorem, restricted to `V₁`
  obtain ⟨e, he, hz₀e, hsrc⟩ : ∃ e : OpenPartialHomeomorph (Euclid d) (Euclid d),
      ⇑e = φ ∧ z₀ ∈ e.source ∧ e.source ⊆ V₁ :=
    ⟨(hstrict.toOpenPartialHomeomorph φ).restrOpen V₁ hV₁, rfl,
      ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀V₁⟩, inter_subset_right⟩
  subst he
  refine ⟨e.source, e.target, e.symm, e.open_source, e.open_target, hz₀e,
    fun z hz => (hsrc hz).1, ?_, e.mapsTo_symm, fun a ha => e.right_inv ha,
    fun z hz => ⟨e.map_source hz, e.left_inv hz⟩⟩
  -- `χ = e.symm` is `C¹` at each `a ∈ O`, since `Dφ(χ(a))` is invertible
  intro a ha
  obtain ⟨hV', L, hL⟩ := hsrc (e.map_target ha)
  have hd : HasFDerivAt e (L : Euclid d →L[ℝ] Euclid d) (e.symm a) := by
    rw [hL]
    exact ((hcd _ hV').differentiableAt one_ne_zero).hasFDerivAt
  exact (e.contDiffAt_symm ha hd (hcd _ hV')).contDiffWithinAt
/-- An embedded `Cʳ` submanifold `M ⊆ ℝᴾ` (Simon Ch. 2, §4, (4.1)) is Borel, and it meets every
small closed ball about one of its points in a compact set.  For a chart `(V, W, ψ)` and a compact
`K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact because `ψ` is proper and continuous on `V`.  With `O`
the union of the chart domains `W`, `M = O ∩ closure M`: a point `p ∈ O ∩ closure M` lies in the
closure of the compact, hence closed, set `M ∩ closedBall p ε`.  So `M` is Borel. -/
theorem Submission.dimred_rpd_embedded_locally_closed : ∀ (P r d : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → MeasurableSet M ∧ ∀ y ∈ M, ∃ ε : ℝ, 0 < ε ∧ IsCompact (M ∩ closedBall y ε) := by
  intro P r d M hM
  -- step 1: for a chart `(V, W, ψ)` at `y` and compact `K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
      ∀ K ⊆ W, IsCompact K → IsCompact (M ∩ K) := by
    intro y hy
    obtain ⟨V, W, ψ, -, hW, hyW, hψ, -, himg, hprop, -⟩ := hM y hy
    refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
    have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨hxM, hxK⟩
        have hx : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, ⟨hv, hxK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have hv' : ψ v ∈ W ∩ M := by rw [← himg]; exact ⟨v, hv, rfl⟩
        exact ⟨hv'.2, hvK⟩
    rw [hEq]
    exact (hprop K hKW hK).image_of_continuousOn (hψ.continuousOn.mono inter_subset_left)
  refine ⟨?_, ?_⟩
  · -- steps 3-5: `O = ⋃_{y ∈ M} W_y` is open and `M = O ∩ closure M`, so `M` is Borel
    choose! Wf hWo hyW hcpt using key
    have hO : IsOpen (⋃ y ∈ M, Wf y) := isOpen_biUnion fun y hy => hWo y hy
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · -- `p ∈ O ∩ closure M` lies in the closure of the compact set `M ∩ closedBall p (r'/2)`
        rintro p ⟨hpO, hpcl⟩
        obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
        obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
        have hcb : closedBall p (r' / 2) ⊆ Wf y :=
          (closedBall_subset_ball (by linarith)).trans hball
        have hC := hcpt y hy (closedBall p (r' / 2)) hcb (isCompact_closedBall p (r' / 2))
        have h1 : p ∈ ball p (r' / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
        have h2 := isOpen_ball.inter_closure h1
        have hsub : ball p (r' / 2) ∩ M ⊆ M ∩ closedBall p (r' / 2) :=
          fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
        have h3 : p ∈ closure (M ∩ closedBall p (r' / 2)) := closure_mono hsub h2
        rw [hC.isClosed.closure_eq] at h3
        exact h3.1
    rw [hMeq]
    exact hO.measurableSet.inter isClosed_closure.measurableSet
  · -- step 2: a closed ball about `y` inside the chart domain `W` meets `M` in a compact set
    intro y hy
    obtain ⟨W, hW, hyW, hcpt⟩ := key y hy
    obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 hW y hyW
    exact ⟨r' / 2, by linarith,
      hcpt _ ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall y _)⟩
/-- **Graph chart of an embedded `C¹` submanifold** (Simon Ch. 2, §4, (4.4)).  Take a chart
`ψ : V → W₀` at `p = ψ(v₀)` and, in place of Simon's coordinate projection, `pr = ‖A‖⁻¹ A*`,
`A = Dψ(v₀)`, so `‖pr‖ ≤ 1` and `pr ∘ A` is injective.  The inverse function theorem for
`Φ = pr(ψ − p)` gives a `C¹` local inverse `χ` near `Φ(v₀) = 0`, and `G = ψ ∘ χ` satisfies
`pr(G(a) − p) = a`.  Continuity of `ψ⁻¹` at `p` and a small radius `r` give `M ∩ W = G(B_r(0))`
for `W = W₀ ∩ B_δ(p) ∩ {z : pr(z − p) ∈ B_r(0)}`; `DG` is bounded on `B̄_r(0)`, so `G` is
Lipschitz on `B_r(0)`.  Differentiating `pr(G(a) − p) = a` gives `pr ∘ DG(a) = id`, and `Dχ(a)`
is invertible, so `T_{G(a)}M = Dψ(χ(a))(ℝᵐ) = DG(a)(ℝᵐ)`. -/
theorem Submission.codim1_hcp_lsa_c1_graph_chart : ∀ (P m : ℕ) (M : Set (Euclid P)) (p : Euclid P), IsEmbeddedSubmanifold 1 m M → p ∈ M → ∃ (pr : Euclid P →L[ℝ] Euclid m) (G : Euclid m → Euclid P) (r : ℝ) (W : Set (Euclid P)) (Λ : NNReal), 0 < r ∧ IsOpen W ∧ p ∈ W ∧ ‖pr‖ ≤ 1 ∧ G 0 = p ∧ ContDiffOn ℝ 1 G (ball 0 r) ∧ LipschitzOnWith Λ G (ball 0 r) ∧ M ∩ W = G '' ball 0 r ∧ (∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a) ∧ (∀ a ∈ ball (0 : Euclid m) r, pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m)) ∧ ∀ a ∈ ball (0 : Euclid m) r, tangentSpace M (G a) = Set.range (fderiv ℝ G a) := by
  intro P m M p hM hp
  -- step 1: a chart `(V, W₀, ψ)` at `p = ψ(v₀)`
  obtain ⟨V, W₀, ψ, hVo, hW₀o, hpW₀, hψc, hψinj, hψV, hproper, hDψinj⟩ := hM p hp
  obtain ⟨v₀, hv₀, hψv₀⟩ : p ∈ ψ '' V := by rw [hψV]; exact ⟨hpW₀, hp⟩
  have hψd : ∀ v ∈ V, HasFDerivAt ψ (fderiv ℝ ψ v) v := fun v hv =>
    ((hψc.contDiffAt (hVo.mem_nhds hv)).differentiableAt one_ne_zero).hasFDerivAt
  -- step 2: the projection `pr = ‖A‖⁻¹ • A*`, `A = Dψ(v₀)`
  set A : Euclid m →L[ℝ] Euclid P := fderiv ℝ ψ v₀ with hA
  set pr : Euclid P →L[ℝ] Euclid m := ‖A‖⁻¹ • ContinuousLinearMap.adjoint A with hprdef
  have hpr : ‖pr‖ ≤ 1 := by
    rw [hprdef, norm_smul, LinearIsometryEquiv.norm_map, norm_inv, norm_norm]
    rcases eq_or_ne ‖A‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hprA : Injective (pr.comp A) := by
    refine (injective_iff_map_eq_zero (pr.comp A)).2 fun h hh => ?_
    have hh' : pr (A h) = 0 := hh
    rcases eq_or_ne ‖A‖ 0 with h0 | h0
    · have hA0 : A = 0 := norm_eq_zero.1 h0
      apply hDψinj v₀ hv₀
      rw [← hA, hA0, map_zero]; rfl
    · have h1 : ContinuousLinearMap.adjoint A (A h) = 0 := by
        have : ‖A‖⁻¹ • ContinuousLinearMap.adjoint A (A h) = 0 := hh'
        exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero h0)
      have h2 : ‖A h‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left, h1,
          inner_zero_left]
      have h3 : A h = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      exact hDψinj v₀ hv₀ (by rw [← hA, h3, map_zero])
  -- step 3: the coordinate map `Φ = pr(ψ − p)` and its local inverse `χ`
  set Φ : Euclid m → Euclid m := fun v => pr (ψ v - p) with hΦ
  have hΦc : ContDiffOn ℝ 1 Φ V := pr.contDiff.comp_contDiffOn (hψc.sub contDiffOn_const)
  have hΦd : ∀ v ∈ V, HasFDerivAt Φ (pr.comp (fderiv ℝ ψ v)) v := fun v hv =>
    pr.hasFDerivAt.comp v ((hψd v hv).sub_const p)
  have hΦinj : Injective (fderiv ℝ Φ v₀) := by rw [(hΦd v₀ hv₀).fderiv]; exact hprA
  obtain ⟨V₀, O, χ, hV₀o, hOo, hv₀V₀, hV₀V, hχc, hχmaps, hΦχ, hχΦ⟩ :=
    Submission.codim1_zsl_gc_local_inverse m Φ V v₀ hVo hv₀ hΦc hΦinj
  -- step 4: the embedding margin `δ`
  obtain ⟨ε, hε, hεV₀⟩ := Metric.isOpen_iff.1 hV₀o v₀ hv₀V₀
  obtain ⟨δ, hδ, hδε⟩ := Submission.dsmc_chart_inverse_continuity P m V W₀ ψ hψc.continuousOn
    hψinj (by rw [hψV]; exact inter_subset_left) hproper v₀ hv₀ ε hε
  have hΦv₀ : Φ v₀ = 0 := by simp [hΦ, hψv₀]
  have h0O : (0 : Euclid m) ∈ O := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).1
  have hχ0 : χ 0 = v₀ := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).2
  -- step 5: the graph map `G = ψ ∘ χ` and the radius `r`
  set G : Euclid m → Euclid P := fun a => ψ (χ a) with hGdef
  have hG0 : G 0 = p := by simp [hGdef, hχ0, hψv₀]
  have hGc : ContDiffOn ℝ 1 G O := hψc.comp hχc fun a ha => hV₀V (hχmaps ha)
  obtain ⟨r₁, hr₁, hr₁O⟩ := Metric.isOpen_iff.1 hOo 0 h0O
  have hGcont0 : ContinuousAt G 0 := hGc.continuousOn.continuousAt (hOo.mem_nhds h0O)
  obtain ⟨r₂, hr₂, hr₂δ⟩ := Metric.mem_nhds_iff.1
    (hGcont0.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds p hδ))
  set r : ℝ := min (r₁ / 2) r₂ with hr
  have hrpos : 0 < r := lt_min (by positivity) hr₂
  have hcbO : closedBall (0 : Euclid m) r ⊆ O :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hr₁O
  have hbO : ball (0 : Euclid m) r ⊆ O := ball_subset_closedBall.trans hcbO
  have hbδ : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ ball p δ := fun a ha =>
    hr₂δ (ball_subset_ball (min_le_right _ _) ha)
  -- the Lipschitz bound on `B_r(0)`: `DG` is bounded on the compact set `B̄_r(0)`
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : Euclid m) r).exists_bound_of_continuousOn
    ((hGc.continuousOn_fderiv_of_isOpen hOo le_rfl).mono hcbO)
  have hGda : ∀ a ∈ O, HasFDerivAt G (fderiv ℝ G a) a := fun a ha =>
    ((hGc.contDiffAt (hOo.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
  have hGL : LipschitzOnWith (Real.toNNReal Cb) G (ball 0 r) := by
    refine (convex_ball (0 : Euclid m) r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun a ha => (hGda a (hbO ha)).differentiableAt) fun a ha => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hCb a (ball_subset_closedBall ha)).trans (Real.le_coe_toNNReal Cb)
  -- step 6: the chart domain `W`
  set W : Set (Euclid P) := W₀ ∩ ball p δ ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r with hW
  have hWo : IsOpen W := (hW₀o.inter isOpen_ball).inter (isOpen_ball.preimage (by fun_prop))
  have hpW : p ∈ W := ⟨⟨hpW₀, mem_ball_self hδ⟩, by simp [hrpos]⟩
  -- step 7: `pr(G(a) − p) = a`
  have hleft : ∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a := fun a ha => hΦχ a (hbO ha)
  -- step 8: `M ∩ W = G(B_r(0))`
  have hMW : M ∩ W = G '' ball 0 r := by
    ext x
    constructor
    · rintro ⟨hxM, ⟨hxW₀, hxδ⟩, hxr⟩
      obtain ⟨v', hv', rfl⟩ : x ∈ ψ '' V := by rw [hψV]; exact ⟨hxW₀, hxM⟩
      have hv'ε : dist v' v₀ < ε := hδε v' hv' (by rw [hψv₀]; exact hxδ)
      have hv'V₀ : v' ∈ V₀ := hεV₀ hv'ε
      refine ⟨Φ v', hxr, ?_⟩
      show ψ (χ (Φ v')) = ψ v'
      rw [(hχΦ v' hv'V₀).2]
    · rintro ⟨a, ha, rfl⟩
      have hχV : χ a ∈ V := hV₀V (hχmaps (hbO ha))
      have hGa : G a ∈ W₀ ∩ M := by rw [← hψV]; exact mem_image_of_mem ψ hχV
      refine ⟨hGa.2, ⟨hGa.1, hbδ a ha⟩, ?_⟩
      show pr (G a - p) ∈ ball 0 r
      rw [hleft a ha]; exact ha
  -- step 9: `pr ∘ DG(a) = id`
  have hderiv : ∀ a ∈ ball (0 : Euclid m) r,
      pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m) := by
    intro a ha
    have h1 : HasFDerivAt (fun b => pr (G b - p)) (pr.comp (fderiv ℝ G a)) a :=
      pr.hasFDerivAt.comp a ((hGda a (hbO ha)).sub_const p)
    have h2 : (fun b => pr (G b - p)) =ᶠ[𝓝 a] fun b => b := by
      filter_upwards [isOpen_ball.mem_nhds ha] with b hb using hleft b hb
    rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
  -- step 10: `T_{G(a)}M = DG(a)(ℝᵐ)`
  have htan : ∀ a ∈ ball (0 : Euclid m) r,
      tangentSpace M (G a) = Set.range (fderiv ℝ G a) := by
    intro a ha
    have haO : a ∈ O := hbO ha
    have hχV : χ a ∈ V := hV₀V (hχmaps haO)
    have hχd : HasFDerivAt χ (fderiv ℝ χ a) a :=
      ((hχc.contDiffAt (hOo.mem_nhds haO)).differentiableAt one_ne_zero).hasFDerivAt
    have hGfd : fderiv ℝ G a = (fderiv ℝ ψ (χ a)).comp (fderiv ℝ χ a) :=
      ((hψd (χ a) hχV).comp a hχd).fderiv
    -- `Dχ(a)` is injective, hence surjective
    have hsurj : Surjective (fderiv ℝ χ a) := by
      have hid : (fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a) = ContinuousLinearMap.id ℝ (Euclid m) := by
        have h1 : HasFDerivAt (fun b => Φ (χ b)) ((fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a)) a :=
          (hΦd (χ a) hχV).differentiableAt.hasFDerivAt.comp a hχd
        have h2 : (fun b => Φ (χ b)) =ᶠ[𝓝 a] fun b => b := by
          filter_upwards [hOo.mem_nhds haO] with b hb using hΦχ b hb
        rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
      have hinj : Injective (fderiv ℝ χ a) := by
        intro u v huv
        have := congrArg (fderiv ℝ Φ (χ a)) huv
        have hu := congrArg (fun L => L u) hid
        have hv := congrArg (fun L => L v) hid
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
        rw [← hu, ← hv]; exact this
      exact (LinearMap.injective_iff_surjective (f := ((fderiv ℝ χ a : Euclid m →L[ℝ] Euclid m) :
        Euclid m →ₗ[ℝ] Euclid m))).1 hinj
    rw [show G a = ψ (χ a) from rfl, Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W₀ V ψ
      (χ a) le_rfl hVo hW₀o hψc hψinj hψV hproper hDψinj hχV, hGfd, ContinuousLinearMap.coe_comp,
      hsurj.range_comp]
  exact ⟨pr, G, r, W, Real.toNNReal Cb, hrpos, hWo, hpW, hpr, hG0, hGc.mono hbO, hGL, hMW, hleft,
    hderiv, htan⟩

/-- Derivatives within a set are unique on the span of its curve tangent vectors (Simon Ch. 2,
§4, p. 55; cf. (4.6)–(4.7)), for an arbitrary set `M ⊆ ℝᴾ`.  If `f` has derivative `f'` within
`M` at `x`, then so does `L = fderivWithin ℝ f M x`, and two derivatives within `M` agree on the
tangent cone of `M` at `x`.  Each `w = γ'(0) ∈ T_xM` lies in that cone: as `t → 0`, `t ≠ 0`,
`γ(t) − x → 0`, `x + (γ(t) − x) = γ(t) ∈ M` and `t⁻¹(γ(t) − x) → w`.  So `L = f'` on `T_xM`,
hence on its linear span. -/
theorem Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span : ∀ (P : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (f' : Euclid P →L[ℝ] ℝ) (x v : Euclid P), HasFDerivWithinAt f f' M x → v ∈ Submodule.span ℝ (tangentSpace M x) → fderivWithin ℝ f M x v = f' v := by
  intro P M f f' x v hf hv
  -- `L = fderivWithin ℝ f M x` and `f'` are both derivatives of `f` within `M` at `x`, so they
  -- agree on the tangent cone of `M` at `x`
  have huniq : EqOn (fderivWithin ℝ f M x) f' (tangentConeAt ℝ M x) :=
    hf.differentiableWithinAt.hasFDerivWithinAt.unique_on hf
  -- the velocity `w = γ'(0)` of a curve `γ` in `M` through `x` lies in the tangent cone:
  -- take `c(t) = t⁻¹` and `d(t) = γ(t) − x` as `t → 0`, `t ≠ 0`
  have hcone : tangentSpace M x ⊆ tangentConeAt ℝ M x := by
    rintro w ⟨γ, -, hγM, hγ0, hγw⟩
    refine mem_tangentConeAt_of_seq (𝓝[≠] (0 : ℝ)) (fun t => t⁻¹) (fun t => γ t - x) ?_ ?_ ?_
    · -- `γ(t) − x → 0`, since `γ` is continuous at `0` and `γ(0) = x`
      rw [tendsto_sub_nhds_zero_iff, ← hγ0]
      exact hγw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · -- `x + (γ(t) − x) = γ(t) ∈ M` for `t ∈ (−1, 1)`
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)]
        with t ht
      rw [add_sub_cancel]
      exact hγM ht
    · -- `t⁻¹(γ(t) − x) = t⁻¹(γ(0 + t) − γ(0)) → γ'(0) = w`
      simpa [hγ0] using hγw.tendsto_slope_zero
  -- `L = f'` on `T_xM`, hence on its linear span
  exact LinearMap.eqOn_span (f := (fderivWithin ℝ f M x : Euclid P →ₗ[ℝ] ℝ))
    (g := (f' : Euclid P →ₗ[ℝ] ℝ)) (fun w hw => huniq (hcone hw)) hv
/-- Hausdorff measure and lower integrals over Lipschitz images (Simon Ch. 2, Theorem 1.8(i)):
if `G : ℝᵐ → ℝᴾ` is `Λ`-Lipschitz on `D`, then `Hᵐ(G(N)) ≤ Λᵐ Lᵐ(N)` for every `N ⊆ D`, measurable
or not, and for Borel `D` and Borel `H ≥ 0`, `∫_{G(D)} H dHᵐ ≤ Λᵐ ∫_D H ∘ G dLᵐ`.  The first
bound is the `μH[m]` estimate for Lipschitz images scaled by the common normalizing constant of
`μHE[m]`, with `μHE[m] = Lᵐ` on `ℝᵐ`.  Applied to `N = G⁻¹(s) ∩ D` it gives
`Hᵐ⌞G(D) ≤ Λᵐ G₊(Lᵐ⌞D)` on Borel sets `s`; integrating `H` against this measure inequality and
changing variables gives the second bound.  Injectivity of `G` is not needed. -/
theorem Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le : ∀ (m P : ℕ) (G : Euclid m → Euclid P) (D : Set (Euclid m)) (Λ : NNReal), LipschitzOnWith Λ G D → (∀ N ⊆ D, μHE[m] (G '' N) ≤ (Λ : ℝ≥0∞) ^ m * volume N) ∧ (MeasurableSet D → ∀ H : Euclid P → ℝ≥0∞, Measurable H → ∫⁻ x in G '' D, H x ∂μHE[m] ≤ (Λ : ℝ≥0∞) ^ m * ∫⁻ a in D, H (G a)) := by
  intro m P G D Λ hG
  -- part (a): `μH[m](G(N)) ≤ Λᵐ μH[m](N)`, scaled by the normalizing constant of `μHE[m]`
  have hset : ∀ N ⊆ D, μHE[m] (G '' N) ≤ (Λ : ℝ≥0∞) ^ m * volume N := by
    intro N hN
    have h := (hG.mono hN).hausdorffMeasure_image_le (d := (m : ℝ)) (Nat.cast_nonneg m)
    rw [ENNReal.rpow_natCast] at h
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m,
      Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc _ ≤ _ := mul_le_mul_right h _
      _ = _ := by ring
  refine ⟨hset, fun hD H hH => ?_⟩
  -- part (b): the measure inequality `Hᵐ⌞G(D) ≤ Λᵐ G₊(Lᵐ⌞D)`, from (a) with `N = G⁻¹(s) ∩ D`
  have hGae : AEMeasurable G (volume.restrict D) := hG.continuousOn.aemeasurable hD
  have hle : μHE[m].restrict (G '' D) ≤ ((Λ : ℝ≥0∞) ^ m) • (volume.restrict D).map G := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.map_apply_of_aemeasurable hGae hs,
      Measure.restrict_apply' hD, smul_eq_mul]
    calc μHE[m] (s ∩ G '' D) ≤ μHE[m] (G '' (G ⁻¹' s ∩ D)) := by
          refine measure_mono ?_
          rintro _ ⟨hy, a, ha, rfl⟩
          exact ⟨a, ⟨hy, ha⟩, rfl⟩
      _ ≤ (Λ : ℝ≥0∞) ^ m * volume (G ⁻¹' s ∩ D) := hset _ inter_subset_right
  -- integrate `H` against the measure inequality and change variables along `G`
  calc ∫⁻ x in G '' D, H x ∂μHE[m] ≤ ∫⁻ x, H x ∂(((Λ : ℝ≥0∞) ^ m) • (volume.restrict D).map G) :=
        lintegral_mono' hle le_rfl
    _ = (Λ : ℝ≥0∞) ^ m * ∫⁻ a in D, H (G a) := by
        rw [lintegral_smul_measure, lintegral_map' hH.aemeasurable hGae, smul_eq_mul]
/-- The tangent projection `x ↦ P_x` of an embedded `C¹` submanifold `M ⊆ ℝᴾ`, `P_x` the
orthogonal projection onto `span T_xM`, is continuous on `M`.  Near `x₀ ∈ M` take a `C¹` graph
chart `G` on `B_r(0) ⊆ ℝᵐ`: `M ∩ W = G(B_r(0))`, `pr(G(a) − x₀) = a`, `pr ∘ DG(a) = id` and
`T_{G(a)}M = DG(a)(ℝᵐ)`.  `A = DG(a)` is injective, so the Gram operator `A*A` is invertible,
and `P_{G(a)} = A(A*A)⁻¹A*` by the orthogonality characterization of the projection.  This is
continuous in `a`, as `DG` is continuous, the adjoint is an isometry and inversion is continuous
at units; composing with `x ↦ pr(x − x₀)` gives continuity on the neighbourhood `M ∩ W` of `x₀`
in `M`. -/
theorem Submission.codim1_hcp_lsa_tangent_projection_continuousOn : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) M := by
  intro P m M hM x₀ hx₀
  -- step 1: a `C¹` graph chart `G` on `B_r(0)` at `x₀`, with `M ∩ W = G(B_r(0))`
  obtain ⟨pr, G, r, W, -, -, hWo, hx₀W, -, -, hGc, -, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M x₀ hM hx₀
  -- step 2: `A(a) = DG(a)` is continuous on `B_r(0)`, and injective since `pr ∘ A(a) = id`
  set A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun a => fderiv ℝ G a
  have hAc : ContinuousOn A (ball 0 r) := hGc.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hAinj : ∀ a ∈ ball (0 : Euclid m) r, Injective (A a) := by
    intro a ha u v huv
    have h1 := congrArg (fun L => L u) (hderiv a ha)
    have h2 := congrArg (fun L => L v) (hderiv a ha)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2]
    exact congrArg pr huv
  -- step 3: the Gram operator `Γ(a) = A(a)* A(a)` is injective, hence a unit of `L(ℝᵐ)`
  set Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) := fun a =>
    (ContinuousLinearMap.adjoint (A a)).comp (A a) with hΓ
  have hΓunit : ∀ a ∈ ball (0 : Euclid m) r, IsUnit (Γ a) := by
    intro a ha
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinj : Injective (Γ a) := by
      intro u v huv
      -- `⟨Γ(a) h, h⟩ = ‖A(a) h‖²` vanishes for `h = u - v`
      have h0 : Γ a (u - v) = 0 := by rw [map_sub, huv, sub_self]
      have h1 : inner ℝ (Γ a (u - v)) (u - v) = ‖A a (u - v)‖ ^ 2 := by
        simp only [hΓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
        exact real_inner_self_eq_norm_sq _
      rw [h0, inner_zero_left] at h1
      have h2 : A a (u - v) = 0 := by
        have : ‖A a (u - v)‖ = 0 := by nlinarith [norm_nonneg (A a (u - v))]
        exact norm_eq_zero.1 this
      exact sub_eq_zero.1 (hAinj a ha (by rw [h2, map_zero]))
    exact ⟨hinj, (LinearMap.injective_iff_surjective
      (f := ((Γ a : Euclid m →L[ℝ] Euclid m) : Euclid m →ₗ[ℝ] Euclid m))).1 hinj⟩
  -- step 4: `P_{G(a)} = Q(a) = A(a) Γ(a)⁻¹ A(a)*`, by the orthogonality characterization
  set Q : Euclid m → (Euclid P →L[ℝ] Euclid P) := fun a =>
    (A a).comp ((Ring.inverse (Γ a)).comp (ContinuousLinearMap.adjoint (A a))) with hQ
  have hQeq : ∀ a ∈ ball (0 : Euclid m) r,
      (Submodule.span ℝ (tangentSpace M (G a))).starProjection = Q a := by
    intro a ha
    -- `T_{G(a)}M = A(a)(ℝᵐ)` is already a linear subspace
    have hspan : Submodule.span ℝ (tangentSpace M (G a)) =
        LinearMap.range ((A a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
      apply le_antisymm
      · rw [Submodule.span_le, htan a ha]
        rintro _ ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro _ ⟨y, rfl⟩
        apply Submodule.subset_span
        rw [htan a ha]
        exact ⟨y, rfl⟩
    have hinvr : Γ a * Ring.inverse (Γ a) = 1 := Ring.mul_inverse_cancel _ (hΓunit a ha)
    ext1 u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hspan]
      exact ⟨_, rfl⟩
    · -- `⟨u − Q(a) u, A(a) h⟩ = ⟨A(a)* u − Γ(a) Γ(a)⁻¹ A(a)* u, h⟩ = 0`
      intro w hw
      rw [hspan] at hw
      obtain ⟨h, rfl⟩ := hw
      simp only [hQ, ContinuousLinearMap.coe_coe]
      rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.adjoint_inner_left]
      have : ContinuousLinearMap.adjoint (A a) ((A a).comp ((Ring.inverse (Γ a)).comp
          (ContinuousLinearMap.adjoint (A a))) u) = ContinuousLinearMap.adjoint (A a) u := by
        have h4 := congrArg
          (fun L : Euclid m →L[ℝ] Euclid m => L (ContinuousLinearMap.adjoint (A a) u)) hinvr
        simpa [hΓ, mul_apply_eq_comp] using h4
      rw [this, sub_self]
  -- step 5: `Q` is continuous on `B_r(0)`: the adjoint is a linear isometry, and inversion is
  -- continuous at every unit
  have hQc : ContinuousOn Q (ball 0 r) := by
    have hadj : ContinuousOn (fun a => ContinuousLinearMap.adjoint (A a)) (ball 0 r) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous
        |>.comp_continuousOn hAc
    have hΓc : ContinuousOn Γ (ball 0 r) := hadj.clm_comp hAc
    have hinv : ContinuousOn (fun a => Ring.inverse (Γ a)) (ball 0 r) := by
      intro a ha
      obtain ⟨u, hu⟩ := hΓunit a ha
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp_continuousWithinAt (hΓc a ha)
    exact hAc.clm_comp (hinv.clm_comp hadj)
  -- step 6: on `M ∩ W`, `x = G(a)` with `a = pr(x − x₀) ∈ B_r(0)`, so `P_x = Q(pr(x − x₀))`
  have hPQ : ∀ x ∈ M ∩ W,
      (Submodule.span ℝ (tangentSpace M x)).starProjection = Q (pr (x - x₀)) := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]
    exact hQeq a ha
  have hcont : ContinuousOn (fun x => Q (pr (x - x₀))) (M ∩ W) := by
    refine hQc.comp (by fun_prop) fun x hx => ?_
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]
    exact ha
  -- step 7: `M ∩ W` is a neighbourhood of `x₀` in `M`
  exact (hcont.congr hPQ x₀ ⟨hx₀, hx₀W⟩).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin M (hWo.mem_nhds hx₀W))

/-- **Mollifying a compactly supported Lipschitz function** (the smoothing step of the Lipschitz
approximation used for Simons' theorem, Simon B.2): if `g : ℝᵐ → ℝ` is `K`-Lipschitz and vanishes
off the compact set `S`, and `δ > 0`, then there are `C^∞` functions `gₖ`, vanishing off the closed
`δ`-neighbourhood of `S`, with `gₖ → g` uniformly and `Dgₖ → Dg` in `L²`.  Take `gₖ = ρₖ ⋆ g` for
normalized bumps `ρₖ ≥ 0` supported in `B_{εₖ}(0)`, `εₖ = δ / (k + 2)`, with
`ρₖ ≤ 2ᵐ / Lᵐ(B̄_{εₖ})`.  Then `|gₖ − g| ≤ K εₖ`, and `Dgₖ = ρₖ ⋆ Dg` by dominated convergence of
difference quotients (`g` is differentiable a.e. by Rademacher), so `Dgₖ → Dg` at every Lebesgue
point of `Dg` (Besicovitch differentiation).  As `|Dgₖ − Dg|² ≤ (2K)²` on the compact
`δ`-neighbourhood of `S` and `= 0` off it, dominated convergence gives the `L²` limit. -/
theorem Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support : ∀ (m : ℕ) (g : Euclid m → ℝ) (K : NNReal) (S : Set (Euclid m)) (δ : ℝ), LipschitzWith K g → IsCompact S → (∀ a, a ∉ S → g a = 0) → 0 < δ → ∃ gs : ℕ → Euclid m → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k)) ∧ (∀ k a, a ∉ Metric.cthickening δ S → gs k a = 0) ∧ TendstoUniformly gs g atTop ∧ Tendsto (fun k => ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0) := by
  intro m g K S δ hg hS hg0 hδ
  classical
  -- the a.e. derivative `F = Dg`
  set F : Euclid m → (Euclid m →L[ℝ] ℝ) := fderiv ℝ g with hFdef
  have hFm : Measurable F := measurable_fderiv ℝ g
  have hFb : ∀ y, ‖F y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hg
  have hF0 : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    have h : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hy] with z hz using hg0 z hz
    rw [hFdef, h.fderiv_eq]; simp
  have hFint : Integrable F := by
    refine Integrable.mono' (g := S.indicator fun _ => (K : ℝ)) ?_ hFm.aestronglyMeasurable ?_
    · exact (integrable_indicator_iff hS.isClosed.measurableSet).2
        (integrableOn_const hS.measure_lt_top.ne)
    · filter_upwards with y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]; exact hFb y
      · rw [indicator_of_notMem hy, hF0 y hy, norm_zero]
  -- radii
  set ε : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hεδ : ∀ k, ε k < δ := fun k => by
    simp only [hεdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ)).div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [hεdef] using h
  -- normalized bumps
  let φ : ℕ → ContDiffBump (0 : Euclid m) := fun k =>
    ⟨ε k / 2, ε k, by linarith [hε k], by linarith [hε k]⟩
  set I : ℕ → ℝ := fun k => ∫ x, (φ k) x with hIdef
  have hφint : ∀ k, Integrable (fun x => (φ k) x) := fun k =>
    (φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport
  -- the volume of balls
  have hvol : ∀ (y : Euclid m) (s : ℝ), 0 ≤ s →
      volume.real (closedBall y s) = s ^ m * volume.real (ball (0 : Euclid m) 1) := by
    intro y s hs
    rw [measureReal_def, Measure.addHaar_closedBall volume y hs, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hc : 0 < volume.real (ball (0 : Euclid m) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hI : ∀ k, volume.real (closedBall (0 : Euclid m) (ε k / 2)) ≤ I k := by
    intro k
    have hle : (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) ≤
        fun x => (φ k) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : Euclid m) (ε k / 2)
      · rw [indicator_of_mem hx]; exact ((φ k).one_of_mem_closedBall hx).ge
      · rw [indicator_of_notMem hx]; exact (φ k).nonneg
    have hint1 : Integrable ((closedBall (0 : Euclid m) (ε k / 2)).indicator fun _ => (1 : ℝ)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc volume.real (closedBall (0 : Euclid m) (ε k / 2))
        = ∫ x, (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) x := by
          rw [integral_indicator measurableSet_closedBall]; simp
      _ ≤ I k := integral_mono hint1 (hφint k) hle
  have hIpos : ∀ k, 0 < I k := fun k =>
    lt_of_lt_of_le (by rw [hvol 0 _ (by linarith [hε k])]; exact mul_pos (pow_pos (by linarith [hε k]) _) hc)
      (hI k)
  set ρ : ℕ → Euclid m → ℝ := fun k x => (I k)⁻¹ * (φ k) x with hρdef
  have hρ0 : ∀ k x, 0 ≤ ρ k x := fun k x => mul_nonneg (inv_nonneg.2 (hIpos k).le) (φ k).nonneg
  have hρint1 : ∀ k, ∫ x, ρ k x = 1 := fun k => by
    have hIk : ∫ x, (φ k) x = I k := rfl
    simp only [hρdef]; rw [integral_const_mul, hIk, inv_mul_cancel₀ (hIpos k).ne']
  have hρsupp : ∀ k, Function.support (ρ k) ⊆ ball 0 (ε k) := fun k =>
    (Function.support_mul_subset_right _ _).trans (φ k).support_eq.subset
  have hρsmooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => contDiff_const.mul (φ k).contDiff
  have hρcs : ∀ k, HasCompactSupport (ρ k) := fun k => (φ k).hasCompactSupport.mul_left
  have hρcont : ∀ k, Continuous (ρ k) := fun k => continuous_const.mul (φ k).continuous
  have hρintg : ∀ k, Integrable (ρ k) := fun k => (hρcont k).integrable_of_hasCompactSupport (hρcs k)
  have hρle : ∀ k x (y : Euclid m), ρ k x ≤ 2 ^ m / volume.real (closedBall y (ε k)) := by
    intro k x y
    have h1 : ρ k x ≤ (I k)⁻¹ := by
      simp only [hρdef]
      calc (I k)⁻¹ * (φ k) x ≤ (I k)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ k).le_one (inv_nonneg.2 (hIpos k).le)
        _ = (I k)⁻¹ := mul_one _
    have hpos2 : 0 < (ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1) :=
      mul_pos (pow_pos (by linarith [hε k]) _) hc
    have h2 : (I k)⁻¹ ≤ ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ := by
      rw [← hvol 0 _ (by linarith [hε k])]
      exact inv_anti₀ (by rw [hvol 0 _ (by linarith [hε k])]; exact hpos2) (hI k)
    have h3 : ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ =
        2 ^ m / volume.real (closedBall y (ε k)) := by
      rw [hvol y _ (hε k).le, div_pow]
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  -- the approximants
  set gs : ℕ → Euclid m → ℝ := fun k => convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hgsdef
  have hgs_apply : ∀ k a, gs k a = ∫ t, ρ k t * g (a - t) := by
    intro k a
    simp only [hgsdef, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hgs_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k) := fun k =>
    (hρcs k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρsmooth k)
      hg.continuous.locallyIntegrable
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hgs_supp : ∀ k a, a ∉ T → gs k a = 0 := by
    intro k a ha
    rw [hgs_apply]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : ρ k t = 0
    · simp [ht]
    · have htb : t ∈ ball (0 : Euclid m) (ε k) := hρsupp k ht
      rw [mem_ball_zero_iff] at htb
      have hS' : a - t ∉ S := by
        intro hmem
        exact ha (Metric.mem_cthickening_of_dist_le a (a - t) δ S hmem
          (by rw [dist_eq_norm, sub_sub_cancel]; linarith [hεδ k]))
      simp [hg0 _ hS']
  refine ⟨gs, hgs_smooth, hgs_supp, ?_, ?_⟩
  · -- uniform convergence
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hK : Tendsto (fun k => (K : ℝ) * ε k) atTop (𝓝 0) := by
      simpa using hεlim.const_mul (K : ℝ)
    filter_upwards [hK.eventually (gt_mem_nhds he)] with k hk a
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ hk
    refine dist_convolution_le (by positivity) (hρsupp k) (hρ0 k) (hρint1 k)
      hg.continuous.aestronglyMeasurable fun x hx => ?_
    calc dist (g x) (g a) ≤ K * dist x a := hg.dist_le_mul x a
      _ ≤ K * ε k := by gcongr; exact (mem_ball.1 hx).le
  · -- the derivative of `gs k` is the mollification of `F`
    have hFae : ∀ a : Euclid m, ∀ᵐ t ∂(volume : Measure (Euclid m)), DifferentiableAt ℝ g (a - t) :=
      fun a => (Measure.measurePreserving_sub_left volume a).quasiMeasurePreserving.ae
        hg.ae_differentiableAt
    have hsl : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall
        fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff]; positivity
    have hderiv : ∀ k a, fderiv ℝ (gs k) a = ∫ t, ρ k t • F (a - t) := by
      intro k a
      have hint : Integrable (fun t => ρ k t • F (a - t)) := by
        refine Integrable.mono' ((hρintg k).mul_const (K : ℝ)) ?_ (Eventually.of_forall fun t => ?_)
        · exact (hρcont k).aestronglyMeasurable.smul
            (hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        · rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
          exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
      ext v
      rw [ContinuousLinearMap.integral_apply hint]
      simp only [_root_.smul_apply, smul_eq_mul]
      set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
      have hspos : ∀ n, 0 < s n := fun n => by positivity
      -- difference quotients of `gs k` along `v`
      have hline : HasDerivAt (fun r : ℝ => gs k (a + r • v)) (fderiv ℝ (gs k) a v) 0 := by
        have h1 : HasDerivAt (fun r : ℝ => a + r • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
        have h2 : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) (a + (0 : ℝ) • v) := by
          rw [zero_smul, add_zero]
          exact ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
        exact h2.comp_hasDerivAt (0 : ℝ) h1
      have hq1 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (fderiv ℝ (gs k) a v)) := by
        have := (hasDerivAt_iff_tendsto_slope_zero.1 hline).comp hsl
        simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      have hgint : ∀ w : Euclid m, Integrable (fun t => ρ k t * g (w - t)) := fun w =>
        ((hρcont k).mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((hρcs k).mul_right)
      have hrepr : ∀ n, (s n)⁻¹ * (gs k (a + s n • v) - gs k a) =
          ∫ t, ρ k t * ((s n)⁻¹ * (g (a - t + s n • v) - g (a - t))) := by
        intro n
        rw [hgs_apply, hgs_apply, ← integral_sub (hgint _) (hgint _), ← integral_const_mul]
        congr 1
        ext t
        rw [show a + s n • v - t = a - t + s n • v by abel]
        ring
      have hq2 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (∫ t, ρ k t * F (a - t) v)) := by
        simp_rw [hrepr]
        refine tendsto_integral_of_dominated_convergence (fun t => ρ k t * (K * ‖v‖)) (fun n => ?_)
          ((hρintg k).mul_const _) (fun n => Eventually.of_forall fun t => ?_) ?_
        · exact ((hρcont k).mul (continuous_const.mul ((hg.continuous.comp
            ((continuous_const.sub continuous_id).add continuous_const)).sub
            (hg.continuous.comp (continuous_const.sub continuous_id))))).aestronglyMeasurable
        · rw [norm_mul, Real.norm_of_nonneg (hρ0 k t)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ0 k t)
          have hL := hg.dist_le_mul (a - t + s n • v) (a - t)
          rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (hspos n).le] at hL
          rw [norm_mul, norm_inv, Real.norm_of_nonneg (hspos n).le, Real.norm_eq_abs]
          calc (s n)⁻¹ * |g (a - t + s n • v) - g (a - t)|
              ≤ (s n)⁻¹ * (K * (s n * ‖v‖)) := by gcongr; exact hL
            _ = K * ‖v‖ := by
                rw [show (s n)⁻¹ * (K * (s n * ‖v‖)) = (s n)⁻¹ * s n * (K * ‖v‖) by ring,
                  inv_mul_cancel₀ (hspos n).ne', one_mul]
        · filter_upwards [hFae a] with t ht
          refine Tendsto.const_mul _ ?_
          have hl : HasDerivAt (fun r : ℝ => g (a - t + r • v)) (F (a - t) v) 0 := by
            have h1 : HasDerivAt (fun r : ℝ => a - t + r • v) v 0 := by
              simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (a - t)
            have h2 : HasFDerivAt g (F (a - t)) (a - t + (0 : ℝ) • v) := by
              rw [zero_smul, add_zero]; exact ht.hasFDerivAt
            exact h2.comp_hasDerivAt (0 : ℝ) h1
          have := (hasDerivAt_iff_tendsto_slope_zero.1 hl).comp hsl
          simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      exact tendsto_nhds_unique hq1 hq2
    -- bounds and support of the derivatives
    have hDgsb : ∀ k a, ‖fderiv ℝ (gs k) a‖ ≤ K := by
      intro k a
      rw [hderiv k a]
      calc ‖∫ t, ρ k t • F (a - t)‖ ≤ ∫ t, ρ k t * K := by
            refine norm_integral_le_of_norm_le ((hρintg k).mul_const _) (Eventually.of_forall fun t => ?_)
            rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
            exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
        _ = K := by rw [integral_mul_const, hρint1 k, one_mul]
    have hDgs0 : ∀ k a, a ∉ T → fderiv ℝ (gs k) a = 0 := by
      intro k a ha
      have h : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds ha] with b hb
        exact hgs_supp k b hb
      rw [h.fderiv_eq]; simp
    -- Lebesgue points: `D gs k → F` a.e.
    have hεlim' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall hε⟩
    have hae : ∀ᵐ a ∂(volume : Measure (Euclid m)), Tendsto (fun k => fderiv ℝ (gs k) a) atTop (𝓝 (F a)) := by
      filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Euclid m))).ae_tendsto_average_norm_sub
        hFint.locallyIntegrable] with a ha
      have havg : Tendsto (fun k => ⨍ y in closedBall a (ε k), ‖F y - F a‖) atTop (𝓝 0) :=
        ha.comp ((Besicovitch.tendsto_filterAt volume a).comp hεlim')
      have hconv := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
        (g := fun k y => ρ k (a - y)) (2 ^ m) havg
        (Eventually.of_forall fun k => hFint.integrableOn)
        (tendsto_const_nhds.congr' (Eventually.of_forall fun k => by
          simp only
          rw [integral_sub_left_eq_self (fun y => ρ k y) volume a, hρint1 k]))
        (Eventually.of_forall fun k y hy => by
          have h := hρsupp k hy
          rw [mem_ball_zero_iff] at h
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact h.le)
        (Eventually.of_forall fun k y => by
          rw [abs_of_nonneg (hρ0 k _)]; exact hρle k _ a)
      refine hconv.congr' (Eventually.of_forall fun k => ?_)
      show _ = fderiv ℝ (gs k) a
      rw [hderiv k a]
      have := integral_sub_left_eq_self (fun t => ρ k t • F (a - t)) volume a
      simp only [sub_sub_cancel] at this
      exact this
    -- dominated convergence in `L²`
    have hTc : IsCompact T := hS.cthickening
    have hkey := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun k a => ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2)) (f := fun _ => 0)
      (T.indicator fun _ => ENNReal.ofReal ((2 * K) ^ 2))
      (fun k => (((measurable_fderiv ℝ (gs k)).sub hFm).norm.pow_const 2).ennreal_ofReal)
      (fun k => Eventually.of_forall fun a => by
        by_cases ha : a ∈ T
        · rw [indicator_of_mem ha]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖fderiv ℝ (gs k) a - F a‖ ≤ 2 * K :=
            (norm_sub_le _ _).trans (by linarith [hDgsb k a, hFb a])
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        · have haS : a ∉ S := fun h => ha (Metric.self_subset_cthickening S h)
          rw [indicator_of_notMem ha]
          show ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2) ≤ 0
          rw [hDgs0 k a ha, hF0 a haS, sub_zero, norm_zero]
          simp)
      (by
        rw [lintegral_indicator_const hTc.isClosed.measurableSet]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTc.measure_lt_top.ne)
      (by
        filter_upwards [hae] with a ha
        have h1 : Tendsto (fun k => ‖fderiv ℝ (gs k) a - F a‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 ha
        have h2 := ENNReal.tendsto_ofReal (h1.pow 2)
        simpa using h2)
    simpa using hkey

/-- **Rademacher's theorem on a `C¹` submanifold** (Simon Ch. 2, 1.4 and §4).  If `M ⊆ ℝᴾ` is an
embedded `C¹` `m`-dimensional submanifold and `ζ` is locally Lipschitz on `M`, then `ζ` is
differentiable within `M` at `Hᵐ`-a.e. point of `M`.  Near `p ∈ M`, a graph chart `G` over
`B_r(0) ⊆ ℝᵐ` with `pr(G(a) − p) = a` is shrunk to `B_{r₁}(0)` so that `ζ ∘ G` is Lipschitz there
and every `x ∈ M ∩ O` is `G(pr(x − p))`, for an open `O ∋ p`.  By Rademacher `ζ ∘ G` is
differentiable off an `Lᵐ`-null set `N`, and `G(N)` is `Hᵐ`-null because `G` is Lipschitz; off
`G(N)`, `ζ` agrees on `M ∩ O` with the differentiable function `(ζ ∘ G)(pr(· − p))`.  Countably
many such `O` cover `M`. -/
theorem Submission.codim1_hcp_lsa_rademacher_on_submanifold : ∀ (P m : ℕ) (M : Set (Euclid P)) (ζ : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M ζ → ∀ᵐ x ∂(μHE[m].restrict M), DifferentiableWithinAt ℝ ζ M x := by
  intro P m M ζ hM hζ
  -- step 1: `M` is Borel
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  -- step 2: near each `p ∈ M`, `ζ` is differentiable within `M` off an `Hᵐ`-null set
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∃ E : Set (Euclid P),
      μHE[m] E = 0 ∧ ∀ x ∈ M ∩ O, x ∉ E → DifferentiableWithinAt ℝ ζ M x := by
    intro p hp
    -- (a) a graph chart `G` of `M ∩ W` over `B_r(0)`, inverted by `z ↦ pr(z − p)`
    obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, -, hG0, hGc, hGL, hMW, hleft, -, -⟩ :=
      Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
    -- (b) `ζ` is `K`-Lipschitz on `t ⊇ M ∩ U`, with `U ∋ p` open
    obtain ⟨K, t, ht, hKt⟩ := hζ hp
    obtain ⟨U, hUo, hpU, hUt⟩ : ∃ U : Set (Euclid P), IsOpen U ∧ p ∈ U ∧ M ∩ U ⊆ t := by
      obtain ⟨U, hUo, hpU, hUt⟩ := mem_nhdsWithin.1 ht
      exact ⟨U, hUo, hpU, fun x hx => hUt ⟨hx.2, hx.1⟩⟩
    -- (c) shrink the chart so that `G(B_{r₁}(0)) ⊆ U`; `O = W ∩ {pr(z − p) ∈ B_{r₁}(0)}`
    obtain ⟨r₁, hr₁, hr₁r, hGU⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r ∧ G '' ball 0 r₁ ⊆ U := by
      have hGcont : ContinuousAt G 0 :=
        hGc.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
      have hpre : G ⁻¹' U ∈ 𝓝 (0 : Euclid m) :=
        hGcont.preimage_mem_nhds (hUo.mem_nhds (by rw [hG0]; exact hpU))
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hpre
      refine ⟨min ε r, lt_min hε hr, min_le_right _ _, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact hεU (ball_subset_ball (min_le_left _ _) ha)
    have hball : ball (0 : Euclid m) r₁ ⊆ ball 0 r := ball_subset_ball hr₁r
    let O : Set (Euclid P) := W ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r₁
    have hOo : IsOpen O := hWo.inter (isOpen_ball.preimage (by fun_prop))
    have hpO : p ∈ O := ⟨hpW, by simp [hr₁]⟩
    -- (d) every `x ∈ M ∩ O` is `G(a)` with `a = pr(x − p) ∈ B_{r₁}(0)`
    have hMO : ∀ x ∈ M ∩ O, pr (x - p) ∈ ball (0 : Euclid m) r₁ ∧ G (pr (x - p)) = x := by
      intro x hx
      have hxW : x ∈ M ∩ W := ⟨hx.1, hx.2.1⟩
      rw [hMW] at hxW
      obtain ⟨a, ha, rfl⟩ := hxW
      have h2 : pr (G a - p) ∈ ball (0 : Euclid m) r₁ := hx.2.2
      rw [hleft a ha] at h2 ⊢
      exact ⟨h2, rfl⟩
    -- (e) `ζ ∘ G` is `KΛ`-Lipschitz on `B_{r₁}(0)`
    have hGM : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M := fun a ha =>
      ((hMW.symm ▸ mem_image_of_mem G ha : G a ∈ M ∩ W)).1
    have hgL : LipschitzOnWith (K * Λ) (ζ ∘ G) (ball 0 r₁) :=
      hKt.comp (hGL.mono hball) fun a ha => hUt ⟨hGM a (hball ha), hGU (mem_image_of_mem G ha)⟩
    -- (f) Rademacher: `ζ ∘ G` is differentiable off the `Lᵐ`-null set `N`
    let N : Set (Euclid m) := {a | a ∈ ball (0 : Euclid m) r₁ ∧ ¬ DifferentiableAt ℝ (ζ ∘ G) a}
    have hN : volume N = 0 := by
      have hrad := hgL.ae_differentiableWithinAt_of_mem (μ := volume)
      rw [ae_iff] at hrad
      refine measure_mono_null (fun a ha => ?_) hrad
      simp only [mem_ofPred_eq, not_imp]
      exact ⟨ha.1, fun hd => ha.2 (hd.differentiableAt (isOpen_ball.mem_nhds ha.1))⟩
    refine ⟨O, hOo, hpO, G '' N, ?_, ?_⟩
    · -- (g) `Hᵐ(G(N)) ≤ Λᵐ Lᵐ(N) = 0`
      have h := (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r₁) Λ
        (hGL.mono hball)).1 N (fun a ha => ha.1)
      rw [hN, mul_zero] at h
      exact le_antisymm h zero_le
    · -- (h) off `G(N)`, `ζ` agrees on `M ∩ O` with `(ζ ∘ G)(pr(· − p))`, differentiable at `x`
      intro x hx hxE
      obtain ⟨ha, hGa⟩ := hMO x hx
      have hdiffa : DifferentiableAt ℝ (ζ ∘ G) (pr (x - p)) := by
        by_contra hnd
        exact hxE ⟨pr (x - p), ⟨ha, hnd⟩, hGa⟩
      have hpr' : DifferentiableAt ℝ (fun z : Euclid P => pr (z - p)) x := by fun_prop
      have hf : DifferentiableAt ℝ ((ζ ∘ G) ∘ fun z : Euclid P => pr (z - p)) x :=
        hdiffa.comp x hpr'
      refine hf.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [inter_mem_nhdsWithin M (hOo.mem_nhds hx.2)] with y hy
        simp only [Function.comp_apply, (hMO y ⟨hy.1, hy.2⟩).2]
      · simp only [Function.comp_apply, hGa]
  -- step 3: countably many of the neighbourhoods `O p` cover `M` (second countability)
  choose! O hOo hpO E hE hdiff using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hnull : μHE[m] (⋃ p ∈ T, E p) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun p hp => hE p (hTM hp)
  -- step 4: every point of `M` where `ζ` is not differentiable within `M` lies in `⋃_{p ∈ T} E p`
  rw [ae_restrict_iff' hMmeas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxM, hxnd⟩ := hx
  have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hxM, hpO x hxM⟩
  rw [← hTU] at hxU
  obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
  refine mem_iUnion₂.2 ⟨p, hpT, ?_⟩
  by_contra hxE
  exact hxnd (hdiff p (hTM hpT) x ⟨hxM, hxO⟩ hxE)
/-- **Measurability of the tangential derivative of a Lipschitz function** (Simon Ch. 2, §4; used
in 7.5).  Let `M ⊆ ℝᴾ` be an embedded `C¹` `m`-dimensional submanifold, `ζ` locally Lipschitz on
`M`, and `P_x` the orthogonal projection onto `T_xM`.  Then `x ↦ d^M_xζ ∘ P_x` is `Hᵐ⌞M`-a.e.
strongly measurable.  On a graph chart `G : B_r(0) → M ∩ W` about `p` with `pr(G(a) − p) = a`,
`pr ∘ DG(a) = id` and `T_{G(a)}M = DG(a)(ℝᵐ)`, the map `Ψ(x) = D(ζ ∘ G)(pr(x − p)) ∘ pr ∘ P_x` is
a.e. strongly measurable (`D(ζ ∘ G)` is Borel and `x ↦ P_x` is continuous on `M`).  Where `ζ` is
differentiable within `M` (`Hᵐ`-a.e. on `M`, by Rademacher), the chain rule gives
`D(ζ ∘ G)(a) = d^M_xζ ∘ DG(a)` and `P_xv = DG(a)(pr P_xv)`, so `Ψ(x) = d^M_xζ ∘ P_x`.  Countably
many chart domains cover `M`. -/
theorem Submission.codim1_hcp_lsa_tangential_derivative_aesm : ∀ (P m : ℕ) (M : Set (Euclid P)) (ζ : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M ζ → AEStronglyMeasurable (fun x => (fderivWithin ℝ ζ M x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection) (μHE[m].restrict M) := by
  intro P m M ζ hM hζ
  -- step 1: `M` is Borel, `ζ` is differentiable within `M` a.e. on `M`, `x ↦ P_x` is continuous
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  have hdiff := Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M ζ hM hζ
  have hPc := Submission.codim1_hcp_lsa_tangent_projection_continuousOn P m M hM
  set F : Euclid P → (Euclid P →L[ℝ] ℝ) := fun x =>
    (fderivWithin ℝ ζ M x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection with hF
  -- step 2: `F` is a.e. strongly measurable on `M ∩ W` for a graph-chart domain `W ∋ p`
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧
      AEStronglyMeasurable F (μHE[m].restrict (M ∩ O)) := by
    intro p hp
    obtain ⟨pr, G, r, W, -, -, hWo, hpW, -, -, hGc, -, hMW, hleft, hderiv, htan⟩ :=
      Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
    refine ⟨W, hWo, hpW, ?_⟩
    have hMWm : MeasurableSet (M ∩ W) := hMmeas.inter hWo.measurableSet
    -- (b) the chart representative `Ψ(x) = D(ζ ∘ G)(pr(x − p)) ∘ pr ∘ P_x` is measurable
    set Ψ : Euclid P → (Euclid P →L[ℝ] ℝ) := fun x =>
      (fderiv ℝ (ζ ∘ G) (pr (x - p))).comp
        (pr.comp (Submodule.span ℝ (tangentSpace M x)).starProjection) with hΨ
    have hΨm : AEStronglyMeasurable Ψ (μHE[m].restrict (M ∩ W)) := by
      have h1 : Measurable (fun x : Euclid P => fderiv ℝ (ζ ∘ G) (pr (x - p))) :=
        (measurable_fderiv ℝ (ζ ∘ G)).comp (by fun_prop)
      have h2 : ContinuousOn (fun x => pr.comp (Submodule.span ℝ (tangentSpace M x)).starProjection)
          (M ∩ W) :=
        ((ContinuousLinearMap.compL ℝ (Euclid P) (Euclid P) (Euclid m) pr).continuous
          |>.comp_continuousOn hPc).mono inter_subset_left
      exact isBoundedBilinearMap_comp.continuous.comp_aestronglyMeasurable
        (h1.aestronglyMeasurable.prodMk (h2.aestronglyMeasurable hMWm))
    -- (c) `Ψ = F` at every `x ∈ M ∩ W` where `ζ` is differentiable within `M`
    refine hΨm.congr ?_
    have hdiff' : ∀ᵐ x ∂(μHE[m].restrict (M ∩ W)), DifferentiableWithinAt ℝ ζ M x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hdiff
    filter_upwards [hdiff', ae_restrict_mem hMWm] with x hxd hxMW
    -- `x = G a` with `a = pr (x - p)`
    have hxMW' := hxMW
    rw [hMW] at hxMW'
    obtain ⟨a, ha, rfl⟩ := hxMW'
    simp only [hΨ, hF]
    rw [hleft a ha]
    -- chain rule: `D(ζ ∘ G)(a) = d^M_{G a}ζ ∘ DG(a)`
    have hGM : MapsTo G (ball 0 r) M :=
      fun b hb => (hMW.symm ▸ mem_image_of_mem G hb : G b ∈ M ∩ W).1
    have hGd : HasFDerivAt G (fderiv ℝ G a) a :=
      ((hGc.contDiffAt (isOpen_ball.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
    have hcomp : HasFDerivAt (ζ ∘ G) ((fderivWithin ℝ ζ M (G a)).comp (fderiv ℝ G a)) a :=
      (hxd.hasFDerivWithinAt.comp a hGd.hasFDerivWithinAt hGM).hasFDerivAt
        (isOpen_ball.mem_nhds ha)
    rw [hcomp.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    -- `P_x v ∈ T_{G a}M = DG(a)(ℝᵐ)`, so `P_x v = DG(a) h` and `pr (P_x v) = h`
    have hmem0 := Submodule.starProjection_apply_mem (Submodule.span ℝ (tangentSpace M (G a))) v
    have hle : Submodule.span ℝ (tangentSpace M (G a)) ≤
        LinearMap.range ((fderiv ℝ G a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
      rw [Submodule.span_le, htan a ha]
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have hmem : ∃ h, (fderiv ℝ G a) h =
        (Submodule.span ℝ (tangentSpace M (G a))).starProjection v :=
      LinearMap.mem_range.1 (hle hmem0)
    obtain ⟨h, hh⟩ := hmem
    rw [← hh]
    congr 1
    have := congrArg (fun L => L h) (hderiv a ha)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [this]
  -- step 3: countably many chart domains `O p`, `p ∈ T`, cover `M`
  choose! O hOo hpO hO using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hcount : Countable T := hTc.to_subtype
  have hMU : M = ⋃ i : T, M ∩ O i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hx, hpO x hx⟩
      rw [← hTU] at hxU
      obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
      exact ⟨⟨p, hpT⟩, hx, hxO⟩
    · rintro ⟨i, hx, -⟩
      exact hx
  -- step 4: a.e. strong measurability passes to the countable union
  rw [hMU]
  exact aestronglyMeasurable_iUnion_iff.2 fun i => hO i.1 (hTM i.2)

/-- **Smooth approximation in one graph chart** (Simon Ch. 2, §4, 4.4–4.9; Lipschitz test
functions in App. B, proof of B.2, used for 7.5.8).  `W` is the domain of a `C¹` graph chart at `p`:
`M ∩ W = G(B_r(0))`, `pr(G(a) − p) = a`.  If `ζ` is locally Lipschitz on `M` and vanishes off a
compact `C ⊆ M ∩ W`, then `g = ζ ∘ G` on `B_r(0)` (`0` outside) is Lipschitz and vanishes off
`S = pr(C − p)`.  Mollify `g` to `gₖ`, supported in `T = cthickening δ S`, and put
`ζₖ = β · gₖ ∘ pr(· − p)` with `β` smooth, `= 1` near `C' = G(T)` and `tsupport β ⊆ W`.
`H^m`-a.e. on `M ∩ W` (Rademacher) the tangential error is `(Dgₖ(a) − Dg(a))(pr Pₓeⱼ)`,
`a = pr(x − p)`, whose squares sum to at most `‖Dgₖ(a) − Dg(a)‖²`; off `W` it vanishes.  The
Lipschitz area bound moves the error integral to `B_r(0)`, where it tends to `0`. -/
theorem Submission.codim1_hcp_lsa_local_chart_approx : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → ∀ p ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ p ∈ W ∧ ∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∩ W ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
  classical
  intro P m M hM p hp
  -- step 1: the graph chart at `p`; its domain `W` is the asserted neighbourhood
  obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, hpr, hG0, hGc, hGL, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  refine ⟨W, hWo, hpW, ?_⟩
  rintro ζ hζ ⟨C, hCc, hCMW, hζC⟩
  have hGMW : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M ∩ W := fun a ha => by
    rw [hMW]; exact mem_image_of_mem G ha
  have hrep : ∀ x ∈ M ∩ W, pr (x - p) ∈ ball (0 : Euclid m) r ∧ G (pr (x - p)) = x := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]; exact ⟨ha, rfl⟩
  have hGcont : ContinuousOn G (ball 0 r) := hGc.continuousOn
  -- step 2: the compact parameter sets `S = pr(C − p) ⊆ T = cthickening δ S ⊆ B_r(0)`
  set S : Set (Euclid m) := (fun x => pr (x - p)) '' C with hS
  have hSc : IsCompact S := hCc.image (by fun_prop)
  have hSball : S ⊆ ball 0 r := by
    rintro _ ⟨x, hx, rfl⟩; exact (hrep x (hCMW hx)).1
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := hSc.exists_cthickening_subset_open isOpen_ball hSball
  set δ : ℝ := δ₀ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hTc : IsCompact T := hSc.cthickening
  have hTball : T ⊆ ball 0 r := (Metric.cthickening_mono (by linarith) S).trans hδ₀sub
  have hST : S ⊆ T := Metric.self_subset_cthickening S
  -- step 3: the coordinate function `g = ζ ∘ G` on `B_r(0)`, `0` outside; `g = 0` off `S`
  set g : Euclid m → ℝ := fun a => if a ∈ ball (0 : Euclid m) r then ζ (G a) else 0 with hg
  have hg_ball : ∀ a ∈ ball (0 : Euclid m) r, g a = ζ (G a) := fun a ha => ite_eq_left ha
  have hg0 : ∀ a, a ∉ S → g a = 0 := by
    intro a ha
    by_cases hab : a ∈ ball (0 : Euclid m) r
    · rw [hg_ball a hab]
      refine hζC (G a) (hGMW a hab).1 fun hGC => ha ?_
      exact ⟨G a, hGC, hleft a hab⟩
    · exact ite_eq_right hab
  -- (b) `ζ ∘ G` is locally Lipschitz on the ball, hence Lipschitz and bounded on `T`
  have hζG : LocallyLipschitzOn (ball (0 : Euclid m) r) (ζ ∘ G) := by
    intro a ha
    obtain ⟨K, t, ht, hKt⟩ := hζ (hGMW a ha).1
    have ht' : t ∈ 𝓝[G '' ball 0 r] (G a) :=
      nhdsWithin_mono _ (fun y hy => by rw [← hMW] at hy; exact hy.1) ht
    refine ⟨K * Λ, G ⁻¹' t ∩ ball 0 r, ?_, ?_⟩
    · exact inter_mem ((hGcont a ha).preimage_mem_nhdsWithin' ht') self_mem_nhdsWithin
    · exact hKt.comp (hGL.mono inter_subset_right) fun b hb => hb.1
  obtain ⟨K₁, hK₁⟩ := (hζG.mono hTball).exists_lipschitzOnWith_of_compact hTc
  obtain ⟨B, hB⟩ := hTc.exists_bound_of_continuousOn (hK₁.continuousOn)
  -- (c) `g` is globally Lipschitz with constant `max(K₁, B/δ)`
  have hgLip : LipschitzWith (max K₁ (Real.toNNReal (B / δ))) g := by
    have hgT : ∀ a ∈ T, g a = ζ (G a) := fun a ha => hg_ball a (hTball ha)
    have hfar : ∀ a b, a ∈ S → b ∉ T →
        dist (g a) (g b) ≤ max K₁ (Real.toNNReal (B / δ)) * dist a b := by
      intro a b ha hb
      have hgb : g b = 0 := hg0 b fun h => hb (hST h)
      have hdist : δ < dist a b := by
        by_contra hle
        exact hb (Metric.mem_cthickening_of_dist_le b a δ S ha (by rw [dist_comm]; linarith))
      rw [hgb, dist_zero_right]
      have hBa : ‖g a‖ ≤ B := by rw [hgT a (hST ha)]; exact hB a (hST ha)
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hBa
      calc ‖g a‖ ≤ B := hBa
        _ ≤ B / δ * dist a b := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
            exact mul_le_mul_of_nonneg_left hdist.le hB0
        _ ≤ (Real.toNNReal (B / δ) : ℝ) * dist a b :=
            mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
        _ ≤ (max K₁ (Real.toNNReal (B / δ)) : ℝ) * dist a b := by
            gcongr; exact le_max_right _ _
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [hgT a ha, hgT b hb]
      calc dist (ζ (G a)) (ζ (G b)) ≤ K₁ * dist a b := hK₁.dist_le_mul a ha b hb
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · by_cases haS : a ∈ S
      · exact hfar a b haS hb
      · rw [hg0 a haS, hg0 b fun h => hb (hST h), dist_self]; positivity
    · by_cases hbS : b ∈ S
      · rw [dist_comm, dist_comm a b]; exact hfar b a hbS ha
      · rw [hg0 a fun h => ha (hST h), hg0 b hbS, dist_self]; positivity
    · rw [hg0 a fun h => ha (hST h), hg0 b fun h => hb (hST h), dist_self]; positivity
  -- step 4: mollification
  obtain ⟨gs, hgs_smooth, hgs_supp, hgs_unif, hgs_L2⟩ :=
    Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support m g _ S δ hgLip hSc hg0 hδpos
  -- step 5: the cutoff `β`, smooth, `= 1` near `K' = G(T)`, `tsupport β ⊆ W`
  set K' : Set (Euclid P) := G '' T with hK'
  have hK'c : IsCompact K' := hTc.image_of_continuousOn (hGcont.mono hTball)
  have hK'MW : K' ⊆ M ∩ W := by rintro _ ⟨a, ha, rfl⟩; exact hGMW a (hTball ha)
  obtain ⟨ε, hε, hεW⟩ := hK'c.exists_cthickening_subset_open hWo fun x hx => (hK'MW hx).2
  obtain ⟨β, hβs, hβr, hβsupp, hβ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (Metric.isOpen_thickening (δ := ε) (E := K'))
    (Metric.isClosed_cthickening (δ := ε / 2) (E := K'))
    (Metric.cthickening_subset_thickening' hε (by linarith) K')
  have htsβ : tsupport β ⊆ Metric.cthickening ε K' := by
    rw [tsupport, hβsupp]; exact Metric.closure_thickening_subset_cthickening ε K'
  have hβcs : HasCompactSupport β :=
    hK'c.cthickening.of_isClosed_subset (isClosed_tsupport β) htsβ
  have hβ0 : ∀ x, x ∉ W → x ∉ tsupport β := fun x hx h => hx (hεW (htsβ h))
  have hβone : ∀ x ∈ Metric.thickening (ε / 2) K', β x = 1 := fun x hx =>
    (hβ1 x).1 (Metric.thickening_subset_cthickening _ _ hx)
  have hK'thick : K' ⊆ Metric.thickening (ε / 2) K' :=
    Metric.self_subset_thickening (by positivity) K'
  have hprc : ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclid P => pr (z - p)) := by fun_prop
  -- step 6: the approximants `ζₖ = β · gₖ ∘ pr(· − p)` and `C' = K'`
  refine ⟨K', fun k z => β z * gs k (pr (z - p)), hK'c, fun x hx => (hK'MW hx).1,
    fun k => ⟨hβs.mul ((hgs_smooth k).comp hprc), hβcs.mul_right⟩, ?_, ?_, ?_⟩
  · -- step 7: `ζₖ = 0` on `M \ K'`
    intro k x hxM hxK
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have haT : pr (x - p) ∉ T := fun h => hxK ⟨_, h, hGa⟩
      simp only [hgs_supp k _ haT, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul]
  · -- step 8: uniform convergence on `M`, read off in chart coordinates
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    filter_upwards [Metric.tendstoUniformly_iff.1 hgs_unif ε' hε'] with k hk x hxM
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have hζx : ζ x = g (pr (x - p)) := by rw [hg_ball _ ha, hGa]
      by_cases haT : pr (x - p) ∈ T
      · rw [hβone x (hK'thick ⟨_, haT, hGa⟩), one_mul, hζx]; exact hk _
      · rw [hgs_supp k _ haT, mul_zero, hζx, hg0 _ fun h => haT (hST h), dist_self]; exact hε'
    · rw [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul,
        hζC x hxM fun h => hxW (hCMW h).2, dist_self]
      exact hε'
  · -- steps 9–11: the tangential gradient error
    set w : Euclid P → Fin P → Euclid P := fun x j =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1) with hw
    -- step 9: `∑ⱼ λ(pr(Pₓeⱼ))² ≤ ‖λ‖²`, via the Riesz vector of `λ ∘ pr ∘ Pₓ`
    have halg : ∀ (l : Euclid m →L[ℝ] ℝ) (x : Euclid P),
        ∑ j : Fin P, (l (pr (w x j))) ^ 2 ≤ ‖l‖ ^ 2 := by
      intro l x
      set ℓ : Euclid P →L[ℝ] ℝ :=
        (l.comp pr).comp (Submodule.span ℝ (tangentSpace M x)).starProjection
      set u : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm ℓ
      have hu : ∀ v, ℓ v = inner ℝ u v := fun v => (InnerProductSpace.toDual_symm_apply).symm
      have hcoord : ∀ j : Fin P, l (pr (w x j)) = u j := by
        intro j
        have := hu (EuclideanSpace.single j 1)
        rw [EuclideanSpace.inner_single_right] at this
        simpa [ℓ, w] using this
      have hnorm : ‖u‖ = ‖ℓ‖ := LinearIsometryEquiv.norm_map _ _
      have hℓ : ‖ℓ‖ ≤ ‖l‖ := by
        calc ‖ℓ‖ ≤ ‖l.comp pr‖ * ‖(Submodule.span ℝ (tangentSpace M x)).starProjection‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (‖l‖ * ‖pr‖) * 1 := by
              gcongr
              · exact ContinuousLinearMap.opNorm_comp_le _ _
              · exact Submodule.starProjection_norm_le _
          _ ≤ ‖l‖ * 1 * 1 := by gcongr
          _ = ‖l‖ := by ring
      calc ∑ j : Fin P, (l (pr (w x j))) ^ 2 = ∑ j : Fin P, (u j) ^ 2 := by simp_rw [hcoord]
        _ = ‖u‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq u).symm
        _ ≤ ‖l‖ ^ 2 := by rw [hnorm]; gcongr
    -- the Borel chart majorant `Hₖ(z) = ‖Dgₖ(pr(z − p)) − Dg(pr(z − p))‖²`
    set H : ℕ → Euclid P → ℝ≥0∞ := fun k z =>
      ENNReal.ofReal (‖fderiv ℝ (gs k) (pr (z - p)) - fderiv ℝ g (pr (z - p))‖ ^ 2) with hH
    have hHm : ∀ k, Measurable (H k) := by
      intro k
      have h1 : Measurable fun z : Euclid P => fderiv ℝ (gs k) (pr (z - p)) :=
        (measurable_fderiv ℝ (gs k)).comp (by fun_prop)
      have h2 : Measurable fun z : Euclid P => fderiv ℝ g (pr (z - p)) :=
        (measurable_fderiv ℝ g).comp (by fun_prop)
      exact ((h1.sub h2).norm.pow_const 2).ennreal_ofReal
    have hζdiff := Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M ζ hM hζ
    -- step 10: the pointwise bound by `1_W · Hₖ`, `H^m`-a.e. on `M`
    have hpt : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
          fderivWithin ℝ ζ M x (w x j)) ^ 2) ≤ W.indicator (H k) x := by
      intro k
      filter_upwards [hζdiff, ae_restrict_mem hMmeas] with x hxd hxM
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW]
        obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
        set a := pr (x - p) with ha_def
        -- (i) `Dg(a) = d^M_xζ ∘ DG(a)`
        have hGd : HasFDerivAt G (fderiv ℝ G a) a :=
          ((hGc.contDiffAt (isOpen_ball.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
        have hGM : MapsTo G (ball 0 r) M := fun b hb => (hGMW b hb).1
        have hcomp : HasFDerivAt (ζ ∘ G) ((fderivWithin ℝ ζ M x).comp (fderiv ℝ G a)) a := by
          have hxd' : HasFDerivWithinAt ζ (fderivWithin ℝ ζ M x) M (G a) := by
            rw [hGa]; exact hxd.hasFDerivWithinAt
          exact (hxd'.comp a hGd.hasFDerivWithinAt hGM).hasFDerivAt (isOpen_ball.mem_nhds ha)
        have hgeq : g =ᶠ[𝓝 a] ζ ∘ G := by
          filter_upwards [isOpen_ball.mem_nhds ha] with b hb
          exact hg_ball b hb
        have hDg : fderiv ℝ g a = (fderivWithin ℝ ζ M x).comp (fderiv ℝ G a) :=
          (hcomp.congr_of_eventuallyEq hgeq).fderiv
        -- (ii) `Dζₖ(x) = Dgₖ(a) ∘ pr`
        have hDζs : fderiv ℝ (fun z => β z * gs k (pr (z - p))) x =
            (fderiv ℝ (gs k) a).comp pr := by
          have hprd : HasFDerivAt (fun z : Euclid P => pr (z - p)) pr x := by
            have h := (pr.hasFDerivAt (x := x - p)).comp x ((hasFDerivAt_id x).sub_const p)
            rw [ContinuousLinearMap.comp_id] at h
            exact h
          by_cases haT : a ∈ T
          · have hxK : x ∈ Metric.thickening (ε / 2) K' := hK'thick ⟨a, haT, hGa⟩
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x]
                fun z => gs k (pr (z - p)) := by
              filter_upwards [Metric.isOpen_thickening.mem_nhds hxK] with z hz
              rw [hβone z hz, one_mul]
            rw [heq.fderiv_eq]
            have hgsd : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) a :=
              ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
            exact (hgsd.comp x hprd).fderiv
          · have hnhds : (fun z : Euclid P => pr (z - p)) ⁻¹' Tᶜ ∈ 𝓝 x :=
              (Metric.isClosed_cthickening.isOpen_compl.preimage (by fun_prop)).mem_nhds haT
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
              filter_upwards [hnhds] with z hz
              rw [hgs_supp k _ hz, mul_zero]
            have hga : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
              filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds haT] with b hb
              exact hgs_supp k b hb
            rw [heq.fderiv_eq, hga.fderiv_eq]
            simp
        -- (iii) `Pₓeⱼ = DG(a)(pr(Pₓeⱼ))`, since `T_xM = range DG(a)` and `pr ∘ DG(a) = id`
        have hwj : ∀ j, fderiv ℝ G a (pr (w x j)) = w x j := by
          intro j
          have hmem0 := Submodule.starProjection_apply_mem (Submodule.span ℝ (tangentSpace M x))
            (EuclideanSpace.single j (1 : ℝ))
          have hle : Submodule.span ℝ (tangentSpace M x) ≤ LinearMap.range
              ((fderiv ℝ G a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
            rw [Submodule.span_le, ← hGa, htan a ha]
            rintro _ ⟨y, rfl⟩
            exact ⟨y, rfl⟩
          obtain ⟨h, hh⟩ := LinearMap.mem_range.1 (hle hmem0)
          have hh' : fderiv ℝ G a h = w x j := hh
          rw [← hh']
          congr 1
          have := congrArg (fun T => T h) (hderiv a ha)
          simpa using this
        -- (iv) the error is `(Dgₖ(a) − Dg(a))(pr(Pₓeⱼ))`; apply step 9
        have herr : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = (fderiv ℝ (gs k) a - fderiv ℝ g a) (pr (w x j)) := by
          intro j
          rw [hDζs, hDg]
          simp only [ContinuousLinearMap.comp_apply, sub_apply, hwj j]
        simp_rw [herr]
        exact ENNReal.ofReal_le_ofReal (halg _ x)
      · rw [indicator_of_notMem hxW]
        -- off `W`: `ζₖ = 0` near `x`, and `ζ` has derivative `0` within `M` at `x`
        have hxC : x ∉ C := fun h => hxW (hCMW h).2
        have hz1 : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 (hβ0 x hxW))] with z hz
          rw [hz, Pi.zero_apply, zero_mul]
        have hz2 : HasFDerivWithinAt ζ (0 : Euclid P →L[ℝ] ℝ) M x := by
          have h0 : HasFDerivWithinAt (fun _ : Euclid P => (0 : ℝ)) (0 : Euclid P →L[ℝ] ℝ) M x :=
            hasFDerivWithinAt_const 0 x M
          refine h0.congr_of_eventuallyEq ?_ (hζC x hxM hxC)
          filter_upwards [inter_mem_nhdsWithin M (hCc.isClosed.isOpen_compl.mem_nhds hxC)]
            with y hy
          exact hζC y hy.1 hy.2
        have hterm : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = 0 := by
          intro j
          rw [hz1.fderiv_eq,
            Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span P M ζ 0 x (w x j) hz2
              (Submodule.starProjection_apply_mem _ _)]
          simp
        have hsum0 : ∑ j : Fin P, (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j)) ^ 2 = 0 := by
          simp only [hterm]; simp
        rw [hsum0, ENNReal.ofReal_zero]
    -- step 11: integrate, transfer to the chart ball, and pass to the limit
    have hint : ∀ k, ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
          fderivWithin ℝ ζ M x (w x j)) ^ 2) ∂μHE[m] ≤ (Λ : ℝ≥0∞) ^ m *
            ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
      intro k
      have hWm : MeasurableSet W := hWo.measurableSet
      calc _ ≤ ∫⁻ x in M, W.indicator (H k) x ∂μHE[m] := lintegral_mono_ae (hpt k)
        _ = ∫⁻ x in G '' ball 0 r, H k x ∂μHE[m] := by
            rw [lintegral_indicator hWm, Measure.restrict_restrict hWm, inter_comm, hMW]
        _ ≤ (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r, H k (G a) :=
            (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r) Λ hGL).2
              measurableSet_ball (H k) (hHm k)
        _ = (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r,
              ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
            congr 1
            refine setLIntegral_congr_fun measurableSet_ball fun a ha => ?_
            simp only [hH, hleft a ha]
        _ ≤ _ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    have hlim : Tendsto (fun k => (Λ : ℝ≥0∞) ^ m *
        ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (Λ : ℝ≥0∞) ^ m) hgs_L2
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hint
/-- **Calculus of locally Lipschitz functions on a `C¹` submanifold** (Simon Ch. 2, 4.4–4.9).
Let `M ⊆ ℝᴾ` be an embedded `C¹` `m`-submanifold and `P_x` the orthogonal projection onto
`span T_xM`.  (i) For `ζ` locally Lipschitz on `M`, `x ↦ d^M_xζ(P_xe_j)` is a.e. strongly
measurable for `Hᵐ⌞M`: evaluate the a.e. strongly measurable operator `d^M_xζ ∘ P_x` at `e_j`.
(ii) If moreover `ζ = 0` on `M` off a compact `C ⊆ M`, cover `C` by finitely many open sets
`W_p ∩ B₁(p)`, `p ∈ C`, where `W_p` carries one-chart approximations, and split `ζ = Σᵢ χᵢζ` on
`M` by a smooth partition of unity `χᵢ` on `C` subordinate to this cover.  Each piece `χᵢζ` is
locally Lipschitz on `M` and vanishes on `M` off the compact `C ∩ spt χᵢ`, so it has approximants
`ζ_{i,k}`; put `ζ_k = Σᵢ ζ_{i,k}`.  At `Hᵐ`-a.e. `x ∈ M` every piece is differentiable within `M`,
so `d^M_xζ = Σᵢ d^M_x(χᵢζ)` on `span T_xM`, and Cauchy–Schwarz over the pieces bounds the
gradient error of `ζ_k` by `#pieces` times the sum of the (a.e. measurable) errors of the pieces,
each of which tends to `0`. -/
theorem Submission.codim1_hcp_lipschitz_smooth_approx : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → (∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
  intro P m M hM
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  -- the tangent projections `P_x e_j` are a.e. strongly measurable on `M`
  have hPj : ∀ j : Fin P, AEStronglyMeasurable
      (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection
        (EuclideanSpace.single j (1 : ℝ))) (μHE[m].restrict M) := by
    intro j
    have hc := Submission.codim1_hcp_lsa_tangent_projection_continuousOn P m M hM
    exact ((ContinuousLinearMap.apply ℝ (Euclid P)
      (EuclideanSpace.single j (1 : ℝ))).continuous.comp_continuousOn hc).aestronglyMeasurable
        hMmeas
  -- part (i): evaluate the operator `d^M_xζ ∘ P_x` at `e_j`
  have part_i : ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P,
      AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)))
        (μHE[m].restrict M) := by
    intro ζ hζ j
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ))).continuous.comp_aestronglyMeasurable
        (Submission.codim1_hcp_lsa_tangential_derivative_aesm P m M ζ hM hζ)
  refine ⟨part_i, ?_⟩
  -- part (ii)
  rintro ζ hζ ⟨C, hCc, hCM, hζC⟩
  -- open sets `W p ∋ p` carrying one-chart approximations
  choose! W hWo hpW hWapprox using Submission.codim1_hcp_lsa_local_chart_approx P m M hM
  -- a finite subcover of `C` by the sets `W p ∩ B₁(p)`, `p ∈ C`
  obtain ⟨t, htC, hCt⟩ := hCc.elim_nhds_subcover (fun p => W p ∩ ball p 1) fun p hp =>
    ((hWo p (hCM hp)).inter isOpen_ball).mem_nhds ⟨hpW p (hCM hp), mem_ball_self one_pos⟩
  let ι := {p // p ∈ t}
  let U : ι → Set (Euclid P) := fun i => W i.1 ∩ ball i.1 1
  have hUo : ∀ i, IsOpen (U i) := fun i => (hWo i.1 (hCM (htC i.1 i.2))).inter isOpen_ball
  have hCU : C ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hCt hx)
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  -- a smooth partition of unity `χᵢ = f i` on `C` subordinate to the cover
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hCc.isClosed U hUo hCU
  have hfsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) := fun i =>
    contMDiff_iff_contDiff.1 (f i).contMDiff
  have hfsum : ∀ x ∈ C, ∑ i, f i x = 1 := by
    intro x hx
    rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx
  -- the pieces `ζᵢ = χᵢ ζ`, with `ζ = Σᵢ ζᵢ` on `M`
  let ζi : ι → Euclid P → ℝ := fun i x => f i x * ζ x
  have hζeq : ∀ x ∈ M, ζ x = ∑ i, ζi i x := by
    intro x hx
    by_cases hxC : x ∈ C
    · simp only [ζi, ← Finset.sum_mul, hfsum x hxC, one_mul]
    · simp [ζi, hζC x hx hxC]
  -- each piece is locally Lipschitz on `M`: near `x`, `χᵢ` is Lipschitz with values in `[0, 1]`
  -- and `ζ` is Lipschitz and bounded by `|ζ x| + K`
  have hζiLip : ∀ i, LocallyLipschitzOn M (ζi i) := by
    intro i x hx
    obtain ⟨K, s, hs, hKs⟩ := hζ hx
    obtain ⟨L, u, hu, hLu⟩ := ((hfsmooth i).of_le (by exact_mod_cast le_top)).locallyLipschitz x
    have hxs : x ∈ s := mem_of_mem_nhdsWithin hx hs
    refine ⟨K + Real.toNNReal (|ζ x| + K) * L, s ∩ u ∩ closedBall x 1,
      inter_mem (inter_mem hs (mem_nhdsWithin_of_mem_nhds hu))
        (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x one_pos)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hζyz := hKs.dist_le_mul y hy.1.1 z hz.1.1
    have hfyz := hLu.dist_le_mul y hy.1.2 z hz.1.2
    have hζz : |ζ z| ≤ |ζ x| + K := by
      have h1 := hKs.dist_le_mul z hz.1.1 x hxs
      have h2 : dist z x ≤ 1 := hz.2
      rw [Real.dist_eq] at h1
      have h3 : |ζ z| ≤ |ζ x| + |ζ z - ζ x| := by
        have := abs_add_le (ζ x) (ζ z - ζ x); simpa using this
      nlinarith [abs_nonneg (ζ z - ζ x), NNReal.coe_nonneg K]
    have hfy : |f i y| ≤ 1 := by rw [abs_of_nonneg (f.nonneg i y)]; exact f.le_one i y
    rw [Real.dist_eq] at hζyz hfyz ⊢
    have hkey : f i y * ζ y - f i z * ζ z =
        f i y * (ζ y - ζ z) + ζ z * (f i y - f i z) := by ring
    simp only [ζi]
    rw [hkey]
    have hdist : 0 ≤ dist y z := dist_nonneg
    calc |f i y * (ζ y - ζ z) + ζ z * (f i y - f i z)|
        ≤ |f i y| * |ζ y - ζ z| + |ζ z| * |f i y - f i z| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * (K * dist y z) + (|ζ x| + K) * (L * dist y z) := by gcongr
      _ = ((K + Real.toNNReal (|ζ x| + K) * L : NNReal) : ℝ) * dist y z := by
          rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; ring
  -- one-chart approximations of the pieces
  have happ : ∀ i : ι, ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧
      C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧
      (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs (ζi i) atTop M ∧
      Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection
          (EuclideanSpace.single j 1)) - fderivWithin ℝ (ζi i) M x
          ((Submodule.span ℝ (tangentSpace M x)).starProjection
            (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
    intro i
    refine hWapprox i.1 (hCM (htC i.1 i.2)) (ζi i) (hζiLip i)
      ⟨C ∩ tsupport (f i), hCc.inter_right (isClosed_tsupport _), ?_, ?_⟩
    · -- `C ∩ spt χᵢ ⊆ M ∩ W pᵢ`
      intro x hx
      exact ⟨hCM hx.1, (hf i hx.2).1⟩
    · -- `ζᵢ = 0` on `M` off `C ∩ spt χᵢ`
      intro x hxM hx
      by_cases hxC : x ∈ C
      · have hxt : x ∉ tsupport (f i) := fun h => hx ⟨hxC, h⟩
        simp [ζi, image_eq_zero_of_notMem_tsupport hxt]
      · simp [ζi, hζC x hxM hxC]
  choose C'i ζsi hC'c hC'M hζsi hζsi0 hζsiU hζsiL using happ
  -- `C' = ⋃ᵢ C'ᵢ` and `ζ_k = Σᵢ ζ_{i,k}`
  refine ⟨⋃ i, C'i i, fun k => ∑ i, ζsi i k, isCompact_iUnion hC'c, iUnion_subset hC'M,
    fun k => ⟨?_, HasCompactSupport.finset_sum fun i _ => (hζsi i k).2⟩, ?_, ?_, ?_⟩
  · -- smoothness
    show ContDiff ℝ _ (∑ i, ζsi i k)
    rw [Finset.sum_fn]
    exact ContDiff.sum fun i _ => (hζsi i k).1
  · -- `ζ_k = 0` on `M ∖ C'`
    intro k x hx hxC'
    show (∑ i, ζsi i k) x = 0
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hζsi0 i k x hx fun h => hxC' (mem_iUnion.2 ⟨i, h⟩)
  · -- uniform convergence on `M`
    have hsum : ∀ s : Finset ι, TendstoUniformlyOn (fun k x => ∑ i ∈ s, ζsi i k x)
        (fun x => ∑ i ∈ s, ζi i x) atTop M := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
          Eventually.of_forall fun k x _ => by simpa using hε
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hζsiU a).add ih
    refine ((hsum Finset.univ).congr_right fun x hx => (hζeq x hx).symm).congr ?_
    exact Eventually.of_forall fun k x _ => by simp [Finset.sum_apply]
  · -- convergence of the tangential gradients
    set w : Euclid P → Fin P → Euclid P := fun x j =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)
    have hwmem : ∀ x j, w x j ∈ Submodule.span ℝ (tangentSpace M x) := fun x j =>
      Submodule.starProjection_apply_mem _ _
    -- `Hᵐ`-a.e. on `M` every piece is differentiable within `M`
    have hdiff : ∀ᵐ x ∂(μHE[m].restrict M),
        x ∈ M ∧ ∀ i, DifferentiableWithinAt ℝ (ζi i) M x := by
      have h1 : ∀ i, ∀ᵐ x ∂(μHE[m].restrict M), DifferentiableWithinAt ℝ (ζi i) M x :=
        fun i => Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M (ζi i) hM (hζiLip i)
      filter_upwards [ae_restrict_mem hMmeas, Filter.eventually_all.2 h1] with x hx hx'
      exact ⟨hx, hx'⟩
    -- there `d^M_xζ = Σᵢ d^M_xζᵢ` on `span T_xM`, so the error of `ζ_k` is the sum of the errors
    -- of the pieces
    have hsplit : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ∀ j,
        fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j) =
          ∑ i, (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j)) := by
      intro k
      filter_upwards [hdiff] with x hx j
      obtain ⟨hxM, hxd⟩ := hx
      have hsum : HasFDerivWithinAt (∑ i, ζi i) (∑ i, fderivWithin ℝ (ζi i) M x) M x :=
        HasFDerivWithinAt.sum fun i _ => (hxd i).hasFDerivWithinAt
      have hζd : HasFDerivWithinAt ζ (∑ i, fderivWithin ℝ (ζi i) M x) M x :=
        hsum.congr (fun y hy => by rw [Finset.sum_apply]; exact hζeq y hy)
          (by rw [Finset.sum_apply]; exact hζeq x hxM)
      have hW := Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span P M ζ _ x (w x j)
        hζd (hwmem x j)
      have hD : fderiv ℝ (∑ i, ζsi i k) x = ∑ i, fderiv ℝ (ζsi i k) x :=
        fderiv_sum fun i _ => ((hζsi i k).1.differentiable (by simp)).differentiableAt
      rw [hW, hD, sum_apply, sum_apply, ← Finset.sum_sub_distrib]
    -- the errors of the pieces are a.e. measurable
    set n : ℕ := Fintype.card ι with hn
    let Fi : ι → ℕ → Euclid P → ℝ≥0∞ := fun i k x => ENNReal.ofReal (∑ j : Fin P,
      (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j)) ^ 2)
    have hFi_meas : ∀ i k, AEMeasurable (Fi i k) (μHE[m].restrict M) := by
      intro i k
      refine AEMeasurable.ennreal_ofReal ?_
      refine (Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_).aemeasurable
      have hcont : Continuous (fderiv ℝ (ζsi i k)) := (hζsi i k).1.continuous_fderiv (by simp)
      have h1 : AEStronglyMeasurable (fun x => fderiv ℝ (ζsi i k) x (w x j))
          (μHE[m].restrict M) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hcont.aestronglyMeasurable.prodMk (hPj j))
      exact (h1.sub (part_i (ζi i) (hζiLip i) j)).pow 2
    -- pointwise Cauchy–Schwarz over the pieces
    have hbound : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2) ≤
          (n : ℝ≥0∞) * ∑ i, Fi i k x := by
      intro k
      filter_upwards [hsplit k] with x hx
      have hcs : ∀ j : Fin P,
          (∑ i, (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j))) ^ 2 ≤
            (n : ℝ) * ∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j)) ^ 2 := by
        intro j
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
          (fun i => fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j))
        simpa [hn] using this
      calc ENNReal.ofReal (∑ j : Fin P,
            (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2)
          = ENNReal.ofReal (∑ j : Fin P, (∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j))) ^ 2) := by simp_rw [hx]
        _ ≤ ENNReal.ofReal (∑ j : Fin P, (n : ℝ) * ∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j)) ^ 2) :=
            ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j _ => hcs j)
        _ = (n : ℝ≥0∞) * ∑ i, Fi i k x := by
            rw [← Finset.mul_sum, Finset.sum_comm, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    -- integrate, split the finite sum, and pass to the limit
    have hint : ∀ k, ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2) ∂μHE[m] ≤
          (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m] := by
      intro k
      calc _ ≤ ∫⁻ x in M, (n : ℝ≥0∞) * ∑ i, Fi i k x ∂μHE[m] :=
            lintegral_mono_ae (hbound k)
        _ = (n : ℝ≥0∞) * ∫⁻ x in M, ∑ i, Fi i k x ∂μHE[m] :=
            lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)
        _ = (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m] := by
            rw [lintegral_finsetSum' _ fun i _ => hFi_meas i k]
    have hlim : Tendsto (fun k => (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m])
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (tendsto_finsetSum Finset.univ fun i _ => hζsiL i)
        (Or.inr (ENNReal.natCast_ne_top n))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hint

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

/-- **Tangential derivatives are well defined** (Simon Ch. 2, §4, p. 55; the tangential gradient
of the Simons cone step): for any set `M ⊆ ℝᴾ` and real normed space `E`, if `f : ℝᴾ → E` has
derivative `f'` within `M` at `x`, then `fderivWithin ℝ f M x` agrees with `f'` on the span of
`T_xM`.  `L = fderivWithin ℝ f M x` is itself a derivative of `f` within `M` at `x`, and two
derivatives within `M` agree on the tangent cone of `M` at `x`.  Each `w = γ'(0) ∈ T_xM` lies in
that cone: with `sₙ = 1/(n+2) ∈ (−1, 1)` and `dₙ = γ(sₙ) − x`, `dₙ → 0`, `x + dₙ = γ(sₙ) ∈ M` and
`(n+2) dₙ = sₙ⁻¹(γ(sₙ) − γ(0)) → w`.  So `L = f'` on `T_xM`, hence on its linear span. -/
theorem Submission.codim1_hcp_sc_fderivWithin_tangent_eq : ∀ (P : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Set (Euclid P)) (f : Euclid P → E) (f' : Euclid P →L[ℝ] E) (x : Euclid P), HasFDerivWithinAt f f' M x → ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderivWithin ℝ f M x v = f' v := by
  intro P E _ _ M f f' x hf v hv
  -- steps 2–3: `L = fderivWithin ℝ f M x` and `f'` are both derivatives of `f` within `M` at
  -- `x`, so they agree on the tangent cone of `M` at `x`
  have huniq : EqOn (fderivWithin ℝ f M x) f' (tangentConeAt ℝ M x) :=
    hf.differentiableWithinAt.hasFDerivWithinAt.unique_on hf
  -- step 1: the velocity `w = γ'(0)` of a curve `γ` in `M` through `x` lies in the tangent cone
  have hcone : tangentSpace M x ⊆ tangentConeAt ℝ M x := by
    rintro w ⟨γ, -, hγM, hγ0, hγw⟩
    -- `sₙ = 1/(n+2)` tends to `0` through nonzero values and lies in `(−1, 1)`
    have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop),
        Eventually.of_forall fun n => by simp only [mem_compl_singleton_iff]; positivity⟩
    have hsI : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ∈ Ioo (-1 : ℝ) 1 := fun n => by
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
      refine ⟨by linarith, ?_⟩
      rw [div_lt_one (by positivity)]
      linarith
    -- `cₙ = n + 2` and `dₙ = γ(sₙ) − x`
    refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => (n : ℝ) + 2)
      (fun n => γ (1 / ((n : ℝ) + 2)) - x) ?_ ?_ ?_
    · -- `dₙ → γ(0) − x = 0`, since `γ` is continuous at `0`
      rw [tendsto_sub_nhds_zero_iff, ← hγ0]
      exact hγw.continuousAt.tendsto.comp (hs.mono_right nhdsWithin_le_nhds)
    · -- `x + dₙ = γ(sₙ) ∈ M`, as `sₙ ∈ (−1, 1)`
      refine Eventually.of_forall fun n => ?_
      simp only [add_sub_cancel]
      exact hγM (hsI n)
    · -- `cₙ dₙ = sₙ⁻¹(γ(0 + sₙ) − γ(0)) → γ'(0) = w`
      refine (hγw.tendsto_slope_zero.comp hs).congr fun n => ?_
      simp [hγ0]
  -- step 4: `L = f'` on `T_xM`; the set where the linear maps `L` and `f'` agree is a subspace,
  -- so it contains the linear span of `T_xM`
  exact LinearMap.eqOn_span (f := (fderivWithin ℝ f M x : Euclid P →ₗ[ℝ] E))
    (g := (f' : Euclid P →ₗ[ℝ] E)) (fun w hw => huniq (hcone hw)) hv
/-- **The unit normal of a cone is homogeneous of degree `0`** (Simon, Appendix B, proof of
Lemma B.11, (1)–(2)).  Let `M ⊆ A₀` be an embedded `C¹` `m`-submanifold with `tM ⊆ M` for
`t > 0`, and `ν` a `C^∞` unit normal to `M` in `A₀`.  By
`Submission.codim1_hcp_sc_tangent_normal_complement`, `T_yM = {v ∈ A₀ : ν(y) · v = 0}` is a
linear subspace.  The curve `s ↦ eˢx` gives `x ∈ T_xM`, and scaling curves gives
`tT_xM ⊆ T_{tx}M`, hence `T_{tx}M = T_xM`.  So `ν(tx)` is a unit vector in
`A₀ ∩ (T_xM)^⊥ = ℝν(x)`, i.e. `ν(tx) = ±ν(x)`; `t ↦ ν(x) · ν(tx)` is continuous on `(0, ∞)`
and equals `1` at `t = 1`, so the intermediate value theorem gives `ν(tx) = ν(x)`.
Differentiating `ν(tγ(s)) = ν(γ(s))` at `s = 0` along curves `γ` in `M` gives
`tDν(tx)v = Dν(x)v`, and differentiating the constant map `t ↦ ν(tx)` at `t = 1` gives
`Dν(x)x = 0`. -/
theorem Submission.codim1_hcp_sc_cone_normal_homogeneous : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → IsEmbeddedSubmanifold 1 m M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, x ∈ tangentSpace M x ∧ fderiv ℝ ν x x = 0 ∧ ∀ t : ℝ, 0 < t → tangentSpace M (t • x) = tangentSpace M x ∧ ν (t • x) = ν x ∧ ∀ v ∈ tangentSpace M x, t • fderiv ℝ ν (t • x) v = fderiv ℝ ν x v := by
  intro P m A₀ M ν hdim hMA hM hcone hO hν x hx
  obtain ⟨O, hOo, hMO, hνO⟩ := hO
  -- Step 0: `ν` is differentiable at every point of `M ⊆ O`, and `T_yM = {v ∈ A₀ : ν(y) · v = 0}`
  have hνd : ∀ y ∈ M, HasFDerivAt ν (fderiv ℝ ν y) y := fun y hy =>
    ((hνO.contDiffAt (hOo.mem_nhds (hMO hy))).differentiableAt (by simp)).hasFDerivAt
  have hT : ∀ y ∈ M, tangentSpace M y = {v : Euclid P | v ∈ A₀ ∧ inner ℝ (ν y) v = 0} :=
    fun y hy =>
      (Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hdim hMA hM hν y hy).1
  -- in particular each `T_yM`, `y ∈ M`, is closed under scalar multiplication
  have hTsmul : ∀ y ∈ M, ∀ (c : ℝ) (v : Euclid P), v ∈ tangentSpace M y →
      c • v ∈ tangentSpace M y := by
    intro y hy c v hv
    rw [hT y hy] at hv ⊢
    exact ⟨A₀.smul_mem c hv.1, by rw [real_inner_smul_right, hv.2, mul_zero]⟩
  -- Step 1: `x ∈ T_xM`, via the curve `s ↦ eˢx` in `M`
  have hxT : x ∈ tangentSpace M x := by
    refine ⟨fun s => Real.exp s • x, (Real.contDiff_exp.smul contDiff_const).contDiffOn,
      fun s _ => hcone _ (Real.exp_pos s) x hx, by simp, ?_⟩
    simpa using (Real.hasDerivAt_exp 0).smul_const x
  -- Step 2: `t • T_yM ⊆ T_{ty}M` for `t > 0`: scale the curves
  have hscale : ∀ t : ℝ, 0 < t → ∀ y v : Euclid P, v ∈ tangentSpace M y →
      t • v ∈ tangentSpace M (t • y) := by
    rintro t ht y v ⟨γ, hγ, hγM, hγ0, hγv⟩
    exact ⟨fun s => t • γ s, hγ.const_smul t, fun s hs => hcone t ht _ (hγM hs),
      by simp [hγ0], hγv.const_smul t⟩
  -- Step 3: `T_{ty}M = T_yM` for `y ∈ M` and `t > 0`
  have hTeq : ∀ y ∈ M, ∀ t : ℝ, 0 < t → tangentSpace M (t • y) = tangentSpace M y := by
    intro y hy t ht
    ext w
    constructor
    · intro hw
      have h1 := hscale t⁻¹ (inv_pos.2 ht) (t • y) w hw
      rw [inv_smul_smul₀ ht.ne'] at h1
      have h2 := hTsmul y hy t _ h1
      rwa [smul_inv_smul₀ ht.ne'] at h2
    · intro hw
      have h1 := hscale t ht y _ (hTsmul y hy t⁻¹ w hw)
      rwa [smul_inv_smul₀ ht.ne'] at h1
  -- Step 4: `ν(ty) = λν(y)` with `λ = ν(y) · ν(ty) ∈ {1, −1}`
  have hpm : ∀ y ∈ M, ∀ t : ℝ, 0 < t →
      ν (t • y) = inner ℝ (ν y) (ν (t • y)) • ν y ∧
        (inner ℝ (ν y) (ν (t • y)) = 1 ∨ inner ℝ (ν y) (ν (t • y)) = -1) := by
    intro y hy t ht
    obtain ⟨hνyA, hνy1, -⟩ := hν y hy
    obtain ⟨hνtA, hνt1, hνtT⟩ := hν (t • y) (hcone t ht y hy)
    set lam : ℝ := inner ℝ (ν y) (ν (t • y)) with hlam
    have hyy : inner ℝ (ν y) (ν y) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hνy1, one_pow]
    -- `h = ν(ty) − λν(y) ∈ A₀` is orthogonal to `ν(y)`, so `h ∈ T_yM = T_{ty}M`
    have hhT : ν (t • y) - lam • ν y ∈ tangentSpace M y := by
      rw [hT y hy]
      refine ⟨A₀.sub_mem hνtA (A₀.smul_mem lam hνyA), ?_⟩
      rw [inner_sub_right, real_inner_smul_right, hyy, mul_one, ← hlam, sub_self]
    have e1 : inner ℝ (ν (t • y)) (ν (t • y) - lam • ν y) = (0 : ℝ) :=
      hνtT _ (by rw [hTeq y hy t ht]; exact hhT)
    have e2 : inner ℝ (ν y) (ν (t • y) - lam • ν y) = (0 : ℝ) := by
      rw [hT y hy] at hhT
      exact hhT.2
    -- `|h|² = ν(ty) · h − λ ν(y) · h = 0`
    have hh0 : ν (t • y) - lam • ν y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).1
      rw [inner_sub_left, real_inner_smul_left, e1, e2, mul_zero, sub_zero]
    have hνt : ν (t • y) = lam • ν y := sub_eq_zero.1 hh0
    refine ⟨hνt, (abs_eq zero_le_one).1 ?_⟩
    -- `1 = |ν(ty)| = |λ| |ν(y)| = |λ|`
    have := congrArg norm hνt
    rw [norm_smul, hνt1, hνy1, mul_one, Real.norm_eq_abs] at this
    exact this.symm
  -- Step 5: `ν(ty) = ν(y)` for `y ∈ M` and `t > 0`: `g(s) = ν(y) · ν(sy)` is continuous on
  -- `(0, ∞)` with values in `{1, −1}` and `g(1) = 1`, so `g(t) = −1` contradicts the IVT
  have hhom : ∀ y ∈ M, ∀ t : ℝ, 0 < t → ν (t • y) = ν y := by
    intro y hy t ht
    have hg : ContinuousOn (fun s : ℝ => inner ℝ (ν y) (ν (s • y))) (Ioi 0) :=
      continuousOn_const.inner (hνO.continuousOn.comp
        (continuous_id.smul continuous_const).continuousOn fun s hs => hMO (hcone s hs y hy))
    obtain ⟨hνt, h1 | h1⟩ := hpm y hy t ht
    · rw [hνt, h1, one_smul]
    · exfalso
      have hg1 : inner ℝ (ν y) (ν ((1 : ℝ) • y)) = (1 : ℝ) := by
        rw [one_smul, real_inner_self_eq_norm_sq, (hν y hy).2.1, one_pow]
      obtain ⟨s, hs, hs0⟩ := isPreconnected_Ioi.intermediate_value (show t ∈ Ioi (0 : ℝ) from ht)
        (Set.mem_Ioi.2 one_pos) hg
        (show (0 : ℝ) ∈ Icc (inner ℝ (ν y) (ν (t • y))) (inner ℝ (ν y) (ν ((1 : ℝ) • y))) by
          rw [h1, hg1]
          constructor <;> norm_num)
      have hs0' : inner ℝ (ν y) (ν (s • y)) = (0 : ℝ) := hs0
      rcases (hpm y hy s hs).2 with h2 | h2 <;> linarith
  refine ⟨hxT, ?_, fun t ht => ⟨hTeq x hx t ht, hhom x hx t ht, ?_⟩⟩
  · -- Step 7: `Dν(x)x = 0`: `t ↦ ν(tx)` is constant near `t = 1`, with derivative `Dν(x)x` there
    have h1 : HasDerivAt (fun t : ℝ => ν (t • x)) (fderiv ℝ ν x x) 1 := by
      have hl : HasDerivAt (fun t : ℝ => t • x) x 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
      exact (hνd x hx).comp_hasDerivAt_of_eq 1 hl (one_smul ℝ x).symm
    have h2 : HasDerivAt (fun t : ℝ => ν (t • x)) 0 1 := by
      refine (hasDerivAt_const (1 : ℝ) (ν x)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds one_pos] with t ht using hhom x hx t ht
    exact h1.unique h2
  · -- Step 6: `tDν(tx)v = Dν(x)v`: differentiate `ν(tγ(s)) = ν(γ(s))` at `s = 0`
    rintro v ⟨γ, -, hγM, hγ0, hγv⟩
    have h1 : HasDerivAt (fun s => ν (t • γ s)) (fderiv ℝ ν (t • x) (t • v)) 0 :=
      (hνd (t • x) (hcone t ht x hx)).comp_hasDerivAt_of_eq 0 (hγv.const_smul t) (by simp [hγ0])
    have h2 : HasDerivAt (fun s => ν (t • γ s)) (fderiv ℝ ν x v) 0 := by
      refine ((hνd x hx).comp_hasDerivAt_of_eq 0 hγv hγ0.symm).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with s hs using hhom (γ s) (hγM hs) t ht
    rw [← map_smul]
    exact h1.unique h2

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
