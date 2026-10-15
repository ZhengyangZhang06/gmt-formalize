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

/-- **Lipschitz cut-off adapted to a compact set** (Simon 7.2.4, step 2 of the proof).  If `U` is
open, `K ⊆ U` is compact and `ε > 0`, there is an `L`-Lipschitz `ψ : ℝᴾ → [0, 1]` with `ψ = 1` on
`K` whose positivity set `W₀ = {ψ > 0}` lies in the `ε`-thickening of `K` and satisfies `W₀ ⊂⊂ U`.
For `K = ∅` take `ψ ≡ 0`.  Otherwise choose `δ > 0` with `cthickening δ K ⊆ U`, put
`r = min δ ε` and `ψ = max 0 (1 - dist(·, K) / r)`: it is `1/r`-Lipschitz and
`W₀ = thickening r K`, whose closure lies in the compact `cthickening r K ⊆ cthickening δ K ⊆ U`. -/
theorem Submission.lcmp_exists_lipschitz_cutoff : ∀ (P : ℕ) (U K : Set (Euclid P)) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → 0 < ε → ∃ (ψ : Euclid P → ℝ) (L : NNReal), LipschitzWith L ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ K, ψ x = 1) ∧ {x | 0 < ψ x} ⊆ thickening ε K ∧ CompactlyContained {x | 0 < ψ x} U := by
  intro P U K ε hU hK hKU hε
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · -- Step 1: `K = ∅`; `ψ ≡ 0` and `L = 0`, so `W₀ = ∅`
    have hempty : {x : Euclid P | (0 : ℝ) < (fun _ : Euclid P => (0 : ℝ)) x} = ∅ := by
      ext x
      simp
    refine ⟨fun _ => 0, 0, LipschitzWith.const 0, fun x => ⟨le_rfl, zero_le_one⟩,
      fun x hx => absurd hx (Set.notMem_empty x), ?_, ?_⟩
    · rw [hempty]
      exact empty_subset _
    · rw [hempty]
      exact ⟨by simp, by simp⟩
  -- Step 2: `cthickening δ K ⊆ U`, `r = min δ ε`, `ψ = max 0 (1 - dist(·, K) / r)`, `L = 1/r`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set r : ℝ := min δ ε with hr
  have hr0 : 0 < r := lt_min hδ hε
  set ψ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r) with hψ
  -- Step 3: `dist(·, K)` is `1`-Lipschitz, so `1 - dist(·, K) / r` is `1/r`-Lipschitz, and taking
  -- the maximum with `0` keeps the constant
  have hlip0 : LipschitzWith (Real.toNNReal (1 / r)) fun x : Euclid P => 1 - infDist x K / r := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    have h1 : (1 - infDist x K / r) - (1 - infDist y K / r) = (infDist y K - infDist x K) / r := by
      ring
    have h2 : |infDist x K - infDist y K| ≤ dist x y := by
      have := (lipschitz_infDist_pt K).dist_le_mul x y
      rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
    rw [h1, abs_div, abs_of_pos hr0, Real.coe_toNNReal _ (by positivity), abs_sub_comm]
    calc |infDist x K - infDist y K| / r ≤ dist x y / r := by gcongr
      _ = 1 / r * dist x y := by ring
  have hlip : LipschitzWith (Real.toNNReal (1 / r)) ψ := hlip0.const_max 0
  -- Step 6: `ψ x > 0 ↔ dist(x, K) < r`, i.e. `W₀ = thickening r K` (uses `K ≠ ∅`)
  have hpos : {x | 0 < ψ x} = thickening r K := by
    ext x
    rw [mem_thickening_iff_infDist_lt hKne]
    simp only [hψ, mem_ofPred_eq, lt_max_iff, lt_irrefl, false_or, sub_pos]
    rw [div_lt_one hr0]
  refine ⟨ψ, Real.toNNReal (1 / r), hlip, fun x => ⟨le_max_left _ _, max_le zero_le_one ?_⟩,
    fun x hx => ?_, ?_, ?_⟩
  · -- Step 4: `1 - dist(x, K) / r ≤ 1`, so `0 ≤ ψ ≤ 1`
    have : 0 ≤ infDist x K / r := div_nonneg infDist_nonneg hr0.le
    linarith
  · -- Step 5: `dist(x, K) = 0` on `K`, so `ψ = 1` there
    simp [hψ, infDist_zero_of_mem hx]
  · -- Step 7: `W₀ = thickening r K ⊆ thickening ε K` as `r ≤ ε`
    rw [hpos]
    exact thickening_mono (min_le_right _ _) K
  · -- Step 8: `closure W₀ ⊆ cthickening r K ⊆ cthickening δ K ⊆ U`, and `cthickening r K` is
    -- compact, so its closed subset `closure W₀` is compact
    rw [hpos]
    have hcl : closure (thickening r K) ⊆ cthickening r K :=
      closure_thickening_subset_cthickening r K
    exact ⟨hK.cthickening.of_isClosed_subset isClosed_closure hcl,
      (hcl.trans (cthickening_mono (min_le_left _ _) K)).trans hδU⟩
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
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
/-- **Integrability and zeroth-order bound of the pairing `∫_E ⟨ω, ξ⟩ dμ`** (Simon 6.2.4–6.2.5,
`μ⌞E ∧ ξ` as a current; used for restrictions of currents in the slicing argument of 7.2.4).
If `|⟨α, ξ(x)⟩| ≤ |α|` for every `n`-covector `α` and `μ`-a.e. `x`, and the continuous form
`ω` vanishes off a measurable `K` with `μ(K) < ∞` and `|ω| ≤ ε`, then `|ξ(ω)| ≤ ε 1_K`
`μ`-a.e., so `ξ(ω)` is `μ⌞E`-integrable and `|∫_E ξ(ω) dμ| ≤ ε μ(K ∩ E) ≤ ε μ(K)`. -/
theorem Submission.cmcs_rc_pairing_integrable_abs_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E K : Set (Euclid P)) (ω : DifferentialForm (Euclid P) n) (ε : ℝ), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Continuous ω → MeasurableSet K → μ K < ∞ → (∀ x, x ∉ K → ω x = 0) → (∀ x, covectorEuclideanNorm (ω x) ≤ ε) → Integrable (fun x => ξ x (ω x)) (μ.restrict E) ∧ |∫ x in E, ξ x (ω x) ∂μ| ≤ ε * (μ K).toReal := by
  intro P n μ ξ E K ω ε hξm hξb hω hK hμK hzero hε
  -- Step 1: `ε ≥ 0`
  have hε0 : 0 ≤ ε := (covectorEuclideanNorm_nonneg _).trans (hε 0)
  -- Step 2: `F x = ξ x (ω x)` is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => ξ x (ω x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n)
      (F := ℝ)).continuous.comp_aestronglyMeasurable₂ (g := fun Λ α => Λ α) hξm
      hω.aestronglyMeasurable
  -- Step 3: `‖F x‖ ≤ K.indicator ε x` a.e.
  have hbd : ∀ᵐ x ∂μ, ‖ξ x (ω x)‖ ≤ K.indicator (fun _ => ε) x := by
    filter_upwards [hξb] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]
      exact (hx (ω x)).trans (hε x)
    · rw [indicator_of_notMem hxK, hzero x hxK, map_zero, norm_zero]
  -- Step 4: the dominating function is integrable
  have hg : Integrable (K.indicator (fun _ => ε)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  -- Step 5: integrability of `F`, then on `μ.restrict E`
  have hint : Integrable (fun x => ξ x (ω x)) μ := hg.mono' hmeas hbd
  refine ⟨hint.restrict, ?_⟩
  -- Step 6: `‖∫_E F‖ ≤ ∫_E g = ν.real K * ε`
  have h1 : ‖∫ x in E, ξ x (ω x) ∂μ‖ ≤ ∫ x in E, K.indicator (fun _ => ε) x ∂μ :=
    norm_integral_le_of_norm_le hg.restrict (ae_restrict_of_ae hbd)
  rw [integral_indicator_const ε hK, smul_eq_mul] at h1
  -- Step 7: `ν K = μ (K ∩ E) ≤ μ K`, multiply by `ε ≥ 0`
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  rw [measureReal_def, Measure.restrict_apply hK]
  exact ENNReal.toReal_mono hμK.ne (measure_mono inter_subset_left)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- **Restriction of a measure-represented current** (Simon Ch. 6, 2.9:
`T ⌞ A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`), for an arbitrary pair `(μ, ξ)` and an arbitrary set `E`: if `μ` is
finite on compact subsets of `U` and `ξ` is `μ`-a.e. strongly measurable with
`|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for `μ`-a.e. `x`, then
`ω ↦ ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` is a current in `U`.  By `rsd_mw_tfa_norm_props`, `|α| ≤ C ‖α‖`.
For `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, `cmcs_rc_pairing_integrable_abs_le` then
gives integrability on `μ ⌞ E` and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`.  The functional is linear
(`integral_add`, `integral_const_mul`), and `cmcs_rc_order_zero_current` turns the order-zero
bound into Simon's sequential continuity. -/
theorem Submission.cmcs_restrict_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
  intro P n U μ ξ E hμK hξm hξb
  -- Step 1: `|α| ≤ C ‖α‖` for every `n`-covector `α`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Steps 2 and 4: for `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, the pairing is
  -- `μ ⌞ E`-integrable and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`
  have hpair : ∀ (ω : TestFormOn U n) (K : Set (Euclid P)) (M : ℝ), IsCompact K → K ⊆ U →
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K →
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) ∧
        |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| ≤ C * M * (μ K).toReal := by
    intro ω K M hK hKU hsupp hM
    exact Submission.cmcs_rc_pairing_integrable_abs_le P n μ ξ E K
      (ω : DifferentialForm (Euclid P) n) (C * M) hξm hξb ω.property.1.1.continuous
      hK.measurableSet (hμK K hK hKU)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))
      (fun x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0))
  -- Step 2: every test form is admissible, with `K = tsupport ω` and `M = sup ‖ω‖ < ∞`
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) := by
    intro ω
    obtain ⟨M, hM⟩ := ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
    exact (hpair ω _ M ω.property.1.2 ω.property.2 subset_rfl hM).1
  -- Step 3: `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω₁) (hint ω₂)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Steps 4 and 5: the order-zero bound with `c_K = C μ(K)` makes `L` a current
  obtain ⟨S, hS⟩ := Submission.cmcs_rc_order_zero_current P n U L fun K hK hKU =>
    ⟨C * (μ K).toReal, fun ω M hsupp hM => by
      calc |L ω| = |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| := rfl
        _ ≤ C * M * (μ K).toReal := (hpair ω K M hK hKU hsupp hM).2
        _ = C * (μ K).toReal * M := by ring⟩
  exact ⟨S, hS⟩
/-- **Level splitting of a test form** (a step in the proof of Simon Ch. 6, 4.8,
`spt ⟨T, f, t₊⟩ ⊆ spt T ∩ {f = t}`).  If `tsupport η` misses the level set `{f = t}` of a
continuous `f`, then `η = η₁ + η₂` with test forms `η₁ = χ η` supported in `{f < t}` and
`η₂ = (1 - χ) η` supported in `{t < f}`.  Here `χ` is a smooth Urysohn function equal to `1` on
`K₋ = tsupport η ∩ {f ≤ t}` and to `0` on `K₊ = tsupport η ∩ {t ≤ f}`; these closed sets are
disjoint, with `K₋ ⊆ {f < t}` and `K₊ ⊆ {t < f}`, because `tsupport η` misses `{f = t}`. -/
theorem Submission.cmcs_ss_testForm_level_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (f : Euclid P → ℝ) (t : ℝ) (η : TestFormOn U n), Continuous f → Disjoint (tsupport (η : DifferentialForm (Euclid P) n)) {x | f x = t} → ∃ η₁ η₂ : TestFormOn U n, η = η₁ + η₂ ∧ tsupport (η₁ : DifferentialForm (Euclid P) n) ⊆ {x | f x < t} ∧ tsupport (η₂ : DifferentialForm (Euclid P) n) ⊆ {x | t < f x} := by
  intro P n U f t η hf hη
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := η.property
  set e : DifferentialForm (Euclid P) n := (η : DifferentialForm (Euclid P) n)
  -- the closed halves `K₋ = K ∩ {f ≤ t}` and `K₊ = K ∩ {t ≤ f}` of `K = tsupport η` are
  -- disjoint, since `K` misses `{f = t}`
  have hKl : IsClosed (tsupport e ∩ {x | f x ≤ t}) :=
    (isClosed_tsupport e).inter (isClosed_le hf continuous_const)
  have hKu : IsClosed (tsupport e ∩ {x | t ≤ f x}) :=
    (isClosed_tsupport e).inter (isClosed_le continuous_const hf)
  have hd : Disjoint (tsupport e ∩ {x | t ≤ f x}) (tsupport e ∩ {x | f x ≤ t}) :=
    Set.disjoint_left.2 fun x hxu hxl => Set.disjoint_left.1 hη hxu.1 (le_antisymm hxl.2 hxu.2)
  -- a smooth `χ` with `χ = 0` on `K₊` and `χ = 1` on `K₋`
  obtain ⟨χ, hχ, -, hχ₀, hχ₁⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hKu hKl hd
  -- `χ η` and `(1 - χ) η` are test forms in `U`, with sum `η`
  have h₁ : (fun x => χ x • e x) ∈ TestFormOn U n :=
    ⟨⟨hχ.smul hsmooth, hcpt.smul_left (f := χ)⟩, (tsupport_smul_subset_right χ e).trans hU⟩
  have h₂ : (fun x => (1 - χ x) • e x) ∈ TestFormOn U n :=
    ⟨⟨(contDiff_const.sub hχ).smul hsmooth, hcpt.smul_left (f := fun x => 1 - χ x)⟩,
      (tsupport_smul_subset_right (fun x => 1 - χ x) e).trans hU⟩
  refine ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext (funext fun x => ?_), ?_, ?_⟩
  · change e x = χ x • e x + (1 - χ x) • e x
    rw [← add_smul, add_sub_cancel, one_smul]
  · -- `support (χ η) ⊆ K₋`, a closed subset of `{f < t}`
    have hs : support (fun x => χ x • e x) ⊆ tsupport e ∩ {x | f x ≤ t} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show f x ≤ t from le_of_not_ge fun h => ?_⟩
      exact left_ne_zero_of_smul hx ((hχ₀ x).1 ⟨he, h⟩)
    exact (closure_minimal hs hKl).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h
  · -- `support ((1 - χ) η) ⊆ K₊`, a closed subset of `{t < f}`
    have hs : support (fun x => (1 - χ x) • e x) ⊆ tsupport e ∩ {x | t ≤ f x} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show t ≤ f x from le_of_not_ge fun h => left_ne_zero_of_smul hx ?_⟩
      rw [(hχ₁ x).1 ⟨he, h⟩, sub_self]
    exact (closure_minimal hs hKu).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h.symm
/-- Restriction commutes with the boundary on forms supported in the restricting set (Simon 6.4.6,
used for 4.8): let `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`, and let `A = T⌞S`,
`B = (∂T)⌞S` be given by the same integrals over `S`.  Then `∂A(θ) = B(θ)` whenever
`spt θ ⊆ S`.  Off `S` both `θ` and `dθ` vanish (`spt dθ ⊆ spt θ`), so both integrals over `S`
are integrals over `ℝᴾ`, and `∂A(θ) = A(dθ) = T(dθ) = ∂T(θ) = B(θ)`. -/
theorem Submission.cmcs_ss_boundary_eq_of_tsupport_subset : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, tsupport (θ : DifferentialForm (Euclid P) k) ⊆ S → A.boundary θ = B θ := by
  intro P k U T μ μ' ξ ξ' S A B hT hbT hA hB θ hθ
  -- `θ` and `dθ` vanish off `S`, as `spt dθ ⊆ spt θ ⊆ S`
  have hθ0 : ∀ x, x ∉ S → (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hθ h)
  have hdθ0 : ∀ x, x ∉ S → exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (hθ (tsupport_exteriorDerivative_subset _ h))
  -- so, `ξ x` and `ξ' x` being linear, both integrals over `S` are integrals over `ℝᴾ`
  have hAT : ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ =
      ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hdθ0 x hx, map_zero]
  have hBT : ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' =
      ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hθ0 x hx, map_zero]
  -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ = ∫ ⟨dθ, ξ⟩ dμ = T(dθ) = ∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`
  -- `= ∫_S ⟨θ, ξ'⟩ dμ' = B(θ)`
  calc A.boundary θ = A (exteriorDerivativeTestOn U k θ) := GeometricCurrentOn.boundary_apply A θ
    _ = ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hA _
    _ = ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hAT
    _ = T (exteriorDerivativeTestOn U k θ) := (hT (exteriorDerivativeTestOn U k θ)).symm
    _ = T.boundary θ := (GeometricCurrentOn.boundary_apply T θ).symm
    _ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hbT θ
    _ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hBT.symm
    _ = B θ := (hB θ).symm
/-- Simon Ch. 6, 4.6–4.8 (support of the slice `∂(T⌞S) − (∂T)⌞S`, `S = {f < t}`): if
`A(ω) = ∫_S ⟨ω, ξ⟩ dμ` and `B(θ) = ∫_S ⟨θ, ξ'⟩ dμ'`, then `∂A(θ) = A(dθ) = 0` and `B(θ) = 0`
whenever `spt θ` misses `S`, because `θ` and `dθ` (`spt dθ ⊆ spt θ`) vanish on `S`. -/
theorem Submission.cmcs_ss_boundary_vanish_of_disjoint : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, Disjoint (tsupport (θ : DifferentialForm (Euclid P) k)) S → A.boundary θ = 0 ∧ B θ = 0 := by
  intro P k U μ μ' ξ ξ' S A B hA hB θ hθ
  -- `θ` vanishes on `S`, and so does `dθ`, as `tsupport dθ ⊆ tsupport θ`
  have hθS : ∀ x ∈ S, (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hθ.notMem_of_mem_right hx)
  have hdθS : ∀ x ∈ S, exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' =>
      hθ.notMem_of_mem_right hx (tsupport_exteriorDerivative_subset _ hx')
  refine ⟨?_, ?_⟩
  · -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ`
    rw [GeometricCurrentOn.boundary_apply, hA]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    change ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) = 0
    rw [hdθS x hx, map_zero]
  · rw [hB]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hθS x hx, map_zero]

/-- **Simon Ch. 6, 4.8** (support of a slice): if `T = ξ μ` and `∂T = ξ' μ'` in `U`,
`A = T ⌞ {f < t}` and `B = (∂T) ⌞ {f < t}` (`f` continuous), then `∂A(η) = B(η)` for every
`η ∈ 𝒟ᵏ(U)` whose support misses the level set `{f = t}`; i.e. the slice `∂A − B` lives on
`{f = t}`.  Split `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {f > t}`
(`cmcs_ss_testForm_level_split`).  Below the level `∂A(η₁) = ∂T(η₁) = B(η₁)`
(`cmcs_ss_boundary_eq_of_tsupport_subset`); above it `∂A(η₂) = 0 = B(η₂)`
(`cmcs_ss_boundary_vanish_of_disjoint`), as `{f > t}` misses `{f < t}`.  Conclude by linearity
of `∂A` and `B`. -/
theorem Submission.cmcs_slice_support : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), Continuous f → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ η : TestFormOn U k, Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → A.boundary η = B η := by
  intro P k U T μ μ' ξ ξ' f t A B hf hT hbT hA hB η hη
  -- `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {t < f}`
  obtain ⟨η₁, η₂, rfl, h₁, h₂⟩ := Submission.cmcs_ss_testForm_level_split P k U f t η hf hη
  -- below the level: `∂A(η₁) = ∂T(η₁) = B(η₁)`
  have e₁ : A.boundary η₁ = B η₁ :=
    Submission.cmcs_ss_boundary_eq_of_tsupport_subset P k U T μ μ' ξ ξ' {x | f x < t} A B
      hT hbT hA hB η₁ h₁
  -- above the level: `∂A(η₂) = 0 = B(η₂)`, since `spt η₂ ⊆ {t < f}` misses `{f < t}`
  obtain ⟨e₂, e₂'⟩ := Submission.cmcs_ss_boundary_vanish_of_disjoint P k U μ μ' ξ ξ'
    {x | f x < t} A B hA hB η₂ (Set.disjoint_left.2 fun x hx hx' =>
      lt_asymm (show t < f x from h₂ hx) (show f x < t from hx'))
  -- `∂A` and `B` are linear
  rw [A.boundary.toCurrent.map_add, B.toCurrent.map_add, e₁, e₂, e₂']
/-- Integrability of the pairing `x ↦ ⟨ω(x), ξ(x)⟩`: if `μ` is finite on compact subsets of `U`,
`ξ` is `μ`-a.e. strongly measurable with `|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for
`μ`-a.e. `x`, and `ω ∈ 𝒟ⁿ(U)`, then `x ↦ ⟨ω(x), ξ(x)⟩` is `μ`-integrable.  The coefficient norm
`|ω(x)|` is continuous with compact support, hence bounded by some `M`, so the pairing is
dominated by `M` times the indicator of `spt ω`, which is integrable as `μ(spt ω) < ∞`. -/
theorem Submission.cmcs_smp_pairing_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (ω : TestFormOn U n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ := by
  intro P n U μ ξ ω hμ hξm hξ
  obtain ⟨w, ⟨hws, hwcs⟩, hwU⟩ := ω
  change Integrable (fun x => ξ x (w x)) μ
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous with compact support, hence bounded by some `M`
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  -- `(Λ, α) ↦ Λ α` is continuous, so the pairing is a.e. strongly measurable
  have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hmeas : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    hev.comp_aestronglyMeasurable₂ hξm hwc.aestronglyMeasurable
  -- domination by `M` times the indicator of `spt w`, integrable as `μ(spt w) < ∞`
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    (integrableOn_const (hμ _ hwcs hwU).ne)) hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs]
  by_cases hxK : x ∈ tsupport w
  · rw [indicator_of_mem hxK]
    exact (hx (w x)).trans ((Real.le_norm_self _).trans (hM x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    simp
/-- **Dominated convergence for level cut-offs** (step 5 of the slice mass bound in the proof of
Simon 7.2.4, cut-offs `g_h` of the level set `{f < t}`).  If `F` is `μ`-integrable, `f` is
measurable and, for `0 < h < 1`, `g_h` is a.e. strongly measurable with `|g_h| ≤ C`, `g_h = 1` on
`{f ≤ t − h}` and `g_h = 0` on `{t ≤ f}`, then `∫ g_h F dμ → ∫_{f < t} F dμ` as `h → 0+`.
Along `𝓝[>] 0` eventually `0 < h < 1`, so `|g_h F| ≤ C|F|` (integrable); for each `x`,
`g_h(x)F(x)` is eventually `1_{f<t}(x)F(x)` (for `h < min (t − f x) 1` if `f x < t`, for all
`h ∈ (0, 1)` if `t ≤ f x`); dominated convergence along the countably generated `𝓝[>] 0`. -/
theorem Submission.cmcs_smp_cutoff_integral_tendsto : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F f : Euclid P → ℝ) (t C : ℝ) (g : ℝ → Euclid P → ℝ), Integrable F μ → Measurable f → (∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) μ) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, |g h x| ≤ C) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, f x ≤ t - h → g h x = 1) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, t ≤ f x → g h x = 0) → Tendsto (fun h : ℝ => ∫ x, g h x * F x ∂μ) (𝓝[>] 0) (𝓝 (∫ x in {x | f x < t}, F x ∂μ)) := by
  intro P μ F f t C g hF hf hgm hgC hg1 hg0
  -- Step 2: eventually along `𝓝[>] 0`, `h ∈ (0, 1)`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- Step 1: `{f < t}` is measurable, so the limit is `∫ 1_{f<t} F dμ`
  have hs : MeasurableSet {x | f x < t} := measurableSet_lt hf measurable_const
  rw [← integral_indicator hs]
  -- Step 6: dominated convergence with the integrable bound `C‖F‖`
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖) ?_ ?_ ?_ ?_
  · -- Step 3: `g_h F` is a.e. strongly measurable for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    exact (hgm h hh.1 hh.2).mul hF.aestronglyMeasurable
  · -- Step 4: `|g_h F| ≤ C|F|` for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgC h hh.1 hh.2 x) (norm_nonneg _)
  · exact hF.norm.const_mul C
  · -- Step 5: `g_h(x)F(x)` is eventually equal to `1_{f<t}(x)F(x)`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : f x < t
    · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
      have hpos : 0 < min (t - f x) 1 := lt_min (by linarith) one_pos
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with h hh
      obtain ⟨h0, h1⟩ := hh
      have h1' : h < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have h2 : h < t - f x := lt_of_lt_of_le h1 (min_le_left _ _)
      rw [hg1 h h0 h1' x (by linarith), one_mul]
    · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with h hh
      rw [hg0 h hh.1 hh.2 x (not_lt.1 hx), zero_mul]
/-- **Simon Ch. 6, 4.9** (end of its proof, p. 158, where `b ↓ a` and then `ε ↓ 0`): if
`Φ(h) → z` as `h ↓ 0` and `|Φ(h)| ≤ L / (h (1 − h/2)) · v(h)` for `0 < h < 1`, then
`z ≤ L · liminf_{h ↓ 0} h⁻¹ v(h)` in `[0, ∞]`.  For `r > 1` eventually `(1 − h/2)⁻¹ < r`, so
`|z| = liminf |Φ(h)| ≤ r · L · liminf h⁻¹ v(h)`; then let `r ↓ 1`. -/
theorem Submission.cmcs_smp_liminf_bound : ∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0) := by
  intro L z Φ v hΦ hb
  set X := (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)
  -- step 1: `(0, 1) ∈ 𝓝[>] 0`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- step 2: `ofReal |Φ h| → ofReal |z|`
  have hlimΦ : Tendsto (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |z|)) :=
    ENNReal.tendsto_ofReal hΦ.abs
  -- step 3: `ofReal z ≤ ofReal r * X` for every `r > 1`
  have key : ∀ r : ℝ, 1 < r → ENNReal.ofReal z ≤ ENNReal.ofReal r * X := by
    intro r hr
    -- 3a: `(1 - h / 2)⁻¹ → 1`, so eventually `(1 - h / 2)⁻¹ < r`
    have hcont : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝 0) (𝓝 (1 - 0 / 2)⁻¹) :=
        (tendsto_const_nhds.sub (tendsto_id.div_const 2)).inv₀ (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hevr : ∀ᶠ h in 𝓝[>] (0 : ℝ), (1 - h / 2)⁻¹ < r := hcont.eventually (gt_mem_nhds hr)
    calc ENNReal.ofReal z ≤ ENNReal.ofReal |z| := ENNReal.ofReal_le_ofReal (le_abs_self z)
      _ = liminf (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) := hlimΦ.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)))
            (𝓝[>] 0) := by
          -- 3b, 3c: the eventual pointwise bound and monotonicity of `liminf`
          refine liminf_le_liminf ?_
          filter_upwards [hev, hevr] with h ⟨h0, h1⟩ hhr
          have h2 : 0 < 1 - h / 2 := by linarith
          have heq : (L : ℝ) / (h * (1 - h / 2)) = (1 - h / 2)⁻¹ * ((L : ℝ) * h⁻¹) := by
            field_simp
          calc ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h :=
                hb h h0 h1
            _ = ENNReal.ofReal (1 - h / 2)⁻¹ * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                rw [heq, ENNReal.ofReal_mul (inv_nonneg.2 h2.le),
                  ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
                ring
            _ ≤ ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                gcongr
      _ = ENNReal.ofReal r * X := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  -- step 4: let `r ↓ 1`
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have htend : Tendsto (fun r : ℝ => ENNReal.ofReal r * X) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * X)) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds) (Or.inr hXtop)
    simpa using ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun r hr => key r hr)
/-- Strip estimate (Simon Ch. 6, 4.11: the bound for the right side `R` of 4.11): if `‖Dg‖ ≤ c`,
`Dg` vanishes off `S`, `spt η ⊆ W` and `|η| ≤ 1`, then `∫⁻ ‖Dg‖ |η| dμ ≤ c μ(W ∩ S)`.  The
integrand is dominated by `c 𝟙_{W ∩ S}`: on `W \ S` it vanishes because `Dg = 0`, off `W` because
`η = 0`.  No measurability is needed, as `∫⁻ c 𝟙_A dμ ≤ c μ(A)` for every set `A`. -/
theorem Submission.cmcs_smp_strip_lintegral_le : ∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S) := by
  intro P k μ g η W S c hc hS hW hη
  -- the integrand is dominated by the indicator of `W ∩ S` with value `ofReal c`
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_indicator_const_le (W ∩ S) (ENNReal.ofReal c))
  show ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ≤
    (W ∩ S).indicator (fun _ => ENNReal.ofReal c) x
  by_cases hx : x ∈ W ∩ S
  · rw [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal
      ((mul_le_of_le_one_right (norm_nonneg _) (hη x)).trans (hc x))
  · rw [indicator_of_notMem hx]
    -- off `W ∩ S` a factor vanishes: `Dg(x) = 0` on `W \ S` and `η(x) = 0` off `W`
    have h0 : ‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x) = 0 := by
      by_cases hxW : x ∈ W
      · obtain hD | hD := eq_or_ne (fderiv ℝ g x) 0
        · rw [hD, norm_zero, zero_mul]
        · exact absurd ⟨hxW, hS x hD⟩ hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxW (hW h)
        rw [hηx, covectorEuclideanNorm_zero, mul_zero]
    rw [h0, ENNReal.ofReal_zero]
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
/-- **Orthonormal basis adapted to a linear functional** (used for the wedge-norm bound
`|β ∧ γ| ≤ ‖β‖ |γ|`, Simon 6.1): for a continuous linear functional `β` on `ℝᴾ` and `i₀ : Fin P`
there is an orthonormal basis `f` of `ℝᴾ` with `β(f_{i₀}) = ‖β‖` and `β(f_i) = 0` for `i ≠ i₀`.
Write `β = ⟨b, ·⟩` (Riesz, `‖b‖ = ‖β‖`).  If `b = 0`, the standard basis `e` works.  Otherwise the
reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ`, `u = ‖b‖⁻¹ b`, maps `e_{i₀}` to `u`, and `f = R ∘ e` has
`β(f_i) = ‖b‖ ⟨R e_{i₀}, R e_i⟩ = ‖b‖ ⟨e_{i₀}, e_i⟩`. -/
theorem Submission.cmcs_wn_adapted_orthonormalBasis : ∀ (P : ℕ) (β : Euclid P →L[ℝ] ℝ) (i₀ : Fin P), ∃ f : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, β (f i) = if i = i₀ then ‖β‖ else 0 := by
  intro P β i₀
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Riesz representative: `β x = ⟪b, x⟫` and `‖b‖ = ‖β‖`
  set b : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm β with hb
  have hβb : ∀ x, β x = inner ℝ b x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hnorm : ‖b‖ = ‖β‖ := by
    rw [hb, LinearIsometryEquiv.norm_map]
  by_cases hb0 : b = 0
  · -- `β = 0`: the standard basis works
    refine ⟨e, fun i => ?_⟩
    have h0 : ‖β‖ = 0 := by rw [← hnorm, hb0, norm_zero]
    rw [hβb, hb0, inner_zero_left, h0, ite_self]
  · -- `u = ‖b‖⁻¹ b` is a unit vector and `b = ‖b‖ u`
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    set u : Euclid P := ‖b‖⁻¹ • b with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
    have hbu : b = ‖b‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
    -- the reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ` maps `e_{i₀}` to `u`
    have he : ‖e i₀‖ = 1 := e.orthonormal.1 i₀
    set R := (ℝ ∙ (e i₀ - u))ᗮ.reflection
    have hR : R (e i₀) = u := Submodule.reflection_sub (he.trans hu.symm)
    -- `f = R ∘ e`: `β(f_i) = ‖b‖ ⟪R e_{i₀}, R e_i⟫ = ‖β‖ ⟪e_{i₀}, e_i⟫`
    refine ⟨e.map R, fun i => ?_⟩
    rw [OrthonormalBasis.map_apply, hβb, hbu, real_inner_smul_left, ← hR,
      LinearIsometryEquiv.inner_map_map, hnorm, orthonormal_iff_ite.mp e.orthonormal i₀ i]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi.symm, ite_eq_left hi, mul_one]
    · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, mul_zero]
/-- **`β ∧ γ` on tuples of a family adapted to `β`** (Simon 6.1.1–1.3; step 4 of the proof of
`|β ∧ γ| ≤ ‖β‖ |γ|`): if `β(v_a) = c` for `a = i₀` and `β(v_a) = 0` otherwise, then for every
`j : Fin (k + 1) → Fin P`, `(β ∧ γ)(v_{j(0)}, …, v_{j(k)})² ≤ c² Σ_{i, j(i) = i₀} γ(v ∘ ĵᵢ)²`,
where `ĵᵢ = i.removeNth j` deletes the `i`-th entry of `j`.  By definition
`(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`.  A repeated index in `j` makes `v ∘ j`
non-injective, so the left side vanishes (alternation); otherwise at most one `i₁` has
`j(i₁) = i₀`, only `i₁` contributes to either side, and `((−1)^{i₁})² = 1`. -/
theorem Submission.cmcs_wn_tuple_sq_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k) (v : Fin P → Euclid P) (i₀ : Fin P) (c : ℝ), Function.Injective v → (∀ i : Fin P, β (v i) = if i = i₀ then c else 0) → ∀ j : Fin (k + 1) → Fin P, (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ) (fun m => v (j m))) ^ 2 ≤ c ^ 2 * ∑ i : Fin (k + 1), if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0 := by
  intro P k β γ v i₀ c _hv hβ j
  classical
  -- the right side is `c²` times a sum of squares and zeros
  have hRHS : 0 ≤ c ^ 2 * ∑ i : Fin (k + 1),
      (if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0) :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  by_cases hj : Injective j
  · -- `(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`, with `β(v_{j(i)}) = c [j(i) = i₀]`
    have hexp : ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
        (fun m => v (j m)) = ∑ i : Fin (k + 1),
          (-1 : ℝ) ^ (i : ℕ) *
            ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, hβ (j i)]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [hexp]
    by_cases hex : ∃ i₁, j i₁ = i₀
    · -- `j` is injective, so `i₁` is the only index with `j(i₁) = i₀`
      obtain ⟨i₁, hi₁⟩ := hex
      have huniq : ∀ i, i ≠ i₁ → j i ≠ i₀ := fun i hi h => hi (hj (h.trans hi₁.symm))
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by rw [ite_eq_right (huniq i hi)]; ring)
          (fun h => absurd (Finset.mem_univ i₁) h),
        Finset.sum_eq_single i₁ (fun i _ hi => ite_eq_right (huniq i hi))
          (fun h => absurd (Finset.mem_univ i₁) h),
        ite_eq_left hi₁, ite_eq_left hi₁]
      have hsign : ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      refine le_of_eq ?_
      calc ((-1 : ℝ) ^ (i₁ : ℕ) * (c * γ (fun m => v (i₁.removeNth j m)))) ^ 2
          = ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 * (c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2) := by
            ring
        _ = c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2 := by rw [hsign, one_mul]
    · -- no index hits `i₀`: every term vanishes
      have h0 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
          ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ite_eq_right fun h => hex ⟨i, h⟩]; ring
      rw [h0]
      simpa using hRHS
  · -- a repeated index makes `v ∘ j` non-injective, and `β ∧ γ` is alternating
    have hvj : ¬ Injective (fun m => v (j m)) := fun h => hj (Injective.of_comp (f := v) h)
    rw [ContinuousAlternatingMap.map_eq_zero_of_not_injective _ _ hvj]
    simpa using hRHS
/-- **Fibres of `j ↦ removeNth i j`** (the counting step of the bound `|β ∧ γ| ≤ ‖β‖ |γ|` for the
Euclidean norm of covectors, Simon Ch. 6, 1.1–1.3, 1.15): for `i₀ : Fin P` and
`F : (Fin k → Fin P) → ℝ`,
`Σ_{j : Fin (k+1) → Fin P} Σ_i [j i = i₀] F(removeNth i j) = (k + 1) Σ_{j' : Fin k → Fin P} F j'`.
For fixed `i`, `j ↦ (j i, removeNth i j)` is a bijection onto `Fin P × (Fin k → Fin P)`
(`Fin.insertNthEquiv`), so only `j i = i₀` survives and each of the `k + 1` indices `i`
contributes `Σ_{j'} F j'`. -/
theorem Submission.cmcs_wn_removeNth_fiber_sum : ∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j' := by
  intro k P i₀ F
  rw [Finset.sum_comm]
  -- for fixed `i`, reindex along `j ↦ (j i, removeNth i j)`; only `j i = i₀` survives
  have hfib : ∀ i : Fin (k + 1),
      ∑ j : Fin (k + 1) → Fin P, (if j i = i₀ then F (i.removeNth j) else 0) =
        ∑ j' : Fin k → Fin P, F j' := by
    intro i
    rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin P) i).symm
      (fun j => if j i = i₀ then F (i.removeNth j) else 0)
      (fun p => if p.1 = i₀ then F p.2 else 0) fun _ => rfl,
      Fintype.sum_prod_type, Fintype.sum_eq_single i₀]
    · simp
    · intro x hx
      simp [hx]
  -- each of the `k + 1` indices `i` contributes `Σ_{j'} F j'`
  rw [Finset.sum_congr rfl fun i _ => hfib i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add_one]
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
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
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
/-- **Triangle inequality for local mass** (Simon 6.2.5).  If `|c| ≤ 1` and
`Z(ω) = X(ω) + c Y(ω)` for every `ω ∈ 𝒟ᵏ(U)` with `spt ω ⊆ G`, then
`M_G(Z) ≤ M_G(X) + M_G(Y)`.  For `ω` admissible for `M_G`, `−ω` is admissible too, so
`|Y(ω)| ≤ M_G(Y)`; since `c Y(ω) ≤ |Y(ω)|`, `Z(ω) ≤ X(ω) + |Y(ω)| ≤ M_G(X) + M_G(Y)`.  Taking the
supremum over admissible `ω` gives the claim (`c = ±1`: sum and difference). -/
theorem Submission.lcmp_massOn_le_add_of_eval_eq : ∀ (P k : ℕ) (U G : Set (Euclid P)) (X Y Z : GeometricCurrentOn U k) (c : ℝ), |c| ≤ 1 → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ G → Z ω = X ω + c * Y ω) → Z.massOn G ≤ X.massOn G + Y.massOn G := by
  intro P k U G X Y Z c hc hZ
  -- Step 4: `M_G(Z)` is a supremum, so bound each admissible value `ofReal (Z ω)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- Step 1: `−ω` is admissible (same support, same Euclidean coefficient norm)
  have hneg : -ω ∈ massAdmissibleOn U k G := by
    refine ⟨?_, fun x => ?_⟩
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) =
          -(ω : DifferentialForm (Euclid P) k) := rfl
      rw [hco, tsupport_neg]
      exact hω.1
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
          -((ω : DifferentialForm (Euclid P) k) x) := rfl
      rw [hco, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 2: `ofReal (X ω) ≤ M_G(X)` and, as `Y(−ω) = −Y(ω)`, `ofReal |Y(ω)| ≤ M_G(Y)`
  have hXle : ENNReal.ofReal (X ω) ≤ X.massOn G := X.le_massOn hω
  have hYle : ENNReal.ofReal (Y ω) ≤ Y.massOn G := Y.le_massOn hω
  have hYle' : ENNReal.ofReal (Y (-ω)) ≤ Y.massOn G := Y.le_massOn hneg
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hYle'
  have habs : ENNReal.ofReal |Y ω| ≤ Y.massOn G := by
    rcases abs_cases (Y ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hYle
    · rw [h]; exact hYle'
  -- Step 3: `c Y(ω) ≤ |c| |Y(ω)| ≤ |Y(ω)|`; `ofReal` is monotone and subadditive
  have hcy : c * Y ω ≤ |Y ω| :=
    calc c * Y ω ≤ |c * Y ω| := le_abs_self _
      _ = |c| * |Y ω| := abs_mul _ _
      _ ≤ 1 * |Y ω| := by gcongr
      _ = |Y ω| := one_mul _
  show ENNReal.ofReal (Z ω) ≤ X.massOn G + Y.massOn G
  calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (X ω + c * Y ω) := by rw [hZ ω hω.1]
    _ ≤ ENNReal.ofReal (X ω + |Y ω|) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (X ω) + ENNReal.ofReal |Y ω| := ENNReal.ofReal_add_le
    _ ≤ X.massOn G + Y.massOn G := add_le_add hXle habs
/-- **Mass localization for a current vanishing away from a compact set** (Simon 7.2.4, proof,
step 4(a)).  Let `C ⊆ V` with `C` compact and `V` open, and let `X ∈ 𝒟ₖ(U)` kill every
`ω ∈ 𝒟ᵏ(U)` with `spt ω ∩ C = ∅`.  Then `M_G(X) ≤ M_V(X)` for every `G`.  Choose a smooth
`χ : ℝᴾ → [0, 1]` with `χ = 1` on an open `N ⊇ C` and `spt χ ⊆ V`.  For `ω` admissible
for `M_G`, `(1 − χ)ω` vanishes on `N`, so `X(ω) = X(χω)`, and `χω` is admissible for `M_V`
because `|χω| = χ|ω| ≤ 1`. -/
theorem Submission.lcmp_massOn_le_of_vanish_off_compact : ∀ (P k : ℕ) (U V C : Set (Euclid P)) (X : GeometricCurrentOn U k), IsCompact C → IsOpen V → C ⊆ V → (∀ ω : TestFormOn U k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) C → X ω = 0) → ∀ G : Set (Euclid P), X.massOn G ≤ X.massOn V := by
  intro P k U V C X hC hV hCV hvan G
  -- Step 4: `|cα| = |c| |α|` for the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
        ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        ring
      · simp
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  -- Step 1: if `C = ∅` then `X = 0`, so `M_G(X) = 0`
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine sSup_le ?_
    rintro r ⟨ω, -, rfl⟩
    show ENNReal.ofReal (X ω) ≤ X.massOn V
    rw [hvan ω (disjoint_empty _), ENNReal.ofReal_zero]
    exact zero_le
  -- Step 2: `C ⊆ V' = {dist(·, C) < δ/2}` with `closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hV'o : IsOpen (thickening (δ / 2) C) := isOpen_thickening
  -- Step 3: `χ = τ(2g/a)`, where `{g ≠ 0} = V'`, `a = min_C g > 0`, `τ` the smooth transition
  obtain ⟨g, hgsupp, hgsmooth, hgrange⟩ := hV'o.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgrange ⟨x, rfl⟩).1
  have hgpos : ∀ x ∈ C, 0 < g x := by
    intro x hx
    have hxs : x ∈ support g := by
      rw [hgsupp]
      exact self_subset_thickening (half_pos hδ) C hx
    exact lt_of_le_of_ne (hgnn x) (Ne.symm hxs)
  obtain ⟨x₀, hx₀C, hx₀min⟩ := hC.exists_isMinOn hCne hgsmooth.continuous.continuousOn
  set a := g x₀
  have ha : 0 < a := hgpos x₀ hx₀C
  set χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 * g x / a)
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hgsmooth).div_const a)
  -- `χ = 1` on the open set `N = {g > a/2} ⊇ C`
  set N : Set (Euclid P) := {x | a / 2 < g x}
  have hNo : IsOpen N := isOpen_lt continuous_const hgsmooth.continuous
  have hCN : C ⊆ N := fun x hx => by
    have h1 : a ≤ g x := hx₀min hx
    show a / 2 < g x
    linarith
  have hχN : ∀ x ∈ N, χ x = 1 := fun x hx => by
    apply Real.smoothTransition.one_of_one_le
    have hx' : a / 2 < g x := hx
    rw [le_div_iff₀ ha]
    linarith
  -- `χ = 0` where `g = 0`, so `spt χ ⊆ closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  have hχsupp : support χ ⊆ thickening (δ / 2) C := by
    intro x hx
    by_contra h
    rw [← hgsupp, mem_support, not_not] at h
    apply hx
    show Real.smoothTransition (2 * g x / a) = 0
    rw [h, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hclχ : tsupport χ ⊆ cthickening (δ / 2) C :=
    (closure_mono hχsupp).trans (closure_thickening_subset_cthickening _ _)
  have htχ : tsupport χ ⊆ V :=
    hclχ.trans ((cthickening_mono (half_le_self hδ.le) C).trans hδV)
  -- Step 5: for `ω` admissible for `M_G`, `ω₁ = χω ∈ 𝒟ᵏ(U)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ X.massOn V
  have hωt : IsTestForm (ω : DifferentialForm (Euclid P) k) := ω.property.1
  obtain ⟨ω₁f, hω₁f⟩ : ∃ g : DifferentialForm (Euclid P) k,
      g = fun x => χ x • (ω : DifferentialForm (Euclid P) k) x := ⟨_, rfl⟩
  have hω₁smooth : IsSmoothForm ω₁f := by
    rw [hω₁f]
    exact hχsmooth.smul hωt.1
  have hω₁supp : tsupport ω₁f ⊆ tsupport (ω : DifferentialForm (Euclid P) k) := by
    rw [hω₁f]
    exact tsupport_smul_subset_right _ _
  have hω₁suppχ : tsupport ω₁f ⊆ tsupport χ := by
    rw [hω₁f]
    exact tsupport_smul_subset_left _ _
  have hω₁cpt : HasCompactSupport ω₁f :=
    IsCompact.of_isClosed_subset hωt.2 (isClosed_tsupport _) hω₁supp
  let ω₁ : TestFormOn U k := ⟨ω₁f, ⟨hω₁smooth, hω₁cpt⟩, hω₁supp.trans ω.property.2⟩
  -- Step 6: `ω₂ = ω − ω₁` vanishes on `N ⊇ C`, so `spt ω₂ ∩ C = ∅` and `X(ω₂) = 0`
  have hω₂van : X (ω - ω₁) = 0 := by
    apply hvan
    rw [Set.disjoint_left]
    intro x hx hxC
    have hzero : ∀ y ∈ N, ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y = 0 := by
      intro y hy
      have hco : ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y =
          (ω : DifferentialForm (Euclid P) k) y - ω₁f y := rfl
      rw [hco, hω₁f]
      beta_reduce
      rw [hχN y hy, one_smul, sub_self]
    have hxN : x ∈ N := hCN hxC
    have hnot : x ∉ tsupport ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hNo.mem_nhds hxN] with y hy
      exact hzero y hy
    exact hnot hx
  have hsplit : X ω = X ω₁ := by
    have : X (ω - ω₁) = X ω - X ω₁ := map_sub X.toCurrent ω ω₁
    linarith
  -- Step 5 (cont.): `spt ω₁ ⊆ spt χ ⊆ V` and `|ω₁(x)| = χ(x) |ω(x)| ≤ 1`
  have hadm : ω₁ ∈ massAdmissibleOn U k V := by
    refine ⟨hω₁suppχ.trans htχ, fun x => ?_⟩
    have hco : (ω₁ : DifferentialForm (Euclid P) k) x =
        χ x • (ω : DifferentialForm (Euclid P) k) x := by
      show ω₁f x = _
      rw [hω₁f]
    rw [hco, hsmul]
    have h0 : 0 ≤ χ x := Real.smoothTransition.nonneg _
    have h1 : χ x ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg h0]
    have h2 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
    have h3 := hω.2 x
    nlinarith
  -- Step 7: `ofReal X(ω) = ofReal X(ω₁) ≤ M_V(X)`; take the supremum over `ω`
  rw [hsplit]
  exact X.le_massOn hadm
/-- Choice of a good slicing level (Simon 7.2.4 (3)–(5), the choice of `α` and of the
subsequence).  Let `A = {a < f < b}` with `νⱼ(A) < ∞`, `νⱼ(A) → 0` and `κⱼ(A) < ∞`.  Some
`t ∈ (a, b)` has `κⱼ{f = t} = 0` and `Dⱼ(t) < ∞` for every `j`, and `D_{φ(j)}(t) → 0` along a
subsequence `φ`, where `Dⱼ(t) = liminf_{h ↓ 0} h⁻¹ νⱼ{t − h < f < t}`.  For `ρⱼ = f_#(νⱼ⌞A)`,
Tonelli gives `∫ ρⱼ((s − c, s)) ds = c νⱼ(A)`, so `Gⱼ(s) = liminf_k (k + 1) ρⱼ((s − 1/(k+1), s))`
has `∫ Gⱼ ≤ νⱼ(A)` (Fatou) and `Dⱼ ≤ Gⱼ` on `(a, b)`.  Fatou in `j` and the countability of the
atoms of `κⱼ⌞A` then give `t`. -/
theorem Submission.lcmp_exists_good_slice_level : ∀ (P : ℕ) (ν κ : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (a b : ℝ), Measurable f → a < b → (∀ j, ν j {x | a < f x ∧ f x < b} < ∞) → Tendsto (fun j => ν j {x | a < f x ∧ f x < b}) atTop (𝓝 0) → (∀ j, κ j {x | a < f x ∧ f x < b} < ∞) → ∃ t ∈ Ioo a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, κ j {x | f x = t} = 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) < ∞) ∧ Tendsto (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (φ j) {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)) atTop (𝓝 0) := by
  intro P ν κ f a b hf hab hνfin hνlim hκfin
  obtain ⟨A, hA⟩ : ∃ A : Set (Euclid P), A = {x | a < f x ∧ f x < b} := ⟨_, rfl⟩
  rw [← hA] at hνfin hνlim hκfin
  -- Step 2: `ρⱼ = f_#(νⱼ⌞A)` is a finite measure on `ℝ`, `ρⱼ(B) = νⱼ(f⁻¹(B) ∩ A)`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Measure ℝ, ρ = fun j => ((ν j).restrict A).map f := ⟨_, rfl⟩
  have hρapp : ∀ j (s : Set ℝ), MeasurableSet s → ρ j s = ν j (f ⁻¹' s ∩ A) := by
    intro j s hs
    rw [hρ, Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
  have hρuniv : ∀ j, ρ j univ = ν j A := by
    intro j
    rw [hρapp j univ MeasurableSet.univ, preimage_univ, univ_inter]
  have hρfin : ∀ j, IsFiniteMeasure (ρ j) := fun j => ⟨by rw [hρuniv]; exact hνfin j⟩
  -- Step 3: Tonelli on `S_c = {(s, y) : s − c < y < s}`: `∫ ρⱼ((s − c, s)) ds = c νⱼ(A)`
  have hSm : ∀ c : ℝ, MeasurableSet {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} := fun c =>
    (measurableSet_lt (measurable_fst.sub_const c) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hsec : ∀ c t : ℝ,
      Prod.mk t ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo (t - c) t := by
    intro c t
    ext y
    simp [mem_Ioo]
  have hsec' : ∀ c y : ℝ,
      (fun t => (t, y)) ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo y (y + c) := by
    intro c y
    ext t
    simp only [mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hmeasF : ∀ j (c : ℝ), Measurable fun t : ℝ => ρ j (Ioo (t - c) t) := by
    intro j c
    have := hρfin j
    have := measurable_measure_prodMk_left (ν := ρ j) (hSm c)
    simpa only [hsec] using this
  have hTon : ∀ j (c : ℝ), ∫⁻ t, ρ j (Ioo (t - c) t) = ENNReal.ofReal c * ν j A := by
    intro j c
    have := hρfin j
    have h1 := Measure.prod_apply (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    have h2 := Measure.prod_apply_symm (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    simp only [hsec, hsec', Real.volume_Ioo, add_sub_cancel_left] at h1 h2
    rw [← h1, h2, lintegral_const, hρuniv]
  -- Step 4: `Fⱼₖ(s) = (k + 1) ρⱼ((s − 1/(k+1), s))` has `∫ Fⱼₖ = νⱼ(A)`, so the majorant
  -- `Gⱼ = liminf_k Fⱼₖ` has `∫ Gⱼ ≤ νⱼ(A)` (Fatou)
  have hFm : ∀ j (k : ℕ),
      Measurable fun t : ℝ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) :=
    fun j k => (hmeasF j _).const_mul _
  have hcancel : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) = 1 := by
    intro k
    have hk : ENNReal.ofReal ((k : ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), hk,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  have hFint : ∀ j (k : ℕ),
      ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) = ν j A := by
    intro j k
    rw [lintegral_const_mul _ (hmeasF j _), hTon j, ← mul_assoc, hcancel, one_mul]
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ → ℝ≥0∞, G = fun j t =>
      liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop :=
    ⟨_, rfl⟩
  have hGm : ∀ j, Measurable (G j) := fun j => by
    rw [hG]
    exact Measurable.liminf (hFm j)
  have hGint : ∀ j, ∫⁻ t, G j t ≤ ν j A := by
    intro j
    rw [hG]
    calc ∫⁻ t, liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop
        ≤ liminf (fun k : ℕ => ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t))
          atTop := lintegral_liminf_le (hFm j)
      _ = ν j A := by simp only [hFint, liminf_const]
  have hGfin : ∀ᵐ t, ∀ j, G j t < ∞ :=
    ae_all_iff.2 fun j => ae_lt_top (hGm j) ((hGint j).trans_lt (hνfin j)).ne
  -- Step 5: Fatou in `j`: `∫ liminf_j Gⱼ ≤ liminf_j νⱼ(A) = 0`, so `liminf_j Gⱼ = 0` a.e.
  have hHm : Measurable fun t => liminf (fun j => G j t) atTop := Measurable.liminf hGm
  have hHint : ∫⁻ t, liminf (fun j => G j t) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ t, liminf (fun j => G j t) atTop ≤ liminf (fun j => ∫⁻ t, G j t) atTop :=
          lintegral_liminf_le hGm
      _ ≤ liminf (fun j => ν j A) atTop := liminf_le_liminf (Eventually.of_forall hGint)
      _ = 0 := hνlim.liminf_eq
  have hH0 : ∀ᵐ t, liminf (fun j => G j t) atTop = 0 :=
    ((lintegral_eq_zero_iff hHm).1 hHint).mono fun t ht => ht
  -- Step 6: only countably many levels are atoms of the finite measure `κⱼ⌞A`
  have hatomsAE : ∀ᵐ s : ℝ, ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    rw [ae_all_iff]
    intro j
    have : IsFiniteMeasure ((κ j).restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hκfin j⟩
    have hc := Measure.countable_meas_level_set_pos (μ := (κ j).restrict A) hf
    filter_upwards [hc.ae_notMem (volume : Measure ℝ)] with s hs
    simp only [not_lt, nonpos_iff_eq_zero] at hs
    exact hs
  -- Step 7: a.e. level in the interval `(a, b)` of positive length is good
  have hIoo : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    simpa using hab
  have : (ae (volume.restrict (Ioo a b))).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hIoo)
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioo a b)), s ∈ Ioo a b ∧
      liminf (fun j => G j s) atTop = 0 ∧ (∀ j, G j s < ∞) ∧
      ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hH0,
      ae_restrict_of_ae hGfin, ae_restrict_of_ae hatomsAE] with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨t, ht, hHt, hGt, hκt⟩ := hgood.exists
  -- Step 9: `Dⱼ(t) ≤ Gⱼ(t)`, along `hₖ = 1/(k + 1)` with `{t − hₖ < f < t} ⊆ A` for large `k`
  have hlink : ∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t})
      (𝓝[>] 0) ≤ G j t := by
    intro j
    have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => ?_⟩
      show (0 : ℝ) < 1 / ((k : ℝ) + 1)
      positivity
    have hle := liminf_le_liminf_of_le
      (u := fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) hseq
    refine hle.trans (le_of_eq ?_)
    rw [hG]
    show liminf ((fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) ∘
      fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop = _
    apply liminf_congr
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < t - a :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (sub_pos.2 ht.1))
    filter_upwards [hsmall] with k hk
    simp only [Function.comp_apply]
    have h1 : ENNReal.ofReal (1 / ((k : ℝ) + 1))⁻¹ = (k : ℝ≥0∞) + 1 := by
      rw [one_div, inv_inv, ENNReal.ofReal_add (by positivity) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    have h2 : ν j {x | t - 1 / ((k : ℝ) + 1) < f x ∧ f x < t} =
        ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) := by
      rw [hρapp j _ measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, hA]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨⟨h3, h4⟩, ?_, ?_⟩ <;> linarith [ht.2]
      · rintro ⟨⟨h3, h4⟩, -⟩
        exact ⟨h3, h4⟩
    rw [h1, h2]
  -- Step 11: `liminf_j Gⱼ(t) = 0` gives `φ` strictly increasing with `G_{φ(n)}(t) < 1/(n + 1)`
  have hfreq : ∀ n : ℕ, ∃ᶠ j in atTop, G j t < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine frequently_lt_of_liminf_lt (by isBoundedDefault) ?_
    rw [hHt]
    exact ENNReal.inv_pos.2 (by simp)
  obtain ⟨φ, hφ, hφlt⟩ := extraction_forall_of_frequently hfreq
  refine ⟨t, ht, φ, hφ, fun j => ?_, fun j => (hlink j).trans_lt (hGt j), ?_⟩
  -- Step 8: (i), as `{f = t} ⊆ A`
  · have hsubA : {x | f x = t} ⊆ A := by
      intro x hx
      rw [hA]
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      exact ht
    have h := hκt j
    rwa [Measure.restrict_apply (measurableSet_eq_fun hf measurable_const),
      inter_eq_left.2 hsubA] at h
  -- Step 11: (iii), `0 ≤ D_{φ(n)}(t) ≤ G_{φ(n)}(t) < 1/(n + 1)`
  · have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => zero_le)
      (fun n => (hlink (φ n)).trans (hφlt n).le)
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion
/-- **Outer bound on a compact set** (Simon 7.2.4, proof: (F4) and step 8).  Let `U ⊆ ℝᴾ` be
open, `E ⊆ U` compact, `ν(K) < ∞` for compact `K ⊆ U`, and `μ(G) ≤ ν(G) + c` for every open
`G ⊇ E` with `G ⊂⊂ U`.  Then `μ(E) ≤ ν(E) + c`.  Choose `δ > 0` with `{dist(·, E) ≤ δ} ⊆ U`; the
open thickenings `G_k = {dist(·, E) < δ/(k + 2)}` contain `E`, are compactly contained in `U` and
decrease to `closure E = E`, and `ν(G₀) < ∞`, so `ν(G_k) → ν(E)` by continuity from above and
`μ(E) ≤ μ(G_k) ≤ ν(G_k) + c` passes to the limit. -/
theorem Submission.lcmp_measure_le_add_of_open_nhds : ∀ (P : ℕ) (U E : Set (Euclid P)) (μ ν : Measure (Euclid P)) (c : ℝ≥0∞), IsOpen U → IsCompact E → E ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → (∀ G : Set (Euclid P), IsOpen G → E ⊆ G → CompactlyContained G U → μ G ≤ ν G + c) → μ E ≤ ν E + c := by
  intro P U E μ ν c hU hE hEU hν hG
  -- Step 1: `cthickening δ E ⊆ U`; the radii `r k = δ/(k + 2) ∈ (0, δ]` decrease
  obtain ⟨δ, hδ, hδU⟩ := hE.exists_cthickening_subset_open hU hEU
  set r : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hr
  have hrpos : ∀ k, 0 < r k := fun k => div_pos hδ (by positivity)
  have hrle : ∀ k, r k ≤ δ := fun k =>
    div_le_self hδ.le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hranti : Antitone r := fun a b hab =>
    div_le_div_of_nonneg_left hδ.le (by positivity) (by
      have : (a : ℝ) ≤ b := Nat.cast_le.2 hab
      linarith)
  -- Step 2: `G k = thickening (r k) E` is open, contains `E`, and has compact closure
  -- `⊆ cthickening δ E ⊆ U`; so `μ(E) ≤ μ(G k) ≤ ν(G k) + c`
  set G : ℕ → Set (Euclid P) := fun k => thickening (r k) E
  have hGo : ∀ k, IsOpen (G k) := fun k => isOpen_thickening
  have hEG : ∀ k, E ⊆ G k := fun k => self_subset_thickening (hrpos k) E
  have hclG : ∀ k, closure (G k) ⊆ cthickening δ E := fun k =>
    (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (hrle k) E)
  have hGcc : ∀ k, CompactlyContained (G k) U := fun k =>
    ⟨hE.cthickening.of_isClosed_subset isClosed_closure (hclG k), (hclG k).trans hδU⟩
  have hle : ∀ k, μ E ≤ ν (G k) + c := fun k =>
    (measure_mono (hEG k)).trans (hG _ (hGo k) (hEG k) (hGcc k))
  -- Step 3: `G k` decreases to `closure E = E`, and `ν(G 0) ≤ ν(cthickening δ E) < ∞`
  have hanti : Antitone G := fun a b hab => thickening_mono (hranti hab) E
  have hinter : ⋂ k, G k = E := by
    apply subset_antisymm
    · intro x hx
      rw [mem_iInter] at hx
      have hxcl : x ∈ closure E := by
        rw [closure_eq_iInter_thickening]
        simp only [mem_iInter]
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_gt (δ / ε)
        have hrk : r k < ε := by
          rw [hr, div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hk
          nlinarith
        exact thickening_mono hrk.le E (hx k)
      rwa [hE.isClosed.closure_eq] at hxcl
    · exact subset_iInter hEG
  have hfin0 : ν (G 0) ≠ ∞ :=
    ((measure_mono ((subset_closure).trans (hclG 0))).trans_lt
      (hν _ hE.cthickening hδU)).ne
  -- Step 4: continuity from above gives `ν(G k) + c → ν(E) + c`; pass to the limit
  have htend : Tendsto (fun k => ν (G k)) atTop (𝓝 (ν E)) := by
    have := tendsto_measure_iInter_atTop (μ := ν)
      (fun k => (hGo k).measurableSet.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rwa [hinter] at this
  exact ge_of_tendsto' (htend.add_const c) hle
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2
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

/-- **Simon Ch. 6, 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U`, then
`M_W(T) = μ_R(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  The upper bound
`dor_ims_massOn_le_measure` and the lower bound `dor_ims_measure_le_massOn` give equality by
antisymmetry. -/
theorem Submission.cmc_massOn_eq_imRep_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := by
  intro P n U T R hU hR W hW
  exact le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
    (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
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

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ
/-- **`|β ∧ γ| ≤ ‖β‖ |γ|`** (Simon 6.1.1–1.3 and 1.15): for a linear functional `β` and a
`k`-covector `γ` on `ℝᴾ`, the Euclidean coefficient norm of the `(k+1)`-covector
`β ∧ γ = alternatizeUncurryFin (β.smulRight γ)` is at most `‖β‖ |γ|`.  Take an orthonormal basis
`f` with `β(fᵢ) = ‖β‖ [i = i₀]`; then `(β ∧ γ)(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²`.
Summing over `j`, each `j' : Fin k → Fin P` arises as `i.removeNth j` with `j i = i₀` for exactly
`k + 1` pairs `(i, j)`, so `(k+1)! |β ∧ γ|² ≤ ‖β‖² (k+1) k! |γ|²` by
`regcomp_covector_sq_sum_orthonormalBasis` in degrees `k + 1` and `k`.  For `P = 0` there are no
coordinate tuples and `|β ∧ γ| = 0`. -/
theorem Submission.cmcs_wedge_norm_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ := by
  intro P k β γ
  classical
  set ω := ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
  have hrhs : 0 ≤ ‖β‖ * covectorEuclideanNorm γ :=
    mul_nonneg (norm_nonneg β) (covectorEuclideanNorm_nonneg γ)
  rcases Nat.eq_zero_or_pos P with hP | hP
  · -- `P = 0`: there is no tuple `Fin (k + 1) → Fin 0`, so `|ω| = 0`
    subst hP
    have h0 : covectorEuclideanNorm ω = 0 := by
      simp [covectorEuclideanNorm]
    rw [h0]
    exact hrhs
  · -- an orthonormal basis `f` with `β(fᵢ) = ‖β‖ [i = i₀]`
    set i₀ : Fin P := ⟨0, hP⟩
    obtain ⟨f, hf⟩ := Submission.cmcs_wn_adapted_orthonormalBasis P β i₀
    -- `ω(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²` for every `j`
    have hle : ∑ j : Fin (k + 1) → Fin P, (ω (fun m => f (j m))) ^ 2 ≤
        ∑ j : Fin (k + 1) → Fin P, ‖β‖ ^ 2 * ∑ i : Fin (k + 1),
          (if j i = i₀ then (γ (fun m => f (i.removeNth j m))) ^ 2 else 0) :=
      Finset.sum_le_sum fun j _ => Submission.cmcs_wn_tuple_sq_le P k β γ f i₀ ‖β‖
        f.orthonormal.linearIndependent.injective hf j
    -- count the fibres of `j ↦ i.removeNth j`, then `Σ_j α(f ∘ j)² = m! |α|²` for `m = k + 1, k`
    rw [← Finset.mul_sum,
      Submission.cmcs_wn_removeNth_fiber_sum k P i₀ (fun j' => (γ (fun m => f (j' m))) ^ 2),
      Submission.regcomp_covector_sq_sum_orthonormalBasis P (k + 1) ω f,
      Submission.regcomp_covector_sq_sum_orthonormalBasis P k γ f] at hle
    -- cancel `(k+1)! = (k+1) k! > 0`
    have hpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hsq : covectorEuclideanNorm ω ^ 2 ≤ (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm ω ^ 2
          ≤ ‖β‖ ^ 2 * (((k : ℝ) + 1) * ((k.factorial : ℝ) * covectorEuclideanNorm γ ^ 2)) := hle
        _ = ((k + 1).factorial : ℝ) * (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
          push_cast [Nat.factorial_succ]
          ring
    exact (sq_le_sq₀ (covectorEuclideanNorm_nonneg ω) hrhs).mp hsq

/-- **Simon Ch. 6, 4.11 (p. 158), the estimate of the cutoff defect**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')` with `|⟨α, ξ⟩| ≤ |α|` `μ`-a.e.: for a `C^∞` function `g`
and `η ∈ 𝒟ᵏ(U)`, `|∫ g ⟨dη, ξ⟩ dμ − ∫ g ⟨η, ξ'⟩ dμ'| ≤ ∫ |Dg| |η| dμ` in `[0, ∞]`.  The left side
is `|T(g dη) − ∂T(gη)| = |T(dg ∧ η)| = |∫ ⟨dg ∧ η, ξ⟩ dμ|` (`cmcs_cd_defect_identity`, with
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`), which is at most `∫ |⟨dg ∧ η, ξ⟩| dμ` whether
or not the integrand is integrable; and `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|` `μ`-a.e. by the bound
on `ξ` and `cmcs_wedge_norm_le`. -/
theorem Submission.cmcs_cutoff_defect_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ENNReal.ofReal |∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ'| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((η : DifferentialForm (Euclid P) k) x)) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hξ hT hbT hg
  -- Simon 4.11: `T(g dη) − ∂T(gη) = −T(dg ∧ η) = −∫ ⟨dg ∧ η, ξ⟩ dμ`
  rw [Submission.cmcs_cd_defect_identity P k U T μ μ' ξ ξ' g η hT hbT hg, abs_neg,
    ← Real.enorm_eq_ofReal_abs]
  -- `‖∫ G dμ‖ₑ ≤ ∫⁻ ‖G‖ₑ dμ` for every `G`, integrable or not; then bound `G` `μ`-a.e.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hξ] with x hx
  -- `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|`
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((hx _).trans (Submission.cmcs_wedge_norm_le P k _ _))
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
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

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Smooth cut-off between two levels of a Lipschitz function** (Simon Ch. 6, proof of 4.9, with
`f^{(σ)}` in place of `f`).  If `f : ℝᴾ → ℝ` is `L`-Lipschitz, `t ∈ ℝ` and `0 < h < 1`, there is a
`C^∞` function `g` with `|g| ≤ 2`, `‖Dg‖ ≤ L/(h(1 − h/2))`, `g = 1` on `{f ≤ t − h}`, `g = 0` on
`{f ≥ t}` and `Dg = 0` off the strip `{t − h < f < t}`.  With `δ = h²/4` and
`w = h − 2δ = h(1 − h/2)`, the clamp `G = max 0 (min 1 ((t − δ − f)/w))` is `(L/w)`-Lipschitz,
`G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`; `g` is its smoothing at scale
`σ = δ/(2(L + 1))` (`cmcs_lipschitz_smoothing`), so `|g − G| ≤ Lσ/w ≤ 1`.  As `2Lσ < δ`, `G` is
constant on `B_{2σ}(x)` when `f x ≤ t − h` or `t ≤ f x`; by locality `g` is then constant on
`B_σ(x)`, so `Dg(x) = 0`. -/
theorem Submission.cmcs_level_cutoff : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (t h : ℝ), LipschitzWith L f → 0 < h → h < 1 → ∃ g : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧ (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧ (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
  intro P f L t h hf h0 h1
  -- parameters `δ = h²/4`, `w = h − 2δ = h(1 − h/2)` and `σ = δ/(2(L + 1))`, so `2Lσ < δ`
  set δ : ℝ := h ^ 2 / 4 with hδ
  set w : ℝ := h * (1 - h / 2) with hw
  have hw0 : 0 < w := mul_pos h0 (by linarith)
  have hδ0 : 0 < δ := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set σ : ℝ := δ / (2 * ((L : ℝ) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have h2Lσ : 2 * (L : ℝ) * σ < δ := by
    rw [hσ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the clamped profile `G = max 0 (min 1 ((t − δ − f)/w))`: `(L/w)`-Lipschitz, `|G| ≤ 1`,
  -- `G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`
  set G : Euclid P → ℝ := fun x => max 0 (min 1 ((t - δ - f x) / w)) with hGdef
  set K : NNReal := L * Real.toNNReal w⁻¹ with hK
  have hKr : (K : ℝ) = L / w := by
    rw [hK, NNReal.coe_mul, Real.coe_toNNReal _ (inv_pos.2 hw0).le, div_eq_mul_inv]
  have hG : LipschitzWith K G := by
    have hlin : LipschitzWith K fun x => (t - δ - f x) / w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hxy := hf.dist_le_mul x y
      rw [Real.dist_eq] at hxy
      rw [Real.dist_eq, hKr, show (t - δ - f x) / w - (t - δ - f y) / w = (f y - f x) / w by ring,
        abs_div, abs_of_pos hw0, abs_sub_comm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxy hw0.le
    exact (hlin.const_min 1).const_max 0
  have hG01 : ∀ y, |G y| ≤ 1 := by
    intro y
    simp only [hGdef]
    rw [abs_le]
    exact ⟨by linarith [le_max_left 0 (min 1 ((t - δ - f y) / w))],
      max_le zero_le_one (min_le_left _ _)⟩
  have hG1 : ∀ y, f y < t - h + δ → G y = 1 := by
    intro y hy
    have : 1 ≤ (t - δ - f y) / w := by rw [le_div_iff₀ hw0]; linarith
    simp [hGdef, min_eq_left this]
  have hG0 : ∀ y, t - δ < f y → G y = 0 := by
    intro y hy
    have : (t - δ - f y) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
    simp only [hGdef]
    exact max_eq_left ((min_le_right _ _).trans this)
  -- smoothing of `G` at scale `σ`
  obtain ⟨g, hgs, hgd, hga, hgl⟩ := Submission.cmcs_lipschitz_smoothing P G K σ hG hσ0
  -- plateaus: if `G = c` on `B_{2σ}(x)`, then `g = c` on `B_σ(x)`, so `g x = c` and `Dg(x) = 0`
  have hnear : ∀ x, ∀ c : ℝ, (∀ y ∈ ball x (2 * σ), G y = c) → g x = c ∧ fderiv ℝ g x = 0 := by
    intro x c hc
    have hball : ∀ x' ∈ ball x σ, g x' = c := fun x' hx' => hgl x' c fun y hy => hc y (by
      rw [mem_ball] at hx' hy ⊢
      linarith [dist_triangle y x' x])
    have hev : g =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (ball_mem_nhds x hσ0) hball
    exact ⟨hball x (mem_ball_self hσ0), hev.fderiv_eq.trans (fderiv_const_apply c)⟩
  -- on `B_{2σ}(x)`, `|f y − f x| ≤ L |y − x| < 2Lσ < δ`
  have hclose : ∀ x, ∀ y ∈ ball x (2 * σ), |f y - f x| < δ := by
    intro x y hy
    have hd := hf.dist_le_mul y x
    rw [Real.dist_eq] at hd
    rw [mem_ball] at hy
    have : (L : ℝ) * dist y x ≤ L * (2 * σ) := mul_le_mul_of_nonneg_left hy.le hL0
    linarith
  have hlow : ∀ x, f x ≤ t - h → g x = 1 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 1 fun y hy => hG1 y (by linarith [(abs_lt.1 (hclose x y hy)).2])
  have hup : ∀ x, t ≤ f x → g x = 0 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 0 fun y hy => hG0 y (by linarith [(abs_lt.1 (hclose x y hy)).1])
  refine ⟨g, hgs, fun x => ?_, fun x => (hgd x).trans_eq hKr, fun x hx => ?_,
    fun x hx => (hlow x hx).1, fun x hx => (hup x hx).1⟩
  · -- `|g| ≤ |G| + Kσ ≤ 2`, as `Kσ = Lδ/(2(L + 1)w) ≤ 1` (`δ ≤ 2w`)
    have hKσ : (K : ℝ) * σ ≤ 1 := by
      rw [hKr, hσ, div_mul_div_comm, div_le_one (by positivity)]
      have hδw : δ ≤ 2 * w := by rw [hδ, hw]; nlinarith
      nlinarith
    linarith [abs_sub_abs_le_abs_sub (g x) (G x), hga x, hG01 x]
  · -- `Dg = 0` on both plateaus, so `Dg(x) ≠ 0` forces `t − h < f x < t`
    by_contra hcon
    rcases not_and_or.1 hcon with hc | hc
    · exact hx (hlow x (not_lt.1 hc)).2
    · exact hx (hup x (not_lt.1 hc)).2

/-- **Mass of a slice, pointwise in `t`** (Simon 6.4.9, proved as in 6.4.11): let `T = ξ μ`,
`∂T = ξ' μ'` with `|ξ|, |ξ'| ≤ 1`, let `f` be `L`-Lipschitz, and let `A = T ⌞ {f < t}`,
`B = (∂T) ⌞ {f < t}`.  Then `M_W(∂A − B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})`.
For an admissible `η` and `h ∈ (0, 1)`, the smooth cut-off `g_h` of `cmcs_level_cutoff` gives
`Φ_h = ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'` with `|Φ_h| ≤ ∫ |Dg_h| |η| dμ ≤ c_h μ(W ∩ S_h)`,
`c_h = L / (h(1 − h/2))`, `S_h = {t − h < f < t}` (`cmcs_cutoff_defect_bound`,
`cmcs_smp_strip_lintegral_le`); `Φ_h → (∂A − B)(η)` by dominated convergence
(`cmcs_smp_cutoff_integral_tendsto`), and `cmcs_smp_liminf_bound` passes to the liminf. -/
theorem Submission.cmcs_slice_mass_pointwise : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro P k U T μ μ' ξ ξ' f L t A B W hμ hμ' hξm hξm' hξ hξ' hT hbT hf hA hB
  -- Step 3: a cut-off `g h` for every `h ∈ (0, 1)` (junk value `0` for other `h`).
  have hcut : ∀ h : ℝ, ∃ g : Euclid P → ℝ, 0 < h → h < 1 →
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧
        (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧
        (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧
        (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
    intro h
    by_cases hh : 0 < h ∧ h < 1
    · obtain ⟨g, hg⟩ := Submission.cmcs_level_cutoff P f L t h hf hh.1 hh.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨0, fun h0 h1 => (hh ⟨h0, h1⟩).elim⟩
  choose g hg using hcut
  -- Step 1: it suffices to bound `ofReal ((∂A − B) η)` for one admissible `η`.
  apply sSup_le
  rintro r ⟨η, ⟨hηW, hη1⟩, rfl⟩
  have hZ : (A.boundary - B) η =
      (∫ x in {x | f x < t}, ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' := by
    change A (exteriorDerivativeTestOn U k η) - B η = _
    rw [hA, hB]
    rfl
  -- Step 2: `F = ξ(dη)` is `μ`-integrable and `F' = ξ'(η)` is `μ'`-integrable.
  have hF : Integrable
      (fun x => ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x)) μ :=
    Submission.cmcs_smp_pairing_integrable P (k + 1) U μ ξ (exteriorDerivativeTestOn U k η)
      hμ hξm hξ
  have hF' : Integrable (fun x => ξ' x ((η : DifferentialForm (Euclid P) k) x)) μ' :=
    Submission.cmcs_smp_pairing_integrable P k U μ' ξ' η hμ' hξm' hξ'
  -- Step 5: `Φ h → (∂A − B)(η)` as `h ↓ 0`, by dominated convergence for each integral.
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : ∀ ν : Measure (Euclid P), ∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) ν :=
    fun _ h h0 h1 => (hg h h0 h1).1.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun h : ℝ =>
      (∫ x, g h x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x, g h x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ')
      (𝓝[>] 0) (𝓝 ((A.boundary - B) η)) := by
    rw [hZ]
    exact (Submission.cmcs_smp_cutoff_integral_tendsto P μ _ f t 2 g hF hfm (hgm μ)
      (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
      (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2)).sub
      (Submission.cmcs_smp_cutoff_integral_tendsto P μ' _ f t 2 g hF' hfm (hgm μ')
        (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
        (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2))
  -- Steps 4 and 6: `ofReal |Φ h| ≤ ofReal (L / (h (1 − h/2))) μ(W ∩ S_h)` for `h ∈ (0, 1)`,
  -- then pass to the liminf.
  refine Submission.cmcs_smp_liminf_bound L ((A.boundary - B) η) _
    (fun h => μ (W ∩ {x | t - h < f x ∧ f x < t})) hlim fun h h0 h1 => ?_
  obtain ⟨hgs, -, hgd, hgS, -, -⟩ := hg h h0 h1
  exact (Submission.cmcs_cutoff_defect_bound P k U T μ μ' ξ ξ' (g h) η hξ hT hbT hgs).trans
    (Submission.cmcs_smp_strip_lintegral_le P k μ (g h) (η : DifferentialForm (Euclid P) k) W
      {x | t - h < f x ∧ f x < t} _ hgd hgS hηW hη1)
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

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **Simon Ch. 6, 4.6–4.10 (slicing by a Lipschitz function, pp. 157–158)**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')`: `A_t = T ⌞ {f < t}` and `B_t = (∂T) ⌞ {f < t}` (2.9, taken
through the given representations) are currents in `U`, and the slice `⟨T, f, t₋⟩ = ∂A_t − B_t`
(4.6) vanishes on forms supported off `{f = t}` (4.8), has
`M_W(⟨T, f, t₋⟩) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (4.9), and
`∫⁻_{(a,b)} M_W(⟨T, f, t₋⟩) dt ≤ L · μ(W ∩ {a < f < b})` (4.10).  `A_t`, `B_t` are chosen by
`cmcs_restrict_current`; 4.8 is `cmcs_slice_support` (`f` is continuous); 4.9 is
`cmcs_slice_mass_pointwise`; 4.10 is `cmcs_slice_mass_integral` applied to `t ↦ M_W(∂A_t − B_t)`
and the bound 4.9 (`f` is measurable, `W` open hence measurable). -/
theorem Submission.cmc_slice_mass_bounds : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b})) := by
  intro P k U T μ μ' ξ ξ' f L _hU hμ hμ' hξm hξm' hξ hξ' hT hbT hf
  -- `A t = T ⌞ {f < t}` and `B t = (∂T) ⌞ {f < t}` (Simon 2.9)
  choose A hA using fun t : ℝ =>
    Submission.cmcs_restrict_current P (k + 1) U μ ξ {x | f x < t} hμ hξm hξ
  choose B hB using fun t : ℝ =>
    Submission.cmcs_restrict_current P k U μ' ξ' {x | f x < t} hμ' hξm' hξ'
  -- Simon 4.9, for every `W` and `t`
  have hpt : ∀ (W : Set (Euclid P)) (t : ℝ), ((A t).boundary - B t).massOn W ≤
      (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
        μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := fun W t =>
    Submission.cmcs_slice_mass_pointwise P k U T μ μ' ξ ξ' f L t (A t) (B t) W hμ hμ' hξm hξm'
      hξ hξ' hT hbT hf (hA t) (hB t)
  refine ⟨A, B, hA, hB, fun t η hη => ?_, fun W t _ => hpt W t, fun W a b hW => ?_⟩
  · -- Simon 4.8
    exact Submission.cmcs_slice_support P k U T μ μ' ξ ξ' f t (A t) (B t) hf.continuous hT hbT
      (hA t) (hB t) η hη
  · -- Simon 4.10, from 4.9 on `(a, b)`
    exact Submission.cmcs_slice_mass_integral P μ f W L
      (fun t => ((A t).boundary - B t).massOn W) a b hf.continuous.measurable hW.measurableSet
      fun t _ => hpt W t

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
