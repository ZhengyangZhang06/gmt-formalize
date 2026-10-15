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

/-- **Planar fibre geometry** (fibre count for the cone-sector endpoint density in the proof of
Simon 7.3.3).  Let `Q ⊆ ℝᴾ` be a plane with orthonormal basis `a, e`, `π = Q.starProjection`,
`Ax = ⟨x, a⟩e − ⟨x, e⟩a` and `f(x) = arctan(⟨x, e⟩/⟨x, a⟩)`.  Then (a) `|p_T(Ax)| ≤ |πx| ≤ |x|`
for every subspace `T`; (b) for `t > 0` and `|α| < Real.pi/2`, the point
`x₀ = t(cos α a + sin α e)` has `⟨x₀, a⟩ > 0`, `|x₀| = t`, `f(x₀) = α`, `πx₀ = x₀` and
`|π(Ax₀)| = t`; (c) every other `x` with `⟨x, a⟩ > 0`, `|x| = t` and `f(x) = α` has `|πx| < t`.
A dimension count gives `Q = span{a, e}`, hence `πx = ⟨x, a⟩a + ⟨x, e⟩e` and `|Ax| = |πx|`; in
(c), `|πx| = |x|` would give `x ∈ Q`, `x = ua + ve` with `u² + v² = t²`, and then `cos α = u/t`,
`sin α = v/t` force `x = x₀`. -/
theorem Submission.idtp_cse_fc_planar_fibre_geometry : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ (T : Submodule ℝ (Euclid P)) (x : Euclid P), ‖T.starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ≤ ‖Q.starProjection x‖ ∧ ‖Q.starProjection x‖ ≤ ‖x‖) ∧ ∀ t α : ℝ, 0 < t → |α| < Real.pi / 2 → (0 < inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a ∧ ‖t • (Real.cos α • a + Real.sin α • e)‖ = t ∧ Real.arctan (inner ℝ (t • (Real.cos α • a + Real.sin α • e)) e / inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a) = α ∧ Q.starProjection (t • (Real.cos α • a + Real.sin α • e)) = t • (Real.cos α • a + Real.sin α • e) ∧ ‖Q.starProjection (inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a • e - inner ℝ (t • (Real.cos α • a + Real.sin α • e)) e • a)‖ = t) ∧ ∀ x : Euclid P, 0 < inner ℝ x a → ‖x‖ = t → Real.arctan (inner ℝ x e / inner ℝ x a) = α → x ≠ t • (Real.cos α • a + Real.sin α • e) → ‖Q.starProjection x‖ < t := by
  intro P Q a e hQ haQ heQ ha he hae
  -- Step 1: the Gram matrix of `(a, e)`
  have haa : inner ℝ a a = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hea : inner ℝ e a = (0 : ℝ) := by rw [real_inner_comm, hae]
  -- Step 2: `Q = span {a, e}` by a dimension count, so every `w ∈ Q` is `c₁ a + c₂ e`
  have hQmem : ∀ w ∈ Q, ∃ c₁ c₂ : ℝ, w = c₁ • a + c₂ • e := by
    have hon : Orthonormal ℝ ![a, e] := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [ha, he, hae, hea]
    have hspan : Submodule.span ℝ (Set.range ![a, e]) = Q := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le, Set.range_subset_iff]
        intro i
        fin_cases i
        · simpa using haQ
        · simpa using heQ
      · rw [finrank_span_eq_card hon.linearIndependent, hQ, Fintype.card_fin]
    intro w hw
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hw
    obtain ⟨c, rfl⟩ := hw
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two]⟩
  -- Step 3: `πx = ⟨x, a⟩ a + ⟨x, e⟩ e`
  have hproj : ∀ x : Euclid P, Q.starProjection x = inner ℝ x a • a + inner ℝ x e • e := by
    intro x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (Q.add_mem (Q.smul_mem _ haQ) (Q.smul_mem _ heQ)) fun w hw => ?_
    obtain ⟨c₁, c₂, rfl⟩ := hQmem w hw
    simp only [inner_sub_left, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, haa, hee, hae, hea]
    ring
  -- Step 4: `‖u e − v a‖² = u² + v² = ‖u a + v e‖²`, hence `‖Ax‖ = ‖πx‖`
  have hnormA : ∀ u v : ℝ, ‖u • e - v • a‖ ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, haa,
      hee, hae, hea]
    ring
  have hnormP : ∀ u v : ℝ, ‖u • a + v • e‖ ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, haa,
      hee, hae, hea]
    ring
  have hAx : ∀ x : Euclid P, ‖inner ℝ x a • e - inner ℝ x e • a‖ = ‖Q.starProjection x‖ := by
    intro x
    rw [hproj x]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((hnormA _ _).trans (hnormP _ _).symm)
  -- Step 5: part (a)
  refine ⟨fun T x => ⟨(T.norm_starProjection_apply_le _).trans (hAx x).le,
    Q.norm_starProjection_apply_le x⟩, fun t α ht hα => ?_⟩
  -- Step 6: part (b)
  obtain ⟨hα₁, hα₂⟩ := abs_lt.1 hα
  have hcos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨hα₁, hα₂⟩
  have hx₀Q : t • (Real.cos α • a + Real.sin α • e) ∈ Q :=
    Q.smul_mem t (Q.add_mem (Q.smul_mem _ haQ) (Q.smul_mem _ heQ))
  have hx₀a : inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a = t * Real.cos α := by
    simp only [real_inner_smul_left, inner_add_left, haa, hea]
    ring
  have hx₀e : inner ℝ (t • (Real.cos α • a + Real.sin α • e)) e = t * Real.sin α := by
    simp only [real_inner_smul_left, inner_add_left, hee, hae]
    ring
  have hx₀n : ‖t • (Real.cos α • a + Real.sin α • e)‖ = t := by
    have h1 : ‖Real.cos α • a + Real.sin α • e‖ = 1 :=
      (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1
        (by rw [hnormP, Real.cos_sq_add_sin_sq, one_pow])
    rw [norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨⟨?_, hx₀n, ?_, Submodule.starProjection_eq_self_iff.2 hx₀Q, ?_⟩, ?_⟩
  · rw [hx₀a]
    exact mul_pos ht hcos
  · rw [hx₀a, hx₀e, mul_div_mul_left _ _ ht.ne', ← Real.tan_eq_sin_div_cos,
      Real.arctan_tan hα₁ hα₂]
  · rw [Submodule.starProjection_eq_self_iff.2 (Q.sub_mem (Q.smul_mem _ heQ) (Q.smul_mem _ haQ)),
      hAx, Submodule.starProjection_eq_self_iff.2 hx₀Q, hx₀n]
  -- Steps 7–8: part (c)
  · intro x hxa hxt hxα hne
    refine not_le.1 fun hlt => ?_
    have hπx : ‖Q.starProjection x‖ = ‖x‖ :=
      le_antisymm (Q.norm_starProjection_apply_le x) (by rw [hxt]; exact hlt)
    have hx : x = inner ℝ x a • a + inner ℝ x e • e := by
      rw [← hproj x,
        Submodule.starProjection_eq_self_iff.2 ((Q.mem_iff_norm_starProjection x).2 hπx)]
    have huv : inner ℝ x a ^ 2 + inner ℝ x e ^ 2 = t ^ 2 := by
      rw [← hnormP, ← hx, hxt]
    have hu0 : inner ℝ x a ≠ 0 := hxa.ne'
    have hsqrt : √(1 + (inner ℝ x e / inner ℝ x a) ^ 2) = t / inner ℝ x a := by
      rw [← Real.sqrt_sq (div_pos ht hxa).le]
      congr 1
      field_simp
      linarith [huv]
    have hcosα : Real.cos α = inner ℝ x a / t := by
      rw [← hxα, Real.cos_arctan, hsqrt, one_div_div]
    have hsinα : Real.sin α = inner ℝ x e / t := by
      rw [← hxα, Real.sin_arctan, hsqrt]
      field_simp
    apply hne
    rw [hcosα, hsinα, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ ht.ne',
      mul_div_cancel₀ _ ht.ne']
    exact hx
/-- **Fibre-count arithmetic** (Simon 7.3.3, cone-sector endpoint density: integrality of the
fibre multiplicity).  Let `θ : ι → ℕ`, `w : ι → ℝ` and `t > 0` with `w i ≤ t` for all `i`, and
`∑' i, θ i · ofReal (w i) = ofReal (m t)` in `[0, ∞]`.  Then `m ≤ ∑' i, θ i`.  If moreover every
`θ i ≥ 1`, `θ i₀ = k`, `w i₀ = t` and `w i < t` for `i ≠ i₀`, then `k ≤ m`, and `k < m` gives
`m + 1 ≤ ∑' i, θ i`: a finite total multiplicity forces `ι` to be finite, and the terms off `i₀`
are strictly below `θ i · ofReal t`. -/
theorem Submission.idtp_cse_fc_tsum_count_arith : ∀ (ι : Type) (θ : ι → ℕ) (w : ι → ℝ) (t : ℝ) (m : ℕ), 0 < t → (∀ i, w i ≤ t) → ∑' i, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) = ENNReal.ofReal ((m : ℝ) * t) → (m : ℝ≥0∞) ≤ ∑' i, (θ i : ℝ≥0∞) ∧ ∀ (i₀ : ι) (k : ℕ), (∀ i, 1 ≤ θ i) → θ i₀ = k → w i₀ = t → (∀ i, i ≠ i₀ → w i < t) → k ≤ m ∧ (k < m → (m : ℝ≥0∞) + 1 ≤ ∑' i, (θ i : ℝ≥0∞)) := by
  intro ι θ w t m ht hw hsum
  -- `τ = ofReal t ∈ (0, ∞)`, and the hypothesis reads `H = m τ`
  have hτ0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have hτ : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast] at hsum
  -- (i): termwise `θ i ofReal (w i) ≤ θ i τ`, so `m τ = H ≤ N τ`
  have hN : ∑' i, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) ≤
      (∑' i, (θ i : ℝ≥0∞)) * ENNReal.ofReal t := by
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_le_tsum fun i => by gcongr; exact hw i
  refine ⟨(ENNReal.mul_le_mul_iff_left hτ0 hτ).mp (hsum ▸ hN), ?_⟩
  intro i₀ k hθ1 hk hw0 hlt
  -- (ii) `k ≤ m`: the `i₀` term `k τ` is at most `H = m τ`
  have hkτ : (k : ℝ≥0∞) * ENNReal.ofReal t ≤ (m : ℝ≥0∞) * ENNReal.ofReal t := by
    rw [← hsum, ← hk, ← hw0]
    exact ENNReal.le_tsum (f := fun i => (θ i : ℝ≥0∞) * ENNReal.ofReal (w i)) i₀
  refine ⟨by exact_mod_cast (ENNReal.mul_le_mul_iff_left hτ0 hτ).mp hkτ, fun hkm => ?_⟩
  -- if `N = ∞` there is nothing to prove; otherwise `ι` is finite, as every `θ i ≥ 1`
  by_cases hNtop : ∑' i, (θ i : ℝ≥0∞) = ∞
  · rw [hNtop]
    exact le_top
  have hfin : {i : ι | (1 : ℝ≥0∞) ≤ θ i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hNtop one_ne_zero
  have huniv : {i : ι | (1 : ℝ≥0∞) ≤ θ i} = univ :=
    eq_univ_of_forall fun i => by exact_mod_cast hθ1 i
  rw [huniv] at hfin
  have : Finite ι := finite_univ_iff.mp hfin
  cases nonempty_fintype ι
  classical
  rw [tsum_fintype] at hsum ⊢
  -- split off the `i₀` term of `H` and of `N τ`
  have hsplitH : (θ i₀ : ℝ≥0∞) * ENNReal.ofReal (w i₀) +
      ∑ i ∈ Finset.univ.erase i₀, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) =
      ∑ i, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) :=
    Finset.add_sum_erase _ (fun i => (θ i : ℝ≥0∞) * ENNReal.ofReal (w i)) (Finset.mem_univ i₀)
  have hsplitN : (θ i₀ : ℝ≥0∞) * ENNReal.ofReal t +
      ∑ i ∈ Finset.univ.erase i₀, (θ i : ℝ≥0∞) * ENNReal.ofReal t =
      ∑ i, (θ i : ℝ≥0∞) * ENNReal.ofReal t :=
    Finset.add_sum_erase _ (fun i => (θ i : ℝ≥0∞) * ENNReal.ofReal t) (Finset.mem_univ i₀)
  -- `E = ι \ {i₀}` is nonempty, since otherwise `k τ = m τ`, i.e. `k = m`
  have hE : (Finset.univ.erase i₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    rw [← hsplitH, hE, Finset.sum_empty, add_zero, hk, hw0, ENNReal.mul_left_inj hτ0 hτ] at hsum
    exact hkm.ne (by exact_mod_cast hsum)
  -- each remaining term is strictly below `θ i τ`, so `m τ < N τ`
  have hstrict : ∑ i ∈ Finset.univ.erase i₀, (θ i : ℝ≥0∞) * ENNReal.ofReal (w i) <
      ∑ i ∈ Finset.univ.erase i₀, (θ i : ℝ≥0∞) * ENNReal.ofReal t := by
    refine ENNReal.sum_lt_sum_of_nonempty hE fun i hi => ?_
    have hθi : (θ i : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hθ1 i))
    exact ENNReal.mul_lt_mul_right hθi (ENNReal.natCast_ne_top _)
      ((ENNReal.ofReal_lt_ofReal_iff ht).mpr (hlt i (Finset.ne_of_mem_erase hi)))
  have hmN : (m : ℝ≥0∞) * ENNReal.ofReal t < (∑ i, (θ i : ℝ≥0∞)) * ENNReal.ofReal t := by
    rw [← hsum, ← hsplitH, Finset.sum_mul, ← hsplitN, hw0]
    exact ENNReal.add_lt_add_left (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hτ) hstrict
  -- `N` is the natural number `∑ i, θ i`, so `m < N` gives `m + 1 ≤ N`
  have hmN' : m < ∑ i, θ i := by exact_mod_cast (ENNReal.mul_lt_mul_iff_left hτ0 hτ).mp hmN
  exact_mod_cast hmN'

/-- Pointwise fibre count for the density at the edge of a planar sector of a `2`-dimensional
minimizing cone (part of the classification of such cones used in the proof of Simon 7.3.3(1),
which the book cites to [Whi82]).  Let `p = (t, α)` with `|t − 1| < s`, `|α| < s ≤ 1/4`, let `X(p) = M ∩ Z_s ∩ F̃⁻¹{p}` be the fibre of
`F̃(x) = (|x|, arctan(⟨x, e⟩/⟨x, a⟩))` and weight its points by `w(x) = |p_{TₓM}(Ax)|`,
`Ax = ⟨x, a⟩e − ⟨x, e⟩a`.  Every fibre point has `|x| = t` and `w(x) ≤ |πx| ≤ t`, so
`Σ θ w = mt` forces `Σ θ ≥ m`.  If `x_Q(p) = t(cos α a + sin α e) ∈ M` has multiplicity `k` and
`T_{x_Q(p)}M = Q`, it is a fibre point of weight `t` and every other fibre point has weight `< t`,
so `k ≤ m`, and `Σ θ ≥ m + 1` if `k < m`.  The planar facts are
`idtp_cse_fc_planar_fibre_geometry`; the counting is `idtp_cse_fc_tsum_count_arith`. -/
theorem Submission.idtp_cse_fc_fibre_pointwise : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (m k : ℕ) (p : ℝ × ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → s ≤ 1 / 4 → |p.1 - 1| < s → |p.2| < s → ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) * ENNReal.ofReal ‖(approxTangentPlane 2 R.carrier (x : Euclid P)).starProjection (inner ℝ (x : Euclid P) a • e - inner ℝ (x : Euclid P) e • a)‖ = ENNReal.ofReal ((m : ℝ) * p.1) → (m : ℝ≥0∞) ≤ ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) ∧ ((p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) ∈ R.carrier → R.mult (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = k → approxTangentPlane 2 R.carrier (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = Q → k ≤ m ∧ (k < m → (m : ℝ≥0∞) + 1 ≤ ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞))) := by
  intro P R Q a e s m k p hQ haQ heQ ha he hae hs hs4 hp1 hp2 hH
  obtain ⟨hA, hB⟩ := Submission.idtp_cse_fc_planar_fibre_geometry P Q a e hQ haQ heQ ha he hae
  -- `t = p.1 > 0` and `|α| = |p.2| < 1/4 < π/2`
  have ht : 0 < p.1 := by linarith [(abs_lt.mp hp1).1]
  have hα : |p.2| < Real.pi / 2 := by linarith [Real.two_le_pi]
  obtain ⟨⟨hx0a, hx0n, hx0f, hx0Q, hx0w⟩, hlt⟩ := hB p.1 p.2 ht hα
  -- a fibre point `x` has `|x| = t` and `f(x) = α`, hence weight `w(x) ≤ |πx| ≤ t`
  have hfib : ∀ x : Euclid P, (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) = p →
      ‖x‖ = p.1 ∧ Real.arctan (inner ℝ x e / inner ℝ x a) = p.2 := fun x hx =>
    ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have hw : ∀ i : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}),
      ‖(approxTangentPlane 2 R.carrier (i : Euclid P)).starProjection
        (inner ℝ (i : Euclid P) a • e - inner ℝ (i : Euclid P) e • a)‖ ≤ p.1 := fun i =>
    ((hA (approxTangentPlane 2 R.carrier i) i).1.trans (hA Q i).2).trans (hfib i i.2.2).1.le
  -- `m ≤ N(p)`
  obtain ⟨hmN, hcount⟩ := Submission.idtp_cse_fc_tsum_count_arith _ _ _ p.1 m ht hw hH
  refine ⟨hmN, fun hx0M hx0k hx0T => ?_⟩
  -- `x_Q(p)` is a fibre point of weight `t`, every other fibre point has weight `< t`
  refine hcount ⟨p.1 • (Real.cos p.2 • a + Real.sin p.2 • e), ⟨hx0M, hx0a, ?_, ?_, ?_⟩, ?_⟩ k
    (fun i => R.mult_pos _ i.2.1.1) hx0k ?_ fun i hi => ?_
  · rw [hx0n]; exact hp1
  · rw [hx0f]; exact hp2
  · rw [hx0Q, sub_self, norm_zero, hx0n]; exact mul_pos hs ht
  · exact Prod.ext hx0n hx0f
  · show ‖(approxTangentPlane 2 R.carrier _).starProjection _‖ = p.1
    rw [hx0T]; exact hx0w
  · obtain ⟨hin, hif⟩ := hfib i i.2.2
    exact (hA (approxTangentPlane 2 R.carrier i) i).1.trans_lt
      (hlt i i.2.1.2.1 hin hif fun h => hi (Subtype.ext h))
/-- **Lower bound for `∫⁻ N` over the square** `Sq = (1 − r, 1 + r) × (−r, r)` (parent step 5).
Let `U = {p : p₂ > 0}` and `g = m + 1_U`.  The two hypotheses give `g ≤ N` a.e. on `Sq`, so
`∫⁻_{Sq} N ≥ ∫⁻_{Sq} g = m·λ(Sq) + λ(U ∩ Sq)` (`U` is measurable, so `lintegral_add_left` and
`lintegral_indicator_one` apply; `N` itself need not be measurable).  Since `r > 0`,
`U ∩ Sq = (1 − r, 1 + r) × (0, r)`, and `Measure.prod_prod` with `Real.volume_Ioo` gives
`λ(Sq) = 4r²` and `λ(U ∩ Sq) = 2r²`.  Hence `∫⁻_{Sq} g = 4m r² + 2r² = (4m + 2) r²`. -/
theorem Submission.idtp_cse_fc_square_lintegral_lower : ∀ (N : ℝ × ℝ → ℝ≥0∞) (m : ℕ) (r : ℝ), 0 < r → (∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r → (m : ℝ≥0∞) ≤ N p) → (∀ᵐ p : ℝ × ℝ, p ∈ Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r → 0 < p.2 → (m : ℝ≥0∞) + 1 ≤ N p) → ENNReal.ofReal ((4 * (m : ℝ) + 2) * r ^ 2) ≤ ∫⁻ p in Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r, N p := by
  intro N m r hr hm hm1
  -- Measurability of `Sq` and of `U = {p₂ > 0}`.
  have hSq : MeasurableSet (Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r : Set (ℝ × ℝ)) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hU : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  -- `g = m + 1_U ≤ N` a.e. on `Sq`.
  have hg : ∀ᵐ p ∂(volume.restrict (Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r)),
      (m : ℝ≥0∞) + {p : ℝ × ℝ | 0 < p.2}.indicator 1 p ≤ N p := by
    rw [ae_restrict_iff' hSq]
    filter_upwards [hm, hm1] with p hp hp1 hpSq
    by_cases hp2 : 0 < p.2
    · rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | 0 < p.2} from hp2), Pi.one_apply]
      exact hp1 hpSq hp2
    · rw [indicator_of_notMem (show p ∉ {p : ℝ × ℝ | 0 < p.2} from hp2), add_zero]
      exact hp hpSq
  -- `U ∩ Sq = (1 − r, 1 + r) × (0, r)`, and the two volumes.
  have hUSq : {p : ℝ × ℝ | 0 < p.2} ∩ Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r =
      Ioo (1 - r) (1 + r) ×ˢ Ioo 0 r := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨h2, h1, -, h2r⟩
      exact ⟨h1, h2, h2r⟩
    · rintro ⟨h1, h2, h2r⟩
      exact ⟨h2, h1, by linarith, h2r⟩
  have hSqvol : volume (Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r : Set (ℝ × ℝ)) =
      ENNReal.ofReal (4 * r ^ 2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  have hUvol : volume (Ioo (1 - r) (1 + r) ×ˢ Ioo 0 r : Set (ℝ × ℝ)) =
      ENNReal.ofReal (2 * r ^ 2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  -- `∫⁻_{Sq} g = m·λ(Sq) + λ(U ∩ Sq) = (4m + 2) r² ≤ ∫⁻_{Sq} N`.
  calc ENNReal.ofReal ((4 * (m : ℝ) + 2) * r ^ 2)
      = (m : ℝ≥0∞) * ENNReal.ofReal (4 * r ^ 2) + ENNReal.ofReal (2 * r ^ 2) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = ∫⁻ p in Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r,
          ((m : ℝ≥0∞) + {p : ℝ × ℝ | 0 < p.2}.indicator 1 p) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_indicator_one hU,
          Measure.restrict_apply hU, hUSq, hSqvol, hUvol]
    _ ≤ ∫⁻ p in Ioo (1 - r) (1 + r) ×ˢ Ioo (-r) r, N p := lintegral_mono_ae hg

/-- **Upper bound for the fibre Jacobian over `Z(s, s')`** (step 6 of the fibre count in the proof
of Simon 7.3.3).  Write `π = p_Q`, `Ax = ⟨x, a⟩e − ⟨x, e⟩a` and `J(x) = |p_{TₓM}(Ax)| / |πx|²`.  At
`μ`-a.e. `x ∈ Z(s, s')` the localization hypothesis gives `|x − πx| < (s'/4)|x|`, so
`|πx| > (1 − s'/4)(1 − s') ≥ 1 − 2s' > 0`.  Since `|p_{TₓM}(Ax)| ≤ |πx|`
(`idtp_cse_fc_planar_fibre_geometry`), `J(x) ≤ 1/|πx| ≤ 1/(1 − 2s')`; integrate this constant
bound over `Z(s, s')`. -/
theorem Submission.idtp_cse_fc_jacobian_upper : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (S : Set (Euclid P)) (s s' : ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ᵐ x ∂R.measure, x ∈ S) → 0 < s' → s' ≤ 1 / 4 → (∀ x ∈ S, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ < s * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖) → ∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ / ‖Q.starProjection x‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (1 / (1 - 2 * s')) * R.measure {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} := by
  intro P R Q a e S s s' hQ ha he ha1 he1 hae hS hs' hs'4 hloc
  -- `|p_T(Ax)| ≤ |πx|` for every plane `T` (planar geometry (a))
  have hw := (Submission.idtp_cse_fc_planar_fibre_geometry P Q a e hQ ha he ha1 he1 hae).1
  -- compare with the constant `ofReal (1 / (1 - 2s'))`, a.e. on `Z(s, s')`
  refine (setLIntegral_mono_ae aemeasurable_const (hS.mono fun x hxS hxZ => ?_)).trans_eq
    (setLIntegral_const _ _)
  obtain ⟨hxa, hx1, hxf, hxs⟩ := hxZ
  -- localization at `x ∈ S ∩ Z(s, s')`, and `|x| > 1 - s'`
  have hxπ := hloc x hxS hxa hx1 hxf hxs
  have hx : 1 - s' < ‖x‖ := by linarith [(abs_lt.mp hx1).1]
  -- `|πx| ≥ |x| - |x - πx| > (1 - s'/4)|x| > (1 - s'/4)(1 - s') ≥ 1 - 2s' > 0`
  have htri : ‖x‖ - ‖x - Q.starProjection x‖ ≤ ‖Q.starProjection x‖ := by
    simpa using norm_sub_norm_le x (x - Q.starProjection x)
  have h2s' : 0 < 1 - 2 * s' := by linarith
  have hπ : 1 - 2 * s' < ‖Q.starProjection x‖ := by
    nlinarith [mul_lt_mul_of_pos_left hx (show 0 < 1 - s' / 4 by linarith)]
  have hπ0 : 0 < ‖Q.starProjection x‖ := h2s'.trans hπ
  -- `J(x) ≤ |πx| / |πx|² = 1 / |πx| ≤ 1 / (1 - 2s')`
  refine ENNReal.ofReal_le_ofReal ?_
  calc _ ≤ ‖Q.starProjection x‖ / ‖Q.starProjection x‖ ^ 2 := by
        gcongr
        exact (hw _ x).1
    _ = 1 / ‖Q.starProjection x‖ := by field_simp
    _ ≤ 1 / (1 - 2 * s') := one_div_le_one_div_of_le h2s' hπ.le

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
