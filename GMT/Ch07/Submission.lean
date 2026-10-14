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

/-- `Hⁿ(Q ∩ B_ρ(y)) = ωₙρⁿ` for an `n`-dimensional linear subspace `Q` of `ℝᴾ`, `y ∈ Q` and
`ρ > 0` (used in the proof of Simon 7.3.3(1), p. 191, for the density of the planes of a
2-dimensional minimizing cone).  The inclusion `Q → ℝᴾ` is an isometry, so `Q ∩ B_ρ(y)` has the
measure of the ball `B_ρ(y)` of `Q`; on `Q`, `μHE[n]` is the volume, Haar scaling gives
`vol(B_ρ(y)) = ρⁿ vol(B_1(0))`, and orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume, so
`vol(B_1(0)) = ωₙ`. -/
theorem Submission.idtp_tdc_subspace_ball_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (y : Euclid P) (ρ : ℝ), Module.finrank ℝ Q = n → y ∈ Q → 0 < ρ → μHE[n] ((Q : Set (Euclid P)) ∩ ball y ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) := by
  intro P n Q y ρ hn hy hρ
  subst hn
  -- the inclusion `Q → ℝᴾ` is an isometry with range `Q`; `B_ρ(y)` pulls back to the ball of `Q`
  have hball : μHE[Module.finrank ℝ Q] ((Q : Set (Euclid P)) ∩ ball y ρ) =
      μHE[Module.finrank ℝ Q] (ball (⟨y, hy⟩ : Q) ρ) := by
    rw [← isometry_subtype_coe.preimage_ball (⟨y, hy⟩ : Q) ρ,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage, Subtype.range_coe, Set.inter_comm]
  -- orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume and map `B_1(0)` onto `B_1(0)`
  have hunit := (stdOrthonormalBasis ℝ Q).measurePreserving_repr.measure_preimage
    (measurableSet_ball (x := (0 : Euclid (Module.finrank ℝ Q))) (ε := 1)).nullMeasurableSet
  rw [LinearIsometryEquiv.preimage_ball, map_zero] at hunit
  -- `μHE[n] = volume` on `Q`, then Haar scaling of balls
  rw [hball, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, hunit, mul_comm]
  rfl

/-- A measure `m` on `ℝᴾ` carried by an `n`-dimensional linear subspace `V`, finite on compact
sets and invariant under the translations by `V`, is a constant multiple of `Hⁿ⌞V` (used for the
product structure of translation invariant measures in the integer multiplicity part of Simon
7.2.4, Remark 7.2.5(1)).  The orthogonal projection `π : ℝᴾ → V` pushes `m` forward to a
translation invariant measure on `V`, finite on compact sets, hence `c • vol_V` by uniqueness of
Haar measure.  As `m` is carried by `V`, it is the image of `π_# m` under the inclusion
`V → ℝᴾ`, an isometry, and `μHE[n] = vol_V` on `V`. -/
theorem Submission.cbr_ci_cp_prod_subspace_haar : ∀ (P n : ℕ) (m : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → m (V : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → m K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → m ((fun x => v + x) ⁻¹' A) = m A) → ∃ c : ℝ≥0∞, m = c • (μHE[n]).restrict (V : Set (Euclid P)) := by
  intro P n m V hn hVc hcpt hinv
  subst hn
  -- the orthogonal projection `π` onto `V` fixes `V` pointwise
  have hπ : ∀ x ∈ V, ((V.orthogonalProjectionOnto x : V) : Euclid P) = x := fun x hx => by
    simpa using congrArg Subtype.val (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩)
  have hπm : Measurable V.orthogonalProjectionOnto :=
    V.orthogonalProjectionOnto.continuous.measurable
  -- invariance of `m` under the translations by `V`, as an identity of measures
  have htr : ∀ v ∈ V, m.map (fun x => v + x) = m := fun v hv => by
    ext A hA
    rw [Measure.map_apply (measurable_const_add v) hA, hinv v hv A hA]
  -- `m' = π_# m` is translation invariant on `V`, as `(g + ·) ∘ π = π ∘ (g + ·)` for `g ∈ V`
  set m' : Measure V := m.map V.orthogonalProjectionOnto with hm'
  have hinv' : m'.IsAddLeftInvariant := ⟨fun g => by
    have hcomm : (fun x : V => g + x) ∘ V.orthogonalProjectionOnto =
        V.orthogonalProjectionOnto ∘ (fun x => (g : Euclid P) + x) := by
      funext x; simp
    rw [hm', Measure.map_map (measurable_const_add g) hπm, hcomm,
      ← Measure.map_map hπm (measurable_const_add _), htr _ g.2]⟩
  -- `m'` is finite on compact sets, as `π⁻¹ K ⊆ ι K ∪ Vᶜ` and `m Vᶜ = 0`
  have hfin' : IsFiniteMeasureOnCompacts m' := ⟨fun K hK => by
    rw [hm', Measure.map_apply hπm hK.isClosed.measurableSet]
    calc m (V.orthogonalProjectionOnto ⁻¹' K)
        ≤ m (Subtype.val '' K ∪ (V : Set (Euclid P))ᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hxV : x ∈ V
          · exact Or.inl ⟨_, hx, hπ x hxV⟩
          · exact Or.inr hxV
      _ ≤ m (Subtype.val '' K) + m (V : Set (Euclid P))ᶜ := measure_union_le _ _
      _ < ∞ := by
          rw [hVc, add_zero]
          exact hcpt _ (hK.image continuous_subtype_val)⟩
  -- uniqueness of Haar measure on `V`
  obtain ⟨c, hc⟩ : ∃ c : NNReal, m' = c • (volume : Measure V) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul m' volume⟩
  -- `m = ι_# m'` for the inclusion `ι : V → ℝᴾ`, as `ι ∘ π = id` on `V`, which carries `m`
  have hm : m = m'.map Subtype.val := by
    rw [hm', Measure.map_map continuous_subtype_val.measurable hπm]
    conv_lhs => rw [← Measure.map_id (μ := m)]
    refine Measure.map_congr (measure_mono_null (fun x hx => ?_) hVc)
    exact fun hxV => hx (hπ x hxV).symm
  -- `ι_# vol_V = Hⁿ⌞V`, as `μHE[n] = vol_V` on `V` and `ι` is an isometry with range `V`
  have hvol : (volume : Measure V).map Subtype.val =
      (μHE[Module.finrank ℝ V]).restrict (V : Set (Euclid P)) := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      isometry_subtype_coe.map_euclideanHausdorffMeasure, Subtype.range_coe]
  refine ⟨c, ?_⟩
  rw [hm, hc, Measure.map_smul _ continuous_subtype_val.aemeasurable, hvol,
    Measure.coe_nnreal_smul]

/-- Let `ν` be a measure on `ℝᴾ`, finite on compact sets and invariant under the translations by
an `n`-dimensional linear subspace `V`, and let `p`, `q` be the orthogonal projections onto `V`
and `Vᗮ`.  Then `ν(p⁻¹ A ∩ q⁻¹ B) = σ(B) Hⁿ(A ∩ V)` for all Borel `A`, `B`, for a measure `σ`
carried by `Vᗮ` and finite on compact sets (used for the product structure of translation
invariant measures in the integer multiplicity part of Simon 7.2.4, Remark 7.2.5(1)).  Take
`σ = ωₙ⁻¹ q_#(ν⌞p⁻¹ B_1(0))`.  For bounded `B`, `p_#(ν⌞q⁻¹ B)` is carried by `V`, finite on
compact sets and invariant under the translations by `V`, hence equal to `c Hⁿ⌞V`; evaluating at
`B_1(0)`, where `Hⁿ(V ∩ B_1(0)) = ωₙ`, gives `c = σ(B)`.  Exhausting `B` by the bounded sets
`B ∩ B_j(0)` gives the general case. -/
theorem Submission.cbr_ci_cp_prod_rectangle_formula : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → ∃ σ : Measure (Euclid P), σ (Vᗮ : Set (Euclid P))ᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) ∧ ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ (V : Set (Euclid P))) := by
  intro P n ν V hn hcpt hinv
  -- `p = V.starProjection` and `q = Vᗮ.starProjection` are continuous linear, hence measurable
  have hpm : Measurable V.starProjection := V.starProjection.continuous.measurable
  have hqm : Measurable Vᗮ.starProjection := Vᗮ.starProjection.continuous.measurable
  -- for `v ∈ V`, `p (v + y) = v + p y` and `q (v + y) = q y`
  have hpv : ∀ v ∈ V, ∀ y, V.starProjection (v + y) = v + V.starProjection y := fun v hv y => by
    rw [map_add, Submodule.starProjection_eq_self_iff.2 hv]
  have hqv : ∀ v ∈ V, ∀ y, Vᗮ.starProjection (v + y) = Vᗮ.starProjection y := fun v hv y => by
    rw [map_add, Submodule.starProjection_orthogonal_apply_eq_zero hv, zero_add]
  -- boxes `{y : p y ∈ E, q y ∈ F}` with `E`, `F` bounded lie in a compact ball, as `y = p y + q y`
  have hbox : ∀ E F : Set (Euclid P), Bornology.IsBounded E → Bornology.IsBounded F →
      ν (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' F) < ∞ := by
    intro E F hE hF
    obtain ⟨R, hR⟩ := hE.subset_closedBall 0
    obtain ⟨S, hS⟩ := hF.subset_closedBall 0
    refine lt_of_le_of_lt (measure_mono fun y hy => ?_) (hcpt _ (isCompact_closedBall 0 (R + S)))
    rw [mem_closedBall_zero_iff, ← V.starProjection_add_starProjection_orthogonal y]
    exact (norm_add_le _ _).trans
      (add_le_add (mem_closedBall_zero_iff.1 (hR hy.1)) (mem_closedBall_zero_iff.1 (hS hy.2)))
  -- `Hⁿ(B_1(0) ∩ V) = ωₙ`, and `0 < ωₙ < ∞`
  have hω : μHE[n] (ball (0 : Euclid P) 1 ∩ V) = unitBallVolume n := by
    rw [Set.inter_comm, Submission.idtp_tdc_subspace_ball_measure P n V 0 1 hn V.zero_mem one_pos]
    simp
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- `σ = ωₙ⁻¹ q_#(ν⌞p⁻¹ B_1(0))`, so `σ(B) = ωₙ⁻¹ ν(q⁻¹ B ∩ p⁻¹ B_1(0))` for Borel `B`
  obtain ⟨σ, hσB⟩ : ∃ σ : Measure (Euclid P), ∀ B, MeasurableSet B → σ B =
      (unitBallVolume n)⁻¹ * ν (Vᗮ.starProjection ⁻¹' B ∩ V.starProjection ⁻¹' ball 0 1) :=
    ⟨(unitBallVolume n)⁻¹ • (ν.restrict (V.starProjection ⁻¹' ball 0 1)).map Vᗮ.starProjection,
      fun B hB => by
        rw [Measure.smul_apply, Measure.map_apply hqm hB, Measure.restrict_apply (hqm hB),
          smul_eq_mul]⟩
  -- the rectangle formula for bounded Borel `B`
  have hbdd : ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → Bornology.IsBounded B →
      ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ V) := by
    intro A B hA hB hBb
    -- `m = p_#(ν⌞q⁻¹ B)`, with `m(E) = ν(p⁻¹ E ∩ q⁻¹ B)` for Borel `E`
    obtain ⟨m, hmE⟩ : ∃ m : Measure (Euclid P), ∀ E, MeasurableSet E →
        m E = ν (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' B) :=
      ⟨(ν.restrict (Vᗮ.starProjection ⁻¹' B)).map V.starProjection, fun E hE => by
        rw [Measure.map_apply hpm hE, Measure.restrict_apply (hpm hE)]⟩
    -- `m` is carried by `V`, as `p y ∈ V`
    have hmV : m (V : Set (Euclid P))ᶜ = 0 := by
      rw [hmE _ (Submodule.closed_of_finiteDimensional V).measurableSet.compl]
      exact measure_mono_null (fun y hy => absurd (V.starProjection_apply_mem y) hy.1) measure_empty
    -- `m` is finite on compact sets, as compact sets are bounded
    have hmcpt : ∀ K : Set (Euclid P), IsCompact K → m K < ∞ := fun K hK => by
      rw [hmE K hK.isClosed.measurableSet]
      exact hbox K B hK.isBounded hBb
    -- `m` is invariant under the translations by `V`, as `ν` is
    have hminv : ∀ v ∈ V, ∀ E : Set (Euclid P), MeasurableSet E →
        m ((fun x => v + x) ⁻¹' E) = m E := by
      intro v hv E hE
      have hpre : V.starProjection ⁻¹' ((fun x => v + x) ⁻¹' E) ∩ Vᗮ.starProjection ⁻¹' B =
          (fun x => v + x) ⁻¹' (V.starProjection ⁻¹' E ∩ Vᗮ.starProjection ⁻¹' B) := by
        ext y
        simp only [mem_inter_iff, mem_preimage, hpv v hv, hqv v hv]
      rw [hmE _ (hE.preimage (measurable_const_add v)), hmE E hE, hpre,
        hinv v hv _ ((hpm hE).inter (hqm hB))]
    -- `m = c • Hⁿ⌞V`; evaluating at `B_1(0)` gives `c = σ(B)`
    obtain ⟨c, hc⟩ := Submission.cbr_ci_cp_prod_subspace_haar P n m V hn hmV hmcpt hminv
    have hball : ν (V.starProjection ⁻¹' ball 0 1 ∩ Vᗮ.starProjection ⁻¹' B) =
        unitBallVolume n * c := by
      rw [← hmE (ball 0 1) measurableSet_ball, hc, Measure.smul_apply,
        Measure.restrict_apply measurableSet_ball, hω, smul_eq_mul, mul_comm]
    have hσc : σ B = c := by
      rw [hσB B hB, Set.inter_comm, hball, ENNReal.inv_mul_cancel_left hω0 hωtop]
    rw [← hmE A hA, hc, Measure.smul_apply, Measure.restrict_apply hA, hσc, smul_eq_mul]
  refine ⟨σ, ?_, fun K hK => ?_, fun A B hA hB => ?_⟩
  · -- `σ` is carried by `Vᗮ`, as `q y ∈ Vᗮ`
    rw [hσB _ V.isClosed_orthogonal.measurableSet.compl,
      measure_mono_null (fun y hy => absurd (Vᗮ.starProjection_apply_mem y) hy.1) measure_empty,
      mul_zero]
  · -- `σ` is finite on compact sets, as compact sets are bounded and `ωₙ ≠ 0`
    rw [hσB K hK.isClosed.measurableSet, Set.inter_comm]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hω0))
      (hbox _ _ isBounded_ball hK.isBounded)
  · -- exhaust `B` by the bounded sets `B ∩ B_j(0)`, by continuity from below for `ν` and `σ`
    have hmono : Monotone fun j : ℕ => B ∩ ball (0 : Euclid P) j := fun i j hij =>
      inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
    have hU : ⋃ j : ℕ, B ∩ ball (0 : Euclid P) j = B := by
      rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
    have hmono' : Monotone fun j : ℕ =>
        V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' (B ∩ ball (0 : Euclid P) j) :=
      fun i j hij => inter_subset_inter_right _ (preimage_mono (hmono hij))
    have hνU := hmono'.measure_iUnion (μ := ν)
    have hσU := hmono.measure_iUnion (μ := σ)
    rw [← inter_iUnion, ← preimage_iUnion, hU] at hνU
    rw [hU] at hσU
    rw [hνU, hσU, ENNReal.iSup_mul]
    exact iSup_congr fun j => hbdd A _ hA (hB.inter measurableSet_ball)
      (isBounded_ball.subset inter_subset_right)
/-- If `σ` is carried by `Vᗮ` and finite on compact sets, and `ν` has the rectangle values
`ν(p⁻¹(A) ∩ q⁻¹(B)) = σ(B) Hⁿ(A ∩ V)` for Borel `A`, `B` (`p`, `q` the orthogonal projections onto
the `n`-dimensional subspace `V` and onto `Vᗮ`), then `ν(A) = ∫_V σ({y : t + y ∈ A}) dHⁿ(t)`, i.e.
`ν` is the image of `(Hⁿ⌞V) ⊗ σ` under `(t, y) ↦ t + y` (used, via the closure theorem, in the
proof of Simon 7.2.4).  The rectangles form a π-system generating the Borel sets (`y = p y + q y`),
the image measure takes the same values on them because `σ` is carried by `Vᗮ`, and the rectangles
over the balls `B_{j+1}(0)` cover `ℝᴾ` and have finite `ν`-measure, so the two measures agree. -/
theorem Submission.cbr_ci_cp_prod_of_rectangles : ∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) → (∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → ν (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B) = σ B * μHE[n] (A ∩ (V : Set (Euclid P)))) → ∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n] := by
  intro P n ν σ V hn hσ hσfin hrect A hA
  -- `σ` is finite on compact sets, hence locally finite and σ-finite on `ℝᴾ`
  have : IsFiniteMeasureOnCompacts σ := ⟨hσfin⟩
  have hp : Measurable V.starProjection := V.starProjection.continuous.measurable
  have hq : Measurable Vᗮ.starProjection := Vᗮ.starProjection.continuous.measurable
  have hV : MeasurableSet (V : Set (Euclid P)) := V.closed_of_finiteDimensional.measurableSet
  -- the candidate `λ = s_#((Hⁿ⌞V) ⊗ σ)` with `s(t, y) = t + y`
  have hs : Measurable fun z : Euclid P × Euclid P => z.1 + z.2 := measurable_fst.add measurable_snd
  have hlam : ∀ A : Set (Euclid P), MeasurableSet A →
      ((μHE[n].restrict (V : Set (Euclid P))).prod σ).map (fun z => z.1 + z.2) A =
        ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n] := by
    intro A hA
    rw [Measure.map_apply hs hA, Measure.prod_apply (hs hA)]
    rfl
  rw [← hlam A hA]
  congr 1
  -- rectangles `p⁻¹(A) ∩ q⁻¹(B)` form a π-system generating the Borel σ-algebra
  let C : Set (Set (Euclid P)) := {S | ∃ A B : Set (Euclid P), MeasurableSet A ∧ MeasurableSet B ∧
    S = V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B}
  have hgen : (inferInstance : MeasurableSpace (Euclid P)) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · have hp' : Measurable[MeasurableSpace.generateFrom C] V.starProjection := fun A hA =>
        MeasurableSpace.measurableSet_generateFrom ⟨A, univ, hA, MeasurableSet.univ, by
          rw [preimage_univ, inter_univ]⟩
      have hq' : Measurable[MeasurableSpace.generateFrom C] Vᗮ.starProjection := fun B hB =>
        MeasurableSpace.measurableSet_generateFrom ⟨univ, B, MeasurableSet.univ, hB, by
          rw [preimage_univ, univ_inter]⟩
      have hid := @Measurable.add _ _ _ _ (MeasurableSpace.generateFrom C)
        (fun y => V.starProjection y) (fun y => Vᗮ.starProjection y) _ hp' hq'
      have hfun : ((fun y => V.starProjection y) + fun y => Vᗮ.starProjection y) = id :=
        funext V.starProjection_add_starProjection_orthogonal
      rw [hfun] at hid
      exact fun S hS => hid hS
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      exact (hp hA).inter (hq hB)
  have hpi : IsPiSystem C := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by
      rw [preimage_inter, preimage_inter, inter_inter_inter_comm]⟩
  -- the rectangles `p⁻¹(B_{j+1}(0)) ∩ q⁻¹(B_{j+1}(0))` cover `ℝᴾ` and have finite `ν`-measure
  refine Measure.ext_of_generateFrom_of_iUnion C
    (fun j : ℕ => V.starProjection ⁻¹' ball 0 (j + 1) ∩ Vᗮ.starProjection ⁻¹' ball 0 (j + 1))
    hgen hpi ?_ ?_ ?_ ?_
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (max ‖V.starProjection y‖ ‖Vᗮ.starProjection y‖)
    exact ⟨j, mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt (hj.trans (lt_add_one _))),
      mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt (hj.trans (lt_add_one _)))⟩
  · exact fun j => ⟨_, _, measurableSet_ball, measurableSet_ball, rfl⟩
  · intro j
    rw [hrect _ _ measurableSet_ball measurableSet_ball, inter_comm,
      Submission.idtp_tdc_subspace_ball_measure P n V 0 (j + 1) hn V.zero_mem (by positivity)]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne
      (ENNReal.mul_ne_top (measure_ball_lt_top (μ := volume)).ne ENNReal.ofReal_ne_top)
  -- `ν` and `λ` agree on rectangles because `σ` is carried by `Vᗮ`
  · rintro _ ⟨A, B, hA, hB, rfl⟩
    rw [hrect A B hA hB, hlam _ ((hp hA).inter (hq hB))]
    have key : EqOn (fun t => σ ((fun y => t + y) ⁻¹'
        (V.starProjection ⁻¹' A ∩ Vᗮ.starProjection ⁻¹' B))) (A.indicator fun _ => σ B) V := by
      intro t ht
      have hsec : ∀ y ∈ (Vᗮ : Set (Euclid P)),
          V.starProjection (t + y) = t ∧ Vᗮ.starProjection (t + y) = y := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [map_add, V.starProjection_eq_self_iff.mpr ht,
            V.starProjection_apply_eq_zero_iff.mpr hy, add_zero]
        · rw [map_add, V.starProjection_orthogonal_apply_eq_zero ht,
            Vᗮ.starProjection_eq_self_iff.mpr hy, zero_add]
      simp only
      rw [← measure_inter_conull hσ]
      by_cases htA : t ∈ A
      · rw [indicator_of_mem htA, ← measure_inter_conull (s := B) hσ]
        congr 1
        ext y
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨⟨-, hyB⟩, hy⟩
          rw [(hsec y hy).2] at hyB
          exact ⟨hyB, hy⟩
        · rintro ⟨hyB, hy⟩
          rw [(hsec y hy).1, (hsec y hy).2]
          exact ⟨⟨htA, hyB⟩, hy⟩
      · rw [indicator_of_notMem htA]
        convert measure_empty (μ := σ)
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨⟨hyA, -⟩, hy⟩
        exact htA ((hsec y hy).1 ▸ hyA)
    rw [setLIntegral_congr_fun hV key, lintegral_indicator_const hA, Measure.restrict_apply hA]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
