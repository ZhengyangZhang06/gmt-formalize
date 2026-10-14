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

/-- **Truncated cone map** (Simon Ch. 6, 2.30: the cone `0 ⨯ T = h_#([[(0,1)]] × T)`,
`h(t, x) = tx`).  Put `ρ' = max ρ 1`, let `r(y) = φ(y) y` with `φ` a smooth bump that is `1` on
`B̄_{ρ'}(0)` and vanishes off `B_{ρ'+1}(0)`, and let `σ(s) = max 0 (min s 1)`.  Then
`H(z) = σ(z₀) r(G(tail z))` is Lipschitz, as a product of bounded Lipschitz factors (`|σ| ≤ 1`,
`‖r‖ ≤ ρ' + 1`).  On the open set `{z₀ ∈ (0,1), ‖G(tail z)‖ < ρ'}`, `H(z) = z₀ G(tail z)`, so
there `DH(z)v = z₀ DG(tail z)(tail v) + v₀ G(tail z)`, which on `ê₀` and `ê_{a+1}` gives the
`Fin.cons` tuple. -/
theorem Submission.dimred_cs_sos_cfs_cp_cone_map : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (L : NNReal) (ρ : ℝ), LipschitzWith L G → ∃ H : Euclid (n + 1) → Euclid P, (∃ K : NNReal, LipschitzWith K H) ∧ ∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ < ρ → H z = WithLp.ofLp z 0 • G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ (DifferentiableAt ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) → (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1))) := by
  intro P n G L ρ hG
  -- step 1: a Lipschitz, bounded `r` with `r = id` on `closedBall 0 ρ'`, `ρ' := max ρ 1`
  set ρ' : ℝ := max ρ 1 with hρ'
  have hρ'pos : 0 < ρ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨r, ⟨Kr, hKr⟩, hr_bound, hr_id⟩ : ∃ r : Euclid P → Euclid P, (∃ K : NNReal, LipschitzWith K r) ∧
      (∀ y, ‖r y‖ ≤ ρ' + 1) ∧ (∀ y : Euclid P, ‖y‖ ≤ ρ' → r y = y) := by
    let φ : ContDiffBump (0 : Euclid P) := ⟨ρ', ρ' + 1, hρ'pos, by linarith⟩
    refine ⟨fun y => φ y • y, ?_, ?_, ?_⟩
    · have hr_smooth : ContDiff ℝ 1 (fun y : Euclid P => φ y • y) := φ.contDiff.smul contDiff_id
      have hr_supp : HasCompactSupport (fun y : Euclid P => φ y • y) := φ.hasCompactSupport.smul_right
      exact ContDiff.lipschitzWith_of_hasCompactSupport hr_supp hr_smooth (by simp)
    · intro y
      by_cases hy : ‖y‖ < ρ' + 1
      · calc ‖φ y • y‖ = |φ y| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * (ρ' + 1) := by
            gcongr
            · rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
          _ = ρ' + 1 := one_mul _
      · have h0 : φ y = 0 := φ.zero_of_le_dist (by simpa [dist_zero_right] using not_lt.mp hy)
        simp [h0]; linarith
    · intro y hy
      have : φ y = 1 := φ.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy)
      simp [this]
  -- the clamp `σ(s) = max(0, min(s, 1))`
  obtain ⟨σ, hσ, hσb, hσid⟩ : ∃ σ : ℝ → ℝ, LipschitzWith 1 σ ∧ (∀ s, |σ s| ≤ 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, σ s = s := by
    refine ⟨fun s => max 0 (min s 1), (LipschitzWith.id.min_const 1).const_max 0, ?_, ?_⟩
    · intro s
      rw [abs_le]; constructor
      · have : (0 : ℝ) ≤ max 0 (min s 1) := le_max_left _ _
        linarith
      · exact max_le (by norm_num) (min_le_right _ _)
    · intro s hs
      simp only [min_eq_left hs.2.le, max_eq_right hs.1.le]
  -- coordinate maps `π₀ z = z₀`, `π' z = tail z`
  let π0 : Euclid (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hπ0 : ∀ z, π0 z = WithLp.ofLp z 0 := fun z => rfl
  let πtl : Euclid (n + 1) →ₗ[ℝ] Euclid n :=
    { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  let πt : Euclid (n + 1) →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap πtl
  have hπt : ∀ z, πt z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) := fun z => rfl
  -- step 2: the map `H(z) = σ(z₀) • r(G(tail z))`
  refine ⟨fun z => σ (WithLp.ofLp z 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))), ?_, ?_⟩
  · -- step 3(a): `H` is Lipschitz
    have h1 : LipschitzWith (1 * ‖π0‖₊) (fun z : Euclid (n + 1) => σ (WithLp.ofLp z 0)) :=
      hσ.comp π0.lipschitzWith
    have h2 : LipschitzWith (Kr * (L * ‖πt‖₊))
        (fun z : Euclid (n + 1) => r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))) :=
      hKr.comp (hG.comp πt.lipschitzWith)
    refine ⟨_, LipschitzWith.of_dist_le' (K := (ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) +
      ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) fun z z' => ?_⟩
    have e1 := h1.dist_le_mul z z'
    have e2 := h2.dist_le_mul z z'
    simp only [dist_eq_norm] at e1 e2 ⊢
    set a := σ (WithLp.ofLp z 0)
    set a' := σ (WithLp.ofLp z' 0)
    set R := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))
    set R' := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))
    have ha' : ‖a'‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (hσb _)
    calc ‖a • R - a' • R'‖ = ‖(a - a') • R + a' • (R - R')‖ := by
          congr 1; rw [sub_smul, smul_sub]; abel
      _ ≤ ‖a - a'‖ * ‖R‖ + ‖a'‖ * ‖R - R'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul (a - a') R, norm_smul a' (R - R')]
      _ ≤ (((1 * ‖π0‖₊ : NNReal) : ℝ) * ‖z - z'‖) * (ρ' + 1) +
            1 * (((Kr * (L * ‖πt‖₊) : NNReal) : ℝ) * ‖z - z'‖) := by
          gcongr
          exact hr_bound _
      _ = ((ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) + ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) *
            ‖z - z'‖ := by ring
  · -- step 4: value and derivative on `{z₀ ∈ (0,1), ‖G(tail z)‖ < ρ}`
    intro z hz hzρ
    let Ht : Euclid (n + 1) → Euclid P := fun z' => π0 z' • G (πt z')
    let O : Set (Euclid (n + 1)) := {z' | π0 z' ∈ Ioo (0 : ℝ) 1 ∧ ‖G (πt z')‖ < ρ'}
    have hO : IsOpen O :=
      (isOpen_Ioo.preimage π0.continuous).inter
        (isOpen_lt (continuous_norm.comp (hG.continuous.comp πt.continuous)) continuous_const)
    have hzO : z ∈ O := ⟨hz, lt_of_lt_of_le hzρ (le_max_left _ _)⟩
    have hEq : ∀ z' ∈ O, σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z')))) =
        Ht z' := by
      rintro z' ⟨h0, hρz⟩
      rw [hπ0] at h0
      rw [hπt] at hρz
      show _ = π0 z' • G (πt z')
      rw [hπ0, hπt, hσid _ h0, hr_id _ hρz.le]
    have hev : (fun z' : Euclid (n + 1) =>
        σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))) =ᶠ[𝓝 z] Ht :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hzO) hEq
    refine ⟨hEq z hzO, fun hGd => ?_⟩
    have hD : HasFDerivAt Ht (π0 z • (fderiv ℝ G (πt z)).comp πt + π0.smulRight (G (πt z))) z :=
      π0.hasFDerivAt.smul (hGd.hasFDerivAt.comp z πt.hasFDerivAt)
    rw [hev.fderiv_eq, hD.fderiv]
    have hs0 : π0 (EuclideanSpace.single 0 1) = 1 := by simp [π0]
    have hss : ∀ a : Fin n, π0 (EuclideanSpace.single a.succ 1) = 0 := by
      intro a; simp [π0, Fin.succ_ne_zero]
    have ht0 : πt (EuclideanSpace.single 0 1) = 0 := by
      rw [hπt]; ext j; simp [Fin.tail, Fin.succ_ne_zero]
    have hts : ∀ a : Fin n, πt (EuclideanSpace.single a.succ 1) = EuclideanSpace.single a 1 := by
      intro a; rw [hπt]; ext j; simp [Fin.tail]
    funext b
    refine Fin.cases ?_ (fun a => ?_) b
    · simp [hs0, ht0]
      rfl
    · simp [hss, hts]
      rfl
/-- Fubini–Tonelli on the cylinder `Â = {z ∈ ℝ^{n+1} : z₀ ∈ (0, 1), tail z ∈ A}` for Borel
`A ⊆ ℝⁿ`.  The map `e(u, t) = (t, u₁, …, uₙ)`, the composite of the swap `ℝⁿ × ℝ ≃ ℝ × ℝⁿ`,
`id × ofLp`, the inverse of `piFinSuccAbove · 0` (i.e. `Fin.cons`) and `toLp`, is a
measure-preserving measurable equivalence `ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}` with `e⁻¹(Â) = A × (0, 1)`.  Hence
`Â` is Borel, and change of variables along `e` followed by Tonelli (resp. Fubini) on the product
set `A × (0, 1)` gives the iterated lower Lebesgue (resp. Bochner) integrals. -/
theorem Submission.cmcdt_lpi_cyl_fubini : ∀ (n : ℕ) (A : Set (Euclid n)), MeasurableSet A → MeasurableSet {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ f : Euclid (n + 1) → ℝ≥0∞, Measurable f → ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) ∧ ∀ f : Euclid (n + 1) → ℝ, IntegrableOn f {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫ u in A, ∫ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
  intro n A hA
  set Ah := {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
    (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} with hAh_def
  -- the measurable equivalence `e : ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}`, `(u, t) ↦ (t, u)`
  let e : (Euclid n × ℝ) ≃ᵐ Euclid (n + 1) :=
    (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm)).trans
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))
  have he : ∀ p : Euclid n × ℝ, e p = WithLp.toLp 2 (Fin.cons p.2 (WithLp.ofLp p.1)) := by
    rintro ⟨u, t⟩
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    exact ⟨rfl, rfl⟩
  -- each factor of `e` preserves Lebesgue measure
  have hmp : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving
        (MeasurableEquiv.prodComm : (Euclid n × ℝ) ≃ᵐ (ℝ × Euclid n)) volume volume :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm) volume volume :=
      (MeasurePreserving.id volume).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
    have h3 : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)) volume volume := by
      have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))).symm _
      simpa using this
    exact h4.comp (h3.comp (h2.comp h1))
  -- `e⁻¹(Â) = A × (0, 1)`
  have hpre : e ⁻¹' Ah = A ×ˢ Ioo (0 : ℝ) 1 := by
    ext ⟨u, t⟩
    simp [Ah, he, and_comm]
  have hAhm : MeasurableSet Ah := by
    have : Ah = e.symm ⁻¹' (A ×ˢ Ioo (0 : ℝ) 1) := by
      rw [← hpre]; ext z; simp
    rw [this]
    exact e.symm.measurable (hA.prod measurableSet_Ioo)
  refine ⟨hAhm, ?_, ?_⟩
  · intro f hf
    rw [← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setLIntegral_prod]
    · simp only [he]
    · exact (hf.comp e.measurable).aemeasurable
  · intro f hf
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setIntegral_prod]
    · simp only [he]
    · rw [← Measure.volume_eq_prod, ← hpre]
      exact (hmp.integrableOn_comp_preimage e.measurableEmbedding).2 hf
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

/-- **Interior product bound for the Euclidean coefficient norm** (Simon 6.1): for `v ∈ ℝᴺ` and a
`(k+1)`-covector `β` on `ℝᴺ`, the interior product `ι_v β = β.curryLeft v`,
`ι_v β(w₁, …, w_k) = β(v, w₁, …, w_k)`, satisfies `|ι_v β|_E ≤ ‖v‖ |β|_E`.  By homogeneity it
suffices to treat `u = v / ‖v‖ = f_{i₀}` for an orthonormal basis `f` of `ℝᴺ`.  The position sums
`R_p = Σ_{J(p) = i₀} β(f ∘ J)²` all equal `R_0 = k! |ι_u β|_E²` (transpose `0 ↔ p`), and
`Σ_p R_p ≤ Σ_J β(f ∘ J)² = (k+1)! |β|_E²` because tuples with `i₀` in two slots vanish
(`regcomp_covector_sq_sum_orthonormalBasis` evaluates both sums). -/
theorem Submission.cmcdt_lp_covector_curryLeft_norm_le : ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  intro N k v β
  classical
  -- the case `v = 0`
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- homogeneity: `|c γ|_E = |c| |γ|_E`
  have hhom : ∀ (c : ℝ) (γ : Covector (Euclid N) k),
      covectorEuclideanNorm (c • γ) = |c| * covectorEuclideanNorm γ := by
    intro c γ
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  -- `N ≥ 1` as `ℝ⁰ = {0}`; an orthonormal basis `f` of `ℝᴺ` with `f i₀ = ‖v‖⁻¹ v`
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => hv (by subst h; exact Subsingleton.elim v 0)
  set i₀ : Fin N := ⟨0, hN⟩
  obtain ⟨f, hf⟩ : ∃ f : OrthonormalBasis (Fin N) ℝ (Euclid N), f i₀ = ‖v‖⁻¹ • v := by
    have hon : Orthonormal ℝ (({i₀} : Set (Fin N)).domRestrict fun _ => ‖v‖⁻¹ • v) := by
      refine ⟨fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
      rw [Set.domRestrict_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    exact ⟨b, hb i₀ rfl⟩
  -- `|ι_v β|_E = ‖v‖ |ι_{f i₀} β|_E`, so it suffices to show `|ι_{f i₀} β|_E ≤ |β|_E`
  have hvu : β.curryLeft v = ‖v‖ • β.curryLeft (f i₀) := by
    rw [hf, map_smul, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  rw [hvu, hhom, abs_of_pos hvpos]
  refine mul_le_mul_of_nonneg_left ?_ hvpos.le
  -- `g J = β(f ∘ J)²` and the position sums `R p = Σ_{J p = i₀} g J`
  set g : (Fin (k + 1) → Fin N) → ℝ := fun J => (β fun t => f (J t)) ^ 2 with hg
  set R : Fin (k + 1) → ℝ := fun p => ∑ J, if J p = i₀ then g J else 0 with hR
  -- `R 0 = Σ_j (ι_{f i₀} β)(f ∘ j)² = k! |ι_{f i₀} β|_E²` (reindex `J = Fin.cons a j`)
  have hR0 : R 0 = (k.factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 := by
    rw [← Submission.regcomp_covector_sq_sum_orthonormalBasis N k (β.curryLeft (f i₀)) f]
    simp only [hR]
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin N).sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.consEquiv_apply, Fin.cons_zero, ↓reduceIte, hg]
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext t
      refine Fin.cases ?_ (fun s => ?_) t <;> simp
    · intro a _ ha
      exact Finset.sum_eq_zero fun j _ => by simp [ha]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  -- `R p = R 0`: reindex `J ↦ J ∘ (0 p)`, and `β(f ∘ J ∘ (0 p)) = ±β(f ∘ J)`
  have hRp : ∀ p, R p = R 0 := by
    intro p
    simp only [hR]
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N))) _ _
      fun J => ?_
    have hJ : ∀ t, Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J t =
        J (Equiv.swap 0 p t) := fun t => by
      simp [Equiv.arrowCongr_apply]
    have hperm : β (fun t => f (J (Equiv.swap 0 p t))) =
        Equiv.Perm.sign (Equiv.swap 0 p) • β (fun t => f (J t)) :=
      β.toAlternatingMap.map_perm (fun t => f (J t)) (Equiv.swap 0 p)
    have hgJ : g (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J) = g J := by
      simp only [hg, hJ, hperm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (k + 1)) p)) with h | h <;>
        simp [h]
    rw [hgJ, hJ, Equiv.swap_apply_left]
  -- `Σ_p R p ≤ Σ_J g J`: a tuple `J` with `i₀` in two slots has `β(f ∘ J) = 0`
  have hsum : ∑ p, R p ≤ ∑ J, g J := by
    simp only [hR]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun J _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    by_cases h : (Finset.univ.filter fun p => J p = i₀).card ≤ 1
    · exact mul_le_of_le_one_left (sq_nonneg _) (by exact_mod_cast h)
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (not_le.mp h)
      rw [Finset.mem_filter] at hp hq
      have h0 : β (fun t => f (J t)) = 0 :=
        β.map_eq_zero_of_eq _ (by rw [hp.2, hq.2]) hpq
      simp [hg, h0]
  -- `(k+1)! |ι_{f i₀} β|_E² = Σ_p R p ≤ Σ_J g J = (k+1)! |β|_E²`
  have key : ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 ≤
      ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 :=
    calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2
        = ∑ p, R p := by
          rw [Finset.sum_congr rfl fun p _ => hRp p, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, hR0, Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ∑ J, g J := hsum
      _ = ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 := by
          simp only [hg]
          exact Submission.regcomp_covector_sq_sum_orthonormalBasis N (k + 1) β f
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _) (covectorEuclideanNorm_nonneg _)
    two_ne_zero).mp (le_of_mul_le_mul_left key (by exact_mod_cast Nat.factorial_pos _))

/-- **Bounds for one piece of the cone** (Simon 6.2.30, `0 ⨯ T = h_#([[(0, 1)]] × T)` with
`h(t, x) = t x`, and the estimate of 6.2.27): let `B = {z ∈ ℝ^{n+1} : z₀ ∈ (0, 1), tail z ∈ A}`
and suppose `(DH(z)ê_b)_b = Fin.cons (G u) (z₀ DG(u)e_a)_a` for `z ∈ B`, `u = tail z`.  Then
`w ∘ tail` is integrable on `B` (Tonelli on `B`, `cmcdt_lpi_cyl_fubini`, and `|(0, 1)| = 1`);
`c′(z) = z₀ⁿ ‖G u‖ c(u)` satisfies `|α(DH(z)ê)| ≤ c′(z) |α|_E`, since
`α(Fin.cons v (s • x)) = sⁿ (ι_v α)(x)` by multilinearity and `|ι_v α|_E ≤ ‖v‖ |α|_E`
(`cmcdt_lp_covector_curryLeft_norm_le`); and Tonelli with `z₀ⁿ ≤ 1` and `‖G‖ ≤ ρ` on `A` gives
`∫⁻_B |w ∘ tail| c′ ≤ ρ ∫⁻_A |w| c`. -/
theorem Submission.dimred_cs_sos_cfs_cp_piece_bounds : ∀ (P n : ℕ) (ρ : ℝ) (G : Euclid n → Euclid P) (H : Euclid (n + 1) → Euclid P) (A : Set (Euclid n)) (w : Euclid n → ℤ) (c : Euclid n → ℝ), Measurable G → MeasurableSet A → Measurable w → Measurable c → IntegrableOn (fun u => (w u : ℝ)) A → (∀ u ∈ A, ‖G u‖ ≤ ρ) → (∀ u ∈ A, 0 ≤ c u ∧ ∀ α : Covector (Euclid P) n, |α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))| ≤ c u * covectorEuclideanNorm α) → (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1))) → IntegrableOn (fun z : Euclid (n + 1) => (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)) {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → 0 ≤ WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ ∀ α : Covector (Euclid P) (n + 1), |α (fun b => fderiv ℝ H z (EuclideanSpace.single b 1))| ≤ WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) * covectorEuclideanNorm α) ∧ ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, ENNReal.ofReal (|(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)| * (WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))) ≤ ENNReal.ofReal ρ * ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u) := by
  intro P n ρ G H A w c hGm hA hw hc hwi hGρ hcb hDH
  obtain ⟨-, hlin, -⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  have htail : Measurable (fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)) := by
    fun_prop
  have hz0 : Measurable (fun z : Euclid (n + 1) => WithLp.ofLp z 0) := by
    fun_prop
  -- `tail (t, u) = u`
  have hιtail : ∀ (t : ℝ) (u : Euclid n),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) = u := by
    intro t u; simp
  have hwR : Measurable (fun u => (w u : ℝ)) := (measurable_of_countable _).comp hw
  refine ⟨?_, ?_, ?_⟩
  · -- integrability of `w ∘ tail` on `B`: `∫⁻_B |w ∘ tail| = ∫⁻_A |w| · |(0, 1)| < ∞`
    refine ⟨(hwR.comp htail).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hlin (fun z => ‖(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)‖ₑ)
      (hwR.comp htail).enorm]
    simp only [hιtail]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    exact hwi.2
  · -- the covector bound, with `s = z₀` and `u = tail z`
    intro z hz hzA
    set s := WithLp.ofLp z 0
    set u := (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)
    have hs : 0 < s := hz.1
    obtain ⟨hc0, hcα⟩ := hcb u hzA
    refine ⟨by positivity, fun α => ?_⟩
    rw [hDH z hz hzA]
    -- `α(Fin.cons v (s • x)) = sⁿ (ι_v α)(x)`
    have key : α (Fin.cons (G u) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1))) =
        s ^ n * (α.curryLeft (G u)) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      have h1 : α (Fin.cons (G u) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1))) =
          (α.curryLeft (G u)) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1)) :=
        (α.curryLeft_apply_apply (G u) _).symm
      rw [h1, ContinuousAlternatingMap.map_smul_univ (α.curryLeft (G u)) (fun _ => s)]
      simp
    rw [key, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ n * |(α.curryLeft (G u)) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))|
        ≤ s ^ n * (c u * covectorEuclideanNorm (α.curryLeft (G u))) := by
          gcongr; exact hcα _
      _ ≤ s ^ n * (c u * (‖G u‖ * covectorEuclideanNorm α)) := by
          gcongr
          exact Submission.cmcdt_lp_covector_curryLeft_norm_le P n (G u) α
      _ = s ^ n * ‖G u‖ * c u * covectorEuclideanNorm α := by ring
  · -- the mass bound: Tonelli on `B`, then `tⁿ ≤ 1` and `‖G u‖ ≤ ρ` for `u ∈ A`
    have hfm : Measurable (fun z : Euclid (n + 1) =>
        ENNReal.ofReal (|(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)| *
          (WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ *
            c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (continuous_abs.measurable.comp (hwR.comp htail)).mul
        (((hz0.pow_const n).mul (hGm.comp htail).norm).mul (hc.comp htail))
    rw [hlin _ hfm]
    simp only [hιtail]
    calc ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (|(w u : ℝ)| * (t ^ n * ‖G u‖ * c u))
        ≤ ∫⁻ u in A, ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
          refine setLIntegral_mono (by fun_prop) fun u hu => ?_
          obtain ⟨hc0, -⟩ := hcb u hu
          have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hGρ u hu)
          calc ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (|(w u : ℝ)| * (t ^ n * ‖G u‖ * c u))
              ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
                refine setLIntegral_mono (by fun_prop) fun t ht => ?_
                rw [← ENNReal.ofReal_mul hρ0]
                refine ENNReal.ofReal_le_ofReal ?_
                have ht1 : t ^ n ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
                have ht0 : 0 ≤ t ^ n := pow_nonneg ht.1.le n
                calc |(w u : ℝ)| * (t ^ n * ‖G u‖ * c u)
                    ≤ |(w u : ℝ)| * (1 * ρ * c u) := by
                      gcongr
                      · exact hGρ u hu
                  _ = ρ * (|(w u : ℝ)| * c u) := by ring
            _ = ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
                rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
      _ = ENNReal.ofReal ρ * ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u) := by
          rw [lintegral_const_mul]
          fun_prop
/-- **Lipschitz pull-back of a test form against an integrable weight** (supplied step 3 of the
cylinder construction, third item).  `ω` is smooth with compact support, so `‖ω(y)‖ ≤ M` for all
`y`; an `L`-Lipschitz `H` has `‖DH(z)‖ ≤ L` at every `z` (`fderiv` is `0` where `H` is not
differentiable), so `|ω(H z)(DH(z)e₁, …, DH(z)eₙ)| ≤ ‖ω(H z)‖ ∏ₐ ‖DH(z)eₐ‖ ≤ M Lⁿ`.  The integrand
is Borel: `z ↦ DH(z)eₐ` is measurable and `(x, w) ↦ ω(H x)(w)` is continuous.  An integrable
function times a bounded a.e. strongly measurable function is integrable. -/
theorem Submission.cmcdt_lpi_cyl_pullback_integrable : ∀ (Q n : ℕ) (L : NNReal) (H : Euclid n → Euclid Q) (S : Set (Euclid n)) (g : Euclid n → ℝ) (ω : TestFormOn (univ : Set (Euclid Q)) n), LipschitzWith L H → IntegrableOn g S → IntegrableOn (fun z => g z * (ω : DifferentialForm (Euclid Q) n) (H z) (fun a => fderiv ℝ H z (EuclideanSpace.single a 1))) S := by
  intro Q n L H S g ω hH hg
  -- `ω` is continuous with compact support, hence bounded: `‖ω(y)‖ ≤ M`
  have hωc : Continuous (ω : DifferentialForm (Euclid Q) n) := ω.2.1.1.continuous
  obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.2.1.2
  -- the integrand is Borel: `z ↦ (DH(z)eₐ)ₐ` is measurable and `(x, w) ↦ ω(H x)(w)` continuous
  have hmeas : Measurable fun z => (ω : DifferentialForm (Euclid Q) n) (H z)
      (fun a => fderiv ℝ H z (EuclideanSpace.single a 1)) := by
    have hv : Measurable fun z => fun a : Fin n => fderiv ℝ H z (EuclideanSpace.single a 1) :=
      measurable_pi_iff.mpr fun a => measurable_fderiv_apply_const ℝ H _
    have hc : Continuous fun p : Euclid n × (Fin n → Euclid Q) =>
        (ω : DifferentialForm (Euclid Q) n) (H p.1) p.2 :=
      (hωc.comp (hH.continuous.comp continuous_fst)).eval continuous_snd
    exact hc.measurable.comp (measurable_id.prodMk hv)
  -- `|ω(H z)(DH(z)e)| ≤ ‖ω(H z)‖ ∏ₐ ‖DH(z)eₐ‖ ≤ M Lⁿ`, since `‖DH(z)eₐ‖ ≤ ‖DH(z)‖ ≤ L`
  have hbd : ∀ z, ‖(ω : DifferentialForm (Euclid Q) n) (H z)
      (fun a => fderiv ℝ H z (EuclideanSpace.single a 1))‖ ≤ M * (L : ℝ) ^ n := by
    intro z
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (H z))
    have hcomp : ∀ a : Fin n, ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖ ≤ L := fun a =>
      calc ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖
          ≤ ‖fderiv ℝ H z‖ * ‖(EuclideanSpace.single a (1 : ℝ))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ H z‖ := by simp
        _ ≤ L := norm_fderiv_le_of_lipschitz ℝ hH
    calc _ ≤ ‖(ω : DifferentialForm (Euclid Q) n) (H z)‖ *
            ∏ a, ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖ :=
          ContinuousAlternatingMap.le_opNorm _ _
      _ ≤ M * ∏ _a : Fin n, (L : ℝ) := by
          gcongr with a
          · exact hM _
          · exact hcomp a
      _ = M * (L : ℝ) ^ n := by simp
  exact hg.mul_bdd hmeas.aestronglyMeasurable (Eventually.of_forall hbd)

/-- **Cone piece change of variables** (Simon Ch. 6, 2.27 and 2.30, for one piece).  Let
`B = {z ∈ ℝ^{n+1} : z₀ ∈ (0, 1), tail z ∈ A}`, and suppose that on `B` the map `H` is the cone
map `H(z) = z₀ G(tail z)` with `DH(z)ê = (G(tail z), z₀ DG(tail z)e)`, and that on `G(A)` the
form `η` is the radial homotopy `η(v) = ∫₀¹ tⁿ ι_v ω(tv) dt`.  The weight `w ∘ tail` is
integrable on `B` by Tonelli on the cylinder (`|(0, 1)| = 1`), so the integrand on `B` is
integrable (Lipschitz pull-back) and Fubini reduces the identity to a fixed `u ∈ A`.  There
multilinearity gives `ω(tv)(v, t x) = tⁿ ω(tv)(v, x)` for `v = G(u)`, `x = DG(u)e`, and
evaluation at `x` commutes with the covector-valued interval integral defining `η(v)`. -/
theorem Submission.dimred_cs_sos_cfs_cp_piece_action : ∀ (P n : ℕ) (L : NNReal) (G : Euclid n → Euclid P) (H : Euclid (n + 1) → Euclid P) (A : Set (Euclid n)) (w : Euclid n → ℤ) (ω : TestFormOn (univ : Set (Euclid P)) (n + 1)) (η : DifferentialForm (Euclid P) n), LipschitzWith L H → MeasurableSet A → Measurable w → IntegrableOn (fun u => (w u : ℝ)) A → (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → H z = WithLp.ofLp z 0 • G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1))) → (∀ u ∈ A, η (G u) = ∫ t in (0 : ℝ)..1, t ^ n • ((ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)).curryLeft (G u)) → ∫ u in A, (w u : ℝ) * η (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) = ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ) * (ω : DifferentialForm (Euclid P) (n + 1)) (H z) (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) := by
  intro P n L G H A w ω η hHL hA hw hwi hHB hη
  obtain ⟨-, hlin, hfub⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  have htail : Measurable (fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)) := by
    fun_prop
  have hιtail : ∀ (t : ℝ) (u : Euclid n),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) = u := by
    intro t u; simp
  have hι0 : ∀ (t : ℝ) (u : Euclid n),
      WithLp.ofLp (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) 0 = t := by
    intro t u; simp
  have hwR : Measurable (fun u => (w u : ℝ)) := (measurable_of_countable _).comp hw
  -- `w ∘ tail` is integrable on `B`: Tonelli on the cylinder and `|(0, 1)| = 1`
  have hint : IntegrableOn
      (fun z : Euclid (n + 1) => (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ))
      {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
        (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} := by
    refine ⟨(hwR.comp htail).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral,
      hlin (fun z => ‖(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)‖ₑ) (hwR.comp htail).enorm]
    simp only [hιtail]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    exact hwi.2
  -- so the integrand on `B` is integrable (Lipschitz pull-back), and Fubini applies
  have hF := Submission.cmcdt_lpi_cyl_pullback_integrable P (n + 1) L H _ _ ω hHL hint
  rw [hfub _ hF]
  refine setIntegral_congr_fun hA fun u hu => ?_
  have hωc : Continuous (ω : DifferentialForm (Euclid P) (n + 1)) := ω.2.1.1.continuous
  -- `α(v, s x) = sⁿ α(v, x)` for an `(n + 1)`-covector `α`
  have hsc : ∀ (α : Covector (Euclid P) (n + 1)) (v : Euclid P) (x : Fin n → Euclid P) (s : ℝ),
      α (Fin.cons v (fun a => s • x a)) = s ^ n * α (Fin.cons v x) := by
    intro α v x s
    have h1 : α (Fin.cons v (fun a => s • x a)) = (α.curryLeft v) (fun a => s • x a) := rfl
    have h2 : α (Fin.cons v x) = (α.curryLeft v) x := rfl
    rw [h1, h2, ContinuousAlternatingMap.map_smul_univ (α.curryLeft v) (fun _ => s)]
    simp
  -- the inner integrand at `z = (t, u)`, `t ∈ (0, 1)`
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1,
      (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1))))) : ℝ) *
        (ω : DifferentialForm (Euclid P) (n + 1)) (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))
          (fun b => fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))
            (EuclideanSpace.single b 1)) =
      (w u : ℝ) * (t ^ n * (ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)
        (Fin.cons (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))) := by
    intro t ht
    have hz : WithLp.ofLp (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) 0 ∈
        Ioo (0 : ℝ) 1 := by rw [hι0]; exact ht
    have hzA : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) ∈ A := by
      rw [hιtail]; exact hu
    obtain ⟨h1, h2⟩ := hHB _ hz hzA
    rw [h1, h2]
    simp only [hιtail, Fin.cons_zero]
    rw [hsc]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul]
  congr 1
  -- evaluation at `DG(u)e` commutes with the covector-valued integral defining `η(G u)`
  rw [hη u hu]
  have hcont : Continuous (fun t : ℝ =>
      t ^ n • ((ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)).curryLeft (G u)) := by
    have : Continuous (fun t : ℝ => (ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)) :=
      hωc.comp (continuous_id.smul continuous_const)
    exact (continuous_pow n).smul
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
        (n := n)).continuous.comp this |>.clm_apply continuous_const)
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
      (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))
    (hcont.intervalIntegrable (μ := volume) 0 1)
  rw [← ContinuousAlternatingMap.apply_apply, ← hcomm,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp only [ContinuousAlternatingMap.apply_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  rfl

/-- **Cone parametrization** (Simon 6.2.30, `0 ⨯ X = h_#([[(0, 1)]] × X)` with `h(t, x) = tx`).
If `X(γ) = Σᵢ ∫_{Aᵢ} wᵢ γ(Gᵢ u)(DGᵢ(u)e) du` for Lipschitz `Gᵢ` with `Gᵢ(Aᵢ) ⊆ spt X` compact,
and `Y(ω) = X(η)` with `η = Kω`, `Kω(x) = ∫₀¹ t^{q+1} ι_x ω(tx) dt`, on `spt X`, then `Y` is
parametrized by the cone maps: `Hᵢ(s, u) = s Gᵢ(u)` on `Bᵢ = {w₀ ∈ (0, 1), tail w ∈ Aᵢ}`,
`hᵢ(w) = wᵢ(tail w)` and `c′ᵢ(w) = w₀^{q+1} ‖Gᵢ(tail w)‖ cᵢ(tail w)`.  Take `ρ` with
`spt X ⊆ B_ρ(0)`, so `‖Gᵢ‖ < ρ` on `Aᵢ`.  `cone_map` gives the Lipschitz `Hᵢ` with this value and
derivative on `Bᵢ`; `piece_bounds` gives the integrability of `hᵢ`, the `c′ᵢ` bound and
`∫⁻_{Bᵢ} |hᵢ| c′ᵢ ≤ ρ ∫⁻_{Aᵢ} |wᵢ| cᵢ`, which sums to a finite bound; `piece_action` turns each
term of the series for `X(η)` into the corresponding term for `Y(ω)`. -/
theorem Submission.dimred_cs_sos_cfs_cone_param : ∀ (P q : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1 + 1)) (G : ℕ → Euclid (q + 1) → Euclid P) (A : ℕ → Set (Euclid (q + 1))) (w : ℕ → Euclid (q + 1) → ℤ) (c : ℕ → Euclid (q + 1) → ℝ), IsCompact X.support → (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) → (∀ i, MeasurableSet (A i)) → (∀ i, Measurable (w i)) → (∀ i, Measurable (c i)) → (∀ i, ∀ u ∈ A i, DifferentiableAt ℝ (G i) u) → (∀ i, G i '' A i ⊆ X.support) → (∀ i, IntegrableOn (fun u => (w i u : ℝ)) (A i)) → (∀ i, ∀ u ∈ A i, 0 ≤ c i u ∧ ∀ α : Covector (Euclid P) (q + 1), |α (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))| ≤ c i u * covectorEuclideanNorm α) → ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) ≠ ∞ → (∀ γ : TestFormOn (univ : Set (Euclid P)) (q + 1), HasSum (fun i => ∫ u in A i, (w i u : ℝ) * (γ : DifferentialForm (Euclid P) (q + 1)) (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (X γ)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid P)) (q + 1), (∀ x ∈ X.support, (η : DifferentialForm (Euclid P) (q + 1)) x = ∫ t in (0 : ℝ)..1, t ^ (q + 1) • ((ω : DifferentialForm (Euclid P) (q + 1 + 1)) (t • x)).curryLeft x) ∧ Y ω = X η) → ∃ (H : ℕ → Euclid (q + 1 + 1) → Euclid P) (B : ℕ → Set (Euclid (q + 1 + 1))) (h : ℕ → Euclid (q + 1 + 1) → ℤ) (c' : ℕ → Euclid (q + 1 + 1) → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (H i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, Measurable (h i)) ∧ (∀ i, Measurable (c' i)) ∧ (∀ i, IntegrableOn (fun u => (h i u : ℝ)) (B i)) ∧ (∀ i, ∀ u ∈ B i, 0 ≤ c' i u ∧ ∀ α : Covector (Euclid P) (q + 1 + 1), |α (fun a => fderiv ℝ (H i) u (EuclideanSpace.single a 1))| ≤ c' i u * covectorEuclideanNorm α) ∧ ∑' i, ∫⁻ u in B i, ENNReal.ofReal (|(h i u : ℝ)| * c' i u) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1), HasSum (fun i => ∫ u in B i, (h i u : ℝ) * (ω : DifferentialForm (Euclid P) (q + 1 + 1)) (H i u) (fun a => fderiv ℝ (H i) u (EuclideanSpace.single a 1))) (Y ω) := by
  intro P q X Y G A w c hXc hGL hA hw hc hGd hGA hwi hcb hsum hXser hYK
  -- step 1: a radius `ρ` with `spt X ⊆ B_ρ(0)`, so `‖Gᵢ u‖ < ρ` on `Aᵢ`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, X.support ⊆ ball (0 : Euclid P) ρ := hXc.isBounded.subset_ball 0
  have hGρ : ∀ i, ∀ u ∈ A i, ‖G i u‖ < ρ := fun i u hu => by
    simpa [mem_ball_zero_iff] using hρ (hGA i ⟨u, hu, rfl⟩)
  -- step 2: the truncated cone maps `Hᵢ`, Lipschitz with `Hᵢ(s, u) = s Gᵢ(u)` near `Bᵢ`
  choose L hL using hGL
  choose H hHL hH using fun i =>
    Submission.dimred_cs_sos_cfs_cp_cone_map P (q + 1) (G i) (L i) ρ (hL i)
  choose K hK using hHL
  have htail : Continuous fun z : Euclid (q + 1 + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid (q + 1)) := by
    fun_prop
  have hz0 : Continuous fun z : Euclid (q + 1 + 1) => WithLp.ofLp z 0 := by
    fun_prop
  -- value and derivative of `Hᵢ` on `Bᵢ = {z₀ ∈ (0, 1), tail z ∈ Aᵢ}`
  have hHB : ∀ i, ∀ z : Euclid (q + 1 + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 →
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid (q + 1)) ∈ A i →
      H i z = WithLp.ofLp z 0 • G i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧
      (fun b => fderiv ℝ (H i) z (EuclideanSpace.single b 1)) =
        Fin.cons (G i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))
          (fun a => WithLp.ofLp z 0 • fderiv ℝ (G i) (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))
            (EuclideanSpace.single a 1)) := by
    intro i z hz hzA
    obtain ⟨h1, h2⟩ := hH i z hz (hGρ i _ hzA)
    exact ⟨h1, h2 (hGd i _ hzA)⟩
  -- steps 3, 5–7 for each piece: integrability of `hᵢ`, the `c′ᵢ` bound and the mass bound
  have hpb := fun i => Submission.dimred_cs_sos_cfs_cp_piece_bounds P (q + 1) ρ (G i) (H i) (A i)
    (w i) (c i) (hL i).continuous.measurable (hA i) (hw i) (hc i) (hwi i)
    (fun u hu => (hGρ i u hu).le) (hcb i) (fun z hz hzA => (hHB i z hz hzA).2)
  refine ⟨H, fun i => {z : Euclid (q + 1 + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid (q + 1)) ∈ A i},
    fun i z => w i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))),
    fun i z => WithLp.ofLp z 0 ^ (q + 1) * ‖G i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ *
      c i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))),
    fun i => ⟨K i, hK i⟩, fun i => (Submission.cmcdt_lpi_cyl_fubini (q + 1) (A i) (hA i)).1,
    fun i => (hw i).comp htail.measurable, fun i => ?_, fun i => (hpb i).1,
    fun i z hz => (hpb i).2.1 z hz.1 hz.2, ?_, ?_⟩
  · -- `c′ᵢ` is measurable
    exact ((hz0.measurable.pow_const (q + 1)).mul
      ((hL i).continuous.comp htail).measurable.norm).mul ((hc i).comp htail.measurable)
  · -- step 7: `Σᵢ ∫⁻_{Bᵢ} |hᵢ| c′ᵢ ≤ ρ Σᵢ ∫⁻_{Aᵢ} |wᵢ| cᵢ < ∞`
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun i => (hpb i).2.2)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  · -- step 8: `Y(ω) = X(η)` with `η = Kω` on `spt X ⊇ Gᵢ(Aᵢ)`, and each term of the series for
    -- `X(η)` is the corresponding cone integral
    intro ω
    obtain ⟨η, hη, hYη⟩ := hYK ω
    rw [hYη]
    convert hXser η using 1
    funext i
    exact (Submission.dimred_cs_sos_cfs_cp_piece_action P (q + 1) (K i) (G i) (H i) (A i) (w i) ω
      η (hK i) (hA i) (hw i) (hwi i) (hHB i) fun u hu => hη (G i u) (hGA i ⟨u, hu, rfl⟩)).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
