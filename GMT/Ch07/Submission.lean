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
/-- Tangential `C¹` deformations (Simon Ch. 2, before 5.8; Ch. 4, 2.5–2.6; step 3 of the proof
of 7.1.2).  A partition of unity splits `X = X₀ + Σᵢ χᵢX`: `X₀` vanishes on `N`, and `χᵢX` is
supported where `N` is straightened by `Ψ x = ψ(vₚ + g x) + (x - A g x)` (`A = Dψ(vₚ)`, `g A = id`,
so `DΨ(0) = I`; inverse function theorem, `Φ = Ψ⁻¹`).  `X₀` is deformed by `id + tX₀`, `Y = χᵢX`
by `Ψ (Φ y + t DΦ(y) Y(y))`, which keeps `N` since `DΦ Y` is tangent to the slice `{A g x = x}`
(`T_zN = range Dψ`) and has `Dφ_t = I + tDY + o(t)` uniformly (mean value inequality, symmetry of
`D²Ψ`).  Composition adds the expansions; for small `t` the result is a bijection with injective
derivative (`‖Dφ_t - I‖ ≤ 1/2`), and `φ_t = id` otherwise. -/
theorem Submission.tangential_c1_deformation_exists : ∀ (P d : ℕ) (U N : Set (Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → ∃ φ : ℝ → Euclid P → Euclid P, (∀ t, ContDiff ℝ 1 (φ t) ∧ Bijective (φ t) ∧ (∀ x, Injective (fderiv ℝ (φ t) x)) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) (N ∩ U) (N ∩ U)) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t| := by
  intro P d U N X hU hN hNU hX hXc hXU hXT
  classical
  -- small `t`: `|t| c < r` eventually as `t → 0`
  have hev : ∀ c r : ℝ, 0 < r → ∀ᶠ t in 𝓝 (0:ℝ), |t| * c < r := fun c r hr => by
    have h : ContinuousAt (fun t : ℝ => |t| * c) 0 :=
      (continuous_abs.mul continuous_const).continuousAt
    exact h.eventually_lt continuousAt_const
      (by show |(0:ℝ)| * c < r; rw [abs_zero, zero_mul]; exact hr)
  -- nonnegative bounds of continuous functions on compact sets
  have hbd : ∀ {F G : Type} [TopologicalSpace F] [SeminormedAddCommGroup G] (s : Set F) (f : F → G),
      IsCompact s → ContinuousOn f s → ∃ M, 0 ≤ M ∧ ∀ x ∈ s, ‖f x‖ ≤ M := fun s f hs hf =>
    let ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hf
    ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  -- the algebra of the two expansions (`D²Ψ` symmetric)
  have halg : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L1 L0 G DV : E →L[ℝ] E)
      (D2 : E →L[ℝ] E →L[ℝ] E) (w : E) (t : ℝ), (∀ u v, D2 u v = D2 v u) →
      L1.comp (G + t • DV) - L0.comp G - t • (L0.comp DV + (D2.comp G).flip w) =
        (L1 - L0 - t • D2 w).comp G + t • ((L1 - L0).comp DV) := by
    intro E _ _ L1 L0 G DV D2 w t hs
    ext v
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.flip_apply, map_add, map_smul, smul_sub, smul_add, hs (G v) w]
    abel
  have halg2 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Pm Q a a' b : E →L[ℝ] E)
      (t : ℝ), Pm.comp Q - ContinuousLinearMap.id ℝ E - t • (a + b) =
        (Pm - ContinuousLinearMap.id ℝ E - t • a').comp Q +
          (Q - ContinuousLinearMap.id ℝ E - t • b) + t • a'.comp (Q - ContinuousLinearMap.id ℝ E) +
          t • (a' - a) := by
    intro E _ _ Pm Q a a' b t
    ext v
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_sub, smul_sub, smul_add]
    abel
  -- conjugated deformations `φ_t y = Ψ (Φ y + t DΦ(y) Y(y))` near `spt Y`, `φ_t y = y` elsewhere
  have gconj : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
      (Ψ Φ Y Vf : E → E) (φ : ℝ → E → E) (B O : Set E), IsOpen B → IsOpen O →
      (∀ b ∈ B, ContDiffAt ℝ 2 Ψ b) → (∀ y ∈ O, ContDiffAt ℝ 2 Φ y ∧ Φ y ∈ B ∧ Ψ (Φ y) = y) →
      ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ O →
      (∀ y, Vf y = fderiv ℝ Φ y (Y y)) →
      (∀ t y, φ t y = if y ∈ O then Ψ (Φ y + t • Vf y) else y) →
      (∀ t y, y ∉ tsupport Y → φ t y = y) ∧
      ∃ C : ℝ, (∀ᶠ t in 𝓝 (0:ℝ), ContDiff ℝ 1 (φ t) ∧ (∀ y ∈ tsupport Y, Φ y + t • Vf y ∈ B) ∧
          ∀ y, ‖φ t y - y‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 (0:ℝ), ∀ y,
          ‖fderiv ℝ (φ t) y - ContinuousLinearMap.id ℝ E - t • fderiv ℝ Y y‖ ≤ ε * |t| := by
    intro E _ _ _ Ψ Φ Y Vf φ B O hB hO hΨ hΦ hY hYc hYO hVf hφ
    -- derivatives of `Ψ`, `DΨ`, `Φ` and `Vf = DΦ · Y`
    have hΦd : ∀ y ∈ O, HasFDerivAt Φ (fderiv ℝ Φ y) y := fun y hy =>
      ((hΦ y hy).1.differentiableAt two_ne_zero).hasFDerivAt
    have hΨ1 : ∀ b ∈ B, ContDiffAt ℝ 1 (fderiv ℝ Ψ) b := fun b hb =>
      (hΨ b hb).fderiv_right (by norm_num)
    have hΨd : ∀ b ∈ B, HasFDerivAt Ψ (fderiv ℝ Ψ b) b := fun b hb =>
      ((hΨ b hb).differentiableAt two_ne_zero).hasFDerivAt
    have hΨ2d : ∀ b ∈ B, HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) b) b := fun b hb =>
      ((hΨ1 b hb).differentiableAt one_ne_zero).hasFDerivAt
    have hVfC : ∀ y ∈ O, ContDiffAt ℝ 1 Vf y := fun y hy =>
      (((hΦ y hy).1.fderiv_right (by norm_num)).clm_apply hY.contDiffAt).congr_of_eventuallyEq
        (Eventually.of_forall hVf)
    have hVfd : ∀ y ∈ O, HasFDerivAt Vf (fderiv ℝ Vf y) y := fun y hy =>
      ((hVfC y hy).differentiableAt one_ne_zero).hasFDerivAt
    -- `DΨ(Φ y) ∘ DΦ(y) = id` on `O`, so `Y = DΨ(Φ) · Vf` there
    have hinv : ∀ y ∈ O, (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Φ y) = ContinuousLinearMap.id ℝ E :=
      fun y hy => ((hΨd _ (hΦ y hy).2.1).comp y (hΦd y hy)).unique
        ((hasFDerivAt_id y).congr_of_eventuallyEq
          (eventually_of_mem (hO.mem_nhds hy) fun z hz => (hΦ z hz).2.2))
    have hYΨ : ∀ y ∈ O, fderiv ℝ Ψ (Φ y) (Vf y) = Y y := fun y hy => by
      rw [hVf, ← ContinuousLinearMap.comp_apply, hinv y hy, ContinuousLinearMap.id_apply]
    have hid : ∀ t y, y ∉ tsupport Y → φ t y = y := fun t y hy => by
      rw [hφ]
      split_ifs with h
      · rw [hVf, image_eq_zero_of_notMem_tsupport hy, map_zero, smul_zero, add_zero,
          (hΦ y h).2.2]
      · rfl
    refine ⟨hid, ?_⟩
    -- compact sets and bounds
    have hK : IsCompact (tsupport Y) := hYc
    have hΦK : IsCompact (Φ '' tsupport Y) :=
      hK.image_of_continuousOn fun y hy => (hΦd y (hYO hy)).continuousAt.continuousWithinAt
    obtain ⟨η, hη, hηB⟩ := hΦK.exists_cthickening_subset_open hB
      (image_subset_iff.2 fun y hy => (hΦ y (hYO hy)).2.1)
    have hK₂ : IsCompact (cthickening η (Φ '' tsupport Y)) := hΦK.cthickening
    have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ Ψ)) (cthickening η (Φ '' tsupport Y)) :=
      fun c hc => ((hΨ1 c (hηB hc)).continuousAt_fderiv one_ne_zero).continuousWithinAt
    obtain ⟨M1, hM10, hM1⟩ := hbd _ (fderiv ℝ Ψ) hK₂ fun c hc =>
      (hΨ1 c (hηB hc)).continuousAt.continuousWithinAt
    obtain ⟨M2, hM20, hM2⟩ := hbd _ _ hK₂ hD2c
    obtain ⟨MΦ, hMΦ0, hMΦ⟩ := hbd _ (fderiv ℝ Φ) hK fun y hy =>
      ((hΦ y (hYO hy)).1.continuousAt_fderiv two_ne_zero).continuousWithinAt
    obtain ⟨MV, hMV0, hMV⟩ := hbd _ Vf hK fun y hy =>
      (hVfC y (hYO hy)).continuousAt.continuousWithinAt
    obtain ⟨MDV, hMDV0, hMDV⟩ := hbd _ (fderiv ℝ Vf) hK fun y hy =>
      ((hVfC y (hYO hy)).continuousAt_fderiv one_ne_zero).continuousWithinAt
    -- for small `t`, the segment `[Φ y, Φ y + t Vf y]` lies in a ball inside `cthickening η (Φ K)`
    have hball : ∀ y ∈ tsupport Y, ∀ t : ℝ, |t| * MV < η →
        closedBall (Φ y) (|t| * MV) ⊆ cthickening η (Φ '' tsupport Y) ∧
          Φ y + t • Vf y ∈ closedBall (Φ y) (|t| * MV) := fun y hy t ht =>
      ⟨(closedBall_subset_closedBall ht.le).trans
        (closedBall_subset_cthickening (mem_image_of_mem Φ hy) η), by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hMV y hy) (abs_nonneg t)⟩
    have hev0 : ∀ t, ∀ y ∈ O, φ t =ᶠ[𝓝 y] fun z => Ψ (Φ z + t • Vf z) := fun t y hy =>
      eventually_of_mem (hO.mem_nhds hy) fun z hz => by rw [hφ, ite_eq_left hz]
    have hev1 : ∀ t, ∀ y ∉ tsupport Y, φ t =ᶠ[𝓝 y] id := fun t y hy =>
      eventually_of_mem ((isClosed_tsupport Y).isOpen_compl.mem_nhds hy) fun z hz => hid t z hz
    refine ⟨M1 * MV, ?_, fun ε hε => ?_⟩
    · -- `C¹`, the deformed points stay in `B`, displacement `≤ M1 MV |t|`
      filter_upwards [hev MV η hη] with t ht
      have hmem : ∀ y ∈ tsupport Y, Φ y + t • Vf y ∈ B := fun y hy =>
        hηB ((hball y hy t ht).1 (hball y hy t ht).2)
      refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hmem, fun y => ?_⟩
      · by_cases hy : y ∈ tsupport Y
        · have hyO := hYO hy
          exact (((hΨ _ (hmem y hy)).of_le (by norm_num)).comp y (((hΦ y hyO).1.of_le
            (by norm_num)).add ((hVfC y hyO).const_smul t))).congr_of_eventuallyEq (hev0 t y hyO)
        · exact contDiffAt_id.congr_of_eventuallyEq (hev1 t y hy)
      · by_cases hy : y ∈ tsupport Y
        · have hyO := hYO hy
          have h :=
            (convex_closedBall (Φ y) (|t| * MV)).norm_image_sub_le_of_norm_hasFDerivWithin_le
              (f := Ψ) (fun c hc => (hΨd c (hηB ((hball y hy t ht).1 hc))).hasFDerivWithinAt)
              (fun c hc => hM1 c ((hball y hy t ht).1 hc))
              (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0)) (hball y hy t ht).2
          rw [(hΦ y hyO).2.2, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
          rw [hφ, ite_eq_left hyO, mul_assoc, mul_comm MV]
          exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMV y hy)
            (abs_nonneg t)) hM10)
        · rw [hid t y hy, sub_self, norm_zero]
          exact mul_nonneg (mul_nonneg hM10 hMV0) (abs_nonneg t)
    -- the expansion `Dφ_t = I + t DY + o(t)`
    obtain ⟨ε₁, hε₁, hε₁b⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ * (MV * MΦ) ≤ ε / 2 := by
      have h1 : 0 < MV * MΦ + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hMV0 hMΦ0) one_pos
      refine ⟨ε / 2 / (MV * MΦ + 1), div_pos (half_pos hε) h1, ?_⟩
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (half_pos hε).le
    obtain ⟨δ₂, hδ₂, hUC⟩ := Metric.uniformContinuousOn_iff_le.1
      (hK₂.uniformContinuousOn_of_continuous hD2c) ε₁ hε₁
    filter_upwards [hev MV η hη, hev MV δ₂ hδ₂,
      hev ((ε₁ * MV + M2 * MV) * MDV) (ε / 2) (half_pos hε)] with t ht1 ht2 ht3 y
    by_cases hy : y ∈ tsupport Y
    · have hyO := hYO hy
      have hΦyB := (hΦ y hyO).2.1
      obtain ⟨hsub, hmem⟩ := hball y hy t ht1
      have hΦyK : Φ y ∈ cthickening η (Φ '' tsupport Y) :=
        hsub (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0))
      have hbtw : Φ y + t • Vf y ∈ B := hηB (hsub hmem)
      have hDφ : fderiv ℝ (φ t) y = (fderiv ℝ Ψ (Φ y + t • Vf y)).comp
          (fderiv ℝ Φ y + t • fderiv ℝ Vf y) :=
        (((hΨd _ hbtw).comp y ((hΦd y hyO).add ((hVfd y hyO).const_smul t))).congr_of_eventuallyEq
          (hev0 t y hyO)).fderiv
      have hDY : fderiv ℝ Y y = (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y) +
          ((fderiv ℝ (fderiv ℝ Ψ) (Φ y)).comp (fderiv ℝ Φ y)).flip (Vf y) :=
        ((((hΨ2d _ hΦyB).comp y (hΦd y hyO)).clm_apply (hVfd y hyO)).congr_of_eventuallyEq
          (eventually_of_mem (hO.mem_nhds hyO) fun z hz => (hYΨ z hz).symm)).fderiv
      have hsymm := (hΨ _ hΦyB).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      rw [hDφ, hDY, ← hinv y hyO, halg _ _ _ _ _ _ t hsymm]
      -- mean value inequality for `DΨ` on the ball
      have hm1 := (convex_closedBall (Φ y) (|t| * MV)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f := fderiv ℝ Ψ) (φ := fderiv ℝ (fderiv ℝ Ψ) (Φ y))
        (fun c hc => (hΨ2d c (hηB (hsub hc))).hasFDerivWithinAt)
        (fun c hc => by
          rw [← dist_eq_norm]
          exact hUC c (hsub hc) _ hΦyK ((mem_closedBall.1 hc).trans ht2.le))
        (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0)) hmem
      rw [add_sub_cancel_left, map_smul] at hm1
      have hw : ‖t • Vf y‖ ≤ |t| * MV := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMV y hy) (abs_nonneg t)
      have hA1 := hm1.trans (mul_le_mul_of_nonneg_left hw hε₁.le)
      have hA2 : ‖t • fderiv ℝ (fderiv ℝ Ψ) (Φ y) (Vf y)‖ ≤ |t| * (M2 * MV) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hM2 _ hΦyK) (hMV y hy) (norm_nonneg _) hM20)) (abs_nonneg t)
      have hA3 := (norm_le_norm_add_norm_sub' _ _).trans (add_le_add hA2 hA1)
      have hT1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hA1 (hMΦ y hy) (norm_nonneg _)
          (mul_nonneg hε₁.le (mul_nonneg (abs_nonneg t) hMV0)))
      have hT2 : ‖t • ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y))‖ ≤
          |t| * ((|t| * (M2 * MV) + ε₁ * (|t| * MV)) * MDV) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hA3 (hMDV y hy) (norm_nonneg _) (by positivity))) (abs_nonneg t)
      have h1 := mul_le_mul_of_nonneg_left hε₁b (abs_nonneg t)
      have h2 := mul_le_mul_of_nonneg_left ht3.le (abs_nonneg t)
      linarith only [norm_add_le ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y) -
        t • fderiv ℝ (fderiv ℝ Ψ) (Φ y) (Vf y)).comp (fderiv ℝ Φ y))
        (t • ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y))), hT1, hT2,
        h1, h2]
    · rw [(hev1 t y hy).fderiv_eq, fderiv_id,
        image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_fderiv_subset ℝ h), smul_zero,
        sub_self, sub_zero, norm_zero]
      exact mul_nonneg hε.le (abs_nonneg t)
  -- `Good A`: a `C¹` family fixing `N` and `K = spt X` with `Dφ_t = I + t DA + o(t)` uniformly
  obtain ⟨Good, hGood⟩ : ∃ Good : (Euclid P → Euclid P) → Prop, ∀ A, Good A ↔
      ∃ φ : ℝ → Euclid P → Euclid P, ∃ C : ℝ, (∀ᶠ t in 𝓝 (0:ℝ), ContDiff ℝ 1 (φ t) ∧
        (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
        ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t| :=
    ⟨_, fun _ => Iff.rfl⟩
  -- composition: `Good A`, `Good B` give `Good (A + B)` (`DA` uniformly continuous)
  have gadd : ∀ A B : Euclid P → Euclid P, ContDiff ℝ 1 A → HasCompactSupport A →
      ContDiff ℝ 1 B → HasCompactSupport B → Good A → Good B → Good (A + B) := by
    intro A B hA hAc hB hBc hGA hGB
    obtain ⟨φ, C₁, hφ, eφ⟩ := (hGood A).1 hGA
    obtain ⟨ψ, C₂, hψ, eψ⟩ := (hGood B).1 hGB
    refine (hGood _).2 ⟨fun t => φ t ∘ ψ t, C₁ + C₂, ?_, fun ε hε => ?_⟩
    · filter_upwards [hφ, hψ] with t h g
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨g1, g2, g3, g4⟩ := g
      refine ⟨h1.comp g1, fun x hx => ?_, h3.comp g3, fun x => ?_⟩
      · rw [Function.comp_apply, g2 x hx, h2 x hx]
      · rw [Function.comp_apply, add_mul]
        exact (norm_sub_le_norm_sub_add_norm_sub _ (ψ t x) _).trans (add_le_add (h4 _) (g4 _))
    · obtain ⟨MA, hMA⟩ :=
        (hAc.fderiv ℝ).exists_bound_of_continuous (hA.continuous_fderiv one_ne_zero)
      obtain ⟨MB, hMB⟩ :=
        (hBc.fderiv ℝ).exists_bound_of_continuous (hB.continuous_fderiv one_ne_zero)
      have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
      have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
      have hε4 : 0 < ε / 4 := by positivity
      obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuous_iff.1
        ((hAc.fderiv ℝ).uniformContinuous_of_continuous (hA.continuous_fderiv one_ne_zero)) _ hε4
      filter_upwards [hφ, hψ, eφ (ε / 8) (by positivity), eψ (ε / 4) hε4,
        hev (ε / 4 + MB) 1 one_pos, hev ((ε / 4 + MB) * MA) (ε / 4) hε4, hev C₂ η hη]
        with t h g e1 e2 k1 k2 k3 x
      obtain ⟨h1, -, -, -⟩ := h
      obtain ⟨g1, -, -, g4⟩ := g
      rw [fderiv_comp x ((h1.differentiable one_ne_zero) _) ((g1.differentiable one_ne_zero) _),
        ((hA.differentiable one_ne_zero x).hasFDerivAt.add
          (hB.differentiable one_ne_zero x).hasFDerivAt).fderiv, halg2 _ _ _ (fderiv ℝ A (ψ t x))]
      have e1' := e1 (ψ t x)
      have e2' := e2 x
      have htb : ‖t • fderiv ℝ B x‖ ≤ |t| * MB := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMB x) (abs_nonneg t)
      have hQI := (norm_le_norm_add_norm_sub' (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _)
        (t • fderiv ℝ B x)).trans (add_le_add htb e2')
      have hQ2 : ‖fderiv ℝ (ψ t) x‖ ≤ 2 := by
        have := (norm_le_norm_add_norm_sub' (fderiv ℝ (ψ t) x) (ContinuousLinearMap.id ℝ _)).trans
          (add_le_add ContinuousLinearMap.norm_id_le hQI)
        linarith only [this, k1]
      have hT1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul e1' hQ2 (norm_nonneg _) (mul_nonneg (by positivity) (abs_nonneg t)))
      have hT3 : ‖t • (fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _)‖ ≤
          |t| * (MA * (|t| * MB + ε / 4 * |t|)) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hMA _) hQI (norm_nonneg _) hMA0)) (abs_nonneg t)
      have hT4 : ‖t • (fderiv ℝ A (ψ t x) - fderiv ℝ A x)‖ ≤ |t| * (ε / 4) := by
        rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
        refine mul_le_mul_of_nonneg_left (hUC ?_).le (abs_nonneg t)
        rw [dist_eq_norm]
        exact (g4 x).trans_lt (by rw [mul_comm]; exact k3)
      have h2 := mul_le_mul_of_nonneg_left k2.le (abs_nonneg t)
      linarith only [norm_add₄_le (a := ((fderiv ℝ (φ t) (ψ t x) - ContinuousLinearMap.id ℝ _ -
        t • fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x))) (b := fderiv ℝ (ψ t) x -
          ContinuousLinearMap.id ℝ _ - t • fderiv ℝ B x)
        (c := t • (fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _))
        (d := t • (fderiv ℝ A (ψ t x) - fderiv ℝ A x)), hT1, e2', hT3, hT4, h2]
  -- near `p ∈ N`: straighten `N` by `Ψ x = ψ(vp + g x) + (x - A g x)` (`g A = id`, `DΨ(0) = I`)
  have glocal : ∀ p ∈ N, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∀ χ : Euclid P → ℝ,
      ContDiff ℝ 1 χ → tsupport χ ⊆ O → Good (fun x => χ x • X x) := by
    intro p hp
    obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hψinj, hψim, hψprop, hψD⟩ := hN p hp
    obtain ⟨vp, hvpV, hvp⟩ : p ∈ ψ '' V := by rw [hψim]; exact ⟨hpW, hp⟩
    have hψ2 : ∀ v ∈ V, ContDiffAt ℝ 2 ψ v := fun v hv => hψ.contDiffAt (hV.mem_nhds hv)
    obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ ψ vp := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Euclid P →L[ℝ] Euclid d, ∀ a, g (A a) = a := by
      obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective (A : Euclid d →ₗ[ℝ] Euclid P)
        (LinearMap.ker_eq_bot.2 (by rw [hA]; exact hψD vp hvpV))
      exact ⟨LinearMap.toContinuousLinearMap g', fun a => LinearMap.congr_fun hg' a⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid P → Euclid P, ∀ x, Ψ x = ψ (vp + g x) + (x - A (g x)) :=
      ⟨_, fun _ => rfl⟩
    have hΨC : ∀ x, vp + g x ∈ V → ContDiffAt ℝ 2 Ψ x := fun x hx =>
      (((hψ2 _ hx).comp x (contDiffAt_const.add g.contDiff.contDiffAt)).add
        (contDiffAt_id.sub (A.comp g).contDiff.contDiffAt)).congr_of_eventuallyEq
        (Eventually.of_forall hΨ)
    have hΨD : ∀ x, vp + g x ∈ V → HasFDerivAt Ψ ((fderiv ℝ ψ (vp + g x)).comp g +
        (ContinuousLinearMap.id ℝ _ - A.comp g)) x := fun x hx =>
      ((((hψ2 _ hx).differentiableAt two_ne_zero).hasFDerivAt.comp x
        (g.hasFDerivAt.const_add vp)).add ((hasFDerivAt_id x).sub
          (A.comp g).hasFDerivAt)).congr_of_eventuallyEq (Eventually.of_forall hΨ)
    have h0V : vp + g 0 ∈ V := by rw [map_zero, add_zero]; exact hvpV
    have hΨD0 : HasFDerivAt Ψ
        ((ContinuousLinearEquiv.refl ℝ (Euclid P) : Euclid P ≃L[ℝ] Euclid P) :
          Euclid P →L[ℝ] Euclid P) 0 := by
      have h := hΨD 0 h0V
      rw [map_zero, add_zero, ← hA, add_sub_cancel] at h
      rw [ContinuousLinearEquiv.coe_refl]
      exact h
    -- inverse function theorem
    have hstrict := (hΨC 0 h0V).hasStrictFDerivAt' hΨD0 two_ne_zero
    obtain ⟨H, hHcoe, h0H⟩ : ∃ H : OpenPartialHomeomorph (Euclid P) (Euclid P),
        ⇑H = Ψ ∧ (0 : Euclid P) ∈ H.source :=
      ⟨hstrict.toOpenPartialHomeomorph Ψ, hstrict.toOpenPartialHomeomorph_coe,
        hstrict.mem_toOpenPartialHomeomorph_source⟩
    have hΩ : IsOpen {x : Euclid P | vp + g x ∈ V} :=
      hV.preimage (continuous_const.add g.continuous)
    have hDΨc : ContinuousOn (fderiv ℝ Ψ) {x : Euclid P | vp + g x ∈ V} := fun x hx =>
      ((hΨC x hx).continuousAt_fderiv two_ne_zero).continuousWithinAt
    obtain ⟨B, hBo, h0B, hBH, hBV, hBe⟩ : ∃ B : Set (Euclid P), IsOpen B ∧ (0 : Euclid P) ∈ B ∧
        (∀ b ∈ B, b ∈ H.source) ∧ (∀ b ∈ B, vp + g b ∈ V) ∧
        ∀ b ∈ B, ∃ e : Euclid P ≃L[ℝ] Euclid P, (e : Euclid P →L[ℝ] Euclid P) = fderiv ℝ Ψ b :=
      ⟨_, H.open_source.inter (hDΨc.isOpen_inter_preimage hΩ ContinuousLinearEquiv.isOpen),
        ⟨h0H, h0V, _, hΨD0.fderiv.symm⟩, fun b hb => hb.1, fun b hb => hb.2.1, fun b hb => hb.2.2⟩
    obtain ⟨O, hOo, hO⟩ : ∃ O : Set (Euclid P), IsOpen O ∧
        ∀ y, y ∈ O ↔ y ∈ H.target ∧ H.symm y ∈ B :=
      ⟨_, H.isOpen_inter_preimage_symm hBo, fun y => Iff.rfl⟩
    have hΦ : ∀ y ∈ O, ContDiffAt ℝ 2 H.symm y ∧ H.symm y ∈ B ∧ Ψ (H.symm y) = y ∧
        ∀ u, fderiv ℝ H.symm y (fderiv ℝ Ψ (H.symm y) u) = u := by
      intro y hy
      obtain ⟨hyT, hyB⟩ := (hO y).1 hy
      obtain ⟨e, he⟩ := hBe _ hyB
      have hC : ContDiffAt ℝ 2 Ψ (H.symm y) := hΨC _ (hBV _ hyB)
      have hD : HasFDerivAt H (e : Euclid P →L[ℝ] Euclid P) (H.symm y) := by
        rw [hHcoe, he]; exact (hC.differentiableAt two_ne_zero).hasFDerivAt
      refine ⟨H.contDiffAt_symm hyT hD (hHcoe ▸ hC), hyB, hHcoe ▸ H.right_inv hyT, fun u => ?_⟩
      rw [(H.hasFDerivAt_symm hyT hD).fderiv, ← he]
      exact e.symm_apply_apply u
    have hΨB : ∀ b ∈ B, H.symm (Ψ b) = b := fun b hb => hHcoe ▸ H.left_inv (hBH b hb)
    have hpO : p ∈ O := by
      have hΨ0 : Ψ 0 = p := by rw [hΨ, map_zero, add_zero, map_zero, sub_zero, add_zero, hvp]
      rw [← hΨ0]
      refine (hO _).2 ⟨hHcoe ▸ H.map_source (hBH 0 h0B), ?_⟩
      rw [hΨB 0 h0B]; exact h0B
    -- the slice: near `p`, `Φ = H.symm` maps `N` into `{x | A (g x) = x}`
    obtain ⟨ε₁, hε₁, hε₁B⟩ : ∃ ε₁ > 0, ∀ v', dist v' vp < ε₁ → A (v' - vp) ∈ B := by
      have hc : Continuous fun v' => A (v' - vp) :=
        A.continuous.comp (continuous_id.sub continuous_const)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hBo.preimage hc) vp
        (by show A (vp - vp) ∈ B; rw [sub_self, map_zero]; exact h0B)
      exact ⟨ε, hε, fun v' hv' => hball (mem_ball.2 hv')⟩
    obtain ⟨δ₁, hδ₁, hδ₁V⟩ := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn
      hψinj (by rw [hψim]; exact inter_subset_left) hψprop vp hvpV ε₁ hε₁
    have hsl : ∀ z ∈ N, z ∈ O ∩ (W ∩ ball p δ₁) → A (g (H.symm z)) = H.symm z := by
      rintro z hzN ⟨-, hzW, hzp⟩
      obtain ⟨v', hv'V, rfl⟩ : z ∈ ψ '' V := by rw [hψim]; exact ⟨hzW, hzN⟩
      have hx := hε₁B v' (hδ₁V v' hv'V (by rw [hvp]; exact hzp))
      have hΨx : Ψ (A (v' - vp)) = ψ v' := by
        rw [hΨ, hg, add_sub_cancel, sub_self, add_zero]
      rw [← hΨx, hΨB _ hx, hg]
    refine ⟨O ∩ (W ∩ ball p δ₁), hOo.inter (hW.inter isOpen_ball), ⟨hpO, hpW, mem_ball_self hδ₁⟩,
      fun χ hχ hχO => ?_⟩
    -- the local field `Y = χ X` and its deformation `Ψ (Φ y + t DΦ(y) Y(y))`
    have hYX : tsupport (fun x => χ x • X x) ⊆ tsupport X := tsupport_smul_subset_right _ _
    have hYO : tsupport (fun x => χ x • X x) ⊆ O ∩ (W ∩ ball p δ₁) :=
      (tsupport_smul_subset_left _ _).trans hχO
    obtain ⟨Vf, hVf⟩ : ∃ Vf : Euclid P → Euclid P, ∀ y, Vf y = fderiv ℝ H.symm y (χ y • X y) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → Euclid P → Euclid P,
        ∀ t y, φ t y = if y ∈ O then Ψ (H.symm y + t • Vf y) else y := ⟨_, fun _ _ => rfl⟩
    obtain ⟨hid, C, hφev, hexp⟩ := gconj Ψ H.symm (fun x => χ x • X x) Vf φ B O hBo hOo
      (fun b hb => hΨC b (hBV b hb)) (fun y hy => ⟨(hΦ y hy).1, (hΦ y hy).2.1, (hΦ y hy).2.2.1⟩)
      (hχ.smul hX) (hXc.mono (support_smul_subset_right χ X)) (fun y hy => (hYO hy).1) hVf hφ
    -- tangency: `DΦ(z) Y(z)` lies in `{x | A (g x) = x}` for `z ∈ N`
    have htan : ∀ z ∈ N, z ∈ tsupport (fun x => χ x • X x) → A (g (Vf z)) = Vf z := by
      intro z hzN hzY
      have hsz := hsl z hzN (hYO hzY)
      obtain ⟨-, hzB, hΨz, hinvz⟩ := hΦ z (hYO hzY).1
      have hzψ : ψ (vp + g (H.symm z)) = z := by
        rw [hΨ, hsz, sub_self, add_zero] at hΨz; exact hΨz
      have hT := Submission.chart_tangentSpace_eq_range_fderiv P d 2 N W V ψ (vp + g (H.symm z))
        (by norm_num) hV hW hψ hψinj hψim hψprop hψD (hBV _ hzB)
      rw [hzψ] at hT
      obtain ⟨h, hh⟩ : X z ∈ range (fderiv ℝ ψ (vp + g (H.symm z))) := by
        rw [← hT]; exact hXT z ⟨hzN, hXU (hYX hzY)⟩
      have hDΨu : fderiv ℝ Ψ (H.symm z) (A (χ z • h)) = χ z • X z := by
        rw [(hΨD _ (hBV _ hzB)).fderiv, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hg, sub_self, add_zero,
          map_smul, hh]
      rw [hVf, ← hDΨu, hinvz, hg]
    refine (hGood _).2 ⟨φ, C, ?_, hexp⟩
    filter_upwards [hφev] with t ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨h1, fun x hx => hid t x fun h => hx (hYX h), fun z hz => ?_, h3⟩
    by_cases hzY : z ∈ tsupport (fun x => χ x • X x)
    · have hS : A (g (H.symm z + t • Vf z)) = H.symm z + t • Vf z := by
        rw [map_add, map_smul, map_add, map_smul, hsl z hz (hYO hzY), htan z hz hzY]
      rw [hφ, ite_eq_left (hYO hzY).1, hΨ, hS, sub_self, add_zero]
      exact ((Set.ext_iff.1 hψim _).1 (mem_image_of_mem ψ (hBV _ (h2 z hzY)))).2
    · rw [hid t z hzY]; exact hz
  -- `N ∩ K` is compact, as `(N̄ \ N) ∩ U = ∅`
  have hNK : IsCompact (N ∩ tsupport X) := by
    have h : N ∩ tsupport X = closure N ∩ tsupport X := by
      refine Subset.antisymm (inter_subset_inter_left _ subset_closure) fun x hx => ⟨?_, hx.2⟩
      by_contra hxN
      exact (hNU.subset ⟨⟨hx.1, hxN⟩, hXU hx.2⟩ : x ∈ (∅ : Set (Euclid P)))
    rw [h]; exact hXc.isCompact.inter_left isClosed_closure
  -- a partition of unity subordinate to finitely many straightening charts and `U \ N̄`
  choose O hOo hpO hOgood using fun p : ↥(N ∩ tsupport X) => glocal p.1 p.2.1
  obtain ⟨s, hs⟩ := hNK.elim_finite_subcover O hOo fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
  have hGopen : ∀ j : Option ↥s, IsOpen (Option.elim j (U \ closure N) fun i => O i.1) := by
    rintro (_ | i)
    · exact hU.sdiff isClosed_closure
    · exact hOo _
  have hGcover : tsupport X ⊆ ⋃ j : Option ↥s, Option.elim j (U \ closure N) fun i => O i.1 := by
    intro x hx
    by_cases hxN : x ∈ N
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hs ⟨hxN, hx⟩)
      exact mem_iUnion.2 ⟨some ⟨i, hi⟩, hxi⟩
    · exact mem_iUnion.2 ⟨none, hXU hx, fun hxc =>
        (hNU.subset ⟨⟨hxc, hxN⟩, hXU hx⟩ : x ∈ (∅ : Set (Euclid P)))⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) (isClosed_tsupport X) _ hGopen hGcover
  have hfC : ∀ j, ContDiff ℝ 1 (f j) := fun j =>
    (contMDiff_iff_contDiff.1 (f j).contMDiff).of_le (by exact_mod_cast le_top)
  have hdecomp : ∑ j, (fun x => f j x • X x) = X := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ tsupport X
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, smul_zero, Finset.sum_const_zero]
  have hpieces : ∀ j ∈ (Finset.univ : Finset (Option ↥s)), ContDiff ℝ 1 (fun x => f j x • X x) ∧
      HasCompactSupport (fun x => f j x • X x) ∧ Good (fun x => f j x • X x) := by
    rintro (_ | i) -
    · -- away from `N`: `id + t f₀ X`, as `f₀ X = 0` on `N`
      have hAC : ContDiff ℝ 1 (fun x => f none x • X x) := (hfC _).smul hX
      have hAc : HasCompactSupport (fun x => f none x • X x) :=
        hXc.mono (support_smul_subset_right (f none) X)
      refine ⟨hAC, hAc, (hGood _).2 ?_⟩
      obtain ⟨MA, hMA⟩ := hAc.exists_bound_of_continuous hAC.continuous
      refine ⟨fun t x => x + t • (f none x • X x), MA, Eventually.of_forall fun t =>
        ⟨contDiff_id.add (hAC.const_smul t), fun x hx => ?_, fun z hz => ?_, fun x => ?_⟩,
        fun ε hε => Eventually.of_forall fun t x => ?_⟩
      · beta_reduce
        rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero, add_zero]
      · have hz0 : f none z = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => (hf none h).2 (subset_closure hz)
        beta_reduce
        rw [hz0, zero_smul, smul_zero, add_zero]; exact hz
      · beta_reduce
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hMA x) (abs_nonneg t)
      · have hd : HasFDerivAt (fun x => x + t • (f none x • X x)) (ContinuousLinearMap.id ℝ _ +
            t • fderiv ℝ (fun x => f none x • X x) x) x :=
          (hasFDerivAt_id x).add ((hAC.differentiable one_ne_zero x).hasFDerivAt.const_smul t)
        beta_reduce
        rw [hd.fderiv, add_sub_cancel_left, sub_self, norm_zero]
        exact mul_nonneg hε.le (abs_nonneg t)
    · exact ⟨(hfC _).smul hX, hXc.mono (support_smul_subset_right (f (some i)) X),
        hOgood i.1 (f (some i)) (hfC _) (hf (some i))⟩
  obtain ⟨-, -, hGX⟩ := Finset.sum_induction_nonempty (fun j x => f j x • X x)
    (fun A => ContDiff ℝ 1 A ∧ HasCompactSupport A ∧ Good A)
    (fun A B hA hB => ⟨hA.1.add hB.1, hA.2.1.add hB.2.1,
      gadd A B hA.1 hA.2.1 hB.1 hB.2.1 hA.2.2 hB.2.2⟩)
    Finset.univ_nonempty hpieces
  rw [hdecomp] at hGX
  -- final family: `φ_t` for good small `t` (where `‖Dφ_t - I‖ ≤ 1/2`), `id` otherwise
  obtain ⟨φ, C, hφ, hexp⟩ := (hGood X).1 hGX
  obtain ⟨MX, hMX⟩ := (hXc.fderiv ℝ).exists_bound_of_continuous (hX.continuous_fderiv one_ne_zero)
  obtain ⟨η, hη, hηU⟩ := hXc.isCompact.exists_cthickening_subset_open hU hXU
  obtain ⟨G, hG⟩ : ∃ G : ℝ → Prop, ∀ t, G t ↔ (ContDiff ℝ 1 (φ t) ∧
      (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
      (∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤
        1 / 4 * |t|) ∧ |t| * 1 < 1 ∧ |t| * MX < 1 / 4 ∧ |t| * C < η := ⟨_, fun _ => Iff.rfl⟩
  have hGev : ∀ᶠ t in 𝓝 (0:ℝ), G t := by
    filter_upwards [hφ, hexp (1 / 4) (by norm_num), hev 1 1 one_pos, hev MX (1 / 4) (by norm_num),
      hev C η hη] with t h1 h2 h3 h4 h5
    exact (hG t).2 ⟨h1, h2, h3, h4, h5⟩
  refine ⟨fun t => if G t then φ t else id, fun t => ?_, fun ε hε => ?_⟩
  · by_cases ht : G t
    · simp only [ht, ↓reduceIte]
      obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := (hG t).1 ht
      have hD : ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)‖ ≤ 1 / 2 := by
        intro x
        have hx := (norm_le_norm_add_norm_sub' (fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ _)
          (t • fderiv ℝ X x)).trans (add_le_add le_rfl (h5 x))
        rw [norm_smul, Real.norm_eq_abs] at hx
        have := mul_le_mul_of_nonneg_left (hMX x) (abs_nonneg t)
        linarith only [hx, this, h6, h7]
      have hdiff : Differentiable ℝ (φ t) := h1.differentiable one_ne_zero
      have happrox : ApproximatesLinearOn (φ t)
          ((ContinuousLinearEquiv.refl ℝ (Euclid P) : Euclid P ≃L[ℝ] Euclid P) :
            Euclid P →L[ℝ] Euclid P) univ (1 / 2 : NNReal) := by
        intro x _ y _
        have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := φ t)
          (φ := ContinuousLinearMap.id ℝ (Euclid P)) (s := univ)
          (fun z _ => (hdiff z).hasFDerivAt.hasFDerivWithinAt) (fun z _ => hD z) convex_univ
          (mem_univ y) (mem_univ x)
        simpa using this
      have hc : Subsingleton (Euclid P) ∨ (1 / 2 : NNReal) <
          ‖(((ContinuousLinearEquiv.refl ℝ (Euclid P)).symm : Euclid P ≃L[ℝ] Euclid P) :
            Euclid P →L[ℝ] Euclid P)‖₊⁻¹ := by
        rcases subsingleton_or_nontrivial (Euclid P) with h | h
        · exact Or.inl h
        · right; simp; norm_num
      refine ⟨h1, ⟨injOn_univ.1 (happrox.injOn hc), happrox.surjective hc⟩, fun x v w hvw => ?_,
        h2, fun x hx => ⟨h3 hx.1, ?_⟩⟩
      · have h0 := (fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ _).le_of_opNorm_le (hD x) (v - w)
        rw [sub_apply, map_sub, hvw, sub_self, zero_sub, norm_neg,
          ContinuousLinearMap.id_apply] at h0
        exact sub_eq_zero.1 (norm_le_zero_iff.1 (by linarith only [h0, norm_nonneg (v - w)]))
      · by_cases hxK : x ∈ tsupport X
        · refine hηU (mem_cthickening_of_dist_le _ x _ _ hxK ?_)
          rw [dist_eq_norm]
          exact (h4 x).trans (by rw [mul_comm]; exact h8.le)
        · rw [h2 x hxK]; exact hx.2
    · simp only [ht, ↓reduceIte]
      refine ⟨contDiff_id, bijective_id, fun x => ?_, fun x _ => rfl, fun x hx => hx⟩
      rw [fderiv_id]; exact injective_id
  · obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (hGev.and (hexp ε hε))
    refine ⟨δ, hδ, fun t ht x => ?_⟩
    obtain ⟨hGt, h2⟩ := h (show dist t 0 < δ by rwa [Real.dist_eq, sub_zero])
    simp only [hGt, ↓reduceIte]
    exact h2 x

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
