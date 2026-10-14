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

/-- **A covector vanishing on all increasing tuples of standard basis vectors is zero**
(definiteness of the Euclidean coefficient norm).  With `e` the standard basis of `ℝᴾ`, an
alternating map is determined by its values `α(e_{J(0)}, …, e_{J(n-1)})` on injective
`J : Fin n → Fin P`.  For such `J`, `σ = Tuple.sort J` makes `J ∘ σ` monotone and injective, hence
strictly increasing, so `0 = α(e_{J ∘ σ}) = sign σ • α(e_J)` with `sign σ = ±1`. -/
theorem Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords : ∀ (P n : ℕ) (α : Covector (Euclid P) n), (∀ I : Fin n → Fin P, StrictMono I → α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) = 0) → α = 0 := by
  intro P n α h
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 1: it suffices to check `α(e_J) = 0` for injective `J`
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine e.ext_alternating fun J hJ => ?_
  show α (fun i => e (J i)) = (0 : ℝ)
  -- Step 2: sorting `J` gives a strictly increasing `J ∘ σ`
  have hmono : StrictMono (J ∘ Tuple.sort J) :=
    (Tuple.monotone_sort J).strictMono_of_injective (hJ.comp (Tuple.sort J).injective)
  -- Step 3: `0 = α(e_J ∘ σ) = sign σ • α(e_J)`, and `sign σ = ±1`
  have h1 : α.toAlternatingMap ((fun i => e (J i)) ∘ Tuple.sort J) = 0 := h _ hmono
  rw [AlternatingMap.map_perm] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort J)) with hs | hs <;> simpa [hs] using h1
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
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Dilations of currents in `ℝᴾ` exist and agree with the blow-up `η_{a,λ#}`** (Simon Ch. 3,
1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413).  Call
`X' ∈ 𝒟ₘ(ℝᴾ)` a dilation of `X` if `X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`, `η = η_{a,λ}`.
Since `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`, so `η_{a,λ#}X ∈ 𝒟ₘ(η(ℝᴾ))` restricts to `ℝᴾ`.  (i) This
restriction is a dilation of `X`; (ii) every dilation `X'` of `X` agrees with `η_{a,λ#}X`:
`X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω₁ ∈ 𝒟ᵐ(η(ℝᴾ))` has the underlying form of `ω`.  Both follow
from `Submission.dtc_blowUp_testForm_corr` with `U = ℝᴾ`. -/
theorem Submission.cbr_cidc_dilation_exists_eq_blowUp : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ (ω : TestFormOn (univ : Set (Euclid P)) m) (ω₁ : TestFormOn (dilation a lam '' (univ : Set (Euclid P))) m), (ω₁ : DifferentialForm (Euclid P) m) = (ω : DifferentialForm (Euclid P) m) → X' ω = blowUp X a lam hlam.ne' ω₁ := by
  intro P m a lam hlam
  obtain ⟨hA, -, hC⟩ := Submission.dtc_blowUp_testForm_corr P m univ a lam hlam
  -- Step 1: `η` maps `ℝᴾ` onto `ℝᴾ`, since `η(a + λy) = y`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by
      simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']⟩
  refine ⟨fun X => ?_, fun X X' hX' ω ω₁ hω => ?_⟩
  · -- Step 2, (i): the restriction of `η_{a,λ#}X` to `ℝᴾ` is a dilation of `X`, by part (c).
    refine ⟨(blowUp X a lam hlam.ne').restrictDomain hsurj, fun ω ω' hωω' => ?_⟩
    rw [GeometricCurrentOn.restrictDomain_apply]
    exact hC X _ ω' (by simpa using hωω')
  · -- Steps 3–4, (ii): part (a) gives `ω' = ω₁ ∘ η = ω ∘ η`, and part (c) and the dilation
    -- property give `η_{a,λ#}X(ω₁) = λ⁻ᵐ X(ω') = X'(ω)`.
    obtain ⟨ω', hω'⟩ := hA ω₁
    rw [hC X ω₁ ω' hω', hX' ω ω' (fun y => by rw [hω', hω])]
/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl

/-- **Dilations commute with the boundary** (Simon 6.2.3, chapter-06.txt line 216, and
6.2.24(1), line 414, for `η = η_{a,λ}`, `λ > 0`; the dilations of the closure theorem 6.8.2):
if `X'(ω) = λ^{-(m+1)} X(ω ∘ η)` on `𝒟^{m+1}(ℝᴾ)`, then `∂X'(ω) = λ⁻ᵐ ∂X(ω ∘ η)` on `𝒟ᵐ(ℝᴾ)`.

`η` maps `ℝᴾ` onto itself, so `ω` is also a test form `ω₁` in `η(ℝᴾ)`, and `dω`, `dω₁` have the
same underlying form.  Hence
`∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`
(`cbr_cidc_dilation_exists_eq_blowUp`, `dtc_blowUp_algebra` (iv), `dtc_blowUp_testForm_corr` (c)). -/
theorem Submission.cbr_cidc_dilation_boundary : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω' := by
  intro P m a lam hlam X X' hX ω ω' hω
  -- Step 1: `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and `ω` is a test form `ω₁` in `η(ℝᴾ)`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  let ω₁ : TestFormOn (dilation a lam '' univ) m := testFormOnInclusion hsurj m ω
  -- Step 2: `X'(dω) = η_#X(dω₁)`, as `dω₁` and `dω` are the same form.
  have h1 := (Submission.cbr_cidc_dilation_exists_eq_blowUp P (m + 1) a lam hlam).2 X X' hX
    (exteriorDerivativeTestOn univ m ω) (exteriorDerivativeTestOn _ m ω₁) rfl
  -- Steps 2–3: `∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁)`.
  rw [GeometricCurrentOn.boundary_apply, h1, ← GeometricCurrentOn.boundary_apply,
    (Submission.dtc_blowUp_algebra P univ a lam hlam).2.2.2 m X]
  -- Step 4: `η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`, as `ω' = ω ∘ η = ω₁ ∘ η`.
  exact (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).2.2 X.boundary ω₁ ω' hω

/-- **A dilation of an integer multiplicity current is integer multiplicity** (item (3) of the
dilation calculus for `η = η_{a,λ}`, `λ > 0`: Simon Ch. 6, 3.3–3.9 for the push-forward 6.2.23,
as used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  If `R = (M, θ, ξ)`
represents `X` in `ℝᴾ`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
(`dtc_blowUp_imrep`).  As `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`: `R'` is also a triple in `ℝᴾ` (a compact
`K ⊆ ℝᴾ` lies in `η(ℝᴾ)`), and `X'(ω) = η_{a,λ#}X(ω) = R'(ω)` for every test form `ω` on `ℝᴾ`
(`cbr_cidc_dilation_exists_eq_blowUp`). -/
theorem Submission.cbr_cidc_dilation_isIntegerMultiplicity : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X' := by
  intro P m a lam hlam X X' hX hXim
  obtain ⟨R, hR⟩ := hXim
  -- `η = η_{a,λ}` is onto, `η(a + λy) = y`, so `ℝᴾ ⊆ η(ℝᴾ)`
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  -- `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
  obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P m univ X a lam hlam R hR
  -- the same triple in `ℝᴾ`: of its conditions only local integrability involves the domain
  refine ⟨{ carrier := R'.carrier
            mult := R'.mult
            orient := R'.orient
            measurableSet_carrier := R'.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := R'.rectifiable
            measurable_mult := R'.measurable_mult
            mult_pos := R'.mult_pos
            locallyIntegrable_mult := fun K hK _ =>
              R'.locallyIntegrable_mult K hK ((subset_univ K).trans hsurj)
            aestronglyMeasurable_orient := R'.aestronglyMeasurable_orient
            orients := R'.orients }, ?_⟩
  -- `X'(ω) = η_{a,λ#}X(ω) = R'(ω)`, with `ω` regarded as a test form in `η(ℝᴾ)`
  intro ω
  rw [(Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX ω
    (testFormOnInclusion hsurj m ω) rfl, hR' (testFormOnInclusion hsurj m ω)]
  rfl

/-- **Integral representations under the dilation `η = η_{a,λ}`, `λ > 0`** (Simon 6.2.7 and
Remark 6.2.24(2), chapter-06.txt lines 271 and 414–419, for `f = η`; `η` as in Ch. 3, 1.4,
chapter-03.txt line 85).  If `X'` is a dilation of `X` (`X'(ω) = λ⁻ᵐ X(ω')` whenever
`ω' = ω ∘ η`) and `X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`, then
`X'(ω) = ∫ ⟨ω(y), ξ(a + λy)⟩ d(λ⁻ᵐ η_*μ)(y)`: take `ω' = ω ∘ η`, change variables `y = η(x)`
(`η` is a homeomorphism, hence a measurable embedding) and use `a + λη(x) = x`. -/
theorem Submission.cbr_cidc_dilation_integral_rep : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) := by
  intro P m a lam hlam X X' μ ξ hX hrep ω
  have hne : lam ≠ 0 := hlam.ne'
  -- `η = η_{a,λ}` (`y ↦ −λ⁻¹a + λ⁻¹y`) and `ι(z) = a + λz` are mutually inverse.
  have hηι : ∀ y, dilation a lam (a + lam • y) = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ x, a + lam • dilation a lam x = x := by
    intro x
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  -- Step 1: `η` maps `ℝᴾ` onto itself, so `ω ∈ 𝒟ᵐ(η(ℝᴾ))`, and the accepted
  -- `dtc_blowUp_testForm_corr` (a) gives `ω' ∈ 𝒟ᵐ(ℝᴾ)` with `ω' = ω ∘ η`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ :=
    fun y _ => ⟨a + lam • y, mem_univ _, hηι y⟩
  obtain ⟨ω', hω'⟩ :=
    (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).1 (testFormOnInclusion hsurj m ω)
  -- Step 2: `X'(ω) = λ⁻ᵐ X(ω') = λ⁻ᵐ ∫ ⟨ω'(x), ξ(x)⟩ dμ(x)`.
  rw [hX ω ω' (fun y => by simpa using hω' y), hrep ω']
  -- Step 3: `η` is a homeomorphism, hence a measurable embedding, so
  -- `∫ g d(η_*μ) = ∫ g ∘ η dμ` for every `g` (no integrability needed).
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have hη : ⇑η = dilation a lam := by
    funext y
    simp [η, dilation, dilationCLM]
  have hemb : MeasurableEmbedding (dilation a lam) := hη ▸ η.measurableEmbedding
  -- Steps 4–5: `∫ g d(c • ν) = c.toReal * ∫ g dν` with `(ofReal λ⁻ᵐ).toReal = λ⁻ᵐ`; for
  -- `g(y) = ⟨ω(y), ξ(a + λy)⟩`, `g(η(x)) = ⟨ω'(x), ξ(x)⟩` because `a + λη(x) = x`.
  rw [integral_smul_measure, hemb.integral_map, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hιη x, hω' x, testFormOnInclusion_coe]
/-- **Mass scaling for dilations: `M_{η(W)}(X') = λ⁻ᵐ M_W(X)`** for `η = η_{a,λ}`, `λ > 0`, a
dilation `X' ∈ 𝒟ₘ(ℝᴾ)` of `X ∈ 𝒟ₘ(ℝᴾ)` (`X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`) and every
`W ⊆ ℝᴾ` (item (5) of the dilation calculus for the integer-multiplicity criterion for cycles;
`η_{x,λ}` of Simon Ch. 3, 1.4, chapter-03.txt line 85; mass `M_W` of 6.2.5, chapter-06.txt
lines 221–233, with the Euclidean coefficient norm).  `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and
`𝒟ᵐ(ℝᴾ)`, `𝒟ᵐ(η(ℝᴾ))` consist of the same forms, with the same admissible forms for `M_{η(W)}`.
By `Submission.cbr_cidc_dilation_exists_eq_blowUp`, `X'(ω) = η_{a,λ#}X(ω)` on equal forms, so
`M_{η(W)}(X') = M_{η(W)}(η_{a,λ#}X)`, which is `λ⁻ᵐ M_W(X)` by
`Submission.dtc_blowUp_massOn_image`. -/
theorem Submission.cbr_cidc_dilation_massOn_image : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W := by
  intro P m a lam hlam X X' hX W
  -- `η = η_{a,λ}` is onto (`η(a + λy) = y`), so `ℝᴾ` and `η(ℝᴾ)` have the same test forms.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  have hsub : dilation a lam '' (univ : Set (Euclid P)) ⊆ univ := subset_univ _
  -- `X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω` and `ω₁` have the same underlying form.
  have hblow := (Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX
  refine Eq.trans ?_ (Submission.dtc_blowUp_massOn_image P m univ X a lam hlam W)
  -- The admissible forms for `M_{η(W)}(X')` and `M_{η(W)}(η_{a,λ#}X)` are the same forms, on
  -- which `X'` and `η_{a,λ#}X` agree.
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨testFormOnInclusion hsurj m φ, hφ,
      congrArg ENNReal.ofReal (hblow φ (testFormOnInclusion hsurj m φ) rfl).symm⟩
  · rintro ⟨φ₁, hφ₁, rfl⟩
    exact ⟨testFormOnInclusion hsub m φ₁, hφ₁,
      congrArg ENNReal.ofReal (hblow (testFormOnInclusion hsub m φ₁) φ₁ rfl)⟩

/-- **Dilation calculus for currents in `ℝᴾ`** (Simon Ch. 6, 2.23 for the similarity
`η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`; used to rescale cycles in the proof that cycles with
the integer slice property are integer multiplicity).  Call `X' ∈ 𝒟ₘ(ℝᴾ)` a dilation of `X` if
`X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`.  (1) Since `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`, and the
restriction of `η_{a,λ#}X ∈ 𝒟ₘ(η(ℝᴾ))` to `ℝᴾ` is a dilation of `X` by part (c) of
`Submission.dtc_blowUp_testForm_corr`.  (2)–(5) are `Submission.cbr_cidc_dilation_boundary`,
`Submission.cbr_cidc_dilation_isIntegerMultiplicity`, `Submission.cbr_cidc_dilation_integral_rep`
and `Submission.cbr_cidc_dilation_massOn_image`; (6) is part (i) of
`Submission.dtc_hausdorff_dilation`. -/
theorem Submission.cbr_ci_dilation_calculus : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω') ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X') ∧ (∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ)) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W) ∧ (∀ A : Set (Euclid P), μHE[m] (dilation a lam '' A) = ENNReal.ofReal (lam⁻¹ ^ m) * μHE[m] A) := by
  intro P m a lam hlam
  refine ⟨fun X => ?_, Submission.cbr_cidc_dilation_boundary P m a lam hlam,
    Submission.cbr_cidc_dilation_isIntegerMultiplicity P m a lam hlam,
    Submission.cbr_cidc_dilation_integral_rep P m a lam hlam,
    Submission.cbr_cidc_dilation_massOn_image P m a lam hlam,
    (Submission.dtc_hausdorff_dilation P m a lam hlam).1⟩
  -- (1) `η` maps `ℝᴾ` onto `ℝᴾ`, as `η(a + λy) = y`; so `η_{a,λ#}X` restricts to `ℝᴾ`, and the
  -- restriction is a dilation of `X` by part (c) of the test-form correspondence.
  obtain ⟨-, -, hC⟩ := Submission.dtc_blowUp_testForm_corr P m univ a lam hlam
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by
      simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']⟩
  refine ⟨(blowUp X a lam hlam.ne').restrictDomain hsurj, fun ω ω' hωω' => ?_⟩
  rw [GeometricCurrentOn.restrictDomain_apply]
  exact hC X _ ω' (by simpa using hωω')
/-- Restricted representing integrals are determined by the represented current (closure theorem,
Simon Ch. 6, 8.2–8.3, as used for 7.2.4): if `∫ ⟨ω, ξ₁⟩ dμ₁ = ∫ ⟨ω, ξ₂⟩ dμ₂ + ∫ ⟨ω, ξ₃⟩ dμ₃` for
every `ω ∈ 𝒟ᵏ(U)`, the same identity holds for the integrals over every Borel set `B`.  For fixed
`ω` the integrands are integrable (bounded by `|ω|`, which vanishes off the compact `spt ω ⊆ U`).
Testing the hypothesis with `gω`, `g` smooth, and letting `g = (1 - f)ʲ ↓ 𝟙_F` (`f` smooth,
`0 ≤ f ≤ 1`, with support `ℝᴾ \ F`) gives the identity on closed sets `F` by dominated
convergence; Dynkin's π-λ theorem extends it to all Borel sets. -/
theorem Submission.cbr_setIntegral_eq_of_integral_eq : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃ := by
  intro P k U μ₁ μ₂ μ₃ ξ₁ ξ₂ ξ₃ _hU hμ₁ hμ₂ hμ₃ hξ₁ hξ₂ hξ₃ hb₁ hb₂ hb₃ heq B ω hB
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := ω.property.1.1
  have hwc : HasCompactSupport w := ω.property.1.2
  have hwU : tsupport w ⊆ U := ω.property.2
  -- Step 1: `x ↦ ξ x (w x)` is integrable: it vanishes off the compact set `tsupport w ⊆ U` and
  -- is bounded by `sup |w|`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖covectorEuclideanNorm (w x)‖ ≤ C := by
    refine Continuous.bounded_above_of_compact_support ?_
      (hwc.comp_left (g := fun α : Covector (Euclid P) k => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P k))
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    exact Continuous.if_const _ ((hws.continuous.eval_const _).pow 2) continuous_const
  have hint : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k),
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) →
      Integrable (fun x => ξ x (w x)) μ := by
    intro μ ξ hμ hξ hb
    have hsupp : support (fun x => ξ x (w x)) ⊆ tsupport w := by
      intro x hx
      by_contra hxw
      exact hx (by simp [image_eq_zero_of_notMem_tsupport hxw])
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    refine Measure.integrableOn_of_bounded (M := C) (hμ _ hwc hwU).ne
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξ
        hws.continuous.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_of_ae hb] with x hx
    rw [Real.norm_eq_abs]
    exact (hx (w x)).trans ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC x))
  have hi₁ := hint μ₁ ξ₁ hμ₁ hξ₁ hb₁
  have hi₂ := hint μ₂ ξ₂ hμ₂ hξ₂ hb₂
  have hi₃ := hint μ₃ ξ₃ hμ₃ hξ₃ hb₃
  -- Step 2: testing the hypothesis with the test form `g • w`, `g` smooth.
  have hmul : ∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∫ x, g x * ξ₁ x (w x) ∂μ₁ = ∫ x, g x * ξ₂ x (w x) ∂μ₂ + ∫ x, g x * ξ₃ x (w x) ∂μ₃ := by
    intro g hg
    have hmem : (fun x => g x • w x) ∈ testFormOnSubmodule U k :=
      ⟨⟨hg.smul hws, hwc.mono' ((subset_tsupport _).trans (tsupport_smul_subset_right g w))⟩,
        (tsupport_smul_subset_right g w).trans hwU⟩
    simpa only [Submodule.coe_mk, map_smul, smul_eq_mul] using heq ⟨fun x => g x • w x, hmem⟩
  -- Step 3: closed sets, by smooth approximation of the indicator and dominated convergence.
  have hclosed : ∀ F : Set (Euclid P), IsClosed F →
      ∫ x in F, ξ₁ x (w x) ∂μ₁ = ∫ x in F, ξ₂ x (w x) ∂μ₂ + ∫ x in F, ξ₃ x (w x) ∂μ₃ := by
    intro F hF
    obtain ⟨f, hfs, hfd, hfr⟩ := hF.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
    have hgd : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (1 - f x) ^ n) :=
      fun n => (contDiff_const.sub hfd).pow n
    have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x => hfr ⟨x, rfl⟩
    have hgb : ∀ (n : ℕ) x, ‖(1 - f x) ^ n‖ ≤ 1 := by
      intro n x
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hf01 x).2])]
      exact pow_le_one₀ (by linarith [(hf01 x).2]) (by linarith [(hf01 x).1])
    have hlim : ∀ (μ : Measure (Euclid P)) (h : Euclid P → ℝ), Integrable h μ →
        Tendsto (fun n : ℕ => ∫ x, (1 - f x) ^ n * h x ∂μ) atTop (𝓝 (∫ x in F, h x ∂μ)) := by
      intro μ h hh
      rw [← integral_indicator hF.measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun n => ?_) hh.norm
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · exact (hgd n).continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hgb n x)
      · by_cases hx : x ∈ F
        · have hfx : f x = 0 := Function.notMem_support.mp (by rw [hfs]; exact fun h => h hx)
          simp [hfx, hx]
        · have hfx : f x ≠ 0 := Function.mem_support.mp (by rw [hfs]; exact hx)
          have hpos : 0 < f x := lt_of_le_of_ne (hf01 x).1 (Ne.symm hfx)
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - f x)
            (by linarith [(hf01 x).2]) (by linarith)).mul_const (h x)
          simpa [hx] using this
    exact tendsto_nhds_unique (hlim μ₁ _ hi₁)
      (((hlim μ₂ _ hi₂).add (hlim μ₃ _ hi₃)).congr fun n => (hmul _ (hgd n)).symm)
  -- Step 4: Dynkin's π-λ theorem extends the identity from closed sets to all Borel sets.
  have hall : ∀ (t : Set (Euclid P)) (_ : MeasurableSet t),
      ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃ := by
    refine MeasurableSpace.induction_on_inter (s := {s | IsClosed s})
      (C := fun t _ =>
        ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃)
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      (by simp) (fun t ht => hclosed t ht) (fun t htm ht => ?_) (fun f hfd hfm hf => ?_)
    · have e₁ := integral_add_compl htm hi₁
      have e₂ := integral_add_compl htm hi₂
      have e₃ := integral_add_compl htm hi₃
      have e := heq ω
      linarith
    · exact (hasSum_integral_iUnion hfm hfd hi₁.integrableOn).unique
        (((hasSum_integral_iUnion hfm hfd hi₂.integrableOn).add
          (hasSum_integral_iUnion hfm hfd hi₃.integrableOn)).congr_fun fun n => hf n)
  exact hall B hB
/-- **Mass upper bound from a representation by a unit-bounded multivector field** (Simon
6.2.5; step 10 of the representation `T = μ_T ∧ ξ⃗`).  Suppose `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x`
and all covectors `α` (`|·|_E` is `covectorEuclideanNorm`), and `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`
for every test form `ω`.  Then `M_W(T) ≤ μ(W)` for every set `W`.  Fix an admissible `ω`, i.e.
`tsupport ω ⊆ W` and `|ω|_E ≤ 1`, and let `K = tsupport ω` (closed, hence Borel) and
`f(x) = ⟨ω(x), ξ(x)⟩`.  Then `|f| ≤ |ω|_E ≤ 1` on `K` and `f = 0` off `K`, so
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_K dμ = μ(K) ≤ μ(W)`; the middle inequality holds whether
or not `f` is integrable.  Taking the supremum over admissible `ω` gives `M_W(T) ≤ μ(W)`. -/
theorem Submission.cmrc_massOn_le_of_repr : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ W : Set (Euclid P), T.massOn W ≤ μ W := by
  intro P n U T μ ξ hξ hT W
  -- Step 1: it suffices to bound `ofReal (T ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  set K : Set (Euclid P) := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  -- Step 2: `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_K(x)` for every `x`
  have hpt : ∀ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ K.indicator 1 x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
  -- Step 3: `T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ μ(K) ≤ μ(W)`
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
    _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono hpt
    _ = μ K := lintegral_indicator_one hKm
    _ ≤ μ W := measure_mono hω.1
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

/-- **The dilated pair `(λ⁻ᵐ η_#μ, ξ(a + λ·))`** (Simon Ch. 6, 2.23 for the similarity
`η = η_{a,λ}`, `η(y) = λ⁻¹(y − a)`, `λ > 0`; used to rescale cycles with the integer slice
property).  `η` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`, hence a measurable
embedding with `η⁻¹(K)` compact for compact `K`, and `a + λη(x) = x`.  So `μ₂ = λ⁻ᵐ η_#μ` is
finite on compact sets, `ξ₂ = ξ(a + λ·)` is `μ₂`-a.e. strongly measurable with `|⟨α, ξ₂⟩| ≤ |α|`
`μ₂`-a.e., and `∫_S ⟨ω, ξ₂⟩ dμ₂ = λ⁻ᵐ ∫_{η⁻¹(S)} ⟨ω ∘ η, ξ⟩ dμ` for every set `S` and every form
`ω` (change of variables along the measurable embedding `η`). -/
theorem Submission.cbr_ci_dsp_pushforward_pair : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), 0 < lam → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) K < ∞) ∧ AEStronglyMeasurable (fun y => ξ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) ∧ (∀ᵐ y ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ), ∀ α : Covector (Euclid P) m, |ξ (a + lam • y) α| ≤ covectorEuclideanNorm α) ∧ ∀ (S : Set (Euclid P)) (ω : DifferentialForm (Euclid P) m), ∫ y in S, ξ (a + lam • y) (ω y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) = lam⁻¹ ^ m * ∫ x in dilation a lam ⁻¹' S, ξ x (ω (dilation a lam x)) ∂μ := by
  intro P m a lam μ ξ hlam hμ hξm hξ
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{a,λ}` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`.
  set e : Euclid P ≃ₜ Euclid P :=
    (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have he : (e : Euclid P → Euclid P) = dilation a lam := by
    funext y
    simp [e, dilation, dilationCLM]
  have hη : MeasurableEmbedding (dilation a lam) := he ▸ e.measurableEmbedding
  -- Step 2: the inverse identity `a + λη(x) = x`.
  have hinv : ∀ x, a + lam • dilation a lam x = x := fun x => by
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  refine ⟨fun K hK => ?_, ?_, ?_, fun S ω => ?_⟩
  · -- (a)
    rw [Measure.smul_apply, hη.map_apply, smul_eq_mul]
    have hKc : IsCompact (dilation a lam ⁻¹' K) := by
      rw [← he]
      exact e.isCompact_preimage.mpr hK
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμ _ hKc)
  · -- (b)
    refine AEStronglyMeasurable.smul_measure ?_ _
    rw [hη.aestronglyMeasurable_map_iff]
    have hcomp : (fun y => ξ (a + lam • y)) ∘ dilation a lam = ξ := funext fun x => by
      simp [hinv]
    rw [hcomp]
    exact hξm
  · -- (c)
    refine Measure.ae_smul_measure ?_ _
    rw [hη.ae_map_iff]
    filter_upwards [hξ] with x hx
    simpa [hinv] using hx
  · -- (d)
    rw [Measure.restrict_smul, integral_smul_measure, hη.setIntegral_map,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp only [hinv]
/-- **Composition with a dilation preserves test forms on `ℝᴾ`** (Simon Ch. 3, 1.4,
chapter-03.txt line 85; `η^#ω` in 6.2.23, chapter-06.txt lines 403–413; used for the dilations
`η_{a,λ#}` in the proof of 7.3.1, chapter-07.txt lines 329–337).  For `λ > 0` and
`η = η_{a,λ}`, `η(y) = −λ⁻¹a + λ⁻¹y`, every `φ ∈ 𝒟ᵐ(ℝᴾ)` gives `φ' = φ ∘ η ∈ 𝒟ᵐ(ℝᴾ)`:
`φ ∘ η` is `C^∞` because `η` is a constant plus the linear map `dilationCLM P λ`; it has compact
support because `η` is a homeomorphism (`y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`), so
`tsupport (φ ∘ η) = η⁻¹(tsupport φ)` is compact; and `tsupport (φ ∘ η) ⊆ ℝᴾ` is trivial. -/
theorem Submission.cbr_ci_dsp_testForm_comp_dilation : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ φ : TestFormOn (univ : Set (Euclid P)) m, ∃ φ' : TestFormOn (univ : Set (Euclid P)) m, ∀ y : Euclid P, (φ' : DifferentialForm (Euclid P) m) y = (φ : DifferentialForm (Euclid P) m) (dilation a lam y) := by
  intro P m a lam hlam φ
  -- Step 2: `η = η_{a,λ}` is the homeomorphism `y ↦ λ⁻¹y` followed by `z ↦ −λ⁻¹a + z`.
  let e : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have he : ⇑e = dilation a lam := by
    funext y
    simp [e, dilation, dilationCLM]
  obtain ⟨⟨hsmooth, hcompact⟩, -⟩ := φ.property
  -- Step 4: `φ' := φ ∘ η`, with `φ'(y) = φ(η(y))` by definition.
  refine ⟨⟨fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y), ?_⟩, fun y => rfl⟩
  change IsTestForm (fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y)) ∧
    tsupport (fun y => (φ : DifferentialForm (Euclid P) m) (dilation a lam y)) ⊆ univ
  -- Step 1: `η = (−λ⁻¹a) + dilationCLM P λ` is `C^∞`, so `φ ∘ η` is `C^∞`; Step 3: `⊆ univ`.
  refine ⟨⟨hsmooth.comp (contDiff_const.add (dilationCLM P lam).contDiff), ?_⟩, subset_univ _⟩
  -- Step 2: `φ ∘ e` has compact support, and `e = η`.
  have h := hcompact.comp_homeomorph e
  rwa [he] at h

/-- **Integer multiplicity slice boundaries of a cycle** (the slicing step of Simon 7.2.4, via
Ch. 6, 4.6–4.10 and the integer slice property).  Let `X ∈ 𝒟_{d+1}(ℝᴾ)`, `∂X = 0`, be represented by
`(μX, ξX)` and have the integer slice property.  As `∂X = 0`, the zero measure with the zero field
represents `∂X` admissibly.  (SL) for `X`, `(μX, ξX)`, `(0, 0)` and an `L`-Lipschitz `g` gives
`A_t = X ⌞ {g < t}` and `B_t = (∂X) ⌞ {g < t}`, and `B_t = 0` since it integrates against the zero
measure.  The integer slice property with the same data makes `∂A_t − B_t = ∂A_t` integer
multiplicity for `L¹`-a.e. `t`. -/
theorem Submission.cbr_ci_dsp_cycle_slice_boundary_im : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μX : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)), X.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) (d + 1), |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ (g : Euclid P → ℝ) (L : NNReal), LipschitzWith L g → ∀ᵐ t ∂(volume : Measure ℝ), ∃ A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | g x < t}, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) ∧ IsIntegerMultiplicity A.boundary := by
  intro hSL P d X μX ξX hX hμX hξXm hξX hXrep hISP g L hg
  -- Step 1: the zero measure with the zero field represents `∂X = 0` admissibly.
  have h0K : ∀ K : Set (Euclid P), IsCompact K → (0 : Measure (Euclid P)) K < ∞ :=
    fun K _ => by simp
  have h0m : AEStronglyMeasurable (fun _ : Euclid P => (0 : MultiVector P d))
      (0 : Measure (Euclid P)) :=
    aestronglyMeasurable_zero_measure _
  have h0b : ∀ᵐ x ∂(0 : Measure (Euclid P)), ∀ α : Covector (Euclid P) d,
      |(fun _ : Euclid P => (0 : MultiVector P d)) x α| ≤ covectorEuclideanNorm α := by
    simp
  have h0rep : ∀ η : TestFormOn (univ : Set (Euclid P)) d, X.boundary η =
      ∫ x, (fun _ : Euclid P => (0 : MultiVector P d)) x ((η : DifferentialForm (Euclid P) d) x)
        ∂(0 : Measure (Euclid P)) := by
    intro η
    rw [hX]
    simp
  -- Step 2: (SL) gives `A t = X ⌞ {g < t}` and `B t = (∂X) ⌞ {g < t}` through `(0, 0)`.
  obtain ⟨A, B, hA, hB, -⟩ := hSL P d univ X μX 0 ξX (fun _ => 0) g L isOpen_univ
    (fun K hK _ => hμX K hK) (fun K hK _ => h0K K hK) hξXm h0m hξX h0b hXrep h0rep hg
  -- Step 4: the integer slice property of `X` with the same data, for a.e. `t`.
  filter_upwards [hISP μX 0 ξX (fun _ => 0) hμX h0K hξXm h0m hξX h0b hXrep h0rep g L hg]
    with t ht
  refine ⟨A t, hA t, ?_⟩
  -- Steps 3 and 6: `B t = 0`, so `∂A t − B t = ∂A t`.
  have hsub : (A t).boundary - B t = (A t).boundary := by
    ext η
    change (A t).boundary η - B t η = (A t).boundary η
    rw [hB t η]
    simp
  -- Step 5: `∂A t − B t` is integer multiplicity.
  have h := ht (A t) (B t) (hA t) (hB t)
  rwa [hsub] at h

/-- Dilation invariance of the integer slice property (ISP), step 2 of the proof that a cycle with
the ISP is integer multiplicity.  Let `η = dilation a lam` and let `X'` be the dilation of the cycle
`X` with admissible representation `(μ_X, ξ_X)`.  Then `∂X' = 0` and `(λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))`
is an admissible representation of `X'`.  Fix admissible representations `(μ, ξ)` of `X'`,
`(μ', ξ')` of `∂X'` and an `L`-Lipschitz `f`.  By (SL) and the ISP of `X`, the slice `A_X(t)` of `X`
by `{f ∘ η < t}` has integer multiplicity boundary for a.e. `t`.  For such `t`, (RU) and the change
of variables `η` show that every slice `A` of `X'` by `{f < t}` is the dilation of `A_X(t)`, and
(RU) with `∂X' = 0` shows that the boundary slice `B` vanishes.  Hence `∂A − B = ∂A` is the dilation
of `∂A_X(t)`, which is integer multiplicity. -/
theorem Submission.cbr_ci_dilation_slice_property : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (P d : ℕ) (a : Euclid P) (lam : ℝ) (X X' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μX : Measure (Euclid P)) (ξX : Euclid P → MultiVector P (d + 1)), 0 < lam → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y = (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (d + 1) * X ω') → X.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) (d + 1), |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μX) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X' ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X').boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) := by
  have hpush := Submission.cbr_ci_dsp_pushforward_pair
  have hcomp := Submission.cbr_ci_dsp_testForm_comp_dilation
  have hcyc := Submission.cbr_ci_dsp_cycle_slice_boundary_im
  have hdc := Submission.cbr_ci_dilation_calculus
  intro SL RU P d a lam X X' μX ξX hlam hdil hXbd hμXK hξXm hξXb hXrep hISP
    μ μ' ξ ξ' hμK hμ'K hξm hξ'm hξb hξ'b hrep hbrep f L hf
  -- Step 1: `(λ⁻ⁿ η_# μ_X, ξ_X(a + λ ·))` is an admissible representation of `X'`
  obtain ⟨hμ₂K, hξ₂m, hξ₂b, hchg⟩ := hpush P (d + 1) a lam μX ξX hlam hμXK hξXm hξXb
  obtain ⟨-, hbd, him, -, -, -⟩ := hdc P d a lam hlam
  obtain ⟨-, -, -, hrepd, -, -⟩ := hdc P (d + 1) a lam hlam
  -- Step 2: `∂X' = 0`, testing `∂X` against `φ ∘ η`
  have hX'bd : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, X'.boundary φ = 0 := by
    intro φ
    obtain ⟨φ', hφ'⟩ := hcomp P d a lam hlam φ
    rw [hbd X X' hdil φ φ' hφ', hXbd, GeometricCurrentOn.zero_apply, mul_zero]
  -- Step 3: the slices `A_X(t)` of `X` by `{f ∘ η < t}` have integer multiplicity boundary
  -- for a.e. `t`
  have hηL : LipschitzWith ‖lam⁻¹‖₊ (dilation a lam) := by
    refine LipschitzWith.of_dist_le_mul fun x y => le_of_eq ?_
    simp [dilation, dilationCLM, dist_smul₀]
  filter_upwards [hcyc SL P d X μX ξX hXbd hμXK hξXm hξXb hXrep hISP (f ∘ dilation a lam)
    (L * ‖lam⁻¹‖₊) (hf.comp hηL)] with t ht
  obtain ⟨AX, hAX, hAXim⟩ := ht
  intro A B hA hB
  have hft : MeasurableSet {x | f x < t} :=
    measurableSet_lt hf.continuous.measurable measurable_const
  -- Step 4: by (RU), `A` is also the slice of the representation of Step 1
  have hRU1 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ =
        ∫ y in {x | f x < t}, ξX (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y)
          ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) := by
    intro ω
    have h := RU P (d + 1) univ μ
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μX) 0 ξ
      (fun y => ξX (a + lam • y)) (fun _ => 0) isOpen_univ (fun K hK _ => hμK K hK)
      (fun K hK _ => hμ₂K K hK) (fun K _ _ => by simp) hξm hξ₂m aestronglyMeasurable_const
      hξb hξ₂b (by simp)
      (fun ω => by rw [← hrep ω, hrepd X X' μX ξX hdil hXrep ω, integral_zero_measure, add_zero])
      {x | f x < t} ω hft
    simpa only [Measure.restrict_zero, integral_zero_measure, add_zero] using h
  -- Step 5: change of variables by `η`: `A` is the dilation of `A_X(t)`
  have hAdil : ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (d + 1),
      (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (d + 1)) y =
        (ω : DifferentialForm (Euclid P) (d + 1)) (dilation a lam y)) →
      A ω = lam⁻¹ ^ (d + 1) * AX ω' := by
    intro ω ω' hω'
    rw [hA ω, hRU1 ω, hchg {x | f x < t} (ω : DifferentialForm (Euclid P) (d + 1)), hAX ω']
    simp only [hω']
    rfl
  -- Step 6: by (RU) and `∂X' = 0`, the boundary slice `B` vanishes
  have hB0 : ∀ φ : TestFormOn (univ : Set (Euclid P)) d, B φ = 0 := by
    intro φ
    have h := RU P d univ μ' 0 0 ξ' (fun _ => 0) (fun _ => 0) isOpen_univ
      (fun K hK _ => hμ'K K hK) (fun K _ _ => by simp) (fun K _ _ => by simp) hξ'm
      aestronglyMeasurable_const aestronglyMeasurable_const hξ'b (by simp) (by simp)
      (fun φ => by rw [← hbrep φ, hX'bd φ, integral_zero_measure, add_zero])
      {x | f x < t} φ hft
    rw [hB φ, h, Measure.restrict_zero, integral_zero_measure, add_zero]
  -- Step 7: `∂A − B = ∂A` is the dilation of the integer multiplicity `∂A_X(t)`
  have hsub : A.boundary - B = A.boundary := by
    refine GeometricCurrentOn.ext fun φ => ?_
    show A.boundary φ - B φ = A.boundary φ
    rw [hB0 φ, sub_zero]
  rw [hsub]
  exact him AX.boundary A.boundary (hbd AX A hAdil) hAXim
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Radial retraction onto the unit ball of `N = covectorEuclideanNorm`** (step 4 of the
approximation of a unit covector field by admissible test forms, used for Simon Ch. 6,
Remark 3.2(3)).  `ρ(a) = max(1, N(a))⁻¹ a` is continuous, `ρ(0) = 0`, `N(ρ(a)) ≤ 1`, and
`N(ρ(a) − b) ≤ 2 N(a − b)` whenever `N(b) ≤ 1`: if `N(a) > 1` then
`N(a − ρ(a)) = N(a) − 1 ≤ N(a − b)`, and the triangle inequality gives the factor `2`. -/
theorem Submission.rsd_mw_tfa_retraction : ∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b) := by
  intro P n
  obtain ⟨htri, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- the rescaling factor `max 1 (N a) ≥ 1` never vanishes
  have hpos : ∀ a : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm a) :=
    fun a => one_pos.trans_le (le_max_left _ _)
  refine ⟨fun a => (max 1 (covectorEuclideanNorm a))⁻¹ • a,
    ((continuous_const.max hcont).inv₀ fun a => (hpos a).ne').smul continuous_id, by simp,
    fun a => ?_, fun a b hb => ?_⟩
  · -- `N (ρ a) = N a / max 1 (N a) ≤ 1`
    dsimp only
    rw [hsmul, abs_of_pos (inv_pos.mpr (hpos a)), inv_mul_le_iff₀ (hpos a), mul_one]
    exact le_max_right _ _
  dsimp only
  rcases le_or_gt (covectorEuclideanNorm a) 1 with ha | ha
  · -- `N a ≤ 1`: `ρ a = a`
    rw [max_eq_left ha, inv_one, one_smul]
    linarith [covectorEuclideanNorm_nonneg (a - b)]
  -- `r := N a > 1`: `ρ a = r⁻¹ a`
  set r := covectorEuclideanNorm a with hr
  rw [max_eq_right ha.le]
  -- `N (a - ρ a) = (1 - r⁻¹) r = r - 1`
  have h₁ : covectorEuclideanNorm (a - r⁻¹ • a) = r - 1 := by
    rw [show a - r⁻¹ • a = (1 - r⁻¹) • a by module, hsmul,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ ha.le)), sub_mul, one_mul, ← hr,
      inv_mul_cancel₀ (one_pos.trans ha).ne']
  -- `r ≤ N (a - b) + N b ≤ N (a - b) + 1`
  have h₂ : r ≤ covectorEuclideanNorm (a - b) + 1 :=
    calc r = covectorEuclideanNorm (a - b + b) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (a - b) + covectorEuclideanNorm b := htri _ _
      _ ≤ covectorEuclideanNorm (a - b) + 1 := by linarith
  calc covectorEuclideanNorm (r⁻¹ • a - b)
      = covectorEuclideanNorm (-(a - r⁻¹ • a) + (a - b)) := by congr 1; abel
    _ ≤ covectorEuclideanNorm (-(a - r⁻¹ • a)) + covectorEuclideanNorm (a - b) := htri _ _
    _ = r - 1 + covectorEuclideanNorm (a - b) := by rw [covectorEuclideanNorm_neg, h₁]
    _ ≤ 2 * covectorEuclideanNorm (a - b) := by linarith

/-- **`L¹(ν)` approximation of a unit covector field by continuous compactly supported unit
fields** (steps 3–4 of the `L¹(ν)` approximation of a unit covector field by admissible test
forms).  Let `ν` be a finite Borel measure on `ℝᴾ` and `β` a `ν`-integrable `n`-covector field
with `N(β) ≤ 1` `ν`-a.e., `N = covectorEuclideanNorm`.  Continuous compactly supported maps are
dense in `L¹(ν)` (`ν` is regular), so one of them, `g₀`, has `∫ ‖β − g₀‖ dν ≤ η`.  With `ρ` the
retraction onto `{N ≤ 1}`, `g = ρ ∘ g₀` is continuous, compactly supported (`ρ 0 = 0`), has
`N(g) ≤ 1`, and `N(g − β) ≤ 2 N(g₀ − β) ≤ 2C ‖β − g₀‖` a.e., so `∫ N(g − β) dν ≤ 2Cη < δ`. -/
theorem Submission.rsd_mw_tfa_continuous_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g x - β x)) ∂ν < ENNReal.ofReal δ := by
  intro P n ν β hν hβ hβ1 δ hδ
  -- Step 1: the constant `C` of `norm_props` (iii), the retraction `ρ`, and the tolerance `η`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨ρ, hρc, hρ0, hρ1, hρ2⟩ := Submission.rsd_mw_tfa_retraction P n
  set η : ℝ := δ / (2 * (2 * C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: continuous compactly supported maps are dense in `L¹(ν)` (`ν` is finite, hence
  -- regular).  The contract does not import `Integrable.exists_hasCompactSupport_lintegral_sub_le`,
  -- so this goes through `MemLp.induction_dense`: `c • 1_s` is approximated by `φ • c`, with `φ`
  -- a Urysohn function for compact `K ⊆ s ⊆ U` open, `ν (U \ K)` small.
  have hind : ∀ (c : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : Euclid P → Covector (Euclid P) n,
        eLpNorm (g - s.indicator fun _ => c) 1 ν ≤ ε ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro c s hs hsν ε hε
    obtain ⟨t, ht0, htε⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hε
    have ht : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht0.ne'
    -- compact `K ⊆ s ⊆ U` open with `ν (s \ K) < t` and `ν (U \ s) < t`
    obtain ⟨K, hKs, hK, hsK⟩ := hs.exists_isCompact_sdiff_lt hsν.ne ht
    obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hsν.ne ht
    -- Urysohn: `φ = 1` on `K`, `φ = 0` off `U`, `0 ≤ φ ≤ 1`, compact support
    obtain ⟨φ, hφK, hφU, hφs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hgc : Continuous fun x => φ x • c := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • c, ?_, hgc, hφs.smul_right⟩
    -- pointwise `‖φ x • c - 1_s(x) c‖ₑ ≤ 1_{U \ K}(x) ‖c‖ₑ`
    have hle : ∀ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ≤
        (U \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      rw [← ofReal_norm]
      by_cases hxK : x ∈ K
      · simp [hφK hxK, hKs hxK]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxK), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [Pi.sub_apply, indicator_of_mem hxs, show φ x • c - c = (φ x - 1) • c by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          nlinarith [norm_nonneg c]
        · rw [Pi.sub_apply, indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg h0]
          nlinarith [norm_nonneg c]
      · simp [hφU hxU, show x ∉ s from fun h => hxU (hsU h), hxU]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (stronglyMeasurable_const.indicator hs).aestronglyMeasurable)]
    calc ∫⁻ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ∂ν
        ≤ ∫⁻ x, (U \ K).indicator (fun _ => ‖c‖ₑ) x ∂ν := lintegral_mono hle
      _ = ‖c‖ₑ * ν (U \ K) := lintegral_indicator_const (hU.measurableSet.diff hK.measurableSet) _
      _ ≤ ‖c‖ₑ * (ν (U \ s) + ν (s \ K)) := by
          gcongr
          refine (measure_mono fun x hx => ?_).trans (measure_union_le (U \ s) (s \ K))
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩
      _ ≤ ‖c‖ₑ * (t + t) := by gcongr
      _ = t * (2 * ‖c‖ₑ) := by ring
      _ ≤ ε := htε.le
  -- the density statement for `β`, with tolerance `η`
  obtain ⟨g₀, hg₀, hg₀c, hg₀s⟩ := (memLp_one_iff_integrable.2 hβ).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.mpr hη0).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hβ.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)] at hg₀
  -- Step 3: `g := ρ ∘ g₀`
  refine ⟨ρ ∘ g₀, hρc.comp hg₀c, hg₀s.comp_left hρ0, fun x => hρ1 _, ?_⟩
  -- Step 4: pointwise a.e. estimate
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x))
      ≤ ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ := by
    filter_upwards [hβ1] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc covectorEuclideanNorm ((ρ ∘ g₀) x - β x)
        ≤ 2 * covectorEuclideanNorm (g₀ x - β x) := hρ2 _ _ hx
      _ ≤ 2 * (C * ‖g₀ x - β x‖) := by gcongr; exact hC _
      _ = 2 * C * ‖β x - g₀ x‖ := by rw [norm_sub_rev]; ring
  -- Step 5: integration
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * C) * ∫⁻ x, ‖β x - g₀ x‖ₑ ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * C) * ENNReal.ofReal η := by gcongr; exact hg₀
    _ = ENNReal.ofReal (2 * C * η) := (ENNReal.ofReal_mul (by positivity)).symm
    -- Step 6: arithmetic
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ, hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smooth uniform approximation keeping the unit bound** (smoothing step in the proof of
`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is `covectorEuclideanNorm`).  Let
`η := δ/(2C + 1)`, where `|·|_E ≤ C‖·‖` (`Submission.rsd_mw_tfa_norm_props`).  A continuous
compactly supported covector field `g` with `|g|_E ≤ 1` is uniformly continuous, so
`‖g y − g x‖ < η` when `dist y x < r`.  Mollifying, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth
bump `φ ≥ 0` with `support φ = B_r(0)` is a `C^∞` field with `‖h' − g‖ ≤ η`; then
`|h' − g|_E ≤ Cη` and `|h'|_E ≤ 1 + Cη`.  The rescaled field `h = (1 + Cη)⁻¹h'` has `|h|_E ≤ 1`
and `|h − h'|_E = Cη(1 + Cη)⁻¹|h'|_E ≤ Cη`, hence `|h − g|_E ≤ 2Cη ≤ δ`. -/
theorem Submission.rsd_mw_tfa_smooth_uniform_approx : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n), Continuous g → HasCompactSupport g → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ h : Euclid P → Covector (Euclid P) n, ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ x, covectorEuclideanNorm (h x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (h x - g x) ≤ δ := by
  intro P n g hgc hgs hg1 δ hδ
  -- `N := covectorEuclideanNorm` is subadditive, absolutely homogeneous and `N ≤ C ‖·‖`
  obtain ⟨htri, hsmul, ⟨C, hC0, hCle⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: the tolerance `η = δ / (2C + 1)`
  set η : ℝ := δ / (2 * C + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hCη : 0 ≤ C * η := mul_nonneg hC0 hη0.le
  -- Step 2: `g` is uniformly continuous: `‖g y - g x‖ < η` whenever `dist y x < r`
  obtain ⟨r, hr, hgr⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη0
  -- Step 3: mollify, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ`, `support φ = B_r(0)`
  let φ : ContDiffBump (0 : Euclid P) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hr
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 r := hψφ.trans φ.support_eq.subset
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  obtain ⟨h', hh's, hh'g⟩ : ∃ h' : Euclid P → Covector (Euclid P) n,
      ContDiff ℝ (⊤ : ℕ∞) h' ∧ ∀ x, dist (h' x) (g x) ≤ η :=
    ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      (φ.hasCompactSupport.mono hψφ).contDiff_convolution_left _ (φ.contDiff.div_const _)
        hgc.locallyIntegrable,
      fun x => dist_convolution_le hη0.le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgr (mem_ball.mp hy)).le⟩
  -- Step 4: `N(h' - g) ≤ Cη` and `N(h') ≤ 1 + Cη`
  have hdiff : ∀ x, covectorEuclideanNorm (h' x - g x) ≤ C * η := fun x =>
    (hCle _).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hh'g x) hC0)
  have hh'1 : ∀ x, covectorEuclideanNorm (h' x) ≤ 1 + C * η := fun x =>
    calc covectorEuclideanNorm (h' x) = covectorEuclideanNorm ((h' x - g x) + g x) := by
          rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (h' x - g x) + covectorEuclideanNorm (g x) := htri _ _
      _ ≤ C * η + 1 := add_le_add (hdiff x) (hg1 x)
      _ = 1 + C * η := add_comm _ _
  -- Step 5: rescale by `s = (1 + Cη)⁻¹ ∈ (0, 1]`
  have hpos : 0 < 1 + C * η := by linarith
  have hne : 1 + C * η ≠ 0 := hpos.ne'
  set s : ℝ := (1 + C * η)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hpos
  refine ⟨fun x => s • h' x, hh's.const_smul s, fun x => ?_, fun x => ?_⟩
  · show covectorEuclideanNorm (s • h' x) ≤ 1
    rw [hsmul, abs_of_pos hs0, hs, inv_mul_le_iff₀ hpos, mul_one]
    exact hh'1 x
  · show covectorEuclideanNorm (s • h' x - g x) ≤ δ
    -- Step 6: `N(s h' - h') = |s - 1| N(h') = Cη s N(h') ≤ Cη`
    have hsh : s • h' x - h' x = (s - 1) • h' x := by module
    have hs1 : |s - 1| = C * η * s := by
      have hle : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      rw [abs_of_nonpos (by linarith), hs]
      field_simp
      ring
    have h6 : covectorEuclideanNorm (s • h' x - h' x) ≤ C * η := by
      rw [hsh, hsmul, hs1]
      calc C * η * s * covectorEuclideanNorm (h' x) ≤ C * η * s * (1 + C * η) :=
            mul_le_mul_of_nonneg_left (hh'1 x) (mul_nonneg hCη hs0.le)
        _ = C * η := by rw [hs]; field_simp
    -- Step 7: `N(s h' - g) ≤ N(s h' - h') + N(h' - g) ≤ 2Cη ≤ δ`
    calc covectorEuclideanNorm (s • h' x - g x)
        = covectorEuclideanNorm ((s • h' x - h' x) + (h' x - g x)) := by
          rw [sub_add_sub_cancel]
      _ ≤ covectorEuclideanNorm (s • h' x - h' x) + covectorEuclideanNorm (h' x - g x) :=
          htri _ _
      _ ≤ C * η + C * η := add_le_add h6 (hdiff x)
      _ ≤ δ := by
          have h2 : 0 < 2 * C + 1 := by linarith
          have h2C : C * η + C * η = 2 * C * δ / (2 * C + 1) := by rw [hη]; ring
          rw [h2C, div_le_iff₀ h2]
          nlinarith

/-- **Test forms approximating a unit-bounded integrable covector field in `L¹(ν)`** (the
approximation behind `M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is
`covectorEuclideanNorm`).  Let `m = ν(ℝᴾ)` and `δ = ε/(4(m + 1))`.  The smooth cut-off `χ` of
`Submission.rsd_mw_tfa_smooth_cutoff` satisfies `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`.  The
continuous field `g₁` of `Submission.rsd_mw_tfa_continuous_approx` satisfies `|g₁|_E ≤ 1` and
`∫ |g₁ − β|_E dν < ε/4`.  Its smoothing `g₂` (`Submission.rsd_mw_tfa_smooth_uniform_approx`)
satisfies `|g₂|_E ≤ 1` and `|g₂ − g₁|_E ≤ δ`.  Then `ω = χ g₂` is a test form, `tsupport ω ⊆ V`
and `|ω|_E ≤ 1`.  For a.e. `x`, `|ω − β|_E ≤ δ + |g₁ − β|_E` where `χ = 1`, and
`|ω − β|_E ≤ 2` where `χ ≠ 1`.  Integrating,
`∫ |ω − β|_E dν ≤ δm + ∫ |g₁ − β|_E dν + 2ν{χ ≠ 1} < ε/4 + ε/4 + ε/4 < ε`. -/
theorem Submission.rsd_mw_exists_testForm_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ ε : ℝ, 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν V β hν hV hVc hβ hβ1 ε hε
  -- `N := covectorEuclideanNorm` is subadditive and absolutely homogeneous
  obtain ⟨htri, hsmul, -, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: a smooth cut-off `χ` with `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`
  obtain ⟨χ, hχs, hχc, hχV, hχ01, hχν⟩ :=
    Submission.rsd_mw_tfa_smooth_cutoff P ν V hν hV hVc (ε / 8) (by positivity)
  -- Step 2: a continuous compactly supported `g₁` with `N(g₁) ≤ 1` and `∫ N(g₁ - β) dν < ε/4`
  obtain ⟨g₁, hg₁c, hg₁s, hg₁1, hg₁β⟩ :=
    Submission.rsd_mw_tfa_continuous_approx P n ν β hν hβ hβ1 (ε / 4) (by positivity)
  -- Step 3: a smooth `g₂` with `N(g₂) ≤ 1` and `N(g₂ - g₁) ≤ δ = ε/(4(m + 1))`, `m = ν(ℝᴾ)`
  set m : ℝ := (ν univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (4 * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g₂, hg₂s, hg₂1, hg₂g₁⟩ :=
    Submission.rsd_mw_tfa_smooth_uniform_approx P n g₁ hg₁c hg₁s hg₁1 δ hδ0
  -- Step 4: `ω = χ g₂` is a test form with `tsupport ω ⊆ V` and `N(ω) ≤ 1`
  have hω1 : ∀ x, covectorEuclideanNorm (χ x • g₂ x) ≤ 1 := fun x => by
    rw [hsmul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hg₂1 x)
  refine ⟨fun x => χ x • g₂ x, ⟨hχs.smul hg₂s, hχc.smul_right⟩,
    (tsupport_smul_subset_left χ g₂).trans hχV, hω1, ?_⟩
  -- Step 5: a.e., `N(ω - β) ≤ δ + N(g₁ - β)` where `χ = 1` and `N(ω - β) ≤ 2` on `S = {χ ≠ 1}`
  set S : Set (Euclid P) := {x | χ x ≠ 1}
  have hSm : MeasurableSet S := (isOpen_ne_fun hχs.continuous continuous_const).measurableSet
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ≤
      ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
        S.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    filter_upwards [hβ1] with x hx
    by_cases h1 : χ x = 1
    · rw [indicator_of_notMem (not_not.mpr h1), add_zero,
        ← ENNReal.ofReal_add hδ0.le (covectorEuclideanNorm_nonneg _), h1, one_smul]
      refine ENNReal.ofReal_le_ofReal ?_
      calc covectorEuclideanNorm (g₂ x - β x)
          = covectorEuclideanNorm ((g₂ x - g₁ x) + (g₁ x - β x)) := by rw [sub_add_sub_cancel]
        _ ≤ covectorEuclideanNorm (g₂ x - g₁ x) + covectorEuclideanNorm (g₁ x - β x) :=
          htri _ _
        _ ≤ δ + covectorEuclideanNorm (g₁ x - β x) := by linarith [hg₂g₁ x]
    · rw [indicator_of_mem h1]
      refine le_add_left (le_of_le_of_eq (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_ofNat 2))
      calc covectorEuclideanNorm (χ x • g₂ x - β x)
          = covectorEuclideanNorm (χ x • g₂ x + -β x) := by rw [sub_eq_add_neg]
        _ ≤ covectorEuclideanNorm (χ x • g₂ x) + covectorEuclideanNorm (-β x) := htri _ _
        _ ≤ 2 := by rw [covectorEuclideanNorm_neg]; linarith [hω1 x]
  -- Step 6: integrate, `∫ N(ω - β) dν ≤ δm + ∫ N(g₁ - β) dν + 2ν(S) < 3ε/4`
  have hδm : ENNReal.ofReal δ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← hm, ← ENNReal.ofReal_mul hδ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc δ * m ≤ δ * (m + 1) := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hS2 : 2 * ν S < ENNReal.ofReal (ε / 4) := by
    calc 2 * ν S = ν S + ν S := two_mul _
      _ < ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := ENNReal.add_lt_add hχν hχν
      _ = ENNReal.ofReal (ε / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
          S.indicator (fun _ => (2 : ℝ≥0∞)) x) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal δ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) ∂ν + 2 * ν S := by
        rw [lintegral_add_right _ (measurable_const.indicator hSm),
          lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hSm]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_le_of_lt
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hδm hg₁β) hS2
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **A norming field bounds `μ(W')` by the mass `M_W(T)`** (the inequality `μ_T(W') ≤ M_W(T)`
behind Simon 6.2.8, `μ_T(W) = M_W(T)`, for the representation 6.2.7 `T(ω) = ∫ ⟨ω, ξ⟩ dμ`;
`|·|_E` is `covectorEuclideanNorm`).  Let `W' ⊂⊂ U` be open with `W' ⊆ W`.  Then `ν = μ⌞W'` is
finite, as `closure W'` is a compact subset of `U`, and the bounded field `β` is `ν`-integrable.
For `ε > 0`, `Submission.rsd_mw_exists_testForm_approx` gives a test form `ω` with
`tsupport ω ⊆ W'`, `|ω|_E ≤ 1` and `∫ |ω − β|_E dν < ε`, so `ω` is admissible for `M_W(T)`.
The function `f = ξ(ω)` vanishes off `W'`, so `T(ω) = ∫ f dν`; and `ν`-a.e.
`1 − f = ξ(β − ω) ≤ |ω − β|_E`, since `ξ(β) = 1` and `|ξ(α)| ≤ |α|_E`.  Hence
`μ(W') − T(ω) = ∫ (1 − f) dν < ε`, and `μ(W') ≤ M_W(T) + ε` for every `ε > 0`. -/
theorem Submission.cmrc_measure_le_massOn_of_norming : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → AEStronglyMeasurable β μ → (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) → (∀ x, covectorEuclideanNorm (β x) ≤ 1) → (∀ᵐ x ∂μ, ξ x (β x) = 1) → ∀ W W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ T.massOn W := by
  intro P n U T μ ξ β hμK hξm hξ1 hT hβm hβC hβ1 hξβ W W' hW' hW'U hW'W
  -- `N := covectorEuclideanNorm`, `ν := μ⌞W'`
  -- Step 1: `ν` is finite (`closure W'` is a compact subset of `U`) and `ν(W'ᶜ) = 0`
  have hμW' : μ W' < ∞ := (measure_mono subset_closure).trans_lt (hμK _ hW'U.1 hW'U.2)
  have : IsFiniteMeasure (μ.restrict W') := isFiniteMeasure_restrict.2 hμW'.ne
  have hνc : μ.restrict W' W'ᶜ = 0 := by
    rw [Measure.restrict_apply hW'.measurableSet.compl, compl_inter_self, measure_empty]
  -- Step 2: `β` is bounded, hence `ν`-integrable
  obtain ⟨C, hC⟩ := hβC
  have hβi : Integrable β (μ.restrict W') :=
    Integrable.of_bound hβm.restrict C (Eventually.of_forall hC)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- Step 3: a test form `ω₀` with `tsupport ω₀ ⊆ W'`, `N(ω₀) ≤ 1` and `∫ N(ω₀ - β) dν < ε`
  obtain ⟨ω₀, hω₀, hω₀W', hω₀1, hω₀β⟩ := Submission.rsd_mw_exists_testForm_approx P n
    (μ.restrict W') W' β inferInstance hW' hνc hβi (Eventually.of_forall hβ1) ε
    (NNReal.coe_pos.2 hε)
  -- Step 4: `ω₀ ∈ 𝒟ⁿ(U)` is admissible for `M_W(T)`, so `T(ω₀) ≤ M_W(T)`
  let ω : TestFormOn U n := ⟨ω₀, hω₀, hω₀W'.trans (subset_closure.trans hW'U.2)⟩
  have hTω : ENNReal.ofReal (T ω) ≤ T.massOn W := T.le_massOn ⟨hω₀W'.trans hW'W, hω₀1⟩
  -- Step 5: `f = ξ(ω₀)` vanishes off `W'`, so `T(ω₀) = ∫ f dν`
  set f : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hf
  have hTf : T ω = ∫ x, f x ∂(μ.restrict W') := by
    rw [hT ω, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    simp [hf, image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W' h)]
  -- Step 6: `|f| ≤ N(ω₀) ≤ 1`, so `f` is `ν`-integrable
  have hf1 : ∀ x, |f x| ≤ 1 := fun x => (hξ1 x (ω₀ x)).trans (hω₀1 x)
  have hfm : AEStronglyMeasurable f μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξm.prodMk hω₀.1.continuous.aestronglyMeasurable)
  have hfi : Integrable f (μ.restrict W') :=
    Integrable.of_bound hfm.restrict 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf1 x)
  -- Step 7: `ν`-a.e., `1 - f = ξ(β - ω₀) ≤ N(ω₀ - β)`, since `ξ(β) = 1` and `|ξ(α)| ≤ N(α)`
  have hle : ∀ᵐ x ∂(μ.restrict W'), 1 - f x ≤ covectorEuclideanNorm (ω₀ x - β x) := by
    filter_upwards [ae_restrict_of_ae hξβ] with x hx
    have h := abs_le.1 (hξ1 x (ω₀ x - β x))
    rw [map_sub, hx] at h
    linarith [h.1]
  -- Step 8: `μ(W') - T(ω₀) = ∫ (1 - f) dν ≤ ∫ N(ω₀ - β) dν < ε`
  have hint : ENNReal.ofReal (μ.real W' - T ω) < ENNReal.ofReal ε := by
    have h1 : ∫ x, (1 - f x) ∂(μ.restrict W') = μ.real W' - T ω := by
      rw [integral_sub (integrable_const 1) hfi, integral_const, hTf, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ]
    have hgi : Integrable (fun x => 1 - f x) (μ.restrict W') := (integrable_const 1).sub hfi
    rw [← h1, ofReal_integral_eq_lintegral_ofReal hgi
      (Eventually.of_forall fun x => sub_nonneg.2 (le_of_abs_le (hf1 x)))]
    exact (lintegral_mono_ae (hle.mono fun x hx => ENNReal.ofReal_le_ofReal hx)).trans_lt hω₀β
  -- Step 9: `μ(W') ≤ T(ω₀) + ε ≤ M_W(T) + ε`
  calc μ W' = ENNReal.ofReal (T ω + (μ.real W' - T ω)) := by
        rw [add_sub_cancel, ofReal_measureReal hμW'.ne]
    _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal (μ.real W' - T ω) := ENNReal.ofReal_add_le
    _ ≤ T.massOn W + ε := add_le_add hTω (hint.le.trans_eq ENNReal.ofReal_coe_nnreal)
/-- Exhaustion by compactly contained open sets: if `U, W ⊆ ℝᴾ` are open, `μ(ℝᴾ \ U) = 0` and
`μ(W') ≤ m` for every open `W' ⊂⊂ U` with `W' ⊆ W`, then `μ(W) ≤ m`.  The open sets
`W'ⱼ = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` have closures inside the compact sets
`{y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} ⊆ W ∩ U`, increase with `j` and exhaust `W ∩ U`,
so `μ(W) = μ(W ∩ U) = supⱼ μ(W'ⱼ) ≤ m` by continuity from below. -/
theorem Submission.cmrc_measure_le_of_compactlyContained : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U W : Set (Euclid P)) (m : ℝ≥0∞), IsOpen U → IsOpen W → μ Uᶜ = 0 → (∀ W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ m) → μ W ≤ m := by
  intro P μ U W m hU hW hUc hm
  -- `V j = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` exhausts the open set `W ∩ U`
  set V : ℕ → Set (Euclid P) :=
    fun j => {y | ‖y‖ < j ∧ ((j : ℝ≥0∞) + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}
  have hd : Continuous fun y : Euclid P => infEDist y (W ∩ U)ᶜ := continuous_infEDist
  have hpos : ∀ j : ℕ, 0 < ((j : ℝ≥0∞) + 1)⁻¹ := fun j => ENNReal.inv_pos.2 (by simp)
  -- `closure (V j)` lies in `F j = {y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ}`, a compact
  -- subset of `W ∩ U`
  have hF : ∀ j : ℕ, IsCompact (closure (V j)) ∧ closure (V j) ⊆ W ∩ U := by
    intro j
    have hVF : closure (V j) ⊆
        {y : Euclid P | ‖y‖ ≤ j ∧ ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} :=
      closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const hd))
    refine ⟨(isCompact_closedBall (0 : Euclid P) (j : ℝ)).of_isClosed_subset isClosed_closure
      fun y hy => ?_, fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact (hVF hy).1
    · by_contra hy'
      have h := (hVF hy).2
      rw [infEDist_zero_of_mem hy'] at h
      exact (hpos j).not_ge h
  have hVsub : ∀ j, V j ⊆ W ∩ U := fun j => subset_closure.trans (hF j).2
  have hVm : ∀ j, μ (V j) ≤ m := fun j =>
    hm (V j) ((isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd))
      ⟨(hF j).1, (hF j).2.trans inter_subset_right⟩ ((hVsub j).trans inter_subset_left)
  have hmono : Monotone V := by
    intro j k hjk y hy
    refine ⟨hy.1.trans_le (by exact_mod_cast hjk), lt_of_le_of_lt ?_ hy.2⟩
    gcongr
  have hUnion : ⋃ j, V j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset hVsub) fun y hy => ?_
    have hne : infEDist y (W ∩ U)ᶜ ≠ 0 := fun h0 =>
      ((mem_iff_infEDist_zero_of_closed (hW.inter hU).isClosed_compl).2 h0) hy
    obtain ⟨j₁, hj₁⟩ := ENNReal.exists_inv_nat_lt hne
    obtain ⟨j₂, hj₂⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max j₁ j₂, hj₂.trans_le (by exact_mod_cast le_max_right j₁ j₂),
      lt_of_le_of_lt ?_ hj₁⟩
    gcongr
    norm_cast
    omega
  -- `μ W = μ (W ∩ U)` since `μ Uᶜ = 0`; continuity from below along the increasing `V j`
  calc μ W = μ (⋃ j, V j) := by rw [hUnion, measure_inter_conull hUc]
    _ = ⨆ j, μ (V j) := hmono.measure_iUnion
    _ ≤ m := iSup_le hVm

/-- **Mass of the current `Ξ(ω) = ∫ ⟨ω, ζ₀⟩ dν` with a constant multivector `ζ₀`** (Simon 6.2.5;
step 5(δ) of the integer-multiplicity criterion for cycles; `|·|_E` is `covectorEuclideanNorm`).
Suppose `ν` is finite on compact sets, `|⟨α, ζ₀⟩| ≤ s |α|_E` for every `α`, and `⟨β, ζ₀⟩ = s` for
some `β` with `|β|_E ≤ 1`.  Then `s ≥ 0`, because `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`.  Put `μ = s ν` and
`ξ ≡ s⁻¹ ζ₀`.  Then `|⟨α, ξ⟩| ≤ |α|_E` and `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ`; for `s = 0` both sides vanish,
since then `ζ₀ = 0`.  `Submission.cmrc_massOn_le_of_repr` gives `M_W(Ξ) ≤ μ(W) = s ν(W)`.  For
`s > 0` the constant field `β` norms `ξ`, as `⟨β, ξ⟩ = 1`.  So
`Submission.cmrc_measure_le_massOn_of_norming` gives `μ(W') ≤ M_W(Ξ)` for every open `W' ⊂⊂ ℝᴾ`
with `W' ⊆ W`, and `Submission.cmrc_measure_le_of_compactlyContained` gives `μ(W) ≤ M_W(Ξ)`. -/
theorem Submission.cbr_ci_const_vector_massOn : ∀ (P m : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P m) (s : ℝ) (Ξ : GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ α : Covector (Euclid P) m, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → (∃ β : Covector (Euclid P) m, covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω = ∫ x, ζ₀ ((ω : DifferentialForm (Euclid P) m) x) ∂ν) → ∀ W : Set (Euclid P), IsOpen W → Ξ.massOn W = ENNReal.ofReal s * ν W := by
  rintro P m ν ζ₀ s Ξ hνK hζ₀ ⟨β, hβ1, hζβ⟩ hΞ W hW
  -- Step 1: `s ≥ 0`, since `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`
  have hs : 0 ≤ s := by
    have h := hζ₀ β
    rw [hζβ] at h
    nlinarith [neg_le_abs s, covectorEuclideanNorm_nonneg β]
  -- Step 2: `ζ₀ = s (s⁻¹ ζ₀)`; for `s = 0` this says `ζ₀ = 0`, as `|⟨α, ζ₀⟩| ≤ 0`
  have hζs : ∀ α : Covector (Euclid P) m, s * (s⁻¹ * ζ₀ α) = ζ₀ α := by
    intro α
    rcases hs.eq_or_lt with h0 | hpos
    · have h := hζ₀ α
      rw [← h0, zero_mul, abs_nonpos_iff] at h
      rw [← h0, zero_mul, h]
    · rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  -- Step 3: the constant field `ξ ≡ s⁻¹ ζ₀` is unit-bounded, `|⟨α, ξ⟩| ≤ |α|_E`
  have hξ : ∀ (_ : Euclid P) (α : Covector (Euclid P) m),
      |(s⁻¹ • ζ₀) α| ≤ covectorEuclideanNorm α := by
    intro _ α
    rw [_root_.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    rcases hs.eq_or_lt with h0 | hpos
    · rw [← h0, abs_zero, inv_zero, zero_mul]
      exact covectorEuclideanNorm_nonneg α
    · rw [abs_of_pos hpos, inv_mul_le_iff₀ hpos]
      exact hζ₀ α
  -- Step 4: `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ` for `μ = s ν`
  have hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω =
      ∫ x, (s⁻¹ • ζ₀) ((ω : DifferentialForm (Euclid P) m) x) ∂(ENNReal.ofReal s • ν) := by
    intro ω
    rw [hΞ ω, integral_smul_measure, ENNReal.toReal_ofReal hs, smul_eq_mul,
      ← integral_const_mul]
    simp only [_root_.smul_apply, smul_eq_mul, hζs]
  have hμW : (ENNReal.ofReal s • ν) W = ENNReal.ofReal s * ν W := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [← hμW]
  -- Step 5: upper bound `M_W(Ξ) ≤ μ(W)`
  refine le_antisymm (Submission.cmrc_massOn_le_of_repr P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) hξ hrep W) ?_
  -- Step 6: lower bound `μ(W) ≤ M_W(Ξ)`; trivial for `s = 0`, where `μ = 0`
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, zero_smul, Measure.coe_zero, Pi.zero_apply]
    exact zero_le
  -- for `s > 0`, `μ` is finite on compact sets and the constant covector `β` norms `ξ`:
  -- `⟨β, ξ⟩ = s⁻¹ ⟨β, ζ₀⟩ = 1`
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ → (ENNReal.ofReal s • ν) K < ∞ := by
    intro K hK _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hνK K hK)
  have hξβ : ∀ᵐ _ ∂(ENNReal.ofReal s • ν), (s⁻¹ • ζ₀) β = 1 := Eventually.of_forall fun _ => by
    rw [_root_.smul_apply, smul_eq_mul, hζβ, inv_mul_cancel₀ hpos.ne']
  -- `μ(W') ≤ M_W(Ξ)` for open `W' ⊂⊂ ℝᴾ` with `W' ⊆ W`; exhaust `W` by such `W'`
  refine Submission.cmrc_measure_le_of_compactlyContained P (ENNReal.ofReal s • ν) univ W
    (Ξ.massOn W) isOpen_univ hW (by rw [compl_univ, measure_empty]) fun W' hW' hW'U hW'W => ?_
  exact Submission.cmrc_measure_le_massOn_of_norming P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) (fun _ => β) hμK aestronglyMeasurable_const hξ hrep
    aestronglyMeasurable_const ⟨‖β‖, fun _ => le_rfl⟩ (fun _ => hβ1) hξβ W W' hW' hW'U hW'W

/-- **The operator norm of an `n`-covector is at most `Pⁿ` times its Euclidean coefficient norm**
(fact (F1) in the proof of `Submission.cbr_ci_blowup_limit`; `|·|_E` is `covectorEuclideanNorm`).
Let `e` be the standard basis of `ℝᴾ`.  Each coefficient satisfies
`|α(e_{J(0)}, …, e_{J(n−1)})| ≤ |α|_E`: it vanishes if `J` repeats an index, and otherwise
`I = J ∘ σ` with `σ = Tuple.sort J` is strictly increasing, `α(e ∘ I) = sgn σ · α(e ∘ J)`, and
`α(e ∘ I)²` is one of the summands of `|α|_E²`.  Expanding every `v_k` in `e` gives
`α(v) = Σ_J (Π_k v_k(J k)) α(e ∘ J)` over the `Pⁿ` maps `J : Fin n → Fin P`; with
`|v_k(i)| ≤ ‖v_k‖` this gives `|α(v)| ≤ Pⁿ |α|_E Π_k ‖v_k‖`, hence `‖α‖ ≤ Pⁿ |α|_E`. -/
theorem Submission.cbr_ci_bl_covector_opNorm_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ‖α‖ ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
  intro P n α
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Step 1: `|α(e_{J(0)}, …, e_{J(n−1)})| ≤ |α|_E` for every `J : Fin n → Fin P`
  have hcoef : ∀ J : Fin n → Fin P, |α (fun k => e (J k))| ≤ covectorEuclideanNorm α := by
    intro J
    by_cases hJ : Injective J
    · -- `I = J ∘ σ` with `σ = Tuple.sort J` is strictly increasing, `α(e ∘ I) = sgn σ · α(e ∘ J)`
      set σ := Tuple.sort J
      have hI : StrictMono (J ∘ σ) :=
        (Tuple.monotone_sort J).strictMono_of_injective (hJ.comp σ.injective)
      have hperm : α ((fun k => e (J k)) ∘ σ) = Equiv.Perm.sign σ • α (fun k => e (J k)) :=
        α.toAlternatingMap.map_perm (fun k => e (J k)) σ
      have habs : |α (fun k => e (J k))| = |α (fun k => e ((J ∘ σ) k))| := by
        change _ = |α ((fun k => e (J k)) ∘ σ)|
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      -- `α(e ∘ I)²` is one of the nonnegative summands of `|α|_E²`
      rw [habs]
      unfold covectorEuclideanNorm
      refine Real.abs_le_sqrt (le_trans (le_of_eq ?_)
        (Finset.single_le_sum (fun I _ => ?_) (Finset.mem_univ (J ∘ σ))))
      · rw [ite_eq_left hI]
      · positivity
    · -- a repeated index: `α(e ∘ J) = 0` by alternation
      have h0 : α (fun k => e (J k)) = 0 :=
        α.map_eq_zero_of_not_injective _ fun h => hJ (Injective.of_comp (f := ⇑e) h)
      rw [h0, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  refine α.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg P) n)
    (covectorEuclideanNorm_nonneg α)) fun v => ?_
  -- Step 2: `α(v) = Σ_J (Π_k v_k(J k)) α(e ∘ J)` by multilinearity
  have hexp : α v = ∑ J : Fin n → Fin P, (∏ k, v k (J k)) * α (fun k => e (J k)) := by
    conv_lhs => rw [show v = fun k => ∑ i, v k i • e i from
      funext fun k => (e.sum_repr (v k)).symm]
    rw [α.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← smul_eq_mul]
    exact α.map_smul_univ (fun k => v k (J k)) (fun k => e (J k))
  -- Step 3: each term is at most `(Π_k ‖v_k‖) |α|_E`, and there are `P ^ n` terms
  rw [hexp, Real.norm_eq_abs]
  calc |∑ J : Fin n → Fin P, (∏ k, v k (J k)) * α (fun k => e (J k))|
      ≤ ∑ J : Fin n → Fin P, |(∏ k, v k (J k)) * α (fun k => e (J k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J : Fin n → Fin P, (∏ k, ‖v k‖) * covectorEuclideanNorm α := by
        refine Finset.sum_le_sum fun J _ => ?_
        rw [abs_mul, Finset.abs_prod]
        refine mul_le_mul (Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => ?_)
          (hcoef J) (abs_nonneg _) (Finset.prod_nonneg fun k _ => norm_nonneg _)
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (v k) (J k)
    _ = (P : ℝ) ^ n * covectorEuclideanNorm α * ∏ k, ‖v k‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        simp only [Fintype.card_fin]
        push_cast
        ring

/-- **The weight is controlled by the multivector difference through a norming covector**
(fact (F2) in the proof of `Submission.cbr_ci_bl_density_bounds`; `|·|_E` is
`covectorEuclideanNorm`).  Let `‖α‖ ≤ C |α|_E` and `|⟨α, ζa⟩| ≤ |α|_E` for every `n`-covector
`α`, and let `β` satisfy `|β|_E ≤ 1` and `⟨β, ζx⟩ = 1`.  For `d = t ζx − t₀ ζa`,
`⟨β, d⟩ = t − t₀ ⟨β, ζa⟩` with `t₀ ⟨β, ζa⟩ ≤ t₀`, and `⟨β, d⟩ ≤ ‖d‖ ‖β‖ ≤ C ‖d‖`, as
`‖β‖ ≤ C |β|_E ≤ C`.  Hence `t ≤ t₀ + C ‖d‖`, and `ENNReal.ofReal` turns this into the bound. -/
theorem Submission.cbr_ci_bl_db_weight_le_enorm : ∀ (P n : ℕ) (ζx ζa : MultiVector P n) (t t₀ C : ℝ), 0 ≤ t₀ → 0 ≤ C → (∀ α : Covector (Euclid P) n, ‖α‖ ≤ C * covectorEuclideanNorm α) → (∀ α : Covector (Euclid P) n, |ζa α| ≤ covectorEuclideanNorm α) → (∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζx β = 1) → ENNReal.ofReal t ≤ ENNReal.ofReal t₀ + ENNReal.ofReal C * ‖t • ζx - t₀ • ζa‖ₑ := by
  rintro P n ζx ζa t t₀ C ht₀ hC hop hζa ⟨β, hβ1, hζβ⟩
  set d : MultiVector P n := t • ζx - t₀ • ζa with hd
  -- Step 1: `⟨β, d⟩ = t − t₀ ⟨β, ζa⟩`
  have hdβ : d β = t - t₀ * ζa β := by
    rw [hd, _root_.sub_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      hζβ, mul_one]
  -- Step 2: `t₀ ⟨β, ζa⟩ ≤ t₀`, as `⟨β, ζa⟩ ≤ |β|_E ≤ 1`
  have hζaβ : t₀ * ζa β ≤ t₀ :=
    mul_le_of_le_one_right ht₀ ((le_abs_self _).trans ((hζa β).trans hβ1))
  -- Step 3: `⟨β, d⟩ ≤ ‖d‖ ‖β‖ ≤ C ‖d‖`, as `‖β‖ ≤ C |β|_E ≤ C`
  have hβC : ‖β‖ ≤ C := (hop β).trans (mul_le_of_le_one_right hC hβ1)
  have hdle : d β ≤ C * ‖d‖ :=
    calc d β ≤ ‖d β‖ := Real.le_norm_self _
      _ ≤ ‖d‖ * ‖β‖ := d.le_opNorm β
      _ ≤ ‖d‖ * C := mul_le_mul_of_nonneg_left hβC (norm_nonneg d)
      _ = C * ‖d‖ := mul_comm _ _
  -- Step 4: `t ≤ t₀ + C ‖d‖`; pass to `[0, ∞]`
  have ht : t ≤ t₀ + C * ‖d‖ := by linarith
  calc ENNReal.ofReal t ≤ ENNReal.ofReal (t₀ + C * ‖d‖) := ENNReal.ofReal_le_ofReal ht
    _ = ENNReal.ofReal t₀ + ENNReal.ofReal C * ‖d‖ₑ := by
      rw [ENNReal.ofReal_add ht₀ (mul_nonneg hC (norm_nonneg d)), ENNReal.ofReal_mul hC,
        ofReal_norm d]
/-- **Mass of a Borel set under a pointwise bound on the density** (step 2, mass of balls, in the
proof of `Submission.cbr_ci_bl_density_bounds`).  Let `μ = θ Hⁿ⌞M` with `M`, `B` Borel, `B ⊆ B'`,
`K ≠ ∞` and `θ ≤ c + K g` on `M`.  Since `B` is Borel, `μ(B) = ∫_{M∩B} θ dHⁿ`.  Integrating the
bound over `M ∩ B` gives `μ(B) ≤ c Hⁿ(M ∩ B) + K ∫_{M∩B} g dHⁿ`, and `M ∩ B ⊆ M ∩ B'`
enlarges the last integral. -/
theorem Submission.cbr_ci_bl_db_withDensity_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (M B B' : Set (Euclid P)) (θ : Euclid P → ℝ) (g : Euclid P → ℝ≥0∞) (c K : ℝ≥0∞), MeasurableSet M → MeasurableSet B → B ⊆ B' → K ≠ ∞ → μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, ENNReal.ofReal (θ x) ≤ c + K * g x) → μ B ≤ c * μHE[n] (M ∩ B) + K * ∫⁻ x in M ∩ B', g x ∂μHE[n] := by
  intro P n μ M B B' θ g c K hM hB hBB' hK hμ hθ
  -- Step 1: `μ(B) = ∫⁻_{M ∩ B} ofReal θ dHⁿ`
  have hμB : μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
    rw [hμ, withDensity_apply _ hB, Measure.restrict_restrict hB, inter_comm]
  rw [hμB]
  calc ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n]
      ≤ ∫⁻ x in M ∩ B, (c + K * g x) ∂μHE[n] :=
        -- Step 2: integrate the pointwise bound over the Borel set `M ∩ B`
        setLIntegral_mono' (hM.inter hB) fun x hx => hθ x hx.1
    _ = c * μHE[n] (M ∩ B) + K * ∫⁻ x in M ∩ B, g x ∂μHE[n] := by
        -- Step 3: split off the constant and factor out the finite `K`
        rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_const_mul' K g hK]
    _ ≤ c * μHE[n] (M ∩ B) + K * ∫⁻ x in M ∩ B', g x ∂μHE[n] := by
        -- Step 4: enlarge `M ∩ B` to `M ∩ B'` in the `g`-integral
        gcongr c * μHE[n] (M ∩ B) + K * ?_
        exact lintegral_mono_set (inter_subset_inter_right M hBB')
/-- **Eventual density bounds from a ball-mass inequality** (steps 3 and 4 of the proof of
`Submission.cbr_ci_bl_density_bounds`).  Write `V(r) = ωₙ rⁿ`, which is nonzero for `r > 0` and
always finite.  As `r ↓ 0`, eventually `ofReal (η₁ / 2) < m / V` (by the liminf bound),
`K (o / V) < ofReal (η₁ / 4)` (since `K (o / V) → K · 0 = 0`) and `H / V < 2` (by the limsup
bound); choose `r₀` so that all three hold on `(0, r₀)`.  Clearing denominators gives
`ofReal (η₁ / 2) V ≤ m(r)`, `K o(r) ≤ ofReal (η₁ / 4) V` and `H(r) ≤ 2 V`.  Splitting
`η₁ / 2 = η₁ / 4 + η₁ / 4`, using `m(r) ≤ ofReal θ₀ h(r) + K o(r)` and cancelling the finite
quarter gives `ofReal (η₁ / 4) V ≤ ofReal θ₀ h(r)`; dividing by `ofReal θ₀ ∈ (0, ∞)` gives
`ofReal (η₁ / (4 θ₀)) V ≤ h(r)`. -/
theorem Submission.cbr_ci_bl_db_eventual_bounds : ∀ (n : ℕ) (m h H o : ℝ → ℝ≥0∞) (θ₀ η₁ : ℝ) (K : ℝ≥0∞), 0 < θ₀ → 0 < η₁ → K ≠ ∞ → (∀ r : ℝ, 0 < r → m r ≤ ENNReal.ofReal θ₀ * h r + K * o r) → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => m r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) → limsup (fun r : ℝ => H r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => o r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ENNReal.ofReal (η₁ / (4 * θ₀)) * (unitBallVolume n * ENNReal.ofReal (r ^ n)) ≤ h r ∧ H r ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n)) := by
  intro n m h H o θ₀ η₁ K hθ₀ hη₁ hK hB hL hU hD
  -- Step 1: `V(r) = ωₙ rⁿ` is nonzero for `r > 0` and always finite
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hV0 : ∀ r : ℝ, 0 < r → unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 := fun r hr =>
    mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne'
  have hVt : ∀ r : ℝ, unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ ∞ := fun r =>
    ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top
  -- Step 2: (a) `ofReal (η₁ / 2) < m / V` eventually, by the liminf bound
  have ha : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (η₁ / 2) < m r / (unitBallVolume n * ENNReal.ofReal (r ^ n)) :=
    eventually_lt_of_lt_liminf
      (((ENNReal.ofReal_lt_ofReal_iff hη₁).2 (half_lt_self hη₁)).trans_le hL)
  -- Step 3: (b) `K (o / V) < ofReal (η₁ / 4)` eventually, since `K (o / V) → K · 0 = 0`
  have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      K * (o r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) < ENNReal.ofReal (η₁ / 4) := by
    have hK0 := ENNReal.Tendsto.const_mul hD (Or.inr hK)
    rw [mul_zero] at hK0
    exact (tendsto_order.1 hK0).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  -- Step 4: (c) `H / V < 2` eventually, by the limsup bound
  have hc : ∀ᶠ r in 𝓝[>] (0 : ℝ), H r / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < 2 :=
    eventually_lt_of_limsup_lt (hU.trans_lt ENNReal.one_lt_two)
  -- Step 5: all three hold on some interval `(0, r₀)`
  obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (ha.and (hb.and hc))
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  obtain ⟨ha', hb', hc'⟩ := hsub ⟨hr, hrr₀⟩
  set V := unitBallVolume n * ENNReal.ofReal (r ^ n) with hV
  -- Step 6: clearing denominators; this already gives `H(r) ≤ 2 V`
  have hmV : ENNReal.ofReal (η₁ / 2) * V ≤ m r :=
    ((ENNReal.lt_div_iff_mul_lt (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 ha').le
  have hoV : K * o r ≤ ENNReal.ofReal (η₁ / 4) * V := by
    rw [← mul_div_assoc] at hb'
    exact ((ENNReal.div_lt_iff (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 hb').le
  refine ⟨?_, ((ENNReal.div_lt_iff (Or.inl (hV0 r hr)) (Or.inl (hVt r))).1 hc').le⟩
  -- Step 7: split `ofReal (η₁ / 2) V` into two quarters
  have hq4 : 0 ≤ η₁ / 4 := by positivity
  have hsplit : ENNReal.ofReal (η₁ / 2) * V =
      ENNReal.ofReal (η₁ / 4) * V + ENNReal.ofReal (η₁ / 4) * V := by
    rw [show η₁ / 2 = η₁ / 4 + η₁ / 4 by ring, ENNReal.ofReal_add hq4 hq4, add_mul]
  -- Step 8: cancel the finite quarter `ofReal (η₁ / 4) V`
  have hq : ENNReal.ofReal (η₁ / 4) * V ≤ ENNReal.ofReal θ₀ * h r := by
    have hfin : ENNReal.ofReal (η₁ / 4) * V ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hVt r)
    refine (ENNReal.add_le_add_iff_right hfin).1 ?_
    calc ENNReal.ofReal (η₁ / 4) * V + ENNReal.ofReal (η₁ / 4) * V
        = ENNReal.ofReal (η₁ / 2) * V := hsplit.symm
      _ ≤ m r := hmV
      _ ≤ ENNReal.ofReal θ₀ * h r + K * o r := hB r hr
      _ ≤ ENNReal.ofReal θ₀ * h r + ENNReal.ofReal (η₁ / 4) * V := by gcongr
  -- Step 9: divide by `ofReal θ₀ ∈ (0, ∞)`
  have hθ0 : ENNReal.ofReal θ₀ ≠ 0 := (ENNReal.ofReal_pos.2 hθ₀).ne'
  have heq : ENNReal.ofReal (η₁ / (4 * θ₀)) = (ENNReal.ofReal θ₀)⁻¹ * ENNReal.ofReal (η₁ / 4) := by
    rw [← ENNReal.ofReal_inv_of_pos hθ₀, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ₀.le)]
    congr 1
    field_simp
  calc ENNReal.ofReal (η₁ / (4 * θ₀)) * V
      = (ENNReal.ofReal θ₀)⁻¹ * (ENNReal.ofReal (η₁ / 4) * V) := by rw [heq, mul_assoc]
    _ ≤ (ENNReal.ofReal θ₀)⁻¹ * (ENNReal.ofReal θ₀ * h r) := by gcongr
    _ = h r := ENNReal.inv_mul_cancel_left hθ0 ENNReal.ofReal_ne_top

/-- **Two-sided density bounds at a good point of `μ = θ Hⁿ⌞M`** (step 1 of the blow-up argument in
the integer multiplicity criterion for cycles; Simon 6.2.8, 7.3.1).  Put `θ₀ = θ(a) > 0`, `τ = θζ`,
`τ₀ = τ(a)`, `V(r) = ωₙ rⁿ` and `o(r) = ∫_{M ∩ B̄_r(a)} ‖τ − τ₀‖ dHⁿ`.  (F2) For `x ∈ M`, testing
`τ(x) − τ₀` on a covector `β` with `|β|_E ≤ 1` and `⟨β, ζ(x)⟩ = 1` gives
`θ(x) ≤ θ₀ + Pⁿ ‖τ(x) − τ₀‖`, since `⟨β, ζ(a)⟩ ≤ 1` and `‖β‖ ≤ Pⁿ |β|_E`
(`Submission.cbr_ci_bl_db_weight_le_enorm`, `Submission.cbr_ci_bl_covector_opNorm_le`).
Integrating (F2) over `M ∩ B_r(a) ⊆ M ∩ B̄_r(a)` gives `μ(B_r(a)) ≤ θ₀ Hⁿ(M ∩ B_r(a)) + Pⁿ o(r)`
(`Submission.cbr_ci_bl_db_withDensity_le`).  For small `r` the lower density bound gives
`μ(B_r(a)) ≥ (η₁/2) V(r)`, `o(r)/V(r) → 0` gives `Pⁿ o(r) ≤ (η₁/4) V(r)` and the upper density
bound gives `Hⁿ(M ∩ B̄_r(a)) ≤ 2 V(r)`; cancelling `(η₁/4) V(r)` and dividing by `θ₀` yields
`Hⁿ(M ∩ B_r(a)) ≥ (η₁/(4θ₀)) V(r)` (`Submission.cbr_ci_bl_db_eventual_bounds`). -/
theorem Submission.cbr_ci_bl_density_bounds : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n) (a : Euclid P) (η₁ : ℝ), MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) → a ∈ M → 0 < η₁ → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => μ (ball a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) → limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ENNReal.ofReal (η₁ / (4 * θ a)) * (unitBallVolume n * ENNReal.ofReal (r ^ n)) ≤ μHE[n] (M ∩ ball a r) ∧ μHE[n] (M ∩ closedBall a r) ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n)) := by
  intro P n μ M θ ζ a η₁ hM _ _ hμ hθ hζ hβ ha hη₁ hL hU hD
  -- `K = ofReal(Pⁿ)` is finite
  have hK : ENNReal.ofReal ((P : ℝ) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Step 1 (F2): `θ(x) ≤ θ(a) + Pⁿ ‖θ(x)ζ(x) − θ(a)ζ(a)‖` on `M`, read in `[0, ∞]`
  have hF2 : ∀ x ∈ M, ENNReal.ofReal (θ x) ≤
      ENNReal.ofReal (θ a) + ENNReal.ofReal ((P : ℝ) ^ n) * ‖θ x • ζ x - θ a • ζ a‖ₑ :=
    fun x hx => Submission.cbr_ci_bl_db_weight_le_enorm P n (ζ x) (ζ a) (θ x) (θ a)
      ((P : ℝ) ^ n) (hθ a ha).le (by positivity) (Submission.cbr_ci_bl_covector_opNorm_le P n)
      (hζ a) (hβ x hx)
  -- Step 2: `μ(B_r(a)) ≤ θ(a) Hⁿ(M ∩ B_r(a)) + Pⁿ o(r)`, integrating (F2) over `M ∩ B_r(a)`
  have hmass : ∀ r : ℝ, 0 < r → μ (ball a r) ≤ ENNReal.ofReal (θ a) * μHE[n] (M ∩ ball a r) +
      ENNReal.ofReal ((P : ℝ) ^ n) *
        ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n] :=
    fun r _ => Submission.cbr_ci_bl_db_withDensity_le P n μ M (ball a r) (closedBall a r) θ
      (fun x => ‖θ x • ζ x - θ a • ζ a‖ₑ) (ENNReal.ofReal (θ a)) (ENNReal.ofReal ((P : ℝ) ^ n))
      hM measurableSet_ball ball_subset_closedBall hK hμ hF2
  -- Steps 3–4: eventual bounds from (L), (D) and (U); cancel `(η₁/4) V(r)`, divide by `θ(a)`
  exact Submission.cbr_ci_bl_db_eventual_bounds n (fun r => μ (ball a r))
    (fun r => μHE[n] (M ∩ ball a r)) (fun r => μHE[n] (M ∩ closedBall a r))
    (fun r => ∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) (θ a) η₁
    (ENNReal.ofReal ((P : ℝ) ^ n)) (hθ a ha) hη₁ hK hmass hL hU hD

/-- The operator norm of an `n`-covector on `ℝᴾ` is at most a constant times its Euclidean
coefficient norm: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_I`, set to `0` on tuples `I` that are not
strictly increasing, is linear and injective on the finite-dimensional space `Λⁿ(ℝᴾ)`, hence
antilipschitz, and each of its coordinates is at most `covectorEuclideanNorm α` in absolute
value. -/
theorem Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm : ∀ (P n : ℕ), ∃ K : ℝ, 0 < K ∧ ∀ α : Covector (Euclid P) n, ‖α‖ ≤ K * covectorEuclideanNorm α := by
  intro P n
  classical
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  -- `L α = (α(e ∘ I))_I` on strictly increasing `I`, and `0` elsewhere
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I =>
        if StrictMono I then α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i) else 0
      map_add' := fun α β => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI]
      map_smul' := fun c α => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro α hα
    refine Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords P n α fun I hI => ?_
    simpa [L, hI] using congrFun hα I
  obtain ⟨K, hKpos, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨K, NNReal.coe_pos.2 hKpos, fun α => ?_⟩
  have h1 : ‖α‖ ≤ K * ‖L α‖ := by
    simpa using hK.le_mul_dist α 0
  -- `|α(e ∘ I)| ≤ covectorEuclideanNorm α`: one summand of the sum under the square root
  have h2 : ‖L α‖ ≤ covectorEuclideanNorm α := by
    refine (pi_norm_le_iff_of_nonneg (covectorEuclideanNorm_nonneg α)).2 fun I => ?_
    by_cases hI : StrictMono I
    · have hs := Finset.single_le_sum (f := fun J : Fin n → Fin P =>
        if StrictMono J then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0)
        (fun J _ => by split_ifs <;> positivity) (Finset.mem_univ I)
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hI, ↓reduceIte, Real.norm_eq_abs]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by simpa [hI] using hs)
    · simp [L, hI, covectorEuclideanNorm_nonneg]
  calc ‖α‖ ≤ K * ‖L α‖ := h1
    _ ≤ K * covectorEuclideanNorm α := by gcongr

/-- **The norm on `n`-vectors dual to the Euclidean coefficient norm** (step 1 of the density
representation of a cycle).  Let `|α|` be the Euclidean coefficient norm on `Λⁿ(ℝᴾ)`,
`B = {β : |β| ≤ 1}` and `N ζ = sup ζ(B)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper, and `B`
is closed (`|·|` is continuous) and bounded (`‖β‖ ≤ K |β| ≤ K`), hence compact; so the supremum
is attained, and `0 ∈ B` gives `N ζ ≥ 0`.  If `|α| = 0` then `‖α‖ ≤ K |α| = 0`; otherwise
`±|α|⁻¹ α ∈ B` gives `|ζ α| ≤ N ζ |α|`.  Finally, if `ζ β = N ζ` with `β ∈ B`, then
`N ζ ≤ ζ' β + ‖ζ - ζ'‖ ‖β‖ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz, hence continuous. -/
theorem Submission.cbr_ci_dr_multivector_dual_norm : ∀ (P n : ℕ), ∃ N : MultiVector P n → ℝ, Continuous N ∧ (∀ ζ : MultiVector P n, 0 ≤ N ζ) ∧ (∀ (ζ : MultiVector P n) (α : Covector (Euclid P) n), |ζ α| ≤ N ζ * covectorEuclideanNorm α) ∧ (∀ ζ : MultiVector P n, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ β = N ζ) := by
  intro P n
  -- Steps 3–4: `Λⁿ(ℝᴾ)` is finite-dimensional (hence proper), `|·|` is continuous and
  -- absolutely homogeneous, and `‖α‖ ≤ K |α|`
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  obtain ⟨-, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨K, hK, hnorm⟩ := Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm P n
  -- Step 5: the unit ball `B` of `|·|` contains `0`, lies in `closedBall 0 K` and is compact
  let B := {β : Covector (Euclid P) n | covectorEuclideanNorm β ≤ 1}
  have h0B : (0 : Covector (Euclid P) n) ∈ B := by
    show covectorEuclideanNorm (0 : Covector (Euclid P) n) ≤ 1
    rw [covectorEuclideanNorm_zero]
    exact zero_le_one
  have hBK : ∀ β ∈ B, ‖β‖ ≤ K := fun β hβ =>
    (hnorm β).trans (mul_le_of_le_one_right hK.le hβ)
  have hBc : IsCompact B :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Covector (Euclid P) n)) (r := K)).subset
        fun β hβ => mem_closedBall_zero_iff.mpr (hBK β hβ))
  -- Step 6: `N ζ = sup ζ(B)` is attained on `B` and bounds `ζ` on `B`
  have hmem : ∀ ζ : MultiVector P n, ∃ β ∈ B, ζ β = sSup (ζ '' B) := fun ζ =>
    (hBc.image ζ.continuous).sSup_mem ⟨ζ 0, 0, h0B, rfl⟩
  have hle : ∀ ζ : MultiVector P n, ∀ β ∈ B, ζ β ≤ sSup (ζ '' B) := fun ζ β hβ =>
    le_csSup (hBc.image ζ.continuous).bddAbove ⟨β, hβ, rfl⟩
  refine ⟨fun ζ => sSup (ζ '' B), ?_, fun ζ => ?_, fun ζ α => ?_, hmem⟩
  · -- Step 9: `N ζ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz
    refine (LipschitzWith.of_le_add_mul' (f := fun ζ : MultiVector P n => sSup (ζ '' B)) K
      fun ζ ζ' => ?_).continuous
    obtain ⟨β, hβ, hζβ⟩ := hmem ζ
    have h1 : ζ β - ζ' β ≤ ‖ζ - ζ'‖ * K := by
      have h := (ζ - ζ').le_opNorm β
      rw [sub_apply, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans
        (h.trans (mul_le_mul_of_nonneg_left (hBK β hβ) (norm_nonneg _)))
    have h2 := hle ζ' β hβ
    rw [dist_eq_norm ζ ζ']
    show sSup (ζ '' B) ≤ sSup (ζ' '' B) + K * ‖ζ - ζ'‖
    linarith
  · -- Step 7: `0 ∈ B` and `ζ 0 = 0`
    exact (map_zero ζ).symm.le.trans (hle ζ 0 h0B)
  · -- Step 8: if `|α| = 0` then `α = 0`; otherwise rescale `α` into `B`
    show |ζ α| ≤ sSup (ζ '' B) * covectorEuclideanNorm α
    rcases (covectorEuclideanNorm_nonneg α).eq_or_lt with h | h
    · have hα : ‖α‖ ≤ 0 := by
        have h' := hnorm α
        rwa [← h, mul_zero] at h'
      rw [norm_le_zero_iff.mp hα, map_zero, abs_zero, covectorEuclideanNorm_zero, mul_zero]
    · have hβ : (covectorEuclideanNorm α)⁻¹ • α ∈ B := by
        show covectorEuclideanNorm ((covectorEuclideanNorm α)⁻¹ • α) ≤ 1
        rw [hsmul, abs_inv, abs_of_pos h, inv_mul_cancel₀ h.ne']
      have hβ' : -((covectorEuclideanNorm α)⁻¹ • α) ∈ B := by
        show covectorEuclideanNorm (-((covectorEuclideanNorm α)⁻¹ • α)) ≤ 1
        rw [covectorEuclideanNorm_neg]
        exact hβ
      have h1 := hle ζ _ hβ
      have h2 := hle ζ _ hβ'
      rw [map_neg] at h2
      calc |ζ α| = covectorEuclideanNorm α * |ζ ((covectorEuclideanNorm α)⁻¹ • α)| := by
            rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h,
              mul_inv_cancel_left₀ h.ne']
        _ ≤ covectorEuclideanNorm α * sSup (ζ '' B) :=
            mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, h1⟩) h.le
        _ = sSup (ζ '' B) * covectorEuclideanNorm α := mul_comm _ _
/-- Positive lower `n`-density of a finite measure forces finite `Hⁿ`-measure (Vitali `5r`-covering,
used for Simon 7.2.4 via the density representation): if `μ(ℝᴾ) < ∞` and
`liminf_{r↓0} μ(B_r(x))/(ωₙrⁿ) ≥ η > 0` for every `x ∈ A`, then `Hⁿ(A) < ∞`.  At scale `k`, choose
radii `rₖ(x) < 1/(k+1)` with `c rₖ(x)ⁿ ≤ μ(B̄_{rₖ(x)}(x))`, `c = (η/2)ωₙ`; the Vitali subfamily
`uₖ ⊆ A` is countable and disjoint, so `Σ_{uₖ} rₖⁿ ≤ μ(ℝᴾ)/c`, and the enlarged balls
`B̄_{5rₖ(b)}(b)` cover `A` with `Σ diamⁿ ≤ 10ⁿ μ(ℝᴾ)/c`. -/
theorem Submission.cbr_ci_dr_euclideanHausdorff_lt_top_of_lower_density : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (η : ℝ), 0 < η → μ univ < ∞ → (∀ x ∈ A, ENNReal.ofReal η ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → μHE[n] A < ∞ := by
  intro P n μ A η hη hμ hA
  -- `c = (η/2) ωₙ ∈ (0, ∞)`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  set c : ℝ≥0∞ := ENNReal.ofReal (η / 2) * unitBallVolume n with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (half_pos hη)).ne' hω0
  have hctop : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop
  -- arbitrarily small radii `ρ` with `c ρⁿ ≤ μ(B̄_ρ(x))`
  have hgood : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
      c * ENNReal.ofReal (ρ ^ n) ≤ μ (closedBall x ρ) := by
    intro x hx δ hδ
    have hlt : ENNReal.ofReal (η / 2) < liminf (fun r : ℝ =>
        μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) :=
      ((ENNReal.ofReal_lt_ofReal_iff hη).2 (half_lt_self hη)).trans_le (hA x hx)
    obtain ⟨ρ, hρ, hρδ⟩ :=
      ((eventually_lt_of_lt_liminf hlt).and (Ioo_mem_nhdsGT hδ)).exists
    refine ⟨ρ, hρδ.1, hρδ.2, ?_⟩
    calc c * ENNReal.ofReal (ρ ^ n)
        = ENNReal.ofReal (η / 2) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
          rw [hc, mul_assoc]
      _ ≤ μ (ball x ρ) := ENNReal.mul_le_of_le_div hρ.le
      _ ≤ μ (closedBall x ρ) := measure_mono ball_subset_closedBall
  -- radii `rₖ(x) < 1/(k+1)` at every scale `k`
  choose! r hr0 hrδ hrμ using fun (k : ℕ) (x : Euclid P) (hx : x ∈ A) =>
    hgood x hx (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  -- Vitali subfamilies `uₖ ⊆ A`; they are countable since the balls have nonempty interior
  have hvit : ∀ k : ℕ, ∃ u ⊆ A, (u.PairwiseDisjoint fun a => closedBall a (r k a)) ∧
      ∀ a ∈ A, ∃ b ∈ u, closedBall a (r k a) ⊆ closedBall b (5 * r k b) := fun k =>
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A (fun a => a) (r k)
      (1 / ((k : ℝ) + 1)) (fun a ha => (hrδ k a ha).le) 5 (by norm_num)
  choose u huA hudisj hucov using hvit
  have hucount : ∀ k, (u k).Countable := fun k =>
    (hudisj k).countable_of_nonempty_interior fun a ha =>
      (nonempty_ball.2 (hr0 k a (huA k ha))).mono
        (interior_maximal ball_subset_closedBall isOpen_ball)
  have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
  -- `Σ_{b ∈ uₖ} rₖ(b)ⁿ ≤ μ(ℝᴾ)/c` by disjointness
  have hsum : ∀ k, ∑' b : u k, ENNReal.ofReal (r k b ^ n) ≤ μ univ / c := by
    intro k
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop), mul_comm, ← ENNReal.tsum_mul_left]
    calc ∑' b : u k, c * ENNReal.ofReal (r k b ^ n)
        ≤ ∑' b : u k, μ (closedBall (b : Euclid P) (r k b)) :=
          ENNReal.tsum_le_tsum fun b => hrμ k b (huA k b.2)
      _ = μ (⋃ b ∈ u k, closedBall b (r k b)) :=
          (measure_biUnion (hucount k) (hudisj k) fun b _ => measurableSet_closedBall).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  -- `diam B̄_{5rₖ(b)}(b) ≤ 10 rₖ(b)`
  have hdiam : ∀ k, ∀ b ∈ u k,
      ediam (closedBall b (5 * r k b)) ≤ ENNReal.ofReal (10 * r k b) := by
    intro k b _
    refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
    calc dist y z ≤ dist y b + dist z b := dist_triangle_right y z b
      _ ≤ 5 * r k b + 5 * r k b := add_le_add (mem_closedBall.1 hy) (mem_closedBall.1 hz)
      _ = 10 * r k b := by ring
  set Λ : ℝ≥0∞ := ENNReal.ofReal (10 ^ n) * (μ univ / c) with hΛ
  have hΛtop : Λ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.div_lt_top hμ.ne hc0)
  -- `μH[n](A) ≤ Λ` from the covers `{B̄_{5rₖ(b)}(b)}_{b ∈ uₖ}` of mesh `≤ 10/(k+1)`
  have hH : μH[n] A ≤ Λ := by
    have htend :
        Tendsto (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (10 : ℝ))
      rw [mul_zero] at h
      simpa using ENNReal.tendsto_ofReal h
    refine (Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) A (l := atTop)
      (ι := fun k => u k) _ htend (fun k b => closedBall (b : Euclid P) (5 * r k b))
      (Eventually.of_forall fun k b => (hdiam k b b.2).trans (ENNReal.ofReal_le_ofReal ?_))
      (Eventually.of_forall fun k a ha => ?_)).trans ?_
    · have := hrδ k b (huA k b.2)
      linarith
    · obtain ⟨b, hb, hab⟩ := hucov k a ha
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 k a ha).le)⟩
    · refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
      calc ∑' b : u k, ediam (closedBall (b : Euclid P) (5 * r k b)) ^ (n : ℝ)
          ≤ ∑' b : u k, ENNReal.ofReal (10 ^ n) * ENNReal.ofReal (r k b ^ n) := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            have h0 : 0 ≤ r k b := (hr0 k b (huA k b.2)).le
            rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
              ENNReal.ofReal_pow (by positivity)]
            exact pow_le_pow_left₀ bot_le (hdiam k b b.2) n
        _ = ENNReal.ofReal (10 ^ n) * ∑' b : u k, ENNReal.ofReal (r k b ^ n) :=
            ENNReal.tsum_mul_left
        _ ≤ Λ := by rw [hΛ]; gcongr; exact hsum k
  -- `μHE[n] = s • μH[n]` with a finite scalar `s`
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hH.trans_lt hΛtop)

/-- **The mass identity forces the representing `n`-vector field to attain `1` a.e.** (Simon Ch. 6,
2.7–2.8: in `T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T` with `μ_T(U) = M(T)`, `|T⃗| = 1` `μ_T`-a.e.).  Let `Γ ∈ 𝒟ₙ(ℝᴾ)`,
`μ` finite with `M(Γ) = μ(ℝᴾ)`, and `ξ` `μ`-a.e. strongly measurable with `|ξ(x)(α)| ≤ |α|` a.e.
and `Γ(ω) = ∫ ξ(x)(ω(x)) dμ`.  For the dual norm `N` of `|·|` on `n`-vectors, `f = N ∘ ξ` has
`0 ≤ f ≤ 1` a.e.; every mass-admissible `ω` gives `Γ(ω) ≤ ∫ f dμ`, so `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`.
Hence `∫ (1 − f) dμ = 0`, `f = 1` a.e., and a covector `β` attaining `N(ξ(x))` has `|β| ≤ 1`
and `ξ(x)(β) = 1`. -/
theorem Submission.cbr_ci_dr_ae_unit_attained_of_mass_eq : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ univ < ∞ → Γ.massOn univ = μ univ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1 := by
  intro P n Γ μ ξ hμ hmass hξ hbound hrep
  -- (1) the dual norm `N` of `|·|` on `n`-vectors (sibling `dual_norm`); `μ` is finite
  obtain ⟨N, hNc, hN0, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  have : IsFiniteMeasure μ := ⟨hμ⟩
  -- (2) `f = N ∘ ξ` satisfies `0 ≤ f ≤ 1` a.e. and is integrable
  have hf_le : ∀ᵐ x ∂μ, N (ξ x) ≤ 1 := by
    filter_upwards [hbound] with x hx
    obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
    calc N (ξ x) = ξ x β := hξβ.symm
      _ ≤ |ξ x β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hx β
      _ ≤ 1 := hβ
  have hf_int : Integrable (fun x => N (ξ x)) μ := by
    refine Integrable.of_bound (hNc.comp_aestronglyMeasurable hξ) 1 ?_
    filter_upwards [hf_le] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (hN0 _)]
  -- (3) every mass-admissible `ω` has `Γ(ω) = ∫ ξ(ω) dμ ≤ ∫ f dμ`, as `|ξ(x)(ω(x))| ≤ f(x)`
  have hadm : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid P)) n univ,
      Γ ω ≤ ∫ x, N (ξ x) ∂μ := by
    intro ω hω
    have hgN : ∀ x, |ξ x ((ω : DifferentialForm (Euclid P) n) x)| ≤ N (ξ x) := fun x =>
      (hNle (ξ x) _).trans (mul_le_of_le_one_right (hN0 _) (hω.2 x))
    have hg_meas : AEStronglyMeasurable
        (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hξ.prodMk ω.property.1.1.continuous.aestronglyMeasurable)
    have hg_int : Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      hf_int.mono' hg_meas (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgN x))
    rw [hrep ω]
    exact integral_mono hg_int hf_int fun x => (le_abs_self _).trans (hgN x)
  -- (4) `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`
  have hmass_le : μ univ ≤ ENNReal.ofReal (∫ x, N (ξ x) ∂μ) := by
    rw [← hmass]
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hadm ω hω)
  have hreal : μ.real univ ≤ ∫ x, N (ξ x) ∂μ :=
    ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => hN0 _) hmass_le
  -- (5) `∫ (1 − f) dμ = μ(ℝᴾ) − ∫ f dμ ≤ 0` with `1 − f ≥ 0` a.e., so `f = 1` a.e.
  have hsub_nonneg : 0 ≤ᵐ[μ] fun x => 1 - N (ξ x) := by
    filter_upwards [hf_le] with x hx
    exact sub_nonneg.2 hx
  have hsub_zero : ∫ x, (1 - N (ξ x)) ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hsub_nonneg)
    rw [integral_sub (integrable_const 1) hf_int, integral_const, smul_eq_mul, mul_one]
    exact sub_nonpos.2 hreal
  have hae : (fun x => 1 - N (ξ x)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hsub_nonneg ((integrable_const 1).sub hf_int)).1 hsub_zero
  -- (6) where `N(ξ(x)) = 1`, the covector attaining `N(ξ(x))` is the required `β`
  filter_upwards [hae] with x hx
  obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
  refine ⟨β, hβ, ?_⟩
  have h1 : 1 - N (ξ x) = 0 := hx
  rw [hξβ]
  linarith

/-- **Bounded strongly measurable modification of an `n`-vector field** (the Borel normalized
field `ξ₀ / max(1, |ξ₀|*)` of the density representation).  If `ξ` is `μ`-a.e. strongly
measurable and `|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x` and every `n`-covector `α`
(`|·| = covectorEuclideanNorm`), then some strongly measurable `ζ` satisfies the bound at every
`x` and agrees with `ξ` `μ`-a.e.  With `N = |·|*` the dual norm of
`cbr_ci_dr_multivector_dual_norm` and `ξ₀` a strongly measurable version of `ξ`, take
`ζ = max(1, N ∘ ξ₀)⁻¹ • ξ₀`: it is a continuous function of `ξ₀`, `|ζ(x)(α)| ≤ |α|` because
`N(ξ₀(x)) ≤ max(1, N(ξ₀(x)))`, and `ζ = ξ₀ = ξ` wherever `ξ₀ = ξ` and `ξ` is bounded, since
there `N(ξ) ≤ 1` by attainment of `N` on the unit ball. -/
theorem Submission.cbr_ci_dr_bounded_stronglyMeasurable_modification : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ ζ : Euclid P → MultiVector P n, StronglyMeasurable ζ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ ζ =ᵐ[μ] ξ := by
  intro P n μ ξ hξm hξb
  -- Step 1: the dual norm `N` on `n`-vectors (`dual_norm`)
  obtain ⟨N, hNc, -, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  -- Step 2: an `n`-vector `η` with `|η(α)| ≤ |α|` for all `α` has `N(η) ≤ 1` (attainment)
  have hN1 : ∀ η : MultiVector P n,
      (∀ α : Covector (Euclid P) n, |η α| ≤ covectorEuclideanNorm α) → N η ≤ 1 := by
    intro η hη
    obtain ⟨β, hβ, hηβ⟩ := hNatt η
    calc N η = η β := hηβ.symm
      _ ≤ |η β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hη β
      _ ≤ 1 := hβ
  -- Step 3: the normalization `η ↦ max(1, N(η))⁻¹ • η` is continuous (denominator `≥ 1`)
  have hm : ∀ η : MultiVector P n, 0 < max 1 (N η) := fun η =>
    zero_lt_one.trans_le (le_max_left _ _)
  have hFc : Continuous fun η : MultiVector P n => (max 1 (N η))⁻¹ • η :=
    ((continuous_const.max hNc).inv₀ fun η => (hm η).ne').smul continuous_id
  -- Step 4: `ζ := max(1, N ∘ ξ₀)⁻¹ • ξ₀` for a strongly measurable version `ξ₀` of `ξ`
  obtain ⟨ξ₀, hξ₀, hξξ₀⟩ : ∃ ξ₀ : Euclid P → MultiVector P n, StronglyMeasurable ξ₀ ∧
      ξ =ᵐ[μ] ξ₀ :=
    ⟨hξm.mk ξ, hξm.stronglyMeasurable_mk, hξm.ae_eq_mk⟩
  refine ⟨fun x => (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x, hFc.comp_stronglyMeasurable hξ₀, ?_, ?_⟩
  · -- Step 5: with `m = max(1, N(ξ₀ x))`, `|ζ(x)(α)| = m⁻¹ |ξ₀(x)(α)| ≤ m⁻¹ N(ξ₀ x) |α| ≤ |α|`
    intro x α
    show |((max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x) α| ≤ covectorEuclideanNorm α
    rw [smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 (hm (ξ₀ x))),
      inv_mul_le_iff₀ (hm (ξ₀ x))]
    exact (hNle (ξ₀ x) α).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (covectorEuclideanNorm_nonneg α))
  · -- Step 6: where `ξ₀ = ξ` and `ξ` is bounded, `N(ξ₀ x) ≤ 1`, so `m = 1` and `ζ(x) = ξ(x)`
    filter_upwards [hξξ₀, hξb] with x hx hxb
    show (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x = ξ x
    rw [← hx, max_eq_left (hN1 (ξ x) hxb), inv_one, one_smul]
/-- Radon–Nikodym with a carrier: if `μ` is finite, `μ(M₀ᶜ) = 0`, `ν(M₀) < ∞` and `μ ≪ ν`, then
`μ = (ν⌞M)·θ` for a Borel `M ⊆ M₀` and a Borel `θ > 0` on `M`.  With `ν₀ = ν⌞M₀` (finite) and
`h = dμ/dν₀`, `μ ≪ ν₀` gives `μ = ν₀·h` with `h < ∞` `ν₀`-a.e.; take
`M = M₀ ∩ {0 < h < ∞}` and `θ = 1_M · h.toReal`, so that `h = 1_M · ofReal θ` `ν₀`-a.e. -/
theorem Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M₀ : Set (Euclid P)), μ univ < ∞ → MeasurableSet M₀ → ν M₀ < ∞ → μ M₀ᶜ = 0 → (∀ E : Set (Euclid P), ν E = 0 → μ E = 0) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ), MeasurableSet M ∧ M ⊆ M₀ ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  intro P μ ν M₀ hμ hM₀ hνM₀ hμM₀c hac
  -- `μ` and `ν₀ = ν⌞M₀` are finite
  have : IsFiniteMeasure μ := ⟨hμ⟩
  have : IsFiniteMeasure (ν.restrict M₀) := isFiniteMeasure_restrict.mpr hνM₀.ne
  -- `μ ≪ ν₀`: `ν₀(E) = ν(E ∩ M₀)` and `μ(M₀ᶜ) = 0`
  have hμν₀ : μ ≪ ν.restrict M₀ := by
    intro E hE
    rw [Measure.restrict_apply' hM₀] at hE
    rw [← inter_union_compl E M₀]
    exact measure_union_null (hac _ hE) (measure_mono_null inter_subset_right hμM₀c)
  -- Radon–Nikodym: `μ = ν₀·h` with `h = dμ/dν₀` Borel and `h < ∞` `ν₀`-a.e.
  obtain ⟨h, hh, hμh, hh_lt⟩ : ∃ h : Euclid P → ℝ≥0∞, Measurable h ∧
      μ = (ν.restrict M₀).withDensity h ∧ ∀ᵐ x ∂(ν.restrict M₀), h x < ∞ := by
    refine ⟨μ.rnDeriv (ν.restrict M₀), Measure.measurable_rnDeriv _ _, ?_,
      Measure.rnDeriv_lt_top _ _⟩
    have hdec := Measure.haveLebesgueDecomposition_add μ (ν.restrict M₀)
    rwa [Measure.singularPart_eq_zero_of_ac hμν₀, zero_add] at hdec
  -- the carrier `M = M₀ ∩ {0 < h} ∩ {h < ∞}` and the density `θ = 1_M · h.toReal`
  set M : Set (Euclid P) := M₀ ∩ {x | 0 < h x} ∩ {x | h x < ∞}
  have hM : MeasurableSet M :=
    (hM₀.inter (measurableSet_lt measurable_const hh)).inter (measurableSet_lt hh measurable_const)
  have hMM₀ : M ⊆ M₀ := fun x hx => hx.1.1
  refine ⟨M, M.indicator fun x => (h x).toReal, hM, hMM₀, hh.ennreal_toReal.indicator hM,
    fun x hx => ?_, ?_⟩
  · rw [indicator_of_mem hx]
    exact ENNReal.toReal_pos hx.1.2.ne' hx.2.ne
  -- `h = 1_M · ofReal θ` `ν₀`-a.e., since `ν₀`-a.e. `x ∈ M₀` and `h x < ∞`
  have hae : h =ᵐ[ν.restrict M₀]
      M.indicator fun x => ENNReal.ofReal (M.indicator (fun x => (h x).toReal) x) := by
    filter_upwards [ae_restrict_mem hM₀, hh_lt] with x hxM₀ hxlt
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, indicator_of_mem hxM, ENNReal.ofReal_toReal hxlt.ne]
    · rw [indicator_of_notMem hxM]
      exact nonpos_iff_eq_zero.mp (not_lt.mp fun hpos => hxM ⟨⟨hxM₀, hpos⟩, hxlt⟩)
  -- `μ = ν₀·(1_M · ofReal θ) = (ν₀⌞M)·ofReal θ = (ν⌞M)·ofReal θ`
  rw [hμh, withDensity_congr_ae hae, withDensity_indicator hM,
    Measure.restrict_restrict_of_subset hMM₀]

/-- Density representation of the limit cycle (Simon 7.2.4 via the closure theorem, step 3 of the
integer multiplicity argument): if `μ = μ_Γ` is finite, `Γ(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|ξ|* ≤ 1`,
`μ ≪ Hⁿ` and `liminf_{r↓0} μ(B_r(x))/(ωₙrⁿ) ≥ η₀ > 0` for `μ`-a.e. `x`, then `μ = θ Hⁿ⌞M` and
`Γ(ω) = ∫_M θ ⟨ω, ζ⟩ dHⁿ` on a Borel carrier `M` with `Hⁿ(M) < ∞`.  `ζ` is the Borel bounded
modification of `ξ`; the mass identity `μ(ℝᴾ) = M(Γ)` makes it attain `1` on the unit covector
ball `μ`-a.e.  `M₀` is the complement of a Borel `μ`-null set off which this and the density
bound hold, so `Hⁿ(M₀) < ∞` (Vitali), and Radon–Nikodym for `μ ≪ Hⁿ⌞M₀` gives `M ⊆ M₀` and
`θ > 0` on `M`. -/
theorem Submission.cbr_ci_density_representation : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (η₀ : ℝ), 0 < η₀ → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0) → (∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M ∧ μHE[n] M < ∞ ∧ Measurable θ ∧ StronglyMeasurable ζ ∧ μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) ∧ (∀ x ∈ M, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) := by
  intro P n Γ μ ξ η₀ hη₀ hμ hmass hξm hξ hrep hnull hdens
  have hξae : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α :=
    Eventually.of_forall hξ
  -- a strongly measurable `ζ` with `|ζ(x)(α)| ≤ |α|` everywhere and `ζ = ξ` `μ`-a.e.
  obtain ⟨ζ, hζm, hζ, hζξ⟩ :=
    Submission.cbr_ci_dr_bounded_stronglyMeasurable_modification P n μ ξ hξm hξae
  -- `μ(ℝᴾ) = M(Γ)` forces `ξ`, hence `ζ`, to attain `1` on the unit covector ball `μ`-a.e.
  have hunit : ∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1 := by
    filter_upwards [Submission.cbr_ci_dr_ae_unit_attained_of_mass_eq P n Γ μ ξ hμ
      (hmass univ isOpen_univ) hξm hξae hrep, hζξ] with x hx hxζ
    rwa [hxζ]
  -- a Borel `μ`-null set `N` off which both `μ`-a.e. properties hold; `M₀ = Nᶜ`
  obtain ⟨N, hsN, hN, hμN⟩ := exists_measurable_superset_of_null (ae_iff.1 (hunit.and hdens))
  have hgood : ∀ x ∈ Nᶜ, (∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) ∧
      ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) /
        (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) :=
    fun x hx => not_not.1 fun h => hx (hsN h)
  -- `Hⁿ(M₀) < ∞` by the Vitali covering argument
  have hHN : μHE[n] Nᶜ < ∞ :=
    Submission.cbr_ci_dr_euclideanHausdorff_lt_top_of_lower_density P n μ Nᶜ η₀ hη₀ hμ
      fun x hx => (hgood x hx).2
  -- Radon–Nikodym for `μ ≪ Hⁿ⌞M₀`: `μ = θ Hⁿ⌞M` with `M ⊆ M₀` Borel and `θ > 0` on `M`
  obtain ⟨M, θ, hM, hMN, hθm, hθpos, hμeq⟩ :=
    Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous P μ μHE[n] Nᶜ hμ hN.compl
      hHN (by rwa [compl_compl]) hnull
  refine ⟨M, θ, ζ, hM, (measure_mono hMN).trans_lt hHN, hθm, hζm, hμeq, hθpos, hζ,
    fun x hx => (hgood x (hMN hx)).1, fun ω => ?_, fun x hx => (hgood x (hMN hx)).2⟩
  -- `Γ(ω) = ∫ ⟨ω, ζ⟩ dμ = ∫_M θ ⟨ω, ζ⟩ dHⁿ`
  have hωζ : (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) =ᵐ[μ]
      fun x => ζ x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hζξ] with x hx
    rw [hx]
  rw [hrep ω, integral_congr_ae hωζ, hμeq, integral_withDensity_eq_integral_toReal_smul
    hθm.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hM fun x hx => ?_
  simp only [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
/-- **Cut-off quadratic moments over `n`-planes** (the constant `cₙ` of the measurability proof
for the approximate tangent planes of Simon Ch. 3, 1.4).  For `n ≥ 1` one constant `c > 0`,
depending only on `n`, gives `∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|²` for every `P`,
every `n`-dimensional subspace `Q ⊆ ℝᴾ` and every `u ∈ ℝᴾ`.  On `ℝⁿ` put
`q(w) = ∫ max(1 − |z|², 0)⟨w, z⟩² dHⁿ(z)` and `c = q(e)`, `|e| = 1`: linear isometries preserve
`Hⁿ`, so `q` is invariant under them, `q(tw) = t²q(w)`, and a reflection maps `|w|e` to `w`,
whence `q(w) = c|w|²`; `c > 0` since the integrand is continuous, `≥ 0`, compactly supported and
`3/16` at `e/2`.  An isometry `ι = L⁻¹ : ℝⁿ → Q ⊆ ℝᴾ` carries `Hⁿ` to `Hⁿ⌞Q`, and
`⟨u, ι z⟩ = ⟨L(p_Q u), z⟩`, so the integral is `q(L(p_Q u)) = c|p_Q u|²`. -/
theorem Submission.exists_plane_cutoff_quadratic_moment_eq : ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ u : Euclid P, ∫ y in (Q : Set (Euclid P)), max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 ∂μHE[n] = c * ‖Q.starProjection u‖ ^ 2 := by
  intro n hn
  -- The moment `q(w)` on the model plane `ℝⁿ`; the constant is `c = q(e)` for a unit vector `e`.
  obtain ⟨q, hq_def⟩ : ∃ q : Euclid n → ℝ,
      ∀ w, q w = ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ w z ^ 2 ∂μHE[n] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Euclid n, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  -- `q(Rw) = q(w)` for a linear isometry `R`: substitute `z = Rz'`, `R` preserves `Hⁿ`.
  have hq_iso : ∀ (R : Euclid n ≃ₗᵢ[ℝ] Euclid n) (w : Euclid n), q (R w) = q w := by
    intro R w
    have key : ∫ z, max (1 - ‖R z‖ ^ 2) 0 * inner ℝ (R w) (R z) ^ 2 ∂μHE[n] =
        ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ (R w) z ^ 2 ∂μHE[n] :=
      (R.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n).integral_comp
        R.toHomeomorph.measurableEmbedding (fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ (R w) y ^ 2)
    simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map] at key
    rw [hq_def, hq_def, ← key]
  have hq_smul : ∀ (t : ℝ) (w : Euclid n), q (t • w) = t ^ 2 * q w := by
    intro t w
    rw [hq_def, hq_def, ← integral_const_mul]
    congr 1
    funext z
    rw [real_inner_smul_left]
    ring
  -- `q(w) = c|w|²`: the reflection in `(|w|e − w)ᗮ` maps `|w|e` to `w`.
  have hq : ∀ w : Euclid n, q w = q e * ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖‖w‖ • e‖ = ‖w‖ := by rw [norm_smul, he, mul_one, norm_norm]
    obtain ⟨R, hR⟩ : ∃ R : Euclid n ≃ₗᵢ[ℝ] Euclid n, R (‖w‖ • e) = w :=
      ⟨_, Submodule.reflection_sub h1⟩
    calc q w = q (R (‖w‖ • e)) := by rw [hR]
      _ = q (‖w‖ • e) := hq_iso R _
      _ = q e * ‖w‖ ^ 2 := by rw [hq_smul, mul_comm]
  -- `c > 0`: on `ℝⁿ`, `Hⁿ` is Lebesgue measure, and the integrand is `3/16` at `e/2`.
  have hc : 0 < q e := by
    have hcont : Continuous fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      fun_prop
    have hsupp : HasCompactSupport fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz => ?_
      have h1 : 1 < ‖z‖ := by simpa using hz
      have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right h2]
    have hnonneg : 0 ≤ fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 :=
      fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)
    have hx : (fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2) ((1 / 2 : ℝ) • e) ≠ 0 := by
      simp only [norm_smul, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      norm_num
    rw [hq_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg hx
  refine ⟨q e, hc, fun P Q hQ u => ?_⟩
  -- An orthonormal basis of `Q` indexed by `Fin n` gives `L : Q ≃ ℝⁿ`; `ι = L⁻¹` is an isometry
  -- of `ℝⁿ` onto `Q ⊆ ℝᴾ`, so `ι_# Hⁿ = Hⁿ⌞Q`.
  obtain ⟨L, -⟩ : ∃ L : Q ≃ₗᵢ[ℝ] Euclid n, True :=
    ⟨((stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)).repr, trivial⟩
  have hι : Isometry fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    isometry_subtype_coe.comp L.symm.isometry
  have hrange : Set.range (fun z : Euclid n => ((L.symm z : Q) : Euclid P)) =
      (Q : Set (Euclid P)) := by
    ext y
    refine ⟨?_, fun hy => ⟨L ⟨y, hy⟩, by simp⟩⟩
    rintro ⟨z, rfl⟩
    exact (L.symm z).2
  have hemb : MeasurableEmbedding fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    hι.isClosedEmbedding.measurableEmbedding
  have hnorm : ∀ z : Euclid n, ‖((L.symm z : Q) : Euclid P)‖ = ‖z‖ := fun z => L.symm.norm_map z
  -- `⟨u, ι z⟩ = ⟨p_Q u, ι z⟩ = ⟨L(p_Q u), z⟩`.
  have hinner : ∀ z : Euclid n, inner ℝ u ((L.symm z : Q) : Euclid P) =
      inner ℝ (L (Q.orthogonalProjectionOnto u)) z := by
    intro z
    rw [LinearIsometryEquiv.inner_map_eq_flip,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← hrange, ← hι.map_euclideanHausdorffMeasure, hemb.integral_map]
  simp only [hnorm, hinner]
  rw [← hq_def, hq, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
  rfl
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
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
/-- Continuity in the centre of the blow-up integrals of Simon Ch. 3, 1.4: for `f` continuous with
compact support, `r > 0` and `μ` finite on compact sets, `x ↦ ∫ f(η_{x,r}(y)) dμ(y)` is continuous,
`η_{x,r}(y) = r⁻¹(y − x)`.  With `‖f‖ ≤ C` and `tsupport f ⊆ B̄_R(0)`, the integrand vanishes for
`x ∈ B_1(x₀)` and `y ∉ B = B̄_{1+rR}(x₀)`; so near `x₀` it is dominated by `C·1_B`, integrable as
`μ(B) < ∞`, and dominated convergence gives continuity at `x₀`. -/
theorem Submission.continuous_integral_comp_blowUpMap : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μ) := by
  intro P μ hμ f hf hfs r hr
  -- `‖f‖ ≤ C` and `tsupport f ⊆ closedBall 0 R`
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  -- `(x, y) ↦ f (r⁻¹ • (y - x))` is jointly continuous
  have hF : Continuous fun p : Euclid P × Euclid P =>
      f (Poincare.SimonGMT.Chapter03.blowUpMap p.1 r p.2) :=
    hf.comp ((continuous_snd.sub continuous_fst).const_smul r⁻¹)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  -- dominated convergence with the bound `C · 1_B`, `B = closedBall x₀ (1 + r R)`
  refine continuousAt_of_dominated (bound := (closedBall x₀ (1 + r * R)).indicator fun _ => C)
    (Eventually.of_forall fun x => (hF.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    ?_ ?_ (Eventually.of_forall fun y => (hF.comp (Continuous.prodMk_left y)).continuousAt)
  · -- for `x ∈ ball x₀ 1`, `f (r⁻¹ • (y - x)) ≠ 0` forces `‖y - x‖ ≤ r R`, so `y ∈ B`
    filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ closedBall x₀ (1 + r * R)
    · rw [indicator_of_mem hy]
      exact hC _
    · rw [indicator_of_notMem hy]
      refine le_of_eq (norm_eq_zero.2 (by_contra fun h => hy ?_))
      have h1 := hR (subset_tsupport f h)
      rw [mem_closedBall, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, ← dist_eq_norm] at h1
      rw [mem_ball] at hx
      rw [mem_closedBall]
      linarith [dist_triangle y x x₀]
  · -- `C · 1_B` is integrable: `B` is compact, so `μ B < ∞`
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (hμ _ (isCompact_closedBall _ _))

/-- **Simon Ch. 3, 1.4**: if `Hⁿ(M ∩ K) < ∞` for every compact `K`, `f` is continuous with
compact support and `r > 0`, then the blow-up integral `x ↦ ∫_{η_{x,r}(M)} f dHⁿ` is continuous.
It equals `r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`, continuous in `x` because `Hⁿ⌞M` is finite on compact
sets. -/
theorem Submission.continuous_blowUp_image_setIntegral : ∀ (P n : ℕ) (M : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) := by
  intro P n M hM f hf hfs r hr
  -- `Hⁿ⌞M` is finite on compact sets: `(Hⁿ⌞M)(K) = Hⁿ(M ∩ K)`, `K` being closed
  have hμ : ∀ K : Set (Euclid P), IsCompact K → (μHE[n].restrict M) K ≠ ∞ := fun K hK => by
    rw [Measure.restrict_apply hK.isClosed.measurableSet, inter_comm]
    exact hM K hK
  -- change of variables, then continuity of `x ↦ r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`
  exact (continuous_const.mul
    (Submission.continuous_integral_comp_blowUpMap P _ hμ f hf hfs r hr)).congr fun x =>
      (Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul P n M x r hr f).symm
/-- A field of orthogonal projections `p_x = (K x).starProjection` is a.e.-measurable (Borel
σ-algebra of the operator-norm topology) when each quadratic form `x ↦ |p_x u|²` is.  As `p_x` is
self-adjoint and idempotent, `⟪p_x u, w⟫ = (|p_x(u + w)|² − |p_x(u − w)|²)/4`, so the matrix
coefficients `⟪p_x e_a, e_b⟫` are a.e.-measurable, and `p_x = Σ_{a,b} ⟪p_x e_a, e_b⟫ ⟪e_a, ·⟫ e_b`
is a continuous linear function of them. -/
theorem Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K : Euclid P → Submodule ℝ (Euclid P)), (∀ u : Euclid P, AEMeasurable (fun x => ‖(K x).starProjection u‖ ^ 2) μ) → AEMeasurable (fun x => (K x).starProjection) μ := by
  intro P μ K h
  -- by polarization every coefficient `x ↦ ⟪p_x u, w⟫` is a.e.-measurable
  have hcoef : ∀ u w : Euclid P,
      AEMeasurable (fun x => inner ℝ ((K x).starProjection u) w) μ := by
    intro u w
    have key : ∀ x, inner ℝ ((K x).starProjection u) w =
        (‖(K x).starProjection (u + w)‖ ^ 2 - ‖(K x).starProjection (u - w)‖ ^ 2) / 4 := by
      intro x
      have hsym : inner ℝ ((K x).starProjection u) w =
          inner ℝ ((K x).starProjection u) ((K x).starProjection w) := by
        rw [Submodule.inner_starProjection_left_eq_right,
          Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 ((K x).starProjection_apply_mem w)]
      rw [hsym, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
      ring
    simp_rw [key]
    exact ((h (u + w)).sub (h (u - w))).div_const 4
  -- `p_x = Λ (g x)`, `Λ m = ∑ m_{ab} ⟪e_a, ·⟫ e_b`, `g x = (⟪p_x e_a, e_b⟫)_{ab}`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Λ : (Fin P × Fin P → ℝ) → (Euclid P →L[ℝ] Euclid P) := fun m =>
    ∑ ab, m ab • (innerSL ℝ (e ab.1)).smulRight (e ab.2)
  have heq : (fun x => (K x).starProjection) =
      fun x => Λ fun ab => inner ℝ ((K x).starProjection (e ab.1)) (e ab.2) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Λ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Fintype.sum_prod_type]
    calc (K x).starProjection v = (K x).starProjection (∑ a, inner ℝ (e a) v • e a) := by
          rw [e.sum_repr']
      _ = ∑ a, inner ℝ (e a) v • (K x).starProjection (e a) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, inner ℝ (e a) v • ∑ b, inner ℝ (e b) ((K x).starProjection (e a)) • e b := by
          simp only [e.sum_repr']
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [real_inner_comm (e b), smul_smul, smul_smul, mul_comm]
  -- `Λ` is continuous and `g` is a.e.-measurable coordinatewise
  have hΛ : Continuous Λ :=
    continuous_finsetSum _ fun ab _ => (continuous_apply ab).smul continuous_const
  rw [heq]
  exact hΛ.measurable.comp_aemeasurable (AEMeasurable.of_eval fun ab => hcoef _ _)
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

/-- **Simon Ch. 3, 1.4** (measurability of the approximate tangent planes): if `Hⁿ(M ∩ K) < ∞`
for every compact `K` and `Q(x)` is an approximate tangent space of `M` at `Hⁿ⌞M`-a.e. `x`, then
`x ↦ p_{Q(x)} = (Q x).starProjection` is `Hⁿ⌞M`-a.e. strongly measurable.  For `n = 0`,
`Q(x) = 0` a.e.  For `n ≥ 1` and `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`, the blow-up integrals
`x ↦ ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` are continuous and tend a.e. to
`∫_{Q(x)} f_u dHⁿ = c|p_{Q(x)} u|²`, so every `x ↦ |p_{Q(x)} u|²` is a.e.-measurable, and hence
so is `x ↦ p_{Q(x)}`. -/
theorem Submission.cbr_ci_imc_tangent_field_aestronglyMeasurable : ∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) := by
  intro P n M Q hloc htan
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `dim Q(x) = 0`, so `Q(x) = 0` and `p_{Q(x)} = 0` a.e.
    refine (aestronglyMeasurable_const (b := (0 : Euclid P →L[ℝ] Euclid P))).congr ?_
    filter_upwards [htan] with x hx
    have h0 : Q x = ⊥ := Submodule.finrank_eq_zero.1 hx.1
    rw [h0]
    ext v
    simp
  · -- `n ≥ 1`: `∫_{Q'} f_u dHⁿ = c|p_{Q'} u|²` for every `n`-plane `Q'`
    obtain ⟨c, hc, hmom⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
    apply AEMeasurable.aestronglyMeasurable
    apply Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq
    intro u
    -- the test function `f_u ∈ C_c(ℝᴾ)`, vanishing outside the closed unit ball
    set f : Euclid P → ℝ := fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 with hf_def
    have hfc : Continuous f := by
      simp only [hf_def]
      fun_prop
    have hfs : HasCompactSupport f := by
      apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1)
      intro y hy
      simp only [mem_closedBall, dist_zero_right, not_le] at hy
      have h1 : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg y]
      simp [hf_def, max_eq_right h1]
    let F : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨f, hfc⟩, hfs⟩
    -- the radii `r_k = 1/(k + 1) → 0⁺`
    let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hrpos : ∀ k, 0 < r k := fun k => by positivity
    have hr : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hrpos⟩
    -- the blow-up integrals are continuous in `x`, hence measurable
    have hmeas : ∀ k, AEMeasurable (fun x => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (r k) '' M, f y ∂μHE[n]) (μHE[n].restrict M) := fun k =>
      (Submission.continuous_blowUp_image_setIntegral P n M hloc f hfc hfs (r k) (hrpos k)).measurable.aemeasurable
    -- and tend a.e. to `∫_{Q(x)} f_u dHⁿ = c|p_{Q(x)} u|²`
    have hlim : ∀ᵐ x ∂(μHE[n].restrict M), Tendsto (fun k => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (r k) '' M, f y ∂μHE[n]) atTop (𝓝 (c * ‖(Q x).starProjection u‖ ^ 2)) := by
      filter_upwards [htan] with x hx
      rw [← hmom P (Q x) hx.1 u]
      exact (hx.2 F).comp hr
    have h1 : AEMeasurable (fun x => c * ‖(Q x).starProjection u‖ ^ 2) (μHE[n].restrict M) :=
      aemeasurable_of_tendsto_metrizable_ae' hmeas hlim
    refine (h1.const_mul c⁻¹).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
/-- **Simon Ch. 6, 3.1** (integer multiplicity currents): if `Γ(ω) = ∫_M θ ⟨ω, ζ⟩ dHⁿ` with `M`
Borel and countably `n`-rectifiable, `θ > 0` on `M`, `∫_M θ dHⁿ < ∞`, and `Hⁿ`-a.e. on `M` the
density `θ` is an integer and `ζ` orients an approximate tangent space of `M`, then `Γ` is integer
multiplicity.  The bad set is `Hⁿ`-null; removing a measurable null hull `N₀` of it leaves a Borel
carrier `M'' = M \ N₀` on which everything holds pointwise, which has the approximate tangent
spaces of `M` (Ch. 3, 1.4) and `Hⁿ⌞M'' = Hⁿ⌞M`; the multiplicity is `⌊θ⌋₊` on `M''`. -/
theorem Submission.cbr_ci_imc_isIntegerMultiplicity_of_rectifiable : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → CountablyRectifiable n M → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m) → IsIntegerMultiplicity Γ := by
  intro P n Γ M θ ζ hM hrect hθ hζ hpos hint hrep hae
  classical
  set p : Euclid P → Prop := fun x => ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m
  -- the bad set `{x ∈ M | ¬ p x}` is `Hⁿ`-null, and so is its measurable hull `N₀`
  have hbad : μHE[n] {x | x ∈ M ∧ ¬ p x} = 0 := by
    rw [ae_restrict_iff' hM, ae_iff] at hae
    simpa only [not_imp] using hae
  set N₀ := toMeasurable (μHE[n]) {x | x ∈ M ∧ ¬ p x} with hN₀_def
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable _ _
  have hN₀ : μHE[n] N₀ = 0 := by rw [hN₀_def, measure_toMeasurable]; exact hbad
  -- the carrier `M'' = M \ N₀` is Borel, `p` holds on all of it, and `M'' =ᵐ M`
  set M'' := M \ N₀
  have hM''m : MeasurableSet M'' := hM.diff hN₀m
  have hM''sub : M'' ⊆ M := Set.sdiff_subset
  have hgood : ∀ x ∈ M'', p x := by
    intro x hx
    by_contra h
    exact hx.2 (subset_toMeasurable _ _ ⟨hx.1, h⟩)
  have hdiff : μHE[n] (M \ M'') = 0 := by
    refine measure_mono_null (fun x hx => ?_) hN₀
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  have hdiff' : μHE[n] (M'' \ M) = 0 := by
    rw [Set.sdiff_eq_empty.2 hM''sub, measure_empty]
  -- the multiplicity `⌊θ⌋₊` on `M''`, which is `θ` there
  let mult : Euclid P → ℕ := fun x => if x ∈ M'' then ⌊θ x⌋₊ else 0
  have hmult_eq : ∀ x ∈ M'', (mult x : ℝ) = θ x := by
    intro x hx
    obtain ⟨Q, -, -, m, hm⟩ := hgood x hx
    simp [mult, hx, hm]
  have hmult_meas : Measurable mult :=
    Measurable.ite hM''m (Nat.floor_mono.measurable.comp hθ) measurable_const
  have hmult_pos : ∀ x ∈ M'', 0 < mult x := by
    intro x hx
    have h2 := hpos x (hM''sub hx)
    rw [← hmult_eq x hx] at h2
    exact_mod_cast h2
  have hmult_int : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in M'' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K _ _
    apply ne_of_lt
    calc ∫⁻ x in M'' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in M'', (mult x : ℝ≥0∞) ∂μHE[n] := lintegral_mono_set inter_subset_left
      _ = ∫⁻ x in M'', ENNReal.ofReal (θ x) ∂μHE[n] := by
        apply setLIntegral_congr_fun hM''m
        intro x hx
        simp only
        rw [← hmult_eq x hx, ENNReal.ofReal_natCast]
      _ ≤ ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] := lintegral_mono_set hM''sub
      _ < ∞ := hint
  -- `M` and `M''` have the same approximate tangent spaces (Ch. 3, 1.4)
  have horients : ∀ᵐ x ∂(μHE[n].restrict M''), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M'' x Q ∧ IsUnitOrientationOf (ζ x) Q := by
    rw [ae_restrict_iff' hM''m]
    refine Eventually.of_forall fun x hx => ?_
    obtain ⟨Q, hQ, hor, -⟩ := hgood x hx
    exact ⟨Q, (Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n M M'' x Q
      hdiff hdiff').1 hQ, hor⟩
  let R : IMRep (univ : Set (Euclid P)) n :=
    { carrier := M''
      mult := mult
      orient := ζ
      measurableSet_carrier := hM''m
      carrier_subset := subset_univ _
      rectifiable := hrect.mono hM''sub
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hmult_int
      aestronglyMeasurable_orient := hζ.aestronglyMeasurable
      orients := horients }
  -- `R` represents `Γ`: `Hⁿ⌞M = Hⁿ⌞M''` and `mult = θ` on `M''`
  refine ⟨R, fun ω => ?_⟩
  rw [hrep ω]
  have hres : μHE[n].restrict M = μHE[n].restrict M'' :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨hdiff, hdiff'⟩)
  show _ = ∫ x in M'', (mult x : ℝ) * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
  rw [hres]
  refine setIntegral_congr_fun hM''m (fun x hx => ?_)
  simp only [hmult_eq x hx]

/-- **Integer multiplicity criterion** (Simon Ch. 6, 3.1, with Ch. 3, 1.4 and the rectifiability
criterion `(RECT)`, assumed as the first hypothesis).  Let `Γ(ω) = ∫_M θ⟨ω, ζ⟩ dHⁿ` with `M` Borel,
`Hⁿ(M) < ∞`, `θ > 0` on `M` and `∫_M θ dHⁿ < ∞`.  If at `Hⁿ`-a.e. `x ∈ M` the multiplicity `θ(x)` is
a natural number and `ζ(x)` orients an approximate tangent space of `M`, then `Γ` is integer
multiplicity.  At such `x` the plane `Tₓ = approxTangentPlane n M x` is an approximate tangent
space; `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞`, so `x ↦ p_{Tₓ}` is `Hⁿ⌞M`-a.e. strongly measurable and `(RECT)`
makes `M` countably `n`-rectifiable.  The representation is then assembled on a Borel part of `M`
of full measure. -/
theorem Submission.cbr_ci_isIntegerMultiplicity_of_ae_tangent : (∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), MeasurableSet M → μHE[n] M ≠ ∞ → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → CountablyRectifiable n M) → ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → μHE[n] M < ∞ → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m) → IsIntegerMultiplicity Γ := by
  intro hRECT P n Γ M θ ζ hM hfin hθ hζ hpos hint hrep hae
  -- `Tₓ = approxTangentPlane n M x` is an approximate tangent space of `M` at a.e. `x ∈ M`
  have htan : ∀ᵐ x ∂(μHE[n].restrict M),
      HasApproximateTangentSpaceAt n M x (approxTangentPlane n M x) := by
    filter_upwards [hae] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n M x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec
  -- `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞`, so `x ↦ p_{Tₓ}` is a.e. strongly measurable and `(RECT)` applies
  have hloc : ∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞ := fun K _ =>
    ne_top_of_le_ne_top hfin.ne (measure_mono inter_subset_left)
  have hrect : CountablyRectifiable n M :=
    hRECT P n M (approxTangentPlane n M) hM hfin.ne
      (Submission.cbr_ci_imc_tangent_field_aestronglyMeasurable P n M _ hloc htan) htan
  -- assemble the integer multiplicity representation of `Γ` on the rectifiable `M`
  exact Submission.cbr_ci_imc_isIntegerMultiplicity_of_rectifiable P n Γ M θ ζ hM hrect hθ hζ
    hpos hint hrep hae
/-- **Simon, Ch. 1, proof of 2.10, final step** (p. 12): a centrally symmetric set `K ⊆ ℝᵈ`
(`x ∈ K → −x ∈ K`; no measurability or boundedness assumed) has `Lᵈ(K) ≤ ω_d (½ diam K)ᵈ`.
If `diam K = ∞` then `d ≥ 1` (`ℝ⁰` is a point) and the right-hand side is `∞`.  Otherwise
`2‖x‖ = |x − (−x)| ≤ diam K` for `x ∈ K`, so `K` lies in the closed ball of radius `½ diam K`
about `0`, whose measure is `(½ diam K)ᵈ ω_d` by the scaling of the Haar measure `Lᵈ`. -/
theorem Submission.cbr_ci_iso_volume_le_of_neg_mem : ∀ (d : ℕ) (K : Set (Euclid d)), (∀ x ∈ K, -x ∈ K) → volume K ≤ unitBallVolume d * (ediam K / 2) ^ d := by
  intro d K hK
  by_cases htop : ediam K = ∞
  · -- `diam K = ∞` forces `d ≥ 1` (`ℝ⁰` is a point), and then the right-hand side is `∞`
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd (ediam_subsingleton Set.subsingleton_of_subsingleton) (htop ▸ ENNReal.top_ne_zero)
    · have hω : unitBallVolume d ≠ 0 := (measure_ball_pos volume (0 : Euclid d) one_pos).ne'
      rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top, ENNReal.top_pow hd.ne',
        ENNReal.mul_top hω]
      exact le_top
  · -- central symmetry: `2‖x‖ = dist(x, -x) ≤ diam K`, so `K ⊆ B̄(0, diam K / 2)`
    have hr : 0 ≤ diam K / 2 := div_nonneg diam_nonneg zero_le_two
    have hsub : K ⊆ closedBall (0 : Euclid d) (diam K / 2) := by
      intro x hx
      have h := dist_le_diam_of_mem' htop hx (hK x hx)
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two] at h
      rw [mem_closedBall_zero_iff]
      linarith
    -- `Lᵈ(B̄(0, r)) = rᵈ ω_d` (`finrank ℝ ℝᵈ = d`) and `ofReal (diam K / 2) = ediam K / 2`
    have hball : volume (closedBall (0 : Euclid d) (diam K / 2)) =
        ENNReal.ofReal ((diam K / 2) ^ d) * unitBallVolume d := by
      rw [Measure.addHaar_closedBall volume _ hr, finrank_euclideanSpace_fin]
      rfl
    have hrad : ENNReal.ofReal ((diam K / 2) ^ d) = (ediam K / 2) ^ d := by
      rw [ENNReal.ofReal_pow hr, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, diam,
        ENNReal.ofReal_toReal htop]
    calc volume K ≤ volume (closedBall (0 : Euclid d) (diam K / 2)) := measure_mono hsub
      _ = unitBallVolume d * (ediam K / 2) ^ d := by rw [hball, hrad, mul_comm]
/-- Reflection symmetries of the coordinate Steiner symmetrization (Simon, Ch. 1, proof of 2.10).
Write `y[i↦t]` for `y` with `i`-th coordinate replaced by `t`, `R_i(y) = y[i↦-y_i]`,
`A^j_y = {t : y[j↦t] ∈ A}` and `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ L¹(A^j_y)/2}`.  Then (a) `S_j(A)`
is invariant under `R_j`, and (b) if `i ≠ j` and `A` is invariant under `R_i`, so is `S_j(A)`.
For (a), `R_j(y)[j↦t] = y[j↦t]`; for (b), `R_i(y)[j↦t] = R_i(y[j↦t])` and `R_i` is an involution,
so the `j`-slices of `y` and of its reflection agree, while `|(R_i y)_j| = |y_j|`. -/
theorem Submission.cbr_ci_iso_steiner_reflection : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), (∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}) ∧ ∀ i : Fin d, i ≠ j → (∀ x ∈ A, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ A) → ∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A
  refine ⟨fun x hx => ?_, fun i hij hA x hx => ?_⟩
  · -- (a) `R_j(x)[j↦t] = x[j↦t]`, so the `j`-slice is unchanged, and `|(R_j x)_j| = |x_j|`
    simpa using hx
  · -- (b) `R_i` is an involution and commutes with `y ↦ y[j↦t]`, so the `j`-slices of `x` and
    -- `R_i(x)` agree; moreover `(R_i x)_j = x_j` since `i ≠ j`
    have hR : ∀ z : Euclid d, WithLp.toLp 2 (update (WithLp.toLp 2 (update z.ofLp i (-z i))).ofLp i
        (-(WithLp.toLp 2 (update z.ofLp i (-z i))) i)) = z := by
      intro z
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have hcomm : ∀ t : ℝ, WithLp.toLp 2 (update (update x.ofLp i (-x i)) j t) =
        WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp j t)).ofLp i
          (-(WithLp.toLp 2 (update x.ofLp j t)) i)) := by
      intro t
      simp only [update_of_ne hij]
      rw [update_comm hij]
    have hslice : {t : ℝ | WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp i (-x i))).ofLp j t) ∈ A} =
        {t : ℝ | WithLp.toLp 2 (update x.ofLp j t) ∈ A} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [hcomm t]
      constructor
      · intro h
        have h' := hA _ h
        rwa [hR] at h'
      · exact hA _
    have hxj : (WithLp.toLp 2 (update x.ofLp i (-x i))) j = x j := by
      simp [hij.symm]
    show _ ∧ _
    rw [hslice, hxj]
    exact hx
/-- **Steiner symmetrization does not increase the diameter** (Simon 2.10, proof of the
isodiametric inequality).  For compact `A ⊆ ℝᵈ` and `j < d`, write `y[j↦t]` for `y` with its `j`-th
coordinate replaced by `t`, `A^j_y = {t : y[j↦t] ∈ A}`, `λ(y) = L¹(A^j_y)` and
`S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}`; then `ediam S_j(A) ≤ ediam A`.  Each slice `A^j_y` is
compact, so it contains `a_y = inf A^j_y` and `b_y = sup A^j_y`, and `λ(y) ≤ b_y - a_y`.  For
`x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2 ≤ max(b_y - a_x, b_x - a_y)`, and replacing the
`j`-th coordinates of `x, y` by the matching endpoints gives two points of `A` at distance at least
`|x - y|`. -/
theorem Submission.cbr_ci_iso_steiner_ediam_le : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ediam {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} ≤ ediam A := by
  intro d j A hA
  -- (1) every slice `A^j_y` is compact: closed, and contained in the compact image of `A`
  -- under the `j`-th coordinate
  have hslice : ∀ y : Euclid d,
      IsCompact {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
    intro y
    have hf : Continuous fun t : ℝ => WithLp.toLp 2 (Function.update y.ofLp j t) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_const.update j continuous_id)
    refine (hA.image (PiLp.continuous_apply 2 _ j)).of_isClosed_subset
      (hA.isClosed.preimage hf) fun t ht => ⟨_, ht, by simp⟩
  -- (2) a nonempty compact `P ⊆ ℝ` contains `inf P` and `sup P`, and `L¹(P) ≤ sup P - inf P`
  have hlen : ∀ P : Set ℝ, IsCompact P → P.Nonempty →
      sInf P ∈ P ∧ sSup P ∈ P ∧ (volume P).toReal ≤ sSup P - sInf P := by
    intro P hP hne
    refine ⟨hP.sInf_mem hne, hP.sSup_mem hne, ?_⟩
    refine ENNReal.toReal_le_of_le_ofReal
      (sub_nonneg.mpr (csInf_le_csSup hne hP.bddBelow hP.bddAbove)) ?_
    calc volume P ≤ volume (Icc (sInf P) (sSup P)) :=
          measure_mono fun t ht => ⟨csInf_le hP.bddBelow ht, le_csSup hP.bddAbove ht⟩
      _ = ENNReal.ofReal (sSup P - sInf P) := Real.volume_Icc
  -- (3) two-point estimate: replacing the `j`-th coordinates by `a, b` with
  -- `|x_j - y_j| ≤ |a - b|` does not decrease the distance
  have hpt : ∀ (x y : Euclid d) (a b : ℝ), WithLp.toLp 2 (Function.update x.ofLp j a) ∈ A →
      WithLp.toLp 2 (Function.update y.ofLp j b) ∈ A → |x j - y j| ≤ |a - b| →
      edist x y ≤ ediam A := by
    intro x y a b ha hb hab
    refine le_trans ?_ (edist_le_ediam_of_mem ha hb)
    rw [edist_dist, edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    · simp only [Function.update_of_ne hi, le_refl]
  -- (4) for `x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2` is realised by a pair of points of `A`
  refine ediam_le ?_
  rintro x ⟨hxne, hxj⟩ y ⟨hyne, hyj⟩
  obtain ⟨hax, hbx, hlx⟩ := hlen _ (hslice x) hxne
  obtain ⟨hay, hby, hly⟩ := hlen _ (hslice y) hyne
  have hx := abs_le.mp hxj
  have hy := abs_le.mp hyj
  rcases le_total
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A})
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}) with h | h
  · refine hpt x y _ _ hax hby ?_
    rw [abs_sub_comm _ (sSup _)]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
  · refine hpt x y _ _ hbx hay ?_
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
/-- **Simon, Ch. 1, Note after the proof of 2.10** (p. 12): for compact `A ⊆ ℝᵈ` and a coordinate
`j`, the length `y ↦ L¹{t : y[j ↦ t] ∈ A}` of the slice of `A` along the `j`-th coordinate line
through `y` is upper semicontinuous.  Every slice lies in `[-R, R]` (`A ⊆ B_R(0)`), so has finite
length.  Given `L¹(A^j_x) < r`, outer regularity gives an open `U ⊇ A^j_x` with `L¹(U) < r`; the
compact set `C = A ∖ {z : z_j ∈ U}` has closed image under `π z = z[j ↦ 0]`, `π x ∉ π(C)`, and for
`y` in the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` the slice `A^j_y` lies in `U`, so `L¹(A^j_y) < r`. -/
theorem Submission.cbr_ci_iso_slice_length_usc : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) := by
  intro d j A hA
  -- every slice lies in `[-R, R]`, so it has finite length
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (0 : Euclid d)
  have hfin : ∀ y : Euclid d,
      volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ≠ ∞ := by
    intro y
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := -R) (b := R)).ne (measure_mono ?_)
    intro t ht
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j t) : Euclid d) j
    rw [WithLp.ofLp_toLp, Function.update_self, Real.norm_eq_abs] at h1
    exact abs_le.mp (h1.trans (mem_closedBall_zero_iff.mp (hR ht)))
  refine upperSemicontinuous_iff.mpr fun x => upperSemicontinuousAt_iff.mpr fun r hr => ?_
  -- outer regularity: an open `U` around the slice through `x` with `L¹(U) < r`
  obtain ⟨U, hxU, hUo, hUr⟩ := Set.exists_isOpen_lt_of_lt
    {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} (ENNReal.ofReal r)
    ((ENNReal.lt_ofReal_iff_toReal_lt (hfin x)).mpr hr)
  -- the projection `z ↦ z[j ↦ 0]` and the compact part of `A` off `{z : z_j ∈ U}`
  let proj : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hproj : Continuous proj :=
    (PiLp.continuous_toLp 2 _).comp
      ((continuous_update j).comp ((PiLp.continuous_ofLp 2 _).prodMk continuous_const))
  have hC : IsCompact (A \ {z : Euclid d | z.ofLp j ∈ U}) :=
    hA.diff (hUo.preimage (PiLp.continuous_apply 2 _ j))
  -- `π x ∉ π(C)`: a point of `C` over `π x` would put its `j`-th coordinate in the slice at `x`
  have hx : proj x ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := by
    rintro ⟨z, ⟨hzA, hzU⟩, hzx⟩
    have h : Function.update z.ofLp j 0 = Function.update x.ofLp j 0 := by
      simpa only [proj, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hzx
    have hz : WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) = z := by
      calc WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j))
          = WithLp.toLp 2 (Function.update (Function.update x.ofLp j 0) j (z.ofLp j)) := by
            rw [Function.update_idem]
        _ = z := by rw [← h, Function.update_idem, Function.update_eq_self, WithLp.toLp_ofLp]
    exact hzU (hxU (show WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) ∈ A by
      rw [hz]; exact hzA))
  -- on the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` every slice lies in `U`
  filter_upwards [((hC.image hproj).isClosed.isOpen_compl.preimage hproj).mem_nhds hx] with y hy
  have hy' : proj y ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := hy
  have hyU : {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ⊆ U := by
    intro t ht
    by_contra htU
    refine hy' ⟨WithLp.toLp 2 (Function.update y.ofLp j t), ⟨ht, ?_⟩, ?_⟩
    · show (WithLp.toLp 2 (Function.update y.ofLp j t)).ofLp j ∉ U
      rwa [WithLp.ofLp_toLp, Function.update_self]
    · simp only [proj, Function.update_idem]
  exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono hyU).trans_lt hUr)
/-- **Steiner symmetrization of a compact set is compact** (Simon Ch. 1, the Note after the proof
of 2.10: `S_j(A)` is compact because the slice length is upper semicontinuous).  Let `A ⊆ ℝ^d` be
compact, `A^j_y = {t : y[j ↦ t] ∈ A}` and `λ(y) = L¹(A^j_y)`.  If `λ` is upper semicontinuous,
then `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}` is compact: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` for
`π z = z[j ↦ 0]`, `{y : |y_j| ≤ λ(y)/2}` is a superlevel set of the upper semicontinuous
`λ − 2|y_j|`, and `S_j(A) ⊆ closedBall(0, 3R)` whenever `A ⊆ closedBall(0, R)`. -/
theorem Submission.cbr_ci_iso_steiner_isCompact : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) → IsCompact {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A hA hlen
  -- Step 1: `π z = z[j ↦ 0]` is continuous, and `π z = π y` forces `y[j ↦ z_j] = z`
  let π : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hπ : Continuous π :=
    (PiLp.continuous_toLp 2 _).comp ((PiLp.continuous_ofLp 2 _).update j continuous_const)
  have hπ_eq : ∀ y z : Euclid d, π z = π y →
      WithLp.toLp 2 (Function.update y.ofLp j (z j)) = z := by
    intro y z h
    ext i
    by_cases hi : i = j
    · subst hi
      simp
    · have := congrArg (fun w : Euclid d => w i) h
      simp only [π, Function.update_of_ne hi] at this ⊢
      exact this.symm
  -- Step 2: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` is closed, `π(A)` being compact
  have hN : IsClosed
      {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty} := by
    convert (hA.image hπ).isClosed.preimage hπ using 1
    ext y
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ht, by simp [π]⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z j, by rw [mem_ofPred_eq, hπ_eq y z h]; exact hz⟩
  -- Step 3: `{y : 0 ≤ λ(y) − 2|y_j|}` is closed, `λ − 2|y_j|` being upper semicontinuous
  have hM : IsClosed {y : Euclid d | 0 ≤
      (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal + -(2 * |y j|)} :=
    (hlen.add ((PiLp.continuous_apply 2 _ j).abs.const_mul 2).neg.upperSemicontinuous)
      |>.isClosed_preimage 0
  -- Step 4: `S_j(A)` is the intersection of these two closed sets
  have hS : IsClosed {y : Euclid d |
      {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧
        |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
    convert hN.inter hM using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr Iff.rfl ⟨fun h => by linarith, fun h => by linarith⟩
  -- Step 5: `S_j(A) ⊆ closedBall(0, 3R)` when `A ⊆ closedBall(0, R)`
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded hS
    ((isBounded_closedBall (x := (0 : Euclid d)) (r := 3 * R)).subset ?_)
  rintro y ⟨⟨t, ht⟩, hy⟩
  rw [mem_closedBall_zero_iff]
  -- every `s ∈ A^j_y` has `|s| ≤ ‖y[j ↦ s]‖ ≤ R`
  have hnorm : ∀ s : ℝ, WithLp.toLp 2 (Function.update y.ofLp j s) ∈ A → |s| ≤ R := by
    intro s hs
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j s)) j
    have h2 := mem_closedBall_zero_iff.1 (hR hs)
    simp only [Function.update_self, Real.norm_eq_abs] at h1
    linarith
  -- hence `A^j_y ⊆ [−R, R]` and `λ(y) ≤ 2R`
  have hR0 : 0 ≤ R := (abs_nonneg t).trans (hnorm t ht)
  have hvol : (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal ≤ 2 * R := by
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    calc volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}
        ≤ volume (Icc (-R) R) := measure_mono fun s hs => abs_le.1 (hnorm s hs)
      _ = ENNReal.ofReal (2 * R) := by rw [Real.volume_Icc]; ring_nf
  -- `y − y[j ↦ t] = (y_j − t) e_j`
  have hdiff : ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ = |y j - t| := by
    have : y - WithLp.toLp 2 (Function.update y.ofLp j t) = EuclideanSpace.single j (y j - t) := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [hi]
    rw [this, PiLp.norm_single, Real.norm_eq_abs]
  have hz : ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ ≤ R := mem_closedBall_zero_iff.1 (hR ht)
  -- Step 6: `‖y‖ ≤ ‖y[j ↦ t]‖ + |y_j − t| ≤ R + |y_j| + |t| ≤ 3R`, using `|y_j| ≤ λ(y)/2 ≤ R`
  calc ‖y‖ = ‖WithLp.toLp 2 (Function.update y.ofLp j t) +
        (y - WithLp.toLp 2 (Function.update y.ofLp j t))‖ := by rw [add_sub_cancel]
    _ ≤ ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ +
        ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ := norm_add_le _ _
    _ ≤ R + (|y j| + |t|) := by
        rw [hdiff]
        gcongr
        exact abs_sub _ _
    _ ≤ 3 * R := by linarith [hnorm t ht]
/-- **Cavalieri's principle along a coordinate direction** (Simon Ch. 1, proof of 2.10: Steiner
symmetrization keeps Lebesgue measure "by Fubini").  If measurable `S, A ⊆ ℝᵈ` have line slices
`{t : y[j↦t] ∈ S}`, `{t : y[j↦t] ∈ A}` of equal `L¹`-measure through every `y`, then
`Lᵈ(S) = Lᵈ(A)`.  With `d = n + 1`, `φ(t, z) = Fin.insertNth j t z` is measure preserving from
`L¹ ⊗ Lⁿ` to `Lᵈ`; its fibre over `z` is the slice through `φ(0, z)`, and Tonelli
(`Measure.prod_apply_symm`) integrates the equal slice measures over `z`. -/
theorem Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (S A : Set (Euclid d)), MeasurableSet S → MeasurableSet A → (∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ S} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}) → volume S = volume A := by
  intro d j S A hS hA hslice
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
    -- `φ(t, z) = Fin.insertNth j t z`, measure preserving from `L¹ ⊗ Lⁿ` to `Lᵈ`
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    let φ : ℝ × (Fin n → ℝ) → Euclid (n + 1) := fun p => WithLp.toLp 2 (e.symm p)
    have hφ : MeasurePreserving φ volume volume :=
      (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
    -- the fibre of `φ` over `z` is the coordinate slice through `φ(0, z)`
    have hfibre (B : Set (Euclid (n + 1))) (z : Fin n → ℝ) :
        (fun t => φ (t, z)) ⁻¹' B =
          {t : ℝ | WithLp.toLp 2 (Function.update (φ (0, z)).ofLp j t) ∈ B} := by
      ext t
      change WithLp.toLp 2 (j.insertNth t z) ∈ B ↔
        WithLp.toLp 2 (Function.update (j.insertNth 0 z) j t) ∈ B
      rw [Fin.update_insertNth]
    -- Tonelli: `Lᵈ(B) = (L¹ ⊗ Lⁿ)(φ⁻¹ B) = ∫⁻ z, L¹(fibre of φ⁻¹ B over z)`
    have hvol (B : Set (Euclid (n + 1))) (hB : MeasurableSet B) :
        volume B = ∫⁻ z : Fin n → ℝ, volume ((fun t => φ (t, z)) ⁻¹' B) :=
      (hφ.measure_preimage hB.nullMeasurableSet).symm.trans
        (Measure.prod_apply_symm (hB.preimage hφ.measurable))
    rw [hvol S hS, hvol A hA]
    refine lintegral_congr fun z => ?_
    rw [hfibre S z, hfibre A z]
    exact hslice (φ (0, z))
/-- Steiner symmetrization in direction `j` keeps the length of every line slice: for compact
`A ⊆ ℝᵈ` and `y ∈ ℝᵈ`, `L¹{t | y[j↦t] ∈ S_j(A)} = L¹(B)` with `B = {t | y[j↦t] ∈ A}`.  Each
point `y[j↦t]` of the line has `j`-th coordinate `t` and slice `B`, so the left set is
`{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = L¹(B)`.  It is empty if `B = ∅` and `[-ℓ/2, ℓ/2]` otherwise, of
length `ℓ`, which is finite because `B` lies in the compact projection `π_j(A)`. -/
theorem Submission.cbr_ci_iso_svol_steiner_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ {x : Euclid d | {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}.Nonempty ∧ |x j| ≤ (volume {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}).toReal / 2}} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
  intro d j A hA y
  -- `B = A^j_y = {s | y[j↦s] ∈ A}`
  obtain ⟨B, hB⟩ : ∃ B : Set ℝ, {s : ℝ | WithLp.toLp 2 (update y.ofLp j s) ∈ A} = B :=
    ⟨_, rfl⟩
  -- steps 1–2: `(y[j↦t])_j = t` and `(y[j↦t])[j↦s] = y[j↦s]` (`WithLp.ofLp_toLp` is `rfl`), so
  -- `A^j_{y[j↦t]} = B` and the left set is `{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = (L¹ B).toReal`
  simp only [mem_ofPred_eq, update_idem, update_self, hB]
  -- step 3: `B ⊆ π_j(A)`, which is compact, so `L¹(B) < ∞`
  have hBfin : volume B ≠ ∞ := by
    have hπ : IsCompact ((fun x : Euclid d => x j) '' A) := hA.image (PiLp.continuous_apply 2 _ j)
    refine (measure_lt_top_of_subset ?_ hπ.measure_lt_top.ne).ne
    rintro s hs
    rw [← hB] at hs
    exact ⟨_, hs, update_self j s y.ofLp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  -- step 4: if `B = ∅`, the left set is empty
  · simp only [Set.not_nonempty_empty, false_and, ofPred_false]
  -- step 5: otherwise it is `[-ℓ/2, ℓ/2]`, of measure `ofReal ℓ = L¹(B)`
  · have hIcc : {t : ℝ | B.Nonempty ∧ |t| ≤ (volume B).toReal / 2} =
        Icc (-((volume B).toReal / 2)) ((volume B).toReal / 2) := by
      ext t
      rw [mem_ofPred_eq, mem_Icc, ← abs_le, and_iff_right hBne]
    rw [hIcc, Real.volume_Icc, sub_neg_eq_add, add_halves, ENNReal.ofReal_toReal hBfin]

/-- **Simon Ch. 1, proof of 2.10 (p. 12): Steiner symmetrization preserves Lebesgue measure.**
Let `A ⊆ ℝ^d` be compact, `j ∈ Fin d`, `A^j_y = {t : y[j↦t] ∈ A}`.  If the Steiner symmetral
`S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ ½ L¹(A^j_y)}` is measurable, then `L^d(S_j(A)) = L^d(A)`, "by
Fubini": each line in direction `e_j` meets `S_j(A)` in `∅` or a centred segment of length
`L¹(A^j_y)`, hence in a set of the same `L¹`-measure as its trace on the measurable set `A`, and
Cavalieri's principle along `e_j` compares the volumes. -/
theorem Submission.cbr_ci_iso_steiner_volume_eq : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → MeasurableSet {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} → volume {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} = volume A := by
  intro d j A hA hS
  exact Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq d j _ A hS hA.measurableSet
    (Submission.cbr_ci_iso_svol_steiner_slice_volume_eq d j A hA)
/-- Iterated coordinate Steiner symmetrization (Simon, Ch. 1, proof of 2.10): every compact
`A ⊆ ℝ^d` has a compact replacement `K` with `L^d(K) = L^d(A)`, `ediam K ≤ ediam A` and `-x ∈ K`
for all `x ∈ K`.  Write `y[i↦t]` for `y` with `i`-th coordinate replaced by `t`,
`R_k(y) = y[k↦-y_k]`, `B^i_y = {t : y[i↦t] ∈ B}`, `S_i(B) = {y : B^i_y ≠ ∅, |y_i| ≤ L¹(B^i_y)/2}`.
By induction over finite `F ⊆ Fin d` there is a compact `K_F` with the measure of `A`, diameter at
most `ediam A` and `R_k(K_F) ⊆ K_F` for `k ∈ F`: for `i ∉ F`, `S_i(K_F)` is compact, has the same
measure and no larger diameter (sibling lemmas), is `R_i`-invariant since `R_i(y)[i↦t] = y[i↦t]`,
and stays `R_k`-invariant for `k ∈ F` since `R_k(y)[i↦t] = R_k(y[i↦t])` and `R_k` is an involution.
For `K = K_{Fin d}`, flipping the coordinates of `x ∈ K` one at a time shows `-x ∈ K`. -/
theorem Submission.cbr_ci_iso_exists_symmetric_replacement : ∀ (d : ℕ) (A : Set (Euclid d)), IsCompact A → ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧ ediam K ≤ ediam A ∧ ∀ x ∈ K, -x ∈ K := by
  intro d A hA
  -- Step 1: for every finite set `F` of coordinates there is a compact `K_F` with the measure of
  -- `A`, diameter at most `ediam A`, and invariant under `R_k` for every `k ∈ F`
  have hF : ∀ F : Finset (Fin d), ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧
      ediam K ≤ ediam A ∧
      ∀ k ∈ F, ∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp k (-x k)) ∈ K := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨A, hA, rfl, le_rfl, by simp⟩
    | insert i F hi ih =>
      -- replace `K' = K_F` by its Steiner symmetrization `S_i(K')` in the new direction `i`
      obtain ⟨K', hK', hvol', hdiam', hsym'⟩ := ih
      have hS := Submission.cbr_ci_iso_steiner_isCompact d i K' hK'
        (Submission.cbr_ci_iso_slice_length_usc d i K' hK')
      refine ⟨_, hS,
        (Submission.cbr_ci_iso_steiner_volume_eq d i K' hK' hS.measurableSet).trans hvol',
        (Submission.cbr_ci_iso_steiner_ediam_le d i K' hK').trans hdiam', fun k hk x hx => ?_⟩
      rcases Finset.mem_insert.1 hk with rfl | hkF
      · -- `R_k(x)[k↦t] = x[k↦t]`, so the `k`-slice is unchanged, and `|(R_k x)_k| = |x_k|`
        simpa using hx
      · -- `k ≠ i`: `R_k` is an involution preserving `K'` with `R_k(x)[i↦t] = R_k(x[i↦t])`, so
        -- `x` and `R_k(x)` have the same `i`-slice of `K'`, and `(R_k x)_i = x_i`
        have hki : k ≠ i := by
          rintro rfl
          exact hi hkF
        have hR := hsym' k hkF
        have hinv : ∀ z : Euclid d, WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update z.ofLp k (-z k))).ofLp k
            (-(WithLp.toLp 2 (Function.update z.ofLp k (-z k))) k)) = z := by
          intro z
          ext m
          by_cases hm : m = k
          · subst hm
            simp
          · simp [hm]
        have hcomm : ∀ t : ℝ,
            WithLp.toLp 2 (Function.update (Function.update x.ofLp k (-x k)) i t) =
              WithLp.toLp 2 (Function.update (WithLp.toLp 2 (Function.update x.ofLp i t)).ofLp k
                (-(WithLp.toLp 2 (Function.update x.ofLp i t)) k)) := by
          intro t
          simp only [Function.update_of_ne hki]
          rw [Function.update_comm hki]
        have hslice : {t : ℝ | WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x.ofLp k (-x k))).ofLp i t) ∈ K'} =
            {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp i t) ∈ K'} := by
          ext t
          simp only [Set.mem_ofPred_eq]
          rw [hcomm t]
          constructor
          · intro h
            have h' := hR _ h
            rwa [hinv] at h'
          · exact hR _
        have hxi : (WithLp.toLp 2 (Function.update x.ofLp k (-x k))) i = x i := by
          simp [hki.symm]
        show _ ∧ _
        rw [hslice, hxi]
        exact hx
  -- Step 4: `K = K_{Fin d}` is invariant under every coordinate reflection
  obtain ⟨K, hK, hvol, hdiam, hsym⟩ := hF Finset.univ
  refine ⟨K, hK, hvol, hdiam, fun x hx => ?_⟩
  -- Step 5: `x^G ∈ K` for every finite `G`, where `x^G` flips the coordinates of `x` in `G`
  have hG : ∀ G : Finset (Fin d), WithLp.toLp 2 (fun k => if k ∈ G then -x k else x k) ∈ K := by
    intro G
    induction G using Finset.induction_on with
    | empty => simpa using hx
    | insert i G hi ih =>
      -- `x^{insert i G} = R_i(x^G)` because `i ∉ G`
      convert hsym i (Finset.mem_univ i) _ ih using 1
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hi]
      · simp [hk]
  -- `x^{Fin d} = -x`
  convert hG Finset.univ using 1
  ext k
  simp

/-- **Simon 2.10** (isodiametric inequality, Ch. 1, p. 11): `Lᵈ(A) ≤ ω_d (diam A / 2)ᵈ` for every
`A ⊆ ℝᵈ`.  If `ediam A = ∞` then `d ≠ 0` (subsets of `ℝ⁰` are subsingletons) and the right side is
`ω_d · ∞ = ∞`, as `ω_d > 0`.  Otherwise the closure `Ā` is compact, `ediam Ā = ediam A` and
`Lᵈ(A) ≤ Lᵈ(Ā)`; a centrally symmetric compact `K` with `Lᵈ(K) = Lᵈ(Ā)` and `ediam K ≤ ediam Ā`
satisfies the bound, and the bound is monotone in the diameter. -/
theorem Submission.cbr_ci_iso_volume_le_ediam_pow : ∀ (d : ℕ) (A : Set (Euclid d)), volume A ≤ unitBallVolume d * (ediam A / 2) ^ d := by
  intro d A
  by_cases hA : ediam A = ⊤
  · -- unbounded `A`: then `d ≠ 0`, and the right side is `ω_d · ∞ = ∞`
    have hd : d ≠ 0 := by
      rintro rfl
      exact ENNReal.zero_ne_top ((ediam_subsingleton Set.subsingleton_of_subsingleton).symm.trans hA)
    have hω : unitBallVolume d ≠ 0 := (measure_ball_pos volume (0 : Euclid d) one_pos).ne'
    have h2 : ediam A / 2 = ⊤ := by
      rw [hA]
      exact ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top
    rw [h2, ENNReal.top_pow hd, ENNReal.mul_top hω]
    exact le_top
  · -- bounded `A`: pass to the compact closure, then to a centrally symmetric replacement
    have hc : IsCompact (closure A) := (isBounded_iff_ediam_ne_top.2 hA).isCompact_closure
    obtain ⟨K, -, hKA, hKd, hKs⟩ :=
      Submission.cbr_ci_iso_exists_symmetric_replacement d (closure A) hc
    rw [ediam_closure] at hKd
    calc volume A ≤ volume (closure A) := measure_mono subset_closure
      _ = volume K := hKA.symm
      _ ≤ unitBallVolume d * (ediam K / 2) ^ d := Submission.cbr_ci_iso_volume_le_of_neg_mem d K hKs
      _ ≤ unitBallVolume d * (ediam A / 2) ^ d := by gcongr

/-- Lebesgue measure on `ℝ^d` is at most `(ω_d / 2^d) • μH[d]` (Simon Ch. 1, "Completion of the
proof of 2.9", pp. 12–13, in Mathlib's unnormalised `μH[d]`, whose weight is `diam^d`).  Put
`c = ω_d / 2^d`; `c ≠ 0, ∞` since `0 < ω_d < ∞`.  The isodiametric inequality
`L^d(s) ≤ ω_d (diam s / 2)^d = c · diam(s)^d` gives `c⁻¹ L^d(s) ≤ diam(s)^d` for every `s`, so
`c⁻¹ • L^d ≤ μH[d]` (`Measure.le_hausdorffMeasure`: cover by sets `C_k` of small diameter,
`c⁻¹ L^d(B) ≤ Σ c⁻¹ L^d(C_k) ≤ Σ diam(C_k)^d`).  Multiplying back by `c` gives
`L^d ≤ c • μH[d]` setwise. -/
theorem Submission.cbr_ci_iso_volume_le_smul_hausdorff : ∀ (d : ℕ), (volume : Measure (Euclid d)) ≤ (unitBallVolume d / 2 ^ d) • (μH[(d : ℝ)] : Measure (Euclid d)) := by
  intro d
  -- Step 1: `c = ω_d / 2^d` is neither `0` nor `∞`
  set c : ℝ≥0∞ := unitBallVolume d / 2 ^ d with hc
  have hω0 : unitBallVolume d ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Euclid d) one_pos).ne'
  have hωtop : unitBallVolume d ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hω0, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩
  have hctop : c ≠ ∞ := ENNReal.div_ne_top hωtop (pow_ne_zero d two_ne_zero)
  -- Step 2: the isodiametric inequality gives `c⁻¹ L^d(s) ≤ diam(s)^d` for every `s`
  have hdiam : ∀ s : Set (Euclid d), c⁻¹ * volume s ≤ ediam s ^ d := by
    intro s
    have hiso : volume s ≤ c * ediam s ^ d :=
      calc volume s ≤ unitBallVolume d * (ediam s / 2) ^ d :=
            Submission.cbr_ci_iso_volume_le_ediam_pow d s
        _ = c * ediam s ^ d := by
            rw [hc, div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
            ring
    calc c⁻¹ * volume s ≤ c⁻¹ * (c * ediam s ^ d) := by gcongr
      _ = ediam s ^ d := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  -- Step 3: `ν = c⁻¹ • L^d ≤ μH[d]`; the bound is needed only for sets of diameter `≤ 1`
  have hν : c⁻¹ • (volume : Measure (Euclid d)) ≤ μH[(d : ℝ)] := by
    refine Measure.le_hausdorffMeasure (d : ℝ) _ 1 one_pos fun s _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
    exact hdiam s
  -- Step 4: `L^d(s) = c · ν(s) ≤ c · μH[d](s)` for every set `s`
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  calc volume s = c * (c⁻¹ * volume s) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
    _ ≤ c * μH[(d : ℝ)] s := by
        gcongr
        simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.1 hν s

/-- `Hⁿ = μHE[n]` is dominated by Simon's normalisation `ωₙ (diam/2)ⁿ` (Simon, Ch. 1, 2.1–2.2 and
the completion of the proof of 2.9): `μHE[n] ≤ (ωₙ/2ⁿ) • μH[n]` on every `ℝᴾ`.  By definition
`μHE[n] = c • μH[n]` with `c = addHaarScalarFactor volume μH[n]` on `ℝⁿ`, so `volume = c • μH[n]`
on `ℝⁿ`.  On the unit cube `K` of `ℝⁿ`, `volume K = 1` gives `c · μH[n](K) = 1`, which forces
`0 < μH[n](K) < ∞`; with `volume K ≤ (ωₙ/2ⁿ) μH[n](K)` (isodiametric inequality) this gives
`c ≤ ωₙ/2ⁿ`, whence `μHE[n](s) = c · μH[n](s) ≤ (ωₙ/2ⁿ) μH[n](s)` for every `s ⊆ ℝᴾ`. -/
theorem Submission.cbr_ci_euclideanHausdorff_le_isodiametric : ∀ (P n : ℕ), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) := by
  intro P n
  -- `c` is the constant with `μHE[n] = c • μH[n]` on every space, so `volume = c • μH[n]` on `ℝⁿ`
  obtain ⟨c, hc⟩ : ∃ c : NNReal,
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)] = c :=
    ⟨_, rfl⟩
  have hvol : (volume : Measure (Euclid n)) = c • (μH[(n : ℝ)] : Measure (Euclid n)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_def,
      hc]
  -- `volume ≤ (ωₙ/2ⁿ) • μH[n]` on `ℝⁿ` (isodiametric inequality, completion of the proof of 2.9)
  have hiso : (volume : Measure (Euclid n)) ≤
      (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid n)) :=
    Submission.cbr_ci_iso_volume_le_smul_hausdorff n
  -- the unit cube `K` of `ℝⁿ` has `volume K = 1`, so `c · μH[n](K) = 1` and `0 < μH[n](K) < ∞`
  set K : Set (Euclid n) := parallelepiped (stdOrthonormalBasis ℝ (Euclid n))
  have hK : (c : ℝ≥0∞) * μH[(n : ℝ)] K = 1 := by
    rw [← Measure.coe_nnreal_smul_apply, ← hvol]
    exact (stdOrthonormalBasis ℝ (Euclid n)).volume_parallelepiped
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hK
    exact zero_ne_one hK
  have hK0 : μH[(n : ℝ)] K ≠ 0 := by
    intro h
    rw [h, mul_zero] at hK
    exact zero_ne_one hK
  have hKtop : μH[(n : ℝ)] K ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hc0] at hK
    exact ENNReal.top_ne_one hK
  -- hence `c ≤ ωₙ/2ⁿ`
  have hcle : (c : ℝ≥0∞) ≤ unitBallVolume n / 2 ^ n := by
    have h := Measure.le_iff'.1 hiso K
    rw [hvol, Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul] at h
    exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).1 h
  -- conclusion on `ℝᴾ`: `μHE[n](s) = c · μH[n](s) ≤ (ωₙ/2ⁿ) · μH[n](s)`
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.euclideanHausdorffMeasure_def, hc, Measure.coe_nnreal_smul_apply,
    Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcle zero_le

/-- **Almost every point of `M` is good** (Simon Ch. 1, 3.26(1), and Lebesgue points of `θζ` by
Besicovitch differentiation).  Let `M ⊆ ℝᴾ` be Borel with `Hⁿ(M) < ∞`, `θ` Borel with `θ > 0` on
`M` and `∫_M θ dHⁿ < ∞`, and `ζ` strongly measurable with `|⟨α, ζ(x)⟩| ≤ |α|`.  Then for
`Hⁿ`-a.e. `a ∈ M`: (i) `limsup_{r↓0} Hⁿ(M ∩ B̄_r(a)) / (ωₙrⁿ) ≤ 1`, and (ii)
`(ωₙrⁿ)⁻¹ ∫_{M ∩ B̄_r(a)} ‖θ(x)ζ(x) − θ(a)ζ(a)‖ dHⁿ(x) → 0` as `r ↓ 0`.  Vitali's covering lemma
with the finite-tail argument and the isodiametric normalisation `Hⁿ ≤ (ωₙ/2ⁿ) μH[n]` give the
sharp density comparison `t Hⁿ(A) ≤ μ(ℝᴾ)` (Simon 3.3, 3.5); outer regularity of `Hⁿ⌞M` turns it
into (i).  The field `τ = θζ` is bounded by a multiple of `θ`, hence in `L¹(Hⁿ⌞M)`, and Besicovitch
differentiation for closed balls makes its Lebesgue error, normalised by `Hⁿ(M ∩ B̄_r(a))`, tend to
`0`; by (i) the same holds with the normalisation `ωₙrⁿ`, which is (ii). -/
theorem Submission.dtc_bc_tc_cl_ci_ae_good_points : ∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → μHE[n] M < ∞ → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → ∀ᵐ a ∂(μHE[n].restrict M), limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 ∧ Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) := by
  -- Step 3 (density comparison; Simon Ch. 1, 3.3 with the finite tail 3.5): under the
  -- isodiametric normalisation `Hⁿ ≤ (ωₙ/2ⁿ) μH[n]`, if `0 < t < limsup_{r↓0} μ(B̄_r(x))/(ωₙrⁿ)`
  -- at every `x ∈ A`, then `t Hⁿ(A) ≤ μ(ℝᴾ)`
  have gp_density_comparison : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (t : ℝ≥0∞), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) → 0 < t → (∀ x ∈ A, t < limsup (fun r : ℝ => μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → t * μHE[n] A ≤ μ univ := by
    intro P n μ A t hIB ht hA
    -- Step 1: trivial cases
    rcases eq_or_ne (μ univ) ∞ with hμ | hμ
    · rw [hμ]; exact le_top
    rcases A.eq_empty_or_nonempty with hAe | ⟨x₀, hx₀⟩
    · simp [hAe]
    have htop : t ≠ ∞ := ne_top_of_lt (hA x₀ hx₀)
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    set ω := unitBallVolume n with hωdef
    have htω0 : t * ω ≠ 0 := mul_ne_zero ht.ne' hω0
    have htωtop : t * ω ≠ ∞ := ENNReal.mul_ne_top htop hωtop
    -- Step 2: fineness
    have hfine : ∀ x ∈ A, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ρ < η ∧
        t * ω * ENNReal.ofReal ρ ^ n < μ (closedBall x ρ) := by
      intro x hx η hη
      have hfreq : ∃ᶠ r in 𝓝[>] (0:ℝ), t < μ (closedBall x r) / (ω * ENNReal.ofReal (r ^ n)) :=
        frequently_lt_of_lt_limsup (by isBoundedDefault) (hA x hx)
      obtain ⟨ρ, hρ, hρη⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hη)).exists
      refine ⟨ρ, hρη.1, hρη.2, ?_⟩
      have hw0 : ω * ENNReal.ofReal (ρ ^ n) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hρη.1 n)).ne'
      have hwtop : ω * ENNReal.ofReal (ρ ^ n) ≠ ∞ := ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl hw0) (Or.inl hwtop)] at hρ
      rw [← ENNReal.ofReal_pow hρη.1.le, mul_assoc]
      exact hρ
    -- Steps 3–8: for every scale δ and slack ε a cheap countable cover of A
    set D : ℝ≥0∞ := 2 ^ n * (μ univ / (t * ω)) with hD
    have hcover : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ u : Set (Euclid P × ℝ), u.Countable ∧ ∃ c : u → Set (Euclid P),
          (∀ b, ediam (c b) ≤ ENNReal.ofReal (5 * δ)) ∧ A ⊆ ⋃ b, c b ∧
          ∑' b, ediam (c b) ^ (n : ℝ) ≤ D + ε := by
      intro δ hδ ε hε
      set T : Set (Euclid P × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 < δ / 2 ∧
        t * ω * ENNReal.ofReal p.2 ^ n < μ (closedBall p.1 p.2)} with hT
      -- Step 3: Vitali selection with the intersection-and-radius property
      obtain ⟨u, huT, hdisj, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
        (fun p : Euclid P × ℝ => closedBall p.1 p.2) T (fun p => p.2) 2 one_lt_two
        (fun p hp => hp.2.1.le) (δ / 2) (fun p hp => hp.2.2.1.le)
        (fun p hp => nonempty_closedBall.2 hp.2.1.le)
      -- Step 5: countability
      have hucount : u.Countable := by
        apply hdisj.countable_of_nonempty_interior
        intro p hp
        refine ⟨p.1, interior_mono ball_subset_closedBall ?_⟩
        rw [isOpen_ball.interior_eq]
        exact mem_ball_self (huT hp).2.1
      have : Countable u := hucount.to_subtype
      refine ⟨u, hucount, ?_⟩
      -- Step 6: packing
      set s : u → ℝ≥0∞ := fun b => ENNReal.ofReal (b : Euclid P × ℝ).2 ^ n with hs
      have hpack : t * ω * ∑' b, s b ≤ μ univ := by
        rw [← ENNReal.tsum_mul_left]
        calc ∑' b : u, t * ω * s b
            ≤ ∑' b : u, μ (closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2) :=
              ENNReal.tsum_le_tsum fun b => (huT b.2).2.2.2.le
          _ = μ (⋃ b ∈ u, closedBall b.1 b.2) :=
              (measure_biUnion hucount hdisj fun b _ => measurableSet_closedBall).symm
          _ ≤ μ univ := measure_mono (subset_univ _)
      have hS : ∑' b, s b ≤ μ univ / (t * ω) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl htω0) (Or.inl htωtop), mul_comm]; exact hpack
      have hSfin : ∑' b, s b ≠ ∞ := ne_top_of_le_ne_top (ENNReal.div_ne_top hμ htω0) hS
      -- Step 8 (tail): a finite subfamily whose complement has small total cost
      have htail := ENNReal.tendsto_tsum_compl_atTop_zero hSfin
      have h10top : (10 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have h10ne : (10 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      obtain ⟨F, hF⟩ := (htail.eventually (gt_mem_nhds (ENNReal.div_pos hε h10top))).exists
      classical
      refine ⟨fun b => if b ∈ F then closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
        else closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2), ?_, ?_, ?_⟩
      · -- diameters
        intro b
        have hb := huT b.2
        have hρ0 : 0 < (b : Euclid P × ℝ).2 := hb.2.1
        have hρδ : (b : Euclid P × ℝ).2 < δ / 2 := hb.2.2.1
        dsimp only
        split_ifs
        · refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
          rw [mem_closedBall] at hy hz
          linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
        · refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
          rw [mem_closedBall] at hy hz
          linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
      · -- Step 7 (Simon 3.5): the tail enlargements cover what the finite part misses
        intro x hx
        by_cases hxK : x ∈ ⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
        · obtain ⟨b, hbF, hxb⟩ := mem_iUnion₂.1 hxK
          exact mem_iUnion.2 ⟨b, by simp only [hbF, ite_true]; exact hxb⟩
        · have hKc : IsClosed (⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2) :=
            isClosed_biUnion_finset fun b _ => isClosed_closedBall
          obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl x hxK
          obtain ⟨ρ, hρ0, hρη, hρμ⟩ := hfine x hx (min (η / 2) (δ / 2)) (by positivity)
          have haT : (x, ρ) ∈ T := ⟨hx, hρ0, lt_of_lt_of_le hρη (min_le_right _ _), hρμ⟩
          obtain ⟨b, hbu, ⟨z, hz1, hz2⟩, hle⟩ := hmeet (x, ρ) haT
          have hzx : dist z x ≤ ρ := hz1
          have hzb : dist z b.1 ≤ b.2 := hz2
          have hle' : ρ ≤ 2 * b.2 := hle
          have hbF : (⟨b, hbu⟩ : u) ∉ F := by
            intro hbF
            have hzK : z ∈ ⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2 :=
              mem_biUnion hbF hz2
            have hzball : z ∈ ball x η := by
              rw [mem_ball]
              have : ρ < η / 2 := lt_of_lt_of_le hρη (min_le_left _ _)
              linarith
            exact hηball hzball hzK
          refine mem_iUnion.2 ⟨⟨b, hbu⟩, ?_⟩
          simp only [hbF, ite_false]
          rw [mem_closedBall]
          have hb0 : 0 < b.2 := (huT hbu).2.1
          calc dist x b.1 ≤ dist x z + dist z b.1 := dist_triangle _ _ _
            _ ≤ ρ + b.2 := by rw [dist_comm] at hzx; linarith
            _ ≤ 5 * b.2 := by linarith
      · -- Step 8: the cost of the cover
        have hterm : ∀ b : u, ediam (if b ∈ F then closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
            else closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2)) ^ (n : ℝ)
            ≤ 2 ^ n * s b + {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b := by
          intro b
          have hb0 : 0 < (b : Euclid P × ℝ).2 := (huT b.2).2.1
          rw [ENNReal.rpow_natCast]
          split_ifs with hbF
          · have hd : ediam (closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2)
                ≤ 2 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
              calc _ ≤ ENNReal.ofReal (2 * (b : Euclid P × ℝ).2) :=
                    ediam_le_of_forall_dist_le fun y hy z hz => by
                      rw [mem_closedBall] at hy hz
                      linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
                _ = 2 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
                    rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
            calc _ ≤ (2 * ENNReal.ofReal (b : Euclid P × ℝ).2) ^ n := by gcongr
              _ = 2 ^ n * s b := by rw [mul_pow]
              _ ≤ _ := le_self_add
          · have hd : ediam (closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2))
                ≤ 10 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
              calc _ ≤ ENNReal.ofReal (10 * (b : Euclid P × ℝ).2) :=
                    ediam_le_of_forall_dist_le fun y hy z hz => by
                      rw [mem_closedBall] at hy hz
                      linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
                _ = 10 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
                    rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
            have hind : {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b = 10 ^ n * s b :=
              indicator_of_mem (show b ∈ {b : u | b ∉ F} from hbF) _
            calc _ ≤ (10 * ENNReal.ofReal (b : Euclid P × ℝ).2) ^ n := by gcongr
              _ = 10 ^ n * s b := by rw [mul_pow]
              _ ≤ _ := by rw [hind]; exact le_add_self
        calc ∑' b, _ ≤ ∑' b : u, (2 ^ n * s b + {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b) :=
              ENNReal.tsum_le_tsum hterm
          _ = 2 ^ n * ∑' b, s b + 10 ^ n * ∑' b : {b : u // b ∉ F}, s b := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← tsum_subtype {b : u | b ∉ F}
                (fun b => 10 ^ n * s b), ENNReal.tsum_mul_left]
              rfl
          _ ≤ D + ε := by
              refine add_le_add (by rw [hD]; exact mul_le_mul_right hS _) ?_
              calc 10 ^ n * ∑' b : {b : u // b ∉ F}, s b ≤ 10 ^ n * (ε / 10 ^ n) :=
                    mul_le_mul_right hF.le _
                _ = ε := ENNReal.mul_div_cancel h10ne h10top
    -- Step 9: the Hausdorff measure bound
    have hH : μH[(n : ℝ)] A ≤ D := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hε' : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
      have hk : ∀ k : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧ ∃ c : u → Set (Euclid P),
          (∀ b, ediam (c b) ≤ ENNReal.ofReal (5 * (1 / ((k : ℝ) + 1)))) ∧ A ⊆ ⋃ b, c b ∧
          ∑' b, ediam (c b) ^ (n : ℝ) ≤ D + ε := fun k => hcover _ (by positivity) _ hε'
      choose u hu c hc1 hc2 hc3 using hk
      have : ∀ k, Countable (u k) := fun k => (hu k).to_subtype
      have hlim := Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P) (ι := fun k => u k)
        (n : ℝ) A (l := atTop) (fun k : ℕ => ENNReal.ofReal (5 * (1 / ((k : ℝ) + 1))))
        (by
          rw [show (0 : ℝ≥0∞) = ENNReal.ofReal (5 * 0) by simp]
          exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 5))
        c (Eventually.of_forall hc1) (Eventually.of_forall hc2)
      exact hlim.trans (liminf_le_of_frequently_le' (Frequently.of_forall hc3))
    -- Step 10: the isodiametric normalisation
    have hle : μHE[n] A ≤ ω / 2 ^ n * μH[(n : ℝ)] A := by
      have := Measure.le_iff'.1 hIB A
      rwa [Measure.smul_apply, smul_eq_mul] at this
    have h2 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2top : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    calc t * μHE[n] A ≤ t * (ω / 2 ^ n * D) := by gcongr; exact hle.trans (by gcongr)
      _ = μ univ := by
        rw [hD, ← mul_assoc (ω / 2 ^ n), ENNReal.div_mul_cancel h2 h2top, ← mul_assoc,
          ENNReal.mul_div_cancel htω0 htωtop]
  -- Step 4 (upper density bound; Simon Ch. 1, 3.26(1)): for `Hⁿ⌞M`-a.e. `a`,
  -- `limsup_{r↓0} Hⁿ(M ∩ B̄_r(a))/(ωₙrⁿ) ≤ 1`
  have gp_upper_density_le_one : ∀ (P n : ℕ) (M : Set (Euclid P)), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) → MeasurableSet M → μHE[n] M < ∞ → ∀ᵐ a ∂(μHE[n].restrict M), limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 := by
    intro P n M hIB hM hMfin
    set Θ : Euclid P → ℝ≥0∞ := fun x => limsup (fun r : ℝ => μHE[n] (M ∩ closedBall x r) /
      (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) with hΘ
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict M) :=
      isFiniteMeasure_restrict.2 hMfin.ne
    -- Step 2: each superlevel set `A_t`, `1 < t < ∞`, is null
    have key : ∀ t : ℝ≥0∞, 1 < t → t ≠ ∞ → μHE[n] {x | x ∈ M ∧ t < Θ x} = 0 := by
      intro t ht1 httop
      set A := {x | x ∈ M ∧ t < Θ x} with hAdef
      have hAM : A ⊆ M := fun x hx => hx.1
      have hAfin : μHE[n] A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAM) hMfin).ne
      have hle : t * μHE[n] A ≤ μHE[n] A := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        have hlt : ((μHE[n] : Measure (Euclid P)).restrict M) A < μHE[n] A + ε := by
          rw [Measure.restrict_apply' hM, inter_eq_left.2 hAM]
          exact ENNReal.lt_add_right hAfin (by simpa using hε.ne')
        obtain ⟨U, hUA, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt A _ hlt
        rw [Measure.restrict_apply hUo.measurableSet] at hU
        have h := gp_density_comparison P n ((μHE[n] : Measure (Euclid P)).restrict (M ∩ U)) A t hIB
          (zero_lt_one.trans ht1) (fun x hx => ?_)
        · rw [Measure.restrict_apply_univ, inter_comm] at h
          exact h.trans hU.le
        · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hUo x (hUA hx)
          have heq : (fun r : ℝ => ((μHE[n] : Measure (Euclid P)).restrict (M ∩ U)) (closedBall x r) /
                (unitBallVolume n * ENNReal.ofReal (r ^ n))) =ᶠ[𝓝[>] 0]
              (fun r : ℝ => μHE[n] (M ∩ closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) := by
            have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < η :=
              nhdsWithin_le_nhds (gt_mem_nhds hη)
            filter_upwards [hsmall] with r hr
            rw [Measure.restrict_apply measurableSet_closedBall]
            have hsub : closedBall x r ⊆ U := (closedBall_subset_ball hr).trans hball
            congr 2
            ext y
            constructor
            · rintro ⟨hy, hyM, -⟩
              exact ⟨hyM, hy⟩
            · rintro ⟨hyM, hy⟩
              exact ⟨hy, hyM, hsub hy⟩
          rw [limsup_congr heq]
          exact hx.2
      by_contra hA0
      have : μHE[n] A * 1 < μHE[n] A * t := ENNReal.mul_lt_mul_right hA0 hAfin ht1
      rw [mul_one, mul_comm] at this
      exact absurd hle (not_le.2 this)
    -- Step 3: the exceptional set is a countable union of null sets
    have hcover : {x | x ∈ M ∧ 1 < Θ x} ⊆
        ⋃ k : ℕ, {x | x ∈ M ∧ 1 + ((k : ℝ≥0∞) + 1)⁻¹ < Θ x} := by
      intro x hx
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hx.2).ne'
      refine mem_iUnion.2 ⟨k, hx.1, ?_⟩
      have h1 : ((k : ℝ≥0∞) + 1)⁻¹ < Θ x - 1 :=
        lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hk
      rw [add_comm]
      exact lt_tsub_iff_right.1 h1
    have hnull : μHE[n] {x | x ∈ M ∧ 1 < Θ x} = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun k => key _ ?_ ?_)
      · exact ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2
          (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩))
      · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by simp)⟩
    -- Step 4: conclusion
    rw [ae_iff, Measure.restrict_apply' hM]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨hx.2, not_le.1 hx.1⟩
  -- Steps 5–6 (Lebesgue points by Besicovitch differentiation): for `Hⁿ⌞M`-a.e. `a` at
  -- which `M` has finite upper density, the Lebesgue error of `τ` normalised by `ωₙrⁿ` tends to `0`
  have gp_lebesgue_error_tendsto : ∀ (P n : ℕ) (M : Set (Euclid P)) (τ : Euclid P → MultiVector P n), MeasurableSet M → μHE[n] M < ∞ → StronglyMeasurable τ → ∫⁻ x in M, ‖τ x‖ₑ ∂μHE[n] < ∞ → ∀ᵐ a ∂(μHE[n].restrict M), limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) < ∞ → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) := by
    intro P n M τ hM hMfin hτ hfin
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict M) := isFiniteMeasure_restrict.2 hMfin.ne
    have hL := (Besicovitch.vitaliFamily ((μHE[n] : Measure (Euclid P)).restrict M)).ae_tendsto_lintegral_enorm_sub_div
      (E := MultiVector P n) (f := τ) (Integrable.locallyIntegrable ⟨hτ.aestronglyMeasurable, hfin⟩)
    filter_upwards [hL] with a ha hlim
    have hball := ha.comp (Besicovitch.tendsto_filterAt ((μHE[n] : Measure (Euclid P)).restrict M) a)
    -- rewrite the Besicovitch quotient in terms of `M ∩ closedBall a r`
    have hq : Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) /
        μHE[n] (M ∩ closedBall a r)) (𝓝[>] 0) (𝓝 0) := by
      refine hball.congr fun r => ?_
      simp only [Function.comp_apply]
      rw [Measure.restrict_restrict measurableSet_closedBall,
        Measure.restrict_apply measurableSet_closedBall, inter_comm]
    -- the density quotient is eventually bounded by a finite constant
    obtain ⟨C, hC1, hC2⟩ := exists_between hlim
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < C :=
      eventually_lt_of_limsup_lt hC1
    have hupper : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))
          ≤ C * ((∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / μHE[n] (M ∩ closedBall a r)) := by
      filter_upwards [hev] with r hr
      set I := ∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]
      set m := μHE[n] (M ∩ closedBall a r)
      set w := unitBallVolume n * ENNReal.ofReal (r ^ n)
      by_cases hm0 : m = 0
      · have hI : I = 0 := setLIntegral_measure_zero _ _ hm0
        simp [hI]
      · have hmtop : m ≠ ∞ := (lt_of_le_of_lt (measure_mono inter_subset_left) hMfin).ne
        have hIw : I / w = I / m * (m / w) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc m⁻¹,
            ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
        rw [hIw, mul_comm C]
        gcongr
    have hCq : Tendsto (fun r : ℝ => C * ((∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) /
        μHE[n] (M ∩ closedBall a r))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hq (Or.inr hC2.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCq
      (Eventually.of_forall fun _ => zero_le) hupper
  -- Steps 1–2 (bounded field, integrability): `θζ` is strongly measurable and
  -- `∫_M ‖θζ‖ dμ < ∞`
  have gp_weighted_field_l1 : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μ < ∞ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → StronglyMeasurable (fun x => θ x • ζ x) ∧ ∫⁻ x in M, ‖θ x • ζ x‖ₑ ∂μ < ∞ := by
    intro P n μ M θ ζ hM hθ hζ hpos hint hbound
    refine ⟨hθ.stronglyMeasurable.smul hζ, ?_⟩
    classical
    set C : ℝ := Real.sqrt ((Fintype.card (Fin n → Fin P) : ℝ)) with hC
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    -- Step 1: the Euclidean coefficient norm is dominated by `C` times the operator norm
    have hcov : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖ := by
      intro α
      have hterm : ∀ I : Fin n → Fin P,
          (if StrictMono I then (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
            ≤ ‖α‖ ^ 2 := by
        intro I
        split_ifs
        · have h1 : ‖α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))‖ ≤ ‖α‖ := by
            have := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))
            simpa using this
          have h2 : |α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
            simpa [Real.norm_eq_abs] using h1
          nlinarith [abs_nonneg (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))),
            sq_abs (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i)))]
        · positivity
      have hsum : (∑ I : Fin n → Fin P,
          if StrictMono I then (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
            ≤ (Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2 := by
        calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := Finset.sum_le_sum fun I _ => hterm I
          _ = _ := by simp
      unfold covectorEuclideanNorm
      calc Real.sqrt _ ≤ Real.sqrt ((Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2) :=
            Real.sqrt_le_sqrt hsum
        _ = C * ‖α‖ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    -- Step 2: `‖ζ x‖ ≤ C`
    have hζC : ∀ x, ‖ζ x‖ ≤ C := by
      intro x
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun α => ?_
      rw [Real.norm_eq_abs]
      exact (hbound x α).trans (hcov α)
    -- Step 3: the lintegral bound
    calc ∫⁻ x in M, ‖θ x • ζ x‖ₑ ∂μ ≤ ∫⁻ x in M, ENNReal.ofReal C * ENNReal.ofReal (θ x) ∂μ := by
          refine setLIntegral_mono' hM fun x hx => ?_
          have hθx : 0 < θ x := hpos x hx
          have hn : ‖θ x • ζ x‖ ≤ C * θ x := by
            refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
            rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
              abs_of_pos hθx]
            calc θ x * |ζ x α| ≤ θ x * (C * ‖α‖) := by
                  gcongr
                  exact (hbound x α).trans (hcov α)
              _ = C * θ x * ‖α‖ := by ring
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hC0]
          exact ENNReal.ofReal_le_ofReal hn
      _ = ENNReal.ofReal C * ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μ :=
          lintegral_const_mul _ hθ.ennreal_ofReal
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  intro P n M θ ζ hM hMfin hθ hζ hpos hint hbound
  -- (i): upper density at most `1`, from the isodiametric normalisation `Hⁿ ≤ (ωₙ/2ⁿ) μH[n]`
  have h1 := gp_upper_density_le_one P n M
    (Submission.cbr_ci_euclideanHausdorff_le_isodiametric P n) hM hMfin
  -- `τ = θζ` is strongly measurable with `∫_M ‖τ‖ dHⁿ < ∞`
  obtain ⟨hτm, hτf⟩ := gp_weighted_field_l1 P n μHE[n] M θ ζ hM hθ hζ hpos hint hbound
  -- Lebesgue points of `τ`, normalised by `ωₙrⁿ` where the upper density of `M` is finite
  have h2 := gp_lebesgue_error_tendsto P n M (fun x => θ x • ζ x) hM hMfin hτm hτf
  -- (ii): where (i) holds the upper density is finite
  filter_upwards [h1, h2] with a ha1 ha2
  exact ⟨ha1, ha2 (ha1.trans_lt ENNReal.one_lt_top)⟩
/-- **Pairing error against a constant multivector** (step 2 of the proof of
`Submission.cbr_ci_bl_constant_vector_limit`, for a single measure).  Let `w` be a continuous
covector field with `‖w‖ ≤ A` that vanishes outside `B̄_R = closedBall 0 R`, and suppose
`E = A ∫_{B̄_R} ‖τ − ζ₀‖ dν'` is finite.  The error `g(x) = ⟨w(x), τ(x) − ζ₀⟩` is a.e. strongly
measurable, being the continuous evaluation of `τ − ζ₀` at `w`.  By `le_opENorm`, and since
`w = 0` off `B̄_R`, `‖g(x)‖ ≤ 1_{B̄_R}(x) A ‖τ(x) − ζ₀‖`.  Hence `∫ ‖g‖ dν' ≤ E < ∞` and `g` is
integrable.  As `⟨w, τ⟩ = ⟨w, ζ₀⟩ + g`, the difference of the two integrals is `∫ g dν'`, and
`|∫ g dν'| ≤ ∫ ‖g‖ dν' ≤ E`. -/
theorem Submission.cbr_ci_bl_cvl_pairing_error_le : ∀ (P n : ℕ) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n) (A R : ℝ), AEStronglyMeasurable τ ν' → Continuous w → (∀ x, ‖w x‖ ≤ A) → (∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0) → Integrable (fun x => ζ₀ (w x)) ν' → ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' ≠ ∞ → |∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν'| ≤ (ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν').toReal := by
  intro P n ν' τ ζ₀ w A R hτ hw hwA hw0 hζ hE
  -- the error integrand `g(x) = ⟨w(x), τ(x) − ζ₀⟩`
  set g : Euclid P → ℝ := fun x => (τ x - ζ₀) (w x) with hg
  -- Step 1: `g` is a.e. strongly measurable (continuous evaluation of `τ − ζ₀` at `w`)
  have hgm : AEStronglyMeasurable g ν' :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : MultiVector P n) v => L v)
      isBoundedBilinearMap_apply.continuous (hτ.sub aestronglyMeasurable_const)
      hw.aestronglyMeasurable
  -- Step 2: `‖g(x)‖ₑ ≤ 1_{B̄_R}(x) A ‖τ(x) − ζ₀‖ₑ`
  have hpt : ∀ x, ‖g x‖ₑ ≤
      (closedBall (0 : Euclid P) R).indicator (fun x => ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : Euclid P) R
    · rw [indicator_of_mem hx, mul_comm]
      calc ‖g x‖ₑ ≤ ‖τ x - ζ₀‖ₑ * ‖w x‖ₑ := (τ x - ζ₀).le_opENorm (w x)
        _ ≤ ‖τ x - ζ₀‖ₑ * ENNReal.ofReal A := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hwA x)
    · rw [indicator_of_notMem hx, hg]
      simp [hw0 x hx]
  -- Step 3: `∫⁻ ‖g‖ₑ ≤ A ∫⁻_{B̄_R} ‖τ − ζ₀‖ₑ = E < ∞`
  have hlint : ∫⁻ x, ‖g x‖ₑ ∂ν' ≤
      ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' := by
    calc ∫⁻ x, ‖g x‖ₑ ∂ν'
        ≤ ∫⁻ x, (closedBall (0 : Euclid P) R).indicator
            (fun x => ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ) x ∂ν' := lintegral_mono hpt
      _ = ∫⁻ x in closedBall (0 : Euclid P) R, ENNReal.ofReal A * ‖τ x - ζ₀‖ₑ ∂ν' :=
          lintegral_indicator measurableSet_closedBall _
      _ = ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 4: `g` is integrable
  have hgi : Integrable g ν' := ⟨hgm, hasFiniteIntegral_iff_enorm.2 (hlint.trans_lt hE.lt_top)⟩
  -- Step 5: `⟨w, τ⟩ = ⟨w, ζ₀⟩ + g`, so the difference of the integrals is `∫ g`
  have hint : ∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν' = ∫ x, g x ∂ν' := by
    have hsplit : (fun x => τ x (w x)) = fun x => ζ₀ (w x) + g x := by
      funext x
      simp [hg]
    rw [hsplit, integral_add hζ hgi, add_sub_cancel_left]
  -- Step 6: `|∫ g| ≤ (∫⁻ ‖g‖ₑ).toReal ≤ E.toReal`
  rw [hint, ← Real.norm_eq_abs, ← toReal_enorm]
  calc (‖∫ x, g x ∂ν'‖ₑ).toReal ≤ (∫⁻ x, ‖g x‖ₑ ∂ν').toReal :=
        ENNReal.toReal_mono (hlint.trans_lt hE.lt_top).ne (enorm_integral_le_lintegral_enorm _)
    _ ≤ _ := ENNReal.toReal_mono hE hlint

/-- **Pairings with a compactly supported form converge.**  Let `νₖ, ν` be measures on `ℝᴾ`, each
`νₖ` finite on compact sets, with `∫ f dνₖ → ∫ f dν` for every continuous compactly supported `f`,
and let `τₖ : ℝᴾ → Λₙ` be `νₖ`-a.e. strongly measurable with `∫_{B̄_R(0)} ‖τₖ − ζ₀‖ dνₖ → 0` for
every `R > 0`.  Then `∫ τₖ(w) dνₖ → ∫ ζ₀(w) dν` for every continuous compactly supported
`w : ℝᴾ → Λⁿ`.  Take `A ≥ ‖w‖` and `R > 0` with `w = 0` off `B̄_R(0)`.  Then `f = ζ₀ ∘ w` is
continuous with compact support, hence `νₖ`-integrable; the error estimate
`cbr_ci_bl_cvl_pairing_error_le` gives `|∫ τₖ(w) dνₖ − ∫ f dνₖ| ≤ A ∫_{B̄_R(0)} ‖τₖ − ζ₀‖ dνₖ → 0`,
and `∫ f dνₖ → ∫ f dν` by hypothesis. -/
theorem Submission.cbr_ci_bl_cvl_pairing_tendsto : ∀ (P n : ℕ) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (τs : ℕ → Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → νs k K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(νs k)) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ k, AEStronglyMeasurable (τs k) (νs k)) → (∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0)) → Continuous w → HasCompactSupport w → Tendsto (fun k => ∫ x, τs k x (w x) ∂(νs k)) atTop (𝓝 (∫ x, ζ₀ (w x) ∂ν)) := by
  intro P n νs ν τs ζ₀ w hfin hconv hmeas hlim hw hwc
  -- Step 1: `‖w‖ ≤ A`, and `w = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨A, hA⟩ := hw.bounded_above_of_compact_support hwc
  obtain ⟨R₀, hR₀⟩ := hwc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  obtain ⟨R, hR, hsupp⟩ : ∃ R : ℝ, 0 < R ∧ tsupport w ⊆ closedBall (0 : Euclid P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left R₀ 1))⟩
  have hzero : ∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxw => hx (hsupp hxw)
  -- Step 2: `f = ζ₀ ∘ w` is continuous with compact support, hence `νₖ`-integrable
  have hfc : Continuous fun x => ζ₀ (w x) := ζ₀.continuous.comp hw
  have hfs : HasCompactSupport fun x => ζ₀ (w x) := hwc.comp_left (map_zero ζ₀)
  have hfi : ∀ k, Integrable (fun x => ζ₀ (w x)) (νs k) := fun k => by
    have : IsFiniteMeasureOnCompacts (νs k) := ⟨fun K hK => hfin k K hK⟩
    exact hfc.integrable_of_hasCompactSupport hfs
  -- Step 3: `eₖ = ofReal A · δₖ(R) → 0`; eventually `eₖ < 1`, so `eₖ ≠ ∞`; `eₖ.toReal → 0`
  have he : Tendsto (fun k => ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (hlim R hR) (Or.inr ENNReal.ofReal_ne_top)
  have he1 : ∀ᶠ k in atTop, ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k) < 1 :=
    (tendsto_order.1 he).2 1 one_pos
  have heR : Tendsto (fun k => (ENNReal.ofReal A *
      ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  -- Step 4: `pairing_error` bounds `dₖ = ∫ τₖ(w) dνₖ − ∫ f dνₖ` by `eₖ.toReal`, so `dₖ → 0`
  have hd : Tendsto (fun k => ∫ x, τs k x (w x) ∂(νs k) - ∫ x, ζ₀ (w x) ∂(νs k)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ heR
    filter_upwards [he1] with k hk
    rw [Real.norm_eq_abs]
    exact Submission.cbr_ci_bl_cvl_pairing_error_le P n (νs k) (τs k) ζ₀ w A R (hmeas k) hw hA
      hzero (hfi k) (ne_top_of_lt hk)
  -- Step 5: `∫ τₖ(w) dνₖ = dₖ + ∫ f dνₖ → 0 + ∫ f dν`
  have hlim' := hd.add (hconv (fun x => ζ₀ (w x)) hfc hfs)
  rw [zero_add] at hlim'
  exact hlim'.congr fun k => sub_add_cancel _ _
/-- **Mass bound for a current `L¹`-close to a constant `n`-vector** (step 4 of the weak
convergence and limsup mass bound for such currents, used for blow-ups of cycles).  Let
`X ∈ 𝒟ₙ(ℝᴾ)` satisfy `X(ω) = ∫ ⟨ω(x), τ(x)⟩ dν'(x)` for every test form, with `ν'` finite on
compact sets, and let `|⟨α, ζ₀⟩| ≤ s|α|` and `‖α‖ ≤ B|α|` for all covectors `α`.  Then for open
`G ⊆ B̄_R(0)`, `M_G(X) ≤ s ν'(G) + B ∫_{B̄_R(0)} ‖τ − ζ₀‖ dν'`.  Fix an admissible `ω`
(`tsupport ω ⊆ G`, `|ω| ≤ 1`); it vanishes off `G ⊆ B̄_R(0)` and `‖ω‖ ≤ B`, so the pairing-error
estimate bounds `X(ω) − ∫ ⟨ω, ζ₀⟩ dν'` by the error term `E`, while `⟨ω, ζ₀⟩ ≤ s 1_G` pointwise
gives `∫ ⟨ω, ζ₀⟩ dν' ≤ s ν'(G)`.  As `ν'(G) < ∞`, `X(ω) ≤ s ν'(G) + E` in `[0, ∞]`. -/
theorem Submission.cbr_ci_bl_cvl_massOn_le : ∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) n) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (s B R : ℝ) (G : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν' K < ∞) → AEStronglyMeasurable τ ν' → 0 ≤ s → (∀ α : Covector (Euclid P) n, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → 0 ≤ B → (∀ α : Covector (Euclid P) n, ‖α‖ ≤ B * covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, X ω = ∫ x, τ x ((ω : DifferentialForm (Euclid P) n) x) ∂ν') → IsOpen G → G ⊆ closedBall (0 : Euclid P) R → X.massOn G ≤ ENNReal.ofReal s * ν' G + ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' := by
  intro P n X ν' τ ζ₀ s B R G hfin hτ hs hζ₀ hB hBnorm hrep hG hGR
  have : IsFiniteMeasureOnCompacts ν' := ⟨hfin⟩
  -- Step 1: `ν'(G) ≤ ν'(B̄_R(0)) < ∞`
  have hGfin : ν' G ≠ ∞ :=
    ((measure_mono hGR).trans_lt (hfin _ (isCompact_closedBall 0 R))).ne
  -- Step 2: `M_G(X)` is the supremum of `X(ω)` over admissible `ω`; fix one, and dispose of the
  -- case `E = ∞`
  refine sSup_le ?_
  rintro r ⟨ω, ⟨hωG, hω1⟩, rfl⟩
  show ENNReal.ofReal (X ω) ≤ _
  by_cases hEtop : ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' = ∞
  · rw [hEtop, add_top]
    exact le_top
  -- Step 3: `w = ω̂` is continuous with compact support, vanishes off `G ⊆ B̄_R(0)`, and
  -- `‖w‖ ≤ B|w| ≤ B`; hence `ζ₀ ∘ w` is `ν'`-integrable
  have hwcont : Continuous (ω : DifferentialForm (Euclid P) n) := ω.2.1.1.continuous
  have hwcs : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.2.1.2
  rw [hrep ω]
  generalize (ω : DifferentialForm (Euclid P) n) = w at hwcont hwcs hωG hω1 ⊢
  have hw0 : ∀ x, x ∉ G → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hωG h)
  have hwR : ∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0 := fun x hx =>
    hw0 x fun h => hx (hGR h)
  have hwB : ∀ x, ‖w x‖ ≤ B := fun x =>
    (hBnorm (w x)).trans ((mul_le_mul_of_nonneg_left (hω1 x) hB).trans (mul_one B).le)
  have hfint : Integrable (fun x => ζ₀ (w x)) ν' :=
    (ζ₀.continuous.comp hwcont).integrable_of_hasCompactSupport (hwcs.comp_left (map_zero ζ₀))
  -- Step 4: the pairing-error estimate gives `X(ω) ≤ ∫ ζ₀(w) dν' + E`
  have herr := Submission.cbr_ci_bl_cvl_pairing_error_le P n ν' τ ζ₀ w B R hτ hwcont hwB hwR
    hfint hEtop
  -- Step 5: `ζ₀(w) ≤ s 1_G` pointwise, so `∫ ζ₀(w) dν' ≤ s ν'(G)`
  have hGm : MeasurableSet G := hG.measurableSet
  have hmain : ∫ x, ζ₀ (w x) ∂ν' ≤ s * (ν' G).toReal := by
    refine (integral_mono hfint ((integrable_indicator_iff hGm).2 (integrableOn_const hGfin))
      fun x => ?_).trans_eq ?_
    · show ζ₀ (w x) ≤ G.indicator (fun _ => s) x
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx]
        exact (le_abs_self _).trans ((hζ₀ (w x)).trans
          ((mul_le_mul_of_nonneg_left (hω1 x) hs).trans (mul_one s).le))
      · rw [indicator_of_notMem hx, hw0 x hx, map_zero]
    · rw [integral_indicator_const _ hGm, smul_eq_mul, measureReal_def, mul_comm]
  -- Step 6: `ofReal(X(ω)) ≤ ofReal(s ν'(G)) + ofReal(E) = ofReal(s) ν'(G) + E`
  generalize ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' = E
    at hEtop herr ⊢
  calc ENNReal.ofReal (∫ x, τ x (w x) ∂ν')
      ≤ ENNReal.ofReal (s * (ν' G).toReal + E.toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith [(abs_sub_le_iff.1 herr).1])
    _ ≤ ENNReal.ofReal (s * (ν' G).toReal) + ENNReal.ofReal E.toReal := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal s * ν' G + E := by
        rw [ENNReal.ofReal_mul hs, ENNReal.ofReal_toReal hGfin, ENNReal.ofReal_toReal hEtop]
/-- **A limsup bound on a compact set through its closed thickenings** (steps 5 and 6 of the proof
of `Submission.cbr_ci_bl_constant_vector_limit`, where `a_k = μ_k(K)` and `c = s`).  Write
`K_r = cthickening r K`; it is compact.  For `r > 0`, since `c ≠ ∞`,
`limsup_k c ν_k(K_r) = c limsup_k ν_k(K_r) ≤ c ν(K_r)`.  Given `d > c ν(K_r)`, pick
`c ν(K_r) < b < d`; eventually `c ν_k(K_r) < b` and `v_k < d − b`, so `a_k ≤ b + (d − b) = d`.
Hence `limsup_k a_k ≤ c ν(K_r)` for every `r > 0`.  As `K` is closed and `ν(K_1) < ∞`,
`ν(K_r) → ν(K)` as `r ↓ 0`, and letting `r ↓ 0` gives `limsup_k a_k ≤ c ν(K)`. -/
theorem Submission.cbr_ci_bl_cvl_limsup_le_of_cthickening : ∀ (P : ℕ) (a : ℕ → ℝ≥0∞) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (c : ℝ≥0∞) (K : Set (Euclid P)), IsCompact K → c ≠ ∞ → (∀ K' : Set (Euclid P), IsCompact K' → ν K' < ∞) → (∀ K' : Set (Euclid P), IsCompact K' → limsup (fun k => νs k K') atTop ≤ ν K') → (∀ r : ℝ, 0 < r → ∃ v : ℕ → ℝ≥0∞, Tendsto v atTop (𝓝 0) ∧ ∀ k, a k ≤ c * νs k (cthickening r K) + v k) → limsup a atTop ≤ c * ν K := by
  intro P a νs ν c K hK hc hνK hlim hv
  -- Steps 1–2: `limsup a ≤ c ν(K_r)` for every `r > 0`, where `K_r = cthickening r K`
  have hr : ∀ r : ℝ, 0 < r → limsup a atTop ≤ c * ν (cthickening r K) := by
    intro r hr
    obtain ⟨v, hv0, hav⟩ := hv r hr
    -- Step 1: `limsup_k c ν_k(K_r) = c limsup_k ν_k(K_r) ≤ c ν(K_r)`, as `K_r` is compact
    have hmain : limsup (fun k => c * νs k (cthickening r K)) atTop ≤ c * ν (cthickening r K) := by
      rw [ENNReal.limsup_const_mul_of_ne_top hc]
      gcongr
      exact hlim (cthickening r K) hK.cthickening
    -- Step 2: for `d > c ν(K_r)` pick `c ν(K_r) < b < d`; eventually
    -- `a_k ≤ c ν_k(K_r) + v_k ≤ b + (d - b) = d`
    refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
    obtain ⟨b, hb, hbd⟩ := exists_between hd
    have h1 : ∀ᶠ k in atTop, c * νs k (cthickening r K) < b :=
      eventually_lt_of_limsup_lt (hmain.trans_lt hb)
    have h2 : ∀ᶠ k in atTop, v k < d - b := (tendsto_order.1 hv0).2 _ (tsub_pos_of_lt hbd)
    refine limsup_le_of_le (h := ?_)
    filter_upwards [h1, h2] with k hk1 hk2
    calc a k ≤ c * νs k (cthickening r K) + v k := hav k
      _ ≤ b + (d - b) := add_le_add hk1.le hk2.le
      _ = d := add_tsub_cancel_of_le hbd.le
  -- Step 3: `c ν(K_r) → c ν(K)` as `r ↓ 0`, since `K` is closed and `ν(K_1) < ∞`
  have htend : Tendsto (fun r => c * ν (cthickening r K)) (𝓝[>] 0) (𝓝 (c * ν K)) :=
    (ENNReal.Tendsto.const_mul (tendsto_measure_cthickening_of_isClosed
      ⟨1, one_pos, (hνK _ hK.cthickening).ne⟩ hK.isClosed) (Or.inr hc)).mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hr)

/-- **Blow-up limit with a constant orienting vector** (the weak convergence `Γ_k ⇀ C` of the
blow-ups and the upper bound for their mass measures, in the proof that cycles with the integer
slice property are integer multiplicity; `|·|` is `covectorEuclideanNorm`).  Let
`X_k(ω) = ∫ ⟨ω, τ_k⟩ dν_k` and `C(ω) = ∫ ⟨ω, ζ₀⟩ dν`, where `∫ f dν_k → ∫ f dν` for continuous
compactly supported `f`, `limsup_k ν_k(K) ≤ ν(K)` for compact `K`, `|⟨α, ζ₀⟩| ≤ s |α|`, and
`∫_{B̄_R(0)} ‖τ_k − ζ₀‖ dν_k → 0` for every `R > 0`.  Let `μ_k` be the mass measure of `X_k`.  Then
`X_k ⇀ C` by `Submission.cbr_ci_bl_cvl_pairing_tendsto` with `w = ω`.  Fix a compact `K` and
`r > 0`, and choose `R > 0` with `cthickening r K ⊆ B̄_R(0)`.  The open set
`G = thickening r K` satisfies `K ⊆ G ⊆ cthickening r K`.  Apply
`Submission.cbr_ci_bl_cvl_massOn_le` with `B = Pⁿ` (`Submission.cbr_ci_bl_covector_opNorm_le`):
`μ_k(K) ≤ M_G(X_k) ≤ s ν_k(cthickening r K) + Pⁿ ∫_{B̄_R(0)} ‖τ_k − ζ₀‖ dν_k`.  The last term tends
to `0`, so `Submission.cbr_ci_bl_cvl_limsup_le_of_cthickening` gives `limsup_k μ_k(K) ≤ s ν(K)`. -/
theorem Submission.cbr_ci_bl_constant_vector_limit : ∀ (P n : ℕ) (Xs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (τs : ℕ → Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (s : ℝ), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → νs k K < ∞) → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(νs k)) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => νs k K) atTop ≤ ν K) → (∀ k, AEStronglyMeasurable (τs k) (νs k)) → 0 ≤ s → (∀ α : Covector (Euclid P) n, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → (∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0)) → (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n), Xs k ω = ∫ x, τs k x ((ω : DifferentialForm (Euclid P) n) x) ∂(νs k)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, C ω = ∫ x, ζ₀ ((ω : DifferentialForm (Euclid P) n) x) ∂ν) → (∀ (k : ℕ) (W : Set (Euclid P)), IsOpen W → (Xs k).massOn W = μs k W) → WeaklyConvergesOn Xs C ∧ ∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μs k K) atTop ≤ ENNReal.ofReal s * ν K := by
  intro P n Xs C νs ν μs τs ζ₀ s hνsK hνK hconv hlimsup hτ hs hζ₀ hδ hX hC hmass
  refine ⟨fun ω => ?_, fun K hK => ?_⟩
  · -- weak convergence: `ω` is continuous with compact support, so
    -- `X_k(ω) = ∫ ⟨ω, τ_k⟩ dν_k → ∫ ⟨ω, ζ₀⟩ dν = C(ω)`
    have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
        tsupport (ω : DifferentialForm (Euclid P) n) ⊆ univ := ω.property
    rw [hC ω]
    exact (Submission.cbr_ci_bl_cvl_pairing_tendsto P n νs ν τs ζ₀
      (ω : DifferentialForm (Euclid P) n) hνsK hconv hτ hδ hω.1.1.continuous hω.1.2).congr
      fun k => (hX k ω).symm
  · -- mass bound: for `r > 0` compare `μ_k(K)` with `ν_k(cthickening r K)` up to an error `v_k → 0`
    refine Submission.cbr_ci_bl_cvl_limsup_le_of_cthickening P (fun k => μs k K) νs ν
      (ENNReal.ofReal s) K hK ENNReal.ofReal_ne_top hνK hlimsup fun r hr => ?_
    -- `cthickening r K` is compact, hence contained in some `B̄_R(0)` with `R > 0`
    obtain ⟨R, hR, hKR⟩ := (hK.cthickening (r := r)).isBounded.subset_closedBall_lt 0 (0 : Euclid P)
    -- `v_k = Pⁿ ∫_{B̄_R(0)} ‖τ_k − ζ₀‖ dν_k → 0`
    have hv := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((P : ℝ) ^ n)) (hδ R hR)
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hv
    refine ⟨_, hv, fun k => ?_⟩
    -- `M_G(X_k) ≤ s ν_k(G) + v_k` for the open `G = thickening r K ⊆ cthickening r K ⊆ B̄_R(0)`,
    -- using `‖α‖ ≤ Pⁿ |α|`
    have hM := Submission.cbr_ci_bl_cvl_massOn_le P n (Xs k) (νs k) (τs k) ζ₀ s ((P : ℝ) ^ n) R
      (thickening r K) (hνsK k) (hτ k) hs hζ₀ (by positivity)
      (Submission.cbr_ci_bl_covector_opNorm_le P n) (hX k) isOpen_thickening
      ((thickening_subset_cthickening r K).trans hKR)
    rw [hmass k _ isOpen_thickening] at hM
    -- `μ_k(K) ≤ μ_k(G) = M_G(X_k)` and `ν_k(G) ≤ ν_k(cthickening r K)`
    calc μs k K ≤ μs k (thickening r K) := measure_mono (self_subset_thickening hr K)
      _ ≤ _ := hM
      _ ≤ ENNReal.ofReal s * νs k (cthickening r K) + ENNReal.ofReal ((P : ℝ) ^ n) *
          ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k) := by
        gcongr
        exact thickening_subset_cthickening r K

/-- **`Hⁿ` and the measure `θ Hⁿ⌞M` under the blow-up map `η = η_{a,λ}`, `λ > 0`** (step 2 of the
blow-up argument in the integer-multiplicity criterion for cycles; `η_{x,λ}(y) = λ⁻¹(y − x)` and
the change of variables for `η_{x,λ#}` as in the proof of Simon Ch. 6, 8.1, chapter-06.txt
lines 2230–2238).  `η = blowUpMap a λ` is the contract's `dilation a λ`, `D(y) = −λ⁻¹a + λ⁻¹y`,
an affine homeomorphism with inverse `x ↦ a + λx`; so (i) `η(M) = D(M)` is Borel.
`Hⁿ(D(s)) = λ⁻ⁿ Hⁿ(s)` for every `s`, as `D(s)` is the translate by `−λ⁻¹a` of `λ⁻¹s`.  For Borel
`B` this gives (ii): `Hⁿ(B ∩ D(M)) = Hⁿ(D(D⁻¹B ∩ M)) = λ⁻ⁿ Hⁿ(D⁻¹B ∩ M)`.  (iii) follows from
(ii): pull `λ⁻ⁿ` out of `withDensity` and transport the density along `D`, as
`θ(a + λD(x)) = θ(x)`. -/
theorem Submission.cbr_ci_bl_blowUp_restrict_scaling : ∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (a : Euclid P) (lam : ℝ), MeasurableSet M → Measurable θ → 0 < lam → MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) ∧ μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) = ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) ∧ ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) ((μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x))) = (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)).withDensity (fun y => ENNReal.ofReal (θ (a + lam • y))) := by
  intro P n M θ a lam hM _ hlam
  -- Step 1: `η = blowUpMap a λ` is `D = dilation a λ`, `y ↦ −λ⁻¹a + λ⁻¹y`, an affine
  -- homeomorphism with inverse `x ↦ a + λx`
  have hηD : Poincare.SimonGMT.Chapter03.blowUpMap a lam = dilation a lam := by
    funext y
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      _root_.smul_apply, ContinuousLinearMap.id_apply, smul_sub]
    abel
  have hDc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • a)))) : Euclid P → Euclid P) = dilation a lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation a lam) := by
    rw [← hDc]
    exact Homeomorph.measurableEmbedding _
  have hιD : ∀ x, a + lam • dilation a lam x = x := fun x => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  -- Step 2: `Hⁿ(D(s)) = λ⁻ⁿ Hⁿ(s)`: `D(s)` is the translate by `−λ⁻¹a` of `λ⁻¹s`
  have himage : ∀ s : Set (Euclid P),
      μHE[n] (dilation a lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro s
    have hs : dilation a lam '' s =
        (fun z => -(lam⁻¹ • a) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • a))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  -- Step 3, (ii): on Borel `B`, `Hⁿ(B ∩ D(M)) = Hⁿ(D(D⁻¹B ∩ M)) = λ⁻ⁿ Hⁿ(D⁻¹B ∩ M)`
  have hrestrict : μHE[n].restrict (dilation a lam '' M) =
      ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.smul_apply, hme.map_apply,
      Measure.restrict_apply (hme.measurable hB), smul_eq_mul, ← himage,
      Set.image_preimage_inter]
  rw [hηD]
  refine ⟨hme.measurableSet_image.mpr hM, hrestrict, ?_⟩
  -- Step 4, (iii): pull out the scalar and transport the density along `D`, using
  -- `θ(a + λD(x)) = θ(x)`
  rw [hrestrict, withDensity_smul_measure]
  congr 1
  ext B hB
  rw [hme.map_apply, withDensity_apply _ (hme.measurable hB), withDensity_apply _ hB,
    hme.restrict_map, hme.lintegral_map]
  simp only [hιD]

/-- **One blow-up scale of a cycle `Γ = μ ∧ ζ` with `μ = θ Hⁿ⌞M`** (Simon 7.3, the blow-ups
`η_{a,λ#}Γ`).  Let `D = η_{a,λ}` (`dilation a λ`, which equals `blowUpMap a λ`),
`c = λ^{-n}` and `μ' = c D_#μ`, and let `Γ'` satisfy the dilation identities (h2), (h4), (h5)
for `∂`, the representation and `M_W`.  `D` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`, with
`a + λD(x) = x`, and `Submission.cbr_ci_bl_blowUp_restrict_scaling` gives that `η(M)` is Borel
and `μ' = θ(a + λ·) Hⁿ⌞η(M)`.  Then `Γ(ω) = ∫ ⟨ω, ζ⟩ dμ`, as `θ > 0` on `M`;
`∂Γ'(ω) = λ^{-d} ∂Γ(ω ∘ D) = 0`; `μ'(K) ≤ c μ(ℝᴾ) < ∞`;
`M_W(Γ') = c M_{D⁻¹W}(Γ) = c μ(D⁻¹W) = μ'(W)` for open `W`;
`Γ'(ω) = ∫ ⟨ω(y), ζ(a + λy)⟩ dμ'(y)` by (h4); `μ'(η(M)ᶜ) = c μ(Mᶜ) = 0`; and rewriting through
the density of `μ'` gives `Γ'(ω) = ∫_{η(M)} θ(a + λy) ⟨ω(y), ζ(a + λy)⟩ dHⁿ(y)`. -/
theorem Submission.cbr_ci_bl_blowup_scale : ∀ (P d : ℕ) (Γ Γ' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P (d + 1)) (a : Euclid P) (lam : ℝ), 0 < lam → Γ.boundary = 0 → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[(d + 1)].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μHE[(d + 1)]) → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) d, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) d) y = (ω : DifferentialForm (Euclid P) d) (dilation a lam y)) → Γ'.boundary ω = lam⁻¹ ^ d * Γ.boundary ω') → ((∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) → (∀ W : Set (Euclid P), Γ'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ (d + 1)) * Γ.massOn W) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ Γ'.boundary = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → Γ'.massOn W = (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) W) ∧ AEStronglyMeasurable (fun y => ζ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) ∧ (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)ᶜ = 0 ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, (θ (a + lam • y) • ζ (a + lam • y)) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M))) := by
  intro P d Γ Γ' μ M θ ζ a lam hlam hΓb hμfin hmass hM hθ hζ hμ hθpos hΓrep h2 h4 h5
  -- Step 1: `D = dilation a λ` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`; it equals
  -- `η = blowUpMap a λ`, is smooth, and `a + λη(x) = x`
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation a lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • a))), by funext y; simp [dilation, dilationCLM]⟩
  have hDme : MeasurableEmbedding (dilation a lam) := by
    rw [← he]
    exact e.measurableEmbedding
  have hDcont : Continuous (dilation a lam) := by
    rw [← he]
    exact e.continuous
  have hDsurj : Surjective (dilation a lam) := by
    rw [← he]
    exact e.surjective
  have hDinj : Injective (dilation a lam) := by
    rw [← he]
    exact e.injective
  have hDsmooth : ∀ k : WithTop ℕ∞, ContDiff ℝ k (dilation a lam) := fun _ =>
    contDiff_const.add (dilationCLM P lam).contDiff
  have hDη : dilation a lam = Poincare.SimonGMT.Chapter03.blowUpMap a lam := by
    funext y
    simp only [dilation, dilationCLM, Poincare.SimonGMT.Chapter03.blowUpMap, _root_.smul_apply,
      ContinuousLinearMap.id_apply, smul_sub, neg_add_eq_sub]
  have hηinv : ∀ x, a + lam • Poincare.SimonGMT.Chapter03.blowUpMap a lam x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hlam.ne', add_sub_cancel]
  -- `η(M)` is Borel and `μ' = c D_#μ = (Hⁿ⌞η(M)) ⌞ θ(a + λ·)` (sibling `blowup_measure`)
  obtain ⟨hηM, -, hμ'⟩ :=
    Submission.cbr_ci_bl_blowUp_restrict_scaling P (d + 1) M θ a lam hM hθ hlam
  rw [← hμ] at hμ'
  have hμ'apply : ∀ s : Set (Euclid P),
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) s =
        ENNReal.ofReal (lam⁻¹ ^ (d + 1)) * μ (dilation a lam ⁻¹' s) := fun s => by
    rw [Measure.smul_apply, hDme.map_apply, smul_eq_mul]
  -- Step 2 (P0): `Γ(ω) = ∫ ζ(ω) dμ`, since `(ofReal θ).toReal = θ` on `M`
  have hP0 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1),
      Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ := by
    intro ω
    rw [hΓrep ω, hμ, integral_withDensity_eq_integral_toReal_smul hθ.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun hM fun x hx => ?_
    simp only [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
  -- Step 3 (P7): `∂Γ'(ω) = λ^{-d} ∂Γ(ω ∘ D) = 0`, `ω ∘ D` being a test form
  have hP7 : Γ'.boundary = 0 := by
    refine GeometricCurrentOn.ext fun ω => ?_
    have hcpt : HasCompactSupport ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) := by
      rw [← he]
      exact ω.property.1.2.comp_homeomorph e
    have hmem : (ω : DifferentialForm (Euclid P) d) ∘ dilation a lam ∈
        testFormOnSubmodule (univ : Set (Euclid P)) d := by
      show IsTestForm ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) ∧
        tsupport ((ω : DifferentialForm (Euclid P) d) ∘ dilation a lam) ⊆ univ
      exact ⟨⟨ω.property.1.1.comp (hDsmooth _), hcpt⟩, subset_univ _⟩
    rw [h2 ω ⟨_, hmem⟩ fun _ => rfl, hΓb]
    simp only [GeometricCurrentOn.zero_apply, mul_zero]
  -- Step 4 (P1): `μ'(K) = c μ(D⁻¹K) ≤ c μ(ℝᴾ) < ∞`
  have hP1 : ∀ K : Set (Euclid P), IsCompact K →
      (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) K < ∞ := fun K _ => by
    rw [hμ'apply]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono (subset_univ _)).trans_lt hμfin)
  -- Step 5 (P2): `M_W(Γ') = M_{D(D⁻¹W)}(Γ') = c M_{D⁻¹W}(Γ) = c μ(D⁻¹W) = μ'(W)`
  have hP2 : ∀ W : Set (Euclid P), IsOpen W →
      Γ'.massOn W = (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) W := by
    intro W hW
    rw [hμ'apply, ← hmass _ (hW.preimage hDcont), ← h5, image_preimage_eq W hDsurj]
  -- Step 6 (P3): `y ↦ a + λy` is measurable, so `y ↦ ζ(a + λy)` is strongly measurable
  have hAmeas : Measurable fun y : Euclid P => a + lam • y :=
    (continuous_const.add (continuous_const_smul lam)).measurable
  -- Step 7 (P5): `(h4)` applied to (P0)
  have hP5 := h4 hP0
  -- Step 8 (P6): `μ'(η(M)ᶜ) = c μ((D⁻¹(D(M)))ᶜ) = c μ(Mᶜ) = 0`
  have hμMc : μ Mᶜ = 0 := by
    rw [hμ]
    exact withDensity_absolutelyContinuous _ _
      (by rw [Measure.restrict_apply' hM, compl_inter_self, measure_empty])
  have hP6 : (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)
      (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)ᶜ = 0 := by
    rw [hμ'apply, preimage_compl, ← hDη, hDinj.preimage_image, hμMc, mul_zero]
  -- Step 9 (P8): rewrite (P5) through `μ' = (Hⁿ⌞η(M)) ⌞ θ(a + λ·)`; for `y = η(x)`, `x ∈ M`,
  -- `a + λy = x` and `(ofReal θ(x)).toReal = θ(x)`
  have hθA : Measurable fun y : Euclid P => ENNReal.ofReal (θ (a + lam • y)) :=
    (hθ.comp hAmeas).ennreal_ofReal
  have hP8 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω =
      ∫ y, (θ (a + lam • y) • ζ (a + lam • y)) ((ω : DifferentialForm (Euclid P) (d + 1)) y)
        ∂(μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) := by
    intro ω
    rw [hP5 ω, hμ', integral_withDensity_eq_integral_toReal_smul hθA
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun hηM fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [hηinv x, ENNReal.toReal_ofReal (hθpos x hx).le, _root_.smul_apply]
  exact ⟨hP0, hP7, hP1, hP2, (hζ.comp_measurable hAmeas).aestronglyMeasurable, hP5, hP6, hP8⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
