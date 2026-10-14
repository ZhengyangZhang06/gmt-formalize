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

/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
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
/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets
`Kᵢ = B̄(0, i + 1) ∩ {x : 1 / (i + 1) ≤ dist(x, y) for all y ∉ U}`: each `Kᵢ ⊆ U` (take `y = x`),
and a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and a radius `R` with
`C ⊆ B̄(0, R)`, so `C ⊆ Kᵢ` once `1 / (i + 1) < δ` and `R ≤ i + 1`. -/
theorem Submission.dor_lmbs_tfa_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) ((i : ℝ) + 1) ∩ ⋂ y ∈ Uᶜ, {x | 1 / ((i : ℝ) + 1) ≤ dist x y},
    fun i => ?_, fun i => ?_, fun C hC hCU => ?_⟩
  · exact (isCompact_closedBall _ _).inter_right
      (isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  · -- `x ∉ U` would give `1 / (i + 1) ≤ dist x x = 0`
    intro x hx
    by_contra hxU
    have h : 1 / ((i : ℝ) + 1) ≤ dist x x := mem_iInter₂.1 hx.2 x hxU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    obtain ⟨M, hM⟩ := exists_nat_ge R
    have hNi : (N : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_left N M
    have hMi : (M : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_right N M
    refine ⟨max N M, fun x hx => ⟨?_, mem_iInter₂.2 fun y hy => ?_⟩⟩
    · have hxR := mem_closedBall.1 (hR hx)
      rw [mem_closedBall]
      linarith
    · -- `y ∉ thickening δ C` gives `δ ≤ dist x y`
      have hxy : δ ≤ dist x y := by
        by_contra h
        exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
      have hle : 1 / (((max N M : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      show 1 / (((max N M : ℕ) : ℝ) + 1) ≤ dist x y
      linarith
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_lmbs_tfa_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
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

/-- Test forms supported in a fixed compact `K` have a countable subfamily `D` approximating every
such `ω` together with `dω`, uniformly on `ℝᴾ`.  The covector spaces are finite-dimensional
(`dor_lmbs_tfa_covector_finiteDimensional`), so `C(K, Λⁿ × Λⁿ⁺¹)` is second countable; pull back
a countable dense subset of the image of `X = {ω : spt ω ⊆ K}` under `Φ ω = (ω, dω)|_K`.  On `K`
the pointwise distances are at most the uniform distance; off `K` all four values vanish. -/
theorem Submission.dor_lmbs_tfa_fixed_support_dense : ∀ (P n : ℕ) (U K : Set (Euclid P)), IsCompact K → ∃ D : Set (TestFormOn U n), D.Countable ∧ (∀ η ∈ D, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ η ∈ D, (∀ x, dist ((ω : DifferentialForm (Euclid P) n) x) ((η : DifferentialForm (Euclid P) n) x) < ε) ∧ ∀ x, dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) (exteriorDerivative (η : DifferentialForm (Euclid P) n) x) < ε := by
  intro P n U K hK
  -- Step 1: a form supported in `K` vanishes off `K`, and so does its exterior derivative
  have hzero : ∀ η : TestFormOn U n, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K →
      ∀ x ∉ K, (η : DifferentialForm (Euclid P) n) x = 0 ∧
        exteriorDerivative (η : DifferentialForm (Euclid P) n) x = 0 := fun η hη x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (hη h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hη (tsupport_exteriorDerivative_subset _ h))⟩
  -- Step 2: `Λⁿ` and `Λⁿ⁺¹` are finite-dimensional, hence proper and second countable
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P n
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P (n + 1)
  have : ProperSpace (Covector (Euclid P) n) := FiniteDimensional.proper_real _
  have : ProperSpace (Covector (Euclid P) (n + 1)) := FiniteDimensional.proper_real _
  have : SecondCountableTopology (Covector (Euclid P) n) := secondCountable_of_proper
  have : SecondCountableTopology (Covector (Euclid P) (n + 1)) := secondCountable_of_proper
  -- Step 3: `K` is compact, so `C(K, Λⁿ × Λⁿ⁺¹)` carries the sup metric, and it is second
  -- countable: up to `ε`, `f` is determined by a modulus `j` of uniform continuity at scale `ε / 4`
  -- and by the indices, in a dense sequence `s`, of `ε / 4`-approximations of its values on a
  -- finite `1 / (j + 1)`-net `t j` of `K`
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := by
    refine Metric.secondCountable_of_countable_discretization
      (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1))) fun ε hε => ?_
    obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq
      (Covector (Euclid P) n × Covector (Euclid P) (n + 1))
    choose r hr using fun y : Covector (Euclid P) n × Covector (Euclid P) (n + 1) =>
      hs.exists_dist_lt y (by positivity : (0 : ℝ) < ε / 4)
    have hnet : ∀ j : ℕ, ∃ t : Finset K, ∀ x : K, ∃ p ∈ t, dist x p < 1 / ((j : ℝ) + 1) := by
      intro j
      obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (univ : Set K)).elim_nhds_subcover
        (fun x => ball x (1 / ((j : ℝ) + 1))) fun x _ => ball_mem_nhds x (by positivity)
      exact ⟨t, fun x => by simpa using ht (mem_univ x)⟩
    choose t ht using hnet
    have hmod : ∀ f : C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)), ∃ j : ℕ,
        ∀ x y : K, dist x y < 1 / ((j : ℝ) + 1) → dist (f x) (f y) < ε / 4 := by
      intro f
      obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
        (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 4) (by positivity)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, fun x y hxy => hfδ (hxy.trans hj)⟩
    choose J hJ using hmod
    refine ⟨ℕ × List ℕ, inferInstance, fun f => (J f, (t (J f)).toList.map fun p => r (f p)),
      fun f g hfg => (ContinuousMap.dist_le hε.le).2 fun x => ?_⟩
    obtain ⟨hj, hl⟩ := Prod.mk.inj hfg
    rw [← hj] at hl
    -- `x` is `1 / (j + 1)`-close to a net point `p`, where `f p` and `g p` have a common index
    obtain ⟨p, hp, hxp⟩ := ht (J f) x
    have hrp : r (f p) = r (g p) := List.map_inj_left.1 hl p (Finset.mem_toList.2 hp)
    have h₁ := hJ f x p hxp
    have h₂ := hr (f p)
    have h₃ := hr (g p)
    have h₄ := hJ g x p (hj ▸ hxp)
    rw [hrp] at h₂
    rw [dist_comm] at h₃ h₄
    linarith [dist_triangle4 (f x) (f p) (s (r (g p))) (g x),
      dist_triangle (s (r (g p))) (g p) (g x)]
  -- Step 4: `Φ ω = (ω, dω)|_K`
  let Φ : TestFormOn U n → C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := fun ω =>
    ⟨fun x => ((ω : DifferentialForm (Euclid P) n) x,
        exteriorDerivative (ω : DifferentialForm (Euclid P) n) x),
      (ω.property.1.1.continuous.prodMk
        (exteriorDerivative_isTestForm ω.property.1).1.continuous).comp continuous_subtype_val⟩
  let X : Set (TestFormOn U n) := {ω | tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K}
  -- Step 5: a countable `T ⊆ Φ(X)` dense in `Φ(X)`, and a choice `σ` of preimages in `X`
  obtain ⟨T, hTc, hTX, hXT⟩ := TopologicalSpace.exists_countable_dense_subset (Φ '' X)
  have hT : ∀ t ∈ T, ∃ η, η ∈ X ∧ Φ η = t := fun t ht => hTX ht
  choose! σ hσX hσΦ using hT
  -- Step 6: `D = σ(T)` is countable and supported in `K`
  refine ⟨σ '' T, hTc.image σ, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hσX t ht
  -- Step 7: pick `t ∈ T` with `dist (Φ ω) t < ε` and put `η = σ t`
  intro ω hω ε hε
  obtain ⟨t, ht, hdist⟩ := (Metric.mem_closure_iff
    (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)))).1 (hXT ⟨ω, hω, rfl⟩) ε hε
  rw [← hσΦ t ht] at hdist
  have key : ∀ x, dist ((ω : DifferentialForm (Euclid P) n) x)
      ((σ t : DifferentialForm (Euclid P) n) x) < ε ∧
      dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x)
        (exteriorDerivative (σ t : DifferentialForm (Euclid P) n) x) < ε := by
    intro x
    by_cases hx : x ∈ K
    · -- (a) on `K`: both distances are at most `dist (Φ ω) (Φ η) < ε`
      have h := (ContinuousMap.dist_apply_le_dist (f := Φ ω) (g := Φ (σ t)) ⟨x, hx⟩).trans_lt hdist
      rw [Prod.dist_eq] at h
      exact ⟨(le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩
    · -- (b) off `K`: all four values vanish
      obtain ⟨h₁, h₂⟩ := hzero ω hω x hx
      obtain ⟨h₃, h₄⟩ := hzero (σ t) (hσX t ht) x hx
      rw [h₁, h₂, h₃, h₄, dist_self, dist_self]
      exact ⟨hε, hε⟩
  exact ⟨σ t, ⟨t, ht, rfl⟩, fun x => (key x).1, fun x => (key x).2⟩

/-- **A countable family of test forms, dense for `ω` and `dω` with common compact supports**
(Simon Ch. 6, proof of 4.5(2), p. 157: "a countable dense set of `ω ∈ 𝒟ⁿ(U)`").  Take the
compact exhaustion `Kᵢ` of `U` (`dor_lmbs_tfa_compact_exhaustion`) and, for each `i`, a
countable `Dᵢ` approximating every `ω` with `spt ω ⊆ Kᵢ` uniformly together with `dω`
(`dor_lmbs_tfa_fixed_support_dense`); then `D = ⋃ᵢ Dᵢ`.  Given `ω`, `spt ω ⊆ Kᵢ` for some `i`,
and `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω` gives `ωₖ → ω`, `dωₖ → dω` uniformly. -/
theorem Submission.dor_lmbs_testForm_countable_approx : ∀ (P n : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ D : Set (TestFormOn U n), D.Countable ∧ ∀ ω : TestFormOn U n, ∃ (K : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), IsCompact K ∧ K ⊆ U ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K ∧ (∀ k, ωs k ∈ D) ∧ (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ K) ∧ TendstoUniformly (fun k x => (ωs k : DifferentialForm (Euclid P) n) x) (ω : DifferentialForm (Euclid P) n) atTop ∧ TendstoUniformly (fun k x => exteriorDerivative (ωs k : DifferentialForm (Euclid P) n) x) (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) atTop := by
  intro P n U hU
  -- step 1: the compact exhaustion `Kᵢ` of `U`
  obtain ⟨K, hKc, hKU, hKex⟩ := Submission.dor_lmbs_tfa_compact_exhaustion P U hU
  -- steps 2–4: a countable `Dᵢ` for the test forms supported in `Kᵢ`
  choose D hDc hDK hDω using fun i =>
    Submission.dor_lmbs_tfa_fixed_support_dense P n U (K i) (hKc i)
  -- step 5: `D = ⋃ᵢ Dᵢ`
  refine ⟨⋃ i, D i, Set.countable_iUnion hDc, fun ω => ?_⟩
  -- step 6: `spt ω` is a compact subset of `U`, so it lies in some `Kᵢ`
  obtain ⟨i, hi⟩ :=
    hKex (tsupport (ω : DifferentialForm (Euclid P) n)) ω.property.1.2 ω.property.2
  -- `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω`
  choose ωs hωsD hωs using fun k : ℕ =>
    hDω i ω hi (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε := fun ε hε => by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact (Nat.one_div_le_one_div hk).trans_lt hN
  refine ⟨K i, ωs, hKc i, hKU i, hi, fun k => Set.mem_iUnion.2 ⟨i, hωsD k⟩,
    fun k => hDK i (ωs k) (hωsD k), ?_, ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).1 x).trans hk
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).2 x).trans hk
/-- Common convergent subsequence for countably many bounded real sequences.  The points
`xᵢ = (b_k(i))_k` lie in the product `Π_k [-M_k, M_k]`, which is compact (Tychonoff,
`isCompact_univ_pi`); `ℝ^ι` is first countable since `ι` is countable, so `IsCompact.tendsto_subseq`
gives a strictly increasing `σ` and a limit `a` with `x_{σ(i)} → a`.  Evaluation at `k` is
continuous, hence `b_k(σ(i)) → a(k)` for every `k`. -/
theorem Submission.codim1_zsl_pc_diagonal_subseq : ∀ (ι : Type) [Countable ι] (b : ι → ℕ → ℝ) (M : ι → ℝ), (∀ k i, |b k i| ≤ M k) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ k, ∃ L : ℝ, Tendsto (fun i => b k (σ i)) atTop (𝓝 L) := by
  intro ι _ b M hb
  have hS : IsCompact (Set.pi univ (fun k => Icc (-M k) (M k))) :=
    isCompact_univ_pi (fun k => isCompact_Icc)
  have hx : ∀ i, (fun k => b k i) ∈ Set.pi univ (fun k => Icc (-M k) (M k)) := by
    intro i
    rw [Set.mem_univ_pi]
    intro k
    exact Set.mem_Icc.mpr (abs_le.mp (hb k i))
  obtain ⟨a, -, σ, hσ, hlim⟩ := hS.tendsto_subseq hx
  exact ⟨σ, hσ, fun k => ⟨a k, ((continuous_apply k).tendsto a).comp hlim⟩⟩
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

/-- **Uniform local mass bounds give uniform evaluation bounds** (Simon Ch. 6, 2.5; first step
of the weak compactness Lemma 2.15).  With `N ≥ 0` such that `|α| ≤ N ‖α‖` and a ball
`W = B_R(0) ⊇ K`, the constant is `c = N · supⱼ M_W(Tⱼ)`: if `spt ω ⊆ K` and `‖ω(x)‖ ≤ s` then
`|ω(x)| ≤ N s`, so the evaluation bound gives `|Tⱼ(ω)| ≤ N s M_W(Tⱼ) ≤ c s`. -/
theorem Submission.dtc_bc_tc_wc_local_bound : ∀ (P n : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, (Ts j).massOn W < ∞) → ∀ K : Set (Euclid P), IsCompact K → ∃ c : ℝ, 0 ≤ c ∧ ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |Ts j ω| ≤ c * s := by
  intro P n Ts hTs K hK
  -- `|α| ≤ N ‖α‖` for the Euclidean coefficient norm
  obtain ⟨N, hN0, hN⟩ := (Submission.rsd_mw_tfa_norm_props P n).2.2.1
  -- `K ⊆ W := B_R(0)`, and `m := supⱼ M_W(Tⱼ) < ∞`
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : Euclid P)
  have hm := hTs (ball 0 R) isOpen_ball isBounded_ball
  refine ⟨N * (⨆ j, (Ts j).massOn (ball 0 R)).toReal, mul_nonneg hN0 ENNReal.toReal_nonneg, ?_⟩
  intro j ω s hωK hωs
  -- `M_W(Tⱼ) ≤ m < ∞`
  have hj : (Ts j).massOn (ball 0 R) ≤ ⨆ j, (Ts j).massOn (ball 0 R) :=
    le_iSup (fun j => (Ts j).massOn (ball 0 R)) j
  have hs : 0 ≤ s := (norm_nonneg _).trans (hωs 0)
  -- the evaluation bound with `r = N s`
  have hev := Submission.cmr_abs_apply_le_massOn P n univ (ball 0 R) (Ts j) ω (N * s)
    (hj.trans_lt hm).ne (hωK.trans hKR)
    fun x => (hN _).trans (mul_le_mul_of_nonneg_left (hωs x) hN0)
  calc |Ts j ω| ≤ N * s * ((Ts j).massOn (ball 0 R)).toReal := hev
    _ ≤ N * s * (⨆ j, (Ts j).massOn (ball 0 R)).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hm.ne hj) (mul_nonneg hN0 hs)
    _ = N * (⨆ j, (Ts j).massOn (ball 0 R)).toReal * s := by ring
/-- **Convergence on a sup-norm-dense family extends to all test forms** (Simon Ch. 6, Lemma
2.15, the boundedness half of the sequential Banach–Alaoglu argument used for 7.2.4).  Suppose the
`Sᵢ` are uniformly bounded on forms supported in each compact `K` (`|Sᵢ(ω)| ≤ c s` when
`‖ω(x)‖ ≤ s`), every `ω` is a uniform limit of forms `ωₖ ∈ D` supported in one compact `K`, and
`(Sᵢ(δ))ᵢ` converges for every `δ ∈ D`.  For `ε > 0` pick `k` with `‖ω(x) − ωₖ(x)‖ < η`,
`η = ε / (3 (c + 1))`.  Since `spt (ω − ωₖ) ⊆ K`, linearity gives `|Sᵢ(ω) − Sᵢ(ωₖ)| ≤ c η < ε / 3`
for every `i`, and `(Sᵢ(ωₖ))ᵢ` is Cauchy; the `ε / 3` estimate shows that `(Sᵢ(ω))ᵢ` is Cauchy, so
it converges in `ℝ`. -/
theorem Submission.dtc_bc_tc_wc_dense_extension : ∀ (P n : ℕ) (S : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (D : Set (TestFormOn (univ : Set (Euclid P)) n)), (∀ K : Set (Euclid P), IsCompact K → ∃ c : ℝ, 0 ≤ c ∧ ∀ (i : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |S i ω| ≤ c * s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ (K : Set (Euclid P)) (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n), IsCompact K ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K ∧ (∀ k, ωs k ∈ D) ∧ (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ K) ∧ TendstoUniformly (fun k x => (ωs k : DifferentialForm (Euclid P) n) x) (ω : DifferentialForm (Euclid P) n) atTop) → (∀ δ ∈ D, ∃ L : ℝ, Tendsto (fun i => S i δ) atTop (𝓝 L)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ L : ℝ, Tendsto (fun i => S i ω) atTop (𝓝 L) := by
  intro P n S D hbound hdense hconv ω
  -- Step 1: `K` and `ωₖ ∈ D` from (b), `c ≥ 0` from (a); it suffices that `(Sᵢ(ω))ᵢ` is Cauchy
  obtain ⟨K, ωs, hK, hωK, hωsD, hωsK, hunif⟩ := hdense ω
  obtain ⟨c, hc0, hc⟩ := hbound K hK
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε => ?_)
  -- Step 2: some `k` with `dist (ω(x), ωₖ(x)) < η = ε / (3 (c + 1))` for every `x`
  have hη : 0 < ε / (3 * (c + 1)) := by positivity
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.mp hunif _ hη).exists
  -- Step 3: `spt (ω − ωₖ) ⊆ K` and `‖(ω − ωₖ)(x)‖ ≤ η`, so linearity and (a) give
  -- `|Sᵢ(ω) − Sᵢ(ωₖ)| = |Sᵢ(ω − ωₖ)| ≤ c η < ε / 3` for every `i`
  have hsupp : tsupport ((ω - ωs k : TestFormOn (univ : Set (Euclid P)) n) :
      DifferentialForm (Euclid P) n) ⊆ K := by
    rw [Submodule.coe_sub]
    exact (tsupport_sub _ _).trans (union_subset hωK (hωsK k))
  have hnorm : ∀ x, ‖((ω - ωs k : TestFormOn (univ : Set (Euclid P)) n) :
      DifferentialForm (Euclid P) n) x‖ ≤ ε / (3 * (c + 1)) := by
    intro x
    rw [Submodule.coe_sub, Pi.sub_apply, ← dist_eq_norm]
    exact (hk x).le
  have hcη : c * (ε / (3 * (c + 1))) < ε / 3 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hclose : ∀ i, |S i ω - S i (ωs k)| < ε / 3 := by
    intro i
    have hsub : S i ω - S i (ωs k) = S i (ω - ωs k) := (map_sub (S i).toCurrent ω (ωs k)).symm
    rw [hsub]
    exact (hc i _ _ hsupp hnorm).trans_lt hcη
  -- Step 4: `(Sᵢ(ωₖ))ᵢ` converges by (c), hence is Cauchy
  obtain ⟨L, hL⟩ := hconv (ωs k) (hωsD k)
  obtain ⟨I, hI⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq (ε / 3) (by positivity)
  -- Step 5: the `ε / 3` estimate for `i, l ≥ I`
  refine ⟨I, fun i hi l hl => ?_⟩
  have h3 := hI i hi l hl
  rw [Real.dist_eq] at h3 ⊢
  obtain ⟨h1l, h1r⟩ := abs_lt.mp (hclose i)
  obtain ⟨h2l, h2r⟩ := abs_lt.mp (hclose l)
  obtain ⟨h3l, h3r⟩ := abs_lt.mp h3
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
/-- **A pointwise limit of currents with uniform zeroth-order bounds is a current** (Simon 6.2.13;
the limit step in the proof of Lemma 6.2.15).  Put `L(ω) = lim_i S_i(ω)`.  By uniqueness of
limits `L` is linear, and letting `i → ∞` in `|S_i(ω)| ≤ c s` gives `|L(ω)| ≤ c s` whenever
`spt ω ⊆ K` and `‖ω(x)‖ ≤ s` for all `x`.  So `Submission.cmcs_rc_order_zero_current` gives a
current `C` with `C(ω) = L(ω)`, and `S_i(ω) → C(ω)` for every `ω`. -/
theorem Submission.dtc_bc_tc_wc_limit_current : ∀ (P n : ℕ) (S : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ K : Set (Euclid P), IsCompact K → ∃ c : ℝ, 0 ≤ c ∧ ∀ (i : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |S i ω| ≤ c * s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ L : ℝ, Tendsto (fun i => S i ω) atTop (𝓝 L)) → ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, WeaklyConvergesOn S C := by
  intro P n S hbd hlim
  -- Step 1: the pointwise limit `L(ω) = lim_i S_i(ω)`
  choose L hL using hlim
  -- Steps 2–3: `L` is linear, by uniqueness of limits
  let Λ : TestFormOn (univ : Set (Euclid P)) n →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := fun ω η => by
        refine tendsto_nhds_unique (hL (ω + η)) ?_
        simpa only [map_add] using (hL ω).add (hL η)
      map_smul' := fun a ω => by
        refine tendsto_nhds_unique (hL (a • ω)) ?_
        simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (hL ω).const_mul a }
  -- Steps 4–5: `|L(ω)| ≤ c s` in the limit, so `order_zero_current` makes `L` a current `C`
  obtain ⟨C, hC⟩ := Submission.cmcs_rc_order_zero_current P n univ Λ fun K hK _ => by
    obtain ⟨c, -, hc⟩ := hbd K hK
    exact ⟨c, fun ω s hsupp hs => le_of_tendsto' (hL ω).abs fun i => hc i ω s hsupp hs⟩
  -- Step 6: `S_i(ω) → L(ω) = C(ω)`
  refine ⟨C, fun ω => ?_⟩
  rw [hC ω]
  exact hL ω

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
