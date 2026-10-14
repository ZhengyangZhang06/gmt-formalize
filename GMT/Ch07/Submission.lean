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

/-- **A test form has bounded Euclidean coefficient norm** (Simon Ch. 6, (1.15):
`|ω| = sup_x |ω(x)|` is finite for `ω ∈ 𝒟ⁿ(U)`).  `ω` is `C^∞`, hence continuous, with compact
support; the coefficient norm `N` is continuous (`rsd_mw_tfa_norm_props`) and `N 0 = 0`, so
`x ↦ N (ω x)` is continuous with compact support, hence bounded by some `C`, and
`c = max C 0 + 1` is a positive bound. -/
theorem Submission.cmc_fc_sc_testForm_coeff_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U n), ∃ c : ℝ, 0 < c ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c := by
  intro P n U ω
  -- Step 1: `ω` is `C^∞`, hence continuous, and has compact support
  have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  -- Step 2: `x ↦ N (ω x)` is continuous, with compact support because `N 0 = 0`
  have hcont : Continuous fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) :=
    (Submission.rsd_mw_tfa_norm_props P n).2.2.2.comp (ContDiff.continuous hsmooth)
  have hcs : HasCompactSupport fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) :=
    HasCompactSupport.comp_left (g := covectorEuclideanNorm) ω.property.1.2
      (covectorEuclideanNorm_zero P n)
  -- Step 3: a continuous compactly supported real function is bounded by some `C`
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  -- Step 4: `c = max C 0 + 1 > 0` and `N (ω x) ≤ |N (ω x)| ≤ C ≤ max C 0 < c`
  refine ⟨max C 0 + 1, by positivity, fun x => ?_⟩
  have hx := hC x
  rw [Real.norm_eq_abs] at hx
  linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)),
    le_max_left C 0]
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
/-- **Mass of a difference** (Simon (6.2.5), chapter-06.txt line 231; this subadditivity makes the
flat distances `d_W` of 7.1 (lines 2018–2022) pseudometrics and is used in the proof of 7.2):
`M_G(A − B) ≤ M_G(A) + M_G(B)` for every set `G`.  If `ω` is admissible for `M_G` then so is `−ω`
(same support, same coefficient norm), and `(A − B)(ω) = A(ω) + B(−ω)`, so
`ofReal ((A − B)(ω)) ≤ ofReal (A(ω)) + ofReal (B(−ω)) ≤ M_G(A) + M_G(B)`. -/
theorem Submission.cmc_fc_cs_massOn_sub_le : ∀ (P n : ℕ) (U G : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).massOn G ≤ A.massOn G + B.massOn G := by
  intro P n U G A B
  -- Step 1: it suffices to bound `ofReal ((A − B)(ω))` for each admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- Step 2: `−ω` is admissible: same support, same coefficient norm
  have hneg : -ω ∈ massAdmissibleOn U n G := by
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_neg, tsupport_neg]
      exact hω.1
    · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 3: `(A − B)(ω) = A(ω) − B(ω) = A(ω) + B(−ω)`, by linearity of `B`
  have hsplit : (A - B) ω = A ω + B (-ω) := by
    have hB : B (-ω) = -B ω := B.toCurrent.map_neg ω
    change A ω - B ω = A ω + B (-ω)
    rw [hB, sub_eq_add_neg]
  -- Steps 4–5: `ofReal` is subadditive, and each term is bounded by the corresponding mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hneg)
/-- **Support calculus** for currents in `ℝᴾ` (Simon 6.2.11): (i) if `E` is closed and `X(ω) = 0`
whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed; (iii)
`spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`.  A point lies off `spt X`
iff it has an open neighbourhood with compact closure on which `X` vanishes.  Small balls are such
neighbourhoods in the proper space `ℝᴾ`; zero neighbourhoods of `A` and `B` intersect to one of
`A − B`; and since `spt dη ⊆ spt η`, a zero neighbourhood of `A` is one of `∂A`. -/
theorem Submission.cmcsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- `B_ε(x)` is open, and its closure lies in the compact `closedBall x ε` (`ℝᴾ` is proper)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ univ := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) for `x ∉ E`, a ball around `x` inside the open set `Eᶜ` is a zero neighbourhood of `x`
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε)
      ⟨(hball x ε).1, (hball x ε).2.1, (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) `spt X = univ \ X.zeroRegion`, and the zero region is open
    intro X
    exact isClosed_univ.sdiff X.isOpen_zeroRegion
  · -- (iii) the intersection of zero neighbourhoods of `A` and `B` is one of `A − B`
    intro A B x hx
    by_contra hAB
    have hxA : x ∈ A.zeroRegion := by
      by_contra h
      exact hAB (mem_union_left _ ⟨mem_univ x, h⟩)
    have hxB : x ∈ B.zeroRegion := by
      by_contra h
      exact hAB (mem_union_right _ ⟨mem_univ x, h⟩)
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp hxA
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp hxB
    refine hx.2 (mem_sUnion_of_mem (⟨hxWA, hxWB⟩ : x ∈ WA ∩ WB) ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (mem_sUnion_of_mem
      (mem_ball_self one_pos) ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2,
        fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `∂A(η) = A(dη)` with `spt dη ⊆ spt η`: a zero neighbourhood of `A` is one of `∂A`
    intro A x hx
    refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp hxA
    refine mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)
/-- **Telescoping series** (Simon Ch. 6, proof of 5.1: the passage from the limits (19) to the
identity (21), chapter-06.txt lines 1792–1820): if `∑ⱼ aⱼ = s`, `a₀ = −k₀`, `aⱼ₊₁ = kⱼ − kⱼ₊₁`
and `kⱼ → 0`, then `s = 0`.  The partial sums telescope, `∑_{i ≤ N} aᵢ = −k_N`; they tend to `s`
because the series converges, and to `−0 = 0` because `k_N → 0`, so `s = 0` by uniqueness of
limits. -/
theorem Submission.cmcsdtd_hasSum_telescoping_eq_zero : ∀ (a k : ℕ → ℝ) (s : ℝ), HasSum a s → a 0 = -k 0 → (∀ j, a (j + 1) = k j - k (j + 1)) → Tendsto k atTop (𝓝 0) → s = 0 := by
  intro a k s hs h0 hsucc hk
  -- Step 1: the partial sums telescope, `∑_{i ≤ N} aᵢ = −k_N`
  have hpart : ∀ N, ∑ i ∈ Finset.range (N + 1), a i = -k N := by
    intro N
    induction N with
    | zero => simp [h0]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hsucc]
      ring
  -- Step 2: the series converges, so its partial sums `∑_{i ≤ N} aᵢ` tend to `s`
  have h1 : Tendsto (fun N => ∑ i ∈ Finset.range (N + 1), a i) atTop (𝓝 s) :=
    hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  -- Step 3: by step 1 they are `−k_N`, which tends to `−0 = 0`
  have h2 : Tendsto (fun N => ∑ i ∈ Finset.range (N + 1), a i) atTop (𝓝 0) := by
    simp_rw [hpart]
    simpa using hk.neg
  -- Step 4: limits in `ℝ` are unique
  exact tendsto_nhds_unique h1 h2

/-- **Mass controls evaluation** (Simon Ch. 6, 2.4–2.5; used in proving the deformation theorem
5.1, chapter-06.txt lines 1792–1838: mass-Cauchy deformed pieces converge weakly, (19), and the
masses of the limits are estimated as in (24)–(25)).  If `|ω(x)| ≤ c` for all `x`
(`cmc_fc_sc_testForm_coeff_bound`), then 6.2.5 with `W = U` (`cmr_abs_apply_le_massOn`) gives
`|X_j(ω)| ≤ c M(X_j)` whenever `M(X_j) < ∞`.  (i) If `M(X_j) → 0`, then `M(X_j)` is eventually
finite and `c M(X_j) → 0`, so `X_j(ω) → 0` by squeezing.  (ii) If `Σ_j M(X_j) < ∞`, every
`M(X_j)` is finite and `Σ_j X_j(ω)` converges by comparison with `Σ_j c M(X_j)`; for `ω`
admissible for `M(Y)`, `Y(ω) = Σ_j X_j(ω) ≤ Σ_j |X_j(ω)| ≤ Σ_j M(X_j)`, and the supremum over
such `ω` gives `M(Y) ≤ Σ_j M(X_j)`. -/
theorem Submission.cmcsdtd_mass_controls_eval : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), (Tendsto (fun j => (X j).mass) atTop (𝓝 0) → ∀ ω : TestFormOn U n, Tendsto (fun j => X j ω) atTop (𝓝 0)) ∧ (∑' j, (X j).mass < ∞ → (∀ ω : TestFormOn U n, Summable (fun j => X j ω)) ∧ ∀ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun j => X j ω) (Y ω)) → Y.mass ≤ ∑' j, (X j).mass) := by
  intro P n U X
  -- Step 1: `|X_j(ω)| ≤ r M(X_j)` if `M(X_j) < ∞` and `|ω(x)| ≤ r` (6.2.5 with `W = U`)
  have hEB : ∀ (ω : TestFormOn U n) (r : ℝ) (j : ℕ), (X j).mass ≠ ∞ →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) →
      |X j ω| ≤ r * (X j).mass.toReal := fun ω r j hj hr =>
    Submission.cmr_abs_apply_le_massOn P n U U (X j) ω r hj ω.property.2 hr
  refine ⟨fun hlim ω => ?_, fun hsum => ?_⟩
  · -- Step 2: (i), `M(X_j)` is eventually finite and `c M(X_j) → 0`; squeeze
    obtain ⟨c, -, hc⟩ := Submission.cmc_fc_sc_testForm_coeff_bound P n U ω
    have hfin : ∀ᶠ j in atTop, (X j).mass ≠ ∞ :=
      (hlim.eventually (gt_mem_nhds zero_lt_one)).mono fun j hj =>
        (hj.trans ENNReal.one_lt_top).ne
    have hreal : Tendsto (fun j => (X j).mass.toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
      rwa [ENNReal.toReal_zero] at h
    have hbound : Tendsto (fun j => c * (X j).mass.toReal) atTop (𝓝 0) := by
      simpa using hreal.const_mul c
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hfin] with j hj
    rw [Real.norm_eq_abs]
    exact hEB ω c j hj hc
  · -- Step 3: every `M(X_j)` is finite and `Σ_j M(X_j)` is a summable real series
    have hfin : ∀ j, (X j).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum.ne
    have hsumR : Summable fun j => (X j).mass.toReal := ENNReal.summable_toReal hsum.ne
    refine ⟨fun ω => ?_, fun Y hY => ?_⟩
    · -- Step 4: (ii)(a), comparison with `Σ_j c M(X_j)`
      obtain ⟨c, -, hc⟩ := Submission.cmc_fc_sc_testForm_coeff_bound P n U ω
      refine Summable.of_norm_bounded (hsumR.mul_left c) fun j => ?_
      rw [Real.norm_eq_abs]
      exact hEB ω c j (hfin j) hc
    · -- Step 5: (ii)(b), `Y(ω) = Σ_j X_j(ω) ≤ Σ_j |X_j(ω)| ≤ Σ_j M(X_j)` for admissible `ω`
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      have hb : ∀ j, |X j ω| ≤ (X j).mass.toReal := fun j =>
        (hEB ω 1 j (hfin j) hω.2).trans_eq (one_mul _)
      have habs : Summable fun j => |X j ω| :=
        Summable.of_nonneg_of_le (fun j => abs_nonneg _) hb hsumR
      have hle : Y ω ≤ ∑' j, (X j).mass.toReal := by
        rw [← (hY ω).tsum_eq]
        calc ∑' j, X j ω ≤ ∑' j, |X j ω| :=
              Summable.tsum_le_tsum (fun j => le_abs_self _) (hY ω).summable habs
          _ ≤ ∑' j, (X j).mass.toReal := Summable.tsum_le_tsum hb habs hsumR
      calc ENNReal.ofReal (Y ω) ≤ ENNReal.ofReal (∑' j, (X j).mass.toReal) :=
            ENNReal.ofReal_le_ofReal hle
        _ = ∑' j, (X j).mass := by
            rw [← ENNReal.tsum_toReal_eq hfin, ENNReal.ofReal_toReal hsum.ne]
/-- **Deformation of the shells** (Simon 6.5.1, proof, displays (11)–(16), (20), (22)–(23);
chapter-06.txt lines 1740–1830).  Let `push`, `homot` satisfy the properties (PF) of push-forward
and straight-line homotopy under Lipschitz maps, and let `∂W₀ = D₀ − Z₀`,
`∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`.  The homotopy formula for the homotopy `h_j` from `φ_j`
to `id`, with `push(id, W_j) = W_j`, gives `W_j − φ_{j#}W_j − h_{j#}∂W_j = ∂h_{j#}W_j`; linearity
and locality (`φ_{j+1} = φ_j` on `spt Z_j`) split `φ_{j#}∂W_j` and `h_{j#}∂W_j` into telescoping
differences.  The deformed currents are integer multiplicity, `Λ_j^k ≤ (2Λ_j)^k` gives the mass
bounds, and `|φ_j(x) + t(x − φ_j(x)) − x| = (1 − t)|φ_j(x) − x| ≤ δ` gives the supports. -/
theorem Submission.cmcsdtd_shell_deformation : ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ((∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary) → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, IsClosed X.support) → (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m, (A - B).support ⊆ A.support ∪ B.support) → ∀ (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (δ : ℝ) (L A A' : Set (Euclid P)), (W 0).boundary = D 0 - Z 0 → (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) → (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) → (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (Z j).support) → (∀ j, ∀ x ∈ (W j).support ∪ (D j).support ∪ (Z j).support, dist (φ j x) x ≤ δ) → (∀ j, ∀ x ∈ (W j).support, φ j x ∈ L) → (∀ j, (W j).support ⊆ A) → (∀ j, (D j).support ⊆ A') → W 0 - push (m + 1) (φ 0) (W 0) - (homot m (φ 0) (fun x => x) (D 0) - homot m (φ 0) (fun x => x) (Z 0)) = (homot (m + 1) (φ 0) (fun x => x) (W 0)).boundary ∧ (∀ j, W (j + 1) - push (m + 1) (φ (j + 1)) (W (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (D (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (Z (j + 1)) - homot m (φ j) (fun x => x) (Z j))) = (homot (m + 1) (φ (j + 1)) (fun x => x) (W (j + 1))).boundary) ∧ (push (m + 1) (φ 0) (W 0)).boundary = push m (φ 0) (D 0) - push m (φ 0) (Z 0) ∧ (∀ j, (push (m + 1) (φ (j + 1)) (W (j + 1))).boundary = push m (φ (j + 1)) (D (j + 1)) - (push m (φ (j + 1)) (Z (j + 1)) - push m (φ j) (Z j))) ∧ (∀ j, IsIntegerMultiplicity (push (m + 1) (φ j) (W j)) ∧ IsIntegerMultiplicity (homot (m + 1) (φ j) (fun x => x) (W j))) ∧ (∀ j, (push (m + 1) (φ j) (W j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass) ∧ (push m (φ j) (D j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass ∧ (homot m (φ j) (fun x => x) (D j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass) ∧ (push m (φ j) (Z j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass ∧ (homot m (φ j) (fun x => x) (Z j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass)) ∧ (∀ j, (push (m + 1) (φ j) (W j)).support ⊆ L ∩ cthickening δ A ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).support ⊆ cthickening δ A ∧ (push m (φ j) (D j)).support ⊆ cthickening δ A' ∧ (homot m (φ j) (fun x => x) (D j)).support ⊆ cthickening δ A') := by
  intro P m push homot hPF hSii hSiii W D Z φ Λ δ L A A' hW0 hWs hIM hWnc hDnc hZnc hLip h1 hmono
    hEq hdist hφL hWA hDA
  obtain ⟨PF1, PF2, PF3, PF4, PF5, -⟩ := hPF
  -- Step 1: `id` is `Λ_j`-Lipschitz (`1 ≤ Λ_j`) and `φ_j` is `Λ_{j+1}`-Lipschitz (`Λ_j ≤ Λ_{j+1}`)
  have hidLip : ∀ j, LipschitzWith (Λ j) (fun x : Euclid P => x) := fun j =>
    LipschitzWith.id.weaken (h1 j)
  have hφLip : ∀ j, LipschitzWith (Λ (j + 1)) (φ j) := fun j => (hLip j).weaken (hmono j)
  -- Step 2: `W_j`, `D_j`, `Z_j` are normal with compact support (for `W_j`, the boundary mass
  -- `boundaryMassOn (W j) univ` is `M(∂W_j)` by definition).
  -- Step 3: so is `Z_{j+1} − Z_j`: its support is closed and lies in `spt Z_{j+1} ∪ spt Z_j`,
  -- and `M(X − Y) ≤ M(X) + M(Y)`, with `∂(X − Y) = ∂X − ∂Y` in positive degree
  have hbmsub : ∀ (n : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) n),
      boundaryMassOn X univ < ∞ → boundaryMassOn Y univ < ∞ → boundaryMassOn (X - Y) univ < ∞ := by
    intro n X Y hX hY
    cases n with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      have e : (X - Y).boundary = X.boundary - Y.boundary := by
        ext ω
        rfl
      show (X - Y).boundary.massOn univ < ∞
      rw [e]
      exact (Submission.cmc_fc_cs_massOn_sub_le P k univ univ X.boundary Y.boundary).trans_lt
        (ENNReal.add_lt_top.2 ⟨hX, hY⟩)
  have hZd : ∀ j, IsCompact (Z (j + 1) - Z j).support ∧ (Z (j + 1) - Z j).mass < ∞ ∧
      boundaryMassOn (Z (j + 1) - Z j) univ < ∞ := by
    intro j
    obtain ⟨hc1, hm1, hb1⟩ := hZnc (j + 1)
    obtain ⟨hc0, hm0, hb0⟩ := hZnc j
    refine ⟨(hc1.union hc0).of_isClosed_subset (hSii _) (hSiii _ _), ?_, hbmsub m _ _ hb1 hb0⟩
    exact (Submission.cmc_fc_cs_massOn_sub_le P m univ univ _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨hm1, hm0⟩)
  -- Step 4: locality, as `φ_{j+1} = φ_j` on `spt Z_j`
  have hloc : ∀ j, push m (φ (j + 1)) (Z j) = push m (φ j) (Z j) ∧
      homot m (φ (j + 1)) (fun x => x) (Z j) = homot m (φ j) (fun x => x) (Z j) := fun j =>
    PF3 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (φ j) (fun x => x) (Z j) (hLip (j + 1))
      (hidLip (j + 1)) (hφLip j) (hidLip (j + 1)) (hZnc j).1 (hZnc j).2.1 (hZnc j).2.2 (hEq j)
      (fun _ _ => rfl)
  -- Step 5: linearity deforms `∂W₀ = D₀ − Z₀` and `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`
  have hlin0 := PF2 m (Λ 0) (φ 0) (fun x => x) (D 0) (Z 0) (hLip 0) (hidLip 0) (hDnc 0).1
    (hDnc 0).2.1 (hDnc 0).2.2 (hZnc 0).1 (hZnc 0).2.1 (hZnc 0).2.2
  have hlinS : ∀ j, push m (φ (j + 1)) (D (j + 1) - (Z (j + 1) - Z j)) =
        push m (φ (j + 1)) (D (j + 1)) - (push m (φ (j + 1)) (Z (j + 1)) - push m (φ j) (Z j)) ∧
      homot m (φ (j + 1)) (fun x => x) (D (j + 1) - (Z (j + 1) - Z j)) =
        homot m (φ (j + 1)) (fun x => x) (D (j + 1)) -
          (homot m (φ (j + 1)) (fun x => x) (Z (j + 1)) - homot m (φ j) (fun x => x) (Z j)) := by
    intro j
    obtain ⟨e1, e2⟩ := PF2 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (D (j + 1)) (Z (j + 1) - Z j)
      (hLip (j + 1)) (hidLip (j + 1)) (hDnc (j + 1)).1 (hDnc (j + 1)).2.1 (hDnc (j + 1)).2.2
      (hZd j).1 (hZd j).2.1 (hZd j).2.2
    obtain ⟨e3, e4⟩ := PF2 m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (Z (j + 1)) (Z j)
      (hLip (j + 1)) (hidLip (j + 1)) (hZnc (j + 1)).1 (hZnc (j + 1)).2.1 (hZnc (j + 1)).2.2
      (hZnc j).1 (hZnc j).2.1 (hZnc j).2.2
    rw [e1, e3, (hloc j).1, e2, e4, (hloc j).2]
    exact ⟨rfl, rfl⟩
  -- Step 6: the homotopy formula from `φ_j` to `id` on `W_j`, where `push_{m+1}(id, W_j) = W_j`
  have hPF5 := fun j => PF5 m (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
    (hWnc j).2.1 (hWnc j).2.2
  have hPF1 : ∀ j, push (m + 1) (fun x => x) (W j) = W j := fun j =>
    PF1 (m + 1) (W j) (hWnc j).1 (hWnc j).2.1 (hWnc j).2.2
  -- Step 7: in `[0, ∞]`, `Λ_j^k ≤ (2Λ_j)^k`
  have hpow : ∀ (j k : ℕ) (M : ℝ≥0∞), (Λ j : ℝ≥0∞) ^ k * M ≤ (2 * (Λ j : ℝ≥0∞)) ^ k * M :=
    fun j k M => by
      gcongr
      exact le_mul_of_one_le_left zero_le one_le_two
  -- Step 8: `φ_j(x) + t(x − φ_j(x)) − x = (1 − t)(φ_j(x) − x)`, so the segment from `φ_j(x)` to
  -- `x` stays within `δ` of `x`
  have hseg : ∀ (j : ℕ) (S B : Set (Euclid P)), S ⊆ B → (∀ x ∈ S, dist (φ j x) x ≤ δ) →
      {y : Euclid P | ∃ x ∈ S, ∃ t ∈ Icc (0 : ℝ) 1, y = φ j x + t • (x - φ j x)} ⊆
        cthickening δ B := by
    rintro j S B hSB hd _ ⟨x, hx, t, ht, rfl⟩
    refine mem_cthickening_of_dist_le _ x δ B (hSB hx) ?_
    have e : φ j x + t • (x - φ j x) - x = (1 - t) • (φ j x - x) := by
      rw [sub_smul, one_smul, smul_sub, smul_sub]
      abel
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    calc dist (φ j x + t • (x - φ j x)) x = (1 - t) * dist (φ j x) x := by
          rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1t, dist_eq_norm]
      _ ≤ 1 * dist (φ j x) x := by gcongr; linarith [ht.1]
      _ ≤ δ := by rw [one_mul]; exact hd x hx
  refine ⟨?_, fun j => ?_, ?_, fun j => ?_, fun j => (hPF5 j).2.2 (hIM j), fun j => ?_, fun j => ?_⟩
  · -- (c1): substitute `∂W₀ = D₀ − Z₀` into the homotopy formula
    have e := (hPF5 0).2.1
    rw [hPF1 0, hW0, hlin0.2] at e
    exact e
  · -- (c2): substitute `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`
    have e := (hPF5 (j + 1)).2.1
    rw [hPF1 (j + 1), hWs j, (hlinS j).2] at e
    exact e
  · -- (c3): `∂φ_{0#}W₀ = φ_{0#}∂W₀`
    rw [(hPF5 0).1, hW0, hlin0.1]
  · -- (c4): `∂φ_{j+1#}W_{j+1} = φ_{j+1#}∂W_{j+1}`
    rw [(hPF5 (j + 1)).1, hWs j, (hlinS j).1]
  · -- (c6): mass bounds, with `|φ_j(x) − x| ≤ δ` on the supports
    have hW4 := PF4 (m + 1) (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
      (hWnc j).2.1 (hWnc j).2.2
    have hD4 := PF4 m (Λ j) (φ j) (fun x => x) (D j) (hLip j) (hidLip j) (hDnc j).1 (hDnc j).2.1
      (hDnc j).2.2
    have hZ4 := PF4 m (Λ j) (φ j) (fun x => x) (Z j) (hLip j) (hidLip j) (hZnc j).1 (hZnc j).2.1
      (hZnc j).2.2
    refine ⟨hW4.1.trans (hpow j _ _), ?_, hD4.1.trans (hpow j _ _), ?_,
      hZ4.1.trans (hpow j _ _), ?_⟩
    · rw [← mul_assoc]
      exact hW4.2.2.1 δ fun x hx => hdist j x (Or.inl (Or.inl hx))
    · rw [← mul_assoc]
      exact hD4.2.2.1 δ fun x hx => hdist j x (Or.inl (Or.inr hx))
    · rw [← mul_assoc]
      exact hZ4.2.2.1 δ fun x hx => hdist j x (Or.inr hx)
  · -- (c7): supports, via `spt φ_{j#}X ⊆ φ_j(spt X)` and Step 8
    have hW4 := PF4 (m + 1) (Λ j) (φ j) (fun x => x) (W j) (hLip j) (hidLip j) (hWnc j).1
      (hWnc j).2.1 (hWnc j).2.2
    have hD4 := PF4 m (Λ j) (φ j) (fun x => x) (D j) (hLip j) (hidLip j) (hDnc j).1 (hDnc j).2.1
      (hDnc j).2.2
    refine ⟨hW4.2.1.trans ?_, hW4.2.2.2.trans (hseg j _ A (hWA j) fun x hx =>
      hdist j x (Or.inl (Or.inl hx))), hD4.2.1.trans ?_, hD4.2.2.2.trans (hseg j _ A' (hDA j)
      fun x hx => hdist j x (Or.inl (Or.inr hx)))⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hφL j x hx, mem_cthickening_of_dist_le _ x δ A (hWA j hx)
        (hdist j x (Or.inl (Or.inl hx)))⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_cthickening_of_dist_le _ x δ A' (hDA j hx) (hdist j x (Or.inl (Or.inr hx)))

/-- **Summation of the deformed shells** (Simon Ch. 6, proof of 5.1, displays (17)–(25)).  The mass
series of the pieces `V_j`, `H_j`, `Y_j`, `E′_j` are dominated by `Σ a_j`, `δ Σ a_j`, `Σ b_j`,
`δ Σ b_j < ∞`, so `(IMS)` sums `V_j`, `H_j`, `E′_j` to `Q₀`, `R₁`, `S₁`, with supports in the closed
sets `K₁`, `K₂`, `K₃`.  At a test form `ω`, (I1)–(I2) make the series of
`(W_j − V_j − E′_j)(ω) − H_j(dω)` telescope with remainder `−K_N(ω) → 0` (`M(K_N) ≤ δ c_N → 0`), so
`T − Q₀ − S₁ = ∂R₁`; likewise (I3)–(I4) give `∂Q₀(η) = Σ_j Y_j(η)` (remainder `−L′_N(η) → 0`).
Hence `M(∂Q₀) ≤ Σ_j M(Y_j)`, and `∂Q₀` vanishes on forms supported off `K₃ ⊇ spt Y_j`. -/
theorem Submission.cmcsdtd_deformed_series_sum : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) E → X ω = 0) → X.support ⊆ E) → (∀ (k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W V E' K : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (H : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (Y L' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (a b c : ℕ → ℝ≥0∞) (δ : ℝ) (K₁ K₂ K₃ : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) → W 0 - V 0 - (E' 0 - K 0) = (H 0).boundary → (∀ j, W (j + 1) - V (j + 1) - (E' (j + 1) - (K (j + 1) - K j)) = (H (j + 1)).boundary) → (V 0).boundary = Y 0 - L' 0 → (∀ j, (V (j + 1)).boundary = Y (j + 1) - (L' (j + 1) - L' j)) → (∀ j, IsIntegerMultiplicity (V j) ∧ IsIntegerMultiplicity (H j)) → (∀ j, (V j).mass ≤ a j ∧ (H j).mass ≤ ENNReal.ofReal δ * a j ∧ (Y j).mass ≤ b j ∧ (E' j).mass ≤ ENNReal.ofReal δ * b j ∧ (L' j).mass ≤ c j ∧ (K j).mass ≤ ENNReal.ofReal δ * c j) → ∑' j, a j < ∞ → ∑' j, b j < ∞ → Tendsto c atTop (𝓝 0) → IsClosed K₁ → IsClosed K₂ → IsClosed K₃ → (∀ j, (V j).support ⊆ K₁ ∧ (H j).support ⊆ K₂ ∧ (Y j).support ⊆ K₃ ∧ (E' j).support ⊆ K₃) → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ K₁ ∧ R₁.support ⊆ K₂ ∧ Q₀.boundary.support ⊆ K₃ ∧ S₁.support ⊆ K₃ ∧ Q₀.mass ≤ ∑' j, a j ∧ Q₀.boundary.mass ≤ ∑' j, b j ∧ R₁.mass ≤ ENNReal.ofReal δ * ∑' j, a j ∧ S₁.mass ≤ ENNReal.ofReal δ * ∑' j, b j := by
  intro hVO P m hSi hIMS T W V E' K H Y L' a b c δ K₁ K₂ K₃ hT h0 hs hb0 hbs hIM hmass hsa hsb
    hc hK₁ hK₂ hK₃ hspt
  -- `ME` for currents in `ℝᴾ` of degrees `m` and `m + 1`
  have hME0 := Submission.cmcsdtd_mass_controls_eval P m univ
  have hME1 := Submission.cmcsdtd_mass_controls_eval P (m + 1) univ
  -- Step 1: termwise comparison of the mass series; all four are finite since `ofReal δ < ∞`
  have hVsum : ∑' j, (V j).mass ≤ ∑' j, a j := ENNReal.tsum_le_tsum fun j => (hmass j).1
  have hHsum : ∑' j, (H j).mass ≤ ENNReal.ofReal δ * ∑' j, a j := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hmass j).2.1
  have hYsum : ∑' j, (Y j).mass ≤ ∑' j, b j := ENNReal.tsum_le_tsum fun j => (hmass j).2.2.1
  have hEsum : ∑' j, (E' j).mass ≤ ENNReal.ofReal δ * ∑' j, b j := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hmass j).2.2.2.1
  have hVfin : ∑' j, (V j).mass < ∞ := hVsum.trans_lt hsa
  have hHfin : ∑' j, (H j).mass < ∞ :=
    hHsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsa)
  have hYfin : ∑' j, (Y j).mass < ∞ := hYsum.trans_lt hsb
  have hEfin : ∑' j, (E' j).mass < ∞ :=
    hEsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsb)
  -- Step 2: `0 ≤ M(L′_j) ≤ c_j → 0` and `0 ≤ M(K_j) ≤ δ c_j → δ · 0 = 0`
  have hLlim : Tendsto (fun j => (L' j).mass) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => zero_le)
      fun j => (hmass j).2.2.2.2.1
  have hKlim : Tendsto (fun j => (K j).mass) atTop (𝓝 0) := by
    have hδc : Tendsto (fun j => ENNReal.ofReal δ * c j) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδc (fun _ => zero_le)
      fun j => (hmass j).2.2.2.2.2
  -- Step 3: `(IMS)` sums `V_j`, `H_j` (degree `(m + 1) + 1 = m + 2`) and `E′_j`
  obtain ⟨Q₀, hQs, hQm, hQspt, hQim⟩ := hIMS m V hVfin
  obtain ⟨R₁, hRs, hRm, hRspt, hRim⟩ := hIMS (m + 1) H hHfin
  obtain ⟨S₁, hSs, hSm, hSspt, -⟩ := hIMS m E' hEfin
  -- Step 4: `α_j = W_j(ω) − V_j(ω) − E′_j(ω) − H_j(dω)` sums to `(T − Q₀ − S₁)(ω) − R₁(dω)`; by
  -- (I1)–(I2), `α₀ = −K₀(ω)` and `α_{j+1} = K_j(ω) − K_{j+1}(ω)`, with `K_j(ω) → 0` (`ME` (i))
  have hid : T - Q₀ - S₁ = R₁.boundary := by
    ext ω
    have hsum := (((hT ω).sub (hQs ω)).sub (hSs ω)).sub
      (hRs (exteriorDerivativeTestOn univ (m + 1) ω))
    have hz := Submission.cmcsdtd_hasSum_telescoping_eq_zero _ (fun j => K j ω) _ hsum ?_ ?_
      ((hME1 K).1 hKlim ω)
    · change T ω - Q₀ ω - S₁ ω = R₁ (exteriorDerivativeTestOn univ (m + 1) ω)
      linarith
    · have e := congrArg (fun X => X ω) h0
      change W 0 ω - V 0 ω - (E' 0 ω - K 0 ω) = H 0 (exteriorDerivativeTestOn univ (m + 1) ω) at e
      linarith
    · intro j
      have e := congrArg (fun X => X ω) (hs j)
      change W (j + 1) ω - V (j + 1) ω - (E' (j + 1) ω - (K (j + 1) ω - K j ω)) =
        H (j + 1) (exteriorDerivativeTestOn univ (m + 1) ω) at e
      linarith
  -- Step 5: `β_j = V_j(dη) − Y_j(η)` sums to `Q₀(dη) − Σ_j Y_j(η)` (`ME` (ii)(a)); by (I3)–(I4),
  -- `β₀ = −L′₀(η)` and `β_{j+1} = L′_j(η) − L′_{j+1}(η)`, with `L′_j(η) → 0` (`ME` (i))
  have hbd : ∀ η : TestFormOn (univ : Set (Euclid P)) m,
      HasSum (fun j => Y j η) (Q₀.boundary η) := by
    intro η
    have hYs := ((hME0 Y).2 hYfin).1 η
    have hsum := (hQs (exteriorDerivativeTestOn univ m η)).sub hYs.hasSum
    have hz := Submission.cmcsdtd_hasSum_telescoping_eq_zero _ (fun j => L' j η) _ hsum ?_ ?_
      ((hME0 L').1 hLlim η)
    · have hq : Q₀.boundary η = ∑' j, Y j η := by
        change Q₀ (exteriorDerivativeTestOn univ m η) = _
        linarith
      rw [hq]
      exact hYs.hasSum
    · have e := congrArg (fun X => X η) hb0
      change V 0 (exteriorDerivativeTestOn univ m η) = Y 0 η - L' 0 η at e
      linarith
    · intro j
      have e := congrArg (fun X => X η) (hbs j)
      change V (j + 1) (exteriorDerivativeTestOn univ m η) =
        Y (j + 1) η - (L' (j + 1) η - L' j η) at e
      linarith
  -- Step 6: `M(∂Q₀) ≤ Σ_j M(Y_j) ≤ Σ_j b_j` (`ME` (ii)(b))
  have hbdm : Q₀.boundary.mass ≤ ∑' j, b j :=
    (((hME0 Y).2 hYfin).2 Q₀.boundary hbd).trans hYsum
  -- Step 7: off `K₃` every `Y_j` vanishes (`(VO)`, `spt Y_j ⊆ K₃`), hence so does `∂Q₀`; `(S-i)`
  have hbdspt : Q₀.boundary.support ⊆ K₃ := by
    refine hSi K₃ Q₀.boundary hK₃ fun η hη => ?_
    have hY0 : (fun j => Y j η) = fun _ => (0 : ℝ) := funext fun j =>
      hVO P m univ (Y j) η (hη.mono_right (hspt j).2.2.1)
    have h := hbd η
    rw [hY0] at h
    exact h.unique hasSum_zero
  -- Step 8: `spt` of a sum lies in `closure ⋃_j spt ⊆ K_i`, as `K_i` is closed
  refine ⟨Q₀, R₁, S₁, hQim fun j => (hIM j).1, hRim fun j => (hIM j).2, hid,
    hQspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).1) hK₁),
    hRspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).2.1) hK₂), hbdspt,
    hSspt.trans (closure_minimal (iUnion_subset fun j => (hspt j).2.2.2) hK₃),
    hQm.trans hVsum, hbdm, hRm.trans hHsum, hSm.trans hEsum⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
