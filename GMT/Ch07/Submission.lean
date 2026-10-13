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

/-- **Blow-ups of a region boundary** (Simon 7.5.1, `T = ∂[[E]]`; 6.2.23, `η_#T(ω) = T(η^#ω)`):
if `T = ∂[[E]]` in `U` with orientation `ξN`, then for `λ > 0` the blow-up `η_{y,λ#}T` is
`∂[[η_{y,λ}(E)]]` in `η_{y,λ}(U)` with orientation `w ↦ ξN(y + λw)`.  For `ω ∈ 𝒟ⁿ(η(U))` and
`ω' = ω ∘ η ∈ 𝒟ⁿ(U)`, `η_#T(ω) = λ⁻ⁿ T(ω')`; `ω' = λⁿ η^#ω` and `d` commutes with the affine
pull-back, so `dω'(z) = λ⁻¹ dω(η(z))`; the change of variables
`∫_{η(E)} g dH^{n+1} = λ^{-(n+1)} ∫_E g ∘ η dH^{n+1}` cancels the powers of `λ`. -/
theorem Submission.codim1_zsl_blowUp_isBoundaryOfRegion : ∀ (P n : ℕ) (U E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (y : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsBoundaryOfRegion T E ξN → IsBoundaryOfRegion (blowUp T y lam hlam.ne') (dilation y lam '' E) (fun w => ξN (y + lam • w)) := by
  intro P n U E ξN T y lam hlam hT ω
  have hne : lam ≠ 0 := hlam.ne'
  -- Steps 1–2: `ω' := ω ∘ η ∈ 𝒟ⁿ(U)`, `η_#T(ω) = λ⁻ⁿ T(ω')`, and `T(ω') = ∫_E ξN (dω')`.
  obtain ⟨ω', hω'⟩ := (Submission.dtc_blowUp_testForm_corr P n U y lam hlam).1 ω
  rw [(Submission.dtc_blowUp_testForm_corr P n U y lam hlam).2.2 T ω ω' hω', hT ω']
  -- Step 3: the affine pull-back `η^#α` of a `k`-form is `λ⁻ᵏ α ∘ η` (multilinearity), so
  -- `ω' = λⁿ η^#ω` and `dω' = λⁿ η^#(dω) = λ⁻¹ (dω) ∘ η`.
  have hpull : ∀ {k : ℕ} (α : DifferentialForm (Euclid P) k) (z : Euclid P),
      affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y)) α z =
        lam⁻¹ ^ k • α (dilation y lam z) := by
    intro k α z
    ext v
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hω'eq : (ω' : DifferentialForm (Euclid P) n) =
      lam ^ n • affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y))
        (ω : DifferentialForm (Euclid P) n) := by
    funext z
    rw [Pi.smul_apply, hpull, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul, hω' z]
  have hdω' : ∀ z, exteriorDerivative (ω' : DifferentialForm (Euclid P) n) z =
      lam⁻¹ • exteriorDerivative (ω : DifferentialForm (Euclid P) n) (dilation y lam z) := by
    intro z
    rw [hω'eq, exteriorDerivative_smul, exteriorDerivative_affinePullbackForm _ _ ω.property.1.1,
      Pi.smul_apply, hpull, smul_smul, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne,
      one_pow, one_mul]
  -- Steps 5–6: `y + λ η(z) = z`, `blowUpMap y λ = η`, and the change of variables.
  have hηinv : ∀ z, y + lam • dilation y lam z = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hbl : Poincare.SimonGMT.Chapter03.blowUpMap y lam = dilation y lam := by
    funext z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub, sub_eq_neg_add]
    simp [dilation, dilationCLM]
  have hcov := Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul P (n + 1) E y lam hlam
    (fun w => ξN (y + lam • w) (exteriorDerivative (ω : DifferentialForm (Euclid P) n) w))
  simp only [hbl, hηinv] at hcov
  -- Steps 4 and 7: pull `λ⁻¹` out of the integral; `λ⁻ⁿ · λ⁻¹ = λ^{-(n+1)}`.
  simp only [hcov, hdω', map_smul, smul_eq_mul, integral_const_mul]
  ring

/-- **Uniform local mass bound for blow-ups with converging centres** (Simon 7.5.3 and 7.5.5,
chapter-07.txt lines 790–901).  If `xᵢ → x`, `λᵢ → 0` (`λᵢ > 0`) and `M_{B_ρ(y)}(T) ≤ Cρⁿ` for
`y ∈ B_{r₀}(x)`, `0 < ρ < r₀`, then for each `R > 0` and all large `i`,
`η_{xᵢ,λᵢ#}T(ω) ≤ max(C, 0)Rⁿ` for every `ω ∈ 𝒟ⁿ(ℝᴾ)` with `spt ω ⊆ B_R(0)` and `|ω| ≤ 1`.  If
`spt ω ⊄ η_{xᵢ,λᵢ}(U)` the value is `0`; otherwise `η_{xᵢ,λᵢ#}T(ω) = λᵢ⁻ⁿ T(ω')` with
`ω' = ω ∘ η_{xᵢ,λᵢ}` admissible for `M_{B_{λᵢR}(xᵢ)}(T) ≤ C(λᵢR)ⁿ`. -/
theorem Submission.codim1_zsl_gbl_blowUp_mass_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i), Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ y ∈ ball x r₀, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) y) ≤ 1) → currentEval (blowUp T (xs i) (lams i) (hlams i).ne') (ω : DifferentialForm (Euclid P) n) ≤ c := by
  intro P n U T x xs lams hlams hxs hlam hmass R hR
  obtain ⟨C, r₀, hr₀, hmass⟩ := hmass
  refine ⟨max C 0 * R ^ n, ?_⟩
  -- Step 1: for all large `i`, `xᵢ ∈ B_{r₀}(x)` and `λᵢR < r₀`.
  have hlamR : Tendsto (fun i => lams i * R) atTop (𝓝 0) := by
    simpa using hlam.mul_const R
  filter_upwards [hxs.eventually (ball_mem_nhds x hr₀), hlamR.eventually (gt_mem_nhds hr₀)]
    with i hxi hlRi
  intro ω hωsupp hωnorm
  have hρ : 0 < lams i * R := mul_pos (hlams i) hR
  unfold currentEval
  split_ifs with h
  · -- Step 2: `spt ω ⊆ η(U)`, so `η_{xᵢ,λᵢ#}T(ω) = λᵢ⁻ⁿ T(ω')` with `ω' = ω ∘ η ∈ 𝒟ⁿ(U)`.
    obtain ⟨ω', hω'⟩ := (Submission.dtc_blowUp_testForm_corr P n U (xs i) (lams i) (hlams i)).1
      ⟨(ω : DifferentialForm (Euclid P) n), h⟩
    rw [(Submission.dtc_blowUp_testForm_corr P n U (xs i) (lams i) (hlams i)).2.2 T
      ⟨(ω : DifferentialForm (Euclid P) n), h⟩ ω' hω']
    -- Step 3: `ω'` is admissible for `M_{B_{λᵢR}(xᵢ)}(T)`: `η(z) = λᵢ⁻¹(z − xᵢ)` lies in
    -- `B_R(0)` iff `z ∈ B_{λᵢR}(xᵢ)`, and `|ω'(z)| = |ω(η(z))| ≤ 1`.
    have hdil : ∀ z, dilation (xs i) (lams i) z = (lams i)⁻¹ • (z - xs i) := by
      intro z
      simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_sub]
      abel
    have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ ball (xs i) (lams i * R) := by
      rw [show (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation (xs i) (lams i) from funext hω']
      have hcont : Continuous (dilation (xs i) (lams i)) :=
        continuous_const.add (dilationCLM P (lams i)).continuous
      refine (tsupport_comp_subset_preimage _ hcont).trans fun z hz => ?_
      have hz' := mem_ball_zero_iff.mp (hωsupp hz)
      rw [hdil, norm_smul, norm_inv, Real.norm_of_nonneg (hlams i).le,
        inv_mul_lt_iff₀ (hlams i)] at hz'
      rwa [mem_ball, dist_eq_norm]
    have hadm : ω' ∈ massAdmissibleOn U n (ball (xs i) (lams i * R)) := by
      refine ⟨hsupp, fun z => ?_⟩
      rw [hω' z]
      exact hωnorm _
    -- Step 4: `T(ω') ≤ M_{B_{λᵢR}(xᵢ)}(T) ≤ C(λᵢR)ⁿ`, hence `T(ω') ≤ max(C, 0)(λᵢR)ⁿ`.
    have hT : T ω' ≤ max C 0 * (lams i * R) ^ n := by
      rcases ENNReal.ofReal_le_ofReal_iff'.mp
          ((T.le_massOn hadm).trans (hmass (xs i) hxi (lams i * R) hρ hlRi)) with hT | hT
      · exact hT.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hρ.le n))
      · exact hT.trans (mul_nonneg (le_max_right C 0) (pow_nonneg hρ.le n))
    -- Step 5: `λᵢ⁻ⁿ max(C, 0)(λᵢR)ⁿ = max(C, 0)Rⁿ`.
    calc (lams i)⁻¹ ^ n * T ω' ≤ (lams i)⁻¹ ^ n * (max C 0 * (lams i * R) ^ n) :=
          mul_le_mul_of_nonneg_left hT (pow_nonneg (inv_nonneg.mpr (hlams i).le) n)
      _ = max C 0 * R ^ n := by
          rw [mul_pow, mul_left_comm, ← mul_assoc ((lams i)⁻¹ ^ n), ← mul_pow,
            inv_mul_cancel₀ (hlams i).ne', one_pow, one_mul]
  · -- `spt ω ⊄ η(U)`: the value is `0 ≤ max(C, 0)Rⁿ`.
    exact mul_nonneg (le_max_right C 0) (pow_nonneg hR.le n)
/-- **Flattening of rescaled `C¹` graphs** (Simon 7.5.5: the rescaled sheets of `N` flatten to the
tangent plane).  Let `u` be `C¹` on `B_δ ⊆ ℝᵐ` with `Du(0) = 0`, `sᵢ → 0`, `λᵢ ↓ 0`, and let the
offsets `tᵢ` be such that `gᵢ(w) = λᵢ⁻¹ (u(sᵢ + λᵢ w) − tᵢ)` satisfies `|gᵢ(w)| ≤ C₀` at some
`|w| ≤ C₀`.  Since `Du` is continuous with `Du(0) = 0`, `u` is `η`-Lipschitz with `‖Du‖ < η` on a
small ball (mean value inequality), and `Dgᵢ(w) = Du(sᵢ + λᵢ w)` by the chain rule.  Hence
`|gᵢ(0)| ≤ 2 C₀` eventually; a subsequence `gᵢ(0) → b` (compactness), and on `B_R` the rescalings
converge to the constant `b` in `C¹`. -/
theorem Submission.codim1_zsl_gbl_rescaled_graph_flattening : ∀ (m k : ℕ) (u : Euclid m → Euclid k) (δ C₀ : ℝ) (s : ℕ → Euclid m) (t : ℕ → Euclid k) (lams : ℕ → ℝ), 0 < δ → ContDiffOn ℝ 1 u (ball 0 δ) → fderiv ℝ u 0 = 0 → (∀ i, 0 < lams i) → Tendsto s atTop (𝓝 0) → Tendsto lams atTop (𝓝 0) → (∀ᶠ i in atTop, ∃ w : Euclid m, ‖w‖ ≤ C₀ ∧ s i + lams i • w ∈ ball (0 : Euclid m) δ ∧ ‖u (s i + lams i • w) - t i‖ ≤ C₀ * lams i) → ∃ (σ : ℕ → ℕ) (b : Euclid k), StrictMono σ ∧ (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (fun w => (lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i))) w) ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖(lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i)) - b‖ < ε ∧ ‖fderiv ℝ (fun w => (lams (σ i))⁻¹ • (u (s (σ i) + lams (σ i) • w) - t (σ i))) w‖ < ε := by
  intro m k u δ C₀ s t lams hδ hu hDu0 hlams hs hlam hoff
  -- `u` is differentiable on the open ball `B_δ` and `Du` is continuous there
  have hdiff : ∀ v ∈ ball (0 : Euclid m) δ, DifferentiableAt ℝ u v := fun v hv =>
    (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hv)
  have hcont : ContinuousOn (fderiv ℝ u) (ball (0 : Euclid m) δ) :=
    hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  -- for every `η > 0`: `‖Du‖ < η` and `u` is `η`-Lipschitz on some `B_ρ ⊆ B_δ`
  have hsmall : ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧
      (∀ v ∈ ball (0 : Euclid m) ρ, ‖fderiv ℝ u v‖ < η) ∧
      ∀ v ∈ ball (0 : Euclid m) ρ, ∀ v' ∈ ball (0 : Euclid m) ρ, ‖u v' - u v‖ ≤ η * ‖v' - v‖ := by
    intro η hη
    obtain ⟨ρ₀, hρ₀, hρ₀D⟩ := Metric.continuousOn_iff.1 hcont 0 (mem_ball_self hδ) η hη
    have hD : ∀ v ∈ ball (0 : Euclid m) (min ρ₀ δ), ‖fderiv ℝ u v‖ < η := by
      intro v hv
      have h := hρ₀D v (ball_subset_ball (min_le_right _ _) hv)
        (mem_ball.1 (ball_subset_ball (min_le_left _ _) hv))
      rwa [hDu0, dist_zero_right] at h
    refine ⟨min ρ₀ δ, lt_min hρ₀ hδ, min_le_right _ _, hD, fun v hv v' hv' => ?_⟩
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hdiff x (ball_subset_ball (min_le_right _ _) hx))
      (fun x hx => (hD x hx).le) (convex_ball _ _) hv hv'
  -- chain rule: `Dgᵢ(w) = Du(sᵢ + λᵢ w)` whenever `sᵢ + λᵢ w ∈ B_δ`
  have hchain : ∀ (i : ℕ) (w : Euclid m), s i + lams i • w ∈ ball (0 : Euclid m) δ →
      HasFDerivAt (fun w => (lams i)⁻¹ • (u (s i + lams i • w) - t i))
        (fderiv ℝ u (s i + lams i • w)) w := by
    intro i w hw
    have h1 : HasFDerivAt (fun w : Euclid m => s i + lams i • w)
        (lams i • ContinuousLinearMap.id ℝ (Euclid m)) w :=
      ((hasFDerivAt_id w).const_smul (lams i)).const_add (s i)
    have h2 := (((hdiff _ hw).hasFDerivAt.comp w h1).sub_const (t i)).const_smul (lams i)⁻¹
    refine h2.congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ (hlams i).ne']
  -- `|sᵢ + λᵢ w| ≤ |sᵢ| + λᵢ R` for `|w| ≤ R`, and `|sᵢ| + λᵢ c → 0`
  have hball : ∀ (i : ℕ) (R r : ℝ) (w : Euclid m), ‖w‖ ≤ R → ‖s i‖ + lams i * R < r →
      s i + lams i • w ∈ ball (0 : Euclid m) r := by
    intro i R r w hw hr
    rw [mem_ball_zero_iff]
    have hmul : lams i * ‖w‖ ≤ lams i * R := mul_le_mul_of_nonneg_left hw (hlams i).le
    calc ‖s i + lams i • w‖ ≤ ‖s i‖ + ‖lams i • w‖ := norm_add_le _ _
      _ = ‖s i‖ + lams i * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (hlams i).le]
      _ < r := by linarith
  have htend : ∀ c : ℝ, Tendsto (fun i => ‖s i‖ + lams i * c) atTop (𝓝 0) := by
    intro c
    simpa using hs.norm.add (hlam.mul_const c)
  -- `C₀ ≥ 0`, witnessed by some offset point
  have hC₀ : 0 ≤ C₀ := by
    obtain ⟨i, w, hw, -, -⟩ := hoff.exists
    exact (norm_nonneg w).trans hw
  -- `|gᵢ(0)| ≤ 2 C₀` for all `i ≥ i₂`
  obtain ⟨ρ₁, hρ₁, -, -, hlip₁⟩ := hsmall 1 one_pos
  obtain ⟨i₂, hi₂⟩ := eventually_atTop.1 (hoff.and ((htend C₀).eventually_lt_const hρ₁))
  have hbound : ∀ j, (lams (i₂ + j))⁻¹ • (u (s (i₂ + j)) - t (i₂ + j)) ∈
      closedBall (0 : Euclid k) (2 * C₀) := by
    intro j
    obtain ⟨⟨w, hw, -, hut⟩, hlt⟩ := hi₂ (i₂ + j) (Nat.le_add_right _ _)
    have hl0 := hlams (i₂ + j)
    have hs0 : s (i₂ + j) ∈ ball (0 : Euclid m) ρ₁ := by
      simpa using hball (i₂ + j) C₀ ρ₁ 0 (by simpa using hC₀) hlt
    have hsw := hball (i₂ + j) C₀ ρ₁ w hw hlt
    have h1 := hlip₁ _ hsw _ hs0
    have hmul : lams (i₂ + j) * ‖w‖ ≤ lams (i₂ + j) * C₀ := mul_le_mul_of_nonneg_left hw hl0.le
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hl0.le,
      inv_mul_le_iff₀ hl0]
    calc ‖u (s (i₂ + j)) - t (i₂ + j)‖
        ≤ ‖u (s (i₂ + j)) - u (s (i₂ + j) + lams (i₂ + j) • w)‖ +
          ‖u (s (i₂ + j) + lams (i₂ + j) • w) - t (i₂ + j)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 * ‖s (i₂ + j) - (s (i₂ + j) + lams (i₂ + j) • w)‖ + C₀ * lams (i₂ + j) :=
          add_le_add h1 hut
      _ = lams (i₂ + j) * ‖w‖ + C₀ * lams (i₂ + j) := by
          rw [one_mul, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hl0.le]
      _ ≤ lams (i₂ + j) * (2 * C₀) := by linarith
  -- a subsequence along which `gᵢ(0) → b`
  obtain ⟨b, -, φ, hφ, hφb⟩ := (isCompact_closedBall (0 : Euclid k) (2 * C₀)).tendsto_subseq hbound
  obtain ⟨σ, hσ, hg0⟩ : ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun j => (lams (σ j))⁻¹ • (u (s (σ j)) - t (σ j))) atTop (𝓝 b) :=
    ⟨fun j => i₂ + φ j, fun a a' h => Nat.add_lt_add_left (hφ h) i₂, hφb⟩
  refine ⟨σ, b, hσ, ?_, ?_⟩
  · -- (H1): differentiability on `B_R`
    intro R hR
    filter_upwards [((htend R).comp hσ.tendsto_atTop).eventually_lt_const hδ] with j hj w hw
    exact (hchain (σ j) w (hball (σ j) R δ w (mem_ball_zero_iff.1 hw).le hj)).differentiableAt
  · -- (H2): `C¹`-closeness to the constant `b` on `B_R`
    intro R ε hR hε
    have hηpos : 0 < min ε (ε / (2 * R)) := lt_min hε (by positivity)
    have hηR : min ε (ε / (2 * R)) * R ≤ ε / 2 := by
      calc min ε (ε / (2 * R)) * R ≤ ε / (2 * R) * R :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
        _ = ε / 2 := by field_simp
    obtain ⟨ρ, hρ, hρδ, hD, hlip⟩ := hsmall _ hηpos
    filter_upwards [((htend R).comp hσ.tendsto_atTop).eventually_lt_const hρ,
      hg0.eventually (ball_mem_nhds b (half_pos hε))] with j hj hgj w hw
    have hl0 := hlams (σ j)
    have hwR : ‖w‖ < R := mem_ball_zero_iff.1 hw
    have hsw : s (σ j) + lams (σ j) • w ∈ ball (0 : Euclid m) ρ := hball (σ j) R ρ w hwR.le hj
    have hs0 : s (σ j) ∈ ball (0 : Euclid m) ρ := by
      simpa using hball (σ j) R ρ 0 (by simpa using hR.le) hj
    have hfd := (hchain (σ j) w (ball_subset_ball hρδ hsw)).fderiv
    refine ⟨?_, ?_⟩
    · have hl := hlip _ hs0 _ hsw
      have hηw : min ε (ε / (2 * R)) * ‖w‖ ≤ ε / 2 :=
        (mul_le_mul_of_nonneg_left hwR.le hηpos.le).trans hηR
      calc ‖(lams (σ j))⁻¹ • (u (s (σ j) + lams (σ j) • w) - t (σ j)) - b‖
          ≤ ‖(lams (σ j))⁻¹ • (u (s (σ j) + lams (σ j) • w) - t (σ j)) -
              (lams (σ j))⁻¹ • (u (s (σ j)) - t (σ j))‖ +
            ‖(lams (σ j))⁻¹ • (u (s (σ j)) - t (σ j)) - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add_of_le_of_lt ?_ (mem_ball_iff_norm.1 hgj)
            rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, norm_inv,
              Real.norm_of_nonneg hl0.le, inv_mul_le_iff₀ hl0]
            calc ‖u (s (σ j) + lams (σ j) • w) - u (s (σ j))‖
                ≤ min ε (ε / (2 * R)) * ‖s (σ j) + lams (σ j) • w - s (σ j)‖ := hl
              _ = lams (σ j) * (min ε (ε / (2 * R)) * ‖w‖) := by
                  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hl0.le]; ring
              _ ≤ lams (σ j) * (ε / 2) := mul_le_mul_of_nonneg_left hηw hl0.le
        _ = ε := add_halves ε
    · rw [hfd]
      exact (hD _ hsw).trans_le (min_le_left _ _)
/-- **Chart coordinates of the blow-up centres and bounded offsets of nearby carrier points**
(Simon 7.5.5, steps 1 and 3 of the graph blow-up limit, chapter-07.txt lines 790–901).  Let
`ι : ℝᵐ → ℝᴾ`, `ι' : ℝᵏ → ℝᴾ` be linear isometries with orthogonal ranges spanning `ℝᴾ`, and let
`N` be the graph `{x + ιv + ι'u(v) : |v| < δ₁}` of `u` inside the chart
`{x + ιv + ι'w : |v| < δ₁, |w| < δ₂}`.  If `xᵢ → x`, `λᵢ ↓ 0` and each `xᵢ` is within `C₀λᵢ` of
some `pᵢ ∈ N`, then `xᵢ = x + ιsᵢ + ι'tᵢ` with `sᵢ, tᵢ → 0`, and for all large `i` the offset
`w = λᵢ⁻¹(v − sᵢ)` of `pᵢ = x + ιv + ι'u(v)` satisfies `|w| ≤ C₀`, `sᵢ + λᵢw ∈ B_{δ₁}(0)` and
`|u(sᵢ + λᵢw) − tᵢ| ≤ C₀λᵢ`.  The key estimate is Pythagoras: `|ιa + ι'b|² = |a|² + |b|²`. -/
theorem Submission.codim1_zsl_gbl_centre_chart_offsets : ∀ (m k P : ℕ) (N : Set (Euclid P)) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (u : Euclid m → Euclid k) (δ₁ δ₂ C₀ : ℝ), Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∀ i, 0 < lams i) → (∀ i, ∃ p ∈ N, dist p (xs i) ≤ C₀ * lams i) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid P, ∃ v w, y = ι v + ι' w) → 0 < δ₁ → 0 < δ₂ → N ∩ {y | ∃ v ∈ ball (0 : Euclid m) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid m) δ₁ → ∃ (s : ℕ → Euclid m) (t : ℕ → Euclid k), (∀ i, xs i = x + ι (s i) + ι' (t i)) ∧ Tendsto s atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 0) ∧ ∀ᶠ i in atTop, ∃ w : Euclid m, ‖w‖ ≤ C₀ ∧ s i + lams i • w ∈ ball (0 : Euclid m) δ₁ ∧ ‖u (s i + lams i • w) - t i‖ ≤ C₀ * lams i := by
  intro m k P N x xs lams ι ι' u δ₁ δ₂ C₀ hxs hlams hlpos hnear horth hspan hδ₁ hδ₂ hchart
  -- Step 1 (Pythagoras): `|ιa + ι'b|² = |a|² + |b|²`, hence `|a|, |b| ≤ |ιa + ι'b|`.
  have hpyth : ∀ (a : Euclid m) (b : Euclid k), ‖a‖ ≤ ‖ι a + ι' b‖ ∧ ‖b‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have hsq : ‖ι a + ι' b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      rw [norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
      ring
    constructor
    · rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hsq]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hsq]
      exact le_add_of_nonneg_left (sq_nonneg _)
  -- Step 2 (coordinates of the centres): `xᵢ − x = ιsᵢ + ι'tᵢ` and `|sᵢ|, |tᵢ| ≤ |xᵢ − x| → 0`.
  choose s t hst using fun i => hspan (xs i - x)
  have hcentre : ∀ i, xs i = x + ι (s i) + ι' (t i) := by
    intro i
    rw [add_assoc, ← hst i, add_sub_cancel]
  have hxs0 : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hxs
  have hst_le : ∀ i, ‖s i‖ ≤ ‖xs i - x‖ ∧ ‖t i‖ ≤ ‖xs i - x‖ := by
    intro i
    rw [hst i]
    exact hpyth (s i) (t i)
  have hs : Tendsto s atTop (𝓝 0) := squeeze_zero_norm (fun i => (hst_le i).1) hxs0
  have ht : Tendsto t atTop (𝓝 0) := squeeze_zero_norm (fun i => (hst_le i).2) hxs0
  -- Step 3 (nearby carrier points converge to `x`): `|pᵢ − x| ≤ |C₀|λᵢ + |xᵢ − x| → 0`.
  choose p hpN hpd using hnear
  have hbound : ∀ i, ‖p i - x‖ ≤ |C₀| * lams i + ‖xs i - x‖ := by
    intro i
    calc ‖p i - x‖ = ‖(p i - xs i) + (xs i - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖p i - xs i‖ + ‖xs i - x‖ := norm_add_le _ _
      _ ≤ |C₀| * lams i + ‖xs i - x‖ := by
        gcongr
        rw [← dist_eq_norm]
        exact (hpd i).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) (hlpos i).le)
  have hlim : Tendsto (fun i => |C₀| * lams i + ‖xs i - x‖) atTop (𝓝 0) := by
    have h := (hlams.const_mul |C₀|).add hxs0
    rwa [mul_zero, add_zero] at h
  have hp : Tendsto (fun i => ‖p i - x‖) atTop (𝓝 0) :=
    squeeze_zero (fun i => norm_nonneg _) hbound hlim
  have hev : ∀ᶠ i in atTop, ‖p i - x‖ < min δ₁ δ₂ := (tendsto_order.1 hp).2 _ (lt_min hδ₁ hδ₂)
  refine ⟨s, t, hcentre, hs, ht, ?_⟩
  filter_upwards [hev] with i hi
  -- Step 4 (`pᵢ` lies on the graph): `pᵢ − x = ιa + ι'b` with `|a| < δ₁`, `|b| < δ₂`, so the
  -- chart identity gives `pᵢ = x + ιv + ι'u(v)` with `|v| < δ₁`.
  obtain ⟨a, b, hab⟩ := hspan (p i - x)
  have hpab : ‖ι a + ι' b‖ = ‖p i - x‖ := by rw [hab]
  have hmem : p i ∈ N ∩ {y | ∃ v ∈ ball (0 : Euclid m) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂,
      y = x + ι v + ι' w} := by
    refine ⟨hpN i, a, ?_, b, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      exact ((hpyth a b).1.trans_eq hpab).trans_lt (hi.trans_le (min_le_left _ _))
    · rw [mem_ball_zero_iff]
      exact ((hpyth a b).2.trans_eq hpab).trans_lt (hi.trans_le (min_le_right _ _))
    · rw [add_assoc, ← hab, add_sub_cancel]
  rw [hchart] at hmem
  obtain ⟨v, hv, hpv⟩ := hmem
  have hpv' : x + ι v + ι' (u v) = p i := hpv
  -- Step 5 (the offset `w = λᵢ⁻¹(v − sᵢ)`): `pᵢ − xᵢ = ι(v − sᵢ) + ι'(u(v) − tᵢ)`, so by Step 1
  -- `|v − sᵢ|, |u(v) − tᵢ| ≤ |pᵢ − xᵢ| ≤ C₀λᵢ`.
  have hdiff : p i - xs i = ι (v - s i) + ι' (u v - t i) := by
    rw [← hpv', hcentre i, map_sub, map_sub]
    abel
  have hd : ‖ι (v - s i) + ι' (u v - t i)‖ ≤ C₀ * lams i := by
    rw [← hdiff, ← dist_eq_norm]
    exact hpd i
  have hl := hlpos i
  have hsv : s i + lams i • ((lams i)⁻¹ • (v - s i)) = v := by
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, add_sub_cancel]
  refine ⟨(lams i)⁻¹ • (v - s i), ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hl, inv_mul_le_iff₀ hl, mul_comm]
    exact (hpyth (v - s i) (u v - t i)).1.trans hd
  · rw [hsv]
    exact hv
  · rw [hsv]
    exact (hpyth (v - s i) (u v - t i)).2.trans hd
/-- Graph representation of a blow-up of `T = ∂[[E]]` (used in the proof of Simon 7.5.5,
pp. 199–200).  Let `Γ(v) = x + ιv + ι'u(v)` be a `C¹` graph chart of `N` over `B_{δ₁}`
(`ι, ι'` orthogonal isometries spanning `ℝ^{n+1+k}`) whose Jacobian orients `ξN`, let
`y = x + ιs + ι't`, `G(w) = ιw + ι'(λ⁻¹(u(s + λw) − t))` and
`F' = {w : s + λw ∈ B_{δ₁}, Γ(s + λw) ∈ E}`.  If `η_{y,λ#}T = ∂[[η_{y,λ}(E)]]` and the area
formula for `C¹` graphs holds, then `F'` is measurable and
`η_{y,λ#}T(ω) = ∫_{F' ∩ B_R} dω(G(w))(DG(w)e₀, …, DG(w)eₙ) dw` for `ω ∈ 𝒟ⁿ(ℝ^{n+1+k})` with
`spt ω ⊆ B_R`, whenever `|s| + λR < δ₁`, `|t| + λR < δ₂` and `B_{λR}(y) ⊆ U`.  Here
`y + λG(w) = Γ(s + λw)` and `DG(w) = DΓ(s + λw)`; Pythagoras and the chart identity give
`η_{y,λ}(E) ∩ B_R ⊆ G(F' ∩ B_R) ⊆ η_{y,λ}(E)`, and `dω = 0` off `B_R`. -/
theorem Submission.codim1_zsl_gbl_blowUp_graph_representation : ∀ (n k : ℕ) (U N E : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (T : GeometricCurrentOn U n) (x y : Euclid (n + 1 + k)) (lam : ℝ) (hlam : 0 < lam) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ₁ δ₂ : ℝ) (s : Euclid (n + 1)) (t : Euclid k), MeasurableSet E → E ⊆ N → IsBoundaryOfRegion (blowUp T y lam hlam.ne') (dilation y lam '' E) (fun z => ξN (y + lam • z)) → (∀ (g : Euclid (n + 1) → Euclid k) (D A : Set (Euclid (n + 1))) (f : Euclid (n + 1 + k) → ℝ), IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → ∫ z in (fun w => ι w + ι' (g w)) '' A, f z ∂μHE[n + 1] = ∫ w in A, Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det) * f (ι w + ι' (g w))) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ z : Euclid (n + 1 + k), ∃ v w, z = ι v + ι' w) → ContDiffOn ℝ 1 u (ball 0 δ₁) → N ∩ {z | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, z = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid (n + 1)) δ₁ → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α) → y = x + ι s + ι' t → MeasurableSet {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∧ ∀ R : ℝ, ‖s‖ + lam * R < δ₁ → ‖t‖ + lam * R < δ₂ → ball y (lam * R) ⊆ U → ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (blowUp T y lam hlam.ne') (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) (fun j => fderiv ℝ (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) w (EuclideanSpace.single j (1 : ℝ))) := by
  intro n k U N E ξN T x y lam hlam ι ι' u δ₁ δ₂ s t hE hEN hbd harea horth hspan hu hchart
    hjac hy
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- Step 1: measurability of F'
  have hΓcont : ContinuousOn (fun v => x + ι v + ι' (u v)) (ball (0 : Euclid (n + 1)) δ₁) := by
    have hcu : ContinuousOn u (ball (0 : Euclid (n + 1)) δ₁) := hu.continuousOn
    exact (continuousOn_const.add ι.continuous.continuousOn).add
      (ι'.continuous.comp_continuousOn hcu)
  have hA₀ : MeasurableSet {v : Euclid (n + 1) | v ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι v + ι' (u v) ∈ E} := by
    classical
    have hpw : Measurable ((ball (0 : Euclid (n + 1)) δ₁).piecewise
        (fun v => x + ι v + ι' (u v)) (fun _ => (0 : Euclid (n + 1 + k)))) :=
      hΓcont.measurable_piecewise continuousOn_const measurableSet_ball
    have heq : {v : Euclid (n + 1) | v ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
        x + ι v + ι' (u v) ∈ E} = ball (0 : Euclid (n + 1)) δ₁ ∩
          (ball (0 : Euclid (n + 1)) δ₁).piecewise (fun v => x + ι v + ι' (u v))
            (fun _ => (0 : Euclid (n + 1 + k))) ⁻¹' E := by
      ext v
      simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hv, hvE⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv]⟩
      · rintro ⟨hv, hvE⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv] at hvE⟩
    rw [heq]
    exact measurableSet_ball.inter (hpw hE)
  have haff : Continuous (fun w : Euclid (n + 1) => s + lam • w) :=
    continuous_const.add (continuous_id.const_smul lam)
  have hF : MeasurableSet {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} :=
    haff.measurable hA₀
  refine ⟨hF, ?_⟩
  intro R hR1 hR2 hRU ω hω
  set F' := {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E}
  -- Step 2: the dilation
  have hdil : ∀ z : Euclid (n + 1 + k), dilation y lam (y + lam • z) = z := by
    intro z
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply,
      smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    abel
  have hdil' : ∀ e : Euclid (n + 1 + k), y + lam • dilation y lam e = e := by
    intro e
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply,
      smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    abel
  have hηE : dilation y lam '' E = (fun z => y + lam • z) ⁻¹' E := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa [hdil' e] using he
    · intro hz
      exact ⟨y + lam • z, hz, hdil z⟩
  have hηEmeas : MeasurableSet (dilation y lam '' E) := by
    rw [hηE]
    exact (continuous_const.add (continuous_id.const_smul lam)).measurable hE
  have hballU : ball (0 : Euclid (n + 1 + k)) R ⊆ dilation y lam '' U := by
    intro z hz
    refine ⟨y + lam • z, hRU ?_, hdil z⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_ball, dist_zero_right] at hz
    exact mul_lt_mul_of_pos_left hz hlam
  -- Step 3: evaluation of the blow-up
  have hωtest : IsTestForm (ω : DifferentialForm (Euclid (n + 1 + k)) n) := ω.2.1
  have hcur : currentEval (blowUp T y lam hlam.ne') (ω : DifferentialForm (Euclid (n + 1 + k)) n) =
      ∫ z in dilation y lam '' E, ξN (y + lam • z)
        (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z) ∂μHE[n + 1] := by
    have h : IsTestForm (ω : DifferentialForm (Euclid (n + 1 + k)) n) ∧
        tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ dilation y lam '' U :=
      ⟨hωtest, hω.trans hballU⟩
    unfold currentEval
    rw [dite_eq_left h]
    exact hbd ⟨ω, h⟩
  -- Step 4: Pythagoras and (4.1)
  have hpyth : ∀ (a : Euclid (n + 1)) (b : Euclid k),
      ‖a‖ ≤ ‖ι a + ι' b‖ ∧ ‖b‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth a b)
    rw [ι.norm_map, ι'.norm_map] at h
    have h0 := norm_nonneg (ι a + ι' b)
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    constructor <;> nlinarith
  have h41 : ∀ w : Euclid (n + 1),
      y + lam • (ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) =
        x + ι (s + lam • w) + ι' (u (s + lam • w)) := by
    intro w
    rw [hy]
    simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hlam0,
      one_smul]
    abel
  -- Step 5: Y ⊆ η(E)
  set G : Euclid (n + 1) → Euclid (n + 1 + k) :=
    fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))
  have hYsub : G '' (F' ∩ ball 0 R) ⊆ dilation y lam '' E := by
    rintro _ ⟨w, ⟨hwF, _⟩, rfl⟩
    rw [hηE, mem_preimage]
    simp only [G]
    rw [h41 w]
    exact hwF.2
  -- Step 6: f vanishes on η(E) \ Y
  have hvan : ∀ z ∈ dilation y lam '' E \ G '' (F' ∩ ball 0 R),
      ξN (y + lam • z)
        (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z) = 0 := by
    rintro z ⟨hzE, hzY⟩
    by_cases hzR : z ∈ ball (0 : Euclid (n + 1 + k)) R
    · exfalso
      apply hzY
      rw [hηE, mem_preimage] at hzE
      obtain ⟨a, b, hzab⟩ := hspan z
      have hzn : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hzR
      obtain ⟨ha, hb⟩ := hpyth a b
      rw [← hzab] at ha hb
      have he : y + lam • z = x + ι (s + lam • a) + ι' (t + lam • b) := by
        rw [hy, hzab]
        simp only [map_add, map_smul, smul_add]
        abel
      have hsa : s + lam • a ∈ ball (0 : Euclid (n + 1)) δ₁ := by
        rw [mem_ball, dist_zero_right]
        calc ‖s + lam • a‖ ≤ ‖s‖ + ‖lam • a‖ := norm_add_le _ _
          _ = ‖s‖ + lam * ‖a‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
          _ < ‖s‖ + lam * R := by
            have := mul_lt_mul_of_pos_left (ha.trans_lt hzn) hlam
            linarith
          _ < δ₁ := hR1
      have htb : t + lam • b ∈ ball (0 : Euclid k) δ₂ := by
        rw [mem_ball, dist_zero_right]
        calc ‖t + lam • b‖ ≤ ‖t‖ + ‖lam • b‖ := norm_add_le _ _
          _ = ‖t‖ + lam * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
          _ < ‖t‖ + lam * R := by
            have := mul_lt_mul_of_pos_left (hb.trans_lt hzn) hlam
            linarith
          _ < δ₂ := hR2
      have hmem : y + lam • z ∈ N ∩ {z | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁,
          ∃ w ∈ ball (0 : Euclid k) δ₂, z = x + ι v + ι' w} :=
        ⟨hEN hzE, s + lam • a, hsa, t + lam • b, htb, he⟩
      rw [hchart] at hmem
      obtain ⟨v, hv, hve⟩ := hmem
      have hsw : s + lam • (lam⁻¹ • (v - s)) = v := by
        rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul]
        abel
      simp only at hve
      have hGw : G (lam⁻¹ • (v - s)) = z := by
        apply smul_right_injective _ hlam0
        apply add_left_cancel (a := y)
        show y + lam • (ι (lam⁻¹ • (v - s)) + ι' (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t))) =
          y + lam • z
        rw [h41 (lam⁻¹ • (v - s)), hsw]
        exact hve
      refine ⟨lam⁻¹ • (v - s), ⟨⟨?_, ?_⟩, ?_⟩, hGw⟩
      · rw [hsw]; exact hv
      · rw [hsw, hve]; exact hzE
      · -- |w| ≤ |G w| = |z| < R
        have := (hpyth (lam⁻¹ • (v - s)) (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t))).1
        rw [mem_ball, dist_zero_right]
        have hGw' : ι (lam⁻¹ • (v - s)) + ι' (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t)) = z :=
          hGw
        rw [hGw'] at this
        exact this.trans_lt hzn
    · have hzt : z ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n)) :=
        fun h => hzR (hω (tsupport_exteriorDerivative_subset _ h))
      rw [image_eq_zero_of_notMem_tsupport hzt, map_zero]
  -- Step 7: restriction of the integral
  have hrestr := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := μHE[n + 1])
    (f := fun z => ξN (y + lam • z)
      (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z)) hηEmeas hYsub hvan
  -- Step 8: area formula
  set D : Set (Euclid (n + 1)) := (fun w => s + lam • w) ⁻¹' ball (0 : Euclid (n + 1)) δ₁
  have hDopen : IsOpen D := isOpen_ball.preimage haff
  have hgC1 : ContDiffOn ℝ 1 (fun w => lam⁻¹ • (u (s + lam • w) - t)) D := by
    have haffC : ContDiff ℝ 1 (fun w : Euclid (n + 1) => s + lam • w) :=
      contDiff_const.add (contDiff_id.const_smul lam)
    have h1 : ContDiffOn ℝ 1 (fun w => u (s + lam • w)) D :=
      hu.comp haffC.contDiffOn (fun w hw => hw)
    exact (h1.sub contDiffOn_const).const_smul lam⁻¹
  have hAmeas : MeasurableSet (F' ∩ ball (0 : Euclid (n + 1)) R) := hF.inter measurableSet_ball
  have hAD : F' ∩ ball (0 : Euclid (n + 1)) R ⊆ D := fun w hw => hw.1.1
  have harea' := harea (fun w => lam⁻¹ • (u (s + lam • w) - t)) D (F' ∩ ball 0 R)
    (fun z => ξN (y + lam • z) (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z))
    hDopen hgC1 hAmeas hAD
  -- Step 9: the derivative of G
  have hDG : ∀ w ∈ D, fderiv ℝ (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) w =
      fderiv ℝ (fun v => x + ι v + ι' (u v)) (s + lam • w) := by
    intro w hw
    have hv : s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ := hw
    have hud : DifferentiableAt ℝ u (s + lam • w) :=
      (hu.differentiableOn one_ne_zero _ hv).differentiableAt (isOpen_ball.mem_nhds hv)
    set L := fderiv ℝ u (s + lam • w)
    have hLd : HasFDerivAt u L (s + lam • w) := hud.hasFDerivAt
    have haffd : HasFDerivAt (fun w : Euclid (n + 1) => s + lam • w)
        (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1))) w :=
      (((ContinuousLinearMap.id ℝ (Euclid (n + 1))).hasFDerivAt (x := w)).const_smul
        lam).const_add s
    have hcomp : HasFDerivAt (fun w => u (s + lam • w))
        (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1)))) w :=
      hLd.comp w haffd
    have hg : HasFDerivAt (fun w => lam⁻¹ • (u (s + lam • w) - t))
        (lam⁻¹ • (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1))))) w :=
      (hcomp.sub_const t).const_smul lam⁻¹
    have hLeq : lam⁻¹ • (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1)))) = L := by
      ext1 e
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [hLeq] at hg
    have hG : HasFDerivAt (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t)))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp L) w :=
      (ι.toContinuousLinearMap.hasFDerivAt).add (ι'.toContinuousLinearMap.hasFDerivAt.comp w hg)
    have hΓd : HasFDerivAt (fun v => x + ι v + ι' (u v))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp L) (s + lam • w) :=
      ((ι.toContinuousLinearMap.hasFDerivAt (x := s + lam • w)).const_add x).add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp (s + lam • w) hLd)
    rw [hG.fderiv, hΓd.fderiv]
  -- Steps 10-11: pointwise identity and conclusion
  rw [hcur, hrestr]
  simp only [G]
  rw [harea']
  refine setIntegral_congr_fun hAmeas ?_
  intro w hw
  have hwD : w ∈ D := hAD hw
  have hv : s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ := hwD
  simp only
  rw [hDG w hwD, h41 w]
  exact (hjac (s + lam • w) hv _).symm
/-- Steps 1–2 of the local comparison for a graph (Simon 7.5, codimension one regularity): for
linear isometries `ι : ℝᵐ → ℝ^{m+k}`, `ι' : ℝᵏ → ℝ^{m+k}` with `⟨ιv, ι'w⟩ = 0` and `g`
differentiable at `w₀`, the graph map `G(w) = ιw + ι'g(w)` has `DG(w₀) = ι + ι' ∘ Dg(w₀)`, and
`|h| ≤ |DG(w₀)h|` because `|DG(w₀)h|² = |h|² + |Dg(w₀)h|²`. -/
theorem Submission.codim1_zsl_ga_lc_graph_fderiv : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ g w₀ → fderiv ℝ (fun w => ι w + ι' (g w)) w₀ = ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ g w₀ ∧ ∀ h : Euclid m, ‖h‖ ≤ ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h‖ := by
  intro m k ι ι' g w₀ horth hg
  -- (1) sum and chain rules, then uniqueness: `DG(w₀) = ι + ι' ∘ Dg(w₀)`
  have hder : fderiv ℝ (fun w => ι w + ι' (g w)) w₀ =
      ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ g w₀ :=
    (ι.toContinuousLinearMap.hasFDerivAt.add
      (ι'.toContinuousLinearMap.hasFDerivAt.comp w₀ hg.hasFDerivAt)).fderiv
  refine ⟨hder, fun h => ?_⟩
  -- (2) Pythagoras: `|ιh + ι'(Dg(w₀)h)|² = |h|² + 2 ⟨ιh, ι'(Dg(w₀)h)⟩ + |Dg(w₀)h|²`, where the
  -- middle term vanishes by orthogonality and `ι`, `ι'` preserve norms
  have hsq : ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h‖ ^ 2 =
      ‖h‖ ^ 2 + ‖fderiv ℝ g w₀ h‖ ^ 2 := by
    have happly : fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h = ι h + ι' (fderiv ℝ g w₀ h) := by
      rw [hder]; rfl
    rw [happly, norm_add_sq_real, horth, ι.norm_map, ι'.norm_map]
    ring
  -- (3) `|h|² ≤ |DG(w₀)h|²`, and both norms are nonnegative
  refine (pow_le_pow_iff_left₀ (norm_nonneg h) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hsq]
  exact le_add_of_nonneg_right (sq_nonneg _)
/-- Choice of the tolerance in the local comparison for the area of a `C¹` graph (Simon 2.3.2,
by the approximation argument from the linear case 2.3.1): for `m ∈ ℕ` and `t > 1` there is
`ε ∈ (0, 1)` with `(1 + ε)^m ≤ t(1 - ε)` and `1 + ε ≤ t(1 - ε)^m`.  By continuity at `0`, pick
`ε ∈ (0, 1)` with `q^{m+1} < t` for `q = (1 + ε)/(1 - ε)`; since `1 + ε ≤ q` and
`1/(1 - ε) ≤ q`, both `(1 + ε)^m/(1 - ε)` and `(1 + ε)/(1 - ε)^m` are at most `q^{m+1}`. -/
theorem Submission.codim1_zsl_ga_lc_eps_choice : ∀ (m : ℕ) (t : ℝ), 1 < t → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 + ε) ^ m ≤ t * (1 - ε) ∧ 1 + ε ≤ t * (1 - ε) ^ m := by
  intro m t ht
  -- (1) `φ(ε) = ((1 + ε)/(1 - ε))^{m+1}` is continuous at `0` and `φ(0) = 1 < t`
  have hφ : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ (m + 1)) 0 :=
    ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
      (by norm_num)).pow (m + 1)
  have hφt : ∀ᶠ ε in 𝓝 (0 : ℝ), ((1 + ε) / (1 - ε)) ^ (m + 1) < t :=
    hφ.eventually_lt continuousAt_const (by simpa using ht)
  -- (2) `(0, 1) ∈ 𝓝[>] 0`, so some `ε ∈ (0, 1)` has `φ(ε) < t`
  have hφt' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((1 + ε) / (1 - ε)) ^ (m + 1) < t :=
    hφt.filter_mono nhdsWithin_le_nhds
  have hIoo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨ε, hεt, hε0, hε1⟩ := (hφt'.and hIoo).exists
  have h1 : 0 < 1 - ε := by linarith
  have h2 : 0 < 1 + ε := by linarith
  -- (3) with `q = (1 + ε)/(1 - ε)`: `1 + ε ≤ q` and `1/(1 - ε) ≤ q`
  have hq1 : 1 + ε ≤ (1 + ε) / (1 - ε) := by
    rw [le_div_iff₀ h1]; nlinarith
  have hq2 : 1 / (1 - ε) ≤ (1 + ε) / (1 - ε) := div_le_div_of_nonneg_right (by linarith) h1.le
  have hq0 : 0 ≤ (1 + ε) / (1 - ε) := h2.le.trans hq1
  have hinv0 : 0 ≤ 1 / (1 - ε) := (one_div_pos.mpr h1).le
  refine ⟨ε, hε0, hε1, ?_, ?_⟩
  -- (4) `(1 + ε)^m/(1 - ε) ≤ q^m · q = q^{m+1} < t`; multiply by `1 - ε > 0`
  · have h : (1 + ε) ^ m * (1 / (1 - ε)) ≤ ((1 + ε) / (1 - ε)) ^ (m + 1) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ h2.le hq1 m) hq2 hinv0 (pow_nonneg hq0 m)
    have h' : (1 + ε) ^ m / (1 - ε) ≤ t := by
      rw [div_eq_mul_one_div]; linarith
    rwa [div_le_iff₀ h1] at h'
  -- (5) `(1 + ε)/(1 - ε)^m ≤ q · q^m = q^{m+1} < t`; multiply by `(1 - ε)^m > 0`
  · have h : (1 + ε) * (1 / (1 - ε)) ^ m ≤ ((1 + ε) / (1 - ε)) ^ (m + 1) := by
      rw [pow_succ']
      exact mul_le_mul hq1 (pow_le_pow_left₀ hinv0 hq2 m) (pow_nonneg hinv0 m) hq0
    have h' : (1 + ε) / (1 - ε) ^ m ≤ t := by
      rw [div_eq_mul_one_div, ← one_div_pow]; linarith
    rwa [div_le_iff₀ (pow_pos h1 m)] at h'

/-- Local `(1 ± ε)`-bi-Lipschitz comparison of a `C¹` graph map with its linearization (Simon 2.3.2,
by the approximation argument from the linear case 2.3.1): for linear isometries
`ι : ℝᵐ → ℝ^{m+k}`, `ι' : ℝᵏ → ℝ^{m+k}` with `⟨ιv, ι'w⟩ = 0`, `g` of class `C¹` on the open set
`D ∋ w₀`, `G(w) = ιw + ι'g(w)` and `L₀ = DG(w₀)`, there is `r > 0` with `B_r(w₀) ⊆ D` and
`(1 - ε)|L₀x - L₀y| ≤ |G(x) - G(y)| ≤ (1 + ε)|L₀x - L₀y|` for `x, y ∈ B_r(w₀)`.  With
`B₀ = Dg(w₀)` and `‖Dg(w) - B₀‖ < ε` on `B_r(w₀)`, the mean value inequality bounds
`e = g(x) - g(y) - B₀(x - y)` by `ε|x - y| ≤ ε|L₀(x - y)|`, and
`G(x) - G(y) = (L₀x - L₀y) + ι'e`. -/
theorem Submission.codim1_zsl_ga_lc_local_bilipschitz : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D : Set (Euclid m)) (ε : ℝ) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → 0 < ε → w₀ ∈ D → ∃ r : ℝ, 0 < r ∧ ball w₀ r ⊆ D ∧ ∀ x ∈ ball w₀ r, ∀ y ∈ ball w₀ r, (1 - ε) * ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ x - fderiv ℝ (fun w => ι w + ι' (g w)) w₀ y‖ ≤ ‖ι x + ι' (g x) - (ι y + ι' (g y))‖ ∧ ‖ι x + ι' (g x) - (ι y + ι' (g y))‖ ≤ (1 + ε) * ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ x - fderiv ℝ (fun w => ι w + ι' (g w)) w₀ y‖ := by
  intro m k ι ι' g D ε w₀ horth hD hg hε hw₀
  -- Step 1: `g` is differentiable at every point of the open set `D`
  have hdiff : ∀ w ∈ D, DifferentiableAt ℝ g w := fun w hw =>
    (hg.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hw)
  -- Step 2: `L₀ = ι + ι' ∘ B₀` and `|h| ≤ |L₀h|` (sibling `graph_fderiv`)
  obtain ⟨hL₀, hlow⟩ :=
    Submission.codim1_zsl_ga_lc_graph_fderiv m k ι ι' g w₀ horth (hdiff w₀ hw₀)
  set L₀ := fderiv ℝ (fun w => ι w + ι' (g w)) w₀
  set B₀ := fderiv ℝ g w₀
  have hL₀app : ∀ h, L₀ h = ι h + ι' (B₀ h) := fun h => by rw [hL₀]; rfl
  -- Step 3: `r = min(r₁, r₂)` with `B_{r₁}(w₀) ⊆ D` and `‖Dg(w) - B₀‖ < ε` on `B_{r₂}(w₀)`
  obtain ⟨r₁, hr₁, hr₁D⟩ := Metric.isOpen_iff.mp hD w₀ hw₀
  obtain ⟨r₂, hr₂, hr₂B⟩ := Metric.continuousAt_iff.mp
    ((hg.continuousOn_fderiv_of_isOpen hD le_rfl).continuousAt (hD.mem_nhds hw₀)) ε hε
  have hrD : ball w₀ (min r₁ r₂) ⊆ D := (ball_subset_ball (min_le_left _ _)).trans hr₁D
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, hrD, fun x hx y hy => ?_⟩
  -- Step 4: mean value inequality for `g - B₀` on the convex ball
  have hmvi : ‖g x - g y - B₀ (x - y)‖ ≤ ε * ‖x - y‖ :=
    (convex_ball w₀ (min r₁ r₂)).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hrD hz))
      (fun z hz => by
        rw [← dist_eq_norm]
        exact (hr₂B ((mem_ball.mp hz).trans_le (min_le_right _ _))).le) hy hx
  -- Step 5: `G(x) - G(y) = (L₀x - L₀y) + ι'e` with `e = g(x) - g(y) - B₀(x - y)`
  have hdecomp : ι x + ι' (g x) - (ι y + ι' (g y)) =
      (L₀ x - L₀ y) + ι' (g x - g y - B₀ (x - y)) := by
    rw [hL₀app, hL₀app]
    simp only [map_sub]
    abel
  -- Step 6: `|ι'e| = |e| ≤ ε|x - y| ≤ ε|L₀(x - y)| = ε|L₀x - L₀y|`
  have herr : ‖ι' (g x - g y - B₀ (x - y))‖ ≤ ε * ‖L₀ x - L₀ y‖ := by
    rw [ι'.norm_map, ← map_sub L₀ x y]
    exact hmvi.trans (mul_le_mul_of_nonneg_left (hlow (x - y)) hε.le)
  -- Step 7: the triangle inequality in both directions
  have h1 := norm_add_le (L₀ x - L₀ y) (ι' (g x - g y - B₀ (x - y)))
  have h2 := norm_sub_le (L₀ x - L₀ y + ι' (g x - g y - B₀ (x - y))) (ι' (g x - g y - B₀ (x - y)))
  rw [add_sub_cancel_right] at h2
  rw [hdecomp]
  constructor <;> linarith
/-- Continuity of the Jacobian in the local comparison for the area formula of `C¹` graphs
(Simon Ch. 2, 3.1–3.3, used for the zero-scale limit plane of 7.5): if `F : ℝᵐ → ℝᴾ` is `C¹` on
the open set `D`, then `w ↦ √det(DF(w)* ∘ DF(w))` is continuous on `D`, being `Φ ∘ DF` with `DF`
continuous on `D` and `Φ(T) = √det(T* ∘ T)` continuous on `ℝᵐ →L ℝᴾ`. -/
theorem Submission.codim1_zsl_ga_lc_jacobian_continuousOn : ∀ (m P : ℕ) (F : Euclid m → Euclid P) (D : Set (Euclid m)), IsOpen D → ContDiffOn ℝ 1 F D → ContinuousOn (fun w => Real.sqrt (((fderiv ℝ F w).adjoint ∘L fderiv ℝ F w).det)) D := by
  intro m P F D hD hF
  -- (1) `F` is `C¹` on the open set `D`, so `DF` is continuous on `D`
  have hDF : ContinuousOn (fderiv ℝ F) D := hF.continuousOn_fderiv_of_isOpen hD le_rfl
  -- (2) `Φ(T) = √det(T* ∘ T)` is continuous: the adjoint is a linear isometric equivalence,
  -- composition is jointly continuous, `det` is continuous in finite dimension, and so is `√`
  have hΦ : Continuous fun T : Euclid m →L[ℝ] Euclid P => Real.sqrt ((T.adjoint ∘L T).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id))
  -- (3) the Jacobian is `Φ ∘ DF`
  exact hΦ.comp_continuousOn hDF
/-- Final step of the local comparison of `Hᵐ` on a `C¹` graph with the integral of its Jacobian
(Simon 7.5.8 via Ch. 2, 3.2–3.3): with `ε < 1`, `c ≥ 0`, `(1 + ε)ᵐ ≤ t(1 − ε)` and
`1 + ε ≤ t(1 − ε)ᵐ`, the `(1 ± ε)`-sandwiches `(1 − ε)ᵐ c X ≤ H ≤ (1 + ε)ᵐ c X` and
`(1 − ε) c X ≤ I ≤ (1 + ε) c X` in `[0, ∞]` give `H ≤ t I` and `I ≤ t H`. -/
theorem Submission.codim1_zsl_ga_lc_sandwich : ∀ (m : ℕ) (t ε c : ℝ) (X H I : ℝ≥0∞), ε < 1 → 0 ≤ c → (1 + ε) ^ m ≤ t * (1 - ε) → 1 + ε ≤ t * (1 - ε) ^ m → ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal c * X) ≤ H → H ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal c * X) → ENNReal.ofReal ((1 - ε) * c) * X ≤ I → I ≤ ENNReal.ofReal ((1 + ε) * c) * X → H ≤ ENNReal.ofReal t * I ∧ I ≤ ENNReal.ofReal t * H := by
  intro m t ε c X H I hε hc h1 h2 hHlo hHhi hIlo hIhi
  -- (1) `1 − ε > 0`, so `(1 − ε) c ≥ 0` and `(1 − ε)ᵐ c ≥ 0`
  have hpos : 0 < 1 - ε := sub_pos.mpr hε
  have hc1 : 0 ≤ (1 - ε) * c := mul_nonneg hpos.le hc
  have hcm : 0 ≤ (1 - ε) ^ m * c := mul_nonneg (pow_nonneg hpos.le m) hc
  -- (2) multiply both hypotheses on `t` by `c ≥ 0`
  have h1' : (1 + ε) ^ m * c ≤ t * ((1 - ε) * c) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hc
  have h2' : (1 + ε) * c ≤ t * ((1 - ε) ^ m * c) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 hc
  constructor
  -- (3) `H ≤ (1 + ε)ᵐ c X ≤ t ((1 − ε) c) X ≤ t I`
  · calc H ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal c * X) := hHhi
      _ = ENNReal.ofReal ((1 + ε) ^ m * c) * X := by rw [ENNReal.ofReal_mul' hc, mul_assoc]
      _ ≤ ENNReal.ofReal (t * ((1 - ε) * c)) * X := by gcongr ENNReal.ofReal ?_ * X
      _ = ENNReal.ofReal t * (ENNReal.ofReal ((1 - ε) * c) * X) := by
        rw [ENNReal.ofReal_mul' hc1, mul_assoc]
      _ ≤ ENNReal.ofReal t * I := by gcongr
  -- (4) `I ≤ (1 + ε) c X ≤ t ((1 − ε)ᵐ c) X ≤ t H`
  · calc I ≤ ENNReal.ofReal ((1 + ε) * c) * X := hIhi
      _ ≤ ENNReal.ofReal (t * ((1 - ε) ^ m * c)) * X := by gcongr ENNReal.ofReal ?_ * X
      _ = ENNReal.ofReal t * (ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal c * X)) := by
        rw [ENNReal.ofReal_mul' hcm, ENNReal.ofReal_mul' hc, mul_assoc, mul_assoc]
      _ ≤ ENNReal.ofReal t * H := by gcongr
/-- **Simon Ch. 2, 3.1** (linear area formula): for an injective linear `L : ℝⁿ → ℝᴾ`,
`det(L*L) > 0` and `Hⁿ(L(S)) = √det(L*L) · Lⁿ(S)` for every `S ⊆ ℝⁿ`.  An orthonormal basis of
`range L` gives a linear isometry `κ : ℝⁿ → ℝᴾ` onto `range L`.  Then `L = κ ∘ M` with
`M = κ* ∘ L`, so `L*L = M*M`, `det(L*L) = (det M)² > 0` and
`Hⁿ(L(S)) = Hⁿ(κ(M(S))) = Lⁿ(M(S)) = |det M| Lⁿ(S)`.  No measurability of `S` is needed. -/
theorem Submission.codim1_zsl_ga_linear_area : ∀ (n P : ℕ) (L : Euclid n →L[ℝ] Euclid P), Function.Injective L → 0 < (L.adjoint ∘L L).det ∧ ∀ S : Set (Euclid n), μHE[n] (L '' S) = ENNReal.ofReal (Real.sqrt ((L.adjoint ∘L L).det)) * volume S := by
  intro n P L hL
  -- step 1: a linear isometry `κ` of `ℝⁿ` onto `V = range L`
  set V : Submodule ℝ (Euclid P) := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) with hV
  have hdim : Module.finrank ℝ V = n := by
    rw [hV, LinearMap.finrank_range_of_inj hL]; simp
  let b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let κ : Euclid n →ₗᵢ[ℝ] Euclid P := V.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let K : Euclid n →L[ℝ] Euclid P := κ.toContinuousLinearMap
  have hKK : K.adjoint ∘L K = 1 := LinearIsometry.adjoint_comp_self κ
  have hrange : ∀ h, ∃ u, K u = L h := by
    intro h
    refine ⟨b.repr ⟨L h, LinearMap.mem_range_self _ h⟩, ?_⟩
    simp [K, κ]
  -- step 2: `L = κ ∘ M` with `M = κ* ∘ L` injective, so `det M ≠ 0`
  let M : Euclid n →L[ℝ] Euclid n := K.adjoint ∘L L
  have hKM : K ∘L M = L := by
    ext1 h
    obtain ⟨u, hu⟩ := hrange h
    have : K.adjoint (K u) = u := by
      simpa using congrArg (fun T : Euclid n →L[ℝ] Euclid n => T u) hKK
    simp only [M, ContinuousLinearMap.comp_apply, ← hu, this]
  have hMinj : Function.Injective M := by
    intro x y hxy
    apply hL
    rw [← hKM]
    simp [hxy]
  have hdetM : M.det ≠ 0 := by
    intro h0
    rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.mpr hMinj)
  -- step 3: `L*L = M*M` and `det M* = det M`, so `det(L*L) = (det M)²`
  have hLL : L.adjoint ∘L L = M.adjoint ∘L M := by
    conv_lhs => rw [← hKM]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc K.adjoint K M, hKK]
    rfl
  have hdetadj : M.adjoint.det = M.det := by
    let e := EuclideanSpace.basisFun (Fin n) ℝ
    have h2 := congrArg Matrix.det (LinearMap.toMatrix_adjoint e e (M : Euclid n →ₗ[ℝ] Euclid n))
    rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h2
    simpa [ContinuousLinearMap.det, ContinuousLinearMap.adjoint_toLinearMap] using h2
  have hdetLL : (L.adjoint ∘L L).det = M.det ^ 2 := by
    rw [hLL, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    rw [show LinearMap.det (M.adjoint : Euclid n →ₗ[ℝ] Euclid n) = M.adjoint.det from rfl, hdetadj]
    ring
  refine ⟨by rw [hdetLL]; positivity, fun S => ?_⟩
  -- step 4: `Hⁿ(L(S)) = Hⁿ(κ(M(S))) = Lⁿ(M(S)) = |det M| Lⁿ(S)`
  have himg : L '' S = K '' (M '' S) := by
    rw [← hKM, ContinuousLinearMap.coe_comp, Set.image_comp]
  have hiso : Isometry K := κ.isometry
  rw [himg, Isometry.euclideanHausdorffMeasure_image hiso,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_image_continuousLinearMap, hdetLL, Real.sqrt_sq_eq_abs]
/-- Relative bi-Lipschitz comparison of `Hⁿ` (Simon Ch. 2, Theorem 1.8(i), relative form).  If
`a‖Lx − Ly‖ ≤ ‖Fx − Fy‖ ≤ b‖Lx − Ly‖` for `x, y ∈ S` (`a > 0`, `b ≥ 0`), then
`aⁿ Hⁿ(L(S)) ≤ Hⁿ(F(S)) ≤ bⁿ Hⁿ(L(S))` for arbitrary (not necessarily measurable) `S`: the
transfer maps `φ = F ∘ (L|_S)⁻¹` on `L(S)` and `ψ = L ∘ (F|_S)⁻¹` on `F(S)` are well defined,
`b`- and `a⁻¹`-Lipschitz, and satisfy `φ(L(S)) = F(S)`, `ψ(F(S)) = L(S)`. -/
theorem Submission.codim1_zsl_ga_relative_lipschitz_measure : ∀ (n P : ℕ) (F L : Euclid n → Euclid P) (S : Set (Euclid n)) (a b : ℝ), 0 < a → 0 ≤ b → (∀ x ∈ S, ∀ y ∈ S, a * ‖L x - L y‖ ≤ ‖F x - F y‖ ∧ ‖F x - F y‖ ≤ b * ‖L x - L y‖) → ENNReal.ofReal (a ^ n) * μHE[n] (L '' S) ≤ μHE[n] (F '' S) ∧ μHE[n] (F '' S) ≤ ENNReal.ofReal (b ^ n) * μHE[n] (L '' S) := by
  intro n P F L S a b ha hb hFL
  -- Step 1: the transfer maps `φ = F ∘ (L|_S)⁻¹` and `ψ = L ∘ (F|_S)⁻¹` (`invFunOn`).
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid P → Euclid P, ∀ x ∈ S, φ (L x) = F x := by
    refine ⟨fun z => F (Function.invFunOn L S z), fun x hx => ?_⟩
    have hex : ∃ y ∈ S, L y = L x := ⟨x, hx, rfl⟩
    have h := (hFL _ (Function.invFunOn_mem hex) x hx).2
    rw [Function.invFunOn_eq hex, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Euclid P → Euclid P, ∀ x ∈ S, ψ (F x) = L x := by
    refine ⟨fun z => L (Function.invFunOn F S z), fun x hx => ?_⟩
    have hex : ∃ y ∈ S, F y = F x := ⟨x, hx, rfl⟩
    have h := (hFL _ (Function.invFunOn_mem hex) x hx).1
    rw [Function.invFunOn_eq hex, sub_self, norm_zero] at h
    have h0 : ‖L (Function.invFunOn F S (F x)) - L x‖ ≤ 0 :=
      le_of_mul_le_mul_left (h.trans (mul_zero a).ge) ha
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  have himφ : φ '' (L '' S) = F '' S := by
    rw [Set.image_image]
    exact Set.image_congr hφ
  have himψ : ψ '' (F '' S) = L '' S := by
    rw [Set.image_image]
    exact Set.image_congr hψ
  -- Step 2: `φ` is `b`-Lipschitz on `L(S)` and `ψ` is `a⁻¹`-Lipschitz on `F(S)`.
  have hφlip : LipschitzOnWith (Real.toNNReal b) φ (L '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hφ x hx, hφ y hy, dist_eq_norm, dist_eq_norm]
    exact (hFL x hx y hy).2
  have hψlip : LipschitzOnWith (Real.toNNReal a⁻¹) ψ (F '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hψ x hx, hψ y hy, dist_eq_norm, dist_eq_norm, inv_mul_eq_div, le_div_iff₀ ha]
    linarith [(hFL x hx y hy).1]
  -- Step 3: the Lipschitz image bound (Simon 2.1.8(i)) for `φ` and `ψ`.
  have hup := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hφlip
  have hlo := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hψlip
  rw [himφ] at hup
  rw [himψ] at hlo
  -- Steps 4–5: `(b⁺)ⁿ = ofReal (bⁿ)` and `ofReal (aⁿ) · (a⁻¹)ⁿ = 1`.
  have hb' : ((Real.toNNReal b : NNReal) : ℝ≥0∞) ^ n = ENNReal.ofReal (b ^ n) :=
    (ENNReal.ofReal_pow hb n).symm
  have ha' : ENNReal.ofReal (a ^ n) * ((Real.toNNReal a⁻¹ : NNReal) : ℝ≥0∞) ^ n = 1 := by
    change ENNReal.ofReal (a ^ n) * ENNReal.ofReal a⁻¹ ^ n = 1
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr ha.le), ← ENNReal.ofReal_mul (pow_nonneg ha.le n),
      ← mul_pow, mul_inv_cancel₀ ha.ne', one_pow, ENNReal.ofReal_one]
  rw [hb'] at hup
  refine ⟨?_, hup⟩
  calc ENNReal.ofReal (a ^ n) * μHE[n] (L '' S)
      ≤ ENNReal.ofReal (a ^ n) * (((Real.toNNReal a⁻¹ : NNReal) : ℝ≥0∞) ^ n * μHE[n] (F '' S)) :=
        mul_le_mul_of_nonneg_left hlo zero_le
    _ = μHE[n] (F '' S) := by rw [← mul_assoc, ha', one_mul]

/-- **Local comparison** for the `C¹` graph map `G(w) = ιw + ι'g(w)` (Simon Ch. 2, 3.2–3.3, by the
approximation argument based on the linear case 3.1): for `t > 1` and `w₀ ∈ D` there is a ball
`B_r(w₀) ⊆ D` on which `Hᵐ(G(B)) ≤ t ∫_B J` and `∫_B J ≤ t Hᵐ(G(B))` for every measurable `B`,
where `J(w) = √det(DG(w)*DG(w))`.  `L₀ = DG(w₀)` is injective, so `J₀ = J(w₀) > 0` and
`Hᵐ(L₀(B)) = J₀ Lᵐ(B)`.  On a small ball, `G` is `(1 ± ε)`-bi-Lipschitz relative to `L₀` and
`(1 − ε)J₀ ≤ J ≤ (1 + ε)J₀`, with `ε` chosen so that both sandwiches give the factor `t`. -/
theorem Submission.codim1_zsl_ga_local_comparison : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D : Set (Euclid m)) (t : ℝ) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → 1 < t → w₀ ∈ D → ∃ r : ℝ, 0 < r ∧ ball w₀ r ⊆ D ∧ ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w₀ r → μHE[m] ((fun w => ι w + ι' (g w)) '' B) ≤ ENNReal.ofReal t * ∫⁻ w in B, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) ∧ ∫⁻ w in B, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) ≤ ENNReal.ofReal t * μHE[m] ((fun w => ι w + ι' (g w)) '' B) := by
  intro m k ι ι' g D t w₀ hperp hD hg ht hw₀
  -- step 1: `ε ∈ (0, 1)` with `(1 + ε)ᵐ ≤ t(1 − ε)` and `1 + ε ≤ t(1 − ε)ᵐ`
  obtain ⟨ε, hε0, hε1, hεm, hε1m⟩ := Submission.codim1_zsl_ga_lc_eps_choice m t ht
  -- step 2: `‖h‖ ≤ ‖L₀ h‖` for `L₀ = DG(w₀)`, so `L₀` is injective, `J₀ = J(w₀) > 0` and
  -- `Hᵐ(L₀(S)) = J₀ Lᵐ(S)`
  have hgw₀ : DifferentiableAt ℝ g w₀ :=
    (hg.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hw₀)
  set L₀ := fderiv ℝ (fun w => ι w + ι' (g w)) w₀
  have hL₀ : Function.Injective L₀ := by
    intro x y hxy
    have h : ‖x - y‖ ≤ ‖L₀ (x - y)‖ :=
      (Submission.codim1_zsl_ga_lc_graph_fderiv m k ι ι' g w₀ hperp hgw₀).2 (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  obtain ⟨hdet, harea⟩ := Submission.codim1_zsl_ga_linear_area m (m + k) L₀ hL₀
  set J : Euclid m → ℝ := fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
    fderiv ℝ (fun w => ι w + ι' (g w)) w).det)
  have hJ₀ : 0 < J w₀ := Real.sqrt_pos.mpr hdet
  -- step 3: `G` is `C¹` on `D`, so `J` is continuous at `w₀`: `|J − J₀| < εJ₀` on `B_δ(w₀)`
  have hG : ContDiffOn ℝ 1 (fun w => ι w + ι' (g w)) D :=
    ι.contDiff.contDiffOn.add (ι'.contDiff.comp_contDiffOn hg)
  obtain ⟨δ, hδ, hJδ⟩ := Metric.continuousAt_iff.mp
    ((Submission.codim1_zsl_ga_lc_jacobian_continuousOn m (m + k) _ D hD hG).continuousAt
      (hD.mem_nhds hw₀)) (ε * J w₀) (mul_pos hε0 hJ₀)
  -- step 4: `G` is `(1 ± ε)`-bi-Lipschitz relative to `L₀` on `B_{r₁}(w₀) ⊆ D`
  obtain ⟨r₁, hr₁, hr₁D, hbil⟩ :=
    Submission.codim1_zsl_ga_lc_local_bilipschitz m k ι ι' g D ε w₀ hperp hD hg hε0 hw₀
  refine ⟨min r₁ δ, lt_min hr₁ hδ, (Metric.ball_subset_ball (min_le_left _ _)).trans hr₁D,
    fun B hB hBr => ?_⟩
  -- step 5: `(1 − ε)ᵐ J₀ Lᵐ(B) ≤ Hᵐ(G(B)) ≤ (1 + ε)ᵐ J₀ Lᵐ(B)`
  have hB₁ : B ⊆ ball w₀ r₁ := hBr.trans (Metric.ball_subset_ball (min_le_left _ _))
  obtain ⟨hHlo, hHhi⟩ := Submission.codim1_zsl_ga_relative_lipschitz_measure m (m + k)
    (fun w => ι w + ι' (g w)) L₀ B (1 - ε) (1 + ε) (by linarith) (by linarith)
    fun x hx y hy => hbil x (hB₁ hx) y (hB₁ hy)
  rw [harea B] at hHlo hHhi
  -- step 6: `(1 − ε) J₀ Lᵐ(B) ≤ ∫_B J ≤ (1 + ε) J₀ Lᵐ(B)`
  have hJB : ∀ w ∈ B, (1 - ε) * J w₀ ≤ J w ∧ J w ≤ (1 + ε) * J w₀ := by
    intro w hw
    have h : |J w - J w₀| < ε * J w₀ :=
      hJδ ((Metric.mem_ball.mp (hBr hw)).trans_le (min_le_right _ _))
    rw [abs_sub_lt_iff] at h
    constructor <;> linarith
  have hIlo : ENNReal.ofReal ((1 - ε) * J w₀) * volume B ≤ ∫⁻ w in B, ENNReal.ofReal (J w) :=
    (setLIntegral_const B _).symm.trans_le
      (setLIntegral_mono' hB fun w hw => ENNReal.ofReal_le_ofReal (hJB w hw).1)
  have hIhi : ∫⁻ w in B, ENNReal.ofReal (J w) ≤ ENNReal.ofReal ((1 + ε) * J w₀) * volume B :=
    (setLIntegral_mono' hB fun w hw => ENNReal.ofReal_le_ofReal (hJB w hw).2).trans_eq
      (setLIntegral_const B _)
  -- step 7: the two sandwiches and the choice of `ε` give the factor `t`
  exact Submission.codim1_zsl_ga_lc_sandwich m t ε (J w₀) (volume B) _ _ hε1 hJ₀.le hεm hε1m
    hHlo hHhi hIlo hIhi

/-- **Area formula for a `C¹` graph over a measurable set** (Simon Ch. 2, 3.2–3.3, for the graph
map `G(w) = ι w + ι' (g w)` of a `g` that is `C¹` on an open `D`, with `ι`, `ι'` linear isometries
with orthogonal ranges): `μHE[m] (G '' A) = ∫⁻_A √det (DG* ∘ DG)` for measurable `A ⊆ D`.
`⟪ι v, G w⟫ = ⟪v, w⟫`, so `G` is injective; it is continuous on `D`.  For `t > 1`, countably many
of the balls of `codim1_zsl_ga_local_comparison` cover `D`; disjointing them cuts `A` into
measurable pieces with disjoint Borel images (Lusin–Souslin), and summing the local comparisons
gives `μHE[m] (G '' A) ≤ t ∫⁻_A J` and `∫⁻_A J ≤ t μHE[m] (G '' A)`.  Let `t ↓ 1`. -/
theorem Submission.codim1_zsl_ga_set_identity : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D A : Set (Euclid m)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → μHE[m] ((fun w => ι w + ι' (g w)) '' A) = ∫⁻ w in A, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) := by
  intro m k ι ι' g D A hperp hD hg hA hAD
  -- steps 2–3 for any injective `G` continuous on `D` and any density `J` comparable with
  -- `B ↦ μHE[m] (G '' B)` up to every factor `t > 1` on small balls around the points of `D`
  have main : ∀ (G : Euclid m → Euclid (m + k)) (J : Euclid m → ℝ≥0∞), Injective G →
      ContinuousOn G D → (∀ t : ℝ, 1 < t → ∀ w ∈ D, ∃ r : ℝ, 0 < r ∧ ball w r ⊆ D ∧
        ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w r →
          μHE[m] (G '' B) ≤ ENNReal.ofReal t * ∫⁻ x in B, J x ∧
            ∫⁻ x in B, J x ≤ ENNReal.ofReal t * μHE[m] (G '' B)) →
      μHE[m] (G '' A) = ∫⁻ x in A, J x := by
    intro G J hinj hcont hloc
    -- step 2: for fixed `t > 1`, `μHE[m] (G '' A) ≤ t ∫_A J` and `∫_A J ≤ t μHE[m] (G '' A)`
    have hstep : ∀ t : ℝ, 1 < t → μHE[m] (G '' A) ≤ ENNReal.ofReal t * ∫⁻ x in A, J x ∧
        ∫⁻ x in A, J x ≤ ENNReal.ofReal t * μHE[m] (G '' A) := by
      intro t ht
      -- (a) a comparison radius at each point of `D` (an arbitrary one elsewhere)
      have hr : ∀ w, ∃ r : ℝ, w ∈ D → 0 < r ∧ ball w r ⊆ D ∧
          ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w r →
            μHE[m] (G '' B) ≤ ENNReal.ofReal t * ∫⁻ x in B, J x ∧
              ∫⁻ x in B, J x ≤ ENNReal.ofReal t * μHE[m] (G '' B) := by
        intro w
        by_cases hw : w ∈ D
        · obtain ⟨r, h⟩ := hloc t ht w hw
          exact ⟨r, fun _ => h⟩
        · exact ⟨1, fun h => absurd h hw⟩
      choose r hr using hr
      -- (b) countably many of these balls cover `D`; enumerate their centres
      obtain ⟨T, hTD, hTc, hDT⟩ := TopologicalSpace.countable_cover_nhdsWithin
        (f := fun w => ball w (r w)) (s := D) fun w hw =>
          mem_nhdsWithin_of_mem_nhds (ball_mem_nhds w (hr w hw).1)
      rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · simp
      obtain ⟨e, rfl⟩ := hTc.exists_eq_range <| by
        obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 (hDT (hAD ha))
        exact ⟨x, hx⟩
      set V : ℕ → Set (Euclid m) := fun j => ball (e j) (r (e j))
      -- (c) the pieces `A ∩ disjointed V j` partition `A`, each inside one ball
      have hPm : ∀ j, MeasurableSet (A ∩ disjointed V j) := fun j =>
        hA.inter (MeasurableSet.disjointed (fun _ => measurableSet_ball) j)
      have hPd : Pairwise (Disjoint on fun j => A ∩ disjointed V j) := fun i j hij =>
        Disjoint.mono inter_subset_right inter_subset_right (disjoint_disjointed V hij)
      have hPA : ⋃ j, A ∩ disjointed V j = A := by
        rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
        intro x hx
        simpa only [biUnion_range] using hDT (hAD hx)
      -- (d) their images are disjoint Borel sets (`G` is injective; Lusin–Souslin)
      have hGm : ∀ j, MeasurableSet (G '' (A ∩ disjointed V j)) := fun j =>
        (hPm j).image_of_continuousOn_injOn (hcont.mono (inter_subset_left.trans hAD))
          hinj.injOn
      have hGd : Pairwise (Disjoint on fun j => G '' (A ∩ disjointed V j)) := fun i j hij =>
        (disjoint_image_iff hinj).2 (hPd hij)
      have hμ : μHE[m] (G '' A) = ∑' j, μHE[m] (G '' (A ∩ disjointed V j)) := by
        conv_lhs => rw [← hPA]
        rw [image_iUnion, measure_iUnion hGd hGm]
      have hJ : ∫⁻ x in A, J x = ∑' j, ∫⁻ x in A ∩ disjointed V j, J x := by
        conv_lhs => rw [← hPA]
        exact lintegral_iUnion hPm hPd J
      -- (e) sum the comparisons on the pieces
      have hc : ∀ j, μHE[m] (G '' (A ∩ disjointed V j)) ≤
            ENNReal.ofReal t * ∫⁻ x in A ∩ disjointed V j, J x ∧
          ∫⁻ x in A ∩ disjointed V j, J x ≤
            ENNReal.ofReal t * μHE[m] (G '' (A ∩ disjointed V j)) := fun j =>
        (hr (e j) (hTD (mem_range_self j))).2.2 _ (hPm j)
          (inter_subset_right.trans (disjointed_subset V j))
      rw [hμ, hJ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
      exact ⟨ENNReal.tsum_le_tsum fun j => (hc j).1, ENNReal.tsum_le_tsum fun j => (hc j).2⟩
    -- step 3: `x ≤ t y` for every `t > 1` gives `x ≤ y` (let `t ↓ 1`)
    have hlim : ∀ x y : ℝ≥0∞, (∀ t : ℝ, 1 < t → x ≤ ENNReal.ofReal t * y) → x ≤ y := by
      intro x y h
      have hty : Tendsto (fun t : ℝ => ENNReal.ofReal t * y) (𝓝[>] 1)
          (𝓝 (ENNReal.ofReal 1 * y)) :=
        ENNReal.Tendsto.mul_const
          ((ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) (Or.inl (by simp))
      simpa using ge_of_tendsto hty (eventually_nhdsWithin_of_forall fun t ht => h t ht)
    exact le_antisymm (hlim _ _ fun t ht => (hstep t ht).1) (hlim _ _ fun t ht => (hstep t ht).2)
  -- step 1: `⟪ι v, G w⟫ = ⟪v, w⟫`, so `G` is injective; `G` is continuous on `D`
  refine main _ _ (fun w₁ w₂ h => ext_inner_left ℝ fun v => ?_)
    (ι.continuous.continuousOn.add (ι'.continuous.comp_continuousOn hg.continuousOn))
    fun t ht w hw => Submission.codim1_zsl_ga_local_comparison m k ι ι' g D t w hperp hD hg ht hw
  simpa only [inner_add_right, LinearIsometry.inner_map_map, hperp, add_zero] using
    congrArg (inner ℝ (ι v)) h
/-- Bochner integrals over an injective continuous image (supplied steps 5–6 of the graph area
formula): if `μ(G(B)) = ∫_B J dLᵐ` for every measurable `B ⊆ A`, then `μ⌞G(A) = φ#ν` for the
measurable embedding `φ = G|_A` of the subtype `A` (Lusin–Souslin) and `ν` the restriction of `J Lᵐ`
to `A`, so `∫_{G(A)} f dμ = ∫_A J·(f ∘ G) dLᵐ` for every `f`. -/
theorem Submission.codim1_zsl_ga_integral_transfer : ∀ (m P : ℕ) (μ : Measure (Euclid P)) (G : Euclid m → Euclid P) (J : Euclid m → ℝ) (A : Set (Euclid m)) (f : Euclid P → ℝ), MeasurableSet A → ContinuousOn G A → InjOn G A → Measurable J → (∀ w ∈ A, 0 ≤ J w) → (∀ B : Set (Euclid m), MeasurableSet B → B ⊆ A → μ (G '' B) = ∫⁻ w in B, ENNReal.ofReal (J w)) → ∫ y in G '' A, f y ∂μ = ∫ w in A, J w * f (G w) := by
  intro m P μ G J A f hA hGc hGi hJm hJ hμ
  -- `G|_A` is a measurable embedding of the subtype `A` (Lusin–Souslin)
  have hφ : MeasurableEmbedding (A.domRestrict G) := hGc.measurableEmbedding hA hGi
  -- `ν` is the restriction to `A` of `J Lᵐ`
  let ν : Measure A := Measure.comap Subtype.val (volume.withDensity fun w => ENNReal.ofReal (J w))
  -- `μ⌞G(A) = (G|_A)#ν`: for measurable `Y`, `Y ∩ G(A) = G(A ∩ G⁻¹Y)`
  have hmap : μ.restrict (G '' A) = Measure.map (A.domRestrict G) ν := by
    ext Y hY
    have hpre : Subtype.val '' (A.domRestrict G ⁻¹' Y) = A ∩ G ⁻¹' Y :=
      Subtype.image_preimage_coe A (G ⁻¹' Y)
    have hB : MeasurableSet (A ∩ G ⁻¹' Y) := hpre ▸ hA.subtype_image (hφ.measurable hY)
    rw [Measure.restrict_apply hY, hφ.map_apply, (MeasurableEmbedding.subtype_coe hA).comap_apply,
      hpre, withDensity_apply _ hB, inter_comm, ← image_inter_preimage, hμ _ hB inter_subset_left]
  calc ∫ y in G '' A, f y ∂μ = ∫ y, f y ∂(Measure.map (A.domRestrict G) ν) := by rw [hmap]
    _ = ∫ x, f (G x) ∂ν := hφ.integral_map f
    _ = ∫ w, f (G w) ∂(Measure.map Subtype.val ν) :=
        ((MeasurableEmbedding.subtype_coe hA).integral_map fun w => f (G w)).symm
    -- `ENNReal.ofReal r = ↑r.toNNReal` by definition
    _ = ∫ w in A, f (G w) ∂(volume.withDensity fun w => ((J w).toNNReal : ℝ≥0∞)) := by
        rw [map_comap_subtype_coe hA]
        rfl
    _ = ∫ w in A, (J w).toNNReal • f (G w) :=
        setIntegral_withDensity_eq_setIntegral_smul hJm.real_toNNReal _ hA
    _ = ∫ w in A, J w * f (G w) := setIntegral_congr_fun hA fun w hw => by
        rw [NNReal.smul_def, Real.coe_toNNReal _ (hJ w hw), smul_eq_mul]
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

/-- **Area formula for a `C¹` graph over an `m`-plane** (Simon Ch. 2, 3.1–3.3).  Let
`G(w) = ιw + ι'g(w)` with `ι`, `ι'` isometries onto orthogonal subspaces and `g` of class `C¹` on
the open set `D ⊇ A`, and `J(w) = √det(DG(w)* ∘ DG(w))`.  Then
`∫_{G(A)} f dHᵐ = ∫_A J(w) f(G(w)) dw` for every `f`.  `G` is continuous on `A` and injective
(`ι(w - w') = ι'(g w' - g w)` is orthogonal to itself), `J` is Borel as a continuous function of
`fderiv ℝ G`, and `Hᵐ(G(B)) = ∫_B J` for every measurable `B ⊆ A` (`codim1_zsl_ga_set_identity`);
`codim1_zsl_ga_integral_transfer` turns this weighted set identity into the Bochner identity. -/
theorem Submission.codim1_zsl_graph_area_formula : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D A : Set (Euclid m)) (f : Euclid (m + k) → ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → ∫ y in (fun w => ι w + ι' (g w)) '' A, f y ∂μHE[m] = ∫ w in A, Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det) * f (ι w + ι' (g w)) := by
  intro m k ι ι' g D A f horth hD hg hA hAD
  -- `G` is continuous on `A ⊆ D`, where `g` is `C¹`
  have hGc : ContinuousOn (fun w => ι w + ι' (g w)) A :=
    ι.continuous.continuousOn.add (ι'.continuous.comp_continuousOn (hg.continuousOn.mono hAD))
  -- `G` is injective: `ι (w - w') = ι' (g w' - g w)` is orthogonal to itself
  have hGi : Injective fun w => ι w + ι' (g w) := by
    intro w w' h
    have h1 : ι (w - w') = ι' (g w' - g w) := by
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, add_comm (ι' (g w'))]
      exact h
    have h2 := horth (w - w') (g w' - g w)
    rw [← h1, inner_self_eq_zero] at h2
    exact sub_eq_zero.1 (ι.injective (h2.trans (map_zero ι).symm))
  -- `J = √det(DG* ∘ DG)` is Borel: a continuous function of the Borel map `fderiv ℝ G`
  have hJm : Measurable fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
      fderiv ℝ (fun w => ι w + ι' (g w)) w).det) := by
    have hc : Continuous fun T : Euclid m →L[ℝ] Euclid (m + k) =>
        Real.sqrt ((T.adjoint ∘L T).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
        ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m)
          (F := Euclid (m + k))).continuous.clm_comp continuous_id))
    exact hc.measurable.comp (measurable_fderiv ℝ fun w => ι w + ι' (g w))
  -- `Hᵐ(G(B)) = ∫_B J` for measurable `B ⊆ A ⊆ D`; transfer to Bochner integrals
  exact Submission.codim1_zsl_ga_integral_transfer m (m + k) μHE[m] (fun w => ι w + ι' (g w))
    (fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
      fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) A f hA hGc hGi.injOn hJm
    (fun w _ => Real.sqrt_nonneg _) fun B hB hBA =>
      Submission.codim1_zsl_ga_set_identity m k ι ι' g D B horth hD hg hB (hBA.trans hAD)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
