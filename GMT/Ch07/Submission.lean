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

/-- **Coefficient bounds for the Euclidean covector norm** (Simon Ch. 6, 1.15; facts used for the
face currents in the proof of the Deformation Theorem 6.5.1, displays (29)–(30) and (34)).  With
`e` the standard basis of `ℝᴾ`, let `f J = α(e_{J(0)}, …, e_{J(k-1)})²` for strictly increasing
`J : Fin k → Fin P` and `f J = 0` otherwise, so `|α|² = ∑_J f J` is a sum of nonnegative terms.
(i) The single term `f I = α(e_I)²` is at most the sum.  (ii) For strictly increasing
`ι : Fin (k+1) → Fin P` the faces `ι ∘ i.succAbove` are strictly increasing and pairwise
distinct, so `∑_i α(e_{ι ∘ i.succAbove})²` is a sub-sum of `∑_J f J`. -/
theorem Submission.cmcdtfrfic_coeff_bounds : ∀ (P k : ℕ) (α : Covector (Euclid P) k), (∀ I : Fin k → Fin P, StrictMono I → |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α) ∧ ∀ ι : Fin (k + 1) → Fin P, StrictMono ι → ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2 ≤ covectorEuclideanNorm α ^ 2 := by
  intro P k α
  -- Step 1: `|α| = √(∑_J f J)` with `f ≥ 0` and `f J = α(e_J)²` for strictly increasing `J`
  obtain ⟨f, hf0, hfJ, hnorm⟩ : ∃ f : (Fin k → Fin P) → ℝ, (∀ J, 0 ≤ f J) ∧
      (∀ J, StrictMono J → f J = (α (fun j => EuclideanSpace.single (J j) (1 : ℝ))) ^ 2) ∧
      covectorEuclideanNorm α = √(∑ J, f J) := by
    refine ⟨_, fun J => ?_, fun J hJ => ?_, rfl⟩
    · split_ifs <;> positivity
    · rw [ite_eq_left hJ]
      simp only [EuclideanSpace.basisFun_apply]
  have hS : 0 ≤ ∑ J, f J := Finset.sum_nonneg fun J _ => hf0 J
  refine ⟨fun I hI => ?_, fun ι hι => ?_⟩
  -- Step 2 (i): the single term `f I = α(e_I)²` is at most the sum, so `|α(e_I)| ≤ √(∑_J f J)`
  · rw [hnorm]
    exact Real.abs_le_sqrt ((hfJ I hI).symm.trans_le
      (Finset.single_le_sum (fun J _ => hf0 J) (Finset.mem_univ I)))
  -- Step 3 (ii): the faces `ι ∘ i.succAbove` are strictly increasing and pairwise distinct
  · have hinj : Function.Injective fun i : Fin (k + 1) => ι ∘ i.succAbove :=
      fun i i' h => Fin.succAbove_left_injective (hι.injective.comp_left h)
    -- Step 4: so the left side is the sub-sum of `∑_J f J = |α|²` over the faces
    rw [hnorm, Real.sq_sqrt hS]
    calc ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2
        = ∑ i : Fin (k + 1), f (ι ∘ i.succAbove) :=
          Finset.sum_congr rfl fun i _ => (hfJ _ (hι.comp (Fin.strictMono_succAbove i))).symm
      _ = ∑ J ∈ Finset.univ.image fun i : Fin (k + 1) => ι ∘ i.succAbove, f J :=
          (Finset.sum_image fun i _ i' _ h => hinj h).symm
      _ ≤ ∑ J, f J := Finset.sum_le_univ_sum_of_nonneg hf0

/-- **The divergence field of a face** (Simon Ch. 6, proof of Theorem 5.1, (29)–(30): the field
`G_p` of the face-current construction).  Let `γ` be a smooth `m`-form on `ℝᴾ`,
`ι : Fin (m + 1) → Fin P` strictly increasing, `a ∈ ℝᴾ`, `E = (e_{ι 0}, …, e_{ι m})` and
`Φ(y) = a + Σⱼ yⱼ e_{ι j}`.  Put `Gᵢ(y) = (−1)ⁱ γ(Φ y)(E⁽ⁱ⁾)`, where `E⁽ⁱ⁾ = i.removeNth E` omits
`e_{ι i}`.  Then `G` is `C^∞`; `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²` by the coefficient bound
`cmcdtfrfic_coeff_bounds` (ii); and, as `DΦ(y) bᵢ = e_{ι i}`,
`trace DG(y) = Σᵢ (DG(y) bᵢ)ᵢ = Σᵢ (−1)ⁱ D(γ(·)(E⁽ⁱ⁾))(Φ y) e_{ι i} = dγ(Φ y)(E)`
(`exteriorDerivative_apply`). -/
theorem Submission.cmcdtfrfic_divergence_field : ∀ (P m : ℕ) (γ : DifferentialForm (Euclid P) m) (ι : Fin (m + 1) → Fin P) (a : Euclid P), ContDiff ℝ (⊤ : ℕ∞) γ → StrictMono ι → ∃ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y, ‖G y‖ ≤ covectorEuclideanNorm (γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) = exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  intro P m γ ι a hγ hι
  classical
  -- the affine map `Φ = a + L`, `L y = Σⱼ yⱼ e_{ι j}`, with `L bᵢ = e_{ι i}`
  set E : Fin (m + 1) → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  let L : Euclid (m + 1) →L[ℝ] Euclid P := ∑ j, (EuclideanSpace.proj j).smulRight (E j)
  have hL : ∀ y : Euclid (m + 1), L y = ∑ j, y j • E j := fun y => by simp [L]
  let Φ : Euclid (m + 1) → Euclid P := fun y => a + L y
  have hΦE : ∀ y : Euclid (m + 1),
      a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) = Φ y := fun y => by simp [Φ, hL, E]
  have hΦd : ∀ y, HasFDerivAt Φ L y := fun y => L.hasFDerivAt.const_add a
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := contDiff_const.add L.contDiff
  have hLb : ∀ i : Fin (m + 1), L (EuclideanSpace.single i 1) = E i := fun i => by simp [hL]
  -- the coefficients `gᵢ = γ(·)(E⁽ⁱ⁾)`: evaluation at a fixed tuple is continuous linear
  let g : Fin (m + 1) → Euclid P → ℝ := fun i x => γ x (i.removeNth E)
  have hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) := fun i =>
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (i.removeNth E)).contDiff.comp hγ
  -- the field `Gᵢ(y) = (−1)ⁱ gᵢ(Φ y)`
  let G : Euclid (m + 1) → Euclid (m + 1) :=
    fun y => WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ) * g i (Φ y)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    contDiff_euclidean.2 fun i => contDiff_const.mul ((hg i).comp hΦs)
  refine ⟨G, hGs, fun y => ?_, fun y => ?_⟩
  · -- `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²`
    rw [hΦE y, EuclideanSpace.norm_eq, ← Real.sqrt_sq (covectorEuclideanNorm_nonneg (γ (Φ y)))]
    refine Real.sqrt_le_sqrt (le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_)
      ((Submission.cmcdtfrfic_coeff_bounds P m (γ (Φ y))).2 ι hι))
    simp only [G, g, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul]
    rw [show (-1 : ℝ) ^ ((i : ℕ) * 2) = 1 by rw [mul_comm, pow_mul, neg_one_sq, one_pow], one_mul]
    rfl
  · -- `trace DG(y) = Σᵢ (DG(y) bᵢ)ᵢ` and `dγ(Φ y)(E) = Σᵢ (−1)ⁱ Dgᵢ(Φ y) e_{ι i}`
    rw [hΦE y, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ),
      exteriorDerivative_apply (hγ.differentiable (by simp)).differentiableAt E]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    -- `(DG(y) bᵢ)ᵢ = D(Gᵢ)(y) bᵢ = (−1)ⁱ Dgᵢ(Φ y)(L bᵢ)`, by uniqueness of the derivative
    have hGi := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (G y) i).comp y
      (hGs.differentiable (by simp) y).hasFDerivAt
    have hGi' : HasFDerivAt ((fun f : Euclid (m + 1) => f i) ∘ G)
        (((-1 : ℝ) ^ (i : ℕ)) • (fderiv ℝ (g i) (Φ y)).comp L) y :=
      (((hg i).differentiable (by simp) (Φ y)).hasFDerivAt.comp y (hΦd y)).const_mul _
    have happ := congrArg (fun T => T (EuclideanSpace.single i (1 : ℝ))) (hGi.unique hGi')
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, PiLp.proj_apply,
      hLb] at happ
    simp only [map_one, one_mul, ContinuousLinearMap.coe_coe]
    rw [happ, zsmul_eq_mul]
    simp [g]
/-- **Simon Ch. 6, proof of 5.1, (29)–(30)**: integrable densities on finitely many unit faces
define a current.  For `p = (ι, b) ∈ s` let `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`,
`E_p = (e_{ι(0)}, …, e_{ι(m)})`, and let `w_p` be integrable on the open unit cube
`Q₁ ⊆ ℝ^{m+1}`.  As the `e_l` are unit vectors, `|ω(x)(E_p)| ≤ ‖ω(x)‖`, which is bounded because
`ω` is continuous with compact support; so `y ↦ w_p(y) ω(Φ_p(y))(E_p)` is integrable on `Q₁`, and
`L(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy` is linear with
`|L(ω)| ≤ (Σ_{p ∈ s} ∫_{Q₁} |w_p|) δ` whenever `‖ω(x)‖ ≤ δ` for all `x`.  Order-`0` uniform
convergence on a common compact set, and vanishing off it, give the sequential continuity of
`L`. -/
theorem Submission.cmcdtfrfic_current_exists : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s w hw
  -- the face maps `Φ_p`, the frames `E_p` and the open unit cube `Q₁`
  let Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let E : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → Euclid P := fun p j =>
    EuclideanSpace.single (p.1 j) (1 : ℝ)
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  -- `y ↦ ω(Φ_p(y))(E_p)` is continuous
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Continuous (ω : DifferentialForm (Euclid P) (m + 1)) :=
    fun ω => ω.property.1.1.continuous
  have hΦ : ∀ p, Continuous (Φ p) := fun p =>
    continuous_const.add (continuous_finsetSum _ fun j _ =>
      (PiLp.continuous_apply 2 _ j).smul continuous_const)
  have hh : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) p,
      Continuous fun y => (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p) :=
    fun ω p => (continuous_eval_const _).comp ((hcont ω).comp (hΦ p))
  -- `|α(E_p)| ≤ ‖α‖`, the `e_l` being unit vectors
  have hev : ∀ (α : Covector (Euclid P) (m + 1)) p, ‖α (E p)‖ ≤ ‖α‖ := by
    intro α p
    simpa [E, PiLp.norm_single] using α.le_opNorm (E p)
  -- (I): `w_p` is integrable on `Q₁`, and `y ↦ ω(Φ_p(y))(E_p)` is continuous and bounded
  have hI : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s,
      IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p))
        Q₁ := by
    intro ω p hp
    obtain ⟨C, hC⟩ := ω.property.1.2.exists_bound_of_continuous (hcont ω)
    exact (hw p hp).mul_bdd (c := C) (hh ω p).aestronglyMeasurable
      (Eventually.of_forall fun y => (hev _ p).trans (hC _))
  -- the linear functional `L(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy`
  let L : TestFormOn (univ : Set (Euclid P)) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω =>
        ∑ p ∈ s, ∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)
      map_add' := by
        intro ω η
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← integral_add (hI ω p hp) (hI η p hp)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
      map_smul' := by
        intro c ω
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        ring }
  -- `|L(ω)| ≤ A δ` whenever `‖ω(x)‖ ≤ δ` for all `x`, where `A = Σ_{p ∈ s} ∫_{Q₁} |w_p|`
  set A : ℝ := ∑ p ∈ s, ∫ y in Q₁, |w p y| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
  have hest : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (δ : ℝ),
      (∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ δ) → |L ω| ≤ A * δ := by
    intro ω δ hδ
    have hterm : ∀ p ∈ s,
        |∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)| ≤
          (∫ y in Q₁, |w p y|) * δ := by
      intro p hp
      rw [← integral_mul_const δ (fun y => |w p y|)]
      refine (Real.norm_eq_abs _).symm.le.trans ?_
      refine norm_integral_le_of_norm_le ((hw p hp).abs.mul_const δ)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hev _ p).trans (hδ _)) (abs_nonneg _)
    calc |L ω|
        ≤ ∑ p ∈ s, |∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, (∫ y in Q₁, |w p y|) * δ := Finset.sum_le_sum hterm
      _ = A * δ := by rw [hA, Finset.sum_mul]
  -- sequential continuity: order-`0` uniform convergence on the common compact set `K`
  have hseq : ∀ (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) (m + 1)),
      TestFormOnConverges ωs 0 → Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    intro ωs hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := hunif 0
    rw [Metric.tendstoUniformlyOn_iff] at h0
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h0 _ hδ)
    refine ⟨N, fun j hj => ?_⟩
    have hbd : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ ε / (A + 1) := by
      intro x
      by_cases hx : x ∈ K
      · have := hN j hj x hx
        rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp] at this
        simp only [Function.comp_apply, Submodule.coe_zero, Pi.zero_apply, map_zero,
          dist_zero_left, LinearIsometryEquiv.norm_map] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
        exact hδ.le
    rw [Real.dist_eq, sub_zero]
    calc |L (ωs j)| ≤ A * (ε / (A + 1)) := hest (ωs j) _ hbd
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  exact ⟨hI, ⟨L, hseq⟩, fun ω => rfl⟩
/-- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30)): let
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy` for every test form `ω`,
where `p = (ι_p, b_p)`, `Q₁ = (0, 1)ⁿ`, `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and each `w_p` is
integrable on `Q₁`.  Then every `x ∈ spt D` is `Φ_p(y)` for some `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0` and
some `y ∈ [0, 1]ⁿ`.  Otherwise `x` lies outside the compact union `Z` of the closed faces
`Φ_p([0, 1]ⁿ)` with `∫_{Q₁} |w_p| ≠ 0`, so a ball `B_r(x)` misses `Z`.  If `spt ω ⊆ B_r(x)`, every
summand vanishes: `w_p = 0` a.e. on `Q₁` when `∫_{Q₁} |w_p| = 0`, and `ω = 0` on `Φ_p(Q₁) ⊆ Z`
otherwise.  So `D` vanishes on `B_r(x)` and `x ∈ zeroRegion D`, contradicting `x ∈ spt D`. -/
theorem Submission.cmcdtfrfic_support_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x := by
  classical
  intro P m s w D hw hD x hx
  by_contra hne
  -- `Z`: the union of the closed faces `Φ_p([0, 1]ⁿ)` over the `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0`
  let Z : Set (Euclid P) :=
    ⋃ p ∈ s.filter fun p => (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0,
      (fun z : Fin (m + 1) → ℝ =>
        WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, z j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ''
        Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  -- `Z` is compact: a finite union of continuous images of the compact cube
  have hZ : IsCompact Z := Finset.isCompact_biUnion _ fun p _ =>
    (isCompact_univ_pi fun _ => isCompact_Icc).image (by fun_prop)
  -- by assumption, `x ∉ Z`
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨p, hp, z, hz, hzx⟩ := Set.mem_iUnion₂.mp hxZ
    obtain ⟨hps, hpw⟩ := Finset.mem_filter.mp hp
    exact hne ⟨p, hps, hpw, WithLp.toLp 2 z, fun i => hz i (Set.mem_univ i), hzx⟩
  -- a ball `B_r(x)` disjoint from the closed set `Z`
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.mp hZ.isClosed.isOpen_compl x hxZ
  -- `D` vanishes on `B_r(x)`, so `x ∈ zeroRegion D`, contradicting `x ∈ spt D`
  refine hx.2 (Set.mem_sUnion.mpr ⟨Metric.ball x r, ⟨Metric.isOpen_ball,
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall, Set.subset_univ _, fun ω hω => ?_⟩,
    Metric.mem_ball_self hr⟩)
  rw [hD ω]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases hpw : (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) = 0
  · -- `∫_{Q₁} |w_p| = 0`: `w_p = 0` a.e. on `Q₁`, so the integrand vanishes a.e.
    have h0 := (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (w p y)) (hw p hp).abs).mp hpw
    refine integral_eq_zero_of_ae (h0.mono fun y hy => ?_)
    have hy' : w p y = 0 := abs_eq_zero.mp hy
    show w p y * _ = 0
    rw [hy', zero_mul]
  · -- `∫_{Q₁} |w_p| ≠ 0`: `Φ_p(Q₁) ⊆ Z` misses `B_r(x) ⊇ spt ω`, so the integrand vanishes on `Q₁`
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hyZ : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Z :=
      Set.mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpw⟩)
        ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
    have hω0 : (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hrZ (hω h) hyZ
    rw [hω0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]

/-- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30) and (34)): for faces
`p = (ι_p, b_p) ∈ s` with `ι_p` strictly increasing and densities `w_p` integrable on
`Q₁ = (0, 1)ⁿ`, put `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy`.  The integrands are
integrable and `D` is a current (I)–(II).  Every such `D` has (a) `M(D) ≤ Σ_p ∫_{Q₁} |w_p|`, since
`|ω(x)(e_{ι_p})| ≤ |ω(x)| ≤ 1` for admissible `ω`; (b) `M(∂D) ≤ Σ_p B_p` whenever
`|∫_{Q₁} w_p div G| ≤ B_p` for all smooth `G` with `|G| ≤ 1`, since `∂D(γ) = D(dγ)` and on the face
`p` the integrand `dγ(Φ_p(y))(e_{ι_p})` is `div G_p(y)` for a smooth `G_p` with
`|G_p| ≤ |γ ∘ Φ_p| ≤ 1`; (c) `spt D` lies in the closed faces with `∫_{Q₁} |w_p| ≠ 0`. -/
theorem Submission.cmcdtfr_face_integral_current : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ∧ (∀ B : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ B p) → D.boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, B p)) ∧ (∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x) := by
  intro P m s w hι hw
  -- (I)–(II): the integrands are integrable and the formula defines a current
  obtain ⟨hint, hex⟩ := Submission.cmcdtfrfic_current_exists P m s w hw
  -- (III)(c) is the support lemma; (a) and (b) bound each admissible evaluation
  refine ⟨hint, hex, fun D hD => ⟨?_, fun B hB => ?_,
    Submission.cmcdtfrfic_support_faces P m s w D hw hD⟩⟩
  · -- (a): for admissible `ω`, `|w_p(y) ω(Φ_p(y))(e_{ι_p})| ≤ |w_p(y)| |ω(Φ_p(y))| ≤ |w_p(y)|`
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hD ω]
    refine Finset.sum_le_sum fun p hp => (Real.le_norm_self _).trans
      (norm_integral_le_of_norm_le (hw p hp).abs (ae_of_all _ fun y => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (((Submission.cmcdtfrfic_coeff_bounds P (m + 1) _).1 p.1 (hι p hp)).trans (hω.2 _))
  · -- (b): for admissible `γ`, `∂D(γ) = D(dγ)`, and on the face `p` the integrand is
    -- `w_p div G_p` with `|G_p| ≤ |γ ∘ Φ_p| ≤ 1`, so the `p`-th summand is at most `B_p`
    refine sSup_le ?_
    rintro r ⟨γ, hγ, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [GeometricCurrentOn.boundary_apply, hD]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨G, hG, hGn, hGt⟩ := Submission.cmcdtfrfic_divergence_field P m
      (γ : DifferentialForm (Euclid P) m) p.1 (WithLp.toLp 2 fun i => (p.2 i : ℝ))
      γ.property.1.1 (hι p hp)
    calc _ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
          integral_congr_ae (ae_of_all _ fun y => congrArg (w p y * ·) (hGt y).symm)
      _ ≤ |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| := le_abs_self _
      _ ≤ B p := hB p hp G hG fun y => (hGn y).trans (hγ.2 _)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
