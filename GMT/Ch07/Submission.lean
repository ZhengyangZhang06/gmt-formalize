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

/-- Step 2 of the Lipschitz approximation lemma (Simon Ch. 5, Lemma 2.6, in Allard's theorem as used
for 7.4.3): orthonormal graph coordinates adapted to an `n`-plane `T₀ ⊆ ℝ^{n+k}`.  With orthonormal
bases `a` of `T₀` and `b` of `T₀ᗮ` (`dim T₀ᗮ = k`), `ι v = Σ vᵢaᵢ` and `ι' w = Σ wⱼbⱼ` are linear
isometries onto `T₀` and `T₀ᗮ`; hence `⟪ι v, ι' w⟫ = 0`, every `x = p_{T₀} x + (x − p_{T₀} x)` is
`ι v + ι' w`, and `p_{T₀}(ι v + ι' w) = ι v`. -/
theorem Submission.dorag_lip_orthonormal_coordinates : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))), Module.finrank ℝ T₀ = n → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ x, ∃ v w, x = ι v + ι' w) ∧ (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) := by
  intro n k T₀ hT₀
  -- `dim T₀ᗮ = k`, since `dim T₀ + dim T₀ᗮ = n + k`
  have hTo : Module.finrank ℝ T₀ᗮ = k := by
    have h := Submodule.finrank_add_finrank_orthogonal T₀
    rw [finrank_euclideanSpace_fin, hT₀] at h
    omega
  -- orthonormal bases of `T₀` and `T₀ᗮ` indexed by `Fin n` and `Fin k`
  let b := (stdOrthonormalBasis ℝ T₀).reindex (finCongr hT₀)
  let b' := (stdOrthonormalBasis ℝ T₀ᗮ).reindex (finCongr hTo)
  -- inverse coordinate maps followed by the inclusions of `T₀` and `T₀ᗮ`
  let ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k) := T₀.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k) := T₀ᗮ.subtypeₗᵢ.comp b'.repr.symm.toLinearIsometry
  have hιmem : ∀ v, ι v ∈ T₀ := fun v => (b.repr.symm v).2
  have hι'mem : ∀ w, ι' w ∈ T₀ᗮ := fun w => (b'.repr.symm w).2
  refine ⟨ι, ι', fun v w => Submodule.inner_right_of_mem_orthogonal (hιmem v) (hι'mem w), hιmem,
    ?_, ?_⟩
  · -- `x = p_{T₀} x + (x − p_{T₀} x)` with `p_{T₀} x ∈ T₀` and `x − p_{T₀} x ∈ T₀ᗮ`
    intro x
    refine ⟨b.repr ⟨T₀.starProjection x, Submodule.starProjection_apply_mem _ _⟩,
      b'.repr ⟨x - T₀.starProjection x, Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    simp [ι, ι']
  · -- `p_{T₀}` fixes `ι v ∈ T₀` and kills `ι' w ∈ T₀ᗮ`
    intro v w
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hιmem v),
      (Submodule.starProjection_apply_eq_zero_iff T₀).mpr (hι'mem w), add_zero]
/-- **Two-measure five-times covering bound**: the summation step after the 5-times Covering
Lemma (Simon Ch. 1, 3.4, chapter-01.txt lines 612–622) in the proof of the Lipschitz
approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 413–425 and 536–548).
If each `y ∈ A` has `0 < r(y) ≤ R₀`, `B_{r(y)}(y) ⊆ B` and `μ(A ∩ B_{5r(y)}(y)) ≤ c ν(B_{r(y)}(y))`,
then `μ(A) ≤ c ν(B)`.  Vitali's lemma (factor `5 > 3`) gives `u ⊆ A` with the balls
`B_{r(b)}(b)`, `b ∈ u`, pairwise disjoint, hence countable in the separable `ℝᴾ`, and
`A ⊆ ⋃_{b ∈ u} B_{5r(b)}(b)`; so `μ(A) ≤ Σ_b μ(A ∩ B_{5r(b)}(b)) ≤ c Σ_b ν(B_{r(b)}(b))
= c ν(⋃_b B_{r(b)}(b)) ≤ c ν(B)`. -/
theorem Submission.dorag_lip_vitali_two_measure_bound : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (A B : Set (Euclid P)) (r : Euclid P → ℝ) (R₀ : ℝ) (c : ℝ≥0∞), (∀ y ∈ A, 0 < r y ∧ r y ≤ R₀ ∧ closedBall y (r y) ⊆ B ∧ μ (A ∩ closedBall y (5 * r y)) ≤ c * ν (closedBall y (r y))) → μ A ≤ c * ν B := by
  intro P μ ν A B r R₀ c h
  -- Vitali selection with enlargement factor `5 > 3`.
  obtain ⟨u, huA, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    A id r R₀ (fun a ha => (h a ha).2.1) 5 (by norm_num)
  simp only [id] at hdisj hcov
  -- Disjoint balls with nonempty interior in the separable `ℝᴾ` are countably many.
  have hu : u.Countable := hdisj.countable_of_nonempty_interior fun a ha => by
    have hr := (h a (huA ha)).1
    exact ⟨a, interior_mono ball_subset_closedBall
      (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr)⟩
  -- `a ∈ B_{r(a)}(a) ⊆ B_{5r(b)}(b)`.
  have hAsub : A ⊆ ⋃ b ∈ u, A ∩ closedBall b (5 * r b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_iUnion₂.2 ⟨b, hb, ha, hab (mem_closedBall_self (h a ha).1.le)⟩
  calc μ A ≤ μ (⋃ b ∈ u, A ∩ closedBall b (5 * r b)) := measure_mono hAsub
    _ ≤ ∑' b : u, μ (A ∩ closedBall b (5 * r b)) := measure_biUnion_le μ hu _
    _ ≤ ∑' b : u, c * ν (closedBall b (r b)) :=
        ENNReal.tsum_le_tsum fun b => (h b (huA b.2)).2.2.2
    _ = c * ∑' b : u, ν (closedBall b (r b)) := ENNReal.tsum_mul_left
    _ = c * ν (⋃ b ∈ u, closedBall b (r b)) := by
        rw [measure_biUnion hu hdisj fun b _ => measurableSet_closedBall]
    _ ≤ c * ν B := by
        gcongr
        exact iUnion₂_subset fun b hb => (h b (huA hb)).2.2.1
/-- **A cone set lies in a bounded Lipschitz graph**: Steps 5–6 of the proof of the Lipschitz
approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 456–480: from
`|Q(y₂ − y₁)| ≤ CβL|y₁ − y₂|` and `Cβ ≤ ½`, "`|Q(y₁) − Q(y₂)| ≤ 2CβL|P(y₁) − P(y₂)|`", so by the
Lipschitz Extension Theorem (Ch. 2, 1.2, chapter-02.txt line 33) `G ⊆ graph f`, and replacing
`fʲ` by `max{min{fʲ, Cδ^{1/(2n+2)}}, −Cδ^{1/(2n+2)}}` gives `sup |f| ≤ Cδ^{1/(2n+2)}`).  Here
`P = p_{T₀}`, `Q = 1 − P`, `λ = lam`.  Writing `y − ξ = ιv_y + ι'w_y`, `Q(y − ξ) = ι'w_y`, so
`|w_y| ≤ A` and the cone condition gives `|w_{y₂} − w_{y₁}| ≤ 2λ|v_{y₂} − v_{y₁}|`; hence
`v_y ↦ w_y` is a well-defined `2λ`-Lipschitz map on `{v_y : y ∈ G}`, whose coordinates are
extended (McShane) and truncated to `[−A, A]`, giving `f` with `Lip f ≤ 2√k λ`, `|f| ≤ √k A` and
`G ⊆ {ξ + ιv + ι'f(v)}`. -/
theorem Submission.dorag_lip_cone_set_graph_extension : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (G : Set (Euclid (n + k))) (lam A : ℝ), (∀ x, ∃ v w, x = ι v + ι' w) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ lam → lam ≤ 1 / 2 → 0 ≤ A → (∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ lam * ‖y₂ - y₁‖) → (∀ y ∈ G, ‖(y - ξ) - T₀.starProjection (y - ξ)‖ ≤ A) → ∃ f : Euclid n → Euclid k, (∀ v w, ‖f v - f w‖ ≤ 2 * Real.sqrt k * lam * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ Real.sqrt k * A) ∧ G ⊆ range (fun v => ξ + ι v + ι' (f v)) := by
  intro n k T₀ ι ι' ξ G lam A hspan hproj hlam0 hlam1 hA hcone hbound
  classical
  -- Step 1: coordinates `y - ξ = ι (φ y) + ι' (ψ y)`, with `Q (y - ξ) = ι' (ψ y)`.
  choose φ ψ hφψ using fun y : Euclid (n + k) => hspan (y - ξ)
  have hψA : ∀ y ∈ G, ‖ψ y‖ ≤ A := by
    intro y hy
    have h := hbound y hy
    rw [hφψ y, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    exact h
  -- Step 2: the two-point estimate `|ψ y₂ - ψ y₁| ≤ 2λ |φ y₂ - φ y₁|`.
  have hdiff : ∀ y₁ y₂ : Euclid (n + k), y₂ - y₁ = ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁) := by
    intro y₁ y₂
    have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
    rw [e, hφψ y₁, hφψ y₂, map_sub, map_sub]
    abel
  have htwo : ∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖ψ y₂ - ψ y₁‖ ≤ 2 * lam * ‖φ y₂ - φ y₁‖ := by
    intro y₁ hy₁ y₂ hy₂
    have h := hcone y₁ hy₁ y₂ hy₂
    rw [hdiff y₁ y₂, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    have h2 : ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖ ≤ ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
      calc ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖
          ≤ ‖ι (φ y₂ - φ y₁)‖ + ‖ι' (ψ y₂ - ψ y₁)‖ := norm_add_le _ _
        _ = ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
    have h3 := mul_le_mul_of_nonneg_left h2 hlam0
    have h4 := mul_nonneg (sub_nonneg.mpr hlam1) (norm_nonneg (ψ y₂ - ψ y₁))
    nlinarith [norm_nonneg (ψ y₂ - ψ y₁), norm_nonneg (φ y₂ - φ y₁)]
  -- Step 3: a function `g` on `D := φ '' G` with `g (φ y) = ψ y`.
  set D : Set (Euclid n) := φ '' G
  let g : Euclid n → Euclid k := fun v => ψ (Function.invFunOn φ G v)
  have hg_eq : ∀ y ∈ G, g (φ y) = ψ y := by
    intro y hy
    obtain ⟨h1, h2⟩ := Function.invFunOn_pos (b := φ y) ⟨y, hy, rfl⟩
    have h := htwo y hy _ h1
    simp only [h2, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hgLip : ∀ v₁ ∈ D, ∀ v₂ ∈ D, ‖g v₁ - g v₂‖ ≤ 2 * lam * ‖v₁ - v₂‖ := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [hg_eq y₁ hy₁, hg_eq y₂ hy₂]
    exact htwo y₂ hy₂ y₁ hy₁
  -- Step 4: McShane extension of each coordinate (Simon Ch. 2, 1.2).
  have hcoordLip : ∀ j : Fin k,
      LipschitzOnWith (Real.toNNReal (2 * lam)) (fun v => g v j) D := by
    intro j
    apply LipschitzOnWith.of_dist_le'
    intro v₁ hv₁ v₂ hv₂
    rw [Real.dist_eq, dist_eq_norm]
    calc |g v₁ j - g v₂ j| = ‖(g v₁ - g v₂) j‖ := by rw [PiLp.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖g v₁ - g v₂‖ := PiLp.norm_apply_le _ j
      _ ≤ 2 * lam * ‖v₁ - v₂‖ := hgLip v₁ hv₁ v₂ hv₂
  choose h hhLip hhEq using fun j => (hcoordLip j).extend_real
  -- Step 5: truncation of each coordinate to `[-A, A]`.
  let F : Fin k → Euclid n → ℝ := fun j v => max (-A) (min A (h j v))
  have hFLip : ∀ j, LipschitzWith (Real.toNNReal (2 * lam)) (F j) :=
    fun j => ((hhLip j).const_min A).const_max (-A)
  have hFbound : ∀ j v, |F j v| ≤ A := by
    intro j v
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hFeq : ∀ y ∈ G, ∀ j, F j (φ y) = ψ y j := by
    intro y hy j
    have hmem : φ y ∈ D := ⟨y, hy, rfl⟩
    have e1 : h j (φ y) = g (φ y) j := (hhEq j hmem).symm
    rw [hg_eq y hy] at e1
    have hb : |ψ y j| ≤ A := by
      calc |ψ y j| = ‖ψ y j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ψ y‖ := PiLp.norm_apply_le _ j
        _ ≤ A := hψA y hy
    show max (-A) (min A (h j (φ y))) = ψ y j
    rw [e1, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  -- Step 6: assemble `f` from its coordinates.
  let f : Euclid n → Euclid k := fun v => WithLp.toLp 2 (fun j => F j v)
  have hf_apply : ∀ v j, f v j = F j v := fun v j => rfl
  have hK : ((Real.toNNReal (2 * lam) : NNReal) : ℝ) = 2 * lam :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v w
    rw [EuclideanSpace.norm_eq (f v - f w)]
    have hterm : ∀ j, ‖(f v - f w) j‖ ^ 2 ≤ (2 * lam * ‖v - w‖) ^ 2 := by
      intro j
      have h1 := (hFLip j).dist_le_mul v w
      rw [hK, Real.dist_eq, dist_eq_norm] at h1
      rw [PiLp.sub_apply, hf_apply, hf_apply, Real.norm_eq_abs, sq_abs]
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v - f w) j‖ ^ 2) ≤ √(∑ _j : Fin k, (2 * lam * ‖v - w‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * (2 * lam * ‖v - w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
      _ = 2 * √(k : ℝ) * lam * ‖v - w‖ := by ring
  · intro v
    rw [EuclideanSpace.norm_eq (f v)]
    have hterm : ∀ j, ‖(f v) j‖ ^ 2 ≤ A ^ 2 := by
      intro j
      rw [hf_apply, Real.norm_eq_abs, sq_abs]
      have h1 := hFbound j v
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v) j‖ ^ 2) ≤ √(∑ _j : Fin k, A ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hA]
  · -- Step 7: `G` lies in the graph `{ξ + ι v + ι' (f v)}`.
    intro y hy
    refine Set.mem_range.mpr ⟨φ y, ?_⟩
    have hfy : f (φ y) = ψ y := by
      apply PiLp.ext
      intro j
      rw [hf_apply]
      exact hFeq y hy j
    show ξ + ι (φ y) + ι' (f (φ y)) = y
    rw [hfy, add_assoc, ← hφψ y]
    abel
/-- **Cone condition and `Hⁿ` bound for a rotated Lipschitz graph**: Steps 8–9 of the proof of the
Lipschitz approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 519–521 and
544–545: `|Q(x − y)| ≤ Cβ|x − y|` on `F` "because `Lip f ≤ βL`", and `Hⁿ(B_{5σⱼ}(ξⱼ) ∩ F) ≤ Cσⱼⁿ`
"since `F` is the graph of the Lipschitz function `f` with `Lip f ≤ 1`").  Here
`Φ(v) = ξ + ιv + ι'f(v)`, `F = Φ(ℝⁿ)` and `P = p_{T₀}`, `Q = 1 − P`.  As `ι ⟂ ι'` are isometries,
`|ιa + ι'b|² = |a|² + |b|²`, and `P(ιa + ι'b) = ιa`; so (i) `|Q(Φv − Φv')| = |f v − f v'| ≤ Λ|v − v'|
≤ Λ|Φv − Φv'|`, and (ii) `F ∩ B_r(Φv₀) ⊆ Φ(Bⁿ_r(v₀))` with `Φ` `√2`-Lipschitz, whence
`Hⁿ(F ∩ B_r(x)) ≤ (√2)ⁿ ωₙ rⁿ` by Simon Ch. 2, 1.8(i). -/
theorem Submission.dorag_lip_graph_cone_hausdorff_bound : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (Λ : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ Λ → Λ ≤ 1 → (∀ v w, ‖f v - f w‖ ≤ Λ * ‖v - w‖) → (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ x' ∈ range (fun v => ξ + ι v + ι' (f v)), ‖(x - x') - T₀.starProjection (x - x')‖ ≤ Λ * ‖x - x'‖) ∧ (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ r : ℝ, 0 < r → μHE[n] (range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall x r) ≤ ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n)) := by
  intro n k T₀ ι ι' ξ f Λ horth hproj hΛ0 hΛ1 hf
  -- `Φ v − Φ v' = ι(v − v') + ι'(f v − f v')`, and Pythagoras `|ιa + ι'b|² = |a|² + |b|²`.
  have hdiff : ∀ v v' : Euclid n, (ξ + ι v + ι' (f v)) - (ξ + ι v' + ι' (f v')) =
      ι (v - v') + ι' (f v - f v') := by
    intro v v'; rw [map_sub, map_sub]; abel
  have hpyth : ∀ (a : Euclid n) (b : Euclid k), ‖ι a + ι' b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b
    rw [norm_add_sq_real, horth a b, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
  have hlow : ∀ (a : Euclid n) (b : Euclid k), ‖a‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have h := hpyth a b
    have h2 : ‖a‖ ^ 2 ≤ ‖ι a + ι' b‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖b‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hQ : ∀ (a : Euclid n) (b : Euclid k),
      (ι a + ι' b) - T₀.starProjection (ι a + ι' b) = ι' b := by
    intro a b; rw [hproj]; abel
  constructor
  · -- (i) `|Q(x − x')| = |f v − f v'| ≤ Λ|v − v'| ≤ Λ|x − x'|`.
    rintro x ⟨v, rfl⟩ x' ⟨v', rfl⟩
    dsimp only
    rw [hdiff, hQ, LinearIsometry.norm_map]
    exact (hf v v').trans (mul_le_mul_of_nonneg_left (hlow _ _) hΛ0)
  · -- (ii) `F ∩ B_r(Φ v₀) ⊆ Φ(Bⁿ_r(v₀))`, `Φ` is `√2`-Lipschitz and `Hⁿ = Lⁿ` on `ℝⁿ`.
    rintro x ⟨v₀, rfl⟩ r hr
    set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v)
    have hdiffΦ : ∀ v v', Φ v - Φ v' = ι (v - v') + ι' (f v - f v') := fun v v' => hdiff v v'
    have hsub : range Φ ∩ closedBall (Φ v₀) r ⊆ Φ '' closedBall v₀ r := by
      rintro x ⟨⟨v, rfl⟩, hx⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc ‖v - v₀‖ ≤ ‖ι (v - v₀) + ι' (f v - f v₀)‖ := hlow _ _
        _ = ‖Φ v - Φ v₀‖ := by rw [hdiffΦ]
        _ ≤ r := hx
    have hLip : LipschitzOnWith (NNReal.sqrt 2) Φ (closedBall v₀ r) := by
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro v v'
      rw [dist_eq_norm, dist_eq_norm, Real.coe_sqrt, NNReal.coe_ofNat]
      have h := hpyth (v - v') (f v - f v')
      have hfv := hf v v'
      have hsq : ‖Φ v - Φ v'‖ ^ 2 ≤ (Real.sqrt 2 * ‖v - v'‖) ^ 2 := by
        rw [hdiffΦ, h, mul_pow, Real.sq_sqrt (by norm_num)]
        have h1 : ‖f v - f v'‖ ^ 2 ≤ (Λ * ‖v - v'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hfv 2
        have h2 : (Λ * ‖v - v'‖) ^ 2 ≤ ‖v - v'‖ ^ 2 := by
          rw [mul_pow]
          have : Λ ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg ‖v - v'‖]
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have hpow : ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) := by
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, NNReal.coe_ofNat,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc μHE[n] (range Φ ∩ closedBall (Φ v₀) r) ≤ μHE[n] (Φ '' closedBall v₀ r) := measure_mono hsub
      _ ≤ ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (closedBall v₀ r) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
      _ = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, hpow]
          unfold unitBallVolume
          ring
/-- **Simon Ch. 5, proof of 2.6, (3)–(4)**, with the case `|y₂ − y₁| > σ₀/2` added (good-set cone
estimate of the Lipschitz approximation).  Put `t = |y₂ − y₁|`, `P = p_{T₀}`, `Q = 1 − P`.
If `t ≤ σ₀/2`, the affine approximation at `(y₁, t)` gives a plane `S` with
`|(y₂ − y₁) − p_S(y₂ − y₁)| ≤ C₃εt`.  Comparing the tilt integrals of `S` and `T₀` over
`B_{t/2}(y₁)` and using the lower density bound yields `|p_S − P|² ≤ (8C₃ + 2^{n+3})β²L²/ω`, and
the Hilbert–Schmidt bound `|(p_S − P)u| ≤ |p_S − P||u|` finishes.  If `t > σ₀/2`, flatness at
scale `σ₀` gives `|Q(y₂ − y₁)| ≤ 2C₆εσ₀ ≤ 4C₆βLt`.  Here `C₈ = max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)`
and `ω = |B₁ⁿ|`. -/
theorem Submission.dorag_lip_good_set_cone_estimate : ∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
  intro n k C₃ C₆ hC₃ hC₆
  -- Hilbert–Schmidt bound `‖A u‖ ≤ |A| ‖u‖` with `|A|² = ∑ᵢ ‖A eᵢ‖²`
  have hHS : ∀ (A : Euclid (n + k) →L[ℝ] Euclid (n + k)) (u : Euclid (n + k)),
      ‖A u‖ ≤ Real.sqrt (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ := by
    intro A u
    have hu : u = ∑ i : Fin (n + k), u i • EuclideanSpace.single i (1 : ℝ) := by
      have := (EuclideanSpace.basisFun (Fin (n + k)) ℝ).sum_repr u
      simpa using this.symm
    have hAu : A u = ∑ i : Fin (n + k), u i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [hu]
/-- **Simon Ch. 5, proof of 2.6, (9)–(10), corrected** (estimate (10') of the Lipschitz
approximation: `B_σ(η)` becomes `B_{3s}(η)`, and as only `κσ₀ ≤ 1` is used there is no additive
error `Cδσⁿ`).
For `η ∈ (F ∖ spt μ) ∩ B_{σ₀/4}(ξ)` let `y ∈ spt μ` be a nearest point and `s = |y − η|/2`.  Then
`μ(B_s(η)) = 0`, the density bounds give `ωsⁿ/2 ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`, and monotonicity with
radii `s < 3s` and `e^{3κs} ≤ 2` gives `μ(B_{3s}(η)) ≤ 2·3ⁿs⁻²∫_{B_{3s}(η)}|p_x^⊥(x − η)|² dμ`.
Splitting `p_x^⊥(x − η) = Q(x − η) + (P − p_x)(x − η)` (cone condition on `F`, Hilbert–Schmidt
bound) and absorbing the `λ²`-term yields `sⁿ ≤ C₉[μ(B_{3s}(η) ∖ F) + ∫_{B_{3s}(η)}|p_x − P|² dμ]`,
with `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`. -/
theorem Submission.dorag_lip_off_support_estimate : ∀ (n k : ℕ), ∃ lam₀ C₉ : ℝ, 0 < lam₀ ∧ 0 < C₉ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (F : Set (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ κ lam : ℝ), 0 < σ₀ → 0 ≤ κ → κ * σ₀ ≤ 1 → 0 ≤ lam → lam ≤ lam₀ → ξ ∈ μ.support → (∀ x ∈ F, ∀ x' ∈ F, ‖(x - x') - T₀.starProjection (x - x')‖ ≤ lam * ‖x - x'‖) → (∀ y ∈ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 8 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 8 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ (y : Euclid (n + k)) (s t : ℝ), y ∈ closedBall ξ (σ₀ / 4) → 0 < s → s < t → t ≤ 3 * σ₀ / 8 → ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * μ (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (τ x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ) → ∀ η ∈ (F \ μ.support) ∩ closedBall ξ (σ₀ / 4), ∃ s : ℝ, ∃ y ∈ μ.support, 0 < s ∧ 2 * s ≤ dist η ξ ∧ dist y η = 2 * s ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) := by
  intro n k
  -- Hilbert–Schmidt bound `‖A u‖² ≤ (∑ᵢ ‖A eᵢ‖²) ‖u‖²`
  have hHS : ∀ (A : Euclid (n + k) →L[ℝ] Euclid (n + k)) (u : Euclid (n + k)),
      ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
    intro A u
    have hu : ∑ i : Fin (n + k), u i • EuclideanSpace.single i (1 : ℝ) = u := by
      have h := (EuclideanSpace.basisFun (Fin (n + k)) ℝ).sum_repr u
      simpa using h
    have hAu : A u = ∑ i : Fin (n + k), u i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← hu]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul A _ _
    have h1 : ‖A u‖ ≤ ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAu]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
        (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ i : Fin (n + k), |u i| ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => sq_abs _
    rw [h3] at h2
    have h4 : ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤
        Real.sqrt (‖u‖ ^ 2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
      (le_abs_self _).trans (Real.abs_le_sqrt h2)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
    calc ‖A u‖ ≤ _ := h1
      _ ≤ _ := h4
      _ = _ := mul_comm _ _
  -- `‖b − c‖² ≤ 2‖a − b‖² + 2‖a − c‖²`
  have hsq : ∀ a b c : Euclid (n + k), ‖b - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 := by
    intro a b c
    have h : ‖b - c‖ ≤ ‖a - b‖ + ‖a - c‖ := by
      calc ‖b - c‖ = ‖(a - c) - (a - b)‖ := by congr 1; abel
        _ ≤ ‖a - c‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - c‖ := add_comm _ _
    have h0 : 0 ≤ ‖b - c‖ := norm_nonneg _
    have hab := norm_nonneg (a - b)
    have hac := norm_nonneg (a - c)
    have hmul : ‖b - c‖ * ‖b - c‖ ≤ (‖a - b‖ + ‖a - c‖) * (‖a - b‖ + ‖a - c‖) :=
      mul_le_mul h h h0 (by positivity)
    nlinarith [sq_nonneg (‖a - b‖ - ‖a - c‖)]
  -- pointwise Hilbert–Schmidt triangle bound `|B − C|² ≤ 2|A − B|² + 2|A − C|²`, in `ℝ≥0∞`
  have hpt : ∀ A B C : Euclid (n + k) →L[ℝ] Euclid (n + k),
      ENNReal.ofReal (∑ i : Fin (n + k), ‖B (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro A B C
    have hle : ∑ i : Fin (n + k), ‖B (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
        2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 +
        2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hsq _ _ _
    refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- from the `ℝ≥0∞` inequalities to a real one
  have hreal_of : ∀ {h w X Y s : ℝ} {m : ℝ≥0∞}, 0 ≤ h → 0 ≤ w → 0 ≤ X → 0 ≤ Y →
      ENNReal.ofReal h * m ≤ 2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y →
      ENNReal.ofReal w * ENNReal.ofReal s ≤ 2 * m → h * w * s ≤ 4 * X + 4 * Y := by
    intro h w X Y s m hh hw hX hY h1 h2
    have h3 : ENNReal.ofReal (h * w * s) ≤ ENNReal.ofReal (4 * X + 4 * Y) := by
      calc ENNReal.ofReal (h * w * s)
          = ENNReal.ofReal h * (ENNReal.ofReal w * ENNReal.ofReal s) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hh hw), ENNReal.ofReal_mul hh, mul_assoc]
        _ ≤ ENNReal.ofReal h * (2 * m) := by gcongr
        _ = 2 * (ENNReal.ofReal h * m) := by ring
        _ ≤ 2 * (2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y) := by gcongr
        _ = ENNReal.ofReal (4 * X + 4 * Y) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_ofNat]
            ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have hC₃0 : 0 < C₃ := by linarith
  -- dividing out the radius factor
  have hdiv : ∀ {h w e b l s : ℝ}, 0 < w → 0 < s → 0 ≤ e → e ≤ b * l →
      h * w * s ≤ 4 * (C₃ * e ^ 2 * s) + 4 * (b ^ 2 * l ^ 2 * (2 ^ n * s)) →
      h ≤ (8 * C₃ + 2 ^ (n + 3)) / w * (b * l) ^ 2 := by
    intro h w e b l s hw hs he hebl H
    have h1 : h * w ≤ 4 * C₃ * e ^ 2 + 4 * 2 ^ n * (b * l) ^ 2 := by
      have : h * w * s ≤ (4 * C₃ * e ^ 2 + 4 * 2 ^ n * (b * l) ^ 2) * s := by
        calc h * w * s ≤ _ := H
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hs
    have he2 : e ^ 2 ≤ (b * l) ^ 2 := pow_le_pow_left₀ he hebl 2
    have h2n : (2:ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
    have hp : (0:ℝ) ≤ 2 ^ n := by positivity
    have hb : 0 ≤ (b * l) ^ 2 := sq_nonneg _
    have h2 : h * w ≤ (8 * C₃ + 2 ^ (n + 3)) * (b * l) ^ 2 := by
      rw [h2n]
      nlinarith [mul_le_mul_of_nonneg_left he2 hC₃0.le, mul_nonneg hC₃0.le hb, mul_nonneg hp hb]
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    exact h2
  -- the constants: `ω = |B₁ⁿ|` and `C₈ = max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)`
  have hvol_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume; exact measure_ball_pos _ _ one_pos
  have hvol_lt : unitBallVolume n < ⊤ := by
    unfold unitBallVolume; exact measure_ball_lt_top
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hw_pos : 0 < w := by rw [hw]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_lt.ne
  have hw_eq : unitBallVolume n = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hvol_lt.ne]
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (8 * C₃ + 2 ^ (n + 3)) / w := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C : ℝ, C = max (C₃ + Real.sqrt K) (4 * C₆) := ⟨_, rfl⟩
  have hC₈a : C₃ + Real.sqrt K ≤ C₈ := by rw [hC₈]; exact le_max_left _ _
  have hC₈b : 4 * C₆ ≤ C₈ := by rw [hC₈]; exact le_max_right _ _
  refine ⟨C₈, by linarith, ?_⟩
  intro μ τ T₀ ξ σ₀ ε β L hmeas hσ₀ hε hβ hL hεβL H1 H2 H3 y₁ hy₁ y₂ hy₂ Hgood
  have hβL : 0 < β * L := mul_pos hβ hL
  -- a.e.-measurability of the tilt integrands
  have haem : ∀ S : Submodule ℝ (Euclid (n + k)), AEMeasurable (fun x => ENNReal.ofReal
      (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) μ := by
    intro S
    have hc : Continuous (fun A : Euclid (n + k) →L[ℝ] Euclid (n + k) => ENNReal.ofReal
        (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) := by
      refine ENNReal.continuous_ofReal.comp ?_
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
    exact (hc.comp_aestronglyMeasurable hmeas).aemeasurable
  -- integrating a pointwise bound over a set
  have hlint : ∀ {s : Set (Euclid (n + k))} {f g : Euclid (n + k) → ℝ≥0∞} {c : ℝ≥0∞},
      AEMeasurable f (μ.restrict s) → (∀ x, c ≤ 2 * f x + 2 * g x) →
      c * μ s ≤ 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
    intro s f g c hf hfg
    rw [← setLIntegral_const]
    calc ∫⁻ _ in s, c ∂μ ≤ ∫⁻ x in s, (2 * f x + 2 * g x) ∂μ := lintegral_mono hfg
      _ = ∫⁻ x in s, 2 * f x ∂μ + ∫⁻ x in s, 2 * g x ∂μ :=
          lintegral_add_left' (hf.const_mul 2) _
      _ = 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
          rw [lintegral_const_mul' 2 f ENNReal.ofNat_ne_top,
            lintegral_const_mul' 2 g ENNReal.ofNat_ne_top]
  rcases (norm_nonneg (y₂ - y₁)).eq_or_lt with ht0 | htpos
  · have hu0 : y₂ - y₁ = 0 := norm_eq_zero.1 ht0.symm
    rw [hu0]; simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖y₂ - y₁‖ = t := ⟨_, rfl⟩
  rw [ht] at htpos ⊢
  rcases le_or_gt t (σ₀ / 2) with hts | hts
  · -- Case `0 < t ≤ σ₀ / 2`.
    obtain ⟨S, hS1, hS2⟩ := H1 y₁ hy₁ t htpos hts
    have hgood := Hgood t htpos hts
    have hy₂ball : y₂ ∈ μ.support ∩ closedBall y₁ t :=
      ⟨hy₂.1, mem_closedBall.2 (le_of_eq (by rw [dist_eq_norm, ht]))⟩
    have hQS : ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ ≤ C₃ * ε * t := hS1 y₂ hy₂ball
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = ∑ i : Fin (n + k),
        ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := ⟨_, rfl⟩
    have hh0 : 0 ≤ h := by rw [hh_def]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hint := hlint (s := closedBall y₁ (t / 2)) (haem S).restrict
      (fun x => hpt ((τ x).starProjection) S.starProjection T₀.starProjection)
    rw [← hh_def] at hint
    have hint2 : ENNReal.ofReal h * μ (closedBall y₁ (t / 2)) ≤
        2 * ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n) +
          2 * ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by
      refine hint.trans ?_
      gcongr
    have hdens := H2 y₁ hy₁ (t / 2) (by positivity) (by linarith)
    rw [hw_eq] at hdens
    have hreal := hreal_of hh0 hw_pos.le (by positivity) (by positivity) hint2 hdens
    have htn : t ^ n = 2 ^ n * (t / 2) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [htn] at hreal
    have hhK : h ≤ K * (β * L) ^ 2 := by
      rw [hK_def]
      exact hdiv hw_pos (by positivity) hε hεβL hreal
    have hsqrt : Real.sqrt h ≤ Real.sqrt K * (β * L) := by
      calc Real.sqrt h ≤ Real.sqrt (K * (β * L) ^ 2) := Real.sqrt_le_sqrt hhK
        _ = Real.sqrt K * (β * L) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hβL.le]
    have hHS' := hHS (S.starProjection - T₀.starProjection) (y₂ - y₁)
    simp only [_root_.sub_apply] at hHS'
    rw [← hh_def, ht] at hHS'
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - y₁) - S.starProjection (y₂ - y₁)) +
            (S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁))‖ := by
          congr 1; abel
      _ ≤ ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ +
            ‖S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ := norm_add_le _ _
      _ ≤ C₃ * ε * t + Real.sqrt h * t := add_le_add hQS hHS'
      _ ≤ C₃ * (β * L) * t + Real.sqrt K * (β * L) * t := by
          have e1 : C₃ * ε * t ≤ C₃ * (β * L) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL hC₃0.le) htpos.le
          have e2 : Real.sqrt h * t ≤ Real.sqrt K * (β * L) * t :=
            mul_le_mul_of_nonneg_right hsqrt htpos.le
          linarith
      _ = (C₃ + Real.sqrt K) * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈a (by positivity)
      _ = C₈ * β * L * t := by ring
  · -- Case `t > σ₀ / 2`.
    have hsub : ∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), y ∈ μ.support ∩ closedBall ξ σ₀ :=
      fun y hy => ⟨hy.1, closedBall_subset_closedBall (by linarith) hy.2⟩
    have h1 := H3 y₁ (hsub y₁ hy₁)
    have h2 := H3 y₂ (hsub y₂ hy₂)
    have hQ : (y₂ - y₁) - T₀.starProjection (y₂ - y₁) =
        ((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) - ((y₁ - ξ) - T₀.starProjection (y₁ - ξ)) := by
      have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
      rw [e, map_sub T₀.starProjection (y₂ - ξ) (y₁ - ξ)]; abel
    have hC₆0 : 0 ≤ C₆ := by linarith
    have hCε : 0 ≤ C₆ * ε := mul_nonneg hC₆0 hε
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) -
            ((y₁ - ξ) - T₀.starProjection (y₁ - ξ))‖ := by rw [hQ]
      _ ≤ ‖(y₂ - ξ) - T₀.starProjection (y₂ - ξ)‖ + ‖(y₁ - ξ) - T₀.starProjection (y₁ - ξ)‖ :=
          norm_sub_le _ _
      _ ≤ C₆ * ε * σ₀ + C₆ * ε * σ₀ := add_le_add h2 h1
      _ = 2 * (C₆ * ε) * σ₀ := by ring
      _ ≤ 2 * (C₆ * ε) * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * C₆ * ε * t := by ring
      _ ≤ 4 * C₆ * (β * L) * t := by
          have : 0 ≤ 4 * C₆ := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL this) htpos.le
      _ = 4 * C₆ * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈b (by positivity)
      _ = C₈ * β * L * t := by ring
    calc ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
      _ = (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
          rw [h3, mul_comm]
  -- pointwise splitting `u - S u = (u - T u) + (T u - S u)` with the Hilbert–Schmidt bound
  have hsplit : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (r q : ℝ),
      ‖u‖ ≤ r → ‖u - T.starProjection u‖ ≤ q →
      ‖u - S.starProjection u‖ ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 *
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    intro T S u r q hr hq
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hA := hHS (T.starProjection - S.starProjection) u
    have e : ∑ i : Fin (n + k), ‖(T.starProjection - S.starProjection)
        (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_apply, norm_sub_rev]
    rw [e, sub_apply] at hA
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hur : ‖u‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hu0 hr 2
    have hq2 : ‖u - T.starProjection u‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have htri : ‖u - S.starProjection u‖ ≤
        ‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖ := by
      have e2 : u - S.starProjection u =
          (u - T.starProjection u) + (T.starProjection u - S.starProjection u) := by abel
      rw [e2]
      exact norm_add_le _ _
    have hB : ‖T.starProjection u - S.starProjection u‖ ^ 2 ≤
        (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * r ^ 2 :=
      hA.trans (mul_le_mul_of_nonneg_left hur hHS0)
    have ha0 : 0 ≤ ‖u - T.starProjection u‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖T.starProjection u - S.starProjection u‖ := norm_nonneg _
    have hc0 : 0 ≤ ‖u - S.starProjection u‖ := norm_nonneg _
    have hsq : ‖u - S.starProjection u‖ ^ 2 ≤
        (‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖) ^ 2 :=
      pow_le_pow_left₀ hc0 htri 2
    nlinarith [sq_nonneg (‖u - T.starProjection u‖ - ‖T.starProjection u - S.starProjection u‖)]
  -- the pointwise bound in `ℝ≥0∞`, in the two cases `x ∈ F` / `x ∉ F`
  have hptE : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (s lam : ℝ)
      (c : ℝ≥0∞), ‖u‖ ≤ 3 * s →
      (‖u - T.starProjection u‖ ≤ lam * (3 * s) ∨ c = ENNReal.ofReal (18 * s ^ 2)) →
      ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + c + ENNReal.ofReal (18 * s ^ 2) *
          ENNReal.ofReal (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro T S u s lam c hu h
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases h with hq | hc
    · have h1 := hsplit T S u (3 * s) (lam * (3 * s)) hu hq
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_self_add le_rfl
    · have hq : ‖u - T.starProjection u‖ ≤ 3 * s := by
        calc ‖u - T.starProjection u‖ = ‖Tᗮ.starProjection u‖ := by
              rw [Submodule.starProjection_orthogonal_val]
          _ ≤ ‖u‖ := Submodule.norm_starProjection_apply_le _ _
          _ ≤ 3 * s := hu
      have h1 := hsplit T S u (3 * s) (3 * s) hu hq
      rw [hc]
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_add_self le_rfl
  -- monotonicity with radii `s < 3 s`, combined with `e^{3κs} ≤ 2`
  have hexpb : ∀ (κ s : ℝ) (a J I₂ : ℝ≥0∞), 0 ≤ κ → 0 < s → κ * (3 * s) ≤ 3 / 8 →
      ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a ≤ J →
      J ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * I₂ →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := by
    intro κ s a J I₂ hκ hs hκs hM hJ
    have hexp : Real.exp (κ * (3 * s)) ≤ 2 := by
      have h0 : 0 ≤ κ * (3 * s) := by positivity
      calc Real.exp (κ * (3 * s)) ≤ (2 + κ * (3 * s)) / (2 - κ * (3 * s)) :=
            Real.exp_le_two_add_div_two_sub h0 (by linarith)
        _ ≤ 2 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
    have hc : 0 ≤ Real.exp (κ * (3 * s)) * (3 * s) ^ n := by positivity
    have hcinv : ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
        ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one]
      congr 1
      have h1 : Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s))) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h2 : (3 * s) ^ n / (3 * s) ^ n = 1 := div_self (by positivity)
      calc Real.exp (κ * (3 * s)) * (3 * s) ^ n * (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n)
          = (Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s)))) *
            ((3 * s) ^ n / (3 * s) ^ n) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    have hcs : Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2)) ≤
        2 * 3 ^ n / s ^ 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), mul_pow, pow_add]
      have hpos : 0 ≤ 3 ^ n * s ^ n * s ^ 2 := by positivity
      nlinarith
    calc a = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a) := by
          rw [← mul_assoc, hcinv, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (1 / s ^ (n + 2)) * I₂) := mul_le_mul_right (hM.trans hJ) _
      _ = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2))) * I₂ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
      _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hcs) _
  -- the final absorption argument (pure `ℝ≥0∞` arithmetic)
  have hfinal : ∀ (ω s lam : ℝ) (a I₂ X₁ X₂ : ℝ≥0∞), 0 < ω → 0 < s →
      72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 → ENNReal.ofReal (ω * s ^ n / 2) ≤ a →
      a ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ →
      I₂ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a + ENNReal.ofReal (18 * s ^ 2) * X₁ +
        ENNReal.ofReal (18 * s ^ 2) * X₂ →
      ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
    intro ω s lam a I₂ X₁ X₂ hω hs hlam2 ha_lower ha_upper haI hI
    have e1 : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have e2 : ENNReal.ofReal (36 * 3 ^ n) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have hmain : a ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
        ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      calc a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := haI
        _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a +
            ENNReal.ofReal (18 * s ^ 2) * X₁ + ENNReal.ofReal (18 * s ^ 2) * X₂) :=
            mul_le_mul_right hI _
        _ = ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
            ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
            rw [e1, e2]
            ring
    have hlamterm : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a ≤
        ENNReal.ofReal (ω * s ^ n / 4) := by
      calc ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a
          ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) :=
            mul_le_mul_right ha_upper _
        _ = ENNReal.ofReal (72 * 15 ^ n * lam ^ 2 * (ω * s ^ n)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (15 : ℝ) ^ n = 3 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
            ring
        _ ≤ ENNReal.ofReal (1 / 4 * (ω * s ^ n)) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right hlam2 (by positivity)
        _ = ENNReal.ofReal (ω * s ^ n / 4) := by
            congr 1
            ring
    have hfin : ENNReal.ofReal (ω * s ^ n / 4) ≤ ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      have h1 : ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4) ≤
          ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
        calc ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4)
            = ENNReal.ofReal (ω * s ^ n / 2) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
          _ ≤ a := ha_lower
          _ ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
              ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := hmain
          _ ≤ ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) :=
              add_le_add hlamterm le_rfl
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp h1
    calc ENNReal.ofReal (s ^ n) = ENNReal.ofReal (4 / ω) * ENNReal.ofReal (ω * s ^ n / 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_mul_div_comm, eq_div_iff (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (4 / ω) * (ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂)) :=
          mul_le_mul_right hfin _
      _ = ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  -- Step 0: the constants `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`
  have hV_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact measure_ball_pos _ _ one_pos
  have hV_lt : unitBallVolume n < ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos hV_pos.ne' hV_lt.ne
  have hV_eq : unitBallVolume n = ENNReal.ofReal ω := by
    rw [hω_def, ENNReal.ofReal_toReal hV_lt.ne]
  refine ⟨1 / Real.sqrt (288 * 15 ^ n), 144 * 3 ^ n / ω, by positivity, by positivity, ?_⟩
  intro μ τ T₀ F ξ σ₀ κ lam hσ₀ hκ hκσ hlam hlam₀ hξ hF hDa hDb hM2 η hη
  obtain ⟨⟨hηF, hηS⟩, hηξ'⟩ := hη
  have hηξ : dist η ξ ≤ σ₀ / 4 := mem_closedBall.mp hηξ'
  -- `72·15ⁿ·λ² ≤ 1/4` for `0 ≤ λ ≤ λ₀`
  have hlam2 : 72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 := by
    have hpos : (0 : ℝ) < 288 * 15 ^ n := by positivity
    have hsq : lam ^ 2 ≤ 1 / (288 * 15 ^ n) := by
      have h1 : lam ^ 2 ≤ (1 / Real.sqrt (288 * 15 ^ n)) ^ 2 := pow_le_pow_left₀ hlam hlam₀ 2
      rwa [div_pow, Real.sq_sqrt hpos.le, one_pow] at h1
    calc 72 * 15 ^ n * lam ^ 2 ≤ 72 * 15 ^ n * (1 / (288 * 15 ^ n)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 1 / 4 := by
          rw [mul_one_div, div_eq_iff hpos.ne']
          ring
  -- Step 1: nearest point of the support
  have hSc : IsClosed μ.support := Measure.isClosed_support
  have hSne : μ.support.Nonempty := ⟨ξ, hξ⟩
  have hd_pos : 0 < Metric.infDist η μ.support := (hSc.notMem_iff_infDist_pos hSne).mp hηS
  have hd_le : Metric.infDist η μ.support ≤ dist η ξ := Metric.infDist_le_dist_of_mem hξ
  obtain ⟨y, hyS, hyd⟩ := hSc.exists_infDist_eq_dist hSne η
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Metric.infDist η μ.support / 2 := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]
    positivity
  have h2s : 2 * s ≤ dist η ξ := by
    rw [hs_def]
    linarith
  have hyη : dist y η = 2 * s := by
    rw [dist_comm, ← hyd, hs_def]
    ring
  have hs8 : s ≤ σ₀ / 8 := by linarith
  have hyξ : dist y ξ ≤ σ₀ / 2 := by linarith [dist_triangle y η ξ]
  refine ⟨s, y, hyS, hs, h2s, hyη, ?_⟩
  -- Step 2: the small ball around `η` misses the support
  have hμs0 : μ (closedBall η s) = 0 := by
    have hsub : closedBall η s ⊆ μ.supportᶜ := by
      intro x hx
      rw [mem_compl_iff]
      intro hxS
      have h1 := Metric.infDist_le_dist_of_mem (x := η) hxS
      have h2 : dist x η ≤ s := mem_closedBall.mp hx
      rw [dist_comm] at h1
      linarith
    exact measure_mono_null hsub (Measure.measure_compl_support (μ := μ))
  -- Step 3: mass bounds `½ωsⁿ ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`
  have hsub1 : closedBall y s ⊆ closedBall η (3 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y η]
  have hsub2 : closedBall η (3 * s) ⊆ closedBall y (5 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    have h := dist_triangle x η y
    rw [dist_comm η y] at h
    linarith
  have hDb' := hDb y ⟨hyS, mem_closedBall.mpr hyξ⟩ s hs hs8
  have hDa' := hDa y (mem_closedBall.mpr hyξ) (5 * s) (by positivity) (by linarith)
  have ha_lower : ENNReal.ofReal (ω * s ^ n / 2) ≤ μ (closedBall η (3 * s)) := by
    have h1 : ENNReal.ofReal (ω * s ^ n) ≤ 2 * μ (closedBall η (3 * s)) := by
      calc ENNReal.ofReal (ω * s ^ n) = unitBallVolume n * ENNReal.ofReal (s ^ n) := by
            rw [hV_eq, ENNReal.ofReal_mul hω_pos.le]
        _ ≤ 2 * μ (closedBall y s) := hDb'
        _ ≤ 2 * μ (closedBall η (3 * s)) := mul_le_mul_right (measure_mono hsub1) _
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul' h1
  have ha_upper : μ (closedBall η (3 * s)) ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
    calc μ (closedBall η (3 * s)) ≤ μ (closedBall y (5 * s)) := measure_mono hsub2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * s) ^ n) := hDa'
      _ = ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
        rw [hV_eq, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  -- Step 4: monotonicity at `η` with radii `s < 3 s`
  have hM2' := hM2 η s (3 * s) hηξ' hs (by linarith) (by linarith)
  rw [hμs0, mul_zero, zero_add] at hM2'
  have hJ : ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ ≤
      ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s) \ closedBall η s, ENNReal.ofReal (1 / s ^ (n + 2)) *
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_closedBall) ?_
          intro x hx
          have hx2 : s < ‖x - η‖ := by
            rw [← dist_eq_norm]
            have h := hx.2
            rw [mem_closedBall, not_le] at h
            exact h
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)
              ≤ ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / s ^ (n + 2) := by
                gcongr
            _ = 1 / s ^ (n + 2) * ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 := by ring
      _ = ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
  -- Step 5: the exponential factor
  have hκs : κ * (3 * s) ≤ 3 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hκ]
  have ha_I2 := hexpb κ s _ _ _ hκ hs hκs hM2' hJ
  -- Step 6: pointwise bound on the ball `B_{3s}(η)`
  obtain ⟨M, hM_def⟩ : ∃ M : Set (Euclid (n + k)),
      M = toMeasurable μ (closedBall η (3 * s) \ F) := ⟨_, rfl⟩
  have hMmeas : MeasurableSet M := by
    rw [hM_def]
    exact measurableSet_toMeasurable _ _
  have hMsub : closedBall η (3 * s) \ F ⊆ M := by
    rw [hM_def]
    exact subset_toMeasurable _ _
  have hMmu : μ M = μ (closedBall η (3 * s) \ F) := by
    rw [hM_def]
    exact measure_toMeasurable _
  have hpt : ∀ x ∈ closedBall η (3 * s),
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
          M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
          ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
            ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro x hx
    have hxr : ‖x - η‖ ≤ 3 * s := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hx
    apply hptE T₀ (τ x) (x - η) s lam _ hxr
    by_cases hxF : x ∈ F
    · left
      exact (hF x hxF η hηF).trans (mul_le_mul_of_nonneg_left hxr hlam)
    · right
      exact Set.indicator_of_mem (hMsub ⟨hx, hxF⟩) _
  -- Step 7: integration over `B_{3s}(η)`
  have hI2 : ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
        ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
        ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
          (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
            ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂μ :=
          setLIntegral_mono' measurableSet_closedBall hpt
      _ = ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x) ∂μ +
          ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ :=
          lintegral_add_left ((measurable_const.indicator hMmeas).const_add _) _
      _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (M ∩ closedBall η (3 * s)) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_indicator_const hMmeas, Measure.restrict_apply hMmeas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          have hμM : μ (M ∩ closedBall η (3 * s)) ≤ μ (closedBall η (3 * s) \ F) :=
            (measure_mono inter_subset_left).trans hMmu.le
          exact add_le_add (add_le_add le_rfl (mul_le_mul_right hμM _)) le_rfl
  -- Step 8: absorption of the `λ²`-term
  exact hfinal ω s lam _ _ _ _ hω_pos hs hlam2 ha_lower ha_upper ha_I2 hI2

/-- **Measure of the bad set** (Simon Ch. 5, proof of Lemma 2.6, (2) and (6)).  If
`μ(B_t(y)) ≤ 2ωₙtⁿ` for `y ∈ B_{3σ₀/4}(ξ)`, `t ∈ (0, 5σ₀/4]`, and
`G' = {y ∈ spt μ : ∫_{B_{t/2}(y)} e⁺ dμ ≤ a tⁿ for all t ∈ (0, σ₀/2]}`, then
`μ(B_{3σ₀/4}(ξ) \ G') ≤ (2(5/2)ⁿ/a) ωₙ ∫_{B_{σ₀}(ξ)} e⁺ dμ`.

Since `μ(ℝ^{n+k} \ spt μ) = 0`, only `A' = (B_{3σ₀/4}(ξ) \ G') ∩ spt μ` counts.  Each `y ∈ A'` has
a bad radius `t_y ∈ (0, σ₀/2]` with `a t_yⁿ < ∫_{B_{t_y/2}(y)} e⁺ dμ` (Simon's (2)), so
`μ(A' ∩ B_{5t_y/2}(y)) ≤ 2ωₙ(5t_y/2)ⁿ ≤ (2(5/2)ⁿ/a) ωₙ (μ ⌞ e⁺)(B_{t_y/2}(y))`.  The five-times
covering bound `dorag_lip_vitali_two_measure_bound`, with radii `t_y/2 ≤ σ₀/4` and
`B_{t_y/2}(y) ⊆ B_{σ₀}(ξ)`, gives the claim. -/
theorem Submission.dorag_lip_bad_set_measure_bound : ∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (ξ : Euclid (n + k)) (σ₀ a : ℝ), 0 < σ₀ → 0 < a → (∀ y ∈ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 4 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → μ (closedBall ξ (3 * σ₀ / 4) \ {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)}) ≤ ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂μ := by
  intro n k μ e ξ σ₀ a hσ₀ ha hdens
  classical
  set Gs := {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
    ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)} with hGs
  set A' := (closedBall ξ (3 * σ₀ / 4) \ Gs) ∩ μ.support with hA'
  -- Step 1: the complement of `spt μ` is `μ`-null.
  have hsplit : μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := by
    calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ (A' ∪ μ.supportᶜ) := by
          apply measure_mono
          intro x hx
          by_cases h : x ∈ μ.support
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
      _ ≤ μ A' + μ μ.supportᶜ := measure_union_le _ _
      _ = μ A' := by rw [Measure.measure_compl_support, add_zero]
  -- Step 2: every point of `A'` has a bad radius `T y ∈ (0, σ₀/2]`.
  have hbad : ∀ y ∈ A', ∃ t : ℝ, 0 < t ∧ t ≤ σ₀ / 2 ∧
      ENNReal.ofReal (a * t ^ n) < ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ := by
    intro y hy
    have hyG : y ∉ Gs := hy.1.2
    simp only [hGs, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hyG
    obtain ⟨t, ht, ht', hlt⟩ := hyG hy.2
    exact ⟨t, ht, ht', hlt⟩
  choose! T hT0 hTσ hTlt using hbad
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n with hc
  -- Step 3: the five-times covering bound for `μ` and `ν = μ ⌞ e⁺` with radii `T y / 2`.
  have key := Submission.dorag_lip_vitali_two_measure_bound (n + k) μ
    (μ.withDensity (fun x => ENNReal.ofReal (e x))) A' (closedBall ξ σ₀)
    (fun y => T y / 2) (σ₀ / 4) c (by
    intro y hy
    have hT0y := hT0 y hy
    have hTσy := hTσ y hy
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · intro x hx
      rw [mem_closedBall] at hx ⊢
      have := dist_triangle x y ξ
      have hyξ := mem_closedBall.1 hy.1.1
      linarith
    · calc μ (A' ∩ closedBall y (5 * (T y / 2))) ≤ μ (closedBall y (5 * (T y / 2))) :=
            measure_mono inter_subset_right
        _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n) :=
            hdens y hy.1.1 _ (by linarith) (by linarith)
        _ = c * ENNReal.ofReal (a * T y ^ n) := by
            have hreal : 2 * (5 / 2) ^ n / a * (a * T y ^ n) = 2 * (5 * (T y / 2)) ^ n := by
              field_simp
              ring
            have h2 : ENNReal.ofReal (2 * (5 / 2) ^ n / a) * ENNReal.ofReal (a * T y ^ n) =
                2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n) := by
              rw [← ENNReal.ofReal_mul (by positivity), hreal, ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_ofNat]
            rw [hc]
            calc 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n)
                = unitBallVolume n * (2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n)) := by ring
              _ = unitBallVolume n * (ENNReal.ofReal (2 * (5 / 2) ^ n / a) *
                    ENNReal.ofReal (a * T y ^ n)) := by rw [h2]
              _ = ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n *
                    ENNReal.ofReal (a * T y ^ n) := by ring
        _ ≤ c * ∫⁻ x in closedBall y (T y / 2), ENNReal.ofReal (e x) ∂μ := by
            gcongr
            exact (hTlt y hy).le
        _ = c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall y (T y / 2)) := by
            rw [withDensity_apply _ measurableSet_closedBall])
  -- Step 4: `ν(B_{σ₀}(ξ)) = ∫_{B_{σ₀}(ξ)} e⁺ dμ`.
  calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := hsplit
    _ ≤ c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall ξ σ₀) := key
    _ = _ := by rw [withDensity_apply _ measurableSet_closedBall]

/-- **`Hⁿ`-measure of the graph off the support** (Simon Ch. 5, proof of Lemma 2.6, the estimate
after (10) via the covering (11), with the balls `B_{3s}(η)`).  Let `A ⊆ F`, let
`Hⁿ(F ∩ B_r(η)) ≤ K rⁿ` for `η ∈ A` and `r > 0`, and let every `η ∈ A` have a radius
`0 < s_η ≤ R₀` with `B_{3s_η}(η) ⊆ B` and `s_ηⁿ ≤ C₉ (μ(B_{3s_η}(η) ∖ F) + ∫_{B_{3s_η}(η)} e⁺ dμ)`.
The comparison measure `ν = μ⌞Fᶜ + μ.withDensity e⁺` has `ν(S) = μ(S ∖ F) + ∫_S e⁺ dμ` for
measurable `S`.  The growth bound at radius `15s_η = 5 · 3s_η` gives
`Hⁿ(A ∩ B_{5·3s_η}(η)) ≤ K 15ⁿ C₉ ν(B_{3s_η}(η))`, and the two-measure Vitali bound with the
radii `3s_η` gives `Hⁿ(A) ≤ K 15ⁿ C₉ ν(B)`. -/
theorem Submission.dorag_lip_graph_hole_measure_bound : ∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (F A B : Set (Euclid (n + k))) (K : ℝ≥0∞) (C₉ R₀ : ℝ), MeasurableSet B → A ⊆ F → (∀ η ∈ A, ∀ r : ℝ, 0 < r → μHE[n] (F ∩ closedBall η r) ≤ K * ENNReal.ofReal (r ^ n)) → (∀ η ∈ A, ∃ s : ℝ, 0 < s ∧ s ≤ R₀ ∧ closedBall η (3 * s) ⊆ B ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (e x) ∂μ)) → μHE[n] A ≤ K * ENNReal.ofReal (15 ^ n * C₉) * (μ (B \ F) + ∫⁻ x in B, ENNReal.ofReal (e x) ∂μ) := by
  intro n k μ e F A B K C₉ R₀ hB hAF hball hrad
  -- Step 1: the radii `r(η) = 3s_η`
  choose! s hs0 hsR hsB hsineq using hrad
  -- Step 2: the comparison measure `ν = μ⌞Fᶜ + μ.withDensity e⁺` (`F` need not be measurable)
  set ν : Measure (Euclid (n + k)) :=
    μ.restrict Fᶜ + μ.withDensity (fun x => ENNReal.ofReal (e x)) with hν
  have hνS : ∀ S : Set (Euclid (n + k)), MeasurableSet S →
      ν S = μ (S \ F) + ∫⁻ x in S, ENNReal.ofReal (e x) ∂μ := by
    intro S hS
    rw [hν, Measure.add_apply, Measure.restrict_apply hS, withDensity_apply _ hS, Set.sdiff_eq]
  -- Step 4: the two-measure Vitali bound gives `Hⁿ(A) ≤ K 15ⁿ C₉ ν(B)`
  rw [← hνS B hB]
  refine Submission.dorag_lip_vitali_two_measure_bound (n + k) μHE[n] ν A B (fun η => 3 * s η)
    (3 * R₀) (K * ENNReal.ofReal (15 ^ n * C₉)) fun η hη => ?_
  -- Step 3: its hypotheses at `η ∈ A`
  have hs0η := hs0 η hη
  refine ⟨by linarith, by linarith [hsR η hη], hsB η hη, ?_⟩
  calc μHE[n] (A ∩ closedBall η (5 * (3 * s η)))
      ≤ μHE[n] (F ∩ closedBall η (15 * s η)) :=
        measure_mono (Set.inter_subset_inter hAF (closedBall_subset_closedBall (by linarith)))
    _ ≤ K * ENNReal.ofReal ((15 * s η) ^ n) := hball η hη _ (by linarith)
    _ = K * ENNReal.ofReal (15 ^ n) * ENNReal.ofReal (s η ^ n) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ K * ENNReal.ofReal (15 ^ n) * (ENNReal.ofReal C₉ * (μ (closedBall η (3 * s η) \ F) +
          ∫⁻ x in closedBall η (3 * s η), ENNReal.ofReal (e x) ∂μ)) := by
        gcongr
        exact hsineq η hη
    _ = K * ENNReal.ofReal (15 ^ n * C₉) * ν (closedBall η (3 * s η)) := by
        rw [hνS _ measurableSet_closedBall, ENNReal.ofReal_mul (by positivity)]
        ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
