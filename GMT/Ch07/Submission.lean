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

/-- **The interior-product covector `ι_z(dy)` on `ℝ^{d+1}`** (used for the `d`-form `f · ι_z(dy)`,
whose exterior derivative is `(∂_z f) dy`, in White's projection argument for the closure theorem
behind Simon 7.2.4; cf. the forms `ωⱼ` in the proof of Simon 6.2.34).  For `z ∈ ℝ^{d+1}` there is
a continuous alternating `d`-form `ε` on `ℝ^{d+1}` with `ε(e₀, …, êᵢ, …, e_d) = (−1)ⁱ zᵢ`:
`ε(u₁, …, u_d) = det [z | u₁ | ⋯ | u_d] = δ(z, u₁, …, u_d)` for the standard determinant form `δ`. -/
theorem Submission.cbr_ci_pw_ipf_coord_covector : ∀ (d : ℕ) (z : Euclid (d + 1)), ∃ ε : Covector (Euclid (d + 1)) d, ∀ i : Fin (d + 1), ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ))) = (-1 : ℝ) ^ (i : ℕ) * z i := by
  intro d z
  classical
  -- The standard basis `b l = e_l` and its determinant `δ₀ c = det (c l r)_{r,l}`.
  let b : Module.Basis (Fin (d + 1)) ℝ (Euclid (d + 1)) :=
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
  have hdet : ∀ c : Fin (d + 1) → Euclid (d + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  -- `δ₀` is continuous (entrywise continuous matrix, then `det`), so it is a covector `δ`.
  have hcont : Continuous (fun c : Fin (d + 1) → Euclid (d + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (d + 1)) (d + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  -- `ε = δ.curryLeft z`, so `ε u = det M(u)` with columns `z, u₀, …, u_{d-1}`; expand along
  -- column `0`: `det M(u) = Σ_r (−1)ʳ z_r det N_r` with minors `N_r`.
  refine ⟨δ.curryLeft z, fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, hdet, Matrix.det_succ_column_zero,
    Finset.sum_eq_single i]
  · -- `r = i`: `(N_i)_{a,k} = (e_{i.succAbove k})_{i.succAbove a} = [a = k]`, so `N_i = 1`.
    have h1 : (Matrix.of fun r l => (Matrix.vecCons z (i.removeNth fun l =>
        EuclideanSpace.single l (1 : ℝ)) : Fin (d + 1) → Euclid (d + 1)) l r).submatrix
          i.succAbove Fin.succ = 1 := by
      ext a k
      simp [Matrix.one_apply, Fin.removeNth_apply]
    rw [h1, Matrix.det_one]
    simp
  · -- `r ≠ i`: row `a₀` of `N_r`, where `r.succAbove a₀ = i`, is `(e_{i.succAbove k})_i = 0`.
    intro r _ hri
    obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq (x := i) (y := r) (Ne.symm hri)
    rw [Matrix.det_eq_zero_of_row_eq_zero a₀, mul_zero]
    intro k
    simp [Fin.removeNth_apply, ha₀]
  · intro h
    exact absurd (Finset.mem_univ i) h
/-- **Coefficient norm of the interior-product covector** (used for `ε = ι_z(dy)` in the closure
and boundary-rectifiability step of the compactness theorem, Simon 7.2.4).  If the `d`-covector `ε`
on `ℝ^{d+1}` takes the value `(−1)ⁱ zᵢ` on `(e₀, …, êᵢ, …, e_d)`, then its Euclidean coefficient
norm (Simon (6.1.15)) is `|z|`: the strictly increasing `I : Fin d → Fin (d + 1)` are exactly the
maps `i.succAbove`, so the coefficients of `ε` are the `(−1)ⁱ zᵢ`. -/
theorem Submission.cbr_ci_pw_ipf_covector_norm_eq : ∀ (d : ℕ) (z : Euclid (d + 1)) (ε : Covector (Euclid (d + 1)) d), (∀ i : Fin (d + 1), ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ))) = (-1 : ℝ) ^ (i : ℕ) * z i) → covectorEuclideanNorm ε = ‖z‖ := by
  intro d z ε hε
  have hI : ∀ I : Fin d → Fin (d + 1), StrictMono I → ∃ i : Fin (d + 1), i.succAbove = I := by
    intro I hI
    have hns : ¬Surjective I := fun h => by
      simpa using Fintype.card_le_of_surjective I h
    obtain ⟨i, hi⟩ := not_forall.mp hns
    have hcard : (Finset.univ.erase i).card = d := by simp
    refine ⟨i, ?_⟩
    rw [Finset.orderEmbOfFin_unique hcard (f := I)
        (fun k => Finset.mem_erase.2 ⟨fun h => hi ⟨k, h⟩, Finset.mem_univ _⟩) hI,
      Finset.orderEmbOfFin_unique hcard (f := i.succAbove)
        (fun k => Finset.mem_erase.2 ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩)
        (Fin.strictMono_succAbove i)]
  rw [covectorEuclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  rw [← Finset.sum_subset
      (Finset.subset_univ (Finset.univ.image fun i : Fin (d + 1) => i.succAbove)) ?_,
    Finset.sum_image fun i _ j _ h => Fin.succAbove_left_injective h]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hb : (fun k => EuclideanSpace.basisFun (Fin (d + 1)) ℝ (i.succAbove k)) =
        i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ)) := by
      funext k
      simp [Fin.removeNth]
    rw [ite_eq_left (Fin.strictMono_succAbove i), hb, hε i, Real.norm_eq_abs, sq_abs, mul_pow,
      pow_right_comm, neg_one_sq, one_pow, one_mul]
  · intro I _ hIm
    refine ite_eq_right fun hmono => ?_
    obtain ⟨i, rfl⟩ := hI I hmono
    exact hIm (Finset.mem_image_of_mem _ (Finset.mem_univ i))
/-- **Exterior derivative of a function times a constant covector** (used for the boundary weak
derivatives in the graph-cycle regularity step of Simon 7.4.3).  If `a : ℝᴾ → ℝ` is
differentiable at `x` and `β` is a fixed `m`-covector, then
`d(a β)(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ Da(x)wᵢ · β(w₀, …, ŵᵢ, …, w_m)`, i.e. `d(a β) = da ∧ β`:
each term of the alternating sum differentiates `y ↦ a(y) β(w₀, …, ŵᵢ, …, w_m)`. -/
theorem Submission.dgcr_bwd_extDeriv_smul_const : ∀ (P m : ℕ) (a : Euclid P → ℝ) (β : Covector (Euclid P) m) (x : Euclid P) (w : Fin (m + 1) → Euclid P), DifferentiableAt ℝ a x → exteriorDerivative (fun y => a y • β) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ a x (w i) * β (i.removeNth w)) := by
  intro P m a β x w ha
  rw [exteriorDerivative_apply (ha.smul_const β) w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (fun y => (a y • β) (i.removeNth w)) = fun y => a y * β (i.removeNth w) := by
    funext y
    simp [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [h1, fderiv_mul_const ha]
  simp [zsmul_eq_mul, mul_comm]

/-- **The interior product `ι_z(dy)` as a constant `d`-form on `ℝ^{d+1}`** (the forms
`f · Σⱼ zⱼ εⱼ` in the BV estimate of the closure argument for Simon 7.2.4; cf. the forms `ωⱼ` in
the proof of Simon Ch. 6, 2.34).  For `z ∈ ℝ^{d+1}` the covector
`ε(u₁, …, u_d) = det[z | u₁ | ⋯ | u_d]` has `ε(e₀, …, êᵢ, …, e_d) = (−1)ⁱ zᵢ` and `|ε| = |z|`,
and `d(f ε) = df ∧ ε` gives
`d(f ε)(y)(e₀, …, e_d) = Σᵢ (−1)ⁱ Df(y)eᵢ · (−1)ⁱ zᵢ = Df(y)(Σᵢ zᵢ eᵢ) = Df(y) z`. -/
theorem Submission.cbr_ci_pw_interior_product_form : ∀ (d : ℕ) (z : Euclid (d + 1)), ∃ ε : Covector (Euclid (d + 1)) d, covectorEuclideanNorm ε ≤ ‖z‖ ∧ ∀ (f : Euclid (d + 1) → ℝ) (y : Euclid (d + 1)), DifferentiableAt ℝ f y → exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z := by
  intro d z
  -- steps 1–2: `ε = ι_z(dy)`, with `ε(i.removeNth e) = (−1)ⁱ zᵢ`
  obtain ⟨ε, hε⟩ := Submission.cbr_ci_pw_ipf_coord_covector d z
  -- step 3: `|ε| = ‖z‖`
  refine ⟨ε, (Submission.cbr_ci_pw_ipf_covector_norm_eq d z ε hε).le, fun f y hf => ?_⟩
  -- step 4: `d(f ε)(y)(e) = Σᵢ (−1)ⁱ Df(y)eᵢ · ε(i.removeNth e)`
  rw [Submission.dgcr_bwd_extDeriv_smul_const (d + 1) d f ε y _ hf]
  -- `(−1)ⁱ (−1)ⁱ = 1`, so the `i`-th term is `zᵢ Df(y)eᵢ`
  have hterm : ∀ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) * ε (i.removeNth (fun l : Fin (d + 1) => EuclideanSpace.single l (1 : ℝ)))) = z i * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have hsq : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hε i]
    linear_combination (z i * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) * hsq
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- `z = Σᵢ zᵢ eᵢ` and `Df(y)` is linear
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, smul_eq_mul]
/-- **Translated test functions** (mollified weights in the closure theorem behind Simon 7.2.4):
if `φ` is smooth with `tsupport φ ⊆ B_s(0)`, `s < R` and `x ∈ B̄_R(0)`, then `b(y) = φ(x − y)` is
smooth with compact support in `B_{2R}(0)` and `∫ b = ∫ φ`.  `tsupport φ` is closed in the compact
`B̄_s(0)`; `y ↦ x − y` is the homeomorphism `Homeomorph.subLeft x`, so `tsupport b` is the preimage
of `tsupport φ`, on which `‖y‖ ≤ ‖x‖ + ‖x − y‖ < R + s < 2R`; and Lebesgue measure is invariant
under `y ↦ x − y`. -/
theorem Submission.cbr_ci_pw_mu_translate_admissible : ∀ (n : ℕ) (R s : ℝ) (φ : Euclid n → ℝ) (x : Euclid n), s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → x ∈ closedBall 0 R → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (x - y)) ∧ HasCompactSupport (fun y => φ (x - y)) ∧ tsupport (fun y => φ (x - y)) ⊆ ball 0 (2 * R) ∧ ∫ y, φ (x - y) = ∫ y, φ y := by
  intro n R s φ x hsR hφ hsupp hx
  -- `φ` has compact support: `tsupport φ` is closed in the compact `closedBall 0 s`
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hsupp.trans ball_subset_closedBall)
  -- `b = φ ∘ e` for the homeomorphism `e = (x - ·)`
  have hb : (fun y => φ (x - y)) = φ ∘ Homeomorph.subLeft x := rfl
  refine ⟨hφ.comp (contDiff_const.sub contDiff_id), hb ▸ hφc.comp_homeomorph _, ?_,
    integral_sub_left_eq_self φ volume x⟩
  intro y hy
  have hxy : x - y ∈ tsupport φ := by
    rw [hb, tsupport_comp_eq_preimage] at hy
    exact hy
  have hxy' : ‖x - y‖ < s := mem_ball_zero_iff.mp (hsupp hxy)
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  rw [mem_ball_zero_iff]
  calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
    _ < 2 * R := by linarith
/-- **Mollification is Lipschitz, with constant `∝ ∫_S |v|`**: for `φ ∈ C^∞_c(ℝⁿ)` there is
`L ≥ 0` such that, for every `S ⊆ ℝⁿ`, every `v` integrable on `S` and all `x, x'`,
`|∫_S v(y)φ(x − y) dy − ∫_S v(y)φ(x' − y) dy| ≤ L (∫_S |v|) |x − x'|`.  `φ` is `C¹` with compact
support, hence `L`-Lipschitz, and bounded, so both integrands are integrable on `S` and the
difference is `|∫_S v(y)(φ(x − y) − φ(x' − y)) dy| ≤ ∫_S |v(y)| L |x − x'| dy`. -/
theorem Submission.cbr_ci_pw_mu_conv_lipschitz : ∀ (n : ℕ) (φ : Euclid n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Set (Euclid n)) (v : Euclid n → ℝ), IntegrableOn v S → ∀ x x' : Euclid n, |(∫ y in S, v y * φ (x - y)) - ∫ y in S, v y * φ (x' - y)| ≤ L * (∫ y in S, |v y|) * dist x x' := by
  intro n φ hφ hφc
  obtain ⟨C, hC⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  refine ⟨C, C.coe_nonneg, fun S v hv x x' => ?_⟩
  have hint : ∀ z : Euclid n, IntegrableOn (fun y => v y * φ (z - y)) S := fun z =>
    Integrable.mul_bdd hv
      (hφ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => hM (z - y))
  rw [← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y in S, v y * φ (x - y) - v y * φ (x' - y)‖
      ≤ ∫ y in S, |v y| * (C * dist x x') := by
        refine norm_integral_le_of_norm_le (hv.abs.mul_const _) (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        gcongr
        rw [← Real.dist_eq]
        simpa [dist_sub_right] using hC.dist_le_mul (x - y) (x' - y)
    _ = C * (∫ y in S, |v y|) * dist x x' := by
        rw [integral_mul_const]
        ring
/-- Pointwise convergence to a constant plus an eventual uniform Lipschitz bound on a compact set
gives uniform convergence (the ε/3 argument): cover `K` by finitely many `η`-balls centred in `K`,
with `max L 0 * η < ε / 3`; eventually every centre is `ε / 3`-close to `a`, and each `x ∈ K` lies
within `η` of a centre. -/
theorem Submission.cbr_ci_pw_mu_uniform_of_equilipschitz : ∀ (n : ℕ) (K : Set (Euclid n)) (F : ℕ → Euclid n → ℝ) (a L : ℝ), IsCompact K → (∀ x ∈ K, Tendsto (fun k => F k x) atTop (𝓝 a)) → (∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K, |F k x - F k x'| ≤ L * dist x x') → TendstoUniformlyOn F (fun _ => a) atTop K := by
  intro n K F a L hK hpt hL
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hM0 : 0 ≤ max L 0 := le_max_right L 0
  have hη : 0 < ε / (3 * (max L 0 + 1)) := by positivity
  have hMη : max L 0 * (ε / (3 * (max L 0 + 1))) < ε / 3 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨t, htK, ht, hcover⟩ := hK.finite_cover_balls hη
  have hnet : ∀ᶠ k in atTop, ∀ z ∈ t, |F k z - a| < ε / 3 :=
    ht.eventually_all.2 fun z hz => by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.1 (hpt z (htK hz)) (ε / 3) (by positivity)
  filter_upwards [hnet, hL] with k hk hkL x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover hx)
  have hzx : |F k z - F k x| < ε / 3 :=
    calc |F k z - F k x| ≤ L * dist z x := hkL z (htK hz) x hx
      _ ≤ max L 0 * dist z x := mul_le_mul_of_nonneg_right (le_max_left L 0) dist_nonneg
      _ ≤ max L 0 * (ε / (3 * (max L 0 + 1))) :=
        mul_le_mul_of_nonneg_left (mem_ball'.1 hxz).le hM0
      _ < ε / 3 := hMη
  rw [Real.dist_eq]
  have htri := abs_sub_le a (F k z) (F k x)
  rw [abs_sub_comm a (F k z)] at htri
  linarith [hk z hz]

/-- **Simon 7.2.4**, uniform convergence of mollified weak limits (step 11(a) of the weight
lower bound `α ≥ 1`): if the `u_k` are eventually `L¹`-bounded by `Λ` on `B_{2R}(0)` and
`∫_{B_{2R}(0)} u_k b → c ∫ b` for every test function `b` with `spt b ⊆ B_{2R}(0)`, then for a test
function `φ` with `spt φ ⊆ B_s(0)`, `s < R`, the mollifications
`w_k(x) = ∫_{B_{2R}(0)} u_k(y) φ(x − y) dy` converge to `c ∫ φ` uniformly on `B̄_R(0)`.  For
`x ∈ B̄_R(0)` the translate `φ(x − ·)` is such a test function with the same integral
(`cbr_ci_pw_mu_translate_admissible`), so `w_k(x) → c ∫ φ`; the `w_k` are eventually
`LΛ`-Lipschitz (`cbr_ci_pw_mu_conv_lipschitz`); and pointwise convergence with an eventual
uniform Lipschitz bound on the compact `B̄_R(0)` is uniform
(`cbr_ci_pw_mu_uniform_of_equilipschitz`). -/
theorem Submission.cbr_ci_pw_mollified_tendstoUniformlyOn : ∀ (n : ℕ) (R s c Λ : ℝ) (φ : Euclid n → ℝ) (u : ℕ → Euclid n → ℝ), 0 < R → 0 < s → s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ ball 0 (2 * R) → Tendsto (fun k => ∫ y in ball 0 (2 * R), u k y * b y) atTop (𝓝 (c * ∫ y, b y))) → TendstoUniformlyOn (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (fun _ => c * ∫ y, φ y) atTop (closedBall 0 R) := by
  intro n R s c Λ φ u _ _ hsR hφ hφs hu hΛ hconv
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  obtain ⟨L, hL, hLip⟩ := Submission.cbr_ci_pw_mu_conv_lipschitz n φ hφ hφc
  refine Submission.cbr_ci_pw_mu_uniform_of_equilipschitz n (closedBall 0 R)
    (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (c * ∫ y, φ y) (L * Λ)
    (isCompact_closedBall 0 R) (fun x hx => ?_) ?_
  · obtain ⟨hb, hbc, hbs, hbi⟩ :=
      Submission.cbr_ci_pw_mu_translate_admissible n R s φ x hsR hφ hφs hx
    have h := hconv (fun y => φ (x - y)) hb hbc hbs
    rwa [hbi] at h
  · filter_upwards [hΛ] with k hk x _ x' _
    exact (hLip (ball 0 (2 * R)) (u k) (hu k) x x').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hL) dist_nonneg)
/-- **Translation bound for smooth tests** (steps 1(b)–(d) of the BV estimate): let `u` be
integrable on `B = B_ρ(0) ⊆ ℝⁿ` with `|∫_B u(y) Df(y)(z) dy| ≤ V ‖z‖ K` for every smooth compactly
supported `f` with `tsupport f ⊆ B` and `|f| ≤ K`.  If `g` is smooth with compact support,
`tsupport g ⊆ B_{ρ−‖v‖}(0)` and `|g| ≤ M`, then `|∫_B u(y) (g(y + v) − g(y)) dy| ≤ V ‖v‖ M`.  By
the fundamental theorem of calculus along `τ ↦ y + τv` and Fubini on `(0, 1] × B` (dominated by
`K_D ‖v‖ |u|`, where `‖Dg‖ ≤ K_D`), the left side is `∫₀¹ ∫_B u(y) Dg(y + τv)(v) dy dτ`; for
`τ ∈ (0, 1]` the inner integral is bounded by the hypothesis applied to the translate `g(· + τv)`,
whose support stays in `B`. -/
theorem Submission.cbr_ci_pw_bv_translate_test : ∀ (n : ℕ) (ρ V M : ℝ) (u g : Euclid n → ℝ) (v : Euclid n), IntegrableOn u (ball 0 ρ) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (K : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 ρ → (∀ y, |f y| ≤ K) → |∫ y in ball 0 ρ, u y * fderiv ℝ f y z| ≤ V * ‖z‖ * K) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (ρ - ‖v‖) → (∀ y, |g y| ≤ M) → |∫ y in ball 0 ρ, u y * (g (y + v) - g y)| ≤ V * ‖v‖ * M := by
  intro n ρ V M u g v hu hvar hg hgc hgs hgb
  -- Step 1: `Dg` is continuous with compact support, hence bounded by some `K_D`
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hDcs : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  obtain ⟨KD, hKD⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 2: FTC along the segment `τ ↦ y + τv`
  have hFTC : ∀ y, g (y + v) - g y = ∫ τ in (0:ℝ)..1, fderiv ℝ g (y + τ • v) v := by
    intro y
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1,
        HasDerivAt (fun τ : ℝ => g (y + τ • v)) (fderiv ℝ g (y + τ • v) v) τ := by
      intro τ _
      have h1 : HasDerivAt (fun τ : ℝ => y + τ • v) v τ := by
        simpa using ((hasDerivAt_id τ).smul_const v).const_add y
      exact (hgd (y + τ • v)).hasFDerivAt.comp_hasDerivAt τ h1
    have hint : IntervalIntegrable (fun τ : ℝ => fderiv ℝ g (y + τ • v) v) volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact (hDc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  -- Step 3: `Φ(τ, y) = u(y) Dg(y + τv)(v)` is integrable on `(0, 1] × B`, dominated by
  -- `K_D ‖v‖ |u(y)|`
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hInt : Integrable (uncurry fun (τ : ℝ) (y : Euclid n) => u y * fderiv ℝ g (y + τ • v) v)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (ball (0 : Euclid n) ρ))) := by
    have hdom : Integrable (fun p : ℝ × Euclid n => (KD * ‖v‖) * ‖u p.2‖)
        ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (ball (0 : Euclid n) ρ))) :=
      (hu.norm.const_mul (KD * ‖v‖)).comp_snd _
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hu.aestronglyMeasurable.comp_snd).mul
        ((hDc.comp (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
          continuous_const).aestronglyMeasurable
    · simp only [uncurry, norm_mul]
      have h1 : ‖fderiv ℝ g (p.2 + p.1 • v) v‖ ≤ KD * ‖v‖ :=
        ((fderiv ℝ g (p.2 + p.1 • v)).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hKD _) (norm_nonneg v))
      calc ‖u p.2‖ * ‖fderiv ℝ g (p.2 + p.1 • v) v‖ ≤ ‖u p.2‖ * (KD * ‖v‖) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = KD * ‖v‖ * ‖u p.2‖ := by ring
  -- Step 4: Fubini, `∫_B u (g(· + v) − g) = ∫₀¹ X(τ) dτ` with `X(τ) = ∫_B u(y) Dg(y + τv)(v) dy`
  have hLHS : ∫ y in ball (0 : Euclid n) ρ, u y * (g (y + v) - g y)
      = ∫ τ in (0:ℝ)..1, ∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v := by
    simp_rw [hFTC, ← intervalIntegral.integral_const_mul]
    exact (intervalIntegral_integral_swap hInt).symm
  -- Step 5: `|X(τ)| ≤ V ‖v‖ M` for `τ ∈ (0, 1]`, by the hypothesis for `f_τ = g(· + τv)`
  have hX : ∀ τ ∈ Set.uIoc (0:ℝ) 1,
      ‖∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v‖ ≤ V * ‖v‖ * M := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    set f : Euclid n → ℝ := fun y => g (y + τ • v) with hf
    have hfs : ContDiff ℝ (⊤ : ℕ∞) f := hg.comp (contDiff_id.add contDiff_const)
    have hfc : HasCompactSupport f := hgc.comp_homeomorph (Homeomorph.addRight (τ • v))
    have hft : tsupport f ⊆ ball 0 ρ := by
      intro y hy
      have : f = g ∘ (Homeomorph.addRight (τ • v)) := rfl
      rw [this, tsupport_comp_eq_preimage] at hy
      have hy' := mem_ball_zero_iff.1 (hgs hy)
      simp only [Homeomorph.coe_addRight] at hy'
      rw [mem_ball_zero_iff]
      have h1 : ‖y‖ ≤ ‖y + τ • v‖ + ‖τ • v‖ := by
        calc ‖y‖ = ‖(y + τ • v) - τ • v‖ := by simp
          _ ≤ ‖y + τ • v‖ + ‖τ • v‖ := norm_sub_le _ _
      have h2 : ‖τ • v‖ ≤ ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
      linarith
    have hfb : ∀ y, |f y| ≤ M := fun y => hgb _
    have := hvar f v M hfs hfc hft hfb
    rw [Real.norm_eq_abs]
    simpa [hf, fderiv_comp_add_right] using this
  -- Step 6: integrate the bound of step 5 over `(0, 1]`
  rw [hLHS, ← Real.norm_eq_abs]
  calc ‖∫ τ in (0:ℝ)..1, ∫ y in ball (0 : Euclid n) ρ, u y * fderiv ℝ g (y + τ • v) v‖
      ≤ V * ‖v‖ * M * |1 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hX
    _ = V * ‖v‖ * M := by simp
/-- **Pairing identity** (steps 1(a) and 1(c) of the BV estimate): let `S ⊆ ℝⁿ` be measurable,
`u` integrable on `S`, `φ` continuous with compact support and `∫ φ = 1`, and `g` continuous with
compact support and `g = 0` off `S`.  Then, with `w(x) = ∫_S u(y) φ(x − y) dy`,
`∫ (u − w) g = ∫ φ(z) ∫_S u(y) (g(y) − g(y + z)) dy dz`.  With `ū = 1_S u`, two applications of
Fubini (dominated by multiples of `|g(x)| |ū(y)|` and `|φ(z)| |ū(y)|`), translation invariance and
`∫ φ = 1` reduce both sides to `∫ ū g − ∫ ū(y) ∫ φ(z) g(z + y) dz dy`. -/
theorem Submission.cbr_ci_pw_bv_pairing_identity : ∀ (n : ℕ) (S : Set (Euclid n)) (φ u g : Euclid n → ℝ), MeasurableSet S → Continuous φ → HasCompactSupport φ → ∫ y, φ y = 1 → IntegrableOn u S → Continuous g → HasCompactSupport g → (∀ x, x ∉ S → g x = 0) → ∫ x, (u x - ∫ y in S, u y * φ (x - y)) * g x = ∫ z, φ z * ∫ y in S, u y * (g y - g (y + z)) := by
  intro n S φ u g hS hφ hφc hφ1 hu hg hgc hgS
  -- Step 1: `ū = 1_S u` is integrable; `φ` and `g` are integrable and bounded
  set ub : Euclid n → ℝ := S.indicator u with hub
  have hubi : Integrable ub := (integrable_indicator_iff hS).2 hu
  obtain ⟨Kφ, hKφ⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨Kg, hKg⟩ := hg.bounded_above_of_compact_support hgc
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  -- Step 2: integrals over `S` become integrals of `ū`, and `(u − w) g = ū g − w g`
  have hw : ∀ x, ∫ y in S, u y * φ (x - y) = ∫ y, ub y * φ (x - y) := by
    intro x
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hI : ∀ z, ∫ y in S, u y * (g y - g (y + z)) = ∫ y, ub y * (g y - g (y + z)) := by
    intro z
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hL : ∀ x, (u x - ∫ y in S, u y * φ (x - y)) * g x
      = ub x * g x - (∫ y, ub y * φ (x - y)) * g x := by
    intro x
    rw [hw x, sub_mul]
    congr 1
    by_cases hx : x ∈ S
    · simp [hub, Set.indicator_of_mem hx]
    · simp [hgS x hx]
  simp_rw [hL, hI]
  have hubg : Integrable (fun x => ub x * g x) :=
    hubi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hKg)
  -- Step 3: first Fubini, for `F(x, y) = ū(y) φ(x − y) g(x)`
  have hFi : Integrable (uncurry fun x y => ub y * φ (x - y) * g x) (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => Kφ * (‖g p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hgi.norm.mul_prod hubi.norm).const_mul Kφ
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hubi.aestronglyMeasurable.comp_snd).mul
        ((hφ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)).mul
        ((hg.comp continuous_fst).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 := hKφ (p.1 - p.2)
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (g p.1)
      calc ‖ub p.2‖ * ‖φ (p.1 - p.2)‖ * ‖g p.1‖ = ‖φ (p.1 - p.2)‖ * (‖g p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ Kφ * (‖g p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  -- translation invariance of Lebesgue measure: `∫ φ(x − y) g(x) dx = ∫ φ(z) g(z + y) dz`
  have htr : ∀ y, ∫ x, φ (x - y) * g x = ∫ z, φ z * g (z + y) := fun y => by
    simpa [sub_add_cancel] using integral_sub_right_eq_self
      (μ := (volume : Measure (Euclid n))) (fun z => φ z * g (z + y)) y
  have hwg : ∀ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * φ (x - y) * g x := fun x =>
    (integral_mul_const _ _).symm
  have hwgi : Integrable (fun x => (∫ y, ub y * φ (x - y)) * g x) := by
    simp_rw [hwg]; exact hFi.integral_prod_left
  have key1 : ∫ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * ∫ z, φ z * g (z + y) := by
    simp_rw [hwg]
    rw [integral_integral_swap hFi]
    congr 1; funext y
    simp_rw [mul_assoc]
    rw [integral_const_mul, htr]
  have hconv : Integrable (fun y => ub y * ∫ z, φ z * g (z + y)) := by
    refine (hFi.integral_prod_right).congr (Eventually.of_forall fun y => ?_)
    simp only [uncurry]
    simp_rw [mul_assoc]
    rw [integral_const_mul, htr]
  -- Step 4: `∫ φ(z) (g(y) − g(y + z)) dz = g(y) − ∫ φ(z) g(z + y) dz`, by `∫ φ = 1`
  have hinner : ∀ y, ∫ z, φ z * (g y - g (y + z)) = g y - ∫ z, φ z * g (z + y) := by
    intro y
    have hc : Integrable (fun z => φ z * g y) := hφi.mul_const _
    have hs : Integrable (fun z => φ z * g (z + y)) :=
      hφi.mul_bdd (hg.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun z => hKg _)
    simp_rw [mul_sub]
    rw [integral_sub hc (by simpa [add_comm] using hs), integral_mul_const, hφ1, one_mul]
    simp_rw [add_comm y]
  -- Step 5: second Fubini, for `H(z, y) = φ(z) ū(y) (g(y) − g(y + z))`
  have hHi : Integrable (uncurry fun z y => φ z * (ub y * (g y - g (y + z))))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hφi.norm.mul_prod hubi.norm).const_mul (2 * Kg)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hφ.comp continuous_fst).aestronglyMeasurable.mul
        ((hubi.aestronglyMeasurable.comp_snd).mul
          ((hg.comp continuous_snd).sub
            (hg.comp (continuous_snd.add continuous_fst))).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 : ‖g p.2 - g (p.2 + p.1)‖ ≤ 2 * Kg := by
        calc ‖g p.2 - g (p.2 + p.1)‖ ≤ ‖g p.2‖ + ‖g (p.2 + p.1)‖ := norm_sub_le _ _
          _ ≤ Kg + Kg := add_le_add (hKg _) (hKg _)
          _ = 2 * Kg := by ring
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (φ p.1)
      calc ‖φ p.1‖ * (‖ub p.2‖ * ‖g p.2 - g (p.2 + p.1)‖)
          = ‖g p.2 - g (p.2 + p.1)‖ * (‖φ p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  have key2 : ∫ z, φ z * ∫ y, ub y * (g y - g (y + z))
      = ∫ y, ub y * (g y - ∫ z, φ z * g (z + y)) := by
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hHi]
    congr 1; funext y
    have : ∀ z, φ z * (ub y * (g y - g (y + z))) = ub y * (φ z * (g y - g (y + z))) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, hinner y]
  -- Step 6: both sides equal `∫ ū g − ∫ ū(y) ∫ φ(z) g(z + y) dz dy`
  rw [integral_sub hubg hwgi, key1, key2]
  simp_rw [mul_sub]
  rw [integral_sub hubg hconv]

/-- **Pairing of `u − u ∗ φ` with a test function, for `u` of bounded variation** (Claim A of the
`BV` mollifier estimate; mollification of `BV` functions as in Simon, Ch. 2, §2).  Let `φ ≥ 0` be
smooth with `tsupport φ ⊆ B_s(0)` and `∫ φ = 1`, let `u` be integrable on `B_{2R}(0)` with
`|∫_{B_{2R}(0)} u(y) Df(y)(z) dy| ≤ V‖z‖M` for all smooth `f` with compact support in `B_{2R}(0)`
and `|f| ≤ M`, and let `2s < R`.  If `g` is smooth with compact support in `B_{R+s}(0)` and
`|g| ≤ 1`, then `|∫ (u − w) g| ≤ sV`, where `w(x) = ∫_{B_{2R}(0)} u(y) φ(x − y) dy`.  By Fubini,
`∫ (u − w) g = ∫ φ(z) I(z) dz` with `I(z) = ∫_{B_{2R}(0)} u(y) (g(y) − g(y + z)) dy`; if
`φ(z) ≠ 0` then `‖z‖ < s < R − s`, so `g` and its translate by `z` are supported in `B_{2R}(0)` and
the translation estimate gives `|I(z)| ≤ V‖z‖ ≤ sV`; integrate against `φ`. -/
theorem Submission.cbr_ci_pw_bv_smooth_test_bound : ∀ (n : ℕ) (R s V : ℝ) (φ u g : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + s) → (∀ x, |g x| ≤ 1) → |∫ x, (u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) * g x| ≤ s * V := by
  intro n R s V φ u g _hR hs h2s hV hφ hφ0 hφs hφ1 hu hvar hg hgc hgs hgb
  -- `φ` has compact support, and `g` vanishes off `B_{2R}(0)` since `R + s ≤ 2R`
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  have hgS : ∀ x, x ∉ ball (0 : Euclid n) (2 * R) → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (ball_subset_ball (by linarith) (hgs hx'))
  -- Fubini: `∫ (u - w) g = ∫ φ(z) ∫_{B_{2R}(0)} u(y) (g(y) - g(y + z)) dy dz`
  rw [Submission.cbr_ci_pw_bv_pairing_identity n (ball 0 (2 * R)) φ u g measurableSet_ball
    hφ.continuous hφc hφ1 hu hg.continuous hgc hgS]
  -- `|φ(z) I(z)| ≤ φ(z) sV`: trivial if `φ(z) = 0`, else `‖z‖ < s` and translate by `z`
  have hbound : ∀ z, ‖φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ ≤
      φ z * (s * V) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    have hzs : ‖z‖ < s := mem_ball_zero_iff.1 (hφs (subset_tsupport φ hz))
    have hT := Submission.cbr_ci_pw_bv_translate_test n (2 * R) V 1 u g z hu hvar hg hgc
      (hgs.trans (ball_subset_ball (by linarith))) hgb
    have hneg : ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z)) =
        -∫ y in ball (0 : Euclid n) (2 * R), u y * (g (y + z) - g y) := by
      rw [← integral_neg]; congr 1; funext y; ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφ0 z), hneg, abs_neg]
    refine mul_le_mul_of_nonneg_left (hT.trans ?_) (hφ0 z)
    linarith [mul_le_mul_of_nonneg_left hzs.le hV]
  -- integrate against `φ`, using `∫ φ = 1`
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  calc |∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))|
      = ‖∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, φ z * (s * V) :=
        norm_integral_le_of_norm_le (hφi.mul_const _) (Eventually.of_forall hbound)
    _ = s * V := by rw [integral_mul_const, hφ1, one_mul]
/-- **Smooth a.e. approximation of a bounded function supported in a ball** (mollification; cf.
Evans, *PDE*, App. C, Thm. 7).  If `g₀ : ℝⁿ → ℝ` is measurable, `|g₀| ≤ 1` and `g₀ = 0` off
`B_R(0)`, let `ρ = b / ∫ b` for the `ContDiffBump` `b` with radii `1/4, 1/2`,
`ψ_ε(x) = ε⁻ⁿ ρ(ε⁻¹ x)` and `θ_j = δ / (j + 2)`.  Then `G_j = g₀ ⋆ ψ_{θ_j}` is `C^∞`, vanishes
off `B̄_{R + θ_j/2}(0) ⊆ B_{R+δ}(0)`, satisfies `|G_j| ≤ ∫ ψ_{θ_j} = 1`, and `G_j(x) → g₀(x)` at
every Lebesgue point `x` of `g₀` (approximate identity with `|ψ_{θ_j}| ≤ C / Lⁿ(B_{θ_j}(x))`),
hence for `Lⁿ`-a.e. `x`. -/
theorem Submission.cbr_ci_pw_bv_smooth_ae_approx : ∀ (n : ℕ) (R δ : ℝ) (g₀ : Euclid n → ℝ), 0 < δ → Measurable g₀ → (∀ x, |g₀ x| ≤ 1) → (∀ x, R ≤ ‖x‖ → g₀ x = 0) → ∃ G : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧ (∀ j, tsupport (G j) ⊆ ball 0 (R + δ)) ∧ (∀ j x, |G j x| ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun j => G j x) atTop (𝓝 (g₀ x)) := by
  intro n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 0: g₀ is integrable
  have hg₀out : ∀ x, x ∉ ball (0 : Euclid n) R → g₀ x = 0 := fun x hx =>
    hg₀z x (by simpa [mem_ball_zero_iff] using hx)
  have hg₀i : Integrable g₀ := by
    have hon : IntegrableOn g₀ (ball (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne hg₀m.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg₀b x)
    exact (integrableOn_iff_integrable_of_support_subset
      (fun x hx => by by_contra h; exact hx (hg₀out x h))).1 hon
  -- Step 1: a normalized bump
  let b : ContDiffBump (0 : Euclid n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbi : Integrable (b : Euclid n → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  set I : ℝ := ∫ x, b x with hIdef
  have hI : 0 < I := by
    rw [hIdef, integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbi, b.support_eq]
    exact measure_ball_pos _ _ (by norm_num)
  set ρ : Euclid n → ℝ := fun x => b x / I with hρdef
  have hρc : ContDiff ℝ (⊤ : ℕ∞) ρ := b.contDiff.div_const I
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => div_nonneg b.nonneg hI.le
  have hρb : ∀ x, ρ x ≤ 1 / I := fun x => div_le_div_of_nonneg_right b.le_one hI.le
  have hρz : ∀ x, (1 / 2 : ℝ) ≤ ‖x‖ → ρ x = 0 := by
    intro x hx
    have : x ∉ support (b : Euclid n → ℝ) := by
      rw [b.support_eq, mem_ball_zero_iff]; exact not_lt.2 hx
    simp [hρdef, notMem_support.1 this]
  have hρ1 : ∫ x, ρ x = 1 := by
    simp only [hρdef]; rw [integral_div, ← hIdef, div_self hI.ne']
  -- Step 2: rescaled mollifiers
  set ψ : ℝ → Euclid n → ℝ := fun ε x => (ε ^ n)⁻¹ * ρ (ε⁻¹ • x) with hψdef
  have hψc : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (ψ ε) := fun ε =>
    contDiff_const.mul (hρc.comp (contDiff_const_smul ε⁻¹))
  have hψ0 : ∀ ε, 0 < ε → ∀ x, 0 ≤ ψ ε x := fun ε hε x =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le n)) (hρ0 _)
  have hψz : ∀ ε, 0 < ε → ∀ x, ε / 2 ≤ ‖x‖ → ψ ε x = 0 := by
    intro ε hε x hx
    have : (1 / 2 : ℝ) ≤ ‖ε⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      rw [le_inv_mul_iff₀ hε]; linarith
    simp [hψdef, hρz _ this]
  have hψb : ∀ ε, 0 < ε → ∀ x, |ψ ε x| ≤ (1 / I) / ε ^ n := by
    intro ε hε x
    rw [abs_of_nonneg (hψ0 ε hε x), hψdef]
    simp only
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hρb _) (inv_nonneg.2 (pow_nonneg hε.le n))
  have hψ1 : ∀ ε, 0 < ε → ∫ x, ψ ε x = 1 := by
    intro ε hε
    simp only [hψdef]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg _ _ hε.le,
      finrank_euclideanSpace_fin, hρ1, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero n hε.ne')]
  have hψcs : ∀ ε, 0 < ε → HasCompactSupport (ψ ε) := by
    intro ε hε
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hψz ε hε x (by linarith)
  -- Step 3: the sequence
  set θ : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hθdef
  have hθpos : ∀ j, 0 < θ j := fun j => div_pos hδ (by positivity)
  have hθlt : ∀ j, θ j < δ := fun j => by
    rw [hθdef]; simp only
    rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hG : ∀ j x, convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = ∫ y, g₀ y * ψ (θ j) (x - y) := by
    intro j x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvan : ∀ j x, R + θ j / 2 ≤ ‖x‖ →
      convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro j x hx
    rw [hG]
    have : (fun y => g₀ y * ψ (θ j) (x - y)) = fun _ => 0 := by
      funext y
      by_cases hy : R ≤ ‖y‖
      · rw [hg₀z y hy, zero_mul]
      · push Not at hy
        have h1 : θ j / 2 ≤ ‖x - y‖ := by
          have := norm_sub_norm_le x y
          linarith
        rw [hψz (θ j) (hθpos j) _ h1, mul_zero]
    rw [this, integral_zero]
  have hsupp : ∀ j, support (convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ closedBall 0 (R + θ j / 2) := by
    intro j x hx
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hx (hvan j x (not_le.1 h).le)
  refine ⟨fun j => convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hψcs (θ j) (hθpos j)).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hg₀i.locallyIntegrable (hψc (θ j))
  · intro j
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp j)
  · intro j
    refine (closure_minimal (hsupp j) isClosed_closedBall).trans (closedBall_subset_ball ?_)
    linarith [hθlt j, hθpos j]
  · intro j x
    simp only
    rw [hG]
    have hψi : Integrable (ψ (θ j)) :=
      (hψc (θ j)).continuous.integrable_of_hasCompactSupport (hψcs (θ j) (hθpos j))
    calc |∫ y, g₀ y * ψ (θ j) (x - y)| ≤ ∫ y, |g₀ y * ψ (θ j) (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, ψ (θ j) (x - y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hψi.comp_sub_left x) (Eventually.of_forall fun y => ?_)
          show |g₀ y * ψ (θ j) (x - y)| ≤ ψ (θ j) (x - y)
          rw [abs_mul, abs_of_nonneg (hψ0 _ (hθpos j) _)]
          exact mul_le_of_le_one_left (hψ0 _ (hθpos j) _) (hg₀b y)
      _ = 1 := by rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)]
  · have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) hg₀i.locallyIntegrable 1
    filter_upwards [hleb] with x hx
    have hθ0 : Tendsto θ atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [hθdef] using this.const_div_atTop δ
    have hθ : Tendsto θ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hθ0
        (Eventually.of_forall fun j => hθpos j)
    have havg := hx (fun _ => x) θ hθ
      (Eventually.of_forall fun j => mem_closedBall_self (by simpa using (hθpos j).le))
    have hB1 : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
    have key := tendsto_integral_smul_of_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) (f := g₀) (c := g₀ x)
      (a := fun j => closedBall x (θ j)) (g := fun j y => ψ (θ j) (x - y))
      ((1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1)) havg
      (Eventually.of_forall fun j => hg₀i.integrableOn)
      (by
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
        simp only
        rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)])
      (Eventually.of_forall fun j y hy => by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        by_contra h
        exact hy (hψz _ (hθpos j) _ (by linarith [hθpos j])))
      (Eventually.of_forall fun j y => by
        rw [Measure.addHaar_real_closedBall' _ _ (hθpos j).le, finrank_euclideanSpace_fin]
        have hpow : 0 < θ j ^ n := pow_pos (hθpos j) n
        calc |ψ (θ j) (x - y)| ≤ (1 / I) / θ j ^ n := hψb _ (hθpos j) _
          _ = (1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1) /
              (θ j ^ n * (volume : Measure (Euclid n)).real (closedBall 0 1)) := by
            field_simp)
    refine key.congr' (Eventually.of_forall fun j => ?_)
    simp only
    rw [hG]
    congr 1; funext y
    rw [smul_eq_mul, mul_comm]

/-- **The `L¹` norm on a ball by duality with smooth test functions** (steps 2 and 4 of the BV
estimate `∫_{B_R} |u − u ∗ φ_s| ≤ s V` in the cycle part of the proof of Simon 7.2.4): if `h` is
integrable on `B_{R+δ}(0)`, `δ > 0`, and `∫ h g ≤ C` for every smooth `g` with compact support in
`B_{R+δ}(0)` and `|g| ≤ 1`, then `∫_{B_R(0)} |h| ≤ C`.  With a Borel representative `h̃` of `h`
on `B_{R+δ}(0)` and `g₀ = 1_{B_R(0)} sgn h̃`, the admissible smooth tests `G_j → g₀` a.e. of
`smooth_ae_approx` give `∫ h G_j ≤ C`, and dominated convergence (dominant `|h|`) gives
`∫ h G_j → ∫_{B_{R+δ}(0)} h g₀ = ∫_{B_R(0)} |h|`. -/
theorem Submission.cbr_ci_pw_bv_l1_duality : ∀ (n : ℕ) (R δ C : ℝ) (h : Euclid n → ℝ), 0 < δ → IntegrableOn h (ball 0 (R + δ)) → (∀ g : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + δ) → (∀ x, |g x| ≤ 1) → ∫ x, h x * g x ≤ C) → ∫ x in ball 0 R, |h x| ≤ C := by
  intro n R δ C h hδ hh htest
  set B : Set (Euclid n) := ball 0 (R + δ) with hB
  -- Step 1: a Borel representative `h̃ = hm` of `h` on `B`
  set hm : Euclid n → ℝ := hh.aestronglyMeasurable.mk h with hhm
  have hhm_meas : Measurable hm := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : h =ᵐ[volume.restrict B] hm := hh.aestronglyMeasurable.ae_eq_mk
  -- Step 2: the sign function `g₀ = 1_{B_R(0)} sgn h̃`: Borel, `|g₀| ≤ 1`, `g₀ = 0` off `B_R(0)`
  set g₀ : Euclid n → ℝ :=
    (ball (0 : Euclid n) R).indicator (fun x => if 0 ≤ hm x then 1 else -1) with hg₀
  have hg₀m : Measurable g₀ :=
    (Measurable.ite (measurableSet_le measurable_const hhm_meas) measurable_const
      measurable_const).indicator measurableSet_ball
  have hg₀b : ∀ x, |g₀ x| ≤ 1 := by
    intro x
    simp only [hg₀, Set.indicator]
    split_ifs <;> norm_num
  have hg₀z : ∀ x, R ≤ ‖x‖ → g₀ x = 0 := by
    intro x hx
    simp only [hg₀]
    exact Set.indicator_of_notMem (by simpa [mem_ball_zero_iff] using hx) _
  -- Step 3: smooth admissible tests `G_j → g₀` a.e.
  obtain ⟨G, hGs, hGc, hGt, hGb, hGl⟩ :=
    Submission.cbr_ci_pw_bv_smooth_ae_approx n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 4: `∫_B h G_j = ∫ h G_j ≤ C`, as `G_j` vanishes off `B`
  have hle : ∀ j, ∫ x in B, h x * G j x ≤ C := by
    intro j
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hGt j hx')), mul_zero])]
    exact htest (G j) (hGs j) (hGc j) (hGt j) (hGb j)
  -- Step 5: dominated convergence on `B`, with dominant `|h|`
  have hlim : Tendsto (fun j => ∫ x in B, h x * G j x) atTop (𝓝 (∫ x in B, h x * g₀ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun j => ?_) hh.norm
      (fun j => ?_) ?_
    · exact hh.aestronglyMeasurable.mul (hGs j).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hGb j x)
    · exact (ae_restrict_of_ae hGl).mono fun x hx => tendsto_const_nhds.mul hx
  -- Step 6: `h g₀ = 1_{B_R(0)} |h|` a.e. on `B`, so `∫_B h g₀ = ∫_{B_R(0)} |h|`
  have heq : ∫ x in B, h x * g₀ x = ∫ x in ball 0 R, |h x| := by
    have hfg : (fun x => h x * g₀ x) =ᵐ[volume.restrict B]
        (ball (0 : Euclid n) R).indicator (fun x => |h x|) := by
      filter_upwards [hae] with x hx
      simp only [hg₀, Set.indicator]
      split_ifs with hxR hpos
      · rw [hx, mul_one, abs_of_nonneg hpos]
      · rw [hx, mul_neg_one, abs_of_neg (not_le.1 hpos)]
      · rw [mul_zero]
    rw [integral_congr_ae hfg, setIntegral_indicator measurableSet_ball,
      Set.inter_eq_right.2 (ball_subset_ball (by linarith : R ≤ R + δ))]
  -- Step 7: a limit of numbers `≤ C` is `≤ C`
  rw [← heq]
  exact le_of_tendsto' hlim hle
/-- **Continuity of the mollification** (the "`w` is continuous" step of the BV estimate): if `u`
is integrable on `S ⊆ ℝⁿ` and `φ` is continuous with compact support, then
`x ↦ ∫_S u(y) φ(x - y) dy` is continuous.  `φ` is bounded, `|φ| ≤ K`, so for every `x` the
integrand is dominated by the `x`-independent integrable function `|u| K`, and it is continuous in
`x` for every `y`; conclude by `continuous_of_dominated`. -/
theorem Submission.cbr_ci_pw_bv_mollify_continuous : ∀ (n : ℕ) (S : Set (Euclid n)) (φ u : Euclid n → ℝ), IntegrableOn u S → Continuous φ → HasCompactSupport φ → Continuous (fun x => ∫ y in S, u y * φ (x - y)) := by
  intro n S φ u hu hφ hφc
  -- `|φ| ≤ K`: `φ` is continuous with compact support
  obtain ⟨K, hK⟩ := hφ.bounded_above_of_compact_support hφc
  -- dominated continuity of parametric integrals, with the dominant `|u| K` integrable on `S`
  refine continuous_of_dominated (bound := fun y => ‖u y‖ * K) (fun x => ?_) (fun x => ?_)
    (hu.norm.mul_const K) (Eventually.of_forall fun y => ?_)
  · -- measurability in `y`: `u` is a.e.-strongly measurable on `S`, `y ↦ φ (x - y)` is continuous
    exact hu.aestronglyMeasurable.mul
      (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · -- domination: `|u y φ (x - y)| ≤ |u y| K`
    exact Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
  · -- continuity in `x` for each fixed `y`
    exact continuous_const.mul (hφ.comp (continuous_id.sub continuous_const))

/-- **BV estimate for mollification** (for the integer multiplicity of limits in Simon 7.2.4,
Remark 7.2.5(1); the boundary mass `M_{B_{2R}}(∂Y)` is replaced by a variation bound `V`): if `u`
is integrable on `B_{2R}(0)` and `|∫_{B_{2R}(0)} u(y) Df(y)(z) dy| ≤ V‖z‖M` for every smooth `f`
supported in `B_{2R}(0)` with `|f| ≤ M`, then `∫_{B_R(0)} |u − w| ≤ sV` for
`w(x) = ∫_{B_{2R}(0)} u(y)φ(x − y) dy`, where `φ ≥ 0` is smooth, `tsupport φ ⊆ B_s(0)`,
`∫φ = 1` and `2s < R`.  The mollification `w` is continuous (`cbr_ci_pw_bv_mollify_continuous`),
so `u − w` is integrable on `B_{R+s}(0)`; its pairings with smooth `g`, `|g| ≤ 1`,
`tsupport g ⊆ B_{R+s}(0)` are at most `sV` (`cbr_ci_pw_bv_smooth_test_bound`); `L¹` duality
(`cbr_ci_pw_bv_l1_duality` with `δ = s`) concludes. -/
theorem Submission.cbr_ci_pw_bv_mollifier_estimate : ∀ (n : ℕ) (R s V : ℝ) (φ u : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ∫ x in ball 0 R, |u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)| ≤ s * V := by
  intro n R s V φ u hR hs hsR hV hφ hφ0 hφs hφ1 hu hvar
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall 0 s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  have hw : Continuous fun x => ∫ y in ball 0 (2 * R), u y * φ (x - y) :=
    Submission.cbr_ci_pw_bv_mollify_continuous n (ball 0 (2 * R)) φ u hu hφ.continuous hφc
  have hh : IntegrableOn (fun x => u x - ∫ y in ball 0 (2 * R), u y * φ (x - y))
      (ball 0 (R + s)) :=
    (hu.mono_set (ball_subset_ball (by linarith))).fun_sub
      ((hw.continuousOn.integrableOn_compact (isCompact_closedBall 0 (R + s))).mono_set
        ball_subset_closedBall)
  exact Submission.cbr_ci_pw_bv_l1_duality n R s (s * V)
    (fun x => u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) hs hh
    fun g hg hgc hgs hg1 => (le_abs_self _).trans
      (Submission.cbr_ci_pw_bv_smooth_test_bound n R s V φ u g hR hs hsR hV hφ hφ0 hφs hφ1 hu
        hvar hg hgc hgs hg1)

/-- **Simon 7.2.4**, `L¹` convergence of the densities to the constant (step 11 of the weight
lower bound `α ≥ 1`): if `Y_k(ω) = ∫_{B_{2R}(0)} u_k ⟨ω(y), e₀ ∧ ⋯ ∧ e_d⟩ dy`, the `u_k` are
eventually `L¹`-bounded by `Λ` on `B_{2R}(0)`, `M_{B_{2R}(0)}(∂Y_k) → 0` and
`Y_k(ω) → c ∫ ⟨ω(y), e₀ ∧ ⋯ ∧ e_d⟩ dy` for every test form `ω`, then `∫_{B_R(0)} |u_k − c| → 0`.
Test functions `b` give the test forms `b dy`, so `∫ u_k b → c ∫ b`; for a normalized bump `φ`
supported in `B_{R/4}(0)` the mollifications `w_k = u_k ∗ φ` converge to `c` uniformly on
`B̄_R(0)` (`cbr_ci_pw_mollified_tendstoUniformlyOn`); `∂Y_k(f ι_z(dy)) = ∫ u_k Df(z)`
(`cbr_ci_pw_interior_product_form`) bounds the variation of `u_k` by `M(∂Y_k)`, so
`∫_{B_R(0)} |u_k − w_k| ≤ (R/4) M(∂Y_k)` (`cbr_ci_pw_bv_mollifier_estimate`); and
`∫_{B_R(0)} |u_k − c| ≤ (R/4) M(∂Y_k) + |B_R(0)| sup_{B̄_R(0)} |w_k − c| → 0`. -/
theorem Submission.dmcbr_ci_pw_density_l1_tendsto_const : ∀ (d : ℕ) (R c Λ : ℝ) (Y : ℕ → GeometricCurrentOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)) (u : ℕ → Euclid (d + 1) → ℝ), 0 < R → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ (k : ℕ) (ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)), Y k ω = ∫ y in ball 0 (2 * R), u k y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Tendsto (fun k => (Y k).boundary.massOn (ball 0 (2 * R))) atTop (𝓝 0) → (∀ ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1), Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → Tendsto (fun k => ∫ y in ball 0 R, |u k y - c|) atTop (𝓝 0) := by
  have aux_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    intro n
    have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
    refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
    · rw [one_mul, Real.norm_eq_abs]
      exact o.abs_volumeForm_apply_le m
    · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
      have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
        funext i; simp [b]
      rw [h, Module.Basis.det_self]
  have aux_scalar_test_tendsto : ∀ (n : ℕ) (U : Set (Euclid n)) (c : ℝ) (Y : ℕ → GeometricCurrentOn U n) (u : ℕ → Euclid n → ℝ), (∀ (k : ℕ) (ω : TestFormOn U n), Y k ω = ∫ y in U, u k y * (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ ω : TestFormOn U n, Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → Tendsto (fun k => ∫ y in U, u k y * b y) atTop (𝓝 (c * ∫ y, b y)) := by
    intro n U c Y u hrep hweak b hb hbc hbU
    obtain ⟨δ, hδ⟩ := aux_exists_det_covector n
    have hmem : (fun y => b y • δ : DifferentialForm (Euclid n) n) ∈ testFormOnSubmodule (E := Euclid n) U n :=
      ⟨⟨hb.smul contDiff_const, hbc.smul_right⟩, (tsupport_smul_subset_left b (fun _ => δ)).trans hbU⟩
    let ω : TestFormOn U n := ⟨fun y => b y • δ, hmem⟩
    have hωe : ∀ y, (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ)) = b y := by
      intro y
      simp [ω, hδ]
    have h1 := hweak ω
    simp only [hωe] at h1
    refine h1.congr (fun k => ?_)
    rw [hrep k ω]
    simp only [hωe]
  have aux_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
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
  have aux_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
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
  have aux_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
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
  have aux_boundary_variation_bound : ∀ (d : ℕ) (U : Set (Euclid (d + 1))) (Y : GeometricCurrentOn U (d + 1)) (u : Euclid (d + 1) → ℝ) (ε : Covector (Euclid (d + 1)) d) (f : Euclid (d + 1) → ℝ) (z : Euclid (d + 1)) (M : ℝ), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ y in U, u y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Y.boundary.massOn U ≠ ∞ → covectorEuclideanNorm ε ≤ ‖z‖ → (∀ y, exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z) → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U → (∀ y, |f y| ≤ M) → |∫ y in U, u y * fderiv ℝ f y z| ≤ (Y.boundary.massOn U).toReal * ‖z‖ * M := by
    intro d U Y u ε f z M hrep hfin hεn hεd hf hfc hfU hM
    -- the test `d`-form `γ = f ε`, with `spt γ ⊆ spt f ⊆ U`
    have hsupp : tsupport (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ⊆ U :=
      (tsupport_smul_subset_left f (fun _ => ε)).trans hfU
    have hmem : (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ∈
        testFormOnSubmodule (E := Euclid (d + 1)) U d :=
      ⟨⟨hf.smul contDiff_const, hfc.smul_right⟩, hsupp⟩
    let γ : TestFormOn U d := ⟨fun x => f x • ε, hmem⟩
    -- `|γ(x)| = |f(x)| |ε| ≤ M ‖z‖`
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hbound : ∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid (d + 1)) d) x) ≤
        M * ‖z‖ := by
      intro x
      change covectorEuclideanNorm (f x • ε) ≤ M * ‖z‖
      rw [(aux_norm_props (d + 1) d).2.1]
      exact mul_le_mul (hM x) hεn (covectorEuclideanNorm_nonneg ε) hM0
    -- `|∂Y(γ)| ≤ M ‖z‖ M_U(∂Y)`
    have key := aux_abs_apply_le_massOn (d + 1) d U U Y.boundary γ (M * ‖z‖) hfin hsupp
      hbound
    -- `∂Y(γ) = Y(dγ) = ∫_U u Df(z)`
    have heq : Y.boundary γ = ∫ y in U, u y * fderiv ℝ f y z := by
      rw [GeometricCurrentOn.boundary_apply, hrep]
      congr 1
      funext y
      change u y * exteriorDerivative (fun x => f x • ε) y
        (fun i => EuclideanSpace.single i (1 : ℝ)) = _
      rw [hεd y]
    rw [heq] at key
    calc |∫ y in U, u y * fderiv ℝ f y z| ≤ M * ‖z‖ * (Y.boundary.massOn U).toReal := key
      _ = (Y.boundary.massOn U).toReal * ‖z‖ * M := by ring
  have aux_l1_squeeze_of_mollified : ∀ (n : ℕ) (R c : ℝ) (φ : Euclid n → ℝ) (u : ℕ → Euclid n → ℝ) (a : ℕ → ℝ), 0 < R → Continuous φ → HasCompactSupport φ → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → TendstoUniformlyOn (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (fun _ => c) atTop (closedBall 0 R) → Tendsto a atTop (𝓝 0) → (∀ᶠ k in atTop, ∫ x in ball 0 R, |u k x - ∫ y in ball 0 (2 * R), u k y * φ (x - y)| ≤ a k) → Tendsto (fun k => ∫ x in ball 0 R, |u k x - c|) atTop (𝓝 0) := by
    intro n R c φ u a hR hφ hφc hint hunif ha hbound
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
    -- continuity of the mollifications
    have hwcont : ∀ k, Continuous (fun x => ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) := by
      intro k
      refine continuous_of_dominated (bound := fun y => ‖u k y‖ * C) (fun x => ?_) (fun x => ?_) ?_ ?_
      · exact (hint k).aestronglyMeasurable.mul
          (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      · exact (hint k).norm.mul_const C
      · exact Eventually.of_forall fun y => continuous_const.mul (hφ.comp (continuous_id.sub continuous_const))
    have hBR : ball (0 : Euclid n) R ⊆ ball 0 (2 * R) := ball_subset_ball (by linarith)
    have hvol : volume (ball (0 : Euclid n) R) < ∞ := measure_ball_lt_top
    have hwint : ∀ k, IntegrableOn (fun x => ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) (ball 0 R) :=
      fun k => ((hwcont k).continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
        ball_subset_closedBall
    have huint : ∀ k, IntegrableOn (u k) (ball 0 R) := fun k => (hint k).mono_set hBR
    have hcint : IntegrableOn (fun _ : Euclid n => c) (ball 0 R) := integrableOn_const hvol.ne
    have htri : ∀ k, ∫ x in ball 0 R, |u k x - c| ≤
        (∫ x in ball 0 R, |u k x - ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)|) +
          ∫ x in ball 0 R, |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c| := by
      intro k
      have hA : IntegrableOn (fun x => |u k x - ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)|)
          (ball 0 R) := ((huint k).sub (hwint k)).abs
      have hB : IntegrableOn (fun x => |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c|)
          (ball 0 R) := ((hwint k).sub hcint).abs
      rw [← integral_add hA hB]
      exact integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hA.add hB)
        (Eventually.of_forall fun x => abs_sub_le _ _ _)
    set m := (volume (ball (0 : Euclid n) R)).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη0 : 0 < ε / (2 * (m + 1)) := by positivity
    have h1 := Metric.tendstoUniformlyOn_iff.1 hunif _ hη0
    have h2 := Metric.tendsto_nhds.1 ha (ε / 2) (by positivity)
    filter_upwards [h1, h2, hbound] with k hk1 hk2 hk3
    have hwc : ∫ x in ball 0 R, |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c| ≤
        ε / (2 * (m + 1)) * m := by
      have := norm_setIntegral_le_of_norm_le_const hvol (C := ε / (2 * (m + 1)))
        (f := fun x => |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c|) (fun x hx => by
          have := hk1 x (ball_subset_closedBall hx)
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
          exact this.le)
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)
    have hnn : 0 ≤ ∫ x in ball 0 R, |u k x - c| := integral_nonneg fun x => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    rw [Real.dist_eq, sub_zero] at hk2
    have hak : a k < ε / 2 := (le_abs_self _).trans_lt hk2
    have hlast : ε / (2 * (m + 1)) * m < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := htri k
    linarith
  intro d R c Λ Y u hR hint hΛ hrep hbd hconv
  -- Step 1: scalar tests `∫_U u_k b → c ∫ b`
  have htest :=
    aux_scalar_test_tendsto (d + 1) (ball 0 (2 * R)) c Y u hrep hconv
  -- Step 2: a normalized mollifier `φ` with `tsupport φ ⊆ B̄_{R/8}(0) ⊆ B_s(0)`, `s = R/4`
  obtain ⟨φ, hφ, hφc, hφ0, hφ1, hφs⟩ :=
    aux_exists_normalized_mollifier (d + 1) (R / 8) (by positivity)
  have hφt : tsupport φ ⊆ ball 0 (R / 4) :=
    (closure_minimal (hφs.trans ball_subset_closedBall) isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  -- Step 3: `w_k → c ∫ φ = c` uniformly on `B̄_R(0)`
  have hunif := Submission.cbr_ci_pw_mollified_tendstoUniformlyOn (d + 1) R (R / 4) c Λ φ u hR
    (by positivity) (by linarith) hφ hφt hint hΛ htest
  rw [hφ1, mul_one] at hunif
  -- Step 4: `V_k = M_U(∂Y_k).toReal → 0`, and eventually `M_U(∂Y_k) ≠ ∞`
  have hV : Tendsto (fun k => ((Y k).boundary.massOn (ball 0 (2 * R))).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hbd
  have hfin := hbd.eventually_ne ENNReal.zero_ne_top
  -- Step 5: `∫_{B_R} |u_k − w_k| ≤ s V_k`, by the BV estimate; its hypothesis
  -- `|∫_U u_k ∂_z f| ≤ V_k ‖z‖ M` comes from `ε_z` and the boundary-mass bound
  have hbv : ∀ᶠ k in atTop,
      ∫ x in ball 0 R, |u k x - ∫ y in ball 0 (2 * R), u k y * φ (x - y)| ≤
        R / 4 * ((Y k).boundary.massOn (ball 0 (2 * R))).toReal := by
    filter_upwards [hfin] with k hk
    refine Submission.cbr_ci_pw_bv_mollifier_estimate (d + 1) R (R / 4)
      ((Y k).boundary.massOn (ball 0 (2 * R))).toReal φ (u k) hR (by positivity) (by linarith)
      ENNReal.toReal_nonneg hφ hφ0 hφt hφ1 (hint k) fun f z M hf hfc hft hM => ?_
    obtain ⟨ε, hε, hεf⟩ := Submission.cbr_ci_pw_interior_product_form d z
    exact aux_boundary_variation_bound d (ball 0 (2 * R)) (Y k) (u k) ε f z M
      (hrep k) hk hε (fun y => hεf f y (hf.differentiable (by simp) y)) hf hfc hft hM
  -- Step 6: the `L¹` squeeze with `a_k = s V_k → 0`
  exact aux_l1_squeeze_of_mollified (d + 1) R c φ u
    (fun k => R / 4 * ((Y k).boundary.massOn (ball 0 (2 * R))).toReal) hR hφ.continuous hφc hint
    hunif (by simpa only [mul_zero] using hV.const_mul (R / 4)) hbv

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
