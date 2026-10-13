<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.divergence_lift-a1 -->

## Theorem `Submission.codim1_zsl_fl_divergence_lift`

Let n, k ∈ ℕ, P := n + 1 + k, and let ι : ℝ^{n+1} → ℝ^P and ι' : ℝ^k → ℝ^P be linear isometries with ⟨ιv, ι'w⟩ = 0 for all v, w and such that every y ∈ ℝ^P equals ιv + ι'w for some v, w (ℝ^d = Euclid d). Then there is a constant K > 0 with the following property. For all real h > 0 and R, and every C^∞ vector field φ : ℝ^{n+1} → ℝ^{n+1} (ContDiff ℝ (⊤ : ℕ∞) φ) with compact support, tsupport φ ⊆ ball(0, R) and |φ(v)| ≤ 1 for all v, there is a test form ω ∈ 𝒟^n(ℝ^P) (ω : TestFormOn univ n, i.e. a C^∞ n-form on ℝ^P with compact support) such that: (i) tsupport ω ⊆ ball(0, R + 2h) ⊆ ℝ^P; (ii) covectorEuclideanNorm(ω(y)) ≤ 1 for every y ∈ ℝ^P; (iii) for every map g : ℝ^{n+1} → ℝ^k and every v ∈ ℝ^{n+1} such that g is differentiable at v and |g(v)| < h, dω(ιv + ι'g(v))(DG(v)e_0, …, DG(v)e_n) = K⁻¹·div φ(v), where G(w) := ιw + ι'g(w), DG(v) := fderiv ℝ G v, e_j := EuclideanSpace.single j 1, dω := exteriorDerivative ω and div φ(v) := trace Dφ(v) (LinearMap.trace of (fderiv ℝ φ v)).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.divergence_lift-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5038

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3484, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3501

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_zsl_fl_divergence_lift`

```lean
∀ (n k : ℕ) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → ∃ K : ℝ, 0 < K ∧ ∀ h R : ℝ, 0 < h → ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∃ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 (R + 2 * h) ∧ (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) ∧ ∀ (g : Euclid (n + 1) → Euclid k) (v : Euclid (n + 1)), DifferentiableAt ℝ g v → ‖g v‖ < h → exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι v + ι' (g v)) (fun j => fderiv ℝ (fun w => ι w + ι' (g w)) v (EuclideanSpace.single j (1 : ℝ))) = K⁻¹ * LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.divergence_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Part A (steps A1–A6) of the supplied proof of the parent node codim1_zsl_flat_graph_limit (lifting divergence fields to test forms with a cut-off in the normal direction; uniform comass bound K), together with the normalisation ω/K of its step B3, which is built into the form here. Simon 7.5.3 (chapter-07.txt lines 790–860) uses this lifting implicitly when it applies the BV Compactness 2.6 of Ch. 2 to the rescaled regions. Departures from the supplied Part A, none of which changes the argument: (1) the contracted volume form Ω(z, ·) of A1–A2 is written Θ(z) = Σ_j z_j·β_j with the coordinate covectors β_j = e_j ⌟ det of the accepted sibling coordinate_covector (Submission.dgcr_bwd_coordinate_covector); this is the same covector because Ω(z, ·) = Σ_j z_j·Ω(e_j, ·); (2) the cut-off χ(|ι'*y|²) built from smoothTransition in A3 is replaced by f(ι'*y) for a ContDiffBump f on ℝ^k with radii h < 2h, which has the same properties (C^∞, values in [0, 1], = 1 where |ι'*y| ≤ h, = 0 where |ι'*y| ≥ 2h); (3) the constant K of A5 is explicit; (4) the identity d(π^#α̃)(G(v))(DG(v)e) = dα̃(v)(e) of A6 is the accepted sibling pullback_extderiv (Submission.dgcr_bwd_graph_pullback_extDeriv) with z = 0.
Notation. P := n + 1 + k; ℝ^d := Euclid d; e_j := EuclideanSpace.single j (1 : ℝ) ∈ ℝ^{n+1}, e := (e_0, …, e_n), and removeNth i e := Fin.removeNth i e (e with e_i deleted). π := ι* := ContinuousLinearMap.adjoint ι.toContinuousLinearMap : ℝ^P → ℝ^{n+1} and π' := ι'* : ℝ^P → ℝ^k likewise. ‖·‖ denotes operator norms; |α| := covectorEuclideanNorm α = (Σ_{I strictly increasing} α(b_{I(0)}, …, b_{I(n−1)})²)^{1/2} for an n-covector α on ℝ^P, b_l := EuclideanSpace.basisFun (Fin P) ℝ l the standard basis of ℝ^P. (In Lean the smoothness order must be written (⊤ : ℕ∞): in the contract scope `∞` is ENNReal's ∞.)
1. Adjoint identities. For v ∈ ℝ^{n+1} and w ∈ ℝ^k: π(ιv) = v, π(ι'w) = 0, π'(ι'w) = w and π'(ιv) = 0. Indeed, for every y, ⟨π(ιv), y⟩ = ⟨ιv, ιy⟩ (ContinuousLinearMap.adjoint_inner_left) = ⟨v, y⟩ (LinearIsometry.inner_map_map), and ⟨π(ι'w), y⟩ = ⟨ι'w, ιy⟩ = ⟨ιy, ι'w⟩ = 0 by the orthogonality hypothesis (real_inner_comm); the same computation with the roles of ι and ι' exchanged gives the other two; vectors with the same inner product against every y are equal (ext_inner_right).
2. Norm splitting. For every y ∈ ℝ^P, |y| ≤ |πy| + |π'y|: write y = ιv + ι'w (spanning hypothesis); by step 1, πy = v and π'y = w, and |y| ≤ |ιv| + |ι'w| = |v| + |w|.
3. Coordinate covectors and Θ. By coordinate_covector with m := n, choose for every j ∈ Fin (n+1) an n-covector β_j on ℝ^{n+1} with β_j(removeNth i e) = (−1)^j if i = j and = 0 if i ≠ j. Let Θ : ℝ^{n+1} → Λ^n(ℝ^{n+1}) be the continuous linear map Θ := Σ_j (EuclideanSpace.proj j).smulRight β_j, i.e. Θ(z) = Σ_j z_j·β_j. Then for all z ∈ ℝ^{n+1} and i: Θ(z)(removeNth i e) = Σ_j z_j·β_j(removeNth i e) = (−1)^i·z_i (ContinuousAlternatingMap.sum_apply; only the summand j = i is nonzero).
4. The constant. Let N := card(Fin n → Fin P) (= P^n) and K := √N·‖Θ‖·‖π‖^n + 1 > 0. K depends only on n, k, ι (through the choice of the β_j and π), not on h, R or φ; this is the asserted constant. From now on fix h > 0, R and φ as in the statement.
5. The form. α̃ := Θ∘φ, i.e. α̃(v) = Σ_j φ_j(v)·β_j = Ω(φ(v), ·): a smooth n-form on ℝ^{n+1} (C^∞ map followed by a continuous linear map). Its affine pull-back P^#α̃ := affinePullbackForm π (−π0) α̃, (P^#α̃)(y) = α̃(−π0 + πy)∘π = α̃(πy)∘π, is a smooth n-form on ℝ^P (affinePullbackForm_isSmoothForm). Let f be the ContDiffBump on ℝ^k centred at 0 with rIn = h and rOut = 2h (0 < h < 2h): f is C^∞ (ContDiffBump.contDiff), 0 ≤ f ≤ 1 (nonneg, le_one), f = 1 on closedBall(0, h) (one_of_mem_closedBall) and support f = ball(0, 2h) (support_eq). Define ω(y) := (K⁻¹·f(π'y))·(P^#α̃)(y). Then ω is C^∞, as the product of the C^∞ function y ↦ K⁻¹f(π'y) with the smooth form P^#α̃ (ContDiff.smul).
6. Support, (i) and ω ∈ 𝒟^n(ℝ^P). Let Q := {y : πy ∈ tsupport φ and |π'y| ≤ 2h}; Q is closed (preimages of closed sets under continuous maps). If ω(y) ≠ 0 then f(π'y) ≠ 0, so π'y ∈ ball(0, 2h) and |π'y| ≤ 2h; and (P^#α̃)(y) ≠ 0, so φ(πy) ≠ 0 (otherwise α̃(πy) = Θ(0) = 0 and the pull-back vanishes), so πy ∈ tsupport φ. Hence the support of ω lies in Q, and tsupport ω ⊆ Q (closure_minimal). For y ∈ Q, πy ∈ tsupport φ ⊆ ball(0, R) gives |πy| < R, so by step 2 |y| ≤ |πy| + |π'y| < R + 2h. Thus tsupport ω ⊆ Q ⊆ ball(0, R + 2h), which is (i); and tsupport ω is a closed subset of the compact closedBall(0, R + 2h), so ω has compact support. Together with step 5, ω is a test form, and tsupport ω ⊆ univ trivially: ω ∈ TestFormOn univ n.
7. Comass bound (ii). Fix y ∈ ℝ^P and a strictly increasing I : Fin n → Fin P. By the definitions (affinePullbackForm, compContinuousLinearMap_apply), ω(y)(b_{I(0)}, …, b_{I(n−1)}) = K⁻¹f(π'y)·Θ(φ(πy))(πb_{I(0)}, …, πb_{I(n−1)}). Here |K⁻¹f(π'y)| ≤ K⁻¹, and by ContinuousAlternatingMap.le_opNorm |Θ(φ(πy))(πb_{I(·)})| ≤ ‖Θ(φ(πy))‖·∏_l |πb_{I(l)}| ≤ ‖Θ‖·|φ(πy)|·‖π‖^n ≤ ‖Θ‖·‖π‖^n (|b_l| = 1 and |φ| ≤ 1). So each of the at most N squared coefficients in |ω(y)|² is at most (K⁻¹‖Θ‖‖π‖^n)², whence |ω(y)|² ≤ N·(K⁻¹‖Θ‖‖π‖^n)² = (√N·K⁻¹‖Θ‖‖π‖^n)² ≤ 1 because √N‖Θ‖‖π‖^n ≤ K; taking square roots (Real.sqrt_le_sqrt, Real.sqrt_one), covectorEuclideanNorm(ω(y)) ≤ 1.
8. Key identity (iii): germ. Let g be differentiable at v with |g(v)| < h, and y₀ := ιv + ι'g(v). By step 1, π'y₀ = g(v), so y₀ lies in the open set {y : |π'y| < h}, on which f(π'y) = 1 (π'y ∈ closedBall(0, h)). Hence ω coincides with K⁻¹·P^#α̃ on a neighbourhood of y₀. The exterior derivative at a point depends only on the germ of the form there (Filter.EventuallyEq.extDeriv_eq; SimonGMT's exteriorDerivative is Mathlib's extDeriv) and d(c·β) = c·dβ (exteriorDerivative_smul). Therefore dω(y₀)(DG(v)e) = K⁻¹·d(P^#α̃)(y₀)(DG(v)e).
9. Key identity (iii): pull-back. Apply pullback_extderiv (Submission.dgcr_bwd_graph_pullback_extDeriv) with m := n, the given k, ι, ι', u := g, z := 0, ψ := α̃ (smooth by step 5) and the point v (g is differentiable at v; orthogonality hypothesis). It gives d(affinePullbackForm π (−π0) α̃)(0 + ιv + ι'g(v))(i ↦ D[w ↦ 0 + ιw + ι'g(w)](v)e_i) = dα̃(v)(e); deleting the summands 0 (zero_add), d(P^#α̃)(y₀)(DG(v)e) = dα̃(v)(e). With step 8: dω(y₀)(DG(v)e) = K⁻¹·dα̃(v)(e).
10. dα̃(v)(e) = div φ(v). The form α̃ is differentiable at v, so by the coordinate formula for d (SimonGMT exteriorDerivative_apply), dα̃(v)(e) = Σ_i (−1)^i·D[x ↦ α̃(x)(removeNth i e)](v)e_i. By step 3, α̃(x)(removeNth i e) = Θ(φ(x))(removeNth i e) = (−1)^i·φ_i(x), where φ_i(x) := (φ(x))_i; by the chain rule with the coordinate projection EuclideanSpace.proj i, the derivative at v applied to e_i is (−1)^i·(Dφ(v)e_i)_i. Hence dα̃(v)(e) = Σ_i (−1)^i(−1)^i(Dφ(v)e_i)_i = Σ_i (Dφ(v)e_i)_i = Σ_i ⟨e_i, Dφ(v)e_i⟩ = trace Dφ(v) (LinearMap.trace_eq_sum_inner for the orthonormal basis EuclideanSpace.basisFun, and ⟨e_i, x⟩ = x_i by EuclideanSpace.inner_single_left). Combining with step 9: dω(ιv + ι'g(v))(DG(v)e_0, …, DG(v)e_n) = K⁻¹·div φ(v), which is (iii). ∎
Formalization note: unless this child is split further it is a machine leaf (one theorem appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declaration, no import, no set_option). The tactic proof below was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context: the frozen Submission.lean with the accepted dependencies Submission.dgcr_bwd_coordinate_covector and Submission.dgcr_bwd_graph_pullback_extDeriv merged before it, under default maxHeartbeats. It passes the workflow's leaf source-delta check (leaf_verification.check_source_delta), its frozen type passes lean_contract.validate_lean_statement and elaborates in the comparator's replayed contract scope, and #print axioms gives only propext, Classical.choice, Quot.sound. It may be used verbatim:
theorem Submission.codim1_zsl_fl_divergence_lift : ∀ (n k : ℕ) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → ∃ K : ℝ, 0 < K ∧ ∀ h R : ℝ, 0 < h → ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∃ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 (R + 2 * h) ∧ (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) ∧ ∀ (g : Euclid (n + 1) → Euclid k) (v : Euclid (n + 1)), DifferentiableAt ℝ g v → ‖g v‖ < h → exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι v + ι' (g v)) (fun j => fderiv ℝ (fun w => ι w + ι' (g w)) v (EuclideanSpace.single j (1 : ℝ))) = K⁻¹ * LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap := by
  intro n k ι ι' hperp hspan
  classical
  set π : Euclid (n + 1 + k) →L[ℝ] Euclid (n + 1) :=
    ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hπeq
  set π' : Euclid (n + 1 + k) →L[ℝ] Euclid k :=
    ContinuousLinearMap.adjoint ι'.toContinuousLinearMap with hπ'eq
  have hπι : ∀ v, π (ι v) = v := by
    intro v
    apply ext_inner_right ℝ
    intro y
    rw [hπeq, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v y
  have hπι' : ∀ w, π (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hπeq, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  have hπ'ι' : ∀ w, π' (ι' w) = w := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hπ'eq, ContinuousLinearMap.adjoint_inner_left]
    exact ι'.inner_map_map w y
  have hπ'ι : ∀ v, π' (ι v) = 0 := by
    intro v
    apply ext_inner_right ℝ
    intro y
    rw [hπ'eq, ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    exact hperp v y
  have hnorm_le : ∀ y, ‖y‖ ≤ ‖π y‖ + ‖π' y‖ := by
    intro y
    obtain ⟨v, w, rfl⟩ := hspan y
    simp only [map_add, hπι, hπι', hπ'ι', hπ'ι, add_zero, zero_add]
    calc ‖ι v + ι' w‖ ≤ ‖ι v‖ + ‖ι' w‖ := norm_add_le _ _
      _ = ‖v‖ + ‖w‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  choose β hβ using Submission.dgcr_bwd_coordinate_covector n
  let Θ : Euclid (n + 1) →L[ℝ] Covector (Euclid (n + 1)) n :=
    ∑ j : Fin (n + 1), (EuclideanSpace.proj j : Euclid (n + 1) →L[ℝ] ℝ).smulRight (β j)
  have hΘe : ∀ (z : Euclid (n + 1)) (i : Fin (n + 1)),
      Θ z (i.removeNth (fun l : Fin (n + 1) => EuclideanSpace.single l (1 : ℝ))) =
        (-1 : ℝ) ^ (i : ℕ) * z i := by
    intro z i
    have hΘz : Θ z = ∑ j, z j • β j := by simp [Θ]
    rw [hΘz, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hβ i i, ite_eq_left rfl]
      ring
    · intro j _ hji
      rw [hβ j i, ite_eq_right (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  set N : ℝ := (Fintype.card (Fin n → Fin (n + 1 + k)) : ℝ) with hN
  set K : ℝ := Real.sqrt N * ‖Θ‖ * ‖π‖ ^ n + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, ?_⟩
  intro h R hh φ hφ hφc hφs hφn
  let f : ContDiffBump (0 : Euclid k) := ⟨h, 2 * h, hh, by linarith⟩
  let α : DifferentialForm (Euclid (n + 1)) n := fun v => Θ (φ v)
  have hαsmooth : IsSmoothForm α := Θ.contDiff.comp hφ
  let ω₀ : DifferentialForm (Euclid (n + 1 + k)) n := fun y =>
    (K⁻¹ * f (π' y)) • affinePullbackForm π (-(π 0)) α y
  have hω₀smooth : IsSmoothForm ω₀ := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => K⁻¹ * f (π' y)) :=
      contDiff_const.mul (f.contDiff.comp π'.contDiff)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (affinePullbackForm π (-(π 0)) α) :=
      affinePullbackForm_isSmoothForm π _ hαsmooth
    exact h1.smul h2
  set Q : Set (Euclid (n + 1 + k)) := {y | π y ∈ tsupport φ ∧ ‖π' y‖ ≤ 2 * h} with hQ
  have hQclosed : IsClosed Q :=
    ((isClosed_tsupport φ).preimage π.continuous).inter
      (isClosed_le (continuous_norm.comp π'.continuous) continuous_const)
  have hsuppQ : support ω₀ ⊆ Q := by
    intro y hy
    by_contra hyQ
    apply hy
    simp only [hQ, Set.mem_ofPred_eq, not_and_or, not_le] at hyQ
    rcases hyQ with h1 | h1
    · have h0 : φ (π y) = 0 := image_eq_zero_of_notMem_tsupport h1
      have hP : affinePullbackForm π (-(π 0)) α y = 0 := by
        ext m
        simp [affinePullbackForm, α, h0]
      show (K⁻¹ * f (π' y)) • affinePullbackForm π (-(π 0)) α y = 0
      rw [hP, smul_zero]
    · have h0 : f (π' y) = 0 := by
        rw [← Function.notMem_support, f.support_eq]
        simp only [mem_ball, dist_zero_right, not_lt]
        exact h1.le
      simp [ω₀, h0]
  have htsuppQ : tsupport ω₀ ⊆ Q := closure_minimal hsuppQ hQclosed
  have hQball : Q ⊆ ball 0 (R + 2 * h) := by
    rintro y ⟨hy1, hy2⟩
    have := hφs hy1
    rw [mem_ball, dist_zero_right] at this ⊢
    linarith [hnorm_le y]
  have hcpt : HasCompactSupport ω₀ :=
    (isCompact_closedBall (0 : Euclid (n + 1 + k)) (R + 2 * h)).of_isClosed_subset
      (isClosed_tsupport _) (htsuppQ.trans (hQball.trans ball_subset_closedBall))
  let ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n := ⟨ω₀, ⟨hω₀smooth, hcpt⟩, subset_univ _⟩
  refine ⟨ω, htsuppQ.trans hQball, ?_, ?_⟩
  · -- comass bound
    intro y
    change covectorEuclideanNorm (ω₀ y) ≤ 1
    have hM : ∀ I : Fin n → Fin (n + 1 + k),
        |ω₀ y (fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))| ≤
          K⁻¹ * (‖Θ‖ * ‖π‖ ^ n) := by
      intro I
      simp only [ω₀, ContinuousAlternatingMap.smul_apply, smul_eq_mul, affinePullbackForm,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [abs_mul]
      have hζ : |K⁻¹ * f (π' y)| ≤ K⁻¹ := by
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hKpos.le) f.nonneg)]
        exact mul_le_of_le_one_right (inv_nonneg.2 hKpos.le) f.le_one
      have hα : |α (-(π 0) + π y) (π ∘ fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))| ≤
          ‖Θ‖ * ‖π‖ ^ n := by
        rw [← Real.norm_eq_abs]
        calc _ ≤ ‖α (-(π 0) + π y)‖ *
              ∏ i, ‖(π ∘ fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i)) i‖ :=
              ContinuousAlternatingMap.le_opNorm _ _
          _ ≤ ‖Θ‖ * ∏ _i : Fin n, ‖π‖ := by
              gcongr with i
              · calc ‖Θ (φ (-(π 0) + π y))‖ ≤ ‖Θ‖ * ‖φ (-(π 0) + π y)‖ := Θ.le_opNorm _
                  _ ≤ ‖Θ‖ * 1 := by gcongr; exact hφn _
                  _ = ‖Θ‖ := mul_one _
              · calc ‖π (EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))‖
                    ≤ ‖π‖ * ‖EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i)‖ := π.le_opNorm _
                  _ = ‖π‖ := by simp
          _ = ‖Θ‖ * ‖π‖ ^ n := by simp
      exact mul_le_mul hζ hα (abs_nonneg _) (inv_nonneg.2 hKpos.le)
    have hsum : (∑ I : Fin n → Fin (n + 1 + k), if StrictMono I then
        (ω₀ y (fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))) ^ 2 else 0) ≤ 1 := by
      calc _ ≤ ∑ _I : Fin n → Fin (n + 1 + k), (K⁻¹ * (‖Θ‖ * ‖π‖ ^ n)) ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · exact sq_le_sq' (abs_le.1 (hM I)).1 (abs_le.1 (hM I)).2
            · positivity
        _ = (Real.sqrt N * (K⁻¹ * (‖Θ‖ * ‖π‖ ^ n))) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, mul_pow (Real.sqrt N),
              Real.sq_sqrt (by positivity)]
        _ ≤ 1 ^ 2 := by
            gcongr
            rw [← mul_assoc, mul_comm (Real.sqrt N), mul_assoc, ← mul_assoc (Real.sqrt N),
              inv_mul_le_one₀ hKpos]
            linarith
        _ = 1 := one_pow 2
    unfold covectorEuclideanNorm
    calc _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  · -- key identity
    intro g v hg hgv
    have hy₀ : π' (ι v + ι' (g v)) = g v := by simp [map_add, hπ'ι, hπ'ι']
    have hev : ω₀ =ᶠ[𝓝 (ι v + ι' (g v))] K⁻¹ • affinePullbackForm π (-(π 0)) α := by
      have hopen : IsOpen {y : Euclid (n + 1 + k) | ‖π' y‖ < h} :=
        isOpen_lt (continuous_norm.comp π'.continuous) continuous_const
      have hmem : ι v + ι' (g v) ∈ {y : Euclid (n + 1 + k) | ‖π' y‖ < h} := by
        simpa [hy₀] using hgv
      filter_upwards [hopen.mem_nhds hmem] with y hy
      have h1 : f (π' y) = 1 :=
        f.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy.le)
      simp [ω₀, h1]
    change exteriorDerivative ω₀ (ι v + ι' (g v)) _ = _
    rw [show exteriorDerivative ω₀ (ι v + ι' (g v)) =
        exteriorDerivative (K⁻¹ • affinePullbackForm π (-(π 0)) α) (ι v + ι' (g v)) from
        hev.extDeriv_eq, exteriorDerivative_smul]
    simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    congr 1
    have h3 := Submission.dgcr_bwd_graph_pullback_extDeriv n k ι ι' g 0 α v hperp hαsmooth hg
    simp only [zero_add] at h3
    rw [h3]
    have hφd : DifferentiableAt ℝ φ v := (hφ.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply (hαsmooth.differentiable (by simp)).differentiableAt]
    have hfun : ∀ i : Fin (n + 1), (fun x => α x (i.removeNth
        (fun l : Fin (n + 1) => EuclideanSpace.single l (1 : ℝ)))) =
          fun x => (-1 : ℝ) ^ (i : ℕ) * φ x i := by
      intro i
      funext x
      exact hΘe (φ x) i
    simp only [hfun]
    have hder : ∀ i : Fin (n + 1), fderiv ℝ (fun x => (-1 : ℝ) ^ (i : ℕ) * φ x i) v
        (EuclideanSpace.single i (1 : ℝ)) =
          (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ φ v (EuclideanSpace.single i (1 : ℝ))) i := by
      intro i
      have hp : HasFDerivAt (fun x => φ x i)
          ((EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).comp (fderiv ℝ φ v)) v :=
        (EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp v hφd.hasFDerivAt
      rw [(hp.const_mul ((-1 : ℝ) ^ (i : ℕ))).fderiv]
      simp
    simp only [hder]
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      EuclideanSpace.inner_single_left]
    rw [zsmul_eq_mul]
    push_cast
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

## Key steps

1. Adjoints π = ι*, π' = ι'* satisfy πι = id, πι' = 0, π'ι' = id, π'ι = 0, and |y| ≤ |πy| + |π'y| (spanning).
2. Θ(z) := Σ_j z_j·β_j with the coordinate covectors β_j = e_j ⌟ det (coordinate_covector) satisfies Θ(z)(removeNth i e) = (−1)^i z_i; K := √N·‖Θ‖·‖π‖^n + 1.
3. ω(y) := K⁻¹·f(π'y)·α̃(πy)∘π with α̃ = Θ∘φ and a ContDiffBump f (radii h, 2h): C^∞, tsupport ω ⊆ {πy ∈ tsupport φ, |π'y| ≤ 2h} ⊆ ball(0, R + 2h), compact.
4. Each coefficient of ω(y) is at most K⁻¹‖Θ‖‖π‖^n in absolute value, so covectorEuclideanNorm(ω(y)) ≤ √N·K⁻¹‖Θ‖‖π‖^n ≤ 1.
5. Near ιv + ι'g(v) with |g(v)| < h, ω = K⁻¹·π^#α̃; germ locality of d and pullback_extderiv (z = 0) give dω(G(v))(DG(v)e) = K⁻¹·dα̃(v)(e).
6. Coordinate formula for d with Θ(z)(removeNth i e) = (−1)^i z_i: dα̃(v)(e) = Σ_i (Dφ(v)e_i)_i = trace Dφ(v) = div φ(v).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: the selected node (status, message, children, descendants by id prefix); lean_name lookup of the 6 child names and of codim1_zsl_perimeter_compactness; byte equality of the 2 reused lean_statements and statements with decomposition-v1.json; raw count of 'codim1_zsl_fl_'; scan of nodes/*/*.json outside this node for 'codim1_zsl_fl_'`
- `python3 dump of this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and parent-child-handoff.json; issue-workers.json entries for issue 5038`
- `git log --all --oneline -S'codim1_zsl_fl_' -- 'GMT/*.lean' (0 commits); positive control git log --all --oneline -S'dgcr_bwd_graph_pullback_extDeriv' -- 'GMT/*.lean'`
- `git show dcc3f4b7fc0f6beb359e7585fbca8b266cc0f38f:GMT/Ch07/Submission.lean; git show 42e24164cfdc5445c7426ab7ee11003f8faee961:GMT/Ch07/Submission.lean (the accepted reused blocks)`
- `grep -n 'structure TestFormOn|def IsTestForm|theorem exteriorDerivative_isTestForm|theorem tsupport_exteriorDerivative_subset|def exteriorDerivative|def covectorEuclideanNorm|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem affinePullbackForm_isSmoothForm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|Bornology.IsBounded.subset_ball_lt|theorem norm_add_sq_real' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -rl 'map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume' local-references/123e8435b4a2469b/mathlib/Mathlib; diff of snapshot vs .lake/packages/mathlib Bochner/Set.lean (identical)`
- `lake env lean /tmp/fl-v2-decomp/lean/Check2.lean (frozen Submission.lean + accepted dcc3f4b7/42e24164 blocks + sorry placeholder for codim1_zsl_perimeter_compactness + verbatim code of the 4 new children + selected theorem; #print axioms of all 7)`
- `lake env lean /tmp/fl-v2-decomp/lean/Types.lean (import GMT.Ch07.Submission + gmt-compare.contract_scope replay; the 6 child types and the selected type as comparator-style challenges)`
- `lake env lean /tmp/fl-v2-decomp/lean/ContractAssembly2.lean (selected type proved from hypotheses with the frozen perimeter_bound, bv_compactness, graph_integral_limit and isometric_transport types; #print axioms)`
- `python3: lean_contract.validate_lean_statement on the 6 types; leaf_verification.check_source_delta on the 4 new children inserted into GMT/Ch07/Submission.lean; models.ScopedDecomposition validation of this response`
- `sed -n 840,860p book/chapter-07.txt (Simon 7.5.3: by (1) and 5.2 and the BV Compactness 2.6 of Ch. 2 a subsequence converges in L¹_loc)`
- `grep -l '"github_selected_issue": 5038,' .humanize/swarm-configs/* and their max_nodes/max_depth/max_children (cffb5a36…: max_nodes 1000, 08:33Z; 5261729…: max_nodes 5000, 11:17Z); mtime ranges of configs by max_nodes value`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-scope-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-d253855dab51/scripts/gmt-compare.py`
- `/tmp/fl-v2-decomp/lean/Check2.lean`
- `/tmp/fl-v2-decomp/lean/Types.lean`
- `/tmp/fl-v2-decomp/lean/ContractAssembly2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/cffb5a36c88f487d9fb784e09cf6981b.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/5261729094924bd1900f1bef36365ca3.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG state. The selected node is 'decomposing' at 'subproblem decomposition attempt 2' and has no children or descendants. Its v1 split passed the independent review (all six nodes acceptable, no required changes) but was never activated. The cause is not recorded. The first worker's config had max_nodes 1000 while the DAG approached 1000 nodes; the current worker's config has max_nodes 5000. The four codim1_zsl_fl_* names occur nowhere in dag.json (1083 nodes at 12:11Z), in other nodes' files, in GMT/, in simongmt or in git history. dgcr_bwd_coordinate_covector (dcc3f4b7) and dgcr_bwd_graph_pullback_extDeriv (42e24164) are accepted, and their DAG types and statements are byte-identical to the reused subproblems.
Library. The SimonGMT definitions used by the children check out: TestFormOn is the submodule of IsTestForm forms supported in U; exteriorDerivative is extDeriv; exteriorDerivative_isTestForm and tsupport_exteriorDerivative_subset hold; covectorEuclideanNorm is the root of the sum of squared strictly-increasing coordinate coefficients; and affinePullbackForm commutes with d. The snapshot Mathlib contains every lemma the assembly cites: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), Bornology.IsBounded.subset_ball_lt (Bounded.lean:105), norm_add_sq_real (InnerProductSpace/Basic.lean:411), and the Hausdorff isometry lemmas (Geometry/Euclidean/Volume/Measure.lean).
Lean (pinned toolchain v4.35.0-rc3). Check2.lean compiles: each of the six children depends only on propext, Classical.choice and Quot.sound, and the selected theorem adds sorryAx solely through the bv_compactness placeholder. ContractAssembly2.lean proves the selected type from the four frozen contract types alone, with only the three standard axioms. Types.lean elaborates all seven types in the comparator's replayed contract scope. validate_lean_statement and check_source_delta accept every child.
Source. Simon 7.5.3 (book/chapter-07.txt lines 852–856) obtains the L¹_loc subsequence from the BV Compactness 2.6 of Ch. 2, which is the sibling bv_compactness.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
