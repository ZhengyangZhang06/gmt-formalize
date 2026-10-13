<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1 -->

## Theorem `Submission.codim1_zsl_perimeter_compactness`

Let m ∈ ℕ and let F_i ⊆ ℝ^m (i ∈ ℕ) be measurable sets. Assume that for every R > 0 there are c ∈ ℝ and i_R such that for every i ≥ i_R and every C^∞ vector field φ : ℝ^m → ℝ^m (ContDiff ℝ (⊤ : ℕ∞)) with compact support, tsupport φ ⊆ ball(0, R) and |φ(v)| ≤ 1 for all v, one has ∫_{F_i} div φ dL^m ≤ c, where div φ(v) = trace Dφ(v) and L^m is Lebesgue measure. Then there are a strictly increasing σ : ℕ → ℕ and a measurable F' ⊆ ℝ^m such that L^m((F_{σ(i)} Δ F') ∩ ball(0, R)) → 0 as i → ∞ for every R ∈ ℝ.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4348

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3183, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5557, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5563, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5569, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5585, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5597, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5634, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5652, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5660, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5672, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5686

## Lean problem

Declaration: `Submission.codim1_zsl_perimeter_compactness`

```lean
∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F i, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball 0 R)) atTop (𝓝 0)
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 2, 2.6 (Compactness Theorem for BV functions, chapter-02.txt lines 598–625), applied to the indicator functions u_i = 1_{F_i}, with the mollifier facts of Simon Ch. 2, 2.5 (chapter-02.txt lines 521–545). Simon refers to [GT01, Theorem 7.22] for the precompactness ("mollification and Arzelà's theorem"); since the Arzelà–Ascoli theorem is not in the import closure of GMT.Ch07.Submission, the precompactness is proved with cube averages (the elementary Kolmogorov–Riesz argument), using the same mollification estimate. This is the compactness used in step 9 of the supplied proof of the parent node. No sibling child is used.

Notation. L^m = volume on ℝ^m = Euclid m; B_R := ball(0, R); u_i := 1_{F_i}; ‖f‖_{1,S} := ∫_S |f| dL^m; div φ := trace(Dφ). A field φ is admissible for radius R if it is C^∞ with compact support, tsupport φ ⊆ B_R and |φ| ≤ 1. For R > 0 let c(R) and i_R be as in the hypothesis. Since −φ is admissible whenever φ is, |∫_{F_i} div φ| ≤ c(R) for i ≥ i_R; taking φ = 0 shows c(R) ≥ 0. A field admissible for R is admissible for every R' ≥ R.

0. (m = 0.) ℝ^0 is a single point, so each F_i is ∅ or ℝ^0; one of the two values occurs for infinitely many i, which gives σ with F_{σ(i)} constant =: F' and (F_{σ(i)} Δ F') ∩ B_R = ∅. From now on m ≥ 1.

1. (Mollifier.) Fix ρ ∈ C_c^∞(ℝ^m) with ρ ≥ 0, ρ(−z) = ρ(z), tsupport ρ ⊆ closedBall(0, 1) and ∫ρ = 1. Construction: let b be the ContDiffBump centred at 0 with inner radius 1/2 and outer radius 1. It is C^∞ (ContDiffBump.contDiff), 0 ≤ b ≤ 1, even (ContDiffBump.neg: b(−z) = b(z)), support b = ball(0, 1) (ContDiffBump.support_eq) and tsupport b = closedBall(0, 1) (ContDiffBump.tsupport_eq); this closed ball is not contained in the open ball ball(0, 1), so only the closed-ball bound is claimed. b is continuous with compact support, hence integrable, and ∫b > 0 by integral_pos_iff_support_of_nonneg, because its support ball(0, 1) has positive Lebesgue measure (Metric.measure_ball_pos). Put ρ := (∫b)^{−1}·b. Multiplication by the positive constant (∫b)^{−1} preserves smoothness, nonnegativity, evenness and the support, so tsupport ρ = closedBall(0, 1), and ∫ρ = 1. For 0 < ε ≤ 1/2 put ρ_ε(z) := ε^{−m}ρ(z/ε): smooth, even, ≥ 0, tsupport ρ_ε = ε·tsupport ρ = closedBall(0, ε), and ∫ρ_ε = ε^{−m}·ε^m·∫ρ = 1 (change of variables z = εz', Measure.integral_comp_inv_smul_of_nonneg). Below only the bound tsupport ρ_ε ⊆ closedBall(0, ε), i.e. ρ_ε(z) = 0 for |z| > ε, is used (in steps 2 and 3). For a bounded measurable f put f_ε := ρ_ε ⋆ f, f_ε(v) = ∫ρ_ε(z)f(v − z) dz. f_ε is C^∞, its derivatives are obtained by differentiating ρ_ε (HasCompactSupport.contDiff_convolution_left), and |f| ≤ 1 implies |f_ε| ≤ 1.

2. (L¹ convergence of mollifications.) If F ⊆ ℝ^m is measurable, f := 1_F and R > 0, then ‖f_ε − f‖_{1,B_R} → 0 as ε → 0 (only f = u_i is needed). Indeed f_ε(v) − f(v) = ∫ρ_ε(z)(f(v − z) − f(v)) dz, so by Tonelli ‖f_ε − f‖_{1,B_R} ≤ sup_{|z|≤ε}∫_{B_R}|f(v − z) − f(v)| dv, and translations are continuous in L¹: given η > 0, put A := F ∩ B_{R+1}, a measurable set of finite measure. By regularity of Lebesgue measure choose a compact K ⊆ A with L^m(A ∖ K) < η/2 (MeasurableSet.exists_isCompact_sdiff_lt) and an open O ⊇ A with L^m(O ∖ A) < η/2 (MeasurableSet.exists_isOpen_sdiff_lt); as O ∖ K ⊆ (O ∖ A) ∪ (A ∖ K), L^m(O ∖ K) < η. Choose a continuous g : ℝ^m → [0, 1] with compact support, g = 1 on K and g = 0 on ℝ^m ∖ O (exists_continuous_one_zero_of_isCompact applied to the compact set K and the closed set ℝ^m ∖ O, which are disjoint). Then 1_A and g agree on K (both 1) and off O (both 0) and differ by at most 1 on O ∖ K, so ∫|1_A − g| dL^m ≤ L^m(O ∖ K) < η. For |z| ≤ 1 and v ∈ B_R we have v, v − z ∈ B_{R+1}, so f(v − z) = 1_A(v − z) and f(v) = 1_A(v); by the triangle inequality and translation invariance of L^m, ∫_{B_R}|f(v − z) − f(v)| dv ≤ 2∫|1_A − g| dL^m + ∫_{B_R}|g(v − z) − g(v)| dv ≤ 2η + ∫_{B_R}|g(v − z) − g(v)| dv, and the last integral tends to 0 as z → 0 because g is uniformly continuous with compact support. Hence limsup_{ε→0}‖f_ε − f‖_{1,B_R} ≤ 2η for every η > 0.

3. (Gradient bound.) Let R > 0, i ≥ i_{R+2} and 0 < ε ≤ 1/2, and let Gr be the gradient of (u_i)_ε: the C^∞ vector field with Gr(v)·h = D(u_i)_ε(v)h for all h, i.e. Gr(v) := (InnerProductSpace.toDual ℝ (Euclid m)).symm(D(u_i)_ε(v)). Then ∫_{B_{R+1}}|Gr| ≤ c(R + 2). Proof: let ψ be a C^∞ vector field with tsupport ψ ⊆ closedBall(0, R + 1) and |ψ| ≤ 1. Integration by parts (ψ has compact support and (u_i)_ε is smooth) gives ∫Gr·ψ = −∫(u_i)_ε div ψ: for each coordinate j, ∫∂_j(u_i)_ε·ψ_j = −∫(u_i)_ε·∂_jψ_j by Fubini (integral_prod) and the one-dimensional formula integral_mul_deriv_eq_deriv_mul_of_integrable along the lines parallel to e_j, after transporting Euclid m to ℝ × ℝ^{m−1} (the j-th coordinate split off) by the measure-preserving maps PiLp.volume_preserving_ofLp and MeasureTheory.volume_preserving_piFinSuccAbove. By Fubini and evenness of ρ_ε, ∫(ρ_ε ⋆ u_i) div ψ = ∫u_i·(ρ_ε ⋆ div ψ), and ρ_ε ⋆ div ψ = div(ρ_ε ⋆ ψ): by HasCompactSupport.hasFDerivAt_convolution_right, D(ρ_ε ⋆ ψ)(v) = ∫ρ_ε(z)Dψ(v − z) dz (a convolution with values in linear maps), and the trace, a continuous linear map on this finite-dimensional space, commutes with the integral (ContinuousLinearMap.integral_comp_comm). The field ψ_ε := ρ_ε ⋆ ψ is C^∞ with compact support, |ψ_ε| ≤ ∫ρ_ε·|ψ| ≤ 1 and tsupport ψ_ε ⊆ tsupport ρ_ε + tsupport ψ ⊆ closedBall(0, ε) + closedBall(0, R + 1) = closedBall(0, R + 1 + ε) ⊆ B_{R+2} (support(ρ_ε ⋆ ψ) ⊆ support ρ_ε + support ψ by support_convolution_subset, and the sum of the two compact sets tsupport ρ_ε and tsupport ψ is compact, hence closed; ε ≤ 1/2); so −ψ_ε is admissible for radius R + 2 and ∫Gr·ψ = ∫_{F_i} div(−ψ_ε) ≤ c(R + 2). Now take ψ := χ_N·Gr/√(|Gr|² + θ²) with θ > 0, N ∈ ℕ, N ≥ 1, and χ_N(v) := smoothTransition(N((R + 1)² − |v|²)/(R + 1)²) (C^∞, 0 ≤ χ_N ≤ 1, χ_N = 0 outside B_{R+1}, so tsupport χ_N ⊆ closedBall(0, R + 1), and χ_N increases to 1 on B_{R+1} as N → ∞). It is of the above kind (C^∞, tsupport ψ ⊆ tsupport χ_N ⊆ closedBall(0, R + 1), |ψ| ≤ 1), so ∫χ_N|Gr|²/√(|Gr|² + θ²) ≤ c(R + 2). Letting θ ↓ 0 and then N → ∞ (monotone convergence: |Gr|²/√(|Gr|² + θ²) increases to |Gr| as θ decreases to 0, and χ_N increases to 1_{B_{R+1}}) gives ∫_{B_{R+1}}|Gr| ≤ c(R + 2).

4. (Translation estimate.) For R > 0, i ≥ i_{R+2} and h ∈ ℝ^m with |h| ≤ 1: ∫_{B_R}|u_i(v + h) − u_i(v)| dv ≤ c(R + 2)|h|. Proof: for 0 < ε ≤ 1/2, (u_i)_ε(v + h) − (u_i)_ε(v) = ∫_0^1 ∇(u_i)_ε(v + th)·h dt, so by Tonelli and translation invariance of L^m (B_R + th ⊆ B_{R+1}), ∫_{B_R}|(u_i)_ε(v + h) − (u_i)_ε(v)| dv ≤ |h|·∫_0^1∫_{B_{R+1}}|∇(u_i)_ε| dt ≤ c(R + 2)|h| by step 3. Moreover ∫_{B_R}|u_i(v + h) − (u_i)_ε(v + h)| dv ≤ ‖u_i − (u_i)_ε‖_{1,B_{R+1}} and ∫_{B_R}|(u_i)_ε − u_i| ≤ ‖(u_i)_ε − u_i‖_{1,B_{R+1}}; both tend to 0 as ε → 0 by step 2. The triangle inequality gives the claim.

5. (Cube averages.) Fix R ≥ 1 and δ ∈ (0, 1/√m]. Let 𝒬 = 𝒬(R, δ) be the finite family of half-open cubes Q = δ(z + [0, 1)^m), z ∈ ℤ^m, that meet B_R; they are pairwise disjoint, cover B_R, and lie in B_{R+1} (diam Q = √m·δ ≤ 1). For i ≥ i_{R+3} put a_{i,Q} := δ^{−m}∫_Q u_i ∈ [0, 1] and Au_i := Σ_{Q∈𝒬} a_{i,Q}·1_Q. For v ∈ Q, |u_i(v) − a_{i,Q}| ≤ δ^{−m}∫_Q|u_i(v) − u_i(v')| dv'. Substituting v' = v + h (h ∈ Q − v ⊆ closedBall(0, √mδ)) and using Tonelli and step 4 on B_{R+1}:
 ‖u_i − Au_i‖_{1,B_R} ≤ δ^{−m}Σ_Q∫_Q∫_Q|u_i(v) − u_i(v')| dv' dv ≤ δ^{−m}∫_{|h|≤√mδ}∫_{B_{R+1}}|u_i(v + h) − u_i(v)| dv dh ≤ δ^{−m}·L^m(closedBall(0, √mδ))·c(R + 3)√mδ = C_m·c(R + 3)·δ,
with C_m := L^m(closedBall(0, 1))·m^{(m+1)/2}.

6. (A subsequence that is Cauchy in every L¹(B_R).) Put δ_l := 1/(l√m) for l ≥ 1 and enumerate the countably many pairs (R, l) ∈ ℕ × ℕ with R, l ≥ 1. For each pair the finitely many averages (a_{i,Q})_{Q∈𝒬(R,δ_l)} lie in the compact cube [0, 1]^{𝒬(R,δ_l)}, so every subsequence has a further subsequence along which they converge (IsCompact.tendsto_subseq). A diagonal argument gives a strictly increasing σ₀ such that, for every pair (R, l), a_{σ₀(i),Q} converges as i → ∞ for every Q ∈ 𝒬(R, δ_l). (Equivalently, with a single extraction: the averages δ_l^{−m}∫_{δ_l(z+[0,1)^m)} u_i, indexed by the countable set of pairs (l, z) with l ≥ 1 and z ∈ ℤ^m, form a sequence in the compact metrizable product [0, 1]^{ℕ×ℤ^m} (isCompact_univ_pi), and IsCompact.tendsto_subseq gives σ₀ along which all of them converge.) Fix R ∈ ℕ, R ≥ 1. For every l and all large i, i':
 ‖u_{σ₀(i)} − u_{σ₀(i')}‖_{1,B_R} ≤ 2C_m·c(R + 3)·δ_l + Σ_{Q∈𝒬(R,δ_l)}|a_{σ₀(i),Q} − a_{σ₀(i'),Q}|·δ_l^m,
and the sum tends to 0 as i, i' → ∞. Hence limsup_{i,i'→∞}‖u_{σ₀(i)} − u_{σ₀(i')}‖_{1,B_R} ≤ 2C_m·c(R + 3)·δ_l for every l, so (u_{σ₀(i)}) is Cauchy in L¹(B_R) for every R ∈ ℕ.

7. (Almost everywhere convergence.) By step 6, choose inductively j_0 < j_1 < j_2 < … with ‖u_{σ₀(i)} − u_{σ₀(i')}‖_{1,B_{l+1}} ≤ 2^{−l} for all i, i' ≥ j_l, and put σ(l) := σ₀(j_l) for l ∈ ℕ, a strictly increasing map ℕ → ℕ. Fix R ∈ ℕ with R ≥ 1. For l ≥ R − 1 we have B_R ⊆ B_{l+1} and j_{l+1} > j_l, so ∫_{B_R}|u_{σ(l+1)} − u_{σ(l)}| ≤ 2^{−l}; each of the finitely many terms with l < R − 1 is at most L^m(B_R) < ∞. Hence Σ_l∫_{B_R}|u_{σ(l+1)} − u_{σ(l)}| < ∞, and by monotone convergence (lintegral_tsum) Σ_l|u_{σ(l+1)}(v) − u_{σ(l)}(v)| < ∞ for a.e. v ∈ B_R; as ℝ^m = ⋃_{R≥1}B_R, this holds for a.e. v ∈ ℝ^m. Since every u_{σ(l)}(v) is 0 or 1, every nonzero term of this series equals 1; so for a.e. v only finitely many terms are nonzero and the sequence (u_{σ(l)}(v))_l is eventually constant.

8. (The limit set.) Put F' := {v : v ∈ F_{σ(l)} for all large l} = ⋃_{l₀}⋂_{l≥l₀}F_{σ(l)}, a measurable set. At every v where (u_{σ(l)}(v)) is eventually constant, its eventual value is 1_{F'}(v). Hence u_{σ(l)} → 1_{F'} a.e., and |u_{σ(l)} − 1_{F'}| ≤ 1. For R > 0, dominated convergence on B_R (a set of finite measure) gives L^m((F_{σ(l)} Δ F') ∩ B_R) = ∫_{B_R}|u_{σ(l)} − 1_{F'}| dL^m → 0; for R ≤ 0, B_R = ∅. This proves the statement with σ and F'. ∎

## Key steps

1. Mollifier ρ := (∫b)^{−1}b from an even ContDiffBump b with radii 1/2 and 1 (tsupport ρ = closedBall(0, 1), so ρ_ε vanishes outside closedBall(0, ε)); mollified indicators satisfy ∫_{B_{R+1}}|∇(u_i)_ε| ≤ c(R + 2): integrate by parts and test the hypothesis with the mollified field ρ_ε ⋆ ψ, whose tsupport lies in closedBall(0, R + 1 + ε) ⊆ B_{R+2}.
2. Translation estimate ‖u_i(· + h) − u_i‖_{L¹(B_R)} ≤ c(R + 2)|h| (fundamental theorem of calculus for (u_i)_ε, then ε → 0 by L¹ convergence of mollifications).
3. Cube averages approximate u_i in L¹(B_R) up to C_m·c(R + 3)·δ; finitely many averages in [0, 1] have convergent subsequences, and a diagonal argument makes (u_{σ₀(i)}) Cauchy in every L¹(B_R).
4. A fast Cauchy subsequence converges a.e. and is eventually constant a.e.; F' := liminf F_{σ(l)} is measurable and dominated convergence gives L^m((F_{σ(l)} Δ F') ∩ B_R) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `cat decomposition-audit-v1.json decomposition-review-receipt-v1.json; python3 dump of decomposition-v1.json (12 subproblems: statements, lean_statements, natural proofs, key steps, dependencies)`
- `python3 scan of dag.json: lean_name lookup of the 8 codim1_zsl_* names, the 4 reused names (status, candidate commit, lean_statement byte equality with decomposition-v1.json), dtc_hausdorff_dilation, dor_ims_unitOrientation_dual and codim1_zero_scale_limit_offset_plane; raw count of 'codim1_zsl'; keyword scan 'area formula|BV|perimeter|bvVariation|indicator' over statements and titles`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl $r -- 'GMT/*.lean' (1277 commits); positive control: the same loop with dgcr_graph_orientation_jacobian; grep -rl codim1_zsl .lake/packages/simongmt/Poincare GMT`
- `grep -n 'def IsTestForm|def exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massOn|def zeroRegion|def support|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/*.lean, then sed of Forms.lean 25-135, Mass.lean 25-80, CurrentLocalEquality.lean 95-125, AffineCurrentPushforward.lean 30-50 and 145-160, Currents.lean 120-190`
- `rg -n 'theorem tsupport_eq|theorem support_eq|protected theorem neg|symmetric :' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'integral_comp_inv_smul_of_nonneg|support_convolution_subset|exists_isCompact_sdiff_lt|exists_isOpen_sdiff_lt|integral_pos_iff_support_of_nonneg|theorem lintegral_tsum' mathlib/Mathlib; rg -n 'namespace Module.Basis|def det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `lean -DautoImplicit=false /tmp/zsl-v2/Lib.lean and /tmp/zsl-v2/Lib2.lean (#check of about 70 Mathlib/SimonGMT lemmas cited by the children)`
- `lean -DautoImplicit=false /tmp/zsl-v2/Bump.lean (ρ := (∫b)⁻¹·b for b : ContDiffBump (0 : Euclid m) with radii 1/2, 1: ContDiff ℝ ⊤, ρ ≥ 0, ρ(−z) = ρ(z), tsupport ρ = closedBall 0 1, ∫ρ = 1)`
- `lean -DautoImplicit=false /tmp/zsl-v2/TypesV2.lean (12 child types generated from the v2 JSON plus the assembly of the selected type); lean -DautoImplicit=false /tmp/zsl-v2/AssemblyV2.lean (children as axioms, #print axioms)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-review-receipt-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/zsl-v2/Lib.lean`
- `/tmp/zsl-v2/Lib2.lean`
- `/tmp/zsl-v2/Bump.lean`
- `/tmp/zsl-v2/TypesV2.lean`
- `/tmp/zsl-v2/AssemblyV2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' with the handoff's exact frozen type.
- The 4 reused declarations are accepted with types byte-identical to v1: dtc_blowUp_testForm_corr (5e184fbc), setIntegral_blowUpMap_image_eq_inv_pow_mul (713eebc5), rsdic_unitOrientation_eq_or_eq_neg (fe95347b) and dgcr_graph_orientation_jacobian (62aa1f11).
- The 8 codim1_zsl_* names have 0 occurrences in dag.json, SimonGMT, GMT/ and the 1277 commits reachable from refs. The positive control dgcr_graph_orientation_jacobian was found on 6 of those commits.
- No accepted node gives an exact graph area formula or BV compactness. The only area-formula nodes are unaccepted (dpf_area_formula_bilipschitz_rectifiable, idtp_carrier_area_formula) and have other types.
Library.
- The SimonGMT definitions match the children's proofs: exteriorDerivative = extDeriv with the alternating-sum formula, IsTestForm = ContDiff ℝ ∞ ∧ HasCompactSupport, covectorEuclideanNorm, massOn/massAdmissibleOn, zeroRegion/support and affinePullbackForm.
- In the snapshot Mathlib, ContDiffBump.tsupport_eq (BumpFunction/Basic.lean:157) gives closedBall c rOut. This confirms the v1 defect, so step 1 of bv_compactness now claims only tsupport ρ = closedBall(0, 1). ContDiffBump.neg (:132) gives evenness, and support_eq (:151) gives the open-ball support.
- Every lemma cited by the corrected proofs exists in the import closure. Examples: integral_comp_inv_smul_of_nonneg (Haar/NormedSpace.lean:129), support_convolution_subset (Convolution.lean:670), MeasurableSet.exists_isCompact_sdiff_lt/exists_isOpen_sdiff_lt (Regular.lean:843/385), exists_continuous_one_zero_of_isCompact and Module.Basis.det (Determinant.lean:591; the old name Basis.det is fixed).
Lean.
- Bump.lean compiles the corrected mollifier.
- TypesV2.lean elaborates all 12 frozen types taken verbatim from the v2 JSON and proves the selected type; lean exits 0. Its axioms are propext, sorryAx, Classical.choice and Quot.sound.
- With the children as axioms, AssemblyV2.lean depends only on propext, Classical.choice, Quot.sound and the 4 direct children.
- leaf_verification.check_source_delta forbids new declarations and imports in leaf proofs, so the deep lemmas must stay separate children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
