<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.submanifold_subset_support-a1 -->

## Theorem `Submission.idtp_ccd_rps_submanifold_subset_support`

Let P, n ∈ ℕ, let U, G, M ⊆ ℝ^P be sets, T ∈ 𝒟_n(U) (T : GeometricCurrentOn U n), m ∈ ℤ and ξ : ℝ^P → Λ_n(ℝ^P) (MultiVector P n). Assume: G is open and G ⊆ U; m ≠ 0; M is an embedded C¹ n-dimensional submanifold (IsEmbeddedSubmanifold 1 n M); ξ is an orientation of M (IsOrientation n M ξ: ξ is continuous on M, and for every z ∈ M, ξ(z) is a unit orientation of the subspace tangentSpace M z); Hⁿ(M ∩ K) < ∞ for every compact K ⊆ G (Hⁿ := μHE[n]); and T(ω) = m·∫_M ξ(x)(ω(x)) dHⁿ(x) for every ω ∈ 𝒟ⁿ(U) (TestFormOn U n) with tsupport ω ⊆ G. Then M ∩ G ⊆ spt T, where spt T = T.support = U ∖ zeroRegion T (Simon 6.2.11).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.submanifold_subset_support-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5353

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4182, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1013

Decomposition children: None

## Lean problem

Declaration: `Submission.idtp_ccd_rps_submanifold_subset_support`

```lean
∀ (P n : ℕ) (U G M : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen G → G ⊆ U → m ≠ 0 → IsEmbeddedSubmanifold 1 n M → IsOrientation n M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ G → μHE[n] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → M ∩ G ⊆ T.support
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.submanifold_subset_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof of the selected node (M ∩ B_ρ(y) ⊆ spt T, the bump-form argument (a)–(g)). Here it is stated for an arbitrary open set G ⊆ U on which T = m[[M]], with both B_ρ(y) and B_{ρ₀}(y) of the supplied proof replaced by G. The supplied proof takes some facts from its steps 2–3; here they are obtained as follows. M is Borel by the sibling embedded_locally_closed. Hⁿ(M ∩ K) < ∞ for the compact ball K ⊆ G is a hypothesis. The integrand is integrable because it is bounded by ‖α‖ on a set of finite measure, so compactness of M ∩ K is not needed.
Conventions. Hⁿ := μHE[n], ω_n := unitBallVolume n, B_r(x) := ball x r. For T ∈ 𝒟_n(U), "T vanishes on W" means T(ω) = 0 for each ω ∈ 𝒟ⁿ(U) (TestFormOn U n) with tsupport ω ⊆ W. zeroRegion T is the union of the open sets W with closure(W) compact and closure(W) ⊆ U on which T vanishes, and spt T = T.support = U ∖ zeroRegion T (Simon 6.2.11). Λⁿ = Covector (Euclid P) n carries the operator norm of continuous alternating maps, and Λ_n = MultiVector P n = (Λⁿ →L[ℝ] ℝ) its operator norm, so |ξ(z)(β)| ≤ ‖ξ(z)‖·‖β‖.
0. (Facts about M and ξ.)
 (i) By the sibling embedded_locally_closed (Submission.dimred_rpd_embedded_locally_closed with r = 1, d = n), M is a measurable set.
 (ii) By IsOrientation n M ξ, ξ is continuous on M, and for every z ∈ M there is a subspace Q_z with IsUnitOrientationOf (ξ(z)) Q_z. So by the sibling unit_orientation_bounds (Submission.imsupp_unit_orientation_ne_zero_norm_le_one), ξ(z) ≠ 0 and ‖ξ(z)‖ ≤ 1 for every z ∈ M.
1. (Setting up the contradiction.) Let x ∈ M ∩ G. Then x ∈ U because G ⊆ U, so it remains to show x ∉ zeroRegion T. Suppose instead that x ∈ zeroRegion T. Then x ∈ W for some open set W (with closure(W) compact and contained in U) on which T vanishes.
2. (A covector α with ξ(x)(α) = 1.) By step 0(ii), ξ(x) ≠ 0, so there is α₀ ∈ Λⁿ with ξ(x)(α₀) ≠ 0; otherwise ξ(x) would be the zero functional. Put α := ξ(x)(α₀)⁻¹·α₀. By linearity, ξ(x)(α) = ξ(x)(α₀)⁻¹·ξ(x)(α₀) = 1.
3. (Continuity.) The function z ↦ ξ(z)(α) is continuous on M: ξ is continuous on M, and evaluating a continuous linear map at the fixed covector α is continuous (ContinuousOn.clm_apply with a constant). Since ξ(x)(α) = 1, there is ε₁ > 0 such that |ξ(z)(α) − 1| < 1/2, hence ξ(z)(α) > 1/2, for every z ∈ M with |z − x| < ε₁.
4. (Radius.) W ∩ G is open and contains x, so there is r > 0 with B_r(x) ⊆ W ∩ G. Put ε := min(r, ε₁) > 0. Then ε ≤ ε₁ and closedBall(x, ε/2) ⊆ B_ε(x) ⊆ B_r(x) ⊆ W ∩ G.
5. (The bump form.) Let g be Mathlib's smooth bump function centred at x with inner radius ε/4 and outer radius ε/2 (a ContDiffBump x with rIn = ε/4 and rOut = ε/2; note 0 < ε/4 < ε/2). It has these properties:
 - g is C^∞ and 0 ≤ g ≤ 1;
 - g = 1 on closedBall(x, ε/4) (one_of_mem_closedBall);
 - tsupport g = closedBall(x, ε/2) (tsupport_eq), so g(z) = 0 for z ∉ closedBall(x, ε/2);
 - g has compact support.
 Define the n-form ω(z) := g(z)·α. It is C^∞ as the product of the smooth function g and the constant α. It has compact support (HasCompactSupport.smul_right), and tsupport ω ⊆ tsupport g = closedBall(x, ε/2) (tsupport_smul_subset_left). Since closedBall(x, ε/2) ⊆ W ∩ G ⊆ U, we get ω ∈ 𝒟ⁿ(U), i.e. ω is a TestFormOn U n.
6. (T(ω) = 0.) tsupport ω ⊆ closedBall(x, ε/2) ⊆ W and T vanishes on W, so T(ω) = 0.
7. (T(ω) as an integral.) tsupport ω ⊆ closedBall(x, ε/2) ⊆ G, so the representation hypothesis gives T(ω) = m·∫_M h dHⁿ with h(z) := ξ(z)(ω(z)). By linearity of ξ(z), h(z) = ξ(z)(g(z)·α) = g(z)·ξ(z)(α).
8. (Properties of h.) Let μ := Hⁿ⌞M (μHE[n].restrict M) and K := closedBall(x, ε/2).
 (a) h is continuous on M, as the product of the continuous g and the function of step 3. Since M is measurable (step 0(i)), h is a.e.-strongly measurable for μ (ContinuousOn.aestronglyMeasurable).
 (b) h(z) = 0 for z ∉ K, because g(z) = 0 there.
 (c) For z ∈ M, |h(z)| = |g(z)|·|ξ(z)(α)| ≤ 1·‖ξ(z)‖·‖α‖ ≤ ‖α‖, using 0 ≤ g ≤ 1 and step 0(ii). Since μ-almost every point lies in M, |h| ≤ ‖α‖ μ-a.e.
 (d) K is compact and K ⊆ G, so Hⁿ(M ∩ K) < ∞ by hypothesis. Since K is measurable, μ(K) = Hⁿ(K ∩ M) < ∞.
 (e) (Integrability.) By (a), (c) and (d), h is integrable on K with respect to μ, being a bounded a.e.-strongly measurable function on a set of finite measure (Measure.integrableOn_of_bounded). By (b), h vanishes off K, so h is μ-integrable (IntegrableOn.integrable_of_forall_notMem_eq_zero).
 (f) (Nonnegativity.) h ≥ 0 μ-a.e. Let z ∈ M. If z ∈ K, then |z − x| ≤ ε/2 < ε ≤ ε₁, so ξ(z)(α) > 1/2 > 0 by step 3; with g(z) ≥ 0 this gives h(z) ≥ 0. If z ∉ K, then h(z) = 0 by (b).
 (g) (Where h is positive.) Let z ∈ M ∩ B_{ε/4}(x). Then z ∈ closedBall(x, ε/4), so g(z) = 1. Also |z − x| < ε/4 < ε₁, so h(z) = ξ(z)(α) > 1/2 > 0. Hence M ∩ B_{ε/4}(x) ⊆ {h ≠ 0} ∩ M.
9. (M has positive measure near x.) We claim Hⁿ(M ∩ B_{ε/4}(x)) > 0. Suppose instead that Hⁿ(M ∩ B_{ε/4}(x)) = 0. For every s ∈ (0, ε/4), monotonicity gives Hⁿ(M ∩ B_s(x)) = 0, so Hⁿ(M ∩ B_s(x))/(ω_n sⁿ) = 0, since in [0, ∞] zero divided by anything is zero. So this ratio is eventually 0 as s ↓ 0, and it tends to 0. But M is an embedded C¹ n-submanifold and x ∈ M, so by the sibling submanifold_density_one (Submission.dimred_rpd_submanifold_density_one) the same ratio tends to 1 as s ↓ 0. The filter s ↓ 0 (𝓝[>] 0) is nontrivial and limits in [0, ∞] are unique, so 1 = 0, which is absurd.
10. (The integral is positive.) For a μ-integrable function that is ≥ 0 μ-a.e., ∫ h dμ > 0 if and only if μ({h ≠ 0}) > 0 (integral_pos_iff_support_of_nonneg_ae, applicable by 8(e) and 8(f)). By 8(g), step 9 and Measure.le_restrict_apply, μ({h ≠ 0}) ≥ Hⁿ({h ≠ 0} ∩ M) ≥ Hⁿ(M ∩ B_{ε/4}(x)) > 0. Hence ∫_M h dHⁿ = ∫ h dμ > 0. This is the supplied proof's bound ∫_M h dHⁿ ≥ ∫_{M ∩ B_{ε/4}(x)} h dHⁿ ≥ ½·Hⁿ(M ∩ B_{ε/4}(x)) > 0, stated as a positivity criterion.
11. (Contradiction.) By steps 6 and 7, 0 = T(ω) = m·∫_M h dHⁿ. But m ≠ 0, so (m : ℝ) ≠ 0, and ∫_M h dHⁿ > 0 by step 10, so the product is nonzero. This contradiction shows x ∉ zeroRegion T, hence x ∈ U ∖ zeroRegion T = spt T. Since x ∈ M ∩ G was arbitrary, M ∩ G ⊆ spt T. ∎

Formalization notes:
- In the contract, IsTestForm ω is ContDiff ℝ ∞ ω ∧ HasCompactSupport ω, where ∞ is ((⊤ : ℕ∞) : WithTop ℕ∞). Write that exponent explicitly: under the contract's `open scoped ENNReal`, a bare ∞ elaborates as an element of ℝ≥0∞.
- x ∈ zeroRegion T unfolds by Set.mem_sUnion.1 to ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩.
- When naming the measure with set/let, ascribe its type, `set μ : Measure (Euclid P) := μHE[n]`; otherwise the BorelSpace instance problem is stuck.

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract `open`s (Filter Function Set MeasureTheory Metric; scoped ENNReal Topology; Poincare.SimonGMT.Chapter06; Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)), with the three sibling declarations above it. `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered proof step by step.

```lean
theorem Submission.idtp_ccd_rps_submanifold_subset_support : ∀ (P n : ℕ) (U G M : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen G → G ⊆ U → m ≠ 0 → IsEmbeddedSubmanifold 1 n M → IsOrientation n M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ G → μHE[n] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → M ∩ G ⊆ T.support := by
  intro P n U G M T m ξ hG hGU hm hM hξ hfin hrep x hx
  obtain ⟨hxM, hxG⟩ := hx
  refine ⟨hGU hxG, fun hxZ => ?_⟩
  obtain ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 n M hM).1
  -- (a) a covector α with ξ(x)(α) = 1, and the bound ‖ξ(z)‖ ≤ 1 on M
  obtain ⟨Qx, -, hQx⟩ := hξ.2 x hxM
  have hξx := (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n (ξ x) Qx hQx).1
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Covector (Euclid P) n, ξ x α₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hξx (ContinuousLinearMap.ext fun a => by simpa using h a)
  obtain ⟨α, hα⟩ : ∃ α : Covector (Euclid P) n, ξ x α = 1 :=
    ⟨(ξ x α₀)⁻¹ • α₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hα₀]⟩
  have hnorm : ∀ z ∈ M, ‖ξ z‖ ≤ 1 := by
    intro z hz
    obtain ⟨Q, -, hQ⟩ := hξ.2 z hz
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n (ξ z) Q hQ).2
  -- (b) continuity of z ↦ ξ(z)(α) on M at x
  have hcont : ContinuousOn (fun z => ξ z α) M := hξ.1.clm_apply continuousOn_const
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.continuousWithinAt_iff.1 (hcont x hxM) (1 / 2) (by norm_num)
  have hhalf : ∀ z ∈ M, dist z x < ε₁ → 1 / 2 < ξ z α := by
    intro z hz hzx
    have h := hε₁' hz hzx
    rw [Real.dist_eq, hα] at h
    linarith [(abs_lt.1 h).1]
  -- (c) the radius ε
  obtain ⟨r, hr, hrWG⟩ := Metric.isOpen_iff.1 (hWo.inter hG) x ⟨hxW, hxG⟩
  set ε := min r ε₁ with hεdef
  have hε : 0 < ε := lt_min hr hε₁
  have hεr : ε ≤ r := min_le_left _ _
  have hεε₁ : ε ≤ ε₁ := min_le_right _ _
  have hcb : closedBall x (ε / 2) ⊆ W ∩ G :=
    (closedBall_subset_ball (by linarith)).trans ((ball_subset_ball hεr).trans hrWG)
  -- (d) the bump form ω = g·α
  let g : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let ω : DifferentialForm (Euclid P) n := fun z => g z • α
  have hωsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := g.contDiff.smul contDiff_const
  have hωcpt : HasCompactSupport ω := g.hasCompactSupport.smul_right
  have hωts : tsupport ω ⊆ closedBall x (ε / 2) :=
    (tsupport_smul_subset_left (fun z => g z) (fun _ => α)).trans g.tsupport_eq.subset
  let ωU : TestFormOn U n :=
    ⟨ω, ⟨hωsmooth, hωcpt⟩, hωts.trans (hcb.trans fun z hz => hGU hz.2)⟩
  have hT0 : T ωU = 0 := hWv ωU (hωts.trans (hcb.trans inter_subset_left))
  have hTrep := hrep ωU (hωts.trans (hcb.trans inter_subset_right))
  -- (e) the integrand h(z) = g(z)·ξ(z)(α)
  have hval : ∀ z, ξ z ((ωU : DifferentialForm (Euclid P) n) z) = g z * ξ z α := by
    intro z
    show ξ z (g z • α) = g z * ξ z α
    rw [map_smul, smul_eq_mul]
  have hzero : ∀ z, z ∉ closedBall x (ε / 2) → g z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (by rw [g.tsupport_eq]; exact hz)
  set μ : Measure (Euclid P) := μHE[n] with hμdef
  set h : Euclid P → ℝ := fun z => ξ z ((ωU : DifferentialForm (Euclid P) n) z) with hhdef
  have hcontOn : ContinuousOn h M := by
    have : ContinuousOn (fun z => g z * ξ z α) M := g.continuous.continuousOn.mul hcont
    exact this.congr fun z _ => hval z
  have hmeas : AEStronglyMeasurable h (μ.restrict M) := hcontOn.aestronglyMeasurable hMmeas
  have hfinK : μ (M ∩ closedBall x (ε / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall _ _) (hcb.trans inter_subset_right)
  have hintK : IntegrableOn h (closedBall x (ε / 2)) (μ.restrict M) := by
    refine Measure.integrableOn_of_bounded (M := ‖α‖) ?_ hmeas ?_
    · rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact hfinK
    · have hM' : ∀ᵐ z ∂(μ.restrict M), z ∈ M := ae_restrict_mem hMmeas
      refine ae_restrict_of_ae ?_
      filter_upwards [hM'] with z hz
      rw [hhdef]
      dsimp only
      rw [hval z, norm_mul]
      have h1 : ‖g z‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (g.nonneg)]
        exact g.le_one
      have h2 : ‖ξ z α‖ ≤ ‖α‖ :=
        ((ξ z).le_opNorm α).trans (by nlinarith [hnorm z hz, norm_nonneg α])
      nlinarith [norm_nonneg (g z), norm_nonneg (ξ z α)]
  have hint : Integrable h (μ.restrict M) :=
    hintK.integrable_of_forall_notMem_eq_zero fun z hz => by
      rw [hhdef]; dsimp only; rw [hval z, hzero z hz, zero_mul]
  have hnonneg : 0 ≤ᵐ[μ.restrict M] h := by
    filter_upwards [ae_restrict_mem hMmeas] with z hz
    show (0 : ℝ) ≤ h z
    rw [hhdef]; dsimp only; rw [hval z]
    by_cases hzb : z ∈ closedBall x (ε / 2)
    · have : 1 / 2 < ξ z α := hhalf z hz (by
        rw [mem_closedBall] at hzb; linarith)
      exact mul_nonneg g.nonneg (by linarith)
    · rw [hzero z hzb, zero_mul]
  -- (f) positive measure of M near x
  have hpos : 0 < μ (M ∩ ball x (ε / 4)) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hlim := Submission.dimred_rpd_submanifold_density_one P n M x hM hxM
    have hev : (fun s : ℝ => μHE[n] (M ∩ ball x s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)))
        =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 4 by positivity)] with s hs
      have : μHE[n] (M ∩ ball x s) = 0 :=
        measure_mono_null (inter_subset_inter_right _ (ball_subset_ball hs.2.le)) h0
      rw [this, ENNReal.zero_div]
    exact one_ne_zero (tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds)
  have hsupp : μ (M ∩ ball x (ε / 4)) ≤ (μ.restrict M) (support h) := by
    refine le_trans (measure_mono ?_) (Measure.le_restrict_apply _ _)
    rintro z ⟨hzM, hzb⟩
    refine ⟨?_, hzM⟩
    rw [mem_support, hhdef]; dsimp only; rw [hval z]
    have hg1 : g z = 1 := g.one_of_mem_closedBall (ball_subset_closedBall hzb)
    have : 1 / 2 < ξ z α := hhalf z hzM (by rw [mem_ball] at hzb; linarith)
    rw [hg1, one_mul]
    linarith
  have hIpos : 0 < ∫ z in M, h z ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2 (hpos.trans_le hsupp)
  -- (g) contradiction
  rw [hTrep] at hT0
  exact mul_ne_zero (Int.cast_ne_zero.2 hm) hIpos.ne' hT0
```

## Key steps

1. M is Borel (embedded_locally_closed), and ξ(z) ≠ 0 with ‖ξ(z)‖ ≤ 1 on M (unit_orientation_bounds). Pick α with ξ(x)(α) = 1, and ε₁ > 0 with ξ(z)(α) > 1/2 on M ∩ B_{ε₁}(x), by continuity of ξ on M.
2. If x ∈ zeroRegion T through an open W, take ε ≤ ε₁ with B_ε(x) ⊆ W ∩ G. The bump form ω = g·α, with g = 1 on closedBall(x, ε/4) and tsupport g = closedBall(x, ε/2), is a test form supported in W, so T(ω) = 0.
3. T(ω) = m·∫_M g·ξ(α) dHⁿ. The integrand is bounded by ‖α‖, measurable on M, vanishes off closedBall(x, ε/2), which has finite Hⁿ⌞M measure, is ≥ 0 on M, and is > 1/2 on M ∩ B_{ε/4}(x).
4. Hⁿ(M ∩ B_{ε/4}(x)) > 0 because the density ratio of M at x tends to 1 (submanifold_density_one). So ∫_M g·ξ(α) dHⁿ > 0 and T(ω) ≠ 0, since m ≠ 0, a contradiction. Hence x ∈ spt T.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (checked against manifest.json)`
- `grep -n 'def zeroRegion|def support|def VanishesOn|theorem|lemma' SimonGMT Chapter06/CurrentLocalEquality.lean; sed -n 80,200p Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn); sed -n 20,80p Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm); sed -n 1,100p Chapter06/Mass.lean (massAdmissibleOn, massOn)`
- `python3 -I scans of dag.json: nodes under cone_constant_density_planar-a1; lean_statements with IsEmbeddedSubmanifold plus MeasurableSet/IsCompact/closure; accepted lemmas whose statements mention support together with VanishesOn/zeroRegion/massOn; statements with IsOrientation or 'closure M' together with .support; local representations 'T ω = _ * ∫ x in M'; records (status, candidate, depends_on) of dimred_rpd_embedded_locally_closed, dimred_rpd_submanifold_density_one, imsupp_unit_orientation_ne_zero_norm_le_one, dimred_rpd_massOn_eq_mult_measure, dimred_regular_point_density`
- `git show 1d91497901e9a040bb92dab7cea2968379e0e3a2:GMT/Ch07/Submission.lean (parent proof base = bare contract); git show {6da66b1e,e8842d90,2e5d20d4,5fcaddaa}:GMT/Ch07/Submission.lean | grep '^theorem Submission.' (accepted candidates contain only their declared dependencies)`
- `scan of nodes/*/parent-child-handoff.json resolved_dependencies (385 non-empty, including cross-branch); nodes/root-dimension-reduction-results-a1-regular-point-density-a1/decomposition-v1.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json (precedent for reusing accepted declarations, with 'Reuse note' natural proofs)`
- `grep -c idtp_ccd_rps dag.json; grep -rl idtp_ccd_rps nodes/ ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission/ (no match)`
- `grep -rn 'theorem integral_pos_iff_support_of_nonneg_ae|setIntegral_eq_zero_of_forall_eq_zero|integrableOn_of_bounded|integrable_of_forall_notMem_eq_zero|ContinuousOn.aestronglyMeasurable|le_restrict_apply|IsOpen.inter_closure|tsupport_smul_subset_left|ContinuousOn.clm_apply' <snapshot>/mathlib/Mathlib; grep -n 'tsupport_eq|one_of_mem_closedBall|nonneg|le_one|hasCompactSupport|contDiff' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `sed -n 290,310p book/chapter-06.txt (Simon 6.2.11-2.12); sed -n 586,600p book/chapter-07.txt (Simon 7.4.1)`
- `lake env lean /tmp/rps-decomp-4RlzzQ/{Probe,Assembly,C1,C2,Full,FromJson}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b656aa468/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b656aa468/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-2d6f974584/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1-f90e8352bc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rps-decomp-4RlzzQ/Assembly.lean`
- `/tmp/rps-decomp-4RlzzQ/C1.lean`
- `/tmp/rps-decomp-4RlzzQ/C2.lean`
- `/tmp/rps-decomp-4RlzzQ/Full.lean`
- `/tmp/rps-decomp-4RlzzQ/FromJson.lean`

Pins match the manifest. The snapshot project commit equals workspace HEAD b4d606d, Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT definitions match the supplied proof: T.support = U ∖ zeroRegion T, where zeroRegion T is the union of the open W with compact closure inside U on which T.VanishesOn W holds. TestFormOn U n is {ω | ContDiff ℝ ∞ ω ∧ HasCompactSupport ω ∧ tsupport ω ⊆ U}.

The selected node cannot reach the lemmas its proof cites. Its proof cites the accepted Submission.imsupp_unit_orientation_ne_zero_norm_le_one (candidate 2e5d20d4) and Submission.dimred_rpd_submanifold_density_one (e8842d90). Its step 2 is the accepted Submission.dimred_rpd_embedded_locally_closed (6da66b1e). Yet the node has no declared dependencies, and its proof base 1d91497 is the bare contract. Accepted candidates contain only their declared dependencies, and the DAG precedent reuses accepted declarations as children at identical frozen types. Hence the three reuse children; their lean_statements are byte-identical to dag.json.

No accepted or pending lemma states either support inclusion. The names idtp_ccd_rps_* have no match in dag.json, nodes/ or any worktree Submission.

Mathlib 25730c7c provides every lemma used by the new children's proofs: ContDiffBump (tsupport_eq, one_of_mem_closedBall, nonneg, le_one, contDiff, hasCompactSupport), setIntegral_eq_zero_of_forall_eq_zero, Measure.integrableOn_of_bounded, IntegrableOn.integrable_of_forall_notMem_eq_zero, ContinuousOn.aestronglyMeasurable, integral_pos_iff_support_of_nonneg_ae, Measure.le_restrict_apply, IsOpen.inter_closure and ContinuousOn.clm_apply.

Lean check: all child types elaborate. The assembly proves the frozen parent type from the children. Both new children are fully proved. FromJson.lean, built from this JSON plus the accepted reused proofs, proves Submission.idtp_ccd_regular_point_support with no sorry and axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
