<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.graph_chart-a1 -->

## Theorem `Submission.codim1_hcp_lsa_c1_graph_chart`

Let P, m ∈ ℕ, let M ⊆ ℝ^P be an embedded C¹ m-dimensional submanifold (IsEmbeddedSubmanifold 1 m M) and let p ∈ M. Then there are a continuous linear map pr : ℝ^P → ℝ^m with ‖pr‖ ≤ 1, a map G : ℝ^m → ℝ^P, a radius r > 0, an open set W ⊆ ℝ^P with p ∈ W, and a constant Λ ≥ 0 such that: G(0) = p; G is C¹ and Λ-Lipschitz on the open ball B_r(0) ⊆ ℝ^m; M ∩ W = G(B_r(0)); and for every a ∈ B_r(0), pr(G(a) − p) = a, pr∘DG(a) = id_{ℝ^m}, and tangentSpace M (G(a)) = range DG(a), where DG = fderiv ℝ G.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.graph_chart-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6001

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5477, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2535

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_hcp_lsa_c1_graph_chart`

```lean
∀ (P m : ℕ) (M : Set (Euclid P)) (p : Euclid P), IsEmbeddedSubmanifold 1 m M → p ∈ M → ∃ (pr : Euclid P →L[ℝ] Euclid m) (G : Euclid m → Euclid P) (r : ℝ) (W : Set (Euclid P)) (Λ : NNReal), 0 < r ∧ IsOpen W ∧ p ∈ W ∧ ‖pr‖ ≤ 1 ∧ G 0 = p ∧ ContDiffOn ℝ 1 G (ball 0 r) ∧ LipschitzOnWith Λ G (ball 0 r) ∧ M ∩ W = G '' ball 0 r ∧ (∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a) ∧ (∀ a ∈ ball (0 : Euclid m) r, pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m)) ∧ ∀ a ∈ ball (0 : Euclid m) r, tangentSpace M (G a) = Set.range (fderiv ℝ G a)
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.graph_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the parent proof ("Graph charts", items (1a)–(1b)): Simon Ch. 2, 4.4 (graph representation of an embedded C¹ submanifold over its tangent plane by the inverse function theorem). Sibling children used: chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv), local_inverse (Submission.codim1_zsl_gc_local_inverse), chart_inverse_continuity (Submission.dsmc_chart_inverse_continuity). The parent's projection π_p = ι_p* (ι_p an isometry onto T_p) is replaced by pr := ‖A‖⁻¹A*, A = Dψ(v₀); all that is used is ‖pr‖ ≤ 1 and that pr∘Dψ(v₀) is invertible.

Notation. B_s(a) is the open ball, B̄_s(a) the closed ball; A* is the adjoint (ContinuousLinearMap.adjoint); 0⁻¹ := 0.

1. (Chart at p.) By IsEmbeddedSubmanifold 1 m M at p there are open V ⊆ ℝ^m, open W₀ ⊆ ℝ^P with p ∈ W₀ and ψ : ℝ^m → ℝ^P that is C¹ on V, injective on V, with ψ(V) = W₀ ∩ M, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W₀, and Dψ(z) injective for z ∈ V. Since p ∈ W₀ ∩ M = ψ(V) choose v₀ ∈ V with ψ(v₀) = p. As V is open and ψ is C¹ on V, ψ has derivative Dψ(v) = fderiv ℝ ψ v at every v ∈ V.
2. (The projection pr.) Put A := Dψ(v₀) and pr := ‖A‖⁻¹·A* : ℝ^P → ℝ^m. Since ‖A*‖ = ‖A‖ (the adjoint is an isometry), ‖pr‖ = ‖A‖⁻¹‖A‖ ≤ 1 (it is 0 if A = 0 and 1 otherwise). pr∘A is injective: let pr(Ah) = 0. If ‖A‖ = 0 then A = 0, so Ah = A0 and h = 0 by injectivity of A. Otherwise A*(Ah) = 0, hence ‖Ah‖² = ⟨A*Ah, h⟩ = 0, so Ah = 0 = A0 and h = 0.
3. (Inverse function theorem.) Let Φ(v) := pr(ψ(v) − p). Φ is C¹ on V with derivative DΦ(v) = pr∘Dψ(v) at v ∈ V (chain rule), and DΦ(v₀) = pr∘A is injective by step 2. Child local_inverse (d = m, φ = Φ, z₀ = v₀) gives open sets V₀, O ⊆ ℝ^m and χ : ℝ^m → ℝ^m with v₀ ∈ V₀ ⊆ V, χ C¹ on O, χ(O) ⊆ V₀, Φ(χ(a)) = a for a ∈ O, and Φ(z) ∈ O, χ(Φ(z)) = z for z ∈ V₀. Since Φ(v₀) = pr(0) = 0 we get 0 ∈ O and χ(0) = v₀.
4. (Embedding margin.) Choose ε > 0 with B_ε(v₀) ⊆ V₀ (V₀ open). ψ is continuous and injective on V, ψ(V) ⊆ W₀, and proper in the above sense, so child chart_inverse_continuity (at v₀ with this ε) gives δ > 0 such that every v' ∈ V with |ψ(v') − p| < δ satisfies |v' − v₀| < ε, hence v' ∈ V₀.
5. (The graph map and the radius.) Put G := ψ∘χ. Then G(0) = ψ(v₀) = p, and G is C¹ on O (χ is C¹ on O and maps O into V₀ ⊆ V, where ψ is C¹). Choose r₁ > 0 with B_{r₁}(0) ⊆ O, and r₂ > 0 with G(B_{r₂}(0)) ⊆ B_δ(p) (G is continuous at 0 ∈ O and G(0) = p). Put r := min(r₁/2, r₂) > 0. Then B̄_r(0) ⊆ B_{r₁}(0) ⊆ O, so G is C¹ on B_r(0). DG is continuous on the open set O, hence bounded, say ‖DG‖ ≤ C_b, on the compact set B̄_r(0); by the mean value inequality on the convex set B_r(0) (Convex.lipschitzOnWith_of_nnnorm_fderiv_le), G is Λ-Lipschitz on B_r(0) with Λ := max(C_b, 0).
6. (The chart domain.) W := W₀ ∩ B_δ(p) ∩ {z : pr(z − p) ∈ B_r(0)} is open (the last set is the preimage of an open ball under a continuous affine map) and contains p (pr(p − p) = 0).
7. (Left inverse.) For a ∈ B_r(0) ⊆ O: pr(G(a) − p) = Φ(χ(a)) = a.
8. (M ∩ W = G(B_r(0)).) (⊆) Let x ∈ M ∩ W. Then x ∈ W₀ ∩ M = ψ(V), x = ψ(v') with v' ∈ V, and |ψ(v') − p| < δ, so v' ∈ V₀ by step 4 and χ(Φ(v')) = v'. Put a := Φ(v') = pr(x − p); a ∈ B_r(0) because x ∈ W, and G(a) = ψ(χ(Φ(v'))) = ψ(v') = x. (⊇) Let a ∈ B_r(0). Then χ(a) ∈ V₀ ⊆ V, so G(a) = ψ(χ(a)) ∈ ψ(V) = W₀ ∩ M; G(a) ∈ B_δ(p) because r ≤ r₂; and pr(G(a) − p) = a ∈ B_r(0) by step 7. Hence G(a) ∈ M ∩ W.
9. (pr∘DG(a) = id.) Let a ∈ B_r(0). The map b ↦ pr(G(b) − p) agrees with the identity on the open ball B_r(0) (step 7), so its derivative at a is id; by the chain rule this derivative is pr∘DG(a).
10. (Tangent spaces.) Let a ∈ B_r(0) and u := χ(a) ∈ V. By the chain rule DG(a) = Dψ(u)∘Dχ(a). Differentiating Φ∘χ = id on the open set O ∋ a gives DΦ(u)∘Dχ(a) = id, so Dχ(a) is injective, hence surjective (a linear endomorphism of ℝ^m). Therefore range DG(a) = range Dψ(u). Child chart_tangent_space (with r = 1, the chart (V, W₀, ψ) of step 1 and v = u ∈ V) gives T_{ψ(u)}M = range Dψ(u). As G(a) = ψ(u), tangentSpace M (G a) = range DG(a).
11. (Conclusion.) pr, G, r, W, Λ satisfy: r > 0, W open, p ∈ W, ‖pr‖ ≤ 1 (step 2), G(0) = p, G C¹ and Λ-Lipschitz on B_r(0) (step 5), M ∩ W = G(B_r(0)) (step 8), pr(G(a) − p) = a and pr∘DG(a) = id on B_r(0) (steps 7, 9), and tangentSpace M (G a) = range DG(a) on B_r(0) (step 10). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_c1_graph_chart : <exactly the frozen lean_statement> := by`, placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c, with the three sibling declarations present with their frozen types; #print axioms: propext, Classical.choice, Quot.sound and those three siblings.
```lean
  intro P m M p hM hp
  obtain ⟨V, W₀, ψ, hVo, hW₀o, hpW₀, hψc, hψinj, hψV, hproper, hDψinj⟩ := hM p hp
  obtain ⟨v₀, hv₀, hψv₀⟩ : p ∈ ψ '' V := by rw [hψV]; exact ⟨hpW₀, hp⟩
  have hψd : ∀ v ∈ V, HasFDerivAt ψ (fderiv ℝ ψ v) v := fun v hv =>
    ((hψc.contDiffAt (hVo.mem_nhds hv)).differentiableAt one_ne_zero).hasFDerivAt
  -- the projection `pr = ‖A‖⁻¹ • Aᴴ`, `A = Dψ(v₀)`
  set A : Euclid m →L[ℝ] Euclid P := fderiv ℝ ψ v₀ with hA
  set pr : Euclid P →L[ℝ] Euclid m := ‖A‖⁻¹ • ContinuousLinearMap.adjoint A with hprdef
  have hpr : ‖pr‖ ≤ 1 := by
    rw [hprdef, norm_smul, LinearIsometryEquiv.norm_map, norm_inv, norm_norm]
    rcases eq_or_ne ‖A‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hprA : Function.Injective (pr.comp A) := by
    refine (injective_iff_map_eq_zero (pr.comp A)).2 fun h hh => ?_
    have hh' : pr (A h) = 0 := hh
    rcases eq_or_ne ‖A‖ 0 with h0 | h0
    · have hA0 : A = 0 := norm_eq_zero.1 h0
      apply hDψinj v₀ hv₀
      rw [← hA, hA0, map_zero]; rfl
    · have h1 : ContinuousLinearMap.adjoint A (A h) = 0 := by
        have : ‖A‖⁻¹ • ContinuousLinearMap.adjoint A (A h) = 0 := hh'
        exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero h0)
      have h2 : ‖A h‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_left]
      have h3 : A h = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      exact hDψinj v₀ hv₀ (by rw [← hA, h3, map_zero])
  -- the coordinate map `Φ = pr (ψ - p)` and its local inverse `χ`
  set Φ : Euclid m → Euclid m := fun v => pr (ψ v - p) with hΦ
  have hΦc : ContDiffOn ℝ 1 Φ V := pr.contDiff.comp_contDiffOn (hψc.sub contDiffOn_const)
  have hΦd : ∀ v ∈ V, HasFDerivAt Φ (pr.comp (fderiv ℝ ψ v)) v := fun v hv =>
    pr.hasFDerivAt.comp v ((hψd v hv).sub_const p)
  have hΦinj : Function.Injective (fderiv ℝ Φ v₀) := by rw [(hΦd v₀ hv₀).fderiv]; exact hprA
  obtain ⟨V₀, O, χ, hV₀o, hOo, hv₀V₀, hV₀V, hχc, hχmaps, hΦχ, hχΦ⟩ :=
    Submission.codim1_zsl_gc_local_inverse m Φ V v₀ hVo hv₀ hΦc hΦinj
  obtain ⟨ε, hε, hεV₀⟩ := Metric.isOpen_iff.1 hV₀o v₀ hv₀V₀
  obtain ⟨δ, hδ, hδε⟩ := Submission.dsmc_chart_inverse_continuity P m V W₀ ψ hψc.continuousOn hψinj
    (by rw [hψV]; exact inter_subset_left) hproper v₀ hv₀ ε hε
  have hΦv₀ : Φ v₀ = 0 := by simp [hΦ, hψv₀]
  have h0O : (0 : Euclid m) ∈ O := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).1
  have hχ0 : χ 0 = v₀ := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).2
  -- the graph map `G = ψ ∘ χ`
  set G : Euclid m → Euclid P := fun a => ψ (χ a) with hGdef
  have hG0 : G 0 = p := by simp [hGdef, hχ0, hψv₀]
  have hGc : ContDiffOn ℝ 1 G O := hψc.comp hχc fun a ha => hV₀V (hχmaps ha)
  obtain ⟨r₁, hr₁, hr₁O⟩ := Metric.isOpen_iff.1 hOo 0 h0O
  have hGcont0 : ContinuousAt G 0 := hGc.continuousOn.continuousAt (hOo.mem_nhds h0O)
  obtain ⟨r₂, hr₂, hr₂δ⟩ := Metric.mem_nhds_iff.1
    (hGcont0.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds p hδ))
  set r : ℝ := min (r₁ / 2) r₂ with hr
  have hrpos : 0 < r := lt_min (by positivity) hr₂
  have hcbO : closedBall (0 : Euclid m) r ⊆ O :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hr₁O
  have hbO : ball (0 : Euclid m) r ⊆ O := ball_subset_closedBall.trans hcbO
  have hbδ : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ ball p δ := fun a ha =>
    hr₂δ (ball_subset_ball (min_le_right _ _) ha)
  -- Lipschitz bound on the ball
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : Euclid m) r).exists_bound_of_continuousOn
    ((hGc.continuousOn_fderiv_of_isOpen hOo le_rfl).mono hcbO)
  have hGda : ∀ a ∈ O, HasFDerivAt G (fderiv ℝ G a) a := fun a ha =>
    ((hGc.contDiffAt (hOo.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
  have hGL : LipschitzOnWith (Real.toNNReal Cb) G (ball 0 r) := by
    refine (convex_ball (0 : Euclid m) r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun a ha => (hGda a (hbO ha)).differentiableAt) fun a ha => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hCb a (ball_subset_closedBall ha)).trans (Real.le_coe_toNNReal Cb)
  -- the chart domain `W`
  set W : Set (Euclid P) := W₀ ∩ ball p δ ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r with hW
  have hWo : IsOpen W := (hW₀o.inter isOpen_ball).inter (isOpen_ball.preimage (by fun_prop))
  have hpW : p ∈ W := ⟨⟨hpW₀, mem_ball_self hδ⟩, by simp [hrpos]⟩
  have hleft : ∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a := fun a ha => hΦχ a (hbO ha)
  have hMW : M ∩ W = G '' ball 0 r := by
    ext x
    constructor
    · rintro ⟨hxM, ⟨hxW₀, hxδ⟩, hxr⟩
      obtain ⟨v', hv', rfl⟩ : x ∈ ψ '' V := by rw [hψV]; exact ⟨hxW₀, hxM⟩
      have hv'ε : dist v' v₀ < ε := hδε v' hv' (by rw [hψv₀]; exact hxδ)
      have hv'V₀ : v' ∈ V₀ := hεV₀ hv'ε
      refine ⟨Φ v', hxr, ?_⟩
      show ψ (χ (Φ v')) = ψ v'
      rw [(hχΦ v' hv'V₀).2]
    · rintro ⟨a, ha, rfl⟩
      have hχV : χ a ∈ V := hV₀V (hχmaps (hbO ha))
      have hGa : G a ∈ W₀ ∩ M := by rw [← hψV]; exact mem_image_of_mem ψ hχV
      refine ⟨hGa.2, ⟨hGa.1, hbδ a ha⟩, ?_⟩
      show pr (G a - p) ∈ ball 0 r
      rw [hleft a ha]; exact ha
  -- `pr ∘ DG(a) = id`
  have hderiv : ∀ a ∈ ball (0 : Euclid m) r, pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m) := by
    intro a ha
    have h1 : HasFDerivAt (fun b => pr (G b - p)) (pr.comp (fderiv ℝ G a)) a :=
      pr.hasFDerivAt.comp a ((hGda a (hbO ha)).sub_const p)
    have h2 : (fun b => pr (G b - p)) =ᶠ[𝓝 a] fun b => b := by
      filter_upwards [isOpen_ball.mem_nhds ha] with b hb using hleft b hb
    rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
  -- tangent spaces
  have htan : ∀ a ∈ ball (0 : Euclid m) r, tangentSpace M (G a) = Set.range (fderiv ℝ G a) := by
    intro a ha
    have haO : a ∈ O := hbO ha
    have hχV : χ a ∈ V := hV₀V (hχmaps haO)
    have hχd : HasFDerivAt χ (fderiv ℝ χ a) a :=
      ((hχc.contDiffAt (hOo.mem_nhds haO)).differentiableAt one_ne_zero).hasFDerivAt
    have hGfd : fderiv ℝ G a = (fderiv ℝ ψ (χ a)).comp (fderiv ℝ χ a) :=
      ((hψd (χ a) hχV).comp a hχd).fderiv
    -- `Dχ(a)` is surjective
    have hsurj : Function.Surjective (fderiv ℝ χ a) := by
      have hid : (fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a) = ContinuousLinearMap.id ℝ (Euclid m) := by
        have h1 : HasFDerivAt (fun b => Φ (χ b)) ((fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a)) a :=
          (hΦd (χ a) hχV).differentiableAt.hasFDerivAt.comp a hχd
        have h2 : (fun b => Φ (χ b)) =ᶠ[𝓝 a] fun b => b := by
          filter_upwards [hOo.mem_nhds haO] with b hb using hΦχ b hb
        rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
      have hinj : Function.Injective (fderiv ℝ χ a) := by
        intro u v huv
        have := congrArg (fderiv ℝ Φ (χ a)) huv
        have hu := congrArg (fun L => L u) hid
        have hv := congrArg (fun L => L v) hid
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
        rw [← hu, ← hv]; exact this
      exact (LinearMap.injective_iff_surjective (f := ((fderiv ℝ χ a : Euclid m →L[ℝ] Euclid m) :
        Euclid m →ₗ[ℝ] Euclid m))).1 hinj
    rw [show G a = ψ (χ a) from rfl, Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W₀ V ψ (χ a)
      le_rfl hVo hW₀o hψc hψinj hψV hproper hDψinj hχV, hGfd, ContinuousLinearMap.coe_comp,
      hsurj.range_comp]
  exact ⟨pr, G, r, W, Real.toNNReal Cb, hrpos, hWo, hpW, hpr, hG0, hGc.mono hbO, hGL, hMW, hleft,
    hderiv, htan⟩
```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. Take a chart ψ at p = ψ(v₀) and pr := ‖Dψ(v₀)‖⁻¹·Dψ(v₀)*. Then ‖pr‖ ≤ 1 and pr∘Dψ(v₀) is injective.
2. The inverse function theorem (local_inverse) applied to Φ = pr(ψ − p) gives a C¹ local inverse χ near 0. Put G := ψ∘χ, so pr(G(a) − p) = a.
3. chart_inverse_continuity and a small radius give M ∩ W = G(B_r(0)) for W := W₀ ∩ B_δ(p) ∩ {z : pr(z − p) ∈ B_r(0)}. DG is bounded on B̄_r(0), which gives the Lipschitz bound.
4. Differentiating pr(G(a) − p) = a gives pr∘DG(a) = id. Since Dχ(a) is invertible, range DG(a) = range Dψ(χ(a)) = T_{G(a)}M by chart_tangent_space.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE usage)`
- `python3 scans of dag.json: selected node (depth 5, max_depth 6), parent hypercone_plane and its decomposition-v1.json, accepted nodes whose statements mention Lipschitz/mollif/convol/graph chart/starProjection/tangentSpace, lean_name collision scan for codim1_hcp_lsa_*`
- `runtime.py: _decompose (max_depth), _existing_lean_name_problem (reuse of accepted declarations by identical name and type)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 93f7ea7a3650 (codim1_rdo_gc_local_inverse_c2, dsmc_chart_inverse_continuity), d25d2377 (codim1_zsl_pc_mollify_indicator_l1), and the handoffs of codim1_zsl_gc_local_inverse and dsmc_chart_inverse_continuity`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt, measurable_fderiv, tangentConeAt, HasFDerivWithinAt.unique_on, mem_tangentConeAt_of_seq, hasFDerivAt_convolution_left, contDiff_convolution_left, ae_convolution_tendsto_right_of_locallyIntegrable, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, LocallyLipschitzOn.mul, exists_isSubordinate, exists_contDiff_support_eq_eq_one_iff, sq_sum_le_card_mul_sum_sq, measurePreserving_sub_left`
- `lean #check probes in the GMT.Ch07.Submission import closure (Imp*.lean, Inst5.lean): SmoothPartitionOfUnity.exists_isSubordinate, ContDiffBump API, ContDiffBump.normed (missing), VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, tendsto_integral_smul_of_tendsto_average_norm_sub, aestronglyMeasurable_iUnion_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, NormedRing.inverse_continuousAt, instances HasContDiffBump/HasBesicovitchCovering (Euclid m)`
- `lean -DautoImplicit=false /tmp/lsa-split/check/{TypesAll,Assembly,N1,N2,N3,N4,N5,N6,N7,N8,Integration}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `git for-each-ref | xargs git grep -l codim1_hcp_lsa -- 'GMT/*.lean' (no match); grep codim1_hcp_lsa dag.json (0); grep -rn codim1_hcp_lsa simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/tmp/lsa-split/check/TypesAll.lean`
- `/tmp/lsa-split/check/Assembly.lean`
- `/tmp/lsa-split/check/Integration.lean`

Pins match: manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). The node has depth 5 with max_depth 6, so the children are leaves. Reuse: four accepted declarations (chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_zsl_gc_local_inverse, dsmc_chart_inverse_continuity) are taken with byte-identical frozen types. The C² graph-chart and tangent-projection lemmas (codim1_rdo_gc_graph_over_tangent, submanifold_tangentProjection_c1_extension, dor_lmb_ret_tangent_projection) do not apply to C¹ M. No C¹ graph chart, Rademacher-on-M, tangent-projection continuity or L²-gradient mollification lemma exists in the DAG, SimonGMT or the snapshot, and the 8 codim1_hcp_lsa_ names are unused everywhere. Mathlib in the Submission import closure provides Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), measurable_fderiv, HasFDerivWithinAt.unique_on with mem_tangentConeAt_of_seq, LipschitzOnWith.hausdorffMeasure_image_le with EuclideanSpace.euclideanHausdorffMeasure_eq_volume, convolution smoothness, ContDiffBump, Besicovitch Lebesgue differentiation, SmoothPartitionOfUnity and exists_contDiff_support_eq_eq_one_iff. It lacks ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and sq_sum_le_card_mul_sum_sq; the mollify proof rebuilds the first two by hand, and the assembly uses Finset.sum_mul_sq_le_sq_mul_sq. Lean: all 12 child types elaborate. The selected type is kernel-checked from the child types as axioms. Every new child is proved from exactly its declared siblings. The integrated file (8 proofs plus assembly, only the 4 reused declarations as axioms) compiles without errors or sorry.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
