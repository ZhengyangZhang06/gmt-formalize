<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1 -->

## Theorem `Submission.idtp_cse_edge_tangent_plane`

Let P ∈ ℕ and C ∈ 𝒟_2(ℝ^P) be minimizing in ℝ^P (IsMinimizingIn C univ), with ∂C = 0 and a cone (IsConeCurrent C). Let Q be a 2-dimensional linear subspace of ℝ^P, a, e ∈ Q with |a| = |e| = 1 and ⟨a, e⟩ = 0, δ > 0 and k ∈ ℕ with k ≥ 1. Assume a ∈ spt C and that for all t > 0 and φ ∈ (0, δ) the point y := t(cos φ·a + sin φ·e) satisfies HasMassDensity C y k and spt C ∩ B_r(y) ⊆ Q for some r > 0. Then there is m ∈ ℕ with m ≥ 1 and HasMassDensity C a m such that: (1) for every sequence λ_j > 0 with λ_j → 0 there are a strictly increasing φ : ℕ → ℕ, C' ∈ 𝒟_2(ℝ^P) and c ∈ ℤ with |c| = m such that blowUp C a λ_{φ(j)} ⇀ C' (ConvergesWeakly), C'(ω) = c·∫_Q ω(x)(a, e) dH²(x) for every ω ∈ 𝒟²(ℝ^P) (H² = μHE[2], ω(x)(a, e) = ω(x) applied to ![a, e]), and, for every integer multiplicity representation R of C and every continuous compactly supported g : ℝ^P → ℝ, λ_{φ(j)}^{−2}·∫ g(η_j(x)) dR.measure(x) → m·∫_Q g dH², where η_j := dilation a λ_{φ(j)} (η_j(x) = λ_{φ(j)}^{−1}(x − a)); and (2) there is s₀ with 0 < s₀ ≤ 1/4 such that for every s' ∈ (0, s₀] and every x ∈ spt C with ⟨x, a⟩ > 0, ||x| − 1| < s', |arctan(⟨x, e⟩/⟨x, a⟩)| < s' and |x − πx| ≤ 2s₀|x| (π := Q.starProjection) one has |x − πx| < (s'/4)|x| and |x − a| < 3s'.

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4821

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5644

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6251, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6264, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6273, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6286, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6298, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6304, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6314

## Lean problem

Declaration: `Submission.idtp_cse_edge_tangent_plane`

```lean
∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ : ℝ) (k : ℕ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < δ → 1 ≤ k → a ∈ C.support → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k ∧ ∃ r : ℝ, 0 < r ∧ C.support ∩ ball (t • (Real.cos φ • a + Real.sin φ • e)) r ⊆ (Q : Set (Euclid P))) → ∃ m : ℕ, 1 ≤ m ∧ HasMassDensity C a m ∧ (∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C' : GeometricCurrentOn (univ : Set (Euclid P)) 2) (c : ℤ), StrictMono φ ∧ c.natAbs = m ∧ ConvergesWeakly (fun j => blowUp C a (lams (φ j)) (hlams (φ j)).ne') C' ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 2, C' ω = (c : ℝ) * ∫ x in (Q : Set (Euclid P)), (ω : DifferentialForm (Euclid P) 2) x ![a, e] ∂μHE[2]) ∧ ∀ R : IMRep (univ : Set (Euclid P)) 2, R.Represents C → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂R.measure) atTop (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 4 ∧ (∀ s' : ℝ, 0 < s' → s' ≤ s₀ → ∀ x ∈ C.support, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ ≤ 2 * s₀ * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖ ∧ dist x a < 3 * s')
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 0, 1, 2 and 4(a) (tangent cones at a, the cusp, and the localization). Conventions: ℝ^P := Euclid P; B_ρ(x) open ball; H² := μHE[2]; ω_2 := unitBallVolume 2 ∈ (0, ∞), so ω_2.toReal > 0; π := Q.starProjection, q(x) := x − πx; f(x) := arctan(⟨x,e⟩/⟨x,a⟩); ⟨·,·⟩, |·| Euclidean. (F1): a, e are orthonormal in the 2-dimensional Q, so (a, e) is an orthonormal basis of Q, Q = span{a,e}, πx = ⟨x,a⟩a + ⟨x,e⟩e; q is linear and q(a) = 0. (Uniq) HasMassDensity C y θ and HasMassDensity C y θ' imply θ = θ' (both ≥ 0, limits in [0, ∞] are unique, ofReal is injective on [0, ∞)). For w ∈ ℝ^P and r > 0 let g_{w,r}(z) := min(1, max(0, 2 − |z − w|/r)): continuous, 0 ≤ g_{w,r} ≤ 1, g_{w,r} = 1 on closedBall(w, r), g_{w,r} = 0 off closedBall(w, 2r), compact support.
0. (Representation and m.) IsMinimizingIn C univ contains IsIntegerMultiplicity C; fix R_0 representing C and put μ := R_0.measure. By `Submission.dimred_im_mass_measure` (U = univ, open): (a) M_W(C) = μ(W) for open W; (b) x ∈ spt C iff μ(B_ε(x)) ≠ 0 for all ε > 0; (c) every representation of C has measure μ. Apply `Submission.idtp_cone_tangent_cone_planar` at p := a (a ∈ spt C, a ≠ 0 as |a| = 1) with λ_j := 1/(j+1): it provides c_* ∈ ℤ with |c_*| ≥ 1 and HasMassDensity C a |c_*|. Put m := |c_*| ∈ ℕ, m ≥ 1.
1. (Sector points.) Let y := t(cos φ a + sin φ e), t > 0, 0 < φ < δ. By hypothesis HasMassDensity C y k. If y ∉ spt C then by (b) μ(B_ε(y)) = 0 for some ε > 0, so M_{B_ρ(y)}(C) = μ(B_ρ(y)) = 0 for 0 < ρ < ε (by (a)), the density quotients vanish for small ρ and their limit ofReal(k) would be 0, contradicting k ≥ 1. So y ∈ spt C, and by the sibling `Submission.idtp_cse_massOn_ball_lower_bound`, μ(B_ρ(y)) = M_{B_ρ(y)}(C) ≥ ω_2ρ² for every ρ > 0.
2. (Blow-up limits along a given sequence.) Let λ_j > 0, λ_j → 0. Apply idtp_cone_tangent_cone_planar at p := a with this sequence: there are φ strictly increasing, C', an orthonormal pair τ = (τ_0, τ_1) and c ∈ ℤ with C_j := blowUp C a λ_{φ(j)} ⇀ C' (ConvergesWeakly), MassMeasuresConverge (C_j) C', a ∈ Q' := span{τ_0, τ_1}, |c| ≥ 1, HasMassDensity C a |c| and C'(ω) = c∫_{Q'} ω(x)(τ) dH²(x) for all ω. By (Uniq), |c| = m. Write λ := λ_{φ(j)} and η_j := dilation a λ when j is fixed.
(2a) A representation of C'. Let R' := (Q', m, ξ') with ξ'(x)(α) := sgn(c)·α(τ) for α ∈ Covector(ℝ^P, 2) (α ↦ α(τ) is linear and continuous, |α(τ)| ≤ ‖α‖|τ_0||τ_1|; sgn(c) = ±1 as c ≠ 0). R' ∈ IMRep(univ, 2): Q' is closed, hence Borel; Q' is the range of the linear isometry ι_τ : Euclid 2 → ℝ^P, v ↦ v_0τ_0 + v_1τ_1, which is Lipschitz, so Q' = range ι_τ is countably 2-rectifiable (SimonGMT `countablyRectifiable_range`; exceptional set ∅, all parametrizations ι_τ); mult ≡ m is measurable and ≥ 1; for compact K, ∫_{Q'∩K} m dH² = m·H²(Q' ∩ K) < ∞ because H²⌞Q' is the image of Lebesgue measure of Euclid 2 under ι_τ (`Isometry.euclideanHausdorffMeasure_image`, `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`) and K is bounded; ξ' is constant, hence strongly measurable; for every x ∈ Q', HasApproximateTangentSpaceAt 2 Q' x Q' (SimonGMT `hasApproximateTangentSpaceAt_submodule`, finrank Q' = 2) and IsUnitOrientationOf (ξ' x) Q' (witness τ, sign sgn(c)). R' represents C': R'.action ω = ∫_{Q'} m·sgn(c)·ω(x)(τ) dH² = c∫_{Q'} ω(x)(τ) dH² = C'(ω). Its measure is R'.measure = m·H²⌞Q'.
(2b) Representations of C_j. By `Submission.dtc_blowUp_imrep` (T := C, x := a, scale λ, R := R_0) there is R_j ∈ IMRep(dilation a λ '' univ, 2) representing C_j with R_j.measure(B) = ofReal(λ^{−2})·μ(η_j⁻¹(B)) for Borel B. So R_j.measure = ofReal(λ^{−2})•(η_j)_#μ, and ∫ g dR_j.measure = λ^{−2}∫ g(η_j(x)) dμ(x) for every bounded continuous g with compact support (g∘η_j is continuous with compact support and μ is locally finite).
(2c) Vague convergence. MassMeasuresConverge applied to (R_j), R' and a continuous compactly supported g (tsupport g ⊆ univ) gives (V): λ_{φ(j)}^{−2}∫ g∘η_j dμ → m∫_{Q'} g dH².
(2d) Q' = Q. Let w := σa + ue with σ ∈ ℝ, u > 0. Put y_j := a + λw = (1 + λσ)a + λu e. For large j, 1 + λσ > 0; then t_j := |y_j| = ((1 + λσ)² + (λu)²)^{1/2} > 0 and φ_j := arctan(λu/(1 + λσ)) ∈ (0, π/2) satisfy cos φ_j = (1 + λσ)/t_j and sin φ_j = λu/t_j, so y_j = t_j(cos φ_j a + sin φ_j e); and φ_j → 0, so φ_j < δ for large j. By step 1, μ(B_ρ(y_j)) ≥ ω_2ρ² for all ρ > 0. Fix r > 0 and g := g_{w,r}. Since η_j⁻¹(closedBall(w, r)) = closedBall(a + λw, λr) ⊇ B_{λr}(y_j) and g∘η_j ≥ 1 on η_j⁻¹(closedBall(w, r)), we get λ^{−2}∫ g∘η_j dμ ≥ λ^{−2}μ(B_{λr}(y_j)) ≥ ω_2.toReal·r² (as real numbers). By (V), m∫_{Q'} g dH² ≥ ω_2.toReal·r² > 0, hence H²(Q' ∩ closedBall(w, 2r)) > 0 and Q' meets closedBall(w, 2r). As r > 0 is arbitrary and Q' is closed, w ∈ Q'. In particular e ∈ Q' (σ = 0, u = 1), and a ∈ Q'; so Q = span{a, e} ⊆ Q', and finrank Q' = 2 = finrank Q gives Q' = Q.
(2e) Orientation. (a, e) and τ are orthonormal bases of Q; let O be the matrix of τ in the basis (a, e); O is orthogonal, so ε := det O ∈ {1, −1}. For every 2-covector α, the restriction of α to Q is an alternating 2-form on the 2-dimensional space Q, hence a multiple of the determinant with respect to (a, e), so α(τ) = ε·α(a, e). Therefore C'(ω) = c'·∫_Q ω(x)(a, e) dH²(x) with c' := εc, |c'| = m.
(2f) For any representation R of C, R.measure = μ by (c), so (V) with Q' = Q is exactly the asserted limit. This proves (1) with (φ, C', c').
3. (Cusp.) Claim: for every ε > 0 there is s_ε > 0 with |q(x)| ≤ ε|x − a| for all x ∈ spt C with |x − a| < s_ε. Suppose not: there are ε > 0 and x_j ∈ spt C with s_j := |x_j − a| → 0 and |q(x_j)| > εs_j; then x_j ≠ a, so s_j > 0. Put w_j := (x_j − a)/s_j; |w_j| = 1 and |q(w_j)| = |q(x_j)|/s_j > ε. Apply step 2 to λ_j := s_j and pass to the subsequence φ; by compactness of the unit sphere pass to a further subsequence with w_j → w (then |w| = 1, |q(w)| ≥ ε), along which (V) still holds with Q. Fix r > 0 and g := g_{w,2r}. For large j, |w_j − w| < r, so B_r(w_j) ⊆ closedBall(w, 2r) and η_j⁻¹(B_r(w_j)) = B_{s_j r}(x_j). Hence s_j^{−2}∫ g∘η_j dμ ≥ s_j^{−2}μ(B_{s_j r}(x_j)) ≥ ω_2.toReal·r² (sibling lower bound, x_j ∈ spt C). By (V), m∫_Q g dH² ≥ ω_2.toReal·r² > 0, so Q meets closedBall(w, 4r). As r is arbitrary and Q is closed, w ∈ Q, so q(w) = 0, contradicting |q(w)| ≥ ε.
4. (Localization.) Let s₀ := min(1/4, s_{1/20}/6) (step 3 with ε = 1/20); then 0 < s₀ ≤ 1/4 and 5s₀ < s_{1/20}. Let 0 < s' ≤ s₀ and x ∈ spt C with ⟨x,a⟩ > 0, ||x| − 1| < s', |f(x)| < s' and |q(x)| ≤ 2s₀|x|. Then |x| > 1 − s' ≥ 3/4. Put η := |q(x)|/|x| ≤ 2s₀ ≤ 1/2 and x̂ := x/|x|; f(x̂) = f(x), and with v := cos f(x)·a + sin f(x)·e (a unit vector), πx̂ = |πx̂|·v (because ⟨x̂,a⟩ > 0: cos(arctan u) = (1 + u²)^{−1/2}, sin(arctan u) = u(1 + u²)^{−1/2}, u := ⟨x̂,e⟩/⟨x̂,a⟩, and |πx̂|² = ⟨x̂,a⟩² + ⟨x̂,e⟩²). Since |πx̂|² = 1 − η², |πx̂| = (1 − η²)^{1/2} ≥ 1 − η². Writing x̂ − a = (πx̂ − v) + (v − a) + q(x̂): |πx̂ − v| = 1 − |πx̂| ≤ η²; |v − a|² = 2 − 2cos f(x) ≤ f(x)², so |v − a| ≤ |f(x)| < s'; |q(x̂)| = η. Hence |x̂ − a| < s' + η² + η ≤ s' + 1.5η, and |x − a| ≤ ||x| − 1| + |x̂ − a| < 2s' + 1.5η ≤ 2s₀ + 3s₀ = 5s₀ < s_{1/20}. By step 3, (3/4)η ≤ η|x| = |q(x)| ≤ |x − a|/20 < (2s' + 1.5η)/20, so (27/40)η < s'/10, η < (4/27)s' < s'/4. Therefore |q(x)| = η|x| < (s'/4)|x| and |x − a| < 2s' + 1.5·(4/27)s' < 3s'. This is (2). ∎

## Key steps

1. m := Θ(a) ∈ ℕ_{≥1} from idtp_cone_tangent_cone_planar; densities are unique.
2. Sector points y have density k ≥ 1, so y ∈ spt C and μ(B_ρ(y)) ≥ ω_2ρ² (sibling mass_lower_bound).
3. For every λ_j → 0, idtp_cone_tangent_cone_planar gives a subsequence with C_j ⇀ c[[Q']] and mass measures converging; with the explicit representation (Q', m, ±τ) of the limit and dtc_blowUp_imrep, λ_j^{-2}∫ g∘η_j dμ → m∫_{Q'} g dH².
4. The sector points a + λ_j(σa + ue) force σa + ue ∈ Q', so Q' = Q; re-orienting τ to (a, e) changes c only by a sign.
5. Cusp: points of spt C near a satisfy |q(x)| ≤ ε|x − a|, by blow-up compactness and the lower density bound.
6. Localization 4(a): with 5s₀ < s_{1/20}, every x ∈ spt C in the box with |q(x)| ≤ 2s₀|x| has |q(x)| < (s'/4)|x| and |x − a| < 3s'.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: status/lean_statement of the selected node, its siblings (idtp_cone_tangent_cone_planar, idtp_imrep_measure_density_ae, idtp_carrier_area_formula) and the cross-branch results dimred_im_mass_measure, dimred_minimizing_monotonicity, minimizing_implies_stationary, stationaryAlong_of_minimizing_in_submanifold, cone_current_imrep_measure_smul_image, imrep_represents_support_eq_inter_measure_support, imrep_approxTangent_starProjection_aesm, dtc_blowUp_massOn_image, dtc_blowUp_imrep, dtc_blowUp_testForm_corr, dtc_approxTangent_dilation, dtc_approxTangent_of_null_diff, dtc_cone_radial_tangency, dsmc_firstVariation_eq_integral`
- `python3 DAG reachability from each external dependency (depends_on + children) to the selected node: none reaches it`
- `grep -o 'idtp_cse_[A-Za-z0-9_]*' dag.json (no match); grep -rl idtp_cse_ nodes/ (only this node's own v1 records); grep -rl --include=*.lean idtp_cse_ .swarm-worktrees/*/gmt-ch07/GMT (no match); grep -rl idtp_cse_ local-references/123e8435b4a2469b/project (no match)`
- `grep -rn 'hasApproximateTangentSpaceAt_submodule|HasApproximateTangentSpaceAt.unique|HasApproximateTangentSpaceAt.finrank_eq|countablyRectifiable_range|ae_eq_const_of_weak_coordinate_derivatives_zero|def CountablyRectifiable|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'lintegral_comp_polarCoord_symm|IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|smoothTransition|support_mem_ae|volume_preserving_finTwoArrow|PiLp.volume_preserving_ofLp|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_smul₀|lintegral_withDensity_eq_lintegral_mul_non_measurable|map_linearDependent|smul_unitBall|integral_eq_lintegral_of_nonneg_ae|measure_prod_null|exists_measurable_superset_of_null|ContinuousMap.instSeparableSpace' .lake/packages/mathlib/Mathlib`
- `lake env lean /tmp/cse2/check/Stmts.lean (all 11 child types plus the parent type elaborate; only sorry warnings)`
- `lake env lean /tmp/cse2/check/Parent.lean (hypothesis-only assembly of the parent from edge_tangent_plane, box_mass_limits, fibre_count; #print axioms: propext, Classical.choice, Quot.sound)`
- `gh issue view 4821 --comments; issue-workers.json, run.json, operator-dependency-edits and decomposition-reopenings inspected for the cause of the unregistered attempt-1 decomposition`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/tmp/cse2/check/Stmts.lean`
- `/tmp/cse2/check/Parent.lean`

Pins and contract match: the workspace Submission.lean (GMT.Ch07, frozen opens) is the compiler authority, with mathlib 25730c7c and SimonGMT 2b36630. All Mathlib and SimonGMT names cited in the child proofs exist at these pins, including countablyRectifiable_range and the hereditarily-Lindelöf support_mem_ae. The 11 proposed idtp_cse_* names are unreserved: they occur in no DAG node, other node record, worktree or the snapshot. The only occurrences are this node's own unregistered attempt-1 records, which hold identical Lean types. All 11 types elaborate. The parent follows from edge_tangent_plane, box_mass_limits and fibre_count, kernel-checked with standard axioms only. External prerequisites are the accepted dtc_*/dimred_im_mass_measure/imrep_*/dsmc_*/cone_current_* lemmas and the pending minimizing_implies_stationary, dimred_minimizing_monotonicity and the three parent siblings; their DAG types match their uses and none depends back on this node.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
