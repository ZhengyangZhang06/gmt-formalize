<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1 -->

## Theorem `Submission.dmcbr_ci_pw_density_l1_tendsto_const`

Let d ∈ ℕ, n := d + 1, R > 0, c, Λ ∈ ℝ, U := B_{2R}(0) ⊆ ℝⁿ, Y_k ∈ 𝒟_n(U) and u_k : ℝⁿ → ℝ (k ∈ ℕ) with u_k Lebesgue integrable on U, ∫_U|u_k| ≤ Λ for all sufficiently large k, and Y_k(ω) = ∫_U u_k(y)·ω(y)(e_0, …, e_d)dy for every k and ω ∈ 𝒟ⁿ(U) (e_i = EuclideanSpace.single i 1). Assume M_U(∂Y_k) → 0 and Y_k(ω) → c∫_{ℝⁿ}ω(y)(e_0, …, e_d)dy for every ω ∈ 𝒟ⁿ(U). Then ∫_{B_R(0)}|u_k − c| → 0.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7066

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6181, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6190, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6198

Decomposition children: None

## Lean problem

Declaration: `Submission.dmcbr_ci_pw_density_l1_tendsto_const`

```lean
∀ (d : ℕ) (R c Λ : ℝ) (Y : ℕ → GeometricCurrentOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)) (u : ℕ → Euclid (d + 1) → ℝ), 0 < R → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ (k : ℕ) (ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)), Y k ω = ∫ y in ball 0 (2 * R), u k y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Tendsto (fun k => (Y k).boundary.massOn (ball 0 (2 * R))) atTop (𝓝 0) → (∀ ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1), Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → Tendsto (fun k => ∫ y in ball 0 R, |u k y - c|) atTop (𝓝 0)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 11 of the parent proof ((a) uniform convergence of u_k∗φ_{s₀}, (b) the BV estimate with the forms ε_j, (c) the combination). Uses the siblings interior_form, mollified_uniform and bv_estimate.
1. (Test functions as top forms.) Let dy ∈ Λⁿ(ℝⁿ) be the determinant of the standard basis (the alternating map (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det, continuous by Continuous.matrix_det, hence a ContinuousAlternatingMap), so dy(e) = 1. For b smooth with compact support and tsupport b ⊆ U, ω_b(y) := b(y)·dy is a test n-form on U (smooth, compact support, tsupport ω_b ⊆ tsupport b ⊆ U) with ω_b(y)(e) = b(y). Hence ∫_U u_k b = Y_k(ω_b) → c∫b.
2. (Mollifier.) Put s := R/4 (so 0 < s < R and 2s < R). Let φ ≥ 0 be smooth with tsupport φ ⊆ B_s(0) and ∫φ = 1: a ContDiffBump centred at 0 with rIn = s/4, rOut = s/2 (smooth, values in [0, 1], equal to 1 on closedBall(0, s/4), tsupport = closedBall(0, s/2)) divided by its integral, which is positive (continuous, ≥ 0 and = 1 on a ball of positive measure; integral_pos_iff_support_of_nonneg).
3. (Uniform convergence of the mollifications.) By mollified_uniform (n, R, s, c, Λ, φ, u_k; s < R; integrability and the eventual Λ-bound; step 1), w_k(x) := ∫_U u_k(y)φ(x − y)dy → c∫φ = c uniformly on closedBall(0, R).
4. (Variation bound.) Let V_k := (M_U(∂Y_k)).toReal ≥ 0. As M_U(∂Y_k) → 0 there is k₀ with M_U(∂Y_k) < ∞ for k ≥ k₀, and V_k → 0 (ENNReal.tendsto_toReal at 0). Claim: for k ≥ k₀, every smooth compactly supported f with tsupport f ⊆ U, every z ∈ ℝⁿ and every M with |f| ≤ M: |∫_U u_k(y)Df(y)(z)dy| ≤ V_k‖z‖M. Proof: by interior_form take ε_z ∈ Λ^d(ℝⁿ) with |ε_z| ≤ ‖z‖ and d(f·ε_z)(y)(e) = Df(y)(z) for every y (f is differentiable everywhere). γ := f·ε_z is a test d-form on U (smooth, tsupport γ ⊆ tsupport f ⊆ U), and dγ is a test n-form on U (exteriorDerivativeTestOn), so by the representation of Y_k: ∂Y_k(γ) = Y_k(dγ) = ∫_U u_k(y)dγ(y)(e)dy = ∫_U u_k(y)Df(y)(z)dy. Pointwise |γ(y)| = |f(y)|·|ε_z| ≤ M‖z‖ (covectorEuclideanNorm (a·α) = |a|·|α|; M ≥ 0 since |f| ≤ M). For every η > 0 the forms ±(M‖z‖ + η)⁻¹γ have coefficient norm ≤ 1 and tsupport ⊆ U, so they belong to massAdmissibleOn U d U and ofReal(±(M‖z‖ + η)⁻¹∂Y_k(γ)) ≤ M_U(∂Y_k) (GeometricCurrentOn.le_massOn, linearity of ∂Y_k); since M_U(∂Y_k) < ∞ this gives |∂Y_k(γ)| ≤ (M‖z‖ + η)V_k, and letting η → 0, |∂Y_k(γ)| ≤ V_k‖z‖M.
5. (BV estimate.) For k ≥ k₀, bv_estimate (n, R, s, V_k, φ, u_k; 2s < R, V_k ≥ 0, φ ≥ 0, tsupport φ ⊆ B_s(0), ∫φ = 1, u_k integrable on U, step 4) gives ∫_{B_R}|u_k − w_k| ≤ sV_k.
6. (Conclusion.) For k ≥ k₀: |u_k − c| ≤ |u_k − w_k| + |w_k − c| pointwise, all functions involved are integrable on B_R(0) (u_k ∈ L¹(B_R), w_k continuous hence bounded on the bounded ball), so ∫_{B_R}|u_k − c| ≤ ∫_{B_R}|u_k − w_k| + ∫_{B_R}|w_k − c| ≤ sV_k + volume(B_R(0)).toReal·sup_{x ∈ closedBall(0,R)}|w_k(x) − c|. Both terms tend to 0 (steps 3–4) and the left side is ≥ 0, so ∫_{B_R(0)}|u_k − c| → 0 (squeeze_zero' / tendsto_of_tendsto_of_tendsto_of_le_of_le'). ∎

Verified Lean realization (supplementary). The single theorem below was compiled with `lake env lean` (Lean v4.35.0-rc3; project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308) in a file that imports GMT.Ch07.Submission and reopens the frozen contract's namespace GMT.Ch07 with its `open`s, with the sibling dependencies Submission.cbr_ci_pw_interior_product_form (interior_form), Submission.cbr_ci_pw_mollified_tendstoUniformlyOn (mollified_uniform) and Submission.cbr_ci_pw_bv_mollifier_estimate (bv_estimate) declared by their exact frozen Lean types: no errors and no warnings; `#count_heartbeats` reports 59551 heartbeats, below the default maxHeartbeats 200000 (no set_option); `#print axioms` lists propext, Classical.choice, Quot.sound and these three siblings; inserted before main_theorem in GMT/Ch07/Submission.lean it passes the runtime's leaf source-delta check (one appended theorem under its exact name; no helper declaration, import, set_option or placeholder). Its local lemmas aux_* are proved inline and correspond to the numbered steps above: aux_exists_det_covector and aux_scalar_test_tendsto are step 1 (a top covector dy with dy(e_0, …, e_d) = 1, the test forms b·dy, and ∫_U u_k b → c∫b); aux_exists_normalized_mollifier is step 2 (with r := R/8, so support φ ⊆ B_{R/8}(0) and tsupport φ ⊆ B_{R/4}(0) = B_s(0)); step 3 calls the sibling mollified_uniform; aux_abs_apply_le_massOn (|T(ω)| ≤ r·M_W(T) when tsupport ω ⊆ W and |ω| ≤ r), aux_norm_props (|t·α| = |t||α| and the other seminorm properties of the coefficient norm) and aux_boundary_variation_bound are step 4, with ε_z from the sibling interior_form; step 5 calls the sibling bv_estimate; aux_l1_squeeze_of_mollified is step 6. It may be appended verbatim as the single leaf theorem:
```lean
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
```

## Key steps

1. Test functions b give test forms b·dy, so ∫_U u_k b → c∫b; fix a normalized bump φ supported in B_{R/4}.
2. mollified_uniform: w_k = u_k∗φ → c uniformly on B̄_R.
3. interior_form: Y_k((∂_zf)dy) = ∂Y_k(f·ε_z) with |f·ε_z| ≤ |z|sup|f|, so ∫u_k∂_zf is bounded by M_U(∂Y_k)|z|sup|f|; bv_estimate gives ∫_{B_R}|u_k − w_k| ≤ (R/4)M_U(∂Y_k).
4. ∫_{B_R}|u_k − c| ≤ (R/4)M_U(∂Y_k) + |B_R|·sup|w_k − c| → 0.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD in the workspace, .lake/packages/mathlib and .lake/packages/simongmt -> b4d606db1, 25730c7c, 2b366308; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2229 nodes): selected node (depth 5, decomposing, attempt 2 started 2026-10-14T02:29:54Z); subtree of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1 (cbr_ci_plane_weight_ge_one: identical frozen type, speculative-ready) with statuses, candidate commits and updated_at; lean_name lookup of all 11 proposed names: the 8 reused names each occur once, accepted with candidate commits (latest 02:28:02Z) and identical lean_statement; the 3 dmcbr_ci_pw_* names have no node; byte comparisons dimred_mbl_slice_mass_bounds = cmc_slice_mass_bounds, dmcbr_measure_convergence_tools = cbr_measure_convergence_tools, first conjunct of dimred_mbl_current_foundations = cmc_exists_massRepresentation, and (REP), (SL), (CT) occur verbatim in the selected type`
- `grep -n / sed -n over /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children existing_by_name), store.py (refresh, update: accepted status is permanent), leaf_verification.py (check_source_delta), lean_contract.py (validate_lean_statement); swarm-project.json -> max_depth 6, max_children 12`
- `read RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/{parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json}: attempt 1 (12 children) was rejected only by the name check on cbr_ci_pw_bv_smooth_test_bound; its child statements, types and proofs were reused here, except smooth_test_bound (dropped) and bv_estimate (now the accepted cbr_ci_pw_bv_mollifier_estimate, with Claim A proved inline)`
- `git show <candidate>:GMT/Ch07/Submission.lean for e55e2ff3e6, f6358e3d52, e42d9153e5, b0c7e18f51, 7bb3791613, 4020906019, 04807323c8, 144655f39d -> each contains 'theorem Submission.<name> : <frozen type> :=' with the reused name occurring exactly once`
- `grep -rn over SNAPSHOT/mathlib/Mathlib for the library names cited in the bv_estimate proof: ae_tendsto_average_norm_sub (Covering/DensityTheorem.lean:150, Covering/Differentiation.lean:837), tendsto_integral_smul_of_tendsto_average_norm_sub, integral_comp_inv_smul_of_nonneg, addHaar_real_closedBall', contDiff_convolution_right, integrableOn_iff_integrable_of_support_subset, integrableOn_of_bounded, continuous_of_dominated, intervalIntegral_integral_swap, norm_integral_le_of_norm_le_const, fderiv_comp_add_right, tsupport_comp_eq_preimage, integral_sub_right_eq_self, Integrable.mul_prod, integral_integral_swap, Integrable.mul_bdd, setIntegral_indicator, integral_pos_iff_support_of_nonneg, measure_ball_pos, Integrable.integral_prod_left, Integrable.integral_prod_right, Continuous.integrable_of_hasCompactSupport, Continuous.bounded_above_of_compact_support, HasCompactSupport.fderiv, integral_eq_sub_of_hasDerivAt -> all present`
- `rg -l dmcbr_ci_pw_projected_current|dmcbr_ci_pw_density_null_off_image|dmcbr_ci_pw_density_l1_tendsto_const over SNAPSHOT/project, GMT and .lake/packages/simongmt -> no match (exit 1)`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Types.lean (the 11 child types as Submission.* theorems) -> only sorry warnings, exit 0`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Assembly.lean (exact frozen parent type from the 11 child types as axioms, no sorry) -> #print axioms: propext, Classical.choice, Quot.sound, cbr_ci_pw_good_level_slices, cbr_ci_pw_isolate_plane, cbr_ci_pw_orthonormal_covector_bounds, cbr_ci_pw_plane_map_volume, cbr_ci_pw_top_current_density, dmcbr_ci_pw_density_l1_tendsto_const, dmcbr_ci_pw_density_null_off_image, dmcbr_ci_pw_projected_current`
- `lake env lean /tmp/dmcbr_ci_a2/lean/check_{projection,null_off_image,l1_constant}.lean (#count_heartbeats in + realization + #print axioms, siblings declared by exact frozen types) -> 102743 / 19932 / 59551 heartbeats, axioms = standard three + declared siblings only`
- `lake env lean /tmp/dmcbr_ci_a2/lean/EndToEnd.lean (3 fresh realizations as theorems + assembly) -> #print axioms: propext, Classical.choice, Quot.sound + the 8 reused accepted declarations, exit 0`
- `python3 -I: AST-extracted leaf_verification.check_source_delta on GMT/Ch07/Submission.lean with each fresh realization inserted before main_theorem's docstring -> OK (3/3); lean_contract.validate_lean_statement on all 11 child types -> valid and unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/tmp/dmcbr_ci_a2/lean/Types.lean`
- `/tmp/dmcbr_ci_a2/lean/Assembly.lean`
- `/tmp/dmcbr_ci_a2/lean/check_projection.lean`
- `/tmp/dmcbr_ci_a2/lean/check_null_off_image.lean`
- `/tmp/dmcbr_ci_a2/lean/check_l1_constant.lean`
- `/tmp/dmcbr_ci_a2/lean/EndToEnd.lean`

The snapshot is compatible: pins match, and the snapshot contract is byte-identical to Submission.lean. No dmcbr_ci_pw_* declaration exists in the snapshot, the workspace or SimonGMT. The 8 reused children (covector_bounds, plane_map, isolate_plane, good_level, top_density, interior_form, mollified_uniform, bv_estimate = cbr_ci_pw_bv_mollifier_estimate) are accepted checkpoints. They were accepted before this attempt's DAG refresh, and each candidate commit declares exactly the frozen type. The 3 fresh children take globally unused dmcbr_ci_pw_* names because their other-branch counterparts are unaccepted. All 11 child types elaborate. The sorry-free conditional assembly and the end-to-end file prove the exact parent type using only propext, Classical.choice, Quot.sound and child or reused accepted declarations. The fresh single-theorem realizations compile within the default heartbeats and pass the leaf delta check.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
