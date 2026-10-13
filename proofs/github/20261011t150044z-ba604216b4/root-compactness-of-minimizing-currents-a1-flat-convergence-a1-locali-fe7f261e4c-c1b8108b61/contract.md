<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.weak_conv-a1 -->

## Theorem `Submission.cmc_fcl_weakConverges_sublevel`

Let P, d ∈ ℕ, U ⊆ ℝ^P, g : ℝ^P → ℝ continuous, s ∈ ℝ and G := {x : g(x) < s}.
Let μ_j (j ∈ ℕ) and μ be measures on the Borel sets of ℝ^P with μ_j(G) < ∞ and μ(G) < ∞.
Let ξ_j, ξ : ℝ^P → Λ_d(ℝ^P) (MultiVector P d) be μ_j- resp. μ-a.e. strongly measurable, with |⟨α, ξ_j(x)⟩| ≤ |α| for μ_j-a.e. x and |⟨α, ξ(x)⟩| ≤ |α| for μ-a.e. x, for every d-covector α (|α| = covectorEuclideanNorm α, ⟨α, ζ⟩ = ζ(α)).
Let T_j, T'_j, T, T' ∈ 𝒟_d(U) satisfy, for every ω ∈ 𝒟^d(U): T_j(ω) = ∫⟨ω(x), ξ_j(x)⟩ dμ_j(x), T(ω) = ∫⟨ω(x), ξ(x)⟩ dμ(x), T'_j(ω) = ∫_G⟨ω(x), ξ_j(x)⟩ dμ_j(x) and T'(ω) = ∫_G⟨ω(x), ξ(x)⟩ dμ(x).
Assume T_j ⇀ T in U (WeaklyConvergesOn), and that for every ε ∈ (0, ∞] there is δ > 0 with μ_j({s - δ ≤ g ≤ s}) ≤ ε for all sufficiently large j.
Then T'_j ⇀ T' in U.

Node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.weak_conv-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4689

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.cmc_fcl_weakConverges_sublevel`

```lean
∀ (P d : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (s : ℝ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P d) (ξ : Euclid P → MultiVector P d) (Ts Ts' : ℕ → GeometricCurrentOn U d) (T T' : GeometricCurrentOn U d), Continuous g → (∀ j, μs j {x | g x < s} < ∞) → μ {x | g x < s} < ∞ → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → AEStronglyMeasurable ξ μ → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) d, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ (j : ℕ) (ω : TestFormOn U d), Ts j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) d) x) ∂(μs j)) → (∀ ω : TestFormOn U d, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn U d), Ts' j ω = ∫ x in {x | g x < s}, ξs j x ((ω : DifferentialForm (Euclid P) d) x) ∂(μs j)) → (∀ ω : TestFormOn U d, T' ω = ∫ x in {x | g x < s}, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → WeaklyConvergesOn Ts T → (∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μs j {x | s - δ ≤ g x ∧ g x ≤ s} ≤ ε) → WeaklyConvergesOn Ts' T'
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.weak_conv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 10 (weak convergence) of the parent proof of cmc_fc_localize, stated abstractly. In the parent: g = dist(·, closure W); s is the good level from cmc_fc_good_slice; μ_j = R_{φ(j)}.measure and ξ_j = R_{φ(j)}.orient; T_j = T_{φ(j)}; T'_j = A_{φ(j)}(s), the slice current T_{φ(j)}⌞{g < s}; μ = R_T.measure, ξ = R_T.orient and T' = T⌞{g < s}. The no-concentration hypothesis (H6) is conclusion (ii) of good_slice transported along g.
Notation: G := {g < s}; |α| := covectorEuclideanNorm α; ⟨β, ζ⟩ := ζ(β).
Hypotheses:
(H0) g is continuous.
(H1) μ_j(G) < ∞ for all j, and μ(G) < ∞.
(H2) ξ_j is μ_j-a.e. strongly measurable, and ξ is μ-a.e. strongly measurable.
(H3) For μ_j-a.e. x, |⟨α, ξ_j(x)⟩| ≤ |α| for all α; likewise for μ-a.e. x and ξ.
(H4) For every ω ∈ 𝒟^d(U) (Bochner integrals): T_j(ω) = ∫⟨ω, ξ_j⟩ dμ_j, T(ω) = ∫⟨ω, ξ⟩ dμ, T'_j(ω) = ∫_G⟨ω, ξ_j⟩ dμ_j, T'(ω) = ∫_G⟨ω, ξ⟩ dμ.
(H5) T_j ⇀ T.
(H6) For every ε ∈ (0, ∞] there is δ > 0 such that μ_j({s - δ ≤ g ≤ s}) ≤ ε for all sufficiently large j.
Claim: T'_j(ω) → T'(ω) for every ω ∈ 𝒟^d(U).
1. (A bound for ω.) Fix ω ∈ 𝒟^d(U); ω also denotes the underlying smooth compactly supported form. The coefficient norm is |α| = sqrt(Σ_{I strictly increasing} α(e_{I(1)}, …, e_{I(d)})²). It is continuous in α: each evaluation α ↦ α(v) at a fixed tuple v is continuous (continuous_eval_const), and squares, finite sums and sqrt are continuous. So x ↦ |ω(x)| is continuous. It has compact support because ω does and |0| = 0 (HasCompactSupport.comp_left). Hence it is bounded (HasCompactSupport.exists_bound_of_continuous). Fix c ∈ ℝ with |ω(x)| ≤ c for all x; then c ≥ |ω(0)| ≥ 0.
2. (Cutoff estimate.) Claim: let ν be a measure on ℝ^P with ν(G) < ∞, and ζ a ν-a.e. strongly measurable d-vector field with |⟨α, ζ(x)⟩| ≤ |α| for all α, for ν-a.e. x. Let r ∈ ℝ, and let χ : ℝ^P → [0, 1] be continuous with χ = 1 on {g ≤ r} and χ = 0 on {g ≥ s}. Then |∫_G⟨ω, ζ⟩ dν - ∫⟨χω, ζ⟩ dν| ≤ c·ν({r < g < s}). Here ν({r < g < s}) ≤ ν(G) < ∞, and its real value is used.
 Proof of the claim.
 (a) F(x) := ⟨ω(x), ζ(x)⟩ is ν-a.e. strongly measurable: (L, v) ↦ L(v) is jointly continuous (Continuous.clm_apply); x ↦ (ζ(x), ω(x)) is ν-a.e. strongly measurable (AEStronglyMeasurable.prodMk, ω continuous); and continuous maps preserve a.e. strong measurability (Continuous.comp_aestronglyMeasurable).
 (b) For ν-a.e. x, |F(x)| ≤ |ω(x)| ≤ c (hypothesis with α := ω(x), and step 1). Also |χ(x)F(x)| ≤ c, since 0 ≤ χ ≤ 1.
 (c) Since ν(G) < ∞, F and χF are integrable on G (Measure.integrableOn_of_bounded).
 (d) ⟨χ(x)ω(x), ζ(x)⟩ = χ(x)F(x) by linearity of ζ(x) (map_smul). χF vanishes outside G, where g ≥ s and so χ = 0. Hence ∫χF dν = ∫_G χF dν (setIntegral_eq_integral_of_forall_compl_eq_zero).
 (e) By (c) and linearity, ∫_G F dν - ∫_G χF dν = ∫_G (1 - χ)F dν (integral_sub).
 (f) (1 - χ)F vanishes on G ∖ {r < g < s} = G ∩ {g ≤ r}, where χ = 1. Since {r < g < s} ⊆ G and G is Borel, ∫_G (1 - χ)F dν = ∫_{r<g<s} (1 - χ)F dν (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero).
 (g) |(1 - χ)F| ≤ c ν-a.e., because 0 ≤ 1 - χ ≤ 1 and by (b). Since ν({r < g < s}) ≤ ν(G) < ∞, |∫_{r<g<s} (1 - χ)F dν| ≤ c·ν({r < g < s}) (norm_setIntegral_le_of_norm_le_const_ae).
 Combining (d)-(g) proves the claim.
3. Fix ε > 0 and put η := ε/(3(c + 1)) > 0.
4. (Small layer for the limit measure.) For i ∈ ℕ let S_i := {s - 1/(i+1) < g < s}.
 - Each S_i is Borel, since g is continuous.
 - The sequence is decreasing: 1/(k+1) ≤ 1/(i+1) for i ≤ k.
 - μ(S_0) ≤ μ(G) < ∞.
 - ⋂_i S_i = ∅: if g(x) < s, choose i with 1/(i+1) < s - g(x) (exists_nat_one_div_lt), so x ∉ S_i; if g(x) ≥ s, then x ∉ S_0.
 By continuity from above (tendsto_measure_iInter_atTop), μ(S_i) → μ(∅) = 0. So some i has μ(S_i) ≤ ENNReal.ofReal η. Put δ₁ := 1/(i+1) > 0; then μ({s - δ₁ < g < s}) ≤ η.
5. (Small layer along the sequence.) Apply (H6) with ε := ENNReal.ofReal η > 0. This gives δ₂ > 0 and N₂ with μ_j({s - δ₂ ≤ g ≤ s}) ≤ η for all j ≥ N₂.
6. (Cutoff.) Let δ' := min(δ₁, δ₂) > 0. The set {g ≤ s - δ'} is closed and contained in the open set {g < s - δ'/2}, which is its own interior. By the smooth Urysohn lemma there is a C^∞ function χ : ℝ^P → [0, 1] with χ = 1 on {g ≤ s - δ'} and χ = 0 outside {g < s - δ'/2}; in particular χ = 0 on {g ≥ s}. (Mathlib: exists_contMDiffMap_one_nhds_of_subset_interior with the model modelWithCornersSelf ℝ ℝ^P and n = ∞, followed by contMDiff_iff_contDiff.)
7. (The test form χω.) The form χω : x ↦ χ(x)ω(x) is C^∞ (ContDiff.smul). Its support is contained in that of ω, since ω(x) = 0 implies χ(x)ω(x) = 0. So it has compact support (HasCompactSupport.mono'), and tsupport(χω) ⊆ tsupport(ω) ⊆ U (closure_mono). Hence χω ∈ 𝒟^d(U).
8. By (H5) applied to χω there is N₁ with |T_j(χω) - T(χω)| < η for all j ≥ N₁.
9. (Estimate.) Let j ≥ max(N₁, N₂).
 - By (H4), T'_j(ω) = ∫_G⟨ω, ξ_j⟩ dμ_j and T_j(χω) = ∫⟨χω, ξ_j⟩ dμ_j. Step 2 with ν := μ_j, ζ := ξ_j, r := s - δ' applies, by (H1)-(H3) and step 6. Using δ' ≤ δ₂ and step 5, |T'_j(ω) - T_j(χω)| ≤ c·μ_j({s - δ' < g < s}) ≤ c·μ_j({s - δ₂ ≤ g ≤ s}) ≤ cη.
 - Likewise, step 2 with ν := μ and ζ := ξ, together with δ' ≤ δ₁ and step 4, gives |T'(ω) - T(χω)| ≤ c·μ({s - δ' < g < s}) ≤ c·μ({s - δ₁ < g < s}) ≤ cη.
 The passage from the ENNReal bounds to real bounds uses ENNReal.toReal_le_of_le_ofReal.
10. By the triangle inequality, for all j ≥ max(N₁, N₂), |T'_j(ω) - T'(ω)| ≤ |T'_j(ω) - T_j(χω)| + |T_j(χω) - T(χω)| + |T(χω) - T'(ω)| < cη + η + cη = (2c + 1)η < 3(c + 1)η = ε.
11. Since ε > 0 was arbitrary, T'_j(ω) → T'(ω). Since ω was arbitrary, T'_j ⇀ T' (WeaklyConvergesOn). ∎
Formalization notes, from the compiled proof below:
- Do not open scoped ContDiff: it makes ω a token, which breaks binder names. Write the smoothness order as ((⊤ : ℕ∞) : WithTop ℕ∞).
- Use modelWithCornersSelf ℝ (Euclid P) instead of the 𝓘 notation.
- Build χω from pointwise support inclusions (HasCompactSupport.mono', closure_mono). The generic HasCompactSupport.smul_left and tsupport_smul_subset_right took several minutes to elaborate for covector-valued forms.
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens. #print axioms: propext, Classical.choice, Quot.sound.
  intro P d U g s μs μ ξs ξ Ts Ts' T T' hg hμsG hμG hξsm hξm hξsb hξb hTs hT hTs' hT' hconv hconc
  intro ω
  obtain ⟨w, hwdef⟩ : ∃ w : DifferentialForm (Euclid P) d, w = (ω : DifferentialForm (Euclid P) d) :=
    ⟨_, rfl⟩
  have hwc : Continuous w := by rw [hwdef]; exact ω.property.1.1.continuous
  -- Step 1: a bound `c` for the coefficient norm of `ω`.
  have hnc : Continuous fun α : Covector (Euclid P) d => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    apply Continuous.sqrt
    apply continuous_finsetSum
    intro I _
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x, covectorEuclideanNorm (w x) ≤ c := by
    have hwcs : HasCompactSupport w := by
      rw [hwdef]
      exact ω.property.1.2
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ w) :=
      hwcs.comp_left (covectorEuclideanNorm_zero P d)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous (hnc.comp hwc)
    exact ⟨C, fun x => le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x)⟩
  have hc0 : 0 ≤ c := le_trans (covectorEuclideanNorm_nonneg _) (hc 0)
  have hGm : MeasurableSet {x | g x < s} := measurableSet_lt hg.measurable measurable_const
  -- Step 2: the cutoff estimate, for an arbitrary measure.
  have key : ∀ (ν : Measure (Euclid P)) (ζ : Euclid P → MultiVector P d) (χ : Euclid P → ℝ) (r : ℝ),
      ν {x | g x < s} < ∞ → AEStronglyMeasurable ζ ν →
      (∀ᵐ x ∂ν, ∀ α : Covector (Euclid P) d, |ζ x α| ≤ covectorEuclideanNorm α) →
      Continuous χ → (∀ x, χ x ∈ Icc (0 : ℝ) 1) → (∀ x, g x ≤ r → χ x = 1) →
      (∀ x, s ≤ g x → χ x = 0) →
      |∫ x in {x | g x < s}, ζ x (w x) ∂ν - ∫ x, ζ x (χ x • w x) ∂ν| ≤
        c * ν.real {x | r < g x ∧ g x < s} := by
    intro ν ζ χ r hνG hζm hζb hχc hχ01 hχ1 hχ0
    have hF : AEStronglyMeasurable (fun x => ζ x (w x)) ν :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hζm.prodMk hwc.aestronglyMeasurable)
    have hFb : ∀ᵐ x ∂ν, |ζ x (w x)| ≤ c := hζb.mono fun x hx => (hx _).trans (hc x)
    have hint1 : IntegrableOn (fun x => ζ x (w x)) {x | g x < s} ν :=
      Measure.integrableOn_of_bounded hνG.ne hF
        (ae_restrict_of_ae (hFb.mono fun x hx => by rwa [Real.norm_eq_abs]))
    have hχF : ∀ x, |ζ x (w x)| ≤ c → |χ x * ζ x (w x)| ≤ c := by
      intro x hx
      rw [abs_mul]
      have h01 := hχ01 x
      calc |χ x| * |ζ x (w x)| ≤ 1 * c :=
            mul_le_mul (by rw [abs_of_nonneg h01.1]; exact h01.2) hx (abs_nonneg _) zero_le_one
        _ = c := one_mul c
    have hint2 : IntegrableOn (fun x => χ x * ζ x (w x)) {x | g x < s} ν :=
      Measure.integrableOn_of_bounded hνG.ne (hχc.aestronglyMeasurable.mul hF)
        (ae_restrict_of_ae (hFb.mono fun x hx => by rw [Real.norm_eq_abs]; exact hχF x hx))
    have hsmul : ∀ x, ζ x (χ x • w x) = χ x * ζ x (w x) := fun x => by
      rw [map_smul, smul_eq_mul]
    have h2 : ∫ x, ζ x (χ x • w x) ∂ν = ∫ x in {x | g x < s}, χ x * ζ x (w x) ∂ν := by
      simp_rw [hsmul]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have : s ≤ g x := not_lt.1 hx
        rw [hχ0 x this, zero_mul]).symm
    rw [h2, ← integral_sub hint1 hint2]
    have h3 : ∫ x in {x | g x < s}, (ζ x (w x) - χ x * ζ x (w x)) ∂ν =
        ∫ x in {x | r < g x ∧ g x < s}, (ζ x (w x) - χ x * ζ x (w x)) ∂ν := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hGm (fun x hx => hx.2)
      intro x hx
      have : g x ≤ r := by
        by_contra h
        exact hx.2 ⟨lt_of_not_ge h, hx.1⟩
      rw [hχ1 x this]
      ring
    rw [h3, ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const_ae
      (lt_of_le_of_lt (measure_mono fun x hx => hx.2) hνG)
    apply ae_restrict_of_ae
    filter_upwards [hFb] with x hx
    rw [Real.norm_eq_abs, show ζ x (w x) - χ x * ζ x (w x) = (1 - χ x) * ζ x (w x) by ring,
      abs_mul]
    have h01 := hχ01 x
    calc |1 - χ x| * |ζ x (w x)| ≤ 1 * c :=
          mul_le_mul (by rw [abs_of_nonneg (by linarith [h01.2])]; linarith [h01.1]) hx
            (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  -- Step 3: the ε-argument.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (3 * (c + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ₁, hδ₁, hμδ₁⟩ :
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ μ {x | s - δ₁ < g x ∧ g x < s} ≤ ENNReal.ofReal η := by
    let S : ℕ → Set (Euclid P) := fun i => {x | s - 1 / ((i : ℝ) + 1) < g x ∧ g x < s}
    have hSm : ∀ i, NullMeasurableSet (S i) μ := fun i =>
      ((measurableSet_lt measurable_const hg.measurable).inter hGm).nullMeasurableSet
    have hSanti : Antitone S := by
      intro i k hik x hx
      refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hik 1)
      linarith
    have hSfin : ∃ i, μ (S i) ≠ ∞ :=
      ⟨0, (lt_of_le_of_lt (measure_mono fun x hx => hx.2) hμG).ne⟩
    have hinter : (⋂ i, S i) = ∅ := by
      ext x
      simp only [S, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
      by_cases hxs : g x < s
      · obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.2 hxs)
        exact ⟨i, fun h => by linarith [h.1]⟩
      · exact ⟨0, fun h => hxs h.2⟩
    have ht := tendsto_measure_iInter_atTop hSm hSanti hSfin
    rw [hinter, measure_empty] at ht
    have hev := (ENNReal.tendsto_nhds_zero.1 ht) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
    obtain ⟨i, hi⟩ := hev.exists
    exact ⟨1 / ((i : ℝ) + 1), by positivity, hi⟩
  obtain ⟨δ₂, hδ₂, hev₂⟩ := hconc (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  have hδ' : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0'⟩ : ∃ χ : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, g x ≤ s - min δ₁ δ₂ → χ x = 1) ∧
      (∀ x, s - min δ₁ δ₂ / 2 ≤ g x → χ x = 0) := by
    obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (modelWithCornersSelf ℝ (Euclid P)) (n := ⊤) (s := {x | g x ≤ s - min δ₁ δ₂})
      (t := {x | g x < s - min δ₁ δ₂ / 2}) (isClosed_le hg continuous_const)
      (by
        rw [(isOpen_lt hg continuous_const).interior_eq]
        intro x (hx : g x ≤ s - min δ₁ δ₂)
        show g x < s - min δ₁ δ₂ / 2
        linarith)
    refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, hf01, fun x hx => hf1.self_of_nhdsSet x hx,
      fun x hx => hf0 x (by simp only [mem_setOf_eq, not_lt]; exact hx)⟩
  have hχ0 : ∀ x, s ≤ g x → χ x = 0 := fun x hx => hχ0' x (by linarith)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by rw [hwdef]; exact ω.property.1.1
  have hwcs : HasCompactSupport w := by rw [hwdef]; exact ω.property.1.2
  have hwU : tsupport w ⊆ U := by rw [hwdef]; exact ω.property.2
  have hsupp : support (fun x => χ x • w x) ⊆ support w := by
    intro x hx h0
    apply hx
    simp only [h0, smul_zero]
  have h1 : IsSmoothForm (fun x => χ x • w x) := hχs.smul hws
  have h2 : HasCompactSupport (fun x => χ x • w x) :=
    hwcs.mono' (hsupp.trans (subset_tsupport w))
  have h3 : tsupport (fun x => χ x • w x) ⊆ U := (closure_mono hsupp).trans hwU
  have hmem : (fun x => χ x • w x) ∈ TestFormOn U d := ⟨⟨h1, h2⟩, h3⟩
  let χω : TestFormOn U d := ⟨fun x => χ x • w x, hmem⟩
  have hconvχ := hconv χω
  rw [Metric.tendsto_atTop] at hconvχ
  obtain ⟨N₁, hN₁⟩ := hconvχ η hη
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev₂
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  have hj₁ : N₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj₂ : N₂ ≤ j := le_trans (le_max_right _ _) hj
  have e1 := key (μs j) (ξs j) χ (s - min δ₁ δ₂) (hμsG j) (hξsm j) (hξsb j) hχs.continuous hχ01
    hχ1 hχ0
  have e2 := key μ ξ χ (s - min δ₁ δ₂) hμG hξm hξb hχs.continuous hχ01 hχ1 hχ0
  have hm1 : (μs j).real {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ η := by
    have : μs j {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ ENNReal.ofReal η :=
      le_trans (measure_mono (show {x | s - min δ₁ δ₂ < g x ∧ g x < s} ⊆
          {x | s - δ₂ ≤ g x ∧ g x ≤ s} from
          fun x hx => ⟨by linarith [hx.1, min_le_right δ₁ δ₂], hx.2.le⟩)) (hN₂ j hj₂)
    exact ENNReal.toReal_le_of_le_ofReal hη.le this
  have hm2 : μ.real {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ η := by
    have : μ {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ ENNReal.ofReal η :=
      le_trans (measure_mono (show {x | s - min δ₁ δ₂ < g x ∧ g x < s} ⊆
          {x | s - δ₁ < g x ∧ g x < s} from
          fun x hx => ⟨by linarith [hx.1, min_le_left δ₁ δ₂], hx.2⟩)) hμδ₁
    exact ENNReal.toReal_le_of_le_ofReal hη.le this
  have h3 : dist (Ts j χω) (T χω) < η := hN₁ j hj₁
  have hTsχ : Ts j χω = ∫ x, ξs j x (χ x • w x) ∂(μs j) := hTs j χω
  have hTχ : T χω = ∫ x, ξ x (χ x • w x) ∂μ := hT χω
  rw [Real.dist_eq, hTsχ, hTχ] at h3
  rw [Real.dist_eq, hTs' j ω, hT' ω, ← hwdef]
  have hc1 := mul_le_mul_of_nonneg_left hm1 hc0
  have hc2 := mul_le_mul_of_nonneg_left hm2 hc0
  have habs := abs_sub_le (∫ x in {x | g x < s}, ξs j x (w x) ∂(μs j))
    (∫ x, ξs j x (χ x • w x) ∂(μs j)) (∫ x in {x | g x < s}, ξ x (w x) ∂μ)
  have habs2 := abs_sub_le (∫ x, ξs j x (χ x • w x) ∂(μs j)) (∫ x, ξ x (χ x • w x) ∂μ)
    (∫ x in {x | g x < s}, ξ x (w x) ∂μ)
  rw [abs_sub_comm (∫ x, ξ x (χ x • w x) ∂μ)] at habs2
  have hfin : (2 * c + 1) * η < ε := by
    rw [hηdef]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

## Key steps

1. Bound |ω(x)| ≤ c, using that the coefficient norm of ω is continuous and compactly supported.
2. Cutoff estimate: |∫_G⟨ω,ζ⟩dν - ∫⟨χω,ζ⟩dν| ≤ c·ν({r < g < s}) for continuous χ ∈ [0,1] with χ = 1 on {g ≤ r} and χ = 0 on {g ≥ s}.
3. Continuity from above gives δ₁ with μ({s-δ₁<g<s}) ≤ η; (H6) gives δ₂ with μ_j({s-δ₂≤g≤s}) ≤ η for large j.
4. A smooth Urysohn cutoff χ (= 1 on {g ≤ s-δ'}, = 0 on {g ≥ s-δ'/2}) gives χω ∈ 𝒟^d(U), and T_j(χω) → T(χω).
5. Triangle inequality: |T'_j(ω) - T'(ω)| ≤ (2c+1)η < ε for large j, so T'_j ⇀ T'.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'cmc_fcl|cmc_fc_localize|weakConverges_sublevel' local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n 'theorem integral_withDensity_eq_integral_smul |theorem exists_contMDiffMap_one_nhds_of_subset_interior|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem tendsto_measure_iInter_atTop|theorem norm_setIntegral_le_of_norm_le_const_ae|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem enorm_integral_le_lintegral_enorm|theorem restrict_withDensity|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem lipschitz_infDist_pt|theorem _root_.IsCompact.cthickening' local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -rn 'GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|GeometricCurrentOn.VanishesOn|restrictDomain' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; cat Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `python3 over dag.json: statuses and frozen types of the flat_convergence siblings (cmc_fc_good_slice); accepted declarations mentioning IMRep/massOn/support (dor_ims_action_eq_integral, dor_ims_massOn_le_measure, rsd_cmr_support_subset_of_vanish, rsd_mw_wlm_eval_eq_integral_restrict); lcmp_massOn_le_add_of_eval_eq (decomposing under another parent); collision check of the cmc_fcl_* names (none)`
- `sed /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, decomposition workspace publication) and store.py ensure`
- `sed -n 2028,2110p book/chapter-06.txt (Simon 7.2; localization sentence at lines 2090-2096)`
- `lake env lean /tmp/lczdec/T1.lean, /tmp/lczdec/check/T2.lean (#check probes of the GMT.Ch07.Submission import closure; smooth Urysohn cutoff via exists_contMDiffMap_one_nhds_of_subset_interior), /tmp/lczdec/check/T6.lean-T8.lean (elaboration-time probes)`
- `lake env lean /tmp/lczdec/Assembly.lean (child stubs, cmc_fc_good_slice stub and the assembly of the exact cmc_fc_localize type: no errors)`
- `lake env lean /tmp/lczdec/Full.lean (six child proofs plus the assembly; #print axioms of the children: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/tmp/lczdec/Assembly.lean`
- `/tmp/lczdec/Full.lean`

The snapshot is project b4d606db with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot contains no cmc_fcl_* or cmc_fc_localize declaration (rg: no match). SimonGMT Chapter06 supplies massOn, mass, support, zeroRegion, massOn_mono and le_massOn, but none of the seven child facts. The pinned Mathlib supplies every tool the compiled child proofs use, all inside the import closure of GMT.Ch07.Submission: integral_withDensity_eq_integral_smul, restrict_withDensity, Measure.restrict_restrict, withDensity_absolutelyContinuous, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, lipschitz_infDist_pt, enorm_integral_le_lintegral_enorm, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const_ae, Measure.integrableOn_of_bounded, tendsto_measure_iInter_atTop, exists_contMDiffMap_one_nhds_of_subset_interior and contMDiff_iff_contDiff. Among accepted DAG declarations, rsd_cmr_support_subset_of_vanish is reused with its identical frozen type. lcmp_massOn_le_add_of_eval_eq is still active under another parent, so it is not shared and cmc_fcl_massOn_le_add is introduced instead. No cmc_fcl_* name collides with any of the 668 DAG names. All seven child types elaborate. The exact frozen type of cmc_fc_localize compiles from the seven children and cmc_fc_good_slice. The six new children compile using only the axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
