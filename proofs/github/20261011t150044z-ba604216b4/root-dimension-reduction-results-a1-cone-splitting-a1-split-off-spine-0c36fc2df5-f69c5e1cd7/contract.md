<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1.coarea_of_pieces-a1 -->

## Theorem `Submission.dimred_cs_sos_sc_coarea_of_pieces`

Setting: P, n ∈ ℕ and L ⊆ ℝ^P a linear subspace with d := dim L < n; m := n − d ≥ 1. p := L.starProjection is the orthogonal projection onto L, viewed as a map ℝ^P → ℝ^P; H^k := μHE[k]; for t ∈ L, M_t := M ∩ p⁻¹(t) = M ∩ {x : L.starProjection x = t}.
Hypotheses on M ⊆ ℝ^P:
- (H1) M is Borel;
- (H2) (bi-Lipschitz pieces) there are maps F_i : ℝ^n → ℝ^P, sets B_i ⊆ ℝ^n and reals m_i (i ∈ ℕ) such that:
 - each F_i is Lipschitz, each B_i is Borel and m_i > 0;
 - m_i|a − a'| ≤ |F_i(a) − F_i(a')| for a, a' ∈ B_i;
 - F_i is differentiable at every a ∈ B_i with injective derivative;
 - each F_i(B_i) is Borel and contained in M, and the sets F_i(B_i) are pairwise disjoint;
 - H^n(M ∖ ⋃_i F_i(B_i)) = 0;
- (H3) H^n(M ∩ K) < ∞ for every compact K;
- (H4) for H^n-a.e. x ∈ M there is a subspace Q with HasApproximateTangentSpaceAt n M x Q and L ⊆ Q.
Conclusions:
(i) For H^d⌞L-a.e. t, M_t is countably m-rectifiable. Moreover, for H^m-a.e. x ∈ M_t and every subspace Q with HasApproximateTangentSpaceAt n M x Q, HasApproximateTangentSpaceAt m M_t x (Q ∩ L^⊥).
(ii) For every Borel g : ℝ^P → [0, ∞], t ↦ ∫_{M_t} g dH^m is a.e.-measurable for H^d⌞L, and ∫_M g dH^n = ∫_L (∫_{M_t} g dH^m) dH^d(t).
This is the selected spine coarea theorem with "M countably n-rectifiable" replaced by the piece decomposition that bilipschitz_pieces produces from it.

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1.coarea_of_pieces-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4876

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4589, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4579, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7843

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_cs_sos_sc_coarea_of_pieces`

```lean
∀ (P n : ℕ) (L : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), Module.finrank ℝ L < n → MeasurableSet M → (∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0) → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ L ≤ Q) → (∀ᵐ t ∂(μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))), CountablyRectifiable (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) ∧ ∀ᵐ x ∂(μHE[n - Module.finrank ℝ L].restrict (M ∩ {x | L.starProjection x = t})), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) x (Q ⊓ Lᗮ)) ∧ ∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L]) (μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))) ∧ ∫⁻ x in M, g x ∂μHE[n] = ∫⁻ t in (L : Set (Euclid P)), ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L] ∂μHE[Module.finrank ℝ L]
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1.coarea_of_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–8 and (T4) of the selected node's supplied proof (Federer 3.2.22 for p restricted to M, with coarea factor 1). This is the slicing step behind Simon Ch. 7, Lemma 3.5 (chapter-07.txt lines 407–418, "the proof of which is left to the reader"). (H2) replaces supplied step 1 and the first half of step 2.
Context (not part of the numbered proof). The steps below follow the accepted Lean proof of the identical-type declaration Submission.idtp_fons_cs_sos_spine_coarea (candidate d35a0320a1655c5aa9479b8fdfc9adcba5c25d5b). Its GMT/Ch07/Submission.lean lines 6555–7356 hold an inline `have master` over abstract spaces V, F, B. Taken verbatim, that block proves exactly this child's frozen type in the environment of the accepted candidate 2626c7a (d35a0320 is 2626c7a plus only that theorem), as follows:
  intro P n L M hdn hM hpieces hloc htan
  have master : … := <d35a0320 GMT/Ch07/Submission.lean lines 6555–7356, verbatim>
  exact master (Euclid n) (Euclid P) (Euclid (n - Module.finrank ℝ L)) n (Module.finrank ℝ L)
    (n - Module.finrank ℝ L) L M finrank_euclideanSpace_fin finrank_euclideanSpace_fin rfl hdn rfl
    hM hloc htan hpieces (Submission.ptd_piece_image_measurable_ae_pullback P n)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P n G Y K
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hdn) hG hY hYl)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P _ G Y K
      (Nat.sub_pos_of_lt hdn) hG hY hYl)
    (Submission.dpf_itt_ae_of_ae_pieces P _)
The argument is uniform in d ≥ 0. For d = 0, L = {0}, p = 0, M_0 = M and H^0⌞L is the unit mass at 0.
Imports. The area formula (A1), (A2) and LinearMap.normDet live in Poincare.SimonGMT.Chapter02.AreaLipschitz and Mathlib.Analysis.InnerProductSpace.NormDet. Both are outside the contract import closure. This leaf gets them through the dependency merge of its sibling tangent_along_lipschitz, whose accepted candidate 2626c7a33b0710ef02dabb5fabccd7f228531ad1 has `import Poincare.SimonGMT.Chapter02.AreaLipschitz` and already contains the other reused declarations. Everything else below is in scope after `import GMT.Ch07.Submission`.

Notation. V := ℝ^n, W := ℝ^P, B := ℝ^m (m = n − d ≥ 1, so n = d + m), H^k := μHE[k], p := L.starProjection, q := I − p = Lᗮ.starProjection, M_t := M ∩ p⁻¹(t). For a linear map D between finite-dimensional inner-product spaces, J(D) := normDet D = det(D*D)^{1/2} ≥ 0. For a map G, JG(u) := J(DG(u)) (SimonGMT areaJacobianAt) and Reg G := {u : G is differentiable at u and DG(u) is injective}.
Siblings used.
- (S1) piece_pullback, in dimension n. Let G : ℝ^n → ℝ^P be Lipschitz, S ⊆ ℝ^n Borel, c > 0 with c|a − a'| ≤ |G(a) − G(a')| on S. Then G(S) is Borel, and every property that holds H^n⌞G(S)-a.e. holds at G(b) for L^n-a.e. b ∈ S.
- (S2) ae_transfer, in dimension m. Let S ⊆ ℝ^P be Borel, G_q : ℝ^m → ℝ^P Lipschitz and T_q ⊆ ℝ^m (q ∈ ℕ) with H^m(S ∖ ⋃_q G_q(T_q)) = 0. If a property π satisfies π(G_q(b)) for L^m-a.e. b ∈ T_q, for every q, then π holds H^m-a.e. on S.
- (S3) tangent_along_lipschitz, for k = n and k = m (both ≥ 1). Let G : ℝ^k → ℝ^P be Lipschitz and Y ⊆ ℝ^P Borel with H^k(Y ∩ C) < ∞ for every compact C. Then for L^k-a.e. u: if G(u) ∈ Y, G is differentiable at u and DG(u) is injective, then HasApproximateTangentSpaceAt k Y (G u) (DG(u)(ℝ^k)).
Library facts.
- (A1) Area formula, SimonGMT weighted_area_formula_lipschitz_injOn. Let G : E → E' be Lipschitz between finite-dimensional inner-product spaces, S ⊆ E Borel with G injective on S, and g ≥ 0 any function. Then ∫_{G(S)} g dH^{dim E} = ∫_S JG(u) g(G(u)) du. Also u ↦ JG(u) is measurable (measurable_areaJacobianAt).
- (A2) Sard-type statement, SimonGMT area_image_compl_regularSet_eq_zero: H^{dim E}(G(S ∖ Reg G)) = 0 for G Lipschitz.
- (A3) Lipschitz image bound, euclideanHausdorffMeasure_image_le_of_lipschitzOn: H^k(G(A)) ≤ Lip(G)^k H^k(A).
- (A4) Mathlib NormDet:
 - J(f∘g) = J(f)J(g) if dim(source g) = dim(target g) (normDet_comp_of_finrank_eq);
 - J of a linear isometry is 1;
 - J(U) = |det U| for an endomorphism U;
 - J(f)² = det Gram(f(b_i)) for an orthonormal basis b of the source (normDet_sq_eq_det_gram).
- (A5) Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt.
- (A6) Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn); LipschitzOnWith.extend_finite_dimension; uniqueness of approximate tangent spaces (HasApproximateTangentSpaceAt.unique); LinearMap.exists_antilipschitzWith.
- (A7) Fubini/Tonelli (lintegral_prod, Measure.ae_ae_of_ae_prod, MeasurePreserving.lintegral_comp).
- (A8) H^k = Lebesgue measure on a k-dimensional space (InnerProductSpace.euclideanHausdorffMeasure_eq_volume), and the image of Lebesgue measure on L under the inclusion L ⊆ W is H^d⌞L (Isometry.map_euclideanHausdorffMeasure).
- (A9) μHE[k] = c_k μH[k] with 0 < c_k < ∞ (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero); Measure.hausdorffMeasure_apply; Measure.hausdorffMeasure_le_liminf_tsum; Measure.addHaar_closedBall'; Fatou (lintegral_liminf_le).

0. (Coordinates.)
- dim V = n = dim(L ×₂ B), so there is a linear isometry Θ : V → L ×₂ B (L² product). Put π₁(z) := (Θz)_L. This is a continuous linear map V → W with values in L, so p(π₁ z) = π₁ z.
- Put j(s) := Θ⁻¹(0, s) for s ∈ B. Then j is linear and injective, and Θ⁻¹(t, s) = Θ⁻¹(t, 0) + j(s).
- (t, s) ↦ Θ⁻¹(t, s) carries the product of the Lebesgue measures of L and B to Lebesgue measure on V.
- By (A8), H^n = Lebesgue measure on V and H^m = Lebesgue measure on B, and Lebesgue measure on L is carried by the inclusion to H^d⌞L.

1. (Jacobian identity.) Let D : V → W be linear with p(Dv) = π₁(v) for all v and L ⊆ D(V). Put Y := D∘j : B → W. Claim: J(D) = J(Y) and Y(B) = D(V) ∩ L^⊥.
 (a) For s ∈ B, p(Ys) = π₁(js) = (Θ js)_L = 0. So Y(B) ⊆ L^⊥.
 (b) By linearity, D(Θ⁻¹(t, s)) = D(Θ⁻¹(t, 0)) + Y(s).
 (c) Let τ ∈ L. Pick v with Dv = τ. Then (Θv)_L = π₁(v) = p(τ) = τ. By (b), τ = D(Θ⁻¹(τ, 0)) + Y((Θv)_B), so D(Θ⁻¹(τ, 0)) − τ = Y(−(Θv)_B) ∈ Y(B).
 (d) The linear map τ ↦ D(Θ⁻¹(τ, 0)) − τ, from L to Y(B), therefore lifts through the surjection Y : B → Y(B). This gives a linear β : L → B with Y(βτ) = D(Θ⁻¹(τ, 0)) − τ.
 (e) Let U(t, s) := (t, s + βt). Then U is block unipotent, and det U = 1. Indeed, with N(t, s) := (0, βt), det(I + N) = det(I + (fst)(inr∘β)) = det(I_L + 0) = 1.
 (f) Let D₀(t, s) := t + Y(s). Then D(Θ⁻¹(t, s)) = t + Y(βt) + Y(s) = D₀(U(t, s)), so D∘Θ⁻¹ = D₀∘U.
 (g) Take orthonormal bases (e_a) of L and (f_b) of B; the vectors (e_a, 0), (0, f_b) form an orthonormal basis of L ×₂ B. Then D₀(e_a, 0) = e_a and D₀(0, f_b) = Y f_b ∈ L^⊥. So the Gram matrix of D₀ is block diagonal, diag(I, Gram(Y f_b)), and (A4) gives J(D₀)² = J(Y)². Hence J(D₀) = J(Y), both being ≥ 0.
 (h) By (A4), J(D) = J(D∘Θ⁻¹) = J(D₀∘U) = J(D₀)|det U| = J(Y), since Θ⁻¹ is an isometry between spaces of equal dimension.
 (i) Y(B) ⊆ D(V) ∩ L^⊥ by (a). Conversely, let y = Dv ∈ L^⊥. Then π₁(v) = p(y) = 0, so v = j((Θv)_B) and y = Y((Θv)_B).
2. (Coercivity constant.) For continuous linear A : V → W, let K_A := ker(p∘A) and π_{K_A} its orthogonal projection.
 - The linear map v ↦ (p(Av), π_{K_A} v) is injective: if both components vanish, then v ∈ K_A, so v = π_{K_A} v = 0.
 - Hence (LinearMap.exists_antilipschitzWith) there is C_A > 0 with |v| ≤ C_A·max(|p(Av)|, |π_{K_A} v|) for all v.
3. (One approximately linear piece.) Claim: let F' : V → W be Lipschitz, T ⊆ V Borel, and m' > 0 with m'|a − a'| ≤ |F'(a) − F'(a')| on T. Let A' : V → W be continuous linear with |F'(a) − F'(a') − A'(a − a')| ≤ (2C_{A'})⁻¹|a − a'| on T, and assume L ⊆ A'(V) if T ≠ ∅. Then there are a Lipschitz H' : V → W, a Borel Ω' ⊆ V and c > 0 such that:
 - c|z − z'| ≤ |H'(z) − H'(z')| on Ω';
 - H'(Ω') = F'(T);
 - p(H'(z)) = π₁(z) for every z ∈ V.
 Proof.
 - If T = ∅, take H' := π₁, Ω' := ∅ and c := 1.
 - Otherwise, p∘A' maps V onto L: for ℓ = A'w ∈ L, p(A'w) = ℓ. So dim K := dim K_{A'} = n − d = m. Fix a linear isometry κ : K → B.
 - Put Λ(x, y) := Θ⁻¹(p(x), κ(π_K y)). This is continuous linear W × V → V. Because Θ⁻¹ and κ are isometries, |p(x)| ≤ |Λ(x, y)| and |π_K y| ≤ |Λ(x, y)|.
 - Put Φ(u) := Λ(F'(u), u). Φ is Lipschitz with some constant K_Φ, and Φv − Φw = Λ(F'v − F'w, v − w).
 - Let v, w ∈ T and C := C_{A'}. Since p is 1-Lipschitz, |p(A'(v − w))| ≤ |p(F'v − F'w)| + |F'v − F'w − A'(v − w)| ≤ |Φv − Φw| + (2C)⁻¹|v − w|. Also |π_K(v − w)| ≤ |Φv − Φw|.
 - By step 2, |v − w| ≤ C|Φv − Φw| + |v − w|/2. Hence (★) |v − w| ≤ 2C|Φv − Φw|.
 - By (★), Φ is injective on T. So Ω' := Φ(T) is Borel (A6), and Φ has an inverse ψ : Ω' → T.
 - By (★), F'∘ψ is Lipschitz on Ω' with constant 2C·Lip(F'). Extend it to a Lipschitz h : V → W (A6), and set H'(z) := π₁(z) + q(h(z)). Then H' is Lipschitz and p(H'z) = π₁ z.
 - For u ∈ T, π₁(Φu) = (ΘΦu)_L = p(F'u) and h(Φu) = F'(u). So H'(Φu) = p(F'u) + q(F'u) = F'(u), and H'(Ω') = F'(T).
 - Finally, for u, u' ∈ T we have |Φu − Φu'| ≤ (K_Φ + 1)|u − u'|. So c := m'(K_Φ + 1)⁻¹ gives c|Φu − Φu'| ≤ m'|u − u'| ≤ |H'(Φu) − H'(Φu')|.
4. (Adapted pieces.) Let (F_i, B_i, m_i) be the pieces of (H2).
 (a) Good parameters. Fix i. By (H4) and F_i(B_i) ⊆ M, the property "∃Q with HasApproximateTangentSpaceAt n M x Q and L ⊆ Q" holds H^n⌞F_i(B_i)-a.e. By (S1), it holds at F_i(a) for L^n-a.e. a ∈ B_i.
  - By (S3) with k = n and Y := M (Borel by (H1), locally H^n-finite by (H3)), for a.e. a ∈ B_i, M has approximate tangent space DF_i(a)(V) at F_i(a). Here F_i(a) ∈ M, F_i is differentiable at a and DF_i(a) is injective.
  - By uniqueness, Q = DF_i(a)(V), so L ⊆ DF_i(a)(V) for a.e. a ∈ B_i.
  - Remove a Borel null set containing the exceptional points (toMeasurable). This gives a Borel G_i ⊆ B_i with L^n(B_i ∖ G_i) = 0 and L ⊆ DF_i(a)(V) for all a ∈ G_i.
 (b) Partition. Apply (A5) to F_i on G_i (where F_i is differentiable) with tolerance r(A) := (2C_A)⁻¹ > 0. This gives pairwise disjoint Borel sets t_{i,k} covering G_i and continuous linear maps A_{i,k} such that:
  - |F_i(a) − F_i(a') − A_{i,k}(a − a')| ≤ (2C_{A_{i,k}})⁻¹|a − a'| on G_i ∩ t_{i,k};
  - if G_i ≠ ∅, then A_{i,k} = DF_i(y) for some y ∈ G_i, so L ⊆ A_{i,k}(V) by (a).
 (c) Reparametrize. Index q ↔ (i, k) through Nat.unpair. Step 3 applies with F' := F_i, T := G_i ∩ t_{i,k} ⊆ B_i, m' := m_i and A' := A_{i,k}. It gives H_q Lipschitz, Ω_q Borel and c_q > 0 such that:
  - H_q is c_q-bi-Lipschitz from below on Ω_q;
  - H_q(Ω_q) = F_i(G_i ∩ t_{i,k}) ⊆ F_i(B_i) ⊆ M;
  - p∘H_q = π₁ on V.
 (d) Disjointness. Let q ≠ q'. If i ≠ i', the images lie in the disjoint sets F_i(B_i) and F_{i'}(B_{i'}). If i = i', then k ≠ k'. Since F_i is injective on B_i (lower bound) and t_{i,k} ∩ t_{i,k'} = ∅, the images are disjoint.
 (e) Null remainder. Let Z := M ∖ ⋃_q H_q(Ω_q). If x ∈ Z ∩ F_i(B_i), say x = F_i(a), then a ∉ G_i, since otherwise a ∈ some t_{i,k}. So Z ⊆ (M ∖ ⋃_i F_i(B_i)) ∪ ⋃_i F_i(B_i ∖ G_i).
  - The first set is H^n-null by (H2).
  - By (A3) and (A8), H^n(F_i(B_i ∖ G_i)) ≤ Lip(F_i)^n L^n(B_i ∖ G_i) = 0.
  - Hence H^n(Z) = 0.
5. (One piece.) Fix q and write H := H_q, Ω := Ω_q.
 (a) H is injective on Ω. By (S1) with c := c_q, H(Ω) is Borel and H^n⌞H(Ω)-a.e. properties pull back to L^n-a.e. w ∈ Ω.
 (b) Good points. For L^n-a.e. w ∈ Ω:
  - H is differentiable at w and DH(w) is injective. By (A2), H^n(H(Ω ∖ Reg H)) = 0. Pulling back "x ∉ H(Ω ∖ Reg H)" by (a) gives w ∈ Reg H.
  - M has approximate tangent space R_w := DH(w)(V) at H(w), and L ⊆ R_w. This follows from (S3) with k = n and Y = M, from (H4) pulled back by (a), and from uniqueness, as in 4(a).
 (c) Where H is differentiable, p∘DH(w) = π₁. Indeed p∘H = π₁ is linear, and D(p∘H)(w) = p∘DH(w).
 (d) Slices. For t ∈ L put H_t(s) := H(Θ⁻¹(t, s)) and Ω_t := {s ∈ B : Θ⁻¹(t, s) ∈ Ω}. Since s ↦ Θ⁻¹(t, 0) + j(s) is affine with derivative j:
  - H_t is Lipschitz and Ω_t is Borel;
  - if H is differentiable at w = Θ⁻¹(t, s), then DH_t(s) = DH(w)∘j;
  - H_t is injective on Ω_t;
  - H_t(Ω_t) = H(Ω) ∩ p⁻¹(t). For ⊆: p(H(Θ⁻¹(t, s))) = π₁(Θ⁻¹(t, s)) = t. For ⊇: if z ∈ Ω and p(Hz) = t, then (Θz)_L = t, so Hz = H_t((Θz)_B) with (Θz)_B ∈ Ω_t.
 (e) Fubini. By step 0 and (A7) applied to the full-measure set of w satisfying "w ∈ Ω ⇒ (b)": for L^d-a.e. t ∈ L and L^m-a.e. s, if s ∈ Ω_t, then (b) holds at w = Θ⁻¹(t, s).
 (f) At such (t, s), step 1 applies to D := DH(w). Its hypotheses hold by (c) and (b). It gives:
  - JH_t(s) = J(DH(w)∘j) = JH(w);
  - (DH(w)∘j)(B) = R_w ∩ L^⊥;
  - DH_t(s) = DH(w)∘j is injective.
 (g) Coarea on the piece. Let g ≥ 0 be Borel and f := 1_Ω·JH·(g∘H), a Borel function on V.
  - By (A1) for H on Ω, step 0 and Tonelli: ∫_{H(Ω)} g dH^n = ∫_V f = ∫_L ∫_B f(Θ⁻¹(t, s)) ds dt.
  - For t as in (e), (A1) for H_t on Ω_t (dim B = m) together with (d) and (f) gives ∫_{H(Ω)∩p⁻¹(t)} g dH^m = ∫_{Ω_t} JH_t(s) g(H_t(s)) ds = ∫_B f(Θ⁻¹(t, s)) ds.
  - The middle function of t is measurable by Tonelli.
  - Transport to H^d⌞L by step 0. Then t ↦ ∫_{H(Ω)∩p⁻¹(t)} g dH^m is a.e.-measurable for H^d⌞L, and ∫_{H(Ω)} g dH^n = ∫_L ∫_{H(Ω)∩p⁻¹(t)} g dH^m dH^d(t).
 (h) Record for step 9: for H^d⌞L-a.e. t and L^m-a.e. s ∈ Ω_{q,t}, with w = Θ⁻¹(t, s):
  - H_{q,t} is differentiable at s with injective derivative DH_q(w)∘j;
  - M has approximate tangent space R_w at H_q(w);
  - (DH_q(w)∘j)(B) = R_w ∩ L^⊥.
6. (Null sets have null slices.) Claim: if H^n(Z) = 0, then H^m(Z ∩ p⁻¹(t)) = 0 for H^d⌞L-a.e. t.
 - By (A9), μH[n](Z) = 0. Fix j ∈ ℕ. Since the 1/(j+1)-premeasure of Z is 0 (hausdorffMeasure_apply), there is a cover (C_{j,k})_k of Z with diam C_{j,k} ≤ 1/(j+1) and Σ_k (diam C_{j,k})^n < 1/(j+1); only nonempty C_{j,k} count in the sum.
 - Choose x_{j,k} with p(C_{j,k}) ⊆ closedBall(p(x_{j,k}), diam C_{j,k}); this works because p is 1-Lipschitz. Put ψ_j(t) := Σ_k 1_{closedBall(p(x_{j,k}), diam C_{j,k})}(t)·(diam C_{j,k})^m, a Borel function.
 - For every t, the sets C_{j,k} ∩ p⁻¹(t) cover Z ∩ p⁻¹(t), and their diameters are ≤ 1/(j+1) → 0. A nonempty one has t in the k-th ball and diameter ≤ diam C_{j,k}; an empty one contributes 0 (m ≥ 1). So hausdorffMeasure_le_liminf_tsum gives μH[m](Z ∩ p⁻¹(t)) ≤ liminf_j ψ_j(t).
 - Let c_B be the Lebesgue measure of the unit ball of L. By step 0 and addHaar_closedBall', ∫_L ψ_j dH^d ≤ c_B Σ_k (diam C_{j,k})^d (diam C_{j,k})^m ≤ c_B/(j+1), since d + m = n.
 - Fatou gives ∫_L liminf_j ψ_j dH^d = 0. So liminf_j ψ_j(t) = 0, hence μH[m](Z ∩ p⁻¹(t)) = 0 and H^m(Z ∩ p⁻¹(t)) = 0, for H^d-a.e. t ∈ L.
7. (Summation: proof of (ii).)
 - If A_q ⊆ S are Borel and pairwise disjoint with H^k(S ∖ ⋃_q A_q) = 0, then ∫_S g dH^k = Σ_q ∫_{A_q} g dH^k. This holds by a.e.-equality of S and ⋃_q A_q and countable additivity (lintegral_iUnion).
 - Apply this to S := M, A_q := H_q(Ω_q) and remainder Z (steps 4 and 5(a)). This gives ∫_M g dH^n = Σ_q ∫_{H_q(Ω_q)} g dH^n.
 - By step 6, H^m(Z ∩ p⁻¹(t)) = 0 for a.e. t. For such t, apply it to S := M_t and A_q := H_q(Ω_q) ∩ p⁻¹(t), whose remainder is Z ∩ p⁻¹(t). This gives ∫_{M_t} g dH^m = Σ_q ∫_{H_q(Ω_q)∩p⁻¹(t)} g dH^m.
 - So t ↦ ∫_{M_t} g dH^m is a.e. equal to a countable sum of a.e.-measurable functions (5(g)), and is therefore a.e.-measurable.
 - Finally, by 5(g) and lintegral_tsum, ∫_M g dH^n = Σ_q ∫_L ∫_{H_q(Ω_q)∩p⁻¹(t)} g dH^m dH^d = ∫_L ∫_{M_t} g dH^m dH^d. This is (ii).
8. (Local finiteness of slices.) For j ∈ ℕ, apply (ii) to g := 1_{closedBall(0, j)}. Then ∫_L H^m(M_t ∩ closedBall(0, j)) dH^d = H^n(M ∩ closedBall(0, j)) < ∞, by (H3). So for a.e. t, H^m(M_t ∩ C) < ∞ for every compact C, since each C lies in some closedBall(0, j).
9. (Proof of (i).) Fix t ∈ L with the following properties, which hold together for a.e. t:
 - 5(h) holds for every q;
 - H^m(Z ∩ p⁻¹(t)) = 0 (step 6);
 - M_t is locally H^m-finite (step 8).
 M_t is Borel by (H1).
 - Rectifiability. M_t ⊆ (Z ∩ p⁻¹(t)) ∪ ⋃_q H_{q,t}(B), using 5(d). Each H_{q,t} : ℝ^m → ℝ^P is Lipschitz. So M_t is countably m-rectifiable, with exceptional set Z ∩ p⁻¹(t).
 - Tangent planes. Let q ∈ ℕ. By 5(h), for a.e. s ∈ Ω_{q,t}, H_{q,t} is differentiable at s with injective derivative.
  - By (S3) with k = m, G := H_{q,t} and Y := M_t (Borel, locally H^m-finite), for a.e. s ∈ Ω_{q,t}, M_t has approximate tangent space (DH_q(w)∘j)(B) = R_w ∩ L^⊥ at x = H_{q,t}(s). This uses x ∈ H_q(Ω_q) ∩ p⁻¹(t) ⊆ M_t.
  - By 5(h), M has approximate tangent space R_w at x. Any Q with HasApproximateTangentSpaceAt n M x Q equals R_w by uniqueness. So HasApproximateTangentSpaceAt m M_t x (Q ⊓ L^⊥) holds for every such Q.
  - Apply (S2) with S := M_t, G_q := H_{q,t} and T_q := Ω_{q,t}. Its remainder is M_t ∖ ⋃_q H_{q,t}(Ω_{q,t}) = Z ∩ p⁻¹(t), which is H^m-null. So this property holds for H^m-a.e. x ∈ M_t. This is (i). ∎

## Key steps

1. Coordinates V = ℝ^n ≅ L ×₂ ℝ^m (Θ, π₁, j). Jacobian identity: if p∘D = π₁ and L ⊆ range D, then the shear U (det 1) and the block-diagonal Gram matrix of D₀ give J(D) = J(D∘j) and range(D∘j) = range D ∩ L^⊥.
2. Refine the given pieces to parameters where L ⊆ range DF_i (piece_pullback, tangent_along_lipschitz, uniqueness). Partition with tolerance (2C_A)⁻¹ and reparametrize each part by Φ = Θ⁻¹(pF', κπ_{ker pA'}) as H(Ω), with H Lipschitz, bi-Lipschitz on Ω and p∘H = π₁. The images are disjoint, lie in M and cover it up to a null set.
3. On each piece, the area formula for H and for the slice maps H(Θ⁻¹(t,·)) (whose derivative is DH∘j and Jacobian equals JH), together with Tonelli, gives ∫_{H(Ω)} g dH^n = ∫_L ∫_{H(Ω)∩p⁻¹(t)} g dH^m dH^d with an a.e.-measurable inner function.
4. Eilenberg: an H^n-null Z has H^m-null slices for H^d-a.e. t (fine covers, ψ_j with ∫_L ψ_j ≤ c_B/(j+1), Fatou).
5. Summing over the disjoint pieces gives (ii); (ii) gives local finiteness of slices. The slice maps make M_t countably m-rectifiable, and tangent_along_lipschitz in dimension m with ae_transfer gives Tan(M_t, x) = T_xM ∩ L^⊥ a.e., which is (i).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d = workspace HEAD; mathlib 25730c7c); diff of 480b1bd:GMT/Ch07/Submission.lean vs the workspace Submission.lean (identical, contract only)`
- `rg -n -i 'coarea|eilenberg|starProjection x = t' <snapshot>/project/GMT --glob '*.lean' (only the unproved Ch02 Contract/Submission Props EilenbergInequality and CoareaFormula); rg -n 'spine_coarea|dimred_cs_sos|idtp_fons' <snapshot>/project (no match)`
- `rg -n in <snapshot>/mathlib/Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, ae_ae_of_ae_prod, normDet_sq_eq_det_gram, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one, LipschitzOnWith.extend_finite_dimension, MeasurableSet.image_of_continuousOn_injOn, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, Isometry.map_euclideanHausdorffMeasure, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, lintegral_liminf_le`
- `grep -n in SimonGMT 2b36630 (lake-packages-25730c7c/simongmt): Chapter02/AreaLipschitz.lean (areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn), Chapter02/Area.lean (areaJacobianAt = normDet), Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn), Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `lake env lean /tmp/sc-decomp/Probe.lean after import GMT.Ch07.Submission. Unknown: LinearMap.normDet, areaJacobianAt, weighted_area_formula_lipschitz_injOn. In scope: euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique, Submodule.measurePreserving_measurableEquivProd, AffineSubspace.euclideanHausdorffMeasure_eq_lintegral, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LipschitzOnWith.extend_real, MeasurableSet.image_of_continuousOn_injOn`
- `python3 -I over dag.json: accepted nodes mentioning 'starProjection x = t', coarea, Eilenberg, ApproximatesLinearOn or Matrix.gram give idtp_fons_cs_sos_spine_coarea (byte-identical type) and dtc_bc_lc_sl_cc_critical_null. Also status, candidate commit and type identity of dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_measurable_ae_pullback, dpf_itt_ae_of_ae_pieces, idtp_fons_cs_sos_lipschitz_approx_tangent and dimred_cs_sos_lipschitz_approx_tangent`
- `git show d35a0320:GMT/Ch07/Submission.lean, lines 6460–7367 (accepted lipschitz_tangent and spine_coarea proofs; master block 6555–7356; instantiation 7358–7367)`
- `git show {a2ba78f,bed5b84,bfe4427,2626c7a,a216804,08ae824,2e81485}:GMT/Ch07/Submission.lean | head (imports); git merge-base --is-ancestor checks (a2ba78f, bed5b84 and bfe4427 are ancestors of 2626c7a; a2ba78f and bfe4427 are not ancestors of 08ae824)`
- `sed -n '/^## Proof/,/^## Key steps/p' on the parent-supplied-natural-proof.md of the 4 reused nodes; read the split_off_spine decomposition-v1.json for the reuse precedent and import policy`
- `python3 -I /tmp/sc-decomp/scripts/gen_challenges.py (gmt-compare.py child_modules, contract mode), then lake env lean /tmp/sc-decomp/Challenges.lean (44 s, exit 0)`
- `lake env lean /tmp/sc-decomp/Check1.lean (with the AreaLipschitz import; #print axioms: propext, sorryAx (stubs only), Classical.choice, Quot.sound)`
- `grep 'dimred_cs_sos_sc_' in dag.json, nodes/*/decomposition-v*.json, .humanize/math-wiki and GMT/ (no match)`
- `sed -n 390,425p book/chapter-07.txt (Simon 7.3.5 at lines 407–418, proof left to the reader)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-ac07005b8c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-6d6197c93d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-aad3a33660/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/sc-decomp/Challenges.lean`
- `/tmp/sc-decomp/Check1.lean`

Pins. The snapshot is project b4d606d (= workspace HEAD) with mathlib 25730c7c; SimonGMT is 2b36630. The proof base 480b1bd has a contract-identical Submission.lean.

What the snapshot lacks. It has no slicing or coarea theorem for rectifiable sets: its project tree holds only the unproved Ch02 contract Props EilenbergInequality and CoareaFormula, and no spine/dimred/idtp declaration. Every Mathlib lemma the new child uses is present at the cited files. The SimonGMT area formula and LinearMap.normDet lie outside the contract import closure, so the new child inherits them by merging the accepted candidate 2626c7a.

Reuse. The reusable work is in DAG-accepted commits, not in the snapshot. idtp_fons_cs_sos_spine_coarea (d35a0320) has exactly the selected type. Its proof uses the four accepted declarations reused here, whose types are byte-identical.

Lean check. All 5 child types elaborate in the comparator's contract scope. The parent's frozen type follows by a one-line assembly, and the new child is proved by the accepted master block. The new name dimred_cs_sos_sc_coarea_of_pieces is unused.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
