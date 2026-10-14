<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.gradient_field-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_co_gradient_field`

Let P, d ∈ ℕ, M ⊆ ℝ^P, L ≥ 0 and f : ℝ^P → ℝ L-Lipschitz. For j ∈ ℕ let ψ_j : ℝ^d → ℝ^P and F_j : ℝ^d → ℝ be C¹ and V_j, Y_j ⊆ ℝ^d, such that ψ_j is injective on V_j, Dψ_j(y) is injective for y ∈ V_j, Y_j is Borel, closure(Y_j) is compact and contained in V_j, and f(ψ_j(y)) = F_j(y) for y ∈ Y_j. Assume the images ψ_j(Y_j) are pairwise disjoint and H^d(M ∖ ⋃_j ψ_j(Y_j)) = 0 (H^d = μHE[d]). Then there are sets Y′_j ⊆ Y_j (j ∈ ℕ) and a map G : ℝ^P → ℝ^P such that: each Y′_j and each ψ_j(Y′_j) is Borel; H^d(M ∖ ⋃_j ψ_j(Y′_j)) = 0; G is Borel; |G(x)| ≤ L for every x ∈ ℝ^P; and for every j and y ∈ Y′_j, G(ψ_j(y)) ∈ Dψ_j(y)(ℝ^d) and ⟨G(ψ_j(y)), Dψ_j(y)e⟩ = DF_j(y)e for every e ∈ ℝ^d.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.gradient_field-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6085

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7060, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7069, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7071

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_co_gradient_field`

```lean
∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), LipschitzWith L f → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, MeasurableSet (Y j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∃ (Y' : ℕ → Set (Euclid d)) (G : Euclid P → Euclid P), (∀ j, Y' j ⊆ Y j) ∧ (∀ j, MeasurableSet (Y' j)) ∧ (∀ j, MeasurableSet (ψ j '' Y' j)) ∧ μHE[d] (M \ ⋃ j, ψ j '' Y' j) = 0 ∧ Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧ ∀ j, ∀ y ∈ Y' j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.gradient_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Simon Ch. 3, Definition 2.1: ∇^M f := ∇^{N_j} f on the j-th piece), with step 2(a)'s removal of the null set where the bound |∇^M f| ≤ L fails, and the null-image remark of Simon's proof of Ch. 3, 2.4 ("if φ is locally Lipschitz and B has Hⁿ-measure zero then Hⁿ(φ(B)) = 0").
Notation: K_j := closure(Y_j) (compact, K_j ⊆ V_j); L^d := volume on ℝ^d; H^d := μHE[d]; B̄_r(y) := closedBall(y, r).

1. (Chart constants.) For each j, ψ_j is C¹, injective on K_j ⊆ V_j, and Dψ_j(y) is injective for y ∈ K_j ⊆ V_j. By chart_bilipschitz there are m_j > 0 and Λ_j with m_j|a − b| ≤ |ψ_j(a) − ψ_j(b)| ≤ Λ_j|a − b| for all a, b ∈ K_j. With Λ_j⁺ := max(Λ_j, 0) ∈ [0, ∞), ψ_j is Λ_j⁺-Lipschitz on K_j (LipschitzOnWith).
2. (Pointwise gradients.) By chart_gradient applied to (ψ_j, F_j, V_j) there is h_j : ℝ^d → ℝ^P, continuous on V_j, with h_j(y) ∈ range Dψ_j(y) and ⟨h_j(y), Dψ_j(y)e⟩ = DF_j(y)e for every y ∈ V_j and e ∈ ℝ^d.
3. (Bound at density points.) Let y ∈ Y_j be a Lebesgue density point of Y_j, i.e. L^d(Y_j ∩ B̄_r(y))/L^d(B̄_r(y)) → 1 as r ↓ 0. ψ_j and F_j are differentiable at y (C¹) and f∘ψ_j = F_j on Y_j, so density_gradient_bound gives |DF_j(y)e| ≤ L|Dψ_j(y)e| for every e. By step 2 (y ∈ Y_j ⊆ V_j) write h_j(y) = Dψ_j(y)w. Then
 |h_j(y)|² = ⟨h_j(y), Dψ_j(y)w⟩ = DF_j(y)w ≤ L|Dψ_j(y)w| = L|h_j(y)|,
 hence |h_j(y)| ≤ L (trivial if h_j(y) = 0; otherwise divide by |h_j(y)|).
4. (Trimmed pieces.) Define Y′_j := {y ∈ Y_j : |h_j(y)| ≤ L}.
 (a) Y′_j ⊆ Y_j.
 (b) Y′_j is Borel: h_j is continuous on the closed set K_j ⊆ V_j, so C_j := K_j ∩ h_j⁻¹(B̄_L(0)) is closed (ContinuousOn.preimage_isClosed_of_isClosed), and Y′_j = Y_j ∩ C_j because Y_j ⊆ K_j.
 (c) L^d(Y_j ∖ Y′_j) = 0. By Lebesgue's density theorem (Besicovitch.ae_tendsto_measure_inter_div for the locally finite measure L^d on ℝ^d and the set Y_j), L^d-a.e. point of Y_j is a density point of Y_j; this is an a.e. statement for L^d restricted to Y_j, and since Y_j is measurable, ae_restrict_iff' turns it into: the set of points of Y_j which are not density points of Y_j is L^d-null. By step 3 every point of Y_j ∖ Y′_j is such a point, so L^d(Y_j ∖ Y′_j) = 0.
 (d) H^d(ψ_j(Y_j ∖ Y′_j)) = 0. Y_j ∖ Y′_j ⊆ K_j and ψ_j is Λ_j⁺-Lipschitz there, so H^d(ψ_j(Y_j ∖ Y′_j)) ≤ (Λ_j⁺)^d·H^d(Y_j ∖ Y′_j) (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn); and H^d = L^d on ℝ^d (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so the right side is (Λ_j⁺)^d·0 = 0.
5. (Images.) A′_j := ψ_j(Y′_j) is Borel by the Lusin–Souslin theorem (MeasurableSet.image_of_continuousOn_injOn: Y′_j is Borel in the Polish space ℝ^d, ψ_j is continuous and injective on Y′_j ⊆ V_j). The A′_j are pairwise disjoint because A′_j ⊆ ψ_j(Y_j).
6. (Null remainder.) If x ∈ M lies in no A′_j, then either x lies in no ψ_j(Y_j), or x = ψ_j(y) for some j and y ∈ Y_j ∖ Y′_j. Hence
 M ∖ ⋃_j A′_j ⊆ (M ∖ ⋃_j ψ_j(Y_j)) ∪ ⋃_j ψ_j(Y_j ∖ Y′_j).
 Both sets on the right are H^d-null (hypothesis; step 4(d) and countable subadditivity), so H^d(M ∖ ⋃_j A′_j) = 0.
7. (Inverse charts.) Let φ_j := invFunOn ψ_j Y′_j : ℝ^P → ℝ^d (ℝ^d is nonempty). Since ψ_j is injective on Y′_j, φ_j(ψ_j(y)) = y for y ∈ Y′_j (InjOn.leftInvOn_invFunOn), so φ_j maps A′_j into Y′_j. For x = ψ_j(y) and x′ = ψ_j(y′) in A′_j (y, y′ ∈ Y′_j ⊆ K_j), step 1 gives |φ_j(x) − φ_j(x′)| = |y − y′| ≤ m_j⁻¹|x − x′|. So φ_j is Lipschitz, hence continuous, on A′_j, and g_j := h_j ∘ φ_j is continuous on A′_j (ContinuousOn.comp: h_j is continuous on Y′_j ⊆ V_j and φ_j(A′_j) ⊆ Y′_j).
8. (Definition of G.) For x ∈ ℝ^P: if x ∈ A′_j for some j (this j is unique by step 5), put G(x) := g_j(x); otherwise put G(x) := 0. [For instance G(x) := if h : ∃ j, x ∈ A′_j then g_{Nat.find h}(x) else 0.]
 (a) For every j and y ∈ Y′_j: ψ_j(y) ∈ A′_j, so G(ψ_j(y)) = h_j(φ_j(ψ_j(y))) = h_j(y). By step 2 (y ∈ V_j): G(ψ_j(y)) ∈ range Dψ_j(y) and ⟨G(ψ_j(y)), Dψ_j(y)e⟩ = DF_j(y)e for every e.
 (b) |G(x)| ≤ L for every x: if x ∈ A′_j then x = ψ_j(y) with y ∈ Y′_j and G(x) = h_j(y), and |h_j(y)| ≤ L by definition of Y′_j; otherwise G(x) = 0 and 0 ≤ L.
9. (G is Borel.) For each j, G_j := A′_j.piecewise g_j 0 is Borel by ContinuousOn.measurable_piecewise (g_j is continuous on the Borel set A′_j, and the zero map is continuous). G agrees with G_j on A′_j and vanishes on ℝ^P ∖ ⋃_k A′_k. Hence for every Borel O ⊆ ℝ^P,
 G⁻¹(O) = ⋃_j (A′_j ∩ G_j⁻¹(O)) ∪ {x ∈ ℝ^P ∖ ⋃_k A′_k : 0 ∈ O},
 a countable union of Borel sets, so G is Borel. (Equivalently: apply Measurable.find to the Borel maps G_j and the Borel predicates p_j(x) :⟺ x ∈ A′_j ∨ x ∉ ⋃_k A′_k; the resulting map is G.)
10. Steps 4(a)(b), 5, 6, 8 and 9 give all assertions. ∎

Lean realization note. The verified code below follows steps 1–10, defining Y′_j := Y_j ∩ (closure(Y_j) ∩ h_j⁻¹(closedBall(0, L))) and building G by the Measurable.find variant of step 9 (helper aux_measurable_find, stated without Nat.find to avoid clashing decidability instances); disjointness of the ψ_j(Y_j) is used exactly to identify the selected index at ψ_j(y). The algebra of step 3 is the helper aux_norm_le_of_inner.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.dtc_bc_lc_sl_co_chart_bilipschitz, Submission.dtc_bc_lc_sl_co_chart_gradient and Submission.dtc_bc_lc_sl_co_density_gradient_bound (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). Auxiliary lemmas are named `Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner`, `Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find` to stay globally unique; they may be renamed or inlined. It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_gradient_field` has exactly the frozen type of this child.

```lean
/-- Step 3 algebra: a gradient vector `v = Dψ w` with `⟨v, Dψ e⟩ = DF e` and
`|DF e| ≤ L |Dψ e|` has `|v| ≤ L`. -/
theorem Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner {P d : ℕ} (A : Euclid d →L[ℝ] Euclid P) (B : Euclid d →L[ℝ] ℝ)
    (L : NNReal) (v : Euclid P) (hv : v ∈ LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P))
    (hinner : ∀ e, inner ℝ v (A e) = B e) (hb : ∀ e, |B e| ≤ L * ‖A e‖) : ‖v‖ ≤ L := by
  obtain ⟨w, hw⟩ := hv
  have hw' : A w = v := hw
  have h1 := hinner w
  rw [hw', real_inner_self_eq_norm_sq] at h1
  have h2 := hb w
  rw [hw'] at h2
  have h3 : ‖v‖ ^ 2 ≤ L * ‖v‖ := by rw [h1]; exact (le_abs_self _).trans h2
  have h4 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  nlinarith [norm_nonneg v]

/-- Measurable countable selection (via `Measurable.find`), stated without `Nat.find`. -/
theorem Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : ℕ → α → β} {p : ℕ → α → Prop} (hf : ∀ n, Measurable (f n))
    (hp : ∀ n, MeasurableSet {x | p n x}) (h : ∀ x, ∃ n, p n x) :
    ∃ G : α → β, Measurable G ∧ ∀ x, ∃ n, p n x ∧ G x = f n x := by
  classical
  exact ⟨fun x => f (Nat.find (h x)) x, Measurable.find hf hp h,
    fun x => ⟨Nat.find (h x), Nat.find_spec (h x), rfl⟩⟩

theorem Submission.dtc_bc_lc_sl_co_gradient_field : ∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), LipschitzWith L f → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, MeasurableSet (Y j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∃ (Y' : ℕ → Set (Euclid d)) (G : Euclid P → Euclid P), (∀ j, Y' j ⊆ Y j) ∧ (∀ j, MeasurableSet (Y' j)) ∧ (∀ j, MeasurableSet (ψ j '' Y' j)) ∧ μHE[d] (M \ ⋃ j, ψ j '' Y' j) = 0 ∧ Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧ ∀ j, ∀ y ∈ Y' j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := by
  have h_chart_bilipschitz : (∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (K : Set (Euclid d)), ContDiff ℝ 1 ψ → IsCompact K → InjOn ψ K → (∀ y ∈ K, Injective (fderiv ℝ ψ y)) → ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ ∧ ‖ψ a - ψ b‖ ≤ Λ * ‖a - b‖) := Submission.dtc_bc_lc_sl_co_chart_bilipschitz
  have h_chart_gradient : (∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (V : Set (Euclid d)), ContDiff ℝ 1 ψ → ContDiff ℝ 1 F → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ h : Euclid d → Euclid P, ContinuousOn h V ∧ ∀ y ∈ V, h y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (h y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) := Submission.dtc_bc_lc_sl_co_chart_gradient
  have h_density_gradient_bound : (∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖) := Submission.dtc_bc_lc_sl_co_density_gradient_bound
  intro P d M f L ψ V Y F hf hψ hinj hdψ hF hYm hYc hYV hfY hdisj hM
  classical
  -- Step 1: chart constants
  have hK : ∀ j, ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ closure (Y j), ∀ b ∈ closure (Y j),
      m * ‖a - b‖ ≤ ‖ψ j a - ψ j b‖ ∧ ‖ψ j a - ψ j b‖ ≤ Λ * ‖a - b‖ := fun j =>
    h_chart_bilipschitz P d (ψ j) (closure (Y j)) (hψ j) (hYc j) ((hinj j).mono (hYV j))
      (fun y hy => hdψ j y (hYV j hy))
  choose m Λ hm hmΛ using hK
  -- Step 2: pointwise gradients
  have hH : ∀ j, ∃ h : Euclid d → Euclid P, ContinuousOn h (V j) ∧ ∀ y ∈ V j,
      h y ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧
        ∀ e : Euclid d, inner ℝ (h y) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := fun j =>
    h_chart_gradient P d (ψ j) (F j) (V j) (hψ j) (hF j) (hdψ j)
  choose h hhc hh using hH
  -- Step 3: the bound at density points
  have hbound : ∀ j, ∀ y ∈ Y j, Tendsto (fun r => volume (Y j ∩ closedBall y r) /
      volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ‖h j y‖ ≤ L := by
    intro j y hy hdens
    have hyV : y ∈ V j := hYV j (subset_closure hy)
    exact Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner (fderiv ℝ (ψ j) y) (fderiv ℝ (F j) y) L (h j y) (hh j y hyV).1
      (hh j y hyV).2
      (h_density_gradient_bound d P f L (ψ j) (F j) (Y j) y hf hy
        ((hψ j).differentiable one_ne_zero y) ((hF j).differentiable one_ne_zero y) (hfY j) hdens)
  -- Step 4: trimmed pieces `Y' j = {y ∈ Y j : ‖h j y‖ ≤ L}`
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → Set (Euclid d),
      ∀ j, Y' j = Y j ∩ (closure (Y j) ∩ h j ⁻¹' closedBall 0 L) := ⟨_, fun j => rfl⟩
  have hY'mem : ∀ j y, y ∈ Y' j ↔ y ∈ Y j ∧ ‖h j y‖ ≤ L := by
    intro j y
    rw [hY' j]
    simp only [mem_inter_iff, mem_preimage, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, subset_closure h1, h3⟩
  have hY'Y : ∀ j, Y' j ⊆ Y j := fun j y hy => ((hY'mem j y).1 hy).1
  have hY'V : ∀ j, Y' j ⊆ V j := fun j => (hY'Y j).trans (subset_closure.trans (hYV j))
  have hY'L : ∀ j, ∀ y ∈ Y' j, ‖h j y‖ ≤ L := fun j y hy => ((hY'mem j y).1 hy).2
  have hY'm : ∀ j, MeasurableSet (Y' j) := by
    intro j
    rw [hY' j]
    exact (hYm j).inter (((hhc j).mono (hYV j)).preimage_isClosed_of_isClosed isClosed_closure
      isClosed_closedBall).measurableSet
  -- 4(c): Lebesgue density theorem
  have hnull : ∀ j, volume (Y j \ Y' j) = 0 := by
    intro j
    have hae := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid d)) (Y j)
    rw [ae_restrict_iff' (hYm j), ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro y hy
    simp only [Set.mem_ofPred_eq]
    intro hcon
    exact hy.2 ((hY'mem j y).2 ⟨hy.1, hbound j y hy.1 (hcon hy.1)⟩)
  -- 4(d): null images
  have hLip : ∀ j, LipschitzOnWith (Real.toNNReal (Λ j)) (ψ j) (closure (Y j)) := by
    intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖ψ j a - ψ j b‖ ≤ Λ j * ‖a - b‖ := (hmΛ j a ha b hb).2
      _ ≤ (Real.toNNReal (Λ j) : ℝ) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)
  have hnullimg : ∀ j, μHE[d] (ψ j '' (Y j \ Y' j)) = 0 := by
    intro j
    have hL' : LipschitzOnWith (Real.toNNReal (Λ j)) (ψ j) (Y j \ Y' j) :=
      (hLip j).mono (Set.sdiff_subset.trans subset_closure)
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d hL'
    have h2 : μHE[d] (Y j \ Y' j) = 0 := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]; exact hnull j
    rw [h2, mul_zero] at h1
    exact le_antisymm h1 zero_le
  -- Step 5: images are Borel (Lusin--Souslin)
  have hA'm : ∀ j, MeasurableSet (ψ j '' Y' j) := fun j =>
    (hY'm j).image_of_continuousOn_injOn (hψ j).continuous.continuousOn
      ((hinj j).mono (hY'V j))
  -- Step 6: null remainder
  have hrem : μHE[d] (M \ ⋃ j, ψ j '' Y' j) = 0 := by
    have hsub : M \ ⋃ j, ψ j '' Y' j ⊆ (M \ ⋃ j, ψ j '' Y j) ∪ ⋃ j, ψ j '' (Y j \ Y' j) := by
      rintro x ⟨hxM, hx⟩
      by_cases hx' : x ∈ ⋃ j, ψ j '' Y j
      · right
        obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.1 hx'
        exact mem_iUnion.2 ⟨j, y, ⟨hy, fun hy' => hx (mem_iUnion.2 ⟨j, y, hy', rfl⟩)⟩, rfl⟩
      · left; exact ⟨hxM, hx'⟩
    exact measure_mono_null hsub (measure_union_null hM (measure_iUnion_null hnullimg))
  -- Step 7: inverse charts
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → Euclid P → Euclid d, ∀ j, ∀ y ∈ Y' j, φ j (ψ j y) = y :=
    ⟨fun j => Function.invFunOn (ψ j) (Y' j), fun j y hy =>
      ((hinj j).mono (hY'V j)).leftInvOn_invFunOn hy⟩
  have hφcont : ∀ j, ContinuousOn (φ j) (ψ j '' Y' j) := by
    intro j
    have hL : LipschitzOnWith (Real.toNNReal (m j)⁻¹) (φ j) (ψ j '' Y' j) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hφ j a ha, hφ j b hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 (hm j).le)]
      have hab := (hmΛ j a (subset_closure (hY'Y j ha)) b (subset_closure (hY'Y j hb))).1
      rw [inv_mul_eq_div, le_div_iff₀ (hm j)]
      linarith [mul_comm (m j) ‖a - b‖]
    exact hL.continuousOn
  have hgcont : ∀ j, ContinuousOn (fun x => h j (φ j x)) (ψ j '' Y' j) := by
    intro j
    refine ((hhc j).mono (hY'V j)).comp (hφcont j) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hφ j y hy]
    exact hy
  -- Step 8/9: the pieces `G_j` and the glued field `G`
  obtain ⟨Gj, hGjm, hGjin, hGjout⟩ : ∃ Gj : ℕ → Euclid P → Euclid P, (∀ j, Measurable (Gj j)) ∧
      (∀ j, ∀ y ∈ Y' j, Gj j (ψ j y) = h j y) ∧ (∀ j x, x ∉ ψ j '' Y' j → Gj j x = 0) := by
    refine ⟨fun j => (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0,
      fun j => (hgcont j).measurable_piecewise continuousOn_const (hA'm j), ?_, ?_⟩
    · intro j y hy
      show (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0 (ψ j y) = h j y
      rw [piecewise_eq_of_mem _ _ _ (mem_image_of_mem _ hy)]
      exact congrArg (h j) (hφ j y hy)
    · intro j x hx
      show (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0 x = 0
      rw [piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]
  have hGjL : ∀ j x, ‖Gj j x‖ ≤ L := by
    intro j x
    by_cases hx : x ∈ ψ j '' Y' j
    · obtain ⟨y, hy, rfl⟩ := hx
      rw [hGjin j y hy]
      exact hY'L j y hy
    · rw [hGjout j x hx, norm_zero]
      exact NNReal.coe_nonneg L
  have hex : ∀ x, ∃ n, x ∈ ψ n '' Y' n ∨ x ∉ ⋃ k, ψ k '' Y' k := by
    intro x
    by_cases hx : x ∈ ⋃ k, ψ k '' Y' k
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hx⟩
  obtain ⟨G, hGm, hG⟩ := Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find (p := fun n x => x ∈ ψ n '' Y' n ∨ x ∉ ⋃ k, ψ k '' Y' k)
    hGjm (fun n => (hA'm n).union (MeasurableSet.iUnion hA'm).compl) hex
  refine ⟨Y', G, hY'Y, hY'm, hA'm, hrem, hGm, ?_, ?_⟩
  · intro x
    obtain ⟨n, -, hn⟩ := hG x
    rw [hn]
    exact hGjL n x
  · intro j y hy
    obtain ⟨n, hpn, hn⟩ := hG (ψ j y)
    have hmem : ψ j y ∈ ψ j '' Y' j := mem_image_of_mem _ hy
    have hnj : n = j := by
      rcases hpn with hpn | hpn
      · by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) (Set.image_mono (hY'Y n) hpn)
          (Set.image_mono (hY'Y j) hmem)
      · exact absurd (mem_iUnion.2 ⟨j, hmem⟩) hpn
    rw [hn, hnj, hGjin j y hy]
    exact hh j y (hY'V j hy)
```

## Key steps

1. chart_bilipschitz on K_j = closure(Y_j): m_j > 0 and Λ_j bounding ψ_j from below and above.
2. chart_gradient: h_j continuous on V_j with h_j(y) ∈ range Dψ_j(y) and ⟨h_j(y), Dψ_j(y)e⟩ = DF_j(y)e.
3. density_gradient_bound at Lebesgue density points y ∈ Y_j gives |h_j(y)| ≤ L.
4. Y′_j := {y ∈ Y_j : |h_j(y)| ≤ L} is Borel and L^d(Y_j ∖ Y′_j) = 0 (density theorem), so H^d(ψ_j(Y_j ∖ Y′_j)) = 0 (Lipschitz image) and M ∖ ⋃_j ψ_j(Y′_j) is null.
5. ψ_j(Y′_j) Borel (Lusin–Souslin) and disjoint; the inverse chart is continuous on it (lower bound).
6. G := h_j ∘ ψ_j⁻¹ on ψ_j(Y′_j), 0 elsewhere: Borel (countable piecewise of ContinuousOn pieces), |G| ≤ L, gradient identities on Y′_j.
7. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
