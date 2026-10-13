<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_cutoff_lift-a1 -->

## Theorem `Submission.dgcr_bwd_graph_cutoff_lift`

Let m, k ∈ ℕ, U ⊆ ℝ^{m+1+k}; ι : ℝ^{m+1} → ℝ^{m+1+k}, ι' : ℝ^k → ℝ^{m+1+k} linear isometries with ⟨ιv, ι'w⟩ = 0 for all v, w and such that every x ∈ ℝ^{m+1+k} equals ιv + ι'w for some v, w; s, h ∈ ℝ with h > 0; u : ℝ^{m+1} → ℝ^k continuous on B_s(0) with u(B_s(0)) ⊆ B_h(0); z ∈ ℝ^{m+1+k} with C := {z + ιv + ι'w : v ∈ B_s(0), w ∈ B_h(0)} ⊆ U; ψ a smooth m-form on ℝ^{m+1} with compact support and tsupport ψ ⊆ B_s(0). Let L := ι* (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) and P^#ψ := affinePullbackForm L (−Lz) ψ. Then there is a test form φ ∈ 𝒟^m(U) (φ : TestFormOn U m) with tsupport φ ⊆ C such that, for every v ∈ B_s(0), φ coincides with P^#ψ on a neighbourhood of z + ιv + ι'u(v).

Node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_cutoff_lift-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2716

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3508

Decomposition children: None

## Lean problem

Declaration: `Submission.dgcr_bwd_graph_cutoff_lift`

```lean
∀ (m k : ℕ) (U : Set (Euclid (m + 1 + k))) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (s h : ℝ) (ψ : DifferentialForm (Euclid (m + 1)) m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (m + 1 + k), ∃ v : Euclid (m + 1), ∃ w : Euclid k, x = ι v + ι' w) → 0 < h → ContinuousOn u (ball 0 s) → (∀ v ∈ ball (0 : Euclid (m + 1)) s, u v ∈ ball (0 : Euclid k) h) → {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → IsSmoothForm ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid (m + 1)) s → ∃ φ : TestFormOn U m, tsupport (φ : DifferentialForm (Euclid (m + 1 + k)) m) ⊆ {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ∧ ∀ v ∈ ball (0 : Euclid (m + 1)) s, (φ : DifferentialForm (Euclid (m + 1 + k)) m) =ᶠ[𝓝 (z + ι v + ι' (u v))] affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ
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

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_cutoff_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 1, 5 and 6 of the parent proof (φ := (η∘Q)·P^#ψ is a test form supported in C, and it agrees with P^#ψ near the graph: η∘Q ≡ 1 near Φ(v) for v ∈ spt ψ, and both forms vanish near Φ(v) for v ∉ spt ψ), stated for an arbitrary smooth compactly supported ψ with spt ψ ⊆ B_s(0). The spanning property of (ι, ι') is a hypothesis here; the parent supplies it from Submission.dgcr_orthogonal_coordinates. Sibling lemma used (as the frozen declaration): Submission.dgcr_bwd_normal_cutoff.
Notation: ℝ^p means Euclid p = EuclideanSpace ℝ (Fin p); e_l := EuclideanSpace.single l (1 : ℝ) is the l-th standard basis vector; for an (m+1)-tuple w, removeNth i w := Fin.removeNth i w is the m-tuple with entry i deleted, so (removeNth i w)(l) = w(i.succAbove l) (Fin.removeNth_apply); Covector E m = E [⋀^Fin m]→L[ℝ] ℝ (continuous alternating m-linear forms); DifferentialForm E m = E → Covector E m; exteriorDerivative = Mathlib's extDeriv (Poincare.SimonGMT.Chapter06.exteriorDerivative is an abbrev), with the alternating-sum formula dω(x)(w₀,…,w_m) = Σᵢ (−1)^i • D[y ↦ ω(y)(removeNth i w)](x)(wᵢ) for ω differentiable at x (exteriorDerivative_apply); IsSmoothForm ψ := ContDiff ℝ ∞ ψ where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) (in the frozen contract scope `∞` denotes ENNReal's ∞ because of `open scoped ENNReal`, so write the order as (⊤ : ℕ∞)). Also L' := ι'* = ContinuousLinearMap.adjoint ι'.toContinuousLinearMap, Pr(x) := L(x − z), Q(x) := L'(x − z), Φ(v) := z + ιv + ι'u(v), and TestFormOn U m consists of the smooth compactly supported m-forms φ with tsupport φ ⊆ U.
1. Adjoint identities: L(ιv) = v, L(ι'w) = 0, L'(ιv) = 0 and L'(ι'w) = w for all v ∈ ℝ^{m+1}, w ∈ ℝ^k. Each is proved by pairing with an arbitrary y and using ext_inner_right: ⟨L(ιv), y⟩ = ⟨ιv, ιy⟩ = ⟨v, y⟩ and ⟨L'(ι'w), y⟩ = ⟨ι'w, ι'y⟩ = ⟨w, y⟩ (ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map); ⟨L(ι'w), y⟩ = ⟨ι'w, ιy⟩ = ⟨ιy, ι'w⟩ = 0 (real_inner_comm and orthogonality) and ⟨L'(ιv), y⟩ = ⟨ιv, ι'y⟩ = 0 (orthogonality), with ⟨0, y⟩ = 0 (inner_zero_left).
2. Decomposition: z + ι(Pr x) + ι'(Q x) = x for every x. Indeed, by the spanning hypothesis x − z = ιv₀ + ι'w₀ for some v₀, w₀; by step 1, Pr x = L(ιv₀ + ι'w₀) = v₀ and Q x = w₀; hence z + ιv₀ + ι'w₀ = z + (x − z) = x (add_assoc applied with explicit first argument z, then add_sub_cancel; note that an unqualified `rw [add_assoc]` would try to rewrite the type index m + 1 + k).
3. Cutoff. K := tsupport ψ is compact (HasCompactSupport ψ) and K ⊆ B_s(0). As u is continuous on B_s(0) ⊇ K, u(K) is compact (IsCompact.image_of_continuousOn with ContinuousOn.mono), and u(K) ⊆ B_h(0) by the hypothesis u(B_s(0)) ⊆ B_h(0). The sibling Submission.dgcr_bwd_normal_cutoff (applied to k, u(K), h and 0 < h) gives η : ℝ^k → ℝ, C^∞, with compact support, tsupport η ⊆ B_h(0), and such that every point of u(K) has a neighbourhood on which η ≡ 1.
4. The test form. Since −Lz + Lx = L(x − z) (map_sub, neg_add_eq_sub), (P^#ψ)(x) = ψ(Pr x).compContinuousLinearMap L. Define φ(x) := η(Q x) • (P^#ψ)(x). The map x ↦ Q x = L'(x − z) is affine, hence C^∞, so x ↦ η(Q x) is C^∞ (ContDiff.comp); P^#ψ is smooth (Poincare.SimonGMT.Chapter06.affinePullbackForm_isSmoothForm); hence φ is smooth (ContDiff.smul). (Write the smoothness order as (⊤ : ℕ∞), not ∞, in the contract scope.)
5. Support. S := {x : Pr x ∈ K ∧ Q x ∈ tsupport η} is closed (preimages of the closed sets K and tsupport η under the continuous maps Pr and Q, intersected). If x ∉ S then φ(x) = 0: if Pr x ∉ K then ψ(Pr x) = 0 (image_eq_zero_of_notMem_tsupport), so (P^#ψ)(x) = 0 (ext; simp) and φ(x) = η(Q x) • 0 = 0; if Q x ∉ tsupport η then η(Q x) = 0 and φ(x) = 0 • (P^#ψ)(x) = 0. Thus support φ ⊆ S, and since S is closed, tsupport φ ⊆ S (closure_minimal). Let F(v, w) := z + ιv + ι'w, a continuous map ℝ^{m+1} × ℝ^k → ℝ^{m+1+k}. By step 2, each x ∈ S equals F(Pr x, Q x) with (Pr x, Q x) ∈ K × tsupport η, so S ⊆ F(K × tsupport η). The set K × tsupport η is compact (IsCompact.prod), so F(K × tsupport η) is compact (IsCompact.image), and F(K × tsupport η) ⊆ C because K ⊆ B_s(0) and tsupport η ⊆ B_h(0). Therefore tsupport φ ⊆ F(K × tsupport η) ⊆ C ⊆ U, and φ has compact support (IsCompact.of_isClosed_subset with isClosed_tsupport). Hence φ, packaged with these facts, is an element of TestFormOn U m (smooth, compactly supported, tsupport ⊆ U), and tsupport φ ⊆ C is the first conclusion.
6. Germ property. Fix v ∈ B_s(0) and x₀ := Φ(v) = z + ιv + ι'u(v). By step 1, Q x₀ = L'(ιv + ι'u(v)) = u(v) and Pr x₀ = v (rewrite x₀ − z = ιv + ι'u(v) by add_assoc z and add_sub_cancel_left, then map_add and step 1).
 (i) If v ∈ K: u(v) ∈ u(K), so by step 3 η ≡ 1 on a neighbourhood of u(v). The map Q is continuous with Q x₀ = u(v), so Q tends to u(v) along 𝓝 x₀ and η(Q x) = 1 for all x near x₀ (Filter.Tendsto.eventually). For such x, φ(x) = 1 • (P^#ψ)(x) = (P^#ψ)(x) (one_smul).
 (ii) If v ∉ K: O := {x : Pr x ∉ K} is open (the complement of the closed set K pulled back by the continuous map Pr) and x₀ ∈ O since Pr x₀ = v ∉ K. For x ∈ O, ψ(Pr x) = 0, so (P^#ψ)(x) = 0 and φ(x) = η(Q x) • 0 = 0 = (P^#ψ)(x) (smul_zero).
 In both cases φ =ᶠ[𝓝 x₀] P^#ψ (filter_upwards), which is the second conclusion. ∎
Formalization note: this child is a machine leaf (one theorem `Submission.dgcr_bwd_graph_cutoff_lift` appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declarations, no set_option). The following tactic proof was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context under default maxHeartbeats, passes the workflow's leaf source-delta check, and depends only on propext, Classical.choice, Quot.sound (and the sibling declaration named above); it may be used verbatim:
theorem Submission.dgcr_bwd_graph_cutoff_lift : ∀ (m k : ℕ) (U : Set (Euclid (m + 1 + k))) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (s h : ℝ) (ψ : DifferentialForm (Euclid (m + 1)) m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (m + 1 + k), ∃ v : Euclid (m + 1), ∃ w : Euclid k, x = ι v + ι' w) → 0 < h → ContinuousOn u (ball 0 s) → (∀ v ∈ ball (0 : Euclid (m + 1)) s, u v ∈ ball (0 : Euclid k) h) → {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → IsSmoothForm ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid (m + 1)) s → ∃ φ : TestFormOn U m, tsupport (φ : DifferentialForm (Euclid (m + 1 + k)) m) ⊆ {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ∧ ∀ v ∈ ball (0 : Euclid (m + 1)) s, (φ : DifferentialForm (Euclid (m + 1 + k)) m) =ᶠ[𝓝 (z + ι v + ι' (u v))] affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ := by
  intro m k U ι ι' u z s h ψ hperp hspan hh hu hmaps hCU hψs hψc hψsupp
  set L := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hL
  set L' := ContinuousLinearMap.adjoint ι'.toContinuousLinearMap with hL'
  have hLι : ∀ v', L (ι v') = v' := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [hL, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v' y
  have hLι' : ∀ w, L (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hL, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  have hL'ι : ∀ v', L' (ι v') = 0 := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [hL', ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    exact hperp v' y
  have hL'ι' : ∀ w, L' (ι' w) = w := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hL', ContinuousLinearMap.adjoint_inner_left]
    exact ι'.inner_map_map w y
  have hdec : ∀ x, z + ι (L (x - z)) + ι' (L' (x - z)) = x := by
    intro x
    obtain ⟨v₀, w₀, hx⟩ := hspan (x - z)
    have h1 : L (x - z) = v₀ := by rw [hx, map_add, hLι, hLι', add_zero]
    have h2 : L' (x - z) = w₀ := by rw [hx, map_add, hL'ι, hL'ι', zero_add]
    rw [h1, h2]
    calc z + ι v₀ + ι' w₀ = z + (ι v₀ + ι' w₀) := add_assoc _ _ _
      _ = z + (x - z) := by rw [hx]
      _ = x := add_sub_cancel z x
  have hK : IsCompact (tsupport ψ) := hψc
  obtain ⟨η, hηs, hηc, hηsupp, hη1⟩ := Submission.dgcr_bwd_normal_cutoff k (u '' tsupport ψ) h hh
    (hK.image_of_continuousOn (hu.mono hψsupp))
    (by rintro _ ⟨v, hv, rfl⟩; exact hmaps v (hψsupp hv))
  have hPr : Continuous (fun x : Euclid (m + 1 + k) => L (x - z)) :=
    L.continuous.comp (continuous_id.sub continuous_const)
  have hQ : Continuous (fun x : Euclid (m + 1 + k) => L' (x - z)) :=
    L'.continuous.comp (continuous_id.sub continuous_const)
  have hPapply : ∀ x, affinePullbackForm L (-(L z)) ψ x = (ψ (L (x - z))).compContinuousLinearMap L := by
    intro x
    simp only [affinePullbackForm, map_sub, neg_add_eq_sub]
  let φ : DifferentialForm (Euclid (m + 1 + k)) m :=
    fun x => η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x
  have hφs : IsSmoothForm φ := by
    have hηQ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid (m + 1 + k) => η (L' (x - z))) :=
      hηs.comp (L'.contDiff.comp (contDiff_id.sub contDiff_const))
    exact hηQ.smul (affinePullbackForm_isSmoothForm L (-(L z)) hψs)
  let F : Euclid (m + 1) × Euclid k → Euclid (m + 1 + k) := fun p => z + ι p.1 + ι' p.2
  have hF : Continuous F := by
    have h1 : Continuous (fun p : Euclid (m + 1) × Euclid k => ι p.1) := ι.continuous.comp continuous_fst
    have h2 : Continuous (fun p : Euclid (m + 1) × Euclid k => ι' p.2) := ι'.continuous.comp continuous_snd
    exact (continuous_const.add h1).add h2
  have hS : IsClosed {x : Euclid (m + 1 + k) | L (x - z) ∈ tsupport ψ ∧ L' (x - z) ∈ tsupport η} :=
    ((isClosed_tsupport ψ).preimage hPr).inter ((isClosed_tsupport η).preimage hQ)
  have hsuppS : support φ ⊆ {x | L (x - z) ∈ tsupport ψ ∧ L' (x - z) ∈ tsupport η} := by
    intro x hx
    by_contra hcon
    apply hx
    rcases not_and_or.mp hcon with h1 | h1
    · have h0 : ψ (L (x - z)) = 0 := image_eq_zero_of_notMem_tsupport h1
      have hP0 : affinePullbackForm L (-(L z)) ψ x = 0 := by
        rw [hPapply, h0]
        ext w
        simp
      show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = 0
      rw [hP0, smul_zero]
    · have h0 : η (L' (x - z)) = 0 := image_eq_zero_of_notMem_tsupport h1
      show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = 0
      rw [h0, zero_smul]
  have hsupp : tsupport φ ⊆ F '' (tsupport ψ ×ˢ tsupport η) := by
    refine (closure_minimal hsuppS hS).trans ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨(L (x - z), L' (x - z)), ⟨hx1, hx2⟩, hdec x⟩
  have hFC : F '' (tsupport ψ ×ˢ tsupport η) ⊆
      {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} := by
    rintro _ ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hψsupp hv, w, hηsupp hw, rfl⟩
  have hcomp : IsCompact (F '' (tsupport ψ ×ˢ tsupport η)) := (hK.prod hηc).image hF
  refine ⟨⟨φ, ⟨hφs, hcomp.of_isClosed_subset (isClosed_tsupport _) hsupp⟩,
    (hsupp.trans hFC).trans hCU⟩, hsupp.trans hFC, ?_⟩
  intro v hv
  have hQv : L' (z + ι v + ι' (u v) - z) = u v := by
    rw [add_assoc z, add_sub_cancel_left, map_add, hL'ι, hL'ι', zero_add]
  have hPv : L (z + ι v + ι' (u v) - z) = v := by
    rw [add_assoc z, add_sub_cancel_left, map_add, hLι, hLι', add_zero]
  by_cases hvK : v ∈ tsupport ψ
  · have hev : ∀ᶠ y in 𝓝 (u v), η y = 1 := hη1 (u v) ⟨v, hvK, rfl⟩
    have hT := hQ.tendsto (z + ι v + ι' (u v))
    rw [hQv] at hT
    filter_upwards [hT.eventually hev] with x hx
    show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = affinePullbackForm L (-(L z)) ψ x
    rw [hx, one_smul]
  · have hopen : IsOpen {x : Euclid (m + 1 + k) | L (x - z) ∉ tsupport ψ} :=
      (isClosed_tsupport ψ).isOpen_compl.preimage hPr
    filter_upwards [hopen.mem_nhds (show L (z + ι v + ι' (u v) - z) ∉ tsupport ψ by rw [hPv]; exact hvK)] with x hx
    have h0 : ψ (L (x - z)) = 0 := image_eq_zero_of_notMem_tsupport hx
    have hP0 : affinePullbackForm L (-(L z)) ψ x = 0 := by
      rw [hPapply, h0]
      ext w
      simp
    show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = affinePullbackForm L (-(L z)) ψ x
    rw [hP0, smul_zero]

## Key steps

1. Adjoint identities for L = ι*, L' = ι'*; spanning gives x = z + ι(L(x−z)) + ι'(L'(x−z)).
2. Apply Submission.dgcr_bwd_normal_cutoff to the compact set u(spt ψ) ⊆ B_h(0) to get η.
3. φ(x) := η(L'(x−z)) • (P^#ψ)(x) is smooth.
4. support φ ⊆ {Pr ∈ spt ψ, Q ∈ spt η} (closed) ⊆ F(spt ψ × spt η), compact and ⊆ C ⊆ U; so φ ∈ TestFormOn U m with tsupport φ ⊆ C.
5. Near Φ(v): if v ∈ spt ψ then η∘Q ≡ 1 (continuity of Q, Q Φ(v) = u(v)); otherwise P^#ψ ≡ 0 near Φ(v); hence φ =ᶠ P^#ψ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (byte-identical); manifest.json project_commit b4d606d, mathlib_commit 25730c7c; simongmt package at 2b36630`
- `rg -n 'extDeriv_eq|theorem extDeriv_apply|theorem extDeriv_pullback' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'theorem curryLeft_apply_apply|def curryLeft' mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean`
- `rg -n 'cons_removeNth_eq_comp_cycleRange_symm|sign_cycleRange' mathlib/Mathlib`
- `rg -n 'theorem det_self|theorem det_apply' mathlib/Mathlib/LinearAlgebra/Determinant.lean; rg -n 'Continuous.matrix_det|continuous_matrix' mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `rg -n 'map_perm|map_eq_zero_of_eq' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean; rg -n 'adjoint_inner_left' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem exists_lt_subset_ball' mathlib/Mathlib; rg -n 'one_of_mem_closedBall|tsupport_eq|hasCompactSupport|contDiff' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'continuous_of_finiteDimensional' mathlib/Mathlib (only LinearMap.continuous_of_finiteDimensional; no MultilinearMap variant)`
- `rg -n 'fderiv_mul_const|DifferentiableAt.smul_const|tsupport_smul_subset_left|image_eq_zero_of_notMem_tsupport|setIntegral_congr_fun' mathlib/Mathlib`
- `rg -n 'exteriorDerivative_apply|exteriorDerivative_affinePullbackForm|affinePullbackForm_isSmoothForm|def affinePullbackForm|tsupport_exteriorDerivative_subset|GeometricCurrentOn.boundary_apply|def exteriorDerivativeTestOn|def IsSmoothForm|abbrev TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,AffineCurrentPushforward}.lean`
- `lake env lean /tmp/bwd-split-work/Names.lean and Names2.lean: #check of all cited names after import GMT.Ch07.Submission`
- `python3 lean_contract.validate_lean_statement on the 6 child types; gmt-compare.contract_scope replay; lake env lean /tmp/bwd-split-work/Elab.lean (types elaborate in the comparator scope)`
- `lake env lean /tmp/bwd-split-work/Full.lean: six child proofs as GMT.Ch07.Submission.* theorems, the exact parent type proved from them plus dgcr_orthogonal_coordinates as a hypothesis, comparator-style `exact Submission.X` checks, #print axioms`
- `lake env lean /tmp/bwd-split-work/SimSubmission.lean: frozen Submission.lean with all six children inserted before `end GMT.Ch07`; leaf_verification.check_source_delta simulated for each insertion`
- `grep 'dgcr_bwd_' over dag.json, nodes/*, and all 1159 git refs (git grep): no match`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-5d86c28dbf/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bwd-split-work/Elab.lean`
- `/tmp/bwd-split-work/Full.lean`
- `/tmp/bwd-split-work/SimSubmission.lean`

The snapshot is project b4d606d with Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Submission.lean. Every cited lemma is in the import closure of GMT.Ch07.Submission.
Mathlib lemmas used: Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, ContinuousAlternatingMap.curryLeft_apply_apply, Fin.cons_removeNth_eq_comp_cycleRange_symm, Fin.sign_cycleRange, Module.Basis.det_apply/det_self, Continuous.matrix_det, continuous_matrix, AlternatingMap.map_perm/map_eq_zero_of_eq, ContinuousLinearMap.adjoint_inner_left, exists_lt_subset_ball, the ContDiffBump API, fderiv_mul_const and setIntegral_congr_fun.
simongmt lemmas used: exteriorDerivative_apply, affinePullbackForm with affinePullbackForm_isSmoothForm and exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply.
MultilinearMap.continuous_of_finiteDimensional has no match, so the determinant covector proves its continuity explicitly.
Lean checks:
- All 6 child types pass validate_lean_statement and elaborate in the comparator contract scope.
- Each child compiles as a single theorem under default heartbeats and passes the leaf source-delta check.
- The exact parent type follows from children coordinate_form, graph_pullback_extderiv and graph_cutoff_lift plus dgcr_orthogonal_coordinates, with axioms only propext, Classical.choice and Quot.sound.
- No dgcr_bwd_ name collision exists in the DAG, node records or git refs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
