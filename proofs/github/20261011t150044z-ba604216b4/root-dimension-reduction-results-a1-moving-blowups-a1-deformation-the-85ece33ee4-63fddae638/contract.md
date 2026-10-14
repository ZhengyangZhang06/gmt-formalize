<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.coord_bound-a1 -->

## Theorem `Submission.dimred_mbl_dt_cbm_st_coord_bound`

Let m ∈ ℕ, n = m + 1, 0 ≤ δ ≤ 1/4, and Q_δ = {z ∈ ℝⁿ : δ < z_j < 1 − δ for all j} ⊆ Euclid n (Lebesgue measure). Let i ∈ Fin n and let e_i = EuclideanSpace.single i 1 be the i-th standard unit vector. For all C¹ functions v, g : ℝⁿ → ℝ with |g(y)| ≤ 1 for all y: |∫_{Q_δ} D(vg)(x)e_i dx| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖, where D denotes the Fréchet derivative (fderiv) and ‖Dv(x)‖ its operator norm.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.coord_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6977

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7478, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7518, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7557

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_dt_cbm_st_coord_bound`

```lean
∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.coord_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 of the supplied proof of `dimred_mbl_dt_cbm_smooth_trace`, for a single coordinate i and a C¹ field component g in place of G_i:
- the fundamental theorem of calculus along each coordinate line (the divergence theorem in direction e_i, via Fubini (F2));
- the boundary bound |vg| ≤ |v|;
- the face (trace) estimate, with side length s = 1 − 2δ ≥ 1/2.
The only change from the supplied text is the order of operations. The supplied proof first integrates the boundary terms over the face variable x' ∈ Q' and then bounds each face integral. Here the same two inequalities (steps 3 and 4 of the supplied proof) are applied on each line, for fixed x', before integrating over x'. This avoids separate face integrals and gives the same constant: 2·(2∫|v| + ∫‖Dv‖) = 4∫|v| + 2∫‖Dv‖.

Notation and hypotheses.
- m ∈ ℕ and n := m + 1. ℝⁿ := `Euclid n` (Lebesgue measure), with coordinates z_j := z.ofLp j. ℝ^m := Fin m → ℝ (product Lebesgue measure).
- 0 ≤ δ ≤ 1/4, a := δ, b := 1 − δ.
- Q := {z ∈ ℝⁿ : δ < z_j < 1 − δ for all j} and Q' := {y ∈ ℝ^m : δ < y_k < 1 − δ for all k}.
- i ∈ Fin n and e_i := EuclideanSpace.single i 1, the i-th standard unit vector (‖e_i‖ = 1, `PiLp.norm_single`).
- ι(t, y) := toLp 2 (Fin.insertNth i t y) for t ∈ ℝ, y ∈ ℝ^m.
- v, g : ℝⁿ → ℝ are C¹ (`ContDiff ℝ 1`), and |g(y)| ≤ 1 for all y.

Claim: |∫_Q D(vg)(x)e_i dx| ≤ 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖, where D(vg)(x)e_i = fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1).

Sibling lemmas used (dependencies of this node):
- `dimred_mbl_dt_cbm_st_box_integrableOn`: continuous functions are integrable on boxes {a < z_j < b}.
- `dimred_mbl_dt_cbm_st_slice_integral`: for a ≤ b and h integrable on the box, y ↦ ∫_a^b h(ι(t, y)) dt is integrable on Q', and ∫_Q h = ∫_{Q'} ∫_a^b h(ι(t, y)) dt dy.
- `dimred_mbl_dt_cbm_st_interval_bound`: for a < b, C¹ φ, γ with |γ| ≤ 1, |∫_a^b (φγ)'| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|.

0. Since δ ≤ 1/4, b − a = 1 − 2δ ≥ 1/2 > 0. So a < b (in particular a ≤ b) and 2/(b − a) ≤ 4. The hypothesis 0 ≤ δ is carried only to match the parent's hypotheses; this lemma does not use it.
1. Lines. For all t and y, ι(t, y) = ι(0, y) + t·e_i. Check coordinatewise, splitting j ∈ Fin n into j = i and j = i.succAbove k (`Fin.succAboveCases`):
   - at i: t = 0 + t·1;
   - at i.succAbove k ≠ i: y_k = y_k + t·0.
   Hence, for fixed y, t ↦ ι(t, y) is affine, C¹, with derivative e_i at every t (`HasDerivAt` of t ↦ c + t·e_i).
2. Integrands.
   - vg is C¹ (product), so x ↦ D(vg)(x) is continuous, and F(x) := D(vg)(x)e_i is continuous.
   - |v| and ‖Dv‖ are continuous because v is C¹, so H(x) := 4|v(x)| + 2‖Dv(x)‖ is continuous.
   - By `dimred_mbl_dt_cbm_st_box_integrableOn` with box parameters δ and 1 − δ, the functions F, H, |v| and ‖Dv‖ are integrable on Q.
3. Slicing (`dimred_mbl_dt_cbm_st_slice_integral`, valid since a ≤ b).
   - Applied to F: ∫_Q F = ∫_{Q'} (∫_a^b F(ι(t, y)) dt) dy.
   - Applied to H: K(y) := ∫_a^b H(ι(t, y)) dt is integrable on Q', and ∫_Q H = ∫_{Q'} K.
4. Linearity on Q. By the integrability of step 2, ∫_Q H = 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖.
5. Line estimate: for every y ∈ ℝ^m, |∫_a^b F(ι(t, y)) dt| ≤ K(y).
   5a. φ(t) := v(ι(t, y)) and γ(t) := g(ι(t, y)) are C¹ (C¹ functions composed with the affine map of step 1), and |γ| ≤ 1.
   5b. By the chain rule (`HasFDerivAt.comp_hasDerivAt`) with step 1, for every t: (φγ)'(t) = D(vg)(ι(t, y))e_i = F(ι(t, y)) and φ'(t) = Dv(ι(t, y))e_i.
   5c. By `dimred_mbl_dt_cbm_st_interval_bound` (a < b) and 5b: |∫_a^b F(ι(t, y)) dt| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |Dv(ι(t, y))e_i| dt.
   5d. Two comparisons:
       - ∫_a^b |φ| ≥ 0 (a ≤ b, nonnegative integrand) and 2/(b − a) ≤ 4, so (2/(b − a)) ∫_a^b |φ| ≤ 4 ∫_a^b |φ|.
       - For every x, |Dv(x)e_i| ≤ ‖Dv(x)‖·‖e_i‖ = ‖Dv(x)‖ by the operator-norm bound (`ContinuousLinearMap.le_opNorm`). Both integrands are continuous in t, so monotonicity of the interval integral (a ≤ b) gives ∫_a^b |Dv(ι(t, y))e_i| dt ≤ ∫_a^b ‖Dv(ι(t, y))‖ dt.
   5e. Continuous integrands are interval integrable, so by linearity K(y) = 4 ∫_a^b |φ| + 2 ∫_a^b ‖Dv(ι(t, y))‖ dt. Combining 5c–5e gives the line estimate.
6. Conclusion.
   - |∫_Q F| = |∫_{Q'} ∫_a^b F(ι(t, y)) dt dy| by step 3.
   - This is ≤ ∫_{Q'} |∫_a^b F(ι(t, y)) dt| dy, since |∫f| ≤ ∫|f|.
   - This is ≤ ∫_{Q'} K by monotonicity (`integral_mono_of_nonneg`): the left integrand is ≥ 0, K is integrable on Q' (step 3), and the pointwise bound is step 5.
   - ∫_{Q'} K = ∫_Q H by step 3, and ∫_Q H = 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖ by step 4. ∎

Formalization notes. The Lean proof below was re-compiled in this decomposition session against exactly the frozen type above (Lean v4.35.0-rc3, Mathlib 25730c7c, project commit b4d606db with GMT/Ch07/Submission.lean byte-identical to the frozen Contract). It compiled (a) in a scratch file `import GMT.Ch07.Submission` followed by the contract scope (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `namespace GMT.Ch07`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), and (b) inserted into a copy of GMT/Ch07/Submission.lean immediately before `main_theorem`, after the contract's `noncomputable section ... end`. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound. The comparator form `theorem _root_.HumanizeNodeComparator.target : (<frozen type>) := by exact Submission.dimred_mbl_dt_cbm_st_coord_bound` elaborates in the replayed contract scope. The proof calls the three sibling declarations by their final names `Submission.dimred_mbl_dt_cbm_st_box_integrableOn`, `Submission.dimred_mbl_dt_cbm_st_slice_integral` and `Submission.dimred_mbl_dt_cbm_st_interval_bound` (in the scratch build they were declared earlier in the same file with exactly their frozen types). `Fin.succAboveCases` is used with `induction j using Fin.succAboveCases i with | x => … | p j => …`. `PiLp.norm_single` replaces the deprecated `EuclideanSpace.norm_single`.

```lean
theorem Submission.dimred_mbl_dt_cbm_st_coord_bound : ∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v g i δ hv hg hgb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ} with hQ
  set Q' : Set (Fin m → ℝ) := {y : Fin m → ℝ | ∀ j, δ < y j ∧ y j < 1 - δ} with hQ'
  have hab : δ < 1 - δ := by linarith
  -- the line `t ↦ ι t y` through the slice point `y` in direction `e_i`
  set ι : ℝ → (Fin m → ℝ) → Euclid (m + 1) := fun t y => WithLp.toLp 2 (Fin.insertNth i t y)
    with hι
  have hι_affine : ∀ t y, ι t y = ι 0 y + t • EuclideanSpace.single i 1 := by
    intro t y
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [ι]
    | p j => simp [ι, Fin.succAbove_ne]
  have hι_deriv : ∀ t y, HasDerivAt (fun s => ι s y) (EuclideanSpace.single i 1) t := by
    intro t y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (ι 0 y)
  have hι_cd : ∀ y, ContDiff ℝ 1 (fun s => ι s y) := by
    intro y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hvg : ContDiff ℝ 1 (fun y => v y * g y) := hv.mul hg
  set F : Euclid (m + 1) → ℝ := fun x => fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)
    with hF
  set H : Euclid (m + 1) → ℝ := fun x => 4 * |v x| + 2 * ‖fderiv ℝ v x‖ with hH
  have hFc : Continuous F := (hvg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : Continuous fun x => |v x| := hv.continuous.abs
  have hDvc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hHc : Continuous H := (continuous_const.mul hvc).add (continuous_const.mul hDvc)
  obtain ⟨-, hFslice⟩ := Submission.dimred_mbl_dt_cbm_st_slice_integral m i δ (1 - δ) F hab.le
    (Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hFc)
  obtain ⟨hHint, hHslice⟩ := Submission.dimred_mbl_dt_cbm_st_slice_integral m i δ (1 - δ) H hab.le
    (Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hHc)
  have hHsplit : ∫ x in Q, H x = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [integral_add ((Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hvc).const_mul 4)
      ((Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hDvc).const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the one-dimensional estimate on each line
  have hline : ∀ y, |∫ t in δ..(1 - δ), F (ι t y)| ≤ ∫ t in δ..(1 - δ), H (ι t y) := by
    intro y
    have hφ : ContDiff ℝ 1 (fun s => v (ι s y)) := hv.comp (hι_cd y)
    have hγ : ContDiff ℝ 1 (fun s => g (ι s y)) := hg.comp (hι_cd y)
    have hderiv_prod : ∀ t, deriv (fun s => v (ι s y) * g (ι s y)) t = F (ι t y) := by
      intro t
      have := ((hvg.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have hderiv_v : ∀ t, deriv (fun s => v (ι s y)) t =
        fderiv ℝ v (ι t y) (EuclideanSpace.single i 1) := by
      intro t
      have := ((hv.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have h1 := Submission.dimred_mbl_dt_cbm_st_interval_bound (fun s => v (ι s y)) (fun s => g (ι s y))
      δ (1 - δ) hφ hγ (fun t => hgb _) hab
    simp only [hderiv_prod, hderiv_v] at h1
    have hcoef : 2 / (1 - δ - δ) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hint_nonneg : 0 ≤ ∫ t in δ..(1 - δ), |v (ι t y)| :=
      intervalIntegral.integral_nonneg hab.le fun t _ => abs_nonneg _
    have hcont_v : Continuous fun t => |v (ι t y)| := hφ.continuous.abs
    have hcont_Dv : Continuous fun t => ‖fderiv ℝ v (ι t y)‖ := hDvc.comp (hι_cd y).continuous
    have hcont_dv : Continuous fun t => |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| :=
      (((hv.continuous_fderiv one_ne_zero).comp (hι_cd y).continuous).clm_apply
        continuous_const).abs
    have hmono : ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| ≤
        ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      refine intervalIntegral.integral_mono_on hab.le (hcont_dv.intervalIntegrable _ _)
        (hcont_Dv.intervalIntegrable _ _) fun t _ => ?_
      have := (fderiv ℝ v (ι t y)).le_opNorm (EuclideanSpace.single i 1)
      rw [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] at this
      exact this
    have hHline : ∫ t in δ..(1 - δ), H (ι t y) =
        4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      simp only [H]
      rw [intervalIntegral.integral_add ((hcont_v.intervalIntegrable _ _).const_mul 4)
        ((hcont_Dv.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hHline]
    calc |∫ t in δ..(1 - δ), F (ι t y)|
        ≤ 2 / (1 - δ - δ) * (∫ t in δ..(1 - δ), |v (ι t y)|) +
            2 * ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| := h1
      _ ≤ 4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
        gcongr
  calc |∫ x in Q, F x|
      = |∫ y in Q', ∫ t in δ..(1 - δ), F (ι t y)| := by rw [hFslice]
    _ ≤ ∫ y in Q', |∫ t in δ..(1 - δ), F (ι t y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q', ∫ t in δ..(1 - δ), H (ι t y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hHint
          (Eventually.of_forall hline)
    _ = ∫ x in Q, H x := hHslice.symm
    _ = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := hHsplit
```

## Key steps

1. a := δ, b := 1 − δ: b − a = 1 − 2δ ≥ 1/2, so a < b and 2/(b − a) ≤ 4.
2. ι(t, y) = ι(0, y) + t e_i, so each coordinate line is affine with derivative e_i.
3. F := D(vg)(·)e_i and H := 4|v| + 2‖Dv‖ are continuous, hence integrable on Q_δ (box_integrable); ∫_Q H = 4∫|v| + 2∫‖Dv‖.
4. Slice F and H in coordinate i (slice_integral); the slice integral of H is integrable on Q'.
5. On each line, the chain rule gives (φγ)' = F∘ι and φ' = Dv(ι)e_i. Then interval_bound, 2/(b − a) ≤ 4 and |Dv(x)e_i| ≤ ‖Dv(x)‖ give |∫_a^b F∘ι| ≤ ∫_a^b H∘ι.
6. |∫_Q F| ≤ ∫_{Q'} |∫_a^b F∘ι| ≤ ∫_{Q'} ∫_a^b H∘ι = ∫_Q H = 4∫_Q|v| + 2∫_Q‖Dv‖.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…); git rev-parse HEAD (b4d606db1da5…); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n 'theorem volume_preserving_piFinSuccAbove|theorem PiLp.volume_preserving_toLp|theorem integral_prod_symm|theorem Integrable.integral_prod_right|theorem ContinuousOn.integrableOn_compact|theorem prod_restrict|theorem integral_deriv_eq_sub|theorem integral_mono_interval|theorem norm_integral_le_abs_integral_norm|lemma trace_eq_sum_inner|theorem contDiff_piLp_apply|theorem norm_apply_le' SNAPSHOT/mathlib/Mathlib -g '*.lean' (all found: Constructions/Pi.lean:818, Measure/Haar/InnerProductSpace.lean:139, Integral/Prod.lean:338,463, Function/LocallyIntegrable.lean:592, Measure/Prod.lean:778, IntervalIntegral/FundThmCalculus.lean:1176, IntervalIntegral/Basic.lean:743,1405, InnerProductSpace/Trace.lean:25, Calculus/ContDiff/WithLp.lean:83, Normed/Lp/PiLp.lean:713)`
- `rg -n 'abs_integral_le_integral_abs' SNAPSHOT/mathlib/Mathlib (Integral/Bochner/Basic.lean:982); rg -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' (Integral/DivergenceTheorem.lean:266, outside the Submission import closure, not needed by the coordinatewise route)`
- `rg -n -i 'piFinSuccAbove|insertNth|trace_eq_sum_inner|integral_divergence|divergence|trace inequality|BVExtension' SNAPSHOT/project -g '*.lean' (only tangentialDivergence definitions and the unproved Ch02 Props BVExtensionEstimate/BVPoincare; no box divergence theorem or trace inequality)`
- `rg -n 'def euclideanDivergence|theorem .*divergence|piFinSuccAbove|insertNth' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/{BV,SubmanifoldCalculus}.lean (euclideanDivergence, euclideanDivergence_eq_sum_inner only; no trace or Fubini-slicing lemma)`
- `python3 -I scan of RUN/dag.json: twin node cmcdt_cbm_smooth_trace (identical lean_statement, waiting-children) with unaccepted children cmcdt_cbm_st_{box_integrableOn,slice_integral,interval_bound,coord_bound,div_product}; grep -c dimred_mbl_dt_cbm_st dag.json = 0; /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py _existing_lean_name_problem and max_depth logic (depth 5 < 6)`
- `lake env lean /tmp/dimred-st-split/All.lean, /tmp/dimred-st-split/SubmissionCopy.lean, /tmp/dimred-st-split/SolutionCombined.lean and /tmp/dimred-st-split/chal/*_NodeChallenge.lean (generated by verifier/gmt-compare.py child_modules); verifier/lean_contract.py validate_lean_statement on all six types`
- `sed -n 655,680p book/chapter-02.txt (Simon Ch. 2, 2.8–2.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-cdd48df72e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/dimred-st-split/All.lean`
- `/tmp/dimred-st-split/SubmissionCopy.lean`
- `/tmp/dimred-st-split/SolutionCombined.lean`

The pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor SimonGMT contains a box divergence theorem, coordinate-slicing lemma or trace inequality. SimonGMT has only euclideanDivergence and its basis-sum formula, and the Ch02 BVExtensionEstimate is an unproved Prop. All Mathlib ingredients exist at the pinned revision inside the bare Submission import closure: volume_preserving_piFinSuccAbove, PiLp.volume_preserving_toLp, integral_prod_symm, Integrable.integral_prod_right, Measure.prod_restrict, ContinuousOn.integrableOn_compact, intervalIntegral FTC and monotonicity, LinearMap.trace_eq_sum_inner, PiLp.norm_apply_le and abs_integral_le_integral_abs. The five child types are byte-identical to the audited, accepted split of the twin cmcdt_cbm_smooth_trace. Those twin children are unaccepted and owned by another parent, so the fresh names dimred_mbl_dt_cbm_st_* are used; they collide with nothing. In this session all five child proofs and the parent assembly compiled with the exact frozen types and only standard axioms. The comparator challenges elaborate, and both statement validators accept the types.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
