<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1 -->

## Theorem `Submission.idtp_tdc_density_locally_constant`

Let P ∈ ℕ and let C ∈ 𝒟_2(ℝ^P) be minimizing in ℝ^P (IsMinimizingIn C univ), with ∂C = 0 (BoundaryVanishes C) and a cone (IsConeCurrent C). Then for every p ∈ spt C with p ≠ 0 there are δ > 0 and k ∈ ℕ such that HasMassDensity C y k (i.e. Θ²(μ_C, y) = k) for every y ∈ spt C ∩ B_δ(p).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4833

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5335, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5360, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5352

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5823, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5837, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5848, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5868, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5878

## Lean problem

Declaration: `Submission.idtp_tdc_density_locally_constant`

```lean
∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → ∀ p ∈ C.support, p ≠ 0 → ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ ∀ y ∈ C.support, y ∈ ball p δ → HasMassDensity C y k
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: paragraph (M) and steps 1–6 of the parent proof (its jump set J is shown to be empty; Departure [D3]: the book, chapter-07.txt lines 497–510, only cites [Whi82] for the classification of 2-dimensional area minimizing cones; cf. F. Morgan, Math. Ann. 261 (1982) 101–110). Steps 4 and 6 of the parent proof are packaged in the sibling idtp_tdc_arc_continuation and the finite-mass count of its step 5 in the sibling idtp_tdc_no_infinite_planar_pieces. Notation: 𝕊 := {x ∈ ℝ^P : |x| = 1}; B_r(x) = ball x r; H² = μHE[2]; M_W = massOn.
0. Facts. (a) Uniqueness of densities: HasMassDensity C y θ and HasMassDensity C y θ' imply θ = θ' (both are ≥ 0, limits in the Hausdorff space [0, ∞] are unique, and ENNReal.ofReal is injective on [0, ∞)). (b) Uniqueness of planes: if Q₁, Q₂ are linear subspaces, x ∈ Q₁, t > 0 and Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x), then Q₁ = Q₂. [x ∈ Q₁ ∩ B_t(x) ⊆ Q₂; for v ∈ Q₁ and 0 < s < t/(|v| + 1), x + s·v ∈ Q₁ ∩ B_t(x) ⊆ Q₂, so s·v ∈ Q₂ and v ∈ Q₂; symmetrically Q₂ ⊆ Q₁.] (c) C is integer multiplicity (first component of IsMinimizingIn C univ), so the sibling idtp_tdc_cone_dilation gives, for s > 0 and all x, θ: s·x ∈ spt C ⟺ x ∈ spt C, and HasMassDensity C (s·x) θ ⟺ HasMassDensity C x θ. (d) spt C is closed (the complement of the open zero region). (e) For w ∈ 𝕊 and y ≠ 0: |y/|y| − w| ≤ |y/|y| − y| + |y − w| = ||y| − |w|| + |y − w| ≤ 2|y − w|.
1. Suppose, for a contradiction, that some p₀ ∈ spt C with p₀ ≠ 0 admits no δ > 0 and k ∈ ℕ as in the claim.
2. (Integer densities; P ≥ 2.) For q ∈ spt C ∖ {0}, the parent's sibling prerequisite Submission.idtp_cone_tangent_cone_planar (with λ_j := 1/(j + 1) > 0, λ_j → 0) gives an orthonormal family τ : Fin 2 → ℝ^P and c ∈ ℤ with |c| ≥ 1 and HasMassDensity C q |c|. Applied at q = p₀, the orthonormal (hence linearly independent) family τ shows P = finrank ℝ^P ≥ 2.
3. (Monotonicity.) Since 1 ≤ 2 ≤ P, the cross-branch theorem Submission.dimred_minimizing_monotonicity applies with n := 2, d := P, U := N := ℝ^P and T := C: ℝ^P is open; IsEmbeddedSubmanifold 2 P ℝ^P holds (for every y take V := W := ℝ^P and ψ := id, which is C², injective, with ψ(V) = W ∩ ℝ^P, V ∩ ψ⁻¹(K) = K compact for every compact K, and injective derivative id); (closure ℝ^P ∖ ℝ^P) ∩ ℝ^P = ∅; C is minimizing in ℝ^P ∩ ℝ^P = ℝ^P; spt C ⊆ ℝ^P ∩ ℝ^P; BoundaryVanishes C. Its part (iii) gives Θ : ℝ^P → ℝ with HasMassDensity C y Θ(y) for every y and Θ upper semicontinuous on ℝ^P. By step 2 and (a), for q ∈ spt C ∖ {0}, Θ(q) = κ(q) for a natural number κ(q) ≥ 1. By (c) and (a), Θ(s·x) = Θ(x) for all s > 0 and x.
4. (The jump set.) Let J := {q ∈ spt C ∖ {0} : for every δ > 0 some y ∈ spt C ∩ B_δ(q) has Θ(y) ≠ Θ(q)}. If q ∈ spt C ∖ {0} and q ∉ J, there is δ > 0 with Θ(y) = Θ(q) = κ(q) for every y ∈ spt C ∩ B_δ(q), i.e. HasMassDensity C y κ(q) there, so the claim holds at q with k := κ(q). Hence p₀ ∈ J. J is dilation invariant: if q ∈ J and s > 0, then s·q ∈ spt C ∖ {0} by (c), and for δ > 0 a point y ∈ spt C ∩ B_{δ/s}(q) with Θ(y) ≠ Θ(q) gives s·y ∈ spt C ∩ B_δ(s·q) with Θ(s·y) = Θ(y) ≠ Θ(q) = Θ(s·q). Thus b' := p₀/|p₀| ∈ J ∩ 𝕊.
5. (A jump point of locally minimal density.) The set {κ(q) : q ∈ J ∩ 𝕊 ∩ B_{1/8}(b')} of natural numbers is nonempty (it contains κ(b')); let m₀ be its least element, attained at b ∈ J ∩ 𝕊 ∩ B_{1/8}(b'). Since Θ(b) = m₀ < m₀ + 1 and Θ is upper semicontinuous at b, there is r₀ > 0 with Θ(y) < m₀ + 1 for every y ∈ B_{r₀}(b). Let r := min(r₀, 1/8 − |b − b'|, 1/2) > 0, so B_r(b) ⊆ B_{1/8}(b'). (5a) If y ∈ spt C ∩ B_r(b), then |y| ≥ 1 − |y − b| > 1/2, so y ≠ 0, Θ(y) = κ(y) ∈ ℕ and κ(y) < m₀ + 1, i.e. κ(y) ≤ m₀. (5b) If q ∈ J ∩ 𝕊 ∩ B_r(b), then κ(q) ≥ m₀ by minimality (q ∈ B_{1/8}(b')) and κ(q) ≤ m₀ by (5a), so κ(q) = m₀.
6. (Light points accumulate at b.) Let r' := r/2. For every η ∈ (0, r'/2) there is z ∈ (spt C ∩ 𝕊) ∖ J with |z − b| < η and κ(z) < m₀. Indeed, b ∈ J gives y ∈ spt C ∩ B_{η/2}(b) with Θ(y) ≠ Θ(b) = m₀, and κ(y) < m₀ by (5a) (η/2 < r). Let z := y/|y|. Then z ∈ spt C by (c), |z| = 1, |z − b| ≤ 2|y − b| < η < r by (e), and Θ(z) = Θ(y) < m₀; if z ∈ J, (5b) would give κ(z) = m₀, so z ∉ J. For each i ∈ ℕ fix such a point z_i for η_i := r'/(4(i + 1)) and let k_i := κ(z_i); then 1 ≤ k_i < m₀ and |z_i − b| < η_i → 0.
7. (Planes at the light points.) Fix i. Since z_i ∈ spt C ∖ {0} and z_i ∉ J, step 4 gives δ_i > 0 with HasMassDensity C y k_i for every y ∈ spt C ∩ B_{δ_i}(z_i). The parent's sibling prerequisite Submission.idtp_cone_constant_density_planar (p := z_i, k := k_i, δ := δ_i) gives δ'_i > 0 and a linear subspace Q_i with finrank Q_i = 2, z_i ∈ Q_i and spt C ∩ B_{δ'_i}(z_i) = Q_i ∩ B_{δ'_i}(z_i). Choose e_i ∈ Q_i with |e_i| = 1 and ⟨z_i, e_i⟩ = 0 (Gram–Schmidt: if (u, v) is a basis of Q_i, then u − ⟨u, z_i⟩z_i and v − ⟨v, z_i⟩z_i lie in Q_i, are orthogonal to z_i, and are not both 0 because u, v are not both multiples of z_i; normalize a nonzero one). For w ∈ ℝ^P let Good_i(w) mean: there is ε > 0 with spt C ∩ B_ε(w) = Q_i ∩ B_ε(w) and HasMassDensity C y k_i for every y ∈ spt C ∩ B_ε(w).
8. (Long light arcs.) Let L := r'/2. Apply the sibling idtp_tdc_arc_continuation to (Q_i, z_i, e_i, k_i, L) and to (Q_i, z_i, −e_i, k_i, L) (−e_i ∈ Q_i is also a unit vector orthogonal to z_i). Its hypotheses hold: C is minimizing in ℝ^P with ∂C = 0 and is a cone; finrank Q_i = 2; z_i, ±e_i ∈ Q_i are orthonormal; k_i ≥ 1; (i) holds with ε := min(δ_i, δ'_i); for (ii), let 0 < φ < L and a := cos φ·z_i + sin φ·(±e_i) with a ∈ spt C and HasMassDensity C a k_i. Then |a| = 1 and |a − z_i| ≤ φ (|a − z_i|² = 2 − 2cos φ = 4sin²(φ/2) ≤ φ²), so |a − b| < φ + η_i < r'/2 + r'/2 = r' < r. If a ∈ J, then (5b) gives Θ(a) = κ(a) = m₀, while (a) gives Θ(a) = k_i < m₀; so a ∉ J, and step 4 gives δ > 0 with HasMassDensity C y κ(a) for every y ∈ spt C ∩ B_δ(a), which is (ii) with k' := κ(a). The sibling yields Good_i(cos φ·z_i + sin φ·e_i) for every φ ∈ (−L, L) (for φ < 0 use −e_i and −φ).
9. (Discs of good points.) Let ρ₀ := min(1/2, r'/8) > 0 and D_i := Q_i ∩ B_{ρ₀}(z_i). Claim: Good_i(x) for every x ∈ D_i. Let x ∈ D_i; then 1/2 < |x| < 3/2, x̂ := x/|x| ∈ Q_i ∩ 𝕊, and |x̂ − z_i| ≤ 2|x − z_i| < 2ρ₀ ≤ r'/4 by (e). Since (z_i, e_i) is an orthonormal basis of Q_i, x̂ = α·z_i + β·e_i with α² + β² = 1; choose φ ∈ (−π, π] with cos φ = α and sin φ = β (φ := arg(α + iβ)). Then |x̂ − z_i|² = 2 − 2cos φ = 4sin²(|φ|/2), and Jordan's inequality sin u ≥ (2/π)u for 0 ≤ u ≤ π/2 (Mathlib Real.mul_le_sin) with u = |φ|/2 gives |x̂ − z_i| ≥ (2/π)|φ|, so |φ| ≤ (π/2)|x̂ − z_i| < πr'/8 < r'/2 = L. By step 8, Good_i(x̂) holds with some ε. Let s := |x|. By (c), y ∈ spt C ∩ B_{sε}(x) iff y/s ∈ spt C ∩ B_ε(x̂) = Q_i ∩ B_ε(x̂) iff y ∈ Q_i ∩ B_{sε}(x); so spt C ∩ B_{sε}(x) = Q_i ∩ B_{sε}(x). For such y, HasMassDensity C (y/s) k_i, hence HasMassDensity C y k_i by (c). So Good_i(x) holds with sε.
10. (Local mass bound.) Let x ∈ D_i and let ε_x witness Good_i(x). Then x ∈ spt C (x ∈ Q_i ∩ B_{ε_x}(x)) and x ≠ 0, so Submission.idtp_cone_constant_density_planar (p := x, k := k_i, δ := ε_x) gives δ''_x > 0 and a subspace Q''_x with spt C ∩ B_{δ''_x}(x) = Q''_x ∩ B_{δ''_x}(x) and M_W(C) = k_i·H²(W ∩ Q''_x) for every open W ⊆ B_{δ''_x}(x). With t := min(ε_x, δ''_x): Q_i ∩ B_t(x) = spt C ∩ B_t(x) = Q''_x ∩ B_t(x) and x ∈ Q_i, so Q''_x = Q_i by (b). Hence for every open W ⊆ B_t(x): H²(W ∩ Q_i) ≤ k_i·H²(W ∩ Q_i) = M_W(C), as k_i ≥ 1.
11. (Disjoint discs.) If Q_i ≠ Q_j, then D_i ∩ D_j = ∅: for x ∈ D_i ∩ D_j, step 9 gives Good_i(x) and Good_j(x); with t the smaller of the two radii, Q_i ∩ B_t(x) = spt C ∩ B_t(x) = Q_j ∩ B_t(x) and x ∈ Q_i, so Q_i = Q_j by (b).
12. (Each plane occurs finitely often.) Suppose Q' is a subspace such that I := {i : Q_i = Q'} is infinite. The points z_i, i ∈ I, lie in the closed set Q' (Submodule.closed_of_finiteDimensional) and converge to b, so b ∈ Q'. Choose i ∈ I with η_i < ρ₀; then |b − z_i| < ρ₀, so b ∈ D_i, and Good_i(b) holds by step 9 with some ε: HasMassDensity C y k_i for all y ∈ spt C ∩ B_ε(b). As b ∈ spt C, (a) gives Θ(b) = k_i and Θ(y) = k_i = Θ(b) for all y ∈ spt C ∩ B_ε(b), so b ∉ J — contradicting b ∈ J. Hence every fibre {i : Q_i = Q'} is finite.
13. (Infinitely many distinct planes.) Let i_0 := 0 and, recursively, i_{l+1} := the least i with Q_i ∉ {Q_{i_0}, …, Q_{i_l}}; it exists because {i : Q_i ∈ {Q_{i_0}, …, Q_{i_l}}} is a finite union of finite fibres (step 12) while ℕ is infinite. The planes Q*_l := Q_{i_l} (l ∈ ℕ) are pairwise distinct.
14. (Contradiction.) Apply the sibling idtp_tdc_no_infinite_planar_pieces to C, the families Q*_l and z*_l := z_{i_l}, ρ := ρ₀ and R := 1: C is integer multiplicity; ρ₀ > 0; finrank Q*_l = 2; z*_l ∈ Q*_l; |z*_l| = 1 ≤ 1; for l ≠ l', Q*_l ≠ Q*_{l'}, so the discs Q*_l ∩ B_{ρ₀}(z*_l) = D_{i_l} and D_{i_{l'}} are disjoint by step 11; and every w ∈ D_{i_l} has ε > 0 with H²(W ∩ Q*_l) ≤ M_W(C) for every open W ⊆ B_ε(w) by step 10. The sibling yields False. This contradiction proves the claim at every p ∈ spt C ∖ {0}. ∎

## Key steps

1. Densities on spt C ∖ {0} are integers ≥ 1 (idtp_cone_tangent_cone_planar), P ≥ 2, and Θ is upper semicontinuous (dimred_minimizing_monotonicity); spt C, Θ and the jump set J are dilation invariant (idtp_tdc_cone_dilation).
2. If J ≠ ∅, pick b ∈ J ∩ 𝕊 of locally minimal density m₀ and r > 0 with Θ ≤ m₀ on spt C ∩ B_r(b) and Θ = m₀ on J ∩ 𝕊 ∩ B_r(b).
3. Light points z_i ∉ J of density k_i < m₀ accumulate at b, and each has a local plane Q_i (idtp_cone_constant_density_planar).
4. idtp_tdc_arc_continuation, whose endpoint hypothesis follows from (5b), extends each light point to a Good arc of half-length r'/2; by dilation every point of D_i = Q_i ∩ B_{ρ₀}(z_i) is Good, which gives H²(W ∩ Q_i) ≤ M_W(C) locally.
5. Discs on distinct planes are disjoint, and each plane occurs only finitely often (otherwise b would be Good); infinitely many disjoint discs contradict idtp_tdc_no_infinite_planar_pieces.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `sed -n 1,140p simongmt Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; sed -n 20,100p Chapter06/Mass.lean; sed -n 30,135p,305,340p Chapter06/Currents.lean; sed -n 36,60p Chapter06/Forms.lean`
- `grep -rn 'μHE\[' mathlib/Mathlib (notation and API in Geometry/Euclidean/Volume/Measure.lean)`
- `rg -n 'theorem isConnected_sphere|theorem isConnected_compl_singleton_of_one_lt_rank|theorem addHaar_ball |theorem addHaar_ball_of_pos|theorem hausdorffMeasure_zero_singleton|theorem ext_of_generateFrom_of_iUnion|theorem mul_le_sin|theorem closed_of_finiteDimensional|theorem isCompact_sphere|measure_compl_support' mathlib/Mathlib`
- `rg -n 'closed_of_finiteDimensional|class OuterRegular|of_pseudoMetrizableSpace_of_isFiniteMeasure|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|exists_isOpen_lt_of_lt' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n 'measurePreserving' Haar/InnerProductSpace.lean; rg -n 'volume_ball' Lebesgue/VolumeOfBalls.lean; rg -n 'theorem isOpen_iUnion_countable|theorem cos_arg|theorem sin_arg|theorem euclideanHausdorffMeasure_preimage|theorem Orthonormal.linearIndependent' mathlib/Mathlib`
- `python3 scan of dag.json: lean_name collisions for the seven idtp_tdc_* names (none among 817 nodes); exact types and statuses of idtp_cone_tangent_cone_planar, idtp_cone_constant_density_planar, idtp_cone_sector_endpoint_density, idtp_planar_cycle_eq_const_mul, dimred_minimizing_monotonicity, dimred_im_mass_measure, dtc_blowUp_massOn_image, dtc_restrictDomain_isIntegerMultiplicity, cone_current_imrep_measure_smul_image, dtc_density_usc, rsd_massOn_eq_measure, rsd_mem_support_iff_measure_ball_pos, codim1_subspace_ball_euclideanHausdorff`
- `grep for idtp_tdc_ in nodes/*/*.json and workspaces/*/GMT (no match)`
- `sed -n 480,520p book/chapter-07.txt`
- `lake env lean /tmp/tdcd-split-a1/gen/Child_<key>.lean for each of the 7 children; lake env lean /tmp/tdcd-split-a1/gen/Assembly.lean (#print axioms tdc_assembly_check); lake env lean /tmp/tdcd-split-a1/gen/Probe.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/tdcd-split-a1/gen/Assembly.lean`
- `/tmp/tdcd-split-a1/gen/Probe.lean`
- `/tmp/tdcd-split-a1/gen/Child_cone_dilation.lean`
- `/tmp/tdcd-split-a1/gen/Child_subspace_ball_measure.lean`
- `/tmp/tdcd-split-a1/gen/Child_no_infinite_planar_pieces.lean`
- `/tmp/tdcd-split-a1/gen/Child_arc_continuation.lean`
- `/tmp/tdcd-split-a1/gen/Child_density_locally_constant.lean`
- `/tmp/tdcd-split-a1/gen/Child_cone_set_finite_planes.lean`
- `/tmp/tdcd-split-a1/gen/Child_planes_union_vertex_density.lean`

Pins and contract:
- The pins match manifest.json: project b4d606db, mathlib 25730c7c, SimonGMT 2b366308.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT Chapter06 definitions used by the children:
- support = U \ zeroRegion with zeroRegion open, so spt C is closed when U = univ.
- restrictDomain, massOn (sSup over admissible test forms), boundary and TestFormOn (IsTestForm ∧ tsupport ⊆ U).

Mathlib snapshot: it contains every library fact the child proofs cite:
- Isometry.euclideanHausdorffMeasure_preimage, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_zero_or_top, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton.
- Measure.addHaar_ball_of_pos (no Nontrivial hypothesis), LinearIsometryEquiv.measurePreserving.
- isConnected_sphere, isConnected_compl_singleton_of_one_lt_rank, Submodule.closed_of_finiteDimensional, isCompact_sphere.
- Measure.ext_of_generateFrom_of_iUnion, WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, Set.exists_isOpen_lt_of_lt, isOpen_iUnion_countable, Real.mul_le_sin, Complex.cos_arg/sin_arg.

Reuse:
- No accepted DAG declaration has the exact type of any proposed child. codim1_subspace_ball_euclideanHausdorff is closest, but it is not accepted and is centred at 0. cone_current_imrep_measure_smul_image is accepted but states something different.
- Seven new idtp_tdc_* names are therefore used. None occurs in dag.json (817 nodes), in any node JSON file, or in the workspace GMT sources.
- The cited black boxes have their frozen DAG types and elaborate (Probe.lean). dimred_im_mass_measure, dtc_blowUp_massOn_image and dtc_restrictDomain_isIntegerMultiplicity are accepted. dimred_minimizing_monotonicity is in progress, and the parent's own proof already cites it.

Lean checks:
- All seven exact lean_statement strings elaborate after import GMT.Ch07.Submission, each in its own file.
- The hypothesis-only assembly derives the exact selected type idtp_two_dim_cone_integer_density. It uses children cone_dilation, density_locally_constant, cone_set_finite_planes and planes_union_vertex_density, plus the frozen type of idtp_cone_constant_density_planar taken from dag.json. Its axioms are propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
