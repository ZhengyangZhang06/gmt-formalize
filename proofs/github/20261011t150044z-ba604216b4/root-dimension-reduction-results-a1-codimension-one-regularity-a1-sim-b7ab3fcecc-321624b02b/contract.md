<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1 -->

## Theorem `Submission.codim1_cone_offvertex_unit_multiplicity_rep`

Multiplicity-one representation of a cone that is regular with density one off the vertex. Data: P, m ∈ ℕ with m ≥ 1 and C ∈ 𝒟_m(ℝ^P) (GeometricCurrentOn univ m). Hypotheses: C is integer multiplicity (IsIntegerMultiplicity C); C is a cone (IsConeCurrent C: η_{0,λ#}C = C for every λ > 0); every y ∈ spt C with y ≠ 0 lies in reg C and has Θ^m(μ_C, y) = 1. Conclusion, with M := spt C ∖ {0}: there is ξ : ℝ^P → Λ_m(ℝ^P) such that (i) M is an embedded C¹ m-dimensional submanifold of ℝ^P; (ii) ξ is an orientation of M (IsOrientation m M ξ); (iii) tx ∈ M for every x ∈ M and t > 0; (iv) H^m(M ∩ K) < ∞ for every compact K ⊆ ℝ^P; (v) C(ω) = ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(ℝ^P). In particular C = 0 when M = ∅. H^m = μHE[m].

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4352

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5209, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1211, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4203

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1211, https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5715, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5722, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5731, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5750, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5760, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5772, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5784

## Lean problem

Declaration: `Submission.codim1_cone_offvertex_unit_multiplicity_rep`

```lean
∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m), 1 ≤ m → IsIntegerMultiplicity C → IsConeCurrent C → (∀ y ∈ C.support, y ≠ 0 → y ∈ regularSet C ∧ HasMassDensity C y 1) → ∃ ξ : Euclid P → MultiVector P m, IsEmbeddedSubmanifold 1 m (C.support \ {0}) ∧ IsOrientation m (C.support \ {0}) ξ ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ C.support \ {0}, t • x ∈ C.support \ {0}) ∧ (∀ K : Set (Euclid P), IsCompact K → μHE[m] ((C.support \ {0}) ∩ K) ≠ ∞) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, C ω = ∫ x in C.support \ {0}, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent steps B0.1 (vertex negligibility), B1 (the case spt C ⊆ {0}), B2e, B3 (global orientation and representation off the vertex), B4 (cone structure of spt C) and B10b (passage to all test forms) of the supplied proof of codim1_simons_regular_cone_density. Book: Simon 7.3.1(2) (cones, η_{0,λ#}C = C), Ch. 6, 2.11 (support, chapter-06.txt line 299), 2.23 (push-forward, line 408) and 3.1 (integer multiplicity currents).
Departures from the parent text, stated explicitly.
(i) The parent's finiteness H^m(M ∩ B_ρ(0)) < ∞ (end of B3d) used oriented_piece_mass. That declaration is unaccepted and owned by another parent, so it cannot be a dependency here. Step 6b replaces it by a cone-scaling argument.
(ii) Agreement of the local orientations on overlaps (B3a–B3b) is proved with orientation_sign and a positive bump-form test (step 4), instead of testing against a countable dense family of covectors. The idea is the same.
(iii) The vertex is handled for every test form at once (B0.1 combined with the dominated-convergence argument of B10b, valid for any locally H^m-finite M). So the case M = ∅ (B1) needs no separate treatment: the representation then reads C = 0.

Sibling subproblems used.
- density_one_local_rep (Submission.codim1_density_one_regular_local_rep): if U is open, m ≥ 1, y ∈ reg T and Θ^m(μ_T, y) = 1, there is ρ₀ > 0 with B_{ρ₀}(y) ⊆ U such that for every ρ ∈ (0, ρ₀] there is ξ with:
 - spt T ∩ B_ρ(y) an embedded C¹ m-submanifold oriented by ξ;
 - H^m(spt T ∩ B_ρ(y)) < ∞;
 - T(ω) = ∫_{spt T ∩ B_ρ(y)} ⟨ω, ξ⟩ dH^m whenever tsupport ω ⊆ B_ρ(y).
- vanish_off_support (Submission.dtc_vanish_off_support): S(ω) = 0 whenever tsupport ω is disjoint from spt S.
- cone_pullback_identity (Submission.cone_current_apply_dilation_pullback): for a cone C, λ > 0 and ω ∈ 𝒟^m(ℝ^P) there is ω' ∈ 𝒟^m(ℝ^P) with ω'(z) = λ^{−m}ω(λ^{−1}z) for all z and C(ω') = C(ω).
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): a continuous linear L : Λ_m → Λ^m such that every unit orientation ξ of a subspace satisfies (a) |ξ(α)| ≤ |α|, (b) |L(ξ)| ≤ 1, (c) ξ(L(ξ)) = 1.
- orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg): two unit orientations v, w of the same subspace satisfy w = v or w = −v.
- chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv): for a chart (V, W, ψ) of an embedded C^r submanifold N (r ≥ 1), tangentSpace N (ψ v) = range Dψ(v).
- bilipschitz_measure (Submission.dimred_rpd_bilipschitz_image_measure): if c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b| on E ⊆ ℝ^n (c₁ > 0, c₂ ≥ 0), then c₁ⁿLⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿLⁿ(E).

Notation.
- H^m := μHE[m], B_s(x) := ball x s, ⟨α, ξ⟩ := ξ(α), |α| := covectorEuclideanNorm α (a norm on Λ^m), sup|ω| := sup_x |ω(x)| < ∞ for ω ∈ 𝒟^m(ℝ^P).
- "C vanishes on W" means C(ω) = 0 whenever tsupport ω ⊆ W. Z(C) is the union of the open W with compact closure on which C vanishes; spt C = ℝ^P ∖ Z(C).
- M := spt C ∖ {0}.
Facts on embedded C¹ m-submanifolds N.
(F0) N is Borel.
(F1) For a chart (V, W, ψ), W ∩ N is closed in W and ψ⁻¹ : W ∩ N → V is continuous.
(F2) For open O, N ∩ O is an embedded C¹ m-submanifold, and tangentSpace(N ∩ O, w) = tangentSpace(N, w) = range Dψ(ψ⁻¹(w)) (dimension m) for w ∈ N ∩ O and every chart (V, W, ψ) of N at w.
(F3) H^m(N ∩ B_r(w)) > 0 for w ∈ N and r > 0.
Proofs.
- (F1): if ψ(v_j) → z ∈ W, the compact set K := {z} ∪ {ψ(v_j)} ⊆ W has V ∩ ψ⁻¹(K) compact; a subsequence v_j → v ∈ V with ψ(v) = z. With injectivity of ψ this gives both claims.
- (F0): by (F1) each point of N has an open W with W ∩ N relatively closed in W, and countably many such W cover N.
- (F2): (V ∩ ψ⁻¹(O), W ∩ O, ψ) is a chart of N ∩ O with the same derivative, and chart_tangent_space computes both tangent spaces.
- (F3): near v₀ := ψ⁻¹(w), ψ satisfies c|a − b| ≤ |ψ(a) − ψ(b)| ≤ C|a − b| on a small ball B_δ(v₀) mapped into B_r(w), by the mean value inequality for ψ − Dψ(v₀) and injectivity of Dψ(v₀). bilipschitz_measure then gives H^m(ψ(B_δ(v₀))) ≥ c^m L^m(B_δ(v₀)) > 0.

Proof. Fix P, m ≥ 1 and C as in the statement.
1. (Local pieces.) Let y ∈ M. Then y ∈ spt C and y ≠ 0, so by hypothesis y ∈ reg C and Θ^m(μ_C, y) = 1.
 - Apply density_one_local_rep with U := ℝ^P and T := C to get ρ₀(y). Put ρ_y := min{ρ₀(y), |y|/2} > 0, B_y := B_{ρ_y}(y), and let ξ_y be the orientation given for ρ = ρ_y.
 - Since 0 ∉ B_y, S_y := spt C ∩ B_y = M ∩ B_y.
 - Hence S_y is an embedded C¹ m-submanifold, ξ_y is an orientation of S_y, H^m(S_y) < ∞, and
 (1.1) C(ω) = ∫_{M ∩ B_y} ⟨ω, ξ_y⟩ dH^m for every ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ B_y.
2. (M is an embedded C¹ submanifold.) Let y ∈ M and (V, W, ψ) a chart of S_y at y. Then (V, W ∩ B_y, ψ) is a chart of M at y:
 - W ∩ B_y is open and contains y;
 - ψ(V) = W ∩ S_y ⊆ B_y, so ψ(V) = (W ∩ B_y) ∩ M;
 - for compact K ⊆ W ∩ B_y, V ∩ ψ⁻¹(K) is compact;
 - the remaining clauses are those of the chart of S_y.
 Hence IsEmbeddedSubmanifold 1 m M. By (F2) with N := M and O := B_y, tangentSpace(S_y, w) = tangentSpace(M, w) for w ∈ S_y. spt C is closed, as Z(C) is a union of open sets. Hence M is relatively closed in ℝ^P ∖ {0} and Borel.
3. (Cone property; parent B4.) Let t > 0 and let W be open with compact closure, with C vanishing on W.
 - Let ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ tW. cone_pullback_identity with λ := t⁻¹ gives ω' ∈ 𝒟^m(ℝ^P) with ω'(z) = t^m ω(tz) and C(ω') = C(ω).
 - tsupport ω' = t⁻¹·tsupport ω ⊆ W, so C(ω) = C(ω') = 0. Thus C vanishes on tW.
 - tW is open with compact closure t·closure(W), so tW ⊆ Z(C).
 Hence t·Z(C) ⊆ Z(C) for every t > 0. Applying this to t⁻¹ gives t·Z(C) = Z(C), so t·spt C = spt C. As tx ≠ 0 for x ≠ 0, tx ∈ M for every x ∈ M and t > 0.
4. (Agreement on overlaps.) Let y, y' ∈ M and G := M ∩ B_y ∩ B_{y'}. We show ξ_{y'} = ξ_y on G.
 - For w ∈ G, ξ_y(w) and ξ_{y'}(w) are unit orientations of subspaces whose carrier is tangentSpace(M, w) (step 2), hence of the same subspace (a submodule is determined by its carrier). By orientation_sign, ξ_{y'}(w) = ±ξ_y(w).
 - Suppose ξ_{y'}(w₀) = −ξ_y(w₀) for some w₀ ∈ G. As ξ_y(w₀)(L(ξ_y(w₀))) = 1, ξ_y(w₀) ≠ 0, so ξ_{y'}(w₀) ≠ ξ_y(w₀).
 - By continuity of ξ_y and ξ_{y'} on G, choose r > 0 with B_r(w₀) ⊆ B_y ∩ B_{y'} such that, with β := L(ξ_y(w₀)), for every x ∈ M ∩ B_r(w₀): ξ_{y'}(x) ≠ ξ_y(x), hence ξ_{y'}(x) = −ξ_y(x); and ξ_y(x)(β) ≥ 1/2.
 - Take a smooth φ : ℝ^P → [0, 1] with φ = 1 on closedBall(w₀, r/2) and tsupport φ ⊆ B_r(w₀), and ω := φ·β.
 - By (1.1) for y and for y', C(ω) = ∫_M φ·ξ_y(β) dH^m = ∫_M φ·ξ_{y'}(β) dH^m = −∫_M φ·ξ_y(β) dH^m. So ∫_M φ·ξ_y(β) dH^m = 0.
 - But this integrand is ≥ 0, and ≥ 1/2 on M ∩ B_{r/2}(w₀), which has positive H^m-measure by (F3) (step 2).
 This contradiction shows ξ_{y'} = ξ_y on G.
5. (Global orientation.) Define ξ_M(x) := ξ_x(x) for x ∈ M and ξ_M(x) := 0 for x ∉ M.
 - For y ∈ M and x ∈ M ∩ B_y, step 4 (with y' := x, using x ∈ B_x) gives ξ_M(x) = ξ_x(x) = ξ_y(x). So ξ_M = ξ_y on the relatively open set M ∩ B_y ∋ y.
 - Hence ξ_M is continuous on M, since ξ_y is continuous on S_y = M ∩ B_y.
 - For x ∈ M, ξ_M(x) = ξ_x(x) is a unit orientation of a subspace with carrier tangentSpace(S_x, x) = tangentSpace(M, x) (step 2).
 Thus IsOrientation m M ξ_M.
6. (Local finiteness.)
 (6a) Let K be compact with 0 ∉ K. Then M ∩ K = spt C ∩ K is compact and covered by the open balls B_y (y ∈ M ∩ K), hence by finitely many B_{y_1}, …, B_{y_N}. So H^m(M ∩ K) ≤ Σ_j H^m(S_{y_j}) < ∞.
 (6b) Let R > 0 and A := {x : R/2 ≤ |x| ≤ R}, a compact set with 0 ∉ A, so a := H^m(M ∩ A) < ∞ by (6a).
 - If x ∈ M and |x| ≤ R, then x ≠ 0 and there is k ∈ ℕ with R·2^{−k−1} ≤ |x| ≤ R·2^{−k}. By step 3, 2^k x ∈ M ∩ A, i.e. x ∈ 2^{−k}·(M ∩ A).
 - So M ∩ closedBall(0, R) ⊆ ⋃_{k≥0} 2^{−k}·(M ∩ A).
 - By countable subadditivity and the scaling law H^m(λE) = λ^m H^m(E) for λ > 0 (Mathlib Measure.euclideanHausdorffMeasure_smul₀), H^m(M ∩ closedBall(0, R)) ≤ Σ_{k≥0} 2^{−km} a = a/(1 − 2^{−m}) < ∞, because m ≥ 1.
 (6c) Every compact K lies in some closedBall(0, R), so H^m(M ∩ K) < ∞.
7. (Representation off the vertex; parent B3c.) Let ω ∈ 𝒟^m(ℝ^P) with 0 ∉ tsupport ω. We show C(ω) = ∫_M ⟨ω, ξ_M⟩ dH^m.
 - K := tsupport ω is compact. Each x ∈ K lies in B_x (if x ∈ spt C; then x ∈ M since x ≠ 0) or in the open set O₀ := ℝ^P ∖ spt C.
 - Choose y_1, …, y_N ∈ M with K ⊆ O₀ ∪ B_{y_1} ∪ ⋯ ∪ B_{y_N}, and smooth compactly supported φ_0, …, φ_N with tsupport φ_0 ⊆ O₀, tsupport φ_j ⊆ B_{y_j} for j ≥ 1, and Σ_j φ_j = 1 on K (smooth partition of unity subordinate to this finite cover). Then ω = Σ_j φ_jω with φ_jω ∈ 𝒟^m(ℝ^P).
 - For j ≥ 1, by (1.1) and step 5: C(φ_jω) = ∫_{M ∩ B_{y_j}} ⟨φ_jω, ξ_{y_j}⟩ dH^m = ∫_M ⟨φ_jω, ξ_M⟩ dH^m. The integrand vanishes off B_{y_j}, and ξ_{y_j} = ξ_M on M ∩ B_{y_j}.
 - For j = 0, tsupport(φ_0ω) ⊆ O₀ is disjoint from spt C, so C(φ_0ω) = 0 by vanish_off_support. Also φ_0 = 0 on spt C ⊇ M, so ∫_M ⟨φ_0ω, ξ_M⟩ dH^m = 0.
 - All integrands are measurable (continuous on the Borel set M) and bounded by sup|ω|·1_K (unit_orientation_dual (a)), and H^m(M ∩ K) < ∞ (step 6). So they are integrable, and summing over j by linearity gives the claim.
8. (Vertex negligibility; parent B0.1.) C is integer multiplicity; fix an IMRep R = (M_R, θ_R, ξ_R) of C. For ε ∈ (0, 1/2] fix a smooth χ_ε : ℝ^P → [0, 1] with χ_ε = 1 on B_ε(0) and tsupport χ_ε ⊆ B_{2ε}(0). Let ω ∈ 𝒟^m(ℝ^P). Then C(χ_εω) = ∫_{M_R} θ_R·χ_ε·ξ_R(ω) dH^m → 0 as ε ↓ 0. Here and in step 9, "as ε ↓ 0" means along every sequence ε_k ↓ 0 (equivalently along the countably generated filter 𝓝[>]0), so the sequential dominated convergence theorem applies:
 - by R.orients and unit_orientation_dual (a), |ξ_R(x)(ω(x))| ≤ |ω(x)| ≤ sup|ω| for H^m-a.e. x ∈ M_R;
 - so the integrand is dominated by θ_R·sup|ω|·1_{closedBall(0,1)}, which is integrable on M_R because ∫_{M_R ∩ closedBall(0,1)} θ_R dH^m < ∞ (R.locallyIntegrable_mult);
 - pointwise, χ_ε(x) → 0 for x ≠ 0 (χ_ε(x) = 0 once 2ε ≤ |x|), and H^m({0}) = 0 because m ≥ 1;
 - dominated convergence gives the limit 0.
 Since C(ω) = C(χ_εω) + C((1 − χ_ε)ω), it follows that C(ω) = lim_{ε↓0} C((1 − χ_ε)ω).
9. (Global representation; parent B10b.) Let ω ∈ 𝒟^m(ℝ^P).
 - (1 − χ_ε)ω ∈ 𝒟^m(ℝ^P) vanishes on B_ε(0), so 0 ∉ tsupport((1 − χ_ε)ω). Step 7 gives C((1 − χ_ε)ω) = ∫_M (1 − χ_ε)⟨ω, ξ_M⟩ dH^m.
 - These integrands are dominated by sup|ω|·1_{tsupport ω}, integrable on M by step 6. They converge pointwise on M to ⟨ω, ξ_M⟩, because 0 ∉ M.
 - By dominated convergence along any sequence ε_k ↓ 0, and step 8, C(ω) = ∫_M ⟨ω(x), ξ_M(x)⟩ dH^m(x).
10. Steps 2, 5, 3, 6 and 9 are the five conclusions, with ξ := ξ_M. (If M = ∅ they hold trivially, and step 9 says C = 0.) ∎

## Key steps

1. density_one_local_rep at each y ∈ M, with radius ≤ |y|/2, gives multiplicity-one oriented C¹ pieces M ∩ B_y representing C. Their charts make M an embedded C¹ submanifold.
2. cone_pullback_identity shows the zero region, hence spt C and M, is invariant under dilations.
3. On overlaps the local orientations differ by a sign (orientation_sign). A sign flip on an open piece contradicts a positive bump-form test, so they agree and define a continuous global orientation ξ_M.
4. Local finiteness: compactness away from 0; near 0, cone scaling H^m(2^{−k}E) = 2^{−km}H^m(E) over dyadic annuli.
5. A partition of unity gives C(ω) = ∫_M⟨ω, ξ_M⟩ when 0 ∉ tsupport ω (vanish_off_support off spt C). Vertex negligibility via the IMRep and dominated convergence extends this to every ω.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsMinimizingIn, HasMassDensity, IsConeCurrent, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, unitBallVolume)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|def massOn|structure GeometricCurrentOn|abbrev Covector' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean and Chapter02/{SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldCalculus,AreaFormula}.lean`
- `sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n 'theorem addHaar_ball_of_pos|theorem ContinuousOn.aestronglyMeasurable|theorem setLIntegral_one|measure_sdiff_null' Mathlib`
- `python3 scans of dag.json: 518 nodes by status; children of codimension_one_regularity; accepted nodes whose statements mention IsConeCurrent, regularSet or HasMassDensity; statuses, frozen types and candidate commits of the 6 reused names; status of codim1_massOn_eq_lintegral_of_oriented_rep (decomposing)`
- `runtime.py of flow gmt-claude-b888e19cffb1: _solve_children, _existing_lean_name_problem, _wait_for_accepted_dependencies, _overlay_accepted_children`
- `git grep over all 2770 refs for the 5 new names (no match); git grep 'PseudoMetrizableSpace (MultiVector' in accepted branches`
- `lean -DautoImplicit=false /tmp/simons-split/check/Types2.lean; lean -DautoImplicit=false /tmp/simons-split/check/Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-B.txt 1-282; chapter-02.txt 1162-1440; chapter-05.txt 1290-1380; chapter-06.txt 400-440 and 770-870; chapter-03.txt 290-330; chapter-07-source.txt 900-1010 and 1256-1300`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/simons-split/check/Types2.lean`
- `/tmp/simons-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the selected frozen type and the 6 reused types are unchanged.
Library.
- SimonGMT supplies GeometricCurrentOn, support = U \ zeroRegion with zeroRegion open, and massOn (Chapter06).
- SimonGMT supplies the Appendix B algebra: simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean) and exists_final_exponent (SimonsInequalities.lean).
- It has only pointwise second-fundamental-form algebra (Chapter02/SecondFundamentalForm.lean): no submanifold curvature field, no Simons identity, no Allard theorem, no nonlinear push-forward. These remain book citations inside hypercone_plane and area_comparison.
- The snapshot Mathlib has μHE isometry invariance and μHE = volume on Euclid d (Geometry/Euclidean/Volume/Measure.lean), Measure.euclideanHausdorffMeasure_smul₀, and addHaar_ball_of_pos (MeasureTheory/Measure/Lebesgue/EqHaar.lean:445), used by subspace_ball_measure and offvertex_rep.
DAG.
- codim1_massOn_eq_lintegral_of_oriented_rep is decomposing (unaccepted) under another parent. It cannot be a child or a child dependency here, so only this node's glue uses it.
- The six reused names are accepted with byte-identical types. Candidate commits: dor_ims_unitOrientation_dual 9c8432cb0101, dtc_vanish_off_support 44ef61f79e21, cone_current_apply_dilation_pullback 52115c22ec2d, rsdic_unitOrientation_eq_or_eq_neg fe95347baaed, chart_tangentSpace_eq_range_fderiv d626082a69a0, dimred_rpd_bilipschitz_image_measure 0501e07ced47.
- Overlapping unaccepted nodes cannot be reused: dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure and imrep_c1_diffeo_pushforward_im. Child sessions may reuse them once accepted.
- The 5 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2770 refs.
Lean.
- Types2.lean elaborates all 11 child types (exit 0).
- Assembly2.lean proves the selected frozen type from 4 child types plus oriented_piece_mass as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound and those 5.
- A MultiVector PseudoMetrizableSpace instance workaround from accepted branches was needed and works.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
