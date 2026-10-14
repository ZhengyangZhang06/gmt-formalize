<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1.flat_stationarity-a1 -->

## Theorem `Submission.dimred_cdg_or_minimizing_firstVariation_eq_zero`

Let P, j ∈ ℕ, let C ∈ 𝒟_j(ℝ^P) (GeometricCurrentOn (univ : Set (Euclid P)) j), and let R = (M, θ, ξ) ∈ IMRep(ℝ^P, j). Suppose that:
- C is minimizing in ℝ^P (IsMinimizingIn C univ, Simon 7.1.1);
- ∂C = 0 (BoundaryVanishes C);
- R represents C (R.Represents C: C(ω) = ∫_M θ⟨ω, ξ⟩ dH^j for every ω ∈ 𝒟^j(ℝ^P));
- spt C ≠ ∅ (C.support.Nonempty).
Let X : ℝ^P → ℝ^P be any C¹ vector field with compact support. Then the first variation δV(X) = R.firstVariation X = ∫_M θ div_M X dH^j of the associated varifold vanishes. That is, minimizing integer multiplicity cycles in ℝ^P are stationary (Simon 7.1.2, flat case N = ℝ^P).

Node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1.flat_stationarity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6119

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_cdg_or_minimizing_firstVariation_eq_zero`

```lean
∀ (P j : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) j) (R : IMRep (univ : Set (Euclid P)) j), IsMinimizingIn C univ → BoundaryVanishes C → R.Represents C → C.support.Nonempty → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0
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

- Parent DAG node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1.flat_stationarity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 7, Lemma 1.2 (minimizing currents are stationary; chapter-07.txt lines 29–60), in the flat case N = U = ℝ^P. This is step 3 of the parent's supplied proof, together with the support fact of its step 2. The only change is that the origin is replaced by an arbitrary point z of spt C; the parent applies this child with z = 0.

Prerequisites. The proof applies three declarations by their exact Lean names. All three are resolved dependencies of the parent node, so they reach this child as inherited prerequisites:
- (E) `Submission.dor_imrep_massOn_eq_measure_and_support` (comparator-accepted). For all P, n, U ⊆ ℝ^P, T ∈ 𝒟_n(U) and R ∈ IMRep(U, n): if U is open and R represents T, then T.massOn W = R.measure W for every open W, and T.support = U ∩ R.measure.support.
- (F) `Submission.dimred_cdg_c1_diffeo_pushforward_im`. Let P, n, U, K ⊆ ℝ^P, T, R and φ : ℝ^P → ℝ^P be given. Assume:
  - U is open, R represents T, and K is compact with K ⊆ U;
  - φ is C¹ and bijective, Dφ(x) is injective for every x, and φ(x) = x for x ∉ K.
  Then there is an integer multiplicity S ∈ 𝒟_n(U) such that:
  - BoundaryVanishes T → BoundaryVanishes S;
  - S(ω) = ∫_M θ(x) ξ(x)(ω(φ(x)) ∘ Dφ(x)) dH^n(x) for every ω ∈ 𝒟^n(U), where ω(φ(x)) ∘ Dφ(x) is `compContinuousLinearMap`.
- (G) `Submission.dimred_cdg_pushforward_massOn_le_first_variation`. Let P, n, U, W ⊆ ℝ^P, R ∈ IMRep(U, n), a C¹ vector field X with compact support and a family φ : ℝ → (ℝ^P → ℝ^P) be given. Assume:
  - W is open, R.measure W ≠ ∞ and spt X ⊆ W;
  - every φ_t is C¹, and φ_t(x) = x for x ∉ spt X;
  - for every ε > 0 there is δ > 0 with ‖Dφ_t(x) − I − tDX(x)‖ ≤ ε|t| for all |t| < δ and all x.
  Then for every ε > 0 there is δ > 0 with the following property. If |t| < δ and S ∈ 𝒟_n(U) satisfies S(ω) = ∫_M θ ξ(ω(φ_t x) ∘ Dφ_t(x)) dH^n for all ω, then M_W(S) ≤ ofReal((R.measure W).toReal + t·R.firstVariation X + ε|t|).

Notation:
- R = (M, θ, ξ) = (R.carrier, R.mult, R.orient), and μ := R.measure = θH^j⌞M.
- δV(X) := R.firstVariation X = ∫_M θ div_M X dH^j.
- B_r(x) is the open ball, spt X := tsupport X, M_W := massOn and spt C := C.support.

Proof.
1. (Set-up.) Fix P, j, C and R as in the statement, and a C¹ vector field X : ℝ^P → ℝ^P with compact support. Since spt C ≠ ∅, choose z ∈ spt C. Put a := δV(X). We must show a = 0.
2. (Mass and support.) Apply E with U := ℝ^P (open), T := C and R. It gives:
 - (E1) M_W(C) = μ(W) for every open W ⊆ ℝ^P;
 - (E2) spt C = ℝ^P ∩ spt μ.
 By (E2), z ∈ spt μ.
3. (A Lipschitz bound for X.) K := spt X is compact, since X has compact support, and it is closed. X is C¹, so DX is continuous. DX has compact support, because tsupport DX ⊆ spt X. Hence A₀ := sup_x ‖DX(x)‖ is finite. Put A := max(A₀, 0); then A ≥ 0 and ‖DX(x)‖ ≤ A for all x. X is differentiable on the convex set ℝ^P, so the mean value inequality gives |X(x) − X(y)| ≤ A|x − y| for all x, y.
4. (The deformations.) For t ∈ ℝ define φ_t(y) := y + tX(y).
 (a) φ_t is C¹, being the identity plus a constant multiple of X.
 (b) φ_t(x) = x for every x ∉ K, because X(x) = 0 there.
 (c) Dφ_t(x) = I + tDX(x) for all x. Hence ‖Dφ_t(x) − I − tDX(x)‖ = 0 ≤ ε|t| for all ε > 0, t and x. In particular, the derivative hypothesis of G holds with δ := 1 for every ε > 0.
5. (φ_t when |t|A < 1.) Let |t|A < 1.
 (a) φ_t is injective. If φ_t(x) = φ_t(y), then x − y = t(X(y) − X(x)), so |x − y| ≤ |t|A|x − y|. Since |t|A < 1, x = y.
 (b) φ_t is surjective. For all x, y, |(φ_t(x) − φ_t(y)) − (x − y)| = |t||X(x) − X(y)| ≤ |t|A|x − y|. So φ_t approximates the identity isomorphism of ℝ^P on all of ℝ^P with constant |t|A < 1 = ‖I⁻¹‖⁻¹, and φ_t is onto by Mathlib's ApproximatesLinearOn.surjective with f' the identity ContinuousLinearEquiv. If P = 0 the space is a single point and there is nothing to prove. Equivalently, for each y the map x ↦ y − tX(x) is a contraction with constant |t|A < 1 of the complete space ℝ^P, and its fixed point x satisfies φ_t(x) = y.
 (c) Dφ_t(x) is injective for every x. If (I + tDX(x))v = 0, then v = −tDX(x)v, so |v| ≤ |t|‖DX(x)‖|v| ≤ |t|A|v|, and hence v = 0.
 (d) φ_t(K) ⊆ K. Let x ∈ K and suppose φ_t(x) ∉ K. By 4(b) at the point φ_t(x), φ_t(φ_t(x)) = φ_t(x). By (a), φ_t(x) = x ∈ K, a contradiction.
6. (The open set W.) Let K' := K ∪ {z}, a compact set, and W := {y : dist(y, K') < 1}, the open 1-thickening of K'.
 (a) W is open, K ⊆ W, and B_1(z) ⊆ W.
 (b) closure(W) ⊆ {y : dist(y, K') ≤ 1}. This set is compact: it is the closed 1-thickening of a compact set in the proper space ℝ^P. Hence closure(W) is compact, and W ⊂⊂ ℝ^P (CompactlyContained W univ).
 (c) μ is finite on compact sets. Let Q be compact; it is closed, hence measurable. By withDensity_apply and Measure.restrict_restrict, μ(Q) = ∫_{M∩Q} θ dH^j, which is finite by the field locallyIntegrable_mult of R (Q ⊆ ℝ^P). Therefore μ(W) ≤ μ({dist(·, K') ≤ 1}) < ∞.
 (d) μ(W) ≥ μ(B_1(z)) > 0, because z ∈ spt μ (step 2) and B_1(z) is a neighbourhood of z (Measure.mem_support_iff_forall).
 Put m := μ(W).toReal. Then μ(W) = ofReal(m) and m > 0.
7. (First-variation bound.) Suppose, for contradiction, that a ≠ 0. Apply G with U := ℝ^P, this W, R, X, the family φ = (φ_t)_t and ε := |a|/2 > 0. Its hypotheses hold:
 - W is open (6a), and μ(W) ≠ ∞ (6c);
 - X is C¹ with compact support, and spt X = K ⊆ W (6a);
 - each φ_t is C¹ (4a), and φ_t = id off spt X (4b);
 - the derivative condition holds (4c).
 G yields δ_G > 0 with the following property. Let |t| < δ_G and let S ∈ 𝒟_j(ℝ^P) satisfy S(ω) = ∫_M θ(x)ξ(x)(ω(φ_t x) ∘ Dφ_t(x)) dH^j(x) for every ω ∈ 𝒟^j(ℝ^P). Then M_W(S) ≤ ofReal(m + t·a + (|a|/2)|t|).
8. (Choice of t.) Put s := min{δ_G/2, 1/(2(A + 1))} > 0. Let t := −s if a > 0, and t := s if a < 0. Then:
 - |t| = s < δ_G;
 - |t|A = sA ≤ A/(2(A + 1)) < 1;
 - t·a = −s|a|.
 The parent text also caps s by m/|a|. That cap is harmless but unnecessary; see step 12.
9. (The competitor.) Apply F with U := ℝ^P (open), K, T := C, R and φ := φ_t. Its hypotheses hold:
 - R represents C, K is compact, and K ⊆ ℝ^P;
 - φ_t is C¹ (4a) and bijective (5a, 5b), and has injective derivative everywhere (5c);
 - φ_t(x) = x for x ∉ K (4b).
 F yields an integer multiplicity S ∈ 𝒟_j(ℝ^P) such that:
 - BoundaryVanishes C implies BoundaryVanishes S, so ∂S = 0;
 - S(ω) = ∫_M θ(x)ξ(x)(ω(φ_t x) ∘ Dφ_t(x)) dH^j(x) for every ω ∈ 𝒟^j(ℝ^P).
10. (spt(S − C) is a compact subset of K.) Let y ∉ K. Since K is closed, there is r > 0 with B_r(y) ∩ K = ∅. Let ω ∈ 𝒟^j(ℝ^P) with spt ω ⊆ B_r(y). Since R represents C, C(ω) = R.action(ω) = ∫_M θ(x)ξ(x)(ω(x)) dH^j(x). By the definition of the difference of currents, (S − C)(ω) = S(ω) − C(ω). The integrands of S(ω) and C(ω) agree at every x:
 - If x ∈ K, then φ_t(x) ∈ K by 5(d). Since ω vanishes off B_r(y) and B_r(y) ∩ K = ∅, ω(φ_t x) = 0 = ω(x). Also 0 ∘ Dφ_t(x) = 0, so both integrands equal θ(x)ξ(x)(0) = 0.
 - If x ∉ K, then φ_t(x) = x (4b). Also DX(x) = 0, because X vanishes on the open neighbourhood ℝ^P ∖ K of x (fderiv_of_notMem_tsupport). So Dφ_t(x) = I and ω(φ_t x) ∘ Dφ_t(x) = ω(x).
 Hence S(ω) = C(ω), that is, (S − C)(ω) = 0. So S − C vanishes on B_r(y). This ball is open, its closure is compact (it lies in the closed ball B̄_r(y)), and it is contained in ℝ^P. Therefore B_r(y) lies in the zero region of S − C, and y ∉ spt(S − C) = ℝ^P ∖ (zero region). Thus spt(S − C) ⊆ K. The zero region is open, so spt(S − C) is closed; as a closed subset of the compact set K, it is compact. Moreover spt(S − C) ⊆ K ⊆ ℝ^P ∩ W.
11. (Same boundary.) SameBoundary S C holds. If j = 0, it is True by definition. If j = i + 1, then ∂S = 0 by step 9 and ∂C = 0 by hypothesis, so ∂S = ∂C.
12. (Contradiction with minimality.) Apply IsMinimizingIn C univ to W and S. The requirements hold:
 - W is open and W ⊂⊂ ℝ^P (6b);
 - S is integer multiplicity (9), and SameBoundary S C (11);
 - spt(S − C) is compact and contained in univ ∩ W (10).
 Hence M_W(C) ≤ M_W(S). By (E1), M_W(C) = μ(W) = ofReal(m). By steps 7–8, M_W(S) ≤ ofReal(m + t·a + (|a|/2)|t|) = ofReal(m − s|a| + s|a|/2) = ofReal(m − s|a|/2). Since s|a| > 0, m − s|a|/2 < m. Since m > 0, ofReal(m − s|a|/2) < ofReal(m); ENNReal.ofReal_lt_ofReal_iff needs only 0 < m. So ofReal(m) ≤ M_W(S) < ofReal(m), a contradiction. Hence a = δV(X) = 0. ∎

Formalization note. This exact proof was checked for this decomposition in the scratch file /tmp/orgsplit/ChildA.lean, theorem orgsplit_childA:
- Hypotheses: exactly the frozen types of E, F and G. Conclusion: exactly this child's frozen type.
- Build: lake env lean against the frozen GMT.Ch07.Submission (project b4d606d, Mathlib 25730c7c, simongmt 2b36630).
- #print axioms: propext, Classical.choice, Quot.sound.
Lemmas used, by step:
- 3: (hX.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hXc.fderiv (𝕜 := ℝ)); convex_univ.norm_image_sub_le_of_norm_fderiv_le.
- 4: contDiff_id.add (hX.const_smul t); image_eq_zero_of_notMem_tsupport; ((hasFDerivAt_id x).add ((hX.differentiable one_ne_zero x).hasFDerivAt.const_smul t)).fderiv.
- 5: injective_iff_map_eq_zero and ContinuousLinearMap.le_opNorm for (c).
- 5(b): ApproximatesLinearOn.surjective with f' := ContinuousLinearEquiv.refl, c := ⟨|t|·A, _⟩ and ContinuousLinearMap.nnnorm_id; subsingleton_or_nontrivial covers P = 0.
- 6: W := thickening 1 (insert z (tsupport X)), using isOpen_thickening, self_subset_thickening, ball_subset_thickening, closure_thickening_subset_cthickening, IsCompact.cthickening and thickening_subset_cthickening.
- 6, finiteness and positivity: IMRep.measure, withDensity_apply, Measure.restrict_restrict, R.locallyIntegrable_mult and Measure.mem_support_iff_forall.
- 10, the zero region: Metric.isOpen_iff on Kᶜ; the region is witnessed by ball y r, with isCompact_closedBall and closure_ball_subset_closedBall.
- 10, the integrands: (S − C) ω = 0 is S ω − C ω = 0 definitionally (`show`); then rw with the push-forward formula, hR ω, IMRep.action and sub_eq_zero, and congr 1; ext x.
- 10, form identities: 0 ∘ L = 0 and α ∘ I = α by ext and ContinuousAlternatingMap.compContinuousLinearMap_apply; fderiv_of_notMem_tsupport ℝ.
- 10, compactness: spt(S − C) = univ \ zeroRegion is closed by compl_eq_univ_diff and isOpen_zeroRegion.
- 11: a structural match on the degree: | 0, … => trivial | _ + 1, …, h₁, h₂ => h₁.trans h₂.symm.
- 12: ENNReal.ofReal_toReal and ENNReal.ofReal_lt_ofReal_iff.

## Key steps

1. E gives M_W(C) = μ(W) for open W and spt C = spt μ, so a chosen z ∈ spt C lies in spt μ.
2. With A := max(sup‖DX‖, 0), the maps φ_t := id + tX are C¹ and equal id off K := spt X, with Dφ_t = I + tDX. For |t|A < 1 they are bijective, have injective derivative and map K into K.
3. W := {dist(·, K ∪ {z}) < 1} is open, W ⊂⊂ ℝ^P and K ⊆ W, and 0 < m := μ(W) < ∞ because z ∈ spt μ and μ is finite on compact sets.
4. If a := δV(X) ≠ 0, G with ε = |a|/2 gives δ_G. Take s := min(δ_G/2, 1/(2(A + 1))) and t := −s·sign(a), so |t| < δ_G, |t|A < 1 and t·a = −s|a|.
5. F applied to φ_t gives an integer multiplicity S with ∂S = 0 and the push-forward formula. S − C vanishes on every ball missing K, so spt(S − C) is a compact subset of K ⊆ W, and SameBoundary S C holds.
6. Minimality, (E1) and G give ofReal(m) = M_W(C) ≤ M_W(S) ≤ ofReal(m − s|a|/2) < ofReal(m), a contradiction; hence δV(X) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 225,457p GMT/Ch07/Contract.lean (regularSet, approxTangentPlane, tangentialDivergence, IMRep.firstVariation, IsMinimizingIn, SameBoundary, BoundaryVanishes)`
- `grep -n 'def GeometricCurrentOn.VanishesOn|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|def GeometricCurrentOn.massOn|abbrev CurrentOn' simongmt Chapter06/{CurrentLocalEquality,Mass,Currents}.lean`
- `grep -n 'mem_support_iff_forall|protected theorem surjective|norm_image_sub_le_of_norm_fderiv_le|closure_thickening_subset_cthickening|IsCompact.cthickening|fderiv_of_notMem_tsupport|measure_ball_lt_top|compContinuousLinearMap_apply' over Mathlib MeasureTheory/Measure/Support.lean, Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean, Analysis/Calculus/MeanValue.lean, Topology/MetricSpace/Thickening.lean, Analysis/Calculus/FDeriv/Const.lean, MeasureTheory/Measure/Typeclasses/Finite.lean, Topology/Algebra/Module/Alternating/Basic.lean`
- `python3 -I scans of dag.json: status, lean_name and lean_statement of this node, of its five resolved dependencies and of every ancestor dependency; every node whose lean_statement contains 'firstVariation X = 0' together with 'IsMinimizingIn', or the Allard ball-graph or cylinder-graph pattern`
- `grep -c dimred_cdg_or_ dag.json (0); grep -rl dimred_cdg_or_ over nodes/, GMT/ and simongmt Poincare/ (no match); grep -rl --include='*.lean' dimred_cdg_or_ over the snapshot project and mathlib (exit 1, no match); grep over the 4366 workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); git log --all --oneline -S dimred_cdg_or_ (empty)`
- `sed -n over the runtime flow _recursive_lean/{runtime.py,inherited.py,speculation.py}: _existing_lean_name_problem, _inherited_prerequisites and cited_inherited, _overlay_accepted_children, _render_parent_supplied_natural, _reference_use_markdown, _reference_use_problem, draft_eligible`
- `lake env lean /tmp/orgsplit/Assembly.lean, /tmp/orgsplit/ChildA.lean, /tmp/orgsplit/ChildB.lean and /tmp/orgsplit/Linked.lean with #print axioms (toolchain lean-4.35.0-rc3)`
- `python3 -I simulation of cited_inherited on the rendered child proof files: flat_stationarity cites exactly the three resolved dependencies E, F and G of its proof; cylinder_graph cites none`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-origin-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-origin-regularity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v8.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c59c141430/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/speculation.py`
- `/tmp/orgsplit/Assembly.lean`
- `/tmp/orgsplit/ChildA.lean`
- `/tmp/orgsplit/ChildB.lean`
- `/tmp/orgsplit/Linked.lean`

Pins and contract:
- The manifest records project b4d606d and Mathlib 25730c7c. These equal the workspace HEAD and the package Mathlib; SimonGMT is at 2b36630.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- SimonGMT defines the support of a current in U as U minus the union of the open, relatively compact sets W (closure W ⊆ U) on which it vanishes. This is the notion step 10 of flat_stationarity uses.

Reuse:
- No accepted declaration states either child.
- A flat-stationarity lemma exists in the integer-density branch (status rlcr-lean, another parent). It has no support hypothesis and is proved from a different, still unaccepted root theorem. It is therefore neither the same type nor shareable.
- The accepted identical-type twins of the parent's C¹-pushforward and first-variation prerequisites are not used. The children follow the supplied proof.

Names:
- dimred_cdg_or_minimizing_firstVariation_eq_zero and dimred_cdg_or_ball_graph_to_cylinder_graph are fresh.
- The prefix dimred_cdg_or_ occurs nowhere in dag.json, the node files, the snapshot, SimonGMT, the workspace GMT sources, 4366 swarm-worktree Submission files or git history.

Runtime:
- A child reaches its parent's resolved dependencies only by citing their exact Lean names in its frozen proof file. That file embeds this ledger, and cited_inherited scans all of it.
- flat_stationarity cites exactly the three dependencies its proof applies. cylinder_graph cites none, so it can be proved at once.
- This ledger names no unaccepted dependency.

Lean (lake env lean against the frozen GMT.Ch07.Submission):
- Both child types elaborate.
- Assembly.lean proves the parent's frozen type from the frozen types of its mass-support, Allard-graph and graph-regularity prerequisites plus the two child types.
- ChildA.lean proves flat_stationarity from the frozen types of the mass-support, C¹-pushforward and first-variation prerequisites.
- ChildB.lean proves cylinder_graph outright.
- Linked.lean wires these to the real Submission names. Only the five prerequisite stubs use sorry.
- #print axioms for the hypothesis-form theorems: propext, Classical.choice, Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
