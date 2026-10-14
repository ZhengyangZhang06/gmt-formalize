<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.imrep_pushforward-a1 -->

## Theorem `Submission.dimred_cs_sp_imrep_linear_pushforward`

Let P, m ∈ ℕ with m ≥ 1, let R = (M, θ, ξ) be an integer multiplicity triple in ℝ^P (IMRep univ m), let L : ℝ^P → ℝ^P be linear (Euclid P →L[ℝ] Euclid P), and let K ⊆ ℝ^P be compact with μ_R(ℝ^P ∖ K) = 0 (R.measure Kᶜ = 0). Then there is an integer multiplicity triple R' = (N, θ', ξ') in ℝ^P (IMRep univ m) with N ⊆ L(K) and R'.action(ω) = R.action(L^#ω) for every ω ∈ 𝒟^m(ℝ^P) (TestFormOn univ m). Here L^#ω(x)(v_1, …, v_m) := ω(Lx)(Lv_1, …, Lv_m) (affinePullbackForm L 0 ω), so R.action(L^#ω) = ∫_M θ(x)·ξ(x)(ω(Lx)∘Λ^m L) dH^m(x). In Simon's notation: L_#τ(M, θ, ξ) = τ(N, θ', ξ').

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.imrep_pushforward-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4269

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1310, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5388, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1309

## Lean problem

Declaration: `Submission.dimred_cs_sp_imrep_linear_pushforward`

```lean
∀ (P m : ℕ) (R : IMRep (univ : Set (Euclid P)) m) (L : Euclid P →L[ℝ] Euclid P) (K : Set (Euclid P)), 0 < m → IsCompact K → R.measure Kᶜ = 0 → ∃ R' : IMRep (univ : Set (Euclid P)) m, R'.carrier ⊆ L '' K ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, R'.action (ω : DifferentialForm (Euclid P) m) = R.action (affinePullbackForm L 0 (ω : DifferentialForm (Euclid P) m))
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.imrep_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 3.3–3.9 (chapter-06.txt lines 770–860), Lemma 3.9: if f is locally Lipschitz and proper on spt T and T = τ(M, θ, ξ), then f_#T = τ(f(M), θ', ξ') is integer multiplicity. Here f = L is linear, so d^M L_x = L|T_xM, and the triple is carried by the compact set K, so L is proper on it. Steps B4–B10 below follow Simon 3.4–3.8: (3.4)–(3.5) are B4–B5, (3.6) is B9, and (3.7)–(3.8) are B6–B8 and B10.
Departure from the book. Simon's printed argument asserts without proof (3.7) that, for H^m-a.e. y, the approximate tangent space T_y(f(M)) exists and equals d^M f_x(T_xM) for every x ∈ f^{-1}(y) ∩ M_+. That gap is filled here by the parametrized-piece fact A7, proved from bilipschitz pieces and the Lipschitz area formula, which is the route of Federer 3.2.18–3.2.19. Simon's own route to such facts goes through the C^1-submanifold cover of Ch. 3, Lemma 1.2 and the proof of Theorem 1.6 (chapter-03.txt lines 25–143). That cover needs the C^1 Approximation Theorem of Ch. 2, 1.5 (chapter-02.txt line 165), which is not in the pinned library. The quantitative partition A5 supplies a positive lower Lipschitz constant on every piece. The proof cites no DAG declaration; every auxiliary fact is proved in Part A from the pinned libraries.
Library facts (pinned Mathlib 25730c7c and SimonGMT; the Lean proof adds the imports Poincare.SimonGMT.Chapter02.AreaLipschitz and Poincare.SimonGMT.Chapter01.DensityComparison, as accepted submissions already do):
(L1) Lipschitz area formula on injective pieces (SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn). If F : ℝ^m → ℝ^P is Lipschitz, S ⊆ ℝ^m is Borel and F is injective on S, then ∫⁻_{F(S)} g dH^m = ∫⁻_S J_F(a)·g(F(a)) dL^m(a) for every g : ℝ^P → [0, ∞]. Applied to g⁺ and g⁻, this gives the same identity of Bochner integrals for every Borel real g with ∫_{F(S)} |g| dH^m < ∞.
(L2) Lipschitz image bound (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn). If φ is K-Lipschitz on a set S of a metric space, then H^m(φ(S)) ≤ K^m H^m(S). On ℝ^m, μHE[m] = L^m (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). In particular, Lipschitz images of L^m-null sets are H^m-null.
(L3) Linear area formula and Jacobians:
- H^m(A(S)) = normDet(A)·L^m(S) for linear A : ℝ^m → ℝ^P and S ⊆ ℝ^m (Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume);
- J_F(a) := areaJacobianAt F a = normDet(DF(a));
- normDet(cA) = |c|^m normDet(A) (LinearMap.normDet_smul);
- normDet(A)² = det(⟨Ae_j, Ae_k⟩)_{j,k} (LinearMap.normDet_sq_eq_det_gram);
- normDet(A) = 0 iff A is not injective (LinearMap.normDet_eq_zero_iff_ker_ne_bot);
- J_F and areaRegularSet F = {a : F differentiable at a, DF(a) injective} are Borel (SimonGMT measurable_areaJacobianAt, measurableSet_areaRegularSet);
- H^m(F(ℝ^m ∖ areaRegularSet F)) = 0 for Lipschitz F (SimonGMT area_image_compl_regularSet_eq_zero).
(L4) Lusin–Souslin (Mathlib MeasurableSet.image_of_continuousOn_injOn): the image of a Borel subset of ℝ^m under a map that is continuous and injective on it is Borel.
(L5) Lebesgue differentiation (Mathlib IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, applied to L^m): for h ∈ L¹_loc(ℝ^m), L^m-a.e. b satisfies ⨍_{B̄_ρ(b)} |h − h(b)| dL^m → 0 as ρ ↓ 0.
(L6) Upper density theorem (Simon Ch. 1, 3.6 and Remark 3.7(1), chapter-01.txt lines 700–710; SimonGMT Chapter01.simon_remark_3_7_hausdorff). If D ⊆ ℝ^P is Borel with H^m(D) < ∞, then H^m(D ∩ B̄_ρ(x))/ρ^m → 0 as ρ ↓ 0 for H^m-a.e. x ∉ D. SimonGMT states this for the literal outer measure simonHausdorffOuterMeasureReal m, and the following lemmas transfer it to μHE[m]:
- simonHausdorffMeasureReal_toOuterMeasure: that outer measure is the outer measure of simonHausdorffMeasureReal m;
- simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure, simonAreaNormalization_pos, simonAreaNormalization_ne_top: that measure is c_m·μHE[m] with c_m := simonAreaNormalization m ∈ (0, ∞);
- simonHausdorffOuterMeasureReal_isBorelRegular: Borel sets are measurable for it;
- realUnitBallVolume_pos, realUnitBallVolume_ne_top: the density quotient uses closed balls and the constant realUnitBallVolume m ∈ (0, ∞).
Hence null sets and the vanishing of the quotient are the same as for μHE[m].
(L7) Uniqueness of approximate tangent spaces (SimonGMT HasApproximateTangentSpaceAt.unique; Simon Ch. 3, Remark 1.5(1)).
(L8) Partition into approximately linear pieces (Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt), and the antilipschitz bound for injective linear maps (LinearMap.exists_antilipschitzWith).
(L9) Alternating maps:
- if τ is a basis of a space Q and β is an alternating m-form on Q, then β(w) = det(τ.toMatrix w)·β(τ) (AlternatingMap.eq_smul_basis_det, Module.Basis.det_apply);
- an alternating map vanishes on linearly dependent families (AlternatingMap.map_linearDependent);
- |β(v_1, …, v_m)| ≤ ‖β‖·Π_j‖v_j‖ (ContinuousAlternatingMap.le_opNorm).
Notation:
- m ≥ 1 (hypothesis). ℝ^m = Euclid m carries Lebesgue measure L^m; H^m = μHE[m] on ℝ^P.
- For F : ℝ^m → ℝ^P, DF(a) := fderiv ℝ F a and J_F(a) := normDet(DF(a)) ≥ 0.
- For a linear A : ℝ^m → ℝ^P, [A] is the m-vector β ↦ β(Ae_1, …, Ae_m), where e is the standard basis of ℝ^m.
- For an m-vector ζ, L_#ζ is the m-vector β ↦ ζ(β∘Λ^mL), where β∘Λ^mL := β.compContinuousLinearMap L. By the definition of affinePullbackForm, (L^#ω)(x) = ω(Lx)∘Λ^mL, so ξ(x)(L^#ω(x)) = (L_#ξ(x))(ω(Lx)).
- ‖β‖ is the operator norm of an m-covector, and η_{x,r}(y) := r^{-1}(y − x) (blowUpMap).
- "T_xY = Q" abbreviates HasApproximateTangentSpaceAt m Y x Q, and "unit orientation of Q" abbreviates IsUnitOrientationOf.
Part A. Auxiliary facts.
A1 (Blow-up scaling.) For x ∈ ℝ^P and r > 0, η_{x,r} is a homeomorphism of ℝ^P with η_{x,r}^{-1}(B̄_R(0)) = B̄_{rR}(x), and H^m(η_{x,r}(S)) = r^{-m}H^m(S) for every S ⊆ ℝ^P. Proof: η_{x,r} is the homothety with centre x and ratio r^{-1}, which multiplies H^m by r^{-m} (Mathlib euclideanHausdorffMeasure_homothety_image), followed by the isometry y ↦ y − x (Isometry.euclideanHausdorffMeasure_image).
A2 (Null modifications.) If H^m(A ∖ B) = H^m(B ∖ A) = 0, then for every x and Q, T_xA = Q ⟺ T_xB = Q. Proof: for r > 0, η_{x,r} is a bijection, so η_{x,r}(A) △ η_{x,r}(B) = η_{x,r}(A △ B), which is H^m-null by A1. Hence H^m⌞η_{x,r}(A) = H^m⌞η_{x,r}(B), and the integrals in Simon Ch. 3, Definition 1.4 coincide for every f and r. The dimension condition is the same on both sides.
A3 (Locality.) Let A' ⊆ Y ⊆ ℝ^P be Borel with H^m(Y) < ∞. Then for H^m-a.e. x ∈ A' and every Q, T_xY = Q ⟺ T_xA' = Q. Proof:
- D := Y ∖ A' is Borel with H^m(D) < ∞, and A' ∩ D = ∅. By L6, H^m(D ∩ B̄_ρ(x))/ρ^m → 0 for H^m-a.e. x ∈ A'.
- Fix such an x, f ∈ C_c(ℝ^P) with |f| ≤ c_f and f = 0 off B̄_R(0) (WLOG R ≥ 1), and r > 0. Since η_{x,r} is injective, η_{x,r}(Y) is the disjoint union of the Borel sets η_{x,r}(A') and η_{x,r}(D).
- By A1, H^m(η_{x,r}(Y) ∩ B̄_R(0)) = r^{-m}H^m(Y ∩ B̄_{rR}(x)) < ∞, so f is integrable on all three sets. Hence |∫_{η_{x,r}(Y)} f dH^m − ∫_{η_{x,r}(A')} f dH^m| = |∫_{η_{x,r}(D)} f dH^m| ≤ c_f H^m(η_{x,r}(D) ∩ B̄_R(0)) = c_f R^m·H^m(D ∩ B̄_{rR}(x))/(rR)^m → 0 as r ↓ 0.
- So for every f the two blow-up integrals converge to ∫_Q f dH^m together or not at all. The dimension conditions agree, hence T_xY = Q ⟺ T_xA' = Q.
A4 (Bilipschitz comparison.) Let F : ℝ^m → ℝ^P, S ⊆ ℝ^m and c > 0 satisfy c|a − a'| ≤ |F(a) − F(a')| for a, a' ∈ S. Then L^m(S) ≤ c^{-m}H^m(F(S)) (outer measures). Proof: F is injective on S, and the inverse φ : F(S) → S, φ(F(a)) = a, is c^{-1}-Lipschitz on F(S). By L2, L^m(S) = H^m(φ(F(S))) ≤ c^{-m}H^m(F(S)).
A5 (Quantitative partition.) Let G : ℝ^m → ℝ^P and B ⊆ ℝ^m Borel, with G differentiable at every b ∈ B and DG(b) injective. Then there are pairwise disjoint Borel sets C_l (l ∈ ℕ) with ⋃_l C_l = B, and constants d_l > 0 with d_l|a − a'| ≤ |G(a) − G(a')| for all a, a' ∈ C_l. Proof:
- If B = ∅, take C_l = ∅ and d_l = 1.
- Otherwise choose r(A) > 0 for every linear A : ℝ^m → ℝ^P. If A is injective, L8 gives K_A > 0 with |v| ≤ K_A|Av| for all v; put κ_A := 1/K_A and r(A) := κ_A/2. Otherwise put r(A) := 1.
- L8 (with s = B and f' = DG; HasFDerivWithinAt holds because G is differentiable on B) gives pairwise disjoint Borel t_l and linear A_l such that: B ⊆ ⋃_l t_l; |G(a) − G(a') − A_l(a − a')| ≤ r(A_l)|a − a'| for a, a' ∈ B ∩ t_l (ApproximatesLinearOn); and A_l = DG(y_l) for some y_l ∈ B, so A_l is injective.
- Put C_l := B ∩ t_l and d_l := κ_{A_l}/2. For a, a' ∈ C_l, |G(a) − G(a')| ≥ |A_l(a − a')| − (κ_{A_l}/2)|a − a'| ≥ κ_{A_l}|a − a'| − (κ_{A_l}/2)|a − a'| = d_l|a − a'|.
A6 (Bilipschitz pieces of a rectifiable set.) Let M₁ ⊆ ℝ^P be Borel and countably m-rectifiable. Then there are Lipschitz F_i : ℝ^m → ℝ^P, Borel B_i ⊆ ℝ^m and c_i > 0 (i ∈ ℕ) such that:
- c_i|b − b'| ≤ |F_i(b) − F_i(b')| for b, b' ∈ B_i;
- F_i is differentiable with injective derivative at every b ∈ B_i;
- the sets F_i(B_i) are Borel, pairwise disjoint and contained in M₁;
- H^m(M₁ ∖ ⋃_i F_i(B_i)) = 0.
Proof:
- By Simon Ch. 3, Definition 1.1 (SimonGMT CountablyRectifiable), M₁ ⊆ Z₀ ∪ ⋃_j F_j(ℝ^m) with H^m(Z₀) = 0 and each F_j Lipschitz.
- Reg_j := areaRegularSet F_j is Borel and H^m(F_j(ℝ^m ∖ Reg_j)) = 0 (L3). S_j := Reg_j ∩ F_j^{-1}(M₁) is Borel. Apply A5 to F_j on S_j, getting pieces S_{j,l} and constants c_{j,l}.
- Enumerate the pairs (j, l) by i ∈ ℕ and write F'_i, B'_i, c_i. Each F'_i(B'_i) is Borel (L4: F'_i is continuous, and injective on B'_i) and contained in M₁.
- Disjointify recursively: B_i := B'_i ∖ F'^{-1}_i(⋃_{i'<i} F'_{i'}(B_{i'})), which is Borel. Then F'_i(B_i) = F'_i(B'_i) ∖ ⋃_{i'<i} F'_{i'}(B_{i'}), these images are pairwise disjoint, and ⋃_i F'_i(B_i) = ⋃_i F'_i(B'_i) = M₁ ∩ ⋃_j F_j(Reg_j).
- Hence M₁ ∖ ⋃_i F'_i(B_i) ⊆ Z₀ ∪ ⋃_j F_j(ℝ^m ∖ Reg_j), which is H^m-null. Subsets of B'_i keep the lower Lipschitz bound and the differentiability. Rename F'_i as F_i.
A7 (Tangent spaces along a bilipschitz piece; the fact (TF).) Let:
- F : ℝ^m → ℝ^P be Λ-Lipschitz;
- B ⊆ ℝ^m be Borel and c > 0, with c|a − a'| ≤ |F(a) − F(a')| for a, a' ∈ B;
- F be differentiable at every b ∈ B with DF(b) injective;
- Y ⊆ ℝ^P be Borel with F(B) ⊆ Y and H^m(Y) < ∞.
Then for L^m-a.e. b ∈ B, T_{F(b)}Y = range DF(b).
Proof.
(1) F(B) is Borel (L4). For every Borel E ⊆ B, H^m(F(E)) = ∫_E J_F dL^m by L1 with g = 1, and this is ≤ Λ^m L^m(E) by L2.
(2) Put h := 1_B·J_F. It is Borel and locally integrable: for bounded Borel D, ∫_D h dL^m = H^m(F(B ∩ D)) ≤ Λ^m L^m(D) < ∞ by (1). By L5, for L^m-a.e. b, ⨍_{B̄_ρ(b)} |h − h(b)| dL^m → 0 as ρ ↓ 0.
(3) (Blow-up convergence and identification with range DF(b).) Fix b ∈ B satisfying (2), and put x := F(b), A := DF(b), Q := range A.
- A is injective, so dim Q = m, and by L8 there is κ > 0 with |Av| ≥ κ|v|. Also h(b) = J_F(b) = normDet(A).
- Let f ∈ C_c(ℝ^P) with |f| ≤ c_f and f = 0 off B̄_R(0), where WLOG R ≥ 1. Put R₁ := max(R/c, R/κ) > 0 and D := B̄_{R₁}(0) ⊆ ℝ^m.
 (a) For r > 0 let G_r := η_{x,r}∘F, i.e. G_r(a) = r^{-1}(F(a) − F(b)). G_r is Lipschitz and injective on B, and η_{x,r}(F(B)) = G_r(B). Moreover J_{G_r}(a) = r^{-m}J_F(a) for every a. Where F is differentiable, DG_r(a) = r^{-1}DF(a), and L3 gives normDet(r^{-1}DF(a)) = r^{-m}normDet(DF(a)). Where F is not differentiable, neither is G_r (since F = F(b) + rG_r), and both Jacobians are normDet(0) = 0 (m ≥ 1).
 (b) If a ∈ B and |G_r(a)| ≤ R, then c|a − b| ≤ |F(a) − F(b)| ≤ rR. So G_r(B) ∩ B̄_R(0) ⊆ G_r(B ∩ B̄_{rR/c}(b)), and since G_r is (Λ/r)-Lipschitz, L2 gives H^m(G_r(B) ∩ B̄_R(0)) ≤ (Λ/r)^m L^m(B̄_{rR/c}(b)) < ∞. Hence f is H^m-integrable on G_r(B), and L1 applied to f⁺ and f⁻ gives ∫_{G_r(B)} f dH^m = ∫_B r^{-m}J_F(a)f(G_r(a)) dL^m(a).
 (c) Substitute a = b + rz, using Mathlib Measure.integral_comp_smul and the translation invariance of L^m. This gives ∫_{η_{x,r}(F(B))} f dH^m = ∫_{ℝ^m} h(b + rz)f(g_r(z)) dL^m(z), where g_r(z) := r^{-1}(F(b + rz) − F(b)) = G_r(b + rz). If h(b + rz)f(g_r(z)) ≠ 0, then b + rz ∈ B and |g_r(z)| ≤ R, so c|z| ≤ |g_r(z)| ≤ R and z ∈ D. So the integral is over D.
 (d) By L3, H^m⌞Q is the image of normDet(A)·L^m under A: for Borel S ⊆ ℝ^P, H^m(Q ∩ S) = H^m(A(A^{-1}S)) = normDet(A)·L^m(A^{-1}S). Therefore ∫_Q f dH^m = ∫_{ℝ^m} h(b)f(Az) dL^m(z). Here f(Az) ≠ 0 forces κ|z| ≤ |Az| ≤ R, so this integral is over D as well.
 (e) Subtracting, |∫_{η_{x,r}(F(B))} f dH^m − ∫_Q f dH^m| ≤ c_f∫_D |h(b + rz) − h(b)| dL^m(z) + h(b)∫_D |f(g_r(z)) − f(Az)| dL^m(z).
  - The first integral equals r^{-m}∫_{B̄_{rR₁}(b)} |h − h(b)| dL^m = L^m(B̄_{R₁}(0))·⨍_{B̄_{rR₁}(b)} |h − h(b)| dL^m, which → 0 by (2).
  - For the second, let ε > 0. Since f is uniformly continuous, there is δ_f > 0 with |f(u) − f(u')| < ε whenever |u − u'| < δ_f. Differentiability of F at b gives ρ₀ > 0 with |F(b + w) − F(b) − Aw| ≤ (δ_f/(2R₁))|w| for |w| ≤ ρ₀. For 0 < r ≤ ρ₀/R₁ and z ∈ D, |g_r(z) − Az| = r^{-1}|F(b + rz) − F(b) − A(rz)| ≤ δ_f/2. Hence |f(g_r(z)) − f(Az)| < ε, and the second integral is ≤ εL^m(D).
  So ∫_{η_{x,r}(F(B))} f dH^m → ∫_Q f dH^m as r ↓ 0, for every f ∈ C_c(ℝ^P). Since dim Q = m, this says T_{F(b)}F(B) = range DF(b).
(4) (Transfer to Y.) By A3 with A' := F(B) ⊆ Y, there is an H^m-null set Z ⊆ F(B) such that T_xY = Q ⟺ T_xF(B) = Q for every x ∈ F(B) ∖ Z and every Q. By A4, L^m({b ∈ B : F(b) ∈ Z}) ≤ c^{-m}H^m(Z) = 0. Together with (3), T_{F(b)}Y = range DF(b) for L^m-a.e. b ∈ B. ∎(A7)
A8 (Linear algebra of simple m-vectors; Simon 6.3.4–3.5.)
(i) Let Q ⊆ ℝ^P be an m-dimensional subspace with orthonormal basis τ = (τ_1, …, τ_m), and A : ℝ^m → ℝ^P linear with range A ⊆ Q. Write Ae_j = Σ_l a_{jl}τ_l. Then [A](β) = det(a)·β(τ_1, …, τ_m) for every m-covector β, and normDet(A) = |det a|.
 Proof: the restriction of β to Q is an alternating m-form on Q. The coordinate matrix of (Ae_j)_j in the basis τ is aᵀ, so L9 gives β(Ae_1, …, Ae_m) = det(a)β(τ). By L3 and the orthonormality of τ, normDet(A)² = det(⟨Ae_j, Ae_k⟩) = det(aaᵀ) = (det a)².
(ii) If A : ℝ^m → ℝ^P is injective and ζ is a unit orientation of Q := range A, then normDet(A) > 0 and [A] = ±normDet(A)·ζ.
 Proof: by IsUnitOrientationOf, ζ = ±[τ] for an orthonormal family τ spanning Q. Since dim Q = m, τ is an orthonormal basis of Q. By (i), [A] = det(a)[τ] with |det a| = normDet(A), which is > 0 by L3.
(iii) If A is injective, η_A := [A]/normDet(A) is a unit orientation of range A. Indeed, by (i) applied with any orthonormal basis τ of range A, [A] = ±normDet(A)[τ], so η_A = ±[τ].
(iv) Two unit orientations ζ = ±[τ] and ζ' = ±[τ'] of the same m-dimensional Q satisfy ζ' = ±ζ. Apply (i) to the map e_j ↦ τ'_j: [τ'] = det(o)[τ], where o is the change-of-basis matrix. By (i) and L3, (det o)² = normDet(e_j ↦ τ'_j)² = det(⟨τ'_j, τ'_k⟩) = 1, so det o = ±1. Also −ζ is a unit orientation of Q.
(v) If A is not injective, then [A] = 0, because the vectors Ae_j are linearly dependent (L9).
(vi) For a unit orientation ζ = ±[τ] and every m-covector β:
 - |ζ(β)| = |β(τ)| ≤ ‖β‖;
 - |(L_#ζ)(β)| = |β(Lτ_1, …, Lτ_m)| ≤ ‖L‖^m‖β‖ (L9);
 - L_#[A] = [L∘A] by definition.
(vii) normDet(L∘A) ≤ ‖L‖^m normDet(A) for every linear A : ℝ^m → ℝ^P.
 Proof: let S := B̄_1(0) ⊆ ℝ^m, so 0 < L^m(S) < ∞. By L3 and L2, normDet(L∘A)L^m(S) = H^m(L(A(S))) ≤ ‖L‖^m H^m(A(S)) = ‖L‖^m normDet(A)L^m(S).
Part B. Construction of R'.
B0 (Reductions.) Write M := R.carrier, θ := R.mult, ξ := R.orient and μ_R := R.measure.
- By aestronglyMeasurable_orient there is a strongly measurable (hence Borel) ξ̃ with ξ = ξ̃ H^m⌞M-a.e. Replacing ξ by ξ̃ does not change R.action, since the integrands agree H^m⌞M-a.e. It also keeps every IMRep field, since orients still holds a.e. So we may assume ξ is Borel.
- θ is measurable, and θ ≥ 1 on M (mult_pos).
B1 (Localization to K.)
- K is compact, hence Borel. μ_R(ℝ^P ∖ K) = ∫⁻_{M∖K} θ dH^m = 0 (withDensity_apply, Measure.restrict_restrict). Since θ ≥ 1 on M, H^m(M ∖ K) = 0.
- Put M₁ := M ∩ K. It is Borel and countably m-rectifiable (CountablyRectifiable.mono). Also I := ∫_{M₁} θ dH^m = μ_R(K) < ∞ (locallyIntegrable_mult with K compact), and H^m(M₁) ≤ I.
- Since H^m⌞M = H^m⌞M₁, R.action(η) = ∫_{M₁} θξ(η) dH^m for every m-form η.
- By A2, T_xM = Q ⟺ T_xM₁ = Q for all x and Q.
B2 (Source pieces.) Apply A6 to M₁. This gives Lipschitz F_i (with constants Λ_i), Borel B_i and constants c_i > 0.
B3 (Good source parameters.) Fix i.
- (1) By A7 (F := F_i, B := B_i, Y := M₁; here F_i(B_i) ⊆ M₁ and H^m(M₁) < ∞), T_{F_i(b)}M₁ = range DF_i(b) for L^m-a.e. b ∈ B_i.
- (2) Let Bad ⊆ M be the set of x for which there is no subspace Q with T_xM = Q and ξ(x) a unit orientation of Q. By R.orients, Bad is H^m-null (use restrict_apply' with M Borel). By A4, L^m({b ∈ B_i : F_i(b) ∈ Bad}) = 0.
- For b outside both null sets, B1 gives T_{F_i(b)}M = range DF_i(b), and L7 gives Q = range DF_i(b). Thus ξ(F_i(b)) is a unit orientation of range DF_i(b).
- Choose a Borel L^m-null set N_i containing the exceptional set (exists_measurable_superset_of_null), and replace B_i by B_i ∖ N_i. F_i(B_i ∩ N_i) is H^m-null by L2, so all conclusions of A6 persist.
Henceforth, for every i and every b ∈ B_i, ξ(F_i(b)) is a unit orientation of range DF_i(b).
B4 (Orientation on the source pieces; Simon 3.4–3.5.)
- Let G_i := L∘F_i. It is ‖L‖Λ_i-Lipschitz, and by the chain rule it is differentiable at every b ∈ B_i with DG_i(b) = L∘DF_i(b).
- For b ∈ B_i, A8(ii) (with A := DF_i(b) and ζ := ξ(F_i(b))) gives [DF_i(b)] = ε_i(b)J_{F_i}(b)ξ(F_i(b)), with ε_i(b) ∈ {1, −1} and J_{F_i}(b) > 0. Applying L_# (A8(vi)) gives J_{F_i}(b)·L_#ξ(F_i(b)) = ε_i(b)[DG_i(b)].
- ε_i(b) = 1 iff [DF_i(b)] = J_{F_i}(b)ξ(F_i(b)). Both sides are Borel functions of b (measurable_fderiv, L3, and continuity of A ↦ [A]), so ε_i is Borel.
B5 (Target pieces.)
- B_i^+ := B_i ∩ areaRegularSet(G_i) = {b ∈ B_i : DG_i(b) injective} is Borel (L3). For b ∈ B_i ∖ B_i^+, [DG_i(b)] = 0 (A8(v)).
- Apply A5 to G_i on B_i^+. This gives pairwise disjoint Borel C_{i,l} with ⋃_l C_{i,l} = B_i^+, and d_{i,l} > 0 with d_{i,l}|c − c'| ≤ |G_i(c) − G_i(c')| on C_{i,l}.
- Enumerate the pairs (i, l) by k ∈ ℕ and write F_k := F_{i(k)}, G_k := G_{i(k)}, ε_k := ε_{i(k)}, C_k := C_{i(k),l(k)} and d_k. Then:
 - A_k := F_k(C_k) are Borel (L4) and pairwise disjoint subsets of M₁, being pieces of the disjoint sets F_i(B_i) with F_i injective on B_i.
 - G_k is injective on C_k, and DG_k(c) is injective for c ∈ C_k. N_k := G_k(C_k) = L(A_k) is Borel (L4).
 - g_k : N_k → C_k, the inverse of G_k|C_k, is Borel: for Borel S ⊆ C_k, g_k^{-1}(S) = G_k(S) is Borel by L4.
 - N₀ := ⋃_k N_k is Borel, N₀ ⊆ L(M₁) ⊆ L(K), and H^m(N₀) ≤ ‖L‖^m H^m(M₁) < ∞ (L2).
 - η_k(c) := [DG_k(c)]/J_{G_k}(c) (c ∈ C_k) is a unit orientation of range DG_k(c) (A8(iii)), and it is Borel in c.
 - J_{G_k}(c) = normDet(L∘DF_k(c)) ≤ ‖L‖^m J_{F_k}(c) (A8(vii)).
B6 (Tangent spaces of the image; this fills the gap in Simon 3.7.)
- For each k, A7 (F := G_k, B := C_k, c := d_k, Y := N₀) gives an L^m-null set E_k ⊆ C_k such that T_{G_k(c)}N₀ = range DG_k(c) for c ∈ C_k ∖ E_k.
- H^m(G_k(E_k)) = 0 (L2). Let E' ⊇ ⋃_k G_k(E_k) be Borel and H^m-null.
- Let y ∈ N₀ ∖ E' and let k satisfy y ∈ N_k. Then g_k(y) ∉ E_k, so T_yN₀ = range DG_k(g_k(y)). By L7 these planes coincide for all such k; call the common plane T_y.
B7 (Reference orientation and signs; Simon 3.7–3.8.)
- For y ∈ N₀ let k(y) := min{k : y ∈ N_k}. This is Borel, since {k(y) = k} = N_k ∖ ⋃_{k'<k} N_{k'}.
- Put ξ'(y) := η_{k(y)}(g_{k(y)}(y)) on N₀ and ξ'(y) := 0 off N₀. Then ξ' is Borel, and for y ∈ N₀ ∖ E' it is a unit orientation of T_y.
- For y ∈ N₀ ∖ E' with y ∈ N_k, η_k(g_k(y)) is also a unit orientation of T_y. By A8(iv), η_k(g_k(y)) = σ_k(y)ξ'(y) with σ_k(y) ∈ {±1}. Define σ_k(y) := 1 if η_k(g_k(y)) = ξ'(y), and −1 otherwise; this is Borel on N_k.
B8 (Integer multiplicity.)
- Θ(y) := Σ_k 1_{N_k}(y)θ(F_k(g_k(y))) ∈ [0, ∞] is Borel.
- By L1 for G_k on C_k (with g := θ∘F_k∘g_k on N_k, using g_k(G_k(c)) = c), then B5, then L1 for F_k on C_k: ∫_{N_k} θ(F_k(g_k(y))) dH^m(y) = ∫_{C_k} J_{G_k}·θ∘F_k dL^m ≤ ‖L‖^m∫_{C_k} J_{F_k}·θ∘F_k dL^m = ‖L‖^m∫_{A_k} θ dH^m.
- Summing by monotone convergence, and using that the A_k are disjoint subsets of M₁: ∫Θ dH^m ≤ ‖L‖^m I < ∞. Hence Θ < ∞ H^m-a.e.
- If Θ(y) < ∞, only finitely many k have y ∈ N_k, because θ ≥ 1 on A_k ⊆ M. Then set s(y) := Σ_{k: y∈N_k} θ(F_k(g_k(y)))ε_k(g_k(y))σ_k(y) ∈ ℤ. Otherwise set s(y) := 0. s is Borel and |s| ≤ Θ.
B9 (Representation formula; Simon 3.6–3.8.) Let ω ∈ 𝒟^m(ℝ^P) and c_ω := sup_y‖ω(y)‖ < ∞. Put φ(x) := θ(x)(L_#ξ(x))(ω(Lx)) = θ(x)ξ(x)(L^#ω(x)).
 (a) φ is Borel on M, and |φ| ≤ c_ω‖L‖^mθ H^m-a.e. on M (A8(vi) and R.orients). So φ is integrable on M₁, and R.action(L^#ω) = ∫_{M₁} φ dH^m by B1.
 (b) H^m(M₁ ∖ ⋃_i F_i(B_i)) = 0 and the F_i(B_i) are disjoint and Borel, so ∫_{M₁} φ = Σ_i∫_{F_i(B_i)} φ (integral_iUnion).
 (c) By L1 (F_i is injective on B_i) and B4, ∫_{F_i(B_i)} φ dH^m = ∫_{B_i} J_{F_i}(b)φ(F_i(b)) db = ∫_{B_i} θ(F_i(b))ε_i(b)[DG_i(b)](ω(G_i(b))) db. The integrand vanishes on B_i ∖ B_i^+ (B5). Splitting B_i^+ = ⨆_l C_{i,l} and re-indexing gives R.action(L^#ω) = Σ_k∫_{C_k} θ(F_k(c))ε_k(c)[DG_k(c)](ω(G_k(c))) dc. The double series converges absolutely: its k-th term is bounded by ∫_{A_k}|φ| dH^m (L1), and Σ_k∫_{A_k}|φ| ≤ ∫_{M₁}|φ| < ∞.
 (d) For c ∈ C_k, [DG_k(c)] = J_{G_k}(c)η_k(c). So the k-th integrand is J_{G_k}(c)ψ_k(G_k(c)), where ψ_k(y) := θ(F_k(g_k(y)))ε_k(g_k(y))η_k(g_k(y))(ω(y)) on N_k and ψ_k := 0 elsewhere. ψ_k is Borel, |ψ_k| ≤ c_ω1_{N_k}θ(F_k∘g_k) by A8(vi), and it is integrable by B8. L1 for G_k on C_k gives ∫_{C_k} J_{G_k}·ψ_k∘G_k dL^m = ∫_{N_k} ψ_k dH^m.
 (e) Since Σ_k∫|ψ_k| dH^m ≤ c_ω∫Θ dH^m < ∞, Σ_k∫ψ_k = ∫Σ_kψ_k (integral_tsum). For y ∈ N₀ ∖ E' with Θ(y) < ∞, B7 gives Σ_kψ_k(y) = Σ_{k: y∈N_k} θ(F_k(g_k(y)))ε_k(g_k(y))σ_k(y)ξ'(y)(ω(y)) = s(y)ξ'(y)(ω(y)). Off N₀ both sides vanish. Hence R.action(L^#ω) = ∫ s(y)ξ'(y)(ω(y)) dH^m(y).
B10 (The triple R'.) Put N := {y ∈ N₀ ∖ E' : Θ(y) < ∞, s(y) ≠ 0}, θ'(y) := |s(y)| and ξ''(y) := sign(s(y))ξ'(y). The fields of IMRep univ m hold:
- N is Borel, and N ⊆ N₀ ⊆ L(K) ⊆ univ.
- N is countably m-rectifiable: N ⊆ ⋃_k G_k(ℝ^m) with every G_k Lipschitz (Definition 1.1 with M₀ = ∅).
- θ' is measurable, ℕ-valued and ≥ 1 on N.
- Local integrability: ∫_{N∩C} θ' dH^m ≤ ∫Θ dH^m < ∞ for every compact C.
- ξ'' is Borel, hence H^m⌞N-a.e. strongly measurable.
- Orientation: apply A3 with A' := N ⊆ Y := N₀ (H^m(N₀) < ∞). For H^m-a.e. y ∈ N, T_yN = T_yN₀ = T_y (B6), and ξ''(y) = ±ξ'(y) is a unit orientation of T_y (B7, A8(iv)).
- Action: θ'ξ'' = sξ' on N, and s = 0 off N ∪ E' with H^m(E') = 0. So R'.action(ω) = ∫_N θ'ξ''(ω) dH^m = ∫ sξ'(ω) dH^m = R.action(L^#ω) by B9.
Thus R' := (N, θ', ξ'') is an IMRep in ℝ^P with R'.carrier ⊆ L(K) and R'.action(ω) = R.action(L^#ω) for every ω ∈ 𝒟^m(ℝ^P). The construction also covers the degenerate case: if every B_i^+ is empty, then N₀ = N = ∅, all sums are empty and both sides vanish. ∎

## Key steps

1. Auxiliary facts are proved inline (A1–A4):
- blow-up scaling;
- invariance of approximate tangent spaces under null modifications;
- locality through the upper density theorem;
- L^m(S) ≤ c^{-m}H^m(F(S)) on sets where F has lower Lipschitz constant c.
2. Quantitative partition (A5–A6). Mathlib's approximately linear partition with error κ_A/2 gives every piece the lower Lipschitz constant κ_A/2. So M₁ = M ∩ K is covered H^m-a.e. by disjoint bilipschitz pieces F_i(B_i).
3. (TF), step A7. On a bilipschitz piece, four ingredients make the blow-ups of F(B) at F(b) converge to H^m⌞range DF(b):
- the area formula;
- the substitution a = b + rz;
- Lebesgue points of 1_B·J_F;
- differentiability at b.
Locality then transfers the tangent plane to any Borel Y ⊇ F(B) of finite measure, for L^m-a.e. b.
4. On the source pieces ξ(F_i(b)) orients range DF_i(b), so J_{F_i}·L_#ξ(F_i(b)) = ±[DG_i(b)] with G_i = L∘F_i. This vanishes where DG_i is singular, and the regular part splits into bilipschitz pieces C_k of G_k.
5. (TF) for G_k gives a common tangent plane T_y of N₀ = ⋃_k G_k(C_k) for H^m-a.e. y. The signs σ_k relative to a reference orientation ξ' give the integer multiplicity s = Σ_k θ·ε_k·σ_k, which is integrable because J_{G_k} ≤ ‖L‖^m J_{F_k}.
6. Two area formulas turn R.action(L^#ω) into ∫ s·ξ'(ω) dH^m. Then R' = (N, |s|, sign(s)ξ'), with N = {s ≠ 0}, is an IMRep carried by L(K); its orientation property follows from locality.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `python3 over dag.json: status counts; lean names, types and statuses of all nodes matching tangent|bilipschitz|pushforward|area; every node whose lean_statement contains HasApproximateTangentSpaceAt; accepted nodes that construct an IMRep or IsIntegerMultiplicity. Found: dpf_approxTangent_ae_bilipschitz_piece decomposing; dpf_rectifiable_bilipschitz_pieces rlcr-lean; no accepted existence theorem for tangent planes of Lipschitz images.`
- `python3 over dag.json: statuses and byte-identity of the six reused types; scan for dimred_cs_sp_* names`
- `grep -n '^theorem|^def' over SimonGMT Chapter03/*.lean; Chapter02/{AreaBranches,AreaNoninjective,AreaLipschitz,Area,AreaApproximation,AreaNormalization,Lipschitz}.lean; Chapter01/{DensityComparison,Densities,Hausdorff}.lean`
- `sed AreaBranches.lean 1–160, AreaLipschitz.lean 1–140, Area.lean 1–110, Rectifiable.lean 20–250, DensityComparison.lean 290–420, AffineCurrentPushforward.lean 35–90, Forms.lean 25–60, Mass.lean 25–75`
- `rg -i 'approximation theorem|c1_approx' in SimonGMT Chapter02 (no match: the C^1 Approximation Theorem of Simon Ch. 2, 1.5 is absent)`
- `grep in the Mathlib snapshot: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (MeasureTheory/Function/Jacobian.lean:255); NormDet.lean 290–440; Geometry/Euclidean/Volume/Measure.lean 125–200; Covering/DensityTheorem.lean 140–160; Determinant.lean (AlternatingMap.eq_smul_basis_det, Module.Basis.det_apply); Constructions/Polish/Basic.lean:821`
- `for f in Jacobian NormDet Volume/Measure DensityTheorem Determinant Alternating/Basic Polish/Basic FiniteDimension: cmp snapshot mathlib file vs .lake/packages/mathlib (all identical); rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem normDet_comp |theorem ae_tendsto_average_norm_sub|theorem AlternatingMap.eq_smul_basis_det|theorem MeasurableSet.image_of_continuousOn_injOn' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -i 'cauchy.binet' in the Mathlib snapshot (no match)`
- `python3 + git show <candidate_commit>:GMT/Ch07/Submission.lean for 419 accepted candidates: import headers. 407 use the contract header only; 5 add Poincare.SimonGMT.Chapter02.AreaLipschitz; 2 add Poincare.SimonGMT.Chapter01.DensityComparison.`
- `sed -n 1,200p book/chapter-03.txt; sed -n 755,880p book/chapter-06.txt; grep item line numbers in chapter-01/02/03/06`
- `lake env lean /tmp/sp-decomp-v2/Types.lean (12 child types)`
- `lake env lean /tmp/sp-decomp-v2/Assembly.lean (frozen parent type from the 12 child propositions; #print axioms)`
- `lake env lean /tmp/sp-decomp-v2/Api.lean and Api2.lean (#check of every library lemma cited by the new imrep_pushforward proof, under the contract imports plus AreaLipschitz and DensityComparison)`
- `lake env lean /tmp/sp-decomp-v2/Inst.lean (IsUnifLocDoublingMeasure instance for volume on Euclid m; affinePullbackForm unfolding; pp.coercions)`
- `grep -l dimred_cs_sp_ over nodes/, GMT/, SimonGMT and the Submission.lean files of the 3029 .swarm-worktrees`
- `independent adversarial review subagent on /tmp/sp-decomp-v2/imrep_proof.txt (verdict ACCEPT; four minor notes incorporated)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/sp-decomp-v2/Types.lean`
- `/tmp/sp-decomp-v2/Assembly.lean`
- `/tmp/sp-decomp-v2/Api.lean`
- `/tmp/sp-decomp-v2/Api2.lean`
- `/tmp/sp-decomp-v2/Inst.lean`
- `/tmp/sp-decomp-v2/imrep_proof.txt`

Pins and contract.
- The snapshot pins match: project b4d606d (= workspace HEAD), mathlib 25730c7c, simongmt 2b36630.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No reusable (TF) or quantitative partition in the DAG.
- dpf_approxTangent_ae_bilipschitz_piece is still decomposing.
- dpf_rectifiable_bilipschitz_pieces is in rlcr-lean.
- No accepted DAG node proves that approximate tangent planes exist along Lipschitz images.
- So (TF) and the quantitative partition are proved inside the imrep_pushforward proof (A5–A7) and cite no DAG declaration.

Pinned library support.
- The SimonGMT injective Lipschitz area formula: weighted_area_formula_lipschitz_injOn.
- The SimonGMT regular-set facts and the Lipschitz image bound.
- The upper density theorem: simon_remark_3_7_hausdorff, with its normalization lemmas.
- Mathlib's approximately linear partition (Jacobian.lean), normDet API, Lebesgue differentiation, Lusin–Souslin and alternating-map determinant lemmas.
- Every cited name elaborates once the two extra SimonGMT imports are added, and accepted submissions already add those imports.
- SimonGMT lacks the C^1 Approximation Theorem, so Simon's own route to (TF) is unavailable; the departure is stated in the proof.

Reused declarations. The six reused declarations remain accepted, with byte-identical types.

Lean checks.
- All 12 child types elaborate.
- The frozen parent type is proved from the 12 child propositions using only the standard axioms.
- No new name collides with anything in the DAG, the project or the swarm worktrees.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
