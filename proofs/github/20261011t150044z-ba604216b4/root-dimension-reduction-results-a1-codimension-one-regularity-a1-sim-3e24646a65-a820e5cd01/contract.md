<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.mollify-a1 -->

## Theorem `Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support`

Let m ∈ ℕ, let g : ℝ^m → ℝ be K-Lipschitz (K ≥ 0), let S ⊆ ℝ^m be compact with g = 0 outside S, and let δ > 0. Then there are C^∞ functions g_k : ℝ^m → ℝ (k ∈ ℕ) with the following properties: g_k(a) = 0 whenever a ∉ cthickening δ S (the closed δ-neighbourhood of S); g_k → g uniformly on ℝ^m; and ∫⁻ ofReal(‖Dg_k(a) − Dg(a)‖²) da → 0 (Lebesgue measure). Here D = fderiv ℝ, so Dg is the Rademacher derivative (0 where g is not differentiable), and ‖·‖ is the operator norm.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.mollify-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6001

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support`

```lean
∀ (m : ℕ) (g : Euclid m → ℝ) (K : NNReal) (S : Set (Euclid m)) (δ : ℝ), LipschitzWith K g → IsCompact S → (∀ a, a ∉ S → g a = 0) → 0 < δ → ∃ gs : ℕ → Euclid m → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k)) ∧ (∀ k a, a ∉ Metric.cthickening δ S → gs k a = 0) ∧ TendstoUniformly gs g atTop ∧ Tendsto (fun k => ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0)
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.mollify-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4 of the parent proof ("Mollification": g_{l,k} := g_l ∗ ϕ_{1/(k+k₀)} is C^∞, supported in a fixed compact neighbourhood of spt g_l, converges uniformly to g_l, and Dg_{l,k} = (Dg_l) ∗ ϕ → Dg_l in L²(ℝ^m) because a Lipschitz function is differentiable a.e. with the bounded gradient Dg_l (Rademacher) and this is its distributional gradient). Here the support margin is an arbitrary δ > 0 and the identity D(g ∗ ϕ) = (Dg) ∗ ϕ is proved directly by dominated convergence of difference quotients. No sibling child is needed. Notation: F := Dg = fderiv ℝ g (defined everywhere; 0 where g is not differentiable), ‖·‖ the operator norm, L^m = volume on ℝ^m = Euclid m, B_s(y) / B̄_s(y) open / closed balls, T := cthickening δ S.

1. (Properties of F.) F is Borel measurable (measurable_fderiv) and ‖F(y)‖ ≤ K for all y (norm_fderiv_le_of_lipschitz). S is compact, hence closed, and g = 0 on the open set ℝ^m \ S, so F(y) = 0 for y ∉ S. Hence F is bounded, Borel, vanishes off the compact S, and is integrable and locally integrable. By Rademacher's theorem (LipschitzWith.ae_differentiableAt) g is differentiable at L^m-a.e. point.
2. (Mollifiers.) For k ∈ ℕ put ε_k := δ/(k+2); then 0 < ε_k < δ and ε_k → 0. Let φ_k be a smooth bump function centred at 0 with inner radius ε_k/2 and outer radius ε_k (ContDiffBump (0 : Euclid m), available for Euclid m): φ_k is C^∞ with compact support, 0 ≤ φ_k ≤ 1, φ_k = 1 on B̄_{ε_k/2}(0) and support φ_k = B_{ε_k}(0). Put I_k := ∫φ_k. Since φ_k ≥ 1_{B̄_{ε_k/2}(0)}, I_k ≥ L^m(B̄_{ε_k/2}(0)) > 0. Let ρ_k := I_k⁻¹φ_k. Then ρ_k is C^∞ with compact support, ρ_k ≥ 0, ∫ρ_k = 1, support ρ_k ⊆ B_{ε_k}(0), and for every y ∈ ℝ^m: ρ_k ≤ I_k⁻¹ ≤ 1/L^m(B̄_{ε_k/2}(0)) = 2^m/L^m(B̄_{ε_k}(y)), because L^m(B̄_s(y)) = s^m·L^m(B_1(0)) for s ≥ 0 (Measure.addHaar_closedBall; for m = 0 both sides equal 1).
 (Mathlib's normalized bump ContDiffBump.normed and the lemma ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable are not in the import closure of GMT.Ch07.Submission; steps 2 and 6 reproduce them.)
3. (The approximants.) g_k := ρ_k ⋆ g, i.e. g_k(a) = ∫ ρ_k(t) g(a − t) dt (convolution with lsmul ℝ ℝ and volume; convolution_def). g is continuous, hence locally integrable, and ρ_k is C^∞ with compact support, so g_k is C^∞ (HasCompactSupport.contDiff_convolution_left).
4. (Support.) Let a ∉ T. If ρ_k(t) ≠ 0 then |t| < ε_k < δ; if a − t were in S then dist(a, a − t) = |t| ≤ δ would give a ∈ cthickening δ S = T; hence a − t ∉ S and g(a − t) = 0. So the integrand ρ_k(t)g(a − t) vanishes for every t and g_k(a) = 0.
5. (Uniform convergence.) For every a, if y ∈ B_{ε_k}(a) then |g(y) − g(a)| ≤ K|y − a| ≤ Kε_k. Since ρ_k ≥ 0, ∫ρ_k = 1 and support ρ_k ⊆ B_{ε_k}(0), |g_k(a) − g(a)| ≤ Kε_k (dist_convolution_le). As Kε_k → 0 uniformly in a, g_k → g uniformly on ℝ^m.
6. (Derivative of the approximants.) Claim: Dg_k(a) = ∫ ρ_k(t) F(a − t) dt for all k and a (Bochner integral in L(ℝ^m, ℝ); the integrand is a.e.-strongly measurable and bounded by Kρ_k, hence integrable). Fix a and v ∈ ℝ^m and let s_n := 1/(n+1) → 0, s_n ≠ 0.
 (i) g_k is differentiable at a, so the difference quotients q_n := s_n⁻¹(g_k(a + s_nv) − g_k(a)) converge to Dg_k(a)v (hasDerivAt_iff_tendsto_slope_zero along the line s ↦ a + sv).
 (ii) By linearity of the integral, q_n = ∫ ρ_k(t)·s_n⁻¹(g(a − t + s_nv) − g(a − t)) dt.
 (iii) The map t ↦ a − t preserves L^m (Measure.measurePreserving_sub_left), so by step 1, for a.e. t, g is differentiable at a − t and then s_n⁻¹(g(a − t + s_nv) − g(a − t)) → F(a − t)v. The integrands are continuous in t and bounded by ρ_k(t)K|v|, an integrable function. By dominated convergence (tendsto_integral_of_dominated_convergence), q_n → ∫ ρ_k(t)F(a − t)v dt.
 (iv) By uniqueness of limits, Dg_k(a)v = ∫ ρ_k(t)F(a − t)v dt = (∫ ρ_k(t)F(a − t) dt)v (ContinuousLinearMap.integral_apply). As v is arbitrary, the claim follows.
 Consequences: ‖Dg_k(a)‖ ≤ ∫ρ_k(t)K dt = K (norm_integral_le_of_norm_le); and Dg_k(a) = 0 for a ∉ T, since g_k = 0 on the open set ℝ^m \ T (step 4; T is closed).
7. (Pointwise convergence at Lebesgue points.) By the Lebesgue differentiation theorem for the Besicovitch Vitali family of L^m (VitaliFamily.ae_tendsto_average_norm_sub with Besicovitch.vitaliFamily; F is locally integrable), for a.e. a the averages ⨍_{B̄_s(a)} ‖F(y) − F(a)‖ dy tend to 0 as s → 0⁺ (Besicovitch.tendsto_filterAt), in particular along s = ε_k. Fix such a. Substituting y = a − t (integral_sub_left_eq_self), Dg_k(a) = ∫ ρ_k(a − y)F(y) dy. The kernels y ↦ ρ_k(a − y) have integral 1, support in B_{ε_k}(a) ⊆ B̄_{ε_k}(a), and absolute value at most 2^m/L^m(B̄_{ε_k}(a)) (step 2); F is integrable on each closed ball. Hence Dg_k(a) → F(a) (tendsto_integral_smul_of_tendsto_average_norm_sub with constant 2^m).
8. (L² convergence.) The functions h_k(a) := ofReal(‖Dg_k(a) − F(a)‖²) are Borel (measurable_fderiv for g_k and g). They satisfy h_k ≤ ofReal((2K)²)·1_T everywhere: on T by ‖Dg_k(a)‖ ≤ K and ‖F(a)‖ ≤ K, and off T both derivatives vanish (steps 1 and 6; S ⊆ T). The bound has finite integral ofReal((2K)²)·L^m(T) (T compact). By step 7, h_k → 0 a.e. By dominated convergence for lower integrals (tendsto_lintegral_of_dominated_convergence), ∫ ofReal(‖Dg_k − Dg‖²) dL^m → ∫ 0 = 0.
9. Steps 3, 4, 5 and 8 give the functions g_k with all asserted properties. ∎

Implementation notes (checked in the import closure of GMT.Ch07.Submission, Mathlib 25730c7c): available are ContDiffBump with one_of_mem_closedBall, le_one, nonneg, support_eq, hasCompactSupport, contDiff, continuous and the instance HasContDiffBump (Euclid m); HasCompactSupport.contDiff_convolution_left; convolution_def; dist_convolution_le; Measure.addHaar_closedBall; LipschitzWith.ae_differentiableAt; measurable_fderiv; norm_fderiv_le_of_lipschitz; Measure.measurePreserving_sub_left; Measure.QuasiMeasurePreserving.ae; tendsto_integral_of_dominated_convergence; hasDerivAt_iff_tendsto_slope_zero; ContinuousLinearMap.integral_apply; integral_sub_left_eq_self; VitaliFamily.ae_tendsto_average_norm_sub; Besicovitch.vitaliFamily (instances HasBesicovitchCovering (Euclid m), SFinite volume); Besicovitch.tendsto_filterAt; tendsto_integral_smul_of_tendsto_average_norm_sub; tendsto_lintegral_of_dominated_convergence; norm_integral_le_of_norm_le. Not available: ContDiffBump.normed, ContDiffBump.integral_pos, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable.

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support : <exactly the frozen lean_statement> := by`, after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c (only deprecation warnings); #print axioms: propext, Classical.choice, Quot.sound.
```lean
  intro m g K S δ hg hS hg0 hδ
  classical
  -- the a.e. derivative `F = Dg`
  set F : Euclid m → (Euclid m →L[ℝ] ℝ) := fderiv ℝ g with hFdef
  have hFm : Measurable F := measurable_fderiv ℝ g
  have hFb : ∀ y, ‖F y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hg
  have hF0 : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    have h : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hy] with z hz using hg0 z hz
    rw [hFdef, h.fderiv_eq]; simp
  have hFint : Integrable F := by
    refine Integrable.mono' (g := S.indicator fun _ => (K : ℝ)) ?_ hFm.aestronglyMeasurable ?_
    · exact (integrable_indicator_iff hS.isClosed.measurableSet).2
        (integrableOn_const hS.measure_lt_top.ne)
    · filter_upwards with y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]; exact hFb y
      · rw [indicator_of_notMem hy, hF0 y hy, norm_zero]
  -- radii
  set ε : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hεδ : ∀ k, ε k < δ := fun k => by
    simp only [hεdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ)).div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [hεdef] using h
  -- normalized bumps
  let φ : ℕ → ContDiffBump (0 : Euclid m) := fun k =>
    ⟨ε k / 2, ε k, by linarith [hε k], by linarith [hε k]⟩
  set I : ℕ → ℝ := fun k => ∫ x, (φ k) x with hIdef
  have hφint : ∀ k, Integrable (fun x => (φ k) x) := fun k =>
    (φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport
  -- the volume of balls
  have hvol : ∀ (y : Euclid m) (s : ℝ), 0 ≤ s →
      volume.real (closedBall y s) = s ^ m * volume.real (ball (0 : Euclid m) 1) := by
    intro y s hs
    rw [measureReal_def, Measure.addHaar_closedBall volume y hs, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hc : 0 < volume.real (ball (0 : Euclid m) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hI : ∀ k, volume.real (closedBall (0 : Euclid m) (ε k / 2)) ≤ I k := by
    intro k
    have hle : (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) ≤
        fun x => (φ k) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : Euclid m) (ε k / 2)
      · rw [indicator_of_mem hx]; exact ((φ k).one_of_mem_closedBall hx).ge
      · rw [indicator_of_notMem hx]; exact (φ k).nonneg
    have hint1 : Integrable ((closedBall (0 : Euclid m) (ε k / 2)).indicator fun _ => (1 : ℝ)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc volume.real (closedBall (0 : Euclid m) (ε k / 2))
        = ∫ x, (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) x := by
          rw [integral_indicator measurableSet_closedBall]; simp
      _ ≤ I k := integral_mono hint1 (hφint k) hle
  have hIpos : ∀ k, 0 < I k := fun k =>
    lt_of_lt_of_le (by rw [hvol 0 _ (by linarith [hε k])]; exact mul_pos (pow_pos (by linarith [hε k]) _) hc)
      (hI k)
  set ρ : ℕ → Euclid m → ℝ := fun k x => (I k)⁻¹ * (φ k) x with hρdef
  have hρ0 : ∀ k x, 0 ≤ ρ k x := fun k x => mul_nonneg (inv_nonneg.2 (hIpos k).le) (φ k).nonneg
  have hρint1 : ∀ k, ∫ x, ρ k x = 1 := fun k => by
    have hIk : ∫ x, (φ k) x = I k := rfl
    simp only [hρdef]; rw [integral_const_mul, hIk, inv_mul_cancel₀ (hIpos k).ne']
  have hρsupp : ∀ k, Function.support (ρ k) ⊆ ball 0 (ε k) := fun k =>
    (Function.support_mul_subset_right _ _).trans (φ k).support_eq.subset
  have hρsmooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => contDiff_const.mul (φ k).contDiff
  have hρcs : ∀ k, HasCompactSupport (ρ k) := fun k => (φ k).hasCompactSupport.mul_left
  have hρcont : ∀ k, Continuous (ρ k) := fun k => continuous_const.mul (φ k).continuous
  have hρintg : ∀ k, Integrable (ρ k) := fun k => (hρcont k).integrable_of_hasCompactSupport (hρcs k)
  have hρle : ∀ k x (y : Euclid m), ρ k x ≤ 2 ^ m / volume.real (closedBall y (ε k)) := by
    intro k x y
    have h1 : ρ k x ≤ (I k)⁻¹ := by
      simp only [hρdef]
      calc (I k)⁻¹ * (φ k) x ≤ (I k)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ k).le_one (inv_nonneg.2 (hIpos k).le)
        _ = (I k)⁻¹ := mul_one _
    have hpos2 : 0 < (ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1) :=
      mul_pos (pow_pos (by linarith [hε k]) _) hc
    have h2 : (I k)⁻¹ ≤ ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ := by
      rw [← hvol 0 _ (by linarith [hε k])]
      exact inv_anti₀ (by rw [hvol 0 _ (by linarith [hε k])]; exact hpos2) (hI k)
    have h3 : ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ =
        2 ^ m / volume.real (closedBall y (ε k)) := by
      rw [hvol y _ (hε k).le, div_pow]
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  -- the approximants
  set gs : ℕ → Euclid m → ℝ := fun k => convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hgsdef
  have hgs_apply : ∀ k a, gs k a = ∫ t, ρ k t * g (a - t) := by
    intro k a
    simp only [hgsdef, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hgs_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k) := fun k =>
    (hρcs k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρsmooth k)
      hg.continuous.locallyIntegrable
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hgs_supp : ∀ k a, a ∉ T → gs k a = 0 := by
    intro k a ha
    rw [hgs_apply]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : ρ k t = 0
    · simp [ht]
    · have htb : t ∈ ball (0 : Euclid m) (ε k) := hρsupp k ht
      rw [mem_ball_zero_iff] at htb
      have hS' : a - t ∉ S := by
        intro hmem
        exact ha (Metric.mem_cthickening_of_dist_le a (a - t) δ S hmem
          (by rw [dist_eq_norm, sub_sub_cancel]; linarith [hεδ k]))
      simp [hg0 _ hS']
  refine ⟨gs, hgs_smooth, hgs_supp, ?_, ?_⟩
  · -- uniform convergence
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hK : Tendsto (fun k => (K : ℝ) * ε k) atTop (𝓝 0) := by
      simpa using hεlim.const_mul (K : ℝ)
    filter_upwards [hK.eventually (gt_mem_nhds he)] with k hk a
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ hk
    refine dist_convolution_le (by positivity) (hρsupp k) (hρ0 k) (hρint1 k)
      hg.continuous.aestronglyMeasurable fun x hx => ?_
    calc dist (g x) (g a) ≤ K * dist x a := hg.dist_le_mul x a
      _ ≤ K * ε k := by gcongr; exact (mem_ball.1 hx).le
  · -- the derivative of `gs k` is the mollification of `F`
    have hFae : ∀ a : Euclid m, ∀ᵐ t ∂(volume : Measure (Euclid m)), DifferentiableAt ℝ g (a - t) :=
      fun a => (Measure.measurePreserving_sub_left volume a).quasiMeasurePreserving.ae
        hg.ae_differentiableAt
    have hsl : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall
        fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff]; positivity
    have hderiv : ∀ k a, fderiv ℝ (gs k) a = ∫ t, ρ k t • F (a - t) := by
      intro k a
      have hint : Integrable (fun t => ρ k t • F (a - t)) := by
        refine Integrable.mono' ((hρintg k).mul_const (K : ℝ)) ?_ (Eventually.of_forall fun t => ?_)
        · exact (hρcont k).aestronglyMeasurable.smul
            (hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        · rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
          exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
      ext v
      rw [ContinuousLinearMap.integral_apply hint]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
      have hspos : ∀ n, 0 < s n := fun n => by positivity
      -- difference quotients of `gs k` along `v`
      have hline : HasDerivAt (fun r : ℝ => gs k (a + r • v)) (fderiv ℝ (gs k) a v) 0 := by
        have h1 : HasDerivAt (fun r : ℝ => a + r • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
        have h2 : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) (a + (0 : ℝ) • v) := by
          rw [zero_smul, add_zero]
          exact ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
        exact h2.comp_hasDerivAt (0 : ℝ) h1
      have hq1 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (fderiv ℝ (gs k) a v)) := by
        have := (hasDerivAt_iff_tendsto_slope_zero.1 hline).comp hsl
        simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      have hgint : ∀ w : Euclid m, Integrable (fun t => ρ k t * g (w - t)) := fun w =>
        ((hρcont k).mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((hρcs k).mul_right)
      have hrepr : ∀ n, (s n)⁻¹ * (gs k (a + s n • v) - gs k a) =
          ∫ t, ρ k t * ((s n)⁻¹ * (g (a - t + s n • v) - g (a - t))) := by
        intro n
        rw [hgs_apply, hgs_apply, ← integral_sub (hgint _) (hgint _), ← integral_const_mul]
        congr 1
        ext t
        rw [show a + s n • v - t = a - t + s n • v by abel]
        ring
      have hq2 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (∫ t, ρ k t * F (a - t) v)) := by
        simp_rw [hrepr]
        refine tendsto_integral_of_dominated_convergence (fun t => ρ k t * (K * ‖v‖)) (fun n => ?_)
          ((hρintg k).mul_const _) (fun n => Eventually.of_forall fun t => ?_) ?_
        · exact ((hρcont k).mul (continuous_const.mul ((hg.continuous.comp
            ((continuous_const.sub continuous_id).add continuous_const)).sub
            (hg.continuous.comp (continuous_const.sub continuous_id))))).aestronglyMeasurable
        · rw [norm_mul, Real.norm_of_nonneg (hρ0 k t)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ0 k t)
          have hL := hg.dist_le_mul (a - t + s n • v) (a - t)
          rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (hspos n).le] at hL
          rw [norm_mul, norm_inv, Real.norm_of_nonneg (hspos n).le, Real.norm_eq_abs]
          calc (s n)⁻¹ * |g (a - t + s n • v) - g (a - t)|
              ≤ (s n)⁻¹ * (K * (s n * ‖v‖)) := by gcongr; exact hL
            _ = K * ‖v‖ := by
                rw [show (s n)⁻¹ * (K * (s n * ‖v‖)) = (s n)⁻¹ * s n * (K * ‖v‖) by ring,
                  inv_mul_cancel₀ (hspos n).ne', one_mul]
        · filter_upwards [hFae a] with t ht
          refine Tendsto.const_mul _ ?_
          have hl : HasDerivAt (fun r : ℝ => g (a - t + r • v)) (F (a - t) v) 0 := by
            have h1 : HasDerivAt (fun r : ℝ => a - t + r • v) v 0 := by
              simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (a - t)
            have h2 : HasFDerivAt g (F (a - t)) (a - t + (0 : ℝ) • v) := by
              rw [zero_smul, add_zero]; exact ht.hasFDerivAt
            exact h2.comp_hasDerivAt (0 : ℝ) h1
          have := (hasDerivAt_iff_tendsto_slope_zero.1 hl).comp hsl
          simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      exact tendsto_nhds_unique hq1 hq2
    -- bounds and support of the derivatives
    have hDgsb : ∀ k a, ‖fderiv ℝ (gs k) a‖ ≤ K := by
      intro k a
      rw [hderiv k a]
      calc ‖∫ t, ρ k t • F (a - t)‖ ≤ ∫ t, ρ k t * K := by
            refine norm_integral_le_of_norm_le ((hρintg k).mul_const _) (Eventually.of_forall fun t => ?_)
            rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
            exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
        _ = K := by rw [integral_mul_const, hρint1 k, one_mul]
    have hDgs0 : ∀ k a, a ∉ T → fderiv ℝ (gs k) a = 0 := by
      intro k a ha
      have h : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds ha] with b hb
        exact hgs_supp k b hb
      rw [h.fderiv_eq]; simp
    -- Lebesgue points: `D gs k → F` a.e.
    have hεlim' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall hε⟩
    have hae : ∀ᵐ a ∂(volume : Measure (Euclid m)), Tendsto (fun k => fderiv ℝ (gs k) a) atTop (𝓝 (F a)) := by
      filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Euclid m))).ae_tendsto_average_norm_sub
        hFint.locallyIntegrable] with a ha
      have havg : Tendsto (fun k => ⨍ y in closedBall a (ε k), ‖F y - F a‖) atTop (𝓝 0) :=
        ha.comp ((Besicovitch.tendsto_filterAt volume a).comp hεlim')
      have hconv := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
        (g := fun k y => ρ k (a - y)) (2 ^ m) havg
        (Eventually.of_forall fun k => hFint.integrableOn)
        (tendsto_const_nhds.congr' (Eventually.of_forall fun k => by
          simp only
          rw [integral_sub_left_eq_self (fun y => ρ k y) volume a, hρint1 k]))
        (Eventually.of_forall fun k y hy => by
          have h := hρsupp k hy
          rw [mem_ball_zero_iff] at h
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact h.le)
        (Eventually.of_forall fun k y => by
          rw [abs_of_nonneg (hρ0 k _)]; exact hρle k _ a)
      refine hconv.congr' (Eventually.of_forall fun k => ?_)
      show _ = fderiv ℝ (gs k) a
      rw [hderiv k a]
      have := integral_sub_left_eq_self (fun t => ρ k t • F (a - t)) volume a
      simp only [sub_sub_cancel] at this
      exact this
    -- dominated convergence in `L²`
    have hTc : IsCompact T := hS.cthickening
    have hkey := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun k a => ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2)) (f := fun _ => 0)
      (T.indicator fun _ => ENNReal.ofReal ((2 * K) ^ 2))
      (fun k => (((measurable_fderiv ℝ (gs k)).sub hFm).norm.pow_const 2).ennreal_ofReal)
      (fun k => Eventually.of_forall fun a => by
        by_cases ha : a ∈ T
        · rw [indicator_of_mem ha]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖fderiv ℝ (gs k) a - F a‖ ≤ 2 * K :=
            (norm_sub_le _ _).trans (by linarith [hDgsb k a, hFb a])
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        · have haS : a ∉ S := fun h => ha (Metric.self_subset_cthickening S h)
          rw [indicator_of_notMem ha]
          show ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2) ≤ 0
          rw [hDgs0 k a ha, hF0 a haS, sub_zero, norm_zero]
          simp)
      (by
        rw [lintegral_indicator_const hTc.isClosed.measurableSet]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTc.measure_lt_top.ne)
      (by
        filter_upwards [hae] with a ha
        have h1 : Tendsto (fun k => ‖fderiv ℝ (gs k) a - F a‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 ha
        have h2 := ENNReal.tendsto_ofReal (h1.pow 2)
        simpa using h2)
    simpa using hkey
```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. Normalized bumps ρ_k are supported in B_{ε_k}(0), with ε_k = δ/(k+2) → 0 and ρ_k ≤ 2^m/L^m(B̄_{ε_k}). The convolution g_k := ρ_k ⋆ g is C^∞.
2. g_k = 0 off cthickening δ S, and |g_k − g| ≤ Kε_k.
3. Dg_k(a) = ∫ρ_k(t)Dg(a − t)dt, by dominated convergence of difference quotients (Rademacher a.e.).
4. Lebesgue differentiation (Besicovitch) gives Dg_k → Dg a.e. Domination by (2K)²·1_{cthickening δ S} then gives the L² convergence.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE usage)`
- `python3 scans of dag.json: selected node (depth 5, max_depth 6), parent hypercone_plane and its decomposition-v1.json, accepted nodes whose statements mention Lipschitz/mollif/convol/graph chart/starProjection/tangentSpace, lean_name collision scan for codim1_hcp_lsa_*`
- `runtime.py: _decompose (max_depth), _existing_lean_name_problem (reuse of accepted declarations by identical name and type)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 93f7ea7a3650 (codim1_rdo_gc_local_inverse_c2, dsmc_chart_inverse_continuity), d25d2377 (codim1_zsl_pc_mollify_indicator_l1), and the handoffs of codim1_zsl_gc_local_inverse and dsmc_chart_inverse_continuity`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt, measurable_fderiv, tangentConeAt, HasFDerivWithinAt.unique_on, mem_tangentConeAt_of_seq, hasFDerivAt_convolution_left, contDiff_convolution_left, ae_convolution_tendsto_right_of_locallyIntegrable, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, LocallyLipschitzOn.mul, exists_isSubordinate, exists_contDiff_support_eq_eq_one_iff, sq_sum_le_card_mul_sum_sq, measurePreserving_sub_left`
- `lean #check probes in the GMT.Ch07.Submission import closure (Imp*.lean, Inst5.lean): SmoothPartitionOfUnity.exists_isSubordinate, ContDiffBump API, ContDiffBump.normed (missing), VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, tendsto_integral_smul_of_tendsto_average_norm_sub, aestronglyMeasurable_iUnion_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, NormedRing.inverse_continuousAt, instances HasContDiffBump/HasBesicovitchCovering (Euclid m)`
- `lean -DautoImplicit=false /tmp/lsa-split/check/{TypesAll,Assembly,N1,N2,N3,N4,N5,N6,N7,N8,Integration}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `git for-each-ref | xargs git grep -l codim1_hcp_lsa -- 'GMT/*.lean' (no match); grep codim1_hcp_lsa dag.json (0); grep -rn codim1_hcp_lsa simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/tmp/lsa-split/check/TypesAll.lean`
- `/tmp/lsa-split/check/Assembly.lean`
- `/tmp/lsa-split/check/Integration.lean`

Pins match: manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). The node has depth 5 with max_depth 6, so the children are leaves. Reuse: four accepted declarations (chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_zsl_gc_local_inverse, dsmc_chart_inverse_continuity) are taken with byte-identical frozen types. The C² graph-chart and tangent-projection lemmas (codim1_rdo_gc_graph_over_tangent, submanifold_tangentProjection_c1_extension, dor_lmb_ret_tangent_projection) do not apply to C¹ M. No C¹ graph chart, Rademacher-on-M, tangent-projection continuity or L²-gradient mollification lemma exists in the DAG, SimonGMT or the snapshot, and the 8 codim1_hcp_lsa_ names are unused everywhere. Mathlib in the Submission import closure provides Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), measurable_fderiv, HasFDerivWithinAt.unique_on with mem_tangentConeAt_of_seq, LipschitzOnWith.hausdorffMeasure_image_le with EuclideanSpace.euclideanHausdorffMeasure_eq_volume, convolution smoothness, ContDiffBump, Besicovitch Lebesgue differentiation, SmoothPartitionOfUnity and exists_contDiff_support_eq_eq_one_iff. It lacks ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and sq_sum_le_card_mul_sum_sq; the mollify proof rebuilds the first two by hand, and the assembly uses Finset.sum_mul_sq_le_sq_mul_sq. Lean: all 12 child types elaborate. The selected type is kernel-checked from the child types as axioms. Every new child is proved from exactly its declared siblings. The integrated file (8 proofs plus assembly, only the 4 reused declarations as axioms) compiles without errors or sorry.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
