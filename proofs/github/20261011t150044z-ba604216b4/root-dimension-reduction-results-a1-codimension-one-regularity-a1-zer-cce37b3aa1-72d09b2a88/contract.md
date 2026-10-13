<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.graph_integral_limit-a1 -->

## Theorem `Submission.codim1_zsl_fl_graph_integral_tendsto`

Let m, k, P ∈ ℕ, let ι : ℝ^m → ℝ^P and ι' : ℝ^k → ℝ^P be linear isometries (ℝ^d = Euclid d), b ∈ ℝ^k, R ∈ ℝ, B := ball(0, R) ⊆ ℝ^m, and let β : ℝ^P → Λ^m(ℝ^P) (Covector (Euclid P) m) be continuous with compact support. Let g_i : ℝ^m → ℝ^k (i ∈ ℕ) and let A_i, A ⊆ ℝ^m be measurable sets. Assume (a) L^m((A_i Δ A) ∩ B) → 0 (L^m = Lebesgue measure, Δ = symmetric difference); (b) for all large i, g_i is differentiable at every w ∈ B; (c) for every ε > 0, for all large i, |g_i(w) − b| < ε and ‖Dg_i(w)‖ < ε for all w ∈ B. Put G_i(w) := ιw + ι'g_i(w), DG_i(w) := fderiv ℝ G_i w and e_j := EuclideanSpace.single j 1. Then ∫_{A_i∩B} β(G_i(w))(DG_i(w)e_0, …, DG_i(w)e_{m−1}) dw → ∫_{A∩B} β(ιw + ι'b)(ιe_0, …, ιe_{m−1}) dw as i → ∞ (Bochner integrals with respect to Lebesgue measure on ℝ^m).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.graph_integral_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5038

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_zsl_fl_graph_integral_tendsto`

```lean
∀ (m k P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (b : Euclid k) (R : ℝ) (β : Euclid P → Covector (Euclid P) m) (gs : ℕ → Euclid m → Euclid k) (As : ℕ → Set (Euclid m)) (A : Set (Euclid m)), Continuous β → HasCompactSupport β → (∀ i, MeasurableSet (As i)) → MeasurableSet A → Tendsto (fun i => volume (symmDiff (As i) A ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) → (∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (gs i) w) → (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → Tendsto (fun i => ∫ w in As i ∩ ball 0 R, β (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) atTop (𝓝 (∫ w in A ∩ ball 0 R, β (ι w + ι' b) (fun j => ι (EuclideanSpace.single j (1 : ℝ)))))
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.graph_integral_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps D1–D4 of the supplied proof of the parent node codim1_zsl_flat_graph_limit (uniform convergence of the integrands from the C¹ convergence g_i → b, and convergence of the integrals from the L¹_loc convergence of the indicators supplied by BV compactness; Simon 7.5.3, chapter-07.txt lines 848–852, "converges in L¹_loc", and 7.5.5, lines 862–901), stated for an arbitrary continuous compactly supported field of m-covectors β in place of dω and for arbitrary dimensions m, k, P. Departure: the uniform continuity argument of D2 is made explicit through the multilinear difference bound ContinuousAlternatingMap.norm_image_sub_le and an ε-argument; no orthogonality of ι and ι' is needed.
Notation. h_i(w) := β(G_i(w))(DG_i(w)e_0, …, DG_i(w)e_{m−1}) and h(w) := β(ιw + ι'b)(ιe_0, …, ιe_{m−1}); L := L^m; |·| Euclidean and operator norms; for u : Fin m → ℝ^P, ‖u‖ := max_j |u_j| (the sup norm, pi_norm_le_iff_of_nonneg).
1. Constants. β is continuous with compact support, hence bounded, |β(y)| ≤ M for all y with some M ≥ 0 (Continuous.bounded_above_of_compact_support), and uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). B is measurable with L(B) < ∞ (measure_ball_lt_top). |e_j| = 1 and |ιe_j| = 1.
2. The limit integrand. |h(w)| ≤ |β(ιw + ι'b)|·∏_j |ιe_j| ≤ M (ContinuousAlternatingMap.le_opNorm), and h is continuous (w ↦ β(ιw + ι'b) is continuous and evaluation at the fixed family ιe is continuous, continuous_eval_const). Hence h is integrable on every set of finite measure (IntegrableOn.of_bound).
3. Derivative of G_i. If g_i is differentiable at w, then DG_i(w) = ι + ι'∘Dg_i(w) (derivative of the linear map ι plus chain rule for ι'∘g_i: HasFDerivAt.add, HasFDerivAt.comp), so DG_i(w)e_j = ιe_j + ι'(Dg_i(w)e_j).
4. Pointwise estimate. Let g_i be differentiable at w with ‖Dg_i(w)‖ ≤ 1; write T := Dg_i(w), y := G_i(w), y' := ιw + ι'b, u_j := DG_i(w)e_j, u'_j := ιe_j. Then |u_j| ≤ |ιe_j| + |ι'(Te_j)| ≤ 1 + ‖T‖ ≤ 2, |u'_j| = 1 and |u_j − u'_j| = |ι'(Te_j)| ≤ ‖T‖; so ‖u‖ ≤ 2, ‖u'‖ ≤ 1 and ‖u − u'‖ ≤ ‖T‖. Split h_i(w) − h(w) = [β(y)(u) − β(y')(u)] + [β(y')(u) − β(y')(u')]. The first bracket equals (β(y) − β(y'))(u) and is at most |β(y) − β(y')|·∏_j|u_j| ≤ 2^m·|β(y) − β(y')| in absolute value (le_opNorm). The second is at most |β(y')|·m·max(‖u‖, ‖u'‖)^{m−1}·‖u − u'‖ ≤ M·m·2^m·‖T‖ (ContinuousAlternatingMap.norm_image_sub_le, 2^{m−1} ≤ 2^m). Hence |h_i(w) − h(w)| ≤ 2^m·|β(G_i(w)) − β(ιw + ι'b)| + M·m·2^m·‖Dg_i(w)‖.
5. Uniform convergence on B. Let ε > 0. By uniform continuity choose δ > 0 with |β(y) − β(y')| < ε/(2·2^m) whenever |y − y'| < δ. Put X := M·m·2^m ≥ 0 and η := min(1, ε/(2(X + 1))) > 0. By (b) and by (c) with δ and with η, for all large i and all w ∈ B: g_i is differentiable at w, |G_i(w) − (ιw + ι'b)| = |ι'(g_i(w) − b)| = |g_i(w) − b| < δ, and ‖Dg_i(w)‖ < η ≤ 1. By step 4, |h_i(w) − h(w)| ≤ 2^m·ε/(2·2^m) + X·ε/(2(X + 1)) ≤ ε/2 + ε/2 = ε. Thus for every ε > 0, for all large i, |h_i − h| ≤ ε on B.
6. Measurability. For every i such that g_i is differentiable on B, h_i is a.e.-strongly measurable with respect to L restricted to B: G_i is continuous at each point of B, hence continuous on B and a.e.-strongly measurable for L⌞B (ContinuousOn.aestronglyMeasurable, B measurable); w ↦ DG_i(w) is measurable for an arbitrary map (measurable_fderiv), hence a.e.-strongly measurable (finite-dimensional target); and h_i(w) = Φ(G_i(w), DG_i(w)) with Φ(y, T) := β(y)(Te_0, …, Te_{m−1}), which is continuous on ℝ^P × L(ℝ^m, ℝ^P) (continuity of β and of T ↦ Te_j, and joint continuity of evaluation, continuous_eval). A continuous function of an a.e.-strongly measurable map is a.e.-strongly measurable. By (b) this holds for all large i.
7. Symmetric differences in ℝ. L((A_i Δ A) ∩ B) → 0 in [0, ∞] by (a), and toReal is continuous at 0 (ENNReal.tendsto_toReal), so the real numbers L((A_i Δ A) ∩ B) tend to 0.
8. Final estimate. Let ε > 0 and V := L(B) ∈ [0, ∞) (as a real number). By steps 5–7, for all large i simultaneously: |h_i − h| ≤ ε/(2(V + 1)) on B, |h_i − h| ≤ 1 on B, h_i is a.e.-strongly measurable for L⌞B, and L((A_i Δ A) ∩ B) < ε/(4(M + 1)). Fix such i and put s := A_i ∩ B, t := A ∩ B (measurable, of finite measure). h_i is integrable on s (a.e.-strongly measurable for L⌞s since s ⊆ B, and |h_i| ≤ |h_i − h| + |h| ≤ 1 + M on s; IntegrableOn.of_bound), and h is integrable on s and on t (step 2). (a) |∫_s h_i − ∫_s h| = |∫_s (h_i − h)| ≤ ε/(2(V + 1))·L(s) ≤ ε/(2(V + 1))·V < ε/2 (integral_sub, norm_setIntegral_le_of_norm_le_const, L(s) ≤ L(B)). (b) ∫_s h = ∫_{s∩t} h + ∫_{s∖t} h and ∫_t h = ∫_{t∩s} h + ∫_{t∖s} h (integral_inter_add_sdiff), so ∫_s h − ∫_t h = ∫_{s∖t} h − ∫_{t∖s} h. A point of s ∖ t lies in B and in A_i but not in A, and a point of t ∖ s lies in B and in A but not in A_i; so both sets lie in (A_i Δ A) ∩ B, and |∫_s h − ∫_t h| ≤ M·L(s∖t) + M·L(t∖s) ≤ 2M·L((A_i Δ A) ∩ B) ≤ 2(M + 1)·ε/(4(M + 1)) = ε/2. Hence |∫_{A_i∩B} h_i − ∫_{A∩B} h| < ε for all large i. As ε > 0 was arbitrary, the integrals converge (Metric.tendsto_nhds). ∎
Formalization note: unless this child is split further it is a machine leaf (one theorem appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declaration, no import, no set_option). The tactic proof below was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context: the frozen Submission.lean, under default maxHeartbeats. It passes the workflow's leaf source-delta check (leaf_verification.check_source_delta), its frozen type passes lean_contract.validate_lean_statement and elaborates in the comparator's replayed contract scope, and #print axioms gives only propext, Classical.choice, Quot.sound. It may be used verbatim:
theorem Submission.codim1_zsl_fl_graph_integral_tendsto : ∀ (m k P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (b : Euclid k) (R : ℝ) (β : Euclid P → Covector (Euclid P) m) (gs : ℕ → Euclid m → Euclid k) (As : ℕ → Set (Euclid m)) (A : Set (Euclid m)), Continuous β → HasCompactSupport β → (∀ i, MeasurableSet (As i)) → MeasurableSet A → Tendsto (fun i => volume (symmDiff (As i) A ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) → (∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (gs i) w) → (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → Tendsto (fun i => ∫ w in As i ∩ ball 0 R, β (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) atTop (𝓝 (∫ w in A ∩ ball 0 R, β (ι w + ι' b) (fun j => ι (EuclideanSpace.single j (1 : ℝ))))) := by
  intro m k P ι ι' b R β gs As A hβc hβs hAs hA hsymm hH1 hH2
  classical
  set B : Set (Euclid m) := ball (0 : Euclid m) R with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hBfin : volume B < ⊤ := measure_ball_lt_top
  obtain ⟨M, hM⟩ := hβc.bounded_above_of_compact_support hβs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hβu : UniformContinuous β := hβs.uniformContinuous_of_continuous hβc
  set e : Fin m → Euclid m := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hej : ∀ j, ‖e j‖ = 1 := by intro j; simp [he]
  set Φ : Euclid P × (Euclid m →L[ℝ] Euclid P) → ℝ := fun p => β p.1 (fun j => p.2 (e j)) with hΦ
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => β p.1 :=
      hβc.comp continuous_fst
    have h2 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => (fun j => p.2 (e j)) :=
      continuous_pi fun j => (continuous_eval_const (e j)).comp continuous_snd
    exact continuous_eval.comp (h1.prodMk h2)
  set G : ℕ → Euclid m → Euclid P := fun i w => ι w + ι' (gs i w) with hG
  set H : ℕ → Euclid m → ℝ := fun i w => Φ (G i w, fderiv ℝ (G i) w) with hH
  set H' : Euclid m → ℝ := fun w => β (ι w + ι' b) (fun j => ι (e j)) with hH'
  change Tendsto (fun i => ∫ w in As i ∩ B, H i w) atTop (𝓝 (∫ w in A ∩ B, H' w))
  have hD : ∀ i w, DifferentiableAt ℝ (gs i) w →
      fderiv ℝ (G i) w = ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w) := by
    intro i w hw
    have hι : HasFDerivAt (fun w => ι w) ι.toContinuousLinearMap w :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun w => ι' (gs i w))
        (ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w)) w :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp w hw.hasFDerivAt
    exact (hι.add hι').fderiv
  have hH'b : ∀ w, ‖H' w‖ ≤ M := by
    intro w
    calc ‖H' w‖ ≤ ‖β (ι w + ι' b)‖ * ∏ j, ‖ι (e j)‖ := ContinuousAlternatingMap.le_opNorm _ _
      _ = ‖β (ι w + ι' b)‖ := by simp [hej]
      _ ≤ M := hM _
  have hH'c : Continuous H' := by
    have h1 : Continuous fun w : Euclid m => β (ι w + ι' b) :=
      hβc.comp (ι.continuous.add continuous_const)
    exact (continuous_eval_const (fun j => ι (e j))).comp h1
  -- pointwise estimate
  have hpt : ∀ i w, DifferentiableAt ℝ (gs i) w → ‖fderiv ℝ (gs i) w‖ ≤ 1 →
      ‖H i w - H' w‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ +
        M * m * 2 ^ m * ‖fderiv ℝ (gs i) w‖ := by
    intro i w hd hL1
    set L := fderiv ℝ (gs i) w with hL
    set u : Fin m → Euclid P := fun j => fderiv ℝ (G i) w (e j) with hueq
    set u' : Fin m → Euclid P := fun j => ι (e j) with hu'eq
    have hu : ∀ j, u j = ι (e j) + ι' (L (e j)) := by
      intro j
      simp [u, hD i w hd, L]
    have hunorm : ‖u‖ ≤ 2 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [hu j]
      calc ‖ι (e j) + ι' (L (e j))‖ ≤ ‖ι (e j)‖ + ‖ι' (L (e j))‖ := norm_add_le _ _
        _ = 1 + ‖L (e j)‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map, hej]
        _ ≤ 1 + ‖L‖ * ‖e j‖ := by gcongr; exact L.le_opNorm _
        _ ≤ 2 := by rw [hej]; linarith
    have hu'norm : ‖u'‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      simp [u', hej]
    have hdiff : ‖u - u'‖ ≤ ‖L‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      rw [Pi.sub_apply, hu j]
      simp only [u', add_sub_cancel_left, LinearIsometry.norm_map]
      calc ‖L (e j)‖ ≤ ‖L‖ * ‖e j‖ := L.le_opNorm _
        _ = ‖L‖ := by rw [hej, mul_one]
    have h1 : ‖β (G i w) u - β (ι w + ι' b) u‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ := by
      rw [← ContinuousAlternatingMap.sub_apply]
      calc _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * ∏ j, ‖u j‖ :=
            ContinuousAlternatingMap.le_opNorm _ _
        _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * 2 ^ m := by
          gcongr
          calc ∏ j, ‖u j‖ ≤ ∏ _j : Fin m, (2 : ℝ) :=
                Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
                  (fun j _ => (norm_le_pi_norm u j).trans hunorm)
            _ = 2 ^ m := by simp
        _ = _ := mul_comm _ _
    have h2 : ‖β (ι w + ι' b) u - β (ι w + ι' b) u'‖ ≤ M * m * 2 ^ m * ‖L‖ := by
      calc _ ≤ ‖β (ι w + ι' b)‖ * (Fintype.card (Fin m)) *
              (max ‖u‖ ‖u'‖) ^ (Fintype.card (Fin m) - 1) * ‖u - u'‖ :=
            ContinuousAlternatingMap.norm_image_sub_le _ _ _
        _ ≤ M * m * 2 ^ m * ‖L‖ := by
            rw [Fintype.card_fin]
            have hmax : max ‖u‖ ‖u'‖ ≤ 2 := max_le hunorm (hu'norm.trans (by norm_num))
            have hpow : (max ‖u‖ ‖u'‖) ^ (m - 1) ≤ 2 ^ m :=
              (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax _).trans
                (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
            gcongr
            exact hM _
    have hsplit : H i w - H' w =
        (β (G i w) u - β (ι w + ι' b) u) + (β (ι w + ι' b) u - β (ι w + ι' b) u') := by
      simp only [H, H', Φ, u, u']
      ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  -- uniform convergence on B
  have hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ w ∈ B, ‖H i w - H' w‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδβ⟩ := Metric.uniformContinuous_iff.1 hβu (ε / (2 * 2 ^ m)) (by positivity)
    set X : ℝ := M * m * 2 ^ m with hX
    have hX0 : 0 ≤ X := by positivity
    set η : ℝ := min 1 (ε / (2 * (X + 1))) with hη
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    filter_upwards [hH1, hH2 δ hδ, hH2 η hηpos] with i hi1 hi2 hi3
    intro w hw
    have hd := hi1 w hw
    have hL1 : ‖fderiv ℝ (gs i) w‖ ≤ 1 := (hi3 w hw).2.le.trans (min_le_left _ _)
    have hLη : ‖fderiv ℝ (gs i) w‖ ≤ ε / (2 * (X + 1)) :=
      (hi3 w hw).2.le.trans (min_le_right _ _)
    have hβd : ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / (2 * 2 ^ m) := by
      rw [← dist_eq_norm]
      apply le_of_lt
      apply hδβ
      rw [dist_eq_norm]
      simp only [G]
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometry.norm_map]
      exact (hi2 w hw).1
    refine (hpt i w hd hL1).trans ?_
    have e1 : 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / 2 := by
      calc 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ 2 ^ m * (ε / (2 * 2 ^ m)) := by gcongr
        _ = ε / 2 := by field_simp
    have e2 : X * ‖fderiv ℝ (gs i) w‖ ≤ ε / 2 := by
      calc X * ‖fderiv ℝ (gs i) w‖ ≤ X * (ε / (2 * (X + 1))) := by gcongr
        _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    linarith
  -- measurability
  have hHmeas : ∀ᶠ i in atTop, AEStronglyMeasurable (H i) (volume.restrict B) := by
    filter_upwards [hH1] with i hi
    have hGc : ContinuousOn (G i) B := fun w hw =>
      (ι.continuous.continuousAt.add
        (ι'.continuous.continuousAt.comp (hi w hw).continuousAt)).continuousWithinAt
    have h1 : AEStronglyMeasurable (G i) (volume.restrict B) := hGc.aestronglyMeasurable hBmeas
    have h2 : AEStronglyMeasurable (fderiv ℝ (G i)) (volume.restrict B) :=
      (measurable_fderiv ℝ (G i)).aestronglyMeasurable
    exact hΦc.comp_aestronglyMeasurable (h1.prodMk h2)
  -- the symmetric differences
  have hsymm' : Tendsto (fun i => (volume (symmDiff (As i) A ∩ B)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
    simpa [Function.comp_def] using this
  set VB : ℝ := (volume B).toReal with hVB
  have hVB0 : 0 ≤ VB := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hunif (ε / (2 * (VB + 1))) (by positivity), hunif 1 one_pos, hHmeas,
    hsymm'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by positivity))]
    with i hi1 hi1' hi2 hi3
  have hsB : As i ∩ B ⊆ B := inter_subset_right
  have hsfin : volume (As i ∩ B) < ⊤ := (measure_mono hsB).trans_lt hBfin
  have htfin : volume (A ∩ B) < ⊤ := (measure_mono inter_subset_right).trans_lt hBfin
  have hsmeas : MeasurableSet (As i ∩ B) := (hAs i).inter hBmeas
  have htmeas : MeasurableSet (A ∩ B) := hA.inter hBmeas
  have hHi_int : IntegrableOn (H i) (As i ∩ B) := by
    refine IntegrableOn.of_bound hsfin (hi2.mono_measure (Measure.restrict_mono hsB le_rfl)) (M + 1) ?_
    refine (ae_restrict_iff' hsmeas).2 (Eventually.of_forall fun w hw => ?_)
    have h := hi1' w hw.2
    calc ‖H i w‖ = ‖(H i w - H' w) + H' w‖ := by rw [sub_add_cancel]
      _ ≤ ‖H i w - H' w‖ + ‖H' w‖ := norm_add_le _ _
      _ ≤ 1 + M := add_le_add h (hH'b w)
      _ = M + 1 := add_comm _ _
  have hH'_int : ∀ s : Set (Euclid m), volume s < ⊤ → IntegrableOn H' s := fun s hs =>
    IntegrableOn.of_bound hs hH'c.aestronglyMeasurable M (Eventually.of_forall hH'b)
  -- first term
  have hT1 : ‖(∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w‖ ≤ ε / (2 * (VB + 1)) * VB := by
    rw [← integral_sub hHi_int (hH'_int _ hsfin)]
    refine (norm_setIntegral_le_of_norm_le_const hsfin fun w hw => hi1 w hw.2).trans ?_
    gcongr
    exact measureReal_mono hsB hBfin.ne
  -- second term
  have hT2 : ‖(∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w‖ ≤
      2 * M * (volume (symmDiff (As i) A ∩ B)).toReal := by
    have e1 := integral_inter_add_sdiff htmeas (hH'_int _ hsfin)
    have e2 := integral_inter_add_sdiff hsmeas (hH'_int _ htfin)
    rw [inter_comm (A ∩ B)] at e2
    have hsub1 : (As i ∩ B) \ (A ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inl ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hsub2 : (A ∩ B) \ (As i ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inr ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hΔfin : volume (symmDiff (As i) A ∩ B) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt hBfin
    have b1 : ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub1).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub1 hΔfin.ne
    have b2 : ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub2).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub2 hΔfin.ne
    have : (∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w =
        (∫ w in (As i ∩ B) \ (A ∩ B), H' w) - ∫ w in (A ∩ B) \ (As i ∩ B), H' w := by
      linarith
    rw [this]
    calc _ ≤ ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ + ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [dist_eq_norm]
  have hsum : (∫ w in As i ∩ B, H i w) - ∫ w in A ∩ B, H' w =
      ((∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w) +
        ((∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w) := by ring
  rw [hsum]
  have hlt1 : ε / (2 * (VB + 1)) * VB < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlt2 : 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal ≤ ε / 2 := by
    have h3 : (volume (symmDiff (As i) A ∩ B)).toReal < ε / (4 * (M + 1)) := hi3
    have h4 : 0 ≤ (volume (symmDiff (As i) A ∩ B)).toReal := ENNReal.toReal_nonneg
    calc 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal
        ≤ 2 * (M + 1) * (volume (symmDiff (As i) A ∩ B)).toReal := by gcongr; linarith
      _ ≤ 2 * (M + 1) * (ε / (4 * (M + 1))) := by gcongr
      _ = ε / 2 := by field_simp; ring
  calc _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

## Key steps

1. β is bounded by M and uniformly continuous; the limit integrand h(w) = β(ιw + ι'b)(ιe) is continuous with |h| ≤ M.
2. Where g_i is differentiable at w with ‖Dg_i(w)‖ ≤ 1, DG_i(w) = ι + ι'∘Dg_i(w) and the multilinear estimates give |h_i(w) − h(w)| ≤ 2^m|β(G_i(w)) − β(ιw + ι'b)| + M·m·2^m·‖Dg_i(w)‖.
3. With the C¹ hypothesis and uniform continuity of β, sup_B |h_i − h| → 0.
4. For large i, h_i is a.e.-strongly measurable on B (G_i continuous on B, measurable_fderiv, Φ continuous), hence integrable on A_i ∩ B.
5. |∫_{A_i∩B} h_i − ∫_{A∩B} h| ≤ L(B)·sup_B|h_i − h| + 2M·L((A_i Δ A) ∩ B) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: the selected node (status, message, children, descendants by id prefix); lean_name lookup of the 6 child names and of codim1_zsl_perimeter_compactness; byte equality of the 2 reused lean_statements and statements with decomposition-v1.json; raw count of 'codim1_zsl_fl_'; scan of nodes/*/*.json outside this node for 'codim1_zsl_fl_'`
- `python3 dump of this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and parent-child-handoff.json; issue-workers.json entries for issue 5038`
- `git log --all --oneline -S'codim1_zsl_fl_' -- 'GMT/*.lean' (0 commits); positive control git log --all --oneline -S'dgcr_bwd_graph_pullback_extDeriv' -- 'GMT/*.lean'`
- `git show dcc3f4b7fc0f6beb359e7585fbca8b266cc0f38f:GMT/Ch07/Submission.lean; git show 42e24164cfdc5445c7426ab7ee11003f8faee961:GMT/Ch07/Submission.lean (the accepted reused blocks)`
- `grep -n 'structure TestFormOn|def IsTestForm|theorem exteriorDerivative_isTestForm|theorem tsupport_exteriorDerivative_subset|def exteriorDerivative|def covectorEuclideanNorm|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem affinePullbackForm_isSmoothForm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|Bornology.IsBounded.subset_ball_lt|theorem norm_add_sq_real' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -rl 'map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume' local-references/123e8435b4a2469b/mathlib/Mathlib; diff of snapshot vs .lake/packages/mathlib Bochner/Set.lean (identical)`
- `lake env lean /tmp/fl-v2-decomp/lean/Check2.lean (frozen Submission.lean + accepted dcc3f4b7/42e24164 blocks + sorry placeholder for codim1_zsl_perimeter_compactness + verbatim code of the 4 new children + selected theorem; #print axioms of all 7)`
- `lake env lean /tmp/fl-v2-decomp/lean/Types.lean (import GMT.Ch07.Submission + gmt-compare.contract_scope replay; the 6 child types and the selected type as comparator-style challenges)`
- `lake env lean /tmp/fl-v2-decomp/lean/ContractAssembly2.lean (selected type proved from hypotheses with the frozen perimeter_bound, bv_compactness, graph_integral_limit and isometric_transport types; #print axioms)`
- `python3: lean_contract.validate_lean_statement on the 6 types; leaf_verification.check_source_delta on the 4 new children inserted into GMT/Ch07/Submission.lean; models.ScopedDecomposition validation of this response`
- `sed -n 840,860p book/chapter-07.txt (Simon 7.5.3: by (1) and 5.2 and the BV Compactness 2.6 of Ch. 2 a subsequence converges in L¹_loc)`
- `grep -l '"github_selected_issue": 5038,' .humanize/swarm-configs/* and their max_nodes/max_depth/max_children (cffb5a36…: max_nodes 1000, 08:33Z; 5261729…: max_nodes 5000, 11:17Z); mtime ranges of configs by max_nodes value`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-scope-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-d253855dab51/scripts/gmt-compare.py`
- `/tmp/fl-v2-decomp/lean/Check2.lean`
- `/tmp/fl-v2-decomp/lean/Types.lean`
- `/tmp/fl-v2-decomp/lean/ContractAssembly2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/cffb5a36c88f487d9fb784e09cf6981b.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/5261729094924bd1900f1bef36365ca3.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG state. The selected node is 'decomposing' at 'subproblem decomposition attempt 2' and has no children or descendants. Its v1 split passed the independent review (all six nodes acceptable, no required changes) but was never activated. The cause is not recorded. The first worker's config had max_nodes 1000 while the DAG approached 1000 nodes; the current worker's config has max_nodes 5000. The four codim1_zsl_fl_* names occur nowhere in dag.json (1083 nodes at 12:11Z), in other nodes' files, in GMT/, in simongmt or in git history. dgcr_bwd_coordinate_covector (dcc3f4b7) and dgcr_bwd_graph_pullback_extDeriv (42e24164) are accepted, and their DAG types and statements are byte-identical to the reused subproblems.
Library. The SimonGMT definitions used by the children check out: TestFormOn is the submodule of IsTestForm forms supported in U; exteriorDerivative is extDeriv; exteriorDerivative_isTestForm and tsupport_exteriorDerivative_subset hold; covectorEuclideanNorm is the root of the sum of squared strictly-increasing coordinate coefficients; and affinePullbackForm commutes with d. The snapshot Mathlib contains every lemma the assembly cites: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), Bornology.IsBounded.subset_ball_lt (Bounded.lean:105), norm_add_sq_real (InnerProductSpace/Basic.lean:411), and the Hausdorff isometry lemmas (Geometry/Euclidean/Volume/Measure.lean).
Lean (pinned toolchain v4.35.0-rc3). Check2.lean compiles: each of the six children depends only on propext, Classical.choice and Quot.sound, and the selected theorem adds sorryAx solely through the bv_compactness placeholder. ContractAssembly2.lean proves the selected type from the four frozen contract types alone, with only the three standard axioms. Types.lean elaborates all seven types in the comparator's replayed contract scope. validate_lean_statement and check_source_delta accept every child.
Source. Simon 7.5.3 (book/chapter-07.txt lines 852–856) obtains the L¹_loc subsequence from the BV Compactness 2.6 of Ch. 2, which is the sibling bv_compactness.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
