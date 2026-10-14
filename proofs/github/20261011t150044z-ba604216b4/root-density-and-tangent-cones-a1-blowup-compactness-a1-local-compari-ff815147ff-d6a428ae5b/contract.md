<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.density_gradient_bound-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_co_density_gradient_bound`

Let d, P ∈ ℕ, L ≥ 0, f : ℝ^P → ℝ L-Lipschitz, ψ : ℝ^d → ℝ^P, F : ℝ^d → ℝ, and Y ⊆ ℝ^d an arbitrary set with f(ψ(z)) = F(z) for every z ∈ Y. Let y ∈ Y be a point at which ψ and F are differentiable and which is a Lebesgue density point of Y: L^d(Y ∩ B̄_r(y))/L^d(B̄_r(y)) → 1 as r ↓ 0 (L^d = volume on ℝ^d = Euclid d, as an outer measure; B̄_r(y) = closedBall y r; quotient in [0, ∞]). Then |DF(y)e| ≤ L|Dψ(y)e| for every e ∈ ℝ^d.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.density_gradient_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6085

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_co_density_gradient_bound`

```lean
∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖
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
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.density_gradient_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(a) of the parent proof (its first three bullets): density points admit sequences y_k ∈ Y approaching y from every direction, and dividing |F(y_k) − F(y)| ≤ L|ψ(y_k) − ψ(y)| by |y_k − y| gives the bound. The truncated cone of the parent proof is replaced by a ball inside it, which gives the same scaling argument with ball measures only.
Notation: B := Dψ(y), ℓ := DF(y); |·| Euclidean norm; B_r(z) open ball, B̄_r(z) closed ball; ω := L^d(B_1(0)).

1. (Reduction to unit vectors.) If e = 0 both sides are 0. If e ≠ 0 put u := e/|e|; if |ℓu| ≤ L|Bu| then |ℓe| = |e||ℓu| ≤ L|e||Bu| = L|Be| by linearity. So it suffices to prove |ℓu| ≤ L|Bu| for every u ∈ ℝ^d with |u| = 1. Fix such u; in particular d ≥ 1, so 0 < ω < ∞ and r ↦ r^d is positive for r > 0.
2. (An elementary inequality.) For a, b ∈ ℝ^d ∖ {0}: |a/|a| − b/|b|| ≤ 2|a − b|/|b|. Indeed a/|a| − b/|b| = (a − b)/|b| + a·(|b| − |a|)/(|a||b|), and ||b| − |a|| ≤ |a − b|.
3. (Directions claim.) For every δ ∈ (0, 1) there is z ∈ Y with 0 < |z − y| < δ and |(z − y)/|z − y| − u| < δ.
 Proof by contradiction: let δ ∈ (0, 1) be such that no such z exists. Put ρ := min(δ/8, 1/4) > 0. For 0 < r < δ let W_r := B_{rρ}(y + (r/2)u).
 (a) W_r ⊆ B̄_r(y) and W_r ∩ Y = ∅. Let w ∈ W_r and v := (w − y)/r; then |v − u/2| < ρ, so |v| ≥ 1/2 − ρ ≥ 1/4 > 0 and |v| ≤ 1/2 + ρ ≤ 3/4. Hence 0 < |w − y| = r|v| ≤ 3r/4 < δ and w ∈ B̄_r(y). By step 2 with a := v, b := u/2 (|b| = 1/2, b/|b| = u) and (w − y)/|w − y| = v/|v|: |(w − y)/|w − y| − u| ≤ 4|v − u/2| < 4ρ ≤ δ/2 < δ. So w would be a point z as in the claim unless w ∉ Y; by the contradiction hypothesis w ∉ Y.
 (b) By translation invariance and scaling of Lebesgue measure (Measure.addHaar_ball_of_pos, Measure.addHaar_closedBall, finrank ℝ^d = d): L^d(W_r) = (rρ)^d ω and L^d(B̄_r(y)) = r^d ω, both finite and positive. W_r is open (measurable), W_r ⊆ B̄_r(y), and by (a) Y ∩ B̄_r(y) ⊆ B̄_r(y) ∖ W_r. By monotonicity of the outer measure and measure_diff,
 L^d(Y ∩ B̄_r(y)) ≤ L^d(B̄_r(y)) − L^d(W_r) = (1 − ρ^d)·L^d(B̄_r(y)).
 (c) Thus L^d(Y ∩ B̄_r(y))/L^d(B̄_r(y)) ≤ 1 − ρ^d for every r ∈ (0, δ), which is a set belonging to 𝓝[>] 0. Passing to the limit (le_of_tendsto), the hypothesis gives 1 ≤ 1 − ρ^d, impossible because ρ^d > 0. This proves the claim.
4. (A sequence.) For k ∈ ℕ apply step 3 with δ := (k + 2)⁻¹: there is z_k ∈ Y with s_k := |z_k − y| ∈ (0, (k + 2)⁻¹) and |u_k − u| < (k + 2)⁻¹, where u_k := (z_k − y)/s_k. Hence z_k → y, s_k > 0, s_k → 0, and u_k → u.
5. (Difference quotients.) F is differentiable at y, so F(z) − F(y) − ℓ(z − y) = o(|z − y|) as z → y (HasFDerivAt.isLittleO). Since z_k → y with z_k ≠ y and z_k − y = s_k u_k,
 (F(z_k) − F(y))/s_k = ℓ(u_k) + (F(z_k) − F(y) − ℓ(z_k − y))/s_k → ℓ(u),
 using continuity of ℓ and u_k → u. In the same way (ψ(z_k) − ψ(y))/s_k → Bu.
6. (Lipschitz comparison.) z_k ∈ Y and y ∈ Y, so F(z_k) − F(y) = f(ψ(z_k)) − f(ψ(y)) and |F(z_k) − F(y)| ≤ L|ψ(z_k) − ψ(y)|. Dividing by s_k > 0: |(F(z_k) − F(y))/s_k| ≤ L|(ψ(z_k) − ψ(y))/s_k| for every k. Both sides converge by step 5 and continuity of |·|, and limits preserve non-strict inequalities (le_of_tendsto_of_tendsto'), so |ℓu| ≤ L|Bu|. By step 1 this proves the statement. ∎

Lean realization note. The verified code below proves the directions claim of step 3 for an arbitrary vector e instead of a unit vector, which also removes the reductions of steps 1–2: for ε, T > 0 there are t ∈ (0, T) and z ∈ Y with |z − (y + te)| < εt. It uses the ball B_{(ε/k)r}(y + (r/k)e) ⊆ B̄_r(y), k := |e| + ε (the same ball-in-cone measure argument, ρ = ε/k), and the additive form L^d(Y ∩ B̄_r(y)) + L^d(ball) ≤ L^d(B̄_r(y)) (so ratio + ρ^d ≤ 1, contradicting ratio → 1) instead of truncated subtraction. Steps 4–6 are realised with HasFDerivWithinAt.lim (c_n := t_n⁻¹, d_n := z_n − y) for both F and ψ and le_of_tendsto_of_tendsto'.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It uses no sibling declaration. Auxiliary lemmas are named `Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets`, `Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir` to stay globally unique; they may be renamed or inlined. It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_density_gradient_bound` has exactly the frozen type of this child.

```lean
/-- At a density point `y` of `Y`, for every `ρ > 0` and all small `r > 0`, every ball of radius
`ρ r` contained in `closedBall y r` meets `Y`. -/
theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets {d : ℕ} {Y : Set (Euclid d)} {y : Euclid d}
    (hY : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ p : Euclid d, ball p (ρ * r) ⊆ closedBall y r →
      (Y ∩ ball p (ρ * r)).Nonempty := by
  have hc0 : ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hρ _
  have h1 : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)
      + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d))) (𝓝[>] 0)
      (𝓝 (1 + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)))) :=
    hY.add tendsto_const_nhds
  have hlt : (1 : ℝ≥0∞) < 1 + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) :=
    ENNReal.lt_add_right ENNReal.one_ne_top hc0
  filter_upwards [(tendsto_order.1 h1).1 1 hlt, self_mem_nhdsWithin] with r hr hr0 p hsub
  have hr0' : 0 < r := hr0
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hdisj : Disjoint (Y ∩ closedBall y r) (ball p (ρ * r)) := by
    rw [Set.disjoint_left]
    intro z hz hzW
    have hmem : z ∈ Y ∩ ball p (ρ * r) := ⟨hz.1, hzW⟩
    rw [hne] at hmem
    exact hmem
  have hmeas : volume (Y ∩ closedBall y r) + volume (ball p (ρ * r)) ≤
      volume (closedBall y r) := by
    rw [← measure_union hdisj measurableSet_ball]
    exact measure_mono (union_subset inter_subset_right hsub)
  have hVW : volume (ball p (ρ * r)) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) * volume (closedBall y r) := by
    rw [Measure.addHaar_ball_of_pos volume p (mul_pos hρ hr0'),
      Measure.addHaar_closedBall volume y hr0'.le, mul_pow,
      ENNReal.ofReal_mul (pow_nonneg hρ.le _), mul_assoc]
  have hV0 : volume (closedBall y r) ≠ 0 := (measure_closedBall_pos volume y hr0').ne'
  have hVT : volume (closedBall y r) ≠ ∞ := measure_closedBall_lt_top.ne
  have hle : volume (Y ∩ closedBall y r) / volume (closedBall y r)
      + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) ≤ 1 := by
    calc volume (Y ∩ closedBall y r) / volume (closedBall y r)
          + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d))
        = (volume (Y ∩ closedBall y r) + volume (ball p (ρ * r))) / volume (closedBall y r) := by
          rw [ENNReal.add_div, hVW, ENNReal.mul_div_cancel_right hV0 hVT]
      _ ≤ volume (closedBall y r) / volume (closedBall y r) := ENNReal.div_le_div_right hmeas _
      _ = 1 := ENNReal.div_self hV0 hVT
  exact absurd hr (not_lt.2 hle)

/-- Directions claim: at a density point `y` of `Y`, every vector `e` is approximated by
difference quotients of points of `Y`. -/
theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir {d : ℕ} {Y : Set (Euclid d)} {y : Euclid d}
    (hY : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1))
    (e : Euclid d) {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) :
    ∃ t ∈ Ioo 0 T, ∃ z ∈ Y, dist z (y + t • e) < ε * t := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = ‖e‖ + ε := ⟨_, rfl⟩
  have hkpos : 0 < k := by rw [hk]; positivity
  obtain ⟨r, hr, hrT⟩ := ((Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets hY (div_pos hε hkpos)).and
    (Ioo_mem_nhdsGT (mul_pos hT hkpos))).exists
  have htpos : 0 < r / k := div_pos hrT.1 hkpos
  have hρr : ε / k * r = ε * (r / k) := by ring
  have hsub : ball (y + (r / k) • e) (ε / k * r) ⊆ closedBall y r := by
    intro w hw
    rw [mem_ball, hρr] at hw
    rw [mem_closedBall]
    have h1 : dist (y + (r / k) • e) y = r / k * ‖e‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have h2 : r / k * ‖e‖ + ε * (r / k) = r := by
      calc r / k * ‖e‖ + ε * (r / k) = r / k * (‖e‖ + ε) := by ring
        _ = r / k * k := by rw [hk]
        _ = r := div_mul_cancel₀ r hkpos.ne'
    linarith [dist_triangle w (y + (r / k) • e) y]
  obtain ⟨z, hzY, hzW⟩ := hr (y + (r / k) • e) hsub
  refine ⟨r / k, ⟨htpos, (div_lt_iff₀ hkpos).2 hrT.2⟩, z, hzY, ?_⟩
  rw [mem_ball, hρr] at hzW
  exact hzW

theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound : ∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖ := by
  intro d P f L ψ F Y y hf hyY hψ hF hfψ hY e
  have key : ∀ n : ℕ, ∃ t ∈ Ioo (0:ℝ) (1 / ((n:ℝ) + 1)), ∃ z ∈ Y,
      dist z (y + t • e) < 1 / ((n:ℝ) + 1) * t :=
    fun n => Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir hY e (by positivity) (by positivity)
  choose t ht z hz hzt using key
  have hlim0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun n => (ht n).1.le) (fun n => (ht n).2.le) hlim0
  have hcd : Tendsto (fun n => (t n)⁻¹ • (z n - y)) atTop (𝓝 e) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    have htn : 0 < t n := (ht n).1
    have hrw : (t n)⁻¹ • (z n - y) - e = (t n)⁻¹ • (z n - (y + t n • e)) := by
      rw [sub_add_eq_sub_sub, smul_sub (t n)⁻¹ (z n - y), smul_smul, inv_mul_cancel₀ htn.ne',
        one_smul]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htn, ← dist_eq_norm,
      inv_mul_le_iff₀ htn, mul_comm]
    exact (hzt n).le
  have hdlim : Tendsto (fun n => z n - y) atTop (𝓝 0) := by
    have h := ht0.smul hcd
    rw [zero_smul] at h
    refine h.congr (fun n => ?_)
    rw [smul_smul, mul_inv_cancel₀ (ht n).1.ne', one_smul]
  have hF' := (hasFDerivWithinAt_univ.2 hF.hasFDerivAt).lim hdlim
    (Eventually.of_forall fun n => mem_univ _) hcd
  have hψ' := (hasFDerivWithinAt_univ.2 hψ.hasFDerivAt).lim hdlim
    (Eventually.of_forall fun n => mem_univ _) hcd
  simp only [add_sub_cancel] at hF' hψ'
  refine le_of_tendsto_of_tendsto' hF'.abs (hψ'.norm.const_mul (L:ℝ)) (fun n => ?_)
  have htn : 0 < t n := (ht n).1
  rw [smul_eq_mul, abs_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htn,
    ← hfψ _ (hz n), ← hfψ _ hyY]
  have hL := hf.dist_le_mul (ψ (z n)) (ψ y)
  rw [Real.dist_eq, dist_eq_norm] at hL
  calc (t n)⁻¹ * |f (ψ (z n)) - f (ψ y)| ≤ (t n)⁻¹ * (L * ‖ψ (z n) - ψ y‖) :=
        mul_le_mul_of_nonneg_left hL (inv_nonneg.2 htn.le)
    _ = L * ((t n)⁻¹ * ‖ψ (z n) - ψ y‖) := by ring
```

## Key steps

1. Reduce to unit vectors u (d ≥ 1).
2. Directions: if no z ∈ Y near y has direction within δ of u, the ball B_{rρ}(y + (r/2)u) ⊆ B̄_r(y) (ρ = min(δ/8, 1/4)) misses Y for all r < δ, so the density ratio is ≤ 1 − ρ^d < 1, contradicting density 1.
3. Choose z_k ∈ Y, z_k → y, z_k ≠ y, (z_k − y)/|z_k − y| → u.
4. Divide |F(z_k) − F(y)| = |f(ψ z_k) − f(ψ y)| ≤ L|ψ(z_k) − ψ(y)| by |z_k − y| and let k → ∞ using differentiability: |DF(y)u| ≤ L|Dψ(y)u|.
5. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

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
