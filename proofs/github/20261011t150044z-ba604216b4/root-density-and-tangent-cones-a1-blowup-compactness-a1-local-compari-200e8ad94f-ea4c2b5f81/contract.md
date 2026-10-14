<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.de_giorgi-a1 -->

## Theorem `Submission.dtc_bc_lc_fd_bim_de_giorgi`

Let n ≥ 1, let E ⊆ ℝ^{n+1} be Borel and C ∈ ℝ, and assume ∫_E div φ dL^{n+1} ≤ C for every C^∞ compactly supported φ : ℝ^{n+1} → ℝ^{n+1} with |φ| ≤ 1 everywhere (div φ = trace Dφ, L^{n+1} = volume). Then there are a Borel set B ⊆ ℝ^{n+1} and a Borel map ν : ℝ^{n+1} → ℝ^{n+1} such that: B is countably n-rectifiable and H^n(B) < ∞ (H^n = μHE[n]); |ν(y)| = 1 for y ∈ B; for H^n-a.e. y ∈ B the approximate tangent space of B at y (Simon Ch. 3, 1.4; SimonGMT HasApproximateTangentSpaceAt) is (span{ν(y)})^⊥; ∫_E div φ dL^{n+1} = −∫_B ⟨φ, ν⟩ dH^n for every C¹ compactly supported φ; and for H^n-a.e. y ∈ B and every ρ ∈ ℝ, L^{n+1}((E_{y,r} Δ {w : ⟨w, ν(y)⟩ > 0}) ∩ B_ρ(0)) → 0 as r ↓ 0, where E_{y,r} := {w : y + rw ∈ E}.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.de_giorgi-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6358

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5160, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4725

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_fd_bim_de_giorgi`

```lean
∀ (n : ℕ) (E : Set (Euclid (n + 1))) (C : ℝ), 1 ≤ n → MeasurableSet E → (∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ y : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) ≤ C) → ∃ (B : Set (Euclid (n + 1))) (ν : Euclid (n + 1) → Euclid (n + 1)), MeasurableSet B ∧ CountablyRectifiable n B ∧ μHE[n] B ≠ ∞ ∧ Measurable ν ∧ (∀ y ∈ B, ‖ν y‖ = 1) ∧ (∀ᵐ y ∂(μHE[n].restrict B), HasApproximateTangentSpaceAt n B y (Submodule.span ℝ {ν y})ᗮ) ∧ (∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ y in E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ y : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) = -∫ y in B, inner ℝ (φ y) (ν y) ∂μHE[n]) ∧ ∀ᵐ y ∂(μHE[n].restrict B), ∀ ρ : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' E) {w | 0 < inner ℝ w (ν y)} ∩ ball (0 : Euclid (n + 1)) ρ)) (𝓝[>] 0) (𝓝 0)
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.de_giorgi-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, 4.1–4.3 (De Giorgi; chapter-03.txt lines 551–746), for U = ℝ^{n+1}. Also used:
- Ch. 2, 2.1–2.2 and 2.5–2.6 (BV functions, mollification, compactness; chapter-02.txt lines 477–626);
- Ch. 1, 3.23 and 4.16 (differentiation of Radon measures; compactness of Radon measures).
This is the De Giorgi input of step 8 of the parent proof. Simon's 3.14 uses 4.3(‡), the half-space blow-up, for the compatibility of the normals of nested sets; the OCR has lost the symbol, and the supplied text writes '4.3(∗)' for the same item.
Errata applied:
- (i) The OCR of 4.1 drops the minus sign. For the inward normal ν the identity is ∫_E div g dL^{n+1} = −∫⟨g, ν⟩ dμ_E.
- (ii) The limit set (9) is {z^{n+1} > c}, not '<': with inward normal e_{n+1}, the blow-ups converge to the upper half-space, consistent with (‡).
- (iii) The printed first sentence of the proof of 4.3 ('By 1.6 and 3.6 of Ch. 1 the first part follows from (†)') is a whole argument: comparison of μ with H^n, the rectifiability criterion of Ch. 3, 1.6 '⇐' for a measure with flat tangent measures, density one of rectifiable sets, and Radon–Nikodym. Here it is supplied in step 5 by the accepted siblings measure_eq_hausdorff and rect_density_one, whose hypotheses are verified there. Those siblings produce rectifiability and the identity μ = H^n⌞B together, from the tangent-measure convergence of step 4(f) alone. So no step uses μ = H^n⌞B before it is established.
Siblings used: gauss_green_measure (codim1_rdo_dg_gauss_green_measure), the Riesz-representation step 4.1; measure_eq_hausdorff (codim1_rdo_dg_measure_eq_hausdorff); rect_density_one (codim1_rdo_rectifiable_ae_density_one).
Notation: L := L^{n+1} = volume = μHE[n+1]; H^n := μHE[n]; ω_k := L^k(B_1); div φ := trace Dφ; η_{y,λ}(z) := λ^{−1}(z − y); E_{y,λ} := η_{y,λ}(E) = {w : y + λw ∈ E}; C₊ := max(C, 0).
1. (Gauss–Green measure; 4.1.) The hypothesis holds with C_K := C for every compact K. So gauss_green_measure (m := n, D := ℝ^{n+1}, F := E) gives a Borel measure μ with μ(K) < ∞ for every compact K, and a Borel ν with |ν(y)| = 1 for every y, such that (4.1) ∫_E div φ dL = −∫⟨φ, ν⟩ dμ for every C¹ compactly supported φ.
2. (Finite total mass.)
 (a) Continuous test fields. Let g be C¹ and compactly supported with |g| ≤ 1. Its mollifications g_ε are C^∞, have |g_ε| ≤ 1, supports in a fixed compact set, and div g_ε → div g uniformly. The hypothesis for −g_ε gives −∫_E div g_ε ≤ C, so ∫⟨g, ν⟩dμ = −∫_E div g ≤ C₊. By uniform approximation, ∫⟨g, ν⟩ dμ ≤ C₊ for every continuous compactly supported g with |g| ≤ 1.
 (b) μ(K) ≤ C₊. Let K be compact and κ > 0. By Lusin there is a compact K' ⊆ K with μ(K ∖ K') < κ and ν|_{K'} continuous. Choose an open W ⊇ K with μ(W ∖ K) < κ. Extend ν|_{K'} to a continuous unit-bounded g (Tietze, then radial retraction onto the unit ball), and multiply it by χ ∈ C_c(W; [0, 1]) with χ = 1 on K'. Then ∫⟨χg, ν⟩dμ ≥ μ(K') − μ(W ∖ K') ≥ μ(K) − 3κ. So μ(K) ≤ C₊ for every compact K, and μ(ℝ^{n+1}) ≤ C₊.
3. (Reduced boundary; 4.2.) Let ∂*E be the set of y ∈ spt μ at which ν_E(y) := lim_{ρ↓0}μ(B̄_ρ(y))^{−1}∫_{B̄_ρ(y)}ν dμ exists and |ν_E(y)| = 1. By differentiation of Radon measures (Ch. 1, 3.23; Mathlib VitaliFamily.ae_tendsto_average with the Besicovitch family), these averages tend to ν(y) for μ-a.e. y. Hence μ(ℝ^{n+1} ∖ ∂*E) = 0 and ν_E = ν μ-a.e.
4. (Blow-up at y ∈ ∂*E; printed proof of 4.3, (1)–(12).) After a rigid motion, y = 0 and ν_E(0) = e_{n+1}. Put E_λ := E_{0,λ}, μ_λ(A) := λ^{−n}μ(λA) and ν_λ(z) := ν(λz); then (4.1) holds for (E_λ, μ_λ, ν_λ).
 (a) (1)–(2): ⨍_{B_ρ}ν^{n+1}dμ → 1 and ⨍_{B_ρ}|ν^i|dμ → 0 for i ≤ n, as ρ ↓ 0.
 (b) (3)–(6): test (4.1) with g = ζ_ke_{n+1}, where ζ_k are Lipschitz radial cut-offs decreasing to 1_{B̄_ρ}. This gives ∫_{B̄_ρ}ν^{n+1}dμ ≤ (d/dρ)L(E ∩ B_ρ) ≤ H^n(∂B_ρ) for a.e. small ρ. With (1), μ(B_ρ) ≤ 2(d/dρ)L(E ∩ B_ρ) ≤ 2(n+1)ω_{n+1}ρ^n for ρ < ρ₁, so μ_λ(B_R) ≤ cR^n.
 (c) (7): by the BV compactness theorem (Ch. 2, 2.6), along any λ_k ↓ 0 a subsequence has 1_{E_{λ_k}} → 1_F in L¹_loc, with F of locally finite perimeter.
 (d) (8)–(9): for ζ ∈ C_c^1 and i ≤ n, |∫_{E_λ}D_iζ| ≤ sup|ζ|·λ^{−n}∫_{B_{λR}}|ν^i|dμ → 0, so F = ℝ^n × H. For ζ ≥ 0, (4.1) and (1) give ∫_FD_{n+1}ζ = lim(−∫ζν_λ^{n+1}dμ_λ) ≤ 0. So 1_H is nondecreasing and F = {z^{n+1} > c} (erratum ii).
 (e) (10)–(11): apply the Sobolev inequality for BV functions (by mollification, Ch. 2, 2.5; Mathlib lintegral_pow_le_pow_lintegral_fderiv) to ζ1_E, using D(ζ1_E) = ζD1_E + 1_EDζ and (6). It gives V^{n/(n+1)} ≤ c·(d/dρ)V for V(ρ) := L(E ∩ B_ρ), which is positive because 0 ∈ spt μ. Integrating, L(E ∩ B_ρ) ≥ c'ρ^{n+1} for small ρ, and the same holds for the complement (normal −ν). These scale-invariant bounds pass to F and force c = 0. The limit is unique, so 1_{E_λ} → 1_{{z^{n+1} > 0}} in L¹_loc as λ ↓ 0. This is (‡).
 (f) (12): put P₀ := {z^{n+1} = 0} = ν_E(0)^⊥.
  - By (4.1) and L¹_loc convergence, ν_λμ_λ → e_{n+1}H^n⌞P₀ weakly.
  - Weak subsequential limits μ* of μ_λ exist by (6) and Ch. 1, 4.16, and H^n⌞P₀ ≤ μ*, since the variation of a weak limit is at most the limit of the variations.
  - Testing with ζe_{n+1}, 1_{B_R} ≤ ζ ≤ 1_{B_{R+ε}}, and using (1): ∫(1 − ν_λ^{n+1})dμ_λ → 0 on B_{R+ε}. So μ*(B_R) ≤ ω_nR^n = H^n⌞P₀(B_R).
  - Hence every subsequential limit is μ* = H^n⌞P₀ (4.3(†)). Every sequence λ_k ↓ 0 has a subsequence along which μ_{λ_k} converges, and all such limits agree. So ∫f dμ_λ → ∫_{P₀}f dH^n as λ ↓ 0, for every f ∈ C_c(ℝ^{n+1}).
5. (Rectifiable carrier and μ = H^n⌞B; the first sentence of the proof of 4.3.) Let G := {y ∈ ∂*E : ν_E(y) = ν(y)}; μ(ℝ^{n+1} ∖ G) = 0 by step 3.
 (a) Flat tangent measures. Let y ∈ G and f ∈ C_c(ℝ^{n+1}). Undo the rigid motion of step 4: Φ(z) := Q(z − y) with Q orthogonal and Qν(y) = e_{n+1}. Then ∫f dμ_λ in step 4 is λ^{−n}∫(f∘Q)(λ^{−1}(z − y))dμ(z). Also Q^{−1}P₀ = (span{ν(y)})^⊥, and H^n is invariant under orthogonal maps. So step 4(f), applied to f∘Q^{−1}, gives
  (FT) r^{−n}∫f(r^{−1}(z − y))dμ(z) → ∫_{(span{ν(y)})^⊥} f dH^n as r ↓ 0,
  for every y ∈ G, hence for μ-a.e. y, and for every continuous compactly supported f.
 (b) Apply measure_eq_hausdorff with m := n ≥ 1, D := ℝ^{n+1} (open), and μ, ν from step 1. Its hypotheses:
  - μ(ℝ^{n+1} ∖ D) = μ(∅) = 0, and μ(K) < ∞ for every compact K (step 1);
  - ν is Borel with |ν(y)| = 1 for every y (step 1);
  - (FT) holds for μ-a.e. y and every continuous compactly supported f (step 5(a));
  - (RD): for every Borel countably n-rectifiable S ⊆ ℝ^{n+1} with H^n(S) < ∞, H^n(S ∩ B_t(w))/(ω_nt^n) → 1 as t ↓ 0 for H^n-a.e. w ∈ S. This is exactly rect_density_one with P := n + 1 and n := n (n ≥ 1).
  It gives a Borel, countably n-rectifiable B ⊆ ℝ^{n+1} with μ = H^n⌞B as measures. For H^n-a.e. y ∈ B, the approximate tangent space of B at y (Simon Ch. 3, 1.4) is (span{ν(y)})^⊥.
6. (Output.)
 - B is Borel and countably n-rectifiable, and H^n(B) = μ(ℝ^{n+1}) ≤ C₊ < ∞ by step 2(b).
 - ν is Borel and |ν(y)| = 1 for every y, in particular on B.
 - For H^n-a.e. y ∈ B, B has approximate tangent space (span{ν(y)})^⊥ at y (step 5).
 - Gauss–Green: by (4.1) and μ = H^n⌞B, ∫_E div φ dL = −∫⟨φ, ν⟩dμ = −∫_B⟨φ, ν⟩dH^n for every C¹ compactly supported φ.
 - (‡): choose a Borel N ⊇ ℝ^{n+1} ∖ G with μ(N) = 0. Then H^n(B ∩ N) = μ(N) = 0. Let y ∈ B ∖ N, so y ∈ G and ν_E(y) = ν(y). Step 4(e), transported back by the rigid motion (L is invariant under orthogonal maps, and B_ρ(0) is rotation invariant), gives L((E_{y,r} Δ {w : ⟨w, ν(y)⟩ > 0}) ∩ B_ρ(0)) → 0 as r ↓ 0, for every ρ ∈ ℝ (B_ρ(0) = ∅ if ρ ≤ 0). So this holds for H^n⌞B-a.e. y. ∎

## Key steps

1. gauss_green_measure gives μ and a unit Borel ν with ∫_E div φ = −∫⟨φ, ν⟩dμ; the perimeter bound gives μ(ℝ^{n+1}) ≤ max(C, 0).
2. Besicovitch differentiation: μ is carried by the reduced boundary ∂*E, where the normal averages converge to ν.
3. Blow-up at y ∈ ∂*E (printed 4.3 (1)–(12)): E_{y,λ} tends in L¹_loc to the half-space {⟨w, ν⟩ > 0} (‡), and λ^{−n}μ(y + λ·) → H^n⌞ν(y)^⊥ for the whole family λ ↓ 0.
4. measure_eq_hausdorff, with (RD) supplied by rect_density_one at P := n + 1, turns these flat tangent measures into a Borel countably n-rectifiable B with μ = H^n⌞B and approximate tangent planes ν^⊥ a.e.; no step uses μ = H^n⌞B before it is obtained.
5. Output: H^n(B) = μ(ℝ^{n+1}) < ∞, the Gauss–Green formula over B, and (‡) at H^n⌞B-a.e. point.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); sha256sum snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (both e4148e7f…)`
- `rg -n 'BoundaryRectifiability|FedererFleming|CompactnessTheorem|DeGiorgi|IsoperimetricTheorem|RectifiabilityTheorem' project/GMT -g '*.lean' (only sorry-based contract definitions in GMT/Ch06 and GMT/Ch08, namespaces GMT.Ch06/GMT.Ch08, not importable from GMT.Ch07); rg -n 'closure|De Giorgi|reduced boundary|slice' project/GMT/Ch07 (only topological closure in definitions; no closure, slicing or De Giorgi theorem)`
- `sed -n 321,345p project/GMT/Ch06/Contract.lean (BoundaryRectifiability, FlatConvergenceIffWeakConvergence, RectifiabilityTheorem: formulation reference only)`
- `rg in snapshot mathlib: 'theorem ae_tendsto_average ' (Covering/Differentiation.lean:855), 'theorem ae_tendsto_rnDeriv' (Differentiation.lean:657), 'lintegral_pow_le_pow_lintegral_fderiv' (FunctionalSpaces/SobolevInequality.lean:371), 'ae_eq_zero_of_integral_contDiff_smul_eq_zero' (Distribution/AEEqOfIntegralContDiff.lean:186), 'euclideanHausdorffMeasure_eq_volume' (Geometry/Euclidean/Volume/Measure.lean:187), 'theorem integral_tsum' (Integral/DominatedConvergence.lean:88), 'exists_disjoint_subfamily_covering_enlargement_closedBall' (Covering/Vitali.lean:158), 'theorem exists_dense_seq' (Topology/Bases.lean:364), 'tendsto_inv_nat_nhds_zero' (Topology/Instances/ENNReal/Lemmas.lean:486)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,FormSupNorm,Forms}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn, TestFormOn, boundary_apply, boundary_boundary, exteriorDerivative_sq, massAdmissibleOn, massOn, mass, le_massOn, massOn_le_liminf, covectorEuclideanNorm (no smul/bound lemma), testFormEuclideanSupNorm, HasApproximateTangentSpaceAt (blow-up integral definition); no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem`
- `python3 -I scans of dag.json (1615 nodes): accepted codim1_rdo_dg_* De Giorgi helpers (measure_eq_hausdorff, rectifiable_of_flat_tangent, flat_tangent_density_cone, normal_average_ae, cutoff_estimates, gauss_green_measure, ...) and codim1_rdo_rectifiable_ae_density_one; non-accepted codim1_rdo_de_giorgi_gauss_green, tangent_measure_ae, blowup_halfspace, volume_density_lower, cmc_closure_and_boundary_rectifiability with cbr_* children, dtc_bc_tc_closure, cmc_deformation_theorem; accepted cbr_isoperimetric_filling (conditional on cmc_deformation_theorem); statement of the deformation sibling dtc_bc_lc_fd_deformation; collision check of dtc_bc_lc_fd_bim_* (only in this node's decomposition-v1.json)`
- `cat nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json} (rejected v1 and its required changes)`
- `python3 -I /tmp/bim_v2_scripts/reuse_check.py: git show <commit>:GMT/Ch07/Submission.lean for 3632b24, be5e512, 44ef61f, cfaa429, 8380287, 2af75d6, d1641e8, 3450f10 (whitespace-normalised types identical to dag.json; only sorry = main_theorem; no axiom/opaque); git show <commit>:GMT/Ch07/Contract.lean | sha256sum (all e4148e7f…); comparator-v1.log and isolated-comparator-result.json of the two new reuses ('Your solution is okay!', passed)`
- `git show 3632b24 / be5e512 :GMT/Ch07/Submission.lean | grep helpers cited by the reused proofs (codim1_rdo_dg_flat_tangent_density_cone, codim1_rdo_dg_rectifiable_of_flat_tangent; regcomp_atl_upper_density_zero, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall): all present and accepted; git log --all -S 'dtc_bc_lc_fd_bim_' (no hit)`
- `lake env lean /tmp/bim_v2_check/Challenges.lean (12 targets in comparator challenge form after the gmt-compare.py contract_scope replay: exit 0, 12 sorry warnings only)`
- `lake env lean /tmp/bim_v2_check/AllChecks.lean (stubs; sorry-free bim_* helper lemmas; node_assembly; de_giorgi_from_children; closure_cycles_from_general; #print axioms)`
- `sed book/chapter-06.txt lines 440-660 (2.23-2.37), 725-960 (3.1-3.15), 1150-1420 (4.1-4.11), 1425-1500 (5.1-5.4), 1925-2160 (6.1-8.1), 2160-2296 (8.1 proof), 2290-2473 (8.2-8.3); chapter-01.txt 596-612, 800-830, 1745-1800 (3.3, 3.12, 4.16); chapter-03.txt 551-746 (4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/bim_v2_check/Challenges.lean`
- `/tmp/bim_v2_check/AllChecks.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the workspace, and the snapshot and workspace GMT/Ch07/Contract.lean are byte-identical (sha256 e4148e7f…). The pinned project proves no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem usable from GMT.Ch07. GMT/Ch06 and GMT/Ch08 only state them as sorry-based contract definitions in other namespaces; they served as formulation references. SimonGMT provides currents, boundary, massOn/mass (Euclidean coefficient norm), le_massOn, massOn_le_liminf, support and HasApproximateTangentSpaceAt, but no bound for covectorEuclideanNorm; the needed homogeneity and operator-norm bounds were proved in the scratch check. Snapshot Mathlib supplies the measure-theory tools cited in the child proofs (Besicovitch/Vitali differentiation, GNS inequality, fundamental lemma, μHE = volume, integral_tsum, separability). In the DAG, the De Giorgi parent codim1_rdo_de_giorgi_gauss_green and the closure theorems are not accepted. The accepted codim1_rdo_dg_measure_eq_hausdorff and codim1_rdo_rectifiable_ae_density_one close the rejected de_giorgi step 6: types identical in commits 3632b24 and be5e512, comparators passed, helpers contained. They are reused together with the six v1 reuses. All eight reused types are identical in their accepted commits, those commits' contracts are byte-identical, and they contain no extra sorry or axioms. The four new names are unreserved and the dependencies are acyclic. Lean: all 12 child types elaborate in challenge form. The parent's frozen type is proved from the 12 child stubs plus the deformation sibling, with the inline weak-limit step proved sorry-free (propext, Classical.choice, Quot.sound). de_giorgi's type is assembled from the three reused De Giorgi lemmas, and closure_cycles follows from the cousin dtc_bc_tc_closure's type.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
