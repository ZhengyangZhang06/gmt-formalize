<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_ae_approx-a1 -->

## Theorem `Submission.cbr_ci_pw_bv_smooth_ae_approx`

Let n ∈ ℕ and R, δ ∈ ℝ with δ > 0 (ℝⁿ = Euclid n with Lebesgue measure), and let g₀ : ℝⁿ → ℝ be measurable with |g₀(x)| ≤ 1 for all x and g₀(x) = 0 whenever ‖x‖ ≥ R. Then there is a sequence (G_j)_{j∈ℕ} of functions ℝⁿ → ℝ such that every G_j is smooth (C^∞) with compact support, tsupport G_j ⊆ B_{R+δ}(0), |G_j(x)| ≤ 1 for all j and x, and G_j(x) → g₀(x) as j → ∞ for Lebesgue-almost every x ∈ ℝⁿ.

Node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_ae_approx-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6198

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.cbr_ci_pw_bv_smooth_ae_approx`

```lean
∀ (n : ℕ) (R δ : ℝ) (g₀ : Euclid n → ℝ), 0 < δ → Measurable g₀ → (∀ x, |g₀ x| ≤ 1) → (∀ x, R ≤ ‖x‖ → g₀ x = 0) → ∃ G : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧ (∀ j, tsupport (G j) ⊆ ball 0 (R + δ)) ∧ (∀ j x, |G j x| ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun j => G j x) atTop (𝓝 (g₀ x))
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_ae_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent proof (mollify the bounded function g₀ by rescaled normalized smooth bumps ψ_ϑ; the mollifications are smooth, bounded by ∫ψ_ϑ = 1, supported in a slightly larger ball, and converge to g₀ at Lebesgue points), for an arbitrary measurable g₀ with |g₀| ≤ 1 vanishing off B_R(0), with the explicit radii θ_j := δ/(j + 2). No assumption on n is needed (n = 0 included).
0. (Integrability of g₀.) If x ∉ B_R(0) then ‖x‖ ≥ R, so g₀(x) = 0. On B_R(0), a set of finite measure, g₀ is measurable and bounded by 1, hence integrable (Measure.integrableOn_of_bounded); its support lies in B_R(0), so g₀ is integrable on ℝⁿ (integrableOn_iff_integrable_of_support_subset), in particular locally integrable.
1. (A normalized bump.) Let b be the ContDiffBump centred at 0 with rIn = 1/4 and rOut = 1/2 (ℝⁿ is finite-dimensional, so Mathlib provides HasContDiffBump). Then b is C^∞, 0 ≤ b ≤ 1, support b = B_{1/2}(0), and b has compact support, hence is integrable. I := ∫ b > 0 by integral_pos_iff_support_of_nonneg, because support b is a nonempty open ball, which has positive measure (measure_ball_pos). Put ρ := b/I. Then ρ is C^∞, 0 ≤ ρ ≤ 1/I, ρ(x) = 0 whenever ‖x‖ ≥ 1/2, and ∫ρ = I/I = 1.
2. (Rescaled mollifiers.) For ε > 0 put ψ_ε(x) := (εⁿ)⁻¹·ρ(ε⁻¹x). Then ψ_ε is C^∞ (a constant times ρ composed with the linear map x ↦ ε⁻¹x); ψ_ε ≥ 0; ψ_ε(x) = 0 whenever ‖x‖ ≥ ε/2 (then ‖ε⁻¹x‖ = ε⁻¹‖x‖ ≥ 1/2); |ψ_ε(x)| ≤ (1/I)/εⁿ; ψ_ε has compact support (it vanishes outside closedBall(0, ε)); and ∫ψ_ε = (εⁿ)⁻¹·εⁿ·∫ρ = 1 by the scaling law ∫ f(ε⁻¹x) dx = ε^{dim ℝⁿ}·∫f (Measure.integral_comp_inv_smul_of_nonneg) with dim ℝⁿ = n (finrank_euclideanSpace_fin). In particular ψ_ε is integrable and ∫ ψ_ε(x − y) dy = ∫ψ_ε = 1 for every x (integral_sub_left_eq_self).
3. (The sequence.) θ_j := δ/(j + 2) satisfies 0 < θ_j < δ (as j + 2 ≥ 2 > 1) and θ_j → 0. Define G_j := g₀ ⋆ ψ_{θ_j}, the convolution with respect to the bilinear map ContinuousLinearMap.lsmul ℝ ℝ and Lebesgue measure, so that G_j(x) = ∫ g₀(y)·ψ_{θ_j}(x − y) dy (convolution_def).
4. (Smoothness.) ψ_{θ_j} is C^∞ with compact support and g₀ is locally integrable, so G_j is C^∞ (HasCompactSupport.contDiff_convolution_right).
5. (Support.) Let ‖x‖ ≥ R + θ_j/2. For each y, either ‖y‖ ≥ R, so g₀(y) = 0, or ‖y‖ < R, so ‖x − y‖ ≥ ‖x‖ − ‖y‖ > θ_j/2 and ψ_{θ_j}(x − y) = 0. Thus the integrand vanishes identically and G_j(x) = 0. Hence support G_j ⊆ closedBall(0, R + θ_j/2), which is compact, so G_j has compact support; and since this closed ball is closed, tsupport G_j ⊆ closedBall(0, R + θ_j/2) ⊆ B_{R+δ}(0) because θ_j/2 < δ.
6. (Uniform bound.) |G_j(x)| ≤ ∫ |g₀(y)·ψ_{θ_j}(x − y)| dy ≤ ∫ ψ_{θ_j}(x − y) dy = 1, using |g₀| ≤ 1, ψ_{θ_j} ≥ 0, integrability of y ↦ ψ_{θ_j}(x − y) (Integrable.comp_sub_left) and step 2.
7. (Convergence at Lebesgue points.) Lebesgue measure on ℝⁿ is uniformly locally doubling (Mathlib instance for additive Haar measures on finite-dimensional spaces). By the Lebesgue differentiation theorem in the form IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (for the locally integrable g₀, with K = 1), for a.e. x: for every sequence of radii r_j → 0 through positive values and centres c_j with x ∈ closedBall(c_j, r_j), the averages ⨍_{closedBall(c_j, r_j)} |g₀(y) − g₀(x)| dy tend to 0. Fix such an x and use c_j := x, r_j := θ_j. Apply the approximate-identity lemma tendsto_integral_smul_of_tendsto_average_norm_sub with sets a_j := closedBall(x, θ_j), kernels k_j(y) := ψ_{θ_j}(x − y) and constant K₀ := (1/I)·|closedBall(0, 1)|, checking its hypotheses for every j:
   (a) ⨍_{a_j} |g₀ − g₀(x)| → 0 (just shown);
   (b) g₀ is integrable on a_j;
   (c) ∫ k_j = 1 (step 2), so ∫ k_j → 1;
   (d) support k_j ⊆ a_j, because k_j(y) ≠ 0 forces ‖x − y‖ < θ_j/2 ≤ θ_j;
   (e) |k_j(y)| ≤ (1/I)/θ_jⁿ = K₀/|closedBall(x, θ_j)|, because |closedBall(x, r)| = rⁿ·|closedBall(0, 1)| for r ≥ 0 (Measure.addHaar_real_closedBall' with dim ℝⁿ = n) and 0 < |closedBall(0, 1)| < ∞.
   The lemma gives ∫ k_j(y)·g₀(y) dy → g₀(x), i.e. G_j(x) → g₀(x). As this holds for a.e. x, the sequence (G_j) has all the required properties. ∎

Verified Lean realization (supplementary; compiled with `lake env lean` inside a copy of GMT/Ch07/Submission.lean at project b4d606db / Mathlib 25730c7c, inserted before `main_theorem`; no new warnings; axioms propext, Classical.choice, Quot.sound). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.cbr_ci_pw_bv_smooth_ae_approx : ∀ (n : ℕ) (R δ : ℝ) (g₀ : Euclid n → ℝ), 0 < δ → Measurable g₀ → (∀ x, |g₀ x| ≤ 1) → (∀ x, R ≤ ‖x‖ → g₀ x = 0) → ∃ G : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧ (∀ j, tsupport (G j) ⊆ ball 0 (R + δ)) ∧ (∀ j x, |G j x| ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun j => G j x) atTop (𝓝 (g₀ x)) := by
  intro n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 0: g₀ is integrable
  have hg₀out : ∀ x, x ∉ ball (0 : Euclid n) R → g₀ x = 0 := fun x hx =>
    hg₀z x (by simpa [mem_ball_zero_iff] using hx)
  have hg₀i : Integrable g₀ := by
    have hon : IntegrableOn g₀ (ball (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne hg₀m.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg₀b x)
    exact (integrableOn_iff_integrable_of_support_subset
      (fun x hx => by by_contra h; exact hx (hg₀out x h))).1 hon
  -- Step 1: a normalized bump
  let b : ContDiffBump (0 : Euclid n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbi : Integrable (b : Euclid n → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  set I : ℝ := ∫ x, b x with hIdef
  have hI : 0 < I := by
    rw [hIdef, integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbi, b.support_eq]
    exact measure_ball_pos _ _ (by norm_num)
  set ρ : Euclid n → ℝ := fun x => b x / I with hρdef
  have hρc : ContDiff ℝ (⊤ : ℕ∞) ρ := b.contDiff.div_const I
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => div_nonneg b.nonneg hI.le
  have hρb : ∀ x, ρ x ≤ 1 / I := fun x => div_le_div_of_nonneg_right b.le_one hI.le
  have hρz : ∀ x, (1 / 2 : ℝ) ≤ ‖x‖ → ρ x = 0 := by
    intro x hx
    have : x ∉ support (b : Euclid n → ℝ) := by
      rw [b.support_eq, mem_ball_zero_iff]; exact not_lt.2 hx
    simp [hρdef, notMem_support.1 this]
  have hρ1 : ∫ x, ρ x = 1 := by
    simp only [hρdef]; rw [integral_div, ← hIdef, div_self hI.ne']
  -- Step 2: rescaled mollifiers
  set ψ : ℝ → Euclid n → ℝ := fun ε x => (ε ^ n)⁻¹ * ρ (ε⁻¹ • x) with hψdef
  have hψc : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (ψ ε) := fun ε =>
    contDiff_const.mul (hρc.comp (contDiff_const_smul ε⁻¹))
  have hψ0 : ∀ ε, 0 < ε → ∀ x, 0 ≤ ψ ε x := fun ε hε x =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le n)) (hρ0 _)
  have hψz : ∀ ε, 0 < ε → ∀ x, ε / 2 ≤ ‖x‖ → ψ ε x = 0 := by
    intro ε hε x hx
    have : (1 / 2 : ℝ) ≤ ‖ε⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      rw [le_inv_mul_iff₀ hε]; linarith
    simp [hψdef, hρz _ this]
  have hψb : ∀ ε, 0 < ε → ∀ x, |ψ ε x| ≤ (1 / I) / ε ^ n := by
    intro ε hε x
    rw [abs_of_nonneg (hψ0 ε hε x), hψdef]
    simp only
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hρb _) (inv_nonneg.2 (pow_nonneg hε.le n))
  have hψ1 : ∀ ε, 0 < ε → ∫ x, ψ ε x = 1 := by
    intro ε hε
    simp only [hψdef]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg _ _ hε.le,
      finrank_euclideanSpace_fin, hρ1, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero n hε.ne')]
  have hψcs : ∀ ε, 0 < ε → HasCompactSupport (ψ ε) := by
    intro ε hε
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hψz ε hε x (by linarith)
  -- Step 3: the sequence
  set θ : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hθdef
  have hθpos : ∀ j, 0 < θ j := fun j => div_pos hδ (by positivity)
  have hθlt : ∀ j, θ j < δ := fun j => by
    rw [hθdef]; simp only
    rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hG : ∀ j x, convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = ∫ y, g₀ y * ψ (θ j) (x - y) := by
    intro j x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvan : ∀ j x, R + θ j / 2 ≤ ‖x‖ →
      convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro j x hx
    rw [hG]
    have : (fun y => g₀ y * ψ (θ j) (x - y)) = fun _ => 0 := by
      funext y
      by_cases hy : R ≤ ‖y‖
      · rw [hg₀z y hy, zero_mul]
      · push Not at hy
        have h1 : θ j / 2 ≤ ‖x - y‖ := by
          have := norm_sub_norm_le x y
          linarith
        rw [hψz (θ j) (hθpos j) _ h1, mul_zero]
    rw [this, integral_zero]
  have hsupp : ∀ j, support (convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ closedBall 0 (R + θ j / 2) := by
    intro j x hx
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hx (hvan j x (not_le.1 h).le)
  refine ⟨fun j => convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hψcs (θ j) (hθpos j)).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hg₀i.locallyIntegrable (hψc (θ j))
  · intro j
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp j)
  · intro j
    refine (closure_minimal (hsupp j) isClosed_closedBall).trans (closedBall_subset_ball ?_)
    linarith [hθlt j, hθpos j]
  · intro j x
    simp only
    rw [hG]
    have hψi : Integrable (ψ (θ j)) :=
      (hψc (θ j)).continuous.integrable_of_hasCompactSupport (hψcs (θ j) (hθpos j))
    calc |∫ y, g₀ y * ψ (θ j) (x - y)| ≤ ∫ y, |g₀ y * ψ (θ j) (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, ψ (θ j) (x - y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hψi.comp_sub_left x) (Eventually.of_forall fun y => ?_)
          show |g₀ y * ψ (θ j) (x - y)| ≤ ψ (θ j) (x - y)
          rw [abs_mul, abs_of_nonneg (hψ0 _ (hθpos j) _)]
          exact mul_le_of_le_one_left (hψ0 _ (hθpos j) _) (hg₀b y)
      _ = 1 := by rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)]
  · have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) hg₀i.locallyIntegrable 1
    filter_upwards [hleb] with x hx
    have hθ0 : Tendsto θ atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [hθdef] using this.const_div_atTop δ
    have hθ : Tendsto θ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hθ0
        (Eventually.of_forall fun j => hθpos j)
    have havg := hx (fun _ => x) θ hθ
      (Eventually.of_forall fun j => mem_closedBall_self (by simpa using (hθpos j).le))
    have hB1 : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
    have key := tendsto_integral_smul_of_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) (f := g₀) (c := g₀ x)
      (a := fun j => closedBall x (θ j)) (g := fun j y => ψ (θ j) (x - y))
      ((1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1)) havg
      (Eventually.of_forall fun j => hg₀i.integrableOn)
      (by
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
        simp only
        rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)])
      (Eventually.of_forall fun j y hy => by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        by_contra h
        exact hy (hψz _ (hθpos j) _ (by linarith [hθpos j])))
      (Eventually.of_forall fun j y => by
        rw [Measure.addHaar_real_closedBall' _ _ (hθpos j).le, finrank_euclideanSpace_fin]
        have hpow : 0 < θ j ^ n := pow_pos (hθpos j) n
        calc |ψ (θ j) (x - y)| ≤ (1 / I) / θ j ^ n := hψb _ (hθpos j) _
          _ = (1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1) /
              (θ j ^ n * (volume : Measure (Euclid n)).real (closedBall 0 1)) := by
            field_simp)
    refine key.congr' (Eventually.of_forall fun j => ?_)
    simp only
    rw [hG]
    congr 1; funext y
    rw [smul_eq_mul, mul_comm]
```

## Key steps

1. g₀ is integrable: measurable, |g₀| ≤ 1, and g₀ = 0 off B_R(0).
2. Normalized bump ρ = b/∫b (ContDiffBump with radii 1/4, 1/2): C^∞, 0 ≤ ρ ≤ 1/I, ρ = 0 for ‖x‖ ≥ 1/2, ∫ρ = 1; rescalings ψ_ε(x) = ε^{−n}ρ(x/ε) have ∫ψ_ε = 1, vanish for ‖x‖ ≥ ε/2 and satisfy |ψ_ε| ≤ (1/I)ε^{−n}.
3. G_j := g₀ ⋆ ψ_{θ_j} with θ_j = δ/(j + 2): C^∞ (convolution with a smooth compactly supported kernel), |G_j| ≤ ∫ψ = 1, support in closedBall(0, R + θ_j/2) so tsupport G_j ⊆ B_{R+δ}(0).
4. Lebesgue differentiation for the doubling Lebesgue measure plus the approximate-identity lemma give G_j(x) → g₀(x) for a.e. x.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical; workspace HEAD b4d606db)`
- `rg -n 'cbr_ci_pw_bv|mollif|convolution|ae_tendsto_average|l1_duality' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT (no match)`
- `grep -rn in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/ for: 'theorem tendsto_integral_smul_of_tendsto_average_norm_sub' (MeasureTheory/Integral/Average.lean:835), 'theorem ae_tendsto_average_norm_sub' (MeasureTheory/Covering/DensityTheorem.lean:150; Covering/Differentiation.lean:837), 'HasCompactSupport.contDiff_convolution_right' (Analysis/Calculus/ContDiff/Convolution.lean:420), 'intervalIntegral_integral_swap' (MeasureTheory/Integral/Prod.lean:483), 'theorem integral_integral_swap' (Integral/Prod.lean:478), 'theorem Integrable.mul_prod' (Integral/Prod.lean:297), 'AEStronglyMeasurable.comp_snd' (Integral/Prod.lean:135), 'lemma Integrable.comp_snd' (Integral/Prod.lean:285), 'theorem continuous_of_dominated' (Integral/Bochner/Basic.lean:476), 'theorem integral_comp_inv_smul_of_nonneg' (Measure/Haar/NormedSpace.lean:129), "theorem addHaar_real_closedBall'" (Measure/Lebesgue/EqHaar.lean:479; IsUnifLocDoublingMeasure instance for Haar measures at EqHaar.lean:551), 'theorem fderiv_comp_add_right' (Analysis/Calculus/FDeriv/Add.lean:855), 'theorem norm_integral_le_of_norm_le_const' (IntervalIntegral/Basic.lean:769), 'theorem tendsto_integral_of_dominated_convergence' (Integral/DominatedConvergence.lean:57), 'theorem integral_eq_sub_of_hasDerivAt' (IntervalIntegral/FundThmCalculus.lean:1148), 'theorem integral_pos_iff_support_of_nonneg' (Bochner/Basic.lean:790), 'theorem support_eq' (Analysis/Calculus/BumpFunction/Basic.lean:151), 'theorem integrableOn_iff_integrable_of_support_subset' (Integral/IntegrableOn.lean:462), 'Measure.integrableOn_of_bounded' (Integral/IntegrableOn.lean:716), 'theorem setIntegral_indicator' (Integral/Bochner/Set.lean:194), 'theorem norm_integral_le_of_norm_le' (Bochner/Basic.lean:985)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: no lean_name with prefix cbr_ci_pw_bv_ except the selected cbr_ci_pw_bv_mollifier_estimate (rechecked immediately before returning); keyword scan (mollif|dualit|Lebesgue point|convolution|translation) of accepted nodes; frozen types of codim1_rdo_dg_bvc_l1_le_of_tests, codim1_rdo_dg_bvc_translate_test_le, codim1_rdo_dg_bvc_translation_l1_le, codim1_rdo_dg_bvc_mollify_l1_le, dorag_ha_weyl_ae_tendsto, dorag_ha_weyl_radial_mollifier, dgcr_stc_exists_normalized_mollifier compared with the needed obligations (none identical)`
- `git show f471edcde (dorag_ha_weyl_ae_tendsto), 376e5f482 (dgcr_stc_exists_normalized_mollifier), bfd6db12d (codim1_rdo_dg_bvc_mollify_l1_le), 499364f8f (codim1_rdo_dg_bvc_l1_le_of_tests), e2ca2a5c7 (codim1_rdo_dg_bvc_translate_test_le) as proof templates`
- `lake env lean /tmp/bvdec/T0.lean and T1.lean (#check after import GMT.Ch07.Submission: all cited lemmas reachable; Real.sign and measurable_sign NOT reachable, so the sign function is an if-then-else; IsUnifLocDoublingMeasure (volume : Measure (Euclid n)) synthesizes for every n)`
- `lake env lean /tmp/bvdec/Stmts.lean (six child types elaborate; parent assembly compiles against them), /tmp/bvdec/AsmAD.lean (smooth_test_bound from pairing_identity + translate_test; l1_duality from smooth_ae_approx), /tmp/bvdec/C.lean, T.lean, A1.lean, M.lean (complete leaf proofs), /tmp/bvdec/SubmissionCopy.lean (all six children plus the parent inserted before main_theorem in a copy of GMT/Ch07/Submission.lean: only the inherited main_theorem sorry warning; #print axioms Submission.cbr_ci_pw_bv_mollifier_estimate = [propext, Classical.choice, Quot.sound])`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the six child types (all pass, normalized text unchanged); regex check that each frozen type is byte-identical to the compiled declaration`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: max_depth, _existing_lean_name_problem, _solve_children, _reference_use_problem), leaf_verification.py check_source_delta (one appended theorem, no helper declarations or set_option), prompts.py DECOMPOSITION_AUDIT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Doubling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bvdec/Stmts.lean`
- `/tmp/bvdec/AsmAD.lean`
- `/tmp/bvdec/SubmissionCopy.lean`

The pinned snapshot (local-project; project b4d606db, Mathlib 25730c7c) has Contract.lean byte-identical to the workspace Contract.lean and Submission.lean, and the project contains no mollification, convolution, duality or Lebesgue-point declaration (rg: no match), so the children rely only on pinned Mathlib. Every Mathlib lemma named in the child proofs was located in the snapshot (paths and lines above) and is reachable from import GMT.Ch07.Submission; Real.sign is not imported and is avoided. No DAG node uses a cbr_ci_pw_bv_* name other than the selected one, so the six names are fresh. Related accepted DAG theorems have different frozen types (codim1_rdo_dg_bvc_l1_le_of_tests needs a bounded measurable integrand and C¹ tests, but u − w is unbounded and only smooth tests are controlled; dorag_ha_weyl_ae_tendsto needs 0 < n), so nothing is reused and the children have no cross-branch dependencies; their accepted proofs were used only as templates. All six child types elaborate in the contract scope and pass validate_lean_statement. Complete Lean proofs of all six, plus the parent proof from mollify_continuous, smooth_test_bound and l1_duality, compile inside a copy of GMT/Ch07/Submission.lean with no new warnings. The parent depends only on propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
