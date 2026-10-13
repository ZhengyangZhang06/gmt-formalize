<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1.whitney_extension-a1 -->

## Theorem `Submission.codim1_rdo_c1a_whitney_extension`

Let n ∈ ℕ and ℝ^n = Euclid n. Let A ⊆ ℝ^n be closed, and let h : ℝ^n → ℝ and D : ℝ^n → (ℝ^n →L[ℝ] ℝ) (continuous linear functionals) be continuous on A; their values off A are irrelevant. Assume Whitney's condition 1.6(∗) in compact-uniform form: for every compact Q ⊆ A and every real ε > 0 there is δ > 0 such that |h(y) − h(x) − D(x)(y − x)| ≤ ε|y − x| for all x ∈ Q and y ∈ A with |x − y| < δ. Then there is g : ℝ^n → ℝ of class C¹ (ContDiff ℝ 1 g) with g = h on A (EqOn g h A) and with Fréchet derivative D(a) at every a ∈ A (HasFDerivAt g (D a) a).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1.whitney_extension-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5092

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_rdo_c1a_whitney_extension`

```lean
∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1.whitney_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source.
- Simon Ch. 2, Theorem 1.6 (chapter-02.txt lines 173–186) states this theorem but prints no proof. Line 186 says 'For the proof see for example [EG92] or [Fed69]', and Remark 1.7(2) treats only n = 1. There is therefore no printed proof to copy.
- The proof below is the standard Whitney-decomposition argument of the cited [EG92] (Evans–Gariepy, Measure Theory and Fine Properties of Functions, §6.5).
- It is given in exactly the form already kernel-checked in the pinned SimonGMT files Chapter02/WhitneyCover.lean, WhitneyPartition.lean, WhitneyJet.lean and WhitneyExtension.lean (theorem exists_contDiff_one_extension_of_whitney). Its hypothesis HasWhitneyC1Compatibility A h D has exactly the three hypotheses above as its fields.
Notation: |·| is the Euclidean norm, ‖·‖ the operator norm on (ℝ^n)*, B(x,r) the open ball, B̄(x,r) the closed ball, d(x) := dist(x, A).

0. (Trivial case and the radius function.) If A = ∅, take g := 0: it is C¹ and the other two conclusions are vacuous. Assume A ≠ ∅, and put r(x) := min(1, d(x))/100.
- d is 1-Lipschitz, so |r(x) − r(y)| ≤ |x − y|/100.
- 0 ≤ r ≤ 1/100 and 100 r(x) ≤ d(x).
- r(x) > 0 exactly when x ∉ A, since A is closed.

1. (Affine jets.) For b ∈ ℝ^n let P_b(x) := h(b) + D(b)(x − b). P_b is affine, hence C^∞, with derivative D(b) at every point, and P_b(b) = h(b). For all a, b, x,
 P_b(x) − P_a(x) = [h(b) − h(a) − D(a)(b − a)] + (D(b) − D(a))(x − b),
so |P_b(x) − P_a(x)| ≤ |h(b) − h(a) − D(a)(b − a)| + ‖D(b) − D(a)‖·|x − b|.

2. (Local uniform estimate.) Let a ∈ A and η > 0. Then there is δ ∈ (0, 1] such that
 (i) ‖D(b) − D(a)‖ ≤ η for all b ∈ A with |b − a| < δ, and
 (ii) |h(c) − h(b) − D(b)(c − b)| ≤ η|c − b| for all b, c ∈ A with |b − a| < δ and |c − a| < δ.
Proof:
- Q := A ∩ B̄(a, 1) is compact (closed and bounded in ℝ^n), so the hypothesis gives r₀ > 0 for Q and η.
- Continuity of D on A at a gives η₀ > 0 with ‖D(b) − D(a)‖ < η for b ∈ A, |b − a| < η₀.
- Take δ := min(1, η₀, r₀/3); (i) holds by the choice of η₀.
- For (ii): b ∈ Q because |b − a| < δ ≤ 1, and |b − c| < 2δ < r₀. So the hypothesis applies with x = b, y = c.

3. (Nearest points.) A is closed and nonempty and ℝ^n is proper, so every x has a nearest point π(x) ∈ A with |x − π(x)| = d(x).
- For b ∈ A: |π(x) − b| ≤ |π(x) − x| + |x − b| ≤ 2|x − b|.
- For a ∈ A: π(a) = a.

4. (Whitney balls.) Apply the Vitali covering lemma (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_ball, τ = 4) to the balls B(x, r(x)), x ∈ ℝ^n ∖ A, whose radii are ≤ 1/100. It gives a set Z ⊆ ℝ^n ∖ A of centres such that:
- the balls B(c, r(c)), c ∈ Z, are pairwise disjoint;
- every x ∉ A satisfies |x − c| < 4r(c) for some c ∈ Z.

5. (Comparability and bounded overlap.) For x ∉ A let Z_x := {c ∈ Z : |x − c| ≤ r(x) + 10 r(c)}.
 (a) If c ∈ Z_x, then r(x)/2 ≤ r(c) ≤ 2r(x) and |x − c| ≤ 21 r(x). This follows from |r(x) − r(c)| ≤ |x − c|/100 ≤ (r(x) + 10 r(c))/100.
 (b) There is N ∈ ℕ, depending only on n, with #Z_x ≤ N for every x ∉ A.
 - The map c ↦ (c − x)/r(x) is injective and sends Z_x into B̄(0, 21).
 - Distinct c, c' ∈ Z satisfy |c − c'| ≥ r(c); otherwise c' ∈ B(c, r(c)) ∩ B(c', r(c')), contradicting disjointness.
 - With (a), the images of distinct elements of Z_x are therefore at distance ≥ r(c)/r(x) ≥ 1/2.
 - Fix a finite 1/4-net of the totally bounded set B̄(0, 21), with N points. Assign to each image a net point within distance < 1/4. Two distinct images assigned the same net point would be at distance < 1/2, so the assignment is injective and #Z_x ≤ N.

6. (Bumps.) Fix ψ ∈ C^∞(ℝ^n) with 0 ≤ ψ ≤ 1, ψ = 1 on B̄(0, 4) and ψ = 0 outside B(0, 8) (Mathlib ContDiffBump with radii 4 < 8). ψ is C¹ with compact support, hence Λ-Lipschitz for some Λ. For c ∈ Z put φ_c(x) := ψ((x − c)/r(c)). Then:
- φ_c is C^∞ and 0 ≤ φ_c ≤ 1;
- φ_c = 1 on B̄(c, 4r(c)) and φ_c = 0 outside B(c, 8r(c));
- φ_c is (Λ/r(c))-Lipschitz, so ‖Dφ_c(x)‖ ≤ Λ/r(c) for all x.

7. (Local finiteness.) Let x ∉ A and |y − x| < r(x).
- y ∉ A, since r(x) ≤ d(x)/100 < d(x).
- If c ∈ Z ∖ Z_x, then |y − c| ≥ |x − c| − |y − x| > 10 r(c) ≥ 8 r(c), so φ_c(y) = 0.
- Hence on B(x, r(x)) the function S := Σ_{c∈Z} φ_c equals the finite sum Σ_{c∈Z_x} φ_c. So S is C^∞ on the open set ℝ^n ∖ A.
- S(x) ≥ 1 for x ∉ A: by step 4 pick c ∈ Z with |x − c| < 4r(c); then c ∈ Z_x and φ_c(x) = 1.

8. (Partition of unity.) For x ∉ A and c ∈ Z put w_c(x) := φ_c(x)/S(x).
- Each w_c is C^∞ on ℝ^n ∖ A, and 0 ≤ w_c ≤ 1.
- By step 7, Σ_{c∈Z_x} w_c(y) = 1 for |y − x| < r(x). Hence Σ_{c∈Z_x} Dw_c(x) = 0.
- Dw_c = Dφ_c/S − φ_c·DS/S², with S ≥ 1 and 0 ≤ φ_c ≤ 1. So ‖Dw_c(x)‖ ≤ ‖Dφ_c(x)‖ + ‖DS(x)‖.
- For c ∈ Z_x, ‖Dφ_c(x)‖ ≤ Λ/r(c) ≤ 2Λ/r(x) by 5(a). Since DS(x) = Σ_{c∈Z_x} Dφ_c(x), we get ‖DS(x)‖ ≤ 2NΛ/r(x).
Therefore Σ_{c∈Z_x} ‖Dw_c(x)‖ ≤ M/r(x), where M := 2Λ(N + 1)² does not depend on x.

9. (The extension.) For c ∈ Z let b_c := π(c) ∈ A. Define g(x) := h(x) for x ∈ A and g(x) := Σ_{c∈Z} w_c(x) P_{b_c}(x) for x ∉ A. By step 7, near each x ∉ A this is the finite sum Σ_{c∈Z_x} w_c P_{b_c}. Hence g = h on A, g is C^∞ on ℝ^n ∖ A, and for x ∉ A
 Dg(x) = Σ_{c∈Z_x} [w_c(x) D(b_c) + P_{b_c}(x) Dw_c(x)].

10. (Anchor distances.) Let x ∉ A and c ∈ Z_x.
- d(c) ≤ d(x) + |x − c|, and |x − c| ≤ 21 r(x) ≤ (21/100) d(x).
- So |x − b_c| ≤ |x − c| + d(c) ≤ 2|x − c| + d(x) ≤ 2 d(x).
- Consequently, for a ∈ A, using d(x) ≤ |x − a|: |x − b_c| ≤ 2|x − a| and |b_c − a| ≤ |b_c − x| + |x − a| ≤ 3|x − a|.

11. (Dg = D on A.) Let a ∈ A and ε > 0. Take δ from step 2 with η := ε/5, and let |x − a| < δ/4. We show |g(x) − g(a) − D(a)(x − a)| ≤ ε|x − a|. Since g(a) = h(a), the left side is |g(x) − P_a(x)|.
- If x ∈ A: by 2(ii) with b = a and c = x, |h(x) − h(a) − D(a)(x − a)| ≤ (ε/5)|x − a|.
- If x ∉ A: since Σ_{c∈Z_x} w_c(x) = 1, g(x) − P_a(x) = Σ_{c∈Z_x} w_c(x)(P_{b_c}(x) − P_a(x)).
 - For c ∈ Z_x, step 10 gives |b_c − a| ≤ 3|x − a| < δ and |x − b_c| ≤ 2|x − a|.
 - Step 1 with step 2 ((ii) for b = a, c = b_c; (i) for b = b_c) gives |P_{b_c}(x) − P_a(x)| ≤ (ε/5)|b_c − a| + (ε/5)|x − b_c| ≤ (ε/5)(3 + 2)|x − a| = ε|x − a|.
 - A convex combination of numbers of absolute value ≤ ε|x − a| has absolute value ≤ ε|x − a|.
Hence g has Fréchet derivative D(a) at a (HasFDerivAt g (D a) a). With step 9, g is differentiable everywhere, Dg = D on A, and Dg is continuous at every point of the open set ℝ^n ∖ A.

12. (Dg is continuous at points of A.) Let a ∈ A and ε > 0. Put η := ε/(2(1 + 700M)), take δ ∈ (0, 1] from step 2 for this η, and let |x − a| < δ/4.
- If x ∈ A: by step 11 and 2(i), ‖Dg(x) − Dg(a)‖ = ‖D(x) − D(a)‖ ≤ η ≤ ε/2.
- If x ∉ A: let b := π(x), so |x − b| = d(x) ≤ |x − a| and |b − a| ≤ 2|x − a| < δ. Since Σ_{c∈Z_x} w_c(x) = 1 and Σ_{c∈Z_x} Dw_c(x) = 0, step 9 gives
 Dg(x) − D(a) = Σ_{c∈Z_x} w_c(x)(D(b_c) − D(a)) + Σ_{c∈Z_x} (P_{b_c}(x) − P_b(x)) Dw_c(x).
 - First sum: for c ∈ Z_x, |b_c − a| ≤ 3|x − a| < δ, so ‖D(b_c) − D(a)‖ ≤ η by 2(i). Being a convex combination, the first sum has norm ≤ η.
 - Second sum: d(x) ≤ |x − a| < 1/4, so r(x) = d(x)/100. For c ∈ Z_x:
 * |b_c − b| ≤ |b_c − x| + |x − b| ≤ 3 d(x);
 * ‖D(b_c) − D(b)‖ ≤ ‖D(b_c) − D(a)‖ + ‖D(b) − D(a)‖ ≤ 2η;
 * |h(b_c) − h(b) − D(b)(b_c − b)| ≤ η|b_c − b| ≤ 3η d(x), by 2(ii), since b, b_c ∈ A lie within δ of a;
 * |x − b_c| ≤ 2 d(x).
 By step 1, |P_{b_c}(x) − P_b(x)| ≤ 3η d(x) + 2η·2 d(x) = 7η d(x) = 700 η r(x). With step 8, the second sum has norm ≤ 700 η r(x)·M/r(x) = 700 M η.
 Hence ‖Dg(x) − D(a)‖ ≤ η(1 + 700M) = ε/2 < ε.
So Dg is continuous at a.

13. (Conclusion.) By steps 9, 11 and 12, g is differentiable on ℝ^n with continuous derivative, so g ∈ C¹ (ContDiff ℝ 1 g, via contDiff_one_iff_fderiv). By step 9, g = h on A. By step 11, HasFDerivAt g (D a) a for every a ∈ A. ∎

Implementation notes (not part of the mathematics).
- The SimonGMT files formalize exactly steps 0–13. The goal is closed by `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney hA ⟨hh, hD, hrem⟩`; the three hypotheses are the fields continuous_value, continuous_derivative and remainder of HasWhitneyC1Compatibility.
- Do NOT import Poincare.SimonGMT.Chapter02.Whitney*.
 - WhitneyExtension has no .olean.
 - The WhitneyCover, WhitneyPartition and WhitneyJet oleans were built on Oct 3 in another environment, so their Lake traces are stale.
 - The comparator runs `lake build` (verifier/comparator/Main.lean), which tries to rebuild them and fails on the read-only shared package tree ('failed to remove output artifacts: read-only file system'). `lake env lean` hides this.
- Vendor all four files instead:
 - Create GMT/Ch07/WhitneyCover.lean, GMT/Ch07/WhitneyPartition.lean, GMT/Ch07/WhitneyJet.lean and GMT/Ch07/WhitneyExtension.lean. The verifier accepts new .lean files under GMT/Ch07/.
 - Copy them unmodified except that each `public import Poincare.SimonGMT.Chapter02.WhitneyX` becomes `public import GMT.Ch07.WhitneyX`.
 - Add `import GMT.Ch07.WhitneyExtension` to Submission.lean.
- In a scratch copy of this project, `lake build` of exactly this layout succeeded. The stated type was proved by the one-line term above, and #print axioms reports propext, Classical.choice and Quot.sound.
- The vendored declarations keep the namespace Poincare.SimonGMT.Chapter02. No other SimonGMT module imports the Whitney files, so no duplicate declarations arise.

## Key steps

1. If A = ∅, g = 0. Otherwise use the radius r(x) = min(1, dist(x,A))/100, the affine jets P_b(x) = h(b) + D(b)(x − b), and nearest points π(x) ∈ A.
2. Compact-uniform compatibility on A ∩ B̄(a,1) plus continuity of D gives the local estimate: ‖D(b) − D(a)‖ ≤ η and |h(c) − h(b) − D(b)(c − b)| ≤ η|c − b| for b, c ∈ A within δ of a.
3. Vitali gives disjoint Whitney balls B(c, r(c)) whose 4-fold enlargements cover ℝ^n ∖ A. Radii of nearby centres are comparable, and the overlap is uniformly bounded by N.
4. Rescaled bumps φ_c, normalized to w_c = φ_c/Σφ, form a smooth partition of unity on ℝ^n ∖ A with Σ‖Dw_c(x)‖ ≤ M/r(x).
5. Let g = h on A and g = Σ w_c P_{π(c)} off A. Then g is smooth off A. Near a ∈ A, |g(x) − P_a(x)| ≤ ε|x − a|, so Dg(a) = D(a). Also ‖Dg(x) − D(a)‖ ≤ η(1 + 700M) near a, so Dg is continuous. Hence g ∈ C¹.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; cat PROBLEM.md README.md swarm-project.json lakefile.toml lean-toolchain; ls GMT/Ch07 (only Contract.lean, Submission.lean, README.md)`
- `rg -l -i whitney <snapshot>/mathlib/Mathlib -> Geometry/Manifold/WhitneyEmbedding.lean, Geometry/Manifold/PartitionOfUnity.lean, CategoryTheory/Monoidal/Rigid/Braided.lean (no C¹ Whitney extension)`
- `rg -l -i lusin <snapshot>/mathlib/Mathlib -> Constructions/Polish/Basic.lean, Topology/MetricSpace/Polish.lean, Topology/MetricSpace/CantorScheme.lean, MeasureTheory/Function/Jacobian.lean, Tactic/Inclusion/Core/Elab.lean (Lusin–Souslin / Lusin separation only; no measure-theoretic Lusin continuity theorem)`
- `rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto' (MeasureTheory/Function/Egorov.lean:205); rg -n 'MeasurableSet.exists_isClosed_sdiff_lt' (MeasureTheory/Measure/Regular.lean:1036); rg -n 'theorem continuousOn_iUnion |theorem isClosed_iUnion' Topology/LocallyFinite.lean (103, 128); rg -n 'measurableSet_of_differentiableAt|measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean (372, 378); rg -n norm_fderiv_le_of_lipschitz Analysis/Calculus/FDeriv/Basic.lean (947); rg -n ae_differentiableAt Analysis/Calculus/Rademacher.lean; rg -n measurable_of_Ioi MeasureTheory/Constructions/BorelSpace/Order.lean (653); rg -n exists_disjoint_subfamily_covering_enlargement_ball MeasureTheory/Covering/Vitali.lean (195); rg -n contDiff_one_iff_fderiv Analysis/Calculus/ContDiff/Defs.lean (1261); rg -n 'structure ContDiffBump' Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n -i 'c1_approx|whitney' <snapshot>/project/GMT/Ch07/Contract.lean (no match)`
- `python3 -I scans of dag.json: lean_name/title/statement matching whitney|lusin|egor|rademacher (only the selected node and the accepted dor_ims_lusin_* nodes); exact title/statement/lean_statement of dor_ims_lusin_measurable_continuousOn (status accepted, candidate e4172a7b); collision check for codim1_rdo_c1a_whitney_extension, codim1_rdo_c1a_lusin_isClosed, codim1_rdo_c1a_egorov_isClosed, codim1_rdo_c1a_whitney_remainder (0 matches); selected node depth 5, no children; parent's decomposition-v1.json format for reused accepted children`
- `git grep -i -E 'whitney|egorov|egoroff|tendstoUniformlyOn_of_ae_tendsto|codim1_rdo_c1a_' over all 768 candidate/speculative/integrated commits in dag.json (no match); git log --all --name-only -- GMT/Ch07 (no Lean file other than Submission.lean ever added); git show e4172a7b:GMT/Ch07/Submission.lean (accepted Lusin proof, lines 453–515, prefix identical to Contract.lean, no extra imports)`
- `sed -n /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py: _decompose (depth >= max_depth check), _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff (accepted checkpoints untouched), _overlay_accepted_children and _merge_candidate_history (Lean-unioned merge of children + depends_on); store.py ensure`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) and child_modules; grep -n 'lake' verifier/comparator/Main.lean (runs `lake build <target>`)`
- `grep -n in book/chapter-02.txt (1.5 Theorem line 165, 1.6 Theorem line 173, 'For the proof see' line 186, Proof of Theorem 1.5 lines 246–266) and book/chapter-01.txt (1.15 infinite-measure case lines 323–342, 1.17 Lusin line 346)`
- `cat simongmt Chapter01/Lusin.lean and Chapter02/Whitney{Cover,Partition,Jet,Extension}.lean; ls -la and find -name '*.olean' ! -newermt 2026-10-10 in simongmt/.lake/build/lib/lean/Poincare/SimonGMT (stale: Audit, Chapter02/WhitneyCover, WhitneyJet, WhitneyPartition; WhitneyExtension.olean absent); grep -rln 'import Poincare.SimonGMT.Chapter02.Whitney' (only WhitneyPartition, WhitneyExtension)`
- `lake env lean /tmp/c1a-split/Avail.lean, Api.lean (#check of cited lemmas, instance probes for SecondCountableTopology/OpensMeasurableSpace on Euclid n →L[ℝ] ℝ and WeaklyRegular/IsAddHaarMeasure volume), Types.lean, Assembly.lean (#print axioms); lake env lean /tmp/c1a-split/proto/{LusinClosed,EgorovClosed,WhitneyRemainder}.lean; lake env lean /tmp/c1a-split/vendor/WhitneyExtensionCopy.lean (#print axioms)`
- `lake build GMT.Ch07.WhitneyTest in scratch copy /tmp/c1a-split/projtest (git archive HEAD, .lake/packages -> shared tree): fails importing stale Poincare.SimonGMT.Chapter02.WhitneyJet ('failed to remove output artifacts: read-only file system'); succeeds with the four Whitney files vendored under GMT/Ch07/; lake build GMT.Ch07.C1AEndToEnd and GMT.Ch07.C1AFinalCheck (#print axioms)`
- `web (standard): Evans–Gariepy 'Measure Theory and Fine Properties of Functions' §6.5 Whitney's extension theorem, §6.6.1 approximation of Lipschitz functions by C¹ functions`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-07b3f8e4c7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-c-3a11b01ce9/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-c-3a11b01ce9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/github_runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/Main.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1a-split/Avail.lean`
- `/tmp/c1a-split/Api.lean`
- `/tmp/c1a-split/Types.lean`
- `/tmp/c1a-split/Assembly.lean`
- `/tmp/c1a-split/proto/LusinClosed.lean`
- `/tmp/c1a-split/proto/EgorovClosed.lean`
- `/tmp/c1a-split/proto/WhitneyRemainder.lean`
- `/tmp/c1a-split/vendor/WhitneyExtensionCopy.lean`
- `/tmp/c1a-split/projtest/GMT/Ch07/WhitneyTest.lean`
- `/tmp/c1a-split/projtest/GMT/Ch07/C1AEndToEnd.lean`
- `/tmp/c1a-split/projtest/GMT/Ch07/C1AFinalCheck.lean`
- `/tmp/c1a-split/final/statements.json`

Pins and scope.
- The snapshot (project b4d606db, Mathlib 25730c7c) matches the workspace, and Submission.lean equals Contract.lean.
- Children are elaborated in the replayed contract scope: namespace GMT.Ch07 with its opens.
- Neither SimonGMT's HasWhitneyC1Compatibility nor its Lusin theorem is in scope after `import GMT.Ch07.Submission`, so the Whitney hypothesis is stated inline.

Library.
- The snapshot Mathlib has no C¹ Whitney extension; 'whitney' matches only the manifold embedding files.
- It has no measure-theoretic Lusin continuity theorem; 'lusin' matches only Lusin–Souslin and Lusin separation.
- It does have everything the children use: Egorov (Egorov.lean:205), closed inner regularity (Regular.lean:1036), LocallyFinite.isClosed_iUnion and continuousOn_iUnion, Rademacher, measurableSet_of_differentiableAt and measurable_fderiv, norm_fderiv_le_of_lipschitz, measurable_of_Ioi, Vitali, contDiff_one_iff_fderiv and ContDiffBump.
- SimonGMT kernel-checks Whitney 1.6 as exists_contDiff_one_extension_of_whitney. However, WhitneyExtension has no olean, and the WhitneyCover, WhitneyPartition and WhitneyJet oleans are stale (Oct 3, built in another environment; every other SimonGMT olean is from Oct 11).
- The comparator runs `lake build`. Importing those modules makes it try to rebuild them on the read-only tree, which fails.
- Vendoring all four files under GMT/Ch07/ with redirected imports builds; the axioms are propext, Classical.choice and Quot.sound.
- Simon prints no proof of 1.6 (chapter-02.txt line 186 refers to [EG92]/[Fed69]). The child's proof is the standard EG92 §6.5 construction that SimonGMT formalizes.

DAG.
- Submission.dor_ims_lusin_measurable_continuousOn is accepted (commit e4172a7b, self-contained) and is reused with its identical type.
- No other node or commit uses Whitney or Egorov.
- The four new names are globally unused.
- Depth 5 < max_depth 6, so depth-6 leaves are allowed.
- Accepted children are not handed off again; their commits are overlaid through children and depends_on.

Lean.
- All five child types elaborate and pass the comparator-style `exact Submission.X` check.
- The parent type follows from the child types.
- A full end-to-end `lake build` (accepted Lusin proof, prototype proofs of lusin_closed, egorov_closed and whitney_remainder, vendored Whitney, and the assembly) proves Submission.codim1_rdo_c1_approximation with axioms propext, Classical.choice and Quot.sound only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
