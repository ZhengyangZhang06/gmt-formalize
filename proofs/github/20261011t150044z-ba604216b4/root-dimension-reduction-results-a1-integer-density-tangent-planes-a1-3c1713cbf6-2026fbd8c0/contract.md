<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1 -->

## Theorem `Submission.idtp_carrier_area_formula`

For all P, n ∈ ℕ with n ≥ 1, every Borel set M ⊆ ℝ^P that is countably n-rectifiable (CountablyRectifiable n M) with H^n(M ∩ K) < ∞ for every compact K ⊆ ℝ^P (H^n := μHE[n]), every open Z ⊆ ℝ^P, every map F : ℝ^P → ℝ^n (= Euclid n) that is C¹ on Z (ContDiffOn ℝ 1 F Z) and every h : ℝ^P → [0, ∞] that is a.e. measurable for H^n⌞M: the fibre-sum function y ↦ Σ_{x ∈ M ∩ Z, F(x) = y} h(x) ∈ [0, ∞] (the tsum over the subtype M ∩ Z ∩ F^{−1}{y}) is a.e. measurable for Lebesgue measure L^n (volume) on ℝ^n, and ∫_{ℝ^n} Σ_{x ∈ M ∩ Z, F(x) = y} h(x) dL^n(y) = ∫_{M∩Z} J*(x)·h(x) dH^n(x), where J*(x) := (det(⟨DF(x)u_i, DF(x)u_j⟩)_{i,j})^{1/2}, DF(x) = fderiv ℝ F x and (u_i) is the standard orthonormal basis (stdOrthonormalBasis) of the approximate tangent plane T_x := approxTangentPlane n M x, indexed by Fin (dim T_x).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1032

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5333, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5345, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5354, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2947, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4589, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4538, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5366, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5372, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5382

## Lean problem

Declaration: `Submission.idtp_carrier_area_formula`

```lean
∀ (P n : ℕ) (M Z : Set (Euclid P)) (F : Euclid P → Euclid n) (h : Euclid P → ℝ≥0∞), 1 ≤ n → MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → IsOpen Z → ContDiffOn ℝ 1 F Z → AEMeasurable h (μHE[n].restrict M) → AEMeasurable (fun y : Euclid n => ∑' x : ↥(M ∩ Z ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(M ∩ Z ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ x in M ∩ Z, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane n M x)) => inner ℝ (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) i)) (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) j))))) * h x ∂μHE[n]
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, §2, 2.1–2.6 (chapter-03.txt lines 330–407): for a countably n-rectifiable M and a locally Lipschitz f, (2.4) ∫_A J^M_f dH^n = ∫ H^0(A ∩ f^{−1}(y)) dH^n(y), and its weighted form (2.5) for nonnegative H^n-measurable h. The book proves (2.4) by decomposing M into pieces M_j ⊆ N_j of C¹ submanifolds (Lemma 1.2), identifying J^M_f on M_j with the Jacobian of a C¹ map on N_j, applying the smooth area formula (Ch. 2, 3.4) and summing over j. The present proof follows the same plan with Lipschitz-parametrized bi-Lipschitz pieces in place of C¹ submanifolds, because the library provides the verified Euclidean-domain Lipschitz area formula (SimonGMT Chapter02, Simon Ch. 2, 3.4–3.5) but neither the C¹ approximation theorem nor the C¹ cover of Lemma 1.2: step 2 is the parametrization reduction (Simon Ch. 3, 1.2–1.3), step 3 the identification of approximate tangent planes along a piece (the density argument of Simon's proof of Theorem 1.6 "⇒", lines 109–143, with a bi-Lipschitz image in place of a C¹ manifold), step 5 the Jacobian chain rule, steps 0, 1(c), 4 and 7 the null-set handling, and step 7 the transfer of parameter fibre sums to carrier fibre sums. It is used with n = 2 by the sibling child cone_sector_endpoint_density (step 7). Notation. E := ℝ^P = Euclid P; ℝ^n := Euclid n with Lebesgue measure L^n := volume; H^n := μHE[n] on E or on ℝ^n, and on ℝ^n, μHE[n] = L^n (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). B_ρ(x) and B̄_ρ(x) are the open and the closed ball. For a map φ between finite-dimensional real inner product spaces, Dφ(a) := fderiv ℝ φ a (the zero map where φ is not differentiable) and J_φ(a) := normDet(Dφ(a)) (SimonGMT areaJacobianAt φ a; Mathlib LinearMap.normDet, the nonnegative square root of det(Dφ(a)^*Dφ(a))). T_x := approxTangentPlane n M x and J*(x) is the integrand factor of the statement. For S ⊆ E and y ∈ ℝ^n, Σ_S(y) := Σ_{x ∈ S, F(x) = y} h(x) ∈ [0, ∞] is the tsum over the subtype S ∩ F^{−1}{y} (SimonGMT weightedAreaFiberSum S F h y); the statement concerns Σ_{M∩Z}. Library facts used. (L1) Lipschitz images. If φ : X → Y (finite-dimensional real inner product spaces) is K-Lipschitz on S ⊆ X, then H^n(φ(S)) ≤ K^n·H^n(S): Mathlib LipschitzOnWith.hausdorffMeasure_image_le for μH[n], and μHE[n] = c_n·μH[n] with a constant c_n ∈ (0, ∞) depending only on n (Measure.euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero). In particular Lipschitz images of H^n-null sets are H^n-null. (A1) Euclidean weighted area formula (SimonGMT Chapter02/AreaNoninjective.lean, weighted_area_formula_lipschitz_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitz): for a Lipschitz φ : ℝ^n → Y, a Borel s ⊆ ℝ^n and a Borel w : ℝ^n → [0, ∞], the fibre sum y ↦ Σ_{a ∈ s, φ(a) = y} w(a) is μHE[n]-a.e. measurable on Y and ∫_Y Σ_{a ∈ s, φ(a) = y} w(a) dμHE[n](y) = ∫_s J_φ(a)w(a) dL^n(a) (finrank ℝ ℝ^n = n). (A2) Injective area formula (SimonGMT Chapter02/AreaLipschitz.lean, weighted_area_formula_lipschitz_injOn): for a Lipschitz φ : ℝ^n → Y, a Borel s on which φ is injective and an arbitrary (not necessarily measurable) κ : Y → [0, ∞], ∫_{φ(s)} κ dμHE[n] = ∫_s J_φ(a)κ(φ(a)) dL^n(a). (G) Gram determinants and the chain rule (Mathlib Analysis/InnerProductSpace/NormDet.lean). For a linear A : E → ℝ^n and a subspace T ⊆ E with orthonormal basis u, det(⟨Au_i, Au_j⟩)_{i,j} = normDet(A|_T)² (LinearMap.normDet_sq_eq_det_gram applied to A.domRestrict T and u); since normDet ≥ 0, J*(x) = normDet(DF(x)|_{T_x}) for every x. For linear L : ℝ^n → E and A : E → ℝ^n, normDet(A∘L) = normDet(A|_{range L})·normDet(L) (LinearMap.normDet_comp). (D) Density points. For Borel S ⊆ ℝ^n, L^n-a.e. a ∈ S is a density point of S: L^n(S ∩ B̄_ρ(a))/L^n(B̄_ρ(a)) → 1 as ρ → 0⁺ (Mathlib Besicovitch.ae_tendsto_measure_inter_div). If a ∈ S is a density point and v ∈ ℝ^n, there are r_k → 0⁺ and v_k → v with a + r_kv_k ∈ S. For v = 0 take v_k := 0. For v ≠ 0 suppose not; then there are ε ∈ (0, |v|) and r_1 > 0 with S ∩ (a + rB_ε(v)) = ∅ for all r ∈ (0, r_1); as a + rB_ε(v) ⊆ B̄_{r(|v|+ε)}(a) has L^n-measure (ε/(|v| + ε))^n·L^n(B̄_{r(|v|+ε)}(a)) (Lebesgue measure scales by r^n, and open and closed balls have equal measure, Measure.addHaar_closedBall_eq_addHaar_ball, ℝ^n being nontrivial as n ≥ 1), L^n(S ∩ B̄_ρ(a))/L^n(B̄_ρ(a)) ≤ 1 − (ε/(|v| + ε))^n for all ρ ∈ (0, r_1(|v| + ε)), contradicting density.
0. (Reduction to Borel h.) As h is a.e. measurable for H^n⌞M, there is a Borel h̃ : E → [0, ∞] with (H^n⌞M)({h ≠ h̃}) = 0, i.e. H^n(N_h) = 0 for N_h := M ∩ {h ≠ h̃} (M is Borel, Measure.restrict_apply'). The right-hand sides for h and h̃ agree, since the integrands agree on (M ∩ Z) ∖ N_h. The fibre sums Σ_{M∩Z}(y) for h and for h̃ agree at every y ∉ F(N_h ∩ Z), and F(N_h ∩ Z) is L^n-null by step 1(c). So both conclusions for h follow from those for h̃ (a.e. measurability is preserved under change on a null set, and lintegrals of a.e. equal functions agree). From now on h is Borel.
1. (Lipschitz localization of F.) (a) If Z = ∅, every fibre is empty, the fibre-sum function is the constant 0 and both sides vanish; assume Z ≠ ∅. For x ∈ Z choose r_x > 0 with B̄_{r_x}(x) ⊆ Z (Z is open). F is C¹ on the convex compact set B̄_{r_x}(x), hence Lipschitz on it (Mathlib ContDiffOn.exists_lipschitzOnWith). The balls B_{r_x}(x), x ∈ Z, cover Z and E is second countable, so countably many of them cover Z; enumerate them as V_0, V_1, … (repetitions allowed) and let K_l be a Lipschitz constant of F on V_l. (b) By Mathlib LipschitzOnWith.extend_finite_dimension there is a Lipschitz F_l : E → ℝ^n with F_l = F on V_l. Put Z_l := V_l ∖ ∪_{l'<l} V_{l'}. The Z_l are Borel and pairwise disjoint, ∪_l Z_l = Z, and F = F_l on Z_l. (c) If S ⊆ Z and H^n(S) = 0, then F(S) = ∪_l F_l(S ∩ Z_l) is L^n-null by (L1) (μHE[n] = L^n on ℝ^n).
2. (Bi-Lipschitz pieces of M.) There are Lipschitz maps g_i : ℝ^n → E, Borel sets A_i ⊆ ℝ^n and constants c_i > 0 (i ∈ ℕ) such that: (i) c_i|a − a'| ≤ |g_i(a) − g_i(a')| for all a, a' ∈ A_i (so g_i is injective on A_i); (ii) g_i is differentiable at every a ∈ A_i and Dg_i(a) is injective; (iii) the sets g_i(A_i) are Borel subsets of M and pairwise disjoint; (iv) H^n(M ∖ ∪_i g_i(A_i)) = 0. Proof. (2a) By CountablyRectifiable n M there are M_0 ⊆ E with H^n(M_0) = 0 and Lipschitz maps G_j : ℝ^n → E (j ∈ ℕ) with M ⊆ M_0 ∪ ∪_j G_j(ℝ^n). (2b) Let R_j := {a : G_j is differentiable at a and DG_j(a) is injective} (SimonGMT areaRegularSet G_j); R_j is Borel (measurableSet_areaRegularSet) and H^n(G_j(ℝ^n ∖ R_j)) = 0 (area_image_compl_regularSet_eq_zero with s := univ). (2c) For an injective linear A : ℝ^n → E choose m(A) > 0 with |Av| ≥ m(A)|v| for all v (m(A) := 1/K for an antilipschitz constant K > 0 of A, Mathlib LinearMap.exists_antilipschitzWith), and put r(A) := m(A)/2 if A is injective and r(A) := 1 otherwise; so r(A) > 0 for every A. (2d) For each j, Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (f := G_j, s := R_j, f' := DG_j — at a ∈ R_j, G_j has derivative DG_j(a), hence also within R_j — and the radius function r) gives pairwise disjoint measurable sets t_{j,k} (k ∈ ℕ) with R_j ⊆ ∪_k t_{j,k} and continuous linear maps A_{j,k} with |G_j(a) − G_j(a') − A_{j,k}(a − a')| ≤ r(A_{j,k})|a − a'| for a, a' ∈ R_j ∩ t_{j,k}, and, if R_j ≠ ∅, A_{j,k} = DG_j(y) for some y ∈ R_j. (2e) Put D_{j,k} := R_j ∩ t_{j,k} (Borel). If D_{j,k} ≠ ∅, then A := A_{j,k} = DG_j(y) with y ∈ R_j is injective, r(A) = m(A)/2, and for a, a' ∈ D_{j,k}, |G_j(a) − G_j(a')| ≥ |A(a − a')| − (m(A)/2)|a − a'| ≥ (m(A)/2)|a − a'| = r(A_{j,k})|a − a'|. (2f) Let i ↦ (j(i), k(i)) be the bijection ℕ → ℕ × ℕ (Nat.unpair) and put g_i := G_{j(i)}, D_i := D_{j(i),k(i)}, c_i := r(A_{j(i),k(i)}) > 0 and N_i := g_i(D_i); N_i is Borel by the Lusin–Souslin theorem (Mathlib MeasurableSet.image_of_continuousOn_injOn; g_i is continuous and, by (2e), injective on D_i). (2g) Put A_i := D_i ∩ g_i^{−1}(M ∖ ∪_{i'<i} N_{i'}) (Borel). Then g_i(A_i) = (N_i ∩ M) ∖ ∪_{i'<i} N_{i'} is Borel and contained in M, and for i' < i, g_{i'}(A_{i'}) ⊆ N_{i'} is disjoint from g_i(A_i): (iii). Since A_i ⊆ D_i ⊆ R_{j(i)}, (i) holds by (2e) and (ii) by the definition of R_{j(i)}. (2h) If x ∈ M ∖ (M_0 ∪ ∪_j G_j(ℝ^n ∖ R_j)), then x = G_j(a) with a ∈ R_j ⊆ ∪_k t_{j,k}; so a ∈ D_i for the index i of the pair (j, k) and x ∈ N_i ∩ M; if i_0 is the least index with x ∈ N_{i_0}, then x ∈ g_{i_0}(A_{i_0}). Hence M ∖ ∪_i g_i(A_i) ⊆ M_0 ∪ ∪_j G_j(ℝ^n ∖ R_j), an H^n-null set: (iv).
3. (Approximate tangent planes along a piece.) For every i and L^n-a.e. a ∈ A_i, M has the approximate tangent space range Dg_i(a) at g_i(a) (HasApproximateTangentSpaceAt n M (g_i(a)) (range Dg_i(a))); consequently T_{g_i(a)} = range Dg_i(a). The "consequently": by definition approxTangentPlane n M x is a chosen Q with HasApproximateTangentSpaceAt n M x Q whenever such a Q exists, and any two such Q coincide (SimonGMT HasApproximateTangentSpaceAt.unique). Recall that HasApproximateTangentSpaceAt n M y Q means dim Q = n and ∫_{η_{y,r}(M)} f dH^n → ∫_Q f dH^n as r → 0⁺ for every f ∈ C_c(E), where η_{y,r}(z) := r^{−1}(z − y) (SimonGMT blowUpMap y r). Proof. Fix i and write g := g_i, B := A_i, c := c_i, Λ := a Lipschitz constant of g, Γ := g(B) ⊆ M (Borel by step 2), λ := L^n, ω_n := λ(B̄_1(0)) ∈ (0, ∞) and ‖f‖_∞ := sup|f|. (3a) Preliminaries. The inverse G : Γ → B of g|_B is c^{−1}-Lipschitz, so by (L1) λ(G(N)) ≤ c^{−n}H^n(N) for N ⊆ Γ: a property holding at every point of Γ outside an H^n-null set N holds at g(b) for every b ∈ B ∖ G(N), and G(N) is λ-null. H^n(g(S)) ≤ Λ^nλ(S) for every S ⊆ ℝ^n (L1). For r > 0 and S ⊆ E, H^n(η_{y,r}(S)) = r^{−n}H^n(S) (Mathlib euclideanHausdorffMeasure_homothety_image together with the isometry invariance Isometry.euclideanHausdorffMeasure_image for the translation z ↦ z − y); η_{y,r} is a homeomorphism, so η_{y,r}(S) is Borel for Borel S and ∫_{η_{y,r}(S)} f dH^n = r^{−n}∫_S f(η_{y,r}(z)) dH^n(z) whenever either side is the integral of an integrable function (MeasurableEmbedding.integral_map, integral_smul_measure). Finally 0 ≤ J_g ≤ Λ^n everywhere and J_g is Borel (SimonGMT measurable_areaJacobianAt): ‖Dg(a)‖ ≤ Λ (Mathlib norm_fderiv_le_of_lipschitz), and normDet(T) ≤ ‖T‖^n for every linear T : ℝ^n → E because normDet(T)·ω_n = H^n(T(B̄_1(0))) ≤ ‖T‖^n·ω_n (Mathlib LinearMap.euclideanHausdorffMeasure_image and (L1)). (3b) Density of Γ in M. For k ∈ ℕ let C_k := B̄_k(0) and ν_k := H^n⌞(M ∩ C_k), a finite Borel measure (H^n(M ∩ C_k) < ∞ by hypothesis). By the Besicovitch density theorem (Mathlib Besicovitch.ae_tendsto_measure_inter_div for ν_k and Γ), for ν_k⌞Γ-a.e. y, ν_k(Γ ∩ B̄_r(y))/ν_k(B̄_r(y)) → 1 as r → 0⁺; since Γ ⊆ M and Γ, M, C_k are Borel, ν_k⌞Γ = H^n⌞(Γ ∩ C_k). Let N_1 be the union over k of the exceptional sets (so H^n(N_1) = 0), and call y ∈ Γ ∖ N_1 density-good; for such y and every k ≥ |y| + 1 the convergence holds. (3c) Smallness of M ∖ Γ. Let y = g(b) (b ∈ B) be density-good and k ≥ |y| + 1. For 0 < r < 1, B̄_r(y) ⊆ C_k; with a(r) := H^n(Γ ∩ B̄_r(y)) and z(r) := H^n((M ∖ Γ) ∩ B̄_r(y)) we have ν_k(Γ ∩ B̄_r(y)) = a(r) and ν_k(B̄_r(y)) = a(r) + z(r) < ∞; by (3b), for every ε ∈ (0, 1/2) there is r_ε ∈ (0, 1) with z(r) ≤ ε(a(r) + z(r)), hence z(r) ≤ 2εa(r), for 0 < r < r_ε. If a' ∈ B and g(a') ∈ B̄_r(y), then c|a' − b| ≤ |g(a') − g(b)| ≤ r; so Γ ∩ B̄_r(y) ⊆ g(B ∩ B̄_{r/c}(b)) and a(r) ≤ Λ^nω_nc^{−n}r^n (for every b ∈ B and r > 0). Thus z(r) ≤ 2εΛ^nω_nc^{−n}r^n for r < r_ε, i.e. r^{−n}z(r) → 0 as r → 0⁺. (3d) Good parameters. λ-a.e. b ∈ B satisfies (α) b is a density point of B (D), and (β) b is a Lebesgue point of J_g: ρ^{−n}∫_{B̄_ρ(b)}|J_g(a) − J_g(b)| dλ(a) → 0 as ρ → 0⁺ (Mathlib IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub for the additive Haar measure λ and the bounded Borel, hence locally integrable, J_g). Every b ∈ B with (α) satisfies (γ) |Dg(b)v| ≥ c|v| for all v ∈ ℝ^n: by (D) there are r_k → 0⁺ and v_k → v with b + r_kv_k ∈ B, so c·r_k|v_k| ≤ |g(b + r_kv_k) − g(b)| = |r_kDg(b)v_k + o(r_k)| (differentiability of g at b, step 2(ii)); divide by r_k and let k → ∞. (3e) Blow-up of Γ. Let b ∈ B satisfy (α) and (β), y := g(b), f ∈ C_c(E) and R > 0 with f = 0 outside B_R(0); put Φ_r(v) := (g(b + rv) − g(b))/r for r > 0. (i) η_{y,r}(Γ) ∩ B_R(0) = η_{y,r}(Γ ∩ B_{rR}(y)) has H^n-measure ≤ r^{−n}a(rR) ≤ Λ^nω_n(R/c)^n, so f is integrable on η_{y,r}(Γ); by (3a), (A2) for the injective Lipschitz map g on B (applied to the positive and the negative part of f∘η_{y,r} and subtracted; all terms are finite since f is bounded and only B ∩ B̄_{rR/c}(b) contributes) and the substitution a = b + rv (λ scales by r^n): ∫_{η_{y,r}(Γ)} f dH^n = r^{−n}∫_B J_g(a)f((g(a) − y)/r) dλ(a) = ∫_{ℝ^n} 1_B(b + rv)J_g(b + rv)f(Φ_r(v)) dλ(v). (ii) If b + rv ∈ B and f(Φ_r(v)) ≠ 0, then c·r|v| ≤ |g(b + rv) − g(b)| < rR, so |v| < R/c; and f(Dg(b)v) = 0 for |v| ≥ R/c by (γ). So with D_R := B̄_{R/c}(0) the integral in (i) is an integral over D_R, and I_∞ := ∫_{ℝ^n} J_g(b)f(Dg(b)v) dλ(v) = ∫_{D_R} J_g(b)f(Dg(b)v) dλ(v). (iii) For v ∈ D_R, |1_B(b + rv)J_g(b + rv)f(Φ_r(v)) − J_g(b)f(Dg(b)v)| ≤ Λ^n‖f‖_∞1_{D_R ∖ r^{−1}(B − b)}(v) + ‖f‖_∞|J_g(b + rv) − J_g(b)| + J_g(b)|f(Φ_r(v)) − f(Dg(b)v)| (add and subtract J_g(b + rv)f(Φ_r(v)) and J_g(b)f(Φ_r(v)); J_g ≤ Λ^n). Integrated over D_R, the first term gives Λ^n‖f‖_∞r^{−n}λ(B̄_{rR/c}(b) ∖ B) → 0 by (α) (λ(B̄_{rR/c}(b)) = ω_n(R/c)^nr^n); the second gives ‖f‖_∞r^{−n}∫_{B̄_{rR/c}(b)}|J_g − J_g(b)| dλ → 0 by (β); the third is ≤ J_g(b)λ(D_R)sup_{v∈D_R}|f(Φ_r(v)) − f(Dg(b)v)| → 0, because Φ_r → Dg(b) uniformly on D_R (differentiability of g at b) and f is uniformly continuous. Hence ∫_{η_{y,r}(Γ)} f dH^n → I_∞ as r → 0⁺. (iv) L_b := Dg(b) is linear and injective with normDet(L_b) = J_g(b), and H^n(L_b(S)) = J_g(b)λ(S) for every S ⊆ ℝ^n (Mathlib LinearMap.euclideanHausdorffMeasure_image); so H^n⌞range L_b is the image of J_g(b)·λ under the closed embedding L_b, and I_∞ = J_g(b)∫ f(L_bv) dλ(v) = ∫_{range L_b} f dH^n (MeasurableEmbedding.integral_map). (3f) Conclusion. Let b ∈ B lie outside the λ-null set where (α) or (β) fails and outside G(N_1 ∩ Γ) (λ-null by (3a) and (3b)); then y := g(b) is density-good. Let f and R be as in (3e) and k ≥ |y| + 1. For 0 < r < 1/R, B̄_{rR}(y) ⊆ C_k, so H^n(η_{y,r}(M) ∩ B_R(0)) ≤ r^{−n}H^n(M ∩ C_k) < ∞ and f is integrable on η_{y,r}(M); as η_{y,r}(M) is the disjoint union of the Borel sets η_{y,r}(Γ) and η_{y,r}(M ∖ Γ), |∫_{η_{y,r}(M)} f dH^n − ∫_{η_{y,r}(Γ)} f dH^n| ≤ ‖f‖_∞H^n(η_{y,r}(M ∖ Γ) ∩ B_R(0)) ≤ ‖f‖_∞r^{−n}z(rR) = ‖f‖_∞R^n(rR)^{−n}z(rR) → 0 by (3c). With (3e), ∫_{η_{y,r}(M)} f dH^n → ∫_{range L_b} f dH^n as r → 0⁺ for every f ∈ C_c(E), and dim range L_b = n (L_b injective). This is HasApproximateTangentSpaceAt n M (g(b)) (range Dg(b)), for λ-a.e. b ∈ B.
4. (Pieces adapted to F.) For i, l ∈ ℕ put A_{i,l} := A_i ∩ g_i^{−1}(Z_l) (Borel, g_i being continuous), S_{i,l} := g_i(A_{i,l}) = g_i(A_i) ∩ Z_l (Borel) and Φ_{i,l} := F_l∘g_i : ℝ^n → ℝ^n (Lipschitz). The S_{i,l} are pairwise disjoint subsets of M ∩ Z (steps 1(b), 2(iii)), and N_0 := (M ∩ Z) ∖ ∪_{i,l} S_{i,l} ⊆ M ∖ ∪_i g_i(A_i) is H^n-null (step 2(iv) and ∪_l Z_l = Z). For a ∈ A_{i,l}, g_i(a) ∈ Z_l, so F(g_i(a)) = F_l(g_i(a)) = Φ_{i,l}(a).
5. (Jacobian chain rule.) For all i, l and L^n-a.e. a ∈ A_{i,l}: J_{Φ_{i,l}}(a) = J*(g_i(a))·J_{g_i}(a). Indeed, by step 3 (A_{i,l} ⊆ A_i), L^n-a.e. a ∈ A_{i,l} satisfies T_{g_i(a)} = range Dg_i(a). Fix such an a and put x := g_i(a) ∈ Z_l ⊆ V_l, L := Dg_i(a) (injective, step 2(ii)) and A' := DF(x); F is C¹ on the open set Z ⊇ V_l, hence differentiable at x. Since F_l = F on the open set V_l ∋ x, F_l is differentiable at x with DF_l(x) = A' (maps that agree on a neighbourhood of x have the same derivative at x, Mathlib HasFDerivAt.congr_of_eventuallyEq, Filter.EventuallyEq.fderiv_eq). By the chain rule, Φ_{i,l} = F_l∘g_i is differentiable at a with DΦ_{i,l}(a) = A'∘L. By (G), J_{Φ_{i,l}}(a) = normDet(A'∘L) = normDet(A'|_{range L})·normDet(L) = normDet(DF(x)|_{T_x})·J_{g_i}(a) = J*(x)·J_{g_i}(a).
6. (Carrier side.) M ∩ Z is the disjoint union of the H^n-null set N_0 and the Borel sets S_{i,l}. The restriction of H^n to the countable disjoint union ∪_{i,l} S_{i,l} is the sum of the restrictions (Mathlib Measure.restrict_iUnion), the lintegral against a sum of measures is the sum of the lintegrals for every [0, ∞]-valued integrand (lintegral_sum_measure), and N_0 contributes nothing; hence ∫_{M∩Z} J*h dH^n = Σ_{i,l} ∫_{S_{i,l}} J*h dH^n. For each (i, l), (A2) (φ := g_i, s := A_{i,l}, on which g_i is injective by 2(i), and κ := J*·h, for which no measurability is needed) and step 5 (the integrands agree L^n-a.e. on A_{i,l}; ofReal of a product of nonnegative reals is the product of the ofReal's) give ∫_{S_{i,l}} J*h dH^n = ∫_{A_{i,l}} J_{g_i}(a)J*(g_i(a))h(g_i(a)) dL^n(a) = ∫_{A_{i,l}} J_{Φ_{i,l}}(a)h(g_i(a)) dL^n(a).
7. (Fibre side and conclusion.) Fix y ∈ ℝ^n. Splitting the [0, ∞]-valued sum along the disjoint decomposition of step 6 (SimonGMT weightedAreaFiberSum_iUnion), Σ_{M∩Z}(y) = Σ_{N_0}(y) + Σ_{i,l} Σ_{S_{i,l}}(y). The first term vanishes unless y ∈ F(N_0), an L^n-null set by step 1(c). For each (i, l), a ↦ g_i(a) is a bijection from {a ∈ A_{i,l} : Φ_{i,l}(a) = y} onto {x ∈ S_{i,l} : F(x) = y} (g_i is injective on A_i, and F∘g_i = Φ_{i,l} on A_{i,l} by step 4), so Σ_{S_{i,l}}(y) = W_{i,l}(y) := Σ_{a ∈ A_{i,l}, Φ_{i,l}(a) = y} h(g_i(a)). Hence Σ_{M∩Z} = Σ_{i,l} W_{i,l} L^n-a.e. The weight h∘g_i is Borel (h Borel, g_i continuous), so (A1) (φ := Φ_{i,l}, s := A_{i,l}, w := h∘g_i, Y := ℝ^n, μHE[n] = L^n) shows that W_{i,l} is L^n-a.e. measurable with ∫ W_{i,l} dL^n = ∫_{A_{i,l}} J_{Φ_{i,l}}(a)h(g_i(a)) dL^n(a). Therefore Σ_{M∩Z} is L^n-a.e. measurable (a countable sum of a.e. measurable [0, ∞]-valued functions, AEMeasurable.ennreal_tsum, changed on a null set), and by lintegral_tsum and step 6, ∫ Σ_{M∩Z} dL^n = Σ_{i,l} ∫ W_{i,l} dL^n = Σ_{i,l} ∫_{A_{i,l}} J_{Φ_{i,l}}(a)h(g_i(a)) dL^n(a) = ∫_{M∩Z} J*h dH^n. ∎

## Key steps

1. Replace h by a Borel h̃ equal to it H^n-a.e. on M; the two sides change only on null sets, since C¹ maps send H^n-null subsets of Z to L^n-null sets.
2. Cover Z by countably many balls V_l on which F is Lipschitz; extend F|V_l to Lipschitz maps F_l on ℝ^P and disjointify into Borel sets Z_l.
3. Parametrization reduction: Rademacher's theorem and Mathlib's partition theorem decompose M, up to an H^n-null set, into disjoint Borel images g_i(A_i) of Lipschitz maps that are bi-Lipschitz with injective derivative on A_i.
4. Tangent identification: at L^n-a.e. a ∈ A_i the approximate tangent plane of M at g_i(a) is range Dg_i(a), by the density of g_i(A_i) in M, the injective area formula and a blow-up of g_i.
5. Chain rule: for a ∈ A_{i,l}, F_l = F on the open ball V_l ∋ g_i(a), so D(F_l∘g_i)(a) = DF(g_i(a))∘Dg_i(a); where T_{g_i(a)} = range Dg_i(a) (a.e.), normDet_comp and normDet_sq_eq_det_gram give J_{F_l∘g_i} = J*(g_i)·J_{g_i}.
6. Carrier side: by the injective area formula for g_i, ∫_{M∩Z} J*h dH^n = Σ_{i,l}∫_{A_{i,l}} J_{F_l∘g_i}·h∘g_i.
7. Fibre side: carrier fibre sums equal parameter fibre sums of F_l∘g_i off an L^n-null set, and the Euclidean Lipschitz area formula integrates them to the same series.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n '^theorem\|^def' simongmt Chapter02/{AreaNoninjective,AreaLipschitz,AreaMultiplicity,AreaBranches,AreaApproximation,WeightedArea}.lean Chapter03/{Rectifiable,Differential,SubmanifoldCover}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|area_image_compl_regularSet_eq_zero|measurable_areaJacobianAt|weightedAreaFiberSum_iUnion|exists_injective_partition_of_regular|ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt/Poincare/SimonGMT`
- `grep -rn 'normDet_sq_eq_det_gram|normDet_comp|euclideanHausdorffMeasure_image|exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|LipschitzWith.ae_differentiableAt|Besicovitch.ae_tendsto_measure_inter_div|extend_finite_dimension|ContDiffOn.exists_lipschitzOnWith|lintegral_withDensity_eq_lintegral_mul_non_measurable|EventuallyEq.fderiv_eq|AEMeasurable.ennreal_tsum|lintegral_tsum|restrict_iUnion|exists_antilipschitzWith' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rln 'C1Approximation|c1_approximation|lusin_c1' simongmt/Poincare/SimonGMT (no match); grep -n 'area formula' book/chapter-03.txt; sed -n 330,412p book/chapter-03.txt`
- `python3 scan of dag.json: lean_names containing idtp (none) or area; lean statements of dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, dpf_area_formula_bilipschitz_rectifiable, imrep_approxTangent_starProjection_aesm, dtc_* lemmas and dimred_* siblings`
- `grep -l idtp_ nodes/*/*.json outside this node (none); for d in .swarm-worktrees/*/gmt-ch07/GMT: grep -rl 'idtp_|carrier_area_formula' (none)`
- `lean /tmp/idtp_v3/check/Probe.lean (normDet, weightedAreaFiberSum, areaJacobianAt, tangentialJacobian are not in the import closure of GMT.Ch07.Submission)`
- `lean /tmp/idtp_v3/check/NewChild.lean; lean /tmp/idtp_v3/check/GramCheck.lean (#print axioms idtp_v3_gram_sqrt_eq_normDet)`
- `lean /tmp/idtp_v3/check/FromJsonV3.lean (#print axioms idtp_parent_check_json_v3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/tmp/idtp_v3/check/FromJsonV3.lean`
- `/tmp/idtp_v3/check/GramCheck.lean`
- `/tmp/idtp_v3/check/NewChild.lean`
- `/tmp/idtp_v3/check/Probe.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Library support for the new child.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitz (AreaNoninjective.lean); weighted_area_formula_lipschitz_injOn with arbitrary weights, areaRegularSet, measurableSet_areaRegularSet and area_image_compl_regularSet_eq_zero (AreaLipschitz.lean); measurable_areaJacobianAt; weightedAreaFiberSum_iUnion.
- SimonGMT also provides HasApproximateTangentSpaceAt.unique and ae_eq_const_of_weak_coordinate_derivatives_zero (C¹ test functions).
- SimonGMT has no area formula on rectifiable carriers, no C¹ approximation theorem, and no rectifiable⇒C¹-cover direction of Ch. 3 Lemma 1.2 (searches found no match; the SubmanifoldCover header confirms this). The new child therefore proves Simon 2.4–2.5 from Lipschitz bi-Lipschitz pieces.
- Mathlib provides normDet_sq_eq_det_gram, normDet_comp, LinearMap.euclideanHausdorffMeasure_image, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Rademacher's theorem, Besicovitch density, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, lintegral_withDensity_eq_lintegral_mul_non_measurable and EventuallyEq.fderiv_eq.

Lean statement of the new child. normDet, weightedAreaFiberSum, areaJacobianAt and tangentialJacobian are not in the import closure of GMT.Ch07.Submission. The new type therefore writes the Jacobian as Real.sqrt (Matrix.det (Matrix.of Gram)) and the fibre sum as a tsum over a subtype. GramCheck.lean proves that this equals normDet of the restricted derivative (axioms propext, Classical.choice, Quot.sound).

DAG. The related other-branch nodes dpf_rectifiable_bilipschitz_pieces and dpf_approxTangent_ae_bilipschitz_piece are not comparator-accepted, so they are not reused; their arguments are re-proved inside the new child. Accepted lemmas cited by children (imrep_approxTangent_starProjection_aesm, dtc_*) have DAG types matching their uses.

Names. No idtp_* name occurs in dag.json, in other nodes' decompositions or in any worktree's GMT sources, so the 11 names are unreserved.

Lean check. All 11 statements elaborate, and the hypothesis-only assembly proves IntegerDensityAndTangentPlanes. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
