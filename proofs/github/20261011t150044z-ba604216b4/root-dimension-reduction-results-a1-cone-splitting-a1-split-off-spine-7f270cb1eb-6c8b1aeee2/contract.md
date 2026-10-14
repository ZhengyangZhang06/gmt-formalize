<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1 -->

## Theorem `Submission.dimred_cs_sos_minimality_transfer`

Data:
- P, n ∈ ℕ; L ⊆ ℝ^P a linear subspace with 1 ≤ d := dim L < n; m := n − d ≥ 1.
- f = (f_1, …, f_d) an orthonormal family in L.
- S ∈ 𝒟_n(ℝ^P), minimizing in ℝ^P (IsMinimizingIn S univ), with an integer multiplicity representation R (μ := R.measure).
- S₀ ∈ 𝒟_m(ℝ^P) with an integer multiplicity representation R₀ (μ₀ := R₀.measure).
Hypotheses:
- ∂S₀ = 0 (BoundaryVanishes S₀) and μ₀(ℝ^P ∖ L^⊥) = 0;
- measure identity: μ(A) = ∫_L μ₀(A − t) dH^d(t) for every Borel A;
- product formula: S(ω) = ∫_L currentEval S₀ (y ↦ ♭(ω(t + y))) dH^d(t) for every test n-form ω and every map ♭ : Λ^n → Λ^m with (♭α)(v) = α(f_1, …, f_d, v_1, …, v_m) (Lean: α (Fin.append f v ∘ Fin.cast _)).
Conclusion: S₀ is minimizing in L^⊥ (IsMinimizingIn S₀ L^⊥). That is, S₀ is integer multiplicity, and M_W(S₀) ≤ M_W(S₀') whenever:
- W ⊆ ℝ^P is open with compact closure;
- S₀' is integer multiplicity with ∂S₀' = ∂S₀;
- spt(S₀' − S₀) is a compact subset of L^⊥ ∩ W.

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4249

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4885, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1310, https://github.com/ZhengyangZhang06/gmt-formalize/issues/861, https://github.com/ZhengyangZhang06/gmt-formalize/issues/987, https://github.com/ZhengyangZhang06/gmt-formalize/issues/982, https://github.com/ZhengyangZhang06/gmt-formalize/issues/781

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7883, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4729, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8622, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8627, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8631, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8636, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8638, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8642, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8643, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8645

## Lean problem

Declaration: `Submission.dimred_cs_sos_minimality_transfer`

```lean
∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (f : Fin (Module.finrank ℝ L) → Euclid P) (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (hd : Module.finrank ℝ L < n), 0 < Module.finrank ℝ L → Orthonormal ℝ f → (∀ i, f i ∈ L) → IsMinimizingIn S univ → R.Represents S → R₀.Represents S₀ → BoundaryVanishes S₀ → R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) (n - Module.finrank ℝ L), (∀ (α : Covector (Euclid P) n) (v : Fin (n - Module.finrank ℝ L) → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[Module.finrank ℝ L]) → IsMinimizingIn S₀ (Lᗮ : Set (Euclid P))
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- p := L.starProjection and q := Lᗮ.starProjection; t^a(x) := ⟨f_a, x⟩, so p(x) = Σ_a t^a(x)f_a.
- H^j := μHE[j]; on j-dimensional subspaces it is Lebesgue measure (isometry invariance and EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so in the coordinates t^a, H^d⌞L is Lebesgue measure on ℝ^d.
- M_W(T) := T.massOn W and M(T) := M_{ℝ^P}(T). For an IM current T, μ_T is the measure of a representation; it is independent of the representation by (F3).
- Translates: (τ_vT)(ω) := T(ω(· + v)) = currentEval (blowUp T (−v) 1) ω. Translating an IMRep by v (carrier + v, mult and orient composed with · − v) gives an IMRep of τ_vT with the translated measure; approximate tangent spaces translate. Mass is translation invariant.
- Sums of currents are written A + B := A − (0 − B), since GeometricCurrentOn has only Sub and Zero. Mass is subadditive, M_W(A + B) ≤ M_W(A) + M_W(B), directly from the sup definition of massOn.
Sibling children used:
- cone_filling_subspace;
- the accepted declarations (reuse siblings):
 (F1) imrep_represents_massOn_eq_measure: M_W(T) = μ_T(W) for open W;
 (F3) imrep_measure_eq_of_represents_same_current;
 (F4) rsd_isIntegerMultiplicity_int_combination: if T₁, T₂ are IM and T(ω) = p₁T₁(ω) + p₂T₂(ω) for all ω (p_i ∈ ℤ), then T is IM;
 (F6) imrep_carrier_sdiff_support_null: H^j(R.carrier ∖ spt T) = 0;
 (F7) dtc_imrep_current: every IMRep represents some current.
 Facts for an IM current T with representation R = (M_T, θ_T, ξ_T):
 (a) T(γ) = ∫_{M_T} θ_Tξ_T(γ) dH = 0 if γ vanishes on spt T, by (F6);
 (b) μ_T(ℝ^P ∖ spt T) = ∫_{M_T ∖ spt T} θ_T dH = 0, by (F6);
 (c) if μ_T(O) = 0 for an open set O, then T vanishes on test forms supported in O, because the integrand is supported in M_T ∩ O, a null set. Every point of O has a ball with compact closure inside O, so spt T ∩ O = ∅. This is immediate from the representation.
Imports. The area formula in Part I, step I.3, is SimonGMT weighted_area_formula_lipschitz_injOn and area_image_compl_regularSet_eq_zero, in Poincare.SimonGMT.Chapter02.AreaLipschitz, outside the contract import closure. The node that formalizes that step needs `import Poincare.SimonGMT.Chapter02.AreaLipschitz`. It is inherited through the dependency merge via cone_filling_subspace ← lipschitz_tangent, which must add it. Otherwise add it in an assembly (non-leaf) proof, since machine leaves cannot add imports; precedent: the accepted parent dtc_isIntegerMultiplicity_sub. All other facts are in scope after `import GMT.Ch07.Submission`.

PART I. Tools.
I.1 (Interior product with an orthonormal frame.) Let g = (g_1, …, g_k) be orthonormal and k + m' = n' (formalize with an explicit m' and h : n' = k + m', to avoid degree casts).
 - For α ∈ Λ^{n'} define ♭_gα(v) := α(Fin.append g v ∘ Fin.cast h), i.e. α(g_1, …, g_k, v_1, …, v_{m'}).
 - Updating one entry of v updates one entry of Fin.append g v (Fin.addCases). Hence ♭_gα is multilinear, and alternating because equal entries stay at distinct indices; and |♭_gα(v)| ≤ ‖α‖∏|v_j|.
 - So ♭_g : Λ^{n'} →L[ℝ] Λ^{m'} is continuous linear with ‖♭_g‖ ≤ 1 (LinearMap.mkContinuous).
 - For a test n'-form ω, ♭_gω(t + ·) := y ↦ ♭_g(ω(t + y)) is a test m'-form with tsupport ⊆ tsupport ω − t.
 - For g = f, k = d and m' = m, any ♭ as in the hypothesis equals ♭_f, both being given by the same formula. So the product formula reads S(ω) = ∫_L S₀(♭_fω(t + ·)) dt.
I.2 (Tangent planes inside a subspace.) If H^j(M' ∖ V) = 0 for a linear subspace V, y ∈ V and HasApproximateTangentSpaceAt j M' y Q, then Q ⊆ V.
 Proof:
 - Suppose z ∈ Q ∖ V. Then ρ := dist(z, V)/2 > 0 and j ≥ 1. Let φ(x) := max(0, 1 − |x − z|/ρ); it vanishes on V, and φ ≥ 1/2 on B(z, ρ/2).
 - For r > 0, η := η_{y,r} preserves V, so η(M') ∖ V = η(M' ∖ V), which has H^j-measure r^{−j}H^j(M' ∖ V) = 0.
 - Hence 0 ≤ ∫_{η(M')} φ dH^j ≤ H^j(η(M') ∖ V) = 0, and the tangent limit gives ∫_Q φ dH^j = 0.
 - This contradicts ∫_Q φ dH^j ≥ (1/2)H^j(Q ∩ B(z, ρ/2)) > 0, since H^j⌞Q is Lebesgue measure on Q.
I.3 (Product with a Borel subset of a frame span.) Let g be orthonormal (k vectors), G := span g, and k + m' = n'. Let E ⊆ G be Borel and A an IM m'-current with an IMRep R_A = (M_A, θ_A, ζ_A) such that μ_A(ℝ^P ∖ G^⊥) = 0. Then there is an IM n'-current [[E]] ×_g A, with an IMRep R_B, such that for every test n'-form ω and Borel C:
 ([[E]] ×_g A)(ω) = ∫_E A(♭_gω(t + ·)) dH^k(t) and R_B.measure(C) = ∫_E μ_A(C − t) dH^k(t).
 Proof. Write q_G := (G^⊥).starProjection and ι(a) := Σ_i a_ig_i, an isometry ℝ^k → G.
 (a) Reduction. H^{m'}(M_A ∖ G^⊥) ≤ μ_A(ℝ^P ∖ G^⊥) = 0. Replace M_A by M_A ∩ G^⊥; action, measure and all blow-up integrals (hence approximate tangent spaces) are unchanged. By I.2 (V = G^⊥), for H^{m'}-a.e. y ∈ M_A the approximate tangent space T_y oriented by ζ_A(y) satisfies T_y ⊆ G^⊥.
 (b) Product formula for H^{n'} (PM). For Borel E ⊆ G, Borel M ⊆ G^⊥ countably m'-rectifiable and locally H^{m'}-finite, and Borel g ≥ 0:
 ∫_{E+M} g dH^{n'} = ∫_E ∫_M g(t + y) dH^{m'}(y) dH^k(t), where E + M = p_G⁻¹(E) ∩ q_G⁻¹(M) is Borel.
 - Null part: if H^{m'}(N) = 0 then H^{n'}(E + N) = 0. By σ-additivity let E lie in a cube of side ℓ in G. Cover N by sets C_i of positive diameters < δ ≤ 1 with Σ_i (diam C_i)^{m'} < ε; enlarge degenerate sets slightly, keeping the sum < ε. Cover the cube by ≤ (ℓ/diam C_i + 1)^k subcubes of side diam C_i; each subcube plus C_i has diameter ≤ (√k + 1) diam C_i. Hence the H^{n'}_{(√k+1)δ}-premeasure of E + N is ≤ c Σ_i (ℓ^k (diam C_i)^{m'} + (diam C_i)^{n'}) ≤ c(ℓ^k + 1)ε. Let ε → 0, then δ → 0.
 - Rectifiable part: cover M up to an H^{m'}-null set by disjoint Borel images Φ_l(T_l), with Φ_l Lipschitz and injective on T_l (bi-Lipschitz pieces via Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, with tolerance c_A/2 for injective A and 1 otherwise; Lusin–Souslin; SimonGMT area_image_compl_regularSet_eq_zero). Replace Φ_l by q_G∘Φ_l, which equals Φ_l on T_l and has values in G^⊥.
 - G_l(a, u) := ι(a) + Φ_l(u) on ℝ^k × ℝ^{m'} is Lipschitz and injective on ι⁻¹E × T_l. At a.e. point DG_l = [ι | DΦ_l(u)] with range DΦ_l(u) ⊆ G^⊥ ⊥ G, so its Gram matrix is diag(I, DΦ_l*DΦ_l) and JG_l = JΦ_l.
 - The area formula for G_l and Φ_l, Tonelli, summation over l and the null part give (PM).
 (c) The product IMRep R_B. Put M_B := E + M_A, θ_B := θ_A∘q_G and ξ_B(x)(α) := ζ_A(q_G x)(♭_gα).
 - M_B is countably n'-rectifiable: covered by E + N and the Lipschitz images G_l(ℝ^{n'}).
 - θ_B ≥ 1 on M_B and θ_B is locally integrable: by (PM), ∫_{M_B∩K} θ_B ≤ H^k(p_GK)·∫_{M_A∩q_GK} θ_A < ∞.
 - ξ_B is a.e.-strongly measurable: compose a Borel version of ζ_A with q_G and ♭_g; the exceptional set is null by (PM).
 - Tangent planes. Let x = t + y with t a Lebesgue density point of E (in G) and y ∈ M_A having T_y ⊆ G^⊥. Then η_{x,r}(M_B) = η_{t,r}(E) + η_{y,r}(M_A). By (PM), for φ ∈ C_c with spt φ ⊆ B_ρ, ∫_{η_{x,r}(M_B)} φ = ∫_{η_{t,r}E} Φ_r(s) dH^k(s) with Φ_r(s) := ∫_{η_{y,r}M_A} φ(s + z) dH^{m'}(z). As r ↓ 0:
  - Φ_r(s) → ∫_{T_y} φ(s + z) dH^{m'}(z) for each s;
  - |Φ_r(s)| ≤ ‖φ‖_∞ H^{m'}(η_{y,r}M_A ∩ B_ρ) is bounded and vanishes for |s| ≥ ρ, because |s + z|² = |s|² + |z|²;
  - 1_{η_{t,r}E} → 1_G in L¹_loc(G).
  Dominated convergence gives the limit ∫_G ∫_{T_y} φ(s + z) = ∫_{G⊕T_y} φ dH^{n'}, by (PM) for subspaces. So M_B has approximate tangent space G ⊕ T_y at x (finrank k + m' = n').
 - Orientation. If ζ_A(y) = ±(β ↦ β(τ)) with τ an orthonormal basis of T_y, then ξ_B(x)(α) = ±α(Fin.append g τ ∘ Fin.cast h), and Fin.append g τ is an orthonormal basis of G ⊕ T_y. The bad x (t not a density point, or y bad) lie in (Z_E + M_A) ∪ (E + Z_A) with Z_E, Z_A Borel null sets, which is H^{n'}-null by (PM).
 - So R_B := (M_B, θ_B, ξ_B) is an IMRep. Let [[E]] ×_g A be a current it represents (F7).
 (d) Formulas. By (PM) applied to θ_B1_C, R_B.measure(C) = ∫_E μ_A(C − t) dt. For the action, the integrand θ_Bξ_B(ω) is integrable, being bounded by θ_B‖ω‖_∞1_{tsupport ω}. By (PM) on its positive and negative parts,
 R_B.action(ω) = ∫_E ∫_{M_A} θ_Aζ_A(♭_gω(t + y)) dH^{m'}(y) dt = ∫_E A(♭_gω(t + ·)) dt. ∎(I.3)

PART II. The comparison.
1. (Integer multiplicity.) S₀ is represented by R₀, so it is integer multiplicity. By (F6c), spt S₀ ⊆ L^⊥, since μ₀ vanishes on the open set ℝ^P ∖ L^⊥.
2. (A competitor and the defect δ.) Let W₀, S₀' be as in the conclusion, with K₀ := spt(S₀' − S₀) compact and K₀ ⊆ L^⊥ ∩ W₀. As m ≥ 1, SameBoundary means ∂S₀' = ∂S₀ = 0. By (F1), M_{W₀}(S₀) = μ₀(W₀) ≤ μ₀(cl W₀) < ∞. Suppose, for contradiction, that M_{W₀}(S₀') < M_{W₀}(S₀), and put δ := M_{W₀}(S₀) − M_{W₀}(S₀') ∈ (0, ∞).
3. (The cycle X₀ and its cone Y₀.)
 - X₀ := S₀' − S₀ is IM by (F4), with ∂X₀ = 0, spt X₀ = K₀ compact and K₀ ⊆ L^⊥.
 - By cone_filling_subspace (V = L^⊥), there is an IM Y₀ ∈ 𝒟_{m+1}(ℝ^P) with ∂Y₀ = X₀, spt Y₀ compact and spt Y₀ ⊆ L^⊥.
 - M(Y₀) = μ_{Y₀}(ℝ^P) = μ_{Y₀}(spt Y₀) < ∞, by (F1) and (F6b).
 - Concentration. spt S₀' ⊆ spt S₀ ∪ K₀ ⊆ L^⊥: if a test form vanishes near spt S₀ ∪ K₀, then S₀ and X₀ vanish on it by (F6a). So by (F6b), μ_{S₀'}, μ_{X₀} and μ_{Y₀} vanish off L^⊥.
4. (Products used.)
 - With g = f (k = d): for Borel E ⊆ L and A ∈ {S₀, S₀', X₀} (m' = m, n' = n), and for A = Y₀ (m' = m + 1, n' = n + 1, no degree cast needed), I.3 gives IM currents [[E]] × A := [[E]] ×_f A with ([[E]] × A)(ω) = ∫_E A(♭_fω(t + ·)) dt and μ_{[[E]]×A}(C) = ∫_E μ_A(C − t) dt.
 - Faces. For a ∈ {1, …, d} let f^{(a)} := (f_1, …, f̂_a, …, f_d), orthonormal, with span L_a, dim d − 1, and L^⊥ ⊆ L_a^⊥. I.3 with g = f^{(a)}, k = d − 1 and m' = m + 1 (n' = n) gives [[E]] ×_a Y₀ for Borel E ⊆ L_a, with M([[E]] ×_a Y₀) = H^{d−1}(E)·M(Y₀) (F1 on ℝ^P). For d = 1 the frame is empty, E = {0}, and the product is Y₀ itself.
5. (Boundary of the cube product.) For r > 0 let:
 - Q_r := {t ∈ L : |t^a| ≤ r ∀a}, with H^d(Q_r) = (2r)^d;
 - Q'_a := {Σ_{b≠a} s^bf_b : |s^b| ≤ r} ⊆ L_a, with H^{d−1}(Q'_a) = (2r)^{d−1};
 - P_a := [[Q'_a]] ×_a Y₀.
 Define E'_r := Σ_{a=1}^d (−1)^{a−1}(τ_{rf_a}P_a − τ_{−rf_a}P_a). It is IM by (F4) and translation, and M(E'_r) ≤ Σ_a 2M(P_a) = 2d(2r)^{d−1}M(Y₀).
 Claim: ∂([[Q_r]] × Y₀) = E'_r + (−1)^d [[Q_r]] × X₀.
 Proof. Let ω be a test n-form and ♭ := ♭_f on Λ^{n+1} (m' = m + 1). Use dω(x)(v_0, …, v_n) = Σ_i (−1)^i Dω(x)[v_i](…v̂_i…) (SimonGMT exteriorDerivative_apply) with v = (f_1, …, f_d, w_1, …, w_{m+1}). For every x and w:
 ♭(dω(x))(w) = Σ_a (−1)^{a−1} D_{f_a}[♭_{f^{(a)}}ω](x)(w) + (−1)^d d(♭_fω)(x)(w).
 The terms with v_i = f_a (i = a − 1) give the first sum. The terms with v_i = w_j (i = d + j − 1) give (−1)^{d+j−1}D_{w_j}[♭_fω](x)(ŵ_j), and Σ_j (−1)^{j−1}D_{w_j}[♭_fω](x)(ŵ_j) = d(♭_fω)(x)(w). Integrate over Q_r:
 - Second term: d(♭_fω)(t + ·) = d[♭_fω(t + ·)] and Y₀(dγ) = (∂Y₀)(γ) = X₀(γ), giving (−1)^d([[Q_r]] × X₀)(ω).
 - First term: g_a(t) := Y₀(♭_{f^{(a)}}ω(t + ·)) is C¹ with ∂_{t^a}g_a(t) = Y₀(D_{f_a}[♭_{f^{(a)}}ω](t + ·)): difference quotients of t ↦ ♭_{f^{(a)}}ω(t + ·) converge in the test-form topology, and Y₀ is continuous. By Fubini in the coordinates t^b and the fundamental theorem of calculus in t^a,
 ∫_{Q_r} ∂_{t^a}g_a dt = ∫_{Q'_a} [g_a(s + rf_a) − g_a(s − rf_a)] dH^{d−1}(s) = (τ_{rf_a}P_a)(ω) − (τ_{−rf_a}P_a)(ω).
 Summing gives ([[Q_r]] × Y₀)(dω) = E'_r(ω) + (−1)^d([[Q_r]] × X₀)(ω).
6. (The competitor for S.) Put Z_r := (−1)^d ∂([[Q_r]] × Y₀) = [[Q_r]] × X₀ + (−1)^d E'_r (step 5).
 - Z_r is IM, by (F4).
 - ∂Z_r = 0, since ∂∂ = 0 (CurrentOn.boundary_boundary).
 - spt Z_r ⊆ spt([[Q_r]] × Y₀) ⊆ Q_r + spt Y₀. The measure of [[Q_r]] × Y₀ vanishes off the closed set Q_r + spt Y₀ (I.3 and (F6b)); then apply (F6c), and use that the support of a boundary lies in the support.
 Choose an open ball B = B_ρ(0) ⊇ cl(W₀) ∪ spt Y₀ (compact). Let C_{r+1} := {t ∈ L : |t^a| < r + 1 ∀a} and W := {x : p(x) ∈ C_{r+1}, q(x) ∈ B}.
 - W is open, and cl W ⊆ {x : |t^a(x)| ≤ r + 1, |q x| ≤ ρ} is compact.
 - spt Z_r ⊆ Q_r + spt Y₀ ⊆ W, since spt Y₀ ⊆ B ∩ L^⊥.
 Let S' := S + Z_r. It is IM (F4); ∂S' = ∂S (n ≥ 2, boundary linear); and S' − S = Z_r, so spt(S' − S) is a compact subset of W = univ ∩ W. Minimality of S gives:
 (MIN) M_W(S) ≤ M_W(S').
7. (Mass of S.) For t ∈ L and y ∈ L^⊥, t + y ∈ W iff t ∈ C_{r+1} and y ∈ B. Hence μ₀(W − t) = 1_{C_{r+1}}(t)μ₀(B), by concentration on L^⊥. By (F1) and the measure identity,
 M_W(S) = μ(W) = ∫_L μ₀(W − t) dt = (2r + 2)^d μ₀(B).
8. (Mass of S'.) For a test n-form ω, the function t ↦ S₀(♭_fω(t + ·)) is continuous and vanishes unless t ∈ p(tsupport ω), by (F6a) and spt S₀ ⊆ L^⊥; so it is integrable. With S₀' = S₀ + X₀:
 (S + [[Q_r]] × X₀)(ω) = ∫_L S₀(♭_fω(t + ·)) dt + ∫_{Q_r} X₀(♭_fω(t + ·)) dt = ∫_{L∖Q_r} S₀(♭_fω(t + ·)) dt + ∫_{Q_r} S₀'(♭_fω(t + ·)) dt.
 Hence S' = [[L ∖ Q_r]] × S₀ + [[Q_r]] × S₀' + (−1)^d E'_r. By subadditivity, (F1) and step 4, as in step 7:
 M_W(S') ≤ μ_{[[L∖Q_r]]×S₀}(W) + μ_{[[Q_r]]×S₀'}(W) + M(E'_r)
 ≤ ((2r + 2)^d − (2r)^d)μ₀(B) + (2r)^d μ_{S₀'}(B) + 2d(2r)^{d−1}M(Y₀).
9. (Comparing μ_{S₀'} and μ₀.) On the open set U' := ℝ^P ∖ K₀, S₀' and S₀ agree: (S₀' − S₀)(γ) = 0 if tsupport γ ⊆ U', by (F6a) for X₀.
 - Restrict a representation R' of S₀' and R₀ to U': carriers ∩ U', same mult and orient. These are IMReps in U': Borel, rectifiable, locally integrable, and approximate tangent spaces at points of the open set U' are unchanged.
 - Both represent the restricted current, so by (F3), μ_{S₀'}(C) = μ₀(C) for Borel C ⊆ U'.
 - As K₀ ⊆ W₀ ⊆ B, and using (F1) for W₀:
 μ_{S₀'}(B) − μ₀(B) = μ_{S₀'}(K₀) − μ₀(K₀) = μ_{S₀'}(W₀) − μ₀(W₀) = M_{W₀}(S₀') − M_{W₀}(S₀) = −δ.
 All these quantities are finite.
10. (Contradiction.) By steps 7–9,
 M_W(S') − M_W(S) ≤ −δ(2r)^d + 2d(2r)^{d−1}M(Y₀) = (2r)^{d−1}(2d M(Y₀) − 2rδ) < 0
 for r > d M(Y₀)/δ. This contradicts (MIN). Hence M_{W₀}(S₀) ≤ M_{W₀}(S₀') for all such competitors, and with step 1, S₀ is minimizing in L^⊥. ∎

## Key steps

1. Tools: the interior product ♭_g with an orthonormal frame, tangent planes inside a subspace, and the IM product [[E]] ×_g A (E ⊆ span g, A concentrated on (span g)^⊥) with product measure, via the Hausdorff product formula and dtc_imrep_current.
2. A competitor S₀' with smaller mass in W₀ gives an IM cycle X₀ = S₀' − S₀ in L^⊥ ∩ W₀; cone_filling_subspace gives Y₀ with ∂Y₀ = X₀ and spt Y₀ ⊆ L^⊥.
3. Stokes in each t^a gives ∂([[Q_r]] × Y₀) = E'_r + (−1)^d[[Q_r]] × X₀, with E'_r the face terms of mass ≤ 2d(2r)^{d−1}M(Y₀).
4. S' := S + (−1)^d∂([[Q_r]] × Y₀) = [[L∖Q_r]] × S₀ + [[Q_r]] × S₀' + (−1)^d E'_r is an admissible competitor in the box W.
5. Mass bookkeeping with M_W = μ(W) gives M_W(S') − M_W(S) ≤ −δ(2r)^d + 2d(2r)^{d−1}M(Y₀) < 0 for large r, contradicting minimality of S.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical; sha256 e4148e7f…)`
- `grep -n -E '^(theorem|def|structure|abbrev|instance)' over SimonGMT Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,Forms}.lean; head of Chapter06/{Product,WedgeForms,GeometricPointProduct,Representation}.lean`
- `sed -n 1,140p SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap); ls Chapter02 (AreaFormula, AreaLipschitz, CoareaLinear, CoareaProjection)`
- `grep -n -E 'theorem|def ' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_zero, Submodule.measurePreserving_measurableEquivProd, AffineSubspace.euclideanHausdorffMeasure_eq_lintegral, euclideanHausdorffMeasure_homothety_image)`
- `lake env lean /tmp/sos-decomp/Probe.lean and Probe2.lean: #check after import GMT.Ch07.Submission (in scope: ContinuousAlternatingMap.curryLeft, MultilinearMap.alternatization, ContDiffBump, lintegral_prod, MeasurableSpace.induction_on_inter, LipschitzWith.ae_differentiableAt, LipschitzOnWith.extend_real, MeasurableSet.image_of_continuousOn_injOn, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Besicovitch.ae_tendsto_measure_inter_div, Besicovitch.ae_tendsto_rnDeriv, VitaliFamily.ae_tendsto_average_norm_sub, exteriorDerivative_apply, CurrentOn.boundary_boundary; not in scope: covectorWedge, GeometricCurrentOn.pointProduct, Add/Neg/SMul on GeometricCurrentOn, SimonGMT AreaLipschitz lemmas, kernel API)`
- `python3 over dag.json: cone_splitting-a1 siblings and statuses; accepted IMRep lemmas (dtc_imrep_current, imrep_weighted_orient_indicator_ae_eq, imrep_measure_eq_of_represents_same_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination, dtc_blowUp_imrep, dtc_vanish_off_support); emf_exists_cone_filling (decomposing, no support conclusion); dpf_ bi-Lipschitz pieces (not accepted); occurrences of dimred_cs_sos in dag.json: 0`
- `git show dd88db7, 9203aee, 77fcc7d: GMT/Ch07/Submission.lean (listed dependencies are merged into a child's Submission; the accepted parent dtc_isIntegerMultiplicity_sub adds a SimonGMT import)`
- `read nodes/root-dimension-reduction-results-a1-cone-splitting-a1/{parent-supplied-natural-proof.md,decomposition-v1.json} (reuse precedent), nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-supplied-natural-proof.md (cone construction adapted for cone_filling_subspace), and the handoffs of the 6 reused accepted nodes`
- `lake env lean /tmp/sos-decomp/CheckFinal.lean (12 child types as Submission stubs, assembly of dimred_cs_split_off_spine including the finrank L = 0 case, #print axioms) and Check5.lean (cone_filling_subspace instantiated at degree n − finrank L)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-imrep-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-vect-8c0391929c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mass-equals-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1/parent-child-handoff.json`
- `/tmp/sos-decomp/CheckFinal.lean`

Pins match. The snapshot is at project b4d606d (= workspace HEAD) with mathlib 25730c7c and SimonGMT 2b36630, and the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the library lacks. SimonGMT has none of:
- slicing;
- Cartesian products of currents beyond point products;
- a Lipschitz push-forward;
- a coarea formula on rectifiable sets (only the linear one).
WedgeForms, the area formula (Chapter02.AreaLipschitz) and Mathlib's kernel API are outside the contract import closure. GeometricCurrentOn has only Sub and Zero instances.
Consequences for the split:
- no child type mentions products or wedges;
- the product structure is passed as an action identity over a quantified interior product ♭ (Fin.append f v ∘ Fin.cast), plus the measure identity and concentration on L^⊥;
- the area-formula import is assigned to the lipschitz_tangent subtree, from which dependents inherit it (precedent: accepted dtc_isIntegerMultiplicity_sub added a SimonGMT import; leaves cannot add imports).
Mathlib facts the proofs use are all in scope, including the μHE Fubini lemmas Submodule.measurePreserving_measurableEquivProd and AffineSubspace.euclideanHausdorffMeasure_eq_lintegral.

Reuse. The parent dependency im_mass_measure, cited by the supplied proof, is not accepted. Six comparator-accepted declarations are reused in its place, with byte-identical types and commits present: dtc_imrep_current 642d745, imrep_weighted_orient_indicator_ae_eq 2d0f5bb, imrep_measure_eq_of_represents_same_current 6907c2c, imrep_represents_massOn_eq_measure c004e5e, imrep_carrier_sdiff_support_null d15b5cf, rsd_isIntegerMultiplicity_int_combination 568bfe5. Listed dependencies are merged into a child's Submission.lean (checked on accepted commits).

No reuse:
- emf_exists_cone_filling is not accepted and lacks the support conclusion, so cone_filling_subspace is new; the construction is adapted from that node's proof.
- The dpf_ bi-Lipschitz/tangent lemmas are not accepted, so lipschitz_tangent is new.

Lean check. All 12 child types elaborate, and the frozen parent type is proved from them, including the finrank L = 0 case. Axioms are propext, sorryAx (stubs only), Classical.choice and Quot.sound. The 6 new dimred_cs_sos_ names are unused elsewhere.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
