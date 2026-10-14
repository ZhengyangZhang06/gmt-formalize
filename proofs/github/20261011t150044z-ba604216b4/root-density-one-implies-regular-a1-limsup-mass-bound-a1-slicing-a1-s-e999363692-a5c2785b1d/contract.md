<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1 -->

## Theorem `Submission.dor_lmbs_imrep_slice_family`

Assume (TL), the frozen statement of the sibling node tangent_locality (Lean dor_lmb_approx_tangent_locality, a sibling of the node being decomposed): for all P, n ∈ ℕ, every open U ⊆ ℝ^P and all Borel sets A ⊆ B ⊆ U with Hⁿ(B ∩ K) < ∞ for every compact K ⊆ U (Hⁿ = μHE[n]), for Hⁿ-a.e. x ∈ A and every linear subspace Q of ℝ^P: B has approximate tangent space Q at x (HasApproximateTangentSpaceAt n B x Q, Simon Ch. 3, 1.4) if and only if A has approximate tangent space Q at x.
Let P, n ∈ ℕ, U ⊆ ℝ^P open, T ∈ 𝒟_{n+1}(U) represented by the integer multiplicity triple RT = (M, θ, ξ) in U (IMRep U (n+1), RT.Represents T), ∂T ∈ 𝒟_n(U) represented by the integer multiplicity triple RB = (M', θ', ξ') in U (IMRep U n, RB.Represents T.boundary), and let f : ℝ^P → ℝ be L-Lipschitz (L ≥ 0). Then there is a family (R_t)_{t∈ℝ} of integer multiplicity triples in U of dimension n (Rs : ℝ → IMRep U n), R_t = (M_t, θ_t, ξ_t), such that:
(1) M_t ⊆ f⁻¹(t) for every t ∈ ℝ;
(2) for every Borel set W ⊆ ℝ^P, the function t ↦ μ_{R_t}(W) (R_t.measure W = ∫_{M_t∩W} θ_t dHⁿ) is a.e.-measurable for Lebesgue measure on ℝ, and ∫_ℝ μ_{R_t}(W) dt ≤ L·μ_{RT}(W) (lower Lebesgue integral in [0, ∞], μ_{RT} = RT.measure = θH^{n+1}⌞M);
(3) for every ω ∈ 𝒟ⁿ(U), the real function s ↦ τ(R_s)(ω) := ∫_{M_s} θ_s⟨ω, ξ_s⟩ dHⁿ (R_s.action ω) is Lebesgue integrable on ℝ;
(4) for every ω ∈ 𝒟ⁿ(U) and all real a < b, writing γ_{a,b}(s) := min{1, max{0, (b − s)/(b − a)}},
  ∫_a^b τ(R_s)(ω) ds = (b − a)·( ∫_M θ·γ_{a,b}(f)·⟨dω, ξ⟩ dH^{n+1} − ∫_{M'} θ'·γ_{a,b}(f)·⟨ω, ξ'⟩ dHⁿ ),
where dω = exteriorDerivative ω, ⟨α, ζ⟩ = ζ(α), and the left side is the interval integral ∫ s in a..b.
Remark (no additional claim): for a.e. t, R_t is Simon's slice ⟨T, f, t⟩ = τ(M_t, θ_t, ξ_t) of Ch. 6, 4.4, and (4) is the identity obtained in the proof of 4.5(2) for the cut-off γ_{a,b} (t = b, ε = b − a) after applying the co-area formula 4.2.

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4724

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5994, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5996, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6000, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6003, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6007, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6015, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6024, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6037, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6053, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6065, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6076, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6088

## Lean problem

Declaration: `Submission.dor_lmbs_imrep_slice_family`

```lean
(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Rs : ℝ → IMRep U n, (∀ t, (Rs t).carrier ⊆ f ⁻¹' {t}) ∧ (∀ W : Set (Euclid P), MeasurableSet W → AEMeasurable (fun t => (Rs t).measure W) ∧ ∫⁻ t, (Rs t).measure W ≤ (L : ℝ≥0∞) * RT.measure W) ∧ (∀ ω : TestFormOn U n, Integrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) ∧ ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, §4: Lemma 4.1, Remark 4.2, 4.3, Definition 4.4 and the printed proofs of Lemma 4.5(1),(2) (chapter-06.txt lines 1156–1325); Ch. 3, Lemma 1.2, Remarks 1.3 and 1.5, the proof of Theorem 1.6 and §2 (2.1, 2.4, 2.8–2.10) (chapter-03.txt lines 1–440); Ch. 2, Theorem 1.2 (Lipschitz extension), 1.4 (Rademacher), 1.5 (C¹ approximation), the area formula (§§3–4) and the co-area formula 6.3/6.6 (chapter-02.txt lines 160–175, 1405–1530). This is steps 1, 2, 4(b)–(c) and 5(a)–(f) of the parent proof, with the details filled in. The hypothesis (TL) replaces the parent's citations of Ch. 3, Remark 1.5(2) ("compare sibling tangent_locality").

Notation. M, θ, ξ are the fields of RT and M', θ', ξ' those of RB. Hᵐ = μHE[m]. μ_T := RT.measure = θH^{n+1}⌞M. For a k-covector α, ‖α‖ is its operator norm. For a vector v, v♭ := ⟨v, ·⟩. For a 1-covector β and an n-covector α, β∧α is the (n+1)-covector (β∧α)(v₀,…,vₙ) = Σ_{i=0}^{n} (−1)^i β(vᵢ) α(v₀,…,v̂ᵢ,…,vₙ), i.e. Mathlib's alternatizeUncurryFin (β.smulRight α). Since exteriorDerivative = extDeriv = alternatizeUncurryFin ∘ fderiv, d(hω) = dh∧ω + h·dω for a C^∞ function h and a C^∞ n-form ω. A unit orientation of a k-dimensional subspace Q is a k-vector ζ with ζ(α) = ±α(τ₁,…,τ_k) for all α, for some orthonormal basis τ of Q (IsUnitOrientationOf ζ Q). τ(R)(ω) := R.action ω. Fix a < b when (4) is proved, with γ := γ_{a,b}.

0. Preliminaries.
 (a) If ζ is a unit orientation of a k-dimensional subspace Q, then |ζ(α)| ≤ ‖α‖ for every k-covector α, since |α(τ₁,…,τ_k)| ≤ ‖α‖·|τ₁|⋯|τ_k| = ‖α‖. If σ is any orthonormal basis of Q, then ζ(α) = ε·α(σ) for all α, with a sign ε ∈ {1, −1} independent of α. Indeed α restricted to Q^k is a multiple of the determinant, and the change of basis between two orthonormal bases has determinant ±1.
 (b) By the field `orients` of RT and uniqueness of approximate tangent spaces (Ch. 3, Remark 1.5(1)): for H^{n+1}-a.e. x ∈ M, the approximate tangent space T_xM exists (it equals approxTangentPlane (n+1) M x) and ξ(x) is a unit orientation of T_xM. The same holds for M', ξ'.
 (c) For every compact K ⊆ U: μ_T(K) = ∫_{M∩K} θ dH^{n+1} < ∞ (locallyIntegrable_mult). Since θ ≥ 1 on M, H^{n+1}(M ∩ K) ≤ μ_T(K). The same holds for RB.
 (d) Let β be a continuous (n+1)-form with tsupport β ⊆ K, K ⊆ U compact. Then x ↦ θ(x)ξ(x)(β(x)) is H^{n+1}⌞M-integrable, and |∫_{M∩E} θξ(β) dH^{n+1}| ≤ (sup‖β‖)·μ_T(K) for every Borel E. Measurability: ξ is a.e. strongly measurable, β is continuous, and evaluation is continuous bilinear. The bound follows from (a)–(c). The same holds for RB and continuous n-forms.
 (e) Fix compact sets K₁ ⊆ K₂ ⊆ … ⊆ U with K_i ⊆ int K_{i+1} and ⋃_i K_i = U. Every compact subset of U lies in some K_i.
 (f) Fix a Borel map ξ₀ : ℝ^P → Λ_{n+1}(ℝ^P) with ξ₀ = ξ H^{n+1}-a.e. on M (ξ is a.e. strongly measurable).

1. C¹ pieces (Ch. 3, Lemma 1.2 "only if", Remark 1.3; Ch. 2, Theorem 1.5). We construct pairwise disjoint Borel sets M_j ⊆ M (j ≥ 1) with H^{n+1}(M ∖ ⋃_j M_j) = 0, together with, for each j:
 - an open V_j ⊆ ℝ^{n+1} and compact sets C_j ⊆ int C'_j ⊆ C'_j ⊆ V_j;
 - a C¹ map ψ_j : V_j → U that is injective, has injective derivative everywhere, and is a homeomorphism onto ψ_j(V_j);
 - a C¹ function F_j : ℝ^{n+1} → ℝ,
 such that M_j ⊆ ψ_j(C_j) and f(ψ_j(y)) = F_j(y) for every y ∈ Y_j := ψ_j⁻¹(M_j).
 Construction.
 - By Lemma 1.2, M ⊆ N₀ ∪ ⋃_{l≥1} N_l with H^{n+1}(N₀) = 0 and each N_l an embedded C¹ (n+1)-dimensional submanifold.
 - Each N_l is covered by countably many local parametrizations ψ : V → ℝ^P (C¹, injective, injective derivative, homeomorphism onto a relatively open subset of N_l; Ch. 2, §4). Replacing V by the open set V ∩ ψ⁻¹(U) we may assume ψ(V) ⊆ U; this loses no point of M ⊆ U.
 - For each such ψ, cover V by countably many closed balls B̄ = B̄_r(c) with B̄_{2r}(c) ⊆ V. The function u := f∘ψ is Lipschitz on B̄_{2r}(c), because ψ is C¹ and hence Lipschitz there. Extend u|B̄ to a Lipschitz function on ℝ^{n+1} (Ch. 2, Theorem 1.2). Apply the C¹ approximation theorem (Ch. 2, 1.5) with ε = 1/k to get C¹ functions G_k with L^{n+1}(B̄ ∩ {u ≠ G_k}) < 1/k. Then B̄ ∖ ⋃_k {u = G_k} is L^{n+1}-null, and its image under ψ is H^{n+1}-null because ψ is Lipschitz on B̄.
 - Enumerate the data (ψ, B̄, k) as j = 1, 2, …. Put ψ_j := ψ, V_j := V, C_j := B̄ ∩ {u = G_k} (compact), C'_j := B̄_{2r}(c), F_j := G_k and E_j := ψ_j(C_j) (compact). Then M ∖ ⋃_j E_j is H^{n+1}-null.
 - Put M_j := (M ∩ E_j) ∖ ⋃_{i<j} E_i (Remark 1.3).
 Below we several times delete an H^{n+1}-null set from each M_j. Each exceptional set (from (TL), `orients`, ξ = ξ₀ a.e., density points, Rademacher) is first enlarged to a Borel H^{n+1}-null superset, which is possible because every null set of the measure H^{n+1}⌞M is contained in a measurable null set (MeasureTheory.exists_measurable_superset_of_null, applied to H^{n+1}⌞M). Deleting it keeps all the above properties, and we keep the name M_j.

2. Tangent planes on the pieces (Ch. 3, Remark 1.5(2), via (TL)). For y ∈ V_j put Q_j(y) := Dψ_j(y)(ℝ^{n+1}), an (n+1)-dimensional subspace. Claim: for H^{n+1}-a.e. x = ψ_j(y) ∈ M_j, M has approximate tangent space Q_j(y) at x.
 (a) S_j := ψ_j(C'_j) is compact, S_j ⊆ U and H^{n+1}(S_j) < ∞.
 (b) For y ∈ int C'_j, the set ψ_j(int C'_j) is relatively open in ψ_j(V_j), so S_j coincides near x = ψ_j(y) with the embedded C¹ submanifold ψ_j(V_j). Hence, as in the proof of Ch. 3, Theorem 1.6 "⇒" ("since x ∈ N_j and N_j is a C¹ submanifold, lim ∫_{η_{x,λ}(N_j)} f dHⁿ = ∫_{T_xN_j} f dHⁿ"), S_j has approximate tangent space Q_j(y) at x.
 (c) Apply (TL) with (A, B) = (M_j, S_j). These are Borel, M_j ⊆ S_j ⊆ U, and H^{n+1}(S_j ∩ K) < ∞. So for H^{n+1}-a.e. x ∈ M_j, M_j has approximate tangent space Q_j(y) at x.
 (d) Apply (TL) with (A, B) = (M_j, M). Here M is Borel, M ⊆ U, and H^{n+1}(M ∩ K) < ∞ by 0(c). So for H^{n+1}-a.e. x ∈ M_j, M has approximate tangent space Q_j(y), i.e. T_xM = Q_j(y).
 After deleting null sets (Step 1, using 0(b) and 0(f)), we may assume for every j and every x = ψ_j(y) ∈ M_j:
 - T_xM = Q_j(y);
 - ξ(x) = ξ₀(x);
 - ξ(x) is a unit orientation of T_xM.

3. Tangential gradient (Ch. 3, 2.1).
 Definition of g. For x = ψ_j(y) ∈ M_j, let g(x) ∈ Q_j(y) be the unique vector with ⟨g(x), Dψ_j(y)e⟩ = DF_j(y)e for all e ∈ ℝ^{n+1}. Explicitly g(x) = Dψ_j(y)G_j(y)⁻¹∇F_j(y), where G_j := Dψ_jᵀDψ_j. Put g := 0 off ⋃_j M_j. Then g is Borel (ψ_j⁻¹ is continuous on ψ_j(V_j), and the M_j are Borel and disjoint), and g(x) ∈ T_xM for x ∈ ⋃_j M_j.
 (a) |g| ≤ L a.e. on M. Let y be a Lebesgue density point of Y_j (almost every point of Y_j is one) and e a unit vector.
 - There are y_k ∈ Y_j with y_k → y and (y_k − y)/|y_k − y| → e.
 - Since F_j = f∘ψ_j on Y_j, |F_j(y_k) − F_j(y)| ≤ L|ψ_j(y_k) − ψ_j(y)|. Dividing by |y_k − y| and letting k → ∞ gives |DF_j(y)e| ≤ L|Dψ_j(y)e|.
 - Hence |⟨g(x), v⟩| ≤ L|v| for every v ∈ Q_j(y). Taking v = g(x) gives |g(x)| ≤ L.
 Delete the null set where this fails; then |g| ≤ L everywhere.
 (b) Tangential gradients of Lipschitz functions. Let k : ℝ^P → ℝ be Lipschitz. Then k∘ψ_j is Lipschitz on C'_j and differentiable at L^{n+1}-a.e. point (Rademacher, Ch. 2, 1.4). At such a point y ∈ int C'_j, let ∇^{N_j}k(ψ_j(y)) be the unique w ∈ Q_j(y) with ⟨w, Dψ_j(y)e⟩ = D(k∘ψ_j)(y)e for all e.
 - Since |D(k∘ψ_j)(y)e| ≤ Lip(k)|Dψ_j(y)e|, we get |∇^{N_j}k| ≤ Lip(k).
 - If k is C¹, the chain rule gives ∇^{N_j}k(x) = P_{Q_j(y)}∇k(x) = P_{T_xM}∇k(x).
 (c) Agreement of derivatives. Two Lipschitz functions on an open subset of ℝ^{n+1} that agree on a set Y have equal derivatives at L^{n+1}-a.e. point of Y. Indeed, at a density point of Y where both are differentiable, the derivative of their difference vanishes in every direction, by the argument of (a). In particular a Lipschitz function has zero derivative a.e. on each of its level sets.
 Since f∘ψ_j = F_j on Y_j, we get ∇^{N_j}f = g H^{n+1}-a.e. on M_j. After deleting null sets: for every x = ψ_j(y) ∈ M_j, f∘ψ_j is differentiable at y and D(f∘ψ_j)(y) = DF_j(y).
 (d) Chain rule. Let h := γ∘f. Put γ'(s) := −1/(b − a) for a < s < b and γ'(s) := 0 otherwise. Then ∇^{N_j}h = γ'(f)g H^{n+1}-a.e. on M_j:
 - At y ∈ Y_j with f(ψ_j y) ∉ {a, b} this is the classical chain rule, since γ is differentiable at f(ψ_j y) and f∘ψ_j is differentiable at y.
 - For c ∈ {a, b}, almost every point of Y_j ∩ {f∘ψ_j = c} is a point where both D(f∘ψ_j) and D(h∘ψ_j) vanish, by (c), because h∘ψ_j = γ(c) is constant on this level set of f∘ψ_j.
 Define M₊ := {x ∈ M : g(x) ≠ 0} ⊆ ⋃_j M_j, ν := g/|g| on M₊, and M_t := M₊ ∩ f⁻¹(t) for t ∈ ℝ. All of these are Borel. Since Dψ_jG_j⁻¹ is injective, x = ψ_j(y) ∈ M_j lies in M₊ iff ∇F_j(y) ≠ 0. Let O_j := {y ∈ V_j : ∇F_j(y) ≠ 0}, an open set.

4. Co-area formula and slices (Ch. 3, 2.8–2.10; Ch. 2, 6.3–6.6; Ch. 6, Lemma 4.1).
 (a) Co-area formula. For every Borel φ : ℝ^P → [0, ∞], the function t ↦ ∫_{M_t} φ dHⁿ is Lebesgue measurable and
  ∫_ℝ ∫_{M_t} φ dHⁿ dt = ∫_M |g|φ dH^{n+1}.
 Proof.
 - Since M₊ ⊆ ⋃_j M_j disjointly, both sides are sums over j of the corresponding quantities for M_j ∩ M₊ (monotone convergence). So fix j and write ψ = ψ_j, F = F_j, Y := ψ⁻¹(M_j ∩ M₊) ⊆ O_j ∩ C_j.
 - For t ∈ ℝ, Γ_t := O_j ∩ F⁻¹(t) is a C¹ hypersurface in V_j (implicit function theorem), with normal ∇F/|∇F|. Since f∘ψ = F on Y, M_t ∩ M_j = ψ(Y ∩ Γ_t).
 - Area formula for the injective C¹ map ψ (Ch. 2, §§3–4): ∫_{M_j∩M₊} |g|φ dH^{n+1} = ∫_Y |g(ψ y)|φ(ψ y)J(y) dy, with J := (det G)^{1/2}.
 - Area formula for ψ|Γ_t: ∫_{M_t∩M_j} φ dHⁿ = ∫_{Y∩Γ_t} φ(ψ y)J_Γ(y) dHⁿ(y), where J_Γ(y) := (det(G(y)|_{∇F(y)^⊥}))^{1/2} is the Jacobian of ψ along Γ_t; it is continuous on O_j.
 - Linear algebra: |g(ψ y)|² = ∇Fᵀ G⁻¹ ∇F. For the unit vector u = ∇F/|∇F|, det(G|_{u^⊥}) = det G · uᵀG⁻¹u (Schur complement / Cramer's rule). Hence |g(ψ y)|·J(y) = |∇F(y)|·J_Γ(y).
 - Euclidean co-area formula for the C¹ function F on O_j (Ch. 2, 6.3/6.6): for Borel G̃ ≥ 0, ∫_{O_j} G̃|∇F| dy = ∫_ℝ ∫_{Γ_t} G̃ dHⁿ dt, and t ↦ ∫_{Γ_t} G̃ dHⁿ is measurable. Since ∇F ≠ 0 on O_j, this follows from the implicit function theorem, Fubini and the area formula after locally straightening F to a coordinate function.
 - Take G̃ := 1_Y·(φ∘ψ)·J_Γ. This gives the formula on M_j; summing over j gives (a).
 (b) Rectifiability and local finiteness.
 - For every t, M_t ∩ M_j ⊆ ψ_j(Γ_t). The set ψ_j(Γ_t) is an embedded C¹ n-dimensional submanifold (a C¹ hypersurface mapped by a C¹ embedding), hence countably n-rectifiable (Lemma 1.2 "if"). So M_t is countably n-rectifiable for every t.
 - By (a) with φ = θ1_{K_i}: ∫_ℝ ∫_{M_t∩K_i} θ dHⁿ dt = ∫_{M∩K_i} |g|θ dH^{n+1} ≤ Lμ_T(K_i) < ∞. So for a.e. t, ∫_{M_t∩K_i} θ dHⁿ < ∞ for every i (a countable intersection of full-measure sets).
 - For such t, Hⁿ(M_t ∩ K) < ∞ for every compact K ⊆ U, since θ ≥ 1 on M and K ⊆ K_i for some i.
 (c) Tangent splitting (Lemma 4.1(2)). Let t satisfy Hⁿ(M_t ∩ K) < ∞ for every compact K ⊆ U.
 - For x = ψ_j(y) ∈ M_t ∩ M_j, the submanifold Σ := ψ_j(Γ_t) has tangent space T_xΣ = Dψ_j(y)(∇F_j(y)^⊥) = {v ∈ Q_j(y) : ⟨g(x), v⟩ = 0} = T_xM ∩ g(x)^⊥. This holds because ⟨g(x), Dψ_j(y)e⟩ = ⟨∇F_j(y), e⟩ and both spaces are n-dimensional.
 - Cover Γ_t by countably many compact sets Λ_k ⊆ Γ_t whose relative interiors cover Γ_t. Put Λ_k⁰ := relint Λ_k ∖ ⋃_{l<k} relint Λ_l and A_{j,k} := M_t ∩ M_j ∩ ψ_j(Λ_k⁰), a Borel set.
 - As in Step 2(b), the compact set ψ_j(Λ_k) ⊆ U, which has finite Hⁿ-measure, has approximate tangent space T_xΣ at each x ∈ ψ_j(relint Λ_k).
 - Apply (TL) with (A, B) = (A_{j,k}, ψ_j(Λ_k)), and then with (A, B) = (A_{j,k}, M_t); here M_t is Borel, M_t ⊆ U and M_t is locally Hⁿ-finite in U. So for Hⁿ-a.e. x ∈ A_{j,k}, M_t has approximate tangent space T_xM ∩ g(x)^⊥ at x.
 - Since M_t = ⋃_{j,k} A_{j,k}, for Hⁿ-a.e. x ∈ M_t: T_xM_t exists, T_xM_t = T_xM ∩ ν(x)^⊥ is n-dimensional, and T_xM = T_xM_t ⊕ ℝν(x) orthogonally.
 (d) Let G₁ be the set of t with ∫_{M_t∩K_i} θ dHⁿ < ∞ for all i; for these t, (c) holds. By (b), G₁ has full L¹-measure.

5. Orientation of the slices (Simon 4.3–4.4).
 Definition of ξ̃. For x ∈ M₊ and n-covectors α put ξ̃(x)(α) := ξ₀(x)(ν(x)♭∧α). This is Simon's ξ⌞ν, where 4.3 writes ⟨v⌞w, a⟩ = ⟨v, w∧a⟩. Put ξ̃(x) := 0 for x ∉ M₊. Then ξ̃ is Borel.
 Claim: for t ∈ G₁ and every x ∈ M_t at which (c) holds, ξ̃(x) is a unit orientation of T_xM_t.
 - Let τ₁,…,τₙ be an orthonormal basis of T_xM_t. Then (ν(x), τ₁,…,τₙ) is an orthonormal basis of T_xM.
 - By Step 2 and 0(a), ξ(x) = ξ₀(x) and ξ(x)(β) = εβ(ν, τ₁,…,τₙ) for all (n+1)-covectors β, with ε ∈ {1, −1}.
 - Expanding the wedge: ξ̃(x)(α) = ε(ν♭∧α)(ν, τ₁,…,τₙ) = ε[ν♭(ν)α(τ₁,…,τₙ) + Σ_{i=1}^{n} (−1)^i ν♭(τᵢ)α(ν, τ₁,…,τ̂ᵢ,…,τₙ)] = εα(τ₁,…,τₙ).
 Moreover, by linearity of β ↦ β∧α and ξ = ξ₀ on ⋃_j M_j: |g(x)|ξ̃(x)(α) = ξ(x)(g(x)♭∧α) for every x ∈ M₊ and every n-covector α.

6. The family (R_t).
 - For t ∈ G₁ let R_t := (M_t, θ, ξ̃), with carrier M_t, multiplicity θ and orientation ξ̃. It is an integer multiplicity triple in U of dimension n:
  - M_t is Borel, M_t ⊆ M ⊆ U, and M_t is countably n-rectifiable (4(b));
  - θ is measurable and θ > 0 on M_t ⊆ M;
  - for compact K ⊆ U, K ⊆ K_i for some i, so ∫_{M_t∩K} θ dHⁿ ≤ ∫_{M_t∩K_i} θ dHⁿ < ∞;
  - ξ̃ is Borel, hence a.e. strongly measurable (finite-dimensional target);
  - for Hⁿ-a.e. x ∈ M_t, Q := T_xM_t is an approximate tangent space of M_t at x and ξ̃(x) is a unit orientation of Q (4(c), 5).
 - For t ∉ G₁ let R_t be the empty triple: carrier ∅, multiplicity 1, orientation 0. It satisfies all conditions vacuously, since ∅ is countably n-rectifiable and every integral or a.e. statement over ∅ is trivial.
 - Conclusion (1) holds, since M_t ⊆ f⁻¹(t) and ∅ ⊆ f⁻¹(t).
 - For t ∈ G₁, μ_{R_t}(W) = ∫_{M_t∩W} θ dHⁿ and τ(R_t)(ω) = ∫_{M_t} θξ̃(ω) dHⁿ. For t ∉ G₁ both are 0.

7. Conclusion (2) (Simon 4.5(1)). Let W be Borel.
 - By 4(a) with φ = θ1_W, t ↦ ∫_{M_t∩W} θ dHⁿ is Lebesgue measurable. It agrees with t ↦ μ_{R_t}(W) on G₁, so the latter is a.e.-measurable.
 - Using |g| ≤ L: ∫_ℝ μ_{R_t}(W) dt = ∫_ℝ ∫_{M_t∩W} θ dHⁿ dt = ∫_{M∩W} |g|θ dH^{n+1} ≤ L∫_{M∩W} θ dH^{n+1} = Lμ_T(W).

8. Conclusion (3). Let ω ∈ 𝒟ⁿ(U), K := tsupport ω (compact, ⊆ U) and c := sup_x ‖ω(x)‖.
 - The function q := θξ̃(ω) is Borel on ℝ^P.
 - For t ∈ G₁, |q| ≤ cθ1_K at every x ∈ M_t where ξ̃(x) is a unit orientation (0(a)), i.e. Hⁿ-a.e. on M_t.
 - By 4(a) applied to q⁺ and q⁻: for t ∈ G₁, τ(R_t)(ω) = ∫_{M_t} q⁺ dHⁿ − ∫_{M_t} q⁻ dHⁿ, both finite. So s ↦ τ(R_s)(ω) is a.e.-measurable.
 - By Step 7, ∫_ℝ |τ(R_s)(ω)| ds ≤ c∫_ℝ μ_{R_s}(K) ds ≤ cLμ_T(K) < ∞. So the function is integrable on ℝ.

9. Leibniz formula for the Lipschitz cut-off (proof of Simon 4.5(2), steps (1)–(4)). Fix ω ∈ 𝒟ⁿ(U) and a < b. Let h := γ∘f, so 0 ≤ h ≤ 1 and h is Lipschitz with constant L/(b − a). Let h_δ := h∗ρ_δ be its standard mollifications: C^∞, 0 ≤ h_δ ≤ 1, |∇h_δ| ≤ Lip(h), and h_δ → h uniformly on ℝ^P as δ ↓ 0.
 (a) h_δω ∈ 𝒟ⁿ(U) (it is C^∞ and tsupport(h_δω) ⊆ tsupport ω), and d(h_δω) = dh_δ∧ω + h_δdω. Since RB represents ∂T and RT represents T, the identity ∂T(h_δω) = T(d(h_δω)) reads
  (i) ∫_{M'} θ'h_δξ'(ω) dHⁿ = ∫_M θξ(dh_δ∧ω) dH^{n+1} + ∫_M θh_δξ(dω) dH^{n+1}.
 All three integrands are integrable by 0(d).
 (b) As δ ↓ 0, the left side of (i) tends to ∫_{M'} θ'hξ'(ω) dHⁿ and the last term to ∫_M θhξ(dω) dH^{n+1}. This is dominated convergence, with dominating functions θ'|ξ'(ω)| and θ|ξ(dω)| (0(d)).
 (c) The middle term. Let x ∈ ⋃_j M_j.
 - ξ(x) is a unit orientation of T_xM. So ξ(x)(β∧ω(x)) = ε(β∧ω(x))(e₀,…,eₙ), for an orthonormal basis e of T_xM, depends on the 1-covector β only through β(e₀),…,β(eₙ), i.e. only through β|_{T_xM}.
 - Hence, for x ∈ M_j, ξ(x)(dh_δ(x)∧ω(x)) = ξ(x)((P_{T_xM}∇h_δ(x))♭∧ω(x)) = Ṽ(x)·∇^{N_j}h_δ(x) (Step 3(b)). Here Ṽ(x) := Σ_{k=1}^{P} ξ₀(x)(e_k♭∧ω(x)) e_k for x ∈ ⋃_j M_j and Ṽ(x) := 0 otherwise, with e_k the standard basis of ℝ^P. This uses the Borel version ξ₀, which equals ξ at every point of ⋃_j M_j (Step 2).
 - Ṽ is a bounded Borel vector field: |Ṽ| ≤ C(P, n)·sup‖ω‖ by 0(a). It vanishes off K = tsupport ω.
 (d) Weak convergence (Simon's (1): "v·∇^M h(δ) → v·∇^M h weakly in L²(μ_T) … we have merely to check that (1) holds with N_j in place of M_j …"). Write ∇^N k := ∇^{N_j}k on M_j. Claim: ∫_M θṼ·∇^N h_δ dH^{n+1} → ∫_M θṼ·∇^N h dH^{n+1}.
 - Reduction to one piece. We have |∇^N h_δ|, |∇^N h| ≤ Lip(h) (Step 3(b)) and Σ_j ∫_{M_j} θ|Ṽ|Lip(h) dH^{n+1} ≤ C sup‖ω‖·Lip(h)·μ_T(K) < ∞. By dominated convergence for series it suffices to prove the convergence on each M_j.
 - Transfer to the chart. Fix j and write ψ = ψ_j. By the area formula and Step 3(b), for k ∈ {h_δ, h}:
  ∫_{M_j} θṼ·∇^{N_j}k dH^{n+1} = ∫_{ℝ^{n+1}} W_j(y)·∇(k∘ψ)(y) dy,
  where W_j(y) := 1_{Y_j}(y)θ(ψ y)J(y)G(y)⁻¹Dψ(y)ᵀṼ(ψ y). We have W_j ∈ L¹, because θ∘ψ·J ∈ L¹(Y_j) (∫_{M_j} θ dH^{n+1} ≤ μ_T(ψ(C_j)) < ∞) and the other factors are bounded on C_j.
 - Weak-* convergence of the chart gradients. The functions ∇(h_δ∘ψ) are bounded on C'_j uniformly in δ. For Φ ∈ C_c^∞(int C'_j; ℝ^{n+1}), ∫Φ·∇(h_δ∘ψ) = −∫(div Φ)·h_δ∘ψ → −∫(div Φ)·h∘ψ = ∫Φ·∇(h∘ψ). This uses uniform convergence h_δ∘ψ → h∘ψ and integration by parts for Lipschitz functions. Since h∘ψ is only Lipschitz on C'_j, first replace it (and likewise h_δ∘ψ) by a globally Lipschitz McShane extension of its restriction to C'_j (Ch. 2, Theorem 1.2). This changes nothing on supp Φ ⊆ int C'_j or on the set where the a.e. gradient is used. Then apply Mathlib's LipschitzWith.integral_lineDeriv_mul_eq.
 - Conclusion. Approximate W_j in L¹ by such Φ (C_j ⊆ int C'_j) and use the uniform bound.
 (e) Passing to the limit. By Step 3(d), ∇^N h = γ'(f)g H^{n+1}-a.e. on M. By Step 5, Ṽ·g = ξ(g♭∧ω) = |g|ξ̃(ω) on M₊, and Ṽ·g = 0 where g = 0. Letting δ ↓ 0 in (i) and using (b)–(d) gives
  (ii) ∫_{M'} θ'hξ'(ω) dHⁿ = −(b − a)⁻¹∫_{M∩{a<f<b}} θ|g|ξ̃(ω) dH^{n+1} + ∫_M θhξ(dω) dH^{n+1}.
 This is Simon's identity after (4) in the proof of 4.5(2), with t = b and ε = b − a.

10. Co-area for the middle term (Simon 4.2) and conclusion (4).
 - Let q := θξ̃(ω)1_{a<f<b}, a Borel function. On M₊, |ξ̃(x)(α)| = |ξ(x)(ν(x)♭∧α)| ≤ ‖ν(x)♭∧α‖ ≤ (n+1)‖α‖, by 0(a) for ξ(x) and the expansion of the wedge. Hence |q| ≤ (n+1)cθ1_K on M₊, and ∫_M |g||q| dH^{n+1} ≤ (n+1)cLμ_T(K) < ∞. Moreover |q| ≤ cθ1_K Hⁿ-a.e. on M_t for t ∈ G₁ (Step 8), so both slice integrals below are finite.
 - Apply 4(a) to q⁺ and q⁻ and subtract. Using f ≡ t on M_t, and τ(R_t)(ω) = ∫_{M_t} θξ̃(ω) dHⁿ for t in the full-measure set G₁:
  ∫_{M∩{a<f<b}} θ|g|ξ̃(ω) dH^{n+1} = ∫_ℝ ∫_{M_t} q dHⁿ dt = ∫_ℝ 1_{(a,b)}(t) ∫_{M_t} θξ̃(ω) dHⁿ dt = ∫_a^b τ(R_t)(ω) dt.
 - Substitute into (ii) and multiply by b − a > 0:
  ∫_a^b τ(R_s)(ω) ds = (b − a)·(∫_M θγ(f)ξ(dω) dH^{n+1} − ∫_{M'} θ'γ(f)ξ'(ω) dHⁿ).
 This is conclusion (4), because h = γ∘f = min{1, max{0, (b − f)/(b − a)}}. ∎

## Key steps

1. Decompose M up to an H^{n+1}-null set into disjoint Borel pieces M_j ⊆ ψ_j(C_j) on C¹ charts, with C¹ functions F_j = f∘ψ_j on the pieces (Simon Ch. 3 Lemma 1.2, Remark 1.3; Ch. 2 Thm 1.5).
2. By (TL) applied to M_j ⊆ ψ_j(C'_j) and M_j ⊆ M, T_xM = Dψ_j(ℝ^{n+1}) on M_j. Define the tangential gradient g with |g| ≤ L, M₊ = {g ≠ 0} and slices M_t = M₊ ∩ f⁻¹(t).
3. Co-area formula ∫_ℝ∫_{M_t}φ dHⁿ dt = ∫_M|g|φ dH^{n+1}, proved on each piece from the area formula, the Jacobian identity |g|J = |∇F|J_Γ and the Euclidean C¹ co-area formula.
4. For a.e. t, M_t is countably n-rectifiable and locally Hⁿ-finite, and T_xM = T_xM_t ⊕ ℝν (Lemma 4.1(2), via (TL) on level submanifolds).
5. ξ̃ = ξ⌞ν is a unit orientation of T_xM_t (4.3). Put R_t = (M_t, θ, ξ̃) for good t and the empty triple otherwise; conclusions (1)–(3) follow from the co-area formula and |g| ≤ L.
6. Leibniz rule ∂T(h_δω) = T(dh_δ∧ω) + T(h_δdω) for mollified cut-offs h_δ of γ_{a,b}∘f. Weak convergence of tangential gradients on the charts and the chain rule give identity (ii).
7. Co-area for the signed middle term turns it into −(b−a)⁻¹∫_a^b τ(R_s)(ω) ds, which gives (4).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn -i 'slice|coarea|co-area|countable dense|SeparableSpace' local-references/123e8435b4a2469b/project/GMT --include=*.lean`
- `grep -n 'def |theorem |abbrev ' simongmt Chapter03/{Differential,Rectifiable}.lean, Chapter02/{Lipschitz,WhitneyExtension,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean, Chapter06/{Forms,Currents,Mass}.lean`
- `grep -rn 'ae_hasDerivAt_integral|ae_tendsto_average' snapshot mathlib Mathlib/MeasureTheory`
- `grep -rn 'SecondCountableTopology C(|SeparableSpace C(' snapshot mathlib Mathlib`
- `grep -rn 'exists_measurable_superset_of_null|integral_lineDeriv_mul_eq|tendsto_slope_zero_left|hasDerivAt_iff_tendsto_slope_left_right|tendsto_integral_filter_of_dominated_convergence' snapshot mathlib Mathlib`
- `dag.json scans: lean_name collision check for dor_lmbs_* (679 nodes, none); regex 'countable dense|separab|TendstoUniformly' and 'co-?area|Lebesgue point|mollif|tangential gradient|approxTangentPlane|Rademacher' over node statements; children of root.compactness_of_minimizing_currents-a1.slicing-a1`
- `git grep dor_lmbs_ over all local branches (no match); git show <accepted branches>:GMT/Ch07/Submission.lean | grep -c '^import' (extra Mathlib imports are used by accepted nodes)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the three statements; lake env lean on the three generated challenge files`
- `lake env lean /tmp/dor-slicing-decomp/Assembly.lean (#print axioms parent_from_children)`
- `lake env lean /tmp/dor-slicing-decomp/Inst.lean (TendstoUniformly on Covector = norm-uniform; default volume; intervalIntegral = Ioc integral; empty IMRep exists)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v6.json`
- `/tmp/dor-slicing-decomp/Assembly.lean`
- `/tmp/dor-slicing-decomp/Inst.lean`
- `/tmp/dor-slicing-decomp/challenges/slice_family_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/testform_dense_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/pointwise_identity_Challenge.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No current slicing, rectifiable co-area formula or countable dense family of test forms exists as a proved declaration:
- The snapshot's GMT/Ch02 and GMT/Ch06 contracts state CoareaFormula, C1Sard, IsSlice and SlicingTheorem, but only as unproven specs under sorry.
- SimonGMT has only linear and projection co-area, Rademacher, Whitney C¹ extension, and CountablyRectifiable/HasApproximateTangentSpaceAt.
- SimonGMT's tangentialGradient uses the ambient fderiv, so it is unusable for Lipschitz f on lower-dimensional sets. This is why no child statement mentions a tangential gradient.
- The compactness-branch slicing node cmc_slice_mass_bounds is about measure-represented currents without integer-multiplicity slices, and its children are not accepted, so none is reused.

Mathlib supplies these lemmas for the child proofs:
- LocallyIntegrable.ae_hasDerivAt_integral (needs an extra import);
- ContinuousMap.instSeparableSpace (needs an extra import);
- LipschitzWith.integral_lineDeriv_mul_eq;
- exists_measurable_superset_of_null;
- HasDerivAt.tendsto_slope_zero_left;
- tendsto_integral_filter_of_dominated_convergence.
Accepted nodes already add Mathlib imports to Submission.lean.

Lean checks:
- All three child types pass validate_lean_statement and elaborate in the exact comparator scope.
- A conditional assembly of the exact frozen parent type from the children, tangent_locality, borel_restriction and (C1) compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- TendstoUniformly on Covector is norm-uniform convergence, and the empty IMRep exists.
- No proposed name collides with any DAG node or branch.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
