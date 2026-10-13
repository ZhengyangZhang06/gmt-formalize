<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.straightening_cover-a1 -->

## Theorem `Submission.dor_lmbsf_pc_straightening_cover`

Let n ∈ ℕ and F : ℝ^{n+1} → ℝ be C¹. Then there are sets B_q ⊆ ℝ^{n+1} and maps Ψ_q : ℝ^{n+1} → ℝ^{n+1} (q ∈ ℕ) such that for every q: B_q is open; Ψ_q is C¹ on B_q and injective on B_q; the derivative DΨ_q(w) = fderiv ℝ Ψ_q w is bijective for every w ∈ B_q; F(Ψ_q(w)) = w(0) (the 0-th coordinate of w) for every w ∈ B_q; Ψ_q(B_q) is open; and {y ∈ ℝ^{n+1} : DF(y) ≠ 0} ⊆ ⋃_q Ψ_q(B_q).

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.straightening_cover-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6015

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5477

Decomposition children: None

## Lean problem

Declaration: `Submission.dor_lmbsf_pc_straightening_cover`

```lean
∀ (n : ℕ) (F : Euclid (n + 1) → ℝ), ContDiff ℝ 1 F → ∃ (B : ℕ → Set (Euclid (n + 1))) (Ψ : ℕ → Euclid (n + 1) → Euclid (n + 1)), (∀ q, IsOpen (B q)) ∧ (∀ q, ContDiffOn ℝ 1 (Ψ q) (B q)) ∧ (∀ q, InjOn (Ψ q) (B q)) ∧ (∀ q, ∀ w ∈ B q, Bijective (fderiv ℝ (Ψ q) w)) ∧ (∀ q, ∀ w ∈ B q, F (Ψ q w) = w 0) ∧ (∀ q, IsOpen (Ψ q '' B q)) ∧ {y | fderiv ℝ F y ≠ 0} ⊆ ⋃ q, Ψ q '' B q
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.straightening_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 2 (local straightening of F by the inverse function theorem near each point with ∇F ≠ 0, and a countable subcover by Lindelöf). Departures: (i) instead of keeping coordinate i in place (Θ(y)_l = y_l for l ≠ i, Θ(y)_i = F(y) in the supplied proof), F is put in the first coordinate and the remaining coordinates follow, Θ(y) = (F(y), y(i.succAbove 0), …, y(i.succAbove (n−1))), so every patch is straightened to the first coordinate, the convention of slice_tonelli and param_coarea; (ii) no box is needed: a patch is the open target O of the inverse function theorem, and the parent assembly forms the disjoint patches Y_q itself (via `disjointed`).

Conventions: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); e_k := EuclideanSpace.single k 1 is the k-th standard basis vector; for v ∈ ℝ^{n+1}, v(0) = v 0 (Lean `v.ofLp 0`) is its 0-th coordinate, while e_k always denotes a basis vector; DΦ(w) := fderiv ℝ Φ w; Hᵏ := μHE[k]; |v| := ‖v‖ and |v|ₑ := ‖v‖ₑ = ofReal ‖v‖; all integrals are lower integrals in [0, ∞].

1. (A good coordinate.) Let y₀ ∈ ℝ^{n+1} with DF(y₀) ≠ 0. There is i ∈ {0, …, n} with DF(y₀)e_i ≠ 0: otherwise DF(y₀)v = Σ_j v_j·DF(y₀)e_j = 0 for every v (v = Σ_j v_j e_j), i.e. DF(y₀) = 0.
2. (The straightening map.) Let L : ℝ^{n+1} → ℝ^{n+1}, L(y) := (0, y(i.succAbove 0), …, y(i.succAbove (n−1))) = WithLp.toLp 2 (Fin.cons 0 (k ↦ y(i.succAbove k))); L is linear (check coordinatewise, Fin.cases), hence a continuous linear map. Let Θ(y) := F(y)·e_0 + L(y). Then Θ(y)(0) = F(y) and Θ(y)(k+1) = y(i.succAbove k). Θ is C¹ (F is C¹ and L is linear) with DΘ(y)h = (DF(y)h)·e_0 + L(h) (HasFDerivAt.smul_const, HasFDerivAt.add).
3. (DΘ(y₀) is injective.) Let DΘ(y₀)h = 0. Coordinate k+1 gives h(i.succAbove k) = 0 for every k < n. Every index j is i or i.succAbove k for some k (Fin.eq_self_or_eq_succAbove), so h = h(i)·e_i. Coordinate 0 gives 0 = DF(y₀)h = h(i)·DF(y₀)e_i, so h(i) = 0 by step 1, i.e. h = 0. As DΘ(y₀) is linear, it is injective.
4. (Local inverse.) Apply the sibling local_inverse with d := n + 1, φ := Θ, V := ℝ^{n+1} (open, contains y₀, Θ is C¹ on it) and z₀ := y₀. It gives open sets V₀ ∋ y₀ and O and a map χ, C¹ on O, with χ(O) ⊆ V₀, Θ(χ(a)) = a for a ∈ O, and Θ(z) ∈ O and χ(Θ(z)) = z for z ∈ V₀.
5. (Properties of (O, χ).) (a) χ is injective on O: χ(a) = χ(b) gives a = Θ(χ(a)) = Θ(χ(b)) = b. (b) χ(O) = V₀: ⊆ holds by step 4; if z ∈ V₀ then z = χ(Θ(z)) with Θ(z) ∈ O. So χ(O) is open and contains y₀. (c) For a ∈ O: F(χ(a)) = Θ(χ(a))(0) = a(0). (d) For a ∈ O: χ is differentiable at a (C¹ on the open set O), Θ is differentiable at χ(a), and Θ∘χ = id on the neighbourhood O of a, so D(Θ∘χ)(a) = D(id)(a) = id (Filter.EventuallyEq.fderiv_eq). By the chain rule DΘ(χ(a))∘Dχ(a) = id, so Dχ(a) is injective, and an injective linear endomorphism of the finite-dimensional space ℝ^{n+1} is surjective (LinearMap.surjective_of_injective); so Dχ(a) is bijective.
 Thus every y₀ in O' := {y : DF(y) ≠ 0} has data (B_{y₀}, Ψ_{y₀}) := (O, χ) with B_{y₀} open, Ψ_{y₀} C¹ and injective on B_{y₀}, DΨ_{y₀}(w) bijective and F(Ψ_{y₀}(w)) = w(0) for w ∈ B_{y₀}, and N_{y₀} := Ψ_{y₀}(B_{y₀}) open with y₀ ∈ N_{y₀}.
6. (Countable subfamily.) Choose such data for every y ∈ O'. The sets N_y (y ∈ O') are open and ℝ^{n+1} is second countable, so there is a countable T ⊆ O' with ⋃_{y∈T} N_y = ⋃_{y∈O'} N_y (TopologicalSpace.isOpen_iUnion_countable). Since y ∈ N_y for y ∈ O', O' ⊆ ⋃_{y∈T} N_y.
7. (Enumeration.) If T ≠ ∅, write T = {y_q : q ∈ ℕ} (Set.Countable.exists_eq_range) and put (B_q, Ψ_q) := (B_{y_q}, Ψ_{y_q}); every required property holds by step 5, and O' ⊆ ⋃_{y∈T} N_y = ⋃_q Ψ_q(B_q) by step 6. If T = ∅, then O' ⊆ ⋃_{y∈T} N_y = ∅; put B_q := ∅ and Ψ_q := id: ∅ is open, id is C¹ and injective on ∅, the pointwise conditions are vacuous, id(∅) = ∅ is open, and O' = ∅ ⊆ ⋃_q Ψ_q(B_q). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.dor_lmbsf_pc_straightening_cover : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c as a single theorem inserted into GMT/Ch07/Submission.lean (namespace GMT.Ch07, frozen imports only) after the declarations of its dependencies (codim1_zsl_gc_local_inverse), with no helper declaration and no set_option; it also compiles under maxHeartbeats 70000, and the controller's leaf gate (leaf_verification.check_source_delta) accepts the insertion. #print axioms of the assembled selected theorem reports propext, Classical.choice and Quot.sound.
```lean
  have hR3 := Submission.codim1_zsl_gc_local_inverse
  intro n F hF
  classical
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  -- pointwise straightening
  have hloc : ∀ y₀ : Euclid (n + 1), fderiv ℝ F y₀ ≠ 0 →
      ∃ (B : Set (Euclid (n + 1))) (Ψ : Euclid (n + 1) → Euclid (n + 1)), IsOpen B ∧
        ContDiffOn ℝ 1 Ψ B ∧ InjOn Ψ B ∧ (∀ w ∈ B, Bijective (fderiv ℝ Ψ w)) ∧
        (∀ w ∈ B, F (Ψ w) = w 0) ∧ IsOpen (Ψ '' B) ∧ y₀ ∈ Ψ '' B := by
    intro y₀ hy₀
    have hexp : ∀ v : Euclid (n + 1), v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
      intro v; ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), fderiv ℝ F y₀ (EuclideanSpace.single i 1) ≠ 0 := by
      by_contra! h
      apply hy₀
      ext1 v
      rw [hexp v, map_sum]
      simp [h]
    -- the linear part `y ↦ (0, y ∘ i.succAbove)`
    let Llin : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1) :=
      { toFun := fun y => WithLp.toLp 2 (Fin.cons 0 (fun k => y (i.succAbove k)) : Fin (n + 1) → ℝ)
        map_add' := by
          intro y z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
        map_smul' := by
          intro c y; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp }
    let L : Euclid (n + 1) →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap Llin
    have hL0 : ∀ y, L y 0 = 0 := fun y => by simp [L, Llin]
    have hLs : ∀ y (k : Fin n), L y k.succ = y (i.succAbove k) := fun y k => by simp [L, Llin]
    let e0 : Euclid (n + 1) := EuclideanSpace.single 0 1
    let Θ : Euclid (n + 1) → Euclid (n + 1) := fun y => F y • e0 + L y
    have hΘ0 : ∀ y, Θ y 0 = F y := fun y => by simp [Θ, e0, hL0]
    have hΘc : ContDiff ℝ 1 Θ := (hF.smul contDiff_const).add L.contDiff
    have hΘD : ∀ y, fderiv ℝ Θ y = (fderiv ℝ F y).smulRight e0 + L := by
      intro y
      have h1 : HasFDerivAt (fun y => F y • e0) ((fderiv ℝ F y).smulRight e0) y :=
        (hFd y).hasFDerivAt.smul_const e0
      exact (h1.add L.hasFDerivAt).fderiv
    have hinj0 : Injective (fderiv ℝ Θ y₀) := by
      rw [hΘD y₀]
      have hker : ∀ h : Euclid (n + 1), ((fderiv ℝ F y₀).smulRight e0 + L) h = 0 → h = 0 := by
        intro h hh
        have hc0 := congrArg (fun v : Euclid (n + 1) => v 0) hh
        have hcs : ∀ k : Fin n, h (i.succAbove k) = 0 := by
          intro k
          have := congrArg (fun v : Euclid (n + 1) => v k.succ) hh
          simpa [e0, hLs, Fin.succ_ne_zero] using this
        have hhi : h = h i • EuclideanSpace.single i (1 : ℝ) := by
          ext j
          rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
          · simp
          · simp [hcs k, Fin.succAbove_ne]
        have hDF : fderiv ℝ F y₀ h = 0 := by simpa [e0, hL0] using hc0
        rw [hhi, map_smul, smul_eq_mul] at hDF
        have hi0 : h i = 0 := by
          rcases mul_eq_zero.mp hDF with h' | h'
          · exact h'
          · exact absurd h' hi
        rw [hhi, hi0, zero_smul]
      intro h1 h2 h12
      have := hker (h1 - h2) (by rw [map_sub, h12, sub_self])
      exact sub_eq_zero.mp this
    obtain ⟨V₀, O, χ, hV₀, hO, hy₀V₀, -, hχ, hχmaps, hΘχ, hχΘ⟩ :=
      hR3 (n + 1) Θ univ y₀ isOpen_univ (mem_univ _) hΘc.contDiffOn hinj0
    have hχd : ∀ a ∈ O, DifferentiableAt ℝ χ a := fun a ha =>
      (hχ.differentiableOn one_ne_zero a ha).differentiableAt (hO.mem_nhds ha)
    have himg : χ '' O = V₀ := by
      apply Subset.antisymm
      · rintro _ ⟨a, ha, rfl⟩; exact hχmaps ha
      · intro z hz; exact ⟨Θ z, (hχΘ z hz).1, (hχΘ z hz).2⟩
    refine ⟨O, χ, hO, hχ, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      rw [← hΘχ a ha, ← hΘχ b hb, hab]
    · intro a ha
      have hid : fderiv ℝ (Θ ∘ χ) a = ContinuousLinearMap.id ℝ (Euclid (n + 1)) := by
        rw [Filter.EventuallyEq.fderiv_eq (f₁ := Θ ∘ χ) (f := id) ?_, fderiv_id]
        filter_upwards [hO.mem_nhds ha] with b hb using hΘχ b hb
      rw [fderiv_comp a (hΘc.differentiable one_ne_zero _) (hχd a ha)] at hid
      have hli : Function.LeftInverse (fderiv ℝ Θ (χ a)) (fderiv ℝ χ a) := fun u => by
        simpa using DFunLike.congr_fun hid u
      have hinj : Injective (fderiv ℝ χ a) := hli.injective
      exact ⟨hinj, LinearMap.surjective_of_injective
        (f := (fderiv ℝ χ a : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))) hinj⟩
    · intro a ha
      rw [← hΘ0, hΘχ a ha]
    · rw [himg]; exact hV₀
    · rw [himg]; exact hy₀V₀
  let O' : Set (Euclid (n + 1)) := {y | fderiv ℝ F y ≠ 0}
  choose! Bf Ψf hBf hΨf hinjf hbijf hFf hopenf hmemf using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : O' => Ψf y '' Bf y) (fun y => hopenf y y.2)
  by_cases hT : T.Nonempty
  · obtain ⟨e, he⟩ := hTc.exists_eq_range hT
    refine ⟨fun q => Bf (e q), fun q => Ψf (e q), fun q => hBf _ (e q).2, fun q => hΨf _ (e q).2,
      fun q => hinjf _ (e q).2, fun q => hbijf _ (e q).2, fun q => hFf _ (e q).2,
      fun q => hopenf _ (e q).2, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.mp h1
    rw [he] at hzT
    obtain ⟨q, rfl⟩ := hzT
    exact mem_iUnion.mpr ⟨q, hz⟩
  · refine ⟨fun _ => ∅, fun _ => id, fun _ => isOpen_empty, fun _ => contDiff_id.contDiffOn,
      fun _ => injOn_empty _, fun _ _ h => absurd h (notMem_empty _),
      fun _ _ h => absurd h (notMem_empty _), fun _ => by simp, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, -⟩ := mem_iUnion₂.mp h1
    exact absurd ⟨z, hzT⟩ hT
```

## Key steps

1. At y₀ with DF(y₀) ≠ 0 pick i with DF(y₀)e_i ≠ 0 and set Θ(y) = F(y)e_0 + (0, y∘i.succAbove).
2. DΘ(y₀) is injective: coordinates k+1 force h = h_i e_i and coordinate 0 forces h_i = 0.
3. local_inverse gives (V₀, O, χ); then χ is injective on O, χ(O) = V₀ is an open neighbourhood of y₀, F∘χ = first coordinate on O, and Dχ is bijective by the chain rule.
4. Second countability selects countably many such charts covering {DF ≠ 0}; enumerate them (or use empty charts if none).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; python3 read of <snapshot>/project/lake-manifest.json; git rev-parse HEAD and git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n '^theorem' simongmt Chapter02/{WeightedArea,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean; cat Chapter02/{Area,AreaParametrization,WeightedArea,CoareaProjection,CoareaLinear}.lean; sed AreaApproximation.lean, AreaCritical.lean`
- `grep -rln 'coarea|Coarea|co-area' simongmt/Poincare/SimonGMT (only the Chapter02 linear and projection co-area files plus mentions in Chapter03; no nonlinear co-area formula)`
- `Lean probe after import GMT.Ch07.Submission in the contract scope: #check weighted_area_formula_of_injective_derivative, areaJacobianAt, LinearMap.normDet, Matrix.gram, ContDiffAt.toOpenPartialHomeomorph (unknown); lintegral_image_eq_lintegral_abs_det_fderiv_mul, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', lintegral_iUnion, lintegral_tsum, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, measurable_fderiv, Matrix.det_succ_row_zero, TopologicalSpace.isOpen_iUnion_countable, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (available)`
- `grep -rnE 'theorem (adjugate_fin_succ_eq_det_submatrix|adjugate_mul |isOpen_iUnion_countable|Countable.exists_eq_range|eq_self_or_eq_succAbove|surjective_of_injective|Filter.EventuallyEq.fderiv_eq|measurable_fderiv |MeasurableSet.image_of_continuousOn_injOn|lintegral_iUnion |lintegral_tsum|Measurable.lintegral_prod_right'|ContinuousOn.measurable_piecewise|normDet_sq_eq_det_gram|lintegral_prod |lintegral_indicator )' <snapshot>/mathlib/Mathlib; grep 'volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' <snapshot>/mathlib/Mathlib`
- `python3 -I scans of dag.json (1527 nodes): regex 'co-?area|Gram|straighten|implicit function|inverse function|Tonelli|areaJacobianAt|normDet|level set' over statements; accepted nodes matching 'Fin.cons|insertNth|piFinSuccAbove|∫⁻ t, ∫⁻|HasStrictFDerivAt|Pairwise|disjoint'; status and candidate_commit of codim1_lura_gram_area_formula, codim1_zsl_gc_local_inverse, codim1_lura_lintegral_image_eq_tsum_pieces, dtc_bc_lr_local_inverse; lean_name collision check for dor_lmbsf_pc_* (none); cross-parent reuse edges (562)`
- `git grep dor_lmbsf_pc_ over all refs (no match); git show 58ab3bbd:GMT/Ch07/Submission.lean (the proof base is the bare frozen contract)`
- `git show d5ba41d6:GMT/Ch07/Submission.lean and git show 013681e4:GMT/Ch07/Submission.lean, then lake env lean with #print axioms (propext, Classical.choice, Quot.sound); git log -1 d5ba41d6 (frozen-import leaf gate)`
- `read _recursive_lean/leaf_verification.py (check_source_delta), parent_verification.py, runtime.py (_existing_lean_name_problem, reuse of accepted children by lean_name), verifier/gmt-compare.py (contract_scope, child_modules), verifier/lean_contract.py`
- `lake env lean /tmp/pc-decomp/v1/{Types,Assembly,Leaves1,Leaves2,Leaves3}.lean, /tmp/pc-decomp/v2/Combined.lean, /tmp/pc-decomp/v2/cmp/*_Challenge.lean, /tmp/pc-decomp/v3/{Submission,SubmissionHB}.lean; python3 check_source_delta on each new leaf insertion`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-ec35f2137a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `/tmp/pc-decomp/v1/Types.lean`
- `/tmp/pc-decomp/v1/Assembly.lean`
- `/tmp/pc-decomp/v2/Combined.lean`
- `/tmp/pc-decomp/v3/Submission.lean`

Pins match. The snapshot manifest gives project b4d606d and Mathlib 25730c7c; its lake-manifest gives simongmt 2b366308. Workspace HEAD and .lake/packages agree. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical.

What exists. Snapshot Mathlib has every library fact the children use:
- adjugate_mul and adjugate_fin_succ_eq_det_submatrix (LinearAlgebra/Matrix/Adjugate.lean:268, 366);
- volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818);
- PiLp.volume_preserving_ofLp and PiLp.volume_preserving_toLp (Haar/InnerProductSpace.lean:134, 139);
- Measurable.lintegral_prod_right' and lintegral_prod (Measure/Prod.lean:123, 1009);
- lintegral_indicator and lintegral_iUnion (Lebesgue/Basic.lean:510, 597), and lintegral_tsum (Lebesgue/Add.lean:362);
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523) and MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821);
- measurable_fderiv (FDeriv/Measurable.lean:378) and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
- Fin.eq_self_or_eq_succAbove (Fin/Tuple/Basic.lean:841) and LinearMap.surjective_of_injective (FiniteDimensional/Basic.lean:291);
- TopologicalSpace.isOpen_iUnion_countable (Topology/Bases.lean:932) and Set.Countable.exists_eq_range (Set/Countable.lean:149).

What is missing. SimonGMT has no nonlinear co-area formula; Chapter02 has only the linear and projection co-area formulas. Its weighted area formula (WeightedArea.lean:76, 120), normDet and areaJacobianAt are not available under the frozen imports, and leaf proofs may not add imports (leaf_verification.check_source_delta). The child types therefore use Gram determinants.

DAG. Two accepted declarations are reused with byte-identical types: codim1_lura_gram_area_formula (candidate d5ba41d6) and codim1_zsl_gc_local_inverse (candidate 013681e4). Fresh compiles of both print only propext, Classical.choice and Quot.sound, and runtime._existing_lean_name_problem permits sharing accepted nodes. The six new dor_lmbsf_pc_* names occur in no dag.json node and in no ref. The related nodes dtc_bc_lc_sl_chart_coarea, dimred_cs_sos_spine_coarea and dtc_bc_lc_sl_coarea are unaccepted and have different types.

Lean. All 8 child types pass validate_lean_statement, and their gmt-compare challenge modules elaborate. The integrated /tmp/pc-decomp/v3/Submission.lean proves the exact frozen selected type from the reused proofs and from prototype proofs of all six new children, with axioms propext, Classical.choice and Quot.sound. Each new prototype passes check_source_delta and fits in 70000 heartbeats.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
