<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.isoperimetric-a1 -->

## Theorem `Submission.dtc_bc_tc_cl_dfm_isoperimetric_filling`

Assume (DTr): for all P, m ∈ ℕ with m + 1 < P there is c ∈ ℝ≥0 with c ≥ 1 such that for every ρ > 0 and every integer multiplicity T ∈ 𝒟_{m+1}(ℝ^P) (SimonGMT GeometricCurrentOn univ (m + 1)) with compact support, M(T) < ∞ and M(∂T) < ∞ there are Q, S ∈ 𝒟_{m+1}(ℝ^P) and R ∈ 𝒟_{m+2}(ℝ^P) such that Q, ∂Q and R are integer multiplicity, T − Q − S = ∂R, Q = 0 or M(Q) ≥ ρ^{m+1}, M(Q) ≤ cM(T), M(∂Q) ≤ cM(∂T), M(R) ≤ cρM(T), M(S) ≤ cρM(∂T), spt Q ∪ spt R ⊆ thickening(3√Pρ, spt T) and spt ∂Q ∪ spt S ⊆ thickening(3√Pρ, spt ∂T) (masses in [0, ∞]; this is verbatim the first conjunct of the selected node's conclusion). Then for all P, m ∈ ℕ with m + 1 < P there is a real c ≥ 1 such that every integer multiplicity Z ∈ 𝒟_{m+1}(ℝ^P) with compact support, ∂Z = 0 and M(Z) < ∞ is the boundary ∂Y of an integer multiplicity Y ∈ 𝒟_{m+2}(ℝ^P) with M(Y) ≤ c(2cz)^{1/(m+1)}z and spt Y ⊆ thickening(3√P(2cz)^{1/(m+1)}, spt Z), where z := M(Z) (real part ENNReal.toReal; the power is Real.rpow) (verbatim the second conjunct of the selected node's conclusion).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.isoperimetric-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8061

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_tc_cl_dfm_isoperimetric_filling`

```lean
(∀ (P m : ℕ), m + 1 < P → ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.isoperimetric-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 6.1 (Isoperimetric Theorem) and its proof (chapter-06.txt lines 1939–1961, printed pp. 168–169): apply the scaled deformation theorem 5.3 to the cycle with ρ chosen so that ρ^{m+1} exceeds the mass bound of the polyhedral part. This is step 7 of the parent's supplied proof. Departures from the printed text: (a) Simon states M(R)^{(n−1)/n} ≤ cM(T) with n the dimension of R; the frozen statement records the equivalent explicit bounds M(Y) ≤ cρz with ρ = (2cz)^{1/(m+1)} and the support bound inherited from (DTr); (b) the trivial case is z = M(Z) = 0 (not T = 0), handled by ρ = 1 and the fact that a current of zero mass vanishes. The same argument, for the all-dimension finite-net antecedent, is the accepted proof of Submission.cbr_isoperimetric_filling; that declaration has a different antecedent, so its proof is adapted rather than reused.

Notation. (DTr) is the displayed hypothesis. All currents are on univ in ℝ^P. For a test form ω, ‖ω‖ := sup_x |ω(x)| with |·| the Euclidean coefficient norm (covectorEuclideanNorm). M(X) = M_{univ}(X) is the supremum of ENNReal.ofReal X(ω) over admissible ω (|ω(x)| ≤ 1 for all x). (X − Y)(ω) = X(ω) − Y(ω), and currents with equal values are equal (GeometricCurrentOn.ext).

1. Fix P, m with m + 1 < P. (DTr) gives c₀ ∈ ℝ≥0 with c₀ ≥ 1 and the deformation property for this (P, m). Put c := c₀ (as a real number); then c ≥ 1, and this c depends only on (P, m).

2. Elementary facts.
 (a) M(0) = 0: every value of the zero current is 0, so every term ofReal(0(ω)) = 0.
 (b) spt 0 = ∅: every x lies in the open ball B_1(x), whose closure is compact and on which 0 vanishes, so x belongs to the zero region of 0.
 (c) |tα| = |t||α| for t ∈ ℝ and a covector α (the coefficients scale by t, and √(t²Σa²) = |t|√(Σa²)).
 (d) A current X with M(X) = 0 is 0. Let ω be a test form. x ↦ |ω(x)| is continuous (a square root of a finite sum of squares of continuous coefficient functions) and has compact support, so it is bounded by some C ∈ ℝ. Put s := (|C| + 1)⁻¹ > 0. For t ∈ {s, −s}, the form tω is admissible: |tω(x)| = |t||ω(x)| ≤ s(|C| + 1) = 1 by (c). Hence ENNReal.ofReal(X(tω)) ≤ M(X) = 0, i.e. X(tω) ≤ 0. By linearity X(sω) = sX(ω) and X(−sω) = −sX(ω), so sX(ω) ≤ 0 and −sX(ω) ≤ 0, whence sX(ω) = 0 and X(ω) = 0 (s ≠ 0). Thus X = 0.

3. Let Z be integer multiplicity with compact support, ∂Z = 0 and M(Z) < ∞, and put z := M(Z).toReal ≥ 0, so M(Z) = ENNReal.ofReal z. Choose ρ > 0 with cz < ρ^{m+1} and (z = 0 or ρ = (2cz)^{1/(m+1)}):
 - if z = 0, take ρ := 1, so cz = 0 < 1 = ρ^{m+1};
 - if z > 0, take ρ := (2cz)^{1/(m+1)} > 0 (rpow of a positive number); then ρ^{m+1} = 2cz (Real.rpow_inv_natCast_pow with 1/(m+1) = ((m+1 : ℕ) : ℝ)⁻¹) and 2cz > cz because cz > 0.

4. Apply (DTr) (step 1) with this ρ and T := Z. Its hypotheses hold: Z is integer multiplicity, spt Z is compact, M(Z) < ∞, and M(∂Z) = M(0) = 0 < ∞ by (a). We obtain Q, R, S with R integer multiplicity, Z − Q − S = ∂R, (Q = 0 or ρ^{m+1} ≤ M(Q)), M(Q) ≤ cM(Z), M(R) ≤ cρM(Z), M(S) ≤ cρM(∂Z) and spt Q ∪ spt R ⊆ thickening(3√Pρ, spt Z).

5. S = 0: M(S) ≤ cρM(∂Z) = cρ·0 = 0, so M(S) = 0 and S = 0 by (d).

6. Q = 0: otherwise ENNReal.ofReal(ρ^{m+1}) ≤ M(Q) ≤ c·ENNReal.ofReal z = ENNReal.ofReal(cz), so ρ^{m+1} ≤ cz (ENNReal.ofReal_le_ofReal_iff, cz ≥ 0), contradicting step 3.

7. ∂R = Z: for every ω, ∂R(ω) = (Z − 0 − 0)(ω) = Z(ω) − 0 − 0 = Z(ω).

8. Put Y := R. It is integer multiplicity and ∂Y = Z (step 7).
 - Case z = 0: M(R) ≤ cρ·ENNReal.ofReal 0 = 0, so R = 0 by (d). Then M(Y) = 0 ≤ ENNReal.ofReal(c(2cz)^{1/(m+1)}z) (every ENNReal is ≥ 0), and spt Y = spt 0 = ∅ by (b), which is contained in any set.
 - Case z > 0: ρ = (2cz)^{1/(m+1)}, and M(Y) = M(R) ≤ c·ENNReal.ofReal(ρ)·ENNReal.ofReal(z) = ENNReal.ofReal(cρz) = ENNReal.ofReal(c(2cz)^{1/(m+1)}z), using ENNReal.ofReal_mul (c ≥ 0, cρ ≥ 0) and ENNReal.ofReal_coe_nnreal. Finally spt Y = spt R ⊆ spt Q ∪ spt R ⊆ thickening(3√P(2cz)^{1/(m+1)}, spt Z) by step 4.
 In both cases Y has all required properties, with the constant c ≥ 1 of step 1, which depends only on (P, m). ∎

Formalization aid (verified in this decomposition session: Lean v4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens; #print axioms gives [propext, Classical.choice, Quot.sound]). It is the accepted Lean proof of Submission.cbr_isoperimetric_filling (candidate 054ff0a9) with the two edits described in steps 1 and 4. The tactic proof of `theorem Submission.dtc_bc_tc_cl_dfm_isoperimetric_filling : <frozen type> := by` is:

  intro hDT P m hPm
  obtain ⟨c, hc1, hDT⟩ := hDT P m hPm
  refine ⟨(c : ℝ), by exact_mod_cast hc1, ?_⟩
  intro Z hZ hZc hZb hZm
  -- `M(0) = 0` and `spt 0 = ∅`
  have hmass0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).mass = 0 := by
    intro k
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  have hsupp0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).support = ∅ := by
    intro k
    refine eq_empty_of_forall_notMem fun x hx => hx.2 ?_
    exact ⟨ball x 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _,
      fun ω _ => rfl⟩, mem_ball_self one_pos⟩
  -- the Euclidean coefficient norm is absolutely homogeneous
  have hhom : ∀ (k : ℕ) (t : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro k t α
    simp only [covectorEuclideanNorm]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- a current of zero mass is zero: test `±sω` with `s‖ω‖_∞ ≤ 1`
  have hzero : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass = 0 →
      X = 0 := by
    intro k X hX
    ext ω
    have hω : Continuous (ω : DifferentialForm (Euclid P) k) := ω.property.1.1.continuous
    have hfc : Continuous (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) := by
      simp only [Function.comp_def, covectorEuclideanNorm]
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hω).pow 2)
        fun _ => continuous_const
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) :=
      ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k)
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hcs
    obtain ⟨s, hs, hsC⟩ : ∃ s : ℝ, 0 < s ∧ s * (|C| + 1) = 1 :=
      ⟨(|C| + 1)⁻¹, by positivity, inv_mul_cancel₀ (by positivity)⟩
    have hadm : ∀ t : ℝ, |t| ≤ s → t • ω ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      intro t ht
      refine ⟨subset_univ _, fun x => ?_⟩
      show covectorEuclideanNorm (t • (ω : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hhom]
      have h0 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
      have h1 : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ |C| + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg h0] at this
        linarith [le_abs_self C]
      calc |t| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x)
          ≤ s * (|C| + 1) := mul_le_mul ht h1 h0 hs.le
        _ = 1 := hsC
    have hX' : X.massOn univ = 0 := hX
    have h1 := X.le_massOn (hadm s (abs_of_pos hs).le)
    have h2 := X.le_massOn (hadm (-s) (by rw [abs_neg, abs_of_pos hs]))
    rw [hX', nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1 h2
    have e1 : X (s • ω) = s * X ω := map_smul X.toCurrent s ω
    have e2 : X ((-s) • ω) = -(s * X ω) := by
      rw [show X ((-s) • ω) = -s * X ω from map_smul X.toCurrent (-s) ω]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 : s * X ω = 0 := by linarith
    rw [GeometricCurrentOn.zero_apply]
    exact (mul_eq_zero.1 h3).resolve_left hs.ne'
  -- the scale `ρ`
  set z : ℝ := Z.mass.toReal
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  have hZmz : Z.mass = ENNReal.ofReal z := (ENNReal.ofReal_toReal hZm.ne).symm
  have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
  have hc0' : (0 : ℝ) < c := by exact_mod_cast zero_lt_one.trans_le hc1
  have hcz0 : 0 ≤ (c : ℝ) * z := mul_nonneg hc0 hz0
  obtain ⟨ρ, hρ0, hρlt, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ (c : ℝ) * z < ρ ^ (m + 1) ∧
      (z = 0 ∨ ρ = (2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) := by
    rcases hz0.eq_or_lt with h | h
    · exact ⟨1, one_pos, by rw [← h]; simp, Or.inl h.symm⟩
    · have hcz : 0 < 2 * (c : ℝ) * z := mul_pos (mul_pos two_pos hc0') h
      refine ⟨_, Real.rpow_pos_of_pos hcz _, ?_, Or.inr rfl⟩
      have hpow : ((2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = 2 * (c : ℝ) * z := by
        rw [one_div, ← Nat.cast_succ]
        exact Real.rpow_inv_natCast_pow hcz.le (Nat.succ_ne_zero m)
      rw [hpow]
      have : 0 < (c : ℝ) * z := mul_pos hc0' h
      linarith
  have hcρ : 0 ≤ (c : ℝ) * ρ := mul_nonneg hc0 hρ0.le
  -- apply (DTr) to `T = Z`
  obtain ⟨Q, R, S, -, -, hR, hZQS, hQ, hQm, -, hRm, hSm, hQR, -⟩ :=
    hDT ρ Z hρ0 hZ hZc hZm (by rw [hZb, hmass0]; exact ENNReal.zero_lt_top)
  -- `M(S) ≤ cρ M(∂Z) = 0`, so `S = 0`
  rw [hZb, hmass0, mul_zero, nonpos_iff_eq_zero] at hSm
  obtain rfl : S = 0 := hzero _ S hSm
  -- `M(Q) ≤ cz < ρ^{m+1}`, so `Q = 0`
  obtain rfl : Q = 0 := by
    refine hQ.resolve_right fun h => ?_
    have h' := h.trans hQm
    rw [hZmz, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_le_ofReal_iff hcz0] at h'
    linarith
  -- hence `Z = ∂R`
  have hRZ : R.boundary = Z := by
    rw [← hZQS]
    ext ω
    show Z ω - 0 - 0 = Z ω
    ring
  rcases hρ with h | rfl
  · -- `z = 0`: `M(R) ≤ cρ · 0 = 0`, so `R = 0`
    rw [hZmz, h, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at hRm
    refine ⟨R, hR, hRZ, hRm.trans_le zero_le, ?_⟩
    rw [hzero _ R hRm, hsupp0]
    exact empty_subset _
  · refine ⟨R, hR, hRZ, hRm.trans (le_of_eq ?_), subset_union_right.trans hQR⟩
    rw [ENNReal.ofReal_mul hcρ, ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal, hZmz]

## Key steps

1. Fix (P, m) with m + 1 < P and take c ≥ 1 from (DTr).
2. Zero current: M(0) = 0, spt 0 = ∅, and a current of zero mass vanishes (test ±sω with s‖ω‖ ≤ 1).
3. Scale: ρ := 1 if z = M(Z) = 0, else ρ := (2cz)^{1/(m+1)}, so cz < ρ^{m+1}.
4. Apply (DTr) to Z: M(S) ≤ cρM(∂Z) = 0 gives S = 0; M(Q) ≤ cz < ρ^{m+1} excludes M(Q) ≥ ρ^{m+1}, so Q = 0 and Z = ∂R.
5. Y := R: mass bound cρz (and R = 0 when z = 0), support in thickening(3√Pρ, spt Z).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); md5sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -l -i 'skeleton_retraction|cmcdt_|dtc_bc_tc_cl_dfm|deformation_theorem|isoperimetric' project -g '*.lean' (only project/GMT/Ch06/Contract.lean and project/GMT/Ch06/Submission.lean); grep -n -i 'DeformationTheorem|IsLatticeChain|LipschitzPushforwardIntegerMultiplicity' project/GMT/Ch06/Contract.lean (defs at lines 177, 223, 274; main_theorem := by sorry at line 362)`
- `grep -n 'theorem mem_thickening_iff_infEDist_lt|theorem mem_cthickening_iff |theorem cthickening_mono|theorem cthickening_subset_of_subset|IsCompact.cthickening|theorem cthickening_cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean; grep -rn 'infEDist_smul₀' mathlib/Mathlib/Analysis/Normed/Module/Ball/ (all found; an unrestricted rg over mathlib/Mathlib timed out after 120 s and was replaced by these targeted greps)`
- `grep -n 'theorem WeaklyConvergesOn.massOn_le_liminf|theorem WeaklyConvergesOn.boundary|theorem GeometricCurrentOn.boundary_affinePushforward|theorem GeometricCurrentOn.le_massOn|theorem GeometricCurrentOn.zero_apply|def GeometricCurrentOn.VanishesOn|def GeometricCurrentOn.support|theorem GeometricCurrentOn.boundary_boundary' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean (all found); grep -n 'def HasApproximateTangentSpaceAt' -A 8 Chapter03/Rectifiable.lean (includes finrank ℝ P = n)`
- `python3 -I over dag.json: status, candidate_commit and updated_at of the six reuse names and of all nodes with identical lean_statement (twins); replay of Runtime._existing_lean_name_problem for the 11 proposed names with parent root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1 (no problem)`
- `grep -n '_existing_lean_name_problem|def _accepted_checkpoint|def _overlay_accepted_children|def _leaf_author_task' /runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/runtime.py; Store.refresh in store.py; github_shared_issue_runtime in scripts/swarm-run-issue.py (HUMANIZE_SWARM_PROTOCOL=shared-theorem-issues-v1, so the DAG store refreshes on every update)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 0c9347ca33 (cmcdt_skeleton_retraction), 42b2a51030, fba5d30a5b, 9b823b5696, 6ae39d3e62, 172c98ff29: declared type byte-identical to the child type, the only sorry is main_theorem, no axiom declarations; grep of the five fresh names in these and in the dependency candidates a1c12d76e1, b23650f455 (no hit)`
- `nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/{parent-child-handoff.json, parent-supplied-natural-proof.md, isolated-comparator-result.json, lean-audit-v1.json} (audited proof and acceptance evidence of cmcdt_skeleton_retraction)`
- `difflib comparison of the bv_median, pushforward, skeleton and face natural proofs with nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-v4.json (only names and provenance differ); decomposition-audit-v4.json (all 12 children acceptable)`
- `PATH=toolchains/lean-4.35.0-rc3-linux/bin:$PATH lake env lean /tmp/dtc_dfm_v2/Final2.lean (13 sorry warnings for stand-ins; #print axioms Check.assembly and Check.iso: [propext, Classical.choice, Quot.sound]; Check.composed typechecks); validate_lean_statement (copy of verifier/lean_contract.py) on all 11 child types (accepted)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-cba2d86b76/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-cba2d86b76/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-audit-v4.json`
- `/runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dtc_dfm_v2/Final2.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. Its only deformation or isoperimetric material is the separate, unsolved Ch06 specification (DeformationTheorem, IsLatticeChain, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). That specification uses incompatible types and cannot be imported into Ch07, so it is not reusable; no cmcdt_ or dtc_bc_tc_cl_dfm_ declaration exists in the snapshot. Mathlib supplies every lemma used by the parent assembly (mem_thickening_iff_infEDist_lt, mem_cthickening_iff, cthickening_mono, cthickening_subset_of_subset, IsCompact.cthickening, cthickening_cthickening, infEDist_smul₀). SimonGMT supplies the cited current lemmas, and HasApproximateTangentSpaceAt includes finrank = n, as the face argument needs. The reuse names are accepted checkpoints with byte-identical types and clean candidates. The replaced name dtc_bc_lc_fd_dfm_skeleton_retraction is not used; its long-accepted twin cmcdt_skeleton_retraction is reused. All child types elaborate, and the parent assembly and the isoperimetric proof compile with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
