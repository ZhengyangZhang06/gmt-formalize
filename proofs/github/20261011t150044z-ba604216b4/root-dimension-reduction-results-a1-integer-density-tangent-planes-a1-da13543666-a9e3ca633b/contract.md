<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1 -->

## Theorem `Submission.idtp_fons_cs_sos_product_current`

Data: P, k, m', n' ∈ ℕ with m' ≥ 1 (0 < m') and an explicit equality h : n' = k + m'; an orthonormal family g = (g_1, …, g_k) in ℝ^P with span G := span{g_1, …, g_k}; a Borel set E ⊆ G; a current A ∈ 𝒟_{m'}(ℝ^P) with an integer multiplicity representation R_A = (M_A, θ_A, ζ_A) (IMRep univ m', R_A.Represents A) whose measure μ_A := R_A.measure is concentrated on G^⊥: μ_A(ℝ^P ∖ G^⊥) = 0. H^k := μHE[k].
Conclusion: there are B ∈ 𝒟_{n'}(ℝ^P) and an integer multiplicity representation R_B of B (IMRep univ n', R_B.Represents B) such that
(i) R_B.measure(C) = ∫_E μ_A(C − t) dH^k(t) for every Borel C ⊆ ℝ^P (Lean: ∫⁻ t in E, R_A.measure((fun y => t + y)⁻¹' C) ∂μHE[k]);
(ii) for every map ♭ : Λ^{n'} → Λ^{m'} with (♭α)(v) = α(g_1, …, g_k, v_1, …, v_{m'}) (Lean: α (Fin.append g v ∘ Fin.cast h)) and every test n'-form ω: B(ω) = ∫_E A(y ↦ ♭(ω(t + y))) dH^k(t), where the integrand is currentEval A of that test form.
B is the Cartesian product [[E]] × A of Simon Ch. 6, 2.17–2.20 (integer multiplicity by Ch. 6, 3.9), transported to ℝ^P = G ⊕ G^⊥ by (t, y) ↦ t + y.

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6973

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1310, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147

Decomposition children: None

## Lean problem

Declaration: `Submission.idtp_fons_cs_sos_product_current`

```lean
∀ (P k m' n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m') (E : Set (Euclid P)) (A : GeometricCurrentOn (univ : Set (Euclid P)) m') (RA : IMRep (univ : Set (Euclid P)) m'), 0 < m' → Orthonormal ℝ g → MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → RA.Represents A → RA.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → ∃ (B : GeometricCurrentOn (univ : Set (Euclid P)) n') (RB : IMRep (univ : Set (Euclid P)) n'), RB.Represents B ∧ (∀ C : Set (Euclid P), MeasurableSet C → RB.measure C = ∫⁻ t in E, RA.measure ((fun y => t + y) ⁻¹' C) ∂μHE[k]) ∧ ∀ flat : Covector (Euclid P) n' → Covector (Euclid P) m', (∀ (α : Covector (Euclid P) n') (v : Fin m' → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n', B ω = ∫ t in E, currentEval A (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) ∂μHE[k]
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration and depth note (context, not part of the numbered proof). New obligation with the fresh name idtp_fons_cs_sos_product_current. It is Part I (tools I.1–I.3) of the independently audited parent-supplied proof of the original minimality_transfer child (dimred_cs_sos_minimality_transfer of root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1). The proof is moved into a separate child so that the depth-6 leaf minimality_transfer stays smaller. The text below is that Part I, changed only in the last bullet of I.1 (adapted to the arbitrary map flat of the statement), in the integrand letter of (PM) (ψ instead of g, which names the frame), and in the final step (e), which matches the conclusion to the frozen type. The hypothesis 0 < m' is not needed by the argument. It is included because every use in minimality_transfer has m' ∈ {m, m + 1} with m = n − d ≥ 1, and it spares the formalization the degenerate case m' = 0. This node sits at depth 6, the configured maximum, so it is a machine leaf: its Lean proof adds only Submission.idtp_fons_cs_sos_product_current, proves I.1, I.2 and every auxiliary claim inline (have/obtain/let/show), and adds no helper declaration and no import.

Source: Simon Ch. 6, 2.17–2.20 (Cartesian products of currents and their mass), 3.9 (products of integer multiplicity currents are integer multiplicity), the area formula of Ch. 3, §2, and Federer 2.10.45 / 3.2.23 for the Hausdorff product formula of rectifiable sets.
Notation: H^j := μHE[j]; Λ^j := Covector (Euclid P) j; p_G := G.starProjection and q_G := (G^⊥).starProjection; E + M := {t + y : t ∈ E, y ∈ M}.
Sibling children used:
 (F7) dtc_imrep_current (sibling imrep_current): every IMRep represents some current;
 dpf_piece, the accepted Submission.dpf_approxTangent_ae_bilipschitz_piece, only for the AreaLipschitz import (see Imports).
Imports. I.3(b) uses the SimonGMT area formula weighted_area_formula_lipschitz_injOn and area_image_compl_regularSet_eq_zero, in Poincare.SimonGMT.Chapter02.AreaLipschitz, outside the contract import closure. This leaf adds no import. Its dependency dpf_piece (candidate a21680472b6919972de04d02dc3e1395a15d4171) carries `import Poincare.SimonGMT.Chapter02.AreaLipschitz` in GMT/Ch07/Submission.lean, and the controller merges accepted dependency candidates into this node's worktree before the implementation base is recorded. All other facts are in scope after `import GMT.Ch07.Submission` (Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, MeasureTheory.euclideanHausdorffMeasure_homothety_image, LinearMap.mkContinuous; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn).

I.1 (Interior product with an orthonormal frame.) Let g = (g_1, …, g_k) be orthonormal and k + m' = n' (formalize with an explicit m' and h : n' = k + m', to avoid degree casts).
 - For α ∈ Λ^{n'} define ♭_gα(v) := α(Fin.append g v ∘ Fin.cast h), i.e. α(g_1, …, g_k, v_1, …, v_{m'}).
 - Updating one entry of v updates one entry of Fin.append g v (Fin.addCases). Hence ♭_gα is multilinear, and alternating because equal entries stay at distinct indices; and |♭_gα(v)| ≤ ‖α‖∏|v_j|.
 - So ♭_g : Λ^{n'} →L[ℝ] Λ^{m'} is continuous linear with ‖♭_g‖ ≤ 1 (LinearMap.mkContinuous).
 - For a test n'-form ω, ♭_gω(t + ·) := y ↦ ♭_g(ω(t + y)) is a test m'-form with tsupport ⊆ tsupport ω − t.
 - Any map flat : Λ^{n'} → Λ^{m'} with flat α v = α(Fin.append g v ∘ Fin.cast h) for all α and v equals ♭_g, both being given by the same formula (evaluate at each α and v). Hence, for a test n'-form ω, y ↦ flat(ω(t + y)) is the test m'-form ♭_gω(t + ·), and currentEval A of it equals A(♭_gω(t + ·)) (currentEval returns the value of A on a test form supported in ℝ^P).
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
 (b) Product formula for H^{n'} (PM). For Borel E ⊆ G, Borel M ⊆ G^⊥ countably m'-rectifiable and locally H^{m'}-finite, and Borel ψ ≥ 0:
 ∫_{E+M} ψ dH^{n'} = ∫_E ∫_M ψ(t + y) dH^{m'}(y) dH^k(t), where E + M = p_G⁻¹(E) ∩ q_G⁻¹(M) is Borel.
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
(e) (Conclusion in the frozen form.) Put B := [[E]] ×_g A and R_B as in I.3(c), so R_B.Represents B. By I.3(d), for every Borel C, R_B.measure(C) = ∫_E μ_A(C − t) dH^k(t), and μ_A(C − t) = R_A.measure({y : t + y ∈ C}) = R_A.measure((fun y => t + y)⁻¹' C); this is (i). For (ii), let flat satisfy the defining identity. By the last bullet of I.1, currentEval A (y ↦ flat(ω(t + y))) = A(♭_gω(t + ·)) for every t, and by I.3(d), B(ω) = R_B.action(ω) = ∫_E A(♭_gω(t + ·)) dH^k(t). The integrand is continuous in t (translation acts continuously on test forms and A is continuous) and bounded by ‖ω‖_∞·μ_A(q_G(tsupport ω)). It vanishes for t ∉ p_G(tsupport ω), since by I.3(a) A only sees M_A ∩ G^⊥ and p_G(t + y) = t for t ∈ G and y ∈ G^⊥. So it is integrable on E, and the Bochner integral in (ii) is the integral computed in I.3(d). ∎

## Key steps

1. I.1: the interior product ♭_g with the orthonormal frame g is continuous linear, and every flat with the defining identity equals it.
2. I.2: if H^j(M' ∖ V) = 0 for a subspace V, then approximate tangent planes of M' at points of V lie in V; so the tangent planes of A lie in G^⊥.
3. Hausdorff product formula (PM) for E + M with E ⊆ G Borel and M ⊆ G^⊥ rectifiable: the null part by coverings, and the rectifiable part by bi-Lipschitz pieces G_l(a, u) = ι(a) + Φ_l(u) with JG_l = JΦ_l and the area formula.
4. R_B := (E + M_A, θ_A∘q_G, ζ_A(q_G ·)∘♭_g) is an IMRep: blow-ups at density points give the tangent plane G ⊕ T_y, oriented by Fin.append g τ.
5. (PM) gives R_B.measure(C) = ∫_E μ_A(C − t) dt and R_B.action(ω) = ∫_E A(♭_gω(t + ·)) dt, which is the frozen conclusion.

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(<snap>/manifest.json); git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `cmp GMT/Ch07/Contract.lean <snap>/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n '^def (IsMinimizingIn|IsConeCurrent|BoundaryVanishes|SameBoundary|blowUp|currentEval|approxTangentPlane)|^structure IMRep|^def IMRep\.(measure|Represents|action)' <snap>/project/GMT/Ch07/Contract.lean`
- `rg -n -i -l coarea <snap>/mathlib/Mathlib (no match)`
- `rg -n -i -l 'cartesian product of currents|slice of a current' <snap>/mathlib/Mathlib (no match)`
- `rg -n 'idtp_fons_cs_sos|dimred_cs_sos|dpf_approxTangent_ae_bilipschitz_piece|dimred_im_mass_measure' <snap>/project (no match)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' <snap>/mathlib/Mathlib`
- `rg -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snap>/mathlib/Mathlib`
- `rg -n "theorem ae_all_iff|theorem ae_restrict_iff'" <snap>/mathlib/Mathlib`
- `rg -n 'theorem isOpen_iUnion_countable' <snap>/mathlib/Mathlib/Topology/Bases.lean; rg -n 'theorem ContinuousLinearMap.isOpen_injective' <snap>/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean; rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero ' <snap>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'theorem weighted_area_formula_lipschitz_injOn|theorem area_image_compl_regularSet_eq_zero|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def areaRegularSet|theorem measurableSet_areaRegularSet' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,Lipschitz}.lean`
- `python3 scans of dag.json: status, candidate_commit, lean_statement, parent of dimred_cs_split_off_spine, dimred_cs_sos_*, the 5 reuses and all accepted nodes; accepted candidates whose Submission.lean imports Poincare.SimonGMT.Chapter02.AreaLipschitz; absence of the 7 fresh names`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for the 5 reuses (declaration with identical type present; a21680472b has import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `cat cluster-state/verification/results/hoa43/20261013T160813Z-ch07-root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_densit-ej3048p6/{result.json,comparator-config.json}`
- `grep -n '_existing_lean_name_problem|_dependency_problem|_overlay_accepted_children|_leaf_author_task|max_depth' /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `lake env lean /tmp/idtp_sos_decomp/check/{Types,Names,NamesArea,Assembly,Assembly2,Assembly3}.lean`
- `python3 /tmp/idtp_sos_decomp/scripts/gates.py /tmp/idtp_sos_decomp/envelope_test3.json (ScopedDecomposition.model_validate; replay of Runtime._dependency_problem, _topological, _existing_lean_name_problem on dag.json)`
- `sed -n 395,420p book/chapter-07.txt (Simon Lemma 7.3.5)`
- `WebSearch: Simon Introduction to GMT Lemma 3.5 minimizing cone translation invariant S = [[R^m]] × S_0`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ac0f702949/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idtp_sos_decomp/check/Assembly3.lean`
- `/tmp/idtp_sos_decomp/check/NamesArea.lean`
- `/tmp/idtp_sos_review/LipCheck.lean`
- `/tmp/idtp_sos_review/CarrierCheck.lean`
- `/tmp/idtp_sos_review/UsageCheck.lean`

Pins match: the snapshot manifest records project b4d606d (= workspace HEAD) and Mathlib 25730c7c (= workspace Mathlib); SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which hold no Submission declarations; none of the 7 fresh names, nor the reused names, occur in the snapshot project. No coarea formula, slicing or Cartesian product of currents exists in the snapshot Mathlib (no match). Mathlib does have exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, measurableSet_of_differentiableAt, measurable_fderiv, ContinuousLinearMap.isOpen_injective, TopologicalSpace.isOpen_iUnion_countable and euclideanHausdorffMeasure_zero, all used by the child proofs. SimonGMT's area formula (weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet) lies in Chapter02/AreaLipschitz.lean, outside the contract imports. In dag.json, the accepted dpf_approxTangent_ae_bilipschitz_piece (candidate a21680472b, comparator passed with propext, Quot.sound, Classical.choice) carries that import and proves the bi-Lipschitz-piece tangent lemma. The 5 reused declarations are accepted with byte-identical types present in their candidate commits. The six dimred_cs_sos_* children of the identical-type node dimred_cs_split_off_spine are unaccepted and owned by another parent, hence the fresh names. All 12 child types and the parent type elaborate. The parent assembly and the product_current usage checks compile; #print axioms shows only propext, Classical.choice and Quot.sound beyond the stubs' sorryAx. The runtime gate replay reports no problem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
