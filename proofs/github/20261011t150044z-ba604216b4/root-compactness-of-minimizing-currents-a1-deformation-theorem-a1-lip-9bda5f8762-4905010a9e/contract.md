<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1 -->

## Theorem `Submission.cmcdt_lp_integer_multiplicity`

Assume, as hypotheses of the statement, (VO) the frozen type of Submission.dtc_vanish_off_support: for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0; (MR) the frozen type of Submission.cmc_massOn_eq_imRep_measure: for U open and an IMRep R representing T ∈ 𝒟_n(U), M_W(T) = R.measure(W) for every open W; (IMC) the frozen type of Submission.cmc_imRep_locality_restrict_sub: (a) for U open and Borel M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ for compact K ⊆ U, for Hⁿ-a.e. x ∈ M the approximate tangent spaces of M and M' at x coincide; (b) for U open, an IMRep R and Borel E, the triple (R.carrier ∩ E, R.mult, R.orient) is an IMRep representing some current; (c) for U open, A − B is integer multiplicity when A and B are; (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x in the carrier of any IMRep R; and (IMS) the exact frozen type of Submission.cmcdt_im_series, which itself assumes (VO), (MR), (IMC) and then asserts: for all P, k and W : ℕ → 𝒟_{k+1}(ℝ^P) with Σ_i M(W_i) < ∞ there is S ∈ 𝒟_{k+1}(ℝ^P) with S(ω) = Σ_i W_i(ω) (HasSum) for every ω, M(S) ≤ Σ_i M(W_i), spt S ⊆ closure ⋃_i spt W_i, and S integer multiplicity if every W_i is. (These are the exact frozen Lean types, written as antecedents.) Currents are on univ; write ι(t, x) := (t, x_1, …, x_N) ∈ ℝ^{N+1} (Lean WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) and e₀ := (1, 0, …, 0) (EuclideanSpace.single 0 1). Then: (I) for all N, N', k ∈ ℕ, Λ ∈ ℝ≥0, Λ-Lipschitz F : ℝ^N → ℝ^{N'}, integer multiplicity X ∈ 𝒟_{k+1}(ℝ^N) with compact support and M(X) < ∞, and S ∈ 𝒟_{k+1}(ℝ^{N'}): if there are C^∞ (ContDiff ℝ (⊤ : ℕ∞)) Λ-Lipschitz maps F_j : ℝ^N → ℝ^{N'} (j ∈ ℕ) converging to F uniformly on ℝ^N such that for every ω ∈ 𝒟^{k+1}(ℝ^{N'}) there are test forms η_j ∈ 𝒟^{k+1}(ℝ^N), each equal to F_j^#ω (x ↦ ω(F_j(x)) ∘ DF_j(x)) on some open set containing spt X, with X(η_j) → S(ω), then S is integer multiplicity; (II) for all N, k ∈ ℕ, integer multiplicity X ∈ 𝒟_{k+1}(ℝ^N) with compact support and M(X) < ∞, and C ∈ 𝒟_{k+2}(ℝ^{N+1}): if for every ω ∈ 𝒟^{k+2}(ℝ^{N+1}) there is η ∈ 𝒟^{k+1}(ℝ^N) with η(x)(v_1, …, v_{k+1}) = ∫_0^1 ω(ι(t, x))(e₀, ι(0, v_1), …, ι(0, v_{k+1})) dt for all x and v and C(ω) = X(η), then C is integer multiplicity.

Node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5204

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6049

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4595, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5648, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5591, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7160, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7162, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7165, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7170, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7175, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7178

## Lean problem

Declaration: `Submission.cmcdt_lp_integer_multiplicity`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ((∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (S : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1)), LipschitzWith Λ F → IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)), IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η : DifferentialForm (Euclid N) (k + 1)) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = X η) → IsIntegerMultiplicity C
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part B of the parent proof (Simon Ch. 6, 3.3–3.9 and 3.2(2): B1 parametrization, B2 tangent planes of pieces, B3 integral representation and integer pieces combined by the series theorem IMS, B4 identification by weak continuity of pull-backs, B5 products, B6 summary). The push-forward and the product enter only through the hypotheses of (I) and (II), which are exactly the interfaces (6) and (9) of the sibling cmcdt_lp_pushforward_operators. The sibling cmcdt_lp_covector_norm_bounds supplies (L1) |A^#β| ≤ ‖A‖^k|β|, (L2) |ι_vβ| ≤ |v||β| and (L3) |α(τ)| ≤ |α| for orthonormal τ. (VO), (MR), (IMC) = ((a) locality of approximate tangent spaces, (b) restriction to a Borel set, (c) differences, (d) |R.orient(x)(α)| ≤ |α| Hⁿ-a.e. on the carrier) and (IMS) are the antecedents; (IMS) is used after discharging its own antecedents with (VO), (MR), (IMC).

Notation. n := k + 1 ≥ 1. Hⁿ := μHE[n]; on ℝⁿ = Euclid n, Hⁿ = Lⁿ = volume (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). e = (e_1, …, e_n) is the standard basis of ℝⁿ. For linear A : ℝⁿ → ℝ^m, JA := √det(AᵀA). A Lipschitz H : ℝⁿ → ℝ^m is differentiable Lⁿ-a.e. (Rademacher, Mathlib LipschitzWith.ae_differentiableAt), and for an n-form ω on ℝ^m we write (H^#ω)(e)(u) := ω(H(u))(DH(u)e_1, …, DH(u)e_n) (defined a.e.). |α| := covectorEuclideanNorm α, ‖ω‖ := sup_y |ω(y)|. Lipschitz maps send Lⁿ-null subsets of ℝⁿ to Hⁿ-null sets (Mathlib LipschitzOnWith.hausdorffMeasure_image_le). "Area formula" means the SimonGMT injective area formula for a map that is Lipschitz and injective on a Borel set E ⊆ ℝⁿ, in its weighted form ∫_{G(E)} f dHⁿ = ∫_E f(G(u))JG(u) du for Borel f ≥ 0 or Hⁿ⌞G(E)-integrable f (SimonGMT injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, whose fibre sums are single terms for injective maps; the Jacobian of the within-derivative equals JG(u) at a.e. u ∈ E where G is differentiable).

0. Linear algebra.
 (0a) For v_1, …, v_n ∈ ℝ^m and an n-covector α: |α(v_1, …, v_n)| ≤ |α|·√det(⟨v_a, v_b⟩). If the v_a are dependent both sides vanish. Otherwise let τ be an orthonormal basis of span(v) (Gram–Schmidt) and C the n×n matrix with v_b = Σ_a C_{ab}τ_a; then α(v) = det(C)·α(τ) (multilinearity and alternation), det(⟨v_a, v_b⟩) = det(CᵀC) = det(C)², and |α(τ)| ≤ |α| by (L3).
 (0b) (Polar decomposition, parent (L3).) If A : ℝⁿ → ℝ^m is linear and injective, S := (AᵀA)^{1/2} is positive definite, O := AS^{−1} is an isometric embedding, τ_a := Oe_a is an orthonormal basis of A(ℝⁿ), and α(Ae) = det(S)·α(τ) = JA·α(τ) for every n-covector α. If A is not injective, α(Ae) = 0 = JA. If τ, τ' are orthonormal bases of the same n-plane then α(τ') = ±α(τ) for all α, with a sign independent of α (the change of basis is orthogonal).
 (0c) For an n-covector β on ℝⁿ, |β(e)| ≤ |β| (by (L3)); hence for linear A : ℝⁿ → ℝ^m and an n-covector ω on ℝ^m, |ω(Ae)| = |(A^#ω)(e)| ≤ |A^#ω| ≤ ‖A‖ⁿ|ω| (L1).
 (0d) If A : ℝⁿ → ℝ^m and B : ℝⁿ → ℝ^{m'} are linear, B injective and |Aw| ≤ Λ|Bw| for all w, then JA ≤ ΛⁿJB: AᵀA ≤ Λ²BᵀB as quadratic forms, BᵀB is positive definite, and 0 ≤ P ≤ Q, Q > 0 imply det P = det Q·det(Q^{−1/2}PQ^{−1/2}) ≤ det Q (the middle matrix has eigenvalues in [0, 1]).
 (0e) The zero current of 𝒟_n(ℝ^m) is integer multiplicity: the IMRep with empty carrier, multiplicity 0 and orientation 0 satisfies all conditions vacuously (μHE[n] ∅ = 0 gives rectifiability by countablyRectifiable_of_measure_zero) and its action is the integral over ∅, i.e. 0.

1. Normalizing X. Let X ∈ 𝒟_n(ℝ^N) be integer multiplicity, with compact support and M(X) < ∞; X = τ(M₀, θ, ξ) for an IMRep R. spt X is closed, hence Borel. By (IMC)(b) (U = ℝ^N open, E = spt X) there are a current A and an IMRep R' representing A with carrier M := M₀ ∩ spt X, multiplicity θ and orientation ξ. A = X: for every test form ω, the integrand θ ξ(ω) is Hⁿ⌞M₀-integrable (it vanishes off the compact tsupport ω, and |θ ξ(ω)| ≤ θ‖ω‖ a.e. by (IMC)(d) with ∫_{M₀ ∩ tsupport ω} θ dHⁿ < ∞ by locallyIntegrable_mult), so X(ω) − A(ω) = ∫_{M₀∖spt X} θ ξ(ω) dHⁿ, and its absolute value is ≤ ‖ω‖·∫_{M₀∖spt X} θ dHⁿ = ‖ω‖·R.measure(ℝ^N ∖ spt X) = ‖ω‖·M_{ℝ^N∖spt X}(X) (MR, the complement being open) = 0 by (VO) (every admissible form with tsupport in the complement is disjoint from spt X). So X = τ(M, θ, ξ) with M ⊆ spt X Borel and countably n-rectifiable (CountablyRectifiable.mono), ∫_M θ dHⁿ = R'.measure(ℝ^N) = M(X) < ∞ (MR with W = ℝ^N), and Hⁿ(M) ≤ M(X) since θ ≥ 1 on M. For every test form η, X(η) = ∫_M θ ξ(η) dHⁿ; in particular X(η) depends only on η restricted to M.

2. B1 (Parametrization). There are countably many compact sets A_i ⊆ ℝⁿ (possibly empty), Lipschitz maps G_i : ℝⁿ → ℝ^N and κ_i > 0 (i ∈ ℕ) such that: G_i is differentiable at every u ∈ A_i with DG_i(u) injective; |G_i(u) − G_i(v)| ≥ κ_i|u − v| for u, v ∈ A_i; the compact sets G_i(A_i) ⊆ M are pairwise disjoint; Hⁿ(M ∖ ⋃_i G_i(A_i)) = 0.
 Proof. By rectifiability M ⊆ Z₀ ∪ ⋃_j F_j(ℝⁿ) with Hⁿ(Z₀) = 0 and F_j : ℝⁿ → ℝ^N Lipschitz. Fix j. D_j := {u : F_j differentiable at u} is Borel (Mathlib measurableSet_of_differentiableAt) with Lⁿ-null complement (Rademacher), so Hⁿ(F_j(ℝⁿ ∖ D_j)) = 0. Z_j := {u ∈ D_j : DF_j(u) not injective} is Borel (u ↦ DF_j(u) is Borel, Mathlib measurable_fderiv; non-injectivity means det(DF_jᵀDF_j) = 0); JF_j = 0 on Z_j, so Hⁿ(F_j(Z_j)) = 0 by the area formula (SimonGMT area_image_criticalSet_eq_zero). E_j := (D_j ∖ Z_j) ∩ F_j^{-1}(M) is Borel. For injective linear A choose K_A > 0 with |Aw| ≥ |w|/K_A (Mathlib LinearMap.exists_antilipschitzWith) and set r(A) := 1/(2K_A); r(A) := 1 if A is not injective. Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (f = F_j, s = E_j, f' = DF_j) gives pairwise disjoint Borel sets t_l covering E_j and linear maps A_l such that |F_j(u) − F_j(v) − A_l(u − v)| ≤ r(A_l)|u − v| for u, v ∈ E_j ∩ t_l, and A_l = DF_j(y_l) for some y_l ∈ E_j (if E_j ≠ ∅); so A_l is injective and |F_j(u) − F_j(v)| ≥ (1/K_{A_l} − 1/(2K_{A_l}))|u − v| on E_j ∩ t_l. Enumerate the pairs (j, l) by i ∈ ℕ and put G_i := F_j, E_i := E_j ∩ t_l, κ_i := 1/(2K_{A_l}). Disjointify: E'_i := E_i ∖ G_i^{-1}(⋃_{i'<i} G_{i'}(E'_{i'})). Inductively each G_{i'}(E'_{i'}) is Borel (Lusin–Souslin: G_{i'} is continuous and injective on the Borel set E'_{i'}; Mathlib MeasurableSet.image_of_continuousOn_injOn), so E'_i is Borel. The G_i(E'_i) are pairwise disjoint subsets of M, and ⋃_i G_i(E'_i) = ⋃_i G_i(E_i) contains every x ∈ M outside the null set Z₀ ∪ ⋃_j F_j(ℝⁿ ∖ D_j) ∪ ⋃_j F_j(Z_j) (such an x is F_j(u) with u ∈ E_j ⊆ ⋃_l t_l). Finally Lⁿ(E'_i) ≤ κ_i^{−n}Hⁿ(G_i(E'_i)) ≤ κ_i^{−n}Hⁿ(M) < ∞ (G_i^{-1} is κ_i^{−1}-Lipschitz on G_i(E'_i)), so by inner regularity (Mathlib MeasurableSet.exists_isCompact_lt_add) each E'_i contains countably many pairwise disjoint compact sets whose union has Lⁿ-null complement in E'_i (choose them recursively, the m-th of measure ≥ that of the remainder minus 2^{−m}); the image of the null remainder is Hⁿ-null. Re-enumerating these compact sets (with their G_i, κ_i) gives the A_i.
 (B1′) For Lⁿ-a.e. u ∈ A_i, |DG_i(u)w| ≥ κ_i|w| for all w, hence JG_i(u) ≥ κ_iⁿ: at a Lebesgue density point u of A_i (a.e. point of A_i, Mathlib Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet), for each unit w there are v_m ∈ A_i with v_m → u and (v_m − u)/|v_m − u| → w (otherwise a cone of directions around w would meet A_i only far from u, contradicting density 1); then |G_i(v_m) − G_i(u)| ≥ κ_i|v_m − u| and differentiability at u give |DG_i(u)w| ≥ κ_i. Consequently ∫_{A_i} θ∘G_i du ≤ κ_i^{−n}∫_{A_i} (θ∘G_i)JG_i du = κ_i^{−n}∫_{G_i(A_i)} θ dHⁿ < ∞ (area formula).

3. B2 (Tangent planes of pieces). Let A ⊆ ℝⁿ be Borel, G : ℝⁿ → ℝ^m Lipschitz, κ > 0, |G(u) − G(v)| ≥ κ|u − v| for u, v ∈ A, and G differentiable at every u ∈ A with DG(u) injective. Then for Lⁿ-a.e. u ∈ A, HasApproximateTangentSpaceAt n (G(A)) (G(u)) (DG(u)(ℝⁿ)).
 Proof. V := DG(u)(ℝⁿ) has dimension n. Let u ∈ A be a density point of A (so |DG(u)w| ≥ κ|w| by the argument of (B1′)) and a Lebesgue point of the bounded Borel function 1_A·JG (JG ≤ Lip(G)ⁿ; Mathlib IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub); a.e. u ∈ A qualifies. Put x := G(u), G̃_r(w) := (G(u + rw) − x)/r and A_r := (A − u)/r (r > 0). Then blowUpMap x r '' G(A) = G̃_r(A_r), G̃_r is Lipschitz and injective on A_r with |G̃_r(w)| ≥ κ|w| for w ∈ A_r, and JG̃_r(w) = JG(u + rw) where G is differentiable. Let f ∈ C_c(ℝ^m) with spt f ⊆ B_ρ(0). By the area formula, ∫_{blowUpMap x r '' G(A)} f dHⁿ = ∫ 1_A(u + rw) f(G̃_r(w)) JG(u + rw) dw, and the integrand vanishes for |w| ≥ ρ/κ. On B_{ρ/κ}(0): G̃_r(w) → DG(u)w uniformly as r ↓ 0 (differentiability at u), so f∘G̃_r → f∘DG(u) uniformly (f is uniformly continuous); and ∫_{B_{ρ/κ}} |1_A(u + rw)JG(u + rw) − JG(u)| dw = r^{−n}∫_{B_{rρ/κ}(u)} |1_A JG − JG(u)| → 0 (Lebesgue point; 1_A(u) = 1). Hence the integral tends to ∫_{B_{ρ/κ}} f(DG(u)w)JG(u) dw = ∫_{ℝⁿ} f(DG(u)w)JG(u) dw (f(DG(u)w) = 0 for |w| ≥ ρ/κ since |DG(u)w| ≥ κ|w|) = ∫_V f dHⁿ (area formula for the injective linear map DG(u)). This is HasApproximateTangentSpaceAt n (G(A)) x V.
 (B2′) For Lⁿ-a.e. u ∈ A_i: T_{G_i(u)}M = V_i(u) := DG_i(u)(ℝⁿ), and there is s_i(u) ∈ {1, −1} with JG_i(u)·ξ(G_i(u))(α) = s_i(u)·α(DG_i(u)e) for all n-covectors α; s_i is Lⁿ⌞A_i-a.e. measurable. Proof: by B2, G_i(A_i) has approximate tangent space V_i(u) at G_i(u) for a.e. u ∈ A_i. By (IMC)(a) (U = ℝ^N, G_i(A_i) ⊆ M Borel, Hⁿ(M) < ∞), for Hⁿ-a.e. x ∈ G_i(A_i) the approximate tangent spaces of G_i(A_i) and of M at x coincide; Hⁿ-null subsets of G_i(A_i) correspond to Lⁿ-null subsets of A_i (G_i is Lipschitz, and κ_i^{−1}-Lipschitz-invertible on A_i). The IMRep gives, for Hⁿ-a.e. x ∈ M, Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q; by uniqueness (SimonGMT HasApproximateTangentSpaceAt.unique) Q = V_i(u) for x = G_i(u), a.e. u. IsUnitOrientationOf gives an orthonormal basis τ of V_i(u) with ξ(x)(α) = ±α(τ) for all α; with the polar basis τ' of (0b) for A = DG_i(u), α(DG_i(u)e) = JG_i(u)α(τ') = ±JG_i(u)α(τ), which is the claim. Set s_i(u) := 1 at the remaining (null) points of A_i, so s_i(u) ∈ {1, −1} everywhere on A_i. On the good set s_i(u) = ξ(G_i(u))(γ_u)/JG_i(u), where γ_u(w) := det(⟨DG_i(u)e_a, w_b⟩)_{a,b} is an n-covector with γ_u(DG_i(u)e) = JG_i(u)², depending Borel-measurably on u; since ξ is a.e. strongly measurable for Hⁿ⌞M and G_i maps Lⁿ⌞A_i to a measure absolutely continuous with respect to Hⁿ⌞G_i(A_i) (area formula), s_i is Lⁿ⌞A_i-a.e. measurable, which suffices for all integrals below. By (0a), |α(DG_i(u)e)| ≤ JG_i(u)|α| for all u ∈ A_i.

4. Setup for (I). Let F : ℝ^N → ℝ^{N'} be Λ-Lipschitz, H_i := F ∘ G_i (Lipschitz), θ_i := θ ∘ G_i. At a.e. u ∈ A_i both G_i and H_i are differentiable and |DH_i(u)w| = lim_{t↓0}|F(G_i(u + tw)) − F(G_i(u))|/t ≤ Λ|DG_i(u)w|, so JH_i(u) ≤ ΛⁿJG_i(u) by (0d). Define for ω ∈ 𝒟ⁿ(ℝ^{N'}):
 Φ(ω) := Σ_i ∫_{A_i} θ_i(u) s_i(u) (H_i^#ω)(e)(u) du.
 By (0a), |(H_i^#ω)(e)(u)| ≤ JH_i(u)‖ω‖ ≤ ΛⁿJG_i(u)‖ω‖, and Σ_i ∫_{A_i} θ_i JG_i du = Σ_i ∫_{G_i(A_i)} θ dHⁿ ≤ ∫_M θ dHⁿ = M(X) < ∞ (area formula, disjoint images). So the series converges absolutely and |Φ(ω)| ≤ ΛⁿM(X)‖ω‖.

5. B3 (Φ is the action of an integer multiplicity current Ŝ).
 (a) Fix i. A_i^+ := {u ∈ A_i : H_i differentiable at u, DH_i(u) injective} is Borel. At points of A_i ∖ A_i^+ where H_i is differentiable, (H_i^#ω)(e) = 0 (the vectors DH_i(u)e_a are dependent), and the non-differentiability points form an Lⁿ-null set; so Φ(ω) = Σ_i ∫_{A_i^+} θ_i s_i (H_i^#ω)(e) du. Exactly as in B1 (partition of Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt with r(A) = 1/(2K_A), then inner regularity) there are countably many pairwise disjoint compact sets A_{il} ⊆ A_i^+ with Lⁿ(A_i^+ ∖ ⋃_l A_{il}) = 0 and κ_{il} > 0 with |H_i(u) − H_i(v)| ≥ κ_{il}|u − v| on A_{il}; in particular H_i is injective on A_{il}.
 (b) For each (i, l) put N_{il} := H_i(A_{il}) (compact), h_{il} := (H_i|A_{il})^{−1} : N_{il} → A_{il} (continuous), g_{il} := (θ_i s_i) ∘ h_{il} (integer valued; |g_{il}| = θ_i ∘ h_{il} ≥ 1 on N_{il}), and η_{il}(y) := the n-vector α ↦ α(DH_i(u)e)/JH_i(u) with u = h_{il}(y) (η_{il} := 0 off N_{il}). R_{il} := (carrier N_{il}, multiplicity θ_i ∘ h_{il} on N_{il} extended by 0, orientation (s_i ∘ h_{il})·η_{il}) is an IMRep in U = ℝ^{N'}: N_{il} is Borel and countably n-rectifiable (a subset of the range of the Lipschitz H_i; SimonGMT countablyRectifiable_range, CountablyRectifiable.mono); the multiplicity is Borel, ℕ-valued and positive at every point of N_{il}, with ∫_{N_{il}} θ_i ∘ h_{il} dHⁿ = ∫_{A_{il}} θ_i JH_i du ≤ Λⁿ∫_{A_i} θ_i JG_i du < ∞ (area formula for H_i on A_{il}); the orientation is a.e. strongly measurable (η_{il} is Borel with finite-dimensional target, s_i ∘ h_{il} is a.e. measurable because h_{il} maps Hⁿ⌞N_{il} to a measure absolutely continuous with respect to Lⁿ⌞A_{il}); by B2 applied to H_i on A_{il}, for a.e. u ∈ A_{il} the approximate tangent space of N_{il} at H_i(u) is DH_i(u)(ℝⁿ), and by (0b) η_{il}(H_i(u))(α) = α(τ) for the orthonormal polar basis τ of DH_i(u)(ℝⁿ), so (s_i ∘ h_{il})·η_{il} = ±η_{il} is a unit orientation of that plane (IsUnitOrientationOf); the exceptional u form an Lⁿ-null set with Hⁿ-null image. So the orientation condition holds Hⁿ-a.e. on N_{il}.
 (c) By (IMC)(b) (U = E = ℝ^{N'}) there is Φ_{il} ∈ 𝒟_n(ℝ^{N'}) represented by an IMRep with the carrier, multiplicity and orientation of R_{il}; thus Φ_{il} is integer multiplicity and, by the area formula, Φ_{il}(ω) = ∫_{N_{il}} (θ_i ∘ h_{il})(s_i ∘ h_{il}) η_{il}(ω) dHⁿ = ∫_{N_{il}} g_{il} η_{il}(ω) dHⁿ = ∫_{A_{il}} θ_i s_i [ω(H_i(u))(DH_i(u)e)/JH_i(u)]·JH_i(u) du = ∫_{A_{il}} θ_i s_i (H_i^#ω)(e) du. By (MR), M(Φ_{il}) = R_{il}.measure(ℝ^{N'}) = ∫_{A_{il}} θ_i JH_i du, so Σ_{i,l} M(Φ_{il}) ≤ ΛⁿM(X) < ∞.
 (d) Enumerate the pairs (i, l) by m ∈ ℕ, W_m := Φ_{i_m l_m}, padding with zero currents (integer multiplicity by (0e)) if there are only finitely many. Σ_m M(W_m) < ∞, so (IMS) (antecedents discharged by (VO), (MR), (IMC)) gives an integer multiplicity Ŝ ∈ 𝒟_n(ℝ^{N'}) with Ŝ(ω) = Σ_m W_m(ω) for all ω. The double series Σ_i Σ_l ∫_{A_{il}} θ_i s_i (H_i^#ω)(e) converges absolutely (bound ‖ω‖∫_{A_{il}} θ_i JH_i), so it may be reordered: Ŝ(ω) = Σ_i ∫_{A_i^+} θ_i s_i (H_i^#ω)(e) du = Φ(ω).

6. B4 lemma (weak continuity of pull-backs). Let L ≥ 0, H_j, H : ℝⁿ → ℝ^{N'} be L-Lipschitz with H_j → H uniformly on ℝⁿ, w ∈ L¹(ℝⁿ) and ω ∈ 𝒟ⁿ(ℝ^{N'}). Then ∫ w (H_j^#ω)(e) du → ∫ w (H^#ω)(e) du.
 Proof. (i) A.e., |(H_j^#ω)(e)| ≤ ‖DH_j‖ⁿ‖ω‖ ≤ Lⁿ‖ω‖ by (0c); likewise for H. (ii) Given ε > 0 choose w̃ ∈ C_c^∞(ℝⁿ) with ‖w − w̃‖_{L¹} < ε; replacing w by w̃ changes every integral by at most Lⁿ‖ω‖ε, so we may assume w ∈ C_c^∞. (iii) Expanding each argument in the standard basis e' of ℝ^{N'} and using alternation, ω(y)(z_1, …, z_n) = Σ_J ω_J(y)·det[(z_b)_{J(a)}]_{a,b}, the sum over strictly increasing J : Fin n → Fin N', with ω_J(y) := ω(y)(e'_{J(1)}, …, e'_{J(n)}) continuous with compact support. Hence (H^#ω)(e) = Σ_J (ω_J ∘ H)·det DH^J, H^J := (H^{J(1)}, …, H^{J(n)}) : ℝⁿ → ℝⁿ, and it suffices to treat one J. (iv) ∫ w ω_J(H_j) det DH_j^J − ∫ w ω_J(H) det DH^J = ∫ w (ω_J(H_j) − ω_J(H)) det DH_j^J + ∫ w ω_J(H)(det DH_j^J − det DH^J). The first term tends to 0: ω_J is uniformly continuous, so ω_J ∘ H_j → ω_J ∘ H uniformly, and |det DH_j^J| ≤ Lⁿ (Hadamard). The second tends to 0 by (v) with c := w·(ω_J ∘ H) ∈ C_c(ℝⁿ), v_j := H_j^J, v := H^J.
 (v) Claim: for c ∈ C_c(ℝⁿ) and L-Lipschitz v_j, v : ℝⁿ → ℝⁿ with v_j → v uniformly, ∫ c det Dv_j → ∫ c det Dv. For a Lipschitz function g put dg := Σ_b ∂_b g dx^b (a.e. derivative), and identify an n-form f dx^1 ∧ ⋯ ∧ dx^n with the function f for integration. We prove by induction on r = 0, …, n the statement (P_r): for every continuous compactly supported (n − r)-form β on ℝⁿ and all a_1, …, a_r ∈ {1, …, n}, ∫ β ∧ dv_j^{a_1} ∧ ⋯ ∧ dv_j^{a_r} → ∫ β ∧ dv^{a_1} ∧ ⋯ ∧ dv^{a_r}. The claim is (P_n) with β = c and a = (1, …, n), since c·dv^1 ∧ ⋯ ∧ dv^n = c·det Dv·dx^1 ∧ ⋯ ∧ dx^n. (P_0) holds trivially. Assume (P_{r−1}), r ≥ 1, and first let β ∈ C_c^∞. Integration by parts: for Lipschitz g, u_2, …, u_r, ∫ β ∧ dg ∧ du_2 ∧ ⋯ ∧ du_r = (−1)^{n−r+1} ∫ g dβ ∧ du_2 ∧ ⋯ ∧ du_r. For C^∞ functions this is Stokes' theorem for the compactly supported exact form d(g β ∧ du_2 ∧ ⋯ ∧ du_r) = dg ∧ β ∧ du_2 ∧ ⋯ + g dβ ∧ du_2 ∧ ⋯ (using d(du) = 0 and dg ∧ β = (−1)^{n−r} β ∧ dg); for Lipschitz functions it follows by mollifying g and all u_i simultaneously: for each Lipschitz h, h ∗ ϕ_δ → h uniformly, D(h ∗ ϕ_δ) = (Dh) ∗ ϕ_δ (the a.e. derivative of a Lipschitz function is its weak derivative, Mathlib LipschitzWith.integral_lineDeriv_mul_eq) → Dh a.e. (Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable) with |D(h ∗ ϕ_δ)| ≤ Lip(h); so both sides of the identity for the mollified functions converge to the corresponding sides for g, u_2, …, u_r by dominated convergence on the compact set spt β. With R_j := dv_j^{a_2} ∧ ⋯ ∧ dv_j^{a_r} and R := dv^{a_2} ∧ ⋯ ∧ dv^{a_r}: ∫ β ∧ dv_j^{a_1} ∧ R_j − ∫ β ∧ dv^{a_1} ∧ R = ±[∫ (v_j^{a_1} − v^{a_1}) dβ ∧ R_j + ∫ v^{a_1} dβ ∧ (R_j − R)]; the first integral is at most sup|v_j − v|·C_β·L^{r−1} → 0, and the second tends to 0 by (P_{r−1}) applied to the continuous compactly supported (n − r + 1)-form v^{a_1}dβ. So (P_r) holds for smooth β. For continuous compactly supported β choose smooth β̃ with supports in a fixed compact K and sup|β − β̃| < ε; then |∫ (β − β̃) ∧ dv_j^{a_1} ∧ ⋯ ∧ dv_j^{a_r}| ≤ ε·C_n·L^r·Lⁿ(K) uniformly in j (and for v), which gives (P_r).

7. Proof of (I). Let S, F_j, η_j be as in the hypothesis: F_j C^∞ and Λ-Lipschitz, F_j → F uniformly on ℝ^N, and for each ω test forms η_j equal to F_j^#ω on open sets W_j ⊇ spt X with X(η_j) → S(ω). Fix ω. By step 1 and M ⊆ spt X ⊆ W_j, X(η_j) = ∫_M θ(x) ξ(x)(ω(F_j(x)) ∘ DF_j(x)) dHⁿ(x) = Σ_i ∫_{G_i(A_i)} (same integrand) dHⁿ (B1; the integrand is bounded by θ·Λⁿ‖ω‖ using (IMC)(d) and (L1)). By the area formula for G_i on A_i, (B2′) and the chain rule (H_{ij} := F_j ∘ G_i, DH_{ij}(u) = DF_j(G_i(u)) ∘ DG_i(u) at every u ∈ A_i): ∫_{G_i(A_i)} θ ξ(ω(F_j) ∘ DF_j) dHⁿ = ∫_{A_i} θ_i(u) JG_i(u) ξ(G_i(u))(ω(F_j(G_i(u))) ∘ DF_j(G_i(u))) du = ∫_{A_i} θ_i s_i (H_{ij}^#ω)(e) du. Each term is bounded in absolute value by Λⁿ‖ω‖∫_{A_i} θ_i JG_i du ((B2′) with α = ω(F_j(G_i(u))) ∘ DF_j(G_i(u)) and (L1)), a summable bound independent of j. For fixed i, H_{ij} → H_i uniformly, all with Lipschitz constant ≤ Λ·Lip(G_i), and w_i := θ_i s_i 1_{A_i} ∈ L¹(ℝⁿ) by (B1′); so step 6 gives ∫_{A_i} θ_i s_i (H_{ij}^#ω)(e) → ∫_{A_i} θ_i s_i (H_i^#ω)(e) as j → ∞. By dominated convergence for series (Mathlib tendsto_tsum_of_dominated_convergence), X(η_j) → Φ(ω). Hence S(ω) = Φ(ω) = Ŝ(ω) for every ω (step 5), so S = Ŝ (GeometricCurrentOn.ext) is integer multiplicity.

8. B5: proof of (II). Let X be normalized as in step 1 (X = τ(M, θ, ξ), M ⊆ spt X, Hⁿ(M) < ∞) and C as in (II). Notation: ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1}, e₀ := EuclideanSpace.single 0 1, Jv := ι(0, v) (linear isometric, J(ℝ^N) ⊥ e₀), tail(y) := (y_1, …, y_N) (so tail(ι(t, x)) = x and ι(t, x)_0 = t). For an (n+1)-covector α on ℝ^{N+1} let α₁ := (ι_{e₀}α) ∘ J^{×n}, i.e. α₁(v) = α(e₀, Jv_1, …, Jv_n); α ↦ α₁ is continuous linear and |α₁| ≤ |α| by (L1) (‖J‖ ≤ 1) and (L2) (|e₀| = 1).
 (a) Product-null lemma: if Hⁿ(Z) = 0 and I ⊆ ℝ is a bounded interval, then H^{n+1}(ι(I × Z)) = 0. μHE[d] is a positive constant multiple of the Hausdorff measure μH[d], so both have the same null sets and it suffices to show μH[n+1](ι(I × Z)) = 0. Given ε ∈ (0, 1), cover Z by sets C_j with Σ_j (diam C_j)ⁿ < ε (possible since μH[n](Z) = 0); index them by j ≥ 1 and put d_j := max(diam C_j, ε·2^{−j}), so 0 < d_j ≤ max(ε^{1/n}, ε) < 1 and Σ_j d_jⁿ ≤ Σ_j (diam C_j)ⁿ + Σ_{j≥1} (ε·2^{−j})ⁿ < 2ε. Cover I × C_j by at most |I|/d_j + 1 sets of the form [a, a + d_j] × C_j, each of diameter ≤ √2·d_j. Then the sum of the (n+1)-st powers of the diameters is ≤ Σ_j (|I|/d_j + 1)(√2·d_j)^{n+1} ≤ 2^{(n+1)/2}(|I| + 1)Σ_j d_jⁿ < 2^{(n+3)/2}(|I| + 1)ε, and all covering sets have diameter ≤ √2·max(ε^{1/n}, ε), which tends to 0 with ε. Hence μH[n+1](I × Z) = 0 in ℝ × ℝ^N, and ι is an isometry, so H^{n+1}(ι(I × Z)) = 0.
 (b) Product pieces. With the A_i, G_i, κ_i of B1 define Ĝ_i : ℝ^{n+1} → ℝ^{N+1}, Ĝ_i(z) := ι(z_0, G_i(tail z)), and Â_i := {z : z_0 ∈ (0,1), tail z ∈ A_i} (Borel). Ĝ_i is Lipschitz; for z, z' ∈ Â_i, |Ĝ_i(z) − Ĝ_i(z')|² = |z_0 − z'_0|² + |G_i(tail z) − G_i(tail z')|² ≥ min(1, κ_i)²|z − z'|²; Ĝ_i is differentiable at every z ∈ Â_i with DĜ_i(z)(s, w) = s·e₀ + J(DG_i(tail z)w), which is injective, and JĜ_i(z) = JG_i(tail z) (the Gram matrix is block diagonal diag(1, DG_iᵀDG_i)).
 (c) Product formula. M̃ := {y : y_0 ∈ (0,1), tail y ∈ M} = ι((0,1) × M) is Borel (preimage of Borel sets under continuous maps). Measure identity: the map Ψ(t, x) := ι(t, x) sends the product measure (L¹⌞(0,1)) ⊗ (Hⁿ⌞M) to H^{n+1}⌞M̃; equivalently, for Borel f ≥ 0 on ℝ^{N+1}, ∫_{M̃} f dH^{n+1} = ∫_0^1 ∫_M f(ι(t, x)) dHⁿ(x) dt, and hence (by the identity of measures) the same formula holds for every f that is integrable for either side, and a.e.-measurability transfers along Ψ. Proof of the formula for Borel f ≥ 0: M̃ is the disjoint union of the Ĝ_i(Â_i) = ι((0,1) × G_i(A_i)) and ι((0,1) × Z), Z := M ∖ ⋃_i G_i(A_i), Hⁿ(Z) = 0; by (a) the last set is H^{n+1}-null. For each i, by the area formula for Ĝ_i on Â_i, Fubini (Lebesgue measure on ℝ^{n+1} is the product of the Lebesgue measures of z_0 and of tail z: Mathlib EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp and MeasureTheory.volume_preserving_piFinSuccAbove) and the area formula for G_i on A_i: ∫_{Ĝ_i(Â_i)} f dH^{n+1} = ∫_{Â_i} f(Ĝ_i(z))JG_i(tail z) dz = ∫_0^1 ∫_{A_i} f(ι(t, G_i(u)))JG_i(u) du dt = ∫_0^1 ∫_{G_i(A_i)} f(ι(t, x)) dHⁿ(x) dt. Summing over i (monotone convergence) gives the formula. In particular H^{n+1}(M̃) = Hⁿ(M) < ∞, ∫_{M̃} θ ∘ tail dH^{n+1} = ∫_M θ dHⁿ = M(X) < ∞, and tail pushes H^{n+1}⌞M̃ forward to Hⁿ⌞M.
 (d) The IMRep. Carrier M̃ ⊆ ℝ^{N+1}; multiplicity θ̃ := θ ∘ tail (Borel, ℕ-valued, ≥ 1 on M̃); orientation ξ̃(y) := ξ(tail y) ∘ (α ↦ α₁), a continuous linear functional on (n+1)-covectors. ξ̃ is a.e. strongly measurable for H^{n+1}⌞M̃ because ξ is for Hⁿ⌞M and tail pushes the first measure to the second ((c)). Rectifiability: M ⊆ Z₀ ∪ ⋃_j F_j(ℝⁿ) (Hⁿ(Z₀) = 0, F_j Lipschitz) gives M̃ ⊆ ι((0,1) × Z₀) ∪ ⋃_j F̃_j(ℝ^{n+1}) with F̃_j(z) := ι(z_0, F_j(tail z)) Lipschitz, and the first set is H^{n+1}-null by (a). Local integrability of θ̃ follows from (c).
 (e) Tangent planes and orientation. For a.e. z ∈ Â_i, B2 (applied to Ĝ_i on Â_i, degree n + 1) shows that Ĝ_i(Â_i) has approximate tangent space DĜ_i(z)(ℝ^{n+1}) = ℝe₀ ⊕ J(V_i(tail z)) at Ĝ_i(z); by (IMC)(a) (U = ℝ^{N+1}, Ĝ_i(Â_i) ⊆ M̃ Borel, H^{n+1}(M̃) < ∞) the same holds for M̃ at H^{n+1}-a.e. point of Ĝ_i(Â_i) (null sets correspond under the bi-Lipschitz Ĝ_i|Â_i). By (B2′), for a.e. u ∈ A_i, V_i(u) = T_{G_i(u)}M and ξ(G_i(u))(β) = ±β(τ) for an orthonormal basis τ of V_i(u); then for y = ι(t, G_i(u)), ξ̃(y)(α) = ξ(G_i(u))(α₁) = ±α₁(τ) = ±α(e₀, Jτ_1, …, Jτ_n), and (e₀, Jτ_1, …, Jτ_n) is an orthonormal basis of ℝe₀ ⊕ J(V_i(u)). All exceptional sets are H^{n+1}-null (by (a) for sets ι((0,1) × Z'), Hⁿ(Z') = 0, and by (c)/Fubini for the a.e.-in-z statements). Hence for H^{n+1}-a.e. y ∈ M̃ there is Q with HasApproximateTangentSpaceAt (n+1) M̃ y Q and IsUnitOrientationOf (ξ̃ y) Q. So (M̃, θ̃, ξ̃) is an IMRep in U = ℝ^{N+1}.
 (f) Representation. Let ω ∈ 𝒟^{n+1}(ℝ^{N+1}) and η as in the hypothesis of (II). For each x, η(x) and the Bochner integral ∫_0^1 ω₁(t, x) dt (ω₁(t, x) := (ω(ι(t, x)))₁, continuous in t) take the same value at every v (evaluation commutes with the integral), so they are equal, and since ξ(x) is continuous linear, ξ(x)(η(x)) = ∫_0^1 ξ(x)(ω₁(t, x)) dt = ∫_0^1 ξ̃(ι(t, x))(ω(ι(t, x))) dt. The integrand θ(x)ξ̃(ι(t, x))(ω(ι(t, x))) is bounded by θ(x)‖ω‖ for Hⁿ-a.e. x ∈ M ((IMC)(d) and |α₁| ≤ |α|), which is integrable on (0,1) × M. By step 1, Fubini and the measure identity (c) (the integrand is integrable for (L¹⌞(0,1)) ⊗ (Hⁿ⌞M), hence θ̃ ξ̃(ω) is integrable for H^{n+1}⌞M̃):
  C(ω) = X(η) = ∫_M θ(x) ξ(x)(η(x)) dHⁿ(x) = ∫_0^1 ∫_M θ(x) ξ̃(ι(t, x))(ω(ι(t, x))) dHⁿ(x) dt = ∫_{M̃} θ̃ ξ̃(ω) dH^{n+1}.
 Hence the IMRep (M̃, θ̃, ξ̃) represents C, and C is integer multiplicity. This proves (II), and together with step 7 the statement. ∎

## Key steps

1. Linear algebra (0a)–(0e) from (L1)–(L3): Gram bound, polar decomposition, |ω(Ae)| ≤ ‖A‖ⁿ|ω|, determinant monotonicity, zero current is integer multiplicity.
2. Normalize X = τ(M, θ, ξ) with M ⊆ spt X by (IMC)(b), (MR), (VO); ∫_M θ dHⁿ = M(X).
3. B1: compact bi-Lipschitz pieces G_i(A_i) covering M up to an Hⁿ-null set (Rademacher, approximately-linear partition, Lusin–Souslin, inner regularity); (B1′) JG_i ≥ κ_iⁿ a.e. on A_i.
4. B2: approximate tangent planes DG(u)(ℝⁿ) of bi-Lipschitz pieces via the area formula and Lebesgue points; (B2′) JG_i·ξ(G_i u)(α) = s_i α(DG_i(u)e) by (IMC)(a) and uniqueness of tangent planes.
5. B3: Φ(ω) = Σ_i ∫_{A_i} θ_i s_i (H_i^#ω)(e) equals the sum of integer multiplicity currents Φ_il on bi-Lipschitz images N_il = H_i(A_il), combined by IMS into an integer multiplicity Ŝ.
6. B4: weak continuity of pull-backs under uniform convergence with bounded Lipschitz constants (Cauchy–Binet expansion, induction on wedge factors with integration by parts for Lipschitz functions).
7. (I): X(η_j) = Σ_i ∫ θ_i s_i (H_ij^#ω)(e) → Φ(ω) by B4 and dominated convergence for series, so S = Ŝ is integer multiplicity.
8. (II): product-null lemma, product pieces Ĝ_i(t,u) = ι(t, G_i(u)), product formula for H^{n+1}⌞((0,1) × M), tangent planes ℝe₀ ⊕ T_xM oriented by e₀ ∧ ξ, and Fubini give an IMRep ((0,1) × M, θ∘tail, e₀ ∧ ξ) representing C.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json)`
- `rg -n 'cmcdt_lp' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'lipschitz.*push|pushforward|homotopy|LipschitzPushforward' project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'noncomputable def curryLeft|theorem curryLeft_apply_apply' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem LipschitzWith.ae_differentiableAt|theorem LinearMap.exists_antilipschitzWith|theorem integral_lineDeriv_mul_eq|theorem ae_convolution_tendsto_right_of_locallyIntegrable|theorem Orthonormal.exists_orthonormalBasis_extension|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|lemma tendsto_tsum_of_dominated_convergence|theorem volume_preserving_piFinSuccAbove|theorem exists_contDiff_tsupport_subset|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem _root_.MeasurableSet.exists_isCompact_lt_add' mathlib/Mathlib -g '*.lean' (all found)`
- `grep -rn for measurableSet_of_differentiableAt, measurable_fderiv, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, ContDiffBump.normed, HasCompactSupport.contDiff_convolution_left, intervalIntegral.integral_eq_sub_of_hasDerivAt, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp in the pinned Mathlib (all found)`
- `grep in lake-packages-25730c7c/simongmt/Poincare/SimonGMT (Chapter06 Currents/Mass/CurrentLocalEquality/Forms/AffineCurrentPushforward/Product, Chapter03/Rectifiable, Chapter02/AreaDomain/AreaCritical): GeometricCurrentOn, massOn, support, boundary, boundary_boundary, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, exteriorDerivative_apply, exteriorDerivativeOn_pullbackFormWithin, tsupport_exteriorDerivative_subset, affinePullbackTestOn, TestFormOnConverges.affinePullback, CountablyRectifiable, countablyRectifiable_range, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, area_image_criticalSet_eq_zero (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: frozen types of the selected node, its siblings and cmcdt_im_series; lean_name scan for push/homot/covector/tangent/rectifiable lemmas; accepted covectorEuclideanNorm and HasApproximateTangentSpaceAt declarations; no name with prefix cmcdt_lp_`
- `grep of the controller (runtime/flows/*/_recursive_lean/runtime.py: _existing_lean_name_problem, _install_parent_supplied_child_handoff, _overlay_accepted_children) for the cross-branch reuse semantics`
- `lake env lean /tmp/lpdecomp/lean/T_L.lean, T_O.lean, T_I.lean (child types elaborate); lake env lean /tmp/lpdecomp/lean/Interface.lean (instance checks and interface derivation; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/lpdecomp/lean/AssemblyFull.lean (sorry-free Part C assembly from the IMS, operators and integrality types to the exact selected frozen type; axioms propext, Classical.choice, Quot.sound)`
- `sed -n 360,620p and 760,900p book/chapter-06.txt (Simon 6.2.17–2.33 and 6.3.3–3.12, the source of Parts A and B)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lpdecomp/lean/T_L.lean`
- `/tmp/lpdecomp/lean/T_O.lean`
- `/tmp/lpdecomp/lean/T_I.lean`
- `/tmp/lpdecomp/lean/Interface.lean`
- `/tmp/lpdecomp/lean/AssemblyFull.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Contract.lean and Submission.lean. Its only Lipschitz push-forward material is the unsolved Ch06 specification (project/GMT/Ch06/Contract.lean and Submission.lean: IsLipschitzPushforward, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). It is written over a different Euclidean type (Eucl), cannot be imported into Ch07 and contains no proofs, so nothing in it is reusable. Mathlib has no flat-norm, deformation or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: curryLeft as interior product, Rademacher, the approximately-linear partition, antilipschitz bounds for injective maps, mollification with a.e. convergence of derivatives, density and Lebesgue points, inner regularity, differentiation under interval integrals, the Fubini splitting of volume on Euclid (n+1), and Tannery's theorem. SimonGMT provides currents, mass, support, weak convergence with lower semicontinuity of mass, the exterior-derivative and pull-back formulas, affine pull-back of test forms, rectifiability, approximate tangent spaces with uniqueness, and the area formulas. No DAG node, snapshot file or Mathlib declaration uses the prefix cmcdt_lp_. All three child types elaborate. The interface derivation compiles with axioms propext, Classical.choice and Quot.sound. The sorry-free Part C assembly compiles to the exact selected frozen type with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
