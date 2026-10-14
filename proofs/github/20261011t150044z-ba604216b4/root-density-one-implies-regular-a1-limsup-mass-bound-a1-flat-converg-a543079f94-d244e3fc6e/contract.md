<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.toolkit_push-a1 -->

## Theorem `Submission.dor_lmb_fcdp_toolkit_push`

Conventions: ℝ^N = Euclid N and Hᵈ = μHE[d]. 𝒟^d(U) = TestFormOn U d (smooth d-forms with compact support in U) and 𝒟_d(U) = GeometricCurrentOn U d; ∂X = X.boundary; X − Y is pointwise on test forms. |α| = covectorEuclideanNorm α is the Euclidean coefficient norm of a covector and ‖·‖ is the operator norm. M_W(X) = X.massOn W and M(X) = X.mass = M_univ(X). An IMRep R = (M, θ, ξ) (contract structure IMRep U d) has μ_R = θ·Hᵈ⌞M = R.measure and R.action(γ) = ∫_M θ ξ(γ) dHᵈ for any d-form γ; X is IM if some IMRep represents it. X vanishes off E if X(ω) = 0 whenever tsupport ω is disjoint from E. For a map Φ and a form ω, Φ^#ω(x) := ω(Φ(x)) ∘ DΦ(x) (Lean (ω (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)). (i) Let P, k ∈ ℕ. Let X ∈ 𝒟_k(ℝ^P) (domain univ) be represented by an IMRep R = (M, θ, ξ) in univ, and let E ⊆ ℝ^P be compact with X vanishing off E. Then H^k(M ∖ E) = 0, M(X) = μ_R(ℝ^P) and μ_R(ℝ^P) ≠ ∞. Moreover R.action(γ) = R.action(γ') for all k-forms γ, γ' (arbitrary functions ℝ^P → Λ^k) with γ = γ' on E. (ii) (Hadamard) For all N, m ∈ ℕ, every m-covector α on ℝ^N and all v_1, …, v_m ∈ ℝ^N: |α(v_1, …, v_m)| ≤ |α|·∏_i‖v_i‖. (iii) Let R = (M, θ, ξ) be an IMRep of degree k in any U ⊆ ℝ^P with μ_R(ℝ^P) ≠ ∞, let γ be any k-form and c ≥ 0. Assume that for H^k-a.e. x ∈ M, |γ(x)(τ_1, …, τ_k)| ≤ c for every orthonormal family τ in ℝ^P. Then |R.action(γ)| ≤ c·μ_R(ℝ^P) (real number via ENNReal.toReal). (iv) For all N, N' ∈ ℕ, Λ ∈ ℝ≥0 and every Λ-Lipschitz F : ℝ^N → ℝ^{N'} there are C^∞ (ContDiff ℝ (⊤ : ℕ∞)) Λ-Lipschitz maps F_j : ℝ^N → ℝ^{N'} (j ∈ ℕ) with F_j → F uniformly on ℝ^N. (v) For every compact E ⊆ ℝ^P there are a C^∞ function χ : ℝ^P → ℝ with compact support and 0 ≤ χ ≤ 1, and an open W ⊇ E with χ = 1 on W. (vi) (Push-forward operator.) Assume (IPF), the conclusion of the frozen statement of dor_lmb_fcd_im_pushforward, which the parent obtains by applying that declaration to the antecedent (IMS). (IPF) says the following. Let N, N', k ∈ ℕ and let R be an IMRep of degree k in univ ⊆ ℝ^N with μ_R(ℝ^N) ≠ ∞. Then there is Y : (ℝ^N → ℝ^{N'}) → 𝒟_k(ℝ^{N'}) with two properties. (a) For every Λ ∈ ℝ≥0 and every Λ-Lipschitz F, Y(F) is IM. Moreover, for every sequence of C¹ Λ-Lipschitz maps F_j → F uniformly and every ω ∈ 𝒟^k(ℝ^{N'}), R.action(F_j^#ω) → Y(F)(ω). (b) Y(F) = Y(F') whenever F, F' are Λ-Lipschitz and F = F' H^k⌞R.carrier-a.e. Then for every P ∈ ℕ there is an operation push : ∀ k, (ℝ^P → ℝ^P) → 𝒟_k(ℝ^P) → 𝒟_k(ℝ^P) with the following property. Let k ∈ ℕ, Λ ∈ ℝ≥0, F Λ-Lipschitz, E ⊆ ℝ^P compact, and X ∈ 𝒟_k(ℝ^P) IM and vanishing off E. Then: (P1) push k F X is IM. (P2) push k F X = push k F' X for every Λ-Lipschitz F' with F = F' on E. (P3) Let F_j be C¹ Λ-Lipschitz maps with F_j → F uniformly on ℝ^P, let ω ∈ 𝒟^k(ℝ^P), and let η_j ∈ 𝒟^k(ℝ^P) be test forms with η_j(x) = F_j^#ω(x) for all x ∈ E. Then X(η_j) → push k F X(ω). (P4) M(push k F X) ≤ Λ^k·M(X). (P5) push k F X vanishes off F(E). The Lean statement is the conjunction (i) ∧ (ii) ∧ (iii) ∧ (iv) ∧ (v) ∧ ((IPF) → (vi)).

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.toolkit_push-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6428

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/986, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4544

Decomposition children: None

## Lean problem

Declaration: `Submission.dor_lmb_fcdp_toolkit_push`

```lean
((∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ') ∧ (∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal) ∧ (∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop) ∧ ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1) ∧ ((∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (Λ : NNReal) (F : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ (∀ F' : Euclid P → Euclid P, LipschitzWith Λ F' → EqOn F F' E → push k F X = push k F' X) ∧ (∀ (Fs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (push k F X ω))) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0)
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.toolkit_push-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof (dor_lmb_fcd_pushforward_homotopy). Part (i) is its step 1(a)–(c). Parts (ii)–(iii) are the Hadamard bound and the estimate (★) in its notation paragraph. Part (iv) is the mollification of step 2, and part (v) is the cut-off functions ζ and χ̃ of steps 2, 4 and 7. Part (vi) is steps 1–2 (push via IPF, Char-push), step 5(3) (locality) and step 6 (integrality, mass bound via (★), vanishing off F(E)) for push. Siblings used: dor_imrep_massOn_eq_measure_and_support (C1), covectorEuclideanNorm_gram_bounds (GB) and dpf_exists_orthonormal_frame_det_gram (GF). ContDiffBump.normed is outside the import closure of GMT.Ch07.Submission, so bumps are normalized by hand, as in the accepted proof of cmcs_lipschitz_smoothing.
Part (i). Let R = (M, θ, ξ) and W₀ := ℝ^P ∖ E, which is open because E is compact, hence closed.
1. By (C1) with U = univ (open) and T = X: X.massOn W = μ_R(W) for every open W.
2. X.massOn W₀ is the supremum of ofReal(X ω) over ω ∈ massAdmissibleOn univ k W₀. Every such ω has tsupport ω ⊆ W₀, so tsupport ω is disjoint from E and X ω = 0. Thus the supremum is taken over a subset of {0}, and X.massOn W₀ = 0 (sSup_le). By step 1, μ_R(W₀) = 0.
3. R.measure = (Hᵏ⌞M).withDensity θ, so μ_R(W₀) = ∫⁻_{M∩W₀} θ dHᵏ (withDensity_apply, Measure.restrict_apply for the measurable W₀). θ is ℕ-valued with θ(x) > 0, i.e. (θ(x) : ℝ≥0∞) ≥ 1, for x ∈ M. Hence Hᵏ(M ∩ W₀) = ∫⁻_{M∩W₀} 1 dHᵏ ≤ ∫⁻_{M∩W₀} θ dHᵏ = 0 (setLIntegral_mono; θ is measurable). As M ∖ E = M ∩ W₀, Hᵏ(M ∖ E) = 0.
4. M(X) = X.massOn univ = μ_R(univ), by step 1 with W = univ.
5. μ_R(univ) = μ_R(E) + μ_R(W₀) = μ_R(E) = ∫⁻_{M∩E} θ dHᵏ. This is ≠ ∞ by R.locallyIntegrable_mult with K = E (compact, ⊆ univ).
6. Let γ = γ' on E. The integrands x ↦ θ(x)ξ(x)(γ x) and x ↦ θ(x)ξ(x)(γ' x) agree at every x ∈ E. Their difference set lies in ℝ^P ∖ E, which is (Hᵏ⌞M)-null by step 3: (Hᵏ⌞M)(Eᶜ) = Hᵏ(M ∩ Eᶜ) = 0. So the integrands agree (Hᵏ⌞M)-a.e., and integral_congr_ae gives R.action γ = R.action γ'. No integrability is needed.
Part (ii).
7. If (v_1, …, v_m) is linearly dependent, then α(v) = 0 (AlternatingMap.map_linearDependent applied to α.toAlternatingMap). The right side is ≥ 0 (covectorEuclideanNorm_nonneg, norms ≥ 0).
8. If v is linearly independent, (GF) gives an orthonormal σ and A_{ab} = ⟨σ_a, v_b⟩ with det(⟨v_a, v_b⟩) = (det A)² and |det A| ≤ ∏‖v_a‖. By (GB)(1), |α(v)| ≤ |α|·√det(⟨v_a, v_b⟩) = |α|·√((det A)²) = |α|·|det A| ≤ |α|·∏‖v_a‖ (Real.sqrt_sq_eq_abs; |α| ≥ 0).
Part (iii). Let μ := Hᵏ⌞M and f(x) := θ(x)·ξ(x)(γ x).
9. By R.orients, for μ-a.e. x there are Q and an orthonormal τ : Fin k → ℝ^P (from IsUnitOrientationOf (ξ x) Q) such that ξ(x)(β) = β(τ) for all β, or ξ(x)(β) = −β(τ) for all β. Combine this with the hypothesis. For μ-a.e. x, |ξ(x)(γ x)| = |γ(x)(τ)| ≤ c, hence ‖f(x)‖ = θ(x)·|ξ(x)(γ x)| ≤ c·θ(x).
10. x ↦ c·θ(x) is μ-integrable: θ is measurable and ∫⁻ θ dμ = μ_R(univ) < ∞ (withDensity_apply on univ).
11. MeasureTheory.norm_integral_le_of_norm_le needs integrability only of the majorant; it gives |R.action γ| = ‖∫ f dμ‖ ≤ ∫ cθ dμ = c·∫ θ dμ. Finally ∫ θ dμ = (∫⁻ θ dμ).toReal = μ_R(univ).toReal (integral_eq_lintegral_of_nonneg_ae; θ is the cast of a natural number).
Part (iv). Fix N, N', Λ and F.
12. For j ∈ ℕ put r_j := 1/(j+1). Let b_j be the ContDiffBump centred at 0 ∈ ℝ^N with rIn = r_j/2 and rOut = r_j. It is C^∞ with 0 ≤ b_j, support b_j = ball(0, r_j), and compact support. I_j := ∫ b_j dvol > 0, because b_j ≥ 0 is continuous and integrable and its support is a ball of positive volume (integral_pos_iff_support_of_nonneg). Put ψ_j := I_j⁻¹·b_j. Then ψ_j is C^∞, ψ_j ≥ 0, ∫ψ_j = 1, support ψ_j ⊆ ball(0, r_j), and ψ_j has compact support.
13. Define F_j := ψ_j ⋆ F, i.e. F_j(x) = ∫ ψ_j(y)•F(x − y) dy (Mathlib convolution ψ_j F (ContinuousLinearMap.lsmul ℝ ℝ) volume). F is continuous, hence locally integrable, so HasCompactSupport.contDiff_convolution_left shows F_j is C^∞.
14. F_j is Λ-Lipschitz. Fix x, x'. The integrands y ↦ ψ_j(y)•F(x − y) and y ↦ ψ_j(y)•F(x' − y) are integrable (continuous, supported in the compact support of ψ_j). So F_j(x) − F_j(x') = ∫ ψ_j(y)•(F(x − y) − F(x' − y)) dy, and ‖F_j(x) − F_j(x')‖ ≤ ∫ ψ_j(y)·Λ‖x − x'‖ dy = Λ‖x − x'‖ (norm_integral_le_of_norm_le, ∫ψ_j = 1). Conclude with LipschitzWith.of_dist_le_mul.
15. For every x and y ∈ ball(x, r_j), dist(F y, F x) ≤ Λ·r_j. Apply Mathlib dist_convolution_le with support ψ_j ⊆ ball(0, r_j), ψ_j ≥ 0, ∫ψ_j = 1, F strongly measurable, z₀ := F x and ε := Λ·r_j. It gives dist(F_j x, F x) ≤ Λ·r_j for every x. Since Λ·r_j → 0, F_j → F uniformly (Metric.tendstoUniformly_iff).
Part (v). Fix a compact E.
16. Let V := thickening 1 E (open, hence measurable). Let ψ be as in step 12 with radius 1/2: C^∞, ψ ≥ 0, ∫ψ = 1, support ψ ⊆ ball(0, 1/2), compact support. Put χ := ψ ⋆ 1_V, the convolution with the indicator of V. This indicator is bounded and measurable, hence locally integrable, so χ is C^∞ by HasCompactSupport.contDiff_convolution_left.
17. χ(x) = ∫ ψ(y)·1_V(x − y) dy ∈ [0, ∫ψ] = [0, 1].
18. Let W := thickening (1/2) E. It is open, and E ⊆ W (self_subset_thickening; trivial if E = ∅). Let x ∈ W and z ∈ ball(x, 1/2). Then infDist(z, E) ≤ infDist(x, E) + dist(z, x) < 1, so z ∈ V and 1_V(z) = 1. dist_convolution_le with ε = 0 and z₀ = 1 gives χ(x) = 1.
19. Let infDist(x, E) ≥ 3/2, or E = ∅. Then every z ∈ ball(x, 1/2) has z ∉ V, so 1_V = 0 there, and dist_convolution_le with ε = 0, z₀ = 0 gives χ(x) = 0. Hence support χ ⊆ cthickening (3/2) E, which is compact (IsCompact.cthickening in the proper space ℝ^P). So χ has compact support (HasCompactSupport.of_support_subset_isCompact or closure argument).
Part (vi). Assume (IPF) and fix P. Parts (i)–(iv) above are used.
20. (Definition.) Call X ∈ 𝒟_k(ℝ^P) admissible if some IMRep R in univ represents X with μ_R(ℝ^P) ≠ ∞. For admissible X, choose (Classical.choose) such an R_X. Then use (IPF) with N = N' = P and R = R_X to choose Y_X satisfying (a) and (b). Define push k F X := Y_X(F) for admissible X, and push k F X := 0 otherwise.
21. Fix k, Λ, a Λ-Lipschitz F, a compact E and an IM X vanishing off E. By part (i) any IMRep of X has finite measure, so X is admissible. Let R := R_X = (M, θ, ξ) and Y := Y_X. By (i): H^k(M ∖ E) = 0, M(X) = μ_R(ℝ^P) < ∞, and R.action γ = R.action γ' whenever γ = γ' on E.
22. (P1): Y(F) is IM by (IPF)(a).
23. (P2): {x ∈ M : F x ≠ F' x} ⊆ M ∖ E is H^k-null, so F = F' H^k⌞M-a.e., and (IPF)(b) gives Y(F) = Y(F').
24. (P3): X(η_j) = R.action(η_j), because R represents X. This equals R.action(F_j^#ω) by step 21, since η_j = F_j^#ω on E. Finally R.action(F_j^#ω) → Y(F)(ω) by (IPF)(a).
25. By (iv) choose C^∞, hence C¹ (ContDiff.of_le), Λ-Lipschitz F_j → F uniformly. Then push k F X(ω) = lim_j R.action(F_j^#ω) for every ω, by (IPF)(a).
26. (P4): Let ω satisfy |ω(y)| ≤ 1 for all y. For all j, x and orthonormal τ: ‖DF_j(x)‖ ≤ Λ (norm_fderiv_le_of_lipschitz), so by (ii) |F_j^#ω(x)(τ)| = |ω(F_j x)(DF_j(x)τ_1, …, DF_j(x)τ_k)| ≤ |ω(F_j x)|·∏‖DF_j(x)τ_i‖ ≤ Λ^k. By (iii) with c = Λ^k, |R.action(F_j^#ω)| ≤ Λ^k·μ_R(ℝ^P).toReal. Let j → ∞ (step 25): push k F X(ω) ≤ Λ^k·M(X).toReal. Hence ofReal(push k F X(ω)) ≤ Λ^k·M(X), using M(X) < ∞, ENNReal.ofReal_mul, ENNReal.ofReal_toReal and (Λ : ℝ≥0∞)^k = ofReal(Λ^k). Taking sSup over massAdmissibleOn univ k univ (sSup_le) gives (push k F X).mass ≤ Λ^k·M(X).
27. (P5): Let tsupport ω ∩ F(E) = ∅.
   If tsupport ω = ∅ then ω = 0, and push k F X(ω) = 0 by linearity.
   If E = ∅ then H^k(M) = 0, so every R.action vanishes (integral over a null set), and push k F X(ω) = lim 0 = 0.
   Otherwise let K := tsupport ω (closed, nonempty). e ↦ infDist(F e, K) is continuous and positive on the compact E (IsClosed.notMem_iff_infDist_pos), so d := min_E infDist(F e, K) > 0. Choose j₀ with ‖F_j − F‖_∞ < d for j ≥ j₀. For j ≥ j₀ and x ∈ E, F_j x ∉ K, since otherwise infDist(F x, K) ≤ dist(F x, F_j x) < d. So ω(F_j x) = 0 (image_eq_zero_of_notMem_tsupport) and F_j^#ω(x) = 0. Hence R.action(F_j^#ω) = R.action(0) = 0 for j ≥ j₀ by step 21, and push k F X(ω) = 0. ∎

## Key steps

1. (i) By C1, M_{ℝ^P∖E}(X) = μ_R(ℝ^P∖E); test forms supported off E are killed by X, so μ_R(ℝ^P∖E) = 0, hence Hᵏ(M∖E) = 0 (θ ≥ 1).
2. (i) M(X) = μ_R(ℝ^P) = μ_R(E) < ∞ by local integrability; forms equal on E have a.e. equal integrands.
3. (ii) Linearly dependent: α(v) = 0. Independent: Gram bound |α(v)| ≤ |α|√det G(v) and the Gram–Schmidt frame det G(v) = (det A)², |det A| ≤ ∏|v_i|.
4. (iii) A.e. ξ(x) = ±(evaluation at an orthonormal frame), so |θξ(γ)| ≤ cθ; integrate against the finite measure μ_R.
5. (iv) Convolve with hand-normalized C^∞ bumps of radius 1/(j+1): smooth, Λ-Lipschitz, and within Λ/(j+1) of F (dist_convolution_le).
6. (v) Convolve the indicator of thickening 1 E with a bump of radius 1/2: smooth, values in [0,1], 1 on thickening 1/2 E, supported in cthickening 3/2 E.
7. (vi) push k F X := Y_{R_X}(F) from IPF for a chosen finite-mass IMRep R_X; integrality and locality from IPF (a), (b); Char-push from X(η_j) = R.action(F_j^#ω) → Y(F)(ω).
8. (vi) Mass from Hadamard and the frame action bound applied to mollified F_j: |R.action(F_j^#ω)| ≤ Λ^k M(X); vanishing because F_j^#ω = 0 on E for large j when tsupport ω avoids F(E).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical)`
- `rg -n 'theorem extDeriv_pullback|analyticOnNhd_compContinuousLinearMapCLM|theorem dist_convolution_le|theorem volume_preserving_piFinSuccAbove|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem curryLeft_compContinuousLinearMap|theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|Filter.EventuallyEq.extDeriv_eq|theorem det_succ_row_zero' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'measure_compl_support|theorem integral_comp_comm|theorem integral_eq_sub_of_hasDerivAt|theorem norm_fderiv_le_of_lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'pushforward|homotop|cartan|curryLeft|dor_lmb_fcdp' local-references/123e8435b4a2469b/project/GMT -g '*.lean' (only sorry-frozen Ch06 IsLipschitzPushforward/LipschitzPushforwardIntegerMultiplicity and Ch07 affinePushforward; no Lipschitz push-forward, product current, homotopy formula or Cartan theorem)`
- `grep -n 'def |theorem ' SimonGMT Chapter06/{Forms,Currents,Mass,WedgeForms,Product,GeometricPointProduct,CurrentLocalEquality}.lean, Chapter03/Rectifiable.lean, Chapter02/AreaLipschitz.lean`
- `lake env lean Avail.lean/Avail2.lean/Avail3.lean/Elab.lean: #check every cited Mathlib/SimonGMT lemma after import GMT.Ch07.Submission (unavailable: ContDiffBump.normed, intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le, SimonGMT Chapter02 area formulas, Matrix.det_gram_ne_zero_iff_linearIndependent)`
- `python3 -I scans of dag.json: status/frozen types of dor_lmb_fcd_im_pushforward (decomposing), dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, covectorEuclideanNorm_gram_bounds, dpf_exists_orthonormal_frame_det_gram, dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, codim1_lura_gram_area_formula (accepted, byte-identical), cmcdt_lipschitz_pushforward_homotopy subtree (not accepted); regex searches for Hadamard, area-formula and mollification lemmas; freshness of dor_lmb_fcdp_* names`
- `git show a95facf7331f:GMT/Ch07/Submission.lean (accepted dpf_pb_smooth_pullback_isTestForm: analyticOnNhd_compContinuousLinearMapCLM + ContDiff.clm_apply)`
- `sed runtime.py (_decompose max_depth, _existing_lean_name_problem, _overlay_accepted_children) and verifier/gmt-compare.py contract_scope`
- `lake env lean /tmp/pfc-decomp-k7q2/lean/AllTypes.lean and Assembly.lean with #print axioms; python3 /tmp/pfc-decomp-k7q2/py/cartan_check2.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-7c9243c42e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/pfc-decomp-k7q2/lean/AllTypes.lean`
- `/tmp/pfc-decomp-k7q2/lean/Assembly.lean`
- `/tmp/pfc-decomp-k7q2/py/cartan_check2.py`

The snapshot (project b4d606db, mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace one. Neither the snapshot nor SimonGMT has a proved Lipschitz push-forward of currents, product current, homotopy formula or Cartan formula. SimonGMT Chapter06 offers only affine push-forwards and point products, and the snapshot's Ch06 Lipschitz push-forward is a sorry-frozen definition outside the import closure. The import closure of GMT.Ch07.Submission lacks SimonGMT Chapter02 area formulas, ContDiffBump.normed and intervalIntegral parametric derivatives. It has every Mathlib lemma the child proofs cite (all located in the snapshot mathlib): extDeriv_pullback, EventuallyEq.extDeriv_eq, analyticOnNhd_compContinuousLinearMapCLM, curryLeft_compContinuousLinearMap, hasFDerivAt_integral_of_dominated_of_fderiv_le, dist_convolution_le, contDiff_convolution_left, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, det_succ_row_zero, measure_compl_support, euclideanHausdorffMeasure_eq_volume, integral_eq_sub_of_hasDerivAt. The missing area formula and Hadamard and piece facts come from six comparator-accepted DAG declarations reused with byte-identical types. IPF is unaccepted, so it is passed as an exact-type antecedent and discharged by this node with Submission.dor_lmb_fcd_im_pushforward hIMS. All 12 child types compile as exact challenges. The conditional assembly proves this node's frozen type with axioms [propext, Classical.choice, Quot.sound]. The six new dor_lmb_fcdp_* names are fresh in dag.json.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
