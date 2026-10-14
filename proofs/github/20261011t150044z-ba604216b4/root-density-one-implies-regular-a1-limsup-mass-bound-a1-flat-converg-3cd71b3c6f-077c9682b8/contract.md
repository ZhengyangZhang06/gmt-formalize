<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1 -->

## Theorem `Submission.dor_lmb_fcd_im_pushforward`

Conventions: ℝ^P = Euclid P and Hᵈ = μHE[d]. For U ⊆ ℝ^P, 𝒟^d(U) = TestFormOn U d (smooth d-forms on ℝ^P with compact support contained in U) and 𝒟_d(U) = GeometricCurrentOn U d; ∂X = X.boundary (∂X(ω) = X(dω)); X − Y is the contract subtraction (pointwise on test forms). For G ⊆ ℝ^P, M_G(X) = X.massOn G is the supremum of max(X(ω), 0) over ω ∈ 𝒟^d(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x, where |·| is the Euclidean coefficient norm of covectors (covectorEuclideanNorm); M(X) = X.mass = M_U(X). An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U d; R represents X when X(ω) = ∫_M θ⟨ω, ξ⟩ dHᵈ for every ω ∈ 𝒟^d(U), where ⟨ω, ξ⟩(x) = ξ(x)(ω(x)); μ_R = θ·Hᵈ⌞M is R.measure and R.action(β) = ∫_M θ ξ(β) dHᵈ for any d-form β; X is integer multiplicity (IM, IsIntegerMultiplicity X) if some IMRep represents it. X vanishes off a set E if X(ω) = 0 for every ω whose tsupport is disjoint from E. Assume (IMS) the exact frozen statement of dor_lmb_fc_im_series (a resolved dependency of the parent node, not yet accepted, hence taken as an antecedent): for all P, m, every open U ⊆ ℝ^P and IM currents X_r ∈ 𝒟_{m+1}(U) (r ∈ ℕ) with Σ_r M(X_r) ≠ ∞ there is an IM Y ∈ 𝒟_{m+1}(U) with Σ_r X_r(ω) = Y(ω) (HasSum) for every ω ∈ 𝒟^{m+1}(U) and M(Y) ≤ Σ_r M(X_r). For all N, N', k ∈ ℕ and every IMRep R = (M, θ, ξ) of degree k in univ ⊆ ℝ^N with finite total measure R.measure(ℝ^N) ≠ ∞, there is a function Y assigning to every map F : ℝ^N → ℝ^{N'} a current Y(F) ∈ 𝒟_k(ℝ^{N'}) (domain univ) such that: (a) for every Λ ∈ ℝ≥0 and every Λ-Lipschitz F, Y(F) is IM and, for every sequence of C¹ Λ-Lipschitz maps F_j : ℝ^N → ℝ^{N'} converging uniformly to F and every ω ∈ 𝒟^k(ℝ^{N'}), R.action(F_j^#ω) → Y(F)(ω), where F_j^#ω(x) := ω(F_j(x)) ∘ DF_j(x) (in Lean (ω (F_j x)).compContinuousLinearMap (fderiv ℝ F_j x)); (b) if F, F' are Λ-Lipschitz and F(x) = F'(x) for Hᵏ-a.e. x ∈ M, then Y(F) = Y(F'). (Y(F) is Simon's F_#τ(M, θ, ξ) of 3.6, which is IM by 3.9 and is the limit of the smooth push-forwards of 2.24(2), 2.29.)

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5455

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6421, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5186, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7223, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7226, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7227, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7231, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7233, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7235, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7237

## Lean problem

Declaration: `Submission.dor_lmb_fcd_im_pushforward`

```lean
(∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F'
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 3.3–3.9 (push-forward of an integer multiplicity current τ(M, θ, ξ) by a Lipschitz map via the area formula, chapter-06.txt from "Next we want to discuss pushing forward an integer multiplicity" to Lemma 3.9), together with Remark 2.24(2),(3) and Lemma 2.29 (the push-forward by a Lipschitz map as the limit of push-forwards by smooth maps). The book defines f_#T for Lipschitz f by the integral formula 3.6 and remarks that it agrees with 2.23 for C¹ maps, but it does not prove that the limit of 2.29 equals the formula 3.6 when f is merely Lipschitz; the deformation proof uses both descriptions. Step 5 below supplies this identification (weak continuity of pulled-back forms under uniform convergence with bounded Lipschitz constants). This is the integrality part ("these push-forwards map IM currents to IM currents", Ch. 6, 3.6–3.9) cited in steps 4–5 of the parent proof. Dependencies: (IMC) = the reused sibling cmc_imRep_locality_restrict_sub (parts (a), (d)); WC = the sibling dor_lmb_fcd_jacobian_weak_continuity (step 5); (IMS) = the antecedent of the statement (frozen type of dor_lmb_fc_im_series), used in step 7. Accepted DAG theorems named below (dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_measurable_ae_pullback, ptd_piece_image_approxTangent_ae when accepted, dpf_itt_approxTangentPlane_eq) are not siblings of this node: they may be reused as children if this node is decomposed; otherwise the arguments given here are formalized directly.

Notation. R = (M, θ, ξ) is an IMRep of degree k in univ ⊆ ℝ^N (Euclid N) with μ_R(ℝ^N) = ∫_M θ dHᵏ < ∞; Hᵏ = μHE[k]; Lᵏ is Lebesgue measure on ℝᵏ = Euclid k; e := (e_1, …, e_k) the standard basis of ℝᵏ. For a k-form β on ℝ^{N'} and a map H, H^#β(u) := β(H(u)) ∘ DH(u) wherever H is differentiable (in Lean, (β (H u)).compContinuousLinearMap (fderiv ℝ H u)); R.action(γ) = ∫_M θ ξ(γ) dHᵏ. |α| is the Euclidean coefficient norm of a covector, ‖ω‖ := sup_y |ω(y)|. For vectors v_1, …, v_k: |α(v_1, …, v_k)| ≤ |α|·|v_1 ∧ ⋯ ∧ v_k| ≤ |α||v_1|⋯|v_k| (expand α in the orthonormal basis dy^I, apply Cauchy–Schwarz, and use Σ_I det(v^I)² = det(v_i·v_j) ≤ Π|v_i|², Hadamard). By (IMC)(d) and the orientation field of R, for Hᵏ-a.e. x ∈ M, ξ(x)(α) = ±α(τ_1, …, τ_k) for an orthonormal basis τ of the approximate tangent space T_xM. Hence for a Λ-Lipschitz C¹ map F_j : ℝ^N → ℝ^{N'} (‖DF_j‖ ≤ Λ):
 (0) |ξ(x)(F_j^#ω(x))| = |ω(F_j x)(DF_j τ_1, …, DF_j τ_k)| ≤ Λ^k‖ω‖ for a.e. x ∈ M, so R.action(F_j^#ω) is an absolutely convergent integral with |R.action(F_j^#ω)| ≤ Λ^k‖ω‖μ_R(ℝ^N).

1. Case k = 0. μHE[0] = μH[0] is the counting measure; θ ≥ 1 on M and Σ_{x∈M}θ(x) < ∞, so M is finite, and (since H⁰ has no nonempty null sets) for every x ∈ M, ξ(x)(α) = ε(x)α with ε(x) ∈ {1, −1} (the only 0-dimensional subspace is {0}; its unit orientations are ±1). For any F put Y(F)(ω) := Σ_{x∈M} θ(x)ε(x)ω(F(x)); it is linear in ω and |Y(F)(ω)| ≤ μ_R(ℝ^N)‖ω‖, so Y(F) ∈ 𝒟_0(ℝ^{N'}). For 0-forms F_j^#ω = ω∘F_j, so if F_j → F pointwise then R.action(F_j^#ω) = Σ_x θ(x)ε(x)ω(F_j x) → Y(F)(ω). Integrality: for y ∈ F(M) let c(y) := Σ_{x∈M, F(x)=y} θ(x)ε(x) ∈ ℤ; the finite set M' := {y : c(y) ≠ 0} with multiplicity |c(y)| and orientation sign(c(y))·id is an IMRep (finite sets are Borel, countably 0-rectifiable, and have approximate tangent space {0} at each of their points: the blow-ups of a finite set at one of its points converge to the point mass at 0) whose action is Y(F). Locality: if F = F' H⁰-a.e. on M, i.e. on all of M, then Y(F) = Y(F'). This proves the statement for k = 0. From now on k ≥ 1.

2. Parametrization (Simon 3.1 with Ch. 3, 1.1; cmc B1). There are countably many compact sets B_i ⊆ ℝᵏ, Lipschitz maps G_i : ℝᵏ → ℝ^N and constants κ_i > 0 such that: G_i is differentiable at every u ∈ B_i with DG_i(u) injective; κ_i|u − v| ≤ |G_i(u) − G_i(v)| for u, v ∈ B_i; the sets G_i(B_i) ⊆ M are pairwise disjoint (and Borel); and Hᵏ(M ∖ ⋃_i G_i(B_i)) = 0. This is the accepted DAG theorem dpf_rectifiable_bilipschitz_pieces (Borel pieces), followed by inner regularity: each Borel piece B is, up to an Lᵏ-null set, a countable disjoint union of compact sets, and the image of an Lᵏ-null set under a Lipschitz map is Hᵏ-null (Mathlib LipschitzOnWith.hausdorffMeasure_image_le). Its proof: M ⊆ M₀ ∪ ⋃_j F_j(ℝᵏ) with Hᵏ(M₀) = 0 and F_j Lipschitz (CountablyRectifiable); by Rademacher the non-differentiability set of F_j is null and has null image; the image of the critical set {DF_j not injective} is null (area formula, the Jacobian vanishes there; SimonGMT area_image_criticalSet_eq_zero); the remaining set is partitioned with Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt into Borel pieces on which F_j is bi-Lipschitz (approximation of an injective linear map with constant less than half its co-norm), and pieces are made disjoint inductively (images of Borel sets under injective continuous maps are Borel, Mathlib MeasurableSet.image_of_continuousOn_injOn).

3. Tangent planes of pieces (cmc B2). Let A ⊆ ℝᵏ be compact and G : ℝᵏ → ℝ^N Lipschitz, differentiable on A, with κ|u − v| ≤ |G(u) − G(v)| on A. Then for Lᵏ-a.e. u ∈ A, DG(u) is injective and G(A) has approximate tangent space V := DG(u)(ℝᵏ) at G(u) (HasApproximateTangentSpaceAt k (G(A)) (G u) V). Proof: let u be a Lebesgue density point of A and a Lebesgue point of 1_A·JG, where JG := |Λ_kDG e| = √det(DGᵀDG). Density gives, for every unit w, points v ∈ A with v − u = tw + o(t), so |DG(u)w| ≥ κ and JG(u) ≥ κ^k > 0. For f ∈ C_c(ℝ^N) with spt f ⊆ B_ρ(0), the injective area formula (SimonGMT injective_area_formula_lipschitz) and the scaling of Hᵏ give ∫_{blowUpMap (G u) t '' G(A)} f dHᵏ = ∫_{ℝᵏ} 1_A(u + tw) f((G(u + tw) − G(u))/t) JG(u + tw) dw. The integrand vanishes for |w| ≥ ρ/κ; on B_{ρ/κ}(0), (G(u + tw) − G(u))/t → DG(u)w uniformly and 1_A(u + t·)JG(u + t·) → JG(u) in L¹; so the integral tends to ∫ f(DG(u)w)JG(u) dw = ∫_V f dHᵏ (area formula for the linear map DG(u)).
 Consequence (B2′). Since Hᵏ(M ∩ K') < ∞ for compact K' (θ ≥ 1, μ_R finite), (IMC)(a) applied to G_i(B_i) ⊆ M shows: for Hᵏ-a.e. x ∈ G_i(B_i), T_xM exists and equals DG_i(u)(ℝᵏ), u = (G_i|B_i)⁻¹(x). At such x the IMRep field `orients` gives a subspace Q with HasApproximateTangentSpaceAt k M x Q and ξ(x) a unit orientation of Q; approximate tangent spaces are unique (the defining limits determine the measure Hᵏ⌞Q, hence Q; accepted DAG theorem dpf_itt_approxTangentPlane_eq), so Q = DG_i(u)(ℝᵏ). Two unit orientations of the same k-plane differ by a sign, and Λ_kDG_i(u)e/JG_i(u) (the k-vector α ↦ α(DG_i(u)e_1, …, DG_i(u)e_k)/JG_i(u)) is a unit orientation of it; hence there is a Borel s_i : B_i → {1, −1} with
 (B2′) ξ(G_i(u))(α) = s_i(u)·α(DG_i(u)e_1, …, DG_i(u)e_k)/JG_i(u) for Lᵏ-a.e. u ∈ B_i and all α.
 (Preimages of Hᵏ-null subsets of G_i(B_i) under G_i|B_i are Lᵏ-null, because G_i⁻¹ is Lipschitz on G_i(B_i); accepted DAG theorem ptd_piece_image_measurable_ae_pullback.)

4. Transfer to the parameter domains. Put θ_i := θ∘G_i and w_i := θ_i s_i on B_i. Since JG_i ≥ κ_i^k on B_i (step 3), ∫_{B_i}|w_i| du ≤ κ_i^{−k}∫_{B_i}θ_iJG_i du = κ_i^{−k}μ_R(G_i(B_i)) < ∞ (injective area formula). For every bounded Borel k-form γ on ℝ^N, the area formula on each B_i, (B2′) and step 2 give
 R.action(γ) = Σ_i ∫_{B_i} w_i(u)·γ(G_i u)(DG_i(u)e_1, …, DG_i(u)e_k) du,
 the series converging absolutely (term i is at most sup|γ|·μ_R(G_i(B_i)), since |γ(DG_i e)| ≤ |γ|JG_i). For γ := F_j^#ω with F_j C¹: γ(G_iu)(DG_i(u)e) = ω(F_j(G_iu))(DF_j(G_iu)DG_i(u)e) = (H_{ij}^#ω)(u)(e), where H_{ij} := F_j∘G_i is Lipschitz (constant ΛLip G_i) and differentiable on B_i with DH_{ij} = DF_j(G_i·)DG_i (chain rule). So
 (4.1) R.action(F_j^#ω) = Σ_i ∫_{B_i} w_i (H_{ij}^#ω)(e) du, with |term i| ≤ Λ^k‖ω‖μ_R(G_i(B_i)).

5. Weak continuity of pulled-back forms (fills the gap between 2.29 and 3.6). This is the sibling theorem WC = dor_lmb_fcd_jacobian_weak_continuity: if A ⊆ ℝᵏ is measurable, w ∈ L¹(A), H_j, H : ℝᵏ → ℝ^{N'} are L-Lipschitz with H_j → H uniformly on ℝᵏ and ω ∈ 𝒟ᵏ(ℝ^{N'}), then ∫_A w·ω(H_j(u))(DH_j(u)e_1, …, DH_j(u)e_k) du → ∫_A w·ω(H(u))(DH(u)e_1, …, DH(u)e_k) du (derivatives via fderiv, which exist a.e. by Rademacher). It is applied with A := B_i (compact, hence measurable), w := w_i, H_j := F_j∘G_i and H := F∘G_i, which are (Λ·Lip G_i)-Lipschitz with F_j∘G_i → F∘G_i uniformly on ℝᵏ because F_j → F uniformly on ℝ^N; at every u ∈ B_i, D(F_j∘G_i)(u) = DF_j(G_iu)DG_i(u) (chain rule), so its integrand is the integrand of (4.1).

6. The current Y(F) (Simon 3.6). For Λ-Lipschitz F : ℝ^N → ℝ^{N'} let H_i := F∘G_i (Lipschitz, differentiable a.e.) and define
 Y(F)(ω) := Σ_i ∫_{B_i} w_i (H_i^#ω)(e) du.
 At every u ∈ B_i where H_i is differentiable (G_i is differentiable at u), |DH_i(u)v| = lim_{t↓0}|F(G_i(u + tv)) − F(G_i(u))|/t ≤ Λ·lim_{t↓0}|G_i(u + tv) − G_i(u)|/t = Λ|DG_i(u)v|, so |(H_i^#ω)(u)(e)| ≤ ‖ω‖|Λ_kDH_i(u)e| ≤ ‖ω‖Λ^kJG_i(u) and term i is at most Λ^k‖ω‖μ_R(G_i(B_i)). So the series converges absolutely, Y(F) is linear in ω with |Y(F)(ω)| ≤ Λ^k‖ω‖μ_R(ℝ^N), hence sequentially continuous on test forms: Y(F) ∈ 𝒟_k(ℝ^{N'}). (For non-Lipschitz F put Y(F) := 0.)
 Limit property. Let F_j be C¹, Λ-Lipschitz, F_j → F uniformly. For each i, H_{ij} = F_j∘G_i → H_i uniformly with Lipschitz constants ≤ ΛLip G_i, so by WC (step 5; w = w_i ∈ L¹(B_i), B_i compact) term i of (4.1) converges to term i of Y(F)(ω); all terms are bounded by the summable Λ^k‖ω‖μ_R(G_i(B_i)); by dominated convergence for series, R.action(F_j^#ω) → Y(F)(ω).
 Locality. Let F, F' be Λ-Lipschitz with F = F' Hᵏ-a.e. on M. Then Z_i := {u ∈ B_i : H_i(u) ≠ H'_i(u)} has G_i(Z_i) Hᵏ-null, so Z_i is Lᵏ-null (step 3); at every density point of B_i ∖ Z_i where H_i, H'_i are differentiable (a.e. u ∈ B_i), DH_i(u) = DH'_i(u) (the derivative of a Lipschitz map at a density point of a set is determined by its values on that set). So the integrands agree a.e. and Y(F) = Y(F').

7. Integrality (Simon 3.6–3.9; cmc B3). Fix Λ-Lipschitz F. Let A_i⁺ := {u ∈ B_i : H_i differentiable at u, DH_i(u) injective}. On B_i ∖ A_i⁺ (up to a null set) Λ_kDH_i e = 0, so (H_i^#ω)(e) = 0 there. Apply step 2's partition argument to H_i on A_i⁺: up to an Lᵏ-null set, A_i⁺ is a countable disjoint union of compact A_{il} on which H_i is injective with |H_i(u) − H_i(v)| ≥ κ_{il}|u − v|. Let N_{il} := H_i(A_{il}) (compact), g_{il} := w_i∘(H_i|A_{il})⁻¹ (a nonzero integer, ±θ) and η_{il} := (Λ_kDH_i e/JH_i)∘(H_i|A_{il})⁻¹ (a unit simple k-vector). By step 3 applied to H_i on A_{il}, for Hᵏ-a.e. y ∈ N_{il}, N_{il} has approximate tangent space DH_i(u)(ℝᵏ) at y = H_i(u), which η_{il}(y) orients. Hence (N_{il}, |g_{il}|, sign(g_{il})η_{il}) is an IMRep in univ ⊆ ℝ^{N'} (N_{il} is Borel and countably k-rectifiable as a Lipschitz image of a compact set, extended to ℝᵏ by Mathlib LipschitzOnWith.extend_pi; the multiplicity is a positive integer, Borel, with ∫_{N_{il}}|g_{il}| dHᵏ = ∫_{A_{il}}|w_i|JH_i du < ∞; the orientation is Borel and orients the approximate tangent spaces). Let Φ_{il} be the current it represents (its action is a current: linear, bounded by ‖ω‖∫|g_{il}|). By the injective area formula for H_i on A_{il},
 ∫_{A_{il}} w_i (H_i^#ω)(e) du = ∫_{A_{il}} w_i ⟨ω(H_i u), η_{il}(H_i u)⟩JH_i(u) du = Φ_{il}(ω),
 so Y(F)(ω) = Σ_{i,l} Φ_{il}(ω), absolutely convergent. M(Φ_{il}) ≤ ∫_{N_{il}}|g_{il}| dHᵏ (for admissible ω, |⟨ω, η⟩| ≤ |ω| ≤ 1), and Σ_{i,l}∫_{N_{il}}|g_{il}| = Σ_{i,l}∫_{A_{il}}|w_i|JH_i ≤ Λ^kΣ_i∫_{B_i}θ_iJG_i = Λ^kμ_R(ℝ^N) < ∞ (JH_i ≤ Λ^kJG_i as in step 6). Enumerate the countably many pairs (i, l) by ℕ, padding with zero currents (IM: the IMRep with empty carrier). (IMS), with U = univ (open), degree k = (k − 1) + 1 and these IM currents of summable mass, gives an IM current Y' with Σ_{i,l}Φ_{il}(ω) = Y'(ω) for every ω. Hence Y(F) = Y' (GeometricCurrentOn.ext) is integer multiplicity.

8. Conclusion. The function F ↦ Y(F) of steps 1 and 6 satisfies the three requirements: Y(F) is IM for Λ-Lipschitz F (steps 1, 7); R.action(F_j^#ω) → Y(F)(ω) for every sequence of C¹ Λ-Lipschitz F_j converging uniformly to F and every test form ω (steps 1, 6); and Y(F) = Y(F') when F = F' Hᵏ-a.e. on the carrier (steps 1, 6). ∎

## Key steps

1. k = 0: the carrier is finite and Y(F) = Σ θ(x)ε(x)δ_{F(x)}, an IM 0-current; the limit and locality are immediate.
2. k ≥ 1: parametrize M up to a null set by compact bi-Lipschitz pieces G_i(B_i); at a.e. u, T_{G_i u}M = DG_i(u)(ℝᵏ) (density-point blow-up with the area formula and (IMC)(a)), so ξ(G_i u) = ±Λ_kDG_i(u)e/JG_i(u).
3. Transfer: R.action(F_j^#ω) = Σ_i ∫_{B_i} w_i (F_j∘G_i)^#ω(e) du with w_i = θ_i s_i ∈ L¹, absolutely convergent.
4. The sibling WC (weak continuity of pulled-back forms) passes to the limit term by term; dominated convergence over i gives R.action(F_j^#ω) → Y(F)(ω) := Σ_i ∫ w_i (F∘G_i)^#ω(e).
5. Locality: equal maps a.e. on M give equal parameter maps a.e. on B_i and equal derivatives at density points.
6. Integrality: split the injective-derivative part of each B_i into bi-Lipschitz pieces A_il; the area formula writes Y(F) = Σ Φ_il with IM Φ_il = τ(H_i(A_il), |g_il|, ±η_il) of summable mass; (IMS) makes the sum IM.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -l -i "latticeFace|DeformationTheorem|deformation theorem|skeleton|retraction" local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean)`
- `rg -n "latticeFace|def DeformationTheorem|IsLatticeChain|pushforward|homotopy|Poincar" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `rg -n "theorem hausdorffMeasure_smul₀|theorem integral_map_equiv|theorem restrict_map|exists_disjoint_subfamily_covering_enlargement|theorem extend_real|theorem cthickening_cthickening_subset|theorem cthickening_eq_biUnion_closedBall|theorem lipschitz_infDist_pt|theorem ae_differentiableAt" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -c for extend_pi, integral_lineDeriv_mul_eq, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, image_of_continuousOn_injOn, ae_convolution_tendsto_right_of_locallyIntegrable, euclideanHausdorffMeasure_image, hausdorffMeasure_image_le, measure_compl_support, measurable_fderiv in Mathlib (all present)`
- `grep -n "theorem integral_lineDeriv_mul_eq" Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,140p Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d], isometry invariance)`
- `grep -n "^def |^theorem" SimonGMT Chapter06/{Product,GeometricPointProduct,AffineCurrentPushforward,Currents,Mass,CurrentLocalEquality,Forms}.lean (only affine push-forward and point products; no Lipschitz push-forward, no [[(0,1)]] × T, no homotopy formula)`
- `grep -rn "theorem [a-zA-Z_.]*area" .lake/packages/simongmt/Poincare/SimonGMT (Chapter02 area formulas: injective_area_formula_lipschitz, area_image_criticalSet_eq_zero, ...)`
- `grep -n "def HasApproximateTangentSpaceAt|def CountablyRectifiable|def blowUpMap" SimonGMT/Chapter03/Rectifiable.lean`
- `rg -c exteriorDerivativeOn_pullbackFormWithin, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.boundary, countablyRectifiable_of_measure_zero in SimonGMT (present)`
- `python3 -I scans of dag.json (1366 nodes, 2026-10-13T14:15Z): statuses and frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub (accepted), dor_lmb_fc_im_series (decomposing), dor_lmb_slicing_lipschitz (speculative-ready), accepted dpf_*/ptd_*/pit_*/dtc_* helpers; byte-identical types of cmcdt_skeleton_retraction, cmcdt_good_center, dimred_mbl_dt_*; freshness of the dor_lmb_fcd_* names`
- `python3 -I parse of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `sed -n 340,960p and 1400,1965p book/chapter-06.txt; sed -n 470,700p book/chapter-02.txt`
- `sed -n 6660,6760p and 3210,3260p /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py (_existing_lean_name_problem, accepted-child overlay scoping)`
- `lake env lean /tmp/dfm-decomp/lean/Challenge_*.lean (12 exact comparator challenges), AllProps.lean, Assembly.lean and UnitAssembly.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/dfm-decomp/lean/Assembly.lean`
- `/tmp/dfm-decomp/lean/UnitAssembly.lean`
- `/tmp/dfm-decomp/lean/AllProps.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot nor SimonGMT contains a proved Deformation Theorem, Lemma 5.4, a Lipschitz push-forward of currents, the product [[(0,1)]] × T, or the homotopy formula: SimonGMT Chapter06 provides only affine push-forwards and point products (plus currents, boundary, massOn, support, weak convergence with lower semicontinuity); Chapter02 provides area formulas for Lipschitz maps; Chapter03 the literal approximate-tangent-space definition. The snapshot's GMT/Ch06/Contract.lean has only sorry-frozen latticeFace/IsLatticeChain/DeformationTheorem definitions (the same unit and ρ-cells as the child face formulas), not imported by GMT.Ch07.Submission. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (Vitali covering, cthickening lemmas, lipschitz_infDist_pt, integral_map_equiv, MeasurableEquiv.restrict_map, hausdorffMeasure_smul₀, integral_lineDeriv_mul_eq, Rademacher, measurable_fderiv, convolution a.e. convergence, Isometry.euclideanHausdorffMeasure_image, measure_compl_support). Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted with byte-identical frozen types (standard axioms per acceptance); dor_lmb_fc_im_series (decomposing) and dor_lmb_slicing_lipschitz (speculative-ready) are passed as exact-type antecedents. Lean: all 12 child types compile as exact comparator challenges; parent_assembly and unit_assembly compile with axioms [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
