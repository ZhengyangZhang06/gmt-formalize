<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1 -->

## Theorem `Submission.dor_lmb_fc_deformation`

Assume (SL) the exact frozen statement of dor_lmb_slicing_lipschitz (a dependency of the parent node), taken as an antecedent: assuming (C1), for every open U ⊆ ℝ^P, every T ∈ 𝒟_{k+1}(U) represented by an IMRep RT = (M, θ, ξ), every IMRep RB = (M', θ', ξ') representing ∂T and every L-Lipschitz f : ℝ^P → ℝ, there are P_t ∈ 𝒟_k(U) (t ∈ ℝ) such that (1) for every open W, t ↦ M_W(P_t) is a.e.-measurable and ∫_ℝ M_W(P_t) dt ≤ L·M_W(T); (2) for L¹-a.e. t: P_t is IM, P_t(ω) = 0 for every ω whose tsupport is disjoint from f⁻¹(t), and P_t(ω) = ∫_{M∩{f<t}} θ⟨dω, ξ⟩ dH^{k+1} − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩ dH^k for every ω ∈ 𝒟^k(U). Conventions: ℝ^P = Euclid P and Hᵈ = μHE[d]. For U ⊆ ℝ^P, 𝒟^d(U) = TestFormOn U d (smooth d-forms on ℝ^P with compact support contained in U) and 𝒟_d(U) = GeometricCurrentOn U d; ∂X = X.boundary (∂X(ω) = X(dω)); X − Y is the contract subtraction (pointwise on test forms). For G ⊆ ℝ^P, M_G(X) = X.massOn G is the supremum of max(X(ω), 0) over ω ∈ 𝒟^d(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x, where |·| is the Euclidean coefficient norm of covectors (covectorEuclideanNorm); M(X) = X.mass = M_U(X). An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U d; R represents X when X(ω) = ∫_M θ⟨ω, ξ⟩ dHᵈ for every ω ∈ 𝒟^d(U), where ⟨ω, ξ⟩(x) = ξ(x)(ω(x)); μ_R = θ·Hᵈ⌞M is R.measure; X is integer multiplicity (IM, IsIntegerMultiplicity X) if some IMRep represents it. X vanishes off a set K if X(ω) = 0 for every ω whose tsupport is disjoint from K. X_j ⇀ Y (WeaklyConvergesOn) means X_j(ω) → Y(ω) for every ω. V ⊂⊂ U (CompactlyContained V U) means that closure V is compact and contained in U. Let P, m ∈ ℕ with n := m + 1 < P. There is c ≥ 0 such that for every ρ > 0, every compact K ⊆ ℝ^P and every IM T ∈ 𝒟_n(ℝ^P) (domain univ) with ∂T IM and T vanishing off K, there are a finite set s of pairs p = (z_p, ι_p) ∈ ℤ^P × (Fin n → Fin P) with ι_p strictly increasing, integers β_p (a function β on such pairs) and currents Π ∈ 𝒟_n(ℝ^P), R ∈ 𝒟_{n+1}(ℝ^P), S ∈ 𝒟_n(ℝ^P) such that: Π(ω) = Σ_{p∈s} β_p ∫_{F_p} ω(x)(e_{ι_p(0)}, …, e_{ι_p(m)}) dHⁿ(x) for every ω ∈ 𝒟ⁿ(ℝ^P), where e_i = EuclideanSpace.single i 1 and F_p := {x : ρz_{p,i} ≤ x_i ≤ ρ(z_{p,i} + 1) for i ∈ range ι_p, x_i = ρz_{p,i} otherwise} is the closed n-face ρ(z_p + F_{ι_p}) of the cubical grid of side ρ (Simon's 𝓛_n(ρ); the same cells as latticeFace in the project's GMT/Ch06/Contract.lean), oriented by e_{ι_p(0)}∧⋯∧e_{ι_p(m)}; R and S are IM; T − Π = ∂R + S; (Σ_{p∈s}|β_p|)·ρⁿ ≤ c·M(T), M(R) ≤ cρ·M(T) and M(S) ≤ cρ·M(∂T) (in [0, ∞]); F_p ⊆ cthickening(2√P·ρ, K) for every p ∈ s; and R and S vanish off cthickening(2√P·ρ, K). This is Simon's Deformation Theorem 5.3 (5.1 when ρ = 1) for IM T with IM ∂T and compact support, with M(Π) = (Σ_{p∈s}|β_p|)ρⁿ.

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4743

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5506, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6409, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6413, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6421, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6424, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6428, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6435, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6438, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6443, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6448, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6453, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

## Lean problem

Declaration: `Submission.dor_lmb_fc_deformation`

```lean
((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn U n, (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn U n, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsCompact K → IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → T ω = 0) → ∃ (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (Pc : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω = ∑ p ∈ s, (β p : ℝ) * ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)}, (ω : DifferentialForm (Euclid P) (m + 1)) x (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Pc ω = R.boundary ω + S ω) ∧ (∑ p ∈ s, ((β p).natAbs : ℝ≥0∞)) * ENNReal.ofReal (ρ ^ (m + 1)) ≤ ENNReal.ofReal c * T.mass ∧ R.mass ≤ ENNReal.ofReal (c * ρ) * T.mass ∧ S.mass ≤ ENNReal.ofReal (c * ρ) * T.boundary.mass ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)} ⊆ cthickening (2 * Real.sqrt P * ρ) K) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (cthickening (2 * Real.sqrt P * ρ) K) → R ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (cthickening (2 * Real.sqrt P * ρ) K) → S ω = 0
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, §5: Deformation Theorem 5.1 (unscaled) and 5.3 (scaled), Lemma 5.4, and the printed proofs (chapter-06.txt lines 1437–1960), specialized to the present hypotheses (T and ∂T IM, T vanishing off the compact K). Errata applied (as recorded for this theorem in the project's GMT/Ch06/Contract.lean, DeformationTheorem): the book's 'n, k ∈ {1, 2, …}' and 'C(n, k)' mean n, ℓ and C(n, ℓ); '𝓛_j(ρ)' in 5.3 means 𝓛_n(ρ); 'so is s' means 'so is S'; and the scaled bounds are M(R) ≤ CρM(T), M(S) ≤ CρM(∂T). Results of the book used by the printed proof: the 5-times covering lemma (Ch. 1, 3.4); push-forwards f_# by maps that are Lipschitz near the support, of currents with locally finite M and M∂ (Ch. 6, 2.23, 2.29), which map IM currents to IM currents (Ch. 6, 3.6–3.9); products [[(0,1)]] × X (2.18–2.22), the homotopy formula 2.25 and the mass bound 2.27 for affine homotopies h(x, t) = x + t(g(x) − x); slices 4.4–4.6 and the slice estimate 4.10 (here supplied by (SL) together with (C1)); the completeness Lemma 3.13 (here the sibling im_series); the constancy theorem 2.34 with Remarks 2.35 and 2.37(1); the BV Poincaré inequalities of Ch. 2, 2.7 and Remark 2.9; lower semicontinuity of mass under weak convergence (2.14; SimonGMT WeaklyConvergesOn.massOn_le_liminf). Siblings: (C1) the reused accepted sibling dor_imrep_massOn_eq_measure_and_support: for open U, X ∈ 𝒟_d(U) and an IMRep R in U representing X, M_W(X) = μ_R(W) for every open W ⊆ ℝ^P, and spt X = U ∩ spt μ_R. (IMC) the reused accepted sibling cmc_imRep_locality_restrict_sub: (a) if U is open, M ⊆ M' ⊆ U are Borel and Hᵈ(M' ∩ K) < ∞ for every compact K ⊆ U, then for Hᵈ-a.e. x ∈ M and every linear subspace Q, M has approximate tangent space Q at x iff M' has (HasApproximateTangentSpaceAt d · x Q); (b) if U is open, R = (M, θ, ξ) is an IMRep in U and E is Borel, there are A ∈ 𝒟_d(U) and an IMRep R' in U with carrier M ∩ E, multiplicity θ and orientation ξ that represents A (so μ_{R'} = μ_R⌞E); (c) if U is open and A, B ∈ 𝒟_d(U) are IM, then A − B is IM; (d) for every IMRep R = (M, θ, ξ) in any U and Hᵈ-a.e. x ∈ M, |ξ(x)(α)| ≤ |α| for every d-covector α. im_series (sibling dor_lmb_fc_im_series): if U ⊆ ℝ^P is open, k ≥ 1 and X_r ∈ 𝒟_k(U) (r ∈ ℕ) are IM with Σ_r M(X_r) < ∞, then there is an IM Y ∈ 𝒟_k(U) with Σ_r X_r(ω) = Y(ω) (a convergent series) for every ω ∈ 𝒟^k(U) and M(Y) ≤ Σ_r M(X_r). The zero current of any degree d in any U is IM: the IMRep with carrier ∅, multiplicity 0 and orientation 0 represents it (∅ is Borel and countably d-rectifiable by Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero, and every integral or a.e. condition over ∅ holds trivially).
Notation. ℓ := P − n ≥ 1, so ℝ^P = ℝ^{n+ℓ}; C := [0, 1]^P; L_j is the j-skeleton of the decomposition ⋃_{z∈ℤ^P}(z + C) and 𝓛_j its set of closed j-faces; 𝓛_n(ρ) := {ρF : F ∈ 𝓛_n}. Each F ∈ 𝓛_n(ρ) equals F_p for exactly one p = (z, ι) with ι strictly increasing (ι lists the coordinate directions of F, ρz is its lowest vertex); [[F_p]](ω) := ∫_{F_p} ω(x)(e_{ι(0)}, …, e_{ι(m)}) dHⁿ(x). S_1, …, S_N (N = binom(n+ℓ, n+1)) are the (n+1)-dimensional coordinate subspaces, p_j the orthogonal projection onto S_j, F_j := C ∩ S_j (an (n+1)-face), x_j its center, q := (1/2, …, 1/2) the center of C, ω_k := L^k(B_1(0)). For a ∈ B_{1/4}(q): L_{ℓ−1}(a) := a + L_{ℓ−1} and L_{ℓ−1}(a; σ) := {x : dist(x, L_{ℓ−1}(a)) < σ}; dist(L_{ℓ−1}(a), L_n) ≥ 1/4; and since L_{ℓ−1} is the union of the affine (ℓ−1)-planes z + S_j^⊥ (z ∈ ℤ^P), L_{ℓ−1}(a) = ⋃_{j=1}^N ⋃_{z∈ℤ^P∩S_j} p_j⁻¹(p_j(a) + z) and L_{ℓ−1}(a; σ) = ⋃_j ⋃_{z∈ℤ^P∩S_j} p_j⁻¹(B_σ(p_j(a) + z)) (balls in S_j). For Borel A and IM X, X⌞A is the restriction (the current of the restricted IMRep, (IMC)(b)). Constants c depend only on n and ℓ and may change from line to line. If M(T) = 0 then T = 0 (by (C1) every IMRep of T has μ = 0, so its carrier is Hⁿ-null) and s := ∅, Π := 0, R := 0, S := 0 (IM by the remark on zero currents) satisfy all assertions; so assume M(T) > 0. M(T) and M(∂T) are finite: by (C1) they equal the total IMRep measures, which are finite because the carriers lie a.e. in the compact K.
1. The retraction (Lemma 5.4). Erratum: the printed proof of the derivative bound (3) is wrong, see (1g). Parts (1a)–(1f) below keep the printed construction of ψ and replace that proof. Fix a ∈ B_{1/4}(q); then a_i ∈ (1/4, 3/4) for every i, because |a_i − 1/2| ≤ |a − q| < 1/4.
 (1a) Skeleta. A point lies in L_j iff at least P − j of its coordinates are integers: a j-face z + F has P − j fixed integer coordinates; conversely, fix P − j integer coordinates of the point and choose unit intervals containing the others. Hence L_{ℓ−1}(a) = {x : x_i − a_i ∈ ℤ for at least n + 1 indices i}. This is a closed ℤ^P-periodic set, the complete periodic lattice. Since |x_i − a_i| < 1 for x ∈ C, its local arrangement in C is Λ(a) := C ∩ L_{ℓ−1}(a) = {x ∈ C : x_i = a_i for at least n + 1 indices i}. Also dist(L_{ℓ−1}(a), L_n) ≥ 1/4. Indeed, let w ∈ L_n and w' ∈ L_{ℓ−1}(a). At least ℓ coordinates of w are integers and at least n + 1 coordinates of w' − a are integers. As ℓ + n + 1 > P, some index i has w_i ∈ ℤ and w'_i ∈ a_i + ℤ, so |w − w'| ≥ dist(a_i, ℤ) > 1/4.
 (1b) Coordinate ratios. For x ∈ C and 1 ≤ i ≤ P let δ_i(x) := |x_i − a_i|. Let h_i(x) := 1 − a_i if x_i ≥ a_i and h_i(x) := a_i if x_i < a_i; this is the distance from a_i to the end of [0, 1] on the side of x_i. Let r_i(x) := δ_i(x)/h_i(x).
 - Since h_i(x) ∈ (1/4, 3/4), δ_i ≤ r_i ≤ 4δ_i.
 - r_i(x) ∈ [0, 1]; r_i(x) = 1 iff x_i ∈ {0, 1}, and r_i(x) = 0 iff x_i = a_i.
 - r_i depends only on x_i and is continuous and piecewise linear in x_i, with slopes 1/(1 − a_i) and −1/a_i, both of modulus < 4. So |r_i(x) − r_i(z)| ≤ 4|x − z|.
 For 1 ≤ k ≤ P let r_{(k)}(x) be the k-th largest of r_1(x), …, r_P(x), counted with multiplicity, and put r_{(0)}(x) := 1. Since r_{(k)} = max over k-element index sets I of min_{i∈I} r_i, we have |r_{(k)}(x) − r_{(k)}(z)| ≤ max_i |r_i(x) − r_i(z)|. So every r_{(k)} is 4-Lipschitz on C. Put κ(x) := r_{(ℓ)}(x) (κ is unrelated to the grid size ρ of the statement). Then κ(x) = 0 iff at most ℓ − 1 of the r_i(x) are positive, iff x_i = a_i for at least P − ℓ + 1 = n + 1 indices, iff x ∈ Λ(a).
 (1c) The printed construction and its closed form. Let F be a j-face of C (n + 1 ≤ j ≤ P) with set of free coordinates I_F (|I_F| = j), so F = {x ∈ C : x_i = e_i for i ∉ I_F} with e_i ∈ {0, 1}. The orthogonal projection of a onto F is a_F, with (a_F)_i = a_i for i ∈ I_F and (a_F)_i = e_i for i ∉ I_F; it lies in the relative interior of F. The printed radial retraction ψ_F : F ∖ {a_F} → ∂F (relative boundary) sends x to the point y = a_F + τ(x − a_F) of ∂F with τ ≥ 1, that is τ = 1/max_{i∈I_F} r_i(x). Explicitly, ψ_F(x)_i = a_i + (x_i − a_i)/max_{i'∈I_F} r_{i'}(x) for i ∈ I_F and ψ_F(x)_i = x_i for i ∉ I_F. Here max_{I_F} r > 0 iff x ≠ a_F. Also ψ_F = id on ∂F, where some free r_i equals 1. As printed, ψ^{(j)} := ψ_F on F ∖ {a_F} for every j-face F. This is consistent, because distinct j-faces meet only in their relative boundaries, where every ψ_F is the identity. Then ψ_0 := ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(P)}.
 Claim A. For x ∈ C ∖ Λ(a) the composite ψ_0(x) is defined and ψ_0(x) = Φ(x), where Φ(x)_i := a_i + (x_i − a_i)/max(r_i(x), κ(x)) for 1 ≤ i ≤ P.
 Proof of Claim A. Fix x ∈ C ∖ Λ(a); then r_{(k)}(x) ≥ κ(x) > 0 for 0 ≤ k ≤ ℓ. For 0 ≤ k ≤ ℓ let y^{(k)} be the point with y^{(k)}_i := a_i + (x_i − a_i)/max(r_i(x), r_{(k)}(x)). Thus y^{(0)} = x (as r_i ≤ 1) and y^{(ℓ)} = Φ(x). It suffices to show, for 0 ≤ k < ℓ, that y := y^{(k)} lies in the domain of ψ^{(P−k)} and that ψ^{(P−k)}(y) = y^{(k+1)}.
 Let A := {i : r_i(x) ≥ r_{(k)}(x)}; then |A| ≥ k. Each y_i − a_i is a positive multiple of x_i − a_i, so h_i(y) = h_i(x) and r_i(y) = r_i(x)/max(r_i(x), r_{(k)}(x)). This equals 1 for i ∈ A and r_i(x)/r_{(k)}(x) < 1 for i ∉ A. So y ∈ C, and y_i ∈ {0, 1} exactly for i ∈ A.
 - Case |A| > k. At least k + 1 of the r_i(x) are ≥ r_{(k)}(x), and r_{(k+1)}(x) ≤ r_{(k)}(x); so r_{(k+1)}(x) = r_{(k)}(x) and y^{(k+1)} = y. The point y lies in a (P − k)-face: fix k of its coordinates indexed by A. Every (P − k)-face G ∋ y has a free coordinate in A, so y ∈ ∂G ∖ {a_G} and ψ_G(y) = y. Hence ψ^{(P−k)}(y) = y = y^{(k+1)}.
 - Case |A| = k. Then A indexes the k largest r_i(x), and r_{(k+1)}(x) = max_{i∉A} r_i(x) > 0, as k + 1 ≤ ℓ. The point y lies in the relative interior of exactly one (P − k)-face G, the one with I_G = {1, …, P} ∖ A. Since max_{i∈I_G} r_i(y) = r_{(k+1)}(x)/r_{(k)}(x) > 0, y ≠ a_G. For i ∉ A, ψ_G(y)_i = a_i + (y_i − a_i)r_{(k)}(x)/r_{(k+1)}(x) = a_i + (x_i − a_i)/r_{(k+1)}(x). For i ∈ A, ψ_G(y)_i = y_i = a_i + (x_i − a_i)/r_i(x). Since r_i(x) ≤ r_{(k+1)}(x) for i ∉ A and r_i(x) ≥ r_{(k)}(x) ≥ r_{(k+1)}(x) for i ∈ A, ψ^{(P−k)}(y) = ψ_G(y) = y^{(k+1)}. This proves Claim A.
 (1d) Properties of ψ_0 = Φ and the periodic extension.
 (i) Φ(C ∖ Λ(a)) ⊆ C ∩ L_n. Indeed |Φ(x)_i − a_i| = δ_i(x)/max(r_i(x), κ(x)) ≤ h_i(x), with equality when r_i(x) ≥ κ(x). As Φ(x)_i − a_i has the sign of x_i − a_i, Φ(x)_i lies between a_i and the end of [0, 1] on the side of x_i. So Φ(x) ∈ C, and Φ(x)_i ∈ {0, 1} for the at least ℓ indices with r_i(x) ≥ κ(x) = r_{(ℓ)}(x).
 (ii) Φ = id on C ∩ L_n, which is contained in C ∖ Λ(a) by (1a). Such an x has at least ℓ coordinates in {0, 1}, so κ(x) = 1 and Φ(x)_i = a_i + (x_i − a_i) = x_i. Hence ψ_0(C ∖ Λ(a)) = C ∩ L_n.
 (iii) Let z ∈ ℤ^P with x, x + z ∈ C. If z_i ≠ 0, then x_i, x_i + z_i ∈ {0, 1}. So r_i(x + z) = r_i(x) for all i (both equal 1 where z_i ≠ 0), and κ(x + z) = κ(x). In the coordinates with z_i ≠ 0, max(r_i, κ) = 1 and Φ(·)_i is the identity. Hence Φ(x + z) = Φ(x) + z; this is the printed property ψ_0(z + x) = z + ψ_0(x).
 As L_{ℓ−1}(a) is ℤ^P-periodic, ψ(w) := z + Φ(w − z), for any z ∈ ℤ^P with w − z ∈ C, is a well-defined map ψ : ℝ^P ∖ L_{ℓ−1}(a) → L_n. It satisfies ψ = id on L_n, ψ(z + w) = z + ψ(w) and ψ((z + C) ∖ L_{ℓ−1}(a)) ⊆ z + C; hence |ψ(w) − w| ≤ √P.
 (1e) The Lipschitz estimate in a cube, uniform in a.
 Claim B. For x, z ∈ C ∖ Λ(a), |Φ(x) − Φ(z)| ≤ 4√P·|x − z|/κ(x).
 Proof of Claim B. Fix i and write u(w) := w_i − a_i and m(w) := max(r_i(w), κ(w)) > 0 for w ∈ {x, z}. By (1b), m is 4-Lipschitz, and |u(x) − u(z)| ≤ |x − z|. If r_i(z) > 0 then |u(z)|/m(z) ≤ |u(z)|/r_i(z) = h_i(z) < 3/4; if r_i(z) = 0 then u(z) = 0. Therefore
 |Φ(x)_i − Φ(z)_i| = |u(x)/m(x) − u(z)/m(z)| ≤ |u(x) − u(z)|/m(x) + (|u(z)|/m(z))·|m(z) − m(x)|/m(x) ≤ (1 + (3/4)·4)|x − z|/m(x) ≤ 4|x − z|/κ(x).
 Summing the squares over i gives Claim B.
 Claim C (comparison with the complete periodic lattice). For x ∈ C, dist(x, L_{ℓ−1}(a)) ≤ √(n + 1)·κ(x).
 Proof of Claim C. Let J be a set of n + 1 indices carrying the n + 1 smallest values δ_i(x). Let x* be the point with x*_i := a_i for i ∈ J and x*_i := x_i for i ∉ J. Then x* − a has n + 1 zero coordinates, so x* ∈ Λ(a) ⊆ L_{ℓ−1}(a). As J omits only ℓ − 1 indices, every i ∈ J has δ_i(x) ≤ δ_{(ℓ)}(x), the ℓ-th largest δ_i(x). Using δ_i ≤ r_i for all i, dist(x, L_{ℓ−1}(a)) ≤ |x − x*| ≤ √(n + 1)·δ_{(ℓ)}(x) ≤ √(n + 1)·r_{(ℓ)}(x).
 Put c₁ := 4√(P(n + 1)). By Claims A, B and C, for all x, z ∈ C ∖ L_{ℓ−1}(a):
 (3') |ψ_0(x) − ψ_0(z)| ≤ c₁|x − z|/dist(x, L_{ℓ−1}(a)).
 Here c₁ depends only on n and ℓ, not on a ∈ B_{1/4}(q).
 (1f) Lipschitz bounds for ψ on ℝ^P. Let D(w) := dist(w, L_{ℓ−1}(a)); D is ℤ^P-periodic and 1-Lipschitz.
 (i) Suppose D ≥ τ > 0 at every point of a segment [w, w']. Then |ψ(w) − ψ(w')| ≤ (c₁/τ)|w − w'|. Indeed, the segment meets finitely many cubes z + C, each in a closed sub-segment. Ordering all endpoints of these sub-segments splits [w, w'] into consecutive closed pieces [w_k, w_{k+1}]. Each piece lies in a single cube z + C: the cube containing the midpoint of the piece contains the whole piece, since no endpoint lies strictly inside it. By (3') applied to w_k − z and w_{k+1} − z, and periodicity of D, |ψ(w_k) − ψ(w_{k+1})| ≤ (c₁/τ)|w_k − w_{k+1}|. Summing over the pieces gives the claim.
 (ii) For σ ∈ (0, 1/4], ψ is (c₂/σ)-Lipschitz on ℝ^P ∖ L_{ℓ−1}(a; σ) = {D ≥ σ}, where c₂ := max(2c₁, 1/4 + 2√P). Let D(w), D(w') ≥ σ.
 - If |w − w'| < σ, every point of [w, w'] lies within |w − w'|/2 < σ/2 of w or of w', so D > σ/2 there. Then (i) gives |ψ(w) − ψ(w')| ≤ (2c₁/σ)|w − w'|.
 - If |w − w'| ≥ σ, then |ψ(w) − ψ(w')| ≤ |w − w'| + |ψ(w) − w| + |ψ(w') − w'| ≤ |w − w'| + 2√P ≤ ((1/4 + 2√P)/σ)|w − w'|, because 1 ≤ 1/(4σ).
 (iii) Consequences.
 - ψ is locally Lipschitz on ℝ^P ∖ L_{ℓ−1}(a): on B_{D(w)/2}(w) it is (c₂/σ)-Lipschitz with σ := min(D(w)/2, 1/4).
 - |Dψ(w)| ≤ c₂/σ at every point w of differentiability with D(w) > σ. By Rademacher's theorem (LipschitzOnWith.ae_differentiableWithinAt_of_mem), this holds for L^P-a.e. such w.
 - The affine homotopy h(w, t) := w + t(ψ(w) − w) satisfies |h(w, t) − h(w', t')| ≤ (2 + c₂/σ)|w − w'| + √P|t − t'| on {D ≥ σ} × [0, 1].
 All these constants depend only on n and ℓ, uniformly over a ∈ B_{1/4}(q). This proves Lemma 5.4, with (3) in the stronger Lipschitz form (ii).
 (1g) Erratum: why the printed proof of (3) is replaced. The printed induction on ℓ passes from x ∈ int C to y := ψ_C(x) in a (P − 1)-face F of C. It then asserts dist(y, L)/dist(x, p_F⁻¹(L)) = |y − a|/|x − a| 'by similarity', where L = L_{ℓ−2}(a_F) is the complete periodic lattice of the hyperplane of F. The homothety with centre a_F and ratio t := |y − a|/|x − a| carries p_F(x) to y and fixes a_F, but it does not fix the other lattice points a_F + z. So the identity is false. Example: P = 3, n = 1, a = (3/10, 1/2, 1/2) and x = (129/200, 1/2, 1/4). Then y = (99/100, 1/2, 0) and t = 2, while dist(y, L) = 31/100 and dist(x, p_F⁻¹(L)) = 69/200 (ratio 62/69).
 The similarity survives, as an inequality, only for the local arrangement through a_F, Λ_F := {w ∈ F : w_i = a_i for at least n + 1 free coordinates i of F}. If F = {w_k = e}, then y_i − a_i = t(x_i − a_i) for i ≠ k. The nearest points of Λ_F are obtained by resetting n + 1 free coordinates to a_i, so dist(y, Λ_F) = t·(sum of the n + 1 smallest δ_i(x)² over i ≠ k)^{1/2}. The same computation in C gives dist(x, Λ(a)) = (sum of the n + 1 smallest δ_i(x)²)^{1/2}. Hence dist(y, Λ_F) ≥ t·dist(x, Λ(a)) ≥ t·dist(x, L_{ℓ−1}(a)). In the example this reads 69/100 ≥ 1/2.
 The proof above avoids the induction altogether. Claim A computes the composite exactly. The only comparison it needs between the local arrangement Λ(a) and the complete lattice L_{ℓ−1}(a) is Claim C, which uses the explicit point x* ∈ Λ(a) ⊆ L_{ℓ−1}(a).
2. Choice of the centre a ((1)–(7) of the printed proof). Let β > 0 be fixed below. For j = 1, …, N let G_j be the set of g ∈ F_j ∩ B_{1/4}(x_j) with M(T⌞⋃_{z∈ℤ^P∩S_j} p_j⁻¹(B_σ(g + z))) ≤ βσ^{n+1}M(T) for all σ ∈ (0, 1/4), and B_j := (F_j ∩ B_{1/4}(x_j)) ∖ G_j. For b ∈ B_j choose σ_b ∈ (0, 1/4) with M(T⌞⋃_z p_j⁻¹(B_{σ_b}(b + z))) > βσ_b^{n+1}M(T). By the 5-times covering lemma there are pairwise disjoint balls B_{σ_i}(b_i) (σ_i = σ_{b_i}) with B_j ⊆ ⋃_i B_{5σ_i}(b_i). The sets p_j⁻¹(B_{σ_i}(b_i + z)) (i ∈ ℕ, z ∈ ℤ^P ∩ S_j) are pairwise disjoint (radii < 1/4, centres in B_{1/4}(x_j)), so summing gives βΣ_iσ_i^{n+1}M(T) ≤ M(T), Σ_iσ_i^{n+1} ≤ β⁻¹, and L^{n+1}(B_j) ≤ Σ_iω_{n+1}(5σ_i)^{n+1} ≤ 5^{n+1}ω_{n+1}β⁻¹. Hence L^P(p_j⁻¹(B_j) ∩ B_{1/4}(q)) ≤ ω_{ℓ−1}(1/4)^{ℓ−1}5^{n+1}ω_{n+1}β⁻¹. The same argument with ∂T in place of T (same subspaces S_j and the same power σ^{n+1}) gives good sets G'_j (all points are good if M(∂T) = 0). Choose β = β(n, ℓ) with 2N·ω_{ℓ−1}(1/4)^{ℓ−1}5^{n+1}ω_{n+1}β⁻¹ < ω_P(1/4)^P = L^P(B_{1/4}(q)); then some a ∈ B_{1/4}(q) has p_j(a) ∈ G_j ∩ G'_j for all j, and by the description of L_{ℓ−1}(a; σ): (6) M(T⌞L_{ℓ−1}(a; σ)) ≤ Nβσ^{n+1}M(T) and (7) M(∂T⌞L_{ℓ−1}(a; σ)) ≤ Nβσ^{n+1}M(∂T) for σ ∈ (0, 1/4). Fix a and the retraction ψ of step 1.
3. Truncations and slices ((8)–(10)). For σ ∈ (0, 1/4] put T_σ := T⌞L_{ℓ−1}(a; σ) and (∂T)_σ := ∂T⌞L_{ℓ−1}(a; σ) (IM by (IMC)(b)); by (6), (7), (9) M(T_σ) ≤ cσ^{n+1}M(T) and M((∂T)_σ) ≤ cσ^{n+1}M(∂T). Let d(x) := dist(x, L_{ℓ−1}(a)) (1-Lipschitz). Apply (SL) (with (C1)) to T, IMReps of T and ∂T, f := d and L := 1; write ⟨T, d, t⟩ := P_t. For a.e. t, ⟨T, d, t⟩ is IM, vanishes off d⁻¹(t), and ⟨T, d, t⟩ = ∂(T⌞{d < t}) − (∂T)⌞{d < t} (the formula of (SL)(2) is the action of the right side). With V := {σ/2 < d < σ} and (C1) (M⟨T, d, t⟩ = M_V⟨T, d, t⟩ for t ∈ (σ/2, σ) since the slice vanishes off d⁻¹(t)), (SL)(1) gives ∫_{σ/2}^{σ} M⟨T, d, t⟩ dt ≤ M_V(T) ≤ M(T_σ − T_{σ/2}). Hence (10): for each σ ∈ (0, 1/4] there is σ̃ ∈ (σ/2, σ), outside any prescribed null set, with ⟨T, d, σ̃⟩ IM, the slice identity, and M⟨T, d, σ̃⟩ ≤ (2/σ)M(T_σ − T_{σ/2}) ≤ cσⁿM(T).
4. Push-forward estimates ((11)–(18)). By step 1(f), for τ ∈ (0, 1/4] ψ is (c₂/τ)-Lipschitz on ℝ^P ∖ L_{ℓ−1}(a; τ), and the affine homotopy h(x, t) := x + t(ψ(x) − x) is Lipschitz with constant ≤ c/τ on (ℝ^P ∖ L_{ℓ−1}(a; τ)) × [0, 1]. ψ_# and h_#([[(0,1)]] × ·) are applied only to currents with locally finite M and M∂ supported in such sets (2.29); a current supported in {d ≥ τ} lies in the open set {d > τ/2}, on which these maps are Lipschitz with constant ≤ 2c/τ. These push-forwards map IM currents to IM currents. Since ψ(z + C) ⊆ z + C, |ψ(x) − x| ≤ √P. Using step 1, (6), (7), (10) and 2.27: (11) M(ψ_#(T_σ − T_{σ/2})) ≤ (c/σ)ⁿM(T_σ) ≤ cσM(T); (12) M(ψ_#((∂T)_σ − (∂T)_{σ/2})) ≤ (c/σ)^{n−1}M((∂T)_σ) ≤ cσM(∂T); (13) M(h_#([[(0,1)]] × (T_σ − T_{σ/2}))) ≤ cσM(T); (14) M(h_#([[(0,1)]] × ((∂T)_σ − (∂T)_{σ/2}))) ≤ cσM(∂T); (15) M(ψ_#⟨T, d, σ̃⟩) ≤ cσM(T); (16) M(h_#([[(0,1)]] × ⟨T, d, σ̃⟩)) ≤ cσM(T). Summing (11)–(14) over the dyadic scales below 1/4, and using that ψ is 4c₂-Lipschitz on ℝ^P ∖ L_{ℓ−1}(a; 1/4) (step 1(f)): (17)–(18) M(ψ_#(T − T_σ)) ≤ cM(T), M(ψ_#(∂T − (∂T)_σ)) ≤ cM(∂T), M(h_#([[(0,1)]] × (T − T_σ))) ≤ cM(T) and M(h_#([[(0,1)]] × (∂T − (∂T)_σ))) ≤ cM(∂T) for every σ ∈ (0, 1/4], with c independent of σ.
5. The limits Q, R₁, S₁ ((19)–(21)). Let σ_k := 2^{−k−2} and σ̃_k ∈ (σ_k/2, σ_k) as in (10) with (15), (16). Put X_k := T − T_{σ̃_k} (IM); by the slice identity ∂X_k = (∂T − (∂T)_{σ̃_k}) − ⟨T, d, σ̃_k⟩ (IM). X_{k+1} − X_k = T⌞{σ̃_{k+1} ≤ d < σ̃_k} is carried by {σ_k/4 < d < σ_k}, so by (11)–(16) the sequences ψ_#X_k, Ř_k := −h_#([[(0,1)]] × X_k) and Š_k := −h_#([[(0,1)]] × ∂X_k) have consecutive differences of mass ≤ c2^{−k}(M(T) + M(∂T)), and M⟨T, d, σ̃_k⟩ + M(ψ_#⟨T, d, σ̃_k⟩) + M(T_{σ̃_k}) → 0. All these currents and their differences are IM ((IMC)(c); ∂T is IM by hypothesis). Applying im_series to the first term followed by the series of consecutive differences (and to its tails for the convergence in mass) yields IM Q, S₁ ∈ 𝒟_n(ℝ^P) and IM R₁ ∈ 𝒟_{n+1}(ℝ^P) with (19) M(Q − ψ_#X_k) → 0, M(R₁ − Ř_k) → 0, M(S₁ − Š_k) → 0. The homotopy formula 2.25 for h (h(·, 0) = id, h(·, 1) = ψ) reads (20) ψ_#X_k − X_k = ∂h_#([[(0,1)]] × X_k) + h_#([[(0,1)]] × ∂X_k), i.e. X_k − ψ_#X_k = ∂Ř_k + Š_k. Since M(T_{σ̃_k}) → 0, X_k → T in mass; mass convergence implies weak convergence and ∂ is weakly continuous, so letting k → ∞: (21) T − Q = ∂R₁ + S₁.
6. Supports and masses of Q, R₁, S₁ ((22)–(25)). (22) ψ maps into L_n, so spt ψ_#X_k ⊆ L_n and spt Q ⊆ L_n. (23) As ψ(z + C) ⊆ z + C and h(x, t) ∈ z + C for x ∈ z + C: spt Q ∪ spt R₁ ⊆ {x : dist(x, spt T) ≤ √P} and spt S₁ ⊆ {x : dist(x, spt ∂T) ≤ √P}, because Š_k = −h_#([[(0,1)]] × (∂T − (∂T)_{σ̃_k})) + h_#([[(0,1)]] × ⟨T, d, σ̃_k⟩) and the last term tends to 0 in mass by (16). Likewise spt ∂Q ⊆ {dist(·, spt ∂T) ≤ √P}, because ∂Q = lim ψ_#∂X_k and the slice terms tend to 0 in mass by (15). (24) M(Q) ≤ cM(T), M(R₁) ≤ cM(T), M(S₁) ≤ cM(∂T) by (17)–(19), (15), (16). (25) M(∂Q) ≤ liminf_k M(∂ψ_#X_k) = liminf_k M(ψ_#∂X_k) ≤ cM(∂T) (lower semicontinuity of mass, (18), (15)).
7. Face-wise structure of Q and the integers β_F ((26)–(37)). For F ∈ 𝓛_n with relative interior F° let V_F := {x : dist(x, F°) < dist(x, L_n ∖ F°)}; the V_F are pairwise disjoint open sets with V_F ∩ L_n = F°, and Q⌞F° is the restriction of the IM current Q to the Borel set F° ((IMC)(b)). Since spt Q ⊆ L_n, ∂Q(ω) = (Q⌞F°)(dω) for every ω supported in V_F; we write M((∂Q)⌞F°) := M_{V_F}(∂Q), the boundary mass of Q⌞F° in V_F, and note Σ_F M_{V_F}(∂Q) ≤ M(∂Q) (admissible forms supported in disjoint open sets can be added). Fix F; renumbering coordinates, F ⊆ ℝⁿ × {0}; let p be the orthogonal projection onto ℝⁿ × {0}. (26) p_#(Q⌞F°) = Q⌞F°, i.e. Q⌞F° is an n-current carried by the n-plane of F and oriented by it. The printed reason is that p ∘ ψ = ψ on the open set ψ⁻¹(F°). Indeed F° is relatively open in L_n (L_n ∖ F° = ∂F ∪ ⋃_{G≠F} G is closed), so F° = O ∩ L_n for an open O. Then ψ⁻¹(F°) = ψ⁻¹(O) is open (ψ is continuous with values in L_n), and ψ maps it into F° ⊆ ℝⁿ × {0}. Since Q is IM, (26) and (27) can be read off directly. Q⌞F° is carried by F°, and by (IMC)(a) the approximate tangent space at Hⁿ-a.e. point of its carrier is ℝⁿ × {0}; so its orientation there is ±e_1∧⋯∧e_n. Hence (27) (Q⌞F°)(ω) = ∫_{F°} ω(x)(e_1, …, e_n)θ_F(x) dLⁿ(x), where θ_F is the multiplicity with that sign (0 off the carrier), an integer-valued function in L¹(F°). Its boundary mass in V_F is M_{V_F}(∂Q) ≤ M(∂Q) < ∞. By the arguments of the constancy theorem 2.34 and Remark 2.35, θ_F ∈ BV(F°) and (28) M(Q⌞F°) = ∫_{F°}|θ_F| dLⁿ, M_{V_F}(∂Q) = |Dθ_F|(F°). For β ∈ ℝ, (29)–(30) M(Q⌞F° − β[[F]]) = ∫_{F°}|θ_F − β| dLⁿ and M(∂(Q⌞F° − β[[F]])) = |D(χ_{F°}(θ_F − β))|(ℝⁿ). Choose β_F ∈ ℤ with (31) min{Lⁿ{x ∈ F° : θ_F ≥ β_F}, Lⁿ{x ∈ F° : θ_F ≤ β_F}} ≥ 1/2 (an integer median; Lⁿ(F°) = 1). The BV Poincaré inequality (Ch. 2, 2.7 and Remark 2.9, on the convex F°) gives (32) M(Q⌞F° − β_F[[F]]) ≤ cM_{V_F}(∂Q) and M(∂(Q⌞F° − β_F[[F]])) ≤ cM_{V_F}(∂Q). By Remark 2.37(1) (Q and ∂Q have finite mass and Hⁿ(L_{n−1}) = 0), (33) Q⌞L_{n−1} = 0, so Q = Σ_F Q⌞F°. Put P := Σ_{F∈𝓛_n} β_F[[F]]: a finite sum, because spt Q is compact and β_F = 0 whenever Q⌞F° = 0. Summing (32) and using Σ_F M_{V_F}(∂Q) ≤ M(∂Q): (34) M(Q − P) ≤ cM(∂Q) and M(∂Q − ∂P) ≤ cM(∂Q). By (31), (35) |β_F| ≤ 2∫_{F°}|θ_F| dLⁿ, hence (36) M(P) = Σ_F|β_F| ≤ 2M(Q) (the faces have Hⁿ(F) = 1 and pairwise Hⁿ-null intersections), and (37) M(∂P) ≤ cM(∂Q).
8. Theorem 5.1 ((38)). By (21), (38) T − P = ∂R₁ + S₁ + (Q − P). Put R := R₁ and S := S₁ + (Q − P), i.e. S₁ − (P − Q) with the contract subtraction. Then T − P = ∂R + S, and by (24), (25), (34), (36): M(P) ≤ cM(T), M(R) ≤ cM(T), M(S) ≤ cM(∂T). Supports: a face F with β_F ≠ 0 has θ_F ≢ 0, so F meets spt Q ⊆ {dist(·, spt T) ≤ √P}, and diam F = √n < √P (ℓ ≥ 1) gives F ⊆ {dist(·, spt T) < 2√P}; a face with Q⌞F° ≠ β_F[[F]] has M_{V_F}(∂Q) > 0 by (32), so V_F meets spt ∂Q ⊆ spt Q ⊆ L_n, i.e. F° meets spt ∂Q, and F lies in {dist(·, spt ∂T) < 2√P}; hence spt P ∪ spt R ⊆ {dist(·, spt T) < 2√P} and spt S ⊆ {dist(·, spt ∂T) < 2√P}. IM: each [[F]] is IM, so P is IM (integer combination, (IMC)(c)); R = R₁ and S₁ are IM, and Q − P and S are IM by (IMC)(c).
9. Theorem 5.3 (scale ρ). Let λ(x) := ρ⁻¹x (a proper linear isomorphism) and T' := λ_#T (SimonGMT affinePushforward). T' and ∂T' = λ_#∂T are IM (transport the IMReps: carrier λ(M), multiplicity θ∘λ⁻¹, the same unit orientation; Hⁿ(λ(A)) = ρ⁻ⁿHⁿ(A)), M(T') = ρ⁻ⁿM(T), M(∂T') = ρ^{−(n−1)}M(∂T), spt T' = ρ⁻¹spt T. Apply step 8 to T' and push forward by λ⁻¹ : x ↦ ρx: P := λ⁻¹_#P' = Σβ_F[[ρF]] (faces of 𝓛_n(ρ), same integer coefficients and orientations), R := λ⁻¹_#R', S := λ⁻¹_#S'. Then T − P = ∂R + S, M(P) ≤ cM(T), M(R) = ρ^{n+1}M(R') ≤ cρM(T), M(S) = ρⁿM(S') ≤ cρM(∂T), spt P ∪ spt R ⊆ {dist(·, spt T) < 2√Pρ}, spt S ⊆ {dist(·, spt ∂T) < 2√Pρ}, and P, R, S are IM.
10. The statement. Since T vanishes off K, spt T ⊆ K (each x ∉ K has a ball whose closure misses K, on which T vanishes), and spt ∂T ⊆ spt T. Let s be the finite set of p = (z, ι) (ι strictly increasing) indexing the faces ρF of 𝓛_n(ρ) with β_F ≠ 0, β_p := β_F, β := 0 off s, and Π := P. The orientation used for F in step 7 is e_{ι(0)}∧⋯∧e_{ι(m)} (increasing coordinate order), so Π(ω) = Σ_{p∈s} β_p ∫_{F_p} ω(x)(e_{ι_p(0)}, …, e_{ι_p(m)}) dHⁿ(x). R and S are IM and T − Π = ∂R + S. (Σ_{p∈s}|β_p|)ρⁿ = M(Π) ≤ cM(T): distinct faces of 𝓛_n(ρ) have pairwise Hⁿ-null intersections and Hⁿ(F_p) = ρⁿ, so (⋃_{p∈s}F_p°, |β_p| on F_p°, sign(β_p)e_{ι_p}) is an IMRep of Π and (C1) gives M(Π) = Σ|β_p|ρⁿ. M(R) ≤ cρM(T) and M(S) ≤ cρM(∂T). For p ∈ s, F_p ⊆ spt Π ⊆ {dist(·, K) < 2√Pρ} ⊆ cthickening(2√Pρ, K). Finally spt R, spt S ⊆ {dist(·, K) < 2√Pρ}, and a current vanishes on every test form whose tsupport misses its support (cover the compact tsupport by finitely many open sets on which the current vanishes and use a smooth partition of unity), so R and S vanish off cthickening(2√Pρ, K). The constant c depends only on n and ℓ, i.e. on (P, m). ∎

## Key steps

1. Lemma 5.4, with the printed proof of (3) corrected: the composite radial retraction ψ_0 has the closed form Φ(x)_i = a_i + (x_i − a_i)/max(r_i(x), r_{(ℓ)}(x)). It satisfies |Φ(x) − Φ(z)| ≤ 4√P|x − z|/r_{(ℓ)}(x), and r_{(ℓ)}(x) ≥ dist(x, L_{ℓ−1}(a))/√(n+1) via an explicit point of Λ(a) = C ∩ L_{ℓ−1}(a). So the periodic retraction ψ is (c/σ)-Lipschitz off L_{ℓ−1}(a; σ), uniformly in a.
2. Averaging with the 5-times covering lemma chooses a with M(T⌞L_{ℓ−1}(a; σ)) ≤ cσ^{n+1}M(T) and the same for ∂T.
3. Slice T by d = dist(·, L_{ℓ−1}(a)) via (SL); the homotopy formula and 2.27 bound ψ_# and h_# of the dyadic pieces and slices by cσ(M(T) + M(∂T)).
4. Completeness (im_series) gives IM Q, R₁, S₁ with T − Q = ∂R₁ + S₁, spt Q ⊆ L_n, M(Q), M(R₁) ≤ cM(T), M(S₁), M(∂Q) ≤ cM(∂T).
5. On each n-face Q is a BV multiple of the face (constancy theorem); an integer median β_F and the BV Poincaré inequality give P = Σβ_F[[F]] with M(Q − P) ≤ cM(∂Q), M(P) ≤ cM(Q).
6. R = R₁, S = S₁ + (Q − P); rescaling by ρ gives 5.3; compact support makes the chain finite, giving the cell formula, the coefficient bound and the support/vanishing statements.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n "^theorem" local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean (LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt)`
- `rg -n "theorem lipschitz_infDist_pt|theorem infDist_le_dist_of_mem" local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -l -i "retraction|skeleton|cubical|radial retract|latticeFace|deformation theorem" .lake/packages/simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06 Contract/Submission; SimonGMT hits are unrelated: "cubically small" remainders in Chapter05, a local chart retraction in Chapter08/ConstancyNormalCharts.lean, a unit-ball retraction in Chapter08/PolarNorm.lean)`
- `rg -n -i "latticeFace|DeformationTheorem|def IsLatticeChain" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean (sorry-frozen Ch06 statements, not imported by GMT.Ch07.Submission)`
- `sed -n 1400,1935p book/chapter-06.txt (Deformation Theorem 5.1-5.3, Lemma 5.4 with the printed induction for (3), proof (1)-(38))`
- `python3 -I scans of dag.json (818 nodes, updated 2026-10-13T09:07Z): statuses and byte-identical frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dor_ims_unitOrientation_dual (accepted); dor_lmb_slicing_lipschitz (decomposing; frozen type equals the (SL) antecedent of localize/total_bounded/deformation/deformation_top); no collision for the seven dor_lmb_fc_* names; child dependency graph acyclic`
- `python3 -I parse of nodes/.../decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json (only deformation step 1 rejected)`
- `python3 -I /tmp/fc-decomp-v2/scripts/check_retraction.py 1 and 7; python3 -I /tmp/fc-decomp-v2/scripts/check_global2.py 3 and 11 (numerical checks of Claims A, B, C and the global Lipschitz bound; audit counterexample ratio 62/69)`
- `python3 -I /tmp/fc-decomp-v2/gen_types.py (gmt-compare.py contract_scope replay; exact comparator challenge file per child) and lean_contract.validate_lean_statement on all ten lean_statement strings`
- `lake env lean /tmp/fc-decomp-v2/lean/Challenge_*.lean and AllProps.lean (0 errors; #check of the cited Mathlib lemmas)`
- `python3 -I /tmp/fc-decomp-v2/check_assembly_types.py; lake env lean /tmp/fc-decomp-v2/lean/Assembly.lean and Slim.lean (#print axioms: [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/PolarNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/ScalarAreaRemainder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/fc-decomp-v2/lean/AllProps.lean`
- `/tmp/fc-decomp-v2/lean/Assembly.lean`
- `/tmp/fc-decomp-v2/lean/Slim.lean`
- `/tmp/fc-decomp-v2/scripts/check_retraction.py`
- `/tmp/fc-decomp-v2/scripts/check_global2.py`

Snapshot: project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
Neither SimonGMT nor the snapshot contains a cubical-skeleton retraction, Lemma 5.4, or a proved Deformation Theorem. The skeleton/retraction keyword hits are unrelated (Chapter05 "cubically small" remainders, a local chart retraction in Chapter08/ConstancyNormalCharts.lean, a unit-ball retraction in Chapter08/PolarNorm.lean). The Ch06 contract has only sorry-frozen latticeFace/DeformationTheorem statements, not imported by GMT.Ch07.Submission. So the corrected Lemma 5.4 argument is written out in deformation step 1 and cites only Mathlib basics present in the snapshot: Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt) and lipschitz_infDist_pt.
DAG state: the reused declarations dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub and dor_ims_unitOrientation_dual are accepted with byte-identical frozen types. dor_lmb_slicing_lipschitz is still decomposing, and its frozen type equals the (SL) antecedent. The seven dor_lmb_fc_* names are fresh.
Lean: all ten child types compile as exact comparator challenges in the replayed contract scope with 0 errors. The conditional assembly of the exact parent type and the derivation of series_limit from im_series compile with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
