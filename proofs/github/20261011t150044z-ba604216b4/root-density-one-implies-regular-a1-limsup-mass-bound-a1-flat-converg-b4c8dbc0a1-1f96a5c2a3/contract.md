<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1 -->

## Theorem `Submission.dor_lmb_fc_deformation_top`

Assume (SL) the exact frozen statement of dor_lmb_slicing_lipschitz (a dependency of the parent node), taken as an antecedent: assuming (C1), for every open U ⊆ ℝ^P, every T ∈ 𝒟_{k+1}(U) represented by an IMRep RT = (M, θ, ξ), every IMRep RB = (M', θ', ξ') representing ∂T and every L-Lipschitz f : ℝ^P → ℝ, there are P_t ∈ 𝒟_k(U) (t ∈ ℝ) such that (1) for every open W, t ↦ M_W(P_t) is a.e.-measurable and ∫_ℝ M_W(P_t) dt ≤ L·M_W(T); (2) for L¹-a.e. t: P_t is IM, P_t(ω) = 0 for every ω whose tsupport is disjoint from f⁻¹(t), and P_t(ω) = ∫_{M∩{f<t}} θ⟨dω, ξ⟩ dH^{k+1} − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩ dH^k for every ω ∈ 𝒟^k(U). Conventions: ℝ^P = Euclid P and Hᵈ = μHE[d]. For U ⊆ ℝ^P, 𝒟^d(U) = TestFormOn U d (smooth d-forms on ℝ^P with compact support contained in U) and 𝒟_d(U) = GeometricCurrentOn U d; ∂X = X.boundary (∂X(ω) = X(dω)); X − Y is the contract subtraction (pointwise on test forms). For G ⊆ ℝ^P, M_G(X) = X.massOn G is the supremum of max(X(ω), 0) over ω ∈ 𝒟^d(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x, where |·| is the Euclidean coefficient norm of covectors (covectorEuclideanNorm); M(X) = X.mass = M_U(X). An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U d; R represents X when X(ω) = ∫_M θ⟨ω, ξ⟩ dHᵈ for every ω ∈ 𝒟^d(U), where ⟨ω, ξ⟩(x) = ξ(x)(ω(x)); μ_R = θ·Hᵈ⌞M is R.measure; X is integer multiplicity (IM, IsIntegerMultiplicity X) if some IMRep represents it. X vanishes off a set K if X(ω) = 0 for every ω whose tsupport is disjoint from K. X_j ⇀ Y (WeaklyConvergesOn) means X_j(ω) → Y(ω) for every ω. V ⊂⊂ U (CompactlyContained V U) means that closure V is compact and contained in U. Let P, m ∈ ℕ with n := m + 1 = P. There is c ≥ 0 such that for every ρ > 0, every compact K ⊆ ℝ^P and every IM T ∈ 𝒟_n(ℝ^P) (domain univ) with ∂T IM and T vanishing off K there are a finite set s of pairs p = (z_p, ι_p) ∈ ℤ^P × (Fin n → Fin P) with ι_p strictly increasing, integers β_p (a function β on such pairs), and currents Π ∈ 𝒟_n(ℝ^P), R ∈ 𝒟_{n+1}(ℝ^P), S ∈ 𝒟_n(ℝ^P) such that: Π(ω) = Σ_{p∈s} β_p ∫_{F_p} ω(x)(e_{ι_p(0)}, …, e_{ι_p(m)}) dHⁿ(x) for every ω ∈ 𝒟ⁿ(ℝ^P), where e_i = EuclideanSpace.single i 1 and F_p := {x : ρz_{p,i} ≤ x_i ≤ ρ(z_{p,i} + 1) for i ∈ range ι_p, x_i = ρz_{p,i} otherwise} (here range ι_p = Fin P, so F_p is the grid cube ρ(z_p + [0, 1]^P)); R and S are IM; T − Π = ∂R + S; (Σ_{p∈s}|β_p|)·ρⁿ ≤ c·M(T), M(R) ≤ cρ·M(T) and M(S) ≤ cρ·M(∂T) (in [0, ∞]); F_p ⊆ cthickening(2√(P+1)·ρ, K) for every p ∈ s; and R and S vanish off cthickening(2√(P+1)·ρ, K). (Simon's Deformation Theorem 5.3 assumes n < P; the parent proof reduces the case n = P to it by embedding ℝ^P into ℝ^{P+1}.)

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4743

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5455, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6247, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6254, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

## Lean problem

Declaration: `Submission.dor_lmb_fc_deformation_top`

```lean
((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn U n, (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn U n, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → ∀ (P m : ℕ), m + 1 = P → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsCompact K → IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → T ω = 0) → ∃ (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (Pc : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω = ∑ p ∈ s, (β p : ℝ) * ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)}, (ω : DifferentialForm (Euclid P) (m + 1)) x (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Pc ω = R.boundary ω + S ω) ∧ (∑ p ∈ s, ((β p).natAbs : ℝ≥0∞)) * ENNReal.ofReal (ρ ^ (m + 1)) ≤ ENNReal.ofReal c * T.mass ∧ R.mass ≤ ENNReal.ofReal (c * ρ) * T.mass ∧ S.mass ≤ ENNReal.ofReal (c * ρ) * T.boundary.mass ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → ρ * p.1 i ≤ x i ∧ x i ≤ ρ * (p.1 i + 1)) ∧ (i ∉ Set.range p.2 → x i = ρ * p.1 i)} ⊆ cthickening (2 * Real.sqrt (P + 1) * ρ) K) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (cthickening (2 * Real.sqrt (P + 1) * ρ) K) → R ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (cthickening (2 * Real.sqrt (P + 1) * ρ) K) → S ω = 0
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
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(c) of the parent-supplied proof (the case n = P of the total boundedness claim, via the Deformation Theorem 5.3 of Simon Ch. 6 in ℝ^{P+1}); no appeal to Simon 3.9 (Lipschitz push-forward) is needed. Tools: the sibling deformation (dor_lmb_fc_deformation): under (SL), for all P', m' with m' + 1 < P' there is c' ≥ 0 such that for every ρ > 0, compact K' ⊆ ℝ^{P'} and IM T' ∈ 𝒟_{m'+1}(ℝ^{P'}) with ∂T' IM vanishing off K' there are s', β', Π', R', S' with the cell formula for Π', R', S' IM, T' − Π' = ∂R' + S', (Σ|β'|)ρ^{m'+1} ≤ c'M(T'), M(R') ≤ c'ρM(T'), M(S') ≤ c'ρM(∂T'), cells ⊆ cthickening(2√P'ρ, K'), R', S' vanishing off cthickening(2√P'ρ, K'). Also (C1) the reused accepted sibling dor_imrep_massOn_eq_measure_and_support: for open U, X ∈ 𝒟_d(U) and an IMRep R in U representing X, M_W(X) = μ_R(W) for every open W ⊆ ℝ^P, and spt X = U ∩ spt μ_R. (IMC) the reused accepted sibling cmc_imRep_locality_restrict_sub: (a) if U is open, M ⊆ M' ⊆ U are Borel and Hᵈ(M' ∩ K) < ∞ for every compact K ⊆ U, then for Hᵈ-a.e. x ∈ M and every linear subspace Q, M has approximate tangent space Q at x iff M' has (HasApproximateTangentSpaceAt d · x Q); (b) if U is open, R = (M, θ, ξ) is an IMRep in U and E is Borel, there are A ∈ 𝒟_d(U) and an IMRep R' in U with carrier M ∩ E, multiplicity θ and orientation ξ that represents A (so μ_{R'} = μ_R⌞E); (c) if U is open and A, B ∈ 𝒟_d(U) are IM, then A − B is IM; (d) for every IMRep R = (M, θ, ξ) in any U and Hᵈ-a.e. x ∈ M, |ξ(x)(α)| ≤ |α| for every d-covector α. The zero current of any degree d in any U is IM: the IMRep with carrier ∅, multiplicity 0 and orientation 0 represents it (∅ is Borel and countably d-rectifiable by Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero, and every integral or a.e. condition over ∅ holds trivially). The SimonGMT push-forward GeometricCurrentOn.affinePushforward (Simon 6.2.23 for proper affine maps) with boundary_affinePushforward, and exteriorDerivative_affinePullbackForm (d commutes with linear pull-back).
Notation: ι₀ : ℝ^P → ℝ^{P+1}, (ι₀x)_i = x_i (i < P), (ι₀x)_P = 0, a linear isometric embedding (proper); p : ℝ^{P+1} → ℝ^P, (py)_i = y_i (i < P), the orthogonal projection, with ‖p‖ = 1 and p ∘ ι₀ = id. For a linear map L and a form ω, L^#ω(x) := ω(Lx)(L·, …, L·). Let c₀ be the constant of deformation for (P' , m') := (P + 1, m) (valid as m + 1 = P < P + 1) and c := c₀.
1. Push-forward by ι₀. T̃ := ι₀#T ∈ 𝒟_n(ℝ^{P+1}) (affinePushforward with L = ι₀, b = 0), T̃(ω) = T(ι₀^#ω), and ∂T̃ = ι₀#∂T (boundary_affinePushforward).
2. Properties of T̃. If (M, θ, ξ) is an IMRep of T, then (ι₀(M), θ∘p, (∧ι₀)ξ∘p) is an IMRep of T̃, where (∧ι₀)ζ(α) := ζ(ι₀^*α): ι₀(M) is Borel (ι₀ is a closed embedding) and countably n-rectifiable (Lipschitz image); Hⁿ(ι₀(A)) = Hⁿ(A) for all A (Isometry.hausdorffMeasure_image), hence ∫_{ι₀(M)} g dHⁿ = ∫_M g∘ι₀ dHⁿ; the approximate tangent space of ι₀(M) at ι₀(x) is ι₀(Q) whenever M has approximate tangent space Q at x (blow-ups commute with the isometry ι₀ and Hⁿ is invariant); and (∧ι₀)(±τ₁∧⋯∧τ_n) = ±ι₀τ₁∧⋯∧ι₀τ_n with ι₀τ orthonormal. Then T̃(ω) = ∫_M θ⟨ω(ι₀x), (∧ι₀)ξ(x)⟩ dHⁿ(x) = ∫_{ι₀(M)} θ(py)⟨ω(y), (∧ι₀)ξ(py)⟩ dHⁿ(y). So T̃ is IM, and likewise ∂T̃ is IM; by (C1), M(T̃) = μ(ι₀(M)) = M(T) and M(∂T̃) = M(∂T). If tsupport ω ∩ ι₀(K) = ∅ then tsupport(ι₀^#ω) ⊆ ι₀⁻¹(tsupport ω) is disjoint from K, so T̃(ω) = 0: T̃ vanishes off the compact ι₀(K).
3. Deformation in ℝ^{P+1}. Apply deformation (with (SL)) to T̃, ρ and K' := ι₀(K): there are s̃, β̃, Π̃, R̃, S̃ with Π̃(η) = Σ_{p∈s̃} β̃_p ∫_{F̃_p} η(y)(e_{ι_p(0)}, …, e_{ι_p(m)}) dHⁿ(y), R̃, S̃ IM, T̃ − Π̃ = ∂R̃ + S̃, (Σ|β̃_p|)ρⁿ ≤ c₀M(T), M(R̃) ≤ c₀ρM(T), M(S̃) ≤ c₀ρM(∂T), cells F̃_p ⊆ K̃ := cthickening(2√(P+1)ρ, ι₀(K)) and R̃, S̃ vanishing off K̃.
4. Cutoff. K̃ is compact; choose a smooth ζ : ℝ^{P+1} → [0, 1] with compact support and ζ = 1 on an open V ⊇ K̃. For ω ∈ 𝒟ⁿ(ℝ^P) put ω̃ := ζ·p^#ω, a smooth form with compact support, i.e. ω̃ ∈ 𝒟ⁿ(ℝ^{P+1}); ω ↦ ω̃ is linear and sequentially continuous for the test-form topologies (derivatives of p^#ω are those of ω composed with the fixed linear map p, and supports lie in the fixed compact tsupport ζ).
5. Evaluation at ω̃. (a) ι₀^#ω̃ = (ζ∘ι₀)·ω because p∘ι₀ = id; since ζ∘ι₀ = 1 on the open set ι₀⁻¹(V) ⊇ K, the form ((ζ∘ι₀) − 1)ω has tsupport disjoint from K, so T̃(ω̃) = T((ζ∘ι₀)ω) = T(ω). (b) On V, ω̃ = p^#ω, so dω̃ = p^#(dω) = 0 on V (dω is an (n+1)-form on the n-dimensional ℝ^P, hence 0); thus tsupport dω̃ ⊆ ℝ^{P+1} ∖ V is disjoint from K̃ and ∂R̃(ω̃) = R̃(dω̃) = 0. (c) As ζ = 1 on every F̃_p ⊆ K̃, Π̃(ω̃) = Σ_{p∈s̃} β̃_p ∫_{F̃_p} ω(py)(p e_{ι_p(0)}, …, p e_{ι_p(m)}) dHⁿ(y). If P ∈ range ι_p ('vertical' cell) one of the vectors is p(e_P) = 0 and the term vanishes. Otherwise range ι_p = {0, …, P − 1}, p e_{ι_p(k)} = e_k, and p maps F̃_p = {y : ρz_i ≤ y_i ≤ ρ(z_i + 1) (i < P), y_P = ρz_P} isometrically onto the cube G_{z'} := ρ(z' + [0, 1]^P) with z' := (z_0, …, z_{P−1}), so ∫_{F̃_p} ω(py)(e_0, …, e_{P−1}) dHⁿ(y) = ∫_{G_{z'}} ω(x)(e_0, …, e_{P−1}) dHⁿ(x). Hence Π̃(ω̃) = Σ_{z'∈s'} β'_{z'} ∫_{G_{z'}} ω(x)(e_0, …, e_{P−1}) dHⁿ(x), where s' is the finite set of z' arising from non-vertical p ∈ s̃ and β'_{z'} := Σ{β̃_p : p ∈ s̃ non-vertical with (z_p)' = z'} ∈ ℤ. (d) Define S(ω) := S̃(ω̃); by step 4, S ∈ 𝒟_n(ℝ^P).
6. The currents. By 5(a)–(d) and step 3, T(ω) − Σ_{z'∈s'} β'_{z'} ∫_{G_{z'}} ω(e_0, …, e_{P−1}) dHⁿ = S(ω) for every ω ∈ 𝒟ⁿ(ℝ^P). Put Π := T − S (contract subtraction), so Π(ω) is the cube sum above, and R := 0 ∈ 𝒟_{n+1}(ℝ^P) (IM by the remark above; in fact every (n+1)-current on ℝ^n vanishes). Then T − Π = S = ∂R + S. Take s := {(z', ι) : z' ∈ s'} with ι : Fin n → Fin P the order isomorphism (n = P), β(z', ι) := β'_{z'} and β := 0 elsewhere; F_{(z',ι)} = G_{z'} and the cell formula of the statement holds.
7. IM. Each cube current [[G]](ω) := ∫_G ω(e_0, …, e_{P−1}) dHⁿ is IM: (G, 1, e_0∧⋯∧e_{P−1}) is an IMRep in ℝ^P — G is Borel and countably P-rectifiable, Hᴾ(G) = ρᴾ, and for Hᴾ-a.e. x ∈ G the approximate tangent space of G at x is ℝ^P by (IMC)(a) applied to G ⊆ ℝ^P (ℝ^P has approximate tangent space ℝ^P at every point, Poincare.SimonGMT.Chapter03.hasApproximateTangentSpaceAt_submodule with the submodule ⊤), with the unit orientation e_0∧⋯∧e_{P−1} of the orthonormal standard basis. A finite integer combination of IM currents is IM ((IMC)(c) repeatedly, with X + Y = X − (0 − Y) and 0 IM). So Π is IM, and S = T − Π is IM by (IMC)(c).
8. Estimates. (Σ_{p∈s}|β_p|)ρⁿ ≤ (Σ_{p∈s̃}|β̃_p|)ρⁿ ≤ c₀M(T̃) = cM(T). M(R) = 0. If ω is admissible for M(S) (|ω(x)| ≤ 1 for all x), then |ω̃(y)| = ζ(y)|p^*(ω(py))| ≤ |ω(py)| ≤ 1, because p^* maps the orthonormal basis {dx_I} of Λⁿ(ℝ^P) onto part of the orthonormal basis {dy_J} of Λⁿ(ℝ^{P+1}), hence preserves the Euclidean coefficient norm; so S(ω) = S̃(ω̃) ≤ M(S̃) and M(S) ≤ M(S̃) ≤ c₀ρM(∂T̃) = cρM(∂T).
9. Supports. G_{z'} = p(F̃_p) ⊆ p(K̃) ⊆ cthickening(2√(P+1)ρ, K) because p is 1-Lipschitz and p(ι₀(K)) = K. R = 0 vanishes everywhere. If tsupport ω ∩ cthickening(2√(P+1)ρ, K) = ∅ then tsupport ω̃ ⊆ p⁻¹(tsupport ω) is disjoint from K̃ (y ∈ K̃ implies p(y) ∈ cthickening(2√(P+1)ρ, K)), so S(ω) = S̃(ω̃) = 0. ∎

## Key steps

1. Embed ℝ^P = ℝ^P × {0} by the linear isometry ι₀ and push T forward (affinePushforward): ι₀#T and its boundary are IM with the same masses and vanish off ι₀(K).
2. Apply the deformation theorem in ℝ^{P+1} (codimension 1) to ι₀#T.
3. Test the resulting identity on ζ·p^#ω (p the projection, ζ = 1 near the thickened set): the T-term gives T(ω), the ∂R̃-term vanishes since d(p^#ω) = p^#(dω) = 0, vertical cells drop out, horizontal cells project isometrically to grid cubes.
4. Π = T − S is an integer cube chain (IM), R = 0, S(ω) = S̃(ζp^#ω) is IM with M(S) ≤ M(S̃) ≤ cρM(∂T); coefficients, cells and supports satisfy the bounds.

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
