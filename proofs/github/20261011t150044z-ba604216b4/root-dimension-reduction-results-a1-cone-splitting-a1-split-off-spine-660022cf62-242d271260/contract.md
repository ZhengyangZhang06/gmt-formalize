<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.cone_map-a1 -->

## Theorem `Submission.dimred_cs_sos_cfs_cp_cone_map`

Let P, n ∈ ℕ, L ≥ 0 (NNReal), ρ ∈ ℝ, and let G : ℝ^n → ℝ^P (Euclid n → Euclid P) be L-Lipschitz. For z ∈ ℝ^{n+1} write z_0 := WithLp.ofLp z 0 and tail z := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) ∈ ℝ^n. Then there is a map H : ℝ^{n+1} → ℝ^P, Lipschitz with some constant K ≥ 0, such that for every z ∈ ℝ^{n+1} with z_0 ∈ (0, 1) and ‖G(tail z)‖ < ρ: (a) H(z) = z_0·G(tail z); and (b) if G is differentiable at tail z, then the tuple (b ↦ DH(z)ê_b) of directional derivatives equals Fin.cons (G(tail z)) (a ↦ z_0·DG(tail z)e_a), i.e. DH(z)ê_0 = G(tail z) and DH(z)ê_{a+1} = z_0·DG(tail z)e_a for a ∈ Fin n. Here D = fderiv ℝ, ê_b := EuclideanSpace.single b 1 ∈ ℝ^{n+1} and e_a := EuclideanSpace.single a 1 ∈ ℝ^n.

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.cone_map-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8635

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_cs_sos_cfs_cp_cone_map`

```lean
∀ (P n : ℕ) (G : Euclid n → Euclid P) (L : NNReal) (ρ : ℝ), LipschitzWith L G → ∃ H : Euclid (n + 1) → Euclid P, (∃ K : NNReal, LipschitzWith K H) ∧ ∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ < ρ → H z = WithLp.ofLp z 0 • G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ (DifferentiableAt ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) → (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1)))
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.cone_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1, 2, 3(a) and 4 of the selected parent proof (the cone parametrization H_i(s, u) = s·G_i(u)), stated for one Lipschitz map G and an arbitrary radius ρ. This parametrizes Simon's cone 0 ⨯ T = h_#([[(0,1)]] × T), h(t, x) = tx (Ch. 6, 2.30, chapter-06.txt lines 525–536).
Notation. π₀ : ℝ^{n+1} → ℝ, π₀(z) := z_0 (EuclideanSpace.proj 0), and π′ : ℝ^{n+1} → ℝ^n, π′(z) := tail z. π′ is linear (additivity and homogeneity hold definitionally), so both are continuous linear maps (LinearMap.toContinuousLinearMap on the finite-dimensional ℝ^{n+1}) and hence Lipschitz with constants ‖π₀‖ and ‖π′‖. On the standard basis: π₀ê_0 = 1, π′ê_0 = 0, π₀ê_{a+1} = 0 and π′ê_{a+1} = e_a. This follows by comparing coordinates: (ê_b)_j = [j = b], Fin.tail shifts indices by Fin.succ, Fin.succ is injective and Fin.succ a ≠ 0.

1. (Radius.) Put ρ′ := max(ρ, 1). Then ρ′ > 0 and ρ′ ≥ ρ.
2. (Retraction.) Let φ be the ContDiffBump centered at 0 ∈ ℝ^P with rIn = ρ′ and rOut = ρ′ + 1 (valid since 0 < ρ′ < ρ′ + 1), and r(y) := φ(y)·y.
 (a) r is C¹, as the product of the smooth φ and the identity, and has compact support because φ does (HasCompactSupport.smul_right). Hence r is Lipschitz with some constant K_r (ContDiff.lipschitzWith_of_hasCompactSupport).
 (b) ‖r(y)‖ ≤ ρ′ + 1 for all y. If ‖y‖ < ρ′ + 1, then ‖r(y)‖ = |φ(y)|·‖y‖ ≤ 1·(ρ′ + 1) since 0 ≤ φ ≤ 1. Otherwise dist(y, 0) ≥ rOut, so φ(y) = 0 (ContDiffBump.zero_of_le_dist) and r(y) = 0.
 (c) r(y) = y whenever ‖y‖ ≤ ρ′, because φ = 1 on closedBall(0, rIn) (ContDiffBump.one_of_mem_closedBall).
3. (Clamp.) σ(s) := max(0, min(s, 1)). σ is 1-Lipschitz (s ↦ min(s, 1) and t ↦ max(0, t) are 1-Lipschitz), 0 ≤ σ ≤ 1 so |σ(s)| ≤ 1, and σ(s) = s for s ∈ (0, 1).
4. (Definition.) H(z) := σ(z_0)·r(G(tail z)).
5. (H is Lipschitz.) Put f₁(z) := σ(π₀z) and f₂(z) := r(G(π′z)). f₁ is ‖π₀‖-Lipschitz with |f₁| ≤ 1, and f₂ is K_r·L·‖π′‖-Lipschitz with ‖f₂‖ ≤ ρ′ + 1 (steps 2 and 3). For z, z′ ∈ ℝ^{n+1}, H(z) − H(z′) = (f₁(z) − f₁(z′))·f₂(z) + f₁(z′)·(f₂(z) − f₂(z′)). Hence
 ‖H(z) − H(z′)‖ ≤ |f₁(z) − f₁(z′)|·‖f₂(z)‖ + |f₁(z′)|·‖f₂(z) − f₂(z′)‖ ≤ ((ρ′ + 1)·‖π₀‖ + K_r·L·‖π′‖)·‖z − z′‖,
 so H is Lipschitz with constant K := ((ρ′ + 1)‖π₀‖ + K_r L ‖π′‖)₊ (LipschitzWith.of_dist_le').
6. (Local form; part (a).) Fix z with z_0 ∈ (0, 1) and ‖G(tail z)‖ < ρ. Let H̃(z′) := π₀(z′)·G(π′z′) and O := {z′ : π₀z′ ∈ (0, 1), ‖G(π′z′)‖ < ρ′}. O is open, as the intersection of the preimages of the open sets (0, 1) and (−∞, ρ′) under continuous maps (G is continuous because it is Lipschitz). z ∈ O because ‖G(tail z)‖ < ρ ≤ ρ′. For z′ ∈ O, σ(z′_0) = z′_0 by step 3 and r(G(tail z′)) = G(tail z′) by step 2(c), since ‖G(tail z′)‖ < ρ′. So H = H̃ on the neighbourhood O of z, i.e. H =ᶠ[𝓝 z] H̃. In particular H(z) = z_0·G(tail z), which is (a).
7. (Derivative.) Assume G is differentiable at u := tail z. π₀ and π′ are continuous linear, so G∘π′ has derivative DG(u)∘π′ at z (chain rule). By the product rule (HasFDerivAt.smul), H̃ has at z the derivative D := z_0·(DG(u)∘π′) + π₀.smulRight(G(u)), that is D(v) = z_0·DG(u)(π′v) + (π₀v)·G(u). Since H =ᶠ[𝓝 z] H̃, DH(z) = DH̃(z) = D (Filter.EventuallyEq.fderiv_eq, HasFDerivAt.fderiv).
8. (Evaluation on the basis; part (b).) From π₀ê_0 = 1 and π′ê_0 = 0 we get D(ê_0) = z_0·DG(u)(0) + 1·G(u) = G(u). From π₀ê_{a+1} = 0 and π′ê_{a+1} = e_a we get D(ê_{a+1}) = z_0·DG(u)e_a. By Fin.cases on b ∈ Fin (n+1) (Fin.cons_zero, Fin.cons_succ), the tuple (b ↦ DH(z)ê_b) equals Fin.cons (G(u)) (a ↦ z_0·DG(u)e_a), which is (b). ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked during decomposition with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens, with the declaration named Submission.dimred_cs_sos_cfs_cp_cone_map as in accepted nodes. It uses no sibling declaration. Its axioms are propext, Classical.choice and Quot.sound only.
Lean tactic block for `theorem Submission.dimred_cs_sos_cfs_cp_cone_map`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro P n G L ρ hG
  -- step 1: a Lipschitz, bounded `r` with `r = id` on `closedBall 0 ρ'`, `ρ' := max ρ 1`
  set ρ' : ℝ := max ρ 1 with hρ'
  have hρ'pos : 0 < ρ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨r, ⟨Kr, hKr⟩, hr_bound, hr_id⟩ : ∃ r : Euclid P → Euclid P, (∃ K : NNReal, LipschitzWith K r) ∧
      (∀ y, ‖r y‖ ≤ ρ' + 1) ∧ (∀ y : Euclid P, ‖y‖ ≤ ρ' → r y = y) := by
    let φ : ContDiffBump (0 : Euclid P) := ⟨ρ', ρ' + 1, hρ'pos, by linarith⟩
    refine ⟨fun y => φ y • y, ?_, ?_, ?_⟩
    · have hr_smooth : ContDiff ℝ 1 (fun y : Euclid P => φ y • y) := φ.contDiff.smul contDiff_id
      have hr_supp : HasCompactSupport (fun y : Euclid P => φ y • y) := φ.hasCompactSupport.smul_right
      exact ContDiff.lipschitzWith_of_hasCompactSupport hr_supp hr_smooth (by simp)
    · intro y
      by_cases hy : ‖y‖ < ρ' + 1
      · calc ‖φ y • y‖ = |φ y| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * (ρ' + 1) := by
            gcongr
            · rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
          _ = ρ' + 1 := one_mul _
      · have h0 : φ y = 0 := φ.zero_of_le_dist (by simpa [dist_zero_right] using not_lt.mp hy)
        simp [h0]; linarith
    · intro y hy
      have : φ y = 1 := φ.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy)
      simp [this]
  -- the clamp `σ(s) = max(0, min(s, 1))`
  obtain ⟨σ, hσ, hσb, hσid⟩ : ∃ σ : ℝ → ℝ, LipschitzWith 1 σ ∧ (∀ s, |σ s| ≤ 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, σ s = s := by
    refine ⟨fun s => max 0 (min s 1), (LipschitzWith.id.min_const 1).const_max 0, ?_, ?_⟩
    · intro s
      rw [abs_le]; constructor
      · have : (0 : ℝ) ≤ max 0 (min s 1) := le_max_left _ _
        linarith
      · exact max_le (by norm_num) (min_le_right _ _)
    · intro s hs
      simp only [min_eq_left hs.2.le, max_eq_right hs.1.le]
  -- coordinate maps `π₀ z = z₀`, `π' z = tail z`
  let π0 : Euclid (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hπ0 : ∀ z, π0 z = WithLp.ofLp z 0 := fun z => rfl
  let πtl : Euclid (n + 1) →ₗ[ℝ] Euclid n :=
    { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  let πt : Euclid (n + 1) →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap πtl
  have hπt : ∀ z, πt z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) := fun z => rfl
  -- step 2: the map `H(z) = σ(z₀) • r(G(tail z))`
  refine ⟨fun z => σ (WithLp.ofLp z 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))), ?_, ?_⟩
  · -- step 3(a): `H` is Lipschitz
    have h1 : LipschitzWith (1 * ‖π0‖₊) (fun z : Euclid (n + 1) => σ (WithLp.ofLp z 0)) :=
      hσ.comp π0.lipschitzWith
    have h2 : LipschitzWith (Kr * (L * ‖πt‖₊))
        (fun z : Euclid (n + 1) => r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))) :=
      hKr.comp (hG.comp πt.lipschitzWith)
    refine ⟨_, LipschitzWith.of_dist_le' (K := (ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) +
      ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) fun z z' => ?_⟩
    have e1 := h1.dist_le_mul z z'
    have e2 := h2.dist_le_mul z z'
    simp only [dist_eq_norm] at e1 e2 ⊢
    set a := σ (WithLp.ofLp z 0)
    set a' := σ (WithLp.ofLp z' 0)
    set R := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))
    set R' := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))
    have ha' : ‖a'‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (hσb _)
    calc ‖a • R - a' • R'‖ = ‖(a - a') • R + a' • (R - R')‖ := by
          congr 1; rw [sub_smul, smul_sub]; abel
      _ ≤ ‖a - a'‖ * ‖R‖ + ‖a'‖ * ‖R - R'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul (a - a') R, norm_smul a' (R - R')]
      _ ≤ (((1 * ‖π0‖₊ : NNReal) : ℝ) * ‖z - z'‖) * (ρ' + 1) +
            1 * (((Kr * (L * ‖πt‖₊) : NNReal) : ℝ) * ‖z - z'‖) := by
          gcongr
          exact hr_bound _
      _ = ((ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) + ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) *
            ‖z - z'‖ := by ring
  · -- step 4: value and derivative on `{z₀ ∈ (0,1), ‖G(tail z)‖ < ρ}`
    intro z hz hzρ
    let Ht : Euclid (n + 1) → Euclid P := fun z' => π0 z' • G (πt z')
    let O : Set (Euclid (n + 1)) := {z' | π0 z' ∈ Ioo (0 : ℝ) 1 ∧ ‖G (πt z')‖ < ρ'}
    have hO : IsOpen O :=
      (isOpen_Ioo.preimage π0.continuous).inter
        (isOpen_lt (continuous_norm.comp (hG.continuous.comp πt.continuous)) continuous_const)
    have hzO : z ∈ O := ⟨hz, lt_of_lt_of_le hzρ (le_max_left _ _)⟩
    have hEq : ∀ z' ∈ O, σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z')))) =
        Ht z' := by
      rintro z' ⟨h0, hρz⟩
      rw [hπ0] at h0
      rw [hπt] at hρz
      show _ = π0 z' • G (πt z')
      rw [hπ0, hπt, hσid _ h0, hr_id _ hρz.le]
    have hev : (fun z' : Euclid (n + 1) =>
        σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))) =ᶠ[𝓝 z] Ht :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hzO) hEq
    refine ⟨hEq z hzO, fun hGd => ?_⟩
    have hD : HasFDerivAt Ht (π0 z • (fderiv ℝ G (πt z)).comp πt + π0.smulRight (G (πt z))) z :=
      π0.hasFDerivAt.smul (hGd.hasFDerivAt.comp z πt.hasFDerivAt)
    rw [hev.fderiv_eq, hD.fderiv]
    have hs0 : π0 (EuclideanSpace.single 0 1) = 1 := by simp [π0]
    have hss : ∀ a : Fin n, π0 (EuclideanSpace.single a.succ 1) = 0 := by
      intro a; simp [π0, Fin.succ_ne_zero]
    have ht0 : πt (EuclideanSpace.single 0 1) = 0 := by
      rw [hπt]; ext j; simp [Fin.tail, Fin.succ_ne_zero]
    have hts : ∀ a : Fin n, πt (EuclideanSpace.single a.succ 1) = EuclideanSpace.single a 1 := by
      intro a; rw [hπt]; ext j; simp [Fin.tail]
    funext b
    refine Fin.cases ?_ (fun a => ?_) b
    · simp [hs0, ht0]
      rfl
    · simp [hss, hts]
      rfl

## Key steps

1. ρ′ := max(ρ, 1). Let r(y) := φ(y)·y, with φ the ContDiffBump with radii ρ′ < ρ′ + 1. Then r is Lipschitz (C¹ with compact support), ‖r‖ ≤ ρ′ + 1 and r = id on closedBall(0, ρ′). The clamp σ(s) := max(0, min(s, 1)) is 1-Lipschitz, |σ| ≤ 1 and σ = id on (0, 1).
2. H(z) := σ(z_0)·r(G(tail z)) is Lipschitz, by the product estimate using the bounds on σ and r and the Lipschitz coordinate maps.
3. On the open set O = {z′ : z′_0 ∈ (0, 1), ‖G(tail z′)‖ < ρ′} ∋ z, H coincides with H̃(z′) := z′_0·G(tail z′), so H(z) = z_0·G(tail z).
4. By the product and chain rules and EventuallyEq.fderiv_eq, DH(z)v = z_0·DG(u)(tail v) + v_0·G(u). Evaluating at ê_0 and ê_{a+1} gives Fin.cons (G(u)) (a ↦ z_0·DG(u)e_a).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (both identical)`
- `python3 over dag.json: depth histogram (depth-6 nodes have no children; the selected node has depth 5); keyword search of lean_statements for Fin.tail|Fin.cons|piFinSuccAbove|Ioo 0 1|curryLeft|ofLp|toLp|volume_preserving|MeasurePreserving|EuclideanSpace.single 0`
- `python3 over dag.json: search for retract|ContDiffBump|closedBall 0 together with LipschitzWith (no reusable Lipschitz retraction); search of lean_name/id for cone (ecf_cone_parametrization and ecf_cone_current are decomposing, with different types)`
- `python3 over dag.json: statements, statuses and candidate commits of cmcdt_lpi_cyl_fubini, cmcdt_lpi_cyl_pullback_integrable, cmcdt_lp_covector_curryLeft_norm_le, cmcdt_lpi_cyl_piece_action, cmcdt_lpi_cyl_piece_mass, cmcdt_lpi_cyl_slice_covector_bound, cmcdt_lpi_cyl_suspension_map, dimred_mbl_dt_lp_imc_cylinder_measure, dor_lmb_fcdp_homotopy_maps`
- `git show 8597f3f / ed778d4 / 0ea228e :GMT/Ch07/Submission.lean | grep ^import (no added imports), and extraction of the accepted proofs between the contract's end and main_theorem`
- `rg dimred_cs_sos_cfs_ over nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-* and dag.json (dimred_cs_sos_cfs_cp_* unused)`
- `grep -n 'homotopy\|cone' book/chapter-06.txt (2.25–2.27 at lines 441–478; 2.30 at lines 525–536)`
- `grep SimonGMT Chapter06/Forms.lean, Currents.lean, Mass.lean for Covector, DifferentialForm, IsSmoothForm, IsTestForm, testFormOnSubmodule, TestFormOn, covectorEuclideanNorm`
- `rg in the Mathlib snapshot for ContDiff.lipschitzWith_of_hasCompactSupport, one_of_mem_closedBall, zero_of_le_dist, curryLeft_apply_apply, curryLeftLI, ContinuousAlternatingMap.apply, map_smul_univ, intervalIntegral_comp_comm, integral_Ioc_eq_integral_Ioo, measurable_fderiv_apply_const, norm_fderiv_le_of_lipschitz, of_dist_le', HasFDerivAt.smul, EventuallyEq.fderiv_eq, setLIntegral_mono, setIntegral_congr_fun, measurable_of_countable`
- `lake env lean /tmp/cp-decomp/Probe.lean (#check of the cited APIs; LipschitzWith.smul does not exist)`
- `lake env lean /tmp/cp-decomp/Check1.lean (six child stubs plus the parent assembly)`
- `lake env lean /tmp/cp-decomp/ConeMap.lean, /tmp/cp-decomp/PieceBounds.lean, /tmp/cp-decomp/PieceAction.lean (new children fully proved)`
- `lake env lean /tmp/cp-decomp/Full.lean (accepted reuse proofs from the three commits, the three new child proofs and the assembly; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-292ca82b13/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-36d21f0b90/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-c728da6cee/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/tmp/cp-decomp/Probe.lean`
- `/tmp/cp-decomp/Check1.lean`
- `/tmp/cp-decomp/ConeMap.lean`
- `/tmp/cp-decomp/PieceBounds.lean`
- `/tmp/cp-decomp/PieceAction.lean`
- `/tmp/cp-decomp/Full.lean`

Pins and contract. The project (b4d606d), Mathlib (25730c7c) and SimonGMT (2b36630) pins match the manifest. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

DAG. The selected node has depth 5, and depth-6 nodes have no children. The three new children are therefore leaves, and each one was proved in Lean here.

Reuse. The DAG already has accepted, compatible lemmas for the generic parts:
- cmcdt_lpi_cyl_fubini (8597f3f): the cylinder B is Borel, with Tonelli and Fubini in the coordinates ι(t, u);
- cmcdt_lpi_cyl_pullback_integrable (ed778d4): an integrable weight times a Lipschitz pull-back of a test form is integrable;
- cmcdt_lp_covector_curryLeft_norm_le (0ea228e): |ι_vβ| ≤ ‖v‖|β|.
Their frozen types were copied byte-for-byte from dag.json and match their handoffs. Their commits add no imports.

No match for the cone-specific parts. The DAG has no reusable cone map, Lipschitz retraction or cone change of variables:
- cmcdt_lpi_cyl_suspension_map, cmcdt_lpi_cyl_piece_action and cmcdt_lpi_cyl_piece_mass concern the cylinder map (t, u) ↦ (t, G u), not s·G(u);
- ecf_cone_parametrization and ecf_cone_current are still decomposing and use Jacobian weights.

Library. SimonGMT supplies TestFormOn (smooth with compact support, via testFormOnSubmodule), Covector, DifferentialForm and covectorEuclideanNorm. Every Mathlib API cited by the children exists in the snapshot and was probed with #check. LipschitzWith.smul does not exist, so cone_map proves the product estimate directly.

Lean. Check1, the three child files and Full.lean compile. The frozen parent type is proved from the six children, and the full chain uses only propext, Classical.choice and Quot.sound.

Book. The construction is Simon Ch. 6, 2.30: the cone 0 ⨯ T = h_#([[(0,1)]] × T) with h(t, x) = tx (chapter-06.txt lines 525–536), together with the integral formula from the proof of 2.27 (lines 468–476).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
