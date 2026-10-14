<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1 -->

## Theorem `Submission.idtp_fons_cs_sos_product_decomposition`

Data:
- P, n ∈ ℕ; L ⊆ ℝ^P a linear subspace with 1 ≤ d := dim L < n; m := n − d.
- f = (f_1, …, f_d) an orthonormal family in L (hence an orthonormal basis of L).
- S ∈ 𝒟_n(ℝ^P) and an integer multiplicity representation R = (M, θ, ξ) of S (IMRep univ n, R.Represents S); μ := R.measure.
Hypotheses:
- S is invariant under translations by L: currentEval (blowUp S (−v) 1) ω = S ω, i.e. S(ω(v + ·)) = S(ω), for v ∈ L and ω ∈ 𝒟^n(ℝ^P).
- For μ-a.e. x, the projection p_x onto approxTangentPlane n M x fixes every v ∈ L.
Conclusion: there are S₀ ∈ 𝒟_m(ℝ^P) and an integer multiplicity representation R₀ of S₀ (IMRep univ m) such that:
- spt S₀ ⊆ L^⊥;
- μ₀ := R₀.measure satisfies μ₀(ℝ^P ∖ L^⊥) = 0;
- μ(A) = ∫_L μ₀(A − t) dH^d(t) for every Borel A, written ∫⁻ t in L, μ₀((fun y => t + y)⁻¹' A) ∂μHE[d];
- product formula: let ♭ : Λ^n → Λ^m be any map with (♭α)(v) = α(f_1, …, f_d, v_1, …, v_m) (Lean: α (Fin.append f v ∘ Fin.cast _)). Then for every test n-form ω,
 S(ω) = ∫_L currentEval S₀ (y ↦ ♭(ω(t + y))) dH^d(t).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6973

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7855, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1310, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1355, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016

Decomposition children: None

## Lean problem

Declaration: `Submission.idtp_fons_cs_sos_product_decomposition`

```lean
∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (f : Fin (Module.finrank ℝ L) → Euclid P) (hd : Module.finrank ℝ L < n), 0 < Module.finrank ℝ L → Orthonormal ℝ f → (∀ i, f i ∈ L) → (∀ v ∈ L, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω) → R.Represents S → (∀ᵐ x ∂R.measure, ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v) → ∃ (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)), R₀.Represents S₀ ∧ S₀.support ⊆ (Lᗮ : Set (Euclid P)) ∧ R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 ∧ (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) ∧ ∀ flat : Covector (Euclid P) n → Covector (Euclid P) (n - Module.finrank ℝ L), (∀ (α : Covector (Euclid P) n) (v : Fin (n - Module.finrank ℝ L) → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[Module.finrank ℝ L]
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
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration and depth note (context, not part of the numbered proof). Fresh name idtp_fons_cs_sos_product_decomposition. Its frozen type is byte-identical to that of dimred_cs_sos_product_decomposition (DAG node root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1, status decomposing), which is owned by the other parent root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1 (the node whose frozen type equals the selected node's) and is not comparator-accepted, so the runtime forbids reusing that name here. The numbered proof below is that node's independently audited parent-supplied proof, changed only as stated here. This node sits at depth 6, the configured maximum, so it is a machine leaf: its Lean proof adds only Submission.idtp_fons_cs_sos_product_decomposition, proves every auxiliary claim below inline (have/obtain/let/show), and adds no helper declaration and no import. The declarations of its listed dependencies are available because the controller merges their accepted candidates into this leaf's worktree before its implementation base is recorded. Changes: the measure-uniqueness lemma imrep_measure_eq_of_represents_same_current is replaced by part (c) of the accepted dimred_im_mass_measure (sibling im_mass_measure), which states the same fact. The child spine_coarea is Submission.idtp_fons_cs_sos_spine_coarea, with the same frozen type as before.

Notation. p := L.starProjection and q := I − p = Lᗮ.starProjection. H^k := μHE[k]; on k-dimensional subspaces it is Lebesgue measure. M_t := M ∩ p⁻¹(t) for t ∈ L. "IMRep" means an IMRep univ of the stated dimension. Let ♭ be a map as in the statement.
Accepted declarations used (DAG reuse siblings):
- dtc_imrep_current (sibling imrep_current): every IMRep defines a current that it represents.
- imrep_weighted_orient_indicator_ae_eq (sibling orient_data_unique): two representations of one current in an open set have H^n-a.e. equal data 1_M θ ξ on the union of their carriers.
- dimred_im_mass_measure (sibling im_mass_measure), part (c): two representations of one current have the same measure. Precisely, if R represents T in an open U, then every representation R' of T in U has R'.measure = R.measure.
Child used: spine_coarea.
1. (♭ is the interior product.) The defining identity determines ♭α. Hence ♭(α + β) = ♭α + ♭β and ♭(cα) = c♭α; evaluate at each v. Also ‖♭α‖ ≤ ‖α‖, since f is orthonormal. So ♭ is continuous linear. For every test n-form ω and t ∈ ℝ^P, the form y ↦ ♭(ω(t + y)) is C^∞ with tsupport ⊆ tsupport ω − t, compact; it is a test m-form, so currentEval S₀ of it equals S₀ applied to it.
2. (Lift.) There is a continuous linear lift : Λ^m → Λ^n with (lift β)(f_1, …, f_d, w_1, …, w_m) = β(w_1, …, w_m) for all w_j ∈ L^⊥. Equivalently, (♭(lift β))(w) = β(w) for w ∈ (L^⊥)^m.
 Construction: (lift β)(v_1, …, v_n) := (1/m!) Σ_{σ∈S_n} sgn(σ) ∏_{a=1}^d ⟨f_a, v_{σ(a)}⟩ · β(q v_{σ(d+1)}, …, q v_{σ(n)}), the alternatization (Mathlib MultilinearMap.alternatization) of a multilinear map.
 Evaluation at (f, w) with w_j ∈ L^⊥: a term is nonzero only if v_{σ(a)} = f_a for every a ≤ d, because ⟨f_a, w_j⟩ = 0 and ⟨f_a, f_b⟩ = δ_ab. So σ fixes 1, …, d. The remaining sum is Σ_{π∈S_m} sgn(π) β(w_π) = m! β(w).
3. (Orientation decomposition.)
 - Borel version of ξ. Let ξ̃ be Borel with ξ̃ = ξ H^n⌞M-a.e. (AEStronglyMeasurable.mk). R̃ := (M, θ, ξ̃) is an IMRep representing S with R̃.measure = μ; the integrands of the action agree a.e.
 - The good set G. Let G be the set of x ∈ M such that:
  - ξ̃(x) = ξ(x);
  - for some Q_x, HasApproximateTangentSpaceAt n M x Q_x holds and ξ(x) is a unit orientation of Q_x (R.orients);
  - L ⊆ Q_x.
  The last condition follows from the hypothesis: approxTangentPlane n M x = Q_x by uniqueness, and starProjection_eq_self_iff. Since μ = θH^n⌞M with θ ≥ 1 on M, μ-a.e. is the same as H^n⌞M-a.e. Hence H^n(M ∖ G) = 0, and G contains a Borel set G' ⊆ M with H^n(M ∖ G') = 0.
 - The m-vector field ζ. Define ζ(x)(β) := ξ̃(x)(lift β); ζ : ℝ^P → MultiVector P m is Borel.
 - Structure at x ∈ G. Q_x = L ⊕ (Q_x ∩ L^⊥) with dim(Q_x ∩ L^⊥) = m. Take an orthonormal basis g of Q_x ∩ L^⊥; then (f, g) is an orthonormal basis of Q_x. If ξ(x)(α) = ±α(τ) for an orthonormal basis τ of Q_x, then τ = O(f, g) with O orthogonal and α(τ) = det(O)α(f, g). So ξ(x)(α) = εα(f, g) for all α, with ε = ±1.
 - Consequences, for x ∈ G:
  (a) ζ(x)(β) = ε(lift β)(f, g) = εβ(g), so ζ(x) is a unit orientation of Q_x ∩ L^⊥ and ‖ζ(x)‖ ≤ 1;
  (b) ξ(x)(α) = εα(f, g) = ε(♭α)(g) = ζ(x)(♭α) for every α.
4. (Coarea.) The child spine_coarea applies to M: M is Borel, countably n-rectifiable, H^n(M ∩ K) ≤ μ(K) < ∞, and tangent planes contain L on G. Write ν_t := H^m⌞M_t. We obtain:
 (C1) for Borel g ≥ 0: ∫_M g dH^n = ∫_L ∫ g dν_t dt, with t ↦ ∫ g dν_t a.e.-measurable;
 (C2) if Z ⊆ M is contained in a Borel H^n-null set Z', then ν_t(Z) ≤ ν_t(Z') = 0 for a.e. t (C1 with g = 1_{Z'});
 (C3) for a.e. t: M_t is countably m-rectifiable, and for ν_t-a.e. x, HasApproximateTangentSpaceAt m M_t x (Q ∩ L^⊥) for every Q with HasApproximateTangentSpaceAt n M x Q.
5. (Slice representations.)
 - The set 𝒯. Let 𝒯 ⊆ L be the set of t such that:
  - (C3) holds at t;
  - ν_t(M ∖ G') = 0 (C2);
  - ∫_{M_t ∩ B̄_j} θ dH^m < ∞ for all j ∈ ℕ. By (C1), ∫_L ∫_{M_t∩B̄_j} θ dH^m dt = μ(B̄_j) < ∞.
  𝒯 has full H^d⌞L-measure.
 - R_t is an IMRep. For t ∈ 𝒯, R_t := (M_t, θ, ζ) is an IMRep of dimension m:
  - the carrier is Borel and countably m-rectifiable;
  - θ is measurable with θ ≥ 1 on M_t, and locally integrable (every compact set lies in some B̄_j);
  - ζ is Borel;
  - orients: for ν_t-a.e. x we have x ∈ G' ⊆ G, so ζ(x) is a unit orientation of Q_x ∩ L^⊥ (step 3a), and M_t has approximate tangent space Q_x ∩ L^⊥ at x (C3).
 - Action formula. Let ω be a test n-form. Write h(x) := θ(x)ζ(x)(♭ω(x)) for x ∈ M; |h| ≤ θ‖ω‖_∞1_{tsupport ω} on G. By step 3b and (C1) applied to h⁺ and h⁻ (finite integrals),
  S(ω) = ∫_M θξ(ω) dH^n = ∫_M h dH^n = ∫_L (∫_{M_t} θζ(♭ω) dH^m) dt = ∫_L R_t.action(♭ω) dt.
 - Measure formula. For Borel A, by (C1): μ(A) = ∫_M θ1_A dH^n = ∫_L R_t.measure(A) dt.
6. (Translation invariance of the data.) Let v ∈ L.
 - Define R^v := (M + v, θ(· − v), ξ̃(· − v)). It is an IMRep: translation preserves Borel sets, Lipschitz covers, local integrability and H^n. Moreover HasApproximateTangentSpaceAt n (M + v) (x + v) Q ⟺ HasApproximateTangentSpaceAt n M x Q, because η_{x+v,r}(M + v) = η_{x,r}(M).
 - R^v represents S. By translation invariance of H^n, R^v.action(ω) = ∫_M θξ̃(ω(· + v)) dH^n = S(ω(v + ·)). The map blowUp S (−v) 1 is the affine push-forward along y ↦ v + y, so S(ω(v + ·)) = currentEval (blowUp S (−v) 1) ω = S(ω) by hypothesis.
 - Applying the two accepted lemmas to R̃ and R^v (both represent S in the open set ℝ^P):
  (i) θ·H^n⌞M = θ(· − v)·H^n⌞(M + v). Both are withDensity measures of the σ-finite H^n⌞(M ∪ (M + v)), so 1_Mθ(z) = 1_{M+v}(z)θ(z − v) for H^n-a.e. z;
  (ii) 1_M(z)θ(z)ξ̃(z) = 1_{M+v}(z)θ(z − v)ξ̃(z − v) for H^n-a.e. z ∈ M ∪ (M + v).
 - Let Γ(z) := (1_M(z)θ(z), 1_M(z)θ(z)ξ̃(z)), a Borel map. Then Γ(z) = Γ(z − v) for H^n-a.e. z, on M ∪ (M + v) by (i)–(ii) and trivially off it.
7. (Selection of a base slice by Fubini.)
 - The sets B and B'. Let B := {(v, x) ∈ L × ℝ^P : x ∈ M, Γ(x + v) ≠ Γ(x)} and B' := {(v, x) : x ∈ M, Γ(x − v) ≠ Γ(x)}; both are Borel. For each v, B_v = {x ∈ M : Γ(x + v) ≠ Γ(x)} is the translate by −v of {z ∈ M + v : Γ(z) ≠ Γ(z − v)}, which is H^n-null by step 6; so H^n(B_v) = 0. Likewise B'_v ⊆ {z : Γ(z) ≠ Γ(z − v)} is H^n-null.
 - A measurable version of the slices.
  - Exhausting boxes. Let C_j := {x : |x_i| < j for all i}. Let 𝒫 be the countable π-system of open boxes with rational corners; it generates the Borel σ-algebra and contains every C_j.
  - Choice of N₀. By (C1), for each Z ∈ 𝒫 the map s ↦ ν_s(Z) is a.e.-measurable, and it is finite a.e. because ∫_L ν_s(Z) ds ≤ H^n(M ∩ cl Z) < ∞. Choose Borel h_Z with ν_s(Z) = h_Z(s) off a Borel null set N_Z. Let N₀ be a Borel null set containing every N_Z (Z ∈ 𝒫) and every s with ν_s(C_j) = ∞ for some j.
  - The modified slices. Put ν'_s := ν_s for s ∉ N₀ and ν'_s := 0 for s ∈ N₀.
 - Measurability of s ↦ ν'_s.
  - For each j, let 𝒟_j be the family of Borel Z such that s ↦ ν'_s(Z ∩ C_j) is Borel. It contains 𝒫, since Z ∩ C_j ∈ 𝒫.
  - 𝒟_j is a Dynkin system: ν'_s(Z^c ∩ C_j) = ν'_s(C_j) − ν'_s(Z ∩ C_j) with ν'_s(C_j) < ∞, and countable disjoint unions give sums.
  - By the π–λ theorem (MeasurableSpace.induction_on_inter), 𝒟_j contains all Borel sets. Letting j → ∞ (monotone), s ↦ ν'_s(Z) is Borel for every Borel Z.
  - By simple-function approximation and monotone convergence, s ↦ ∫ g dν'_s is Borel for every Borel g ≥ 0, and ∫_M g dH^n = ∫_L ∫ g dν'_s ds, since ν' = ν off a null set.
 - Joint measurability. For B ⊆ L × ℝ^P and v ∈ L, write B_v := {x : (v, x) ∈ B}.
  - Let 𝒞 be the family of Borel B ⊆ L × ℝ^P such that (s, v) ↦ ν'_s(B_v ∩ C_j) is Borel on L × L for every j.
  - 𝒞 contains the rectangles A × Z (A, Z Borel), for which the function is 1_A(v)·ν'_s(Z ∩ C_j). It is a Dynkin system by the same complement/disjoint-union argument.
  - By the π–λ theorem, 𝒞 contains all Borel B. Letting j → ∞, (s, v) ↦ ν'_s(B_v) is Borel. No kernel API is needed.
  - Applying this to B' and composing with the Borel map (s, v) ↦ (s + v, v) shows that (s, v) ↦ ν'_{s+v}(B'_v) is Borel.
 - Tonelli. For each v: ∫_L ν'_s(B_v) ds = H^n(M ∩ B_v) = 0, and ∫_L ν'_{s+v}(B'_v) ds = ∫_L ν'_t(B'_v) dt = H^n(M ∩ B'_v) = 0, using translation invariance of H^d⌞L. By Tonelli on L × L, for a.e. s: for a.e. v, ν'_s(B_v) = 0 and ν'_{s+v}(B'_v) = 0.
 - Choice of t₀. Fix t₀ ∈ 𝒯 ∖ N₀ with this property. Let V₀ be the full-measure set of v with ν_{t₀}(B_v) = 0, ν'_{t₀+v}(B'_v) = 0 and t₀ + v ∈ 𝒯 ∖ N₀; it has full measure since 𝒯 ∖ N₀ − t₀ is conull.
 - Consequence. Let v ∈ V₀ and t := t₀ + v. Then Γ(x + v) = Γ(x) for H^m-a.e. x ∈ M_{t₀}, and Γ(z − v) = Γ(z) for H^m-a.e. z ∈ M_t. For z ∈ p⁻¹(t) we have 1_M(z) = 1_{M_t}(z) and 1_M(z − v) = 1_{M_{t₀}}(z − v). Since ζ = ξ̃∘lift, the data (1_{M_t}θ, 1_{M_t}θζ) and z ↦ (1_{M_{t₀}}θ, 1_{M_{t₀}}θζ)(z − v) agree H^m-a.e. on M_t ∪ (M_{t₀} + v); both vanish off this set. By translation invariance of H^m:
 (★) R_t.action(γ) = R_{t₀}.action(γ(· + v)) for every test m-form γ, and R_t.measure(A) = R_{t₀}.measure(A − v) for every Borel A.
8. (Definition of R₀ and S₀.)
 - R₀ := (M₀, θ₀, ζ₀) with M₀ := M_{t₀} − t₀, θ₀(y) := θ(y + t₀) and ζ₀(y) := ζ(y + t₀). It is an IMRep of dimension m: the translate of R_{t₀}, as in step 6.
 - By the accepted dtc_imrep_current, let S₀ ∈ 𝒟_m(ℝ^P) be a current represented by R₀. Then R₀.action(γ) = R_{t₀}.action(γ(· − t₀)) and μ₀(A) := R₀.measure(A) = R_{t₀}.measure(A + t₀).
 (a) M₀ ⊆ {y : p(y + t₀) = t₀} = {y : p(y) = 0} = L^⊥, since p(t₀) = t₀. Hence μ₀(ℝ^P ∖ L^⊥) = 0.
 (b) spt S₀ ⊆ L^⊥. Let x ∉ L^⊥; L^⊥ is closed, so some ball W around x with compact closure misses L^⊥. Every test m-form γ with tsupport γ ⊆ W vanishes on M₀ ⊆ L^⊥, so S₀(γ) = ∫_{M₀} θ₀ζ₀(γ) dH^m = 0. Hence W lies in the zero region of S₀ and x ∉ spt S₀.
 (c) Measure identity. For Borel A, μ(A) = ∫_L R_t.measure(A) dt (step 5). For a.e. t, namely t = t₀ + v with v ∈ V₀, (★) gives R_t.measure(A) = R_{t₀}.measure(A − v) = μ₀(A − t) = R₀.measure((fun y => t + y)⁻¹' A). Hence μ(A) = ∫⁻ t in L, R₀.measure((fun y => t + y)⁻¹' A) ∂μHE[d].
 (d) Product formula. Let ω be a test n-form. By step 5, S(ω) = ∫_L R_t.action(♭ω) dt. For t = t₀ + v with v ∈ V₀, (★) gives R_t.action(♭ω) = R_{t₀}.action((♭ω)(· + v)) = R₀.action(y ↦ ♭ω(y + t₀ + v)) = S₀(y ↦ ♭(ω(t + y))). By step 1 this equals currentEval S₀ (fun y => ♭(ω(t + y))). The integrands agree a.e. in t, so S(ω) = ∫_L currentEval S₀ (fun y => ♭(ω(t + y))) dH^d(t). ∎

## Key steps

1. Write ξ = f_1∧⋯∧f_d∧ζ on the good set, with ζ := ξ̃∘lift a measurable unit orientation of T_x∩L^⊥ and ξ(α) = ζ(♭α).
2. The child spine_coarea slices M by p: for a.e. t, R_t = (M ∩ p⁻¹(t), θ, ζ) is an m-dimensional IMRep, S(ω) = ∫_L R_t.action(♭ω) dt and μ(A) = ∫_L R_t.measure(A) dt.
3. Translation invariance and the accepted uniqueness lemmas make the data (1_Mθ, 1_Mθξ̃) L-invariant H^n-a.e.
4. Tonelli on L × L, with a measurable version of the slice kernel, picks a base slice t₀ with R_{t₀+v} = τ_{v#}R_{t₀} for a.e. v.
5. R₀ := R_{t₀} − t₀ and S₀ := its current give μ₀ concentrated on L^⊥, spt S₀ ⊆ L^⊥, μ = ∫_L μ₀(· − t) dt and S(ω) = ∫_L S₀(♭ω(t + ·)) dt.

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
