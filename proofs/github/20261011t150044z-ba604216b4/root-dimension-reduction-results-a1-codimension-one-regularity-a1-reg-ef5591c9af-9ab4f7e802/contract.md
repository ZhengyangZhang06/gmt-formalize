<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.orientation_along_graph-a1 -->

## Theorem `Submission.codim1_rdo_gc_orientation_along_graph`

Let P, n ∈ ℕ, N ⊆ ℝ^P, ξN : ℝ^P → Λ_{n+1}(ℝ^P) an orientation of N (IsOrientation (n+1) N ξN), x ∈ ℝ^P, and ι : ℝ^{n+1} → ℝ^P a linear isometry with ξN(x)(α) = α(ιe_0, …, ιe_n) for every (n+1)-covector α (e_i = EuclideanSpace.single i 1). Let δ > 0 and u : ℝ^{n+1} → ℝ^P with u(0) = 0, Du(0) = 0, u of class C¹ on D := ball(0, δ), ⟨ιw, u(v)⟩ = 0 for all v ∈ D and w ∈ ℝ^{n+1}, and x + ιv + u(v) ∈ N for all v ∈ D. Then for every v ∈ D and every (n+1)-covector α, ξN(x + ιv + u(v))(α)·J(v) = α(a_0(v), …, a_n(v)), where a_i(v) := ιe_i + Du(v)e_i and J(v) := √det(⟨a_i(v), a_j(v)⟩)_{i,j}.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.orientation_along_graph-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4739

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5167, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2574, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3134

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_rdo_gc_orientation_along_graph`

```lean
∀ (P n : ℕ) (N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ α : Covector (Euclid P) (n + 1), ξN x α = α (fun i => ι (EuclideanSpace.single i 1))) → 0 < δ → u 0 = 0 → fderiv ℝ u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 δ) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + u v ∈ N) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.orientation_along_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6, (6a)–(6e), of the parent proof of codim1_rdo_graph_chart, with the graph data (u C¹ on D, u ⊥ range ι, graph in N, u(0) = 0, Du(0) = 0) and the normalization ξN(x) = ιe_0∧…∧ιe_n of parent step 1 taken as hypotheses. Siblings used: gram_unit_orientation (Submission.codim1_rdo_gc_gram_unitOrientation) for (6c); the accepted orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg) for (6d); the accepted unit_orientation_dual (Submission.dor_ims_unitOrientation_dual) for the map L of (6e); the accepted chart_range_subset_tangent (Submission.dsmc_chart_range_subset_tangentSpace) for the curves of (6b); and the accepted covector_eval_continuous (Submission.dgoj_exists_continuous_covector_eval) for the continuity of (b_i) ↦ (α ↦ α(b_0, …, b_n)) used in (6e).

Notation. m := n + 1; G(v) := x + ιv + u(v); A(v) := ι + Du(v), a continuous linear map ℝ^m → ℝ^P; a(v) := (A(v)e_0, …, A(v)e_n), so a_i(v) = ιe_i + Du(v)e_i; Γ(v) := det(⟨a_i(v), a_j(v)⟩)_{i,j}; J(v) := √Γ(v).

Proof.
1. (Calculus.) D is open and u is C¹ on D. Hence for v ∈ D: u is differentiable at v with derivative Du(v); G has derivative A(v) at v (sum of the constant x, the continuous linear map ι and u), so DG(v)e_i = a_i(v); v ↦ Du(v) is continuous on D (ContDiffOn.continuousOn_fderiv_of_isOpen); and G is C¹ on D.
2. (Du(v) ⊥ range ι; parent (6a).) Fix v ∈ D and w ∈ ℝ^m. The real function v' ↦ ⟨ιw, u(v')⟩ vanishes on the open set D ∋ v, so its derivative at v, c ↦ ⟨ιw, Du(v)c⟩, is the derivative of the zero function, i.e. 0 (HasFDerivAt.congr_of_eventuallyEq and uniqueness of derivatives). Thus ⟨ιw, Du(v)c⟩ = 0 for all w, c.
3. (Injectivity; parent (6a).) For v ∈ D and c ∈ ℝ^m, step 2 gives ‖A(v)c‖² = ‖ιc‖² + 2⟨ιc, Du(v)c⟩ + ‖Du(v)c‖² = ‖c‖² + ‖Du(v)c‖² ≥ ‖c‖². So A(v)c = 0 implies c = 0: A(v) is injective. Hence a(v), the image of the standard basis under the injective linear map A(v), is linearly independent (LinearIndependent.map').
4. (Pointwise unit orientation; parent (6c).) Let ev : (Fin m → ℝ^P) → MultiVector P m be the continuous map with ev(c)(α) = α(c) from covector_eval_continuous. For v ∈ D, gram_unit_orientation applied to the linearly independent family a(v) gives Γ(v) > 0, so J(v) > 0. Define η(v) := J(v)⁻¹·ev(a(v)). Then η(v)(α)·J(v) = J(v)⁻¹α(a(v))·J(v) = α(a(v)) for every α, so by gram_unit_orientation again, η(v) is a unit orientation of S_v := span{a_0(v), …, a_n(v)}.
5. (Tangent space; parent (6b).) Let v ∈ D. IsOrientation at G(v) ∈ N gives a subspace Q_v with (Q_v as a set) = tangentSpace N (G(v)) and ξN(G(v)) a unit orientation of Q_v. chart_range_subset_tangent (with r = 1, the open set D, the C¹ map G and G(D) ⊆ N) gives range DG(v) ⊆ tangentSpace N (G(v)) = Q_v; in particular a_i(v) = DG(v)e_i ∈ Q_v for every i, so S_v ≤ Q_v. Now dim S_v = m because a(v) is linearly independent, and dim Q_v = m because Q_v is spanned by the orthonormal (hence linearly independent) m-family τ from IsUnitOrientationOf. Hence S_v = Q_v (Submodule.eq_of_le_of_finrank_eq), and η(v) is a unit orientation of Q_v.
6. (Sign; parent (6d).) By orientation_sign applied to the unit orientations η(v) and ξN(G(v)) of Q_v: ξN(G(v)) = η(v) or ξN(G(v)) = −η(v), for every v ∈ D.
7. (A continuous sign function; parent (6e).) Let L : MultiVector P m → Covector(ℝ^P, m) be the continuous linear map of unit_orientation_dual; since η(v) is a unit orientation (step 4), η(v)(L(η(v))) = 1 for v ∈ D. Put s(v) := ξN(G(v))(L(η(v))). By step 6, s(v) = 1 or s(v) = −1 for every v ∈ D. s is continuous on D:
 - v ↦ ξN(G(v)) is continuous on D, because ξN is continuous on N (IsOrientation) and G is continuous on D with G(D) ⊆ N;
 - v ↦ a(v) is continuous on D (a_i(v) = ιe_i + Du(v)e_i with Du continuous on D), hence v ↦ ev(a(v)) is continuous on D; Γ is continuous on D (determinant of a matrix with continuous entries ⟨a_i(v), a_j(v)⟩), so J = √Γ is continuous and positive on D and v ↦ J(v)⁻¹ is continuous on D; hence η is continuous on D;
 - L is continuous, and evaluation (ξ, β) ↦ ξ(β) is jointly continuous, so s is continuous on D (ContinuousOn.clm_apply).
8. (Value at the centre.) 0 ∈ D since δ > 0. G(0) = x + ι0 + u(0) = x. Since Du(0) = 0, a_i(0) = ιe_i, and ⟨ιe_i, ιe_j⟩ = ⟨e_i, e_j⟩ = δ_ij (ι is an isometry), so the Gram matrix at 0 is the identity, Γ(0) = 1 and J(0) = 1. Hence η(0)(α) = α(ιe_0, …, ιe_n) = ξN(x)(α) for every α, i.e. η(0) = ξN(x) = ξN(G(0)), and s(0) = η(0)(L(η(0))) = 1.
9. (Connectedness.) D is convex, hence preconnected. Suppose s(v₁) = −1 for some v₁ ∈ D. By the intermediate value theorem on the preconnected set D (IsPreconnected.intermediate_value with the points v₁ and 0), the value 0 ∈ [−1, 1] = [s(v₁), s(0)] is attained: s(w) = 0 for some w ∈ D. This contradicts s(w) ∈ {1, −1}. Hence s(v) = 1 for every v ∈ D.
10. (Conclusion.) Let v ∈ D. If ξN(G(v)) = −η(v), then s(v) = −η(v)(L(η(v))) = −1, contradicting step 9. So by step 6, ξN(G(v)) = η(v). Therefore, for every (n+1)-covector α, ξN(x + ιv + u(v))(α)·J(v) = η(v)(α)·J(v) = α(a(v)) = α(ιe_0 + Du(v)e_0, …, ιe_n + Du(v)e_n). ∎

Formalization note (verified). The following Lean proof was compiled against the frozen import closure of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3, Mathlib 25730c7c), with the five listed prerequisites present, as a single appended declaration inside namespace GMT.Ch07 before main_theorem; #print axioms gives propext, Classical.choice, Quot.sound; it passes the runtime leaf-delta check (check_source_delta). It may be used verbatim:

theorem Submission.codim1_rdo_gc_orientation_along_graph : ∀ (P n : ℕ) (N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ α : Covector (Euclid P) (n + 1), ξN x α = α (fun i => ι (EuclideanSpace.single i 1))) → 0 < δ → u 0 = 0 → fderiv ℝ u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 δ) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + u v ∈ N) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) := by
  intro P n N ξN x ι u δ hξ hιξ hδ hu0 hDu0 hu horth hmem
  set D := ball (0 : Euclid (n + 1)) δ with hD
  have hDopen : IsOpen D := isOpen_ball
  let e : Fin (n + 1) → Euclid (n + 1) := fun i => EuclideanSpace.single i 1
  let G : Euclid (n + 1) → Euclid P := fun v => x + ι v + u v
  let A : Euclid (n + 1) → (Euclid (n + 1) →L[ℝ] Euclid P) :=
    fun v => ι.toContinuousLinearMap + fderiv ℝ u v
  let a : Euclid (n + 1) → Fin (n + 1) → Euclid P := fun v i => ι (e i) + fderiv ℝ u v (e i)
  let gram : Euclid (n + 1) → ℝ := fun v => Matrix.det (Matrix.of fun i j => inner ℝ (a v i) (a v j))
  let J : Euclid (n + 1) → ℝ := fun v => Real.sqrt (gram v)
  have hudiff : ∀ v ∈ D, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((hu.contDiffAt (hDopen.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  have hGderiv : ∀ v ∈ D, HasFDerivAt G (A v) v := fun v hv => by
    have h1 : HasFDerivAt (fun v : Euclid (n + 1) => x + ι v) ι.toContinuousLinearMap v :=
      (ι.toContinuousLinearMap.hasFDerivAt).const_add x
    exact h1.add (hudiff v hv)
  have hAe : ∀ v ∈ D, ∀ i, fderiv ℝ G v (e i) = a v i := fun v hv i => by
    rw [(hGderiv v hv).fderiv]; rfl
  have hDuc : ContinuousOn (fderiv ℝ u) D := hu.continuousOn_fderiv_of_isOpen hDopen le_rfl
  have hGc : ContDiffOn ℝ 1 G D :=
    (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add hu
  -- derivative of u is orthogonal to range ι
  have hDorth : ∀ v ∈ D, ∀ w a', inner ℝ (ι w) (fderiv ℝ u v a') = 0 := by
    intro v hv w a'
    have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 v] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hDopen.mem_nhds hv) (fun v' hv' => horth v' hv' w)
    have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
        ((innerSL ℝ (ι w)).comp (fderiv ℝ u v)) v :=
      (innerSL ℝ (ι w)).hasFDerivAt.comp v (hudiff v hv)
    have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid (n + 1) →L[ℝ] ℝ) v :=
      (hasFDerivAt_const (0 : ℝ) v).congr_of_eventuallyEq hloc
    have h2 := congrArg (fun L => L a') (hd.unique hd0)
    simpa using h2
  -- injectivity and linear independence
  have hnorm : ∀ v ∈ D, ∀ c : Euclid (n + 1), ‖c‖ ^ 2 ≤ ‖A v c‖ ^ 2 := by
    intro v hv c
    have h1 : A v c = ι c + fderiv ℝ u v c := rfl
    rw [h1, norm_add_sq_real, hDorth v hv c c, LinearIsometry.norm_map]
    nlinarith [sq_nonneg ‖fderiv ℝ u v c‖]
  have hinj : ∀ v ∈ D, Injective (A v) := by
    intro v hv c₁ c₂ h12
    have h1 := hnorm v hv (c₁ - c₂)
    rw [map_sub, h12, sub_self, norm_zero] at h1
    have h2 : ‖c₁ - c₂‖ = 0 := by nlinarith [norm_nonneg (c₁ - c₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hlin : ∀ v ∈ D, LinearIndependent ℝ (a v) := by
    intro v hv
    have hb := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.linearIndependent
    have hker : LinearMap.ker (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (hinj v hv)
    have := hb.map' (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) hker
    convert this using 1
    funext i
    simp [a, A, e]
  -- pointwise orientation
  obtain ⟨ev, hevc, hev⟩ := Submission.dgoj_exists_continuous_covector_eval P (n + 1)
  let η : Euclid (n + 1) → MultiVector P (n + 1) := fun v => (J v)⁻¹ • ev (a v)
  have hgpos : ∀ v ∈ D, 0 < gram v := fun v hv =>
    (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).1
  have hJpos : ∀ v ∈ D, 0 < J v := fun v hv => Real.sqrt_pos.2 (hgpos v hv)
  have hηJ : ∀ v ∈ D, ∀ α, η v α * J v = α (a v) := by
    intro v hv α
    simp only [η, smul_apply, hev, smul_eq_mul]
    field_simp [(hJpos v hv).ne']
  have hηunit : ∀ v ∈ D, IsUnitOrientationOf (η v) (Submodule.span ℝ (Set.range (a v))) :=
    fun v hv => (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).2 _
      (hηJ v hv)
  -- tangent space identification
  have hrange := Submission.dsmc_chart_range_subset_tangentSpace P 1 (n + 1) N D G le_rfl hDopen
    (by simpa using hGc) (by rintro _ ⟨v, hv, rfl⟩; exact hmem v hv)
  have hsign : ∀ v ∈ D, ξN (G v) = η v ∨ ξN (G v) = -η v := by
    intro v hv
    obtain ⟨Q, hQ, hQξ⟩ := hξ.2 (G v) (hmem v hv)
    have hle : Submodule.span ℝ (Set.range (a v)) ≤ Q := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : a v i ∈ tangentSpace N (G v) := hrange v hv ⟨e i, hAe v hv i⟩
      rw [← hQ] at h1
      exact h1
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ (Set.range (a v))) = n + 1 := by
      rw [finrank_span_eq_card (hlin v hv)]; simp
    have hfin2 : Module.finrank ℝ Q = n + 1 := by
      obtain ⟨τ, hτ, hτspan, -⟩ := hQξ
      rw [← hτspan, finrank_span_eq_card hτ.linearIndependent]; simp
    have hEq := Submodule.eq_of_le_of_finrank_eq hle (hfin1.trans hfin2.symm)
    have hηQ : IsUnitOrientationOf (η v) Q := hEq ▸ hηunit v hv
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P (n + 1) (η v) (ξN (G v)) Q hηQ hQξ
  -- the sign function
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P (n + 1)
  have hηL : ∀ v ∈ D, η v (L (η v)) = 1 := fun v hv => (hL _ _ (hηunit v hv)).2.2
  let s : Euclid (n + 1) → ℝ := fun v => ξN (G v) (L (η v))
  have hs : ∀ v ∈ D, s v = 1 ∨ s v = -1 := by
    intro v hv
    rcases hsign v hv with h | h
    · left; simp only [s, h]; exact hηL v hv
    · right; simp only [s, h, neg_apply]; rw [hηL v hv]
  -- continuity
  have hGcont : ContinuousOn G D := hGc.continuousOn
  have hξG : ContinuousOn (fun v => ξN (G v)) D := hξ.1.comp hGcont (fun v hv => hmem v hv)
  have hac : ContinuousOn a D := continuousOn_pi.2 fun i =>
    continuousOn_const.add (hDuc.clm_apply continuousOn_const)
  have hgramc : ContinuousOn gram D := by
    have hM : ContinuousOn (fun v => (Matrix.of fun i j => inner ℝ (a v i) (a v j) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) D :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
        ((continuousOn_pi.1 hac) i).inner ((continuousOn_pi.1 hac) j)
    exact (continuous_id.matrix_det).comp_continuousOn hM
  have hJc : ContinuousOn J D := Real.continuous_sqrt.comp_continuousOn hgramc
  have hηc : ContinuousOn η D :=
    (hJc.inv₀ (fun v hv => (hJpos v hv).ne')).smul (hevc.comp_continuousOn hac)
  have hsc : ContinuousOn s D := hξG.clm_apply (L.continuous.comp_continuousOn hηc)
  -- value at the centre
  have h0D : (0 : Euclid (n + 1)) ∈ D := mem_ball_self hδ
  have hG0 : G 0 = x := by simp [G, hu0]
  have ha0 : a 0 = fun i => ι (e i) := by funext i; simp [a, hDu0]
  have hgram0 : gram 0 = 1 := by
    have hM : (Matrix.of fun i j => inner ℝ (a 0 i) (a 0 j) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := by
      ext i j
      rw [ha0, Matrix.of_apply, LinearIsometry.inner_map_map, Matrix.one_apply]
      simp [e, EuclideanSpace.inner_single_left]
    simp only [gram, hM, Matrix.det_one]
  have hJ0 : J 0 = 1 := by simp [J, hgram0]
  have hη0 : η 0 = ξN x := by
    ext α
    simp only [η, hJ0, inv_one, one_smul, hev, ha0, hιξ]
    rfl
  have hs0 : s 0 = 1 := by
    show ξN (G 0) (L (η 0)) = 1
    rw [hG0, ← hη0]; exact hηL 0 h0D
  have hsconst : ∀ v ∈ D, s v = 1 := by
    intro v hv
    rcases hs v hv with h | h
    · exact h
    · exfalso
      have hpre : IsPreconnected D := (convex_ball (0 : Euclid (n + 1)) δ).isPreconnected
      have hivt := hpre.intermediate_value hv h0D hsc
      rw [h, hs0] at hivt
      obtain ⟨w, hw, hw0⟩ := hivt (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      rcases hs w hw with h' | h' <;> rw [hw0] at h' <;> norm_num at h'
  -- conclusion
  intro v hv α
  have hpos : ξN (G v) = η v := by
    rcases hsign v hv with h | h
    · exact h
    · exfalso
      have h1 := hsconst v hv
      simp only [s, h, neg_apply] at h1
      rw [hηL v hv] at h1
      norm_num at h1
  show ξN (G v) α * J v = α (a v)
  rw [hpos]
  exact hηJ v hv α

## Key steps

1. Du(v) ⊥ range ι (the derivative of v' ↦ ⟨ιw, u(v')⟩ ≡ 0), so ‖A(v)c‖ ≥ ‖c‖ and a(v) is linearly independent.
2. η(v) := J(v)⁻¹ ev(a(v)) is a unit orientation of span a(v) (gram_unit_orientation); span a(v) = T_{G v}N by range DG(v) ⊆ T_{G v}N (chart_range_subset_tangent) and equal dimensions.
3. orientation_sign gives ξN(G v) = ±η(v).
4. s(v) = ξN(G v)(L η(v)) ∈ {±1} is continuous on D (continuity of ξN on N, ev, J), and s(0) = 1 because G(0) = x, a(0) = ιe, J(0) = 1.
5. The intermediate value theorem on the convex ball forces s ≡ 1, so ξN(G v) = η(v), which is the claimed identity.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: accepted lean_statements containing tangentSpace, IsEmbeddedSubmanifold, IsOrientation, IsUnitOrientationOf, Matrix.det, .det, InjOn, fderiv; lean_name lookups chart_tangentSpace_eq_range_fderiv, dsmc_chart_tangentSpace_eq_range, dsmc_chart_inverse_continuity, dsmc_chart_range_subset_tangentSpace, dgoj_unitOrientation_of_injective, dgoj_exists_continuous_covector_eval, dgoj_exists_det_covector, dgoj_covector_eq_det_mul_of_mem_span, dgoj_det_adjoint_comp_eq_det_sq, dpf_exists_orthonormal_frame_det_gram, rsdic_unitOrientation_eq_or_eq_neg, dor_ims_unitOrientation_dual, dgcr_graph_orientation_jacobian, regcomp_unit_orientation_pairing, unit_orientations_common_unit_covector; collision check for the five codim1_rdo_gc_* names`
- `grep in snapshot mathlib: to_localInverse, toOpenPartialHomeomorph, contDiffAt_symm, isOpen_injective, isometryOfOrthonormal, coe_toBasis, constr_range, norm_image_sub_le, ContinuousAlternatingMap.apply`
- `grep -rln 'toOpenPartialHomeomorph|localInverse|InverseFunctionTheorem|contDiffAt_symm' simongmt (--include=*.lean); import lines of simongmt Chapter03/Rectifiable.lean and Chapter06/{Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `lean -DautoImplicit=false /tmp/gc-split-check/Probe.lean and Probe2.lean (#print Covector, MultiVector; #check ContDiffAt.to_localInverse, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, ContDiffAt.hasStrictFDerivAt', ContinuousLinearMap.isOpen_injective, ContDiffOn.continuousOn_fderiv_of_isOpen, Convex.isPreconnected, ContinuousAlternatingMap.map_update_smul, LinearMap.det_toMatrix)`
- `lean -DautoImplicit=false /tmp/gc-split-check/Types.lean (all 12 child types plus the parent assembly; #print axioms)`
- `lean -DautoImplicit=false /tmp/gc-split-check/{Prove124b,Prove1,Prove3,Prove5}.lean (new child proofs against stubs of their prerequisites)`
- `git show <commit>:GMT/Ch07/Submission.lean for fe95347b, 9c8432cb, 44afba4d, 8f402cb9, 05029c89, 93ec31ab, 73310ec9; git merge-base --is-ancestor 8f402cb9 44afba4d; lean -DautoImplicit=false /tmp/gc-split-check/FullCheck.lean with #print axioms`
- `python3: _recursive_lean.leaf_verification.check_source_delta on each new proof and the assembly; _recursive_lean.lean_contract.validate_lean_statement on all 12 types; acyclicity and byte-identity of reused types against dag.json`
- `sed -n of /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _accepted_checkpoint), __init__.py limits, swarm-project.json (max_depth 6, max_children 12, max_nodes 1000), verifier/gmt-compare.py header`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-751a76913b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ea8963379b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-ce923d2f7f/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gc-split-check/Types.lean`
- `/tmp/gc-split-check/Prove124b.lean`
- `/tmp/gc-split-check/Prove3.lean`
- `/tmp/gc-split-check/Prove5.lean`
- `/tmp/gc-split-check/FullCheck.lean`

Pins match:
- manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308;
- the snapshot Contract.lean, workspace Contract.lean and Submission.lean share sha256 e4148e7f9503aa28….

Library (import closure of GMT.Ch07.Submission):
- Present: HasStrictFDerivAt.toOpenPartialHomeomorph (InverseFunctionTheorem/FDeriv.lean:117), OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881), ContinuousLinearMap.isOpen_injective (Normed/Module/FiniteDimension.lean:263), LinearMap.isometryOfOrthonormal (InnerProductSpace/Orthonormal.lean:330), Module.Basis.constr_range (Basis/Defs.lean:547), ContinuousAlternatingMap.map_update_smul.
- Missing: ContDiffAt.to_localInverse (InverseFunctionTheorem/ContDiff.lean). #check reports an unknown constant; SimonGMT uses it only in Chapter08/ConstancyNormalCharts.lean, which the contract does not import. It also gives C² only at the image point, so the neighbourhood inverse function theorem becomes the new child local_inverse_c2.

DAG (683 nodes):
- 7 accepted declarations are reused with byte-identical frozen types and non-empty candidate commits: dsmc_chart_tangentSpace_eq_range 44afba4d, dsmc_chart_range_subset_tangentSpace 8f402cb9 (an ancestor of 44afba4d), dgoj_exists_continuous_covector_eval 05029c89, dpf_exists_orthonormal_frame_det_gram 93ec31ab, dgoj_covector_eq_det_mul_of_mem_span 73310ec9, rsdic_unitOrientation_eq_or_eq_neg fe95347b, dor_ims_unitOrientation_dual 9c8432cb.
- The runtime allows reusing accepted checkpoints with an identical type (_existing_lean_name_problem, _accepted_checkpoint) and merges prerequisite candidate commits (_overlay_accepted_children).
- The five codim1_rdo_gc_* names occur nowhere in dag.json.
- No accepted node gives a neighbourhood C² inverse function theorem, the Gram-matrix form of the unit-orientation lemma (dgoj_unitOrientation_of_injective uses det(F*∘F)), or the orientation normal form of step 1.

Lean:
- All 12 child types elaborate after import GMT.Ch07.Submission in the contract scope.
- FullCheck.lean compiles; it contains the frozen Submission, the accepted reused proofs taken from their candidate commits, the 5 new child proofs and the parent assembly.
- #print axioms for Submission.codim1_rdo_graph_chart and all five new children gives [propext, Classical.choice, Quot.sound].
- Each new proof and the assembly pass check_source_delta, and every type passes validate_lean_statement.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
