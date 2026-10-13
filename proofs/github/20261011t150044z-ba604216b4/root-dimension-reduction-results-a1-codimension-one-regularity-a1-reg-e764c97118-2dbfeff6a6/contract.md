<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.graph_over_tangent-a1 -->

## Theorem `Submission.codim1_rdo_gc_graph_over_tangent`

Let P, d ∈ ℕ, let U ⊆ ℝ^P be open, let N ⊆ ℝ^P be an embedded C² submanifold of dimension d (IsEmbeddedSubmanifold 2 d N), let x ∈ N ∩ U, and let ι : ℝ^d → ℝ^P be a linear isometry whose range equals the tangent space tangentSpace N x (as sets). Then there are u : ℝ^d → ℝ^P and reals δ₁, δ₂ > 0 such that: closedBall(x, δ₁ + δ₂) ⊆ U; u(0) = 0; Du(0) = fderiv ℝ u 0 = 0; u is C² on D := ball(0, δ₁); for every v ∈ D, u(v) ⊥ ι(ℝ^d) (⟨ιw, u(v)⟩ = 0 for all w), ‖Du(v)‖ ≤ 1, ‖u(v)‖ < δ₂/2 and x + ιv + u(v) ∈ N; and whenever v ∈ ℝ^d, h ∈ ℝ^P, ‖v‖ < δ₁, ‖h‖ < δ₂, h ⊥ ι(ℝ^d) and x + ιv + h ∈ N, then h = u(v).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.graph_over_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4739

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5153, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1262

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_rdo_gc_graph_over_tangent`

```lean
∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v
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
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.graph_over_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 2–5 of the parent proof of codim1_rdo_graph_chart: (1b) the chart is a homeomorphism, (1c) range Dψ(z₀) = Π, (1d) the graph map from the inverse function theorem and the choice of δ₁, δ₂, and the verification 5(a)–(d). Here the plane Π = T_xN is given through an arbitrary isometric parametrization ι, and the dimension is a general d (the parent uses d = n + 1). Siblings used: chart_tangent_range (accepted Submission.dsmc_chart_tangentSpace_eq_range) for parent steps 2–3, and local_inverse_c2 (Submission.codim1_rdo_gc_local_inverse_c2) for the inverse function theorem of step 4. Additionally the proof records Du(0) = 0, which the parent derives in step 4 and uses in step 6.

Notation. ι* := adjoint of ι (ι.toContinuousLinearMap.adjoint : ℝ^P → ℝ^d), so ⟨ιw, h⟩ = ⟨w, ι*h⟩ for w ∈ ℝ^d, h ∈ ℝ^P. "h ⊥ range ι" means ⟨ιw, h⟩ = 0 for all w.

Proof.
1. (Adjoint facts.)
 (a) ι*(ιw) = w for every w: for every w', ⟨w', ι*ιw⟩ = ⟨ιw', ιw⟩ = ⟨w', w⟩ because ι preserves inner products (LinearIsometry.inner_map_map).
 (b) If h ⊥ range ι then ι*h = 0: ⟨w, ι*h⟩ = ⟨ιw, h⟩ = 0 for all w.
 (c) If ι*h = 0 then h ⊥ range ι: ⟨ιw, h⟩ = ⟨w, ι*h⟩ = 0.
2. (Chart; parent (1b).) IsEmbeddedSubmanifold 2 d N at x ∈ N gives open V ⊆ ℝ^d and open W ⊆ ℝ^P with x ∈ W, and ψ : ℝ^d → ℝ^P that is C² and injective on V, with ψ(V) = W ∩ N, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W, and Dψ(z) injective for every z ∈ V. Since x ∈ W ∩ N = ψ(V), fix z₀ ∈ V with ψ(z₀) = x.
3. (Tangent plane and continuity of the inverse chart; parent (1b)–(1c).) The accepted lemma chart_tangent_range (dsmc_chart_tangentSpace_eq_range, with r = 2 ≥ 1, applied to the chart data of step 2 at z₀) gives:
 (i) tangentSpace N x = range Dψ(z₀);
 (ii) for every ε > 0 there is δ > 0 such that every z ∈ V with |ψ(z) − x| < δ satisfies |z − z₀| < ε. (This is the continuity of ψ⁻¹ at x, the consequence of properness that the parent derives in step 2.)
 With the hypothesis range ι = tangentSpace N x, (i) gives range Dψ(z₀) = range ι.
4. (The map φ; parent (1d).) Define φ(z) := ι*(ψ(z) − x). φ is C² on V (the continuous linear map ι* composed with ψ − x), and φ(z₀) = ι*(x − x) = 0. By the chain rule Dφ(z₀) = ι*∘Dψ(z₀). Dφ(z₀) is injective: let ι*Dψ(z₀)a₁ = ι*Dψ(z₀)a₂ and a := a₁ − a₂, so ι*Dψ(z₀)a = 0. As Dψ(z₀)a ∈ range Dψ(z₀) = range ι, write Dψ(z₀)a = ιw; then w = ι*ιw = ι*Dψ(z₀)a = 0 by 1(a), so Dψ(z₀)a = 0 = Dψ(z₀)0, and a = 0 because Dψ(z₀) is injective.
5. (Local inverse.) local_inverse_c2 applied to φ, V, z₀ gives open V₀, O ⊆ ℝ^d and g : ℝ^d → ℝ^d with z₀ ∈ V₀ ⊆ V, g C² on O, g(O) ⊆ V₀, φ(g(y)) = y for y ∈ O, and φ(z) ∈ O, g(φ(z)) = z for z ∈ V₀. Taking z = z₀: 0 = φ(z₀) ∈ O and g(0) = z₀.
6. (The graph map u; parent (★).) Define u(v) := ψ(g(v)) − x − ιv for every v ∈ ℝ^d.
 (a) (★) x + ιv + u(v) = ψ(g(v)) for every v.
 (b) u(0) = ψ(z₀) − x − ι0 = 0.
 (c) u is C² on O: g is C² on O with g(O) ⊆ V₀ ⊆ V and ψ is C² on V, so ψ∘g is C² on O; subtracting the constant x and the linear map ι keeps it C².
 (d) For v ∈ O: ι*u(v) = ι*(ψ(g(v)) − x) − ι*ιv = φ(g(v)) − v = v − v = 0, so u(v) ⊥ range ι by 1(c).
 (e) For v ∈ O: g(v) ∈ V, so x + ιv + u(v) = ψ(g(v)) ∈ ψ(V) = W ∩ N ⊆ N.
7. (Du(0) = 0; parent (1d).) Since u is C² on the open set O, it is differentiable at every point of O; g is differentiable at 0 ∈ O and ψ at g(0) = z₀ ∈ V.
 (a) Fix w ∈ ℝ^d. The real function v ↦ ⟨ιw, u(v)⟩ vanishes on the open neighbourhood O of 0 by 6(d), so its derivative at 0, namely a ↦ ⟨ιw, Du(0)a⟩, equals the derivative of the zero function, i.e. 0 (HasFDerivAt.congr_of_eventuallyEq and uniqueness of derivatives). Thus Du(0)a ⊥ range ι for every a.
 (b) By the chain rule, Du(0) = Dψ(z₀)∘Dg(0) − ι. For a ∈ ℝ^d, Dψ(z₀)(Dg(0)a) ∈ range Dψ(z₀) = range ι, say Dψ(z₀)(Dg(0)a) = ιw₁; so Du(0)a = ιw₁ − ιa = ι(w₁ − a).
 (c) By (a) with w = w₁ − a: ‖Du(0)a‖² = ⟨ι(w₁ − a), Du(0)a⟩ = 0. Hence Du(0)a = 0 for every a, i.e. Du(0) = 0.
8. (N near x lies in ψ(V₀); parent step 2.) V₀ is open and z₀ ∈ V₀, so choose ε > 0 with ball(z₀, ε) ⊆ V₀, and let δ_C > 0 correspond to this ε by 3(ii). Choose ρ_W > 0 with ball(x, ρ_W) ⊆ W and ρ_U > 0 with ball(x, ρ_U) ⊆ U (W, U open, x ∈ W ∩ U). Put s := min(ρ_W, δ_C, ρ_U) > 0. Claim: if q ∈ N and |q − x| < s, then q = ψ(z) for some z ∈ V₀. Indeed q ∈ ball(x, ρ_W) ⊆ W, so q ∈ W ∩ N = ψ(V) and q = ψ(z) with z ∈ V; |ψ(z) − x| < δ_C gives |z − z₀| < ε, so z ∈ V₀.
9. (Choice of δ₁, δ₂; parent step 4, last item.) Put r₁ := s/4 > 0 and δ₂ := r₁.
 - u is continuous at 0 (6(c)) with u(0) = 0, so there is ρ₁ > 0 with ‖u(v)‖ < r₁/2 whenever ‖v‖ < ρ₁.
 - Du is continuous on the open set O (u is C² on O; ContDiffOn.continuousOn_fderiv_of_isOpen) and Du(0) = 0, so there is ρ₂ > 0 with ‖Du(v)‖ < 1 whenever ‖v‖ < ρ₂.
 - O is open with 0 ∈ O, so there is ρ₃ > 0 with ball(0, ρ₃) ⊆ O.
 Put δ₁ := min(ρ₁, ρ₂, ρ₃, r₁) > 0.
10. (Verification; parent step 5.)
 (a) If |q − x| ≤ δ₁ + δ₂ then |q − x| ≤ 2r₁ = s/2 < s ≤ ρ_U, so q ∈ U. Hence closedBall(x, δ₁ + δ₂) ⊆ U.
 (b) u(0) = 0 (6(b)), Du(0) = 0 (step 7), and u is C² on ball(0, δ₁) ⊆ ball(0, ρ₃) ⊆ O (6(c)).
 (c) Let v ∈ ball(0, δ₁), so v ∈ O, ‖v‖ < ρ₁ and ‖v‖ < ρ₂. Then u(v) ⊥ range ι (6(d)), ‖Du(v)‖ ≤ 1, ‖u(v)‖ < r₁/2 = δ₂/2, and x + ιv + u(v) ∈ N (6(e)).
 (d) (Uniqueness; parent 5(d).) Let ‖v‖ < δ₁, ‖h‖ < δ₂, h ⊥ range ι, and q := x + ιv + h ∈ N. Then |q − x| = ‖ιv + h‖ ≤ ‖ιv‖ + ‖h‖ = ‖v‖ + ‖h‖ < δ₁ + δ₂ ≤ 2r₁ < s. By step 8, q = ψ(z) with z ∈ V₀. Then φ(z) = ι*(q − x) = ι*(ιv + h) = ι*ιv + ι*h = v + 0 = v by 1(a) and 1(b). By step 5, z = g(φ(z)) = g(v). By (★), x + ιv + u(v) = ψ(g(v)) = ψ(z) = q = x + ιv + h, hence h = u(v). (The parent uses ‖q − x‖² = ‖v‖² + ‖h‖²; the triangle inequality suffices.) ∎

Formalization note (verified). The following Lean proof was compiled against the frozen import closure of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3, Mathlib 25730c7c), with the accepted Submission.dsmc_chart_tangentSpace_eq_range and the sibling Submission.codim1_rdo_gc_local_inverse_c2 present, as a single appended declaration inside namespace GMT.Ch07 before main_theorem; #print axioms gives propext, Classical.choice, Quot.sound; it passes the runtime leaf-delta check (check_source_delta). It may be used verbatim:

theorem Submission.codim1_rdo_gc_graph_over_tangent : ∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v := by
  intro P d U N x ι hU hN hx hι
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hψinj, hψimg, hprop, hDψ⟩ := hN x hx.1
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [hψimg]; exact ⟨hxW, hx.1⟩
  obtain ⟨htan, hinvc, -⟩ := Submission.dsmc_chart_tangentSpace_eq_range P 2 d N V W ψ
    (by norm_num) hV hW hψ hψinj hψimg hprop hDψ z₀ hz₀V
  rw [hψz₀] at htan hinvc
  have hrangeψ : Set.range (fderiv ℝ ψ z₀) = Set.range ι := by rw [← htan, hι]
  have hψ2 : ContDiffOn ℝ 2 ψ V := by exact_mod_cast hψ
  -- the adjoint of ι
  set ιs : Euclid P →L[ℝ] Euclid d := ι.toContinuousLinearMap.adjoint with hιs
  have hadj : ∀ w h, inner ℝ (ι w) h = inner ℝ w (ιs h) := fun w h => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_right]; rfl
  have hιsι : ∀ w, ιs (ι w) = w := by
    intro w
    apply ext_inner_left ℝ
    intro w'
    rw [← hadj, LinearIsometry.inner_map_map]
  have hιs0 : ∀ h, (∀ w, inner ℝ (ι w) h = 0) → ιs h = 0 := by
    intro h hh
    apply ext_inner_left ℝ
    intro w
    rw [← hadj, hh w, inner_zero_right]
  -- the map φ = ι*(ψ - x) and its derivative at z₀
  have hψdiff : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz =>
    ((hψ2.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  let φ : Euclid d → Euclid d := fun z => ιs (ψ z - x)
  have hφ : ContDiffOn ℝ 2 φ V := ιs.contDiff.comp_contDiffOn (hψ2.sub contDiffOn_const)
  have hφderiv : HasFDerivAt φ (ιs.comp (fderiv ℝ ψ z₀)) z₀ :=
    ιs.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).sub_const x)
  have hφinj : Injective (fderiv ℝ φ z₀) := by
    rw [hφderiv.fderiv]
    intro a₁ a₂ h
    have h1 : ιs (fderiv ℝ ψ z₀ (a₁ - a₂)) = 0 := by
      have h' : ιs (fderiv ℝ ψ z₀ a₁) = ιs (fderiv ℝ ψ z₀ a₂) := h
      rw [map_sub, map_sub, h', sub_self]
    obtain ⟨w, hw⟩ : fderiv ℝ ψ z₀ (a₁ - a₂) ∈ Set.range ι := hrangeψ ▸ ⟨a₁ - a₂, rfl⟩
    rw [← hw, hιsι] at h1
    have h2 : fderiv ℝ ψ z₀ (a₁ - a₂) = fderiv ℝ ψ z₀ 0 := by rw [← hw, h1, map_zero, map_zero]
    exact sub_eq_zero.mp (hDψ z₀ hz₀V h2)
  obtain ⟨V₀, O, g, hV₀, hO, hz₀V₀, hV₀V, hg, hgmaps, hφg, hgφ⟩ :=
    Submission.codim1_rdo_gc_local_inverse_c2 d φ V z₀ hV hz₀V hφ hφinj
  have hφz₀ : φ z₀ = 0 := by simp [φ, hψz₀]
  obtain ⟨h0O, hg0⟩ := hgφ z₀ hz₀V₀
  rw [hφz₀] at h0O hg0
  -- the graph map u
  let u : Euclid d → Euclid P := fun v => ψ (g v) - x - ι v
  have hGu : ∀ v, x + ι v + u v = ψ (g v) := fun v => by simp only [u]; abel
  have hu0 : u 0 = 0 := by simp [u, hg0, hψz₀]
  have hgV : MapsTo g O V := fun y hy => hV₀V (hgmaps hy)
  have huC2 : ContDiffOn ℝ 2 u O :=
    ((hψ2.comp hg hgV).sub contDiffOn_const).sub ι.toContinuousLinearMap.contDiff.contDiffOn
  have hιsu : ∀ v ∈ O, ιs (u v) = 0 := by
    intro v hv
    have h1 : ιs (ψ (g v) - x) = v := hφg v hv
    simp only [u, map_sub, hιsι]
    rw [← map_sub, h1, sub_self]
  have horthO : ∀ v ∈ O, ∀ w, inner ℝ (ι w) (u v) = 0 := by
    intro v hv w
    rw [hadj, hιsu v hv, inner_zero_right]
  have hmemO : ∀ v ∈ O, x + ι v + u v ∈ N := fun v hv => by
    rw [hGu]
    have h1 : ψ (g v) ∈ ψ '' V := ⟨g v, hgV hv, rfl⟩
    rw [hψimg] at h1
    exact h1.2
  have hudiff : ∀ v ∈ O, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((huC2.contDiffAt (hO.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  -- Du(0) = 0
  have hDu0 : fderiv ℝ u 0 = 0 := by
    have hgdiff : HasFDerivAt g (fderiv ℝ g 0) 0 :=
      ((hg.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by norm_num)).hasFDerivAt
    have hψg : HasFDerivAt (fun v => ψ (g v)) ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0)) 0 := by
      have h' : HasFDerivAt ψ (fderiv ℝ ψ z₀) (g 0) := by rw [hg0]; exact hψdiff z₀ hz₀V
      exact h'.comp 0 hgdiff
    have huder : HasFDerivAt u ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0) - ι.toContinuousLinearMap) 0 :=
      (hψg.sub_const x).sub ι.toContinuousLinearMap.hasFDerivAt
    ext1 c
    -- orthogonality of the derivative
    have horthD : ∀ w, inner ℝ (ι w) (fderiv ℝ u 0 c) = 0 := by
      intro w
      have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hO.mem_nhds h0O) (fun v' hv' => horthO v' hv' w)
      have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
          ((innerSL ℝ (ι w)).comp (fderiv ℝ u 0)) 0 :=
        (innerSL ℝ (ι w)).hasFDerivAt.comp 0 (hudiff 0 h0O)
      have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid d →L[ℝ] ℝ) 0 :=
        (hasFDerivAt_const (0 : ℝ) 0).congr_of_eventuallyEq hloc
      have h2 := congrArg (fun L => L c) (hd.unique hd0)
      simpa using h2
    -- the derivative lies in the range of ι
    obtain ⟨w₁, hw₁⟩ : fderiv ℝ ψ z₀ (fderiv ℝ g 0 c) ∈ Set.range ι :=
      hrangeψ ▸ ⟨fderiv ℝ g 0 c, rfl⟩
    have hDuc : fderiv ℝ u 0 c = ι (w₁ - c) := by
      rw [huder.fderiv, map_sub]
      simp [hw₁]
    have h3 := horthD (w₁ - c)
    rw [← hDuc, real_inner_self_eq_norm_sq] at h3
    simpa using h3
  -- neighbourhood of x in N is covered by ψ(V₀)
  obtain ⟨ε, hε, hballV₀⟩ := Metric.isOpen_iff.mp hV₀ z₀ hz₀V₀
  obtain ⟨δC, hδC, hδCprop⟩ := hinvc ε hε
  obtain ⟨ρW, hρW, hballW⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨ρU, hρU, hballU⟩ := Metric.isOpen_iff.mp hU x hx.2
  set s := min (min ρW δC) ρU with hs
  have hspos : 0 < s := lt_min (lt_min hρW hδC) hρU
  have hNball : ∀ q ∈ N, dist q x < s → ∃ z ∈ V₀, ψ z = q := by
    intro q hq hqx
    have hqW : q ∈ W :=
      hballW (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_left _ _)))
    obtain ⟨z, hzV, rfl⟩ : q ∈ ψ '' V := by rw [hψimg]; exact ⟨hqW, hq⟩
    have h1 := hδCprop z hzV (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_right _ _)))
    exact ⟨z, hballV₀ h1, rfl⟩
  set r₁ := s / 4 with hr₁eq
  have hr₁ : 0 < r₁ := by positivity
  -- smallness of u and Du near 0
  have hucont : ContinuousAt u 0 := huC2.continuousOn.continuousAt (hO.mem_nhds h0O)
  have hDucont : ContinuousAt (fderiv ℝ u) 0 :=
    (huC2.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds h0O)
  obtain ⟨ρ₁, hρ₁, hρ₁prop⟩ := Metric.continuousAt_iff.mp hucont (r₁ / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, hρ₂prop⟩ := Metric.continuousAt_iff.mp hDucont 1 one_pos
  obtain ⟨ρ₃, hρ₃, hρ₃O⟩ := Metric.isOpen_iff.mp hO 0 h0O
  set δ₁ := min (min (min ρ₁ ρ₂) ρ₃) r₁ with hδ₁eq
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min (lt_min hρ₁ hρ₂) hρ₃) hr₁
  have hδ₁ρ₁ : δ₁ ≤ ρ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁ρ₂ : δ₁ ≤ ρ₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁ρ₃ : δ₁ ≤ ρ₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁r₁ : δ₁ ≤ r₁ := min_le_right _ _
  have hballO : ball (0 : Euclid d) δ₁ ⊆ O := (ball_subset_ball hδ₁ρ₃).trans hρ₃O
  refine ⟨u, δ₁, r₁, hδ₁pos, hr₁, ?_, hu0, hDu0, huC2.mono hballO, ?_, ?_⟩
  · -- closed ball inside U
    intro q hq
    apply hballU
    rw [mem_closedBall] at hq
    rw [mem_ball]
    have : s ≤ ρU := min_le_right _ _
    linarith
  · intro v hv
    have hvO := hballO hv
    have hv0 : dist v 0 < δ₁ := hv
    refine ⟨horthO v hvO, ?_, ?_, hmemO v hvO⟩
    · have h1 := hρ₂prop (lt_of_lt_of_le hv0 hδ₁ρ₂)
      rw [hDu0, dist_zero_right] at h1
      exact h1.le
    · have h1 := hρ₁prop (lt_of_lt_of_le hv0 hδ₁ρ₁)
      rw [hu0, dist_zero_right] at h1
      exact h1
  · intro v h hv hh horthh hq
    have hvO : v ∈ O := hballO (by rw [mem_ball, dist_zero_right]; exact hv)
    have hqx : dist (x + ι v + h) x < s := by
      rw [dist_eq_norm, show x + ι v + h - x = ι v + h by abel]
      calc ‖ι v + h‖ ≤ ‖ι v‖ + ‖h‖ := norm_add_le _ _
        _ = ‖v‖ + ‖h‖ := by rw [LinearIsometry.norm_map]
        _ < δ₁ + r₁ := add_lt_add hv hh
        _ ≤ r₁ + r₁ := by linarith
        _ < s := by rw [hr₁eq]; linarith
    obtain ⟨z, hzV₀, hψz⟩ := hNball _ hq hqx
    have hφz : φ z = v := by
      show ιs (ψ z - x) = v
      rw [hψz, show x + ι v + h - x = ι v + h by abel, map_add, hιsι, hιs0 h horthh, add_zero]
    have hgz : g v = z := by rw [← hφz]; exact (hgφ z hzV₀).2
    have h1 := hGu v
    rw [hgz, hψz] at h1
    exact (add_left_cancel h1).symm

## Key steps

1. Chart ψ at x with ψ(z₀) = x; the accepted dsmc_chart_tangentSpace_eq_range gives range Dψ(z₀) = T_xN = range ι and continuity of ψ⁻¹ at x.
2. φ := ι*(ψ − x) is C² on V with injective Dφ(z₀) = ι*Dψ(z₀); local_inverse_c2 gives V₀, O, g.
3. u(v) := ψ(g v) − x − ιv is C² on O, u(0) = 0, ι*u = 0 on O, and x + ιv + u(v) = ψ(g v) ∈ N.
4. Du(0)a is both orthogonal to range ι and in range ι, so Du(0) = 0.
5. Continuity of ψ⁻¹ puts N ∩ B_s(x) inside ψ(V₀); take δ₂ = s/4 and δ₁ small enough that ‖u‖ < δ₂/2, ‖Du‖ ≤ 1 and ball(0, δ₁) ⊆ O.
6. Uniqueness: q = x + ιv + h ∈ N near x equals ψ(z) with φ(z) = v, so z = g(v) and h = u(v).

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
