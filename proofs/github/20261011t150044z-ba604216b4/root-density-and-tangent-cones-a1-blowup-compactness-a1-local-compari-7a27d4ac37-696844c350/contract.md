<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1.lower_lipschitz-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_c1t_lower_lipschitz`

Let P, d ∈ ℕ, let U ⊆ ℝ^d be open and K ⊆ U compact, and let g : ℝ^d → ℝ^P be C¹ on U (ContDiffOn ℝ 1 g U). Assume g is injective on K and Dg(z) = fderiv ℝ g z is injective for every z ∈ K. Then there is m > 0 such that m|a − b| ≤ |g(a) − g(b)| for all a, b ∈ K (Euclidean norms).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1.lower_lipschitz-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6044

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_c1t_lower_lipschitz`

```lean
∀ (P d : ℕ) (g : Euclid d → Euclid P) (U K : Set (Euclid d)), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → InjOn g K → (∀ z ∈ K, Injective (fderiv ℝ g z)) → ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖g a - g b‖
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1.lower_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 ("Lower") of the parent proof: "there is m > 0 with |g(a) − g(b)| ≥ m|a − b| for a, b ∈ B̄. Otherwise there are a_k ≠ b_k in B̄ with |g(a_k) − g(b_k)| < k⁻¹|a_k − b_k|. By compactness, pass to a subsequence with a_k → a, b_k → b, and e_k := (a_k − b_k)/|a_k − b_k| → e with |e| = 1. If a ≠ b, continuity gives g(a) = g(b), contradicting injectivity on B̄. If a = b, … |Dg(a)e| = lim_k |g(a_k) − g(b_k)|/|a_k − b_k| = 0, contradicting injectivity of Dg(a)." The parent applies this child with K = B̄ = closedBall(c, r), which is compact in ℝ^d. The only change is that B̄ is replaced by an arbitrary compact K ⊆ U. Accordingly the segment estimate of the case a = b is taken on a small ball around a inside U, where it is the mean value inequality; convexity of K is not needed.

Notation. |·| is the Euclidean norm; S := {e ∈ ℝ^d : |e| = 1}.

1. (Local facts at points of K.) Let x ∈ K. Then x ∈ U and U is open, so U is a neighbourhood of x on which g is C¹; hence g is C¹ at x (ContDiffOn.contDiffAt). In particular:
 (a) g is continuous at x;
 (b) g is strictly differentiable at x with derivative L_x := Dg(x): for every ε > 0 there is δ > 0 such that |g(y) − g(y') − L_x(y − y')| ≤ ε|y − y'| for all y, y' ∈ ball(x, δ).
 Proof of (b). Dg is continuous on the open set U because g is C¹ there. Choose δ > 0 with ball(x, δ) ⊆ U and ‖Dg(w) − L_x‖ ≤ ε for all w ∈ ball(x, δ). The map ψ(w) := g(w) − L_x w is differentiable on the convex set ball(x, δ) with ‖Dψ(w)‖ = ‖Dg(w) − L_x‖ ≤ ε. The mean value inequality gives |ψ(y) − ψ(y')| ≤ ε|y − y'| for y, y' ∈ ball(x, δ), which is the claim. (Mathlib packages (b) as ContDiffAt.hasStrictFDerivAt: HasStrictFDerivAt g (fderiv ℝ g x) x, whose isLittleO form says g(y) − g(y') − L_x(y − y') = o(|y − y'|) as (y, y') → (x, x).)

2. (Contradiction hypothesis.) Suppose no m > 0 has the stated property. Then for each k ∈ ℕ, applying this to m = 1/(k + 1) > 0, there are a_k, b_k ∈ K with
 |g(a_k) − g(b_k)| < (k + 1)⁻¹ |a_k − b_k|.   (∗)

3. (a_k ≠ b_k.) If |a_k − b_k| = 0, the right side of (∗) is 0 and (∗) would make a norm negative, which is impossible. So |a_k − b_k| > 0, and e_k := |a_k − b_k|⁻¹ (a_k − b_k) satisfies |e_k| = |a_k − b_k|⁻¹ |a_k − b_k| = 1, i.e. e_k ∈ S.

4. (Convergent subsequence.) K is compact, and S is compact (closed and bounded in the finite-dimensional space ℝ^d). So K × K × S is compact, and it contains (a_k, b_k, e_k) for every k. By sequential compactness there are (a, b, e) ∈ K × K × S and a strictly increasing φ : ℕ → ℕ with a_{φ(k)} → a, b_{φ(k)} → b and e_{φ(k)} → e. In particular a, b ∈ K and |e| = 1. Since φ(k) ≥ k, (φ(k) + 1)⁻¹ → 0.

5. (Case a ≠ b.) By 1(a) at a and at b, g(a_{φ(k)}) → g(a) and g(b_{φ(k)}) → g(b), so g(a_{φ(k)}) − g(b_{φ(k)}) → g(a) − g(b). By (∗),
 0 ≤ |g(a_{φ(k)}) − g(b_{φ(k)})| ≤ (φ(k) + 1)⁻¹ |a_{φ(k)} − b_{φ(k)}|,
 and the right side tends to 0 · |a − b| = 0. By the squeeze principle g(a_{φ(k)}) − g(b_{φ(k)}) → 0, so by uniqueness of limits g(a) − g(b) = 0. Thus g(a) = g(b) with a, b ∈ K and a ≠ b, contradicting the injectivity of g on K.

6. (Case a = b.) Put L := Dg(a); this is defined with a ∈ K. Write d_k := |a_{φ(k)} − b_{φ(k)}| > 0. Since e_{φ(k)} = d_k⁻¹(a_{φ(k)} − b_{φ(k)}) and L is linear,
 L e_{φ(k)} = d_k⁻¹ (g(a_{φ(k)}) − g(b_{φ(k)})) − d_k⁻¹ (g(a_{φ(k)}) − g(b_{φ(k)}) − L(a_{φ(k)} − b_{φ(k)})).
 Taking norms, and using (∗) on the first term,
 |L e_{φ(k)}| ≤ (φ(k) + 1)⁻¹ + |g(a_{φ(k)}) − g(b_{φ(k)}) − L(a_{φ(k)} − b_{φ(k)})| / d_k.
 The first term tends to 0 by step 4. For the second term, let ε > 0 and take δ from 1(b) at x = a. Since a_{φ(k)} → a and b_{φ(k)} → a, both points lie in ball(a, δ) for all large k, and then the quotient is ≤ ε. So the second term also tends to 0. By the squeeze principle, |L e_{φ(k)}| → 0. On the other hand L is a continuous linear map, so L e_{φ(k)} → L e and |L e_{φ(k)}| → |L e|. By uniqueness of limits |L e| = 0. Then L e = 0 = L 0, and injectivity of L = Dg(a) gives e = 0, contradicting |e| = 1.

7. (Conclusion.) Both cases are impossible, so the hypothesis of step 2 is false. Hence there is m > 0 with m|a − b| ≤ |g(a) − g(b)| for all a, b ∈ K. ∎

Implementation note (not part of the mathematics). Mathlib alone suffices; no import beyond the frozen header is needed. The appendix below is a Lean proof of exactly this type. It compiled with `lake env lean` after `import GMT.Ch07.Submission` in the comparator's replayed contract scope, with no warnings; `#print axioms` gives [propext, Classical.choice, Quot.sound]. Key names: push Not; choose; mem_sphere_zero_iff_norm; IsCompact.prod; isCompact_sphere; IsCompact.tendsto_subseq; tendsto_one_div_add_atTop_nhds_zero_nat; StrictMono.tendsto_atTop; ContDiffOn.contDiffAt; ContDiffAt.hasStrictFDerivAt (with one_ne_zero); HasStrictFDerivAt.isLittleO; Filter.Tendsto.prodMk_nhds; Asymptotics.IsLittleO.comp_tendsto; IsLittleO.norm_norm; IsLittleO.tendsto_div_nhds_zero; squeeze_zero; tendsto_nhds_unique; ContDiffAt.continuousAt.

Appendix (verified Lean draft, scope: namespace GMT.Ch07 with the contract's open commands):
```lean
theorem Submission.dtc_bc_lc_sl_c1t_lower_lipschitz : (∀ (P d : ℕ) (g : Euclid d → Euclid P) (U K : Set (Euclid d)), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → InjOn g K → (∀ z ∈ K, Injective (fderiv ℝ g z)) → ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖g a - g b‖) := by
  intro P d g U K hU hK hKU hg hinj hDinj
  by_contra hcon
  push Not at hcon
  -- Steps 2–3: for each `k` there are `a_k ≠ b_k` in `K` with `|g a_k - g b_k| < (k + 1)⁻¹ |a_k - b_k|`
  choose a ha b hb hab using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  have hpos : ∀ k, 0 < ‖a k - b k‖ := by
    intro k
    have h1 := hab k
    have h2 := norm_nonneg (g (a k) - g (b k))
    by_contra hle
    push Not at hle
    have h0 : ‖a k - b k‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, mul_zero] at h1
    linarith
  -- Steps 3–4: unit vectors `e_k` and a convergent subsequence
  set e : ℕ → Euclid d := fun k => ‖a k - b k‖⁻¹ • (a k - b k) with he_def
  have he : ∀ k, e k ∈ sphere (0 : Euclid d) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, he_def]
    simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hpos k).ne'
  obtain ⟨⟨a0, b0, e0⟩, ⟨ha0, hb0, he0⟩, φ, hφ, hlim⟩ :=
    (hK.prod (hK.prod (isCompact_sphere (0 : Euclid d) 1))).tendsto_subseq
      (x := fun k => (a k, b k, e k)) (fun k => ⟨ha k, hb k, he k⟩)
  have hla : Tendsto (fun k => a (φ k)) atTop (𝓝 a0) := (continuous_fst.tendsto _).comp hlim
  have hlb : Tendsto (fun k => b (φ k)) atTop (𝓝 b0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hle : Tendsto (fun k => e (φ k)) atTop (𝓝 e0) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hinvk : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  by_cases hab0 : a0 = b0
  · -- Step 6: `a = b`; strict differentiability of `g` at `a` forces `Dg(a) e = 0`
    subst hab0
    have hstrict : HasStrictFDerivAt g (fderiv ℝ g a0) a0 :=
      (hg.contDiffAt (hU.mem_nhds (hKU ha0))).hasStrictFDerivAt one_ne_zero
    have hpair : Tendsto (fun k => (a (φ k), b (φ k))) atTop (𝓝 (a0, a0)) := hla.prodMk_nhds hlb
    have ho := (hstrict.isLittleO.comp_tendsto hpair).norm_norm.tendsto_div_nhds_zero
    -- `|Dg(a)e_k| ≤ |g a_k - g b_k| / |a_k - b_k| + o(1) → 0`
    have hbound : ∀ k, ‖fderiv ℝ g a0 (e (φ k))‖ ≤ 1 / ((φ k : ℝ) + 1) +
        ‖g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))‖ / ‖a (φ k) - b (φ k)‖ := by
      intro k
      have hk := hpos (φ k)
      have hdec : fderiv ℝ g a0 (e (φ k)) = ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k))) -
          ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))) := by
        rw [he_def, map_smul, ← smul_sub, sub_sub_cancel]
      rw [hdec]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hk]
        have := (hab (φ k)).le
        linarith [mul_comm (1 / ((φ k : ℝ) + 1)) ‖a (φ k) - b (φ k)‖]
      · rw [norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
    have htend : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
      simpa using hinvk.add ho
    have hL : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 ‖fderiv ℝ g a0 e0‖) :=
      (((fderiv ℝ g a0).continuous.tendsto _).comp hle).norm
    have hL0 : fderiv ℝ g a0 e0 = 0 := norm_eq_zero.1 (tendsto_nhds_unique hL htend)
    have he00 : e0 = 0 := hDinj a0 ha0 (by rw [hL0, map_zero])
    rw [he00, mem_sphere_zero_iff_norm, norm_zero] at he0
    exact zero_ne_one he0
  · -- Step 5: `a ≠ b`; continuity of `g` forces `g a = g b`
    have hcont : ∀ x ∈ K, ContinuousAt g x := fun x hx =>
      (hg.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt
    have hga : Tendsto (fun k => g (a (φ k))) atTop (𝓝 (g a0)) := (hcont a0 ha0).tendsto.comp hla
    have hgb : Tendsto (fun k => g (b (φ k))) atTop (𝓝 (g b0)) := (hcont b0 hb0).tendsto.comp hlb
    have hdiff : Tendsto (fun k => g (a (φ k)) - g (b (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbd : Tendsto (fun k => 1 / ((φ k : ℝ) + 1) * ‖a (φ k) - b (φ k)‖) atTop (𝓝 0) := by
        simpa using hinvk.mul (hla.sub hlb).norm
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hab (φ k)).le) hbd
    have hzero : g a0 - g b0 = 0 := tendsto_nhds_unique (hga.sub hgb) hdiff
    exact hab0 (hinj ha0 hb0 (sub_eq_zero.1 hzero))
```

## Key steps

1. Suppose not: for each k pick a_k, b_k ∈ K with |g(a_k) − g(b_k)| < (k+1)⁻¹|a_k − b_k|; then a_k ≠ b_k and e_k = (a_k − b_k)/|a_k − b_k| is a unit vector.
2. By compactness of K × K × S^{d−1}, a subsequence has a_{φ(k)} → a ∈ K, b_{φ(k)} → b ∈ K and e_{φ(k)} → e with |e| = 1.
3. If a ≠ b, continuity of g at a and b gives g(a) = g(b), contradicting injectivity of g on K.
4. If a = b, strict differentiability of the C¹ map g at a (mean value inequality near a) gives |Dg(a)e_{φ(k)}| ≤ (φ(k)+1)⁻¹ + o(1) → 0, so Dg(a)e = 0 with |e| = 1, contradicting injectivity of Dg(a).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in snapshot mathlib (25730c7c759d108ef87ab70af2342a196760f79d) and project (b4d606db1da5da8fa2c0292ad4924d97de8b3c4b); simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 in snapshot project/lake-manifest.json = workspace .lake/packages/simongmt HEAD; diff snapshot project/GMT/Ch07/Contract.lean vs workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `sed -n 1,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt = finrank ∧ Tendsto over 𝓝[>] 0 for every f : C_c)`
- `grep -n '^theorem' SimonGMT Chapter02/{WeightedArea,AreaLinearWeighted,AreaWeighted}.lean; sed WeightedArea.lean (integral_area_formula_of_injective_derivative, weighted_area_formula_volume_of_injective_derivative), AreaLinearWeighted.lean (weighted_linear_area_formula), Area.lean (areaJacobianAt), AreaApproximation.lean (continuous_normDet, measurable_areaJacobianAt)`
- `python3 -I import-closure walk from the Submission.lean imports over .lake/packages/simongmt: SimonGMT closure = Chapter01.{Basic,Hausdorff,MetricCriterion}, Chapter02.Lipschitz, Chapter03.Rectifiable (no WeightedArea / AreaLinearWeighted / AreaFormula)`
- `python3 -I tally of import headers over accepted candidate commits (892 keep the frozen header; some add Chapter02.WeightedArea, Chapter02.AreaLipschitz, BumpFunction.SmoothApprox); sed verifier/gmt-compare.py frozen_inputs/candidate_inputs (Submission.lean is excluded from the frozen byte check)`
- `python3 -I scans of dag.json (1523 nodes): lean_statement containing HasApproximateTangentSpaceAt together with ContDiff/fderiv/Lipschitz/graph; lean_name matching c1_image|lower_lipschitz; children of root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- `python3 -I /tmp/c1t_scripts/verify_reuse.py: git show <candidate_commit>:GMT/Ch07/Submission.lean, whitespace-normalised type comparison and sorry scan for codim1_rdo_c1pt_{fderiv_lower_bound,rescaled_area_formula,linear_range_integral,rescaled_integral_tendsto} and codim1_rdo_c1_piece_approxTangent (all IDENTICAL, no sorry); import-line count of commits dd15d7b, e2ca8ae, 9a707fe, 9ff7690 (8 = frozen header)`
- `lake env lean /tmp/c1t_check/reuse/Sub9ff.lean (commit 9ff76906 Submission + #print axioms)`
- `rg -n in snapshot mathlib/Mathlib: 'theorem ContDiffAt.hasStrictFDerivAt ', 'alias ⟨HasStrictFDerivAt.isLittleO', 'theorem IsCompact.tendsto_subseq ', 'theorem tendsto_one_div_add_atTop_nhds_zero_nat', 'theorem IsLittleO.tendsto_div_nhds_zero', 'theorem IsLittleO.comp_tendsto', 'theorem tendsto_integral_filter_of_dominated_convergence', 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'theorem HasFDerivAt.lim', 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen'; grep mem_sphere_zero_iff_norm, IsLittleO.norm_norm, Filter.Tendsto.prodMk_nhds`
- `grep -rl dtc_bc_lc_sl_c1t over the run directory (0 files); git log --all --oneline -S 'dtc_bc_lc_sl_c1t' over 6398 refs (0 commits)`
- `python3 -I /tmp/c1t_scripts/scope.py and /tmp/c1t_scripts/gen.py (gmt-compare.contract_scope and child_modules in contract mode; lean_contract.validate_lean_statement on all five child types)`
- `lake env lean /tmp/c1t_check/final/Challenge_{lower_lipschitz,rescaled_tendsto,fderiv_lower_bound,rescaled_area_formula,linear_range_integral}.lean, /tmp/c1t_check/assembly/Assembly.lean, /tmp/c1t_check/childA/ChildA.lean, /tmp/c1t_check/childB/ChildB.lean, /tmp/c1t_check/final/Combined.lean, /tmp/c1t_check/final/EndToEnd.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-3c37190a96/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e9bb54472d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-bab615aebf/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-272e126047/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/c1t_check/reuse/Sub9ff.lean`
- `/tmp/c1t_check/final/Challenge_lower_lipschitz.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_tendsto.lean`
- `/tmp/c1t_check/final/Challenge_fderiv_lower_bound.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_area_formula.lean`
- `/tmp/c1t_check/final/Challenge_linear_range_integral.lean`
- `/tmp/c1t_check/assembly/Assembly.lean`
- `/tmp/c1t_check/childA/ChildA.lean`
- `/tmp/c1t_check/childB/ChildB.lean`
- `/tmp/c1t_check/final/Combined.lean`
- `/tmp/c1t_check/final/EndToEnd.lean`

Pins match: snapshot Mathlib 25730c7c and project b4d606db; workspace SimonGMT at 2b366308. The snapshot Contract.lean equals the workspace Contract.lean, and Submission.lean is a byte copy of it.

SimonGMT has the cited weighted area formulas, in Chapter02/WeightedArea.lean and Chapter02/AreaLinearWeighted.lean, but neither is in Submission.lean's import closure.

The DAG already has comparator-accepted, sorry-free declarations whose types are verbatim the Bochner/√det forms of supplied steps 3 and 7, plus the derivative lower bound:
- codim1_rdo_c1pt_rescaled_area_formula (e2ca8ae)
- codim1_rdo_c1pt_linear_range_integral (9a707fe)
- codim1_rdo_c1pt_fderiv_lower_bound (dd15d7b)
Their commits keep the frozen header, and their axioms are [propext, Classical.choice, Quot.sound]. These three are reused.

No accepted declaration covers step 2 on a compact set, or steps 4–6 with g C¹ only on U and the closed ball:
- codim1_rdo_c1pt_rescaled_integral_tendsto needs g and the weight continuous everywhere and B open;
- codim1_rdo_c1cov_local_lower_lipschitz is only local and needs global ContDiff;
- dor_lmbsf_c1_image_approxTangent is still decomposing.
So there are two new leaves. Snapshot Mathlib supplies everything they need: ContDiffAt.hasStrictFDerivAt, IsCompact.tendsto_subseq, the isLittleO calculus, tendsto_integral_filter_of_dominated_convergence and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero.

All five child types validate and elaborate in the comparator contract scope. The frozen parent type is derived from them with no sorry, and its axioms are [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
