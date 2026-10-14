<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_masses-a1 -->

## Theorem `Submission.dimred_cs_sos_mt_cm_box_masses`

Let P, k, m, n ∈ ℕ, let g = (g_1, …, g_k) (g : Fin k → Euclid P) be orthonormal with span G := span{g_1, …, g_k}, p := G.starProjection, q := G^⊥.starProjection, H^k := μHE[k], let 0 < r < s, Q_r := {t ∈ G : |⟨g_i, t⟩| ≤ r for all i}, C_s := {x ∈ ℝ^P : |⟨g_i, x⟩| < s for all i}, let B ⊆ ℝ^P be open and W := p⁻¹(C_s) ∩ q⁻¹(B). Let S, A₁, A₂ ∈ 𝒟_n(ℝ^P) be represented by IMReps R, R_{A₁}, R_{A₂} (IMRep univ n), and let R₀, R₀′ ∈ IMRep(ℝ^P, m) have measures μ₀ := R₀.measure, μ₀′ := R₀′.measure carried by G^⊥ (μ₀(ℝ^P ∖ G^⊥) = 0 = μ₀′(ℝ^P ∖ G^⊥)). Assume, for every Borel A ⊆ ℝ^P (with A − t := (y ↦ t + y)⁻¹(A)): R.measure(A) = ∫_G μ₀(A − t) dH^k(t), R_{A₁}.measure(A) = ∫_{G∖Q_r} μ₀(A − t) dH^k(t) and R_{A₂}.measure(A) = ∫_{Q_r} μ₀′(A − t) dH^k(t) (lower Lebesgue integrals). Then M_W(S) = ofReal((2s)^k)·μ₀(B), M_W(A₁) = (ofReal((2s)^k) − ofReal((2r)^k))·μ₀(B) (truncated subtraction in [0, ∞]) and M_W(A₂) = ofReal((2r)^k)·μ₀′(B), where M_W = massOn W and ofReal = ENNReal.ofReal.

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_masses-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8645

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_cs_sos_mt_cm_box_masses`

```lean
∀ (P k m n : ℕ) (g : Fin k → Euclid P) (S A₁ A₂ : GeometricCurrentOn (univ : Set (Euclid P)) n) (R RA₁ RA₂ : IMRep (univ : Set (Euclid P)) n) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (r s : ℝ) (B : Set (Euclid P)), Orthonormal ℝ g → 0 < r → r < s → IsOpen B → R.Represents S → RA₁.Represents A₁ → RA₂.Represents A₂ → R₀.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → R₀'.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₁.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)) \ {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₂.measure A = ∫⁻ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀'.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → S.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * s) ^ k) * R₀.measure B ∧ A₁.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = (ENNReal.ofReal ((2 * s) ^ k) - ENNReal.ofReal ((2 * r) ^ k)) * R₀.measure B ∧ A₂.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * r) ^ k) * R₀'.measure B
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_masses-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 8 of the selected proof ("box masses"), with the half-width r + 1 replaced by s > r and ball(0, ρ) by an arbitrary open B. The selected proof is the project's argument for Simon, Lemma 7.3.5 (book/chapter-07.txt, lines 407–417), whose proof Simon leaves to the reader.
Inherited results cited by exact Lean name:
 (F1) Submission.imrep_represents_massOn_eq_measure: if U is open, R represents T ∈ 𝒟_n(U) and W ⊆ U is open, then M_W(T) = R.measure(W).
 (PB) Submission.dimred_cs_sos_mt_product_box_measure: for a subspace G, measures ν, σ on ℝ^P and a Borel E ⊆ G with σ(ℝ^P ∖ G^⊥) = 0 and ν(A) = ∫_E σ(A − t) dH^k(t) for all Borel A, one has ν(p⁻¹(C) ∩ q⁻¹(B)) = H^k(E ∩ C)·σ(B) for all Borel C, B (p := G.starProjection, q := G^⊥.starProjection).
 (FM) Submission.dimred_cs_sos_mt_frame_measure, part (ii): for orthonormal g and every ρ′ > 0, H^k({t ∈ span g : |⟨g_i, t⟩| ≤ ρ′ ∀ i}) = H^k({t ∈ span g : |⟨g_i, t⟩| < ρ′ ∀ i}) = ofReal((2ρ′)^k).
Notation. G := span g, H^k := μHE[k], a := ofReal((2s)^k), b := ofReal((2r)^k), O_s := {t ∈ G : |⟨g_i, t⟩| < s ∀ i}.

1. (Borel sets.) G is closed (finite-dimensional subspace); Q_r = G ∩ ⋂_i {t : |⟨g_i, t⟩| ≤ r} is closed; C_s = ⋂_i {x : |⟨g_i, x⟩| < s} is open (finite intersection of open sets); B is open. Hence G, Q_r, G ∖ Q_r, C_s and B are Borel; Q_r ⊆ G and G ∖ Q_r ⊆ G.
2. (W is open.) p and q are continuous linear maps, so W = p⁻¹(C_s) ∩ q⁻¹(B) is open.
3. (Box volumes.) By (FM)(ii) with ρ′ := r > 0: H^k(Q_r) = b; with ρ′ := s > 0 (s > r > 0): H^k(O_s) = a. Note G ∩ C_s = O_s as sets.
4. (Mass = measure.) By (F1) with U := ℝ^P (open) and the open W ⊆ ℝ^P: M_W(S) = R.measure(W), M_W(A₁) = R_{A₁}.measure(W), M_W(A₂) = R_{A₂}.measure(W).
5. (Product formula on the box.) Apply (PB) with the subspace G, C := C_s and the Borel set B, three times: (ν, σ, E) := (R.measure, μ₀, G), (R_{A₁}.measure, μ₀, G ∖ Q_r), (R_{A₂}.measure, μ₀′, Q_r). In each case σ(ℝ^P ∖ G^⊥) = 0 by hypothesis, E is a Borel subset of G (step 1) and the required integral formula for ν is a hypothesis. This gives
 R.measure(W) = H^k(G ∩ C_s)·μ₀(B), R_{A₁}.measure(W) = H^k((G ∖ Q_r) ∩ C_s)·μ₀(B), R_{A₂}.measure(W) = H^k(Q_r ∩ C_s)·μ₀′(B).
6. (S.) H^k(G ∩ C_s) = H^k(O_s) = a by step 3, so M_W(S) = ofReal((2s)^k)·μ₀(B).
7. (A₂.) Q_r ⊆ C_s, because |⟨g_i, t⟩| ≤ r < s; hence Q_r ∩ C_s = Q_r and M_W(A₂) = H^k(Q_r)·μ₀′(B) = ofReal((2r)^k)·μ₀′(B).
8. (A₁.) Elementwise, (G ∖ Q_r) ∩ C_s = (G ∩ C_s) ∖ Q_r = O_s ∖ Q_r. Moreover Q_r ⊆ O_s (Q_r ⊆ G and step 7), Q_r is Borel and H^k(Q_r) = b < ∞, so H^k(O_s ∖ Q_r) = H^k(O_s) − H^k(Q_r) = a − b (measure_sdiff). Hence M_W(A₁) = (ofReal((2s)^k) − ofReal((2r)^k))·μ₀(B). ∎

Formalization sketch (context, not part of the numbered proof). The following Lean proof of exactly the frozen type compiled during decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract opens), with every cited Submission.* dependency present as a stub of its exact frozen type:
theorem Submission.dimred_cs_sos_mt_cm_box_masses : ∀ (P k m n : ℕ) (g : Fin k → Euclid P) (S A₁ A₂ : GeometricCurrentOn (univ : Set (Euclid P)) n) (R RA₁ RA₂ : IMRep (univ : Set (Euclid P)) n) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (r s : ℝ) (B : Set (Euclid P)), Orthonormal ℝ g → 0 < r → r < s → IsOpen B → R.Represents S → RA₁.Represents A₁ → RA₂.Represents A₂ → R₀.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → R₀'.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₁.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)) \ {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₂.measure A = ∫⁻ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀'.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → S.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * s) ^ k) * R₀.measure B ∧ A₁.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = (ENNReal.ofReal ((2 * s) ^ k) - ENNReal.ofReal ((2 * r) ^ k)) * R₀.measure B ∧ A₂.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * r) ^ k) * R₀'.measure B := by
  intro P k m n g S A₁ A₂ R RA₁ RA₂ R₀ R₀' r s B hg hr hrs hB hR hRA₁ hRA₂ hR₀c hR₀'c hRμ hμA₁ hμA₂
  have hGc : IsClosed ((Submodule.span ℝ (Set.range g) : Set (Euclid P))) :=
    Submodule.closed_of_finiteDimensional _
  have hQc : IsClosed {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} := by
    have hset : {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} =
        (Submodule.span ℝ (Set.range g) : Set (Euclid P)) ∩ ⋂ i, {t | |inner ℝ (g i) t| ≤ r} := by
      ext t; simp
    rw [hset]
    exact hGc.inter (isClosed_iInter fun i =>
      isClosed_le (continuous_const.inner continuous_id).abs continuous_const)
  have hCo : IsOpen {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} := by
    have hset : {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} = ⋂ i, {x | |inner ℝ (g i) x| < s} := by
      ext x; simp
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_const.inner continuous_id).abs continuous_const
  have hWo : IsOpen ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩
      (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) :=
    (hCo.preimage (Submodule.span ℝ (Set.range g)).starProjection.continuous).inter
      (hB.preimage (Submodule.span ℝ (Set.range g))ᗮ.starProjection.continuous)
  -- box volumes (frame_measure (ii))
  obtain ⟨-, hfm⟩ := Submission.dimred_cs_sos_mt_frame_measure P k g hg
  have hQμ := (hfm r hr).1
  have hOμ := (hfm s (hr.trans hrs)).2
  have hQC : {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} ⊆
      {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} := fun t ht i => (ht.2 i).trans_lt hrs
  have hGC : (Submodule.span ℝ (Set.range g) : Set (Euclid P)) ∩ {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} =
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < s} := rfl
  -- masses = measures (F1), then the product formula on the box (product_box_measure)
  have mS := Submission.imrep_represents_massOn_eq_measure P n univ _ S R isOpen_univ hR hWo (subset_univ _)
  have mA₁ := Submission.imrep_represents_massOn_eq_measure P n univ _ A₁ RA₁ isOpen_univ hRA₁ hWo (subset_univ _)
  have mA₂ := Submission.imrep_represents_massOn_eq_measure P n univ _ A₂ RA₂ isOpen_univ hRA₂ hWo (subset_univ _)
  rw [Submission.dimred_cs_sos_mt_product_box_measure P k _ R.measure R₀.measure _ hR₀c hGc.measurableSet
    subset_rfl hRμ _ B hCo.measurableSet hB.measurableSet, hGC, hOμ] at mS
  rw [Submission.dimred_cs_sos_mt_product_box_measure P k _ RA₁.measure R₀.measure _ hR₀c
    (hGc.measurableSet.diff hQc.measurableSet) sdiff_subset hμA₁ _ B hCo.measurableSet hB.measurableSet] at mA₁
  rw [Submission.dimred_cs_sos_mt_product_box_measure P k _ RA₂.measure R₀'.measure _ hR₀'c
    hQc.measurableSet (fun t ht => ht.1) hμA₂ _ B hCo.measurableSet hB.measurableSet,
    inter_eq_left.mpr hQC, hQμ] at mA₂
  have hdiff : ((Submodule.span ℝ (Set.range g) : Set (Euclid P)) \
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}) ∩ {x | ∀ i, |inner ℝ (g i) x| < s} =
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < s} \
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} := by
    rw [← hGC]; ext t; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
  have hQO : {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} ⊆
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < s} :=
    fun t ht => ⟨ht.1, fun i => (ht.2 i).trans_lt hrs⟩
  rw [hdiff, measure_sdiff hQO hQc.measurableSet.nullMeasurableSet
    (by rw [hQμ]; exact ENNReal.ofReal_ne_top), hOμ, hQμ] at mA₁
  exact ⟨mS, mA₁, mA₂⟩

## Key steps

1. G, Q_r, G ∖ Q_r, C_s, B are Borel and W = p⁻¹(C_s) ∩ q⁻¹(B) is open; by Submission.imrep_represents_massOn_eq_measure the three masses on W are R.measure(W), R_{A₁}.measure(W), R_{A₂}.measure(W).
2. Submission.dimred_cs_sos_mt_product_box_measure turns each into H^k(E ∩ C_s)·σ(B) with (E, σ) = (G, μ₀), (G ∖ Q_r, μ₀), (Q_r, μ₀′).
3. Submission.dimred_cs_sos_mt_frame_measure (ii): H^k(G ∩ C_s) = ofReal((2s)^k) and H^k(Q_r) = ofReal((2r)^k).
4. Q_r ⊆ G ∩ C_s (r < s), so Q_r ∩ C_s = Q_r and H^k((G ∖ Q_r) ∩ C_s) = H^k((G ∩ C_s) ∖ Q_r) = ofReal((2s)^k) − ofReal((2r)^k) by measure_sdiff.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1 = workspace HEAD, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean and Submission.lean with the workspace copies (identical)`
- `python3 over dag.json: the selected node, its ancestors' depends_on and statuses, the exact lean_statement of all 14 dependency/reuse declarations, accepted nodes whose lean_statement mentions '.support', 'ᶜ = 0', 'cycle', 'competitor' (found dimred_mbl_lc_rc_cycle_competitor, dtc_bc_lc_rc_cycle_competitor, cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top), and grep -c of the five new dimred_cs_sos_mt_cm_* names (0 hits)`
- `git show 35e359955ef6bac37033306b3f33a12c284b7174:GMT/Ch07/Submission.lean: Submission.dimred_mbl_lc_rc_cycle_competitor present with a type byte-identical to dag.json; its import lines equal the contract's`
- `grep -n over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean: GeometricCurrentOn, boundary(_apply), zero_apply, ext, massOn, mass, massOn_mono, massAdmissibleOn, VanishesOn, zeroRegion, support, testFormOnInclusion, restrictDomain, IsTestForm`
- `grep -rn over the snapshot mathlib: setIntegral_sdiff, integral_sub, measure_sdiff (measure_diff deprecated), ENNReal.le_of_add_le_add_left, withDensity_absolutelyContinuous, withDensity_apply, Measure.restrict_apply', Measure.restrict_restrict, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, starProjection_apply_mem, starProjection_eq_self_iff, Submodule.isClosed_orthogonal, Submodule.closed_of_finiteDimensional, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype, isBounded_iff_subset_ball, isBounded_iff_subset_closedBall, Bornology.IsBounded.isCompact_closure`
- `grep -n '3.5\|left to the reader' book/chapter-07.txt; sed -n 405,420p (Lemma 3.5, proof left to the reader)`
- `lake env lean /tmp/cm-decomp/{T0,Assembly,A,B,D,E,F,Final}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8a972d0014/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-4725781174/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Pins match. The manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean and Submission.lean are byte-identical to the workspace files. Simon leaves Lemma 7.3.5 to the reader, so the children are extracted from the supplied project proof. Neither SimonGMT nor the snapshot mathlib contains the five new statements, and their names are unused in dag.json and the snapshot. One accepted declaration fits exactly: Submission.dimred_mbl_lc_rc_cycle_competitor (accepted; candidate 35e35995; type byte-identical; contract imports). It is reused as the Step 4 child. Other accepted lemmas found (cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top) are not ancestor dependencies. Their content is covered in a few lines inside carried_transfer and box_cancellation, so they are not added. The snapshot mathlib supplies every library fact the child proofs use, under the names cited, including setIntegral_sdiff, measure_sdiff, ENNReal.le_of_add_le_add_left, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype and Bornology.IsBounded.isCompact_closure. Lean check (Final.lean): the 5 new children are proved from stubs of exactly their cited dependencies, and the frozen parent type is proved from the child and dependency stubs. It compiles with no errors; sorry occurs only in the 14 stubs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
