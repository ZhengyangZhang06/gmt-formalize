<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1 -->

## Theorem `Submission.cmcdt_lpo_slice_forms`

For all N, k ∈ ℕ, writing ι(t, x) := (t, x_1, …, x_N) ∈ ℝ^{N+1} (Lean WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))), Jv := ι(0, v), e₀ := (1, 0, …, 0) (EuclideanSpace.single 0 1), |α| := covectorEuclideanNorm α and d := exteriorDerivative (Mathlib extDeriv): (a) for every ω ∈ 𝒟^{k+1}(ℝ^{N+1}) (TestFormOn univ (k + 1)) there is η ∈ 𝒟^k(ℝ^N) with η(x)(v_1, …, v_k) = ∫_0^1 ω(ι(t, x))(e₀, Jv_1, …, Jv_k) dt for all x and v, and tsupport η ⊆ {x : ∃ t ∈ [0, 1], ι(t, x) ∈ tsupport ω}; (b) for every s ∈ ℝ and ω ∈ 𝒟^k(ℝ^{N+1}) there is ρ ∈ 𝒟^k(ℝ^N) with ρ(x)(v_1, …, v_k) = ω(ι(s, x))(Jv_1, …, Jv_k) for all x and v; (c) for every β ∈ 𝒟^{k+1}(ℝ^{N+1}) and θ ∈ 𝒟^k(ℝ^N) such that θ(x)(v) = ∫_0^1 β(ι(t, x))(e₀, Jv_1, …, Jv_k) dt for all x and v ∈ (ℝ^N)^k, one has, for all x and v = (v_0, …, v_k) ∈ (ℝ^N)^{k+1}, ∫_0^1 dβ(ι(t, x))(e₀, Jv_0, …, Jv_k) dt = β(ι(1, x))(Jv_0, …, Jv_k) − β(ι(0, x))(Jv_0, …, Jv_k) − dθ(x)(v); (d) for every β ∈ 𝒟^0(ℝ^{N+1}), x ∈ ℝ^N and the empty tuple v: ∫_0^1 dβ(ι(t, x))(e₀) dt = β(ι(1, x))() − β(ι(0, x))(); (e) for every k-covector α on ℝ^N, continuous f : ℝ → Λ^k(ℝ^N)* and c ∈ ℝ with α(v) = ∫_0^1 f(t)(v) dt for all v and |f(t)| ≤ c for all t ∈ [0, 1]: |α| ≤ c.

Node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6064

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7530, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7569, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7606, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7628, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7654, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7671, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7697, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7718

## Lean problem

Declaration: `Submission.cmcdt_lpo_slice_forms`

```lean
(∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) ∧ (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof 0(a), 0(g) and A2(a), A2(d) (Simon Ch. 6, 2.17–2.22), stated at the level of forms. Notation. ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} for t ∈ ℝ, x ∈ ℝ^N; Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; tail y := WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)). |α| := covectorEuclideanNorm α. 𝒟^k(ℝ^N) = TestFormOn univ k (C^∞ forms with compact support; tsupport ⊆ univ is automatic) and 𝒟_k(ℝ^N) = GeometricCurrentOn univ k. For a C^∞ map F, F^#ω(x) := (ω (F x)).compContinuousLinearMap (fderiv ℝ F x). d = exteriorDerivative (Mathlib extDeriv). 
1. Coordinates. J : ℝ^N → ℝ^{N+1} is linear and ‖Jv‖ = ‖v‖ (the Euclidean norm of (0, v) is that of v), so J is a continuous linear isometric embedding; ι(t, x) = t·e₀ + Jx; tail is continuous linear with tail(ι(t, x)) = x and y = ι(y 0, tail y). Hence t ↦ ι(t, x) is affine with derivative e₀ and x ↦ ι(t, x) is affine with derivative J.
2. Contraction. For m ∈ ℕ let Φ_m : Λ^{m+1}(ℝ^{N+1})* → Λ^m(ℝ^N)*, Φ_m(γ) := (γ.curryLeft e₀).compContinuousLinearMap J. It is continuous linear (γ ↦ γ.curryLeft is the linear isometry ContinuousAlternatingMap.curryLeftLI, evaluation at e₀ is continuous linear, and compContinuousLinearMapCLM J is continuous linear), and Φ_m(γ)(v) = γ(Fin.cons e₀ (J ∘ v)) by curryLeft_apply_apply and compContinuousLinearMap_apply.
3. Smoothness of parametric integrals. Claim: if V is a finite-dimensional real normed space and h : ℝ × ℝ^N → V is C^∞, then x ↦ ∫_0^1 h(t, x) dt is C^∞ and has derivative ∫_0^1 D_x h(t, x) dt at x, where D_x h(t, x) := Dh(t, x) ∘ (0, ·) ∈ L(ℝ^N, V). Proof. Fix x₀. (t, x) ↦ D_x h(t, x) is continuous, hence bounded by some B on the compact set [0, 1] × closedBall(x₀, 1); h(t, ·) has derivative D_x h(t, x) at every x; all functions are continuous, hence measurable and interval integrable. By hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ = volume, a = 0, b = 1, s = ball(x₀, 1), constant bound B), x ↦ ∫_0^1 h(t, x) dt has derivative ∫_0^1 D_x h(t, x₀) dt at x₀. Now show by induction on n ∈ ℕ, for all finite-dimensional V and all C^∞ h simultaneously, that x ↦ ∫_0^1 h(t, x) dt is C^n: for n = 0 it is differentiable, hence continuous; for n + 1 it is differentiable with derivative x ↦ ∫_0^1 D_x h(t, x) dt, where (t, x) ↦ D_x h(t, x) is C^∞ with values in the finite-dimensional space L(ℝ^N, V) (composition of the C^∞ map Dh with the continuous linear map L ↦ L ∘ (0, ·)), so the derivative is C^n by the induction hypothesis and the function is C^{n+1} (contDiff_succ_iff_hasFDerivAt). Being C^n for every n, it is C^∞.
4. Part (a). Let ω ∈ 𝒟^{k+1}(ℝ^{N+1}) and g(t, x) := Φ_k(ω(ι(t, x))); g is C^∞ (ω is C^∞, (t, x) ↦ t·e₀ + Jx is affine, Φ_k is continuous linear). Put η(x) := ∫_0^1 g(t, x) dt ∈ Λ^k(ℝ^N)*. By step 3, η is C^∞. Evaluation at v is a continuous linear map (ContinuousAlternatingMap.apply) and commutes with the interval integral of the continuous function g(·, x) (ContinuousLinearMap.intervalIntegral_comp_comm), so η(x)(v) = ∫_0^1 g(t, x)(v) dt = ∫_0^1 ω(ι(t, x))(Fin.cons e₀ (J ∘ v)) dt, the required formula. Support: let K := {x : ∃ t ∈ [0, 1], ι(t, x) ∈ tsupport ω}. Since ω has compact support, tsupport ω is compact; K = tail(tsupport ω ∩ {y : y 0 ∈ [0, 1]}) (if ι(t, x) ∈ tsupport ω with t ∈ [0, 1] then y := ι(t, x) has y 0 = t and tail y = x; conversely y = ι(y 0, tail y)), the continuous image of a compact set, so K is compact and closed. If x ∉ K then ω(ι(t, x)) = 0 for every t ∈ [0, 1], so g(·, x) vanishes on [0, 1] and η(x) = 0. Hence support η ⊆ K and tsupport η ⊆ K. So η is C^∞ with compact support, i.e. an element of TestFormOn univ k, and both conjuncts of (a) hold.
5. Part (b). Let s ∈ ℝ and ω ∈ 𝒟^k(ℝ^{N+1}). The affine map a_s(x) := s·e₀ + Jx is proper: ‖a_s(x)‖ ≥ ‖Jx‖ − |s| = ‖x‖ − |s|, so preimages of bounded sets are bounded, and preimages of compact sets are closed and bounded, hence compact. By SimonGMT affinePullbackForm_isTestForm (L := J, b := s·e₀), ρ(x) := (ω(s·e₀ + Jx)).compContinuousLinearMap J is C^∞ with compact support, i.e. ρ ∈ TestFormOn univ k, and ρ(x)(v) = ω(ι(s, x))(J ∘ v).
6. Part (c). Fix β, θ as in (c), x ∈ ℝ^N and v : Fin (k + 1) → ℝ^N. Put w := J ∘ v and W := Fin.cons e₀ w : Fin (k + 2) → ℝ^{N+1}. Let g(t, x') := Φ_k(β(ι(t, x'))) (C^∞ by step 4's argument). By the hypothesis on θ, the evaluation identity of step 4 and ContinuousAlternatingMap.ext, θ(x') = ∫_0^1 g(t, x') dt for every x'.
 (c1) For each t, by extDeriv_apply (β is differentiable): dβ(ι(t, x))(W) = Σ_{i : Fin (k+2)} (−1)^i · D[y ↦ β(y)(i.removeNth W)](ι(t, x))(W i).
 (c2) The term i = 0: removeNth 0 W = Fin.tail W = w (Fin.removeNth_zero, Fin.tail_cons) and W 0 = e₀; by the chain rule along t ↦ ι(t, x) it equals φ'(t) for φ(t) := β(ι(t, x))(w), a C^1 function. By the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt), ∫_0^1 φ'(t) dt = β(ι(1, x))(w) − β(ι(0, x))(w).
 (c3) The term i = j.succ (j : Fin (k + 1)): W (j.succ) = w j = J(v j), and removeNth j.succ W = Fin.cons e₀ (removeNth j w) = Fin.cons e₀ (J ∘ removeNth j v) (both sides agree at 0 and at every successor index, since Fin.removeNth p i = p ∘ i.succAbove, j.succ.succAbove 0 = 0 and j.succ.succAbove l.succ = (j.succAbove l).succ). By the chain rule along x' ↦ ι(t, x') (derivative J), with u := removeNth j v: D[y ↦ β(y)(Fin.cons e₀ (J ∘ u))](ι(t, x))(J v_j) = D[x' ↦ β(ι(t, x'))(Fin.cons e₀ (J ∘ u))](x)(v_j) = D[x' ↦ g(t, x')(u)](x)(v_j).
 (c4) By step 3 (derivative of a parametric integral) composed with the evaluation map at u (continuous linear), D[x' ↦ θ(x')(u)](x) = ∫_0^1 D[x' ↦ g(t, x')(u)](x) dt for every u. By extDeriv_apply for the smooth form θ, dθ(x)(v) = Σ_{j : Fin (k+1)} (−1)^j D[x' ↦ θ(x')(removeNth j v)](x)(v_j) = ∫_0^1 Σ_j (−1)^j D[x' ↦ g(t, x')(removeNth j v)](x)(v_j) dt.
 (c5) Every term in (c1) is continuous in t (β is C^∞), hence interval integrable. Integrating (c1) over [0, 1], using (c2), (c3), (c4) and (−1)^{j.succ} = −(−1)^j: ∫_0^1 dβ(ι(t, x))(W) dt = β(ι(1, x))(w) − β(ι(0, x))(w) − dθ(x)(v). This is (c).
7. Part (d). For β ∈ 𝒟^0(ℝ^{N+1}), x and v : Fin 0 → ℝ^N: by extDeriv_apply with n = 0 the only index is 0, removeNth 0 (Fin.cons e₀ (J ∘ v)) = J ∘ v (both are the empty tuple), so dβ(ι(t, x))(Fin.cons e₀ (J ∘ v)) = D[y ↦ β(y)(J ∘ v)](ι(t, x))(e₀) = d/dt[β(ι(t, x))(J ∘ v)]. The fundamental theorem of calculus gives (d).
8. Part (e). Let κ : Λ^k(ℝ^N)* → EuclideanSpace ℝ (Fin k → Fin N), κ(γ) I := if StrictMono I then γ(fun i ↦ EuclideanSpace.basisFun (Fin N) ℝ (I i)) else 0; κ is continuous linear. By EuclideanSpace.norm_eq and (if p then a else 0)^2 = (if p then a^2 else 0), ‖κ(γ)‖ = covectorEuclideanNorm γ for every γ. t ↦ κ(f(t)) is continuous, hence interval integrable. For each I, using the hypothesis with v := (e_{I i})_i and that the coordinate projection is continuous linear (so it commutes with the interval integral): κ(α) I = [StrictMono I]·∫_0^1 f(t)(e_I) dt = ∫_0^1 κ(f(t)) I dt = (∫_0^1 κ(f(t)) dt) I. Hence κ(α) = ∫_0^1 κ(f(t)) dt, and by intervalIntegral.norm_integral_le_of_norm_le_const (for t ∈ Ι 0 1 ⊆ [0, 1], ‖κ(f(t))‖ = |f(t)| ≤ c): |α| = ‖κ(α)‖ ≤ c·|1 − 0| = c. □

## Key steps

1. J is a linear isometric embedding, ι(t, x) = t·e₀ + Jx, tail(ι(t, x)) = x; the contraction Φ(γ) = (γ.curryLeft e₀) ∘ J is continuous linear with Φ(γ)(v) = γ(e₀, Jv).
2. Parametric integrals x ↦ ∫_0^1 h(t, x) dt of C^∞ h are C^∞ with derivative ∫_0^1 D_x h dt (dominated differentiation under the interval integral, induction on the order).
3. (a) η(x) := ∫_0^1 Φ(ω(ι(t, x))) dt is C^∞, satisfies the evaluation formula, and vanishes off the compact set tail(tsupport ω ∩ {y_0 ∈ [0, 1]}).
4. (b) ρ is the affine pull-back of ω by the proper map x ↦ s·e₀ + Jx (SimonGMT affinePullbackForm_isTestForm).
5. (c) Expand dβ(ι(t, x))(e₀, Jv) by extDeriv_apply: the 0-th term is ∂_t[β(ι(t, x))(Jv)], the others are −d_x of the slice integrand; integrate (FTC, differentiation under the integral) to get S_{dβ} = i_1^#β − i_0^#β − dθ.
6. (d) In degree 0 only the ∂_t term occurs; integrate by the FTC.
7. (e) The coefficient map κ is continuous linear with ‖κ(γ)‖ = |γ|; κ(α) = ∫_0^1 κ(f(t)) dt, so |α| ≤ ∫_0^1 |f(t)| dt ≤ c.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as recorded in manifest.json)`
- `rg -n cmcdt_lpo local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'IsLipschitzPushforward|LipschitzPushforwardIntegerMultiplicity' local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n 'theorem extDeriv_pullback|theorem extDeriv_apply' mathlib/Mathlib (Analysis/Calculus/DifferentialForm/Basic.lean:198, :259)`
- `rg -n 'theorem exists_contDiff_tsupport_subset|theorem IsOpen.exists_contDiff_support_eq|theorem HasCompactSupport.contDiff_convolution_left|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem norm_integral_le_of_norm_le_const|theorem norm_fderiv_le_of_lipschitz|def curryLeftLI|theorem curryLeft_apply_apply|theorem integral_eq_sub_of_hasDerivAt|theorem integral_pos_iff_support_of_nonneg|def smoothTransition' mathlib/Mathlib -g '*.lean'`
- `rg -n compContinuousLinearMap mathlib/Mathlib/Analysis/Calculus/ContDiff mathlib/Mathlib/Analysis/Normed/Module/Alternating mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean -g '*.lean'`
- `sed -n 200,260p mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean (interval version hasFDerivAt_integral_of_dominated_of_fderiv_le'')`
- `sed -n 1,140p mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,AffineCurrentPushforward}.lean`
- `lake env lean /tmp/ops-decomp-k7q2/Avail.lean, Avail2.lean, Avail3.lean, Avail4.lean (#check availability of every cited lemma in the frozen import closure of GMT.Ch07.Submission)`
- `lake env lean /tmp/ops-decomp-k7q2/Children.lean (all eight child types elaborate; sorry-free assembly Submission.lpo_assembly_check of the exact selected frozen type; #print axioms)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields and of the selected node's depth and dependencies`
- `grep of /runtime/flows/*/_recursive_lean/inherited.py and runtime.py _overlay_accepted_children (ancestor dependency names cited in a child proof become inherited prerequisites)`
- `sed -n 350,530p book/chapter-06.txt (Simon 6.2.17-2.29: product with [[0,1]], push-forward 2.23-2.24, homotopy formula 2.25-2.27, Lemmas 2.28-2.29)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-3968ae1944/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ops-decomp-k7q2/Children.lean`
- `/tmp/ops-decomp-k7q2/Avail.lean`
- `/tmp/ops-decomp-k7q2/Avail2.lean`
- `/tmp/ops-decomp-k7q2/Avail3.lean`
- `/tmp/ops-decomp-k7q2/Avail4.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Submission.lean. Its only Lipschitz push-forward material is the unsolved Ch06 specification (IsLipschitzPushforward, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). That specification is written over another Euclidean type and cannot be imported into Ch07, so no proof can be reused. Every Mathlib tool the child proofs cite is in the frozen import closure: extDeriv_apply, extDeriv_pullback, Filter.EventuallyEq.extDeriv_eq, curryLeftLI, curryLeft_apply_apply, exists_contDiff_tsupport_subset, IsOpen.exists_contDiff_support_eq, Real.smoothTransition, ContDiffBump with hasContDiffBump_of_innerProductSpace, HasCompactSupport.contDiff_convolution_left, hasFDerivAt_integral_of_dominated_of_fderiv_le'', intervalIntegral.integral_eq_sub_of_hasDerivAt, norm_integral_le_of_norm_le_const (Bochner and interval), norm_fderiv_le_of_lipschitz, integral_pos_iff_support_of_nonneg and LinearMap.exists_leftInverse_of_injective. ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le, contDiff_parametric_integral_of_contDiff and exists_smooth_zero_one_of_isClosed are not in the closure, and the child proofs do not use them. SimonGMT Chapter 6 provides GeometricCurrentOn, TestFormOn, TestFormOnConverges, massOn and mass, support via zeroRegion, boundary and boundary_boundary, tsupport_exteriorDerivative_subset, exteriorDerivative_apply and affinePullbackForm_isTestForm. No DAG node or snapshot declaration uses the prefix cmcdt_lpo_. All eight child types elaborate after import GMT.Ch07.Submission. The assembly of the exact selected frozen type from the pushforward, cylinder and homotopy child types and the covector-bounds type compiles without sorry, with axioms propext, Classical.choice and Quot.sound. Simon 6.2.25-2.29 in book/chapter-06.txt matches the decomposition: the homotopy formula, the mass estimate 2.27, the smooth estimate in the proof of 2.28, and the mollifier limit of 2.29.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
