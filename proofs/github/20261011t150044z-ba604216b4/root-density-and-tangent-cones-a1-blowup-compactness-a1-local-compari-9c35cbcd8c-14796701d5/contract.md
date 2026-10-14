<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.closure_cycles-a1 -->

## Theorem `Submission.dtc_bc_lc_fd_bim_closure_cycles`

Let P, n ∈ ℕ with n < P. Let T_j (j ∈ ℕ) and T be currents in 𝒟_n(ℝ^P) (GeometricCurrentOn univ n) such that every T_j is integer multiplicity (IsIntegerMultiplicity), ∂T_j = 0 for every j (contract BoundaryVanishes; vacuous for n = 0), sup_j M(T_j) < ∞ (M = mass = M_{ℝ^P}), and T_j ⇀ T in ℝ^P (WeaklyConvergesOn). Then T is integer multiplicity.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.closure_cycles-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6358

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_fd_bim_closure_cycles`

```lean
∀ (P n : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (T : GeometricCurrentOn (univ : Set (Euclid P)) n), n < P → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ j, BoundaryVanishes (Ts j)) → ⨆ j, (Ts j).mass < ∞ → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.closure_cycles-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Theorem 8.2 and its printed proof (chapter-06.txt lines 2303–2473, printed pp. 176–179), in the case ∂T_j = 0 singled out by Remark 6.4 (lines 1999–2001) and Remark 8.3(2), with U = ℝ^P. This is the result cited in step 4 of the parent proof, where it is applied to the cycles ∂Q_k.
Book results used:
- Ch. 1: 3.3 (density comparison, chapter-01.txt line 602); 3.12 with Remark 3.11(3) (Besicovitch covering, lines 773–858); 4.4 (Urysohn) and 4.16 (compactness of Radon measures, line 1750).
- Ch. 2: 2.6 (BV compactness, chapter-02.txt line 598).
- Ch. 6: 2.7–2.9 (T = ξ_T μ_T and T⌞A, lines 271–293); 2.14 (lower semicontinuity of M_W); 2.23–2.24 (push-forward); 2.26–2.27 and 2.30–2.31 (cone and its mass bound, lines 452–545); 2.35 (top-dimensional currents with locally finite boundary mass are BV functions, lines 606–639); 3.2(3) and 3.9 (mass and Lipschitz push-forward of IM currents, lines 755–862); 4.4–4.5 and 4.6–4.9 (slices, lines 1223–1374); 5.3 and 6.1 (isoperimetric theorem, with the support bound of its proof, lines 1461–1490 and 1939–1961); 8.1 (Rectifiability Theorem, lines 2155–2296), with the blow-up identities (11)–(13) of its proof.
Sibling used: im_calculus (cmc_imRep_locality_restrict_sub), parts (b) (restriction of an IM current to a Borel set) and (d) (orientation bound).
Departure. The T_j are cycles with sup_j M(T_j) < ∞, so the printed reductions to spt T_j ⊆ K and to ∂T = 0 (Remark 8.3(1)) are not needed. Every step below is local or uses only the global mass bound.
Errata and completions:
- (E1) The isoperimetric fillings in (4) must lie in balls of radius comparable to the balls they fill. The proof of 6.1 via 5.3 gives this support bound. It supplies the radius factor in the cone estimate after (5); the OCR prints '|(S_j − T⌞B_j)(ω)| ≤ cM(S_j − T⌞B_j)|dω|' without it.
- (E2) The constant in (4) is c·γ^{1/(n−1)}; the OCR drops the power.
- (E3) The covering result cited as '??(2) of Ch. 1' is the Besicovitch covering lemma 3.12, in the form of Remark 3.11(3).
- (E4) Footnote 5 (n = 1): an IM 0-current of mass < 1 is zero, so S_r := 0.
- (E5) The selection after (7) ('justified by 4.5(1) and a selection argument') is carried out in full in steps 7–8. The uniform rescaled mass bounds come from a weak limit μ of the mass measures μ_{T_j} and from Θ^{*n}(μ, x) < ∞ at H^n-a.e. x (Ch. 1, 3.3). Bounds for T alone would not do, since weak convergence permits cancellation. The truncation level δ is chosen so that a weak limit ν of the mass measures of the rescaled approximants does not charge {d = δ}, and the convergence of the truncated currents is then proved (step 8(h)).
Notation:
- IM = integer multiplicity; M = mass; M_W = mass in the open set W; ‖ω‖ := sup_x|ω(x)| (Euclidean coefficient norm), finite for test forms.
- (ME) Mass estimate. If spt ω ⊆ W with W open, then |X(ω)| ≤ ‖ω‖·M_W(X). Apply the definition of M_W to ±ω/‖ω‖; if ‖ω‖ = 0 then ω = 0.
- Mass measures (2.7–2.9). If M_W(X) < ∞ for every bounded open W, μ_X is the Radon measure with μ_X(W) = M_W(X) for open W, and X(ω) = ∫⟨ω, ξ_X⟩dμ_X with |ξ_X| = 1 μ_X-a.e. For Borel A, X⌞A(ω) := ∫_A⟨ω, ξ_X⟩dμ_X. So |X⌞A(ω)| ≤ ‖ω‖μ_X(A ∩ spt ω) and μ_{X⌞A} = μ_X⌞A. For IM X = τ(M, θ, ξ) we have μ_X = θH^n⌞M (3.2(3)), ξ_X = ξ μ_X-a.e. (|ξ(x)(α)| ≤ |α| by im_calculus (d)), and X⌞A is the current represented by (M ∩ A, θ, ξ), which is IM (im_calculus (b)).
- (W) Let λ_i → λ weakly as Radon measures, i.e. ∫f dλ_i → ∫f dλ for f ∈ C_c(ℝ^P). Then limsup_iλ_i(K) ≤ λ(K) for compact K, and λ(V) ≤ liminf_iλ_i(V) for open V. Proof: for compact K ⊆ V open take f ∈ C_c(V; [0, 1]) with f = 1 on K (Ch. 1, 4.4). Then λ_i(K) ≤ ∫f dλ_i → ∫f dλ ≤ λ(V); let V ↓ K (outer regularity). Also λ_i(V) ≥ ∫f dλ_i → ∫f dλ ≥ λ(K); let K ↑ V (inner regularity).
- ω_n := L^n(B^n_1); Θ^{*n}(λ, x) := limsup_{ρ↓0}λ(B_ρ(x))/(ω_nρ^n); η_{x,λ}(y) := λ^{−1}(y − x).
We prove by induction on n the statement CL(n): for every P > n, every sequence of IM T_j ∈ 𝒟_n(ℝ^P) with ∂T_j = 0 (if n ≥ 1), sup_jM(T_j) < ∞ and T_j ⇀ T has an IM limit T. Passing to a subsequence changes neither the hypotheses nor the conclusion; we do so freely.

1. (n = 0.)
 (a) An IM 0-current X of finite mass has finite carrier, because H⁰ is counting measure, θ ≥ 1 and M(X) = Σθ (3.2(3)). So X = Σ_{i=1}^{N}ε_iδ_{x_i}, with points listed with multiplicity, ε_i = ±1 and N = M(X).
 (b) Let Λ := sup_jM(T_j) and T_j = Σ_{i=1}^{N_j}ε_{j,i}δ_{x_{j,i}} with N_j ≤ Λ. Pass to a subsequence with N_j = N and ε_{j,i} = ε_i for all j, and such that for each i either x_{j,i} → y_i or |x_{j,i}| → ∞. Let I be the set of i of the first kind.
 (c) For a smooth compactly supported function a, T(a) = lim_jΣ_iε_ia(x_{j,i}) = Σ_{i∈I}ε_ia(y_i). So T = Σ_ym(y)δ_y with m(y) := Σ_{i∈I, y_i = y}ε_i ∈ ℤ.
 (d) With F := {m ≠ 0} (finite), T = τ(F, |m|, sign m). F is Borel and countably 0-rectifiable. The multiplicity is a positive integer on F and locally integrable. At each point of F the approximate tangent space is {0}, since the blow-ups of F converge to the single point 0; the orientation is ±1. So T is IM.
2. (Inductive step: set-up.) Let 1 ≤ n < P and assume CL(n − 1); note n − 1 < P. Let T_j, T be as in CL(n) and Λ := sup_jM(T_j) < ∞.
 (a) By 2.14 (SimonGMT WeaklyConvergesOn.massOn_le_liminf), M(T) ≤ liminf_jM(T_j) ≤ Λ. Also ∂T(η) = T(dη) = lim_jT_j(dη) = 0. So T is a cycle of finite mass, T = ξ_Tμ_T and μ_T(ℝ^P) ≤ Λ.
 (b) μ_j := μ_{T_j} = θ_jH^n⌞M_j satisfies μ_j(ℝ^P) = M(T_j) ≤ Λ. By Ch. 1, 4.16, after passing to a subsequence, μ_j → μ weakly for a Radon measure μ. By (W) with V = ℝ^P, μ(ℝ^P) ≤ Λ.
 (c) μ_T ≤ μ. Let K be compact, r > 0 and V := {y : dist(y, K) < r}. By 2.14 and (W), μ_T(K) ≤ μ_T(V) = M_V(T) ≤ liminf_jM_V(T_j) = liminf_jμ_j(V) ≤ limsup_jμ_j(V̄) ≤ μ(V̄). Letting r ↓ 0 gives μ_T(K) ≤ μ(K). By inner regularity, μ_T(A) ≤ μ(A) for every Borel A.
3. (Slices of T are IM; printed (1)–(2).) Fix ξ₀ ∈ ℝ^P, f := |· − ξ₀| (Lip f = 1) and the nondecreasing function F(r) := μ_T(B_r(ξ₀)).
 (a) Fix j. T_j is IM with ∂T_j = 0, so by 4.4–4.5, for a.e. r > 0 the slice ⟨T_j, f, r⟩ is IM and equals ∂(T_j⌞B_r(ξ₀)) (4.5(2)). Moreover ∫_0^∞M(⟨T_j, f, r⟩)dr ≤ M(T_j) ≤ Λ (4.5(1)). As there are countably many j, there is a null set N₁ ⊂ (0, ∞) off which this holds for every j. By Fatou (the functions r ↦ M(⟨T_j, f, r⟩) are L¹-measurable, being the coarea integrands of 4.1 and 4.5(1)), ∫_0^∞liminf_jM(∂(T_j⌞B_r(ξ₀)))dr ≤ Λ, so liminf_jM(∂(T_j⌞B_r(ξ₀))) < ∞ off a null set N₂.
 (b) The spheres ∂B_r(ξ₀), r > 0, are pairwise disjoint and μ is finite. So μ(∂B_r(ξ₀)) = 0 for r off a countable set N₃, and then μ_T(∂B_r(ξ₀)) = 0 by 2(c).
 (c) Fix r ∉ N₁ ∪ N₂ ∪ N₃ and a subsequence (j′) with sup_{j′}M(∂(T_{j′}⌞B_r(ξ₀))) < ∞. Claim: T_{j′}⌞B_r(ξ₀) ⇀ T⌞B_r(ξ₀). Fix ω and s ∈ (0, r). Take χ ∈ C_c^∞(B_r(ξ₀); [0, 1]) with χ = 1 on B̄_{r−s}(ξ₀), and put A_s := B̄_r(ξ₀) ∖ B_{r−s}(ξ₀) (compact). Then T_j⌞B_r(ξ₀)(ω) − T_j(χω) = ∫_{B_r(ξ₀)}(1 − χ)⟨ω, ξ_{T_j}⟩dμ_j, so |T_j⌞B_r(ξ₀)(ω) − T_j(χω)| ≤ ‖ω‖μ_j(A_s). Likewise |T⌞B_r(ξ₀)(ω) − T(χω)| ≤ ‖ω‖μ_T(A_s) ≤ ‖ω‖μ(A_s). Since T_j(χω) → T(χω) and limsup_jμ_j(A_s) ≤ μ(A_s) by (W), limsup_{j′}|T_{j′}⌞B_r(ξ₀)(ω) − T⌞B_r(ξ₀)(ω)| ≤ 2‖ω‖μ(A_s). As s ↓ 0, A_s decreases to ∂B_r(ξ₀), so μ(A_s) → μ(∂B_r(ξ₀)) = 0.
 (d) Hence ∂(T_{j′}⌞B_r(ξ₀)) ⇀ ∂(T⌞B_r(ξ₀)) (evaluate at dη). These are IM (n − 1)-currents in ℝ^P by (a), cycles (∂∂ = 0; vacuous if n = 1), of bounded mass. By CL(n − 1), Z_r := ∂(T⌞B_r(ξ₀)) is IM.
 (e) By 4.9 (∂T = 0, Lip f = 1), M(Z_r) ≤ liminf_{h↓0}h^{−1}μ_T({r − h < f < r}). This is ≤ F′(r) wherever F is differentiable at r, since μ_T({r − h < f < r}) ≤ F(r) − F(r − h). By 4.8, spt Z_r ⊆ ∂B_r(ξ₀).
 Conclusion (printed (1), (2)): for every ξ₀ and a.e. r > 0, μ_T(∂B_r(ξ₀)) = 0 and Z_r = ∂(T⌞B_r(ξ₀)) is an IM cycle supported in ∂B_r(ξ₀), with M(Z_r) ≤ F′(r) wherever F′(r) exists.
4. (Fillings of small mass; printed (3)–(4).)
 (a) Constants. Let n ≥ 2 and let C₅ be the constant of 5.3 for (n − 1)-currents in ℝ^P. Let Z be an IM (n − 1)-cycle with compact support, Z ≠ 0. Apply 5.3 to Z with ε := (2C₅M(Z))^{1/(n−1)}, as in the proof of 6.1. The polyhedral part of 5.3 (Simon's P) vanishes, since its mass is N(ε)ε^{n−1} ≤ C₅M(Z) < ε^{n−1} with N(ε) a nonnegative integer; and Simon's S vanishes, since ∂Z = 0. So Z = ∂S′ for an IM S′ (Simon's R) with M(S′) ≤ C₅εM(Z). By the support bound of 5.3, spt S′ ⊆ {x : dist(x, spt Z) < 2√P·ε} (E1). Hence there is c₁ ≥ 1, namely c₁ := max{1, (C₅(2C₅)^{1/(n−1)})^{(n−1)/n}, 2√P(2C₅)^{1/(n−1)}}, with M(S′)^{(n−1)/n} ≤ c₁M(Z) and spt S′ ⊆ {x : dist(x, spt Z) ≤ c₁M(Z)^{1/(n−1)}}; for Z = 0 take S′ = 0. (This is the accepted DAG lemma cbr_isoperimetric_filling, there conditional on the deformation theorem.) Let c₂ := (2nc₁)^{n/(n−1)}ω_n^{1/(n−1)} and fix γ ∈ (0, 1/4) with c₂γ^{1/(n−1)} ≤ 1/2. For n = 1 take any γ ∈ (0, 1/4).
 (b) Good radius. Let Θ^{*n}(μ_T, ξ₀) < γ. Then F(δ) < γω_nδ^n for all small δ > 0. For such δ, (1/δ)∫_0^δ(F^{1/n})′(r)dr ≤ δ^{−1}F(δ)^{1/n} < (γω_n)^{1/n}, because F^{1/n} is nondecreasing (∫_0^δg′ ≤ g(δ) − g(0+) for nondecreasing g). So the set of r ∈ (0, δ) with (F^{1/n})′(r) ≤ 2(γω_n)^{1/n} has positive measure. Choose such an r to which the conclusion of step 3 applies and at which F and F^{1/n} are differentiable. Then M(Z_r) ≤ F′(r) = nF(r)^{(n−1)/n}(F^{1/n})′(r) ≤ 2n(γω_n)^{1/n}F(r)^{(n−1)/n}.
 (c) If n ≥ 2, let S_r be the filling of Z_r from (a). Then M(S_r) ≤ (c₁M(Z_r))^{n/(n−1)} ≤ c₂γ^{1/(n−1)}F(r) ≤ μ_T(B_r(ξ₀))/2 (printed (4), (E2)). Since F(r) ≤ F(δ) < γω_nδ^n, M(Z_r) < 2nγω_nδ^{n−1}, so M(Z_r)^{1/(n−1)} < (2nγω_n)^{1/(n−1)}δ. Hence spt S_r ⊆ B̄_{c₃δ}(ξ₀) with c₃ := 1 + c₁(2nγω_n)^{1/(n−1)}.
 (d) If n = 1, M(Z_r) ≤ 2γω_1 = 4γ < 1 and Z_r is an IM 0-current, so Z_r = 0 by 1(a). Put S_r := 0 and c₃ := 1 (E4).
 In both cases ∂S_r = ∂(T⌞B_r(ξ₀)), M(S_r) ≤ μ_T(B_r(ξ₀))/2, and S_r − T⌞B_r(ξ₀) is a cycle supported in B̄_{c₃δ}(ξ₀).
5. (Lower density bound; printed (4)–(6).) A_γ := {x : Θ^{*n}(μ_T, x) < γ} is Borel: ρ ↦ μ_T(B_ρ(x)) is left-continuous, so the limsup may be taken over rational ρ, and x ↦ μ_T(B_ρ(x)) is lower semicontinuous. Let C be a compact subset of A_γ. We show μ_T(C) = 0.
 (a) Covering. Fix ε > 0 and W_ε := {dist(·, C) < ε}. Step 4 with δ < ε/c₃ gives, at each point ξ₀ ∈ C, arbitrarily small admissible closed balls B̄_r(ξ₀) ⊆ W_ε with μ_T(∂B_r(ξ₀)) = 0, so that T⌞B̄_r(ξ₀) = T⌞B_r(ξ₀). By the Besicovitch covering lemma (E3) there are pairwise disjoint such balls B_i with μ_T(C ∖ ⋃_iB_i) = 0. They come with IM S_i such that ∂S_i = ∂(T⌞B_i), M(S_i) ≤ μ_T(B_i)/2, and X_i := S_i − T⌞B_i is a cycle supported in a closed ball of radius < ε (printed (4), (5)).
 (b) Cone estimate (2.27, 2.30–2.31). A cycle X of finite mass supported in B̄_ρ(a) satisfies X = ∂(a ⨯ X) and M(a ⨯ X) ≤ ρM(X) (2.27 with f ≡ a, g = id). Hence |X(ω)| ≤ ρM(X)‖dω‖ (E1). So |X_i(ω)| ≤ (3/2)εμ_T(B_i)‖dω‖.
 (c) Σ_iS_i and Σ_iT⌞B_i converge in mass, because Σ_iμ_T(B_i) ≤ μ_T(W_ε) < ∞. So T_ε := T + Σ_iX_i = T⌞(ℝ^P ∖ ⋃_iB_i) + Σ_iS_i is a current, and |T_ε(ω) − T(ω)| ≤ (3/2)εM(T)‖dω‖. Hence T_ε ⇀ T as ε ↓ 0 (printed (6)).
 (d) Fix ε₀ > 0 and W := W_{ε₀}. For ε < ε₀ every B_i lies in W, so M_W(T_ε) ≤ μ_T(W ∖ ⋃_iB_i) + Σ_iM(S_i) ≤ μ_T(W ∖ C) + μ_T(W)/2. By lower semicontinuity of M_W along ε = 1/k, μ_T(W) ≤ μ_T(W ∖ C) + μ_T(W)/2. So μ_T(W_{ε₀}) ≤ 2μ_T(W_{ε₀} ∖ C) → 0 as ε₀ ↓ 0, since μ_T is finite and ⋂_{ε₀}(W_{ε₀} ∖ C) = ∅. Hence μ_T(C) = 0.
 (e) By inner regularity μ_T(A_γ) = 0, i.e. Θ^{*n}(μ_T, x) ≥ γ for μ_T-a.e. x.
6. (Rectifiability; 8.1.) M(T) + M(∂T) < ∞ and Θ^{*n}(μ_T, ·) > 0 μ_T-a.e. So by 8.1, T = τ(M, θ, ξ) with:
 - M countably n-rectifiable and H^n-measurable, H^n⌞M σ-finite;
 - θ > 0 real valued and locally H^n-integrable on M, so μ_T = θH^n⌞M;
 - ξ(x) orienting T_xM for H^n-a.e. x ∈ M.
 Here (M, θ, ξ) is the representation constructed in the proof of 8.1, so its identities (11)–(13) apply in step 7. Moreover H^n(M) < ∞: by step 5, M ∖ {Θ^{*n}(μ_T, ·) ≥ γ} is μ_T-null, hence H^n-null (μ_T = θH^n⌞M with θ > 0 on M); and γH^n(M ∩ {Θ^{*n}(μ_T, ·) ≥ γ}) ≤ μ_T(ℝ^P) ≤ Λ by Ch. 1, 3.3. So H^n(M) ≤ Λ/γ, and all blow-up integrals of M below are finite.
 It remains to show θ(x) ∈ ℤ for H^n-a.e. x ∈ M.
7. (Good points; printed (7).)
 - By (11)–(13) of the proof of 8.1, for H^n-a.e. x ∈ M: η_{x,λ#}T(ω) → C_x(ω) := θ(x)∫_{T_xM}⟨ω(z), ξ(x)⟩dH^n(z) as λ ↓ 0, for every ω ∈ 𝒟^n(ℝ^P). Here T_xM is the approximate tangent space and ξ(x) orients it.
 - Finite upper density of μ. By Ch. 1, 3.3 (μ Borel regular, A₁ := {Θ^{*n}(μ, ·) = ∞}, A₂ := ℝ^P, any t > 0), tH^n(A₁) ≤ μ(ℝ^P) ≤ Λ. So H^n({Θ^{*n}(μ, ·) = ∞}) = 0.
 Let G be the set of x ∈ M such that θ(x) ∈ (0, ∞); the approximate tangent space T_xM exists, is n-dimensional and is oriented by ξ(x); the blow-up convergence above holds; and Θ^{*n}(μ, x) < ∞. Then H^n(M ∖ G) = 0.
8. (Rescaled approximants; printed (7)–(9).) Fix x ∈ G. Choose orthonormal coordinates of ℝ^P with x = 0 and T_xM = ℝ^n × {0} =: L; since ξ(x) = ±e₁∧⋯∧e_n by step 7, replacing e₁ by −e₁ if necessary we may assume ξ(x) = e₁∧⋯∧e_n. A rigid motion maps IM currents to IM currents, commutes with ∂, with η_{·,λ#} and with weak convergence, and preserves mass measures; this is the printed 'without loss of generality'. Then C := C_x = θ(x)[[L]], i.e. C(ω) = θ(x)∫_L⟨ω, e₁∧⋯∧e_n⟩dH^n. Let p(y) := (y¹, …, yⁿ), q(y) := (y^{n+1}, …, y^P), d(y) := |q(y)| = dist(y, L), V := B_2(0), Ω := {|p| < 1} = B^n_1(0) × ℝ^{P−n} and Ω′ := Ω ∩ {d < 1}. Ω′ is open and Ω′ ⊆ V, since |y|² = |p(y)|² + d(y)² < 2.
 (a) Uniform bound for the approximants. Since Θ^{*n}(μ, 0) < ∞, there are Λ₀ ∈ [1, ∞) and ρ₀ ∈ (0, 1] with μ(B̄_ρ(0)) ≤ Λ₀ρ^n for 0 < ρ ≤ ρ₀. Let λ ∈ (0, ρ₀/2]. B̄_{2λ}(0) is compact, so by (W) limsup_jμ_j(B̄_{2λ}(0)) ≤ μ(B̄_{2λ}(0)) ≤ 2^nΛ₀λ^n. As 2^nΛ₀λ^n < 2^{n+1}Λ₀λ^n, there is J(λ) with μ_j(B̄_{2λ}(0)) ≤ 2^{n+1}Λ₀λ^n for all j ≥ J(λ).
 (b) Rescaling. Put X_{λ,j} := η_{0,λ#}T_j and Y_λ := η_{0,λ#}T, i.e. X_{λ,j}(ω) = T_j(η_{0,λ}^#ω) (2.23). If T_j = τ(M_j, θ_j, ξ_j), then X_{λ,j} = τ(λ^{−1}M_j, θ_j(λ·), ξ_j(λ·)). This is 3.9 for the injective linear map η_{0,λ}, which maps the orienting n-vector ξ_j(y) to λ^{−n}ξ_j(y), with normalization ξ_j(y). So X_{λ,j} is IM, ∂X_{λ,j} = η_{0,λ#}∂T_j = 0 (2.24(1)), and μ_{X_{λ,j}}(A) = λ^{−n}μ_j(λA) (H^n(λ^{−1}E) = λ^{−n}H^n(E)). Thus, for j ≥ J(λ), μ_{X_{λ,j}}(B̄_2(0)) = λ^{−n}μ_j(B̄_{2λ}(0)) ≤ 2^{n+1}Λ₀ =: Λ₁; in particular M_V(X_{λ,j}) ≤ Λ₁. For fixed λ, X_{λ,j} ⇀ Y_λ as j → ∞ (apply T_j ⇀ T to η_{0,λ}^#ω), and Y_λ ⇀ C as λ ↓ 0 by step 7.
 (c) A countable test family. Let 𝒟_V := {ω ∈ 𝒟^n(ℝ^P) : spt ω ⊆ V}. For ω, ω′ ∈ 𝒟_V, ‖ω − ω′‖ equals the sup-distance of their restrictions to the compact set B̄_2(0). So 𝒟_V with this metric is isometric to a subset of the separable metric space C(B̄_2(0); Λ^n(ℝ^P)), hence separable. Fix a sequence (ω_l)_{l≥1} in 𝒟_V that is ‖·‖-dense in 𝒟_V.
  Test lemma. Let Z_i, Z be currents with M_V(Z_i) ≤ Λ₂ and M_V(Z) ≤ Λ₂, and Z_i(ω_l) → Z(ω_l) for every l. Then Z_i(ω) → Z(ω) for every ω ∈ 𝒟_V. Indeed, for ε > 0 choose l with ‖ω − ω_l‖ < ε. By (ME), |Z_i(ω) − Z(ω)| ≤ |Z_i(ω − ω_l)| + |Z_i(ω_l) − Z(ω_l)| + |Z(ω_l − ω)| ≤ 2Λ₂ε + |Z_i(ω_l) − Z(ω_l)|.
 (d) Diagonal selection. For i = 1, 2, … choose λ_i ∈ (0, min(ρ₀/2, 1/i)] with |Y_{λ_i}(ω_l) − C(ω_l)| < 1/i for l ≤ i. Then choose j_i ≥ J(λ_i) with |X_{λ_i,j_i}(ω_l) − Y_{λ_i}(ω_l)| < 1/i for l ≤ i. Both choices are possible by (b). Put X_i := X_{λ_i,j_i}. Each X_i is an IM cycle with μ_{X_i}(B̄_2(0)) ≤ Λ₁, by (b) and j_i ≥ J(λ_i). This is the uniform rescaled mass bound for the approximants; it comes from μ, not from T. For every l, |X_i(ω_l) − C(ω_l)| < 2/i when i ≥ l. Also M_V(C) = θ(x)ω_n2^n < ∞. So the test lemma, with Λ₂ := max(Λ₁, θ(x)ω_n2^n), gives X_i(ω) → C(ω) for every ω ∈ 𝒟_V.
 (e) Weak limit of the approximants' mass measures. The measures ν_i := μ_{X_i}⌞B̄_2(0) satisfy ν_i(ℝ^P) ≤ Λ₁. By Ch. 1, 4.16, after passing to a subsequence (which preserves (d)), ν_i → ν weakly for a Radon measure ν with ν(ℝ^P) ≤ Λ₁ (by (W)).
 (f) Choice of the truncation level. For each i, X_i is IM with ∂X_i = 0, and d is 1-Lipschitz. By 4.4–4.5, for a.e. t > 0: ⟨X_i, d, t⟩ is IM, is represented by a triple carried by {d = t} (4.4), and equals ∂(X_i⌞{d < t}) (4.5(2)). By 4.5(1) with W = Ω′ and |∇^Md| ≤ 1, ∫_0^∞M_{Ω′}(⟨X_i, d, t⟩)dt ≤ M_{Ω′}(X_i) ≤ μ_{X_i}(B̄_2(0)) ≤ Λ₁. By Fatou (the integrands are L¹-measurable, as in step 3(a)), ∫_0^∞liminf_iM_{Ω′}(⟨X_i, d, t⟩)dt ≤ Λ₁. The sets {d = t}, t > 0, are pairwise disjoint and ν is finite, so ν({d = t}) > 0 for at most countably many t. Hence there is δ ∈ (0, 1) with:
  (f1) for every i, ⟨X_i, d, δ⟩ is IM, carried by {d = δ}, and equal to ∂(X_i⌞{d < δ});
  (f2) liminf_iM_{Ω′}(⟨X_i, d, δ⟩) < ∞;
  (f3) ν({d = δ}) = 0.
  Pass to a subsequence with M_{Ω′}(⟨X_i, d, δ⟩) ≤ L₀ < ∞ for all i; (d), (e), (f1) and (f3) persist.
 (g) Truncations; printed (9). S_i := X_i⌞{d < δ} is IM (im_calculus (b)), and ∂S_i = ⟨X_i, d, δ⟩ by (f1). The representation of ⟨X_i, d, δ⟩ is carried by {d = δ}, and Ω ∩ {d = δ} ⊆ Ω′. So M_Ω(∂S_i) = M_{Ω′}(⟨X_i, d, δ⟩) ≤ L₀. Also M_Ω(S_i) = μ_{X_i}(Ω ∩ {d < δ}) ≤ μ_{X_i}(Ω′) ≤ Λ₁. Thus sup_i(M_Ω(S_i) + M_Ω(∂S_i)) ≤ Λ₁ + L₀.
 (h) Convergence of the truncations. Claim: S_i(ω) → C(ω) for every ω ∈ 𝒟^n(ℝ^P) with spt ω ⊆ Ω. Fix such ω and s ∈ (0, δ/2). Let φ_s ∈ C^∞(ℝ; [0, 1]) with φ_s = 1 on (−∞, δ − s] and φ_s = 0 on [δ, ∞), and χ_s := φ_s∘d. χ_s is C^∞: d is smooth on {d > 0}, and χ_s = 1 on the open neighbourhood {d < δ − s} of {d = 0}. ω_s := χ_sω ∈ 𝒟_V, because spt ω_s ⊆ spt ω ∩ {d ≤ δ}, a compact subset of Ω′ ⊆ V. Since χ_s = 0 on {d ≥ δ} and χ_s = 1 on {d ≤ δ − s},
  S_i(ω) − X_i(ω_s) = ∫_{{d<δ}}(1 − χ_s)⟨ω, ξ_{X_i}⟩dμ_{X_i},
  so |S_i(ω) − X_i(ω_s)| ≤ ‖ω‖μ_{X_i}(K_s), where K_s := spt ω ∩ {δ − s ≤ d ≤ δ} is a compact subset of Ω′ ⊆ B̄_2(0).
  - By (W) for ν_i → ν, limsup_iμ_{X_i}(K_s) = limsup_iν_i(K_s) ≤ ν(K_s).
  - By (d), X_i(ω_s) → C(ω_s). Also C(ω_s) = C(ω), because C is carried by L ⊆ {d = 0}, where χ_s = 1.
  Hence limsup_i|S_i(ω) − C(ω)| ≤ ‖ω‖ν(K_s) ≤ ‖ω‖ν(B̄_2(0) ∩ {δ − s ≤ d ≤ δ}). As s ↓ 0 these sets decrease to B̄_2(0) ∩ {d = δ} and ν is finite, so the bound tends to ‖ω‖ν(B̄_2(0) ∩ {d = δ}) = 0 by (f3). This proves the claim: S_i ⇀ C = θ(x)[[ℝ^n × {0}]] in Ω. The limiting mass measure ν, not the limit current, controls the truncation boundary.
9. (Projection and BV compactness; printed (10).)
 (a) The projected currents. Let δ₁ := (1 + δ)/2 and δ₂ := (3 + δ)/4, so δ < δ₁ < δ₂ < 1. Take φ ∈ C^∞(ℝ; [0, 1]) with φ = 1 on (−∞, δ₁] and φ = 0 on [δ₂, ∞), and let ζ := φ∘d, a C^∞ function equal to 1 on {d ≤ δ₁}. For α ∈ 𝒟^n(B^n_1(0)), ζ·p^#α is C^∞ and spt(ζp^#α) ⊆ spt α × B̄^{P−n}_{δ₂}(0), a compact subset of Ω′. Define Π_i(α) := S_i(ζ·p^#α).
  - Π_i is linear and sequentially continuous on 𝒟^n(B^n_1(0)): if α_k → 0 in 𝒟, then ζp^#α_k → 0 in 𝒟 with supports in a fixed compact set. So Π_i ∈ 𝒟_n(B^n_1(0)).
  - Π_i does not depend on φ: two such cut-offs agree on {d ≤ δ₁} ⊇ {d < δ}, which carries μ_{S_i}.
  - Π_i is Simon's p_#S̃_i (2.23–2.24(2)): p is smooth and proper on {d ≤ δ} ⊇ spt S_i ∩ Ω, since the preimage there of a compact K ⊆ B^n_1(0) is K × B̄^{P−n}_δ(0).
 (b) Masses. p^# maps dx^{i_1}∧⋯∧dx^{i_n} to dy^{i_1}∧⋯∧dy^{i_n}, so |p^#α(y)| = |α(p(y))| for the Euclidean coefficient norms, and 0 ≤ ζ ≤ 1. Hence M_{B^n_1(0)}(Π_i) ≤ M_Ω(S_i) ≤ Λ₁. For β ∈ 𝒟^{n−1}(B^n_1(0)): ∂Π_i(β) = S_i(ζp^#dβ) = S_i(d(ζp^#β)) − S_i(dζ ∧ p^#β) = ∂S_i(ζp^#β). Here d commutes with p^# (1.14), and dζ = φ′(d)·dd vanishes on {d < δ₁} ⊇ {d < δ}, which carries μ_{S_i}. So M_{B^n_1(0)}(∂Π_i) ≤ M_Ω(∂S_i) ≤ L₀.
 (c) Integrality. Π_i is IM in B^n_1(0) by 3.9. Apply it to the IM current S_i restricted to Ω, represented by (M_{S_i} ∩ Ω, θ, ξ), and to the Lipschitz map p : Ω → B^n_1(0), which is proper on spt S_i ∩ Ω. For C¹ maps the push-forward of 3.9 agrees with that of 2.24(2) (remark after 3.10), so it equals Π_i.
 (d) BV representation. By 2.35 (top dimension, U = B^n_1(0), M_W(∂Π_i) < ∞), Π_i(a dx¹∧⋯∧dxⁿ) = ∫aθ_i dL^n for a ∈ C_c^∞(B^n_1(0)), with θ_i ∈ BV_loc(B^n_1(0)), ∫_{B^n_1(0)}|θ_i| = M(Π_i) ≤ Λ₁ and |Dθ_i|(B^n_1(0)) = M(∂Π_i) ≤ L₀. Write Π_i = τ(M′, ϑ′, ξ′). H^n = L^n on ℝ^n, ϑ′ is a positive integer, and ξ′(z) = ±e₁∧⋯∧eₙ for a.e. z ∈ M′ (the only unit n-vectors of ℝ^n). So θ_i = ±ϑ′ on M′ and 0 elsewhere, a.e. Thus θ_i is integer valued a.e., as in the first lines of the proof of 3.14.
 (e) Compactness. sup_i(∫_{B^n_1(0)}|θ_i| + |Dθ_i|(B^n_1(0))) ≤ Λ₁ + L₀. By Ch. 2, 2.6, a subsequence θ_i → θ̃ in L¹_loc(B^n_1(0)), and a further subsequence converges a.e. So θ̃ is integer valued a.e.
 (f) Identification. Let a ∈ C_c^∞(B^n_1(0)) and α := a dx¹∧⋯∧dxⁿ. Since spt(ζp^#α) ⊆ Ω, step 8(h) gives Π_i(α) = S_i(ζp^#α) → C(ζp^#α) = θ(x)∫_Lζ(z)a(p(z))⟨dy¹∧⋯∧dyⁿ, e₁∧⋯∧eₙ⟩dH^n(z) = θ(x)∫_{B^n_1(0)}a dL^n. Here ζ = 1 on L, p|_L is the identity of ℝ^n and H^n⌞L = L^n. Also Π_i(α) = ∫aθ_i → ∫aθ̃. Hence ∫aθ̃ = θ(x)∫a for all such a, so θ̃ = θ(x) a.e. in B^n_1(0). As θ̃ is integer valued a.e. and L^n(B^n_1(0)) > 0, θ(x) ∈ ℤ, and θ(x) ≥ 1 because θ(x) > 0.
10. (Conclusion.) By steps 7–9, θ(x) is a positive integer for every x ∈ G, hence for H^n-a.e. x ∈ M. Choose a Borel set M′ ⊆ G with H^n(M ∖ M′) = 0; this is possible since H^n is Borel regular and H^n⌞M is σ-finite. Shrinking M′ by an H^n-null Borel set, we may assume that θ agrees on M′ with a Borel function and that ξ(x) orients T_xM for every x ∈ M′.
 - mult := θ on M′ and 0 elsewhere is Borel, ℕ-valued and ≥ 1 on M′. It is locally H^n-integrable, since ∫_{M′}θ dH^n ≤ μ_T(ℝ^P) = M(T) < ∞.
 - orient := ξ is a.e. strongly measurable for H^n⌞M′.
 - M′ ⊆ M is countably n-rectifiable. Removing an H^n-null set changes no blow-up integral ∫_{η_{x,r}(·)}f dH^n, so M′ has approximate tangent space T_xM at H^n-a.e. x ∈ M′, oriented by ξ(x).
 Hence (M′, mult, ξ) is an IMRep in ℝ^P, and T(ω) = ∫_Mθ⟨ω, ξ⟩dH^n = ∫_{M′}mult·ξ(ω)dH^n for every ω. So T is IM. This proves CL(n), and by induction the statement. ∎

## Key steps

1. Induction on the degree: CL(0) holds because bounded-mass IM 0-currents are finite signed sums of point masses, and the bounded points converge.
2. Pass to μ_{T_j} → μ (Ch. 1, 4.16); μ_T ≤ μ. Slices ∂(T⌞B_r(ξ₀)) are IM for a.e. r: the slices of the T_j are IM with liminf-bounded mass (4.5, Fatou), μ(∂B_r) = 0 makes the restrictions converge, and CL(n − 1) applies (printed (1)–(2)).
3. Where Θ^{*n}(μ_T, ·) < γ, radii with small (F^{1/n})′ give IM fillings S_r with M(S_r) ≤ μ_T(B_r)/2 in comparable balls (6.1 with the support bound of 5.3); for n = 1 the slice vanishes.
4. Besicovitch covering, the cone estimate and lower semicontinuity give μ_T{Θ^{*n} < γ} = 0; the Rectifiability Theorem 8.1 gives T = τ(M, θ, ξ) with real θ.
5. At H^n-a.e. x ∈ M the blow-ups of T converge to θ(x)[[T_xM]] and Θ^{*n}(μ, x) < ∞ (Ch. 1, 3.3); the latter bounds μ_{η_{x,λ#}T_j}(B̄_2(0)) uniformly for j ≥ J(λ).
6. Diagonal selection on a countable dense family of test forms gives IM cycles X_i ⇀ θ(x)[[T_xM]] with uniform mass bounds. A weak limit ν of their mass measures and Fatou on 4.5(1) give a level δ with IM slices of bounded mass and ν{d = δ} = 0, which proves X_i⌞{d < δ} ⇀ θ(x)[[T_xM]].
7. Projecting to T_xM gives integer-valued BV functions with uniform bounds (3.9, 2.35); BV compactness and identification of the limit force θ(x) ∈ ℤ, and a Borel modification gives an IMRep of T.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); sha256sum snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (both e4148e7f…)`
- `rg -n 'BoundaryRectifiability|FedererFleming|CompactnessTheorem|DeGiorgi|IsoperimetricTheorem|RectifiabilityTheorem' project/GMT -g '*.lean' (only sorry-based contract definitions in GMT/Ch06 and GMT/Ch08, namespaces GMT.Ch06/GMT.Ch08, not importable from GMT.Ch07); rg -n 'closure|De Giorgi|reduced boundary|slice' project/GMT/Ch07 (only topological closure in definitions; no closure, slicing or De Giorgi theorem)`
- `sed -n 321,345p project/GMT/Ch06/Contract.lean (BoundaryRectifiability, FlatConvergenceIffWeakConvergence, RectifiabilityTheorem: formulation reference only)`
- `rg in snapshot mathlib: 'theorem ae_tendsto_average ' (Covering/Differentiation.lean:855), 'theorem ae_tendsto_rnDeriv' (Differentiation.lean:657), 'lintegral_pow_le_pow_lintegral_fderiv' (FunctionalSpaces/SobolevInequality.lean:371), 'ae_eq_zero_of_integral_contDiff_smul_eq_zero' (Distribution/AEEqOfIntegralContDiff.lean:186), 'euclideanHausdorffMeasure_eq_volume' (Geometry/Euclidean/Volume/Measure.lean:187), 'theorem integral_tsum' (Integral/DominatedConvergence.lean:88), 'exists_disjoint_subfamily_covering_enlargement_closedBall' (Covering/Vitali.lean:158), 'theorem exists_dense_seq' (Topology/Bases.lean:364), 'tendsto_inv_nat_nhds_zero' (Topology/Instances/ENNReal/Lemmas.lean:486)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,FormSupNorm,Forms}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn, TestFormOn, boundary_apply, boundary_boundary, exteriorDerivative_sq, massAdmissibleOn, massOn, mass, le_massOn, massOn_le_liminf, covectorEuclideanNorm (no smul/bound lemma), testFormEuclideanSupNorm, HasApproximateTangentSpaceAt (blow-up integral definition); no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem`
- `python3 -I scans of dag.json (1615 nodes): accepted codim1_rdo_dg_* De Giorgi helpers (measure_eq_hausdorff, rectifiable_of_flat_tangent, flat_tangent_density_cone, normal_average_ae, cutoff_estimates, gauss_green_measure, ...) and codim1_rdo_rectifiable_ae_density_one; non-accepted codim1_rdo_de_giorgi_gauss_green, tangent_measure_ae, blowup_halfspace, volume_density_lower, cmc_closure_and_boundary_rectifiability with cbr_* children, dtc_bc_tc_closure, cmc_deformation_theorem; accepted cbr_isoperimetric_filling (conditional on cmc_deformation_theorem); statement of the deformation sibling dtc_bc_lc_fd_deformation; collision check of dtc_bc_lc_fd_bim_* (only in this node's decomposition-v1.json)`
- `cat nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json} (rejected v1 and its required changes)`
- `python3 -I /tmp/bim_v2_scripts/reuse_check.py: git show <commit>:GMT/Ch07/Submission.lean for 3632b24, be5e512, 44ef61f, cfaa429, 8380287, 2af75d6, d1641e8, 3450f10 (whitespace-normalised types identical to dag.json; only sorry = main_theorem; no axiom/opaque); git show <commit>:GMT/Ch07/Contract.lean | sha256sum (all e4148e7f…); comparator-v1.log and isolated-comparator-result.json of the two new reuses ('Your solution is okay!', passed)`
- `git show 3632b24 / be5e512 :GMT/Ch07/Submission.lean | grep helpers cited by the reused proofs (codim1_rdo_dg_flat_tangent_density_cone, codim1_rdo_dg_rectifiable_of_flat_tangent; regcomp_atl_upper_density_zero, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall): all present and accepted; git log --all -S 'dtc_bc_lc_fd_bim_' (no hit)`
- `lake env lean /tmp/bim_v2_check/Challenges.lean (12 targets in comparator challenge form after the gmt-compare.py contract_scope replay: exit 0, 12 sorry warnings only)`
- `lake env lean /tmp/bim_v2_check/AllChecks.lean (stubs; sorry-free bim_* helper lemmas; node_assembly; de_giorgi_from_children; closure_cycles_from_general; #print axioms)`
- `sed book/chapter-06.txt lines 440-660 (2.23-2.37), 725-960 (3.1-3.15), 1150-1420 (4.1-4.11), 1425-1500 (5.1-5.4), 1925-2160 (6.1-8.1), 2160-2296 (8.1 proof), 2290-2473 (8.2-8.3); chapter-01.txt 596-612, 800-830, 1745-1800 (3.3, 3.12, 4.16); chapter-03.txt 551-746 (4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/bim_v2_check/Challenges.lean`
- `/tmp/bim_v2_check/AllChecks.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the workspace, and the snapshot and workspace GMT/Ch07/Contract.lean are byte-identical (sha256 e4148e7f…). The pinned project proves no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem usable from GMT.Ch07. GMT/Ch06 and GMT/Ch08 only state them as sorry-based contract definitions in other namespaces; they served as formulation references. SimonGMT provides currents, boundary, massOn/mass (Euclidean coefficient norm), le_massOn, massOn_le_liminf, support and HasApproximateTangentSpaceAt, but no bound for covectorEuclideanNorm; the needed homogeneity and operator-norm bounds were proved in the scratch check. Snapshot Mathlib supplies the measure-theory tools cited in the child proofs (Besicovitch/Vitali differentiation, GNS inequality, fundamental lemma, μHE = volume, integral_tsum, separability). In the DAG, the De Giorgi parent codim1_rdo_de_giorgi_gauss_green and the closure theorems are not accepted. The accepted codim1_rdo_dg_measure_eq_hausdorff and codim1_rdo_rectifiable_ae_density_one close the rejected de_giorgi step 6: types identical in commits 3632b24 and be5e512, comparators passed, helpers contained. They are reused together with the six v1 reuses. All eight reused types are identical in their accepted commits, those commits' contracts are byte-identical, and they contain no extra sorry or axioms. The four new names are unreserved and the dependencies are acyclic. Lean: all 12 child types elaborate in challenge form. The parent's frozen type is proved from the 12 child stubs plus the deformation sibling, with the inline weak-limit step proved sorry-free (propext, Classical.choice, Quot.sound). de_giorgi's type is assembled from the three reused De Giorgi lemmas, and closure_cycles follows from the cousin dtc_bc_tc_closure's type.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
