import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.AreaLipschitz

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

/-- Simon 6.3.1: `Hⁿ`-a.e. on `M` the orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` of an integer
multiplicity triple is a unit simple `n`-vector (`τ` orthonormal), so every `n`-covector `β`
satisfies `|⟨β, ξ(x)⟩| = |β(τ₁, …, τₙ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖` (operator norm). -/
theorem Submission.dpf_pfc_imrep_orient_abs_apply_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ β : Covector (Euclid P) n, |R.orient x β| ≤ ‖β‖ := by
  intro P n U R
  filter_upwards [R.orients] with x hx β
  -- `ξ(x)` is `±` evaluation at an orthonormal frame `τ`
  obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
  have hβ : |β τ| ≤ ‖β‖ :=
    calc |β τ| = ‖β τ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖β‖ * ∏ i, ‖τ i‖ := β.le_opNorm τ
      _ = ‖β‖ := by rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one]
  rcases hξ with h | h
  · rw [h β]
    exact hβ
  · rw [h β, abs_neg]
    exact hβ

/-- **Pairing bound for `τ(M, θ, ξ)`** (the estimate behind Simon 6.2.24(2)).  If `F` is
`Hⁿ⌞M`-a.e. strongly measurable, vanishes off the compact `C ⊆ U` and `‖F‖ ≤ B`, then
`θ ⟨F, ξ⟩` is `Hⁿ⌞M`-integrable and `|∫_M θ ⟨F, ξ⟩ dHⁿ| ≤ B ∫_{M ∩ C} θ dHⁿ`.  By
`dpf_pfc_imrep_orient_abs_apply_le`, `|θ ⟨F, ξ⟩| ≤ B θ 1_C` a.e., and `θ 1_C` is integrable by
the local integrability of `θ`. -/
theorem Submission.dpf_pfc_imrep_pairing_integrable_abs_le : ∀ (P n : ℕ) (U C : Set (Euclid P)) (R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact C → C ⊆ U → AEStronglyMeasurable F (μHE[n].restrict R.carrier) → (∀ x, x ∉ C → F x = 0) → (∀ x, ‖F x‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x (F x)) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n]| ≤ B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U C R F B hC hCU hF hF0 hFB
  -- Step 1: `C` is measurable; step 2: `θ` is measurable
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
  -- Step 3: `μ.restrict C = Hⁿ⌞(M ∩ C)`
  have hres : (μHE[n].restrict R.carrier).restrict C = μHE[n].restrict (R.carrier ∩ C) := by
    rw [Measure.restrict_restrict hCm, inter_comm]
  -- Step 4: `θ` is integrable on `C`, so `g = B · 1_C θ` is integrable
  have hθC : IntegrableOn (fun x => (R.mult x : ℝ)) C (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hres]
    simpa using (R.locallyIntegrable_mult C hC hCU).lt_top
  have hg : Integrable (fun x => B * C.indicator (fun y => (R.mult y : ℝ)) x)
      (μHE[n].restrict R.carrier) :=
    ((integrable_indicator_iff hCm).2 hθC).const_mul B
  -- Step 5: `h = θ · ξ(F)` is a.e. strongly measurable
  have hh : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (F x))
      (μHE[n].restrict R.carrier) :=
    hθm.aestronglyMeasurable.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      R.aestronglyMeasurable_orient hF)
  -- Step 6: `|h| ≤ g` a.e., by `orient_bound`
  have hdom : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (F x)‖ ≤ B * C.indicator (fun y => (R.mult y : ℝ)) x := by
    filter_upwards [Submission.dpf_pfc_imrep_orient_abs_apply_le P n U R] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (F x)).trans (hFB x)) (Nat.cast_nonneg _)
    · simp [indicator_of_notMem hxC, hF0 x hxC]
  -- Step 7: integrability
  refine ⟨hg.mono' hh hdom, ?_⟩
  -- Step 8: `∫ g dμ = B · (∫⁻_{M ∩ C} θ dHⁿ).toReal`
  have hgval : ∫ x, B * C.indicator (fun y => (R.mult y : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_const_mul, integral_indicator hCm, hres,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Nat.cast_nonneg _)
        hθm.aestronglyMeasurable]
    simp
  -- Step 9: `|∫ h dμ| ≤ ∫ g dμ`
  rw [← Real.norm_eq_abs, ← hgval]
  exact norm_integral_le_of_norm_le hg hdom
/-- **Simon §6.1** (the test-form topology, the case `β = 0`): if `ωⱼ → 0` in `𝒟ⁿ(U)`, the
`ωⱼ` vanish outside one compact `C ⊆ U`, and `supₓ ‖ωⱼ(x)‖ → 0`.  The compact set is the one in
`TestFormOnConverges`; uniform convergence of the `0`-th iterated derivatives on `C` gives the
bound on `C`, and `ωⱼ = 0` off `C`. -/
theorem Submission.dpf_pfc_testFormOnConverges_zero_uniform : ∀ (P n : ℕ) (U : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), TestFormOnConverges ωs 0 → ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ U ∧ (∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε := by
  intro P n U ωs h
  obtain ⟨C, hC, hCU, hsupp, -, hderiv⟩ := h
  have hzero : ∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')
  refine ⟨C, hC, hCU, hzero, fun ε hε => ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ C
  · have hjx := hj x hx
    simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
      norm_iteratedFDeriv_zero] at hjx
    exact hjx.le
  · rw [hzero j x hx, norm_zero]
    exact hε.le
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion
/-- **Push-forward of `τ(M, θ, ξ)` by a `C¹` map** (Simon 6.2.23–6.2.24(2), with a compact `K`
carrying `Hⁿ⌞M` in place of `B̄_t(y)`).  If `Hⁿ(M \ K) = 0`, `f` is `C¹` on an open `O ⊇ K` and
`f(K) ⊆ U`, then `Q(ω) = ∫_M θ ⟨ω(f x) ∘ Df(x), ξ⟩ dHⁿ` is a current in `U` with compact support
`spt Q ⊆ f(K)`.  With `‖Df‖ ≤ Λ` on `K`, `|θ ⟨ω(f x) ∘ Df(x), ξ⟩| ≤ ‖ω‖_∞ Λⁿ θ 1_K` a.e., so `Q` is
well defined, linear and `|Q(ω)| ≤ ‖ω‖_∞ Λⁿ ∫_{M ∩ K} θ dHⁿ`, which gives continuity; forms
vanishing on `f(K)` are killed by `Q`. -/
theorem Submission.dor_lmb_pc_pushforward_current_exists : ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → ∃ Q : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) ∧ IsCompact Q.support ∧ Q.support ⊆ f '' K := by
  intro P n U K O R f hU hK hKU hnull hO hKO hf hfKU
  -- Step 1: `f` and `Df` are continuous on `O`, `f(K)` is compact and `‖Df‖ ≤ Λ` on `K`
  have hfc : ContinuousOn f O := hf.continuousOn
  have hdfc : ContinuousOn (fderiv ℝ f) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  have hfK : IsCompact (f '' K) := hK.image_of_continuousOn (hfc.mono hKO)
  obtain ⟨Λ, hΛ0, hΛ⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ Λ := by
    obtain ⟨Λ, hΛ⟩ := hK.exists_bound_of_continuousOn (hdfc.mono hKO)
    exact ⟨max Λ 0, le_max_right _ _, fun x hx => (hΛ x hx).trans (le_max_left _ _)⟩
  -- Step 2: `Hⁿ⌞M` is carried by `K`
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hae : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    by_contra hxK
    exact hx ⟨hxM, hxK⟩
  -- Step 3: the pulled-back covector field `β_ω(x) = ω(f x) ∘ Df(x)` is continuous on `O`
  obtain ⟨β, hβ⟩ : ∃ β : TestFormOn U n → Euclid P → Covector (Euclid P) n, ∀ ω x,
      β ω x = ((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x) :=
    ⟨fun ω x => ((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap
      (fderiv ℝ f x), fun _ _ => rfl⟩
  have hcomp : Continuous fun p : Covector (Euclid P) n × (Euclid P →L[ℝ] Euclid P) =>
      p.1.compContinuousLinearMap p.2 :=
    continuous_iff_continuousAt.2 fun p =>
      (ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap p).hasFDerivAt.continuousAt
  have hβc : ∀ ω : TestFormOn U n, ContinuousOn (β ω) O := by
    intro ω
    have hω : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous ω.property.1.1
    have h : ContinuousOn (fun x => ((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap
        (fderiv ℝ f x)) O := hcomp.comp_continuousOn ((hω.comp_continuousOn hfc).prodMk hdfc)
    exact h.congr fun x _ => hβ ω x
  -- Step 4: `β_ω` is linear in `ω`
  have hβadd : ∀ (ω η : TestFormOn U n) x, β (ω + η) x = β ω x + β η x := by
    intro ω η x
    simp only [hβ]
    ext v
    simp
  have hβsmul : ∀ (c : ℝ) (ω : TestFormOn U n) x, β (c • ω) x = c • β ω x := by
    intro c ω x
    simp only [hβ]
    ext v
    simp
  -- Step 5: the truncation `1_K β_ω` is measurable, vanishes off `K` and `‖1_K β_ω‖ ≤ M Λⁿ`
  have hFm : ∀ ω : TestFormOn U n,
      AEStronglyMeasurable (K.indicator (β ω)) (μHE[n].restrict R.carrier) := fun ω =>
    (aestronglyMeasurable_indicator_iff hKm).2 (((hβc ω).mono hKO).aestronglyMeasurable hKm)
  have hFB : ∀ (ω : TestFormOn U n) (M : ℝ), (∀ z, ‖(ω : DifferentialForm (Euclid P) n) z‖ ≤ M) →
      ∀ x, ‖K.indicator (β ω) x‖ ≤ M * Λ ^ n := by
    intro ω M hM x
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, hβ]
      calc ‖((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)‖
          ≤ ‖(ω : DifferentialForm (Euclid P) n) (f x)‖ * ‖fderiv ℝ f x‖ ^ Fintype.card (Fin n) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ ≤ M * Λ ^ n := by
            rw [Fintype.card_fin]
            exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) (hΛ x hx) n)
              (pow_nonneg (norm_nonneg _) n) hM0
    · rw [indicator_of_notMem hx, norm_zero]
      exact mul_nonneg hM0 (pow_nonneg hΛ0 n)
  -- Step 6: integrability and `|∫_M θ ⟨β_ω, ξ⟩| ≤ M Λⁿ ∫_{M ∩ K} θ`
  have hpair : ∀ (ω : TestFormOn U n) (M : ℝ),
      (∀ z, ‖(ω : DifferentialForm (Euclid P) n) z‖ ≤ M) →
      Integrable (fun x => (R.mult x : ℝ) * R.orient x (β ω x)) (μHE[n].restrict R.carrier) ∧
      |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (β ω x) ∂μHE[n]| ≤
        M * Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    intro ω M hM
    obtain ⟨hint, hle⟩ := Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U K R
      (K.indicator (β ω)) (M * Λ ^ n) hK hKU (hFm ω) (fun x hx => indicator_of_notMem hx _)
      (hFB ω M hM)
    have heq : (fun x => (R.mult x : ℝ) * R.orient x (K.indicator (β ω) x))
        =ᵐ[μHE[n].restrict R.carrier] fun x => (R.mult x : ℝ) * R.orient x (β ω x) := by
      filter_upwards [hae] with x hx
      rw [indicator_of_mem hx]
    exact ⟨hint.congr heq, by rwa [← integral_congr_ae heq]⟩
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x (β ω x)) (μHE[n].restrict R.carrier) := by
    intro ω
    obtain ⟨M, hM⟩ := (ContDiff.continuous ω.property.1.1).bounded_above_of_compact_support
      ω.property.1.2
    exact (hpair ω M hM).1
  -- Step 7: the linear functional `Q(ω) = ∫_M θ ⟨β_ω, ξ⟩ dHⁿ`
  let I : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (β ω x) ∂μHE[n]
      map_add' := fun ω η => by
        simp only [hβadd, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := fun c ω => by
        have h : ∀ x, (R.mult x : ℝ) * R.orient x (β (c • ω) x) =
            c * ((R.mult x : ℝ) * R.orient x (β ω x)) := by
          intro x
          rw [hβsmul, map_smul, smul_eq_mul]
          ring
        simp only [h, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  have hIapply : ∀ ω : TestFormOn U n,
      I ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (β ω x) ∂μHE[n] := fun _ => rfl
  -- Step 8: continuity, from `supₓ ‖ωⱼ(x)‖ → 0`
  have hcont : ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 →
      Tendsto (fun j => I (ωs j)) atTop (𝓝 0) := by
    intro ωs hωs
    obtain ⟨-, -, -, -, hunif⟩ := Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
    have hc : 0 ≤ (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal :=
      ENNReal.toReal_nonneg
    have hA : 0 ≤ Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal :=
      mul_nonneg (pow_nonneg hΛ0 n) hc
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hε : 0 < δ / (Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal + 1) :=
      div_pos hδ (by linarith)
    filter_upwards [hunif _ hε] with j hj
    rw [Real.dist_eq, sub_zero, hIapply]
    calc |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (β (ωs j) x) ∂μHE[n]|
        ≤ δ / (Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal + 1) *
            Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal :=
          (hpair (ωs j) _ hj).2
      _ = δ * (Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal) /
            (Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal + 1) := by
          ring
      _ < δ := by
          rw [div_lt_iff₀ (by linarith)]
          nlinarith
  let Q : GeometricCurrentOn U n := ⟨I, hcont⟩
  -- Step 9: `Q` kills every form vanishing near `f(K)`, so `spt Q ⊆ f(K)` is compact
  have hvan : ∀ ω : TestFormOn U n,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f '' K) → Q ω = 0 := by
    intro ω hω
    change I ω = 0
    rw [hIapply]
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    have hfx : (ω : DifferentialForm (Euclid P) n) (f x) = 0 :=
      image_eq_zero_of_notMem_tsupport (disjoint_right.1 hω (mem_image_of_mem f hx))
    have h0 : ((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap
        (fderiv ℝ f x) = 0 := by
      rw [hfx]
      ext v
      simp
    rw [Pi.zero_apply, hβ, h0, map_zero, mul_zero]
  obtain ⟨hsub, hcpt⟩ :=
    Submission.rsd_cmr_support_subset_of_vanish P n U (f '' K) Q hU hfK hfKU hvan
  refine ⟨Q, fun ω => ?_, hcpt, hsub⟩
  change I ω = _
  simp only [hIapply, hβ]
/-- **Simon Ch. 3, Lemma 1.2 and Remark 1.3**, with bi-Lipschitz Borel pieces in place of `C¹`
submanifolds: a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null set, the disjoint
union of Borel sets `Fᵢ(Bᵢ) ⊆ M`, where `Fᵢ : ℝⁿ → ℝᴾ` is Lipschitz, `Bᵢ` is Borel,
`mᵢ|a − a'| ≤ |Fᵢ(a) − Fᵢ(a')|` on `Bᵢ` for some `mᵢ > 0`, and `DFᵢ` exists and is injective on
`Bᵢ`.  Each Lipschitz `Fⱼ` of the cover maps its non-differentiability points (Rademacher) and
its critical points (the image of `{JFⱼ = 0}`) to `Hⁿ`-null sets.  Mathlib's partition lemma cuts
the regular points into pieces on which `Fⱼ` is close to an injective linear map, hence
bi-Lipschitz; the images of the pieces are Borel (Lusin–Souslin) and are made disjoint as in
Remark 1.3. -/
theorem Submission.dpf_rectifiable_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0 := by
  intro P n M hM hrect
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F₀, hF₀, hcover⟩ := hrect
  choose K hK using hF₀
  -- Step 2: the regular sets `Gⱼ` are Borel and `Hⁿ(Fⱼ(ℝⁿ ∖ Gⱼ)) = 0`
  have hGmeas : ∀ f : Euclid n → Euclid P,
      MeasurableSet {a | DifferentiableAt ℝ f a ∧ Injective (fderiv ℝ f a)} := fun f =>
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet)
  -- Step 2(a): nondifferentiability points have null image (Rademacher)
  have hrad : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 := by
    intro f L hf
    have hz : volume {a : Euclid n | ¬ DifferentiableAt ℝ f a} = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hf.lipschitzOnWith (s := {a | ¬ DifferentiableAt ℝ f a}))
    rw [hvol, hz, mul_zero] at hle
    exact le_antisymm hle bot_le
  -- Step 2(b): critical points have null image.  On a piece where `f` is `ε`-close to a
  -- rank-deficient `A` (`Av = 0`, `‖v‖ = 1`), `|f a - f a'| ≤ (L + 1)|D a - D a'|` for
  -- `D = id - (1 - ε) v ⊗ v`, and `det D = ε`.
  have hsard : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}) = 0 := by
    intro f L hf
    set S := {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}
    have hSmeas : MeasurableSet S :=
      (measurableSet_of_differentiableAt ℝ f).inter
        (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet).compl
    have hR : ∀ R : ℕ, μHE[n] (f '' (S ∩ ball (0 : Euclid n) R)) = 0 := by
      intro R
      set s := S ∩ ball (0 : Euclid n) R
      have hsmeas : MeasurableSet s := hSmeas.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (f '' s) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
        intro ε hε hε1
        rcases s.eq_empty_or_nonempty with hse | hsne
        · rw [hse, image_empty, measure_empty]; exact bot_le
        obtain ⟨t, A, htdisj, htmeas, hst, hA, hAy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
            (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (f '' (s ∩ t k)) ≤
            ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
          intro k
          obtain ⟨y, hy, hAk⟩ := hAy hsne k
          have hAnorm : ‖A k‖ ≤ L := hAk ▸ norm_fderiv_le_of_lipschitz ℝ hf
          have hAni : ¬ Injective (A k) := hAk ▸ hy.1.2
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ A k v = 0 := by
            simp only [Injective, not_forall] at hAni
            obtain ⟨a, b, hab, hne⟩ := hAni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c : ℝ := 1 - (ε : ℝ) with hc
          have hc0 : 0 ≤ c := by
            rw [hc]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hAD : ∀ h, A k (D h) = A k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc]; ring
          have hfD : ∀ a ∈ s ∩ t k, ∀ a' ∈ s ∩ t k,
              ‖f a - f a'‖ ≤ ((L : ℝ) + 1) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hA k a ha a' ha'
            have h2 : ‖A k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hAD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (f a - f a') (A k (a - a'))
            linarith
          have himg : μHE[n] (f '' (s ∩ t k)) ≤
              ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := by
            set X := s ∩ t k
            set g := Function.invFunOn D X
            have hg : ∀ y ∈ D '' X, g y ∈ X ∧ D (g y) = y :=
              fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
            have hLip : LipschitzOnWith (L + 1) (f ∘ g) (D '' X) := by
              refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
              obtain ⟨hgy, hDy⟩ := hg y hy
              obtain ⟨hgy', hDy'⟩ := hg y' hy'
              simp only [comp_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
              calc ‖f (g y) - f (g y')‖ ≤ ((L : ℝ) + 1) * ‖D (g y) - D (g y')‖ :=
                    hfD _ hgy _ hgy'
                _ = _ := by rw [hDy, hDy']
            have hsub : f '' X ⊆ (f ∘ g) '' (D '' X) := by
              rintro _ ⟨a, ha, rfl⟩
              refine ⟨D a, mem_image_of_mem D ha, ?_⟩
              obtain ⟨hga, hDa⟩ := hg (D a) (mem_image_of_mem D ha)
              have := hfD _ hga _ ha
              rw [hDa, sub_self, norm_zero, mul_zero] at this
              exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
            exact (measure_mono hsub).trans
              (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c * v i) = 1 - c * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc]; ring
          calc μHE[n] (f '' (s ∩ t k)) ≤
                ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := himg
            _ = ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
              rw [hvol, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
                NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
              push_cast
              ring
        calc μHE[n] (f '' s) ≤ μHE[n] (⋃ k, f '' (s ∩ t k)) := by
              apply measure_mono
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨k, hk⟩ := mem_iUnion.mp (hst ha)
              exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
          _ ≤ ∑' k, μHE[n] (f '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := ENNReal.tsum_le_tsum hpiece
          _ = ((L : ℝ≥0∞) + 1) ^ n * volume (⋃ k, s ∩ t k) * ε := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right
              · exact fun k => hsmeas.inter (htmeas k)
          _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left.trans inter_subset_right
      have hfin : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have htend : Tendsto (fun ε : NNReal =>
          ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * (ε : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.coe_zero]
          exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      refine le_antisymm (ge_of_tendsto htend ?_) bot_le
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
      exact hbound ε hε.1 hε.2
    refine measure_mono_null ?_ (measure_iUnion_null hR)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
  set G : ℕ → Set (Euclid n) := fun j =>
    {a | DifferentiableAt ℝ (F₀ j) a ∧ Injective (fderiv ℝ (F₀ j) a)}
  have hGnull : ∀ j, μHE[n] (F₀ j '' (G j)ᶜ) = 0 := by
    intro j
    refine measure_mono_null ?_ (measure_union_null (hrad _ _ (hK j)) (hsard _ _ (hK j)))
    rintro _ ⟨a, ha, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F₀ j) a
    · exact Or.inr ⟨a, ⟨hd, fun hi => ha ⟨hd, hi⟩⟩, rfl⟩
    · exact Or.inl ⟨a, hd, rfl⟩
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Step 4: Mathlib's partition of `Gⱼ` into pieces on which `Fⱼ` is close to linear
  have hpart : ∀ j, ∃ (t : ℕ → Set (Euclid n)) (A : ℕ → Euclid n →L[ℝ] Euclid P),
      Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G j ⊆ ⋃ k, t k ∧
      (∀ k, ApproximatesLinearOn (F₀ j) (A k) (G j ∩ t k) (c (A k) / 2)) ∧
      ((G j).Nonempty → ∀ k, ∃ y ∈ G j, A k = fderiv ℝ (F₀ j) y) := fun j =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F₀ j) (G j) (fderiv ℝ (F₀ j))
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun A => c A / 2)
      (fun A => (div_pos (hcpos A) two_pos).ne')
  choose t A htdisj htmeas hGt hAapprox hAy using hpart
  -- Step 5: `Fⱼ` is bi-Lipschitz on `Gⱼ ∩ tⱼₖ` with lower constant `c(Aⱼₖ)/2`
  have hlow : ∀ j k, ∀ a ∈ G j ∩ t j k, ∀ a' ∈ G j ∩ t j k,
      ((c (A j k) / 2 : NNReal) : ℝ) * ‖a - a'‖ ≤ ‖F₀ j a - F₀ j a'‖ := by
    intro j k a ha a' ha'
    obtain ⟨y, hy, hAk⟩ := hAy j ⟨a, ha.1⟩ k
    have hinj : Injective (A j k) := hAk ▸ hy.2
    have h1 := hc (A j k) hinj (a - a')
    have h2 := hAapprox j k a ha a' ha'
    have h3 := norm_sub_norm_le (A j k (a - a')) (F₀ j a - F₀ j a')
    rw [norm_sub_rev (A j k (a - a'))] at h3
    push_cast at h2 ⊢
    linarith
  -- Step 6: enumerate the pieces by `i ↦ (unpair i)`; their images are Borel (Lusin–Souslin)
  set Fi : ℕ → Euclid n → Euclid P := fun i => F₀ (Nat.unpair i).1 with hFi
  set Di : ℕ → Set (Euclid n) := fun i =>
    G (Nat.unpair i).1 ∩ t (Nat.unpair i).1 (Nat.unpair i).2 with hDi
  set mi : ℕ → ℝ := fun i =>
    ((c (A (Nat.unpair i).1 (Nat.unpair i).2) / 2 : NNReal) : ℝ) with hmi
  have hDmeas : ∀ i, MeasurableSet (Di i) := fun i =>
    (hGmeas _).inter (htmeas _ _)
  have hmipos : ∀ i, 0 < mi i := fun i => by
    simp only [hmi, NNReal.coe_div, NNReal.coe_ofNat]
    exact div_pos (hcpos _) two_pos
  have hlowi : ∀ i, ∀ a ∈ Di i, ∀ a' ∈ Di i, mi i * ‖a - a'‖ ≤ ‖Fi i a - Fi i a'‖ :=
    fun i => hlow _ _
  have hNmeas : ∀ i, MeasurableSet (Fi i '' Di i) := by
    intro i
    refine (hDmeas i).image_of_continuousOn_injOn (hK _).continuous.continuousOn ?_
    intro a ha a' ha' h
    have := hlowi i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmipos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 7: disjointify the images inside `M`
  set Ñ : ℕ → Set (Euclid P) := fun i => Fi i '' Di i ∩ M
  have hÑmeas : ∀ i, MeasurableSet (Ñ i) := fun i => (hNmeas i).inter hM
  set B : ℕ → Set (Euclid n) := fun i => Di i ∩ Fi i ⁻¹' disjointed Ñ i with hB
  have himg : ∀ i, Fi i '' B i = disjointed Ñ i := by
    intro i
    rw [hB, image_inter_preimage]
    exact inter_eq_right.mpr ((disjointed_subset Ñ i).trans inter_subset_left)
  refine ⟨Fi, B, mi, fun i => ⟨K _, hK _⟩,
    fun i => (hDmeas i).inter ((hK _).continuous.measurable (MeasurableSet.disjointed hÑmeas i)),
    hmipos, fun i a ha a' ha' => hlowi i a ha.1 a' ha'.1, fun i a ha => ha.1.1,
    fun i => himg i ▸ MeasurableSet.disjointed hÑmeas i,
    fun i => himg i ▸ ((disjointed_subset Ñ i).trans inter_subset_right), ?_, ?_⟩
  · intro i j hij
    rw [himg i, himg j]
    exact disjoint_disjointed Ñ hij
  -- Step 8: the remainder lies in `M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ ∖ Gⱼ)`
  · have hU : (⋃ i, Fi i '' B i) = ⋃ i, Ñ i := by
      simp_rw [himg]
      exact iUnion_disjointed
    rw [hU]
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hGnull))
    rintro x ⟨hxM, hxN⟩
    rcases hcover hxM with hx0 | hx
    · exact Or.inl hx0
    · obtain ⟨j, a, rfl⟩ := mem_iUnion.mp hx
      by_cases ha : a ∈ G j
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt j ha)
        apply hxN
        refine mem_iUnion.mpr ⟨Nat.pair j k, ⟨a, ?_, ?_⟩, hxM⟩
        · simp only [hDi, Nat.unpair_pair]
          exact ⟨ha, hk⟩
        · simp only [hFi, Nat.unpair_pair]
      · exact Or.inr (mem_iUnion.mpr ⟨j, a, ha, rfl⟩)
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.ptd_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]
/-- Localized Besicovitch density (Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6, with
Simon Ch. 1, Theorem 3.16 = Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be
open, `A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e.
`x` and every `ε > 0`, `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`; the
exceptional set does not depend on `ε`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `a/β`, where
  `a = Hⁿ(A ∩ B̄_ρ(x))` and `β = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `a/β > 1 − ε`, which forces `0 < β < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = β − a ≤ εβ`. -/
theorem Submission.ptd_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many open balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2–3: Besicovitch density for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`, off one
  -- `Hⁿ⌞A`-null set for all `y ∈ D` at once
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  -- Step 4: `x ∈ B(y, r y)` for some `y ∈ D`, so `B̄_ρ(x) ⊆ B̄(y, r y)` for `ρ < δ`
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- (i)–(ii): for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  -- (iii): `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄(y, r y)) < ∞` for `ρ < δ`
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- (iv): `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 5: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- (a) `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- (b) `ε < 1`: eventually `a / β > 1 − ε`, with `β ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set β := μHE[n] (B ∩ closedBall x ρ)
    set a := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hβtop : β ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + a = β := hsplit ρ
    -- `β ≠ 0`, since otherwise `a / β = 0 / 0 = 0 ≤ 1 − ε`
    have hβ0 : β ≠ 0 := by
      intro h0
      have ha0 : a = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : a / β = 0 := by rw [ha0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * β < a :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hβ0) (Or.inl hβtop)).1 hρq
    -- `e + (1 − ε)β ≤ e + a = β = εβ + (1 − ε)β`, and `(1 − ε)β ≠ ∞`
    have h1 : e + (1 - ε) * β ≤ ε * β + (1 - ε) * β := by
      calc e + (1 - ε) * β ≤ e + a := by gcongr
        _ = β := hsplitρ
        _ = (ε + (1 - ε)) * β := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * β + (1 - ε) * β := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hβtop) h1
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in `U`** (Simon
Ch. 1, Remark 3.7(2); chapter-01.txt lines 705–711).  If `U ⊆ ℝᴾ` is open and `S` is Borel with
`Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ U ∖ S`,
`Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B_{r_y}(y)` with
`B̄_{r_y}(y) ⊆ U` cover `U` (Lindelöf); the finite-measure version applies to each piece
`S ∩ B_{r_y}(y)`, and near `x ∈ B_{r_y}(y)` the piece agrees with `S`. -/
theorem Submission.regcomp_atl_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U`.
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2 and 3, the finite-measure theorem on each piece `S ∩ B(y, r y)`, simultaneously
  -- for the countably many `y ∈ D`.
  have hpiece : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ ball y (r y) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    apply Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball)
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right S ball_subset_closedBall))
  -- Step 4, localization: for small `ρ`, `B̄(x, ρ) ⊆ B(y, r y)`, so the piece agrees with `S`.
  filter_upwards [hpiece] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov hxU)
  obtain ⟨ε, hε, hεy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεy)]

/-- **Simon Ch. 3, Remark 1.5(3)** (the upper bound, with `ε = 1`): if `D` has approximate
tangent space `Q` at `x` and `Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all
small `ρ > 0`.

* Test Definition 1.4 with `φ = max(0, min(1, 2 − |w|)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`:
  `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`, so for `0 < ρ < r₁` it is `< C := |Λ| + 1`, and
  `2ρ < r₀`.
* By the blow-up scaling, `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, so `φ` is
  integrable on `η_{x,ρ}(D)` and `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} φ dHⁿ < C`.
* Scaling back, `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ Cρⁿ`. -/
theorem Submission.ptd_tl_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1: the cutoff `φ = max(0, min(1, 2 − ‖w‖)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`
  have hout : ∀ w : Euclid P, w ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖w‖)) = 0 := by
    intro w hw
    rw [mem_closedBall_zero_iff, not_le] at hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let φ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun w => max 0 (min 1 (2 - ‖w‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => le_max_left _ _
  have hφ1 : ∀ w, φ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hφB : ∀ w ∈ closedBall (0 : Euclid P) 1, φ w = 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    show max 0 (min 1 (2 - ‖w‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`; choose `r₁` such that
  -- `∫_{η_{x,ρ}(D)} φ dHⁿ < |Λ| + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set Λ := ∫ w in (Q : Set (Euclid P)), φ w ∂μHE[n]
  have hC : (0 : ℝ) ≤ |Λ| + 1 := by positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, φ w ∂μHE[n]) < |Λ| + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 φ).eventually_lt_const ((le_abs_self Λ).trans_lt (lt_add_one _))).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨|Λ| + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hI, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hρ).ne'
  -- the blow-up scaling with `R = 2` and `R = 1`
  have h2 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 2 D hρ
  have h1 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 1 D hρ
  rw [mul_one ρ] at h1
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  -- Step 3: `Hⁿ(T ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, as `2ρ < r₀`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    rw [h2]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hρ0)) ?_
    refine ne_top_of_le_ne_top hfin (measure_mono (Set.inter_subset_inter_right _ ?_))
    exact closedBall_subset_closedBall (by linarith)
  -- Step 4: `|φ| ≤ 1_{B̄₂(0)}`, which is integrable for `Hⁿ⌞T`; hence so is `φ`
  have hint : Integrable (fun w => φ w) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      φ.continuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hw : w ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hw, Real.norm_of_nonneg (hφ0 w)]
        exact hφ1 w
      · rw [Set.indicator_of_notMem hw, norm_le_zero_iff]
        exact hout w hw
  -- Step 5: `Hⁿ(T ∩ B̄₁(0)) = ∫⁻ 1_{B̄₁(0)} d(Hⁿ⌞T) ≤ ∫⁻ φ d(Hⁿ⌞T) = ∫_T φ dHⁿ < |Λ| + 1`
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (|Λ| + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ w, (closedBall (0 : Euclid P) 1).indicator 1 w ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ w, ENNReal.ofReal (φ w) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hw, Pi.one_apply, hφB w hw, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hw]
            exact zero_le
      _ = ENNReal.ofReal (∫ w, φ w ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hφ0)).symm
      _ ≤ ENNReal.ofReal (|Λ| + 1) := ENNReal.ofReal_le_ofReal hI.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(T ∩ B̄₁(0)) ≤ (|Λ| + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      = ENNReal.ofReal ρ ^ n * ((ENNReal.ofReal ρ)⁻¹ ^ n * μHE[n] (D ∩ closedBall x ρ)) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hρ0 ENNReal.ofReal_ne_top, one_pow,
          one_mul]
    _ = ENNReal.ofReal ρ ^ n * μHE[n] (T ∩ closedBall 0 1) := by rw [h1]
    _ ≤ ENNReal.ofReal ρ ^ n * ENNReal.ofReal (|Λ| + 1) := by gcongr
    _ = ENNReal.ofReal ((|Λ| + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hρ.le, mul_comm (ENNReal.ofReal ρ ^ n)]
/-- Zero `n`-density of the excess `B ∖ A` (step 6 of the tangent-locality argument for a piece):
if `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0` as
`ρ ↓ 0`.  With `ε = 1/2`, subadditivity and cancellation of the finite half give
`Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ`; then `ε = δ/(2C + 1)` gives
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.ptd_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hG hE
  -- Step 1: for `ρ > 0`, `ofReal (Cρⁿ) = ofReal C · (ofReal ρ)ⁿ`
  have hA : ∀ ρ : ℝ, 0 < ρ → ρ < r₁ →
      μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal C * ENNReal.ofReal ρ ^ n := by
    intro ρ hρ hρ₁
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul' (pow_nonneg hρ.le n)]
    exact hG ρ hρ hρ₁
  -- Step 2: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ κ (ofReal ρ)ⁿ` with `κ = 2 ofReal C`
  set κ : ℝ≥0∞ := 2 * ENNReal.ofReal C with hκ
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ κ * ENNReal.ofReal ρ ^ n := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hE 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := hρ.2.le.trans (min_le_left _ _)
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hβ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hρ₀)))
    -- `B ∩ B̄_ρ(x) ⊆ (A ∩ B̄_ρ(x)) ∪ ((B ∖ A) ∩ B̄_ρ(x))`, so subadditivity applies
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- `β/2 + β/2 = β ≤ a + e ≤ a + β/2`; cancelling the finite `β/2` gives `β/2 ≤ a`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hβ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add le_rfl he)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal C * ENNReal.ofReal ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = κ * ENNReal.ofReal ρ ^ n := by rw [hκ, mul_assoc]
  -- Step 3: for `δ > 0`, `ε = δ/(κ + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δ (ofReal ρ)ⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hκ₁ : κ + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hκ₀ : κ + 1 ≠ 0 := by positivity
  filter_upwards [hB, hE (δ / (κ + 1)) (ENNReal.div_pos hδ.ne' hκ₁)] with ρ hρB hρe
  -- Step 4: hence `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / (ofReal ρ)ⁿ ≤ δ`
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ)
      ≤ δ / (κ + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (κ + 1) * ((κ + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hκ₀ hκ₁]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value
(by `Submission.ptd_tl_blowUp_measure_scaling`), and this tends to `0`. -/
theorem Submission.ptd_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)` is Borel
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Step 2: for every `f ∈ C_c`, `Δ_f(ρ) = ∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- (a): `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- (b): `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- (c)–(e) give `|Δ_f(ρ)| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for `0 < ρ < r₀/R`; (f) sends the
    -- bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- (c): for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- (d): `Δ_f(ρ) = ∫_{η_{x,ρ}(B ∖ A)} f`, as `η_{x,ρ}(B ∖ A) = η_{x,ρ}(B) ∖ η_{x,ρ}(A)`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- (e): `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- (f): `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Steps 3–4: transfer the limits of Definition 1.4 in both directions; `finrank Q = n` is shared
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _

/-- **Simon Ch. 3, Remarks 1.5(2)–(3) and the proof of Theorem 1.6 "⇒"**: let `U` be open,
`A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x`,
simultaneously for every subspace `Q`, `B` has approximate tangent space `Q` at `x` iff `A` does.

* Off one `Hⁿ⌞A`-null set, independent of `Q`, `x ∈ A` and for every `ε > 0`,
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0` (Besicovitch).
* `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`.
* A tangent plane of `B` or of `A` at `x` gives `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for small `ρ` (via
  `A ⊆ B` in the first case), hence `Hⁿ((B \ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals
  of `B` and `A` have the same limits. -/
theorem Submission.ptd_ae_approxTangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 2–4: off one `Hⁿ⌞A`-null set, chosen before `Q`, `x ∈ A` and the excess of `B` over
  -- `A` near `x` is eventually small relative to `Hⁿ(B ∩ B̄_ρ(x))`
  filter_upwards [Submission.ptd_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB_le : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 6–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` makes the excess `o(ρⁿ)`, which forces
  -- the same approximate tangent spaces
  have hiff : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.ptd_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.ptd_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth
          hexc) Q
  -- Step 8: step 5 turns the assumed tangent plane into the growth bound
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (hiff C r₁ hr₁ fun ρ hρ hρr₁ => (hAB_le ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB_le (s / 2))) hTA
    exact (hiff C r₁ hr₁ hgrowth).2 hTA
/-- Borel image and null-set pullback along a bi-Lipschitz piece: if `F : ℝⁿ → ℝᴾ` is Lipschitz,
`B ⊆ ℝⁿ` is Borel and `m‖a − a'‖ ≤ ‖F a − F a'‖` on `B` (`m > 0`), then `F(B)` is Borel
(Lusin–Souslin), and a property holding `Hⁿ⌞F(B)`-a.e. holds at `F b` for Lebesgue-a.e. `b ∈ B`:
`invFunOn F B` is `m⁻¹`-Lipschitz on `F(B)` (Simon Ch. 2, 1.8(i)) and maps the `Hⁿ`-null bad
image set onto a superset of the bad parameters, and `Hⁿ` is Lebesgue measure on `ℝⁿ`. -/
theorem Submission.ptd_piece_image_measurable_ae_pullback : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → MeasurableSet (F '' B) ∧ ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ b ∂(volume.restrict B), p (F b) := by
  intro P n F B L m hF hB hm hlow
  -- Step 1: the lower bound makes `F` injective on `B`
  have hinj : InjOn F B := fun a ha a' ha' h => by
    have hle := hlow a ha a' ha'
    rw [h, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle hm))
  -- Step 2: Lusin–Souslin
  have hFB : MeasurableSet (F '' B) := hB.image_of_continuousOn_injOn hF.continuous.continuousOn hinj
  refine ⟨hFB, fun p hp => ?_⟩
  -- Step 3: `G = invFunOn F B` is `m⁻¹`-Lipschitz on `F '' B`
  have hG : LipschitzOnWith (Real.toNNReal m⁻¹) (invFunOn F B) (F '' B) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn ha', dist_eq_norm, dist_eq_norm,
      inv_mul_eq_div, le_div_iff₀' hm]
    exact hlow a ha a' ha'
  -- Step 4: the bad parameters lie in the `G`-image of the `Hⁿ`-null bad image set
  rw [ae_restrict_iff' hFB, ae_iff] at hp
  rw [ae_restrict_iff' hB, ae_iff, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hnull : μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)}) = 0 := by
    refine le_zero_iff.1 ?_
    calc μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)})
        ≤ (Real.toNNReal m⁻¹ : ℝ≥0∞) ^ n * μHE[n] {y | ¬(y ∈ F '' B → p y)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hG.mono fun y hy => (not_imp.1 hy).1)
      _ = 0 := by rw [hp, mul_zero]
  refine measure_mono_null (fun b hb => ?_) hnull
  obtain ⟨hbB, hpb⟩ := not_imp.1 (show ¬(b ∈ B → p (F b)) from hb)
  exact ⟨F b, show ¬(F b ∈ F '' B → p (F b)) from not_imp.2 ⟨mem_image_of_mem F hbB, hpb⟩,
    hinj.leftInvOn_invFunOn hbB⟩
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.pit_setIntegral_blowUpMap_image : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
  intro P n M x r hr f
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
      ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
    ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
  -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
  have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
    intro S
    have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
      rw [image_image, he]
      rfl
    rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
  have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
      Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
      e.image_preimage]
  -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
  rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]

/-- **Rescaled area formula** (Jacobian kept abstract): if `F` is continuous, `B` and `J ≥ 0` are
Borel and `∫⁻_{F(B)} g dHⁿ = ∫⁻_B J(x) g(F(x)) dλ(x)` for every `g ≥ 0`, then for `r > 0` and
continuous `f`,
`∫_{η_{F(b),r}(F(B))} f dHⁿ = ∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dλ(c)`.
The area hypothesis says `Hⁿ⌞F(B) = F_#ν` with `ν = J λ⌞B`, which transports every integral;
the substitution `a = b + rc` produces the factor `rⁿ` that cancels the `r⁻ⁿ` of the blow-up. -/
theorem Submission.pit_blowUp_image_setIntegral_eq_rescaled : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (b : Euclid n) (r : ℝ) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) → 0 < r → Continuous f → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F b) r '' (F '' B), f z ∂μHE[n] = ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume := by
  intro P n F B J b r f hF hB hJ hJ0 harea hr hf
  -- blow-up scaling: `∫_{η(F(B))} f dHⁿ = r⁻ⁿ ∫_{F(B)} f ∘ η dHⁿ`, `η = η_{F(b),r}`
  rw [Submission.pit_setIntegral_blowUpMap_image P n (F '' B) (F b) r hr f]
  -- `Hⁿ⌞F(B) = F_#ν`: the area hypothesis with `g = 1_T` for every Borel `T`
  have hmeas : μHE[n].restrict (F '' B) =
      Measure.map F ((volume.restrict B).withDensity fun x => ENNReal.ofReal (J x)) := by
    ext T hT
    have h := harea (T.indicator 1)
    rw [lintegral_indicator_one hT] at h
    rw [h, Measure.map_apply hF.measurable hT, withDensity_apply _ (hT.preimage hF.measurable),
      ← lintegral_indicator (hT.preimage hF.measurable)]
    congr 1
    funext x
    by_cases hx : F x ∈ T <;> simp [hx]
  -- `∫_{F(B)} f ∘ η dHⁿ = ∫ 1_B J (f ∘ η ∘ F) dλ`, with no integrability needed
  have hη : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r z) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hpull : ∫ y in F '' B, f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r y) ∂μHE[n] =
      ∫ x, B.indicator J x * f (r⁻¹ • (F x - F b)) ∂volume := by
    rw [hmeas, integral_map hF.aemeasurable hη.aestronglyMeasurable]
    have h := integral_withDensity_eq_integral_smul (μ := volume.restrict B) hJ.real_toNNReal
      (fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r (F x)))
    simp only [ENNReal.ofReal]
    rw [h, ← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B
    · simp [hx, NNReal.smul_def, hJ0 x, Poincare.SimonGMT.Chapter03.blowUpMap]
    · simp [hx]
  rw [hpull]
  -- substitution `a = b + rc`: `∫ G(b + rc) dλ(c) = r⁻ⁿ ∫ G dλ`
  set G : Euclid n → ℝ := fun x => B.indicator J x * f (r⁻¹ • (F x - F b))
  have hsubst : ∫ c, G (b + r • c) ∂volume = r⁻¹ ^ n * ∫ a, G a ∂volume := by
    rw [Measure.integral_comp_smul volume (fun x => G (b + x)) r,
      integral_add_left_eq_self (fun x => G x) b, finrank_euclideanSpace_fin, smul_eq_mul,
      ← inv_pow, abs_of_pos (pow_pos (inv_pos.2 hr) n)]
  exact hsubst.symm
/-- Co-Lipschitz bounds pass to the derivative at density points: if `m > 0`,
`m‖a − b‖ ≤ ‖F(a) − F(b)‖` for every `a ∈ B` (`B` arbitrary), `F` is differentiable at `b` and
`λ(B ∩ B̄_ρ(b)) / λ(B̄_ρ(b)) → 1` as `ρ ↓ 0`, then `m‖c‖ ≤ ‖DF(b)c‖` for every `c`.
For small `r > 0` the ball `B_{rδ}(b + rc)`, a fixed fraction `(δ / (‖c‖ + δ))ⁿ` of
`B̄_{r(‖c‖+δ)}(b)`, must meet `B`; the bound at such a point and differentiability give
`m‖c‖ ≤ ‖DF(b)c‖ + δ(m + ‖DF(b)‖ + ‖c‖ + δ)`, and `δ ↓ 0`. -/
theorem Submission.pit_fderiv_lower_bound_of_density : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (m : ℝ) (b : Euclid n), 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → ∀ c : Euclid n, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ := by
  intro P n F B m b hm hB hF hdens c
  set L := fderiv ℝ F b with hL
  have hFL : HasFDerivAt F L b := hF.hasFDerivAt
  -- main estimate: for every `δ > 0`, `m‖c‖ ≤ ‖Lc‖ + δ (m + ‖L‖ + ‖c‖ + δ)`
  have key : ∀ δ : ℝ, 0 < δ → m * ‖c‖ ≤ ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ) := by
    intro δ hδ
    have hK : 0 < ‖c‖ + δ := by positivity
    -- differentiability: `‖F a - F b - L (a - b)‖ ≤ δ ‖a - b‖` near `b`
    obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.1 (hFL.isLittleO.bound hδ)
    -- density: the ratio exceeds `1 - q`, `q = (δ / (‖c‖ + δ)) ^ n`, on some `(0, ρ₀)`
    obtain ⟨q, hq_def⟩ : ∃ q : ℝ≥0∞, q = ENNReal.ofReal ((δ / (‖c‖ + δ)) ^ n) := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hlt : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (hdens.eventually_const_lt hlt)
    have hρ₀' : 0 < ρ₀ := hρ₀
    -- the radius `ρ = r (‖c‖ + δ)`
    obtain ⟨ρ, hρ, hρε, hρρ₀⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ρ < ρ₀ :=
      ⟨min ε ρ₀ / 2, by positivity, by linarith [min_le_left ε ρ₀, lt_min hε hρ₀'],
        by linarith [min_le_right ε ρ₀, lt_min hε hρ₀']⟩
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / (‖c‖ + δ) := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hr_def]; positivity
    have hrK : r * (‖c‖ + δ) = ρ := by rw [hr_def]; field_simp
    -- some point of `B` lies in `B_{rδ}(b + r c)`, else the ratio at `ρ` is `≤ 1 - q`
    obtain ⟨a, haB, ha⟩ : ∃ a ∈ B, ‖a - (b + r • c)‖ < r * δ := by
      by_contra! hcon
      have hsub : ball (b + r • c) (r * δ) ⊆ closedBall b ρ := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx
        rw [mem_closedBall, dist_eq_norm]
        calc ‖x - b‖ = ‖(x - (b + r • c)) + r • c‖ := by congr 1; abel
          _ ≤ ‖x - (b + r • c)‖ + ‖r • c‖ := norm_add_le _ _
          _ = ‖x - (b + r • c)‖ + r * ‖c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
          _ ≤ ρ := by rw [← hrK]; linarith
      have hBsub : B ∩ closedBall b ρ ⊆ closedBall b ρ \ ball (b + r • c) (r * δ) := by
        rintro x ⟨hxB, hx⟩
        refine ⟨hx, fun hxW => ?_⟩
        rw [mem_ball, dist_eq_norm] at hxW
        exact (hcon x hxB).not_gt hxW
      have hVfin : volume (closedBall b ρ) ≠ ∞ := measure_closedBall_lt_top.ne
      have hball : volume (ball (b + r • c) (r * δ)) = q * volume (closedBall b ρ) := by
        rw [Measure.addHaar_ball_of_pos volume _ (mul_pos hr hδ),
          Measure.addHaar_closedBall volume _ hρ.le, finrank_euclideanSpace_fin, ← mul_assoc,
          hq_def, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (δ / (‖c‖ + δ)) ^ n), ← mul_pow,
          ← hrK]
        congr 3
        field_simp
      have hle : volume (B ∩ closedBall b ρ) ≤ (1 - q) * volume (closedBall b ρ) := by
        calc volume (B ∩ closedBall b ρ)
            ≤ volume (closedBall b ρ \ ball (b + r • c) (r * δ)) := measure_mono hBsub
          _ = volume (closedBall b ρ) - volume (ball (b + r • c) (r * δ)) :=
            measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
          _ = (1 - q) * volume (closedBall b ρ) := by
            rw [hball, ENNReal.sub_mul (fun _ _ => hVfin), one_mul]
      have hgt : 1 - q < volume (B ∩ closedBall b ρ) / volume (closedBall b ρ) :=
        hρ₀sub ⟨hρ, hρρ₀⟩
      exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
    -- the estimate at `a`, with `a - b = r c + e`, `‖e‖ < r δ`
    obtain ⟨e, he_def⟩ : ∃ e : Euclid n, e = a - (b + r • c) := ⟨_, rfl⟩
    rw [← he_def] at ha
    have hab : a - b = r • c + e := by rw [he_def]; abel
    have hab_le : ‖a - b‖ ≤ r * ‖c‖ + ‖e‖ := by
      rw [hab]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hab_lt : ‖a - b‖ < r * (‖c‖ + δ) := by rw [mul_add]; linarith
    have hdist : dist a b < ε := by rw [dist_eq_norm]; linarith
    have h1 : m * ‖a - b‖ ≤ ‖F a - F b‖ := hB a haB
    have h2 : ‖F a - F b‖ ≤ ‖L (a - b)‖ + δ * ‖a - b‖ := by
      have h := hεF hdist
      have h' := norm_sub_norm_le (F a - F b) (L (a - b))
      linarith
    have h3 : ‖L (a - b)‖ ≤ r * ‖L c‖ + ‖L‖ * ‖e‖ := by
      rw [hab, map_add, map_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      linarith [L.le_opNorm e]
    have h4 : r * ‖c‖ ≤ ‖a - b‖ + ‖e‖ := by
      have : r • c = (a - b) - e := by rw [hab]; abel
      calc r * ‖c‖ = ‖r • c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ = ‖(a - b) - e‖ := by rw [this]
        _ ≤ ‖a - b‖ + ‖e‖ := norm_sub_le _ _
    have h5 : ‖L‖ * ‖e‖ ≤ ‖L‖ * (r * δ) := mul_le_mul_of_nonneg_left ha.le (norm_nonneg _)
    have h6 : m * ‖e‖ ≤ m * (r * δ) := mul_le_mul_of_nonneg_left ha.le hm.le
    have h7 : δ * ‖a - b‖ ≤ δ * (r * (‖c‖ + δ)) := mul_le_mul_of_nonneg_left hab_lt.le hδ.le
    have h8 : m * (r * ‖c‖) ≤ m * (‖a - b‖ + ‖e‖) := mul_le_mul_of_nonneg_left h4 hm.le
    have hfin : r * (m * ‖c‖) ≤ r * (‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by
      linarith
    exact le_of_mul_le_mul_left hfin hr
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) (𝓝[>] 0) (𝓝 ‖L c‖) := by
    have hcont : Continuous (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
/-- If `F` has derivative `L` at `b` and `f` is continuous with compact support, then
`∫_{B̄_R(0)} |f(r⁻¹(F(b + rc) − F(b))) − f(Lc)| dc → 0` as `r ↓ 0` (the error term `T₃` in the
limit of rescaled integrals over the image of a `C¹` piece; cf. the tangent-plane limit in Simon
Ch. 3, proof of 1.6 "⇒").  With `V = |B̄_R(0)|` and `S = |R| + 1`, take `η` from the uniform
continuity of `f` for `ε / (V + 1)`, then `δ₀` with `‖F(b + k) − F(b) − Lk‖ ≤ (η / 2S)‖k‖` for
`‖k‖ < δ₀`; for `0 < r < δ₀ / S` the integrand is `≤ ε / (V + 1)` on the ball. -/
theorem Submission.pit_ril_diffQuot_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (b : Euclid n) (f : Euclid P → ℝ) (R : ℝ), HasFDerivAt F L b → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro P n F L b f R hF hfc hfs
  -- `D = B̄_R(0)` has finite measure `V`, and `‖c‖ < S = |R| + 1` on `D`
  have hDfin : (volume : Measure (Euclid n)) (closedBall 0 R) < ∞ := measure_closedBall_lt_top
  set V : ℝ := (volume : Measure (Euclid n)).real (closedBall 0 R)
  have hV : 0 ≤ V := measureReal_nonneg
  set S : ℝ := |R| + 1
  have hS : 0 < S := by positivity
  have hcS : ∀ c ∈ closedBall (0 : Euclid n) R, ‖c‖ < S := fun c hc =>
    ((mem_closedBall_zero_iff.1 hc).trans (le_abs_self R)).trans_lt (lt_add_one _)
  -- uniform continuity of `f` and the little-o form of `HasFDerivAt`
  have huc := Metric.uniformContinuous_iff.1 (hfs.uniformContinuous_of_continuous hfc)
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hV1 : 0 < V + 1 := by linarith
  set ε₁ : ℝ := ε / (V + 1) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos hε hV1
  obtain ⟨η, hη, hηf⟩ := huc ε₁ hε₁
  set θ : ℝ := η / (2 * S) with hθ_def
  have hθ : 0 < θ := div_pos hη (by linarith)
  obtain ⟨δ₀, hδ₀, hδ₀F⟩ := Metric.eventually_nhds_iff.1 (hlo.bound hθ)
  refine ⟨δ₀ / S, div_pos hδ₀ hS, fun r hr hrδ => ?_⟩
  rw [mem_Ioi] at hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hrδ
  have hrS : r * S < δ₀ := (lt_div_iff₀ hS).1 hrδ
  -- pointwise bound on the integrand
  have hpt : ∀ c ∈ closedBall (0 : Euclid n) R,
      ‖‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖ ≤ ε₁ := by
    intro c hc
    have hc' := hcS c hc
    have hnorm : ‖r • c‖ = r * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hrc : dist (r • c) 0 < δ₀ := by
      rw [dist_zero_right, hnorm]
      calc r * ‖c‖ ≤ r * S := mul_le_mul_of_nonneg_left hc'.le hr.le
        _ < δ₀ := hrS
    have hbound := hδ₀F hrc
    have heq : r⁻¹ • (F (b + r • c) - F b) - L c
        = r⁻¹ • (F (b + r • c) - F b - L (r • c)) := by
      rw [map_smul, smul_sub _ (F (b + r • c) - F b), inv_smul_smul₀ hr.ne']
    have hclose : dist (r⁻¹ • (F (b + r • c) - F b)) (L c) < η := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      calc r⁻¹ * ‖F (b + r • c) - F b - L (r • c)‖
          ≤ r⁻¹ * (θ * ‖r • c‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr.le)
        _ = θ * ‖c‖ := by rw [hnorm]; field_simp
        _ ≤ θ * S := mul_le_mul_of_nonneg_left hc'.le hθ.le
        _ = η / 2 := by rw [hθ_def]; field_simp
        _ < η := half_lt_self hη
    have := hηf hclose
    rw [Real.dist_eq] at this
    rw [norm_norm, Real.norm_eq_abs]
    exact this.le
  -- integral bound
  have hint := norm_setIntegral_le_of_norm_le_const hDfin hpt
  rw [dist_zero_right]
  calc ‖∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖
      ≤ ε₁ * V := hint
    _ < ε := by
      rw [hε₁_def, div_mul_eq_mul_div, div_lt_iff₀ hV1]
      nlinarith
/-- At a point `b` of Lebesgue density one of the Borel set `B` (`λ(B ∩ B̄_ρ(b))/λ(B̄_ρ(b)) → 1`
as `ρ ↓ 0`, the quotient taken in `[0, ∞]`), the averages `⨍_{B̄_s(b)} 1_{ℝⁿ∖B} dλ` tend to `0`
as `s ↓ 0`.  For `s > 0`, `0 < λ(B̄_s(b)) < ∞` and, by additivity, the average equals
`1 − (λ(B ∩ B̄_s(b))/λ(B̄_s(b))).toReal`; `toReal` is continuous at `1`. -/
theorem Submission.pit_ril_compl_average_tendsto : ∀ (n : ℕ) (B : Set (Euclid n)) (b : Euclid n), MeasurableSet B → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, Bᶜ.indicator (fun _ => (1 : ℝ)) a ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n B b hB hlim
  -- `q(ρ).toReal → 1` (`toReal` is continuous at `1 ≠ ∞`), so `1 - q(ρ).toReal → 0`
  have h1 : Tendsto (fun ρ : ℝ =>
      1 - (volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub
      ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim)
    rwa [ENNReal.toReal_one, sub_self] at h
  refine h1.congr' ?_
  -- for `s > 0`, `0 < λ(C_s) < ∞` and the average equals `1 - q(s).toReal`
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hfin : volume (closedBall b s) ≠ ∞ := measure_closedBall_lt_top.ne
  have hC : volume.real (closedBall b s) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume b hs).ne' hfin).ne'
  -- `λ_ℝ(C_s ∩ B) + λ_ℝ(C_s \ B) = λ_ℝ(C_s)`
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := closedBall b s) hB hfin
  rw [setAverage_eq, setIntegral_indicator hB.compl, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, inter_comm B,
    ← Set.sdiff_eq, ← hsplit]
  rw [← hsplit] at hC
  field_simp
  ring
/-- Localised three-term estimate for the rescaled area integrals (one fixed `r > 0`).  With
`Φ_r(c) = r⁻¹(F(b + rc) − F(b))` and `D = B̄_{R/m}(0)`, the integrands
`X(c) = 1_B(b + rc) J(b + rc) f(Φ_r(c))` and `Y(c) = J(b) f(Lc)` vanish off `D` (by the lower
bounds for `F` on `B` and for `L`, as `f = 0` off the open `R`-ball), and pointwise
`|X − Y| ≤ KM·1_{Bᶜ}(b + rc) + M|J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(Lc)|`, by cases on
`b + rc ∈ B`; all are bounded Borel functions, so integrate over `D`. -/
theorem Submission.pit_ril_three_term_bound : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ) (R M r : ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → (∀ c, m * ‖c‖ ≤ ‖L c‖) → Continuous f → (∀ w, R ≤ ‖w‖ → f w = 0) → (∀ w, ‖f w‖ ≤ M) → 0 < r → ‖(∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) - J b * (∫ c, f (L c) ∂volume)‖ ≤ K * M * (∫ c in closedBall (0 : Euclid n) (R / m), Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) ∂volume) + M * (∫ c in closedBall (0 : Euclid n) (R / m), ‖J (b + r • c) - J b‖ ∂volume) + J b * (∫ c in closedBall (0 : Euclid n) (R / m), ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) := by
  intro P n F L B J K m b f R M r hF hB hJ hJK hm hFB hL hf hfR hfM hr
  -- constants: `0 ≤ M`, `0 ≤ J b ≤ K`, `0 ≤ K`, and `λ(D) < ∞` for `D = B̄_{R/m}(0)`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfM 0)
  have hJb0 : 0 ≤ J b := (hJK b).1
  have hJbK : J b ≤ K := (hJK b).2
  have hK0 : 0 ≤ K := hJb0.trans hJbK
  have hDfin : volume (closedBall (0 : Euclid n) (R / m)) ≠ ∞ := measure_closedBall_lt_top.ne
  -- measurability of the integrands
  have hshift : Continuous fun c : Euclid n => b + r • c :=
    continuous_const.add (continuous_id.const_smul r)
  have hΦ : Continuous fun c : Euclid n => f (r⁻¹ • (F (b + r • c) - F b)) :=
    hf.comp (((hF.comp hshift).sub continuous_const).const_smul r⁻¹)
  have hfL : Continuous fun c : Euclid n => f (L c) := hf.comp L.continuous
  have hIJ : Measurable fun c : Euclid n => B.indicator J (b + r • c) :=
    (hJ.indicator hB).comp hshift.measurable
  have hg₁ : Measurable fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) :=
    (measurable_const.indicator hB.compl).comp hshift.measurable
  have hg₂ : Measurable fun c : Euclid n => ‖J (b + r • c) - J b‖ :=
    ((hJ.comp hshift.measurable).sub measurable_const).norm
  have hg₃ : Continuous fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
    (hΦ.sub hfL).norm
  -- bounded measurable functions are integrable on `D`
  have hIJb : ∀ c : Euclid n, ‖B.indicator J (b + r • c)‖ ≤ K := by
    intro c
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hJK _).1]
      exact (hJK _).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact hK0
  have hXint : IntegrableOn
      (fun c : Euclid n => B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (hIJ.mul hΦ.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul]
    exact mul_le_mul (hIJb c) (hfM _) (norm_nonneg _) hK0
  have hYint : IntegrableOn (fun c : Euclid n => J b * f (L c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (measurable_const.mul hfL.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul, Real.norm_of_nonneg hJb0]
    exact mul_le_mul hJbK (hfM _) (norm_nonneg _) hK0
  have hg₁int : IntegrableOn (fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := 1) hDfin hg₁.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    by_cases h : b + r • c ∈ Bᶜ
    · rw [Set.indicator_of_mem h, norm_one]
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact zero_le_one
  have hg₂int : IntegrableOn (fun c : Euclid n => ‖J (b + r • c) - J b‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K) hDfin hg₂.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hJK (b + r • c), hJK b]
  have hg₃int : IntegrableOn
      (fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := M + M) hDfin hg₃.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hfM _) (hfM _))
  -- localisation: both integrands vanish off `D`
  have hloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → R < m * ‖c‖ := by
    intro c hc
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hc
    rwa [mul_comm] at hc
  have hXloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) →
      B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) = 0 := by
    intro c hc
    by_cases h : b + r • c ∈ B
    · have h1 := hFB _ h
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : R ≤ ‖r⁻¹ • (F (b + r • c) - F b)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc R ≤ m * ‖c‖ := (hloc c hc).le
          _ = r⁻¹ * (m * (r * ‖c‖)) := by rw [mul_left_comm m r, inv_mul_cancel_left₀ hr.ne']
          _ ≤ r⁻¹ * ‖F (b + r • c) - F b‖ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hr.le)
      rw [hfR _ h2, mul_zero]
    · rw [Set.indicator_of_notMem h, zero_mul]
  have hYloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → J b * f (L c) = 0 := by
    intro c hc
    rw [hfR _ ((hloc c hc).le.trans (hL c)), mul_zero]
  -- pointwise three-term estimate, by cases on `b + r • c ∈ B`
  have hpt : ∀ c : Euclid n,
      ‖B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖ ≤
        K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) + M * ‖J (b + r • c) - J b‖ +
          J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
    intro c
    have hu := hfM (r⁻¹ • (F (b + r • c) - F b))
    have hv := hfM (L c)
    have hA : 0 ≤ M * ‖J (b + r • c) - J b‖ := mul_nonneg hM0 (norm_nonneg _)
    have hB' : 0 ≤ J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
      mul_nonneg hJb0 (norm_nonneg _)
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), mul_zero,
        zero_add]
      have hJu := mul_le_mul_of_nonneg_left hu (norm_nonneg (J (b + r • c) - J b))
      calc ‖J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖
          = ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b)) +
              J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := by
            congr 1
            ring
        _ ≤ ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b))‖ +
              ‖J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := norm_add_le _ _
        _ = ‖J (b + r • c) - J b‖ * ‖f (r⁻¹ • (F (b + r • c) - F b))‖ +
              J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hJb0]
        _ ≤ M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            linarith [mul_comm M ‖J (b + r • c) - J b‖]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_mul, zero_sub,
        norm_neg, norm_mul, Real.norm_of_nonneg hJb0, mul_one]
      have hJv : J b * ‖f (L c)‖ ≤ K * M := mul_le_mul hJbK hv (norm_nonneg _) hK0
      linarith
  -- integrate the pointwise estimate over `D`
  have h1 : (∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m),
        B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hXloc).symm
  have h2 : J b * (∫ c, f (L c) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m), J b * f (L c) ∂volume := by
    rw [← integral_const_mul]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hYloc).symm
  have hG₁₂ : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖) (closedBall (0 : Euclid n) (R / m)) volume :=
    (hg₁int.const_mul _).add (hg₂int.const_mul _)
  have hG : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume :=
    hG₁₂.add (hg₃int.const_mul _)
  rw [h1, h2, ← integral_sub hXint hYint]
  refine (norm_integral_le_of_norm_le hG (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add hG₁₂ (hg₃int.const_mul _), integral_add (hg₁int.const_mul _) (hg₂int.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
/-- **Rescaled integrals at a point of vanishing ball averages**: for `R > 0`, if
`⨍_{B̄_s(b)} h → 0` as `s → 0⁺`, then `∫_{B̄_R(0)} h(b + rc) dc → 0` as `r → 0⁺`.
For `r > 0`, dilation by `r` and translation by `b` give
`∫_{B̄_R(0)} h(b + rc) dc = r⁻ⁿ ∫_{B̄_{rR}(b)} h = ω Rⁿ ⨍_{B̄_{rR}(b)} h`, `ω = λ(B̄₁(0))`. -/
theorem Submission.pit_integral_closedBall_rescale_tendsto : ∀ (n : ℕ) (h : Euclid n → ℝ) (b : Euclid n) (R : ℝ), 0 < R → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, h a ∂volume) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n h b R hR hlim
  -- `ω = λ(B̄₁(0)) ∈ (0, ∞)` and `λ(B̄_s(z)) = sⁿ ω` for `s ≥ 0`
  set ω : ℝ := volume.real (closedBall (0 : Euclid n) 1) with hω_def
  have hω : 0 < ω := by
    rw [hω_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  have hvol : ∀ (z : Euclid n) {s : ℝ}, 0 ≤ s → volume.real (closedBall z s) = s ^ n * ω := by
    intro z s hs
    rw [Measure.addHaar_real_closedBall' volume z hs, finrank_euclideanSpace_fin]
  -- for `r > 0`: `∫_{B̄_R(0)} h(b + rc) dc = Rⁿ ω ⨍_{B̄_{rR}(b)} h`
  have key : ∀ r : ℝ, 0 < r → ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
      R ^ n * ω * ⨍ a in closedBall b (r * R), h a ∂volume := by
    intro r hr
    set H : Euclid n → ℝ := (closedBall b (r * R)).indicator h with hH
    have hmem : ∀ c : Euclid n, b + r • c ∈ closedBall b (r * R) ↔ c ∈ closedBall (0 : Euclid n) R := by
      intro c
      rw [mem_closedBall, mem_closedBall, dist_self_add_left, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_iff_of_pos_left hr]
    -- `1_{B̄_R(0)}(c) h(b + rc) = H(b + rc)`
    have h1 : ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
        ∫ c, H (b + r • c) ∂volume := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      ext c
      by_cases hc : c ∈ closedBall (0 : Euclid n) R
      · rw [indicator_of_mem hc, hH, indicator_of_mem ((hmem c).2 hc)]
      · rw [indicator_of_notMem hc, hH, indicator_of_notMem (mt (hmem c).1 hc)]
    -- dilation by `r` and translation by `b`
    have h2 : ∫ c, H (b + r • c) ∂volume = (r ^ n)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [Measure.integral_comp_smul volume (fun x => H (b + x)) r, integral_add_left_eq_self H b,
        hH, integral_indicator measurableSet_closedBall, finrank_euclideanSpace_fin, smul_eq_mul,
        abs_of_pos (inv_pos.2 (pow_pos hr n))]
    have h3 : ⨍ a in closedBall b (r * R), h a ∂volume =
        ((r * R) ^ n * ω)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [setAverage_eq, hvol b (mul_pos hr hR).le, smul_eq_mul]
    rw [h1, h2, h3, mul_pow]
    field_simp
  -- `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have hlim' := (hlim.comp hmap).const_mul (R ^ n * ω)
  rw [mul_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (key r hr).symm

/-- **Rescaled integrals at a density point of `B` and a Lebesgue point of `J`**: let
`m|a − b| ≤ |F(a) − F(b)|` on `B`, `m|c| ≤ |Lc|` for `L = DF(b)`, `0 ≤ J ≤ K`, let `B` have
density `1` at `b` and `⨍_{B̄_ρ(b)} |J − J(b)| → 0`.  Then for `f ∈ C_c(ℝᴾ)`,
`∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dc → J(b) ∫ f(Lc) dc` as `r → 0⁺`.
With `f = 0` off `B_R(0)` and `|f| ≤ M`, the error is at most `K M T₁ + M T₂ + J(b) T₃`, where
`T₁, T₂, T₃` integrate `1_{Bᶜ}(b + rc)`, `|J(b + rc) − J(b)|` and
`|f(r⁻¹(F(b + rc) − F(b))) − f(Lc)|` over `B̄_{R/m}(0)`; each tends to `0`. -/
theorem Submission.pit_rescaled_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → (∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖) → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) (𝓝[>] 0) (𝓝 (J b * ∫ c, f (fderiv ℝ F b c) ∂volume)) := by
  intro P n F B J K m b f hF hB hJ hJK hm hFB hdiff hL hdens hLeb hf hfc
  -- `f = 0` off `B_R(0)` and `|f| ≤ M`; the integrals live on `B̄_{R/m}(0)`
  obtain ⟨R, hR, hRf⟩ := hfc.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hRm : 0 < R / m := div_pos hR hm
  -- `T₁ → 0`: `B` has density `1` at `b`
  have hT₁ := Submission.pit_integral_closedBall_rescale_tendsto n
    (Bᶜ.indicator fun _ => (1 : ℝ)) b (R / m) hRm
    (Submission.pit_ril_compl_average_tendsto n B b hB hdens)
  -- `T₂ → 0`: `b` is a Lebesgue point of `J`
  have hT₂ := Submission.pit_integral_closedBall_rescale_tendsto n (fun a => ‖J a - J b‖) b
    (R / m) hRm hLeb
  -- `T₃ → 0`: `r⁻¹(F(b + rc) − F(b)) → Lc` uniformly on `B̄_{R/m}(0)`
  have hT₃ := Submission.pit_ril_diffQuot_integral_tendsto P n F (fderiv ℝ F b) b f (R / m)
    hdiff.hasFDerivAt hf hfc
  have hlim := ((hT₁.const_mul (K * M)).add (hT₂.const_mul M)).add (hT₃.const_mul (J b))
  simp only [mul_zero, add_zero] at hlim
  -- squeeze `|I(r) − J(b) ∫ f(Lc) dc| ≤ K M T₁(r) + M T₂(r) + J(b) T₃(r)` for `r > 0`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Submission.pit_ril_three_term_bound P n F (fderiv ℝ F b) B J K m b f R M r hF hB hJ hJK
    hm hFB hL hf hRf hM hr
/-- Integral over the range of a linear map with constant Jacobian: if `T : ℝⁿ → ℝᴾ` is linear
and `Hⁿ(T(S)) = j λ(S)` for every `S ⊆ ℝⁿ` (`j ≥ 0`, `λ` Lebesgue measure), then for continuous
`f`, `∫_{T(ℝⁿ)} f dHⁿ = j ∫ f(T(c)) dλ(c)`.  On Borel `A`, `A ∩ T(ℝⁿ) = T(T⁻¹(A))`, so
`Hⁿ⌞T(ℝⁿ) = j T_#λ`. -/
theorem Submission.pit_setIntegral_range_linear : ∀ (P n : ℕ) (T : Euclid n →L[ℝ] Euclid P) (j : ℝ) (f : Euclid P → ℝ), 0 ≤ j → (∀ S : Set (Euclid n), μHE[n] (T '' S) = ENNReal.ofReal j * volume S) → Continuous f → ∫ y in (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = j * ∫ c, f (T c) ∂volume := by
  intro P n T j f hj hT hf
  -- the carrier of the submodule `range T` is the set `T(ℝⁿ)`
  have hrange : (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) = range T := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  -- `Hⁿ⌞T(ℝⁿ) = ofReal(j) • T_#λ`, checked on Borel sets
  have hmeas : μHE[n].restrict (range T) = ENNReal.ofReal j • volume.map T := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply T.measurable hA,
      ← image_preimage_eq_inter_range, hT, smul_eq_mul]
  -- change of variables, with `(ofReal j).toReal = j` since `j ≥ 0`
  rw [hrange, hmeas, integral_smul_measure,
    integral_map T.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Simon Ch. 3, 1.4** (approximate tangent spaces of a bi-Lipschitz piece): let `F : ℝⁿ → ℝᴾ`
be `L`-Lipschitz, `B ⊆ ℝⁿ` Borel and `m > 0` with `m|a − a'| ≤ |F a − F a'|` on `B`, and let `F`
be differentiable at every point of `B` with injective derivative.  Then for a.e. `b ∈ B`,
`F(B)` has approximate tangent space `range DF(b)` at `F b`.
With `J := normDet DF` (Borel, `0 ≤ J ≤ Lⁿ`) the injective area formula holds on `B`.  A.e.
`b ∈ B` is a density point of `B` and a Lebesgue point of `J`; there
`∫_{η_{F b,r}(F(B))} f dHⁿ = ∫ 1_B J(b + rc) f(r⁻¹(F(b + rc) − F b)) dc` tends to
`J(b) ∫ f(DF(b)c) dc = ∫_{range DF(b)} f dHⁿ` as `r ↓ 0`. -/
theorem Submission.ptd_piece_image_approxTangent_ae : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n (F '' B) (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F B L m hF hB hm hcolip hreg
  have hfin : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  -- the area Jacobian `J = normDet DF`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid n → ℝ, J = Poincare.SimonGMT.Chapter02.areaJacobianAt F :=
    ⟨_, rfl⟩
  have hJmeas : Measurable J := hJ ▸ Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
  have hJnonneg : ∀ a, 0 ≤ J a := hJ ▸ Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
  -- `Hⁿ(T(S)) = normDet T · λ(S)` for every linear `T`
  have hlin : ∀ (T : Euclid n →L[ℝ] Euclid P) (S : Set (Euclid n)),
      μHE[n] (T '' S) = ENNReal.ofReal (T : Euclid n →ₗ[ℝ] Euclid P).normDet * volume S := by
    intro T S
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (T : Euclid n →ₗ[ℝ] Euclid P) S
    rw [hfin] at h
    simpa using h
  have hJlin : ∀ a (S : Set (Euclid n)),
      μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S := by
    intro a S
    rw [hlin, hJ, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
  -- `J ≤ Lⁿ`: compare `Hⁿ(DF(a)(B̄₁(0)))` with the Lipschitz bound `‖DF(a)‖ ≤ L`
  have hJle : ∀ a, J a ≤ (L : ℝ) ^ n := by
    intro a
    have hTL : ‖fderiv ℝ F a‖₊ ≤ L := by
      have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := a) hF
      exact_mod_cast h
    have hpos : volume (closedBall (0 : Euclid n) 1) ≠ 0 :=
      (measure_closedBall_pos volume (0 : Euclid n) one_pos).ne'
    have hfin' : volume (closedBall (0 : Euclid n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
    have hle : ENNReal.ofReal (J a) * volume (closedBall (0 : Euclid n) 1) ≤
        (L : ℝ≥0∞) ^ n * volume (closedBall (0 : Euclid n) 1) := by
      rw [← hJlin a, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
      calc μHE[n] (fderiv ℝ F a '' closedBall 0 1)
          ≤ (‖fderiv ℝ F a‖₊ : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (fderiv ℝ F a).lipschitzWith.lipschitzOnWith
        _ ≤ (L : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) := by gcongr
    have h2 : ENNReal.ofReal (J a) ≤ (L : ℝ≥0∞) ^ n :=
      (ENNReal.mul_le_mul_iff_left hpos hfin').1 hle
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_pow L.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    exact h2
  -- `F` is injective on `B`, so the area formula holds on `B` with weight `J`
  have hinjOn : InjOn F B := by
    intro a ha a' ha' hFa
    have h := hcolip a ha a' ha'
    rw [hFa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have harea : ∀ g : Euclid P → ℝ≥0∞,
      ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hB hinjOn g
    rw [hfin] at h
    rw [h, hJ]
  -- `J` is bounded and Borel, hence locally integrable
  have hJloc : LocallyIntegrable J volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne hJmeas.aestronglyMeasurable
      (M := (L : ℝ) ^ n) (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hJnonneg a)]
    exact hJle a
  -- a.e. `b ∈ B` is a density point of `B` and a Lebesgue point of `J`
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Euclid n))
    hJloc 1
  filter_upwards [ae_restrict_mem hB, Besicovitch.ae_tendsto_measure_inter_div volume B,
    ae_restrict_of_ae hleb] with b hbB hα hβ
  have hβ' : Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) :=
    hβ (fun _ => b) id tendsto_id (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) =>
      mem_closedBall_self (by simpa using hρ.le))
  obtain ⟨hdb, hinj⟩ := hreg b hbB
  have hcolb : ∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖ := fun a ha => hcolip a ha b hbB
  have hγ : ∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ :=
    Submission.pit_fderiv_lower_bound_of_density P n F B m b hm hcolb hdb hα
  refine ⟨?_, fun f => ?_⟩
  · rw [LinearMap.finrank_range_of_inj (by simpa using hinj), hfin]
  · rw [Submission.pit_setIntegral_range_linear P n (fderiv ℝ F b) (J b) f (hJnonneg b)
      (hJlin b) f.continuous]
    refine (Submission.pit_rescaled_integral_tendsto P n F B J ((L : ℝ) ^ n) m b f hF.continuous
      hB hJmeas (fun a => ⟨hJnonneg a, hJle a⟩) hm hcolb hdb hγ hα hβ' f.continuous
      f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (Submission.pit_blowUp_image_setIntegral_eq_rescaled P n F B J b r f hF.continuous hB
      hJmeas hJnonneg harea hr f.continuous).symm

/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"**, for a bi-Lipschitz piece: let `U` be open,
`Y ⊆ U` Borel with `Hⁿ(Y ∩ C) < ∞` for compact `C ⊆ U`, `F` Lipschitz, `B` Borel with
`m|a − a'| ≤ |F(a) − F(a')|` on `B`, `DF(a)` injective for `a ∈ B`, and `F(B) ⊆ Y`.  Then for
a.e. `b ∈ B`, `Y` has approximate tangent space `range DF(b)` at `F(b)`.  The image `F(B)` itself
has this tangent space at `F(b)` for a.e. `b`; `Y` and its Borel subset `F(B)` have the same
approximate tangent spaces `Hⁿ`-a.e. on `F(B)`; and `Hⁿ⌞F(B)`-null sets pull back along `F` to
Lebesgue-null subsets of `B`. -/
theorem Submission.dpf_approxTangent_ae_bilipschitz_piece : ∀ (P n : ℕ) (U Y : Set (Euclid P)) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → MeasurableSet Y → Y ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (Y ∩ C) ≠ ∞) → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ Y → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n U Y F B L m hU hY hYU hfin hF hB hm hbi hdiff hFBY
  -- Step 0(a)–(b): `F(B)` is Borel; `Hⁿ⌞F(B)`-a.e. properties hold at `F(b)` for a.e. `b ∈ B`
  obtain ⟨hA, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback P n F B L m hF hB hm hbi
  -- Steps 1–3 and 6: `Hⁿ`-a.e. on `F(B)`, `Y` and `F(B)` have the same approximate tangent spaces
  have hloc := Submission.ptd_ae_approxTangent_iff_of_subset P n U (F '' B) Y hU hA hY hFBY hYU hfin
  -- Steps 4, 5 and 7: `F(B)` has approximate tangent space `range DF(b)` at `F(b)` for a.e. `b ∈ B`
  filter_upwards [hpull _ hloc,
    Submission.ptd_piece_image_approxTangent_ae P n F B L m hF hB hm hbi hdiff] with b hYA hA'
  exact (hYA _).2 hA'
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable

/-- **Algebra of unit orientations** (Simon 6.1.1, 6.1.7, 6.2.2): for `n`-vectors on `ℝᴾ`,
(a) two unit orientations `ξ`, `ξ'` of the same subspace `T` agree up to sign, `ξ' = ±ξ`;
(b) a unit orientation `ξ` satisfies `|ξ(β)| ≤ ‖β‖` for every `n`-covector `β`;
(c) if `A : ℝⁿ → ℝᴾ` is injective, then `J_A = det(⟨Aeₖ, Aeₗ⟩)^{1/2} > 0` and
`J_A⁻¹ A_#e : β ↦ J_A⁻¹ β(Ae₁, …, Aeₙ)` is a unit orientation of `range A`;
(d) if `A` is not injective, then `β(Ae₁, …, Aeₙ) = 0` for every `n`-covector `β`.
For an orthonormal `τ` and `bⱼ ∈ span τ`, with `M = (⟨τᵢ, bⱼ⟩)`, `α(b) = det M · α(τ)` (expand
`α` in the basis `τ` of `span τ`) and `det(⟨bₖ, bₗ⟩) = (det M)²` (Parseval).  Two orthonormal
frames of `T` therefore differ by `det M = ±1`; for injective `A`, a Gram–Schmidt frame `τ` of
`range A` gives an invertible `M` and `J_A = |det M|`; a non-injective `A` makes `(Aeₖ)` linearly
dependent. -/
theorem Submission.dtc_bc_lc_pfi_unitOrientation_algebra : ∀ (P n : ℕ), (∀ (ξ ξ' : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → IsUnitOrientationOf ξ' T → ξ' = ξ ∨ ξ' = -ξ) ∧ (∀ (ξ : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → ∀ β : Covector (Euclid P) n, |ξ β| ≤ ‖β‖) ∧ (∀ A : Euclid n →L[ℝ] Euclid P, Injective A → 0 < Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) ∧ IsUnitOrientationOf ((Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))))⁻¹ • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun k : Fin n => A (EuclideanSpace.single k 1))) (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P))) ∧ ∀ A : Euclid n →L[ℝ] Euclid P, ¬ Injective A → ∀ β : Covector (Euclid P) n, β (fun k : Fin n => A (EuclideanSpace.single k 1)) = 0 := by
  intro P n
  -- Step 1 (expansion): for orthonormal `τ` and `bⱼ ∈ span τ`, `α(b) = det(⟨τᵢ, bⱼ⟩) α(τ)`
  have hE : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n,
        α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
    intro τ b hτ hb α
    set L := Submodule.span ℝ (Set.range τ)
    -- `τ` is a basis `e` of `L`
    let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
    have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
      rw [Module.Basis.span_apply hτ.linearIndependent i]
    -- the restriction `α_L` of `α` to `L`
    let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
    let b' : Fin n → L := fun j => ⟨b j, hb j⟩
    have h1 : α b = αL b' := rfl
    have h2 : α τ = αL e := by
      show α τ = α (fun i => (e i : Euclid P))
      congr 1
      funext i
      exact (he i).symm
    -- coordinates of `b'` in `e` are the inner products with `τ`
    have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
      intro i j
      have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
        have := congrArg (Subtype.val) (e.sum_repr (b' j))
        simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
        exact this.symm
      rw [hs, hτ.inner_right_fintype]
    have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
      ext i j
      rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
    -- `α_L = α_L(e) • det_e`
    have h3 : αL b' = αL e * e.det b' := by
      conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
      rfl
    rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
  -- Step 2 (coordinates): for orthonormal `τ` and `bⱼ ∈ span τ`, `bⱼ = Σᵢ ⟨τᵢ, bⱼ⟩ τᵢ`
  have hcoord : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ j, b j = ∑ i, inner ℝ (τ i) (b j) • τ i := by
    intro τ b hτ hb j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hb j)
    have hci : ∀ i, inner ℝ (τ i) (b j) = c i := fun i => by rw [← hc, hτ.inner_right_fintype]
    calc b j = ∑ i, c i • τ i := hc.symm
      _ = ∑ i, inner ℝ (τ i) (b j) • τ i := Finset.sum_congr rfl fun i _ => by rw [hci i]
  -- Step 3 (Parseval): `(⟨bₖ, bₗ⟩) = MᵀM` for `M = (⟨τᵢ, bⱼ⟩)`, so `det(⟨bₖ, bₗ⟩) = (det M)²`
  have hG : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) →
        (Matrix.of fun k l => inner ℝ (b k) (b l)).det =
          (Matrix.of fun i j => inner ℝ (τ i) (b j)).det ^ 2 := by
    intro τ b hτ hb
    have hmat : (Matrix.of fun k l => inner ℝ (b k) (b l)) =
        (Matrix.of fun i j => inner ℝ (τ i) (b j)).transpose *
          Matrix.of fun i j => inner ℝ (τ i) (b j) := by
      ext k l
      rw [Matrix.mul_apply, Matrix.of_apply]
      conv_lhs => rw [hcoord τ b hτ hb k]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
    rw [hmat, Matrix.det_mul, Matrix.det_transpose, sq]
  -- Step 4: the standard basis `eₖ = single k 1` of `ℝⁿ` is independent and spanning
  have he_fun : ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
      fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n) := by
    rw [OrthonormalBasis.coe_toBasis]
    funext k
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ k
  have he_li : LinearIndependent ℝ (fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n)) := by
    have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    rwa [he_fun] at this
  have he_span :
      Submodule.span ℝ (Set.range fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n)) = ⊤ := by
    have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
    rwa [he_fun] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) `τ'` lies in `span τ`, so `α(τ') = det O · α(τ)` with `(det O)² = det 1 = 1`
    rintro ξ ξ' T ⟨τ, hτ, hτT, hξ⟩ ⟨τ', hτ', hτ'T, hξ'⟩
    have hmem : ∀ j, τ' j ∈ Submodule.span ℝ (Set.range τ) := fun j => by
      rw [hτT, ← hτ'T]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨d, hexp, hd⟩ : ∃ d : ℝ, (∀ α : Covector (Euclid P) n, α τ' = d * α τ) ∧ d ^ 2 = 1 := by
      refine ⟨_, hE τ τ' hτ hmem, ?_⟩
      rw [← hG τ τ' hτ hmem]
      have h1 : (Matrix.of fun k l => inner ℝ (τ' k) (τ' l)) = 1 := by
        ext k l
        rw [Matrix.of_apply, Matrix.one_apply]
        exact orthonormal_iff_ite.mp hτ' k l
      rw [h1, Matrix.det_one]
    -- the signs `s, s' = ±1` of `ξ = s τ` and `ξ' = s' τ'`
    obtain ⟨s, hs, hξs⟩ : ∃ s : ℝ, s * s = 1 ∧ ∀ α, ξ α = s * α τ := by
      rcases hξ with h | h
      · exact ⟨1, one_mul 1, fun α => by rw [h, one_mul]⟩
      · exact ⟨-1, by norm_num, fun α => by rw [h, neg_one_mul]⟩
    obtain ⟨s', hs', hξs'⟩ : ∃ s : ℝ, s * s = 1 ∧ ∀ α, ξ' α = s * α τ' := by
      rcases hξ' with h | h
      · exact ⟨1, one_mul 1, fun α => by rw [h, one_mul]⟩
      · exact ⟨-1, by norm_num, fun α => by rw [h, neg_one_mul]⟩
    -- `ξ' = c ξ` with `c = s' · det O · s` and `c² = 1`
    have hc : ∀ α : Covector (Euclid P) n, ξ' α = (s' * d * s) * ξ α := by
      intro α
      rw [hξs' α, hexp α, hξs α]
      linear_combination (-(s' * d * α τ)) * hs
    have hc1 : (s' * d * s) * (s' * d * s) = 1 := by
      linear_combination (s' * s' * d ^ 2) * hs + (s' * s') * hd + hs'
    rcases mul_self_eq_one_iff.mp hc1 with h | h
    · left
      exact ContinuousLinearMap.ext fun α => by rw [hc α, h, one_mul]
    · right
      exact ContinuousLinearMap.ext fun α => by rw [hc α, h, neg_apply, neg_one_mul]
  · -- (b) `|ξ(β)| = |β(τ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖`
    rintro ξ T ⟨τ, hτ, -, hξ⟩ β
    have h1 : |β τ| ≤ ‖β‖ := by
      have h := β.le_opNorm τ
      rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h β]
      exact h1
    · rw [h β, abs_neg]
      exact h1
  · -- (c) a Gram–Schmidt frame `τ` of `range A = span (Aeₖ)`, and `M = (⟨τᵢ, Aeⱼ⟩)`
    intro A hA
    set v : Fin n → Euclid P := fun k => A (EuclideanSpace.single k 1) with hv_def
    have hv : LinearIndependent ℝ v :=
      he_li.map' (A : Euclid n →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.mpr hA)
    have hspan_v :
        Submodule.span ℝ (Set.range v) = LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P) := by
      rw [LinearMap.range_eq_map, ← he_span, Submodule.map_span, ← Set.range_comp]
      rfl
    obtain ⟨τ, hτ, hτspan⟩ : ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
        Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range v) :=
      ⟨InnerProductSpace.gramSchmidtNormed ℝ v, InnerProductSpace.gramSchmidtNormed_orthonormal hv,
        by rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]⟩
    have hvmem : ∀ j, v j ∈ Submodule.span ℝ (Set.range τ) := fun j => by
      rw [hτspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    -- `M` is invertible: `M c = 0` gives `Σⱼ cⱼ vⱼ = Σᵢ (M c)ᵢ τᵢ = 0`, so `c = 0`
    have hMne : (Matrix.of fun i j => inner ℝ (τ i) (v j)).det ≠ 0 := by
      intro h0
      obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hc0
      funext j
      refine Fintype.linearIndependent_iff.mp hv c ?_ j
      calc ∑ j, c j • v j = ∑ j, c j • ∑ i, inner ℝ (τ i) (v j) • τ i :=
            Finset.sum_congr rfl fun j _ => by rw [← hcoord τ v hτ hvmem j]
        _ = ∑ i, (∑ j, inner ℝ (τ i) (v j) * c j) • τ i := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [mul_comm]
        _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            have := congrFun hc i
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
            rw [this, zero_smul]
    obtain ⟨d, hd0, hexp, hgram⟩ : ∃ d : ℝ, d ≠ 0 ∧ (∀ α : Covector (Euclid P) n, α v = d * α τ) ∧
        (Matrix.of fun k l => inner ℝ (v k) (v l)).det = d ^ 2 :=
      ⟨_, hMne, hE τ v hτ hvmem, hG τ v hτ hvmem⟩
    -- `J_A = ((det M)²)^{1/2} = |det M| > 0` and `J_A⁻¹ β(Ae) = sign(det M) β(τ)`
    have hJ : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n =>
        inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) = |d| := by
      rw [← Real.sqrt_sq_eq_abs, ← hgram]
    rw [hJ]
    refine ⟨abs_pos.mpr hd0, τ, hτ, hτspan.trans hspan_v, ?_⟩
    have hval : ∀ α : Covector (Euclid P) n,
        (|d|⁻¹ • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v) α = (|d|⁻¹ * d) * α τ := by
      intro α
      rw [smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul, hexp α, mul_assoc]
    rcases lt_or_gt_of_ne hd0 with hneg | hpos
    · right
      intro α
      rw [hval, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd0, neg_one_mul]
    · left
      intro α
      rw [hval, abs_of_pos hpos, inv_mul_cancel₀ hd0, one_mul]
  · -- (d) if `(Aeₖ)` were independent, `A` would be injective (`e` spans `ℝⁿ`)
    intro A hA β
    have hdep : ¬ LinearIndependent ℝ (fun k : Fin n => A (EuclideanSpace.single k 1)) := fun hli =>
      hA (LinearMap.injective_of_linearIndependent (f := (A : Euclid n →ₗ[ℝ] Euclid P)) he_span hli)
    exact β.toAlternatingMap.map_linearDependent _ hdep
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- Vector density of a sum (step 1 of the competitor mass bound in the proof of Simon Ch. 7,
2.4 (8)–(9)).  Let `U` be open, `R = (M, θ, ξ)` represent `T`, and `T = τ(M₁, θ₁, ξ₁) +
τ(M₂, θ₂, ξ₂)` on `𝒟ⁿ(U)`.  Then `1_M θ ξ = 1_{M₁} θ₁ ξ₁ + 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Simon Ch. 6,
3.2(1) with `p₁ = p₂ = 1` gives an IMRep `R' = (M', θ', ξ')` with `1_{M'} θ' ξ' = 1_{M₁} θ₁ ξ₁ +
1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e., so `τ(R') = τ(R₁) + τ(R₂) = T`.  Uniqueness of the vector density
(3.2(3)) gives `1_{M'} θ' ξ' = 1_M θ ξ` `Hⁿ`-a.e. on `M' ∪ M`, and off `M' ∪ M` both vanish. -/
theorem Submission.dor_lmb_pc_cm_vector_density_add : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (T : GeometricCurrentOn U n), IsOpen U → R.Represents T → (∀ ω : TestFormOn U n, T ω = R₁.action (ω : DifferentialForm (Euclid P) n) + R₂.action (ω : DifferentialForm (Euclid P) n)) → ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ R T hU hR hT
  -- Step 1: an IMRep `R'` with `1_{M'} θ' ξ' = 1_{M₁} θ₁ ξ₁ + 1_{M₂} θ₂ ξ₂` a.e.
  obtain ⟨R', hR'⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ 1 1 hU
  -- Step 2: `τ(R') = τ(R₁) + τ(R₂) = T`
  have hR'T : R'.Represents T := by
    intro ω
    rw [hT ω, Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R' 1 1 hR' ω]
    simp only [Int.cast_one, one_mul]
  -- Step 3: `1_{M'} θ' ξ' = 1_M θ ξ` `Hⁿ`-a.e. on `M' ∪ M`
  have hR'R := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R' R hU hR'T hR
  rw [ae_restrict_iff' (R'.measurableSet_carrier.union R.measurableSet_carrier)] at hR'R
  filter_upwards [hR'R, hR'] with x hx hx'
  -- Step 4: hence `1_M θ ξ = 1_{M'} θ' ξ'` at `x`, as off `M' ∪ M` both indicators vanish
  have hxR : R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
      R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x := by
    by_cases hxs : x ∈ R'.carrier ∪ R.carrier
    · exact (hx hxs).symm
    · have h₁ : x ∉ R'.carrier := fun h => hxs (Or.inl h)
      have h₂ : x ∉ R.carrier := fun h => hxs (Or.inr h)
      rw [indicator_of_notMem h₂, indicator_of_notMem h₁]
  -- Step 5: combine with step 1
  rw [hxR, hx']
  simp only [Int.cast_one, one_smul]
/-- **Simon Ch. 6, Definition 3.1, from an integer density**: let `N ⊆ U` be Borel and countably
`n`-rectifiable with `Hⁿ(N ∩ K) < ∞` for compact `K ⊆ U`, let `η` orient the approximate tangent
spaces of `N` `Hⁿ`-a.e. on `N`, and let `m` be integer-valued with `∫_{N ∩ K} |m| dHⁿ < ∞` for
compact `K ⊆ U`.  Then `(N', |m|, sign(m) η)`, `N' = N ∩ {m ≠ 0}`, is an `IMRep` in `U` acting by
`ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ`.

Proof sketch:
* `N' ⊆ N` is Borel and countably `n`-rectifiable; `⌊|m|⌋₊ = |m|` is measurable, positive on `N'`
  and locally integrable; `sign(m) η` is strongly measurable.
* By locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)), for `Hⁿ`-a.e.
  `x ∈ N'` a tangent space `Q` of `N` at `x` is one of `N'`, and `±η(x)` still orients `Q`.
* Pointwise on `N`, `1_{N'} |m| ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩`, so the two integrals agree. -/
theorem Submission.cmcdt_ims_imrep_of_int_density : ∀ (P n : ℕ) (U N : Set (Euclid P)) (η : Euclid P → MultiVector P n) (m : Euclid P → ℝ), IsOpen U → MeasurableSet N → N ⊆ U → CountablyRectifiable n N → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞) → StronglyMeasurable η → Measurable m → (∀ x, ∃ z : ℤ, m x = z) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict N), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R : IMRep U n, ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ x in N, m x * η x (ω x) ∂μHE[n] := by
  intro P n U N η m hU hN hNU hrect hfin hη hm hint hloc hor
  classical
  -- Step 1: the carrier `N' = N ∩ {m ≠ 0}`
  set N' : Set (Euclid P) := N ∩ {x | m x ≠ 0}
  have hN'meas : MeasurableSet N' :=
    hN.inter ((measurableSet_singleton (0 : ℝ)).preimage hm).compl
  have hN'N : N' ⊆ N := inter_subset_left
  -- Steps 2–3: the multiplicity `⌊|m|⌋₊ = |m|` and the orientation `sign(m) η`
  set mult : Euclid P → ℕ := fun x => ⌊|m x|⌋₊ with hmultdef
  set orient : Euclid P → MultiVector P n := fun x => if m x < 0 then -η x else η x with horientdef
  have hmult_cast : ∀ x, ((mult x : ℕ) : ℝ) = |m x| := by
    intro x
    obtain ⟨z, hz⟩ := hint x
    simp only [hmultdef, hz]
    rw [show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs]]
    rw [Nat.floor_natCast]
  have hmult_meas : Measurable mult :=
    (Nat.floor_mono.measurable).comp (continuous_abs.measurable.comp hm)
  have hmult_pos : ∀ x ∈ N', 0 < mult x := by
    intro x hx
    have hx0 : m x ≠ 0 := hx.2
    have h1 : (0 : ℝ) < ((mult x : ℕ) : ℝ) := by
      rw [hmult_cast]; exact abs_pos.mpr hx0
    exact_mod_cast h1
  have horient_sm : StronglyMeasurable orient := by
    have hset : MeasurableSet {x | m x < 0} := measurableSet_lt hm measurable_const
    have hneg : StronglyMeasurable (fun x => -η x) := by
      have := hη.const_smul (-1 : ℝ)
      convert this using 1
      funext x
      exact (neg_one_smul ℝ (η x)).symm
    exact StronglyMeasurable.ite hset hneg hη
  -- Step 4: local integrability, `∫_{N' ∩ K} ⌊|m|⌋₊ ≤ ∫_{N ∩ K} |m| < ∞`
  have hloc' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hloc K hK hKU) ?_
    calc ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in N ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left _ hN'N)
      _ ≤ ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs, ← hmult_cast x, ENNReal.ofReal_natCast]
  -- Step 5: tangent spaces of `N` are tangent spaces of `N'` a.e. on `N'`, and `±η` orients them
  have hor' : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N' x Q ∧ IsUnitOrientationOf (orient x) Q := by
    have h1 := Submission.rsdic_ae_tangent_iff_of_subset P n U N' N hU hN'meas hN hN'N hNU hfin
    have h2 : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q :=
      ae_restrict_of_ae_restrict_of_subset hN'N hor
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx2
    refine ⟨Q, (hx1 Q).1 hQ1, ?_⟩
    simp only [horientdef]
    split_ifs
    · obtain ⟨τ, hτ, hspan, hξ⟩ := hQ2
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hξ with h | h
      · right; intro α; simp [h]
      · left; intro α; simp [h]
    · exact hQ2
  -- Step 6: the `IMRep`
  let R : IMRep U n :=
    { carrier := N'
      mult := mult
      orient := orient
      measurableSet_carrier := hN'meas
      carrier_subset := hN'N.trans hNU
      rectifiable := hrect.mono hN'N
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hloc'
      aestronglyMeasurable_orient := horient_sm.aestronglyMeasurable
      orients := hor' }
  refine ⟨R, ?_⟩
  -- Step 7: the action, from `1_{N'} ⌊|m|⌋₊ ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩` pointwise on `N`
  intro ω
  show ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] = ∫ x in N, m x * η x (ω x) ∂μHE[n]
  have hpt : ∀ x ∈ N,
      N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x = m x * η x (ω x) := by
    intro x hx
    by_cases hx0 : m x = 0
    · have : x ∉ N' := fun h => h.2 hx0
      simp [this, hx0]
    · have hxN' : x ∈ N' := ⟨hx, hx0⟩
      rw [indicator_of_mem hxN', hmult_cast]
      simp only [horientdef]
      split_ifs with hneg
      · rw [abs_of_neg hneg]; simp
      · rw [abs_of_nonneg (not_lt.mp hneg)]
  calc ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n]
      = ∫ x in N ∩ N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] := by
        rw [inter_eq_right.mpr hN'N]
    _ = ∫ x in N, N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x ∂μHE[n] :=
        (setIntegral_indicator hN'meas).symm
    _ = ∫ x in N, m x * η x (ω x) ∂μHE[n] := setIntegral_congr_fun hN hpt
/-- **`C¹` cut-off with a global Lipschitz bound** (step 1(b) of the integer multiplicity
push-forward).  If `f` is `C¹` on an open `O ⊇ K`, `K` compact, then `φ = id + χ (f − id)` is `C¹`
on `ℝᴾ`, globally Lipschitz, and agrees with `f` to first order on `K`; here `χ ∈ [0, 1]` is a
smooth cut-off with `χ = 1` exactly on `cthickening δ K` and `support χ = thickening (2δ) K`, where
`cthickening (3δ) K ⊆ O`.  `Dφ` is continuous and equals `id` off the compact set `spt χ`, so it
is bounded, and the mean value inequality makes `φ` Lipschitz. -/
theorem Submission.dtc_bc_lc_pfi_c1_cutoff_lipschitz : ∀ (P : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → IsCompact K → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (φ : Euclid P → Euclid P) (Λ : NNReal), ContDiff ℝ 1 φ ∧ LipschitzWith Λ φ ∧ ∀ x ∈ K, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x := by
  intro P O K f hO hK hKO hf
  -- Step 1: a margin `cthickening (3δ) K ⊆ O`
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 3 * δ = ε := ⟨ε / 3, by positivity, by ring⟩
  -- Step 2: the cut-off `χ`, equal to `1` exactly on `cthickening δ K`, with
  -- `support χ = thickening (2δ) K`
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
    (isOpen_thickening (δ := 2 * δ) (E := K)) (isClosed_cthickening (δ := δ) (E := K))
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
  have hχ' : ContDiff ℝ 1 χ := hχ
  have htsupp : tsupport χ ⊆ cthickening (2 * δ) K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  have htO : tsupport χ ⊆ O := htsupp.trans ((cthickening_mono (by linarith) K).trans hεO)
  have htcpt : IsCompact (tsupport χ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) htsupp
  have hχK : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, χ y = 1 := fun x hx =>
    Filter.mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx))
      fun y hy => (hχ1 y).1 (thickening_subset_cthickening δ K hy)
  -- Step 3: `φ = id + χ (f − id)`; it is the identity near every point off `spt χ`
  set φ : Euclid P → Euclid P := fun x => x + χ x • (f x - x) with hφdef
  have hφid : ∀ x, x ∉ tsupport χ → φ =ᶠ[𝓝 x] id := by
    intro x hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    have hy' : χ y = 0 := hy
    simp [hφdef, hy']
  -- Step 4: `φ` is `C¹`
  have hφ : ContDiff ℝ 1 φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact contDiffAt_id.add
        (hχ'.contDiffAt.smul ((hf.contDiffAt (hO.mem_nhds hx)).sub contDiffAt_id))
    · exact contDiffAt_id.congr_of_eventuallyEq (hφid x fun h => hx (htO h))
  -- Step 6: `‖Dφ‖ ≤ max 1 C`, so `φ` is Lipschitz
  obtain ⟨C, hC⟩ :=
    htcpt.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨φ, (max 1 C).toNNReal, hφ, ?_, ?_⟩
  · refine lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable one_ne_zero) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (zero_le_one.trans (le_max_left _ _))]
    by_cases hx : x ∈ tsupport χ
    · exact (hC x hx).trans (le_max_right _ _)
    · rw [(hφid x hx).fderiv_eq, fderiv_id]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
  -- Step 5: `φ = f` near each point of `K`
  · intro x hx
    have heq : φ =ᶠ[𝓝 x] f := by
      filter_upwards [hχK x hx] with y hy
      simp [hφdef, hy]
    exact ⟨heq.eq_of_nhds, heq.fderiv_eq⟩
/-- **Area change of variables for injective maps.**  Write `J_T = √det(⟨T eₖ, T eₗ⟩)` for linear
`T : ℝⁿ → ℝᴾ`.  (I) For injective `T` the area formula gives `Hⁿ(T(S)) = J_T |S|`; on the unit
ball the Lipschitz bound `Hⁿ(L(X)) ≤ ‖L‖ⁿ Hⁿ(X)` gives `J_{L∘A} ≤ ‖L‖ⁿ J_A`.  (II) Let `F` be
differentiable with injective `DF` at every point of the Borel set `B` and injective on `B`, and
`J(x) = J_{DF(x)}`.  `F(B)` is Borel (Lusin–Souslin).  For Borel `S`, `(invFunOn F B)⁻¹(S)` is
`F(B ∩ S)` together with `F(B)ᶜ` if `S` contains the default value, so `invFunOn F B` is Borel.
A Borel `Hⁿ⌞F(B)`-null `Z` has `∫_B J · 1_Z ∘ F = Hⁿ(Z ∩ F(B)) = 0`, and `J > 0` on `B`, so
`F⁻¹(Z)` is null in `B`.  The area formula for `‖h‖ₑ`, `h⁺` and `h⁻` gives the integrability
criterion and the integral identity; if `h` is not integrable both integrals vanish. -/
theorem Submission.dtc_bc_lc_pfi_area_change_of_variables : ∀ (P n : ℕ), (∀ (A : Euclid n →L[ℝ] Euclid P) (L : Euclid P →L[ℝ] Euclid P), Injective (L.comp A) → Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ ((L.comp A) (EuclideanSpace.single k 1)) ((L.comp A) (EuclideanSpace.single l 1)))) ≤ ‖L‖ ^ n * Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1))))) ∧ ∀ (F : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ x ∈ B, DifferentiableAt ℝ F x ∧ Injective (fderiv ℝ F x)) → InjOn F B → MeasurableSet (F '' B) ∧ Measurable (Function.invFunOn F B) ∧ (∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ x ∂(volume.restrict B), p (F x)) ∧ ∀ h : Euclid P → ℝ, AEStronglyMeasurable h (μHE[n].restrict (F '' B)) → (IntegrableOn h (F '' B) μHE[n] ↔ IntegrableOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x)) B) ∧ ∫ y in F '' B, h y ∂μHE[n] = ∫ x in B, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x) := by
  intro P n
  -- `G T = √det(⟨T eₖ, T eₗ⟩)`, the Gram-determinant Jacobian of a linear `T : ℝⁿ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid n →L[ℝ] Euclid P) → ℝ, ∀ T, G T = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin n => inner ℝ (T (EuclideanSpace.single k 1)) (T (EuclideanSpace.single l 1)))) :=
    ⟨_, fun T => rfl⟩
  have harea := Submission.codim1_lura_gram_area_formula n P
  simp only [← hG] at harea ⊢
  have hG0 : ∀ T, 0 ≤ G T := fun T => by rw [hG]; exact Real.sqrt_nonneg _
  -- `J_T > 0` for injective `T` (orient_algebra (c))
  have hGpos : ∀ T : Euclid n →L[ℝ] Euclid P, Injective T → 0 < G T := fun T hT => by
    rw [hG]
    exact ((Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n).2.2.1 T hT).1
  -- linear area identity: `Hⁿ(T(S)) = J_T |S|` for injective `T` and Borel `S`
  have hlin : ∀ T : Euclid n →L[ℝ] Euclid P, Injective T → ∀ S : Set (Euclid n),
      MeasurableSet S → μHE[n] (T '' S) = ENNReal.ofReal (G T) * volume S := by
    intro T hT S hS
    simpa only [ContinuousLinearMap.fderiv, mul_one, setLIntegral_one, setLIntegral_const] using
      (harea T).2 S hS (fun x _ => T.differentiableAt) (fun x _ => by rwa [T.fderiv]) hT.injOn
        fun _ => 1
  refine ⟨fun A L hLA => ?_, fun F B hB hF hinj => ?_⟩
  · -- (I): compare the images of the unit ball under `L ∘ A` and `A`
    have hA : Injective A := fun x y hxy => hLA (by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hxy])
    have hle : μHE[n] ((L.comp A) '' ball 0 1) ≤ (‖L‖₊ : ℝ≥0∞) ^ n * μHE[n] (A '' ball 0 1) := by
      rw [ContinuousLinearMap.coe_comp, image_comp]
      exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        L.lipschitzWith.lipschitzOnWith
    rw [hlin _ hLA _ measurableSet_ball, hlin _ hA _ measurableSet_ball, ← mul_assoc,
      ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
        measure_ball_lt_top.ne] at hle
    refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg (norm_nonneg L) n) (hG0 A))).1 ?_
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg L) n), ENNReal.ofReal_pow (norm_nonneg L),
      ofReal_norm, enorm_eq_nnnorm]
    exact hle
  have hcont : ContinuousOn F B := fun x hx => (hF x hx).1.continuousAt.continuousWithinAt
  have hFae : AEMeasurable F (volume.restrict B) := hcont.aemeasurable hB
  have hJ : Measurable fun x => G (fderiv ℝ F x) := (harea F).1
  have hAF := (harea F).2 B hB (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2) hinj
  -- (i) Lusin–Souslin: images of Borel subsets of `B` are Borel
  have himage : ∀ S, MeasurableSet S → S ⊆ B → MeasurableSet (F '' S) :=
    fun S hS hSB => hS.image_of_continuousOn_injOn (hcont.mono hSB) (hinj.mono hSB)
  -- (ii) `(invFunOn F B)⁻¹(S) = F(B ∩ S) ∪ (F(B)ᶜ ∩ {_ | c ∈ S})`, `c` the default value
  have hψ : Measurable (Function.invFunOn F B) := by
    intro S hS
    obtain ⟨c, hc⟩ : ∃ c, ∀ y, y ∉ F '' B → Function.invFunOn F B y = c :=
      ⟨_, fun y hy => Function.invFunOn_neg hy⟩
    have heq : Function.invFunOn F B ⁻¹' S = F '' (B ∩ S) ∪ (F '' B)ᶜ ∩ {_y | c ∈ S} := by
      ext y
      by_cases hy : y ∈ F '' B
      · obtain ⟨x, hx, rfl⟩ := hy
        rw [mem_preimage, hinj.leftInvOn_invFunOn hx]
        constructor
        · exact fun hxS => Or.inl ⟨x, ⟨hx, hxS⟩, rfl⟩
        · rintro (⟨x', ⟨hx', hx'S⟩, hx'x⟩ | ⟨hFx, -⟩)
          · rwa [← hinj hx' hx hx'x]
          · exact absurd (mem_image_of_mem F hx) hFx
      · rw [mem_preimage, hc y hy]
        constructor
        · exact fun hcS => Or.inr ⟨hy, hcS⟩
        · rintro (⟨x', ⟨hx', -⟩, rfl⟩ | ⟨-, hcS⟩)
          · exact absurd (mem_image_of_mem F hx') hy
          · exact hcS
    rw [heq]
    exact (himage _ (hB.inter hS) inter_subset_left).union
      ((himage B hB Subset.rfl).compl.inter (MeasurableSet.const _))
  -- (iii) `Hⁿ⌞F(B)`-null sets pull back to null subsets of `B`, since `J > 0` on `B`
  have hnull : ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) →
      ∀ᵐ x ∂(volume.restrict B), p (F x) := by
    intro p hp
    obtain ⟨Z, hpZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hp)
    have h0 : ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ F x)) * Z.indicator 1 (F x) = 0 := by
      rw [← hAF (Z.indicator 1), lintegral_indicator_one hZ, hZ0]
    have h1 := (lintegral_eq_zero_iff' (hJ.ennreal_ofReal.aemeasurable.mul
      ((measurable_one.indicator hZ).comp_aemeasurable hFae))).1 h0
    filter_upwards [h1, ae_restrict_mem hB] with x hx hxB
    by_contra hpx
    have hZx : Z.indicator (1 : Euclid P → ℝ≥0∞) (F x) = 1 := indicator_of_mem (hpZ hpx) _
    simp only [Pi.mul_apply, Pi.zero_apply, comp_apply, hZx, mul_one, ENNReal.ofReal_eq_zero] at hx
    exact absurd hx (not_le.2 (hGpos _ (hF x hxB).2))
  refine ⟨himage B hB Subset.rfl, hψ, hnull, fun h hh => ?_⟩
  -- `x ↦ J(x) h(F(x))` is a.e. strongly measurable on `B`: replace `h` by a Borel version
  have hmeas : AEStronglyMeasurable (fun x => G (fderiv ℝ F x) * h (F x)) (volume.restrict B) := by
    refine (hJ.aemeasurable.mul (hh.stronglyMeasurable_mk.measurable.comp_aemeasurable
      hFae)).aestronglyMeasurable.congr ?_
    filter_upwards [hnull (fun y => hh.mk h y = h y) hh.ae_eq_mk.symm] with x hx
    simp only [Pi.mul_apply, comp_apply, hx]
  -- `∫⁻_{F(B)} ‖h‖ₑ dHⁿ = ∫⁻_B ‖J · h ∘ F‖ₑ`
  have hnorm : ∫⁻ y in F '' B, ‖h y‖ₑ ∂μHE[n] = ∫⁻ x in B, ‖G (fderiv ℝ F x) * h (F x)‖ₑ := by
    rw [hAF]
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, Real.enorm_of_nonneg (hG0 _)]
  have hint : IntegrableOn h (F '' B) μHE[n] ↔
      IntegrableOn (fun x => G (fderiv ℝ F x) * h (F x)) B := by
    refine ⟨fun hi => ⟨hmeas, ?_⟩, fun hi => ⟨hh, ?_⟩⟩
    · rw [hasFiniteIntegral_iff_enorm, ← hnorm]
      exact hi.2
    · rw [hasFiniteIntegral_iff_enorm, hnorm]
      exact hi.2
  refine ⟨hint, ?_⟩
  by_cases hi : IntegrableOn h (F '' B) μHE[n]
  · -- area formula for `h⁺` and `h⁻`
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi.integrable,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint.1 hi).integrable, hAF, hAF]
    have e1 : ∀ x, ENNReal.ofReal (G (fderiv ℝ F x)) * ENNReal.ofReal (h (F x)) =
        ENNReal.ofReal (G (fderiv ℝ F x) * h (F x)) := fun x =>
      (ENNReal.ofReal_mul (hG0 _)).symm
    have e2 : ∀ x, ENNReal.ofReal (G (fderiv ℝ F x)) * ENNReal.ofReal (-h (F x)) =
        ENNReal.ofReal (-(G (fderiv ℝ F x) * h (F x))) := fun x => by
      rw [← ENNReal.ofReal_mul (hG0 _), mul_neg]
    simp only [e1, e2]
  · rw [integral_undef hi, integral_undef fun h' => hi (hint.2 h')]

/-- **Simon Ch. 3, Lemma 1.2, refined for the push-forward of Ch. 6, 3.4–3.6**: for a
differentiable `φ : ℝᴾ → ℝᴾ`, a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null
set, the disjoint union of Borel pieces `Gⱼ(Aⱼ) ⊆ M` as in `dpf_rectifiable_bilipschitz_pieces`
such that on each piece either `φ ∘ Gⱼ` is bi-Lipschitz with injective derivative (Simon's `M₊`,
where `J^M φ > 0`) or `D(φ ∘ Gⱼ)` is nowhere injective (where `J^M φ = 0`, 3.4).  Each piece
`Fᵢ(Bᵢ)` of `dpf_rectifiable_bilipschitz_pieces` is split into the Borel critical set
`{a ∈ Bᵢ : D(φ ∘ Fᵢ)(a) not injective}` and Mathlib's partition of the rest into sets on which
`φ ∘ Fᵢ` is close to an injective linear map, hence bi-Lipschitz. -/
theorem Submission.dtc_bc_lc_pfi_refined_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)) (φ : Euclid P → Euclid P), MeasurableSet M → CountablyRectifiable n M → Differentiable ℝ φ → ∃ (G : ℕ → Euclid n → Euclid P) (A : ℕ → Set (Euclid n)) (κ : ℕ → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (G j)) ∧ (∀ j, MeasurableSet (A j)) ∧ (∀ j, 0 < κ j) ∧ (∀ j, ∀ a ∈ A j, ∀ a' ∈ A j, κ j * ‖a - a'‖ ≤ ‖G j a - G j a'‖) ∧ (∀ j, ∀ a ∈ A j, DifferentiableAt ℝ (G j) a ∧ Injective (fderiv ℝ (G j) a)) ∧ (∀ j, MeasurableSet (G j '' A j)) ∧ (∀ j, G j '' A j ⊆ M) ∧ Pairwise (fun i j => Disjoint (G i '' A i) (G j '' A j)) ∧ μHE[n] (M \ ⋃ j, G j '' A j) = 0 ∧ ∀ j, ((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ A j, ∀ a' ∈ A j, κ' * ‖a - a'‖ ≤ ‖φ (G j a) - φ (G j a')‖) ∧ ∀ a ∈ A j, Injective (fderiv ℝ (φ ∘ G j) a)) ∨ ∀ a ∈ A j, ¬ Injective (fderiv ℝ (φ ∘ G j) a) := by
  intro P n M φ hM hrect hφ
  -- Step 1: the bi-Lipschitz parametrization `Fᵢ(Bᵢ)` of `M`
  obtain ⟨F, B, m, hFL, hBmeas, hmpos, hmlow, hFdiff, -, hFBM, hFBdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P n M hM hrect
  have hFcont : ∀ i, Continuous (F i) := fun i => by
    obtain ⟨L, hL⟩ := hFL i
    exact hL.continuous
  have hinjB : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have := hmlow i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmpos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Steps 2 and 4: split `Bᵢ` into the critical set `Cᵢ = {D(φ ∘ Fᵢ) not injective}` and the
  -- pieces `Bᵢ⁺ ∩ tᵢₗ` of `Bᵢ⁺ = Bᵢ ∖ Cᵢ` on which `φ ∘ Fᵢ` is bi-Lipschitz
  have hsplit : ∀ i, ∃ D : ℕ → Set (Euclid n), (∀ k, D k ⊆ B i) ∧ (∀ k, MeasurableSet (D k)) ∧
      Pairwise (Disjoint on D) ∧ B i ⊆ ⋃ k, D k ∧
      ∀ k, ((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ D k, ∀ a' ∈ D k,
          κ' * ‖a - a'‖ ≤ ‖φ (F i a) - φ (F i a')‖) ∧
        ∀ a ∈ D k, Injective (fderiv ℝ (φ ∘ F i) a)) ∨
        ∀ a ∈ D k, ¬ Injective (fderiv ℝ (φ ∘ F i) a) := by
    intro i
    set S := {a | Injective (fderiv ℝ (φ ∘ F i) a)} with hS
    have hSmeas : MeasurableSet S :=
      measurable_fderiv ℝ (φ ∘ F i) ContinuousLinearMap.isOpen_injective.measurableSet
    obtain ⟨t, T, htdisj, htmeas, hRt, hTapprox, hTy⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (φ ∘ F i) (B i ∩ S)
        (fderiv ℝ (φ ∘ F i))
        (fun x hx => ((hφ (F i x)).comp x (hFdiff i x hx.1).1).hasFDerivAt.hasFDerivWithinAt)
        (fun T => c T / 2) (fun T => (div_pos (hcpos T) two_pos).ne')
    refine ⟨fun k => if k = 0 then B i ∩ Sᶜ else B i ∩ S ∩ t (k - 1), ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      split_ifs
      · exact inter_subset_left
      · exact inter_subset_left.trans inter_subset_left
    · intro k
      dsimp only
      split_ifs
      · exact (hBmeas i).inter hSmeas.compl
      · exact ((hBmeas i).inter hSmeas).inter (htmeas _)
    · intro k k' hkk'
      dsimp only [Function.onFun]
      split_ifs with hk hk'
      · exact absurd (hk.trans hk'.symm) hkk'
      · exact disjoint_left.mpr fun a ha ha' => ha.2 ha'.1.2
      · exact disjoint_left.mpr fun a ha ha' => ha'.2 ha.1.2
      · exact (htdisj fun h => hkk' (by omega)).mono inter_subset_right inter_subset_right
    · intro a ha
      by_cases haS : a ∈ S
      · obtain ⟨l, hl⟩ := mem_iUnion.mp (hRt ⟨ha, haS⟩)
        refine mem_iUnion.mpr ⟨l + 1, ?_⟩
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        exact ⟨⟨ha, haS⟩, hl⟩
      · refine mem_iUnion.mpr ⟨0, ?_⟩
        simp only [↓reduceIte]
        exact ⟨ha, haS⟩
    · intro k
      dsimp only
      split_ifs with hk
      · exact Or.inr fun a ha => ha.2
      · refine Or.inl ⟨⟨((c (T (k - 1)) / 2 : NNReal) : ℝ),
          NNReal.coe_pos.mpr (div_pos (hcpos _) two_pos), ?_⟩, fun a ha => ha.1.2⟩
        intro a ha a' ha'
        obtain ⟨y, hy, hTk⟩ := hTy ⟨a, ha.1⟩ (k - 1)
        have hinj : Injective (T (k - 1)) := by
          rw [hTk]
          exact hy.2
        have h1 := hc (T (k - 1)) hinj (a - a')
        have h2 := hTapprox (k - 1) a ha a' ha'
        have h3 := norm_sub_norm_le (T (k - 1) (a - a')) (φ (F i a) - φ (F i a'))
        rw [norm_sub_rev (T (k - 1) (a - a'))] at h3
        simp only [comp_apply] at h2
        push_cast at h2 ⊢
        linarith
  choose D hDB hDmeas hDdisj hBD hDdich using hsplit
  -- Step 5: enumerate the pieces `(i, k) ↦ Fᵢ(Dᵢₖ)` by `j ↦ unpair j`
  refine ⟨fun j => F (Nat.unpair j).1, fun j => D (Nat.unpair j).1 (Nat.unpair j).2,
    fun j => m (Nat.unpair j).1, fun j => hFL _, fun j => hDmeas _ _, fun j => hmpos _,
    fun j a ha a' ha' => hmlow _ a (hDB _ _ ha) a' (hDB _ _ ha'),
    fun j a ha => hFdiff _ a (hDB _ _ ha), fun j => ?_, fun j => ?_, ?_, ?_,
    fun j => hDdich _ _⟩
  -- Step 6: the images are Borel (Lusin–Souslin) and lie in `M`
  · exact (hDmeas _ _).image_of_continuousOn_injOn (hFcont _).continuousOn
      ((hinjB _).mono (hDB _ _))
  · exact (image_mono (hDB _ _)).trans (hFBM _)
  -- Step 7: disjointness
  · intro j j' hjj'
    dsimp only
    rcases eq_or_ne (Nat.unpair j).1 (Nat.unpair j').1 with hi | hi
    · have hk : (Nat.unpair j).2 ≠ (Nat.unpair j').2 := fun hk => hjj' (by
        rw [← Nat.pair_unpair j, ← Nat.pair_unpair j', hi, hk])
      rw [hi]
      rw [disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨a', ha', heq⟩
      have := hinjB _ (hDB _ _ ha') (hDB _ _ ha) heq
      subst this
      exact disjoint_left.mp (hDdisj _ hk) ha ha'
    · exact (hFBdisj hi).mono (image_mono (hDB _ _)) (image_mono (hDB _ _))
  -- Step 8: the remainder is the null remainder of the parametrization
  · refine measure_mono_null (sdiff_subset_sdiff_right ?_) hnull
    refine iUnion_subset fun i => ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hBD i ha)
    refine mem_iUnion.mpr ⟨Nat.pair i k, a, ?_, ?_⟩
    · simp only [Nat.unpair_pair]
      exact hk
    · simp only [Nat.unpair_pair]
/-- **Simon Ch. 6, (3.4)–(3.5)** (orientation along a bi-Lipschitz piece): let `R = (M, θ, ξ)` be
an integer multiplicity triple in the open set `U`, `G : ℝⁿ → ℝᴾ` `L`-Lipschitz, `A ⊆ ℝⁿ` Borel
and `κ > 0` with `κ|a − a'| ≤ |G a − G a'|` on `A`, `G` differentiable with injective derivative
at every point of `A`, and `G(A) ⊆ M`.  Then for a.e. `a ∈ A` there is `σ = ±1` with
`J_G(a) ⟨β, ξ(G a)⟩ = σ β(DG(a)e₁, …, DG(a)eₙ)` for every `n`-covector `β`, where
`J_G(a) = (det[DG(a)eₖ · DG(a)eₗ])^{1/2}`.
`M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` is locally integrable, so `M` has approximate
tangent space `range DG(a)` at `G a` for a.e. `a ∈ A`; the `Hⁿ`-a.e. orientation condition of `R`
pulls back along `G` to a.e. `a ∈ A`; uniqueness of approximate tangent spaces identifies the
oriented plane with `range DG(a)`, which `J_G(a)⁻¹ DG(a)_# e` orients, so
`ξ(G a) = ±J_G(a)⁻¹ DG(a)_# e`. -/
theorem Submission.dtc_bc_lc_pfi_piece_orientation_sign : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (κ : ℝ), IsOpen U → LipschitzWith L G → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∀ᵐ a ∂(volume.restrict A), ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ β : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ G a (EuclideanSpace.single k 1)) (fderiv ℝ G a (EuclideanSpace.single l 1)))) * R.orient (G a) β = σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1)) := by
  intro P n U R G A L κ hU hG hA hκ hbi hdiff hGA
  -- Step 1: `Hⁿ(M ∩ C) ≤ ∫_{M ∩ C} θ dHⁿ < ∞` for compact `C ⊆ U`, as `θ ≥ 1` on `M`
  have hfin : ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (R.carrier ∩ C) ≠ ∞ := by
    intro C hC hCU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult C hC hCU) ?_
    calc μHE[n] (R.carrier ∩ C) = ∫⁻ _ in R.carrier ∩ C, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hC.isClosed.measurableSet)
          fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1)
  -- Step 2: `M` has approximate tangent space `range DG(a)` at `G a` for a.e. `a ∈ A`
  have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n U R.carrier G A L κ hU
    R.measurableSet_carrier R.carrier_subset hfin hG hA hκ hbi hdiff hGA
  -- Step 3: `G` is injective on `A`, so the `Hⁿ`-a.e. orientation condition of `R`, which holds
  -- `Hⁿ`-a.e. on `G(A) ⊆ M`, pulls back along `G` to a.e. `a ∈ A`
  have hinj : InjOn G A := by
    intro a ha a' ha' hGa
    have h := hbi a ha a' ha'
    rw [hGa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hκ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  obtain ⟨-, -, hpull, -⟩ :=
    (Submission.dtc_bc_lc_pfi_area_change_of_variables P n).2 G A hA hdiff hinj
  have horient := hpull _ (ae_restrict_of_ae_restrict_of_subset hGA R.orients)
  obtain ⟨hsign, -, hunit, -⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  filter_upwards [htan, horient, ae_restrict_mem hA] with a hta hor ha
  -- Step 4: by uniqueness of approximate tangent spaces, `ξ(G a)` orients `range DG(a)`
  obtain ⟨Q, hQ, hξ⟩ := hor
  rw [hQ.unique hta] at hξ
  -- Step 5: `J_G(a) > 0` and `ζ := J_G(a)⁻¹ DG(a)_# e` also orients `range DG(a)`, so
  -- `ξ(G a) = ±ζ`, whence `J_G(a) ξ(G a)(β) = ±β(DG(a)e)`
  obtain ⟨hJ, hζ⟩ := hunit (fderiv ℝ G a) (hdiff a ha).2
  rcases hsign _ _ _ hζ hξ with h | h
  · refine ⟨1, Or.inl rfl, fun β => ?_⟩
    rw [h, smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul,
      mul_inv_cancel_left₀ hJ.ne', one_mul]
  · refine ⟨-1, Or.inr rfl, fun β => ?_⟩
    rw [h, neg_apply, smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul, mul_neg,
      mul_inv_cancel_left₀ hJ.ne', neg_one_mul]
/-- **Push-forward of one bi-Lipschitz piece** (Simon Ch. 6, 3.4–3.7, for one piece `G(A)` of
`M`).  `G` is Lipschitz, bi-Lipschitz on the Borel set `A` with injective `DG` there, `G(A) ⊆ M`,
`∫_{G(A)} θ dHⁿ < ∞`, and `J_G(a) ξ(G(a)) = ±DG(a)_# e` for a.e. `a ∈ A`; `φ` is differentiable
and `Λ`-Lipschitz, and `H = φ ∘ G`.  If `DH` is nowhere injective on `A`, then `DH(a)_# e = 0`,
the integrand `θ ξ(β(φ) ∘ Dφ)` vanishes `Hⁿ`-a.e. on `G(A)`, and `N = ∅`.  If `H` is bi-Lipschitz
on `A` with injective `DH`, take `N = H(A)`, `g = θ ∘ G ∘ H⁻¹` and
`η = (J_G / J_H) ξ̃(G)(· ∘ Dφ(G)) ∘ H⁻¹`: `η(H(a)) = ±J_H(a)⁻¹ DH(a)_# e` orients `range DH(a)`,
the approximate tangent space of `N` at `H(a)`; `J_H ≤ Λⁿ J_G` bounds the mass; and the area
formula along `G` and along `H` turns both integrals into one integral over `A`. -/
theorem Submission.dtc_bc_lc_pfi_piece_pushforward_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (κ : ℝ) (φ : Euclid P → Euclid P) (Λ : NNReal), LipschitzWith L G → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ → (∀ᵐ a ∂(volume.restrict A), ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ β : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ G a (EuclideanSpace.single k 1)) (fderiv ℝ G a (EuclideanSpace.single l 1)))) * R.orient (G a) β = σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1))) → Differentiable ℝ φ → LipschitzWith Λ φ → (((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ A, ∀ a' ∈ A, κ' * ‖a - a'‖ ≤ ‖φ (G a) - φ (G a')‖) ∧ ∀ a ∈ A, Injective (fderiv ℝ (φ ∘ G) a)) ∨ ∀ a ∈ A, ¬ Injective (fderiv ℝ (φ ∘ G) a)) → ∃ (N : Set (Euclid P)) (g : Euclid P → ℤ) (η : Euclid P → MultiVector P n), MeasurableSet N ∧ N ⊆ φ '' (G '' A) ∧ CountablyRectifiable n N ∧ Measurable g ∧ (∀ y ∈ N, g y ≠ 0) ∧ StronglyMeasurable η ∧ (∀ᵐ y ∂(μHE[n].restrict N), ∃ T : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N y T ∧ IsUnitOrientationOf (η y) T) ∧ ∫⁻ y in N, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] ≤ (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] ∧ ∀ β : Euclid P → Covector (Euclid P) n, StronglyMeasurable β → ∫ x in G '' A, (R.mult x : ℝ) * R.orient x ((β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] = ∫ y in N, (g y : ℝ) * η y (β y) ∂μHE[n] := by
  intro P n U R G A L κ φ Λ hG hA hκ hbi hdiff hGA hfin hor hφd hφ hcase
  obtain ⟨hJacI, hcov⟩ := Submission.dtc_bc_lc_pfi_area_change_of_variables P n
  obtain ⟨-, -, horientInj, horientCrit⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  -- Gram Jacobians `J_G` of `G` and `J_H` of `H = φ ∘ G`
  obtain ⟨JG, hJG⟩ : ∃ JG : Euclid n → ℝ, ∀ x, JG x = Real.sqrt (Matrix.det (Matrix.of
      fun k l : Fin n => inner ℝ (fderiv ℝ G x (EuclideanSpace.single k 1))
        (fderiv ℝ G x (EuclideanSpace.single l 1)))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨JH, hJH⟩ : ∃ JH : Euclid n → ℝ, ∀ x, JH x = Real.sqrt (Matrix.det (Matrix.of
      fun k l : Fin n => inner ℝ (fderiv ℝ (φ ∘ G) x (EuclideanSpace.single k 1))
        (fderiv ℝ (φ ∘ G) x (EuclideanSpace.single l 1)))) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hJG] at hor
  -- Step 1(a): `G` is injective on `A`; change of variables along `G`
  have hinjOn : ∀ (F : Euclid n → Euclid P) (m : ℝ), 0 < m →
      (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → InjOn F A := by
    intro F m hm hF a ha a' ha' heq
    have h := hF a ha a' ha'
    rw [heq, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := by nlinarith [norm_nonneg (a - a')]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h')
  have hGinj : InjOn G A := hinjOn G κ hκ hbi
  obtain ⟨-, -, hGpull, hGint⟩ := hcov G A hA hdiff hGinj
  simp only [← hJG] at hGint
  -- Step 1(b): the integrand `θ ξ(β(φ) ∘ Dφ)` is a.e. strongly measurable on `G(A)`
  have hDφ : StronglyMeasurable (fderiv ℝ φ) := (measurable_fderiv ℝ φ).stronglyMeasurable
  have hLHSm : ∀ β : Euclid P → Covector (Euclid P) n, StronglyMeasurable β →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) *
        R.orient x ((β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)))
        (μHE[n].restrict (G '' A)) := by
    intro β hβ
    have hβφ : StronglyMeasurable (fun x => (β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) := by
      have hev : Continuous fun p : (Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n) ×
          Covector (Euclid P) n => p.1 p.2 := continuous_fst.clm_apply continuous_snd
      exact hev.comp_stronglyMeasurable
        ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable
          hDφ).prodMk (hβ.comp_measurable hφd.continuous.measurable))
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hGA le_rfl)).prodMk
          hβφ.aestronglyMeasurable))
  -- Step 1(d): a strongly measurable `ξ̃ = ξ` a.e. on `M`, hence `ξ̃(G(a)) = ξ(G(a))` a.e. on `A`
  set ξ' := R.aestronglyMeasurable_orient.mk R.orient
  have hξ'm : StronglyMeasurable ξ' := R.aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξG : ∀ᵐ a ∂(volume.restrict A), R.orient (G a) = ξ' (G a) :=
    hGpull (fun x => R.orient x = ξ' x)
      (ae_restrict_of_ae_restrict_of_subset hGA R.aestronglyMeasurable_orient.ae_eq_mk)
  rcases hcase with ⟨⟨κ', hκ', hbi'⟩, hinjH⟩ | hcrit
  · -- Step 3: regular case, `N = H(A)`
    have hdiffH : ∀ a ∈ A, DifferentiableAt ℝ (φ ∘ G) a ∧ Injective (fderiv ℝ (φ ∘ G) a) :=
      fun a ha => ⟨(hφd (G a)).comp a (hdiff a ha).1, hinjH a ha⟩
    have hHinj : InjOn (φ ∘ G) A := hinjOn (φ ∘ G) κ' hκ' hbi'
    obtain ⟨hNm, hψm, -, hHint⟩ := hcov (φ ∘ G) A hA hdiffH hHinj
    simp only [← hJH] at hHint
    set ψ := Function.invFunOn (φ ∘ G) A
    have hψH : ∀ a ∈ A, ψ ((φ ∘ G) a) = a := fun a ha => hHinj.leftInvOn_invFunOn ha
    have hGψ : Measurable (fun y => G (ψ y)) := hG.continuous.measurable.comp hψm
    -- Step 3(b): `g = θ ∘ G ∘ ψ` and `η = (J_G/J_H) ∘ ψ · ξ̃(G ∘ ψ)(· ∘ Dφ(G ∘ ψ))`
    obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℤ, ∀ y, g y = (R.mult (G (ψ y)) : ℤ) := ⟨_, fun _ => rfl⟩
    obtain ⟨η, hη⟩ : ∃ η : Euclid P → MultiVector P n, ∀ y, η y = (JG (ψ y) / JH (ψ y)) •
        (ξ' (G (ψ y))).comp (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (fderiv ℝ φ (G (ψ y)))) := ⟨_, fun _ => rfl⟩
    have hgm : Measurable g := by
      rw [show g = fun y => ((R.mult (G (ψ y)) : ℕ) : ℤ) from funext hg]
      exact measurable_from_nat.comp (R.measurable_mult.comp hGψ)
    have hg0 : ∀ y ∈ (φ ∘ G) '' A, g y ≠ 0 := by
      rintro y ⟨a, ha, rfl⟩
      rw [hg, hψH a ha]
      exact Nat.cast_ne_zero.2 (R.mult_pos (G a) (hGA (mem_image_of_mem G ha))).ne'
    have hηm : StronglyMeasurable η := by
      have hJGm : Measurable JG := by
        have h := (Submission.codim1_lura_gram_area_formula n P G).1
        simp only [← hJG] at h
        exact h
      have hJHm : Measurable JH := by
        have h := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).1
        simp only [← hJH] at h
        exact h
      rw [show η = fun y => (JG (ψ y) / JH (ψ y)) •
          (ξ' (G (ψ y))).comp (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (fderiv ℝ φ (G (ψ y)))) from funext hη]
      exact ((hJGm.comp hψm).div (hJHm.comp hψm)).stronglyMeasurable.smul
        ((continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
          ((hξ'm.comp_measurable hGψ).prodMk
            (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable
              (hDφ.comp_measurable hGψ))))
    -- Step 3(c): `J_H ≤ ‖Dφ(G a)‖ⁿ J_G ≤ Λⁿ J_G` and `0 < J_H` on `A`
    have hJpos : ∀ a ∈ A, 0 < JH a := fun a ha => by
      rw [hJH]; exact (horientInj _ (hinjH a ha)).1
    have hJle : ∀ a ∈ A, JH a ≤ (Λ : ℝ) ^ n * JG a := by
      intro a ha
      have hcomp := fderiv_comp a (hφd (G a)) (hdiff a ha).1
      have h1 := hJacI (fderiv ℝ G a) (fderiv ℝ φ (G a)) (by rw [← hcomp]; exact hinjH a ha)
      rw [hJH, hJG, hcomp]
      refine h1.trans ?_
      gcongr
      exact norm_fderiv_le_of_lipschitz ℝ hφ
    -- Step 3(d): mass bound
    have hmass : ∫⁻ y in (φ ∘ G) '' A, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] ≤
        (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      have hareaH := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).2 A hA
        (fun a ha => (hdiffH a ha).1) (fun a ha => (hdiffH a ha).2) hHinj
      have hareaG := (Submission.codim1_lura_gram_area_formula n P G).2 A hA
        (fun a ha => (hdiff a ha).1) (fun a ha => (hdiff a ha).2) hGinj
      simp only [← hJG] at hareaG
      simp only [← hJH] at hareaH
      rw [hareaH, hareaG, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
      refine setLIntegral_mono' hA fun a ha => ?_
      rw [hg, hψH a ha, Int.natAbs_natCast, ← mul_assoc]
      gcongr
      calc ENNReal.ofReal (JH a) ≤ ENNReal.ofReal ((Λ : ℝ) ^ n * JG a) :=
            ENNReal.ofReal_le_ofReal (hJle a ha)
        _ = (Λ : ℝ≥0∞) ^ n * ENNReal.ofReal (JG a) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    have hNfin : μHE[n] ((φ ∘ G) '' A) ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfin)
        (le_trans ?_ hmass)
      calc μHE[n] ((φ ∘ G) '' A) = ∫⁻ _ in (φ ∘ G) '' A, 1 ∂μHE[n] := (setLIntegral_one _).symm
        _ ≤ ∫⁻ y in (φ ∘ G) '' A, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' hNm fun y hy => Nat.one_le_cast.2 (Int.natAbs_pos.2 (hg0 y hy))
    -- Step 3(e): `Hⁿ⌞N`-a.e. properties come from a.e. properties on `A` (`Hⁿ(H(A₀)) = 0`)
    have hpush : ∀ p : Euclid P → Prop, (∀ᵐ a ∂(volume.restrict A), p ((φ ∘ G) a)) →
        ∀ᵐ y ∂(μHE[n].restrict ((φ ∘ G) '' A)), p y := by
      intro p hp
      have hTm := measurableSet_toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)}
      have hT0 : volume (toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)} ∩ A) = 0 := by
        rw [← Measure.restrict_apply hTm, measure_toMeasurable]
        exact ae_iff.1 hp
      have hHT : μHE[n] ((φ ∘ G) '' (toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)} ∩ A))
          = 0 := by
        have h := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).2 _ (hTm.inter hA)
          (fun a ha => (hdiffH a ha.2).1) (fun a ha => (hdiffH a ha.2).2)
          (hHinj.mono inter_subset_right) (fun _ => 1)
        rw [setLIntegral_one, setLIntegral_measure_zero _ _ hT0] at h
        exact h
      rw [ae_iff, Measure.restrict_apply' hNm]
      refine measure_mono_null ?_ hHT
      rintro y ⟨hy, a, ha, rfl⟩
      refine ⟨a, ⟨?_, ha⟩, rfl⟩
      by_contra haT
      exact hy (not_not.1 fun h => haT (subset_toMeasurable _ _ h))
    -- `H(A)` has approximate tangent space `range DH(a)` at `H(a)` for a.e. `a ∈ A`
    have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n univ ((φ ∘ G) '' A) (φ ∘ G)
      A (Λ * L) κ' isOpen_univ hNm (subset_univ _)
      (fun C _ _ => ne_top_of_le_ne_top hNfin (measure_mono inter_subset_left)) (hφ.comp hG) hA
      hκ' hbi' hdiffH subset_rfl
    -- `η(H(a)) = ±J_H(a)⁻¹ DH(a)_# e` orients `range DH(a)`
    have hηor : ∀ a ∈ A, R.orient (G a) = ξ' (G a) → (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ β : Covector (Euclid P) n, JG a * R.orient (G a) β =
          σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1))) →
        IsUnitOrientationOf (η ((φ ∘ G) a))
          (LinearMap.range (fderiv ℝ (φ ∘ G) a : Euclid n →ₗ[ℝ] Euclid P)) := by
      rintro a ha hξa ⟨σ, hσ, hσβ⟩
      obtain ⟨-, τ, hτ, hspan, hτor⟩ := horientInj _ (hinjH a ha)
      rw [← hJH a] at hτor
      have hcomp := fderiv_comp a (hφd (G a)) (hdiff a ha).1
      have key : ∀ α : Covector (Euclid P) n, η ((φ ∘ G) a) α =
          σ * ((JH a)⁻¹ * α (fun k => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1))) := by
        intro α
        rw [hη, hψH a ha, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hξa, smul_eq_mul,
          div_eq_inv_mul, mul_assoc, hσβ, ContinuousAlternatingMap.compContinuousLinearMap_apply,
          hcomp]
        exact mul_left_comm _ _ _
      have hζ : ∀ α : Covector (Euclid P) n, ((JH a)⁻¹ •
          ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
            (fun k : Fin n => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1))) α =
          (JH a)⁻¹ * α (fun k => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1)) := fun α => rfl
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hσ with rfl | rfl <;> rcases hτor with h | h
      · exact Or.inl fun α => by rw [key, ← hζ, h, one_mul]
      · exact Or.inr fun α => by rw [key, ← hζ, h, one_mul]
      · exact Or.inr fun α => by rw [key, ← hζ, h, neg_one_mul]
      · exact Or.inl fun α => by rw [key, ← hζ, h, neg_one_mul, neg_neg]
    refine ⟨(φ ∘ G) '' A, g, η, hNm, (image_comp φ G A).subset,
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hφ.comp hG)).mono
        (image_subset_range _ _), hgm, hg0, hηm, ?_, hmass, ?_⟩
    · refine hpush _ ?_
      filter_upwards [ae_restrict_mem hA, htan, hξG, hor] with a ha hta hξa hora
      exact ⟨_, hta, hηor a ha hξa hora⟩
    · -- Step 3(f): both sides are the same integral over `A`
      intro β hβ
      have hRHSm : AEStronglyMeasurable (fun y => (g y : ℝ) * η y (β y))
          (μHE[n].restrict ((φ ∘ G) '' A)) :=
        ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp hgm).aestronglyMeasurable.mul
          ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
            (hηm.prodMk hβ)).aestronglyMeasurable
      rw [(hGint _ (hLHSm β hβ)).2, (hHint _ hRHSm).2]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hA, hξG] with a ha hξa
      rw [hg, hη, hψH a ha, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hξa, smul_eq_mul,
        Int.cast_natCast, Function.comp_apply]
      field_simp [(hJpos a ha).ne']
  · -- Step 2: critical case, `N = ∅`
    refine ⟨∅, fun _ => 0, fun _ => 0, MeasurableSet.empty, empty_subset _,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
      measurable_const, fun y hy => hy.elim, stronglyMeasurable_const, by simp, by simp,
      fun β hβ => ?_⟩
    rw [(hGint _ (hLHSm β hβ)).2, Measure.restrict_empty, integral_zero_measure]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hA, hor] with a ha hora
    obtain ⟨σ, -, hσβ⟩ := hora
    have h0 : ((β (φ (G a))).compContinuousLinearMap (fderiv ℝ φ (G a)))
        (fun k => fderiv ℝ G a (EuclideanSpace.single k 1)) = 0 := by
      have h := horientCrit (fderiv ℝ (φ ∘ G) a) (hcrit a ha) (β (φ (G a)))
      rw [fderiv_comp a (hφd (G a)) (hdiff a ha).1] at h
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact h
    rw [Pi.zero_apply, mul_left_comm, hσβ, h0, mul_zero, mul_zero]
/-- **Integer density of a summable family** (step 10 of the push-forward proof, Simon
6.3.3–3.9).  If `fⱼ : ℝᴾ → ℤ` are measurable with `Σⱼ ∫ |fⱼ| dHⁿ < ∞`, then `m = Σⱼ fⱼ` (the real
`tsum`, `0` where the family is not summable) is measurable, integer valued everywhere and bounded
by `Σⱼ |fⱼ|`, and `Hⁿ`-a.e. the family `(fⱼ(y))ⱼ` is summable with sum `m(y)`. -/
theorem Submission.dtc_bc_lc_pfi_integer_density_of_summable : ∀ (P n : ℕ) (f : ℕ → Euclid P → ℤ), (∀ j, Measurable (f j)) → ∑' j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → ∃ m : Euclid P → ℝ, Measurable m ∧ (∀ y, ∃ z : ℤ, m y = z) ∧ (∀ y, ENNReal.ofReal |m y| ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞)) ∧ ∀ᵐ y ∂μHE[n], Summable (fun j => (f j y : ℝ)) ∧ m y = ∑' j, (f j y : ℝ) := by
  intro P n f hf hfin
  -- Step 3: a summable family of integers has finite support, so its tsum is a finite sum
  have hsum : ∀ y, Summable (fun j => (f j y : ℝ)) → ∃ s : Finset ℕ,
      ∑' j, (f j y : ℝ) = ∑ j ∈ s, (f j y : ℝ) := by
    intro y hs
    have hfs : {j | f j y ≠ 0}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hs.tendsto_cofinite_zero.eventually (ball_mem_nhds (0 : ℝ) one_pos)]
        with j hj
      rw [dist_zero_right, Real.norm_eq_abs] at hj
      exact Int.abs_lt_one_iff.1 (by exact_mod_cast hj)
    exact ⟨hfs.toFinset, tsum_eq_sum fun j hj => by simpa using hj⟩
  have hm : ∀ j, Measurable fun y => ((f j y).natAbs : ℝ≥0∞) := fun j =>
    (Measurable.of_discrete (f := fun z : ℤ => (z.natAbs : ℝ≥0∞))).comp (hf j)
  refine ⟨fun y => ∑' j, (f j y : ℝ), Measurable.tsum fun j => Measurable.of_discrete.comp (hf j),
    fun y => ?_, fun y => ?_, ?_⟩
  · -- Step 3: integrality (the tsum is `0` if the family is not summable)
    show ∃ z : ℤ, ∑' j, (f j y : ℝ) = z
    by_cases hs : Summable (fun j => (f j y : ℝ))
    · obtain ⟨s, hs⟩ := hsum y hs
      exact ⟨∑ j ∈ s, f j y, by rw [hs, Int.cast_sum]⟩
    · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs, Int.cast_zero]⟩
  · -- Step 4: pointwise bound `|m| ≤ S`
    show ENNReal.ofReal |∑' j, (f j y : ℝ)| ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞)
    by_cases hs : Summable (fun j => (f j y : ℝ))
    · obtain ⟨s, hs⟩ := hsum y hs
      calc ENNReal.ofReal |∑' j, (f j y : ℝ)| ≤ ENNReal.ofReal (∑ j ∈ s, |(f j y : ℝ)|) := by
            rw [hs]; exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ j ∈ s, ((f j y).natAbs : ℝ≥0∞) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
        _ ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞) := ENNReal.sum_le_tsum s
    · rw [tsum_eq_zero_of_not_summable hs, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  · -- Step 5: `S = Σ_j |f_j|` has finite integral, so it is finite a.e.
    filter_upwards [ae_lt_top (Measurable.tsum hm)
      ((lintegral_tsum fun j => (hm j).aemeasurable).trans_ne hfin)] with y hy
    refine ⟨summable_abs_iff.1 ?_, rfl⟩
    have h1 : Summable fun j => ((f j y).natAbs : NNReal) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa using hy.ne
    simpa [Nat.cast_natAbs] using NNReal.summable_coe.2 h1

/-- **Simon Ch. 6, 3.7–3.9 (gluing integer pieces)**: let `U` be open, `N_j ⊆ U` Borel and
countably `n`-rectifiable, `g_j` integer-valued and nonzero on `N_j`, and `η_j` a unit orientation
of an approximate tangent space of `N_j` at `Hⁿ`-a.e. point of `N_j`, with
`Σ_j ∫_{N_j} |g_j| dHⁿ < ∞`.  If `Q(ω) = Σ_j ∫_{N_j} g_j ⟨ω, η_j⟩ dHⁿ` for `ω ∈ 𝒟ⁿ(U)`, then `Q` is
integer multiplicity.  The locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2),
1.8(1)) is the first hypothesis.

Proof sketch:
* `N = ⋃_j N_j` is Borel and countably `n`-rectifiable, and `Hⁿ(N) ≤ Σ_j ∫_{N_j} |g_j| < ∞`
  since `|g_j| ≥ 1` on `N_j`.
* By locality, for `Hⁿ`-a.e. `y` and every `j` with `y ∈ N_j`, `η_j(y)` orients an approximate
  tangent space of `N` at `y`.
* `ξ(y) = η_{j₀(y)}(y)`, `j₀(y)` the first `j` with `y ∈ N_j`, is strongly measurable and orients
  the (unique) approximate tangent space of `N` a.e. on `N`, so `η_j = ±ξ` a.e. on `N_j` (3.7).
* With `f_j = 1_{N_j} (±g_j)` (so that `g_j η_j = f_j ξ` a.e. on `N_j`), the integer density
  `m = Σ_j f_j` (3.8) is measurable and `Hⁿ`-integrable.
* Dominated convergence (`|⟨ω, ξ⟩| ≤ sup ‖ω‖` a.e. on `N`) gives `Q(ω) = ∫_N m ⟨ω, ξ⟩ dHⁿ`, and
  `(N, m, ξ)` yields an `IMRep` (3.9) by `cmcdt_ims_imrep_of_int_density`. -/
theorem Submission.dtc_bc_lc_pfi_isIntegerMultiplicity_of_pieces : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (N : ℕ → Set (Euclid P)) (g : ℕ → Euclid P → ℤ) (η : ℕ → Euclid P → MultiVector P n) (Q : GeometricCurrentOn U n), IsOpen U → (∀ j, MeasurableSet (N j)) → (∀ j, N j ⊆ U) → (∀ j, CountablyRectifiable n (N j)) → (∀ j, Measurable (g j)) → (∀ j, ∀ y ∈ N j, g j y ≠ 0) → (∀ j, StronglyMeasurable (η j)) → (∀ j, ∀ᵐ y ∂(μHE[n].restrict (N j)), ∃ T : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (N j) y T ∧ IsUnitOrientationOf (η j y) T) → ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → (∀ ω : TestFormOn U n, Q ω = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y ((ω : DifferentialForm (Euclid P) n) y) ∂μHE[n]) → IsIntegerMultiplicity Q := by
  intro hTL P n U N g η Q hU hNmeas hNU hNrect hg hg0 hη hηor hsum hQ
  classical
  -- `MultiVector P n` is (pseudo)metrizable; instance search does not find it
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (MultiVector P n) inferInstance
  obtain ⟨horient_pm, horient_le, -, -⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  -- Step 1: the union `NN = ⋃_j N_j`, of finite measure since `|g_j| ≥ 1` on `N_j`
  set NN : Set (Euclid P) := ⋃ j, N j
  have hNNmeas : MeasurableSet NN := MeasurableSet.iUnion hNmeas
  have hNNU : NN ⊆ U := iUnion_subset hNU
  have hNNrect : CountablyRectifiable n NN :=
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion N hNrect
  have hNjle : ∀ j, μHE[n] (N j) ≤ ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] := by
    intro j
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (hNmeas j) fun y hy => ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hg0 j y hy))
  have hNNfin : μHE[n] NN ≠ ∞ :=
    ne_top_of_le_ne_top hsum ((measure_iUnion_le N).trans (ENNReal.tsum_le_tsum hNjle))
  have hNNK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (NN ∩ K) ≠ ∞ :=
    fun K _ _ => ne_top_of_le_ne_top hNNfin (measure_mono inter_subset_left)
  -- Step 2: by locality (`hTL`), a.e. on `N_j`, `η_j` orients a tangent space of `NN`
  have hgood : ∀ᵐ y ∂μHE[n], ∀ j, y ∈ N j → ∃ T : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n NN y T ∧ IsUnitOrientationOf (η j y) T := by
    refine ae_all_iff.2 fun j => (ae_restrict_iff' (hNmeas j)).1 ?_
    filter_upwards [hTL P n U (N j) NN hU (hNmeas j) hNNmeas (subset_iUnion N j) hNNU hNNK,
      hηor j] with y hy hyη
    obtain ⟨T, hT, hTη⟩ := hyη
    exact ⟨T, (hy T).2 hT, hTη⟩
  -- Step 3: the common orientation `ξ(y) = η_{j₀(y)}(y)`, `j₀(y)` the first `j` with `y ∈ N_j`
  have hex : ∀ y, ∃ j, y ∈ N j ∨ y ∉ NN := fun y => by
    by_cases hy : y ∈ NN
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hy
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hy⟩
  set j₀ : Euclid P → ℕ := fun y => Nat.find (hex y)
  have hj₀meas : Measurable j₀ := measurable_find hex fun j => (hNmeas j).union hNNmeas.compl
  have hj₀mem : ∀ y ∈ NN, y ∈ N (j₀ y) := fun y hy =>
    (Nat.find_spec (hex y)).resolve_right (not_not.2 hy)
  set ξ : Euclid P → MultiVector P n := fun y => η (j₀ y) y
  have hξsm : StronglyMeasurable ξ :=
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun _ => continuous_of_discreteTopology) hη).comp_measurable (hj₀meas.prodMk measurable_id)
  have hξor : ∀ᵐ y ∂(μHE[n].restrict NN), ∃ T : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n NN y T ∧ IsUnitOrientationOf (ξ y) T := by
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hNNmeas] with y hy hyNN
    exact hy (j₀ y) (hj₀mem y hyNN)
  -- Step 4: `η_j = ±ξ` a.e. on `N_j`, by uniqueness of approximate tangent spaces
  have hsign : ∀ᵐ y ∂μHE[n], ∀ j, y ∈ N j → η j y = ξ y ∨ η j y = -ξ y := by
    filter_upwards [hgood] with y hy j hyj
    obtain ⟨T, hT, hTη⟩ := hy j hyj
    obtain ⟨T', hT', hT'ξ⟩ := hy (j₀ y) (hj₀mem y (mem_iUnion.2 ⟨j, hyj⟩))
    rw [hT'.unique hT] at hT'ξ
    exact horient_pm (ξ y) (η j y) T hT'ξ hTη
  -- Step 5: the integer density `m = Σ_j f_j`, `f_j = 1_{N_j} (±g_j)` with `g_j η_j = f_j ξ`
  set f : ℕ → Euclid P → ℤ := fun j y =>
    if y ∈ N j then (if η j y = ξ y then g j y else -g j y) else 0 with hfdef
  have hf_meas : ∀ j, Measurable (f j) := fun j =>
    Measurable.ite (hNmeas j)
      (Measurable.ite ((hη j).measurableSet_eq_fun hξsm) (hg j)
        ((measurable_of_countable fun z : ℤ => -z).comp (hg j)))
      measurable_const
  have hf_natAbs_meas : ∀ j, Measurable fun y => ((f j y).natAbs : ℝ≥0∞) := fun j =>
    (measurable_of_countable fun z : ℤ => ((z.natAbs : ℕ) : ℝ≥0∞)).comp (hf_meas j)
  have hf_abs : ∀ j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] =
      ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] := by
    intro j
    rw [← lintegral_indicator (hNmeas j)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ N j
    · rw [indicator_of_mem hy]
      simp only [hfdef, ite_eq_left hy]
      split_ifs <;> simp
    · rw [indicator_of_notMem hy]
      simp [hfdef, hy]
  have hf_sum : ∑' j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    rwa [tsum_congr hf_abs]
  obtain ⟨m, hm_meas, hm_int, hm_le, hm_ae⟩ :=
    Submission.dtc_bc_lc_pfi_integer_density_of_summable P n f hf_meas hf_sum
  have hm_loc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in NN ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top hf_sum ((setLIntegral_le_lintegral _ _).trans ?_)
    calc ∫⁻ x, ‖m x‖ₑ ∂μHE[n]
        ≤ ∫⁻ x, ∑' j, ((f j x).natAbs : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono fun x => (Real.enorm_eq_ofReal_abs (m x)).trans_le (hm_le x)
      _ = ∑' j, ∫⁻ x, ((f j x).natAbs : ℝ≥0∞) ∂μHE[n] :=
          lintegral_tsum fun j => (hf_natAbs_meas j).aemeasurable
  -- Step 6: the triple `(NN, m, ξ)` gives an `IMRep` acting by `ω ↦ ∫_NN m ⟨ω, ξ⟩ dHⁿ`
  obtain ⟨R, hR⟩ := Submission.cmcdt_ims_imrep_of_int_density P n U NN ξ m hU hNNmeas hNNU
    hNNrect hNNK hξsm hm_meas hm_int hm_loc hξor
  refine ⟨R, fun ω => ?_⟩
  -- Step 7: `Q(ω) = Σ_j ∫_NN f_j ⟨ω, ξ⟩ dHⁿ = ∫_NN m ⟨ω, ξ⟩ dHⁿ` by dominated convergence
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hwc : Continuous w := ω.property.1.1.continuous
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support ω.property.1.2
  have hpiece : ∀ j, ∫ y in N j, (g j y : ℝ) * η j y (w y) ∂μHE[n] =
      ∫ y in NN, (f j y : ℝ) * ξ y (w y) ∂μHE[n] := by
    intro j
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hNNmeas (subset_iUnion N j)
      fun y hy => by simp [hfdef, hy.2]]
    refine setIntegral_congr_ae (hNmeas j) ?_
    filter_upwards [hsign] with y hy hyj
    simp only [hfdef, ite_eq_left hyj]
    split_ifs with he
    · rw [he]
    · rcases hy j hyj with h | h
      · exact absurd h he
      · rw [h, neg_apply, Int.cast_neg, mul_neg, neg_mul]
  have hξbd : ∀ᵐ y ∂(μHE[n].restrict NN), ‖ξ y (w y)‖ₑ ≤ ENNReal.ofReal C := by
    filter_upwards [hξor] with y hy
    obtain ⟨T, -, hT⟩ := hy
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((horient_le (ξ y) T hT (w y)).trans (hC y))
  have hcont : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hterm_meas : ∀ j, AEStronglyMeasurable (fun y => (f j y : ℝ) * ξ y (w y))
      (μHE[n].restrict NN) := fun j =>
    ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp (hf_meas j)).aestronglyMeasurable.mul
      (hcont.comp_aestronglyMeasurable (hξsm.aestronglyMeasurable.prodMk hwc.aestronglyMeasurable))
  have hzabs : ∀ z : ℤ, ‖(z : ℝ)‖ₑ = ((z.natAbs : ℕ) : ℝ≥0∞) := fun z => by
    rw [Real.enorm_eq_ofReal_abs, show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs],
      ENNReal.ofReal_natCast]
  have hterm_bd : ∑' j, ∫⁻ y in NN, ‖(f j y : ℝ) * ξ y (w y)‖ₑ ∂μHE[n] ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hf_sum (ENNReal.ofReal_ne_top (r := C))) ?_
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun j => ?_
    calc ∫⁻ y in NN, ‖(f j y : ℝ) * ξ y (w y)‖ₑ ∂μHE[n]
        ≤ ∫⁻ y in NN, ((f j y).natAbs : ℝ≥0∞) * ENNReal.ofReal C ∂μHE[n] := by
          refine lintegral_mono_ae ?_
          filter_upwards [hξbd] with y hy
          rw [enorm_mul, hzabs]
          exact mul_le_mul_right hy _
      _ = (∫⁻ y in NN, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n]) * ENNReal.ofReal C :=
          lintegral_mul_const _ (hf_natAbs_meas j)
      _ ≤ (∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n]) * ENNReal.ofReal C :=
          mul_le_mul_left (setLIntegral_le_lintegral _ _) _
  have hsum_eq : ∀ᵐ y ∂(μHE[n].restrict NN),
      ∑' j, (f j y : ℝ) * ξ y (w y) = m y * ξ y (w y) := by
    filter_upwards [ae_restrict_of_ae hm_ae] with y hy
    rw [tsum_mul_right, ← hy.2]
  calc Q ω = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y (w y) ∂μHE[n] := hQ ω
    _ = ∑' j, ∫ y in NN, (f j y : ℝ) * ξ y (w y) ∂μHE[n] := tsum_congr hpiece
    _ = ∫ y in NN, ∑' j, (f j y : ℝ) * ξ y (w y) ∂μHE[n] :=
        (integral_tsum hterm_meas hterm_bd).symm
    _ = ∫ y in NN, m y * ξ y (w y) ∂μHE[n] := integral_congr_ae hsum_eq
    _ = R.action w := (hR w).symm

/-- **Push-forward of an integer multiplicity current by a `C¹` map** (Simon Ch. 6, 3.3–3.9, with
the area formula of Ch. 3, 2.4–2.6).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in the
open `U` with `Hⁿ(M ∖ K) = 0` for a compact `K ⊆ U`, let `f` be `C¹` on an open `O ⊇ K` with
`f(K) ⊆ U`, and let `Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ(x)` for `ω ∈ 𝒟ⁿ(U)`.  Replace `f`
by a globally `Λ`-Lipschitz `C¹` map `φ` with `φ = f` and `Dφ = Df` on `K`, and cut
`M₁ = M ∩ K` (with `∫_{M₁} θ < ∞`), up to an `Hⁿ`-null set, into disjoint bi-Lipschitz pieces
`Gⱼ(Aⱼ)` on which `φ ∘ Gⱼ` either is bi-Lipschitz with injective derivative or has nowhere
injective derivative.  On each piece `ξ ∘ Gⱼ = ±DGⱼ#e / J_{Gⱼ}` a.e., and the area formula turns
the contribution of `Gⱼ(Aⱼ)` to `Q(ω)` into `∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩ dHⁿ`, with
`Nⱼ ⊆ φ(Gⱼ(Aⱼ)) ⊆ f(K) ⊆ U`, an integer `gⱼ ≠ 0` on `Nⱼ`, an orientation `ηⱼ` of `TNⱼ`, and
`∫_{Nⱼ} |gⱼ| ≤ Λⁿ ∫_{Gⱼ(Aⱼ)} θ`.  As `|⟨β, ξ⟩| ≤ ‖β‖` a.e. on `M` and `‖Dφ‖ ≤ Λ`, the integrand
`θ ⟨ω(φ) ∘ Dφ, ξ⟩` is `Hⁿ⌞M₁`-integrable, so `Q(ω) = Σⱼ ∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩ dHⁿ` with
`Σⱼ ∫_{Nⱼ} |gⱼ| ≤ Λⁿ ∫_{M₁} θ < ∞`; gluing the pieces gives an integer multiplicity triple
representing `Q`. -/
theorem Submission.dor_lmb_pc_pushforward_isIntegerMultiplicity : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (Q : GeometricCurrentOn U n), IsOpen U → 0 < n → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → IsIntegerMultiplicity Q := by
  intro hTL P n U K O R f Q hU _hn hK hKU hMK hO hKO hf hfK hQ
  -- Step 1(b): a globally Lipschitz `C¹` map `φ` with `φ = f` and `Dφ = Df` on `K`
  obtain ⟨φ, Λ, hφ, hφL, hφK⟩ :=
    Submission.dtc_bc_lc_pfi_c1_cutoff_lipschitz P O K f hO hK hKO hf
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- Step 1(a): `M₁ = M ∩ K` is Borel with `∫_{M₁} θ dHⁿ < ∞`
  have hM₁ : MeasurableSet (R.carrier ∩ K) :=
    R.measurableSet_carrier.inter hK.isClosed.measurableSet
  have hθM₁ : ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ :=
    R.locallyIntegrable_mult K hK hKU
  -- Step 2: disjoint bi-Lipschitz pieces `Gⱼ(Aⱼ)` covering `M₁` up to a null set, on which
  -- `φ ∘ Gⱼ` is bi-Lipschitz with injective derivative or has nowhere injective derivative
  obtain ⟨G, A, κ, hGL, hA, hκ, hGκ, hGd, hGA, hGAM, hdisj, hnull, hφG⟩ :=
    Submission.dtc_bc_lc_pfi_refined_bilipschitz_pieces P n (R.carrier ∩ K) φ hM₁
      (R.rectifiable.mono inter_subset_left) hφd
  choose L hL using hGL
  have hGAR : ∀ j, G j '' A j ⊆ R.carrier := fun j => (hGAM j).trans inter_subset_left
  -- Step 4: `ξ ∘ Gⱼ = ±DGⱼ#e / J_{Gⱼ}` a.e. on `Aⱼ`; Steps 5–8: the image pieces
  -- `Nⱼ ⊆ φ(Gⱼ(Aⱼ))` with integer multiplicities `gⱼ` and orientations `ηⱼ`
  have hpiece := fun j =>
    Submission.dtc_bc_lc_pfi_piece_pushforward_image P n U R (G j) (A j) (L j) (κ j) φ Λ
      (hL j) (hA j) (hκ j) (hGκ j) (hGd j) (hGAR j)
      (ne_top_of_le_ne_top hθM₁ (lintegral_mono_set (hGAM j)))
      (Submission.dtc_bc_lc_pfi_piece_orientation_sign P n U R (G j) (A j) (L j) (κ j) hU
        (hL j) (hA j) (hκ j) (hGκ j) (hGd j) (hGAR j))
      hφd hφL (hφG j)
  choose N g η hN hNφ hNr hg hg0 hη hηT hgθ hNint using hpiece
  -- Steps 9–11: glue the image pieces into one integer multiplicity triple in `U`
  refine Submission.dtc_bc_lc_pfi_isIntegerMultiplicity_of_pieces hTL P n U N g η Q hU hN ?_
    hNr hg hg0 hη hηT ?_ ?_
  · -- `Nⱼ ⊆ φ(Gⱼ(Aⱼ)) ⊆ φ(K) = f(K) ⊆ U`
    intro j y hy
    obtain ⟨x, hx, rfl⟩ := hNφ j hy
    have hxK : x ∈ K := (hGAM j hx).2
    rw [(hφK x hxK).1]
    exact hfK (mem_image_of_mem f hxK)
  · -- `Σⱼ ∫_{Nⱼ} |gⱼ| ≤ Λⁿ Σⱼ ∫_{Gⱼ(Aⱼ)} θ = Λⁿ ∫_{⋃ⱼ Gⱼ(Aⱼ)} θ ≤ Λⁿ ∫_{M₁} θ < ∞`
    have hle : ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] ≤
        (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
      calc ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n]
          ≤ ∑' j, (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G j '' A j, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
            ENNReal.tsum_le_tsum hgθ
        _ = (Λ : ℝ≥0∞) ^ n * ∫⁻ x in ⋃ j, G j '' A j, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            rw [ENNReal.tsum_mul_left, lintegral_iUnion hGA hdisj]
        _ ≤ (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            gcongr
            exact iUnion_subset hGAM
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hθM₁) hle
  · -- `Q(ω) = ∫_{M₁} θ ⟨ω(φ) ∘ Dφ, ξ⟩ = Σⱼ ∫_{Gⱼ(Aⱼ)} θ ⟨ω(φ) ∘ Dφ, ξ⟩ = Σⱼ ∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩`
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- Step 1(c): `x ↦ θ(x) ⟨ω(φ(x)) ∘ Dφ(x), ξ(x)⟩` is `Hⁿ⌞M₁`-integrable, being bounded by
    -- `C Λⁿ θ` (`|⟨β, ξ⟩| ≤ ‖β‖` a.e. on `M`, `‖β ∘ Dφ‖ ≤ ‖β‖ ‖Dφ‖ⁿ`, `‖Dφ‖ ≤ Λ`)
    have hβ : Continuous fun x =>
        ((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x) := by
      have h := (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
        (hφ.continuous_fderiv one_ne_zero)).clm_apply (hωc.comp hφ.continuous)
      simpa only [Function.comp_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply] using h
    have hθ : Measurable fun x => (R.mult x : ℝ) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
    have hθi : Integrable (fun x => (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
      refine ⟨hθ.aestronglyMeasurable, ?_⟩
      show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μHE[n].restrict (R.carrier ∩ K)) < ∞
      simp only [Real.enorm_natCast]
      exact lt_top_iff_ne_top.mpr hθM₁
    have hint : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x
        (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)))
        (R.carrier ∩ K) μHE[n] := by
      refine Integrable.mono' (hθi.const_mul (C * (Λ : ℝ) ^ n))
        (hθ.aestronglyMeasurable.mul ?_) ?_
      · exact Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
          (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
          (R.aestronglyMeasurable_orient.mono_set inter_subset_left) hβ.aestronglyMeasurable
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients]
          with x hx
        obtain ⟨T, -, hT⟩ := hx
        have h1 := (Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n).2.1 _ T hT
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x))
        have h2 := ContinuousAlternatingMap.norm_compContinuousLinearMap_le
          ((ω : DifferentialForm (Euclid P) n) (φ x)) (fderiv ℝ φ x)
        rw [Fintype.card_fin] at h2
        have h3 : ‖fderiv ℝ φ x‖ ^ n ≤ (Λ : ℝ) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hφL) n
        rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_comm (C * (Λ : ℝ) ^ n)]
        gcongr
        exact h1.trans (h2.trans (mul_le_mul (hC _) h3 (by positivity) hC0))
    calc Q ω = ∫ x in R.carrier ∩ K, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] := by
          -- `Hⁿ(M ∖ K) = 0`, and `φ = f`, `Dφ = Df` on `M₁ ⊆ K`
          rw [hQ ω, setIntegral_congr_set (ae_eq_set.mpr
            ⟨by rw [sdiff_self_inter]; exact hMK,
              by rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty]⟩)]
          refine setIntegral_congr_fun hM₁ fun x hx => ?_
          simp only [(hφK x hx.2).1, (hφK x hx.2).2]
      _ = ∫ x in ⋃ j, G j '' A j, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] :=
          -- the pieces cover `M₁` up to an `Hⁿ`-null set
          setIntegral_congr_set (ae_eq_set.mpr ⟨hnull,
            by rw [sdiff_eq_empty.mpr (iUnion_subset hGAM), measure_empty]⟩)
      _ = ∑' j, ∫ x in G j '' A j, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] :=
          integral_iUnion hGA hdisj (hint.mono_set (iUnion_subset hGAM))
      _ = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y ((ω : DifferentialForm (Euclid P) n) y)
          ∂μHE[n] :=
          tsum_congr fun j => hNint j _ hωc.stronglyMeasurable
/-- **Cut-off of a `C¹` map to a compactly supported perturbation of the identity** (the cutoff
step of the `C¹` push-forward, Simon 6.2.24).  Let `O` be open, `K ⊆ O` compact and `f` `C¹` on
`O`.  Take `δ > 0` with `cthickening δ K ⊆ O` and a smooth cutoff `χ` with
`support χ = thickening δ K` and `χ = 1` exactly on `cthickening (δ/2) K`.  Then
`φ = χ f + (1 − χ) id` is `C¹` on `ℝᴾ`, equals `f` on the open neighbourhood
`V = thickening (δ/2) K` of `K` (so `Dφ = Df` on `V`), and equals `id` off the compact set
`K' = spt χ ⊆ cthickening δ K ⊆ O`. -/
theorem Submission.dimred_mbl_pfb_c1_compact_perturbation : ∀ (P : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → IsCompact K → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (φ : Euclid P → Euclid P) (V K' : Set (Euclid P)), IsOpen V ∧ K ⊆ V ∧ IsCompact K' ∧ K' ⊆ O ∧ ContDiff ℝ 1 φ ∧ (∀ x ∈ V, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x) ∧ ∀ x, x ∉ K' → φ x = x := by
  intro P O K f hO hK hKO hf
  -- Step 1: a margin `δ > 0` with `cthickening δ K ⊆ O`
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  -- Step 2: smooth Urysohn cutoff `χ` with `support χ = thickening δ K` and
  -- `χ x = 1 ↔ x ∈ cthickening (δ/2) K`
  obtain ⟨χ, hχ, -, hχs, hχt⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening : IsOpen (thickening δ K))
    (isClosed_cthickening : IsClosed (cthickening (δ / 2) K))
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  -- Step 3: `K' = spt χ ⊆ cthickening δ K ⊆ O` is compact
  have hK'δ : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening δ K
  have hK'O : tsupport χ ⊆ O := hK'δ.trans hδO
  have hK' : IsCompact (tsupport χ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hK'δ
  -- Step 4: `φ = χ f + (1 − χ) id`, `V = thickening (δ/2) K`
  refine ⟨fun x => χ x • f x + (1 - χ x) • x, thickening (δ / 2) K, tsupport χ,
    isOpen_thickening, self_subset_thickening (half_pos hδ) K, hK', hK'O, ?_, ?_, ?_⟩
  · -- Step 7: `φ` is `C¹` at every point
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · -- (a) on `O`, `φ` is a `C¹` combination of `χ`, `f` and `id`
      have hfx : ContDiffAt ℝ 1 f x := hf.contDiffAt (hO.mem_nhds hx)
      exact (hχ1.contDiffAt.smul hfx).add
        ((contDiffAt_const.sub hχ1.contDiffAt).smul contDiffAt_id)
    · -- (b) off `O ⊇ K'`, `φ = id` near `x`
      have hxK' : x ∉ tsupport χ := fun h => hx (hK'O h)
      have hev : (fun y => χ y • f y + (1 - χ y) • y) =ᶠ[𝓝 x] id := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxK'] with y hy
        simp [hy]
      exact contDiffAt_id.congr_of_eventuallyEq hev
  · -- Step 6: `χ = 1` on the open set `V`, so `φ = f` near each `x ∈ V`
    intro x hx
    have hev : (fun y => χ y • f y + (1 - χ y) • y) =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
      have hy1 : χ y = 1 := (hχt y).1 (thickening_subset_cthickening _ _ hy)
      simp [hy1]
    exact ⟨hev.eq_of_nhds, hev.fderiv_eq⟩
  · -- Step 5: `χ = 0` off `K'`, so `φ = id` there
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
/-- **Pull-back of a test form by a compactly supported perturbation of the identity**
(Simon 6.2.23–6.2.24).  Let `K'` be compact and `ψ` a `C^∞` map with `ψ = id` off `K'`.  For a
test form `α ∈ 𝒟ᵈ`, the pull-back `ψ^#α(x) = α(ψ(x)) ∘ Dψ(x)` is a test form with
`spt ψ^#α ⊆ spt α ∪ K'`.  It is `C^∞` as `ψ^#α(x) = Φ(Dψ(x))(α(ψ(x)))`, where the precomposition
`Φ(L) = (γ ↦ γ ∘ L)` is analytic in `L`.  Off the closed compact set `spt α ∪ K'` we have
`ψ(z) = z` and `α(z) = 0`, so `ψ^#α(z) = 0`. -/
theorem Submission.dpf_pb_smooth_pullback_isTestForm : ∀ (P d : ℕ) (K' : Set (Euclid P)) (ψ : Euclid P → Euclid P) (α : DifferentialForm (Euclid P) d), IsCompact K' → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ x, x ∉ K' → ψ x = x) → IsTestForm α → IsTestForm (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ∧ tsupport (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ⊆ tsupport α ∪ K' := by
  intro P d K' ψ α hK hψ hfix hα
  -- `α` is `C^∞` with compact support
  obtain ⟨hαs, hαc⟩ := hα
  -- the precomposition `Φ(L) = (γ ↦ γ ∘ L)` on `d`-covectors is analytic, hence `C^∞`
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclid P →L[ℝ] Euclid P) →
        (Euclid P [⋀^Fin d]→L[ℝ] ℝ) →L[ℝ] (Euclid P [⋀^Fin d]→L[ℝ] ℝ)) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- `Dψ` and `α ∘ ψ` are `C^∞`, so `ψ^#α = Φ(Dψ)(α ∘ ψ)` is `C^∞`
  have hDψ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.mp hψ).2
  have hαψ : ContDiff ℝ (⊤ : ℕ∞) (fun x => α (ψ x)) := hαs.comp hψ
  have hsmooth : IsSmoothForm (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) :=
    (hΦ.comp hDψ).clm_apply hαψ
  -- off the closed set `spt α ∪ K'`, `ψ(z) = z` and `α(z) = 0`, so `ψ^#α(z) = 0`
  have hsupp : tsupport (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ⊆
      tsupport α ∪ K' := by
    refine closure_minimal ?_ ((isClosed_tsupport α).union hK.isClosed)
    intro z hz
    by_contra hzF
    rw [mem_union, not_or] at hzF
    refine Function.mem_support.mp hz ?_
    show (α (ψ z)).compContinuousLinearMap (fderiv ℝ ψ z) = 0
    rw [hfix z hzF.2, image_eq_zero_of_notMem_tsupport hzF.1]
    ext v
    simp
  -- `spt ψ^#α` is a closed subset of the compact set `spt α ∪ K'`
  exact ⟨⟨hsmooth, (IsCompact.union hαc hK).of_isClosed_subset (isClosed_tsupport _) hsupp⟩,
    hsupp⟩
/-- **Dominated convergence for pulled-back integrals** (Simon 6.2.23–6.2.24, the limit step in the
push-forward by a `C¹` map).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in `U`, `α` a
continuous `n`-form with compact support in `U`, and `ψₖ` `C¹` maps equal to the identity off the
compact `K' ⊆ U`, with `‖Dψₖ‖ ≤ C`, `ψₖ → φ` and `Dψₖ → Dφ` pointwise.  Then
`∫_M θ ⟨α(ψₖ)∘Dψₖ, ξ⟩ dHⁿ → ∫_M θ ⟨α(φ)∘Dφ, ξ⟩ dHⁿ`: the integrands are dominated by
`A Cⁿ θ 1_{spt α ∪ K'}` (`‖α‖ ≤ A`, `|ξ(γ)| ≤ ‖γ‖` a.e.), which is integrable since `θ` is locally
`Hⁿ⌞M`-integrable in `U`. -/
theorem Submission.dpf_pb_imrep_pullback_integral_tendsto : ∀ (P n : ℕ) (U K' : Set (Euclid P)) (R : IMRep U n) (α : DifferentialForm (Euclid P) n) (ψ : ℕ → Euclid P → Euclid P) (φ : Euclid P → Euclid P) (C : ℝ), IsCompact K' → K' ⊆ U → Continuous α → HasCompactSupport α → tsupport α ⊆ U → (∀ k, ContDiff ℝ 1 (ψ k)) → (∀ k x, x ∉ K' → ψ k x = x) → (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) → (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) → (∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n])) := by
  intro P n U K' R α ψ φ C hK' hK'U hα hαc hαU hψ hψid hψC hψφ hDψ
  -- `C₀ = spt α ∪ K'` is compact, closed (hence measurable) and contained in `U`
  have hC₀ : IsCompact (tsupport α ∪ K') := hαc.isCompact.union hK'
  have hC₀m : MeasurableSet (tsupport α ∪ K') := hC₀.isClosed.measurableSet
  -- `‖α‖ ≤ A` everywhere, so `0 ≤ A`
  obtain ⟨A, hA⟩ := hα.bounded_above_of_compact_support hαc
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- `θ` is measurable
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- orientation bound: `|ξ(x)(γ)| = |γ(τ)| ≤ ‖γ‖ ∏ ‖τᵢ‖ = ‖γ‖` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂μHE[n].restrict R.carrier, ∀ γ : Covector (Euclid P) n,
      |R.orient x γ| ≤ ‖γ‖ := by
    filter_upwards [R.orients] with x ⟨Q, _, τ, hτ, _, hor⟩ γ
    have hγ : |γ τ| ≤ ‖γ‖ := by
      have h := γ.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one] at h
      rwa [Real.norm_eq_abs] at h
    rcases hor with h | h
    · rw [h γ]; exact hγ
    · rw [h γ, abs_neg]; exact hγ
  -- `x ↦ α(ψₖ(x))∘Dψₖ(x)` is continuous
  have hβ : ∀ k, Continuous fun x =>
      (α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x) := by
    intro k
    have h1 : Continuous fun x => (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ (ψ k) x) : Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n) :=
      ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
        ((hψ k).continuous_fderiv one_ne_zero)
    exact h1.clm_apply (hα.comp (hψ k).continuous)
  refine tendsto_integral_of_dominated_convergence
    ((tsupport α ∪ K').indicator fun x => A * C ^ n * (R.mult x : ℝ)) ?_ ?_ ?_ ?_
  · -- each integrand is a.e. strongly measurable
    intro k
    refine hθm.aestronglyMeasurable.mul ?_
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    exact Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P n) (v : Covector (Euclid P) n) => L v) hev
      R.aestronglyMeasurable_orient (hβ k).aestronglyMeasurable
  · -- the bound `A Cⁿ θ 1_{C₀}` is integrable, as `θ` is integrable on `M ∩ C₀`
    refine IntegrableOn.integrable_indicator ?_ hC₀m
    refine Integrable.const_mul ?_ _
    show Integrable _ ((μHE[n].restrict R.carrier).restrict (tsupport α ∪ K'))
    rw [Measure.restrict_restrict hC₀m, inter_comm]
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in R.carrier ∩ (tsupport α ∪ K'), ‖(R.mult x : ℝ)‖ₑ ∂μHE[n] < ∞
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult _ hC₀ (union_subset hαU hK'U))
  · -- domination `|hₖ| ≤ A Cⁿ θ 1_{C₀}` a.e.
    intro k
    filter_upwards [hξ] with x hx
    by_cases hxC : x ∈ tsupport α ∪ K'
    · rw [indicator_of_mem hxC]
      have hβle : ‖(α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)‖ ≤ A * C ^ n := by
        refine (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Fintype.card_fin]
        exact mul_le_mul (hA _) (pow_le_pow_left₀ (norm_nonneg _) (hψC k x) n)
          (pow_nonneg (norm_nonneg _) n) hA0
      rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x))|
          ≤ (R.mult x : ℝ) * (A * C ^ n) :=
            mul_le_mul_of_nonneg_left ((hx _).trans hβle) (Nat.cast_nonneg _)
        _ = A * C ^ n * (R.mult x : ℝ) := mul_comm _ _
    · -- off `C₀`: `ψₖ(x) = x` and `α(x) = 0`, so the integrand vanishes
      rw [indicator_of_notMem hxC]
      have hxK : x ∉ K' := fun h => hxC (Or.inr h)
      have hxα : x ∉ tsupport α := fun h => hxC (Or.inl h)
      have h0 : (0 : Covector (Euclid P) n).compContinuousLinearMap (fderiv ℝ (ψ k) x) = 0 :=
        map_zero (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ (ψ k) x))
      rw [hψid k x hxK, image_eq_zero_of_notMem_tsupport hxα, h0, map_zero, mul_zero, norm_zero]
  · -- pointwise convergence, by continuity of `α`, of `L ↦ (· ∘ L)` and of evaluation
    refine Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.mul (((R.orient x).continuous.tendsto _).comp ?_)
    have h1 : Tendsto (fun k => (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ (ψ k) x) : Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n)) atTop
        (𝓝 (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ φ x))) :=
      (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.tendsto _).comp (hDψ x)
    have h2 : Tendsto (fun k => α (ψ k x)) atTop (𝓝 (α (φ x))) := (hα.tendsto _).comp (hψφ x)
    exact (isBoundedBilinearMap_apply.continuous.tendsto _).comp (h1.prodMk_nhds h2)
/-- Simon 6.2.24(1), reduction from `C¹` to smooth maps (step 3 of the push-forward proof): a `C¹`
map `φ` of `ℝᴾ` with `φ = id` off the compact set `K ⊆ U` is the pointwise `C¹` limit of `C^∞`
maps `ψₖ` that equal `id` off one compact `K' ⊆ U` and have uniformly bounded differentials.
`K' = cthickening δ K ⊆ U` and `ψₖ = id + ρₖ ⋆ (φ − id)`, `ρₖ` a normalized smooth bump supported
in `B_{δ/(k+2)}(0)`; then `Dψₖ = I + ρₖ ⋆ D(φ − id)`, so `‖Dψₖ‖ ≤ 1 + sup ‖D(φ − id)‖`, and the
mollifications of the continuous `φ − id` and `D(φ − id)` converge pointwise. -/
theorem Submission.dpf_smooth_approx_compact_perturbation : ∀ (P : ℕ) (U K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ (ψ : ℕ → Euclid P → Euclid P) (K' : Set (Euclid P)) (C : ℝ), IsCompact K' ∧ K' ⊆ U ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧ (∀ k x, x ∉ K' → ψ k x = x) ∧ (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) ∧ (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) ∧ ∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x)) := by
  intro P U K φ hU hK hKU hφ hfix
  -- Step 1: a margin `δ > 0` with `K' = cthickening δ K ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: the perturbation `g = φ - id` is `C¹` and vanishes off `K`; `‖Dg‖ ≤ A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → Euclid P, ∀ x, g x = φ x - x := ⟨fun x => φ x - x, fun _ => rfl⟩
  have hgφ : g = fun x => φ x - x := funext hg
  have hg1 : ContDiff ℝ 1 g := by
    rw [hgφ]
    exact hφ.sub contDiff_id
  have hgK : ∀ x, x ∉ K → g x = 0 := fun x hx => by rw [hg, hfix x hx, sub_self]
  have hgcs : HasCompactSupport g := HasCompactSupport.intro hK hgK
  have hgc : Continuous g := hg1.continuous
  have hDgc : Continuous (fderiv ℝ g) := hg1.continuous_fderiv one_ne_zero
  have hDg : ∀ x, fderiv ℝ g x = fderiv ℝ φ x - ContinuousLinearMap.id ℝ (Euclid P) := by
    intro x
    rw [hgφ]
    exact (((hφ.differentiable one_ne_zero) x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  obtain ⟨A, hA⟩ := hDgc.bounded_above_of_compact_support (hgcs.fderiv ℝ)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 3: nonnegative smooth `ρ k` with `∫ ρ k = 1`, supported in `ball 0 (r k)`, where
  -- `r k = δ / (k + 2)`: the bump `β k` with `rOut = r k`, divided by its integral
  obtain ⟨r, hr0, hrδ, hrlim⟩ : ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ (∀ k, r k ≤ δ) ∧
      Tendsto r atTop (𝓝 0) := by
    refine ⟨fun k => δ / ((k : ℝ) + 2), fun k => by positivity, fun k => ?_, ?_⟩
    · exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨ρ, hρs, hρn, hρi, hρsupp⟩ : ∃ ρ : ℕ → Euclid P → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k)) ∧ (∀ k x, 0 ≤ ρ k x) ∧ (∀ k, ∫ x, ρ k x = 1) ∧
      (∀ k, support (ρ k) ⊆ ball 0 (r k)) := by
    let β : ∀ k, ContDiffBump (0 : Euclid P) := fun k =>
      ⟨r k / 2, r k, half_pos (hr0 k), half_lt_self (hr0 k)⟩
    have hβi : ∀ k, 0 < ∫ x, β k x := fun k => by
      rw [integral_pos_iff_support_of_nonneg (fun x => (β k).nonneg)
        ((β k).continuous.integrable_of_hasCompactSupport (β k).hasCompactSupport),
        (β k).support_eq]
      exact measure_ball_pos _ _ (hr0 k)
    refine ⟨fun k x => (∫ y, β k y)⁻¹ * β k x, fun k => contDiff_const.mul (β k).contDiff,
      fun k x => mul_nonneg (inv_nonneg.2 (hβi k).le) (β k).nonneg, fun k => ?_,
      fun k x hx => ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ (hβi k).ne']
    · have hx' : x ∈ support (β k) := right_ne_zero_of_mul hx
      rwa [(β k).support_eq] at hx'
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall 0 (r k)) fun x hx =>
      notMem_support.1 fun h => hx (ball_subset_closedBall (hρsupp k h))
  have hρloc : ∀ k, LocallyIntegrable (ρ k) volume := fun k => (hρs k).continuous.locallyIntegrable
  have hsmall : Tendsto (fun k => support (ρ k)) atTop (𝓝 (0 : Euclid P)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [(tendsto_order.1 hrlim).2 ε hε] with k hk
    exact (hρsupp k).trans ((ball_subset_ball hk.le).trans hεt)
  -- Steps 4 and 6: `ψ k = id + ρ k ⋆ g` has derivative `I + ρ k ⋆ Dg` (the `precompR`
  -- convolution of `hasFDerivAt_convolution_right` is the scalar one)
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P).precompR (Euclid P) =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (Euclid P →L[ℝ] Euclid P) →L[ℝ] (Euclid P →L[ℝ] Euclid P)) := by
    ext a f v
    simp [ContinuousLinearMap.precompR]
  have hderiv : ∀ k x, HasFDerivAt
      (fun y => y + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume y)
      (ContinuousLinearMap.id ℝ (Euclid P) +
        convolution (ρ k) (fderiv ℝ g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) x := by
    intro k x
    have h := hgcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hρloc k) hg1 x
    rw [hL] at h
    exact (hasFDerivAt_id x).add h
  -- Step 5: off `K'`, `g = 0` on `ball x (r k)`, so `(ρ k ⋆ g) x = 0`
  have hsupp : ∀ k x, x ∉ cthickening δ K →
      convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro k x hx
    have hgy : ∀ y ∈ ball x (r k), g y = 0 := fun y hy => hgK y fun hyK =>
      hx (mem_cthickening_of_dist_le x y δ K hyK ((mem_ball'.1 hy).le.trans (hrδ k)))
    rw [convolution_eq_right' _ (hρsupp k) fun y hy =>
      (hgy y hy).trans (hgy x (mem_ball_self (hr0 k))).symm, hgy x (mem_ball_self (hr0 k))]
    simp
  refine ⟨fun k x => x + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x,
    cthickening δ K, 1 + A, hK.cthickening, hδU, fun k => ?_, fun k x hx => ?_, fun k x => ?_,
    fun x => ?_, fun x => ?_⟩
  · exact contDiff_id.add
      ((hρc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs k)
        hgc.locallyIntegrable)
  · simp only [hsupp k x hx, add_zero]
  · -- Step 6: `‖Dψ k‖ ≤ ‖I‖ + sup ‖Dg‖ ≤ 1 + A`
    rw [(hderiv k x).fderiv]
    refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
    have h := dist_convolution_le (x₀ := x) (z₀ := 0) (μ := volume) hA0 (hρsupp k) (hρn k) (hρi k)
      hDgc.aestronglyMeasurable fun y _ => by rw [dist_zero_right]; exact hA y
    rwa [dist_zero_right] at h
  · -- Step 7: `ψ k x → x + g x = φ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hgc.aestronglyMeasurable) ((hgc.tendsto x).comp tendsto_snd)
      tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add h
    rwa [hg x, add_sub_cancel] at h2
  · -- Step 7: `Dψ k x → I + Dg x = Dφ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => fderiv ℝ g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hDgc.aestronglyMeasurable)
      ((hDgc.tendsto x).comp tendsto_snd) tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ContinuousLinearMap.id ℝ (Euclid P))
      atTop (𝓝 (ContinuousLinearMap.id ℝ (Euclid P)))).add h
    rw [hDg x, add_sub_cancel] at h2
    exact h2.congr fun k => ((hderiv k x).fderiv).symm

/-- Simon 6.2.24(1), `∂f_#T = f_#∂T`, for the `C¹` push-forward formula of 6.2.24(2) (step 3
of the push-forward proof): if `T = τ(M, θ, ξ)` has `∂T = 0` in `U` and
`S(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ`, where the `C¹` map `φ` is the identity off a compact
`K ⊆ U`, then `∂S = 0` in `U`.  Take `C^∞` maps `ψₖ`, equal to the identity off one compact
`K' ⊆ U`, with `‖Dψₖ‖ ≤ C`, `ψₖ → φ` and `Dψₖ → Dφ` pointwise.  For `η ∈ 𝒟ⁿ⁻¹(U)`,
`ψₖ^#η ∈ 𝒟ⁿ⁻¹(U)` and `d(ψₖ^#η) = ψₖ^#(dη)`, so `0 = ∂T(ψₖ^#η) = ∫_M θ ⟨ψₖ^#(dη), ξ⟩ dHⁿ`;
by dominated convergence these integrals tend to `S(dη) = ∂S(η)`. -/
theorem Submission.dpf_pushforward_formula_boundaryVanishes : ∀ (P n : ℕ) (U K : Set (Euclid P)) (T S : GeometricCurrentOn U n) (R : IMRep U n) (φ : Euclid P → Euclid P), IsOpen U → R.Represents T → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → (∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]) → BoundaryVanishes T → BoundaryVanishes S := by
  intro P n U K T S R φ hU hRT hK hKU hφ hφK hS hT
  -- Step 1: `∂ = 0` in degree `0`; for `n = m + 1` show `∂S(η) = S(dη) = 0` for every `η`
  rcases n with _ | m
  · trivial
  change T.boundary = 0 at hT
  change S.boundary = 0
  -- Step 2: `C^∞` maps `ψₖ = id` off a compact `K' ⊆ U`, `‖Dψₖ‖ ≤ C`, `ψₖ → φ`, `Dψₖ → Dφ`
  obtain ⟨ψ, K', C, hK', hK'U, hψ, hψK', hψC, hψφ, hDψφ⟩ :=
    Submission.dpf_smooth_approx_compact_perturbation P U K φ hU hK hKU hφ hφK
  ext η
  rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply, hS]
  -- the test form `α = dη ∈ 𝒟ⁿ(U)`
  set α : DifferentialForm (Euclid P) (m + 1) :=
    (exteriorDerivativeTestOn U m η : DifferentialForm (Euclid P) (m + 1))
  have hα : IsTestForm α ∧ tsupport α ⊆ U := (exteriorDerivativeTestOn U m η).property
  -- Steps 3–5: `∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ = ∂T(ψₖ^#η) = 0` for every `k`
  have hI : ∀ k, ∫ x in R.carrier, (R.mult x : ℝ) *
      R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)) ∂μHE[m + 1] = 0 := by
    intro k
    -- Step 3: `ψₖ^#η` is a test form supported in `tsupport η ∪ K' ⊆ U`
    obtain ⟨hηk, hηkK⟩ := Submission.dpf_pb_smooth_pullback_isTestForm P m K' (ψ k)
      (η : DifferentialForm (Euclid P) m) hK' (hψ k) (hψK' k) η.property.1
    let ηk : TestFormOn U m :=
      ⟨fun x => ((η : DifferentialForm (Euclid P) m) (ψ k x)).compContinuousLinearMap
        (fderiv ℝ (ψ k) x), hηk, hηkK.trans (union_subset η.property.2 hK'U)⟩
    -- Step 4: `d(ψₖ^#η) = ψₖ^#(dη)` (Simon 6.1.14; Mathlib `extDeriv_pullback`)
    have hnat : (exteriorDerivativeTestOn U m ηk : DifferentialForm (Euclid P) (m + 1)) =
        fun x => (α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x) := by
      funext x
      exact extDeriv_pullback (η.property.1.1.differentiable (by simp)).differentiableAt
        (hψ k).contDiffAt (by simp)
    -- Step 5: `0 = ∂T(ψₖ^#η) = T(d(ψₖ^#η)) = ∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ`
    have h0 : T (exteriorDerivativeTestOn U m ηk) = 0 := by
      rw [← GeometricCurrentOn.boundary_apply, hT, GeometricCurrentOn.zero_apply]
    rw [hRT, IMRep.action, hnat] at h0
    exact h0
  -- Step 6: dominated convergence, `∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ → ∫_M θ ⟨φ^#α, ξ⟩ dHⁿ = S(dη)`
  have hlim := Submission.dpf_pb_imrep_pullback_integral_tendsto P (m + 1) U K' R α ψ φ C hK'
    hK'U hα.1.1.continuous hα.1.2 hα.2 (fun k => (hψ k).of_le (by exact_mod_cast le_top)) hψK'
    hψC hψφ hDψφ
  -- Step 7: the limit of the vanishing integrals is `0`
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k => (hI k).symm)

/-- Simon 6.2.24(1), `∂f_#T = f_#∂T`, for a `C¹` map `f` on an open `O ⊇ K` (step 5(d) of the
projected comparison): if `X = τ(M, θ, ξ)` has `∂X = 0` in `U`, `Hⁿ(M ∖ K) = 0` for a compact
`K ⊆ U`, and `Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ⟩ dHⁿ`, then `∂Q = 0` in `U`.  Replace `f` by a
`C¹` map `φ` equal to `f` on an open `V ⊇ K` and to the identity off a compact `K' ⊆ O ∩ U`.
Since `φ = f` and `Dφ = Df` on `K`, which carries `Hⁿ`-almost all of `M`,
`Q(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ`, and the push-forward formula for `φ` gives `∂Q = 0`. -/
theorem Submission.dor_lmb_pc_pushforward_boundaryVanishes : ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (X Q : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → R.Represents X → BoundaryVanishes X → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → BoundaryVanishes Q := by
  intro P n U K O R f X Q hU hK hKU hMK hO hKO hf hRX hX hQ
  -- Step 1: a `C¹` map `φ` with `φ = f`, `Dφ = Df` on an open `V ⊇ K` and `φ = id` off a
  -- compact `K' ⊆ O ∩ U`
  obtain ⟨φ, V, K', -, hKV, hK', hK'OU, hφ, hφf, hφK'⟩ :=
    Submission.dimred_mbl_pfb_c1_compact_perturbation P (O ∩ U) K f (hO.inter hU) hK
      (subset_inter hKO hKU) (hf.mono inter_subset_left)
  -- Step 2: `Hⁿ`-almost every point of `M` lies in `K`
  have hae : ∀ᵐ x ∂μHE[n], x ∈ R.carrier → x ∈ K := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hMK
    exact not_imp.1 hx
  -- Step 3: `Q(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ`, so `∂Q = 0` by the push-forward formula
  refine Submission.dpf_pushforward_formula_boundaryVanishes P n U K' X Q R φ hU hRX hK'
    (hK'OU.trans inter_subset_right) hφ hφK' (fun ω => ?_) hX
  rw [hQ ω]
  refine setIntegral_congr_ae R.measurableSet_carrier (hae.mono fun x hx hxM => ?_)
  obtain ⟨h1, h2⟩ := hφf x (hKV (hx hxM))
  simp only [h1, h2]
/-- **Flatness of a submanifold at a chart point** (step 2 of the approximate-tangent-space
argument; Simon Ch. 2, 4.1–4.3).  Let `ψ : V → W` be a 1:1 `C¹` map with `ψ(V) = W ∩ N`, proper
into `W`, and `Dψ(v)` injective.  Then near `ψ(v)` every `z ∈ N` lies within `ε|z − ψ(v)|` of
`ψ(v) + range Dψ(v)`.  Properness, continuity and injectivity of `ψ` force `z = ψ(β)` with `β`
close to `v`; the first-order expansion at `v` and the coercivity `|h| ≤ K|Dψ(v)h|` then absorb
the remainder. -/
theorem Submission.atsm_chart_image_flat : ∀ (P d : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → Injective (fderiv ℝ ψ v) → v ∈ V → ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z (ψ v) < ρ → ∃ h : Euclid d, ‖z - ψ v - fderiv ℝ ψ v h‖ ≤ ε * ‖z - ψ v‖ := by
  intro P d N W V ψ v hV hW hψ hinj himg hprop hLinj hv ε hε
  set L := fderiv ℝ ψ v with hLdef
  have hdiff : DifferentiableAt ℝ ψ v :=
    (hψ.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)
  have hL : HasFDerivAt ψ L v := hdiff.hasFDerivAt
  have hcont : ContinuousOn ψ V := hψ.continuousOn
  have hψvW : ψ v ∈ W := by
    have : ψ v ∈ ψ '' V := mem_image_of_mem ψ hv
    rw [himg] at this
    exact this.1
  -- coercivity of the injective derivative
  obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith (L : Euclid d →ₗ[ℝ] Euclid P)
    (LinearMap.ker_eq_bot.mpr hLinj)
  have hcoer : ∀ h : Euclid d, ‖h‖ ≤ K * ‖L h‖ := fun h =>
    ContinuousLinearMap.bound_of_antilipschitz L hK h
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  set η : ℝ := min (1 / (2 * K)) (ε / (2 * K)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηK : η * K ≤ 1 / 2 := by
    calc η * K ≤ 1 / (2 * K) * K := by gcongr; exact min_le_left _ _
      _ = 1 / 2 := by field_simp
  have hηε : η * (2 * K) ≤ ε := by
    calc η * (2 * K) ≤ ε / (2 * K) * (2 * K) := by gcongr; exact min_le_right _ _
      _ = ε := by field_simp
  -- first-order expansion
  obtain ⟨σ, hσ, hσball⟩ := Metric.eventually_nhds_iff.1 (hL.isLittleO.bound hη)
  -- a compact set away from v
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψvW
  set δ₀ : ℝ := δ₁ / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hcbW : closedBall (ψ v) δ₀ ⊆ W := (closedBall_subset_ball (by linarith)).trans hδ₁W
  have hA : IsCompact (V ∩ ψ ⁻¹' closedBall (ψ v) δ₀) := hprop _ hcbW (isCompact_closedBall _ _)
  set C := (V ∩ ψ ⁻¹' closedBall (ψ v) δ₀) \ ball v σ with hCdef
  have hC : IsCompact C := hA.diff isOpen_ball
  have hCV : C ⊆ V := fun β hβ => hβ.1.1
  -- positive separation on C
  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ β ∈ C, m ≤ ‖ψ β - ψ v‖ := by
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨1, one_pos, fun β hβ => ?_⟩
      rw [hCe] at hβ
      exact hβ.elim
    · have hfc : ContinuousOn (fun β => ‖ψ β - ψ v‖) C :=
        ((hcont.mono hCV).sub continuousOn_const).norm
      obtain ⟨β₀, hβ₀C, hβ₀min⟩ := hC.exists_isMinOn hCne hfc
      refine ⟨‖ψ β₀ - ψ v‖, ?_, fun β hβ => (isMinOn_iff.mp hβ₀min) β hβ⟩
      rcases (norm_nonneg (ψ β₀ - ψ v)).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have h0 : ψ β₀ = ψ v := by
          have h' := heq.symm
          rwa [norm_eq_zero, sub_eq_zero] at h'
        have hβv := hinj (hCV hβ₀C) hv h0
        apply hβ₀C.2
        rw [hβv]
        exact mem_ball_self hσ
  refine ⟨min δ₀ m, lt_min hδ₀ hm, ?_⟩
  intro z hzN hzd
  have hzcb : z ∈ closedBall (ψ v) δ₀ := mem_closedBall.2 (hzd.trans_le (min_le_left _ _)).le
  have hzim : z ∈ ψ '' V := by
    rw [himg]
    exact ⟨hcbW hzcb, hzN⟩
  obtain ⟨β, hβV, rfl⟩ := hzim
  have hβA : β ∈ V ∩ ψ ⁻¹' closedBall (ψ v) δ₀ := ⟨hβV, hzcb⟩
  have hβσ : dist β v < σ := by
    by_contra hcon
    have hβC : β ∈ C := ⟨hβA, fun hb => hcon (mem_ball.1 hb)⟩
    have h1 := hmC β hβC
    rw [← dist_eq_norm] at h1
    have h2 : min δ₀ m ≤ dist (ψ β) (ψ v) := (min_le_right _ _).trans h1
    linarith
  refine ⟨β - v, ?_⟩
  have hest : ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hσball hβσ
  have hLh : ‖L (β - v)‖ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by
    calc ‖L (β - v)‖ = ‖(ψ β - ψ v) - (ψ β - ψ v - L (β - v))‖ := by congr 1; abel
      _ ≤ ‖ψ β - ψ v‖ + ‖ψ β - ψ v - L (β - v)‖ := norm_sub_le _ _
      _ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by gcongr
  have hh : ‖β - v‖ ≤ 2 * K * ‖ψ β - ψ v‖ := by
    have h2 : ‖β - v‖ ≤ K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by
      calc ‖β - v‖ ≤ K * ‖L (β - v)‖ := hcoer (β - v)
        _ ≤ K * (‖ψ β - ψ v‖ + η * ‖β - v‖) := by gcongr
        _ = K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by ring
    have h3 : (η * K) * ‖β - v‖ ≤ 1 / 2 * ‖β - v‖ := by gcongr
    linarith
  calc ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ β - ψ v‖) := by gcongr
    _ = (η * (2 * K)) * ‖ψ β - ψ v‖ := by ring
    _ ≤ ε * ‖ψ β - ψ v‖ := by gcongr
/-- **Simon Ch. 3, Definition 1.4 and Remark 1.5(1)**: an approximate tangent space of `M` at `x`
lies in every subspace `T` along which a set `N` carrying `Hⁿ`-almost all of `M` is flat at `x`
(for each `ε > 0` there is `ρ > 0` such that every `z ∈ N` with `|z − x| < ρ` has some `t ∈ T`
with `|z − x − t| ≤ ε|z − x|`).  If `q ∈ Q \ T`, put `δ = dist(q, T) > 0` and
`g = max(0, δ/2 − |· − q|) ∈ C_c(ℝᴾ)`; `∫_Q g dHⁿ > 0` because `spt(Hⁿ⌞Q) = Q`.  With
`ε = δ / (2(|q| + δ))` and `0 < r < ρ / (|q| + δ)`, flatness makes `g` vanish on `η_{x,r}(M ∩ N)`,
and `Hⁿ(η_{x,r}(M \ N)) = 0`; so `∫_{η_{x,r}(M)} g dHⁿ = 0` for all small `r`, contradicting
the defining limit. -/
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  -- `T` is closed, so `δ = dist(q, T) > 0`
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
  -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants: `ε (|q| + δ) = δ / 2`
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- `∫_{η_{x,r}(M)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    -- `η_{x,r}(M \ N) = r⁻¹ (M \ N − x)` is `Hⁿ`-null
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (M \ N)) := by
        rw [Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    -- flatness: `g` vanishes on `η_{x,r}(M ∩ N)`
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(M)`, evaluated on the open set `{g ≠ 0}`
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)

/-- **`TₓM ⊆ TₓN`** (Simon Ch. 3, 1.4 and Ch. 2, §4, (4.1)–(4.3); used in Ch. 4, 2.6–2.7).  Let
`N` be an embedded `C¹` `d`-dimensional submanifold, `Hⁿ(M \ N) = 0` and `x ∈ N`.  Then every
approximate tangent plane `Q` of `M` at `x` lies in `TₓN`.  Write `x = ψ(v)` for a chart `ψ` of
`N` and `A = Dψ(v)`: `N` is flat at `x` along `A(ℝᵈ)` (`atsm_chart_image_flat`), hence
`Q ⊆ A(ℝᵈ)` (`atsm_approxTangent_le_of_flat`), and `A(ℝᵈ) = TₓN`
(`chart_tangentSpace_eq_range_fderiv`). -/
theorem Submission.approxTangent_le_submanifold_tangentSpace : ∀ (P n d : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), IsEmbeddedSubmanifold 1 d N → x ∈ N → μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → (Q : Set (Euclid P)) ⊆ tangentSpace N x := by
  intro P n d N M x Q hN hxN hnull hQ
  -- a chart `ψ : V → W ∩ N` of `N` around `x`, and `v ∈ V` with `ψ v = x`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, himg, hprop, hDψ⟩ := hN x hxN
  obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := by
    rw [himg]
    exact ⟨hxW, hxN⟩
  -- `N` is flat at `ψ v` along `A(ℝᵈ)`, `A = Dψ(v)`
  have hflat : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z (ψ v) < ρ →
      ∃ t ∈ LinearMap.range (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P),
        ‖z - ψ v - t‖ ≤ ε * ‖z - ψ v‖ := by
    intro ε hε
    obtain ⟨ρ, hρ, hρN⟩ := Submission.atsm_chart_image_flat P d N W V ψ v hV hW
      (by exact_mod_cast hψ) hinj himg hprop (hDψ v hv) hv ε hε
    refine ⟨ρ, hρ, fun z hz hzρ => ?_⟩
    obtain ⟨h, hh⟩ := hρN z hz hzρ
    exact ⟨_, LinearMap.mem_range_self (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P) h, hh⟩
  -- hence `Q ⊆ A(ℝᵈ)`, and `A(ℝᵈ) = T_{ψ v}N`
  have hQA := Submission.atsm_approxTangent_le_of_flat P n N M (ψ v) Q _ hnull hflat hQ
  rw [Submission.chart_tangentSpace_eq_range_fderiv P d 1 N W V ψ v le_rfl hV hW hψ hinj himg
    hprop hDψ hv]
  intro w hw
  exact LinearMap.mem_range.1 (hQA hw)

/-- **Additivity of the pairing with a bounded field** (the identity
`∫ ⟨φ, ν_Y⟩ dHⁿ = ∫ ⟨φ, ν_Z + ν_X⟩ dHⁿ` in the competitor mass bound of Simon 7.2.4 (8)–(9)).
Write `ν_R = 1_M θ ξ` for `R = (M, θ, ξ)`.  If `ν_R = ν_{R₁} + ν_{R₂}` `Hⁿ`-a.e. and `F` is
`Hⁿ`-a.e. strongly measurable, vanishes off the compact `K ⊆ U` and `‖F‖ ≤ B`, then
`∫_M θ ⟨F, ξ⟩ dHⁿ = ∫_{M₁} θ₁ ⟨F, ξ₁⟩ dHⁿ + ∫_{M₂} θ₂ ⟨F, ξ₂⟩ dHⁿ`.  Each side is the integral
over `ℝᴾ` of `⟨F, ν⟩ = 1_M θ ⟨F, ξ⟩`, integrable by `dpf_pfc_imrep_pairing_integrable_abs_le`. -/
theorem Submission.dor_lmb_pc_cm_pairing_add_of_bounded : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact K → K ⊆ U → AEStronglyMeasurable F μHE[n] → (∀ x, x ∉ K → F x = 0) → (∀ x, ‖F x‖ ≤ B) → (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n] = ∫ x in R₁.carrier, (R₁.mult x : ℝ) * R₁.orient x (F x) ∂μHE[n] + ∫ x in R₂.carrier, (R₂.mult x : ℝ) * R₂.orient x (F x) ∂μHE[n] := by
  intro P n U K R₁ R₂ R F B hK hKU hF hF0 hFB hvd
  -- Steps 1–3: for each `R'`, `⟨F, ν_{R'}⟩` is `Hⁿ`-integrable with integral `∫_{M'} θ' ⟨F, ξ'⟩`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x))
        μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x) ∂μHE[n] =
        ∫ x in R'.carrier, (R'.mult x : ℝ) * R'.orient x (F x) ∂μHE[n] := by
    intro R'
    -- Step 2: `⟨F, ν_{R'}⟩ = 1_{M'} θ' ⟨F, ξ'⟩`
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x)) =
        R'.carrier.indicator (fun y => (R'.mult y : ℝ) * R'.orient y (F y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    -- Steps 1 and 3: integrability on `M'` from the pairing bound, then `integral_indicator`
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    exact ⟨(Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U K R' F B hK hKU hF.restrict
      hF0 hFB).1, rfl⟩
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  -- Steps 4–5: evaluate `ν_R = ν_{R₁} + ν_{R₂}` at `F` a.e. and integrate additively
  rw [← he, ← he₁, ← he₂, ← integral_add hi₁ hi₂]
  refine integral_congr_ae ?_
  filter_upwards [hvd] with x hx
  rw [hx, add_apply]
/-- **Pull-back field** (the integrand `⟨ω(f(x)), df_x# T⃗⟩` of Simon Ch. 6, 2.24(2)–(3), and the
estimate behind 2.29): if `f` is `C¹` on the open set `O ⊇ G`, `G` is open, `‖Df‖ ≤ Λ` on `G`, and
the continuous form `ω` has `‖ω‖ ≤ W`, then `φ = 1_G · ω(f) ∘ Df` is a.e. strongly measurable for
every measure and `‖φ‖ ≤ W Λⁿ`.  `Df` and `ω ∘ f` are continuous on `O` and `L ↦ (α ↦ α ∘ L)` is
continuous, so `ω(f) ∘ Df` is continuous on the open set `G`; on `G`, `‖α ∘ L‖ ≤ ‖α‖ ‖L‖ⁿ`, and
`φ = 0` off `G`. -/
theorem Submission.dor_lmb_pc_cm_pullback_field_bounded : ∀ (P n : ℕ) (G O : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) n) (Λ W : ℝ), IsOpen G → IsOpen O → G ⊆ O → ContDiffOn ℝ 1 f O → Continuous ω → 0 ≤ Λ → (∀ x ∈ G, ‖fderiv ℝ f x‖ ≤ Λ) → (∀ z, ‖ω z‖ ≤ W) → (∀ μ : Measure (Euclid P), AEStronglyMeasurable (G.indicator fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) μ) ∧ ∀ x, ‖G.indicator (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) x‖ ≤ W * Λ ^ n := by
  intro P n G O f ω Λ W hG hO hGO hf hω hΛ hDf hW
  -- Steps 1–3: `Df` and `ω ∘ f` are continuous on `O`, hence so is `ω(f) ∘ Df`
  have hcont : ContinuousOn
      (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) G := by
    have h1 : ContinuousOn (fun y => fderiv ℝ f y) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
    have h2 : ContinuousOn (fun y => ω (f y)) O := hω.comp_continuousOn hf.continuousOn
    have h3 : ContinuousOn (fun y => ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ f y) (ω (f y))) O :=
      (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn h1).clm_apply h2
    exact h3.mono hGO
  -- Step 5: `W ≥ 0`
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  refine ⟨fun μ => ?_, fun x => ?_⟩
  -- Step 4: continuity on the open (Borel) set `G` gives measurability of `1_G · ω(f) ∘ Df`
  · rw [aestronglyMeasurable_indicator_iff hG.measurableSet]
    exact hcont.aestronglyMeasurable hG.measurableSet
  -- Steps 6–7: `‖α ∘ L‖ ≤ ‖α‖ ‖L‖ⁿ` on `G`; the field vanishes off `G`
  · by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      calc ‖(ω (f x)).compContinuousLinearMap (fderiv ℝ f x)‖
          ≤ ‖ω (f x)‖ * ‖fderiv ℝ f x‖ ^ Fintype.card (Fin n) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ = ‖ω (f x)‖ * ‖fderiv ℝ f x‖ ^ n := by rw [Fintype.card_fin]
        _ ≤ W * Λ ^ n := mul_le_mul (hW _) (pow_le_pow_left₀ (norm_nonneg _) (hDf x hx) n)
            (pow_nonneg (norm_nonneg _) _) hW0
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg hW0 (pow_nonneg hΛ n)
/-- The integral form of the mass bound **Simon Ch. 6, 2.29**, `M_W(f_#T) ≤ (sup |Df|)ⁿ M(T)`: if
`|g| ≤ c 1_G` holds `Hⁿ⌞M`-a.e. with `G` measurable, then `ofReal(∫_M θ g dHⁿ) ≤ ofReal(c) μ_R(G)`,
where `μ_R = (Hⁿ⌞M).withDensity θ`.  Indeed `ofReal(∫ θg) ≤ ‖∫ θg‖ₑ ≤ ∫⁻ ‖θg‖ₑ`, and a.e.
`‖θg‖ₑ ≤ 1_G ofReal(c) θ` (on `G` since `|g| ≤ c`, off `G` since `g = 0`), whose lower integral
over `Hⁿ⌞M` is `ofReal(c) μ_R(G)`. -/
theorem Submission.dor_lmb_pc_cm_ofReal_integral_le_measure : ∀ (P n : ℕ) (U G : Set (Euclid P)) (R : IMRep U n) (g : Euclid P → ℝ) (c : ℝ), MeasurableSet G → (∀ᵐ x ∂(μHE[n].restrict R.carrier), |g x| ≤ G.indicator (fun _ => c) x) → ENNReal.ofReal (∫ x in R.carrier, (R.mult x : ℝ) * g x ∂μHE[n]) ≤ ENNReal.ofReal c * R.measure G := by
  intro P n U G R g c hG hg
  -- the weight `θ` is measurable into `[0, ∞]`, being measurable into `ℕ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  calc ENNReal.ofReal (∫ x in R.carrier, (R.mult x : ℝ) * g x ∂μHE[n])
      ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * g x ∂μHE[n]‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in R.carrier, ‖(R.mult x : ℝ) * g x‖ₑ ∂μHE[n] := enorm_integral_le_lintegral_enorm _
    -- `‖θg‖ₑ ≤ 1_G ofReal(c) θ` holds `Hⁿ⌞M`-a.e.
    _ ≤ ∫⁻ x in R.carrier, G.indicator (fun x => ENNReal.ofReal c * (R.mult x : ℝ≥0∞)) x
          ∂μHE[n] := by
        refine lintegral_mono_ae ?_
        filter_upwards [hg] with x hx
        by_cases hxG : x ∈ G
        · rw [Set.indicator_of_mem hxG] at hx ⊢
          rw [Real.enorm_eq_ofReal_abs, abs_mul, Nat.abs_cast]
          calc ENNReal.ofReal ((R.mult x : ℝ) * |g x|) ≤ ENNReal.ofReal ((R.mult x : ℝ) * c) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
            _ = ENNReal.ofReal c * (R.mult x : ℝ≥0∞) := by
                rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
        · rw [Set.indicator_of_notMem hxG] at hx ⊢
          have : g x = 0 := abs_nonpos_iff.mp hx
          simp [this]
    -- `∫⁻_G ofReal(c) θ d(Hⁿ⌞M) = ofReal(c) (Hⁿ⌞M).withDensity θ (G)`
    _ = ENNReal.ofReal c * R.measure G := by
        rw [lintegral_indicator hG, lintegral_const_mul _ hθ, IMRep.measure,
          withDensity_apply _ hG]
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]

/-- **Simon 6.1.8–1.10, 6.3.4–3.5** for a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of `Q` and a
linear map `L`: `ξ(α ∘ L) = ±α(Lτ₁, …, Lτₙ)`, hence (a) `|ξ(α ∘ L)| ≤ |α|_E ‖L‖ⁿ`, the value
being `0` if `Lτ` is linearly dependent and otherwise bounded by Cauchy–Binet and Hadamard,
`|α(Lτ)| ≤ |α|_E det(⟨Lτᵢ, Lτⱼ⟩)^{1/2} ≤ |α|_E ∏ᵢ |Lτᵢ|`; and (b) `ξ(α ∘ L) = ξ(α)` when `L`
fixes `Q` pointwise. -/
theorem Submission.dor_lmb_pc_unitOrientation_comp : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ (α.compContinuousLinearMap L)| ≤ covectorEuclideanNorm α * ‖L‖ ^ n) ∧ ((∀ v ∈ Q, L v = v) → ∀ α : Covector (Euclid P) n, ξ (α.compContinuousLinearMap L) = ξ α) := by
  intro P n ξ Q L hξ
  obtain ⟨τ, hτ, hspan, hsign⟩ := hξ
  -- `ξ(β) = ±β(τ)`, so `|ξ(β)| = |β(τ)|`
  have habs : ∀ β : Covector (Euclid P) n, |ξ β| = |β τ| := by
    intro β
    rcases hsign with h | h
    · rw [h β]
    · rw [h β, abs_neg]
  refine ⟨fun α => ?_, fun hL α => ?_⟩
  · -- (a): `ξ(α ∘ L) = ±α(v)` with `v = Lτ`
    rw [habs, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    set v : Fin n → Euclid P := L ∘ τ
    have hα := covectorEuclideanNorm_nonneg α
    -- `|vᵢ| = |Lτᵢ| ≤ ‖L‖`
    have hprod : ∏ i, ‖v i‖ ≤ ‖L‖ ^ n := by
      calc ∏ i, ‖v i‖ ≤ ∏ _i : Fin n, ‖L‖ :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => by
              calc ‖v i‖ = ‖L (τ i)‖ := rfl
                _ ≤ ‖L‖ * ‖τ i‖ := L.le_opNorm _
                _ = ‖L‖ := by rw [hτ.1 i, mul_one]
        _ = ‖L‖ ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases hli : LinearIndependent ℝ v
    · -- Cauchy–Binet and Hadamard: `|α(v)| ≤ |α|_E det(⟨vᵢ, vⱼ⟩)^{1/2} ≤ |α|_E ∏ |vᵢ|`
      obtain ⟨σ, -, -, hG, -, hA⟩ := Submission.dpf_exists_orthonormal_frame_det_gram P n v hli
      have h1 := (Submission.covectorEuclideanNorm_gram_bounds P n).1 α v
      rw [hG, Real.sqrt_sq_eq_abs] at h1
      calc |α v| ≤ covectorEuclideanNorm α *
            |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| := h1
        _ ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ := mul_le_mul_of_nonneg_left hA hα
        _ ≤ covectorEuclideanNorm α * ‖L‖ ^ n := mul_le_mul_of_nonneg_left hprod hα
    · -- a linearly dependent `v` gives `α(v) = 0`
      rw [show α v = 0 from α.toAlternatingMap.map_linearDependent v hli, abs_zero]
      exact mul_nonneg hα (pow_nonneg (norm_nonneg L) n)
  · -- (b): `L` fixes each `τᵢ ∈ span τ = Q`, so `α(Lτ) = α(τ)`
    have hLτ : L ∘ τ = τ := funext fun i => hL (τ i) (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
    rcases hsign with h | h
    · rw [h, h, ContinuousAlternatingMap.compContinuousLinearMap_apply, hLτ]
    · rw [h, h, ContinuousAlternatingMap.compContinuousLinearMap_apply, hLτ]

/-- **A map fixing `N` to first order fixes the orientation of a triple carried by `N`** (steps
3–4 of the projected comparison; Simon Ch. 3, §1 and Ch. 2, §4).  Let `R = (M, θ, ξ)` satisfy
`Hⁿ(M \ N) = 0` for an embedded `C¹` submanifold `N`, and let `f(x) = x` and `Df(x)v = v` for
`x ∈ N ∩ O` and `v ∈ TₓN`.  For `Hⁿ`-a.e. `x ∈ M`, `x ∈ N` and `ξ(x)` orients an approximate
tangent plane `Q` of `M` at `x` (`R.orients`), and `Q ⊆ TₓN`
(`approxTangent_le_submanifold_tangentSpace`).  If also `x ∈ O`, then `f(x) = x` and `Df(x)`
fixes `Q`, so `ξ(x)(α ∘ Df(x)) = ξ(x)(α)` (`dor_lmb_pc_unitOrientation_comp`, part (b)). -/
theorem Submission.dor_lmb_pc_imrep_orient_fixed_by_retraction : ∀ (P n d : ℕ) (U N O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 d N → MeasurableSet O → μHE[n] (R.carrier \ N) = 0 → (∀ x ∈ N ∩ O, f x = x) → (∀ x ∈ N ∩ O, ∀ v ∈ tangentSpace N x, fderiv ℝ f x v = v) → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), f x = x ∧ ∀ α : Covector (Euclid P) n, R.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = R.orient x α := by
  intro P n d U N O R f hN hO hnull hfix hDfix
  -- `Hⁿ⌞M`-a.e. point lies in `N`: `Hⁿ⌞M(ℝᴾ \ N) = Hⁿ(M \ N) = 0`
  have hMN : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ N := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    exact fun x hx => ⟨hx.2, hx.1⟩
  -- with `R.orients`, pass from `Hⁿ⌞M` to `Hⁿ⌞(M ∩ O)`
  have hMO : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), x ∈ N ∧ ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (hMN.and R.orients)
  filter_upwards [hMO, ae_restrict_mem (R.measurableSet_carrier.inter hO)]
    with x ⟨hxN, Q, hQ, hξ⟩ hx
  have hxNO : x ∈ N ∩ O := ⟨hxN, hx.2⟩
  -- the approximate tangent plane `Q` lies in `TₓN`, on which `Df(x)` is the identity
  have hQN := Submission.approxTangent_le_submanifold_tangentSpace P n d N R.carrier x Q hN hxN
    hnull hQ
  exact ⟨hfix x hxNO, (Submission.dor_lmb_pc_unitOrientation_comp P n (R.orient x) Q
    (fderiv ℝ f x) hξ).2 fun v hv => hDfix x hxNO v (hQN hv)⟩
/-- **Competitor mass bound** (Simon 7.2.4 (8)–(9), for the competitor `S = Z + f_#X`).  Let
`Y = τ(RY) = τ(RZ) + τ(RX)`, `f ∈ C¹(O)` with `‖Df‖ ≤ Λ` on `G ⊂⊂ U`, `f = id` and
`ξ_Z(α ∘ Df) = ξ_Z(α)` a.e. on `M_Z ∩ G`, and `M_X ⊆ G` a.e.  For an admissible `ω`
(`spt ω ⊆ G`, `|ω|_E ≤ 1`), `φ := 1_G · ω(f) ∘ Df` is bounded, measurable and vanishes off the
compact `Ḡ ⊆ U`; it represents both parts of `S(ω)`, so the vector density identity
`1_{M_Y} θ_Y ξ_Y = 1_{M_Z} θ_Z ξ_Z + 1_{M_X} θ_X ξ_X` gives `S(ω) = ∫_{M_Y} θ_Y ξ_Y(φ) dHⁿ`.
As `|ξ_Y(α ∘ Df)| ≤ |α|_E ‖Df‖ⁿ ≤ Λⁿ` on `G`, `S(ω) ≤ Λⁿ μ_{RY}(G)`; take the supremum over `ω`. -/
theorem Submission.dor_lmb_pc_competitor_massOn_le : ∀ (P n : ℕ) (U G O : Set (Euclid P)) (RZ RX RY : IMRep U n) (Y S : GeometricCurrentOn U n) (f : Euclid P → Euclid P) (Λ : ℝ), IsOpen U → IsOpen G → CompactlyContained G U → IsOpen O → G ⊆ O → ContDiffOn ℝ 1 f O → 0 ≤ Λ → (∀ x ∈ G, ‖fderiv ℝ f x‖ ≤ Λ) → RY.Represents Y → (∀ ω : TestFormOn U n, Y ω = RZ.action (ω : DifferentialForm (Euclid P) n) + RX.action (ω : DifferentialForm (Euclid P) n)) → (∀ᵐ x ∂(μHE[n].restrict (RZ.carrier ∩ G)), f x = x ∧ ∀ α : Covector (Euclid P) n, RZ.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = RZ.orient x α) → μHE[n] (RX.carrier \ G) = 0 → (∀ ω : TestFormOn U n, S ω = RZ.action (ω : DifferentialForm (Euclid P) n) + ∫ x in RX.carrier, (RX.mult x : ℝ) * RX.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → S.massOn G ≤ ENNReal.ofReal (Λ ^ n) * RY.measure G := by
  intro P n U G O RZ RX RY Y S f Λ hU hG hGU hO hGO hf hΛ hDf hY hYZX hZfix hXG hS
  obtain ⟨hKc, hKU⟩ := hGU
  -- Step 1: the vector densities satisfy `ν_Y = ν_Z + ν_X` `Hⁿ`-a.e.
  have hvd := Submission.dor_lmb_pc_cm_vector_density_add P n U RZ RX RY Y hU hY hYZX
  -- `M_G(S)` is the supremum of `S(ω)` over the admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, ⟨hωG, hω1⟩, rfl⟩
  show ENNReal.ofReal (S ω) ≤ ENNReal.ofReal (Λ ^ n) * RY.measure G
  -- `ω` is continuous and bounded by `W`
  obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 2: `φ = 1_G · ω(f) ∘ Df` is measurable, bounded by `W Λⁿ` and vanishes off `Ḡ`
  set φ : Euclid P → Covector (Euclid P) n := G.indicator fun y =>
    ((ω : DifferentialForm (Euclid P) n) (f y)).compContinuousLinearMap (fderiv ℝ f y) with hφ
  obtain ⟨hφm, hφB⟩ := Submission.dor_lmb_pc_cm_pullback_field_bounded P n G O f
    (ω : DifferentialForm (Euclid P) n) Λ W hG hO hGO hf hωc hΛ hDf hW
  have hφ0 : ∀ x, x ∉ closure G → φ x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (subset_closure h)) _
  -- Step 4: `τ(RZ)(ω) = ∫_{M_Z} θ_Z ξ_Z(φ) dHⁿ`, as `f` fixes `M_Z ∩ G` and `ω = φ = 0` off `G`
  have hZ : RZ.action (ω : DifferentialForm (Euclid P) n) =
      ∫ x in RZ.carrier, (RZ.mult x : ℝ) * RZ.orient x (φ x) ∂μHE[n] := by
    refine setIntegral_congr_ae RZ.measurableSet_carrier ?_
    filter_upwards [(ae_restrict_iff' (RZ.measurableSet_carrier.inter hG.measurableSet)).1 hZfix]
      with x hx hxZ
    by_cases hxG : x ∈ G
    · obtain ⟨hfx, hor⟩ := hx ⟨hxZ, hxG⟩
      rw [hφ, Set.indicator_of_mem hxG, hfx, hor]
    · rw [hφ, Set.indicator_of_notMem hxG,
        image_eq_zero_of_notMem_tsupport fun h => hxG (hωG h)]
  -- Step 5: the `X` part equals `∫_{M_X} θ_X ξ_X(φ) dHⁿ`, as `M_X ⊆ G` a.e.
  have hX : ∫ x in RX.carrier, (RX.mult x : ℝ) * RX.orient x
        (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x))
        ∂μHE[n] =
      ∫ x in RX.carrier, (RX.mult x : ℝ) * RX.orient x (φ x) ∂μHE[n] := by
    refine setIntegral_congr_ae RX.measurableSet_carrier ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hXG] with x hx hxX
    have hxG : x ∈ G := by_contra fun h => hx ⟨hxX, h⟩
    rw [hφ, Set.indicator_of_mem hxG]
  -- Steps 3 and 6: `S(ω) = ∫_{M_Y} θ_Y ξ_Y(φ) dHⁿ`, integrating `ν_Y = ν_Z + ν_X` against `φ`
  have hSY : S ω = ∫ x in RY.carrier, (RY.mult x : ℝ) * RY.orient x (φ x) ∂μHE[n] := by
    rw [hS ω, hZ, hX]
    exact (Submission.dor_lmb_pc_cm_pairing_add_of_bounded P n U (closure G) RZ RX RY φ
      (W * Λ ^ n) hKc hKU (hφm μHE[n]) hφ0 hφB hvd).symm
  -- Step 7: `|ξ_Y(φ)| ≤ |ω(f)|_E ‖Df‖ⁿ ≤ Λⁿ` on `G` and `ξ_Y(φ) = 0` off `G`, `Hⁿ⌞M_Y`-a.e.
  have hbound : ∀ᵐ x ∂(μHE[n].restrict RY.carrier),
      |RY.orient x (φ x)| ≤ G.indicator (fun _ => Λ ^ n) x := by
    filter_upwards [RY.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    by_cases hxG : x ∈ G
    · rw [hφ, Set.indicator_of_mem hxG, Set.indicator_of_mem hxG]
      calc |RY.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap
            (fderiv ℝ f x))|
          ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) (f x)) *
              ‖fderiv ℝ f x‖ ^ n :=
            (Submission.dor_lmb_pc_unitOrientation_comp P n (RY.orient x) Q (fderiv ℝ f x) hQ).1 _
        _ ≤ 1 * Λ ^ n := mul_le_mul (hω1 (f x)) (pow_le_pow_left₀ (norm_nonneg _) (hDf x hxG) n)
            (pow_nonneg (norm_nonneg _) n) zero_le_one
        _ = Λ ^ n := one_mul _
    · rw [hφ, Set.indicator_of_notMem hxG, Set.indicator_of_notMem hxG, map_zero, abs_zero]
  -- Step 8: `ofReal(S(ω)) ≤ ofReal(Λⁿ) μ_{RY}(G)`
  rw [hSY]
  exact Submission.dor_lmb_pc_cm_ofReal_integral_le_measure P n U G RY
    (fun x => RY.orient x (φ x)) (Λ ^ n) hG.measurableSet hbound

/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- **A unit covector attaining `1` on an orthonormal frame** (Simon (6.1.1); step 1(b) of the
mass formula, Remark 6.3.2(3)): every orthonormal `τ₁, …, τₙ` in `ℝᴾ` admits an `n`-covector `β`
with `|β|_E = 1` and `β(τ) = 1`.  Take the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors
`⟨τᵢ, ·⟩`, so `β(τ) = det 1 = 1`.  Extend `τ` to an orthonormal basis `f` of `ℝᴾ` with
`f ∘ ι = τ`, `ι = Fin.castLE`.  Then `β(f ∘ j) = sgn π` if `j = ι ∘ π` for a permutation `π`,
and `β(f ∘ j) = 0` otherwise (a zero column, or a repeated vector), so `Σ_j β(f ∘ j)² = n!`;
`regcomp_covector_sq_sum_orthonormalBasis` turns this into `n! = n! |β|_E²`. -/
theorem Submission.regcomp_exists_covector_eval_orthonormal_eq_one : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1 := by
  intro P n τ hτ
  classical
  -- Step 1: the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors `⟨τᵢ, ·⟩` (Simon (6.1.1))
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n, ∀ v : Fin n → Euclid P,
      β v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => (innerSL ℝ (τ i) : Euclid P →L[ℝ] ℝ).toLinearMap
    let g : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hg : ∀ v, g v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      intro v
      rw [← Matrix.det_transpose]
      show Matrix.det (Matrix.of fun a b => L (v a) b) = _
      congr 1
    have hcont : Continuous fun v : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i k
      exact Continuous.inner (f := fun _ => τ i) (g := fun v : Fin n → Euclid P => v k)
        continuous_const (continuous_apply k)
    refine ⟨{ g with cont := ?_ }, hg⟩
    have : (g : (Fin n → Euclid P) → ℝ) =
        fun v => Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := funext hg
    simpa [this] using hcont
  -- Step 2: by orthonormality `(⟨τᵢ, τ_k⟩) = 1`, so `β(τ) = det 1 = 1`
  have hβτ : β τ = 1 := by
    have hone : (Matrix.of fun i k => inner ℝ (τ i) (τ k) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i k
      rw [Matrix.of_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.mp hτ i k
    rw [hβ, hone, Matrix.det_one]
  -- Step 3: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 4: `β(f ∘ j)² = 1` if `j = ι ∘ π` for a permutation `π`, and `0` otherwise
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), β (fun k => f (Φ π k)) ^ 2 = 1 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : β (τ ∘ π) = Equiv.Perm.sign π • β τ := β.toAlternatingMap.map_perm τ π
    rw [h1, h2, hβτ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hzero : ∀ j : Fin n → Fin P, j ∉ Finset.univ.image Φ → β (fun k => f (j k)) ^ 2 = 0 := by
    intro j hj
    have hj' : ∀ π, Φ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
    rw [sq_eq_zero_iff]
    by_cases hr : ∀ k, j k ∈ range ι
    · -- `j = ι ∘ ρ` with `ρ` not a permutation, hence not injective: `f ∘ j` repeats a vector
      choose ρ hρ using hr
      have hρ' : ¬ Injective ρ := fun hinj =>
        hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
      refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
      exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
    · -- some `j k₀ ∉ range ι`: column `k₀` of `(⟨τᵢ, f (j k)⟩)` vanishes
      obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
      rw [hβ]
      refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
      rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
  have hsum : ∑ j : Fin n → Fin P, β (fun k => f (j k)) ^ 2 = n.factorial := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) fun j _ hj => hzero j hj,
      Finset.sum_image fun π _ π' _ h => hΦ h]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- Step 5: `n! = n! |β|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`, so `|β|_E = 1`
  have hsq := Submission.regcomp_covector_sq_sum_orthonormalBasis P n β f
  rw [hsum] at hsq
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine ⟨β, (pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β) two_ne_zero).mp ?_, hβτ⟩
  exact mul_left_cancel₀ hfac (by rw [← hsq, mul_one])
/-- **Simon Ch. 6, 1.7 and 1.15**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has dual Euclidean coefficient norm exactly one: `|ξ(α)| = |α(τ)| ≤ |α|_E` for every
`n`-covector `α`, and `ξ(±β₀) = 1` for a covector `β₀` with `|β₀|_E = 1` and `β₀(τ) = 1`
(`+β₀` for the sign `+`, `−β₀` for the sign `−`, using `|−β₀|_E = |β₀|_E`). -/
theorem Submission.regcomp_unit_orientation_pairing : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ β = 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  obtain ⟨β₀, hβ₀, hβ₀τ⟩ := Submission.regcomp_exists_covector_eval_orthonormal_eq_one P n τ hτ
  rcases hξ with h | h
  · -- `ξ(α) = α(τ)`: take `β = β₀`
    refine ⟨fun α => ?_, β₀, hβ₀.le, ?_⟩
    · rw [h α]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [h β₀, hβ₀τ]
  · -- `ξ(α) = −α(τ)`: `|ξ(α)| = |α(τ)|`, and take `β = −β₀`
    refine ⟨fun α => ?_, -β₀, ?_, ?_⟩
    · rw [h α, abs_neg]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [covectorEuclideanNorm_neg]
      exact hβ₀.le
    · rw [h (-β₀), ContinuousAlternatingMap.neg_apply, hβ₀τ, neg_neg]

/-- **Mass bound for an integer combination** (Simon Ch. 6, Remark 3.2(1)): if
`1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e. for integer multiplicity triples
`R = (M, θ, ξ)`, `R₁ = (M₁, θ₁, ξ₁)`, `R₂ = (M₂, θ₂, ξ₂)`, then `μ_R ≤ |p₁| μ_{R₁} + |p₂| μ_{R₂}`.
At a.e. `x ∈ M`, `regcomp_unit_orientation_pairing` gives `β` with `|β|_E ≤ 1` and
`ξ(x)(β) = 1`, and `|ξᵢ(x)(β)| ≤ |β|_E ≤ 1` at a.e. `x ∈ Mᵢ`; evaluating the identity at `β`
gives `1_M θ ≤ |p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂` a.e.  Since `μ_{R'}` has density `1_{M'} θ'` with
respect to `Hⁿ`, this bound integrates to the claim. -/
theorem Submission.dor_lmb_ic_measure_le_of_weighted_orient_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → R.measure ≤ (p₁.natAbs : ℝ≥0∞) • R₁.measure + (p₂.natAbs : ℝ≥0∞) • R₂.measure := by
  intro P n U R₁ R₂ R p₁ p₂ h
  -- Step 1: `Hⁿ`-a.e., `x ∈ M'` implies that `ξ'(x)` is a unit orientation
  have hor : ∀ R' : IMRep U n, ∀ᵐ x ∂μHE[n], x ∈ R'.carrier →
      ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R'.orient x) Q := by
    intro R'
    filter_upwards [(ae_restrict_iff' R'.measurableSet_carrier).mp R'.orients] with x hx hxM
    obtain ⟨Q, -, hQ⟩ := hx hxM
    exact ⟨Q, hQ⟩
  -- Step 2: at such `x`, `|(1_{M'} θ' ξ')(x)(β)| ≤ 1_{M'} θ'(x)` whenever `|β|_E ≤ 1`
  have hone : ∀ (R' : IMRep U n) (x : Euclid P),
      (x ∈ R'.carrier → ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R'.orient x) Q) →
      ∀ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 →
        |R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x β| ≤
          ((R'.carrier.indicator R'.mult x : ℕ) : ℝ) := by
    intro R' x hx β hβ
    by_cases hxM : x ∈ R'.carrier
    · obtain ⟨Q, hQ⟩ := hx hxM
      have hle :=
        ((Submission.regcomp_unit_orientation_pairing P n (R'.orient x) Q hQ).1 β).trans hβ
      rw [Set.indicator_of_mem hxM, Set.indicator_of_mem hxM, smul_apply, smul_eq_mul, abs_mul,
        Nat.abs_cast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hle
    · rw [Set.indicator_of_notMem hxM, Set.indicator_of_notMem hxM]
      simp
  -- Step 3: `μ_{R'}` has the measurable density `1_{M'} θ'` with respect to `Hⁿ`
  have hM : ∀ R' : IMRep U n,
      R'.measure = μHE[n].withDensity (R'.carrier.indicator fun x => (R'.mult x : ℝ≥0∞)) := by
    intro R'
    rw [IMRep.measure, withDensity_indicator R'.measurableSet_carrier]
  have hmeas : ∀ R' : IMRep U n, Measurable (R'.carrier.indicator fun x => (R'.mult x : ℝ≥0∞)) :=
    fun R' => (measurable_from_nat.comp R'.measurable_mult).indicator R'.measurableSet_carrier
  have hind : ∀ (R' : IMRep U n) (x : Euclid P), R'.carrier.indicator
      (fun y => (R'.mult y : ℝ≥0∞)) x = ((R'.carrier.indicator R'.mult x : ℕ) : ℝ≥0∞) := by
    intro R' x
    by_cases hxM : x ∈ R'.carrier
    · rw [Set.indicator_of_mem hxM, Set.indicator_of_mem hxM]
    · rw [Set.indicator_of_notMem hxM, Set.indicator_of_notMem hxM, Nat.cast_zero]
  -- Step 4: `|p₁| μ_{R₁} + |p₂| μ_{R₂}` has density `|p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂`, so it
  -- suffices to compare the densities `Hⁿ`-a.e.
  rw [hM R, hM R₁, hM R₂, ← withDensity_smul _ (hmeas R₁), ← withDensity_smul _ (hmeas R₂),
    ← withDensity_add_left ((hmeas R₁).const_smul _)]
  refine withDensity_mono ?_
  -- Step 5: `1_M θ ≤ |p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂` wherever the identity and Step 1 hold
  filter_upwards [h, hor R, hor R₁, hor R₂] with x hx h0 h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hind]
  by_cases hxM : x ∈ R.carrier
  swap
  · rw [Set.indicator_of_notMem hxM, Nat.cast_zero]
    exact zero_le
  -- evaluate the identity at a `β` with `|β|_E ≤ 1` and `ξ(x)(β) = 1`
  obtain ⟨Q, hQ⟩ := h0 hxM
  obtain ⟨-, β, hβ, hξβ⟩ := Submission.regcomp_unit_orientation_pairing P n (R.orient x) Q hQ
  have hev := congrArg (fun F : MultiVector P n => F β) hx
  simp only [Set.indicator_of_mem hxM, add_apply, smul_apply, smul_eq_mul, hξβ, mul_one] at hev
  have hreal : (R.mult x : ℝ) ≤ (p₁.natAbs : ℝ) * ((R₁.carrier.indicator R₁.mult x : ℕ) : ℝ) +
      (p₂.natAbs : ℝ) * ((R₂.carrier.indicator R₂.mult x : ℕ) : ℝ) := by
    rw [hev, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    calc (p₁ : ℝ) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x β +
          (p₂ : ℝ) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x β
        ≤ |(p₁ : ℝ)| * |R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x β| +
          |(p₂ : ℝ)| * |R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x β| := by
          rw [← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ _ := by
          gcongr
          · exact hone R₁ x h1 β hβ
          · exact hone R₂ x h2 β hβ
  -- a real inequality between natural numbers
  have hnat : R.mult x ≤ p₁.natAbs * R₁.carrier.indicator R₁.mult x +
      p₂.natAbs * R₂.carrier.indicator R₂.mult x := by
    exact_mod_cast hreal
  rw [Set.indicator_of_mem hxM]
  exact_mod_cast hnat

/-- Locality of approximate tangent spaces (Simon 3.1.5(2), from the proof of 3.1.6 "⇒"): if
`A ⊆ B` are Borel, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B \ A) ∩ B̄_ρ(x))/ρⁿ → 0` as `ρ ↓ 0`, then
`B` and `A` have the same approximate tangent spaces at `x`.  For `f ∈ C_c(ℝᴾ)` with `|f| ≤ C`
and `f = 0` off `B̄_R(0)`, and `0 < r < r₀/R`, the integrals of `f` over `η_{x,r}(B)` and
`η_{x,r}(A)` differ by at most `C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))`,
which tends to `0` as `r ↓ 0`. -/
theorem Submission.regcomp_atl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n B A x fun f => ?_
  -- `‖f‖ ≤ C` everywhere, and `f = 0` off `B̄_R(0)` with `R > 0`
  obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₁, hR₁⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₁ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₁ 1)
  have hf0 : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (closedBall_subset_closedBall (le_max_left R₁ 1) (hR₁ (subset_tsupport f hne)))
  -- the bound `C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))` tends to `0` as `r ↓ 0`
  have hlim : Tendsto (fun r : ℝ => C * ((ENNReal.ofReal r)⁻¹ ^ n *
      μHE[n] ((B \ A) ∩ closedBall x (r * R))).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ)) R hR hdens)
    rw [ENNReal.toReal_zero] at h
    have h' := h.const_mul C
    rw [mul_zero] at h'
    exact h'
  refine squeeze_zero_norm' ?_ hlim
  -- for `0 < r < r₀ / R` the fixed-scale comparison applies, and the scaling identity rewrites
  -- its bound
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
  have hrR : r * R ≤ r₀ := ((lt_div_iff₀ hR).1 hr.2).le
  have hBfin : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ := by
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R B hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr.1).ne'))
      (ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hrR))))
  have key := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n A B x r R C f
    (map_continuous f) hA hB hAB hr.1 hBfin hC hf0
  rwa [Submission.regcomp_atl_blowUp_measure_scaling P n x r R (B \ A) hr.1] at key

/-- **Locality of approximate tangent spaces** (Simon Ch. 3, Remark 1.5(2); proof of 3.1.6 "⇒",
chapter-03.txt lines 113–143).  If `U ⊆ ℝᴾ` is open and `A ⊆ B ⊆ U` are Borel with
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same
approximate tangent spaces at `x`.  `D = B \ A` is Borel with `Hⁿ(D ∩ K) < ∞` for compact `K ⊆ U`,
so by the upper density theorem `Hⁿ(D ∩ B̄_ρ(x))/ρⁿ → 0` as `ρ ↓ 0` for `Hⁿ`-a.e. `x ∈ U ∖ D`,
hence for `Hⁿ⌞A`-a.e. `x`.  At such `x ∈ A ⊆ U`, a closed ball `B̄_{r₀}(x) ⊆ U` is compact, so
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and the blow-ups of `B` and `A` at `x` have asymptotically equal
integrals. -/
theorem Submission.dor_lmb_approx_tangent_locality : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–3: `D = B \ A` has finite measure on compact subsets of `U`, so its `n`-density
  -- vanishes at `Hⁿ`-a.e. point of `U ∖ D`
  have hdens := Submission.regcomp_atl_local_density_zero P n U (B \ A) hU (hB.diff hA)
    fun K hK hKU => ne_top_of_le_ne_top (hfin K hK hKU)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 7: `Hⁿ⌞A`-a.e. `x` lies in `A`, hence in `U` and outside `D`
  filter_upwards [ae_restrict_of_ae hdens, ae_restrict_mem hA] with x hx hxA
  have hxU : x ∈ U := hBU (hAB hxA)
  -- Step 4: a closed ball `B̄_{r₀}(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Steps 5–6: comparison of the blow-up integrals of `B` and `A` at `x`
  exact Submission.regcomp_atl_tangent_iff_of_density_zero P n A B x (ε / 2) hA hB hAB
    (half_pos hε) (hfin _ (isCompact_closedBall x (ε / 2)) hsub) (hx hxU fun h => h.2 hxA)

/-- **Simon Ch. 6, Remark 3.2(1)**, with a mass bound (chapter-06.txt lines 755–757): if
`T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)` in the open set `U` and `S = p₁T₁ + p₂T₂` with
`p₁, p₂ ∈ ℤ`, then `S = τ(M, θ, ξ)` for an integer multiplicity triple `R = (M, θ, ξ)` in `U` with
`μ_R ≤ |p₁| μ_{R₁} + |p₂| μ_{R₂}`.  Tangent locality and the sign of the orientations on
`M₁ ∩ M₂` give `R` with `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Integrating this
identity against `ω ∈ 𝒟ⁿ(U)` gives `τ(R)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.  Evaluating it at a
covector norming `ξ` gives `θ 1_M ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}` a.e., hence the mass bound. -/
theorem Submission.dor_lmb_int_combination_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → R₁.Represents T₁ → R₂.Represents T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → ∃ R : IMRep U n, R.Represents S ∧ R.measure ≤ (p₁.natAbs : ℝ≥0∞) • R₁.measure + (p₂.natAbs : ℝ≥0∞) • R₂.measure := by
  intro P n U T₁ T₂ S R₁ R₂ p₁ p₂ hU h₁ h₂ hS
  -- Steps 2–6: an IMRep `R = (M, θ, ξ)` in `U` with
  -- `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e. (the identity (†) of step 5)
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Steps 5 and 8: (†) bounds `θ 1_M` a.e., so `μ_R ≤ |p₁| μ_{R₁} + |p₂| μ_{R₂}`
  refine ⟨R, fun ω => ?_,
    Submission.dor_lmb_ic_measure_le_of_weighted_orient_eq P n U R₁ R₂ R p₁ p₂ hR⟩
  -- Step 7: integrating (†) against `ω` gives `τ(R)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`
  rw [hS ω, h₁ ω, h₂ ω, Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Comparison with the projected competitor** (Simon 7.2.4, proof of (8)–(9),
chapter-07.txt lines 222–246, with the competitor projected into `N` by `π`; README erratum 5,
`Nᵢ = N`).  Assume (C1): `M_W(T) = μ_R(W)` for open `W` and `spt T = U ∩ spt μ_R` whenever `R`
represents `T`.  Put `F = B̄_t(y)`, `G = B_{3ρ}(y)`, `Λ = 1 + 3cρ`; if `t < 0` then `F = ∅`.
1. `π(y) = y`, and the mean value inequality with `‖Dπ‖ ≤ 1 + ct` on `F` gives
   `|π(x) − y| ≤ (1 + ct)t < 3ρ` on `F` (as `4cρ ≤ 1`), so `π(F) ⊆ (U ∩ N) ∩ G`.
2. By (C1), `X = 0` off `F` gives `Hⁿ(M_X \ F) = 0`, and `spt Z ⊆ N` gives `Hⁿ(M_Z \ N) = 0`.
3. `π(x) = x` and `ξ_Z(x)(α ∘ Dπ(x)) = ξ_Z(x)(α)` for `Hⁿ`-a.e. `x ∈ M_Z ∩ G` (`fix_orient`).
4. `Q_π = π_#X` is an integer multiplicity cycle with compact support in `π(F)` (`pf_current`,
   `pf_integer`, `pf_boundary`).
5. `Z' = Z + Q_π` is integer multiplicity (`int_combination`), `∂Z' = ∂Z` and
   `spt(Z' − Z) = spt Q_π`, so minimality of `Z` in `U ∩ N` gives `M_G(Z) ≤ M_G(Z')`.
6. `M_G(Z') ≤ Λⁿ μ_Y(G)` (`competitor_mass`), hence `μ_Z(G) ≤ Λⁿ μ_Y(G)` by (C1).
7. `Y = Z` on the open set `G \ F`, so `μ_Y(G \ F) = μ_Z(G \ F) < ∞`.  Splitting
   `G = F ∪ (G \ F)` and cancelling `μ_Z(G \ F)` gives
   `μ_Z(F) ≤ Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G \ F) ≤ Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G)`. -/
theorem Submission.dor_lmb_projected_competitor_comparison : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P d n : ℕ) (U N : Set (Euclid P)) (Z X Y : GeometricCurrentOn U n) (RZ RY : IMRep U n) (proj : Euclid P → Euclid P) (y : Euclid P) (r c ρ t : ℝ), IsOpen U → 0 < n → IsEmbeddedSubmanifold 2 d N → IsMinimizingIn Z (U ∩ N) → Z.support ⊆ N → BoundaryVanishes Z → RZ.Represents Z → IsIntegerMultiplicity X → BoundaryVanishes X → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (closedBall y t) → X ω = 0) → (∀ ω : TestFormOn U n, Y ω = Z ω + X ω) → RY.Represents Y → y ∈ N → 0 ≤ c → 0 < ρ → 3 * ρ < r → 4 * c * ρ ≤ 1 → t < 2 * ρ → closedBall y (3 * ρ) ⊆ U → ContDiffOn ℝ 1 proj (ball y r) → MapsTo proj (ball y r) N → (∀ x ∈ N ∩ ball y r, proj x = x) → (∀ x ∈ N ∩ ball y r, ∀ v ∈ tangentSpace N x, fderiv ℝ proj x v = v) → (∀ x ∈ ball y r, ‖fderiv ℝ proj x‖ ≤ 1 + c * dist x y) → RZ.measure (closedBall y t) ≤ ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) + ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ)) := by
  intro hC1 P d n U N Z X Y RZ RY proj y r c ρ t hU hn hN hZmin hZsupp _hZbd hRZ hXim hXbd hXvan
    hY hRY hyN hc hρ hρr hcρ ht hGU hproj hmaps hfix hdfix hnorm
  -- If `t < 0` then `F = B̄_t(y) = ∅`
  rcases lt_or_ge t 0 with ht0 | ht0
  · rw [closedBall_eq_empty.2 ht0, measure_empty]
    exact zero_le
  obtain ⟨RX, hRX⟩ := hXim
  -- `F ⊆ G ⊆ B_r(y)`, `G ⊆ U`, and `G ⊂⊂ U`
  have hFG : closedBall y t ⊆ ball y (3 * ρ) := closedBall_subset_ball (by linarith)
  have hGr : ball y (3 * ρ) ⊆ ball y r := ball_subset_ball hρr.le
  have hFr : closedBall y t ⊆ ball y r := hFG.trans hGr
  have hGU' : ball y (3 * ρ) ⊆ U := ball_subset_closedBall.trans hGU
  have hFU : closedBall y t ⊆ U := hFG.trans hGU'
  have hclG : closure (ball y (3 * ρ)) = closedBall y (3 * ρ) :=
    closure_ball y (by linarith : (0 : ℝ) < 3 * ρ).ne'
  have hGcc : CompactlyContained (ball y (3 * ρ)) U := by
    refine ⟨?_, ?_⟩ <;> rw [hclG]
    · exact isCompact_closedBall y _
    · exact hGU
  -- Step 1: `π(y) = y` and `|π(x) − y| ≤ (1 + ct)t < 3ρ` on `F`, so `π(F) ⊆ (U ∩ N) ∩ G`
  have hdiff : ∀ z ∈ ball y r, DifferentiableAt ℝ proj z := fun z hz =>
    (hproj.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hz)
  have hprojy : proj y = y := hfix y ⟨hyN, mem_ball_self (by linarith)⟩
  have hπF : ∀ x ∈ closedBall y t, proj x ∈ ball y (3 * ρ) := by
    intro x hx
    have hbound : ∀ z ∈ closedBall y t, ‖fderiv ℝ proj z‖ ≤ 1 + c * t := fun z hz =>
      (hnorm z (hFr hz)).trans
        (by nlinarith [mul_le_mul_of_nonneg_left (mem_closedBall.1 hz) hc])
    have hmvt := (convex_closedBall y t).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hdiff z (hFr hz)) hbound (mem_closedBall_self ht0) hx
    have hxy : ‖x - y‖ ≤ t := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hx
    rw [mem_ball, dist_eq_norm]
    calc ‖proj x - y‖ = ‖proj x - proj y‖ := by rw [hprojy]
      _ ≤ (1 + c * t) * ‖x - y‖ := hmvt
      _ ≤ (1 + c * t) * t := mul_le_mul_of_nonneg_left hxy (by nlinarith)
      _ < 3 * ρ := by
        nlinarith [mul_nonneg (mul_nonneg hc ht0) (by linarith : (0 : ℝ) ≤ 2 * ρ - t),
          mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 4 * c * ρ)]
  have hπFG : proj '' closedBall y t ⊆ ball y (3 * ρ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hπF x hx
  have hπFU : proj '' closedBall y t ⊆ U := hπFG.trans hGU'
  have hπFN : proj '' closedBall y t ⊆ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps (hFr hx)
  -- `Hⁿ(M ∩ S) ≤ μ_R(S)` for Borel `S`, since `θ ≥ 1` on `M`
  have hcarrier_le : ∀ (R : IMRep U n) (S : Set (Euclid P)), MeasurableSet S →
      μHE[n] (R.carrier ∩ S) ≤ R.measure S := by
    intro R S hS
    rw [IMRep.measure, withDensity_apply _ hS, Measure.restrict_restrict hS]
    calc μHE[n] (R.carrier ∩ S) = ∫⁻ _ in S ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_one, inter_comm]
      _ ≤ ∫⁻ x in S ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' (hS.inter R.measurableSet_carrier) fun x hx =>
            Nat.one_le_cast.2 (R.mult_pos x hx.2)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`
  have hfin : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro R K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Step 2(a): by (C1), `μ_X(U \ F) = M_{U \ F}(X) = 0`, so `Hⁿ(M_X \ F) = 0`
  have hXF : μHE[n] (RX.carrier \ closedBall y t) = 0 := by
    have hopen : IsOpen (U \ closedBall y t) := hU.sdiff isClosed_closedBall
    have hmass : X.massOn (U \ closedBall y t) = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (X ω) ≤ 0
      rw [hXvan ω (Disjoint.mono_left hω.1 Set.disjoint_sdiff_left), ENNReal.ofReal_zero]
    have hmeas : RX.measure (U \ closedBall y t) = 0 := by
      rw [← (hC1 P n U X RX hU hRX).1 _ hopen, hmass]
    have hsub : RX.carrier \ closedBall y t ⊆ RX.carrier ∩ (U \ closedBall y t) :=
      fun x hx => ⟨hx.1, RX.carrier_subset hx.1, hx.2⟩
    refine measure_mono_null hsub (le_antisymm ?_ zero_le)
    exact (hcarrier_le RX _ hopen.measurableSet).trans hmeas.le
  -- Step 2(b): by (C1), `U ∩ spt μ_Z = spt Z ⊆ N`, so `Hⁿ(M_Z \ N) = 0`
  have hZN : μHE[n] (RZ.carrier \ N) = 0 := by
    have hsupp := (hC1 P n U Z RZ hU hRZ).2
    have hsub : RZ.carrier \ N ⊆ RZ.carrier ∩ RZ.measure.supportᶜ := by
      intro x hx
      refine ⟨hx.1, fun hxs => hx.2 (hZsupp ?_)⟩
      rw [hsupp]
      exact ⟨RZ.carrier_subset hx.1, hxs⟩
    refine measure_mono_null hsub (le_antisymm ?_ zero_le)
    calc μHE[n] (RZ.carrier ∩ RZ.measure.supportᶜ) ≤ RZ.measure RZ.measure.supportᶜ :=
          hcarrier_le RZ _ Measure.isClosed_support.isOpen_compl.measurableSet
      _ = 0 := Measure.measure_compl_support
  -- Step 3 (`fix_orient`): `π` fixes `Z` on `G`
  have hN1 : IsEmbeddedSubmanifold 1 d N := by
    intro z hz
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, hprop, hrank⟩ := hN z hz
    exact ⟨V, W, ψ, hV, hW, hzW, hψ.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by norm_num)),
      hinj, himg, hprop, hrank⟩
  have hfixZ := Submission.dor_lmb_pc_imrep_orient_fixed_by_retraction P n d U N (ball y (3 * ρ))
    RZ proj hN1 isOpen_ball.measurableSet hZN (fun x hx => hfix x ⟨hx.1, hGr hx.2⟩)
    (fun x hx v hv => hdfix x ⟨hx.1, hGr hx.2⟩ v hv)
  -- Step 4 (`pf_current`, `pf_integer`, `pf_boundary`): the projected cycle `Q_π = π_#X`
  obtain ⟨Q, hQ, hQcpt, hQsupp⟩ := Submission.dor_lmb_pc_pushforward_current_exists P n U
    (closedBall y t) (ball y r) RX proj hU (isCompact_closedBall y t) hFU hXF isOpen_ball hFr hproj
    hπFU
  have hQim : IsIntegerMultiplicity Q :=
    Submission.dor_lmb_pc_pushforward_isIntegerMultiplicity
      Submission.dor_lmb_approx_tangent_locality P n U (closedBall y t) (ball y r) RX proj Q hU hn
      (isCompact_closedBall y t) hFU hXF isOpen_ball hFr hproj hπFU hQ
  have hQbd : BoundaryVanishes Q :=
    Submission.dor_lmb_pc_pushforward_boundaryVanishes P n U (closedBall y t) (ball y r) RX proj X Q
      hU (isCompact_closedBall y t) hFU hXF isOpen_ball hFr hproj hRX hXbd hQ
  -- Step 5: the competitor `Z' = Z + Q_π`
  obtain ⟨Z', hZ'⟩ : ∃ Z' : GeometricCurrentOn U n, ∀ ω, Z' ω = Z ω + Q ω :=
    ⟨{ toCurrent := Z.toCurrent + Q.toCurrent
       continuous' := fun ωs h => by
         simpa using (Z.continuous' ωs h).add (Q.continuous' ωs h) }, fun ω => rfl⟩
  -- (a) `Z'` is integer multiplicity (`int_combination` with `p₁ = p₂ = 1`)
  obtain ⟨RQ, hRQ⟩ := hQim
  obtain ⟨RZ', hRZ', -⟩ := Submission.dor_lmb_int_combination_imrep P n U Z Q Z' RZ RQ 1 1 hU hRZ
    hRQ fun ω => by rw [hZ' ω]; push_cast; ring
  -- (b) `∂Z' = ∂Z`, as `∂Q_π = 0`
  have hSB : SameBoundary Z' Z := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hQ0 : Q.boundary = 0 := hQbd
    show Z'.boundary = Z.boundary
    ext η
    have h0 : Q (exteriorDerivativeTestOn U m η) = 0 := by
      rw [← GeometricCurrentOn.boundary_apply, hQ0, GeometricCurrentOn.zero_apply]
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hZ', h0, add_zero]
  -- (c) `Z' − Z = Q_π`, with compact support in `π(F) ⊆ (U ∩ N) ∩ G`
  have hZ'Z : Z' - Z = Q := by
    ext ω
    show Z' ω - Z ω = Q ω
    rw [hZ' ω]
    ring
  -- (d) minimality of `Z` in `U ∩ N`, tested on `W = G`
  have hmin : Z.massOn (ball y (3 * ρ)) ≤ Z'.massOn (ball y (3 * ρ)) := by
    refine hZmin.2 (ball y (3 * ρ)) Z' isOpen_ball hGcc ⟨RZ', hRZ'⟩ hSB ?_ ?_
    · rw [hZ'Z]
      exact hQcpt
    · rw [hZ'Z]
      intro z hz
      have hz' := hQsupp hz
      exact ⟨⟨hπFU hz', hπFN hz'⟩, hπFG hz'⟩
  -- Step 6 (`competitor_mass`): `M_G(Z') ≤ Λⁿ μ_Y(G)`, so `μ_Z(G) ≤ Λⁿ μ_Y(G)` by (C1)
  have hmass := Submission.dor_lmb_pc_competitor_massOn_le P n U (ball y (3 * ρ)) (ball y r) RZ RX
    RY Y Z' proj (1 + 3 * c * ρ) hU isOpen_ball hGcc isOpen_ball hGr hproj
    (by nlinarith [mul_nonneg hc hρ.le])
    (fun x hx => (hnorm x (hGr hx)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (mem_ball.1 hx).le hc]))
    hRY (fun ω => by rw [hY ω, hRZ ω, hRX ω]) hfixZ
    (measure_mono_null (sdiff_subset_sdiff_right hFG) hXF) (fun ω => by rw [hZ' ω, hRZ ω, hQ ω])
  have hmain : RZ.measure (ball y (3 * ρ)) ≤
      ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (ball y (3 * ρ)) := by
    rw [← (hC1 P n U Z RZ hU hRZ).1 (ball y (3 * ρ)) isOpen_ball]
    exact hmin.trans hmass
  -- Step 7: `Y = Z` on forms supported in the open set `G \ F`, so `μ_Y(G \ F) = μ_Z(G \ F)`
  have hGFopen : IsOpen (ball y (3 * ρ) \ closedBall y t) := isOpen_ball.sdiff isClosed_closedBall
  have hYZ : RY.measure (ball y (3 * ρ) \ closedBall y t) =
      RZ.measure (ball y (3 * ρ) \ closedBall y t) := by
    rw [← (hC1 P n U Y RY hU hRY).1 _ hGFopen, ← (hC1 P n U Z RZ hU hRZ).1 _ hGFopen]
    unfold GeometricCurrentOn.massOn
    congr 1
    refine Set.image_congr fun ω hω => ?_
    show ENNReal.ofReal (Y ω) = ENNReal.ofReal (Z ω)
    rw [hY ω, hXvan ω (Disjoint.mono_left hω.1 Set.disjoint_sdiff_left), add_zero]
  -- split `G = F ∪ (G \ F)` and cancel the finite `μ_Z(G \ F)`
  have hFm : MeasurableSet (closedBall y t) := measurableSet_closedBall
  have hZsplit := measure_inter_add_sdiff (μ := RZ.measure) (ball y (3 * ρ)) hFm
  have hYsplit := measure_inter_add_sdiff (μ := RY.measure) (ball y (3 * ρ)) hFm
  rw [inter_eq_right.2 hFG] at hZsplit hYsplit
  have hbfin : RZ.measure (ball y (3 * ρ) \ closedBall y t) ≠ ∞ :=
    ne_top_of_le_ne_top (hfin RZ _ (isCompact_closedBall y (3 * ρ)) hGU)
      (measure_mono (sdiff_subset.trans ball_subset_closedBall))
  have hL : ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) =
      ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) + 1 := by
    have h1 : (1 : ℝ) ≤ (1 + 3 * c * ρ) ^ n := one_le_pow₀ (by nlinarith [mul_nonneg hc hρ.le])
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.2 h1) zero_le_one, sub_add_cancel]
  have hLb : ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RZ.measure (ball y (3 * ρ) \ closedBall y t) =
      ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ) \ closedBall y t) +
        RZ.measure (ball y (3 * ρ) \ closedBall y t) := by
    rw [hL, add_mul, one_mul]
  have key : RZ.measure (closedBall y t) + RZ.measure (ball y (3 * ρ) \ closedBall y t) ≤
      (ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) +
        ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ) \ closedBall y t)) +
      RZ.measure (ball y (3 * ρ) \ closedBall y t) := by
    calc RZ.measure (closedBall y t) + RZ.measure (ball y (3 * ρ) \ closedBall y t)
        = RZ.measure (ball y (3 * ρ)) := hZsplit
      _ ≤ ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (ball y (3 * ρ)) := hmain
      _ = ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) +
          ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RZ.measure (ball y (3 * ρ) \ closedBall y t) := by
        rw [← hYsplit, hYZ, mul_add]
      _ = _ := by rw [hLb, add_assoc]
  calc RZ.measure (closedBall y t)
      ≤ ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) +
        ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ) \ closedBall y t) :=
        ENNReal.le_of_add_le_add_right hbfin key
    _ ≤ _ := by
        gcongr
        exact sdiff_subset

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
