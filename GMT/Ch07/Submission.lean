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

/-- **`∫_Q g dHⁿ > 0` for a nonnegative `C_c` function `g` with `g(w) > 0` at a point `w` of an
`n`-plane `Q`** (step 4 of the proof that approximate tangent planes of a submanifold lie in its
tangent spaces; Simon Ch. 3, 1.4).  `Hⁿ⌞Q` is regular with support `Q` (SimonGMT Ch. 3), so `g` is
`Hⁿ⌞Q`-integrable and the open set `{g ≠ 0} ∋ w` has positive `Hⁿ⌞Q`-measure. -/
theorem Submission.dsmc_att_setIntegral_submodule_pos : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (g : Euclid P → ℝ) (w : Euclid P), Module.finrank ℝ Q = n → Continuous g → HasCompactSupport g → (∀ y, 0 ≤ g y) → w ∈ Q → 0 < g w → 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
  intro P n Q g w hQ hg hgc hg0 hw hgw
  -- `Hⁿ⌞Q` is regular, hence finite on compact sets, so the `C_c` function `g` is integrable.
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ
  rw [integral_pos_iff_support_of_nonneg hg0 (hg.integrable_of_hasCompactSupport hgc)]
  -- `w ∈ Q = spt(Hⁿ⌞Q)` and `{g ≠ 0}` is an open neighbourhood of `w`.
  have hwμ : w ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
    rwa [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ]
  exact (Measure.mem_support_iff_forall _).1 hwμ _ (hg.isOpen_support.mem_nhds hgw.ne')
/-- Blow-up maps preserve `Hⁿ`-null sets: if `λ ≠ 0` and `Hⁿ(E) = 0`, then `Hⁿ(η_{x,λ}(E)) = 0`.
Since `η_{x,λ}(E) = λ⁻¹ · (E − x)`, the translation `y ↦ y − x` is an isometry (so
`Hⁿ(E − x) = Hⁿ(E) = 0`) and the dilation by `λ⁻¹ ≠ 0` multiplies `Hⁿ` by `|λ⁻¹|ⁿ`. -/
theorem Submission.dsmc_att_blowUpMap_image_null : ∀ (P n : ℕ) (E : Set (Euclid P)) (x : Euclid P) (lam : ℝ), lam ≠ 0 → μHE[n] E = 0 → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E) = 0 := by
  intro P n E x lam hlam hE
  -- Step 1: `η_{x,λ}(E) = λ⁻¹ · τ(E)`, where `τ y = y − x`
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E =
      (fun z : Euclid P => lam⁻¹ • z) '' ((fun y : Euclid P => y - x) '' E) := by
    rw [Set.image_image]
    rfl
  -- Step 2: `τ` is an isometry, so `Hⁿ(τ(E)) = Hⁿ(E) = 0`
  have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
  have htrans : μHE[n] ((fun y : Euclid P => y - x) '' E) = 0 := by
    rw [hτ.euclideanHausdorffMeasure_image, hE]
  -- Steps 3–4: `Hⁿ(λ⁻¹ · τ(E)) = ‖λ⁻¹‖₊ⁿ • Hⁿ(τ(E)) = 0`
  rw [himage, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam), htrans,
    smul_zero]

/-- **Blow-ups of `M ∩ N` approach every vector of an approximate tangent space** (Simon Ch. 3,
Definition 1.4, chapter-03.txt lines 77–83, tested as in Remark 1.5(3), lines 90–92).  If
`Hⁿ(M \ N) = 0`, `Q` is an approximate tangent space of `M` at `x`, `w ∈ Q` and `s > 0`, then for
all small `λ > 0` some `y ∈ M ∩ N` has `|λ⁻¹(y − x) − w| < s`.  The tent `f = max(0, s − |· − w|)`
lies in `C_c`, vanishes off `B_s(w)` and has `∫_Q f dHⁿ > 0`, so `∫_{η_{x,λ}(M)} f dHⁿ > 0` for
small `λ`; hence `Hⁿ(η_{x,λ}(M) ∩ B_s(w)) ≠ 0`, and since `η_{x,λ}(M \ N)` is `Hⁿ`-null,
`η_{x,λ}(M ∩ N)` meets `B_s(w)`. -/
theorem Submission.dsmc_att_blowUp_points_of_approxTangent : ∀ (P n : ℕ) (M N : Set (Euclid P)) (x w : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → w ∈ Q → ∀ s : ℝ, 0 < s → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ y ∈ M ∩ N, ‖lam⁻¹ • (y - x) - w‖ < s := by
  intro P n M N x w Q hMN hQ hw s hs
  -- the tent `g = max(0, s − |· − w|)`: continuous, `g ≥ 0`, `g(w) = s` and `{g ≠ 0} ⊆ B_s(w)`
  set g : Euclid P → ℝ := fun y => max 0 (s - ‖y - w‖)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y => le_max_left _ _
  have hg_ball : ∀ y, g y ≠ 0 → y ∈ ball w s := by
    intro y hy
    rw [mem_ball, dist_eq_norm]
    by_contra h
    exact hy (max_eq_left (by linarith [not_lt.mp h]))
  have hg_supp : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall w s) fun y hy =>
      not_not.mp fun h => hy (ball_subset_closedBall (hg_ball y h))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_supp⟩
  -- `∫_Q f dHⁿ > 0`, hence `∫_{η_{x,λ}(M)} f dHⁿ > 0` for every `λ ∈ (0, λ₀)`
  have hI : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] :=
    Submission.dsmc_att_setIntegral_submodule_pos P n Q g w hQ.1 hg_cont hg_supp hg_nonneg hw
      (by simp [g, hs])
  obtain ⟨lam₀, hlam₀, hpos⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp ((hQ.2 f).eventually (lt_mem_nhds hI))
  refine ⟨lam₀, hlam₀, fun lam hlam hlam₀' => ?_⟩
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x lam with hη
  -- a positive integral of `f` over `η(M)` forces `Hⁿ(η(M) ∩ B_s(w)) ≠ 0`
  have hball : μHE[n] (η '' M ∩ ball w s) ≠ 0 := by
    intro h0
    have hF : 0 < ∫ y in η '' M, f y ∂μHE[n] := hpos ⟨hlam, hlam₀'⟩
    have hF0 : ∫ y in η '' M, f y ∂μHE[n] = 0 := by
      apply integral_eq_zero_of_ae
      rw [EventuallyEq, ae_iff]
      refine measure_mono_null (fun y hy => hg_ball y hy) ?_
      rw [Measure.restrict_apply measurableSet_ball, inter_comm]
      exact h0
    exact hF.ne' hF0
  -- `η(M \ N)` is `Hⁿ`-null and `η(M) ∩ B_s(w) ⊆ (η(M ∩ N) ∩ B_s(w)) ∪ η(M \ N)`
  have hnull : μHE[n] (η '' (M \ N)) = 0 :=
    Submission.dsmc_att_blowUpMap_image_null P n (M \ N) x lam hlam.ne' hMN
  have hcov : η '' M ∩ ball w s ⊆ (η '' (M ∩ N) ∩ ball w s) ∪ η '' (M \ N) := by
    rintro z ⟨⟨y, hyM, rfl⟩, hz⟩
    by_cases hyN : y ∈ N
    · exact Or.inl ⟨⟨y, ⟨hyM, hyN⟩, rfl⟩, hz⟩
    · exact Or.inr ⟨y, ⟨hyM, hyN⟩, rfl⟩
  have hne : μHE[n] (η '' (M ∩ N) ∩ ball w s) ≠ 0 := fun h0 =>
    hball (measure_mono_null hcov (measure_union_null h0 hnull))
  -- so `η(M ∩ N)` meets `B_s(w)`
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := nonempty_of_measure_ne_zero hne
  refine ⟨y, hy, ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  simpa [hη, Poincare.SimonGMT.Chapter03.blowUpMap] using hz
/-- **Simon Ch. 3, 1.4**: approximate tangent planes are local and do not see `Hⁿ`-null
modifications.  If `M' ⊆ M`, `V` is open, `x ∈ V` and `Hⁿ((M \ M') ∩ V) = 0`, then an
approximate tangent plane of `M` at `x` is one of `M'`.  Given `f ∈ C_c(ℝᴾ)`, take
`B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`.  For `0 < r < s / L` the parts of `η_{x,r}(M)` and
`η_{x,r}(M')` in `B_L(0)` differ inside `η_{x,r}((M \ M') ∩ V)`, which is `Hⁿ`-null because
`η_{x,r}` is Lipschitz.  So the blow-up integrals agree for small `r` and have the same limit. -/
theorem Submission.dtc_approxTangent_of_null_diff : ∀ (P n : ℕ) (M M' V : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), M' ⊆ M → IsOpen V → x ∈ V → μHE[n] ((M \ M') ∩ V) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' V x Q hMM' hV hxV hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV x hxV
  obtain ⟨L, hL, hfL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  -- the blow-up integrals of `M` and `M'` agree for `0 < r < s / L`, so they have the same limit
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
  have hr0 : 0 < r := hr.1
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη]
  -- `f` vanishes off `B_L(0)`, so every set integral may be cut to `B_L(0)`
  have hfB : ∀ y, y ∉ ball (0 : Euclid P) L → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfL h)
  have hcut : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) L ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hfB).symm
  -- `η_{x,r}` is `r⁻¹`-Lipschitz, so it maps the `Hⁿ`-null set `(M \ M') ∩ V` to a null set
  have hnullimg : μHE[n] ((fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V)) = 0 := by
    have hlip : LipschitzWith ‖r⁻¹‖₊ (fun y : Euclid P => r⁻¹ • (y - x)) :=
      LipschitzWith.of_dist_le_mul fun a b =>
        le_of_eq (by rw [dist_smul₀, dist_sub_right, coe_nnnorm])
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul] at hnull ⊢
    have hH : μH[(n : ℝ)] ((M \ M') ∩ V) = 0 := by
      simpa [Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n] using hnull
    have hle := hlip.hausdorffMeasure_image_le (Nat.cast_nonneg n) ((M \ M') ∩ V)
    rw [hH, mul_zero, nonpos_iff_eq_zero] at hle
    rw [hle, mul_zero]
  -- in `B_L(0)`, `η_{x,r}(M)` and `η_{x,r}(M')` differ inside `η_{x,r}((M \ M') ∩ V)`
  have hsub : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) \
      (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M') ⊆
      (fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V) := by
    rintro y ⟨⟨hyB, ⟨z, hz, rfl⟩⟩, hy'⟩
    refine ⟨z, ⟨⟨hz, fun hz' => hy' ⟨hyB, z, hz', rfl⟩⟩, hsV ?_⟩, rfl⟩
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
      inv_mul_lt_iff₀ hr0] at hyB
    have hrL := (lt_div_iff₀ hL).mp hr.2
    rw [mem_ball, dist_eq_norm]
    linarith
  -- hence the two parts are `Hⁿ`-a.e. equal (`M' ⊆ M` gives the other inclusion)
  have hae : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M' : Set (Euclid P))
      =ᵐ[μHE[n]] (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.mpr (inter_subset_inter_right _ (image_mono hMM'))]
      exact measure_empty
    · exact measure_mono_null hsub hnullimg
  rw [hcut, hcut ((fun y : Euclid P => r⁻¹ • (y - x)) '' M'), Measure.restrict_congr_set hae]

/-- **`Df(x)` fixes the approximate tangent space of a pointwise fixed set** (steps 5–6 of the proof
that a map fixing `spt T` preserves the orientation of `T`; approximate tangent spaces as in Simon
Ch. 3, Definition 1.4).  If `f` is differentiable at `x`, `f(x) = x`, `f` fixes every point of `A`
and `Q` is an approximate tangent space of `A` at `x`, then `Df(x)v = v` for every `v ∈ Q`.  The
blow-up points `u = λ⁻¹(y − x)`, `y ∈ A`, approach `v` as `λ ↓ 0`; since `f(y) − f(x) = y − x`,
differentiability gives `|u − Df(x)u| ≤ η|u|`, so `|Df(x)v − v| ≤ ε` for every `ε > 0`. -/
theorem Submission.dtc_bc_lc_fderiv_apply_eq_of_approxTangent : ∀ (P n : ℕ) (A : Set (Euclid P)) (f : Euclid P → Euclid P) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), HasApproximateTangentSpaceAt n A x Q → DifferentiableAt ℝ f x → f x = x → (∀ y ∈ A, f y = y) → ∀ v ∈ Q, fderiv ℝ f x v = v := by
  intro P n A f x Q hQ hf hfx hA v hv
  set L := fderiv ℝ f x
  have hfL : HasFDerivAt f L x := hf.hasFDerivAt
  -- Step 1: it suffices to show `|Lv − v| ≤ ε` for every `ε > 0`; fix the constants
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  set C : ℝ := ‖v‖ + 1 with hC
  set K : ℝ := ‖L‖ + 1 with hK
  have hCpos : 0 < C := by rw [hC]; positivity
  have hKpos : 0 < K := by rw [hK]; positivity
  set η : ℝ := ε / (2 * C) with hη
  set s : ℝ := min 1 (ε / (2 * K))
  have hηpos : 0 < η := div_pos hε (mul_pos two_pos hCpos)
  have hspos : 0 < s := lt_min one_pos (div_pos hε (mul_pos two_pos hKpos))
  have hKs : K * s ≤ ε / 2 := by
    calc K * s ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hKpos.le
      _ = ε / 2 := by field_simp
  have hηC : η * C = ε / 2 := by rw [hη]; field_simp
  -- Step 2: differentiability gives `δ > 0` with `|f(y) − f(x) − L(y − x)| ≤ η|y − x|` near `x`
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp (hfL.isLittleO.bound hηpos)
  -- Step 3: blow-up points of `A ∩ A = A` approach `v`
  obtain ⟨lam₀, hlam₀, hpts⟩ :=
    Submission.dsmc_att_blowUp_points_of_approxTangent P n A A x v Q (by simp) hQ hv s hspos
  -- Step 4: the scale `λ = min(λ₀/2, δ/(2C))` and the point `u = λ⁻¹(y − x)`
  set lam : ℝ := min (lam₀ / 2) (δ / (2 * C))
  have hlampos : 0 < lam := lt_min (half_pos hlam₀) (div_pos hδ (mul_pos two_pos hCpos))
  obtain ⟨y, ⟨hyA, -⟩, hy⟩ := hpts lam hlampos ((min_le_left _ _).trans_lt (half_lt_self hlam₀))
  set u : Euclid P := lam⁻¹ • (y - x) with hu
  have hyx : y - x = lam • u := by rw [hu, smul_inv_smul₀ hlampos.ne']
  have huv : ‖u - v‖ < s := hy
  have huC : ‖u‖ ≤ C := by
    have h1 := norm_le_norm_sub_add u v
    have h2 := huv.trans_le (min_le_left _ _)
    rw [hC]; linarith
  have hyδ : dist y x < δ := by
    rw [dist_eq_norm, hyx, norm_smul, Real.norm_of_nonneg hlampos.le]
    calc lam * ‖u‖ ≤ δ / (2 * C) * C :=
          mul_le_mul (min_le_right _ _) huC (norm_nonneg _) (div_pos hδ (mul_pos two_pos hCpos)).le
      _ = δ / 2 := by field_simp
      _ < δ := half_lt_self hδ
  -- Step 5: `f(y) = y` and `f(x) = x` turn the estimate into `|u − Lu| ≤ η|u| ≤ ε/2`
  have hkey : ‖u - L u‖ ≤ ε / 2 := by
    have h := hδf hyδ
    rw [hA y hyA, hfx, hyx, map_smul, ← smul_sub, norm_smul, norm_smul,
      Real.norm_of_nonneg hlampos.le, mul_left_comm] at h
    calc ‖u - L u‖ ≤ η * ‖u‖ := le_of_mul_le_mul_left h hlampos
      _ ≤ η * C := mul_le_mul_of_nonneg_left huC hηpos.le
      _ = ε / 2 := hηC
  -- Step 6: `|Lv − v| ≤ |L(v − u)| + |Lu − u| + |u − v| ≤ Ks + ε/2 ≤ ε`
  have hLvu : ‖L v - L u‖ ≤ ‖L‖ * ‖u - v‖ := by
    calc ‖L v - L u‖ = ‖L (v - u)‖ := by rw [map_sub]
      _ ≤ ‖L‖ * ‖v - u‖ := L.le_opNorm _
      _ = ‖L‖ * ‖u - v‖ := by rw [norm_sub_rev]
  calc ‖L v - v‖ = ‖(L v - L u) + (L u - u) + (u - v)‖ := by congr 1; abel
    _ ≤ ‖L v - L u‖ + ‖L u - u‖ + ‖u - v‖ := norm_add₃_le
    _ ≤ ‖L‖ * ‖u - v‖ + ε / 2 + ‖u - v‖ := by rw [norm_sub_rev (L u) u]; linarith
    _ = K * ‖u - v‖ + ε / 2 := by rw [hK]; ring
    _ ≤ K * s + ε / 2 := by linarith [mul_le_mul_of_nonneg_left huv.le hKpos.le]
    _ ≤ ε := by linarith
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
/-- **Hilbert–Schmidt bound for precomposing every slot with `A`** (the estimate behind
`|α ∘ L|_E ≤ ‖L‖ⁿ |α|_E` and the push-forward mass bound, Simon 6.2.24(2), 6.2.29, 6.3.3): for a
continuous linear `A : ℝᴺ → ℝᴺ'` and an `n`-linear `γ` on `ℝᴺ'`,
`Σ_{j : Fin n → Fin N} γ(Ae_{j 0}, …, Ae_{j (n-1)})² ≤ (‖A‖²)ⁿ Σ_{j : Fin n → Fin N'} γ(e'_{j 0}, …, e'_{j (n-1)})²`.
One slot: a linear `φ = ⟨g, ·⟩` has `Σᵢ φ(Aeᵢ)² = |A*g|² ≤ ‖A‖² |g|² = ‖A‖² Σₐ φ(e'ₐ)²`; the
other slots follow by induction on `n`, splitting each index tuple as `Fin.cons i j'`. -/
theorem Submission.dimred_mbl_pf_oc_multilinear_hs_comp_le : ∀ (N N' n : ℕ) (A : Euclid N →L[ℝ] Euclid N') (γ : MultilinearMap ℝ (fun _ : Fin n => Euclid N') ℝ), ∑ j : Fin n → Fin N, (γ (fun k => A (EuclideanSpace.basisFun (Fin N) ℝ (j k)))) ^ 2 ≤ (‖A‖ ^ 2) ^ n * ∑ j : Fin n → Fin N', (γ (fun k => EuclideanSpace.basisFun (Fin N') ℝ (j k))) ^ 2 := by
  intro N N' n A γ
  set e := EuclideanSpace.basisFun (Fin N) ℝ
  set e' := EuclideanSpace.basisFun (Fin N') ℝ
  -- one slot: `φ = ⟨g, ·⟩` with `g = Σₐ φ(e'ₐ) e'ₐ`; Parseval for `e` and `e'`, and `‖A*‖ = ‖A‖`
  have hone : ∀ φ : Euclid N' →ₗ[ℝ] ℝ,
      ∑ i : Fin N, (φ (A (e i))) ^ 2 ≤ ‖A‖ ^ 2 * ∑ a : Fin N', (φ (e' a)) ^ 2 := by
    intro φ
    set g : Euclid N' := ∑ a, φ (e' a) • e' a with hg_def
    have hφ : ∀ v, φ v = inner ℝ g v := by
      intro v
      conv_lhs => rw [← e'.sum_repr' v]
      simp only [hg_def, map_sum, map_smul, smul_eq_mul, sum_inner, real_inner_smul_left]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    have hg : ∑ a : Fin N', (φ (e' a)) ^ 2 = ‖g‖ ^ 2 := by
      rw [← e'.sum_sq_inner_left g]
      simp only [hφ]
    have hAg : ∑ i : Fin N, (φ (A (e i))) ^ 2 = ‖(ContinuousLinearMap.adjoint A) g‖ ^ 2 := by
      rw [← e.sum_sq_inner_left]
      simp only [hφ, ContinuousLinearMap.adjoint_inner_left]
    have hnorm : ‖(ContinuousLinearMap.adjoint A) g‖ ≤ ‖A‖ * ‖g‖ := by
      calc ‖(ContinuousLinearMap.adjoint A) g‖
          ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖g‖ := (ContinuousLinearMap.adjoint A).le_opNorm g
        _ = ‖A‖ * ‖g‖ := by rw [LinearIsometryEquiv.norm_map]
    rw [hAg, hg, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    apply le_of_eq
    rw [Fintype.sum_unique, Fintype.sum_unique]
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    -- split each index tuple as `Fin.cons i j'`
    have hsplit : ∀ (M : ℕ) (c : Fin M → Euclid N'),
        ∑ j : Fin (n + 1) → Fin M, (γ (fun k => c (j k))) ^ 2 =
          ∑ i : Fin M, ∑ j' : Fin n → Fin M, (γ (Fin.cons (c i) fun k => c (j' k))) ^ 2 := by
      intro M c
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin M)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j' _ => ?_
      congr 2
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [hsplit N (fun i => A (e i)), hsplit N' e']
    calc ∑ i : Fin N, ∑ j' : Fin n → Fin N, (γ (Fin.cons (A (e i)) fun k => A (e (j' k)))) ^ 2
        ≤ ∑ i : Fin N, (‖A‖ ^ 2) ^ n *
            ∑ j' : Fin n → Fin N', (γ (Fin.cons (A (e i)) fun k => e' (j' k))) ^ 2 := by
          -- the last `n` slots: the induction hypothesis for `γ(Aeᵢ, ·)`
          refine Finset.sum_le_sum fun i _ => ?_
          simpa only [MultilinearMap.curryLeft_apply] using ih (γ.curryLeft (A (e i)))
      _ = (‖A‖ ^ 2) ^ n *
            ∑ j' : Fin n → Fin N', ∑ i : Fin N, (γ (Fin.cons (A (e i)) fun k => e' (j' k))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (‖A‖ ^ 2) ^ n * ∑ j' : Fin n → Fin N',
            ‖A‖ ^ 2 * ∑ a : Fin N', (γ (Fin.cons (e' a) fun k => e' (j' k))) ^ 2 := by
          -- the first slot: `hone` for the linear map `v ↦ γ(v, e'_{j' 0}, …)`
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j' _ => ?_) (by positivity)
          have h := hone (γ.toLinearMap (Fin.cons 0 fun k => e' (j' k)) 0)
          simp only [MultilinearMap.toLinearMap_apply, Fin.update_cons_zero] at h
          exact h
      _ = (‖A‖ ^ 2) ^ (n + 1) *
            ∑ a : Fin N', ∑ j' : Fin n → Fin N', (γ (Fin.cons (e' a) fun k => e' (j' k))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          ring

/-- **The Euclidean coefficient norm under pull-back** (Simon 6.1.15, step (L1) behind the
push-forward of oriented tangent planes): for a linear map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β`
on `ℝᴺ'`, `|β ∘ A|_E ≤ ‖A‖ᵏ |β|_E`.  In the standard bases `e`, `e'` the Hilbert–Schmidt sum
`Σ_j β(Ae_{j(0)}, …, Ae_{j(k−1)})²` is at most `(‖A‖²)ᵏ Σ_j β(e'_{j(0)}, …, e'_{j(k−1)})²`
(`dimred_mbl_pf_oc_multilinear_hs_comp_le`), and the two sums are `k! |β ∘ A|_E²` and `k! |β|_E²`
(`regcomp_covector_sq_sum_orthonormalBasis`); cancel `k! > 0` and take square roots. -/
theorem Submission.dimred_mbl_pf_oc_covectorEuclideanNorm_comp_le : ∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β := by
  intro N N' k A β
  -- Hilbert–Schmidt comparison for `β`, forgetting alternation and continuity
  have hHS := Submission.dimred_mbl_pf_oc_multilinear_hs_comp_le N N' k A
    β.toContinuousMultilinearMap.toMultilinearMap
  -- both sums are `k!` times squared coefficient norms; `(β ∘ A)(e ∘ j) = β(Ae ∘ j)` by definition
  have hL : ∑ j : Fin k → Fin N,
      (β.toContinuousMultilinearMap.toMultilinearMap
        (fun m => A (EuclideanSpace.basisFun (Fin N) ℝ (j m)))) ^ 2 =
      (k.factorial : ℝ) * covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2 :=
    Submission.regcomp_covector_sq_sum_orthonormalBasis N k (β.compContinuousLinearMap A)
      (EuclideanSpace.basisFun (Fin N) ℝ)
  have hR : ∑ j : Fin k → Fin N',
      (β.toContinuousMultilinearMap.toMultilinearMap
        (fun m => EuclideanSpace.basisFun (Fin N') ℝ (j m))) ^ 2 =
      (k.factorial : ℝ) * covectorEuclideanNorm β ^ 2 :=
    Submission.regcomp_covector_sq_sum_orthonormalBasis N' k β (EuclideanSpace.basisFun (Fin N') ℝ)
  rw [hL, hR] at hHS
  -- `k! |β ∘ A|_E² ≤ (‖A‖²)ᵏ k! |β|_E² = k! (‖A‖ᵏ |β|_E)²`; cancel `k! > 0`
  have hsq : covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2 ≤
      (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 :=
    le_of_mul_le_mul_left (hHS.trans_eq (by ring)) (Nat.cast_pos.mpr k.factorial_pos)
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (pow_nonneg (norm_nonneg A) k) (covectorEuclideanNorm_nonneg β)) two_ne_zero).mp hsq
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

/-- **Pulled-back integrand of `f_# τ(M, θ, ξ)`** (Simon 6.2.24(2): for `C¹` `f`,
`f_#T(ω) = ∫_M ⟨ω(f(x)), df_{x#} ξ(x)⟩ θ dHⁿ` makes sense).  If `Hⁿ(M \ K) = 0` for a compact
`K ⊆ U` and `f` is `C¹` on an open `O ⊇ K`, then for continuous `ω` with `‖ω‖ ≤ B` the integrand
`θ ⟨ω(f(x)) ∘ Df(x), ξ⟩` is `Hⁿ⌞M`-integrable and its integral is at most `A B`, where
`A = Λⁿ ∫_{M ∩ K} θ dHⁿ` and `‖Df‖ ≤ Λ` on `K`.  Apply `dpf_pfc_imrep_pairing_integrable_abs_le`
to `F = 1_K · (ω ∘ f) ∘ Df`, which is bounded by `B Λⁿ` and equals `(ω ∘ f) ∘ Df` `Hⁿ⌞M`-a.e. -/
theorem Submission.dimred_mbl_pfc_pullback_integrand_bound : ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ A : ℝ, 0 ≤ A ∧ ∀ (ω : DifferentialForm (Euclid P) n) (B : ℝ), Continuous ω → (∀ z, ‖ω z‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x))) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]| ≤ A * B := by
  intro P n U K O R f hK hKU hMK hO hKO hf
  -- Step 1: `Df` is continuous on `K ⊆ O`, so `‖Df‖ ≤ Λ` on `K` for some `Λ ≥ 0`
  have hDf : ContinuousOn (fderiv ℝ f) K := (hf.continuousOn_fderiv_of_isOpen hO le_rfl).mono hKO
  obtain ⟨Λ, hΛ0, hΛ⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ Λ := by
    obtain ⟨Λ₀, hΛ₀⟩ := hK.exists_bound_of_continuousOn hDf
    exact ⟨max Λ₀ 0, le_max_right _ _, fun x hx => (hΛ₀ x hx).trans (le_max_left _ _)⟩
  -- Step 2: `A = Λⁿ c_K`, `c_K = ∫_{M ∩ K} θ dHⁿ`
  refine ⟨Λ ^ n * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal,
    mul_nonneg (pow_nonneg hΛ0 n) ENNReal.toReal_nonneg, fun ω B hω hωB => ?_⟩
  have hB : 0 ≤ B := (norm_nonneg _).trans (hωB 0)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- Step 3: `β(x) = ω(f(x)) ∘ Df(x)` is continuous on `K`
  have hβ : ContinuousOn (fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) K := by
    simpa using (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      hDf).clm_apply (hω.comp_continuousOn (hf.continuousOn.mono hKO))
  -- Step 4: `F = 1_K β` is a.e. strongly measurable, vanishes off `K` and `‖F‖ ≤ B Λⁿ`
  set F : Euclid P → Covector (Euclid P) n :=
    K.indicator fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x) with hF
  have hFm : AEStronglyMeasurable F (μHE[n].restrict R.carrier) :=
    (aestronglyMeasurable_indicator_iff hKm).2 (hβ.aestronglyMeasurable hKm)
  have hF0 : ∀ x, x ∉ K → F x = 0 := fun x hx => indicator_of_notMem hx _
  have hFB : ∀ x, ‖F x‖ ≤ B * Λ ^ n := by
    intro x
    by_cases hx : x ∈ K
    · rw [hF, indicator_of_mem hx]
      calc ‖(ω (f x)).compContinuousLinearMap (fderiv ℝ f x)‖
          ≤ ‖ω (f x)‖ * ‖fderiv ℝ f x‖ ^ Fintype.card (Fin n) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ ≤ B * Λ ^ n := by
          rw [Fintype.card_fin]
          exact mul_le_mul (hωB _) (pow_le_pow_left₀ (norm_nonneg _) (hΛ x hx) n)
            (pow_nonneg (norm_nonneg _) n) hB
    · rw [hF0 x hx, norm_zero]
      exact mul_nonneg hB (pow_nonneg hΛ0 n)
  -- Step 5: the pairing bound for `F`, with `C = K`
  obtain ⟨hint, hbd⟩ := Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U K R F
    (B * Λ ^ n) hK hKU hFm hF0 hFB
  -- Step 6: `Hⁿ(M \ K) = 0`, so `Hⁿ⌞M`-a.e. `x` lies in `K`, where `F x = β x`
  have hae : (fun x => (R.mult x : ℝ) * R.orient x (F x)) =ᵐ[μHE[n].restrict R.carrier]
      fun x => (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) := by
    have hMK' : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K :=
      (ae_restrict_iff' R.measurableSet_carrier).2
        (ae_iff.2 (measure_mono_null (fun x hx => not_imp.1 hx) hMK))
    filter_upwards [hMK'] with x hx
    rw [hF, indicator_of_mem hx]
  -- Step 7: transfer integrability and the bound `B Λⁿ c_K = A B`
  refine ⟨hint.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  exact hbd.trans_eq (by ring)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]
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
/-- **Simon Ch. 6, 2.23 and Remark 2.24(2)**: the cut-off `χ f^#ω` of a pull-back.  If `f` is
`C¹` on the open set `O`, `K ⊆ O` is compact and `ω` is a continuous `n`-form, then
`f^#ω = ω(f)∘Df` is continuous on `O` (`f`, `Df` are continuous there and `(β, A) ↦ β∘A` is
continuous), and `h = χ f^#ω`, for a Urysohn function `χ` equal to `1` on `K` with compact
`tsupport χ ⊆ O`, is continuous, compactly supported and equal to `f^#ω` on `K`. -/
theorem Submission.dimred_mbl_pf_ext_pullback_cutoff : ∀ (P n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) n), Continuous ω → IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → ∃ h : Euclid P → Covector (Euclid P) n, Continuous h ∧ HasCompactSupport h ∧ ∀ x ∈ K, h x = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  intro P n O K f ω hω hO hf hK hKO
  -- `γ = ω(f)∘Df` is continuous on `O`: `β∘A = compContinuousLinearMapCLM A β`, continuous in `A`
  have hγ : ContinuousOn (fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) O :=
    (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hO le_rfl)).clm_apply
      (hω.comp_continuousOn hf.continuousOn)
  -- Urysohn cut-off: `χ = 1` on `K`, `χ = 0` off an open `V` with `closure V ⊆ O` compact
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχK, hχV, hχc, -⟩ := exists_continuous_one_zero_of_isCompact hK hVo.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKV)
  have hχO : tsupport χ ⊆ O :=
    (closure_mono (support_subset_iff'.mpr fun _ hxV => hχV hxV)).trans hVO
  -- `h = χγ` is continuous on `O` and vanishes off `tsupport χ ⊆ O`
  refine ⟨fun x => χ x • (ω (f x)).compContinuousLinearMap (fderiv ℝ f x),
    (χ.continuous.continuousOn.smul hγ).continuous_of_tsupport_subset hO
      ((tsupport_smul_subset_left _ _).trans hχO), hχc.smul_right, fun x hx => ?_⟩
  simp only [hχK hx, Pi.one_apply, one_smul]
/-- **Simon Ch. 6, remark after 2.14**, with the mollifiers of Ch. 2, §2: test forms approximate
a continuous compactly supported `n`-covector field `h` on `ℝᴾ` uniformly.  Normalise smooth bumps
`φⱼ` with `spt φⱼ = B_{1/(j+1)}(0)` to `ρⱼ = φⱼ / ∫ φⱼ` (`ρⱼ ≥ 0`, `∫ ρⱼ = 1`).  Then `ωⱼ = ρⱼ ⋆ h`
is `C^∞` with compact support, and uniform continuity of `h` gives `‖ωⱼ(x) − h(x)‖ ≤ ε/2` for every
`x` once `1/(j+1) < δ(ε/2)`. -/
theorem Submission.dimred_mbl_pf_ext_testForm_uniform_approx : ∀ (P n : ℕ) (h : Euclid P → Covector (Euclid P) n), Continuous h → HasCompactSupport h → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, TendstoUniformly (fun j x => (ωs j : DifferentialForm (Euclid P) n) x) h atTop := by
  intro P n h hc hs
  -- (1) `h` is locally integrable and uniformly continuous
  have hli : LocallyIntegrable h volume := hc.locallyIntegrable
  have huc : UniformContinuous h := hs.uniformContinuous_of_continuous hc
  -- (2) radii `1/(j+1)` and smooth bumps `φ j` with `support (φ j) = ball 0 (1/(j+1))`
  have hr : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => Nat.one_div_pos_of_nat
  let φ : ℕ → ContDiffBump (0 : Euclid P) := fun j =>
    ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), half_pos (hr j), half_lt_self (hr j)⟩
  have hφpos : ∀ j, 0 < ∫ y, φ j y := fun j => by
    refine (integral_pos_iff_support_of_nonneg (φ j).nonneg'
      ((φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport)).mpr ?_
    rw [(φ j).support_eq]
    exact measure_ball_pos volume 0 (hr j)
  -- the normalised mollifiers `ρ j = φ j / ∫ φ j`
  let ρ : ℕ → Euclid P → ℝ := fun j y => φ j y / ∫ y, φ j y
  have hρφ : ∀ j, support (ρ j) ⊆ support (φ j) := fun j y hy h0 => hy (by simp [ρ, h0])
  have hρs : ∀ j, support (ρ j) ⊆ ball 0 (1 / ((j : ℝ) + 1)) := fun j =>
    (hρφ j).trans (φ j).support_eq.subset
  have hρc : ∀ j, HasCompactSupport (ρ j) := fun j => (φ j).hasCompactSupport.mono (hρφ j)
  have hρ0 : ∀ j y, 0 ≤ ρ j y := fun j y => div_nonneg (φ j).nonneg (hφpos j).le
  have hρ1 : ∀ j, ∫ y, ρ j y = 1 := fun j => by
    simp only [ρ]
    rw [integral_div, div_self (hφpos j).ne']
  -- (3) the test forms `ω j = ρ j ⋆ h`: smooth with compact support
  let ω : ℕ → DifferentialForm (Euclid P) n := fun j =>
    convolution (ρ j) h (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hωmem : ∀ j, ω j ∈ TestFormOn (univ : Set (Euclid P)) n := fun j =>
    ⟨⟨(hρc j).contDiff_convolution_left _ ((φ j).contDiff.div_const _) hli,
      (hρc j).convolution _ hs⟩, subset_univ _⟩
  refine ⟨fun j => ⟨ω j, hωmem j⟩, ?_⟩
  -- (4) the uniform estimate `dist (ω j x) (h x) ≤ ε/2` for `j ≥ J`
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hhδ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.mpr ⟨J, fun j hj x => ?_⟩
  have hrj : 1 / ((j : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
    gcongr
  have hd : dist (ω j x) (h x) ≤ ε / 2 :=
    dist_convolution_le (half_pos hε).le (hρs j) (hρ0 j) (hρ1 j) hc.aestronglyMeasurable
      fun y hy => (hhδ ((mem_ball.mp hy).trans_le (hrj.trans hJ.le))).le
  -- (5) conclusion
  rw [dist_comm]
  exact hd.trans_lt (half_lt_self hε)
/-- **The action of `τ(M, θ, ξ)` is continuous under uniform convergence on a compact set carrying
`M`** (Simon 6.3.1 (‡); used to extend push-forwards in the dimension reduction argument).  Let
`R = (M, θ, ξ)` be a triple in `U`, `K ⊆ U` compact with `Hⁿ(M \ K) = 0`, and `hⱼ → h` uniformly
on `K`, all continuous.  Then `R.action hⱼ → R.action h`.

With `μ = Hⁿ⌞M`: `μ`-a.e. point lies in `K`; `|ξ(x)(α)| ≤ ‖α‖` `μ`-a.e. (orthonormal `τ`);
`θ` is `μ`-integrable since `μ = Hⁿ⌞(M ∩ K)`; with `‖h‖ ≤ B` on `K` and eventually
`‖hⱼ − h‖ < 1` on `K`, dominated convergence with bound `(B + 1) θ` applies. -/
theorem Submission.dimred_mbl_pf_ext_action_tendsto : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (hs : ℕ → Euclid P → Covector (Euclid P) n) (h : Euclid P → Covector (Euclid P) n), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → (∀ j, Continuous (hs j)) → Continuous h → TendstoUniformlyOn hs h atTop K → Tendsto (fun j => R.action (hs j)) atTop (𝓝 (R.action h)) := by
  intro P n U K R hs h hK hKU hnull hsc hc hu
  -- (1) `μ`-a.e. point lies in `K`
  have hμK : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    exact fun x hx => ⟨hx.2, hx.1⟩
  -- (2) orientation bound `|ξ(x)(α)| ≤ ‖α‖`, from `ξ(x)(α) = ±α(τ)` with `τ` orthonormal
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hsign⟩ := hx
    have hτα : ‖α τ‖ ≤ ‖α‖ := (α.le_opNorm τ).trans_eq (by simp [hτ.1])
    rcases hsign with hξα | hξα
    · rw [hξα α]
      exact hτα
    · rw [hξα α, norm_neg]
      exact hτα
  -- (3) `θ` is `μ`-integrable, as `μ = Hⁿ⌞(M ∩ K)`
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hμ : μHE[n].restrict R.carrier = μHE[n].restrict (R.carrier ∩ K) := by
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · rwa [Set.sdiff_self_inter]
    · refine measure_mono_null ?_ measure_empty
      exact fun x hx => hx.2 hx.1.1
  have hθi : Integrable (fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hμ]
    simp only [Real.enorm_natCast]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  -- (4) `θ ξ(g)` is `μ`-a.e. strongly measurable for continuous `g`
  have hmeas : ∀ g : Euclid P → Covector (Euclid P) n, Continuous g →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (g x))
        (μHE[n].restrict R.carrier) := fun g hg =>
    hθm.aestronglyMeasurable.mul
      (Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        isBoundedBilinearMap_apply.continuous R.aestronglyMeasurable_orient
        hg.aestronglyMeasurable)
  -- (5) `‖h‖ ≤ B` on `K`, and eventually `‖hⱼ − h‖ < 1` on `K`
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hu1 := Metric.tendstoUniformlyOn_iff.mp hu 1 one_pos
  -- (6) dominated convergence with bound `(B + 1) θ`
  simp only [IMRep.action]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (B + 1) * (R.mult x : ℝ))
    (Eventually.of_forall fun j => hmeas (hs j) (hsc j)) ?_ (hθi.const_mul (B + 1)) ?_
  · filter_upwards [hu1] with j hj
    filter_upwards [hμK, hξ] with x hxK hxξ
    have hjx : ‖hs j x‖ ≤ B + 1 :=
      (norm_le_insert' (hs j x) (h x)).trans (add_le_add (hB x hxK) (by
        rw [← dist_eq_norm, dist_comm]
        exact (hj x hxK).le))
    rw [norm_mul, Real.norm_natCast, mul_comm (B + 1)]
    exact mul_le_mul_of_nonneg_left ((hxξ _).trans hjx) (Nat.cast_nonneg _)
  · filter_upwards [hμK] with x hxK
    exact (((R.orient x).continuous.tendsto _).comp (hu.tendsto_at hxK)).const_mul _
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
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0

/-- **Simon Ch. 6, 3.2(3) and 2.11–2.12**: if `T = τ(M, θ, ξ)` in the open set `U`, then
(i) `M_W(T) = μ_R(W)` for every open `W`, where `μ_R = θ Hⁿ⌞M`, and (ii) `spt T = U ∩ spt μ_R`.
`M_W(T) ≤ μ_R(W)` because admissible forms pair with `ξ` to at most `1`; `μ_R(W) ≤ M_W(T)` by
smoothing the dual covector field of `ξ` (Lusin); (ii) follows from (i) alone. -/
theorem Submission.dor_imrep_massOn_eq_measure_and_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support := by
  intro P n U T R hU hR
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  exact ⟨hmass, Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass⟩
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
/-- **Countable bi-Lipschitz partition.**  If `H : ℝⁿ → ℝᴾ` is differentiable with injective
derivative at every point of a Borel set `B`, then `B` is the disjoint union of Borel sets `Cₗ`
with `mₗ|a − a'| ≤ |H(a) − H(a')|` on `Cₗ` for some `mₗ > 0`.  An injective `A` satisfies
`c(A)|v| ≤ |Av|` for some `c(A) > 0` (finite dimension); Mathlib's partition lemma, with radius
`c(A)/2`, cuts `B` into Borel pieces on which `H` is `c(Aₗ)/2`-close to some `Aₗ = DH(y)`,
`y ∈ B`, and the triangle inequality gives the bound with `mₗ = c(Aₗ)/2`. -/
theorem Submission.dimred_mbl_pfi_bilipschitz_partition : ∀ (P n : ℕ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → ∃ (C : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ l, MeasurableSet (C l)) ∧ Pairwise (fun k l => Disjoint (C k) (C l)) ∧ (⋃ l, C l) = B ∧ (∀ l, 0 < m l) ∧ ∀ l, ∀ a ∈ C l, ∀ a' ∈ C l, m l * ‖a - a'‖ ≤ ‖H a - H a'‖ := by
  intro P n H B hB hd
  classical
  -- coercivity constants of injective linear maps
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, Injective A →
      ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ≤ ‖A v‖ := by
    intro A hA
    obtain ⟨K, hK0, hK⟩ := (A : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hA)
    refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK0, fun v => ?_⟩
    have h := hK.le_mul_dist v 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h
    have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
    rw [inv_mul_le_iff₀ hK0']
    exact h
  let c : (Euclid n →L[ℝ] Euclid P) → ℝ := fun A =>
    if h : Injective A then Classical.choose (hcoer A h) else 1
  have hc : ∀ A, 0 < c A := by
    intro A
    by_cases h : Injective A
    · simp only [c, dite_eq_left h]; exact (Classical.choose_spec (hcoer A h)).1
    · simp only [c, dite_eq_right h]; exact one_pos
  have hcA : ∀ A : Euclid n →L[ℝ] Euclid P, Injective A → ∀ v, c A * ‖v‖ ≤ ‖A v‖ := by
    intro A h v
    simp only [c, dite_eq_left h]
    exact (Classical.choose_spec (hcoer A h)).2 v
  -- the partition radius `r(A) = c(A)/2`
  let r : (Euclid n →L[ℝ] Euclid P) → NNReal := fun A => (c A / 2).toNNReal
  have hr : ∀ A, (r A : ℝ) = c A / 2 := fun A => Real.coe_toNNReal _ (by linarith [hc A])
  have rpos : ∀ A, r A ≠ 0 := fun A => (Real.toNNReal_pos.mpr (by linarith [hc A])).ne'
  obtain ⟨t, A, hdisj, htm, hcov, happ, hrep⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H B (fderiv ℝ H)
      (fun x hx => (hd x hx).1.hasFDerivAt.hasFDerivWithinAt) r rpos
  -- pieces `Cₗ = B ∩ tₗ`, constants `mₗ = r(Aₗ)`
  refine ⟨fun l => B ∩ t l, fun l => r (A l), fun l => hB.inter (htm l), ?_, ?_,
    fun l => ?_, fun l a ha a' ha' => ?_⟩
  · intro k l hkl
    exact (hdisj hkl).mono inter_subset_right inter_subset_right
  · rw [← inter_iUnion]
    exact inter_eq_left.mpr hcov
  · have := hc (A l)
    show 0 < (r (A l) : ℝ)
    rw [hr]
    linarith
  -- lower bound: `Aₗ = DH(y)` is injective, and `H` is `c(Aₗ)/2`-close to `Aₗ` on `Cₗ`
  · have hne : B.Nonempty := ⟨a, ha.1⟩
    obtain ⟨y, hy, hAy⟩ := hrep hne l
    have hinjA : Injective (A l) := hAy ▸ (hd y hy).2
    have h1 := happ l a ha a' ha'
    have h2 := hcA (A l) hinjA (a - a')
    have h3 : ‖A l (a - a')‖ ≤ ‖H a - H a'‖ + ‖H a - H a' - A l (a - a')‖ := by
      have := norm_sub_le (H a - H a') (H a - H a' - A l (a - a'))
      simpa using this
    show (r (A l) : ℝ) * ‖a - a'‖ ≤ ‖H a - H a'‖
    rw [hr] at h1 ⊢
    linarith
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
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

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

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ
/-- **A unit orientation paired with a pulled-back covector** (Simon Ch. 6, 1.8–1.10 and
3.3–3.4: `⟨L^#α, ξ⟩ = ⟨α, L_#ξ⟩` with `L_#(τ₁ ∧ ⋯ ∧ τₙ) = Lτ₁ ∧ ⋯ ∧ Lτₙ`).  Write
`ξ(β) = ±β(τ)` with `τ` an orthonormal basis of `Q`, and `α ∘ L = α.compContinuousLinearMap L`.
(a) `|ξ(α ∘ L)| = |(α ∘ L)(τ)| ≤ |α ∘ L|_E ≤ ‖L‖ⁿ |α|_E` (`regcomp_covector_eval_orthonormal_le`,
then `dimred_mbl_pf_oc_covectorEuclideanNorm_comp_le`).  (b) If `L` fixes `Q` pointwise, then
`Lτᵢ = τᵢ` since `τᵢ ∈ span τ = Q`, so `(α ∘ L)(τ) = α(Lτ₁, …, Lτₙ) = α(τ)` and
`ξ(α ∘ L) = ξ(α)`. -/
theorem Submission.dimred_mbl_pf_unitOrientation_comp : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ (α.compContinuousLinearMap L)| ≤ covectorEuclideanNorm α * ‖L‖ ^ n) ∧ ((∀ v ∈ Q, L v = v) → ∀ α : Covector (Euclid P) n, ξ (α.compContinuousLinearMap L) = ξ α) := by
  intro P n ξ Q L hξ
  -- `ξ(β) = ±β(τ)` with one sign, `τ` an orthonormal basis of `Q`; hence `|ξ(β)| = |β(τ)|`
  obtain ⟨τ, hτ, hspan, hsign⟩ := hξ
  have habs : ∀ β : Covector (Euclid P) n, |ξ β| = |β τ| := by
    intro β
    rcases hsign with h | h
    · rw [h]
    · rw [h, abs_neg]
  refine ⟨fun α => ?_, fun hL α => ?_⟩
  · -- (a) `|ξ(α ∘ L)| = |(α ∘ L)(τ)| ≤ |α ∘ L|_E ≤ ‖L‖ⁿ |α|_E`
    rw [habs, mul_comm]
    exact (Submission.regcomp_covector_eval_orthonormal_le P n (α.compContinuousLinearMap L) τ
      hτ).trans (Submission.dimred_mbl_pf_oc_covectorEuclideanNorm_comp_le P P n L α)
  · -- (b) `τᵢ ∈ span τ = Q` is fixed by `L`, so `(α ∘ L)(τ) = α(L ∘ τ) = α(τ)`
    have hLτ : ⇑L ∘ τ = τ := funext fun i =>
      hL (τ i) (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
    have hτα : (α.compContinuousLinearMap L) τ = α τ := by
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hLτ]
    rcases hsign with h | h <;> rw [h, h, hτα]

/-- **Simon Ch. 6, 2.4, 2.11 and 3.2(3)**, for currents in `ℝᴾ`.  If `Y = τ(M, θ, ξ)`, then
`M(Y) = μ_R(ℝᴾ)` and `spt Y = spt μ_R`; `ℝᴾ` is hereditarily Lindelöf, so `μ_R(ℝᴾ \ spt Y) = 0`,
and `θ ≥ 1` on `M` gives `Hⁿ(M \ spt Y) = 0`.  If `spt Y` is compact, `μ_R(ℝᴾ) = μ_R(spt Y)` is
finite by local integrability of `θ`.  Supports are complements of open zero regions, and a common
relatively compact neighbourhood on which `Y₁` and `Y₂` vanish lies in the zero region of
`Y₁ - Y₂`. -/
theorem Submission.dimred_mbl_pf_imrep_carrier_mass_support : ∀ (P n : ℕ), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → μHE[n] (R.carrier \ Y.support) = 0 ∧ Y.mass = R.measure univ ∧ (IsCompact Y.support → R.measure univ ≠ ∞)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y₁.support ∧ (Y₁ - Y₂).support ⊆ Y₁.support ∪ Y₂.support := by
  intro P n
  -- Step 6: `spt Y = ℝᴾ \ Z(Y)` is the complement of the open zero region
  have hclosed : ∀ Y : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y.support :=
    fun Y => by
      rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
      exact Y.isOpen_zeroRegion.isClosed_compl
  refine ⟨fun Y R hR => ?_, fun Y₁ Y₂ => ⟨hclosed Y₁, ?_⟩⟩
  · -- Step 1: `M_W(Y) = μ_R(W)` for open `W`, and `spt Y = spt μ_R`
    obtain ⟨hmass, hsupp⟩ :=
      Submission.dor_imrep_massOn_eq_measure_and_support P n univ Y R isOpen_univ hR
    rw [univ_inter] at hsupp
    -- Step 3: `μ_R(ℝᴾ \ spt Y) = 0`, `ℝᴾ` being hereditarily Lindelöf
    have hnull : R.measure (Y.support)ᶜ = 0 := by
      rw [hsupp]
      exact Measure.measure_compl_support
    refine ⟨?_, hmass univ isOpen_univ, fun hK => ?_⟩
    · -- Step 4: `θ ≥ 1` on `M`, so `Hⁿ(M \ spt Y) = 0`
      have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
        (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp R.measurable_mult
      have h0 := (withDensity_apply_eq_zero hθ).1 hnull
      rw [Measure.restrict_apply' R.measurableSet_carrier] at h0
      refine measure_mono_null (fun x hx => ?_) h0
      exact ⟨⟨Nat.cast_ne_zero.2 (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    · -- Step 5: `μ_R(ℝᴾ) = μ_R(spt Y) = ∫_{M ∩ spt Y} θ dHⁿ < ∞`
      have hfin : R.measure Y.support ≠ ∞ := by
        rw [IMRep.measure, withDensity_apply _ (hclosed Y).measurableSet,
          Measure.restrict_restrict (hclosed Y).measurableSet, inter_comm]
        exact R.locallyIntegrable_mult _ hK (subset_univ _)
      refine ne_top_of_le_ne_top hfin ?_
      calc R.measure univ ≤ R.measure Y.support + R.measure (Y.support)ᶜ :=
            measure_univ_le_add_compl _
        _ = R.measure Y.support := by rw [hnull, add_zero]
  · -- Step 7: a common relatively compact neighbourhood where `Y₁`, `Y₂` vanish
    intro x hx
    by_contra hx'
    rw [mem_union, not_or] at hx'
    simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_univ, true_and, not_not] at hx hx'
    obtain ⟨⟨W₁, ⟨hW₁, hW₁c, -, hY₁⟩, hxW₁⟩, ⟨W₂, ⟨hW₂, -, -, hY₂⟩, hxW₂⟩⟩ := hx'
    refine hx ⟨W₁ ∩ W₂, ⟨hW₁.inter hW₂, hW₁c.of_isClosed_subset isClosed_closure
      (closure_mono inter_subset_left), subset_univ _, fun ω hω => ?_⟩, hxW₁, hxW₂⟩
    show Y₁ ω - Y₂ ω = 0
    rw [hY₁ ω (hω.trans inter_subset_left), hY₂ ω (hω.trans inter_subset_right), sub_zero]

/-- **Push-forward of `τ(M, θ, ξ)` by a `C¹` map** (Simon 6.2.23–6.2.24(2)).  If `Hⁿ⌞M` is
carried by the compact `K ⊆ U`, `f` is `C¹` on an open `O ⊇ K` and `f(K) ⊆ U`, then
`Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ(x)` defines `Q ∈ 𝒟ₙ(U)` with `spt Q` a compact
subset of `f(K)`.  The bound `|Q(ω)| ≤ A sup |ω|` makes the linear functional `Q` a current.
If `spt ω` misses `f(K)`, then `ω(f(x)) = 0` for `x ∈ K`, which is `Hⁿ`-almost all of `M`, so
`Q(ω) = 0`. -/
theorem Submission.dimred_mbl_pf_pushforward_current_exists : ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → ∃ Q : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) ∧ IsCompact Q.support ∧ Q.support ⊆ f '' K := by
  intro P n U K O R f hU hK hKU hMK hO hKO hf hfK
  -- Step 1: `I(ω) = θ ⟨ω(f) ∘ Df, ξ⟩` is integrable and `|∫_M I(ω)| ≤ A B` if `‖ω‖ ≤ B`
  obtain ⟨A, -, hA⟩ := Submission.dimred_mbl_pfc_pullback_integrand_bound P n U K O R f hK hKU
    hMK hO hKO hf
  let I : DifferentialForm (Euclid P) n → Euclid P → ℝ := fun ω x =>
    (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x))
  -- a test form is continuous with compact support, hence bounded
  have hint : ∀ ω : TestFormOn U n,
      Integrable (I (ω : DifferentialForm (Euclid P) n)) (μHE[n].restrict R.carrier) := by
    intro ω
    obtain ⟨B, hB⟩ := ω.2.1.1.continuous.bounded_above_of_compact_support ω.2.1.2
    exact (hA _ B ω.2.1.1.continuous hB).1
  -- Step 2: `I` is linear in `ω`, since `α ↦ α ∘ Df(x)` and `ξ(x)` are linear
  have hadd : ∀ (ω η : TestFormOn U n) (x : Euclid P),
      I ((ω + η : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
        I (ω : DifferentialForm (Euclid P) n) x + I (η : DifferentialForm (Euclid P) n) x := by
    intro ω η x
    have h : ∀ α β : Covector (Euclid P) n, (α + β).compContinuousLinearMap (fderiv ℝ f x) =
        α.compContinuousLinearMap (fderiv ℝ f x) + β.compContinuousLinearMap (fderiv ℝ f x) := by
      intro α β
      ext v
      simp
    simp only [I, Submodule.coe_add, Pi.add_apply, h, map_add, mul_add]
  have hsmul : ∀ (c : ℝ) (ω : TestFormOn U n) (x : Euclid P),
      I ((c • ω : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
        c * I (ω : DifferentialForm (Euclid P) n) x := by
    intro c ω x
    have h : ∀ α : Covector (Euclid P) n, (c • α).compContinuousLinearMap (fderiv ℝ f x) =
        c • α.compContinuousLinearMap (fderiv ℝ f x) := by
      intro α
      ext v
      simp
    simp only [I, Submodule.coe_smul, Pi.smul_apply, h, map_smul, smul_eq_mul]
    ring
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in R.carrier, I (ω : DifferentialForm (Euclid P) n) x ∂μHE[n]
      map_add' := fun ω η => by
        simp only [hadd]
        exact integral_add (hint ω) (hint η)
      map_smul' := fun c ω => by
        simp only [hsmul, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  -- Step 3: with `c = A` on every compact set, `L` is a current `Q`
  obtain ⟨Q, hQ⟩ := Submission.cmcs_rc_order_zero_current P n U L fun _ _ _ =>
    ⟨A, fun ω B _ hB => (hA _ B ω.2.1.1.continuous hB).2⟩
  -- Step 4: `Hⁿ`-a.e. point of `M` lies in `K`
  have hMKae : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K := by
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff]
    exact measure_mono_null (fun x hx => not_imp.mp hx) hMK
  -- Step 5: `Q(ω) = 0` if `spt ω ∩ f(K) = ∅`, as then `ω(f(x)) = 0` for `x ∈ K`
  have hvan : ∀ ω : TestFormOn U n,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f '' K) → Q ω = 0 := by
    intro ω hω
    rw [hQ]
    show ∫ x in R.carrier, I (ω : DifferentialForm (Euclid P) n) x ∂μHE[n] = 0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hMKae] with x hx
    have h0 : (ω : DifferentialForm (Euclid P) n) (f x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hω.notMem_of_mem_left h (mem_image_of_mem f hx)
    have h : ((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x) =
        0 := by
      ext v
      simp [h0]
    simp only [I, h, map_zero, mul_zero, Pi.zero_apply]
  -- Step 6: `f(K)` is a compact subset of `U`, so `spt Q` is a compact subset of `f(K)`
  obtain ⟨hsub, hcpt⟩ := Submission.rsd_cmr_support_subset_of_vanish P n U (f '' K) Q hU
    (hK.image_of_continuousOn (hf.continuousOn.mono hKO)) hfK hvan
  exact ⟨Q, hQ, hcpt, hsub⟩
/-- **Simon Ch. 6, 2.23 and Remark 2.24(2)**: the pulled-back integral `∫_M θ ξ(f^#ω) dHⁿ` is the
limit of `Y(ωⱼ)` for test forms `ωⱼ` chosen before `Y` and its representation.  The cut-off
`h = χ f^#ω` is continuous, compactly supported and equal to `f^#ω` on `K`, and test forms
`ωⱼ → h` uniformly; both depend only on `f`, `ω`, `O` and `K`.  If `Y = τ(M, θ, ξ)` with
`spt Y ⊆ K`, then `Hⁿ(M \ K) = 0`, so `Y(ωⱼ) = τ(M, θ, ξ)(ωⱼ) → τ(M, θ, ξ)(h)`, and
`τ(M, θ, ξ)(h) = ∫_M θ ξ(f^#ω) dHⁿ` since `h = f^#ω` on `K`. -/
theorem Submission.dimred_mbl_pf_pullback_integral_extension : ∀ (P n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) n), IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, ∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → Y.support ⊆ K → Tendsto (fun j => Y (ωs j)) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n])) := by
  intro P n O K f ω hO hf hK hKO
  -- (1) the cut-off `h = χ f^#ω`: continuous, compactly supported, `h = f^#ω` on `K`
  obtain ⟨h, hc, hs, hhK⟩ := Submission.dimred_mbl_pf_ext_pullback_cutoff P n O K f
    (ω : DifferentialForm (Euclid P) n) ω.property.1.1.continuous hO hf hK hKO
  -- (2) test forms `ωⱼ → h` uniformly on `ℝᴾ`, chosen before `Y` and `R`
  obtain ⟨ωs, hu⟩ := Submission.dimred_mbl_pf_ext_testForm_uniform_approx P n h hc hs
  refine ⟨ωs, fun Y R hR hYK => ?_⟩
  -- (3) `Hⁿ(M \ K) = 0`, since `Hⁿ(M \ spt Y) = 0` and `spt Y ⊆ K`
  have hnull : μHE[n] (R.carrier \ K) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_right hYK)
      ((Submission.dimred_mbl_pf_imrep_carrier_mass_support P n).1 Y R hR).1
  -- (4) `τ(M, θ, ξ)(ωⱼ) → τ(M, θ, ξ)(h)`
  have hlim := Submission.dimred_mbl_pf_ext_action_tendsto P n univ K R
    (fun j => (ωs j : DifferentialForm (Euclid P) n)) h hK (subset_univ K) hnull
    (fun j => (ωs j).property.1.1.continuous) hc hu.tendstoUniformlyOn
  -- (5) `τ(M, θ, ξ)(h) = ∫_M θ ξ(f^#ω) dHⁿ`, as `Hⁿ⌞M`-a.e. point lies in `K`
  have hμK : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    exact fun x hx => ⟨hx.2, hx.1⟩
  have heq : R.action h = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x
      (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x))
        ∂μHE[n] := by
    rw [IMRep.action]
    refine integral_congr_ae ?_
    filter_upwards [hμK] with x hx
    rw [hhK x hx]
  -- (6) `Y(ωⱼ) = τ(M, θ, ξ)(ωⱼ)`
  rw [← heq]
  exact hlim.congr fun j => (hR (ωs j)).symm
/-- **Simon Ch. 6, 2.24(2) and 2.29, mass of a `C¹` push-forward**: let `Y = τ(M, θ, ξ)` have
compact support `spt Y ⊆ O`, `‖Df‖ ≤ L` on `O`, and `Z(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ`.
Then `M(Z) ≤ Lⁿ M(Y)`.  `Hⁿ`-a.e. on `M`, `x ∈ spt Y ⊆ O` (so `0 ≤ ‖Df(x)‖ ≤ L`) and `ξ(x)` is a
unit orientation, so `|⟨ω(f(x)) ∘ Df(x), ξ(x)⟩| ≤ |ω(f(x))| ‖Df(x)‖ⁿ ≤ Lⁿ` for admissible `ω`;
with `∫_M θ dHⁿ = μ_Y(ℝᴾ) = M(Y) < ∞` this gives `|Z(ω)| ≤ Lⁿ M(Y)`. -/
theorem Submission.dimred_mbl_pf_pushforward_mass_le : ∀ (P n : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P) (L : ℝ) (Y Z : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ L) → R.Represents Y → IsCompact Y.support → Y.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → Z.mass ≤ ENNReal.ofReal (L ^ n) * Y.mass := by
  intro P n O f L Y Z R hL hR hK hKO hZ
  obtain ⟨hnull, hmass, hfin⟩ :=
    (Submission.dimred_mbl_pf_imrep_carrier_mass_support P n).1 Y R hR
  have hfin' : R.measure univ ≠ ∞ := hfin hK
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  -- `μ_Y(ℝᴾ) = ∫_M θ dHⁿ < ∞`: `θ` is `Hⁿ⌞M`-integrable and `∫_M θ dHⁿ = μ_Y(ℝᴾ)`
  have hlin : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    simpa using integrable_toReal_of_lintegral_ne_top hθm.aemeasurable (hlin ▸ hfin')
  have hθ : ∫ x in R.carrier, (R.mult x : ℝ) ∂μHE[n] = (R.measure univ).toReal := by
    rw [hlin, ← integral_toReal hθm.aemeasurable (ae_of_all _ fun x => ENNReal.natCast_lt_top _)]
    simp only [ENNReal.toReal_natCast]
  -- `Hⁿ`-a.e. point of `M` lies in `spt Y ⊆ O`
  have hO : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ O := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    exact hKO (Classical.byContradiction fun h => hx ⟨hxM, h⟩)
  rw [hmass]
  apply sSup_le
  rintro r ⟨ω, ⟨-, hω1⟩, rfl⟩
  -- `|θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩| ≤ Lⁿ θ` `Hⁿ`-a.e. on `M`
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖(R.mult x : ℝ) * R.orient x
      (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x))‖ ≤
        L ^ n * (R.mult x : ℝ) := by
    filter_upwards [hO, R.orients] with x hxO hx
    obtain ⟨Q, -, hQ⟩ := hx
    have h1 := (Submission.dimred_mbl_pf_unitOrientation_comp P n (R.orient x) Q (fderiv ℝ f x)
      hQ).1 ((ω : DifferentialForm (Euclid P) n) (f x))
    have h2 : ‖fderiv ℝ f x‖ ^ n ≤ L ^ n := pow_le_pow_left₀ (norm_nonneg _) (hL x hxO) n
    rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_comm (L ^ n)]
    exact mul_le_mul_of_nonneg_left
      (h1.trans ((mul_le_of_le_one_left (by positivity) (hω1 _)).trans h2)) (Nat.cast_nonneg _)
  -- `|Z(ω)| ≤ Lⁿ ∫_M θ dHⁿ = Lⁿ μ_Y(ℝᴾ)`
  have hZω : ‖Z ω‖ ≤ L ^ n * (R.measure univ).toReal := by
    rw [hZ ω, ← hθ, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hθint.const_mul _) hbound
  calc ENNReal.ofReal (Z ω) ≤ ENNReal.ofReal (L ^ n * (R.measure univ).toReal) :=
        ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans hZω)
    _ = ENNReal.ofReal (L ^ n) * R.measure univ := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin']
/-- **A push-forward by a `C¹` map fixing `spt Y` pointwise is `Y`** (Simon Ch. 6, 2.24(2)–(3)
and 3.3; approximate tangent spaces as in Ch. 3, 1.4).  Let `Y = τ(M, θ, ξ)`, `spt Y ⊆ O` with `O`
open, `f ∈ C¹(O)` fix `spt Y` pointwise and `Z(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ`.  Since
`Hⁿ(M \ spt Y) = 0`, blow-ups of points of `M ∩ spt Y` approach every vector of the approximate
tangent plane `Q` oriented by `ξ(x)` at `Hⁿ`-a.e. `x ∈ M`; `f` fixes these points, so `Df(x)`
fixes `Q`, hence `ξ(x)(ω(f(x)) ∘ Df(x)) = ξ(x)(ω(x))` and the integrands of `Z(ω)` and `Y(ω)`
agree `Hⁿ⌞M`-a.e. -/
theorem Submission.dimred_mbl_pf_pushforward_eq_self_of_fix : ∀ (P n : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P) (Y Z : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsOpen O → ContDiffOn ℝ 1 f O → R.Represents Y → Y.support ⊆ O → (∀ y ∈ Y.support, f y = y) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → Z = Y := by
  intro P n O f Y Z R hO hf hR hYO hfix hZ
  -- Step 1 (carrier_facts): `Hⁿ(M \ spt Y) = 0`
  have hnull : μHE[n] (R.carrier \ Y.support) = 0 :=
    ((Submission.dimred_mbl_pf_imrep_carrier_mass_support P n).1 Y R hR).1
  -- Step 2: `Hⁿ⌞M`-a.e. `x` lies in `spt Y` and `ξ(x)` orients an approximate tangent plane of `M`
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ Y.support ∧
      ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    have hK : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ Y.support := by
      rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
      refine measure_mono_null (fun x hx => ?_) hnull
      exact ⟨hx.2, hx.1⟩
    filter_upwards [hK, R.orients] with x hxK hxQ using ⟨hxK, hxQ⟩
  -- Steps 3–4: at `x ∈ spt Y`, `Df(x)` fixes every approximate tangent plane `Q` of `M` at `x`
  have hDf : ∀ x ∈ Y.support, ∀ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q → ∀ w ∈ Q, fderiv ℝ f x w = w := by
    intro x hxK Q hQ w hw
    -- Step 3: `x ∈ spt Y ⊆ O` with `O` open and `f ∈ C¹(O)`, so `f` is differentiable at `x`;
    -- and `f(x) = x`
    set L := fderiv ℝ f x
    have hfL : HasFDerivAt f L x :=
      ((hf.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hYO hxK))).hasFDerivAt
    have hfx : f x = x := hfix x hxK
    -- Step 4: it suffices to show `|Lw − w| ≤ ε` for every `ε > 0`; fix the constants
    refine eq_of_forall_dist_le fun ε hε => ?_
    rw [dist_eq_norm]
    set C : ℝ := ‖w‖ + 1 with hC
    set B : ℝ := ‖L‖ + 1 with hB
    have hCpos : 0 < C := by rw [hC]; positivity
    have hBpos : 0 < B := by rw [hB]; positivity
    set η : ℝ := ε / (2 * C) with hη
    set s : ℝ := min 1 (ε / (2 * B))
    have hηpos : 0 < η := div_pos hε (mul_pos two_pos hCpos)
    have hspos : 0 < s := lt_min one_pos (div_pos hε (mul_pos two_pos hBpos))
    have hBs : B * s ≤ ε / 2 := by
      calc B * s ≤ B * (ε / (2 * B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hBpos.le
        _ = ε / 2 := by field_simp
    have hηC : η * C = ε / 2 := by rw [hη]; field_simp
    -- differentiability at `x`: `|f(y) − f(x) − L(y − x)| ≤ η|y − x|` for `|y − x| < δ`
    obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp (hfL.isLittleO.bound hηpos)
    -- blowup_points with `N = spt Y`: for `0 < λ < λ₀` some `y ∈ M ∩ spt Y` has
    -- `|λ⁻¹(y − x) − w| < s`
    obtain ⟨lam₀, hlam₀, hpts⟩ :=
      Submission.dsmc_att_blowUp_points_of_approxTangent P n R.carrier Y.support x w Q hnull hQ
        hw s hspos
    set lam : ℝ := min (lam₀ / 2) (δ / (2 * C))
    have hlampos : 0 < lam := lt_min (half_pos hlam₀) (div_pos hδ (mul_pos two_pos hCpos))
    obtain ⟨y, ⟨-, hyK⟩, hy⟩ :=
      hpts lam hlampos ((min_le_left _ _).trans_lt (half_lt_self hlam₀))
    -- the secant point `u = λ⁻¹(y − x)`: `|u − w| < s`, `|u| ≤ C` and `|y − x| = λ|u| < δ`
    set u : Euclid P := lam⁻¹ • (y - x) with hu
    have hyx : y - x = lam • u := by rw [hu, smul_inv_smul₀ hlampos.ne']
    have huw : ‖u - w‖ < s := hy
    have huC : ‖u‖ ≤ C := by
      have h1 := norm_le_norm_sub_add u w
      have h2 := huw.trans_le (min_le_left _ _)
      rw [hC]; linarith
    have hyδ : dist y x < δ := by
      rw [dist_eq_norm, hyx, norm_smul, Real.norm_of_nonneg hlampos.le]
      calc lam * ‖u‖ ≤ δ / (2 * C) * C :=
            mul_le_mul (min_le_right _ _) huC (norm_nonneg _)
              (div_pos hδ (mul_pos two_pos hCpos)).le
        _ = δ / 2 := by field_simp
        _ < δ := half_lt_self hδ
    -- `f(y) = y` (`y ∈ spt Y`) and `f(x) = x`, so dividing by `λ > 0`: `|u − Lu| ≤ η|u| ≤ ε/2`
    have hkey : ‖u - L u‖ ≤ ε / 2 := by
      have h := hδf hyδ
      rw [hfix y hyK, hfx, hyx, map_smul, ← smul_sub, norm_smul, norm_smul,
        Real.norm_of_nonneg hlampos.le, mul_left_comm] at h
      calc ‖u - L u‖ ≤ η * ‖u‖ := le_of_mul_le_mul_left h hlampos
        _ ≤ η * C := mul_le_mul_of_nonneg_left huC hηpos.le
        _ = ε / 2 := hηC
    -- `|Lw − w| ≤ |L(w − u)| + |Lu − u| + |u − w| ≤ Bs + ε/2 ≤ ε`
    have hLwu : ‖L w - L u‖ ≤ ‖L‖ * ‖u - w‖ := by
      calc ‖L w - L u‖ = ‖L (w - u)‖ := by rw [map_sub]
        _ ≤ ‖L‖ * ‖w - u‖ := L.le_opNorm _
        _ = ‖L‖ * ‖u - w‖ := by rw [norm_sub_rev]
    calc ‖L w - w‖ = ‖(L w - L u) + (L u - u) + (u - w)‖ := by congr 1; abel
      _ ≤ ‖L w - L u‖ + ‖L u - u‖ + ‖u - w‖ := norm_add₃_le
      _ ≤ ‖L‖ * ‖u - w‖ + ε / 2 + ‖u - w‖ := by rw [norm_sub_rev (L u) u]; linarith
      _ = B * ‖u - w‖ + ε / 2 := by rw [hB]; ring
      _ ≤ B * s + ε / 2 := by linarith [mul_le_mul_of_nonneg_left huw.le hBpos.le]
      _ ≤ ε := by linarith
  -- Step 6: `Z(ω) = ∫_M θ ξ(ω) dHⁿ = Y(ω)`, the integrands agreeing `Hⁿ⌞M`-a.e.
  ext ω
  rw [hZ ω, hR ω, IMRep.action]
  refine integral_congr_ae ?_
  filter_upwards [hgood] with x hx
  obtain ⟨hxK, Q, hQ, hξ⟩ := hx
  -- Step 5 (orient_comp (b)): `ξ(x)(α ∘ Df(x)) = ξ(x)(α)`, and `ω(f(x)) = ω(x)`
  rw [(Submission.dimred_mbl_pf_unitOrientation_comp P n (R.orient x) Q (fderiv ℝ f x) hξ).2
    (hDf x hxK Q hQ), hfix x hxK]

/-- Simon 6.2.24(1), `∂f_#X = f_#∂X`, for a map `f` that is only `C¹` on an open `O ⊇ K`: if
`X = τ(M, θ, ξ)` has `∂X = 0` in `U`, `Hⁿ(M ∖ K) = 0` and
`Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ⟩ dHⁿ`, then `∂Q = 0` in `U`.  Cut `f` off on `O ∩ U` to a `C¹`
map `φ` with `φ = f`, `Dφ = Df` on an open `V ⊇ K` and `φ = id` off a compact `K' ⊆ O ∩ U`.  The
integrands for `f` and `φ` agree on `M ∩ K`, hence `Hⁿ⌞M`-a.e., so `Q` is the push-forward
formula for `φ`, and `∂Q = 0` by the `C¹` push-forward boundary formula. -/
theorem Submission.dimred_mbl_pf_pushforward_boundaryVanishes : ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (X Q : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → R.Represents X → BoundaryVanishes X → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → BoundaryVanishes Q := by
  intro P n U K O R f X Q hU hK hKU hnull hO hKO hf hRX hX hQ
  -- Step 1: cut `f` off on `O ∩ U`: `φ = f`, `Dφ = Df` on an open `V ⊇ K`, `φ = id` off a
  -- compact `K' ⊆ O ∩ U`
  obtain ⟨φ, V, K', -, hKV, hK', hK'OU, hφ, hφf, hφid⟩ :=
    Submission.dimred_mbl_pfb_c1_compact_perturbation P (O ∩ U) K f (hO.inter hU) hK
      (subset_inter hKO hKU) (hf.mono inter_subset_left)
  -- Step 2: `Hⁿ`-a.e. point of `M` lies in `K`, as `Hⁿ(M ∖ K) = 0`
  have hae : ∀ᵐ x ∂μHE[n], x ∈ R.carrier → x ∈ K := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => not_imp.1 hx) hnull
  -- Step 3: `∂Q = 0` by the push-forward boundary formula for `φ`, once
  -- `Q(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ`: the integrands agree on `M ∩ K ⊆ V`
  refine Submission.dpf_pushforward_formula_boundaryVanishes P n U K' X Q R φ hU hRX hK'
    (hK'OU.trans inter_subset_right) hφ hφid (fun ω => ?_) hX
  rw [hQ ω]
  refine setIntegral_congr_ae R.measurableSet_carrier ?_
  filter_upwards [hae] with x hxK hxM
  obtain ⟨h1, h2⟩ := hφf x (hKV (hxK hxM))
  rw [h1, h2]
/-- **A common Borel orientation for countably many integer multiplicity pieces** (countable
form of the orientation argument behind Simon Ch. 6, Remark 3.2(1); chapter-06.txt lines
733–756, with Ch. 3, 1.4–1.5, chapter-03.txt lines 77–89).  Let `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` be
`IMRep`s in an open `U` whose union `N = ⋃ᵢ Mᵢ` is locally `Hⁿ`-finite in `U`.  Then there are
a Borel `η` and Borel signs `sᵢ = ±1` such that, for `Hⁿ`-a.e. `x ∈ N`, `η(x)` orients an
approximate tangent space of `N` at `x`, and `ξᵢ = sᵢ η` for `Hⁿ`-a.e. `x ∈ Mᵢ`.

Proof sketch:
* Replace `ξᵢ` by a Borel `ξ'ᵢ` with `ξ'ᵢ = ξᵢ` `Hⁿ`-a.e. on `Mᵢ`, and disjointify the
  carriers: `Dᵢ = Mᵢ \ ⋃_{j<i} Mⱼ`.
* `η = Σᵢ 1_{Dᵢ} ξ'ᵢ` equals `ξ'ⱼ` on `Dⱼ` and `0` off `N`; it is Borel as the pointwise limit
  of the finite-stage approximants `gₖ₊₁ = ξ'ₖ` on `Dₖ`, `gₖ₊₁ = gₖ` elsewhere.
* Tangent transfer for `Mⱼ ⊆ N`: `Hⁿ`-a.e. on `N`, for every `j` with `x ∈ Mⱼ`, `ξ'ⱼ(x)`
  orients an approximate tangent space of `N` at `x`.
* Approximate tangent spaces are unique (Remark 1.5(1)), so `η(x)` and every `ξ'ᵢ(x)` with
  `x ∈ Mᵢ` orient the same `TₓN`, and the sign rule gives `ξ'ᵢ(x) = ±η(x)`.  With `sᵢ = 1`
  where `ξ'ᵢ = η` and `sᵢ = -1` elsewhere, `ξᵢ = ξ'ᵢ = sᵢ η` `Hⁿ`-a.e. on `Mᵢ`. -/
theorem Submission.cmcdt_ims_common_orientation : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] ((⋃ i, (R i).carrier) ∩ K) ≠ ∞) → ∃ (η : Euclid P → MultiVector P n) (s : ℕ → Euclid P → ℝ), StronglyMeasurable η ∧ (∀ i, Measurable (s i)) ∧ (∀ i x, s i x = 1 ∨ s i x = -1) ∧ (∀ᵐ x ∂(μHE[n].restrict (⋃ i, (R i).carrier)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (⋃ i, (R i).carrier) x Q ∧ IsUnitOrientationOf (η x) Q) ∧ ∀ i, ∀ᵐ x ∂(μHE[n].restrict (R i).carrier), (R i).orient x = s i x • η x := by
  intro P n U R hU hfin
  classical
  set M : ℕ → Set (Euclid P) := fun i => (R i).carrier with hMdef
  set N : Set (Euclid P) := ⋃ i, M i with hNdef
  have hMmeas : ∀ i, MeasurableSet (M i) := fun i => (R i).measurableSet_carrier
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion hMmeas
  have hNU : N ⊆ U := iUnion_subset fun i => (R i).carrier_subset
  -- Borel versions `ξ'ᵢ` of the orientations, `ξ'ᵢ = ξᵢ` a.e. on `Mᵢ`
  set ξ' : ℕ → Euclid P → MultiVector P n :=
    fun i => (R i).aestronglyMeasurable_orient.mk (R i).orient
  have hξ'sm : ∀ i, StronglyMeasurable (ξ' i) :=
    fun i => (R i).aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξ'ae : ∀ i, ∀ᵐ x ∂(μHE[n].restrict (M i)), (R i).orient x = ξ' i x :=
    fun i => (R i).aestronglyMeasurable_orient.ae_eq_mk
  -- the disjoint pieces `Dᵢ = Mᵢ \ ⋃_{j<i} Mⱼ`
  set D : ℕ → Set (Euclid P) := disjointed M with hDdef
  have hDmeas : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hMmeas
  have hDsub : ∀ i, D i ⊆ M i := disjointed_subset M
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed M
  have hDunion : ⋃ i, D i = N := iUnion_disjointed
  -- the reference orientation `η = Σᵢ 1_{Dᵢ} ξ'ᵢ`: `η = ξ'ⱼ` on `Dⱼ`, `η = 0` off `N`
  set η : Euclid P → MultiVector P n := fun x => ∑' i, (D i).indicator (ξ' i) x with hηdef
  have hη_eq : ∀ j x, x ∈ D j → η x = ξ' j x := by
    intro j x hx
    simp only [hηdef]
    rw [tsum_eq_single j]
    · exact indicator_of_mem hx _
    · intro i hij
      exact indicator_of_notMem (fun hxi => (hDdisj hij).ne_of_mem hxi hx rfl) _
  have hη_zero : ∀ x, (∀ i, x ∉ D i) → η x = 0 := by
    intro x hx
    simp only [hηdef]
    have h0 : ∀ i, (D i).indicator (ξ' i) x = 0 := fun i => indicator_of_notMem (hx i) _
    simp [h0]
  -- `MultiVector P n` is metrizable: its operator-norm topology is the strong topology
  have hmetr : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
    { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
        Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
      toT0Space := inferInstance }
  -- finite-stage approximants `gₖ₊₁ = ξ'ₖ` on `Dₖ`, `gₖ₊₁ = gₖ` elsewhere (`ite` only)
  let g : ℕ → Euclid P → MultiVector P n := fun k => Nat.rec (fun _ => 0)
    (fun j gj => fun x => if x ∈ D j then ξ' j x else gj x) k
  have hg_succ : ∀ k x, g (k + 1) x = if x ∈ D k then ξ' k x else g k x := fun k x => rfl
  have hg_sm : ∀ k, StronglyMeasurable (g k) := by
    intro k
    induction k with
    | zero => exact stronglyMeasurable_const
    | succ k ih =>
      have : g (k + 1) = fun x => if x ∈ D k then ξ' k x else g k x := funext (hg_succ k)
      rw [this]
      exact StronglyMeasurable.ite (hDmeas k) (hξ'sm k) ih
  have hg_eq : ∀ k x, (∀ i, i < k → x ∉ D i) → g k x = 0 := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [hg_succ, ite_eq_right (hx k (Nat.lt_succ_self k))]
      exact ih x fun i hi => hx i (Nat.lt_succ_of_lt hi)
  have hg_mem : ∀ j x, x ∈ D j → ∀ k, j < k → g k x = ξ' j x := by
    intro j x hj k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      rw [hg_succ]
      by_cases hjk : j = k
      · subst hjk; rw [ite_eq_left hj]
      · have hxk : x ∉ D k := fun hxk => (hDdisj (Ne.symm hjk)).ne_of_mem hxk hj rfl
        rw [ite_eq_right hxk]
        exact ih (by omega)
  -- `gₖ → η` pointwise, so `η` is Borel
  have hη_sm : StronglyMeasurable η := by
    refine stronglyMeasurable_of_tendsto atTop hg_sm ?_
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : ∃ j, x ∈ D j
    · obtain ⟨j, hj⟩ := hx
      apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
      intro k hk
      rw [hη_eq j x hj]
      exact hg_mem j x hj k (by omega)
    · have hx' : ∀ i, x ∉ D i := fun i hi => hx ⟨i, hi⟩
      rw [hη_zero x hx']
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro k _
      exact hg_eq k x fun i _ => hx' i
  -- the signs `sᵢ = 1` where `ξ'ᵢ = η`, `sᵢ = -1` elsewhere
  set s : ℕ → Euclid P → ℝ := fun i x => if ξ' i x = η x then 1 else -1 with hsdef
  have hs_meas : ∀ i, Measurable (s i) := fun i =>
    Measurable.ite ((hξ'sm i).measurableSet_eq_fun hη_sm) measurable_const measurable_const
  have hs_val : ∀ i x, s i x = 1 ∨ s i x = -1 := by
    intro i x
    by_cases h : ξ' i x = η x
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  -- tangent transfer for `Mⱼ ⊆ N`: a.e. on `Mⱼ`, `ξ'ⱼ(x)` orients a tangent space of `N`
  have hP : ∀ j, ∀ᵐ x ∂(μHE[n].restrict (M j)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    intro j
    have h1 := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M j) N (R j) hU
      (hMmeas j) hNmeas subset_rfl (subset_iUnion M j) hNU hfin
    filter_upwards [h1, hξ'ae j] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx1
    exact ⟨Q, hQ1, hx2 ▸ hQ2⟩
  -- the same, for every `j` at once, `Hⁿ`-a.e. on `N`
  have hPN : ∀ᵐ x ∂(μHE[n].restrict N), ∀ j, x ∈ M j → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    rw [ae_all_iff]
    intro j
    exact ae_restrict_of_ae ((ae_restrict_iff' (hMmeas j)).mp (hP j))
  -- uniqueness of `TₓN` and the sign rule: `η(x)` orients `TₓN`, `ξ'ᵢ(x) = ±η(x)` on `Mᵢ`
  have hgood : ∀ᵐ x ∂(μHE[n].restrict N), (∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) ∧
      ∀ i, x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) := by
    filter_upwards [hPN, ae_restrict_mem hNmeas] with x hx hxN
    rw [← hDunion] at hxN
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxN
    obtain ⟨Qj, hQj1, hQj2⟩ := hx j (hDsub j hj)
    rw [← hη_eq j x hj] at hQj2
    refine ⟨⟨Qj, hQj1, hQj2⟩, fun i hi => ?_⟩
    obtain ⟨Qi, hQi1, hQi2⟩ := hx i hi
    rw [hQi1.unique hQj1] at hQi2
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (η x) (ξ' i x) Qj hQj2 hQi2
  refine ⟨η, s, hη_sm, hs_meas, hs_val, hgood.mono fun x hx => hx.1, fun i => ?_⟩
  -- `ξᵢ = ξ'ᵢ = sᵢ η` a.e. on `Mᵢ ⊆ N`
  have hgoodi : ∀ᵐ x ∂(μHE[n].restrict (M i)), x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) :=
    ae_restrict_of_ae_restrict_of_subset (subset_iUnion M i) (hgood.mono fun x hx => hx.2 i)
  filter_upwards [hgoodi, ae_restrict_mem (hMmeas i), hξ'ae i] with x hx hxM hxe
  rw [hxe]
  by_cases h : ξ' i x = η x
  · rw [show s i x = 1 from ite_eq_left h, one_smul, h]
  · rw [show s i x = -1 from ite_eq_right h, (hx hxM).resolve_left h]
    exact (neg_one_smul ℝ (η x)).symm
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

/-- A countable family of integer multiplicity triples `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` in `U` with
`Σᵢ μ_{Rᵢ}(U) < ∞` is summed by one triple `R'`: `Σᵢ Rᵢ(ω) = R'(ω)` for every `ω ∈ 𝒟ⁿ(U)`.
On `N = ⋃ᵢ Mᵢ` take a common orientation `η` with `ξᵢ = sᵢ η` a.e. on `Mᵢ` (`sᵢ = ±1`); `R'`
represents `ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ` for the integer density `m = Σᵢ sᵢ θᵢ 1_{Mᵢ}`, and the series
converges by dominated convergence, as `|m| ≤ Θ := Σᵢ θᵢ 1_{Mᵢ}` and `∫ Θ dHⁿ = Σᵢ μ_{Rᵢ}(U)`. -/
theorem Submission.cmcdt_ims_imrep_tsum : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → ∑' i, (R i).measure U ≠ ∞ → ∃ R' : IMRep U n, ∀ ω : TestFormOn U n, HasSum (fun i => (R i).action (ω : DifferentialForm (Euclid P) n)) (R'.action (ω : DifferentialForm (Euclid P) n)) := by
  intro P n U R hU hA
  classical
  set M : ℕ → Set (Euclid P) := fun i => (R i).carrier
  set N : Set (Euclid P) := ⋃ i, M i
  have hMmeas : ∀ i, MeasurableSet (M i) := fun i => (R i).measurableSet_carrier
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion hMmeas
  have hNU : N ⊆ U := iUnion_subset fun i => (R i).carrier_subset
  -- Step 1: `Θᵢ = θᵢ 1_{Mᵢ}` has `∫ Θᵢ dHⁿ = μ_{Rᵢ}(U)`, so `Θ = Σᵢ Θᵢ` has finite integral
  set Θi : ℕ → Euclid P → ℝ≥0∞ := fun i => (M i).indicator (fun y => ((R i).mult y : ℝ≥0∞))
    with hΘidef
  have hΘi_meas : ∀ i, Measurable (Θi i) := fun i =>
    (measurable_from_nat.comp (R i).measurable_mult).indicator (hMmeas i)
  have hΘi_ne_top : ∀ i x, Θi i x ≠ ∞ := by
    intro i x
    simp only [hΘidef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx]; exact ENNReal.natCast_ne_top _
    · rw [indicator_of_notMem hx]; exact ENNReal.zero_ne_top
  have hmeasU : ∀ i, (R i).measure U = ∫⁻ x, Θi i x ∂μHE[n] := by
    intro i
    simp only [IMRep.measure, hΘidef]
    rw [withDensity_apply _ hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
      inter_eq_right.mpr (R i).carrier_subset, lintegral_indicator (hMmeas i)]
  set Θ : Euclid P → ℝ≥0∞ := fun x => ∑' i, Θi i x with hΘdef
  have hΘ_meas : Measurable Θ := Measurable.tsum hΘi_meas
  have hΘ_int : ∫⁻ x, Θ x ∂μHE[n] = ∑' i, (R i).measure U := by
    rw [lintegral_tsum (fun i => (hΘi_meas i).aemeasurable)]
    simp_rw [hmeasU]
  have hΘ_fin : ∫⁻ x, Θ x ∂μHE[n] ≠ ∞ := hΘ_int ▸ hA
  -- Step 2: `Hⁿ(N) ≤ Σᵢ μ_{Rᵢ}(U)`, as `θᵢ ≥ 1` on `Mᵢ`
  have hN_le : μHE[n] N ≤ ∑' i, (R i).measure U := by
    refine (measure_iUnion_le M).trans (ENNReal.tsum_le_tsum fun i => ?_)
    rw [hmeasU i, hΘidef]
    simp only
    rw [lintegral_indicator (hMmeas i), ← setLIntegral_one]
    refine setLIntegral_mono' (hMmeas i) fun x hx => ?_
    have := (R i).mult_pos x hx
    exact_mod_cast this
  have hNfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞ := by
    intro K _ _
    exact ne_top_of_le_ne_top hA ((measure_mono inter_subset_left).trans hN_le)
  -- Step 3: the common orientation `η` of `N`, with `ξᵢ = sᵢ η` a.e. on `Mᵢ`
  obtain ⟨η, s, hη, hs_meas, hs_val, hor, hrel⟩ :=
    Submission.cmcdt_ims_common_orientation P n U R hU hNfin
  -- Step 4: the integer density `m = Σᵢ aᵢ`, `aᵢ = sᵢ θᵢ 1_{Mᵢ}`, with `|m| ≤ Θ`
  set a : ℕ → Euclid P → ℝ := fun i => (M i).indicator (fun y => s i y * ((R i).mult y : ℝ))
    with hadef
  have ha_meas : ∀ i, Measurable (a i) := fun i =>
    ((hs_meas i).mul (measurable_from_nat.comp (R i).measurable_mult)).indicator (hMmeas i)
  have ha_norm : ∀ i x, ‖a i x‖ = (Θi i x).toReal := by
    intro i x
    simp only [hadef, hΘidef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      rcases hs_val i x with h | h <;> simp [h]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  have ha_enorm : ∀ i x, ‖a i x‖ₑ = Θi i x := by
    intro i x
    rw [← ofReal_norm, ha_norm, ENNReal.ofReal_toReal (hΘi_ne_top i x)]
  have ha_int : ∀ i x, ∃ z : ℤ, a i x = z := by
    intro i x
    simp only [hadef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx]
      rcases hs_val i x with h | h
      · exact ⟨(R i).mult x, by simp [h]⟩
      · exact ⟨-((R i).mult x : ℤ), by simp [h]⟩
    · exact ⟨0, by simp [indicator_of_notMem hx]⟩
  choose z hz using ha_int
  set m : Euclid P → ℝ := fun x => ∑' i, a i x with hmdef
  have hm_meas : Measurable m := Measurable.tsum ha_meas
  -- a summable series of integers has finitely many nonzero terms; `m = 0` if not summable
  have hm_int : ∀ x, ∃ k : ℤ, m x = k := by
    intro x
    by_cases hsum : Summable (fun i => a i x)
    · have hfin : {i | a i x ≠ 0}.Finite := by
        have ht := hsum.tendsto_cofinite_zero
        have hev : ∀ᶠ i in cofinite, a i x ∈ ball (0 : ℝ) 1 := ht (ball_mem_nhds 0 one_pos)
        refine (Filter.eventually_cofinite.mp hev).subset fun i hi => ?_
        simp only [mem_ofPred_eq, mem_ball, dist_zero_right] at hi ⊢
        intro hlt
        apply hi
        rw [hz i x] at hlt ⊢
        have : z i x = 0 := by
          rw [Real.norm_eq_abs] at hlt
          have h1 : |(z i x : ℝ)| < 1 := hlt
          have h2 : |z i x| < 1 := by exact_mod_cast h1
          exact Int.abs_lt_one_iff.mp h2
        simp [this]
      refine ⟨∑ i ∈ hfin.toFinset, z i x, ?_⟩
      simp only [hmdef]
      rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => by simpa using hi)]
      push_cast
      exact Finset.sum_congr rfl fun i _ => hz i x
    · exact ⟨0, by simp [hmdef, tsum_eq_zero_of_not_summable hsum]⟩
  have hm_le : ∀ x, ‖m x‖ₑ ≤ Θ x := by
    intro x
    calc ‖m x‖ₑ ≤ ∑' i, ‖a i x‖ₑ := enorm_tsum_le_tsum_enorm
      _ = Θ x := by simp only [hΘdef, ha_enorm]
  have hloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top hΘ_fin ?_
    exact (setLIntegral_le_lintegral _ _).trans (lintegral_mono hm_le)
  have hrect : CountablyRectifiable n N :=
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M fun i => (R i).rectifiable
  -- Step 5: the triple `(N, m, η)` gives `R'` with `R'(ω) = ∫_N m ⟨ω, η⟩ dHⁿ`
  obtain ⟨R', hR'⟩ := Submission.cmcdt_ims_imrep_of_int_density P n U N η m hU hNmeas hNU hrect
    hNfin hη hm_meas hm_int hloc hor
  refine ⟨R', fun ω => ?_⟩
  -- Step 6: dominated convergence for the series `Σᵢ aᵢ ⟨ω, η⟩`, dominated by `B Θᵢ`
  have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨B, hB⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
  have hev_sm : StronglyMeasurable (fun x => η x ((ω : DifferentialForm (Euclid P) n) x)) := by
    have hcont : Continuous (fun p : MultiVector P n × Euclid P =>
        p.1 ((ω : DifferentialForm (Euclid P) n) p.2)) :=
      isBoundedBilinearMap_apply.continuous.comp (continuous_fst.prodMk (hωc.comp continuous_snd))
    exact hcont.comp_stronglyMeasurable (hη.prodMk stronglyMeasurable_id)
  set F : ℕ → Euclid P → ℝ := fun i x => a i x * η x ((ω : DifferentialForm (Euclid P) n) x)
    with hFdef
  set bound : ℕ → Euclid P → ℝ := fun i x => B * (Θi i x).toReal with hbounddef
  have hF_sm : ∀ i, AEStronglyMeasurable (F i) (μHE[n].restrict N) := fun i =>
    ((ha_meas i).stronglyMeasurable.mul hev_sm).aestronglyMeasurable
  have hηnorm : ∀ᵐ x ∂(μHE[n].restrict N), ‖η x‖ ≤ 1 := by
    filter_upwards [hor] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q (η x) hQ
  have hF_le : ∀ i, ∀ᵐ x ∂(μHE[n].restrict N), ‖F i x‖ ≤ bound i x := by
    intro i
    filter_upwards [hηnorm] with x hx
    simp only [hFdef, hbounddef, norm_mul, ha_norm]
    have h1 : ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤ B := by
      calc ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖
          ≤ ‖η x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (η x).le_opNorm _
        _ ≤ 1 * B := mul_le_mul hx (hB x) (norm_nonneg _) zero_le_one
        _ = B := one_mul B
    calc (Θi i x).toReal * ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖
        ≤ (Θi i x).toReal * B := mul_le_mul_of_nonneg_left h1 ENNReal.toReal_nonneg
      _ = B * (Θi i x).toReal := mul_comm _ _
  have hΘ_lt : ∀ᵐ x ∂(μHE[n].restrict N), Θ x < ∞ :=
    ae_restrict_of_ae (ae_lt_top hΘ_meas hΘ_fin)
  have hsumΘ : ∀ x, Θ x < ∞ → Summable (fun i => (Θi i x).toReal) :=
    fun x hx => ENNReal.summable_toReal hx.ne
  have hbound_sum : ∀ᵐ x ∂(μHE[n].restrict N), Summable (fun i => bound i x) := by
    filter_upwards [hΘ_lt] with x hx
    exact (hsumΘ x hx).mul_left B
  have hbound_int : Integrable (fun x => ∑' i, bound i x) (μHE[n].restrict N) := by
    have hmeas : Measurable (fun x => ∑' i, bound i x) :=
      Measurable.tsum fun i => measurable_const.mul (hΘi_meas i).ennreal_toReal
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hle : ∀ x, ‖∑' i, bound i x‖ₑ ≤ ‖B‖ₑ * Θ x := by
      intro x
      calc ‖∑' i, bound i x‖ₑ ≤ ∑' i, ‖bound i x‖ₑ := enorm_tsum_le_tsum_enorm
        _ = ∑' i, ‖B‖ₑ * Θi i x := by
            congr 1; funext i
            simp only [hbounddef]
            rw [enorm_mul, ← ofReal_norm (Θi i x).toReal, Real.norm_eq_abs,
              abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hΘi_ne_top i x)]
        _ = ‖B‖ₑ * Θ x := ENNReal.tsum_mul_left
    calc ∫⁻ x, ‖∑' i, bound i x‖ₑ ∂(μHE[n].restrict N)
        ≤ ∫⁻ x, ‖B‖ₑ * Θ x ∂(μHE[n].restrict N) := lintegral_mono hle
      _ = ‖B‖ₑ * ∫⁻ x, Θ x ∂(μHE[n].restrict N) := lintegral_const_mul _ hΘ_meas
      _ ≤ ‖B‖ₑ * ∫⁻ x, Θ x ∂μHE[n] := by gcongr; exact Measure.restrict_le_self
      _ < ∞ := ENNReal.mul_lt_top enorm_lt_top hΘ_fin.lt_top
  have hF_sum : ∀ᵐ x ∂(μHE[n].restrict N),
      HasSum (fun i => F i x) (m x * η x ((ω : DifferentialForm (Euclid P) n) x)) := by
    filter_upwards [hΘ_lt] with x hx
    have hs : Summable (fun i => a i x) :=
      Summable.of_norm_bounded (hsumΘ x hx) fun i => (ha_norm i x).le
    exact hs.hasSum.mul_right _
  have hmain :=
    hasSum_integral_of_dominated_convergence bound hF_sm hF_le hbound_sum hbound_int hF_sum
  -- Step 7: `∫_N Fᵢ dHⁿ = Rᵢ(ω)`, as `ξᵢ = sᵢ η` a.e. on `Mᵢ ⊆ N`
  have hterm : ∀ i, ∫ x, F i x ∂(μHE[n].restrict N) =
      (R i).action (ω : DifferentialForm (Euclid P) n) := by
    intro i
    have h1 : ∀ᵐ x ∂(μHE[n].restrict (M i)),
        ((R i).mult x : ℝ) * (R i).orient x ((ω : DifferentialForm (Euclid P) n) x) =
          s i x * ((R i).mult x : ℝ) * η x ((ω : DifferentialForm (Euclid P) n) x) := by
      filter_upwards [hrel i] with x hx
      rw [hx, smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ x, F i x = (M i).indicator (fun y => s i y * ((R i).mult y : ℝ) *
        η y ((ω : DifferentialForm (Euclid P) n) y)) x := by
      intro x
      simp only [hFdef, hadef]
      by_cases hx : x ∈ M i
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    simp only [IMRep.action]
    rw [setIntegral_congr_ae (hMmeas i) ((ae_restrict_iff' (hMmeas i)).mp h1)]
    simp_rw [h2]
    rw [setIntegral_indicator (hMmeas i), inter_eq_right.mpr (subset_iUnion M i)]
  simp_rw [hterm] at hmain
  rw [hR' (ω : DifferentialForm (Euclid P) n)]
  exact hmain

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
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
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
/-- Steps 3(ii)–(iii) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3,
via Allard's theorem): if `τ` is an orthonormal `n`-frame whose span contains every `F eⱼ`, then
`det(F* ∘ F) = (det 𝒜)²` with `𝒜ᵢⱼ = ⟨τᵢ, F eⱼ⟩`.  Expanding `F eⱼ = Σₗ 𝒜ₗⱼ τₗ` gives the Gram
identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`, and the Gram matrix is the matrix of `F* ∘ F` in the standard
basis of `ℝⁿ`. -/
theorem Submission.dgoj_det_adjoint_comp_eq_det_sq : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ)) → (F.adjoint ∘L F).det = (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det ^ 2 := by
  intro P n F τ hτ hb
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ))) with hA
  -- `F eⱼ = Σₗ 𝒜ₗⱼ τₗ`: the coordinates of a vector of `span τ` are its inner products with `τ`
  have hexp : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) = ∑ l, A l j • τ l := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hb j)
    have hcA : ∀ l, A l j = c l := by
      intro l
      rw [hA, Matrix.of_apply, ← hc, hτ.inner_right_fintype]
    rw [← hc]
    simp only [hcA]
  -- the Gram identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`
  have hgram : ∀ i j, inner ℝ (F (EuclideanSpace.single i (1 : ℝ)))
      (F (EuclideanSpace.single j (1 : ℝ))) = (A.transpose * A) i j := by
    intro i j
    rw [Matrix.mul_apply]
    conv_lhs => rw [hexp i]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, Matrix.transpose_apply]
    simp [hA]
  -- the matrix of `F* ∘ F` in the standard basis has entries `⟨eᵢ, F* F eⱼ⟩ = ⟨F eᵢ, F eⱼ⟩`
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmat : LinearMap.toMatrix B B ((F.adjoint ∘L F : Euclid n →L[ℝ] Euclid n) : Euclid n →ₗ[ℝ] Euclid n)
      = A.transpose * A := by
    ext i j
    rw [LinearMap.toMatrix_apply, ← hgram i j]
    simp only [B, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_single_left]
    simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, hmat, Matrix.det_mul,
    Matrix.det_transpose, sq]
/-- Step 3 of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem): if `F : ℝⁿ → ℝᴾ` is injective, its range `L` has an orthonormal basis
`τ = (τ₁, …, τₙ)`, regarded as an orthonormal `n`-frame in `ℝᴾ` spanning `L`.  Since
`dim L = n`, reindex `stdOrthonormalBasis ℝ L` along `Fin (dim L) ≃ Fin n` and include it into
`ℝᴾ` by the linear isometry `L → ℝᴾ`. -/
theorem Submission.dgoj_exists_orthonormal_frame_range : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (Set.range τ) = LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) := by
  intro P n F hF
  set L := LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) with hLdef
  -- `dim L = dim ℝⁿ = n`, since `F` is injective
  have hL : Module.finrank ℝ L = n := by
    rw [hLdef, LinearMap.finrank_range_of_inj hF, finrank_euclideanSpace_fin]
  let T : OrthonormalBasis (Fin n) ℝ L := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  refine ⟨fun i => (T i : Euclid P), ?_, ?_⟩
  · -- the inclusion `L → ℝᴾ` is a linear isometry
    exact T.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  · -- `span (ι '' range T) = ι '' span (range T) = ι '' L = L`
    have h1 : (fun i => (T i : Euclid P)) = L.subtype ∘ T := rfl
    rw [h1, Set.range_comp, Submodule.span_image, ← T.coe_toBasis, T.toBasis.span_eq,
      Submodule.map_top, Submodule.range_subtype]

/-- **The normalized evaluation at `F e` is a unit orientation of `range F`** (Simon 6.1.1,
6.1.7; `√det(F* ∘ F)` is the area Jacobian of Ch. 2, 3.1/3.3).  For injective `F : ℝⁿ → ℝᴾ`,
`det(F* ∘ F) > 0`, and if `α(F e₁, …, F eₙ) = √det(F* ∘ F) ξ(α)` for every `n`-covector `α` then
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal frame `τ` of `range F`: with `d = det(⟨τᵢ, F eⱼ⟩)` one has
`det(F* ∘ F) = d² ≠ 0` and `α(F e) = d α(τ)`, so `|d| ξ(α) = d α(τ)` and the sign is that of `d`. -/
theorem Submission.dgoj_unitOrientation_of_injective : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → 0 < (F.adjoint ∘L F).det ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, α (fun i => F (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt ((F.adjoint ∘L F).det) * ξ α) → IsUnitOrientationOf ξ (LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F hF
  -- an orthonormal frame `τ` of `range F`; every `F eⱼ` lies in its span
  obtain ⟨τ, hτo, hτs⟩ := Submission.dgoj_exists_orthonormal_frame_range P n F hF
  have hb : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ) := by
    intro j
    rw [hτs]
    exact LinearMap.mem_range_self _ _
  -- `det(F* ∘ F) = d²` for `d = det(⟨τᵢ, F eⱼ⟩)`
  set d := (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det
  have hdet : (F.adjoint ∘L F).det = d ^ 2 :=
    Submission.dgoj_det_adjoint_comp_eq_det_sq P n F τ hτo hb
  -- `ker(F* ∘ F) = ker F = 0`, so `det(F* ∘ F) ≠ 0` and hence `d ≠ 0`
  have hd : d ≠ 0 := by
    intro h
    have h0 : (F.adjoint ∘L F).det = 0 := by rw [hdet, h, zero_pow two_ne_zero]
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0
    rw [F.ker_adjoint_comp_self, LinearMap.ker_eq_bot]
    exact hF
  -- (i): `det(F* ∘ F) = d² > 0`
  refine ⟨by rw [hdet]; positivity, fun ξ hξ => ⟨τ, hτo, hτs, ?_⟩⟩
  -- (ii): `|d| ξ(α) = √det(F* ∘ F) ξ(α) = α(F e) = d α(τ)` for every `α`
  have key : ∀ α : Covector (Euclid P) n, |d| * ξ α = d * α τ := by
    intro α
    rw [← Real.sqrt_sq_eq_abs, ← hdet, ← hξ α]
    exact Submission.dgoj_covector_eq_det_mul_of_mem_span P n τ _ hτo hb α
  -- the sign of `d` decides between `ξ(α) = -α(τ)` and `ξ(α) = α(τ)`
  rcases hd.lt_or_gt with hneg | hpos
  · right
    intro α
    have h := key α
    rw [abs_of_neg hneg] at h
    apply mul_left_cancel₀ hd
    linarith
  · left
    intro α
    have h := key α
    rw [abs_of_pos hpos] at h
    exact mul_left_cancel₀ hd h
/-- `C¹` cutoff near a compact set: if `K ⊆ O ⊆ ℝᴾ`, `K` compact, `O` open and `f` is `C¹` on `O`,
then `g = χ • f` is `C¹` on `ℝᴾ` and globally Lipschitz, and `g = f`, `Dg = Df` on `K`.  Here `χ` is
a smooth Urysohn function, `χ = 1` on `cthickening (δ/3) K` and `support χ = thickening (2δ/3) K`
for `cthickening δ K ⊆ O`, so `g = f` near `K` and `g = 0` off the compact `tsupport χ ⊆ O`;
`Dg` is continuous with compact support, hence bounded, and the mean value inequality applies. -/
theorem Submission.dimred_mbl_pfi_c1_lipschitz_cutoff : ∀ (P : ℕ) (K O : Set (Euclid P)) (f : Euclid P → Euclid P), IsCompact K → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (g : Euclid P → Euclid P) (L : NNReal), ContDiff ℝ 1 g ∧ LipschitzWith L g ∧ ∀ x ∈ K, g x = f x ∧ fderiv ℝ g x = fderiv ℝ f x := by
  intro P K O f hK hO hKO hf
  classical
  -- Step 1: room around `K` and a smooth Urysohn function `χ` with `tsupport χ ⊆ O` compact
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hts : cthickening (δ / 3) K ⊆ thickening (2 * δ / 3) K :=
    cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    isOpen_thickening isClosed_cthickening hts
  have hcl : tsupport χ ⊆ cthickening (2 * δ / 3) K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  have hclO : tsupport χ ⊆ O := hcl.trans ((cthickening_mono (by linarith) K).trans hδO)
  have hχc : HasCompactSupport χ :=
    (hK.cthickening (r := 2 * δ / 3)).of_isClosed_subset (isClosed_tsupport _) hcl
  -- Step 2: `g = χ • f` is `C¹` at points of `O` (product rule) and off `O` (`g = 0` nearby)
  set g : Euclid P → Euclid P := fun x => χ x • f x with hgdef
  have hgC1 : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact (hχ.contDiffAt.of_le (by exact_mod_cast le_top)).smul (hf.contDiffAt (hO.mem_nhds hx))
    · have hnx : (tsupport χ)ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds (fun h => hx (hclO h))
      apply (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq
      filter_upwards [hnx] with y hy
      simp [hgdef, image_eq_zero_of_notMem_tsupport hy]
  -- Step 3: `g = f` on the open set `thickening (δ/3) K ⊇ K`, where `χ = 1`
  have hgK : ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
    intro x hx
    have hmem : thickening (δ / 3) K ∈ 𝓝 x :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by positivity) K hx)
    filter_upwards [hmem] with y hy
    have h1 : χ y = 1 := (hχ1 y).1 (thickening_subset_cthickening _ _ hy)
    simp [hgdef, h1]
  -- Step 4: `Dg` is continuous with compact support, hence bounded; mean value inequality
  have hgc : HasCompactSupport g := hχc.smul_right
  obtain ⟨C, hC⟩ := hgc.fderiv (𝕜 := ℝ) |>.exists_bound_of_continuous
    (hgC1.continuous_fderiv one_ne_zero)
  refine ⟨g, (max C 0).toNNReal, hgC1, ?_, fun x hx =>
    ⟨(hgK x hx).eq_of_nhds, (hgK x hx).fderiv_eq⟩⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hgC1.differentiable one_ne_zero) (fun x => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hC x).trans (le_max_left _ _)
/-- **The image of a weighted bi-Lipschitz piece is an integer multiplicity current** (one image
piece of the integrality of push-forwards, Simon Ch. 6, 3.3–3.9, via the area formula of Ch. 2).
Let `U` be open, `H : ℝⁿ → ℝᴾ` Lipschitz, `B` Borel with `m|a − a'| ≤ |H(a) − H(a')|` on `B`,
`DH(a)` injective for `a ∈ B` and `H(B) ⊆ U`; let `w ≥ 1` on `B` be integer-valued and
`ζ(a) = ±DH(a)_# e` for a.e. `a ∈ B`, with `∫_B w J < ∞`, `J = √det(DH* ∘ DH)`.  Then
`(H(B), w ∘ (H|_B)⁻¹, (J⁻¹ ζ) ∘ (H|_B)⁻¹)` is an integer multiplicity triple in `U` of mass
`∫_B w J` acting by `ω ↦ ∫_B w ⟨ω(H(a)), ζ(a)⟩ da`.  `H(B)` is Borel (Lusin–Souslin), the area
formula transports `Hⁿ⌞H(B)` to `J Lⁿ⌞B`, and for a.e. `a ∈ B` the approximate tangent space of
`H(B)` at `H(a)` is `range DH(a)`, oriented by `±DH(a)_# e / J(a)`. -/
theorem Submission.dimred_mbl_pfi_bilipschitz_piece_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ) (w : Euclid n → ℕ) (ζ : Euclid n → MultiVector P n), IsOpen U → LipschitzWith L H → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → H '' B ⊆ U → Measurable w → (∀ a ∈ B, 1 ≤ w a) → AEStronglyMeasurable ζ (volume.restrict B) → (∀ᵐ a ∂(volume.restrict B), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, ζ a α = s * α (fun j => fderiv ℝ H a (EuclideanSpace.single j (1 : ℝ)))) → ∫⁻ a in B, (w a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ H a).adjoint ∘L fderiv ℝ H a).det)) ∂volume ≠ ∞ → ∃ R : IMRep U n, R.measure U = ∫⁻ a in B, (w a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ H a).adjoint ∘L fderiv ℝ H a).det)) ∂volume ∧ ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ a in B, (w a : ℝ) * ζ a (ω (H a)) ∂volume := by
  intro P n U H B L m w ζ hU hHL hB hm hlow hdiff hHU hwm hw1 hζm hsign hfin
  classical
  -- Step 1: `H` is injective on `B`; `N = H(B)` is Borel and `H|_B` is a measurable embedding
  have hinj : InjOn H B := by
    intro a ha a' ha' h
    have h3 : m * ‖a - a'‖ ≤ m * 0 := by simpa [h] using hlow a ha a' ha'
    have h4 : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left h3 hm
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)
  have hcont : ContinuousOn H B := hHL.continuous.continuousOn
  have hNmeas : MeasurableSet (H '' B) := hB.image_of_continuousOn_injOn hcont hinj
  have hemb : MeasurableEmbedding (B.domRestrict H) := hcont.measurableEmbedding hB hinj
  have heinj : Injective (B.domRestrict H) := hinj.injective
  -- Step 2: the Jacobian `J = √det(DH* ∘ DH)` is Borel, and positive on `B`
  set J : Euclid n → ℝ := fun a => Real.sqrt (((fderiv ℝ H a).adjoint ∘L fderiv ℝ H a).det)
    with hJdef
  have hcJ : Continuous (fun A : Euclid n →L[ℝ] Euclid P => Real.sqrt ((A.adjoint ∘L A).det)) := by
    refine Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp ?_)
    exact isBoundedBilinearMap_comp.continuous.comp
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid n) (F := Euclid P)).continuous.prodMk
        continuous_id)
  have hJmeas : Measurable J := hcJ.measurable.comp (measurable_fderiv ℝ H)
  have hJpos : ∀ a ∈ B, 0 < J a := fun a ha =>
    Real.sqrt_pos.2 (Submission.dgoj_unitOrientation_of_injective P n (fderiv ℝ H a) (hdiff a ha).2).1
  have hJarea : ∀ a, Poincare.SimonGMT.Chapter02.areaJacobianAt H a = J a := fun a =>
    Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp H a
  -- Step 3: the area formulas `∫⁻_N g dHⁿ = ∫⁻_B J (g ∘ H)` and `∫_N g dHⁿ = ∫_B J (g ∘ H)`
  have hareaL : ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in H '' B, g y ∂μHE[n] =
      ∫⁻ a in B, ENNReal.ofReal (J a) * g (H a) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_volume_of_injective_derivative
      hB (fun a ha => (hdiff a ha).1) (fun a ha => (hdiff a ha).2) hinj g
    rw [finrank_euclideanSpace_fin] at h
    simpa only [hJarea] using h
  have hareaI : ∀ g : Euclid P → ℝ, ∫ y in H '' B, g y ∂μHE[n] =
      ∫ a in B, J a * g (H a) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
      hB (fun a ha => (hdiff a ha).1) (fun a ha => (hdiff a ha).2) hinj g
    rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume n] at h
    simpa only [hJarea, smul_eq_mul] using h
  -- Step 4: a strongly measurable version `ζ'` of `ζ`
  set ζ' := hζm.mk ζ with hζ'eq
  have hζ'sm : StronglyMeasurable ζ' := hζm.stronglyMeasurable_mk
  have hζ'ae : ζ =ᵐ[volume.restrict B] ζ' := hζm.ae_eq_mk
  -- Step 5: `mult = w ∘ (H|_B)⁻¹` and `orient = (J⁻¹ ζ') ∘ (H|_B)⁻¹` on `N`, `0` off `N`
  set mult : Euclid P → ℕ := Function.extend (B.domRestrict H) (fun a : B => w a) 0 with hmultdef
  set orient : Euclid P → MultiVector P n :=
    Function.extend (B.domRestrict H) (fun a : B => (J a)⁻¹ • ζ' a) 0 with horientdef
  have hmult_apply : ∀ a ∈ B, mult (H a) = w a := fun a ha =>
    heinj.extend_apply (fun a : B => w a) 0 ⟨a, ha⟩
  have horient_apply : ∀ a ∈ B, orient (H a) = (J a)⁻¹ • ζ' a := fun a ha =>
    heinj.extend_apply (fun a : B => (J a)⁻¹ • ζ' a) 0 ⟨a, ha⟩
  have hmult_meas : Measurable mult :=
    hemb.measurable_extend (hwm.comp measurable_subtype_coe) measurable_const
  have horient_sm : StronglyMeasurable orient :=
    hemb.stronglyMeasurable_extend
      (((hJmeas.inv.stronglyMeasurable).smul hζ'sm).comp_measurable measurable_subtype_coe)
      stronglyMeasurable_const
  -- Step 6: `∫⁻_N mult dHⁿ = ∫⁻_B w J < ∞`, and `Hⁿ(N) ≤ ∫⁻_B w J` as `w ≥ 1` on `B`
  have hlint : ∫⁻ y in H '' B, (mult y : ℝ≥0∞) ∂μHE[n] =
      ∫⁻ a in B, (w a : ℝ≥0∞) * ENNReal.ofReal (J a) ∂volume := by
    rw [hareaL]
    refine setLIntegral_congr_fun hB (fun a ha => ?_)
    simp only [hmult_apply a ha]
    ring
  have hNfin : μHE[n] (H '' B) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [← setLIntegral_one, hareaL]
    refine setLIntegral_mono' hB (fun a ha => ?_)
    simp only [mul_one]
    calc ENNReal.ofReal (J a) = 1 * ENNReal.ofReal (J a) := (one_mul _).symm
      _ ≤ (w a : ℝ≥0∞) * ENNReal.ofReal (J a) := by
          gcongr
          exact_mod_cast hw1 a ha
  -- Step 7: for a.e. `a ∈ B`, `N` has approximate tangent space `range DH(a)` at `H(a)`, and
  -- `orient(H(a)) = ±DH(a)_# e / J(a)` is a unit orientation of it
  have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n univ (H '' B) H B L m isOpen_univ hNmeas (subset_univ _)
    (fun C _ _ => ne_top_of_le_ne_top hNfin (measure_mono inter_subset_left))
    hHL hB hm hlow hdiff subset_rfl
  have hgood : ∀ᵐ a ∂(volume.restrict B), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (H '' B) (H a) Q ∧ IsUnitOrientationOf (orient (H a)) Q := by
    filter_upwards [htan, hsign, hζ'ae, ae_restrict_mem hB] with a ha1 ha2 ha3 haB
    obtain ⟨s, hs, hsα⟩ := ha2
    refine ⟨_, ha1, ?_⟩
    rw [horient_apply a haB]
    have hJa := hJpos a haB
    have hc5 := (Submission.dgoj_unitOrientation_of_injective P n (fderiv ℝ H a) (hdiff a haB).2).2 (s • ((J a)⁻¹ • ζ' a)) (by
      intro α
      have hα := hsα α
      rw [ha3] at hα
      have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hα]
      field_simp
      rw [hs2, mul_one])
    rcases hs with rfl | rfl
    · simpa using hc5
    · obtain ⟨τ, hτ, hspan, hor⟩ := hc5
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hor with h | h
      · right
        intro α
        have := h α
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
        linarith
      · left
        intro α
        have := h α
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
        linarith
  -- Step 8: transfer to `Hⁿ`-a.e. `y ∈ N`; the exceptional set has `Hⁿ`-null image (`H` Lipschitz)
  have horients : ∀ᵐ y ∂(μHE[n].restrict (H '' B)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (H '' B) y Q ∧ IsUnitOrientationOf (orient y) Q := by
    rw [ae_restrict_iff' hB] at hgood
    rw [ae_iff] at hgood
    rw [ae_restrict_iff' hNmeas, ae_iff]
    set Z := {a | ¬(a ∈ B → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (H '' B) (H a) Q ∧ IsUnitOrientationOf (orient (H a)) Q)}
    have hZ : μHE[n] (H '' Z) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (A := Z) n (hHL.lipschitzOnWith)
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, hgood, mul_zero] at h
      exact nonpos_iff_eq_zero.mp h
    refine measure_mono_null ?_ hZ
    intro y hy
    simp only [mem_ofPred_eq, not_imp] at hy
    obtain ⟨⟨a, haB, rfl⟩, hbad⟩ := hy
    push Not at hbad
    refine ⟨a, ?_, rfl⟩
    show ¬(a ∈ B → _)
    intro h
    obtain ⟨Q, h1, h2⟩ := h haB
    exact hbad Q h1 h2
  -- Step 9: `(N, mult, orient)` is an integer multiplicity triple in `U`
  let R : IMRep U n :=
    { carrier := H '' B
      mult := mult
      orient := orient
      measurableSet_carrier := hNmeas
      carrier_subset := hHU
      rectifiable := (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hHL).mono
        (image_subset_range _ _)
      measurable_mult := hmult_meas
      mult_pos := by
        rintro _ ⟨a, ha, rfl⟩
        rw [hmult_apply a ha]
        exact hw1 a ha
      locallyIntegrable_mult := by
        intro C _ _
        refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
        rw [hlint]; exact hfin
      aestronglyMeasurable_orient := horient_sm.aestronglyMeasurable
      orients := horients }
  -- Steps 10–11: the mass `μ_R(U) = ∫⁻_N mult dHⁿ` and the action, by the area formulas
  refine ⟨R, ?_, fun ω => ?_⟩
  · show ((μHE[n].restrict (H '' B)).withDensity fun x => (mult x : ℝ≥0∞)) U = _
    rw [withDensity_apply _ hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
      inter_eq_right.mpr hHU, hlint]
  · show ∫ x in H '' B, (mult x : ℝ) * orient x (ω x) ∂μHE[n] = _
    rw [hareaI]
    refine setIntegral_congr_ae hB ?_
    filter_upwards [(ae_restrict_iff' hB).1 hζ'ae] with a ha haB
    rw [hmult_apply a haB, horient_apply a haB, ha haB]
    have hJa := (hJpos a haB).ne'
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- Algebra of the area Jacobian for the push-forward of an integer multiplicity current by a `C¹`
map (Simon 6.3.3–3.9; `J_A = √det(A* ∘ A)` is the area Jacobian of Ch. 2, 3.1/3.3).  For linear
`A : ℝⁿ → ℝᴾ` and `Ae = (A e₁, …, A eₙ)`: (a) `J_{L∘A} ≤ ‖L‖ⁿ J_A` for every linear `L` of `ℝᴾ`;
(b) `|α(Ae)| ≤ J_A ‖α‖` for every `n`-covector `α`; (c) if `A` is injective, then
`J_A ξ(α) = s α(Ae)` for every unit orientation `ξ` of `range A`, with one sign `s = ±1` for all
`α`.  If `A` is not injective, `Ae` is linearly dependent, so `α(Ae) = 0`.  Otherwise
`ζ(α) = J_A⁻¹ α(Ae)` is a unit orientation `±τ₁ ∧ ⋯ ∧ τₙ` of `range A`, which gives (b) as
`|α(τ)| ≤ ‖α‖`, and (c) since two unit orientations of `range A` differ by a sign.  For (a),
with orthonormal frames `τ` of `range A` and `σ` of `range (L ∘ A)`, `J_A = |det M|` and
`J_{L∘A} = |det N|` for `M = (⟨τᵢ, A eⱼ⟩)` and `N = (⟨σᵢ, L A eⱼ⟩) = K M`, `K = (⟨σᵢ, L τₖ⟩)`;
by Hadamard's inequality `|det K| ≤ ∏ₖ |L τₖ| ≤ ‖L‖ⁿ`. -/
theorem Submission.dimred_mbl_pfi_gram_jacobian_algebra : ∀ (P n : ℕ) (A : Euclid n →L[ℝ] Euclid P), (∀ L : Euclid P →L[ℝ] Euclid P, Real.sqrt (((L ∘L A).adjoint ∘L (L ∘L A)).det) ≤ ‖L‖ ^ n * Real.sqrt ((A.adjoint ∘L A).det)) ∧ (∀ α : Covector (Euclid P) n, |α (fun j => A (EuclideanSpace.single j (1 : ℝ)))| ≤ Real.sqrt ((A.adjoint ∘L A).det) * ‖α‖) ∧ (Injective A → ∀ ξ : MultiVector P n, IsUnitOrientationOf ξ (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)) → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, Real.sqrt ((A.adjoint ∘L A).det) * ξ α = s * α (fun j => A (EuclideanSpace.single j (1 : ℝ)))) := by
  intro P n A
  -- if `A` is not injective, `Ae` is linearly dependent and every `α(Ae)` vanishes
  have hdep : ¬ Injective A → ∀ α : Covector (Euclid P) n,
      α (fun j => A (EuclideanSpace.single j (1 : ℝ))) = 0 := by
    intro hA α
    apply α.toAlternatingMap.map_linearDependent
    intro hli
    apply hA
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ∑ j, x j • A (EuclideanSpace.single j (1 : ℝ)) = 0 := by
      have hsum : x = ∑ j, x j • EuclideanSpace.single j (1 : ℝ) := by
        ext k
        simp [Pi.single_apply]
      have : A x = 0 := hx
      rw [hsum, map_sum] at this
      simpa [map_smul] using this
    have h0 := (Fintype.linearIndependent_iff.mp hli) (fun j => x j) hx'
    ext k
    simp [h0 k]
  -- if `A` is injective, `J_A > 0` and `ζ(α) = J_A⁻¹ α(Ae)` is a unit orientation of `range A`
  have hζ : Injective A → 0 < Real.sqrt ((A.adjoint ∘L A).det) ∧ ∃ ζ : MultiVector P n,
      (∀ β : Covector (Euclid P) n, β (fun j => A (EuclideanSpace.single j (1 : ℝ))) =
        Real.sqrt ((A.adjoint ∘L A).det) * ζ β) ∧
      IsUnitOrientationOf ζ (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)) := by
    intro hA
    obtain ⟨hpos, hor⟩ := Submission.dgoj_unitOrientation_of_injective P n A hA
    have hJpos : 0 < Real.sqrt ((A.adjoint ∘L A).det) := Real.sqrt_pos.2 hpos
    let ζ : MultiVector P n := (Real.sqrt ((A.adjoint ∘L A).det))⁻¹ •
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun j => A (EuclideanSpace.single j (1 : ℝ)))
    have hev : ∀ β : Covector (Euclid P) n, β (fun j => A (EuclideanSpace.single j (1 : ℝ))) =
        Real.sqrt ((A.adjoint ∘L A).det) * ζ β := by
      intro β
      simp only [ζ, FunLike.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.apply_apply,
        smul_eq_mul]
      field_simp
    exact ⟨hJpos, ζ, hev, hor ζ hev⟩
  refine ⟨fun L => ?_, fun α => ?_, fun hA ξ hξ => ?_⟩
  · -- (a)
    by_cases hLA : Injective (L ∘L A)
    · have hA : Injective A := fun x y hxy => hLA (by simp [hxy])
      -- orthonormal frames `σ` of `range (L ∘ A)` and `τ` of `range A`
      obtain ⟨σ, hσo, hσs⟩ := Submission.dgoj_exists_orthonormal_frame_range P n (L ∘L A) hLA
      obtain ⟨τ, hτo, hτs⟩ := Submission.dgoj_exists_orthonormal_frame_range P n A hA
      have hbσ : ∀ j, (L ∘L A) (EuclideanSpace.single j (1 : ℝ)) ∈
          Submodule.span ℝ (Set.range σ) := by
        intro j
        rw [hσs]
        exact LinearMap.mem_range_self _ _
      have hbτ : ∀ j, A (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ) := by
        intro j
        rw [hτs]
        exact LinearMap.mem_range_self _ _
      -- `J_{L∘A} = |det N|` and `J_A = |det M|`
      rw [Submission.dgoj_det_adjoint_comp_eq_det_sq P n (L ∘L A) σ hσo hbσ,
        Submission.dgoj_det_adjoint_comp_eq_det_sq P n A τ hτo hbτ,
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
      set M := Matrix.of fun i j => inner ℝ (τ i) (A (EuclideanSpace.single j (1 : ℝ))) with hM
      set K := Matrix.of fun i k => inner ℝ (σ i) (L (τ k)) with hK
      -- `A eⱼ = ∑ₖ Mₖⱼ τₖ`
      have hexp : ∀ j, A (EuclideanSpace.single j (1 : ℝ)) = ∑ k, M k j • τ k := by
        intro j
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hbτ j)
        have hcM : ∀ k, M k j = c k := by
          intro k
          rw [hM, Matrix.of_apply, ← hc]
          exact hτo.inner_right_fintype c k
        simp_rw [hcM]
        exact hc.symm
      -- `N = K M`
      have hN : (Matrix.of fun i j => inner ℝ (σ i) ((L ∘L A) (EuclideanSpace.single j (1 : ℝ)))) =
          K * M := by
        ext i j
        rw [Matrix.of_apply, Matrix.mul_apply, ContinuousLinearMap.comp_apply, hexp j, map_sum,
          inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, inner_smul_right, hK, Matrix.of_apply, mul_comm]
      rw [hN, Matrix.det_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      -- Hadamard's inequality: `|det K| ≤ ∏ₖ |L τₖ| ≤ ‖L‖ⁿ`
      set Q := Submodule.span ℝ (Set.range σ)
      have hmem : ∀ i, σ i ∈ Q := fun i => Submodule.subset_span (Set.mem_range_self i)
      let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
      have hu : Orthonormal ℝ u := by
        rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
        exact hσo
      have huspan : ⊤ ≤ Submodule.span ℝ (Set.range u) := by
        rintro ⟨y, hy⟩ -
        rw [Submodule.mem_span_range_iff_exists_fun] at hy
        obtain ⟨c, hc⟩ := hy
        rw [Submodule.mem_span_range_iff_exists_fun]
        exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
      let b : OrthonormalBasis (Fin n) ℝ Q := OrthonormalBasis.mk hu huspan
      have hb : ∀ i, (b i : Euclid P) = σ i := fun i => by simp [b, u]
      have hw : ∀ k, L (τ k) ∈ Q := by
        intro k
        have hk : τ k ∈ LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P) :=
          hτs ▸ Submodule.subset_span (Set.mem_range_self k)
        obtain ⟨x, hx⟩ := hk
        rw [hσs]
        exact ⟨x, by simp [← hx]⟩
      let w : Fin n → Q := fun k => ⟨L (τ k), hw k⟩
      have hKw : K.det = b.toBasis.det w := by
        rw [Module.Basis.det_apply]
        congr 1
        ext i k
        rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, Submodule.coe_inner, hb, hK, Matrix.of_apply]
      have : Fact (Module.finrank ℝ Q = n) :=
        ⟨by rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]⟩
      have hH := (b.toBasis.orientation).abs_volumeForm_apply_le w
      rw [(b.toBasis.orientation).volumeForm_robust b rfl] at hH
      rw [hKw]
      refine hH.trans ?_
      calc ∏ k, ‖w k‖ ≤ ∏ _k : Fin n, ‖L‖ := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
            have h1 : ‖w k‖ = ‖L (τ k)‖ := rfl
            rw [h1]
            calc ‖L (τ k)‖ ≤ ‖L‖ * ‖τ k‖ := L.le_opNorm _
              _ = ‖L‖ := by rw [hτo.1 k, mul_one]
        _ = ‖L‖ ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · -- `L ∘ A` is not injective: `det((L ∘ A)* ∘ (L ∘ A)) = 0`
      have h0 : ((L ∘L A).adjoint ∘L (L ∘L A)).det = 0 := by
        apply LinearMap.det_eq_zero_iff_ker_ne_bot.2
        rw [ContinuousLinearMap.ker_adjoint_comp_self, Ne, LinearMap.ker_eq_bot]
        exact hLA
      rw [h0, Real.sqrt_zero]
      positivity
  · -- (b)
    by_cases hA : Injective A
    · obtain ⟨hJpos, ζ, hev, τ, hτ, -, hsgn⟩ := hζ hA
      have hατ : |α τ| ≤ ‖α‖ := by
        simpa [hτ.norm_eq_one, Real.norm_eq_abs] using α.le_opNorm τ
      rw [hev α, abs_mul, abs_of_pos hJpos]
      refine mul_le_mul_of_nonneg_left ?_ hJpos.le
      rcases hsgn with h | h
      · rwa [h α]
      · rwa [h α, abs_neg]
    · rw [hdep hA α, abs_zero]
      positivity
  · -- (c): `ξ = ±ζ`
    obtain ⟨-, ζ, hev, hζo⟩ := hζ hA
    rcases Submission.rsdic_unitOrientation_eq_or_eq_neg P n ζ ξ _ hζo hξ with h | h
    · exact ⟨1, Or.inl rfl, fun α => by rw [h, hev α]; ring⟩
    · exact ⟨-1, Or.inr rfl, fun α => by rw [h, hev α, neg_apply]; ring⟩

/-- Orientation of an integer multiplicity triple `(M, θ, ξ)` in `U` along a bi-Lipschitz piece of
its carrier: let `F` be Lipschitz, `B` Borel with `m|a − a'| ≤ |F(a) − F(a')|` on `B`, `DF(a)`
injective for `a ∈ B`, and `F(B) ⊆ M`.  Then `b ↦ ξ(F(b))` is a.e. strongly measurable on `B`, and
for a.e. `b ∈ B`, `ξ(F(b))` is a unit orientation of `range DF(b)`.  As `θ ≥ 1` on `M`, `M` is
locally `Hⁿ`-finite in `U`, so it has approximate tangent space `range DF(b)` at `F(b)` for a.e.
`b`; `ξ` orients an approximate tangent space of `M` `Hⁿ`-a.e. on `F(B) ⊆ M`, which pulls back to
a.e. `b ∈ B`; and approximate tangent spaces are unique (Simon Ch. 3, Remark 1.5(1)). -/
theorem Submission.dimred_mbl_pfi_imrep_orient_along_piece : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ R.carrier → AEStronglyMeasurable (fun b => R.orient (F b)) (volume.restrict B) ∧ ∀ᵐ b ∂(volume.restrict B), IsUnitOrientationOf (R.orient (F b)) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n U R F B L m hU hFL hB hm hlow hdiff hsub
  -- Step 1: `θ ≥ 1` on `M` and `θ` is locally integrable, so `M` is locally `Hⁿ`-finite in `U`
  have hloc : ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (R.carrier ∩ C) ≠ ∞ := by
    intro C hC hCU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult C hC hCU) ?_
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (R.measurableSet_carrier.inter hC.isClosed.measurableSet)
      (fun x hx => ?_)
    have := R.mult_pos x hx.1
    exact_mod_cast this
  -- Step 2: `M` has approximate tangent space `range DF(b)` at `F(b)` for a.e. `b ∈ B`
  have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n U R.carrier F B L m hU
    R.measurableSet_carrier R.carrier_subset hloc hFL hB hm hlow hdiff hsub
  -- Step 3: `ξ(F(b))` orients some approximate tangent space of `M` at `F(b)` for a.e. `b ∈ B`
  have hpull := (Submission.ptd_piece_image_measurable_ae_pullback P n F B L m hFL hB hm hlow).2
  have hor1 : ∀ᵐ y ∂(μHE[n].restrict (F '' B)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier y Q ∧ IsUnitOrientationOf (R.orient y) Q :=
    ae_restrict_of_ae_restrict_of_subset hsub R.orients
  have hor2 := hpull _ hor1
  -- Step 5: `ξ(F(b)) = ξ̃(F(b))` for a.e. `b ∈ B`, `ξ̃` a strongly measurable version of `ξ`
  have hξ := R.aestronglyMeasurable_orient
  have heq1 : ∀ᵐ y ∂(μHE[n].restrict (F '' B)), R.orient y = hξ.mk _ y :=
    ae_restrict_of_ae_restrict_of_subset hsub hξ.ae_eq_mk
  have heq2 := hpull _ heq1
  refine ⟨?_, ?_⟩
  · refine (hξ.stronglyMeasurable_mk.comp_measurable
      hFL.continuous.measurable).aestronglyMeasurable.congr ?_
    filter_upwards [heq2] with b hb
    exact hb.symm
  -- Step 4: uniqueness of approximate tangent spaces identifies the oriented one with `range DF(b)`
  · filter_upwards [htan, hor2] with b hb1 hb2
    obtain ⟨Q, hQ, hor⟩ := hb2
    have hQeq := hQ.unique hb1
    rw [← hQeq]
    exact hor

/-- A summable series of integer-weighted Lipschitz parametrizations `Hᵢ : Bᵢ → U` with
orientations `ζᵢ = ±DHᵢ#e` is summed by one integer multiplicity triple `R` in `U`:
`Σᵢ ∫_{Bᵢ} wᵢ ⟨ω ∘ Hᵢ, ζᵢ⟩ = R(ω)` for every `ω ∈ 𝒟ⁿ(U)`.  `DHᵢ` is injective on
`Bᵢ⁺ = {a ∈ Bᵢ : Jᵢ(a) > 0, wᵢ(a) ≥ 1}`; cut `Bᵢ⁺` into bi-Lipschitz pieces `C_{il}`, make each
piece a triple `R_{il}` by the area formula and sum the `R_{il}`, whose total mass is at most
`Σᵢ ∫_{Bᵢ} wᵢJᵢ < ∞`.  The integrands are dominated by `wᵢJᵢ‖ω‖_∞` and vanish a.e. off `Bᵢ⁺`,
so summing over the pieces of each `Bᵢ⁺` gives the series. -/
theorem Submission.dimred_mbl_pfi_param_series_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (H : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (w : ℕ → Euclid n → ℕ) (ζ : ℕ → Euclid n → MultiVector P n), IsOpen U → (∀ i, ∃ L : NNReal, LipschitzWith L (H i)) → (∀ i, MeasurableSet (B i)) → (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (H i) a) → (∀ i, H i '' B i ⊆ U) → (∀ i, Measurable (w i)) → (∀ i, AEStronglyMeasurable (ζ i) (volume.restrict (B i))) → (∀ i, ∀ᵐ a ∂(volume.restrict (B i)), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, ζ i a α = s * α (fun j => fderiv ℝ (H i) a (EuclideanSpace.single j (1 : ℝ)))) → ∑' i, ∫⁻ a in B i, (w i a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)) ∂volume ≠ ∞ → ∃ R : IMRep U n, ∀ ω : TestFormOn U n, HasSum (fun i => ∫ a in B i, (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)) ∂volume) (R.action (ω : DifferentialForm (Euclid P) n)) := by
  intro P n U H B w ζ hU hHL hBm hHd hHU hwm hζm hsign hsum
  classical
  choose LH hLH using hHL
  have hcJ : Continuous (fun A : Euclid n →L[ℝ] Euclid P => Real.sqrt ((A.adjoint ∘L A).det)) := by
    refine Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp ?_)
    exact isBoundedBilinearMap_comp.continuous.comp
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid n) (F := Euclid P)).continuous.prodMk
        continuous_id)
  have hJmeas : ∀ i, Measurable (fun a =>
      Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)) :=
    fun i => hcJ.measurable.comp (measurable_fderiv ℝ (H i))
  set Bp : ℕ → Set (Euclid n) := fun i => B i ∩
    {a | 0 < Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)} ∩
    {a | 1 ≤ w i a}
  have hBpm : ∀ i, MeasurableSet (Bp i) := fun i =>
    ((hBm i).inter (measurableSet_lt measurable_const (hJmeas i))).inter
      (measurableSet_le measurable_const (hwm i))
  have hBpB : ∀ i, Bp i ⊆ B i := fun i => inter_subset_left.trans inter_subset_left
  have hinjBp : ∀ i, ∀ a ∈ Bp i, DifferentiableAt ℝ (H i) a ∧ Injective (fderiv ℝ (H i) a) := by
    intro i a ha
    refine ⟨hHd i a (hBpB i ha), ?_⟩
    have hpos : 0 < ((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det :=
      Real.sqrt_pos.mp ha.1.2
    set A := fderiv ℝ (H i) a
    have hT : IsUnit ((A.adjoint ∘L A : Euclid n →L[ℝ] Euclid n) : Euclid n →ₗ[ℝ] Euclid n) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hpos.ne')
    intro x y hxy
    have h2 : (A.adjoint ∘L A) x = (A.adjoint ∘L A) y := by
      simp only [ContinuousLinearMap.comp_apply, hxy]
    exact (Module.End.isUnit_iff _).1 hT |>.1 h2
  have hpart := fun i => Submission.dimred_mbl_pfi_bilipschitz_partition P n (H i) (Bp i) (hBpm i)
    (hinjBp i)
  choose C mC hCm hCdisj hCunion hmC hClow using hpart
  have hCsub : ∀ i l, C i l ⊆ Bp i := fun i l => (hCunion i) ▸ subset_iUnion (C i) l
  have hJfin : ∀ i, ∫⁻ a in B i, (w i a : ℝ≥0∞) *
      ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det))
        ∂volume ≠ ∞ := fun i => ENNReal.ne_top_of_tsum_ne_top hsum i
  have hpiece : ∀ i l, ∃ R : IMRep U n, R.measure U = ∫⁻ a in C i l, (w i a : ℝ≥0∞) *
      ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det))
        ∂volume ∧ ∀ ω : DifferentialForm (Euclid P) n,
          R.action ω = ∫ a in C i l, (w i a : ℝ) * ζ i a (ω (H i a)) ∂volume := by
    intro i l
    have hsub : C i l ⊆ B i := (hCsub i l).trans (hBpB i)
    exact Submission.dimred_mbl_pfi_bilipschitz_piece_imrep P n U (H i) (C i l) (LH i) (mC i l)
      (w i) (ζ i) hU (hLH i) (hCm i l) (hmC i l) (hClow i l) (fun a ha => hinjBp i a (hCsub i l ha))
      ((Set.image_mono hsub).trans (hHU i)) (hwm i) (fun a ha => (hCsub i l ha).2)
      ((hζm i).mono_measure (Measure.restrict_mono hsub le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hsub (hsign i))
      (ne_top_of_le_ne_top (hJfin i) (lintegral_mono_set hsub))
  choose Rp hRpmeas hRpact using hpiece
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  have hmass : ∑' k, (Rp (e k).1 (e k).2).measure U ≠ ∞ := by
    rw [e.tsum_eq (fun p => (Rp p.1 p.2).measure U), ENNReal.tsum_prod']
    simp_rw [hRpmeas]
    refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun i => ?_)
    rw [← lintegral_iUnion (hCm i) (hCdisj i), hCunion i]
    exact lintegral_mono_set (hBpB i)
  obtain ⟨R', hR'⟩ := Submission.cmcdt_ims_imrep_tsum P n U (fun k => Rp (e k).1 (e k).2) hU hmass
  refine ⟨R', fun ω => ?_⟩
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous ω.property.1.1
  obtain ⟨Bω, hBω⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
  have hint : ∀ i, IntegrableOn
      (fun a => (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a))) (B i) volume := by
    intro i
    have hζ' := hζm i
    have hsm : StronglyMeasurable
        (fun a => (w i a : ℝ) * (hζ'.mk _ a) ((ω : DifferentialForm (Euclid P) n) (H i a))) := by
      have hc : Continuous (fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2) :=
        isBoundedBilinearMap_apply.continuous
      exact (measurable_from_nat.comp (hwm i)).stronglyMeasurable.mul
        (hc.comp_stronglyMeasurable (hζ'.stronglyMeasurable_mk.prodMk
          (hωc.comp (hLH i).continuous).stronglyMeasurable))
    have hae : (fun a => (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)))
        =ᵐ[volume.restrict (B i)]
        (fun a => (w i a : ℝ) * (hζ'.mk _ a) ((ω : DifferentialForm (Euclid P) n) (H i a))) := by
      filter_upwards [hζ'.ae_eq_mk] with a ha
      simp only [ha]
    have hdom : IntegrableOn (fun a => Bω * ((w i a : ℝ) *
        Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det))) (B i) volume := by
      refine Integrable.const_mul ?_ _
      refine ⟨((measurable_from_nat.comp (hwm i)).mul (hJmeas i)).aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have : ∀ a, ‖(w i a : ℝ) *
          Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)‖ₑ =
          (w i a : ℝ≥0∞) *
            ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)) := by
        intro a
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      simp_rw [this]
      exact (hJfin i).lt_top
    refine hdom.mono' (hsm.aestronglyMeasurable.congr hae.symm) ?_
    filter_upwards [hsign i] with a ⟨s, hs, hsα⟩
    rw [hsα, norm_mul, norm_mul, Real.norm_natCast]
    have hb := (Submission.dimred_mbl_pfi_gram_jacobian_algebra P n (fderiv ℝ (H i) a)).2.1
      ((ω : DifferentialForm (Euclid P) n) (H i a))
    have hs1 : ‖s‖ = 1 := by rcases hs with h | h <;> simp [h]
    rw [hs1, one_mul, Real.norm_eq_abs]
    calc (w i a : ℝ) * |((ω : DifferentialForm (Euclid P) n) (H i a))
          (fun j => fderiv ℝ (H i) a (EuclideanSpace.single j (1 : ℝ)))|
        ≤ (w i a : ℝ) * (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det) * Bω) := by
          gcongr
          exact hb.trans (mul_le_mul_of_nonneg_left (hBω _) (Real.sqrt_nonneg _))
      _ = Bω * ((w i a : ℝ) *
          Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)) := by ring
  have hvanish : ∀ i,
      ∫ a in B i, (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)) ∂volume =
        ∫ a in Bp i, (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)) ∂volume := by
    intro i
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hBm i).nullMeasurableSet (hBpB i) ?_
    filter_upwards [(ae_restrict_iff' (hBm i)).1 (hsign i)] with a ha hdiff
    obtain ⟨s, hs, hsα⟩ := ha hdiff.1
    have hnot : ¬ (0 < Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det) ∧
        1 ≤ w i a) := fun h => hdiff.2 ⟨⟨hdiff.1, h.1⟩, h.2⟩
    by_cases hw : 1 ≤ w i a
    · have hJ0 : Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det) = 0 :=
        le_antisymm (not_lt.1 fun h => hnot ⟨h, hw⟩) (Real.sqrt_nonneg _)
      have hb := (Submission.dimred_mbl_pfi_gram_jacobian_algebra P n (fderiv ℝ (H i) a)).2.1
        ((ω : DifferentialForm (Euclid P) n) (H i a))
      rw [hJ0, zero_mul] at hb
      have h0 : ((ω : DifferentialForm (Euclid P) n) (H i a))
          (fun j => fderiv ℝ (H i) a (EuclideanSpace.single j (1 : ℝ))) = 0 :=
        abs_nonpos_iff.mp hb
      rw [hsα, h0, mul_zero, mul_zero]
    · have hw0 : w i a = 0 := by omega
      simp [hw0]
  have hfib : ∀ i, HasSum (fun l => (Rp i l).action (ω : DifferentialForm (Euclid P) n))
      (∫ a in B i, (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)) ∂volume) := by
    intro i
    simp_rw [hRpact]
    have h1 := hasSum_integral_iUnion (hCm i) (hCdisj i)
      ((hint i).mono_set (by rw [hCunion i]; exact hBpB i))
    rw [hCunion i] at h1
    rw [hvanish i]
    exact h1
  have hprod : HasSum (fun p : ℕ × ℕ => (Rp p.1 p.2).action (ω : DifferentialForm (Euclid P) n))
      (R'.action (ω : DifferentialForm (Euclid P) n)) :=
    (e.hasSum_iff
      (f := fun p : ℕ × ℕ => (Rp p.1 p.2).action (ω : DifferentialForm (Euclid P) n))).mp (hR' ω)
  exact hprod.prod_fiberwise hfib

/-- **Simon Ch. 6, 3.3–3.9**: the push-forward of an integer multiplicity current by a `C¹` map is
integer multiplicity.  Let `R = (M, θ, ξ)` be an integer multiplicity triple in the open set `U`,
`K ⊆ U` compact with `Hⁿ(M \ K) = 0`, `f` of class `C¹` on an open `O ⊇ K` with `f(K) ⊆ U`, and
`Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ(x)`.  Then `Q = τ(N', θ', ξ')` in `U`.

Proof sketch:
* Replace `f` by a globally Lipschitz `C¹` map `g` with `g = f` and `Dg = Df` on `K`.
* Up to an `Hⁿ`-null set, `M ∩ K` is the disjoint union of the bi-Lipschitz Borel pieces
  `Gᵢ(Bᵢ)`, and `ξ(Gᵢ(u))` orients `DGᵢ(u)(ℝⁿ)` for a.e. `u ∈ Bᵢ`.  Hence
  `Jᵢ(u) ξ(Gᵢ(u)) = ±DGᵢ(u)e₁ ∧ ⋯ ∧ DGᵢ(u)eₙ`, where `Jᵢ = J_{Gᵢ}` is the area Jacobian.
* Put `Hᵢ = g ∘ Gᵢ`, `wᵢ = θ ∘ Gᵢ` and `ζᵢ(u)(α) = Jᵢ(u) ξ(Gᵢ(u))(α ∘ Dg(Gᵢ(u)))`.  The chain
  rule gives `ζᵢ(u) = ±DHᵢ(u)e₁ ∧ ⋯ ∧ DHᵢ(u)eₙ`.  Since `J_{Hᵢ} ≤ Lip(g)ⁿ Jᵢ`, the series
  `Σᵢ ∫_{Bᵢ} wᵢ ζᵢ(ω ∘ Hᵢ)` has mass at most `Lip(g)ⁿ ∫_{M ∩ K} θ dHⁿ < ∞`.  So it is represented
  by one integer multiplicity triple.
* By the area formula on each piece and countable additivity, its sum is `Q(ω)`.

The tangent-locality hypothesis and `0 < n` are not needed. -/
theorem Submission.dimred_mbl_pf_pushforward_isIntegerMultiplicity : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (Q : GeometricCurrentOn U n), IsOpen U → 0 < n → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → IsIntegerMultiplicity Q := by
  intro _TL P n U K O R f Q hU _hn hK hKU hMK hO hKO hf hfK hQ
  classical
  -- Step 1(c): a globally Lipschitz `C¹` map `g` with `g = f`, `Dg = Df` on `K`
  obtain ⟨g, Lg, hgC1, hgL, hgK⟩ :=
    Submission.dimred_mbl_pfi_c1_lipschitz_cutoff P K O f hK hO hKO hf
  have hgdiff : Differentiable ℝ g := hgC1.differentiable one_ne_zero
  have hDgcont : Continuous (fderiv ℝ g) := hgC1.continuous_fderiv one_ne_zero
  have hDg_le : ∀ x, ‖fderiv ℝ g x‖ ≤ (Lg : ℝ) := fun x => norm_fderiv_le_of_lipschitz ℝ hgL
  -- Step 1(a): `M₁ = M ∩ K` is Borel, countably `n`-rectifiable, and `∫_{M₁} θ dHⁿ < ∞`
  have hMmeas : MeasurableSet R.carrier := R.measurableSet_carrier
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hM1meas : MeasurableSet (R.carrier ∩ K) := hMmeas.inter hKmeas
  have hM1rect : CountablyRectifiable n (R.carrier ∩ K) := R.rectifiable.mono inter_subset_left
  have hθfin : ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ :=
    R.locallyIntegrable_mult K hK hKU
  -- Step 2: disjoint bi-Lipschitz Borel pieces `Gᵢ(Bᵢ) ⊆ M₁` covering `M₁` up to a null set
  obtain ⟨G, B, m, hGL, hBmeas, hm, hlow, hdiff, hGBmeas, hGBsub, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P n (R.carrier ∩ K) hM1meas hM1rect
  choose LG hLG using hGL
  have hinj : ∀ i, InjOn (G i) (B i) := by
    intro i a ha a' ha' h
    have h3 : m i * ‖a - a'‖ ≤ m i * 0 := by simpa [h] using hlow i a ha a' ha'
    have h4 : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left h3 (hm i)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)
  -- Steps 3–4: `ξ ∘ Gᵢ` is measurable and orients `DGᵢ(u)(ℝⁿ)` for a.e. `u ∈ Bᵢ`
  have hor := fun i => Submission.dimred_mbl_pfi_imrep_orient_along_piece P n U R (G i) (B i)
    (LG i) (m i) hU (hLG i) (hBmeas i) (hm i) (hlow i) (hdiff i)
    ((hGBsub i).trans inter_subset_left)
  -- Step 5: the parametrized data `Hᵢ = g ∘ Gᵢ`, `wᵢ = θ ∘ Gᵢ`, `ζᵢ = Jᵢ (Dg ∘ Gᵢ)_# (ξ ∘ Gᵢ)`
  set H : ℕ → Euclid n → Euclid P := fun i u => g (G i u) with hHdef
  set w : ℕ → Euclid n → ℕ := fun i u => R.mult (G i u) with hwdef
  set J : ℕ → Euclid n → ℝ := fun i u =>
    Real.sqrt (((fderiv ℝ (G i) u).adjoint ∘L fderiv ℝ (G i) u).det) with hJdef
  set ζ : ℕ → Euclid n → MultiVector P n := fun i u =>
    J i u • (R.orient (G i u)).comp
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ g (G i u))) with hζdef
  have hHd : ∀ i, ∀ u ∈ B i, DifferentiableAt ℝ (H i) u ∧
      fderiv ℝ (H i) u = (fderiv ℝ g (G i u)).comp (fderiv ℝ (G i) u) := by
    intro i u hu
    have h1 : DifferentiableAt ℝ g (G i u) := hgdiff _
    have h2 : DifferentiableAt ℝ (G i) u := (hdiff i u hu).1
    exact ⟨h1.comp u h2, fderiv_comp u h1 h2⟩
  have hJmeas : ∀ i, Measurable (J i) := by
    intro i
    have hc : Continuous (fun A : Euclid n →L[ℝ] Euclid P =>
        Real.sqrt ((A.adjoint ∘L A).det)) := by
      refine Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp ?_)
      exact isBoundedBilinearMap_comp.continuous.comp
        ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid n) (F := Euclid P)).continuous.prodMk
          continuous_id)
    exact hc.measurable.comp (measurable_fderiv ℝ (G i))
  have hcomp : Continuous (fun p : MultiVector P n × (Euclid P →L[ℝ] Euclid P) =>
      p.1.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM (𝕜 := ℝ) (ι := Fin n)
        (F := ℝ) p.2)) :=
    isBoundedBilinearMap_comp.continuous.comp
      (continuous_fst.prodMk
        (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp continuous_snd))
  have hζmeas : ∀ i, AEStronglyMeasurable (ζ i) (volume.restrict (B i)) := by
    intro i
    have h1 : AEStronglyMeasurable (fun u => R.orient (G i u)) (volume.restrict (B i)) :=
      (hor i).1
    have h2 : Continuous (fun u => fderiv ℝ g (G i u)) := hDgcont.comp (hLG i).continuous
    have hsm : StronglyMeasurable (fun u => J i u • (h1.mk _ u).comp
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ g (G i u)))) :=
      (hJmeas i).stronglyMeasurable.smul
        (hcomp.comp_stronglyMeasurable (h1.stronglyMeasurable_mk.prodMk h2.stronglyMeasurable))
    refine hsm.aestronglyMeasurable.congr ?_
    filter_upwards [h1.ae_eq_mk] with u hu
    simp only [hζdef, hu]
  -- `(★)` composed with `Dg`: `ζᵢ(u)(α) = ±α(DHᵢ(u)e₁, …, DHᵢ(u)eₙ)` for a.e. `u ∈ Bᵢ`
  have hsign : ∀ i, ∀ᵐ u ∂(volume.restrict (B i)), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ α : Covector (Euclid P) n,
        ζ i u α = s * α (fun j => fderiv ℝ (H i) u (EuclideanSpace.single j (1 : ℝ))) := by
    intro i
    filter_upwards [(hor i).2, ae_restrict_mem (hBmeas i)] with u hu huB
    obtain ⟨s, hs, hsα⟩ := (Submission.dimred_mbl_pfi_gram_jacobian_algebra P n
      (fderiv ℝ (G i) u)).2.2 (hdiff i u huB).2 (R.orient (G i u)) hu
    refine ⟨s, hs, fun α => ?_⟩
    have key := hsα (α.compContinuousLinearMap (fderiv ℝ g (G i u)))
    rw [(hHd i u huB).2]
    simp only [hζdef, hJdef, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, smul_eq_mul]
    rw [key]
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  -- `J_{Hᵢ} ≤ ‖Dg‖ⁿ J_{Gᵢ} ≤ Lip(g)ⁿ J_{Gᵢ}` on `Bᵢ`
  have hJH : ∀ i, ∀ u ∈ B i,
      Real.sqrt (((fderiv ℝ (H i) u).adjoint ∘L fderiv ℝ (H i) u).det) ≤ (Lg : ℝ) ^ n * J i u := by
    intro i u hu
    rw [(hHd i u hu).2]
    refine ((Submission.dimred_mbl_pfi_gram_jacobian_algebra P n (fderiv ℝ (G i) u)).1
      (fderiv ℝ g (G i u))).trans ?_
    gcongr
    exact hDg_le _
  -- Step 6: total mass `Σᵢ ∫_{Bᵢ} wᵢ J_{Hᵢ} ≤ Lip(g)ⁿ Σᵢ ∫_{Gᵢ(Bᵢ)} θ ≤ Lip(g)ⁿ ∫_{M₁} θ < ∞`
  have hsum : ∑' i, ∫⁻ u in B i, (w i u : ℝ≥0∞) *
      ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) u).adjoint ∘L fderiv ℝ (H i) u).det))
        ∂volume ≠ ∞ := by
    have hterm : ∀ i, ∫⁻ u in B i, (w i u : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) u).adjoint ∘L fderiv ℝ (H i) u).det))
          ∂volume ≤ ENNReal.ofReal ((Lg : ℝ) ^ n) *
            ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
      intro i
      have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_volume_of_injective_derivative
        (hBmeas i) (fun x hx => (hdiff i x hx).1) (fun x hx => (hdiff i x hx).2) (hinj i)
        (fun y => (R.mult y : ℝ≥0∞))
      rw [finrank_euclideanSpace_fin] at harea
      rw [harea, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' (hBmeas i) (fun u hu => ?_)
      rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp]
      calc (w i u : ℝ≥0∞) *
            ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) u).adjoint ∘L fderiv ℝ (H i) u).det))
          ≤ (w i u : ℝ≥0∞) * ENNReal.ofReal ((Lg : ℝ) ^ n * J i u) := by
            gcongr
            exact hJH i u hu
        _ = ENNReal.ofReal ((Lg : ℝ) ^ n) * (ENNReal.ofReal (J i u) * (R.mult (G i u) : ℝ≥0∞)) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            simp only [hwdef]
            ring
    have htot : ∑' i, ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[n] ≤
        ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      rw [← lintegral_iUnion hGBmeas hdisj]
      exact lintegral_mono_set (iUnion_subset hGBsub)
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (Lg : ℝ) ^ n)) hθfin) ?_
    calc _ ≤ ∑' i, ENNReal.ofReal ((Lg : ℝ) ^ n) *
            ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[n] := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal ((Lg : ℝ) ^ n) *
            ∑' i, ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[n] := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr
  -- `Hᵢ(Bᵢ) ⊆ g(K) = f(K) ⊆ U`
  have himg : ∀ i, H i '' B i ⊆ U := by
    rintro i _ ⟨u, hu, rfl⟩
    have hx : G i u ∈ R.carrier ∩ K := hGBsub i ⟨u, hu, rfl⟩
    show g (G i u) ∈ U
    rw [(hgK _ hx.2).1]
    exact hfK ⟨G i u, hx.2, rfl⟩
  -- Steps 7–11: the parametrized series is represented by one integer multiplicity triple `R'`
  obtain ⟨R', hR'⟩ := Submission.dimred_mbl_pfi_param_series_imrep P n U H B w ζ hU
    (fun i => ⟨Lg * LG i, hgL.comp (hLG i)⟩) hBmeas (fun i u hu => (hHd i u hu).1) himg
    (fun i => R.measurable_mult.comp (hLG i).continuous.measurable) hζmeas hsign hsum
  refine ⟨R', fun ω => ?_⟩
  -- Step 6: `Q(ω)` is the sum of the series (area formula on each piece)
  have hωs : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hωs
  obtain ⟨Bω, hBω⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
  set Φ : Euclid P → ℝ := fun x => (R.mult x : ℝ) * R.orient x
    (((ω : DifferentialForm (Euclid P) n) (g x)).compContinuousLinearMap (fderiv ℝ g x))
    with hΦdef
  have hQ1 : Q ω = ∫ x in R.carrier ∩ K, Φ x ∂μHE[n] := by
    rw [hQ ω]
    have hae : (R.carrier : Set (Euclid P)) =ᵐ[μHE[n]] (R.carrier ∩ K : Set (Euclid P)) := by
      rw [ae_eq_set]
      constructor
      · rw [sdiff_self_inter]; exact hMK
      · rw [sdiff_eq_empty.mpr inter_subset_left]; exact measure_empty
    rw [setIntegral_congr_set hae]
    refine setIntegral_congr_fun hM1meas (fun x hx => ?_)
    simp only [hΦdef, (hgK x hx.2).1, (hgK x hx.2).2]
  have hQ2 : ∫ x in R.carrier ∩ K, Φ x ∂μHE[n] = ∫ x in ⋃ i, G i '' B i, Φ x ∂μHE[n] := by
    apply setIntegral_congr_set
    rw [ae_eq_set]
    constructor
    · exact hnull
    · rw [sdiff_eq_empty.mpr (iUnion_subset hGBsub)]; exact measure_empty
  -- integrability: `|Φ| ≤ sup|ω| · Lip(g)ⁿ · θ` a.e. on `M`, as `|ξ(x)(β)| ≤ ‖β‖`
  have hUsub : (⋃ i, G i '' B i) ⊆ R.carrier :=
    iUnion_subset fun i => (hGBsub i).trans inter_subset_left
  have hβc : Continuous (fun x => ((ω : DifferentialForm (Euclid P) n) (g x)).compContinuousLinearMap
      (fderiv ℝ g x)) := by
    have := (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM (𝕜 := ℝ)
      (ι := Fin n) (E := Euclid P) (F := Euclid P) (G := ℝ)).comp hDgcont
    exact this.clm_apply (hωc.comp hgdiff.continuous)
  have hξm := R.aestronglyMeasurable_orient
  have hΦsm : StronglyMeasurable (fun x => (R.mult x : ℝ) * (hξm.mk _ x)
      (((ω : DifferentialForm (Euclid P) n) (g x)).compContinuousLinearMap (fderiv ℝ g x))) := by
    have hc : Continuous (fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2) :=
      isBoundedBilinearMap_apply.continuous
    exact (measurable_from_nat.comp R.measurable_mult).stronglyMeasurable.mul
      (hc.comp_stronglyMeasurable (hξm.stronglyMeasurable_mk.prodMk hβc.stronglyMeasurable))
  have hΦae : Φ =ᵐ[μHE[n].restrict R.carrier] (fun x => (R.mult x : ℝ) * (hξm.mk _ x)
      (((ω : DifferentialForm (Euclid P) n) (g x)).compContinuousLinearMap (fderiv ℝ g x))) := by
    filter_upwards [hξm.ae_eq_mk] with x hx
    simp only [hΦdef, hx]
  have hΦbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖Φ x‖ ≤ Bω * (Lg : ℝ) ^ n * (R.mult x : ℝ) := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Qx, -, τ, hτ, -, hsgn⟩ := hx
    set β := ((ω : DifferentialForm (Euclid P) n) (g x)).compContinuousLinearMap (fderiv ℝ g x)
    have hβτ : ‖β τ‖ ≤ ‖β‖ := by
      have h := β.le_opNorm τ
      simpa [hτ.norm_eq_one] using h
    have hξβ : ‖R.orient x β‖ ≤ ‖β‖ := by
      rcases hsgn with h | h
      · rw [h β]; exact hβτ
      · rw [h β, norm_neg]; exact hβτ
    have hβle : ‖β‖ ≤ Bω * (Lg : ℝ) ^ n := by
      refine (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Fintype.card_fin]
      have h0 : 0 ≤ Bω := (norm_nonneg _).trans (hBω 0)
      exact mul_le_mul (hBω _) (pow_le_pow_left₀ (norm_nonneg _) (hDg_le x) n)
        (pow_nonneg (norm_nonneg _) n) h0
    simp only [hΦdef, norm_mul, Real.norm_natCast]
    calc (R.mult x : ℝ) * ‖R.orient x β‖ ≤ (R.mult x : ℝ) * (Bω * (Lg : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left (hξβ.trans hβle) (Nat.cast_nonneg _)
      _ = Bω * (Lg : ℝ) ^ n * (R.mult x : ℝ) := by ring
  have hθint : IntegrableOn (fun x => (R.mult x : ℝ)) (R.carrier ∩ K) μHE[n] := by
    refine ⟨(measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have : ∀ x, ‖(R.mult x : ℝ)‖ₑ = (R.mult x : ℝ≥0∞) := fun x => by simp
    simp_rw [this]
    exact hθfin.lt_top
  have hint : IntegrableOn Φ (⋃ i, G i '' B i) μHE[n] := by
    have hθint' : IntegrableOn (fun x => Bω * (Lg : ℝ) ^ n * (R.mult x : ℝ))
        (⋃ i, G i '' B i) μHE[n] :=
      (hθint.mono_set (iUnion_subset hGBsub)).const_mul _
    refine hθint'.mono' ?_ ?_
    · exact (hΦsm.aestronglyMeasurable.congr hΦae.symm).mono_measure
        (Measure.restrict_mono hUsub le_rfl)
    · exact ae_restrict_of_ae_restrict_of_subset hUsub hΦbound
  -- countable additivity over the disjoint pieces, and the area formula on each piece
  have hpieces := hasSum_integral_iUnion hGBmeas hdisj hint
  have hterm : ∀ i, ∫ x in G i '' B i, Φ x ∂μHE[n] =
      ∫ u in B i, (w i u : ℝ) * ζ i u ((ω : DifferentialForm (Euclid P) n) (H i u)) ∂volume := by
    intro i
    have harea := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
      (hBmeas i) (fun x hx => (hdiff i x hx).1) (fun x hx => (hdiff i x hx).2) (hinj i) Φ
    rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume n] at harea
    rw [harea]
    refine setIntegral_congr_fun (hBmeas i) (fun u _ => ?_)
    simp only [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp, hΦdef, hζdef,
      hJdef, hHdef, hwdef, smul_eq_mul, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    ring
  simp_rw [hterm] at hpieces
  rw [hQ1, hQ2]
  exact hpieces.unique (hR' ω)
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
