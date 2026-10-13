<!-- theorem-id: gmt-ch08/root.first_rectifiability-a1 -->

## Theorem `Submission.first_rectifiability_theorem`

Let V be an n-varifold on open U ⊆ ℝ^N such that for μ_V-a.e. x there are T ∈ G(N,n) and θ with HasTangentPlane V x T θ (Def. 1.1: x ∈ U, θ > 0, V_{x,λ} → θ v(T) as λ ↓ 0 against C_c(ℝ^N × G)). Let M := {x ∈ spt μ_V : ∃ T θ', HasTangentPlane V x T θ'}. Then there is θ : ℝ^N → ℝ such that for every x ∈ M some T satisfies HasTangentPlane V x T (θ x), and IsVarifoldOf V M θ: M ⊆ U is H^n-null-measurable and countably n-rectifiable, θ > 0 on M, θ is H^n-integrable on M ∩ K for every compact K ⊆ U, and V(A) = ∫_{{x ∈ M : ∃ S, M has approximate tangent plane S at x w.r.t. θ (Ch. 3 1.7), (x,S) ∈ A}} θ dH^n for all Borel A. (Exactly FirstRectifiabilityTheorem.)

Node: `root.first_rectifiability-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/327, https://github.com/ZhengyangZhang06/gmt-formalize/issues/330

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/836, https://github.com/ZhengyangZhang06/gmt-formalize/issues/842, https://github.com/ZhengyangZhang06/gmt-formalize/issues/846, https://github.com/ZhengyangZhang06/gmt-formalize/issues/850, https://github.com/ZhengyangZhang06/gmt-formalize/issues/854, https://github.com/ZhengyangZhang06/gmt-formalize/issues/858, https://github.com/ZhengyangZhang06/gmt-formalize/issues/862, https://github.com/ZhengyangZhang06/gmt-formalize/issues/866, https://github.com/ZhengyangZhang06/gmt-formalize/issues/869, https://github.com/ZhengyangZhang06/gmt-formalize/issues/872, https://github.com/ZhengyangZhang06/gmt-formalize/issues/876, https://github.com/ZhengyangZhang06/gmt-formalize/issues/878

## Lean problem

Declaration: `Submission.first_rectifiability_theorem`

```lean
FirstRectifiabilityTheorem
```

### Frozen project context

`GMT/Ch08/Contract.lean` at `63436ae63eb6a2fd7525bef73c73cf88e2cd7e93` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.Submanifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 8 (printed pp. 205–224)

## Theory of General Varifolds — frozen contract

Ambient space `ℝ^{n+ℓ}` is `Euclidean N = EuclideanSpace ℝ (Fin N)` (so `N = n + ℓ`), `U` is an
open subset, and an `n`-varifold on `U` is `Poincare.SimonGMT.Chapter08.Varifold N n U`: a Borel
measure on `ℝ^N × G(N,n)` that vanishes off `U × G(N,n)` and is finite on `K × G(N,n)` for every
compact `K ⊆ U` (i.e. the zero extension of a Radon measure on `Gₙ(U)`).  `G(N,n)` is
`Grassmannian N n`, realized by orthogonal projection matrices (Simon's own metric on `G(n+ℓ,n)`
is the Frobenius distance of these matrices).  Reused, already verified SimonGMT notions:
`Varifold.weight` (`μ_V = π_# V`), `Varifold.firstVariation` (`δV(X) = ∫ div_S X dV`, 2.3),
`Varifold.TestVectorField U` (`K(U;ℝ^{n+ℓ})`: compactly supported `C¹` fields with support in `U`),
`Varifold.firstVariationNormOn` (the supremum in 2.5), `Varifold.HasLocallyBoundedFirstVariation`,
`Varifold.IsFirstVariationMeasure` (characterization 2.5 of `‖δV‖`), `Varifold.Stationary`,
`Varifold.RadonConverges` (convergence as Radon measures on `Gₙ(U)`), `Varifold.pushforwardMeasure`
(formula 2.1), `Chapter03.CountablyRectifiable`, `Chapter03.HasWeightedApproximateTangentSpaceAt`
(Ch. 3, 1.7), `Chapter02.IsSimonSubmanifold` (Ch. 2, §4).  `H^n` is Mathlib's `μHE[n]` (normalized
so that it agrees with Lebesgue measure on `n`-planes, as Simon's `H^n` does).
Simon's `B_ρ(x)` is the closed ball `Metric.closedBall x ρ`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal CompactlySupported Pointwise

namespace GMT.Ch08

open Poincare.SimonGMT
open Poincare.SimonGMT.Chapter08

section Definitions

variable {N n : ℕ} {U : Set (Euclidean N)}

/-- `ω_n`, the volume of the unit ball of `ℝ^n` (Simon Ch. 1; `ω_0 = 1`). -/
noncomputable def unitBallVolume (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The density quotient `μ(B_ρ(x)) / (ω_n ρ^n)` (Simon Ch. 1, 3.1), closed balls. -/
noncomputable def densityRatio (n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (ρ : ℝ) :
    ℝ≥0∞ :=
  μ (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal ρ ^ n)

/-- `Θ^n(μ, x)` exists and equals `θ ∈ [0, ∞]`: `lim_{ρ↓0} μ(B_ρ(x))/(ω_n ρ^n) = θ`
(Simon Ch. 1, 3.1; used throughout Ch. 8 with `μ = μ_V`). -/
def HasDensity (n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞) : Prop :=
  Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 θ)

/-- Simon's `W ⊂⊂ U` for open `W`: `W` is open with compact closure contained in `U`. -/
def IsRelCompactOpenIn (W U : Set (Euclidean N)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- `‖δV‖`, the total variation measure of `δV` (Simon Ch. 8, 2.5, p. 209), zero-extended off `U`.
When `V` has locally bounded first variation this is SimonGMT's Riesz construction
`firstVariationRieszMeasure`, which is proved (`Varifold.isFirstVariationMeasure_riesz`) to be locally
finite on `U` with `‖δV‖(W) = sup {|δV(X)| : X ∈ K(U;ℝ^N), |X| ≤ 1, spt X ⊆ W}` for every open
`W ⊂⊂ U`; such a Radon measure is unique.  It is only used under that hypothesis. -/
noncomputable def variationMeasure (V : Varifold N n U) : Measure (Euclidean N) :=
  open Classical in
  if h : V.HasLocallyBoundedFirstVariation then V.firstVariationRieszMeasure h else 0

/-- `D_{μ_V} ‖δV‖ (x) = lim_{ρ↓0} ‖δV‖(B_ρ(x)) / μ_V(B_ρ(x))` (Simon Ch. 8, 2.7), taken as the
`limsup` so that it is defined everywhere (it is a genuine limit `μ_V`-a.e.). -/
noncomputable def variationDensity (V : Varifold N n U) (x : Euclidean N) : ℝ≥0∞ :=
  limsup (fun ρ : ℝ ↦ variationMeasure V (closedBall x ρ) / V.weight (closedBall x ρ)) (𝓝[>] 0)

/-- The generalized boundary `Z = {x ∈ U : D_{μ_V}‖δV‖(x) = +∞}` (Simon Ch. 8, 2.9). -/
def generalizedBoundary (V : Varifold N n U) : Set (Euclidean N) :=
  U ∩ {x | variationDensity V x = ∞}

/-- The generalized boundary measure `σ = ‖δV‖ ⌞ Z` (Simon Ch. 8, 2.9). -/
noncomputable def generalizedBoundaryMeasure (V : Varifold N n U) : Measure (Euclidean N) :=
  (variationMeasure V).restrict (generalizedBoundary V)

/-- The generalized mean curvature `H = (D_{μ_V}‖δV‖) ν` (Simon Ch. 8, 2.8), for a given
polar field `ν` of `δV` (the real factor is set to `0` where the density is `+∞`, a `μ_V`-null set). -/
noncomputable def generalizedMeanCurvature (V : Varifold N n U) (ν : Euclidean N → Euclidean N)
    (x : Euclidean N) : Euclidean N :=
  (variationDensity V x).toReal • ν x

/-- `∫_{Gₙ(A)} r^{-n-2} |p_{S^⊥}(y - x)|² dV(y,S)` with `r = |y - x|` (the defect term in Simon
Ch. 8, 3.3–3.4); here `p_{S^⊥}(v) = v - p_S(v)`. -/
noncomputable def normalDefect (V : Varifold N n U) (x : Euclidean N) (A : Set (Euclidean N)) :
    ℝ≥0∞ :=
  ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)),
    ENNReal.ofReal (‖(z.1 - x) - Grassmannian.project z.2 (z.1 - x)‖ ^ 2 / ‖z.1 - x‖ ^ (n + 2))
    ∂V.measure

/-- The rescaled varifold `V_{x,λ} = η_{x,λ #} V` (Simon Ch. 8, 1.1 and 5.1), as a measure on
`ℝ^N × G(N,n)`: `V_{x,λ}(A) = λ^{-n} V({(λy + x, S) : (y,S) ∈ A} ∩ Gₙ(U))`. -/
noncomputable def rescaledMeasure (V : Varifold N n U) (x : Euclidean N) (t : ℝ) :
    Measure (Euclidean N × Grassmannian N n) :=
  ENNReal.ofReal (t⁻¹ ^ n) • V.measure.map (fun z ↦ (t⁻¹ • (z.1 - x), z.2))

/-- The varifold `v(T)` of an `n`-plane `T` with multiplicity one:
`v(T)(A) = H^n({y ∈ T : (y, T) ∈ A})`. -/
noncomputable def planeVarifoldMeasure (T : Grassmannian N n) :
    Measure (Euclidean N × Grassmannian N n) :=
  ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))).map (fun y ↦ (y, T))

/-- Simon Ch. 8, Definition 1.1 (p. 206): `V` has tangent space `T` with multiplicity
`θ ∈ (0,∞)` at `x ∈ U`, i.e. `lim_{λ↓0} V_{x,λ} = θ v(T)` as Radon measures on `Gₙ(ℝ^{n+ℓ})`. -/
def HasTangentPlane (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ) :
    Prop :=
  x ∈ U ∧ 0 < θ ∧
    ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
      Tendsto (fun t : ℝ ↦ ∫ z, f z ∂(rescaledMeasure V x t)) (𝓝[>] 0)
        (𝓝 (θ * ∫ z, f z ∂(planeVarifoldMeasure T)))

/-- Convergence in the sense of Radon measures on `Gₙ(ℝ^{n+ℓ})`: convergence of integrals of
every continuous compactly supported function. -/
def VagueConverges (μs : ℕ → Measure (Euclidean N × Grassmannian N n))
    (μ : Measure (Euclidean N × Grassmannian N n)) : Prop :=
  ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
    Tendsto (fun j ↦ ∫ z, f z ∂(μs j)) atTop (𝓝 (∫ z, f z ∂μ))

/-- Simon Ch. 8, Definition 5.4 (p. 215): `C ∈ VarTan(V, x)`, i.e. `C = lim_j η_{x,λ_j #} V`
(Radon measures on `Gₙ(ℝ^{n+ℓ})`) for some `λ_j > 0`, `λ_j → 0`. -/
def IsVarifoldTangent (V : Varifold N n U) (x : Euclidean N)
    (C : Varifold N n (univ : Set (Euclidean N))) : Prop :=
  ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧ Tendsto t atTop (𝓝 0) ∧
    VagueConverges (fun j ↦ rescaledMeasure V x (t j)) C.measure

/-- `V = v(M, θ)` (Simon Ch. 8, p. 206, with Ch. 4 §1 and Ch. 3, 1.7): `M ⊆ U` is
`H^n`-measurable and countably `n`-rectifiable, `θ > 0` on `M` is locally `H^n`-integrable in `U`, and
`V(A) = μ(π(TM ∩ A))` for Borel `A`, where `μ = H^n ⌞ θ`, `TM = {(x, T_x M) : x ∈ M_*}` and `M_*`
is the set of `x ∈ M` at which `M` has an approximate tangent space `T_x M` with respect to `θ`.
No tangent field is supplied as data: `T_x M` is the (unique, as `θ(x) > 0`) plane satisfying
Ch. 3, 1.7. -/
def IsVarifoldOf (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) : Prop :=
  M ⊆ U ∧ NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) ∧
    Chapter03.CountablyRectifiable n M ∧ (∀ x ∈ M, 0 < θ x) ∧
    (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μHE[n]) ∧
    ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A →
      V.measure A =
        ∫⁻ x in {x | x ∈ M ∧ ∃ S : Grassmannian N n,
            Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ∧ (x, S) ∈ A},
          ENNReal.ofReal (θ x) ∂μHE[n]

/-- `V` is an `n`-rectifiable varifold: `V = v(M, θ)` for some `M`, `θ` as in `IsVarifoldOf`
(Simon Ch. 8, p. 206 and 5.5). -/
def IsRectifiable (V : Varifold N n U) : Prop :=
  ∃ (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf V M θ

/-- `V` is an integer multiplicity (integral) rectifiable `n`-varifold: `V = v(M, θ)` with `θ`
integer-valued `H^n`-a.e. on `M` (Simon Ch. 4 §1, Ch. 8, 5.9). -/
def IsIntegral (V : Varifold N n U) : Prop :=
  ∃ (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf V M θ ∧
    ∀ᵐ x ∂((μHE[n] : Measure (Euclidean N)).restrict M), ∃ k : ℕ, θ x = k

/-- The classical tangent space `T_y M` of a `C¹` submanifold (Simon Ch. 2, §4, p. 55): velocities
`γ'(0)` of `C¹` curves `γ : (-1,1) → M` with `γ(0) = y`. -/
def classicalTangentSpace (M : Set (Euclidean N)) (y : Euclidean N) : Set (Euclidean N) :=
  {ξ | ∃ γ : ℝ → Euclidean N, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ ξ 0}

end Definitions

/-- **Simon Ch. 8, 1.2 (First Rectifiability Theorem), p. 206.**
If an `n`-varifold `V` on `U` has a tangent space `T_x` with multiplicity `θ(x) ∈ (0,∞)` (in the
sense of 1.1) at `μ_V`-a.e. `x ∈ U`, then `V` is `n`-rectifiable; in fact, for the set
`M = {x ∈ spt μ_V : T_x and θ(x) both exist}` and the multiplicity function `θ`, `M` is
`H^n`-measurable and countably `n`-rectifiable, `θ` is locally `H^n`-integrable on `M`, and
`V = v(M, θ)`. (`spt V` is read as `spt μ_V`.) -/
def FirstRectifiabilityTheorem : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U),
    (∀ᵐ x ∂V.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ) →
    ∃ θ : Euclidean N → ℝ,
      (∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
          HasTangentPlane V x T θ'}, ∃ T : Grassmannian N n, HasTangentPlane V x T (θ x)) ∧
      IsVarifoldOf V {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
          HasTangentPlane V x T θ'} θ

/-- **Simon Ch. 8, 2.2–2.4 (first variation of a general varifold), pp. 208–209.**
Let `φ : (-1,1) × U → U` be a `C²` one-parameter family as in Ch. 2, 5.1/5.6: `φ_0 = id`, each
`φ_t` maps `U` injectively into `U` (a diffeomorphism of `U` onto itself in the book; injectivity
is all that is used), and `φ_t = id` on `U ∖ K` for a fixed compact `K ⊆ U`; let `X = ∂φ/∂t|_{t=0}`.
Then `t ↦ M(φ_{t#} V ⌞ Gₙ(K))` (with `φ_{t#}V` as in 2.1) is differentiable at `0` with derivative
`δV(X) = ∫ div_S X dV(x,S)` (2.2 = 2.3), and `div_S X = Σ_i τ_i · D_{τ_i} X` for every orthonormal
basis `τ_1,…,τ_n` of `S` (2.4). -/
def FirstVariationIsMassDerivative : Prop :=
  (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U)
      (φ : ℝ × Euclidean N → Euclidean N) (K : Set (Euclidean N)) (X : Euclidean N → Euclidean N),
      IsCompact K → K ⊆ U →
      ContDiffOn ℝ 2 φ (Ioo (-1 : ℝ) 1 ×ˢ U) →
      (∀ x ∈ U, φ (0, x) = x) →
      (∀ t ∈ Ioo (-1 : ℝ) 1, MapsTo (fun x ↦ φ (t, x)) U U ∧ InjOn (fun x ↦ φ (t, x)) U) →
      (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → φ (t, x) = x) →
      (∀ x ∈ U, HasDerivAt (fun t ↦ φ (t, x)) (X x) 0) →
      HasDerivAt
        (fun t : ℝ ↦ (V.pushforwardMeasure (fun x ↦ φ (t, x))
          (K ×ˢ (univ : Set (Grassmannian N n)))).toReal)
        (V.firstVariation X) 0) ∧
  (∀ (N n : ℕ) (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
      (b : OrthonormalBasis (Fin n) ℝ S.plane),
      Varifold.tangentialDivergence X x S =
        ∑ i, inner ℝ (b i : Euclidean N) ((fderiv ℝ X x) (b i : Euclidean N)))

/-- **Simon Ch. 8, 2.5–2.10 (total variation, mean curvature, generalized boundary), pp. 209–210.**
If `V` has locally bounded first variation in `U`, then: `‖δV‖` is a Radon measure on `U`
characterized by 2.5; there is a Borel field `ν` with `|ν| = 1` `‖δV‖`-a.e. and
`δV(X) = -∫ ν·X d‖δV‖` (2.6); `D_{μ_V}‖δV‖(x)` exists and is finite for `μ_V`-a.e. `x` (2.7);
`Z = {D_{μ_V}‖δV‖ = ∞}` has `μ_V(Z) = 0` (2.9); and with `H = (D_{μ_V}‖δV‖) ν`, `σ = ‖δV‖⌞Z`,
`δV(X) = -∫ H·X dμ_V - ∫_Z ν·X dσ` for all `X ∈ K(U;ℝ^{n+ℓ})` (2.8, 2.10), all integrals being
absolutely convergent. -/
def FirstVariationRepresentation : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U),
    V.HasLocallyBoundedFirstVariation →
      V.IsFirstVariationMeasure (variationMeasure V) ∧
      (∀ᵐ x ∂V.weight, variationDensity V x ≠ ∞ ∧
        Tendsto (fun ρ : ℝ ↦ variationMeasure V (closedBall x ρ) / V.weight (closedBall x ρ))
          (𝓝[>] 0) (𝓝 (variationDensity V x))) ∧
      V.weight (generalizedBoundary V) = 0 ∧
      ∃ ν : Euclidean N → Euclidean N, Measurable ν ∧
        (∀ᵐ x ∂(variationMeasure V), ‖ν x‖ = 1) ∧
        ∀ X : Varifold.TestVectorField U,
          Integrable (fun x ↦ inner ℝ (ν x) (X x)) (variationMeasure V) ∧
          V.firstVariation X = -∫ x, inner ℝ (ν x) (X x) ∂(variationMeasure V) ∧
          Integrable (fun x ↦ inner ℝ (generalizedMeanCurvature V ν x) (X x)) V.weight ∧
          Integrable (fun x ↦ inner ℝ (ν x) (X x)) (generalizedBoundaryMeasure V) ∧
          V.firstVariation X =
            -(∫ x, inner ℝ (generalizedMeanCurvature V ν x) (X x) ∂V.weight) -
              ∫ x, inner ℝ (ν x) (X x) ∂(generalizedBoundaryMeasure V)

/-- **Simon Ch. 8, 3.3 (monotonicity with `‖δV‖ ≤ Λ μ_V`), p. 210.**
Let `V` have locally bounded first variation in `U`, `x ∈ U`, `0 < ρ₀` with `B_{ρ₀}(x) ⊆ U`
(the book's `ρ₀ < dist(x, ∂U)`), `Λ ≥ 0`, and `‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for `0 < ρ < ρ₀` (3.1).
Then `e^{Λρ} ρ^{-n} μ_V(B_ρ(x))` is increasing on `(0, ρ₀)`, `Θ^n(μ_V, x)` exists (and is finite),
and for `0 < σ ≤ ρ < ρ₀`:
`Θ^n(μ_V,x) ≤ e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))` and
`e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x)) + ω_n^{-1} ∫_{Gₙ(B_ρ(x) ∖ B_σ(x))} r^{-n-2}|p_{S^⊥}(y-x)|² dV
  ≤ e^{Λρ} ω_n^{-1} ρ^{-n} μ_V(B_ρ(x))` (the book's subtraction, rearranged; all terms finite). -/
def MonotonicityFormula : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ₀ Λ : ℝ),
    V.HasLocallyBoundedFirstVariation → 0 < ρ₀ → ball x ρ₀ ⊆ U → 0 ≤ Λ →
    (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      variationMeasure V (closedBall x ρ) ≤ ENNReal.ofReal Λ * V.weight (closedBall x ρ)) →
    MonotoneOn (fun ρ : ℝ ↦
        ENNReal.ofReal (Real.exp (Λ * ρ)) * V.weight (closedBall x ρ) / ENNReal.ofReal ρ ^ n)
      (Ioo 0 ρ₀) ∧
    ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ θ ≠ ∞ ∧
      ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ →
        θ ≤ ENNReal.ofReal (Real.exp (Λ * σ)) * densityRatio n V.weight x σ ∧
        ENNReal.ofReal (Real.exp (Λ * σ)) * densityRatio n V.weight x σ +
            (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ \ closedBall x σ) ≤
          ENNReal.ofReal (Real.exp (Λ * ρ)) * densityRatio n V.weight x ρ

/-- **Simon Ch. 8, 3.4 (monotonicity identity, `Λ = 0`), p. 211.**
If `B_{ρ₀}(x) ⊆ U` and `V` is stationary in `B_{ρ₀}(x)` (`δV(X) = 0` whenever `spt X ⊆ B_{ρ₀}(x)`),
then `Θ^n(μ_V, x)` exists and for `0 < ρ < ρ₀`
`Θ^n(μ_V,x) = ω_n^{-1} ρ^{-n} μ_V(B_ρ(x)) - ω_n^{-1} ∫_{Gₙ(B_ρ(x))} r^{-n-2}|p_{S^⊥}(y-x)|² dV`
(stated additively; all terms are finite).  The section's global hypothesis of locally bounded first
variation is not needed and is omitted. -/
def StationaryMonotonicityIdentity : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ₀ : ℝ),
    0 < ρ₀ → ball x ρ₀ ⊆ U →
    (∀ X : Varifold.TestVectorField U, tsupport X.toFun ⊆ ball x ρ₀ → V.firstVariation X = 0) →
    ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        θ + (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ) =
          densityRatio n V.weight x ρ

/-- **Simon Ch. 8, 3.6 (Lemma), p. 211.**
If `V` has locally bounded first variation in `U`, then `Θ^n(μ_V, x)` exists and is real-valued for
`μ_V`-a.e. `x ∈ U`, and `x ↦ Θ^n(μ_V, x)` is `μ_V`-measurable (it agrees `μ_V`-a.e. with a Borel
function).  (The "in fact" clause — existence wherever `‖δV‖(B_ρ(x)) ≤ Λ(x) μ_V(B_ρ(x))` for small
`ρ` — is the density part of `MonotonicityFormula`.) -/
def DensityExistsAE : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U),
    V.HasLocallyBoundedFirstVariation →
    ∃ Θ : Euclidean N → ℝ≥0∞, Measurable Θ ∧
      ∀ᵐ x ∂V.weight, Θ x ≠ ∞ ∧ HasDensity n V.weight x (Θ x)

/-- **Simon Ch. 8, 3.7 (semi-continuity of `Θ^n` under varifold convergence), p. 211.**
Suppose `V_i → V` as Radon measures on `Gₙ(U)`, each `V_i` has locally bounded first variation with
`liminf_i ‖δV_i‖(W) < ∞` for each `W ⊂⊂ U`, and `Θ^n(μ_{V_i}, y) ≥ 1` for `y ∈ U ∖ B_i`, where
`μ_{V_i}(B_i ∩ W) → 0` for each `W ⊂⊂ U`.  Then `V` has locally bounded first variation,
`‖δV‖(W) ≤ liminf_i ‖δV_i‖(W)` for each open `W ⊂⊂ U`, and `Θ^n(μ_V, y) ≥ 1` for `μ_V`-a.e. `y`. -/
def DensitySemicontinuity : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U)
    (B : ℕ → Set (Euclidean N)),
    Varifold.RadonConverges Vi V →
    (∀ i, (Vi i).HasLocallyBoundedFirstVariation) →
    (∀ W, IsRelCompactOpenIn W U → liminf (fun i ↦ variationMeasure (Vi i) W) atTop ≠ ∞) →
    (∀ i, ∀ y ∈ U \ B i, ∃ θ : ℝ≥0∞, HasDensity n (Vi i).weight y θ ∧ 1 ≤ θ) →
    (∀ W, IsRelCompactOpenIn W U → Tendsto (fun i ↦ (Vi i).weight (B i ∩ W)) atTop (𝓝 0)) →
    V.HasLocallyBoundedFirstVariation ∧
    (∀ W, IsRelCompactOpenIn W U →
      variationMeasure V W ≤ liminf (fun i ↦ variationMeasure (Vi i) W) atTop) ∧
    ∀ᵐ y ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ 1 ≤ θ

/-- **Simon Ch. 8, 4.1 (Constancy Theorem), p. 213 — corrected.**
Suppose `V` is stationary in `U`, `U ∩ spt μ_V ⊆ M` where `M` is an `n`-dimensional `C²` submanifold
of `ℝ^{n+ℓ}` (Ch. 2, §4) and **`M ∩ U` is connected**.  Then `V = θ₀ v(M ∩ U)` for a constant
`θ₀ ≥ 0`, i.e. `V(A) = θ₀ H^n({x ∈ M ∩ U : (x, T_x M) ∈ A})` for Borel `A`.
Erratum: the book assumes only that `M` is connected; that version is false (SimonGMT
`ConstancyDomainCounterexample.counterexample_constancy_printed_hypotheses`: `U = ℝ ∖ {0}`,
`M = ℝ`, `V = v((0,∞))`).  The book's proof uses connectedness of `M ∩ U`. -/
def ConstancyTheorem : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)),
    V.Stationary →
    Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M →
    U ∩ V.weight.support ⊆ M →
    IsPreconnected (M ∩ U) →
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A →
        V.measure A = ENNReal.ofReal θ₀ *
          (μHE[n] : Measure (Euclidean N))
            {x | x ∈ M ∩ U ∧ ∃ S : Grassmannian N n,
              (S.plane : Set (Euclidean N)) = classicalTangentSpace M x ∧ (x, S) ∈ A}

/-- **Simon Ch. 8, 5.1–5.4 (varifold tangents), p. 215 — with corrected 5.2 and 5.3.**
Let `V` have locally bounded first variation in `U`, `x ∈ U`, `Θ^n(μ_V, x) = θ₀ ∈ (0,∞)` and
`lim_{ρ↓0} ρ^{1-n} ‖δV‖(B_ρ(x)) = 0` (5.1).  Then (a) every sequence `λ_j ↓ 0` has a subsequence
along which `η_{x,λ_j #} V` converges as Radon measures to some varifold `C` on `ℝ^{n+ℓ}`; and
(b) every such limit `C` (`C ∈ VarTan(V,x)`) is stationary in `ℝ^{n+ℓ}`, satisfies
`μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for all `ρ > 0` (5.2), and `μ_C(s A) = s^n μ_C(A)` for all `s > 0` and
`A ⊆ ℝ^{n+ℓ}` (5.3).
Errata: 5.2 prints `μ_C(B_ρ(x))`; the centre must be `0`.  5.3 prints
`λ^{-n} μ_C(η_{0,λ}(A)) = μ_C(A)` with `η_{0,λ}(y) = λ^{-1}y`, which has the wrong power; the
correct homogeneity is `λ^{n} μ_C(η_{0,λ}(A)) = μ_C(A)`, i.e. `μ_C(sA) = s^n μ_C(A)` (SimonGMT
`TangentScalingCounterexample`). -/
def VarifoldTangentCones : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ),
    V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < θ₀ →
    HasDensity n V.weight x (ENNReal.ofReal θ₀) →
    Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) /
      ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
    (∀ t : ℕ → ℝ, (∀ j, 0 < t j) → Tendsto t atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Varifold N n (univ : Set (Euclidean N)),
        VagueConverges (fun j ↦ rescaledMeasure V x (t (φ j))) C.measure) ∧
    ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
      C.Stationary ∧
      (∀ ρ : ℝ, 0 < ρ →
        C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n) ∧
      ∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A

/-- **Simon Ch. 8, 5.7 (Corollary), p. 216.**
If `x ∈ U` satisfies 5.1 (with `V` of locally bounded first variation) and
`lim_{ρ↓0} ρ^{-n} μ_V({y ∈ B_ρ(x) : Θ^n(μ_V, y) < 1}) = 0`, then every `C ∈ VarTan(V, x)` is
rectifiable and `η_{0,λ #} C = C` for all `λ > 0` (tangent cones are rectifiable cones).
Here `{Θ^n(μ_V, y) < 1}` is read as the set where `Θ^n(μ_V, y) ≥ 1` fails (it differs from the set
where `Θ^n` exists and is `< 1` by a `μ_V`-null set, by 3.6). -/
def TangentConesAreRectifiableCones : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ),
    V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < θ₀ →
    HasDensity n V.weight x (ENNReal.ofReal θ₀) →
    Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) /
      ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧
        ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ 1 ≤ θ} / ENNReal.ofReal ρ ^ n)
      (𝓝[>] 0) (𝓝 0) →
    ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
      IsRectifiable C ∧ ∀ s : ℝ, 0 < s → rescaledMeasure C 0 s = C.measure

/-- **Simon Ch. 8, 5.5 (Allard's Rectifiability Theorem), p. 215, with Remark 5.6.**
If `V` has locally bounded first variation in `U` and `Θ^n(μ_V, x) > 0` for `μ_V`-a.e. `x ∈ U`,
then `V` is an `n`-rectifiable varifold (`V = v(M, θ)`); moreover (5.6) `V` has a tangent plane
with positive multiplicity in the sense of 1.1 at `μ_V`-a.e. `x`. -/
def AllardRectifiabilityTheorem : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U),
    V.HasLocallyBoundedFirstVariation →
    (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 0 < θ) →
    IsRectifiable V ∧ ∀ᵐ x ∂V.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ

/-- **Simon Ch. 8, 5.8 (Compactness Theorem for rectifiable `n`-varifolds), p. 218.**
Let `V_j` be rectifiable `n`-varifolds in `U` with locally bounded first variation,
`sup_j (μ_{V_j}(W) + ‖δV_j‖(W)) < ∞` for each `W ⊂⊂ U`, and `Θ^n(μ_{V_j}, x) ≥ 1` on `U ∖ A_j`
where `μ_{V_j}(A_j ∩ W) → 0` for each `W ⊂⊂ U`.  Then there are a subsequence `V_{j'}` and a
rectifiable varifold `V` with locally bounded first variation in `U` such that `V_{j'} → V` as Radon
measures on `Gₙ(U)`, `Θ^n(μ_V, x) ≥ 1` for `μ_V`-a.e. `x`, and `‖δV‖(W) ≤ liminf_{j'} ‖δV_{j'}‖(W)`
for each open `W ⊂⊂ U` (the `liminf` is along the subsequence, as in the book's proof). -/
def CompactnessTheorem : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vj : ℕ → Varifold N n U) (A : ℕ → Set (Euclidean N)),
    (∀ j, IsRectifiable (Vj j)) →
    (∀ j, (Vj j).HasLocallyBoundedFirstVariation) →
    (∀ W, IsRelCompactOpenIn W U →
      ⨆ j, ((Vj j).weight W + variationMeasure (Vj j) W) ≠ ∞) →
    (∀ j, ∀ x ∈ U \ A j, ∃ θ : ℝ≥0∞, HasDensity n (Vj j).weight x θ ∧ 1 ≤ θ) →
    (∀ W, IsRelCompactOpenIn W U → Tendsto (fun j ↦ (Vj j).weight (A j ∩ W)) atTop (𝓝 0)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Varifold N n U,
      Varifold.RadonConverges (fun j ↦ Vj (φ j)) V ∧
      IsRectifiable V ∧ V.HasLocallyBoundedFirstVariation ∧
      (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 1 ≤ θ) ∧
      ∀ W, IsRelCompactOpenIn W U →
        variationMeasure V W ≤ liminf (fun j ↦ variationMeasure (Vj (φ j)) W) atTop

/-- **Simon Ch. 8, 5.9 (Allard's Integral Compactness Theorem), p. 218.**
If the `V_j` are integer multiplicity rectifiable `n`-varifolds in `U` with locally bounded first
variation and `sup_j (μ_{V_j}(W) + ‖δV_j‖(W)) < ∞` for each `W ⊂⊂ U`, then some subsequence converges
as Radon measures on `Gₙ(U)` to an integer multiplicity `V` with locally bounded first variation and
`‖δV‖(W) ≤ liminf_{j'} ‖δV_{j'}‖(W)` for open `W ⊂⊂ U`; moreover every limit (as Radon measures on
`Gₙ(U)`) of a subsequence of the `V_j` is integer multiplicity. -/
def IntegralCompactnessTheorem : Prop :=
  ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vj : ℕ → Varifold N n U),
    (∀ j, IsIntegral (Vj j)) →
    (∀ j, (Vj j).HasLocallyBoundedFirstVariation) →
    (∀ W, IsRelCompactOpenIn W U →
      ⨆ j, ((Vj j).weight W + variationMeasure (Vj j) W) ≠ ∞) →
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Varifold N n U,
      Varifold.RadonConverges (fun j ↦ Vj (φ j)) V ∧
      IsIntegral V ∧ V.HasLocallyBoundedFirstVariation ∧
      ∀ W, IsRelCompactOpenIn W U →
        variationMeasure V W ≤ liminf (fun j ↦ variationMeasure (Vj (φ j)) W) atTop) ∧
    ∀ (φ : ℕ → ℕ) (V : Varifold N n U), StrictMono φ →
      Varifold.RadonConverges (fun j ↦ Vj (φ j)) V → IsIntegral V

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.first_rectifiability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Theorem 1.2 and its printed proof (p. 208), which uses Lemma 1.3 (sibling plane_disintegration) and “1.9 of Ch. 3”. ERRATUM: the printed line “η_V^(x)(β) = θ(x)β(T_x)” must read “η_V^(x)(β) = β(T_x)” (the averages in 1.3 are normalised by μ_V(B_ρ(x)), so the multiplicity cancels; the printed (1) is consistent only with the corrected value). GAP FILLED: Ch. 3, 1.9 presupposes an H^n-measurable set M and a positive locally H^n-integrable θ, whereas here only the measure μ_V is given, and the proof of 1.9 rests on both directions of Ch. 3, Theorem 1.6, neither of which is available in the pinned library. “By 1.9 of Ch. 3” is therefore expanded into Steps 2–6 below: Step 2 is the Lipschitz-graph (cone) argument of the printed proof of Ch. 3, 1.6 “⇐”, supplied by the sibling tangent_graph_cover (with L = 1); Steps 3–4 are the comparison and measurability arguments (Ch. 1, 3.3); Step 5 proves the density-one property of H^n on the carrier — the part of Ch. 3, 1.6 “⇒”/Remark 1.5(3) that is used here — directly from Lipschitz graphs of arbitrarily small slope (sibling tangent_graph_cover with L → 0), using only Lipschitz image bounds for H^n and the Lebesgue density theorem (no area formula, no Jacobians); Step 6 identifies μ_V = θ H^n ⌞ M by the Besicovitch differentiation / Radon–Nikodym theorem (Ch. 1, 3.23–3.24). “spt V” is read as spt μ_V (contract docstring). Notation: μ := μ_V = V.weight (σ-finite by Varifold.weight.instSigmaFinite; finite on compact subsets of U by V.finite_on_compact; μ(Uᶜ) = 0 by V.supported); G := Grassmannian N n (a compact metric space); p_S := Grassmannian.project S and ‖p_S − p_{S'}‖ the operator norm; H^n := μHE[n] (for natural n this is Simon's normalised H^n: SimonGMT simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, Chapter02/AreaLiteral.lean:42); B_r(x) := closedBall x r; V_{x,t} := rescaledMeasure V x t; v(T) := planeVarifoldMeasure T; ω_n := unitBallVolume n ∈ (0,∞) (ω_0 = 1); L^n := Lebesgue measure (volume) on ℝ^n = EuclideanSpace ℝ (Fin n). Compact exhaustion: K_p := {x : |x| ≤ p, dist(x, ℝ^N ∖ U) ≥ 1/p} (K_p := B_p(0) if U = ℝ^N, as Lean's infDist to ∅ is 0), so each K_p is compact, K_p ⊆ interior K_{p+1}, and ∪_p K_p = U.

Statement. Suppose for μ-a.e. x there are T ∈ G and θ ∈ ℝ with HasTangentPlane V x T θ (Def. 1.1: x ∈ U, θ > 0, V_{x,t} → θ v(T) against C_c(ℝ^N × G) as t ↓ 0). Let M := {x ∈ spt μ : ∃ T θ', HasTangentPlane V x T θ'}. Then there is θ : ℝ^N → ℝ with HasTangentPlane V x T (θ x) for some T at every x ∈ M, and IsVarifoldOf V M θ.

STEP 0 (consequences of Def. 1.1 at a point; uniqueness). Let HasTangentPlane V x T θ.
 (0a) x ∈ U and θ > 0 (definition).
 (0b) Weight blow-ups: for every g ∈ C_c(ℝ^N), t^{−n}∫ g((z − x)/t) dμ(z) → θ∫_{T.plane} g dH^n as t ↓ 0. (Test Def. 1.1 with f(y,S) := g(y), which is in C_c(ℝ^N × G) because G is compact; ∫ f dV_{x,t} = t^{−n}∫ g((z − x)/t) dμ(z) by Measure.map / integral_map and μ = V.measure.map Prod.fst, and ∫ f dv(T) = ∫_{T.plane} g dH^n.)
 (0c) Density: HasDensity n μ x θ, i.e. μ(B_t(x))/(ω_nt^n) → θ. Indeed H^n⌞T.plane is the image of L^n under a linear isometry of ℝ^n onto T.plane (Mathlib Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so H^n(T.plane ∩ B_κ(0)) = ω_nκ^n for κ > 0. Testing (0b) with g ∈ C_c, 0 ≤ g ≤ 1, g = 1 on B_κ(0), tsupport g ⊆ B_1(0) (κ < 1) gives liminf_t t^{−n}μ(B_t(x)) ≥ θω_nκ^n; testing with g = 1 on B_1(0), tsupport g ⊆ B_κ(0) (κ > 1) gives limsup_t t^{−n}μ(B_t(x)) ≤ θω_nκ^n; let κ → 1. In particular μ(B_t(x)) > 0 for every t > 0, so x ∈ spt μ; hence M = {x : ∃ T θ', HasTangentPlane V x T θ'}.
 (0d) Uniqueness: if also HasTangentPlane V x T' θ', then θ = θ' (both equal the density by (0c)), and θH^n⌞T.plane = θ'H^n⌞T'.plane as measures (both are the vague limit of the same weight blow-ups by (0b); they are locally finite Borel measures on ℝ^N, so Measure.ext_of_integral_eq_on_compactlySupported applies). Hence H^n⌞T.plane = H^n⌞T'.plane; their supports are T.plane and T'.plane (SimonGMT Chapter03.support_euclideanHausdorffMeasure_restrict_submodule), so T.plane = T'.plane and T = T' (Grassmannian.eq_of_plane_eq). For x ∈ M let θ(x) > 0 and T(x) ∈ G be these unique values, and put θ(x) := 0 for x ∉ M. Then HasTangentPlane V x T(x) (θ x) for every x ∈ M (the first conclusion), θ > 0 on M, and M ⊆ U.
 (0e) μ(ℝ^N ∖ M) = 0 (outer measure): ℝ^N ∖ M = {x : ¬∃ T θ, HasTangentPlane V x T θ}, which is μ-null by hypothesis.
 (0f) Borel representative of θ: for r > 0, x ↦ μ(B_r(x)) is Borel (Tonelli for the s-finite μ; SimonGMT Chapter01.measurable_closedBall_mass_of_sFinite), so Θ̂(x) := liminf_{k→∞} densityRatio n μ x (1/(k+1)) is a Borel function ℝ^N → [0,∞], and by (0c), θ(x) = (Θ̂(x)).toReal for every x ∈ M.

STEP 1 (degenerate dimensions). If n > N then G = ∅, so V.measure = 0 (a measure on the empty space ℝ^N × ∅), μ = 0 and M = ∅; IsVarifoldOf V ∅ θ holds trivially (∅ ⊆ U, ∅ is null-measurable, countably rectifiable by countablyRectifiable_of_measure_zero, positivity and integrability are vacuous, and both sides of the identity are 0). If n = 0: by (0c) (ω_0 = 1, t^0 = 1), μ({x}) = lim_{t↓0} μ(B_t(x)) = θ(x) > 0 for x ∈ M (μ(B_t(x)) < ∞ for small t as x ∈ U), so M consists of atoms of the σ-finite measure μ and is countable; hence M is Borel, CountablyRectifiable 0 M (each point is the range of a constant map ℝ^0 → ℝ^N, with M₀ = ∅), and by (0e) μ = Σ_{x∈M} θ(x)δ_x = θ H^0⌞M (μHE[0] = μH[0] is the counting measure, Mathlib euclideanHausdorffMeasure_zero); in particular for compact K ⊆ U, ∫_{M∩K} θ dH^0 = μ(M ∩ K) ≤ μ(K) < ∞, and every μ-null subset of M is empty. Steps 7–9 below then apply verbatim, with “Step 6” replaced by this paragraph. Assume n ≥ 1 in Steps 2–6.

STEP 2 (countable rectifiability; printed “M is … countably n-rectifiable”). G is compact and S ↦ p_S is continuous into the operators, so there are P_1, …, P_J ∈ G such that every T ∈ G satisfies ‖p_T − p_{P_j}‖ ≤ 1/4 for some j. The sibling tangent_graph_cover with L = 1 and P = P_j gives closed sets Γ_{j,i} (i ∈ ℕ), each a 1-graph over P_j (|q_j(y − z)| ≤ |p_j(y − z)| for y, z ∈ Γ_{j,i}, where p_j := p_{P_j}, q_j := I − p_j), such that every x ∈ M (with T := T(x), which is within 1/4 of some P_j) lies in some Γ_{j,i}. On Γ := Γ_{j,i}: |y − z|² = |p_j(y − z)|² + |q_j(y − z)|² ≤ 2|p_j(y − z)|², so p_j is injective on Γ and its inverse h : p_j(Γ) → Γ is √2-Lipschitz. Let ι_j be a linear isometry of ℝ^n onto P_j.plane (orthonormal basis; finrank = n). The map a ↦ h(ι_j a) on ι_j^{−1}(p_j(Γ)) is √2-Lipschitz; extending each of its N real coordinates by McShane's formula (Mathlib LipschitzOnWith.extend_real, Topology/MetricSpace/Lipschitz.lean:308; or SimonGMT exists_lipschitz_extension_finiteDimensional, Chapter02/AreaDomain.lean) gives a Lipschitz F_{j,i} : ℝ^n → ℝ^N with Γ ⊆ range F_{j,i}. Re-indexing the countable family by ℕ, M ⊆ ∪ range F_{j,i}: CountablyRectifiable n M (with M₀ = ∅).

STEP 3 (comparison of μ and H^n on M).
 (3a) If Z ⊆ M and H^n(Z) = 0, then μ(Z) = 0. Fix k ∈ ℕ and τ > 0, and put Z_k := {x ∈ Z : θ(x) ≤ k}, Z_{k,δ} := {x ∈ Z_k : μ(B_ρ(x)) ≤ (k + τ)ω_nρ^n for 0 < ρ ≤ δ}; by (0c), Z_k = ∪_{j≥1} Z_{k,1/j}. Since H^n(Z_{k,δ}) = 0, for every ζ > 0 there is a countable cover of Z_{k,δ} by sets C_i of diameters d_i < δ with Σ_i ω_n(d_i/2)^n < ζ (definition of Simon's normalised H^n). Discard the C_i not meeting Z_{k,δ} and pick x_i ∈ C_i ∩ Z_{k,δ}; then C_i ⊆ B_{d_i}(x_i) and μ(B_{d_i}(x_i)) ≤ (k + τ)ω_nd_i^n (if d_i = 0, then μ({x_i}) ≤ (k + τ)ω_nρ^n for all small ρ > 0, so μ({x_i}) = 0). Hence μ(Z_{k,δ}) ≤ Σ_i (k + τ)ω_nd_i^n = 2^n(k + τ)Σ_i ω_n(d_i/2)^n < 2^n(k + τ)ζ for every ζ > 0, so μ(Z_{k,δ}) = 0, and μ(Z) ≤ Σ_{k,j} μ(Z_{k,1/j}) = 0.
 (3b) Let m ≥ 1 and let Z ⊆ ℝ^N be contained in some K_p, with μ(Z) = 0 and limsup_{ρ↓0} μ(B_ρ(y))/(ω_nρ^n) ≥ 1/m for every y ∈ Z. Then H^n(Z) = 0. Indeed μ⌞interior(K_{p+1}) is a finite Borel measure on ℝ^N, hence outer regular, so for every ζ > 0 there is an open O with Z ⊆ O ⊆ interior(K_{p+1}) and μ(O) < ζ. For y ∈ Z the upper density of μ⌞O at y equals that of μ (small balls about y lie in O), so Simon's comparison theorem Ch. 1, 3.3 (SimonGMT Chapter01.simon_theorem_3_3 with A₁ := Z, A₂ := O, t := 1/m; its density is the upper density of μ restricted to A₂) gives (1/m)H^n(Z) ≤ μ(O) < ζ. (SimonGMT states 3.3 for Simon's Gamma-normalised Hausdorff outer measure simonHausdorffOuterMeasureReal n and density quotients normalised by realUnitBallVolume n; for natural n these are μHE[n] and ω_n by Chapter01.simonHausdorffMeasureReal_toOuterMeasure, Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure and Chapter01.volume_euclidean_ball_eq (n ≥ 1). Its Borel-regularity hypothesis holds for the outer measure of the Borel measure μ⌞interior(K_{p+1}) (every set has a measurable superset of the same measure, toMeasurable); alternatively the underlying Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity only needs Borel sets to be Carathéodory-measurable.) Hence H^n(Z) = 0. Consequence: every μ-null set Z ⊆ M is H^n-null (apply (3b) to the pieces Z ∩ K_p ∩ {θ ≥ 1/m}, using (0c), and take the countable union over p, m).

STEP 4 (H^n-measurability of M; printed “M is H^n-measurable”). For m, k ≥ 1 let F_{m,k} := {x ∈ M : θ(x) ≥ 1/m and μ(B_ρ(x)) ≥ (2m)^{−1}ω_nρ^n for 0 < ρ ≤ 1/k}; by (0c), M = ∪_{m,k} F_{m,k}. Choose countably many closed balls B_r(x_0) (x_0 ∈ ℚ^N, r ∈ ℚ_{>0}, B_{2r}(x_0) ⊆ U) covering U, and for each put E := F_{m,k} ∩ B_r(x_0), whose closure cl E ⊆ B_r(x_0) is a compact subset of U (contained in some K_p). For y ∈ cl E write y = lim x_i with x_i ∈ E; for 0 < ρ ≤ 1/k and i large, B_{ρ − |x_i − y|}(x_i) ⊆ B_ρ(y), so μ(B_ρ(y)) ≥ (2m)^{−1}ω_n(ρ − |x_i − y|)^n → (2m)^{−1}ω_nρ^n; thus the upper density of μ is ≥ (2m)^{−1} at every point of cl E. Since μ(cl E ∖ M) = 0 by (0e), (3b) (with 2m in place of m) gives H^n(cl E ∖ M) = 0. Hence M ∩ cl E = cl E ∖ (cl E ∖ M) is a closed set minus an H^n-null set, so it is H^n-null-measurable, and M = ∪(M ∩ cl E) (countable union over m, k and the balls; E ⊆ M ∩ cl E ⊆ M) is null-measurable: NullMeasurableSet M μHE[n].

STEP 5 (density one of H^n on the carrier). For p ≥ 1 let M_p := {x ∈ M : θ(x) ≥ 1/p} ∩ K_p; it is H^n-null-measurable (Step 4, and θ = Θ̂.toReal on M with Θ̂ Borel, (0f)). The upper density of μ is ≥ 1/p on M_p, so Ch. 1, 3.3 (with A₁ := M_p, A₂ := interior K_{p+1}) gives H^n(M_p) ≤ p·μ(interior K_{p+1}) < ∞. Let λ_p := H^n⌞M_p, a finite Borel measure on ℝ^N. CLAIM: lim_{r↓0} λ_p(B_r(x))/(ω_nr^n) = 1 for λ_p-a.e. x.
 Fix L ∈ (0,1]. As in Step 2 choose P_1, …, P_J ∈ G such that every T ∈ G satisfies ‖p_T − p_{P_j}‖ ≤ L/4 for some j, and apply the sibling tangent_graph_cover with this L to each P_j: closed L-graphs Γ_{j,i} over P_j (i ∈ ℕ) such that every x ∈ M lies in some Γ_{j,i}. Fix one Γ := Γ_{j,i}, write P := P_j, p := p_P, q := I − p, and A := M_p ∩ Γ (H^n-null-measurable).
 (i) Graph comparison. For z, x ∈ Γ, |p(z) − p(x)| ≤ |z − x| ≤ (1 + L²)^{1/2}|p(z) − p(x)|, because |z − x|² = |p(z − x)|² + |q(z − x)|² ≤ (1 + L²)|p(z − x)|². So p is injective on Γ and h := (p|_Γ)^{−1} : p(Γ) → Γ is (1 + L²)^{1/2}-Lipschitz. For x ∈ A, r > 0 and s := r(1 + L²)^{−1/2} we have p(A) ∩ B_s(p x) ⊆ p(A ∩ B_r(x)) ⊆ p(A) ∩ B_r(p x) and A ∩ B_r(x) = h(p(A ∩ B_r(x))). Since H^n does not increase under the 1-Lipschitz map p and increases at most by the factor (1 + L²)^{n/2} under h (Mathlib LipschitzWith.hausdorffMeasure_image_le / LipschitzOnWith.hausdorffMeasure_image_le, MeasureTheory/Measure/Hausdorff.lean:733,745; μHE[n] is a constant multiple of μH[n]; these bounds hold for arbitrary sets),
 H^n(p(A) ∩ B_s(p x)) ≤ H^n(A ∩ B_r(x)) ≤ (1 + L²)^{n/2} H^n(p(A) ∩ B_r(p x)).
 (ii) Lebesgue density in the plane. Let ι be a linear isometry of ℝ^n onto P.plane. Then H^n(ι(B)) = L^n(B) for every B ⊆ ℝ^n and ι^{−1}(B_s(ι b)) = B^n_s(b), so H^n(P.plane ∩ B_s(a)) = ω_ns^n for a ∈ P.plane. By the Lebesgue density theorem in ℝ^n for the set ι^{−1}(p(A)) (Mathlib Besicovitch.ae_tendsto_measure_inter_div with μ = volume, Covering/Besicovitch.lean:1105, valid for arbitrary sets), there is an H^n-null set N_A ⊆ p(A) such that H^n(p(A) ∩ B_s(a))/(ω_ns^n) → 1 as s ↓ 0 for every a ∈ p(A) ∖ N_A. The set of x ∈ A with p(x) ∈ N_A is h(N_A), of H^n-measure ≤ (1 + L²)^{n/2}H^n(N_A) = 0.
 (iii) Lebesgue density of Γ for λ_p. By Mathlib Besicovitch.ae_tendsto_measure_inter_div for the finite measure λ_p and the closed set Γ, for λ_p-a.e. x ∈ Γ: λ_p(B_r(x)) > 0 for r > 0 and λ_p(Γ ∩ B_r(x))/λ_p(B_r(x)) → 1 as r ↓ 0; moreover λ_p(Γ ∩ B_r(x)) = H^n(A ∩ B_r(x)).
 (iv) Combining (i)–(iii): for λ_p-a.e. x ∈ A, (1 + L²)^{−n/2} ≤ liminf_r H^n(A ∩ B_r(x))/(ω_nr^n) ≤ limsup_r H^n(A ∩ B_r(x))/(ω_nr^n) ≤ (1 + L²)^{n/2} and λ_p(B_r(x)) = (1 + o(1))H^n(A ∩ B_r(x)); hence (1 + L²)^{−n/2} ≤ liminf_r λ_p(B_r(x))/(ω_nr^n) ≤ limsup_r λ_p(B_r(x))/(ω_nr^n) ≤ (1 + L²)^{n/2}. Since M_p ⊆ M ⊆ ∪_{j,i}Γ_{j,i} (countably many graphs), these two-sided bounds hold for λ_p-a.e. x ∈ M_p, i.e. λ_p-a.e. Taking L = 1/l for l = 1, 2, … and intersecting the countably many full-measure sets proves the CLAIM.

STEP 6 (μ = θ H^n ⌞ M; printed “μ_V = H^n ⌞ θ in U”). Fix p and let ρ_p := μ⌞M_p, a finite measure (ρ_p(ℝ^N) ≤ μ(K_p) < ∞).
 (a) ρ_p ≪ λ_p: if λ_p(Z) = 0 then H^n(Z ∩ M_p) = 0, so μ(Z ∩ M_p) = 0 by (3a).
 (b) By the Besicovitch differentiation theorem (Mathlib Besicovitch.ae_tendsto_rnDeriv, Covering/Besicovitch.lean:1078) for the finite measures ρ_p and λ_p, for λ_p-a.e. x, ρ_p(B_r(x))/λ_p(B_r(x)) → (dρ_p/dλ_p)(x) as r ↓ 0; by (a) and the Radon–Nikodym theorem, ρ_p = (dρ_p/dλ_p)·λ_p (Measure.withDensity_rnDeriv_eq).
 (c) For λ_p-a.e. x ∈ M_p: (α) λ_p(B_r(x))/(ω_nr^n) → 1 (Step 5); (β) μ(M_p ∩ B_r(x))/μ(B_r(x)) → 1 — this holds for μ-a.e. x ∈ M_p by Besicovitch.ae_tendsto_measure_inter_div applied to the finite measure μ⌞interior(K_{p+1}) (which agrees with μ on small balls about points of M_p ⊆ K_p) and the set M_p, and its exceptional set is a μ-null subset of M, hence H^n-null by (3b), hence λ_p-null; (γ) μ(B_r(x))/(ω_nr^n) → θ(x) (0c). Therefore ρ_p(B_r(x))/λ_p(B_r(x)) = [μ(M_p ∩ B_r(x))/μ(B_r(x))]·[μ(B_r(x))/(ω_nr^n)]/[λ_p(B_r(x))/(ω_nr^n)] → θ(x). So dρ_p/dλ_p = θ λ_p-a.e., i.e. μ⌞M_p = θ·H^n⌞M_p.
 (d) Since θ > 0 on M and M ⊆ U = ∪_p K_p, the sets M_p increase to M; by monotone convergence μ⌞M = θ·H^n⌞M, and with (0e), μ(B) = ∫_{B ∩ M} θ dH^n for every Borel B ⊆ ℝ^N (and then for every μ-null-measurable B). θ is (H^n⌞M)-a.e. measurable (θ = Θ̂.toReal on M, (0f)), and for compact K ⊆ U, ∫_{M∩K} θ dH^n = μ(M ∩ K) ≤ μ(K) < ∞: IntegrableOn θ (M ∩ K) μHE[n].

STEP 7 (approximate tangent planes w.r.t. θ, Ch. 3, 1.7, at every x ∈ M). Let x ∈ M and f ∈ C_c(ℝ^N) with tsupport f ⊆ B_R(0). For r > 0 with B_{rR}(x) ⊆ U, the homothety z ↦ (z − x)/r = blowUpMap x r z scales H^n by the factor r^{−n} (Mathlib euclideanHausdorffMeasure_homothety_image / _preimage), so ∫_{blowUpMap x r '' M} f(y)θ(x + ry) dH^n(y) = r^{−n}∫_M f((z − x)/r)θ(z) dH^n(z) = r^{−n}∫ f((z − x)/r) dμ(z) (Step 6(d); the integrands are bounded Borel functions times θ, supported in the compact set B_{rR}(x) ⊆ U where θ is H^n⌞M-integrable and μ is finite, so these Bochner integrals are integrals of integrable functions), and this tends to θ(x)∫_{T(x).plane} f dH^n by (0b). Since finrank T(x).plane = n, this is HasWeightedApproximateTangentSpaceAt n M θ x T(x).plane. By HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean; θ(x) ≠ 0) and Grassmannian.eq_of_plane_eq, for every x ∈ M and S ∈ G: HasWeightedApproximateTangentSpaceAt n M θ x S.plane ⇔ S = T(x).

STEP 8 (V is the graph varifold; printed (1)–(2), with the erratum). Let η be given by the sibling plane_disintegration (Lemma 1.3). For μ-a.e. x we have x ∈ M, η(x) a probability measure and avg_ρ(β) := ∫_{Gₙ(B_ρ(x))} β dV / μ(B_ρ(x)) → ∫β dη(x) for all β ∈ C(G). At such x, avg_ρ(β) = ∫_{B_1(0)×G} β(S) dV_{x,ρ} / V_{x,ρ}(B_1(0) × G) (change of variables), and V_{x,ρ} → θ(x) v(T(x)) with θ(x) v(T(x))(∂B_1(0) × G) = θ(x)H^n(T(x).plane ∩ ∂B_1(0)) = 0 (n ≥ 1: the unit sphere of the n-plane is H^n-null; n = 0: T(x).plane ∩ ∂B_1(0) = ∅). Approximating 1_{B_1(0)}(y) from above and below by continuous compactly supported cutoffs χ(y) (and splitting β = β⁺ − β⁻), avg_ρ(β) → θ(x)β(T(x))H^n(T(x).plane ∩ B_1(0))/(θ(x)H^n(T(x).plane ∩ B_1(0))) = β(T(x)). Hence ∫β dη(x) = β(T(x)) (corrected printed claim) and, by the second part of Lemma 1.3, for every Borel A ⊆ ℝ^N and β ∈ C(G), β ≥ 0:
 (1) ∫_{Gₙ(A)} β(S) dV(x,S) = ∫_{M∩A} β(T(x)) dμ(x).
 x ↦ T(x) is μ-a.e. equal to a Borel map: with β_{ab}(S) := S_{ab} (matrix entries, continuous), T(x)_{ab} = ∫β_{ab} dη(x) = lim_k ∫_{Gₙ(B_{1/k}(x))} S_{ab} dV / μ(B_{1/k}(x)), a limit of Borel functions of x (Tonelli for the σ-finite V and the bounded integrand 1_{|y−x|≤1/k}S_{ab}); set T̃(x) := this limit where it exists and lies in G (a Borel set of x), and a fixed S0 ∈ G otherwise. Then T̃ is Borel and T̃ = T μ-a.e. The measures V and ν := μ.map(x ↦ (x, T̃(x))) on ℝ^N × G both vanish on Uᶜ × G and are finite on K × G for compact K ⊆ U; by (1) they agree on all integrals of 1_A(x)β(S) (A Borel, β ∈ C(G), β ≥ 0), hence on all rectangles A × B (A ⊆ K_m Borel, B ⊆ G closed, using continuous β_k ↓ 1_B and dominated convergence; then all Borel B by the π-λ theorem). Both measures also vanish on every rectangle A × B with A ⊆ Uᶜ. The rectangles A × B with A Borel and either A ⊆ K_m for some m or A ⊆ Uᶜ, and B ⊆ G Borel, form a π-system (intersections stay of this form) that generates the Borel σ-algebra of ℝ^N × G (every Borel rectangle is a countable union of such rectangles, and Borel rectangles generate it because both factors are second countable); V and ν agree on it, and it contains the countable cover {K_m × G}_m ∪ {Uᶜ × G} of ℝ^N × G by sets of finite V-measure. Hence V = ν (Measure.ext_of_generateFrom_of_iUnion) — this is the printed (2).

STEP 9 (assembly). For Borel A ⊆ ℝ^N × G: V(A) = ν(A) = μ({x : (x, T̃(x)) ∈ A}) = μ({x ∈ M : (x, T(x)) ∈ A}) (μ is carried by M by (0e), and T̃ = T μ-a.e.) = ∫⁻_{{x ∈ M : (x,T(x)) ∈ A}} θ dH^n (Step 6(d); this set differs from the null-measurable set M ∩ {x : (x, T̃(x)) ∈ A} by a μ-null subset of M, which is H^n-null by (3b)) = ∫⁻_{{x ∈ M : ∃ S, HasWeightedApproximateTangentSpaceAt n M θ x S.plane ∧ (x,S) ∈ A}} ofReal(θ x) dμHE[n] (Step 7: the two sets coincide). Together with M ⊆ U (0d), NullMeasurableSet M μHE[n] (Step 4), CountablyRectifiable n M (Step 2), θ > 0 on M (0d), and IntegrableOn θ (M ∩ K) μHE[n] for compact K ⊆ U (Step 6(d)), this is IsVarifoldOf V M θ; with the first conclusion from (0d) this proves FirstRectifiabilityTheorem.

## Key steps

1. Def. 1.1 consequences: weight blow-ups → θH^n⌞T, HasDensity n μ_V x θ (so x ∈ spt μ_V), uniqueness of (T,θ), μ_V(ℝ^N ∖ M) = 0, Borel representative of θ; n > N trivial and n = 0 by atoms.
2. Countable rectifiability (Ch. 3 1.6 ⇐): finite 1/4-net of planes and tangent_graph_cover with L = 1 give closed 1-Lipschitz graphs covering M; inverse projections extend (McShane) to Lipschitz maps ℝ^n → ℝ^N.
3. Comparison: H^n-null subsets of M are μ_V-null (covering with μ_V(B_ρ) ≤ (k+τ)ω_nρ^n); μ_V-null sets with positive upper density are H^n-null (Ch. 1 3.3 + outer regularity).
4. H^n-measurability of M: closures of the uniform lower-density pieces differ from M by H^n-null sets.
5. Density one (replacing Ch. 3 1.6 ⇒): on each L-graph piece, Lipschitz image bounds and Lebesgue density in the plane squeeze H^n(A ∩ B_r(x))/(ω_nr^n) between (1+L²)^{∓n/2}; Lebesgue density of the graph for λ_p = H^n⌞M_p; let L = 1/l → 0.
6. Besicovitch differentiation + Radon–Nikodym: d(μ_V⌞M_p)/d(H^n⌞M_p) = θ, hence μ_V = θH^n⌞M and θ is locally H^n-integrable on M.
7. Every x ∈ M is an approximate tangent point of (M,θ) with plane T(x) (homothety change of variables), and it is unique.
8. Lemma 1.3 with the corrected identity η_V^(x)(β) = β(T(x)) gives V = μ_V.map(x ↦ (x, T̃(x))) (printed (2)); assemble IsVarifoldOf V M θ.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean workspace GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i 'varifold' mathlib/Mathlib (0 files)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem ae_tendsto_rnDeriv' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib`
- `rg -n 'theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite' mathlib/Mathlib`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -n '^theorem|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover,DisjointCover,Differential}.lean`
- `grep -n '^theorem' simongmt Chapter02/{Area,AreaLipschitz,AreaNoninjective,AreaMultiplicity,AreaLiteral}.lean`
- `grep -n '^theorem' simongmt Chapter01/{DensityComparison,Densities,HausdorffDensityBounds,InfiniteDensitySet}.lean`
- `grep -rn 'theorem <name>' simongmt for hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity, aemeasurable_imageMap, measurable_imageMap_domain, pushforwardMeasure_apply_of_contDiffOn, imageMap_preimage_cylinder_ae_of_fixed, eq_of_plane_eq, hasDerivAt_normalized_weightedCutoffMass, simonHausdorffMeasureReal_toOuterMeasure, volume_euclidean_ball_eq, mul_simonHausdorff_le_of_le_dimensionalUpperDensity, measurable_dimensionalUpperDensity`
- `lake env lean Scratch/Final.lean (import GMT.Ch08.Submission + comparator scope replay; 12 child statements + parent assembly + example : type_of% GMT.Ch08.main_theorem)`
- `lake env lean Scratch/Axioms.lean (#print axioms for 13 cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so every Ch. 8 result is proved in the DAG. Pinned SimonGMT Chapter03 has no Theorem 1.6/1.9 (no rectifiable ⇒ approximate tangents / density one) and no area formula on rectifiable carriers (Chapter02 area formulas have a Euclidean parameter domain) — the reason v1 was rejected — so the new decomposition avoids both: density one and the 5.9 mass/fibre comparison are proved with Lipschitz graphs of small slope from the new sibling tangent_graph_cover, using only Mathlib LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733/745), Isometry.euclideanHausdorffMeasure_image + EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Besicovitch.ae_tendsto_measure_inter_div / ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1105,1078), withDensity_rnDeriv_eq (RadonNikodym.lean:60), LipschitzOnWith.extend_real (Lipschitz.lean:308), measure_toMeasurable_inter_of_sFinite (SFinite.lean:477), and SimonGMT simon_theorem_3_3 / simon_theorem_3_6 / measurable_dimensional{Upper,Lower}Density (Chapter01). The first-variation derivative is the kernel-checked Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity (DeformationIntegral.lean:266), whose hypotheses match the contract. #print axioms for the 13 newly cited SimonGMT lemmas shows only propext, Classical.choice, Quot.sound. In a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope, all 12 child lean_statements elaborate and pass validate_lean_statement, and the parent assembly term checks against type_of% GMT.Ch08.main_theorem with no sorry of its own. The active DAG contains only root, so no name reservations conflict; all lean_names are fresh bare identifiers.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/3919

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
