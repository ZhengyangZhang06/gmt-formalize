<!-- theorem-id: gmt-ch08/root.integral_compactness-a1.allard_lemma-a1 -->

## Theorem `Submission.intcpt_allard_integrality_lemma`

Assume MonotonicityFormula (Simon 8.3.3, frozen contract statement). Let N, n ∈ ℕ with n ≥ 1 and Λ ≥ 1. There are δ̄ > 0 and c₀ ≥ 0 such that for all δ ∈ (0,δ̄] and ε ∈ (0,δ⁴], every U ⊆ ℝ^N with B°_3(0) ⊆ U, every n-varifold W on U with locally bounded first variation and every P ∈ G(N,n) with (‡) μ_W(B°_3(0)) ≤ Λ, ‖δW‖(B°_3(0)) < ε² and ∫_{B°_3(0)×G} t_P(S) dW(z,S) < ε² (t_P(S) the operator norm of p_S − p_P): calling y good if (1) ‖δW‖(B_ρ(y)) ≤ εμ_W(B_ρ(y)) for all ρ ∈ (0,1) and (2) ∫_{B_ρ(y)×G} t_P dW ≤ ερ^n for all ρ ∈ (0,1), (a) the set E of points of B_2(0) ∩ spt μ_W that are not good has μ_W(E) ≤ c₀ε; (b) for every x ∈ P with |x| < 1, every finite set s of good points y ∈ B_2(0) ∩ spt μ_W with p_P(y) = x and |y − p_P(y)| < ε, and every Θ : ℝ^N → [0,∞] with HasDensity n μ_W y (Θ(y)) and Θ(y) ≥ 1 for y ∈ s: Σ_{y∈s} Θ(y) ≤ (1+δ)μ_W(B_1(x))/ω_n + δ.

Node: `root.integral_compactness-a1.allard_lemma-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/339

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1346, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1347, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1348, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1349, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1350, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1351, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1352, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1353, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1357

## Lean problem

Declaration: `Submission.intcpt_allard_integrality_lemma`

```lean
MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ n → 1 ≤ Λ → ∃ δbar c₀ : ℝ, 0 < δbar ∧ 0 ≤ c₀ ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δbar → 0 < ε → ε ≤ δ ^ 4 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → variationMeasure W (ball (0 : Euclidean N) 3) < ENNReal.ofReal (ε ^ 2) → (∫⁻ z in ball (0 : Euclidean N) 3 ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) < ENNReal.ofReal (ε ^ 2) → W.weight {y | y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ ¬ ((∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)))} ≤ ENNReal.ofReal (c₀ * ε) ∧ ∀ (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞), x ∈ P.plane → ‖x‖ < 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) ∧ ‖y - Grassmannian.project P y‖ < ε ∧ HasDensity n W.weight y (Θ y) ∧ 1 ≤ Θ y) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ
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

- Parent DAG node: `root.integral_compactness-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 8.5.10, Remark 5.11 and the printed proof of 5.10 (pp. 219–223), in the corrected form of step B5 of the parent proof. ERRATA (E2): in (1), "δ‖W‖(B_ρ(y))" means ‖δW‖(B_ρ(y)); (6)–(7) are stated for y ∈ B_1^n(0) ∖ p(A_1 ∪ A_2) but are used, and proved, for good points y of spt μ; the sign of δV(X) in 3.5 is "−" (SimonGMT WeightedRadialIdentity.lean), irrelevant because only |δW(X)| enters; the normalisation "translating and changing scale by 3/2" is replaced by working directly with balls of radius 1 at every fibre. Integrality of W is not used. Notation: G := Grassmannian N n; μ := μ_W = W.weight; ‖δW‖ := variationMeasure W; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; H^n := μHE[n]; ω_n := unitBallVolume n ∈ (0,∞), also used for its real value; Θ^n(μ,y) = c means HasDensity n μ y c; p := Grassmannian.project P, q := id − p (|v|² = |pv|² + |qv|², q symmetric idempotent); t_P(S) := ‖LinearMap.toContinuousLinearMap(Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖, the operator norm of p_S − p, so |(p_S − p)v| ≤ t_P(S)|v|; U^τ_σ(y) := B_σ(y) ∩ {z : |q(z − y)| < τ} (Borel). "y satisfies (1)" means ‖δW‖(B_ρ(y)) ≤ ε μ(B_ρ(y)) for all ρ ∈ (0,1); "y satisfies (2)" means ∫_{B_ρ(y)×G} t_P dW ≤ ερ^n for all ρ ∈ (0,1); E := {y ∈ B_2(0) ∩ spt μ : not ((1) and (2))}. N_B = N_B(N) is the Besicovitch constant of ℝ^N. Constants: c1 := eΛ/ω_n, c0 := N_B(c1ω_n + 1) = N_B(eΛ + 1), c3 := 2^{n+1}(4 + c1ω_n), c2 := c3/ω_n (they depend only on n, N, Λ); δ̄ ∈ (0,1/2] is fixed in step 7 and depends only on n, N, Λ. Throughout, δ ∈ (0,δ̄] and ε ∈ (0,δ⁴], so ε ≤ 1/16 and e^ε ≤ 2; U ⊇ B°_3(0), W, P satisfy the hypotheses (LBFV and (‡)).

1. Monotonicity at points satisfying (1) (printed (3)). Let y ∈ B_2(0) satisfy (1). Then B°_1(y) ⊆ B°_3(0) ⊆ U, and the hypothesis MonotonicityFormula applied to W, y, ρ₀ := 1 and Λ_mono := ε gives: ρ ↦ e^{ερ}μ(B_ρ(y))/ρ^n is non-decreasing on (0,1); Θ^n(μ,y) exists and is finite; Θ^n(μ,y) ≤ e^{εσ}μ(B_σ(y))/(ω_nσ^n) for σ ∈ (0,1). For 0 < σ ≤ ρ < 1, e^{εσ}μ(B_σ(y))/σ^n ≤ e^{ερ}μ(B_ρ(y))/ρ^n ≤ e^ε Λ/ρ^n (B_ρ(y) ⊆ B°_3(0), μ(B°_3(0)) ≤ Λ); letting ρ ↑ 1, μ(B_σ(y)) ≤ e^εΛσ^n ≤ c1ω_nσ^n for every σ ∈ (0,1).

2. The bad set (printed (4)–(5)); proof of (a). Let A_1 := {y ∈ E : (1) fails}. For y ∈ A_1 choose ρ_y ∈ (0,1) with ε μ(B_{ρ_y}(y)) < ‖δW‖(B_{ρ_y}(y)). For y ∈ E ∖ A_1, (1) holds and (2) fails, so by step 1 there is ρ_y ∈ (0,1) with ∫_{B_{ρ_y}(y)×G} t_P dW > ερ_y^n ≥ (ε/(c1ω_n)) μ(B_{ρ_y}(y)). In both cases μ(B_{ρ_y}(y)) ≤ (c1ω_n/ε)∫_{B_{ρ_y}(y)×G} t_P dW + ε^{-1}‖δW‖(B_{ρ_y}(y)), and B_{ρ_y}(y) ⊆ B°_3(0) (|y| ≤ 2, ρ_y < 1). By the Besicovitch covering theorem (Simon Ch. 1, 3.12; Mathlib Besicovitch.exist_disjoint_covering_families, or SimonGMT Chapter01.exists_besicovitchCovering_families after importing it) the balls B_{ρ_y}(y), y ∈ E, contain N_B subfamilies, each pairwise disjoint (hence countable: Set.PairwiseDisjoint.countable_of_nonempty_interior), whose union covers E. For one such disjoint subfamily 𝓑, summing over its balls (disjoint subsets of B°_3(0)): Σ_{B∈𝓑} μ(B) ≤ (c1ω_n/ε)∫_{B°_3(0)×G} t_P dW + ε^{-1}‖δW‖(B°_3(0)) < (c1ω_n/ε)ε² + ε^{-1}ε² = (c1ω_n + 1)ε by (‡). Hence μ(E) ≤ N_B(c1ω_n + 1)ε = c0ε (outer measure; E need not be measurable). This is (a), for every δ, ε as above.

3. Cylinder monotonicity (printed (7)). Claim: if y ∈ B_2(0) satisfies (1) and (2), 0 < τ ≤ 1 and 0 < σ ≤ ρ < 1, then μ(U^τ_σ(y))/(ω_nσ^n) ≤ μ(U^{2τ}_ρ(y))/(ω_nρ^n) + c2ερ/τ.
 Proof. Choose a C^∞ non-increasing f : ℝ → [0,1] with f = 1 on (−∞,τ], f = 0 on [2τ,∞) and |f'| ≤ 4/τ (e.g. a rescaled Real.smoothTransition, whose derivative is at most 2/τ), and set h(z) := f(|q(z − y)|). As f is constant near 0, h is C¹ with 0 ≤ h ≤ 1, ∇h(z) = f'(|q(z − y)|) q(z − y)/|q(z − y)| ∈ P^⊥ and |∇h| ≤ 4/τ; hence p∇h = 0 and |p_S∇h| = |(p_S − p)∇h| ≤ (4/τ)t_P(S) for S ∈ G. Fix η₀ ∈ (0,1] with (1+η₀)ρ < 1; for each η ∈ (0,η₀] fix a C¹ non-increasing φ_η : ℝ → [0,1] with φ_η = 1 on (−∞,1] and φ_η = 0 on [(1+η)²,∞); and let R := ((1+η₀)ρ + 1)/2 < 1, so B_R(y) ⊆ B°_3(0) ⊆ U and t(1+η) < R for t ∈ [σ,ρ]. Let Ĩ(t) := ∫ φ_η(|z − y|²/t²) h(z) dμ(z) (= Varifold.weightedCutoffMass W y h φ_η t). By the weighted radial identity 3.5 (SimonGMT Varifold.hasDerivAt_normalized_weightedCutoffMass in Poincare.SimonGMT.Chapter08.WeightedRadialIdentity, which the prover may need to import; centre y, A := 1 + η, this R; valid at every t ∈ [σ,ρ] since t(1+η) < R), d/dt(t^{-n}Ĩ(t)) = t^{-n}J̃'(t) + t^{-n-1}(G(t) − δW(X_t)), where J̃'(t) = ∫ (−2|z−y|²/t³) φ_η'(|z−y|²/t²) · (radialNormalSq) · h(z) dW ≥ 0 (φ_η' ≤ 0, h ≥ 0, radialNormalSq ≥ 0; it is the derivative of Varifold.weightedCutoffNormalMass), X_t(z) := h(z) φ_η(|z−y|²/t²)(z − y) (weightedRadialVectorField) and G(t) := ∫ φ_η(|z−y|²/t²) ⟨∇h(z), p_S(z − y)⟩ dW(z,S) (weightedRadialGradientTerm). X_t is a C¹ test field on U with tsupport X_t ⊆ B_{(1+η)t}(y) and |X_t| ≤ (1+η)t, so by the polar representation of δW (SimonGMT Varifold.isFirstVariationPolarRepresentation_riesz; ‖δW‖ = variationMeasure W since W has LBFV), (1) and step 1: |δW(X_t)| ≤ (1+η)t ‖δW‖(B_{(1+η)t}(y)) ≤ (1+η)t ε μ(B_{(1+η)t}(y)) ≤ (1+η)^{n+1} ε c1ω_n t^{n+1}. Since ⟨∇h, p_S(z − y)⟩ = ⟨p_S∇h, z − y⟩, (2) gives |G(t)| ≤ (1+η)t(4/τ)∫_{B_{(1+η)t}(y)×G} t_P dW ≤ 4(1+η)^{n+1}εt^{n+1}/τ. Hence, as η ≤ 1 and τ ≤ 1, d/dt(t^{-n}Ĩ(t)) ≥ −(1+η)^{n+1}ε(4/τ + c1ω_n) ≥ −c3ε/τ on [σ,ρ], and by the mean value theorem ρ^{-n}Ĩ(ρ) − σ^{-n}Ĩ(σ) ≥ −c3ε(ρ − σ)/τ ≥ −c3ερ/τ. Let η ↓ 0 along η = η₀/j: φ_η(|z−y|²/t²) → 1_{B_t(y)}(z) for every z (φ_η = 1 on (−∞,1] and = 0 on [(1+η)²,∞)), dominated by 1_{B_{(1+η₀)t}(y)}, and B_{(1+η₀)t}(y) is a compact subset of B°_3(0) with μ-measure ≤ Λ; so Ĩ(t) → ∫_{B_t(y)} h dμ by dominated convergence (no monotonicity in η is needed). Thus σ^{-n}∫_{B_σ(y)} h dμ ≤ ρ^{-n}∫_{B_ρ(y)} h dμ + c3ερ/τ. Finally U^τ_σ(y) ⊆ {h = 1} ∩ B_σ(y) and {h > 0} ∩ B_ρ(y) ⊆ U^{2τ}_ρ(y), so μ(U^τ_σ(y))/σ^n ≤ μ(U^{2τ}_ρ(y))/ρ^n + c3ερ/τ; divide by ω_n.

4. Density bound by cylinders (printed (6)). Claim: if y ∈ B_2(0) satisfies (1) and (2), 0 < τ ≤ 1/4 and 0 < σ < 1, then Θ^n(μ,y) ≤ e^ε μ(U^{4τ}_σ(y))/(ω_nσ^n) + c2εσ/τ. If τ ≥ σ: B_σ(y) ⊆ U^{4τ}_σ(y) (|q(z−y)| ≤ |z−y| ≤ σ < 4τ), and step 1 gives Θ^n(μ,y) ≤ e^{εσ}μ(B_σ(y))/(ω_nσ^n) ≤ e^εμ(U^{4τ}_σ(y))/(ω_nσ^n). If τ < σ: step 1 gives Θ^n(μ,y) ≤ e^{ετ}μ(B_τ(y))/(ω_nτ^n), B_τ(y) ⊆ U^{2τ}_τ(y), and step 3 with parameter 2τ ≤ 1/2 and radii τ < σ gives μ(U^{2τ}_τ(y))/(ω_nτ^n) ≤ μ(U^{4τ}_σ(y))/(ω_nσ^n) + c2εσ/(2τ); since e^ε ≤ 2, Θ^n(μ,y) ≤ e^εμ(U^{4τ}_σ(y))/(ω_nσ^n) + c2εσ/τ.

5. Clustering (printed (8)). Call y_1, …, y_m (m ≥ 1) admissible at x if x ∈ P.plane, |x| < 1, the y_j are distinct, p(y_j) = x, |q(y_j)| < ε, and every y_j lies in B_2(0) and satisfies (1) and (2). Then y_j − y_l = q(y_j) − q(y_l) and |y_j − x| = |q(y_j)| < ε. Claim: for every m ≥ 1 there are c_m ≥ 1 and δ_m ∈ (0,1/2] (depending only on n, N, Λ, m) such that for δ ∈ (0,δ_m], ε ∈ (0,δ⁴] and y_1,…,y_m admissible at x: if m = 1, μ(U^τ_σ(y_1))/(ω_nσ^n) ≤ (1 + c_1δ²)μ(B_1(x))/ω_n for all τ > 0 and 0 < σ ≤ 1 − ε; if m ≥ 2, with d := min_{j≠l}|y_j − y_l| ∈ (0,2ε), for all σ, τ > 0 with 2δ²σ ≤ τ ≤ d/4: Σ_j μ(U^τ_σ(y_j))/(ω_nσ^n) ≤ (1 + c_mδ²)μ(B_1(x))/ω_n + c_mδ². Proof by strong induction on m.
 m = 1: μ(U^τ_σ(y_1)) ≤ μ(B_σ(y_1)); by step 1 (σ ≤ 1 − ε < 1), μ(B_σ(y_1))/σ^n ≤ e^{ε(1−ε)}μ(B_{1−ε}(y_1))/(1−ε)^n ≤ e^ε(1−ε)^{-n}μ(B_1(x)), as B_{1−ε}(y_1) ⊆ B_1(x). Since ε ≤ δ⁴ ≤ δ², e^ε(1−ε)^{-n} ≤ 1 + c_1δ² for a suitable c_1 = c_1(n) and all δ ≤ δ_1 (small).
 m ≥ 2: let ρ := d/(4δ²) and τ̃ := 2δ²ρ = d/2. Then σ ≤ τ/(2δ²) ≤ d/(8δ²) < ρ < ε/(2δ²) ≤ δ²/2 < 1.
 (a) Since τ ≤ d/4 = τ̃/2, U^τ_σ(y_j) ⊆ U^{τ̃/2}_σ(y_j), and step 3 with parameter τ̃/2 ≤ 1 gives μ(U^τ_σ(y_j))/(ω_nσ^n) ≤ μ(U^{τ̃}_ρ(y_j))/(ω_nρ^n) + c2ερ/(τ̃/2) = μ(U^{τ̃}_ρ(y_j))/(ω_nρ^n) + c2ε/δ² ≤ μ(U^{τ̃}_ρ(y_j))/(ω_nρ^n) + c2δ².
 (b) The sets U^{τ̃}_ρ(y_j) (j = 1,…,m) are pairwise disjoint: a common point z would give |y_j − y_l| = |q(y_j) − q(y_l)| ≤ |q(z − y_j)| + |q(z − y_l)| < 2τ̃ = d.
 (c) For t > 0 let 𝒞(t) be the partition of {1,…,m} into the connected components of the graph joining j and l when |y_j − y_l| ≤ t. #𝒞(d) ≤ m − 1, and t ↦ #𝒞(t) is non-increasing with values in {1,…,m−1} for t ≥ d. With t_i := (10m)^i d (i = 0,…,m−1), the m values #𝒞(t_0) ≥ … ≥ #𝒞(t_{m−1}) lie in a set with m − 1 elements, so #𝒞(t_i) = #𝒞(t_{i+1}) for some i ≤ m − 2; since 𝒞(t_{i+1}) coarsens 𝒞(t_i), 𝒞(t_i) = 𝒞(t_{i+1}) =: {C_1,…,C_Q} with Q ≤ m − 1. Two indices in one class are joined by a path of at most m − 1 edges of length ≤ t_i, so every class has diameter ≤ s := (m−1)t_i ≤ (10m)^m d; indices in different classes satisfy |y_j − y_l| > t_{i+1} = 10m t_i. Pick z_k ∈ {y_j : j ∈ C_k} and put τ̂ := τ̃ + s and ρ̂ := ρ + s. Then U^{τ̃}_ρ(y_j) ⊆ U^{τ̂}_{ρ̂}(z_k) for j ∈ C_k (|z − z_k| ≤ |z − y_j| + |y_j − z_k| and |q(z − z_k)| ≤ |q(z − y_j)| + |y_j − z_k|); ρ̂ ≤ ρ(1 + 4(10m)^mδ²) because s ≤ (10m)^m d = (10m)^m 4δ²ρ; 2δ²ρ̂ = τ̃ + 2δ²s ≤ τ̂; and 4τ̂ = 4(d/2 + s) ≤ 2t_i + 4(m−1)t_i ≤ 10m t_i < min_{k≠k'}|z_k − z_{k'}| =: d' (if Q ≥ 2), i.e. τ̂ ≤ d'/4.
 (d) By (b) and (c), for each k the pairwise disjoint sets U^{τ̃}_ρ(y_j), j ∈ C_k, lie in U^{τ̂}_{ρ̂}(z_k); so Σ_j μ(U^{τ̃}_ρ(y_j))/ρ^n ≤ Σ_k μ(U^{τ̂}_{ρ̂}(z_k))/ρ^n = (ρ̂/ρ)^n Σ_k μ(U^{τ̂}_{ρ̂}(z_k))/ρ̂^n.
 (e) z_1,…,z_Q are admissible at x and Q < m. If Q ≥ 2, the induction hypothesis with σ' := ρ̂ and τ' := τ̂ (2δ²ρ̂ ≤ τ̂ ≤ d'/4) gives Σ_k μ(U^{τ̂}_{ρ̂}(z_k))/(ω_nρ̂^n) ≤ (1 + c_Qδ²)μ(B_1(x))/ω_n + c_Qδ²; if Q = 1, the case m = 1 applies with σ' := ρ̂, because ρ̂ ≤ 2ρ < δ² ≤ 1 − ε (using 4(10m)^mδ² ≤ 1 and δ ≤ 1/2).
 Combining (a), (d), (e): Σ_j μ(U^τ_σ(y_j))/(ω_nσ^n) ≤ (1 + 4(10m)^mδ²)^n[(1 + c_Qδ²)μ(B_1(x))/ω_n + c_Qδ²] + mc2δ², which is ≤ (1 + c_mδ²)μ(B_1(x))/ω_n + c_mδ² for a suitable c_m (depending on n, N, Λ, m and max_{Q<m} c_Q) and all δ ≤ δ_m, where δ_m ≤ min_{Q<m} δ_Q is chosen with 4(10m)^mδ_m² ≤ 1.

6. Fibre bound for m points. Claim: for every m ≥ 1 there is δ'_m ∈ (0,δ_m] such that for δ ∈ (0,δ'_m], ε ∈ (0,δ⁴] and y_1,…,y_m admissible at x: Σ_j Θ^n(μ,y_j) ≤ (1 + δ)μ(B_1(x))/ω_n + δ (the densities exist by step 1). For m = 1: step 1 with σ := 1 − ε and B_{1−ε}(y_1) ⊆ B_1(x) give Θ^n(μ,y_1) ≤ e^{ε(1−ε)}μ(B_{1−ε}(y_1))/(ω_n(1−ε)^n) ≤ (1 + c_1δ²)μ(B_1(x))/ω_n; put C_1 := c_1. For m ≥ 2: with d as in step 5 take τ := d/16 ≤ 1/4 and σ := d/(8δ²) < 2ε/(8δ²) ≤ δ²/4 < 1. By step 4 (4τ = d/4), Θ^n(μ,y_j) ≤ e^εμ(U^{d/4}_σ(y_j))/(ω_nσ^n) + c2εσ/τ = e^εμ(U^{d/4}_σ(y_j))/(ω_nσ^n) + 2c2ε/δ², and step 5 applies with τ = d/4 = 2δ²σ. Hence Σ_jΘ^n(μ,y_j) ≤ e^ε[(1 + c_mδ²)μ(B_1(x))/ω_n + c_mδ²] + 2mc2δ² ≤ (1 + C_mδ²)μ(B_1(x))/ω_n + C_mδ² with C_m := 2(c_m + 1) + 2mc2 (using e^ε ≤ 1 + 2ε ≤ 1 + 2δ² and ε ≤ δ⁴). Choose δ'_m ∈ (0,δ_m] with C_mδ'_m ≤ 1; then C_mδ² ≤ δ and the claim follows.

7. A-priori bound (Remark 5.11) and the choice of δ̄; proof of (b). Let m0 := ⌈(3/2)Λ/ω_n⌉ + 2 and δ̄ := min{δ'_1,…,δ'_{m0}} ∈ (0,1/2] (depending only on n, N, Λ). Let δ ∈ (0,δ̄], ε ∈ (0,δ⁴], x ∈ P.plane with |x| < 1, s a finite set of points y with p(y) = x, y ∈ B_2(0) ∩ spt μ, (1), (2), |q(y)| = |y − p(y)| < ε, and Θ : ℝ^N → [0,∞] with HasDensity n μ y (Θ(y)) and Θ(y) ≥ 1 for y ∈ s. By step 1 and uniqueness of limits in [0,∞] (the filter 𝓝[>]0 is non-trivial), Θ(y) = Θ^n(μ,y) for y ∈ s, and the elements of s, listed in any order, are admissible at x. Since B_1(x) ⊆ B_2(0) ⊆ B°_3(0), μ(B_1(x)) ≤ Λ. If #s ≥ m0, any m0 elements of s are admissible and step 6 (δ ≤ δ'_{m0}) gives m0 ≤ Σ Θ ≤ (1+δ)μ(B_1(x))/ω_n + δ ≤ (3/2)Λ/ω_n + 1/2 < m0, a contradiction. Hence #s < m0, and if s ≠ ∅, step 6 with m := #s (δ ≤ δ̄ ≤ δ'_m) gives Σ_{y∈s} Θ(y) ≤ (1+δ)μ(B_1(x))/ω_n + δ, i.e. in [0,∞]: Σ_{y∈s}Θ(y) ≤ ofReal(1+δ)·μ(B_1(x))/ω_n + ofReal δ; for s = ∅ the sum is 0. This is (b). With step 2, δ̄ > 0 and c0 ≥ 0 have all required properties. ∎

## Key steps

1. Monotonicity 3.3 at points with (1): density exists and μ(B_σ(y)) ≤ eΛσ^n for σ < 1.
2. Besicovitch on the bad points with (‡): μ(E) ≤ N_B(eΛ+1)ε = c₀ε.
3. Cylinder monotonicity (7) from the weighted radial identity 3.5 with h = f(|q(z−y)|), using (1), (2) and the polar representation.
4. Density bound by cylinders (6) from 3.3 and (7).
5. Clustering induction (8) on the number m of fibre points: disjoint cylinders, cluster scale selection t_i = (10m)^i d, reduction to fewer points.
6. Fibre bound for m points from (6) and (8) with τ = d/16, σ = d/(8δ²).
7. A-priori bound (Remark 5.11): fewer than m0 = ⌈(3/2)Λ/ω_n⌉+2 points per fibre; δ̄ := min_{m≤m0} δ'_m gives (b).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i varifold mathlib/Mathlib (0 files)`
- `rg -n 'theorem exist_disjoint_covering_families|theorem hausdorffMeasure_image_le|theorem lintegral_iUnion₀|theorem lintegral_tsum|theorem _root_.Monotone.measure_iUnion|theorem lintegral_map_equiv|theorem restrict_restrict_of_subset|theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite|euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_zero_singleton|theorem lintegral_withDensity_eq_lintegral_mul₀|IsCompact.exists_cthickening_subset_open|Set.PairwiseDisjoint.countable_of_nonempty_interior|theorem eventually_lt_of_lt_liminf|theorem ae_restrict_iff'₀|theorem exists_measurable_subset_ae_eq|theorem AEMeasurable.indicator₀|theorem measure_inter_add_sdiff₀|theorem lintegral_eq_lintegral_meas_lt' mathlib/Mathlib`
- `grep -n 'structure Varifold|def weight|def firstVariationNormOn|def HasLocallyBoundedFirstVariation|def domainMeasure|def project|def projectionLinearMap' simongmt Chapter08/Varifold.lean; grep RadonConverges Chapter08/VarifoldConvergence.lean`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem simon_theorem_3_3|theorem simon_theorem_3_6|theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|measurable_dimensional(Upper|Lower)Density|exists_besicovitchCovering_families' simongmt Chapter01/{DensityComparison,Densities}.lean`
- `grep -n 'hasDerivAt_normalized_weightedCutoffMass|weightedCutoffMass|weightedRadialVectorField|weightedRadialGradientTerm' simongmt Chapter08/WeightedRadialIdentity.lean; grep -n 'scaledRadialCutoff|squaredRadialVectorField' Chapter04/FirstVariation.lean`
- `grep -n 'isFirstVariationPolarRepresentation_riesz|firstVariationRieszMeasure_eq_norm|isFirstVariationMeasure_riesz' simongmt Chapter08/FirstVariationRiesz.lean`
- `python3 gmt-compare.py contract_scope(Contract.lean) -> replayed scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section/end Definitions`
- `lake build GMT.Ch08.Submission && lake env lean Test/Assembly2.lean (scratch copy /tmp/ic-decomp-cAI8Ux: 8 child statements in comparator form + 6 sibling stubs + parent term Submission.integral_compactness_theorem : IntegralCompactnessTheorem; no sorry in the parent)`
- `lake env lean Test/Axioms.lean (#print axioms for 11 cited SimonGMT lemmas: propext, Classical.choice, Quot.sound only)`
- `python3 -c validate_lean_statement (verifier/lean_contract.py) on all 8 lean_statements; dag.json lean_name scan for collisions`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-v2.json`
- `/tmp/ic-decomp-cAI8Ux/Test/Assembly2.lean`
- `/tmp/ic-decomp-cAI8Ux/Test/Axioms.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so all Ch. 8 obligations are proved in the DAG. Every Mathlib lemma cited in the child proofs exists in the snapshot with suitable hypotheses: the Besicovitch covering families, the Lipschitz/Hölder image bounds for Hausdorff measure, Euclidean Hausdorff measure scaling, isometry invariance and agreement with volume, the s-finite measurable-hull identities, restrict_restrict_of_subset, Monotone.measure_iUnion, lintegral_iUnion₀/tsum/map_equiv/withDensity, cthickening, countability of disjoint families, and the liminf lemmas. The SimonGMT lemmas used — Theorems 3.3/3.6, Borel-measurable densities, the Besicovitch families 3.12, the weighted radial identity 3.5, the Riesz polar representation and 2.5 characterization, and simonHausdorffMeasureReal = μHE[n] — exist in the pinned package and use only propext, Classical.choice and Quot.sound. 3.5 lives in Chapter08.WeightedRadialIdentity, which Submission does not import. In a scratch copy with the comparator's replayed contract scope, all 8 child lean_statements elaborate in the exact comparator form and pass validate_lean_statement. With the 8 children and 6 frozen root-level sibling types as sorried stubs, the parent assembly `Submission.integral_compactness_theorem : IntegralCompactnessTheorem` type-checks with no sorry of its own. dag.json and the node files reserve no `intcpt_*` names, so all 8 lean_names are fresh.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
