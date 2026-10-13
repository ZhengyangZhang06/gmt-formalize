<!-- theorem-id: gmt-ch08/root.integral_compactness-a1 -->

## Theorem `Submission.integral_compactness_theorem`

Let U ⊆ ℝ^N be open and V_j (j ∈ ℕ) integer multiplicity rectifiable n-varifolds on U (IsIntegral: V_j = v(M_j, θ_j) with θ_j ∈ ℕ H^n-a.e. on M_j) with locally bounded first variation and sup_j(μ_{V_j}(W) + ‖δV_j‖(W)) < ∞ for every open W ⊂⊂ U. Then (i) some subsequence V_{φ(j)} (φ strictly increasing) converges as Radon measures on Gₙ(U) to an integral V with locally bounded first variation and ‖δV‖(W) ≤ liminf_j ‖δV_{φ(j)}‖(W) for every open W ⊂⊂ U; and (ii) for every strictly increasing φ and every V with V_{φ(j)} → V as Radon measures on Gₙ(U) (RadonConverges), V is integral. (Exactly IntegralCompactnessTheorem.)

Node: `root.integral_compactness-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/313, https://github.com/ZhengyangZhang06/gmt-formalize/issues/315, https://github.com/ZhengyangZhang06/gmt-formalize/issues/317, https://github.com/ZhengyangZhang06/gmt-formalize/issues/335, https://github.com/ZhengyangZhang06/gmt-formalize/issues/332, https://github.com/ZhengyangZhang06/gmt-formalize/issues/330, https://github.com/ZhengyangZhang06/gmt-formalize/issues/337

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/888, https://github.com/ZhengyangZhang06/gmt-formalize/issues/891, https://github.com/ZhengyangZhang06/gmt-formalize/issues/894, https://github.com/ZhengyangZhang06/gmt-formalize/issues/895, https://github.com/ZhengyangZhang06/gmt-formalize/issues/896, https://github.com/ZhengyangZhang06/gmt-formalize/issues/897, https://github.com/ZhengyangZhang06/gmt-formalize/issues/898, https://github.com/ZhengyangZhang06/gmt-formalize/issues/899

## Lean problem

Declaration: `Submission.integral_compactness_theorem`

```lean
IntegralCompactnessTheorem
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
- Child DAG node: `root.integral_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Remark 5.9 and the printed proof “that V is integer multiplicity if the V_i are”, Lemma 5.10, Remark 5.11 and the printed proof of 5.10 (pp. 218–223); the existence part uses Theorem 5.8 (sibling compactness). ERRATA AND REPAIRS (each is needed for a correct proof): (E1) 5.8's “liminf_{j→∞}” is along the extracted subsequence (contract). (E2) In the proof of 5.10, “δ‖W‖(B_ρ(y)) ≤ εμ(B_ρ(y))” in (1) means ‖δW‖(B_ρ(y)) ≤ εμ(B_ρ(y)); (6)–(7) are stated “for y ∈ B_1^n(0) ∖ p(A_1 ∪ A_2)” but are used, and proved, for good points y ∉ A_1 ∪ A_2 of spt μ; the sign of δV(X) in 3.5 is “−” (SimonGMT WeightedRadialIdentity.lean), irrelevant since only |δW(X)| enters; the normalisation “translating and changing scale by 3/2” is replaced by working at every fibre directly with balls of radius 1 (any fixed radius works in the application). (E3) The printed conclusion of the proof of 5.9 is incomplete: from (7) ∫fψ_i → θ0∫f and (8) ψ_i ≤ θ0 + ε_i off A_i with L^n(A_i) → 0 one cannot conclude (mass of ψ_i may concentrate over A_i), and “max{ψ_i, N}” must in any case read “min{ψ_i, N}”. The repair below (Lemma 5.10′ in B5 and step B6) bounds the GOOD part of every fibre sum by an integer k0 and controls the BAD part directly by its mass μ_W(A_1 ∪ A_2) ≤ cε; the mass of the good part is compared with its fibre sums through Lipschitz graphs of small slope over P (sibling tangent_graph_cover) and the Lipschitz image bound for Hausdorff measure, so no area formula on rectifiable carriers and no Jacobian/tangent identification is needed. Notation: μ_j = μ_{V_j}, ‖δV_j‖ = variationMeasure (Vj j), G = Grassmannian N n, B_ρ(y) closed ball, B°_ρ(y) open ball, W ⊂⊂ U = IsRelCompactOpenIn W U, H^n = μHE[n], ω_n = unitBallVolume n, V_{ξ,λ} = rescaledMeasure V ξ λ, v(P) = planeVarifoldMeasure P; for an n-plane P we write P also for P.plane.

Hypotheses: each V_j is integral (IsIntegral: V_j = v(M_j, θ_j) with θ_j ∈ ℕ H^n-a.e. on M_j) with locally bounded first variation (LBFV), and sup_j(μ_j(W) + ‖δV_j‖(W)) < ∞ for every open W ⊂⊂ U.

B0 (integral varifolds have density ≥ 1 a.e.; printed “the hypothesis Θ^n(μ_{V_j},x) ≥ 1 on U ∖ A_j is automatically satisfied with μ_{V_j}(A_j) = 0”). Let V be an n-varifold on U with IsVarifoldOf V M θ and θ ∈ ℕ H^n-a.e. on M. Let K_p be a compact exhaustion of U with K_p ⊆ interior K_{p+1}. Put ν := θ·H^n⌞M (locally finite on U, as θ is integrable on M ∩ K for compact K ⊆ U), let M* := {x ∈ M : ∃ S, HasWeightedApproximateTangentSpaceAt n M θ x S.plane}, and let M' := M ∩ toMeasurable(M*), the measurable hull being taken w.r.t. the s-finite measure H^n⌞M (σ-finite because θ > 0 on M and θ is integrable on each M ∩ K_p). Then M' is H^n-null-measurable, M* ⊆ M' ⊆ M, and (H^n⌞M)(B ∩ M') = (H^n⌞M)(B ∩ M*) for every Borel B (Mathlib measure_toMeasurable_inter_of_sFinite), hence also for every (H^n⌞M)-null-measurable B (split off a null set), and the same holds with ν in place of H^n⌞M. The IsVarifoldOf identity with A = B × G gives μ_V(B) = ∫⁻_{M*∩B} θ dH^n = ν(B ∩ M') for Borel B (Measure.restrict_toMeasurable_of_sFinite), i.e. μ_V = ν⌞M'.
 (a) At every x ∈ M*, Ch. 3 Remark 1.8(2) holds: testing Definition 1.7 (HasWeightedApproximateTangentSpaceAt) with continuous f, 1_{B_κ(0)} ≤ f ≤ 1_{B_{1/κ}(0)}, κ ↑ 1, and using the homothety scaling of H^n, gives ν(B_ρ(x))/(ω_nρ^n) → θ(x) as ρ ↓ 0.
 (b) By the upper density theorem (Ch. 1, 3.6; SimonGMT simon_theorem_3_6, applied for each p to the finite Borel measure ν⌞K_{p+1} and the ν-measurable set (M ∖ M') ∩ K_{p+1}), for H^n-a.e. — hence ν-a.e. — x ∈ M': limsup_{ρ↓0} ν((M ∖ M') ∩ B_ρ(x))/(ω_nρ^n) = 0.
 (c) θ ∈ ℕ_{≥1} ν-a.e. on M (θ > 0 on M and θ ∈ ℕ H^n-a.e. on M).
 (d) Let F := {x ∈ U : ¬(HasDensity n μ_V x (ENNReal.ofReal (θ x)) ∧ θ(x) ∈ ℕ_{≥1})}. At every x ∈ M* at which (b) and (c) hold, μ_V(B_ρ(x)) = ν(B_ρ(x)) − ν((M ∖ M') ∩ B_ρ(x)) for small ρ (all terms finite), so by (a) Θ^n(μ_V, x) = θ(x) ∈ ℕ_{≥1}; hence ν(F ∩ M*) = 0. Moreover F is ν-null-measurable: on each K_p the densities of μ_V coincide with those of the finite measure μ_V⌞interior(K_{p+1}), whose upper and lower densities are Borel functions of x (SimonGMT Chapter01.measurable_dimensionalUpperDensity / measurable_dimensionalLowerDensity), and θ agrees ν-a.e. with a Borel function (θ is a.e.-strongly measurable on each M ∩ K_p by IntegrableOn). By the hull property, μ_V(F) = ν(F ∩ M') = ν(F ∩ M*) = 0, and μ_V(Uᶜ) = 0. So Θ^n(μ_V, x) exists and equals θ(x) ∈ ℕ_{≥1} for μ_V-a.e. x; in particular {x : ¬ ∃ θ', HasDensity n μ_V x θ' ∧ 1 ≤ θ'} is μ_V-null.

B1 (existence part). Put A_j := {x : ¬ ∃ θ, HasDensity n μ_j x θ ∧ 1 ≤ θ}. By B0, μ_j(A_j) = 0, so μ_j(A_j ∩ W) = 0 → 0, and the density is ≥ 1 on U ∖ A_j; IsIntegral V_j gives IsRectifiable V_j. The sibling compactness (CompactnessTheorem), applied to (V_j) with these A_j (its hypotheses: each V_j rectifiable and LBFV, the sup bounds, density ≥ 1 on U ∖ A_j, μ_j(A_j ∩ W) = 0 → 0), yields a strictly increasing φ and V with RadonConverges (V_{φ(j)}) V, IsRectifiable V, LBFV and ‖δV‖(W) ≤ liminf_j ‖δV_{φ(j)}‖(W) for open W ⊂⊂ U. By B2–B7 below, IsIntegral V. This is the first conjunct.

B2–B7 prove the second conjunct: let φ be strictly increasing and V with RadonConverges (V_{φ(i)}) V; write V_i := V_{φ(i)} (the bounds persist). We show IsIntegral V.
B2 (structure of V). Apply the sibling density_semicontinuity (DensitySemicontinuity) to (V_i)_i → V with B_i := A_{φ(i)} (A_j as in B1, so μ_i(B_i) = 0 by B0 and the density is ≥ 1 on U ∖ B_i; each V_i has LBFV; liminf_i ‖δV_i‖(W) ≤ sup_j ‖δV_j‖(W) < ∞ for W ⊂⊂ U): V has LBFV and Θ^n(μ_V,·) ≥ 1 μ_V-a.e.; by the sibling allard_tangent_cones (first conjunct, AllardRectifiabilityTheorem), V has a tangent plane at μ_V-a.e. point, and the sibling first_rectifiability gives the canonical representation IsVarifoldOf V M θ, M = {x ∈ spt μ_V : ∃ T θ', HasTangentPlane V x T θ'}, with HasTangentPlane V ξ T(ξ) θ(ξ) for every ξ ∈ M (θ(ξ) = Θ^n(μ_V,ξ) > 0). Let ν := θ H^n⌞M, M* the set of approximate tangent points of (M,θ) and M' := M ∩ toMeasurable(M*) as in B0 (hull w.r.t. the σ-finite measure H^n⌞M; θ > 0 is locally integrable on M); the IsVarifoldOf identity with A = B × G gives μ_V = ν⌞M', so μ_V(M ∖ M') = 0, while Θ^n(μ_V, y) = θ(y) > 0 at every y ∈ M. (Tangent-point facts, directly from Def. 1.1: if HasTangentPlane V y T θ then testing with f(z,S) = g(z), g ∈ C_c(ℝ^N), gives t^{-n}∫g((z−y)/t)dμ_V(z) → θ∫_T g dH^n; approximating 1_{B_1(0)} and using H^n(T ∩ ∂B_1(0)) = 0 (n ≥ 1; T = {0} if n = 0) gives Θ^n(μ_V, y) = θ; hence θ and T (the support of θH^n⌞T) are unique.) For each k and each compact K_p of an exhaustion of U (K_p ⊆ interior K_{p+1}), outer regularity of the finite measure μ_V⌞interior(K_{p+1}) gives open O with (M ∖ M') ∩ {θ ≥ 1/k} ∩ K_p ⊆ O ⊆ interior(K_{p+1}) of arbitrarily small μ_V-measure (μ_V(M ∖ M') = 0), and Ch. 1 3.3 (SimonGMT simon_theorem_3_3; the upper density of μ_V⌞O equals that of μ_V, which is θ ≥ 1/k, on this set) gives (1/k)H^n((M ∖ M') ∩ {θ ≥ 1/k} ∩ K_p) ≤ μ_V(O); hence H^n(M ∖ M') = 0 and μ_V = θ H^n⌞M. The same argument shows that every μ_V-null Z ⊆ M is H^n-null (H^n⌞M ≪ μ_V on M). Hence it suffices to show θ(ξ) ∈ ℕ for μ_V-a.e. ξ ∈ M.

B3 (printed (1)–(2)). Claim: for μ_V-a.e. ξ ∈ U there are c(ξ) < ∞ and r(ξ) > 0 with liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ c(ξ)ρ^n for 0 < ρ < r(ξ). Fix W ⊂⊂ U, r_W := min{1, dist(W, ℝ^N∖U)/2} (r_W := 1 if U = ℝ^N; Lean's infDist to ∅ is 0), W̃ := {y : dist(y, W) < r_W} ⊂⊂ U and S_W := sup_l ‖δV_l‖(W̃) < ∞. Let A ⊆ W be the set of ξ for which no c satisfies liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ c μ_V(B_ρ(ξ)) for all 0 < ρ < r_W. If μ_V(A) > 0 (outer measure), fix j ≥ 1: for each ξ ∈ A there are ρ_ξ ∈ (0, r_W) and i_ξ with μ_V(B_{ρ_ξ}(ξ)) < j^{-1}‖δV_i‖(B_{ρ_ξ}(ξ)) for all i ≥ i_ξ. With A_i := {ξ ∈ A : i_ξ ≤ i} ↑ A, Besicovitch (Ch. 1 3.12; N_B families of disjoint balls ⊆ W̃) gives μ_V(A_i) ≤ N_B j^{-1} ‖δV_l‖(W̃) ≤ N_B j^{-1} S_W for any l ≥ i, hence μ_V(A) = lim_i μ_V(A_i) ≤ N_B S_W / j for all j, so μ_V(A) = 0 — a contradiction; thus (1) holds μ_V-a.e. on W, and on U by a countable exhaustion. Since Θ^n(μ_V, ξ) exists and is finite μ_V-a.e. (sibling monotonicity_density, third conjunct DensityExistsAE), μ_V(B_ρ(ξ)) ≤ c'(ξ)ρ^n for 0 < ρ < r(ξ), giving (2); enlarging c(ξ) we may and do assume c(ξ) ≥ 1.

B4 (diagonal blow-ups; printed (3)–(4)). Fix ξ ∈ M at which (2) holds; put θ0 := θ(ξ) > 0 and P := T(ξ) (so V_{ξ,λ} → θ0 v(P) as λ ↓ 0). Fix a countable family {f_m} ⊆ C_c(ℝ^N × G), enumerated so that tsupport f_m ⊆ B_m(0) × G, which together with uniform local mass bounds determines vague convergence (e.g. for each R ∈ ℕ a countable subset, dense in sup norm, of the functions supported in B_R(0) × G, cut off to lie in B_{R+1}(0) × G). Choose λ_k ↓ 0 with λ_k ≤ k^{-n-2}, kλ_k < r(ξ), B_{kλ_k}(ξ) ⊆ U, |∫ f_m dV_{ξ,λ_k} − θ0∫ f_m dv(P)| < 1/k for m ≤ k, and V_{ξ,λ_k}(B_R(0) × G) ≤ θ0ω_nR^n + 1 for the integers R = 1,…,k (finitely many conditions, each holding for small λ by the density at ξ; non-integer R are handled by monotonicity in R). Since ∫ f d(rescaledMeasure V_i ξ λ) = λ^{-n}∫ f∘η_{ξ,λ} dV_i and f_m∘η_{ξ,λ_k} ∈ C_c(U × G), RadonConverges gives ∫ f_m d(rescaledMeasure V_i ξ λ_k) → ∫ f_m dV_{ξ,λ_k} as i → ∞ (m ≤ k), and limsup_i of the masses of compact sets is ≤ the limit's. By (2), infinitely many i satisfy ‖δV_i‖(B_{kλ_k}(ξ)) ≤ 2c(ξ)(kλ_k)^n. Choose i_k > i_{k−1} among these with |∫ f_m d(rescaledMeasure V_{i_k} ξ λ_k) − ∫ f_m dV_{ξ,λ_k}| < 1/k (m ≤ k) and masses ≤ θ0ω_nR^n + 2 on B_R(0) × G for the integers R ≤ k. Let W_k be the varifold on B°_k(0) with measure rescaledMeasure V_{i_k} ξ λ_k ⌞ (B°_k(0) × G). Then (3) W_k → θ0 v(P) (on every fixed ball), and by the first-variation scaling (Y(z) = λX((z−ξ)/λ), |δV(Y)| ≤ sup|Y| ‖δV‖(spt Y) from 2.6, sibling first_variation) (4) ‖δW_k‖(B°_R(0)) ≤ λ_k^{1−n}‖δV_{i_k}‖(B_{Rλ_k}(ξ)) ≤ 2c(ξ) k^n λ_k ≤ 2c(ξ)/k² → 0 for k > R (for k > R, B°_R(0) has compact closure in B°_k(0), so the characterization 2.5 of ‖δW_k‖ = variationMeasure W_k applies to it). Each W_k is integral: homotheties and restriction to open sets preserve IsVarifoldOf with integer θ (approximate tangent planes are local and homothety-invariant: HasWeightedApproximateTangentSpaceAt n ((M−ξ)/λ) (θ(ξ + λ·)) y S ⇔ HasWeightedApproximateTangentSpaceAt n M θ (ξ + λy) S; H^n(ξ + λA) = λ^n H^n(A)). Canonical form of W_k: W_k has LBFV and, by B0, Θ^n(μ_{W_k},·) ≥ 1 μ_{W_k}-a.e.; so the siblings allard_tangent_cones (AllardRectifiabilityTheorem) and first_rectifiability give θ̃_k with IsVarifoldOf W_k M̃_k θ̃_k, where M̃_k := {y ∈ spt μ_{W_k} : ∃ T θ', HasTangentPlane W_k y T θ'}, and with HasTangentPlane W_k y T_k(y) θ̃_k(y) for every y ∈ M̃_k; by the tangent-point facts recalled in B2, θ̃_k(y) = Θ^n(μ_{W_k}, y) > 0 for y ∈ M̃_k. Exactly as in B2 (with W_k, M̃_k, θ̃_k in place of V, M, θ): μ_{W_k} = θ̃_k H^n⌞M̃_k, and every μ_{W_k}-null subset of M̃_k is H^n-null. Finally, by B0 applied to the integral varifold W_k, Θ^n(μ_{W_k}, y) ∈ ℕ_{≥1} for μ_{W_k}-a.e. y, so the set of y ∈ M̃_k with θ̃_k(y) ∉ ℕ_{≥1} is μ_{W_k}-null, hence H^n-null: θ̃_k ∈ ℕ_{≥1} H^n-a.e. on M̃_k.

B5 (Lemma 5.10′, corrected 5.10/5.11). Let n ≥ 1, P an n-plane, p, q the orthogonal projections onto P and P^⊥, and for y ∈ ℝ^N, σ, τ > 0, U^τ_σ(y) := B_σ(y) ∩ {z : |q(z − y)| < τ}. CLAIM: for Λ ≥ 1 there are δ̄ = δ̄(n,N,Λ) ∈ (0,1) and c0 = c0(n,N,Λ) such that for each δ ∈ (0, δ̄] there is ε = ε(δ,n,N,Λ) ∈ (0, δ⁴] with: if W is an integral n-varifold on B°_3(0) with LBFV and (‡) μ(B°_3(0)) ≤ Λ, ‖δW‖(B°_3(0)) < ε², ∫_{B°_3(0)×G} ‖p_S − p‖ dW < ε² (μ := μ_W), then the set E of points y ∈ B_2(0) ∩ spt μ violating (1) ‖δW‖(B_ρ(y)) ≤ εμ(B_ρ(y)) ∀ρ ∈ (0,1) or (2) ∫_{B_ρ(y)×G}‖p_S − p‖ dW ≤ ερ^n ∀ρ ∈ (0,1) has μ(E) ≤ c0 ε, and for every x ∈ P with |x| < 1 and every finite set of distinct points y_1,…,y_m ∈ p^{-1}(x) ∩ spt μ ∖ E with |q(y_j)| < ε and Θ^n(μ, y_j) ≥ 1: Σ_j Θ^n(μ, y_j) ≤ (1+δ)μ(B_1(x))/ω_n + δ. (“Good” := in B_2(0) ∩ spt μ ∖ E.)
 Proof. (3) For y ∈ B_2(0) ∩ spt μ satisfying (1) (in particular for good y and for y ∈ E ∖ A_1, A_1 := points violating (1)): ball y 1 ⊆ B°_3(0), so by the sibling monotonicity_density (MonotonicityFormula, i.e. 3.3 with Λ = ε, ρ0 = 1) e^{ερ}μ(B_ρ(y))/(ω_nρ^n) is non-decreasing on (0,1), Θ^n(μ,y) exists, and μ(B_ρ(y)) ≤ c1 ω_n ρ^n (0 < ρ < 1), c1 := eΛ/ω_n.
 (4)–(5) For y ∈ E ∖ A_1 there is ρ_y ∈ (0,1) with ∫_{B_{ρ_y}(y)}‖p_S−p‖dW > ερ_y^n ≥ (ε/(c1ω_n))μ(B_{ρ_y}(y)) by (3); for y ∈ A_1 there is ρ_y ∈ (0,1) with μ(B_{ρ_y}(y)) < ε^{-1}‖δW‖(B_{ρ_y}(y)). Besicovitch (N_B disjoint countable subfamilies, all balls ⊆ B°_3(0)) gives μ(E) ≤ N_B( (c1ω_n/ε)·ε² + ε^{-1}·ε² ) = c0 ε, c0 := N_B(c1ω_n + 1).
 (7) For y good, 0 < τ ≤ 1 and 0 < σ ≤ ρ < 1: μ(U^τ_σ(y))/(ω_nσ^n) ≤ μ(U^{2τ}_ρ(y))/(ω_nρ^n) + c2 ερ/τ (c2 = c2(n,N,Λ)). Proof: take f ∈ C^∞, 0 ≤ f ≤ 1, f = 1 on (−∞,τ], f = 0 on [2τ,∞), |f'| ≤ 2/τ, h(z) := f(|q(z−y)|) (C¹, constant near q(z−y) = 0). Then ∇h ∈ P^⊥, so |∇^S h| = |p_S∇h| = |(p_S − p)∇h| ≤ (2/τ)‖p_S − p‖. Apply 3.5 (SimonGMT hasDerivAt_normalized_weightedCutoffMass at centre y, with this h ≥ 0 and the squared-radius profile used there: a C¹ non-increasing φ_η with φ_η = 1 on (−∞,1] and φ_η = 0 on [(1+η)², ∞), so that the cutoff is φ_η(|z−y|²/t²), decreasing to 1_{B_t(y)}(z) as η ↓ 0): d/dt(t^{-n}Ĩ(t)) = t^{-n}J̃'(t) + t^{-n-1}(G(t) − δW(X_t)) with Ĩ(t) = ∫φ_η(|z−y|²/t²)h dμ, J̃'(t) ≥ 0 (because φ_η' ≤ 0 and h ≥ 0, the derivative of the weighted normal-mass term is non-negative), X_t = hφ_η(|z−y|²/t²)(z−y), G(t) = ∫φ_η(|z−y|²/t²)⟨z−y, ∇^S h⟩ dW. By (1) and (3), |δW(X_t)| ≤ (1+η)t‖δW‖(B_{(1+η)t}(y)) ≤ (1+η)^{n+1}εc1ω_n t^{n+1}; by (2), |G(t)| ≤ (1+η)t(2/τ)∫_{B_{(1+η)t}(y)}‖p_S − p‖ dW ≤ 2(1+η)^{n+1}εt^{n+1}/τ (for (1+η)t < 1). So d/dt(t^{-n}Ĩ) ≥ −c3ε/τ on [σ,ρ] (τ ≤ 1); by the mean value theorem ρ^{-n}Ĩ(ρ) − σ^{-n}Ĩ(σ) ≥ −c3ε(ρ − σ)/τ ≥ −c3ερ/τ; let η ↓ 0 (monotone/dominated convergence: Ĩ(t) → ∫_{B_t(y)} h dμ), and use U^τ_σ(y) ⊆ {h = 1} ∩ B_σ(y) and {h > 0} ∩ B_ρ(y) ⊆ U^{2τ}_ρ(y); this gives (7) with c2 := c3/ω_n.
 (6) For y good, 0 < τ ≤ 1/4, 0 < σ < 1: Θ^n(μ,y) ≤ e^{ε}μ(U^{4τ}_σ(y))/(ω_nσ^n) + c2εσ/τ. (If τ ≥ σ: B_σ(y) ⊆ U^{4τ}_σ(y) and 3.3. If τ < σ: Θ ≤ e^{ετ}μ(B_τ(y))/(ω_nτ^n) by 3.3, B_τ(y) ⊆ U^{2τ}_τ(y), and (7) with parameter 2τ and radii τ < σ.)
 (8) Claim: for each m ≥ 1 there are c_m and δ_m > 0 such that for δ ∈ (0, δ_m], ε ≤ δ⁴, x ∈ P with |x| < 1 and distinct good y_1,…,y_m ∈ p^{-1}(x) with |q(y_j)| < ε: if m = 1, μ(U^τ_σ(y_1))/(ω_nσ^n) ≤ (1 + c_1δ²)μ(B_1(x))/ω_n for all τ > 0, 0 < σ ≤ 1 − ε; if m ≥ 2, with d := min_{j≠l}|y_j − y_l| (< 2ε, since y_j − y_l = q(y_j) − q(y_l)), for all σ, τ with 2δ²σ ≤ τ ≤ d/4: Σ_j μ(U^τ_σ(y_j))/(ω_nσ^n) ≤ (1 + c_mδ²)μ(B_1(x))/ω_n + c_mδ².
  m = 1: μ(U^τ_σ(y_1)) ≤ μ(B_σ(y_1)) and by 3.3 at y_1 with ρ = 1 − ε: μ(B_σ(y_1))/(ω_nσ^n) ≤ e^{ε}μ(B_{1−ε}(y_1))/(ω_n(1−ε)^n) ≤ e^ε(1−ε)^{-n}μ(B_1(x))/ω_n (|y_1 − x| < ε).
  m ≥ 2 (induction on m, printed argument made explicit): put ρ := d/(4δ²) (then σ ≤ τ/(2δ²) < ρ < ε/(2δ²) ≤ δ²/2) and τ̃ := 2δ²ρ = d/2. (a) Since τ ≤ d/4 = τ̃/2, (7) with parameter τ̃/2 gives μ(U^τ_σ(y_j))/(ω_nσ^n) ≤ μ(U^{τ̃}_ρ(y_j))/(ω_nρ^n) + c2ε/δ² ≤ … + c2δ². (b) The U^{τ̃}_ρ(y_j) are pairwise disjoint (|q(y_j) − q(y_l)| ≥ d = 2τ̃). (c) Clustering: for t > 0 let 𝒞(t) be the components of the graph on {1..m} joining j, l when |q(y_j) − q(y_l)| ≤ t; #𝒞(d) ≤ m − 1. With t_i := (10m)^i d (i = 0..m−1) the non-increasing values #𝒞(t_i) ∈ {1..m−1} repeat consecutively, so 𝒞(t_i) = 𝒞(t_{i+1}) =: {C_1,…,C_Q} for some i ≤ m − 2, Q ≤ m − 1; each class has diameter ≤ s := (m−1)t_i ≤ (10m)^m d and distinct classes are > t_{i+1} = 10m t_i apart. Pick z_k ∈ {y_j : j ∈ C_k}; put τ̂ := τ̃ + s, ρ̂ := ρ + s ≤ ρ(1 + 4(10m)^mδ²). Then U^{τ̃}_ρ(y_j) ⊆ U^{τ̂}_{ρ̂}(z_k) for j ∈ C_k, 2δ²ρ̂ ≤ τ̂, and τ̂ ≤ (1/4)min_{k≠k'}|z_k − z_{k'}| (10m t_i ≥ 4(d/2 + (m−1)t_i)). (d) Hence Σ_j μ(U^{τ̃}_ρ(y_j))/ρ^n ≤ (ρ̂/ρ)^n Σ_k μ(U^{τ̂}_{ρ̂}(z_k))/ρ̂^n. (e) Apply the claim for Q < m points (for Q = 1 the m = 1 case, as ρ̂ ≤ 2ρ < 1 − ε). Combining (a)–(e) and absorbing products of (1 + Cδ²)-factors for δ ≤ δ_m gives (8) with a suitable c_m.
 Conclusion of B5. For m ≥ 2 distinct good y_j as in the CLAIM, take τ := d/16 and σ := d/(8δ²) (< 1): by (6), Θ^n(μ,y_j) ≤ e^ε μ(U^{d/4}_σ(y_j))/(ω_nσ^n) + 2c2ε/δ², and (8) applies with parameter d/4 (2δ²σ = d/4); for m = 1 use 3.3 with ρ = 1 − ε. Thus Σ_jΘ^n(μ,y_j) ≤ (1 + C_mδ²)μ(B_1(x))/ω_n + C_mδ² ≤ (1+δ)μ(B_1(x))/ω_n + δ for δ ≤ δ'_m. A-priori bound (Remark 5.11): let m0 := ⌈(3/2)Λ/ω_n⌉ + 2, δ̄ := min_{m ≤ m0} δ'_m (≤ 1/2) and ε(δ) := δ⁴ (the constraints above only require ε ≤ δ⁴ and δ small). If m ≥ m0 distinct good points with Θ ≥ 1 were in one fibre, applying the bound to m0 of them would give m0 ≤ (3/2)Λ/ω_n + 1/2 < m0; so every admissible finite set has fewer than m0 points and the bound holds for it.

B6 (θ0 is an integer; repaired printed conclusion — no area formula is used). 
 Case n = 0. Then P = {0}, and for n = 0 the condition “θ ∈ ℕ H^0-a.e.” in IsIntegral means θ ∈ ℕ at every point of the carrier (H^0 = μHE[0] = μH[0] is the counting measure), so the IsVarifoldOf identity gives μ_{W_k}(B) = Σ_{y ∈ M*_k ∩ B} θ_k(y) ∈ ℕ ∪ {∞} for every Borel B (M*_k the set of approximate tangent points of the carrier). By (3), μ_{W_k}(B_{1/2}(0)) → θ0 (the limit θ0 v(P), whose weight is θ0δ_0, does not charge ∂B_{1/2}(0), and the masses are bounded for large k by B4), so θ0 is a limit of non-negative integers: θ0 ∈ ℕ.
 Case n ≥ 1. Let Λ := θ0ω_n3^n + 1 (≥ 1) and let δ̄, c0 and ε(·) be the constants of B5 for this Λ. Suppose, for contradiction, that k0 < θ0 < k0 + 1 for an integer k0 ≥ 0. Fix δ ∈ (0, δ̄] so small that (1 + δ)(θ0 + δ) + δ < k0 + 1 and 4δ⁴ ≤ ω_n; put ε := ε(δ) (≤ δ⁴) and L := 4ε/ω_n ∈ (0, 1]. Write p, q for the orthogonal projections onto P = P.plane and onto its orthogonal complement, and ‖p_S − p‖ for the operator norm (the norm used in B5).
 (i) Choice of k. For all large k, the varifold W'_k on B°_3(0) with measure W_k ⌞ (B°_3(0) × G) is an integral n-varifold with LBFV (B4) satisfying (‡) of B5, and sup_{a ∈ P, |a| ≤ 1} μ_{W_k}(B_1(a))/ω_n ≤ θ0 + δ. Indeed: limsup_k μ_{W_k}(B_3(0)) ≤ θ0ω_n3^n < Λ (upper semicontinuity of vague limits on compact sets, by (3)); ‖δW'_k‖(B°_3(0)) ≤ ‖δW_k‖(B°_3(0)) ≤ 2c(ξ)/k² < ε² for large k by (4) (k > 3; the first inequality holds because B°_3(0) is the increasing union of the balls B°_{3−1/j}(0), which have compact closure in B°_3(0), on each of which ‖δW'_k‖ is the supremum 2.5 over test fields supported there, and these fields are also test fields of W_k with δW'_k(X) = δW_k(X)); for a continuous χ with 1_{[0,3]} ≤ χ ≤ 1_{[0,4]}, limsup_k ∫_{B_3(0)×G} ‖p_S − p‖ dW_k ≤ lim_k ∫ χ(|z|)‖p_S − p‖ dW_k(z,S) = θ0∫_P χ(|z|)‖p_P − p‖ dH^n(z) = 0 by (3) (S ↦ ‖p_S − p‖ is continuous); and covering {a ∈ P : |a| ≤ 1} by finitely many balls B_η(a_i), a_i ∈ P, with θ0(1 + η)^n ≤ θ0 + δ/2, every B_1(a) lies in some B_{1+η}(a_i) and limsup_k μ_{W_k}(B_{1+η}(a_i)) ≤ θ0H^n(P ∩ B_{1+η}(a_i)) = θ0ω_n(1 + η)^n. Fix such a large k and write W := W'_k, μ := μ_W, M̃ := M̃_k ∩ B°_3(0), θ̃ := θ̃_k and T(y) := T_k(y). By B4: μ = θ̃ H^n ⌞ M̃ (as measures on B°_3(0)); every y ∈ M̃ lies in spt μ and W has tangent plane T(y) with multiplicity θ̃(y) = Θ^n(μ, y) > 0 at y (Def. 1.1 is local, so the tangent points of W in B°_3(0) are those of W_k); and θ̃ ∈ ℕ_{≥1} H^n-a.e. on M̃. Let E be the bad set of B5 for W and E' ⊇ E a Borel set with μ(E') = μ(E) ≤ c0ε (measurable hull); points outside E' are outside E.
 (ii) Good tangent points are flat. Let G' := {y ∈ M̃ ∖ E' : |p(y)| < 1, |q(y)| < ε, θ̃(y) ∈ ℕ_{≥1}} (an H^n-null-measurable set). Every y ∈ G' lies in B_2(0) ∩ spt μ ∖ E (|y|² = |p(y)|² + |q(y)|² < 1 + ε² < 4), i.e. is a good point of B5, so ∫_{B_ρ(y)×G} ‖p_S − p‖ dW ≤ ερ^n for ρ ∈ (0,1). Test the tangent-plane convergence of W at y (rescaledMeasure W y ρ → θ̃(y) v(T(y))) with the continuous compactly supported function (z,S) ↦ χ_κ(|z|)‖p_S − p‖, where χ_κ is continuous, 1_{[0,κ]} ≤ χ_κ ≤ 1_{[0,1]}, κ < 1: since ∫ χ_κ(|z|)‖p_S − p‖ d(rescaledMeasure W y ρ) ≤ ρ^{−n}∫_{B_ρ(y)×G} ‖p_S − p‖ dW ≤ ε, the limit gives θ̃(y)‖p_{T(y)} − p‖∫_{T(y).plane} χ_κ(|z|) dH^n(z) ≤ ε, hence θ̃(y)ω_nκ^n‖p_{T(y)} − p‖ ≤ ε; letting κ ↑ 1 and using θ̃(y) ≥ 1, ‖p_{T(y)} − p‖ ≤ ε/ω_n = L/4.
 (iii) Small-slope Lipschitz graphs. The sibling tangent_graph_cover, applied to the varifold W, the plane P and the slope L ∈ (0,1], gives closed L-graphs Γ_0, Γ_1, … over P (|q(y − z)| ≤ L|p(y − z)| for y, z ∈ Γ_i) such that every y ∈ G' (a tangent point of W with ‖p_{T(y)} − p‖ ≤ L/4, by (ii)) lies in some Γ_i. Put A_i := (G' ∩ Γ_i) ∖ ∪_{j<i} Γ_j: pairwise disjoint H^n-null-measurable sets with union G'. On Γ_i, |p(y) − p(z)| ≤ |y − z| ≤ (1 + L²)^{1/2}|p(y) − p(z)| (because |y − z|² = |p(y − z)|² + |q(y − z)|²), so p is injective on Γ_i, its inverse h_i : p(Γ_i) → Γ_i is (1 + L²)^{1/2}-Lipschitz, and p|_{Γ_i} is a bi-Lipschitz homeomorphism of the closed set Γ_i onto the closed set p(Γ_i).
 (iv) Graph inequality (replaces the area formula on the rectifiable carrier). For every (H^n⌞G')-measurable g : ℝ^N → [0,∞]:
  ∫_{G'} g dH^n ≤ (1 + L²)^{n/2} ∫_{P} Σ_{y ∈ G' ∩ p^{−1}(a)} g(y) dH^n(a).
 Proof: for s ≥ 0, A_i ∩ {g > s} = h_i(p(A_i ∩ {g > s})) and p(A_i ∩ {g > s}) = {a ∈ p(A_i) : g(h_i(a)) > s}; by the Lipschitz image bound for Hausdorff measure (Mathlib LipschitzOnWith.hausdorffMeasure_image_le; μHE[n] is a constant multiple of μH[n]), H^n(A_i ∩ {g > s}) ≤ (1 + L²)^{n/2} H^n({a ∈ p(A_i) : g(h_i(a)) > s}). The function a ↦ 1_{p(A_i)}(a)·g(h_i(a)) is (H^n⌞P)-measurable (the bi-Lipschitz homeomorphism p|_{Γ_i} maps Borel subsets of Γ_i to Borel subsets of p(Γ_i) and H^n-null sets to H^n-null sets, hence H^n-null-measurable sets to H^n-null-measurable sets). Integrating in s (layer-cake formula, Mathlib lintegral_eq_lintegral_meas_lt) gives ∫_{A_i} g dH^n ≤ (1 + L²)^{n/2} ∫_P 1_{p(A_i)}(a) g(h_i(a)) dH^n(a). Summing over i (monotone convergence) and noting that, for each a ∈ P, the points of G' ∩ p^{−1}(a) are exactly the h_i(a) with a ∈ p(A_i), one for each such i (the A_i are disjoint and p is injective on each Γ_i), gives the inequality.
 (v) Integer fibre bound. For every a ∈ P with |a| < 1: Σ_{y ∈ G' ∩ p^{−1}(a)} θ̃(y) ≤ k0. Indeed every such y is a good point of B5 with |q(y)| < ε and Θ^n(μ, y) = θ̃(y) ∈ ℕ_{≥1}, so by B5 every finite set y_1, …, y_m of them satisfies Σ_j θ̃(y_j) ≤ (1 + δ)μ(B_1(a))/ω_n + δ ≤ (1 + δ)(θ0 + δ) + δ < k0 + 1 (by (i)); the terms being positive integers, every finite subfamily has sum ≤ k0, so the fibre has at most k0 points and its sum is ≤ k0.
 (vi) Conclusion. Fix a continuous f₀ : P → [0,1] with compact support in {a ∈ P : |a| < 1} and ∫_P f₀ dH^n > 0, and a continuous χ : ℝ → [0,1] with χ = 1 on (−∞, ε/2] and χ = 0 on [ε, ∞). Then g₀(y) := f₀(p(y))χ(|q(y)|) is a continuous function with compact support in B_2(0), g₀ ≤ f₀∘p · 1_{{|p| < 1, |q| < ε}}, and g₀ = f₀ on P. By (3) (testing with (z,S) ↦ g₀(z)), ∫ g₀ dμ_{W_k} → θ0∫_P g₀ dH^n = θ0∫_P f₀ dH^n as k → ∞. On the other hand, for each large k as in (i)–(v), using μ = θ̃H^n⌞M̃ (spt g₀ ⊆ B°_3(0)), μ(E') ≤ c0ε, the fact that G' differs from (M̃ ∖ E') ∩ {|p| < 1, |q| < ε} by the H^n-null set {θ̃ ∉ ℕ_{≥1}}, and (iv)–(v) with g := (f₀∘p)·θ̃·1_{G'}:
  ∫ g₀ dμ_{W_k} ≤ μ(E') + ∫_{G'} f₀(p(y))θ̃(y) dH^n(y) ≤ c0ε + (1 + L²)^{n/2} ∫_P f₀(a) Σ_{y ∈ G' ∩ p^{−1}(a)} θ̃(y) dH^n(a) ≤ c0ε + (1 + L²)^{n/2} k0 ∫_P f₀ dH^n.
 Letting k → ∞: θ0∫_P f₀ dH^n ≤ c0ε(δ) + (1 + 16ε(δ)²/ω_n²)^{n/2} k0 ∫_P f₀ dH^n. This holds for every sufficiently small δ > 0, and ε(δ) ≤ δ⁴ → 0 as δ → 0, so θ0 ≤ k0, contradicting k0 < θ0. Hence θ0 is an integer, and θ0 ≥ 1 because θ0 > 0 (the case θ0 ∈ (0,1) is the case k0 = 0).

B7 (conclusion). By B3–B6, θ(ξ) ∈ ℕ for every ξ ∈ M at which (2) holds, i.e. for μ_V-a.e. ξ ∈ M; since H^n⌞M ≪ μ_V on M (B2), θ ∈ ℕ H^n-a.e. on M, and IsVarifoldOf V M θ (B2) gives IsIntegral V. With B1 this proves IntegralCompactnessTheorem.

## Key steps

1. Integral varifolds have Θ^n = θ ∈ ℕ_{≥1} a.e. (Ch. 3 Remark 1.8(2), upper density theorem), so 5.8 applies with null A_j: existence part.
2. Existence part: with A_j := {density ≥ 1 fails}, μ_j(A_j) = 0, so CompactnessTheorem (sibling compactness) gives a convergent subsequence; integrality from the second conjunct.
3. Any subsequential limit V: density_semicontinuity gives LBFV and Θ ≥ 1 a.e.; Allard + first_rectifiability give the canonical representation V = v(M,θ) with μ_V = θH^n⌞M (Ch. 1 3.3).
4. Printed (1)–(2) by Besicovitch: liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ c(ξ)ρ^n μ_V-a.e.
5. Printed (3)–(4): diagonal integral blow-ups W_k → θ0 v(P), ‖δW_k‖(B_R) → 0, in canonical integral form.
6. Corrected Lemma 5.10′: bad set E with μ_W(E) ≤ c0ε (Besicovitch), cylinder estimates (6)–(7) from 3.3/3.5, clustering induction (8), a-priori bound on the number of fibre points; bound for good points of every fibre.
7. Repaired conclusion (B6): at good tangent points the tilt bound 5.10′(2) gives ‖p_{T(y)} − p‖ ≤ ε/ω_n; tangent_graph_cover covers them by closed graphs over P of slope L = 4ε/ω_n; the Lipschitz image bound gives ∫_{good} g dH^n ≤ (1+L²)^{n/2}∫_P Σ_fibre g, fibre sums of good points are integers ≤ k0, and the bad part is ≤ μ(E) ≤ c0ε; letting δ → 0 forces θ0 ≤ k0, so θ0 ∈ ℕ and V is integral.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/5066

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
