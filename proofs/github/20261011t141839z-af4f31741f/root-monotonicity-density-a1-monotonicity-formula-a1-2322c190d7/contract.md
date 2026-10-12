<!-- theorem-id: gmt-ch08/root.monotonicity_density-a1.monotonicity_formula-a1 -->

## Theorem `Submission.monotonicity_formula_8_3_3`

(Simon Ch. 8, 3.3; exactly the contract Prop MonotonicityFormula.) For all N, n ∈ ℕ, U ⊆ ℝ^N and every n-varifold V on U (SimonGMT Varifold N n U; U is open): let V have locally bounded first variation in U, let x ∈ ℝ^N and ρ0 > 0 with the open ball B°_{ρ0}(x) = ball x ρ0 ⊆ U, let Λ ≥ 0, and assume ‖δV‖(B_ρ(x)) ≤ ofReal(Λ)·μ_V(B_ρ(x)) for all 0 < ρ < ρ0, where B_ρ(x) = closedBall x ρ, μ_V = V.weight and ‖δV‖ = variationMeasure V. Then (i) ρ ↦ ofReal(e^{Λρ})·μ_V(B_ρ(x))/ofReal(ρ)^n is monotone non-decreasing on (0, ρ0) (values in [0,∞]); (ii) there is θ ∈ [0,∞] with θ ≠ ∞ and HasDensity n μ_V x θ, i.e. densityRatio n μ_V x ρ = μ_V(B_ρ(x))/(ω_n·ofReal(ρ)^n) → θ as ρ ↓ 0, where ω_n = unitBallVolume n; and (iii) for all 0 < σ ≤ ρ < ρ0: θ ≤ ofReal(e^{Λσ})·densityRatio n μ_V x σ and ofReal(e^{Λσ})·densityRatio n μ_V x σ + ω_n^{-1}·normalDefect V x (B_ρ(x) ∖ B_σ(x)) ≤ ofReal(e^{Λρ})·densityRatio n μ_V x ρ, where normalDefect V x A = ∫_{A×G(N,n)} ofReal(|(y − x) − p_S(y − x)|²/|y − x|^{n+2}) dV(y,S) (integrand 0 at y = x).

Node: `root.monotonicity_density-a1.monotonicity_formula-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/315

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3206, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3213, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3218

## Lean problem

Declaration: `Submission.monotonicity_formula_8_3_3`

```lean
MonotonicityFormula
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

- Parent DAG node: `root.monotonicity_density-a1`
- Child DAG node: `root.monotonicity_density-a1.monotonicity_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 8, 3.1–3.3 (printed pp. 210–211), proved “by essentially the same computation as in §4 of Ch. 4” (Ch. 4, 3.1–3.6 and 4.7) with the radial test field X_y = γ(r)(y − x). The argument below is extracted from the parent node's accepted proof (its common radial computation and its Part A) with all details filled in; it is self-contained. Errata/normalisations: (i) the printed 3.3 is a subtraction; it is stated here additively in [0,∞], which is equivalent because every term is finite (B_ρ(x) is a compact subset of U); (ii) the sign of δV(X) in the radial identity is −δV(X) (SimonGMT Chapter08/WeightedRadialIdentity.lean, header); only |δV(X)| is used below, so the sign is irrelevant. The two first-variation inputs (‖δV‖ is the Riesz measure; the polar representation, Simon 2.6) are kernel-checked SimonGMT results that need only locally bounded first variation (Steps 0.5 and 3.1), so no sibling theorem is used. Implementation note: the SimonGMT modules cited below (Chapter08/StationaryCutoff.lean, WeightedRadialIdentity.lean, RadialCutoffDifferentiation.lean, RadialFirstVariation.lean, FirstVariationRiesz.lean, Chapter04/FirstVariation.lean) are all imported by Poincare.SimonGMT.Chapter08.StationaryMonotonicity, which the frozen contract does not import; an implementation file may import it.

Notation. Fix N, n, U, V, x, ρ0, Λ as in the statement and hV : V.HasLocallyBoundedFirstVariation; the hypothesis (3.1) reads ‖δV‖(B_ρ) ≤ ofReal(Λ)·μ(B_ρ) for 0 < ρ < ρ0. U is open (V.isOpen_domain). μ := V.weight, so μ(A) = V(A × G) for Borel A (Varifold.weight_apply); ‖δV‖ := variationMeasure V; G := G(N,n) = Grassmannian N n; p_S := Grassmannian.project S and p_{S⊥}(v) := v − p_S(v) (orthogonal projections onto S and S⊥); B_s := closedBall x s; ω_n := unitBallVolume n; for t ∈ (0, ρ0), m_t := μ(B_t).toReal = V.weight.real(B_t) (a finite real number, see 0.1). For (y,S) ∈ ℝ^N × G put g(y,S) := |p_{S⊥}(|y − x|^{-1}(y − x))|², with 0^{-1} = 0 so that g(x,S) = 0; since p_{S⊥} is an orthogonal projection, 0 ≤ g ≤ 1 (in SimonGMT g(y,S) = S.radialNormalSq x y, Chapter08/RadialFirstVariation.lean:109, with radialNormalSq_nonneg, radialNormalSq_le_one and measurable_radialNormalSq). All functions below are Borel measurable.

Step 0 (preliminaries).
0.1 For 0 < s < ρ0, B_s ⊆ ball x ρ0 ⊆ U and B_s is compact, so V(B_s × G) = μ(B_s) < ∞ (V.finite_on_compact, Varifold.weight_finite_on_compact).
0.2 0 < ω_n < ∞: ω_n is the volume of the open unit ball of EuclideanSpace ℝ (Fin n), a nonempty, open, bounded set, and volume is an additive Haar measure (measure_ball_pos, measure_ball_lt_top; for n = 0, ω_0 = 1).
0.3 For t > 0 and any measure m on ℝ^N: m(B_t)/(ω_n·ofReal(t)^n) = ω_n^{-1}·(m(B_t)/ofReal(t)^n) in [0,∞] (ENNReal.mul_inv, using ω_n ≠ 0, ∞), and ofReal(t)^n = ofReal(t^n) (ENNReal.ofReal_pow). In particular densityRatio n μ x t = ω_n^{-1}·(μ(B_t)/ofReal(t)^n), and the contract's expression ofReal(e^{Λt})·μ(B_t)/ofReal(t)^n equals ofReal(e^{Λt})·(μ(B_t)/ofReal(t)^n) (mul_div_assoc).
0.4 Integrand identity: for every (y,S), |p_{S⊥}(y − x)|²/|y − x|^{n+2} = g(y,S)/|y − x|^n. If y ≠ x, linearity gives p_{S⊥}(y − x) = |y − x|·p_{S⊥}(|y − x|^{-1}(y − x)), so |p_{S⊥}(y − x)|² = |y − x|²·g(y,S) (Grassmannian.normalProject_eq_sub and Grassmannian.norm_normalProject_radial_sq, RadialFirstVariation.lean:81,123); divide by |y − x|^{n+2} > 0. If y = x both sides are 0 (Lean's 0/0 = 0, and g(x,S) = 0). Hence normalDefect V x A = ∫_{A×G} ofReal(g(y,S)/|y − x|^n) dV(y,S) for every set A.
0.5 Since V has locally bounded first variation, ‖δV‖ = variationMeasure V = V.firstVariationRieszMeasure hV (definition of variationMeasure, dif_pos hV). By (3.1) and 0.1, ‖δV‖(B_s) ≤ ofReal(Λ)·μ(B_s) < ∞ for 0 < s < ρ0.

Step 1 (cutoffs and radial test fields). For ε > 0 let φ_ε := monotonicityCutoff ε, φ_ε(τ) = 1 − smoothTransition((τ − 1)/ε) (SimonGMT Chapter04/FirstVariation.lean:825). It is C¹ (contDiff_monotonicityCutoff), antitone, so φ_ε' ≤ 0 (monotonicityCutoff_antitone), has values in [0,1] (monotonicityCutoff_mem_Icc), equals 1 on (−∞,1] and 0 on [1+ε, ∞) (monotonicityCutoff_one, monotonicityCutoff_zero), hence vanishes on [(1+ε)², ∞) (monotonicityCutoff_cutoff). For t > 0 put
   c_t(y) := φ_ε(|y − x|²/t²) ∈ [0,1],   ċ_t(y) := ∂_t c_t(y) = (−2|y − x|²/t³)·φ_ε'(|y − x|²/t²) ≥ 0,   X_t(y) := c_t(y)·(y − x)
(SimonGMT scaledRadialCutoff x φ_ε t, scaledRadialCutoffDeriv x φ_ε t, weightedRadialVectorField x (fun _ ↦ 1) φ_ε t; the t-derivative is hasDerivAt_scaledRadialCutoff, the sign is scaledRadialCutoffDeriv_nonneg). This is Simon's field γ(r)(y − x) with the C¹ profile γ(r) = φ(r/t), φ(s) := φ_ε(s²), which equals 1 on [0,1], vanishes for s ≥ √(1+ε) and is non-increasing on [0,∞). (c_t, ċ_t, X_t and I, J, G below depend on ε; the dependence is suppressed until Step 5.)
1.1 If c_t(y) ≠ 0 then |y − x|²/t² < 1 + ε, so |y − x| < √(1+ε)·t ≤ (1+ε)·t. Hence |X_t(y)| = c_t(y)|y − x| ≤ (1+ε)t·c_t(y) for all y, and tsupport X_t ⊆ B_{(1+ε)t} (weightedRadialVectorField_support with A = 1 + ε).
1.2 If ċ_t(y) ≠ 0 then t ≤ |y − x| ≤ (1+ε)t, because φ_ε is locally constant on (−∞,1) and on ((1+ε)², ∞), so φ_ε' vanishes there (scaledRadialCutoffDeriv_support).
1.3 X_t is C¹ on ℝ^N (contDiff_weightedRadialVectorField) with compact support; if (1+ε)t < ρ0 then tsupport X_t ⊆ B_{(1+ε)t} ⊆ ball x ρ0 ⊆ U, so X_t is a test field in K(U;ℝ^N), i.e. a Varifold.TestVectorField U with toFun = X_t.

Step 2 (the radial identity (★), Simon 3.2). Fix ε > 0 and R ∈ (0, ρ0), so B_R ⊆ U and V(B_R × G) < ∞ (0.1), and let t > 0 with (1+ε)t < R. Put I(t) := ∫ c_t(y) dV(y,S) = ∫ c_t dμ and J(t) := ∫ c_t(y)·g(y,S) dV(y,S).
2.1 (Differentiation under the integral.) For every measurable q on ℝ^N × G with |q| ≤ B on B_R × G, the function t' ↦ ∫ c_{t'}(y) q(y,S) dV is differentiable at t with derivative ∫ ċ_t q dV, and ċ_t q is V-integrable. Reason: choose 0 < t1 < t < t2 with (1+ε)t2 < R; for t' ∈ [t1,t2], c_{t'} and ċ_{t'} vanish off B_R (Steps 1.1–1.2), (t', y) ↦ ċ_{t'}(y) is continuous on [t1,t2] × B_R and hence bounded by some C, so |ċ_{t'} q| ≤ C·B·1_{B_R×G}, which is V-integrable; dominated differentiation applies (SimonGMT Varifold.hasDerivAt_integral_radialCutoff_of_radius, Chapter08/RadialCutoffDifferentiation.lean:91, with A = 1 + ε). In particular I'(t) = ∫ ċ_t dV and J'(t) = ∫ ċ_t g dV.
2.2 (Pointwise divergence.) For all (y,S): div_S X_t(y) = n·c_t(y) − t·ċ_t(y) + t·ċ_t(y)·g(y,S). Indeed, with η(τ) := φ_ε(τ/t²), X_t(y) = η(|y − x|²)(y − x) and DX_t(y) = η(|y − x|²)·Id + 2η'(|y − x|²)·(y − x)⊗(y − x), so div_S X_t(y) = trace(p_S DX_t(y)) = n·η + 2η'(|y − x|²)·|p_S(y − x)|²; moreover |p_S(y − x)|² = |y − x|² − |p_{S⊥}(y − x)|² = |y − x|²(1 − g(y,S)) by 0.4, and 2η'(|y − x|²)|y − x|² = 2|y − x|²φ_ε'(|y − x|²/t²)/t² = −t·ċ_t(y). (SimonGMT tangentialDivergence_weightedRadialVectorField, Chapter08/WeightedRadialIdentity.lean:44, with h ≡ 1, whose gradient term vanishes.)
2.3 Integrating 2.2 against V (every term is integrable by 2.1 and 0.1) gives δV(X_t) = n·I(t) − t·I'(t) + t·J'(t) (SimonGMT weightedRadial_firstVariation_identity, WeightedRadialIdentity.lean:152, with h ≡ 1).
2.4 Therefore t' ↦ I(t')/t'^n is differentiable at t and
   (I/t^n)'(t) = I'(t)/t^n − n·I(t)/t^{n+1} = J'(t)/t^n − δV(X_t)/t^{n+1}.        (★)
(SimonGMT Varifold.hasDerivAt_normalized_weightedCutoffMass, WeightedRadialIdentity.lean:200, with h ≡ 1, where the gradient integral is 0 and deriv J(t) = ∫ ċ_t g dV by hasDerivAt_weightedCutoffNormalMass, line 96; here I = weightedCutoffMass x (fun _ ↦ 1) φ_ε and J = weightedCutoffNormalMass x (fun _ ↦ 1) φ_ε.)
2.5 J'(t) = ∫ ċ_t g dV ≥ 0, because ċ_t ≥ 0 and g ≥ 0.

Step 3 (bound for the first variation). Let ε > 0 and t > 0 with (1+ε)t < ρ0. Then |δV(X_t)| ≤ (1+ε)·Λ·t·I(t).
3.1 (Polar representation, Simon 2.6.) By SimonGMT Varifold.isFirstVariationPolarRepresentation_riesz (Chapter08/FirstVariationRiesz.lean:133; it needs only locally bounded first variation) and 0.5, there is a measurable ν : ℝ^N → ℝ^N with |ν| = 1 ‖δV‖-a.e. such that for every test field X ∈ K(U;ℝ^N), y ↦ ⟨ν(y), X(y)⟩ is ‖δV‖-integrable and δV(X) = −∫⟨ν, X⟩ d‖δV‖. Apply this to X_t (Step 1.3). By Cauchy–Schwarz and Step 1.1, |δV(X_t)| ≤ ∫|⟨ν, X_t⟩| d‖δV‖ ≤ ∫|X_t| d‖δV‖ ≤ (1+ε)t·∫ c_t d‖δV‖; all these integrals are finite because c_t ≤ 1_{B_{(1+ε)t}} and ‖δV‖(B_{(1+ε)t}) < ∞ (0.5).
3.2 (Layer cake with closed super-level sets.) For any measure m on ℝ^N, since c_t is continuous with 0 ≤ c_t ≤ 1, ∫⁻ ofReal(c_t) dm = ∫⁻_{s ∈ (0,∞)} m({c_t ≥ s}) ds (Mathlib MeasureTheory.lintegral_eq_lintegral_meas_le, MeasureTheory/Integral/Layercake.lean:445), and {c_t ≥ s} = ∅ for s > 1.
3.3 For s ∈ (0,1] the set {c_t ≥ s} is a closed ball B_r with 0 < r < ρ0. Indeed E := {τ ∈ ℝ : φ_ε(τ) ≥ s} is closed (φ_ε is continuous), down-closed (φ_ε is antitone), contains (−∞,1] (φ_ε = 1 ≥ s there) and is disjoint from [1+ε, ∞) (φ_ε = 0 < s there); hence b := sup E belongs to E, 1 ≤ b < 1 + ε, and E = (−∞, b]. Thus {c_t ≥ s} = {y : |y − x|²/t² ≤ b} = B_r with r := t√b, and t ≤ r < √(1+ε)·t ≤ (1+ε)t < ρ0. By (3.1), ‖δV‖({c_t ≥ s}) ≤ ofReal(Λ)·μ({c_t ≥ s}).
3.4 Hence ∫⁻ ofReal(c_t) d‖δV‖ = ∫⁻_{(0,∞)} ‖δV‖({c_t ≥ s}) ds ≤ ofReal(Λ)·∫⁻_{(0,∞)} μ({c_t ≥ s}) ds = ofReal(Λ)·∫⁻ ofReal(c_t) dμ. Both lintegrals are finite (c_t ≤ 1_{B_{(1+ε)t}}, 0.1, 0.5), so taking toReal gives ∫ c_t d‖δV‖ ≤ Λ·∫ c_t dμ = Λ·I(t), and with 3.1, |δV(X_t)| ≤ (1+ε)·Λ·t·I(t).

Step 4 (integrating factor and comparison, Ch. 4 3.5). Fix 0 < σ ≤ ρ < ρ0, put R := (ρ + ρ0)/2 ∈ (ρ, ρ0), and consider ε > 0 with (1+ε)ρ < R (all sufficiently small ε > 0 qualify). Write Λ_ε := (1+ε)Λ ≥ 0. For every t ∈ [σ, ρ], (1+ε)t ≤ (1+ε)ρ < R < ρ0, so Steps 2 and 3 apply at t (with this R).
4.1 F(t) := e^{Λ_ε t}·I(t)/t^n is differentiable at each t ∈ [σ, ρ] with F'(t) = e^{Λ_ε t}·[Λ_ε I(t)/t^n + J'(t)/t^n − δV(X_t)/t^{n+1}] (product rule and (★)). Since δV(X_t) ≤ Λ_ε·t·I(t) (Step 3), the bracket is ≥ J'(t)/t^n; since J'(t) ≥ 0 (2.5) and e^{Λ_ε t} ≥ 1 (Λ_ε t ≥ 0), F'(t) ≥ J'(t)/t^n.
4.2 Let q(y,S) := g(y,S)/max(σ, |y − x|)^n (SimonGMT truncatedRadialDefect x σ, Chapter08/StationaryCutoff.lean:121), a measurable function with 0 ≤ q ≤ σ^{-n} (norm_truncatedRadialDefect_le), and G(t) := ∫ c_t q dV. By 2.1, G is differentiable at every t ∈ [σ, ρ] with G'(t) = ∫ ċ_t q dV. Pointwise ċ_t q ≤ ċ_t g/t^n: where ċ_t(y) ≠ 0, Step 1.2 gives |y − x| ≥ t ≥ σ, so q = g/|y − x|^n ≤ g/t^n, and ċ_t ≥ 0; where ċ_t(y) = 0 both sides vanish (SimonGMT Varifold.scaledRadialCutoffDeriv_defect_bounds, StationaryCutoff.lean:142, first half). Integrating, G'(t) ≤ J'(t)/t^n ≤ F'(t).
4.3 F − G is differentiable at every point of [σ, ρ], hence continuous there, with nonnegative derivative, so it is non-decreasing on [σ, ρ] (mean value theorem; Mathlib monotoneOn_of_deriv_nonneg on Icc σ ρ). Writing the dependence on ε explicitly:
   e^{Λ_ε ρ}·I_ε(ρ)/ρ^n − e^{Λ_ε σ}·I_ε(σ)/σ^n ≥ G_ε(ρ) − G_ε(σ).        (4.3)

Step 5 (ε ↓ 0). Keep σ, ρ, R fixed; (4.3) holds for all sufficiently small ε > 0. As ε → 0+:
5.1 For t ∈ {σ, ρ} and every y, c_t(y) = φ_ε(|y − x|²/t²) → 1_{B_t}(y): if |y − x| ≤ t it equals 1 for every ε; if |y − x| > t it equals 0 as soon as 1 + ε ≤ |y − x|²/t² (SimonGMT tendsto_scaledRadialCutoff, Chapter04/FirstVariation.lean:886). For ε with (1+ε)t < R, |c_t| ≤ 1_{B_R×G} and |c_t q| ≤ σ^{-n}·1_{B_R×G}, both V-integrable (0.1). By dominated convergence I_ε(t) → m_t = V.weight.real(B_t) and G_ε(t) → ∫_{B_t×G} q dV (SimonGMT Varifold.tendsto_cutoffMass and Varifold.tendsto_integral_radialCutoff, StationaryCutoff.lean:111 and 63, with this R).
5.2 e^{Λ_ε t} = e^{(1+ε)Λt} → e^{Λt}.
5.3 Passing to the limit in (4.3), an inequality between real numbers:
   e^{Λρ}m_ρ/ρ^n − e^{Λσ}m_σ/σ^n ≥ ∫_{B_ρ×G} q dV − ∫_{B_σ×G} q dV = ∫_{(B_ρ∖B_σ)×G} q dV = ∫_{(B_ρ∖B_σ)×G} g(y,S)/|y − x|^n dV(y,S),
because q is V-integrable on B_ρ × G, B_σ × G ⊆ B_ρ × G, (B_ρ × G) ∖ (B_σ × G) = (B_ρ ∖ B_σ) × G, and on that annulus |y − x| > σ, so max(σ, |y − x|) = |y − x|.

Step 6 (additive form of 3.3 and normalisation). Let D := normalDefect V x (B_ρ ∖ B_σ). By 0.4, D = ∫_{(B_ρ∖B_σ)×G} ofReal(g/|y − x|^n) dV = ofReal(∫_{(B_ρ∖B_σ)×G} g/|y − x|^n dV), the integrand being nonnegative and V-integrable (bounded by σ^{-n} on a set of finite V-measure; ofReal_integral_eq_lintegral_ofReal). Write 5.3 as a + d ≤ b with a := e^{Λσ}m_σ/σ^n ≥ 0, d := ∫_{(B_ρ∖B_σ)×G} g/|y − x|^n dV ≥ 0 and b := e^{Λρ}m_ρ/ρ^n; apply ofReal (monotone, and additive on nonnegative reals) and use ofReal(e^{Λt}·m_t/t^n) = ofReal(e^{Λt})·ofReal(m_t)/ofReal(t)^n (ofReal_mul, ofReal_div_of_pos, ofReal_pow) together with ofReal(m_t) = μ(B_t) (ofReal_toReal, μ(B_t) finite by 0.1). This gives
   ofReal(e^{Λσ})·μ(B_σ)/ofReal(σ)^n + D ≤ ofReal(e^{Λρ})·μ(B_ρ)/ofReal(ρ)^n.        (3.3)
Multiplying (3.3) by the finite constant ω_n^{-1} and using 0.3 and distributivity:
   ofReal(e^{Λσ})·densityRatio n μ x σ + ω_n^{-1}·normalDefect V x (B_ρ ∖ B_σ) ≤ ofReal(e^{Λρ})·densityRatio n μ x ρ
for all 0 < σ ≤ ρ < ρ0 — the second inequality of the conclusion.

Step 7 (monotonicity). Let f(t) := ofReal(e^{Λt})·μ(B_t)/ofReal(t)^n. For σ, ρ ∈ (0, ρ0) with σ ≤ ρ, (3.3) and D ≥ 0 give f(σ) ≤ f(σ) + D ≤ f(ρ). Hence f is MonotoneOn (Ioo 0 ρ0); f is exactly the function in the contract (0.3).

Step 8 (the density θ). Let h(t) := ofReal(e^{Λt})·densityRatio n μ x t = ω_n^{-1}·f(t) (0.3). By Step 7, h is monotone on (0, ρ0) and bounded below by 0, so h(t) → θ := inf{h(s) : s ∈ (0, ρ0)} as t → 0+ (Mathlib MonotoneOn.tendsto_nhdsWithin_Ioo_right, Topology/Order/Monotone.lean:457). For t > 0, ofReal(e^{−Λt})·ofReal(e^{Λt}) = ofReal(1) = 1, so densityRatio n μ x t = ofReal(e^{−Λt})·h(t); as t → 0+, ofReal(e^{−Λt}) → 1, and multiplication on [0,∞] is continuous at (1, θ) because 1 ≠ 0 and 1 ≠ ∞ (ENNReal.Tendsto.mul), so densityRatio n μ x t → θ, i.e. HasDensity n μ x θ. For every σ ∈ (0, ρ0), θ ≤ h(σ) = ofReal(e^{Λσ})·densityRatio n μ x σ (θ is the infimum) — the first inequality of the conclusion. Finally θ ≤ h(ρ0/2) = ofReal(e^{Λρ0/2})·μ(B_{ρ0/2})/(ω_n·ofReal(ρ0/2)^n) < ∞ by 0.1–0.2, so θ ≠ ∞.

Step 9 (conclusion). Steps 6–8 give the monotonicity of f on (0, ρ0) and a θ with HasDensity n μ x θ, θ ≠ ∞, and both inequalities for all 0 < σ ≤ ρ < ρ0. Since N, n, U, V, x, ρ0, Λ were arbitrary, MonotonicityFormula holds. Nothing above uses n ≥ 1: for n = 0, t^0 = 1, ω_0 = 1 and the defect integrand equals g = 1 off y = x.

## Key steps

1. Preliminaries: μ_V(B_s(x)) < ∞ for 0 < s < ρ0; 0 < ω_n < ∞; densityRatio = ω_n^{-1}·μ_V(B_t)/ofReal(t)^n; the integrand identity |p_{S⊥}(y−x)|²/r^{n+2} = g/r^n with g = |p_{S⊥}((y−x)/r)|² (both 0 at y = x); ‖δV‖ = variationMeasure V = firstVariationRieszMeasure (dif_pos).
2. Radial cutoff fields X_t(y) = φ_ε(|y−x|²/t²)(y−x) (φ_ε = monotonicityCutoff ε) are test fields when (1+ε)t < ρ0, with |X_t| ≤ (1+ε)t·c_t and ∂_t c_t supported in t ≤ r ≤ (1+ε)t.
3. Radial identity (★): d/dt(I/t^n) = J'/t^n − δV(X_t)/t^{n+1} with I = ∫c_t dμ_V, J = ∫c_t g dV and J' ≥ 0 (SimonGMT hasDerivAt_normalized_weightedCutoffMass with h ≡ 1).
4. Polar representation (SimonGMT isFirstVariationPolarRepresentation_riesz) gives |δV(X_t)| ≤ (1+ε)t∫c_t d‖δV‖; the layer cake over the closed super-level sets {c_t ≥ s} = B_r(x), r < ρ0, and the hypothesis give ∫c_t d‖δV‖ ≤ Λ I(t).
5. Integrating factor: F = e^{Λ_ε t}I/t^n has F' ≥ J'/t^n ≥ G' with G = ∫c_t·g/max(σ,r)^n dV; the mean value theorem on [σ,ρ] gives F(ρ) − F(σ) ≥ G(ρ) − G(σ).
6. Let ε ↓ 0 by dominated convergence: e^{Λρ}μ_V(B_ρ)/ρ^n − e^{Λσ}μ_V(B_σ)/σ^n ≥ ∫_{(B_ρ∖B_σ)×G} g/r^n dV.
7. Pass to [0,∞] (all terms finite), identify the defect with normalDefect, multiply by ω_n^{-1}: the defect inequality; dropping the defect gives monotonicity of ofReal(e^{Λρ})μ_V(B_ρ)/ofReal(ρ)^n on (0,ρ0).
8. θ := inf over (0,ρ0) of ofReal(e^{Λt})·densityRatio(t) is its limit at 0+; since ofReal(e^{−Λt}) → 1, HasDensity n μ_V x θ; θ ≤ ofReal(e^{Λσ})·densityRatio(σ) and θ ≠ ∞.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all three 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'MonotonicityFormula|StationaryMonotonicityIdentity|DensityExistsAE' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean (defs at lines 238, 259, 273; conjuncts of main_theorem at 413)`
- `rg -l -i 'varifold' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib (0 files); rg -n -i 'monotonicity formula' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib (no match)`
- `rg -n 'theorem lintegral_eq_lintegral_meas_lt|theorem Measurable.liminf\b|theorem MonotoneOn.tendsto_nhdsWithin_Ioo_right|theorem tendsto_measure_iUnion_atTop|theorem measurable_measure_prodMk_left \[' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib`
- `rg -n 'tendsto_nhdsWithin_Ioo_right' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib; rg -n 'theorem lintegral_eq_lintegral_meas_le' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean; rg -n '^theorem withDensity_apply' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib; rg -n 'theorem Filter.Tendsto.liminf_eq' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib`
- `grep -n '^theorem\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/{StationaryMonotonicity,WeightedRadialIdentity,BallVariationBound,RadialFirstVariation,RadialCutoffDifferentiation,StationaryCutoff,FirstVariationRiesz}.lean`
- `grep -rn 'def scaledRadialCutoff\|def monotonicityCutoff\|theorem scaledRadialCutoffDeriv_support\|theorem tendsto_scaledRadialCutoff' .lake/packages/simongmt/Poincare/SimonGMT`
- `git -C .lake/packages/simongmt rev-parse HEAD (2b3663083f3fe399b6296fb8eaee52169170e197, matches lakefile/lake-manifest; worktree clean)`
- `lake env lean -o /tmp/mono_split_check/olean/GMT/Ch08/Submission.olean GMT/Ch08/Submission.lean (private olean; only the expected main_theorem sorry warning)`
- `lake env lean /tmp/mono_split_check/src/Types.lean (import GMT.Ch08.Submission + contract scope replay: the three child types elaborate as Prop; #check_failure shows Submission.monotonicity_formula_8_3_3 / stationary_monotonicity_identity_8_3_4 / density_exists_ae_8_3_6 are unused; ⟨hA, hB, hC⟩ checks against MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE)`
- `lake env lean /tmp/mono_split_check/src/Axioms.lean (#check of the cited SimonGMT and Mathlib lemmas; #print axioms of 15 cited SimonGMT lemmas)`
- `lake env lean /tmp/mono_split_check/src/Sanity.lean (0 < ω_n < ∞; variationMeasure V = firstVariationRieszMeasure hV under LBFV; normalDefect integrand = radialNormalSq/r^n for all (y,S) incl. y = x; centre integrand 0; densityRatio factorization; annularMonotonicityDefect = normalDefect on annuli; Tonelli measurability of a ↦ μ_V(closedBall a t))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/mono_split_check/src/Types.lean`
- `/tmp/mono_split_check/src/Axioms.lean`
- `/tmp/mono_split_check/src/Sanity.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its Contract.lean is byte-identical to the workspace Contract and Submission, and MonotonicityFormula / StationaryMonotonicityIdentity / DensityExistsAE are contract defs (lines 238/259/273). Mathlib has no varifold or monotonicity-formula material (0 matches), so the analytic content comes from the pinned SimonGMT package (rev 2b366308, clean): the Λ = 0 identity StationaryOn.stationaryMonotonicity (StationaryMonotonicity.lean:131) and its limit (:174) already exist; the general-Λ formula is new but all its ingredients exist — hasDerivAt_normalized_weightedCutoffMass (WeightedRadialIdentity.lean:200, h ≡ 1), hasDerivAt_integral_radialCutoff_of_radius (RadialCutoffDifferentiation.lean:91), tendsto_cutoffMass / tendsto_integral_radialCutoff / scaledRadialCutoffDeriv_defect_bounds (StationaryCutoff.lean:111/63/142), the polar representation isFirstVariationPolarRepresentation_riesz (FirstVariationRiesz.lean:133) and the a.e. ball bound ae_exists_ballFirstVariationBound_inside (BallVariationBound.lean:66), all needing only LBFV, so no child depends on the parent's sibling first_variation. #print axioms on the 15 cited SimonGMT lemmas shows only propext, Classical.choice, Quot.sound. Mathlib supplies the layer cake (Layercake.lean:445/496), Tonelli measurability measurable_measure_prodMk_left (Prod.lean:97), Measurable.liminf (BorelSpace/Order.lean:1058), MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457), tendsto_measure_iUnion_atTop (Continuity.lean:198) and Filter.Tendsto.liminf_eq (LiminfLimsup.lean:195). A scratch file importing a privately compiled GMT.Ch08.Submission with the contract scope shows the three child types elaborate, the three proposed Submission names are unused, and ⟨hA, hB, hC⟩ inhabits the frozen parent type; Sanity.lean kernel-checks the convention facts the child proofs rely on. The DAG (dag.json) reserves only the 13 depth-0/1 names; the proposed names are fresh. An independent reviewer agent found no mathematical errors in the three child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
