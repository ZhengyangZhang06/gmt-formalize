<!-- theorem-id: gmt-ch08/root.tangent_graph_cover-a1 -->

## Theorem `Submission.tangent_points_lipschitz_graph_cover`

Let N, n ∈ ℕ, 0 < L ≤ 1, U ⊆ ℝ^N open, V an n-varifold on U and P ∈ G(N,n), with p := Grassmannian.project P the orthogonal projection onto P and q := I − p. Then there are closed sets Γ_0, Γ_1, … ⊆ ℝ^N, each an L-Lipschitz graph over P, i.e. |q(y − z)| ≤ L|p(y − z)| (‖(y − z) − Grassmannian.project P (y − z)‖ ≤ L‖Grassmannian.project P (y − z)‖) for all y, z ∈ Γ_i, such that every x at which V has a tangent plane T with some multiplicity θ in the sense of Def. 8.1.1 (HasTangentPlane V x T θ) and whose plane is L/4-close to P in operator norm (|p_T v − p v| ≤ (L/4)|v| for all v) lies in some Γ_i.

Node: `root.tangent_graph_cover-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/644, https://github.com/ZhengyangZhang06/gmt-formalize/issues/646, https://github.com/ZhengyangZhang06/gmt-formalize/issues/648, https://github.com/ZhengyangZhang06/gmt-formalize/issues/652, https://github.com/ZhengyangZhang06/gmt-formalize/issues/654, https://github.com/ZhengyangZhang06/gmt-formalize/issues/659, https://github.com/ZhengyangZhang06/gmt-formalize/issues/662

## Lean problem

Declaration: `Submission.tangent_points_lipschitz_graph_cover`

```lean
∀ (N n : ℕ) (L : ℝ), 0 < L → L ≤ 1 → ∀ (U : Set (Euclidean N)) (V : Varifold N n U) (P : Grassmannian N n), ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) → ∃ i, x ∈ Γ i
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
- Child DAG node: `root.tangent_graph_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is the cone/Lipschitz-graph argument of Simon's printed proof of Ch. 3, Theorem 1.6 “⇐” (the definitions (1)–(3), estimate (9), claim (10) and the graph construction following it, printed pp. 72–74), which the printed proof of Ch. 8, Theorem 1.2 invokes through “1.9 of Ch. 3” (Ch. 3, 1.9 is derived from 1.6 via Remark 1.8). Here it is run directly for the weight measure of a varifold at its tangent points in the sense of Ch. 8, Def. 1.1, with two adaptations: (a) Egoroff's theorem (printed (8)) is replaced by a countable decomposition into classes with uniform constants, so that EVERY admissible tangent point (not only almost every one) is covered; (b) the aperture of the cones is adapted to an arbitrary prescribed slope L ∈ (0,1] relative to a fixed reference plane P (the printed proof uses a fixed aperture and slope ≤ 4 relative to finitely many reference planes). Notation: μ := μ_V = V.weight; G := Grassmannian N n; for S ∈ G, p_S := Grassmannian.project S (the orthogonal projection onto S.plane: symmetric and idempotent, so |v|² = |p_S v|² + |v − p_S v|²) and q_S := I − p_S; p := p_P, q := q_P; B_r(y) := closedBall y r; H^n := μHE[n]; ω_n := unitBallVolume n ∈ (0,∞) (ω_0 = 1); V_{x,t} := rescaledMeasure V x t; v(T) := planeVarifoldMeasure T. “Γ is an L-graph over P” means |q(y − z)| ≤ L|p(y − z)| for all y, z ∈ Γ — in Lean notation ‖(y − z) − Grassmannian.project P (y − z)‖ ≤ L * ‖Grassmannian.project P (y − z)‖; “‖p_T − p‖ ≤ L/4” means |p_T v − p v| ≤ (L/4)|v| for every v ∈ ℝ^N.

Statement. Let N, n ∈ ℕ, 0 < L ≤ 1, U ⊆ ℝ^N open, V an n-varifold on U and P ∈ G. Then there are closed sets Γ_0, Γ_1, … ⊆ ℝ^N, each an L-graph over P, such that every x ∈ ℝ^N for which there are T ∈ G and θ ∈ ℝ with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 belongs to some Γ_i.

1. Consequences of Def. 1.1 at a point. Let HasTangentPlane V x T θ: x ∈ U, θ > 0, and ∫ f dV_{x,t} → θ∫ f dv(T) as t ↓ 0 for every f ∈ C_c(ℝ^N × G).
 (1.1) Weight blow-ups. For g ∈ C_c(ℝ^N) the function f(y,S) := g(y) lies in C_c(ℝ^N × G), because G is compact (tsupport f ⊆ tsupport g × G). By the definitions (V_{x,t} = ofReal(t^{−n}) • V.measure.map((z,S) ↦ (t^{−1}(z − x), S)), integral_map, and V.weight = V.measure.map Prod.fst), ∫ f dV_{x,t} = t^{−n}∫ g((z − x)/t) dμ(z) (for small t the integrand is supported in the compact set x + t·tsupport g ⊆ U, where μ is finite), and ∫ f dv(T) = ∫_{T.plane} g dH^n (v(T) = (H^n⌞T.plane).map(y ↦ (y,T))). Writing ν_t(A) := t^{−n}μ(x + tA), this says ∫ g dν_t → θ∫_{T.plane} g dH^n as t ↓ 0, for every g ∈ C_c(ℝ^N).
 (1.2) Normalisation. T.plane has dimension n (Grassmannian.finrank_plane), so there is a linear isometry ι of ℝ^n = EuclideanSpace ℝ (Fin n) onto T.plane (an orthonormal basis), and H^n(ι(A)) = L^n(A) for every A ⊆ ℝ^n (Mathlib Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence H^n(T.plane ∩ B_κ(0)) = L^n(B^n_κ(0)) = ω_nκ^n for κ > 0 (Measure.addHaar_closedBall; closed and open balls have the same volume).
 (1.3) Lower mass bound. For κ ∈ (0,1) take g ∈ C_c(ℝ^N) with 0 ≤ g ≤ 1, g = 1 on B_κ(0) and tsupport g ⊆ B_1(0). Then t^{−n}μ(B_t(x)) = ν_t(B_1(0)) ≥ ∫ g dν_t → θ∫_{T.plane} g dH^n ≥ θH^n(T.plane ∩ B_κ(0)) = θω_nκ^n. Letting κ ↑ 1: liminf_{t↓0} t^{−n}μ(B_t(x)) ≥ θω_n.
 (1.4) Cone decay (n ≥ 1). For α ∈ (0,1) let K_α(T) := {v ∈ ℝ^N : |p_T v| ≤ α|v|}, a closed cone (invariant under v ↦ sv, s > 0). Then t^{−n}μ((x + K_α(T)) ∩ B_t(x)) → 0 as t ↓ 0. Indeed C := K_α(T) ∩ B_1(0) is compact, C ∩ T.plane = {0} (for v ∈ T.plane, p_T v = v, and |v| ≤ α|v| forces v = 0), and (x + K_α(T)) ∩ B_t(x) = x + tC, so the quantity equals ν_t(C). For κ ∈ (0,1] let C_κ := {v : dist(v, C) ≤ κ} (compact) and choose g ∈ C_c(ℝ^N), 0 ≤ g ≤ 1, g = 1 on C, tsupport g ⊆ C_κ (Urysohn). Then limsup_t ν_t(C) ≤ lim_t ∫ g dν_t = θ∫_{T.plane} g dH^n ≤ θH^n(T.plane ∩ C_κ). As κ ↓ 0 the sets T.plane ∩ C_κ decrease to T.plane ∩ C = {0} (C is closed), and H^n(T.plane ∩ C_1) < ∞ by (1.2), so H^n(T.plane ∩ C_κ) → H^n({0}) = 0 (n ≥ 1). Hence ν_t(C) → 0.

2. Degenerate dimensions. If n > N there is no P ∈ G (a symmetric idempotent N × N matrix has trace ≤ N), and the claim is vacuous. If n = 0, G has exactly one element, the zero projection (a symmetric idempotent matrix of trace 0 is 0), so p = p_T = 0, q = I, and an L-graph over P is a set with at most one point. If HasTangentPlane V x T θ, then (1.3) with t^0 = 1 and ω_0 = 1 gives liminf_{t↓0} μ(B_t(x)) ≥ θ > 0; since x ∈ U, μ(B_t(x)) < ∞ for small t (V.finite_on_compact), so by continuity from above μ({x}) = lim_{t↓0} μ(B_t(x)) ≥ θ > 0: x is an atom of μ. The measure μ is σ-finite (Varifold.weight.instSigmaFinite), so it has at most countably many atoms a_0, a_1, …; put Γ_i := {a_i} (and Γ_i := ∅ for unused indices). Singletons and ∅ are closed L-graphs, and every point in question is an atom, hence some a_i. This proves the claim for n = 0. Assume 1 ≤ n ≤ N from now on. (For n = N the claim is also trivial — then P is the identity, q = 0 and Γ_0 := ℝ^N works — but the argument below covers it.)

3. Linear algebra. Put c := L/4, γ := c/2 = L/8 and α := (1 − c²/16)^{1/2} = (1 − L²/256)^{1/2} ∈ (0,1). Let T ∈ G with ‖p_T − p‖ ≤ L/4; then also |q_T v − q v| = |p v − p_T v| ≤ (L/4)|v|.
 (3.1) If v ∈ ℝ^N and |q v| > L|p v|, then v ≠ 0 and |q_T v| > c|v|. Indeed |q v|² > L²|p v|² = L²(|v|² − |q v|²) gives |q v| > L|v|/(1 + L²)^{1/2} ≥ L|v|/√2 (as L ≤ 1), so |q_T v| ≥ |q v| − (L/4)|v| > (1/√2 − 1/4)L|v| ≥ (L/4)|v|.
 (3.2) If moreover w ∈ ℝ^N with |w − v| ≤ γ|v|, then w ∈ K_α(T) and 0 < |w| ≤ 2|v|. Indeed |w| ≤ (1 + γ)|v| ≤ 2|v| and |w| ≥ (1 − γ)|v| > 0; |q_T w| ≥ |q_T v| − |q_T(w − v)| ≥ |q_T v| − |w − v| > (c − γ)|v| = (c/2)|v| ≥ (c/4)|w|; hence |p_T w|² = |w|² − |q_T w|² ≤ (1 − c²/16)|w|², i.e. |p_T w| ≤ α|w|.

4. Uniform classes (replacing Egoroff, printed (7)–(9)). For m ≥ 1 put ε_m := (2m)^{−1}(γ/2)^n/2 > 0. For m, k ≥ 1 let E_{m,k} be the set of x ∈ ℝ^N for which there are T ∈ G and θ ∈ ℝ with HasTangentPlane V x T θ, ‖p_T − p‖ ≤ L/4, θ ≥ 1/m, and, for every t ∈ (0, 1/k],
 (i) μ(B_t(x)) ≥ (2m)^{−1}ω_n t^n, and (ii) μ((x + K_α(T)) ∩ B_t(x)) ≤ ε_m ω_n t^n.
 Every x with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 lies in some E_{m,k}: choose m with θ ≥ 1/m (θ > 0); by (1.3), liminf_t t^{−n}μ(B_t(x)) ≥ θω_n ≥ ω_n/m > (2m)^{−1}ω_n, and by (1.4), t^{−n}μ((x + K_α(T)) ∩ B_t(x)) → 0 < ε_mω_n; so (i) and (ii) hold for all t ∈ (0, 1/k] once k is large enough.

5. Graph property (printed (10)). CLAIM: if x, x' ∈ E_{m,k} and |x' − x| ≤ 1/(2k), then |q(x' − x)| ≤ L|p(x' − x)|. Suppose not, and put v := x' − x, s := |v|; then |q v| > L|p v|, so v ≠ 0 by (3.1) and 0 < s ≤ 1/(2k). Let T be a plane witnessing x ∈ E_{m,k}. For z ∈ B_{γs}(x') the vector w := z − x satisfies |w − v| = |z − x'| ≤ γs = γ|v|, so by (3.2) w ∈ K_α(T) and |w| ≤ 2s; that is, B_{γs}(x') ⊆ (x + K_α(T)) ∩ B_{2s}(x). Since 0 < γs ≤ 2s ≤ 1/k, (i) at x' (with t = γs) and (ii) at x (with t = 2s) give
 (2m)^{−1}ω_n(γs)^n ≤ μ(B_{γs}(x')) ≤ μ((x + K_α(T)) ∩ B_{2s}(x)) ≤ ε_mω_n(2s)^n = (2m)^{−1}ω_nγ^ns^n/2,
 which is impossible because ω_nγ^ns^n > 0. (This is the printed contradiction between (9) at the base point and the ball around the point y in (10), with the cone aperture adapted to L.)

6. Closed graph pieces (printed paragraph after (10)). Let D ⊆ ℝ^N be countable and dense (points with rational coordinates). For m, k ≥ 1 and d ∈ D put Γ_{m,k,d} := closure(E_{m,k} ∩ B_{1/(4k)}(d)). If y, z ∈ E_{m,k} ∩ B_{1/(4k)}(d), then |y − z| ≤ 1/(2k), so |q(y − z)| ≤ L|p(y − z)| by step 5; since (y,z) ↦ L|p(y − z)| − |q(y − z)| is continuous, the inequality persists on the closure. Hence each Γ_{m,k,d} is a closed L-graph over P. Every x ∈ E_{m,k} lies in B_{1/(4k)}(d) for some d ∈ D (density of D). Enumerate the countable family (Γ_{m,k,d})_{m,k ≥ 1, d ∈ D} as (Γ_i)_{i ∈ ℕ}. By step 4, every x with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 lies in some E_{m,k}, hence in some Γ_i. Together with step 2 this proves the statement: ∃ Γ : ℕ → Set ℝ^N with every Γ i closed, every Γ i an L-graph over P (‖(y − z) − Grassmannian.project P (y − z)‖ ≤ L‖Grassmannian.project P (y − z)‖ for y, z ∈ Γ i), and every such tangent point in some Γ i.

## Key steps

1. Testing Def. 1.1 with f(y,S) = g(y): weight blow-ups t^{−n}μ_V(x + t·) → θH^n⌞T; lower mass bound liminf t^{−n}μ_V(B_t(x)) ≥ θω_n; cone decay t^{−n}μ_V((x + K_α(T)) ∩ B_t(x)) → 0 for n ≥ 1 (K_α(T) = {|p_T v| ≤ α|v|}, C ∩ T = {0}).
2. n > N is vacuous; for n = 0 every tangent point is an atom of the σ-finite μ_V, and singletons are L-graphs.
3. Linear algebra: if |q v| > L|p v| and ‖p_T − p‖ ≤ L/4 then |q_T v| > (L/4)|v|, and every w with |w − v| ≤ (L/8)|v| lies in K_α(T), α = (1 − L²/256)^{1/2}.
4. Classes E_{m,k} (θ ≥ 1/m, μ(B_t) ≥ (2m)^{−1}ω_nt^n and cone mass ≤ ε_mω_nt^n for t ≤ 1/k) cover every admissible tangent point (replacing Egoroff).
5. Printed (10): two points of E_{m,k} within 1/(2k) violating the L-graph inequality would put a ball of mass ≥ (2m)^{−1}ω_n(γs)^n inside a cone region of mass ≤ ε_mω_n(2s)^n — contradiction.
6. Closures of E_{m,k} ∩ B_{1/(4k)}(d), d in a countable dense set, are closed L-graphs over P covering all admissible tangent points; enumerate them by ℕ.

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

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
