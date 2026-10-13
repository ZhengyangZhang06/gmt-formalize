<!-- theorem-id: gmt-ch08/root.allard_tangent_cones-a1 -->

## Theorem `Submission.allard_rectifiability_and_tangent_cones`

If V has locally bounded first variation in open U ⊆ ℝ^N and Θ^n(μ_V,x) exists and is > 0 for μ_V-a.e. x, then V is rectifiable (IsRectifiable V: V = v(M,θ) for some M, θ) and V has a tangent plane with positive multiplicity in the sense of Def. 1.1 at μ_V-a.e. x. Moreover (Simon 5.7): let V have locally bounded first variation, x ∈ U, θ0 > 0, Θ^n(μ_V,x) = θ0, ρ^{1−n}‖δV‖(B_ρ(x)) → 0, and ρ^{-n}μ_V({y ∈ B_ρ(x) : not (Θ^n(μ_V,y) exists and ≥ 1)}) → 0 as ρ ↓ 0. Then every C ∈ VarTan(V,x) is rectifiable and η_{0,s#}C = C (rescaledMeasure C 0 s = C.measure) for all s > 0. (Exactly AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones.)

Node: `root.allard_tangent_cones-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/313, https://github.com/ZhengyangZhang06/gmt-formalize/issues/315, https://github.com/ZhengyangZhang06/gmt-formalize/issues/320, https://github.com/ZhengyangZhang06/gmt-formalize/issues/324, https://github.com/ZhengyangZhang06/gmt-formalize/issues/327, https://github.com/ZhengyangZhang06/gmt-formalize/issues/332

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/795, https://github.com/ZhengyangZhang06/gmt-formalize/issues/797, https://github.com/ZhengyangZhang06/gmt-formalize/issues/798, https://github.com/ZhengyangZhang06/gmt-formalize/issues/801, https://github.com/ZhengyangZhang06/gmt-formalize/issues/803, https://github.com/ZhengyangZhang06/gmt-formalize/issues/804, https://github.com/ZhengyangZhang06/gmt-formalize/issues/805, https://github.com/ZhengyangZhang06/gmt-formalize/issues/807, https://github.com/ZhengyangZhang06/gmt-formalize/issues/811, https://github.com/ZhengyangZhang06/gmt-formalize/issues/815

## Lean problem

Declaration: `Submission.allard_rectifiability_and_tangent_cones`

```lean
AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones
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
- Child DAG node: `root.allard_tangent_cones-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This child proves both conjuncts. PART A is AllardRectifiabilityTheorem (Simon 5.5 with Remark 5.6); PART B is TangentConesAreRectifiableCones (Simon 5.7), whose printed proof uses 5.5, here Part A.

==== PART A: AllardRectifiabilityTheorem (5.5, 5.6).
Source: Simon, Ch. 8, Theorem 5.5, Remark 5.6 and the printed proof of 5.5 (pp. 215–218). ERRATA: in printed (5), “Θ^n(μ_{V_j}, y) ≤ θ0 − ε_j” must read “≥ θ0 − ε_j” (it is the rescaling of (3)); 5.2 is read with centre 0 (μ_C(B_ρ(0))). Details filled in: the use of 3.7 in (3)–(7) is exactly the second conjunct of the sibling varifold_tangents (blow-up density lower bound) applied with τ = θ0 − ε; “(and hence for every y ∈ spt μ_C by 3.4)” is the upper semicontinuity of the density of a stationary varifold; “C = θ0 v(T) by Constancy 4.1” is the sibling constancy with U = ℝ^N, M = T. Notation: μ = μ_V, Θ(y) := Θ^n(μ, y), G = Grassmannian N n, B_ρ(y) closed ball, V_{x,λ} = rescaledMeasure V x λ, v(T) = planeVarifoldMeasure T, ω_n = unitBallVolume n, VarTan(V,x) = {C : IsVarifoldTangent V x C}.

Statement. If V has locally bounded first variation in U and Θ^n(μ, x) exists and is > 0 for μ-a.e. x, then V has a tangent plane in the sense of 1.1 (HasTangentPlane V x T θ for some T, θ) at μ-a.e. x, and V is rectifiable (IsRectifiable V).

STEP A1 (good points, Remark 5.6). Let x satisfy:
 (i) x ∈ U and Θ(x) = θ0 ∈ (0,∞) — μ-a.e. by hypothesis and the sibling monotonicity_density (third conjunct DensityExistsAE: finiteness a.e.), μ(Uᶜ) = 0;
 (ii) the conclusion of Lemma 1.3 at x: η(x) is a probability measure on G and for every β ∈ C(G), ∫_{Gₙ(B_ρ(x))} β dV / μ(B_ρ(x)) → ∫ β dη(x) — μ-a.e. by the sibling plane_disintegration;
 (iii) Θ is μ-approximately continuous at x: with the Borel function Θ̃ of the sibling monotonicity_density (third conjunct DensityExistsAE) (Θ̃ = Θ, finite, μ-a.e.), for every ε > 0, μ({y ∈ B_ρ(x) : |Θ̃(y) − Θ̃(x)| ≥ ε})/μ(B_ρ(x)) → 0 — μ-a.e. by the Lebesgue differentiation theorem for the Radon measure μ on U (Ch. 1 3.16–3.17; Mathlib Besicovitch.ae_tendsto_measure_inter_div applied, on a compact exhaustion of U, to the countably many Borel sets {Θ̃ ∈ (a,b)}, a < b rational), together with Θ̃(x) = Θ(x);
 (iv) ‖δV‖(B_ρ(x)) ≤ Λ(x) μ(B_ρ(x)) for 0 < ρ < ρ0, with ball x ρ0 ⊆ U and Λ(x) < ∞ — μ-a.e. by 2.7 (sibling first_variation; SimonGMT ae_exists_ballFirstVariationBound_inside).
 Conditions (i)–(iv) hold for μ-a.e. x. Fix such an x.

STEP A2 (5.1 holds at x). By (iv) and (i), ρ^{1−n}‖δV‖(B_ρ(x)) ≤ Λ(x) ρ · μ(B_ρ(x))/ρ^n = Λ(x) ω_n ρ · densityRatio(ρ) → 0. So by the sibling varifold_tangents (VarifoldTangentCones): every sequence λ_j ↓ 0 has a subsequence along which V_{x,λ_j} converges to some C (in particular VarTan(V,x) ≠ ∅), and every C ∈ VarTan(V,x) is stationary in ℝ^N and satisfies
 (1) μ_C(B_ρ(0)) = θ0 ω_n ρ^n for all ρ > 0.
Fix C ∈ VarTan(V,x), along λ_j > 0, λ_j → 0.

STEP A3 (printed (2): Θ^n(μ_C, y) ≤ μ_C(B_ρ(y))/(ω_nρ^n) ≤ θ0). C is stationary in ℝ^N, so by the sibling monotonicity_density (3.3 with Λ = 0, or the identity 3.4) for every y the ratio ρ ↦ μ_C(B_ρ(y))/(ω_nρ^n) is non-decreasing on (0,∞) and Θ^n(μ_C, y) exists. For R > 0, B_R(y) ⊆ B_{R+|y|}(0), so by (1): μ_C(B_ρ(y))/(ω_nρ^n) ≤ μ_C(B_R(y))/(ω_nR^n) ≤ μ_C(B_{R+|y|}(0))/(ω_n(R+|y|)^n)·(1+|y|/R)^n = θ0(1+|y|/R)^n → θ0 as R → ∞. Hence Θ^n(μ_C, y) ≤ μ_C(B_ρ(y))/(ω_nρ^n) ≤ θ0 for all y and ρ > 0.

STEP A4 (printed (3)–(7): Θ^n(μ_C, ·) ≥ θ0 μ_C-a.e.). Let 0 < ε < θ0 and τ := θ0 − ε. By (iii) and (i): writing E_τ := {y : ¬ ∃ θ, HasDensity n μ y θ ∧ ofReal τ ≤ θ}, we have E_τ ⊆ N ∪ {y : Θ̃(y) < θ0 − ε} with N μ-null (where Θ̃(y) ≠ ∞ ∧ HasDensity n μ y (Θ̃ y) fails), so μ(E_τ ∩ B_ρ(x)) ≤ μ({y ∈ B_ρ(x) : |Θ̃(y) − θ0| ≥ ε}) = o(μ(B_ρ(x))) = o(ρ^n) (μ(B_ρ(x)) ≤ 2θ0ω_nρ^n for small ρ). This is printed (3)–(6) (G := {Θ ≥ θ0 − ε}, with the corrected inequality in (5)). Together with 5.1 (Step A2), the second conjunct of the sibling varifold_tangents (the 3.7 argument on rescalings) gives: for μ_C-a.e. y, Θ^n(μ_C, y) ≥ θ0 − ε. Intersecting over ε = θ0/k: (7) Θ^n(μ_C, y) ≥ θ0 for μ_C-a.e. y.

STEP A5 (printed “(and hence for every y ∈ spt μ_C by 3.4)”). Upper semicontinuity: for y ∈ spt μ_C there are y_k → y with Θ^n(μ_C, y_k) ≥ θ0 (the set where (7) holds is μ_C-conull, hence dense in spt μ_C); for ρ > 0, by the monotonicity of Step A3 at y_k, Θ^n(μ_C, y_k) ≤ μ_C(B_ρ(y_k))/(ω_nρ^n) ≤ μ_C(B_{ρ+|y_k−y|}(y))/(ω_nρ^n), so θ0 ≤ μ_C(B_{ρ'}(y))/(ω_nρ^n) for every ρ' > ρ, hence (closed balls, continuity from above) θ0 ≤ μ_C(B_ρ(y))/(ω_nρ^n) for all ρ, and Θ^n(μ_C, y) ≥ θ0. With Step A3: Θ^n(μ_C, y) = θ0 = μ_C(B_ρ(y))/(ω_nρ^n) for all y ∈ spt μ_C and ρ > 0.

STEP A6 (printed (8): x' − y ∈ S). Fix y ∈ spt μ_C. The sibling monotonicity_density (second conjunct StationaryMonotonicityIdentity for C at centre y, any ρ0) gives Θ^n(μ_C,y) + ω_n^{-1}normalDefect C y (B_ρ(y)) = μ_C(B_ρ(y))/(ω_nρ^n), so by Step A5 normalDefect C y (B_ρ(y)) = 0 for all ρ: p_{S⊥}(x' − y) = 0 for C-a.e. (x', S). As (x',S) ↦ p_{S⊥}(x' − y) is continuous, x' − y ∈ S for every (x',S) ∈ spt C. Hence (8): x' − y ∈ S for all y ∈ spt μ_C and (x',S) ∈ spt C.

STEP A7 (C = θ0 v(T), printed via Constancy 4.1). By (1), μ_C(B_ρ(0)) > 0 for all ρ, so 0 ∈ spt μ_C = π(spt C) (G compact; SimonGMT weight_support_eq_fst_image_support, ConstancyTangentGraph.lean): choose T with (0,T) ∈ spt C. By (8) with (x',S) = (0,T): −y ∈ T, i.e. y ∈ T, for all y ∈ spt μ_C; so spt μ_C ⊆ T. Apply the sibling constancy (ConstancyTheorem) with U = ℝ^N, V = C (stationary), M = T (an n-plane is an n-dimensional C² Simon submanifold via a linear isometric parametrisation ℝ^n → T; T ∩ ℝ^N = T is convex, hence preconnected; classicalTangentSpace T x = T for x ∈ T): C(A) = θ' H^n({x ∈ T : (x,T) ∈ A}) = θ' v(T)(A) for some θ' ≥ 0 (a Grassmannian point is determined by its plane). By (1), θ' ω_n ρ^n = θ0 ω_n ρ^n (H^n(T ∩ B_ρ(0)) = ω_nρ^n), so θ' = θ0: every C ∈ VarTan(V,x) is θ0 v(T) for some n-plane T.

STEP A8 (uniqueness, printed (9)). Let θ0 v(T) ∈ VarTan(V,x) along λ_j, and β ∈ C(G). Since θ0 v(T)(∂B_1(0) × G) = θ0 H^n(T ∩ ∂B_1(0)) = 0 (n ≥ 1; for n = 0, T ∩ ∂B_1(0) = ∅), the portmanteau property (convergence of ∫ F for bounded F with compact support whose discontinuity set is null for the limit) gives ∫_{B_1(0)×G} β dV_{x,λ_j}/V_{x,λ_j}(B_1(0)×G) → θ0∫_{T∩B_1(0)} β(T) dH^n/(θ0 ω_n) = β(T). By the definition of V_{x,λ} (change of variables), this ratio equals ∫_{Gₙ(B_{λ_j}(x))} β dV / μ(B_{λ_j}(x)), which by (ii) converges to ∫ β dη(x). Hence β(T) = ∫ β dη(x) for every β ∈ C(G). Continuous functions separate the points of the metric space G, so T is uniquely determined by η(x): VarTan(V,x) = {θ0 v(T_x)} for a single n-plane T_x.

STEP A9 (full limit). For each f ∈ C_c(ℝ^N × G), every sequence λ_j → 0+ has (Step A2) a subsequence along which ∫ f dV_{x,λ_j} → θ0 ∫ f dv(T_x) (the limit lies in VarTan(V,x) = {θ0 v(T_x)}). A real function of λ all of whose sequential limits along every λ_j → 0+ have sub-subsequences converging to the same value converges along 𝓝[>]0 to that value. Hence lim_{λ↓0} V_{x,λ} = θ0 v(T_x): HasTangentPlane V x T_x θ0 (x ∈ U, θ0 > 0; θ0 is real here, θ0 = Θ(x).toReal).

STEP A10 (conclusion; “the required rectifiability of V will then follow from 1.2”). By Steps A1–A9, V has a tangent plane at μ-a.e. x (second conclusion). The sibling first_rectifiability (FirstRectifiabilityTheorem) then gives θ with IsVarifoldOf V M θ for M = {x ∈ spt μ : ∃ T θ', HasTangentPlane V x T θ'}, hence IsRectifiable V. This proves AllardRectifiabilityTheorem.

==== PART B: TangentConesAreRectifiableCones (5.7).
Source: Simon, Ch. 8, Corollary 5.7 and its printed proof (p. 216). ERRATA/READINGS: 5.3 is used in its corrected form μ_C(sA) = s^n μ_C(A) (sibling varifold_tangents); the hypothesis “{y ∈ B_ρ(x) : Θ^n(μ_V,y) < 1}” is read, as in the contract, as the set where “Θ^n(μ_V,y) exists and is ≥ 1” fails. Details filled in: (a) the printed “from the hypothesis … and the Semi-continuity 3.7” is the second conjunct of the sibling varifold_tangents with τ = 1; (b) the printed step “we can write C = v(M,θ) with η_{0,λ}(M) = M and θ(λy) = θ(y) … hence η_{0,λ#}C = C” is carried out with the canonical representation of the sibling first_rectifiability (tangent points, multiplicity = density) and the fact that approximate tangent planes depend only on the weight; the printed intermediate remark “y ∈ T_yM” is not needed — what is used is T_{sy}M = T_yM. Notation: μ_C = C.weight, H^n = μHE[n], G = Grassmannian N n, B_ρ(y) closed ball, C_{y,t} := rescaledMeasure C y t (t^{-n}·image of C under (z,S) ↦ ((z−y)/t, S)), v(T) = planeVarifoldMeasure T, ω_n = unitBallVolume n.

Statement. Let V have locally bounded first variation, x ∈ U, θ0 > 0, Θ^n(μ_V, x) = θ0, ρ^{1−n}‖δV‖(B_ρ(x)) → 0 (5.1), and ρ^{-n} μ_V({y ∈ B_ρ(x) : ¬(Θ^n(μ_V,y) exists and ≥ 1)}) → 0 as ρ ↓ 0. Then every C ∈ VarTan(V,x) (IsVarifoldTangent V x C) is rectifiable and rescaledMeasure C 0 s = C.measure for all s > 0.

STEP B1 (Θ^n(μ_C, ·) ≥ 1 a.e.; printed first sentence). The hypotheses are those of the second conjunct of the sibling varifold_tangents with τ = 1 (ofReal 1 = 1). Hence for μ_C-a.e. y, Θ^n(μ_C, y) exists and is ≥ 1.

STEP B2 (C is rectifiable; printed “Hence by 5.5”). By the first conjunct of the sibling varifold_tangents (VarifoldTangentCones (b)), C is stationary in ℝ^N, hence has locally bounded first variation (Stationary.hasLocallyBoundedFirstVariation), and μ_C(sA) = s^n μ_C(A) for all s > 0 and A ⊆ ℝ^N. By Step B1, Θ^n(μ_C,·) > 0 μ_C-a.e., so Part A of this proof (AllardRectifiabilityTheorem) applied to C (U = ℝ^N) gives IsRectifiable C (first conclusion) and: (T) for μ_C-a.e. y there are T_y ∈ G, θ_y > 0 with HasTangentPlane C y T_y θ_y.

STEP B3 (canonical representation). Basic facts at a tangent point (proved directly from Def. 1.1): if HasTangentPlane C y T θ then (a) testing with f(z,S) = g(z), g ∈ C_c(ℝ^N), gives t^{-n}∫ g((z−y)/t) dμ_C(z) → θ∫_T g dH^n; (b) approximating 1_{B_1(0)} from above and below by such g and using H^n(T ∩ ∂B_1(0)) = 0 (n ≥ 1; for n = 0, T = {0}), μ_C(B_t(y))/(ω_nt^n) → θ H^n(T ∩ B_1(0))/ω_n = θ, i.e. Θ^n(μ_C, y) = θ; (c) consequently θ is unique, and θH^n⌞T is determined by μ_C (Riesz uniqueness), so T = its support is unique. By (T) and the sibling first_rectifiability applied to C: with M := {y ∈ spt μ_C : ∃ T θ', HasTangentPlane C y T θ'} there is θ with HasTangentPlane C y T(y) θ(y) for every y ∈ M, where by (a)–(c) θ(y) = Θ^n(μ_C, y) > 0 and T(y) is the unique plane with t^{-n}(η_{y,t})_#μ_C → θ(y)H^n⌞T(y), and IsVarifoldOf C M θ. Write M* := {y ∈ M : ∃ S, HasWeightedApproximateTangentSpaceAt n M θ y S.plane}. From IsVarifoldOf (taking A = B × G): μ_C = θ H^n ⌞ M* and C(A) = ∫_{{y ∈ M* : (y, S_y) ∈ A}} θ dH^n with S_y the (unique, θ(y) > 0) approximate tangent plane.
 (B3a) μ_C = θ H^n ⌞ M. Let ν := H^n ⌞ M, which is σ-finite (θ > 0 and θ is integrable on M ∩ K for compact K), and let M' := M ∩ toMeasurable(M*), the measurable hull being taken w.r.t. the s-finite measure ν = H^n⌞M; then M* ⊆ M' ⊆ M, M' is H^n-null-measurable and ν(B ∩ M') = ν(B ∩ M*) for Borel B (Mathlib measure_toMeasurable_inter_of_sFinite). The IsVarifoldOf identity with A = B × G reads μ_C(B) = ∫_{M*∩B} θ dH^n = ∫_{M'∩B} θ dν, so μ_C = θ ν⌞M' and μ_C(M ∖ M') = 0. On M ∖ M', Θ^n(μ_C, y) = θ(y) > 0 (every y ∈ M is a tangent point of C, whose density is its multiplicity by (b)). For each k, μ_C being a locally finite Borel measure on ℝ^N and hence outer regular, and μ_C((M ∖ M') ∩ {θ ≥ 1/k}) = 0, there are open O ⊇ (M ∖ M') ∩ {θ ≥ 1/k} of arbitrarily small μ_C-measure, and Ch. 1 3.3 (A_1 = (M∖M') ∩ {θ ≥ 1/k}, A_2 = O) gives (1/k)H^n(A_1) ≤ μ_C(O); hence H^n(M ∖ M') = 0 and μ_C = θ H^n ⌞ M.
 (B3b) Hence, for y ∈ M, the weighted blow-up of (M,θ) is the weight blow-up of μ_C: ∫_{η_{y,r}(M)} f(w) θ(y + r w) dH^n(w) = r^{-n} ∫ f((z−y)/r) dμ_C(z) → θ(y) ∫_{T(y)} f dH^n (HasTangentPlane tested on f(z,S) = f(z)). So M* = M and S_y = T(y), i.e.
 (★) C(A) = ∫_{{y ∈ M : (y, T(y)) ∈ A}} θ dH^n for Borel A ⊆ ℝ^N × G,
 where, for y ∈ M, θ(y) and T(y) are determined by μ_C alone: θ(y)H^n⌞T(y) = lim_{r↓0} r^{-n}(η_{y,r})_#μ_C.

STEP B4 (scale invariance of the weight blow-ups; printed “Θ^n(μ_C, y) = Θ^n(μ_C, λy) (by 5.3)”). Fix s > 0. From μ_C(sA) = s^nμ_C(A) we get ∫ g(z/s) dμ_C(z) = s^n ∫ g dμ_C for Borel g ≥ 0 or g ∈ C_c. Hence for f ∈ C_c(ℝ^N), r > 0 and y ∈ ℝ^N: (sr)^{-n} ∫ f((z − sy)/(sr)) dμ_C(z) = r^{-n} ∫ f((w − y)/r) dμ_C(w) (substitute z = s w). So the weight blow-ups of μ_C at sy (scale sr) coincide with those at y (scale r). Consequently, if y ∈ M and sy ∈ M then θ(sy) = θ(y) and T(sy) = T(y) (uniqueness of the limit measure θH^n⌞T, whose support is T).

STEP B5 (M is a cone up to null sets). Let M_s := {y ∈ M : sy ∈ M}. Then μ_C(M ∖ M_s) ≤ μ_C(s^{-1}·(ℝ^N ∖ M)) = s^{-n}μ_C(ℝ^N ∖ M) = 0 (μ_C is carried by M), and since μ_C = θH^n⌞M with θ > 0 on M, H^n(M ∖ M_s) = 0. Likewise H^n(M ∖ M_{1/s}) = 0, and s^{-1}M ∖ M = s^{-1}(M ∖ M_{1/s}) has H^n-measure s^{-n}H^n(M ∖ M_{1/s}) = 0.

STEP B6 (η_{0,s#}C = C; printed last sentence). For Borel A ⊆ ℝ^N × G, by the definition of rescaledMeasure, (★), and the scaling H^n(s·E) = s^n H^n(E) (substituting z = s w):
 rescaledMeasure C 0 s (A) = s^{-n} C({(z,S) : (z/s, S) ∈ A}) = s^{-n} ∫_{{z ∈ M : (z/s, T(z)) ∈ A}} θ(z) dH^n(z) = ∫_{{w ∈ s^{-1}M : (w, T(sw)) ∈ A}} θ(sw) dH^n(w).
 By Step B5 the domain may be replaced by M_s (it differs from s^{-1}M ∩ M = M_s by an H^n-null set, and from M by an H^n-null set), and on M_s, θ(sw) = θ(w), T(sw) = T(w) (Step B4). Hence rescaledMeasure C 0 s (A) = ∫_{{w ∈ M : (w,T(w)) ∈ A}} θ dH^n = C(A). Two measures agreeing on Borel sets are equal: rescaledMeasure C 0 s = C.measure. Together with Step B2 this proves TangentConesAreRectifiableCones.

Parts A and B prove AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones.

## Key steps

1. Part A (5.5): Good points 5.6 (i)–(iv) are μ_V-a.e. (monotonicity_density's DensityExistsAE, plane_disintegration, Lebesgue differentiation for approximate continuity, 2.7).
2. Part A (5.5): 5.1 holds; varifold_tangents: tangents exist, are stationary with μ_C(B_ρ(0)) = θ0ω_nρ^n.
3. Part A (5.5): Printed (2): Θ^n(μ_C,y) ≤ μ_C(B_ρ(y))/(ω_nρ^n) ≤ θ0 by monotonicity at y and R → ∞.
4. Part A (5.5): Printed (3)–(7) (corrected '≥' in (5)): blow-up density lower bound with τ = θ0 − ε gives Θ^n(μ_C,·) ≥ θ0 a.e.; upper semicontinuity gives it on spt μ_C.
5. Part A (5.5): 3.4 at each y ∈ spt μ_C: zero defect, so x' − y ∈ S on spt C (8); spt μ_C ⊆ T with (0,T) ∈ spt C; Constancy 4.1 with M = T gives C = θ0 v(T).
6. Part A (5.5): Lemma 1.3 at x forces β(T) = ∫β dη(x) for all β: T unique; subsequence principle gives the full limit HasTangentPlane V x T θ0.
7. Part A (5.5): FirstRectifiabilityTheorem gives IsRectifiable V.
8. Part B (5.7): Blow-up density lower bound (varifold_tangents part B, τ = 1): Θ^n(μ_C,·) ≥ 1 μ_C-a.e.
9. Part B (5.7): C is stationary (hence LBFV) with μ_C(sA) = s^nμ_C(A); Part A on C gives IsRectifiable C and tangent planes μ_C-a.e.
10. Part B (5.7): FirstRectifiabilityTheorem on C: canonical representation; Ch. 1 3.3 shows μ_C = θH^n⌞M and that the planes are the weight tangent planes of μ_C.
11. Part B (5.7): Weight homogeneity makes the weight blow-ups at sy (scale sr) equal those at y (scale r): θ(sy) = θ(y), T(sy) = T(y); M is a cone up to H^n-null sets.
12. Part B (5.7): Change of variables x = sw in the representation gives rescaledMeasure C 0 s = C.measure.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4813

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
