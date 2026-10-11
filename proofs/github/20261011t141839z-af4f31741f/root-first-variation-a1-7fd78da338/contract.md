<!-- theorem-id: gmt-ch08/root.first_variation-a1 -->

## Theorem `Submission.first_variation_theorems`

For all N, n, open U ⊆ ℝ^N and n-varifolds V on U: (a) (Simon 8.2.2–8.2.4) if K ⊆ U is compact, φ : ℝ × ℝ^N → ℝ^N is C² on (−1,1) × U with φ(0,x) = x on U, each φ_t := φ(t,·) (|t| < 1) maps U injectively into U and equals the identity on U ∖ K, and X(x) is the t-derivative of φ(t,x) at t = 0 for x ∈ U, then t ↦ (V.pushforwardMeasure φ_t (K × G(N,n))).toReal = M(φ_{t#}V ⌞ Gₙ(K)) has derivative δV(X) = ∫ div_S X dV at t = 0; and div_S X(x) = Σ_i ⟨τ_i, DX(x)τ_i⟩ for every S ∈ G(N,n) and orthonormal basis τ of S. (b) (Simon 8.2.5–8.2.10) if V has locally bounded first variation, then variationMeasure V is the measure ‖δV‖ characterised by 2.5; for μ_V-a.e. x, variationDensity V x = D_{μ_V}‖δV‖(x) is finite and is the limit of ‖δV‖(B_ρ(x))/μ_V(B_ρ(x)) as ρ ↓ 0; μ_V(generalizedBoundary V) = 0; and there is a Borel ν : ℝ^N → ℝ^N with |ν| = 1 ‖δV‖-a.e. such that for every X ∈ K(U;ℝ^N): ⟨ν,X⟩ is ‖δV‖-integrable and δV(X) = −∫⟨ν,X⟩ d‖δV‖, ⟨H,X⟩ is μ_V-integrable and ⟨ν,X⟩ is σ-integrable, and δV(X) = −∫⟨H,X⟩ dμ_V − ∫⟨ν,X⟩ dσ, where H = generalizedMeanCurvature V ν and σ = generalizedBoundaryMeasure V. (Exactly FirstVariationIsMassDerivative ∧ FirstVariationRepresentation.)

Node: `root.first_variation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.first_variation_theorems`

```lean
FirstVariationIsMassDerivative ∧ FirstVariationRepresentation
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
- Child DAG node: `root.first_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, §2 (2.1–2.10), printed pp. 208–210; the computation “exactly as in §5 of Ch. 2” and the Riesz/differentiation theorems of Ch. 1 (4.14, 3.23, 3.24) that the book cites. No erratum affects 2.1–2.10. Correction relative to an earlier draft of this proof: under the hypothesis that φ is only C² one may NOT claim D_xφ_t = I + t·DX + O(t²) uniformly (a C² family can have a remainder of exact order |t|^{3/2} at a point, e.g. via g(x+t) − g(x) with g(u) = |u|^{5/2}); the argument below uses only continuity of ∂_tD_xφ, i.e. a uniform o(t) remainder, and differentiates the Jacobian on a short time interval where it is bounded away from 0. Notation: G = Grassmannian N n (orthogonal projection matrices; P_S := S.1 is the projection matrix of S ∈ G), Gₙ(A) = A × G, μ_V = V.weight, ‖δV‖ = variationMeasure V, closed balls B_ρ(x) = closedBall x ρ, K(U;ℝ^N) = Varifold.TestVectorField U.

PART (a): FirstVariationIsMassDerivative (2.2–2.4).

1. Setup (2.1). Fix N, n, U, V, φ, K, X as in the hypotheses: K ⊆ U compact, φ is C² on (−1,1) × U, φ(0,·) = id on U, for t ∈ (−1,1) the map φ_t := φ(t,·) maps U into U and is injective on U, φ_t = id on U ∖ K, and HasDerivAt (t ↦ φ(t,x)) (X x) 0 for x ∈ U. (U is open: V.isOpen_domain.) By 2.1 the image varifold is φ_{t#}V(A) = ∫_{F_t⁻¹(A)} J_Sφ_t(x) dV(x,S), F_t(x,S) = (φ_t(x), dφ_t(x)(S)), J_Sφ_t = (det((dφ_t|S)*(dφ_t|S)))^{1/2}; in the contract this is V.pushforwardMeasure (fun x ↦ φ (t, x)) = (imageMap φ_t)_#(J·V) (Varifold.pushforwardMeasure, with imageMap φ_t (x,S) = (φ_t x, transportedPlane φ_t x S)). Only the first component of imageMap φ_t enters the evaluation on the cylinder K × G below, but since the push-forward is a Measure.map, its evaluation formula requires (a.e.-)measurability of the whole map imageMap φ_t; this holds because φ_t is C¹ on U (SimonGMT Varifold.aemeasurable_imageMap / measurable_imageMap_domain, which give the evaluation formula Varifold.pushforwardMeasure_apply_of_contDiffOn).

2. φ_t(K) ⊆ K and U ∩ φ_t⁻¹(K) = K. If x ∈ U ∖ K then φ_t(x) = x ∉ K. If x ∈ K and u := φ_t(x) ∉ K, then u ∈ U ∖ K, so φ_t(u) = u = φ_t(x) and injectivity on U gives x = u ∉ K, a contradiction. Since V is carried by U × G (V.supported) and imageMap φ_t⁻¹(K × G) = φ_t⁻¹(K) × G, which agrees with K × G up to the V-null set Uᶜ × G, the evaluation formula gives (SimonGMT imageMap_preimage_cylinder_ae_of_fixed and pushforwardMeasure_cylinder_toReal_eq_integral_of_fixed) V.pushforwardMeasure φ_t (K × G) = ∫_{Gₙ(K)} J_Sφ_t(x) dV(x,S), i.e. M(φ_{t#}V ⌞ Gₙ(K)) = ∫_{Gₙ(K)} J_Sφ_t dV, a finite number because V(Gₙ(K)) < ∞ (V.finite_on_compact) and, for fixed t, (x,S) ↦ J_Sφ_t(x) is continuous, hence bounded, on the compact set K × G.

3. Regularity of the spatial derivative. Because φ is C² on the open set (−1,1) × U, the spatial derivative D(t,x) := D_xφ(t,x) (an N × N matrix) is C¹ on (−1,1) × U, and by the symmetry of second derivatives ∂_tD(t,x) = D_x(∂_tφ)(t,x). Since φ(0,·) = id on the open set U, D(0,x) = I for x ∈ U. By the velocity hypothesis ∂_tφ(0,x) = X(x) for x ∈ U, so X = ∂_tφ(0,·) is C¹ on U and ∂_tD(0,x) = DX(x) for x ∈ U.

4. The Jacobian on a short time interval (uniform o(t), no O(t²) claim). For (t,x,S) ∈ (−1,1) × U × G put g(t,x,S) := det(P_S D(t,x)ᵀD(t,x) P_S + I − P_S). With respect to the orthogonal splitting ℝ^N = S ⊕ S^⊥ this matrix is block diagonal with blocks the Gram matrix (⟨D(t,x)τ_i, D(t,x)τ_j⟩)_{i,j} (τ_1,…,τ_n an orthonormal basis of S) and the identity of S^⊥; hence g(t,x,S) = det((D(t,x)|_S)*(D(t,x)|_S)) and J_Sφ_t(x) = g(t,x,S)^{1/2}, independently of the basis. As a polynomial in the entries of D(t,x) and P_S, g is continuous on (−1,1) × U × G, C¹ in t, and ∂_tg is continuous on (−1,1) × U × G (D is C¹). Since g(0,x,S) = det I = 1 and [−1/2,1/2] × K × G is compact, uniform continuity gives t0 ∈ (0,1/2] with g ≥ 1/2 on [−t0,t0] × K × G. On this set t ↦ J_Sφ_t(x) = g^{1/2} is C¹ with ∂_tJ = ½g^{−1/2}∂_tg, which is continuous on the compact set [−t0,t0] × K × G and therefore bounded by a constant C. At t = 0, Jacobi's formula d/dt det(I + E(t))|_{t=0} = tr E'(0) for E(t) := P_S(D(t,x)ᵀD(t,x) − I)P_S (E(0) = 0 because D(0,x) = I) gives ∂_tg(0,x,S) = tr(P_S(DX(x)ᵀ + DX(x))P_S) = 2tr(P_S DX(x)) (P_S² = P_S, cyclicity of the trace), hence ∂_tJ_Sφ_t(x)|_{t=0} = tr(P_S DX(x)) = div_S X(x), which is Varifold.tangentialDivergence X x S = trace(S.1 * jacobian X x). Equivalently, J_Sφ_t(x) = 1 + t·div_S X(x) + o(t) uniformly on Gₙ(K).

5. Differentiation under the integral. For 0 < |t| ≤ t0 the mean value theorem gives |(J_Sφ_t(x) − J_Sφ_0(x))/t| ≤ C on K × G, the quotient tends to div_S X(x) as t → 0 for every (x,S) ∈ K × G (step 4), and J_Sφ_0 = 1 on K × G (D(0,·) = I). Since V(Gₙ(K)) < ∞, dominated convergence gives (1/t)(∫_{Gₙ(K)} J_Sφ_t dV − V(Gₙ(K))) → ∫_{Gₙ(K)} div_S X dV as t → 0. By step 2 the left side is the difference quotient at 0 of the real function t ↦ (V.pushforwardMeasure φ_t (K × G)).toReal (all values finite, and the value at t = 0 is V(Gₙ(K))), so this function has derivative ∫_{Gₙ(K)} div_S X dV at t = 0.

6. X vanishes with its derivative off K. On the open set U ∖ K we have φ_t = id for all t, so X = ∂_tφ(0,·) = 0 there and DX = 0 there; V vanishes off U × G (V.supported). Hence ∫_{Gₙ(K)} div_S X dV = ∫ div_S X dV = δV(X) (2.3; V.firstVariation X = ∫ tangentialDivergence X z.1 z.2 dV, the integrand being bounded on Gₙ(K) and zero V-a.e. off Gₙ(K); values of X off U are irrelevant since the derivative of X at points of the open set U only depends on X on U). This is 2.2 = 2.3: t ↦ (V.pushforwardMeasure φ_t (K ×ˢ univ)).toReal has derivative V.firstVariation X at 0.

7. 2.4. Let b be any orthonormal basis of S and extend it by an orthonormal basis (c_k) of S^⊥ to an orthonormal basis of ℝ^N. Computing the trace in this basis, Varifold.tangentialDivergence X x S = trace(P_S DX(x)) = Σ_i ⟨b_i, P_S DX(x) b_i⟩ + Σ_k ⟨c_k, P_S DX(x) c_k⟩, and the second sum vanishes because ⟨c_k, P_S w⟩ = ⟨P_S c_k, w⟩ = 0 (P_S self-adjoint, P_S c_k = 0). Moreover ⟨b_i, P_S DX(x) b_i⟩ = ⟨P_S b_i, DX(x) b_i⟩ = ⟨b_i, DX(x) b_i⟩ (P_S b_i = b_i). Hence div_S X(x) = Σ_i ⟨b_i, DX(x) b_i⟩.

8. Formal counterparts (pinned SimonGMT, kernel-checked, standard axioms only). Steps 1–6 are Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity (Poincare/SimonGMT/Chapter08/DeformationIntegral.lean:266), whose proof follows exactly this route (Varifold.hasDerivAt_integral_tangentialJacobianReal_family differentiates the Jacobian under the integral on a short time interval, and setIntegral_tangentialDivergence_initialVelocity_eq_firstVariation is step 6). Its hypotheses coincide with the contract's after (i) splitting the contract hypothesis `MapsTo … ∧ InjOn …` into its two components and (ii) passing the velocity hypothesis as `deriv (fun t ↦ φ (t, x)) 0 = X x`, which is `(h x hx).deriv` from the contract's HasDerivAt. Step 7 is Varifold.tangentialDivergence_eq_sum_inner (Chapter08/Varifold.lean:1047), whose statement is the second conjunct verbatim. This proves FirstVariationIsMassDerivative.

PART (b): FirstVariationRepresentation (2.5–2.10). Fix V with locally bounded first variation (h : V.HasLocallyBoundedFirstVariation).

9. ‖δV‖ (2.5). By the Riesz representation theorem (Ch. 1, 4.14) for the linear functional X ↦ δV(X) on K(U;ℝ^N), which satisfies |δV(X)| ≤ c_W sup|X| when spt X ⊆ W ⊂⊂ U, there is a Radon measure ‖δV‖ on U with ‖δV‖(W) = sup{|δV(X)| : |X| ≤ 1, spt X ⊆ W} for every open W ⊂⊂ U. In the contract variationMeasure V unfolds (dif_pos h) to SimonGMT's V.firstVariationRieszMeasure h, and SimonGMT's isFirstVariationMeasure_riesz (FirstVariationRiesz.lean:226) states V.IsFirstVariationMeasure (V.firstVariationRieszMeasure h): local finiteness on U, ‖δV‖(Uᶜ) = 0, and the characterization 2.5 on every open W with compact closure in U. This is the first conjunct.

10. Polar field (2.6). The same Riesz theorem gives a ‖δV‖-measurable ν with |ν| = 1 ‖δV‖-a.e. and δV(X) = −∫ ν·X d‖δV‖ for all X ∈ K(U;ℝ^N). Take ν := V.firstVariationPolarField h (FirstVariationRiesz.lean:61): it is Borel measurable (measurable_firstVariationPolarField), has ‖ν‖ = 1 ‖δV‖-a.e. (ae_firstVariationPolarField_norm_one), and isFirstVariationPolarRepresentation_riesz (FirstVariationRiesz.lean:133) gives, for every test field X, integrability of x ↦ ⟨ν x, X x⟩ w.r.t. ‖δV‖ and V.firstVariation X = −∫⟨ν, X⟩ d‖δV‖.

11. Density D_{μ_V}‖δV‖ (2.7). μ_V and ‖δV‖ are Radon measures on U; every Radon measure on an open subset of ℝ^N has the symmetric Vitali property (Besicovitch, Ch. 1 3.11(3)/3.25(1)), so by the differentiation theorem (Ch. 1, 3.23(ii)) lim_{ρ↓0} ‖δV‖(B_ρ(x))/μ_V(B_ρ(x)) exists and is finite for μ_V-a.e. x. The contract's variationDensity V x is the limsup of this ratio; where the limit exists it equals the limsup. Formally: variationDensity V unfolds to V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure h) (FirstVariationDensity.lean:50) and firstVariationRiesz_symmetricDensity_spec (FirstVariationRiesz.lean:254) gives, μ_V-a.e., both the Tendsto statement and finiteness. This is the second conjunct.

12. Generalized boundary (2.8–2.9). By the Radon–Nikodym theorem in the form of Ch. 1, 3.24(iii): ‖δV‖ = (D_{μ_V}‖δV‖) μ_V + ‖δV‖ ⌞ Z with Z = {x ∈ U : D_{μ_V}‖δV‖(x) = ∞} and μ_V(Z) = 0. The contract's generalizedBoundary V, generalizedBoundaryMeasure V and generalizedMeanCurvature V ν unfold to SimonGMT's symmetricGeneralizedBoundarySet, symmetricGeneralizedBoundaryMeasure, symmetricGeneralizedMeanCurvature (FirstVariationDecomposition.lean:93,181,188) applied to the Riesz measure (and ν). firstVariationRiesz_boundary_spec gives μ_V(Z) = 0 (third conjunct).

13. Integrability and 2.10. For each test field X: firstVariationRiesz_integrable_meanCurvature_and_boundary gives integrability of ⟨H, X⟩ w.r.t. μ_V and of ⟨ν, X⟩ w.r.t. σ = ‖δV‖⌞Z (H := generalizedMeanCurvature V ν), and firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded gives δV(X) = −∫⟨H,X⟩ dμ_V − ∫_{Z}⟨ν,X⟩ dσ; since σ is already the restriction of ‖δV‖ to Z, restricting σ again to Z does not change it (Measure.restrict_restrict / restrict_eq_self), so this is exactly the contract's identity δV(X) = −∫⟨H,X⟩ dμ_V − ∫⟨ν,X⟩ dσ. Mathematically this is 2.6 + 2.8: −∫ν·X d‖δV‖ = −∫H·X dμ_V − ∫_Z ν·X d‖δV‖, all integrals absolutely convergent because X is bounded with compact support in U and both measures are finite on compact subsets of U.

14. Conclusion. With ν = V.firstVariationPolarField h, steps 9–13 give every conjunct of FirstVariationRepresentation; with Part (a) this proves FirstVariationIsMassDerivative ∧ FirstVariationRepresentation.

## Key steps

1. (a) φ_t(K) ⊆ K and U ∩ φ_t⁻¹(K) = K by injectivity, so M(φ_{t#}V⌞Gₙ(K)) = ∫_{Gₙ(K)} J_Sφ_t dV (formula 2.1), finite since V(Gₙ(K)) < ∞.
2. C² regularity: D(t,x) = D_xφ(t,x) is C¹, D(0,·) = I and ∂_tD(0,·) = DX on U (symmetry of second derivatives, velocity hypothesis).
3. On a short interval [−t0,t0] the Gram determinant g = det(P_S DᵀD P_S + I − P_S) is ≥ 1/2 on [−t0,t0] × K × G, so J_Sφ_t = g^{1/2} is C¹ in t with bounded derivative and ∂_tJ|_{t=0} = tr(P_S DX) = div_S X (uniform o(t); no O(t²) remainder is claimed).
4. Dominated convergence on the finite measure V⌞Gₙ(K) gives d/dt|₀ ∫_{Gₙ(K)} J_Sφ_t dV = ∫_{Gₙ(K)} div_S X dV; X and DX vanish on U ∖ K, so this is δV(X) (SimonGMT hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity after splitting MapsTo ∧ InjOn and converting HasDerivAt to deriv).
5. 2.4: trace(P_S DX) = Σ⟨b_i, DX b_i⟩ for any orthonormal basis (SimonGMT tangentialDivergence_eq_sum_inner).
6. (b) variationMeasure V = firstVariationRieszMeasure (dif_pos); Riesz 4.14 gives IsFirstVariationMeasure (isFirstVariationMeasure_riesz) and the polar field ν (measurable, |ν| = 1 a.e., δV(X) = −∫ν·X d‖δV‖).
7. Differentiation theorem (Ch. 1 3.23): a.e. existence and finiteness of D_{μ_V}‖δV‖, which equals the limsup-defined variationDensity (firstVariationRiesz_symmetricDensity_spec).
8. Radon–Nikodym (Ch. 1 3.24(iii)): ‖δV‖ = D_{μ_V}‖δV‖ μ_V + ‖δV‖⌞Z, μ_V(Z) = 0; integrability and 2.10 from the SimonGMT symmetric decomposition lemmas, the extra restriction to Z being idempotent.

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
