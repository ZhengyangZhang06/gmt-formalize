import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.Submanifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Poincare.SimonGMT.Chapter01.DensityComparison
import Poincare.SimonGMT.Chapter02.AreaLiteral

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

/-- A compact exhaustion of an open `U ⊆ ℝ^N` (preamble of the proof of Simon Ch. 8, 1.2): compact
`K_p ⊆ U`, `p ∈ ℕ`, with `K_p ⊆ interior K_{p+1}`, increasing in `p`, and `⋃_p K_p = U`.  If
`U = ℝ^N` then `K_p = B_{p+1}(0)`; otherwise, with `F = ℝ^N ∖ U`,
`K_p = {x : |x| ≤ p + 1, dist(x, F) ≥ 1/(p + 1)}`. -/
theorem Submission.frt_weq_open_compact_exhaustion :
    ∀ (N : ℕ) (U : Set (Euclidean N)), IsOpen U → ∃ K : ℕ → Set (Euclidean N), (∀ p, IsCompact (K p)) ∧ (∀ p, K p ⊆ U) ∧ (∀ p, K p ⊆ interior (K (p + 1))) ∧ Monotone K ∧ ⋃ p, K p = U := by
  intro N U hU
  by_cases hUu : U = univ
  · -- Case 1: `U = ℝ^N`; take `K_p = B_{p+1}(0)`.
    subst hUu
    refine ⟨fun p : ℕ ↦ closedBall (0 : Euclidean N) ((p : ℝ) + 1),
      fun p ↦ isCompact_closedBall _ _, fun p ↦ subset_univ _, fun p ↦ ?_, fun p q hpq ↦ ?_, ?_⟩
    · -- `B_{p+1}(0) ⊆ U_{p+2}(0) = interior B_{p+2}(0)`.
      rw [interior_closedBall _ (by positivity)]
      exact closedBall_subset_ball (by push_cast; linarith)
    · -- The radii increase with `p`.
      exact closedBall_subset_closedBall (by simpa using hpq)
    · -- Every `x` lies in `B_{q+1}(0)` once `q ≥ |x|`.
      refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
      obtain ⟨q, hq⟩ := exists_nat_ge ‖x‖
      exact ⟨q, mem_closedBall_zero_iff.2 (by linarith)⟩
  · -- Case 2: `F = ℝ^N ∖ U` is closed and nonempty;
    -- take `K_p = {x : |x| ≤ p + 1, dist(x, F) ≥ 1/(p + 1)}`.
    have hF : (Uᶜ).Nonempty := nonempty_compl.2 hUu
    have hFc : IsClosed Uᶜ := hU.isClosed_compl
    let K : ℕ → Set (Euclidean N) := fun p ↦
      {x | ‖x‖ ≤ (p : ℝ) + 1 ∧ 1 / ((p : ℝ) + 1) ≤ infDist x Uᶜ}
    -- (a) `K_p` is closed and lies in the compact ball `B_{p+1}(0)`.
    have hKc : ∀ p, IsCompact (K p) := fun p ↦
      (isCompact_closedBall (0 : Euclidean N) ((p : ℝ) + 1)).of_isClosed_subset
        ((isClosed_le continuous_norm continuous_const).inter
          (isClosed_le continuous_const (continuous_infDist_pt _)))
        fun x hx ↦ mem_closedBall_zero_iff.2 hx.1
    -- (b) `K_p` misses `F`, as `dist(x, F) = 0 < 1/(p + 1)` for `x ∈ F`.
    have hKU : ∀ p, K p ⊆ U := by
      intro p x hx
      by_contra hxU
      have h0 : infDist x Uᶜ = 0 := infDist_zero_of_mem hxU
      have hpos : (0 : ℝ) < 1 / ((p : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith [hx.2]
    -- (c) The open set `O_p = {|x| < p + 2, dist(x, F) > 1/(p + 2)}` contains `K_p` and lies in
    -- `K_{p+1}`, hence in `interior K_{p+1}`.
    have hKint : ∀ p, K p ⊆ interior (K (p + 1)) := by
      intro p
      have hO : IsOpen {x : Euclidean N | ‖x‖ < (p : ℝ) + 2 ∧ 1 / ((p : ℝ) + 2) < infDist x Uᶜ} :=
        (isOpen_lt continuous_norm continuous_const).inter
          (isOpen_lt continuous_const (continuous_infDist_pt _))
      have hOK : {x : Euclidean N | ‖x‖ < (p : ℝ) + 2 ∧ 1 / ((p : ℝ) + 2) < infDist x Uᶜ} ⊆
          K (p + 1) := by
        intro x hx
        refine ⟨?_, ?_⟩
        · push_cast; linarith [hx.1]
        · push_cast
          have : (p : ℝ) + 1 + 1 = (p : ℝ) + 2 := by ring
          rw [this]; exact hx.2.le
      refine Subset.trans ?_ (interior_maximal hOK hO)
      intro x hx
      refine ⟨by linarith [hx.1], lt_of_lt_of_le ?_ hx.2⟩
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    -- (d) Monotonicity, by induction from `K_p ⊆ interior K_{p+1} ⊆ K_{p+1}`.
    have hKmono : Monotone K := monotone_nat_of_le_succ fun p ↦ (hKint p).trans interior_subset
    refine ⟨K, hKc, hKU, hKint, hKmono, ?_⟩
    -- (e) Each `x ∈ U` has `dist(x, F) > 0`, so `x ∈ K_m` with `m = max p q` for `p, q` below.
    refine Subset.antisymm (iUnion_subset hKU) fun x hx ↦ ?_
    have hδ : 0 < infDist x Uᶜ := (hFc.notMem_iff_infDist_pos hF).1 fun h ↦ h hx
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt hδ
    obtain ⟨q, hq⟩ := exists_nat_ge ‖x‖
    have hpm : (p : ℝ) ≤ (max p q : ℕ) := by exact_mod_cast le_max_left p q
    have hqm : (q : ℝ) ≤ (max p q : ℕ) := by exact_mod_cast le_max_right p q
    refine mem_iUnion.2 ⟨max p q, ?_, ?_⟩
    · linarith
    · have : 1 / (((max p q : ℕ) : ℝ) + 1) ≤ 1 / ((p : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
/-- A Borel representative of the `n`-density (Step 1 of the proof of Simon Ch. 8, 1.2): for an
s-finite `μ` on `ℝ^N`, `g(x) = liminf_k μ(B_{1/(k+1)}(x)) / (ω_n (k+1)^{-n})` is Borel and
`g(x) = Θ^n(μ, x)` at every `x` where `Θ^n(μ, x)` exists. -/
theorem Submission.frt_weq_density_borel_representative :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) [SFinite μ], ∃ g : Euclidean N → ℝ≥0∞, Measurable g ∧ ∀ (x : Euclidean N) (t : ℝ≥0∞), HasDensity n μ x t → g x = t := by
  intro N n μ _
  -- Step 1: `x ↦ μ(B_r(x))` is Borel, as `B_r(x)` is the section at `x` of the closed set
  -- `{(x, y) : dist y x ≤ r}`.
  have hball : ∀ r : ℝ, Measurable fun x : Euclidean N ↦ μ (closedBall x r) := fun r ↦
    measurable_measure_prodMk_left (ν := μ)
      (s := {p : Euclidean N × Euclidean N | dist p.2 p.1 ≤ r})
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  -- Step 2: hence so is `x ↦ densityRatio n μ x r`, a constant multiple of it.
  have hratio : ∀ r : ℝ, Measurable fun x ↦ densityRatio n μ x r := fun r ↦
    (hball r).div_const _
  -- Step 3: `g(x) = liminf_k densityRatio n μ x (1/(k+1))` is Borel.
  refine ⟨fun x ↦ liminf (fun k : ℕ ↦ densityRatio n μ x (1 / ((k : ℝ) + 1))) atTop,
    Measurable.liminf fun k ↦ hratio _, fun x t ht ↦ ?_⟩
  -- Step 4: `ρ_k = 1/(k+1) → 0⁺`, so the ratios along `ρ_k` tend to `t` and their liminf is `t`.
  have hρ : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun _ ↦ Set.mem_Ioi.2 Nat.one_div_pos_of_nat⟩
  have ht' : Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 t) := ht
  exact (ht'.comp hρ).liminf_eq
/-- Upper-density comparison with `H^n` (Simon Ch. 1, 3.3, in the form used for Ch. 8, 1.2): if `W`
is open, `A ⊆ W` and `t ≤ limsup_{ρ↓0} μ(B_ρ(x))/(ω_n ρ^n)` for every `x ∈ A`, then
`t H^n(A) ≤ μ(W)`.  Mathlib's `μHE[n]` is `c • μH[n]` for a Haar scalar `c`; the isodiametric
inequality (Simon Ch. 1, 2.10, by Steiner symmetrization) gives `c 2^n ≤ ω_n`, and Vitali's covering
lemma with Simon's finite-tail argument bounds `μH[n](A)` by the radii of disjoint good balls. -/
theorem Submission.frt_weq_mul_hausdorff_le_of_upper_density :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (t : ℝ≥0∞), IsOpen W → A ⊆ W → (∀ x ∈ A, t ≤ limsup (densityRatio n μ x) (𝓝[>] 0)) → t * μHE[n] A ≤ μ W := by
  intro N n μ W A t hW hAW hden
  -- Step 1a: two nonempty real sets at mutual distance `≤ d` have total length `≤ 2d`.
  have hcross1 : ∀ {P Q : Set ℝ}, P.Nonempty → Q.Nonempty → ∀ {d : ℝ},
      (∀ a ∈ P, ∀ b ∈ Q, dist a b ≤ d) → volume P + volume Q ≤ ENNReal.ofReal (2 * d) := by
    intro P Q hP hQ d hcross
    obtain ⟨a₀, ha₀⟩ := hP
    obtain ⟨b₀, hb₀⟩ := hQ
    have hdist (a : ℝ) (ha : a ∈ P) (b : ℝ) (hb : b ∈ Q) : a - b ≤ d ∧ b - a ≤ d :=
      abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
    have hPl : BddBelow P := ⟨b₀ - d, fun a ha => by linarith [(hdist a ha b₀ hb₀).2]⟩
    have hPu : BddAbove P := ⟨b₀ + d, fun a ha => by linarith [(hdist a ha b₀ hb₀).1]⟩
    have hQl : BddBelow Q := ⟨a₀ - d, fun b hb => by linarith [(hdist a₀ ha₀ b hb).1]⟩
    have hQu : BddAbove Q := ⟨a₀ + d, fun b hb => by linarith [(hdist a₀ ha₀ b hb).2]⟩
    have hPQ : sSup P ≤ d + sInf Q := by
      apply csSup_le ⟨a₀, ha₀⟩
      intro a ha
      have h : a - d ≤ sInf Q :=
        le_csInf ⟨b₀, hb₀⟩ fun b hb => by linarith [(hdist a ha b hb).1]
      linarith
    have hQP : sSup Q ≤ d + sInf P := by
      apply csSup_le ⟨b₀, hb₀⟩
      intro b hb
      have h : b - d ≤ sInf P :=
        le_csInf ⟨a₀, ha₀⟩ fun a ha => by linarith [(hdist a ha b hb).2]
      linarith
    have hwidthP : 0 ≤ sSup P - sInf P :=
      sub_nonneg.mpr ((csInf_le hPl ha₀).trans (le_csSup hPu ha₀))
    have hwidthQ : 0 ≤ sSup Q - sInf Q :=
      sub_nonneg.mpr ((csInf_le hQl hb₀).trans (le_csSup hQu hb₀))
    calc
      volume P + volume Q ≤ volume (Icc (sInf P) (sSup P)) + volume (Icc (sInf Q) (sSup Q)) :=
        add_le_add (measure_mono (subset_Icc_csInf_csSup hPl hPu))
          (measure_mono (subset_Icc_csInf_csSup hQl hQu))
      _ = ENNReal.ofReal ((sSup P - sInf P) + (sSup Q - sInf Q)) := by
        rw [Real.volume_Icc, Real.volume_Icc, ENNReal.ofReal_add hwidthP hwidthQ]
      _ ≤ ENNReal.ofReal (2 * d) := ENNReal.ofReal_le_ofReal (by linarith)
  -- Step 1: the isodiametric inequality `|C| ≤ ω_n (diam C / 2)^n` on `ℝ^n` (Simon Ch. 1, 2.10).
  have hiso : ∀ C : Set (EuclideanSpace ℝ (Fin n)),
      volume C ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (ediam C / 2) ^ n := by
    intro C
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hball : (ball (0 : EuclideanSpace ℝ (Fin 0)) 1) = univ := by
        ext x
        simp [Subsingleton.elim x 0]
      rw [pow_zero, mul_one, hball]
      exact measure_mono (subset_univ C)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    -- Step 1b: Steiner symmetrization in the coordinate `j`, followed by closure, keeps a compact
    -- set compact, does not increase its diameter or decrease its volume, makes it symmetric under
    -- the reflection `x_j ↦ -x_j` and keeps its symmetry under the other coordinate reflections.
    have hstep : ∀ (j : Fin (m + 1)) (K : Set (EuclideanSpace ℝ (Fin (m + 1)))), IsCompact K →
        ∃ K' : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K' ∧ ediam K' ≤ ediam K ∧
          volume K ≤ volume K' ∧
          (∀ x ∈ K', WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ K') ∧
          (∀ i, i ≠ j → (∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K) →
            ∀ x ∈ K', WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K') := by
      intro j K hK
      -- The centred interval replacing a slice, the slice through `x`, and the symmetrized set.
      set cen : Set ℝ → Set ℝ := fun T => {s | T.Nonempty ∧ |s| ≤ (volume T).toReal / 2}
        with hcen
      set sl : EuclideanSpace ℝ (Fin (m + 1)) → Set ℝ :=
        fun x => {t | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ K} with hsl
      set S : Set (EuclideanSpace ℝ (Fin (m + 1))) := {x | x j ∈ cen (sl x)} with hS
      have hrefl_cont : ∀ i : Fin (m + 1), Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
          WithLp.toLp 2 (Function.update x.ofLp i (-x i)) := by
        intro i
        apply (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp
        apply continuous_pi
        intro k
        by_cases hki : k = i
        · subst k
          simpa only [Function.update_self] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => -x i) by fun_prop)
        · simpa only [Function.update_of_ne hki] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x k) by fun_prop)
      -- The diameter does not increase.
      have hdiamS : ediam S ≤ ediam K := by
        by_cases hfin : ediam K = ∞
        · rw [hfin]
          exact le_top
        have hbounded : Bornology.IsBounded K := isBounded_iff_ediam_ne_top.mpr hfin
        have hdiam : ediam S ≤ ENNReal.ofReal (diam K) := by
          apply ediam_le_of_forall_dist_le
          intro x hx y hy
          have hx' : x j ∈ cen (sl x) := hx
          have hy' : y j ∈ cen (sl y) := hy
          let D : ℝ := diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2
          have hupd : ∀ a b : ℝ,
              dist (WithLp.toLp 2 (Function.update x.ofLp j a) : EuclideanSpace ℝ (Fin (m + 1)))
                (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
                dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
            intro a b
            rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
            have hsum := Finset.sum_erase_add Finset.univ
              (fun i : Fin (m + 1) => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
            have hsum' := Finset.sum_erase_add Finset.univ
              (fun i : Fin (m + 1) => dist (Function.update x.ofLp j a i)
                (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
            have hrest : (∑ i ∈ Finset.univ.erase j,
                dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
                ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
            rw [hrest, Function.update_self, Function.update_self] at hsum'
            simp only
            linarith
          have hsq (a : ℝ) (ha : a ∈ sl x) (b : ℝ) (hb : b ∈ sl y) :
              dist a b ^ 2 ≤ D := by
            have hsq' := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hbounded ha hb) 2
            rw [hupd] at hsq'
            dsimp [D]
            linarith
          have hD : 0 ≤ D := by
            obtain ⟨a, ha⟩ := hx'.1
            obtain ⟨b, hb⟩ := hy'.1
            exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
          have hsqrt := Real.sq_sqrt hD
          have hcross : ∀ a ∈ sl x, ∀ b ∈ sl y, dist a b ≤ Real.sqrt D := by
            intro a ha b hb
            have h := hsq a ha b hb
            nlinarith [dist_nonneg (x := a) (y := b), Real.sqrt_nonneg D]
          have hsum := hcross1 hx'.1 hy'.1 hcross
          have hfin' : volume (sl x) + volume (sl y) ≠ ∞ :=
            ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
          have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
          rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp hfin').1 (ENNReal.add_ne_top.mp hfin').2,
            ENNReal.toReal_ofReal (by positivity)] at hreal
          have hcentered : dist (x j) (y j) ≤ Real.sqrt D := by
            calc
              dist (x j) (y j) = |x j - y j| := Real.dist_eq _ _
              _ ≤ |x j| + |y j| := abs_sub _ _
              _ ≤ (volume (sl x)).toReal / 2 + (volume (sl y)).toReal / 2 :=
                add_le_add hx'.2 hy'.2
              _ ≤ Real.sqrt D := by linarith
          have hcentered_sq : dist (x j) (y j) ^ 2 ≤ D := by
            nlinarith [dist_nonneg (x := x j) (y := y j), Real.sqrt_nonneg D]
          dsimp [D] at hcentered_sq
          nlinarith [dist_nonneg (x := x) (y := y), diam_nonneg (s := K)]
        simpa only [diam, ENNReal.ofReal_toReal hfin] using hdiam
      -- The volume does not decrease (Fubini along the `j`-th coordinate).
      have hvolS : volume K ≤ volume S := by
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
        let φ : ℝ × (Fin m → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) :=
          fun p => WithLp.toLp 2 (e.symm p)
        have hφ : MeasurePreserving φ volume volume :=
          (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
            (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
        have hφcoord (t : ℝ) (z : Fin m → ℝ) : φ (t, z) j = t :=
          Fin.insertNth_apply_same (α := fun _ : Fin (m + 1) => ℝ) j t z
        let T := toMeasurable volume S
        have hT : MeasurableSet T := measurableSet_toMeasurable volume S
        have hTS : S ⊆ T := subset_toMeasurable volume S
        have hslice (t : ℝ) (z : Fin m → ℝ) : sl (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' K := by
          ext s
          change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ K) ↔
            WithLp.toLp 2 (j.insertNth s z) ∈ K
          rw [Fin.update_insertNth]
        have hfinite (z : Fin m → ℝ) : volume ((fun t => φ (t, z)) ⁻¹' K) ≠ ∞ := by
          have hproj : IsCompact ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x j) '' K) :=
            hK.image (by fun_prop)
          have hsub : (fun t => φ (t, z)) ⁻¹' K ⊆
              (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x j) '' K :=
            fun t ht => ⟨φ (t, z), ht, hφcoord t z⟩
          exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
        have hcenvol : ∀ U : Set ℝ, volume U ≠ ∞ → volume (cen U) = volume U := by
          intro U hfin
          rcases U.eq_empty_or_nonempty with rfl | hU
          · simp [hcen]
          · have hinterval : cen U = Icc (-(volume U).toReal / 2) ((volume U).toReal / 2) := by
              ext x
              simp [hcen, hU, abs_le, neg_div]
            rw [hinterval, Real.volume_Icc]
            convert ENNReal.ofReal_toReal hfin using 1
            congr 1
            ring
        calc
          volume K = volume (φ ⁻¹' K) :=
            (hφ.measure_preimage hK.measurableSet.nullMeasurableSet).symm
          _ = ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' K) :=
            Measure.prod_apply_symm (hK.measurableSet.preimage hφ.measurable)
          _ = ∫⁻ z : Fin m → ℝ, volume (cen ((fun t => φ (t, z)) ⁻¹' K)) :=
            lintegral_congr fun z => (hcenvol _ (hfinite z)).symm
          _ ≤ ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
            apply lintegral_mono
            intro z
            apply measure_mono
            intro t ht
            apply hTS
            change φ (t, z) j ∈ cen (sl (φ (t, z)))
            rw [hφcoord, hslice]
            exact ht
          _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
          _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
          _ = volume S := measure_toMeasurable S
      -- Symmetry under the reflection in the `j`-th coordinate.
      have hsymS : ∀ x ∈ S, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ S := by
        intro x hx
        have hx' : x j ∈ cen (sl x) := hx
        show (WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :
            EuclideanSpace ℝ (Fin (m + 1))) j ∈
          cen (sl (WithLp.toLp 2 (Function.update x.ofLp j (-x j))))
        have hsl : sl (WithLp.toLp 2 (Function.update x.ofLp j (-x j))) = sl x := by
          ext t
          simp only [hsl, mem_ofPred_eq, Function.update_idem]
        rw [hsl]
        simp only [Function.update_self]
        exact ⟨hx'.1, by simpa only [abs_neg] using hx'.2⟩
      -- Symmetry under the reflection in another coordinate `i ≠ j` is preserved.
      have hpresS : ∀ i, i ≠ j →
          (∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K) →
          ∀ x ∈ S, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ S := by
        intro i hij hKi x hx
        have hx' : x j ∈ cen (sl x) := hx
        show (WithLp.toLp 2 (Function.update x.ofLp i (-x i)) :
            EuclideanSpace ℝ (Fin (m + 1))) j ∈
          cen (sl (WithLp.toLp 2 (Function.update x.ofLp i (-x i))))
        have hcomm : ∀ t : ℝ,
            (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x.ofLp i (-x i)) :
                EuclideanSpace ℝ (Fin (m + 1))).ofLp j t) : EuclideanSpace ℝ (Fin (m + 1))) =
            WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x.ofLp j t) : EuclideanSpace ℝ (Fin (m + 1))).ofLp i
              (-(WithLp.toLp 2 (Function.update x.ofLp j t) :
                EuclideanSpace ℝ (Fin (m + 1))) i)) := by
          intro t
          ext k
          by_cases hki : k = i
          · subst k
            simp [hij]
          · by_cases hkj : k = j
            · subst k
              simp [Function.update_apply, hki]
            · simp [Function.update_apply, hki, hkj]
        have hsl : sl (WithLp.toLp 2 (Function.update x.ofLp i (-x i))) = sl x := by
          ext t
          simp only [hsl, mem_ofPred_eq]
          rw [hcomm t]
          constructor
          · intro h
            convert hKi _ h using 1
            ext k
            by_cases hki : k = i
            · subst k
              simp [hij]
            · simp [Function.update_apply, hki]
          · exact hKi _
        rw [hsl]
        simpa only [WithLp.ofLp_toLp, Function.update_of_ne (Ne.symm hij)] using hx'
      refine ⟨closure S, ?_, ?_, ?_, ?_, ?_⟩
      · apply Bornology.IsBounded.isCompact_closure
        apply isBounded_iff_ediam_ne_top.mpr
        exact ne_top_of_le_ne_top hK.isBounded.ediam_ne_top hdiamS
      · rw [ediam_closure]
        exact hdiamS
      · exact hvolS.trans (measure_mono subset_closure)
      · intro x hx
        have hsub : S ⊆ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
            WithLp.toLp 2 (Function.update x.ofLp j (-x j))) ⁻¹' closure S :=
          fun y hy => subset_closure (hsymS y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (hrefl_cont j)) hx
      · intro i hij hKi x hx
        have hsub : S ⊆ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
            WithLp.toLp 2 (Function.update x.ofLp i (-x i))) ⁻¹' closure S :=
          fun y hy => subset_closure (hpresS i hij hKi y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (hrefl_cont i)) hx
    by_cases hfin : ediam C = ∞
    · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        ENNReal.top_pow (Nat.succ_ne_zero m),
        ENNReal.mul_top (measure_ball_pos volume _ one_pos).ne']
      exact le_top
    have hbounded : Bornology.IsBounded C := isBounded_iff_ediam_ne_top.mpr hfin
    -- Step 1c: symmetrizing `closure C` in every coordinate gives a compact `K` with
    -- `diam K ≤ diam C`, `|C| ≤ |K|`, symmetric under every coordinate reflection.
    have hiter : ∀ s : Finset (Fin (m + 1)), ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))),
        IsCompact K ∧ ediam K ≤ ediam C ∧ volume C ≤ volume K ∧
        ∀ i ∈ s, ∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨closure C, hbounded.isCompact_closure, (ediam_closure C).le,
          measure_mono subset_closure, by simp⟩
      | @insert i s hi ih =>
        obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
        obtain ⟨K', hK', hdiam', hvol', hsym', hpres'⟩ := hstep i K hK
        refine ⟨K', hK', hdiam'.trans hdiam, hvol.trans hvol', ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hsym'
        · exact hpres' k (fun h => hi (h ▸ hk)) (hsym k hk)
    obtain ⟨K, hK, hdiam, hvol, hsym⟩ := hiter Finset.univ
    -- Step 1d: `K` is centrally symmetric, hence `K ⊆ B_{diam K / 2}(0)`.
    have hneg : ∀ x ∈ K, -x ∈ K := by
      intro x hx
      have hmem (s : Finset (Fin (m + 1))) :
          WithLp.toLp 2 (fun k => if k ∈ s then -x k else x k) ∈ K := by
        induction s using Finset.induction_on with
        | empty => simpa using hx
        | @insert i s hi ih =>
          convert hsym i (Finset.mem_univ i) _ ih using 1
          ext k
          by_cases hki : k = i
          · subst k
            simp [hi]
          · simp [hki]
      have heq : (WithLp.toLp 2 fun k => -x k) = -x := by
        ext k
        rfl
      simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
    have hKb : Bornology.IsBounded K := hK.isBounded
    have hsub : K ⊆ closedBall 0 (diam K / 2) := by
      intro x hx
      have hdist := dist_le_diam_of_mem hKb hx (hneg x hx)
      rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
      norm_num at hdist
      rw [mem_closedBall, dist_zero_right]
      linarith
    calc volume C ≤ volume K := hvol
      _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) (diam K / 2)) :=
          measure_mono hsub
      _ = ENNReal.ofReal ((diam K / 2) ^ (m + 1)) *
            volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
          rw [Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin]
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) * (ediam K / 2) ^ (m + 1) := by
          rw [mul_comm, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by norm_num),
            ENNReal.ofReal_ofNat, diam, ENNReal.ofReal_toReal hKb.ediam_ne_top]
      _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) * (ediam C / 2) ^ (m + 1) := by
          gcongr
  -- Step 2: the Haar scalar `c` with `μHE[n] = c • μH[n]` satisfies `c 2^n ≤ ω_n`: by Step 1,
  -- `volume ≤ (ω_n / 2^n) • μH[n]` on `ℝ^n`, and `volume = c • μH[n]`; compare on the unit ball.
  have hnorm : ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
      ℝ≥0∞) * 2 ^ n ≤ unitBallVolume n := by
    have hω0 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      (measure_ball_pos volume _ one_pos).ne'
    have hωtop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ∞ := measure_ball_lt_top.ne
    have h2n0 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2ntop : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] •
          μH[(n:ℝ)] :=
      Measure.isAddLeftInvariant_eq_smul _ _
    have h1 : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
        Measure.mkMetric ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
          fun r : ℝ≥0∞ => r ^ (n:ℝ)) := by
      apply Measure.le_mkMetric _ _ 1 one_pos
      intro s _
      calc volume s ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (ediam s / 2) ^ n :=
            hiso s
        _ = ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
              fun r : ℝ≥0∞ => r ^ (n:ℝ)) (ediam s) := by
          simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast, div_eq_mul_inv, mul_pow,
            ENNReal.inv_pow]
          ring
    have h2 : (Measure.mkMetric ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
          fun r : ℝ≥0∞ => r ^ (n:ℝ)) : Measure (EuclideanSpace ℝ (Fin n))) ≤
        (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) • μH[(n:ℝ)] :=
      Measure.mkMetric_mono_smul (ENNReal.div_ne_top hωtop h2n0)
        (ENNReal.div_pos hω0 h2ntop).ne' (Eventually.of_forall fun _ => le_rfl)
    have hB : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n *
          μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      simpa only [Measure.smul_apply, smul_eq_mul] using
        (h1.trans h2) (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    have hcB : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
          ℝ≥0∞) * μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using
        congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin n)) => ν (ball 0 1)) hvol
    have h2le : (2 : ℝ≥0∞) ^ n ≤ μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      have hmul : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n ≤
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        calc volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n
            ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n *
                μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n := by gcongr
          _ = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
                μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
            rw [mul_right_comm, ENNReal.div_mul_cancel h2n0 h2ntop]
      exact (ENNReal.mul_le_mul_iff_right hω0 hωtop).mp hmul
    calc ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
          ℝ≥0∞) * 2 ^ n
        ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
            ℝ≥0∞) * μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by gcongr
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcB.symm
  -- Step 3: the covering argument (Simon's proof of 3.3).  If every `x ∈ A` is the centre of
  -- arbitrarily small balls `B` with `τ ω_n r^n ≤ μ(B)`, then `τ c μH[n](A) ≤ μ(W)`.
  have hcov : ∀ τ c : ℝ≥0∞, c * 2 ^ n ≤ unitBallVolume n → τ ≠ 0 → μ W ≠ ∞ →
      (∀ x ∈ A, ∀ ε > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < ε ∧
        τ * (unitBallVolume n * ENNReal.ofReal r ^ n) ≤ μ (closedBall x r)) →
      τ * (c * μH[(n:ℝ)] A) ≤ μ W := by
    intro τ c hc hτ0 hμW hball
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
    have hH : μH[(n:ℝ)] A = ⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ),
        OuterMeasure.mkMetric'.pre (fun s : Set (Euclidean N) => ediam s ^ (n:ℝ)) δ A := by
      rw [← Measure.toOuterMeasure_apply, Measure.hausdorffMeasure,
        Measure.mkMetric_toOuterMeasure, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
        OuterMeasure.iSup_apply]
      simp only [OuterMeasure.iSup_apply]
    rw [hH, ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun δ => ?_
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun hδ => ?_
    obtain ⟨R₀, -, hR₀, hR₀δ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
    have hR : 0 < R₀ / 6 := by
      have := ENNReal.ofReal_pos.mp hR₀
      positivity
    set R := R₀ / 6 with hRdef
    -- Step 3a: the fine family `G` of good balls of radius `≤ R` inside `W`.
    set G : Set (Euclidean N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ R ∧
        closedBall p.1 p.2 ⊆ W ∧ τ * (unitBallVolume n * ENNReal.ofReal p.2 ^ n) ≤
          μ (closedBall p.1 p.2)} with hG
    have hfine : ∀ x ∈ A, ∀ ε > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < ε ∧ (x, r) ∈ G := by
      intro x hx ε hε
      obtain ⟨ε', hε', hε'W⟩ := Metric.isOpen_iff.mp hW x (hAW hx)
      obtain ⟨r, hr0, hrlt, hr⟩ := hball x hx (min ε (min R (ε' / 2))) (by positivity)
      have h1 : r < ε := hrlt.trans_le (min_le_left _ _)
      have h2 : r < R := hrlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h3 : r < ε' / 2 := hrlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      refine ⟨r, hr0, h1, hx, hr0, h2.le, ?_, hr⟩
      exact (closedBall_subset_ball (h3.trans (half_lt_self hε'))).trans hε'W
    -- Step 3b: Vitali's lemma gives a countable disjoint subfamily `u` such that every ball of
    -- `G` meets a ball of `u` of at least half its radius.
    obtain ⟨u, huG, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun p : Euclidean N × ℝ => closedBall p.1 p.2) G (fun p => p.2) 2 one_lt_two
      (fun p hp => hp.2.1.le) R (fun p hp => hp.2.2.1)
      (fun p hp => nonempty_closedBall.mpr hp.2.1.le)
    have hucount : u.Countable := by
      refine Set.PairwiseDisjoint.countable_of_nonempty_interior (α := Euclidean N) hudisj ?_
      intro p hp
      exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huG hp).2.1)⟩
    have : Countable u := hucount.to_subtype
    set w : u → ℝ≥0∞ := fun p => ENNReal.ofReal p.1.2 ^ n with hw
    have hsum : τ * unitBallVolume n * ∑' p, w p ≤ μ W := by
      calc τ * unitBallVolume n * ∑' p, w p = ∑' p : u, τ * (unitBallVolume n * w p) := by
            rw [← ENNReal.tsum_mul_left]
            congr 1
            funext p
            ring
        _ ≤ ∑' p : u, μ (closedBall p.1.1 p.1.2) :=
            ENNReal.tsum_le_tsum fun p => (huG p.2).2.2.2.2
        _ = μ (⋃ p : u, closedBall p.1.1 p.1.2) :=
            (measure_iUnion (fun (p q : u) hpq => hudisj p.2 q.2 (Subtype.coe_ne_coe.mpr hpq))
              fun (p : u) => measurableSet_closedBall).symm
        _ ≤ μ W := measure_mono (iUnion_subset fun p => (huG p.2).2.2.2.1)
    have hSfin : ∑' p, w p ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.mul_top (mul_ne_zero hτ0 hω0)] at hsum
      exact hμW (top_le_iff.mp hsum)
    -- Step 3c: for every finite `F ⊆ u`, the balls of `F` and the tripled balls of `u ∖ F`
    -- cover `A`.
    have hrem : ∀ F : Finset u, A ⊆ (⋃ p ∈ F, closedBall p.1.1 p.1.2) ∪
        ⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2) := by
      intro F x hx
      by_cases hxF : x ∈ ⋃ p ∈ F, closedBall p.1.1 p.1.2
      · exact Or.inl hxF
      right
      have hclosed : IsClosed (⋃ p ∈ F, closedBall p.1.1 p.1.2) :=
        isClosed_biUnion_finset fun p _ => isClosed_closedBall
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hxF
      obtain ⟨r, hr0, hrε, hrG⟩ := hfine x hx (ε / 2) (half_pos hε)
      obtain ⟨b, hbu, ⟨z, hz1, hz2⟩, hrb⟩ := hucov (x, r) hrG
      simp only [mem_closedBall] at hz1 hz2 hrb
      have hbF : (⟨b, hbu⟩ : u) ∉ F := by
        intro hbF
        have hzF : z ∈ ⋃ p ∈ F, closedBall p.1.1 p.1.2 :=
          mem_iUnion₂.mpr ⟨⟨b, hbu⟩, hbF, mem_closedBall.mpr hz2⟩
        have hzball : z ∈ ball x ε := by
          rw [mem_ball]
          linarith
        exact hεsub hzball hzF
      refine mem_iUnion.mpr ⟨⟨⟨b, hbu⟩, hbF⟩, ?_⟩
      rw [mem_closedBall]
      have := dist_triangle x z b.1
      rw [dist_comm] at hz1
      simp only
      linarith
    -- Step 3d: estimate the size-`δ` approximation of `μH[n]` and let `F` exhaust `u`.
    set pre := OuterMeasure.mkMetric'.pre (fun s : Set (Euclidean N) => ediam s ^ (n:ℝ)) δ
      with hpre
    have hpreball : ∀ (x : Euclidean N) (r : ℝ), 0 ≤ r → r ≤ 3 * R →
        pre (closedBall x r) ≤ ENNReal.ofReal (2 * r) ^ n := by
      intro x r hr hrR
      have hd : ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
        ediam_le_of_forall_dist_le fun y hy z hz => by
          have := dist_triangle_right y z x
          rw [mem_closedBall] at hy hz
          linarith
      have hδ' : ENNReal.ofReal (2 * r) ≤ δ :=
        (ENNReal.ofReal_le_ofReal (by rw [hRdef] at hrR; linarith)).trans hR₀δ.le
      refine (OuterMeasure.mkMetric'.pre_le (hd.trans hδ')).trans ?_
      rw [ENNReal.rpow_natCast]
      exact pow_le_pow_left' hd n
    have hbound : ∀ F : Finset u,
        pre A ≤ 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p := by
      intro F
      have hsmall : ∀ p : u, pre (closedBall p.1.1 p.1.2) ≤ 2 ^ n * w p := by
        intro p
        have hp := huG p.2
        refine (hpreball _ _ hp.2.1.le (by linarith [hp.2.2.1])).trans_eq ?_
        rw [ENNReal.ofReal_mul (by norm_num), mul_pow, ENNReal.ofReal_ofNat]
      have hlarge : ∀ p : {p : u // p ∉ F},
          pre (closedBall p.1.1.1 (3 * p.1.1.2)) ≤ 6 ^ n * w p.1 := by
        intro p
        have hp := huG p.1.2
        refine (hpreball _ _ (by linarith [hp.2.1]) (by linarith [hp.2.2.1])).trans_eq ?_
        rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num), mul_pow]
        norm_num
        rfl
      calc pre A ≤ pre ((⋃ p ∈ F, closedBall p.1.1 p.1.2) ∪
            ⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2)) := measure_mono (hrem F)
        _ ≤ pre (⋃ p ∈ F, closedBall p.1.1 p.1.2) +
            pre (⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2)) :=
            measure_union_le _ _
        _ ≤ (∑ p ∈ F, 2 ^ n * w p) + ∑' p : {p : u // p ∉ F}, 6 ^ n * w p.1 := by
            gcongr
            · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun p _ => hsmall p)
            · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun p => hlarge p)
        _ ≤ 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p := by
            rw [← Finset.mul_sum, ENNReal.tsum_mul_left]
            gcongr
            exact ENNReal.sum_le_tsum F
    have hlim : Tendsto
        (fun F : Finset u => 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p)
        atTop (𝓝 (2 ^ n * ∑' p, w p)) := by
      have h0 := ENNReal.tendsto_tsum_compl_atTop_zero hSfin
      have h6 : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      simpa using (tendsto_const_nhds (x := (2 : ℝ≥0∞) ^ n * ∑' p, w p)).add
        (ENNReal.Tendsto.const_mul (a := (6 : ℝ≥0∞) ^ n) h0 (Or.inr h6))
    have hpreA : pre A ≤ 2 ^ n * ∑' p, w p := ge_of_tendsto' hlim hbound
    calc τ * (c * pre A) ≤ τ * (c * (2 ^ n * ∑' p, w p)) := by gcongr
      _ = τ * (c * 2 ^ n) * ∑' p, w p := by ring
      _ ≤ τ * unitBallVolume n * ∑' p, w p := by gcongr
      _ ≤ μ W := hsum
  -- Step 4: for `0 < τ < t` the density hypothesis yields the good balls of Step 3; take the
  -- supremum over `τ`.
  by_cases hμW : μ W = ∞
  · rw [hμW]
    exact le_top
  have hHE : μHE[n] A = ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor
      μH[(n:ℝ)] : ℝ≥0∞) * μH[(n:ℝ)] A := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hHE]
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  rw [ENNReal.iSup_mul]
  refine iSup_le fun τ => ?_
  rw [ENNReal.iSup_mul]
  refine iSup_le fun hτ => ?_
  rcases eq_or_ne τ 0 with rfl | hτ0
  · simp
  refine hcov τ _ hnorm hτ0 hμW fun x hx ε hε => ?_
  have hlt : τ < limsup (densityRatio n μ x) (𝓝[>] 0) := hτ.trans_le (hden x hx)
  obtain ⟨r, hqr, hr⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hlt).and_eventually
    (Ioo_mem_nhdsGT hε)).exists
  refine ⟨r, hr.1, hr.2, ?_⟩
  have hne0 : unitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
    mul_ne_zero (measure_ball_pos volume _ one_pos).ne'
      (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr.1).ne')
  have hnetop : unitBallVolume n * ENNReal.ofReal r ^ n ≠ ∞ :=
    ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).mp hqr).le
/-- Lebesgue density for an arbitrary subset `A` of an open set `W` with `μ(W) < ∞` (statement (β)
of Step 8 in the proof of Simon Ch. 8, 1.2): the set of `x ∈ A` at which
`μ(A ∩ B_r(x))/μ(B_r(x))` does not tend to `1` as `r ↓ 0` is `μ`-null.  Apply
`Besicovitch.ae_tendsto_measure_inter_div` to the finite measure `ν = μ ⌞ W`; a measurable hull
`T` of its failure set has `μ(T ∩ A ∩ W) = (ν ⌞ A)(T) = 0`, and at `x ∈ A ∖ T` small balls lie in
`W`, so the `μ`- and `ν`-ratios agree near `0⁺`.  No measurability of `A` is used. -/
theorem Submission.frt_weq_nondensity_points_null :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)), IsOpen W → μ W ≠ ∞ → A ⊆ W → μ {x | x ∈ A ∧ ¬ Tendsto (fun r : ℝ => μ (A ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)} = 0 := by
  intro N μ W A hW hμW hAW
  -- Step 1: `ν = μ ⌞ W` is a finite measure.
  let ν : Measure (Euclidean N) := μ.restrict W
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμW
  -- Step 2: the failure set `S` of the Besicovitch density theorem for `ν` and `A` is
  -- `(ν ⌞ A)`-null, and so is its measurable hull `T`.
  let S : Set (Euclidean N) :=
    {x | ¬ Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ν (closedBall x r)) (𝓝[>] 0) (𝓝 1)}
  have hS : ν.restrict A S = 0 := ae_iff.1 (Besicovitch.ae_tendsto_measure_inter_div ν A)
  let T : Set (Euclidean N) := toMeasurable (ν.restrict A) S
  have hT : ν.restrict A T = 0 := (measure_toMeasurable S).trans hS
  -- Step 3: `μ(T ∩ A ∩ W) = (ν ⌞ A)(T) = 0`.
  have hTAW : μ (T ∩ A ∩ W) = 0 := by
    rw [← Measure.restrict_apply' hW.measurableSet, ← Measure.restrict_apply
      (measurableSet_toMeasurable _ _)]
    exact hT
  -- Steps 4–5: every non-density point of `A` lies in `T ∩ A ∩ W`.
  refine measure_mono_null ?_ hTAW
  rintro x ⟨hxA, hxE⟩
  refine ⟨⟨?_, hxA⟩, hAW hxA⟩
  by_contra hxT
  have hx : Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ν (closedBall x r)) (𝓝[>] 0) (𝓝 1) :=
    not_not.1 fun hxS ↦ hxT (subset_toMeasurable (ν.restrict A) S hxS)
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 hW x (hAW hxA)
  refine hxE (hx.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hrW : closedBall x r ⊆ W := (closedBall_subset_ball hr.2).trans hδW
  simp only [ν, Measure.restrict_apply' hW.measurableSet, inter_eq_left.2 hrW,
    inter_eq_left.2 (inter_subset_right.trans hrW)]

/-- Steps 6–8 of the proof of Simon Ch. 8, 1.2, on one piece `A ⊆ W` (`W` open, `μ(W) < ∞`,
`H^n(A) < ∞`): if `μ` has density `θ(x) > 0` at every `x ∈ A`, `μ` and `H^n` have the same null
subsets of `A`, and `H^n ⌞ A` has density one `H^n ⌞ A`-a.e., then `μ ⌞ A = (H^n ⌞ A) ⌞ θ`, i.e.
`μ(B ∩ A) = ∫_{B ∩ A} θ dH^n` for every Borel `B` (Besicovitch differentiation and
Radon–Nikodym). -/
theorem Submission.frt_weq_piece_restrict_eq_density :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsOpen W → μ W ≠ ∞ → A ⊆ W → μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → (∀ x ∈ A, 0 < θ x ∧ HasDensity n μ x (ENNReal.ofReal (θ x))) → (∀ Z ⊆ A, μHE[n] Z = 0 → μ Z = 0) → (∀ Z ⊆ A, μ Z = 0 → μHE[n] Z = 0) → (∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)).restrict A, HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict A) x 1) → ∀ B : Set (Euclidean N), MeasurableSet B → μ (B ∩ A) = ∫⁻ x in B ∩ A, ENNReal.ofReal (θ x) ∂μHE[n] := by
  intro N n μ W A θ hW hμW hAW hHA hAnm hθ hnullμ hnullH hdens B hB
  -- Notation: `H = H^n`, `ρ = μ ⌞ A`, `ν = H^n ⌞ A`, `c(r) = ω_n r^n`.
  set H : Measure (Euclidean N) := μHE[n]
  set ρ : Measure (Euclidean N) := μ.restrict A with hρ
  set ν : Measure (Euclidean N) := H.restrict A with hν
  let c : ℝ → ℝ≥0∞ := fun r ↦ unitBallVolume n * ENNReal.ofReal r ^ n
  -- Step 1: `0 < ω_n < ∞`, so `c(r) ∉ {0, ∞}` for `r > 0`.
  have hc0 : ∀ r : ℝ, 0 < r → c r ≠ 0 := fun r hr ↦
    mul_ne_zero (measure_ball_pos volume _ one_pos).ne'
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
  have hctop : ∀ r : ℝ, c r ≠ ∞ := fun r ↦
    ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- Step 2: `ρ` and `ν` are finite measures.
  have : IsFiniteMeasure ρ :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hμW (measure_mono hAW))
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hHA
  -- Step 3: `ρ ≪ ν`, by (ii).
  have hac : ρ ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ by
    rw [hν, Measure.restrict_apply hs] at hs0
    rw [hρ, Measure.restrict_apply hs]
    exact hnullμ _ inter_subset_right hs0
  -- Step 4: the non-density points `E` of `A` are `μ`-null, hence `H`-null by (iii) and `ν`-null.
  set E : Set (Euclidean N) := {x | x ∈ A ∧ ¬ Tendsto (fun r : ℝ ↦ μ (A ∩ closedBall x r) /
    μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)}
  have hEν : ν E = 0 := nonpos_iff_eq_zero.1 <| (Measure.restrict_apply_le A E).trans_eq <|
    hnullH E (fun x hx ↦ hx.1) (Submission.frt_weq_nondensity_points_null N μ W A hW hμW hAW)
  -- Steps 5–7: `ν`-a.e., `ρ(B_r(x))/ν(B_r(x)) → θ(x)`, so `dρ/dν = θ` `ν`-a.e. (Besicovitch).
  have hderiv : ρ.rnDeriv ν =ᵐ[ν] fun x ↦ ENNReal.ofReal (θ x) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hEν, ae_restrict_mem₀ hAnm, hdens,
      Besicovitch.ae_tendsto_rnDeriv ρ ν] with x hxE hxA hxα hxD
    -- (α) `ν(B_r(x))/c(r) → 1`, (β) `μ(A ∩ B_r(x))/μ(B_r(x)) → 1`, (γ) `μ(B_r(x))/c(r) → θ(x)`.
    have hα : Tendsto (fun r ↦ ν (closedBall x r) / c r) (𝓝[>] 0) (𝓝 1) := hxα
    have hβ : Tendsto (fun r : ℝ ↦ μ (A ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) := by
      by_contra h
      exact hxE ⟨hxA, h⟩
    have hγ : Tendsto (fun r ↦ μ (closedBall x r) / c r) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (θ x))) := (hθ x hxA).2
    have hL0 : ENNReal.ofReal (θ x) ≠ 0 := (ENNReal.ofReal_pos.2 (hθ x hxA).1).ne'
    -- (c) the product of the three ratios tends to `1 · θ(x) / 1`.
    have hlim : Tendsto (fun r ↦ μ (A ∩ closedBall x r) / μ (closedBall x r) *
        (μ (closedBall x r) / c r) / (ν (closedBall x r) / c r)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (θ x))) := by
      simpa using ENNReal.Tendsto.div (ENNReal.Tendsto.mul hβ (Or.inl one_ne_zero) hγ
        (Or.inr ENNReal.one_ne_top)) (Or.inr one_ne_zero) hα (Or.inl ENNReal.one_ne_top)
    -- (a), (b), (d): eventually that product is `ρ(B_r(x))/ν(B_r(x))`.
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (A ∩ closedBall x r) / μ (closedBall x r) *
        (μ (closedBall x r) / c r) / (ν (closedBall x r) / c r) =
          ρ (closedBall x r) / ν (closedBall x r) := by
      filter_upwards [self_mem_nhdsWithin, hγ.eventually_ne hL0,
        hγ.eventually_ne ENNReal.ofReal_ne_top, hα.eventually_ne one_ne_zero,
        hα.eventually_ne ENNReal.one_ne_top] with r hr hb0 hbtop hd0 hdtop
      have hb0' : μ (closedBall x r) ≠ 0 := fun h ↦ hb0 (by rw [h, ENNReal.zero_div])
      have hbtop' : μ (closedBall x r) ≠ ∞ := fun h ↦
        hbtop (by rw [h, ENNReal.top_div_of_ne_top (hctop r)])
      have hd0' : ν (closedBall x r) ≠ 0 := fun h ↦ hd0 (by rw [h, ENNReal.zero_div])
      have hdtop' : ν (closedBall x r) ≠ ∞ := fun h ↦
        hdtop (by rw [h, ENNReal.top_div_of_ne_top (hctop r)])
      have hρr : ρ (closedBall x r) = μ (A ∩ closedBall x r) := by
        rw [hρ, Measure.restrict_apply (μ := μ) isClosed_closedBall.measurableSet,
          inter_comm (closedBall x r) A]
      rw [hρr]
      simp only [div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inl hd0') (Or.inl hdtop'), inv_inv]
      calc μ (A ∩ closedBall x r) * (μ (closedBall x r))⁻¹ * (μ (closedBall x r) * (c r)⁻¹) *
            ((ν (closedBall x r))⁻¹ * c r)
          = μ (A ∩ closedBall x r) * (ν (closedBall x r))⁻¹ *
              ((μ (closedBall x r))⁻¹ * μ (closedBall x r)) * ((c r)⁻¹ * c r) := by ring
        _ = μ (A ∩ closedBall x r) * (ν (closedBall x r))⁻¹ := by
          rw [ENNReal.inv_mul_cancel hb0' hbtop', ENNReal.inv_mul_cancel (hc0 r hr) (hctop r),
            mul_one, mul_one]
    exact tendsto_nhds_unique hxD (hlim.congr' hev)
  -- Step 8: Radon–Nikodym, `ρ = ν ⌞ θ`.
  have hρeq : ρ = ν.withDensity fun x ↦ ENNReal.ofReal (θ x) := by
    rw [← withDensity_congr_ae hderiv, Measure.withDensity_rnDeriv_eq ρ ν hac]
  -- Step 9: evaluate on the Borel set `B`.
  calc μ (B ∩ A) = ρ B := (Measure.restrict_apply hB).symm
    _ = ν.withDensity (fun x ↦ ENNReal.ofReal (θ x)) B := by rw [← hρeq]
    _ = ∫⁻ x in B, ENNReal.ofReal (θ x) ∂ν := withDensity_apply _ hB
    _ = ∫⁻ x in B ∩ A, ENNReal.ofReal (θ x) ∂H := by rw [hν, Measure.restrict_restrict hB]
/-- Lebesgue density one of `H^n` on an arbitrary subset `T` of an `n`-plane (Simon Ch. 8, proof of
1.2, via the Lebesgue density theorem in `ℝ^n`): outside an `H^n`-null set `Z`, every `a ∈ T` has
`Θ^n(H^n ⌞ T, a) = 1`. -/
theorem Submission.frt_plane_subset_hasDensity_one :
    ∀ (N n : ℕ) (P : Grassmannian N n) (T : Set (Euclidean N)), T ⊆ (P.plane : Set (Euclidean N)) → ∃ Z : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) Z = 0 ∧ ∀ a ∈ T, a ∉ Z → HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict T) a 1 := by
  intro N n P T hT
  -- Step 1: an isometry `ι : ℝ^n → ℝ^N` onto the plane, from an orthonormal basis of `P.plane`.
  obtain ⟨ι, hι, hsurj⟩ : ∃ ι : EuclideanSpace ℝ (Fin n) → Euclidean N, Isometry ι ∧
      ∀ a ∈ (P.plane : Set (Euclidean N)), ∃ y, ι y = a := by
    let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] P.plane :=
      ((stdOrthonormalBasis ℝ P.plane).reindex (finCongr P.finrank_plane)).repr.symm
    exact ⟨P.plane.subtypeₗᵢ.comp e.toLinearIsometry, LinearIsometry.isometry _,
      fun a ha ↦ ⟨e.symm ⟨a, ha⟩, by simp⟩⟩
  -- Step 2: `H^n(ι B) = L^n(B)` for every `B ⊆ ℝ^n`.
  have hmeas : ∀ B : Set (EuclideanSpace ℝ (Fin n)),
      (μHE[n] : Measure (Euclidean N)) (ι '' B) = volume B := fun B ↦ by
    rw [hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Step 3: `ι(ι⁻¹(T) ∩ B_s(y)) = B_s(ι y) ∩ T`.
  have himg : ∀ y s, ι '' (ι ⁻¹' T ∩ closedBall y s) = closedBall (ι y) s ∩ T := by
    intro y s
    ext a
    constructor
    · rintro ⟨z, ⟨hzT, hz⟩, rfl⟩
      exact ⟨mem_closedBall.mpr ((hι.dist_eq z y).trans_le (mem_closedBall.mp hz)), hzT⟩
    · rintro ⟨ha, haT⟩
      obtain ⟨z, rfl⟩ := hsurj a (hT haT)
      exact ⟨z, ⟨haT, mem_closedBall.mpr ((hι.dist_eq z y).symm.trans_le (mem_closedBall.mp ha))⟩,
        rfl⟩
  -- Step 4: Lebesgue density theorem for `ι⁻¹(T)`, and a measurable null hull `E` of its bad set.
  obtain ⟨E, hbad, hEm, hE0⟩ := exists_measurable_superset_of_null (ae_iff.mp
    (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (ι ⁻¹' T)))
  rw [Measure.restrict_apply hEm] at hE0
  -- Step 5: `Z = ι(E ∩ ι⁻¹(T))` is `H^n`-null.
  refine ⟨ι '' (E ∩ ι ⁻¹' T), (hmeas _).trans hE0, ?_⟩
  -- Step 6: at `a = ι y ∈ T ∖ Z` the density ratio is `L^n(ι⁻¹(T) ∩ B_s(y)) / L^n(B_s(y)) → 1`.
  intro a haT haZ
  obtain ⟨y, rfl⟩ := hsurj a (hT haT)
  have hy : Tendsto (fun r ↦ volume (ι ⁻¹' T ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1) := by
    by_contra h
    exact haZ ⟨y, ⟨hbad h, haT⟩, rfl⟩
  refine hy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [densityRatio, Measure.restrict_apply measurableSet_closedBall, ← himg y s, hmeas,
    Measure.addHaar_closedBall volume y hs.le, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hs.le,
    unitBallVolume, mul_comm (ENNReal.ofReal s ^ n)]
/-- Hausdorff-measure comparison between an `L`-graph and its projection (used for the density-one
property of `H^n` on the carrier in the proof of Simon Ch. 8, 1.2; cf. Ch. 3, 1.6): if
`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ S` and `β = (1 + L²)^{1/2}`, then `p_P` is
`1`-Lipschitz, and injective on `S` with a `β`-Lipschitz inverse, so for `x ∈ S` and `r ∈ ℝ`
`H^n(p_P(S) ∩ B_{r/β}(p_P x)) ≤ H^n(S ∩ B_r(x)) ≤ β^n H^n(p_P(S) ∩ B_r(p_P x))`, and
`H^n(S ∩ p_P⁻¹(Y)) ≤ β^n H^n(Y)` for every `Y ⊆ ℝ^N`. -/
theorem Submission.frt_lipschitz_graph_hausdorff_compare :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (S : Set (Euclidean N)), 0 ≤ L → (∀ y ∈ S, ∀ z ∈ S, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → (∀ x ∈ S, ∀ r : ℝ, (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2))) ≤ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ∧ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) r)) ∧ ∀ Y : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) (S ∩ Grassmannian.project P ⁻¹' Y) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
  intro N n P L S hL hgraph
  -- Step 1: `β = √(1 + L²)` satisfies `β ≥ 1 > 0`.
  have hβ0 : 0 < Real.sqrt (1 + L ^ 2) :=
    one_pos.trans_le (Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg L)))
  -- Step 2: `p_P` is linear.
  have hsub : ∀ u v : Euclidean N,
      Grassmannian.project P (u - v) = Grassmannian.project P u - Grassmannian.project P v :=
    fun u v ↦ map_sub P.projectionLinearMap u v
  -- Step 3: `p_P` is symmetric and idempotent, so `|v|² = |p_P v|² + |v - p_P v|²`; hence
  -- `|p_P v| ≤ |v|` and `p_P` is `1`-Lipschitz.
  have hpyth : ∀ v : Euclidean N,
      ‖v‖ ^ 2 = ‖Grassmannian.project P v‖ ^ 2 + ‖v - Grassmannian.project P v‖ ^ 2 := by
    intro v
    have hker : Grassmannian.project P (v - Grassmannian.project P v) = 0 := by
      rw [hsub, Grassmannian.project_project, sub_self]
    have horth : inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) = 0 := by
      rw [show inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) =
          inner ℝ v (Grassmannian.project P (v - Grassmannian.project P v)) from
        P.projectionLinearMap_isSymmetric v (v - Grassmannian.project P v), hker, inner_zero_right]
    have h := norm_add_sq_real (Grassmannian.project P v) (v - Grassmannian.project P v)
    rw [horth, add_sub_cancel] at h
    linarith
  have hnorm : ∀ v : Euclidean N, ‖Grassmannian.project P v‖ ≤ ‖v‖ := by
    intro v
    have h := hpyth v
    nlinarith [norm_nonneg v, norm_nonneg (Grassmannian.project P v),
      sq_nonneg ‖v - Grassmannian.project P v‖]
  have hlip : ∀ A : Set (Euclidean N), LipschitzOnWith 1 (Grassmannian.project P) A := by
    refine fun A ↦ LipschitzOnWith.mk_one fun u _ v _ ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← hsub]
    exact hnorm (u - v)
  -- Step 4: on `S`, `|y - z|² ≤ (1 + L²) |p_P(y - z)|²`, i.e. `|y - z| ≤ β |p_P y - p_P z|`.
  have hkey : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤
      Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P y - Grassmannian.project P z‖ := by
    intro y hy z hz
    rw [← hsub]
    have h1 := hpyth (y - z)
    have h2 := hgraph y hy z hz
    have h3 : ‖(y - z) - Grassmannian.project P (y - z)‖ ^ 2 ≤
        (L * ‖Grassmannian.project P (y - z)‖) ^ 2 := by
      gcongr
    have h4 : ‖y - z‖ ^ 2 ≤ (1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ ^ 2 := by
      nlinarith
    calc ‖y - z‖ = Real.sqrt (‖y - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ ^ 2) := Real.sqrt_le_sqrt h4
      _ = Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  -- Step 5: `p_P` is injective on `S`, and `h = invFunOn p_P S` is `β`-Lipschitz on `p_P(S)` with
  -- `h (p_P y) = y` for `y ∈ S`.
  have hinj : InjOn (Grassmannian.project P) S := by
    intro y hy z hz hyz
    have h := hkey y hy z hz
    rw [hyz, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hleft : ∀ y ∈ S,
      Function.invFunOn (Grassmannian.project P) S (Grassmannian.project P y) = y :=
    fun y hy ↦ hinj.leftInvOn_invFunOn hy
  have hinv : LipschitzOnWith (Real.toNNReal (Real.sqrt (1 + L ^ 2)))
      (Function.invFunOn (Grassmannian.project P) S) (Grassmannian.project P '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [hleft y hy, hleft z hz, dist_eq_norm, dist_eq_norm]
    exact hkey y hy z hz
  -- Steps 6–7 (b): `S ∩ p_P⁻¹(Y) = h(p_P(S ∩ p_P⁻¹(Y)))` and `p_P(S ∩ p_P⁻¹(Y)) ⊆ Y`, so the
  -- Lipschitz image bound for `h` gives `H^n(S ∩ p_P⁻¹(Y)) ≤ β^n H^n(Y)`.
  have hb : ∀ Y : Set (Euclidean N), (μHE[n] : Measure (Euclidean N))
      (S ∩ Grassmannian.project P ⁻¹' Y) ≤
        ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
    intro Y
    calc (μHE[n] : Measure (Euclidean N)) (S ∩ Grassmannian.project P ⁻¹' Y)
        = (μHE[n] : Measure (Euclidean N)) (Function.invFunOn (Grassmannian.project P) S ''
            (Grassmannian.project P '' (S ∩ Grassmannian.project P ⁻¹' Y))) := by
          rw [hinj.invFunOn_image inter_subset_left]
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N))
            (Grassmannian.project P '' (S ∩ Grassmannian.project P ⁻¹' Y)) :=
          Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hinv.mono (image_mono inter_subset_left))
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
          gcongr
          exact (image_mono inter_subset_right).trans (image_preimage_subset _ _)
  refine ⟨fun x hx r ↦ ⟨?_, ?_⟩, hb⟩
  · -- Step 8: `p_P(S) ∩ B_{r/β}(p_P x) ⊆ p_P(S ∩ B_r(x))`, then the `1`-Lipschitz bound for `p_P`.
    have hsubset : Grassmannian.project P '' S ∩
        closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2)) ⊆
          Grassmannian.project P '' (S ∩ closedBall x r) := by
      rintro _ ⟨⟨z, hz, rfl⟩, hzr⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hzr ⊢
      calc ‖z - x‖
          ≤ Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P z - Grassmannian.project P x‖ :=
            hkey z hz x hx
        _ ≤ Real.sqrt (1 + L ^ 2) * (r / Real.sqrt (1 + L ^ 2)) :=
            mul_le_mul_of_nonneg_left hzr hβ0.le
        _ = r := mul_div_cancel₀ r hβ0.ne'
    calc (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' S ∩
          closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2)))
        ≤ (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' (S ∩ closedBall x r)) :=
          measure_mono hsubset
      _ ≤ ((1 : NNReal) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) :=
          Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hlip _)
      _ = (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) := by
          rw [ENNReal.coe_one, one_pow, one_mul]
  · -- Step 9: `S ∩ B_r(x) ⊆ S ∩ p_P⁻¹(p_P(S) ∩ B_r(p_P x))`, as `|p_P z - p_P x| ≤ |z - x|`;
    -- then (b).
    have hsubset : S ∩ closedBall x r ⊆ S ∩ Grassmannian.project P ⁻¹'
        (Grassmannian.project P '' S ∩ closedBall (Grassmannian.project P x) r) := by
      rintro z ⟨hz, hzr⟩
      refine ⟨hz, mem_image_of_mem _ hz, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzr ⊢
      rw [← hsub]
      exact (hnorm (z - x)).trans hzr
    exact (measure_mono hsubset).trans (hb _)

/-- Two-sided density bounds on a closed Lipschitz-graph piece (Simon Ch. 8, proof of 1.2, the
density-one step for `H^n ⌞ A` on one graph piece `Γ`): let `H^n(A) < ∞` with `A` `H^n`-measurable,
`L ≥ 0`, `β = (1 + L²)^{1/2}`, and let `Γ` be closed with `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|`
for `y, z ∈ Γ`.  Then for `(H^n ⌞ A) ⌞ Γ`-a.e. `x`, with `λ = H^n ⌞ A`,
`β^{-n} ≤ liminf_{r↓0} λ(B_r(x)) / (ω_n r^n)` and `limsup_{r↓0} λ(B_r(x)) / (ω_n r^n) ≤ β^n`. -/
theorem Submission.frt_graph_piece_density_bounds :
    ∀ (N n : ℕ) (A Γ : Set (Euclidean N)) (P : Grassmannian N n) (L : ℝ), μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → 0 ≤ L → IsClosed Γ → (∀ y ∈ Γ, ∀ z ∈ Γ, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → ∀ᵐ x ∂((μHE[n] : Measure (Euclidean N)).restrict A).restrict Γ, (ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n)⁻¹ ≤ liminf (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ∧ limsup (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n := by
  intro N n A Γ P L hA hAm hL hΓ hgraph
  set H : Measure (Euclidean N) := (μHE[n] : Measure (Euclidean N))
  set β : ℝ := Real.sqrt (1 + L ^ 2)
  set c : ℝ≥0∞ := ENNReal.ofReal β ^ n with hc
  set ω : ℝ≥0∞ := unitBallVolume n
  set lam : Measure (Euclidean N) := H.restrict A with hlam
  -- Step 1: `β > 0`, so `c = β^n ∈ (0, ∞)`; and `λ = H^n ⌞ A` is a finite measure.
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hc0 : c ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hβ0).ne'
  have hctop : c ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 hA
  -- Step 2: `A_c = A ∩ Γ` is an `L`-graph, and `T = p_P(A_c)` lies in `P.plane`.
  set Ac : Set (Euclidean N) := A ∩ Γ with hAc
  set T : Set (Euclidean N) := Grassmannian.project P '' Ac
  have hTP : T ⊆ (P.plane : Set (Euclidean N)) := by
    rintro _ ⟨y, -, rfl⟩
    exact LinearMap.mem_range_self _ y
  -- Steps 3–4: the plane density result gives an `H^n`-null `Z` off which `H^n ⌞ T` has density
  -- one on `T`; the graph comparison gives the ball bounds (i)/(ii) for `A_c`, and
  -- `H^n(A_c ∩ p_P⁻¹(Z)) ≤ c H^n(Z) = 0`.
  obtain ⟨Z, hZ0, hZ⟩ := Submission.frt_plane_subset_hasDensity_one N n P T hTP
  obtain ⟨hball, hpre⟩ := Submission.frt_lipschitz_graph_hausdorff_compare N n P L Ac hL
    (fun y hy z hz ↦ hgraph y hy.2 z hz.2)
  have hX0 : H (Ac ∩ Grassmannian.project P ⁻¹' Z) = 0 := by
    have h := hpre Z
    rw [hZ0, mul_zero] at h
    exact le_antisymm h bot_le
  -- Step 5: Besicovitch differentiation, `λ(Γ ∩ B_r(x)) / λ(B_r(x)) → 1` for `λ ⌞ Γ`-a.e. `x`.
  have hbes := Besicovitch.ae_tendsto_measure_inter_div lam Γ
  -- Step 6: `λ ⌞ Γ = H^n ⌞ (Γ ∩ A)`, so `λ ⌞ Γ`-a.e. `x` lies in `A_c` and off `A_c ∩ p_P⁻¹(Z)`.
  have hrr : lam.restrict Γ = H.restrict (Γ ∩ A) := Measure.restrict_restrict hΓ.measurableSet
  have hmem : ∀ᵐ x ∂lam.restrict Γ, x ∈ Γ ∩ A := by
    rw [hrr]
    exact ae_restrict_mem₀ (hΓ.measurableSet.nullMeasurableSet.inter hAm)
  have hnotX : ∀ᵐ x ∂lam.restrict Γ, x ∉ Ac ∩ Grassmannian.project P ⁻¹' Z := by
    rw [hrr]
    exact ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hX0)
  filter_upwards [hbes, hmem, hnotX] with x hq hxm hxX
  have hxAc : x ∈ Ac := ⟨hxm.2, hxm.1⟩
  -- Step 7: `a = p_P x ∈ T ∖ Z`, so `g(s) = H^n(T ∩ B_s(a)) / (ω_n s^n) → 1` as `s ↓ 0`.
  set a := Grassmannian.project P x
  have hg : Tendsto (densityRatio n (H.restrict T) a) (𝓝[>] 0) (𝓝 1) :=
    hZ a ⟨x, hxAc, rfl⟩ fun h ↦ hxX ⟨hxAc, h⟩
  have hgeq : ∀ s, densityRatio n (H.restrict T) a s =
      H (T ∩ closedBall a s) / (ω * ENNReal.ofReal s ^ n) := by
    intro s
    rw [densityRatio, Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- Step 8: the key identity `λ(Γ ∩ B_r(x)) = H^n(A_c ∩ B_r(x))`.
  have hkey : ∀ r, lam (Γ ∩ closedBall x r) = H (Ac ∩ closedBall x r) := by
    intro r
    rw [hlam, Measure.restrict_apply (hΓ.measurableSet.inter measurableSet_closedBall)]
    congr 1
    ext y
    simp only [mem_inter_iff, hAc]
    tauto
  constructor
  · -- Step 9: for `r > 0`, `densityRatio n λ x r ≥ c⁻¹ g(r/β)`, since `ω_n r^n = c ω_n (r/β)^n`
    -- and `λ(B_r(x)) ≥ H^n(A_c ∩ B_r(x)) ≥ H^n(T ∩ B_{r/β}(a))`; and `c⁻¹ g(r/β) → c⁻¹`.
    have hdiv : Tendsto (fun r : ℝ ↦ r / β) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun r : ℝ ↦ r / β) (𝓝 0) (𝓝 (0 / β)) := tendsto_id.div_const β
        rw [zero_div] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using div_pos hr hβ0
    have hlim : Tendsto (fun r ↦ c⁻¹ * densityRatio n (H.restrict T) a (r / β)) (𝓝[>] 0)
        (𝓝 (c⁻¹ * 1)) :=
      ENNReal.Tendsto.const_mul (hg.comp hdiv) (Or.inr (ENNReal.inv_ne_top.2 hc0))
    rw [mul_one] at hlim
    have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        c⁻¹ * densityRatio n (H.restrict T) a (r / β) ≤ densityRatio n lam x r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hgeq]
      have hnorm : ω * ENNReal.ofReal r ^ n = c * (ω * ENNReal.ofReal (r / β) ^ n) := by
        have h : ENNReal.ofReal r = ENNReal.ofReal β * ENNReal.ofReal (r / β) := by
          rw [← ENNReal.ofReal_mul hβ0.le, mul_div_cancel₀ r hβ0.ne']
        rw [h, mul_pow, hc]
        ring
      have hnum : H (T ∩ closedBall a (r / β)) ≤ lam (closedBall x r) :=
        calc H (T ∩ closedBall a (r / β)) ≤ H (Ac ∩ closedBall x r) := (hball x hxAc r).1
          _ = lam (Γ ∩ closedBall x r) := (hkey r).symm
          _ ≤ lam (closedBall x r) := measure_mono inter_subset_right
      calc c⁻¹ * (H (T ∩ closedBall a (r / β)) / (ω * ENNReal.ofReal (r / β) ^ n))
          = H (T ∩ closedBall a (r / β)) / (c * (ω * ENNReal.ofReal (r / β) ^ n)) := by
            generalize H (T ∩ closedBall a (r / β)) = M
            generalize ω * ENNReal.ofReal (r / β) ^ n = D
            rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
            ring
        _ = H (T ∩ closedBall a (r / β)) / (ω * ENNReal.ofReal r ^ n) := by rw [hnorm]
        _ ≤ lam (closedBall x r) / (ω * ENNReal.ofReal r ^ n) := by gcongr
        _ = densityRatio n lam x r := rfl
    calc c⁻¹ = liminf (fun r ↦ c⁻¹ * densityRatio n (H.restrict T) a (r / β)) (𝓝[>] 0) :=
          hlim.liminf_eq.symm
      _ ≤ liminf (densityRatio n lam x) (𝓝[>] 0) := liminf_le_liminf hle
  · -- Step 10: eventually `q_x(r) ≠ 0`, and then `λ(B_r(x)) = q_x(r)⁻¹ λ(Γ ∩ B_r(x))` with
    -- `λ(Γ ∩ B_r(x)) = H^n(A_c ∩ B_r(x)) ≤ c H^n(T ∩ B_r(a))`, so
    -- `densityRatio n λ x r ≤ q_x(r)⁻¹ (c g(r)) → 1⁻¹ (c · 1) = c`.
    have hne : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (Γ ∩ closedBall x r) / lam (closedBall x r) ≠ 0 :=
      hq.eventually_ne one_ne_zero
    have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), densityRatio n lam x r ≤
        (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
          (c * densityRatio n (H.restrict T) a r) := by
      filter_upwards [hne] with r hr
      have hΓB0 : lam (Γ ∩ closedBall x r) ≠ 0 := by
        intro h
        apply hr
        rw [h, ENNReal.zero_div]
      have hΓBtop : lam (Γ ∩ closedBall x r) ≠ ∞ := measure_ne_top _ _
      have hBtop : lam (closedBall x r) ≠ ∞ := measure_ne_top _ _
      have hB0 : lam (closedBall x r) ≠ 0 := fun h ↦
        hΓB0 (measure_mono_null inter_subset_right h)
      have hinv : (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ =
          lam (closedBall x r) / lam (Γ ∩ closedBall x r) :=
        ENNReal.inv_div (Or.inl hBtop) (Or.inl hB0)
      have hBeq : lam (closedBall x r) =
          (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * lam (Γ ∩ closedBall x r) := by
        rw [hinv, ENNReal.div_mul_cancel hΓB0 hΓBtop]
      rw [hgeq]
      calc densityRatio n lam x r = lam (closedBall x r) / (ω * ENNReal.ofReal r ^ n) := rfl
        _ = (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * lam (Γ ∩ closedBall x r) /
              (ω * ENNReal.ofReal r ^ n) := by rw [← hBeq]
        _ ≤ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * (c * H (T ∩ closedBall a r)) /
              (ω * ENNReal.ofReal r ^ n) := by
            gcongr
            rw [hkey r]
            exact (hball x hxAc r).2
        _ = _ := by rw [mul_div_assoc, mul_div_assoc]
    have hlim : Tendsto (fun r ↦ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
        (c * densityRatio n (H.restrict T) a r)) (𝓝[>] 0) (𝓝 (1⁻¹ * (c * 1))) :=
      ENNReal.Tendsto.mul (tendsto_inv_iff.2 hq) (Or.inl (by simp))
        (ENNReal.Tendsto.const_mul hg (Or.inl one_ne_zero)) (Or.inl (by simp [hc0]))
    rw [inv_one, mul_one, one_mul] at hlim
    calc limsup (densityRatio n lam x) (𝓝[>] 0)
        ≤ limsup (fun r ↦ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
            (c * densityRatio n (H.restrict T) a r)) (𝓝[>] 0) := limsup_le_limsup hle
      _ = c := hlim.limsup_eq

/-- Density one of `H^n` on a set covered by closed Lipschitz graphs of arbitrarily small slope
(Simon Ch. 8, proof of 1.2, the density-one property of `H^n` on the rectifiable carrier; cf. Ch. 3,
1.6 and 1.9): if `H^n(A) < ∞`, `A` is `H^n`-measurable and, for every `L ∈ (0,1]`, `A` is covered by
countably many closed sets `Γ`, each an `L`-graph over some `P ∈ G(N,n)`
(`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` on `Γ`), then `Θ^n(H^n ⌞ A, x) = 1` for
`H^n ⌞ A`-a.e. `x`. -/
theorem Submission.frt_hausdorff_density_one_of_flat_covers :
    ∀ (N n : ℕ) (A : Set (Euclidean N)), μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → (∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ A ⊆ ⋃ c ∈ C, c.2) → ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)).restrict A, HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict A) x 1 := by
  intro N n A hA hAm hcov
  set lam : Measure (Euclidean N) := (μHE[n] : Measure (Euclidean N)).restrict A
  -- Slopes `L_l = 1/(l+1) ∈ (0,1]` with factors `c_l = β_l^n`, `β_l = (1 + L_l²)^{1/2}`.
  set c : ℕ → ℝ≥0∞ := fun l ↦ ENNReal.ofReal (Real.sqrt (1 + (1 / ((l : ℝ) + 1)) ^ 2)) ^ n
  -- Step 8: for each `l`, `c_l⁻¹ ≤ liminf` and `limsup ≤ c_l` for `λ`-a.e. `x`.
  have hstep : ∀ l : ℕ, ∀ᵐ x ∂lam, (c l)⁻¹ ≤ liminf (densityRatio n lam x) (𝓝[>] 0) ∧
      limsup (densityRatio n lam x) (𝓝[>] 0) ≤ c l := by
    intro l
    have hL0 : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
    have hL1 : 1 / ((l : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg l)) (by positivity)
    obtain ⟨C, hCc, hC, hAC⟩ := hcov _ hL0 hL1
    -- `λ`-a.e. point lies in `A ⊆ W = ⋃_{c ∈ C} c.2`, so `λ ⌞ W = λ`.
    have hW : lam.restrict (⋃ c ∈ C, c.2) = lam :=
      Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem₀ hAm).mono fun x hx ↦ hAC hx)
    have h := (ae_restrict_biUnion_iff Prod.snd hCc _).2 fun c hcC ↦
      Submission.frt_graph_piece_density_bounds N n A c.2 c.1 _ hA hAm hL0.le (hC c hcC).1
        (hC c hcC).2
    rwa [hW] at h
  -- Step 9: `c_l → 1`, hence `c_l⁻¹ → 1`.
  have hlim : Tendsto c atTop (𝓝 1) := by
    have hcont : Continuous fun t : ℝ ↦ ENNReal.ofReal (Real.sqrt (1 + t ^ 2)) ^ n :=
      (ENNReal.continuous_pow n).comp (ENNReal.continuous_ofReal.comp
        (continuous_const.add (continuous_pow 2)).sqrt)
    have h := (hcont.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_one, ENNReal.ofReal_one, one_pow] at h
    exact h
  have hinv : Tendsto (fun l ↦ (c l)⁻¹) atTop (𝓝 1) := by
    have h := hlim.inv
    rwa [inv_one] at h
  -- So `1 ≤ liminf` and `limsup ≤ 1` `λ`-a.e., i.e. `Θ^n(λ, x) = 1`.
  filter_upwards [ae_all_iff.2 hstep] with x hx
  exact tendsto_of_le_liminf_of_limsup_le (le_of_tendsto' hinv fun l ↦ (hx l).1)
    (ge_of_tendsto' hlim fun l ↦ (hx l).2)
/-- Simon Ch. 8, proof of 1.2 (the null case of the upper counterpart of the density comparison
Ch. 1, 3.3): if `H^n(A) = 0` and `μ(B_ρ(x)) ≤ c ρ^n` for all `x ∈ A` and `0 < ρ ≤ δ`, with
`c < ∞`, then `μ(A) = 0` (outer measure; `A` need not be measurable). -/
theorem Submission.frt_measure_null_of_hausdorff_null_ball_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (A : Set (Euclidean N)) (c : ℝ≥0∞) (δ : ℝ), c ≠ ∞ → 0 < δ → μHE[n] A = 0 → (∀ x ∈ A, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → μ (closedBall x ρ) ≤ c * ENNReal.ofReal ρ ^ n) → μ A = 0 := by
  intro N n μ A c δ hc hδ hA hball
  -- Step 1: `H^n = c_n • μH[n]` with `c_n ≠ 0`, so the unnormalised `μH[n](A)` vanishes.
  have hH : (μH[(n : ℝ)] : Measure (Euclidean N)) A = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      mul_eq_zero] at hA
    rcases hA with h | h
    · exact absurd (by exact_mod_cast h) (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
    · exact h
  -- Step 2: one covering set `t` with `diam t ≤ δ` has `μ(t ∩ A) ≤ c · ⨆_{t ≠ ∅} (diam t)^n`.
  have hone : ∀ t : Set (Euclidean N), ediam t ≤ ENNReal.ofReal δ →
      μ (t ∩ A) ≤ c * ⨆ (_ : t.Nonempty), ediam t ^ n := by
    intro t ht
    rcases (t ∩ A).eq_empty_or_nonempty with h | ⟨x, hxt, hxA⟩
    · simp [h]
    rw [iSup_pos ⟨x, hxt⟩]
    have hfin : ediam t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ht
    set d := (ediam t).toReal
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    have hdδ : d ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le ht
    have hdeq : ENNReal.ofReal d = ediam t := ENNReal.ofReal_toReal hfin
    -- `t ⊆ B_r(x)` for every `r ≥ d`, since `x ∈ t`.
    have hsub : ∀ r : ℝ, d ≤ r → t ∩ A ⊆ closedBall x r := by
      intro r hr y hy
      rw [mem_closedBall, dist_edist]
      exact (ENNReal.toReal_mono hfin (edist_le_ediam_of_mem hy.1 hxt)).trans hr
    rcases hd0.lt_or_eq with hdpos | hdzero
    · -- Case `d > 0`: the ball bound at `ρ = d`.
      calc μ (t ∩ A) ≤ μ (closedBall x d) := measure_mono (hsub d le_rfl)
        _ ≤ c * ENNReal.ofReal d ^ n := hball x hxA d hdpos hdδ
        _ = c * ediam t ^ n := by rw [hdeq]
    · have hdiam0 : ediam t = 0 := by rw [← hdeq, ← hdzero, ENNReal.ofReal_zero]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · -- Case `d = 0`, `n = 0`: the ball bound at `ρ = δ`.
        subst hn
        calc μ (t ∩ A) ≤ μ (closedBall x δ) := measure_mono (hsub δ (hdzero ▸ hδ.le))
          _ ≤ c * ENNReal.ofReal δ ^ 0 := hball x hxA δ hδ le_rfl
          _ = c * ediam t ^ 0 := by simp
      · -- Case `d = 0`, `n ≥ 1`: let `ρ ↓ 0`; `c ρ^n → 0` because `c ≠ ∞`.
        rw [hdiam0, zero_pow hn.ne', mul_zero]
        have h1 : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ) (𝓝[>] 0) (𝓝 0) := by
          have := ENNReal.continuous_ofReal.tendsto 0
          rw [ENNReal.ofReal_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
          have := ((ENNReal.continuous_pow n).tendsto 0).comp h1
          simpa [Function.comp_def, zero_pow hn.ne'] using this
        have h3 : Tendsto (fun ρ : ℝ => c * ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
          simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hc)
        refine ge_of_tendsto h3 ?_
        filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
        calc μ (t ∩ A) ≤ μ (closedBall x ρ) := measure_mono (hsub ρ (hdzero ▸ hρ.1.le))
          _ ≤ c * ENNReal.ofReal ρ ^ n := hball x hxA ρ hρ.1 hρ.2.le
  -- Step 3: `μH[n](A) = 0` gives, for each `ζ > 0`, a cover of `A` by sets of diameter `≤ δ`
  -- with `∑_k ⨆_{t_k ≠ ∅} (diam t_k)^n < ζ` (`hausdorffMeasure_apply` at scale `r = δ`).
  have hcover : ∀ ζ : ℝ≥0∞, 0 < ζ → ∃ t : ℕ → Set (Euclidean N), A ⊆ ⋃ k, t k ∧
      (∀ k, ediam (t k) ≤ ENNReal.ofReal δ) ∧ ∑' k, ⨆ (_ : (t k).Nonempty), ediam (t k) ^ n < ζ := by
    intro ζ hζ
    rw [Measure.hausdorffMeasure_apply] at hH
    have hle : (⨅ (t : ℕ → Set (Euclidean N)) (_ : A ⊆ ⋃ k, t k)
        (_ : ∀ k, ediam (t k) ≤ ENNReal.ofReal δ),
          ∑' k, ⨆ (_ : (t k).Nonempty), ediam (t k) ^ (n : ℝ)) = 0 := by
      refine nonpos_iff_eq_zero.1 ?_
      rw [← hH]
      exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ) le_rfl
    have hlt := hle ▸ hζ
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hcov, ht⟩ := iInf_lt_iff.1 ht
    obtain ⟨hdiam, hsum⟩ := iInf_lt_iff.1 ht
    refine ⟨t, hcov, hdiam, ?_⟩
    simpa only [ENNReal.rpow_natCast] using hsum
  -- Step 4: countable subadditivity gives `μ(A) ≤ c · ζ` for every `ζ > 0`.
  have key : ∀ ζ : ℝ≥0∞, 0 < ζ → μ A ≤ c * ζ := by
    intro ζ hζ
    obtain ⟨t, hcov, hdiam, hsum⟩ := hcover ζ hζ
    calc μ A ≤ μ (⋃ k, t k ∩ A) := by
          refine measure_mono fun y hy => ?_
          obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hy)
          exact mem_iUnion.2 ⟨k, hk, hy⟩
      _ ≤ ∑' k, μ (t k ∩ A) := measure_iUnion_le _
      _ ≤ ∑' k, c * ⨆ (_ : (t k).Nonempty), ediam (t k) ^ n :=
          ENNReal.tsum_le_tsum fun k => hone (t k) (hdiam k)
      _ = c * ∑' k, ⨆ (_ : (t k).Nonempty), ediam (t k) ^ n := ENNReal.tsum_mul_left
      _ ≤ c * ζ := by gcongr
  -- Step 5: `c < ∞`, so `ζ = ε / c` (or `ζ = 1` when `c = 0`) gives `μ(A) = 0`.
  refine nonpos_iff_eq_zero.1 ?_
  rcases eq_or_ne c 0 with h0 | h0
  · simpa [h0] using key 1 one_pos
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := key (ε / c) (ENNReal.div_pos (by exact_mod_cast hε.ne') hc)
    rw [ENNReal.mul_div_cancel h0 hc] at this
    simpa using this
/-- Finite density gives a small-ball mass bound (Simon Ch. 8, proof of 1.2: the decomposition
`Z = ⋃ Z_{k,j}` at a single point).  If `Θ^n(μ, x) = θ < ∞`, then there are `K, j ∈ ℕ` with
`μ(B_ρ(x)) ≤ K ρ^n` for all `0 < ρ ≤ 1/(j+1)`: eventually `μ(B_ρ(x))/(ω_n ρ^n) < m` for a natural
`m > θ`, and `K` is any natural number above `m ω_n`. -/
theorem Submission.frt_ball_bound_of_finite_density :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞), θ ≠ ∞ → HasDensity n μ x θ → ∃ K j : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / ((j : ℝ) + 1) → μ (closedBall x ρ) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ρ ^ n := by
  intro N n μ x θ hθ hdens
/-- Uniform lower density bound (Simon Ch. 8, 1.2, Step 1 "uniform pieces" of the proof that `M` is
`H^n`-measurable): if `Θ^n(μ, x) = t > 0` (`t = ∞` allowed), then for some `m, k ∈ ℕ`,
`(2(m+1))⁻¹ ≤ μ(B_ρ(x))/(ω_n ρ^n)` for every `0 < ρ ≤ 1/(k+1)`. -/
theorem Submission.frt_cnm_exists_uniform_densityRatio_lower :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (t : ℝ≥0∞), 0 < t → HasDensity n μ x t → ∃ m k : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / ((k : ℝ) + 1) → (2 * ((m : ℝ≥0∞) + 1))⁻¹ ≤ densityRatio n μ x ρ := by
  intro N n μ x t ht hdens
  -- Step 1: `m⁻¹ < t` for some `m ∈ ℕ`, hence `(m + 1)⁻¹ ≤ m⁻¹ < t`.
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt ht.ne'
  have hm1 : ((m : ℝ≥0∞) + 1)⁻¹ ≤ t :=
    (ENNReal.inv_le_inv.2 (le_add_of_nonneg_right zero_le_one)).trans hm.le
  -- Step 2: `a = m + 1 ∈ (0, ∞)` gives `a = 1 * a < 2 * a`, so `c = (2a)⁻¹ < a⁻¹ ≤ t`.
  have ha0 : (m : ℝ≥0∞) + 1 ≠ 0 := (zero_lt_one.trans_le (le_add_of_nonneg_left zero_le)).ne'
  have hatop : (m : ℝ≥0∞) + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩
  have hc : (2 * ((m : ℝ≥0∞) + 1))⁻¹ < t := by
    refine lt_of_lt_of_le (ENNReal.inv_lt_inv.2 ?_) hm1
    calc (m : ℝ≥0∞) + 1 = 1 * ((m : ℝ≥0∞) + 1) := (one_mul _).symm
      _ < 2 * ((m : ℝ≥0∞) + 1) := ENNReal.mul_lt_mul_left ha0 hatop ENNReal.one_lt_two
  -- Step 3: `Ioi c` is a neighbourhood of `t`, so its preimage `S` lies in `𝓝[>] 0`.
  have hS : densityRatio n μ x ⁻¹' Ioi (2 * ((m : ℝ≥0∞) + 1))⁻¹ ∈ 𝓝[>] (0 : ℝ) :=
    Filter.tendsto_def.1 hdens _ (Ioi_mem_nhds hc)
  -- Step 4: some `(0, u)` lies in `S`, and `1/(k+1) < u` for some `k ∈ ℕ`.
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hS
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
  -- Step 5: every `ρ ∈ (0, 1/(k+1)]` lies in `(0, u) ⊆ S`.
  refine ⟨m, k, fun ρ hρ hρk ↦ ?_⟩
  have hρS : ρ ∈ densityRatio n μ x ⁻¹' Ioi (2 * ((m : ℝ≥0∞) + 1))⁻¹ :=
    hsub ⟨hρ, hρk.trans_lt hk⟩
  exact le_of_lt hρS
/-- Uniform lower density-ratio bounds pass to the closure (Step 4 of the proof that the carrier `M`
in Simon Ch. 8, 1.2 is `H^n`-measurable): if `c ≤ μ(B_ρ(x))/(ω_n ρ^n)` for all `x ∈ E` and
`0 < ρ ≤ δ`, then the same holds for all `y ∈ closure E`, since `B_s(x) ⊆ B_ρ(y)` whenever
`s + |x - y| ≤ ρ`, and `s ↑ ρ`. -/
theorem Submission.frt_cnm_densityRatio_lower_closure :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (E : Set (Euclidean N)) (c : ℝ≥0∞) (δ : ℝ), (∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → c ≤ densityRatio n μ x ρ) → ∀ y ∈ closure E, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → c ≤ densityRatio n μ y ρ := by
  intro N n μ E c δ hE y hy ρ hρ hρδ
  -- Step 1: `0 < ω_n < ∞` (`volume` on `ℝ^n` is an additive Haar measure).
  have hω0 : unitBallVolume n ≠ 0 :=
    (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).ne
  -- Step 2: a natural number `m > θ`.
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hθ
  -- Step 3: `densityRatio n μ x ρ < m` for all `ρ ∈ (0, ε)`.
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hdens (Iio_mem_nhds hm))
  -- Step 4: `1/(j+1) < ε`.
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.1 hε)
  -- Step 5: a natural number `K > m ω_n`.
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hωtop)
  refine ⟨K, j, fun ρ hρ hρj ↦ ?_⟩
  -- Step 6: `ρ ∈ (0, ε)`; clear the denominator `ω_n ρ^n ∈ (0, ∞)`.
  have hlt : densityRatio n μ x ρ < m := hεsub ⟨hρ, hρj.trans_lt hj⟩
  have hD0 : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne')
  have hDtop : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- Step 7: `μ(B_ρ(x)) < m (ω_n ρ^n) = (m ω_n) ρ^n ≤ K ρ^n`.
  calc μ (closedBall x ρ) ≤ m * (unitBallVolume n * ENNReal.ofReal ρ ^ n) :=
        ((ENNReal.div_lt_iff (Or.inl hD0) (Or.inl hDtop)).1 hlt).le
    _ = m * unitBallVolume n * ENNReal.ofReal ρ ^ n := (mul_assoc _ _ _).symm
    _ ≤ K * ENNReal.ofReal ρ ^ n := mul_le_mul_left hK.le _

/-- Simon Ch. 8, proof of 1.2, step (3a) (the covering comparison of Ch. 1, 3.2): if `H^n(Z) = 0`
and `Θ^n(μ, x)` exists and is finite at every `x ∈ Z`, then `μ(Z) = 0`. -/
theorem Submission.frt_weight_null_of_hausdorff_null :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (Z : Set (Euclidean N)), μHE[n] Z = 0 → (∀ x ∈ Z, ∃ θ : ℝ≥0∞, θ ≠ ∞ ∧ HasDensity n μ x θ) → μ Z = 0 := by
  intro N n μ Z hZ hdens
  -- `Z_{K,j}`: the points `x ∈ Z` with `μ(B_ρ(x)) ≤ K ρ^n` for all `0 < ρ ≤ 1/(j+1)`.
  let Zs : ℕ → ℕ → Set (Euclidean N) := fun K j ↦ {x | x ∈ Z ∧ ∀ ρ : ℝ, 0 < ρ →
    ρ ≤ 1 / ((j : ℝ) + 1) → μ (closedBall x ρ) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ρ ^ n}
  -- Step 1: a finite density at `x ∈ Z` puts `x` into some `Z_{K,j}`.
  have hcover : Z ⊆ ⋃ (K : ℕ) (j : ℕ), Zs K j := fun x hx ↦ by
    obtain ⟨θ, hθ, hxθ⟩ := hdens x hx
    obtain ⟨K, j, hKj⟩ := Submission.frt_ball_bound_of_finite_density N n μ x θ hθ hxθ
    exact mem_iUnion₂.2 ⟨K, j, hx, hKj⟩
  -- Steps 2–5: `Z_{K,j} ⊆ Z` is `H^n`-null and satisfies the ball bound with the finite constant
  -- `K` at scales `ρ ≤ 1/(j+1)`, so the covering comparison makes it `μ`-null.
  have hnull (K j : ℕ) : μ (Zs K j) = 0 :=
    Submission.frt_measure_null_of_hausdorff_null_ball_bound N n μ (Zs K j) K (1 / ((j : ℝ) + 1))
      (ENNReal.natCast_ne_top K) Nat.one_div_pos_of_nat (measure_mono_null (fun _ hx ↦ hx.1) hZ)
      fun _ hx ↦ hx.2
  -- Countable subadditivity over `(K, j) ∈ ℕ × ℕ`.
  exact measure_mono_null hcover (measure_iUnion_null fun K ↦ measure_iUnion_null (hnull K))
  -- Step 2: the denominators `D(s) = ω_n ofReal(s)^n` are finite, and nonzero for `s > 0`.
  have hD0 : ∀ s : ℝ, 0 < s → unitBallVolume n * ENNReal.ofReal s ^ n ≠ 0 := fun s hs ↦
    mul_ne_zero hω0 (pow_ne_zero n (ENNReal.ofReal_pos.2 hs).ne')
  have hDtop : ∀ s : ℝ, unitBallVolume n * ENNReal.ofReal s ^ n ≠ ∞ := fun s ↦
    ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- Step 3: for `s > 0`, `c ≤ densityRatio n μ z s ↔ c D(s) ≤ μ(B_s(z))`.
  have hiff : ∀ (z : Euclidean N) (s : ℝ), 0 < s → (c ≤ densityRatio n μ z s ↔
      c * (unitBallVolume n * ENNReal.ofReal s ^ n) ≤ μ (closedBall z s)) := fun z s hs ↦
    ENNReal.le_div_iff_mul_le (Or.inl (hD0 s hs)) (Or.inl (hDtop s))
  -- Step 4: it suffices to show `c D(ρ) ≤ μ(B_ρ(y))`.
  refine (hiff y ρ hρ).2 ?_
  -- Step 5: for `0 < s < ρ` pick `x ∈ E` with `|x - y| < ρ - s`; then `B_s(x) ⊆ B_ρ(y)`.
  have hbound : ∀ s ∈ Ioo 0 ρ,
      c * (unitBallVolume n * ENNReal.ofReal s ^ n) ≤ μ (closedBall y ρ) := by
    rintro s ⟨hs0, hsρ⟩
    obtain ⟨x, hx, hyx⟩ := Metric.mem_closure_iff.1 hy (ρ - s) (sub_pos.2 hsρ)
    calc c * (unitBallVolume n * ENNReal.ofReal s ^ n) ≤ μ (closedBall x s) :=
          (hiff x s hs0).1 (hE x hx s hs0 (hsρ.le.trans hρδ))
      _ ≤ μ (closedBall y ρ) :=
          measure_mono (Metric.closedBall_subset_closedBall' (by rw [dist_comm]; linarith))
  -- Step 6: let `s ↑ ρ`; `c D(s) → c D(ρ)` since `ω_n ≠ ∞` and `D(ρ) ≠ 0` (this covers `c = ∞`).
  have hlim : Tendsto (fun s : ℝ ↦ c * (unitBallVolume n * ENNReal.ofReal s ^ n)) (𝓝[<] ρ)
      (𝓝 (c * (unitBallVolume n * ENNReal.ofReal ρ ^ n))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
      ((((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal).tendsto ρ).mono_left
        nhdsWithin_le_nhds) (Or.inr hωtop)) (Or.inl (hD0 ρ hρ))
  exact le_of_tendsto hlim (mem_of_superset (Ioo_mem_nhdsLT hρ) hbound)
/-- `ω_n = π^{n/2} / Γ(n/2 + 1)` for every `n ∈ ℕ` (including `ω_0 = 1`): for `n = 0` the volume
of `EuclideanSpace ℝ (Fin 0)` is the Dirac mass at `0`, and for `n ≥ 1` this is
`EuclideanSpace.volume_ball` at radius `1` together with `√π ^ n = π ^ (n / 2)`. -/
theorem Submission.frt_hnw_unitBallVolume_eq_gamma :
    ∀ n : ℕ, unitBallVolume n = ENNReal.ofReal (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)) := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Step 1: the volume of `EuclideanSpace ℝ (Fin 0)` is `dirac 0`, so `ω_0 = 1 = π^0 / Γ(1)`.
    rw [unitBallVolume, volume_euclideanSpace_eq_dirac (Fin 0),
      Measure.dirac_apply_of_mem (mem_ball_self (x := (0 : EuclideanSpace ℝ (Fin 0))) one_pos)]
    simp
  · -- Step 2: the ball formula at centre `0` and radius `1`, with `card (Fin n) = n`.
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [unitBallVolume, EuclideanSpace.volume_ball (Fin n) 0 1, Fintype.card_fin,
      ENNReal.ofReal_one, one_pow, one_mul]
    -- Step 3: `√π ^ n = π ^ (n / 2)`.
    have hpow : Real.sqrt Real.pi ^ n = Real.pi ^ ((n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
      congr 1
      ring
    rw [hpow]
/-- Small open neighbourhoods of null sets (used for the First Rectifiability Theorem, Simon Ch. 8,
1.2): if `μ` is finite on compact subsets of the open set `U` and `Z ⊆ U` is `μ`-null, then for every
`ζ > 0` there is an open `O` with `Z ⊆ O ⊆ U` and `μ(O) < ζ`. -/
theorem Submission.frt_hnw_exists_open_superset_measure_lt :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (U Z : Set (Euclidean N)) (ζ : ℝ≥0∞), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → Z ⊆ U → μ Z = 0 → 0 < ζ → ∃ O : Set (Euclidean N), IsOpen O ∧ Z ⊆ O ∧ O ⊆ U ∧ μ O < ζ := by
  intro N μ U Z ζ hU hfin hZU hZ hζ
  -- Step 1: for each `x ∈ U` a radius `r x > 0` with `closedBall x (r x) ⊆ U`.
  have hrad : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose! r hr using hrad
  -- Steps 2–3: the balls `ball x (r x)`, `x ∈ U`, cover `U`; by Lindelöf, so do those with
  -- centres in a countable `T ⊆ U`.
  have hcover : ⋃ x ∈ U, ball x (r x) = U := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun x hx ↦ ball_subset_closedBall.trans (hr x hx).2
    · intro x hx
      exact mem_iUnion₂.mpr ⟨x, hx, mem_ball_self (hr x hx).1⟩
  obtain ⟨T, hTU, hTc, hTcover⟩ :=
    TopologicalSpace.isOpen_biUnion_countable U (fun x ↦ ball x (r x)) (fun _ _ ↦ isOpen_ball)
  rw [hcover] at hTcover
  have : Countable T := hTc.to_subtype
  -- Step 4: a budget `ε i > 0` with `∑' i, ε i < ζ`.
  obtain ⟨ε, hεpos, hεsum⟩ := ENNReal.exists_pos_sum_of_countable hζ.ne' T
  -- Step 5: outer regularity of the finite measure `μ.restrict (ball i (r i))` gives an open
  -- `O' i ⊇ Z` with `μ (O' i ∩ ball i (r i)) < ε i`.
  have hloc : ∀ i : T, ∃ O' : Set (Euclidean N), Z ⊆ O' ∧ IsOpen O' ∧
      μ (O' ∩ ball (i : Euclidean N) (r i)) < ε i := by
    intro i
    have hballfin : μ (ball (i : Euclidean N) (r i)) ≠ ∞ :=
      ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) (hr _ (hTU i.2)).2)
        (measure_mono ball_subset_closedBall)
    have : IsFiniteMeasure (μ.restrict (ball (i : Euclidean N) (r i))) :=
      isFiniteMeasure_restrict.mpr hballfin
    have hZν : μ.restrict (ball (i : Euclidean N) (r i)) Z < ε i := by
      rw [Measure.restrict_apply' measurableSet_ball]
      exact (measure_mono_null inter_subset_left hZ).trans_lt (by exact_mod_cast hεpos i)
    obtain ⟨O', hZO', hO'open, hO'⟩ := Set.exists_isOpen_lt_of_lt Z _ hZν
    refine ⟨O', hZO', hO'open, ?_⟩
    rwa [Measure.restrict_apply hO'open.measurableSet] at hO'
  choose O' hZO' hO'open hO' using hloc
  -- Step 6: glue `O = ⋃ i, O' i ∩ ball i (r i)`.
  refine ⟨⋃ i : T, O' i ∩ ball (i : Euclidean N) (r i), ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun i ↦ (hO'open i).inter isOpen_ball
  · intro z hz
    have hz' : z ∈ ⋃ x ∈ T, ball x (r x) := hTcover ▸ hZU hz
    obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp hz'
    exact mem_iUnion.mpr ⟨⟨x, hxT⟩, hZO' _ hz, hzx⟩
  · exact iUnion_subset fun i ↦ inter_subset_right.trans
      (ball_subset_closedBall.trans (hr _ (hTU i.2)).2)
  · calc μ (⋃ i : T, O' i ∩ ball (i : Euclidean N) (r i))
        ≤ ∑' i : T, μ (O' i ∩ ball (i : Euclidean N) (r i)) := measure_iUnion_le _
      _ ≤ ∑' i : T, (ε i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i ↦ (hO' i).le
      _ < ζ := hεsum
/-- Step (3b) in the proof of Simon Ch. 8, 1.2 (child `hausdorff_null_of_weight_null` of
`first_rectifiability`), via Simon Ch. 1, 3.3: let `U` be open and `μ` finite on compact subsets
of `U`.  If `Z ⊆ U` is `μ`-null and `limsup_{ρ↓0} μ(B_ρ(x)) / (ω_n ρ^n) > 0` at every `x ∈ Z`,
then `H^n(Z) = 0`.  For `Z_m = {x ∈ Z : limsup ≥ 1/m}`, Simon 3.3 gives `(1/m) H^n(Z_m) ≤ μ(O)`
for every open `O ⊇ Z_m`, and there are such `O` with `μ(O)` arbitrarily small. -/
theorem Submission.frt_hausdorff_null_of_weight_null :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (U Z : Set (Euclidean N)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → Z ⊆ U → μ Z = 0 → (∀ x ∈ Z, 0 < limsup (densityRatio n μ x) (𝓝[>] 0)) → μHE[n] Z = 0 := by
  intro N n μ U Z hU hfin hZU hZ hpos
  -- (a) `ω_n` is Simon's normalization `π^{n/2} / Γ(n/2 + 1)`, also for `n = 0`.
  have hω : unitBallVolume n = Chapter01.realUnitBallVolume (n : ℝ) := by
    rw [Chapter01.realUnitBallVolume_eq]
    exact Submission.frt_hnw_unitBallVolume_eq_gamma n
  -- (b) Borel sets are Carathéodory measurable for `μ`.
  have hcar : borel (Euclidean N) ≤ μ.toOuterMeasure.caratheodory := by
    rw [← BorelSpace.measurable_eq]
    exact le_toOuterMeasure_caratheodory μ
  -- (c) Simon 3.3: if `t ≤ limsup densityRatio` on `A ⊆ O` with `O` open, then
  -- `t H^n(A) ≤ μ(O)`, because `O ∩ B_ρ(x) = B_ρ(x)` for small `ρ`.
  have hcomp : ∀ (O A : Set (Euclidean N)) (t : ℝ≥0∞), IsOpen O → A ⊆ O →
      (∀ x ∈ A, t ≤ limsup (densityRatio n μ x) (𝓝[>] 0)) → t * μHE[n] A ≤ μ O := by
    intro O A t hO hAO hA
    have h := Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity μ.toOuterMeasure hcar
      (Nat.cast_nonneg n) A O t fun x hx ↦ by
        obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
        refine (hA x hx).trans_eq (limsup_congr ?_)
        filter_upwards [Ioo_mem_nhdsGT hR] with ρ hρ
        rw [Chapter01.dimensionalDensityQuotient, densityRatio, hω, ENNReal.rpow_natCast,
          inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hRO), Measure.toOuterMeasure_apply]
    rwa [← Chapter01.simonHausdorffMeasureReal_toOuterMeasure (Nat.cast_nonneg n),
      Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure] at h
  -- (d) For `t ≠ 0`, `Z_t = {x ∈ Z : t ≤ limsup densityRatio}` is `H^n`-null: otherwise an open
  -- `O ⊇ Z_t` with `μ(O) < t H^n(Z_t)` exists (`Z_t` is `μ`-null), contradicting (c).
  have hnull : ∀ t : ℝ≥0∞, t ≠ 0 →
      μHE[n] {x | x ∈ Z ∧ t ≤ limsup (densityRatio n μ x) (𝓝[>] 0)} = 0 := by
    intro t ht
    by_contra hH
    obtain ⟨O, hO, hZO, -, hμO⟩ := Submission.frt_hnw_exists_open_superset_measure_lt N μ U
      {x | x ∈ Z ∧ t ≤ limsup (densityRatio n μ x) (𝓝[>] 0)} _ hU hfin
      ((sep_subset _ _).trans hZU) (measure_mono_null (sep_subset _ _) hZ) (ENNReal.mul_pos ht hH)
    exact (hcomp O _ t hO hZO fun x hx ↦ hx.2).not_gt hμO
  -- (e) `Z ⊆ ⋃ m, Z_{1/m}`, as `limsup densityRatio > 0` exceeds some `1/m` at each `x ∈ Z`.
  refine measure_mono_null (fun x hx ↦ ?_)
    (measure_iUnion_null fun m : ℕ ↦ hnull _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m)))
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt (hpos x hx).ne'
  exact mem_iUnion.2 ⟨m, hx, hm.le⟩
/-- The carrier is `H^n`-measurable (Simon Ch. 8, 1.2, the printed claim "`M` is `H^n`-measurable",
which Ch. 3, 1.9 presupposes): if `M ⊆ U`, `μ_V(ℝ^N ∖ M) = 0` and `Θ^n(μ_V, x) = θ(x) > 0` for every
`x ∈ M`, then `M` is `H^n`-null-measurable.  `M` is the countable union of the sets
`M ∩ closure (F_{m,k} ∩ C_j)`, where `F_{m,k} ⊆ M` carries a uniform lower density bound and the
closed sets `C_j ⊆ U` cover `U`; each is a closed set minus an `H^n`-null set. -/
theorem Submission.frt_carrier_nullMeasurable :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), M ⊆ U → V.weight Mᶜ = 0 → (∀ x ∈ M, 0 < θ x ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) → NullMeasurableSet M μHE[n] := by
  intro N n U V M θ hMU hMc hθ
  -- Step 0: `U` is open and `μ_V` is finite on compact subsets of `U`.
  have hU : IsOpen U := V.isOpen_domain
  have hfin : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → V.weight K ≠ ∞ :=
    V.weight_finite_on_compact
  -- Step 1: the uniform pieces `F m k ⊆ M`, with `(2(m+1))⁻¹ ≤ densityRatio` on `(0, 1/(k+1)]`.
  set F : ℕ → ℕ → Set (Euclidean N) := fun m k ↦ {x | x ∈ M ∧ ∀ ρ : ℝ, 0 < ρ →
    ρ ≤ 1 / ((k : ℝ) + 1) → (2 * ((m : ℝ≥0∞) + 1))⁻¹ ≤ densityRatio n V.weight x ρ}
  -- Step 2: countably many closed sets `C j ⊆ U` cover `U`.
  obtain ⟨C, hCclosed, hCU, hCcover, -⟩ := hU.exists_iUnion_isClosed
  -- Steps 3–6: each `M ∩ closure (F m k ∩ C j)` is `H^n`-null-measurable.
  have hpiece : ∀ m k j, NullMeasurableSet (M ∩ closure (F m k ∩ C j)) μHE[n] := by
    intro m k j
    -- Step 3: the closure stays inside the closed set `C j ⊆ U`.
    have hclU : closure (F m k ∩ C j) ⊆ U :=
      (closure_minimal inter_subset_right (hCclosed j)).trans (hCU j)
    -- Step 4: the lower bound passes to the closure, so `limsup densityRatio > 0` there.
    have hc0 : (0 : ℝ≥0∞) < (2 * ((m : ℝ≥0∞) + 1))⁻¹ :=
      ENNReal.inv_pos.2 (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩))
    have hlim : ∀ y ∈ closure (F m k ∩ C j), 0 < limsup (densityRatio n V.weight y) (𝓝[>] 0) := by
      intro y hy
      have hlow := Submission.frt_cnm_densityRatio_lower_closure N n V.weight (F m k ∩ C j) _ _
        (fun x hx ↦ hx.1.2) y hy
      refine hc0.trans_le (le_limsup_of_frequently_le (Eventually.frequently ?_))
      filter_upwards [Ioo_mem_nhdsGT (Nat.one_div_pos_of_nat (n := k))] with ρ hρ
      exact hlow ρ hρ.1 hρ.2.le
    -- Step 5: the defect `closure (F m k ∩ C j) ∖ M` is `μ_V`-null, hence `H^n`-null.
    have hZ : μHE[n] (closure (F m k ∩ C j) \ M) = 0 :=
      Submission.frt_hausdorff_null_of_weight_null N n V.weight U _ hU hfin
        (sdiff_subset.trans hclU) (measure_mono_null (fun x hx ↦ hx.2) hMc)
        (fun y hy ↦ hlim y hy.1)
    -- Step 6: `M ∩ closure (F m k ∩ C j)` is a closed set minus an `H^n`-null set.
    rw [inter_comm, ← Set.sdiff_sdiff_right_self]
    exact isClosed_closure.measurableSet.nullMeasurableSet.diff (NullMeasurableSet.of_null hZ)
  -- Step 7: `M` is the countable union of these pieces.
  have hcover : M = ⋃ m, ⋃ k, ⋃ j, M ∩ closure (F m k ∩ C j) := by
    refine Subset.antisymm (fun x hx ↦ ?_)
      (iUnion_subset fun m ↦ iUnion_subset fun k ↦ iUnion_subset fun j ↦ inter_subset_left)
    obtain ⟨m, k, hmk⟩ := Submission.frt_cnm_exists_uniform_densityRatio_lower N n V.weight x _
      (ENNReal.ofReal_pos.2 (hθ x hx).1) (hθ x hx).2
    have hxC : x ∈ ⋃ j, C j := by
      rw [hCcover]
      exact hMU hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hxC
    exact mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨j, hx, subset_closure ⟨⟨hx, hmk⟩, hj⟩⟩⟩⟩
  rw [hcover]
  exact NullMeasurableSet.iUnion fun m ↦ NullMeasurableSet.iUnion fun k ↦
    NullMeasurableSet.iUnion fun j ↦ hpiece m k j

/-- Simon Ch. 8, 1.2, Step 6 (`μ_V = H^n ⌞ θ`): if `μ_V(ℝ^N ∖ M) = 0`, `M ⊆ U`, `μ_V` has density
`θ(x) ∈ (0, ∞)` at every `x ∈ M`, and for every `L ∈ (0, 1]` `M` is covered by countably many closed
`L`-graphs over `n`-planes, then `θ` is `H^n`-integrable on `M ∩ K` for every compact `K ⊆ U` and
`μ_V(B) = ∫_{B ∩ M} θ dH^n` for every `μ_V`-null-measurable `B`. -/
theorem Submission.frt_weight_eq_multiplicity_hausdorff :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), M ⊆ U → V.weight Mᶜ = 0 → (∀ x ∈ M, 0 < θ x ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) → (∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ M ⊆ ⋃ c ∈ C, c.2) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μHE[n]) ∧ ∀ B : Set (Euclidean N), NullMeasurableSet B V.weight → V.weight B = ∫⁻ x in B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n] := by
  intro N n U V M θ hMU hMc hθ hcov
  -- Step 0: `U` is open, `μ_V` is finite on compact subsets of `U`, `M` is `H^n`-null-measurable.
  have hU : IsOpen U := V.isOpen_domain
  have hfin : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → V.weight K ≠ ∞ :=
    V.weight_finite_on_compact
  have hMnm : NullMeasurableSet M μHE[n] :=
    Submission.frt_carrier_nullMeasurable N n U V M θ hMU hMc hθ
  -- Step 1: a Borel `g` with `g = ofReal ∘ θ` on `M`.
  obtain ⟨g, hgm, hg⟩ := Submission.frt_weq_density_borel_representative N n V.weight
  have hgθ : ∀ x ∈ M, g x = ENNReal.ofReal (θ x) := fun x hx ↦ hg x _ (hθ x hx).2
  -- Step 2: `μ_V` and `H^n` have the same null subsets of `M`.
  have hnullH : ∀ Z ⊆ M, V.weight Z = 0 → μHE[n] Z = 0 := fun Z hZ hZ0 ↦
    Submission.frt_hausdorff_null_of_weight_null N n V.weight U Z hU hfin (hZ.trans hMU) hZ0
      fun x hx ↦ by
        rw [Filter.Tendsto.limsup_eq (hθ x (hZ hx)).2]
        exact ENNReal.ofReal_pos.2 (hθ x (hZ hx)).1
  have hnullV : ∀ Z ⊆ M, μHE[n] Z = 0 → V.weight Z = 0 := fun Z hZ hZ0 ↦
    Submission.frt_weight_null_of_hausdorff_null N n V.weight Z hZ0 fun x hx ↦
      ⟨ENNReal.ofReal (θ x), ENNReal.ofReal_ne_top, (hθ x (hZ hx)).2⟩
  -- Step 3: the pieces `A p = {x ∈ M : θ x ≥ 1/(p+1)} ∩ K p` increase to `M`.
  obtain ⟨K, hKc, hKU, hKint, hKmono, hKunion⟩ :=
    Submission.frt_weq_open_compact_exhaustion N U hU
  let t : ℕ → ℝ≥0∞ := fun p ↦ ((p + 1 : ℕ) : ℝ≥0∞)⁻¹
  have ht0 : ∀ p, t p ≠ 0 := fun p ↦ ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  let A : ℕ → Set (Euclidean N) := fun p ↦ M ∩ ({x | t p ≤ g x} ∩ K p)
  have hAM : ∀ p, A p ⊆ M := fun p ↦ inter_subset_left
  have hAmono : Monotone A := fun p q hpq x hx ↦
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 (Nat.cast_le.2 (Nat.add_le_add_right hpq 1))) hx.2.1,
      hKmono hpq hx.2.2⟩
  have hAunion : ⋃ p, A p = M := by
    refine Subset.antisymm (iUnion_subset hAM) fun x hx ↦ ?_
    have hxK : x ∈ ⋃ p, K p := by rw [hKunion]; exact hMU hx
    obtain ⟨q, hq⟩ := mem_iUnion.1 hxK
    have hgx : g x ≠ 0 := by
      rw [hgθ x hx]
      exact (ENNReal.ofReal_pos.2 (hθ x hx).1).ne'
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hgx
    refine mem_iUnion.2 ⟨max m q, hx, ?_, hKmono (le_max_right m q) hq⟩
    exact le_trans (ENNReal.inv_le_inv.2 (Nat.cast_le.2 ((le_max_left m q).trans
      (Nat.le_succ _)))) hm.le
  have hAnm : ∀ p, NullMeasurableSet (A p) μHE[n] := fun p ↦
    hMnm.inter ((measurableSet_le measurable_const hgm).inter
      (hKc p).isClosed.measurableSet).nullMeasurableSet
  -- Step 4: `H^n (A p) < ∞`, by the upper-density bound on `W = interior (K (p + 1))`.
  have hWfin : ∀ p, V.weight (interior (K (p + 1))) ≠ ∞ := fun p ↦
    ne_top_of_le_ne_top (hfin _ (hKc _) (hKU _)) (measure_mono interior_subset)
  have hAW : ∀ p, A p ⊆ interior (K (p + 1)) := fun p ↦
    (inter_subset_right.trans inter_subset_right).trans (hKint p)
  have hAfin : ∀ p, μHE[n] (A p) ≠ ∞ := by
    intro p hp
    have hle := Submission.frt_weq_mul_hausdorff_le_of_upper_density N n V.weight
      (interior (K (p + 1))) (A p) (t p) isOpen_interior (hAW p) fun x hx ↦ by
        rw [Filter.Tendsto.limsup_eq (hθ x (hAM p hx)).2, ← hgθ x (hAM p hx)]
        exact hx.2.1
    rw [hp, ENNReal.mul_top (ht0 p)] at hle
    exact hWfin p (top_le_iff.1 hle)
  -- Step 5: `H^n ⌞ A p` has density one almost everywhere.
  have hdens : ∀ p, ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)).restrict (A p),
      HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict (A p)) x 1 := fun p ↦
    Submission.frt_hausdorff_density_one_of_flat_covers N n (A p) (hAfin p) (hAnm p)
      fun L hL0 hL1 ↦ by
        obtain ⟨C, hCc, hCg, hMC⟩ := hcov L hL0 hL1
        exact ⟨C, hCc, hCg, (hAM p).trans hMC⟩
  -- Steps 6–8: `μ_V (B ∩ A p) = ∫_{B ∩ A p} θ dH^n` for Borel `B`.
  have hpiece : ∀ p, ∀ B : Set (Euclidean N), MeasurableSet B →
      V.weight (B ∩ A p) = ∫⁻ x in B ∩ A p, ENNReal.ofReal (θ x) ∂μHE[n] := fun p ↦
    Submission.frt_weq_piece_restrict_eq_density N n V.weight (interior (K (p + 1))) (A p) θ
      isOpen_interior (hWfin p) (hAW p) (hAfin p) (hAnm p) (fun x hx ↦ hθ x (hAM p hx))
      (fun Z hZ hZ0 ↦ hnullV Z (hZ.trans (hAM p)) hZ0)
      (fun Z hZ hZ0 ↦ hnullH Z (hZ.trans (hAM p)) hZ0) (hdens p)
  -- Step 9: Borel `B`, letting `p → ∞` (no measurability of the pieces is needed).
  have hBorel : ∀ B : Set (Euclidean N), MeasurableSet B →
      V.weight B = ∫⁻ x in B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n] := by
    intro B hB
    have hmonoB : Monotone fun p ↦ B ∩ A p := fun p q hpq ↦
      inter_subset_inter_right B (hAmono hpq)
    have hdir : Directed (· ⊆ ·) fun p ↦ B ∩ A p := hmonoB.directed_le
    have hBM : B ∩ M = ⋃ p, B ∩ A p := by rw [← inter_iUnion, hAunion]
    calc V.weight B = V.weight (B ∩ M) := (measure_inter_conull hMc).symm
      _ = ⨆ p, V.weight (B ∩ A p) := by rw [hBM, hdir.measure_iUnion]
      _ = ⨆ p, ∫⁻ x in B ∩ A p, ENNReal.ofReal (θ x) ∂μHE[n] :=
        iSup_congr fun p ↦ hpiece p B hB
      _ = ∫⁻ x in B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n] := by
        rw [hBM, setLIntegral_iUnion_of_directed (fun x ↦ ENNReal.ofReal (θ x)) hdir]
  refine ⟨fun K' hK' hK'U ↦ ?_, fun B hB ↦ ?_⟩
  · -- Step 11: `θ` is integrable on `M ∩ K'`, since `∫_{K' ∩ M} θ dH^n = μ_V(K') < ∞`.
    have hnm : NullMeasurableSet (M ∩ K') μHE[n] :=
      hMnm.inter hK'.isClosed.measurableSet.nullMeasurableSet
    have hae : g =ᵐ[(μHE[n] : Measure (Euclidean N)).restrict (M ∩ K')]
        fun x ↦ ENNReal.ofReal (θ x) := by
      filter_upwards [ae_restrict_mem₀ hnm] with x hx using hgθ x hx.1
    have hlin : ∫⁻ x in M ∩ K', ENNReal.ofReal (θ x) ∂μHE[n] ≠ ∞ := by
      rw [inter_comm, ← hBorel K' hK'.isClosed.measurableSet]
      exact hfin K' hK' hK'U
    refine (integrable_toReal_of_lintegral_ne_top (hgm.aemeasurable.congr hae) hlin).congr ?_
    filter_upwards [ae_restrict_mem₀ hnm] with x hx using ENNReal.toReal_ofReal (hθ x hx.1).1.le
  · -- Step 10: `μ_V`-null-measurable `B`, through a measurable hull.
    have hBB : B ⊆ toMeasurable V.weight B := subset_toMeasurable _ _
    have hdiff : V.weight (toMeasurable V.weight B \ B) = 0 :=
      (ae_eq_set.1 hB.toMeasurable_ae_eq).1
    have hae : B ∩ M =ᵐ[(μHE[n] : Measure (Euclidean N))] toMeasurable V.weight B ∩ M := by
      refine ae_eq_set.2 ⟨?_, ?_⟩
      · rw [Set.sdiff_eq_empty.2 (inter_subset_inter_left M hBB), measure_empty]
      · refine hnullH _ (fun x hx ↦ hx.1.2) (measure_mono_null ?_ hdiff)
        exact fun x hx ↦ ⟨hx.1.1, fun h ↦ hx.2 ⟨h, hx.1.2⟩⟩
    calc V.weight B = V.weight (toMeasurable V.weight B) := (measure_toMeasurable B).symm
      _ = ∫⁻ x in toMeasurable V.weight B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n] :=
        hBorel _ (measurableSet_toMeasurable _ _)
      _ = ∫⁻ x in B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n] := (setLIntegral_congr hae).symm

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
