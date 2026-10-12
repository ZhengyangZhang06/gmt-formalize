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

/-- The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane
`T ∈ G(N,n)` is `ω_n r^n` (Simon Ch. 3, Remark 1.8(2); step 3 of the tangent-plane density proof
for Simon Ch. 8, 1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric
parametrization of `T`. -/
theorem Submission.frt_td_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: orthonormal coordinates `e : ℝ^n ≃ₗᵢ T.plane`, since `finrank T.plane = n`.
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] T.plane :=
    ((stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)).repr.symm
  -- Step 2: the isometric embedding `ι : ℝ^n → ℝ^N`, `ι v = e v`.
  let ι : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp e.toLinearIsometry
  -- Step 3: `ι '' B_r(0) = T.plane ∩ B_r(0)`.
  have himage : ι '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(e v).2, ?_⟩
      rw [mem_closedBall_zero_iff] at hv ⊢
      rwa [ι.norm_map]
    · rintro ⟨hy, hyr⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff] at hyr ⊢
        rwa [e.symm.norm_map]
      · change ((e (e.symm ⟨y, hy⟩) : T.plane) : Euclidean N) = y
        rw [e.apply_symm_apply]
  -- Steps 4–5: `H^n` is invariant under the isometry `ι`, and `H^n = vol` on `ℝ^n`.
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Steps 6–7: Haar scaling `vol (B_r(0)) = r^n vol (B°_1(0))` (`r ≥ 0`; no `0 < n` needed).
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr,
    unitBallVolume, mul_comm]

/-- Lower ball-mass bound from weight blow-ups (Simon Ch. 3, Remark 1.8(2), lower cutoff): if
`t^{-n} ∫ g(t^{-1}(z - x)) dμ(z) → θ ∫_T g dH^n` as `t ↓ 0` for every `g ∈ C_c(ℝ^N)`, then for
every `c < θ ω_n` we have `c t^n ≤ μ(B_t(x))` for all small `t > 0`. -/
theorem Submission.frt_td_ball_mass_lower_of_blowup :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), 0 < θ → (∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) → ∀ c : ℝ≥0∞, c < ENNReal.ofReal θ * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t) := by
  intro N n μ x T θ hθ hblow c hc
  -- Steps 1–2: `ω_n < ∞`, hence `c < ∞` and `c.toReal < θ ω_n`.
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcθ : c.toReal < θ * (unitBallVolume n).toReal := by
    have h := (ENNReal.toReal_lt_toReal hc_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 3: choose `κ ∈ (0, 1)` with `c.toReal < θ ω_n κ^n`, by continuity of `κ ↦ κ^n` at `1`.
  have hlim : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    have h := ((continuous_pow n).tendsto (1 : ℝ)).const_mul (θ * (unitBallVolume n).toReal)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hκ01 : ∀ᶠ κ in 𝓝[<] (1 : ℝ), κ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨κ, hκc, hκ0, hκ1⟩ := ((hlim.eventually (lt_mem_nhds hcθ)).and hκ01).exists
  have h1κ : 0 < 1 - κ := sub_pos.2 hκ1
  -- Step 4: the cutoff `χ(y) = max(0, min(1, (1 - ‖y‖)/(1 - κ)))`.
  let χ : Euclidean N → ℝ := fun y ↦ max 0 (min 1 ((1 - ‖y‖) / (1 - κ)))
  have hχ_zero : ∀ y : Euclidean N, 1 ≤ ‖y‖ → χ y = 0 := fun y hy ↦ by
    have h : (1 - ‖y‖) / (1 - κ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h1κ.le
    simp only [χ]
    rw [min_eq_right (h.trans zero_le_one), max_eq_left h]
  have hχ_one : ∀ y : Euclidean N, ‖y‖ ≤ κ → χ y = 1 := fun y hy ↦ by
    have h : 1 ≤ (1 - ‖y‖) / (1 - κ) := (one_le_div h1κ).2 (by linarith)
    simp only [χ]
    rw [min_eq_left h, max_eq_right zero_le_one]
  let g : C_c(Euclidean N, ℝ) :=
    ⟨⟨χ, by fun_prop⟩, HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) 1)
      fun y hy ↦ hχ_zero y (not_le.1 fun h ↦ hy (mem_closedBall_zero_iff.2 h)).le⟩
  have hg_nonneg : ∀ y, 0 ≤ g y := fun _ ↦ le_max_left _ _
  have hg_le : ∀ y, g y ≤ 1 := fun _ ↦ max_le zero_le_one (min_le_left _ _)
  -- Step 5: plane side, `ω_n κ^n ≤ ∫_T g dH^n`.
  set ν : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hνB : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n :=
    fun r hr ↦ by
      rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact Submission.frt_td_plane_closedBall_hausdorff N n T r hr
  have hν1 : ν (closedBall 0 1) ≠ ∞ := by
    rw [hνB 1 zero_le_one]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hg_int : Integrable (fun y ↦ g y) ν := by
    refine ((integrableOn_const (C := (1 : ℝ)) hν1).integrable_indicator
      measurableSet_closedBall).mono' (map_continuous g).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg y)]
    by_cases hy : y ∈ closedBall (0 : Euclidean N) 1
    · rw [indicator_of_mem hy]
      exact hg_le y
    · rw [indicator_of_notMem hy]
      exact (hχ_zero y (not_le.1 fun h ↦ hy (mem_closedBall_zero_iff.2 h)).le).le
  have hplane : (unitBallVolume n).toReal * κ ^ n ≤ ∫ y, g y ∂ν := by
    have hle : ∀ y, (closedBall (0 : Euclidean N) κ).indicator 1 y ≤ g y := fun y ↦ by
      by_cases hy : y ∈ closedBall (0 : Euclidean N) κ
      · rw [indicator_of_mem hy, Pi.one_apply]
        exact (hχ_one y (mem_closedBall_zero_iff.1 hy)).ge
      · rw [indicator_of_notMem hy]
        exact hg_nonneg y
    have h := integral_mono_of_nonneg (f := (closedBall (0 : Euclidean N) κ).indicator 1)
      (Eventually.of_forall (indicator_nonneg fun _ _ ↦ zero_le_one)) hg_int
      (Eventually.of_forall hle)
    rwa [integral_indicator_one measurableSet_closedBall, measureReal_def,
      hνB κ hκ0.le, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hκ0.le] at h
  -- Step 6: the blow-up limit `θ ∫_T g dH^n` exceeds `c.toReal`.
  have hlt : c.toReal < θ * ∫ y, g y ∂ν :=
    calc c.toReal < θ * (unitBallVolume n).toReal * κ ^ n := hκc
      _ = θ * ((unitBallVolume n).toReal * κ ^ n) := mul_assoc _ _ _
      _ ≤ θ * ∫ y, g y ∂ν := mul_le_mul_of_nonneg_left hplane hθ.le
  filter_upwards [(hblow g).eventually (lt_mem_nhds hlt), self_mem_nhdsWithin] with t ht ht0
  have ht0 : 0 < t := ht0
  -- Step 7: comparison with the ball mass.
  rcases eq_or_ne (μ (closedBall x t)) ∞ with hμt | hμt
  · rw [hμt]
    exact le_top
  have hcmp : ∫ z, g (t⁻¹ • (z - x)) ∂μ ≤ μ.real (closedBall x t) := by
    rw [← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ hg_nonneg _)
      ((integrableOn_const (C := (1 : ℝ)) hμt).integrable_indicator measurableSet_closedBall)
      (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ closedBall x t
    · rw [indicator_of_mem hz]
      exact hg_le _
    · rw [indicator_of_notMem hz]
      refine (hχ_zero _ ?_).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0), one_le_inv_mul₀ ht0,
        ← dist_eq_norm]
      exact (not_le.1 fun h ↦ hz (mem_closedBall.2 h)).le
  -- Step 8: conclusion.
  have hfin : c.toReal * t ^ n < μ.real (closedBall x t) := by
    have htn : t⁻¹ ^ n * t ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ ht0.ne', one_pow]
    calc c.toReal * t ^ n < (t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) * t ^ n :=
          mul_lt_mul_of_pos_right ht (pow_pos ht0 n)
      _ = ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
          rw [mul_comm, ← mul_assoc, mul_comm (t ^ n), htn, one_mul]
      _ ≤ μ.real (closedBall x t) := hcmp
  calc c * ENNReal.ofReal t ^ n = ENNReal.ofReal (c.toReal * t ^ n) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_pow ht0.le,
          ENNReal.ofReal_toReal hc_top]
    _ ≤ ENNReal.ofReal (μ.real (closedBall x t)) := ENNReal.ofReal_le_ofReal hfin.le
    _ = μ (closedBall x t) := ofReal_measureReal hμt
/-- Upper ball-mass bound from the blow-up limit (Simon Ch. 8, 1.2, Steps 2, 4 and 6; the upper
cutoff of Simon Ch. 3, Remark 1.8(2)): if `t⁻ⁿ ∫ g(t⁻¹(z - x)) dμ(z) → θ ∫_T g dHⁿ` for every
`g ∈ C_c(ℝ^N)` and `μ(B_{r₀}(x)) < ∞`, then `μ(B_t(x)) ≤ c tⁿ` for all small `t > 0` whenever
`θ ωₙ < c`.  The test function is a cutoff equal to `1` on `B_1(0)` and to `0` off `B_κ(0)`,
with `κ > 1` chosen so that `θ ωₙ κⁿ < c`. -/
theorem Submission.frt_td_ball_mass_upper_of_blowup :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (T : Grassmannian N n) (θ r₀ : ℝ), 0 < θ → 0 < r₀ → μ (closedBall x r₀) ≠ ⊤ → (∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) → ∀ c : ℝ≥0∞, ENNReal.ofReal θ * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n := by
  intro N n μ x T θ r₀ hθ hr₀ hμr₀ hblow c hc
  -- Step 1: `ωₙ < ∞`.
  have hωtop : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin n)))).ne
  -- Step 2: the case `c = ∞` is trivial.
  rcases eq_or_ne c ∞ with rfl | hctop
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [ENNReal.top_mul (pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne')]
    exact le_top
  -- Step 3: `θ ωₙ < c` in `ℝ`.
  have hθω : θ * (unitBallVolume n).toReal < c.toReal := by
    have h := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop) hctop).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 4: choose `κ > 1` with `θ ωₙ κⁿ < c`, by continuity of `κ ↦ θ ωₙ κⁿ` at `κ = 1`.
  obtain ⟨κ, hκc, hκ1⟩ : ∃ κ : ℝ, θ * (unitBallVolume n).toReal * κ ^ n < c.toReal ∧ 1 < κ := by
    have hcont : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[>] 1)
        (𝓝 (θ * (unitBallVolume n).toReal * 1 ^ n)) :=
      (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
    rw [one_pow, mul_one] at hcont
    exact ((hcont.eventually (gt_mem_nhds hθω)).and self_mem_nhdsWithin).exists
  have hκ0 : 0 < κ := zero_lt_one.trans hκ1
  -- Step 5: the cutoff `g(y) = max 0 (min 1 ((κ - ‖y‖)/(κ - 1)))`: `0 ≤ g ≤ 1`, `g = 1` on
  -- `B_1(0)` and `g = 0` off `B°_κ(0)`, so `g ∈ C_c(ℝ^N)`.
  obtain ⟨χ, hχ⟩ : ∃ χ : Euclidean N → ℝ, χ = fun y ↦ max 0 (min 1 ((κ - ‖y‖) / (κ - 1))) :=
    ⟨_, rfl⟩
  have hχcont : Continuous χ := by
    rw [hχ]
    fun_prop
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ by
    rw [hχ]
    exact le_max_left _ _
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ by
    rw [hχ]
    exact max_le zero_le_one (min_le_left _ _)
  have hχ_one : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦ by
    have h : 1 ≤ (κ - ‖y‖) / (κ - 1) := by
      rw [le_div_iff₀ (sub_pos.2 hκ1)]
      linarith
    simp only [hχ, min_eq_left h, max_eq_right zero_le_one]
  have hχ_zero : ∀ y, κ ≤ ‖y‖ → χ y = 0 := fun y hy ↦ by
    have h : (κ - ‖y‖) / (κ - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [hχ]
    exact max_eq_left ((min_le_right _ _).trans h)
  have hχsupp : HasCompactSupport χ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) κ) fun y hy ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact hχ_zero y hy.le
  let g : C_c(Euclidean N, ℝ) := ⟨⟨χ, hχcont⟩, hχsupp⟩
  have hg0 : ∀ y, 0 ≤ g y := hχ0
  have hg1 : ∀ y, g y ≤ 1 := hχ1
  have hg_one : ∀ y, ‖y‖ ≤ 1 → g y = 1 := hχ_one
  have hg_zero : ∀ y, κ ≤ ‖y‖ → g y = 0 := hχ_zero
  -- Step 6: `∫_T g dHⁿ ≤ Hⁿ(T ∩ B_κ(0)) = ωₙ κⁿ`, by the sibling plane-ball formula.
  have hνball : ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)))
      (closedBall 0 κ) = unitBallVolume n * ENNReal.ofReal κ ^ n := by
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.frt_td_plane_closedBall_hausdorff N n T κ hκ0.le
  have hplane : ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] ≤
      (unitBallVolume n).toReal * κ ^ n := by
    have hind : Integrable ((closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ))
        ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))) := by
      refine (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const ?_)
      rw [hνball]
      exact ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    calc ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]
        ≤ ∫ y in (T.plane : Set (Euclidean N)),
            (closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ) y ∂μHE[n] := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y ↦ hg0 y) hind
            (Eventually.of_forall fun y ↦ ?_)
          by_cases hy : y ∈ closedBall (0 : Euclidean N) κ
          · rw [indicator_of_mem hy, Pi.one_apply]
            exact hg1 y
          · have hκy : κ ≤ ‖y‖ := by
              rw [mem_closedBall_zero_iff, not_le] at hy
              exact hy.le
            rw [indicator_of_notMem hy, hg_zero y hκy]
      _ = ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))).real
            (closedBall 0 κ) := integral_indicator_one measurableSet_closedBall
      _ = (unitBallVolume n).toReal * κ ^ n := by
          rw [measureReal_def, hνball, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal hκ0.le]
  -- Step 7: eventually `t⁻ⁿ ∫ g(t⁻¹(z - x)) dμ < c` and `t ∈ (0, r₀/κ)`.
  have hlim : θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] < c.toReal :=
    (mul_le_mul_of_nonneg_left hplane hθ.le).trans_lt (by rwa [← mul_assoc])
  filter_upwards [(hblow g).eventually (gt_mem_nhds hlim), Ioo_mem_nhdsGT (div_pos hr₀ hκ0)]
    with t hlt ⟨ht0, htr⟩
  -- Step 8: `B_t(x) ⊆ B_{κt}(x) ⊆ B_{r₀}(x)` have finite mass.
  have hκt : κ * t ≤ r₀ := by
    rw [lt_div_iff₀ hκ0] at htr
    linarith
  have hfinκt : μ (closedBall x (κ * t)) ≠ ∞ :=
    ne_top_of_le_ne_top hμr₀ (measure_mono (closedBall_subset_closedBall hκt))
  have hfint : μ (closedBall x t) ≠ ∞ :=
    ne_top_of_le_ne_top hfinκt
      (measure_mono (closedBall_subset_closedBall (le_mul_of_one_le_left ht0.le hκ1.le)))
  -- Step 9: `z ↦ g(t⁻¹(z - x))` is `μ`-integrable, being bounded by `1_{B_{κt}(x)}`.
  have hnorm : ∀ z, ‖t⁻¹ • (z - x)‖ = ‖z - x‖ / t := fun z ↦ by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_eq_div]
  have hint : Integrable (fun z ↦ g (t⁻¹ • (z - x))) μ := by
    have hind : Integrable ((closedBall x (κ * t)).indicator (1 : Euclidean N → ℝ)) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfinκt)
    refine hind.mono' ((map_continuous g).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_of_nonneg (hg0 _)]
    by_cases hz : z ∈ closedBall x (κ * t)
    · rw [indicator_of_mem hz, Pi.one_apply]
      exact hg1 _
    · have hκz : κ ≤ ‖t⁻¹ • (z - x)‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [hnorm, le_div_iff₀ ht0]
        exact hz.le
      rw [indicator_of_notMem hz, hg_zero _ hκz]
  -- Step 10: `μ(B_t(x)) ≤ ∫ g(t⁻¹(z - x)) dμ`, as `1_{B_t(x)} ≤ g(t⁻¹(· - x))`.
  have hcmp : μ.real (closedBall x t) ≤ ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
    rw [← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ ?_) hint
      (Eventually.of_forall fun z ↦ ?_)
    · exact indicator_nonneg (fun _ _ ↦ zero_le_one) z
    · dsimp only
      by_cases hz : z ∈ closedBall x t
      · have hle : ‖t⁻¹ • (z - x)‖ ≤ 1 := by
          rw [hnorm, div_le_one ht0, ← dist_eq_norm]
          exact hz
        rw [indicator_of_mem hz, Pi.one_apply, hg_one _ hle]
      · rw [indicator_of_notMem hz]
        exact hg0 _
  -- Step 11: `μ(B_t(x)) ≤ c.toReal tⁿ`, and back to `ℝ≥0∞` using `μ(B_t(x)) < ∞`.
  have hreal : μ.real (closedBall x t) ≤ c.toReal * t ^ n := by
    have heq : (t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) * t ^ n = ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ ht0.ne', one_pow, one_mul]
    rw [← heq] at hcmp
    exact hcmp.trans (mul_le_mul_of_nonneg_right hlt.le (pow_nonneg ht0.le n))
  calc μ (closedBall x t) = ENNReal.ofReal (μ.real (closedBall x t)) :=
        (ENNReal.ofReal_toReal hfint).symm
    _ ≤ ENNReal.ofReal (c.toReal * t ^ n) := ENNReal.ofReal_le_ofReal hreal
    _ = c * ENNReal.ofReal t ^ n := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hctop,
          ENNReal.ofReal_pow ht0.le]
/-- Density squeeze (Simon Ch. 3, Remark 1.8(2), last step): if, as `t ↓ 0`, eventually
`c t^n ≤ μ(B_t(x))` for every `c < a ω_n` and eventually `μ(B_t(x)) ≤ c t^n` for every
`c > a ω_n`, then `Θ^n(μ, x) = a`. -/
theorem Submission.frt_td_hasDensity_of_ball_mass_bounds :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (a : ℝ≥0∞), (∀ c : ℝ≥0∞, c < a * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) → (∀ c : ℝ≥0∞, a * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n) → HasDensity n μ x a := by
  intro N n μ x a hlow hup
  -- Step 1: `0 < ω_n < ∞`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (x := 0)
      (r := 1)).ne
  -- Step 3: by `tendsto_order`, squeeze the density ratio from below and from above.
  rw [HasDensity, tendsto_order]
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- Step 4: for `b < b' < a`, eventually `b' ω_n t^n ≤ μ(B_t(x))`, so `b' ≤ densityRatio`.
    obtain ⟨b', hbb', hb'a⟩ := exists_between hb
    filter_upwards [hlow _ (ENNReal.mul_lt_mul_left hω0 hωt hb'a), self_mem_nhdsWithin]
      with t ht (htpos : (0 : ℝ) < t)
    -- Step 2: for `t > 0` the normalizer `ω_n t^n` is nonzero and finite.
    have hD0 : unitBallVolume n * ENNReal.ofReal t ^ n ≠ 0 :=
      mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 htpos).ne')
    have hDt : unitBallVolume n * ENNReal.ofReal t ^ n ≠ ∞ :=
      ENNReal.mul_ne_top hωt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    refine hbb'.trans_le ?_
    rw [densityRatio, ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDt), ← mul_assoc]
    exact ht
  · -- Step 5: for `a < b' < b`, eventually `μ(B_t(x)) ≤ b' ω_n t^n`, so `densityRatio ≤ b'`.
    obtain ⟨b', hab', hb'b⟩ := exists_between hb
    filter_upwards [hup _ (ENNReal.mul_lt_mul_left hω0 hωt hab')] with t ht
    exact (ENNReal.div_le_of_le_mul (by rwa [← mul_assoc])).trans_lt hb'b
/-- Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(y,S) = g(y)`):
if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`,
`t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` as `t ↓ 0`. -/
theorem Submission.frt_weight_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂V.weight) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n])) := by
  intro N n U V x T θ hT g
  -- Step 1: the test function `f(y, S) = g(y)` is compactly supported, `G(N,n)` being compact.
  have hf : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1) :=
    HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) fun z hz ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨h, mem_univ _⟩
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    ⟨⟨fun z ↦ g z.1, (map_continuous g).comp continuous_fst⟩, hf⟩
  have hfc : Continuous (f : Euclidean N × Grassmannian N n → ℝ) := map_continuous f
  -- Step 2: the convergence clause of Definition 1.1 applied to `f`.
  have hlim := hT.2.2 f
  -- Step 3: plane side, `∫ f dv(T) = ∫_T g dH^n`.
  have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
      ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] := by
    rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T)) (by fun_prop)
      hfc.aestronglyMeasurable]
    rfl
  rw [hplane] at hlim
  -- Steps 4–5: for `t > 0`, `∫ f dV_{x,t} = t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z)`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (le_of_lt ht)) n
  have hg : Continuous fun y : Euclidean N ↦ g (t⁻¹ • (y - x)) := by fun_prop
  rw [rescaledMeasure, integral_smul_measure,
    integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2))
      (by fun_prop) hfc.aestronglyMeasurable, ENNReal.toReal_ofReal ht', smul_eq_mul,
    Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  rfl
/-- Density at a tangent point (Simon Ch. 8, 1.2, step (0c); Ch. 3, Remark 1.8(2)): if `V` has
tangent plane `T` with multiplicity `θ` at `x`, then `Θ^n(μ_V, x) = θ`, i.e.
`μ_V(B_t(x)) / (ω_n t^n) → θ` as `t ↓ 0`. -/
theorem Submission.frt_tangent_plane_hasDensity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → HasDensity n V.weight x (ENNReal.ofReal θ) := by
  intro N n U V x T θ hT
  -- Step 1: `x ∈ U` and `θ > 0`; as `U` is open, some `B_{r₀}(x) ⊆ U` has finite `μ_V`-mass.
  have hθ : 0 < θ := hT.2.1
  obtain ⟨r₀, hr₀, hr₀U⟩ := nhds_basis_closedBall.mem_iff.1 (V.isOpen_domain.mem_nhds hT.1)
  have hμr₀ : V.weight (closedBall x r₀) ≠ ⊤ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x r₀) hr₀U
  -- Step 2: `t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` for every `g ∈ C_c(ℝ^N)`.
  have hblow := Submission.frt_weight_blowup_tendsto N n U V x T θ hT
  -- Steps 3–4: `c t^n ≤ μ_V(B_t(x))` eventually for `c < θ ω_n` and `μ_V(B_t(x)) ≤ c t^n`
  -- eventually for `c > θ ω_n`; the density squeeze then gives `Θ^n(μ_V, x) = θ`.
  exact Submission.frt_td_hasDensity_of_ball_mass_bounds N n V.weight x (ENNReal.ofReal θ)
    (Submission.frt_td_ball_mass_lower_of_blowup N n V.weight x T θ hθ hblow)
    (Submission.frt_td_ball_mass_upper_of_blowup N n V.weight x T θ r₀ hθ hr₀ hμr₀ hblow)

/-- **Simon Ch. 8, Definition 1.1: the tangent space and its multiplicity are unique** (child
`tangent_unique` of `first_rectifiability`: step (0d) of the parent's proof of 1.2; cf. Ch. 3,
Remark 1.5(1)).  If `V` has tangent space `T` with multiplicity `θ` and `T'` with multiplicity
`θ'` at `x`, then `T' = T` and `θ' = θ`.  Both multiplicities are the density `Θ^n(μ_V, x)`; the
weight blow-ups then give `∫ g dH^n⌞T' = ∫ g dH^n⌞T` for every `g ∈ C_c(ℝ^N)`, so the regular
measures `H^n⌞T'` and `H^n⌞T` agree, hence so do their supports `T'` and `T`; a projection matrix
is determined by its range. -/
theorem Submission.frt_tangent_plane_unique :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N)
      (T T' : Grassmannian N n) (θ θ' : ℝ),
      HasTangentPlane V x T θ → HasTangentPlane V x T' θ' → T' = T ∧ θ' = θ := by
  intro N n U V x T T' θ θ' hT hT'
  -- Step 1: `θ'` and `θ` are both the limit of the density ratio along `𝓝[>] 0`.
  have hθ : θ' = θ :=
    (ENNReal.ofReal_eq_ofReal_iff hT'.2.1.le hT.2.1.le).mp
      (tendsto_nhds_unique (Submission.frt_tangent_plane_hasDensity N n U V x T' θ' hT')
        (Submission.frt_tangent_plane_hasDensity N n U V x T θ hT))
  refine ⟨?_, hθ⟩
  -- Steps 2–3: `H^n⌞T'` and `H^n⌞T` are regular with the same `C_c` integrals (cancel `θ > 0`).
  have hmeasure : (μHE[n] : Measure (Euclidean N)).restrict (T'.plane : Set (Euclidean N)) =
      (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) := by
    have := Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane
    have := Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ ?_
    have h := tendsto_nhds_unique (Submission.frt_weight_blowup_tendsto N n U V x T' θ' hT' g)
      (Submission.frt_weight_blowup_tendsto N n U V x T θ hT g)
    rw [hθ] at h
    exact mul_left_cancel₀ hT.2.1.ne' h
  -- Step 4: the support of `H^n⌞P` is the `n`-plane `P`.
  have hplane : T'.plane = T.plane := by
    apply SetLike.ext'
    rw [← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane,
      ← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane, hmeasure]
  -- Step 5: `p_S` is symmetric and idempotent, hence the orthogonal projection onto its range
  -- `S.plane`, and `S` is the matrix of `p_S`.
  have hproj : ∀ S : Grassmannian N n,
      S.projectionLinearMap = S.plane.starProjection.toLinearMap := by
    intro S
    obtain ⟨_, hS⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
      ⟨S.projectionLinearMap_comp_self, S.projectionLinearMap_isSymmetric⟩
    exact hS
  apply Subtype.ext
  rw [← T'.toMatrix_projectionLinearMap, ← T.toMatrix_projectionLinearMap, hproj T', hproj T,
    hplane]
/-- The net-of-planes step of Simon Ch. 3, proof of Theorem 1.6 "⇐" (p. 73), for the tangent
points of a varifold (Ch. 8, 1.2): suppose that for every `L ∈ (0,1]` and every plane `P` there are
closed `L`-graphs `Γ_0, Γ_1, …` over `P` (`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for
`y, z ∈ Γ_i`) containing every `x` at which `V` has a tangent plane `T` with
`|p_T v - p_P v| ≤ (L/4)|v|`.  Then for every `L ∈ (0,1]` countably many closed `L`-graphs, each
paired with its base plane, cover all points at which `V` has a tangent plane.  A countable dense set
of planes replaces the book's finite net: `S ↦ p_S` is continuous into operators, so every plane is
within operator distance `L/4` of a plane of the dense set. -/
theorem Submission.frt_tangent_points_flat_graph_cover :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), (∀ L : ℝ, 0 < L → L ≤ 1 → ∀ P : Grassmannian N n, ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) → ∃ i, x ∈ Γ i) → ∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ} ⊆ ⋃ c ∈ C, c.2 := by
  intro N n U V hcov L hL0 hL1
  -- Step 2: `Φ S = p_S`, as a continuous linear operator, depends continuously on `S`, being a
  -- linear function of the projection matrix `S.1`.
  let Φ : Grassmannian N n → (Euclidean N →L[ℝ] Euclidean N) := fun S ↦
    LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S)
  have hΦ : Continuous Φ := by
    let F : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N) :=
      (LinearMap.toContinuousLinearMap :
          (Euclidean N →ₗ[ℝ] Euclidean N) ≃ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N)).toLinearMap ∘ₗ
        (LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
          Grassmannian.coordinateBasis.toBasis).symm.toLinearMap
    exact F.continuous_of_finiteDimensional.comp continuous_subtype_val
  have hΦapp : ∀ S v, Φ S v = Grassmannian.project S v := fun _ _ ↦ rfl
  -- Step 3: a countable dense set `D` of planes is an `L/4`-net in operator norm.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Grassmannian N n)
  have hnet : ∀ T : Grassmannian N n, ∃ P ∈ D, ∀ v : Euclidean N,
      ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖ := by
    intro T
    have hopen : IsOpen {S | ‖Φ S - Φ T‖ < L / 4} :=
      isOpen_lt (continuous_norm.comp (hΦ.sub continuous_const)) continuous_const
    obtain ⟨P, hPD, hP⟩ := hDd.exists_mem_open hopen ⟨T, by simpa using div_pos hL0 four_pos⟩
    refine ⟨P, hPD, fun v ↦ ?_⟩
    have hTP : ‖Φ T - Φ P‖ ≤ L / 4 := by
      rw [norm_sub_rev]
      exact le_of_lt hP
    simpa [hΦapp] using (Φ T - Φ P).le_of_opNorm_le hTP v
  -- Step 4: choose the covers `Γ P` supplied for the planes `P ∈ D` and collect them over `D × ℕ`.
  choose Γ hΓc hΓg hΓx using hcov L hL0 hL1
  refine ⟨(fun p : Grassmannian N n × ℕ ↦ (p.1, Γ p.1 p.2)) '' (D ×ˢ univ),
    (hDc.prod countable_univ).image _, ?_, ?_⟩
  · -- Step 5: each member is a closed `L`-graph over its plane.
    rintro c ⟨⟨P, i⟩, -, rfl⟩
    exact ⟨hΓc P i, hΓg P i⟩
  · -- Step 6: a tangent point with plane `T` lies in a graph over a plane `P ∈ D` near `T`.
    rintro x ⟨T, θ, hx⟩
    obtain ⟨P, hPD, hP⟩ := hnet T
    obtain ⟨i, hi⟩ := hΓx P x T θ hx hP
    exact mem_iUnion₂.2 ⟨(P, Γ P i), ⟨(P, i), ⟨hPD, mem_univ i⟩, rfl⟩, hi⟩
/-- Sets covered by countably many `1`-graphs are countably `n`-rectifiable (Simon Ch. 3, proof of
Theorem 1.6 "⇐", p. 74): if `C` is countable and every `(P, Γ) ∈ C` satisfies
`|(y - z) - p_P(y - z)| ≤ |p_P(y - z)|` for `y, z ∈ Γ`, then `p_P` is injective on `Γ` with a
`√2`-Lipschitz inverse, so `Γ` lies in the range of a Lipschitz map `ℝ^n → ℝ^N`, and every
`M ⊆ ⋃_{c ∈ C} c.2` is countably `n`-rectifiable. -/
theorem Submission.frt_countablyRectifiable_of_graph_cover :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (C : Set (Grassmannian N n × Set (Euclidean N))), C.Countable → (∀ c ∈ C, ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ ‖Grassmannian.project c.1 (y - z)‖) → M ⊆ ⋃ c ∈ C, c.2 → Chapter03.CountablyRectifiable n M := by
  intro N n M C hC hgraph hM
  -- Step 1: `p_P` is symmetric and idempotent, so `|v|² = |p_P v|² + |v - p_P v|²`.
  have hpyth : ∀ (P : Grassmannian N n) (v : Euclidean N),
      ‖v‖ ^ 2 = ‖Grassmannian.project P v‖ ^ 2 + ‖v - Grassmannian.project P v‖ ^ 2 := by
    intro P v
    have hker : Grassmannian.project P (v - Grassmannian.project P v) = 0 := by
      rw [show Grassmannian.project P (v - Grassmannian.project P v) =
          Grassmannian.project P v - Grassmannian.project P (Grassmannian.project P v) from
        map_sub P.projectionLinearMap v (Grassmannian.project P v),
        Grassmannian.project_project, sub_self]
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
  -- Step 3 (plane coordinates): a linear isometry `ι : ℝ^n → ℝ^N` onto `P.plane`, from an
  -- orthonormal basis of `P.plane` indexed by `Fin n` (`finrank P.plane = n`).
  have hparam : ∀ P : Grassmannian N n, ∃ ι : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N,
      ∀ x ∈ P.plane, ∃ a, ι a = x := by
    intro P
    let b := (stdOrthonormalBasis ℝ P.plane).reindex (finCongr P.finrank_plane)
    exact ⟨P.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,
      fun x hx ↦ ⟨b.repr ⟨x, hx⟩, by simp⟩⟩
  -- Steps 2–5: each `1`-graph `Γ` over `P` lies in the range of a Lipschitz map `ℝ^n → ℝ^N`.
  have hone : ∀ (P : Grassmannian N n) (Γ : Set (Euclidean N)),
      (∀ y ∈ Γ, ∀ z ∈ Γ,
        ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ ‖Grassmannian.project P (y - z)‖) →
      ∃ (K : NNReal) (F : EuclideanSpace ℝ (Fin n) → Euclidean N),
        LipschitzWith K F ∧ Γ ⊆ range F := by
    intro P Γ hΓ
    -- Step 2: `|y - z|² ≤ 2 |p_P y - p_P z|²` on `Γ`, so `p_P` is injective on `Γ` and its
    -- inverse `h` is `√2`-Lipschitz on `p_P(Γ)`.
    have hkey : ∀ y ∈ Γ, ∀ z ∈ Γ,
        ‖y - z‖ ≤ Real.sqrt 2 * ‖Grassmannian.project P y - Grassmannian.project P z‖ := by
      intro y hy z hz
      have hsub : Grassmannian.project P (y - z) =
          Grassmannian.project P y - Grassmannian.project P z :=
        map_sub P.projectionLinearMap y z
      have h1 := hpyth P (y - z)
      have h2 := hΓ y hy z hz
      have h3 : ‖y - z‖ ^ 2 ≤ 2 * ‖Grassmannian.project P (y - z)‖ ^ 2 := by
        nlinarith [norm_nonneg ((y - z) - Grassmannian.project P (y - z)),
          norm_nonneg (Grassmannian.project P (y - z))]
      rw [hsub] at h3
      calc ‖y - z‖ = Real.sqrt (‖y - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (2 * ‖Grassmannian.project P y - Grassmannian.project P z‖ ^ 2) :=
          Real.sqrt_le_sqrt h3
        _ = Real.sqrt 2 * ‖Grassmannian.project P y - Grassmannian.project P z‖ := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
    have hinj : InjOn (Grassmannian.project P) Γ := by
      intro y hy z hz hyz
      have h := hkey y hy z hz
      rw [hyz, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    let h := Function.invFunOn (Grassmannian.project P) Γ
    have hleft : ∀ y ∈ Γ, h (Grassmannian.project P y) = y :=
      fun y hy ↦ hinj.leftInvOn_invFunOn hy
    -- Step 3: `k = h ∘ ι` is `√2`-Lipschitz on `S = ι⁻¹(p_P(Γ))`, as `ι` is an isometry.
    obtain ⟨ι, hι⟩ := hparam P
    let S : Set (EuclideanSpace ℝ (Fin n)) := ι ⁻¹' (Grassmannian.project P '' Γ)
    have hk : LipschitzOnWith (Real.toNNReal (Real.sqrt 2)) (fun a ↦ h (ι a)) S := by
      refine LipschitzOnWith.of_dist_le' fun a ha b hb ↦ ?_
      obtain ⟨y, hy, hya⟩ := ha
      obtain ⟨z, hz, hzb⟩ := hb
      have hka : h (ι a) = y := by rw [← hya, hleft y hy]
      have hkb : h (ι b) = z := by rw [← hzb, hleft z hz]
      rw [hka, hkb, dist_eq_norm, dist_eq_norm]
      calc ‖y - z‖ ≤ Real.sqrt 2 * ‖Grassmannian.project P y - Grassmannian.project P z‖ :=
            hkey y hy z hz
        _ = Real.sqrt 2 * ‖a - b‖ := by rw [hya, hzb, ← map_sub, ι.norm_map]
    -- Step 4: extend `k` to a Lipschitz map `F : ℝ^n → ℝ^N` (coordinatewise McShane extension).
    obtain ⟨F, hF, hkF⟩ := hk.extend_finite_dimension
    -- Step 5: for `y ∈ Γ` write `p_P y = ι a`; then `a ∈ S` and `F a = h (p_P y) = y`.
    refine ⟨_, F, hF, fun y hy ↦ ?_⟩
    obtain ⟨a, ha⟩ := hι (Grassmannian.project P y) (LinearMap.mem_range_self _ y)
    refine ⟨a, ?_⟩
    rw [← hkF (show a ∈ S from ⟨y, hy, ha.symm⟩)]
    change h (ι a) = y
    rw [ha, hleft y hy]
  -- Step 6: `{c.2 : c ∈ C}` is a countable family of countably `n`-rectifiable sets (the empty
  -- family included), and `M` is contained in its union.
  have hrect : ∀ S ∈ (fun c : Grassmannian N n × Set (Euclidean N) ↦ c.2) '' C,
      Chapter03.CountablyRectifiable n S := by
    rintro S ⟨c, hc, rfl⟩
    obtain ⟨K, F, hF, hsub⟩ := hone c.1 c.2 (hgraph c hc)
    exact (Chapter03.countablyRectifiable_range hF).mono hsub
  refine (Chapter03.countablyRectifiable_sUnion (hC.image _) hrect).mono ?_
  rwa [sUnion_image]
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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
