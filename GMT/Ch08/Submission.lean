import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter08.TangentRadialRigidity
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.Submanifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Poincare.SimonGMT.Chapter08.StationaryMonotonicity
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

/-- A countably `n`-rectifiable set `M ⊆ ℝ^N` carries a σ-finite measure `H^n ⌞ M`: up to the
`H^n`-null set `M₀`, `M` is covered by the compact Lipschitz images `F_j(B_k(0))`, each of finite
`H^n`-measure. -/
theorem Submission.allard_tc_tpr_rectifiable_sigmaFinite :
    ∀ (N n : ℕ) (M : Set (Euclidean N)), Chapter03.CountablyRectifiable n M → SigmaFinite ((μHE[n] : Measure (Euclidean N)).restrict M) := by
  intro N n M hM
  -- Step 1: `M ⊆ M₀ ∪ ⋃ j, range (F j)` with `H^n(M₀) = 0` and `F j` `K j`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  -- Step 2: the compact pieces `C (j, k) = F j '' closedBall 0 k` are measurable.
  let C : ℕ × ℕ → Set (Euclidean N) := fun p ↦ F p.1 '' closedBall 0 p.2
  have hCmeas : ∀ p, MeasurableSet (C p) := fun p ↦
    ((isCompact_closedBall _ _).image (hK p.1).continuous).isClosed.measurableSet
  -- Step 3: `H^n(C (j, k)) ≤ K_j^n H^n(closedBall 0 k) < ∞`, using `μHE[n] = c • μH[n]`.
  have hCfin : ∀ p, (μHE[n] : Measure (Euclidean N)) (C p) < ∞ := by
    intro p
    have hball : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n)))
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) p.2) < ∞ := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact measure_closedBall_lt_top
    have hle : (μHE[n] : Measure (Euclidean N)) (C p) ≤
        (K p.1 : ℝ≥0∞) ^ (n : ℝ) * (μHE[n] : Measure (EuclideanSpace ℝ (Fin n)))
          (closedBall (0 : EuclideanSpace ℝ (Fin n)) p.2) := by
      simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul]
      rw [mul_left_comm]
      gcongr
      exact (hK p.1).hausdorffMeasure_image_le (Nat.cast_nonneg n) _
    exact hle.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hball)
  -- Step 4: `S = toMeasurable H M₀ ∪ ⋃ C` is measurable and contains `M`.
  let T := toMeasurable (μHE[n] : Measure (Euclidean N)) M₀
  let S := T ∪ ⋃ p, C p
  have hSmeas : MeasurableSet S :=
    (measurableSet_toMeasurable _ _).union (MeasurableSet.iUnion hCmeas)
  have hMS : M ⊆ S := by
    intro x hx
    rcases hcover hx with h0 | hr
    · exact Or.inl (subset_toMeasurable _ _ h0)
    · obtain ⟨j, y, rfl⟩ := mem_iUnion.1 hr
      obtain ⟨k, hk⟩ := exists_nat_ge ‖y‖
      exact Or.inr (mem_iUnion.2 ⟨(j, k), y, mem_closedBall_zero_iff.2 hk, rfl⟩)
  -- Steps 5–7: the countable family `{Sᶜ, T} ∪ {C p}` covers and has finite `H^n ⌞ M`-measure.
  refine Measure.sigmaFinite_of_countable (S := insert Sᶜ (insert T (range C)))
    (((countable_range C).insert _).insert _) ?_ ?_
  · rintro s (rfl | rfl | ⟨p, rfl⟩)
    · rw [Measure.restrict_apply hSmeas.compl,
        measure_mono_null (fun x hx ↦ (hx.1 (hMS hx.2)).elim) measure_empty]
      exact ENNReal.zero_lt_top
    · refine (Measure.restrict_apply_le _ _).trans_lt ?_
      rw [measure_toMeasurable, hM₀]
      exact ENNReal.zero_lt_top
    · exact (Measure.restrict_apply_le _ _).trans_lt (hCfin p)
  · rw [sUnion_insert, sUnion_insert, sUnion_range]
    exact compl_union_self S
/-- `μ`-null sets of positive density are `H^n`-null (Simon Ch. 1, Theorem 3.3, as used in Ch. 8):
if `μ` is finite on compact sets, `μ(Z) = 0` and `Θ^n(μ, x) = θ(x) > 0` for every `x ∈ Z`, then
`H^n(Z) = 0`.  Proof by a Vitali covering of `Z_k = {x ∈ Z : θ(x) > 1/(k+1)}` with closed balls
inside an open `O ⊇ Z_k` of small `μ`-measure. -/
theorem Submission.allard_tc_tpr_hausdorff_null_of_weight_null :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (Z : Set (Euclidean N)) (θ : Euclidean N → ℝ), (∀ K : Set (Euclidean N), IsCompact K → μ K ≠ ∞) → μ Z = 0 → (∀ x ∈ Z, 0 < θ x ∧ HasDensity n μ x (ENNReal.ofReal (θ x))) → μHE[n] Z = 0 := by
  intro N n μ Z θ hμK hμZ hZ
  -- Step 1: `μ` is finite on compact sets, hence outer regular on `ℝ^N`.
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK ↦ (hμK K hK).lt_top⟩
  -- Step 2: `μHE[n]` is a constant multiple of `μH[n]`, so it suffices that `μH[n] Z = 0`.
  suffices hH : μH[(n : ℝ)] Z = 0 by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Step 3: `ω_n ∈ (0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Step 4: `Z ⊆ ⋃ k, Z_k` with `Z_k = {x ∈ Z : 1/(k+1) < θ x}`; fix `k`.
  have hcover : Z ⊆ ⋃ k : ℕ, {x | x ∈ Z ∧ 1 / ((k : ℝ) + 1) < θ x} := fun x hx ↦
    mem_iUnion.2 ((exists_nat_one_div_lt (hZ x hx).1).imp fun _ hk ↦ ⟨hx, hk⟩)
  refine measure_mono_null hcover (measure_iUnion_null fun k ↦ ?_)
  set A := {x | x ∈ Z ∧ 1 / ((k : ℝ) + 1) < θ x} with hA
  have hs : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
  have hμA : μ A = 0 := measure_mono_null (fun x hx ↦ hx.1) hμZ
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / ((k : ℝ) + 1)) * unitBallVolume n with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hs).ne' hω0
  have hct : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωt
  -- Step 5: small closed balls about points of `A` have mass at least `c ρ^n`.
  have hball : ∀ x ∈ A, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      c * ENNReal.ofReal ρ ^ n ≤ μ (closedBall x ρ) := by
    intro x hx
    have hlt : ENNReal.ofReal (1 / ((k : ℝ) + 1)) < ENNReal.ofReal (θ x) :=
      (ENNReal.ofReal_lt_ofReal_iff (hs.trans hx.2)).2 hx.2
    filter_upwards [(hZ x hx.1).2.eventually (lt_mem_nhds hlt)] with ρ hρ
    rw [hc, mul_assoc]
    exact ENNReal.mul_le_of_le_div hρ.le
  -- Step 6: Vitali covering: for every open `O ⊇ A`, `μH[n](A) ≤ 8^n c⁻¹ μ(O)`.
  have hcov : ∀ O : Set (Euclidean N), IsOpen O → A ⊆ O →
      μH[(n : ℝ)] A ≤ 8 ^ n * c⁻¹ * μ O := by
    intro O hO hAO
    have hrad : ∀ (m : ℕ) (x : Euclidean N), ∃ ρ : ℝ, x ∈ A → 0 < ρ ∧ ρ ≤ 1 / ((m : ℝ) + 1) ∧
        closedBall x ρ ⊆ O ∧ c * ENNReal.ofReal ρ ^ n ≤ μ (closedBall x ρ) := by
      intro m x
      by_cases hx : x ∈ A
      · obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
        have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < min δ (1 / ((m : ℝ) + 1)) :=
          nhdsWithin_le_nhds (gt_mem_nhds (lt_min hδ Nat.one_div_pos_of_nat))
        obtain ⟨ρ, ⟨hρc, hρs⟩, hρ0⟩ := (((hball x hx).and hsmall).and self_mem_nhdsWithin).exists
        exact ⟨ρ, fun _ ↦ ⟨hρ0, (hρs.trans_le (min_le_right _ _)).le,
          (closedBall_subset_ball (hρs.trans_le (min_le_left _ _))).trans hδO, hρc⟩⟩
      · exact ⟨1, fun h ↦ absurd h hx⟩
    choose r hr using hrad
    have hvit : ∀ m : ℕ, ∃ u ⊆ A, (u.PairwiseDisjoint fun b ↦ closedBall b (r m b)) ∧
        ∀ a ∈ A, ∃ b ∈ u, closedBall a (r m a) ⊆ closedBall b (4 * r m b) := fun m ↦
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A id (r m)
        (1 / ((m : ℝ) + 1)) (fun a ha ↦ (hr m a ha).2.1) 4 (by norm_num)
    choose u huA hud huc using hvit
    have hcount : ∀ m, (u m).Countable := fun m ↦
      (hud m).countable_of_nonempty_interior fun b hb ↦
        ⟨b, ball_subset_interior_closedBall (mem_ball_self (hr m b (huA m hb)).1)⟩
    have : ∀ m, Countable (u m) := fun m ↦ (hcount m).to_subtype
    have hdiam : ∀ (b : Euclidean N) (R : ℝ), ediam (closedBall b R) ≤ ENNReal.ofReal (2 * R) :=
      fun b R ↦ ediam_le_of_forall_dist_le fun x hx y hy ↦
        calc dist x y ≤ dist x b + dist y b := dist_triangle_right _ _ _
          _ ≤ R + R := add_le_add hx hy
          _ = 2 * R := by ring
    have hsum : ∀ m, ∑' b : u m, ediam (closedBall (b : Euclidean N) (4 * r m b)) ^ (n : ℝ) ≤
        8 ^ n * c⁻¹ * μ O := by
      intro m
      calc ∑' b : u m, ediam (closedBall (b : Euclidean N) (4 * r m b)) ^ (n : ℝ)
          ≤ ∑' b : u m, 8 ^ n * c⁻¹ * μ (closedBall (b : Euclidean N) (r m b)) := by
            refine ENNReal.tsum_le_tsum fun b ↦ ?_
            obtain ⟨hb0, -, -, hbμ⟩ := hr m b (huA m b.2)
            have hd : ediam (closedBall (b : Euclidean N) (4 * r m b)) ≤
                8 * ENNReal.ofReal (r m b) := by
              refine (hdiam _ _).trans (le_of_eq ?_)
              rw [show 2 * (4 * r m b) = 8 * r m b by ring, ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_ofNat]
            rw [ENNReal.rpow_natCast, mul_assoc]
            calc ediam (closedBall (b : Euclidean N) (4 * r m b)) ^ n
                ≤ (8 * ENNReal.ofReal (r m b)) ^ n := by gcongr
              _ = 8 ^ n * ENNReal.ofReal (r m b) ^ n := mul_pow _ _ _
              _ ≤ 8 ^ n * (c⁻¹ * μ (closedBall (b : Euclidean N) (r m b))) := by
                gcongr
                exact (ENNReal.mul_le_iff_le_inv hc0 hct).1 hbμ
        _ = 8 ^ n * c⁻¹ * μ (⋃ b ∈ u m, closedBall b (r m b)) := by
            rw [ENNReal.tsum_mul_left, measure_biUnion (hcount m) (hud m)
              fun b _ ↦ measurableSet_closedBall]
        _ ≤ 8 ^ n * c⁻¹ * μ O := by
            gcongr
            exact iUnion₂_subset fun b hb ↦ (hr m b (huA m hb)).2.2.1
    calc μH[(n : ℝ)] A
        ≤ liminf (fun m ↦ ∑' b : u m, ediam (closedBall (b : Euclidean N) (4 * r m b)) ^ (n : ℝ))
            atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) A
            (fun m : ℕ ↦ ENNReal.ofReal (8 * (1 / ((m : ℝ) + 1)))) ?_
            (fun m (b : u m) ↦ closedBall (b : Euclidean N) (4 * r m b)) ?_ ?_
      _ ≤ 8 ^ n * c⁻¹ * μ O := liminf_le_of_frequently_le' (Frequently.of_forall hsum)
    · have h := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 8)
      rwa [mul_zero, ENNReal.ofReal_zero] at h
    · refine Eventually.of_forall fun m b ↦ (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [(hr m b (huA m b.2)).2.1]
    · refine Eventually.of_forall fun m a ha ↦ ?_
      obtain ⟨b, hb, hsub⟩ := huc m a ha
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hsub (mem_closedBall_self (hr m a ha).1.le)⟩
  -- Step 7: outer regularity makes `μ(O)` arbitrarily small, so `μH[n](A) = 0`.
  have hle : ∀ m : ℕ, μH[(n : ℝ)] A ≤ 8 ^ n * c⁻¹ * (m : ℝ≥0∞)⁻¹ := by
    intro m
    obtain ⟨O, hAO, hO, hμO⟩ := Set.exists_isOpen_lt_of_lt A ((m : ℝ≥0∞)⁻¹)
      (hμA.symm ▸ ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
    exact (hcov O hO hAO).trans (by gcongr)
  have htend : Tendsto (fun m : ℕ ↦ 8 ^ n * c⁻¹ * (m : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_top.2 hc0)) : (0 : ℝ≥0∞) ≠ 0 ∨ 8 ^ n * c⁻¹ ≠ ∞)
    rwa [mul_zero] at h
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' htend hle)

/-- **The weight is `θ H^n ⌞ M` once it is `θ H^n ⌞ E` for some `E ⊆ M`** (child
`weight_eq_restrict` of `tangent_point_representation`; gives `μ_C = θ H^n ⌞ M` when writing
`C = v(M, θ)` in the proof of Simon Ch. 8, 5.7).  Let `B* = toMeasurable (H^n ⌞ M) E`.  The
hypothesis on `B*ᶜ` is an integral over `E ∩ B*ᶜ = ∅`, so `μ(M ∖ B*) = 0`, and child
`hausdorff_null_of_weight_null` gives `H^n(M ∖ B*) = 0` because `θ > 0` is the density of `μ` on
`M`.  As `H^n ⌞ M` is s-finite, `(H^n ⌞ M)(B* ∩ D) = (H^n ⌞ M)(E ∩ D)` for measurable `D`; hence
`H^n ⌞ (E ∩ B) = H^n ⌞ (M ∩ B)` for Borel `B`, and the two set integrals agree. -/
theorem Submission.allard_tc_tpr_weight_eq_restrict :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M E : Set (Euclidean N)) (θ : Euclidean N → ℝ), (∀ K : Set (Euclidean N), IsCompact K → μ K ≠ ∞) → SFinite ((μHE[n] : Measure (Euclidean N)).restrict M) → E ⊆ M → (∀ x ∈ M, 0 < θ x ∧ HasDensity n μ x (ENNReal.ofReal (θ x))) → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in E ∩ B, ENNReal.ofReal (θ x) ∂μHE[n]) → ∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
  intro N n μ M E θ hμK hSF hEM hθ hrep B hB
  set H : Measure (Euclidean N) := μHE[n]
  -- Step 1: the measurable hull `B*` of `E` for the s-finite measure `ν = H^n ⌞ M`.
  set ν : Measure (Euclidean N) := H.restrict M with hν
  set Bs : Set (Euclidean N) := toMeasurable ν E
  have hBs : MeasurableSet Bs := measurableSet_toMeasurable ν E
  have hEBs : E ⊆ Bs := subset_toMeasurable ν E
  -- Step 2: `μ(M ∖ B*) = 0`, since `μ(B*ᶜ)` is the integral over `E ∩ B*ᶜ = ∅`.
  have hμc : μ Bsᶜ = 0 := by
    have hempty : E ∩ Bsᶜ = ∅ := subset_empty_iff.1 fun x hx ↦ hx.2 (hEBs hx.1)
    rw [hrep Bsᶜ hBs.compl, hempty, Measure.restrict_empty, lintegral_zero_measure]
  have hμZ : μ (M \ Bs) = 0 := measure_mono_null (fun x hx ↦ hx.2) hμc
  -- Step 3: `H^n(M ∖ B*) = 0` by child `hausdorff_null_of_weight_null`, as `M ∖ B* ⊆ M`.
  have hHZ : H (M \ Bs) = 0 :=
    Submission.allard_tc_tpr_hausdorff_null_of_weight_null N n μ (M \ Bs) θ hμK hμZ
      fun x hx ↦ hθ x hx.1
  -- Step 4: `H^n ⌞ (E ∩ B) = H^n ⌞ (M ∩ B)`, tested on measurable `D`.
  have hres : H.restrict (E ∩ B) = H.restrict (M ∩ B) := by
    refine Measure.ext fun D hD ↦ ?_
    rw [Measure.restrict_apply hD, Measure.restrict_apply hD]
    refine le_antisymm (measure_mono (inter_subset_inter_right D
      (inter_subset_inter_left B hEM))) ?_
    have hDB : MeasurableSet (D ∩ B) := hD.inter hB
    calc H (D ∩ (M ∩ B)) ≤ H (Bs ∩ (D ∩ B) ∩ M ∪ M \ Bs) := by
          refine measure_mono fun x hx ↦ ?_
          by_cases hx' : x ∈ Bs
          · exact Or.inl ⟨⟨hx', hx.1, hx.2.2⟩, hx.2.1⟩
          · exact Or.inr ⟨hx.2.1, hx'⟩
      _ ≤ H (Bs ∩ (D ∩ B) ∩ M) + H (M \ Bs) := measure_union_le _ _
      _ = ν (Bs ∩ (D ∩ B)) := by
          rw [hHZ, add_zero, hν, Measure.restrict_apply (hBs.inter hDB)]
      _ = ν (E ∩ (D ∩ B)) := Measure.measure_toMeasurable_inter_of_sFinite hDB E
      _ = H (E ∩ (D ∩ B)) := Measure.restrict_eq_self H fun x hx ↦ hEM hx.1
      _ = H (D ∩ (E ∩ B)) := by rw [inter_left_comm]
  -- Step 5: the two set integrals are integrals against equal measures.
  rw [hrep B hB, hres]
/-- Integration against the weight `μ = H^n ⌞ θ` of `v(M, θ)` (Simon Ch. 8, p. 206): if
`μ(B) = ∫_{M ∩ B} θ dH^n` for every Borel `B`, then `∫ g dμ = ∫_M g θ dH^n` for every
`g : ℝ^N → ℝ`. -/
theorem Submission.allard_tc_tpr_integral_eq_weighted :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), NullMeasurableSet M μHE[n] → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]) → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n]) → ∀ g : Euclidean N → ℝ, ∫ z, g z ∂μ = ∫ z in M, g z * θ z ∂μHE[n] := by
  intro N n μ M θ hM hθ hint hμ g
  -- Step 1: `θ` is a.e.-measurable for `H^n ⌞ M`, exhausting `M` by the pieces `M ∩ B_k(0)`.
  have hθm : AEMeasurable θ ((μHE[n] : Measure (Euclidean N)).restrict M) := by
    have hcover : M = ⋃ k : ℕ, M ∩ closedBall (0 : Euclidean N) k := by
      rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
    rw [hcover, aemeasurable_iUnion_iff]
    exact fun k ↦ (hint _ (isCompact_closedBall 0 k)).aemeasurable
  -- Step 2: `μ = (H^n ⌞ M).withDensity (ofReal ∘ θ)`, as both agree on Borel sets.
  have hμeq : μ = ((μHE[n] : Measure (Euclidean N)).restrict M).withDensity
      fun x ↦ ENNReal.ofReal (θ x) := by
    ext B hB
    rw [hμ B hB, withDensity_apply _ hB, Measure.restrict_restrict hB, Set.inter_comm M B]
  -- Step 3: the `withDensity` identity for the Bochner integral, valid for every `g`.
  rw [hμeq, integral_withDensity_eq_integral_toReal_smul₀ hθm.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  -- Step 4: `(ofReal θ).toReal = θ` on `M`, and `H^n ⌞ M`-a.e. point lies in `M`.
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem₀ hM] with x hx
  rw [ENNReal.toReal_ofReal (hθ x hx).le, smul_eq_mul, mul_comm]
/-- Change of variables under a blow-up (Simon Ch. 8, 5.1/5.5): for `r > 0` and
`η_{x,r}(z) = r⁻¹(z - x)`, `∫_{η_{x,r}(M)} φ dH^n = r^{-n} ∫_M φ ∘ η_{x,r} dH^n` for every set `M`
and every function `φ`. -/
theorem Submission.allard_tc_tpr_blowup_setIntegral :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (φ : Euclidean N → ℝ) (x : Euclidean N) (r : ℝ), 0 < r → ∫ y in Chapter03.blowUpMap x r '' M, φ y ∂μHE[n] = r⁻¹ ^ n * ∫ z in M, φ (Chapter03.blowUpMap x r z) ∂μHE[n] := by
  intro N n M φ x r hr
  set H : Measure (Euclidean N) := μHE[n]
  set η : Euclidean N → Euclidean N := Chapter03.blowUpMap x r
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  -- Step 1: `η` is translation by `-x` followed by dilation by `r⁻¹`, a homeomorphism, hence a
  -- measurable embedding.
  let e : Euclidean N ≃ₜ Euclidean N :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ hr')
  have he : ⇑e = η := by
    funext z
    simp [e, η, Chapter03.blowUpMap]
  have hemb : MeasurableEmbedding η := he ▸ e.toMeasurableEquiv.measurableEmbedding
  -- Step 2: `H(η(A)) = r^{-n} H(A)` for every set `A` (translation invariance and scaling).
  have hscale : ∀ A : Set (Euclidean N), H (η '' A) = ENNReal.ofReal (r⁻¹ ^ n) * H A := by
    intro A
    have himg : η '' A = r⁻¹ • ((fun z ↦ z - x) '' A) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    have hiso : Isometry (fun z : Euclidean N ↦ z - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Measure.euclideanHausdorffMeasure_smul₀ n hr', hiso.euclideanHausdorffMeasure_image]
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      Real.norm_of_nonneg (inv_pos.mpr hr).le, ← ENNReal.ofReal_pow (inv_pos.mpr hr).le]
  -- Step 3: `H ⌞ η(M) = r^{-n} η_# (H ⌞ M)`, checked on measurable sets `D` via
  -- `η(η⁻¹(D) ∩ M) = D ∩ η(M)`.
  have hmeas : H.restrict (η '' M) = ENNReal.ofReal (r⁻¹ ^ n) • (H.restrict M).map η := by
    ext D hD
    rw [Measure.restrict_apply hD, Measure.smul_apply, Measure.map_apply hemb.measurable hD,
      Measure.restrict_apply (hemb.measurable hD), smul_eq_mul, ← hscale,
      Set.inter_comm (η ⁻¹' D), Set.image_inter_preimage, Set.inter_comm]
  -- Step 4: integrate; `MeasurableEmbedding.integral_map` needs no measurability of `φ`.
  rw [hmeas, integral_smul_measure, hemb.integral_map, ENNReal.toReal_ofReal
    (pow_nonneg (inv_pos.mpr hr).le n), smul_eq_mul]
/-- Varifold tangent planes versus approximate tangent planes (Simon Ch. 8, Definition 1.1 against
Ch. 3, 1.7): if `μ_V = H^n ⌞ θ` on `M` and `V` has tangent plane `T` with multiplicity `θ(x)`
at `x`, then `T` is the unique approximate tangent space of `M` at `x` with respect to `θ`. -/
theorem Submission.allard_tc_tpr_weighted_approx_tangent_iff :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (T : Grassmannian N n), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]) → (∀ B : Set (Euclidean N), MeasurableSet B → V.weight B = ∫⁻ y in M ∩ B, ENNReal.ofReal (θ y) ∂μHE[n]) → HasTangentPlane V x T (θ x) → ∀ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ↔ S = T := by
  intro N n U V M θ x T hM hθ hθint hweight hT
  -- Steps 1–6: `T.plane` is an approximate tangent space of `M` at `x` with respect to `θ`.
  have hTM : Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x T.plane := by
    refine ⟨T.finrank_plane, fun g ↦ ?_⟩
    -- Step 2: the test function `f(z, S) = g(z)` is compactly supported, `G(N,n)` being compact.
    have hf : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1) :=
      HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) fun z hz ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨h, mem_univ _⟩
    let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
      ⟨⟨fun z ↦ g z.1, (map_continuous g).comp continuous_fst⟩, hf⟩
    have hfc : Continuous (f : Euclidean N × Grassmannian N n → ℝ) := map_continuous f
    -- Step 3: Definition 1.1 tested with `f`; the plane side is `θ(x) ∫_T g dH^n`.
    have hlim := hT.2.2 f
    have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
        ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] := by
      rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T)) (by fun_prop)
        hfc.aestronglyMeasurable]
      rfl
    rw [hplane] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hr' : (0 : ℝ) ≤ r⁻¹ ^ n := pow_nonneg (inv_nonneg.2 hr0.le) n
    have hg : Continuous fun y : Euclidean N ↦ g (r⁻¹ • (y - x)) := by fun_prop
    -- Step 5: by the two sibling children and `x + r • η_{x,r}(z) = z`, the weighted blow-up
    -- integral is `r^{-n} ∫ g(r^{-1}(z - x)) dμ_V(z)` for `r > 0`.
    have hblow : ∫ y in Chapter03.blowUpMap x r '' M, g y * θ (x + r • y) ∂μHE[n] =
        r⁻¹ ^ n * ∫ z, g (r⁻¹ • (z - x)) ∂V.weight := by
      rw [Submission.allard_tc_tpr_blowup_setIntegral N n M
          (fun y ↦ g y * θ (x + r • y)) x r hr0,
        Submission.allard_tc_tpr_integral_eq_weighted N n V.weight M θ hM hθ hθint hweight]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
      simp only [Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul,
        add_sub_cancel]
    -- Step 4: the rescaled side `∫ f dV_{x,r}` is also `r^{-n} ∫ g(r^{-1}(z - x)) dμ_V(z)`.
    rw [hblow, rescaledMeasure, integral_smul_measure,
      integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (r⁻¹ • (z.1 - x), z.2))
        (by fun_prop) hfc.aestronglyMeasurable, ENNReal.toReal_ofReal hr', smul_eq_mul,
      Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
    rfl
  -- Step 7: weighted approximate tangent planes are unique where `θ(x) ≠ 0`, and a point of
  -- `G(N,n)` is determined by its plane, since `Grassmannian.ofSubmodule S.plane _ = S`.
  intro S
  refine ⟨fun hS ↦ ?_, ?_⟩
  · have hST : S.plane = T.plane := hS.unique hT.2.1.ne' hTM
    calc S = Grassmannian.ofSubmodule S.plane S.finrank_plane :=
          (Grassmannian.ofSubmodule_plane S).symm
      _ = Grassmannian.ofSubmodule T.plane T.finrank_plane := by congr 1
      _ = T := Grassmannian.ofSubmodule_plane T
  · rintro rfl
    exact hTM
/-- Change of variables for `H^n` under a dilation (used for the rescaling invariance of
tangent cones, Simon Ch. 8, 5.3 and 5.7): for `s > 0`, an arbitrary set `D` and an arbitrary
`f : ℝ^N → [0,∞]`, `∫_D f dH^n = s^n ∫_{s⁻¹ D} f(s w) dH^n(w)`. -/
theorem Submission.allard_tc_cri_hausdorff_dilation_lintegral :
    ∀ (N n : ℕ) (s : ℝ) (D : Set (Euclidean N)) (f : Euclidean N → ℝ≥0∞), 0 < s → ∫⁻ x in D, f x ∂(μHE[n] : Measure (Euclidean N)) = ENNReal.ofReal s ^ n * ∫⁻ w in {w : Euclidean N | s • w ∈ D}, f (s • w) ∂(μHE[n] : Measure (Euclidean N)) := by
  intro N n s D f hs
  -- Step 1: the dilation `σ w = s • w` is a measurable equivalence of `ℝ^N`.
  let σ : Euclidean N ≃ᵐ Euclidean N := MeasurableEquiv.smul₀ s hs.ne'
  -- Step 2: `H^n.map σ = ofReal (s⁻¹) ^ n • H^n`, since `σ⁻¹ E = s⁻¹ • E`.
  have hmap : (μHE[n] : Measure (Euclidean N)).map σ =
      ENNReal.ofReal s⁻¹ ^ n • (μHE[n] : Measure (Euclidean N)) := by
    ext E hE
    rw [Measure.map_apply σ.measurable hE, Measure.smul_apply, smul_eq_mul,
      show (σ : Euclidean N → Euclidean N) ⁻¹' E = s⁻¹ • E from Set.preimage_smul₀ hs.ne' E,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hs.ne'), ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal (inv_nonneg.2 hs.le)]
  -- Step 3: hence `H^n = ofReal s ^ n • H^n.map σ`.
  have hH : (μHE[n] : Measure (Euclidean N)) =
      ENNReal.ofReal s ^ n • (μHE[n] : Measure (Euclidean N)).map σ := by
    rw [hmap, smul_smul, ← mul_pow, ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne',
      ENNReal.ofReal_one, one_pow, one_smul]
  -- Steps 4–6: pull out the constant, commute restriction with `σ`, change variables.
  conv_lhs => rw [hH]
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, MeasurableEquiv.restrict_map,
    lintegral_map_equiv]
  -- Step 7: `σ⁻¹ D = {w | s • w ∈ D}` and `σ w = s • w` definitionally.
  rfl

/-- **Dilation of a varifold given by a fibrewise `H^n`-representation** (child
`rescaled_representation` of `cone_rescaling_invariance`; Simon Ch. 8, 5.3 and 5.7).  If
`C(A) = ∫_{x ∈ M, ∃ T, P x T ∧ (x, T) ∈ A} g dH^n` for Borel `A`, then for `s > 0`
`η_{0,s #} C (A) = ∫_{s w ∈ M, ∃ T, P (s w) T ∧ (w, T) ∈ A} g (s w) dH^n(w)`: pull `A` back by
`Φ(z, S) = (s⁻¹ (z - 0), S)`, apply the representation, change variables `x = s w` with child
`hausdorff_dilation_lintegral`, and cancel `s^{-n} s^n = 1`. -/
theorem Submission.allard_tc_cri_rescaled_representation :
    ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (M : Set (Euclidean N)) (P : Euclidean N → Grassmannian N n → Prop) (g : Euclidean N → ℝ≥0∞), (∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n, P x T ∧ (x, T) ∈ A}, g x ∂(μHE[n] : Measure (Euclidean N))) → ∀ s : ℝ, 0 < s → ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → rescaledMeasure C 0 s A = ∫⁻ w in {w : Euclidean N | s • w ∈ M ∧ ∃ T : Grassmannian N n, P (s • w) T ∧ (w, T) ∈ A}, g (s • w) ∂(μHE[n] : Measure (Euclidean N)) := by
  intro N n C M P g hrep s hs A hA
  -- Step 1: `Φ(z, S) = (s⁻¹ • (z - 0), S)` is measurable, so `A' = Φ⁻¹ A` is measurable.
  have hΦ : Measurable fun z : Euclidean N × Grassmannian N n ↦ (s⁻¹ • (z.1 - 0), z.2) := by
    fun_prop
  -- Step 6: `ofReal (s⁻¹ ^ n) * ofReal s ^ n = 1`.
  have hconst : ENNReal.ofReal (s⁻¹ ^ n) * ENNReal.ofReal s ^ n = 1 := by
    rw [ENNReal.ofReal_pow (inv_nonneg.2 hs.le), ← mul_pow,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le), inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one,
      one_pow]
  -- Step 2: `rescaledMeasure C 0 s A = ofReal (s⁻¹ ^ n) * C(A')`.
  rw [rescaledMeasure, Measure.smul_apply, smul_eq_mul, Measure.map_apply hΦ hA]
  -- Steps 3–4: the representation at `A'`, then child `hausdorff_dilation_lintegral` at
  -- `D₁ = {x ∈ M | ∃ T, P x T ∧ (x, T) ∈ A'}`; Step 7: the constants cancel.
  rw [hrep _ (hΦ hA), Submission.allard_tc_cri_hausdorff_dilation_lintegral N n s _ g hs,
    ← mul_assoc, hconst, one_mul]
  -- Step 5: `{w | s • w ∈ D₁}` is the claimed set, as `s⁻¹ • (s • w - 0) = w`.
  congr 2
  ext w
  simp only [mem_ofPred_eq, mem_preimage, sub_zero, inv_smul_smul₀ hs.ne']
/-- The carrier of a dilation-homogeneous measure `θ H^n ⌞ M` is dilation-invariant up to
`H^n`-null sets (used for the rescaling invariance of tangent cones, Simon Ch. 8, 5.3 and 5.7):
if `M` is `H^n`-measurable, `θ > 0` on `M` is locally `H^n`-integrable,
`μ(B) = ∫_{M ∩ B} θ dH^n` for Borel `B` and `μ(s A) = s^n μ(A)` for `s > 0`, then for every
`s > 0` the sets `{w ∈ M : s w ∉ M}` and `{w ∉ M : s w ∈ M}` are `H^n`-null. -/
theorem Submission.allard_tc_cri_carrier_dilation_null :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Euclidean N))) → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Euclidean N))) → (∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → μ (s • A) = ENNReal.ofReal s ^ n * μ A) → ∀ s : ℝ, 0 < s → (μHE[n] : Measure (Euclidean N)) {w : Euclidean N | w ∈ M ∧ s • w ∉ M} = 0 ∧ (μHE[n] : Measure (Euclidean N)) {w : Euclidean N | s • w ∈ M ∧ w ∉ M} = 0 := by
  intro N n μ M θ hM hθ hint hμ hhom s hs
  -- Step 1: a measurable kernel `M₀ ⊆ M` with `H^n (M \ M₀) = 0`.
  obtain ⟨M₀, hM₀M, hM₀, hM₀ae⟩ := hM.exists_measurable_subset_ae_eq
  have hdiff : (μHE[n] : Measure (Euclidean N)) (M \ M₀) = 0 := (ae_eq_set.1 hM₀ae).2
  -- Step 2: `μ (M₀ᶜ) = ∫⁻_{M \ M₀} ofReal θ dH^n = 0`.
  have hμc : μ M₀ᶜ = 0 := by
    rw [hμ _ hM₀.compl, ← Set.sdiff_eq]
    exact setLIntegral_measure_zero _ _ hdiff
  -- Step 3: a measurable `μ`-null subset `E` of `M₀` is `H^n`-null.
  have hnull : ∀ E : Set (Euclidean N), MeasurableSet E → E ⊆ M₀ → μ E = 0 →
      (μHE[n] : Measure (Euclidean N)) E = 0 := by
    intro E hE hEM₀ hμE
    have hEM : E ⊆ M := hEM₀.trans hM₀M
    have hk : ∀ k : ℕ, (μHE[n] : Measure (Euclidean N)) (E ∩ closedBall 0 k) = 0 := by
      intro k
      have hEk : MeasurableSet (E ∩ closedBall (0 : Euclidean N) k) :=
        hE.inter measurableSet_closedBall
      -- (a) `∫⁻_{E ∩ B_k} ofReal θ dH^n = μ (E ∩ B_k) = 0`, as `E ∩ B_k ⊆ M`.
      have h0 : ∫⁻ x in E ∩ closedBall (0 : Euclidean N) k, ENNReal.ofReal (θ x)
          ∂(μHE[n] : Measure (Euclidean N)) = 0 := by
        rw [← Set.inter_eq_right.2 (inter_subset_left.trans hEM), ← hμ _ hEk]
        exact measure_mono_null inter_subset_left hμE
      -- (b) `ofReal ∘ θ` is a.e.-measurable on `E ∩ B_k ⊆ M ∩ B_k` (local integrability).
      have hθk : AEMeasurable (fun x ↦ ENNReal.ofReal (θ x))
          ((μHE[n] : Measure (Euclidean N)).restrict (E ∩ closedBall 0 k)) :=
        ((hint _ (isCompact_closedBall (0 : Euclidean N) k)).mono_set
          (inter_subset_inter_left _ hEM)).aemeasurable.ennreal_ofReal
      -- (c) `ofReal θ = 0` a.e. on `E ∩ B_k ⊆ M`, where `θ > 0`; so `H^n (E ∩ B_k) = 0`.
      rw [lintegral_eq_zero_iff' hθk] at h0
      have hfalse : ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)).restrict (E ∩ closedBall 0 k),
          False := by
        filter_upwards [h0, ae_restrict_mem hEk] with x hx hxE
        exact absurd (ENNReal.ofReal_eq_zero.1 hx) (not_le.2 (hθ x (hEM hxE.1)))
      rwa [eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hfalse
    -- (d) `E ⊆ ⋃ k, E ∩ B_k`.
    refine measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null hk)
    obtain ⟨k, hxk⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨k, hx, mem_closedBall_zero_iff.2 hxk⟩
  -- Step 4: for `t > 0`, `{w ∈ M : t • w ∉ M} ⊆ (M \ M₀) ∪ (M₀ ∩ t⁻¹ • M₀ᶜ)` is `H^n`-null.
  have hkey : ∀ t : ℝ, 0 < t →
      (μHE[n] : Measure (Euclidean N)) {w : Euclidean N | w ∈ M ∧ t • w ∉ M} = 0 := by
    intro t ht
    have hEm : MeasurableSet (M₀ ∩ (fun w : Euclidean N ↦ t • w) ⁻¹' M₀ᶜ) :=
      hM₀.inter (hM₀.compl.preimage (measurable_const_smul t))
    have hμE : μ (M₀ ∩ (fun w : Euclidean N ↦ t • w) ⁻¹' M₀ᶜ) = 0 := by
      refine measure_mono_null inter_subset_right ?_
      rw [Set.preimage_smul₀ ht.ne', hhom _ _ (inv_pos.2 ht), hμc, mul_zero]
    refine measure_mono_null ?_ (measure_union_null hdiff (hnull _ hEm inter_subset_left hμE))
    rintro w ⟨hwM, hwt⟩
    by_cases hw : w ∈ M₀
    · exact Or.inr ⟨hw, fun h ↦ hwt (hM₀M h)⟩
    · exact Or.inl ⟨hwM, hw⟩
  -- Step 5: the first conjunct is step 4 with `t = s`.
  refine ⟨hkey s hs, ?_⟩
  -- Step 6: `{w : s • w ∈ M ∧ w ∉ M} = s⁻¹ • {y ∈ M : s⁻¹ • y ∉ M}`; apply step 4 with `t = s⁻¹`.
  have hset : {w : Euclidean N | s • w ∈ M ∧ w ∉ M} =
      s⁻¹ • {y : Euclidean N | y ∈ M ∧ s⁻¹ • y ∉ M} := by
    ext w
    rw [Set.mem_inv_smul_set_iff₀ hs.ne']
    show s • w ∈ M ∧ w ∉ M ↔ s • w ∈ M ∧ s⁻¹ • s • w ∉ M
    rw [inv_smul_smul₀ hs.ne']
  rw [hset, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hs.ne'),
    hkey _ (inv_pos.2 hs), smul_zero]
/-- Set-lintegrals agree when the sets and the integrands agree on a null-measurable set `G`
off which both sets are null (used for the rescaling invariance of tangent cones, Simon Ch. 8,
5.3 and 5.7): if `μ (D \ G) = μ (D' \ G) = 0`, `x ∈ D ↔ x ∈ D'` and `f x = g x` for `x ∈ G`,
then `∫⁻_D f dμ = ∫⁻_{D'} g dμ`.  `D`, `D'`, `f`, `g` are arbitrary and `μ` need not be
σ-finite. -/
theorem Submission.allard_tc_cri_setLIntegral_congr_off_null :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (G D D' : Set (Euclidean N)) (f g : Euclidean N → ℝ≥0∞), NullMeasurableSet G μ → μ (D \ G) = 0 → μ (D' \ G) = 0 → (∀ x ∈ G, x ∈ D ↔ x ∈ D') → (∀ x ∈ G, f x = g x) → ∫⁻ x in D, f x ∂μ = ∫⁻ x in D', g x ∂μ := by
  intro N μ G D D' f g hG hD hD' hDD' hfg
  -- Step 1: `D \ D' ⊆ D \ G` and `D' \ D ⊆ D' \ G`, so `D =ᵐ[μ] D'`.
  have hDeq : D =ᵐ[μ] D' := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ hD, measure_mono_null ?_ hD'⟩
    · rintro x ⟨hxD, hxD'⟩
      exact ⟨hxD, fun hxG ↦ hxD' ((hDD' x hxG).1 hxD)⟩
    · rintro x ⟨hxD', hxD⟩
      exact ⟨hxD', fun hxG ↦ hxD ((hDD' x hxG).2 hxD')⟩
  -- Step 2: a measurable kernel `Z ⊆ G` with `μ (G \ Z) = 0`.
  obtain ⟨Z, hZG, hZ, hZae⟩ := hG.exists_measurable_subset_ae_eq
  have hGZ : μ (G \ Z) = 0 := (ae_eq_set.1 hZae).2
  -- Step 3: `(μ.restrict D) Zᶜ = μ (Zᶜ ∩ D) = 0`, as `Zᶜ ∩ D ⊆ (D \ G) ∪ (G \ Z)`.
  have hZc : μ.restrict D Zᶜ = 0 := by
    rw [Measure.restrict_apply hZ.compl]
    refine measure_mono_null ?_ (measure_union_null hD hGZ)
    rintro x ⟨hxZ, hxD⟩
    by_cases hxG : x ∈ G
    · exact Or.inr ⟨hxG, hxZ⟩
    · exact Or.inl ⟨hxD, hxG⟩
  -- Step 4: `{x | f x ≠ g x} ⊆ Zᶜ`, so `f = g` `(μ.restrict D)`-a.e.
  have hfg_ae : f =ᵐ[μ.restrict D] g :=
    ae_iff.2 (measure_mono_null (fun x hx hxZ ↦ hx (hfg x (hZG hxZ))) hZc)
  -- Step 5: `lintegral_congr_ae`, then `μ.restrict D = μ.restrict D'` (`setLIntegral_congr`).
  exact (lintegral_congr_ae hfg_ae).trans (setLIntegral_congr hDeq)
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
/-- An `n`-plane `T ∈ G(N,n)` is determined by the `H^n`-integrals over it of compactly supported
continuous functions (the plane half of the step `Θ^n(μ_C, λy) = Θ^n(μ_C, y)` in the proof of
Simon Ch. 8, 5.7): equal integrals force `H^n ⌞ T' = H^n ⌞ T` (uniqueness in the Riesz
representation for regular measures), so the supports `T'.plane` and `T.plane` agree, and a point
of `G(N,n)` is the matrix of the orthogonal projection onto its plane. -/
theorem Submission.allard_tc_tpd_plane_eq_of_integral_eq :
    ∀ (N n : ℕ) (T T' : Grassmannian N n), (∀ g : C_c(Euclidean N, ℝ), ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] = ∫ y in (T'.plane : Set (Euclidean N)), g y ∂μHE[n]) → T' = T := by
  intro N n T T' h
  -- Steps 1–2: `finrank T.plane = finrank T'.plane = n`, so both restrictions of `H^n` are regular.
  have : ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))).Regular :=
    Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane
  have : ((μHE[n] : Measure (Euclidean N)).restrict (T'.plane : Set (Euclidean N))).Regular :=
    Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane
  -- Step 3: Riesz uniqueness, `H^n ⌞ T'.plane = H^n ⌞ T.plane`.
  have hμ : (μHE[n] : Measure (Euclidean N)).restrict (T'.plane : Set (Euclidean N)) =
      (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) :=
    Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ (h g).symm
  -- Step 4: the support of `H^n ⌞ P` is `P`, so `T'.plane = T.plane`.
  have hplane : T'.plane = T.plane := by
    apply SetLike.coe_injective
    rw [← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane,
      ← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane, hμ]
  -- Step 5: `p_S` is a symmetric idempotent, hence the orthogonal projection onto `S.plane`.
  have hproj : ∀ S : Grassmannian N n,
      S.projectionLinearMap = S.plane.starProjection.toLinearMap := fun S ↦
    (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
      ⟨S.projectionLinearMap_comp_self, S.projectionLinearMap_isSymmetric⟩).2
  -- Step 6: compare coordinate matrices.
  apply Subtype.ext
  rw [← T'.toMatrix_projectionLinearMap, ← T.toMatrix_projectionLinearMap, hproj T', hproj T,
    hplane]
/-- The `n`-dimensional Hausdorff measure of the closed and open balls `B_r(0)` of an `n`-plane
`T ∈ G(N,n)` is `ω_n r^n` (step 6 of the flat blow-up ball limits used for Simon Ch. 8, 5.5):
`H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`. -/
theorem Submission.allard_tc_fbl_plane_ball_measure :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 < r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n ∧ (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ ball 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: a linear isometry `J : ℝ^n → ℝ^N` with range `T.plane`, from an orthonormal basis
  -- of `T.plane` indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  -- Step 2: `H^n (J '' E) = vol E` for every `E ⊆ ℝ^n`.
  have hmeas : ∀ E : Set (EuclideanSpace ℝ (Fin n)),
      (μHE[n] : Measure (Euclidean N)) (J '' E) = volume E := by
    intro E
    rw [J.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Step 3: `T.plane ∩ {‖w‖ ∈ A} = J '' {‖y‖ ∈ A}`, since `J` preserves norms and has range
  -- `T.plane`.
  have himage : ∀ A : Set ℝ,
      (T.plane : Set (Euclidean N)) ∩ {w | ‖w‖ ∈ A} = J '' {y | ‖y‖ ∈ A} := by
    intro A
    ext w
    constructor
    · rintro ⟨hw, hwA⟩
      refine ⟨b.repr ⟨w, hw⟩, ?_, ?_⟩
      · simpa using hwA
      · simp [J]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simp [J], by simpa using hy⟩
  have hcl : (T.plane : Set (Euclidean N)) ∩ closedBall 0 r = J '' closedBall 0 r := by
    simpa only [Set.mem_Iic, ← mem_closedBall_zero_iff, Set.ofPred_mem_eq] using himage (Set.Iic r)
  have hop : (T.plane : Set (Euclidean N)) ∩ ball 0 r = J '' ball 0 r := by
    simpa only [Set.mem_Iio, ← mem_ball_zero_iff, Set.ofPred_mem_eq] using himage (Set.Iio r)
  -- Steps 4–5: `vol (B_r(0)) = vol (B°_r(0)) = ω_n r^n` in `ℝ^n` (`r > 0`).
  have hcl_vol : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) =
      unitBallVolume n * ENNReal.ofReal r ^ n := by
    rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin,
      ENNReal.ofReal_pow hr.le, unitBallVolume, mul_comm]
  have hop_vol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      unitBallVolume n * ENNReal.ofReal r ^ n := by
    rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin,
      ENNReal.ofReal_pow hr.le, unitBallVolume, mul_comm]
  -- Step 6: conclusion.
  exact ⟨by rw [hcl, hmeas, hcl_vol], by rw [hop, hmeas, hop_vol]⟩
/-- The monotonicity identity 3.4 at every centre of a stationary varifold `C` on `ℝ^N` (Simon
Ch. 8, as used in the proof of 5.5): applying 3.4 with `U = ℝ^N` and `ρ₀ = k + 1` gives `θ_k` with
`θ_k + ω_n^{-1} ∫_{Gₙ(B_ρ(y))} r^{-n-2}|p_{S^⊥}(x-y)|² dC = μ_C(B_ρ(y))/(ω_n ρ^n)` for
`0 < ρ < k + 1`.  Limits along `ρ ↓ 0` are unique, so `θ_k = θ_0` and the identity holds for every
`ρ > 0`; the defect integral is monotone in the ball, so the density ratio is non-decreasing. -/
theorem Submission.allard_tc_scf_monotonicity_identity :
    StationaryMonotonicityIdentity → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))), C.Stationary → ∀ y : Euclidean N, (∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ∀ ρ : ℝ, 0 < ρ → θ + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) = densityRatio n C.weight y ρ) ∧ MonotoneOn (densityRatio n C.weight y) (Ioi 0) := by
  intro hSMI N n C hC y
  -- Step 1: 3.4 with `U = ℝ^N` and `ρ₀ = k + 1`; global stationarity gives the local premise.
  have hlocal : ∀ k : ℕ, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < (k : ℝ) + 1 →
        θ + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) =
          densityRatio n C.weight y ρ := fun k ↦
    hSMI N n univ C y ((k : ℝ) + 1) (by positivity) (subset_univ _) (fun X _ ↦ hC X)
  choose θ hθ hid using hlocal
  -- Step 2: limits along `𝓝[>] 0` are unique, so `θ_k = θ_0`.
  have hθk : ∀ k, θ k = θ 0 := fun k ↦ tendsto_nhds_unique (hθ k) (hθ 0)
  -- Step 3: every `ρ > 0` lies below some `k + 1`.
  have hall : ∀ ρ : ℝ, 0 < ρ →
      θ 0 + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) =
        densityRatio n C.weight y ρ := by
    intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_gt ρ
    rw [← hθk k]
    exact hid k ρ hρ (by linarith)
  refine ⟨⟨θ 0, hθ 0, hall⟩, ?_⟩
  -- Step 4: `B_ρ(y) ⊆ B_ρ'(y)`, and a set lintegral is monotone in the set.
  intro ρ hρ ρ' hρ' hle
  rw [← hall ρ hρ, ← hall ρ' hρ']
  gcongr
  exact lintegral_mono_set (prod_mono (closedBall_subset_closedBall hle) subset_rfl)
/-- Density ratios are bounded by the ball-mass constant about `0` (Simon Ch. 8, the display before
5.5(2)): if `ρ ↦ μ(B_ρ(y))/(ω_n ρ^n)` is non-decreasing on `(0,∞)` for every `y` and
`μ(B_ρ(0)) = a ω_n ρ^n` for every `ρ > 0`, then for `ρ' ≥ ρ`, using `B_{ρ'}(y) ⊆ B_{ρ'+|y|}(0)`,
`μ(B_ρ(y))/(ω_n ρ^n) ≤ μ(B_{ρ'}(y))/(ω_n ρ'^n) ≤ a (1 + |y|/ρ')^n → a` as `ρ' → ∞`. -/
theorem Submission.allard_tc_scf_ratio_le :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (a : ℝ≥0∞), (∀ y : Euclidean N, MonotoneOn (densityRatio n μ y) (Ioi 0)) → (∀ ρ : ℝ, 0 < ρ → μ (closedBall 0 ρ) = a * unitBallVolume n * ENNReal.ofReal ρ ^ n) → ∀ (y : Euclidean N) (ρ : ℝ), 0 < ρ → densityRatio n μ y ρ ≤ a := by
  intro N n μ a hmono hball y ρ hρ
  -- Step 1: `ω_n ∈ (0, ∞)`.
  have hω₀ : unitBallVolume n ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Steps 2–4: for every `ρ' ≥ ρ`, `R(y, ρ) ≤ R(y, ρ') ≤ a (1 + |y|/ρ')^n`.
  have hbound : ∀ ρ' : ℝ, ρ ≤ ρ' →
      densityRatio n μ y ρ ≤ a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n) := by
    intro ρ' hρρ'
    have hρ' : 0 < ρ' := hρ.trans_le hρρ'
    have hsub : closedBall y ρ' ⊆ closedBall 0 (ρ' + ‖y‖) :=
      closedBall_subset_closedBall' (by rw [dist_zero_right])
    have hmass : μ (closedBall y ρ') ≤ a * unitBallVolume n * ENNReal.ofReal (ρ' + ‖y‖) ^ n :=
      (measure_mono hsub).trans_eq (hball _ (by positivity))
    calc densityRatio n μ y ρ ≤ densityRatio n μ y ρ' := hmono y hρ hρ' hρρ'
      _ ≤ a * unitBallVolume n * ENNReal.ofReal (ρ' + ‖y‖) ^ n /
            (unitBallVolume n * ENNReal.ofReal ρ' ^ n) := ENNReal.div_le_div_right hmass _
      _ = a * (ENNReal.ofReal (ρ' + ‖y‖) ^ n / ENNReal.ofReal ρ' ^ n) := by
        rw [mul_comm a, mul_assoc, ENNReal.mul_div_mul_left _ _ hω₀ hω, mul_div_assoc]
      _ = a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hρ'.le,
          ← ENNReal.ofReal_div_of_pos (pow_pos hρ' n), ← div_pow, add_div, div_self hρ'.ne']
  -- Step 6: `a (1 + |y|/ρ')^n → a` as `ρ' → ∞`.
  have hlim : Tendsto (fun ρ' : ℝ ↦ a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n)) atTop (𝓝 a) := by
    have h : Tendsto (fun ρ' : ℝ ↦ (1 + ‖y‖ / ρ') ^ n) atTop (𝓝 ((1 + 0) ^ n)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).pow n
    rw [add_zero, one_pow] at h
    have h' := ENNReal.Tendsto.const_mul (a := a) (ENNReal.tendsto_ofReal h)
      (Or.inl (by rw [ENNReal.ofReal_one]; exact one_ne_zero))
    rwa [ENNReal.ofReal_one, mul_one] at h'
  -- Steps 5 and 7: `R(y, ρ)` is eventually below a quantity tending to `a`.
  exact ge_of_tendsto hlim ((eventually_ge_atTop ρ).mono hbound)
/-- Density ratios at points of `spt μ` are bounded below by an a.e. lower bound of the density
(the step "(and hence for every `y ∈ spt μ_C` by 3.4)" after Simon Ch. 8, 5.5(7)): if `μ` is finite
on closed balls, `ρ ↦ R(x, ρ) = μ(B_ρ(x))/(ω_n ρ^n)` is non-decreasing on `(0, ∞)` for every `x`
and `Θ^n(μ, x) ≥ a` for `μ`-a.e. `x`, then `a ≤ R(y, ρ)` for `y ∈ spt μ` and `ρ > 0`.  Each open
ball of radius `1/(k+1)` about `y` contains a point `y_k` with
`a ≤ Θ^n(μ, y_k) ≤ R(y_k, ρ) ≤ μ(B_{ρ+1/(k+1)}(y))/(ω_n ρ^n)`, and continuity from above for the
decreasing closed balls `B_{ρ+1/(k+1)}(y)` lets `k → ∞`. -/
theorem Submission.allard_tc_scf_ratio_ge_on_support :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (a : ℝ≥0∞), (∀ (y : Euclidean N) (ρ : ℝ), μ (closedBall y ρ) ≠ ∞) → (∀ y : Euclidean N, MonotoneOn (densityRatio n μ y) (Ioi 0)) → (∀ᵐ y ∂μ, ∃ θ : ℝ≥0∞, HasDensity n μ y θ ∧ a ≤ θ) → ∀ y ∈ μ.support, ∀ ρ : ℝ, 0 < ρ → a ≤ densityRatio n μ y ρ := by
  intro N n μ a hfin hmono hae y hy ρ hρ
  -- Step 1: `c = ω_n ρ^n ∈ (0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ).ne')
  have hct : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- Step 2: the density at any point is at most its density ratio at radius `ρ`.
  have hdens : ∀ (x : Euclidean N) (θ : ℝ≥0∞), HasDensity n μ x θ →
      θ ≤ densityRatio n μ x ρ := by
    intro x θ hx
    refine le_of_tendsto hx ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with s hs
    exact hmono x hs.1 hρ hs.2.le
  -- Steps 3–5: a point `z ∈ B°_{1/(k+1)}(y)` of density `θ ≥ a` exists since `y ∈ spt μ`, and
  -- `a ≤ θ ≤ R(z, ρ) ≤ μ(B_{ρ+1/(k+1)}(y))/c`.
  have hk : ∀ k : ℕ, a * (unitBallVolume n * ENNReal.ofReal ρ ^ n) ≤
      μ (closedBall y (ρ + 1 / ((k : ℝ) + 1))) := by
    intro k
    have hr : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨z, hz, θ, hzθ, haθ⟩ : ∃ z ∈ ball y (1 / ((k : ℝ) + 1)), ∃ θ : ℝ≥0∞,
        HasDensity n μ z θ ∧ a ≤ θ := by
      by_contra hcon
      have h0 : μ (ball y (1 / ((k : ℝ) + 1))) = 0 :=
        measure_mono_null (fun z hz hzθ ↦ hcon ⟨z, hz, hzθ⟩) (ae_iff.1 hae)
      exact ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hr)).ne' h0
    rw [← ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc a ≤ θ := haθ
      _ ≤ densityRatio n μ z ρ := hdens z θ hzθ
      _ ≤ μ (closedBall y (ρ + 1 / ((k : ℝ) + 1))) /
          (unitBallVolume n * ENNReal.ofReal ρ ^ n) :=
        ENNReal.div_le_div_right (measure_mono (closedBall_subset_closedBall'
          (add_le_add le_rfl (mem_ball.1 hz).le))) _
  -- Step 6: continuity from above for the decreasing closed balls `B_{ρ+1/(k+1)}(y)`.
  have hinter : (⋂ k : ℕ, closedBall y (ρ + 1 / ((k : ℝ) + 1))) = closedBall y ρ := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    refine ⟨fun h ↦ ?_, fun h k ↦ h.trans (le_add_of_nonneg_right Nat.one_div_pos_of_nat.le)⟩
    by_contra hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hlt))
    linarith [h k]
  have htend : Tendsto (fun k : ℕ ↦ μ (closedBall y (ρ + 1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (μ (closedBall y ρ))) := by
    rw [← hinter]
    exact tendsto_measure_iInter_atTop (fun _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun i j hij ↦ closedBall_subset_closedBall
        (add_le_add le_rfl (Nat.one_div_le_one_div hij))) ⟨0, hfin _ _⟩
  -- Step 7: pass to the limit and divide by `c`.
  exact (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).2 (ge_of_tendsto' htend hk)
/-- Vanishing normal defect about `y` gives `x - y ∈ S` at every `(x, S) ∈ spt V` (Simon Ch. 8,
proof of 5.5, p. 217, display (8)): if `∫_{Gₙ(B_ρ(y))} |x - y|^{-n-2} |p_{S^⊥}(x - y)|² dV = 0` for
every `ρ > 0`, then `p_{S^⊥}(x - y) = 0` for `V`-a.e. `(x, S)`, hence, by continuity of
`p_{S^⊥}(x - y)` in `(x, S)`, at every point of `spt V`. -/
theorem Submission.allard_tc_scf_zero_defect_mem_plane :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (y : Euclidean N), (∀ ρ : ℝ, 0 < ρ → normalDefect V y (closedBall y ρ) = 0) → ∀ z ∈ V.measure.support, z.1 - y ∈ z.2.plane := by
  intro N n U V y h z hz
  -- Step 1: `(S, v) ↦ p_S(v)` is continuous (`S ↦ p_S` is the restriction to `G(N,n)` of a linear
  -- map on the finite-dimensional matrix space), so `w(x, S) = (x - y) - p_S(x - y)` is too.
  let Φ : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N) :=
    (LinearMap.toContinuousLinearMap :
        (Euclidean N →ₗ[ℝ] Euclidean N) ≃ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N)).toLinearMap.comp
      (LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis).symm.toLinearMap
  have hp : Continuous (fun p : Grassmannian N n × Euclidean N ↦ Grassmannian.project p.1 p.2) :=
    (Φ.continuous_of_finiteDimensional.comp (continuous_subtype_val.comp continuous_fst)).clm_apply
      continuous_snd
  have hg : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (z.2, z.1 - y)) :=
    continuous_snd.prodMk (continuous_fst.sub continuous_const)
  have hpg := hp.comp hg
  have hw : Continuous (fun z : Euclidean N × Grassmannian N n ↦
      (z.1 - y) - Grassmannian.project z.2 (z.1 - y)) :=
    (continuous_fst.sub continuous_const).sub hpg
  -- Step 2: the defect integrand is measurable.
  have hmeas : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      ENNReal.ofReal (‖(z.1 - y) - Grassmannian.project z.2 (z.1 - y)‖ ^ 2 /
        ‖z.1 - y‖ ^ (n + 2))) :=
    ENNReal.measurable_ofReal.comp ((hw.norm.pow 2).measurable.div
      ((continuous_fst.sub continuous_const).norm.pow (n + 2)).measurable)
  -- Steps 3–4: for each `k`, `w = 0` at `V`-a.e. point of `B_{k+1}(y) × G(N,n)`.
  have hball : ∀ k : ℕ, ∀ᵐ z ∂V.measure,
      z ∈ closedBall y ((k : ℝ) + 1) ×ˢ (univ : Set (Grassmannian N n)) →
        (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 := by
    intro k
    have h0 := (lintegral_eq_zero_iff hmeas).mp (h ((k : ℝ) + 1) (by positivity))
    filter_upwards [(ae_restrict_iff' (measurableSet_closedBall.prod MeasurableSet.univ)).mp h0]
      with z hzero hzk
    by_cases hzy : z.1 - y = 0
    · -- At `x = y`: `w = 0 - p_S(0) = 0`.
      rw [hzy, sub_eq_zero]
      exact (map_zero z.2.projectionLinearMap).symm
    · -- Off `x = y`: `|w|² / |x - y|^{n+2} ≤ 0` with a positive denominator, so `|w|² ≤ 0`.
      have hpos : 0 < ‖z.1 - y‖ ^ (n + 2) := pow_pos (norm_pos_iff.mpr hzy) _
      have hle := ENNReal.ofReal_eq_zero.mp (hzero hzk)
      rw [div_le_iff₀ hpos, zero_mul] at hle
      exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hle (sq_nonneg _)))
  -- Step 5: the balls `B_{k+1}(y)` exhaust `ℝ^N`, so `w = 0` `V`-a.e.
  have hae : ∀ᵐ z ∂V.measure, (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 := by
    filter_upwards [ae_all_iff.mpr hball] with z hzero
    obtain ⟨k, hk⟩ := exists_nat_ge ‖z.1 - y‖
    refine hzero k ⟨?_, mem_univ _⟩
    rw [mem_closedBall, dist_eq_norm]
    linarith
  -- Step 6: `{w = 0}` is closed and of full measure, so it contains `spt V`.
  have hz0 : (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 :=
    Measure.support_subset_of_isClosed (isClosed_eq hw continuous_const) hae hz
  -- Step 7: `p_S(x - y) = x - y`, so `x - y` lies in the range of `p_S`, which is `S.plane`.
  exact ⟨z.1 - y, (sub_eq_zero.mp hz0).symm⟩
/-- A linear subspace `P` of `ℝ^N` with `dim P = n` is an `n`-dimensional `C²` submanifold in
Simon's sense (Ch. 2, §4), so the Constancy Theorem 4.1 applies with `M = P` (step 7(b) of the proof
that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`, used for Simon Ch. 8, 5.5): a linear
isometry `J : ℝ^n → ℝ^N` with range `P` is a single global chart `(ℝ^n, ℝ^N, J)`. -/
theorem Submission.allard_tc_scf_subspace_submanifold :
    ∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)), Module.finrank ℝ P = n → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 (P : Set (Euclidean N)) := by
  intro N n P hP
  -- Step 1: a linear isometry `J : ℝ^n → ℝ^N` with range `P`, from an orthonormal basis of `P`
  -- indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ P := (stdOrthonormalBasis ℝ P).reindex (finCongr hP)
  let e : Euclidean n ≃ₗᵢ[ℝ] P := b.repr.symm
  let J : Euclidean n →L[ℝ] Euclidean N := P.subtypeL.comp (e : Euclidean n →L[ℝ] P)
  have hJ : Isometry J :=
    AddMonoidHomClass.isometry_of_norm J fun x ↦ (Submodule.norm_coe (e x)).trans (e.norm_map x)
  have hrange : range J = (P : Set (Euclidean N)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hw
      exact ⟨e.symm ⟨w, hw⟩, by simp [J]⟩
  -- Steps 2–3: `1 ≤ 2`, and the single global chart `(V', W, φ) = (ℝ^n, ℝ^N, J)` at every `y ∈ P`.
  refine ⟨by norm_num, fun y _ ↦ ⟨univ, univ, J, mem_univ y, isOpen_univ, isOpen_univ,
    J.contDiff.contDiffOn, hJ.injective.injOn, ?_, ?_, ?_⟩⟩
  · -- (d) `J(ℝ^n) = range J = P = ℝ^N ∩ P`.
    rw [image_univ, hrange, univ_inter]
  · -- (e) `J` is proper: an isometry is a closed embedding, so compact sets have compact preimages.
    intro K hK _
    rw [univ_inter]
    exact hJ.isClosedEmbedding.isCompact_preimage hK
  · -- (f) `DJ(x) = J` is injective.
    intro x _
    rw [J.fderiv]
    exact hJ.injective
/-- **Simon Ch. 8, proof of 5.5, p. 215, the plane's classical tangent space** (child
`subspace_tangent` of `stationary_cone_flat`, step 7): for a linear subspace `P` of `ℝ^N` and
`y ∈ P`, the classical tangent space `T_y P` (Ch. 2, §4) is `P` itself. A velocity `γ'(0)` is the
limit of the difference quotients `t⁻¹(γ(t) - y) ∈ P` and `P` is closed (finite-dimensional);
conversely `ξ ∈ P` is the velocity of the line `s ↦ y + sξ`, which stays in `P`. -/
theorem Submission.allard_tc_scf_subspace_classical_tangent :
    ∀ (N : ℕ) (P : Submodule ℝ (Euclidean N)) (y : Euclidean N), y ∈ P →
      classicalTangentSpace (P : Set (Euclidean N)) y = (P : Set (Euclidean N)) := by
  intro N P y hy
  ext ξ
  constructor
  · rintro ⟨γ, -, hγP, hγ0, hγ⟩
    -- `t⁻¹ • (γ t - γ 0) → ξ` as `t → 0`, `t ≠ 0`; for `t ∈ (-1,1)` these quotients lie in `P`,
    -- and `P` is closed.
    refine P.closed_of_finiteDimensional.mem_of_tendsto hγ.tendsto_slope_zero ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)]
      with t ht
    rw [zero_add, hγ0]
    exact P.smul_mem _ (P.sub_mem (hγP ht) hy)
  · intro hξ
    -- The line `s ↦ y + s • ξ` lies in `P` and has velocity `ξ`.
    refine ⟨fun s ↦ y + s • ξ, ?_, fun s _ ↦ P.add_mem hy (P.smul_mem s hξ), by simp, ?_⟩
    · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add y
/-- **Simon Ch. 8, 4.1 for a plane** (child `constancy_plane` of `stationary_cone_flat`; the step
"`C = θ₀ v(T)` by Constancy 4.1" in the proof of 5.5): a stationary `n`-varifold `C` on `ℝ^N` with
`spt μ_C ⊆ T` is `θ v(T)` for a constant `θ ≥ 0`.  `ConstancyTheorem` applies with `U = ℝ^N` and
`M = T`: `T` is a `C²` submanifold (`allard_tc_scf_subspace_submanifold`) and `T ∩ ℝ^N = T` is
convex, hence connected.  Since `T_x T = T` (`allard_tc_scf_subspace_classical_tangent`) and a point
of `G(N,n)` is determined by its plane, the constancy set of `A` is `{x ∈ T : (x, T) ∈ A}`, whose
`H^n`-measure is `v(T)(A)`. -/
theorem Submission.allard_tc_scf_constancy_plane :
    ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N)))
      (T : Grassmannian N n), C.Stationary → C.weight.support ⊆ (T.plane : Set (Euclidean N)) →
      ∃ θ : ℝ, 0 ≤ θ ∧ C.measure = ENNReal.ofReal θ • planeVarifoldMeasure T := by
  intro hconst N n C T hC hspt
  obtain ⟨θ, hθ, hA⟩ := hconst N n univ C (T.plane : Set (Euclidean N)) hC
    (Submission.allard_tc_scf_subspace_submanifold N n T.plane T.finrank_plane)
    (fun x hx ↦ hspt hx.2)
    (by rw [inter_univ]; exact T.plane.convex.isPreconnected)
  refine ⟨θ, hθ, Measure.ext fun A hA' ↦ ?_⟩
  have hmeas : Measurable fun y : Euclidean N ↦ (y, T) := measurable_prodMk_right
  rw [hA A hA', Measure.smul_apply, smul_eq_mul, planeVarifoldMeasure,
    Measure.map_apply hmeas hA', Measure.restrict_apply (hmeas hA')]
  -- The constancy set of `A` is `{x ∈ T : (x, T) ∈ A}`.
  congr 2
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_univ, and_true, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, S, hS, hxS⟩
    rw [Submission.allard_tc_scf_subspace_classical_tangent N T.plane x hx] at hS
    -- A point of `G(N,n)` is determined by its plane: `S = ofSubmodule S.plane = T`.
    have hST : S = T := by
      rw [← S.ofSubmodule_plane, ← T.ofSubmodule_plane]
      congr 1
      exact SetLike.coe_injective hS
    rw [hST] at hxS
    exact ⟨hxS, hx⟩
  · rintro ⟨hxT, hx⟩
    exact ⟨hx, T, (Submission.allard_tc_scf_subspace_classical_tangent N T.plane x hx).symm, hxT⟩
/-- The plane varifold `v(T)` of an `n`-plane `T ∈ G(N,n)` has mass `ω_n r^n` over the cylinder
`B_r(0) × G(N,n)` (step 8 of the proof that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`,
used for Simon Ch. 8, 5.5): `v(T)(B_r(0) × G(N,n)) = H^n(B_r(0) ∩ T)`, and `H^n` is transported to
Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`. -/
theorem Submission.allard_tc_scf_plane_ball_mass :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 < r → planeVarifoldMeasure T (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n))) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: `v(T)(B_r(0) × G(N,n)) = H^n(B_r(0) ∩ T)`, by `map_apply` and `restrict_apply`.
  rw [planeVarifoldMeasure, Measure.map_apply measurable_prodMk_right
      (measurableSet_closedBall.prod MeasurableSet.univ), mk_preimage_prod_left (mem_univ T),
    Measure.restrict_apply measurableSet_closedBall]
  -- Step 2: a linear isometry `J : ℝ^n → ℝ^N` with range `T`, from an orthonormal basis of `T`
  -- indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  have hrange : range J = (T.plane : Set (Euclidean N)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact (b.repr.symm x).2
    · intro hw
      exact ⟨b.repr ⟨w, hw⟩, by simp [J]⟩
  -- Step 3: `H^n(B_r(0) ∩ T) = H^n(J⁻¹(B_r(0)))` and `J⁻¹(B_r(0)) = B_r(0) ⊆ ℝ^n`.
  have hpre : J ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext x
    simp
  rw [← hrange, ← J.isometry.euclideanHausdorffMeasure_preimage, hpre]
  -- Steps 4–6: `H^n` is Lebesgue measure on `ℝ^n` and `vol(B_r(0)) = ω_n r^n`.
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hr.le,
    finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le, unitBallVolume, mul_comm]
/-- **Simon Ch. 8, proof of 5.5, pp. 216–217: a stationary cone with density `≥ θ₀` a.e. is
`θ₀ v(T)`.** Let `C` be a stationary `n`-varifold on `ℝ^N` with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every
`ρ > 0` (printed (1)) and `Θ^n(μ_C, y) ≥ θ₀` for `μ_C`-a.e. `y` (printed (7)). By 3.4 at every
centre, `R(y, ρ) = μ_C(B_ρ(y))/(ω_n ρ^n) ≤ θ₀` for all `y` (printed (2)) and `R(y, ρ) ≥ θ₀` for
`y ∈ spt μ_C`, so `Θ^n(μ_C, y) = θ₀` and the normal defect about `y` vanishes; hence `x - y ∈ S` for
`y ∈ spt μ_C` and `(x, S) ∈ spt C` (printed (8)). As `0 ∈ spt μ_C = π(spt C)`, some `(0, T)` lies in
`spt C`, so `spt μ_C ⊆ T`; Constancy 4.1 gives `C = θ v(T)`, and the mass of `B_1(0)` gives
`θ = θ₀`. -/
theorem Submission.allard_tc_stationary_cone_flat :
    StationaryMonotonicityIdentity → ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (θ₀ : ℝ), 0 < θ₀ → C.Stationary → (∀ ρ : ℝ, 0 < ρ → C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n) → (∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal θ₀ ≤ θ) → ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T := by
  intro hSMI hconst N n C θ₀ hθ₀ hC hball hae
  -- Step 0: `θ₀` and `ω_n` lie in `(0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have ha0 : ENNReal.ofReal θ₀ ≠ 0 := (ENNReal.ofReal_pos.2 hθ₀).ne'
  -- Step 1: the monotonicity identity 3.4 at every centre; density ratios are non-decreasing.
  have hMI := Submission.allard_tc_scf_monotonicity_identity hSMI N n C hC
  have hmono : ∀ y, MonotoneOn (densityRatio n C.weight y) (Ioi 0) := fun y ↦ (hMI y).2
  -- Step 2: `R(y, ρ) ≤ θ₀` everywhere (printed (2)) and `θ₀ ≤ R(y, ρ)` on `spt μ_C` (by (7)).
  have hle := Submission.allard_tc_scf_ratio_le N n C.weight (ENNReal.ofReal θ₀) hmono hball
  have hge := Submission.allard_tc_scf_ratio_ge_on_support N n C.weight (ENNReal.ofReal θ₀)
    (fun y ρ ↦ C.weight_finite_on_compact _ (isCompact_closedBall y ρ) (subset_univ _)) hmono hae
  -- Step 3: at `y ∈ spt μ_C`, `R(y, ·) ≡ θ₀`, so `Θ^n(μ_C, y) = θ₀` and 3.4 reads
  -- `θ₀ + ω_n⁻¹ D_y(ρ) = θ₀`; as `θ₀ < ∞` and `ω_n⁻¹ ≠ 0`, the normal defect `D_y(ρ)` vanishes.
  have hdefect : ∀ y ∈ C.weight.support, ∀ ρ : ℝ, 0 < ρ →
      normalDefect C y (closedBall y ρ) = 0 := by
    intro y hy ρ hρ
    obtain ⟨θ, hθ, hid⟩ := (hMI y).1
    have hR : ∀ r : ℝ, 0 < r → densityRatio n C.weight y r = ENNReal.ofReal θ₀ := fun r hr ↦
      le_antisymm (hle y r hr) (hge y hy r hr)
    have hθa : θ = ENNReal.ofReal θ₀ := by
      refine tendsto_nhds_unique hθ (tendsto_const_nhds.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hR r hr).symm
    have h := hid ρ hρ
    rw [hθa, hR ρ hρ, ← add_zero (ENNReal.ofReal θ₀), add_assoc, zero_add,
      ENNReal.add_right_inj ENNReal.ofReal_ne_top] at h
    exact (mul_eq_zero.1 h).resolve_left (ENNReal.inv_ne_zero.2 hωt)
  -- Step 4: printed (8), `x - y ∈ S` for `y ∈ spt μ_C` and `(x, S) ∈ spt C`.
  have h8 : ∀ y ∈ C.weight.support, ∀ z ∈ C.measure.support, z.1 - y ∈ z.2.plane :=
    fun y hy ↦ Submission.allard_tc_scf_zero_defect_mem_plane N n univ C y (hdefect y hy)
  -- Step 5: `0 ∈ spt μ_C`, since every ball about `0` has mass `θ₀ ω_n ρ^n > 0`.
  have h0 : (0 : Euclidean N) ∈ C.weight.support := by
    rw [Measure.mem_support_iff_forall]
    intro s hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
    refine lt_of_lt_of_le ?_ (measure_mono ((closedBall_subset_ball (half_lt_self hε)).trans hεs))
    rw [hball _ (half_pos hε)]
    exact pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero ha0 hω0)
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 (half_pos hε)).ne'))
  -- Step 6: `spt μ_C ⊆ π(spt C)`, as `π(spt C)` is closed (`G(N,n)` is compact) and `μ_C`-conull;
  -- so some `(0, T)` lies in `spt C`.
  obtain ⟨T, hT⟩ : ∃ T : Grassmannian N n, ((0 : Euclidean N), T) ∈ C.measure.support := by
    have hc : IsClosed (Prod.fst '' C.measure.support) :=
      isClosedMap_fst_of_compactSpace _ C.measure.isClosed_support
    have hsub : C.weight.support ⊆ Prod.fst '' C.measure.support := by
      refine Measure.support_subset_of_isClosed hc ?_
      change ∀ᵐ x ∂C.measure.map Prod.fst, x ∈ Prod.fst '' C.measure.support
      refine (ae_map_iff measurable_fst.aemeasurable hc.measurableSet).2 ?_
      filter_upwards [C.measure.support_mem_ae] with z hz
      exact mem_image_of_mem Prod.fst hz
    obtain ⟨⟨x, S⟩, hS, hx⟩ := hsub h0
    obtain rfl : x = 0 := hx
    exact ⟨S, hS⟩
  -- Step 7: `spt μ_C ⊆ T`, since (8) at `(x, S) = (0, T)` gives `-y ∈ T`.
  have hspt : C.weight.support ⊆ (T.plane : Set (Euclidean N)) := by
    intro y hy
    have h : (0 : Euclidean N) - y ∈ T.plane := h8 y hy ((0 : Euclidean N), T) hT
    rw [zero_sub] at h
    simpa using T.plane.neg_mem h
  -- Step 8: Constancy 4.1 gives `C = θ v(T)` with `θ ≥ 0`.
  obtain ⟨θ, -, hCθ⟩ := Submission.allard_tc_scf_constancy_plane hconst N n C T hC hspt
  -- Step 9: `μ_C(B_1(0)) = θ ω_n = θ₀ ω_n` and `ω_n ∈ (0, ∞)`, so `θ = θ₀`.
  have h1 := hball 1 one_pos
  rw [C.weight_apply measurableSet_closedBall, hCθ, Measure.smul_apply, smul_eq_mul,
    Submission.allard_tc_scf_plane_ball_mass N n T 1 one_pos, ENNReal.ofReal_one, one_pow,
    mul_one, mul_one, ENNReal.mul_left_inj hω0 hωt] at h1
  exact ⟨T, by rw [hCθ, h1]⟩
/-- Lebesgue density theorem for a measure `μ` on `ℝ^N` that vanishes off an open set `U` and is
finite on compact subsets of `U` (Simon Ch. 8, Remark 5.6(iii), localized as in Simon Ch. 1, 3.23):
for measurable `A` and `μ`-a.e. `x`, `μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 1_A(x)` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_dbd_lebesgue_density :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → ∀ A : Set (Euclidean N), MeasurableSet A → ∀ᵐ x ∂μ, Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (A.indicator 1 x)) := by
  intro N U μ hU hUc hK A hA
  -- Step 1: the countable family of compact balls `K_i = B_r(q) ⊆ U`, `i = (q, r) ∈ I`, with `q`
  -- in a countable dense set `D` and `r ∈ ℚ_{>0}`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euclidean N)
  let I : Set (Euclidean N × ℚ) := {i | i.1 ∈ D ∧ 0 < i.2 ∧ closedBall i.1 (i.2 : ℝ) ⊆ U}
  have hIc : I.Countable :=
    (hDc.prod (countable_univ (α := ℚ))).mono fun i hi ↦ mem_prod.2 ⟨hi.1, mem_univ _⟩
  -- Steps 3–4: Besicovitch differentiation for each finite measure `μ ⌞ K_i`, off one `μ`-null set.
  have hball : ∀ᵐ x ∂μ, ∀ i ∈ I, x ∈ closedBall i.1 (i.2 : ℝ) →
      Tendsto (fun ρ : ℝ ↦ μ.restrict (closedBall i.1 (i.2 : ℝ)) (A ∩ closedBall x ρ) /
          μ.restrict (closedBall i.1 (i.2 : ℝ)) (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (A.indicator 1 x)) := by
    refine (ae_ball_iff hIc).2 fun i hi ↦ ?_
    have : IsFiniteMeasure (μ.restrict (closedBall i.1 (i.2 : ℝ))) :=
      isFiniteMeasure_restrict.2 (hK _ (isCompact_closedBall _ _) hi.2.2)
    exact (ae_restrict_iff' measurableSet_closedBall).1
      (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _ hA)
  filter_upwards [hball, mem_ae_iff.2 hUc] with x hx hxU
  -- Steps 2 and 5: some `i = (q, r) ∈ I` with `dist x q < r`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (half_pos hε)
  obtain ⟨q, hqD, hqx⟩ := hDd.exists_mem_open isOpen_ball ⟨x, mem_ball_self hr0⟩
  have hxq : dist x q < r := by rw [dist_comm]; exact mem_ball.1 hqx
  have hi : (q, r) ∈ I := by
    have h1 : (r : ℝ) + dist q x < ε := by linarith [mem_ball.1 hqx]
    exact ⟨hqD, Rat.cast_pos.1 hr0, (closedBall_subset_ball' h1).trans hεU⟩
  -- Step 6: for `0 < ρ < r - dist x q`, `B_ρ(x) ⊆ K_i`, so the two ratios agree near `0`.
  refine (hx (q, r) hi (mem_closedBall.2 hxq.le)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hxq)] with ρ hρ
  have hsub : closedBall x ρ ⊆ closedBall q r := closedBall_subset_closedBall' (by linarith [hρ.2])
  rw [Measure.restrict_apply' measurableSet_closedBall,
    Measure.restrict_apply' measurableSet_closedBall, inter_assoc, inter_eq_left.2 hsub]
/-- Relative density zero at a point of finite density gives `o(ρ^n)` mass (closing steps 8–9 of
the density blow-up decay for Simon Ch. 8, 5.6(iii)): if `Θ^n(μ, x) = θ < ∞`,
`μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 0` as `ρ ↓ 0` and `μ`-a.e. point of `E` lies in `A`, then
`μ(B_ρ(x) ∩ E) / ρ^n → 0` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_dbd_relative_decay :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞) (A E : Set (Euclidean N)), HasDensity n μ x θ → θ ≠ ∞ → Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → (∀ᵐ y ∂μ, y ∈ E → y ∈ A) → Tendsto (fun ρ : ℝ ↦ μ (closedBall x ρ ∩ E) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro N n μ x θ A E hθ hθ_ne hκ hAE
  -- Step 1: `0 < ω_n < ∞`.
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Step 2: `μ(B_ρ) / ρ^n = ω_n · densityRatio ρ → ω_n θ ≠ ∞`.
  have hf_eq : ∀ ρ : ℝ, μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n =
      unitBallVolume n * densityRatio n μ x ρ := fun ρ ↦ by
    rw [densityRatio, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hω0 hωtop]
  have hf : Tendsto (fun ρ : ℝ ↦ μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0)
      (𝓝 (unitBallVolume n * θ)) := by
    simp_rw [hf_eq]
    exact ENNReal.Tendsto.const_mul hθ (Or.inr hωtop)
  have hωθ : unitBallVolume n * θ ≠ ∞ := ENNReal.mul_ne_top hωtop hθ_ne
  -- Step 3: `κ(ρ) · μ(B_ρ) / ρ^n → 0 · ω_n θ = 0`.
  have hprod : Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) *
      (μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul hκ (Or.inr hωθ) hf (Or.inr ENNReal.zero_ne_top)
  -- Step 4: eventually `μ(B_ρ) / ρ^n < ∞`.
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n < ∞ :=
    hf.eventually (gt_mem_nhds hωθ.lt_top)
  -- Step 6: squeeze `0 ≤ μ(B_ρ ∩ E) / ρ^n ≤ κ(ρ) · μ(B_ρ) / ρ^n`, the upper bound holding for
  -- every `ρ` of step 4.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hev] with ρ hρ
  -- Step 4, continued: `ρ^n ≠ ∞`, hence `μ(B_ρ) ≠ ∞`.
  have hP : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hB : μ (closedBall x ρ) ≠ ∞ := fun h ↦ by
    rw [h, ENNReal.top_div_of_ne_top hP] at hρ
    exact lt_irrefl _ hρ
  -- Step 5(a): `μ(B_ρ ∩ E) ≤ μ(A ∩ B_ρ)`, since `B_ρ ∩ E ⊆ A ∩ B_ρ` up to a `μ`-null set.
  have ha : μ (closedBall x ρ ∩ E) ≤ μ (A ∩ closedBall x ρ) :=
    measure_mono_ae (hAE.mono fun y hy hyBE ↦ ⟨hy hyBE.2, hyBE.1⟩)
  -- Step 5(b): `μ(A ∩ B_ρ) ≤ κ(ρ) · μ(B_ρ)`, the case `μ(B_ρ) = 0` separately.
  have hb : μ (A ∩ closedBall x ρ) ≤
      μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) * μ (closedBall x ρ) := by
    by_cases h0 : μ (closedBall x ρ) = 0
    · rw [h0, mul_zero]
      exact (measure_mono inter_subset_right).trans h0.le
    · exact (ENNReal.div_mul_cancel h0 hB).ge
  -- Step 5(c): divide by `ρ^n`.
  calc μ (closedBall x ρ ∩ E) / ENNReal.ofReal ρ ^ n
      ≤ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) * μ (closedBall x ρ) /
          ENNReal.ofReal ρ ^ n := ENNReal.div_le_div_right (ha.trans hb) _
    _ = _ := mul_div_assoc _ _ _

/-- Density blow-up decay (Simon Ch. 8, Remark 5.6(iii) and (3)–(4) in the proof of 5.5): assuming
3.6, if `V` has locally bounded first variation, then for `μ_V`-a.e. `x`, whenever
`Θ^n(μ_V, x) = θ₀` and `τ < θ₀`, `ρ^{-n} μ_V({y ∈ B_ρ(x) : not (Θ^n(μ_V, y) exists and is ≥ τ)})`
tends to `0` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_density_blowup_decay :
    DensityExistsAE → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → ∀ᵐ x ∂V.weight, ∀ θ₀ τ : ℝ, HasDensity n V.weight x (ENNReal.ofReal θ₀) → τ < θ₀ → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro hD N n U V hV
  -- Step 1: a Borel `Θ̃`, finite and equal to the density off a `μ_V`-null set.
  obtain ⟨Θ, hΘm, hΘ⟩ := hD N n U V hV
  -- Step 2: `μ_V(Uᶜ) = 0`.
  have hUc : V.weight Uᶜ = 0 := by
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  -- Steps 3–4: off one `μ_V`-null set, `x` is a Lebesgue density point of every
  -- `A_p = {Θ̃ < p}`, `p ∈ ℚ`.
  have hLeb : ∀ᵐ x ∂V.weight, ∀ p : ℚ,
      Tendsto (fun ρ : ℝ ↦ V.weight ({y | Θ y < ENNReal.ofReal p} ∩ closedBall x ρ) /
          V.weight (closedBall x ρ))
        (𝓝[>] 0) (𝓝 ({y | Θ y < ENNReal.ofReal p}.indicator 1 x)) :=
    ae_all_iff.2 fun p ↦ Submission.allard_tc_dbd_lebesgue_density N U V.weight V.isOpen_domain
      hUc V.weight_finite_on_compact _ (measurableSet_lt hΘm measurable_const)
  filter_upwards [hΘ, hLeb] with x hx hxL
  intro θ₀ τ hθ₀ hτ
  -- Step 5: `Θ̃(x) = θ₀`, so a rational `p ∈ (τ, θ₀)` has `x ∉ A_p`.
  have heq : Θ x = ENNReal.ofReal θ₀ := tendsto_nhds_unique hx.2 hθ₀
  obtain ⟨p, hτp, hpθ⟩ := exists_rat_btwn hτ
  have hxA : x ∉ {y | Θ y < ENNReal.ofReal p} := by
    rw [Set.mem_ofPred_eq, not_lt, heq]
    exact ENNReal.ofReal_le_ofReal hpθ.le
  -- Step 7: `μ_V(A_p ∩ B_ρ(x)) / μ_V(B_ρ(x)) → 0`.
  have hκ := hxL p
  rw [Set.indicator_of_notMem hxA] at hκ
  -- Steps 8–9: the relative decay, applied with `A = A_p` and `E = E_τ`.
  refine Submission.allard_tc_dbd_relative_decay N n V.weight x (ENNReal.ofReal θ₀)
    {y | Θ y < ENNReal.ofReal p}
    {y | ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ}
    hθ₀ ENNReal.ofReal_ne_top hκ ?_
  -- Step 6: `E_τ ⊆ Z ∪ A_p`.
  filter_upwards [hΘ] with y hy hyE
  by_contra hyA
  exact hyE ⟨Θ y, hy.2, (ENNReal.ofReal_le_ofReal hτp.le).trans (not_lt.1 hyA)⟩

/-- The plane integrals of the unit-ball cut-offs `φ_k⁺ = max(0, 1 - (k+1) max(0, |y| - 1))` and
`φ_k⁻ = min(1, (k+1) max(0, 1 - |y|))` over an `n`-plane `T ∈ G(N,n)` both converge to `ω_n`
(steps 5–6 of the flat blow-up ball limits used for Simon Ch. 8, 5.5): dominated convergence with
the bound `1_{B_2(0)}` and the pointwise limits `1_{B_1(0)}`, `1_{B°_1(0)}`, whose integrals are
`ω_n` by `allard_tc_fbl_plane_ball_measure`. -/
theorem Submission.allard_tc_fbl_plane_cutoff_limits :
    ∀ (N n : ℕ) (T : Grassmannian N n), Tendsto (fun k : ℕ ↦ ∫ y in (T.plane : Set (Euclidean N)), max 0 (1 - ((k : ℝ) + 1) * max 0 (‖y‖ - 1)) ∂(μHE[n] : Measure (Euclidean N))) atTop (𝓝 (unitBallVolume n).toReal) ∧ Tendsto (fun k : ℕ ↦ ∫ y in (T.plane : Set (Euclidean N)), min 1 (((k : ℝ) + 1) * max 0 (1 - ‖y‖)) ∂(μHE[n] : Measure (Euclidean N))) atTop (𝓝 (unitBallVolume n).toReal) := by
  intro N n T
  set μ : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hμ
  -- Step 1: masses of balls under `μ = H^n ⌞ T.plane`, from `allard_tc_fbl_plane_ball_measure`.
  have hball : ∀ r : ℝ, 0 < r → μ (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n ∧
      μ (ball 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
    intro r hr
    obtain ⟨h₁, h₂⟩ := Submission.allard_tc_fbl_plane_ball_measure N n T r hr
    rw [hμ, Measure.restrict_apply measurableSet_closedBall,
      Measure.restrict_apply measurableSet_ball, inter_comm, h₁, inter_comm, h₂]
    exact ⟨rfl, rfl⟩
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have h₂ : μ (closedBall 0 2) ≠ ∞ := by
    rw [(hball 2 two_pos).1]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h₁cl : μ (closedBall 0 1) = unitBallVolume n := by
    rw [(hball 1 one_pos).1, ENNReal.ofReal_one, one_pow, mul_one]
  have h₁op : μ (ball 0 1) = unitBallVolume n := by
    rw [(hball 1 one_pos).2, ENNReal.ofReal_one, one_pow, mul_one]
  -- Step 2: the dominating function `g = 1_{B_2(0)}` is `μ`-integrable.
  have hg : Integrable ((closedBall (0 : Euclidean N) 2).indicator 1) μ :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const (C := (1 : ℝ)) h₂)
  have hk : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k ↦ le_add_of_nonneg_left (Nat.cast_nonneg k)
  constructor
  · -- Steps 3–6 for `φ_k⁺`, with pointwise limit `1_{B_1(0)}`.
    have key := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (k : ℕ) (y : Euclidean N) ↦ max 0 (1 - ((k : ℝ) + 1) * max 0 (‖y‖ - 1)))
      (f := (closedBall (0 : Euclidean N) 1).indicator 1)
      ((closedBall (0 : Euclidean N) 2).indicator 1)
      (fun k ↦ by fun_prop) hg ?_ ?_
    · rwa [integral_indicator_one measurableSet_closedBall, Measure.real, h₁cl] at key
    · -- Step 3: `|φ_k⁺| ≤ 1_{B_2(0)}`.
      intro k
      refine Eventually.of_forall fun y ↦ ?_
      rcases le_or_gt ‖y‖ 2 with hy | hy
      · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hy), Pi.one_apply,
          Real.norm_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one
          (sub_le_self _ (mul_nonneg (zero_le_one.trans (hk k)) (le_max_left _ _)))
      · rw [indicator_of_notMem (fun h ↦ hy.not_ge (mem_closedBall_zero_iff.1 h)),
          max_eq_right (by linarith : (0 : ℝ) ≤ ‖y‖ - 1),
          max_eq_left (by nlinarith [hk k] : 1 - ((k : ℝ) + 1) * (‖y‖ - 1) ≤ 0), norm_zero]
    · -- Step 4(a): `φ_k⁺ → 1_{B_1(0)}` pointwise; the sequence is eventually constant.
      refine Eventually.of_forall fun y ↦ ?_
      rcases le_or_gt ‖y‖ 1 with hy | hy
      · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hy), Pi.one_apply]
        have h : ∀ k : ℕ, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖y‖ - 1)) = 1 := fun k ↦ by
          rw [max_eq_left (by linarith : ‖y‖ - 1 ≤ 0), mul_zero, sub_zero,
            max_eq_right zero_le_one]
        exact tendsto_const_nhds.congr fun k ↦ (h k).symm
      · rw [indicator_of_notMem (fun h ↦ hy.not_ge (mem_closedBall_zero_iff.1 h))]
        have h₁ : 0 < ‖y‖ - 1 := sub_pos.2 hy
        obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (‖y‖ - 1))
        rw [div_lt_iff₀ h₁] at hk₀
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eventually_ge_atTop k₀] with k hk'
        have h₃ : (k₀ : ℝ) ≤ k := Nat.cast_le.2 hk'
        rw [max_eq_right h₁.le]
        exact max_eq_left (by nlinarith)
  · -- Steps 3–6 for `φ_k⁻`, with pointwise limit `1_{B°_1(0)}`.
    have key := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (k : ℕ) (y : Euclidean N) ↦ min 1 (((k : ℝ) + 1) * max 0 (1 - ‖y‖)))
      (f := (ball (0 : Euclidean N) 1).indicator 1)
      ((closedBall (0 : Euclidean N) 2).indicator 1)
      (fun k ↦ by fun_prop) hg ?_ ?_
    · rwa [integral_indicator_one measurableSet_ball, Measure.real, h₁op] at key
    · -- Step 3: `|φ_k⁻| ≤ 1_{B_2(0)}`.
      intro k
      refine Eventually.of_forall fun y ↦ ?_
      rcases le_or_gt ‖y‖ 2 with hy | hy
      · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hy), Pi.one_apply,
          Real.norm_of_nonneg
            (le_min zero_le_one (mul_nonneg (zero_le_one.trans (hk k)) (le_max_left _ _)))]
        exact min_le_left _ _
      · rw [indicator_of_notMem (fun h ↦ hy.not_ge (mem_closedBall_zero_iff.1 h)),
          max_eq_left (by linarith : 1 - ‖y‖ ≤ 0), mul_zero, min_eq_right zero_le_one, norm_zero]
    · -- Step 4(b): `φ_k⁻ → 1_{B°_1(0)}` pointwise; the sequence is eventually constant.
      refine Eventually.of_forall fun y ↦ ?_
      rcases lt_or_ge ‖y‖ 1 with hy | hy
      · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), Pi.one_apply]
        have h₁ : 0 < 1 - ‖y‖ := sub_pos.2 hy
        obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (1 - ‖y‖))
        rw [div_lt_iff₀ h₁] at hk₀
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eventually_ge_atTop k₀] with k hk'
        have h₃ : (k₀ : ℝ) ≤ k := Nat.cast_le.2 hk'
        rw [max_eq_right h₁.le]
        exact min_eq_left (by nlinarith)
      · rw [indicator_of_notMem (fun h ↦ hy.not_gt (mem_ball_zero_iff.1 h))]
        have h : ∀ k : ℕ, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖y‖)) = 0 := fun k ↦ by
          rw [max_eq_left (by linarith : 1 - ‖y‖ ≤ 0), mul_zero, min_eq_right zero_le_one]
        exact tendsto_const_nhds.congr fun k ↦ (h k).symm
/-- Cut-off sandwich for the rescaled ball integral (flat blow-up ball limits for Simon Ch. 8, 5.5):
if `r > 0`, `B_{2r}(x) ⊆ U`, `β ≥ 0` is continuous on `G(N,n)` and `a = k + 1`, then
`∫ φ⁻ β dV_{x,r} ≤ r⁻ⁿ ∫_{B_r(x) × G(N,n)} β dV ≤ ∫ φ⁺ β dV_{x,r}`, where
`φ⁻(y) = min(1, a max(0, 1 - |y|))` and `φ⁺(y) = max(0, 1 - a max(0, |y| - 1))`. -/
theorem Submission.allard_tc_fbl_rescaled_sandwich :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (β : C(Grassmannian N n, ℝ)) (r : ℝ) (k : ℕ), 0 < r → closedBall x (2 * r) ⊆ U → (∀ S, 0 ≤ β S) → (∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2 ∂(rescaledMeasure V x r)) ≤ (∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / r ^ n ∧ (∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / r ^ n ≤ ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2 ∂(rescaledMeasure V x r) := by
  intro N n U V x β r k hr hU hβ
  -- Notation: `a = k + 1`, `B = B_r(x) × G`, `K = B_{2r}(x) × G`; `Φ(y,S) = (r⁻¹(y - x), S)`.
  set a : ℝ := (k : ℝ) + 1 with ha_def
  have ha : 1 ≤ a := by rw [ha_def]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set B : Set (Euclidean N × Grassmannian N n) := closedBall x r ×ˢ univ
  set K : Set (Euclidean N × Grassmannian N n) := closedBall x (2 * r) ×ˢ univ
  -- Step 1: `V(K) < ∞`, since `B_{2r}(x)` is compact and contained in `U`.
  have hKfin : V.measure K ≠ ∞ := V.finite_on_compact _ (isCompact_closedBall x (2 * r)) hU
  have hBm : MeasurableSet B := measurableSet_closedBall.prod MeasurableSet.univ
  have hBK : B ⊆ K := prod_mono (closedBall_subset_closedBall (by linarith)) subset_rfl
  -- `|β(S)| ≤ ‖β‖`, as `G` is compact. The cut-off facts of Step 2 are checked inline below.
  have hβb : ∀ S, ‖β S‖ ≤ ‖β‖ := β.norm_coe_le_norm
  -- Step 3: geometry of `Φ`: `‖Φ(y,S).1‖ = |y - x| / r`.
  have hnorm : ∀ z : Euclidean N × Grassmannian N n, ‖r⁻¹ • (z.1 - x)‖ = dist z.1 x / r := by
    intro z
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, dist_eq_norm, inv_mul_eq_div]
  have hB_iff : ∀ z, z ∈ B ↔ ‖r⁻¹ • (z.1 - x)‖ ≤ 1 := by
    intro z
    rw [hnorm, div_le_one hr]
    simp only [B, mem_prod, mem_closedBall, mem_univ, and_true]
  have hK_out : ∀ z, z ∉ K → 2 < ‖r⁻¹ • (z.1 - x)‖ := by
    intro z hz
    rw [hnorm, lt_div_iff₀ hr]
    simp only [K, mem_prod, mem_closedBall, mem_univ, and_true, not_le] at hz
    exact hz
  -- Step 4: change of variables, `∫ g dV_{x,r} = r⁻ⁿ ∫ g ∘ Φ dV` for continuous `g`.
  have hcv : ∀ g : Euclidean N × Grassmannian N n → ℝ, Continuous g →
      ∫ z, g z ∂(rescaledMeasure V x r) = r⁻¹ ^ n * ∫ z, g (r⁻¹ • (z.1 - x), z.2) ∂V.measure := by
    intro g hg
    have hΦ : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (r⁻¹ • (z.1 - x), z.2)) := by
      fun_prop
    rw [rescaledMeasure, integral_smul_measure,
      integral_map hΦ.measurable.aemeasurable hg.aestronglyMeasurable,
      ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.2 hr.le) n), smul_eq_mul]
  -- Step 5: the middle term is `r⁻ⁿ ∫ 1_B β dV`.
  have hmid : (∫ z in B, β z.2 ∂V.measure) / r ^ n =
      r⁻¹ ^ n * ∫ z, B.indicator (fun z ↦ β z.2) z ∂V.measure := by
    rw [integral_indicator hBm, inv_pow, div_eq_inv_mul]
  -- Step 6: a function bounded by `‖β‖` and vanishing off `K` is `V`-integrable.
  have hint : ∀ h : Euclidean N × Grassmannian N n → ℝ, AEStronglyMeasurable h V.measure →
      (∀ z, ‖h z‖ ≤ ‖β‖) → (∀ z, z ∉ K → h z = 0) → Integrable h V.measure := fun h hm hb h0 ↦
    (Measure.integrableOn_of_bounded hKfin hm (ae_of_all _ hb)).integrable_of_forall_notMem_eq_zero
      h0
  have hm_int : Integrable
      (fun z ↦ min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (fun z ↦ ?_) (fun z hz ↦ ?_)
    · have h0 : 0 ≤ min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) :=
        le_min zero_le_one (mul_nonneg (by linarith) (le_max_left _ _))
      calc ‖min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) * β z.2‖
          = min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) * ‖β z.2‖ := by
            rw [norm_mul, Real.norm_of_nonneg h0]
        _ ≤ 1 * ‖β‖ := mul_le_mul (min_le_left _ _) (hβb _) (norm_nonneg _) zero_le_one
        _ = ‖β‖ := one_mul _
    · have h2 := hK_out z hz
      have : max 0 (1 - ‖r⁻¹ • (z.1 - x)‖) = 0 := max_eq_left (by linarith)
      simp [this]
  have hp_int : Integrable
      (fun z ↦ max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (fun z ↦ ?_) (fun z hz ↦ ?_)
    · have h0 : 0 ≤ max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) := le_max_left _ _
      have h1 : max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) ≤ 1 :=
        max_le zero_le_one (by nlinarith [le_max_left (0 : ℝ) (‖r⁻¹ • (z.1 - x)‖ - 1)])
      calc ‖max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) * β z.2‖
          = max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) * ‖β z.2‖ := by
            rw [norm_mul, Real.norm_of_nonneg h0]
        _ ≤ 1 * ‖β‖ := mul_le_mul h1 (hβb _) (norm_nonneg _) zero_le_one
        _ = ‖β‖ := one_mul _
    · have h2 := hK_out z hz
      have h3 : max 0 (‖r⁻¹ • (z.1 - x)‖ - 1) = ‖r⁻¹ • (z.1 - x)‖ - 1 := max_eq_right (by linarith)
      have : max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) = 0 :=
        max_eq_left (by rw [h3]; nlinarith)
      simp [this]
  have hB_int : Integrable (B.indicator (fun z ↦ β z.2)) V.measure := by
    refine hint _ ((Continuous.aestronglyMeasurable (by fun_prop)).indicator hBm)
      (fun z ↦ (norm_indicator_le_norm_self _ _).trans (hβb _)) (fun z hz ↦ ?_)
    exact indicator_of_notMem (fun h ↦ hz (hBK h)) _
  -- Step 7: pointwise sandwich `φ⁻(Φ.1) β ≤ 1_B β ≤ φ⁺(Φ.1) β`.
  have hlow : ∀ z, min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) * β z.2 ≤
      B.indicator (fun z ↦ β z.2) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz]
      exact mul_le_of_le_one_left (hβ _) (min_le_left _ _)
    · rw [indicator_of_notMem hz]
      have h1 : 1 < ‖r⁻¹ • (z.1 - x)‖ := lt_of_not_ge fun h ↦ hz ((hB_iff z).2 h)
      have : max 0 (1 - ‖r⁻¹ • (z.1 - x)‖) = 0 := max_eq_left (by linarith)
      simp [this]
  have hup : ∀ z, B.indicator (fun z ↦ β z.2) z ≤
      max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) * β z.2 := by
    intro z
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz]
      have h1 := (hB_iff z).1 hz
      have : max 0 (‖r⁻¹ • (z.1 - x)‖ - 1) = 0 := max_eq_left (by linarith)
      simp [this]
    · rw [indicator_of_notMem hz]
      exact mul_nonneg (le_max_left _ _) (hβ _)
  -- Step 8: integrate, multiply by `r⁻ⁿ ≥ 0`, and change variables back.
  have hlow_eq : ∫ z, min 1 (a * max 0 (1 - ‖z.1‖)) * β z.2 ∂(rescaledMeasure V x r) =
      r⁻¹ ^ n * ∫ z, min 1 (a * max 0 (1 - ‖r⁻¹ • (z.1 - x)‖)) * β z.2 ∂V.measure :=
    hcv (fun z ↦ min 1 (a * max 0 (1 - ‖z.1‖)) * β z.2) (by fun_prop)
  have hup_eq : ∫ z, max 0 (1 - a * max 0 (‖z.1‖ - 1)) * β z.2 ∂(rescaledMeasure V x r) =
      r⁻¹ ^ n * ∫ z, max 0 (1 - a * max 0 (‖r⁻¹ • (z.1 - x)‖ - 1)) * β z.2 ∂V.measure :=
    hcv (fun z ↦ max 0 (1 - a * max 0 (‖z.1‖ - 1)) * β z.2) (by fun_prop)
  have hc : 0 ≤ r⁻¹ ^ n := pow_nonneg (inv_nonneg.2 hr.le) n
  rw [hlow_eq, hup_eq, hmid]
  exact ⟨mul_le_mul_of_nonneg_left (integral_mono hm_int hB_int hlow) hc,
    mul_le_mul_of_nonneg_left (integral_mono hB_int hp_int hup) hc⟩
/-- Squeeze along a filter by approximating families (the `ε`-argument closing the flat blow-up
ball limits used for Simon Ch. 8, 5.5): if for each `k` eventually `a_k ≤ m ≤ b_k` along `l`,
`a_k → A_k` and `b_k → B_k` along `l`, and `A_k → L`, `B_k → L` as `k → ∞`, then `m → L` along `l`. -/
theorem Submission.allard_tc_fbl_squeeze :
    ∀ {ι : Type} (l : Filter ι) (m : ι → ℝ) (a b : ℕ → ι → ℝ) (A B : ℕ → ℝ) (L : ℝ), (∀ k, ∀ᶠ i in l, a k i ≤ m i ∧ m i ≤ b k i) → (∀ k, Tendsto (a k) l (𝓝 (A k))) → (∀ k, Tendsto (b k) l (𝓝 (B k))) → Tendsto A atTop (𝓝 L) → Tendsto B atTop (𝓝 L) → Tendsto m l (𝓝 L) := by
  intro ι l m a b A B L hab ha hb hA hB
  -- Step 1: by `Metric.tendsto_nhds` it suffices that `|m i - L| < ε` eventually along `l`.
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Step 2: one index `k` with `|A k - L| < ε / 2` and `|B k - L| < ε / 2`.
  obtain ⟨k, hAk, hBk⟩ :=
    ((Metric.tendsto_nhds.1 hA _ hε2).and (Metric.tendsto_nhds.1 hB _ hε2)).exists
  -- Step 3: eventually along `l`, `a k i ≤ m i ≤ b k i`, `|a k i - A k| < ε / 2` and
  -- `|b k i - B k| < ε / 2`.
  filter_upwards [hab k, Metric.tendsto_nhds.1 (ha k) _ hε2, Metric.tendsto_nhds.1 (hb k) _ hε2]
    with i hi hai hbi
  -- Step 4: hence `L - ε < a k i ≤ m i ≤ b k i < L + ε`.
  rw [Real.dist_eq, abs_lt] at hAk hBk hai hbi ⊢
  constructor <;> linarith [hi.1, hi.2, hAk.1, hAk.2, hBk.1, hBk.2, hai.1, hai.2, hbi.1, hbi.2]

/-- Ball-integral limit at a flat blow-up for `β ≥ 0` (flat blow-up ball limits for Simon Ch. 8,
5.5): if `t_i → 0⁺` along `l` and `∫ f dV_{x,t_i} → θ ∫ f dv(T)` for every `f ∈ C_c(ℝ^N × G(N,n))`,
then `t_i⁻ⁿ ∫_{B_{t_i}(x) × G(N,n)} β dV → θ ω_n β(T)` for every continuous `β ≥ 0` on `G(N,n)`. -/
theorem Submission.allard_tc_fbl_nonneg_limit :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ) {ι : Type} (l : Filter ι) (t : ι → ℝ), x ∈ U → Tendsto t l (𝓝[>] 0) → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), Tendsto (fun i ↦ ∫ z, f z ∂(rescaledMeasure V x (t i))) l (𝓝 (θ * ∫ z, f z ∂(planeVarifoldMeasure T)))) → ∀ β : C(Grassmannian N n, ℝ), (∀ S, 0 ≤ β S) → Tendsto (fun i ↦ (∫ z in closedBall x (t i) ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / t i ^ n) l (𝓝 (θ * (unitBallVolume n).toReal * β T)) := by
  intro N n U V x T θ ι l t hx ht hconv β hβ
  -- Step 1: good radii. `B°_ε(x) ⊆ U` for some `ε > 0`, and eventually `0 < t i < ε / 2`,
  -- so then `B_{2 t i}(x) ⊆ U`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hx
  have hgood : ∀ᶠ i in l, 0 < t i ∧ closedBall x (2 * t i) ⊆ U := by
    filter_upwards [ht.eventually_mem (Ioo_mem_nhdsGT (half_pos hε))] with i hi
    exact ⟨hi.1, (closedBall_subset_ball (by linarith [hi.2])).trans hball⟩
  -- Step 2: the cut-offs `φ_k^±` vanish where `|y| > 2`, i.e. off the compact set `B_2(0) × G`.
  have hK : IsCompact (closedBall (0 : Euclidean N) 2 ×ˢ (univ : Set (Grassmannian N n))) :=
    (isCompact_closedBall 0 2).prod isCompact_univ
  have hK_out : ∀ z : Euclidean N × Grassmannian N n,
      z ∉ closedBall (0 : Euclidean N) 2 ×ˢ (univ : Set (Grassmannian N n)) → 2 < ‖z.1‖ := by
    intro z hz
    simpa using hz
  -- Steps 3 and 5: `F_k^± = φ_k^± β ∈ C_c(ℝ^N × G)`, so the hypothesis applies to them.
  have hlow : ∀ k : ℕ, Tendsto (fun i ↦ ∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2
      ∂(rescaledMeasure V x (t i))) l
      (𝓝 (θ * ∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2
        ∂(planeVarifoldMeasure T))) := by
    intro k
    have hcs : HasCompactSupport fun z : Euclidean N × Grassmannian N n ↦
        min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2 := by
      refine HasCompactSupport.intro hK fun z hz ↦ ?_
      have : max 0 (1 - ‖z.1‖) = 0 := max_eq_left (by linarith [hK_out z hz])
      simp [this]
    exact hconv ⟨⟨_, by fun_prop⟩, hcs⟩
  have hupp : ∀ k : ℕ, Tendsto (fun i ↦ ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2
      ∂(rescaledMeasure V x (t i))) l
      (𝓝 (θ * ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2
        ∂(planeVarifoldMeasure T))) := by
    intro k
    have hcs : HasCompactSupport fun z : Euclidean N × Grassmannian N n ↦
        max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2 := by
      refine HasCompactSupport.intro hK fun z hz ↦ ?_
      have h2 := hK_out z hz
      have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have h3 : max 0 (‖z.1‖ - 1) = ‖z.1‖ - 1 := max_eq_right (by linarith)
      have : max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) = 0 :=
        max_eq_left (by rw [h3]; nlinarith)
      simp [this]
    exact hconv ⟨⟨_, by fun_prop⟩, hcs⟩
  -- Step 4: plane side, `∫ φ(y) β(S) dv(T) = (∫_T φ dHⁿ) β(T)` for continuous `φ`.
  have hplane : ∀ φ : Euclidean N → ℝ, Continuous φ →
      ∫ z, φ z.1 * β z.2 ∂(planeVarifoldMeasure T) =
        (∫ y in (T.plane : Set (Euclidean N)), φ y ∂(μHE[n] : Measure (Euclidean N))) * β T := by
    intro φ hφ
    rw [planeVarifoldMeasure,
      integral_map (by fun_prop : Continuous fun y : Euclidean N ↦ (y, T)).aemeasurable
        (by fun_prop : Continuous fun z : Euclidean N × Grassmannian N n ↦
          φ z.1 * β z.2).aestronglyMeasurable]
    exact integral_mul_const (β T) φ
  -- Step 6: `c_k^± → ω_n` (plane cut-off limits), so `θ c_k^± β(T) → θ ω_n β(T)`.
  obtain ⟨hcp, hcm⟩ := Submission.allard_tc_fbl_plane_cutoff_limits N n T
  -- Steps 7 and 8: eventually `a_k(i) ≤ m(i) ≤ b_k(i)` (sandwich), then squeeze.
  refine Submission.allard_tc_fbl_squeeze l _
    (fun k i ↦ ∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2 ∂(rescaledMeasure V x (t i)))
    (fun k i ↦ ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2
      ∂(rescaledMeasure V x (t i)))
    (fun k ↦ θ * ∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2 ∂(planeVarifoldMeasure T))
    (fun k ↦ θ * ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2
      ∂(planeVarifoldMeasure T))
    _ (fun k ↦ ?_) hlow hupp ?_ ?_
  · filter_upwards [hgood] with i hi
    exact Submission.allard_tc_fbl_rescaled_sandwich N n U V x β (t i) k hi.1 hi.2 hβ
  · rw [mul_assoc]
    refine ((hcm.mul_const (β T)).const_mul θ).congr fun k ↦ ?_
    rw [hplane (fun y ↦ min 1 (((k : ℝ) + 1) * max 0 (1 - ‖y‖))) (by fun_prop)]
  · rw [mul_assoc]
    refine ((hcp.mul_const (β T)).const_mul θ).congr fun k ↦ ?_
    rw [hplane (fun y ↦ max 0 (1 - ((k : ℝ) + 1) * max 0 (‖y‖ - 1))) (by fun_prop)]

/-- Ball limits at a flat blow-up (the portmanteau step in the proof of Simon Ch. 8, 5.5: the limit
stated right after display (9), p. 218): if `V_{x,t_i} → θ v(T)` as Radon measures along `l`, with
`t_i → 0⁺`, then `t_i^{-n} ∫_{B_{t_i}(x) × G(N,n)} β(S) dV(y,S) → θ ω_n β(T)` for every continuous
`β` on `G(N,n)`, and `t_i^{-n} μ_V(B_{t_i}(x)) → θ ω_n`. -/
theorem Submission.allard_tc_flat_blowup_ball_limits :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ) {ι : Type} (l : Filter ι) (t : ι → ℝ), x ∈ U → Tendsto t l (𝓝[>] 0) → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), Tendsto (fun i ↦ ∫ z, f z ∂(rescaledMeasure V x (t i))) l (𝓝 (θ * ∫ z, f z ∂(planeVarifoldMeasure T)))) → (∀ β : C(Grassmannian N n, ℝ), Tendsto (fun i ↦ (∫ z in closedBall x (t i) ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / t i ^ n) l (𝓝 (θ * (unitBallVolume n).toReal * β T))) ∧ Tendsto (fun i ↦ (V.weight (closedBall x (t i))).toReal / t i ^ n) l (𝓝 (θ * (unitBallVolume n).toReal)) := by
  intro N n U V x T θ ι l t hx ht hconv
  -- Step 1: `U` is open, so eventually along `l` the closed ball `B_{t_i}(x)` is a compact subset
  -- of `U`, hence `V(B_{t_i}(x) × G(N,n)) < ∞`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hx
  have hfin : ∀ᶠ i in l,
      V.measure (closedBall x (t i) ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ := by
    filter_upwards [ht (Ioo_mem_nhdsGT (half_pos hε))] with i hi
    exact V.finite_on_compact _ (isCompact_closedBall x (t i))
      ((closedBall_subset_ball (by linarith [hi.2])).trans hεU)
  -- Step 2: the case `β ≥ 0` is the sibling `nonneg_limit`.
  have hnn := Submission.allard_tc_fbl_nonneg_limit N n U V x T θ l t hx ht hconv
  -- Step 3: a general `β` is `(β + ‖β‖) - ‖β‖`, a difference of nonnegative continuous functions
  -- (`G(N,n)` is compact, so `‖β‖ = sup_S |β(S)| < ∞`), and both are integrable on
  -- `B_{t_i}(x) × G(N,n)` once that set has finite `V`-measure.
  have hβ : ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun i ↦ (∫ z in closedBall x (t i) ×ˢ
      (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / t i ^ n) l
      (𝓝 (θ * (unitBallVolume n).toReal * β T)) := by
    intro β
    have hpos : ∀ S, 0 ≤ (β + ContinuousMap.const _ ‖β‖ : C(Grassmannian N n, ℝ)) S := fun S ↦ by
      have hS := β.norm_coe_le_norm S
      rw [Real.norm_eq_abs] at hS
      rw [ContinuousMap.add_apply, ContinuousMap.const_apply]
      linarith [neg_abs_le (β S)]
    have hlim := (hnn _ hpos).sub (hnn (ContinuousMap.const _ ‖β‖) fun _ ↦ norm_nonneg β)
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, mul_add,
      add_sub_cancel_right] at hlim
    refine hlim.congr' ?_
    filter_upwards [hfin] with i hi
    have hint : IntegrableOn (fun z : Euclidean N × Grassmannian N n ↦ β z.2)
        (closedBall x (t i) ×ˢ (univ : Set (Grassmannian N n))) V.measure :=
      Measure.integrableOn_of_bounded hi (β.continuous.comp continuous_snd).aestronglyMeasurable
        (ae_of_all _ fun z ↦ β.norm_coe_le_norm z.2)
    rw [integral_add hint (integrableOn_const hi), add_div, add_sub_cancel_right]
  refine ⟨hβ, ?_⟩
  -- Step 4: `β ≡ 1` gives the weight, since `∫_{B × G(N,n)} 1 dV = V(B × G(N,n)) = μ_V(B)`.
  have h1 := hβ (ContinuousMap.const _ 1)
  simp only [ContinuousMap.const_apply, mul_one] at h1
  refine h1.congr fun i ↦ ?_
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    V.weight_apply measurableSet_closedBall]
/-- **Simon Ch. 8, proof of 5.5 from (9) to the end** (child `unique_tangent_plane` of
`allard_tangent_cones`): suppose every blow-up sequence at `x` has a vaguely convergent subsequence,
every `C ∈ VarTan(V, x)` is `θ₀ v(T)` for some plane `T`, and the `β`-averages of `V` over `B_ρ(x)`
tend to `∫ β dν` (printed (9)).  Then `θ₀ v(T)` is the only varifold tangent and
`V_{x,λ} → θ₀ v(T)` as `λ ↓ 0`.  With (9), `allard_tc_flat_blowup_ball_limits` gives
`β(T) = ∫ β dν` for every such `T`, and the matrix-entry functions separate the points of
`G(N,n)`. -/
theorem Submission.allard_tc_unique_tangent_plane :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ)
      (ν : Measure (Grassmannian N n)), x ∈ U → 0 < θ₀ →
      (∀ t : ℕ → ℝ, (∀ j, 0 < t j) → Tendsto t atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Varifold N n (univ : Set (Euclidean N)),
          VagueConverges (fun j ↦ rescaledMeasure V x (t (φ j))) C.measure) →
      (∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
        ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T) →
      (∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦
        (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) /
          (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂ν))) →
      ∃ T : Grassmannian N n, HasTangentPlane V x T θ₀ := by
  intro N n U V x θ₀ ν hx hθ hsub htan hβ
  have hsmul : ∀ (T : Grassmannian N n) (f : C_c(Euclidean N × Grassmannian N n, ℝ)),
      ∫ z, f z ∂(ENNReal.ofReal θ₀ • planeVarifoldMeasure T) =
        θ₀ * ∫ z, f z ∂(planeVarifoldMeasure T) := fun T f ↦ by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hθ.le, smul_eq_mul]
  have hω : 0 < (unitBallVolume n).toReal := by
    rw [unitBallVolume]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  -- With (9), a varifold tangent `θ₀ v(T)` forces `∫ β dν = β(T)`.
  have hident : ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
      ∀ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T →
      ∀ β : C(Grassmannian N n, ℝ), ∫ S, β S ∂ν = β T := by
    rintro C ⟨s, hs0, hs, hconv⟩ T hC β
    have hs' : Tendsto s atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall hs0⟩
    obtain ⟨hball, hweight⟩ :=
      Submission.allard_tc_flat_blowup_ball_limits N n U V x T θ₀ atTop s hx hs' fun f ↦ by
        have h := hconv f
        rwa [hC, hsmul] at h
    have hθω : θ₀ * (unitBallVolume n).toReal ≠ 0 := (mul_pos hθ hω).ne'
    have hlim := (hball β).div hweight hθω
    rw [mul_div_cancel_left₀ (β T) hθω] at hlim
    refine tendsto_nhds_unique ((hβ β).comp hs') (hlim.congr fun j ↦ ?_)
    simp only [Pi.div_apply, Function.comp_apply]
    exact div_div_div_cancel_right₀ (pow_ne_zero n (hs0 j).ne') _ _
  -- Some varifold tangent exists (blow up along `1 / (j + 1)`); it is `θ₀ v(T₀)`.
  obtain ⟨φ₀, hφ₀, C₀, hC₀⟩ := hsub (fun j ↦ 1 / ((j : ℝ) + 1))
    (fun j ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat
  have hC₀tan : IsVarifoldTangent V x C₀ :=
    ⟨fun j ↦ 1 / ((φ₀ j : ℝ) + 1), fun j ↦ Nat.one_div_pos_of_nat,
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ₀.tendsto_atTop, hC₀⟩
  obtain ⟨T₀, hT₀⟩ := htan C₀ hC₀tan
  -- Every varifold tangent is `θ₀ v(T₀)`: the matrix entries separate the points of `G(N,n)`.
  have huniq : ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
      C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T₀ := by
    intro C hC
    obtain ⟨T, hT⟩ := htan C hC
    suffices T = T₀ by rw [hT, this]
    refine Subtype.ext (Matrix.ext fun i k ↦ ?_)
    let β : C(Grassmannian N n, ℝ) := ⟨fun S ↦ S.1 i k, continuous_subtype_val.matrix_elem i k⟩
    exact (hident C hC T hT β).symm.trans (hident C₀ hC₀tan T₀ hT₀ β)
  -- Full limit: along every `u → 0⁺` some subsequence of `V_{x,u}` tends to `θ₀ v(T₀)`.
  refine ⟨T₀, hx, hθ, fun f ↦ tendsto_of_subseq_tendsto fun u hu ↦ ?_⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hu.eventually eventually_mem_nhdsWithin)
  have hu0 : Tendsto (fun j ↦ u (j + J)) atTop (𝓝 0) :=
    (tendsto_nhds_of_tendsto_nhdsWithin hu).comp (tendsto_add_atTop_nat J)
  obtain ⟨φ, hφ, C, hC⟩ := hsub (fun j ↦ u (j + J)) (fun j ↦ hJ (j + J) (Nat.le_add_left J j)) hu0
  have hCtan : IsVarifoldTangent V x C :=
    ⟨fun j ↦ u (φ j + J), fun j ↦ hJ (φ j + J) (Nat.le_add_left J (φ j)),
      hu0.comp hφ.tendsto_atTop, hC⟩
  refine ⟨fun j ↦ φ j + J, ?_⟩
  have hf := hC f
  rwa [huniq C hCtan, hsmul] at hf
/-- **Simon Ch. 8, 5.5 (Allard's Rectifiability Theorem) with Remark 5.6** (child
`allard_rectifiability` of `allard_tangent_cones`).  At `μ_V`-a.e. `x`: `θ₀ = Θ^n(μ_V, x)` exists
in `(0, ∞)`, `D_{μ_V}‖δV‖(x) < ∞` (which gives 5.1), the `β`-averages of `V` over `B_ρ(x)` converge
(Lemma 1.3), and the density decay of `allard_tc_density_blowup_decay` holds.  At such `x` the
blow-up density lower bound with `τ_k = θ₀ - θ₀/(k+2) ↑ θ₀` gives `Θ^n(μ_C, ·) ≥ θ₀` `μ_C`-a.e.
(printed (7)) for each `C ∈ VarTan(V, x)`, so `C = θ₀ v(T)` (`allard_tc_stationary_cone_flat`) and
`V` has a tangent plane at `x` (`allard_tc_unique_tangent_plane`).  Rectifiability then follows
from 1.2. -/
theorem Submission.allard_tc_rectifiability :
    FirstVariationRepresentation → StationaryMonotonicityIdentity → DensityExistsAE → ConstancyTheorem → VarifoldTangentCones → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ) → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), ∃ η : Euclidean N → Measure (Grassmannian N n), (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) ∧ ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight) → FirstRectifiabilityTheorem → AllardRectifiabilityTheorem := by
  intro hFVR hSMI hDE hCT hVTC hlower hdisint hFRT N n U V hV hpos
  obtain ⟨η, hη, -⟩ := hdisint N n U V
  obtain ⟨Θ, -, hΘ⟩ := hDE N n U V hV
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  have hω0 : unitBallVolume n ≠ 0 := by
    rw [unitBallVolume]
    exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Remark 5.6: `V` has a tangent plane at every point where the a.e. statements hold.
  have htan : ∀ᵐ x ∂V.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ := by
    filter_upwards [hη, hΘ, (hFVR N n U V hV).2.1, hU,
      Submission.allard_tc_density_blowup_decay hDE N n U V hV, hpos]
      with x hηx hΘx hFx hxU hdec hpx
    -- `θ₀ = Θ^n(μ_V, x) ∈ (0, ∞)`.
    obtain ⟨θ, hθ, hθpos⟩ := hpx
    have hθtop : θ ≠ ∞ := by
      rw [tendsto_nhds_unique hθ hΘx.2]
      exact hΘx.1
    obtain ⟨θ₀, hθ₀, rfl⟩ : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ENNReal.ofReal θ₀ = θ :=
      ⟨θ.toReal, ENNReal.toReal_pos hθpos.ne' hθtop, ENNReal.ofReal_toReal hθtop⟩
    -- 5.1: `‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for small `ρ`, since `D_{μ_V}‖δV‖(x) < ∞`.
    obtain ⟨Λ, hΛ, hev⟩ : ∃ Λ : ℝ≥0∞, Λ ≠ ∞ ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        variationMeasure V (closedBall x ρ) ≤ Λ * V.weight (closedBall x ρ) := by
      have hΛ : variationDensity V x + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hFx.1, ENNReal.one_ne_top⟩
      refine ⟨_, hΛ, ?_⟩
      filter_upwards [hFx.2.eventually (gt_mem_nhds (ENNReal.lt_add_right hFx.1 one_ne_zero))]
        with ρ hρ
      exact (ENNReal.div_le_iff_le_mul (Or.inr hΛ) (Or.inr (by positivity))).1 hρ.le
    have h51 : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) /
        ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ) (𝓝[>] 0) (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      have hlim := ENNReal.Tendsto.mul h0
        (Or.inr (ENNReal.mul_ne_top hΛ (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top)))
        (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hθ (Or.inr hωtop)) (Or.inr hΛ))
        (Or.inr ENNReal.zero_ne_top)
      rw [zero_mul] at hlim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun _ ↦ zero_le) ?_
      filter_upwards [hev] with ρ hρ
      calc ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n
          ≤ ENNReal.ofReal ρ * (Λ * V.weight (closedBall x ρ)) / ENNReal.ofReal ρ ^ n := by
            gcongr
        _ = ENNReal.ofReal ρ * (Λ * (unitBallVolume n * densityRatio n V.weight x ρ)) := by
            rw [densityRatio, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hω0 hωtop,
              mul_div_assoc, mul_div_assoc]
    -- 5.2–5.4: compactness, stationarity and the ball identity of the varifold tangents.
    obtain ⟨hcpt, hcone⟩ := hVTC N n U V x θ₀ hV hxU hθ₀ hθ h51
    -- Every `C ∈ VarTan(V, x)` is `θ₀ v(T)`.
    have hflat : ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
        ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T := by
      intro C hC
      obtain ⟨hstat, hball, -⟩ := hcone C hC
      refine Submission.allard_tc_stationary_cone_flat hSMI hCT N n C θ₀ hθ₀ hstat hball ?_
      -- Printed (3)–(7): `Θ^n(μ_C, ·) ≥ τ_k` a.e. for `τ_k = θ₀ - θ₀/(k+2)`, and `τ_k → θ₀`.
      have hk : ∀ k : ℕ, ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧
          ENNReal.ofReal (θ₀ - θ₀ / ((k : ℝ) + 2)) ≤ θ := by
        intro k
        have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        have hsmall : 0 < θ₀ / ((k : ℝ) + 2) := div_pos hθ₀ (by linarith)
        have hlt : θ₀ / ((k : ℝ) + 2) < θ₀ := div_lt_self hθ₀ hk2
        exact hlower N n U V x (θ₀ - θ₀ / ((k : ℝ) + 2)) hV hxU (by linarith) h51
          (hdec θ₀ (θ₀ - θ₀ / ((k : ℝ) + 2)) hθ (by linarith)) C hC
      have hτ : Tendsto (fun k : ℕ ↦ θ₀ - θ₀ / ((k : ℝ) + 2)) atTop (𝓝 θ₀) := by
        have h2 : Tendsto (fun k : ℕ ↦ θ₀ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
        have h3 : Tendsto (fun k : ℕ ↦ θ₀ - θ₀ / ((k : ℝ) + 2)) atTop (𝓝 (θ₀ - 0)) :=
          tendsto_const_nhds.sub h2
        rwa [sub_zero] at h3
      filter_upwards [ae_all_iff.2 hk] with y hy
      obtain ⟨θy, hθy, -⟩ := hy 0
      refine ⟨θy, hθy, le_of_tendsto' (ENNReal.tendsto_ofReal hτ) fun k ↦ ?_⟩
      obtain ⟨θ, hθ', hle⟩ := hy k
      rwa [tendsto_nhds_unique hθ' hθy] at hle
    -- (8)–(9): the varifold tangent is unique, so `V` has a tangent plane at `x`.
    obtain ⟨T, hT⟩ := Submission.allard_tc_unique_tangent_plane N n U V x θ₀ (η x) hxU hθ₀
      hcpt hflat hηx.2
    exact ⟨T, θ₀, hT⟩
  -- 1.2 turns the tangent planes into `V = v(M, θ)`.
  obtain ⟨θ, -, hM⟩ := hFRT N n U V htan
  exact ⟨⟨_, θ, hM⟩, htan⟩
/-- **Simon Ch. 2, 4.3** (child `classical_tangent` of the constancy theorem): at a point `φ a`
of a `C²` local representation, the classical tangent space (velocities of `C¹` curves in `M`) is
the range of `L = Dφ(a)`.  `⊇`: the curve `t ↦ φ (a + (ε sin (t/ε)) w)` stays in the chart and has
velocity `L w`.  `⊆`: relative properness makes the chart parameter `β t` of `γ t` tend to `a`,
`L` is antilipschitz so `β t - a = O(t)`, and then the component of `γ` normal to `range L` has
derivative `0` at `0`. -/
theorem Submission.simon_chart_classicalTangentSpace_eq_range :
    ∀ (N n : ℕ) (M W : Set (Euclidean N)) (D : Set (Euclidean n)) (φ : Euclidean n → Euclidean N)
      (a : Euclidean n), Chapter02.IsSimonLocalRepresentation 2 M D W φ → a ∈ D →
      classicalTangentSpace M (φ a) = Set.range (fderiv ℝ φ a) := by
  intro N n M W D φ a hφ ha
  have hφ1 : ContDiffOn ℝ 1 φ D := hφ.contDiffOn.of_le (by norm_num)
  have hL : HasFDerivAt φ (fderiv ℝ φ a) a :=
    ((hφ1.contDiffAt (hφ.isOpen_source.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
  ext ξ
  constructor
  · rintro ⟨γ, -, hmaps, hγ0, hder⟩
    have hφa : φ a ∈ W ∩ M := hφ.image_eq ▸ Set.mem_image_of_mem φ ha
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hφ.isOpen_target (φ a) hφa.1
    have hKW : closedBall (φ a) (r / 2) ⊆ W :=
      (closedBall_subset_ball (half_lt_self hr)).trans hrW
    have hS : IsCompact (D ∩ φ ⁻¹' closedBall (φ a) (r / 2)) :=
      hφ.isCompact_source_inter_preimage _ (isCompact_closedBall _ _) hKW
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ closedBall (φ a) (r / 2) ∧ γ t ∈ M := by
      filter_upwards [hder.continuousAt.preimage_mem_nhds
          (by rw [hγ0]; exact closedBall_mem_nhds _ (half_pos hr)),
        Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht1 ht2
      exact ⟨ht1, hmaps ht2⟩
    -- `β t` is the chart parameter of `γ t`; it exists for `t` near `0`.
    set β : ℝ → Euclidean n := fun t ↦ Function.invFunOn φ D (γ t)
    have hβ : ∀ᶠ t in 𝓝 (0 : ℝ), β t ∈ D ∩ φ ⁻¹' closedBall (φ a) (r / 2) ∧ φ (β t) = γ t := by
      filter_upwards [hev] with t ht
      have hex : γ t ∈ φ '' D := hφ.image_eq ▸ ⟨hKW ht.1, ht.2⟩
      obtain ⟨h1, h2⟩ := Function.invFunOn_pos hex
      exact ⟨⟨h1, by rw [Set.mem_preimage, h2]; exact ht.1⟩, h2⟩
    -- Relative properness: `β t → a`.
    have hβa : Tendsto β (𝓝 0) (𝓝 a) := by
      refine hS.tendsto_nhds_of_unique_mapClusterPt (hβ.mono fun t ht ↦ ht.1) fun b hb hcl ↦ ?_
      have hφb : ContinuousAt φ b :=
        hφ.contDiffOn.continuousOn.continuousAt (hφ.isOpen_source.mem_nhds hb.1)
      have h1 : MapClusterPt (φ b) (𝓝 0) (φ ∘ β) := hcl.continuousAt_comp hφb
      have h2 : ClusterPt (φ b) (map γ (𝓝 0)) := by
        rw [← Filter.map_congr (hβ.mono fun t ht ↦ ht.2)]
        exact h1
      have h3 : φ b = γ 0 := eq_of_nhds_neBot (h2.mono hder.continuousAt.tendsto).neBot
      exact hφ.injOn hb.1 ha (h3.trans hγ0)
    -- `L = Dφ(a)` is injective, hence antilipschitz, so `β t - a = O(t)`.
    obtain ⟨C, -, hC⟩ := (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr (hφ.injective_fderiv ha))
    have hrev : (fun u ↦ u - a) =O[𝓝 a] fun u ↦ φ u - φ a := by
      have A : (fun u ↦ u - a) =O[𝓝 a] fun u ↦ fderiv ℝ φ a (u - a) :=
        Asymptotics.isBigO_iff.mpr ⟨C, Eventually.of_forall fun u ↦ by
          have := hC.le_mul_dist 0 (u - a)
          rwa [map_zero, dist_zero_left, dist_zero_left] at this⟩
      have B : Asymptotics.IsEquivalent (𝓝 a) (fun u ↦ φ u - φ a)
          fun u ↦ fderiv ℝ φ a (u - a) :=
        hL.isLittleO.trans_isBigO A
      exact A.trans B.isBigO_symm
    have hγφ : (fun t ↦ φ (β t) - φ a) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ γ t - γ 0 := by
      filter_upwards [hβ] with t ht
      rw [ht.2, hγ0]
    have hβO : (fun t ↦ β t - a) =O[𝓝 (0 : ℝ)] fun t ↦ t := by
      have h1 : (fun t ↦ β t - a) =O[𝓝 (0 : ℝ)] fun t ↦ φ (β t) - φ a := hrev.comp_tendsto hβa
      have h2 : (fun t ↦ γ t - γ 0) =O[𝓝 (0 : ℝ)] fun t ↦ t - 0 := hder.isBigO_sub
      simpa only [sub_zero] using (h1.congr' EventuallyEq.rfl hγφ).trans h2
    -- The normal part `Q = id - P_{range L}` of `γ` has zero derivative at `0`.
    set K : Submodule ℝ (Euclidean N) :=
      LinearMap.range (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N)
    set Q : Euclidean N →L[ℝ] Euclidean N := ContinuousLinearMap.id ℝ _ - K.starProjection with hQ
    have hQL : Q.comp (fderiv ℝ φ a) = 0 := by
      ext1 v
      have hv : K.starProjection (fderiv ℝ φ a v) = fderiv ℝ φ a v :=
        Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ v)
      simp [hQ, hv]
    have hQφ : (fun u ↦ Q (φ u) - Q (φ a)) =o[𝓝 a] fun u ↦ u - a := by
      simpa [hQL] using (Q.hasFDerivAt.comp a hL).isLittleO
    have hQγ : HasDerivAt (fun t ↦ Q (γ t)) 0 0 := by
      refine hasDerivAt_iff_isLittleO.mpr ?_
      have h1 := (hQφ.comp_tendsto hβa).trans_isBigO hβO
      have h2 : (fun t ↦ Q (φ (β t)) - Q (φ a)) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ Q (γ t) - Q (γ 0) := by
        filter_upwards [hβ] with t ht
        rw [ht.2, hγ0]
      simpa using h1.congr' h2 EventuallyEq.rfl
    have hQξ : Q ξ = 0 := (Q.hasFDerivAt.comp_hasDerivAt 0 hder).unique hQγ
    have hξK : ξ ∈ K := by
      rw [← Submodule.starProjection_eq_self_iff]
      have : ξ - K.starProjection ξ = 0 := by simpa [hQ] using hQξ
      exact (sub_eq_zero.mp this).symm
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hξK
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hφ.isOpen_source a ha
    have hw1 : 0 < ‖w‖ + 1 := by positivity
    set ε : ℝ := r / (‖w‖ + 1) with hε
    have hε0 : 0 < ε := div_pos hr hw1
    -- `c t = a + (ε sin (t / ε)) w` stays in `B(a, r) ⊆ D` and has velocity `w` at `0`.
    have hcD : ∀ t : ℝ, a + (ε * Real.sin (t / ε)) • w ∈ D := by
      intro t
      apply hrD
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_of_pos hε0]
      calc ε * |Real.sin (t / ε)| * ‖w‖ ≤ ε * 1 * ‖w‖ := by
            gcongr
            exact Real.abs_sin_le_one _
        _ < r := by
            rw [mul_one, hε, div_mul_eq_mul_div, div_lt_iff₀ hw1]
            nlinarith [norm_nonneg w]
    have hcd : ContDiff ℝ 1 fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w :=
      contDiff_const.add <|
        (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ε))).smul contDiff_const
    have hcder : HasDerivAt (fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w) w 0 := by
      have hdiv : HasDerivAt (fun t : ℝ ↦ t / ε) (1 / ε) 0 := (hasDerivAt_id (0 : ℝ)).div_const ε
      have hsin : HasDerivAt (fun t : ℝ ↦ ε * Real.sin (t / ε))
          (ε * (Real.cos (0 / ε) * (1 / ε))) 0 :=
        hdiv.sin.const_mul ε
      have h1 : ε * (Real.cos (0 / ε) * (1 / ε)) = 1 := by
        rw [zero_div, Real.cos_zero]
        field_simp
      rw [h1] at hsin
      simpa using (hsin.smul_const w).const_add a
    refine ⟨φ ∘ fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w, ?_, ?_, ?_, ?_⟩
    · exact (hφ1.comp_contDiff hcd hcD).contDiffOn
    · intro t _
      exact (hφ.image_eq ▸ Set.mem_image_of_mem φ (hcD t) : φ _ ∈ W ∩ M).2
    · simp
    · have hL' : HasFDerivAt φ (fderiv ℝ φ a)
          ((fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w) 0) := by
        simpa using hL
      exact hL'.comp_hasDerivAt 0 hcder

theorem Submission.stationary_constancy_tangentGraph_measure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)),
      V.Stationary → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M →
      U ∩ V.weight.support ⊆ M → IsPreconnected (M ∩ U) → M.Nonempty →
      ∃ (c : ℝ≥0∞) (T : Euclidean N → Grassmannian N n), c ≠ ∞ ∧ Measurable T ∧
        V.measure = (c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).map
          (fun x ↦ (x, T x)) ∧
        (c ≠ 0 → ∀ x ∈ M ∩ U, ((T x).plane : Set (Euclidean N)) = classicalTangentSpace M x) := by
  intro N n U V M hV hSM hM hconn hne
  -- smooth cut-offs of maps that are smooth on an open set
  have GCut : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (k : ℕ∞) (χ : X → ℝ) (g : X → Y) (O : Set X), IsOpen O →
      ContDiff ℝ k χ → ContDiffOn ℝ k g O → tsupport χ ⊆ O → ContDiff ℝ k (fun x ↦ χ x • g x) := by
    intro X Y _ _ _ _ k χ g O hO hχ hg hs
    refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hg.contDiffAt (hO.mem_nhds hx))
    · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ ↦ (0 : Y)) ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hx (hs h)] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  -- a `C²` left inverse `ψ` of a chart near a chart point
  have GI : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (M W : Set F) (D : Set E) (φ : E → F) (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
      (a : E) (ha : a ∈ D),
      ∃ (ψ : F → E) (T₀ : Set F), IsOpen T₀ ∧ φ a ∈ T₀ ∧ ContDiffOn ℝ 2 ψ T₀ ∧ MapsTo ψ T₀ D ∧
        ∀ y ∈ M ∩ T₀, φ (ψ y) = y := by
    intro E F _ _ _ _ _ _ M W D φ hφ a ha
    obtain ⟨hDo, hWo, hφc, hφi, hφim, hφp, hφd⟩ := hφ
    obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ a := ⟨_, rfl⟩
    obtain ⟨P', hP'⟩ := (L : E →ₗ[ℝ] F).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hL ▸ hφd a ha))
    obtain ⟨P, hPL⟩ : ∃ P : F →L[ℝ] E, ∀ x, P (L x) = x :=
      ⟨LinearMap.toContinuousLinearMap P', fun x ↦ LinearMap.congr_fun hP' x⟩
    have hφa : ContDiffAt ℝ 2 φ a := hφc.contDiffAt (hDo.mem_nhds ha)
    -- the straightening map `Φ z = φ (a + P z) + (z - L (P z))`, with `DΦ(0) = id`
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : F → F, Φ = fun z ↦ φ (a + P z) + (z - L (P z)) := ⟨_, rfl⟩
    have hA : HasFDerivAt (fun z : F ↦ a + P z) P 0 := (P.hasFDerivAt).const_add a
    have hφa' : ContDiffAt ℝ 2 φ (a + P 0) := by rw [map_zero, add_zero]; exact hφa
    have hΦc : ContDiffAt ℝ 2 Φ 0 := by
      rw [hΦ]
      exact (hφa'.comp (0 : F) (contDiffAt_const.add P.contDiff.contDiffAt)).add
        (contDiffAt_id.sub (L.contDiff.comp P.contDiff).contDiffAt)
    have hΦd : HasFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ F : F ≃L[ℝ] F) : F →L[ℝ] F) 0 := by
      have h1 : HasFDerivAt (fun z : F ↦ φ (a + P z)) (L.comp P) 0 := by
        have : HasFDerivAt φ L (a + P 0) := by
          rw [map_zero, add_zero, hL]; exact (hφa.differentiableAt (by norm_num)).hasFDerivAt
        exact this.comp (0 : F) hA
      rw [hΦ]
      refine (h1.add ((hasFDerivAt_id (0 : F)).sub (L.comp P).hasFDerivAt)).congr_fderiv ?_
      ext z
      simp
    have hstrict := hΦc.hasStrictFDerivAt' hΦd (by norm_num)
    set e := hstrict.toOpenPartialHomeomorph Φ with he
    have h0s : (0 : F) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
    have hΦ0 : Φ 0 = φ a := by rw [hΦ]; simp
    have hφat : φ a ∈ e.target := hΦ0 ▸ hstrict.image_mem_toOpenPartialHomeomorph_target
    have hsymm : e.symm (φ a) = 0 := by rw [← hΦ0]; exact e.left_inv h0s
    -- the inverse is `C²` near `φ a`
    have hΨ : ContDiffAt ℝ 2 e.symm (φ a) := by
      refine e.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ F) hφat ?_ ?_
      · rw [hsymm]; exact hΦd
      · rw [hsymm]; exact hΦc
    obtain ⟨O₁, hO₁, hO₁o, hφaO₁⟩ := _root_.mem_nhds_iff.mp
      (inter_mem (hΨ.eventually (by norm_num)) (e.open_target.mem_nhds hφat))
    -- `ψ y = a + P (e.symm y)`; on the chart, `ψ (φ w) = w`
    obtain ⟨ψ, hψ⟩ : ∃ ψ : F → E, ψ = fun y ↦ a + P (e.symm y) := ⟨_, rfl⟩
    have hψc : ContDiffOn ℝ 2 ψ O₁ := by
      rw [hψ]
      exact fun y hy ↦ (contDiffAt_const.add (P.contDiff.contDiffAt.comp y
        (show ContDiffAt ℝ 2 e.symm y from (hO₁ hy).1))).contDiffWithinAt
    -- a ball `B(a, r)` in `D` whose linearized image lies in `e.source`
    obtain ⟨r, hr, hrD⟩ : ∃ r > 0, ball a r ⊆ D ∩ (fun w ↦ L (w - a)) ⁻¹' e.source := by
      refine Metric.isOpen_iff.mp (hDo.inter (e.open_source.preimage
        (L.continuous.comp (continuous_id.sub continuous_const)))) a ⟨ha, ?_⟩
      show L (a - a) ∈ e.source
      rw [sub_self, map_zero]; exact h0s
    have hψφ : ∀ w ∈ ball a r, ψ (φ w) = w := by
      intro w hw
      have hsrc := (hrD hw).2
      have hΦw : Φ (L (w - a)) = φ w := by
        rw [hΦ]; simp only [hPL, add_sub_cancel, sub_self, add_zero]
      rw [hψ, ← hΦw]
      show a + P (e.symm (e (L (w - a)))) = w
      rw [e.left_inv hsrc, hPL, add_sub_cancel]
    -- relative properness: near `φ a`, `M` is covered by `φ (B(a, r))`
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hWo (φ a) (hφim ▸ mem_image_of_mem φ ha).1
    have hK : IsCompact ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r) :=
      (hφp _ (isCompact_closedBall _ _) ((closedBall_subset_ball (half_lt_self hρ)).trans hρW)).diff
        isOpen_ball
    have hKφ : φ a ∉ φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r) := by
      rintro ⟨w, ⟨⟨hwD, _⟩, hwB⟩, hw⟩
      exact hwB (hφi hwD ha hw ▸ mem_ball_self hr)
    have hKc : IsClosed (φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r)) :=
      (hK.image_of_continuousOn (hφc.continuousOn.mono fun w hw ↦ hw.1.1)).isClosed
    set O₂ := ball (φ a) (ρ / 2) \ φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r)
    have hO₂ : IsOpen O₂ := isOpen_ball.sdiff hKc
    have hMO₂ : ∀ y ∈ M ∩ O₂, ∃ w ∈ ball a r, φ w = y := by
      rintro y ⟨hyM, hyB, hyK⟩
      have hyW : y ∈ W := hρW (ball_subset_ball (half_le_self hρ.le) hyB)
      obtain ⟨w, hwD, rfl⟩ : y ∈ φ '' D := hφim ▸ ⟨hyW, hyM⟩
      refine ⟨w, ?_, rfl⟩
      by_contra hwB
      exact hyK ⟨w, ⟨⟨hwD, ball_subset_closedBall hyB⟩, hwB⟩, rfl⟩
    -- the final neighbourhood
    refine ⟨ψ, O₁ ∩ O₂ ∩ ψ ⁻¹' ball a r, ?_, ⟨⟨hφaO₁, mem_ball_self (half_pos hρ), hKφ⟩,
      by rw [mem_preimage, hψφ a (mem_ball_self hr)]; exact mem_ball_self hr⟩,
      hψc.mono fun y hy ↦ hy.1.1, fun y hy ↦ (hrD hy.2).1, ?_⟩
    · exact (hψc.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hO₁o.inter hO₂)
        isOpen_ball
    · rintro y ⟨hyM, ⟨_, hyO₂⟩, _⟩
      obtain ⟨w, hw, rfl⟩ := hMO₂ y ⟨hyM, hyO₂⟩
      rw [hψφ w hw]
  -- `normDet` is continuous, and `C¹` at injective maps
  have GNg : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (NJ : (E →L[ℝ] F) → ℝ) (hNJ : ∀ T, NJ T = (T : E →ₗ[ℝ] F).normDet),
      Continuous NJ ∧ ∀ T : E →L[ℝ] F, Function.Injective T → ContDiffAt ℝ 1 NJ T := by
    intro E F _ _ _ _ _ _ NJ hNJ
    set b := stdOrthonormalBasis ℝ E
    have hN : NJ = fun S ↦ Real.sqrt (Matrix.gram ℝ (fun i ↦ S (b i))).det := by
      funext S
      have h := LinearMap.normDet_sq_eq_det_gram (S : E →ₗ[ℝ] F) b
      rw [RCLike.ofReal_real_eq_id, id] at h
      simp only [ContinuousLinearMap.coe_coe] at h
      rw [hNJ, ← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
    have hg : ∀ i j, ContDiff ℝ 1 (fun S : E →L[ℝ] F ↦ inner ℝ (S (b i)) (S (b j))) :=
      fun i j ↦ (ContinuousLinearMap.apply ℝ F (b i)).contDiff.inner ℝ
        (ContinuousLinearMap.apply ℝ F (b j)).contDiff
    have hd : ContDiff ℝ 1 (fun S : E →L[ℝ] F ↦ (Matrix.gram ℝ (fun i ↦ S (b i))).det) := by
      simp only [Matrix.det_apply, Matrix.gram_apply]
      fun_prop
    refine ⟨hN ▸ Real.continuous_sqrt.comp hd.continuous, fun T hT ↦ ?_⟩
    rw [hN]
    refine hd.contDiffAt.sqrt fun h0 ↦ ?_
    have h1 : NJ T = 0 := by rw [hN]; show Real.sqrt _ = 0; rw [h0, Real.sqrt_zero]
    rw [hNJ] at h1
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h1) (LinearMap.ker_eq_bot.mpr hT)
  -- weighted distributional constancy on a ball
  have G4wg : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (vol : Measure E) [vol.IsAddHaarMeasure]
      (ϑ : Measure E) [IsFiniteMeasure ϑ] (J : E → ℝ) (a : E) (R m : ℝ) (hR : 0 < R) (hm : 0 < m)
      (hJ : Measurable J) (hJm : ∀ᵐ u ∂ϑ, m ≤ J u)
      (h : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v,
        ∫ u, (1 / J u) * fderiv ℝ ζ u v ∂ϑ = 0),
      ∃ c : ℝ, ϑ.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
        (vol.restrict (ball a (R / 2 / 2 / 2))).withDensity (fun u ↦ ENNReal.ofReal (J u)) := by
    intro E _ _ _ _ _ vol _ ϑ _ J a R m hR hm hJ hJm h
    have P4 : ∀ (ν : Measure E) [IsFiniteMeasure ν],
        (∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v, ∫ u, fderiv ℝ ζ u v ∂ν = 0) →
        ∃ c : ℝ, ν.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
            vol.restrict (ball a (R / 2 / 2 / 2)) := by
      intro ν _ h
      have h2 : 0 < R / 2 := half_pos hR
      have h4 : 0 < R / 2 / 2 := half_pos h2
      have h8 : 0 < R / 2 / 2 / 2 := half_pos h4
      -- Step A: translation invariance.
      have hA : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2) →
          ∀ h₀ ∈ ball (0 : E) (R / 2), ∫ y, ζ (y - h₀) ∂ν = ∫ y, ζ y ∂ν := by
        intro ζ hζ hs
        have hc : HasCompactSupport ζ :=
          (isCompact_closedBall a (R / 2)).of_isClosed_subset (isClosed_tsupport ζ)
            (hs.trans ball_subset_closedBall)
        have hζ' := hζ.continuous_fderiv one_ne_zero
        obtain ⟨C, hC⟩ := hζ'.bounded_above_of_compact_support (hc.fderiv ℝ)
        have hD : ∀ y h : E, HasFDerivAt (fun h ↦ ζ (y - h)) (-fderiv ℝ ζ (y - h)) h := by
          intro y h
          exact ((hζ.differentiable one_ne_zero (y - h)).hasFDerivAt.comp h
            ((hasFDerivAt_id h).const_sub y)).congr_fderiv
                (by rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id])
        have hF : ∀ h₀ : E, HasFDerivAt (fun h ↦ ∫ y, ζ (y - h) ∂ν)
            (∫ y, -fderiv ℝ ζ (y - h₀) ∂ν) h₀ := fun h₀ ↦
          hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun h y ↦ ζ (y - h))
            (F' := fun h y ↦ -fderiv ℝ ζ (y - h)) (bound := fun _ ↦ C) Filter.univ_mem
            (Eventually.of_forall fun h ↦
              (hζ.continuous.comp (continuous_sub_right h)).aestronglyMeasurable)
            ((hζ.continuous.comp (continuous_sub_right h₀)).integrable_of_hasCompactSupport
              (hc.comp_homeomorph (Homeomorph.subRight h₀)))
            ((hζ'.comp (continuous_sub_right h₀)).neg.aestronglyMeasurable)
            (Eventually.of_forall fun y h _ ↦ (norm_neg _).trans_le (hC _))
            (integrable_const C) (Eventually.of_forall fun y h _ ↦ hD y h)
        have h0 : ∀ h₀ ∈ ball (0 : E) (R / 2),
            fderiv ℝ (fun h ↦ ∫ y, ζ (y - h) ∂ν) h₀ = 0 := by
          intro h₀ hh₀
          rw [(hF h₀).fderiv]
          ext v
          rw [ContinuousLinearMap.integral_apply (φ := fun y ↦ -fderiv ℝ ζ (y - h₀))
            ((hζ'.comp (continuous_sub_right h₀)).neg.integrable_of_hasCompactSupport
              ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.subRight h₀)).neg) v]
          have := h (fun y ↦ ζ (y - h₀)) (hζ.comp (contDiff_id.sub contDiff_const)) ?_ v
          · simp only [fderiv_comp_sub, ContinuousLinearMap.neg_apply, integral_neg,
              ContinuousLinearMap.zero_apply, neg_eq_zero] at this ⊢
            exact this
          · refine (tsupport_comp_subset_preimage _ (continuous_sub_right h₀)).trans ?_
            intro y hy
            have h1 := hs hy
            rw [mem_ball, dist_eq_norm] at h1 ⊢
            rw [mem_ball, dist_zero_right] at hh₀
            calc ‖y - a‖ = ‖(y - h₀ - a) + h₀‖ := by rw [sub_right_comm, sub_add_cancel]
              _ ≤ ‖y - h₀ - a‖ + ‖h₀‖ := norm_add_le _ _
              _ < R / 2 + R / 2 := add_lt_add h1 hh₀
              _ = R := add_halves R
        intro h₀ hh₀
        have := isOpen_ball.is_const_of_fderiv_eq_zero
          (convex_ball (0 : E) (R / 2)).isPreconnected
          (fun h _ ↦ (hF h).differentiableAt.differentiableWithinAt) h0 hh₀
          (mem_ball_self (half_pos hR))
        simpa only [sub_zero] using this
      -- integrability on products of functions supported over a compact set
      have hI : ∀ f : E × E → ℝ, Continuous f → ∀ K : Set (E),
          IsCompact K → (∀ p, p.1 ∉ K → f p = 0) → (∃ C, ∀ p, ‖f p‖ ≤ C) →
          Integrable f (vol.prod ν) := by
        intro f hf K hK hfK ⟨C, hC⟩
        have hfin : (vol.prod ν) (K ×ˢ univ) ≠ ∞ := by
          rw [Measure.prod_prod]
          exact ENNReal.mul_ne_top hK.measure_lt_top.ne (measure_ne_top _ _)
        refine (integrableOn_iff_integrable_of_support_subset (s := K ×ˢ univ) ?_).mp
          (Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
            (Eventually.of_forall fun p ↦ hC p))
        intro p hp
        by_contra hpK
        exact hp (hfK p fun h1 ↦ hpK ⟨h1, mem_univ _⟩)
      -- Step B: a bump `ρ` and its integral `m > 0`.
      let ρb : ContDiffBump (0 : E) := ⟨R / 2 / 2 / 2, R / 2 / 2, h8, half_lt_self h4⟩
      obtain ⟨ρ, hρdef⟩ : ∃ ρ : E → ℝ, ρ = ρb := ⟨_, rfl⟩
      have hρc : ContDiff ℝ 1 ρ := hρdef ▸ ρb.contDiff
      have hρs : tsupport ρ = closedBall 0 (R / 2 / 2) := hρdef ▸ ρb.tsupport_eq
      have hρ0 : ∀ x, 0 ≤ ρ x := fun x ↦ by rw [hρdef]; exact ρb.nonneg
      have hρcs : HasCompactSupport ρ := by
        rw [HasCompactSupport, hρs]; exact isCompact_closedBall _ _
      obtain ⟨Cρ, hCρ⟩ := hρc.continuous.bounded_above_of_compact_support hρcs
      set m := ∫ x, ρ x ∂vol with hm
      have hm0 : 0 < m := by
        rw [hm, integral_pos_iff_support_of_nonneg hρ0
          (hρc.continuous.integrable_of_hasCompactSupport hρcs), hρdef, ρb.support_eq]
        exact measure_ball_pos _ _ h4
      set c₀ := (∫ y, ρ (y - a) ∂ν) / m with hc₀
      have hρa : ∀ x ∈ ball a (R / 2 / 2), ∫ y, ρ (y - x) ∂ν = ∫ y, ρ (y - a) ∂ν := by
        intro x hx
        have hx' : x - a ∈ ball (0 : E) (R / 2) := by
          rw [mem_ball, dist_zero_right, ← dist_eq_norm]
          exact (mem_ball.mp hx).trans (half_lt_self h2)
        have := hA (fun y ↦ ρ (y - a)) (hρc.comp (contDiff_id.sub contDiff_const)) ?_ (x - a) hx'
        · simpa only [sub_sub, sub_add_cancel] using this
        · refine (tsupport_comp_subset_preimage _ (continuous_sub_right a)).trans ?_
          intro y hy
          rw [mem_preimage, hρs, mem_closedBall, dist_zero_right] at hy
          rw [mem_ball, dist_eq_norm]
          exact hy.trans_lt (half_lt_self h2)
      have hB : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2 / 2) →
          ∫ y, ζ y ∂ν = c₀ * ∫ x, ζ x ∂vol := by
        intro ζ hζ hs
        have hc : HasCompactSupport ζ :=
          (isCompact_closedBall a (R / 2 / 2)).of_isClosed_subset (isClosed_tsupport ζ)
            (hs.trans ball_subset_closedBall)
        obtain ⟨Cζ, hCζ⟩ := hζ.continuous.bounded_above_of_compact_support hc
        have hs2 : tsupport ζ ⊆ ball a (R / 2) := hs.trans (ball_subset_ball (half_le_self h2.le))
        have hbd : ∀ (u w : E), ‖ρ u * ζ w‖ ≤ Cρ * Cζ := fun u w ↦ by
          rw [norm_mul]
          exact mul_le_mul (hCρ u) (hCζ w) (norm_nonneg _) ((norm_nonneg _).trans (hCρ u))
        have i1 : Integrable (fun p : E × E ↦ ρ p.1 * ζ (p.2 - p.1))
            (vol.prod ν) :=
          hI _ ((hρc.continuous.comp continuous_fst).mul
            (hζ.continuous.comp (continuous_snd.sub continuous_fst))) _ hρcs.isCompact
            (fun p hp ↦ by rw [image_eq_zero_of_notMem_tsupport hp, zero_mul])
            ⟨_, fun p ↦ hbd _ _⟩
        have i2 : Integrable (fun p : E × E ↦ ρ (p.2 - p.1) * ζ p.1)
            (vol.prod ν) :=
          hI _ ((hρc.continuous.comp (continuous_snd.sub continuous_fst)).mul
            (hζ.continuous.comp continuous_fst)) _ hc.isCompact
            (fun p hp ↦ by rw [image_eq_zero_of_notMem_tsupport hp, mul_zero])
            ⟨_, fun p ↦ hbd _ _⟩
        rw [hc₀, div_mul_eq_mul_div, eq_div_iff hm0.ne']
        calc (∫ y, ζ y ∂ν) * m = ∫ h, ρ h * ∫ y, ζ y ∂ν ∂vol := by rw [integral_mul_const, mul_comm]
          _ = ∫ h, ρ h * ∫ y, ζ (y - h) ∂ν ∂vol := by
              refine integral_congr_ae (Eventually.of_forall fun h ↦ ?_)
              by_cases hh : ρ h = 0
              · simp only [hh, zero_mul]
              · have hh' : h ∈ ball (0 : E) (R / 2) := by
                  have := subset_tsupport ρ hh
                  rw [hρs] at this
                  exact closedBall_subset_ball (half_lt_self h2) this
                simp only
                rw [hA ζ hζ hs2 h hh']
          _ = ∫ y, ∫ h, ρ h * ζ (y - h) ∂vol ∂ν := by
              simp_rw [← integral_const_mul]
              exact integral_integral_swap i1
          _ = ∫ y, ∫ x, ρ (y - x) * ζ x ∂vol ∂ν := by
              refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
              have := integral_sub_left_eq_self (fun h ↦ ρ h * ζ (y - h)) (vol : Measure (E)) y
              simpa only [sub_sub_cancel] using this.symm
          _ = ∫ x, ∫ y, ρ (y - x) * ζ x ∂ν ∂vol := integral_integral_swap
              (f := fun y x ↦ ρ (y - x) * ζ x) i2.swap
          _ = ∫ x, (∫ y, ρ (y - a) ∂ν) * ζ x ∂vol := by
              refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
              simp only
              rw [integral_mul_const]
              by_cases hx : ζ x = 0
              · rw [hx, mul_zero, mul_zero]
              · rw [hρa x (hs (subset_tsupport _ hx))]
          _ = (∫ y, ρ (y - a) ∂ν) * ∫ x, ζ x ∂vol := integral_const_mul _ _
      -- Step C: the measures agree on open subsets of `ball a (R / 2 / 2 / 2)`, hence on that ball.
      have hc0 : 0 ≤ c₀ := div_nonneg (integral_nonneg fun y ↦ hρ0 _) hm0.le
      have hO : ∀ O : Set E, IsOpen O → O ⊆ ball a (R / 2 / 2 / 2) →
          ν O = ENNReal.ofReal c₀ * vol O := by
        intro O hO hOs
        obtain ⟨f, hfs, hfc, hfr⟩ := hO.exists_contDiff_support_eq (n := 1)
        have hf0 : ∀ x, 0 ≤ f x := fun x ↦ (hfr ⟨x, rfl⟩).1
        set g : ℕ → E → ℝ := fun k x ↦ Real.smoothTransition ((k : ℝ) * f x) with hgdef
        have hg : ∀ k, ContDiff ℝ 1 (g k) := fun k ↦
          Real.smoothTransition.contDiff.comp (contDiff_const.mul hfc)
        have hsupp : ∀ k, Function.support (g k) ⊆ O := by
          intro k x hx
          rw [← hfs]
          intro hfx
          exact hx (by simp only [hgdef, hfx, mul_zero, Real.smoothTransition.zero])
        have hgs : ∀ k, tsupport (g k) ⊆ ball a (R / 2 / 2) := fun k ↦
          (closure_mono ((hsupp k).trans hOs)).trans (closure_ball_subset_closedBall.trans
            (closedBall_subset_ball (half_lt_self h4)))
        have hlim : ∀ x, Tendsto (fun k ↦ g k x) atTop (𝓝 (O.indicator 1 x)) := by
          intro x
          by_cases hx : x ∈ O
          · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm (by rw [← hfs] at hx; exact hx))
            rw [indicator_of_mem hx, Pi.one_apply]
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const hfx).eventually_ge_atTop 1]
              with k hk
            exact (Real.smoothTransition.one_of_one_le hk).symm
          · have hfx : f x = 0 := by
              by_contra h'
              exact hx (hfs ▸ h')
            rw [indicator_of_notMem hx]
            refine tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦ ?_)
            simp only [hgdef, hfx, mul_zero, Real.smoothTransition.zero]
        have hb : ∀ k x, ‖g k x‖ ≤ 1 := fun k x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
        have h1 : Tendsto (fun k ↦ ∫ x, g k x ∂ν) atTop (𝓝 (ν.real O)) := by
          rw [← integral_indicator_one hO.measurableSet]
          exact tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
            (fun k ↦ (hg k).continuous.aestronglyMeasurable) (integrable_const 1)
            (fun k ↦ Eventually.of_forall (hb k)) (Eventually.of_forall hlim)
        have h2 : Tendsto (fun k ↦ ∫ x, g k x ∂vol) atTop (𝓝 (vol.real O)) := by
          rw [← integral_indicator_one hO.measurableSet]
          refine tendsto_integral_of_dominated_convergence ((ball a (R / 2 / 2)).indicator 1)
            (fun k ↦ (hg k).continuous.aestronglyMeasurable)
            ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball)
            (fun k ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall hlim)
          by_cases hx : x ∈ ball a (R / 2 / 2)
          · rw [indicator_of_mem hx]; exact hb k x
          · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs k h),
              norm_zero]
        have h3 : ν.real O = c₀ * vol.real O := tendsto_nhds_unique h1
          ((h2.const_mul c₀).congr fun k ↦ (hB _ (hg k) (hgs k)).symm)
        have hvO : vol O ≠ ∞ := ((measure_mono (hOs.trans ball_subset_closedBall)).trans_lt
          (isCompact_closedBall a _).measure_lt_top).ne
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν O), ← measureReal_def, h3,
          ENNReal.ofReal_mul hc0, measureReal_def, ENNReal.ofReal_toReal hvO]
      refine ⟨c₀, ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
        (fun s hs ↦ ?_) ?_⟩
      · rw [Measure.restrict_apply (IsOpen.measurableSet hs), Measure.smul_apply,
          Measure.restrict_apply (IsOpen.measurableSet hs), smul_eq_mul]
        exact hO _ ((IsOpen.inter hs isOpen_ball)) inter_subset_right
      · rw [Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ,
          smul_eq_mul]
        exact hO _ isOpen_ball subset_rfl

    have hJ' : Measurable fun u ↦ ENNReal.ofReal (1 / J u) :=
        (measurable_const.div hJ).ennreal_ofReal
    have hν : IsFiniteMeasure (ϑ.withDensity fun u ↦ ENNReal.ofReal (1 / J u)) := by
      refine ⟨?_⟩
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine (lintegral_mono_ae (g := fun _ ↦ ENNReal.ofReal (1 / m)) ?_).trans_lt ?_
      · filter_upwards [hJm] with u hu
        exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hm hu)
      · rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    obtain ⟨c, hc⟩ := P4 _ fun ζ hζ hs v ↦ by
      rw [integral_withDensity_eq_integral_toReal_smul hJ' (Eventually.of_forall fun _ ↦
        ENNReal.ofReal_lt_top)]
      refine (integral_congr_ae ?_).trans (h ζ hζ hs v)
      filter_upwards [hJm] with u hu
      rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr (hm.le.trans hu)), smul_eq_mul]
    refine ⟨c, ?_⟩
    have hϑ : ϑ = (ϑ.withDensity fun u ↦ ENNReal.ofReal (1 / J u)).withDensity
        fun u ↦ ENNReal.ofReal (J u) := by
      rw [← withDensity_mul _ hJ' hJ.ennreal_ofReal]
      conv_lhs => rw [← withDensity_one (μ := ϑ)]
      refine withDensity_congr_ae ?_
      filter_upwards [hJm] with u hu
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (one_div_nonneg.mpr (hm.le.trans hu)),
        one_div_mul_cancel (hm.trans_le hu).ne', ENNReal.ofReal_one, Pi.one_apply]
    rw [hϑ, restrict_withDensity measurableSet_ball, hc, withDensity_smul_measure]
  -- the area formula on a chart ball
  have G5g : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      (φ : E → F) (ψ : F → E) (b : E) (r : ℝ) (K : NNReal)
      (hφ : ∀ u ∈ ball b r, ContDiffAt ℝ 1 φ u)
      (hinj : ∀ u ∈ ball b r, Function.Injective (fderiv ℝ φ u))
      (hψφ : ∀ u ∈ ball b r, ψ (φ u) = u) (hK : LipschitzOnWith K φ (ball b r))
      (hm : MeasurableSet (φ '' ball b r)) (hψ : ContinuousOn ψ (φ '' ball b r)),
      ((μHE[Module.finrank ℝ E] : Measure F).restrict (φ '' ball b r)).map ψ =
        ((μHE[Module.finrank ℝ E] : Measure E).restrict (ball b r)).withDensity
          (fun u ↦ ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet) := by
    intro E F _ _ _ _ _ _ _ _ _ _ φ ψ b r K hφ hinj hψφ hK hm hψ
    set d := Module.finrank ℝ E
    have hψm : AEMeasurable ψ ((μHE[d] : Measure F).restrict (φ '' ball b r)) := hψ.aemeasurable hm
    obtain ⟨ν, hνdef⟩ : ∃ ν, ν = ((μHE[d] : Measure F).restrict (φ '' ball b r)).map ψ := ⟨_, rfl⟩
    rw [← hνdef]
    have himg : ∀ A : Set E, ψ ⁻¹' A ∩ φ '' ball b r = φ '' (ball b r ∩ A) := by
      intro A; ext y; constructor
      · rintro ⟨hyA, u, hu, rfl⟩
        exact ⟨u, ⟨hu, by rwa [mem_preimage, hψφ u hu] at hyA⟩, rfl⟩
      · rintro ⟨u, ⟨hu, huA⟩, rfl⟩
        exact ⟨by rwa [mem_preimage, hψφ u hu], u, hu, rfl⟩
    have hν : ∀ A, MeasurableSet A → ν A = μHE[d] (φ '' (ball b r ∩ A)) := fun A hA ↦ by
      rw [hνdef, Measure.map_apply_of_aemeasurable hψm hA, Measure.restrict_apply' hm, himg]
    have hνle : ∀ A, MeasurableSet A → ν A ≤ (K : ℝ≥0∞) ^ d * μHE[d] (ball b r ∩ A) :=
      fun A hA ↦ (hν A hA).trans_le
        (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d (hK.mono inter_subset_left))
    have : IsFiniteMeasure ν := ⟨(hνle univ MeasurableSet.univ).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
        ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top))⟩
    have hac : ν ≪ μHE[d] := Measure.AbsolutelyContinuous.mk fun A hA h0 ↦
      le_antisymm ((hνle A hA).trans (by rw [measure_mono_null inter_subset_right h0, mul_zero]))
        bot_le
    have hνB : ν (ball b r)ᶜ = 0 := by
      rw [hν _ measurableSet_ball.compl, inter_compl_self, image_empty, measure_empty]
    -- the density at every point of the ball
    have hpt : ∀ u ∈ ball b r, ∀ D : ℝ≥0∞,
        Tendsto (fun s ↦ ν (closedBall u s) / μHE[d] (closedBall u s)) (𝓝[>] 0) (𝓝 D) →
        D = ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet := by
      intro u hu D hD
      obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ u := ⟨_, rfl⟩
      rw [← hL]
      have hker : LinearMap.ker (L : E →ₗ[ℝ] F) = ⊥ := LinearMap.ker_eq_bot.mpr (hL ▸ hinj u hu)
      obtain ⟨P', hP'⟩ := (L : E →ₗ[ℝ] F).exists_leftInverse_of_injective hker
      have hPL : ∀ x, P' (L x) = x := fun x ↦ LinearMap.congr_fun hP' x
      obtain ⟨κ, -, hκ⟩ := (L : E →ₗ[ℝ] F).exists_antilipschitzWith hker
      have hxy : ∀ x y : E, ‖x - y‖ ≤ κ * ‖L x - L y‖ := fun x y ↦ by
        have h := hκ.le_mul_dist x y
        rwa [dist_eq_norm, dist_eq_norm] at h
      set J := (L : E →ₗ[ℝ] F).normDet with hJ
      have hJ0 : 0 ≤ J := LinearMap.normDet_nonneg _
      have hstrict : HasStrictFDerivAt φ L u := hL ▸ (hφ u hu).hasStrictFDerivAt one_ne_zero
      have hlin : ∀ t, μHE[d] ((L : E →ₗ[ℝ] F) '' closedBall u t) =
          ENNReal.ofReal J * μHE[d] (closedBall u t) :=
        fun t ↦ (L : E →ₗ[ℝ] F).euclideanHausdorffMeasure_image _
      have hκ1 : (0 : ℝ) < κ + 1 := add_pos_of_nonneg_of_pos κ.2 one_pos
      have key : ∀ δ : ℝ, 0 < δ → δ < 1 →
          D ≤ ENNReal.ofReal ((1 + δ) ^ d * J) ∧ ENNReal.ofReal ((1 - δ) ^ d * J) ≤ D := by
        intro δ hδ hδ1
        have h1δ : 0 < 1 + δ := add_pos one_pos hδ
        have h1δ' : 0 < 1 - δ := sub_pos.mpr hδ1
        obtain ⟨c, hc⟩ : ∃ c : NNReal, c = Real.toNNReal (δ / (κ + 1)) := ⟨_, rfl⟩
        have hc0 : 0 < c := hc ▸ Real.toNNReal_pos.mpr (div_pos hδ hκ1)
        have hcκ : (c : ℝ) * κ ≤ δ := by
          rw [hc, Real.coe_toNNReal _ (div_nonneg hδ.le hκ1.le), div_mul_eq_mul_div,
            div_le_iff₀ hκ1]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le
        obtain ⟨s, hs, hA⟩ := hstrict.approximates_deriv_on_nhds (Or.inr hc0)
        have hA' : ∀ x ∈ s, ∀ y ∈ s, ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖L x - L y‖ := by
          intro x hx y hy
          calc ‖φ x - φ y - (L x - L y)‖ = ‖φ x - φ y - L (x - y)‖ := by rw [map_sub]
            _ ≤ c * ‖x - y‖ := hA x hx y hy
            _ ≤ c * (κ * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hxy x y) c.2
            _ ≤ δ * ‖L x - L y‖ := by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcκ (norm_nonneg _)
        obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (isOpen_ball.mem_nhds hu))
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ closedBall u t ⊆ s ∩ ball b r := by
          filter_upwards [Ioo_mem_nhdsGT hε] with t ht
          exact ⟨ht.1, (closedBall_subset_ball ht.2).trans hεs⟩
        have hνt : ∀ t, closedBall u t ⊆ s ∩ ball b r →
            ν (closedBall u t) = μHE[d] (φ '' closedBall u t) := fun t ht ↦ by
          rw [hν _ measurableSet_closedBall, inter_eq_right.mpr (ht.trans inter_subset_right)]
        constructor
        · refine le_of_tendsto hD ?_
          filter_upwards [hev] with t ht
          refine ENNReal.div_le_of_le_mul ?_
          rw [hνt t ht.2]
          have himg' : φ '' closedBall u t = (fun p ↦ φ (P' p)) ''
              ((L : E →ₗ[ℝ] F) '' closedBall u t) := by
            rw [image_image]
            exact image_congr fun x _ ↦ by rw [ContinuousLinearMap.coe_coe, hPL]
          rw [himg']
          refine (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
            (K := Real.toNNReal (1 + δ)) d ?_).trans ?_
          · refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
            obtain ⟨x, hx, rfl⟩ := hp
            obtain ⟨y, hy, rfl⟩ := hq
            rw [ContinuousLinearMap.coe_coe, hPL, hPL, dist_eq_norm, dist_eq_norm,
              Real.coe_toNNReal _ h1δ.le]
            have h1 := hA' x (ht.2 hx).1 y (ht.2 hy).1
            calc ‖φ x - φ y‖ = ‖(φ x - φ y - (L x - L y)) + (L x - L y)‖ := by rw [sub_add_cancel]
              _ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_add_le _ _
              _ ≤ δ * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add h1 le_rfl
              _ = (1 + δ) * ‖L x - L y‖ := by rw [add_comm, one_add_mul]
          · rw [hlin, ← mul_assoc, ENNReal.ofReal_mul (pow_pos h1δ d).le,
              ENNReal.ofReal_pow h1δ.le]
            rfl
        · refine ge_of_tendsto hD ?_
          filter_upwards [hev] with t ht
          rw [ENNReal.le_div_iff_mul_le (Or.inl (measure_closedBall_pos _ u ht.1).ne')
            (Or.inl measure_closedBall_lt_top.ne), hνt t ht.2]
          have himg' : (L : E →ₗ[ℝ] F) '' closedBall u t = (fun p ↦ L (ψ p)) ''
              (φ '' closedBall u t) := by
            rw [image_image]
            exact image_congr fun x hx ↦ by rw [hψφ x (ht.2 hx).2]; rfl
          have hle : μHE[d] ((L : E →ₗ[ℝ] F) '' closedBall u t) ≤
              (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ d * μHE[d] (φ '' closedBall u t) := by
            rw [himg']
            refine Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d
              (LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_)
            obtain ⟨x, hx, rfl⟩ := hp
            obtain ⟨y, hy, rfl⟩ := hq
            rw [hψφ x (ht.2 hx).2, hψφ y (ht.2 hy).2, dist_eq_norm, dist_eq_norm,
              Real.coe_toNNReal _ (inv_nonneg.mpr h1δ'.le), ← div_eq_inv_mul, le_div_iff₀ h1δ',
              mul_sub, mul_one, sub_le_iff_le_add]
            have h1 := hA' x (ht.2 hx).1 y (ht.2 hy).1
            have h2 : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
              calc ‖L x - L y‖ = ‖(φ x - φ y) - (φ x - φ y - (L x - L y))‖ := by rw [sub_sub_cancel]
                _ ≤ _ := norm_sub_le _ _
            exact h2.trans (add_le_add le_rfl (h1.trans_eq (mul_comm _ _)))
          rw [hlin] at hle
          calc ENNReal.ofReal ((1 - δ) ^ d * J) * μHE[d] (closedBall u t)
              = ENNReal.ofReal ((1 - δ) ^ d) * (ENNReal.ofReal J * μHE[d] (closedBall u t)) := by
                rw [ENNReal.ofReal_mul (pow_pos h1δ' d).le, mul_assoc]
            _ ≤ ENNReal.ofReal ((1 - δ) ^ d) *
                ((Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ d * μHE[d] (φ '' closedBall u t)) :=
                mul_le_mul' le_rfl hle
            _ = μHE[d] (φ '' closedBall u t) := by
                rw [← mul_assoc, show (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) =
                    ENNReal.ofReal (1 - δ)⁻¹ from rfl,
                  ← ENNReal.ofReal_pow (inv_nonneg.mpr h1δ'.le), ← ENNReal.ofReal_mul
                  (pow_pos h1δ' d).le, ← mul_pow, mul_inv_cancel₀ h1δ'.ne', one_pow,
                  ENNReal.ofReal_one, one_mul]
      apply le_antisymm
      · have ht : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal ((1 + δ) ^ d * J)) (𝓝[>] 0)
            (𝓝 (ENNReal.ofReal J)) := by
          have h : Tendsto (fun δ : ℝ ↦ (1 + δ) ^ d * J) (𝓝 0) (𝓝 ((1 + 0) ^ d * J)) :=
            ((tendsto_const_nhds.add tendsto_id).pow d).mul tendsto_const_nhds
          rw [add_zero, one_pow, one_mul] at h
          exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
        refine ge_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ hδ
        exact (key δ hδ.1 hδ.2).1
      · have ht : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal ((1 - δ) ^ d * J)) (𝓝[>] 0)
            (𝓝 (ENNReal.ofReal J)) := by
          have h : Tendsto (fun δ : ℝ ↦ (1 - δ) ^ d * J) (𝓝 0) (𝓝 ((1 - 0) ^ d * J)) :=
            ((tendsto_const_nhds.sub tendsto_id).pow d).mul tendsto_const_nhds
          rw [sub_zero, one_pow, one_mul] at h
          exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
        refine le_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ hδ
        exact (key δ hδ.1 hδ.2).2
    have hae : ∀ᵐ u ∂((μHE[d] : Measure E).restrict (ball b r)),
        ν.rnDeriv μHE[d] u = ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν (μHE[d] : Measure E)] with u hu hub
      exact hpt u hub _ hu
    calc ν = ν.restrict (ball b r) :=
          (Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hνB)).symm
      _ = ((μHE[d] : Measure E).withDensity (ν.rnDeriv μHE[d])).restrict (ball b r) := by
          rw [Measure.withDensity_rnDeriv_eq ν _ hac]
      _ = ((μHE[d] : Measure E).restrict (ball b r)).withDensity (ν.rnDeriv μHE[d]) :=
          restrict_withDensity measurableSet_ball _
      _ = _ := withDensity_congr_ae hae
  -- the calculus half of the coordinate divergence identity
  have GPx : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (NJ : (E →L[ℝ] F) → ℝ) (φ : E → F) (ζ : E → ℝ) (u v : E) (Y : E → E)
      (hφ : ContDiffAt ℝ 2 φ u) (hN : DifferentiableAt ℝ NJ (fderiv ℝ φ u))
      (hN0 : NJ (fderiv ℝ φ u) ≠ 0) (hζ : DifferentiableAt ℝ ζ u)
      (hY : ∀ w, Y w = (ζ w / NJ (fderiv ℝ φ w)) • v),
      ∃ ℓ : E →L[ℝ] ℝ,
        HasDerivAt (fun t : ℝ ↦ NJ (fderiv ℝ φ u + t • fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) u))
          (fderiv ℝ ζ u v - NJ (fderiv ℝ φ u) * ℓ v +
            fderiv ℝ NJ (fderiv ℝ φ u) (ℓ.smulRight (fderiv ℝ φ u v))) 0 ∧
        HasDerivAt (fun t : ℝ ↦ NJ (fderiv ℝ φ u + t • ℓ.smulRight (fderiv ℝ φ u v)))
          (fderiv ℝ NJ (fderiv ℝ φ u) (ℓ.smulRight (fderiv ℝ φ u v))) 0 := by
    intro E F _ _ _ _ _ _ NJ φ ζ u v Y hφ hN hN0 hζ hY
    have hNd := hN.hasFDerivAt
    have hDφd := ((hφ.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt
      one_ne_zero).hasFDerivAt
    have hJd := hNd.comp u hDφd
    obtain ⟨ℓ, hgd⟩ : ∃ ℓ, HasFDerivAt (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) ℓ u :=
      ⟨_, (hζ.mul (hJd.differentiableAt.inv hN0)).hasFDerivAt⟩
    refine ⟨ℓ, (hNd.hasLineDerivAt _).congr_deriv ?_, hNd.hasLineDerivAt _⟩
    have hfun : (fun w ↦ fderiv ℝ φ w (Y w)) =
        (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) • fun w ↦ fderiv ℝ φ w v :=
      funext fun w ↦ by rw [hY, map_smul]; rfl
    have hsym := hφ.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le
    have hKe : fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) u =
        (ζ u / NJ (fderiv ℝ φ u)) • fderiv ℝ (fderiv ℝ φ) u v + ℓ.smulRight (fderiv ℝ φ u v) := by
      have hWd : HasFDerivAt (fun w ↦ fderiv ℝ φ w v)
          ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) u)) u :=
        (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp u hDφd
      rw [hfun, (hgd.smul hWd).fderiv]
      congr 2
      ext w
      exact hsym w v
    have hev2 : ζ =ᶠ[𝓝 u] (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) * (NJ ∘ fderiv ℝ φ) := by
      filter_upwards [hJd.continuousAt.eventually_ne hN0] with w hw
      exact (div_mul_cancel₀ _ hw).symm
    rw [hKe, map_add, map_smul, smul_eq_mul, hev2.fderiv_eq, (hgd.mul hJd).fderiv]
    exact congrArg (· + _) (add_sub_cancel_right (G := ℝ) _ _).symm
  -- `normDet` on charts
  obtain ⟨NJ, hNJ⟩ : ∃ NJ : (Euclidean n →L[ℝ] Euclidean N) → ℝ,
      ∀ T, NJ T = (T : Euclidean n →ₗ[ℝ] Euclidean N).normDet := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hNc, GN⟩ := GNg _ _ NJ hNJ
  have hNpos : ∀ T : Euclidean n →L[ℝ] Euclidean N, Function.Injective T → 0 < NJ T := by
    intro T hT
    rw [hNJ]
    exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm (mt
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp (not_not.mpr (LinearMap.ker_eq_bot.mpr hT))))
  have hN0 : ∀ T, 0 ≤ NJ T := fun T ↦ by rw [hNJ]; exact LinearMap.normDet_nonneg _
  have G4w : ∀ (ϑ : Measure (Euclidean n)) [IsFiniteMeasure ϑ] (J : Euclidean n → ℝ)
      (a : Euclidean n) (R m : ℝ), 0 < R → 0 < m → Measurable J → (∀ᵐ u ∂ϑ, m ≤ J u) →
      (∀ ζ : Euclidean n → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v,
        ∫ u, (1 / J u) * fderiv ℝ ζ u v ∂ϑ = 0) →
      ∃ c : ℝ, ϑ.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
        (volume.restrict (ball a (R / 2 / 2 / 2))).withDensity (fun u ↦ ENNReal.ofReal (J u)) := by
    intro ϑ _ J a R m hR hm hJ hJm h
    exact G4wg _ volume ϑ J a R m hR hm hJ hJm h
  have G5 : ∀ (φ : Euclidean n → Euclidean N) (ψ : Euclidean N → Euclidean n) (b : Euclidean n)
      (r : ℝ) (K : NNReal), (∀ u ∈ ball b r, ContDiffAt ℝ 1 φ u) →
      (∀ u ∈ ball b r, Function.Injective (fderiv ℝ φ u)) →
      (∀ u ∈ ball b r, ψ (φ u) = u) → LipschitzOnWith K φ (ball b r) →
      MeasurableSet (φ '' ball b r) → ContinuousOn ψ (φ '' ball b r) →
      ((μHE[n] : Measure (Euclidean N)).restrict (φ '' ball b r)).map ψ =
        (volume.restrict (ball b r)).withDensity (fun u ↦ ENNReal.ofReal (NJ (fderiv ℝ φ u))) := by
    intro φ ψ b r K hφ hinj hψφ hK hm hψ
    have h := G5g _ _ φ ψ b r K hφ hinj hψφ hK hm hψ
    rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
    rw [h]
    congr 1
    funext u
    rw [hNJ]
  -- basic facts
  have hU : IsOpen U := V.isOpen_domain
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = V.weight := ⟨_, rfl⟩
  rw [← hμ] at hM
  have hμU : μ Uᶜ = 0 := by rw [hμ, V.weight_apply hU.measurableSet.compl]; exact V.supported
  have hμM : μ (M ∩ U)ᶜ = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hμU μ.measure_compl_support)
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hx ⟨hM ⟨h.1, h.2⟩, h.1⟩
  have hVM : ∀ᵐ z ∂V.measure, z.1 ∈ M ∩ U :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [← Varifold.weight, ← hμ]; exact hμM)
  have hfst : ∀ z ∈ V.measure.support, z.1 ∈ μ.support := fun z hz ↦
    Measure.support_subset_of_isClosed (μ.isClosed_support.preimage continuous_fst)
      (ae_of_ae_map measurable_fst.aemeasurable
        (by rw [← Varifold.weight, ← hμ]; exact μ.support_mem_ae)) hz
  -- the tangential divergence as a trace
  have hTD : ∀ (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n),
      Varifold.tangentialDivergence X x S = LinearMap.trace ℝ (Euclidean N)
        (S.projectionLinearMap ∘ₗ (fderiv ℝ X x : Euclidean N →ₗ[ℝ] Euclidean N)) := by
    intro X x S
    rw [Varifold.tangentialDivergence, LinearMap.trace_eq_matrix_trace ℝ
      Grassmannian.coordinateBasis.toBasis, LinearMap.toMatrix_comp
        Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis]
    simp [Varifold.jacobian_eq_toMatrix]
  -- P1: every support plane is the chart tangent plane
  have hP1 : ∀ z ∈ V.measure.support, z.1 ∈ U → ∀ (D : Set (Euclidean n)) (W : Set (Euclidean N))
      (φ : Euclidean n → Euclidean N), Chapter02.IsSimonLocalRepresentation 2 M D W φ →
      ∀ a ∈ D, φ a = z.1 →
        z.2.plane = LinearMap.range (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N) := by
    intro z hz hzU D W φ hφ a ha hφa
    obtain ⟨ψ, T₀, hT₀o, hφaT₀, hψc, hψD, hψM⟩ := GI _ _ M W D φ hφ a ha
    obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ a := ⟨_, rfl⟩
    rw [← hL]
    have hzM : z.1 ∈ M := hM ⟨hzU, hfst z hz⟩
    have hψa : ψ z.1 = a := hφ.injOn (hψD (hφa ▸ hφaT₀)) ha (by
      rw [hψM z.1 ⟨hzM, hφa ▸ hφaT₀⟩, hφa])
    have key : ∀ e ∈ (LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N))ᗮ,
        z.2.projectionLinearMap e = 0 := by
      intro e he
      obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp (hT₀o.inter hU) z.1 ⟨hφa ▸ hφaT₀, hzU⟩
      let χ : ContDiffBump z.1 :=
          ⟨r / 2 / 2, r / 2, half_pos (half_pos hr), half_lt_self (half_pos hr)⟩
      have hχs : tsupport χ ⊆ T₀ ∩ U := by
        rw [χ.tsupport_eq]; exact (closedBall_subset_ball (half_lt_self hr)).trans hrT
      have hφc2 : ContDiffOn ℝ 2 φ D := hφ.contDiffOn
      have hg : ContDiffOn ℝ 2 (fun y ↦ inner ℝ e (y - φ (ψ y))) T₀ :=
        (contDiffOn_const.inner ℝ (contDiffOn_id.sub (hφc2.comp hψc hψD)))
      obtain ⟨f, hfdef⟩ : ∃ f : Euclidean N → ℝ, f = fun y ↦ χ y • inner ℝ e (y - φ (ψ y)) :=
        ⟨_, rfl⟩
      have hf : ContDiff ℝ 2 f := hfdef ▸ GCut _ _ 2 χ _ T₀ hT₀o χ.contDiff hg
        (hχs.trans inter_subset_left)
      have hfs : tsupport f ⊆ T₀ ∩ U := hfdef ▸ (tsupport_smul_subset_left _ _).trans hχs
      have hfc : HasCompactSupport f := hfdef ▸ χ.hasCompactSupport.smul_right
      have hfM : ∀ y ∈ M, f y = 0 := by
        intro y hy
        by_cases hyT : y ∈ T₀
        · rw [hfdef]; simp only [hψM y ⟨hy, hyT⟩, sub_self, inner_zero_right, smul_zero]
        · exact image_eq_zero_of_notMem_tsupport fun h ↦ hyT (hfs h).1
      obtain ⟨G, hGdef⟩ : ∃ G : Euclidean N → Euclidean N,
          G = fun y ↦ (InnerProductSpace.toDual ℝ (Euclidean N)).symm (fderiv ℝ f y) := ⟨_, rfl⟩
      have hG : ContDiff ℝ 1 G := hGdef ▸
        (InnerProductSpace.toDual ℝ (Euclidean N)).symm.contDiff.comp
          (hf.fderiv_right one_add_one_eq_two.le)
      have hfd : ∀ y, HasFDerivAt f (fderiv ℝ f y) y := fun y ↦
        (hf.differentiable two_ne_zero y).hasFDerivAt
      -- the gradient at the base point is `e`
      have hGz : G z.1 = e := by
        have hψd : DifferentiableAt ℝ ψ z.1 :=
          (hψc.contDiffAt (hT₀o.mem_nhds (hφa ▸ hφaT₀))).differentiableAt two_ne_zero
        have hφd : HasFDerivAt φ L (ψ z.1) := by
          rw [hψa, hL]
          exact ((hφc2.contDiffAt (hφ.isOpen_source.mem_nhds ha)).differentiableAt
            two_ne_zero).hasFDerivAt
        have hgd : HasFDerivAt (fun y ↦ inner ℝ e (y - φ (ψ y)))
            ((innerSL ℝ e).comp (ContinuousLinearMap.id ℝ _ - L.comp (fderiv ℝ ψ z.1))) z.1 :=
          (innerSL ℝ e).hasFDerivAt.comp z.1
            ((hasFDerivAt_id z.1).sub (hφd.comp z.1 hψd.hasFDerivAt))
        have hχd := (χ.contDiff (n := 1)).differentiable one_ne_zero z.1
        have h1 := hχd.hasFDerivAt.smul hgd
        rw [show ((χ : Euclidean N → ℝ) • fun y ↦ inner ℝ e (y - φ (ψ y))) = f from hfdef.symm]
            at h1
        have h2 : fderiv ℝ f z.1 = innerSL ℝ e := by
          rw [h1.fderiv]
          ext v
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
            χ.one_of_mem_closedBall (mem_closedBall_self (half_pos (half_pos hr)).le), one_smul,
            innerSL_apply_apply, hψa, hφa, sub_self, inner_zero_right, smul_eq_mul,
            mul_zero, add_zero, inner_sub_right]
          rw [show inner ℝ e (L ((fderiv ℝ ψ z.1) v)) = 0 from
            (Submodule.mem_orthogonal' _ e).mp he _
              (LinearMap.mem_range_self (L : Euclidean n →ₗ[ℝ] Euclidean N) _), sub_zero]
        rw [hGdef]
        simp only [h2]
        exact (InnerProductSpace.toDual ℝ (Euclidean N)).symm_apply_apply e
      -- the test field `f ∇f`
      let X : Varifold.TestVectorField (N := N) U :=
        ⟨fun y ↦ f y • G y, (hf.of_le one_le_two).smul hG, hfc.smul_right,
          (tsupport_smul_subset_left _ _).trans (hfs.trans inter_subset_right)⟩
      have hdiv : ∀ (y : Euclidean N) (S : Grassmannian N n), f y = 0 →
          Varifold.tangentialDivergence X y S = ‖S.projectionLinearMap (G y)‖ ^ 2 := by
        intro y S hy
        have hd := ((hfd y).smul (hG.differentiable one_ne_zero y).hasFDerivAt).fderiv
        rw [hy, zero_smul, zero_add] at hd
        change Varifold.tangentialDivergence (f • G) y S = _
        rw [hTD, hd, show S.projectionLinearMap ∘ₗ
            (((fderiv ℝ f y).smulRight (G y) : Euclidean N →L[ℝ] Euclidean N) :
              Euclidean N →ₗ[ℝ] Euclidean N) =
            (fderiv ℝ f y : Euclidean N →ₗ[ℝ] ℝ).smulRight (S.projectionLinearMap (G y)) from
          LinearMap.ext fun v ↦ map_smul S.projectionLinearMap (fderiv ℝ f y v) (G y),
          LinearMap.trace_smulRight]
        have hG' : fderiv ℝ f y (S.projectionLinearMap (G y)) =
            inner ℝ (G y) (S.projectionLinearMap (G y)) := by
          rw [hGdef]; exact (InnerProductSpace.toDual_symm_apply).symm
        rw [ContinuousLinearMap.coe_coe, hG']
        calc inner ℝ (G y) (S.projectionLinearMap (G y))
            = inner ℝ (G y) (S.projectionLinearMap (S.projectionLinearMap (G y))) := by
              rw [← LinearMap.comp_apply, S.projectionLinearMap_comp_self]
          _ = inner ℝ (S.projectionLinearMap (G y)) (S.projectionLinearMap (G y)) :=
              (S.projectionLinearMap_isSymmetric _ _).symm
          _ = ‖S.projectionLinearMap (G y)‖ ^ 2 := real_inner_self_eq_norm_sq _
      have hint : ∫ z', Varifold.tangentialDivergence X z'.1 z'.2 ∂V.measure = 0 := hV X
      have hnn : 0 ≤ᵐ[V.measure] fun z' ↦ Varifold.tangentialDivergence X z'.1 z'.2 := by
        filter_upwards [hVM] with z' hz'
        rw [hdiv _ _ (hfM _ hz'.1)]
        exact sq_nonneg _
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
        (V.integrable_tangentialDivergence X X.contDiff X.compactSupport X.support_subset)).mp hint
      have hz0 : Varifold.tangentialDivergence X z.1 z.2 = 0 :=
        Measure.support_subset_of_isClosed
          (isClosed_eq (Varifold.continuous_tangentialDivergence X.contDiff) continuous_const)
          hae hz
      rw [hdiv _ _ (hfM _ hzM), hGz] at hz0
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz0)
    have hle : z.2.plane ≤ LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N) := by
      intro s hs
      rw [← Submodule.orthogonal_orthogonal (LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N))]
      intro e he
      rw [← z.2.projectionLinearMap_apply_of_mem hs, ← z.2.projectionLinearMap_isSymmetric,
        key e he, inner_zero_left]
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [z.2.finrank_plane, LinearMap.finrank_range_of_inj (hL ▸ hφ.injective_fderiv ha),
        finrank_euclideanSpace_fin])
  -- P2: the plane field `T`
  have hGext : ∀ S₁ S₂ : Grassmannian N n, S₁.plane = S₂.plane → S₁ = S₂ := by
    intro S₁ S₂ h
    rw [← Grassmannian.ofSubmodule_plane S₁, ← Grassmannian.ofSubmodule_plane S₂]
    congr 1
  obtain ⟨P₀⟩ : Nonempty (Grassmannian N n) := by
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨D₀, W₀, φ₀, hxW₀, hφ₀⟩ := hSM.exists_localRepresentation hx₀
    obtain ⟨a₀, ha₀, -⟩ : x₀ ∈ φ₀ '' D₀ := hφ₀.image_eq ▸ ⟨hxW₀, hx₀⟩
    exact ⟨Grassmannian.ofSubmodule (LinearMap.range (fderiv ℝ φ₀ a₀ :
      Euclidean n →ₗ[ℝ] Euclidean N)) (by rw [LinearMap.finrank_range_of_inj
        (hφ₀.injective_fderiv ha₀), finrank_euclideanSpace_fin])⟩
  have hfib : ∀ x ∈ μ.support, ∃ S, (x, S) ∈ V.measure.support := by
    intro x hx
    by_contra h
    simp only [not_exists] at h
    obtain ⟨O, Q, hO, -, hxO, hQ, hOQ⟩ := generalized_tube_lemma isCompact_singleton
      isCompact_univ V.measure.isOpen_compl_support
      (fun p hp ↦ by
        obtain ⟨y, S⟩ := p
        obtain rfl : y = x := hp.1
        exact h S)
    refine ((Measure.mem_support_iff_forall x).mp hx O (hO.mem_nhds (hxO rfl))).ne' ?_
    rw [hμ, V.weight_apply hO.measurableSet]
    exact measure_mono_null (fun p hp ↦ hOQ ⟨hp.1, hQ (mem_univ _)⟩)
      V.measure.measure_compl_support
  classical
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclidean N → Grassmannian N n, ∀ x ∈ μ.support,
      (x, τ x) ∈ V.measure.support :=
    ⟨fun x ↦ if h : ∃ S, (x, S) ∈ V.measure.support then h.choose else P₀,
      fun x hx ↦ by simp only [dif_pos (hfib x hx)]; exact (hfib x hx).choose_spec⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Euclidean N → Grassmannian N n,
      T = (U ∩ μ.support).piecewise τ (fun _ ↦ P₀) := ⟨_, rfl⟩
  have hTτ : ∀ x ∈ U ∩ μ.support, T x = τ x := fun x hx ↦ by
    rw [hTdef]; exact piecewise_eq_of_mem _ _ _ hx
  have hTspt : ∀ x ∈ U ∩ μ.support, (x, T x) ∈ V.measure.support := fun x hx ↦
    hTτ x hx ▸ hτ x hx.2
  have hTuniq : ∀ z ∈ V.measure.support, z.1 ∈ U → z.2 = T z.1 := by
    intro z hz hzU
    have hx : z.1 ∈ U ∩ μ.support := ⟨hzU, hfst z hz⟩
    obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation (hM hx)
    obtain ⟨a, ha, hφa⟩ : z.1 ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hM hx⟩
    exact hGext _ _ ((hP1 z hz hzU D W φ hφ a ha hφa).trans
      (hP1 (z.1, T z.1) (hTspt z.1 hx) hzU D W φ hφ a ha hφa).symm)
  have hTc : ContinuousOn T (U ∩ μ.support) := by
    intro x hx
    rw [ContinuousWithinAt, _root_.tendsto_nhds]
    intro Q hQ hTxQ
    obtain ⟨O, Q', hO, -, hxO, hQQ', hOQ'⟩ := generalized_tube_lemma isCompact_singleton
      hQ.isClosed_compl.isCompact V.measure.isOpen_compl_support (by
        rintro ⟨y, S⟩ ⟨hy, hS⟩ hyS
        obtain rfl : y = x := hy
        exact hS ((congrArg (· ∈ Q) (hTuniq (y, S) hyS hx.1)).mpr hTxQ))
    filter_upwards [inter_mem_nhdsWithin _ (hO.mem_nhds (hxO rfl))] with y hy
    by_contra hyQ
    exact hOQ' (show (y, T y) ∈ O ×ˢ Q' from ⟨hy.2, hQQ' hyQ⟩) (hTspt y hy.1)
  have hTm : Measurable T := by
    have h := ContinuousOn.measurable_piecewise (f := τ) (g := fun _ ↦ P₀)
      (hTc.congr fun x hx ↦ (hTτ x hx).symm) continuousOn_const
      (hU.measurableSet.inter μ.isClosed_support.measurableSet)
    rwa [← hTdef] at h
  have hgm : Measurable fun x : Euclidean N ↦ (x, T x) := measurable_id.prodMk hTm
  have hVT : V.measure = μ.map (fun x ↦ (x, T x)) := by
    rw [hμ, Varifold.weight, Measure.map_map (show Measurable fun x : Euclidean N ↦ (x, T x) from
      measurable_id.prodMk hTm) measurable_fst,
      Measure.map_congr (g := id) ?_, Measure.map_id]
    filter_upwards [V.measure.support_mem_ae, hVM] with z hz hzM
    exact Prod.ext rfl (hTuniq z hz hzM.2).symm
  -- the Euclidean half of the coordinate divergence identity
  have hGE : ∀ (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
      (L : Euclidean n →L[ℝ] Euclidean N), DifferentiableAt ℝ X x →
      S.plane = LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N) →
      HasDerivAt (fun t : ℝ ↦ NJ (L + t • (fderiv ℝ X x).comp L))
        (Varifold.tangentialDivergence X x S * NJ L) 0 := by
    intro X x S L hX hS
    refine ((Varifold.hasDerivAt_tangentialJacobianReal_id_add_smul X x S hX).mul_const
      (NJ L)).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    have hd := HasFDerivAt.fderiv (f := fun y ↦ y + t • X y)
      ((hasFDerivAt_id x).add (hX.hasFDerivAt.const_smul t))
    simp only [Varifold.tangentialJacobianReal, Varifold.tangentialDerivative, hd, hNJ]
    have hdr : ∀ (g : Euclidean N →ₗ[ℝ] Euclidean N) (p q : Submodule ℝ (Euclidean N)), p = q →
        (g.domRestrict p).normDet = (g.domRestrict q).normDet := by rintro g p q rfl; rfl
    rw [hdr _ _ _ hS, ← LinearMap.normDet_comp]
    congr 1
  -- local constancy
  have hLC : ∀ x₀ ∈ M ∩ U, ∃ O : Set (Euclidean N), IsOpen O ∧ x₀ ∈ O ∧ O ⊆ U ∧ ∃ c : ℝ≥0∞,
      c ≠ ∞ ∧ μ.restrict O = c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ O) ∧
      μHE[n] (M ∩ O) ≠ ∞ ∧ ∀ O', IsOpen O' → x₀ ∈ O' → 0 < μHE[n] (M ∩ O' ∩ O) := by
    intro x₀ hx₀
    obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx₀.1
    obtain ⟨a, ha, hφa⟩ : x₀ ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hx₀.1⟩
    obtain ⟨ψ, T₀, hT₀o, hφaT₀, hψc, hψD, hψM⟩ := GI _ _ M W D φ hφ a ha
    have hx₀T : x₀ ∈ T₀ := hφa ▸ hφaT₀
    have hDo : IsOpen D := hφ.isOpen_source
    have hφc2 : ContDiffOn ℝ 2 φ D := hφ.contDiffOn
    have hφM : ∀ w ∈ D, φ w ∈ M := fun w hw ↦ (hφ.image_eq ▸ mem_image_of_mem φ hw).2
    have hψφ : ∀ w ∈ D, φ w ∈ T₀ → ψ (φ w) = w := fun w hw hwT ↦
      hφ.injOn (hψD hwT) hw (hψM _ ⟨hφM w hw, hwT⟩)
    have hψa : ψ x₀ = a := by rw [← hφa]; exact hψφ a ha hφaT₀
    obtain ⟨ρ, hρ, hρT⟩ := Metric.isOpen_iff.mp (hT₀o.inter hU) x₀ ⟨hx₀T, hx₀.2⟩
    have hK₀ : closedBall x₀ (ρ / 2) ⊆ T₀ ∩ U :=
      (closedBall_subset_ball (half_lt_self hρ)).trans hρT
    have hρ2 : 0 < ρ / 2 := half_pos hρ
    have hρ8 : 0 < ρ / 2 / 2 / 2 := half_pos (half_pos hρ2)
    obtain ⟨R, hR, hRD⟩ : ∃ R > 0, ball a R ⊆ D ∩ φ ⁻¹' ball x₀ (ρ / 2 / 2 / 2) :=
      Metric.mem_nhds_iff.mp (inter_mem (hDo.mem_nhds ha)
        ((hφc2.continuousOn.continuousAt (hDo.mem_nhds ha)).preimage_mem_nhds
          (by rw [hφa]; exact ball_mem_nhds x₀ hρ8)))
    have hDφ := hφc2.fderiv_of_isOpen hDo (m := 1) one_add_one_eq_two.le
    have hJc : ContDiffOn ℝ 1 (fun w ↦ NJ (fderiv ℝ φ w)) D := fun w hw ↦
      ((GN _ (hφ.injective_fderiv hw)).comp w (hDφ.contDiffAt (hDo.mem_nhds hw))).contDiffWithinAt
    have hJpos : ∀ w ∈ D, 0 < NJ (fderiv ℝ φ w) := fun w hw ↦ hNpos _ (hφ.injective_fderiv hw)
    -- a positive lower bound for `J ∘ ψ` near `x₀`
    have hψK : ∀ x ∈ closedBall x₀ (ρ / 2), ψ x ∈ D := fun x hx ↦ hψD (hK₀ hx).1
    obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x₀ (ρ / 2)).exists_isMinOn
      ⟨x₀, mem_closedBall_self hρ2.le⟩
      (hJc.continuousOn.comp (hψc.continuousOn.mono fun x hx ↦ (hK₀ hx).1) hψK)
    have hm : 0 < NJ (fderiv ℝ φ (ψ xm)) := hJpos _ (hψK xm hxm)
    -- the weighted pulled-back measure
    have hψB : ContinuousOn ψ (ball x₀ (ρ / 2)) :=
      hψc.continuousOn.mono fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).1
    have hψm : AEMeasurable ψ (μ.restrict (ball x₀ (ρ / 2))) := hψB.aemeasurable measurableSet_ball
    have hμK : μ (closedBall x₀ (ρ / 2)) ≠ ∞ := by
      rw [hμ]; exact V.weight_finite_on_compact _ (isCompact_closedBall _ _)
          (hK₀.trans inter_subset_right)
    obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : Measure (Euclidean n), ϑ = (μ.restrict (ball x₀ (ρ / 2))).map ψ :=
        ⟨_, rfl⟩
    have hϑfin : ϑ univ < ∞ := by
      rw [hϑ, Measure.map_apply_of_aemeasurable hψm MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt (lt_top_iff_ne_top.mpr hμK)
    have hJm : Measurable (fun u ↦ NJ (fderiv ℝ φ u)) := hNc.measurable.comp (measurable_fderiv ℝ φ)
    have hϑm : ∀ᵐ u ∂ϑ, NJ (fderiv ℝ φ (ψ xm)) ≤ NJ (fderiv ℝ φ u) := by
      rw [hϑ, ae_map_iff hψm (measurableSet_le measurable_const hJm),
        ae_restrict_iff' measurableSet_ball]
      exact Eventually.of_forall fun x hx ↦ (isMinOn_iff.mp hmin) x (ball_subset_closedBall hx)
    -- the hypothesis of the distributional constancy lemma, from tangent test fields
    have hT₀B : ball x₀ (ρ / 2) ⊆ T₀ := fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).1
    have hMU : M ∩ U ∈ ae μ := mem_ae_iff.mpr hμM
    have hG4h : ∀ ζ : Euclidean n → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2) → ∀ v,
        ∫ u, (1 / NJ (fderiv ℝ φ u)) * fderiv ℝ ζ u v ∂ϑ = 0 := by
      intro ζ hζ hζs v
      obtain ⟨Y, hY⟩ : ∃ Y : Euclidean n → Euclidean n,
          ∀ w, Y w = (ζ w / NJ (fderiv ℝ φ w)) • v := ⟨_, fun _ ↦ rfl⟩
      have hYc : ContDiffOn ℝ 1 Y D := by
        rw [funext hY]
        exact (hζ.contDiffOn.div hJc fun w hw ↦ (hJpos w hw).ne').smul contDiffOn_const
      have hY0 : ∀ w, w ∉ ball a (R / 2) → Y w = 0 := fun w hw ↦ by
        rw [hY, image_eq_zero_of_notMem_tsupport (fun h ↦ hw (hζs h)), zero_div, zero_smul]
      let χ : ContDiffBump x₀ := ⟨ρ / 2 / 2 / 2, ρ / 2 / 2, hρ8, half_lt_self (half_pos hρ2)⟩
      have hχs : tsupport χ ⊆ ball x₀ (ρ / 2) := by
        rw [χ.tsupport_eq]; exact closedBall_subset_ball (half_lt_self hρ2)
      obtain ⟨Xf, hXf⟩ : ∃ Xf : Euclidean N → Euclidean N,
          Xf = fun y ↦ χ y • fderiv ℝ φ (ψ y) (Y (ψ y)) := ⟨_, rfl⟩
      have hψ1 : ContDiffOn ℝ 1 ψ T₀ := hψc.of_le one_le_two
      have hXc : ContDiff ℝ 1 Xf := by
        rw [hXf]
        exact GCut _ _ 1 χ _ T₀ hT₀o χ.contDiff ((hDφ.comp hψ1 hψD).clm_apply
          (hYc.comp hψ1 hψD)) (hχs.trans hT₀B)
      have hXs : tsupport Xf ⊆ ball x₀ (ρ / 2) := by
        rw [hXf]; exact (tsupport_smul_subset_left _ _).trans hχs
      let X : Varifold.TestVectorField (N := N) U := ⟨Xf, hXc,
        (isCompact_closedBall x₀ (ρ / 2)).of_isClosed_subset (isClosed_tsupport _)
          (hXs.trans ball_subset_closedBall),
        hXs.trans fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).2⟩
      -- the coordinate divergence identity at chart points
      have hdiv : ∀ x ∈ ball x₀ (ρ / 2), x ∈ M → x ∈ μ.support →
          Varifold.tangentialDivergence Xf x (T x) =
            (1 / NJ (fderiv ℝ φ (ψ x))) * fderiv ℝ ζ (ψ x) v := by
        intro x hxB hxM hxs
        have hxT : x ∈ T₀ := hT₀B hxB
        have hxU : x ∈ U := (hK₀ (ball_subset_closedBall hxB)).2
        have hu : ψ x ∈ D := hψD hxT
        have hφu : φ (ψ x) = x := hψM x ⟨hxM, hxT⟩
        have hplane := hP1 (x, T x) (hTspt x ⟨hxU, hxs⟩) hxU D W φ hφ (ψ x) hu hφu
        have hev : (fun w ↦ Xf (φ w)) =ᶠ[𝓝 (ψ x)] fun w ↦ fderiv ℝ φ w (Y w) := by
          filter_upwards [hDo.mem_nhds hu,
            (hφc2.continuousOn.continuousAt (hDo.mem_nhds hu)).preimage_mem_nhds
              (hT₀o.mem_nhds (by rw [hφu]; exact hxT))] with w hw hwT
          rw [hXf]
          simp only [hψφ w hw hwT]
          by_cases hwB : w ∈ ball a (R / 2)
          · rw [χ.one_of_mem_closedBall (ball_subset_closedBall
              (hRD (ball_subset_ball (half_le_self hR.le) hwB)).2), one_smul]
          · rw [hY0 w hwB, map_zero, smul_zero]
        have hφd : DifferentiableAt ℝ φ (ψ x) :=
          (hφc2.contDiffAt (hDo.mem_nhds hu)).differentiableAt two_ne_zero
        have hK : (fderiv ℝ Xf x).comp (fderiv ℝ φ (ψ x)) =
            fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) (ψ x) := by
          rw [← hev.fderiv_eq]
          have := fderiv_comp (ψ x) (hXc.differentiable one_ne_zero (φ (ψ x))) hφd
          rw [hφu] at this
          exact this.symm
        have h1 := hGE Xf x (T x) (fderiv ℝ φ (ψ x)) (hXc.differentiable one_ne_zero x) hplane
        rw [hK] at h1
        -- the calculus half of the identity, from the generic lemma
        obtain ⟨ℓ, hK1, hK2⟩ := GPx _ _ NJ φ ζ (ψ x) v Y (hφc2.contDiffAt (hDo.mem_nhds hu))
          ((GN _ (hφ.injective_fderiv hu)).differentiableAt one_ne_zero) (hJpos _ hu).ne'
          (hζ.differentiable one_ne_zero _) hY
        have e1 := h1.unique hK1
        -- the rank-one part, through `hGE` for an auxiliary linear field
        obtain ⟨P', hP'⟩ :=
            ((fderiv ℝ φ (ψ x)) : Euclidean n →ₗ[ℝ] Euclidean N).exists_leftInverse_of_injective
          (LinearMap.ker_eq_bot.mpr (hφ.injective_fderiv hu))
        obtain ⟨Pl, hPl⟩ : ∃ Pl : Euclidean N →L[ℝ] Euclidean n, ∀ w, Pl (fderiv ℝ φ (ψ x) w) = w :=
          ⟨LinearMap.toContinuousLinearMap P', fun w ↦ LinearMap.congr_fun hP' w⟩
        obtain ⟨X₂, hX₂⟩ : ∃ X₂ : Euclidean N →L[ℝ] Euclidean N,
            X₂ = (ℓ.comp Pl).smulRight (fderiv ℝ φ (ψ x) v) := ⟨_, rfl⟩
        have h4 := hGE X₂ x (T x) (fderiv ℝ φ (ψ x)) X₂.differentiableAt hplane
        rw [X₂.fderiv, show X₂.comp (fderiv ℝ φ (ψ x)) = ℓ.smulRight (fderiv ℝ φ (ψ x) v) from
          ContinuousLinearMap.ext fun w ↦ by
            rw [hX₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
              ContinuousLinearMap.comp_apply, hPl, ContinuousLinearMap.smulRight_apply]] at h4
        have e3 := h4.unique hK2
        have e4 : Varifold.tangentialDivergence X₂ x (T x) = ℓ v := by
          rw [hTD, X₂.fderiv, show
              (T x).projectionLinearMap ∘ₗ (X₂ : Euclidean N →ₗ[ℝ] Euclidean N) =
              ((ℓ.comp Pl : Euclidean N →L[ℝ] ℝ) : Euclidean N →ₗ[ℝ] ℝ).smulRight
                ((T x).projectionLinearMap (fderiv ℝ φ (ψ x) v)) from
            LinearMap.ext fun w ↦ by rw [hX₂]; exact map_smul (T x).projectionLinearMap _ _,
            LinearMap.trace_smulRight, (T x).projectionLinearMap_apply_of_mem
              (hplane ▸ LinearMap.mem_range_self _ v)]
          show ℓ (Pl (fderiv ℝ φ (ψ x) v)) = ℓ v
          rw [hPl]
        rw [one_div, inv_mul_eq_div, eq_div_iff (hJpos _ hu).ne', e1, ← e3, e4, mul_comm (ℓ v),
          sub_add_cancel]
      have h0 : ∫ z, Varifold.tangentialDivergence Xf z.1 z.2 ∂V.measure = 0 := hV X
      rw [hVT, integral_map hgm.aemeasurable
        (Varifold.continuous_tangentialDivergence hXc).aestronglyMeasurable,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball x₀ (ρ / 2)) (fun x hx ↦ by
          simp only [hTD, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hXs h)),
            ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, map_zero]),
        setIntegral_congr_ae measurableSet_ball (Eventually.mono (inter_mem hMU μ.support_mem_ae)
          fun x hx hxB ↦ hdiv x hxB hx.1.1 hx.2)] at h0
      rw [hϑ, integral_map (f := fun u ↦ (1 / NJ (fderiv ℝ φ u)) * fderiv ℝ ζ u v) hψm
        ((measurable_const.div hJm).mul ((hζ.continuous_fderiv
          one_ne_zero).clm_apply continuous_const).measurable).aestronglyMeasurable]
      exact h0
    obtain ⟨c, hc⟩ := @G4w ϑ ⟨hϑfin⟩ (fun u ↦ NJ (fderiv ℝ φ u)) a (R / 2) _ (half_pos hR) hm hJm
        hϑm hG4h
    -- the chart ball `ball a r` and the matching open set `O`
    have hR2 : 0 < R / 2 := half_pos hR
    have hR4 : 0 < R / 2 / 2 := half_pos hR2
    have hR8' : 0 < R / 2 / 2 / 2 := half_pos hR4
    have hR8 : 0 < R / 2 / 2 / 2 / 2 := half_pos hR8'
    have hrR : closedBall a (R / 2 / 2 / 2 / 2) ⊆ ball a R := closedBall_subset_ball
      ((half_lt_self hR8').trans ((half_lt_self hR4).trans ((half_lt_self hR2).trans
        (half_lt_self hR))))
    have hBD : ∀ w ∈ ball a (R / 2 / 2 / 2 / 2), w ∈ D ∧ φ w ∈ ball x₀ (ρ / 2) := fun w hw ↦
      ⟨(hRD (hrR (ball_subset_closedBall hw))).1,
        ball_subset_ball ((half_le_self (half_pos hρ2).le).trans (half_le_self hρ2.le))
          (hRD (hrR (ball_subset_closedBall hw))).2⟩
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Euclidean N),
        O = ball x₀ (ρ / 2) ∩ ψ ⁻¹' ball a (R / 2 / 2 / 2 / 2) := ⟨_, rfl⟩
    have hOB : O ⊆ ball x₀ (ρ / 2) := hOdef ▸ inter_subset_left
    have hOo : IsOpen O := hOdef ▸ hψB.isOpen_inter_preimage isOpen_ball isOpen_ball
    have hψO : ContinuousOn ψ O := hψB.mono hOB
    have hMO : φ '' ball a (R / 2 / 2 / 2 / 2) = M ∩ O := by
      rw [hOdef]; ext y; constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨hwD, hwB⟩ := hBD w hw
        exact ⟨hφM w hwD, hwB, by rw [mem_preimage, hψφ w hwD (hT₀B hwB)]; exact hw⟩
      · rintro ⟨hyM, hyB, hyr⟩
        exact ⟨ψ y, hyr, hψM y ⟨hyM, hT₀B hyB⟩⟩
    have hMOm : MeasurableSet (M ∩ O) := by
      have hgc : ContinuousOn (fun y ↦ φ (ψ y) - y) O :=
        ((hφc2.continuousOn.comp hψB fun y hy ↦ hψK y (ball_subset_closedBall hy)).sub
          continuousOn_id).mono hOB
      have e : M ∩ O = O \ (O ∩ (fun y ↦ φ (ψ y) - y) ⁻¹' {0}ᶜ) := by
        ext y; constructor
        · rintro ⟨hyM, hyO⟩
          exact ⟨hyO, fun h ↦ h.2 (sub_eq_zero.mpr (hψM y ⟨hyM, hT₀B (hOB hyO)⟩))⟩
        · rintro ⟨hyO, hy⟩
          refine ⟨?_, hyO⟩
          have e' : φ (ψ y) = y := by_contra fun h ↦ hy ⟨hyO, sub_ne_zero.mpr h⟩
          rw [← e']; exact hφM _ (hψD (hT₀B (hOB hyO)))
      rw [e]
      exact hOo.measurableSet.diff
          (hgc.isOpen_inter_preimage hOo isOpen_compl_singleton).measurableSet
    -- a Lipschitz bound for `φ` on the chart ball
    obtain ⟨C, hC⟩ := (isCompact_closedBall a (R / 2 / 2 / 2 / 2)).exists_bound_of_continuousOn
      (hDφ.continuousOn.mono fun w hw ↦ (hRD (hrR hw)).1)
    have hK : LipschitzOnWith (Real.toNNReal C) φ (ball a (R / 2 / 2 / 2 / 2)) :=
      (convex_ball a _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun w hw ↦
        ((hφc2.contDiffAt (hDo.mem_nhds (hBD w hw).1)).differentiableAt
            two_ne_zero).hasFDerivAt.hasFDerivWithinAt)
        fun w hw ↦ by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
          exact le_max_of_le_left (hC w (ball_subset_closedBall hw))
    have h5 := G5 φ ψ a (R / 2 / 2 / 2 / 2) _
        (fun u hu ↦ (hφc2.contDiffAt (hDo.mem_nhds (hBD u hu).1)).of_le
      one_le_two) (fun u hu ↦ hφ.injective_fderiv (hBD u hu).1)
      (fun u hu ↦ hψφ u (hBD u hu).1 (hT₀B (hBD u hu).2)) hK (hMO ▸ hMOm)
      (hMO ▸ hψO.mono inter_subset_right)
    rw [hMO] at h5
    -- the pushforwards to the chart agree
    have hpush : (μ.restrict O).map ψ =
        ENNReal.ofReal c • ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ O)).map ψ := by
      rw [h5, ← hc, hϑ, Measure.restrict_map_of_aemeasurable hψm measurableSet_ball,
        Measure.restrict_restrict' measurableSet_ball, hOdef, inter_comm]
    have hφB : AEMeasurable φ ((volume.restrict (ball a (R / 2 / 2 / 2 / 2))).withDensity
        fun u ↦ ENNReal.ofReal (NJ (fderiv ℝ φ u))) :=
      ((hφc2.continuousOn.mono fun w hw ↦ (hBD w hw).1).aemeasurable measurableSet_ball).mono_ac
        (withDensity_absolutelyContinuous _ _)
    have hpull : ∀ ϖ : Measure (Euclidean N), ϖ (M ∩ O)ᶜ = 0 → AEMeasurable ψ ϖ →
        AEMeasurable φ (ϖ.map ψ) → (ϖ.map ψ).map φ = ϖ := by
      intro ϖ h0 hψ' hφ'
      rw [AEMeasurable.map_map_of_aemeasurable hφ' hψ', Measure.map_congr (g := id) ?_,
        Measure.map_id]
      filter_upwards [mem_ae_iff.mpr h0] with y hy
      exact hψM y ⟨hy.1, hT₀B (hOB hy.2)⟩
    have e1 := hpull (μ.restrict O) (by
        rw [Measure.restrict_apply' hOo.measurableSet]
        refine measure_mono_null (fun y hy ↦ ?_) hμM
        exact fun h ↦ hy.1 ⟨h.1, hy.2⟩)
      (hψO.aemeasurable hOo.measurableSet) (by rw [hpush, h5]; exact hφB.smul_measure _)
    have e2 := hpull ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ O)) (by
        rw [Measure.restrict_apply' hMOm, compl_inter_self, measure_empty])
      ((hψO.mono inter_subset_right).aemeasurable hMOm) (by rw [h5]; exact hφB)
    refine ⟨O, hOo, ?_, fun y hy ↦ (hK₀ (ball_subset_closedBall (hOB hy))).2,
      ENNReal.ofReal c, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
    · rw [hOdef]
      exact ⟨mem_ball_self hρ2, by rw [mem_preimage, hψa]; exact mem_ball_self hR8⟩
    · rw [← e1, hpush, Measure.map_smul _ (by rw [h5]; exact hφB), e2]
    · rw [← hMO]
      refine ne_top_of_le_ne_top ?_
          (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hK)
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_ball_lt_top.ne
    · intro O' hO' hxO'
      obtain ⟨s', hs', hsB⟩ : ∃ s' > 0, ball a s' ⊆ ball a (R / 2 / 2 / 2 / 2) ∩ φ ⁻¹' O' :=
        Metric.mem_nhds_iff.mp (inter_mem (ball_mem_nhds a hR8)
          ((hφc2.continuousOn.continuousAt (hDo.mem_nhds ha)).preimage_mem_nhds
            (hO'.mem_nhds (by rw [hφa]; exact hxO'))))
      refine lt_of_lt_of_le ?_ (measure_mono (s := ψ ⁻¹' ball a s' ∩ (M ∩ O)) ?_)
      · rw [← Measure.restrict_apply' hMOm, ← Measure.map_apply_of_aemeasurable
          ((hψO.mono inter_subset_right).aemeasurable hMOm) measurableSet_ball, h5,
          withDensity_apply _ measurableSet_ball, setLIntegral_pos_iff hJm.ennreal_ofReal,
          Measure.restrict_apply' measurableSet_ball]
        refine lt_of_lt_of_le (measure_ball_pos volume a hs') (measure_mono fun u hu ↦ ?_)
        exact ⟨⟨(ENNReal.ofReal_pos.mpr (hJpos u (hBD u (hsB hu).1).1)).ne', hu⟩, (hsB hu).1⟩
      · rintro y ⟨hys, hyM, hyO⟩
        refine ⟨⟨hyM, ?_⟩, hyO⟩
        rw [← hψM y ⟨hyM, hT₀B (hOB hyO)⟩]
        exact (hsB hys).2
  -- gluing: one constant on `M ∩ U`
  have hglue : ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U) := by
    choose! O hO hxO hOU c hc hμO hfinO hposO using hLC
    have hcc : ∀ x ∈ M ∩ U, ∀ y ∈ M ∩ U, y ∈ O x → c y = c x := by
      intro x hx y hy hyx
      have h1 : μ (O x ∩ O y) = c y * μHE[n] (O x ∩ (M ∩ O y)) := by
        rw [← Measure.restrict_apply (hO x hx).measurableSet, hμO y hy, Measure.smul_apply,
          Measure.restrict_apply (hO x hx).measurableSet, smul_eq_mul]
      have h2 : μ (O y ∩ O x) = c x * μHE[n] (O y ∩ (M ∩ O x)) := by
        rw [← Measure.restrict_apply (hO y hy).measurableSet, hμO x hx, Measure.smul_apply,
          Measure.restrict_apply (hO y hy).measurableSet, smul_eq_mul]
      rw [inter_comm (O y) (O x), show O y ∩ (M ∩ O x) = O x ∩ (M ∩ O y) from
        Set.ext fun _ ↦ ⟨fun h ↦ ⟨h.2.2, h.2.1, h.1⟩, fun h ↦ ⟨h.2.2, h.2.1, h.1⟩⟩] at h2
      have hpos : μHE[n] (O x ∩ (M ∩ O y)) ≠ 0 := by
        refine ((hposO y hy (O x) (hO x hx) hyx).trans_le (measure_mono ?_)).ne'
        exact fun _ h ↦ ⟨h.1.2, h.1.1, h.2⟩
      exact (ENNReal.mul_left_inj hpos (ne_top_of_le_ne_top (hfinO y hy)
        (measure_mono inter_subset_right))).mp (h1.symm.trans h2)
    by_cases hne' : (M ∩ U).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne'
      have hall : ∀ y ∈ M ∩ U, c y = c x₀ := by
        have hsplit := isPreconnected_iff_subset_of_disjoint.mp hconn
          (⋃ x ∈ {x | x ∈ M ∩ U ∧ c x = c x₀}, O x) (⋃ x ∈ {x | x ∈ M ∩ U ∧ c x ≠ c x₀}, O x)
          (isOpen_biUnion fun x hx ↦ hO x hx.1) (isOpen_biUnion fun x hx ↦ hO x hx.1)
          (fun y hy ↦ by
            by_cases h : c y = c x₀
            · exact Or.inl (mem_biUnion (x := y) ⟨hy, h⟩ (hxO y hy))
            · exact Or.inr (mem_biUnion (x := y) ⟨hy, h⟩ (hxO y hy)))
          (by
            refine eq_empty_iff_forall_notMem.mpr fun y ⟨hy, h₁, h₂⟩ ↦ ?_
            obtain ⟨x, ⟨hx, hcx⟩, hyx⟩ := mem_iUnion₂.mp h₁
            obtain ⟨x', ⟨hx', hcx'⟩, hyx'⟩ := mem_iUnion₂.mp h₂
            exact hcx' ((hcc x' hx' y hy hyx').symm.trans ((hcc x hx y hy hyx).trans hcx)))
        intro y hy
        rcases hsplit with h | h
        · obtain ⟨x, ⟨hx, hcx⟩, hyx⟩ := mem_iUnion₂.mp (h hy)
          exact (hcc x hx y hy hyx).trans hcx
        · obtain ⟨x, ⟨hx, hcx⟩, hx₀x⟩ := mem_iUnion₂.mp (h hx₀)
          exact absurd (hcc x hx x₀ hx₀ hx₀x).symm hcx
      obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable
        (fun x : ↥(M ∩ U) ↦ O x) (fun x ↦ hO x x.2)
      have hcov : M ∩ U ⊆ ⋃ x ∈ S, O x := by
        intro y hy
        rw [hSU]
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxO y hy⟩
      have : Countable S := hSc.to_subtype
      have hres : μ.restrict (⋃ x : S, O x) =
          (c x₀ • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).restrict (⋃ x : S, O x) := by
        refine Measure.restrict_iUnion_congr.mpr fun x ↦ ?_
        rw [hμO x x.1.2, hall x x.1.2, Measure.restrict_smul,
          Measure.restrict_restrict (hO x x.1.2).measurableSet]
        congr 2
        ext y
        exact ⟨fun h ↦ ⟨h.2, h.1, hOU x x.1.2 h.2⟩, fun h ↦ ⟨h.2.1, h.1⟩⟩
      have hcov' : M ∩ U ⊆ ⋃ x : S, O x := fun y hy ↦ by
        obtain ⟨x, hxS, hyx⟩ := mem_iUnion₂.mp (hcov hy)
        exact mem_iUnion.mpr ⟨⟨x, hxS⟩, hyx⟩
      have hUo : MeasurableSet (⋃ x : S, O x) := (isOpen_iUnion fun x ↦ hO _ x.1.2).measurableSet
      have h1 : μ.restrict (⋃ x : S, O x) = μ :=
        Measure.restrict_eq_self_of_ae_mem (mem_of_superset (mem_ae_iff.mpr hμM) hcov')
      rw [h1, Measure.restrict_smul, Measure.restrict_restrict hUo, inter_eq_right.mpr hcov']
          at hres
      exact ⟨c x₀, hc x₀ hx₀, hres⟩
    · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
      rw [zero_smul]
      have h0 : M ∩ U = ∅ := not_nonempty_iff_eq_empty.mp hne'
      rw [h0, compl_empty] at hμM
      exact Measure.measure_univ_eq_zero.mp hμM
  -- assembly
  obtain ⟨c, hc, hμc⟩ := hglue
  refine ⟨c, T, hc, hTm, by rw [hVT, hμc], fun hc0 x hx ↦ ?_⟩
  have hxs : x ∈ μ.support := by
    rw [Measure.mem_support_iff_forall]
    intro O' hO'
    obtain ⟨O'', hO''O', hO''o, hxO''⟩ := _root_.mem_nhds_iff.mp hO'
    obtain ⟨O, -, -, hOU, -, -, -, -, hposO⟩ := hLC x hx
    refine lt_of_lt_of_le ?_ (measure_mono hO''O')
    rw [hμc, Measure.smul_apply, Measure.restrict_apply hO''o.measurableSet, smul_eq_mul]
    exact ENNReal.mul_pos hc0 ((hposO O'' hO''o hxO'').trans_le
      (measure_mono (s := M ∩ O'' ∩ O) (t := O'' ∩ (M ∩ U))
        fun y hy ↦ ⟨hy.1.2, hy.1.1, hOU hy.2⟩)).ne'
  obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx.1
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hx.1⟩
  rw [Submission.simon_chart_classicalTangentSpace_eq_range N n M W D φ a hφ ha,
    hP1 (φ a, T (φ a)) (hTspt (φ a) ⟨hx.2, hxs⟩) hx.2 D W φ hφ a ha rfl]
  exact LinearMap.coe_range _
/-- **Simon Ch. 8, 5.2, the cylinder cut-off** (child `cylinder_cutoff` of `limit_ball_mass`):
for `a < b` one `F ∈ C_c(ℝ^N × G(N,n), ℝ)`, chosen before the measure, satisfies
`ν(B_a(0) × G(N,n)) ≤ ∫ F dν ≤ ν(B_b(0) × G(N,n))` for every `ν` with `ν(B_b(0) × G(N,n)) < ∞`.
Take the ramp `F(y, S) = min 1 (max 0 ((b - |y|) / (b - a)))`: it is continuous, `0 ≤ F ≤ 1`,
`F = 1` on `B_a(0) × G(N,n)` and `F = 0` off the compact `B_b(0) × G(N,n)`.  Then
`|F| ≤ 1_{B_b(0) × G(N,n)}` gives integrability, so `ofReal (∫ F dν) = ∫⁻ ofReal ∘ F dν`, and
`1_{B_a(0) × G(N,n)} ≤ ofReal ∘ F ≤ 1_{B_b(0) × G(N,n)}` gives both bounds. -/
theorem Submission.varifold_tangents_lbm_exists_cylinder_cutoff :
    ∀ (N n : ℕ) (a b : ℝ), a < b → ∃ F : C_c(Euclidean N × Grassmannian N n, ℝ), ∀ ν : Measure (Euclidean N × Grassmannian N n), ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → ν (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ ENNReal.ofReal (∫ z, F z ∂ν) ∧ ENNReal.ofReal (∫ z, F z ∂ν) ≤ ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n a b hab
  have hd : 0 < b - a := sub_pos.2 hab
  set Ka := closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))
  set Kb := closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)) with hKb
  -- The ramp `h(y, S) = min 1 (max 0 ((b - ‖y‖) / (b - a)))`: `0 ≤ h ≤ 1`, `h = 1` on `Ka`,
  -- `h = 0` off `Kb`.
  set h : Euclidean N × Grassmannian N n → ℝ := fun z ↦ min 1 (max 0 ((b - ‖z.1‖) / (b - a)))
  have hcont : Continuous h :=
    continuous_const.min (continuous_const.max
      ((continuous_const.sub (continuous_norm.comp continuous_fst)).div_const _))
  have h_nonneg : ∀ z, 0 ≤ h z := fun z ↦ le_min zero_le_one (le_max_left _ _)
  have h_le_one : ∀ z, h z ≤ 1 := fun z ↦ min_le_left _ _
  have h_one : ∀ z ∈ Ka, h z = 1 := by
    rintro ⟨y, S⟩ ⟨hy, -⟩
    rw [mem_closedBall, dist_zero_right] at hy
    have h1 : 1 ≤ (b - ‖y‖) / (b - a) := by
      rw [le_div_iff₀ hd]
      linarith
    show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 1
    rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  have h_zero : ∀ z ∉ Kb, h z = 0 := by
    rintro ⟨y, S⟩ hz
    have hy : b < ‖y‖ := by
      simpa [hKb, mem_prod, mem_closedBall, dist_zero_right] using hz
    have h0 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 0
    rw [max_eq_left h0, min_eq_right zero_le_one]
  -- `Kb` is compact (`ℝ^N` is proper and `G(N,n)` is compact), so `h ∈ C_c`.
  have hKb_cpt : IsCompact Kb := (isCompact_closedBall 0 b).prod isCompact_univ
  refine ⟨⟨⟨h, hcont⟩, HasCompactSupport.intro hKb_cpt h_zero⟩, fun ν hν ↦ ?_⟩
  have hFz : ∀ z, (⟨⟨h, hcont⟩, HasCompactSupport.intro hKb_cpt h_zero⟩ :
      C_c(Euclidean N × Grassmannian N n, ℝ)) z = h z := fun z ↦ rfl
  simp only [hFz]
  have hmeasA : MeasurableSet Ka := measurableSet_closedBall.prod MeasurableSet.univ
  have hmeasB : MeasurableSet Kb := measurableSet_closedBall.prod MeasurableSet.univ
  -- `|h| ≤ 1_{Kb}` and `ν(Kb) < ∞`, so `h` is `ν`-integrable.
  have hint : Integrable h ν := by
    refine Integrable.mono' ((integrable_indicator_iff hmeasB).2
      (integrableOn_const (C := (1 : ℝ)) hν)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ Kb
    · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (h_nonneg z)]
      exact h_le_one z
    · rw [indicator_of_notMem hz, h_zero z hz, norm_zero]
  -- `ofReal (∫ h dν) = ∫⁻ ofReal ∘ h dν`, and `1_{Ka} ≤ ofReal ∘ h ≤ 1_{Kb}` pointwise.
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall h_nonneg)]
  constructor
  · calc ν Ka = ∫⁻ z, Ka.indicator 1 z ∂ν := (lintegral_indicator_one hmeasA).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂ν := lintegral_mono fun z ↦ by
        by_cases hz : z ∈ Ka
        · rw [indicator_of_mem hz, Pi.one_apply, h_one z hz, ENNReal.ofReal_one]
        · rw [indicator_of_notMem hz]
          exact zero_le
  · calc ∫⁻ z, ENNReal.ofReal (h z) ∂ν ≤ ∫⁻ z, Kb.indicator 1 z ∂ν := lintegral_mono fun z ↦ by
          by_cases hz : z ∈ Kb
          · rw [indicator_of_mem hz, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (h_le_one z)
          · rw [indicator_of_notMem hz, h_zero z hz, ENNReal.ofReal_zero]
      _ = ν Kb := lintegral_indicator_one hmeasB

/-- **Simon Ch. 8, 5.2, vague-limit cylinder bounds** (child `vague_cylinder_bounds` of
`limit_ball_mass`): if `μs j → μ` vaguely, `a < b`, `μ(B_b(0) × G(N,n)) < ∞`,
`μs j (B_a(0) × G(N,n)) → La` and `μs j (B_b(0) × G(N,n)) → Lb < ∞`, then
`μ(B_a(0) × G(N,n)) ≤ Lb` and `La ≤ μ(B_b(0) × G(N,n))`.
Take the cut-off `F` of `varifold_tangents_lbm_exists_cylinder_cutoff` for `a < b`: it puts
`ofReal (∫ F dμ)` between `μ(B_a(0) × G(N,n))` and `μ(B_b(0) × G(N,n))`, and, as `Lb < ∞`,
eventually puts `ofReal (∫ F dμs j)` between `μs j (B_a(0) × G(N,n))` and `μs j (B_b(0) × G(N,n))`.
Vague convergence gives `ofReal (∫ F dμs j) → ofReal (∫ F dμ)`, so passing to the limit gives
`ofReal (∫ F dμ) ≤ Lb` and `La ≤ ofReal (∫ F dμ)`. -/
theorem Submission.varifold_tangents_lbm_vague_cylinder_bounds :
    ∀ (N n : ℕ) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (a b : ℝ) (La Lb : ℝ≥0∞), VagueConverges μs μ → a < b → μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 La) → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 Lb) → Lb ≠ ∞ → μ (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ Lb ∧ La ≤ μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n μs μ a b La Lb hconv hab hμb hLa hLb hLb_ne
  obtain ⟨F, hF⟩ := Submission.varifold_tangents_lbm_exists_cylinder_cutoff N n a b hab
  -- The cut-off bounds `ofReal (∫ F dμ)`, and, since `μs j (B_b(0) × G(N,n)) → Lb ≠ ∞`, eventually
  -- also `ofReal (∫ F dμs j)`.
  obtain ⟨hμa, hμF⟩ := hF μ hμb
  have hev := (hLb.eventually_ne hLb_ne).mono fun j hj ↦ hF (μs j) hj
  -- Vague convergence at `F`, composed with the continuous `ENNReal.ofReal`.
  have hFlim := ENNReal.tendsto_ofReal (hconv F)
  exact ⟨hμa.trans (le_of_tendsto_of_tendsto hFlim hLb (hev.mono fun j hj ↦ hj.2)),
    (le_of_tendsto_of_tendsto hLa hFlim (hev.mono fun j hj ↦ hj.1)).trans hμF⟩
/-- **Simon Ch. 8, 5.1–5.2, the ball-mass computation** (child `rescaled_ball_mass` of
`varifold_tangents`): if `Θ^n(μ_V, x) = θ`, then `V_{x,t}(B_R(0) × G(N,n)) → θ ω_n R^n` as `t ↓ 0`.
For `t > 0` the preimage of `B_R(0) × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is
`B_{tR}(x) × G(N,n)`, so `V_{x,t}(B_R(0) × G(N,n)) = t^{-n} μ_V(B_{tR}(x))`, which equals
`densityRatio n μ_V x (tR) · ω_n R^n` because `0 < ω_n < ∞`; then compose `HasDensity` with
`t ↦ tR` (as in SimonGMT's `Varifold.tendsto_blowUpWeight_closedBall_of_density`). -/
theorem Submission.varifold_tangents_rescaled_ball_mass_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ : ℝ≥0∞) (R : ℝ), HasDensity n V.weight x θ → 0 < R → Tendsto (fun t : ℝ ↦ rescaledMeasure V x t (closedBall (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)))) (𝓝[>] 0) (𝓝 (θ * unitBallVolume n * ENNReal.ofReal R ^ n)) := by
  intro N n U V x θ R hθ hR
  have hθ' : Tendsto (densityRatio n V.weight x) (𝓝[>] 0) (𝓝 θ) := hθ
  -- `c = ω_n R^n` is a positive finite constant.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : unitBallVolume n * ENNReal.ofReal R ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne')
  have hctop : unitBallVolume n * ENNReal.ofReal R ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- `t ↦ tR` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have hs : Tendsto (fun t : ℝ ↦ t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [zero_mul, id_eq] using
        ((tendsto_id.mono_left inf_le_left : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0)).mul_const R)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hR
  rw [mul_assoc]
  refine (ENNReal.Tendsto.mul_const (hθ'.comp hs) (Or.inr hctop)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  -- `V_{x,t}(B_R(0) × G) = t^{-n} μ_V(B_{tR}(x))`.
  have hpre : (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) ⁻¹'
      (closedBall (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) =
      closedBall x (t * R) ×ˢ univ := by
    ext z
    simp only [mem_preimage, mem_prod, mem_closedBall, dist_eq_norm, sub_zero, mem_univ,
      and_true, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
    exact inv_mul_le_iff₀ ht
  have hmeas : Measurable (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) := by
    fun_prop
  rw [Function.comp_apply, densityRatio, rescaledMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hmeas (measurableSet_closedBall.prod MeasurableSet.univ), hpre,
    ← V.weight_apply measurableSet_closedBall]
  -- `μ / (ω (tR)^n) · (ω R^n) = t^{-n} μ`, cancelling the positive finite `ω R^n`.
  have ha0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne'
  have hatop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul ht.le, mul_pow, mul_left_comm (unitBallVolume n),
    ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
  calc (ENNReal.ofReal t ^ n)⁻¹ * (unitBallVolume n * ENNReal.ofReal R ^ n)⁻¹ *
        V.weight (closedBall x (t * R)) * (unitBallVolume n * ENNReal.ofReal R ^ n)
      = (ENNReal.ofReal t ^ n)⁻¹ * V.weight (closedBall x (t * R)) *
          ((unitBallVolume n * ENNReal.ofReal R ^ n)⁻¹ *
            (unitBallVolume n * ENNReal.ofReal R ^ n)) := by ring
    _ = (ENNReal.ofReal t ^ n)⁻¹ * V.weight (closedBall x (t * R)) := by
      rw [ENNReal.inv_mul_cancel hc0 hctop, mul_one]
/-- Densities transfer under ball-mass scaling (steps 6 and 9 of the blow-up density lower bound
used in Simon Ch. 8, 5.5 and 5.7): if `t > 0`, `c ≠ ∞` and `ν(B_ρ(y)) = c t^{-n} μ(B_{tρ}(z))` for
`0 < ρ < δ`, then `Θ^n(μ, z) = θ` implies `Θ^n(ν, y) = c θ`. -/
theorem Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling :
    ∀ (N n : ℕ) (μ ν : Measure (Euclidean N)) (y z : Euclidean N) (t δ : ℝ) (c θ : ℝ≥0∞), 0 < t → 0 < δ → c ≠ ∞ → (∀ ρ : ℝ, 0 < ρ → ρ < δ → ν (closedBall y ρ) = c * (ENNReal.ofReal (t⁻¹ ^ n) * μ (closedBall z (t * ρ)))) → HasDensity n μ z θ → HasDensity n ν y (c * θ) := by
  intro N n μ ν y z t δ c θ ht hδ hc hscale hμ
  -- Step 1: `ω_n = unitBallVolume n` lies in `(0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_ne_top
  -- Step 2: `ρ ↦ t ρ` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have hs : Tendsto (fun ρ : ℝ ↦ t * ρ) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul t).tendsto' 0 0 (mul_zero t)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun ρ hρ ↦ mul_pos ht hρ⟩
  -- Step 3: `c · densityRatio n μ z (t ρ) → c θ` as `ρ ↓ 0`, since `c ≠ ∞`.
  have hlim : Tendsto (fun ρ ↦ c * densityRatio n μ z (t * ρ)) (𝓝[>] 0) (𝓝 (c * θ)) :=
    ENNReal.Tendsto.const_mul (Tendsto.comp hμ hs) (Or.inr hc)
  -- Step 5: it suffices that the two quotients agree on `(0, δ) ∈ 𝓝[>] 0`.
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  -- Step 4: with `T = ofReal t ^ n ∈ (0, ∞)`, `ofReal (t⁻¹ ^ n) = T⁻¹` and
  -- `ofReal (t ρ) ^ n = T · ofReal ρ ^ n`; then distribute the inverses.
  have hT0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero n (ENNReal.ofReal_pos.2 ht).ne'
  have hTtop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [densityRatio, densityRatio, hscale ρ hρ.1 hρ.2, ENNReal.ofReal_mul ht.le, mul_pow,
    ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop),
    ENNReal.mul_inv (Or.inl hT0) (Or.inl hTtop), ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop)]
  ring
/-- **Masses of the rescaled varifold on cylinders and closed balls** (child `rescaled_mass_formula`
of `varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): for every real `t` and Borel
`A ⊆ ℝ^N`, `V_{x,t}(A × G(N,n)) = t^{-n} μ_V({z : t⁻¹(z - x) ∈ A})`, because the preimage of
`A × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is `{z : t⁻¹(z - x) ∈ A} × G(N,n)`; and for `t > 0`,
`V_{x,t}(B_ρ(y) × G(N,n)) = t^{-n} μ_V(B_{tρ}(x + ty))`, because
`t⁻¹(w - x) - y = t⁻¹(w - (x + ty))` gives `{w : t⁻¹(w - x) ∈ B_ρ(y)} = B_{tρ}(x + ty)`. -/
theorem Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t : ℝ), (∀ A : Set (Euclidean N), MeasurableSet A → rescaledMeasure V x t (A ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | t⁻¹ • (z - x) ∈ A}) ∧ (0 < t → ∀ (y : Euclidean N) (ρ : ℝ), rescaledMeasure V x t (closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall (x + t • y) (t * ρ))) := by
  intro N n U V x t
  -- Step 1: the dilation `z ↦ t⁻¹ • (z - x)` and `φ (z, S) = (t⁻¹ • (z - x), S)` are measurable.
  have hη : Measurable fun z : Euclidean N ↦ t⁻¹ • (z - x) := by fun_prop
  have hφ : Measurable fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2) := by
    fun_prop
  -- Step 2 (part (i)): `φ⁻¹(A × G) = {z | t⁻¹ • (z - x) ∈ A} × G`, a measurable cylinder.
  have hcyl : ∀ A : Set (Euclidean N), MeasurableSet A →
      rescaledMeasure V x t (A ×ˢ (univ : Set (Grassmannian N n))) =
        ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | t⁻¹ • (z - x) ∈ A} := by
    intro A hA
    have hA' : MeasurableSet {z : Euclidean N | t⁻¹ • (z - x) ∈ A} := hη hA
    rw [rescaledMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hφ (hA.prod MeasurableSet.univ), V.weight_apply hA']
    rfl
  refine ⟨hcyl, fun ht y ρ ↦ ?_⟩
  -- Step 3 (part (ii)): for `t > 0`, `{w | t⁻¹ • (w - x) ∈ B_ρ(y)} = B_{tρ}(x + t • y)`, since
  -- `t⁻¹ • (w - x) - y = t⁻¹ • (w - (x + t • y))` and `t⁻¹ * d ≤ ρ ↔ d ≤ t * ρ`.
  have hball : {z : Euclidean N | t⁻¹ • (z - x) ∈ closedBall y ρ} =
      closedBall (x + t • y) (t * ρ) := by
    ext w
    have hw : t⁻¹ • (w - x) - y = t⁻¹ • (w - (x + t • y)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rw [mem_ofPred_eq, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, hw, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht]
  rw [hcyl _ measurableSet_closedBall, hball]
/-- **Simon Ch. 8, proofs of 5.5 and 5.7, restricted varifolds** (child `restricted_varifold` of the
density lower bound for varifold tangents): the construction of `W_j = τ⁻¹ V_{x,λ_j} ⌞ Gₙ(Ω)` and
`C_Ω = τ⁻¹ C ⌞ Gₙ(Ω)`, for a general measure `μ`.  If `Ω` is open, `c < ∞` and `μ(K × G(N,n)) < ∞`
for every compact `K ⊆ Ω`, then `c • μ ⌞ (Ω × G(N,n))` vanishes on `Ωᶜ × G(N,n)` (disjoint from
`Ω × G(N,n)`) and is finite on `K × G(N,n)` for compact `K ⊆ Ω`, so it is a varifold on `Ω`. -/
theorem Submission.varifold_tangents_dlb_exists_restricted_varifold :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μ : Measure (Euclidean N × Grassmannian N n)) (c : ℝ≥0∞), IsOpen Ω → c ≠ ∞ → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ Ω → μ (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞) → ∃ W : Varifold N n Ω, W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n Ω μ c hΩ hc hμ
  -- Step 1: `W` has the four fields of `Varifold N n Ω`, with measure `c • μ ⌞ (Ω × G(N,n))`.
  refine ⟨⟨hΩ, c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))), ?_, ?_⟩, rfl⟩
  · -- Step 2: `(Ωᶜ × G) ∩ (Ω × G) = ∅`, and `Ωᶜ × G` is measurable since `Ω` is open.
    rw [Measure.smul_apply, Measure.restrict_apply (hΩ.measurableSet.compl.prod MeasurableSet.univ),
      prod_inter_prod, compl_inter_self, empty_prod, measure_empty, smul_zero]
  · -- Step 3: `c • μ ⌞ (Ω × G)(K × G) ≤ c · μ(K × G) < ∞` for compact `K ⊆ Ω`.
    intro K hK hKΩ
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top hc
      (ne_top_of_le_ne_top (hμ K hK hKΩ) (Measure.restrict_apply_le _ _))
/-- **Simon Ch. 8, proof of 5.5, step 5** (child `first_variation_control` of
`density_lower_bound`): if `W = c · μ ⌞ Gₙ(Ω)` with `c < ∞` and `|∫ div_S X dμ| ≤ β < ∞` for every
`C¹` field `X` with `|X| ≤ 1` and compact support in `Ω`, then `W` has locally bounded first
variation and `‖δW‖(O) ≤ c β` for every open `O ⊂⊂ Ω`.  On test fields `div_S X` vanishes off
`Gₙ(Ω)`, so `δW(X) = c ∫ div_S X dμ`; every term of the supremum (8.2.5) is then at most `c β`, and
on `O ⊂⊂ Ω` that supremum is `‖δW‖(O)` (`firstVariationRieszMeasure_eq_norm`). -/
theorem Submission.varifold_tangents_dlb_restricted_firstVariation_control :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μ : Measure (Euclidean N × Grassmannian N n)) (W : Varifold N n Ω) (c β : ℝ≥0∞), c ≠ ∞ → β ≠ ∞ → W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → (∀ X : Euclidean N → Euclidean N, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ Ω → (∀ y, ‖X y‖ ≤ 1) → ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂μ| ≤ β) → W.HasLocallyBoundedFirstVariation ∧ ∀ O : Set (Euclidean N), IsRelCompactOpenIn O Ω → variationMeasure W O ≤ c * β := by
  intro N n Ω μ W c β hc hβ hW hdiv
  -- Step 1: for a test field `X` on `Ω`, `δW(X) = c ∫ div_S X dμ`, since `div_S X` vanishes off
  -- `tsupport X × G(N,n) ⊆ Ω × G(N,n)`.
  have hfv : ∀ X : Varifold.TestVectorField Ω,
      W.firstVariation X = c.toReal * ∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂μ := by
    intro X
    rw [Varifold.firstVariation, hW, integral_smul_measure, smul_eq_mul,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    by_contra hne
    exact hz ⟨X.support_subset (Varifold.support_tangentialDivergence_subset X hne).1, mem_univ _⟩
  -- Step 2: every term of the supremum (8.2.5) defining `firstVariationNormOn O` is at most `c β`.
  have hnorm : ∀ O : Set (Euclidean N), W.firstVariationNormOn O ≤ c * β := by
    intro O
    rw [Varifold.firstVariationNormOn]
    refine iSup_le fun X ↦ ?_
    split_ifs with hXO
    · rw [hfv X, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
      gcongr
      exact hdiv X X.contDiff X.compactSupport X.support_subset hXO.2
    · exact zero_le
  -- Step 3: `c β < ∞`, so `W` has locally bounded first variation.
  have hW' : W.HasLocallyBoundedFirstVariation := fun O _ _ ↦
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hβ) (hnorm O)
  -- Step 4: for open `O ⊂⊂ Ω`, `‖δW‖(O)` is the supremum (8.2.5), hence at most `c β`.
  refine ⟨hW', fun O hO ↦ ?_⟩
  rw [variationMeasure, dite_eq_left hW', W.firstVariationRieszMeasure_eq_norm hW' O hO.1 hO.2]
  exact hnorm O

/-- Bad-set mass in the restricted blow-up (step 7 of the parent `density_lower_bound` proof, Simon
Ch. 8, 5.5 and 5.7, for one scale `t`): if `W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and
`O ⊆ B°_R(0)`, then `μ_W({y : x + t y ∈ E} ∩ O) ≤ c R^n μ_V(B_{tR}(x) ∩ E) / (tR)^n`, the
measures being applied to arbitrary sets as outer measures. -/
theorem Submission.varifold_tangents_dlb_restricted_bad_set_weight_le :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R : ℝ) (c : ℝ≥0∞) (W : Varifold N n (ball (0 : Euclidean N) R)) (E O : Set (Euclidean N)), 0 < t → 0 < R → W.measure = c • (rescaledMeasure V x t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) → O ⊆ ball (0 : Euclidean N) R → W.weight ({y | x + t • y ∈ E} ∩ O) ≤ c * (ENNReal.ofReal R ^ n * (V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} / ENNReal.ofReal (t * R) ^ n)) := by
  intro N n U V x t R c W E O ht hR hW hO
  -- Step 1: a Borel hull `Eh` of `E' = B_{tR}(x) ∩ E` with `μ_V(Eh) = μ_V(E')`, and the Borel set
  -- `A = {y : x + t y ∈ Eh}`.
  obtain ⟨Eh, hEEh, hEhm, hμEh⟩ : ∃ Eh : Set (Euclidean N),
      {z | z ∈ closedBall x (t * R) ∧ z ∈ E} ⊆ Eh ∧ MeasurableSet Eh ∧
        V.weight Eh = V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} :=
    ⟨_, subset_toMeasurable _ _, measurableSet_toMeasurable _ _, measure_toMeasurable _⟩
  have hAm : MeasurableSet {y : Euclidean N | x + t • y ∈ Eh} :=
    hEhm.preimage (measurable_const.add (measurable_id.const_smul t))
  -- Step 2: `{y : x + t y ∈ E} ∩ O ⊆ A`, since `|y| < R` gives `x + t y ∈ B_{tR}(x)`.
  have hsub : {y | x + t • y ∈ E} ∩ O ⊆ {y | x + t • y ∈ Eh} := by
    rintro y ⟨hyE, hyO⟩
    refine hEEh ⟨?_, hyE⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 (hO hyO)).le ht.le
  -- Step 4: `{z : t⁻¹ (z - x) ∈ A} = Eh`, as `x + t (t⁻¹ (z - x)) = z`.
  have hpre : {z | t⁻¹ • (z - x) ∈ {y | x + t • y ∈ Eh}} = Eh := by
    ext z
    simp only [mem_ofPred_eq, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
  -- Step 5: `ofReal(t⁻¹ⁿ) M = Rⁿ (M / (tR)ⁿ)`, with `T = tⁿ` and `Q = Rⁿ` in `(0, ∞)`.
  have harith : ∀ M : ℝ≥0∞, ENNReal.ofReal (t⁻¹ ^ n) * M =
      ENNReal.ofReal R ^ n * (M / ENNReal.ofReal (t * R) ^ n) := by
    intro M
    have hT0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne'
    have hTtop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hQ0 : ENNReal.ofReal R ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne'
    have hQtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
      ENNReal.ofReal_mul ht.le, mul_pow, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl hT0) (Or.inl hTtop)]
    calc (ENNReal.ofReal t ^ n)⁻¹ * M
        = (ENNReal.ofReal t ^ n)⁻¹ * M * (ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹) := by
          rw [ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
      _ = ENNReal.ofReal R ^ n * ((ENNReal.ofReal t ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * M) := by
          ring
  -- Steps 3, 4 and 6: monotonicity, `restrict ≤ self`, and the sibling rescaled mass formula.
  calc W.weight ({y | x + t • y ∈ E} ∩ O)
      ≤ W.weight {y | x + t • y ∈ Eh} := measure_mono hsub
    _ = W.measure ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := W.weight_apply hAm
    _ = c * (rescaledMeasure V x t).restrict
          (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)))
          ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := by
        rw [hW, Measure.smul_apply, smul_eq_mul]
    _ ≤ c * rescaledMeasure V x t ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := by
        gcongr
        exact Measure.restrict_le_self
    _ = c * (ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E}) := by
        rw [(Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ N n U V x t).1 _ hAm,
          hpre, hμEh]
    _ = c * (ENNReal.ofReal R ^ n *
          (V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} / ENNReal.ofReal (t * R) ^ n)) := by
        rw [harith]

/-- **Densities of the restricted blow-up** (child `restricted_density` of
`varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): if `t > 0`, `c ≠ ∞`,
`W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and `Θ^n(μ_V, x + ty) = θ` at a point `y ∈ B°_R(0)`, then
`Θ^n(μ_W, y) = cθ`.  For `0 < ρ < R - |y|` the closed ball `B_ρ(y)` lies in `B°_R(0)`, so the
restriction does not cut it and `μ_W(B_ρ(y)) = c t^{-n} μ_V(B_{tρ}(x + ty))` by the rescaled mass
formula; the scaling lemma for densities (with centre `z = x + ty`) then gives the density. -/
theorem Submission.varifold_tangents_dlb_restricted_hasDensity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R : ℝ) (c θ : ℝ≥0∞) (W : Varifold N n (ball (0 : Euclidean N) R)) (y : Euclidean N), 0 < t → c ≠ ∞ → W.measure = c • (rescaledMeasure V x t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) → y ∈ ball (0 : Euclidean N) R → HasDensity n V.weight (x + t • y) θ → HasDensity n W.weight y (c * θ) := by
  intro N n U V x t R c θ W y ht hc hW hy hθ
  -- Step 1: `δ := R - ‖y‖ > 0`, because `y ∈ B°_R(0)`.
  have hδ : 0 < R - ‖y‖ := sub_pos.2 (mem_ball_zero_iff.1 hy)
  -- Step 4: the scaling lemma with `z = x + t • y`; its ball-mass hypothesis is steps 2–3.
  refine Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling N n V.weight W.weight
    y (x + t • y) t (R - ‖y‖) c θ ht hδ hc (fun ρ _ hρδ ↦ ?_) hθ
  -- Step 2: for `ρ < δ`, `B_ρ(y) ⊆ B°_R(0)`, since `‖w‖ ≤ ‖w - y‖ + ‖y‖ ≤ ρ + ‖y‖ < R`.
  have hsub : closedBall y ρ ⊆ ball (0 : Euclidean N) R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
      _ < R := by linarith
  -- Step 3: `μ_W(B_ρ(y)) = c V_{x,t}((B_ρ(y) × G) ∩ (B°_R(0) × G)) = c V_{x,t}(B_ρ(y) × G)`,
  -- which is `c (t^{-n} μ_V(B_{tρ}(x + t • y)))` by part (ii) of the rescaled mass formula.
  rw [W.weight_apply measurableSet_closedBall, hW, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_closedBall.prod MeasurableSet.univ),
    Set.inter_eq_left.2 (Set.prod_mono hsub subset_rfl),
    (Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ N n U V x t).2 ht y ρ]

/-- **Simon Ch. 8, step 9 of the use of 3.7 in 5.5 and 5.7** (child `density_pullback` of
`density_lower_bound`): if `μ_W = c μ_V ⌞ Ω` with `0 < c < ∞` (`W.measure = c V ⌞ (Ω × G)`) and
`Θ^n(μ_W, ·) ≥ 1` holds `μ_W`-a.e., then `Θ^n(μ_V, ·) ≥ c⁻¹` holds `μ_V`-a.e. on `Ω`.  Near a
good `y ∈ Ω`, `μ_V(B_ρ(y)) = c⁻¹ μ_W(B_ρ(y))` for small `ρ`, so `density_scaling` with `t = 1`
gives `Θ^n(μ_V, y) = c⁻¹ Θ^n(μ_W, y) ≥ c⁻¹`. -/
theorem Submission.varifold_tangents_dlb_ae_hasDensity_of_restricted :
    ∀ (N n : ℕ) (U Ω : Set (Euclidean N)) (V : Varifold N n U) (W : Varifold N n Ω) (c : ℝ≥0∞), c ≠ 0 → c ≠ ∞ → W.measure = c • V.measure.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → (∀ᵐ y ∂W.weight, ∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ 1 ≤ θ) → ∀ᵐ y ∂V.weight, y ∈ Ω → ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ c⁻¹ ≤ θ := by
  intro N n U Ω V W c hc0 hctop hW hdens
  have hΩ : MeasurableSet Ω := W.isOpen_domain.measurableSet
  -- Step 2: `μ_W = c • (μ_V ⌞ Ω)`, checked on Borel sets.
  have hweight : W.weight = c • V.weight.restrict Ω := by
    ext A hA
    rw [W.weight_apply hA, hW, Measure.smul_apply,
      Measure.restrict_apply (hA.prod MeasurableSet.univ), prod_inter_prod, inter_univ,
      Measure.smul_apply, Measure.restrict_apply hA, V.weight_apply (hA.inter hΩ)]
  -- Step 3: `μ_V ⌞ Ω ≪ μ_W` as `c ≠ 0`, so `W` has a density `≥ 1` at `μ_V`-a.e. `y ∈ Ω`.
  have hac : V.weight.restrict Ω ≪ W.weight := by
    rw [hweight]
    exact Measure.absolutelyContinuous_smul hc0
  filter_upwards [(ae_restrict_iff' hΩ).1 (hac.ae_le hdens)] with y hy hyΩ
  obtain ⟨θ, hθ, h1θ⟩ := hy hyΩ
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 W.isOpen_domain y hyΩ
  -- Step 5: `density_scaling` with `(μ, ν, z, t, c) = (μ_W, μ_V, y, 1, c⁻¹)`.
  refine ⟨c⁻¹ * θ, Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling N n W.weight
    V.weight y y 1 δ c⁻¹ θ one_pos hδ (ENNReal.inv_ne_top.2 hc0) (fun ρ _ hρδ ↦ ?_) hθ, ?_⟩
  · -- Step 4: `B_ρ(y) ⊆ Ω` for `ρ < δ`, so `μ_V(B_ρ(y)) = c⁻¹ μ_W(B_ρ(y))`.
    rw [inv_one, one_pow, ENNReal.ofReal_one, one_mul, one_mul, hweight, Measure.smul_apply,
      Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.2 ((closedBall_subset_ball hρδ).trans hδΩ), smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  · calc c⁻¹ = c⁻¹ * 1 := (mul_one _).symm
      _ ≤ c⁻¹ * θ := by gcongr
/-- Simon Ch. 8, 5.1–5.2 (p. 215), the change of variables behind the first variation of the
rescaled varifold `V_{x,t} = η_{x,t #} V`: for a `C¹` field `X` and `t > 0`,
`∫ div_S X dV_{x,t} = t⁻ⁿ δV(Y)` with `Y(z) = t X(t⁻¹(z - x))`, since `DY(z) = DX(t⁻¹(z - x))`. -/
theorem Submission.varifold_tangents_rdb_rescaled_integral_eq :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t : ℝ) (X : Euclidean N → Euclidean N), 0 < t → ContDiff ℝ 1 X → ∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x t) = t⁻¹ ^ n * V.firstVariation (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) := by
  intro N n U V x t X ht hX
  -- Step 1: `D(t X(t⁻¹(· - x)))(w) = t (DX(t⁻¹(w - x)) ∘ t⁻¹ id) = DX(t⁻¹(w - x))`.
  have hfderiv : ∀ w : Euclidean N,
      fderiv ℝ (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) w = fderiv ℝ X (t⁻¹ • (w - x)) := by
    intro w
    have hψ : HasFDerivAt (fun z : Euclidean N ↦ t⁻¹ • (z - x))
        (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N)) w :=
      ((hasFDerivAt_id w).sub_const x).const_smul t⁻¹
    have hXψ : HasFDerivAt X (fderiv ℝ X (t⁻¹ • (w - x))) (t⁻¹ • (w - x)) :=
      (hX.differentiable one_ne_zero _).hasFDerivAt
    have hY : HasFDerivAt (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x)))
        (t • (fderiv ℝ X (t⁻¹ • (w - x))).comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N))) w :=
      (hXψ.comp w hψ).const_smul t
    rw [hY.fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [smul_smul, mul_inv_cancel₀ ht.ne']
  -- Step 2: hence `div_S Y(z) = div_S X(t⁻¹(z - x))` for every `(z, S)`.
  have hdiv : ∀ z : Euclidean N × Grassmannian N n,
      Varifold.tangentialDivergence X (t⁻¹ • (z.1 - x)) z.2 =
        Varifold.tangentialDivergence (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) z.1 z.2 := by
    intro z
    simp only [Varifold.tangentialDivergence, Varifold.jacobian, hfderiv]
  -- Steps 3–5: pull out the factor `t⁻ⁿ`, then change variables along `(z, S) ↦ (t⁻¹(z - x), S)`.
  have hφ : Measurable (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) :=
    ((measurable_fst.sub_const x).const_smul t⁻¹).prodMk measurable_snd
  rw [rescaledMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    integral_map hφ.aemeasurable (Varifold.continuous_tangentialDivergence hX).aestronglyMeasurable]
  simp only [hdiv]
  rfl
/-- **Simon Ch. 8, 2.5 (p. 209), the supremum bound** (child `first_variation_sup_bound` of the
rescaled divergence bound for varifold tangents).  If `V` has locally bounded first variation,
`W ⊂⊂ U` is open and `Y` is a `C¹` field with `spt Y ⊆ W` and `|Y| ≤ K`, then
`|δV(Y)| ≤ K ‖δV‖(W)`: `Y` is a test field, `‖δV‖(W)` is the supremum in 2.5
(`firstVariationRieszMeasure_eq_norm`), and `K⁻¹ Y` is admissible in that supremum. -/
theorem Submission.varifold_tangents_rdb_firstVariation_le_variationMeasure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (W : Set (Euclidean N)) (Y : Euclidean N → Euclidean N) (K : ℝ), V.HasLocallyBoundedFirstVariation → IsOpen W → IsCompact (closure W) → closure W ⊆ U → ContDiff ℝ 1 Y → tsupport Y ⊆ W → (∀ z, ‖Y z‖ ≤ K) → ENNReal.ofReal |V.firstVariation Y| ≤ ENNReal.ofReal K * variationMeasure V W := by
  intro N n U V W Y K hV hW hWc hWU hY hYW hYK
  -- Step 1: `spt Y ⊆ W ⊆ closure W`, which is compact and contained in `U`, so `Y` is a test field.
  have hYc : HasCompactSupport Y :=
    hWc.of_isClosed_subset (isClosed_tsupport Y) (hYW.trans subset_closure)
  let Y' : Varifold.TestVectorField U := ⟨Y, hY, hYc, (hYW.trans subset_closure).trans hWU⟩
  -- Step 2: `‖δV‖(W)` is the supremum in 2.5.
  have hμW : variationMeasure V W = V.firstVariationNormOn W := by
    rw [variationMeasure, dite_eq_left hV]
    exact V.firstVariationRieszMeasure_eq_norm hV W hW ⟨hWc, hWU⟩
  rw [hμW]
  -- Step 3: `0 ≤ ‖Y 0‖ ≤ K`.
  have hK : 0 ≤ K := (norm_nonneg _).trans (hYK 0)
  rcases hK.eq_or_lt with rfl | hKpos
  · -- Step 4: if `K = 0` then `Y = 0` and `δV(Y) = 0`.
    have hY0 : Y = fun _ ↦ 0 := funext fun z ↦ norm_le_zero_iff.mp (hYK z)
    rw [hY0, V.firstVariation_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  · -- Step 5: `K⁻¹ Y` is a unit test field supported in `W`, so it enters the supremum.
    have hunit : (Y'.scale K⁻¹).UnitSupportedIn W := by
      refine ⟨(Y'.tsupport_scale_subset _).trans hYW, fun z ↦ ?_⟩
      change ‖K⁻¹ • Y z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKpos)]
      calc K⁻¹ * ‖Y z‖ ≤ K⁻¹ * K := mul_le_mul_of_nonneg_left (hYK z) (inv_nonneg.mpr hK)
        _ = 1 := inv_mul_cancel₀ hKpos.ne'
    have hle := V.le_firstVariationNormOn W _ hunit
    -- Step 6: `δV(K⁻¹ Y) = K⁻¹ δV(Y)`.
    change ENNReal.ofReal |V.firstVariation (K⁻¹ • Y)| ≤ _ at hle
    rw [V.firstVariation_const_smul K⁻¹ hY hYc, abs_mul, abs_of_pos (inv_pos.mpr hKpos)] at hle
    -- Step 7: `|δV(Y)| = K (K⁻¹ |δV(Y)|)`.
    calc ENNReal.ofReal |V.firstVariation Y|
        = ENNReal.ofReal K * ENNReal.ofReal (K⁻¹ * |V.firstVariation Y|) := by
          rw [← ENNReal.ofReal_mul hK, ← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul]
      _ ≤ ENNReal.ofReal K * V.firstVariationNormOn W := mul_le_mul_right hle _

/-- **Simon Ch. 8, 5.1–5.2, the first-variation bound for `V_{x,t}`** (child
`rescaled_divergence_bound` of `varifold_tangents`): if `X` is `C¹`, `spt X ⊆ B°_R(0)` and
`|X| ≤ M`, then `|∫ div_S X dV_{x,t}| ≤ M R^{n-1} (tR)^{1-n} ‖δV‖(B_{tR}(x))`.
With `ψ(z) = t⁻¹(z - x)` and `Y(z) = t X(ψ z)`, `∫ div_S X dV_{x,t} = t^{-n} δV(Y)`
(`varifold_tangents_rdb_rescaled_integral_eq`).  `Y` is `C¹`, `|Y| ≤ tM` and
`spt Y ⊆ ψ⁻¹(B°_R(0)) = B°_{tR}(x)`, an open set with compact closure inside `B_{tR}(x) ⊆ U`, so 2.5
gives `|δV(Y)| ≤ tM ‖δV‖(B°_{tR}(x))` (`varifold_tangents_rdb_firstVariation_le_variationMeasure`).
The rest is `ℝ≥0∞` arithmetic: `t^{-n} · tM · A = M (R^n / R) (tR · A / (tR)^n)`. -/
theorem Submission.varifold_tangents_rescaled_divergence_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R M : ℝ) (X : Euclidean N → Euclidean N), V.HasLocallyBoundedFirstVariation → 0 < t → 0 < R → closedBall x (t * R) ⊆ U → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball (0 : Euclidean N) R → (∀ y, ‖X y‖ ≤ M) → ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x t)| ≤ ENNReal.ofReal M * (ENNReal.ofReal R ^ n / ENNReal.ofReal R) * (ENNReal.ofReal (t * R) * variationMeasure V (closedBall x (t * R)) / ENNReal.ofReal (t * R) ^ n) := by
  intro N n U V x t R M X hV ht hR hBU hX _ hXR hXM
  rw [Submission.varifold_tangents_rdb_rescaled_integral_eq N n U V x t X ht hX]
  -- The pulled-back field `Y(z) = t X(t⁻¹(z - x))`: `C¹`, `|Y| ≤ tM`, `spt Y ⊆ B°_{tR}(x)`.
  have hψ : Continuous (fun z : Euclidean N ↦ t⁻¹ • (z - x)) := by fun_prop
  have hY : ContDiff ℝ 1 (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) := by fun_prop
  have hYM : ∀ z, ‖t • X (t⁻¹ • (z - x))‖ ≤ t * M := fun z ↦ by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (hXM _) ht.le
  have hYW : tsupport (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) ⊆ ball x (t * R) := by
    refine (tsupport_smul_subset_right (fun _ ↦ t) _).trans
      ((tsupport_comp_subset_preimage X hψ).trans fun z hz ↦ ?_)
    have hz' := mem_ball_zero_iff.1 (hXR hz)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht] at hz'
    exact mem_ball_iff_norm.2 hz'
  -- `W = B°_{tR}(x)` is open with compact closure inside `B_{tR}(x) ⊆ U`: 2.5 with `K = tM`.
  have hWcl : closure (ball x (t * R)) ⊆ closedBall x (t * R) := closure_ball_subset_closedBall
  have hδ := Submission.varifold_tangents_rdb_firstVariation_le_variationMeasure N n U V
    (ball x (t * R)) _ (t * M) hV isOpen_ball
    ((isCompact_closedBall x (t * R)).of_isClosed_subset isClosed_closure hWcl)
    (hWcl.trans hBU) hY hYW hYM
  -- `ℝ≥0∞` arithmetic: `ofReal t, ofReal R ∈ (0, ∞)`; insert `(R R⁻¹)(R R⁻¹)^n = 1`, rearrange.
  have htn : 0 ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 ht.le) n
  have hr : ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top
  rw [abs_mul, abs_of_nonneg htn, ENNReal.ofReal_mul htn, ENNReal.ofReal_pow (inv_nonneg.2 ht.le),
    ENNReal.ofReal_inv_of_pos ht, ENNReal.ofReal_mul ht.le, mul_pow, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 ht).ne'))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), ENNReal.inv_pow, ENNReal.inv_pow]
  calc (ENNReal.ofReal t)⁻¹ ^ n * ENNReal.ofReal |V.firstVariation fun z ↦ t • X (t⁻¹ • (z - x))|
      ≤ (ENNReal.ofReal t)⁻¹ ^ n *
          (ENNReal.ofReal t * ENNReal.ofReal M * variationMeasure V (closedBall x (t * R))) := by
        gcongr
        rw [← ENNReal.ofReal_mul ht.le]
        refine hδ.trans ?_
        gcongr
        exact ball_subset_closedBall
    _ = (ENNReal.ofReal t)⁻¹ ^ n *
          (ENNReal.ofReal t * ENNReal.ofReal M * variationMeasure V (closedBall x (t * R))) *
          (ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹ *
            (ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹) ^ n) := by
        rw [hr, one_pow, mul_one, mul_one]
    _ = _ := by ring

/-- **Simon Ch. 8, 5.4 (p. 215), varifold tangents are stationary** (child `limit_stationary` of
`varifold_tangents`): if `V` has locally bounded first variation, `x ∈ U`,
`γ(ρ) = ρ^{1-n} ‖δV‖(B_ρ(x)) → 0` as `ρ ↓ 0` (5.1) and `C ∈ VarTan(V, x)`, then `C` is stationary.
For `X ∈ K(ℝ^N;ℝ^N)`, `div_S X` is continuous with compact support, so vague convergence gives
`I_j = ∫ div_S X dV_{x,t_j} → δC(X)`.  With `spt X ⊆ B°_R(0)`, `|X| ≤ M` and `B_r(x) ⊆ U`, for large
`j` the rescaled divergence bound (`varifold_tangents_rescaled_divergence_bound`) gives
`|I_j| ≤ M (R^n / R) γ(t_j R) → 0`, hence `δC(X) = 0`. -/
theorem Submission.varifold_tangents_limit_stationary :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (C : Varifold N n (univ : Set (Euclidean N))), V.HasLocallyBoundedFirstVariation → x ∈ U → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → IsVarifoldTangent V x C → C.Stationary := by
  rintro N n U V x C hV hx h51 ⟨t, ht, ht0, hconv⟩ X
  -- Step 1: `div_S X ∈ C_c(Gₙ(ℝ^N))`, so `I_j = ∫ div_S X dV_{x,t_j} → δC(X)`.
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    ⟨⟨fun z ↦ Varifold.tangentialDivergence X z.1 z.2,
      Varifold.continuous_tangentialDivergence X.contDiff⟩,
      Varifold.hasCompactSupport_tangentialDivergence X X.compactSupport⟩
  have hI : Tendsto (fun j ↦ ∫ z, Varifold.tangentialDivergence X z.1 z.2
      ∂(rescaledMeasure V x (t j))) atTop (𝓝 (C.firstVariation X)) := hconv f
  -- Step 2: `spt X ⊆ B°_R(0)` with `R > 0`, `|X| ≤ M`, and `B_r(x) ⊆ U` with `r > 0`.
  obtain ⟨R, hR, hXR⟩ := X.compactSupport.isBounded.subset_ball_lt 0 0
  obtain ⟨M, hM⟩ := X.compactSupport.exists_bound_of_continuous X.contDiff.continuous
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (V.isOpen_domain.mem_nhds hx)
  -- Step 3: `t_j R → 0`, so for large `j`, `B_{t_j R}(x) ⊆ U` and `ofReal |I_j| ≤ K γ(t_j R)`.
  have htR : Tendsto (fun j ↦ t j * R) atTop (𝓝 0) := by
    simpa using ht0.mul_const R
  obtain ⟨K, hK, hbound⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ᶠ j in atTop,
      ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x (t j))| ≤
        K * (ENNReal.ofReal (t j * R) * variationMeasure V (closedBall x (t j * R)) /
          ENNReal.ofReal (t j * R) ^ n) := by
    refine ⟨ENNReal.ofReal M * (ENNReal.ofReal R ^ n / ENNReal.ofReal R),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.ofReal_pos.2 hR).ne'), ?_⟩
    filter_upwards [htR.eventually (eventually_lt_nhds hr)] with j hj
    exact Submission.varifold_tangents_rescaled_divergence_bound N n U V x (t j) R M X hV (ht j) hR
      ((closedBall_subset_closedBall hj.le).trans hrU) X.contDiff X.compactSupport hXR hM
  -- Step 4: `t_j R → 0⁺`, so `K γ(t_j R) → K · 0 = 0` by (5.1); squeeze, then `|I_j| → 0`.
  have hγ := h51.comp (tendsto_nhdsWithin_iff.2
    ⟨htR, Eventually.of_forall fun j ↦ mul_pos (ht j) hR⟩)
  have hKγ := ENNReal.Tendsto.const_mul hγ (Or.inr hK)
  rw [mul_zero] at hKγ
  have habs := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKγ
    (Eventually.of_forall fun _ ↦ zero_le) hbound
  have habs' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp habs
  rw [ENNReal.toReal_zero] at habs'
  have hI0 : Tendsto (fun j ↦ ∫ z, Varifold.tangentialDivergence X z.1 z.2
      ∂(rescaledMeasure V x (t j))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j ↦ (Real.norm_eq_abs _).le)
      (habs'.congr fun j ↦ ENNReal.toReal_ofReal (abs_nonneg _))
  -- Step 5: uniqueness of limits in `ℝ`.
  exact tendsto_nhds_unique hI hI0

/-- **Simon Ch. 8, 5.2 (centre corrected to `0`), ball masses of a varifold tangent** (child
`limit_ball_mass` of `varifold_tangents`): if `Θ^n(μ_V, x) = θ₀` and `C ∈ VarTan(V, x)`, then
`μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every `ρ > 0`.
Write `L(r) = θ₀ ω_n r^n` and `K_r = B_r(0) × G(N,n)`.  For the radii `t_j > 0`, `t_j → 0` of `C`,
`varifold_tangents_rescaled_ball_mass_tendsto` gives `V_{x,t_j}(K_r) → L(r) < ∞` for `r > 0`.  As
`C(K_ρ') = μ_C(B_ρ'(0)) < ∞`, `varifold_tangents_lbm_vague_cylinder_bounds` (with `a = ρ`, `b = ρ'`)
gives `μ_C(B_ρ(0)) ≤ L(ρ')` and `L(ρ) ≤ μ_C(B_ρ'(0))` for every `ρ' > ρ`.  Let `ρ' ↓ ρ`: `L` is
continuous, and `μ_C(B_ρ'(0)) → μ_C(B_ρ(0))` by continuity from above, since
`⋂_{ρ' > ρ} B_ρ'(0) = B_ρ(0)`. -/
theorem Submission.varifold_tangents_limit_ball_mass :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ) (C : Varifold N n (univ : Set (Euclidean N))), HasDensity n V.weight x (ENNReal.ofReal θ₀) → IsVarifoldTangent V x C → ∀ ρ : ℝ, 0 < ρ → C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n := by
  intro N n U V x θ₀ C hθ hC ρ hρ
  obtain ⟨t, ht_pos, ht_lim, hconv⟩ := hC
  set L : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal r ^ n
  -- `t j → 0⁺`, so `V_{x,t_j}(B_r(0) × G(N,n)) → L r < ∞` for every `r > 0`.
  have ht : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨ht_lim, Eventually.of_forall ht_pos⟩
  have hmass : ∀ r : ℝ, 0 < r → Tendsto (fun j ↦ rescaledMeasure V x (t j)
      (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 (L r)) :=
    fun r hr ↦ (Submission.varifold_tangents_rescaled_ball_mass_tendsto N n U V x _ r hθ hr).comp ht
  have hc : ENNReal.ofReal θ₀ * unitBallVolume n ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hL : ∀ r, L r ≠ ∞ := fun r ↦ ENNReal.mul_ne_top hc (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- `C(B_r(0) × G(N,n)) = μ_C(B_r(0)) < ∞`, as `B_r(0)` is compact.
  have hCK : ∀ r : ℝ, C.measure (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n)))
      = C.weight (closedBall 0 r) := fun r ↦ (C.weight_apply measurableSet_closedBall).symm
  have hCtop : ∀ r : ℝ, C.weight (closedBall 0 r) ≠ ∞ :=
    fun r ↦ C.weight_finite_on_compact _ (isCompact_closedBall 0 r) (subset_univ _)
  -- For `ρ' > ρ`: `μ_C(B_ρ(0)) ≤ L ρ'` and `L ρ ≤ μ_C(B_ρ'(0))`.
  have hbd : ∀ ρ' > ρ, C.weight (closedBall 0 ρ) ≤ L ρ' ∧ L ρ ≤ C.weight (closedBall 0 ρ') := by
    intro ρ' hρ'
    have := Submission.varifold_tangents_lbm_vague_cylinder_bounds N n _ C.measure ρ ρ' (L ρ)
      (L ρ') hconv hρ' (hCK ρ' ▸ hCtop ρ') (hmass ρ hρ) (hmass ρ' (hρ.trans hρ')) (hL ρ')
    rwa [hCK, hCK] at this
  -- Let `ρ' ↓ ρ`: `L` is continuous and `r ↦ μ_C(B_r(0))` is continuous from the right.
  have hLlim : Tendsto L (𝓝[>] ρ) (𝓝 (L ρ)) :=
    ((ENNReal.continuous_const_mul hc).comp
      ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hClim : Tendsto (fun r ↦ C.weight (closedBall (0 : Euclidean N) r)) (𝓝[>] ρ)
      (𝓝 (C.weight (closedBall 0 ρ))) := by
    have := tendsto_measure_biInter_gt (μ := C.weight) (s := closedBall (0 : Euclidean N)) (a := ρ)
      (fun r _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun i j _ hij ↦ closedBall_subset_closedBall hij) ⟨ρ + 1, by linarith, hCtop _⟩
    rwa [biInter_gt_closedBall] at this
  have hev : ∀ᶠ ρ' in 𝓝[>] ρ, ρ < ρ' := self_mem_nhdsWithin
  exact le_antisymm (ge_of_tendsto hLlim (hev.mono fun ρ' h ↦ (hbd ρ' h).1))
    (ge_of_tendsto hClim (hev.mono fun ρ' h ↦ (hbd ρ' h).2))
/-- Radial Euler identity for a stationary varifold `C` on `ℝ^N` with `y ∈ S` for `C`-a.e.
`(y, S)` (Simon Ch. 8, 3.5 at `x = 0` with vanishing normal defect): testing `δC = 0` against the
radial field `X(y) = g(y) y` gives `∫ (n g(y) + Dg(y)(y)) dμ_C(y) = 0` for every compactly
supported `C¹` function `g`. -/
theorem Submission.varifold_tangents_rh_radial_euler_identity :
    ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))), C.Stationary → (∀ᵐ z ∂C.measure, Grassmannian.project z.2 z.1 = z.1) → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, ((n : ℝ) * g y + fderiv ℝ g y y) ∂C.weight = 0 := by
  intro N n C hC hrad g hg hgc
  -- Step 1: the radial test field `X(y) = g(y) • y` lies in `K(ℝ^N; ℝ^N)`, so `δC(X) = 0`.
  have hX : C.firstVariation (fun y ↦ g y • y) = 0 :=
    hC ⟨fun y ↦ g y • y, hg.smul contDiff_id, hgc.smul_right, subset_univ _⟩
  -- Steps 2–3: `div_S X(y) = n g(y) + Dg(y)(p_S y)` for every `(y, S)`, since
  -- `P_S ∘ DX(y) = g(y) P_S + Dg(y)(·) p_S y` and `trace P_S = n`.
  have hdiv : ∀ (y : Euclidean N) (S : Grassmannian N n),
      Varifold.tangentialDivergence (fun y ↦ g y • y) y S =
        n * g y + fderiv ℝ g y (S.project y) := by
    intro y S
    let b := (Grassmannian.coordinateBasis (N := N)).toBasis
    have hcomp : S.projectionLinearMap ∘ₗ
        (fderiv ℝ (fun y ↦ g y • y) y : Euclidean N →ₗ[ℝ] Euclidean N) =
        g y • S.projectionLinearMap +
          (fderiv ℝ g y : Euclidean N →ₗ[ℝ] ℝ).smulRight (S.project y) := by
      rw [fderiv_fun_smul (f := fun y : Euclidean N ↦ y) (hg.differentiable_one y)
        differentiableAt_id, fderiv_fun_id]
      refine LinearMap.ext fun v ↦ ?_
      simp [Grassmannian.project]
    rw [Varifold.tangentialDivergence, Varifold.jacobian_eq_toMatrix,
      ← Grassmannian.toMatrix_projectionLinearMap S, ← LinearMap.toMatrix_comp,
      ← LinearMap.trace_eq_matrix_trace ℝ b, hcomp, map_add, map_smul,
      LinearMap.trace_smulRight, LinearMap.trace_eq_matrix_trace ℝ b,
      Grassmannian.toMatrix_projectionLinearMap, Grassmannian.trace_eq, smul_eq_mul, mul_comm]
    rfl
  -- Step 4: by the radial hypothesis, `div_S X(y) = n g(y) + Dg(y)(y)` for `C`-a.e. `(y, S)`.
  have hae : (fun z : Euclidean N × Grassmannian N n ↦
      Varifold.tangentialDivergence (fun y ↦ g y • y) z.1 z.2) =ᵐ[C.measure]
      fun z ↦ (n : ℝ) * g z.1 + fderiv ℝ g z.1 z.1 := by
    filter_upwards [hrad] with z hz
    rw [hdiv, hz]
  -- Step 5: the integrand is continuous, so it transfers to `μ_C = π_# C` (`integral_map`).
  have hcont : Continuous (fun y ↦ (n : ℝ) * g y + fderiv ℝ g y y) :=
    (continuous_const.mul hg.continuous).add
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_id)
  rw [Varifold.weight, integral_map measurable_fst.aemeasurable hcont.aestronglyMeasurable,
    ← integral_congr_ae hae]
  exact hX
/-- Integration of Euler's ODE (used for the radial homogeneity of tangent cones, Simon Ch. 8,
5.3): if `F'(t) = n F(t) / t` for every `t > 0`, then `F(s) = sⁿ F(1)` for every `s > 0`. -/
theorem Submission.varifold_tangents_rh_edc_pow_of_hasDerivAt :
    ∀ (n : ℕ) (F : ℝ → ℝ), (∀ t : ℝ, 0 < t → HasDerivAt F ((n : ℝ) * F t / t) t) → ∀ s : ℝ, 0 < s → F s = s ^ n * F 1 := by
  intro n F hF s hs
  -- Steps 1–3: `G(r) = F(r) / rⁿ` has derivative `0` at every `t > 0` (quotient rule, `tⁿ ≠ 0`).
  have hG : ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ ↦ F r / r ^ n) 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    refine ((hF t ht).fun_div (hasDerivAt_pow n t) (pow_ne_zero n ht0)).congr_deriv ?_
    rcases n with _ | m
    · simp
    · rw [Nat.add_sub_cancel]
      field_simp
      ring
  -- Step 4: `G` is constant on the open preconnected set `(0, ∞)`, so `G(s) = G(1)`.
  have hconst : F s / s ^ n = F 1 / 1 ^ n :=
    (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero (f := fun r : ℝ ↦ F r / r ^ n)
      isPreconnected_Ioi (fun t ht ↦ (hG t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hG t ht).deriv) hs (Set.mem_Ioi.mpr one_pos)
  -- Step 5: `G(1) = F(1)`; clear the denominator `sⁿ ≠ 0`.
  rw [one_pow, div_one, div_eq_iff (pow_ne_zero n hs.ne')] at hconst
  exact hconst.trans (mul_comm _ _)
/-- Euler's identity on the dilates (used for the radial homogeneity of tangent cones, Simon
Ch. 8, 5.3): if `∫ (n h + Dh(y) y) dμ = 0` for every compactly supported `C¹` function `h`, then
`n ∫ g(t⁻¹ y) dμ + ∫ Dg(t⁻¹ y)(t⁻¹ y) dμ = 0` for every such `g` and every `t > 0`. -/
theorem Submission.varifold_tangents_rh_edc_euler_dilate :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → (∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, ((n : ℝ) * g y + fderiv ℝ g y y) ∂μ = 0) → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ t : ℝ, 0 < t → (n : ℝ) * (∫ y, g (t⁻¹ • y) ∂μ) + ∫ y, fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y) ∂μ = 0 := by
  intro N n μ hμ H g hg hgc t ht
  have hc : t⁻¹ ≠ 0 := inv_ne_zero ht.ne'
  -- Step 2: the dilate `y ↦ g (t⁻¹ • y)` is `C¹` with compact support.
  have hdil : ContDiff ℝ 1 (fun y : Euclidean N ↦ g (t⁻¹ • y)) :=
    hg.comp (contDiff_id.const_smul t⁻¹)
  have hdilc : HasCompactSupport (fun y : Euclidean N ↦ g (t⁻¹ • y)) := hgc.comp_smul hc
  -- Step 3: chain rule, `D(g(t⁻¹ •))(y) y = Dg(t⁻¹ • y)(t⁻¹ • y)`.
  have hchain : ∀ y : Euclidean N,
      fderiv ℝ (fun z : Euclidean N ↦ g (t⁻¹ • z)) y y = fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y) := by
    intro y
    have hy : HasFDerivAt (fun z : Euclidean N ↦ g (t⁻¹ • z))
        ((fderiv ℝ g (t⁻¹ • y)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N))) y :=
      ((hg.differentiable one_ne_zero) (t⁻¹ • y)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).const_smul t⁻¹)
    rw [hy.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply]
  -- Step 4: both summands are continuous with compact support, hence `μ`-integrable.
  have hi₁ : Integrable (fun y : Euclidean N ↦ (n : ℝ) * g (t⁻¹ • y)) μ :=
    (hdil.continuous.integrable_of_hasCompactSupport hdilc).const_mul _
  have hDc : Continuous (fun x : Euclidean N ↦ fderiv ℝ g x x) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_id
  -- `Dg(x) = 0` off `tsupport g`, so `x ↦ Dg(x) x` is supported in the compact `tsupport g`.
  have hDs : HasCompactSupport (fun x : Euclidean N ↦ fderiv ℝ g x x) := by
    refine hgc.mono' fun x hx ↦ ?_
    by_contra hxg
    exact hx (by simp only [fderiv_of_notMem_tsupport ℝ hxg, zero_apply])
  have hi₂ : Integrable (fun y : Euclidean N ↦ fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y)) μ :=
    (hDc.comp (continuous_const_smul t⁻¹)).integrable_of_hasCompactSupport (hDs.comp_smul hc)
  -- Step 5: apply the hypothesis to the dilate, rewrite by the chain rule and split the integral.
  have hH := H _ hdil hdilc
  simp only [hchain] at hH
  rwa [integral_add hi₁ hi₂, integral_const_mul] at hH
/-- Differentiation under the integral sign for dilates (used for the homogeneity 5.3 in Simon
Ch. 8): if `μ` is finite on compact sets and `g` is `C¹` with compact support, then for `t > 0` the
function `r ↦ ∫ g(r⁻¹y) dμ(y)` has derivative `-(t⁻¹ ∫ Dg(t⁻¹y)(t⁻¹y) dμ(y))` at `t`. -/
theorem Submission.varifold_tangents_rh_edc_hasDerivAt_dilate_integral :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => ∫ y, g (r⁻¹ • y) ∂μ) (-(t⁻¹ * ∫ y, fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y) ∂μ)) t := by
  intro N μ hμ g hg hgc t ht
  -- Step 2: `tsupport g ⊆ B_R(0)` with `R > 0`, and `‖Dg‖ ≤ L` everywhere with `L ≥ 0`.
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hDcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Euclidean N)
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsuppR : tsupport g ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨L, hL⟩ := hDcont.bounded_above_of_compact_support (hgc.fderiv ℝ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- Step 3: for `r > 0`, `ρ ↦ g(ρ⁻¹y)` has derivative `Φ(r,y) = -(r⁻¹ Dg(r⁻¹y)(r⁻¹y))` at `r`.
  have hpt : ∀ y : Euclidean N, ∀ r : ℝ, 0 < r →
      HasDerivAt (fun ρ : ℝ => g (ρ⁻¹ • y)) (-(r⁻¹ * fderiv ℝ g (r⁻¹ • y) (r⁻¹ • y))) r := by
    intro y r hr
    have h := (hdiff (r⁻¹ • y)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_inv hr.ne').smul_const y)
    refine h.congr_deriv ?_
    simp only [map_smul, smul_eq_mul]
    ring
  -- Step 4: the neighbourhood `(t/2, 2t)` of `t` and the bound `b = (2LR/t) 1_{B_{2tR}(0)}`.
  have hI : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  set b : Euclidean N → ℝ :=
    (closedBall (0 : Euclidean N) (2 * t * R)).indicator fun _ => 2 * L * R / t with hb
  -- Step 5: `|Φ(r,y)| ≤ b(y)` for every `y` and every `r ∈ (t/2, 2t)`.
  have hbound : ∀ y : Euclidean N, ∀ r ∈ Ioo (t / 2) (2 * t),
      ‖-(r⁻¹ * fderiv ℝ g (r⁻¹ • y) (r⁻¹ • y))‖ ≤ b y := by
    intro y r hr
    have hr0 : 0 < r := by linarith [hr.1]
    by_cases hy : r⁻¹ • y ∈ tsupport g
    · have hyR : ‖r⁻¹ • y‖ ≤ R := mem_closedBall_zero_iff.1 (hsuppR hy)
      have hyb : y ∈ closedBall (0 : Euclidean N) (2 * t * R) := by
        rw [mem_closedBall_zero_iff]
        calc ‖y‖ = r * ‖r⁻¹ • y‖ := by
              rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), ← mul_assoc,
                mul_inv_cancel₀ hr0.ne', one_mul]
          _ ≤ 2 * t * R := mul_le_mul hr.2.le hyR (norm_nonneg _) (by linarith)
      have hD : |fderiv ℝ g (r⁻¹ • y) (r⁻¹ • y)| ≤ L * R :=
        ((fderiv ℝ g (r⁻¹ • y)).le_opNorm _).trans (mul_le_mul (hL _) hyR (norm_nonneg _) hL0)
      have hinv : r⁻¹ ≤ 2 / t := by
        rw [inv_le_comm₀ hr0 (by positivity), inv_div]
        exact hr.1.le
      rw [hb, indicator_of_mem hyb, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hr0)]
      calc r⁻¹ * |fderiv ℝ g (r⁻¹ • y) (r⁻¹ • y)| ≤ 2 / t * (L * R) :=
            mul_le_mul hinv hD (abs_nonneg _) (by positivity)
        _ = 2 * L * R / t := by ring
    · rw [fderiv_of_notMem_tsupport ℝ hy, zero_apply, mul_zero, neg_zero, norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) y
  -- Step 6: integrability of `b` and of `F(t,·)`, measurability of `F(r,·)` and `Φ(t,·)`.
  have hb_int : Integrable b μ :=
    (integrableOn_const (isCompact_closedBall 0 _).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hF_meas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun y : Euclidean N => g (r⁻¹ • y)) μ :=
    Eventually.of_forall fun r =>
      (hg.continuous.comp (continuous_const_smul r⁻¹)).aestronglyMeasurable
  have hF_int : Integrable (fun y : Euclidean N => g (t⁻¹ • y)) μ :=
    (hg.continuous.comp (continuous_const_smul t⁻¹)).integrable_of_hasCompactSupport
      (hgc.comp_smul (inv_ne_zero ht.ne'))
  have hF'_meas : AEStronglyMeasurable
      (fun y : Euclidean N => -(t⁻¹ * fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y))) μ :=
    (((hDcont.comp (continuous_const_smul t⁻¹)).clm_apply
      (continuous_const_smul t⁻¹)).const_mul t⁻¹).neg.aestronglyMeasurable
  -- Step 7: differentiation under the integral sign.
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r (y : Euclidean N) => g (r⁻¹ • y))
    (F' := fun r (y : Euclidean N) => -(r⁻¹ * fderiv ℝ g (r⁻¹ • y) (r⁻¹ • y)))
    hI hF_meas hF_int hF'_meas (Eventually.of_forall fun y r hr => hbound y r hr) hb_int
    (Eventually.of_forall fun y r hr => hpt y r (by linarith [hr.1]))).2
  -- Step 8: `∫ Φ(t,y) dμ = -(t⁻¹ ∫ Dg(t⁻¹y)(t⁻¹y) dμ)`.
  rwa [integral_neg, integral_const_mul] at key

/-- **Simon Ch. 8, 5.3 (p. 215), from Euler's identity to dilation homogeneity** (child
`euler_dilation_c1` of the radial homogeneity step for varifold tangents).  If `μ` is finite on
compact sets and `∫ (n h + Dh(y) y) dμ = 0` for every compactly supported `C¹` function `h`, then
`∫ g(s⁻¹ y) dμ(y) = sⁿ ∫ g dμ` for every such `g` and every `s > 0`: `F(t) = ∫ g(t⁻¹ y) dμ(y)` has
derivative `-t⁻¹ ∫ Dg(t⁻¹ y)(t⁻¹ y) dμ(y)` (differentiation under the integral sign), Euler's
identity on the dilates turns this into `n F(t) / t`, and that ODE forces `F(s) = sⁿ F(1)`. -/
theorem Submission.varifold_tangents_rh_scaling_of_euler_identity :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → (∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, ((n : ℝ) * g y + fderiv ℝ g y y) ∂μ = 0) → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ s : ℝ, 0 < s → ∫ y, g (s⁻¹ • y) ∂μ = s ^ n * ∫ y, g y ∂μ := by
  intro N n μ hμ H g hg hgc s hs
  -- Steps 3, 5 and 6: for `t > 0`, `F'(t) = -t⁻¹ J(t)` and `n F(t) + J(t) = 0`, so
  -- `F'(t) = n F(t) / t`, where `F(t) = ∫ g(t⁻¹ y) dμ` and `J(t) = ∫ Dg(t⁻¹ y)(t⁻¹ y) dμ`.
  have hF : ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ ↦ ∫ y, g (r⁻¹ • y) ∂μ)
      ((n : ℝ) * (∫ y, g (t⁻¹ • y) ∂μ) / t) t := by
    intro t ht
    have hE := Submission.varifold_tangents_rh_edc_euler_dilate N n μ hμ H g hg hgc t ht
    refine (Submission.varifold_tangents_rh_edc_hasDerivAt_dilate_integral N μ hμ g hg hgc t
      ht).congr_deriv ?_
    linear_combination (-t⁻¹) * hE
  -- Step 7: the ODE forces `F(s) = sⁿ F(1)`, and `F(1) = ∫ g dμ`.
  simpa only [inv_one, one_smul] using
    Submission.varifold_tangents_rh_edc_pow_of_hasDerivAt n
      (fun r : ℝ ↦ ∫ y, g (r⁻¹ • y) ∂μ) hF s hs
/-- Uniform convergence with a common compact support gives convergence of integrals: if `μ` is
finite on compacts, `K` is compact, `F k = G` off `K` for every `k` and `F k → G` uniformly, then
`∫ F k dμ → ∫ G dμ` (the limit step of the mollification argument for Simon Ch. 8, 5.3). -/
theorem Submission.varifold_tangents_rh_mc_tendsto_integral_of_uniform :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (K : Set (Euclidean N)) (F : ℕ → Euclidean N → ℝ) (G : Euclidean N → ℝ), IsFiniteMeasureOnCompacts μ → IsCompact K → (∀ k, Integrable (F k) μ) → Integrable G μ → (∀ k, ∀ y ∉ K, F k y = G y) → (∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ y, |F k y - G y| ≤ ε) → Tendsto (fun k => ∫ y, F k y ∂μ) atTop (𝓝 (∫ y, G y ∂μ)) := by
  intro N μ K F G hμ hK hF hG hV hU
  -- Step 1: `μ K < ∞`, and `c := μ.real K` satisfies `0 < c + 1`.
  have hKfin : μ K < ∞ := hμ.lt_top_of_isCompact hK
  have hc1 : 0 < μ.real K + 1 := by linarith [measureReal_nonneg (μ := μ) (s := K)]
  -- Step 5: by `Metric.tendsto_atTop` it suffices to find `k₀` for each `ε > 0`.
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  -- Step 3: `η := ε / (c + 1) > 0`, and `k₀` from the uniform hypothesis for `η`.
  have hη : 0 < ε / (μ.real K + 1) := div_pos hε hc1
  obtain ⟨k₀, hk₀⟩ := hU _ hη
  refine ⟨k₀, fun k hk ↦ ?_⟩
  -- Step 4: `F k - G` vanishes off `K`, so its integral is its integral over `K` (step 2).
  have hint : ∫ y in K, F k y - G y ∂μ = ∫ y, F k y - G y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hV k y hy, sub_self]
  -- Step 2: `|F k - G| ≤ η` on `K` and `μ K < ∞`, so `|∫_K (F k - G) dμ| ≤ η c < ε`.
  rw [Real.dist_eq, ← integral_sub (hF k) hG, ← hint, ← Real.norm_eq_abs]
  calc ‖∫ y in K, F k y - G y ∂μ‖ ≤ ε / (μ.real K + 1) * μ.real K :=
        norm_setIntegral_le_of_norm_le_const hKfin fun y _ ↦ by
          rw [Real.norm_eq_abs]; exact hk₀ k hk y
    _ < ε / (μ.real K + 1) * (μ.real K + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hη
    _ = ε := div_mul_cancel₀ ε hc1.ne'
/-- Uniform `C¹` approximation by mollification (step 3 of extending the dilation law for varifold
tangents, Simon Ch. 8, 5.3, from `C¹_c` to `C_c`): a continuous compactly supported `g` on `ℝ^N`
is the uniform limit of the `C¹` functions `φ_k = ψ_k ⋆ g`, where `ψ_k` is a normalized smooth
bump supported in `B(0, 1/(k+1))`, and `g` and every `φ_k` vanish off the compact set
`K = closedBall 0 1 + tsupport g`. -/
theorem Submission.varifold_tangents_rh_mc_exists_c1_approx :
    ∀ (N : ℕ) (g : Euclidean N → ℝ), Continuous g → HasCompactSupport g → ∃ (K : Set (Euclidean N)) (φ : ℕ → Euclidean N → ℝ), IsCompact K ∧ (∀ y ∉ K, g y = 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, ∀ y ∉ K, φ k y = 0) ∧ (∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ y, |φ k y - g y| ≤ ε) := by
  intro N g hg hgc
  -- Step 1: smooth bumps `b k` at `0` with radii `1 / (2 (k + 1)) < r_k = 1 / (k + 1)`.
  have hr : ∀ k : ℕ, 0 < 1 / (2 * ((k : ℝ) + 1)) ∧ 1 / (2 * ((k : ℝ) + 1)) < 1 / ((k : ℝ) + 1) :=
    fun k ↦ ⟨by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith [k.cast_nonneg (α := ℝ)])⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ContDiffBump (0 : Euclidean N), ∀ k, (b k).rOut = 1 / ((k : ℝ) + 1) :=
    ⟨fun k ↦ ⟨_, _, (hr k).1, (hr k).2⟩, fun k ↦ rfl⟩
  -- The normalizations `ψ k = b k / ∫ b k` (i.e. `(b k).normed volume`): `ψ k ≥ 0`, `∫ ψ k = 1`,
  -- `support (ψ k) ⊆ B(0, r_k)`, and `ψ k` is `C¹` with compact support.
  obtain ⟨ψ, hψ0, hψ1, hψs, hψd, hψc⟩ : ∃ ψ : ℕ → Euclidean N → ℝ, (∀ k x, 0 ≤ ψ k x) ∧
      (∀ k, ∫ x, ψ k x = 1) ∧ (∀ k, Function.support (ψ k) ⊆ ball 0 (1 / ((k : ℝ) + 1))) ∧
      (∀ k, ContDiff ℝ (1 : ℕ∞) (ψ k)) ∧ (∀ k, HasCompactSupport (ψ k)) := by
    have hpos : ∀ k, 0 < ∫ y, b k y := fun k ↦ by
      refine (integral_pos_iff_support_of_nonneg (fun x ↦ (b k).nonneg)
        ((b k).continuous.integrable_of_hasCompactSupport (b k).hasCompactSupport)).2 ?_
      rw [(b k).support_eq]
      exact measure_ball_pos _ _ (b k).rOut_pos
    have hsupp : ∀ k, Function.support (fun x ↦ b k x / ∫ y, b k y) ⊆ Function.support (b k) :=
      fun k x hx h ↦ hx (by simp only [h, zero_div])
    refine ⟨fun k x ↦ b k x / ∫ y, b k y, fun k x ↦ div_nonneg (b k).nonneg (hpos k).le,
      fun k ↦ ?_, fun k ↦ ?_, fun k ↦ (b k).contDiff.div_const _,
      fun k ↦ (b k).hasCompactSupport.mono' ((hsupp k).trans (subset_tsupport _))⟩
    · rw [integral_div, div_self (hpos k).ne']
    · rw [← hb k, ← (b k).support_eq]
      exact hsupp k
  -- Step 2: `K = closedBall 0 1 + tsupport g` is compact; `φ k = ψ k ⋆ g` (Lebesgue convolution).
  refine ⟨closedBall 0 1 + tsupport g,
    fun k ↦ convolution (ψ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    (isCompact_closedBall 0 1).add hgc, ?_, ?_, ?_, ?_⟩
  -- Step 3: `g` vanishes off `K`, since `y = 0 + y` with `0 ∈ closedBall 0 1`.
  · intro y hy
    by_contra h
    refine hy ?_
    simpa only [zero_add] using
      Set.add_mem_add (mem_closedBall_self zero_le_one : (0 : Euclidean N) ∈ closedBall 0 1)
        (subset_tsupport g h)
  -- Step 4: each `φ k` is `C¹` (`ψ k` is `C¹` with compact support, `g` is locally integrable).
  · intro k
    exact (hψc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hψd k)
      hg.locallyIntegrable
  -- Step 5: each `φ k` vanishes off `K`: `support (ψ k ⋆ g) ⊆ support (ψ k) + support g ⊆ K`,
  -- as `support (ψ k) ⊆ B(0, r_k)` and `r_k ≤ 1`.
  · intro k y hy
    by_contra h
    obtain ⟨a, ha, c, hc, rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) h
    refine hy (Set.add_mem_add ?_ (subset_tsupport g hc))
    refine ball_subset_closedBall (ball_subset_ball ?_ (hψs k ha))
    rw [div_le_one (by positivity)]
    linarith [k.cast_nonneg (α := ℝ)]
  -- Step 6: uniform estimate. `g` is uniformly continuous; for `‖x - y‖ < δ` we have
  -- `|g x - g y| < ε`, and `r_k ≤ r_{k₀} < δ` for `k ≥ k₀`, so `|φ k y - g y| ≤ ε`, as `ψ k ≥ 0`
  -- has integral `1` and support in `B(0, r_k)`.
  · intro ε hε
    obtain ⟨δ, hδ, hδg⟩ :=
      Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hg) ε hε
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδ
    refine ⟨k₀, fun k hk y ↦ ?_⟩
    rw [← Real.dist_eq]
    refine dist_convolution_le hε.le (hψs k) (hψ0 k) (hψ1 k) hg.aestronglyMeasurable
      fun x hx ↦ (hδg ?_).le
    calc dist x y < 1 / ((k : ℝ) + 1) := hx
      _ ≤ 1 / ((k₀ : ℝ) + 1) := by gcongr
      _ < δ := hk₀

/-- Extension of the dilation law from `C¹_c` to `C_c` by mollification (step 3 of the proof of
the corrected Simon Ch. 8, 5.3): if `μ` is finite on compact sets, `s > 0` and
`∫ h(s⁻¹ y) dμ(y) = sⁿ ∫ h dμ` for every compactly supported `C¹` function `h`, then the same
identity holds for every continuous compactly supported `g`.  The `C¹` approximants `φ_k → g`
(uniformly, all vanishing off one compact `K`) satisfy the identity, and both sides pass to the
limit because the integrands converge uniformly and agree with their limits off the fixed compact
sets `s • K` and `K`. -/
theorem Submission.varifold_tangents_rh_scaling_continuous :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (s : ℝ), IsFiniteMeasureOnCompacts μ → 0 < s → (∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, g (s⁻¹ • y) ∂μ = s ^ n * ∫ y, g y ∂μ) → ∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → ∫ y, g (s⁻¹ • y) ∂μ = s ^ n * ∫ y, g y ∂μ := by
  intro N n μ s hμ hs hS g hg hgc
  -- Step 3: `C¹` functions `φ k → g` uniformly, with `g` and every `φ k` vanishing off `K`.
  obtain ⟨K, φ, hK, hgK, hφ, hφK, hunif⟩ :=
    Submission.varifold_tangents_rh_mc_exists_c1_approx N g hg hgc
  have hφc : ∀ k, HasCompactSupport (φ k) := fun k ↦ HasCompactSupport.intro hK (hφK k)
  -- Step 4: the hypothesis applies to every `φ k`.
  have h4 : ∀ k, ∫ y, φ k (s⁻¹ • y) ∂μ = s ^ n * ∫ y, φ k y ∂μ :=
    fun k ↦ hS (φ k) (hφ k) (hφc k)
  -- Step 5(i): `∫ φ k dμ → ∫ g dμ`, the differences vanishing off `K`.
  have hlim1 : Tendsto (fun k ↦ ∫ y, φ k y ∂μ) atTop (𝓝 (∫ y, g y ∂μ)) :=
    Submission.varifold_tangents_rh_mc_tendsto_integral_of_uniform N μ K φ g hμ hK
      (fun k ↦ (hφ k).continuous.integrable_of_hasCompactSupport (hφc k))
      (hg.integrable_of_hasCompactSupport hgc)
      (fun k y hy ↦ (hφK k y hy).trans (hgK y hy).symm) hunif
  -- Step 5(ii): `∫ φ k (s⁻¹ y) dμ(y) → ∫ g (s⁻¹ y) dμ(y)`, the differences vanishing off `s • K`
  -- since `y ∉ s • K` gives `s⁻¹ • y ∉ K`.
  have hs' : s⁻¹ ≠ 0 := inv_ne_zero hs.ne'
  have hsK : ∀ y ∉ s • K, s⁻¹ • y ∉ K := fun y hy h ↦
    hy ((mem_smul_set_iff_inv_smul_mem₀ hs.ne' K y).2 h)
  have hlim2 : Tendsto (fun k ↦ ∫ y, φ k (s⁻¹ • y) ∂μ) atTop (𝓝 (∫ y, g (s⁻¹ • y) ∂μ)) :=
    Submission.varifold_tangents_rh_mc_tendsto_integral_of_uniform N μ (s • K)
      (fun k y ↦ φ k (s⁻¹ • y)) (fun y ↦ g (s⁻¹ • y)) hμ (hK.smul s)
      (fun k ↦ ((hφ k).continuous.comp (continuous_const_smul s⁻¹)).integrable_of_hasCompactSupport
        ((hφc k).comp_smul hs'))
      ((hg.comp (continuous_const_smul s⁻¹)).integrable_of_hasCompactSupport (hgc.comp_smul hs'))
      (fun k y hy ↦ (hφK k _ (hsK y hy)).trans (hgK _ (hsK y hy)).symm)
      (fun ε hε ↦ (hunif ε hε).imp fun k₀ hk₀ k hk y ↦ hk₀ k hk (s⁻¹ • y))
  -- Step 6: by step 4 both limits are limits of the same sequence.
  exact tendsto_nhds_unique hlim2 ((hlim1.const_mul (s ^ n)).congr fun k ↦ (h4 k).symm)
/-- **Simon Ch. 8, 5.3 (p. 215), from integrals to sets** (child `dilation_riesz_sets` of the radial
homogeneity step for varifold tangents).  If `μ` is finite on compact sets, `s > 0` and
`∫ g(s⁻¹ y) dμ(y) = sⁿ ∫ g dμ` for every `g ∈ C_c(ℝ^N)`, then `μ(s A) = sⁿ μ(A)` for every set `A`:
the image of `μ` under `T y = s⁻¹ y` and `sⁿ μ` are regular and agree on `C_c`, so they are equal
by uniqueness in the Riesz representation theorem, and an image under a measurable equivalence is
evaluated exactly on every set, with `T⁻¹(A) = s A`. -/
theorem Submission.varifold_tangents_rh_measure_homogeneous :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (s : ℝ), IsFiniteMeasureOnCompacts μ → 0 < s → (∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → ∫ y, g (s⁻¹ • y) ∂μ = s ^ n * ∫ y, g y ∂μ) → ∀ A : Set (Euclidean N), μ (s • A) = ENNReal.ofReal s ^ n * μ A := by
  intro N n μ s hμ hs hg A
  -- Step 1: `T y = s⁻¹ • y` is a homeomorphism, hence a measurable equivalence.
  have hs₀ : s⁻¹ ≠ 0 := inv_ne_zero hs.ne'
  let T : Euclidean N ≃ᵐ Euclidean N := (Homeomorph.smulOfNeZero s⁻¹ hs₀).toMeasurableEquiv
  -- Step 2: `μ` is regular (locally finite on `ℝ^N`), hence so are `μ.map T` and `sⁿ μ`.
  have hc : ENNReal.ofReal s ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h₁ : (μ.map T).Regular := Measure.Regular.map (Homeomorph.smulOfNeZero s⁻¹ hs₀)
  have h₂ : (ENNReal.ofReal s ^ n • μ).Regular := Measure.Regular.smul hc
  -- Steps 3–4: both measures give `∫ f(s⁻¹ y) dμ = sⁿ ∫ f dμ` to every `f ∈ C_c`, so they are equal.
  have hν : μ.map T = ENNReal.ofReal s ^ n • μ := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_map_equiv, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs.le,
      smul_eq_mul]
    exact hg f f.continuous f.hasCompactSupport
  -- Step 5: `s • A = T⁻¹(A)` and `(μ.map T)(A) = μ(T⁻¹(A))` for every set `A`.
  have hA : s • A = T ⁻¹' A := (Set.preimage_smul_inv₀ hs.ne' A).symm
  rw [hA, ← MeasurableEquiv.map_apply T A, hν, Measure.smul_apply, smul_eq_mul]

/-- **Simon Ch. 8, 5.3 (p. 215), corrected**: radial homogeneity of a stationary varifold `C` on
`ℝ^N` with `y ∈ S` for `C`-a.e. `(y, S)`, namely `μ_C(s A) = sⁿ μ_C(A)` for every `s > 0` and
every set `A ⊆ ℝ^N` (the printed `λ^{-n} μ_C(η_{0,λ}(A)) = μ_C(A)` has the wrong power).  Testing
`δC = 0` against `g(y) y` gives Euler's identity `∫ (n g + Dg(y)(y)) dμ_C = 0`; this yields the
dilation law `∫ g(s⁻¹ y) dμ_C(y) = sⁿ ∫ g dμ_C` for `C¹_c` functions, mollification extends it to
`C_c`, and Riesz uniqueness turns it into the stated identity on all sets. -/
theorem Submission.varifold_tangents_radial_stationary_homogeneous :
    ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))), C.Stationary → (∀ᵐ z ∂C.measure, Grassmannian.project z.2 z.1 = z.1) → ∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A := by
  intro N n C hC hrad s A hs
  -- `μ_C` is finite on compact sets, since every compact set lies in the domain `ℝ^N`.
  have hfin : IsFiniteMeasureOnCompacts C.weight :=
    ⟨fun K hK ↦ lt_top_iff_ne_top.2 (C.weight_finite_on_compact K hK (subset_univ K))⟩
  -- Step 1: Euler's identity `∫ (n g + Dg(y)(y)) dμ_C = 0` for `g ∈ C¹_c`.
  have hH := Submission.varifold_tangents_rh_radial_euler_identity N n C hC hrad
  -- Step 2: the dilation law `∫ g(s⁻¹ y) dμ_C(y) = sⁿ ∫ g dμ_C` for `g ∈ C¹_c`.
  have hS1 := Submission.varifold_tangents_rh_scaling_of_euler_identity N n C.weight hfin hH
  -- Step 3: mollification extends the law to `C_c`; steps 4–5: Riesz uniqueness gives it on sets.
  exact Submission.varifold_tangents_rh_measure_homogeneous N n C.weight s hfin hs
    (Submission.varifold_tangents_rh_scaling_continuous N n C.weight s hfin hs
      fun g hg hgc ↦ hS1 g hg hgc s hs) A
/-- Restricting vague convergence to an open set (step B2 of the proof of Simon Ch. 8, 5.4): if
`μ_i → μ` as Radon measures on `Gₙ(ℝ^{n+ℓ})` and `W_i = c μ_i ⌞ Gₙ(Ω)`, `W = c μ ⌞ Gₙ(Ω)` are
varifolds on `Ω`, then `W_i → W` as Radon measures on `Gₙ(Ω)`. -/
theorem Submission.varifold_tangents_restricted_radon_converges :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (Ws : ℕ → Varifold N n Ω) (W : Varifold N n Ω) (c : ℝ≥0∞), VagueConverges μs μ → c ≠ ∞ → (∀ i, (Ws i).measure = c • (μs i).restrict (Ω ×ˢ (univ : Set (Grassmannian N n)))) → W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → Varifold.RadonConverges Ws W := by
  intro N n Ω μs μ Ws W c hμ _ hWs hW f
  -- Step 1: `P = Ω × G(N,n)` is open (`Ω` is the open domain of `W`), hence measurable.
  have hPopen : IsOpen (Ω ×ˢ (univ : Set (Grassmannian N n))) := W.isOpen_domain.prod isOpen_univ
  have hPmeas : MeasurableSet (Ω ×ˢ (univ : Set (Grassmannian N n))) := hPopen.measurableSet
  -- Step 2: the zero extension `F` of `f` is continuous with compact support on `ℝ^N × G(N,n)`;
  -- it agrees with `f` on `P` and vanishes off `P`.
  let F : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    { toFun := Subtype.val.extend f 0
      continuous_toFun :=
        HasCompactSupport.continuous_extend_zero hPopen f.continuous f.hasCompactSupport
      hasCompactSupport' := f.hasCompactSupport.extend_zero continuous_subtype_val }
  have hF : ∀ z : Ω ×ˢ (univ : Set (Grassmannian N n)), F z = f z :=
    Subtype.val_injective.extend_apply f 0
  have hF0 : ∀ x ∉ Ω ×ˢ (univ : Set (Grassmannian N n)), F x = 0 := fun x hx ↦
    Function.extend_apply' _ _ _ fun ⟨z, hz⟩ ↦ hx (hz ▸ z.2)
  -- Steps 3–4: `∫ f dZ_dom = c ∫ F dν` for every varifold `Z = c ν ⌞ P` on `Ω`.
  have key : ∀ (Z : Varifold N n Ω) (ν : Measure (Euclidean N × Grassmannian N n)),
      Z.measure = c • ν.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) →
        ∫ z, f z ∂Z.domainMeasure = c.toReal * ∫ x, F x ∂ν := by
    intro Z ν hZ
    calc ∫ z, f z ∂Z.domainMeasure = ∫ z, F z ∂Z.domainMeasure := by simp only [hF]
      _ = ∫ x, F x ∂Z.domainMeasure.map Subtype.val :=
        ((MeasurableEmbedding.subtype_coe hPmeas).integral_map _).symm
      _ = c.toReal * ∫ x in Ω ×ˢ (univ : Set (Grassmannian N n)), F x ∂ν := by
        rw [Z.map_domainMeasure, hZ, integral_smul_measure, smul_eq_mul]
      _ = c.toReal * ∫ x, F x ∂ν := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  -- Step 5: vague convergence tested on `F`, multiplied by the constant `c`.
  have hlim := (hμ F).const_mul c.toReal
  rw [← key W μ hW] at hlim
  exact hlim.congr fun i ↦ (key (Ws i) (μs i) (hWs i)).symm

/-- **Simon Ch. 8, the use of 3.7 in the proofs of 5.5 and 5.7** (child `density_lower_bound` of
`varifold_tangents`): if 5.1 holds at `x` and
`ρ^{-n} μ_V({y ∈ B_ρ(x) : Θ^n(μ_V, y) ≥ τ fails}) → 0`, then `Θ^n(μ_C, ·) ≥ τ` holds `μ_C`-a.e.
for every `C ∈ VarTan(V, x)`.  On each ball `Ω = B°_R(0)`, the varifolds
`W_i = τ⁻¹ V_{x,t_{j₀+i}} ⌞ (Ω × G)` converge to `τ⁻¹ C ⌞ (Ω × G)`.  For `O ⊂⊂ Ω` and
`ρ = t_{j₀+i} R`, `‖δW_i‖(O) = O(ρ^{1-n}‖δV‖(B_ρ(x))) → 0`.  Also `Θ^n(μ_{W_i}, y) ≥ 1` unless
`x + t_{j₀+i} y` lies in the bad set, whose `μ_{W_i}`-mass in `O` is
`O(ρ^{-n} μ_V(bad ∩ B_ρ(x))) → 0`.  So 3.7 gives density `≥ 1` a.e. for the limit `τ⁻¹ μ_C ⌞ Ω`,
i.e. `Θ^n(μ_C, ·) ≥ τ` `μ_C`-a.e. on `Ω`. -/
theorem Submission.varifold_tangents_density_lower_bound :
    DensitySemicontinuity → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ := by
  intro hsemi N n U V x τ hV hx hτ hvar hbad C hC
  obtain ⟨t, ht0, ht, hconv⟩ := hC
  -- `c = τ⁻¹ ∈ (0, ∞)` normalizes the density bound `τ` to `1`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, c = (ENNReal.ofReal τ)⁻¹ := ⟨_, rfl⟩
  have hτ0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ).ne'
  have hc0 : c ≠ 0 := by rw [hc]; exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hctop : c ≠ ∞ := by rw [hc]; exact ENNReal.inv_ne_top.2 hτ0
  have hc1 : c * ENNReal.ofReal τ = 1 := by
    rw [hc]; exact ENNReal.inv_mul_cancel hτ0 ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ = ENNReal.ofReal τ := by rw [hc, inv_inv]
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hx
  -- Step 0: it suffices to work on each ball `B°_R(0)`; the balls `B°_{k+1}(0)` exhaust `ℝ^N`.
  suffices key : ∀ R : ℝ, 0 < R → ∀ᵐ y ∂C.weight, y ∈ ball (0 : Euclidean N) R →
      ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ by
    filter_upwards [ae_all_iff.2 fun k : ℕ ↦ key ((k : ℝ) + 1) k.cast_add_one_pos] with y hy
    obtain ⟨k, hk⟩ := exists_nat_gt ‖y‖
    exact hy k (mem_ball_zero_iff.2 (hk.trans (lt_add_one _)))
  intro R hR
  -- Step 1: `t_j R → 0⁺`; choose `j₀` with `t_j R < ε` and `γ(t_j R) < 1` for `j ≥ j₀`, where
  -- `γ(ρ) = ρ^{1-n}‖δV‖(B_ρ(x))`.
  have htR : Tendsto (fun j ↦ t j * R) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using ht.mul_const R, .of_forall fun j ↦ mul_pos (ht0 j) hR⟩
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1
    ((htR.eventually (hvar.eventually (eventually_lt_nhds zero_lt_one))).and
      ((tendsto_nhdsWithin_iff.1 htR).1.eventually (eventually_lt_nhds hε)))
  have hTU : ∀ i : ℕ, closedBall x (t (i + j₀) * R) ⊆ U := fun i ↦
    (closedBall_subset_ball (hj₀ _ (Nat.le_add_left j₀ i)).2).trans hεU
  have hKR : ENNReal.ofReal 1 * (ENNReal.ofReal R ^ n / ENNReal.ofReal R) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.ofReal_pos.2 hR).ne')
  -- Step 3: `W_i = τ⁻¹ V_{x,t_{j₀+i}} ⌞ (Ω × G)` and `C' = τ⁻¹ C ⌞ (Ω × G)` are varifolds on `Ω`.
  have hWex : ∀ i : ℕ, ∃ W : Varifold N n (ball (0 : Euclidean N) R), W.measure =
      c • (rescaledMeasure V x (t (i + j₀))).restrict
        (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) := by
    intro i
    refine Submission.varifold_tangents_dlb_exists_restricted_varifold N n
      (ball (0 : Euclidean N) R) (rescaledMeasure V x (t (i + j₀))) c isOpen_ball hctop
      fun K _ hKR ↦ ne_top_of_le_ne_top ?_
        (measure_mono (prod_mono (hKR.trans ball_subset_closedBall) subset_rfl))
    rw [(Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ N n U V x (t (i + j₀))).2
      (ht0 _) 0 R, smul_zero, add_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (V.weight_finite_on_compact _ (isCompact_closedBall _ _) (hTU i))
  choose W hW using hWex
  obtain ⟨C', hC'⟩ := Submission.varifold_tangents_dlb_exists_restricted_varifold N n
    (ball (0 : Euclidean N) R) C.measure c isOpen_ball hctop fun K hK _ ↦
      C.finite_on_compact K hK (subset_univ K)
  -- Step 4: `W_i → C'` as Radon measures on `Gₙ(Ω)`.
  have hRadon : Varifold.RadonConverges W C' :=
    Submission.varifold_tangents_restricted_radon_converges N n (ball (0 : Euclidean N) R)
      (fun i ↦ rescaledMeasure V x (t (i + j₀))) C.measure W C' c
      (fun f ↦ (hconv f).comp (tendsto_add_atTop_nat j₀)) hctop hW hC'
  -- Step 5: `‖δW_i‖(O) ≤ τ⁻¹ (R^n / R) γ(t_{j₀+i} R) → 0` for `O ⊂⊂ Ω`.
  have hFV : ∀ i : ℕ, (W i).HasLocallyBoundedFirstVariation ∧
      ∀ O : Set (Euclidean N), IsRelCompactOpenIn O (ball (0 : Euclidean N) R) →
        variationMeasure (W i) O ≤ c * (ENNReal.ofReal 1 *
          (ENNReal.ofReal R ^ n / ENNReal.ofReal R) * (ENNReal.ofReal (t (i + j₀) * R) *
            variationMeasure V (closedBall x (t (i + j₀) * R)) /
              ENNReal.ofReal (t (i + j₀) * R) ^ n)) := fun i ↦
    Submission.varifold_tangents_dlb_restricted_firstVariation_control N n
      (ball (0 : Euclidean N) R) (rescaledMeasure V x (t (i + j₀))) (W i) c _ hctop
      (ENNReal.mul_ne_top hKR (ne_top_of_lt (hj₀ _ (Nat.le_add_left j₀ i)).1)) (hW i)
      fun X hX hXc hXR hX1 ↦ Submission.varifold_tangents_rescaled_divergence_bound N n U V x
        (t (i + j₀)) R 1 X hV (ht0 _) hR (hTU i) hX hXc hXR hX1
  have hβ : Tendsto (fun i : ℕ ↦ c * (ENNReal.ofReal 1 *
      (ENNReal.ofReal R ^ n / ENNReal.ofReal R) * (ENNReal.ofReal (t (i + j₀) * R) *
        variationMeasure V (closedBall x (t (i + j₀) * R)) /
          ENNReal.ofReal (t (i + j₀) * R) ^ n))) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
      ((hvar.comp htR).comp (tendsto_add_atTop_nat j₀)) (Or.inr hKR)) (Or.inr hctop)
    rw [mul_zero, mul_zero] at h
    exact h
  have hliminf : ∀ O : Set (Euclidean N), IsRelCompactOpenIn O (ball (0 : Euclidean N) R) →
      liminf (fun i ↦ variationMeasure (W i) O) atTop ≠ ∞ := by
    intro O hO
    rw [(tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hβ (fun _ ↦ zero_le)
      fun i ↦ (hFV i).2 O hO).liminf_eq]
    exact ENNReal.zero_ne_top
  -- Step 6: `Θ^n(μ_{W_i}, y) ≥ 1` unless `x + t_{j₀+i} y` lies in the bad set.
  have hdens : ∀ i : ℕ, ∀ y ∈ ball (0 : Euclidean N) R \ {y | x + t (i + j₀) • y ∈
      {z | ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight z θ ∧ ENNReal.ofReal τ ≤ θ}},
      ∃ θ : ℝ≥0∞, HasDensity n (W i).weight y θ ∧ 1 ≤ θ := by
    rintro i y ⟨hyR, hyE⟩
    simp only [mem_ofPred_eq, not_not] at hyE
    obtain ⟨θ, hθ, hτθ⟩ := hyE
    exact ⟨c * θ, Submission.varifold_tangents_dlb_restricted_hasDensity N n U V x (t (i + j₀)) R
      c θ (W i) y (ht0 _) hctop (hW i) hyR hθ, hc1.symm.le.trans (mul_le_mul_right hτθ c)⟩
  -- Step 7: `μ_{W_i}(bad ∩ O) ≤ τ⁻¹ R^n e(t_{j₀+i} R) → 0`, where
  -- `e(ρ) = ρ^{-n} μ_V(bad ∩ B_ρ(x))`.
  have hbadW : ∀ O : Set (Euclidean N), IsRelCompactOpenIn O (ball (0 : Euclidean N) R) →
      Tendsto (fun i ↦ (W i).weight ({y | x + t (i + j₀) • y ∈
        {z | ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight z θ ∧ ENNReal.ofReal τ ≤ θ}} ∩ O)) atTop
        (𝓝 0) := by
    intro O hO
    have h := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
      ((hbad.comp htR).comp (tendsto_add_atTop_nat j₀))
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top : ENNReal.ofReal R ^ n ≠ ∞)))
      (Or.inr hctop)
    rw [mul_zero, mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
      fun i ↦ Submission.varifold_tangents_dlb_restricted_bad_set_weight_le N n U V x
        (t (i + j₀)) R c (W i) _ O (ht0 _) hR (hW i) (subset_closure.trans hO.2.2)
  -- Step 8: semicontinuity 3.7 on `Ω` gives `Θ^n(μ_{C'}, ·) ≥ 1` `μ_{C'}`-a.e.
  obtain ⟨-, -, hC'ae⟩ := hsemi N n (ball (0 : Euclidean N) R) W C'
    (fun i ↦ {y | x + t (i + j₀) • y ∈
      {z | ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight z θ ∧ ENNReal.ofReal τ ≤ θ}})
    hRadon (fun i ↦ (hFV i).1) hliminf hdens hbadW
  -- Step 9: transfer back to `C` on `Ω`, multiplying the density by `c⁻¹ = τ`.
  have h := Submission.varifold_tangents_dlb_ae_hasDensity_of_restricted N n univ
    (ball (0 : Euclidean N) R) C C' c hc0 hctop hC' hC'ae
  rwa [hcinv] at h
/-- **Simon Ch. 8, Remark 3.8(1), p. 211** (child `variation_lsc` of `density_semicontinuity`): if
`V_i → V` as Radon measures on `Gₙ(U)`, every `V_i` has locally bounded first variation and
`liminf_i ‖δV_i‖(W) < ∞` for each open `W ⊂⊂ U`, then `V` has locally bounded first variation and
`‖δV‖(W) ≤ liminf_i ‖δV_i‖(W)` for each open `W ⊂⊂ U`.  On such `W`, `‖δX‖(W)` is the supremum of
2.5 (`firstVariationNormOn`), which is lower semicontinuous because `δV_i(X) → δV(X)`. -/
theorem Submission.variationMeasure_le_liminf_of_radonConverges :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U),
      Varifold.RadonConverges Vi V → (∀ i, (Vi i).HasLocallyBoundedFirstVariation) →
      (∀ W, IsRelCompactOpenIn W U → liminf (fun i ↦ variationMeasure (Vi i) W) atTop ≠ ∞) →
      V.HasLocallyBoundedFirstVariation ∧ ∀ W, IsRelCompactOpenIn W U →
        variationMeasure V W ≤ liminf (fun i ↦ variationMeasure (Vi i) W) atTop := by
  intro N n U Vi V h hi hbound
  -- Under local boundedness `variationMeasure` is the Riesz measure, which equals the supremum
  -- of 2.5 on every `W ⊂⊂ U`.
  have hnorm : ∀ X : Varifold N n U, X.HasLocallyBoundedFirstVariation →
      ∀ W, IsRelCompactOpenIn W U → variationMeasure X W = X.firstVariationNormOn W := by
    intro X hX W hW
    rw [variationMeasure, dite_eq_left hX]
    exact X.firstVariationRieszMeasure_eq_norm hX W hW.1 hW.2
  have hlim : ∀ W, IsRelCompactOpenIn W U →
      liminf (fun i ↦ variationMeasure (Vi i) W) atTop =
        liminf (fun i ↦ (Vi i).firstVariationNormOn W) atTop := fun W hW ↦
    congrArg (liminf · atTop) (funext fun i ↦ hnorm (Vi i) (hi i) W hW)
  have hV : V.HasLocallyBoundedFirstVariation :=
    h.hasLocallyBoundedFirstVariation fun W hW hWU ↦ by
      rw [← hlim W ⟨hW, hWU⟩]
      exact hbound W ⟨hW, hWU⟩
  refine ⟨hV, fun W hW ↦ ?_⟩
  rw [hnorm V hV W hW, hlim W hW]
  exact h.firstVariationNormOn_le_liminf W
/-- **Simon Ch. 8, proof of 3.7, p. 212, choice of `ρ₀` and `W̃`** (child `thickening_rel_compact`
of `lower_density_ae`): if `W ⊂⊂ U` then `W̃ = {x : dist(x, W) < ρ₀} ⊂⊂ U` for some `ρ₀ > 0`.
The compact set `closure W` has a closed thickening `cthickening ρ₀ (closure W) ⊆ U`; it is compact
(`ℝ^N` is proper) and contains `closure W̃ ⊆ cthickening ρ₀ W = cthickening ρ₀ (closure W)`. -/
theorem Submission.exists_thickening_isRelCompactOpenIn :
    ∀ (N : ℕ) (U W : Set (Euclidean N)), IsOpen U → IsRelCompactOpenIn W U →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ IsRelCompactOpenIn (thickening ρ₀ W) U := by
  intro N U W hU hW
  obtain ⟨-, hWc, hWU⟩ := hW
  -- Some closed thickening of the compact set `closure W ⊆ U` still lies in the open set `U`.
  obtain ⟨δ, hδ, hδU⟩ := hWc.exists_cthickening_subset_open hU hWU
  -- `closure (thickening δ W) ⊆ cthickening δ W = cthickening δ (closure W)`.
  have hcl : closure (thickening δ W) ⊆ cthickening δ (closure W) := by
    rw [cthickening_closure]
    exact closure_thickening_subset_cthickening δ W
  exact ⟨δ, hδ, isOpen_thickening, hWc.cthickening.of_isClosed_subset isClosed_closure hcl,
    hcl.trans hδU⟩
/-- **Simon Ch. 8, proof of 3.7, p. 213, final step** (child `relcompact_exhaustion_ae` of
`lower_density_ae`): the book proves the density bound on one `W ⊂⊂ U` off a `μ`-null set ((4),
(5)); this passes to `μ`-a.e. point.  If `μ(ℝ^N ∖ U) = 0` and `P` holds on each `W ⊂⊂ U` off a
`μ`-null set, then `P` holds `μ`-a.e.: each `x ∈ U` has a ball `W_x = B°_{r_x}(x) ⊂⊂ U`, countably
many `W_x` cover `U` (`ℝ^N` is second countable), and `{¬P} ⊆ Uᶜ ∪ ⋃_{x ∈ T} E_x` is `μ`-null.
No measurability of `P` or of the exceptional sets is used. -/
theorem Submission.ae_of_forall_relCompactOpen_null_exceptional :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N)) (P : Euclidean N → Prop),
      IsOpen U → μ Uᶜ = 0 →
      (∀ W : Set (Euclidean N), IsRelCompactOpenIn W U →
        ∃ E : Set (Euclidean N), μ E = 0 ∧ ∀ x ∈ W, x ∉ E → P x) →
      ∀ᵐ x ∂μ, P x := by
  intro N U μ P hU hUc hP
  -- Step 1: each `x ∈ U` has a radius `r x > 0` with `B_{r x}(x) ⊆ U`.
  have hr : ∀ x : U, ∃ r : ℝ, 0 < r ∧ closedBall (x : Euclidean N) r ⊆ U := by
    intro x
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x x.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose r hr0 hrU using hr
  -- Step 2: `W_x = B°_{r x}(x) ⊂⊂ U`, since `closure W_x ⊆ B_{r x}(x) ⊆ U` and closed balls are
  -- compact.
  have hW : ∀ x : U, IsRelCompactOpenIn (ball (x : Euclidean N) (r x)) U := fun x ↦
    ⟨isOpen_ball, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, closure_ball_subset_closedBall.trans (hrU x)⟩
  -- Step 3: countably many `W_x` (`x ∈ T`) have the same union as all of them, which contains `U`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U ↦ ball (x : Euclidean N) (r x)) fun _ ↦ isOpen_ball
  -- Step 4: a `μ`-null exceptional set `E x` for each `W_x`.
  choose E hE0 hEP using fun x : U ↦ hP _ (hW x)
  -- Steps 5–7: `{¬P} ⊆ Uᶜ ∪ ⋃_{x ∈ T} E x`, which is `μ`-null.
  rw [ae_iff]
  refine measure_mono_null (t := Uᶜ ∪ ⋃ x ∈ T, E x) ?_
    (measure_union_null hUc ((measure_biUnion_null_iff hTc).2 fun x _ ↦ hE0 x))
  intro y hy
  by_cases hyU : y ∈ U
  · have hyT : y ∈ ⋃ x ∈ T, ball (x : Euclidean N) (r x) := by
      rw [hTU]
      exact mem_iUnion.2 ⟨⟨y, hyU⟩, mem_ball_self (hr0 _)⟩
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 hyT
    refine Or.inr (mem_iUnion₂.2 ⟨x, hxT, ?_⟩)
    by_contra hyE
    exact hy (hEP x y hyx hyE)
  · exact Or.inl hyU
/-- **Simon Ch. 8, proof of 3.7, pp. 212–213, displays (3) and (5)** (child `bad_interior_null` of
`lower_density_ae`): suppose `μ(O) ≤ liminf_q μ_q(O)` for every open `O ⊆ W`, and the sets
`Bad q k ⊆ W` satisfy `μ_q(Bad q k) ≤ C k⁻¹ a_q + b_q` for `k ≥ 1`, with `liminf_q a_q < ∞` and
`b_q → 0`.  Then `⋂_{k ≥ 1} ⋃_i interior (⋂_{ℓ ≥ i} Bad ℓ k)` is `μ`-null.  The open set
`O_{i,k} = interior (⋂_{ℓ ≥ i} Bad ℓ k)` lies in `Bad q k` for every `q ≥ i`, so
`μ(O_{i,k}) ≤ C k⁻¹ liminf_q a_q` (printed (3)).  As `O_{i,k}` increases in `i`, the exceptional set
has measure `≤ C k⁻¹ liminf_q a_q` for every `k ≥ 1` (printed (5)), and this bound tends to `0`. -/
theorem Submission.measure_bad_interior_exceptional_eq_zero :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (μs : ℕ → Measure (Euclidean N)) (W : Set (Euclidean N)) (Bad : ℕ → ℕ → Set (Euclidean N)) (C : ℕ) (a b : ℕ → ℝ≥0∞), (∀ O : Set (Euclidean N), IsOpen O → O ⊆ W → μ O ≤ liminf (fun q ↦ μs q O) atTop) → (∀ q k, Bad q k ⊆ W) → liminf a atTop ≠ ∞ → Tendsto b atTop (𝓝 0) → (∀ q k : ℕ, 1 ≤ k → μs q (Bad q k) ≤ (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * a q + b q) → μ (⋂ k : ℕ, ⋂ (_ : 1 ≤ k), ⋃ i : ℕ, interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) = 0 := by
  intro N μ μs W Bad C a b hP1 hW hL hb hbad
  -- Step 1: `O i k = interior (⋂_{ℓ ≥ i} Bad ℓ k)` is in `Bad ℓ k` for `ℓ ≥ i`, and grows with `i`.
  have hO_sub : ∀ i k ℓ, i ≤ ℓ → interior (⋂ ℓ' : ℕ, ⋂ (_ : i ≤ ℓ'), Bad ℓ' k) ⊆ Bad ℓ k :=
    fun i k ℓ hℓ ↦ interior_subset.trans (iInter₂_subset ℓ hℓ)
  have hO_mono : ∀ k, Monotone fun i ↦ interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k) :=
    fun k i i' hii' ↦ interior_mono (subset_iInter₂ fun ℓ hℓ ↦ iInter₂_subset ℓ (hii'.trans hℓ))
  -- Step 2 (printed (3)): `μ(O i k) ≤ liminf_q μ_q(O i k) ≤ liminf_q (C k⁻¹ a_q + b_q)`
  -- `= liminf_q (C k⁻¹ a_q) = C k⁻¹ liminf_q a_q`, using `C k⁻¹ ≠ ∞` and `b_q → 0`.
  have hstep2 : ∀ i k, 1 ≤ k →
      μ (interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) ≤
        (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * liminf a atTop := by
    intro i k hk
    have hc : (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top C)
        (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (by omega)))
    calc μ (interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k))
        ≤ liminf (fun q ↦ μs q (interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k))) atTop :=
          hP1 _ isOpen_interior ((hO_sub i k i le_rfl).trans (hW i k))
      _ ≤ liminf (fun q ↦ (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * a q + b q) atTop :=
          liminf_le_liminf <| (eventually_ge_atTop i).mono fun q hq ↦
            (measure_mono (hO_sub i k q hq)).trans (hbad q k hk)
      _ = liminf (fun q ↦ (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * a q) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero hb _
      _ = (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * liminf a atTop := ENNReal.liminf_const_mul_of_ne_top hc
  -- Step 3 (printed (5)): for `k ≥ 1` the exceptional set lies in `⋃_i O i k`, whose measure is
  -- `⨆_i μ(O i k)` by continuity from below.
  have hstep3 : ∀ k : ℕ, 1 ≤ k →
      μ (⋂ k : ℕ, ⋂ (_ : 1 ≤ k), ⋃ i : ℕ, interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) ≤
        (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * liminf a atTop := fun k hk ↦
    calc _ ≤ μ (⋃ i : ℕ, interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) :=
          measure_mono (iInter₂_subset k hk)
      _ = ⨆ i, μ (interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) := (hO_mono k).measure_iUnion
      _ ≤ _ := iSup_le fun i ↦ hstep2 i k hk
  -- Step 4: `C k⁻¹ liminf_q a_q → C · 0 · liminf_q a_q = 0`, as `C ≠ ∞` and `liminf_q a_q ≠ ∞`.
  have hstep4 : Tendsto (fun k : ℕ ↦ (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * liminf a atTop) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top C))) (Or.inr hL)
    rwa [mul_zero, zero_mul] at h
  -- Step 5: the measure is eventually below a sequence tending to `0`, so it is `0`.
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hstep4 ((eventually_ge_atTop 1).mono hstep3))
/-- Choice of `y_i`, `q_i` in the proof of 3.7 (Simon Ch. 8, p. 212, before (4)): if `x ∈ W` with
`W` open and `x ∉ interior (⋂_{ℓ ≥ i} Bad ℓ)` for every `i`, then there are `y_i → x` in `W` and
`q_i → ∞` with `y_i ∉ Bad (q_i)`. -/
theorem Submission.exists_nearby_points_off_bad_sets :
    ∀ (N : ℕ) (W : Set (Euclidean N)) (Bad : ℕ → Set (Euclidean N)) (x : Euclidean N), IsOpen W → x ∈ W → (∀ i : ℕ, x ∉ interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ)) → ∃ (q : ℕ → ℕ) (y : ℕ → Euclidean N), Tendsto q atTop atTop ∧ Tendsto y atTop (𝓝 x) ∧ ∀ i, y i ∈ W ∧ y i ∉ Bad (q i) := by
  intro N W Bad x hW hxW hx
  -- Steps 1–2: for each `i`, the open neighbourhood `W ∩ B_{1/(i+1)}(x)` of `x` is not contained
  -- in `⋂_{ℓ ≥ i} Bad ℓ` (else `x` would be in its interior), so it has a point off some `Bad ℓ`.
  have key : ∀ i : ℕ, ∃ ℓ : ℕ, ∃ z : Euclidean N,
      i ≤ ℓ ∧ z ∈ W ∧ dist z x < 1 / ((i : ℝ) + 1) ∧ z ∉ Bad ℓ := by
    intro i
    by_contra hcon
    push Not at hcon
    apply hx i
    have hsub : W ∩ ball x (1 / ((i : ℝ) + 1)) ⊆ ⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ := by
      intro z hz
      simp only [mem_iInter]
      intro ℓ hℓ
      exact hcon ℓ z hℓ hz.1 (mem_ball.1 hz.2)
    exact interior_maximal hsub (hW.inter isOpen_ball) ⟨hxW, mem_ball_self (by positivity)⟩
  -- Step 3: choose `q i ≥ i` and `y i` for every `i`.
  choose q y hq hyW hyx hyBad using key
  refine ⟨q, y, ?_, ?_, fun i ↦ ⟨hyW i, hyBad i⟩⟩
  -- Step 4: `q i ≥ i`, so `q i → ∞`.
  · exact tendsto_atTop_mono hq tendsto_id
  -- Step 5: `0 ≤ dist (y i) x < 1/(i+1) → 0`, so `y i → x`.
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun i ↦ dist_nonneg) (fun i ↦ (hyx i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
/-- Radon convergence of varifolds gives vague convergence of their weights on `U` (Simon Ch. 8,
proof of 3.7): if `V_i → V` as Radon measures on `Gₙ(U)` and `g ∈ C_c(ℝ^N)` has `spt g ⊆ U`, then
`∫ g dμ_{V_i} → ∫ g dμ_V`. -/
theorem Submission.varifold_weight_integral_tendsto_of_radonConverges :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U), Varifold.RadonConverges Vi V → ∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Tendsto (fun i ↦ ∫ x, g x ∂(Vi i).weight) atTop (𝓝 (∫ x, g x ∂V.weight)) := by
  intro N n U Vi V hconv g hg hgc hgU
  -- Step 1: the lift `F z = g z.1.1` of `g` to Simon's open product `Gₙ(U)`.
  let Ω := U ×ˢ (univ : Set (Grassmannian N n))
  -- Step 2: `F` vanishes off the compact set `ι⁻¹(spt g × G(N,n))`, so `F ∈ C_c(Gₙ(U))`.
  let F : C_c(Ω, ℝ) :=
    { toFun := fun z ↦ g z.1.1
      continuous_toFun := hg.comp (continuous_fst.comp continuous_subtype_val)
      hasCompactSupport' := by
        have hK : IsCompact ((Subtype.val : Ω → Euclidean N × Grassmannian N n) ⁻¹'
            (tsupport g ×ˢ (univ : Set (Grassmannian N n)))) :=
          Topology.IsInducing.subtypeVal.isCompact_preimage' (hgc.isCompact.prod isCompact_univ)
            (by
              intro z hz
              exact ⟨⟨z, hgU hz.1, mem_univ _⟩, rfl⟩)
        refine HasCompactSupport.intro hK fun z hz ↦ ?_
        exact image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨h, mem_univ _⟩ }
  -- Step 3: `∫ F dX = ∫ g(p.1) dX.measure(p) = ∫ g dμ_X` for every varifold `X` on `U`.
  have hdom : ∀ X : Varifold N n U, ∫ z, F z ∂X.domainMeasure = ∫ x, g x ∂X.weight := by
    intro X
    rw [Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable,
      ← X.map_domainMeasure, (MeasurableEmbedding.subtype_coe
        (X.isOpen_domain.measurableSet.prod MeasurableSet.univ)).integral_map]
    rfl
  -- Step 4: apply `RadonConverges` to `F` and rewrite both sides with step 3.
  simpa only [hdom] using hconv F
/-- Urysohn sandwich (Simon Ch. 8, proof of 3.7): for compact `K` inside open `O` there is one
continuous `g` with compact support in `O` such that `ν(K) ≤ ∫ g dν ≤ ν(O)` for every measure
`ν` that is finite on compact subsets of `O`. -/
theorem Submission.exists_urysohn_integral_sandwich :
    ∀ (N : ℕ) (K O : Set (Euclidean N)), IsCompact K → IsOpen O → K ⊆ O → ∃ g : Euclidean N → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ O ∧ ∀ ν : Measure (Euclidean N), (∀ L : Set (Euclidean N), IsCompact L → L ⊆ O → ν L ≠ ∞) → ν K ≤ ENNReal.ofReal (∫ x, g x ∂ν) ∧ ENNReal.ofReal (∫ x, g x ∂ν) ≤ ν O := by
  intro N K O hK hO hKO
  -- Step 1: a compact buffer `L` with `K ⊆ interior L` and `L ⊆ O`.
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between hK hO hKO
  -- Step 2: Urysohn's lemma: `g = 1` on `K`, `g = 0` off `interior L`, `0 ≤ g ≤ 1`.
  obtain ⟨g, hg1, hg0, hgc, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKL)
  -- Step 3: `tsupport g ⊆ L ⊆ O`, as `support g ⊆ interior L` and `L` is closed.
  have hgL : tsupport g ⊆ L := by
    refine closure_minimal (fun x hx ↦ ?_) hL.isClosed
    by_contra hxL
    exact hx (hg0 fun hx' ↦ hxL (interior_subset hx'))
  refine ⟨g, g.continuous, hgc, hgL.trans hLO, fun ν hν ↦ ?_⟩
  -- Steps 4–5: `ν L < ∞` and `|g| ≤ 1` with `support g ⊆ L`, so `g` is `ν`-integrable.
  have hint : Integrable g ν := by
    rw [← integrableOn_iff_integrable_of_support_subset ((subset_tsupport g).trans hgL)]
    refine Measure.integrableOn_of_bounded (M := 1) (hν L hL hLO)
      g.continuous.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hg01 x).1], (hg01 x).2⟩
  -- Step 6: `g ≥ 0`, so `ofReal (∫ g dν) = ∫⁻ ofReal ∘ g dν`.
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ (hg01 x).1)]
  -- Steps 7–8: integrate `1_K ≤ ofReal ∘ g ≤ 1_O` (`K` closed and `O` open are measurable).
  constructor
  · rw [← lintegral_indicator_one hK.isClosed.measurableSet]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ K
    · simp [hx, hg1 hx]
    · simp [hx]
  · rw [← lintegral_indicator_one hO.measurableSet]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ O
    · simpa [hx] using (hg01 x).2
    · simp [hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hLO (hgL h))]

/-- Portmanteau (P1) for vague convergence (Simon Ch. 8, proof of 3.7): if `∫ g dμᵢ → ∫ g dμ` for
every continuous compactly supported `g` with support in `U`, and all measures are finite on
compact subsets of `U`, then `μ(O) ≤ liminf μᵢ(O)` for every open `O ⊆ U`. -/
theorem Submission.measure_open_le_liminf_of_tendsto_integral :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N)) (μ : Measure (Euclidean N)), (∀ (i : ℕ) (K : Set (Euclidean N)), IsCompact K → K ⊆ U → μs i K ≠ ∞) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Tendsto (fun i ↦ ∫ x, g x ∂(μs i)) atTop (𝓝 (∫ x, g x ∂μ))) → ∀ O : Set (Euclidean N), IsOpen O → O ⊆ U → μ O ≤ liminf (fun i ↦ μs i O) atTop := by
  intro N U μs μ hμs hμ hlim O hO hOU
  -- Step 1: closed sets `F m ⊆ O`, increasing in `m`, with union `O`.
  obtain ⟨F, hFc, hFO, hFU, hFm⟩ := hO.exists_iUnion_isClosed
  -- Step 2: the compact sets `K m = F m ∩ B_m(0)` are increasing and lie in `O`.
  let K : ℕ → Set (Euclidean N) := fun m ↦ F m ∩ closedBall 0 m
  have hKc : ∀ m, IsCompact (K m) := fun m ↦ (isCompact_closedBall 0 m).inter_left (hFc m)
  have hKO : ∀ m, K m ⊆ O := fun m ↦ inter_subset_left.trans (hFO m)
  have hKm : Monotone K := fun a b hab ↦
    inter_subset_inter (hFm hab) (closedBall_subset_closedBall (Nat.cast_le.mpr hab))
  -- Step 3: `⋃ m, K m = O`.
  have hKU : ⋃ m, K m = O := by
    refine Subset.antisymm (iUnion_subset hKO) fun x hx ↦ ?_
    rw [← hFU] at hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.mpr ⟨max a b, hFm (le_max_left a b) ha, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hb.trans (Nat.cast_le.mpr (le_max_right a b))
  -- Step 4: `μ(O) = ⨆ m, μ(K m)`, so it suffices to bound each `μ(K m)`.
  have hμO : μ O = ⨆ m, μ (K m) := by
    rw [← hKU]
    exact hKm.measure_iUnion
  rw [hμO]
  refine iSup_le fun m ↦ ?_
  -- Step 5: the Urysohn sandwich function for `K m ⊆ O`; every `μᵢ` and `μ` is admissible.
  obtain ⟨g, hgc, hgs, hgO, hg⟩ :=
    Submission.exists_urysohn_integral_sandwich N (K m) O (hKc m) hO (hKO m)
  -- Step 6: `ofReal (∫ g dμᵢ) → ofReal (∫ g dμ)`.
  have ht : Tendsto (fun i ↦ ENNReal.ofReal (∫ x, g x ∂(μs i))) atTop
      (𝓝 (ENNReal.ofReal (∫ x, g x ∂μ))) :=
    ENNReal.tendsto_ofReal (hlim g hgc hgs (hgO.trans hOU))
  -- Step 7: `μ(K m) ≤ ofReal ∫ g dμ = liminf ofReal ∫ g dμᵢ ≤ liminf μᵢ(O)`.
  calc μ (K m) ≤ ENNReal.ofReal (∫ x, g x ∂μ) :=
        (hg μ fun L hL hLO ↦ hμ L hL (hLO.trans hOU)).1
    _ = liminf (fun i ↦ ENNReal.ofReal (∫ x, g x ∂(μs i))) atTop := ht.liminf_eq.symm
    _ ≤ liminf (fun i ↦ μs i O) atTop := liminf_le_liminf (Eventually.of_forall fun i ↦
        (hg (μs i) fun L hL hLO ↦ hμs i L hL (hLO.trans hOU)).2)
/-- Compact-set half of the portmanteau theorem (Simon Ch. 8, proof of 3.7): if `μ_i` and `μ` are
finite on compact subsets of the open set `U` and `∫ g dμ_i → ∫ g dμ` for every continuous `g` with
compact support in `U`, then `limsup_i μ_i(K) ≤ μ(K)` for every compact `K ⊆ U`. -/
theorem Submission.limsup_measure_compact_le_of_tendsto_integral :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N)) (μ : Measure (Euclidean N)), IsOpen U → (∀ (i : ℕ) (K : Set (Euclidean N)), IsCompact K → K ⊆ U → μs i K ≠ ∞) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Tendsto (fun i ↦ ∫ x, g x ∂(μs i)) atTop (𝓝 (∫ x, g x ∂μ))) → ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → limsup (fun i ↦ μs i K) atTop ≤ μ K := by
  intro N U μs μ hU hμs hμ hconv K hK hKU
  -- Step 1: a closed thickening `cthickening δ K` of `K` lies in `U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: radii `r m = δ / (m + 1)` and neighbourhoods `O m = thickening (r m) K`.
  set r : ℕ → ℝ := fun m ↦ δ / (m + 1)
  have hr_pos : ∀ m, 0 < r m := fun m ↦ div_pos hδ (Nat.cast_add_one_pos m)
  have hr_le : ∀ m, r m ≤ δ := fun m ↦
    div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg m))
  have hr_anti : Antitone r := fun m m' hmm' ↦
    div_le_div_of_nonneg_left hδ.le (Nat.cast_add_one_pos m) (by gcongr)
  set O : ℕ → Set (Euclidean N) := fun m ↦ thickening (r m) K
  -- (a) `O m` is open and contains `K`; (b) `O m ⊆ U`; (c) `O` is decreasing.
  have hO_open : ∀ m, IsOpen (O m) := fun m ↦ isOpen_thickening
  have hKO : ∀ m, K ⊆ O m := fun m ↦ self_subset_thickening (hr_pos m) K
  have hOU : ∀ m, O m ⊆ U := fun m ↦
    (thickening_subset_cthickening_of_le (hr_le m) K).trans hδU
  have hO_anti : Antitone O := fun m m' h ↦ thickening_mono (hr_anti h) K
  -- (d) `⋂ m, O m = closure K = K`.
  have hO_inter : ⋂ m, O m = K := by
    refine Subset.antisymm (fun x hx ↦ ?_) (subset_iInter hKO)
    rw [mem_iInter] at hx
    have hxcl : x ∈ closure K := by
      rw [closure_eq_iInter_thickening]
      simp only [mem_iInter]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_gt (δ / ε)
      have hrε : r m < ε := by
        rw [div_lt_iff₀ hε] at hm
        show δ / (m + 1) < ε
        rw [div_lt_iff₀ (Nat.cast_add_one_pos m)]
        nlinarith
      exact thickening_mono hrε.le K (hx m)
    rwa [hK.isClosed.closure_eq] at hxcl
  -- (e) `μ (O 0) ≤ μ (cthickening δ K) < ∞`, since `cthickening δ K` is a compact subset of `U`.
  have hO0 : μ (O 0) ≠ ∞ :=
    ne_top_of_le_ne_top (hμ _ hK.cthickening hδU)
      (measure_mono (thickening_subset_cthickening_of_le (hr_le 0) K))
  -- Step 3: continuity from above gives `μ (O m) → μ K`.
  have htend : Tendsto (fun m ↦ μ (O m)) atTop (𝓝 (μ K)) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun m ↦ (hO_open m).measurableSet.nullMeasurableSet) hO_anti ⟨0, hO0⟩
    rwa [hO_inter] at h
  -- Steps 4–6: `limsup_i μ_i(K) ≤ μ(O m)` for each `m`.
  have key : ∀ m, limsup (fun i ↦ μs i K) atTop ≤ μ (O m) := by
    intro m
    -- Step 4: the sandwich function for `K ⊆ O m`; each `μ_i` and `μ` is admissible as `O m ⊆ U`.
    obtain ⟨g, hgc, hgcs, hgO, hg⟩ :=
      Submission.exists_urysohn_integral_sandwich N K (O m) hK (hO_open m) (hKO m)
    have hfin : ∀ ν : Measure (Euclidean N), (∀ L, IsCompact L → L ⊆ U → ν L ≠ ∞) →
        ∀ L, IsCompact L → L ⊆ O m → ν L ≠ ∞ :=
      fun ν hν L hL hLO ↦ hν L hL (hLO.trans (hOU m))
    -- Step 5: `tsupport g ⊆ O m ⊆ U`, so `ofReal (∫ g dμ_i) → ofReal (∫ g dμ)`.
    have hlim := ENNReal.tendsto_ofReal (hconv g hgc hgcs (hgO.trans (hOU m)))
    -- Step 6: `limsup_i μ_i(K) ≤ limsup_i ofReal (∫ g dμ_i) = ofReal (∫ g dμ) ≤ μ(O m)`.
    calc limsup (fun i ↦ μs i K) atTop
        ≤ limsup (fun i ↦ ENNReal.ofReal (∫ x, g x ∂(μs i))) atTop :=
          limsup_le_limsup (Eventually.of_forall fun i ↦ (hg (μs i) (hfin _ (hμs i))).1)
      _ = ENNReal.ofReal (∫ x, g x ∂μ) := hlim.limsup_eq
      _ ≤ μ (O m) := (hg μ (hfin μ hμ)).2
  -- Step 7: let `m → ∞`.
  exact ge_of_tendsto' htend key

/-- Portmanteau for varifold weights (Simon Ch. 8, proof of 3.7): if `Vᵢ → V` as Radon measures on
`Gₙ(U)`, then `μ_V(O) ≤ liminf μ_{Vᵢ}(O)` for every open `O ⊆ U` and
`limsup μ_{Vᵢ}(K) ≤ μ_V(K)` for every compact `K ⊆ U`. -/
theorem Submission.weight_portmanteau_of_radonConverges :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U), Varifold.RadonConverges Vi V → (∀ O : Set (Euclidean N), IsOpen O → O ⊆ U → V.weight O ≤ liminf (fun i ↦ (Vi i).weight O) atTop) ∧ ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → limsup (fun i ↦ (Vi i).weight K) atTop ≤ V.weight K := by
  intro N n U Vi V hconv
  -- Step 1 (T): `∫ g dμ_{Vᵢ} → ∫ g dμ_V` for every `g ∈ C_c(ℝ^N)` with `spt g ⊆ U`.
  have hlim := Submission.varifold_weight_integral_tendsto_of_radonConverges N n U Vi V hconv
  -- Step 2: every weight is finite on compact subsets of `U`.
  have hfin : ∀ (X : Varifold N n U) (K : Set (Euclidean N)), IsCompact K → K ⊆ U →
      X.weight K ≠ ∞ := fun X ↦ X.weight_finite_on_compact
  -- Steps 3–5: (P1) by inner exhaustion of `O`, (P2) by outer approximation of `K` inside the
  -- open set `U`, both via Urysohn functions and (T).
  exact ⟨Submission.measure_open_le_liminf_of_tendsto_integral N U (fun i ↦ (Vi i).weight)
      V.weight (fun i ↦ hfin (Vi i)) (hfin V) hlim,
    Submission.limsup_measure_compact_le_of_tendsto_integral N U (fun i ↦ (Vi i).weight)
      V.weight V.isOpen_domain (fun i ↦ hfin (Vi i)) (hfin V) hlim⟩
/-- **Simon Ch. 8, proof of 3.7, printed step (2)** (child `besicovitch_ratio_cover` of
`density_semicontinuity`): if every `x ∈ A` is the centre of a closed ball `B_σ(x)`, `0 < σ < ρ₀`,
with `μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν({dist(·, A) < ρ₀})`, where `C` is the
Besicovitch number of `ℝ^N` (Ch. 1, 3.12).  The covering lemma splits a subfamily of these balls
covering `A` into `C` disjoint, hence countable, subfamilies; sum the ratio bound over each. -/
theorem Submission.besicovitch_ratio_cover_estimate :
    ∀ N : ℕ, ∃ C : ℕ, ∀ (μ ν : Measure (Euclidean N)) (A : Set (Euclidean N)) (ρ₀ : ℝ)
      (t : ℝ≥0∞), (∀ x ∈ A, ∃ σ : ℝ, 0 < σ ∧ σ < ρ₀ ∧
        μ (closedBall x σ) ≤ t * ν (closedBall x σ)) →
      μ A ≤ (C : ℝ≥0∞) * t * ν (thickening ρ₀ A) := by
  intro N
  -- `C` admits no satellite configuration of `C + 1` balls in `ℝ^N`.
  obtain ⟨C, τ, hτ, hC⟩ := HasBesicovitchCovering.no_satelliteConfig (α := Euclidean N)
  refine ⟨C, fun μ ν A ρ₀ t h ↦ ?_⟩
  choose σ hσ0 hσρ hσ using h
  obtain ⟨s, hdisj, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hC
    { c := ((↑) : A → Euclidean N), r := fun x ↦ σ x x.2, rpos := fun x ↦ hσ0 x x.2,
      r_bound := ρ₀, r_le := fun x ↦ (hσρ x x.2).le }
  set B : A → Set (Euclidean N) := fun x ↦ closedBall (x : Euclidean N) (σ x x.2)
  have hdisj' : ∀ i, (s i).PairwiseDisjoint B := hdisj
  have hcov' : A ⊆ ⋃ i, ⋃ x ∈ s i, B x := fun y hy ↦ by
    have hy' := hcov ⟨⟨y, hy⟩, rfl⟩
    simp only [mem_iUnion] at hy' ⊢
    obtain ⟨i, x, hx, hyx⟩ := hy'
    exact ⟨i, x, hx, ball_subset_closedBall hyx⟩
  -- Each disjoint subfamily is countable: its balls have nonempty interior.
  have hcount : ∀ i, (s i).Countable := fun i ↦
    (hdisj' i).countable_of_nonempty_interior fun x _ ↦
      ⟨x, ball_subset_interior_closedBall (mem_ball_self (hσ0 x x.2))⟩
  have hsub : ∀ x : A, B x ⊆ thickening ρ₀ A := fun x ↦
    (closedBall_subset_ball (hσρ x x.2)).trans (ball_subset_thickening x.2 ρ₀)
  calc μ A ≤ μ (⋃ i, ⋃ x ∈ s i, B x) := measure_mono hcov'
    _ ≤ ∑ i, μ (⋃ x ∈ s i, B x) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ∑' x : s i, μ (B x) :=
        Finset.sum_le_sum fun i _ ↦ measure_biUnion_le μ (hcount i) B
    _ ≤ ∑ i, ∑' x : s i, t * ν (B x) :=
        Finset.sum_le_sum fun i _ ↦ ENNReal.tsum_le_tsum fun x ↦ hσ _ x.1.2
    _ = ∑ i, t * ν (⋃ x ∈ s i, B x) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ENNReal.tsum_mul_left,
          measure_biUnion (hcount i) (hdisj' i) fun x _ ↦ measurableSet_closedBall]
    _ ≤ ∑ _i : Fin C, t * ν (thickening ρ₀ A) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_right (measure_mono (iUnion₂_subset fun x _ ↦ hsub x)) t
    _ = (C : ℝ≥0∞) * t * ν (thickening ρ₀ A) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
/-- **Simon Ch. 8, 3.7, printed step (4)** (child `monotonicity_mass_lower_bound` of the density
semicontinuity theorem): at a point where `Θ^n(μ_V, x) ≥ 1` and the ball bound 3.1 holds on
`(0, ρ₀)`, the monotonicity formula 3.3 gives `e^{-Λρ} ω_n ρ^n ≤ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`.
The density supplied by 3.3 equals `θ` by uniqueness of limits along `𝓝[>] 0`, and
`D = ω_n ρ^n ∈ (0, ∞)` cancels in `1 ≤ θ ≤ e^{Λρ} μ_V(B_ρ(x)) / D`. -/
theorem Submission.weight_closedBall_lower_bound_of_density_ge_one :
    MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U)
      (x : Euclidean N) (ρ₀ Λ : ℝ) (θ : ℝ≥0∞), V.HasLocallyBoundedFirstVariation → 0 < ρ₀ →
      ball x ρ₀ ⊆ U → 0 ≤ Λ →
      (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        variationMeasure V (closedBall x ρ) ≤ ENNReal.ofReal Λ * V.weight (closedBall x ρ)) →
      HasDensity n V.weight x θ → 1 ≤ θ → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤
        V.weight (closedBall x ρ) := by
  intro hMF N n U V x ρ₀ Λ θ hV hρ₀ hU hΛ hδ hθ h1 ρ hρ hρρ₀
  obtain ⟨-, θ', hθ', -, hθ'le⟩ := hMF N n U V x ρ₀ Λ hV hρ₀ hU hΛ hδ
  have hθθ' : θ = θ' := tendsto_nhds_unique hθ hθ'
  have hle : 1 ≤ ENNReal.ofReal (Real.exp (Λ * ρ)) * densityRatio n V.weight x ρ :=
    h1.trans (hθθ' ▸ (hθ'le ρ ρ hρ le_rfl hρρ₀).1)
  have hω0 : unitBallVolume n ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hD0 : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ).ne')
  have hDtop : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hexp : ENNReal.ofReal (Real.exp (-(Λ * ρ))) * ENNReal.ofReal (Real.exp (Λ * ρ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n
      = ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal ρ ^ n) * 1 := by
        rw [mul_one, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal ρ ^ n) *
          (ENNReal.ofReal (Real.exp (Λ * ρ)) * densityRatio n V.weight x ρ) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(Λ * ρ))) * ENNReal.ofReal (Real.exp (Λ * ρ)) *
          ((unitBallVolume n * ENNReal.ofReal ρ ^ n) * densityRatio n V.weight x ρ) := by ring
    _ = V.weight (closedBall x ρ) := by
        rw [hexp, one_mul, densityRatio, ENNReal.mul_div_cancel hD0 hDtop]

/-- **Simon Ch. 8, proof of 3.7, second half of printed step (4)** (child `limit_mass_lower_bound`
of `density_semicontinuity`): let `V_i → V` as Radon measures on `Gₙ(U)`, `q_i → ∞`, `y_i → x`,
`B°_{ρ₀}(x) ⊆ U` and `e^{-Λρ} ω_n ρ^n ≤ μ_{V_{q_i}}(B_ρ(y_i))` for all `i` and `0 < ρ < ρ₀`.  Then
`e^{-Λρ} ω_n ρ^n ≤ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`, hence `liminf_{ρ↓0} μ_V(B_ρ(x))/(ω_n ρ^n) ≥ 1`.
For large `i`, `B_{ρ-|y_i-x|}(y_i) ⊆ B_ρ(x)`, so `e^{-Λρ} ω_n ρ^n ≤ limsup_i μ_{V_{q_i}}(B_ρ(x))
≤ μ_V(B_ρ(x))` by (P2) of `weight_portmanteau_of_radonConverges`; then divide by `ω_n ρ^n`. -/
theorem Submission.lower_density_ge_one_of_nearby_mass_bounds :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U)
      (x : Euclidean N) (ρ₀ Λ : ℝ) (q : ℕ → ℕ) (y : ℕ → Euclidean N),
      Varifold.RadonConverges Vi V → 0 < ρ₀ → ball x ρ₀ ⊆ U → Tendsto q atTop atTop →
      Tendsto y atTop (𝓝 x) →
      (∀ i, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤
          (Vi (q i)).weight (closedBall (y i) ρ)) →
      (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤
          V.weight (closedBall x ρ)) ∧
      1 ≤ liminf (densityRatio n V.weight x) (𝓝[>] 0) := by
  intro N n U Vi V x ρ₀ Λ q y hV hρ₀ hU hq hy hmass
  -- `ω_n ∈ (0, ∞)`, and `F(r) = e^{-Λr} ω_n r^n` is continuous with finite values.
  have hω0 : unitBallVolume n ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  set F : ℝ → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal (Real.exp (-(Λ * r))) * unitBallVolume n * ENNReal.ofReal r ^ n
  have hE : Continuous fun r : ℝ ↦ ENNReal.ofReal (Real.exp (-(Λ * r))) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hF : ∀ r : ℝ, Tendsto F (𝓝 r) (𝓝 (F r)) := fun r ↦
    ENNReal.Tendsto.mul (ENNReal.Tendsto.mul_const (hE.tendsto r) (Or.inr hωtop))
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      (ENNReal.Tendsto.pow (ENNReal.continuous_ofReal.tendsto r))
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop))
  -- The mass bound for `V`: `F(ρ - |y_i - x|) ≤ μ_{V_{q_i}}(B_ρ(x))` for large `i`, and (P2).
  have hmassV : ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → F ρ ≤ V.weight (closedBall x ρ) := by
    intro ρ hρ hρρ₀
    have hP2 := (Submission.weight_portmanteau_of_radonConverges N n U Vi V hV).2
      (closedBall x ρ) (isCompact_closedBall x ρ) ((closedBall_subset_ball hρρ₀).trans hU)
    have hd : Tendsto (fun i ↦ dist (y i) x) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hy
    have hr : Tendsto (fun i ↦ ρ - dist (y i) x) atTop (𝓝 ρ) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ρ) atTop (𝓝 ρ)).sub hd
      rwa [sub_zero] at h
    have hle : ∀ᶠ i in atTop, F (ρ - dist (y i) x) ≤ (Vi (q i)).weight (closedBall x ρ) := by
      filter_upwards [hd.eventually (eventually_lt_nhds hρ)] with i hi
      refine (hmass i _ (sub_pos.2 hi) ((sub_le_self ρ dist_nonneg).trans_lt hρρ₀)).trans
        (measure_mono fun z hz ↦ ?_)
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z (y i) x]
    calc F ρ = limsup (fun i ↦ F (ρ - dist (y i) x)) atTop := ((hF ρ).comp hr).limsup_eq.symm
      _ ≤ limsup (fun i ↦ (Vi (q i)).weight (closedBall x ρ)) atTop := limsup_le_limsup hle
      _ ≤ limsup (fun j ↦ (Vi j).weight (closedBall x ρ)) atTop :=
          Tendsto.limsup_comp_le_limsup (u := fun j ↦ (Vi j).weight (closedBall x ρ)) hq
      _ ≤ V.weight (closedBall x ρ) := hP2
  refine ⟨hmassV, ?_⟩
  -- The lower density: `e^{-Λr} ≤ densityRatio n μ_V x r` on `(0, ρ₀)`, and `e^{-Λr} → 1`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(Λ * r))) ≤ densityRatio n V.weight x r := by
    filter_upwards [Ioo_mem_nhdsGT hρ₀] with r hr
    rw [densityRatio, ENNReal.le_div_iff_mul_le
      (Or.inl (mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr.1).ne')))
      (Or.inl (ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))), ← mul_assoc]
    exact hmassV r hr.1 hr.2
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (-(Λ * r)))) (𝓝[>] 0) (𝓝 1) := by
    have h := (hE.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one] at h
  calc (1 : ℝ≥0∞) = liminf (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (-(Λ * r)))) (𝓝[>] 0) :=
        hlim.liminf_eq.symm
    _ ≤ liminf (densityRatio n V.weight x) (𝓝[>] 0) := liminf_le_liminf hev

/-- **Simon Ch. 8, 3.7, density part** (child `lower_density_ae` of `density_semicontinuity`;
printed proof, pp. 212–213, (1)–(5), with the monotonicity formula 3.3): if `V_i → V` as Radon
measures on `Gₙ(U)`, `liminf_i ‖δV_i‖(W) < ∞` and `Θ^n(μ_{V_i}, ·) ≥ 1` off `B_i` with
`μ_{V_i}(B_i ∩ W) → 0` for every `W ⊂⊂ U`, then `liminf_{ρ↓0} μ_V(B_ρ(y)) / (ω_n ρ^n) ≥ 1` for
`μ_V`-a.e. `y`.  Fix `W ⊂⊂ U` and `W̃ = {dist(·, W) < ρ₀} ⊂⊂ U`.  A point of `W ∖ B_q` is good
for `(q, k)` if `‖δV_q‖ ≤ k μ_q` on its balls of radius `< ρ₀`; Besicovitch bounds the bad set by
`C k⁻¹ ‖δV_q‖(W̃) + μ_q(B_q ∩ W)` (printed (2)), so the points interior to `⋂_{ℓ ≥ i}` of the bad
sets for every `k ≥ 1` form a `μ_V`-null set (printed (3), (5)).  Each other `x ∈ W` is a limit of
good points `y_i` of `V_{q_i}`, where 3.3 with `Λ = k` gives `μ_{q_i}(B_ρ(y_i)) ≥ e^{-kρ} ω_n ρ^n`;
these bounds pass to `μ_V` at `x` (printed (4)).  Countably many `W ⊂⊂ U` exhaust `U`. -/
theorem Submission.lower_density_ge_one_ae_of_radonConverges :
    MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (B : ℕ → Set (Euclidean N)), Varifold.RadonConverges Vi V → (∀ i, (Vi i).HasLocallyBoundedFirstVariation) → (∀ W, IsRelCompactOpenIn W U → liminf (fun i ↦ variationMeasure (Vi i) W) atTop ≠ ∞) → (∀ i, ∀ y ∈ U \ B i, ∃ θ : ℝ≥0∞, HasDensity n (Vi i).weight y θ ∧ 1 ≤ θ) → (∀ W, IsRelCompactOpenIn W U → Tendsto (fun i ↦ (Vi i).weight (B i ∩ W)) atTop (𝓝 0)) → ∀ᵐ y ∂V.weight, 1 ≤ liminf (densityRatio n V.weight y) (𝓝[>] 0) := by
  intro hMF N n U Vi V B hconv hLB hbound hdens hsmall
  -- The Besicovitch constant `C` of `ℝ^N` and the portmanteau inequality (P1) for `V_i → V`.
  obtain ⟨C, hC⟩ := Submission.besicovitch_ratio_cover_estimate N
  have hP1 := (Submission.weight_portmanteau_of_radonConverges N n U Vi V hconv).1
  have hU : IsOpen U := V.isOpen_domain
  -- Step 2: `μ_V(Uᶜ) = 0`, so it suffices to prove the bound on each `W ⊂⊂ U` off a null set.
  have hUc : V.weight Uᶜ = 0 := by
    rw [V.weight_apply hU.measurableSet.compl]
    exact V.supported
  refine Submission.ae_of_forall_relCompactOpen_null_exceptional N U V.weight
    (fun y ↦ 1 ≤ liminf (densityRatio n V.weight y) (𝓝[>] 0)) hU hUc fun W hW ↦ ?_
  -- Step 1a: `W̃ = thickening ρ₀ W ⊂⊂ U`, and `B°_{ρ₀}(y) ⊆ W̃ ⊆ U` for every `y ∈ W`.
  obtain ⟨ρ₀, hρ₀, hWt⟩ := Submission.exists_thickening_isRelCompactOpenIn N U W hU hW
  have hWU : W ⊆ U := subset_closure.trans hW.2.2
  have hballU : ∀ y ∈ W, ball y ρ₀ ⊆ U := fun y hy ↦
    (ball_subset_thickening hy ρ₀).trans (subset_closure.trans hWt.2.2)
  -- Step 1b (printed (1)): `Bad q k = W ∖ A_{q,k}`, where `A_{q,k}` is the set of `y ∉ B_q` with
  -- `‖δV_q‖(B_ρ(y)) ≤ k μ_q(B_ρ(y))` for `0 < ρ < ρ₀`.
  set Bad : ℕ → ℕ → Set (Euclidean N) := fun q k ↦ W \ {y | y ∉ B q ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
    variationMeasure (Vi q) (closedBall y ρ) ≤ ENNReal.ofReal k * (Vi q).weight (closedBall y ρ)}
  -- Step 1c (printed (2)): `μ_q(Bad q k) ≤ C k⁻¹ ‖δV_q‖(W̃) + μ_q(B_q ∩ W)` for `k ≥ 1`.
  have hcover : ∀ q k : ℕ, 1 ≤ k → (Vi q).weight (Bad q k) ≤
      (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * variationMeasure (Vi q) (thickening ρ₀ W) +
        (Vi q).weight (B q ∩ W) := by
    intro q k hk
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    -- Every `x ∈ Bad q k ∖ B q` centres a ball `B_σ(x)`, `σ < ρ₀`, with
    -- `μ_q(B_σ(x)) ≤ k⁻¹ ‖δV_q‖(B_σ(x))`.
    have hratio : ∀ x ∈ Bad q k \ B q, ∃ σ : ℝ, 0 < σ ∧ σ < ρ₀ ∧
        (Vi q).weight (closedBall x σ) ≤
          (k : ℝ≥0∞)⁻¹ * variationMeasure (Vi q) (closedBall x σ) := by
      rintro x ⟨⟨-, hxA⟩, hxB⟩
      obtain ⟨σ, hσ, hσρ₀, hlt⟩ : ∃ σ : ℝ, 0 < σ ∧ σ < ρ₀ ∧ ENNReal.ofReal k *
          (Vi q).weight (closedBall x σ) < variationMeasure (Vi q) (closedBall x σ) := by
        by_contra hcon
        push Not at hcon
        exact hxA ⟨hxB, hcon⟩
      rw [ENNReal.ofReal_natCast] at hlt
      exact ⟨σ, hσ, hσρ₀, (ENNReal.mul_le_iff_le_inv hk0 (ENNReal.natCast_ne_top k)).1 hlt.le⟩
    calc (Vi q).weight (Bad q k)
        ≤ (Vi q).weight (Bad q k ∩ B q) + (Vi q).weight (Bad q k \ B q) :=
          measure_le_inter_add_sdiff _ _ _
      _ ≤ (Vi q).weight (B q ∩ W) +
            (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * variationMeasure (Vi q) (thickening ρ₀ W) := by
          gcongr ?_ + ?_
          · exact measure_mono fun x hx ↦ ⟨hx.2, hx.1.1⟩
          · refine (hC (Vi q).weight (variationMeasure (Vi q)) (Bad q k \ B q) ρ₀ (k : ℝ≥0∞)⁻¹
              hratio).trans ?_
            gcongr
            exact thickening_subset_of_subset ρ₀ (sdiff_subset.trans sdiff_subset)
      _ = _ := add_comm _ _
  -- Steps 1d–1e (printed (3), (5)): `⋂_{k ≥ 1} ⋃_i interior (⋂_{ℓ ≥ i} Bad ℓ k)` is `μ_V`-null.
  refine ⟨_, Submission.measure_bad_interior_exceptional_eq_zero N V.weight (fun q ↦ (Vi q).weight)
    W Bad C (fun q ↦ variationMeasure (Vi q) (thickening ρ₀ W)) (fun q ↦ (Vi q).weight (B q ∩ W))
    (fun O hO hOW ↦ hP1 O hO (hOW.trans hWU)) (fun _ _ ↦ sdiff_subset) (hbound _ hWt) (hsmall W hW)
    hcover, fun x hxW hxE ↦ ?_⟩
  -- Step 1f (printed (4)): for some `k ≥ 1`, `x` is interior to no `⋂_{ℓ ≥ i} Bad ℓ k`.
  obtain ⟨k, -, hxk⟩ : ∃ k : ℕ, 1 ≤ k ∧
      ∀ i : ℕ, x ∉ interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k) := by
    by_contra hcon
    push Not at hcon
    exact hxE (mem_iInter₂.2 fun k hk ↦ mem_iUnion.2 (hcon k hk))
  -- Good points `y i → x` of `V_{q i}` in `W`, with `q i → ∞`.
  obtain ⟨q, y, hq, hy, hyq⟩ :=
    Submission.exists_nearby_points_off_bad_sets N W (fun ℓ ↦ Bad ℓ k) x hW.1 hxW hxk
  have hgood : ∀ i, y i ∉ B (q i) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      variationMeasure (Vi (q i)) (closedBall (y i) ρ) ≤
        ENNReal.ofReal k * (Vi (q i)).weight (closedBall (y i) ρ) := fun i ↦
    not_not.1 fun h ↦ (hyq i).2 ⟨(hyq i).1, h⟩
  -- Monotonicity 3.3 with `Λ = k` at `y i`, where `Θ^n(μ_{q i}, y i) ≥ 1`.
  have hmass : ∀ i, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ENNReal.ofReal (Real.exp (-((k : ℝ) * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤
        (Vi (q i)).weight (closedBall (y i) ρ) := fun i ↦ by
    obtain ⟨θ, hθ, h1θ⟩ := hdens (q i) (y i) ⟨hWU (hyq i).1, (hgood i).1⟩
    exact Submission.weight_closedBall_lower_bound_of_density_ge_one hMF N n U (Vi (q i)) (y i) ρ₀
      k θ (hLB (q i)) hρ₀ (hballU _ (hyq i).1) (Nat.cast_nonneg k) (hgood i).2 hθ h1θ
  -- The mass bounds pass to `μ_V` at `x = lim y i`.
  exact (Submission.lower_density_ge_one_of_nearby_mass_bounds N n U Vi V x ρ₀ k q y hconv hρ₀
    (hballU x hxW) hq hy hmass).2

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
/-- Hypothesis 3.1 of the monotonicity formula holds `μ_V`-a.e. (the remark in the proof of Simon
Ch. 8, 3.6, p. 211, by the differentiation theorem 2.7): for `μ_V`-a.e. `x` there are `R > 0` with
`B_R(x) ⊆ U` and `Λ ≥ 0` with `‖δV‖(B_r(x)) ≤ Λ μ_V(B_r(x))` for all `0 < r < R`. -/
theorem Submission.dea_ae_variationMeasure_ball_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → ∀ᵐ x ∂V.weight, ∃ R Λ : ℝ, 0 < R ∧ 0 ≤ Λ ∧ closedBall x R ⊆ U ∧ ∀ r : ℝ, 0 < r → r < R → variationMeasure V (closedBall x r) ≤ ENNReal.ofReal Λ * V.weight (closedBall x r) := by
  intro N n U V hV
  -- Step 1: `μ_V` is carried by `U`, since `μ_V(Uᶜ) = V(Uᶜ × G(N,n)) = 0`.
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  -- Step 2: under `hV`, `‖δV‖` is the Riesz measure `ν`.
  have hvar : variationMeasure V = V.firstVariationRieszMeasure hV := dite_eq_left hV
  -- Step 3: by the differentiation theorem (Simon 2.7), for `μ_V`-a.e. `x` the ratio
  -- `ν(B_r(x)) / μ_V(B_r(x))` tends to a finite `D(x)` as `r ↓ 0`.
  filter_upwards [(V.firstVariationRiesz_symmetricDensity_spec hV).2, hU] with x hx hxU
  obtain ⟨ht, hD⟩ := hx
  -- Step 4: `Λ = D(x) + 1 > 0` satisfies `D(x) < Λ`.
  set D := V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure hV) x
  set Λ : ℝ := D.toReal + 1
  have hΛ : 0 < Λ := by positivity
  have hlt : D < ENNReal.ofReal Λ := by
    rw [← ENNReal.ofReal_toReal hD]
    exact (ENNReal.ofReal_lt_ofReal_iff hΛ).mpr (lt_add_one _)
  -- Step 5: the ratio is `< Λ` for all `r ∈ (0, r₁)`.
  obtain ⟨r₁, hr₁, hsmall⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually (gt_mem_nhds hlt))
  -- Step 7: `B_{r₂}(x) ⊆ U` (open ball), and `R = min r₁ (r₂ / 2)`.
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp V.isOpen_domain x hxU
  refine ⟨min r₁ (r₂ / 2), Λ, lt_min hr₁ (half_pos hr₂), hΛ.le, ?_, fun r hr hrR ↦ ?_⟩
  · exact (closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr₂))).trans hball
  -- Step 6: `ν(B_r(x)) / μ_V(B_r(x)) ≤ Λ` gives `ν(B_r(x)) ≤ Λ μ_V(B_r(x))`, as `Λ ≠ 0, ∞`.
  · rw [hvar]
    exact (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
      (Or.inr (ENNReal.ofReal_pos.mpr hΛ).ne')).mp
      (hsmall ⟨hr, hrR.trans_le (min_le_left _ _)⟩).le

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

/-- Integration against a measure that is `θ H^n ⌞ M` on Borel sets (used in the proof of Simon
Ch. 8, 1.2, where `μ_V = θ H^n ⌞ M`): if `μ B = ∫⁻_{B ∩ M} θ dH^n` for every Borel set `B`,
`θ > 0` on `M`, `θ` is `H^n`-integrable on `M ∩ K` for a Borel set `K` and `h` vanishes off `K`,
then `∫ h dμ = ∫_M h θ dH^n`.  `h` is arbitrary: no measurability or integrability is assumed. -/
theorem Submission.frt_wat_integral_eq_setIntegral_mul :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M K : Set (Euclidean N)) (θ h : Euclidean N → ℝ), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → MeasurableSet K → IntegrableOn θ (M ∩ K) μHE[n] → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ y in B ∩ M, ENNReal.ofReal (θ y) ∂μHE[n]) → (∀ z, z ∉ K → h z = 0) → ∫ z, h z ∂μ = ∫ z in M, h z * θ z ∂μHE[n] := by
  intro N n μ M K θ h hM hθ hK hθK hμ hh
  -- Step 1: `μ ⌞ K = (H^n ⌞ (M ∩ K)).withDensity (ofReal ∘ θ)`, compared on Borel sets `B`.
  have hrestr : μ.restrict K =
      ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ K)).withDensity
        (fun y ↦ ENNReal.ofReal (θ y)) := by
    ext B hB
    rw [Measure.restrict_apply hB, hμ _ (hB.inter hK), withDensity_apply _ hB,
      Measure.restrict_restrict hB, inter_assoc, inter_comm K M]
  -- `M ∩ K` is `H^n`-null-measurable, so `H^n ⌞ (M ∩ K)`-a.e. point lies in `M ∩ K`.
  have hMK : NullMeasurableSet (M ∩ K) (μHE[n] : Measure (Euclidean N)) :=
    hM.inter hK.nullMeasurableSet
  calc ∫ z, h z ∂μ = ∫ z in K, h z ∂μ :=
        -- Step 2: `h = 0` off `K`.
        (setIntegral_eq_integral_of_forall_compl_eq_zero hh).symm
    _ = ∫ z, (ENNReal.ofReal (θ z)).toReal • h z
          ∂((μHE[n] : Measure (Euclidean N)).restrict (M ∩ K)) := by
        -- Step 3: the density `ofReal ∘ θ` is a.e.-measurable (`θ` is integrable) and finite.
        rw [hrestr, integral_withDensity_eq_integral_toReal_smul₀
          (Integrable.aemeasurable hθK).ennreal_ofReal
          (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    _ = ∫ z in M ∩ K, h z * θ z ∂μHE[n] := by
        -- Step 4: `(ofReal (θ z)).toReal = θ z` for a.e. `z ∈ M ∩ K`, as `θ > 0` on `M`.
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem₀ hMK] with z hz
        rw [ENNReal.toReal_ofReal (hθ z hz.1).le, smul_eq_mul, mul_comm]
    _ = ∫ z in M, h z * θ z ∂μHE[n] :=
        -- Step 5: `h θ = 0` on `M \ (M ∩ K)` and `M` is null-measurable.
        (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM inter_subset_left
          (Eventually.of_forall fun z hz ↦ by
            rw [hh z fun hzK ↦ hz.2 ⟨hz.1, hzK⟩, zero_mul])).symm

/-- Dilation change of variables for `H^n` set integrals over blow-up images (the homothety step
behind Simon Ch. 8, 1.2 with Ch. 3, 1.7): for `r > 0`, `η = η_{x,r}` (`η y = r⁻¹ • (y - x)`), an
arbitrary set `M` and an arbitrary `F : ℝ^N → ℝ`, `∫_{η(M)} F dH^n = r⁻¹ ^ n ∫_M F ∘ η dH^n`. -/
theorem Submission.frt_wat_setIntegral_blowUpMap_image :
    ∀ (N n : ℕ) (x : Euclidean N) (r : ℝ) (M : Set (Euclidean N)) (F : Euclidean N → ℝ), 0 < r → ∫ y in Chapter03.blowUpMap x r '' M, F y ∂μHE[n] = r⁻¹ ^ n * ∫ z in M, F (Chapter03.blowUpMap x r z) ∂μHE[n] := by
  intro N n x r M F hr
  -- Step 1: `η = blowUpMap x r` is a homeomorphism (inverse `y ↦ x + r • y`), hence an
  -- injective measurable embedding.
  let η : Euclidean N ≃ₜ Euclidean N :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hη : (η : Euclidean N → Euclidean N) = Chapter03.blowUpMap x r := rfl
  have hemb : MeasurableEmbedding η := η.measurableEmbedding
  -- Step 2: `H^n(η⁻¹ S) = r ^ n H^n(S)` for every set `S`, as `η⁻¹ S = x + r • S`.
  have hpre : ∀ S : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) (η ⁻¹' S) =
      ENNReal.ofReal (r ^ n) * μHE[n] S := by
    intro S
    have hS : (η : Euclidean N → Euclidean N) ⁻¹' S = (fun y ↦ x + y) '' (r • S) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_smul_set]
      constructor
      · intro h
        refine ⟨r • (r⁻¹ • (y - x)), ⟨_, h, rfl⟩, ?_⟩
        simp [smul_smul, mul_inv_cancel₀ hr.ne']
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        simpa [η, smul_smul, inv_mul_cancel₀ hr.ne'] using hs
    rw [hS, (isometry_add_left x).euclideanHausdorffMeasure_image,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne', ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr.le, ENNReal.ofReal_pow hr.le]
  -- Step 3: `H^n.map η = r ^ n • H^n` (`Measure.ext` on Borel sets).
  have hmap : (μHE[n] : Measure (Euclidean N)).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)) := by
    ext S hS
    rw [Measure.map_apply hemb.measurable hS, hpre, Measure.smul_apply, smul_eq_mul]
  -- Step 4: `(H^n ⌞ M).map η = r ^ n • H^n ⌞ η(M)`, using `η⁻¹(η(M)) = M`.
  have hres : ((μHE[n] : Measure (Euclidean N)).restrict M).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)).restrict (η '' M) := by
    rw [← Measure.restrict_smul, ← hmap, hemb.restrict_map, Set.preimage_image_eq M η.injective]
  -- Step 5: `∫_M F ∘ η dH^n = r ^ n ∫_{η(M)} F dH^n` (no measurability of `M` or `F` needed).
  have hcov : ∫ z in M, F (η z) ∂μHE[n] = r ^ n * ∫ y in η '' M, F y ∂μHE[n] := by
    rw [← hemb.integral_map, hres, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_nonneg hr.le n), smul_eq_mul]
  -- Step 6: multiply by `r⁻¹ ^ n`, using `r⁻¹ ^ n * r ^ n = 1`.
  rw [← hη, hcov, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]

/-- Tangent planes of `V` are the approximate tangent planes of its carrier (Simon Ch. 8, proof of
1.2, with Ch. 3, Definition 1.7): if `μ_V(B) = ∫_{B ∩ M} θ dH^n` for Borel `B` and `V` has tangent
plane `T` with multiplicity `θ(x)` at `x`, then `T` is the unique `n`-plane that is an approximate
tangent space of `M` at `x` with respect to `θ`. -/
theorem Submission.frt_weighted_approx_tangent :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (T : Grassmannian N n), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μHE[n]) → (∀ B : Set (Euclidean N), MeasurableSet B → V.weight B = ∫⁻ y in B ∩ M, ENNReal.ofReal (θ y) ∂μHE[n]) → HasTangentPlane V x T (θ x) → ∀ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ↔ S = T := by
  intro N n U V M θ x T hM hθ hint hweight hT
  -- Steps 1, 4 and 5: `T.plane` is an approximate tangent space of `M` at `x` w.r.t. `θ`.
  have hTM : Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x T.plane := by
    refine ⟨T.finrank_plane, fun f ↦ ?_⟩
    -- Radii `0 < r < ε / R` with `B_ε(x) ⊆ U` and `spt f ⊆ B_R(0)`, so that `B_{rR}(x) ⊆ U`.
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hT.1
    obtain ⟨R₀, hR₀⟩ :=
      f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclidean N)
    have hR : (0 : ℝ) < max R₀ 1 := lt_max_of_lt_right one_pos
    refine (Submission.frt_weight_blowup_tendsto N n U V x T (θ x) hT f).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hε hR)] with r hr
    have hr0 : 0 < r := hr.1
    have hKU : closedBall x (r * max R₀ 1) ⊆ U :=
      (closedBall_subset_ball ((lt_div_iff₀ hR).1 hr.2)).trans hεU
    -- `z ↦ f(r⁻¹(z - x))` vanishes off the compact set `B_{rR}(x) ⊆ U`.
    have hvanish : ∀ z, z ∉ closedBall x (r * max R₀ 1) → f (r⁻¹ • (z - x)) = 0 := by
      intro z hz
      by_contra hfz
      have hmem := hR₀ (subset_tsupport _ hfz)
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le] at hmem
      refine hz (mem_closedBall_iff_norm.2 ?_)
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
        _ ≤ r * max R₀ 1 := mul_le_mul_of_nonneg_left (hmem.trans (le_max_left _ _)) hr0.le
    -- Step 2: `∫ f(r⁻¹(z - x)) dμ_V(z) = ∫_M f(r⁻¹(z - x)) θ(z) dH^n(z)`.
    have h₁ : ∫ z, f (r⁻¹ • (z - x)) ∂V.weight =
        ∫ z in M, f (r⁻¹ • (z - x)) * θ z ∂μHE[n] :=
      Submission.frt_wat_integral_eq_setIntegral_mul N n V.weight M
        (closedBall x (r * max R₀ 1)) θ (fun z ↦ f (r⁻¹ • (z - x))) hM hθ
        measurableSet_closedBall (hint _ (isCompact_closedBall x _) hKU) hweight hvanish
    -- Step 3: the homothety change of variables `y = η_{x,r}(z)`, with `x + r η_{x,r}(z) = z`.
    have h₂ : ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n] =
        r⁻¹ ^ n * ∫ z in M, f (Chapter03.blowUpMap x r z) *
          θ (x + r • Chapter03.blowUpMap x r z) ∂μHE[n] :=
      Submission.frt_wat_setIntegral_blowUpMap_image N n x r M (fun y ↦ f y * θ (x + r • y)) hr0
    have h₃ : ∀ z, f (Chapter03.blowUpMap x r z) * θ (x + r • Chapter03.blowUpMap x r z) =
        f (r⁻¹ • (z - x)) * θ z := fun z ↦ by
      rw [Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
    simp only [h₃] at h₂
    rw [h₁, h₂]
  -- Step 6: weighted approximate tangent planes are unique as `θ(x) ≠ 0`, and a point of
  -- `G(N,n)` is determined by its plane.
  intro S
  refine ⟨fun hS ↦ ?_, fun hST ↦ hST ▸ hTM⟩
  have hplane : S.plane = T.plane :=
    Chapter03.HasWeightedApproximateTangentSpaceAt.unique hT.2.1.ne' hS hTM
  calc S = Grassmannian.ofSubmodule S.plane S.finrank_plane :=
        (Grassmannian.ofSubmodule_plane S).symm
    _ = Grassmannian.ofSubmodule T.plane T.finrank_plane := by simp only [hplane]
    _ = T := Grassmannian.ofSubmodule_plane T

/-- Simon Ch. 8, Definition 1.1 tested on a product function: if `V` has tangent plane `T` with
multiplicity `θ` at `x`, then for `g ∈ C_c(ℝ^N)` and continuous `β` on `G(N,n)`,
`t^{-n} ∫ g(t⁻¹(y - x)) β(S) dV(y,S) → θ β(T) ∫_T g dH^n` as `t ↓ 0` (the test function is
`f(y,S) = g(y) β(S)`; used for the tangent-ball averages in the proof of 1.2). -/
theorem Submission.frt_vgm_tba_product_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ (g : C_c(Euclidean N, ℝ)) (β : C(Grassmannian N n, ℝ)), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z.1 - x)) * β z.2 ∂V.measure) (𝓝[>] 0) (𝓝 (θ * (β T * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) := by
  intro N n U V x T θ hT g β
  -- Step 1: the product test function `f(y,S) = g(y) β(S)` lies in `C_c(ℝ^N × G(N,n))`: it is
  -- continuous and vanishes off the compact set `tsupport g × G(N,n)`.
  have hcont : Continuous (fun z : Euclidean N × Grassmannian N n ↦ g z.1 * β z.2) :=
    (g.continuous.comp continuous_fst).mul (β.continuous.comp continuous_snd)
  have hsupp : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1 * β z.2) := by
    refine HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) ?_
    intro z hz
    have hz1 : z.1 ∉ tsupport g := fun h ↦ hz ⟨h, mem_univ _⟩
    simp [image_eq_zero_of_notMem_tsupport hz1]
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) := ⟨⟨_, hcont⟩, hsupp⟩
  -- Step 2: Def. 1.1 applied to `f`.
  have h := hT.2.2 f
  -- Step 3: the plane side, `∫ f dv(T) = β(T) ∫_T g dH^n`.
  have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
      β T * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] := by
    rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T))
      (continuous_id.prodMk continuous_const).aemeasurable (map_continuous f).aestronglyMeasurable]
    change ∫ y in (T.plane : Set (Euclidean N)), g y * β T ∂μHE[n] = _
    rw [integral_mul_const, mul_comm]
  -- Step 4: the rescaled side, `∫ f dV_{x,t} = t^{-n} ∫ g(t⁻¹(y - x)) β(S) dV` for `t > 0`.
  have hresc : ∀ t ∈ Ioi (0 : ℝ), ∫ z, f z ∂(rescaledMeasure V x t) =
      t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z.1 - x)) * β z.2 ∂V.measure := by
    intro t ht
    rw [rescaledMeasure, integral_smul_measure,
      integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2))
        (show Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) by
          fun_prop).aemeasurable (map_continuous f).aestronglyMeasurable,
      ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (mem_Ioi.mp ht).le) n), smul_eq_mul]
    rfl
  -- Step 5: the two sides agree on `(0, ∞) ∈ 𝓝[>] 0`, so the limit transfers.
  rw [hplane] at h
  exact h.congr' (eventually_nhdsWithin_of_forall hresc)

/-- The cut-off sandwich for a ball (steps 2 and 7 of the tangent-ball average used for Simon
Ch. 8, 1.2): with `χ⁻ = max(0, min(1, (1 - |w|)/κ))`, `χ⁺ = max(0, min(1, (1 + κ - |w|)/κ))` and
`w = t⁻¹(y - x)`, `∫ χ⁻ β dV ≤ ∫_{B_t(x) × G} β dV ≤ ∫ χ⁺ β dV` for `β ≥ 0`, since
`χ⁻(w) β ≤ 1_{B_t(x) × G} β ≤ χ⁺(w) β` pointwise and all three integrands are bounded, measurable
and vanish off `B_{2t}(x) × G`, which has finite `V`-measure. -/
theorem Submission.frt_vgm_tba_ball_cutoff_sandwich :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (β : C(Grassmannian N n, ℝ)) (κ t : ℝ), 0 < κ → κ < 1 → 0 < t → closedBall x (2 * t) ⊆ U → (∀ S, 0 ≤ β S) → (∫ z, max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure) ≤ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ∧ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ≤ ∫ z, max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure := by
  intro N n U V x β κ t hκ hκ1 ht hU hβ
  -- Step 1: `V(B_{2t}(x) × G) < ∞` (`B_{2t}(x)` is a compact subset of `U`), and
  -- `B = B_t(x) × G` is Borel.
  have hK : V.measure (closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ :=
    V.finite_on_compact _ (isCompact_closedBall x (2 * t)) hU
  have hB : MeasurableSet (closedBall x t ×ˢ (univ : Set (Grassmannian N n))) :=
    measurableSet_closedBall.prod MeasurableSet.univ
  -- Step 2: `|β| ≤ ‖β‖` on the compact Grassmannian.
  have hβb : ∀ S, ‖β S‖ ≤ ‖β‖ := β.norm_coe_le_norm
  -- Step 3: `|t⁻¹(y - x)| = dist(y, x)/t`; hence `z ∈ B ↔ |w(z)| ≤ 1`, and `|w(z)| > 2` off
  -- `B_{2t}(x) × G`.
  have hw : ∀ y : Euclidean N, ‖t⁻¹ • (y - x)‖ = dist y x / t := fun y ↦ by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), dist_eq_norm, inv_mul_eq_div]
  have hin : ∀ z : Euclidean N × Grassmannian N n,
      z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n)) ↔ ‖t⁻¹ • (z.1 - x)‖ ≤ 1 := fun z ↦ by
    rw [mem_prod, mem_closedBall, hw, div_le_one ht, and_iff_left (mem_univ _)]
  have hfar : ∀ z : Euclidean N × Grassmannian N n,
      z ∉ closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n)) → 2 < ‖t⁻¹ • (z.1 - x)‖ := by
    intro z hz
    rw [mem_prod, mem_closedBall, and_iff_left (mem_univ _), not_le] at hz
    rw [hw, lt_div_iff₀ ht]
    exact hz
  -- Step 4: cut-off facts for `χ_a(w) = max(0, min(1, (a - |w|)/κ))`.
  have hχ0 : ∀ a r : ℝ, 0 ≤ max 0 (min 1 ((a - r) / κ)) := fun a r ↦ le_max_left _ _
  have hχ1 : ∀ a r : ℝ, max 0 (min 1 ((a - r) / κ)) ≤ 1 := fun a r ↦
    max_le zero_le_one (min_le_left _ _)
  have hχz : ∀ a r : ℝ, a ≤ r → max 0 (min 1 ((a - r) / κ)) = 0 := fun a r h ↦
    max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) hκ.le))
  have hχo : ∀ a r : ℝ, r ≤ a - κ → max 0 (min 1 ((a - r) / κ)) = 1 := fun a r h ↦ by
    rw [min_eq_left ((one_le_div hκ).2 (by linarith)), max_eq_right zero_le_one]
  -- Step 5: a measurable function bounded by `‖β‖` and vanishing off `B_{2t}(x) × G` is
  -- `V`-integrable.
  have hint : ∀ k : Euclidean N × Grassmannian N n → ℝ, AEStronglyMeasurable k V.measure →
      (∀ z, ‖k z‖ ≤ ‖β‖) →
      (∀ z, z ∉ closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n)) → k z = 0) →
      Integrable k V.measure := fun k hk hb h0 ↦
    (Measure.integrableOn_of_bounded hK hk (ae_of_all _ hb)).integrable_of_forall_notMem_eq_zero h0
  have hβc : Continuous fun z : Euclidean N × Grassmannian N n ↦ β z.2 :=
    β.continuous.comp continuous_snd
  have hbd : ∀ (a : ℝ) (z : Euclidean N × Grassmannian N n),
      ‖max 0 (min 1 ((a - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2‖ ≤ ‖β‖ := fun a z ↦ by
    rw [norm_mul, Real.norm_of_nonneg (hχ0 _ _)]
    exact (mul_le_mul (hχ1 _ _) (hβb _) (norm_nonneg _) zero_le_one).trans (one_mul _).le
  have hm : Integrable (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (hbd 1) fun z hz ↦ ?_
    rw [hχz 1 _ (by linarith [hfar z hz]), zero_mul]
  have hp : Integrable (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (hbd (1 + κ)) fun z hz ↦ ?_
    rw [hχz (1 + κ) _ (by linarith [hfar z hz]), zero_mul]
  have hi : Integrable ((closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator
      fun z : Euclidean N × Grassmannian N n ↦ β z.2) V.measure := by
    refine hint _ (hβc.aestronglyMeasurable.indicator hB)
      (fun z ↦ (norm_indicator_le_norm_self _ z).trans (hβb _)) fun z hz ↦ ?_
    refine indicator_of_notMem (fun hzB ↦ hz ?_) _
    exact ⟨mem_closedBall.2 ((mem_closedBall.1 hzB.1).trans (by linarith)), mem_univ _⟩
  -- Step 6: the pointwise sandwich `χ⁻(w) β ≤ 1_B β ≤ χ⁺(w) β`.
  have hle₁ : (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) ≤
      (closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator fun z ↦ β z.2 := by
    intro z
    dsimp only
    by_cases hz : z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n))
    · rw [indicator_of_mem hz]
      exact mul_le_of_le_one_left (hβ _) (hχ1 _ _)
    · rw [indicator_of_notMem hz, hχz 1 _ (not_le.1 (mt (hin z).2 hz)).le, zero_mul]
  have hle₂ : (closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator
      (fun z : Euclidean N × Grassmannian N n ↦ β z.2) ≤
      fun z ↦ max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 := by
    intro z
    dsimp only
    by_cases hz : z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n))
    · rw [indicator_of_mem hz, hχo (1 + κ) _ (by linarith [(hin z).1 hz]), one_mul]
    · rw [indicator_of_notMem hz]
      exact mul_nonneg (hχ0 _ _) (hβ _)
  -- Step 7: integrate, using `∫ 1_B β dV = ∫_B β dV`.
  rw [← integral_indicator hB]
  exact ⟨integral_mono hm hi hle₁, integral_mono hi hp hle₂⟩

/-- The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane
`T ∈ G(N,n)` is `ω_n r^n` (step 5, plane balls, of the tangent-ball average proof for Simon Ch. 8,
1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`. -/
theorem Submission.frt_vgm_tba_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: an orthonormal basis `b` of `T.plane` indexed by `Fin n`, since `finrank T.plane = n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  -- Step 2: the isometric parametrization `ι : ℝ^n → ℝ^N`, `ι v = b.repr.symm v ∈ T.plane`.
  let ι : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  -- Step 3: `ι '' B_r(0) = T.plane ∩ B_r(0)`.
  have himage : ι '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(b.repr.symm v).2, ?_⟩
      rw [mem_closedBall_zero_iff] at hv ⊢
      rwa [ι.norm_map]
    · rintro ⟨hw, hwr⟩
      refine ⟨b.repr ⟨w, hw⟩, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff] at hwr ⊢
        rwa [b.repr.norm_map]
      · change ((b.repr.symm (b.repr ⟨w, hw⟩) : T.plane) : Euclidean N) = w
        rw [b.repr.symm_apply_apply]
  -- Step 4: `H^n` is invariant under the isometry `ι`, and `H^n = vol` on `ℝ^n`.
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Step 5: Haar scaling `vol (B_r(0)) = r^n vol (B°_1(0))` (`r ≥ 0`; no `0 < n` needed).
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr,
    unitBallVolume, mul_comm]

/-- The plane integrals of the radial cut-offs `χ⁻ = χ_{1-κ,1}` and `χ⁺ = χ_{1,1+κ}`, where
`χ_{a,b}(y) = max(0, min(1, (b - |y|)/(b - a)))`, over an `n`-plane `T ∈ G(N,n)` satisfy
`ω_n (1-κ)^n ≤ ∫_T χ⁻ dH^n` and `∫_T χ⁺ dH^n ≤ ω_n (1+κ)^n` for `0 < κ < 1` (step 6 of the
tangent-ball average in the proof of Simon Ch. 8, 1.2): `1_{B_{1-κ}(0)} ≤ χ⁻` and
`χ⁺ ≤ 1_{B_{1+κ}(0)}`, while `H^n(T ∩ B_r(0)) = ω_n r^n`
(`frt_vgm_tba_plane_closedBall_hausdorff`). -/
theorem Submission.frt_vgm_tba_plane_cutoff_bounds :
    ∀ (N n : ℕ) (T : Grassmannian N n) (κ : ℝ), 0 < κ → κ < 1 → (unitBallVolume n).toReal * (1 - κ) ^ n ≤ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n] ∧ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n] ≤ (unitBallVolume n).toReal * (1 + κ) ^ n := by
  intro N n T κ hκ hκ1
  set μ : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hμ
  -- Step 1: `μ(B_r(0)) = ω_n r^n < ∞` for `r ≥ 0`, from `frt_vgm_tba_plane_closedBall_hausdorff`.
  have hball : ∀ r : ℝ, 0 ≤ r → μ (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
    intro r hr
    rw [hμ, Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.frt_vgm_tba_plane_closedBall_hausdorff N n T r hr
  have hfin : ∀ r : ℝ, 0 ≤ r → μ (closedBall 0 r) ≠ ∞ := by
    intro r hr
    rw [hball r hr]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hreal : ∀ r : ℝ, 0 ≤ r → μ.real (closedBall 0 r) = (unitBallVolume n).toReal * r ^ n := by
    intro r hr
    rw [measureReal_def, hball r hr, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr]
  -- Step 2: the cut-off `χ_a(y) = max(0, min(1, (a - |y|)/κ))` takes values in `[0,1]`, vanishes
  -- where `|y| ≥ a` and equals `1` where `|y| ≤ a - κ`.
  have hχ0 : ∀ (a : ℝ) (y : Euclidean N), 0 ≤ max 0 (min 1 ((a - ‖y‖) / κ)) :=
    fun a y ↦ le_max_left _ _
  have hχ1 : ∀ (a : ℝ) (y : Euclidean N), max 0 (min 1 ((a - ‖y‖) / κ)) ≤ 1 :=
    fun a y ↦ max_le zero_le_one (min_le_left _ _)
  have hχ_out : ∀ (a : ℝ) (y : Euclidean N), a ≤ ‖y‖ → max 0 (min 1 ((a - ‖y‖) / κ)) = 0 :=
    fun a y hy ↦ max_eq_left
      ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hy) hκ.le))
  have hχ_in : ∀ (a : ℝ) (y : Euclidean N), ‖y‖ ≤ a - κ → max 0 (min 1 ((a - ‖y‖) / κ)) = 1 := by
    intro a y hy
    rw [min_eq_left ((le_div_iff₀ hκ).2 (by linarith)), max_eq_right zero_le_one]
  -- Step 3: `χ_a` (`a ≤ 2`) and the ball indicators are `μ`-integrable.
  have hχ_int : ∀ a : ℝ, a ≤ 2 →
      Integrable (fun y : Euclidean N ↦ max 0 (min 1 ((a - ‖y‖) / κ))) μ := by
    intro a ha
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := closedBall (0 : Euclidean N) 2) ?_ fun y hy ↦ hχ_out a y ?_
    · refine Measure.integrableOn_of_bounded (M := 1) (hfin 2 zero_le_two) (by fun_prop) ?_
      exact Eventually.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hχ0 a y)]; exact hχ1 a y
    · rw [mem_closedBall_zero_iff, not_le] at hy
      linarith
  have hind_int : ∀ r : ℝ, 0 ≤ r → Integrable ((closedBall (0 : Euclidean N) r).indicator 1) μ :=
    fun r hr ↦ (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (C := (1 : ℝ)) (hfin r hr))
  constructor
  · -- Step 4: `1_{B_{1-κ}(0)} ≤ χ⁻`, so `ω_n (1-κ)^n = μ(B_{1-κ}(0)) ≤ ∫ χ⁻ dμ`.
    rw [← hreal (1 - κ) (by linarith), ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono (hind_int (1 - κ) (by linarith)) (hχ_int 1 (by norm_num)) fun y ↦ ?_
    by_cases hy : y ∈ closedBall (0 : Euclidean N) (1 - κ)
    · rw [indicator_of_mem hy, Pi.one_apply, hχ_in 1 y (mem_closedBall_zero_iff.1 hy)]
    · rw [indicator_of_notMem hy]
      exact hχ0 1 y
  · -- Step 5: `χ⁺ ≤ 1_{B_{1+κ}(0)}`, so `∫ χ⁺ dμ ≤ μ(B_{1+κ}(0)) = ω_n (1+κ)^n`.
    rw [← hreal (1 + κ) (by linarith), ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono (hχ_int (1 + κ) (by linarith)) (hind_int (1 + κ) (by linarith))
      fun y ↦ ?_
    by_cases hy : y ∈ closedBall (0 : Euclidean N) (1 + κ)
    · rw [indicator_of_mem hy, Pi.one_apply]
      exact hχ1 (1 + κ) y
    · rw [indicator_of_notMem hy, hχ_out (1 + κ) y (not_le.1 (mt mem_closedBall_zero_iff.2 hy)).le]

/-- Ball integrals at a tangent plane for `β ≥ 0` (the step "`ν_V^{(x)}(β) = θ(x) β(T_x)`" in the
proof of Simon Ch. 8, 1.2, p. 207, for the ratios of 1.3): if `V` has tangent space `T` with
multiplicity `θ` at `x` (1.1), then `t^{-n} ∫_{B_t(x) × G(N,n)} β(S) dV(y,S) → θ ω_n β(T)` as
`t ↓ 0` for every continuous `β ≥ 0` on `G(N,n)`. -/
theorem Submission.frt_vgm_tba_nonneg_ball_limit :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ β : C(Grassmannian N n, ℝ), (∀ S, 0 ≤ β S) → Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) (𝓝[>] 0) (𝓝 (θ * (unitBallVolume n).toReal * β T)) := by
  intro N n U V x T θ hT β hβ
  -- `J(t) = t^{-n} ∫_{B_t(x) × G(N,n)} β dV` is to tend to `c = θ β(T) ω_n`; here `θ β(T) ≥ 0`
  -- since `θ > 0` and `β ≥ 0`.
  have hθβ : 0 ≤ θ * β T := mul_nonneg hT.2.1.le (hβ T)
  set c : ℝ := θ * β T * (unitBallVolume n).toReal with hc
  -- Step 1: `x ∈ U` and `U` is open, so eventually as `t → 0⁺`, `t > 0` and `B_{2t}(x) ⊆ U`.
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hT.1
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ closedBall x (2 * t) ⊆ U := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ)] with t ht
    exact ⟨ht.1, (closedBall_subset_ball (by linarith [ht.2])).trans hδU⟩
  -- Step 2: the cut-off `χ_a(y) = max(0, min(1, (a - |y|)/κ))` is continuous and vanishes off the
  -- compact ball `B_a(0)`, so it is an element of `C_c(ℝ^N)`.
  have hcut : ∀ a κ : ℝ, 0 < κ →
      ∃ g : C_c(Euclidean N, ℝ), ∀ y, g y = max 0 (min 1 ((a - ‖y‖) / κ)) := by
    intro a κ hκ
    refine ⟨⟨⟨fun y ↦ max 0 (min 1 ((a - ‖y‖) / κ)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) a) fun y hy ↦ ?_⟩,
      fun _ ↦ rfl⟩
    have hay : a < ‖y‖ := by simpa using hy
    exact max_eq_left ((min_le_right _ _).trans (div_neg_of_neg_of_pos (by linarith) hκ).le)
  -- Step 3: by `tendsto_order`, show that eventually `a' < J(t)` for each `a' < c`, and
  -- `J(t) < b'` for each `b' > c`.
  rw [show θ * (unitBallVolume n).toReal * β T = c by rw [hc]; ring]
  refine tendsto_order.2 ⟨fun a' ha' ↦ ?_, fun b' hb' ↦ ?_⟩
  · -- Step 4: with `ε = c - a'`, fix `κ ∈ (0,1)` such that `c (1 - κ)^n > c - ε/2`.
    have hε : 0 < c - a' := sub_pos.2 ha'
    have hcont : Tendsto (fun κ : ℝ ↦ c * (1 - κ) ^ n) (𝓝[>] 0) (𝓝 c) := by
      have h : Continuous fun κ : ℝ ↦ c * (1 - κ) ^ n := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨κ, hκc, hκ⟩ := ((hcont.eventually (lt_mem_nhds (sub_lt_self c (half_pos hε)))).and
      (Ioo_mem_nhdsGT one_pos)).exists
    -- (a) `I⁻(t) = t^{-n} ∫ χ⁻(t⁻¹(y - x)) β(S) dV → θ β(T) c⁻` with `c⁻ = ∫_T χ⁻ dHⁿ`.
    obtain ⟨g, hg⟩ := hcut 1 κ hκ.1
    have hlim := Submission.frt_vgm_tba_product_blowup_tendsto N n U V x T θ hT g β
    simp only [hg] at hlim
    -- (b) `c (1 - κ)^n ≤ θ β(T) c⁻`, from `ω_n (1 - κ)^n ≤ c⁻`.
    have hL : c * (1 - κ) ^ n ≤ θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
        max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n]) := by
      calc c * (1 - κ) ^ n = θ * β T * ((unitBallVolume n).toReal * (1 - κ) ^ n) := by
            rw [hc]; ring
        _ ≤ θ * β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n] :=
          mul_le_mul_of_nonneg_left
            (Submission.frt_vgm_tba_plane_cutoff_bounds N n T κ hκ.1 hκ.2).1 hθβ
        _ = _ := mul_assoc _ _ _
    -- (c), (d): eventually `a' < I⁻(t) ≤ J(t)`, the second by the ball cut-off sandwich.
    filter_upwards [hlim.eventually (lt_mem_nhds (sub_lt_self _ (half_pos hε))), hgood]
      with t hI ht
    have hJ := mul_le_mul_of_nonneg_left
      (Submission.frt_vgm_tba_ball_cutoff_sandwich N n U V x β κ t hκ.1 hκ.2 ht.1 ht.2 hβ).1
      (pow_nonneg (inv_nonneg.2 ht.1.le) n)
    linarith
  · -- Step 5: with `ε = b' - c`, fix `κ ∈ (0,1)` such that `c (1 + κ)^n < c + ε/2`.
    have hε : 0 < b' - c := sub_pos.2 hb'
    have hcont : Tendsto (fun κ : ℝ ↦ c * (1 + κ) ^ n) (𝓝[>] 0) (𝓝 c) := by
      have h : Continuous fun κ : ℝ ↦ c * (1 + κ) ^ n := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨κ, hκc, hκ⟩ := ((hcont.eventually
      (gt_mem_nhds (lt_add_of_pos_right c (half_pos hε)))).and (Ioo_mem_nhdsGT one_pos)).exists
    -- (a) `I⁺(t) = t^{-n} ∫ χ⁺(t⁻¹(y - x)) β(S) dV → θ β(T) c⁺` with `c⁺ = ∫_T χ⁺ dHⁿ`.
    obtain ⟨g, hg⟩ := hcut (1 + κ) κ hκ.1
    have hlim := Submission.frt_vgm_tba_product_blowup_tendsto N n U V x T θ hT g β
    simp only [hg] at hlim
    -- (b) `θ β(T) c⁺ ≤ c (1 + κ)^n`, from `c⁺ ≤ ω_n (1 + κ)^n`.
    have hU : θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
        max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n]) ≤ c * (1 + κ) ^ n := by
      calc θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n])
          = θ * β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n] := (mul_assoc _ _ _).symm
        _ ≤ θ * β T * ((unitBallVolume n).toReal * (1 + κ) ^ n) :=
          mul_le_mul_of_nonneg_left
            (Submission.frt_vgm_tba_plane_cutoff_bounds N n T κ hκ.1 hκ.2).2 hθβ
        _ = c * (1 + κ) ^ n := by rw [hc]; ring
    -- (c), (d): eventually `J(t) ≤ I⁺(t) < b'`, the first by the ball cut-off sandwich.
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε))), hgood]
      with t hI ht
    have hJ := mul_le_mul_of_nonneg_left
      (Submission.frt_vgm_tba_ball_cutoff_sandwich N n U V x β κ t hκ.1 hκ.2 ht.1 ht.2 hβ).2
      (pow_nonneg (inv_nonneg.2 ht.1.le) n)
    linarith

/-- Averages over balls at a tangent plane (Simon Ch. 8, proof of 1.2, p. 208, with the erratum
`η_V^{(x)}(β) = β(T_x)`): if `V` has tangent plane `T` with multiplicity `θ` at `x` (Def. 1.1),
then `μ_V(B_ρ(x))⁻¹ ∫_{Gₙ(B_ρ(x))} β(S) dV(y,S) → β(T)` as `ρ ↓ 0` for every continuous `β` on
`G(N,n)`.  The multiplicity cancels because the averages are normalised by `μ_V(B_ρ(x))`. -/
theorem Submission.frt_vgm_tangent_ball_average :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (β T)) := by
  intro N n U V x T θ hT β
  -- Step 1: `ω_n = (unitBallVolume n).toReal` is positive (the unit ball has positive, finite
  -- volume).
  have hω : 0 < (unitBallVolume n).toReal := by
    rw [unitBallVolume]
    exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
      measure_ball_lt_top.ne
  -- Step 2: `x ∈ U` and `U` is open, so for small `t > 0` the closed ball `B_t(x)` is a compact
  -- subset of `U`, hence `V(B_t(x) × G(N,n)) < ∞`.
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hT.1
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      V.measure (closedBall x t ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    exact V.finite_on_compact _ (isCompact_closedBall x t)
      ((closedBall_subset_ball ht.2).trans hδU)
  -- Step 8: `β = β⁺ - β⁻` with `β⁺ = max(β, 0)` and `β⁻ = max(-β, 0)` continuous and `≥ 0`. The
  -- sibling `nonneg_ball_limit` gives `t^{-n} ∫_{Gₙ(B_t(x))} β^± dV → θ ω_n β^±(T)`, and the ball
  -- integrals split once `V(B_t(x) × G(N,n)) < ∞`.
  let βp : C(Grassmannian N n, ℝ) := ⟨fun S ↦ max (β S) 0, β.continuous.max continuous_const⟩
  let βm : C(Grassmannian N n, ℝ) := ⟨fun S ↦ max (-β S) 0, β.continuous.neg.max continuous_const⟩
  have hβpm : ∀ S, βp S - βm S = β S := fun S ↦ max_zero_sub_max_neg_zero_eq_self (β S)
  have hnum : Tendsto (fun t : ℝ ↦ t⁻¹ ^ n *
      ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) (𝓝[>] 0)
      (𝓝 (θ * (unitBallVolume n).toReal * β T)) := by
    have hlim := (Submission.frt_vgm_tba_nonneg_ball_limit N n U V x T θ hT βp
      fun _ ↦ le_max_right _ _).sub
      (Submission.frt_vgm_tba_nonneg_ball_limit N n U V x T θ hT βm fun _ ↦ le_max_right _ _)
    rw [← mul_sub, hβpm] at hlim
    refine hlim.congr' ?_
    filter_upwards [hfin] with t ht
    have hint : ∀ γ : C(Grassmannian N n, ℝ), IntegrableOn (fun z : Euclidean N ×
        Grassmannian N n ↦ γ z.2) (closedBall x t ×ˢ (univ : Set (Grassmannian N n))) V.measure :=
      fun γ ↦ Measure.integrableOn_of_bounded ht
        (γ.continuous.comp continuous_snd).aestronglyMeasurable
        (ae_of_all _ fun z ↦ γ.norm_coe_le_norm z.2)
    rw [← mul_sub, ← integral_sub (hint βp) (hint βm)]
    simp only [hβpm]
  -- Step 9: `β ≡ 1` gives the weight, since
  -- `∫_{Gₙ(B_t(x))} 1 dV = V(B_t(x) × G(N,n)) = μ_V(B_t(x))`; so `t^{-n} μ_V(B_t(x)) → θ ω_n ≠ 0`.
  have hden : Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * (V.weight (closedBall x t)).toReal) (𝓝[>] 0)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    have h1 := Submission.frt_vgm_tba_nonneg_ball_limit N n U V x T θ hT
      (ContinuousMap.const _ 1) fun _ ↦ zero_le_one
    simp only [ContinuousMap.const_apply, mul_one] at h1
    refine h1.congr fun t ↦ ?_
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      V.weight_apply measurableSet_closedBall]
  have hne : θ * (unitBallVolume n).toReal ≠ 0 := (mul_pos hT.2.1 hω).ne'
  -- Step 10: divide.  The factor `t^{-n} ≠ 0` cancels for `t > 0`, and `θ ω_n` cancels in the
  -- limit.
  have hratio := hnum.div hden hne
  rw [mul_div_cancel_left₀ _ hne] at hratio
  refine hratio.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Pi.div_apply]
  exact mul_div_mul_left _ _ (pow_ne_zero n (inv_ne_zero (ne_of_gt ht)))

/-- The closed-ball mass `x ↦ μ(B_r(x))` of an s-finite measure `μ` on `ℝ^N` is Borel measurable for
every radius `r` (used with `μ = μ_V` for the Borel choice of `x ↦ T_x` in Simon Ch. 8, proof of
1.2). -/
theorem Submission.frt_vgm_mps_weight_closedBall_measurable :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)), SFinite μ → ∀ r : ℝ, Measurable (fun x : Euclidean N ↦ μ (closedBall x r)) := by
  intro N μ hμ r
  -- Steps 1–2: `D_r = {(x, y) : dist y x ≤ r}` is closed in `ℝ^N × ℝ^N`, hence measurable.
  have hD : MeasurableSet {p : Euclidean N × Euclidean N | dist p.2 p.1 ≤ r} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  -- Step 3: the slice of `D_r` at `x` is `closedBall x r`.
  have hslice (x : Euclidean N) :
      Prod.mk x ⁻¹' {p : Euclidean N × Euclidean N | dist p.2 p.1 ≤ r} = closedBall x r :=
    Set.ext fun _ ↦ mem_closedBall.symm
  -- Steps 4–5: `μ` is s-finite, so `x ↦ μ (Prod.mk x ⁻¹' D_r) = μ (closedBall x r)` is measurable.
  simpa only [hslice] using measurable_measure_prodMk_left (ν := μ) hD

/-- The ball integral `x ↦ ∫_{B_r(x) × G(N,n)} β(S) dν(y,S)` is Borel measurable for every
s-finite measure `ν` on `ℝ^N × G(N,n)`, every `r` and every continuous `β` (step 3 of the Borel
choice of `x ↦ T_x` in the proof of Simon Ch. 8, 1.2): it equals
`x ↦ ∫ 1_{E_r}(x, z) β(z.2) dν(z)` for the closed set `E_r = {(x, z) : |z.1 - x| ≤ r}`, which is
measurable in `x` by `StronglyMeasurable.integral_prod_right'`. -/
theorem Submission.frt_vgm_mps_ball_integral_measurable :
    ∀ (N n : ℕ) (ν : Measure (Euclidean N × Grassmannian N n)), SFinite ν → ∀ (r : ℝ) (β : C(Grassmannian N n, ℝ)), Measurable (fun x : Euclidean N ↦ ∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂ν) := by
  intro N n ν hν r β
  -- Steps 1–2: `E_r = {(x, z) | dist z.1 x ≤ r}` is closed in `ℝ^N × (ℝ^N × G(N,n))`, hence
  -- measurable (the factors are second countable).
  have hE : IsClosed {p : Euclidean N × (Euclidean N × Grassmannian N n) | dist p.2.1 p.1 ≤ r} :=
    isClosed_le ((continuous_fst.comp continuous_snd).dist continuous_fst) continuous_const
  -- Step 3: `F = 1_{E_r}(x, z) β(z.2)` is measurable, hence strongly measurable.
  have hF : StronglyMeasurable
      ({p : Euclidean N × (Euclidean N × Grassmannian N n) | dist p.2.1 p.1 ≤ r}.indicator
        fun p ↦ β p.2.2) :=
    ((β.continuous.measurable.comp (measurable_snd.comp measurable_snd)).indicator
      hE.measurableSet).stronglyMeasurable
  -- Step 4: `ν` is s-finite, so `x ↦ ∫ F(x, z) dν(z)` is (strongly) measurable.
  convert (hF.integral_prod_right' (ν := ν)).measurable using 1
  -- Steps 5–6: by `integral_indicator` the ball integral at `x` is `∫ 1_{B_r(x) × G}(z) β(z.2) dν`,
  -- and `1_{B_r(x) × G}(z) β(z.2) = F(x, z)` for every `z`.
  funext x
  rw [← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  congr 1
  funext z
  simp [Set.indicator, Set.mem_prod, Metric.mem_closedBall]

/-- Measurable selection of entrywise limits in `G(N,n)` (the Borel version of `x ↦ T_x` in Simon
Ch. 8, proof of 1.2, p. 208): if every entry `x ↦ a_k(x)_{ij}` is measurable, there is a measurable
`τ : X → G(N,n)` with `τ x = T` whenever `a_k(x)_{ij} → T_{ij}` as `k → ∞` for all `i, j`. -/
theorem Submission.frt_vgm_mps_limit_selection :
    ∀ (X : Type) [MeasurableSpace X] (N n : ℕ), Nonempty (Grassmannian N n) → ∀ (a : ℕ → X → Fin N → Fin N → ℝ), (∀ (k : ℕ) (i j : Fin N), Measurable (fun x ↦ a k x i j)) → ∃ τ : X → Grassmannian N n, Measurable τ ∧ ∀ (x : X) (T : Grassmannian N n), (∀ i j : Fin N, Tendsto (fun k ↦ a k x i j) atTop (𝓝 (T.1 i j))) → τ x = T := by
  intro X _ N n hne a ha
  classical
  -- Step 1: a base point `S₀`; the projection set `𝒢` is closed, hence measurable.
  obtain ⟨S₀⟩ := hne
  have hG : MeasurableSet
      {P : Matrix (Fin N) (Fin N) ℝ | P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)} :=
    Grassmannian.isClosed_projectionSet.measurableSet
  -- Step 2: the convergence sets `C^{ij}` are measurable.
  have hC : ∀ i j : Fin N, MeasurableSet {x | ∃ c, Tendsto (fun k ↦ a k x i j) atTop (𝓝 c)} :=
    fun i j ↦ measurableSet_exists_tendsto fun k ↦ ha k i j
  -- Step 3: the entrywise limits `L^{ij}` are measurable.
  have hL : ∀ i j : Fin N, Measurable fun x ↦ limUnder atTop fun k ↦ a k x i j :=
    fun i j ↦ (StronglyMeasurable.limUnder fun k ↦ (ha k i j).stronglyMeasurable).measurable
  -- Step 4: the limit matrix `M` is measurable.
  obtain ⟨M, hM_def⟩ : ∃ M : X → Matrix (Fin N) (Fin N) ℝ,
      M = fun x ↦ Matrix.of fun i j ↦ limUnder atTop fun k ↦ a k x i j := ⟨_, rfl⟩
  have hM : Measurable M := Measurable.of_eval_matrix M fun i j ↦ by simpa [hM_def] using hL i j
  -- Step 5: the good set `Y` is measurable.
  obtain ⟨Y, hY_def⟩ : ∃ Y : Set X, Y = (⋂ i, ⋂ j, {x | ∃ c, Tendsto (fun k ↦ a k x i j) atTop (𝓝 c)}) ∩
      M ⁻¹' {P | P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)} := ⟨_, rfl⟩
  have hY : MeasurableSet Y := hY_def ▸
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ hC i j).inter (hM hG)
  -- Step 6: `τ x := ⟨Y.piecewise M (fun _ ↦ S₀.1) x, _⟩` is a measurable `G(N,n)`-valued map.
  have hmem : ∀ x, Y.piecewise M (fun _ ↦ S₀.1) x ∈
      {P : Matrix (Fin N) (Fin N) ℝ | P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)} := by
    intro x
    by_cases hx : x ∈ Y
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      rw [hY_def] at hx
      exact hx.2
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact S₀.2
  refine ⟨fun x ↦ ⟨Y.piecewise M (fun _ ↦ S₀.1) x, hmem x⟩,
    (Measurable.piecewise hY hM measurable_const).subtype_mk, ?_⟩
  -- Step 7: if every entry converges to that of `T`, then `M x = T`, `x ∈ Y` and `τ x = T`.
  intro x T hT
  have hMx : M x = T.1 := by
    ext i j
    rw [hM_def]
    exact (hT i j).limUnder_eq
  have hxY : x ∈ Y := by
    rw [hY_def]
    refine ⟨Set.mem_iInter.2 fun i ↦ Set.mem_iInter.2 fun j ↦ ⟨T.1 i j, hT i j⟩, ?_⟩
    rw [Set.mem_preimage, hMx]
    exact T.2
  exact Subtype.ext ((Set.piecewise_eq_of_mem Y M (fun _ ↦ S₀.1) hxY).trans hMx)

/-- A Borel selection of the plane determined by ball averages (the Borel version `T̃` of
`x ↦ T_x` needed in the proof of Simon Ch. 8, 1.2, p. 208): there is a measurable
`τ : ℝ^N → G(N,n)` with `τ x = T` whenever the averages of every continuous `β` over `Gₙ(B_ρ(x))`
tend to `β T` as `ρ ↓ 0`.  The averages of the matrix entries `S ↦ S_{ij}` along `ρ_k = 1/(k+1)`
are measurable in `x`, and `τ` selects their entrywise limit. -/
theorem Submission.frt_vgm_measurable_plane_selection :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), Nonempty (Grassmannian N n) → ∃ τ : Euclidean N → Grassmannian N n, Measurable τ ∧ ∀ (x : Euclidean N) (T : Grassmannian N n), (∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (β T))) → τ x = T := by
  intro N n U V hG
  -- Step 1: the matrix-entry functions `e_{ij}(S) = S_{ij}` are continuous on `G(N,n)`, and the
  -- radii are `ρ_k = 1/(k+1)`.
  let e : Fin N → Fin N → C(Grassmannian N n, ℝ) := fun i j ↦
    ⟨fun S ↦ S.1 i j, (continuous_id.matrix_elem i j).comp continuous_subtype_val⟩
  let ρ : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  -- Steps 2–4: the averages `a_k(x)_{ij} = (∫_{B_{ρ_k}(x) × G} e_{ij} dV) / μ_V(B_{ρ_k}(x))` are
  -- measurable in `x` (`V.measure` and `V.weight` are σ-finite, hence s-finite).
  -- Steps 5–6: a measurable selection `τ` of their entrywise limits.
  obtain ⟨τ, hτm, hτ⟩ := Submission.frt_vgm_mps_limit_selection (Euclidean N) N n hG
    (fun k x i j ↦ (∫ z in closedBall x (ρ k) ×ˢ (univ : Set (Grassmannian N n)),
      e i j z.2 ∂V.measure) / (V.weight (closedBall x (ρ k))).toReal)
    (fun k i j ↦ (Submission.frt_vgm_mps_ball_integral_measurable N n V.measure inferInstance
      (ρ k) (e i j)).div
        (Submission.frt_vgm_mps_weight_closedBall_measurable N V.weight inferInstance
          (ρ k)).ennreal_toReal)
  refine ⟨τ, hτm, fun x T hT ↦ hτ x T fun i j ↦ ?_⟩
  -- Step 7: `ρ_k → 0⁺`, so the hypothesis for `β = e_{ij}` gives `a_k(x)_{ij} → T_{ij}`.
  have hρ : Tendsto ρ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall fun k ↦ by simp only [Set.mem_Ioi, ρ]; positivity)
  exact (hT (e i j)).comp hρ

/-- A finite Borel measure on a pseudo-metrizable space is determined by the lower integrals of
nonnegative continuous functions (the uniqueness step behind "from the arbitrariness of `A` and `β`
it then easily follows" in the proof of Simon Ch. 8, 1.2, p. 208): each closed `F` is approximated
by `max 0 (1 - (j + 1) d(·, F))`, and closed sets form a π-system generating the Borel σ-algebra. -/
theorem Submission.frt_vgm_ext_finite_of_lintegral_continuous :
    ∀ (X : Type) [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X] (m₁ m₂ : Measure X), IsFiniteMeasure m₁ → (∀ β : C(X, ℝ), (∀ x, 0 ≤ β x) → ∫⁻ x, ENNReal.ofReal (β x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (β x) ∂m₂) → m₁ = m₂ := by
  intro X _ _ _ _ m₁ m₂ h₁ hβ
  -- Step 1: a pseudometric `d` inducing the topology of `X`.
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  -- Step 2: testing with `β ≡ 1`, `m₁ X = m₂ X`, so `m₂` is finite as well.
  have huniv : m₁ univ = m₂ univ := by
    simpa using hβ (ContinuousMap.const X 1) fun _ ↦ zero_le_one
  have h₂ : IsFiniteMeasure m₂ := ⟨huniv ▸ measure_lt_top m₁ univ⟩
  -- Step 3: `m₁ F = m₂ F` for every closed `F`.
  have hclosed : ∀ F : Set X, IsClosed F → m₁ F = m₂ F := by
    intro F hF
    -- (a) `F = ∅`.
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · simp
    -- (b)–(c) with `d_F = infDist · F` continuous, the cutoffs `β_j = max 0 (1 - (j + 1) d_F)`
    -- are continuous and `0 ≤ β_j ≤ 1`.
    let β : ℕ → C(X, ℝ) := fun j ↦
      ⟨fun x ↦ max 0 (1 - ((j : ℝ) + 1) * infDist x F),
        continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_infDist_pt F)))⟩
    have hβ0 : ∀ j x, 0 ≤ β j x := fun j x ↦ le_max_left _ _
    have hβ1 : ∀ j x, ENNReal.ofReal (β j x) ≤ 1 := by
      intro j x
      refine ENNReal.ofReal_le_one.2 (max_le zero_le_one ?_)
      have : 0 ≤ ((j : ℝ) + 1) * infDist x F := mul_nonneg (by positivity) infDist_nonneg
      linarith
    have hmeas : ∀ j, Measurable fun x ↦ ENNReal.ofReal (β j x) :=
      fun j ↦ ENNReal.measurable_ofReal.comp (β j).continuous.measurable
    -- (d) `ofReal ∘ β_j → 1_F` pointwise.
    have hlim : ∀ x, Tendsto (fun j ↦ ENNReal.ofReal (β j x)) atTop (𝓝 (F.indicator 1 x)) := by
      intro x
      by_cases hx : x ∈ F
      · have h1 : ∀ j, ENNReal.ofReal (β j x) = 1 := by
          intro j
          show ENNReal.ofReal (max 0 (1 - ((j : ℝ) + 1) * infDist x F)) = 1
          simp [infDist_zero_of_mem hx]
        simp only [h1, indicator_of_mem hx, Pi.one_apply]
        exact tendsto_const_nhds
      · have hpos : 0 < infDist x F := (hF.notMem_iff_infDist_pos hFne).1 hx
        obtain ⟨j₀, hj₀⟩ := exists_nat_gt (infDist x F)⁻¹
        rw [indicator_of_notMem hx]
        refine tendsto_atTop_of_eventually_const (i₀ := j₀) fun j hj ↦ ?_
        have hj' : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
        have h1 : 1 < ((j : ℝ) + 1) * infDist x F := by
          calc (1 : ℝ) = (infDist x F)⁻¹ * infDist x F := (inv_mul_cancel₀ hpos.ne').symm
            _ < ((j : ℝ) + 1) * infDist x F := mul_lt_mul_of_pos_right (by linarith) hpos
        show ENNReal.ofReal (max 0 (1 - ((j : ℝ) + 1) * infDist x F)) = 0
        rw [max_eq_left (by linarith), ENNReal.ofReal_zero]
    -- (e) dominated convergence with the bound `1` for a finite measure.
    have key : ∀ m : Measure X, IsFiniteMeasure m →
        Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal (β j x) ∂m) atTop (𝓝 (m F)) := by
      intro m hm
      have := tendsto_lintegral_of_dominated_convergence (μ := m) (fun _ ↦ 1) hmeas
        (fun j ↦ ae_of_all _ (hβ1 j)) (by simp) (ae_of_all _ hlim)
      rwa [lintegral_indicator_one hF.measurableSet] at this
    -- (f) uniqueness of limits.
    exact tendsto_nhds_unique (key m₁ h₁)
      ((key m₂ h₂).congr fun j ↦ (hβ (β j) (hβ0 j)).symm)
  -- Step 4: closed sets form a π-system generating the Borel σ-algebra.
  refine ext_of_generate_finite {s | IsClosed s} ?_ isPiSystem_isClosed hclosed huniv
  rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]

/-- Uniqueness of measures on `X × Y` from rectangles with `μ`-finite base (Step 5 of the proof
that a varifold is determined by its graph measure): if `μ` is σ-finite, `ρ₁` is finite on the
cylinders `A × Y` with `μ(A) < ∞`, and `ρ₁`, `ρ₂` agree on the rectangles `A × B` with
`μ(A) < ∞`, then `ρ₁ = ρ₂` (Dynkin's π-λ theorem, `Measure.ext_of_generateFrom_of_iUnion`). -/
theorem Submission.frt_vgm_ext_prod_of_finite_rectangles :
    ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ρ₁ ρ₂ : Measure (X × Y)), SigmaFinite μ → (∀ A : Set X, MeasurableSet A → μ A ≠ ∞ → ρ₁ (A ×ˢ (univ : Set Y)) ≠ ∞) → (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B → μ A ≠ ∞ → ρ₁ (A ×ˢ B) = ρ₂ (A ×ˢ B)) → ρ₁ = ρ₂ := by
  intro X Y _ _ μ ρ₁ ρ₂ hμ hfin hrect
  -- Step 1: the spanning sets `E m` of `μ` are measurable, of finite measure, and cover `X`.
  have hE : ∀ m, MeasurableSet (spanningSets μ m) ∧ μ (spanningSets μ m) ≠ ∞ :=
    fun m ↦ ⟨measurableSet_spanningSets μ m, (measure_spanningSets_lt_top μ m).ne⟩
  -- Step 2: `C` is the class of rectangles `A ×ˢ B` with `A, B` measurable and `μ A ≠ ∞`.
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {A : Set X | MeasurableSet A ∧ μ A ≠ ∞} {B : Set Y | MeasurableSet B})
    (fun m ↦ spanningSets μ m ×ˢ univ) ?_ ?_ ?_ ?_ ?_ ?_
  · -- Step 4: `C` generates the product σ-algebra.
    refine le_antisymm (generateFrom_prod.symm.le.trans (MeasurableSpace.generateFrom_le ?_))
      (MeasurableSpace.generateFrom_le ?_)
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      have hAB : A ×ˢ B = ⋃ m, (A ∩ spanningSets μ m) ×ˢ B := by
        rw [← iUnion_prod_const, ← inter_iUnion, iUnion_spanningSets, inter_univ]
      dsimp only
      rw [hAB]
      exact MeasurableSet.iUnion fun m ↦ MeasurableSpace.measurableSet_generateFrom
        ⟨A ∩ spanningSets μ m, ⟨hA.inter (hE m).1,
          ne_top_of_le_ne_top (hE m).2 (measure_mono inter_subset_right)⟩, B, hB, rfl⟩
    · rintro _ ⟨A, ⟨hA, -⟩, B, hB, rfl⟩
      exact hA.prod hB
  · -- Step 3: `C` is a π-system.
    rintro _ ⟨A, ⟨hA, hμA⟩, B, hB, rfl⟩ _ ⟨A', ⟨hA', -⟩, B', hB', rfl⟩ -
    rw [prod_inter_prod]
    exact ⟨A ∩ A', ⟨hA.inter hA', ne_top_of_le_ne_top hμA (measure_mono inter_subset_left)⟩,
      B ∩ B', hB.inter hB', rfl⟩
  · -- Step 5: the cylinders `E m ×ˢ univ` cover `X × Y` ...
    rw [← iUnion_prod_const, iUnion_spanningSets, univ_prod_univ]
  · -- ... lie in `C` ...
    exact fun m ↦ ⟨spanningSets μ m, hE m, univ, MeasurableSet.univ, rfl⟩
  · -- ... and have finite `ρ₁`-measure.
    exact fun m ↦ hfin _ (hE m).1 (hE m).2
  · -- Step 6: `ρ₁` and `ρ₂` agree on `C`.
    rintro _ ⟨A, ⟨hA, hμA⟩, B, hB, rfl⟩
    exact hrect A B hA hB hμA

/-- Graph-measure extensionality (Simon Ch. 8, proof of 1.2, p. 208: "from the arbitrariness of
`A` and `β`"): if `∫_{Gₙ(A)} β(S) dV(y,S) = ∫_A β(τ(x)) dμ_V(x)` for every Borel `A ⊆ ℝ^N` and
every continuous `β ≥ 0` on `G(N,n)`, then `V = (μ_V)_#(x ↦ (x, τ(x)))`. -/
theorem Submission.frt_vgm_eq_map_graph_of_lintegral :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (τ : Euclidean N → Grassmannian N n), Measurable τ → (∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, ENNReal.ofReal (β (τ x)) ∂V.weight) → V.measure = V.weight.map (fun x ↦ (x, τ x)) := by
  intro N n U V τ hτ hH
  -- Step 1: the graph map `x ↦ (x, τ x)` is measurable.
  have hg : Measurable fun x : Euclidean N ↦ (x, τ x) := measurable_id.prodMk hτ
  -- Step 5: `μ_V` is σ-finite and `V(A ×ˢ G) = μ_V(A)`, so it suffices to compare `V` with
  -- `(μ_V)_#(x ↦ (x, τ x))` on rectangles `A ×ˢ B` with `μ_V(A) < ∞`.
  refine Submission.frt_vgm_ext_prod_of_finite_rectangles (Euclidean N) (Grassmannian N n)
    V.weight V.measure (V.weight.map fun x ↦ (x, τ x)) inferInstance
    (fun A hA hAfin ↦ by rwa [← V.weight_apply hA]) fun A B hA hB hAfin ↦ ?_
  -- Step 2: the slice measures `m₁(B) = V(A ×ˢ B)` and `m₂(B) = μ_V(A ∩ τ⁻¹ B)` on `G(N,n)`.
  have hm₁B : (V.measure.restrict (A ×ˢ univ)).map Prod.snd B = V.measure (A ×ˢ B) := by
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 1
    ext z
    simp [and_comm]
  have hm₂B : (V.weight.restrict A).map τ B = V.weight (A ∩ τ ⁻¹' B) := by
    rw [Measure.map_apply hτ hB, Measure.restrict_apply (hτ hB), inter_comm]
  -- `m₁` is finite: `m₁(G) = V(A ×ˢ G) = μ_V(A) < ∞`.
  have hfin : IsFiniteMeasure ((V.measure.restrict (A ×ˢ univ)).map Prod.snd) := by
    have : IsFiniteMeasure (V.measure.restrict (A ×ˢ univ)) :=
      isFiniteMeasure_restrict.2 (by rwa [← V.weight_apply hA])
    infer_instance
  -- Steps 3–4: equal integrals of every continuous `β ≥ 0` force `m₁ = m₂`.
  have hm : (V.measure.restrict (A ×ˢ univ)).map Prod.snd = (V.weight.restrict A).map τ := by
    refine Submission.frt_vgm_ext_finite_of_lintegral_continuous (Grassmannian N n) _ _ hfin
      fun β hβ ↦ ?_
    have hβm : Measurable fun S ↦ ENNReal.ofReal (β S) :=
      ENNReal.measurable_ofReal.comp β.continuous.measurable
    rw [lintegral_map hβm measurable_snd, lintegral_map hβm hτ]
    exact hH A β hA hβ
  rw [← hm₁B, hm, hm₂B, Measure.map_apply hg (hA.prod hB)]
  rfl

/-- **A varifold with tangent planes `μ_V`-a.e. is the graph measure of its tangent planes**
(Simon Ch. 8, proof of 1.2, p. 208, printed (1)–(2), with the corrected `η_V^(x)(β) = β(T_x)`).
Let `η` satisfy the conclusions of Lemma 1.3, and let `V` have a tangent plane at `μ_V`-a.e. `x`.
Then for every Borel `A ⊆ ℝ^N × G(N,n)` the set `S_A = {x : (x, T_x) ∈ A}` is
`μ_V`-null-measurable and `V(A) = μ_V(S_A)`.  At a tangent point the ball averages tend to
`β(T_x)`, so `∫ β dη(x) = β(T_x)` for `μ_V`-a.e. `x`.  With a Borel selection `τ` of `x ↦ T_x`,
the second part of 1.3 becomes identity (1), hence `V = (μ_V)_#(x ↦ (x, τ x))`. -/
theorem Submission.frt_varifold_eq_tangent_graph_measure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), (∃ η : Euclidean N → Measure (Grassmannian N n), (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) ∧ ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight) → (∀ᵐ x ∂V.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ) → ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → NullMeasurableSet {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A} V.weight ∧ V.measure A = V.weight {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A} := by
  intro N n U V hη htan A hA
  obtain ⟨η, hη₁, hη₂⟩ := hη
  -- Step 0: if `G(N,n) = ∅`, then `S_A = ∅` and `A = ∅`.
  rcases isEmpty_or_nonempty (Grassmannian N n) with hG | hG
  · have hS : {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A} = ∅ :=
      eq_empty_of_forall_notMem fun _ ⟨T, _⟩ ↦ hG.elim T
    have hA₀ : A = ∅ := eq_empty_of_forall_notMem fun z _ ↦ hG.elim z.2
    rw [hS, hA₀]
    simp
  -- Step 1: a Borel `τ : ℝ^N → G(N,n)` with `τ x = T` whenever the averages tend to `β(T)`.
  obtain ⟨τ, hτm, hτ⟩ := Submission.frt_vgm_measurable_plane_selection N n U V hG
  -- Step 2: at a tangent point the averages tend to `β(T)`, so `τ x = T`.
  have hτT : ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ),
      HasTangentPlane V x T θ → τ x = T := fun x T θ hT ↦
    hτ x T (Submission.frt_vgm_tangent_ball_average N n U V x T θ hT)
  -- Step 3: identity (1).  For `μ_V`-a.e. `x`, `η(x)` is a probability measure and
  -- `∫ β dη(x) = β(T_x) = β(τ x)` by uniqueness of limits as `ρ ↓ 0`.
  have hid : ∀ (A' : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A' →
      (∀ S, 0 ≤ β S) →
      ∫⁻ z in A' ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure =
        ∫⁻ x in A', ENNReal.ofReal (β (τ x)) ∂V.weight := by
    intro A' β hA' hβ
    rw [hη₂ A' β hA' hβ]
    refine setLIntegral_congr_fun_ae hA' ?_
    filter_upwards [hη₁, htan] with x hx htx _
    obtain ⟨hprob, hlim⟩ := hx
    obtain ⟨T, θ, hT⟩ := htx
    have hβT : ∫ S, β S ∂(η x) = β T :=
      tendsto_nhds_unique (hlim β) (Submission.frt_vgm_tangent_ball_average N n U V x T θ hT β)
    rw [hτT x T θ hT, ← hβT, ofReal_integral_eq_lintegral_ofReal
      (β.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall hβ)]
  -- Step 4: hence `V = (μ_V)_#(x ↦ (x, τ x))` (printed (2)).
  have hV := Submission.frt_vgm_eq_map_graph_of_lintegral N n U V τ hτm hid
  -- Step 5: `S_A` agrees `μ_V`-a.e. with the Borel set `{x : (x, τ x) ∈ A}`, since `τ x = T` at
  -- every tangent pair `(x, T)` and tangent points have full `μ_V`-measure.
  have hg : Measurable fun x ↦ (x, τ x) := measurable_id.prodMk hτm
  have hAe : {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧ (x, T) ∈ A}
      =ᵐ[V.weight] (fun x ↦ (x, τ x)) ⁻¹' A := by
    filter_upwards [htan] with x htx
    obtain ⟨T, θ, hT⟩ := htx
    refine propext ⟨fun ⟨T', θ', hT', hmem⟩ ↦ ?_, fun hmem ↦ ⟨T, θ, hT, ?_⟩⟩
    · show (x, τ x) ∈ A
      rwa [hτT x T' θ' hT']
    · rwa [← hτT x T θ hT]
  refine ⟨(hg hA).nullMeasurableSet.congr hAe.symm, ?_⟩
  rw [hV, Measure.map_apply hg hA, measure_congr hAe]

/-- **At a tangent point the density equals the multiplicity** (child `tangent_plane_density` of
`allard_tangent_cones`; Simon Ch. 8, 1.1 with Ch. 1, 3.1): if `V` has tangent plane `T` with
multiplicity `θ` at `x`, then `Θ^n(μ_V, x) = θ`.  Child `flat_blowup_ball_limits` along `t = id` on
`𝓝[>] 0` gives `μ_V(B_ρ(x)) / ρ^n → θ ω_n`.  For `B_ρ(x) ⊆ U` the ball mass is finite, so with
`0 < ω_n < ∞` the density ratio is `ofReal (μ_V(B_ρ(x)) / ρ^n / ω_n)`; continuity of `ofReal`
concludes. -/
theorem Submission.allard_tc_tangent_plane_density :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → HasDensity n V.weight x (ENNReal.ofReal θ) := by
  intro N n U V x T θ hT
  obtain ⟨hxU, -, hconv⟩ := hT
  -- `0 < ω_n < ∞`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hω : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0 hωtop
  -- `μ_V(B_ρ(x)) / ρ^n → θ ω_n` as `ρ ↓ 0`.
  have hball : Tendsto (fun ρ : ℝ ↦ (V.weight (closedBall x ρ)).toReal / ρ ^ n) (𝓝[>] 0)
      (𝓝 (θ * (unitBallVolume n).toReal)) :=
    (Submission.allard_tc_flat_blowup_ball_limits N n U V x T θ (𝓝[>] 0) id hxU tendsto_id
      hconv).2
  -- Hence `ofReal (μ_V(B_ρ(x)) / ρ^n / ω_n) → ofReal θ`.
  have hlim := ENNReal.tendsto_ofReal (hball.div_const (unitBallVolume n).toReal)
  rw [mul_div_cancel_right₀ θ hω.ne'] at hlim
  -- On `(0, δ)` with `B_δ(x) ⊆ U` this is the density ratio.
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hxU
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hfin : V.weight (closedBall x ρ) ≠ ∞ := V.weight_finite_on_compact _
    (isCompact_closedBall x ρ) ((closedBall_subset_ball hρ.2).trans hδU)
  have hden : unitBallVolume n * ENNReal.ofReal ρ ^ n =
      ENNReal.ofReal ((unitBallVolume n).toReal * ρ ^ n) := by
    rw [ENNReal.ofReal_mul hω.le, ENNReal.ofReal_pow hρ.1.le, ENNReal.ofReal_toReal hωtop]
  rw [densityRatio, hden, div_div, mul_comm (ρ ^ n),
    ENNReal.ofReal_div_of_pos (mul_pos hω (pow_pos hρ.1 n)), ENNReal.ofReal_toReal hfin]
/-- **Simon Ch. 8, 2.2–2.10** (child `first_variation` of `main_theorem`): the mass derivative of a
deformation is `δV(X)` (2.2–2.4), and locally bounded first variation gives `‖δV‖`, the polar field,
the density `D_{μ_V}‖δV‖`, the generalized boundary and the decomposition 2.10 (2.5–2.10).
Both parts are SimonGMT's kernel-checked theorems; `variationMeasure V` unfolds to its Riesz
measure, which turns the contract's density, boundary and mean curvature into SimonGMT's
symmetric ones. -/
theorem Submission.first_variation_theorems :
    FirstVariationIsMassDerivative ∧ FirstVariationRepresentation := by
  refine ⟨⟨fun N n U V φ K X hK hKU hφ hzero hmaps hfix hX ↦ ?_,
    fun N n X x S b ↦ Varifold.tangentialDivergence_eq_sum_inner X x S b⟩, ?_⟩
  · exact V.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity φ hφ hzero K hK hKU
      (fun t ht ↦ (hmaps t ht).1) (fun t ht ↦ (hmaps t ht).2) hfix X (fun x hx ↦ (hX x hx).deriv)
  · intro N n U V hV
    have hμ : variationMeasure V = V.firstVariationRieszMeasure hV := dite_eq_left hV
    have hD : variationDensity V =
        V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure hV) := by
      funext x
      rw [variationDensity, Varifold.symmetricFirstVariationDensity, hμ]
    have hZ : generalizedBoundary V =
        V.symmetricGeneralizedBoundarySet (V.firstVariationRieszMeasure hV) := by
      rw [generalizedBoundary, Varifold.symmetricGeneralizedBoundarySet, hD]
    have hσ : generalizedBoundaryMeasure V =
        V.symmetricGeneralizedBoundaryMeasure (V.firstVariationRieszMeasure hV) := by
      rw [generalizedBoundaryMeasure, Varifold.symmetricGeneralizedBoundaryMeasure, hμ, hZ]
    have hH : generalizedMeanCurvature V =
        V.symmetricGeneralizedMeanCurvature (V.firstVariationRieszMeasure hV) := by
      funext ν x
      rw [generalizedMeanCurvature, Varifold.symmetricGeneralizedMeanCurvature, hD]
    rw [hH, hσ, hZ, hD, hμ]
    refine ⟨V.isFirstVariationMeasure_riesz hV, ?_, (V.firstVariationRiesz_boundary_spec hV).2.1,
      V.firstVariationPolarField hV, V.measurable_firstVariationPolarField hV,
      V.ae_firstVariationPolarField_norm_one hV, fun X ↦ ?_⟩
    · filter_upwards [(V.firstVariationRiesz_symmetricDensity_spec hV).2] with x hx
      exact ⟨hx.2, hx.1⟩
    · obtain ⟨hint, hform⟩ := (V.isFirstVariationPolarRepresentation_riesz hV).2.2 X
      obtain ⟨hHint, hσint⟩ := V.firstVariationRiesz_integrable_meanCurvature_and_boundary hV X
      refine ⟨hint, hform, hHint, hσint, ?_⟩
      -- 2.10 restricts `σ = ‖δV‖ ⌞ Z` once more to `Z`, which does not change it.
      rw [V.firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded hV X,
        Varifold.symmetricGeneralizedBoundaryMeasure,
        Measure.restrict_restrict_of_subset subset_rfl]
/-- **Simon Ch. 8, Lemma 1.3, printed (1)–(2)** (child `slice_density` of `plane_disintegration`):
for continuous `β ≥ 0` on `G(N,n)`, the `β`-weighted slices `γ(B) = ∫_{Gₙ(B)} β(S) dV(y,S)` of `V`
are differentiated by `μ_V`: the ratio `γ(B_ρ(x)) / μ_V(B_ρ(x))` tends to a Borel `e(x)` for
`μ_V`-a.e. `x`, and `γ(A) = ∫_A e dμ_V` for Borel `A`.  Since `γ ≤ ‖β‖ μ_V`, `γ` is the zero
extension of a locally finite measure on `U`, so SimonGMT's Besicovitch differentiation on `U`
(`Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure`) and Radon–Nikodym apply, with
`e = (dγ/dμ_V).toReal`. -/
theorem Submission.plane_disint_slice_density :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (β : C(Grassmannian N n, ℝ)), (∀ S, 0 ≤ β S) → ∃ e : Euclidean N → ℝ, Measurable e ∧ (∀ᵐ x ∂V.weight, Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (e x))) ∧ ∀ A : Set (Euclidean N), MeasurableSet A → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, ENNReal.ofReal (e x) ∂V.weight := by
  intro N n U V β hβ
  have hU : IsOpen U := V.isOpen_domain
  -- `γ(B) = ∫_{Gₙ(B)} β dV`, i.e. `γ = π_#(V ⌞ β)`.
  obtain ⟨γ, hγ⟩ : ∃ γ : Measure (Euclidean N), ∀ B, MeasurableSet B →
      γ B = ∫⁻ z in B ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure :=
    ⟨(V.measure.withDensity fun z ↦ ENNReal.ofReal (β z.2)).map Prod.fst, fun B hB ↦ by
      rw [Measure.map_apply measurable_fst hB, withDensity_apply _ (measurable_fst hB),
        ← Set.prod_univ]⟩
  -- `γ ≤ ‖β‖ μ_V`: so `γ ≪ μ_V`, `γ` vanishes off `U` and is finite on compact subsets of `U`.
  have hγle : ∀ B, MeasurableSet B → γ B ≤ ENNReal.ofReal ‖β‖ * V.weight B := by
    intro B hB
    rw [hγ B hB, V.weight_apply hB, ← setLIntegral_const]
    exact lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (β.norm_coe_le_norm z.2))
  have hγac : γ ≪ V.weight :=
    Measure.absolutelyContinuous_of_le_smul (Measure.le_iff.2 fun B hB ↦ hγle B hB)
  have hUc : V.weight Uᶜ = 0 := by
    rw [V.weight_apply hU.measurableSet.compl]
    exact V.supported
  have hγU : γ Uᶜ = 0 := by
    have := hγle Uᶜ hU.measurableSet.compl
    rwa [hUc, mul_zero, nonpos_iff_eq_zero] at this
  -- `γ` is the zero extension of the locally finite measure `γ.comap Subtype.val` on `U`.
  have hemb := MeasurableEmbedding.subtype_coe hU.measurableSet
  obtain ⟨γU, hmap, hγUfin⟩ : ∃ γU : Measure U,
      γU.map Subtype.val = γ ∧ IsLocallyFiniteMeasure γU := by
    refine ⟨γ.comap Subtype.val, ?_, ?_⟩
    · rw [map_comap_subtype_coe hU.measurableSet]
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hγU
    · have : LocallyCompactSpace U := hU.locallyCompactSpace
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
      have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
      refine ⟨K, hKx, ?_⟩
      rw [hemb.comap_apply]
      exact (hγle _ hK'.measurableSet).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_top_iff_ne_top.2 (V.weight_finite_on_compact _ hK'
          (by rintro _ ⟨y, _, rfl⟩; exact y.2))))
  have : SigmaFinite γ := by
    rw [← hmap]
    exact hemb.sigmaFinite_map
  -- Besicovitch differentiation on `U`: `γ(B_ρ(x)) / μ_V(B_ρ(x)) → dγ/dμ_V(x)` for `μ_V`-a.e. `x`.
  have hdiff := V.ae_tendsto_firstVariationDensity_of_domainMeasure γU
  rw [hmap] at hdiff
  refine ⟨fun x ↦ (γ.rnDeriv V.weight x).toReal,
    (Measure.measurable_rnDeriv γ V.weight).ennreal_toReal, ?_, fun A hA ↦ ?_⟩
  · -- (1): near `x ∈ U` the real quotient is the `toReal` of the `[0,∞]` quotient.
    have hUae : ∀ᵐ x ∂V.weight, x ∈ U := by
      rw [ae_iff]
      exact hUc
    filter_upwards [hdiff, Measure.rnDeriv_lt_top γ V.weight, hUae] with x hx hfin hxU
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hxU
    refine ((ENNReal.tendsto_toReal hfin.ne).comp hx).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ
    have hfinB : V.measure (closedBall x ρ ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ :=
      V.finite_on_compact _ (isCompact_closedBall x ρ)
        ((closedBall_subset_ball hρ.2).trans hrU)
    have hint : IntegrableOn (fun z : Euclidean N × Grassmannian N n ↦ β z.2)
        (closedBall x ρ ×ˢ univ) V.measure :=
      Measure.integrableOn_of_bounded hfinB
        (β.continuous.comp continuous_snd).aestronglyMeasurable
        (M := ‖β‖) (ae_of_all _ fun z ↦ β.norm_coe_le_norm z.2)
    rw [Function.comp_apply, ENNReal.toReal_div, hγ _ measurableSet_closedBall,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z ↦ hβ z.2),
      ENNReal.toReal_ofReal (integral_nonneg fun z : Euclidean N × Grassmannian N n ↦ hβ z.2)]
  · -- (2): Radon–Nikodym, `γ = μ_V ⌞ (dγ/dμ_V)` with `dγ/dμ_V < ∞` `μ_V`-a.e.
    have hRN : V.weight.withDensity (γ.rnDeriv V.weight) A = γ A := by
      rw [Measure.withDensity_rnDeriv_eq γ V.weight hγac]
    rw [withDensity_apply _ hA] at hRN
    rw [← hγ A hA, ← hRN]
    refine setLIntegral_congr_fun_ae hA ?_
    filter_upwards [Measure.rnDeriv_lt_top γ V.weight] with x hx _
    exact (ENNReal.ofReal_toReal hx.ne).symm
/-- **Simon Ch. 8, proof of Lemma 1.3, printed (3)–(4) and the Riesz step** (child `riesz_limit` of
`plane_disintegration`): if `m ρ` is eventually a probability measure on `G(N,n)` and `∫ f dm_ρ`
converges along the nontrivial filter `l` for every `f` in a dense `D ⊆ C(G(N,n), ℝ)`, then
`∫ f dm_ρ → ∫ f dη` for every `f ∈ C(G(N,n), ℝ)` and some probability measure `η`.  The estimate
`|∫ f dm - ∫ g dm| ≤ ‖f - g‖` makes `ρ ↦ ∫ f dm_ρ` Cauchy along `l`; the limit `L f` is a positive
linear functional with `L 1 = 1`, and Riesz–Markov–Kakutani on the compact space `G(N,n)`
represents it by `η`. -/
theorem Submission.plane_disint_riesz_limit :
    ∀ (N n : ℕ) (l : Filter ℝ) (m : ℝ → Measure (Grassmannian N n))
      (D : Set C(Grassmannian N n, ℝ)), l.NeBot → (∀ᶠ ρ in l, IsProbabilityMeasure (m ρ)) →
      Dense D → (∀ f ∈ D, ∃ c : ℝ, Tendsto (fun ρ ↦ ∫ S, f S ∂(m ρ)) l (𝓝 c)) →
      ∃ η : Measure (Grassmannian N n), IsProbabilityMeasure η ∧
        ∀ f : C(Grassmannian N n, ℝ), Tendsto (fun ρ ↦ ∫ S, f S ∂(m ρ)) l (𝓝 (∫ S, f S ∂η)) := by
  intro N n l m D hl hprob hD hlim
  have hint : ∀ μ : Measure (Grassmannian N n), IsProbabilityMeasure μ →
      ∀ f : C(Grassmannian N n, ℝ), Integrable (fun S ↦ f S) μ := fun μ _ f ↦
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Printed (3): `|∫ f dμ - ∫ g dμ| ≤ ‖f - g‖` for a probability measure `μ`.
  have hest : ∀ μ : Measure (Grassmannian N n), IsProbabilityMeasure μ →
      ∀ f g : C(Grassmannian N n, ℝ), dist (∫ S, f S ∂μ) (∫ S, g S ∂μ) ≤ dist f g := by
    intro μ hμ f g
    rw [dist_eq_norm, ← integral_sub (hint μ hμ f) (hint μ hμ g), dist_eq_norm]
    calc ‖∫ S, f S - g S ∂μ‖ ≤ ‖f - g‖ * μ.real univ :=
          norm_integral_le_of_norm_le_const
            (Eventually.of_forall fun S ↦ (f - g).norm_coe_le_norm S)
      _ = ‖f - g‖ := by simp
  -- Printed (4): approximating `f` by `g ∈ D` makes `ρ ↦ ∫ f dm_ρ` Cauchy along `l`.
  have hconv : ∀ f : C(Grassmannian N n, ℝ), ∃ c : ℝ,
      Tendsto (fun ρ ↦ ∫ S, f S ∂(m ρ)) l (𝓝 c) := by
    intro f
    refine cauchy_map_iff_exists_tendsto.mp (Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε ↦ ?_⟩)
    obtain ⟨g, hgD, hfg⟩ := hD.exists_dist_lt f (by positivity : (0 : ℝ) < ε / 4)
    obtain ⟨c, hc⟩ := hlim g hgD
    refine ⟨ball c (ε / 2), ?_, fun x hx y hy ↦ ?_⟩
    · rw [mem_map]
      filter_upwards [hprob, hc (ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4))] with ρ hρ hgρ
      calc dist (∫ S, f S ∂(m ρ)) c
          ≤ dist (∫ S, f S ∂(m ρ)) (∫ S, g S ∂(m ρ)) + dist (∫ S, g S ∂(m ρ)) c :=
            dist_triangle _ _ _
        _ < ε / 4 + ε / 4 := add_lt_add ((hest (m ρ) hρ f g).trans_lt hfg) hgρ
        _ = ε / 2 := by ring
    · calc dist x y ≤ dist x c + dist y c := dist_triangle_right _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hx hy
        _ = ε := by ring
  choose L hL using hconv
  -- `L` is additive, homogeneous, monotone and `L 1 = 1`: limits of eventual identities.
  have hadd : ∀ f g : C(Grassmannian N n, ℝ), L (f + g) = L f + L g := fun f g ↦
    tendsto_nhds_unique (hL (f + g)) (((hL f).add (hL g)).congr' (by
      filter_upwards [hprob] with ρ hρ
      exact (integral_add (hint _ hρ f) (hint _ hρ g)).symm))
  have hsmul : ∀ (a : ℝ) (f : C(Grassmannian N n, ℝ)), L (a • f) = a * L f := fun a f ↦
    tendsto_nhds_unique (hL (a • f)) (((hL f).const_mul a).congr'
      (Eventually.of_forall fun ρ ↦ (integral_const_mul a _).symm))
  have hmono : ∀ f g : C(Grassmannian N n, ℝ), (∀ S, f S ≤ g S) → L f ≤ L g := fun f g hfg ↦
    le_of_tendsto_of_tendsto (hL f) (hL g) (by
      filter_upwards [hprob] with ρ hρ
      exact integral_mono (hint _ hρ f) (hint _ hρ g) hfg)
  have hone : L 1 = 1 :=
    tendsto_nhds_unique (hL 1) (tendsto_const_nhds.congr' (by
      filter_upwards [hprob] with ρ hρ
      simp))
  -- Riesz (Ch. 1, 4.12): `C(G(N,n), ℝ) = C_c(G(N,n), ℝ)` as `G(N,n)` is compact.
  let Λ : C_c(Grassmannian N n, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ L f.toContinuousMap
      map_add' := fun f g ↦ hadd f.toContinuousMap g.toContinuousMap
      map_smul' := fun a f ↦ hsmul a f.toContinuousMap
      monotone' := fun f g hfg ↦ hmono f.toContinuousMap g.toContinuousMap hfg }
  have hη : ∀ f : C(Grassmannian N n, ℝ), ∫ S, f S ∂(RealRMK.rieszMeasure Λ) = L f := fun f ↦
    RealRMK.integral_rieszMeasure Λ ⟨f, HasCompactSupport.of_compactSpace _⟩
  refine ⟨RealRMK.rieszMeasure Λ, ⟨?_⟩, fun f ↦ by rw [hη f]; exact hL f⟩
  have h1 := hη 1
  rw [hone] at h1
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h1
  rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h1

/-- **Simon Ch. 8, proof of Lemma 1.3, first part, pp. 207–208** (child `pointwise_measure` of
`plane_disintegration`): for `μ_V`-a.e. `x` the normalized slices of `V` over `B_ρ(x)` converge, as
`ρ ↓ 0`, to a probability measure `η` on `G(N,n)`.  Take a dense sequence `f_j` in the separable
space `C(G(N,n), ℝ)` and apply `plane_disint_slice_density` to `β_j = f_j + ‖f_j‖ ≥ 0`.  At a point
`x ∈ U ∩ spt μ_V` where all these limits exist, the slice measures
`m_ρ = μ_V(B_ρ(x))⁻¹ σ_#(V ⌞ (B_ρ(x) × G(N,n)))`, `σ(y, S) = S`, satisfy
`∫ f dm_ρ = (∫_{B_ρ(x) × G(N,n)} f(S) dV) / μ_V(B_ρ(x))` and are probability measures for small
`ρ`, and `∫ f_j dm_ρ = ∫ β_j dm_ρ - ‖f_j‖` converges for every `j`; `plane_disint_riesz_limit`
gives `η`. -/
theorem Submission.plane_disint_pointwise_measure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), ∀ᵐ x ∂V.weight, ∃ η : Measure (Grassmannian N n), IsProbabilityMeasure η ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂η)) := by
  intro N n U V
  -- `C(G(N,n), ℝ)` is separable: the matrix entries `S ↦ S i j` separate the points of `G(N,n)`,
  -- so by Stone–Weierstrass the subalgebra they generate is dense, and it is spanned by the
  -- countably many monomials in these entries.
  have : TopologicalSpace.SeparableSpace C(Grassmannian N n, ℝ) := by
    obtain ⟨g, hg⟩ : ∃ g : Fin N × Fin N → C(Grassmannian N n, ℝ), ∀ p S, g p S = S.1 p.1 p.2 :=
      ⟨fun p ↦ ⟨fun S ↦ S.1 p.1 p.2, continuous_subtype_val.matrix_elem p.1 p.2⟩, fun _ _ ↦ rfl⟩
    have hsep : (Algebra.adjoin ℝ (range g)).SeparatesPoints := by
      intro S T hST
      obtain ⟨i, j, hij⟩ : ∃ i j, S.1 i j ≠ T.1 i j := by
        by_contra! h
        exact hST (Subtype.ext (Matrix.ext h))
      refine ⟨_, ⟨g (i, j), Algebra.subset_adjoin ⟨(i, j), rfl⟩, rfl⟩, ?_⟩
      simpa only [hg] using hij
    have hcount : (Submonoid.closure (range g) : Set C(Grassmannian N n, ℝ)).Countable := by
      rw [Submonoid.closure_eq_image_prod, ← Set.range_list_map_coe, ← Set.range_comp]
      exact countable_range _
    have hA : TopologicalSpace.IsSeparable
        (Algebra.adjoin ℝ (range g) : Set C(Grassmannian N n, ℝ)) := by
      rw [← Subalgebra.coe_toSubmodule, Algebra.adjoin_eq_span]
      exact hcount.isSeparable.span
    rw [← TopologicalSpace.isSeparable_univ_iff, ← Algebra.coe_top (R := ℝ),
      ← ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep,
      Subalgebra.topologicalClosure_coe]
    exact hA.closure
  -- A dense sequence `f_j` in `C(G(N,n), ℝ)` and the nonnegative shifts `β_j = f_j + ‖f_j‖`.
  obtain ⟨f, hf⟩ := TopologicalSpace.exists_dense_seq C(Grassmannian N n, ℝ)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → C(Grassmannian N n, ℝ), ∀ j S, β j S = f j S + ‖f j‖ :=
    ⟨fun j ↦ f j + ContinuousMap.const (Grassmannian N n) ‖f j‖, fun _ _ ↦ rfl⟩
  have hβ_nonneg : ∀ j S, 0 ≤ β j S := fun j S ↦ by
    rw [hβ]
    linarith [neg_abs_le (f j S), Real.norm_eq_abs (f j S), (f j).norm_coe_le_norm S]
  -- Printed (1) for every `β_j`.
  have hlim : ∀ j, ∃ e : Euclidean N → ℝ, ∀ᵐ x ∂V.weight,
      Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)),
          β j z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (e x)) :=
    fun j ↦ by
      obtain ⟨e, -, he, -⟩ := Submission.plane_disint_slice_density N n U V (β j) (hβ_nonneg j)
      exact ⟨e, he⟩
  choose e he using hlim
  -- Countably many conull conditions: `x ∈ U`, `x ∈ spt μ_V`, and the limits for every `β_j`.
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  filter_upwards [hU, Measure.support_mem_ae (μ := V.weight), ae_all_iff.2 he]
    with x hxU hxspt hxlim
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hxU
  -- The slice measures `m_ρ = μ_V(B_ρ(x))⁻¹ σ_#(V ⌞ (B_ρ(x) × G(N,n)))`, `σ(y, S) = S`.
  obtain ⟨m, hm⟩ : ∃ m : ℝ → Measure (Grassmannian N n), ∀ ρ, m ρ =
      (V.weight (closedBall x ρ))⁻¹ •
        (V.measure.restrict (closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)))).map Prod.snd :=
    ⟨_, fun _ ↦ rfl⟩
  -- `∫ f dm_ρ` is the quotient of the statement, for every `ρ`.
  have hm_int : ∀ (ρ : ℝ) (g : C(Grassmannian N n, ℝ)), ∫ S, g S ∂(m ρ) =
      (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), g z.2 ∂V.measure) /
        (V.weight (closedBall x ρ)).toReal := by
    intro ρ g
    rw [hm, integral_smul_measure, integral_map measurable_snd.aemeasurable
      g.continuous.aestronglyMeasurable, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
  -- For `0 < ρ < r`, `0 < μ_V(B_ρ(x)) < ∞` (`x ∈ spt μ_V`, `B_ρ(x) ⊆ U` compact), so `m_ρ(G) = 1`.
  have hm_prob : ∀ ρ ∈ Ioo 0 r, IsProbabilityMeasure (m ρ) := by
    intro ρ hρ
    have hpos : 0 < V.weight (closedBall x ρ) :=
      (Measure.mem_support_iff_forall x).1 hxspt _ (closedBall_mem_nhds x hρ.1)
    have hfin : V.weight (closedBall x ρ) ≠ ∞ :=
      V.weight_finite_on_compact _ (isCompact_closedBall x ρ)
        ((closedBall_subset_ball hρ.2).trans hrU)
    constructor
    rw [hm, Measure.smul_apply, Measure.map_apply measurable_snd MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, ← V.weight_apply measurableSet_closedBall,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos.ne' hfin
  -- Printed (4) on the dense family: `∫ f_j dm_ρ = ∫ β_j dm_ρ - ‖f_j‖ → e_j(x) - ‖f_j‖`.
  have hm_lim : ∀ g ∈ range f, ∃ c : ℝ, Tendsto (fun ρ ↦ ∫ S, g S ∂(m ρ)) (𝓝[>] 0) (𝓝 c) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨e j x - ‖f j‖, ((hxlim j).sub_const ‖f j‖).congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ
    have := hm_prob ρ hρ
    rw [← hm_int]
    simp only [hβ]
    rw [integral_add ((f j).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (integrable_const _), integral_const,
      probReal_univ, one_smul, add_sub_cancel_right]
  -- Printed (3), (4) and the Riesz representation.
  obtain ⟨η, hη, hηlim⟩ := Submission.plane_disint_riesz_limit N n (𝓝[>] 0) m (range f)
    inferInstance (by filter_upwards [Ioo_mem_nhdsGT hr] using hm_prob) hf hm_lim
  exact ⟨η, hη, fun g ↦ (hηlim g).congr fun ρ ↦ hm_int ρ g⟩

/-- **Tangent planes of a homogeneous varifold are dilation invariant** (the step
`Θ^n(μ_C, λy) = Θ^n(μ_C, y)` "by 5.3" in the proof of Simon Ch. 8, 5.7, with 5.3 in its corrected
form `μ_C(sA) = s^n μ_C(A)`).  If `C` has tangent plane `T` with multiplicity `θ` at `y` and `T'`
with multiplicity `θ'` at `s y`, then `T' = T` and `θ' = θ`: the density ratio and the weight
blow-ups of `C` at `s y` and scale `s t` are those at `y` and scale `t`.  With `s = 1` this is the
uniqueness of the tangent plane and multiplicity at a point. -/
theorem Submission.allard_tc_tangent_plane_dilation :
    ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (s : ℝ) (y : Euclidean N) (T T' : Grassmannian N n) (θ θ' : ℝ), 0 < s → (∀ A : Set (Euclidean N), C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A) → HasTangentPlane C y T θ → HasTangentPlane C (s • y) T' θ' → T' = T ∧ θ' = θ := by
  intro N n C s y T T' θ θ' hs hhom hT hT'
  have hs0 : s ≠ 0 := hs.ne'
  -- The dilation `t ↦ s t` maps `𝓝[>] 0` into itself.
  have hscale : Tendsto (fun t : ℝ ↦ s * t) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun t : ℝ ↦ s * t).tendsto' 0 0 (mul_zero s)).mono_left
        nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos hs ht)
  -- Step 1: `θ' = θ`.  By homogeneity and `s B_r(y) = B_{sr}(s y)`, the density ratio at `s y` and
  -- radius `s r` is the one at `y` and radius `r`; both multiplicities are densities.
  have hratio : ∀ r : ℝ, 0 < r →
      densityRatio n C.weight (s • y) (s * r) = densityRatio n C.weight y r := by
    intro r hr
    have hball : closedBall (s • y) (s * r) = s • closedBall y r := by
      rw [smul_closedBall s y hr.le, Real.norm_of_nonneg hs.le]
    simp only [densityRatio]
    rw [hball, hhom, ENNReal.ofReal_mul hs.le, mul_pow, mul_left_comm (unitBallVolume n),
      ENNReal.mul_div_mul_left _ _ (pow_ne_zero n (ENNReal.ofReal_pos.2 hs).ne')
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hθ : θ' = θ := by
    have hy : Tendsto (densityRatio n C.weight y) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) :=
      Submission.allard_tc_tangent_plane_density N n univ C y T θ hT
    have hsy : Tendsto (densityRatio n C.weight (s • y)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ')) :=
      Submission.allard_tc_tangent_plane_density N n univ C (s • y) T' θ' hT'
    have hy' : Tendsto (densityRatio n C.weight y) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ')) :=
      (hsy.comp hscale).congr'
        (by filter_upwards [self_mem_nhdsWithin] with r hr using hratio r hr)
    exact (ENNReal.ofReal_eq_ofReal_iff hT'.2.1.le hT.2.1.le).1 (tendsto_nhds_unique hy' hy)
  -- Step 3: by homogeneity, `μ_C` pushed forward by `z ↦ s⁻¹ z` is `s^n μ_C`, so the weight
  -- blow-up of `C` at `s y` and scale `s t` is the one at `y` and scale `t`.
  have hmap : C.weight.map (fun z : Euclidean N ↦ s⁻¹ • z) = ENNReal.ofReal s ^ n • C.weight := by
    ext A hA
    rw [Measure.map_apply (measurable_const_smul s⁻¹) hA, Set.preimage_smul_inv₀ hs0, hhom,
      Measure.smul_apply, smul_eq_mul]
  have hblow : ∀ (g : C_c(Euclidean N, ℝ)) (t : ℝ),
      (s * t)⁻¹ ^ n * ∫ z, g ((s * t)⁻¹ • (z - s • y)) ∂C.weight =
        t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - y)) ∂C.weight := by
    intro g t
    have hG : Continuous fun w : Euclidean N ↦ g (t⁻¹ • (w - y)) := by fun_prop
    have hpt : ∀ z : Euclidean N, (s * t)⁻¹ • (z - s • y) = t⁻¹ • (s⁻¹ • z - y) := fun z ↦ by
      rw [mul_inv, mul_comm s⁻¹, mul_smul, smul_sub, inv_smul_smul₀ hs0]
    have hint : ∫ z, g (t⁻¹ • (s⁻¹ • z - y)) ∂C.weight =
        s ^ n * ∫ z, g (t⁻¹ • (z - y)) ∂C.weight := by
      have h := integral_map (μ := C.weight) (φ := fun z : Euclidean N ↦ s⁻¹ • z)
        (measurable_const_smul s⁻¹).aemeasurable hG.aestronglyMeasurable
      rw [hmap, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs.le,
        smul_eq_mul] at h
      exact h.symm
    have hc : (s * t)⁻¹ ^ n * s ^ n = t⁻¹ ^ n := by
      rw [mul_inv, mul_pow, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]
    simp_rw [hpt]
    rw [hint, ← mul_assoc, hc]
  -- Steps 2 and 4: the weight blow-ups at `y` tend to `θ ∫_T g dH^n` and, through `t ↦ s t`,
  -- to `θ' ∫_{T'} g dH^n`; as `θ' = θ > 0`, the `H^n`-integrals over `T` and `T'` agree.
  have hplane : ∀ g : C_c(Euclidean N, ℝ),
      ∫ x in (T.plane : Set (Euclidean N)), g x ∂μHE[n] =
        ∫ x in (T'.plane : Set (Euclidean N)), g x ∂μHE[n] := by
    intro g
    have hy := Submission.frt_weight_blowup_tendsto N n univ C y T θ hT g
    have hy' : Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - y)) ∂C.weight) (𝓝[>] 0)
        (𝓝 (θ' * ∫ x in (T'.plane : Set (Euclidean N)), g x ∂μHE[n])) :=
      ((Submission.frt_weight_blowup_tendsto N n univ C (s • y) T' θ' hT' g).comp hscale).congr'
        (Eventually.of_forall fun t ↦ hblow g t)
    have h := tendsto_nhds_unique hy' hy
    rw [hθ] at h
    exact (mul_left_cancel₀ hT.2.1.ne' h).symm
  -- Step 5: an `n`-plane is determined by these integrals.
  exact ⟨Submission.allard_tc_tpd_plane_eq_of_integral_eq N n T T' hplane, hθ⟩

/-- **Canonical representation `C = v(M, θ)` by varifold tangent planes** (step B3 of the proof of
Simon Ch. 8, 5.7).  Take `M` and `θ` from the First Rectifiability Theorem 1.2.  Since `μ_C` is
`θ H^n ⌞ M`, at every `x ∈ M` the weighted approximate tangent planes of `(M, θ)` are exactly the
varifold tangent planes of `C` with multiplicity `θ(x)`, so they may replace the approximate tangent
planes in `IsVarifoldOf`. -/
theorem Submission.allard_tc_tangent_point_representation :
    FirstRectifiabilityTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))),
      (∀ᵐ x ∂C.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane C x T θ) →
      ∃ (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf C M θ ∧
        (∀ x ∈ M, ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x)) ∧
        ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A →
          C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n,
            HasTangentPlane C x T (θ x) ∧ (x, T) ∈ A}, ENNReal.ofReal (θ x) ∂μHE[n] := by
  intro hFRT N n C hC
  -- 1.2 gives `θ`, a tangent plane with multiplicity `θ(x)` at every `x ∈ M`, and `C = v(M, θ)`,
  -- where `M` is the set of tangent points in `spt μ_C`; only these properties of `M` are used.
  obtain ⟨θ, hT, hV⟩ := hFRT N n univ C hC
  generalize {x | x ∈ C.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
    HasTangentPlane C x T θ'} = M at hT hV
  obtain ⟨-, hMmeas, hMrect, hθpos, hθint, hrep⟩ := id hV
  refine ⟨M, θ, hV, hT, ?_⟩
  -- `μ_C(B) = ∫_{E ∩ B} θ dH^n`, where `E ⊆ M` is the set of points with an approximate tangent
  -- plane (`IsVarifoldOf` at `A = B × G(N,n)`).
  obtain ⟨E, hEM, hE⟩ : ∃ E ⊆ M, ∀ B : Set (Euclidean N), MeasurableSet B →
      C.weight B = ∫⁻ x in E ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
    refine ⟨{x | x ∈ M ∧ ∃ S : Grassmannian N n,
      Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane}, fun x hx ↦ hx.1, ?_⟩
    intro B hB
    rw [C.weight_apply hB, hrep _ (hB.prod MeasurableSet.univ)]
    congr 2
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
    constructor
    · rintro ⟨hx, S, hS, hxB⟩
      exact ⟨⟨hx, S, hS⟩, hxB⟩
    · rintro ⟨⟨hx, S, hS⟩, hxB⟩
      exact ⟨hx, S, hS, hxB⟩
  -- `μ_C = θ H^n ⌞ M`: `H^n ⌞ M` is σ-finite and `θ(x)` is the density of `μ_C` at `x ∈ M`.
  have hW : ∀ B : Set (Euclidean N), MeasurableSet B →
      C.weight B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
    have := Submission.allard_tc_tpr_rectifiable_sigmaFinite N n M hMrect
    refine Submission.allard_tc_tpr_weight_eq_restrict N n C.weight M E θ
      (fun K hK ↦ C.weight_finite_on_compact K hK (subset_univ K)) inferInstance hEM
      (fun x hx ↦ ⟨hθpos x hx, ?_⟩) hE
    obtain ⟨T, hTx⟩ := hT x hx
    exact Submission.allard_tc_tangent_plane_density N n univ C x T (θ x) hTx
  -- Hence at `x ∈ M` the approximate tangent planes are exactly the tangent planes of `C` with
  -- multiplicity `θ(x)`.
  have hiff : ∀ x : Euclidean N, ∀ T : Grassmannian N n, HasTangentPlane C x T (θ x) →
      ∀ S : Grassmannian N n,
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ↔ S = T :=
    fun x T hTx ↦ Submission.allard_tc_tpr_weighted_approx_tangent_iff N n univ C M θ x T
      hMmeas hθpos (fun K hK ↦ hθint K hK (subset_univ K)) hW hTx
  intro A hA
  rw [hrep A hA]
  congr 2
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hx, S, hS, hxS⟩
    obtain ⟨T, hTx⟩ := hT x hx
    refine ⟨hx, S, ?_, hxS⟩
    rw [(hiff x T hTx S).1 hS]
    exact hTx
  · rintro ⟨hx, T, hTx, hxT⟩
    exact ⟨hx, T, (hiff x T hTx T).2 rfl, hxT⟩
/-- **Rectifiable tangent cones are invariant under dilations** (child `cone_rescaling_invariance`
of `allard_tangent_cones`; Simon Ch. 8, 5.7, last sentence of the proof).  If `C = v(M, θ)` has
tangent plane `T_x` with multiplicity `θ(x)` at every `x ∈ M`, is represented by these planes and
`μ_C(s A) = s^n μ_C(A)`, then `η_{0,s #} C = C` for `s > 0`: on `G = {w ∈ M : s w ∈ M}` the sibling
`tangent_plane_dilation` gives `θ(s w) = θ(w)` and the same planes, child
`carrier_dilation_null` makes `G` of full `H^n`-measure in both representing sets, and children
`rescaled_representation` and `setLIntegral_congr_off_null` compare the two integrals. -/
theorem Submission.allard_tc_cone_rescaling_invariance :
    ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf C M θ → (∀ x ∈ M, ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x)) → (∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x) ∧ (x, T) ∈ A}, ENNReal.ofReal (θ x) ∂μHE[n]) → (∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A) → ∀ s : ℝ, 0 < s → rescaledMeasure C 0 s = C.measure := by
  intro N n C M θ hC htan hrep hhom s hs
  obtain ⟨-, hM, -, hθ, hint, -⟩ := hC
  -- Step 1: `μ_C(B) = ∫⁻_{M ∩ B} ofReal θ dH^n` for Borel `B`, since every `x ∈ M` has a plane.
  have hweight : ∀ B : Set (Euclidean N), MeasurableSet B →
      C.weight B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Euclidean N)) := by
    intro B hB
    rw [C.weight_apply hB, hrep _ (hB.prod MeasurableSet.univ)]
    congr 2
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
    exact ⟨fun ⟨hxM, _, _, hxB⟩ ↦ ⟨hxM, hxB⟩,
      fun ⟨hxM, hxB⟩ ↦ ⟨hxM, (htan x hxM).choose, (htan x hxM).choose_spec, hxB⟩⟩
  -- Step 2: child `carrier_dilation_null` for `μ = μ_C`: `M ∖ s⁻¹ M` and `s⁻¹ M ∖ M` are null.
  obtain ⟨hnull₁, hnull₂⟩ := Submission.allard_tc_cri_carrier_dilation_null N n C.weight M θ hM
    hθ (fun K hK ↦ hint K hK (subset_univ K)) hweight hhom s hs
  -- Step 3: for `w ∈ M` with `s w ∈ M`, the sibling `tangent_plane_dilation` (at `s`, in both
  -- directions) gives `θ(s w) = θ(w)` and the same tangent planes at `w` and `s w`.
  have hdil : ∀ w ∈ M, s • w ∈ M → θ (s • w) = θ w ∧ ∀ S : Grassmannian N n,
      (HasTangentPlane C (s • w) S (θ (s • w)) ↔ HasTangentPlane C w S (θ w)) := by
    intro w hwM hswM
    obtain ⟨Tw, hTw⟩ := htan w hwM
    obtain ⟨Tsw, hTsw⟩ := htan (s • w) hswM
    refine ⟨(Submission.allard_tc_tangent_plane_dilation N n C s w Tw Tsw (θ w) (θ (s • w)) hs
      (hhom s · hs) hTw hTsw).2, fun S ↦ ⟨fun hS ↦ ?_, fun hS ↦ ?_⟩⟩
    · obtain ⟨rfl, -⟩ := Submission.allard_tc_tangent_plane_dilation N n C s w Tw S (θ w)
        (θ (s • w)) hs (hhom s · hs) hTw hS
      exact hTw
    · obtain ⟨rfl, -⟩ := Submission.allard_tc_tangent_plane_dilation N n C s w S Tsw (θ w)
        (θ (s • w)) hs (hhom s · hs) hS hTsw
      exact hTsw
  -- Step 4: on a Borel `A`, child `rescaled_representation` (with `P x T = HasTangentPlane C x T
  -- (θ x)` and `g = ofReal ∘ θ`) and the representation of `C` turn the claim into an equality of
  -- set-lintegrals, closed by child `setLIntegral_congr_off_null` at `G = {w ∈ M : s w ∈ M}`.
  ext A hA
  rw [Submission.allard_tc_cri_rescaled_representation N n C M
      (fun x T ↦ HasTangentPlane C x T (θ x)) (fun x ↦ ENNReal.ofReal (θ x)) hrep s hs A hA,
    hrep A hA]
  refine Submission.allard_tc_cri_setLIntegral_congr_off_null N (μHE[n] : Measure (Euclidean N))
    {w | w ∈ M ∧ s • w ∈ M} _ _ _ _ ?_ ?_ ?_ ?_ ?_
  -- (a) `G` is null-measurable: `G ⊆ M` and `M ∖ G ⊆ M ∖ s⁻¹ M` is null.
  · refine hM.congr (ae_eq_set.2 ⟨measure_mono_null ?_ hnull₁, measure_mono_null ?_ measure_empty⟩)
    · exact fun w ⟨hwM, hwG⟩ ↦ ⟨hwM, fun hswM ↦ hwG ⟨hwM, hswM⟩⟩
    · exact fun w ⟨hwG, hwM⟩ ↦ hwM hwG.1
  -- (b) the rescaled representing set lies in `G ∪ (s⁻¹ M ∖ M)`.
  · refine measure_mono_null ?_ hnull₂
    exact fun w ⟨⟨hswM, _⟩, hwG⟩ ↦ ⟨hswM, fun hwM ↦ hwG ⟨hwM, hswM⟩⟩
  -- (c) the representing set of `C` lies in `G ∪ (M ∖ s⁻¹ M)`.
  · refine measure_mono_null ?_ hnull₁
    exact fun w ⟨⟨hwM, _⟩, hwG⟩ ↦ ⟨hwM, fun hswM ↦ hwG ⟨hwM, hswM⟩⟩
  -- (d) on `G` the two representing sets agree, by step 3.
  · rintro w ⟨hwM, hswM⟩
    have hiff := (hdil w hwM hswM).2
    exact ⟨fun ⟨_, S, hS, hwS⟩ ↦ ⟨hwM, S, (hiff S).1 hS, hwS⟩,
      fun ⟨_, S, hS, hwS⟩ ↦ ⟨hswM, S, (hiff S).2 hS, hwS⟩⟩
  -- (e) on `G` the integrands agree, as `θ(s w) = θ(w)` by step 3.
  · rintro w ⟨hwM, hswM⟩
    rw [(hdil w hwM hswM).1]
/-- **Tangent cones are rectifiable cones** (child `tangent_cones_rectifiable` of
`allard_tangent_cones`; Simon Ch. 8, Corollary 5.7 and its proof, p. 216): from 5.1–5.4, the
blow-up density lower bound, Allard's 5.5/5.6 and the First Rectifiability Theorem 1.2.  The lower
bound with `τ = 1` gives `Θ^n(μ_C, ·) ≥ 1` `μ_C`-a.e.; `C` is stationary (5.2), so 5.5 makes it
rectifiable with tangent planes `μ_C`-a.e.; the siblings `tangent_point_representation` and
`cone_rescaling_invariance` with the homogeneity 5.3 then give `η_{0,s #} C = C` for `s > 0`. -/
theorem Submission.allard_tc_tangent_cones_rectifiable :
    VarifoldTangentCones → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C → ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ) → AllardRectifiabilityTheorem → FirstRectifiabilityTheorem → TangentConesAreRectifiableCones := by
  intro hVTC hLB hAllard hFRT N n U V x θ₀ hV hx hθ₀ hdens h51 hdecay C hC
  -- Step B1: the blow-up density lower bound with `τ = 1` (`ENNReal.ofReal 1 = 1`).
  have hdecay1 : Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧
      ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal 1 ≤ θ} / ENNReal.ofReal ρ ^ n)
      (𝓝[>] 0) (𝓝 0) := by
    rw [ENNReal.ofReal_one]
    exact hdecay
  have hge : ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal 1 ≤ θ :=
    hLB N n U V x 1 hV hx one_pos h51 hdecay1 C hC
  -- Step B2: by 5.1–5.4 `C` is stationary with `μ_C(sA) = s^n μ_C(A)`; Allard 5.5/5.6 on `C`.
  obtain ⟨hstat, -, hhom⟩ := (hVTC N n U V x θ₀ hV hx hθ₀ hdens h51).2 C hC
  have hpos : ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ 0 < θ := by
    filter_upwards [hge] with y ⟨θ, hθ, h1θ⟩
    exact ⟨θ, hθ, (ENNReal.ofReal_pos.2 one_pos).trans_le h1θ⟩
  obtain ⟨hrect, htan⟩ := hAllard N n univ C hstat.hasLocallyBoundedFirstVariation hpos
  refine ⟨hrect, ?_⟩
  -- Step B3: the canonical representation `C = v(M, θ)` with tangent planes on `M`.
  obtain ⟨M, θ, hMθ, hTM, hrep⟩ :=
    Submission.allard_tc_tangent_point_representation hFRT N n C htan
  -- Steps B4–B6: dilation invariance `η_{0,s #} C = C` from the homogeneity 5.3.
  exact Submission.allard_tc_cone_rescaling_invariance N n C M θ hMθ hTM hrep hhom
/-- Layer-cake comparison of radial cutoff integrals (Simon Ch. 8, 3.3, p. 210): if
`ν(B_r(x)) ≤ Λ μ(B_r(x))` for `0 < r < ρ₀`, and `φ` is continuous and non-increasing with `φ = 1`
on `(-∞, 1]` and `φ = 0` on `[A², ∞)`, where `A, t > 0` and `t A < ρ₀`, then
`∫ φ(|y - x|² / t²) dν(y) ≤ Λ ∫ φ(|y - x|² / t²) dμ(y)`.  Every superlevel set of the integrand at
a positive height is empty or a closed ball `B_r(x)` with `0 < r < ρ₀`; no finiteness of `ν`, `μ`
and no sign condition on `Λ` is needed. -/
theorem Submission.mono833_radial_layer_cake_le :
    ∀ (N : ℕ) (ν μ : Measure (Euclidean N)) (x : Euclidean N) (ρ₀ Λ A t : ℝ) (φ : ℝ → ℝ), (∀ r : ℝ, 0 < r → r < ρ₀ → ν (closedBall x r) ≤ ENNReal.ofReal Λ * μ (closedBall x r)) → Continuous φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, A ^ 2 ≤ s → φ s = 0) → 0 < A → 0 < t → t * A < ρ₀ → ∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂ν ≤ ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂μ := by
  intro N ν μ x ρ₀ Λ A t φ hball hφc hφa hφ1 hφ0 hA ht htA
  -- Step 1: `0 ≤ φ ≤ 1`, from antitonicity and the two plateaus.
  have hφnn : ∀ s, 0 ≤ φ s := fun s ↦
    (hφ0 (max s (A ^ 2)) (le_max_right _ _)).symm.le.trans (hφa (le_max_left _ _))
  have hφle : ∀ s, φ s ≤ 1 := fun s ↦
    (hφa (min_le_left s 1)).trans (hφ1 (min s 1) (min_le_right _ _)).le
  -- Step 2: the radial profile `c(y) = φ(|y - x|² / t²)` is continuous, hence measurable.
  set c : Euclidean N → ℝ := fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) with hc
  have hcm : Measurable c :=
    (hφc.comp (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).measurable
  -- Step 3: the layer-cake formula, for an arbitrary measure.
  have hlc : ∀ m : Measure (Euclidean N),
      ∫⁻ y, ENNReal.ofReal (c y) ∂m = ∫⁻ s in Ioi 0, m {y | s ≤ c y} := fun m ↦
    lintegral_eq_lintegral_meas_le m (Eventually.of_forall fun y ↦ hφnn _) hcm.aemeasurable
  -- Step 4: each superlevel set `{c ≥ s}`, `s > 0`, is empty or a ball of radius in `(0, ρ₀)`.
  have hsub : ∀ s ∈ Ioi (0 : ℝ),
      ν {y | s ≤ c y} ≤ ENNReal.ofReal Λ * μ {y | s ≤ c y} := by
    intro s hs
    rw [mem_Ioi] at hs
    rcases lt_or_ge 1 s with h1 | h1
    · -- 4a: `s > 1`, the superlevel set is empty.
      have hempty : {y | s ≤ c y} = ∅ := by
        ext y
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
        exact (hφle _).trans_lt h1
      simp [hempty]
    · -- 4b: `E = {τ : s ≤ φ τ}` is closed, contains `1`, and is bounded above by `A²`.
      set E : Set ℝ := {τ | s ≤ φ τ} with hE
      have hEc : IsClosed E := isClosed_le continuous_const hφc
      have h1E : (1 : ℝ) ∈ E := by
        rw [hE, mem_ofPred_eq, hφ1 1 le_rfl]
        exact h1
      have hEbdd : BddAbove E := by
        refine ⟨A ^ 2, fun τ hτ ↦ ?_⟩
        by_contra h
        rw [hE, mem_ofPred_eq, hφ0 τ (not_le.1 h).le] at hτ
        exact absurd hτ (not_le.2 hs)
      set b := sSup E with hb
      have hbE : b ∈ E := hEc.csSup_mem ⟨1, h1E⟩ hEbdd
      have hb1 : 1 ≤ b := le_csSup hEbdd h1E
      have hbA : b < A ^ 2 := by
        by_contra h
        have hbE' := hbE
        rw [hE, mem_ofPred_eq, hφ0 b (not_lt.1 h)] at hbE'
        exact absurd hbE' (not_le.2 hs)
      -- 4c: `E = (-∞, b]`.
      have hEiff : ∀ τ, s ≤ φ τ ↔ τ ≤ b := fun τ ↦
        ⟨fun h ↦ le_csSup hEbdd h, fun h ↦ hbE.trans (hφa h)⟩
      -- 4d–4e: `{c ≥ s} = B_r(x)` with `r = t √b ∈ (0, ρ₀)`.
      have hb0 : 0 ≤ b := zero_le_one.trans hb1
      set r := t * Real.sqrt b with hr
      have hr0 : 0 < r := mul_pos ht (Real.sqrt_pos.2 (zero_lt_one.trans_le hb1))
      have hrρ : r < ρ₀ :=
        (mul_lt_mul_of_pos_left ((Real.sqrt_lt' hA).2 hbA) ht).trans htA
      have hr2 : r ^ 2 = b * t ^ 2 := by
        rw [hr, mul_pow, Real.sq_sqrt hb0, mul_comm]
      have hset : {y | s ≤ c y} = closedBall x r := by
        ext y
        rw [mem_ofPred_eq, mem_closedBall, dist_eq_norm, hc, hEiff,
          div_le_iff₀ (pow_pos ht 2), ← hr2]
        exact pow_le_pow_iff_left₀ (norm_nonneg _) hr0.le two_ne_zero
      -- 4f: the ball hypothesis.
      rw [hset]
      exact hball r hr0 hrρ
  -- Step 5: integrate over `(0, ∞)` and pull out the finite constant `ofReal Λ`.
  calc ∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂ν
      = ∫⁻ s in Ioi 0, ν {y | s ≤ c y} := hlc ν
    _ ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal Λ * μ {y | s ≤ c y} :=
      setLIntegral_mono' measurableSet_Ioi hsub
    _ = ENNReal.ofReal Λ * ∫⁻ s in Ioi 0, μ {y | s ≤ c y} :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂μ := by
      rw [← hlc μ]

/-- **Simon Ch. 8, 3.3 (printed p. 210), the first-variation estimate** (child
`radial_first_variation_bound` of `monotonicity_formula`): for the radial field
`X(y) = φ(|y - x|²/t²)(y - x)`, where `φ` is `C¹`, non-increasing, `φ = 1` on `(-∞, 1]` and
`φ = 0` on `[A², ∞)`, with `tA < ρ₀`, hypothesis 3.1 (`‖δV‖(B_r(x)) ≤ Λ μ_V(B_r(x))` for
`0 < r < ρ₀`) gives `|δV(X)| ≤ A Λ t ∫ φ(|y - x|²/t²) dμ_V(y)`.
Write `δV(X) = -∫ ν·X d‖δV‖` with `|ν| = 1` `‖δV‖`-a.e. (2.6); then `|ν·X| ≤ tA φ(|y - x|²/t²)`,
and the layer-cake comparison `mono833_radial_layer_cake_le` turns 3.1 into
`∫ φ(|y - x|²/t²) d‖δV‖ ≤ Λ ∫ φ(|y - x|²/t²) dμ_V`. -/
theorem Submission.mono833_radial_first_variation_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ₀ Λ A t : ℝ) (φ : ℝ → ℝ), V.HasLocallyBoundedFirstVariation → ball x ρ₀ ⊆ U → 0 ≤ Λ → (∀ r : ℝ, 0 < r → r < ρ₀ → variationMeasure V (closedBall x r) ≤ ENNReal.ofReal Λ * V.weight (closedBall x r)) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, A ^ 2 ≤ s → φ s = 0) → 0 < A → 0 < t → t * A < ρ₀ → |V.firstVariation (fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x))| ≤ A * Λ * t * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight := by
  intro N n U V x ρ₀ Λ A t φ hV hball hΛ hbound hφ hanti hone hzero hA ht htA
  have htA0 : 0 < t * A := mul_pos ht hA
  -- Step 1: `0 ≤ φ ≤ 1`, and the profile `c(y) = φ(|y - x|²/t²)` is continuous.
  have hφ_nonneg : ∀ s, 0 ≤ φ s := fun s ↦
    (hzero _ (le_max_right s (A ^ 2))).symm.le.trans (hanti (le_max_left s (A ^ 2)))
  have hφ_le_one : ∀ s, φ s ≤ 1 := fun s ↦
    (hanti (min_le_left s 1)).trans (hone _ (min_le_right s 1)).le
  have hq : ContDiff ℝ 1 (fun y : Euclidean N ↦ ‖y - x‖ ^ 2 / t ^ 2) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _
  have hc_cont : Continuous (fun y : Euclidean N ↦ φ (‖y - x‖ ^ 2 / t ^ 2)) :=
    hφ.continuous.comp hq.continuous
  -- Step 2: `c(y) ≠ 0` forces `|y - x| < tA`, since `|y - x| ≥ tA` gives `|y - x|²/t² ≥ A²`.
  have hc_supp : ∀ y : Euclidean N, φ (‖y - x‖ ^ 2 / t ^ 2) ≠ 0 → ‖y - x‖ < t * A := by
    intro y hy
    by_contra hge
    refine hy (hzero _ ?_)
    rw [le_div_iff₀ (by positivity)]
    calc A ^ 2 * t ^ 2 = (t * A) ^ 2 := by ring
      _ ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ htA0.le (not_lt.1 hge) 2
  have hc_mem : ∀ y : Euclidean N, φ (‖y - x‖ ^ 2 / t ^ 2) ≠ 0 → y ∈ closedBall x (t * A) :=
    fun y hy ↦ mem_closedBall_iff_norm.2 (hc_supp y hy).le
  -- Step 3: `|X(y)| = c(y) |y - x| ≤ tA c(y)`.
  have hX_norm : ∀ y : Euclidean N,
      ‖φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)‖ ≤ t * A * φ (‖y - x‖ ^ 2 / t ^ 2) := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (hφ_nonneg _)]
    by_cases hy : φ (‖y - x‖ ^ 2 / t ^ 2) = 0
    · simp [hy]
    · calc φ (‖y - x‖ ^ 2 / t ^ 2) * ‖y - x‖ ≤ φ (‖y - x‖ ^ 2 / t ^ 2) * (t * A) :=
            mul_le_mul_of_nonneg_left (hc_supp y hy).le (hφ_nonneg _)
        _ = t * A * φ (‖y - x‖ ^ 2 / t ^ 2) := mul_comm _ _
  -- Step 4: `X` is a test field: `C¹`, `spt X ⊆ B_{tA}(x)` compact, and `B_{tA}(x) ⊆ U`.
  have hX_cd : ContDiff ℝ 1 (fun y : Euclidean N ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) :=
    (hφ.comp hq).smul (contDiff_id.sub contDiff_const)
  have hX_tsupp : tsupport (fun y : Euclidean N ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) ⊆
      closedBall x (t * A) := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    apply hc_mem y
    intro h
    apply hy
    simp [h]
  have hK : IsCompact (closedBall x (t * A)) := isCompact_closedBall x (t * A)
  have hKU : closedBall x (t * A) ⊆ U := (closedBall_subset_ball htA).trans hball
  let X : Varifold.TestVectorField (N := N) U :=
    ⟨fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x), hX_cd,
      hK.of_isClosed_subset (isClosed_tsupport _) hX_tsupp, hX_tsupp.trans hKU⟩
  -- Step 5: `‖δV‖` is the Riesz measure `m`, with polar field `η`, `|η| = 1` `m`-a.e. (2.6).
  have hvm : variationMeasure V = V.firstVariationRieszMeasure hV := by
    simp only [variationMeasure, dite_eq_left hV]
  set m := V.firstVariationRieszMeasure hV
  set η := V.firstVariationPolarField hV
  have hrep : V.IsFirstVariationPolarRepresentation m η :=
    V.isFirstVariationPolarRepresentation_riesz hV
  obtain ⟨hint, hfv⟩ := hrep.2.2 X
  -- Step 6: `m` and `μ_V` are finite on `B_{tA}(x)`.
  have hμK : V.weight (closedBall x (t * A)) < ∞ :=
    (V.weight_finite_on_compact _ hK hKU).lt_top
  have hmK : m (closedBall x (t * A)) < ∞ := by
    have h1 := hbound (t * A) htA0 htA
    rw [hvm] at h1
    exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK)
  -- Step 7: `c` is integrable for every measure finite on `B_{tA}(x)` (`0 ≤ c ≤ 1`, `c = 0` off it).
  have hc_int : ∀ m' : Measure (Euclidean N), m' (closedBall x (t * A)) < ∞ →
      Integrable (fun y : Euclidean N ↦ φ (‖y - x‖ ^ 2 / t ^ 2)) m' := by
    intro m' hm'
    have hon : IntegrableOn (fun y : Euclidean N ↦ φ (‖y - x‖ ^ 2 / t ^ 2))
        (closedBall x (t * A)) m' :=
      Measure.integrableOn_of_bounded (M := 1) hm'.ne hc_cont.aestronglyMeasurable
        (Eventually.of_forall fun y ↦ by
          rw [Real.norm_of_nonneg (hφ_nonneg _)]
          exact hφ_le_one _)
    refine hon.integrable_of_forall_notMem_eq_zero fun y hy ↦ ?_
    by_contra hcy
    exact hy (hc_mem y hcy)
  have hcm := hc_int m hmK
  have hcμ := hc_int V.weight hμK
  -- Step 8: `|δV(X)| ≤ ∫ |η·X| dm ≤ tA ∫ c dm` (Cauchy–Schwarz and step 3).
  have hstep8 : |V.firstVariation (fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x))| ≤
      t * A * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂m := by
    have hfv' : V.firstVariation (fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) =
        -∫ y, inner ℝ (η y) (φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) ∂m := hfv
    rw [hfv', abs_neg, ← integral_const_mul]
    refine abs_integral_le_integral_abs.trans (integral_mono_ae hint.abs (hcm.const_mul _) ?_)
    filter_upwards [hrep.2.1] with y hy
    calc |inner ℝ (η y) (φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x))|
        ≤ ‖η y‖ * ‖φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)‖ := abs_real_inner_le_norm _ _
      _ = ‖φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x)‖ := by rw [hy, one_mul]
      _ ≤ t * A * φ (‖y - x‖ ^ 2 / t ^ 2) := hX_norm y
  -- Step 9: the layer-cake comparison with `(ν, μ) = (m, μ_V)`.
  have hlc := Submission.mono833_radial_layer_cake_le N m V.weight x ρ₀ Λ A t φ
    (fun r hr hrρ ↦ by rw [← hvm]; exact hbound r hr hrρ) hφ.continuous hanti hone hzero hA ht
    htA
  -- Step 10: back to real integrals, `∫ c dm ≤ Λ ∫ c dμ_V` (the right side is finite, `Λ ≥ 0`).
  have hstep10 : ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂m ≤
      Λ * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ hφ_nonneg _)
        hc_cont.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ hφ_nonneg _)
        hc_cont.aestronglyMeasurable]
    calc (∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂m).toReal
        ≤ (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂V.weight).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcμ.lintegral_lt_top.ne)
            hlc
      _ = Λ * (∫⁻ y, ENNReal.ofReal (φ (‖y - x‖ ^ 2 / t ^ 2)) ∂V.weight).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ]
  -- Step 11: `|δV(X)| ≤ tA ∫ c dm ≤ tA Λ ∫ c dμ_V = A Λ t ∫ c dμ_V`.
  calc |V.firstVariation (fun y ↦ φ (‖y - x‖ ^ 2 / t ^ 2) • (y - x))|
      ≤ t * A * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂m := hstep8
    _ ≤ t * A * (Λ * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight) :=
        mul_le_mul_of_nonneg_left hstep10 htA0.le
    _ = A * Λ * t * ∫ y, φ (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight := by ring
/-- Integrating-factor comparison in mean value theorem form (Simon Ch. 8, 3.3, with the
integrating factor `e^{Lt}` of Ch. 4, 3.15–3.17): if `0 ≤ L`, `0 ≤ a ≤ b`, `f` and `g` have
derivatives `f'` and `g'` at every point of `[a, b]`, and `0 ≤ f' t + L f t` and
`g' t ≤ f' t + L f t` on `[a, b]`, then `e^{La} f(a) + (g(b) - g(a)) ≤ e^{Lb} f(b)`. -/
theorem Submission.mono833_integrating_factor_comparison :
    ∀ (L a b : ℝ) (f g f' g' : ℝ → ℝ), 0 ≤ L → 0 ≤ a → a ≤ b → (∀ t ∈ Icc a b, HasDerivAt f (f' t) t) → (∀ t ∈ Icc a b, HasDerivAt g (g' t) t) → (∀ t ∈ Icc a b, 0 ≤ f' t + L * f t) → (∀ t ∈ Icc a b, g' t ≤ f' t + L * f t) → Real.exp (L * a) * f a + (g b - g a) ≤ Real.exp (L * b) * f b := by
  intro L a b f g f' g' hL ha hab hf hg hpos hle
  -- Steps 1–2: by the chain and product rules, `H s = e^{Ls} f s - g s` has derivative
  -- `e^{Lt} (f' t + L f t) - g' t` at every `t ∈ [a, b]`.
  have hH : ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ Real.exp (L * s) * f s - g s)
      (Real.exp (L * t) * (f' t + L * f t) - g' t) t := by
    intro t ht
    have he : HasDerivAt (fun s ↦ Real.exp (L * s)) (Real.exp (L * t) * (L * 1)) t :=
      ((hasDerivAt_id t).const_mul L).exp
    convert (he.fun_mul (hf t ht)).fun_sub (hg t ht) using 1
    ring
  -- Steps 3–4: on `interior [a, b] = (a, b)`, `0 ≤ L t` gives `1 ≤ e^{Lt}`, so with
  -- `u = f' t + L f t ≥ 0` we get `H' t = e^{Lt} u - g' t ≥ u - g' t ≥ 0`; hence `H` is
  -- monotone on `[a, b]` by the mean value theorem.
  have hmono : MonotoneOn (fun s ↦ Real.exp (L * s) * f s - g s) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun t ht ↦ (hH t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hH t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ ?_
    have ht' : t ∈ Icc a b := interior_subset ht
    have h1 : 1 ≤ Real.exp (L * t) := Real.one_le_exp (mul_nonneg hL (ha.trans ht'.1))
    linarith [mul_le_mul_of_nonneg_right h1 (hpos t ht'), hle t ht']
  -- Step 5: `H a ≤ H b` rearranges to the claim.
  have hab' : Real.exp (L * a) * f a - g a ≤ Real.exp (L * b) * f b - g b :=
    hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith
/-- Density limit from monotonicity of the exponentially weighted ratio (Simon Ch. 8, 3.3, p. 210):
if `ρ ↦ e^{Λρ} P(ρ)` is non-decreasing on `(0, ρ₀)` and `P(ρ₀/2) < ∞`, then `P(t)` tends as
`t ↓ 0` to `θ = inf_{(0,ρ₀)} e^{Λρ} P(ρ)`, which is finite and bounded by `e^{Λσ} P(σ)`. -/
theorem Submission.mono833_exp_weighted_density_limit :
    ∀ (P : ℝ → ℝ≥0∞) (ρ₀ Λ : ℝ), 0 < ρ₀ → MonotoneOn (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (Λ * ρ)) * P ρ) (Ioo 0 ρ₀) → P (ρ₀ / 2) ≠ ∞ → ∃ θ : ℝ≥0∞, Tendsto P (𝓝[>] 0) (𝓝 θ) ∧ θ ≠ ∞ ∧ ∀ σ : ℝ, 0 < σ → σ < ρ₀ → θ ≤ ENNReal.ofReal (Real.exp (Λ * σ)) * P σ := by
  intro P ρ₀ Λ hρ₀ hmono hP
  -- `h ρ = e^{Λρ} P(ρ)` is monotone on `I = (0, ρ₀)`; `θ = inf h(I)`.
  set h : ℝ → ℝ≥0∞ := fun ρ ↦ ENNReal.ofReal (Real.exp (Λ * ρ)) * P ρ with hh
  have hmem : ρ₀ / 2 ∈ Ioo 0 ρ₀ := ⟨half_pos hρ₀, half_lt_self hρ₀⟩
  -- Step 2: `h(t) → θ` as `t → 0+`.
  have hlim : Tendsto h (𝓝[>] 0) (𝓝 (sInf (h '' Ioo 0 ρ₀))) :=
    hmono.tendsto_nhdsWithin_Ioo_right ⟨ρ₀ / 2, hmem⟩ (OrderBot.bddBelow _)
  -- Step 3: `θ ≤ h(σ)` for `0 < σ < ρ₀`.
  have hle : ∀ σ : ℝ, 0 < σ → σ < ρ₀ → sInf (h '' Ioo 0 ρ₀) ≤ h σ := fun σ h0 h1 ↦
    sInf_le (mem_image_of_mem h ⟨h0, h1⟩)
  refine ⟨sInf (h '' Ioo 0 ρ₀), ?_, ?_, hle⟩
  · -- Steps 5–7: `P(t) = e^{-Λt} h(t)` and `e^{-Λt} → 1`, so `P(t) → 1 · θ = θ`.
    have hw : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-Λ * t))) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-Λ * t))) :=
        ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      have h0 := hc.tendsto 0
      rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hprod := ENNReal.Tendsto.mul hw (Or.inl one_ne_zero) hlim (Or.inr ENNReal.one_ne_top)
    rw [one_mul] at hprod
    refine hprod.congr fun t ↦ ?_
    rw [hh, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_mul,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  · -- Step 4: `θ ≤ h(ρ₀/2) = e^{Λρ₀/2} P(ρ₀/2) < ∞`.
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP) (hle _ hmem.1 hmem.2)
/-- **Simon Ch. 8, 3.3 (monotonicity formula with `‖δV‖ ≤ Λ μ_V`), p. 210.**
If `V` has locally bounded first variation, `B°_{ρ₀}(x) ⊆ U`, `Λ ≥ 0` and
`‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`, then `e^{Λρ} ρ^{-n} μ_V(B_ρ(x))` is increasing on
`(0, ρ₀)`, `Θ^n(μ_V, x)` exists and is finite, and for `0 < σ ≤ ρ < ρ₀` it is bounded by
`e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))`, while `e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))` plus
`ω_n^{-1} ∫_{Gₙ(B_ρ(x) ∖ B_σ(x))} r^{-n-2} |p_{S^⊥}(y - x)|² dV` is at most
`e^{Λρ} ω_n^{-1} ρ^{-n} μ_V(B_ρ(x))`.  For each smooth cutoff `φ_ε` (SimonGMT's
`monotonicityCutoff ε`) the radial identity (★) for `I(t)/tⁿ` (SimonGMT's
`hasDerivAt_normalized_weightedCutoffMass` with weight `h ≡ 1`) and the bound
`|δV(X_t)| ≤ (1 + ε) Λ t I(t)` (`mono833_radial_first_variation_bound`) feed the
integrating-factor comparison `mono833_integrating_factor_comparison` on `[σ, ρ]`; letting `ε ↓ 0`
by dominated convergence gives the annular inequality, and `mono833_exp_weighted_density_limit`
gives the density. -/
theorem Submission.monotonicity_formula_8_3_3 : MonotonicityFormula := by
  open Chapter04.RectifiableVarifold in
  intro N n U V x ρ₀ Λ hV hρ₀ hball hΛ hbound
  -- Step 0: `0 < ω_n < ∞`.
  have hω₀ : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos _ _ one_pos).ne'
  have hω : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  -- For `t > 0`, `densityRatio` is `ω_n⁻¹` times SimonGMT's `normalizedBallMass = μ_V(B_t) / t^n`.
  have hratio : ∀ t : ℝ, 0 < t →
      densityRatio n V.weight x t = (unitBallVolume n)⁻¹ * V.normalizedBallMass x t := by
    intro t ht
    rw [densityRatio, Varifold.normalizedBallMass, ENNReal.ofReal_pow ht.le,
      ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hω₀) (Or.inl hω),
      mul_assoc]
  -- `|p_{S^⊥}(y - x)|² / r^{n+2} = radialNormalSq / r^n` (both `0` at `y = x`), so on annuli
  -- `normalDefect` is SimonGMT's `annularMonotonicityDefect`.
  have hdefect : ∀ σ ρ : ℝ, normalDefect V x (closedBall x ρ \ closedBall x σ) =
      V.annularMonotonicityDefect x σ ρ := by
    intro σ ρ
    unfold normalDefect Varifold.annularMonotonicityDefect
    refine lintegral_congr fun z ↦ congrArg ENNReal.ofReal ?_
    rw [← Grassmannian.normalProject_eq_sub z.2 (z.1 - x),
      Grassmannian.norm_normalProject_radial_sq]
    rcases eq_or_ne ‖z.1 - x‖ 0 with h | h
    · have hg : z.2.radialNormalSq x z.1 = 0 := by
        simp [Grassmannian.radialNormalSq, Grassmannian.normalProject, norm_eq_zero.1 h]
      simp [hg]
    · field_simp
      ring
  -- Steps 1–5: the real form of (3.3) on the annulus `B_ρ(x) ∖ B_σ(x)`.
  have hreal : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ →
      Real.exp (Λ * σ) * (V.weight.real (closedBall x σ) / σ ^ n) +
          ∫ z in (closedBall x ρ \ closedBall x σ) ×ˢ (univ : Set (Grassmannian N n)),
            z.2.radialNormalSq x z.1 / ‖z.1 - x‖ ^ n ∂V.measure ≤
        Real.exp (Λ * ρ) * (V.weight.real (closedBall x ρ) / ρ ^ n) := by
    intro σ ρ hσ hσρ hρ
    have hρpos : 0 < ρ := hσ.trans_le hσρ
    -- an intermediate radius `ρ < R < ρ₀`, so that `B_R(x)` is a compact subset of `U`
    obtain ⟨R, hρR, hRρ₀⟩ := exists_between hρ
    have hballR : closedBall x R ⊆ U := (closedBall_subset_ball hRρ₀).trans hball
    -- the bounded weight `q = g / max(σ, r)ⁿ` (SimonGMT's `truncatedRadialDefect`)
    have hqm : AEStronglyMeasurable (Varifold.truncatedRadialDefect (n := n) x σ) V.measure :=
      (Varifold.measurable_truncatedRadialDefect x σ).aestronglyMeasurable
    have hqb : ∀ z : Euclidean N × Grassmannian N n, z.1 ∈ closedBall x R →
        ‖Varifold.truncatedRadialDefect x σ z‖ ≤ (σ ^ n)⁻¹ :=
      fun z _ ↦ Varifold.norm_truncatedRadialDefect_le x hσ z
    -- Step 4: the integrating-factor comparison for the cutoff `φ_ε`, for every admissible `ε`.
    have hstep : ∀ ε : ℝ, 0 < ε → ρ * (1 + ε) < R →
        Real.exp ((1 + ε) * Λ * σ) * (V.cutoffMass x (monotonicityCutoff ε) σ / σ ^ n) +
            ((∫ z, scaledRadialCutoff x (monotonicityCutoff ε) ρ z.1 *
                Varifold.truncatedRadialDefect x σ z ∂V.measure) -
              ∫ z, scaledRadialCutoff x (monotonicityCutoff ε) σ z.1 *
                Varifold.truncatedRadialDefect x σ z ∂V.measure) ≤
          Real.exp ((1 + ε) * Λ * ρ) * (V.cutoffMass x (monotonicityCutoff ε) ρ / ρ ^ n) := by
      intro ε hε hεR
      have hA : 0 < 1 + ε := by linarith
      have hφ : ContDiff ℝ 1 (monotonicityCutoff ε) := contDiff_monotonicityCutoff ε
      have hcut : ∀ s, (1 + ε) ^ 2 ≤ s → monotonicityCutoff ε s = 0 := monotonicityCutoff_cutoff hε
      have hpos : ∀ t ∈ Icc σ ρ, 0 < t := fun t ht ↦ hσ.trans_le ht.1
      have hscale : ∀ t ∈ Icc σ ρ, t * (1 + ε) < R :=
        fun t ht ↦ (mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hεR
      -- (★): `(I/tⁿ)' = J'/tⁿ - δV(X_t)/t^{n+1}` (SimonGMT's radial identity with weight `h ≡ 1`)
      have hF : ∀ t ∈ Icc σ ρ, HasDerivAt (fun s ↦ V.cutoffMass x (monotonicityCutoff ε) s / s ^ n)
          ((∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
              z.2.radialNormalSq x z.1 ∂V.measure) / t ^ n -
            V.firstVariation (Varifold.weightedRadialVectorField x (fun _ ↦ 1)
              (monotonicityCutoff ε) t) / t ^ (n + 1)) t := by
        intro t ht
        have hJ := (V.hasDerivAt_weightedCutoffNormalMass x (h := fun _ ↦ 1) continuous_const hφ hA
          hcut (hpos t ht) (hscale t ht) hballR).2
        have hd := V.hasDerivAt_normalized_weightedCutoffMass x (h := fun _ ↦ 1) contDiff_const hφ
          hA hcut (hpos t ht) (hscale t ht) hballR
        rw [hJ.deriv] at hd
        refine hd.congr_deriv ?_
        simp only [Varifold.weightedRadialGradientTerm, fderiv_const_apply, zero_apply, mul_zero,
          integral_zero, mul_one]
        ring
      -- `G(t) = ∫ c_t q dV` has derivative `G'(t) = ∫ ċ_t q dV`
      have hG : ∀ t ∈ Icc σ ρ, HasDerivAt
          (fun s ↦ ∫ z, scaledRadialCutoff x (monotonicityCutoff ε) s z.1 *
            Varifold.truncatedRadialDefect x σ z ∂V.measure)
          (∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
            Varifold.truncatedRadialDefect x σ z ∂V.measure) t := fun t ht ↦
        (V.hasDerivAt_integral_radialCutoff_of_radius x hφ hA hcut (hpos t ht) (hscale t ht) hballR
          hqm hqb).2
      -- Step 3: `δV(X_t) ≤ (1 + ε) Λ t I(t)`
      have hδ : ∀ t ∈ Icc σ ρ, V.firstVariation (Varifold.weightedRadialVectorField x (fun _ ↦ 1)
          (monotonicityCutoff ε) t) ≤
            (1 + ε) * Λ * t * V.cutoffMass x (monotonicityCutoff ε) t := by
        intro t ht
        have hb := Submission.mono833_radial_first_variation_bound N n U V x ρ₀ Λ (1 + ε) t
          (monotonicityCutoff ε) hV hball hΛ hbound hφ (monotonicityCutoff_antitone hε)
          (fun s hs ↦ monotonicityCutoff_one hε hs) hcut hA (hpos t ht) ((hscale t ht).trans hRρ₀)
        have hX : Varifold.weightedRadialVectorField x (fun _ ↦ 1) (monotonicityCutoff ε) t =
            fun y ↦ monotonicityCutoff ε (‖y - x‖ ^ 2 / t ^ 2) • (y - x) := by
          funext y
          simp only [Varifold.weightedRadialVectorField, squaredRadialVectorField, one_smul]
        have hI : V.cutoffMass x (monotonicityCutoff ε) t =
            ∫ y, monotonicityCutoff ε (‖y - x‖ ^ 2 / t ^ 2) ∂V.weight := by
          rw [Varifold.cutoffMass, V.weightedCutoffMass_eq_weight_integral x continuous_const
            hφ.continuous]
          simp only [scaledRadialCutoff, mul_one]
        rw [hX, hI]
        exact (le_abs_self _).trans hb
      -- `J'(t) ≥ 0`, and `G'(t) ≤ J'(t)/tⁿ` (Step 4.2)
      have hJnn : ∀ t ∈ Icc σ ρ, 0 ≤ ∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
          z.2.radialNormalSq x z.1 ∂V.measure := fun t ht ↦
        integral_nonneg fun z ↦ mul_nonneg
          (scaledRadialCutoffDeriv_nonneg x z.1 (monotonicityCutoff_antitone hε) (hpos t ht))
          (z.2.radialNormalSq_nonneg x z.1)
      have hGJ : ∀ t ∈ Icc σ ρ, (∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
            Varifold.truncatedRadialDefect x σ z ∂V.measure) ≤
          (∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
            z.2.radialNormalSq x z.1 ∂V.measure) / t ^ n := by
        intro t ht
        have hgint := (V.hasDerivAt_integral_radialCutoff_of_radius x hφ hA hcut (hpos t ht)
          (hscale t ht) hballR hqm hqb).1
        have hfint := (V.hasDerivAt_integral_radialCutoff_of_radius x hφ hA hcut (hpos t ht)
          (hscale t ht) hballR (Grassmannian.measurable_radialNormalSq x).aestronglyMeasurable
          (B := 1) fun z _ ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (z.2.radialNormalSq_nonneg x z.1)]
            exact z.2.radialNormalSq_le_one x z.1).1
        rw [← integral_div]
        exact integral_mono hgint (hfint.div_const (t ^ n))
          fun z ↦ (Varifold.scaledRadialCutoffDeriv_defect_bounds x z hε hσ ht.1).1
      -- Step 4.1: `J'(t)/tⁿ ≤ F'(t) + (1 + ε) Λ F(t)` with `F = I/tⁿ`
      have hkey : ∀ t ∈ Icc σ ρ, (∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
            z.2.radialNormalSq x z.1 ∂V.measure) / t ^ n ≤
          ((∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
              z.2.radialNormalSq x z.1 ∂V.measure) / t ^ n -
            V.firstVariation (Varifold.weightedRadialVectorField x (fun _ ↦ 1)
              (monotonicityCutoff ε) t) / t ^ (n + 1)) +
          (1 + ε) * Λ * (V.cutoffMass x (monotonicityCutoff ε) t / t ^ n) := by
        intro t ht
        have ht0 : 0 < t := hpos t ht
        have ht0' : t ≠ 0 := ht0.ne'
        have h1 : V.firstVariation (Varifold.weightedRadialVectorField x (fun _ ↦ 1)
            (monotonicityCutoff ε) t) / t ^ (n + 1) ≤
            (1 + ε) * Λ * (V.cutoffMass x (monotonicityCutoff ε) t / t ^ n) := by
          rw [div_le_iff₀ (pow_pos ht0 (n + 1))]
          calc _ ≤ (1 + ε) * Λ * t * V.cutoffMass x (monotonicityCutoff ε) t := hδ t ht
            _ = (1 + ε) * Λ * (V.cutoffMass x (monotonicityCutoff ε) t / t ^ n) * t ^ (n + 1) := by
              rw [pow_succ]
              field_simp
        linarith
      exact Submission.mono833_integrating_factor_comparison ((1 + ε) * Λ) σ ρ
        (fun t ↦ V.cutoffMass x (monotonicityCutoff ε) t / t ^ n)
        (fun t ↦ ∫ z, scaledRadialCutoff x (monotonicityCutoff ε) t z.1 *
          Varifold.truncatedRadialDefect x σ z ∂V.measure)
        (fun t ↦ (∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
            z.2.radialNormalSq x z.1 ∂V.measure) / t ^ n -
          V.firstVariation (Varifold.weightedRadialVectorField x (fun _ ↦ 1)
            (monotonicityCutoff ε) t) / t ^ (n + 1))
        (fun t ↦ ∫ z, scaledRadialCutoffDeriv x (monotonicityCutoff ε) t z.1 *
          Varifold.truncatedRadialDefect x σ z ∂V.measure)
        (mul_nonneg hA.le hΛ) hσ.le hσρ hF hG
        (fun t ht ↦ (div_nonneg (hJnn t ht) (pow_pos (hpos t ht) n).le).trans (hkey t ht))
        (fun t ht ↦ (hGJ t ht).trans (hkey t ht))
    -- Step 5: let `ε ↓ 0` (dominated convergence for the cutoffs, continuity of `exp`).
    have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left inf_le_left
    have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hid
    have hexp : ∀ t : ℝ, Tendsto (fun ε : ℝ ↦ Real.exp ((1 + ε) * Λ * t)) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (Λ * t))) := fun t ↦ by
      simpa only [add_zero, one_mul] using ((hsum.mul_const Λ).mul_const t).rexp
    have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
      simpa only [add_zero, mul_one] using hsum.const_mul ρ
    have hlim := le_of_tendsto_of_tendsto
      (((hexp σ).mul ((V.tendsto_cutoffMass x hσ (hσρ.trans_lt hρR) hballR).div_const (σ ^ n))).add
        ((V.tendsto_integral_radialCutoff x hρpos hρR hballR hqm hqb).sub
          (V.tendsto_integral_radialCutoff x hσ (hσρ.trans_lt hρR) hballR hqm hqb)))
      ((hexp ρ).mul ((V.tendsto_cutoffMass x hρpos hρR hballR).div_const (ρ ^ n)))
      (by
        filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρR)] with ε hε hεR
        exact hstep ε hε hεR)
    -- the limit of `G(ρ) - G(σ)` is the defect integral over the annulus, where `q = g / rⁿ`
    have hsd : (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)),
          Varifold.truncatedRadialDefect x σ z ∂V.measure) -
        ∫ z in closedBall x σ ×ˢ (univ : Set (Grassmannian N n)),
          Varifold.truncatedRadialDefect x σ z ∂V.measure =
        ∫ z in (closedBall x ρ \ closedBall x σ) ×ˢ (univ : Set (Grassmannian N n)),
          z.2.radialNormalSq x z.1 / ‖z.1 - x‖ ^ n ∂V.measure := by
      rw [← setIntegral_sdiff (measurableSet_closedBall.prod MeasurableSet.univ)
        (V.integrableOn_truncatedRadialDefect x hσ
          ((closedBall_subset_closedBall hρR.le).trans hballR))
        (prod_mono_left (closedBall_subset_closedBall hσρ)),
        prod_sdiff_prod, sdiff_self, prod_empty, empty_union]
      refine setIntegral_congr_fun
        ((measurableSet_closedBall.diff measurableSet_closedBall).prod MeasurableSet.univ)
        fun z hz ↦ ?_
      have hr : σ < ‖z.1 - x‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hz.1.2
      simp only [Varifold.truncatedRadialDefect, max_eq_right hr.le]
    rw [hsd] at hlim
    exact hlim
  -- Step 6: the additive form of (3.3) in `[0, ∞]` (every term is finite).
  have hann : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ →
      ENNReal.ofReal (Real.exp (Λ * σ)) * V.normalizedBallMass x σ +
          V.annularMonotonicityDefect x σ ρ ≤
        ENNReal.ofReal (Real.exp (Λ * ρ)) * V.normalizedBallMass x ρ := by
    intro σ ρ hσ hσρ hρ
    have hρpos : 0 < ρ := hσ.trans_le hσρ
    have hρU : closedBall x ρ ⊆ U := (closedBall_subset_ball hρ).trans hball
    have hσU : closedBall x σ ⊆ U := (closedBall_subset_closedBall hσρ).trans hρU
    have hnonneg : ∀ z : Euclidean N × Grassmannian N n,
        0 ≤ z.2.radialNormalSq x z.1 / ‖z.1 - x‖ ^ n :=
      fun z ↦ div_nonneg (z.2.radialNormalSq_nonneg x z.1) (pow_nonneg (norm_nonneg _) n)
    have hint : 0 ≤ ∫ z in (closedBall x ρ \ closedBall x σ) ×ˢ (univ : Set (Grassmannian N n)),
        z.2.radialNormalSq x z.1 / ‖z.1 - x‖ ^ n ∂V.measure := integral_nonneg hnonneg
    have hmass : 0 ≤ Real.exp (Λ * σ) * (V.weight.real (closedBall x σ) / σ ^ n) :=
      mul_nonneg (Real.exp_pos _).le (div_nonneg ENNReal.toReal_nonneg (pow_pos hσ n).le)
    have h := ENNReal.ofReal_le_ofReal (hreal σ ρ hσ hσρ hρ)
    rw [ENNReal.ofReal_add hmass hint, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le, V.ofReal_normalizedBallMass_real x hσ hσU,
      V.ofReal_normalizedBallMass_real x hρpos hρU,
      ofReal_integral_eq_lintegral_ofReal (V.integrableOn_radialDefect_annulus x hσ hρU)
        (Eventually.of_forall hnonneg)] at h
    exact h
  -- Multiplying by `ω_n⁻¹`: the second inequality of the conclusion.
  have hnorm : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ →
      ENNReal.ofReal (Real.exp (Λ * σ)) * densityRatio n V.weight x σ +
          (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ \ closedBall x σ) ≤
        ENNReal.ofReal (Real.exp (Λ * ρ)) * densityRatio n V.weight x ρ := by
    intro σ ρ hσ hσρ hρ
    rw [hratio σ hσ, hratio ρ (hσ.trans_le hσρ), hdefect, mul_left_comm _ (unitBallVolume n)⁻¹,
      mul_left_comm _ (unitBallVolume n)⁻¹, ← mul_add]
    gcongr
    exact hann σ ρ hσ hσρ hρ
  refine ⟨fun σ hσ ρ hρ hσρ ↦ ?_, ?_⟩
  -- Step 7: monotonicity of `e^{Λρ} ρ^{-n} μ_V(B_ρ(x))` on `(0, ρ₀)`.
  · have h := le_self_add.trans (hann σ ρ hσ.1 hσρ hρ.2)
    simp only [Varifold.normalizedBallMass, ENNReal.ofReal_pow hσ.1.le, ENNReal.ofReal_pow hρ.1.le,
      ← mul_div_assoc] at h
    exact h
  -- Step 8: the density `θ`, from the monotonicity of `e^{Λρ} · densityRatio`.
  · have hmono : MonotoneOn (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (Λ * ρ)) *
        densityRatio n V.weight x ρ) (Ioo 0 ρ₀) :=
      fun σ hσ ρ hρ hσρ ↦ le_self_add.trans (hnorm σ ρ hσ.1 hσρ hρ.2)
    have hfin : densityRatio n V.weight x (ρ₀ / 2) ≠ ∞ := by
      rw [hratio _ (half_pos hρ₀)]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hω₀) (V.normalizedBallMass_ne_top x
        (half_pos hρ₀) ((closedBall_subset_ball (half_lt_self hρ₀)).trans hball))
    obtain ⟨θ, hθ, hθtop, hθle⟩ := Submission.mono833_exp_weighted_density_limit
      (densityRatio n V.weight x) ρ₀ Λ hρ₀ hmono hfin
    exact ⟨θ, hθ, hθtop, fun σ ρ hσ hσρ hρ ↦ ⟨hθle σ hσ (hσρ.trans_lt hρ), hnorm σ ρ hσ hσρ hρ⟩⟩
/-- The normal defect of the annuli `B_ρ(x) ∖ B_σ(x)` tends to that of `B_ρ(x)` as `σ ↓ 0`
(Simon Ch. 8, 3.4, p. 211): the defect is continuous from below along the annuli, and its
integrand vanishes at the centre `y = x`.  No hypothesis on `V` or `ρ` is needed. -/
theorem Submission.normalDefect_annulus_tendsto_closedBall :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ : ℝ), Tendsto (fun σ : ℝ ↦ normalDefect V x (closedBall x ρ \ closedBall x σ)) (𝓝[>] 0) (𝓝 (normalDefect V x (closedBall x ρ))) := by
  intro N n U V x ρ
  -- The defect integrand `f` and the measure `ν = V.withDensity f`, so that
  -- `ν(A × G) = normalDefect V x A` for every Borel set `A`.
  set f : Euclidean N × Grassmannian N n → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (‖(z.1 - x) - Grassmannian.project z.2 (z.1 - x)‖ ^ 2 / ‖z.1 - x‖ ^ (n + 2))
    with hf
  set ν := V.measure.withDensity f with hν
  have hD : ∀ A : Set (Euclidean N), MeasurableSet A →
      normalDefect V x A = ν (A ×ˢ (univ : Set (Grassmannian N n))) := fun A hA ↦
    (withDensity_apply f (hA.prod MeasurableSet.univ)).symm
  -- Step 1: `f` vanishes on `{x} × G` (`0 ^ (n + 2) = 0` and `a / 0 = 0`), so `ν({x} × G) = 0`.
  have hcentre : ν ({x} ×ˢ (univ : Set (Grassmannian N n))) = 0 := by
    have hs : MeasurableSet ({x} ×ˢ (univ : Set (Grassmannian N n))) :=
      (measurableSet_singleton x).prod MeasurableSet.univ
    rw [hν, withDensity_apply f hs, setLIntegral_congr_fun hs (g := fun _ ↦ 0) ?_, lintegral_zero]
    rintro ⟨y, S⟩ ⟨hy, -⟩
    rw [mem_singleton_iff] at hy
    subst hy
    simp [hf]
  -- Step 2: removing the centre does not change the defect of `B_ρ(x)`.
  have hpunct : ν ((closedBall x ρ \ {x}) ×ˢ (univ : Set (Grassmannian N n))) =
      normalDefect V x (closedBall x ρ) := by
    have hset : (closedBall x ρ \ {x}) ×ˢ (univ : Set (Grassmannian N n)) =
        closedBall x ρ ×ˢ univ \ {x} ×ˢ univ := by
      ext ⟨y, S⟩
      simp
    rw [hD _ measurableSet_closedBall, hset]
    exact measure_sdiff_null hcentre
  -- Step 3: the annular defect is antitone in `σ` and bounded by the defect of `B_ρ(x)`.
  have hanti : Antitone fun σ : ℝ ↦ normalDefect V x (closedBall x ρ \ closedBall x σ) :=
    fun σ σ' h ↦ lintegral_mono_set <|
      prod_mono (sdiff_subset_sdiff_right (closedBall_subset_closedBall h)) subset_rfl
  have hle : ∀ σ : ℝ, normalDefect V x (closedBall x ρ \ closedBall x σ) ≤
      normalDefect V x (closedBall x ρ) := fun σ ↦
    lintegral_mono_set (prod_mono sdiff_subset subset_rfl)
  -- Step 4: the annuli with inner radii `1 / (k + 1)` increase to `(B_ρ(x) ∖ {x}) × G`.
  set s : ℕ → Set (Euclidean N × Grassmannian N n) := fun k ↦
    (closedBall x ρ \ closedBall x (1 / ((k : ℝ) + 1))) ×ˢ univ with hs
  have hsmono : Monotone s := fun k l hkl ↦
    prod_mono (sdiff_subset_sdiff_right
      (closedBall_subset_closedBall (Nat.one_div_le_one_div hkl))) subset_rfl
  have hsunion : ⋃ k, s k = (closedBall x ρ \ {x}) ×ˢ (univ : Set (Grassmannian N n)) := by
    ext ⟨y, S⟩
    simp only [hs, mem_iUnion, mem_prod, Set.mem_sdiff, mem_closedBall, mem_univ, and_true,
      mem_singleton_iff]
    constructor
    · rintro ⟨k, hyρ, hyk⟩
      refine ⟨hyρ, fun hyx ↦ hyk ?_⟩
      rw [hyx, dist_self]
      positivity
    · rintro ⟨hyρ, hyx⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hyx)
      exact ⟨k, hyρ, not_le.2 hk⟩
  -- Step 5: continuity from below of `ν` along these annuli.
  have hseq : Tendsto
      (fun k : ℕ ↦ normalDefect V x (closedBall x ρ \ closedBall x (1 / ((k : ℝ) + 1))))
      atTop (𝓝 (normalDefect V x (closedBall x ρ))) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν) hsmono
    rw [hsunion, hpunct] at h
    exact h.congr fun k ↦ (hD _ (measurableSet_closedBall.diff measurableSet_closedBall)).symm
  -- Step 6: monotonicity upgrades the sequential limit to the limit as `σ ↓ 0`.
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ Eventually.of_forall fun σ ↦ (hle σ).trans_lt hb⟩
  obtain ⟨k, hk⟩ := (hseq.eventually (lt_mem_nhds ha)).exists
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with σ hσ
  exact hk.trans_le (hanti hσ.2)
/-- Passage to the limit `σ ↓ 0` in an additive annular identity in `[0, ∞]` (Simon Ch. 8, 3.4):
if `P σ + D σ ρ = P ρ` for `0 < σ ≤ ρ < ρ₀` and `D σ ρ → T ρ` as `σ ↓ 0`, then `P` has a limit `θ`
at `0⁺` and `θ + T ρ = P ρ` for `0 < ρ < ρ₀`. -/
theorem Submission.annular_identity_limit_at_zero :
    ∀ (P : ℝ → ℝ≥0∞) (D : ℝ → ℝ → ℝ≥0∞) (T : ℝ → ℝ≥0∞) (ρ₀ : ℝ), 0 < ρ₀ → (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ → P σ + D σ ρ = P ρ) → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → Tendsto (fun σ : ℝ ↦ D σ ρ) (𝓝[>] 0) (𝓝 (T ρ))) → ∃ θ : ℝ≥0∞, Tendsto P (𝓝[>] 0) (𝓝 θ) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → θ + T ρ = P ρ := by
  intro P D T ρ₀ hρ₀ hPD hD
  -- Step 1: `P` is monotone on `(0, ρ₀)`, since `P σ ≤ P σ + D σ ρ = P ρ` for `σ ≤ ρ` there.
  have hmono : MonotoneOn P (Ioo 0 ρ₀) := fun σ hσ ρ hρ hσρ ↦
    le_self_add.trans_eq (hPD σ ρ hσ.1 hσρ hρ.2)
  -- Step 2: hence `P t → θ := inf P((0, ρ₀))` as `t → 0⁺`.
  have hlim : Tendsto P (𝓝[>] 0) (𝓝 (sInf (P '' Ioo 0 ρ₀))) :=
    hmono.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hρ₀) (OrderBot.bddBelow _)
  refine ⟨sInf (P '' Ioo 0 ρ₀), hlim, fun ρ hρ hρρ₀ ↦ ?_⟩
  -- Step 3: `P σ + D σ ρ → θ + T ρ` as `σ → 0⁺`, by continuity of addition on `[0, ∞]`.
  have h₁ : Tendsto (fun σ ↦ P σ + D σ ρ) (𝓝[>] 0) (𝓝 (sInf (P '' Ioo 0 ρ₀) + T ρ)) :=
    hlim.add (hD ρ hρ hρρ₀)
  -- Step 4: on `(0, ρ] ∈ 𝓝[>] 0` the same function is the constant `P ρ`.
  have h₂ : Tendsto (fun σ ↦ P σ + D σ ρ) (𝓝[>] 0) (𝓝 (P ρ)) :=
    tendsto_const_nhds.congr' <| eventuallyEq_of_mem (Ioc_mem_nhdsGT hρ) fun σ hσ ↦
      (hPD σ ρ hσ.1 hσ.2 hρρ₀).symm
  -- Step 5: limits along the proper filter `𝓝[>] 0` in the Hausdorff space `[0, ∞]` are unique.
  exact tendsto_nhds_unique h₁ h₂

/-- **Simon Ch. 8, 3.4 (monotonicity identity, `Λ = 0`), p. 211.**
If `V` is stationary in the open ball `B°_{ρ₀}(x) ⊆ U`, then `Θ^n(μ_V, x)` exists and
`Θ^n(μ_V, x) + ω_n^{-1} ∫_{Gₙ(B_ρ(x))} r^{-n-2} |p_{S^⊥}(y - x)|² dV = ω_n^{-1} ρ^{-n} μ_V(B_ρ(x))`
for `0 < ρ < ρ₀`.  The annular identity for `0 < σ ≤ ρ` is SimonGMT's
`StationaryOn.stationaryMonotonicity` on a ball `B_R(x)` with `ρ < R < ρ₀`; the two preceding
lemmas pass it to the limit `σ ↓ 0`. -/
theorem Submission.stationary_monotonicity_identity_8_3_4 : StationaryMonotonicityIdentity := by
  intro N n U V x ρ₀ hρ₀ hball hstat
  -- Step 0: `0 < ω_n < ∞`.
  have hω₀ : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos _ _ one_pos).ne'
  have hω : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  -- For `t > 0`, `densityRatio` is `ω_n⁻¹` times SimonGMT's `normalizedBallMass = μ_V(B_t) / t^n`.
  have hratio : ∀ t : ℝ, 0 < t →
      densityRatio n V.weight x t = (unitBallVolume n)⁻¹ * V.normalizedBallMass x t := by
    intro t ht
    rw [densityRatio, Varifold.normalizedBallMass, ENNReal.ofReal_pow ht.le,
      ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hω₀) (Or.inl hω),
      mul_assoc]
  -- `|p_{S^⊥}(y - x)|² / r^{n+2} = radialNormalSq / r^n` (both `0` at `y = x`), so on annuli
  -- `normalDefect` is SimonGMT's `annularMonotonicityDefect`.
  have hdefect : ∀ σ ρ : ℝ, normalDefect V x (closedBall x ρ \ closedBall x σ) =
      V.annularMonotonicityDefect x σ ρ := by
    intro σ ρ
    unfold normalDefect Varifold.annularMonotonicityDefect
    refine lintegral_congr fun z ↦ congrArg ENNReal.ofReal ?_
    rw [← Grassmannian.normalProject_eq_sub z.2 (z.1 - x),
      Grassmannian.norm_normalProject_radial_sq]
    rcases eq_or_ne ‖z.1 - x‖ 0 with h | h
    · have hg : z.2.radialNormalSq x z.1 = 0 := by
        simp [Grassmannian.radialNormalSq, Grassmannian.normalProject, norm_eq_zero.1 h]
      simp [hg]
    · field_simp
      ring
  -- Step 1: the annular identity, from stationarity in `B_R(x)` with `R = (ρ + ρ₀) / 2`.
  have hann : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < ρ₀ →
      densityRatio n V.weight x σ +
          (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ \ closedBall x σ) =
        densityRatio n V.weight x ρ := by
    intro σ ρ hσ hσρ hρ
    have hR : ρ < (ρ + ρ₀) / 2 := by linarith
    have hRU : closedBall x ((ρ + ρ₀) / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hball
    have hstatR : V.StationaryOn (ball x ((ρ + ρ₀) / 2)) := fun X hX ↦
      hstat X (hX.trans (ball_subset_ball (by linarith)))
    rw [hratio σ hσ, hratio ρ (hσ.trans_le hσρ), hdefect, ← mul_add,
      hstatR.stationaryMonotonicity hRU hσ hσρ hR]
  -- Steps 2–4: `σ ↓ 0` in the annular identity (density limit and centre continuity of the defect).
  exact Submission.annular_identity_limit_at_zero (densityRatio n V.weight x)
    (fun σ ρ ↦ (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ \ closedBall x σ))
    (fun ρ ↦ (unitBallVolume n)⁻¹ * normalDefect V x (closedBall x ρ)) ρ₀ hρ₀ hann
    fun ρ _ _ ↦ ENNReal.Tendsto.const_mul
      (Submission.normalDefect_annulus_tendsto_closedBall N n U V x ρ)
      (Or.inr (ENNReal.inv_ne_top.2 hω₀))

/-- **Simon Ch. 8, 3.6 (Lemma).** If `V` has locally bounded first variation in `U`, then
`Θ^n(μ_V, x)` exists and is finite for `μ_V`-a.e. `x`, and a Borel `Θ` equals it there: the
monotonicity formula 3.3 applies at `μ_V`-a.e. `x`, and the Borel representative of the density
takes the value of every existing density limit. -/
theorem Submission.density_exists_ae_8_3_6 : DensityExistsAE := by
  intro N n U V hV
  -- Step 1: a Borel `Θ` with `Θ x = Θ^n(μ_V, x)` wherever the density exists (`μ_V` is
  -- σ-finite, hence s-finite).
  obtain ⟨Θ, hΘ, hΘ_eq⟩ := Submission.frt_weq_density_borel_representative N n V.weight
  refine ⟨Θ, hΘ, ?_⟩
  -- Step 2: for `μ_V`-a.e. `x` there are `R > 0`, `Λ ≥ 0` with `B_R(x) ⊆ U` and
  -- `‖δV‖(B_r(x)) ≤ Λ μ_V(B_r(x))` for `0 < r < R` (hypothesis 3.1 of 3.3).
  filter_upwards [Submission.dea_ae_variationMeasure_ball_bound N n U V hV]
    with x ⟨R, Λ, hR, hΛ, hRU, hbound⟩
  -- Step 3: at such `x`, the monotonicity formula 3.3 with `ρ₀ = R` gives a finite density `θ`.
  obtain ⟨θ, hθ, hθ_ne_top, -⟩ := (Submission.monotonicity_formula_8_3_3 N n U V x R Λ hV hR
    (ball_subset_closedBall.trans hRU) hΛ hbound).2
  -- Step 4: `Θ` takes the value of the density limit, so `Θ x = θ`.
  rw [hΘ_eq x θ hθ]
  exact ⟨hθ_ne_top, hθ⟩
/-- **Simon Ch. 8, 3.3, 3.4 and 3.6** (child `monotonicity_density` of `main_theorem`): the
monotonicity formula under `‖δV‖ ≤ Λ μ_V` (3.3), the stationary monotonicity identity (3.4), and
the `μ_V`-a.e. existence and finiteness of `Θ^n(μ_V, ·)` with a Borel representative (3.6).
Each conjunct is its own child theorem; 3.6 is derived there from 3.3 and the a.e. bound 3.1. -/
theorem Submission.monotonicity_and_density_theorems :
    MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE :=
  ⟨Submission.monotonicity_formula_8_3_3, Submission.stationary_monotonicity_identity_8_3_4,
    Submission.density_exists_ae_8_3_6⟩
/-- Test functions for the sequential form of the Alaoglu step in Simon Ch. 1, 4.16 (erratum: the
Alaoglu theorem only yields a subnet).  If `X` is locally compact, Hausdorff and second countable,
there is a sequence `g` in `C_c(X, ℝ)` such that every `f ∈ C_c(X, ℝ)` has a compact
`K ⊇ tsupport f` and, for each `η > 0`, some `g k` with `tsupport (g k) ⊆ K` and `|f - g k| ≤ η`
everywhere. -/
theorem Submission.radon_compactlySupported_countable_approx :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X], ∃ g : ℕ → C_c(X, ℝ), ∀ f : C_c(X, ℝ), ∃ K : Set X,
        IsCompact K ∧ tsupport f ⊆ K ∧ ∀ η : ℝ, 0 < η → ∃ k : ℕ, tsupport (g k) ⊆ K ∧
          ∀ x : X, |f x - g k x| ≤ η := by
  intro X _ _ _ _
  -- Step 1: `C(X, ℝ)` with the compact-open topology is second countable.  This inlines Mathlib's
  -- `ContinuousMap.compactOpen_eq_generateFrom` and `ContinuousMap.instSecondCountableTopology`
  -- (`Mathlib.Topology.ContinuousMap.SecondCountableSpace`, outside this file's imports), with
  -- the closures of the relatively compact basic open sets of `X` as the compact sets.
  set S : Set (Set X) :=
    closure '' {B | B ∈ TopologicalSpace.countableBasis X ∧ IsCompact (closure B)}
  set T : Set (Set ℝ) := TopologicalSpace.countableBasis ℝ
  have hT : TopologicalSpace.IsTopologicalBasis T := TopologicalSpace.isBasis_countableBasis ℝ
  have hS₁ : ∀ K ∈ S, IsCompact K := by
    rintro _ ⟨B, hB, rfl⟩
    exact hB.2
  have hS₂ : ∀ f : C(X, ℝ), ∀ x, ∀ V ∈ T, f x ∈ V → ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V := by
    intro f x V hV hxV
    have hpre : f ⁻¹' V ∈ 𝓝 x := ((hT.isOpen hV).preimage f.continuous).mem_nhds hxV
    obtain ⟨C, hCx, hCV, hC⟩ := local_compact_nhds hpre
    obtain ⟨B, hB, hxB, hBC⟩ := (TopologicalSpace.isBasis_countableBasis X).mem_nhds_iff.1 hCx
    have hBC' : closure B ⊆ C := closure_minimal hBC hC.isClosed
    refine ⟨closure B, ⟨B, ⟨hB, hC.of_isClosed_subset isClosed_closure hBC'⟩, rfl⟩, ?_, ?_⟩
    · exact mem_of_superset
        ((TopologicalSpace.isOpen_of_mem_countableBasis hB).mem_nhds hxB) subset_closure
    · exact fun y hy => hCV (hBC' hy)
  have hkey : (ContinuousMap.compactOpen : TopologicalSpace C(X, ℝ)) =
      TopologicalSpace.generateFrom (Set.image2 (fun K t ↦
        {f : C(X, ℝ) | MapsTo f K (⋃₀ t)}) S {t : Set (Set ℝ) | t.Finite ∧ t ⊆ T}) := by
    apply le_antisymm
    · apply_rules [TopologicalSpace.generateFrom_anti, image2_subset_iff.mpr]
      intro K hK t ht
      exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h ↦ hT.isOpen <| ht.2 h)
    · refine le_of_nhds_le_nhds fun f ↦ ?_
      simp only [ContinuousMap.nhds_compactOpen, le_iInf_iff, le_principal_iff]
      intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
      simp only [TopologicalSpace.nhds_generateFrom]
      obtain ⟨t, htT, htf, hTU, hKT⟩ :
          ∃ t ⊆ T, t.Finite ∧ (∀ V ∈ t, V ⊆ U) ∧ f '' K ⊆ ⋃₀ t := by
        rw [hT.open_eq_sUnion' hU, mapsTo_iff_image_subset, sUnion_eq_biUnion] at hfKU
        obtain ⟨t, ht, hfin, htK⟩ :=
          (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV ↦ hT.isOpen hV.1)
            hfKU
        refine ⟨t, fun _ h ↦ (ht h).1, hfin, fun _ h ↦ (ht h).2, ?_⟩
        rwa [sUnion_eq_biUnion]
      rw [image_subset_iff] at hKT
      obtain ⟨s, hsS, hsf, hKs, hst⟩ :
          ∃ s ⊆ S, s.Finite ∧ K ⊆ ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
        have : ∀ x ∈ K, ∃ L ∈ S, L ∈ 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
          intro x hx
          rcases hKT hx with ⟨V, hVt, hxV⟩
          rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
          exact ⟨L, hLS, hLx, hLV.mono_right <| subset_sUnion_of_mem hVt⟩
        choose! L hLS hLmem hLt using this
        rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
        refine ⟨L '' s, image_subset_iff.2 fun x hx ↦ hLS x <| hsK x hx, s.finite_toSet.image _,
          by rwa [sUnion_image], ?_⟩
        rw [mapsTo_sUnion, forall_mem_image]
        exact fun x hx ↦ hLt x <| hsK x hx
      have hsub : (⋂ L ∈ s, {g : C(X, ℝ) | MapsTo g L (⋃₀ t)}) ⊆ {g | MapsTo g K U} := by
        simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
        exact fun g hg ↦ hg.mono hKs (sUnion_subset hTU)
      refine mem_of_superset ((biInter_mem hsf).2 fun L hL ↦ ?_) hsub
      refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_principal_self _
      exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩
  have hcount : (Set.image2 (fun K t ↦ {f : C(X, ℝ) | MapsTo f K (⋃₀ t)}) S
      {t : Set (Set ℝ) | t.Finite ∧ t ⊆ T}).Countable :=
    (((TopologicalSpace.countable_countableBasis X).mono fun _ hB => hB.1).image _).image2
      (countable_ofPred_finite_subset (TopologicalSpace.countable_countableBasis ℝ)) _
  have : SecondCountableTopology C(X, ℝ) := ⟨⟨_, hcount, hkey⟩⟩
  -- Step 2: a dense sequence `d` in `C(X, ℝ)` approximates every `h` uniformly on compact sets,
  -- since the compact-open topology is that of the compact-convergence uniformity.
  obtain ⟨d, hd⟩ : ∃ d : ℕ → C(X, ℝ), DenseRange d :=
    ⟨TopologicalSpace.denseSeq C(X, ℝ), TopologicalSpace.denseRange_denseSeq C(X, ℝ)⟩
  have happrox : ∀ (h : C(X, ℝ)) (L : Set X), IsCompact L → ∀ η : ℝ, 0 < η →
      ∃ i, ∀ x ∈ L, |h x - d i x| < η := by
    intro h L hL η hη
    have hW : {p : C(X, ℝ) × C(X, ℝ) | ∀ x ∈ L,
        (p.1 x, p.2 x) ∈ {q : ℝ × ℝ | dist q.1 q.2 < η}} ∈ uniformity C(X, ℝ) :=
      ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem
        (i := (L, {q : ℝ × ℝ | dist q.1 q.2 < η})) ⟨hL, Metric.dist_mem_uniformity hη⟩
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hd.inter_nhds_nonempty (UniformSpace.ball_mem_nhds h hW)
    exact ⟨i, fun x hx => by simpa [Real.dist_eq] using hi x hx⟩
  -- Step 3: a compact exhaustion `E` of `X` and Urysohn cutoffs `χ m` with values in `[0, 1]`,
  -- equal to `1` on `E m` and vanishing off `interior (E (m + 1))`.
  set E := CompactExhaustion.choice X
  choose χ hχ1 hχ0 hχc hχI using fun m => exists_continuous_one_zero_of_isCompact
    (E.isCompact m) isOpen_interior.isClosed_compl
    (disjoint_compl_right_iff_subset.2 (E.subset_interior_succ m))
  have hχsupp : ∀ m, tsupport (χ m) ⊆ E (m + 1) := by
    intro m
    refine closure_minimal ?_ (E.isCompact (m + 1)).isClosed
    intro x hx
    by_contra hxE
    exact hx (hχ0 m (fun hxi => hxE (interior_subset hxi)))
  -- Step 4: the family `g (Nat.pair m i) = χ m * d i`, supported in `E (m + 1)`.
  let g : ℕ → C_c(X, ℝ) := fun k =>
    ⟨χ (Nat.unpair k).1 * d (Nat.unpair k).2, (hχc (Nat.unpair k).1).mul_right⟩
  have hgx : ∀ k x, g k x = χ (Nat.unpair k).1 x * d (Nat.unpair k).2 x := fun _ _ => rfl
  have hgsupp : ∀ k, tsupport (g k) ⊆ E ((Nat.unpair k).1 + 1) := fun k =>
    (tsupport_mul_subset_left (f := χ (Nat.unpair k).1) (g := d (Nat.unpair k).2)).trans
      (hχsupp _)
  clear_value g
  -- Step 5: if `tsupport f ⊆ E m`, take `K = E (m + 1)`.  As `f = χ m * f`, we get
  -- `|f - χ m * d i| = χ m * |f - d i| ≤ η` once `|f - d i| < η` on `E (m + 1)`.
  refine ⟨g, fun f => ?_⟩
  obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact f.hasCompactSupport.isCompact
  refine ⟨E (m + 1), E.isCompact _, hm.trans (E.subset_succ m), fun η hη => ?_⟩
  obtain ⟨i, hi⟩ := happrox f (E (m + 1)) (E.isCompact _) η hη
  refine ⟨Nat.pair m i, ?_, fun x => ?_⟩
  · simpa [Nat.unpair_pair] using hgsupp (Nat.pair m i)
  · have hfx : f x = χ m x * f x := by
      by_cases hx : x ∈ E m
      · rw [hχ1 m hx, Pi.one_apply, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hm h)), mul_zero]
    rw [hgx, Nat.unpair_pair, hfx, ← mul_sub, abs_mul, abs_of_nonneg (hχI m x).1]
    by_cases hx : x ∈ E (m + 1)
    · calc χ m x * |f x - d i x| ≤ 1 * η :=
            mul_le_mul (hχI m x).2 (hi x hx).le (abs_nonneg _) zero_le_one
        _ = η := one_mul η
    · rw [hχ0 m (fun h => hx (interior_subset h)), Pi.zero_apply, zero_mul]
      exact hη.le
/-- Final step of Simon Ch. 1, 4.16 (Riesz representation, Theorem 4.12): if the masses `μ_j(K)` of
each compact `K` are eventually bounded and `∫ f dμ_j` converges for every `f ∈ C_c(X, ℝ)`, then
the limits are the integrals `∫ f dν` against a single locally finite measure `ν` on `X`. -/
theorem Submission.radon_exists_measure_of_tendsto_integral :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
      [BorelSpace X] (μ : ℕ → Measure X),
      (∀ K : Set X, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ j in atTop, μ j K ≤ C) →
      (∀ f : C_c(X, ℝ), ∃ L : ℝ, Tendsto (fun j ↦ ∫ x, f x ∂(μ j)) atTop (𝓝 L)) →
      ∃ ν : Measure X, IsLocallyFiniteMeasure ν ∧
        ∀ f : C_c(X, ℝ), Tendsto (fun j ↦ ∫ x, f x ∂(μ j)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  intro X _ _ _ _ _ μ hμ hconv
  -- Step 1: each `f ∈ C_c(X, ℝ)` is `μ j`-integrable for all large `j`, since `f` is continuous,
  -- vanishes off the compact set `tsupport f`, and `μ j (tsupport f) < ∞` for large `j`.
  have hint : ∀ f : C_c(X, ℝ), ∀ᶠ j in atTop, Integrable f (μ j) := by
    intro f
    obtain ⟨C, hC, hev⟩ := hμ (tsupport f) f.hasCompactSupport.isCompact
    filter_upwards [hev] with j hj
    have : IsFiniteMeasure ((μ j).restrict (tsupport f)) :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hC hj)
    exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  -- Step 2: the limit functional `F f = lim_j ∫ f dμ_j` is additive, homogeneous and positive.
  choose F hF using hconv
  have hadd : ∀ f g : C_c(X, ℝ), F (f + g) = F f + F g := by
    intro f g
    refine tendsto_nhds_unique (hF (f + g)) (((hF f).add (hF g)).congr' ?_)
    filter_upwards [hint f, hint g] with j hf hg
    rw [CompactlySupportedContinuousMap.coe_add]
    exact (integral_add hf hg).symm
  have hsmul : ∀ (c : ℝ) (f : C_c(X, ℝ)), F (c • f) = c • F f := by
    intro c f
    refine tendsto_nhds_unique (hF (c • f)) (((hF f).const_smul c).congr fun j ↦ ?_)
    rw [CompactlySupportedContinuousMap.coe_smul]
    exact (integral_smul c _).symm
  have hpos : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ F f := fun f hf ↦
    ge_of_tendsto' (hF f) fun j ↦ integral_nonneg (CompactlySupportedContinuousMap.le_def.1 hf)
  -- Step 3: by the Riesz–Markov–Kakutani theorem, `F f = ∫ f dν` for the Riesz measure `ν` of `F`,
  -- which is regular, hence finite on compact sets, hence locally finite.
  refine ⟨RealRMK.rieszMeasure (PositiveLinearMap.mk₀ ⟨⟨F, hadd⟩, hsmul⟩ hpos), inferInstance,
    fun f ↦ ?_⟩
  rw [RealRMK.integral_rieszMeasure]
  exact hF f

/-- **Simon Ch. 8, 3.7** (child `density_semicontinuity` of `main_theorem`; Step 4 of its proof).
Remark 3.8(1) (child `variation_lsc`) gives that `V` has locally bounded first variation and
`‖δV‖(W) ≤ liminf_i ‖δV_i‖(W)`.  The printed steps (1)–(5) (child `lower_density_ae`, run with the
monotonicity formula 3.3) give `liminf_{ρ↓0} μ_V(B_ρ(y)) / (ω_n ρ^n) ≥ 1` for `μ_V`-a.e. `y`, and
Lemma 3.6 for `V` gives that `Θ^n(μ_V, y)` exists for `μ_V`-a.e. `y`.  Where the density exists it
equals that `liminf`, so it is `≥ 1`. -/
theorem Submission.density_semicontinuity_theorem : DensitySemicontinuity := by
  intro N n U Vi V B hconv hLB hbound hdens hsmall
  obtain ⟨hV, hle⟩ :=
    Submission.variationMeasure_le_liminf_of_radonConverges N n U Vi V hconv hLB hbound
  refine ⟨hV, hle, ?_⟩
  obtain ⟨Θ, -, hΘ⟩ := Submission.monotonicity_and_density_theorems.2.2 N n U V hV
  have hlow := Submission.lower_density_ge_one_ae_of_radonConverges
    Submission.monotonicity_and_density_theorems.1 N n U Vi V B hconv hLB hbound hdens hsmall
  filter_upwards [hΘ, hlow] with y hy hy'
  have h : Tendsto (densityRatio n V.weight y) (𝓝[>] 0) (𝓝 (Θ y)) := hy.2
  exact ⟨Θ y, hy.2, by rwa [h.liminf_eq] at hy'⟩

/-- **Simon Ch. 8, 4.1 (Constancy Theorem), corrected** (child `constancy` of `main_theorem`).
If `M = ∅`, then `V` is carried by `U ∩ spt μ_V = ∅`, so `V = 0` and `θ₀ = 0` works.  Otherwise the
measure form `V = (c H^n ⌞ (M ∩ U)).map (x ↦ (x, T x))` with `c < ∞` (child
`stationary_constancy_tangentGraph_measure`) gives the formula with `θ₀ = c`: if `c = 0` both
sides vanish, and if `c ≠ 0` then `T x` is the only point of `G(N,n)` whose plane is
`classicalTangentSpace M x`, since a point of `G(N,n)` is determined by its plane. -/
theorem Submission.constancy_theorem : ConstancyTheorem := by
  intro N n U V M hV hM hsupp hconn
  rcases M.eq_empty_or_nonempty with rfl | hne
  · have hV0 : V.measure = 0 := by
      refine ae_eq_bot.mp (eventually_false_iff_eq_bot.mp ?_)
      filter_upwards [V.ae_mem_domain,
        ae_of_ae_map measurable_fst.aemeasurable V.weight.support_mem_ae] with z hzU hz
      exact hsupp ⟨hzU.1, hz⟩
    exact ⟨0, le_rfl, fun A _ ↦ by simp [hV0]⟩
  obtain ⟨c, T, hc, hT, hVc, hplane⟩ :=
    Submission.stationary_constancy_tangentGraph_measure N n U V M hV hM hsupp hconn hne
  refine ⟨c.toReal, ENNReal.toReal_nonneg, fun A hA ↦ ?_⟩
  have hgraph : Measurable fun x : Euclidean N ↦ (x, T x) := measurable_id.prodMk hT
  rw [ENNReal.ofReal_toReal hc, hVc, Measure.map_apply hgraph hA, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hgraph hA)]
  -- Now `V(A) = c H^n({x ∈ M ∩ U : (x, T x) ∈ A})`; for `c ≠ 0` this set is the contract's.
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zero_mul, zero_mul]
  congr 2
  ext x
  refine ⟨fun ⟨hxA, hx⟩ ↦ ⟨hx, T x, hplane hc0 x hx, hxA⟩, fun ⟨hx, S, hS, hxS⟩ ↦ ⟨?_, hx⟩⟩
  -- `S` and `T x` have the same plane, so they are the same point of `G(N,n)`.
  obtain rfl : S = T x := by
    rw [← S.ofSubmodule_plane, ← (T x).ofSubmodule_plane]
    congr 1
    exact SetLike.coe_injective (hS.trans (hplane hc0 x hx).symm)
  exact hxS

/-- **Simon Ch. 8, Lemma 1.3, last part** (child `identity_of_limits` of `plane_disintegration`):
if for `μ_V`-a.e. `x` the measure `η(x)` on `G(N,n)` is a probability measure and the slice ratios
`(∫_{Gₙ(B_ρ(x))} β(S) dV(y,S)) / μ_V(B_ρ(x))` tend to `∫ β dη(x)` for every continuous `β`, then
`∫_{Gₙ(A)} β(S) dV(y,S) = ∫_A ∫ β dη(x) dμ_V(x)` for Borel `A` and continuous `β ≥ 0`.  The density
`e` of `plane_disint_slice_density` is the limit of the same ratios, so `e(x) = ∫ β dη(x)` for
`μ_V`-a.e. `x` by uniqueness of limits ("`e(x,j)` is exactly `η̃_V^(x)(β_j)`"). -/
theorem Submission.plane_disint_identity_of_limits :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (η : Euclidean N → Measure (Grassmannian N n)), (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧ ∀ β : C(Grassmannian N n, ℝ), Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) → ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight := by
  intro N n U V η hη A β hA hβ
  -- Printed (1)–(2) for `β`: the slice ratios tend to `e(x)` a.e. and `γ(A) = ∫_A e dμ_V`.
  obtain ⟨e, -, he, hslice⟩ := Submission.plane_disint_slice_density N n U V β hβ
  rw [hslice A hA]
  refine setLIntegral_congr_fun_ae hA ?_
  -- `e(x) = ∫ β dη(x)` by uniqueness of limits as `ρ ↓ 0`; `β` is bounded, so `η(x)`-integrable.
  filter_upwards [hη, he] with x ⟨hprob, hlim⟩ hex _
  rw [tendsto_nhds_unique hex (hlim β)]
  exact ofReal_integral_eq_lintegral_ofReal
    (β.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace β))
    (ae_of_all _ hβ)

/-- **Simon Ch. 8, Lemma 1.3, pp. 207–208** (child `plane_disintegration` of `main_theorem`): the
measures `η_V^(x)` on `G(N,n)` that disintegrate `V` along its weight `μ_V`.  Child
`plane_disint_pointwise_measure` gives, for `μ_V`-a.e. `x`, a probability measure that is the limit
of the normalized slices of `V` over `B_ρ(x)`.  `η(x)` is such a measure wherever one exists; its
value on the remaining `μ_V`-null set is irrelevant (the printed lemma only defines `η_V^(x)` for
`μ_V`-a.e. `x`).  The second part is child `plane_disint_identity_of_limits` applied to this `η`. -/
theorem Submission.plane_disintegration :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U),
      ∃ η : Euclidean N → Measure (Grassmannian N n),
        (∀ᵐ x ∂V.weight, IsProbabilityMeasure (η x) ∧
          ∀ β : C(Grassmannian N n, ℝ),
            Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)),
                β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal)
              (𝓝[>] 0) (𝓝 (∫ S, β S ∂(η x)))) ∧
        ∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A →
          (∀ S, 0 ≤ β S) →
          ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure =
            ∫⁻ x in A, (∫⁻ S, ENNReal.ofReal (β S) ∂(η x)) ∂V.weight := by
  intro N n U V
  -- `Filter.skolem` chooses `η(x)` from the first part wherever it exists.
  obtain ⟨η, hη⟩ := Filter.skolem.1 (Submission.plane_disint_pointwise_measure N n U V)
  exact ⟨η, hη, Submission.plane_disint_identity_of_limits N n U V η hη⟩

/-- Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(y,S) = g(y)`):
if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`,
`t^{-n} ∫ g(t^{-1}(y - x)) dμ_V(y) → θ ∫_T g dH^n` as `t ↓ 0`. -/
theorem Submission.tgc_weight_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ y, g (t⁻¹ • (y - x)) ∂V.weight) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)))) := by
  intro N n U V x T θ hT g
  -- Step 1: the lifted test function `f(y, S) = g(y)` is compactly supported, `G(N,n)` being
  -- compact (it vanishes off `tsupport g ×ˢ univ`).
  have hf : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1) :=
    HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) fun z hz ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨h, mem_univ _⟩
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    ⟨⟨fun z ↦ g z.1, (map_continuous g).comp continuous_fst⟩, hf⟩
  have hfc : Continuous (f : Euclidean N × Grassmannian N n → ℝ) := map_continuous f
  -- Step 2: the convergence clause of Definition 1.1 applied to `f`.
  have hlim := hT.2.2 f
  -- Step 3: the limit, `∫ f dv(T) = ∫_T g dH^n` (push-forward along `y ↦ (y, T)`).
  have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
      ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) := by
    rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T)) (by fun_prop)
      hfc.aestronglyMeasurable]
    rfl
  rw [hplane] at hlim
  -- Step 4: for `t > 0`, `∫ f dV_{x,t} = t^{-n} ∫ g(t^{-1}(y - x)) dμ_V(y)`; step 5: these agree
  -- on `Ioi 0 ∈ 𝓝[>] 0`, so the limit transfers.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (le_of_lt ht)) n
  have hg : Continuous fun y : Euclidean N ↦ g (t⁻¹ • (y - x)) := by fun_prop
  rw [rescaledMeasure, integral_smul_measure,
    integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2))
      (by fun_prop) hfc.aestronglyMeasurable, ENNReal.toReal_ofReal ht', smul_eq_mul,
    Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  rfl

/-- `H^n(T ∩ B_r(0)) = ω_n r^n` for an `n`-plane `T ∈ G(N,n)` and every `r ≥ 0` (step (1.2) of
the tangent graph cover proof): an isometric parametrization of `T` by `ℝ^n` carries `H^n` on `T`
to Lebesgue measure on `ℝ^n`. -/
theorem Submission.tgc_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: an orthonormal basis of `T.plane` indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  -- Step 2: the linear isometry `J : ℝ^n → ℝ^N`, with range `T.plane`.
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  -- Step 3: `J (B_r(0)) = T.plane ∩ B_r(0)`.
  have himg : J '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(b.repr.symm u).2, ?_⟩
      rw [mem_closedBall_zero_iff, J.norm_map]
      exact mem_closedBall_zero_iff.mp hu
    · rintro ⟨hy, hyr⟩
      exact ⟨b.repr ⟨y, hy⟩, by simpa using hyr, by simp [J]⟩
  -- Steps 4–6: isometry invariance, `μHE[n] = volume` on `ℝ^n`, and the Haar closed-ball formula.
  rw [← himg, J.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hr,
    finrank_euclideanSpace_fin, unitBallVolume, ENNReal.ofReal_pow hr, mul_comm]

/-- **Lower mass bound at a tangent point** (child `lower_mass_bound` of `tangent_graph_cover`,
step (1.3) of its proof, in eventual form): if `V` has tangent plane `T` with multiplicity `θ` at
`x`, then for every `c < θ ω_n` we have `c t^n ≤ μ_V(B_t(x))` for all small `t > 0`.  Choose
`κ ∈ (0,1)` with `c < θ ω_n κ^n` and the cut-off `g = min(1, max(0, (1 - |v|)/(1 - κ)))`, so that
`1_{B_κ(0)} ≤ g ≤ 1_{B_1(0)}`.  Then `θ ∫_T g dH^n ≥ θ H^n(T ∩ B_κ(0)) = θ ω_n κ^n > c`
(`plane_ball_measure`), the weight blow-ups `t^{-n} ∫ g((y - x)/t) dμ_V(y)` tend to
`θ ∫_T g dH^n` (`weight_blowup`), and each of them is at most `t^{-n} μ_V(B_t(x))`. -/
theorem Submission.tgc_tangent_weight_lower_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ c : ℝ≥0∞, c < ENNReal.ofReal θ * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ V.weight (closedBall x t) := by
  intro N n U V x T θ hT c hc
  -- Step 1: `θ > 0` and `ω_n < ∞`, so `c < θ ω_n < ∞`; pass to real numbers.
  have hθ : 0 < θ := hT.2.1
  have hω : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcr : c.toReal < θ * (unitBallVolume n).toReal := by
    have h := (ENNReal.toReal_lt_toReal hc_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 2: choose `κ ∈ (0,1)` with `c < θ ω_n κ^n`, by continuity of `κ ↦ θ ω_n κ^n` at `1`.
  have hcont : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    have h := ((continuous_pow n).tendsto (1 : ℝ)).const_mul (θ * (unitBallVolume n).toReal)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hκ01 : ∀ᶠ κ in 𝓝[<] (1 : ℝ), κ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨κ, hκc, hκ0, hκ1⟩ := ((hcont.eventually (eventually_gt_nhds hcr)).and hκ01).exists
  have h1κ : 0 < 1 - κ := sub_pos.2 hκ1
  -- Step 3: the cut-off `g(v) = min(1, max(0, (1 - |v|)/(1 - κ)))` lies in `C_c(ℝ^N)`, and
  -- `1_{B_κ(0)} ≤ g ≤ 1_{B_1(0)}`.
  have hcut : ∀ v : Euclidean N, 1 ≤ ‖v‖ → min 1 (max 0 ((1 - ‖v‖) / (1 - κ))) = 0 :=
    fun v hv ↦ by
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) h1κ.le),
        min_eq_right zero_le_one]
  have hout : ∀ v : Euclidean N, v ∉ closedBall (0 : Euclidean N) 1 → 1 ≤ ‖v‖ := fun v hv ↦
    (not_le.1 (mt mem_closedBall_zero_iff.2 hv)).le
  let g : C_c(Euclidean N, ℝ) :=
    ⟨⟨fun v ↦ min 1 (max 0 ((1 - ‖v‖) / (1 - κ))), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 1) fun v hv ↦ hcut v (hout v hv)⟩
  have hg : ∀ v, g v = min 1 (max 0 ((1 - ‖v‖) / (1 - κ))) := fun _ ↦ rfl
  have hg_nonneg : ∀ v, 0 ≤ g v := fun _ ↦ le_min zero_le_one (le_max_left _ _)
  have hg_le : ∀ v, g v ≤ 1 := fun _ ↦ min_le_left _ _
  have hg_one : ∀ v : Euclidean N, ‖v‖ ≤ κ → g v = 1 := fun v hv ↦ by
    have h : 1 ≤ (1 - ‖v‖) / (1 - κ) := (one_le_div h1κ).2 (by linarith)
    rw [hg, max_eq_right (zero_le_one.trans h), min_eq_left h]
  -- Step 4: `θ ∫_T g dH^n ≥ θ H^n(T ∩ B_κ(0)) = θ ω_n κ^n > c` (`plane_ball_measure`).
  set ν := (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hνB : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n :=
    fun r hr ↦ by
      rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact Submission.tgc_plane_closedBall_hausdorff N n T r hr
  have hνB_ne : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) ≠ ∞ := fun r hr ↦ by
    rw [hνB r hr]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hg_int : Integrable g ν :=
    (integrableOn_iff_integrable_of_support_subset fun v hv ↦
        by_contra fun hv' ↦ hv ((hg v).trans (hcut v (hout v hv')))).1
      (Measure.integrableOn_of_bounded (M := 1) (hνB_ne 1 zero_le_one)
        (map_continuous g).aestronglyMeasurable
        (ae_of_all _ fun v ↦ (Real.norm_of_nonneg (hg_nonneg v)).trans_le (hg_le v)))
  have hκ_int : Integrable ((closedBall (0 : Euclidean N) κ).indicator fun _ ↦ (1 : ℝ)) ν :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const (hνB_ne κ hκ0.le))
  have hκ_le : (closedBall (0 : Euclidean N) κ).indicator (fun _ ↦ (1 : ℝ)) ≤ g := fun v ↦ by
    by_cases hv : v ∈ closedBall (0 : Euclidean N) κ
    · rw [indicator_of_mem hv, hg_one v (mem_closedBall_zero_iff.1 hv)]
    · rw [indicator_of_notMem hv]
      exact hg_nonneg v
  have hint : (unitBallVolume n).toReal * κ ^ n ≤
      ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) := by
    have h := integral_mono hκ_int hg_int hκ_le
    rwa [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      measureReal_def, hνB κ hκ0.le, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hκ0.le] at h
  have hℓ : c.toReal <
      θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) :=
    calc c.toReal < θ * (unitBallVolume n).toReal * κ ^ n := hκc
      _ = θ * ((unitBallVolume n).toReal * κ ^ n) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hint hθ.le
  -- Step 5: by `weight_blowup`, `t^{-n} ∫ g((y - x)/t) dμ_V(y) > c` for all small `t > 0`.
  filter_upwards [(Submission.tgc_weight_blowup_tendsto N n U V x T θ hT g).eventually
    (eventually_gt_nhds hℓ), self_mem_nhdsWithin] with t ht ht0
  replace ht0 : 0 < t := ht0
  -- Step 6: `g((y - x)/t) ≤ 1_{B_t(x)}(y)`, so the blow-up integral is at most `μ_V(B_t(x))`.
  rcases eq_or_ne (V.weight (closedBall x t)) ∞ with hB | hB
  · rw [hB]
    exact le_top
  have hle : ∀ y, g (t⁻¹ • (y - x)) ≤ (closedBall x t).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ closedBall x t
    · rw [indicator_of_mem hy]
      exact hg_le _
    · rw [mem_closedBall, not_le] at hy
      have h : 1 ≤ ‖t⁻¹ • (y - x)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_eq_div,
          one_le_div ht0, ← dist_eq_norm]
        exact hy.le
      rw [indicator_of_notMem (by rwa [mem_closedBall, not_le]), hg, hcut _ h]
  have hcmp : ∫ y, g (t⁻¹ • (y - x)) ∂V.weight ≤ (V.weight (closedBall x t)).toReal := by
    have h : ∫ y, g (t⁻¹ • (y - x)) ∂V.weight ≤
        ∫ y, (closedBall x t).indicator (fun _ ↦ (1 : ℝ)) y ∂V.weight :=
      integral_mono_of_nonneg (ae_of_all _ fun y ↦ hg_nonneg _)
        ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hB))
        (ae_of_all _ hle)
    rwa [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      measureReal_def] at h
  -- Step 7: back in `[0, ∞]`, `c < t^{-n} μ_V(B_t(x))`; multiply by `t^n`.
  have htn : 0 ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 ht0.le) n
  have hlt : c < ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall x t) := by
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
      (ht.trans_le (mul_le_mul_of_nonneg_left hcmp htn))
    rwa [ENNReal.ofReal_toReal hc_top, ENNReal.ofReal_mul htn, ENNReal.ofReal_toReal hB] at h
  calc c * ENNReal.ofReal t ^ n
      ≤ ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall x t) * ENNReal.ofReal t ^ n :=
        mul_le_mul_left hlt.le _
    _ = V.weight (closedBall x t) := by
        rw [mul_right_comm, ← ENNReal.ofReal_pow ht0.le, ← ENNReal.ofReal_mul htn, ← mul_pow,
          inv_mul_cancel₀ ht0.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-- **Cone decay at a tangent point** (child `cone_decay` of `tangent_graph_cover`, step (1.4) of
its proof; the varifold form of the second limit in Simon Ch. 3, Remark 1.5(3), for a tangent plane
as in Ch. 8, 1.1): if `V` has tangent plane `T` with multiplicity `θ` at `x` and `n ≥ 1`, then for
every `β > 0` the cone section `{y ∈ B_t(x) : β|y - x| ≤ |(y - x) - p_T(y - x)|}` has `μ_V`-mass
`o(t^n)` as `t ↓ 0`.  The rescaled section `C` meets `T` only at `0`, an `H^n`-null set, so a
cut-off `g ≥ 1_C` has `θ ∫_T g dH^n` as small as we like, and the weight blow-ups of `g` bound
`t^{-n}` times the `μ_V`-mass of the section. -/
theorem Submission.tgc_tangent_cone_weight_decay :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), 0 < n → HasTangentPlane V x T θ → ∀ β : ℝ, 0 < β → ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), V.weight {y | y ∈ closedBall x t ∧ β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤ ε * ENNReal.ofReal t ^ n := by
  intro N n U V x T θ hn hT β hβ ε hε
  have hblow := Submission.tgc_weight_blowup_tendsto N n U V x T θ hT
  have hplane := Submission.tgc_plane_closedBall_hausdorff N n T
  -- Step 1: the case `ε = ∞` is trivial; otherwise `ε = ofReal e` with `e > 0`.
  by_cases hεtop : ε = ∞
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hεtop, ENNReal.top_mul (pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne')]
    exact le_top
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 < e ∧ ε = ENNReal.ofReal e :=
    ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεtop, (ENNReal.ofReal_toReal hεtop).symm⟩
  obtain ⟨hxU, hθ, -⟩ := hT
  set ν : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hp_cont : Continuous (Grassmannian.project T) :=
    T.projectionLinearMap.continuous_of_finiteDimensional
  have hp_smul : ∀ (c : ℝ) (v : Euclidean N),
      Grassmannian.project T (c • v) = c • Grassmannian.project T v :=
    fun c v ↦ T.projectionLinearMap.map_smul c v
  -- Step 2: the rescaled cone section `C`; it is closed, lies in `B_1(0)`, contains `0`, and
  -- `t⁻¹ • (y - x) ∈ C` for every `y` in the cone section at scale `t`.
  set C : Set (Euclidean N) := {w | ‖w‖ ≤ 1 ∧ β * ‖w‖ ≤ ‖w - Grassmannian.project T w‖}
  have hC_closed : IsClosed C :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le (continuous_const.mul continuous_norm) (continuous_id.sub hp_cont).norm)
  have hC_ball : C ⊆ closedBall 0 1 := fun w hw ↦ by simpa using hw.1
  have hC0 : (0 : Euclidean N) ∈ C := by
    refine ⟨by simp, ?_⟩
    rw [norm_zero, mul_zero]
    exact norm_nonneg _
  have hC_scale : ∀ t : ℝ, 0 < t → ∀ y : Euclidean N, y ∈ closedBall x t →
      β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖ → t⁻¹ • (y - x) ∈ C := by
    intro t ht y hyB hyβ
    have hti : 0 ≤ t⁻¹ := inv_nonneg.2 ht.le
    have hyx : ‖y - x‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hyB
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg hti]
      calc t⁻¹ * ‖y - x‖ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hyx hti
        _ = 1 := inv_mul_cancel₀ ht.ne'
    · rw [hp_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hti]
      calc β * (t⁻¹ * ‖y - x‖) = t⁻¹ * (β * ‖y - x‖) := by ring
        _ ≤ t⁻¹ * ‖(y - x) - Grassmannian.project T (y - x)‖ :=
          mul_le_mul_of_nonneg_left hyβ hti
  -- Step 3: `C ∩ T ⊆ {0} = T ∩ B_0(0)`, which is `H^n`-null since `n ≥ 1`; so `ν C = 0`.
  have hνC : ν C = 0 := by
    rw [hν, Measure.restrict_apply hC_closed.measurableSet]
    refine measure_mono_null (t := (T.plane : Set (Euclidean N)) ∩ closedBall 0 0) ?_ ?_
    · rintro w ⟨hwC, hwT⟩
      have hpw : Grassmannian.project T w = w := T.projectionLinearMap_apply_of_mem hwT
      have h0 : β * ‖w‖ ≤ β * 0 := by
        have := hwC.2
        rwa [hpw, sub_self, norm_zero, ← mul_zero β] at this
      refine ⟨hwT, mem_closedBall.2 ?_⟩
      rw [dist_zero_right]
      exact le_of_mul_le_mul_left h0 hβ
    · rw [hplane 0 le_rfl, ENNReal.ofReal_zero, zero_pow hn.ne', mul_zero]
  -- Step 4: thickenings of `C` lie in `B_2(0)`, which has finite `ν`-measure; choose `κ ∈ (0,1]`
  -- with `ν (cthickening κ C) < e / θ`.
  have hthick : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → cthickening r C ⊆ closedBall 0 2 := by
    intro r hr0 hr1
    calc cthickening r C ⊆ cthickening r (closedBall (0 : Euclidean N) 1) :=
          cthickening_subset_of_subset r hC_ball
      _ = closedBall 0 (r + 1) := cthickening_closedBall hr0 zero_le_one 0
      _ ⊆ closedBall 0 2 := closedBall_subset_closedBall (by linarith)
  have hν2 : ν (closedBall 0 2) ≠ ∞ := by
    rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane 2 zero_le_two]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hν1 : ν (cthickening 1 C) ≠ ∞ :=
    ne_top_of_le_ne_top hν2 (measure_mono (hthick 1 zero_le_one le_rfl))
  have htend : Tendsto (fun r ↦ ν (cthickening r C)) (𝓝 0) (𝓝 0) := by
    rw [← hνC]
    exact tendsto_measure_cthickening_of_isClosed ⟨1, one_pos, hν1⟩ hC_closed
  have heθ : 0 < e / θ := div_pos he hθ
  obtain ⟨δ, hδ, hδν⟩ :=
    Metric.eventually_nhds_iff.1 (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 heθ)))
  set κ : ℝ := min (δ / 2) 1
  have hκ0 : 0 < κ := lt_min (half_pos hδ) one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκν : ν (cthickening κ C) < ENNReal.ofReal (e / θ) := by
    refine hδν ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hκ0]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hκfin : ν (cthickening κ C) ≠ ∞ := (hκν.trans ENNReal.ofReal_lt_top).ne
  have hκreal : (ν (cthickening κ C)).toReal < e / θ := by
    have := (ENNReal.toReal_lt_toReal hκfin ENNReal.ofReal_ne_top).2 hκν
    rwa [ENNReal.toReal_ofReal heθ.le] at this
  -- Step 5: the cut-off `g = max(0, 1 - dist(·, C)/κ)`: continuous, `0 ≤ g ≤ 1`, `g = 1` on `C`,
  -- `g = 0` off `cthickening κ C ⊆ B_2(0)`; hence `g ∈ C_c(ℝ^N)`.
  set g₀ : Euclidean N → ℝ := fun v ↦ max 0 (1 - infDist v C / κ)
  have hg₀_cont : Continuous g₀ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt C).div_const κ))
  have hg₀_nonneg : ∀ v, 0 ≤ g₀ v := fun v ↦ le_max_left _ _
  have hg₀_le_one : ∀ v, g₀ v ≤ 1 := fun v ↦
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hκ0.le))
  have hg₀_one : ∀ v ∈ C, g₀ v = 1 := fun v hv ↦ by
    simp only [g₀, infDist_zero_of_mem hv, zero_div, sub_zero]
    exact max_eq_right zero_le_one
  have hg₀_zero : ∀ v, v ∉ cthickening κ C → g₀ v = 0 := by
    intro v hv
    have hge : κ ≤ infDist v C := by
      by_contra hlt
      obtain ⟨w, hwC, hvw⟩ := (infDist_lt_iff ⟨0, hC0⟩).1 (not_le.1 hlt)
      exact hv (mem_cthickening_of_dist_le v w κ C hwC hvw.le)
    refine max_eq_left ?_
    rw [sub_nonpos, le_div_iff₀ hκ0, one_mul]
    exact hge
  have hg₀_supp : HasCompactSupport g₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) 2) fun v hv ↦
      hg₀_zero v fun h ↦ hv (hthick κ hκ0.le hκ1 h)
  let g : C_c(Euclidean N, ℝ) := ⟨⟨g₀, hg₀_cont⟩, hg₀_supp⟩
  -- Step 6: `θ ∫_T g dH^n ≤ θ ν(cthickening κ C) < e`, so eventually the blow-ups are `< e`.
  have hint_le : ∫ v, g v ∂ν ≤ (ν (cthickening κ C)).toReal := by
    have hmeas : MeasurableSet (cthickening κ C) := isClosed_cthickening.measurableSet
    calc ∫ v, g v ∂ν ≤ ∫ v, (cthickening κ C).indicator (fun _ ↦ (1 : ℝ)) v ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun v ↦ hg₀_nonneg v)
            ((integrable_indicator_iff hmeas).2 (integrableOn_const hκfin))
            (ae_of_all _ fun v ↦ ?_)
          by_cases hv : v ∈ cthickening κ C
          · rw [indicator_of_mem hv]
            exact hg₀_le_one v
          · rw [indicator_of_notMem hv]
            exact (hg₀_zero v hv).le
      _ = (ν (cthickening κ C)).toReal := by
          rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one, measureReal_def]
  have hℓ : θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) < e :=
    calc θ * ∫ v, g v ∂ν ≤ θ * (ν (cthickening κ C)).toReal :=
          mul_le_mul_of_nonneg_left hint_le hθ.le
      _ < θ * (e / θ) := mul_lt_mul_of_pos_left hκreal hθ
      _ = e := by field_simp
  have hev := (hblow g).eventually (gt_mem_nhds hℓ)
  -- Step 7: `B_{R/2}(x)` is a compact subset of `U`, so it has finite `μ_V`-measure.
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hxU
  have hμR : V.weight (closedBall x (R / 2)) ≠ ∞ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x _)
      ((closedBall_subset_ball (half_lt_self hR)).trans hRU)
  -- Step 8: for `0 < t ≤ R/4` with blow-up `< e`, compare the cone section `S` with the
  -- rescaled cut-off `k y = g(t⁻¹ • (y - x))`.
  filter_upwards [hev, Ioc_mem_nhdsGT (by positivity : (0 : ℝ) < R / 4)] with t hFt ht
  obtain ⟨ht0, htR⟩ := ht
  set S : Set (Euclidean N) :=
    {y | y ∈ closedBall x t ∧ β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖}
  set k : Euclidean N → ℝ := fun y ↦ g₀ (t⁻¹ • (y - x))
  have hk_cont : Continuous k := hg₀_cont.comp (by fun_prop)
  -- (a) `k` vanishes off `B_{R/2}(x)`.
  have hk_supp : Function.support k ⊆ closedBall x (R / 2) := by
    intro y hy
    have hmem : t⁻¹ • (y - x) ∈ cthickening κ C := by
      by_contra hn'
      exact hy (hg₀_zero _ hn')
    have hnorm : ‖t⁻¹ • (y - x)‖ ≤ 2 := by
      simpa using hthick κ hκ0.le hκ1 hmem
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_le_iff₀ ht0] at hnorm
    rw [mem_closedBall, dist_eq_norm]
    linarith
  -- (b) `k` is `μ_V`-integrable.
  have hk_int : Integrable k V.weight := by
    refine (integrableOn_iff_integrable_of_support_subset hk_supp).1 ?_
    refine Measure.integrableOn_of_bounded (M := 1) hμR hk_cont.aestronglyMeasurable
      (ae_of_all _ fun y ↦ ?_)
    rw [Real.norm_of_nonneg (hg₀_nonneg _)]
    exact hg₀_le_one _
  -- (c) `1_S ≤ k`, so `μ_V(S) ≤ ∫ k dμ_V`.
  have hS_meas : MeasurableSet S :=
    (isClosed_closedBall.inter (isClosed_le (continuous_const.mul (continuous_id.sub
      continuous_const).norm) ((continuous_id.sub continuous_const).sub
        (hp_cont.comp (continuous_id.sub continuous_const))).norm)).measurableSet
  have hmass : V.weight S ≤ ENNReal.ofReal (∫ y, k y ∂V.weight) := by
    rw [← lintegral_indicator_one hS_meas,
      ofReal_integral_eq_lintegral_ofReal hk_int (ae_of_all _ fun y ↦ hg₀_nonneg _)]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ S
    · have hky : k y = 1 := hg₀_one _ (hC_scale t ht0 y hy.1 hy.2)
      rw [indicator_of_mem hy, Pi.one_apply, hky, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hy]
      exact zero_le
  -- Step 9: `μ_V(S) ≤ ∫ k dμ_V = t^n · (t⁻¹^n ∫ k dμ_V) ≤ t^n e`.
  have hFt' : t⁻¹ ^ n * ∫ y, k y ∂V.weight < e := hFt
  have hI : ∫ y, k y ∂V.weight ≤ t ^ n * e := by
    have htn : ∫ y, k y ∂V.weight = t ^ n * (t⁻¹ ^ n * ∫ y, k y ∂V.weight) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht0.ne', one_pow, one_mul]
    rw [htn]
    exact mul_le_mul_of_nonneg_left hFt'.le (pow_nonneg ht0.le n)
  refine hmass.trans ((ENNReal.ofReal_le_ofReal hI).trans_eq ?_)
  rw [ENNReal.ofReal_mul (pow_nonneg ht0.le n), ENNReal.ofReal_pow ht0.le, mul_comm]

/-- **Dimension `0`: tangent points are atoms of `μ_V`** (child `dim_zero_countable` of
`tangent_graph_cover`, step 2 of its proof).  If the `0`-varifold `V` has a tangent plane with
multiplicity `θ` at `x`, then for `0 < c < θ ω_0` the lower mass bound gives `c ≤ μ_V(B_t(x))` for
all small `t > 0`; `μ_V` is finite on a small closed ball about `x ∈ U`, and `B_t(x) ↓ {x}` as
`t ↓ 0`, so `μ_V({x}) ≥ c > 0`.  The σ-finite measure `μ_V` has only countably many atoms. -/
theorem Submission.tgc_dim_zero_tangent_points_countable :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (V : Varifold N 0 U),
      {x : Euclidean N | ∃ (T : Grassmannian N 0) (θ : ℝ), HasTangentPlane V x T θ}.Countable := by
  intro N U V
  -- Step 1: the atoms `{y | 0 < μ_V({y})}` of the σ-finite measure `μ_V` form a countable set.
  refine (Measure.countable_meas_pos_of_disjoint_iUnion (μ := V.weight)
    (As := fun y : Euclidean N ↦ ({y} : Set (Euclidean N))) (fun y ↦ measurableSet_singleton y)
    fun y z hyz ↦ Set.disjoint_singleton.2 hyz).mono ?_
  rintro x ⟨T, θ, hx⟩
  show 0 < V.weight {x}
  -- Step 2: for `0 < c < θ ω_0`, the lower mass bound with `n = 0` gives `c ≤ μ_V(B_t(x))` for all
  -- small `t > 0`.
  have hω : unitBallVolume 0 ≠ 0 :=
    (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 0))) 0 one_pos).ne'
  obtain ⟨c, hc0, hc⟩ := exists_between (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hx.2.1).ne' hω)
  have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ), c ≤ V.weight (closedBall x t) := by
    filter_upwards [Submission.tgc_tangent_weight_lower_bound N 0 U V x T θ hx c hc] with t ht
    rwa [pow_zero, mul_one] at ht
  -- Step 3: `x ∈ U` with `U` open, so a small closed ball about `x` is a compact subset of `U` and
  -- has finite mass.
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hx.1
  have hfin : ∃ r > 0, V.weight (cthickening r {x}) ≠ ∞ := by
    refine ⟨R / 2, half_pos hR, ?_⟩
    rw [cthickening_singleton x (half_pos hR).le]
    exact V.weight_finite_on_compact _ (isCompact_closedBall x _)
      ((closedBall_subset_ball (half_lt_self hR)).trans hRU)
  -- Step 4: continuity from above, `μ_V(B_t(x)) → μ_V({x})` as `t ↓ 0`, so `c ≤ μ_V({x})`.
  have hlim : Tendsto (fun t : ℝ ↦ V.weight (closedBall x t)) (𝓝[>] 0) (𝓝 (V.weight {x})) := by
    refine ((tendsto_measure_cthickening_of_isClosed hfin isClosed_singleton).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [cthickening_singleton x (mem_Ioi.1 ht).le]
  exact hc0.trans_le (ge_of_tendsto hlim hlow)

/-- Closed graph pieces from a local graph property (the localization `E_j ∩ B_{δ/4}(x_0)` after
printed (10) in Simon Ch. 3, Thm 1.6, p. 74, with closures taken): if the `L`-graph inequality over
`P` holds for all points of `E` at distance `≤ r`, then `E` is covered by countably many closed sets
on each of which it holds for all pairs of points. -/
theorem Submission.tgc_local_graph_closed_cover :
    ∀ (N n : ℕ) (L r : ℝ) (P : Grassmannian N n) (E : Set (Euclidean N)), 0 < r → (∀ y ∈ E, ∀ z ∈ E, ‖y - z‖ ≤ r → ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ x ∈ E, ∃ i, x ∈ Γ i := by
  intro N n L r P E hr hE
  -- Step 1: a dense sequence `d` in the separable, nonempty space `ℝ^N`.
  obtain ⟨d, hd⟩ : ∃ d : ℕ → Euclidean N, DenseRange d :=
    ⟨_, TopologicalSpace.denseRange_denseSeq (Euclidean N)⟩
  -- Step 3: the graph relation `F` is closed, as `Grassmannian.project P` is a linear map on a
  -- finite-dimensional space, hence continuous.
  have hp : Continuous (Grassmannian.project P) :=
    P.projectionLinearMap.continuous_of_finiteDimensional
  have hsub : Continuous fun q : Euclidean N × Euclidean N ↦ q.1 - q.2 :=
    continuous_fst.sub continuous_snd
  have hF : IsClosed {q : Euclidean N × Euclidean N |
      ‖(q.1 - q.2) - Grassmannian.project P (q.1 - q.2)‖ ≤
        L * ‖Grassmannian.project P (q.1 - q.2)‖} :=
    isClosed_le (hsub.sub (hp.comp hsub)).norm (continuous_const.mul (hp.comp hsub).norm)
  -- Step 2: the closed pieces `Γ_j = closure (E ∩ B_{r/2}(d_j))`.
  refine ⟨fun j ↦ closure (E ∩ closedBall (d j) (r / 2)), fun j ↦ isClosed_closure, ?_, ?_⟩
  · intro j y hy z hz
    -- Step 4: two points of `S_j = E ∩ B_{r/2}(d_j)` are at distance `≤ r`, so `S_j × S_j ⊆ F`.
    have hSF : (E ∩ closedBall (d j) (r / 2)) ×ˢ (E ∩ closedBall (d j) (r / 2)) ⊆
        {q : Euclidean N × Euclidean N |
          ‖(q.1 - q.2) - Grassmannian.project P (q.1 - q.2)‖ ≤
            L * ‖Grassmannian.project P (q.1 - q.2)‖} := by
      rintro ⟨a, b⟩ ⟨⟨haE, ha⟩, hbE, hb⟩
      rw [mem_closedBall, dist_eq_norm] at ha hb
      refine hE a haE b hbE ?_
      calc ‖a - b‖ = ‖(a - d j) - (b - d j)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖a - d j‖ + ‖b - d j‖ := norm_sub_le _ _
        _ ≤ r / 2 + r / 2 := add_le_add ha hb
        _ = r := by ring
    -- Step 5: `(y, z) ∈ closure S_j ×ˢ closure S_j = closure (S_j ×ˢ S_j) ⊆ F`.
    have hyz : (y, z) ∈
        closure ((E ∩ closedBall (d j) (r / 2)) ×ˢ (E ∩ closedBall (d j) (r / 2))) := by
      rw [closure_prod_eq]
      exact ⟨hy, hz⟩
    have hmem := closure_minimal hSF hF hyz
    exact hmem
  · -- Step 6: density gives `j` with `dist x (d j) < r / 2`, so `x ∈ S_j ⊆ Γ_j`.
    intro x hx
    obtain ⟨j, hj⟩ := hd.exists_dist_lt x (half_pos hr)
    exact ⟨j, subset_closure ⟨hx, mem_closedBall.2 hj.le⟩⟩

/-- Uniformization of eventual density bounds (Simon Ch. 3, 1.6, replacing Egoroff's theorem in
(7)–(9)): if `c t^n ≤ F(t)` eventually for some `c > 0` and `G(t) ≤ ε t^n` eventually for every
`ε > 0`, then for some `m, k` both `t^n/(m+1) ≤ F(t)` and `G(t) ≤ β t^n/(m+1)` hold for all
`t ∈ (0, 1/(k+1)]`. -/
theorem Submission.tgc_eventual_density_bounds_uniform :
    ∀ (n : ℕ) (β : ℝ) (F G : ℝ → ℝ≥0∞), 0 < β → (∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ F t) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), G t ≤ ε * ENNReal.ofReal t ^ n) → ∃ m k : ℕ, ∀ t : ℝ, 0 < t → t ≤ 1 / ((k : ℝ) + 1) → ENNReal.ofReal (1 / ((m : ℝ) + 1) * t ^ n) ≤ F t ∧ G t ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1) * β * t ^ n) := by
  rintro n β F G hβ ⟨c, hc, hF⟩ hG
  -- Step 1: `m` with `m⁻¹ < c`, so `ofReal (1/(m+1)) = (m+1)⁻¹ ≤ m⁻¹ < c`.
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hc.ne'
  have ha : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hac : ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≤ c := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_add (Nat.cast_nonneg m) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    exact (ENNReal.inv_le_inv.mpr le_self_add).trans hm.le
  -- Steps 2–3: with `ε = ofReal (β/(m+1)) > 0`, both bounds hold on a common interval `(0, δ)`.
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hF.and (hG (ENNReal.ofReal (1 / ((m : ℝ) + 1) * β)) (ENNReal.ofReal_pos.mpr (mul_pos ha hβ))))
  -- Step 4: `k` with `1/(k+1) < δ`.
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ from hδ)
  -- Step 5: evaluate both bounds at `t ∈ (0, 1/(k+1)] ⊆ (0, δ)`.
  refine ⟨m, k, fun t ht htk ↦ ?_⟩
  obtain ⟨hFt, hGt⟩ := hsub ⟨ht, htk.trans_lt hk⟩
  constructor
  · rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_pow ht.le]
    exact (mul_le_mul_left hac _).trans hFt
  · rwa [ENNReal.ofReal_mul (mul_pos ha hβ).le, ENNReal.ofReal_pow ht.le]

/-- Linear algebra of tilted cones (step 3, (3.1)–(3.2), of the tangent-graph cover, with `c = L/4`
and `γ = L/8`): if `‖p_T u - p_P u‖ ≤ (L/4)‖u‖` for all `u` and `v` violates the `L`-graph inequality
over `P`, i.e. `L‖p_P v‖ < ‖v - p_P v‖`, then every `w` with `‖w - v‖ ≤ (L/8)‖v‖` lies in the cone
`(L/16)‖w‖ ≤ ‖w - p_T w‖` around `T^⊥`, and `‖w‖ ≤ 2‖v‖`. -/
theorem Submission.tgc_tilted_cone_inclusion :
    ∀ (N n : ℕ) (L : ℝ) (P T : Grassmannian N n) (v w : Euclidean N), 0 < L → L ≤ 1 → (∀ u : Euclidean N, ‖Grassmannian.project T u - Grassmannian.project P u‖ ≤ L / 4 * ‖u‖) → L * ‖Grassmannian.project P v‖ < ‖v - Grassmannian.project P v‖ → ‖w - v‖ ≤ L / 8 * ‖v‖ → L / 16 * ‖w‖ ≤ ‖w - Grassmannian.project T w‖ ∧ ‖w‖ ≤ 2 * ‖v‖ := by
  intro N n L P T v w hL0 hL1 htilt hv hw
  -- Step 0: `p_S` is symmetric and idempotent, so `p_S u ⊥ u - p_S u` and Pythagoras gives
  -- `‖u‖² = ‖p_S u‖² + ‖u - p_S u‖²`; in particular `‖u - p_S u‖ ≤ ‖u‖`.
  have pythagoras : ∀ (S : Grassmannian N n) (u : Euclidean N),
      ‖u‖ ^ 2 = ‖Grassmannian.project S u‖ ^ 2 + ‖u - Grassmannian.project S u‖ ^ 2 := by
    intro S u
    have hsymm : inner ℝ (Grassmannian.project S u) (Grassmannian.project S u) =
        inner ℝ u (Grassmannian.project S (Grassmannian.project S u)) :=
      S.projectionLinearMap_isSymmetric u (Grassmannian.project S u)
    rw [Grassmannian.project_project] at hsymm
    have horth : inner ℝ (Grassmannian.project S u) (u - Grassmannian.project S u) = 0 := by
      rw [inner_sub_right, hsymm, real_inner_comm, sub_self]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [add_sub_cancel] at h
    linarith
  have contraction : ∀ (S : Grassmannian N n) (u : Euclidean N),
      ‖u - Grassmannian.project S u‖ ≤ ‖u‖ := by
    intro S u
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    linarith [pythagoras S u, sq_nonneg ‖Grassmannian.project S u‖]
  -- Step 1: `L‖p_P v‖ < ‖v - p_P v‖` and `L ≤ 1` give `(L/2)‖v‖ < ‖v - p_P v‖`.
  have step1 : L / 2 * ‖v‖ < ‖v - Grassmannian.project P v‖ := by
    have hpyth := pythagoras P v
    have h1 : (L * ‖Grassmannian.project P v‖) ^ 2 < ‖v - Grassmannian.project P v‖ ^ 2 :=
      pow_lt_pow_left₀ hv (mul_nonneg hL0.le (norm_nonneg _)) two_ne_zero
    have h2 : L ^ 2 * ‖v - Grassmannian.project P v‖ ^ 2 ≤ ‖v - Grassmannian.project P v‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hL0.le hL1)
    have h3 : L ^ 2 * ‖v‖ ^ 2 =
        L ^ 2 * ‖Grassmannian.project P v‖ ^ 2 + L ^ 2 * ‖v - Grassmannian.project P v‖ ^ 2 := by
      rw [hpyth]
      ring
    have h4 : (L * ‖v‖) ^ 2 < (2 * ‖v - Grassmannian.project P v‖) ^ 2 := by
      nlinarith [sq_nonneg ‖v - Grassmannian.project P v‖]
    have h5 := (sq_lt_sq₀ (mul_nonneg hL0.le (norm_nonneg v)) (by positivity)).1 h4
    linarith
  -- Step 2: `p_P v - p_T v = (v - p_T v) - (v - p_P v)` and the tilt bound give
  -- `(L/4)‖v‖ < ‖v - p_T v‖`.
  have step2 : L / 4 * ‖v‖ < ‖v - Grassmannian.project T v‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub v (Grassmannian.project T v)
      (Grassmannian.project P v)
    linarith [htilt v]
  -- Step 3: `‖w‖ ≤ ‖v‖ + ‖w - v‖ ≤ (1 + L/8)‖v‖ ≤ 2‖v‖`.
  have step3 : ‖w‖ ≤ 2 * ‖v‖ := by
    have h1 := norm_le_norm_add_norm_sub' w v
    have h2 : L / 8 * ‖v‖ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg v) (by linarith)
    linarith
  -- Step 4: by linearity `v - p_T v = (w - p_T w) - ((w - v) - p_T (w - v))`, and
  -- `‖(w - v) - p_T (w - v)‖ ≤ ‖w - v‖`, so `‖w - p_T w‖ > (L/4 - L/8)‖v‖ ≥ (L/16)‖w‖`.
  refine ⟨?_, step3⟩
  have hlin : v - Grassmannian.project T v =
      (w - Grassmannian.project T w) - ((w - v) - Grassmannian.project T (w - v)) := by
    have hmap : Grassmannian.project T (w - v) =
        Grassmannian.project T w - Grassmannian.project T v :=
      map_sub T.projectionLinearMap w v
    rw [hmap]
    abel
  have h1 : ‖v - Grassmannian.project T v‖ ≤
      ‖w - Grassmannian.project T w‖ + ‖(w - v) - Grassmannian.project T (w - v)‖ := by
    rw [hlin]
    exact norm_sub_le _ _
  have h2 := contraction T (w - v)
  have h3 : L / 16 * ‖w‖ ≤ L / 16 * (2 * ‖v‖) := mul_le_mul_of_nonneg_left step3 (by positivity)
  linarith

/-- Cone/density covering lemma (steps 4–6 of the tangent-graph cover; Simon Ch. 3, Thm 1.6,
printed (7)–(10), for an arbitrary measure `μ`): if every `x ∈ A` has a plane `T` tilted from `P`
by at most `L/4`, an eventual lower mass bound `c t^n ≤ μ(B_t(x))` with `c > 0`, and eventual cone
mass `μ{y ∈ B_t(x) : (L/16)‖y - x‖ ≤ ‖(y - x) - p_T(y - x)‖} ≤ ε t^n` for every `ε > 0`, then `A`
is covered by countably many closed `L`-Lipschitz graphs over `P`. -/
theorem Submission.tgc_cone_density_graph_cover :
    ∀ (N n : ℕ) (L : ℝ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (A : Set (Euclidean N)), 0 < L → L ≤ 1 → (∀ x ∈ A, ∃ T : Grassmannian N n, (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) ∧ (∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ {y | y ∈ closedBall x t ∧ L / 16 * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤ ε * ENNReal.ofReal t ^ n) → ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ x ∈ A, ∃ i, x ∈ Γ i := by
  intro N n L μ P A hL0 hL1 hA
  -- Step 1: with `γ = L/8` and `β = (L/16)^n/2`, class `m` uses the lower constant
  -- `a_m = 1/(m+1)` and the cone constant `a_m β`, so that `a_m β (2s)^n = a_m (γs)^n / 2`.
  have hβ : 0 < (L / 16) ^ n / 2 := by positivity
  -- Step 2: the uniform classes `E m k`: some tilted `T` gives the lower bound `a_m t^n` and the
  -- cone bound `a_m β t^n` for every `t ∈ (0, 1/(k+1)]`.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → Set (Euclidean N), ∀ m k x, x ∈ E m k ↔
      ∃ T : Grassmannian N n,
        (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 / ((k : ℝ) + 1) →
          ENNReal.ofReal (1 / ((m : ℝ) + 1) * t ^ n) ≤ μ (closedBall x t) ∧
          μ {y | y ∈ closedBall x t ∧
              L / 16 * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤
            ENNReal.ofReal (1 / ((m : ℝ) + 1) * ((L / 16) ^ n / 2) * t ^ n) :=
    ⟨fun m k ↦ {x | _}, fun _ _ _ ↦ Iff.rfl⟩
  -- Step 3: the classes cover `A`, by uniformizing the eventual bounds (i) and (ii).
  have hcover : ∀ x ∈ A, ∃ m k : ℕ, x ∈ E m k := by
    intro x hx
    obtain ⟨T, htilt, hlow, hcone⟩ := hA x hx
    obtain ⟨m, k, hmk⟩ := Submission.tgc_eventual_density_bounds_uniform n ((L / 16) ^ n / 2)
      (fun t ↦ μ (closedBall x t))
      (fun t ↦ μ {y | y ∈ closedBall x t ∧
        L / 16 * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖}) hβ hlow hcone
    exact ⟨m, k, (hE m k x).2 ⟨T, htilt, hmk⟩⟩
  -- Step 4 (printed (10)): two points of one class at distance `≤ 1/(2(k+1))` satisfy the
  -- `L`-graph inequality over `P`.
  have hgraph : ∀ m k : ℕ, ∀ y ∈ E m k, ∀ z ∈ E m k, ‖y - z‖ ≤ 1 / ((k : ℝ) + 1) / 2 →
      ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖ := by
    intro m k y hy z hz hyz
    by_contra hcon
    have hcon := not_le.1 hcon
    obtain ⟨_, -, hy⟩ := (hE m k y).1 hy
    obtain ⟨T, htilt, hz⟩ := (hE m k z).1 hz
    -- `s = ‖y - z‖ > 0`: at `y - z = 0` both sides of the graph inequality vanish.
    have hs : 0 < ‖y - z‖ := by
      refine norm_pos_iff.2 fun h ↦ ?_
      have h0 : Grassmannian.project P 0 = 0 := map_zero P.projectionLinearMap
      rw [h, h0, sub_zero, norm_zero, mul_zero] at hcon
      exact lt_irrefl 0 hcon
    -- (a) `B_{γs}(y)` lies in the cone region at `z` of radius `2s`.
    have hsub : closedBall y (L / 8 * ‖y - z‖) ⊆ {w | w ∈ closedBall z (2 * ‖y - z‖) ∧
        L / 16 * ‖w - z‖ ≤ ‖(w - z) - Grassmannian.project T (w - z)‖} := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      have hwv : ‖(w - z) - (y - z)‖ ≤ L / 8 * ‖y - z‖ := by
        rwa [sub_sub_sub_cancel_right]
      obtain ⟨hwcone, hwnorm⟩ :=
        Submission.tgc_tilted_cone_inclusion N n L P T (y - z) (w - z) hL0 hL1 htilt hcon hwv
      exact ⟨by rwa [mem_closedBall, dist_eq_norm], hwcone⟩
    -- (b) the lower bound at `y` (radius `γs`), monotonicity of `μ` and the cone bound at `z`
    -- (radius `2s`) give `a_m (γs)^n ≤ a_m β (2s)^n`.
    have h2s : 2 * ‖y - z‖ ≤ 1 / ((k : ℝ) + 1) := by linarith
    have hγs : L / 8 * ‖y - z‖ ≤ 1 / ((k : ℝ) + 1) :=
      (mul_le_mul_of_nonneg_right (by linarith) hs.le).trans h2s
    have hchain := ((hy (L / 8 * ‖y - z‖) (by positivity) hγs).1.trans
      (measure_mono (μ := μ) hsub)).trans (hz (2 * ‖y - z‖) (by positivity) h2s).2
    have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
    -- (c) but `a_m β (2s)^n = a_m (γs)^n / 2` and `a_m (γs)^n > 0`.
    have h16 : (L / 16) ^ n * (2 * ‖y - z‖) ^ n = (L / 8 * ‖y - z‖) ^ n := by
      rw [← mul_pow]
      ring
    have heq : 1 / ((m : ℝ) + 1) * ((L / 16) ^ n / 2) * (2 * ‖y - z‖) ^ n =
        1 / ((m : ℝ) + 1) * (L / 8 * ‖y - z‖) ^ n / 2 := by
      rw [← h16]
      ring
    have hpos : 0 < 1 / ((m : ℝ) + 1) * (L / 8 * ‖y - z‖) ^ n := by positivity
    linarith
  -- Step 5: each class lies on countably many closed `L`-graphs over `P`.
  choose Γ hΓclosed hΓgraph hΓcover using fun m k : ℕ ↦
    Submission.tgc_local_graph_closed_cover N n L (1 / ((k : ℝ) + 1) / 2) P (E m k)
      (by positivity) (hgraph m k)
  -- Step 6: enumerate the triples `(m, k, j)` with `Nat.unpair`.
  refine ⟨fun i ↦ Γ i.unpair.1 i.unpair.2.unpair.1 i.unpair.2.unpair.2, fun i ↦ hΓclosed _ _ _,
    fun i ↦ hΓgraph _ _ _, fun x hx ↦ ?_⟩
  obtain ⟨m, k, hmk⟩ := hcover x hx
  obtain ⟨j, hj⟩ := hΓcover m k x hmk
  refine ⟨Nat.pair m (Nat.pair k j), ?_⟩
  simpa only [Nat.unpair_pair] using hj

/-- **Tangent points with nearly horizontal planes lie on countably many closed `L`-Lipschitz
graphs** (node `tangent_graph_cover`; the cone argument of Simon's proof of Ch. 3, 1.6 "⇐", which
the proof of Ch. 8, 1.2 invokes through Ch. 3, 1.9).  For `0 < L ≤ 1` and `P ∈ G(N,n)` there are
closed sets `Γ_i` with `|q(y - z)| ≤ L |p(y - z)|` on each `Γ_i` (`p = p_P`, `q = I - p`) containing
every point `x` at which `V` has a tangent plane `T` (Def. 1.1) with `‖p_T - p‖ ≤ L/4`.
For `n = 0` such points are atoms of `μ_V`, hence countably many, and singletons are `L`-graphs.
For `n ≥ 1` each such point satisfies the lower mass bound `c t^n ≤ μ_V(B_t(x))` for small `t`
(any `0 < c < θ ω_n`) and the cone decay `μ_V({y ∈ B_t(x) : (L/16)|y - x| ≤ |q_T(y - x)|}) ≤ ε t^n`
for small `t`, which is all the uniform-class/graph construction needs. -/
theorem Submission.tangent_points_lipschitz_graph_cover :
    ∀ (N n : ℕ) (L : ℝ), 0 < L → L ≤ 1 → ∀ (U : Set (Euclidean N)) (V : Varifold N n U)
      (P : Grassmannian N n), ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧
        (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i,
          ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧
        ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ →
          (∀ v : Euclidean N,
            ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) →
          ∃ i, x ∈ Γ i := by
  intro N n L hL0 hL1 U V P
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: the tangent points form a countable set, so they are values `f i` of a sequence;
    -- each singleton `{f i}` is closed, and an `L`-graph since `y - z = 0` on it.
    obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1
      (Submission.tgc_dim_zero_tangent_points_countable N U V)
    refine ⟨fun i ↦ {f i}, fun i ↦ isClosed_singleton, ?_, fun x T θ hx _ ↦ ?_⟩
    · intro i y hy z hz
      rw [Set.mem_singleton_iff.1 hy, Set.mem_singleton_iff.1 hz, sub_self]
      simp [Grassmannian.project]
    · obtain ⟨i, hi⟩ := hf ⟨T, θ, hx⟩
      exact ⟨i, hi.symm⟩
  · -- `n ≥ 1`: the cone/density graph cover, applied to `μ_V` and the set `A` of tangent points
    -- whose plane is `L/4`-close to `P`, covers `A` by closed `L`-graphs over `P`.
    refine (Submission.tgc_cone_density_graph_cover N n L V.weight P
      {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ ∧
        ∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖}
      hL0 hL1 ?_).imp fun Γ ⟨hΓ, hgraph, hcover⟩ ↦
        ⟨hΓ, hgraph, fun x T θ hx hTP ↦ hcover x ⟨T, θ, hx, hTP⟩⟩
    -- Each `x ∈ A`, with plane `T` and multiplicity `θ > 0`, has the lower mass bound for any
    -- `0 < c < θ ω_n` (`ω_n > 0`) and the cone decay with aperture `β = L/16`.
    rintro x ⟨T, θ, hx, hTP⟩
    have hω : unitBallVolume n ≠ 0 :=
      (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
    obtain ⟨c, hc0, hc⟩ := exists_between (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hx.2.1).ne' hω)
    exact ⟨T, hTP, ⟨c, hc0, Submission.tgc_tangent_weight_lower_bound N n U V x T θ hx c hc⟩,
      fun ε hε ↦ Submission.tgc_tangent_cone_weight_decay N n U V x T θ hn hx (L / 16)
        (by positivity) ε hε⟩

/-- **Simon Ch. 8, 1.2 (First Rectifiability Theorem), p. 206** (child `first_rectifiability` of
`root`; Step 9 of its proof, assembling Steps 0–8).  Let `M = {x ∈ spt μ_V : T_x, θ(x) exist}` and
let `θ(x)` be the multiplicity of a tangent plane at `x` (and `0` off `M`).  Points of `M` have
density `θ(x)`, and `μ_V(ℝ^N ∖ M) = 0`.  For every `L ∈ (0,1]`, countably many closed `L`-flat
graphs cover `M` (sibling `tangent_points_lipschitz_graph_cover`), so `M` is `H^n`-null-measurable
and countably `n`-rectifiable, and `μ_V = θ H^n ⌞ M`.  Lemma 1.3 (sibling `plane_disintegration`)
gives `V(A) = μ_V({x : (x, T_x) ∈ A})`.  On `M` the tangent plane `T_x` is the unique approximate
tangent plane of `(M, θ)` at `x`, which turns this identity into `V = v(M, θ)`. -/
theorem Submission.first_rectifiability_theorem : FirstRectifiabilityTheorem := by
  intro N n U V hae
  classical
  set M : Set (Euclidean N) := {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
    HasTangentPlane V x T θ'}
  -- Step (0d): `θ(x)` is the multiplicity of a chosen tangent plane at `x`, and `0` elsewhere.
  let θ : Euclidean N → ℝ := fun x ↦
    if h : ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ' then
      h.choose_spec.choose else 0
  have hθ : ∀ x (h : ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'),
      HasTangentPlane V x h.choose (θ x) := fun x h ↦ by
    rw [show θ x = h.choose_spec.choose from dite_eq_left h]
    exact h.choose_spec.choose_spec
  have hMU : M ⊆ U := fun x hx ↦ (hθ x hx.2).1
  have hθpos : ∀ x ∈ M, 0 < θ x := fun x hx ↦ (hθ x hx.2).2.1
  -- Step (0c): the density of `μ_V` at a point `x` of `M` is `θ(x)`.
  have hdens : ∀ x ∈ M, 0 < θ x ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x)) := fun x hx ↦
    ⟨hθpos x hx, Submission.frt_tangent_plane_hasDensity N n U V x _ _ (hθ x hx.2)⟩
  -- Step (0e): `μ_V` is carried by `spt μ_V` and, by hypothesis, by the tangent points.
  have hMc : V.weight Mᶜ = 0 := by
    have h0 := measure_union_null (Measure.measure_compl_support (μ := V.weight)) (ae_iff.1 hae)
    refine measure_mono_null (fun x hx ↦ ?_) h0
    by_contra h
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at h
    exact hx h
  -- Step 2: for `L ∈ (0,1]`, countably many closed `L`-flat graphs cover the tangent points.
  have hcov := Submission.frt_tangent_points_flat_graph_cover N n U V
    fun L hL hL1 P ↦ Submission.tangent_points_lipschitz_graph_cover N n L hL hL1 U V P
  -- Step 4: `M` is `H^n`-null-measurable.
  have hMmeas : NullMeasurableSet M μHE[n] :=
    Submission.frt_carrier_nullMeasurable N n U V M θ hMU hMc hdens
  -- Step 2 with `L = 1`: `M` is countably `n`-rectifiable.
  have hrect : Chapter03.CountablyRectifiable n M := by
    obtain ⟨C, hC, hCg, hCM⟩ := hcov 1 one_pos le_rfl
    exact Submission.frt_countablyRectifiable_of_graph_cover N n M C hC
      (fun c hc y hy z hz ↦ ((hCg c hc).2 y hy z hz).trans_eq (one_mul _)) fun x hx ↦ hCM hx.2
  -- Steps 3, 5 and 6: `μ_V = θ H^n ⌞ M`, and `θ` is locally `H^n`-integrable on `M`.
  obtain ⟨hint, hweight⟩ := Submission.frt_weight_eq_multiplicity_hausdorff N n U V M θ hMU hMc
    hdens fun L hL hL1 ↦ (hcov L hL hL1).imp fun C hC ↦ ⟨hC.1, hC.2.1, fun x hx ↦ hC.2.2 hx.2⟩
  refine ⟨θ, fun x hx ↦ ⟨_, hθ x hx.2⟩, hMU, hMmeas, hrect, hθpos, hint, fun A hA ↦ ?_⟩
  -- Step 8: Lemma 1.3 gives `V(A) = μ_V({x : (x, T_x) ∈ A})`.
  obtain ⟨hSA, hVA⟩ := Submission.frt_varifold_eq_tangent_graph_measure N n U V
    (Submission.plane_disintegration N n U V) hae A hA
  -- Step 7: at `x ∈ M`, `T_x` is the unique approximate tangent plane of `(M, θ)`.
  have happrox : ∀ x (hx : x ∈ M) (S : Grassmannian N n),
      Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ↔ S = hx.2.choose :=
    fun x hx ↦ Submission.frt_weighted_approx_tangent N n U V M θ x _ hMmeas hθpos hint
      (fun B hB ↦ hweight B hB.nullMeasurableSet) (hθ x hx.2)
  -- Step 9: by uniqueness of `T_x` (step (0d)), both sides integrate over the same set.
  have hset : {x | ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ' ∧ (x, T) ∈ A} ∩ M =
      {x | x ∈ M ∧ ∃ S : Grassmannian N n,
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ∧ (x, S) ∈ A} := by
    ext x
    constructor
    · rintro ⟨⟨T, θ', hT, hxT⟩, hx⟩
      refine ⟨hx, T, (happrox x hx T).2 ?_, hxT⟩
      exact (Submission.frt_tangent_plane_unique N n U V x _ T (θ x) θ' (hθ x hx.2) hT).1
    · rintro ⟨hx, S, hS, hxS⟩
      refine ⟨⟨S, θ x, ?_, hxS⟩, hx⟩
      rw [(happrox x hx S).1 hS]
      exact hθ x hx.2
  rw [hVA, hweight _ hSA, hset]
theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

/-- Subsequence extraction in Simon Ch. 1, 4.16 (erratum: the Alaoglu theorem only yields a
subnet, so `X` is taken second countable).  If `X` is locally compact, Hausdorff and second
countable and the masses `μ j K` of each compact `K` are eventually bounded, then for one strictly
increasing `φ` every `∫ f dμ (φ j)` with `f ∈ C_c(X, ℝ)` converges.  A Tychonoff (diagonal)
extraction in `ℕ → ℝ` makes `∫ g k dμ (φ j)` converge for the countable family `g` of
`radon_compactlySupported_countable_approx`; uniform approximation of `f` by `g k` supported in a
fixed compact `K ⊇ tsupport f` and the mass bound on `K` then make `∫ f dμ (φ j)` Cauchy. -/
theorem Submission.radon_exists_subseq_tendsto_integral :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : ℕ → Measure X),
      (∀ K : Set X, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ j in atTop, μ j K ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : C_c(X, ℝ), ∃ L : ℝ,
        Tendsto (fun j ↦ ∫ x, f x ∂(μ (φ j))) atTop (𝓝 L) := by
  intro X _ _ _ _ _ _ μ hμ
  -- Step 0(a): `h ∈ C_c(X, ℝ)` is `ν`-integrable if `ν K < ∞` for some `K ⊇ tsupport h`.
  have hint : ∀ (ν : Measure X) (h : C_c(X, ℝ)) (K : Set X), tsupport h ⊆ K → ν K ≠ ∞ →
      Integrable (fun x ↦ h x) ν := by
    intro ν h K hK hν
    obtain ⟨M, hM⟩ := (map_continuous h).bounded_above_of_compact_support h.hasCompactSupport
    exact (integrableOn_iff_integrable_of_support_subset ((subset_tsupport _).trans hK)).1
      (Measure.integrableOn_of_bounded hν (map_continuous h).aestronglyMeasurable
        (Eventually.of_forall hM))
  -- Step 0(b): `|∫ h dν| ≤ η ν(K)` if `h = 0` off `K`, `|h| ≤ η` and `ν K < ∞`.
  have hest : ∀ (ν : Measure X) (h : X → ℝ) (K : Set X) (η : ℝ), ν K ≠ ∞ →
      (∀ x, x ∉ K → h x = 0) → (∀ x, |h x| ≤ η) → |∫ x, h x ∂ν| ≤ η * ν.real K := by
    intro ν h K η hν hK hη
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hK, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hν.lt_top fun x _ ↦
      (Real.norm_eq_abs _).le.trans (hη x)
  -- Step 1: the countable approximating family `g`.
  obtain ⟨g, hg⟩ := Submission.radon_compactlySupported_countable_approx X
  -- Step 2: each sequence `j ↦ ∫ g k dμ j` is bounded, by `|M| C` for `j ≥ J` and by the
  -- finitely many earlier terms otherwise.
  have hbdd : ∀ k, ∃ B : ℝ, ∀ j, |∫ x, g k x ∂(μ j)| ≤ B := by
    intro k
    obtain ⟨C, hC, hev⟩ := hμ _ (g k).hasCompactSupport.isCompact
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    obtain ⟨M, hM⟩ :=
      (map_continuous (g k)).bounded_above_of_compact_support (g k).hasCompactSupport
    refine ⟨|M| * C.toReal + ∑ i ∈ Finset.range J, |∫ x, g k x ∂(μ i)|, fun j ↦ ?_⟩
    have hsum : 0 ≤ ∑ i ∈ Finset.range J, |∫ x, g k x ∂(μ i)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hMC : 0 ≤ |M| * C.toReal := mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg
    rcases lt_or_ge j J with hj | hj
    · have h1 : |∫ x, g k x ∂(μ j)| ≤ ∑ i ∈ Finset.range J, |∫ x, g k x ∂(μ i)| :=
        Finset.single_le_sum (f := fun i ↦ |∫ x, g k x ∂(μ i)|) (fun _ _ ↦ abs_nonneg _)
          (Finset.mem_range.2 hj)
      linarith
    · have hjC : μ j (tsupport (g k)) ≤ C := hJ j hj
      have h1 : |∫ x, g k x ∂(μ j)| ≤ |M| * (μ j).real (tsupport (g k)) :=
        hest (μ j) (g k) _ |M| (hjC.trans_lt hC.lt_top).ne
          (fun x hx ↦ image_eq_zero_of_notMem_tsupport hx)
          (fun x ↦ (Real.norm_eq_abs _).ge.trans ((hM x).trans (le_abs_self M)))
      have h2 : |M| * (μ j).real (tsupport (g k)) ≤ |M| * C.toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hC hjC) (abs_nonneg M)
      linarith
  choose B hB using hbdd
  -- Step 3: the points `(∫ g k dμ j)_k` lie in the compact set `∏_k [-B k, B k]` of the first
  -- countable space `ℕ → ℝ`, so a subsequence converges, i.e. converges in every coordinate `k`.
  obtain ⟨l, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun k ↦ isCompact_Icc (a := -B k) (b := B k)).tendsto_subseq
      (x := fun j k ↦ ∫ x, g k x ∂(μ j)) fun j ↦ mem_univ_pi.2 fun k ↦ abs_le.1 (hB k j)
  have hconv : ∀ k, Tendsto (fun j ↦ ∫ x, g k x ∂(μ (φ j))) atTop (𝓝 (l k)) :=
    fun k ↦ tendsto_pi_nhds.1 hlim k
  refine ⟨φ, hφ, fun f ↦ ?_⟩
  -- Step 4: `∫ f dμ (φ j)` is Cauchy, hence convergent.
  obtain ⟨K, hK, hfK, happrox⟩ := hg f
  obtain ⟨C, hC, hev⟩ := hμ K hK
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  have hc : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε ↦ ?_)
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η * (2 * C.toReal + 2) = ε :=
    ⟨ε / (2 * C.toReal + 2), div_pos hε (by linarith), div_mul_cancel₀ ε (by linarith)⟩
  obtain ⟨k, hgK, hfg⟩ := happrox η hη
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 (hconv k).cauchySeq η hη
  -- (i): for `p ≥ J`, `φ p ≥ p ≥ J`, so `μ (φ p) K ≤ C` and `|∫ f - ∫ g k| ≤ η C`.
  have hclose : ∀ p, J ≤ p →
      |∫ x, f x ∂(μ (φ p)) - ∫ x, g k x ∂(μ (φ p))| ≤ η * C.toReal := by
    intro p hp
    have hpC : μ (φ p) K ≤ C := hJ _ (hp.trans (hφ.id_le p))
    have hfin : μ (φ p) K ≠ ∞ := (hpC.trans_lt hC.lt_top).ne
    rw [← integral_sub (hint _ f K hfK hfin) (hint _ (g k) K hgK hfin)]
    refine (hest _ (fun x ↦ f x - g k x) K η hfin (fun x hx ↦ ?_) hfg).trans
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hC hpC) hη.le)
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hfK h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hgK h)), sub_zero]
  -- (ii): the triangle inequality, with `η C + η + η C < η (2 C + 2) = ε`.
  refine ⟨max N₁ J, fun p hp q hq ↦ ?_⟩
  have h1 := abs_le.1 (hclose p (le_of_max_le_right hp))
  have h2 := abs_le.1 (hclose q (le_of_max_le_right hq))
  have h3 := abs_lt.1 (show |∫ x, g k x ∂(μ (φ p)) - ∫ x, g k x ∂(μ (φ q))| < η from
    Real.dist_eq _ _ ▸ hN₁ p (le_of_max_le_left hp) q (le_of_max_le_left hq))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Simon Ch. 1, 4.16 (Compactness Theorem for Radon measures), corrected**, on `Gₙ(U)`; used in
Ch. 8, 5.1 and 5.8.  If `μ_j(K × G(N,n))` is eventually bounded for each compact `K ⊆ U`, then a
subsequence `μ_{φ(j)}` converges to an `n`-varifold `V` on `U` against every test function supported
in `U × G(N,n)`.  The printed proof extracts with Alaoglu, which only yields a subnet; on the second
countable space `Gₙ(U)` the extraction is sequential, and the limit functional is represented by
the Riesz theorem (Ch. 1, 4.12). -/
theorem Submission.varifold_radon_compactness :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (μ : ℕ → Measure (Euclidean N × Grassmannian N n)),
      IsOpen U →
      (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
        ∀ᶠ j in atTop, μ j (K ×ˢ (univ : Set (Grassmannian N n))) ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Varifold N n U,
        ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
          tsupport f ⊆ U ×ˢ (univ : Set (Grassmannian N n)) →
          Tendsto (fun j ↦ ∫ z, f z ∂(μ (φ j))) atTop (𝓝 (∫ z, f z ∂V.measure)) := by
  intro N n U μ hU hμ
  -- Simon's `Gₙ(U)`: the open subset `U × G(N,n)`, as a subtype.
  set S : Set (Euclidean N × Grassmannian N n) := U ×ˢ (univ : Set (Grassmannian N n))
  have hSo : IsOpen S := hU.prod isOpen_univ
  have hS : MeasurableSet S := hSo.measurableSet
  have : LocallyCompactSpace S := hSo.locallyCompactSpace
  -- The `μ_j` restricted to `Gₙ(U)`; a compact subset of `Gₙ(U)` lies over a compact `K ⊆ U`.
  have hμS : ∀ K : Set S, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ j in atTop, (μ j).comap Subtype.val K ≤ C := by
    intro K hK
    obtain ⟨C, hC, hev⟩ := hμ ((fun z : S ↦ z.1.1) '' K)
      (hK.image (continuous_fst.comp continuous_subtype_val)) (by rintro _ ⟨z, _, rfl⟩; exact z.2.1)
    refine ⟨C, hC, hev.mono fun j hj ↦ ?_⟩
    rw [comap_subtype_coe_apply hS]
    refine (measure_mono ?_).trans hj
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, mem_univ _⟩
  -- Sequential extraction, then Riesz representation of the limit functional on `C_c(Gₙ(U))`.
  obtain ⟨φ, hφ, hlim⟩ :=
    Submission.radon_exists_subseq_tendsto_integral S (fun j ↦ (μ j).comap Subtype.val) hμS
  obtain ⟨ν, hν, hconv⟩ :=
    Submission.radon_exists_measure_of_tendsto_integral S (fun j ↦ (μ (φ j)).comap Subtype.val)
      (fun K hK ↦ (hμS K hK).imp fun _ h ↦ ⟨h.1, hφ.tendsto_atTop.eventually h.2⟩) hlim
  refine ⟨φ, hφ, Varifold.ofDomainMeasure hU ν, fun f hf ↦ ?_⟩
  -- `f` vanishes off `Gₙ(U)` and restricts to a compactly supported function on it.
  have hf0 : ∀ z, z ∉ S → f z = 0 := fun z hz ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hz (hf h)
  let f' : C_c(S, ℝ) :=
    ⟨⟨fun z ↦ f z, f.continuous.comp continuous_subtype_val⟩,
      IsCompact.of_isClosed_subset (Topology.IsInducing.subtypeVal.isCompact_preimage'
          f.hasCompactSupport (by rwa [Subtype.range_coe])) (isClosed_tsupport _)
        (closure_minimal (fun z hz ↦ subset_tsupport f hz)
          ((isClosed_tsupport f).preimage continuous_subtype_val))⟩
  have hμf : ∀ j, ∫ z, f' z ∂((μ (φ j)).comap Subtype.val) = ∫ z, f z ∂(μ (φ j)) := fun j ↦
    (integral_subtype_comap hS _).trans (setIntegral_eq_integral_of_forall_compl_eq_zero hf0)
  have hVf : ∫ z, f z ∂(Varifold.ofDomainMeasure hU ν).measure = ∫ z, f' z ∂ν :=
    (MeasurableEmbedding.subtype_coe hS).integral_map _
  rw [hVf]
  exact (hconv f').congr hμf

/-- **Simon Ch. 8, 5.1–5.4 and the use of 3.7 in 5.5/5.7** (child `varifold_tangents` of
`main_theorem`), at a point `x` where `ρ^{1-n}‖δV‖(B_ρ(x)) → 0` (5.1). First, if
`Θ^n(μ_V, x) = θ₀ > 0`, every `λ_j ↓ 0` has a subsequence along which `V_{x,λ_j}` converges, and
every `C ∈ VarTan(V, x)` is stationary with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` and `μ_C(s A) = s^n μ_C(A)`
(5.2 and 5.3, corrected). Second, if `ρ^{-n} μ_V({y ∈ B_ρ(x) : Θ^n(μ_V, y) ≥ τ fails}) → 0`, then
`Θ^n(μ_C, ·) ≥ τ` holds `μ_C`-a.e. for every `C ∈ VarTan(V, x)`. Between 5.2 and 5.3, the constant
ratio `μ_C(B_R(0)) / R^n` forces `y ∈ S` for `C`-a.e. `(y, S)`: this is SimonGMT's radial rigidity,
the equality case of 3.4. -/
theorem Submission.varifold_tangent_theorems :
    VarifoldTangentCones ∧ ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U)
      (x : Euclidean N) (τ : ℝ), V.HasLocallyBoundedFirstVariation → x ∈ U → 0 < τ →
      Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) /
        ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧
          ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} /
        ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      ∀ C : Varifold N n (univ : Set (Euclidean N)), IsVarifoldTangent V x C →
        ∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal τ ≤ θ := by
  refine ⟨fun N n U V x θ₀ hV hx _ hdens hvar ↦ ⟨fun t ht0 ht ↦ ?_, fun C hC ↦ ?_⟩,
    Submission.varifold_tangents_density_lower_bound Submission.density_semicontinuity_theorem⟩
  · -- (a) `V_{x,t}(B_R(0) × G) → θ₀ ω_n R^n` as `t ↓ 0`, so the masses of `V_{x,t_j}` on `K × G`
    -- are eventually bounded and Radon compactness on `ℝ^N` extracts a convergent subsequence.
    have htw : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨ht, .of_forall ht0⟩
    have hbound : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ univ → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
        ∀ᶠ j in atTop, rescaledMeasure V x (t j) (K ×ˢ (univ : Set (Grassmannian N n))) ≤ M := by
      intro K hK _
      obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall 0
      have hR : 0 < max R 1 := lt_max_of_lt_right one_pos
      have hL : ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal (max R 1) ^ n ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      refine ⟨_, ENNReal.add_ne_top.2 ⟨hL, ENNReal.one_ne_top⟩, ?_⟩
      filter_upwards [((Submission.varifold_tangents_rescaled_ball_mass_tendsto N n U V x _ _ hdens
        hR).comp htw).eventually (eventually_lt_nhds (ENNReal.lt_add_right hL one_ne_zero))]
        with j hj
      exact (measure_mono (prod_mono (hKR.trans (closedBall_subset_closedBall (le_max_left R 1)))
        subset_rfl)).trans hj.le
    obtain ⟨φ, hφ, C, hC⟩ := Submission.varifold_radon_compactness N n univ
      (fun j ↦ rescaledMeasure V x (t j)) isOpen_univ hbound
    exact ⟨φ, hφ, C, fun f ↦ hC f (by simp)⟩
  · -- (b) `C` is stationary and satisfies 5.2, which makes `μ_C(B_R(0)) / R^n` constant; hence
    -- `p_S(y) = y` for `C`-a.e. `(y, S)`, and 5.3 follows.
    have hstat := Submission.varifold_tangents_limit_stationary N n U V x C hV hx hvar hC
    have hmass := Submission.varifold_tangents_limit_ball_mass N n U V x θ₀ C hdens hC
    refine ⟨hstat, hmass, Submission.varifold_tangents_radial_stationary_homogeneous N n C hstat ?_⟩
    have hrad := hstat.ae_normalProject_eq_zero_of_constant_mass_ratio
      (c := ENNReal.ofReal θ₀ * unitBallVolume n) fun R hR ↦ by
        rw [Varifold.normalizedBallMass, hmass R hR, ENNReal.ofReal_pow hR.le]
        exact ENNReal.mul_div_cancel_right (pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    filter_upwards [hrad] with z hz
    rw [Grassmannian.normalProject_eq_sub, sub_eq_zero] at hz
    exact hz.symm

/-- **Simon Ch. 8, 5.5 with Remark 5.6, and 5.7, pp. 215–218** (child `allard_tangent_cones` of
`main_theorem`): Allard's Rectifiability Theorem, and tangent cones are rectifiable cones.
Part A (5.5, 5.6) is child `allard_rectifiability`, applied to 2.5–2.10
(`first_variation_theorems`), 3.4 and 3.6 (`monotonicity_and_density_theorems`), 4.1
(`constancy_theorem`), 5.1–5.4 with the blow-up density lower bound (`varifold_tangent_theorems`),
Lemma 1.3 (`plane_disintegration`) and 1.2 (`first_rectifiability_theorem`).  Part B (5.7) is child
`tangent_cones_rectifiable`; as in the printed proof of 5.7, it applies 5.5, i.e. Part A, to each
tangent cone. -/
theorem Submission.allard_rectifiability_and_tangent_cones :
    AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones := by
  -- Part A (5.5, 5.6): child `allard_rectifiability` with the sibling theorems it assumes.
  have hA : AllardRectifiabilityTheorem :=
    Submission.allard_tc_rectifiability Submission.first_variation_theorems.2
      Submission.monotonicity_and_density_theorems.2.1
      Submission.monotonicity_and_density_theorems.2.2 Submission.constancy_theorem
      Submission.varifold_tangent_theorems.1 Submission.varifold_tangent_theorems.2
      Submission.plane_disintegration Submission.first_rectifiability_theorem
  -- Part B (5.7): child `tangent_cones_rectifiable`, whose proof applies Part A to the cones.
  exact ⟨hA, Submission.allard_tc_tangent_cones_rectifiable Submission.varifold_tangent_theorems.1
    Submission.varifold_tangent_theorems.2 hA Submission.first_rectifiability_theorem⟩

end GMT.Ch08

/-- **Simon Ch. 8, 5.8 (Compactness Theorem)**, "a direct consequence of" Ch. 1, 4.16, 3.7 and 5.5.
Uniform mass bounds on compact sets let the Radon compactness theorem (Ch. 1, 4.16, corrected)
extract `V_{φ(j)} → V`; zero extension of test functions on `Gₙ(U)` makes this convergence as Radon
measures on `Gₙ(U)`; semicontinuity 3.7 along the subsequence gives locally bounded first
variation, `‖δV‖(W) ≤ liminf_{j} ‖δV_{φ(j)}‖(W)` and `Θ^n(μ_V, ·) ≥ 1` `μ_V`-a.e.; and Allard's
theorem 5.5 makes `V` rectifiable.  The rectifiability of the `V_j` is not needed. -/
theorem Submission.compactness_theorem : CompactnessTheorem := by
  intro N n U Vj A _ hVj hbound hdens hA
  have hU : IsOpen U := (Vj 0).isOpen_domain
  -- Ch. 1, 4.16 needs `sup_j μ_{V_j}(K) < ∞` for compact `K ⊆ U`: take an open `W ⊂⊂ U` around `K`.
  have hmass : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ j in atTop, (Vj j).measure (K ×ˢ (univ : Set (Grassmannian N n))) ≤ C := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    refine ⟨_, hbound W ⟨hWo, hWc, hWU⟩, Eventually.of_forall fun j ↦ ?_⟩
    rw [← (Vj j).weight_apply hK.measurableSet]
    exact (measure_mono hKW).trans (le_self_add.trans (le_iSup
      (fun j ↦ (Vj j).weight W + variationMeasure (Vj j) W) j))
  obtain ⟨φ, hφ, V, hconv⟩ :=
    Submission.varifold_radon_compactness N n U (fun j ↦ (Vj j).measure) hU hmass
  -- A test function on `Gₙ(U)` extends by zero to one on `ℝ^N × G(N,n)` supported in `U × G(N,n)`.
  have hRC : Varifold.RadonConverges (fun j ↦ Vj (φ j)) V := by
    intro f
    let g : C_c(Euclidean N × Grassmannian N n, ℝ) :=
      { toFun := Subtype.val.extend f 0
        continuous_toFun :=
          f.hasCompactSupport.continuous_extend_zero (hU.prod isOpen_univ) f.continuous
        hasCompactSupport' := f.hasCompactSupport.extend_zero continuous_subtype_val }
    have hg : tsupport g ⊆ U ×ˢ (univ : Set (Grassmannian N n)) :=
      (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    have hint : ∀ W : Varifold N n U, ∫ z, g z ∂W.measure = ∫ z, f z ∂W.domainMeasure := by
      intro W
      rw [← W.map_domainMeasure, (MeasurableEmbedding.subtype_coe
        (hU.measurableSet.prod MeasurableSet.univ)).integral_map]
      exact integral_congr_ae (Eventually.of_forall fun z ↦
        Subtype.val_injective.extend_apply f 0 z)
    simpa only [hint] using hconv g hg
  -- 3.7 along the subsequence; its `liminf` hypothesis follows from the uniform bound.
  have hliminf : ∀ W, IsRelCompactOpenIn W U →
      liminf (fun j ↦ variationMeasure (Vj (φ j)) W) atTop ≠ ∞ := fun W hW ↦
    ne_top_of_le_ne_top (hbound W hW) (liminf_le_of_frequently_le' (Frequently.of_forall
      fun j ↦ le_add_self.trans (le_iSup
        (fun j ↦ (Vj j).weight W + variationMeasure (Vj j) W) (φ j))))
  obtain ⟨hVbv, hVvar, hVdens⟩ :=
    Submission.density_semicontinuity_theorem N n U (fun j ↦ Vj (φ j)) V (fun j ↦ A (φ j)) hRC
      (fun j ↦ hVj (φ j)) hliminf (fun j ↦ hdens (φ j))
      (fun W hW ↦ (hA W hW).comp hφ.tendsto_atTop)
  -- 5.5: `Θ^n(μ_V, ·) ≥ 1 > 0` `μ_V`-a.e.
  have hrect : IsRectifiable V :=
    (Submission.allard_rectifiability_and_tangent_cones.1 N n U V hVbv
      (hVdens.mono fun _ ⟨θ, hθ, hθ1⟩ ↦ ⟨θ, hθ, zero_lt_one.trans_le hθ1⟩)).1
  exact ⟨φ, hφ, V, hRC, hrect, hVbv, hVdens, hVvar⟩
