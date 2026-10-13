import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.Submanifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Poincare.SimonGMT.Chapter01.DensityComparison
import Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper
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

/-- σ-finiteness of `μ ⌞ M` for a positive, locally integrable multiplicity (Simon Ch. 8, p. 206;
used for 5.9 with `μ = H^n`): if `U` is open, `M ⊆ U`, `θ > 0` on `M` and `θ` is `μ`-integrable on
`M ∩ K` for every compact `K ⊆ U`, then `μ ⌞ M` is σ-finite.  `M` need not be measurable. -/
theorem Submission.intcpt_id_restrict_sigmaFinite :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (U M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsOpen U → M ⊆ U → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μ) → SigmaFinite (μ.restrict M) := by
  intro N μ U M θ hU hMU hpos hint
  -- Step 2: compact sets `K i ⊆ U` with `⋃ i, K i = U`.  Instead of the explicit cover by
  -- rational closed balls, use that an open subset of the locally compact, second countable
  -- space `ℝ^N` is σ-compact.
  obtain ⟨K, hKc, hKU⟩ : IsSigmaCompact U :=
    haveI := hU.locallyCompactSpace
    isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hKsub : ∀ i, K i ⊆ U := fun i ↦ hKU ▸ subset_iUnion K i
  have hKm : ∀ i, MeasurableSet (K i) := fun i ↦ (hKc i).isClosed.measurableSet
  -- Step 3: Borel `g i` with `θ = g i` `μ ⌞ (M ∩ K i)`-a.e. and
  -- `∫⁻ ofReal (g i) d(μ ⌞ (M ∩ K i)) = ∫⁻ ofReal θ d(μ ⌞ (M ∩ K i)) < ∞`.
  have hI : ∀ i, Integrable θ (μ.restrict (M ∩ K i)) := fun i ↦ hint (K i) (hKc i) (hKsub i)
  choose g hgm hgeq using fun i ↦ (hI i).aemeasurable
  have hlint : ∀ i, ∫⁻ y, ENNReal.ofReal (g i y) ∂(μ.restrict (M ∩ K i)) < ∞ := fun i ↦
    (lintegral_congr_ae ((hgeq i).mono fun y hy ↦ congrArg ENNReal.ofReal hy.symm)).trans_lt
      (hI i).lintegral_lt_top
  -- Step 4: the countable family `{Uᶜ} ∪ {Z i} ∪ {S (i, k)}`, with
  -- `Z i = K i ∩ {g i ≤ 0}` and `S (i, k) = K i ∩ {g i ≥ 1 / (k + 1)}`.
  let Z : ℕ → Set (Euclidean N) := fun i ↦ K i ∩ {y | g i y ≤ 0}
  let S : ℕ × ℕ → Set (Euclidean N) := fun p ↦ K p.1 ∩ {y | 1 / ((p.2 : ℝ) + 1) ≤ g p.1 y}
  refine Measure.sigmaFinite_of_countable (S := insert Uᶜ (range Z ∪ range S))
    (((countable_range Z).union (countable_range S)).insert _) ?_ ?_
  · -- Step 5: every member of the family has finite `μ ⌞ M`-measure.
    rintro s (rfl | ⟨i, rfl⟩ | ⟨⟨i, k⟩, rfl⟩)
    · -- (a) `(μ ⌞ M)(Uᶜ) = μ(Uᶜ ∩ M) = 0`, since `M ⊆ U`.
      rw [Measure.restrict_apply hU.isClosed_compl.measurableSet]
      exact (measure_mono_null (fun y hy ↦ hy.1 (hMU hy.2)) measure_empty).trans_lt
        ENNReal.zero_lt_top
    · -- (b) `(μ ⌞ M)(Z i) = 0`: on `Z i ∩ M`, `g i ≤ 0 < θ`, so `Z i ∩ M ⊆ {θ ≠ g i} ∩ (M ∩ K i)`,
      -- which is `μ`-null because `{θ ≠ g i}` is `μ ⌞ (M ∩ K i)`-null.
      rw [Measure.restrict_apply ((hKm i).inter (measurableSet_le (hgm i) measurable_const))]
      have hnull : μ ({y | θ y ≠ g i y} ∩ (M ∩ K i)) = 0 :=
        nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply _ _).trans_eq (hgeq i))
      refine (measure_mono_null ?_ hnull).trans_lt ENNReal.zero_lt_top
      rintro y ⟨⟨hyK, hyg⟩, hyM⟩
      refine ⟨?_, hyM, hyK⟩
      have hθ : 0 < θ y := hpos y hyM
      have hg : g i y ≤ 0 := hyg
      exact (hg.trans_lt hθ).ne'
    · -- (c) Markov: `(μ ⌞ M)(S (i, k)) = (μ ⌞ (M ∩ K i)){1 / (k + 1) ≤ g i}`
      -- `≤ (k + 1) ∫⁻ ofReal (g i) d(μ ⌞ (M ∩ K i)) < ∞`.
      have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hL : MeasurableSet {y | 1 / ((k : ℝ) + 1) ≤ g i y} :=
        measurableSet_le measurable_const (hgm i)
      rw [Measure.restrict_apply ((hKm i).inter hL)]
      have hEq : K i ∩ {y | 1 / ((k : ℝ) + 1) ≤ g i y} ∩ M
          = {y | ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ ENNReal.ofReal (g i y)} ∩ (M ∩ K i) := by
        ext y
        simp only [mem_inter_iff, mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff', not_le.mpr hc,
          or_false]
        tauto
      rw [hEq, ← Measure.restrict_apply
        (measurableSet_le measurable_const (hgm i).ennreal_ofReal)]
      have hmarkov := mul_meas_ge_le_lintegral₀ (μ := μ.restrict (M ∩ K i))
        (hgm i).ennreal_ofReal.aemeasurable (ENNReal.ofReal (1 / ((k : ℝ) + 1)))
      exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top (hlint i).ne hmarkov)
        (ENNReal.ofReal_pos.mpr hc).ne'
  · -- Step 4: the family covers `ℝ^N`.
    refine eq_univ_of_forall fun y ↦ ?_
    by_cases hy : y ∈ U
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hKU.symm ▸ hy : y ∈ ⋃ i, K i)
      rcases le_or_gt (g i y) 0 with h | h
      · exact ⟨Z i, Or.inr (Or.inl ⟨i, rfl⟩), hi, h⟩
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt h
        exact ⟨S (i, k), Or.inr (Or.inr ⟨(i, k), rfl⟩), hi, hk.le⟩
    · exact ⟨Uᶜ, Or.inl rfl, hy⟩

/-- The weight of `V = v(M, θ)` (Simon Ch. 8, p. 206: `V(A) = μ(π(TM ∩ A))` with `μ = H^n ⌞ θ`) is
`θ H^n ⌞ M` restricted to a Borel hull `T` of the tangent-point set
`M_* = {x ∈ M : M has an approximate tangent space at x with respect to θ}` (Ch. 3, 1.7):
`μ_V = ((H^n ⌞ M) ⌞ θ) ⌞ T` with `M_* ⊆ T`, and `μ_V(B) = ∫_{M_* ∩ B} θ dH^n` for Borel `B`. -/
theorem Submission.intcpt_id_weight_hull :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf V M θ → ∃ T : Set (Euclidean N), MeasurableSet T ∧ {x | x ∈ M ∧ ∃ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane} ⊆ T ∧ V.weight = (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun x ↦ ENNReal.ofReal (θ x)).restrict T ∧ ∀ B : Set (Euclidean N), MeasurableSet B → V.weight B = ∫⁻ x in {x | x ∈ M ∧ ∃ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane} ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
  intro N n U V M θ hV
  -- Step 1: unpack `V = v(M, θ)`; `M_* ⊆ M ⊆ U`.
  obtain ⟨hMU, -, -, hθpos, hθint, hVA⟩ := hV
  set Mstar : Set (Euclidean N) := {x | x ∈ M ∧ ∃ S : Grassmannian N n,
    Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane}
  have hMstarM : Mstar ⊆ M := fun x hx ↦ hx.1
  -- Step 2: `μ_V(B) = V(B × G(N,n)) = ∫⁻_{M_* ∩ B} θ dH^n` for Borel `B`.
  have hweight : ∀ B : Set (Euclidean N), MeasurableSet B →
      V.weight B = ∫⁻ x in Mstar ∩ B, ENNReal.ofReal (θ x) ∂μHE[n] := by
    intro B hB
    have hset : {x | x ∈ M ∧ ∃ S : Grassmannian N n,
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ∧
          (x, S) ∈ B ×ˢ (univ : Set (Grassmannian N n))} = Mstar ∩ B := by
      ext x
      constructor
      · rintro ⟨hxM, S, hS, hxB, -⟩
        exact ⟨⟨hxM, S, hS⟩, hxB⟩
      · rintro ⟨⟨hxM, S, hS⟩, hxB⟩
        exact ⟨hxM, S, hS, hxB, mem_univ S⟩
    rw [V.weight_apply hB, hVA _ (hB.prod MeasurableSet.univ), hset]
  -- Step 3: `H^n ⌞ M` is σ-finite (sibling `intcpt_id_restrict_sigmaFinite`).
  have : SigmaFinite ((μHE[n] : Measure (Euclidean N)).restrict M) :=
    Submission.intcpt_id_restrict_sigmaFinite N μHE[n] U M θ V.isOpen_domain hMU hθpos hθint
  -- Step 4: the measurable hull `T` of `M_*` for `H^n ⌞ M` has `(H^n ⌞ M) ⌞ T = H^n ⌞ M_*`.
  set T : Set (Euclidean N) := toMeasurable ((μHE[n] : Measure (Euclidean N)).restrict M) Mstar
    with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hhull : ((μHE[n] : Measure (Euclidean N)).restrict M).restrict T =
      (μHE[n] : Measure (Euclidean N)).restrict Mstar := by
    rw [hT, Measure.restrict_toMeasurable_of_sFinite, Measure.restrict_restrict_of_subset hMstarM]
  -- Step 5: `μ_V(B) = (ν ⌞ T)(B)` on Borel `B`, hence `μ_V = ν ⌞ T`.
  refine ⟨T, hTm, subset_toMeasurable _ _, ?_, hweight⟩
  ext1 B hB
  rw [hweight B hB, Measure.restrict_apply hB, withDensity_apply _ (hB.inter hTm),
    ← Measure.restrict_restrict hB, hhull, Measure.restrict_restrict hB, inter_comm B Mstar]
/-- Change of variables for `H^n` set integrals under the blow-up map (step 1 of the tangent-point
density argument, Simon Ch. 3, Remark 1.8(2)): for `r > 0`, `η = η_{x,r}` (`η y = r⁻¹ • (y - x)`),
an arbitrary set `M` and an arbitrary `F : ℝ^N → ℝ`, `∫_{η(M)} F dH^n = r⁻¹ ^ n ∫_M F ∘ η dH^n`. -/
theorem Submission.intcpt_id_tpd_setIntegral_blowUpMap_image :
    ∀ (N n : ℕ) (x : Euclidean N) (r : ℝ) (M : Set (Euclidean N)) (F : Euclidean N → ℝ), 0 < r → ∫ y in Chapter03.blowUpMap x r '' M, F y ∂μHE[n] = r⁻¹ ^ n * ∫ z in M, F (Chapter03.blowUpMap x r z) ∂μHE[n] := by
  intro N n x r M F hr
  -- Step 1: `η` is a homeomorphism of `ℝ^N` (inverse `y ↦ x + r • y`), hence an injective
  -- measurable embedding.
  let η : Euclidean N ≃ₜ Euclidean N :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hη : (η : Euclidean N → Euclidean N) = Chapter03.blowUpMap x r := rfl
  have hemb : MeasurableEmbedding η := η.measurableEmbedding
  -- Step 2: for every set `S`, `η⁻¹(S) = x + r • S`, so `H^n(η⁻¹(S)) = r ^ n H^n(S)`.
  have hpre : ∀ S : Set (Euclidean N),
      (μHE[n] : Measure (Euclidean N)) (η ⁻¹' S) = ENNReal.ofReal (r ^ n) * μHE[n] S := by
    intro S
    have hS : (η : Euclidean N → Euclidean N) ⁻¹' S = (x + ·) '' (r • S) := by
      ext y
      constructor
      · intro hy
        refine ⟨r • η y, Set.smul_mem_smul_set hy, ?_⟩
        change x + r • (r⁻¹ • (y - x)) = y
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        change r⁻¹ • (x + r • s - x) ∈ S
        rwa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [hS, (isometry_add_left x).euclideanHausdorffMeasure_image,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne', ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr.le, ENNReal.ofReal_pow hr.le]
  -- Step 3: `H^n.map η = r ^ n • H^n`, checked on Borel sets.
  have hmap : (μHE[n] : Measure (Euclidean N)).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)) := by
    ext S hS
    rw [Measure.map_apply hemb.measurable hS, hpre, Measure.smul_apply, smul_eq_mul]
  -- Step 4: `(H^n ⌞ M).map η = r ^ n • H^n ⌞ η(M)`, since `η⁻¹(η(M)) = M`.
  have hres : ((μHE[n] : Measure (Euclidean N)).restrict M).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)).restrict (η '' M) := by
    rw [← Measure.restrict_smul, ← hmap, hemb.restrict_map, Set.preimage_image_eq M η.injective]
  -- Step 5: `∫_M F ∘ η dH^n = r ^ n ∫_{η(M)} F dH^n`; neither `M` nor `F` need be measurable.
  have hcov : ∫ z in M, F (η z) ∂μHE[n] = r ^ n * ∫ y in η '' M, F y ∂μHE[n] := by
    rw [← hemb.integral_map, hres, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_nonneg hr.le n), smul_eq_mul]
  -- Step 6: multiply by `r⁻¹ ^ n`, as `r⁻¹ ^ n * r ^ n = 1`.
  rw [← hη, hcov, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
/-- The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-dimensional subspace
`P ⊆ ℝ^N` is `ω_n r^n` (Simon Ch. 3, Remark 1.8(2); the plane-ball step of the tangent-point density
argument for Simon Ch. 8, 5.9): `P ∩ B_r(0)` is the image of the closed `r`-ball of `P` under the
isometric inclusion, `H^n = vol` on `P`, and an orthonormal coordinate map `P ≃ ℝ^n` carries the
volume of the open unit ball of `P` to `ω_n`. -/
theorem Submission.intcpt_id_tpd_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)) (r : ℝ), Module.finrank ℝ P = n → 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((P : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n P r hP hr
  -- Step 1: `P ∩ B_r(0)` is the image of the closed `r`-ball of `P` under the inclusion.
  have himage : (P : Set (Euclidean N)) ∩ closedBall 0 r =
      (Subtype.val : P → Euclidean N) '' closedBall (0 : P) r := by
    ext z
    constructor
    · rintro ⟨hz, hzr⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [mem_closedBall_zero_iff] at hzr ⊢
      exact hzr
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      rw [mem_closedBall_zero_iff] at hw ⊢
      exact hw
  -- Step 3: `H^n = vol` on `P`, because `finrank P = n`.
  have hvol : (μHE[n] : Measure P) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P)
    rwa [hP] at h
  -- Step 5: orthonormal coordinates `e : P ≃ ℝ^n` preserve volume and the open unit ball.
  let e : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr
  have hball : volume (ball (0 : P) 1) = unitBallVolume n := by
    have hpre : e ⁻¹' ball 0 1 = ball (0 : P) 1 := by
      ext w
      simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
    rw [← hpre, e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]
    rfl
  -- Steps 2, 4 and 6: isometry invariance of `H^n`, Haar scaling of balls in `P`, and
  -- `ofReal (r ^ n) = ofReal r ^ n` for `r ≥ 0`.
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hvol,
    Measure.addHaar_closedBall volume (0 : P) hr, hP, hball, ENNReal.ofReal_pow hr, mul_comm]
/-- Density squeeze (Simon Ch. 3, Remark 1.8(2), final step): if, as `t ↓ 0`, eventually
`c t^n ≤ μ(B_t(x))` for each `c < a ω_n` and eventually `μ(B_t(x)) ≤ c t^n` for each
`c > a ω_n`, then `Θ^n(μ, x)` exists and equals `a`. -/
theorem Submission.intcpt_id_tpd_hasDensity_of_ball_mass_bounds :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (a : ℝ≥0∞), (∀ c : ℝ≥0∞, c < a * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) → (∀ c : ℝ≥0∞, a * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n) → HasDensity n μ x a := by
  intro N n μ x a hlower hupper
  -- `0 < ω_n < ∞`: the open unit ball of `ℝ^n` is nonempty, open and bounded.
  have hω₀ : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hω : unitBallVolume n ≠ ∞ := measure_ball_ne_top
  -- By `tendsto_order`, bound the density ratio eventually from below and from above.
  rw [HasDensity, tendsto_order]
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- For `b < b' < a`: eventually `(b' ω_n) t^n ≤ μ(B_t(x))`, so `b' ≤ densityRatio`.
    obtain ⟨b', hbb', hb'a⟩ := exists_between hb
    filter_upwards [hlower _ (ENNReal.mul_lt_mul_left hω₀ hω hb'a), self_mem_nhdsWithin]
      with t hmass ht
    -- For `t > 0` the normalizer `ω_n t^n` is nonzero and finite.
    have hD₀ : unitBallVolume n * ENNReal.ofReal t ^ n ≠ 0 :=
      mul_ne_zero hω₀ (pow_ne_zero n (ENNReal.ofReal_pos.mpr ht).ne')
    have hD : unitBallVolume n * ENNReal.ofReal t ^ n ≠ ∞ :=
      ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    calc b < b' := hbb'
      _ ≤ densityRatio n μ x t := by
        rw [densityRatio, ENNReal.le_div_iff_mul_le (Or.inl hD₀) (Or.inl hD), ← mul_assoc]
        exact hmass
  · -- For `a < b' < b`: eventually `μ(B_t(x)) ≤ (b' ω_n) t^n`, so `densityRatio ≤ b'`.
    obtain ⟨b', hab', hb'b⟩ := exists_between hb
    filter_upwards [hupper _ (ENNReal.mul_lt_mul_left hω₀ hω hab')] with t hmass
    calc densityRatio n μ x t ≤ b' := by
          rw [densityRatio]
          exact ENNReal.div_le_of_le_mul (by rwa [← mul_assoc])
      _ < b := hb'b

/-- Cut-off sandwich for one blow-up integral (tangent point density, Simon Ch. 3, Remark 1.8(2)):
let `θ ≥ 0` on `M` be `H^n`-integrable on `M ∩ B_{r₀}(x)`, `ν = (H^n ⌞ M) ⌞ θ`, `η = η_{x,r}`
(`η z = r⁻¹ • (z - x)`) with `r > 0`, and `f ∈ C_c(ℝ^N)` with `0 ≤ f ≤ 1`, `f = 1` on `B_a(0)` and
`f = 0` off `B_R(0)`, where `rR ≤ r₀`. Then
`ν(B_{ra}(x)) ≤ r^n ∫_{η(M)} f(y) θ(x + r y) dH^n(y) ≤ ν(B_{rR}(x))`. -/
theorem Submission.intcpt_id_tpd_ball_sandwich :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (f : C_c(Euclidean N, ℝ)) (r₀ a R r : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ 1) → (∀ y, ‖y‖ ≤ a → f y = 1) → (∀ y, R < ‖y‖ → f y = 0) → 0 < r → r * R ≤ r₀ → (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * a)) ≤ ENNReal.ofReal (r ^ n * ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n]) ∧ ENNReal.ofReal (r ^ n * ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n]) ≤ (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * R)) := by
  intro N n M θ x f r₀ a R r hM hθ hint hf0 hf1 hfa hfR hr hrR
  -- Notation: `η = blowUpMap x r`, `ν` the weighted measure of the statement, and
  -- `J = ∫⁻_M ofReal (f (η z)) * ofReal (θ z) dH^n(z) ∈ [0, ∞]`.
  -- Step 1: `‖η z‖ = |z - x| / r`, so `f ∘ η = 1` on `B_{ra}(x)` and `f ∘ η = 0` off `B_{rR}(x)`.
  have hnorm : ∀ z, ‖Chapter03.blowUpMap x r z‖ = dist z x / r := by
    intro z
    rw [Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, dist_eq_norm,
      inv_mul_eq_div]
  have hone : ∀ z ∈ closedBall x (r * a), f (Chapter03.blowUpMap x r z) = 1 := by
    intro z hz
    refine hfa _ ?_
    rw [hnorm, div_le_iff₀ hr, mul_comm a r]
    exact hz
  have hzero : ∀ z ∉ closedBall x (r * R), f (Chapter03.blowUpMap x r z) = 0 := by
    intro z hz
    refine hfR _ ?_
    rw [hnorm, lt_div_iff₀ hr, mul_comm R r]
    exact not_le.1 hz
  -- Step 2: `ν(B_s(x)) = ∫⁻_M 1_{B_s(x)} ofReal θ dH^n` (no measurability of `θ` is needed).
  have hball : ∀ s : ℝ, (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity
      fun y ↦ ENNReal.ofReal (θ y)) (closedBall x s) =
      ∫⁻ z in M, (closedBall x s).indicator (fun y ↦ ENNReal.ofReal (θ y)) z ∂μHE[n] := by
    intro s
    rw [withDensity_apply _ measurableSet_closedBall, lintegral_indicator measurableSet_closedBall]
  -- Step 3: `ν(B_{ra}(x)) ≤ J ≤ ν(B_{rR}(x))`, comparing the integrands pointwise.
  have hlow_pt : ∀ z, (closedBall x (r * a)).indicator (fun y ↦ ENNReal.ofReal (θ y)) z ≤
      ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z) := by
    intro z
    by_cases hz : z ∈ closedBall x (r * a)
    · rw [indicator_of_mem hz, hone z hz, ENNReal.ofReal_one, one_mul]
    · rw [indicator_of_notMem hz]
      exact zero_le
  have hup_pt : ∀ z, ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z) ≤
      (closedBall x (r * R)).indicator (fun y ↦ ENNReal.ofReal (θ y)) z := by
    intro z
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz]
      exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (hf1 _))
    · rw [indicator_of_notMem hz, hzero z hz, ENNReal.ofReal_zero, zero_mul]
  have hlow : (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity
      fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * a)) ≤
      ∫⁻ z in M, ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z) ∂μHE[n] := by
    rw [hball]
    exact lintegral_mono hlow_pt
  have hup : ∫⁻ z in M, ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z)
      ∂μHE[n] ≤ (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity
      fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * R)) := by
    rw [hball]
    exact lintegral_mono hup_pt
  -- Step 4: `J ≤ ν(B_{r₀}(x)) = ∫⁻_{M ∩ B_{r₀}(x)} ofReal θ dH^n < ∞`, as `rR ≤ r₀`.
  have hfin : ∫⁻ z in M, ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z)
      ∂μHE[n] ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (hup.trans (measure_mono (closedBall_subset_closedBall hrR)))
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (Integrable.lintegral_lt_top hint).ne
  -- Step 5: change of variables (`blowup_cov`) and `x + r • η z = z` give
  -- `r^n ∫_{η(M)} f(y) θ(x + r y) dH^n(y) = ∫_M f(η z) θ(z) dH^n(z)`.
  have hback : ∀ z, x + r • Chapter03.blowUpMap x r z = z := by
    intro z
    rw [Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hI : r ^ n * ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n] =
      ∫ z in M, f (Chapter03.blowUpMap x r z) * θ z ∂μHE[n] := by
    rw [Submission.intcpt_id_tpd_setIntegral_blowUpMap_image N n x r M
      (fun y ↦ f y * θ (x + r • y)) hr]
    simp only [hback]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  -- Step 6: `g = (f ∘ η) θ` is `≥ 0` a.e. on `M` and vanishes off `B_{r₀}(x)`, where `θ` is
  -- integrable, so `g` is a.e. strongly measurable and `∫_M g dH^n = J.toReal`.
  have hg0 : 0 ≤ᵐ[(μHE[n] : Measure (Euclidean N)).restrict M]
      fun z ↦ f (Chapter03.blowUpMap x r z) * θ z := by
    filter_upwards [ae_restrict_mem₀ hM] with z hz
    exact mul_nonneg (hf0 _) (hθ z hz)
  have hind : (closedBall x r₀).indicator (fun z ↦ f (Chapter03.blowUpMap x r z) * θ z) =
      fun z ↦ f (Chapter03.blowUpMap x r z) * θ z := by
    funext z
    by_cases hz : z ∈ closedBall x r₀
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz,
        hzero z fun h ↦ hz (closedBall_subset_closedBall hrR h), zero_mul]
  have hgm : AEStronglyMeasurable (fun z ↦ f (Chapter03.blowUpMap x r z) * θ z)
      ((μHE[n] : Measure (Euclidean N)).restrict M) := by
    rw [← hind, aestronglyMeasurable_indicator_iff measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    have hcont : Continuous fun z ↦ f (Chapter03.blowUpMap x r z) :=
      (map_continuous f).comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
    exact hcont.aestronglyMeasurable.mul hint.aestronglyMeasurable
  have hJ : ∫⁻ z in M, ENNReal.ofReal (f (Chapter03.blowUpMap x r z) * θ z) ∂μHE[n] =
      ∫⁻ z in M, ENNReal.ofReal (f (Chapter03.blowUpMap x r z)) * ENNReal.ofReal (θ z) ∂μHE[n] :=
    lintegral_congr fun z ↦ ENNReal.ofReal_mul (hf0 _)
  -- Step 7: `ofReal (r^n I) = ofReal J.toReal = J`, and Step 3 is the claim.
  rw [hI, integral_eq_lintegral_of_nonneg_ae hg0 hgm, hJ, ENNReal.ofReal_toReal hfin]
  exact ⟨hlow, hup⟩

/-- Plane cutoffs (steps 2 and 4 of the tangent-point density argument, Simon Ch. 3,
Remark 1.8(2)): for an `n`-dimensional subspace `P` of `ℝ^N` and `0 < a < R`, the radial cutoff
`f y = min 1 (max 0 ((R - ‖y‖) / (R - a)))` is in `C_c(ℝ^N, ℝ)`, takes values in `[0, 1]`, equals
`1` on `B_a(0)` and `0` off `B_R(0)`, and `ω_n a^n ≤ ∫_P f dH^n ≤ ω_n R^n`. -/
theorem Submission.intcpt_id_tpd_plane_cutoff :
    ∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)) (a R : ℝ), Module.finrank ℝ P = n → 0 < a → a < R → ∃ f : C_c(Euclidean N, ℝ), (∀ y, 0 ≤ f y) ∧ (∀ y, f y ≤ 1) ∧ (∀ y, ‖y‖ ≤ a → f y = 1) ∧ (∀ y, R < ‖y‖ → f y = 0) ∧ (unitBallVolume n).toReal * a ^ n ≤ ∫ y in (P : Set (Euclidean N)), f y ∂μHE[n] ∧ ∫ y in (P : Set (Euclidean N)), f y ∂μHE[n] ≤ (unitBallVolume n).toReal * R ^ n := by
  intro N n P a R hP ha haR
  have hRa : 0 < R - a := sub_pos.mpr haR
  have hR : 0 ≤ R := ha.le.trans haR.le
  -- Step 1: the cutoff `g y = min 1 (max 0 ((R - ‖y‖) / (R - a)))` is continuous, `[0, 1]`-valued,
  -- `1` where `‖y‖ ≤ a` and `0` where `R ≤ ‖y‖`; it vanishes off the compact `B̄_R`, so it
  -- packages as `f ∈ C_c(ℝ^N, ℝ)`.
  set g : Euclidean N → ℝ := fun y ↦ min 1 (max 0 ((R - ‖y‖) / (R - a))) with hg_def
  have hg_cont : Continuous g := by
    simp only [hg_def]
    fun_prop
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y ↦ le_min zero_le_one (le_max_left _ _)
  have hg_le_one : ∀ y, g y ≤ 1 := fun y ↦ min_le_left _ _
  have hg_one : ∀ y, ‖y‖ ≤ a → g y = 1 := by
    intro y hy
    have h1 : 1 ≤ (R - ‖y‖) / (R - a) := by
      rw [le_div_iff₀ hRa]
      linarith
    simp only [hg_def]
    exact min_eq_left (h1.trans (le_max_right _ _))
  have hg_zero : ∀ y, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have h1 : (R - ‖y‖) / (R - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hRa.le
    simp only [hg_def]
    rw [max_eq_left h1, min_eq_right zero_le_one]
  have hg_supp : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) R) fun y hy ↦ ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    exact hg_zero y hy.le
  let f : C_c(Euclidean N, ℝ) := ⟨⟨g, hg_cont⟩, hg_supp⟩
  have hf : ∀ y, f y = g y := fun y ↦ rfl
  -- Step 2: by the sibling `plane_ball`, `(H^n ⌞ P)(B̄_s) = ω_n s^n < ∞` for `s ≥ 0`, so
  -- `1_{B̄_s}` is `H^n ⌞ P`-integrable and `∫_P 1_{B̄_s} dH^n = ω_n s^n`.
  have hω : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have hball : ∀ s : ℝ, 0 ≤ s →
      ((μHE[n] : Measure (Euclidean N)).restrict (P : Set (Euclidean N))) (closedBall 0 s) =
        unitBallVolume n * ENNReal.ofReal s ^ n := by
    intro s hs
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.intcpt_id_tpd_plane_closedBall_hausdorff N n P s hP hs
  have hind_int : ∀ s : ℝ, 0 ≤ s →
      Integrable ((closedBall (0 : Euclidean N) s).indicator (1 : Euclidean N → ℝ))
        ((μHE[n] : Measure (Euclidean N)).restrict (P : Set (Euclidean N))) := by
    intro s hs
    rw [integrable_indicator_iff measurableSet_closedBall]
    refine integrableOn_const ?_
    rw [hball s hs]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hind_integral : ∀ s : ℝ, 0 ≤ s →
      ∫ y in (P : Set (Euclidean N)),
          (closedBall (0 : Euclidean N) s).indicator (1 : Euclidean N → ℝ) y ∂μHE[n] =
        (unitBallVolume n).toReal * s ^ n := by
    intro s hs
    rw [integral_indicator_one measurableSet_closedBall, measureReal_def, hball s hs,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs]
  -- Step 3: pointwise `1_{B̄_a} ≤ f ≤ 1_{B̄_R}`; as `|f| = f ≤ 1_{B̄_R}`, `f` is `H^n ⌞ P`-integrable.
  have hlow : ∀ y, (closedBall (0 : Euclidean N) a).indicator (1 : Euclidean N → ℝ) y ≤ f y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : Euclidean N) a
    · rw [indicator_of_mem hy, hf, hg_one y (by rwa [mem_closedBall, dist_zero_right] at hy)]
      rfl
    · rw [indicator_of_notMem hy, hf]
      exact hg_nonneg y
  have hup : ∀ y, f y ≤ (closedBall (0 : Euclidean N) R).indicator (1 : Euclidean N → ℝ) y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : Euclidean N) R
    · rw [indicator_of_mem hy, hf]
      exact hg_le_one y
    · rw [indicator_of_notMem hy, hf]
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact (hg_zero y hy.le).le
  have hf_int : Integrable (fun y ↦ f y)
      ((μHE[n] : Measure (Euclidean N)).restrict (P : Set (Euclidean N))) := by
    refine Integrable.mono' (hind_int R hR) f.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    have hfy : 0 ≤ f y := hg_nonneg y
    rw [Real.norm_eq_abs, abs_of_nonneg hfy]
    exact hup y
  -- Step 4: integrate the comparison over `P` and evaluate both sides by step 2.
  refine ⟨f, hg_nonneg, hg_le_one, hg_one, fun y hy ↦ hg_zero y hy.le, ?_, ?_⟩
  · rw [← hind_integral a ha.le]
    exact integral_mono (hind_int a ha.le) hf_int hlow
  · rw [← hind_integral R hR]
    exact integral_mono hf_int (hind_int R hR) hup

/-- Lower ball-mass bound at a weighted approximate tangent point (the lower half of Simon Ch. 3,
Remark 1.8(2)): if `M` has weighted approximate tangent space `P` at `x` with respect to `θ ≥ 0`
(Ch. 3, 1.7) and `θ` is `H^n`-integrable on `M ∩ B_{r₀}(x)`, then for every `c < θ(x) ω_n`,
`c t^n ≤ ν(B_t(x))` for all small `t > 0`, where `ν = (H^n ⌞ M).withDensity θ`. -/
theorem Submission.intcpt_id_tpd_ball_mass_lower :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (P : Submodule ℝ (Euclidean N)) (r₀ : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → 0 < r₀ → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P → ∀ c : ℝ≥0∞, c < ENNReal.ofReal (θ x) * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x t) := by
  intro N n M θ x P r₀ hM hθ hr₀ hint hP c hc
  -- Step 0: `0 < ω_n < ∞`, as `ω_n` is the volume of the open unit ball of `ℝ^n`.
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hω : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0 hωtop
  -- Step 1: `θ(x) > 0` (else the bound `c < 0` is impossible), and `c = ofReal c'` with
  -- `0 ≤ c' < θ(x) ω_n`.
  have hθx : 0 < θ x := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h), zero_mul] at hc
    exact ENNReal.not_lt_zero hc
  rw [← ENNReal.ofReal_toReal hωtop, ← ENNReal.ofReal_mul hθx.le] at hc
  obtain ⟨c', hc'0, rfl⟩ : ∃ c' : ℝ, 0 ≤ c' ∧ c = ENNReal.ofReal c' :=
    ⟨c.toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (hc.trans ENNReal.ofReal_lt_top).ne).symm⟩
  rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hθx hω)] at hc
  -- Step 2: some `κ ∈ (0, 1)` has `c' < θ(x) ω_n κ^n`, by continuity of `κ ↦ κ^n` at `1`.
  have hcont : Tendsto (fun κ : ℝ ↦ θ x * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
      (𝓝 (θ x * (unitBallVolume n).toReal)) := by
    have h := ((continuous_pow n).tendsto (1 : ℝ)).const_mul (θ x * (unitBallVolume n).toReal)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨κ, hκ, hκ01⟩ := ((hcont.eventually_const_lt hc).and (Ioo_mem_nhdsLT zero_lt_one)).exists
  -- Step 3: the sibling `plane_cutoff` gives `f ∈ C_c` with `1_{B_κ(0)} ≤ f ≤ 1_{B_1(0)}` and
  -- `ω_n κ^n ≤ ∫_P f dH^n`.
  obtain ⟨f, hf0, hf1, hfκ, hf1', hfP, -⟩ :=
    Submission.intcpt_id_tpd_plane_cutoff N n P κ 1 hP.1 hκ01.1 hκ01.2
  -- Step 4: by 1.7 the blow-up integrals `I_f(t)` tend to `θ(x) ∫_P f dH^n > c'`.
  have hlt : c' < θ x * ∫ y in (P : Set (Euclidean N)), f y ∂μHE[n] :=
    hκ.trans_le (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfP hθx.le)
  -- Step 5: for `0 < t ≤ r₀` the sibling `ball_sandwich` gives `ofReal (t^n I_f(t)) ≤ ν(B_t(x))`.
  filter_upwards [(hP.2 f).eventually_const_lt hlt, Ioc_mem_nhdsGT hr₀] with t ht htr
  have hsand := (Submission.intcpt_id_tpd_ball_sandwich N n M θ x f r₀ κ 1 t hM hθ hint hf0 hf1
    hfκ hf1' htr.1 ((mul_one t).le.trans htr.2)).2
  rw [mul_one] at hsand
  -- Step 6: `c t^n = ofReal (t^n c') ≤ ofReal (t^n I_f(t)) ≤ ν(B_t(x))`.
  calc ENNReal.ofReal c' * ENNReal.ofReal t ^ n = ENNReal.ofReal (t ^ n * c') := by
        rw [← ENNReal.ofReal_pow htr.1.le, ← ENNReal.ofReal_mul hc'0, mul_comm c']
    _ ≤ ENNReal.ofReal (t ^ n *
          ∫ y in Chapter03.blowUpMap x t '' M, f y * θ (x + t • y) ∂μHE[n]) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht.le (pow_nonneg htr.1.le n))
    _ ≤ _ := hsand
/-- Upper ball-mass bound at a weighted approximate tangent point (tangent point density, Simon
Ch. 3, Remark 1.8(2)): let `M` have weighted approximate tangent space `P` at `x ∈ M` with respect
to `θ ≥ 0` on `M`, with `θ` `H^n`-integrable on `M ∩ B_{r₀}(x)`, and let `ν = (H^n ⌞ M) ⌞ θ`.
Then every `c > θ(x) ω_n` satisfies `ν(B_t(x)) ≤ c t^n` for all sufficiently small `t > 0`. -/
theorem Submission.intcpt_id_tpd_ball_mass_upper :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (P : Submodule ℝ (Euclidean N)) (r₀ : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → x ∈ M → 0 < r₀ → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P → ∀ c : ℝ≥0∞, ENNReal.ofReal (θ x) * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x t) ≤ c * ENNReal.ofReal t ^ n := by
  intro N n M θ x P r₀ hM hθ hx hr₀ hint hP c hc
  -- Step 0: `ω_n` is the volume of a bounded ball, so `ω_n < ∞`; and `θ(x) ≥ 0` as `x ∈ M`.
  have hω : unitBallVolume n ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  have hθx : 0 ≤ θ x := hθ x hx
  -- Step 1: for `c = ∞` the bound holds at every `t > 0`.
  by_cases hctop : c = ∞
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hctop, ENNReal.top_mul (pow_ne_zero n (ENNReal.ofReal_pos.2 (mem_Ioi.1 ht)).ne')]
    exact le_top
  -- Step 2: otherwise `c = ofReal c'` with `c' = c.toReal`, and `θ(x) ω_n < c'`.
  have hc' : θ x * (unitBallVolume n).toReal < c.toReal := by
    refine (ENNReal.ofReal_lt_ofReal_iff'.1 ?_).1
    rwa [ENNReal.ofReal_mul hθx, ENNReal.ofReal_toReal hω, ENNReal.ofReal_toReal hctop]
  -- Step 3: choose `κ ∈ (0, 1)` with `θ(x) ω_n (κ⁻¹)^n < c'`, by continuity of `κ⁻¹` at `1`.
  have hlim : Tendsto (fun κ : ℝ ↦ θ x * (unitBallVolume n).toReal * κ⁻¹ ^ n) (𝓝[<] 1)
      (𝓝 (θ x * (unitBallVolume n).toReal)) := by
    have h : Tendsto (fun κ : ℝ ↦ θ x * (unitBallVolume n).toReal * κ⁻¹ ^ n) (𝓝 1)
        (𝓝 (θ x * (unitBallVolume n).toReal * (1 : ℝ)⁻¹ ^ n)) :=
      tendsto_const_nhds.mul ((tendsto_inv₀ one_ne_zero).pow n)
    rw [inv_one, one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨κ, hκc, hκ0, hκ1⟩ :=
    ((hlim.eventually_lt_const hc').and (Ioo_mem_nhdsLT zero_lt_one)).exists
  -- Step 4: the outer cutoff `f ∈ C_c` with `1_{B_1} ≤ f ≤ 1_{B_{1/κ}}` and
  -- `∫_P f dH^n ≤ ω_n (κ⁻¹)^n`.
  obtain ⟨f, hf0, hf1, hfa, hfR, -, hfP⟩ := Submission.intcpt_id_tpd_plane_cutoff N n P 1 κ⁻¹
    hP.1 zero_lt_one ((one_lt_inv₀ hκ0).2 hκ1)
  -- Step 5: `I_f(t) → θ(x) ∫_P f dH^n ≤ θ(x) ω_n (κ⁻¹)^n < c'`, so eventually `I_f(t) < c'`,
  -- where `I_f(t) = ∫_{η_t(M)} f(y) θ(x + t y) dH^n(y)`.
  have hfc : θ x * ∫ y in (P : Set (Euclidean N)), f y ∂μHE[n] < c.toReal := by
    refine (mul_le_mul_of_nonneg_left hfP hθx).trans_lt ?_
    rwa [← mul_assoc]
  -- Step 6: for `0 < t ≤ κ r₀` we have `t κ⁻¹ ≤ r₀`, and the sandwich (with `a = 1`,
  -- `R = κ⁻¹`) gives `ν(B_t(x)) ≤ ofReal (t^n I_f(t))`.
  filter_upwards [(hP.2 f).eventually_lt_const hfc, Ioc_mem_nhdsGT (mul_pos hκ0 hr₀)]
    with t hIt ht
  have htR : t * κ⁻¹ ≤ r₀ := by
    rw [← div_eq_mul_inv, div_le_iff₀ hκ0, mul_comm r₀ κ]
    exact ht.2
  have hsand := (Submission.intcpt_id_tpd_ball_sandwich N n M θ x f r₀ 1 κ⁻¹ t hM hθ hint hf0 hf1
    hfa hfR ht.1 htR).1
  rw [mul_one] at hsand
  -- Step 7: `ofReal (t^n I_f(t)) ≤ ofReal (t^n c') = c ofReal(t)^n`.
  refine hsand.trans ((ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hIt.le (pow_nonneg ht.1.le n))).trans_eq ?_)
  rw [mul_comm (t ^ n), ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hctop,
    ENNReal.ofReal_pow ht.1.le]

/-- Density at a weighted approximate tangent point (Simon Ch. 3, Remark 1.8(2)): if `M` is
`H^n`-measurable, `θ ≥ 0` on `M` is `H^n`-integrable on `M ∩ B_{r₀}(x)`, `x ∈ M`, and `M` has
weighted approximate tangent space `P` at `x` with respect to `θ` (Ch. 3, 1.7), then
`ν = (H^n ⌞ M).withDensity θ` has `Θ^n(ν, x) = θ(x)`, i.e. `ν(B_ρ(x))/(ω_n ρ^n) → θ(x)` as
`ρ ↓ 0`. -/
theorem Submission.intcpt_id_tangent_point_density :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (P : Submodule ℝ (Euclidean N)) (r₀ : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → x ∈ M → 0 < r₀ → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P → HasDensity n (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) x (ENNReal.ofReal (θ x)) := by
  intro N n M θ x P r₀ hM hθ hx hr₀ hint hP
  -- Steps 1–5: comparing `1_{B_t(x)}` with cut-offs blown up by `η_{x,t}` and passing to the
  -- limit in 1.7 gives `c t^n ≤ ν(B_t(x))` eventually for every `c < θ(x) ω_n` (sibling
  -- `ball_mass_lower`) and `ν(B_t(x)) ≤ c t^n` eventually for every `c > θ(x) ω_n` (sibling
  -- `ball_mass_upper`).
  -- Step 6: the two-sided bounds squeeze `ν(B_t(x))/(ω_n t^n)` to `θ(x)` in `[0, ∞]`.
  exact Submission.intcpt_id_tpd_hasDensity_of_ball_mass_bounds N n _ x _
    (Submission.intcpt_id_tpd_ball_mass_lower N n M θ x P r₀ hM hθ hr₀ hint hP)
    (Submission.intcpt_id_tpd_ball_mass_upper N n M θ x P r₀ hM hθ hx hr₀ hint hP)
/-- **Simon Ch. 1, 3.6 (Upper Density Theorem), localized as in Remark 3.7(2)** (child
`zero_density_off_set` of `integral_density`, parent step 5): if `μ` is finite on compact subsets
of the open set `U` and `A` is Borel, then `Θ^n(μ⌞A, x) = 0` for `H^n`-a.e. `x ∈ U ∖ A`.
Simon's proof of 3.6 is carried out inline: the comparison estimate of 3.3 comes from a covering
lemma (3.4; here Mathlib's Vitali lemma with enlargement `4`, which only changes the constant),
closed sets `C_j ⊆ A` with `μ(A ∖ C_j) → 0` (1.15(2)) make the bad set `H^n`-null, and `U` is
covered by countably many balls `B_q(c)` with `B_{2q}(c) ⊆ U`, on which `μ` is finite (3.7(2)). -/
theorem Submission.intcpt_id_restrict_density_zero_ae : ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (U A : Set (Euclidean N)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → MeasurableSet A → ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)), x ∈ U → x ∉ A → HasDensity n (μ.restrict A) x 0 := by
  intro N n μ U A hU hfin hA
  -- `H^n = c • μH[n]`, so it suffices to work with `μH[n]`.
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  refine Measure.ae_smul_measure ?_ _
  -- `ω_n` is positive and finite.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Comparison estimate (Simon 3.3–3.4, Vitali covering): if every point of `F` is the centre of
  -- arbitrarily small closed balls `B_ρ` with `s ρ^n ≤ ν(B_ρ)`, then `μH[n](F) ≤ 8^n ν(ℝ^N) / s`.
  have hcov : ∀ (ν : Measure (Euclidean N)) (F : Set (Euclidean N)) (s : ℝ≥0∞), s ≠ 0 → s ≠ ∞ →
      (∀ x ∈ F, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        s * ENNReal.ofReal ρ ^ n ≤ ν (closedBall x ρ)) →
      μH[(n : ℝ)] F ≤ 8 ^ n * ν univ * s⁻¹ := by
    intro ν F s hs0 hstop hF
    choose! r hr0 hrδ hrν using hF
    have hδ : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
    have hV := fun m : ℕ => Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall F id
      (fun a => r a (1 / ((m : ℝ) + 1))) (1 / ((m : ℝ) + 1))
      (fun a ha => (hrδ a ha _ (hδ m)).le) 4 (by norm_num)
    choose u huF hud hucov using hV
    have huc : ∀ m, (u m).Countable := fun m =>
      (hud m).countable_of_nonempty_interior fun a ha =>
        ⟨a, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds a (hr0 a (huF m ha) _ (hδ m)))⟩
    have : ∀ m, Countable (u m) := fun m => (huc m).to_subtype
    have htend : Tendsto (fun m : ℕ => ENNReal.ofReal (8 * (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => 8 * (1 / ((m : ℝ) + 1))) atTop (𝓝 (8 * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 8
      rw [mul_zero] at h1
      simpa using ENNReal.tendsto_ofReal h1
    have hdiam : ∀ᶠ m in atTop, ∀ i : u m,
        ediam (closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1)))) ≤
          ENNReal.ofReal (8 * (1 / ((m : ℝ) + 1))) := by
      refine Eventually.of_forall fun m i => ?_
      refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
      rw [mem_closedBall] at hx hy
      have := hrδ i (huF m i.2) _ (hδ m)
      linarith [dist_triangle_right x y (i : Euclidean N)]
    have hcover : ∀ᶠ m in atTop,
        F ⊆ ⋃ i : u m, closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1))) := by
      refine Eventually.of_forall fun m a ha => ?_
      obtain ⟨b, hb, hab⟩ := hucov m a ha
      exact mem_iUnion.mpr ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 a ha _ (hδ m)).le)⟩
    have key := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) F
      (fun m : ℕ => ENNReal.ofReal (8 * (1 / ((m : ℝ) + 1)))) htend
      (fun m i => closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1)))) hdiam hcover
    refine key.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
    calc ∑' i : u m, ediam (closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1)))) ^ (n : ℝ)
        ≤ ∑' i : u m, 8 ^ n * (ν (closedBall (i : Euclidean N) (r i (1 / ((m : ℝ) + 1)))) * s⁻¹) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have hiν := hrν i (huF m i.2) _ (hδ m)
          have hd : ediam (closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1)))) ≤
              ENNReal.ofReal (8 * r i (1 / ((m : ℝ) + 1))) := by
            refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
            rw [mem_closedBall] at hx hy
            linarith [dist_triangle_right x y (i : Euclidean N)]
          calc ediam (closedBall (i : Euclidean N) (4 * r i (1 / ((m : ℝ) + 1)))) ^ (n : ℝ)
              ≤ ENNReal.ofReal (8 * r i (1 / ((m : ℝ) + 1))) ^ (n : ℝ) :=
                ENNReal.rpow_le_rpow hd (Nat.cast_nonneg n)
            _ = 8 ^ n * ENNReal.ofReal (r i (1 / ((m : ℝ) + 1))) ^ n := by
                rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul (by norm_num), mul_pow,
                  ENNReal.ofReal_ofNat]
            _ ≤ 8 ^ n * (ν (closedBall (i : Euclidean N) (r i (1 / ((m : ℝ) + 1)))) * s⁻¹) := by
                gcongr
                calc ENNReal.ofReal (r i (1 / ((m : ℝ) + 1))) ^ n
                    = s⁻¹ * (s * ENNReal.ofReal (r i (1 / ((m : ℝ) + 1))) ^ n) := by
                      rw [← mul_assoc, ENNReal.inv_mul_cancel hs0 hstop, one_mul]
                  _ ≤ s⁻¹ * ν (closedBall (i : Euclidean N) (r i (1 / ((m : ℝ) + 1)))) := by
                      gcongr
                  _ = ν (closedBall (i : Euclidean N) (r i (1 / ((m : ℝ) + 1)))) * s⁻¹ :=
                      mul_comm _ _
      _ = 8 ^ n * ((∑' i : u m, ν (closedBall (i : Euclidean N) (r i (1 / ((m : ℝ) + 1))))) *
            s⁻¹) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ ≤ 8 ^ n * (ν univ * s⁻¹) := by
          gcongr
          exact (measure_biUnion (huc m) (hud m) (fun _ _ => measurableSet_closedBall)).symm.le.trans
            (measure_mono (subset_univ _))
      _ = 8 ^ n * ν univ * s⁻¹ := (mul_assoc _ _ _).symm
  -- Simon 3.6 for a measure `ν` with `ν(A) < ∞`.
  have hC : ∀ ν : Measure (Euclidean N), ν A ≠ ∞ →
      ∀ᵐ x ∂(μH[(n : ℝ)] : Measure (Euclidean N)), x ∉ A → HasDensity n (ν.restrict A) x 0 := by
    intro ν hνA
    have : IsFiniteMeasure (ν.restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hνA.lt_top⟩
    -- Closed sets `K j ⊆ A` with `ν(A ∖ K j) < 1/j`.
    have hK : ∀ j : ℕ, ∃ K ⊆ A, IsClosed K ∧ ν.restrict A (A \ K) < (j : ℝ≥0∞)⁻¹ := fun j =>
      hA.exists_isClosed_sdiff_lt (measure_ne_top _ _) (by simp)
    choose K hKA hKc hKν using hK
    -- The set where the density ratio exceeds `1/(k+1)` for arbitrarily small radii is null.
    have hS : ∀ k : ℕ, μH[(n : ℝ)] {x | x ∉ A ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        ((k : ℝ≥0∞) + 1)⁻¹ < densityRatio n (ν.restrict A) x ρ} = 0 := by
      intro k
      have hs0 : ((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n ≠ 0 := mul_ne_zero (by simp) hω0
      have hstop : ((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n ≠ ∞ :=
        ENNReal.mul_ne_top (by simp) hωtop
      have hbound : ∀ j : ℕ, μH[(n : ℝ)] {x | x ∉ A ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
          ((k : ℝ≥0∞) + 1)⁻¹ < densityRatio n (ν.restrict A) x ρ} ≤
            8 ^ n * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹ * (j : ℝ≥0∞)⁻¹ := by
        intro j
        refine (hcov (ν.restrict (A \ K j)) _ _ hs0 hstop ?_).trans ?_
        · rintro x ⟨hxA, hfreq⟩ δ hδ
          obtain ⟨r, hr, hrK⟩ :=
            Metric.isOpen_iff.mp (hKc j).isOpen_compl x (fun hx => hxA (hKA j hx))
          obtain ⟨ρ, hρlt, hρI⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hr))).exists
          refine ⟨ρ, hρI.1, hρI.2.trans_le (min_le_left _ _), ?_⟩
          have hden0 : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
            mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hρI.1).ne')
          have hdentop : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
            ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          rw [densityRatio, ENNReal.lt_div_iff_mul_lt (Or.inl hden0) (Or.inl hdentop)] at hρlt
          have hball : closedBall x ρ ∩ (A \ K j) = closedBall x ρ ∩ A := by
            ext y
            constructor
            · exact fun h => ⟨h.1, h.2.1⟩
            · intro h
              exact ⟨h.1, h.2, hrK (closedBall_subset_ball (hρI.2.trans_le (min_le_right _ _)) h.1)⟩
          rw [Measure.restrict_apply measurableSet_closedBall, hball,
            ← Measure.restrict_apply measurableSet_closedBall, mul_assoc]
          exact hρlt.le
        · rw [Measure.restrict_apply_univ]
          have hνj : ν (A \ K j) ≤ (j : ℝ≥0∞)⁻¹ := by
            have h := (hKν j).le
            rwa [Measure.restrict_apply (hA.diff (hKc j).measurableSet),
              inter_eq_left.mpr sdiff_subset] at h
          calc 8 ^ n * ν (A \ K j) * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹
              = 8 ^ n * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹ * ν (A \ K j) := by ring
            _ ≤ 8 ^ n * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹ * (j : ℝ≥0∞)⁻¹ := by gcongr
      have hlim : Tendsto (fun j : ℕ => 8 ^ n * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹ *
          (j : ℝ≥0∞)⁻¹) atTop (𝓝 (8 ^ n * (((k : ℝ≥0∞) + 1)⁻¹ * unitBallVolume n)⁻¹ * 0)) :=
        ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.inv_ne_top.mpr hs0)))
      rw [mul_zero] at hlim
      exact nonpos_iff_eq_zero.mp (ge_of_tendsto' hlim hbound)
    rw [ae_iff]
    refine measure_mono_null ?_ (measure_iUnion_null hS)
    intro x hx
    simp only [mem_ofPred_eq, not_imp] at hx
    obtain ⟨hxA, hnot⟩ := hx
    rw [HasDensity, ENNReal.tendsto_nhds_zero] at hnot
    simp only [not_forall, Filter.not_eventually, not_le, exists_prop] at hnot
    obtain ⟨ε, hε, hfreq⟩ := hnot
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.mpr ⟨k, hxA, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
      _ < ε := hk
      _ < densityRatio n (ν.restrict A) x ρ := hρ
  -- Countable cover of `U` by closed balls whose doubles lie in `U`.
  obtain ⟨F, hFc, hFgood, hFcover⟩ : ∃ F : Set (Euclidean N × ℝ), F.Countable ∧
      (∀ p ∈ F, 0 < p.2 ∧ closedBall p.1 (2 * p.2) ⊆ U) ∧ U ⊆ ⋃ p ∈ F, closedBall p.1 p.2 := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euclidean N)
    refine ⟨{p | p ∈ D ×ˢ range ((↑) : ℚ → ℝ) ∧ 0 < p.2 ∧ closedBall p.1 (2 * p.2) ⊆ U},
      (hDc.prod (countable_range _)).mono fun p hp => hp.1, fun p hp => hp.2, ?_⟩
    intro y hy
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (div_pos hε (by norm_num : (0 : ℝ) < 3))
    obtain ⟨c, hcD, hc⟩ := hDd.exists_dist_lt y hq0
    refine mem_iUnion₂.mpr ⟨(c, (q : ℝ)), ⟨⟨hcD, q, rfl⟩, hq0, ?_⟩, ?_⟩
    · intro z hz
      apply hεU
      rw [mem_ball]
      rw [mem_closedBall] at hz
      have h1 := dist_triangle z c y
      rw [dist_comm] at hc
      simp only at hz
      linarith
    · rw [mem_closedBall]
      exact hc.le
  -- Localize on each ball and combine countably many null sets.
  have hball : ∀ p ∈ F, ∀ᵐ x ∂(μH[(n : ℝ)] : Measure (Euclidean N)), x ∉ A →
      HasDensity n ((μ.restrict (closedBall p.1 (2 * p.2))).restrict A) x 0 := by
    intro p hp
    apply hC
    rw [Measure.restrict_apply hA]
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) (hFgood p hp).2)
      (measure_mono inter_subset_right)
  filter_upwards [(ae_ball_iff hFc).mpr hball] with x hx hxU hxA
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ F, x ∈ closedBall p.1 p.2 := by
    simpa only [mem_iUnion, exists_prop] using hFcover hxU
  have hpos : 0 < p.2 := (hFgood p hp).1
  refine (hx p hp hxA).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hpos] with ρ hρ
  have hsub : closedBall x ρ ⊆ closedBall p.1 (2 * p.2) := by
    apply closedBall_subset_closedBall'
    rw [mem_closedBall] at hxp
    linarith [hρ.2]
  simp only [densityRatio]
  rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall,
    Measure.restrict_apply (measurableSet_closedBall.inter hA),
    inter_eq_left.mpr (inter_subset_left.trans hsub)]
/-- Borel measurability of the upper and lower `n`-densities of an s-finite measure and of each
level set `{x | Θ^n(μ, x) = c}` (Simon Ch. 1, 3.2; used in Ch. 8 for `μ = μ_V`, which need not be
locally finite near `∂U`). -/
theorem Submission.intcpt_id_measurable_densities :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) [SFinite μ], Measurable (fun x ↦ limsup (densityRatio n μ x) (𝓝[>] 0)) ∧ Measurable (fun x ↦ liminf (densityRatio n μ x) (𝓝[>] 0)) ∧ ∀ c : ℝ≥0∞, MeasurableSet {x | HasDensity n μ x c} := by
  intro N n μ _
  -- `ω_n < ∞`, so `ψ(ρ) = ω_n ρ^n` is finite and continuous in `ρ`.
  have hω : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have hψ : Continuous fun ρ : ℝ ↦ unitBallVolume n * ENNReal.ofReal ρ ^ n :=
    (ENNReal.continuous_const_mul hω).comp
      ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal)
  -- Step 1: for a fixed radius, `x ↦ μ(B̄_ρ(x)) / (ω_n ρ^n)` is Borel (sections of the closed set
  -- `{(x, y) | dist y x ≤ ρ}` under the s-finite measure `μ`).
  have hfix : ∀ ρ : ℝ, Measurable fun x ↦ densityRatio n μ x ρ := by
    intro ρ
    have hs : MeasurableSet {p : Euclidean N × Euclidean N | dist p.2 p.1 ≤ ρ} :=
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
    exact (measurable_measure_prodMk_left (ν := μ) hs).div_const _
  -- Step 2: `μ(B̄_ρ(x)) / ψ(q) → μ(B̄_ρ(x)) / ψ(ρ)` as `q → ρ` (`ψ(ρ) < ∞`, so this holds even
  -- when `μ(B̄_ρ(x)) = ∞`).
  have htend : ∀ (x : Euclidean N) (ρ : ℝ), Tendsto
      (fun q : ℝ ↦ μ (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal q ^ n)) (𝓝 ρ)
      (𝓝 (densityRatio n μ x ρ)) := fun x ρ ↦
    ENNReal.Tendsto.const_div (hψ.tendsto ρ)
      (Or.inl (ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)))
  -- Step 2(a): the supremum over radii in `(0, δ)` equals the supremum over rational radii.
  have hsup : ∀ (x : Euclidean N) (δ : ℝ), ⨆ ρ ∈ Ioo 0 δ, densityRatio n μ x ρ =
      ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), densityRatio n μ x q := by
    intro x δ
    refine le_antisymm (iSup₂_le fun ρ hρ ↦ not_lt.1 fun hlt ↦ ?_)
      (iSup₂_le fun q hq ↦
        le_iSup₂ (f := fun ρ (_ : ρ ∈ Ioo 0 δ) ↦ densityRatio n μ x ρ) (q : ℝ) hq)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((htend x ρ).eventually_const_lt hlt)
    obtain ⟨q, hρq, hqδ⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right ρ hε) hρ.2)
    have hq : (q : ℝ) ∈ Ioo 0 δ := ⟨hρ.1.trans hρq, (lt_min_iff.1 hqδ).2⟩
    have hdist : dist (q : ℝ) ρ < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [(lt_min_iff.1 hqδ).1]
    have hmono : μ (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal q ^ n) ≤
        densityRatio n μ x q :=
      ENNReal.div_le_div_right (measure_mono (closedBall_subset_closedBall hρq.le)) _
    have hle : densityRatio n μ x q ≤ ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), densityRatio n μ x q :=
      le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ) ↦ densityRatio n μ x q) q hq
    exact lt_irrefl _ ((hball hdist).trans_le (hmono.trans hle))
  -- Step 2(b): the infimum over radii in `(0, δ)` equals the infimum over rational radii.
  have hinf : ∀ (x : Euclidean N) (δ : ℝ), ⨅ ρ ∈ Ioo 0 δ, densityRatio n μ x ρ =
      ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), densityRatio n μ x q := by
    intro x δ
    refine le_antisymm
      (le_iInf₂ fun q hq ↦
        iInf₂_le (f := fun ρ (_ : ρ ∈ Ioo 0 δ) ↦ densityRatio n μ x ρ) (q : ℝ) hq)
      (le_iInf₂ fun ρ hρ ↦ not_lt.1 fun hlt ↦ ?_)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((htend x ρ).eventually_lt_const hlt)
    obtain ⟨q, hq0, hqρ⟩ := exists_rat_btwn (max_lt (sub_lt_self ρ hε) hρ.1)
    have hq : (q : ℝ) ∈ Ioo 0 δ := ⟨(max_lt_iff.1 hq0).2, hqρ.trans hρ.2⟩
    have hdist : dist (q : ℝ) ρ < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [(max_lt_iff.1 hq0).1]
    have hmono : densityRatio n μ x q ≤
        μ (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal q ^ n) :=
      ENNReal.div_le_div_right (measure_mono (closedBall_subset_closedBall hqρ.le)) _
    have hle : ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), densityRatio n μ x q ≤ densityRatio n μ x q :=
      iInf₂_le (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ) ↦ densityRatio n μ x q) q hq
    exact lt_irrefl _ ((hball hdist).trans_le (hle.trans hmono))
  -- Step 3: `limsup` and `liminf` along `𝓝[>] 0` through the basis `(0, 1/(m+1))`, `m ∈ ℕ`, are
  -- countable infima/suprema of the fixed-radius ratios at rational radii.
  have hbasis : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ ↦ True) (fun m ↦ Ioo 0 (1 / ((m : ℝ) + 1))) :=
    (nhdsGT_basis (0 : ℝ)).to_hasBasis
      (fun u hu ↦ (exists_nat_one_div_lt hu).imp fun m hm ↦ ⟨trivial, Ioo_subset_Ioo_right hm.le⟩)
      (fun m _ ↦ ⟨1 / ((m : ℝ) + 1), Nat.one_div_pos_of_nat, subset_rfl⟩)
  have hlimsup : Measurable fun x ↦ limsup (densityRatio n μ x) (𝓝[>] 0) := by
    have heq : (fun x ↦ limsup (densityRatio n μ x) (𝓝[>] 0)) = fun x ↦
        ⨅ m : ℕ, ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (1 / ((m : ℝ) + 1))), densityRatio n μ x q := by
      funext x
      rw [hbasis.limsup_eq_iInf_iSup]
      simp only [iInf_true, hsup]
    rw [heq]
    exact Measurable.iInf fun m ↦ Measurable.iSup fun q ↦ Measurable.iSup fun _ ↦ hfix q
  have hliminf : Measurable fun x ↦ liminf (densityRatio n μ x) (𝓝[>] 0) := by
    have heq : (fun x ↦ liminf (densityRatio n μ x) (𝓝[>] 0)) = fun x ↦
        ⨆ m : ℕ, ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (1 / ((m : ℝ) + 1))), densityRatio n μ x q := by
      funext x
      rw [hbasis.liminf_eq_iSup_iInf]
      simp only [iSup_true, hinf]
    rw [heq]
    exact Measurable.iSup fun m ↦ Measurable.iInf fun q ↦ Measurable.iInf fun _ ↦ hfix q
  -- Step 4: `Θ^n(μ, x) = c` iff the upper and lower densities both equal `c`.
  refine ⟨hlimsup, hliminf, fun c ↦ ?_⟩
  have heq : {x | HasDensity n μ x c} =
      (fun x ↦ limsup (densityRatio n μ x) (𝓝[>] 0)) ⁻¹' {c} ∩
        (fun x ↦ liminf (densityRatio n μ x) (𝓝[>] 0)) ⁻¹' {c} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, HasDensity]
    exact ⟨fun h ↦ ⟨h.limsup_eq, h.liminf_eq⟩, fun h ↦ tendsto_of_liminf_eq_limsup h.2 h.1⟩
  rw [heq]
  exact (hlimsup (measurableSet_singleton c)).inter (hliminf (measurableSet_singleton c))

/-- **Simon Ch. 8, Remark 5.9** (step B0 of 5.9, for one varifold): an integral varifold has
integer density `Θ^n(μ_V, x) ≥ 1` at `μ_V`-a.e. `x`.  Write `V = v(M, θ)`, `ν = θ H^n ⌞ M` and
`μ_V = ν ⌞ T` for a Borel hull `T` of the tangent-point set `M_*` (`intcpt_id_weight_hull`).  At
`x ∈ M_*`, `Θ^n(ν, x) = θ(x)` (Ch. 3, Remark 1.8(2): `intcpt_id_tangent_point_density`), and off an
`H^n`-null set `Θ^n(ν ⌞ Tᶜ, x) = 0` (Ch. 1, 3.6: `intcpt_id_restrict_density_zero_ae`) and
`θ(x) ∈ ℕ`; hence `Θ^n(μ_V, x) = θ(x) ∈ {1, 2, …}` for `H^n`-a.e. `x ∈ M_*`.  The set where the
conclusion fails is Borel (`intcpt_id_measurable_densities`), so its `μ_V`-measure is the integral
of `θ` over an `H^n`-null subset of `M_*`, i.e. `0`. -/
theorem Submission.intcpt_integral_density_integer :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), IsIntegral V → ∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ HasDensity n V.weight x (k : ℝ≥0∞) := by
  intro N n U V hV
  -- Step 1: `V = v(M, θ)` with `θ ∈ ℕ` `H^n`-a.e. on `M`, and `μ_V = ν ⌞ T` with `M_* ⊆ T` Borel
  -- (sibling `intcpt_id_weight_hull`).
  obtain ⟨M, θ, hVM, hint⟩ := hV
  obtain ⟨T, hT, hMT, hweight, hformula⟩ := Submission.intcpt_id_weight_hull N n U V M θ hVM
  obtain ⟨hMU, hMnull, -, hθpos, hθint, -⟩ := hVM
  set Mstar : Set (Euclidean N) := {x | x ∈ M ∧ ∃ S : Grassmannian N n,
    Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane}
  set ν : Measure (Euclidean N) := ((μHE[n] : Measure (Euclidean N)).restrict M).withDensity
    fun x ↦ ENNReal.ofReal (θ x) with hν
  -- `ν(K) = ∫_{M ∩ K} θ dH^n < ∞` for compact `K ⊆ U`.
  have hνK : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → ν K ≠ ∞ := by
    intro K hK hKU
    rw [hν, withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_comm]
    exact (hθint K hK hKU).lintegral_lt_top.ne
  -- Step 2 (Ch. 1, 3.6): `Θ^n(ν ⌞ Tᶜ, x) = 0` for `H^n`-a.e. `x ∈ U ∩ T`
  -- (sibling `intcpt_id_restrict_density_zero_ae`).
  have hzero := Submission.intcpt_id_restrict_density_zero_ae N n ν U Tᶜ V.isOpen_domain hνK
    hT.compl
  -- Step 3: `θ(x) ∈ ℕ` for `H^n`-a.e. `x ∈ M` (`M` need not be measurable here).
  have hintAE : ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)), x ∈ M → ∃ k : ℕ, θ x = k := by
    rw [ae_iff] at hint ⊢
    refine measure_mono_null (fun x hx ↦ ?_)
      (nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply _ _).trans hint.le))
    simp only [mem_ofPred_eq, not_imp] at hx
    exact ⟨hx.2, hx.1⟩
  -- Step 4: the target set `P = {x | ∃ k ≥ 1, Θ^n(μ_V, x) = k}` is Borel
  -- (sibling `intcpt_id_measurable_densities`; `μ_V` is σ-finite).
  set P : Set (Euclidean N) := {x | ∃ k : ℕ, 1 ≤ k ∧ HasDensity n V.weight x (k : ℝ≥0∞)} with hP
  have hPmeas : MeasurableSet P := by
    have hPeq : P = ⋃ k : ℕ, ({_x : Euclidean N | 1 ≤ k} ∩
        {x | HasDensity n V.weight x (k : ℝ≥0∞)}) := by
      ext x
      simp [hP]
    rw [hPeq]
    exact MeasurableSet.iUnion fun k ↦ (MeasurableSet.const _).inter
      ((Submission.intcpt_id_measurable_densities N n V.weight).2.2 _)
  -- Step 5: `Θ^n(μ_V, x) = θ(x) ∈ {1, 2, …}` at `H^n`-a.e. `x ∈ M_*`.
  have hkey : ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)), x ∈ Mstar → x ∈ P := by
    filter_upwards [hzero, hintAE] with x hx0 hxint hxMstar
    obtain ⟨hxM, S, hS⟩ := hxMstar
    obtain ⟨k, hk⟩ := hxint hxM
    -- (a) `Θ^n(ν, x) = θ(x)` (Ch. 3, Remark 1.8(2): sibling `intcpt_id_tangent_point_density`),
    -- with `θ` integrable on `M ∩ B_{ε/2}(x)` for a closed ball `B_{ε/2}(x) ⊆ U`.
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp V.isOpen_domain x (hMU hxM)
    have hcl : closedBall x (ε / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hball
    have hdens := Submission.intcpt_id_tangent_point_density N n M θ x S.plane (ε / 2) hMnull
      (fun y hy ↦ (hθpos y hy).le) hxM (by linarith)
      (hθint _ (isCompact_closedBall x (ε / 2)) hcl) hS
    -- (b) `Θ^n(ν ⌞ Tᶜ, x) = 0`, since `x ∈ M_* ⊆ T`.
    have hxT : x ∈ T := hMT ⟨hxM, S, hS⟩
    have h0 : HasDensity n (ν.restrict Tᶜ) x 0 := hx0 (hMU hxM) (fun h ↦ h hxT)
    -- (c) `ν = μ_V + ν ⌞ Tᶜ`, so the density ratios add and `Θ^n(μ_V, x) = θ(x) - 0`.
    have hsplit : ν = V.weight + ν.restrict Tᶜ := by
      rw [hweight, Measure.restrict_add_restrict_compl hT]
    have hadd : ∀ ρ, densityRatio n ν x ρ =
        densityRatio n V.weight x ρ + densityRatio n (ν.restrict Tᶜ) x ρ := by
      intro ρ
      simp only [densityRatio]
      conv_lhs => rw [hsplit]
      rw [Measure.add_apply, ENNReal.add_div]
    have hW : HasDensity n V.weight x (ENNReal.ofReal (θ x)) := by
      have h1 := ENNReal.Tendsto.sub hdens h0 (Or.inl ENNReal.ofReal_ne_top)
      rw [tsub_zero] at h1
      unfold HasDensity
      refine h1.congr' ?_
      have hfin : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), densityRatio n (ν.restrict Tᶜ) x ρ ≠ ∞ :=
        h0.eventually (eventually_ne_nhds ENNReal.zero_ne_top)
      filter_upwards [hfin] with ρ hρ
      rw [hadd ρ, ENNReal.add_sub_cancel_right hρ]
    -- (d) `θ(x) = k` with `k ≥ 1`, as `θ > 0` on `M`.
    refine ⟨k, ?_, ?_⟩
    · have hpos := hθpos x hxM
      rw [hk] at hpos
      exact_mod_cast hpos
    · rwa [hk, ENNReal.ofReal_natCast] at hW
  -- Step 6: `μ_V(Pᶜ) = ∫_{M_* ∩ Pᶜ} θ dH^n = 0`, as `P` is Borel and `H^n(M_* ∩ Pᶜ) = 0`.
  rw [ae_iff]
  change V.weight Pᶜ = 0
  rw [hformula _ hPmeas.compl]
  have hnull : (μHE[n] : Measure (Euclidean N)) (Mstar ∩ Pᶜ) = 0 := by
    rw [ae_iff] at hkey
    refine measure_mono_null (fun x hx ↦ ?_) hkey
    simp only [mem_ofPred_eq, not_imp]
    exact ⟨hx.1, hx.2⟩
  rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
/-- Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(z,S) = g(z)`):
if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`,
`t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` as `t ↓ 0`. -/
theorem Submission.intcpt_canon_weight_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂V.weight) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n])) := by
  intro N n U V x T θ hT g
  -- Step 1: `f(z, S) := g(z)` is compactly supported, `G(N,n)` being compact.
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
/-- `H^n` of a closed disc in an `n`-plane (step 3 of the canonical-representation proof for
Simon Ch. 8, 5.9): for `T ∈ G(N,n)` and `r ≥ 0`, `H^n(T ∩ B_r(0)) = ω_n r^n`, because `T.plane` is
an `n`-dimensional inner product space, isometrically included in `ℝ^N`, on which `μHE[n]` is
Lebesgue measure. -/
theorem Submission.intcpt_canon_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: `dim T.plane = n`.
  have hP : Module.finrank ℝ T.plane = n := T.finrank_plane
  -- Step 2: `T.plane ∩ B_r(0)` is the image of the closed `r`-ball of `T.plane` under the inclusion.
  have himage : (T.plane : Set (Euclidean N)) ∩ closedBall 0 r =
      ((↑) : T.plane → Euclidean N) '' closedBall (0 : T.plane) r := by
    ext z
    constructor
    · rintro ⟨hz, hzr⟩
      exact ⟨⟨z, hz⟩, by simpa using hzr, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by simpa using hw⟩
  -- Steps 3–5: the inclusion is an isometry, `μHE[finrank T.plane] = volume` on `T.plane`, and
  -- Haar scaling gives `volume (B_r(0)) = ofReal (r ^ n) * volume (ball 0 1)`.
  have hvol : (μHE[n] : Measure T.plane) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := T.plane)
    rwa [hP] at h
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hvol,
    Measure.addHaar_closedBall volume (0 : T.plane) hr, hP]
  -- Step 6: a linear isometry `T.plane ≃ ℝ^n` carries `volume (ball 0 1)` to `ω_n`.
  have hball : (volume : Measure T.plane) (ball 0 1) = unitBallVolume n := by
    let e : T.plane ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((stdOrthonormalBasis ℝ T.plane).reindex (finCongr hP)).repr
    have hpre : e ⁻¹' ball 0 1 = ball (0 : T.plane) 1 := by
      ext w
      simp [e]
    rw [unitBallVolume, ← hpre,
      e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]
  -- Step 7: `ofReal (r ^ n) = ofReal r ^ n`.
  rw [hball, ENNReal.ofReal_pow hr, mul_comm]

/-- Tangent planes force densities (step 3 of the canonical-representation proof for Simon Ch. 8,
5.9): if `V` has tangent plane `T` with multiplicity `θ` at `x` (Definition 1.1), then
`Θ^n(μ_V, x) = θ`, i.e. `μ_V(B_ρ(x)) / (ω_n ρ^n) → θ` as `ρ ↓ 0`.  Radial cut-offs in `C_c`
squeeze `1_{B_ρ(x)}`, the weight blow-up gives their limits, and `H^n` of discs in `T` bounds them. -/
theorem Submission.intcpt_canon_tangent_plane_hasDensity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → HasDensity n V.weight x (ENNReal.ofReal θ) := by
  intro N n U V x T θ hT
  -- Step 0: `ω_n ∈ (0, ∞)`; write `w := ω_n.toReal > 0`.
  have hω0 : 0 < unitBallVolume n := measure_ball_pos _ _ one_pos
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hw : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0.ne' hω
  -- Step 1: `θ > 0`, and a radius `δ > 0` with `B_δ(x) ⊆ U`, so that `μ_V(B_δ(x)) < ∞`.
  have hθ : 0 < θ := hT.2.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hT.1
  have hδ : 0 < r / 2 := half_pos hr
  have hfin : V.weight (closedBall x (r / 2)) ≠ ∞ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x (r / 2))
      ((closedBall_subset_ball (half_lt_self hr)).trans hball)
  have hA := Submission.intcpt_canon_weight_blowup_tendsto N n U V x T θ hT
  have hB := Submission.intcpt_canon_plane_closedBall_hausdorff N n T
  generalize r / 2 = δ at hδ hfin
  generalize V.weight = μ at hfin hA ⊢
  have hnorm : ∀ {t : ℝ}, 0 < t → ∀ z : Euclidean N, ‖t⁻¹ • (z - x)‖ = t⁻¹ * dist z x := by
    intro t ht z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), dist_eq_norm]
  -- Step 2: the radial cut-offs `χ_{a,c}(y) = min(1, max(0, (c - ‖y‖)/(c - a)))`, which lie in
  -- `C_c(ℝ^N, ℝ)` when `a < c`.
  obtain ⟨χ, χ_cont, χ_nonneg, χ_le_one, χ_eq_one, χ_eq_zero⟩ :
      ∃ χ : ℝ → ℝ → Euclidean N → ℝ, (∀ a c, Continuous (χ a c)) ∧ (∀ a c y, 0 ≤ χ a c y) ∧
        (∀ a c y, χ a c y ≤ 1) ∧ (∀ a c, a < c → ∀ y, ‖y‖ ≤ a → χ a c y = 1) ∧
        (∀ a c, a < c → ∀ y, c ≤ ‖y‖ → χ a c y = 0) := by
    refine ⟨fun a c y ↦ min 1 (max 0 ((c - ‖y‖) / (c - a))), fun a c ↦ by fun_prop,
      fun a c y ↦ le_min zero_le_one (le_max_left _ _), fun a c y ↦ min_le_left _ _, ?_, ?_⟩
    · intro a c hac y hy
      have h1 : 1 ≤ (c - ‖y‖) / (c - a) := by
        rw [le_div_iff₀ (sub_pos.2 hac)]
        linarith
      exact min_eq_left (le_max_of_le_right h1)
    · intro a c hac y hy
      have h0 : (c - ‖y‖) / (c - a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      show min 1 (max 0 ((c - ‖y‖) / (c - a))) = 0
      rw [max_eq_left h0]
      exact min_eq_right zero_le_one
  obtain ⟨G, hG⟩ : ∃ G : ∀ a c : ℝ, a < c → C_c(Euclidean N, ℝ),
      ∀ a c (hac : a < c) y, G a c hac y = χ a c y :=
    ⟨fun a c hac ↦ ⟨⟨χ a c, χ_cont a c⟩, HasCompactSupport.intro (isCompact_closedBall 0 c)
      fun y hy ↦ χ_eq_zero a c hac y (by
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le)⟩, fun _ _ _ _ ↦ rfl⟩
  -- Step 3(c): on the plane, `∫_T 1_{B_r(0)} dH^n = w r^n` (by the disc measure `ω_n r^n`).
  have h3c : ∀ {r : ℝ}, 0 ≤ r →
      Integrable ((closedBall (0 : Euclidean N) r).indicator (fun _ ↦ (1 : ℝ)))
        ((μHE[n] : Measure (Euclidean N)).restrict T.plane) ∧
      ∫ y in (T.plane : Set (Euclidean N)), (closedBall (0 : Euclidean N) r).indicator
        (fun _ ↦ (1 : ℝ)) y ∂μHE[n] = (unitBallVolume n).toReal * r ^ n := by
    intro r hr
    have hmeas : ((μHE[n] : Measure (Euclidean N)).restrict T.plane) (closedBall 0 r) =
        unitBallVolume n * ENNReal.ofReal r ^ n := by
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hB r hr]
    have hfin' : ((μHE[n] : Measure (Euclidean N)).restrict T.plane) (closedBall 0 r) ≠ ∞ := by
      rw [hmeas]
      exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    refine ⟨(integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin'), ?_⟩
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      measureReal_def, hmeas, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  -- Step 3(d): `χ_{a,c}` is `H^n ⌞ T`-integrable, being dominated by `1_{B_c(0)}`.
  have h3d : ∀ {a c : ℝ}, a < c → 0 ≤ c →
      Integrable (χ a c) ((μHE[n] : Measure (Euclidean N)).restrict T.plane) := by
    intro a c hac hc
    refine (h3c hc).1.mono' (χ_cont a c).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (χ_nonneg _ _ _)]
    by_cases hy : y ∈ closedBall (0 : Euclidean N) c
    · rw [indicator_of_mem hy]
      exact χ_le_one _ _ _
    · rw [indicator_of_notMem hy]
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact (χ_eq_zero a c hac y hy.le).le
  -- Step 3(a): `z ↦ χ_{a,c}(t⁻¹ • (z - x))` is `μ_V`-integrable once `t c ≤ δ`, being dominated
  -- by `1_{B_δ(x)}`.
  have h3a : ∀ {a c t : ℝ}, a < c → 0 < t → t * c ≤ δ →
      Integrable (fun z ↦ χ a c (t⁻¹ • (z - x))) μ := by
    intro a c t hac ht htc
    have hind : Integrable ((closedBall x δ).indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin)
    refine hind.mono' ((χ_cont a c).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (χ_nonneg _ _ _)]
    by_cases hz : z ∈ closedBall x δ
    · rw [indicator_of_mem hz]
      exact χ_le_one _ _ _
    · rw [indicator_of_notMem hz]
      rw [mem_closedBall, not_le] at hz
      refine (χ_eq_zero a c hac _ ?_).le
      rw [hnorm ht, le_inv_mul_iff₀ ht]
      linarith
  -- Step 3(b): for `t ≤ δ`, `1_{B_t(x)}` is `μ_V`-integrable with integral `μ_V(B_t(x))`.
  have h3b : ∀ {t : ℝ}, t ≤ δ →
      Integrable ((closedBall x t).indicator (fun _ ↦ (1 : ℝ))) μ ∧
      ∫ z, (closedBall x t).indicator (fun _ ↦ (1 : ℝ)) z ∂μ = (μ (closedBall x t)).toReal := by
    intro t ht
    have hfin' : μ (closedBall x t) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall ht))
    refine ⟨(integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin'), ?_⟩
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one, measureReal_def]
  -- Step 4: lower bound via `g⁻ = χ_{κ,1}`: if `a < θ w κ^n` then eventually `a < b(t)`, where
  -- `b(t) = t^{-n} μ_V(B_t(x))`.
  have hlower : ∀ {κ a : ℝ}, 0 < κ → κ < 1 → a < θ * (unitBallVolume n).toReal * κ ^ n →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), a < t⁻¹ ^ n * (μ (closedBall x t)).toReal := by
    intro κ a hκ0 hκ1 ha
    obtain ⟨hint, hval⟩ := h3c hκ0.le
    have hgint := h3d hκ1 zero_le_one
    have hI : (unitBallVolume n).toReal * κ ^ n ≤
        ∫ y in (T.plane : Set (Euclidean N)), χ κ 1 y ∂μHE[n] := by
      rw [← hval]
      refine integral_mono hint hgint fun y ↦ ?_
      by_cases hy : y ∈ closedBall (0 : Euclidean N) κ
      · rw [indicator_of_mem hy]
        rw [mem_closedBall, dist_zero_right] at hy
        exact (χ_eq_one κ 1 hκ1 y hy).ge
      · rw [indicator_of_notMem hy]
        exact χ_nonneg _ _ _
    have hlt : a < θ * ∫ y in (T.plane : Set (Euclidean N)), χ κ 1 y ∂μHE[n] := by
      have h := mul_le_mul_of_nonneg_left hI hθ.le
      rw [← mul_assoc] at h
      linarith
    have hAκ := hA (G κ 1 hκ1)
    simp only [hG] at hAκ
    filter_upwards [hAκ.eventually (lt_mem_nhds hlt), Ioo_mem_nhdsGT (mul_pos hκ0 hδ)]
      with t hta ht
    have ht0 : 0 < t := ht.1
    have htδ : t ≤ δ := by nlinarith [ht.2]
    obtain ⟨hbint, hbval⟩ := h3b htδ
    have hle : ∫ z, χ κ 1 (t⁻¹ • (z - x)) ∂μ ≤ (μ (closedBall x t)).toReal := by
      rw [← hbval]
      refine integral_mono (h3a hκ1 ht0 (by linarith)) hbint fun z ↦ ?_
      by_cases hz : z ∈ closedBall x t
      · rw [indicator_of_mem hz]
        exact χ_le_one _ _ _
      · rw [indicator_of_notMem hz]
        rw [mem_closedBall, not_le] at hz
        refine (χ_eq_zero κ 1 hκ1 _ ?_).le
        rw [hnorm ht0, le_inv_mul_iff₀ ht0]
        linarith
    calc a < t⁻¹ ^ n * ∫ z, χ κ 1 (t⁻¹ • (z - x)) ∂μ := hta
      _ ≤ t⁻¹ ^ n * (μ (closedBall x t)).toReal :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (inv_nonneg.2 ht0.le) n)
  -- Step 5: upper bound via `g⁺ = χ_{1,κ⁻¹}`: if `θ w κ^{-n} < a` then eventually `b(t) < a`.
  have hupper : ∀ {κ a : ℝ}, 0 < κ → κ < 1 → θ * (unitBallVolume n).toReal * κ⁻¹ ^ n < a →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ ^ n * (μ (closedBall x t)).toReal < a := by
    intro κ a hκ0 hκ1 ha
    have hκi : 1 < κ⁻¹ := one_lt_inv_iff₀.2 ⟨hκ0, hκ1⟩
    obtain ⟨hint, hval⟩ := h3c (inv_pos.2 hκ0).le
    have hgint := h3d hκi (inv_pos.2 hκ0).le
    have hI : ∫ y in (T.plane : Set (Euclidean N)), χ 1 κ⁻¹ y ∂μHE[n] ≤
        (unitBallVolume n).toReal * κ⁻¹ ^ n := by
      rw [← hval]
      refine integral_mono hgint hint fun y ↦ ?_
      by_cases hy : y ∈ closedBall (0 : Euclidean N) κ⁻¹
      · rw [indicator_of_mem hy]
        exact χ_le_one _ _ _
      · rw [indicator_of_notMem hy]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact (χ_eq_zero 1 κ⁻¹ hκi y hy.le).le
    have hlt : θ * ∫ y in (T.plane : Set (Euclidean N)), χ 1 κ⁻¹ y ∂μHE[n] < a := by
      have h := mul_le_mul_of_nonneg_left hI hθ.le
      rw [← mul_assoc] at h
      linarith
    have hAκ := hA (G 1 κ⁻¹ hκi)
    simp only [hG] at hAκ
    filter_upwards [hAκ.eventually (gt_mem_nhds hlt), Ioo_mem_nhdsGT (mul_pos hκ0 hδ)]
      with t hta ht
    have ht0 : 0 < t := ht.1
    have htδ : t ≤ δ := by nlinarith [ht.2]
    have htc : t * κ⁻¹ ≤ δ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hκ0]
      linarith [ht.2]
    obtain ⟨hbint, hbval⟩ := h3b htδ
    have hle : (μ (closedBall x t)).toReal ≤ ∫ z, χ 1 κ⁻¹ (t⁻¹ • (z - x)) ∂μ := by
      rw [← hbval]
      refine integral_mono hbint (h3a hκi ht0 htc) fun z ↦ ?_
      by_cases hz : z ∈ closedBall x t
      · rw [indicator_of_mem hz]
        refine (χ_eq_one 1 κ⁻¹ hκi _ ?_).ge
        rw [mem_closedBall] at hz
        rw [hnorm ht0, inv_mul_le_iff₀ ht0]
        linarith
      · rw [indicator_of_notMem hz]
        exact χ_nonneg _ _ _
    calc t⁻¹ ^ n * (μ (closedBall x t)).toReal
        ≤ t⁻¹ ^ n * ∫ z, χ 1 κ⁻¹ (t⁻¹ • (z - x)) ∂μ :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (inv_nonneg.2 ht0.le) n)
      _ < a := hta
  -- Step 6: `b(t) → θ w` along `𝓝[>] 0`, letting `κ → 1` in steps 4 and 5.
  have hb : Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * (μ (closedBall x t)).toReal) (𝓝[>] 0)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have hc : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
          (𝓝 (θ * (unitBallVolume n).toReal)) := by
        have hcont : Continuous (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) := by
          fun_prop
        simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
      obtain ⟨κ, hκa, hκ⟩ :=
        ((hc.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT one_pos)).exists
      exact hlower hκ.1 hκ.2 hκa
    · intro a ha
      have hc : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ⁻¹ ^ n) (𝓝[<] 1)
          (𝓝 (θ * (unitBallVolume n).toReal)) := by
        have hcont : ContinuousAt (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ⁻¹ ^ n) 1 := by
          fun_prop (disch := norm_num)
        simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
      obtain ⟨κ, hκa, hκ⟩ :=
        ((hc.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsLT one_pos)).exists
      exact hupper hκ.1 hκ.2 hκa
  -- Step 7: for `0 < t < δ`, `densityRatio n μ_V x t = ofReal (b(t) / w)`, and
  -- `ofReal (b(t) / w) → ofReal θ`.
  have h2 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t⁻¹ ^ n * (μ (closedBall x t)).toReal /
      (unitBallVolume n).toReal)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) := by
    have h := ENNReal.tendsto_ofReal (hb.div_const (unitBallVolume n).toReal)
    rwa [mul_div_cancel_right₀ _ hw.ne'] at h
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  have ht0 : 0 < t := ht.1
  have hmt : μ (closedBall x t) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall ht.2.le))
  have e1 : t⁻¹ ^ n * (μ (closedBall x t)).toReal / (unitBallVolume n).toReal =
      (μ (closedBall x t)).toReal / ((unitBallVolume n).toReal * t ^ n) := by
    rw [inv_pow, div_mul_eq_div_div_swap, inv_mul_eq_div]
  have e2 : unitBallVolume n * ENNReal.ofReal t ^ n =
      ENNReal.ofReal ((unitBallVolume n).toReal * t ^ n) := by
    rw [ENNReal.ofReal_mul hw.le, ENNReal.ofReal_toReal hω, ENNReal.ofReal_pow ht0.le]
  rw [e1, ENNReal.ofReal_div_of_pos (mul_pos hw (pow_pos ht0 n)), ENNReal.ofReal_toReal hmt, ← e2]
  rfl
/-- **Countable cover of an open set by open subsets of finite mass** (child
`open_cover_finite_measure` of `null_transfer`; step 2 of the supplied proof of
`intcpt_canon_hausdorff_null_of_weight_null`): if `μ` is finite on the compact subsets of an open set
`U ⊆ ℝ^N`, then `U` is covered by countably many open sets `W i ⊆ U` with `μ (W i) < ∞`.
Every `y ∈ U` has a ball `B_y = ball y r_y` with `closedBall y r_y ⊆ U`; that closed ball is compact
(`ℝ^N` is proper), so `μ B_y < ∞`.  Lindelöf (`ℝ^N` is second countable) extracts a countable
subfamily `(B_y)_{y ∈ T}` with the same union, enumerated by a surjection `ℕ → Option T`
(`none ↦ ∅`). -/
theorem Submission.intcpt_canon_nt_open_cover_finite_measure :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (U : Set (Euclidean N)), IsOpen U →
      (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) →
      ∃ W : ℕ → Set (Euclidean N), (∀ i, IsOpen (W i) ∧ W i ⊆ U ∧ μ (W i) ≠ ∞) ∧ U ⊆ ⋃ i, W i := by
  intro N μ U hU hfin
  -- Radii: `0 < r y` and `closedBall y (r y) ⊆ U` for every `y ∈ U`.
  have hr : ∀ y : U, ∃ r : ℝ, 0 < r ∧ closedBall (y : Euclidean N) r ⊆ U := fun y => by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y y.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose r hr0 hrU using hr
  -- Lindelöf: countably many of the balls `ball y (r y)` already have the full union.
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : U => ball (y : Euclidean N) (r y)) (fun _ => isOpen_ball)
  have : Countable T := hTc.to_subtype
  -- Enumerate `T` and one extra index `none`, which is sent to `∅`.
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option T)
  refine ⟨fun i => (f i).elim ∅ (fun y => ball ((y : U) : Euclidean N) (r y)), ?_, ?_⟩
  · intro i
    cases h : f i with
    | none => simp [h]
    | some y =>
      simp only [h, Option.elim_some]
      refine ⟨isOpen_ball, ball_subset_closedBall.trans (hrU y), ?_⟩
      -- `μ (ball y r) ≤ μ (closedBall y r) < ∞`, the closed ball being a compact subset of `U`.
      exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) (hrU y))
        (measure_mono ball_subset_closedBall)
  · intro x hx
    have hx' : x ∈ ⋃ y : U, ball (y : Euclidean N) (r y) :=
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr0 _)⟩
    rw [← hT] at hx'
    obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 hx'
    obtain ⟨i, hi⟩ := hf (some ⟨y, hyT⟩)
    refine mem_iUnion.2 ⟨i, ?_⟩
    simp only [hi, Option.elim_some]
    exact hxy
/-- **Open neighbourhood of small measure inside an open set of finite measure** (child
`open_subset_measure_lt` of `null_transfer`; step 4 of the supplied proof of
`intcpt_canon_hausdorff_null_of_weight_null`): if `W ⊆ ℝ^N` is open with `μ W < ∞` and `A ⊆ W` is
an arbitrary set with `μ A < ε` (outer measure), then some open `O` with `A ⊆ O ⊆ W` has
`μ O < ε`.  The restriction `μ ⌞ W` is a finite Borel measure on a metric space, hence outer regular
(`WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`); since `(μ ⌞ W) A ≤ μ A < ε`, there is
an open `O' ⊇ A` with `(μ ⌞ W) O' < ε`, and `O = O' ∩ W` has `μ O = (μ ⌞ W) O'`. -/
theorem Submission.intcpt_canon_nt_exists_open_subset_measure_lt :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (ε : ℝ≥0∞), IsOpen W →
      μ W ≠ ∞ → A ⊆ W → μ A < ε →
      ∃ O : Set (Euclidean N), IsOpen O ∧ A ⊆ O ∧ O ⊆ W ∧ μ O < ε := by
  intro N μ W A ε hW hWfin hAW hAε
  -- `μ ⌞ W` is finite, hence outer regular (`ℝ^N` is metrizable with its Borel σ-algebra).
  have : IsFiniteMeasure (μ.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hWfin.lt_top⟩
  -- Outer regularity at the arbitrary set `A`, as `(μ ⌞ W) A ≤ μ A < ε`.
  obtain ⟨O', hAO', hO', hO'ε⟩ :=
    Set.exists_isOpen_lt_of_lt A ε ((Measure.restrict_apply_le W A).trans_lt hAε)
  -- `O' ∩ W` works: `O'` is open, hence measurable, so `μ (O' ∩ W) = (μ ⌞ W) O' < ε`.
  refine ⟨O' ∩ W, hO'.inter hW, subset_inter hAO' hAW, inter_subset_right, ?_⟩
  rwa [Measure.restrict_apply hO'.measurableSet] at hO'ε
/-- Step 4 of the canonical representation in the proof of Simon Ch. 8, 5.9 (child `null_transfer`
of `canonical_representation`), via Simon Ch. 1, 3.3: let `U` be open and `μ` finite on compact
subsets of `U`.  If `Z ⊆ U` is `μ`-null and `limsup_{ρ↓0} μ(B_ρ(x)) / (ω_n ρ^n) > 0` at every
`x ∈ Z`, then `H^n(Z) = 0`.  Cover `U` by open `W_i ⊆ U` of finite mass
(`intcpt_canon_nt_open_cover_finite_measure`) and put
`Z_{i,k} = {x ∈ Z ∩ W_i : limsup ≥ 1/(k+1)}`.  For `ε > 0` there is an open `O` with
`Z_{i,k} ⊆ O ⊆ W_i` and `μ(O) < ε` (`intcpt_canon_nt_exists_open_subset_measure_lt`); on `Z_{i,k}`
the upper density of `μ` relative to `O` is that `limsup`, so Simon 3.3 gives
`(k+1)⁻¹ H^n(Z_{i,k}) ≤ μ(O) < ε`.  Hence each `Z_{i,k}`, and so `Z`, is `H^n`-null. -/
theorem Submission.intcpt_canon_hausdorff_null_of_weight_null :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (U Z : Set (Euclidean N)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → Z ⊆ U → μ Z = 0 → (∀ x ∈ Z, 0 < limsup (densityRatio n μ x) (𝓝[>] 0)) → (μHE[n] : Measure (Euclidean N)) Z = 0 := by
  intro N n μ U Z hU hfin hZU hZ hpos
  -- Step 1(a): `ω_n` is Simon's normalization `realUnitBallVolume n`, also for `n = 0`.
  have hω : unitBallVolume n = Chapter01.realUnitBallVolume (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Chapter01.realUnitBallVolume_zero, unitBallVolume,
        volume_euclideanSpace_eq_dirac (Fin 0), Measure.dirac_apply_of_mem (mem_ball_self one_pos)]
    · rw [unitBallVolume, Chapter01.volume_euclidean_ball_eq hn, ENNReal.ofReal_one, one_pow,
        mul_one]
  -- Step 1(b): Simon's `H^n` is `μHE[n]` on all sets.
  have hH : ∀ A : Set (Euclidean N),
      Chapter01.simonHausdorffOuterMeasureReal (n : ℝ) A = (μHE[n] : Measure (Euclidean N)) A := by
    intro A
    rw [← Chapter01.simonHausdorffMeasureReal_toOuterMeasure (Nat.cast_nonneg n),
      Measure.toOuterMeasure_apply,
      Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure]
  -- Step 1(c): Borel sets are Carathéodory measurable for `μ`.
  have hcar : borel (Euclidean N) ≤ μ.toOuterMeasure.caratheodory := by
    rw [← BorelSpace.measurable_eq]
    exact le_toOuterMeasure_caratheodory μ
  -- Step 2: countably many open `W_i ⊆ U` of finite mass cover `U ⊇ Z`.
  obtain ⟨W, hW, hUW⟩ := Submission.intcpt_canon_nt_open_cover_finite_measure N μ U hU hfin
  -- Step 3: `Z ⊆ ⋃_{i,k} Z_{i,k}`, as the positive `limsup` exceeds some `k⁻¹ ≥ (k+1)⁻¹`.
  have hcover : Z ⊆ ⋃ i, ⋃ k : ℕ,
      {x | x ∈ Z ∧ x ∈ W i ∧ ((k : ℝ≥0∞) + 1)⁻¹ ≤ limsup (densityRatio n μ x) (𝓝[>] 0)} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hUW (hZU hx))
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (hpos x hx).ne'
    exact mem_iUnion₂.2 ⟨i, k, hx, hi, (ENNReal.inv_le_inv.2 le_self_add).trans hk.le⟩
  refine measure_mono_null hcover (measure_iUnion_null fun i ↦ measure_iUnion_null fun k ↦ ?_)
  set A := {x | x ∈ Z ∧ x ∈ W i ∧ ((k : ℝ≥0∞) + 1)⁻¹ ≤ limsup (densityRatio n μ x) (𝓝[>] 0)}
  -- Steps 4–6: `(k+1)⁻¹ H^n(Z_{i,k}) < ε` for every `ε > 0`.
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      ((k : ℝ≥0∞) + 1)⁻¹ * (μHE[n] : Measure (Euclidean N)) A < ε := by
    intro ε hε
    -- Step 4: `μ(Z_{i,k}) = 0 < ε` gives an open `O` with `Z_{i,k} ⊆ O ⊆ W_i` and `μ(O) < ε`.
    obtain ⟨O, hO, hAO, -, hOε⟩ := Submission.intcpt_canon_nt_exists_open_subset_measure_lt N μ
      (W i) A ε (hW i).1 (hW i).2.2 (fun x hx ↦ hx.2.1)
      ((measure_mono_null (fun x hx ↦ hx.1) hZ).trans_lt hε)
    -- Step 5: on `Z_{i,k}` the upper density of `μ` relative to `O` is `limsup densityRatio`,
    -- because `O ∩ B_ρ(x) = B_ρ(x)` for small `ρ`.
    have hden : ∀ x ∈ A, ((k : ℝ≥0∞) + 1)⁻¹ ≤
        Chapter01.dimensionalUpperDensity μ.toOuterMeasure (n : ℝ) O x := by
      intro x hx
      obtain ⟨η, hη, hηO⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
      refine hx.2.2.trans_eq (limsup_congr ?_)
      filter_upwards [Ioo_mem_nhdsGT hη] with ρ hρ
      rw [Chapter01.dimensionalDensityQuotient, densityRatio, hω, ENNReal.rpow_natCast,
        inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hηO), Measure.toOuterMeasure_apply]
    -- Step 6: Simon 3.3 with `A₁ = Z_{i,k}`, `A₂ = O` and `t = (k+1)⁻¹`.
    have h33 := Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity μ.toOuterMeasure
      hcar (Nat.cast_nonneg n) A O _ hden
    rw [hH, Measure.toOuterMeasure_apply] at h33
    exact h33.trans_lt hOε
  -- Step 7: hence `(k+1)⁻¹ H^n(Z_{i,k}) = 0`, and `(k+1)⁻¹ ≠ 0`.
  have h0 : ((k : ℝ≥0∞) + 1)⁻¹ * (μHE[n] : Measure (Euclidean N)) A = 0 := by
    by_contra hne
    exact lt_irrefl _ (key _ (pos_iff_ne_zero.2 hne))
  exact (mul_eq_zero.1 h0).resolve_left (ENNReal.inv_ne_zero.2 (by simp))
/-- **Canonical representation** (step B2 of the proof of Simon Ch. 8, 5.9; child
`canonical_representation` of `integral_compactness`): let `V` have locally bounded first variation
and `Θ^n(μ_V, x) > 0` for `μ_V`-a.e. `x`, and let `M = {x ∈ spt μ_V : V has a tangent plane at x}`.
Allard's theorem (5.5 with 5.6) gives tangent planes `μ_V`-a.e., so the First Rectifiability
Theorem (1.2) gives `θ` with `V = v(M, θ)` and a tangent plane of multiplicity `θ(x)` at each
`x ∈ M`.  Such a tangent plane forces `Θ^n(μ_V, x) = θ(x)` (`intcpt_canon_tangent_plane_hasDensity`),
and as `θ > 0` on `M ⊆ U`, every `μ_V`-null `Z ⊆ M` is `H^n`-null
(`intcpt_canon_hausdorff_null_of_weight_null`, via Simon Ch. 1, 3.3). -/
theorem Submission.intcpt_canonical_tangent_representation :
    AllardRectifiabilityTheorem → FirstRectifiabilityTheorem → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 0 < θ) → ∃ θ : Euclidean N → ℝ, IsVarifoldOf V {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'} θ ∧ (∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane V x T (θ x)) ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) ∧ ∀ Z ⊆ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, V.weight Z = 0 → (μHE[n] : Measure (Euclidean N)) Z = 0 := by
  intro hAllard hFirst N n U V hV hdens
  -- Step 1: Allard (5.5 with 5.6) gives a tangent plane at `μ_V`-a.e. `x`.
  obtain ⟨-, hae⟩ := hAllard N n U V hV hdens
  -- Step 2: the First Rectifiability Theorem (1.2) gives `θ` with `V = v(M, θ)` and a tangent
  -- plane of multiplicity `θ(x)` at every `x ∈ M`; in particular `M ⊆ U` and `θ > 0` on `M`.
  obtain ⟨θ, hθT, hθM⟩ := hFirst N n U V hae
  -- Step 3: a tangent plane of multiplicity `θ(x)` forces `Θ^n(μ_V, x) = θ(x)`.
  have hden : ∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
      HasTangentPlane V x T θ'}, HasDensity n V.weight x (ENNReal.ofReal (θ x)) := by
    intro x hx
    obtain ⟨T, hT⟩ := hθT x hx
    exact Submission.intcpt_canon_tangent_plane_hasDensity N n U V x T (θ x) hT
  refine ⟨θ, hθM, fun x hx ↦ ⟨hθT x hx, hden x hx⟩, fun Z hZM hZ ↦ ?_⟩
  -- Step 4: `Z ⊆ M ⊆ U` is `μ_V`-null and `limsup_{ρ↓0} μ_V(B_ρ(x)) / (ω_n ρ^n) = θ(x) > 0` on
  -- `Z`, so Simon Ch. 1, 3.3 (through the null-transfer child) makes `Z` `H^n`-null.
  refine Submission.intcpt_canon_hausdorff_null_of_weight_null N n V.weight U Z V.isOpen_domain
    V.weight_finite_on_compact (hZM.trans hθM.1) hZ fun x hx ↦ ?_
  rw [Filter.Tendsto.limsup_eq (hden x (hZM hx))]
  exact ENNReal.ofReal_pos.2 (hθM.2.2.2.1 x (hZM hx))
/-- **Simon Ch. 8, 5.9, proof of estimate (1), Besicovitch step, p. 219** (child
`besicovitch_cover_estimate` of `liminf_ratio_bound_ae`): if every `x ∈ A` is the centre of a closed
ball `B_σ(x)`, `0 < σ < ρ₀`, with `μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν({dist(·, A) < ρ₀})`,
where `C` is the Besicovitch number of `ℝ^N` (Ch. 1, 3.12).  The covering lemma splits a subfamily
of these balls covering `A` into `C` disjoint, hence countable, subfamilies; sum the ratio bound
over each. -/
theorem Submission.intcpt_vdb_besicovitch_cover_estimate :
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
/-- **Simon Ch. 8, proof of Lemma 5.10, the Besicovitch step (p. 221)** (child `besicovitch_cover`
of `bad_set_bound`): if every `x ∈ A` is the centre of a closed ball `B_σ(x) ⊆ O`, `0 < σ ≤ R`, with
`μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν(O)`, where `C` is the Besicovitch number of `ℝ^N`
(Ch. 1, 3.12).  The covering lemma splits a subfamily of these balls covering `A` into `C`
disjoint, hence countable, subfamilies; sum the ratio bound over each. -/
theorem Submission.intcpt_allard_bsb_besicovitch_cover :
    ∀ N : ℕ, ∃ C : ℕ, ∀ (μ ν : Measure (Euclidean N)) (A O : Set (Euclidean N)) (R : ℝ)
      (t : ℝ≥0∞), (∀ x ∈ A, ∃ σ : ℝ, 0 < σ ∧ σ ≤ R ∧ closedBall x σ ⊆ O ∧
        μ (closedBall x σ) ≤ t * ν (closedBall x σ)) →
      μ A ≤ (C : ℝ≥0∞) * t * ν O := by
  intro N
  -- `C` admits no satellite configuration of `C + 1` balls in `ℝ^N`.
  obtain ⟨C, τ, hτ, hC⟩ := HasBesicovitchCovering.no_satelliteConfig (α := Euclidean N)
  refine ⟨C, fun μ ν A O R t h ↦ ?_⟩
  choose σ hσ0 hσR hσO hσ using h
  obtain ⟨s, hdisj, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hC
    { c := ((↑) : A → Euclidean N), r := fun x ↦ σ x x.2, rpos := fun x ↦ hσ0 x x.2,
      r_bound := R, r_le := fun x ↦ hσR x x.2 }
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
  have hsub : ∀ x : A, B x ⊆ O := fun x ↦ hσO x x.2
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
    _ ≤ ∑ _i : Fin C, t * ν O :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_right (measure_mono (iUnion₂_subset fun x _ ↦ hsub x)) t
    _ = (C : ℝ≥0∞) * t * ν O := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
/-- **Simon Ch. 8, proof of 5.9, estimate (1)** (child `liminf_bound_ae_of_cover` of
`liminf_ratio_bound_ae`): suppose `μ(A) ≤ C t ν_i({dist(·, A) < r})` whenever every `x ∈ A` is the
centre of a closed ball `B_σ(x)`, `0 < σ < r`, with `μ(B_σ(x)) ≤ t ν_i(B_σ(x))` (the Besicovitch
estimate), and `S = sup_i ν_i({dist(·, W) < r}) < ∞`.  Then for `μ`-a.e. `x ∈ W` there is `c` with
`liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for all `0 < ρ < r`.  For each `j`, the exceptional set lies
in the increasing union of the sets `A_i` of points with one radius `ρ` such that
`(j + 1) μ(B_ρ(x)) < ν_k(B_ρ(x))` for all `k ≥ i`; each `A_i` has measure at most
`C S / (j + 1)`, hence so does the exceptional set, which is therefore `μ`-null. -/
theorem Submission.intcpt_vdb_liminf_bound_ae_of_cover :
    ∀ (N C : ℕ) (μ : Measure (Euclidean N)) (ν : ℕ → Measure (Euclidean N))
      (W : Set (Euclidean N)) (r : ℝ),
      (∀ (A : Set (Euclidean N)) (i : ℕ) (t : ℝ≥0∞),
        (∀ x ∈ A, ∃ σ : ℝ, 0 < σ ∧ σ < r ∧ μ (closedBall x σ) ≤ t * ν i (closedBall x σ)) →
        μ A ≤ (C : ℝ≥0∞) * t * ν i (thickening r A)) →
      ⨆ i, ν i (thickening r W) ≠ ∞ →
      ∀ᵐ x ∂μ, x ∈ W → ∃ c : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < r →
        liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ (c : ℝ≥0∞) * μ (closedBall x ρ) := by
  intro N C μ ν W r hH hS
  rw [ae_iff]
  set E := {x | ¬(x ∈ W → ∃ c : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < r →
    liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ (c : ℝ≥0∞) * μ (closedBall x ρ))}
  set S := ⨆ i, ν i (thickening r W)
  have key : ∀ j : ℕ, μ E ≤ (C : ℝ≥0∞) * ((j : ℝ≥0∞) + 1)⁻¹ * S := by
    intro j
    have ha0 : (j : ℝ≥0∞) + 1 ≠ 0 := by simp
    have hatop : (j : ℝ≥0∞) + 1 ≠ ∞ := by simp
    set a : ℝ≥0∞ := (j : ℝ≥0∞) + 1
    -- `E` lies in the increasing union of the sets `A i` of points `x ∈ W` having a radius
    -- `ρ ∈ (0, r)` with `a μ(B_ρ(x)) < ν_k(B_ρ(x))` for every `k ≥ i`.
    set A : ℕ → Set (Euclidean N) := fun i ↦ {x | x ∈ W ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
      ∀ k, i ≤ k → a * μ (closedBall x ρ) < ν k (closedBall x ρ)}
    have hA : Monotone A := fun i i' hi x ⟨hxW, ρ, hρ, hρr, hk⟩ ↦
      ⟨hxW, ρ, hρ, hρr, fun k hk' ↦ hk k (hi.trans hk')⟩
    have hEA : E ⊆ ⋃ i, A i := by
      intro x hx
      simp only [E, mem_ofPred_eq, not_imp, not_exists, not_forall, not_le] at hx
      obtain ⟨ρ, hρ, hρr, hlt⟩ := hx.2 (j + 1)
      rw [Nat.cast_add_one] at hlt
      obtain ⟨i, hi⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hlt)
      exact mem_iUnion.2 ⟨i, hx.1, ρ, hρ, hρr, hi⟩
    -- On `A i` the ball ratios are at most `a⁻¹`, so the covering estimate `hH` applies.
    have hAS : ∀ i, μ (A i) ≤ (C : ℝ≥0∞) * a⁻¹ * S := by
      intro i
      have hcov : ∀ x ∈ A i, ∃ σ : ℝ, 0 < σ ∧ σ < r ∧
          μ (closedBall x σ) ≤ a⁻¹ * ν i (closedBall x σ) := by
        rintro x ⟨-, ρ, hρ, hρr, hk⟩
        refine ⟨ρ, hρ, hρr, ?_⟩
        calc μ (closedBall x ρ) = a⁻¹ * (a * μ (closedBall x ρ)) :=
              (ENNReal.inv_mul_cancel_left ha0 hatop).symm
          _ ≤ a⁻¹ * ν i (closedBall x ρ) := by
              gcongr
              exact (hk i le_rfl).le
      refine (hH _ i _ hcov).trans ?_
      gcongr
      exact (measure_mono (thickening_subset_of_subset r fun x hx ↦ hx.1)).trans
        (le_iSup (fun k ↦ ν k (thickening r W)) i)
    calc μ E ≤ μ (⋃ i, A i) := measure_mono hEA
      _ = ⨆ i, μ (A i) := hA.measure_iUnion
      _ ≤ (C : ℝ≥0∞) * a⁻¹ * S := iSup_le hAS
  -- `C (j + 1)⁻¹ S → 0` as `j → ∞`, because `C` and `S` are finite.
  have hlim : Tendsto (fun j : ℕ ↦ (C : ℝ≥0∞) * ((j : ℝ≥0∞) + 1)⁻¹ * S) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, Nat.cast_add_one] at h
    have h' := ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.natCast_ne_top C))) (Or.inr hS)
    rwa [mul_zero, zero_mul] at h'
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim key)

/-- **Simon Ch. 8, proof of 5.9, printed estimate (1)** (child `liminf_ratio_bound_ae` of
`variation_density_bound`): if `sup_i ν_i(thickening(r, W)) < ∞`, then for `μ`-a.e. `x ∈ W` some
`c ∈ ℕ` satisfies `liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for every `ρ ∈ (0, r)`.  The Besicovitch
covering estimate (Ch. 1, 3.12), with its constant `C = C(N)` and `ρ₀ = r`, is exactly the covering
hypothesis of the a.e. argument for each `ν_i`. -/
theorem Submission.intcpt_vdb_liminf_ratio_bound_ae :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (ν : ℕ → Measure (Euclidean N)) (W : Set (Euclidean N))
      (r : ℝ), ⨆ i, ν i (thickening r W) ≠ ∞ → ∀ᵐ x ∂μ, x ∈ W → ∃ c : ℕ, ∀ ρ : ℝ, 0 < ρ →
        ρ < r → liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ (c : ℝ≥0∞) * μ (closedBall x ρ) := by
  intro N μ ν W r hS
  -- Steps 1–2: the Besicovitch number `C` of `ℝ^N` and the covering estimate it gives.
  obtain ⟨C, hC⟩ := Submission.intcpt_vdb_besicovitch_cover_estimate N
  -- Steps 3–6: applied to `ν i` with `ρ₀ = r`, it makes the exceptional set `μ`-null.
  exact Submission.intcpt_vdb_liminf_bound_ae_of_cover N C μ ν W r
    (fun A i t h ↦ hC μ (ν i) A r t h) hS
/-- **Simon Ch. 8, proof of 5.9, printed (1)–(2), localisation and exhaustion** (child
`open_thickening_exhaustion` of `variation_density_bound`): an open `U ⊆ ℝ^N` is covered by
countably many sets `W_p` whose `r_p`-thickenings (`r_p > 0`) are relatively compact open subsets of
`U`.  Take `W = B°_s(x)` and `r = s` with `B°_{3s}(x) ⊆ U`: `thickening s (B°_s(x)) ⊆ B°_{2s}(x)`
has compact closure inside `B_{2s}(x) ⊆ U`, and countably many such balls cover `U` (Lindelöf). -/
theorem Submission.intcpt_vdb_open_thickening_exhaustion :
    ∀ (N : ℕ) (U : Set (Euclidean N)), IsOpen U → ∃ (W : ℕ → Set (Euclidean N)) (r : ℕ → ℝ),
      (∀ p, 0 < r p) ∧ (∀ p, IsRelCompactOpenIn (thickening (r p) (W p)) U) ∧ U ⊆ ⋃ p, W p := by
  intro N U hU
  -- For `x ∈ U` choose `s x > 0` with `B°_{3 s x}(x) ⊆ U`.
  have hrad : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ ball x (3 * s) ⊆ U := fun x hx ↦ by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 3, by positivity, by rwa [mul_div_cancel₀ ε three_ne_zero]⟩
  choose! s hs0 hsU using hrad
  -- `thickening (s x) (B°_{s x}(x)) ⊆ B°_{2 s x}(x)` has closure in `B_{2 s x}(x) ⊆ B°_{3 s x}(x)`.
  have hrel : ∀ x ∈ U, IsRelCompactOpenIn (thickening (s x) (ball x (s x))) U := fun x hx ↦ by
    have hsub : closure (thickening (s x) (ball x (s x))) ⊆ closedBall x (2 * s x) := by
      refine (closure_mono ?_).trans closure_ball_subset_closedBall
      simpa only [two_mul] using Metric.thickening_ball x (s x) (s x)
    refine ⟨isOpen_thickening, (isCompact_closedBall x _).of_isClosed_subset isClosed_closure hsub,
      hsub.trans ((closedBall_subset_ball ?_).trans (hsU x hx))⟩
    linarith [hs0 x hx]
  -- Lindelöf: countably many of the balls `B°_{s x}(x)`, `x ∈ U`, cover `U`.
  obtain ⟨T, hTU, hTc, hT⟩ :=
    TopologicalSpace.isOpen_biUnion_countable U (fun x ↦ ball x (s x)) fun _ _ ↦ isOpen_ball
  have hcov : U ⊆ ⋃ x ∈ T, ball x (s x) := by
    rw [hT]
    exact fun x hx ↦ mem_biUnion hx (mem_ball_self (hs0 x hx))
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- `U = ∅`: take `W p = ∅` and `r p = 1`.
    rw [biUnion_empty] at hcov
    refine ⟨fun _ ↦ ∅, fun _ ↦ 1, fun _ ↦ one_pos, fun _ ↦ ?_, hcov.trans (empty_subset _)⟩
    rw [thickening_empty]
    refine ⟨isOpen_empty, ?_, ?_⟩ <;> rw [closure_empty]
    exacts [isCompact_empty, empty_subset U]
  · -- `T = range f`: take `W p = B°_{s (f p)}(f p)` and `r p = s (f p)`.
    obtain ⟨f, rfl⟩ := hTc.exists_eq_range hTne
    rw [biUnion_range] at hcov
    exact ⟨fun p ↦ ball (f p) (s (f p)), fun p ↦ s (f p), fun p ↦ hs0 _ (hTU ⟨p, rfl⟩),
      fun p ↦ hrel _ (hTU ⟨p, rfl⟩), hcov⟩
/-- **Simon Ch. 8, proof of 5.9, passage from (1) to (2)** (child `ball_mass_le_of_density` of
`variation_density_bound`): a finite density `Θ^n(μ, x) = θ < ∞` gives `μ(B_ρ(x)) ≤ C ρ^n`, with
`C = (θ + 1) ω_n`, for all small `ρ > 0`.  The ratio `μ(B_ρ(x)) / (ω_n ρ^n)` is eventually
`< θ + 1`, and `0 < ω_n ρ^n < ∞` clears the denominator. -/
theorem Submission.intcpt_vdb_ball_mass_le_of_density :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞), HasDensity n μ x θ →
      θ ≠ ∞ → ∃ C r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
        μ (closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro N n μ x θ hθ hθ_top
  -- The density ratio is eventually `< θ + 1`, so it is `< θ + 1` on some interval `(0, r)`.
  have hlim : Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 θ) := hθ
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), densityRatio n μ x ρ < θ + 1 :=
    hlim.eventually (Iio_mem_nhds (ENNReal.lt_add_right hθ_top one_ne_zero))
  obtain ⟨r, hr, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  -- `ω_n` is the Haar volume of the nonempty open bounded unit ball, so `0 < ω_n < ∞`.
  have hω₀ : unitBallVolume n ≠ 0 :=
    (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
  have hω_top : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (x := 0)
      (r := 1)).ne
  refine ⟨(θ.toReal + 1) * (unitBallVolume n).toReal, r, hr, fun ρ hρ hρr ↦ ?_⟩
  have hρ' : densityRatio n μ x ρ < θ + 1 := hsub ⟨hρ, hρr⟩
  have hD₀ : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
    mul_ne_zero hω₀ (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne')
  have hD_top : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hω_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  calc μ (closedBall x ρ) ≤ (θ + 1) * (unitBallVolume n * ENNReal.ofReal ρ ^ n) :=
        (ENNReal.div_le_iff hD₀ hD_top).1 hρ'.le
    _ = ENNReal.ofReal ((θ.toReal + 1) * (unitBallVolume n).toReal * ρ ^ n) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg ENNReal.toReal_nonneg zero_le_one)
            ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (add_nonneg ENNReal.toReal_nonneg zero_le_one),
          ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hθ_top,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal hω_top, ENNReal.ofReal_pow hρ.le, mul_assoc]

/-- **Simon Ch. 8, proof of 5.9, printed estimates (1)–(2)** (child `variation_density_bound` of
`integral_compactness`): if `μ(ℝ^N ∖ U) = 0`, `sup_i ν_i(W) < ∞` for every open `W ⊂⊂ U` and
`Θ^n(μ, x)` exists and is finite for `μ`-a.e. `x`, then for `μ`-a.e. `x` there are `c` and `r > 0`
with `liminf_i ν_i(B_ρ(x)) ≤ c ρ^n` for `0 < ρ < r`.  Cover `U` by countably many `W_p` whose
`r_p`-thickenings are `⊂⊂ U` (child `open_thickening_exhaustion`).  At `μ`-a.e. `x ∈ W_p`,
Besicovitch gives `liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for `ρ < r_p` (child
`liminf_ratio_bound_ae`), and the finite density gives `μ(B_ρ(x)) ≤ C ρ^n` for small `ρ` (child
`ball_mass_le_of_density`). -/
theorem Submission.intcpt_variation_liminf_density_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N))
      (ν : ℕ → Measure (Euclidean N)), IsOpen U → μ Uᶜ = 0 →
      (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) →
      (∀ W : Set (Euclidean N), IsRelCompactOpenIn W U → ⨆ i, ν i W ≠ ∞) →
      (∀ᵐ x ∂μ, ∃ θ : ℝ≥0∞, HasDensity n μ x θ ∧ θ ≠ ∞) →
      ∀ᵐ x ∂μ, ∃ c r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
        liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ ENNReal.ofReal (c * ρ ^ n) := by
  intro N n U μ ν hU hUc _ hν hdens
  obtain ⟨W, r, hr, hWU, hUW⟩ := Submission.intcpt_vdb_open_thickening_exhaustion N U hU
  -- Each `thickening (r p) (W p)` is `⊂⊂ U`, so its `ν_i`-masses are bounded and the
  -- Besicovitch bound holds at `μ`-a.e. point of `W p`; countably many `p` keep it a.e.
  have hratio : ∀ᵐ x ∂μ, ∀ p, x ∈ W p → ∃ c : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < r p →
      liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ (c : ℝ≥0∞) * μ (closedBall x ρ) :=
    ae_all_iff.2 fun p ↦
      Submission.intcpt_vdb_liminf_ratio_bound_ae N μ ν (W p) (r p) (hν _ (hWU p))
  have hmemU : ∀ᵐ x ∂μ, x ∈ U := mem_ae_iff.2 hUc
  filter_upwards [hratio, hmemU, hdens] with x hx hxU hxθ
  obtain ⟨p, hxp⟩ := mem_iUnion.1 (hUW hxU)
  obtain ⟨c, hc⟩ := hx p hxp
  obtain ⟨θ, hθ, hθtop⟩ := hxθ
  obtain ⟨C, r', hr', hC⟩ := Submission.intcpt_vdb_ball_mass_le_of_density N n μ x θ hθ hθtop
  refine ⟨c * C, min (r p) r', lt_min (hr p) hr', fun ρ hρ hρr ↦ ?_⟩
  calc liminf (fun i ↦ ν i (closedBall x ρ)) atTop
      ≤ (c : ℝ≥0∞) * μ (closedBall x ρ) := hc ρ hρ (hρr.trans_le (min_le_left _ _))
    _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal (C * ρ ^ n) := by
        gcongr
        exact hC ρ hρ (hρr.trans_le (min_le_right _ _))
    _ = ENNReal.ofReal (c * C * ρ ^ n) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg c), ENNReal.ofReal_natCast]
/-- Blow-ups preserve Radon convergence (Simon Ch. 8, proof of 5.9: "`V_i → V`, and hence
`η_{ξ,λ#}V_i → η_{ξ,λ#}V` for each fixed `λ > 0`").  If `V_i → V` as Radon measures on `Gₙ(U)`,
`t > 0` and `F ∈ C_c(ℝ^N × G(N,n))` has `ξ + t y ∈ U` for every `(y, S) ∈ spt F`, then
`∫ F dV_{i,ξ,t} → ∫ F dV_{ξ,t}`. -/
theorem Submission.intcpt_diag_rescaled_radon_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U)
      (ξ : Euclidean N) (t : ℝ) (F : C_c(Euclidean N × Grassmannian N n, ℝ)),
      Varifold.RadonConverges Vi V → 0 < t → (∀ z ∈ tsupport F, ξ + t • z.1 ∈ U) →
      Tendsto (fun i ↦ ∫ z, F z ∂(rescaledMeasure (Vi i) ξ t)) atTop
        (𝓝 (∫ z, F z ∂(rescaledMeasure V ξ t))) := by
  intro N n U Vi V ξ t F hconv ht hF
  -- The dilation `Φ (y, S) = (t⁻¹ (y - ξ), S)` is a homeomorphism with inverse `(ξ + t y, S)`.
  let Φ : Euclidean N × Grassmannian N n ≃ₜ Euclidean N × Grassmannian N n :=
    { toFun := fun z ↦ (t⁻¹ • (z.1 - ξ), z.2)
      invFun := fun z ↦ (ξ + t • z.1, z.2)
      left_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      right_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  -- The pulled-back test function `H = F ∘ Φ` is supported in `U × G(N,n)`.
  let H : C_c(Euclidean N × Grassmannian N n, ℝ) := F.comp Φ.toCocompactMap
  have hHsupp : tsupport H ⊆ U ×ˢ (univ : Set (Grassmannian N n)) := by
    intro z hz
    have hz' : Φ z ∈ tsupport F := tsupport_comp_subset_preimage F Φ.continuous hz
    refine ⟨?_, trivial⟩
    have := hF _ hz'
    simpa [Φ, smul_smul, ht.ne'] using this
  -- Rescaling formula: `∫ F dV'_{ξ,t} = t⁻ⁿ ∫ H dV'`.
  have hresc : ∀ V' : Varifold N n U,
      ∫ z, F z ∂(rescaledMeasure V' ξ t) = t⁻¹ ^ n * ∫ z, H z ∂V'.measure := by
    intro V'
    have hm : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) := by
      fun_prop
    rw [rescaledMeasure, integral_smul_measure,
      integral_map hm.measurable.aemeasurable (map_continuous F).aestronglyMeasurable,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    rfl
  -- The restriction `h` of `H` to Simon's open product `Gₙ(U)` is a test function there.
  let Ω := U ×ˢ (univ : Set (Grassmannian N n))
  let h : C_c(Ω, ℝ) :=
    { toFun := fun w ↦ H w.1
      continuous_toFun := H.continuous.comp continuous_subtype_val
      hasCompactSupport' := by
        have hK : IsCompact ((Subtype.val : Ω → Euclidean N × Grassmannian N n) ⁻¹' tsupport H) :=
          Topology.IsInducing.subtypeVal.isCompact_preimage' H.hasCompactSupport.isCompact (by
            intro z hz
            exact ⟨⟨z, hHsupp hz⟩, rfl⟩)
        exact hK.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_comp_subset_preimage H continuous_subtype_val) }
  have hdom : ∀ V' : Varifold N n U, ∫ w, h w ∂V'.domainMeasure = ∫ z, H z ∂V'.measure := by
    intro V'
    rw [← V'.map_domainMeasure, (MeasurableEmbedding.subtype_coe
      (V'.isOpen_domain.measurableSet.prod MeasurableSet.univ)).integral_map]
    rfl
  have := (hconv h).const_mul (t⁻¹ ^ n)
  simp only [hdom] at this
  simpa only [hresc] using this
/-- Test functions are integrable for the blow-up `V_{ξ,t} = η_{ξ,t #} V` (Simon Ch. 8, 1.1 and
5.1) when the blow-up of their support stays in `U`: if `t > 0` and `ξ + t y ∈ U` for every
`(y, S) ∈ spt F`, then `F ∈ C_c(ℝ^N × G(N,n))` is `rescaledMeasure V ξ t`-integrable. -/
theorem Submission.intcpt_diag_rescaled_integrable :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (ξ : Euclidean N) (t : ℝ)
      (F : C_c(Euclidean N × Grassmannian N n, ℝ)), 0 < t →
      (∀ z ∈ tsupport F, ξ + t • z.1 ∈ U) → Integrable (fun z ↦ F z) (rescaledMeasure V ξ t) := by
  intro N n U V ξ t F ht hF
  -- The blow-up `Φ(y, S) = (t⁻¹ (y - ξ), S)` is a homeomorphism of `ℝ^N × G(N,n)`.
  let Φ : Euclidean N × Grassmannian N n ≃ₜ Euclidean N × Grassmannian N n :=
    { toFun := fun z ↦ (t⁻¹ • (z.1 - ξ), z.2)
      invFun := fun z ↦ (ξ + t • z.1, z.2)
      left_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      right_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  -- The pull-back `H = F ∘ Φ` is compactly supported in `U × G(N,n)`.
  let H : C_c(Euclidean N × Grassmannian N n, ℝ) := F.comp Φ.toCocompactMap
  have hHsupp : tsupport H ⊆ U ×ˢ (univ : Set (Grassmannian N n)) := by
    intro z hz
    have hz' : Φ z ∈ tsupport F := tsupport_comp_subset_preimage F Φ.continuous hz
    refine ⟨?_, trivial⟩
    simpa [Φ, smul_smul, ht.ne'] using hF _ hz'
  -- `K = π(spt H)` is a compact subset of `U`, so `V(K × G(N,n)) < ∞`.
  let K : Set (Euclidean N) := Prod.fst '' tsupport H
  have hKc : IsCompact K := H.hasCompactSupport.isCompact.image continuous_fst
  have hKU : K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hHsupp hz).1
  have hfin := V.finite_on_compact K hKc hKU
  have hsuppK : Function.support H ⊆ K ×ˢ (univ : Set (Grassmannian N n)) := by
    intro z hz
    exact ⟨⟨z, subset_tsupport _ hz, rfl⟩, trivial⟩
  -- `H` is bounded and vanishes off `K × G(N,n)`, hence `V`-integrable.
  obtain ⟨M, hM⟩ := H.hasCompactSupport.exists_bound_of_continuous H.continuous
  have hHint : Integrable (fun z ↦ H z) V.measure := by
    have hOn : IntegrableOn (fun z ↦ H z) (K ×ˢ (univ : Set (Grassmannian N n))) V.measure :=
      Measure.integrableOn_of_bounded (M := M) hfin H.continuous.aestronglyMeasurable
        (Eventually.of_forall hM)
    exact (integrableOn_iff_integrable_of_support_subset hsuppK).mp hOn
  -- Transfer along `Φ`, then scale by `t^{-n}`.
  have hmap : Integrable (fun z ↦ F z) (V.measure.map Φ) :=
    (integrable_map_measure (map_continuous F).aestronglyMeasurable
      Φ.continuous.measurable.aemeasurable).mpr hHint
  exact hmap.smul_measure ENNReal.ofReal_ne_top
/-- A countable sup-dense family of test functions on `B°_R(0) × G(N,n)` (Simon Ch. 8, proof of
5.9, printed (3)–(4), step 1 of the diagonal blow-up): for `R > 0` there are
`g_m ∈ C_c(ℝ^N × G(N,n))` with `spt g_m ⊆ B°_R(0) × G(N,n)` such that every
`f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ B°_R(0) × G(N,n)` is a uniform limit of the `g_m`. -/
theorem Submission.intcpt_diag_ball_cc_dense_seq :
    ∀ (N n : ℕ) (R : ℝ), 0 < R → ∃ g : ℕ → C_c(Euclidean N × Grassmannian N n, ℝ),
      (∀ m, tsupport (g m) ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) ∧
      ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
        tsupport f ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)) →
        ∀ η : ℝ, 0 < η → ∃ m, ∀ z, |f z - g m z| ≤ η := by
  intro N n R hR
  -- Step 1: `C(Z, ℝ)` (compact-open) is second countable (inlined, as in the accepted
  -- `Submission.radon_compactlySupported_countable_approx`).
  set X := Euclidean N × Grassmannian N n
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
  -- Step 2: dense sequence, uniform approximation on compact sets.
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
  -- Step 3: exhaustion of the ball and cutoffs.
  set r : ℕ → ℝ := fun m ↦ R * ((m + 1 : ℝ) / (m + 2)) with hr
  have hrpos : ∀ m, 0 < r m := fun m ↦ by positivity
  have hrlt : ∀ m, r m < R := by
    intro m
    have : ((m : ℝ) + 1) / (m + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc r m = R * (((m : ℝ) + 1) / (m + 2)) := rfl
      _ < R * 1 := mul_lt_mul_of_pos_left this hR
      _ = R := mul_one R
  have hrmono : ∀ m, r m < r (m + 1) := by
    intro m
    have h1 : ((m : ℝ) + 1) / (m + 2) < ((m + 1 : ℕ) + 1 : ℝ) / ((m + 1 : ℕ) + 2) := by
      push_cast
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact mul_lt_mul_of_pos_left h1 hR
  have hrlim : ∀ y : Euclidean N, ‖y‖ < R → ∃ m, ‖y‖ < r m := by
    intro y hy
    have ht : Tendsto r atTop (𝓝 R) := by
      have h1 : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1) / (m + 2)) atTop (𝓝 1) := by
        have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)
        have h2 : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) + 1)) atTop (𝓝 1) :=
          this.comp (tendsto_add_atTop_nat 1)
        refine h2.congr (fun m ↦ ?_)
        push_cast; ring_nf
      simpa using h1.const_mul R
    exact (ht.eventually (lt_mem_nhds hy)).exists
  set E : ℕ → Set X := fun m ↦ closedBall (0 : Euclidean N) (r m) ×ˢ (univ : Set (Grassmannian N n))
  have hEc : ∀ m, IsCompact (E m) := fun m ↦ (isCompact_closedBall _ _).prod isCompact_univ
  choose χ hχ1 hχ0 hχc hχI using fun m => exists_continuous_one_zero_of_isCompact (X := X)
    (hEc m)
    ((isOpen_ball (x := (0 : Euclidean N)) (ε := r (m + 1))).prod isOpen_univ).isClosed_compl
    (by
      rw [disjoint_compl_right_iff_subset]
      exact prod_mono (closedBall_subset_ball (hrmono m)) subset_rfl)
  have hχsupp : ∀ m,
      tsupport (χ m) ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)) := by
    intro m
    have hcl : IsClosed (closedBall (0 : Euclidean N) (r (m + 1)) ×ˢ
        (univ : Set (Grassmannian N n))) := isClosed_closedBall.prod isClosed_univ
    refine (closure_minimal ?_ hcl).trans ?_
    · intro x hx
      by_contra hxE
      apply hx
      apply hχ0 m
      intro hxb
      exact hxE (prod_mono ball_subset_closedBall subset_rfl hxb)
    · exact prod_mono (closedBall_subset_ball (hrlt (m + 1))) subset_rfl
  -- Step 4: the family.
  let g : ℕ → C_c(X, ℝ) := fun k =>
    ⟨χ (Nat.unpair k).1 * d (Nat.unpair k).2, (hχc (Nat.unpair k).1).mul_right⟩
  have hgx : ∀ k x, g k x = χ (Nat.unpair k).1 x * d (Nat.unpair k).2 x := fun _ _ => rfl
  have hgsupp : ∀ k, tsupport (g k) ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)) :=
    fun k => (tsupport_mul_subset_left (f := χ (Nat.unpair k).1) (g := d (Nat.unpair k).2)).trans
      (hχsupp _)
  clear_value g
  refine ⟨g, hgsupp, fun f hf η hη => ?_⟩
  -- Step 5: approximation.
  obtain ⟨m, hm⟩ : ∃ m, tsupport f ⊆ E m := by
    have hcov : tsupport f ⊆
        ⋃ m, ball (0 : Euclidean N) (r m) ×ˢ (univ : Set (Grassmannian N n)) := by
      intro z hz
      have hz1 := (hf hz).1
      rw [mem_ball, dist_zero_right] at hz1
      obtain ⟨m, hm⟩ := hrlim z.1 hz1
      exact mem_iUnion.mpr ⟨m, ⟨by rw [mem_ball, dist_zero_right]; exact hm, trivial⟩⟩
    have hmono :
        Monotone (fun m ↦ ball (0 : Euclidean N) (r m) ×ˢ (univ : Set (Grassmannian N n))) := by
      intro a b hab
      apply prod_mono _ subset_rfl
      apply ball_subset_ball
      exact (strictMono_nat_of_lt_succ hrmono).monotone hab
    obtain ⟨m, hm⟩ := f.hasCompactSupport.isCompact.elim_directed_cover _
      (fun m ↦ isOpen_ball.prod isOpen_univ) hcov hmono.directed_le
    exact ⟨m, hm.trans (prod_mono ball_subset_closedBall subset_rfl)⟩
  obtain ⟨i, hi⟩ := happrox f (E (m + 1)) (hEc _) η hη
  refine ⟨Nat.pair m i, fun x => ?_⟩
  have hfx : f x = χ m x * f x := by
    by_cases hx : x ∈ E m
    · rw [hχ1 m hx, Pi.one_apply, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hm h)), mul_zero]
  rw [hgx, Nat.unpair_pair, hfx, ← mul_sub, abs_mul, abs_of_nonneg (hχI m x).1]
  by_cases hx : x ∈ E (m + 1)
  · calc χ m x * |f x - d i x| ≤ 1 * η :=
          mul_le_mul (hχI m x).2 (hi x hx).le (abs_nonneg _) zero_le_one
      _ = η := one_mul η
  · have hx' : x ∈ (ball (0 : Euclidean N) (r (m + 1)) ×ˢ (univ : Set (Grassmannian N n)))ᶜ := by
      intro hb
      exact hx (prod_mono ball_subset_closedBall subset_rfl hb)
    rw [hχ0 m hx', Pi.zero_apply, zero_mul]
    exact hη.le
/-- One blow-up of the diagonal argument in Simon Ch. 8, proof of 5.9 (printed (4): "(by (2))
`‖δW_i‖(B_R(0)) → 0`").  If `V` has locally bounded first variation in `U`, `t, R > 0` and
`ξ + t y ∈ U` for every `y ∈ B°_R(0)`, then `W = V_{ξ,t} ⌞ (B°_R(0) × G(N,n))` is an `n`-varifold on
`B°_R(0)` with locally bounded first variation, and `‖δW‖(B°_R(0)) ≤ t^{-n} t ‖δV‖(B_{tR}(ξ))`. -/
theorem Submission.intcpt_diag_blowup_variation_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (ξ : Euclidean N) (t R : ℝ),
      V.HasLocallyBoundedFirstVariation → 0 < t → 0 < R →
      (∀ y ∈ ball (0 : Euclidean N) R, ξ + t • y ∈ U) →
      ∃ W : Varifold N n (ball (0 : Euclidean N) R),
        W.measure = (rescaledMeasure V ξ t).restrict
          (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) ∧
        W.HasLocallyBoundedFirstVariation ∧
        variationMeasure W (ball (0 : Euclidean N) R) ≤
          ENNReal.ofReal (t⁻¹ ^ n * t) * variationMeasure V (closedBall ξ (t * R)) := by
  intro N n U V ξ t R hV ht hR hσU
  set O : Set (Euclidean N) := ball (0 : Euclidean N) R with hOdef
  have hOm : MeasurableSet O := measurableSet_ball
  -- the homeomorphism `σ(y) = ξ + t • y`, with inverse `η(z) = t⁻¹ • (z - ξ)`
  let σ : Euclidean N ≃ₜ Euclidean N :=
    { toFun := fun y ↦ ξ + t • y
      invFun := fun z ↦ t⁻¹ • (z - ξ)
      left_inv := by intro y; simp [smul_smul, ht.ne']
      right_inv := by intro z; simp [smul_smul, ht.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hσ : ∀ y, σ y = ξ + t • y := fun _ ↦ rfl
  have hσO : σ '' O ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hσU y hy
  have hσball : σ '' O ⊆ closedBall ξ (t * R) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hσ, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    rw [hOdef, mem_ball, dist_zero_right] at hy
    exact mul_le_mul_of_nonneg_left hy.le ht.le
  have hΦc : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) := by
    fun_prop
  -- Step 1: the varifold `W`
  let W : Varifold N n O :=
    { isOpen_domain := isOpen_ball
      measure := (rescaledMeasure V ξ t).restrict (O ×ˢ (univ : Set (Grassmannian N n)))
      supported := by
        rw [Measure.restrict_apply (hOm.compl.prod MeasurableSet.univ)]
        have : (Oᶜ ×ˢ (univ : Set (Grassmannian N n))) ∩ (O ×ˢ (univ : Set (Grassmannian N n))) =
            ∅ := by
          ext z; simp
        rw [this, measure_empty]
      finite_on_compact := by
        intro K hK hKO
        apply ne_top_of_le_ne_top _ (Measure.restrict_apply_le _ _)
        rw [rescaledMeasure, Measure.smul_apply,
          Measure.map_apply hΦc.measurable (hK.measurableSet.prod MeasurableSet.univ), smul_eq_mul]
        apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        have he : (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) ⁻¹'
            (K ×ˢ (univ : Set (Grassmannian N n))) =
              (σ '' K) ×ˢ (univ : Set (Grassmannian N n)) := by
          ext z
          simp only [mem_preimage, mem_prod, mem_univ, and_true]
          rw [σ.image_eq_preimage_symm]
          rfl
        rw [he]
        exact V.finite_on_compact _ (hK.image σ.continuous) ((image_mono hKO).trans hσO) }
  have hWmeas :
      W.measure = (rescaledMeasure V ξ t).restrict (O ×ˢ (univ : Set (Grassmannian N n))) := rfl
  refine ⟨W, rfl, ?_⟩
  -- Steps 3-4: pulled-back test fields and the first-variation scaling `δW(X) = t^{-n} t δV(Y)`
  have hη : ContDiff ℝ 1 (fun z : Euclidean N ↦ t⁻¹ • (z - ξ)) := by fun_prop
  have hfd : ∀ z : Euclidean N, fderiv ℝ (fun z : Euclidean N ↦ t⁻¹ • (z - ξ)) z =
      t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N) :=
    fun z ↦ (((hasFDerivAt_id z).sub_const ξ).const_smul t⁻¹).fderiv
  have hpull : ∀ X : Varifold.TestVectorField (N := N) O, ∃ Y : Varifold.TestVectorField (N := N) U,
      (∀ z, Y z = X (t⁻¹ • (z - ξ))) ∧ tsupport Y.toFun ⊆ σ '' tsupport X.toFun ∧
      W.firstVariation X = t⁻¹ ^ n * t * V.firstVariation Y := by
    intro X
    let Yf : Euclidean N → Euclidean N := fun z ↦ X (t⁻¹ • (z - ξ))
    have hYsupp : tsupport Yf ⊆ σ '' tsupport X.toFun := by
      rw [σ.image_eq_preimage_symm]
      exact tsupport_comp_subset_preimage X.toFun σ.symm.continuous
    let Y : Varifold.TestVectorField (N := N) U :=
      { toFun := Yf
        contDiff := X.contDiff.comp hη
        compactSupport :=
          (X.compactSupport.isCompact.image σ.continuous).of_isClosed_subset (isClosed_tsupport _)
            hYsupp
        support_subset := hYsupp.trans ((image_mono X.support_subset).trans hσO) }
    refine ⟨Y, fun z ↦ rfl, hYsupp, ?_⟩
    have hdiv : ∀ z (S : Grassmannian N n), Varifold.tangentialDivergence Y z S =
        t⁻¹ * Varifold.tangentialDivergence X (t⁻¹ • (z - ξ)) S := by
      intro z S
      have hX' : DifferentiableAt ℝ X.toFun (t⁻¹ • (z - ξ)) :=
        (X.contDiff.differentiable one_ne_zero) _
      have hcomp : fderiv ℝ Yf z = t⁻¹ • fderiv ℝ X.toFun (t⁻¹ • (z - ξ)) := by
        have h1 : fderiv ℝ (X.toFun ∘ fun z ↦ t⁻¹ • (z - ξ)) z =
            (fderiv ℝ X.toFun (t⁻¹ • (z - ξ))).comp (fderiv ℝ (fun z ↦ t⁻¹ • (z - ξ)) z) :=
          fderiv_comp z hX' ((hη.differentiable one_ne_zero) z)
        rw [show Yf = X.toFun ∘ fun z ↦ t⁻¹ • (z - ξ) from rfl, h1, hfd]
        ext v
        simp
      change Matrix.trace (S.1 * Varifold.clmToMatrix (fderiv ℝ Yf z)) =
        t⁻¹ * Matrix.trace (S.1 * Varifold.clmToMatrix (fderiv ℝ X.toFun (t⁻¹ • (z - ξ))))
      rw [hcomp, map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hdivX_cont := Varifold.continuous_tangentialDivergence (n := n) X.contDiff
    have hvanish : ∀ z ∉ O ×ˢ (univ : Set (Grassmannian N n)),
        Varifold.tangentialDivergence X.toFun z.1 z.2 = 0 := by
      intro z hz
      by_contra hne
      exact hz (prod_mono X.support_subset subset_rfl
        (Varifold.support_tangentialDivergence_subset X.toFun hne))
    calc W.firstVariation X = ∫ z, Varifold.tangentialDivergence X.toFun z.1 z.2 ∂W.measure := rfl
      _ = ∫ z, Varifold.tangentialDivergence X.toFun z.1 z.2 ∂(rescaledMeasure V ξ t) := by
          rw [hWmeas]; exact setIntegral_eq_integral_of_forall_compl_eq_zero hvanish
      _ = t⁻¹ ^ n *
            ∫ z, Varifold.tangentialDivergence X.toFun (t⁻¹ • (z.1 - ξ)) z.2 ∂V.measure := by
          rw [rescaledMeasure, integral_smul_measure,
            integral_map hΦc.measurable.aemeasurable hdivX_cont.aestronglyMeasurable,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      _ = t⁻¹ ^ n * ∫ z, t * Varifold.tangentialDivergence Y z.1 z.2 ∂V.measure := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          rw [hdiv]
          field_simp
      _ = t⁻¹ ^ n * t * V.firstVariation Y := by
          rw [integral_const_mul, mul_assoc]
          rfl
  -- Step 5: comparison of the first-variation norms
  have hc0 : (0 : ℝ) ≤ t⁻¹ ^ n * t := by positivity
  have hcmp : ∀ O' : Set (Euclidean N), W.firstVariationNormOn O' ≤
      ENNReal.ofReal (t⁻¹ ^ n * t) * V.firstVariationNormOn (σ '' O') := by
    intro O'
    classical
    generalize hB : V.firstVariationNormOn (σ '' O') = B
    unfold Varifold.firstVariationNormOn
    refine iSup_le fun X ↦ ?_
    split_ifs with hX
    · obtain ⟨Y, hYz, hYsupp, hδ⟩ := hpull X
      have hY : Y.UnitSupportedIn (σ '' O') := by
        refine ⟨hYsupp.trans (image_mono hX.1), fun z ↦ ?_⟩
        rw [hYz]
        exact hX.2 _
      have hle := Varifold.le_firstVariationNormOn V (σ '' O') Y hY
      rw [hB] at hle
      rw [hδ, abs_mul, abs_of_nonneg hc0, ENNReal.ofReal_mul hc0]
      exact mul_le_mul_of_nonneg_left hle zero_le
    · exact zero_le
  -- Step 6: `W` has locally bounded first variation
  have hW : W.HasLocallyBoundedFirstVariation := by
    intro O' hO' hO'c
    have hσO' : IsOpen (σ '' O') := σ.isOpenMap _ hO'
    have hcl : closure (σ '' O') = σ '' closure O' := (σ.image_closure O').symm
    have hfin := hV (σ '' O') hσO'
      ⟨by rw [hcl]; exact hO'c.1.image σ.continuous,
       by rw [hcl]; exact (image_mono hO'c.2).trans hσO⟩
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hcmp O')
  refine ⟨hW, ?_⟩
  -- Steps 7-8: the Riesz measures and the exhaustion of `O` by the balls `B°_{r_j}(0)`
  have hvW : variationMeasure W = W.firstVariationRieszMeasure hW := by
    simp [variationMeasure, hW]
  have hvV : variationMeasure V = V.firstVariationRieszMeasure hV := by
    simp [variationMeasure, hV]
  have hpolar : ∀ A, V.firstVariationNormOn A ≤ variationMeasure V A := by
    intro A
    rw [hvV]
    exact V.firstVariationNormOn_le_of_polarRepresentation
      (V.isFirstVariationPolarRepresentation_riesz hV) A
  set r : ℕ → ℝ := fun j ↦ R * (((j : ℝ) + 1) / ((j : ℝ) + 2)) with hr
  have hrpos : ∀ j, 0 < r j := fun j ↦ by positivity
  have hrlt : ∀ j, r j < R := by
    intro j
    have : ((j : ℝ) + 1) / ((j : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc r j = R * (((j : ℝ) + 1) / ((j : ℝ) + 2)) := rfl
      _ < R * 1 := mul_lt_mul_of_pos_left this hR
      _ = R := mul_one R
  have hrmono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro j
    apply mul_le_mul_of_nonneg_left _ hR.le
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hrlim : Tendsto r atTop (𝓝 R) := by
    have h1 : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1) / ((m : ℝ) + 2)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)
      have h2 : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) + 1)) atTop (𝓝 1) :=
        this.comp (tendsto_add_atTop_nat 1)
      refine h2.congr (fun m ↦ ?_)
      push_cast
      ring_nf
    simpa using h1.const_mul R
  have hunion : O = ⋃ j, ball (0 : Euclidean N) (r j) := by
    ext y
    simp only [hOdef, mem_iUnion, mem_ball, dist_zero_right]
    constructor
    · intro hy
      exact (hrlim.eventually (lt_mem_nhds hy)).exists
    · rintro ⟨j, hj⟩
      exact hj.trans (hrlt j)
  have hmono : Monotone (fun j ↦ ball (0 : Euclidean N) (r j)) :=
    fun a b hab ↦ ball_subset_ball (hrmono hab)
  have hOj : ∀ j, variationMeasure W (ball (0 : Euclidean N) (r j)) ≤
      ENNReal.ofReal (t⁻¹ ^ n * t) * variationMeasure V (closedBall ξ (t * R)) := by
    intro j
    have hclj : closure (ball (0 : Euclidean N) (r j)) = closedBall 0 (r j) :=
      closure_ball _ (hrpos j).ne'
    rw [hvW, Varifold.firstVariationRieszMeasure_eq_norm W hW _ isOpen_ball
      ⟨by rw [hclj]; exact isCompact_closedBall _ _,
       by rw [hclj]; exact closedBall_subset_ball (hrlt j)⟩]
    refine (hcmp _).trans (mul_le_mul_of_nonneg_left ((hpolar _).trans (measure_mono ?_)) zero_le)
    exact (image_mono (ball_subset_ball (hrlt j).le)).trans hσball
  calc variationMeasure W O = variationMeasure W (⋃ j, ball (0 : Euclidean N) (r j)) :=
        congrArg _ hunion
    _ = ⨆ j, variationMeasure W (ball (0 : Euclidean N) (r j)) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hOj
/-- Convergence on a dense family of test functions extends to all of them under a uniform mass
bound (Simon Ch. 8, proof of 5.9, printed (3): the diagonal blow-up converges against every test
function once it does against a countable dense family).  Let `A = O × G(N,n)`, let the
`g_m ∈ C_c(ℝ^N × G(N,n))` with `spt g_m ⊆ A` be uniformly dense among the `f ∈ C_c(ℝ^N × G(N,n))`
with `spt f ⊆ A`, and let `μ_k(A) ≤ C` and `ν_k(A) ≤ C < ∞` for all large `k`.  If
`∫ g_m dμ_k - ∫ g_m dν_k → 0` for every `m`, then `∫ f dμ_k - ∫ f dν_k → 0` for every such `f`. -/
theorem Submission.intcpt_diag_dense_family_tendsto :
    ∀ (N n : ℕ) (O : Set (Euclidean N)) (g : ℕ → C_c(Euclidean N × Grassmannian N n, ℝ))
      (μ ν : ℕ → Measure (Euclidean N × Grassmannian N n)) (C : ℝ≥0∞), MeasurableSet O →
      C ≠ ∞ → (∀ m, tsupport (g m) ⊆ O ×ˢ (univ : Set (Grassmannian N n))) →
      (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
        tsupport f ⊆ O ×ˢ (univ : Set (Grassmannian N n)) →
        ∀ η : ℝ, 0 < η → ∃ m, ∀ z, |f z - g m z| ≤ η) →
      (∀ᶠ k in atTop, μ k (O ×ˢ (univ : Set (Grassmannian N n))) ≤ C) →
      (∀ᶠ k in atTop, ν k (O ×ˢ (univ : Set (Grassmannian N n))) ≤ C) →
      (∀ m, Tendsto (fun k ↦ ∫ z, g m z ∂(μ k) - ∫ z, g m z ∂(ν k)) atTop (𝓝 0)) →
      ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
        tsupport f ⊆ O ×ˢ (univ : Set (Grassmannian N n)) →
        Tendsto (fun k ↦ ∫ z, f z ∂(μ k) - ∫ z, f z ∂(ν k)) atTop (𝓝 0) := by
  intro N n O g μ ν C _hO hC hgsupp hdense hμ hν hconv f hf
  set A : Set (Euclidean N × Grassmannian N n) := O ×ˢ (univ : Set (Grassmannian N n))
  set C₀ : ℝ := C.toReal
  have hC₀nn : 0 ≤ C₀ := ENNReal.toReal_nonneg
  -- Step 1: a test function supported in `A` is integrable for any measure with `μ'(A) ≤ C`.
  have hintegr : ∀ (μ' : Measure (Euclidean N × Grassmannian N n))
      (h : C_c(Euclidean N × Grassmannian N n, ℝ)),
      μ' A ≤ C → tsupport h ⊆ A → Integrable (fun z ↦ h z) μ' := by
    intro μ' h hμ' hh
    obtain ⟨M, hM⟩ := h.hasCompactSupport.exists_bound_of_continuous h.continuous
    have hOn : IntegrableOn (fun z ↦ h z) A μ' :=
      Measure.integrableOn_of_bounded (M := M) (ne_top_of_le_ne_top hC hμ')
        h.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    exact (integrableOn_iff_integrable_of_support_subset ((subset_tsupport _).trans hh)).mp hOn
  -- Step 2: if `|h| ≤ η` and `h = 0` off `A`, then `|∫ h dμ'| ≤ η μ'(A) ≤ η C₀`.
  have hest : ∀ (μ' : Measure (Euclidean N × Grassmannian N n))
      (h : Euclidean N × Grassmannian N n → ℝ) (η : ℝ),
      0 ≤ η → μ' A ≤ C → (∀ z, z ∉ A → h z = 0) → (∀ z, |h z| ≤ η) →
      |∫ z, h z ∂μ'| ≤ η * C₀ := by
    intro μ' h η hηnn hμ' h0 hη
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
    have hlt : μ' A < ∞ := lt_of_le_of_lt hμ' (lt_top_iff_ne_top.mpr hC)
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ') (s := A) (f := h) (C := η) hlt
      (fun z _ ↦ by simpa [Real.norm_eq_abs] using hη z)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hηnn)
    exact ENNReal.toReal_mono hC hμ'
  -- Step 3: approximate `f` by `g m` within `η = ε / (4 (C₀ + 1))`, and take `k` so large that
  -- both mass bounds hold and `|∫ g m dμ_k - ∫ g m dν_k| < ε / 2`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * (C₀ + 1)) with hηdef
  have hηpos : 0 < η := by positivity
  obtain ⟨m, hm⟩ := hdense f hf η hηpos
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp (hconv m) (ε / 2) (by positivity)
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp hμ
  obtain ⟨K₃, hK₃⟩ := eventually_atTop.mp hν
  refine ⟨max K₁ (max K₂ K₃), fun k hk ↦ ?_⟩
  have hk1 : K₁ ≤ k := le_of_max_le_left hk
  have hk2 : K₂ ≤ k := le_trans (le_max_left _ _) (le_of_max_le_right hk)
  have hk3 : K₃ ≤ k := le_trans (le_max_right _ _) (le_of_max_le_right hk)
  have hμk := hK₂ k hk2
  have hνk := hK₃ k hk3
  have hgk := hK₁ k hk1
  rw [Real.dist_eq, sub_zero] at hgk ⊢
  have hfμ := hintegr (μ k) f hμk hf
  have hgμ := hintegr (μ k) (g m) hμk (hgsupp m)
  have hfν := hintegr (ν k) f hνk hf
  have hgν := hintegr (ν k) (g m) hνk (hgsupp m)
  -- Step 4: `f - g m` vanishes off `A` and is bounded by `η`, so Step 2 applies to both measures.
  have h0 : ∀ z, z ∉ A → f z - g m z = 0 := by
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hf h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hgsupp m h)), sub_zero]
  have e1 := hest (μ k) (fun z ↦ f z - g m z) η hηpos.le hμk h0 hm
  have e2 := hest (ν k) (fun z ↦ f z - g m z) η hηpos.le hνk h0 hm
  rw [integral_sub hfμ hgμ] at e1
  rw [integral_sub hfν hgν] at e2
  -- Step 5: the triangle inequality, with `2 η C₀ = (ε / 2) C₀ / (C₀ + 1) < ε / 2`.
  have hsmall : 2 * (η * C₀) < ε / 2 := by
    have h4 : 0 < C₀ + 1 := by linarith
    have hrw : η * C₀ = ε / 4 * (C₀ / (C₀ + 1)) := by
      rw [hηdef]; field_simp
    have hfrac : C₀ / (C₀ + 1) < 1 := by rw [div_lt_one h4]; linarith
    have hfrac0 : 0 ≤ C₀ / (C₀ + 1) := div_nonneg hC₀nn h4.le
    rw [hrw]; nlinarith
  have a1 := abs_le.mp e1
  have a2 := abs_le.mp e2
  have a3 := abs_lt.mp hgk
  rw [abs_lt]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
/-- `H^n ⌞ σ(A) = t^n σ_# (H^n ⌞ A)` for the similarity `σ(y) = ξ + t y`, `t > 0`, and every
set `A` (measurable or not): `σ = (ξ + ·) ∘ (t • ·)` scales `H^n` of every set by `t^n`, and on a
Borel set `B` both sides evaluate to `H^n(B ∩ σ(A)) = H^n(σ(σ⁻¹(B) ∩ A))`. -/
theorem Submission.intcpt_ri_restrict_similarity_image :
    ∀ (N n : ℕ) (ξ : Euclidean N) (t : ℝ) (A : Set (Euclidean N)), 0 < t → (μHE[n] : Measure (Euclidean N)).restrict ((fun y : Euclidean N ↦ ξ + t • y) '' A) = ENNReal.ofReal (t ^ n) • ((μHE[n] : Measure (Euclidean N)).restrict A).map (fun y : Euclidean N ↦ ξ + t • y) := by
  intro N n ξ t A ht
  -- Step 1: `σ = fun y ↦ ξ + t • y` is continuous, hence Borel measurable.
  have hσ : Measurable (fun y : Euclidean N ↦ ξ + t • y) :=
    (show Continuous (fun y : Euclidean N ↦ ξ + t • y) by fun_prop).measurable
  -- Step 2: `H^n(σ(S)) = t^n H^n(S)` for every set `S`, since `σ(S) = ξ + t • S`.
  have hscale : ∀ S : Set (Euclidean N),
      (μHE[n] : Measure (Euclidean N)) ((fun y : Euclidean N ↦ ξ + t • y) '' S) =
        ENNReal.ofReal (t ^ n) * μHE[n] S := by
    intro S
    rw [← Set.image_image (fun z : Euclidean N ↦ ξ + z) (fun y : Euclidean N ↦ t • y) S,
      Set.image_smul, (isometry_add_left ξ).euclideanHausdorffMeasure_image,
      Measure.euclideanHausdorffMeasure_smul₀ n ht.ne' S, ENNReal.smul_def, smul_eq_mul,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg ht.le]
  -- Steps 3–6: both sides agree on every Borel set `B`.
  ext B hB
  rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply hσ hB,
    Measure.restrict_apply (hσ hB), smul_eq_mul, ← hscale, Set.image_preimage_inter]
/-- Countable `n`-rectifiability is preserved by the inverse similarity (used for the rescaled
integral varifolds in Simon Ch. 8, 5.9): if `M` is countably `n`-rectifiable and `t > 0`, then so is
`σ⁻¹(M)` for `σ(y) = ξ + t y`, with exceptional set `σ⁻¹(M₀)` and parametrizations
`v ↦ t⁻¹ (F_j(v) - ξ)`. -/
theorem Submission.intcpt_ri_countablyRectifiable_similarity_preimage :
    ∀ (N n : ℕ) (ξ : Euclidean N) (t : ℝ) (M : Set (Euclidean N)), 0 < t → Chapter03.CountablyRectifiable n M → Chapter03.CountablyRectifiable n ((fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M) := by
  intro N n ξ t M ht hM
  have ht0 : t ≠ 0 := ht.ne'
  -- Step 1: `M ⊆ M₀ ∪ ⋃ j, range (F j)` with `H^n(M₀) = 0` and `F j` `K j`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  -- Step 2: `η x = t⁻¹ • (x - ξ)` is `‖t⁻¹‖₊`-Lipschitz, hence so is `η ∘ F j` up to `K j`.
  have hη : LipschitzWith ‖t⁻¹‖₊ (fun x : Euclidean N ↦ t⁻¹ • (x - ξ)) := by
    refine LipschitzWith.of_dist_le_mul fun x x' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, coe_nnnorm]
  -- Step 3: `σ⁻¹(M₀) = t⁻¹ • (-ξ + M₀)` is `H^n`-null.
  have hset : (fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M₀ =
      t⁻¹ • ((fun x : Euclidean N ↦ -ξ + x) '' M₀) := by
    ext y
    constructor
    · intro hy
      refine ⟨-ξ + (ξ + t • y), mem_image_of_mem _ hy, ?_⟩
      show t⁻¹ • (-ξ + (ξ + t • y)) = y
      rw [neg_add_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      show ξ + t • t⁻¹ • (-ξ + x) ∈ M₀
      rwa [smul_smul, mul_inv_cancel₀ ht0, one_smul, add_neg_cancel_left]
  have hnull : μHE[n] ((fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M₀) = 0 := by
    rw [hset, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero ht0),
      (isometry_add_left (-ξ)).euclideanHausdorffMeasure_image, hM₀, smul_zero]
  -- Steps 4–5: cover `σ⁻¹(M)` by `σ⁻¹(M₀)` and the ranges of `η ∘ F j`.
  refine ⟨_, hnull, fun j v ↦ t⁻¹ • (F j v - ξ), fun j ↦ ⟨‖t⁻¹‖₊ * K j, hη.comp (hK j)⟩, ?_⟩
  intro y hy
  rcases hcover hy with h0 | hrange
  · exact Or.inl h0
  · obtain ⟨j, v, hv⟩ := mem_iUnion.1 hrange
    refine Or.inr (mem_iUnion.2 ⟨j, v, ?_⟩)
    show t⁻¹ • (F j v - ξ) = y
    rw [hv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul]
/-- Weighted approximate tangent planes (Simon Ch. 3, 1.7) are local: if `O` is open and `y ∈ O`,
then `O ∩ M` has weighted approximate tangent space `P` at `y` with respect to `θ` if and only if
`M` has. -/
theorem Submission.intcpt_ri_weightedApproxTangent_inter_open_iff :
    ∀ (N n : ℕ) (O M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (y : Euclidean N)
      (P : Submodule ℝ (Euclidean N)), IsOpen O → y ∈ O →
      (Chapter03.HasWeightedApproximateTangentSpaceAt n (O ∩ M) θ y P ↔
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P) := by
  intro N n O M θ y P hO hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y hy
  -- The dimension conditions and the prescribed limits `θ(y) ∫_P f` coincide.
  unfold Chapter03.HasWeightedApproximateTangentSpaceAt
  refine and_congr Iff.rfl (forall_congr' fun f ↦ ?_)
  -- `f` vanishes off `B = closedBall 0 R` for some `R > 0`.
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hRpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : tsupport f ⊆ closedBall (0 : Euclidean N) (max R₀ 1) :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  -- The blow-up integrals for `O ∩ M` and `M` agree for `0 < r < ε / R`.
  refine tendsto_congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hRpos)] with r hr
  -- Cut-off: integrals over any `A` only see `B ∩ A`; no integrability is needed.
  have hcut : ∀ A : Set (Euclidean N),
      ∫ v in A, f v * θ (y + r • v) ∂μHE[n] =
        ∫ v in closedBall (0 : Euclidean N) (max R₀ 1) ∩ A, f v * θ (y + r • v) ∂μHE[n] := by
    intro A
    rw [← Measure.restrict_restrict measurableSet_closedBall]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv ↦ ?_).symm
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hv (hsupp h)), zero_mul]
  -- Within `B`, every blow-up point of `M` comes from `ball y ε ∩ M ⊆ O ∩ M`.
  have hset : closedBall (0 : Euclidean N) (max R₀ 1) ∩ Chapter03.blowUpMap y r '' (O ∩ M) =
      closedBall (0 : Euclidean N) (max R₀ 1) ∩ Chapter03.blowUpMap y r '' M := by
    refine Subset.antisymm (inter_subset_inter_right _ (image_mono inter_subset_right)) ?_
    rintro v ⟨hvB, z, hzM, rfl⟩
    refine ⟨hvB, z, ⟨hball ?_, hzM⟩, rfl⟩
    rw [mem_closedBall_zero_iff, Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg hr.1.le, inv_mul_le_iff₀ hr.1] at hvB
    have hrR : r * max R₀ 1 < ε := (lt_div_iff₀ hRpos).1 hr.2
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hvB hrR
  rw [hcut (Chapter03.blowUpMap y r '' (O ∩ M)), hcut (Chapter03.blowUpMap y r '' M), hset]
/-- Weighted approximate tangent planes (Simon Ch. 3, 1.7) are invariant under the similarity
`σ(w) = ξ + t w`, `t > 0`: `σ⁻¹(M)` has weighted approximate tangent space `P` at `y` with respect
to `θ ∘ σ` if and only if `M` has weighted approximate tangent space `P` at `σ(y)` with respect
to `θ`. -/
theorem Submission.intcpt_ri_weightedApproxTangent_similarity_iff :
    ∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (ξ y : Euclidean N) (t : ℝ)
      (P : Submodule ℝ (Euclidean N)), 0 < t →
      (Chapter03.HasWeightedApproximateTangentSpaceAt n ((fun w : Euclidean N ↦ ξ + t • w) ⁻¹' M)
          (fun w : Euclidean N ↦ θ (ξ + t • w)) y P ↔
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ (ξ + t • y) P) := by
  intro N n M θ ξ y t P ht
  have ht0 : t ≠ 0 := ht.ne'
  -- Blow-up sets: `η_{y,r}(σ⁻¹ M) = η_{σ(y),tr}(M)` for every `r` (also `r = 0`, as `0⁻¹ = 0`).
  have hset : ∀ r : ℝ, Chapter03.blowUpMap y r '' ((fun w : Euclidean N ↦ ξ + t • w) ⁻¹' M) =
      Chapter03.blowUpMap (ξ + t • y) (t * r) '' M := by
    intro r
    ext v
    simp only [mem_image, mem_preimage, Chapter03.blowUpMap]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨ξ + t • w, hw, ?_⟩
      rw [add_sub_add_left_eq_sub, ← smul_sub, smul_smul, mul_inv, mul_comm t⁻¹ r⁻¹, mul_assoc,
        inv_mul_cancel₀ ht0, mul_one]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨t⁻¹ • (z - ξ), ?_, ?_⟩
      · rwa [smul_smul, mul_inv_cancel₀ ht0, one_smul, add_sub_cancel]
      · have hw : t⁻¹ • (z - ξ) - y = t⁻¹ • (z - (ξ + t • y)) := by
          rw [sub_add_eq_sub_sub, smul_sub t⁻¹ (z - ξ) (t • y), smul_smul, inv_mul_cancel₀ ht0,
            one_smul]
        rw [hw, smul_smul, mul_inv, mul_comm t⁻¹ r⁻¹]
  -- `r ↦ t r` maps `𝓝[>] 0` onto itself, so it does not change limits along `𝓝[>] 0`.
  have hmap : map (fun r : ℝ ↦ t * r) (𝓝[>] (0 : ℝ)) = 𝓝[>] 0 := by
    have hsurj : Function.Surjective (fun r : ℝ ↦ t * r) := fun s ↦
      ⟨t⁻¹ * s, by simp only [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]⟩
    conv_lhs => rw [← comap_mulLeft_nhdsGT_zero ht]
    exact map_comap_of_surjective hsurj _
  have key : ∀ (G : ℝ → ℝ) (L : Filter ℝ),
      Tendsto (G ∘ fun r : ℝ ↦ t * r) (𝓝[>] 0) L ↔ Tendsto G (𝓝[>] 0) L := by
    intro G L
    rw [← tendsto_map'_iff, hmap]
  -- With `σ(y + r v) = σ(y) + (t r) v`, the blow-up integral for `σ⁻¹(M)` at scale `r` is the one
  -- for `M` at scale `t r`; the limits `θ(σ(y)) ∫_P f` agree.
  unfold Chapter03.HasWeightedApproximateTangentSpaceAt
  refine and_congr Iff.rfl (forall_congr' fun f ↦ ?_)
  refine Iff.trans ?_ (key (fun s : ℝ ↦ ∫ v in Chapter03.blowUpMap (ξ + t • y) s '' M,
    f v * θ (ξ + t • y + s • v) ∂μHE[n]) _)
  refine Filter.tendsto_congr fun r ↦ ?_
  simp only [Function.comp_apply]
  rw [hset r]
  simp only [smul_add, smul_smul, add_assoc]
/-- Rescaled restrictions of integral varifolds are integral (Simon Ch. 8, 5.9): if `V = v(M, θ)` is
an integral `n`-varifold on `U`, `t > 0`, the similarity `σ(y) = ξ + t y` maps `O` into `U`, and `W`
is `η_{ξ,t #} V` restricted to `Gₙ(O)`, then `W = v(O ∩ σ⁻¹(M), θ ∘ σ)` is integral. -/
theorem Submission.intcpt_rescaled_restriction_integral :
    ∀ (N n : ℕ) (U O : Set (Euclidean N)) (V : Varifold N n U) (W : Varifold N n O) (ξ : Euclidean N) (t : ℝ), 0 < t → (∀ y ∈ O, ξ + t • y ∈ U) → IsIntegral V → W.measure = (rescaledMeasure V ξ t).restrict (O ×ˢ (univ : Set (Grassmannian N n))) → IsIntegral W := by
  intro N n U O V W ξ t ht hσU hV hW
  have ht0 : t ≠ 0 := ht.ne'
  obtain ⟨M, θ, ⟨-, hMmeas, hMrect, hθpos, hθint, hVrep⟩, hθnat⟩ := hV
  -- Step 1: `σ(y) = ξ + t y` is a homeomorphism with inverse `x ↦ t⁻¹ (x - ξ)`, hence a measurable
  -- embedding, and `H^n ⌞ σ(A) = t^n σ_# (H^n ⌞ A)` for every set `A`.
  have hη : ∀ y : Euclidean N, t⁻¹ • (ξ + t • y - ξ) = y := fun y ↦ by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hσsurj : Function.Surjective (fun y : Euclidean N ↦ ξ + t • y) := fun x ↦
    ⟨t⁻¹ • (x - ξ), by simp only [smul_smul, mul_inv_cancel₀ ht0, one_smul, add_sub_cancel]⟩
  have hσemb : MeasurableEmbedding (fun y : Euclidean N ↦ ξ + t • y) :=
    ((Homeomorph.smulOfNeZero t ht0).trans (Homeomorph.addLeft ξ)).measurableEmbedding
  have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht n)).ne'
  have hrestr := Submission.intcpt_ri_restrict_similarity_image N n ξ t
  -- Step 2: `σ` is quasi-measure-preserving for `H^n`, as `H^n = t^n σ_# H^n`.
  have hqmp : Measure.QuasiMeasurePreserving (fun y : Euclidean N ↦ ξ + t • y)
      (μHE[n] : Measure (Euclidean N)) μHE[n] := by
    have h := hrestr univ ht
    rw [image_univ_of_surjective hσsurj, Measure.restrict_univ] at h
    have hac := Measure.absolutelyContinuous_smul (μ := (μHE[n] : Measure (Euclidean N)).map
      (fun y : Euclidean N ↦ ξ + t • y)) hc0
    rw [← h] at hac
    exact ⟨hσemb.measurable, hac⟩
  -- Step 3: approximate tangent planes of `O ∩ σ⁻¹(M)` at `y ∈ O` are those of `M` at `σ(y)`.
  have htan : ∀ y ∈ O, ∀ P : Submodule ℝ (Euclidean N),
      Chapter03.HasWeightedApproximateTangentSpaceAt n (O ∩ (fun w : Euclidean N ↦ ξ + t • w) ⁻¹' M)
          (fun w : Euclidean N ↦ θ (ξ + t • w)) y P ↔
        Chapter03.HasWeightedApproximateTangentSpaceAt n M θ (ξ + t • y) P := fun y hy P ↦
    (Submission.intcpt_ri_weightedApproxTangent_inter_open_iff N n O _ _ y P W.isOpen_domain
      hy).trans (Submission.intcpt_ri_weightedApproxTangent_similarity_iff N n M θ ξ y t P ht)
  -- Step 4: change of variables `∫_E θ ∘ σ dH^n = t^{-n} ∫_{σ(E)} θ dH^n`.
  have hchange : ∀ E : Set (Euclidean N),
      ∫⁻ y in E, ENNReal.ofReal (θ (ξ + t • y)) ∂μHE[n] =
        ENNReal.ofReal (t⁻¹ ^ n) *
          ∫⁻ x in (fun y : Euclidean N ↦ ξ + t • y) '' E, ENNReal.ofReal (θ x) ∂μHE[n] := by
    intro E
    rw [hrestr E ht, lintegral_smul_measure, hσemb.lintegral_map, smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 ht.le) n), ← mul_pow, inv_mul_cancel₀ ht0,
      one_pow, ENNReal.ofReal_one, one_mul]
  refine ⟨O ∩ (fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M, fun y ↦ θ (ξ + t • y),
    ⟨inter_subset_left, W.isOpen_domain.measurableSet.nullMeasurableSet.inter
      (hMmeas.preimage hqmp),
      (Submission.intcpt_ri_countablyRectifiable_similarity_preimage N n ξ t M ht hMrect).mono
        inter_subset_right,
      fun y hy ↦ hθpos _ hy.2, ?_, ?_⟩, ?_⟩
  · -- Step 5: local integrability, from `θ ∈ L¹(H^n ⌞ M ∩ σ(K))` with `σ(K) ⊆ U` compact.
    intro K hK hKO
    have hσK : (fun y : Euclidean N ↦ ξ + t • y) '' K ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      exact hσU y (hKO hy)
    have hθK := hθint _ (hK.image (show Continuous (fun y : Euclidean N ↦ ξ + t • y) by fun_prop))
      hσK
    rw [← image_preimage_inter, IntegrableOn, hrestr _ ht,
      integrable_smul_measure hc0 ENNReal.ofReal_ne_top, hσemb.integrable_map_iff] at hθK
    have hset : (O ∩ (fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M) ∩ K =
        (fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M ∩ K :=
      Subset.antisymm (fun y hy ↦ ⟨hy.1.2, hy.2⟩) (fun y hy ↦ ⟨⟨hKO hy.2, hy.1⟩, hy.2⟩)
    rw [hset]
    exact hθK
  · -- Step 6: `W(A) = t^{-n} V(Φ⁻¹(A ∩ Gₙ(O)))`, `Φ(x, S) = (t⁻¹ (x - ξ), S)`, and the carrier of
    -- `V` there is the `σ`-image of the carrier of `W` in `A`.
    intro A hA
    have hOA : MeasurableSet (A ∩ O ×ˢ (univ : Set (Grassmannian N n))) :=
      hA.inter (W.isOpen_domain.measurableSet.prod MeasurableSet.univ)
    have hΦ : Measurable (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) := by
      fun_prop
    rw [hW, Measure.restrict_apply hA, rescaledMeasure, Measure.smul_apply,
      Measure.map_apply hΦ hOA, smul_eq_mul, hVrep _ (hΦ hOA), hchange]
    refine congrArg (fun s ↦ ENNReal.ofReal (t⁻¹ ^ n) * ∫⁻ x in s, ENNReal.ofReal (θ x) ∂μHE[n])
      ((image_preimage_eq _ hσsurj).symm.trans (congrArg _ ?_))
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, hη]
    constructor
    · rintro ⟨hyM, S, hS, hyA, hyO⟩
      exact ⟨⟨hyO, hyM⟩, S, (htan y hyO _).2 hS, hyA⟩
    · rintro ⟨⟨hyO, hyM⟩, S, hS, hyA⟩
      exact ⟨hyM, S, (htan y hyO _).1 hS, hyA, hyO⟩
  · -- Step 7: `θ ∘ σ ∈ ℕ` a.e. on `σ⁻¹(M) ⊇ O ∩ σ⁻¹(M)`, since `H^n ⌞ M = t^n σ_# (H^n ⌞ σ⁻¹(M))`.
    have h := hrestr ((fun y : Euclidean N ↦ ξ + t • y) ⁻¹' M) ht
    rw [image_preimage_eq M hσsurj] at h
    rw [h, Measure.ae_ennreal_smul_measure_iff hc0, hσemb.ae_map_iff] at hθnat
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_right hθnat

/-- The diagonal blow-up in the proof of **Simon Ch. 8, 5.9** (printed steps (3)–(4); node
`diagonal_blowup` of `integral_compactness`), restricted to the fixed ball `B°_5(0)`.  Let
`V_i → V` with each `V_i` integral of locally bounded first variation, let `V` have tangent plane
`P` with multiplicity `θ₀` at `ξ`, and let `liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ c ρ^n` for `0 < ρ < r`.
For scales `λ_k ↓ 0` and well-chosen indices `i_k`, the blow-ups
`W_k = (V_{i_k})_{ξ,λ_k} ⌞ (B°_5(0) × G)` are integral varifolds on `B°_5(0)` with locally bounded
first variation, `‖δW_k‖(B°_5(0)) ≤ 2 max(c,1) 5^n λ_k → 0`, and `W_k → θ₀ v(P)` on
`B°_5(0) × G`. -/
theorem Submission.intcpt_diagonal_integral_blowup :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U)
      (ξ : Euclidean N) (P : Grassmannian N n) (θ₀ c r : ℝ), Varifold.RadonConverges Vi V →
      (∀ i, IsIntegral (Vi i)) → (∀ i, (Vi i).HasLocallyBoundedFirstVariation) →
      HasTangentPlane V ξ P θ₀ → 0 < r →
      (∀ ρ : ℝ, 0 < ρ → ρ < r →
        liminf (fun i ↦ variationMeasure (Vi i) (closedBall ξ ρ)) atTop ≤
          ENNReal.ofReal (c * ρ ^ n)) →
      ∃ W : ℕ → Varifold N n (ball (0 : Euclidean N) 5), (∀ k, IsIntegral (W k)) ∧
        (∀ k, (W k).HasLocallyBoundedFirstVariation) ∧
        Tendsto (fun k ↦ variationMeasure (W k) (ball (0 : Euclidean N) 5)) atTop (𝓝 0) ∧
        ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ),
          tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) →
          Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop
            (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P))) := by
  intro N n U Vi V ξ P θ₀ c r hconv hint hlbfv htan hr hlim
  obtain ⟨hξU, -, htanf⟩ := htan
  set O : Set (Euclidean N) := ball (0 : Euclidean N) 5 with hO
  -- A ball `B°_ε(ξ) ⊆ U`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp V.isOpen_domain ξ hξU
  -- The scales `λ_k = δ₀ / (k + 1)`: `5 λ_k < r`, `6 λ_k < ε` and `λ_k → 0⁺`.
  set δ₀ : ℝ := min r ε / 7 with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  set lam : ℕ → ℝ := fun k ↦ δ₀ * (1 / ((k : ℝ) + 1)) with hlam
  have hlampos : ∀ k, 0 < lam k := fun k ↦ by positivity
  have hlamle : ∀ k, lam k ≤ δ₀ := by
    intro k
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc lam k = δ₀ * (1 / ((k : ℝ) + 1)) := rfl
      _ ≤ δ₀ * 1 := mul_le_mul_of_nonneg_left h1 hδ₀pos.le
      _ = δ₀ := mul_one _
  have hlamr : ∀ k, lam k * 5 < r := by
    intro k
    have : δ₀ * 5 < r := by
      have := min_le_left r ε
      rw [hδ₀]; nlinarith
    nlinarith [hlamle k]
  have hlamε : ∀ k, lam k * 6 < ε := by
    intro k
    have : δ₀ * 6 < ε := by
      have := min_le_right r ε
      rw [hδ₀]; nlinarith
    nlinarith [hlamle k]
  have hlamlim : Tendsto lam atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul δ₀
    simpa [hlam] using this
  have hlamwithin : Tendsto lam atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlamlim, Eventually.of_forall hlampos⟩
  -- Points of `B_6(0)` blow down into `U`.
  have hinU : ∀ k (y : Euclidean N), ‖y‖ ≤ 6 → ξ + lam k • y ∈ U := by
    intro k y hy
    apply hεU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hlampos k)]
    calc lam k * ‖y‖ ≤ lam k * 6 := mul_le_mul_of_nonneg_left hy (hlampos k).le
      _ < ε := hlamε k
  have hballU : ∀ k, ∀ y ∈ O, ξ + lam k • y ∈ U := by
    intro k y hy
    apply hinU
    rw [hO, mem_ball, dist_zero_right] at hy
    linarith
  -- A cut-off `χ ∈ C_c` with `0 ≤ χ ≤ 1`, `χ = 1` on `B_5(0) × G` and `χ = 0` off `B°_6(0) × G`.
  obtain ⟨χ0, hχ1, hχ0, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact
    (X := Euclidean N × Grassmannian N n)
    (s := closedBall (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)))
    (t := (ball (0 : Euclidean N) 6)ᶜ ×ˢ (univ : Set (Grassmannian N n)))
    ((isCompact_closedBall _ _).prod isCompact_univ)
    (isOpen_ball.isClosed_compl.prod isClosed_univ)
    (by
      rw [Set.disjoint_left]
      rintro z ⟨hz, -⟩ ⟨hz', -⟩
      exact hz' (closedBall_subset_ball (by norm_num) hz))
  let χ : C_c(Euclidean N × Grassmannian N n, ℝ) := ⟨χ0, hχc⟩
  have hχnn : ∀ z, 0 ≤ χ z := fun z ↦ (hχI z).1
  have hχone : ∀ z ∈ O ×ˢ (univ : Set (Grassmannian N n)), χ z = 1 := by
    intro z hz
    exact hχ1 ⟨ball_subset_closedBall hz.1, trivial⟩
  have hχsupp : ∀ z ∈ tsupport χ, ‖z.1‖ ≤ 6 := by
    have hsub : tsupport χ ⊆
        closedBall (0 : Euclidean N) 6 ×ˢ (univ : Set (Grassmannian N n)) := by
      apply closure_minimal _ (isClosed_closedBall.prod isClosed_univ)
      intro z hz
      refine ⟨?_, trivial⟩
      by_contra h
      apply hz
      exact hχ0 ⟨fun h' ↦ h (ball_subset_closedBall h'), trivial⟩
    intro z hz
    simpa using (hsub hz).1
  have hχU : ∀ k, ∀ z ∈ tsupport χ, ξ + lam k • z.1 ∈ U :=
    fun k z hz ↦ hinU k z.1 (hχsupp z hz)
  -- The countable dense family `g` of tests supported in `B°_5(0) × G` (step 1).
  obtain ⟨g, hgsupp, hgdense⟩ := Submission.intcpt_diag_ball_cc_dense_seq N n 5 (by norm_num)
  have hgU : ∀ k m, ∀ z ∈ tsupport (g m), ξ + lam k • z.1 ∈ U := by
    intro k m z hz
    apply hinU
    have := (hgsupp m hz).1
    rw [mem_ball, dist_zero_right] at this
    linarith
  set c' : ℝ := max c 1 with hc'
  have hc'pos : 0 < c' := lt_of_lt_of_le one_pos (le_max_right c 1)
  -- Choice of the indices `i_k` (step 3): (v) the variation bound holds frequently in `i`, while
  -- (vi) and the mass bound (vii) hold eventually in `i`, because blow-ups preserve the
  -- convergence `V_i → V`.
  have hsel : ∀ k, ∃ i, variationMeasure (Vi i) (closedBall ξ (lam k * 5)) <
        ENNReal.ofReal (2 * c' * (lam k * 5) ^ n) ∧
      (∀ m ∈ Finset.range (k + 1), |∫ z, g m z ∂(rescaledMeasure (Vi i) ξ (lam k)) -
          ∫ z, g m z ∂(rescaledMeasure V ξ (lam k))| < 1 / ((k : ℝ) + 1)) ∧
      ∫ z, χ z ∂(rescaledMeasure (Vi i) ξ (lam k)) <
        ∫ z, χ z ∂(rescaledMeasure V ξ (lam k)) + 1 := by
    intro k
    have hρ : 0 < lam k * 5 := by have := hlampos k; positivity
    have hv : ∃ᶠ i in atTop, variationMeasure (Vi i) (closedBall ξ (lam k * 5)) <
        ENNReal.ofReal (2 * c' * (lam k * 5) ^ n) := by
      have hp : 0 < c' * (lam k * 5) ^ n := by positivity
      have hlt : liminf (fun i ↦ variationMeasure (Vi i) (closedBall ξ (lam k * 5))) atTop <
          ENNReal.ofReal (2 * c' * (lam k * 5) ^ n) := by
        refine lt_of_le_of_lt (hlim _ hρ (hlamr k)) ?_
        calc ENNReal.ofReal (c * (lam k * 5) ^ n) ≤ ENNReal.ofReal (c' * (lam k * 5) ^ n) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left c 1) (by positivity))
          _ < ENNReal.ofReal (2 * c' * (lam k * 5) ^ n) := by
              rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
              nlinarith
      exact frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    have hvi : ∀ᶠ i in atTop, ∀ m ∈ Finset.range (k + 1),
        |∫ z, g m z ∂(rescaledMeasure (Vi i) ξ (lam k)) -
          ∫ z, g m z ∂(rescaledMeasure V ξ (lam k))| < 1 / ((k : ℝ) + 1) := by
      rw [Filter.eventually_all_finset]
      intro m _
      have ht := Submission.intcpt_diag_rescaled_radon_tendsto N n U Vi V ξ (lam k) (g m) hconv
        (hlampos k) (hgU k m)
      have := Metric.tendsto_nhds.mp ht (1 / ((k : ℝ) + 1)) (by positivity)
      filter_upwards [this] with i hi
      simpa [Real.dist_eq] using hi
    have hvii : ∀ᶠ i in atTop, ∫ z, χ z ∂(rescaledMeasure (Vi i) ξ (lam k)) <
        ∫ z, χ z ∂(rescaledMeasure V ξ (lam k)) + 1 := by
      have ht := Submission.intcpt_diag_rescaled_radon_tendsto N n U Vi V ξ (lam k) χ hconv
        (hlampos k) (hχU k)
      exact ht.eventually_lt_const (lt_add_one _)
    exact (hv.and_eventually (hvi.and hvii)).exists
  choose i hi using hsel
  -- The varifolds `W_k = (V_{i_k})_{ξ,λ_k} ⌞ (B°_5(0) × G)` (steps 4 and 6).
  have hD : ∀ k, ∃ W : Varifold N n O,
      W.measure = (rescaledMeasure (Vi (i k)) ξ (lam k)).restrict
        (O ×ˢ (univ : Set (Grassmannian N n))) ∧ W.HasLocallyBoundedFirstVariation ∧
      variationMeasure W O ≤ ENNReal.ofReal ((lam k)⁻¹ ^ n * lam k) *
        variationMeasure (Vi (i k)) (closedBall ξ (lam k * 5)) :=
    fun k ↦ Submission.intcpt_diag_blowup_variation_bound N n U (Vi (i k)) ξ (lam k) 5
      (hlbfv _) (hlampos k) (by norm_num) (hballU k)
  choose W hWmeas hWlbfv hWvar using hD
  refine ⟨W, fun k ↦ ?_, hWlbfv, ?_, ?_⟩
  · -- Integrality (step 5).
    exact Submission.intcpt_rescaled_restriction_integral N n U O (Vi (i k)) (W k) ξ (lam k)
      (hlampos k) (hballU k) (hint _) (hWmeas k)
  · -- `‖δW_k‖(B°_5(0)) ≤ 2 c' 5^n λ_k → 0` (step 6(b)).
    have hbound : ∀ k, variationMeasure (W k) O ≤ ENNReal.ofReal (2 * c' * 5 ^ n * lam k) := by
      intro k
      refine (hWvar k).trans ?_
      calc ENNReal.ofReal ((lam k)⁻¹ ^ n * lam k) *
            variationMeasure (Vi (i k)) (closedBall ξ (lam k * 5))
          ≤ ENNReal.ofReal ((lam k)⁻¹ ^ n * lam k) *
            ENNReal.ofReal (2 * c' * (lam k * 5) ^ n) := by gcongr; exact (hi k).1.le
        _ = ENNReal.ofReal ((lam k)⁻¹ ^ n * lam k * (2 * c' * (lam k * 5) ^ n)) :=
            (ENNReal.ofReal_mul (p := (lam k)⁻¹ ^ n * lam k)
              (q := 2 * c' * (lam k * 5) ^ n) (by have := hlampos k; positivity)).symm
        _ = ENNReal.ofReal (2 * c' * 5 ^ n * lam k) := by
            congr 1
            have hl := (hlampos k).ne'
            rw [mul_pow, inv_pow]
            field_simp
    have hupper : Tendsto (fun k ↦ ENNReal.ofReal (2 * c' * 5 ^ n * lam k)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hlamlim.const_mul (2 * c' * 5 ^ n))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ ↦ zero_le) hbound
  · -- Convergence to `θ₀ v(P)` (step 7): compare `W_k` with `V_{ξ,λ_k}` on the dense family,
    -- extend to all admissible tests by the uniform mass bound, and use the tangent plane.
    intro f hf
    set A : ℝ := θ₀ * ∫ z, χ z ∂(planeVarifoldMeasure P) with hA
    have hχtan : ∀ᶠ k in atTop, ∫ z, χ z ∂(rescaledMeasure V ξ (lam k)) < A + 1 :=
      ((htanf χ).comp hlamwithin).eventually_lt_const (lt_add_one _)
    -- The mass of `B°_5(0) × G` under a blow-up is at most the `χ`-integral.
    have hmass : ∀ (V' : Varifold N n U) (k : ℕ),
        rescaledMeasure V' ξ (lam k) (O ×ˢ (univ : Set (Grassmannian N n))) ≤
          ENNReal.ofReal (∫ z, χ z ∂(rescaledMeasure V' ξ (lam k))) := by
      intro V' k
      have hint' :=
        Submission.intcpt_diag_rescaled_integrable N n U V' ξ (lam k) χ (hlampos k) (hχU k)
      rw [ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall hχnn),
        ← lintegral_indicator_one (measurableSet_ball.prod MeasurableSet.univ)]
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ O ×ˢ (univ : Set (Grassmannian N n))
      · show (O ×ˢ (univ : Set (Grassmannian N n))).indicator 1 z ≤ ENNReal.ofReal (χ z)
        rw [indicator_of_mem hz, hχone z hz]; simp
      · show (O ×ˢ (univ : Set (Grassmannian N n))).indicator 1 z ≤ ENNReal.ofReal (χ z)
        rw [indicator_of_notMem hz]; exact zero_le
    have hmassμ : ∀ᶠ k in atTop,
        (W k).measure (O ×ˢ (univ : Set (Grassmannian N n))) ≤ ENNReal.ofReal (A + 2) := by
      filter_upwards [hχtan] with k hk
      rw [hWmeas k, Measure.restrict_apply_self]
      refine (hmass (Vi (i k)) k).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [(hi k).2.2]
    have hmassν : ∀ᶠ k in atTop,
        rescaledMeasure V ξ (lam k) (O ×ˢ (univ : Set (Grassmannian N n))) ≤
          ENNReal.ofReal (A + 2) := by
      filter_upwards [hχtan] with k hk
      refine (hmass V k).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    have hrestrict : ∀ (h : C_c(Euclidean N × Grassmannian N n, ℝ)),
        tsupport h ⊆ O ×ˢ (univ : Set (Grassmannian N n)) → ∀ k,
        ∫ z, h z ∂(W k).measure = ∫ z, h z ∂(rescaledMeasure (Vi (i k)) ξ (lam k)) := by
      intro h hh k
      rw [hWmeas k]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h' ↦ hz (hh h')))
    have hconvg : ∀ m, Tendsto (fun k ↦ ∫ z, g m z ∂(W k).measure -
        ∫ z, g m z ∂(rescaledMeasure V ξ (lam k))) atTop (𝓝 0) := by
      intro m
      apply squeeze_zero_norm' _ tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop m] with k hk
      rw [hrestrict (g m) (hgsupp m) k, Real.norm_eq_abs]
      exact ((hi k).2.1 m (Finset.mem_range.mpr (by omega))).le
    have hdiff := Submission.intcpt_diag_dense_family_tendsto N n O g (fun k ↦ (W k).measure)
      (fun k ↦ rescaledMeasure V ξ (lam k)) (ENNReal.ofReal (A + 2)) measurableSet_ball
      ENNReal.ofReal_ne_top hgsupp hgdense hmassμ hmassν hconvg f hf
    have hb := (htanf f).comp hlamwithin
    have := hdiff.add hb
    simpa using this
/-- **Simon Ch. 8, proof of 5.10, p. 221, the Besicovitch step** (child `marginal_measure` of
`bad_set_bound`): for any measure `m` on `ℝ^N × G(N,n)` and any `g : ℝ^N × G(N,n) → [0,∞]`, the
functional `A ↦ ∫_{A × G(N,n)} g dm` agrees on Borel sets `A ⊆ ℝ^N` with a measure, namely the
image of `m ⌞ g` under `(x, S) ↦ x`; so it is monotone and countably additive there. -/
theorem Submission.intcpt_allard_bsb_marginal_measure :
    ∀ (N n : ℕ) (m : Measure (Euclidean N × Grassmannian N n))
      (g : Euclidean N × Grassmannian N n → ℝ≥0∞), ∃ τ : Measure (Euclidean N),
      ∀ A : Set (Euclidean N), MeasurableSet A →
        τ A = ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), g z ∂m := by
  intro N n m g
  refine ⟨(m.withDensity g).map Prod.fst, fun A hA ↦ ?_⟩
  -- `τ(A) = (m ⌞ g)(Prod.fst ⁻¹' A) = (m ⌞ g)(A × G(N,n))`; `withDensity_apply` needs only
  -- `A × G(N,n)` to be measurable, not `g`.
  rw [Measure.map_apply measurable_fst hA, ← prod_univ,
    withDensity_apply g (hA.prod MeasurableSet.univ)]
/-- Simon Ch. 8, proof of Lemma 5.10, printed (6): if `θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for
`σ ∈ (0,1)` (D) and the cylinder ratios satisfy the comparison (C) with error `Kερ/τ`, then for
`τ ∈ (0,1/4]` and `σ ∈ (0,1)`, `θ ≤ (e^ε μ(U^{4τ}_σ(y))/σ^n + Kεσ/τ)/ω_n`, where
`U^t_r(y) = B_r(y) ∩ {z : |q(z - y)| < t}` and `q(v) = v - p_P(v)`.  Since `|q(v)| ≤ |v|`, the
ball `B_r(y)` lies in `U^t_r(y)` for `r < t`; for `σ ≤ τ` apply (D) at `σ`, and for `τ < σ` apply
(D) at `τ` and then (C) with parameter `2τ` and radii `τ ≤ σ`, using `e^ε ≤ 2`. -/
theorem Submission.intcpt_allard_fdsb_density_cylinder_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (θ : ℝ≥0∞) (ε K : ℝ), 0 ≤ ε → Real.exp ε ≤ 2 → 0 ≤ K → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → (∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → θ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
  intro N n μ P y θ ε K hε hexp hK hD hC τ σ hτ hτ4 hσ hσ1
  -- Step 1: `|q(v)| ≤ |v|`, by Pythagoras, as `p = p_P` is symmetric and idempotent.
  have hq : ∀ v : Euclidean N, ‖v - Grassmannian.project P v‖ ≤ ‖v‖ := by
    intro v
    have hpp : inner ℝ (Grassmannian.project P v) (Grassmannian.project P v) =
        inner ℝ (Grassmannian.project P v) v := by
      calc inner ℝ (Grassmannian.project P v) (Grassmannian.project P v)
          = inner ℝ (Grassmannian.project P (Grassmannian.project P v)) v :=
            (Grassmannian.projectionLinearMap_isSymmetric P _ _).symm
        _ = inner ℝ (Grassmannian.project P v) v := by rw [Grassmannian.project_project]
    have h0 : inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) = (0 : ℝ) := by
      rw [inner_sub_right, hpp, sub_self]
    have h := norm_add_sq_real (Grassmannian.project P v) (v - Grassmannian.project P v)
    rw [add_sub_cancel, h0, mul_zero, add_zero] at h
    nlinarith [norm_nonneg v, norm_nonneg (v - Grassmannian.project P v),
      sq_nonneg ‖Grassmannian.project P v‖]
  -- Step 2: `B_r(y) ⊆ U^t_r(y)` whenever `r < t`.
  have hball : ∀ r t : ℝ, r < t →
      closedBall y r ⊆ closedBall y r ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < t} := by
    intro r t hrt z hz
    refine ⟨hz, ?_⟩
    show ‖(z - y) - Grassmannian.project P (z - y)‖ < t
    calc ‖(z - y) - Grassmannian.project P (z - y)‖ ≤ ‖z - y‖ := hq _
      _ = dist z y := (dist_eq_norm z y).symm
      _ ≤ r := mem_closedBall.mp hz
      _ < t := hrt
  -- Steps 3–4: by (D), `θ ≤ e^ε (μ(B_r(y))/r^n)/ω_n` for `r ∈ (0,1)`.
  have hθ : ∀ r : ℝ, 0 < r → r < 1 → θ ≤ ENNReal.ofReal (Real.exp ε) *
      (μ (closedBall y r) / ENNReal.ofReal r ^ n) / unitBallVolume n := by
    intro r hr hr1
    have hrn0 : ENNReal.ofReal r ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne'
    have hrnt : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hdr : densityRatio n μ y r =
        μ (closedBall y r) / ENNReal.ofReal r ^ n / unitBallVolume n := by
      rw [densityRatio, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inr hrnt) (Or.inr hrn0)]
      ring
    have hexp_le : ENNReal.ofReal (Real.exp (ε * r)) ≤ ENNReal.ofReal (Real.exp ε) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    calc θ ≤ ENNReal.ofReal (Real.exp (ε * r)) * densityRatio n μ y r := hD r hr hr1
      _ ≤ ENNReal.ofReal (Real.exp ε) * densityRatio n μ y r := by gcongr
      _ = ENNReal.ofReal (Real.exp ε) * (μ (closedBall y r) / ENNReal.ofReal r ^ n) /
          unitBallVolume n := by rw [hdr, mul_div_assoc]
  rcases le_or_gt σ τ with hστ | hτσ
  · -- Step 5, case `σ ≤ τ`: (D) at `σ`, and `B_σ(y) ⊆ U^{4τ}_σ(y)`.
    calc θ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ) / ENNReal.ofReal σ ^ n) /
          unitBallVolume n := hθ σ hσ hσ1
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) /
          unitBallVolume n := by
        gcongr
        exact hball σ (4 * τ) (by linarith)
      _ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        gcongr
        exact le_self_add
  · -- Step 6, case `τ < σ`: (D) at `τ`, `B_τ(y) ⊆ U^{2τ}_τ(y)`, and (C) with parameter `2τ` and
    -- radii `τ ≤ σ`; the error is `e^ε Kεσ/(2τ) ≤ Kεσ/τ` as `e^ε ≤ 2`.
    have hC' := hC (2 * τ) τ σ (by linarith) (by linarith) hτ hτσ.le hσ1
    rw [show (2 : ℝ) * (2 * τ) = 4 * τ by ring] at hC'
    have herr : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (K * ε * σ / (2 * τ)) ≤
        ENNReal.ofReal (K * ε * σ / τ) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      apply ENNReal.ofReal_le_ofReal
      have hA : 0 ≤ K * ε * σ / τ := by positivity
      rw [show K * ε * σ / (2 * τ) = K * ε * σ / τ / 2 by rw [div_div, mul_comm τ 2]]
      nlinarith
    calc θ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y τ) / ENNReal.ofReal τ ^ n) /
          unitBallVolume n := hθ τ hτ (hτσ.trans hσ1)
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y τ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal τ ^ n) /
          unitBallVolume n := by
        gcongr
        exact hball τ (2 * τ) (by linarith)
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n +
          ENNReal.ofReal (K * ε * σ / (2 * τ))) / unitBallVolume n := by
        gcongr
      _ = (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (K * ε * σ / (2 * τ))) /
          unitBallVolume n := by rw [mul_add]
      _ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        gcongr
/-- Simon Ch. 8, proof of Lemma 5.10 (one-point case of Remark 5.11 (∗)): if
`θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for every `σ ∈ (0,1)`, where `0 < δ ≤ 1/2`, `2^{n+2} δ ≤ 1`,
`0 < ε ≤ δ⁴` and `|y - x| < ε`, then `θ ≤ (1 + δ) μ(B_1(x))/ω_n`.  Take `σ = 1 - ε`, so that
`B_σ(y) ⊆ B_1(x)`; then `e^{ε(1-ε)} ≤ e^ε ≤ 1 + 2ε`, `(1 - ε)^{-n} ≤ (1 + 2ε)^n ≤ 1 + (2^n - 1)2ε`,
and `e^{ε(1-ε)} (1 - ε)^{-n} ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ`. -/
theorem Submission.intcpt_allard_fdsb_one_point_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (θ : ℝ≥0∞) (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 2 ^ (n + 2) * δ ≤ 1 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → θ ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n := by
  intro N n μ x y θ δ ε hδ hδ2 hnδ hε hε4 hyx hD
  -- Step 1: `ε ≤ δ⁴ ≤ δ² ≤ 1/4`.
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hεδ : ε ≤ δ ^ 2 := hε4.trans (by nlinarith [pow_pos hδ 2])
  have hε14 : ε ≤ 1 / 4 := hεδ.trans hδsq
  -- Step 2: `σ = 1 - ε ∈ (0,1)` and `B_{1-ε}(y) ⊆ B_1(x)`.
  have hσ : 0 < 1 - ε := by linarith
  have hball : closedBall y (1 - ε) ⊆ closedBall x 1 :=
    closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith)
  -- Step 3: `e^{ε(1-ε)} ≤ e^ε ≤ 1 + 2ε`, by `|e^t - 1| ≤ 2|t|` for `|t| ≤ 1`.
  have hexp : Real.exp (ε * (1 - ε)) ≤ 1 + 2 * ε := by
    have h1 : Real.exp (ε * (1 - ε)) ≤ Real.exp ε := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε]; linarith)
    rw [abs_of_pos hε] at h2
    linarith [le_abs_self (Real.exp ε - 1)]
  -- Step 4: `(1 - ε)⁻¹ ≤ 1 + 2ε`, as `(1 - ε)(1 + 2ε) = 1 + ε(1 - 2ε) ≥ 1`.
  have hinv : (1 - ε)⁻¹ ≤ 1 + 2 * ε := by
    rw [inv_eq_one_div, div_le_iff₀ hσ]
    nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
  -- Step 5: `(1 + u)^m ≤ 1 + (2^m - 1)u` for `u = 2ε ∈ [0,1]`, by induction on `m`.
  have hbern : ∀ m : ℕ, (1 + 2 * ε) ^ m ≤ 1 + (2 ^ m - 1) * (2 * ε) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      calc (1 + 2 * ε) ^ (k + 1) = (1 + 2 * ε) ^ k * (1 + 2 * ε) := pow_succ _ _
        _ ≤ (1 + (2 ^ k - 1) * (2 * ε)) * (1 + 2 * ε) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + (2 ^ (k + 1) - 1) * (2 * ε) := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2k) hε.le)
            (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
  -- Step 6: `((1 - ε)^n)⁻¹ = ((1 - ε)⁻¹)^n ≤ (1 + 2ε)^n ≤ 1 + (2^n - 1)2ε`.
  have hpowinv : ((1 - ε) ^ n)⁻¹ ≤ 1 + (2 ^ n - 1) * (2 * ε) := by
    rw [← inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hσ.le) hinv n).trans (hbern n)
  -- Step 7: `e^{ε(1-ε)}/(1 - ε)^n ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ`.
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [show (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n by ring] at hnδ
  have hreal : Real.exp (ε * (1 - ε)) / (1 - ε) ^ n ≤ 1 + δ := by
    rw [div_eq_mul_inv]
    calc Real.exp (ε * (1 - ε)) * ((1 - ε) ^ n)⁻¹
        ≤ (1 + 2 * ε) * (1 + (2 ^ n - 1) * (2 * ε)) :=
          mul_le_mul hexp hpowinv (inv_nonneg.mpr (pow_nonneg hσ.le n)) (by linarith)
      _ ≤ 1 + 4 * 2 ^ n * ε := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ n) hε.le)
            (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
      _ ≤ 1 + δ := by
          nlinarith [mul_le_mul_of_nonneg_left hεδ (by linarith : (0 : ℝ) ≤ 4 * 2 ^ n)]
  -- Step 8: the density bound at `σ = 1 - ε`, rearranged in `[0,∞]`: `densityRatio` is
  -- `μ(B_σ(y)) ω_n⁻¹ (σ^n)⁻¹` as `σ^n ∈ (0,∞)`, and `e^{εσ}/σ^n` is a single `ofReal`.
  have hRn0 : ENNReal.ofReal (1 - ε) ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hσ).ne'
  have hRnt : ENNReal.ofReal (1 - ε) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hfac : ENNReal.ofReal (Real.exp (ε * (1 - ε))) * (ENNReal.ofReal (1 - ε) ^ n)⁻¹ =
      ENNReal.ofReal (Real.exp (ε * (1 - ε)) / (1 - ε) ^ n) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hσ n), ENNReal.ofReal_pow hσ.le, div_eq_mul_inv]
  calc θ ≤ ENNReal.ofReal (Real.exp (ε * (1 - ε))) * densityRatio n μ y (1 - ε) :=
        hD (1 - ε) hσ (by linarith)
    _ = ENNReal.ofReal (Real.exp (ε * (1 - ε))) * (ENNReal.ofReal (1 - ε) ^ n)⁻¹ *
          μ (closedBall y (1 - ε)) / unitBallVolume n := by
      simp only [densityRatio, div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inr hRnt) (Or.inr hRn0)]
      ring
    _ = ENNReal.ofReal (Real.exp (ε * (1 - ε)) / (1 - ε) ^ n) * μ (closedBall y (1 - ε)) /
          unitBallVolume n := by rw [hfac]
    _ ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n := by
      gcongr
/-- Density sum over a fibre with at least two points (Simon Ch. 8, 5.11(∗) from (8), in the proof
of 5.9): with `d` the minimal distance between distinct points of `s`, the per-point bounds at
`τ = d/16`, `σ = d/(8δ²)` and the cluster bound at `(σ, d/4)` sum to
`Σ_{y∈s} Θ(y) ≤ (1 + δ) μ(B_1(x))/ω_n + δ`, the constants being absorbed by `Aδ ≤ 1`. -/
theorem Submission.intcpt_allard_fdsb_separated_sum_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞) (K c δ ε : ℝ) (M : ℕ), 0 ≤ K → 0 ≤ c → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → (2 + 2 * c + 2 * c / (unitBallVolume n).toReal + 2 * (M : ℝ) * K / (unitBallVolume n).toReal) * δ ≤ 1 → 2 ≤ s.card → s.card ≤ M → (∀ y ∈ s, ‖y - x‖ < ε ∧ ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → Θ y ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n) → (∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) + ENNReal.ofReal (c * δ ^ 2)) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
  intro N n μ P x s Θ K c δ ε M hK hc hδ hδh hε hεδ hA hs2 hsM hpt hCB
  -- Step 0: `ω_n ∈ (0, ∞)`; `ω := ω_n.toReal` is positive with `ofReal ω = ω_n`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨ω, hω_def⟩ : ∃ ω, (unitBallVolume n).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos hω0 hωtop
  have hωW : ENNReal.ofReal ω = unitBallVolume n := hω_def ▸ ENNReal.ofReal_toReal hωtop
  rw [hω_def] at hA
  -- `δ² ≤ 1/4`, `ε ≤ δ⁴ ≤ δ²` and `e^ε ≤ 1 + 2ε ≤ 1 + 2δ²`.
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hδ2 hδ2pos.le]
  have hexp : Real.exp ε ≤ 1 + 2 * δ ^ 2 := by
    have h := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε]; linarith)
    rw [abs_of_pos hε] at h
    linarith [le_abs_self (Real.exp ε - 1)]
  -- Step 1: the minimal distance `d` between distinct points of `s`; `0 < d < 2ε`.
  obtain ⟨p, hp, hpmin⟩ := s.offDiag.exists_min_image (fun q ↦ ‖q.1 - q.2‖) (by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    exact ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩⟩)
  obtain ⟨hp1, hp2, hp12⟩ := Finset.mem_offDiag.1 hp
  obtain ⟨d, hd_def⟩ : ∃ d, ‖p.1 - p.2‖ = d := ⟨_, rfl⟩
  have hdmin : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖ := by
    intro y hy y' hy' h
    rw [← hd_def]
    exact hpmin (y, y') (Finset.mem_offDiag.2 ⟨hy, hy', h⟩)
  have hd : 0 < d := hd_def ▸ norm_pos_iff.2 (sub_ne_zero.2 hp12)
  have hdε : d < 2 * ε := by
    rw [← hd_def]
    calc ‖p.1 - p.2‖ = ‖(p.1 - x) - (p.2 - x)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖p.1 - x‖ + ‖p.2 - x‖ := norm_sub_le _ _
      _ < ε + ε := add_lt_add (hpt _ hp1).1 (hpt _ hp2).1
      _ = 2 * ε := by ring
  -- Step 2: the scales `τ = d/16` and `σ = d/(8δ²)`.
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = d / 16 := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = d / (8 * δ ^ 2) := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd.ne'
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 / 4 := by rw [hτ]; linarith
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσδ : σ ≤ δ ^ 2 := by
    rw [hσ, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hδ 4]
  have hσ1 : σ < 1 := by linarith
  have hστ : 2 * δ ^ 2 * σ ≤ 4 * τ := le_of_eq (by rw [hσ, hτ]; field_simp; ring)
  have hsep : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * (4 * τ) ≤ ‖y - y'‖ := by
    intro y hy y' hy' h
    rw [hτ]
    linarith [hdmin y hy y' hy' h]
  have hk : K * ε * σ / τ ≤ 2 * K * δ ^ 2 := by
    have e : K * ε * σ / τ = 2 * K * ε / δ ^ 2 := by
      rw [hσ, hτ]; field_simp; ring
    rw [e, div_le_iff₀ hδ2pos]
    nlinarith [mul_le_mul_of_nonneg_left hεδ hK]
  -- Step 6: the real absorption inequalities, from `Aδ ≤ 1`.
  have ha : 0 ≤ 2 * c / ω := by positivity
  have hb : 0 ≤ 2 * (M : ℝ) * K / ω := by positivity
  have hA1 : (2 + 2 * c) * δ ≤ 1 := by
    nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le]
  have hA2 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * c) hδ.le]
  have hi : Real.exp ε * (1 + c * δ ^ 2) ≤ 1 + δ := by
    have h1 : Real.exp ε * (1 + c * δ ^ 2) ≤ (1 + 2 * δ ^ 2) * (1 + c * δ ^ 2) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    have h2 : (2 + 2 * c) * δ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hA1 hδ.le
    have h3 : 0 ≤ c * (δ ^ 2 * (1 - 2 * δ ^ 2)) :=
      mul_nonneg hc (mul_nonneg hδ2pos.le (by linarith))
    nlinarith [h1, h2, h3]
  have hii : Real.exp ε * (c * δ ^ 2) + (M : ℝ) * (2 * K * δ ^ 2) ≤ δ * ω := by
    have h1 : Real.exp ε * (c * δ ^ 2) ≤ 2 * (c * δ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ * (δ * ω) ≤ 1 * (δ * ω) :=
      mul_le_mul_of_nonneg_right hA2 (by positivity)
    have h3 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ * (δ * ω) =
        (2 * c + 2 * (M : ℝ) * K) * δ ^ 2 := by
      field_simp
    nlinarith [h1, h2, h3]
  -- Steps 3–5: sum the per-point bounds at `(τ, σ)` and apply (CB) at `(σ, 4τ)`, `#s ≤ M`.
  have hCB' := hCB σ (4 * τ) hσ0 hσδ hστ hsep
  have hfin : ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
        ENNReal.ofReal (c * δ ^ 2)) + (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2) ≤
      ENNReal.ofReal (1 + δ) * μ (closedBall x 1) + ENNReal.ofReal δ * unitBallVolume n := by
    have e1 : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (1 + c * δ ^ 2) ≤
        ENNReal.ofReal (1 + δ) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal hi
    have h1 : 0 ≤ Real.exp ε * (c * δ ^ 2) := by positivity
    have h2 : 0 ≤ (M : ℝ) * (2 * K * δ ^ 2) := by positivity
    have e2 : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (c * δ ^ 2) +
        (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2) ≤ ENNReal.ofReal δ * unitBallVolume n := by
      rw [← hωW, ← ENNReal.ofReal_mul (Real.exp_pos ε).le, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add h1 h2,
        ← ENNReal.ofReal_mul hδ.le]
      exact ENNReal.ofReal_le_ofReal hii
    calc _ = ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
          (ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (c * δ ^ 2) +
            (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_left e1 _) e2
  calc ∑ y ∈ s, Θ y
      ≤ ∑ y ∈ s, (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
          {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n :=
        Finset.sum_le_sum fun y hy ↦ (hpt y hy).2 τ σ hτ0 hτ1 hσ0 hσ1
    _ = (ENNReal.ofReal (Real.exp ε) * ∑ y ∈ s, μ (closedBall y σ ∩
          {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n +
          (s.card : ℝ≥0∞) * ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        rw [← ENNReal.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ (ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
          ENNReal.ofReal (c * δ ^ 2)) + (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2)) /
          unitBallVolume n :=
        ENNReal.div_le_div_right (add_le_add (mul_le_mul_right hCB' _)
          (mul_le_mul' (by exact_mod_cast hsM) (ENNReal.ofReal_le_ofReal hk))) _
    _ ≤ (ENNReal.ofReal (1 + δ) * μ (closedBall x 1) + ENNReal.ofReal δ * unitBallVolume n) /
          unitBallVolume n := ENNReal.div_le_div_right hfin _
    _ = ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
        rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hω0 hωtop]
/-- **Simon Ch. 8, proof of 5.10, printed (3), p. 221** (child `good_point_monotonicity` of
`allard_lemma`): if `B°_1(y) ⊆ U`, `μ_W(B°_1(y)) ≤ Λ` and `‖δW‖(B_ρ(y)) ≤ ε μ_W(B_ρ(y))` for
`0 < ρ < 1` (printed (1)), the monotonicity formula 3.3 with `ρ₀ = 1` shows that
`e^{ερ} ρ^{-n} μ_W(B_ρ(y))` is increasing on `(0, 1)` and that `Θ^n(μ_W, y)` exists, is finite and
is at most `e^{εσ} ω_n^{-1} σ^{-n} μ_W(B_σ(y))`.  Hence `μ_W(B_σ(y)) ≤ e^ε Λ ρ^{-n} σ^n` for
`0 < σ < ρ < 1`, and letting `ρ ↑ 1` gives `μ_W(B_σ(y)) ≤ e^ε Λ σ^n`. -/
theorem Submission.intcpt_allard_good_point_monotonicity :
    MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (ε Λ : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 ≤ ε → W.weight (ball y 1) ≤ ENNReal.ofReal Λ → (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) → MonotoneOn (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (ε * ρ)) * W.weight (closedBall y ρ) / ENNReal.ofReal ρ ^ n) (Ioo 0 1) ∧ (∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ θ ≠ ∞ ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n W.weight y σ) ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → W.weight (closedBall y σ) ≤ ENNReal.ofReal (Real.exp ε * Λ * σ ^ n) := by
  intro hMF N n U W y ε Λ hW hball hε hΛ hratio
  -- The monotonicity and density statements are 3.3 with `ρ₀ = 1`, `Λ = ε` (and `ρ = σ`).
  obtain ⟨hmono, θ, hθ, hθfin, hθle⟩ := hMF N n U W y 1 ε hW one_pos hball hε hratio
  refine ⟨hmono, ⟨θ, hθ, hθfin, fun σ hσ0 hσ1 ↦ (hθle σ σ hσ0 le_rfl hσ1).1⟩, ?_⟩
  intro σ hσ0 hσ1
  -- For `σ < ρ < 1`: `μ_W(B_σ(y)) ≤ e^{εσ} μ_W(B_σ(y)) ≤ e^{ερ} μ_W(B_ρ(y)) σ^n / ρ^n`
  -- `≤ e^ε Λ σ^n / ρ^n`, using `B_ρ(y) ⊆ B°_1(y)`.
  have key : ∀ ρ ∈ Ioo σ 1,
      W.weight (closedBall y σ) ≤ ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n) := by
    rintro ρ ⟨hσρ, hρ1⟩
    have hρ0 : 0 < ρ := hσ0.trans hσρ
    have hs0 : ENNReal.ofReal σ ^ n ≠ 0 := pow_ne_zero n (ENNReal.ofReal_pos.mpr hσ0).ne'
    have hsT : ENNReal.ofReal σ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hexp : ENNReal.ofReal (Real.exp (ε * ρ)) ≤ ENNReal.ofReal (Real.exp ε) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_of_le_one_right hε hρ1.le))
    have hμ : W.weight (closedBall y ρ) ≤ ENNReal.ofReal Λ :=
      (measure_mono (closedBall_subset_ball hρ1)).trans hΛ
    calc W.weight (closedBall y σ)
        ≤ ENNReal.ofReal (Real.exp (ε * σ)) * W.weight (closedBall y σ) :=
          le_mul_of_one_le_left zero_le
            (ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg hε hσ0.le)))
      _ = ENNReal.ofReal (Real.exp (ε * σ)) * W.weight (closedBall y σ) / ENNReal.ofReal σ ^ n *
            ENNReal.ofReal σ ^ n := (ENNReal.div_mul_cancel hs0 hsT).symm
      _ ≤ ENNReal.ofReal (Real.exp (ε * ρ)) * W.weight (closedBall y ρ) / ENNReal.ofReal ρ ^ n *
            ENNReal.ofReal σ ^ n := mul_le_mul_left (hmono ⟨hσ0, hσ1⟩ ⟨hρ0, hρ1⟩ hσρ.le) _
      _ ≤ ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal Λ / ENNReal.ofReal ρ ^ n *
            ENNReal.ofReal σ ^ n :=
          mul_le_mul_left (ENNReal.div_le_div_right (mul_le_mul' hexp hμ) _) _
      _ = ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n) := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hσ0.le n), ENNReal.ofReal_div_of_pos (pow_pos hρ0 n),
            ENNReal.ofReal_mul (Real.exp_pos ε).le, ENNReal.ofReal_pow hρ0.le,
            ENNReal.ofReal_pow hσ0.le]
  -- Let `ρ ↑ 1`.
  have hlim : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n)) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (Real.exp ε * Λ * σ ^ n))) := by
    have h : Tendsto (fun ρ : ℝ ↦ Real.exp ε * Λ / ρ ^ n * σ ^ n) (𝓝 1)
        (𝓝 (Real.exp ε * Λ / 1 ^ n * σ ^ n)) :=
      (tendsto_const_nhds.div ((continuous_pow n).tendsto 1) (by simp)).mul tendsto_const_nhds
    rw [one_pow, div_one] at h
    exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT hσ1) key)

/-- **Simon Ch. 8, proof of 5.10, printed (4)–(5) and the Besicovitch estimate, p. 221** (child
`bad_set_bound` of `allard_lemma`): if `μ_W(B°_3(0)) ≤ Λ`, `‖δW‖(B°_3(0)) < ε²` and
`∫_{B°_3(0) × G} ‖p_S - p_P‖ dW < ε²`, then the set of `y ∈ B_2(0) ∩ spt μ_W` at which
`‖δW‖(B_ρ(y)) ≤ ε μ_W(B_ρ(y))` (printed (1), with `δ‖W‖` read as `‖δW‖`) or
`∫_{B_ρ(y) × G} ‖p_S - p_P‖ dW ≤ ε ρ^n` (printed (2)) fails for some `ρ ∈ (0, 1)` has
`μ_W`-measure at most `c₀ ε`, with `c₀` depending only on `N` and `Λ`.  At such a `y` some
`ρ_y ∈ (0, 1)` has `μ_W(B_{ρ_y}(y)) ≤ ε⁻¹ ‖δW‖(B_{ρ_y}(y))` or, where (1) holds, by printed (3)
`μ_W(B_{ρ_y}(y)) ≤ e Λ ρ_y^n ≤ e Λ ε⁻¹ ∫_{B_{ρ_y}(y) × G} ‖p_S - p_P‖ dW`; the Besicovitch covering
lemma then bounds `μ_W` of the bad set by `C (ε⁻¹ ε² + e Λ ε⁻¹ ε²) = C (e Λ + 1) ε`. -/
theorem Submission.intcpt_allard_bad_set_bound :
    MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ Λ → ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → variationMeasure W (ball (0 : Euclidean N) 3) < ENNReal.ofReal (ε ^ 2) → (∫⁻ z in ball (0 : Euclidean N) 3 ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) < ENNReal.ofReal (ε ^ 2) → W.weight {y | y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ ¬ ((∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)))} ≤ ENNReal.ofReal (c₀ * ε) := by
  intro hMF N n Λ hΛ
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  -- `C` is the Besicovitch constant of `ℝ^N`; `c₀ := C (e Λ + 1)`.
  obtain ⟨C, hC⟩ := Submission.intcpt_allard_bsb_besicovitch_cover N
  refine ⟨C * (Real.exp 1 * Λ + 1), by positivity, ?_⟩
  intro ε hε0 hε1 U W P hU hW hμ hδ hT
  -- `τ(A) = ∫_{A × G} ‖p_S - p_P‖ dW(z, S)` for Borel `A`.
  obtain ⟨τ, hτ⟩ := Submission.intcpt_allard_bsb_marginal_measure N n W.measure fun z ↦
    ENNReal.ofReal ‖LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
  -- `ν := ε⁻¹ ‖δW‖ + e Λ ε⁻¹ τ`.
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Euclidean N), ∀ A, ν A =
      ENNReal.ofReal (1 / ε) * variationMeasure W A + ENNReal.ofReal (Real.exp 1 * Λ / ε) * τ A :=
    ⟨ENNReal.ofReal (1 / ε) • variationMeasure W + ENNReal.ofReal (Real.exp 1 * Λ / ε) • τ,
      fun A ↦ by rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul]⟩
  refine le_trans (hC W.weight ν _ (ball 0 3) 1 1 ?_) ?_
  · -- Every bad point `y` is the centre of a ball `B_ρ(y) ⊆ B°_3(0)`, `ρ ∈ (0, 1)`, with
    -- `μ_W(B_ρ(y)) ≤ ν(B_ρ(y))`.
    rintro y ⟨hy, -, hbad⟩
    have hy2 : dist y 0 ≤ 2 := mem_closedBall.mp hy
    have hsub : ∀ ρ : ℝ, ρ < 1 → closedBall y ρ ⊆ ball (0 : Euclidean N) 3 := fun ρ hρ ↦
      closedBall_subset_ball' (by linarith)
    by_cases h1 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)
    · -- (1) holds, so (2) fails at some `ρ`, and printed (3) gives `μ_W(B_ρ(y)) ≤ e^ε Λ ρ^n`.
      have h2 := not_and.mp hbad h1
      push Not at h2
      obtain ⟨ρ, hρ0, hρ1, hlt⟩ := h2
      have hb1 : ball y 1 ⊆ ball (0 : Euclidean N) 3 := ball_subset_ball' (by linarith)
      have hgood := (Submission.intcpt_allard_good_point_monotonicity hMF N n U W y ε Λ hW
        (hb1.trans hU) hε0.le ((measure_mono hb1).trans hμ) h1).2.2 ρ hρ0 hρ1
      refine ⟨ρ, hρ0, hρ1.le, hsub ρ hρ1, ?_⟩
      rw [one_mul, hν]
      calc W.weight (closedBall y ρ) ≤ ENNReal.ofReal (Real.exp ε * Λ * ρ ^ n) := hgood
        _ ≤ ENNReal.ofReal (Real.exp 1 * Λ / ε * (ε * ρ ^ n)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← mul_assoc, div_mul_cancel₀ _ hε0.ne']
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hε1) hΛ0) (pow_nonneg hρ0.le n)
        _ = ENNReal.ofReal (Real.exp 1 * Λ / ε) * ENNReal.ofReal (ε * ρ ^ n) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (Real.exp 1 * Λ / ε) * τ (closedBall y ρ) := by
            rw [hτ _ measurableSet_closedBall]
            exact mul_le_mul_right hlt.le _
        _ ≤ _ := le_add_self
    · -- (1) fails at some `ρ`: `μ_W(B_ρ(y)) ≤ ε⁻¹ ‖δW‖(B_ρ(y))`.
      push Not at h1
      obtain ⟨ρ, hρ0, hρ1, hlt⟩ := h1
      refine ⟨ρ, hρ0, hρ1.le, hsub ρ hρ1, ?_⟩
      rw [one_mul, hν]
      calc W.weight (closedBall y ρ)
          = ENNReal.ofReal (1 / ε) * (ENNReal.ofReal ε * W.weight (closedBall y ρ)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hε0.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (1 / ε) * variationMeasure W (closedBall y ρ) :=
            mul_le_mul_right hlt.le _
        _ ≤ _ := le_self_add
  · -- `ν(B°_3(0)) ≤ ε⁻¹ ε² + e Λ ε⁻¹ ε² = (e Λ + 1) ε`.
    have hτ3 : τ (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal (ε ^ 2) :=
      (hτ _ measurableSet_ball).trans_le hT.le
    rw [mul_one, hν]
    calc (C : ℝ≥0∞) * (ENNReal.ofReal (1 / ε) * variationMeasure W (ball (0 : Euclidean N) 3) +
          ENNReal.ofReal (Real.exp 1 * Λ / ε) * τ (ball (0 : Euclidean N) 3))
        ≤ C * (ENNReal.ofReal (1 / ε) * ENNReal.ofReal (ε ^ 2) +
          ENNReal.ofReal (Real.exp 1 * Λ / ε) * ENNReal.ofReal (ε ^ 2)) :=
          mul_le_mul_right (add_le_add (mul_le_mul_right hδ.le _) (mul_le_mul_right hτ3 _)) _
      _ = ENNReal.ofReal (C * (Real.exp 1 * Λ + 1) * ε) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          field_simp
          ring
/-- Cylinder cut-off weight (Simon Ch. 8, proof of Lemma 5.10, displays (6)–(7): the `h` used in
3.5, `h(z) = f(|q(z - y)|)` with `f ≡ 1` on `[0, τ)`, `f ≡ 0` on `(2τ, ∞)`).  With
`M₀ = 4 sup |st'|` (`st = Real.smoothTransition`), `h(z) = st(4 - ‖q(z - y)‖²/τ²)` is `C¹`, takes
values in `[0, 1]`, equals `1` where `‖q(z - y)‖ < τ` and `0` where `‖q(z - y)‖ ≥ 2τ`
(`q = id - p_P`), and `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ) ‖p_S - p_P‖ ‖z - y‖`. -/
theorem Submission.intcpt_allard_cm_cylinder_weight :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (N n : ℕ) (P : Grassmannian N n) (y : Euclidean N) (τ : ℝ), 0 < τ → ∃ h : Euclidean N → ℝ, ContDiff ℝ 1 h ∧ (∀ z, 0 ≤ h z ∧ h z ≤ 1) ∧ (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) ∧ (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) ∧ ∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M₀ / τ * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖ := by
  -- Step 1: `deriv smoothTransition` vanishes off `[0, 1]`, where `smoothTransition` is locally
  -- constant (`0` on `(-∞, 0)`, `1` on `(1, ∞)`).
  have hst'_zero : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition u = 0 := by
    intro u hu
    rcases lt_or_ge u 0 with hu0 | hu0
    · have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hu0] with v hv
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hv)
      rw [hev.deriv_eq, deriv_const]
    · have hu1 : 1 < u := lt_of_not_ge fun h1 ↦ hu ⟨hu0, h1⟩
      have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu1] with v hv
        exact Real.smoothTransition.one_of_one_le (le_of_lt hv)
      rw [hev.deriv_eq, deriv_const]
  -- Step 2: `deriv smoothTransition` is continuous with compact support, hence bounded by some
  -- `L ≥ 0`; take `M₀ := 4 L`.
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨L, hL⟩ :=
    (HasCompactSupport.intro isCompact_Icc hst'_zero).exists_bound_of_continuous hcont
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨4 * L, by positivity, ?_⟩
  intro N n P y τ hτ
  -- Step 3: `Q = id - p_P` as a continuous linear map, and
  -- `h z = smoothTransition (4 - ‖Q (z - y)‖² / τ²)`.
  obtain ⟨Q, hQ⟩ : ∃ Q : Euclidean N →L[ℝ] Euclidean N,
      ∀ v, Q v = v - Grassmannian.project P v :=
    ⟨LinearMap.toContinuousLinearMap (LinearMap.id - Grassmannian.projectionLinearMap P),
      fun v ↦ rfl⟩
  have hτ2 : 0 < τ ^ 2 := by positivity
  refine ⟨fun z ↦ Real.smoothTransition (4 - ‖Q (z - y)‖ ^ 2 / τ ^ 2), ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 4: `h` is `C^∞`, in particular `C¹`.
    exact (Real.smoothTransition.contDiff (n := 1)).comp
      (contDiff_const.sub
        (((Q.contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ).div_const _))
  · -- Step 5: values in `[0, 1]`.
    exact fun z ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · -- Step 6: `‖q(z - y)‖ < τ` gives `4 - F(z) > 3 ≥ 1`, so `h z = 1`.
    intro z hz
    apply Real.smoothTransition.one_of_one_le
    have h1 : ‖Q (z - y)‖ ^ 2 < τ ^ 2 := by
      rw [hQ]
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    have h2 : ‖Q (z - y)‖ ^ 2 / τ ^ 2 < 1 := (div_lt_one hτ2).2 h1
    linarith
  · -- Step 7: `‖q(z - y)‖ ≥ 2τ` gives `4 - F(z) ≤ 0`, so `h z = 0`.
    intro z hz
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : (2 * τ) ^ 2 ≤ ‖Q (z - y)‖ ^ 2 := by
      rw [hQ]
      exact pow_le_pow_left₀ (by positivity) hz 2
    have h2 : 4 ≤ ‖Q (z - y)‖ ^ 2 / τ ^ 2 := by
      rw [le_div_iff₀ hτ2]
      nlinarith
    linarith
  · intro z S
    -- Step 8: chain rule.  `z' ↦ Q (z' - y)` has derivative `Q`, so with
    -- `G z' = 4 - ‖Q (z' - y)‖² (τ²)⁻¹` we get `Dh(z) = st'(G z) • DG(z)`.
    have hQd : HasFDerivAt (fun z' ↦ Q (z' - y)) Q z := by
      have h1 := Q.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
      rwa [ContinuousLinearMap.comp_id] at h1
    have hGd := (hQd.norm_sq.mul_const ((τ ^ 2)⁻¹)).const_sub (4 : ℝ)
    have hst : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (4 - ‖Q (z - y)‖ ^ 2 * (τ ^ 2)⁻¹))
        (4 - ‖Q (z - y)‖ ^ 2 * (τ ^ 2)⁻¹) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hfun : (fun z' ↦ Real.smoothTransition (4 - ‖Q (z' - y)‖ ^ 2 / τ ^ 2)) =
        Real.smoothTransition ∘ fun z' ↦ 4 - ‖Q (z' - y)‖ ^ 2 * (τ ^ 2)⁻¹ := by
      funext z'
      simp only [Function.comp_apply, div_eq_mul_inv]
    rw [hfun, (hst.comp_hasFDerivAt z hGd).fderiv]
    simp only [_root_.smul_apply, _root_.neg_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    -- Step 9: `p_P (Q w) = 0`, and self-adjointness of `p_P`, `p_S` gives
    -- `⟪Q w, Q (p_S w)⟫ = ⟪(p_S - p_P) (Q w), w⟫` with `w = z - y`.
    have hpa : Grassmannian.projectionLinearMap P (Q (z - y)) = 0 := by
      have h1 := Grassmannian.project_project P (z - y)
      simp only [Grassmannian.project] at h1
      rw [hQ, Grassmannian.project, map_sub, h1, sub_self]
    have hkey : inner ℝ (Q (z - y)) (Q (Grassmannian.project S (z - y))) =
        inner ℝ (LinearMap.toContinuousLinearMap
          (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P) (Q (z - y)))
          (z - y) := by
      rw [LinearMap.coe_toContinuousLinearMap', LinearMap.sub_apply, hpa, sub_zero,
        hQ (Grassmannian.project S (z - y)), inner_sub_right]
      simp only [Grassmannian.project]
      rw [← Grassmannian.projectionLinearMap_isSymmetric P (Q (z - y)), hpa, inner_zero_left,
        sub_zero, Grassmannian.projectionLinearMap_isSymmetric S (Q (z - y)) (z - y)]
    rw [hkey]
    -- Step 10: if `G z < 0` then `st'(G z) = 0`; otherwise `‖Q w‖ ≤ 2τ`, and
    -- `|Dh(z)[p_S w]| ≤ L (2/τ²) ‖T‖ (2τ) ‖w‖ = (4L/τ) ‖T‖ ‖w‖`.
    set T := LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)
    set a := Q (z - y)
    set w := z - y
    have hRHS : 0 ≤ 4 * L / τ * ‖T‖ * ‖w‖ := by positivity
    rcases lt_or_ge (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹) 0 with hneg | hnn
    · rw [hst'_zero _ fun hmem ↦ (not_le.2 hneg) hmem.1, zero_mul, abs_zero]
      exact hRHS
    · have ha2 : ‖a‖ ≤ 2 * τ := by
        rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hτ2] at hnn
        nlinarith [norm_nonneg a]
      have hd : |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)| ≤ L := by
        simpa only [Real.norm_eq_abs] using hL (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)
      have hX : |inner ℝ (T a) w| ≤ ‖T‖ * (2 * τ) * ‖w‖ :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right ((T.le_opNorm a).trans
            (mul_le_mul_of_nonneg_left ha2 (norm_nonneg _))) (norm_nonneg _))
      calc |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹) *
            -((τ ^ 2)⁻¹ * (2 * inner ℝ (T a) w))|
          = |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)| *
            ((τ ^ 2)⁻¹ * (2 * |inner ℝ (T a) w|)) := by
            rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hτ2), abs_two]
        _ ≤ L * ((τ ^ 2)⁻¹ * (2 * (‖T‖ * (2 * τ) * ‖w‖))) := by
            gcongr
        _ = 4 * L / τ * ‖T‖ * ‖w‖ := by
            field_simp
            ring
/-- **Simon Ch. 8, proof of 5.10, p. 221, the radial cutoffs** (child `radial_cutoff` of
`cylinder_monotonicity`, step 1): for `A > 1`, `φ(s) = st((A² - s)/(A² - 1))`, with `st` Mathlib's
`Real.smoothTransition`, is a `C¹` non-increasing function with values in `[0,1]` that is `1` on
`(-∞, 1]` and `0` on `[A², ∞)`. -/
theorem Submission.intcpt_allard_cm_radial_cutoff :
    ∀ A : ℝ, 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) ∧
      (∀ s, s ≤ 1 → φ s = 1) ∧ (∀ s, A ^ 2 ≤ s → φ s = 0) := by
  intro A hA
  -- `d = A² - 1 > 0`, so `s ↦ (A² - s)/d` is a decreasing affine map.
  have hd : 0 < A ^ 2 - 1 := by nlinarith
  refine ⟨fun s ↦ Real.smoothTransition ((A ^ 2 - s) / (A ^ 2 - 1)), ?_, fun s s' hs ↦ ?_,
    fun s ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, fun s hs ↦ ?_,
    fun s hs ↦ ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hd.le)
  · -- `s ≤ 1` gives `(A² - s)/d ≥ 1`.
    exact Real.smoothTransition.one_of_one_le ((one_le_div₀ hd).2 (by linarith))
  · -- `A² ≤ s` gives `(A² - s)/d ≤ 0`.
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
/-- Dominated convergence for shrinking radial cutoffs (step 4 of the cylinder monotonicity used
for Simon Ch. 8, 5.9): if `φ_j = 1` on `(-∞, 1]`, `φ_j = 0` on `[A_j², ∞)`, `0 ≤ φ_j ≤ 1`,
`A_j → 1` and `μ(B_R(y)) < ∞` with `t A_j ≤ R`, then
`∫ φ_j(|z - y|²/t²) h(z) dμ(z) → ∫_{B_t(y)} h dμ` for measurable `0 ≤ h ≤ 1`. -/
theorem Submission.intcpt_allard_cm_cutoff_integral_tendsto :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℕ → ℝ → ℝ) (A : ℕ → ℝ) (t R : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ j, Measurable (φ j)) → (∀ j s, 0 ≤ φ j s ∧ φ j s ≤ 1) → (∀ j s, s ≤ 1 → φ j s = 1) → (∀ j s, A j ^ 2 ≤ s → φ j s = 0) → (∀ j, 0 < A j) → Tendsto A atTop (𝓝 1) → 0 < t → (∀ j, t * A j ≤ R) → μ (closedBall y R) ≠ ∞ → Tendsto (fun j ↦ ∫ z, φ j (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) atTop (𝓝 (∫ z in closedBall y t, h z ∂μ)) := by
  intro N μ y h φ A t R hh h01 hφm hφ01 hφ1 hφ0 hA hAlim ht htR hμR
  -- Step 1: `∫_{B_t(y)} h dμ = ∫ 1_{B_t(y)} h dμ`; dominated convergence with bound `1_{B_R(y)}`.
  rw [← integral_indicator measurableSet_closedBall]
  refine tendsto_integral_filter_of_dominated_convergence
    ((closedBall y R).indicator fun _ ↦ (1 : ℝ)) ?_ ?_ ?_ ?_
  -- Step 2: every `F_j` is measurable.
  · have hmeas : Measurable fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2 := by fun_prop
    exact Eventually.of_forall fun j ↦ (((hφm j).comp hmeas).mul hh).aestronglyMeasurable
  -- Step 3: domination `‖F_j z‖ ≤ 1_{B_R(y)} z`.
  · refine Eventually.of_forall fun j ↦ ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ closedBall y R
    · rw [indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hφ01 j _).1 (h01 z).1)]
      exact (mul_le_of_le_one_left (h01 z).1 (hφ01 j _).2).trans (h01 z).2
    · have hRz : R < ‖z - y‖ := by rwa [mem_closedBall, dist_eq_norm, not_le] at hz
      have hAz : A j ≤ ‖z - y‖ / t := by
        rw [le_div_iff₀ ht]
        linarith [htR j, mul_comm (A j) t]
      have hs : A j ^ 2 ≤ ‖z - y‖ ^ 2 / t ^ 2 := by
        rw [← div_pow]
        exact pow_le_pow_left₀ (hA j).le hAz 2
      rw [indicator_of_notMem hz, hφ0 j _ hs, zero_mul, norm_zero]
  -- Step 4: `1_{B_R(y)}` is integrable since `μ(B_R(y)) < ∞`.
  · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hμR)
  -- Step 5: pointwise convergence `F_j z → 1_{B_t(y)} h z`.
  · refine ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ closedBall y t
    · have hzt : ‖z - y‖ ≤ t := by rwa [mem_closedBall, dist_eq_norm] at hz
      have hs : ‖z - y‖ ^ 2 / t ^ 2 ≤ 1 := by
        rw [div_le_one₀ (pow_pos ht 2)]
        exact pow_le_pow_left₀ (norm_nonneg _) hzt 2
      rw [indicator_of_mem hz]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      rw [hφ1 j _ hs, one_mul]
    · have hzt : t < ‖z - y‖ := by rwa [mem_closedBall, dist_eq_norm, not_le] at hz
      have hs : 1 < ‖z - y‖ ^ 2 / t ^ 2 := by
        rw [one_lt_div₀ (pow_pos ht 2)]
        exact pow_lt_pow_left₀ hzt ht.le two_ne_zero
      have hA2 : Tendsto (fun j ↦ A j ^ 2) atTop (𝓝 1) := by simpa using hAlim.pow 2
      rw [indicator_of_notMem hz]
      refine tendsto_const_nhds.congr' ((hA2.eventually_le_const hs).mono fun j hj ↦ ?_)
      dsimp only
      rw [hφ0 j _ hj, zero_mul]
/-- Cylinder masses from cut-off ball integrals (Simon Ch. 8, proof of Lemma 5.10, display (7):
the last step after integrating 3.5 from `σ` to `ρ`).  Let `0 ≤ h ≤ 1` be measurable with `h = 1`
where `‖q(z - y)‖ < τ` and `h = 0` where `‖q(z - y)‖ ≥ 2τ` (`q = id - p_P`), `0 < σ ≤ ρ` and
`μ(B_ρ(y)) < ∞`.  If `σ^{-n} ∫_{B_σ(y)} h dμ ≤ ρ^{-n} ∫_{B_ρ(y)} h dμ + E`, then in `[0, ∞]`
`σ^{-n} μ(U^τ_σ(y)) ≤ ρ^{-n} μ(U^{2τ}_ρ(y)) + max(E, 0)`, where
`U^τ_r(y) = B_r(y) ∩ {z : ‖q(z - y)‖ < τ}`. -/
theorem Submission.intcpt_allard_cm_cylinder_mass_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (h : Euclidean N → ℝ) (τ σ ρ E : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) → (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) → 0 < σ → σ ≤ ρ → μ (closedBall y ρ) ≠ ∞ → (∫ z in closedBall y σ, h z ∂μ) / σ ^ n ≤ (∫ z in closedBall y ρ, h z ∂μ) / ρ ^ n + E → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal E := by
  intro N n μ P y h τ σ ρ E hmeas hbd h1 h0 hσ hσρ hfin hineq
  -- Step 1: `z ↦ ‖q(z - y)‖` is continuous (`p_P` is linear on `ℝ^N`), so the cylinders
  -- `S₁ = {‖q(z - y)‖ < τ}` and `S₂ = {‖q(z - y)‖ < 2τ}` are open, hence measurable.
  have hcont : Continuous fun z : Euclidean N ↦ ‖(z - y) - Grassmannian.project P (z - y)‖ := by
    have hP : Continuous (Grassmannian.project P) :=
      (Grassmannian.projectionLinearMap P).continuous_of_finiteDimensional
    exact ((continuous_id.sub continuous_const).sub
      (hP.comp (continuous_id.sub continuous_const))).norm
  have hS₁ : MeasurableSet {z : Euclidean N | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ} :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hS₂ : MeasurableSet
      {z : Euclidean N | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ} :=
    (isOpen_lt hcont continuous_const).measurableSet
  -- Step 2: `B_σ(y) ⊆ B_ρ(y)`, so `B_σ(y)`, `U₁ = B_σ(y) ∩ S₁` and `U₂ = B_ρ(y) ∩ S₂` have finite
  -- measure.
  have hρ : 0 < ρ := lt_of_lt_of_le hσ hσρ
  have hfinσ : μ (closedBall y σ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall hσρ))
  have hU₁fin : μ (closedBall y σ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) ≠ ∞ :=
    ne_top_of_le_ne_top hfinσ (measure_mono inter_subset_left)
  have hU₂fin : μ (closedBall y ρ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  -- Step 3: `h` is measurable with `|h| ≤ 1`, hence integrable on every set of finite measure.
  have hint : ∀ s, μ s ≠ ∞ → IntegrableOn h s μ := fun s hs ↦
    Measure.integrableOn_of_bounded hs hmeas.aestronglyMeasurable (M := 1)
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hbd z).1], (hbd z).2⟩)
  -- Step 4: `h = 1` on `U₁` and `h ≥ 0`, so `μ(U₁) = ∫_{U₁} h dμ ≤ ∫_{B_σ(y)} h dμ`.
  have hlow : μ.real (closedBall y σ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) ≤ ∫ z in closedBall y σ, h z ∂μ := by
    have heq : ∫ z in closedBall y σ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}, h z ∂μ =
        μ.real (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) := by
      rw [setIntegral_congr_fun (measurableSet_closedBall.inter hS₁) (g := fun _ ↦ (1 : ℝ))
        (fun z hz ↦ h1 z hz.2)]
      exact setIntegral_one_eq_measureReal
    rw [← heq]
    exact setIntegral_mono_set (hint _ hfinσ) (Eventually.of_forall fun z ↦ (hbd z).1)
      (Eventually.of_forall fun z hz ↦ hz.1)
  -- Step 5: `h = 0` on `B_ρ(y) ∖ S₂` and `h ≤ 1`, so `∫_{B_ρ(y)} h dμ = ∫_{U₂} h dμ ≤ μ(U₂)`.
  have hup : ∫ z in closedBall y ρ, h z ∂μ ≤ μ.real (closedBall y ρ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) := by
    rw [← integral_inter_add_sdiff hS₂ (hint _ hfin)]
    have hzero : ∫ z in closedBall y ρ \
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}, h z ∂μ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ h0 z (not_lt.mp hz.2)
    rw [hzero, add_zero, ← setIntegral_one_eq_measureReal]
    exact setIntegral_mono_on (hint _ hU₂fin) (integrableOn_const hU₂fin)
      (measurableSet_closedBall.inter hS₂) fun z _ ↦ (hbd z).2
  -- Step 6: the real inequality `μ(U₁)/σ^n ≤ μ(U₂)/ρ^n + E`.
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  have hreal : μ.real (closedBall y σ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / σ ^ n ≤
      μ.real (closedBall y ρ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ρ ^ n + E :=
    calc _ ≤ (∫ z in closedBall y σ, h z ∂μ) / σ ^ n := div_le_div_of_nonneg_right hlow hσn.le
      _ ≤ (∫ z in closedBall y ρ, h z ∂μ) / ρ ^ n + E := hineq
      _ ≤ _ := by gcongr
  -- Step 7: for `r > 0` and `μ s < ∞`, `μ s / ofReal r ^ n = ofReal (μ.real s / r ^ n)`; conclude
  -- with monotonicity of `ofReal` and `ofReal (a + E) ≤ ofReal a + ofReal E`.
  have hconv : ∀ (s : Set (Euclidean N)) (r : ℝ), 0 < r → μ s ≠ ∞ →
      μ s / ENNReal.ofReal r ^ n = ENNReal.ofReal (μ.real s / r ^ n) := by
    intro s r hr hs
    rw [ENNReal.ofReal_div_of_pos (pow_pos hr n), ENNReal.ofReal_pow hr.le, measureReal_def,
      ENNReal.ofReal_toReal hs]
  rw [hconv _ σ hσ hU₁fin, hconv _ ρ hρ hU₂fin]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
/-- Differentiation of the radial cutoff mass under the integral sign (step 5 of the weighted
radial monotonicity argument, Simon Ch. 8, §3): if `φ` is `C¹` with `φ = 0` on `[A², ∞)`, `h` is
continuous and `μ(B_R(y)) < ∞`, then for `t₀ > 0` with `t₀ A < R` the map
`t ↦ ∫ φ(|z - y|²/t²) h(z) dμ(z)` has derivative `∫ φ'(|z - y|²/t₀²)(-2|z - y|²/t₀³) h(z) dμ(z)`
at `t₀`. -/
theorem Submission.intcpt_allard_wrm_cutoff_mass_hasDerivAt :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A R t₀ : ℝ), Continuous h → ContDiff ℝ 1 φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → μ (closedBall y R) ≠ ∞ → 0 < t₀ → t₀ * A < R → HasDerivAt (fun t : ℝ ↦ ∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) (∫ z, deriv φ (‖z - y‖ ^ 2 / t₀ ^ 2) * (-2 * ‖z - y‖ ^ 2 / t₀ ^ 3) * h z ∂μ) t₀ := by
  intro N μ y h φ A R t₀ hh hφ hA hφA hμ ht₀ htR
  -- Step 1: `a := t₀ / 2 < t₀ < b := (t₀ + R / A) / 2` with `b * A < R`; `K := B_R(y)`.
  have hRA : t₀ < R / A := (lt_div_iff₀ hA).2 htR
  obtain ⟨a, b, ha, hat, htb, hbA⟩ : ∃ a b : ℝ, 0 < a ∧ a < t₀ ∧ t₀ < b ∧ b * A < R :=
    ⟨t₀ / 2, (t₀ + R / A) / 2, half_pos ht₀, half_lt_self ht₀, by linarith,
      (lt_div_iff₀ hA).1 (by linarith)⟩
  have hKc : IsCompact (closedBall y R) := isCompact_closedBall y R
  have hKm : MeasurableSet (closedBall y R) := measurableSet_closedBall
  -- Step 2 (i): `φ' = 0` on `(A², ∞)`.
  have hφ'0 : ∀ s, A ^ 2 < s → deriv φ s = 0 := by
    intro s hs
    have hev : φ =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun u hu ↦ hφA u (le_of_lt hu)
    rw [hev.deriv_eq, deriv_const]
  -- Step 2 (ii): for `t ∈ [a, b]` and `z ∉ K`, `‖z - y‖² / t² > A²`.
  have hout : ∀ t, a ≤ t → t ≤ b → ∀ z, z ∉ closedBall y R → A ^ 2 < ‖z - y‖ ^ 2 / t ^ 2 := by
    intro t hat htb z hz
    have ht : 0 < t := lt_of_lt_of_le ha hat
    have hzR : R < ‖z - y‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      exact hz
    have htA : t * A < ‖z - y‖ := by nlinarith
    have hsq : (t * A) ^ 2 < ‖z - y‖ ^ 2 := pow_lt_pow_left₀ htA (by positivity) two_ne_zero
    rw [lt_div_iff₀ (by positivity)]
    linarith [hsq, show (t * A) ^ 2 = A ^ 2 * t ^ 2 by ring]
  -- Step 3: continuity.
  have hFc : ∀ t : ℝ, Continuous fun z : Euclidean N ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z := fun t ↦
    (hφ.continuous.comp (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).mul hh
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hF'c : ContinuousOn (fun p : ℝ × Euclidean N ↦
      deriv φ (‖p.2 - y‖ ^ 2 / p.1 ^ 2) * (-2 * ‖p.2 - y‖ ^ 2 / p.1 ^ 3) * h p.2)
      (Icc a b ×ˢ closedBall y R) := by
    have hne : ∀ p ∈ Icc a b ×ˢ closedBall y R, p.1 ≠ 0 := fun p hp ↦
      (lt_of_lt_of_le ha hp.1.1).ne'
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (hh.comp continuous_snd).continuousOn
    · exact hφ'c.comp_continuousOn
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ pow_ne_zero _ (hne p hp))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ pow_ne_zero _ (hne p hp)
  -- Step 4: domination by `C · 1_K`.
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hKc).exists_bound_of_continuousOn hF'c
  have h_bound : ∀ᵐ z ∂μ, ∀ t ∈ Ioo a b,
      ‖deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z‖ ≤
        (closedBall y R).indicator (fun _ ↦ C) z := by
    refine Eventually.of_forall fun z t ht ↦ ?_
    by_cases hz : z ∈ closedBall y R
    · rw [indicator_of_mem hz]
      exact hC (t, z) ⟨Ioo_subset_Icc_self ht, hz⟩
    · rw [indicator_of_notMem hz, hφ'0 _ (hout t ht.1.le ht.2.le z hz)]
      simp
  have hbound_int : Integrable ((closedBall y R).indicator fun _ ↦ C) μ :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hμ)
  -- Step 5: integrability of `F(t₀, ·)`.
  have hF_int : Integrable (fun z ↦ φ (‖z - y‖ ^ 2 / t₀ ^ 2) * h z) μ := by
    obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn (hFc t₀).continuousOn
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (Measure.integrableOn_of_bounded hμ (hFc t₀).aestronglyMeasurable
        (ae_restrict_of_forall_mem hKm hC₀)) fun z hz ↦ ?_
    rw [hφA _ (hout t₀ hat.le htb.le z hz).le, zero_mul]
  have hF'meas : AEStronglyMeasurable
      (fun z ↦ deriv φ (‖z - y‖ ^ 2 / t₀ ^ 2) * (-2 * ‖z - y‖ ^ 2 / t₀ ^ 3) * h z) μ :=
    ((hφ'c.comp (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).mul
      ((((continuous_id.sub continuous_const).norm.pow 2).const_mul (-2)).div_const _)).mul
      hh |>.aestronglyMeasurable
  -- Step 6: pointwise derivative in `t`.
  have h_diff : ∀ᵐ z ∂μ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z)
        (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z) t := by
    refine Eventually.of_forall fun z t ht ↦ ?_
    have ht0 : t ≠ 0 := (lt_trans ha ht.1).ne'
    have hs : HasDerivAt (fun t ↦ ‖z - y‖ ^ 2 / t ^ 2) (-2 * ‖z - y‖ ^ 2 / t ^ 3) t :=
      ((hasDerivAt_const t (‖z - y‖ ^ 2)).div (hasDerivAt_pow 2 t)
        (pow_ne_zero 2 ht0)).congr_deriv (by field_simp; ring)
    exact ((hφ.differentiable one_ne_zero _).hasDerivAt.comp t hs).mul_const (h z)
  -- Step 7: differentiation under the integral sign on `(a, b) ∋ t₀`.
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z)
    (F' := fun t z ↦ deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z)
    (Ioo_mem_nhds hat htb) (Eventually.of_forall fun t ↦ (hFc t).aestronglyMeasurable) hF_int
    hF'meas h_bound hbound_int h_diff).2
/-- Weighted radial first-variation inequality at a fixed radius (Simon Ch. 8, 3.5, with the sign
of `δV(X)` corrected): for `X_t(z) = h(z) φ(|z - y|²/t²) (z - y)`,
`n Ĩ(t) - t J(t) + G(t) ≤ δW(X_t)`, because the dropped normal term is nonnegative (`h ≥ 0`,
`φ' ≤ 0` and `⟨w, p_S w⟩ ≤ |w|²`).  The divergence of `X_t` is supplied by hypothesis (Div). -/
theorem Submission.intcpt_allard_wrm_first_variation_lower_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A t : ℝ), (∀ (a : Euclidean N → ℝ) (c z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - c)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - c))) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z) → ContDiff ℝ 1 φ → Antitone φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → 0 < t → closedBall y (t * A) ⊆ U → (n : ℝ) * (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) - t * (∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) + (∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure) ≤ W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) := by
  intro N n U W y h φ A t hDiv hh hh0 hφ hφa hA hcut ht hU
  -- Step 1: with `s(z) = ‖z - y‖²/t²`, `φ(s(z)) = φ'(s(z)) = 0` off `K = B_{tA}(y)`.
  have hKc : IsCompact (closedBall y (t * A)) := isCompact_closedBall y (t * A)
  have hout : ∀ z : Euclidean N, z ∉ closedBall y (t * A) → A ^ 2 < ‖z - y‖ ^ 2 / t ^ 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos ht hA]
  have hφ0 : ∀ z : Euclidean N, z ∉ closedBall y (t * A) → φ (‖z - y‖ ^ 2 / t ^ 2) = 0 :=
    fun z hz ↦ hcut _ (hout z hz).le
  have hdφ0 : ∀ z : Euclidean N, z ∉ closedBall y (t * A) →
      deriv φ (‖z - y‖ ^ 2 / t ^ 2) = 0 := by
    intro z hz
    have hev : φ =ᶠ[𝓝 (‖z - y‖ ^ 2 / t ^ 2)] fun _ ↦ 0 :=
      (eventually_gt_nhds (hout z hz)).mono fun s hs ↦ hcut s hs.le
    rw [hev.deriv_eq, deriv_const]
  -- Step 2: `s`, `a = h · (φ ∘ s)` and `X_t = a · (· - y)` are `C¹`.
  have hs : ContDiff ℝ 1 (fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2) :=
    ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _
  have ha : ContDiff ℝ 1 (fun z ↦ h z * φ (‖z - y‖ ^ 2 / t ^ 2)) := hh.mul (hφ.comp hs)
  have hX : ContDiff ℝ 1 (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) :=
    ha.smul (contDiff_id.sub contDiff_const)
  -- Step 3: `tsupport X_t ⊆ K ⊆ U`, so `div_S X_t` is `W`-integrable (step 7a).
  have hXK : tsupport (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) ⊆
      closedBall y (t * A) := by
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    by_contra hzK
    exact hz (by simp only [hφ0 z hzK, mul_zero, zero_smul])
  have hdiv := W.integrable_tangentialDivergence _ hX
    (hKc.of_isClosed_subset (isClosed_tsupport _) hXK) (hXK.trans hU)
  -- Step 7: a continuous integrand vanishing off `K × G` is `W`-integrable, as `W(K × G) < ∞`.
  have hint : ∀ F : Euclidean N × Grassmannian N n → ℝ, Continuous F →
      (∀ p : Euclidean N × Grassmannian N n, p.1 ∉ closedBall y (t * A) → F p = 0) →
      Integrable F W.measure := by
    intro F hF hF0
    have hKG : IsCompact (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))) :=
      hKc.prod isCompact_univ
    obtain ⟨C, hC⟩ := hKG.exists_bound_of_continuousOn hF.continuousOn
    have hOn : IntegrableOn F (closedBall y (t * A) ×ˢ univ) W.measure :=
      Measure.integrableOn_of_bounded (W.finite_on_compact _ hKc hU) hF.aestronglyMeasurable
        ((ae_restrict_iff' (isClosed_closedBall.measurableSet.prod MeasurableSet.univ)).mpr
          (Eventually.of_forall hC))
    exact hOn.integrable_of_forall_notMem_eq_zero fun p hp ↦ hF0 p fun h1 ↦ hp ⟨h1, mem_univ _⟩
  have hhc : Continuous h := hh.continuous
  have hφs : Continuous (fun z : Euclidean N ↦ φ (‖z - y‖ ^ 2 / t ^ 2)) :=
    hφ.continuous.comp hs.continuous
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hf1 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) W.measure :=
    hint _ ((hφs.mul hhc).comp continuous_fst) fun p hp ↦ by rw [hφ0 p.1 hp, zero_mul]
  have hf2 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) W.measure :=
    hint _ (by fun_prop) fun p hp ↦ by rw [hdφ0 p.1 hp, zero_mul, zero_mul]
  -- (Div) with `a = h` writes the gradient term through the continuous `div_S (h · (· - y))`.
  have hG : ∀ p : Euclidean N × Grassmannian N n,
      fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) =
        Varifold.tangentialDivergence (fun w ↦ h w • (w - y)) p.1 p.2 - n * h p.1 := fun p ↦ by
    rw [hDiv h y p.1 p.2 (hh.differentiable_one p.1)]
    ring
  have hf3 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)))
      W.measure := by
    refine hint _ ?_ fun p hp ↦ by rw [hφ0 p.1 hp, zero_mul]
    simp_rw [hG]
    exact (hφs.comp continuous_fst).mul
      ((Varifold.continuous_tangentialDivergence (hh.smul (contDiff_id.sub contDiff_const))).sub
        (continuous_const.mul (hhc.comp continuous_fst)))
  -- Steps 4–6: the pointwise inequality `E ≤ div_S X_t`.
  have hpt : ∀ p : Euclidean N × Grassmannian N n,
      (n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
          t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) +
          φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ≤
        Varifold.tangentialDivergence (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))
          p.1 p.2 := by
    rintro ⟨z, S⟩
    dsimp only
    -- Step 2: `Da(z) = h(z) φ'(s) (2/t²) ⟨z - y, ·⟩ + φ(s) Dh(z)`; then (Div) with `c = y`.
    have hg : HasFDerivAt (fun x : Euclidean N ↦ ‖x - y‖ ^ 2)
        (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N))) z :=
      ((hasFDerivAt_id z).sub_const y).norm_sq
    have hη : HasDerivAt (fun r : ℝ ↦ φ (r / t ^ 2))
        (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) (‖z - y‖ ^ 2) :=
      HasDerivAt.comp (h₂ := φ) (h := fun r : ℝ ↦ r / t ^ 2) (‖z - y‖ ^ 2)
        (hφ.differentiable_one _).hasDerivAt ((hasDerivAt_id' _).div_const _)
    have hcomp : HasFDerivAt ((fun r : ℝ ↦ φ (r / t ^ 2)) ∘ fun x : Euclidean N ↦ ‖x - y‖ ^ 2)
        ((deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) •
          (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N)))) z :=
      hη.comp_hasFDerivAt z hg
    have hfd : HasFDerivAt (fun x ↦ h x * φ (‖x - y‖ ^ 2 / t ^ 2))
        (h z • ((deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) •
          (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N)))) +
          φ (‖z - y‖ ^ 2 / t ^ 2) • fderiv ℝ h z) z :=
      (hh.differentiable_one z).hasFDerivAt.fun_mul hcomp
    rw [hDiv _ y z S (ha.differentiable_one z), hfd.fderiv]
    -- Step 5: `⟨w, p_S w⟩ = ‖p_S w‖² ≤ ‖w‖²` (`p_S` is symmetric and idempotent).
    have hP : inner ℝ (S.project (z - y)) (S.project (z - y)) =
        inner ℝ (z - y) (S.project (z - y)) := by
      rw [show inner ℝ (S.project (z - y)) (S.project (z - y)) =
          inner ℝ (z - y) (S.project (S.project (z - y))) from
        Grassmannian.projectionLinearMap_isSymmetric S (z - y) (S.projectionLinearMap (z - y)),
        Grassmannian.project_project]
    have hip : inner ℝ (z - y) (S.project (z - y)) ≤ ‖z - y‖ ^ 2 := by
      linarith [norm_sub_sq_real (z - y) (S.project (z - y)),
        real_inner_self_eq_norm_sq (S.project (z - y)), sq_nonneg ‖z - y - S.project (z - y)‖]
    -- Step 6: `div_S X_t - E = (2/t²) h(z) (-φ'(s)) (‖w‖² - ⟨w, p_S w⟩) ≥ 0`.
    have hnn : 0 ≤ h z * -deriv φ (‖z - y‖ ^ 2 / t ^ 2) *
        (‖z - y‖ ^ 2 - inner ℝ (z - y) (S.project (z - y))) / t ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (hh0 z) (neg_nonneg.mpr hφa.deriv_nonpos))
        (sub_nonneg.mpr hip)) (by positivity)
    have ht3 : t * (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z) =
        deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 2) * h z := by
      field_simp
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    rw [ht3, ← sub_nonneg]
    convert mul_nonneg zero_le_two hnn using 1
    ring
  -- Steps 8–9: integrate (`μ_W = π_# W` for the first two integrals) and use `integral_mono`.
  have hw1 : ∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight =
      ∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1 ∂W.measure :=
    integral_map measurable_fst.aemeasurable (hφs.mul hhc).aestronglyMeasurable
  have hw2 : ∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight =
      ∫ p, deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1 ∂W.measure :=
    integral_map measurable_fst.aemeasurable (by fun_prop : Continuous fun z : Euclidean N ↦
      deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z).aestronglyMeasurable
  have hf12 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      (n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
        t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1)) W.measure :=
    (hf1.const_mul _).sub (hf2.const_mul _)
  calc _ = ∫ p, ((n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
          t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) +
          φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)))
          ∂W.measure := by
        rw [integral_add hf12 hf3, integral_sub (hf1.const_mul _) (hf2.const_mul _),
          integral_const_mul, integral_const_mul, hw1, hw2]
    _ ≤ _ := integral_mono (hf12.add hf3) hdiv hpt
/-- The gradient term `G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)` of the weighted radial
monotonicity argument (Simon Ch. 8, 3.3–3.5; tilt-excess estimate) satisfies
`|G(t)| ≤ M A^{n+1} ε t^{n+1}`: off `B_{tA}(y) × G(N,n)` the cutoff vanishes, on it the integrand is
at most `M (tA) ‖p_S - p_P‖`, and the tilt-excess hypothesis bounds the integral of `‖p_S - p_P‖`. -/
theorem Submission.intcpt_allard_wrm_gradient_term_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε M A t : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), 0 ≤ ε → 0 ≤ M → 0 < A → 0 < t → (∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * (t * A) ^ n) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → (∀ s, A ^ 2 ≤ s → φ s = 0) → |∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure| ≤ M * A ^ (n + 1) * ε * t ^ (n + 1) := by
  intro N n U W P y ε M A t h φ hε hM hA ht htilt hgrad hφ hφA
  have htA : 0 < t * A := mul_pos ht hA
  have hMtA : 0 ≤ M * (t * A) := mul_nonneg hM htA.le
  -- Step 1: pointwise, `|g| ≤ 1_K · M (tA) ‖p_S - p_P‖` with `K = B_{tA}(y) × G(N,n)`.
  have hpt : ∀ p : Euclidean N × Grassmannian N n,
      ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
          fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ≤
        (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))).indicator
          (fun z ↦ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖) p := by
    intro p
    by_cases hp : p ∈ closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))
    · -- On `K`: `|φ| ≤ 1` and (grad) with `|z - y| ≤ tA`.
      rw [Set.indicator_of_mem hp, ← ENNReal.ofReal_mul hMtA]
      apply ENNReal.ofReal_le_ofReal
      have hdist : ‖p.1 - y‖ ≤ t * A := by
        have h1 := hp.1
        rwa [mem_closedBall, dist_eq_norm] at h1
      have hφ1 : |φ (‖p.1 - y‖ ^ 2 / t ^ 2)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hφ (‖p.1 - y‖ ^ 2 / t ^ 2)]
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ (‖p.1 - y‖ ^ 2 / t ^ 2)| * |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))|
          ≤ 1 * |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))| :=
            mul_le_mul_of_nonneg_right hφ1 (abs_nonneg _)
        _ = |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))| := one_mul _
        _ ≤ M * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ *
              ‖p.1 - y‖ := hgrad p.1 p.2
        _ ≤ M * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ *
              (t * A) := mul_le_mul_of_nonneg_left hdist (mul_nonneg hM (norm_nonneg _))
        _ = M * (t * A) * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ := by
            ring
    · -- Off `K`: `|z - y| > tA`, so `|z - y|²/t² > A²` and the cutoff vanishes.
      rw [Set.indicator_of_notMem hp]
      have hdist : t * A < ‖p.1 - y‖ := by
        have h1 : p.1 ∉ closedBall y (t * A) := fun h1 ↦ hp ⟨h1, mem_univ _⟩
        rwa [mem_closedBall, dist_eq_norm, not_le] at h1
      have hs : A ^ 2 ≤ ‖p.1 - y‖ ^ 2 / t ^ 2 := by
        rw [le_div_iff₀ (pow_pos ht 2)]
        calc A ^ 2 * t ^ 2 = (t * A) ^ 2 := by ring
          _ ≤ ‖p.1 - y‖ ^ 2 := pow_le_pow_left₀ htA.le hdist.le 2
      rw [hφA _ hs, zero_mul, norm_zero, ENNReal.ofReal_zero]
  -- Step 2: `∫⁻ |g| ≤ ofReal (M tA) · ∫⁻_K ‖p_S - p_P‖ ≤ ofReal (M tA · ε (tA)^n)`.
  have hlint : ∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure ≤
      ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n)) := by
    calc ∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
          fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure
        ≤ ∫⁻ p, (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))).indicator
          (fun z ↦ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖) p
            ∂W.measure := lintegral_mono hpt
      _ ≤ ∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)),
          ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
            ∂W.measure := lintegral_indicator_le _ _
      _ = ENNReal.ofReal (M * (t * A)) *
          ∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)),
            ENNReal.ofReal ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
            ∂W.measure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal (ε * (t * A) ^ n) := by gcongr
      _ = ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n)) :=
          (ENNReal.ofReal_mul hMtA).symm
  -- Step 3: `|∫ g| ≤ (∫⁻ |g|).toReal ≤ M tA · ε (tA)^n = M A^{n+1} ε t^{n+1}`.
  calc |∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure|
      = ‖∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = M * (t * A) * (ε * (t * A) ^ n) :=
        ENNReal.toReal_ofReal (mul_nonneg hMtA (mul_nonneg hε (pow_nonneg htA.le n)))
    _ = M * A ^ (n + 1) * ε * t ^ (n + 1) := by ring
/-- **Simon Ch. 8, 2.5–2.6, as used in the proof of 5.10 (printed (7))** (child
`first_variation_bound` of `allard_lemma`): if `W` has locally bounded first variation, `K ⊆ U` is
compact and `X` is a `C¹` field with `spt X ⊆ K` and `|X| ≤ B`, then `|δW(X)| ≤ B ‖δW‖(K)`.
Write `δW(X) = -∫ ν·X d‖δW‖` with `|ν| = 1` `‖δW‖`-a.e. (2.6); the integrand is bounded by `B`
on `K` and vanishes off `K`. -/
theorem Submission.intcpt_allard_first_variation_le_sup_mul :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (X : Euclidean N → Euclidean N) (K : Set (Euclidean N)) (B : ℝ), W.HasLocallyBoundedFirstVariation → ContDiff ℝ 1 X → IsCompact K → K ⊆ U → tsupport X ⊆ K → (∀ z, ‖X z‖ ≤ B) → ENNReal.ofReal |W.firstVariation X| ≤ ENNReal.ofReal B * variationMeasure W K := by
  intro N n U W X K B hW hX hK hKU hXK hXB
  -- `X` is a test field of `U`: `C¹`, with compact support `spt X ⊆ K ⊆ U`.
  let T : Varifold.TestVectorField U :=
    ⟨X, hX, hK.of_isClosed_subset (isClosed_tsupport X) hXK, hXK.trans hKU⟩
  -- `‖δW‖` is the Riesz measure `μ`, with polar field `ν`, `|ν| = 1` `μ`-a.e. (2.6).
  have hμ : variationMeasure W = W.firstVariationRieszMeasure hW := by
    simp only [variationMeasure, dite_eq_left hW]
  set μ := W.firstVariationRieszMeasure hW
  set ν := W.firstVariationPolarField hW
  have hrep : W.IsFirstVariationPolarRepresentation μ ν :=
    W.isFirstVariationPolarRepresentation_riesz hW
  have hfv : W.firstVariation X = -∫ x, inner ℝ (ν x) (X x) ∂μ := (hrep.2.2 T).2
  rw [hμ, hfv, abs_neg, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ x, inner ℝ (ν x) (X x) ∂μ‖ₑ ≤ ∫⁻ x, ‖inner ℝ (ν x) (X x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator (fun _ ↦ ENNReal.ofReal B) x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hrep.2.1] with x hx
        by_cases hxK : x ∈ K
        · -- On `K`: `|ν·X| ≤ |ν| |X| = |X| ≤ B`.
          rw [indicator_of_mem hxK, Real.enorm_eq_ofReal_abs]
          apply ENNReal.ofReal_le_ofReal
          have hb := norm_inner_le_norm (𝕜 := ℝ) (ν x) (X x)
          rw [Real.norm_eq_abs, hx, one_mul] at hb
          exact hb.trans (hXB x)
        · -- Off `K ⊇ spt X` the field vanishes.
          have hz : X x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hxK (hXK h)
          simp only [hz, inner_zero_right, enorm_zero, indicator_of_notMem hxK, le_refl]
    _ = ENNReal.ofReal B * μ K := lintegral_indicator_const hK.measurableSet _
/-- The tangential divergence of the radial-type field `Y(w) = a(w) (w - y)` (the pointwise
computation behind Simon Ch. 8, 3.2–3.5): if `a` is differentiable at `z`, then
`div_S Y(z) = n a(z) + Da(z)[p_S(z - y)]`, via `DY(z) = a(z) id + Da(z) ⊗ (z - y)`,
`div_S Y(z) = trace (p_S ∘ DY(z))`, `trace p_S = n` and `trace (ℓ ⊗ u) = ℓ(u)`. -/
theorem Submission.intcpt_allard_radial_field_divergence :
    ∀ (N n : ℕ) (a : Euclidean N → ℝ) (y z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - y)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - y)) := by
  intro N n a y z S ha
  -- Step 1: the product rule, `DY(z) = a(z) • id + Da(z).smulRight (z - y)`.
  have hD : fderiv ℝ (fun w ↦ a w • (w - y)) z =
      a z • ContinuousLinearMap.id ℝ (Euclidean N) + (fderiv ℝ a z).smulRight (z - y) := by
    have hsub : DifferentiableAt ℝ (fun w : Euclidean N ↦ w - y) z :=
      differentiableAt_fun_id.sub_const y
    rw [fderiv_fun_smul ha hsub, fderiv_sub_const, fderiv_fun_id]
  -- Step 2: `div_S Y(z) = trace (S.1 * jacobian Y z) = trace (p_S ∘ DY(z))`, since `S.1` and
  -- `jacobian Y z` are the matrices of `p_S` and `DY(z)` in the standard basis.
  have htr : Varifold.tangentialDivergence (fun w ↦ a w • (w - y)) z S =
      LinearMap.trace ℝ (Euclidean N)
        (S.projectionLinearMap ∘ₗ (fderiv ℝ (fun w ↦ a w • (w - y)) z).toLinearMap) := by
    rw [Varifold.tangentialDivergence, LinearMap.trace_eq_matrix_trace ℝ
      Grassmannian.coordinateBasis.toBasis, LinearMap.toMatrix_comp
      Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis, Grassmannian.toMatrix_projectionLinearMap,
      Varifold.jacobian_eq_toMatrix]
  -- Step 3: `p_S ∘ DY(z) = a(z) • p_S + Da(z).smulRight (p_S (z - y))`.
  have hcomp : S.projectionLinearMap ∘ₗ (fderiv ℝ (fun w ↦ a w • (w - y)) z).toLinearMap =
      a z • S.projectionLinearMap +
        (fderiv ℝ a z).toLinearMap.smulRight (Grassmannian.project S (z - y)) := by
    ext v
    simp [hD, Grassmannian.project]
  -- Step 4: `trace p_S = trace S.1 = n` and `trace (ℓ.smulRight u) = ℓ u`.
  have hP : LinearMap.trace ℝ (Euclidean N) S.projectionLinearMap = n := by
    rw [LinearMap.trace_eq_matrix_trace ℝ Grassmannian.coordinateBasis.toBasis,
      Grassmannian.toMatrix_projectionLinearMap, Grassmannian.trace_eq]
  rw [htr, hcomp, map_add, map_smul, hP, LinearMap.trace_smulRight, smul_eq_mul, mul_comm,
    ContinuousLinearMap.coe_coe]

/-- Integrated weighted monotonicity (Simon Ch. 8, 3.5 integrated from `σ` to `ρ`, as for (6)–(7)
in the proof of 5.10): if (1r)–(3r) hold on `B_r(y)` for `0 < r < 1`, then for `0 < σ ≤ ρ` with
`ρA < 1` and `Ĩ(t) = ∫ φ(|z - y|²/t²) h(z) dμ_W(z)`, `Ĩ(σ)/σ^n ≤ Ĩ(ρ)/ρ^n + 2^{n+1}(M + K)ερ`.
For `t ∈ [σ, ρ]`, `tĨ'(t) - nĨ(t) ≥ G(t) - δW(X_t)`, where `X_t(z) = h(z)φ(|z - y|²/t²)(z - y)` and
`G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)`, and
`|G(t)| + |δW(X_t)| ≤ A^{n+1}(M + K)εt^{n+1}`; so `t ↦ Ĩ(t)/t^n + 2^{n+1}(M + K)εt` is
nondecreasing on `[σ, ρ]`. -/
theorem Submission.intcpt_allard_weighted_radial_monotonicity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K M A : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → 0 ≤ M → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → ContDiff ℝ 1 φ → Antitone φ → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → 0 < A → A ≤ 2 → (∀ s, A ^ 2 ≤ s → φ s = 0) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ * A < 1 → (∫ z, φ (‖z - y‖ ^ 2 / σ ^ 2) * h z ∂W.weight) / σ ^ n ≤ (∫ z, φ (‖z - y‖ ^ 2 / ρ ^ 2) * h z ∂W.weight) / ρ ^ n + 2 ^ (n + 1) * (M + K) * ε * ρ := by
  intro N n U W P y ε K M A h φ hW hU hε hK hM hvar htilt hmass hh hh01 hDh hφ hφanti hφ01 hA
    hA2 hφA σ ρ hσ hσρ hρA
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 ^ (n + 1) * (M + K) * ε := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; exact mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (add_nonneg hM hK)) hε.le
  -- Step 2: a radius `R` with `ρA < R < 1`, so `B_R(y) ⊆ B°_1(y) ⊆ U` has finite `μ_W`-mass.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (ρ * A + 1) / 2 := ⟨_, rfl⟩
  have hρAR : ρ * A < R := by rw [hR]; linarith
  have hRfin : W.weight (closedBall y R) ≠ ∞ :=
    W.weight_finite_on_compact _ (isCompact_closedBall y R)
      ((closedBall_subset_ball (by rw [hR]; linarith)).trans hU)
  -- Steps 3–7: for `t ∈ [σ, ρ]`, `tĨ'(t) - nĨ(t) ≥ G(t) - δW(X_t) ≥ -2^{n+1}(M + K)εt^{n+1}`.
  have key : ∀ t, σ ≤ t → t ≤ ρ →
      -(C * t ^ (n + 1)) ≤
        t * (∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) -
          n * (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) := by
    intro t hσt htρ
    have ht0 : 0 < t := hσ.trans_le hσt
    have htA0 : 0 < t * A := mul_pos ht0 hA
    have htA1 : t * A < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right htρ hA.le) hρA
    have hball : closedBall y (t * A) ⊆ U := (closedBall_subset_ball htA1).trans hU
    -- The weighted radial inequality (Simon 8.3.5 with the normal term dropped).
    have hlow := Submission.intcpt_allard_wrm_first_variation_lower_bound N n U W y h φ A t
      (Submission.intcpt_allard_radial_field_divergence N n) hh (fun z ↦ (hh01 z).1) hφ hφanti
      hA hφA ht0 hball
    -- (b): `|G(t)| ≤ M A^{n+1} ε t^{n+1}`, from (2r) at radius `tA`.
    have hgrad := Submission.intcpt_allard_wrm_gradient_term_bound N n U W P y ε M A t h φ hε.le
      hM hA ht0 (htilt (t * A) htA0 htA1) hDh hφ01 hφA
    -- (a): `|δW(X_t)| ≤ K A^{n+1} ε t^{n+1}`, from (1r) and (3r) at radius `tA`.
    have hvanish : ∀ z : Euclidean N, t * A ≤ ‖z - y‖ → φ (‖z - y‖ ^ 2 / t ^ 2) = 0 := by
      intro z hz
      apply hφA
      rw [le_div_iff₀ (pow_pos ht0 2)]
      calc A ^ 2 * t ^ 2 = (t * A) ^ 2 := by ring
        _ ≤ ‖z - y‖ ^ 2 := pow_le_pow_left₀ htA0.le hz 2
    have hX1 : ContDiff ℝ 1 (fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) := by
      have hsq : ContDiff ℝ 1 (fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2) :=
        ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _
      exact (hh.mul (hφ.comp hsq)).smul (contDiff_id.sub contDiff_const)
    have hsupp : tsupport (fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) ⊆
        closedBall y (t * A) := by
      refine closure_minimal ?_ isClosed_closedBall
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      by_contra hlt
      exact hz (by simp [hvanish z (not_le.mp hlt).le])
    have hbound : ∀ z, ‖(fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) z‖ ≤
        t * A := by
      intro z
      by_cases hz : t * A ≤ ‖z - y‖
      · simp [hvanish z hz, htA0.le]
      · have h1 : |h z * φ (‖z - y‖ ^ 2 / t ^ 2)| ≤ 1 := by
          rw [abs_of_nonneg (mul_nonneg (hh01 z).1 (hφ01 _).1)]
          calc h z * φ (‖z - y‖ ^ 2 / t ^ 2) ≤ 1 * 1 :=
                mul_le_mul (hh01 z).2 (hφ01 _).2 (hφ01 _).1 zero_le_one
            _ = 1 := one_mul 1
        show ‖(h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)‖ ≤ t * A
        rw [norm_smul, Real.norm_eq_abs]
        calc |h z * φ (‖z - y‖ ^ 2 / t ^ 2)| * ‖z - y‖ ≤ 1 * (t * A) :=
              mul_le_mul h1 (not_le.mp hz).le (norm_nonneg _) zero_le_one
          _ = t * A := one_mul _
    have hδ : |W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))| ≤
        K * A ^ (n + 1) * ε * t ^ (n + 1) := by
      have hfv := Submission.intcpt_allard_first_variation_le_sup_mul N n U W
        (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) (closedBall y (t * A)) (t * A) hW hX1
        (isCompact_closedBall y (t * A)) hball hsupp hbound
      have hchain : ENNReal.ofReal |W.firstVariation
          (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))| ≤
          ENNReal.ofReal (t * A * (ε * (K * (t * A) ^ n))) := by
        calc ENNReal.ofReal |W.firstVariation
              (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))|
            ≤ ENNReal.ofReal (t * A) * variationMeasure W (closedBall y (t * A)) := hfv
          _ ≤ ENNReal.ofReal (t * A) * (ENNReal.ofReal ε * W.weight (closedBall y (t * A))) :=
            mul_le_mul_of_nonneg_left (hvar (t * A) htA0 htA1) zero_le
          _ ≤ ENNReal.ofReal (t * A) * (ENNReal.ofReal ε * ENNReal.ofReal (K * (t * A) ^ n)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hmass (t * A) htA0 htA1) zero_le) zero_le
          _ = ENNReal.ofReal (t * A * (ε * (K * (t * A) ^ n))) := by
            rw [ENNReal.ofReal_mul htA0.le, ENNReal.ofReal_mul hε.le]
      calc |W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))|
          ≤ t * A * (ε * (K * (t * A) ^ n)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg htA0.le (mul_nonneg hε.le
              (mul_nonneg hK (pow_nonneg htA0.le n))))).mp hchain
        _ = K * A ^ (n + 1) * ε * t ^ (n + 1) := by ring
    -- (c): combine, using `A^{n+1} ≤ 2^{n+1}`.
    have hA' : (M + K) * ε * t ^ (n + 1) * A ^ (n + 1) ≤
        (M + K) * ε * t ^ (n + 1) * 2 ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hA2 (n + 1))
        (mul_nonneg (mul_nonneg (add_nonneg hM hK) hε.le) (pow_nonneg ht0.le _))
    have hG := (abs_le.mp hgrad).1
    have hδ' := (abs_le.mp hδ).2
    rw [hC]
    linarith
  -- The derivative of `F(t) = Ĩ(t)/t^n + Ct` is `(tĨ'(t) - nĨ(t))/t^{n+1} + C ≥ 0`.
  have alg : ∀ t I J : ℝ, 0 < t → -(C * t ^ (n + 1)) ≤ t * J - n * I →
      0 ≤ (J * t ^ n - I * (n * t ^ (n - 1))) / (t ^ n) ^ 2 + C * 1 := by
    intro t I J ht0 hk
    have hpow : ∀ m : ℕ, (m : ℝ) * t ^ (m - 1) * t = m * t ^ m := by
      intro m
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        ring
    have htn : 0 < t ^ n := pow_pos ht0 n
    have h1 : t ^ n * (-(C * t ^ (n + 1))) ≤ t ^ n * (t * J - n * I) :=
      mul_le_mul_of_nonneg_left hk htn.le
    have h2 : -C * (t ^ n) ^ 2 * t ≤ (J * t ^ n - I * (n * t ^ (n - 1))) * t := by
      have e1 : -C * (t ^ n) ^ 2 * t = t ^ n * (-(C * t ^ (n + 1))) := by ring
      have e2 : (J * t ^ n - I * (n * t ^ (n - 1))) * t = t ^ n * (t * J - n * I) := by
        calc (J * t ^ n - I * (n * t ^ (n - 1))) * t =
            J * t ^ n * t - I * ((n : ℝ) * t ^ (n - 1) * t) := by ring
          _ = t ^ n * (t * J - n * I) := by rw [hpow n]; ring
      rw [e1, e2]
      exact h1
    have h3 : -C ≤ (J * t ^ n - I * (n * t ^ (n - 1))) / (t ^ n) ^ 2 := by
      rw [le_div_iff₀ (pow_pos htn 2)]
      exact le_of_mul_le_mul_right h2 ht0
    linarith
  -- Step 5: `Ĩ` is differentiable on `[σ, ρ]`, hence so is `F`.
  have hderiv : ∀ t, σ ≤ t → t ≤ ρ →
      HasDerivAt (fun s ↦ (∫ z, φ (‖z - y‖ ^ 2 / s ^ 2) * h z ∂W.weight) / s ^ n + C * s)
        (((∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) *
            t ^ n - (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) * (n * t ^ (n - 1))) /
          (t ^ n) ^ 2 + C * 1) t := by
    intro t hσt htρ
    have ht0 : 0 < t := hσ.trans_le hσt
    have hI := Submission.intcpt_allard_wrm_cutoff_mass_hasDerivAt N W.weight y h φ A R t
      hh.continuous hφ hA hφA hRfin ht0
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right htρ hA.le) hρAR)
    exact (hI.div (hasDerivAt_pow n t) (pow_ne_zero n ht0.ne')).add
      ((hasDerivAt_id' t).const_mul C)
  -- Step 8: `F` is monotone on `[σ, ρ]`, so `F(σ) ≤ F(ρ)`.
  have hmono : MonotoneOn
      (fun s ↦ (∫ z, φ (‖z - y‖ ^ 2 / s ^ 2) * h z ∂W.weight) / s ^ n + C * s) (Icc σ ρ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc σ ρ)
      (fun t ht ↦ (hderiv t ht.1 ht.2).continuousAt.continuousWithinAt) (fun t ht ↦ ?_)
      (fun t ht ↦ ?_)
    · rw [interior_Icc] at ht
      exact (hderiv t ht.1.le ht.2.le).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hderiv t ht.1.le ht.2.le).deriv]
      exact alg t _ _ (hσ.trans ht.1) (key t ht.1.le ht.2.le)
  have hF := hmono ⟨le_rfl, hσρ⟩ ⟨hσρ, le_rfl⟩ hσρ
  have hCσ : 0 ≤ C * σ := mul_nonneg hC0 hσ.le
  simp only at hF
  rw [← hC]
  linarith

/-- Cylinder monotonicity (Simon Ch. 8, (7) in the proof of 5.10, "proved by simply integrating
3.5"): under (1r)–(3r) on `B_r(y)` for `0 < r < 1`, for `0 < τ ≤ 1` and `0 < σ ≤ ρ < 1`,
`μ_W(U^τ_σ(y))/σ^n ≤ μ_W(U^{2τ}_ρ(y))/ρ^n + C(1 + K)ερ/τ` with `C = 2^{n+1}(M₀ + 1)`, where
`U^τ_r(y) = B_r(y) ∩ {z : |q(z - y)| < τ}` and `q = id - p_P`.  The integrated weighted
monotonicity is applied to a cylindrical weight `h` (`1` where `|q(z - y)| < τ`, `0` where
`|q(z - y)| ≥ 2τ`, `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ)|p_S - p_P||z - y|`) and radial cutoffs `φ_j` with
`A_j ↓ 1`; letting `j → ∞` gives the inequality for `∫_{B_t(y)} h dμ_W`, which bounds the
cylinder masses. -/
theorem Submission.intcpt_allard_cylinder_monotonicity :
    ∀ (N n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → W.weight (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ W.weight (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (C * (1 + K) * ε * ρ / τ) := by
  intro N n
  -- Step 0: `C = 2^{n+1}(M₀ + 1)`, where `M₀/τ` is the gradient constant of the cylindrical weight.
  obtain ⟨M₀, hM₀, hweight⟩ := Submission.intcpt_allard_cm_cylinder_weight
  refine ⟨2 ^ (n + 1) * (M₀ + 1), mul_nonneg (pow_nonneg zero_le_two _) (by linarith), ?_⟩
  intro U W P y ε K hW hU hε hK hvar htilt hmass τ σ ρ hτ hτ1 hσ hσρ hρ
  have hρ0 : 0 < ρ := hσ.trans_le hσρ
  -- Step 2: the cylindrical weight `h`.
  obtain ⟨h, hh, hh01, hh1, hh0, hDh⟩ := hweight N n P y τ hτ
  have hhm : Measurable h := hh.continuous.measurable
  -- Step 1: `A_j = 1 + (1 - ρ)/(2(j + 1)) ↓ 1`, with `A_j ≤ 2` and `ρA_j ≤ R := (1 + ρ)/2 < 1`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hR1 : R < 1 := by rw [hR]; linarith
  obtain ⟨A, hA1, hA2, hρA, hAlim⟩ : ∃ A : ℕ → ℝ, (∀ j, 1 < A j) ∧ (∀ j, A j ≤ 2) ∧
      (∀ j, ρ * A j ≤ R) ∧ Tendsto A atTop (𝓝 1) := by
    have hx : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) ∧ 1 / ((j : ℝ) + 1) ≤ 1 := fun j ↦
      ⟨by positivity, (div_le_one₀ (by positivity)).2 (by linarith [j.cast_nonneg (α := ℝ)])⟩
    refine ⟨fun j ↦ 1 + (1 - ρ) / 2 * (1 / ((j : ℝ) + 1)), fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
    · nlinarith [mul_pos (sub_pos.2 hρ) (hx j).1]
    · nlinarith [mul_nonneg hρ0.le (hx j).1.le, (hx j).2]
    · rw [hR]
      nlinarith [mul_nonneg (sub_nonneg.2 hρ.le) (sub_nonneg.2 hρ.le),
        mul_nonneg (mul_nonneg hρ0.le (sub_nonneg.2 hρ.le)) (sub_nonneg.2 (hx j).2)]
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((1 - ρ) / 2)).const_add 1
  have hA0 : ∀ j, 0 < A j := fun j ↦ zero_lt_one.trans (hA1 j)
  -- The radial cutoffs `φ_j`: `1` on `(-∞, 1]`, `0` on `[A_j², ∞)`.
  choose φ hφ hφanti hφ01 hφ1 hφ0 using fun j ↦
    Submission.intcpt_allard_cm_radial_cutoff (A j) (hA1 j)
  -- Step 3: for each `j`, the integrated weighted monotonicity with `M = M₀/τ`.
  have hj : ∀ j, (∫ z, φ j (‖z - y‖ ^ 2 / σ ^ 2) * h z ∂W.weight) / σ ^ n ≤
      (∫ z, φ j (‖z - y‖ ^ 2 / ρ ^ 2) * h z ∂W.weight) / ρ ^ n +
        2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ := fun j ↦
    Submission.intcpt_allard_weighted_radial_monotonicity N n U W P y ε K (M₀ / τ) (A j) h (φ j)
      hW hU hε hK (div_nonneg hM₀ hτ.le) hvar htilt hmass hh hh01 hDh (hφ j) (hφanti j) (hφ01 j)
      (hA0 j) (hA2 j) (hφ0 j) σ ρ hσ hσρ ((hρA j).trans_lt hR1)
  -- Step 4: let `j → ∞`; `B_R(y) ⊆ B°_1(y) ⊆ U` is compact, so `μ_W(B_R(y)) < ∞`.
  have hRfin : W.weight (closedBall y R) ≠ ∞ :=
    W.weight_finite_on_compact _ (isCompact_closedBall y R) ((closedBall_subset_ball hR1).trans hU)
  have hlim : ∀ t, 0 < t → t ≤ ρ →
      Tendsto (fun j ↦ ∫ z, φ j (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) atTop
        (𝓝 (∫ z in closedBall y t, h z ∂W.weight)) := fun t ht htρ ↦
    Submission.intcpt_allard_cm_cutoff_integral_tendsto N W.weight y h φ A t R hhm hh01
      (fun j ↦ (hφ j).continuous.measurable) hφ01 hφ1 hφ0 hA0 hAlim ht
      (fun j ↦ (mul_le_mul_of_nonneg_right htρ (hA0 j).le).trans (hρA j)) hRfin
  have hI : (∫ z in closedBall y σ, h z ∂W.weight) / σ ^ n ≤
      (∫ z in closedBall y ρ, h z ∂W.weight) / ρ ^ n + 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ :=
    le_of_tendsto_of_tendsto' ((hlim σ hσ hσρ).div_const _)
      (((hlim ρ hρ0 le_rfl).div_const _).add_const _) hj
  -- `2^{n+1}(M₀/τ + K)ερ ≤ C(1 + K)ερ/τ`, since `τ ≤ 1` gives `M₀ + Kτ ≤ (M₀ + 1)(1 + K)`.
  have hMK : M₀ / τ + K ≤ (M₀ + 1) * (1 + K) / τ := by
    rw [div_add' _ _ _ hτ.ne', div_le_div_iff_of_pos_right hτ]
    nlinarith [mul_nonneg hM₀ hK, mul_nonneg hK (sub_nonneg.2 hτ1)]
  have hE : 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ ≤
      2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ :=
    calc 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ = 2 ^ (n + 1) * ε * ρ * (M₀ / τ + K) := by ring
      _ ≤ 2 ^ (n + 1) * ε * ρ * ((M₀ + 1) * (1 + K) / τ) :=
        mul_le_mul_of_nonneg_left hMK (mul_pos (mul_pos (pow_pos two_pos _) hε) hρ0).le
      _ = 2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ := by ring
  -- Step 5: compare the ball integrals of `h` with the cylinder masses.
  exact Submission.intcpt_allard_cm_cylinder_mass_bound N n W.weight P y h τ σ ρ
    (2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ) hhm hh01 hh1 hh0 hσ hσρ
    (W.weight_finite_on_compact _ (isCompact_closedBall y ρ) ((closedBall_subset_ball hρ).trans hU))
    (by linarith)
/-- Cylinder grouping (Simon Ch. 8, proof of 5.10 (8), steps (b)–(d)): for a `d`-separated finite
set `s` in one fibre of `p = Grassmannian.project P`, the cylinders `U^{d/2}_ρ(y)`, `y ∈ s`, are
disjoint and lie in the enlarged cylinders `U^{d/2+S}_{ρ+S}(z)` about representatives `z ∈ Z`
within distance `S`; hence the `ρ^{-n}`-normalized sum over `s` is at most `1 + (2^n - 1) u` times
the `(ρ + S)^{-n}`-normalized sum over `Z`, when `S ≤ u ρ` and `u ≤ 1`. -/
theorem Submission.intcpt_allard_ccb_cylinder_grouping :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s Z : Finset (Euclidean N)) (d ρ S u : ℝ), (∀ y ∈ s, Grassmannian.project P y = x) → Z ⊆ s → 0 < d → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖) → 0 < ρ → 0 ≤ S → S ≤ u * ρ → u ≤ 1 → (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) → ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) / ENNReal.ofReal ρ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * u) * ∑ y ∈ Z, μ (closedBall y (ρ + S) ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2 + S}) / ENNReal.ofReal (ρ + S) ^ n := by
  intro N n μ P x s Z d ρ S u hpx hZs hd hsep hρ hS hSu hu1 hcov
  classical
  -- Step 0: `p = Grassmannian.project P` is linear and continuous, and `p (y - y') = 0` on `s`.
  have hsub : ∀ a b : Euclidean N,
      Grassmannian.project P (a - b) = Grassmannian.project P a - Grassmannian.project P b :=
    fun a b ↦ map_sub (Grassmannian.projectionLinearMap P) a b
  have hadd : ∀ a b : Euclidean N,
      Grassmannian.project P (a + b) = Grassmannian.project P a + Grassmannian.project P b :=
    fun a b ↦ map_add (Grassmannian.projectionLinearMap P) a b
  have hcont : Continuous (Grassmannian.project P) :=
    (Grassmannian.projectionLinearMap P).continuous_of_finiteDimensional
  have hfibre : ∀ y ∈ s, ∀ y' ∈ s, Grassmannian.project P (y - y') = 0 := fun y hy y' hy' ↦ by
    rw [hsub, hpx y hy, hpx y' hy', sub_self]
  have hu0 : 0 ≤ u := by nlinarith
  -- Step 1: representatives `r y ∈ Z` with `‖y - r y‖ ≤ S`.
  choose! r hrZ hrS using hcov
  -- Steps 2–5: the disjoint Borel cylinders about the fibre `{y ∈ s | r y = w}` lie in the
  -- enlarged cylinder about `w`.
  have hfib : ∀ w ∈ Z, ∑ y ∈ s with r y = w,
      μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) ≤
        μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) := by
    intro w hw
    rw [← measure_biUnion_finset]
    · -- Step 4: inclusion, by the triangle inequality and `q (z - r y) = q (z - y) + (y - r y)`.
      refine measure_mono (iUnion₂_subset fun y hy z hz ↦ ?_)
      obtain ⟨hys, rfl⟩ := Finset.mem_filter.1 hy
      have hws : r y ∈ s := hZs (hrZ y hys)
      obtain ⟨hzball, hzcyl⟩ := hz
      rw [mem_closedBall, dist_eq_norm] at hzball
      have hq : (z - r y) - Grassmannian.project P (z - r y) =
          ((z - y) - Grassmannian.project P (z - y)) + (y - r y) := by
        have h1 : z - r y = (z - y) + (y - r y) := by abel
        rw [h1, hadd, hfibre y hys (r y) hws, add_zero]
        abel
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm]
        calc ‖z - r y‖ = ‖(z - y) + (y - r y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖y - r y‖ := norm_add_le _ _
          _ ≤ ρ + S := add_le_add hzball (hrS y hys)
      · show ‖(z - r y) - Grassmannian.project P (z - r y)‖ < d / 2 + S
        rw [hq]
        calc _ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ + ‖y - r y‖ := norm_add_le _ _
          _ < d / 2 + S := add_lt_add_of_lt_of_le hzcyl (hrS y hys)
    · -- Step 3: disjointness, as `y - y' = q (z - y') - q (z - y)` would have norm `< d`.
      intro y hy y' hy' hne
      have hys : y ∈ s := (Finset.mem_filter.1 hy).1
      have hy's : y' ∈ s := (Finset.mem_filter.1 hy').1
      refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
      have h1 : ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2 := hz.2
      have h2 : ‖(z - y') - Grassmannian.project P (z - y')‖ < d / 2 := hz'.2
      have hkey : y - y' = ((z - y') - Grassmannian.project P (z - y')) -
          ((z - y) - Grassmannian.project P (z - y)) := by
        have h3 : Grassmannian.project P (z - y') - Grassmannian.project P (z - y) =
            Grassmannian.project P (y - y') := by
          rw [← hsub]
          congr 1
          abel
        rw [hfibre y hys y' hy's, sub_eq_zero] at h3
        rw [h3]
        abel
      have h4 : ‖y - y'‖ < d := by
        rw [hkey]
        calc _ ≤ ‖(z - y') - Grassmannian.project P (z - y')‖ +
              ‖(z - y) - Grassmannian.project P (z - y)‖ := norm_sub_le _ _
          _ < d / 2 + d / 2 := add_lt_add h2 h1
          _ = d := add_halves d
      linarith [hsep y hys y' hy's hne]
    · -- Step 2: each cylinder is a closed ball intersected with an open set.
      intro y _
      refine measurableSet_closedBall.inter (IsOpen.measurableSet ?_)
      exact isOpen_lt (by fun_prop) continuous_const
  -- Step 6: `(1 + u)^k ≤ 1 + (2^k - 1) u` for `0 ≤ u ≤ 1`.
  have hF1 : ∀ k : ℕ, (1 + u) ^ k ≤ 1 + (2 ^ k - 1) * u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      calc (1 + u) ^ (k + 1) = (1 + u) ^ k * (1 + u) := pow_succ _ _
        _ ≤ (1 + (2 ^ k - 1) * u) * (1 + u) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + (2 ^ (k + 1) - 1) * u := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h2k) hu0) (sub_nonneg.2 hu1)]
  -- Step 7: rescaling, `X / ρ^n ≤ κ (X / (ρ + S)^n)` with `κ = ofReal (1 + (2^n - 1) u)`.
  have hk1 : (1 : ℝ) ≤ 1 + (2 ^ n - 1) * u := by
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hreal : (ρ + S) ^ n ≤ (1 + (2 ^ n - 1) * u) * ρ ^ n := by
    calc (ρ + S) ^ n ≤ ((1 + u) * ρ) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (1 + u) ^ n * ρ ^ n := mul_pow _ _ _
      _ ≤ (1 + (2 ^ n - 1) * u) * ρ ^ n :=
          mul_le_mul_of_nonneg_right (hF1 n) (pow_nonneg hρ.le n)
  have hκ : ENNReal.ofReal (ρ + S) ^ n ≤
      ENNReal.ofReal (1 + (2 ^ n - 1) * u) * ENNReal.ofReal ρ ^ n := by
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hκ0 : ENNReal.ofReal (1 + (2 ^ n - 1) * u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hresc : ∀ X : ℝ≥0∞, X / ENNReal.ofReal ρ ^ n ≤
      ENNReal.ofReal (1 + (2 ^ n - 1) * u) * (X / ENNReal.ofReal (ρ + S) ^ n) := by
    intro X
    rw [← ENNReal.mul_div_mul_left X (ENNReal.ofReal ρ ^ n) hκ0 ENNReal.ofReal_ne_top,
      ← mul_div_assoc]
    exact ENNReal.div_le_div_left hκ _
  -- Step 8: group the sum over `s` by representatives, then rescale.
  calc ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
        ENNReal.ofReal ρ ^ n
      = ∑ w ∈ Z, ∑ y ∈ s with r y = w,
          μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
            ENNReal.ofReal ρ ^ n :=
        (Finset.sum_fiberwise_of_maps_to hrZ _).symm
    _ = ∑ w ∈ Z, (∑ y ∈ s with r y = w,
          μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2})) /
            ENNReal.ofReal ρ ^ n := by
        simp_rw [ENNReal.sum_div]
    _ ≤ ∑ w ∈ Z, μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) / ENNReal.ofReal ρ ^ n :=
        Finset.sum_le_sum fun w hw ↦ ENNReal.div_le_div_right (hfib w hw) _
    _ ≤ ∑ w ∈ Z, ENNReal.ofReal (1 + (2 ^ n - 1) * u) * (μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) /
            ENNReal.ofReal (ρ + S) ^ n) :=
        Finset.sum_le_sum fun w _ ↦ hresc _
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- One-point bound from monotonicity (Simon Ch. 8, 5.10, proof of (8), one point): if
`‖y - x‖ < ε ≤ δ⁴`, `0 < δ ≤ 1/2`, `0 < σ ≤ δ²` and `r ↦ e^{εr} μ(B_r(y)) / r^n` is non-decreasing
on `(0,1)`, then `μ(B_σ(y)) / σ^n ≤ (1 + 2^{n+2} δ²) μ(B_1(x))`. -/
theorem Submission.intcpt_allard_ccb_one_point_ball_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (δ ε σ : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * μ (closedBall y r) / ENNReal.ofReal r ^ n) (Ioo 0 1) → 0 < σ → σ ≤ δ ^ 2 → μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1) := by
  intro N n μ x y δ ε σ hδ hδ2 hε hεδ hyx hmono hσ hσδ
  -- Step 1: `ε ≤ δ⁴ ≤ δ² ≤ 1/4`, so `σ, 1 - ε ∈ (0,1)` and `σ ≤ 1 - ε`.
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
  have hεδ2 : ε ≤ δ ^ 2 := hεδ.trans hδ4
  have hε4 : ε ≤ 1 / 4 := hεδ2.trans hδsq
  have hσ1 : σ < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have h1ε1 : 1 - ε < 1 := by linarith
  have hσle : σ ≤ 1 - ε := by linarith
  -- Step 2: monotonicity `f(σ) ≤ f(1 - ε)`.
  have hf : ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤
      ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
        ENNReal.ofReal (1 - ε) ^ n :=
    hmono ⟨hσ, hσ1⟩ ⟨h1ε, h1ε1⟩ hσle
  -- Step 3: `e^{εσ} ≥ 1`, so `μ(B_σ(y)) / σ^n ≤ f(σ)`.
  have hlow : μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤
      ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n := by
    refine ENNReal.div_le_div_right ?_ _
    calc μ (closedBall y σ) = 1 * μ (closedBall y σ) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) :=
        mul_le_mul' (ENNReal.one_le_ofReal.2 (Real.one_le_exp (by positivity))) le_rfl
  -- Step 4: `B_{1-ε}(y) ⊆ B_1(x)` and `e^{ε(1-ε)} ≤ e^ε`.
  have hball : closedBall y (1 - ε) ⊆ closedBall x 1 := by
    apply closedBall_subset_closedBall'
    rw [dist_eq_norm]
    linarith
  have hexp : ENNReal.ofReal (Real.exp (ε * (1 - ε))) ≤ ENNReal.ofReal (Real.exp ε) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have hup : ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
        ENNReal.ofReal (1 - ε) ^ n ≤
      ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n :=
    ENNReal.div_le_div_right (mul_le_mul' hexp (measure_mono hball)) _
  -- Step 5: `ofReal(e^ε) μ(B_1(x)) / ofReal(1 - ε)^n = ofReal(e^ε / (1 - ε)^n) μ(B_1(x))`.
  have hrw : ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n =
      ENNReal.ofReal (Real.exp ε / (1 - ε) ^ n) * μ (closedBall x 1) := by
    rw [ENNReal.mul_div_right_comm, ← ENNReal.ofReal_pow h1ε.le,
      ← ENNReal.ofReal_div_of_pos (pow_pos h1ε n)]
  -- Step 6: the real inequality `e^ε / (1 - ε)^n ≤ 1 + 2^{n+2} δ²`.
  -- (F1) `(1 + u)^k ≤ 1 + (2^k - 1) u` for `0 ≤ u ≤ 1`, by induction on `k`.
  have hF1 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ k : ℕ, (1 + u) ^ k ≤ 1 + (2 ^ k - 1) * u := by
    intro u hu0 hu1 k
    induction k with
    | zero => simp
    | succ k ih =>
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      calc (1 + u) ^ (k + 1) = (1 + u) ^ k * (1 + u) := pow_succ _ _
        _ ≤ (1 + (2 ^ k - 1) * u) * (1 + u) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ = 1 + 2 ^ k * u + (2 ^ k - 1) * u ^ 2 := by ring
        _ ≤ 1 + 2 ^ k * u + (2 ^ k - 1) * u := by
          have hu2 : u ^ 2 ≤ u := by nlinarith
          have := mul_le_mul_of_nonneg_left hu2 (sub_nonneg.2 h2k)
          linarith
        _ = 1 + (2 ^ (k + 1) - 1) * u := by ring
  -- (F2) `e^ε ≤ 1 / (1 - ε) ≤ 1 + 2ε`.
  have hinv : 1 / (1 - ε) ≤ 1 + 2 * ε := by
    rw [div_le_iff₀ h1ε]
    nlinarith
  have hF2 : Real.exp ε ≤ 1 + 2 * ε :=
    (Real.exp_bound_div_one_sub_of_interval hε.le (by linarith)).trans hinv
  have hpow : 1 / (1 - ε) ^ n ≤ 1 + (2 ^ n - 1) * (2 * ε) := by
    calc 1 / (1 - ε) ^ n = (1 / (1 - ε)) ^ n := (one_div_pow _ _).symm
      _ ≤ (1 + 2 * ε) ^ n := pow_le_pow_left₀ (one_div_nonneg.2 h1ε.le) hinv n
      _ ≤ 1 + (2 ^ n - 1) * (2 * ε) := hF1 (2 * ε) (by linarith) (by linarith) n
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hreal : Real.exp ε / (1 - ε) ^ n ≤ 1 + 2 ^ (n + 2) * δ ^ 2 := by
    calc Real.exp ε / (1 - ε) ^ n = Real.exp ε * (1 / (1 - ε) ^ n) := (mul_one_div _ _).symm
      _ ≤ (1 + 2 * ε) * (1 + (2 ^ n - 1) * (2 * ε)) :=
        mul_le_mul hF2 hpow (one_div_nonneg.2 (pow_nonneg h1ε.le n)) (by linarith)
      _ = 1 + 2 ^ n * (2 * ε) + (2 ^ n - 1) * (4 * ε ^ 2) := by ring
      _ ≤ 1 + 2 ^ n * (2 * ε) + 2 ^ n * (4 * ε ^ 2) := by
        have := mul_le_mul_of_nonneg_right (sub_le_self (2 ^ n : ℝ) zero_le_one)
          (by positivity : (0 : ℝ) ≤ 4 * ε ^ 2)
        linarith
      _ ≤ 1 + 2 ^ n * (2 * ε) + 2 ^ n * (2 * ε) := by
        have h4 : 4 * ε ^ 2 ≤ 2 * ε := by nlinarith
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 ^ n)
        linarith
      _ = 1 + 2 ^ (n + 2) * ε := by ring
      _ ≤ 1 + 2 ^ (n + 2) * δ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hεδ2 (by positivity : (0 : ℝ) ≤ 2 ^ (n + 2))
        linarith
  -- Step 7: chain the estimates.
  calc μ (closedBall y σ) / ENNReal.ofReal σ ^ n
      ≤ ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n := hlow
    _ ≤ ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
          ENNReal.ofReal (1 - ε) ^ n := hf
    _ ≤ ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n := hup
    _ = ENNReal.ofReal (Real.exp ε / (1 - ε) ^ n) * μ (closedBall x 1) := hrw
    _ ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- Reduction step (Simon Ch. 8, proof of 5.10 (8), inductive step for `#s ≥ 2`): let `s` be a
`4τ`-separated set of `2 ≤ #s ≤ m + 1` points in one fibre of `p = Grassmannian.project P`, each
within `ε` of that plane and satisfying the comparison (C_y).  Cluster selection (CS) at the minimal
distance `d` of `s` gives `Z ⊆ s` with `#Z ≤ m` and admissible scales `σ' = ρ + S`, `τ' = d/2 + S`
(`ρ = d/(4δ²)`) such that the `σ^{-n}`-normalized cylinder sum over `s` is at most
`1 + (2^n - 1) a δ²` times the `σ'^{-n}`-normalized sum over `Z`, plus `(m + 1) K δ²`, where
`a = 4 (10 (m + 1))^{m + 1}`. -/
theorem Submission.intcpt_allard_ccb_reduction_step :
    ∀ (N n : ℕ) (K : ℝ) (m : ℕ), (∀ (t : Finset (Euclidean N)) (d : ℝ), 2 ≤ t.card → 0 < d → (∀ y ∈ t, ∀ y' ∈ t, y ≠ y' → d ≤ ‖y - y'‖) → (∃ y ∈ t, ∃ y' ∈ t, y ≠ y' ∧ ‖y - y'‖ ≤ d) → ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ t ∧ Z.card < t.card ∧ 0 ≤ S ∧ S ≤ (10 * (t.card : ℝ)) ^ t.card * d ∧ (∀ y ∈ t, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖) → 0 ≤ K → ∀ δ ε : ℝ, 0 < δ → δ ≤ 1 / (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) → 0 < ε → ε ≤ δ ^ 4 → ∀ (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)), 2 ≤ s.card → s.card ≤ m + 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ ‖y - Grassmannian.project P y‖ < ε ∧ ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∃ (Z : Finset (Euclidean N)) (σ' τ' : ℝ), Z ⊆ s ∧ Z.card ≤ m ∧ 0 < σ' ∧ σ' ≤ δ ^ 2 ∧ 2 * δ ^ 2 * σ' ≤ τ' ∧ (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 4 * τ' ≤ ‖z - z'‖) ∧ ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) * δ ^ 2) * ∑ y ∈ Z, μ (closedBall y σ' ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ'}) / ENNReal.ofReal σ' ^ n + ENNReal.ofReal (((m : ℝ) + 1) * K * δ ^ 2) := by
  intro N n K m hCS hK δ ε hδ hδa hε hεδ μ P x s hs2 hsm hy σ τ hσ hσδ hστ hsep
  classical
  -- Step 0: elementary bounds, with `a = 4 (10 (m + 1))^{m + 1} ≥ 40` and `u = a δ² ≤ 1`.
  set a : ℝ := 4 * (10 * ((m : ℝ) + 1)) ^ (m + 1) with ha_def
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ 10 * ((m : ℝ) + 1) := by linarith
  have hpow : 10 * ((m : ℝ) + 1) ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) := by
    calc 10 * ((m : ℝ) + 1) = (10 * ((m : ℝ) + 1)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hm1 (by omega)
  have ha40 : 40 ≤ a := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have haδ : a * δ ≤ 1 := by
    rw [le_div_iff₀ ha0] at hδa
    linarith [mul_comm a δ]
  have h40δ : 40 * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha40 hδ.le
    linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hδ2le : δ ^ 2 ≤ δ := by rw [sq]; exact mul_le_of_le_one_left hδ.le hδ1
  have h2δ2 : 2 * δ ^ 2 ≤ 1 := by linarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by
    have : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left hδ2pos.le (hδ2le.trans hδ1)
  have hu1 : a * δ ^ 2 ≤ 1 := by
    have : a * δ ^ 2 = (a * δ) * δ := by ring
    rw [this]
    calc (a * δ) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right haδ hδ.le
      _ ≤ 1 := by linarith
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hστ
  have hyx : ∀ y ∈ s, ‖y - x‖ < ε := fun y hys ↦ by
    have h := hy y hys
    rw [← h.1]; exact h.2.1
  -- Step 1: the minimal distance `d` of `s`, attained at a pair `q`; `4τ ≤ d < 2ε`.
  have hne : s.offDiag.Nonempty := by
    obtain ⟨y, hys, y', hy's, hyy'⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    exact ⟨(y, y'), Finset.mem_offDiag.2 ⟨hys, hy's, hyy'⟩⟩
  obtain ⟨q, hq, hqmin⟩ := Finset.exists_min_image s.offDiag (fun q ↦ ‖q.1 - q.2‖) hne
  obtain ⟨hq1, hq2, hq12⟩ := Finset.mem_offDiag.1 hq
  set d : ℝ := ‖q.1 - q.2‖ with hd_def
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hq12)
  have hdmin : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖ := fun y hys y' hy's hyy' ↦
    hqmin (y, y') (Finset.mem_offDiag.2 ⟨hys, hy's, hyy'⟩)
  have hd2ε : d < 2 * ε := by
    have h1 := hyx q.1 hq1
    have h2 := hyx q.2 hq2
    calc d = ‖(q.1 - x) - (q.2 - x)‖ := by rw [hd_def]; congr 1; abel
      _ ≤ ‖q.1 - x‖ + ‖q.2 - x‖ := norm_sub_le _ _
      _ < 2 * ε := by linarith
  have h4τd : 4 * τ ≤ d := hsep q.1 hq1 q.2 hq2 hq12
  -- Step 2: the scale `ρ = d / (4δ²)`, with `σ ≤ ρ < δ²/2 < 1` and `0 < d/4 ≤ 1`.
  set ρ : ℝ := d / (4 * δ ^ 2) with hρ_def
  have hρ0 : 0 < ρ := by positivity
  have hdρ : d = 4 * δ ^ 2 * ρ := by
    rw [hρ_def]; field_simp
  have hσρ : σ ≤ ρ := by
    have h1 : δ ^ 2 * (2 * σ) ≤ δ ^ 2 * ρ := by linarith
    have h2 : 2 * σ ≤ ρ := le_of_mul_le_mul_left h1 hδ2pos
    linarith
  have hρδ : ρ < δ ^ 2 / 2 := by
    have : 4 * δ ^ 2 * ρ < 4 * δ ^ 2 * (δ ^ 2 / 2) := by
      calc 4 * δ ^ 2 * ρ = d := hdρ.symm
        _ < 2 * ε := hd2ε
        _ ≤ 2 * δ ^ 4 := by linarith
        _ = 4 * δ ^ 2 * (δ ^ 2 / 2) := by ring
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hρ1 : ρ < 1 := by linarith
  have hd4pos : 0 < d / 4 := by positivity
  have hd4le : d / 4 ≤ 1 := by linarith
  -- Step 3: (C_y) at `(d/4, σ, ρ)`, after enlarging `τ` to `d/4`; its error is at most `K δ²`.
  have hstep3 : ∀ y ∈ s,
      μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
          ENNReal.ofReal σ ^ n ≤
        μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * δ ^ 2) := by
    intro y hys
    have hC := (hy y hys).2.2 (d / 4) σ ρ hd4pos hd4le hσ hσρ hρ1
    have h2 : 2 * (d / 4) = d / 2 := by ring
    rw [h2] at hC
    have hsub : closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ} ⊆
        closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4} := by
      refine inter_subset_inter_right _ fun z hz ↦ ?_
      have hz' : ‖(z - y) - Grassmannian.project P (z - y)‖ < τ := hz
      show ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4
      linarith
    have herr : K * ε * ρ / (d / 4) ≤ K * δ ^ 2 := by
      rw [div_le_iff₀ hd4pos]
      have hKε : K * ε ≤ K * δ ^ 4 := mul_le_mul_of_nonneg_left hεδ hK
      have : K * δ ^ 2 * (d / 4) = K * δ ^ 4 * ρ := by rw [hdρ]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hKε hρ0.le
    calc _ ≤ μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4}) /
          ENNReal.ofReal σ ^ n := ENNReal.div_le_div_right (measure_mono hsub) _
      _ ≤ _ := hC
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal herr)
  -- Step 4: summation over `s`, with `#s · K δ² ≤ (m + 1) K δ²`.
  have hstep4 : ∑ y ∈ s,
      μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
          ENNReal.ofReal σ ^ n ≤
        ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (((m : ℝ) + 1) * K * δ ^ 2) := by
    calc _ ≤ ∑ y ∈ s, (μ (closedBall y ρ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * δ ^ 2)) := Finset.sum_le_sum hstep3
      _ = _ + s.card • ENNReal.ofReal (K * δ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const]
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hsm
          have hKδ : 0 ≤ K * δ ^ 2 := by positivity
          calc (s.card : ℝ) * (K * δ ^ 2) ≤ ((m : ℝ) + 1) * (K * δ ^ 2) :=
                mul_le_mul_of_nonneg_right hcard hKδ
            _ = ((m : ℝ) + 1) * K * δ ^ 2 := by ring
  -- Step 5: clusters from (CS) at scale `d`, with `S ≤ (10 (m + 1))^{m + 1} d = a δ² ρ`.
  obtain ⟨Z, S, hZs, hZcard, hS0, hSd, hcov, hZsep⟩ :=
    hCS s d hs2 hd0 hdmin ⟨q.1, hq1, q.2, hq2, hq12, le_refl _⟩
  have hcardpow : (10 * (s.card : ℝ)) ^ s.card ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) := by
    have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hsm
    calc (10 * (s.card : ℝ)) ^ s.card ≤ (10 * ((m : ℝ) + 1)) ^ s.card :=
          pow_le_pow_left₀ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hm1 hsm
  have hSu : S ≤ a * δ ^ 2 * ρ := by
    calc S ≤ (10 * (s.card : ℝ)) ^ s.card * d := hSd
      _ ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) * d := mul_le_mul_of_nonneg_right hcardpow hd0.le
      _ = a * δ ^ 2 * ρ := by rw [hdρ, ha_def]; ring
  -- Step 6: grouping (the accepted sibling `cylinder_grouping`) with `u = a δ²`.
  have hpx : ∀ y ∈ s, Grassmannian.project P y = x := fun y hys ↦ (hy y hys).1
  have hgroup := Submission.intcpt_allard_ccb_cylinder_grouping N n μ P x s Z d ρ S (a * δ ^ 2)
    hpx hZs hd0 hdmin hρ0 hS0 hSu hu1 hcov
  -- Step 7: the witnesses `Z`, `σ' = ρ + S ≤ 2ρ < δ²` and `τ' = d/2 + S`.
  refine ⟨Z, ρ + S, d / 2 + S, hZs, by omega, by linarith, ?_, ?_, ?_, ?_⟩
  · have hSρ : a * δ ^ 2 * ρ ≤ ρ := mul_le_of_le_one_left hρ0.le hu1
    linarith
  · have h1 : 2 * δ ^ 2 * S ≤ S := mul_le_of_le_one_left hS0 h2δ2
    have h2 : 2 * δ ^ 2 * (ρ + S) = d / 2 + 2 * δ ^ 2 * S := by rw [hdρ]; ring
    rw [h2]
    linarith
  · intro z hz z' hz' hzz'
    have := hZsep z hz z' hz' hzz'
    linarith
  -- Step 8: chain steps 4 and 6.
  have hcoef : (1 + (2 ^ n - 1) * (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) * δ ^ 2) =
      1 + (2 ^ n - 1) * (a * δ ^ 2) := by rw [ha_def]; ring
  rw [hcoef]
  calc _ ≤ _ := hstep4
    _ ≤ _ := add_le_add hgroup le_rfl

/-- Composing two affine bounds in `[0,∞]` (Simon Ch. 8, proof of 5.10 (8), recombination of the
induction constants): if `X ≤ (1 + b δ²) Y + k δ²` and `Y ≤ (1 + c δ²) M + c δ²` with `b, c, k ≥ 0`,
`δ² ≤ 1`, `b + c + b c ≤ c'` and `(1 + b) c + k ≤ c'`, then `X ≤ (1 + c' δ²) M + c' δ²`
(`M = ∞` allowed). -/
theorem Submission.intcpt_allard_ccb_affine_combine :
    ∀ (b c c' k δ : ℝ) (X Y M : ℝ≥0∞), 0 ≤ b → 0 ≤ c → 0 ≤ k → δ ^ 2 ≤ 1 → b + c + b * c ≤ c' → (1 + b) * c + k ≤ c' → X ≤ ENNReal.ofReal (1 + b * δ ^ 2) * Y + ENNReal.ofReal (k * δ ^ 2) → Y ≤ ENNReal.ofReal (1 + c * δ ^ 2) * M + ENNReal.ofReal (c * δ ^ 2) → X ≤ ENNReal.ofReal (1 + c' * δ ^ 2) * M + ENNReal.ofReal (c' * δ ^ 2) := by
  intro b c c' k δ X Y M hb hc hk hδ hbc hbck hX hY
  -- Step 1: `0 ≤ δ² ≤ 1`, so `b c δ⁴ ≤ b c δ²`.
  have hδ0 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ4 : b * c * (δ ^ 2 * δ ^ 2) ≤ b * c * δ ^ 2 :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hδ0 hδ) (mul_nonneg hb hc)
  have hp : 0 ≤ 1 + b * δ ^ 2 := by positivity
  -- Step 2: `(1 + b δ²)(1 + c δ²) ≤ 1 + (b + c + b c) δ² ≤ 1 + c' δ²`.
  have h1 : (1 + b * δ ^ 2) * (1 + c * δ ^ 2) ≤ 1 + c' * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hbc hδ0]
  -- Step 3: `(1 + b δ²) c δ² + k δ² ≤ ((1 + b) c + k) δ² ≤ c' δ²`.
  have h2 : (1 + b * δ ^ 2) * (c * δ ^ 2) + k * δ ^ 2 ≤ c' * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hbck hδ0]
  -- Steps 4–5: substitute the bound on `Y`, distribute in `[0,∞]`, and compare coefficients.
  calc X ≤ ENNReal.ofReal (1 + b * δ ^ 2) * Y + ENNReal.ofReal (k * δ ^ 2) := hX
    _ ≤ ENNReal.ofReal (1 + b * δ ^ 2) *
          (ENNReal.ofReal (1 + c * δ ^ 2) * M + ENNReal.ofReal (c * δ ^ 2)) +
          ENNReal.ofReal (k * δ ^ 2) := by gcongr
    _ = ENNReal.ofReal ((1 + b * δ ^ 2) * (1 + c * δ ^ 2)) * M +
          ENNReal.ofReal ((1 + b * δ ^ 2) * (c * δ ^ 2) + k * δ ^ 2) := by
      rw [ENNReal.ofReal_add (mul_nonneg hp (mul_nonneg hc hδ0)) (mul_nonneg hk hδ0),
        ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hp]
      ring
    _ ≤ ENNReal.ofReal (1 + c' * δ ^ 2) * M + ENNReal.ofReal (c' * δ ^ 2) := by gcongr

/-- Cluster selection (Simon Ch. 8, proof of 5.10 (8)): if two distinct points of a finite set `s`
with `#s ≥ 2` are at distance `≤ d`, there are centres `Z ⊆ s` with `#Z < #s` and a radius
`0 ≤ S ≤ (10 #s)^{#s} d` such that every `y ∈ s` is within `S` of `Z` and distinct centres are at
least `2d + 4S` apart.  Greedy merging: take an admissible pair (`Z ⊆ s` nonempty, `#Z < #s`,
`S`-covering, `S ≤ d (5^{#s - #Z} - 1) / 2`) with `#Z` minimal; two centres closer than `2d + 4S`
would give the admissible pair `(Z ∖ {z'}, 2d + 5S)`. -/
theorem Submission.intcpt_allard_cluster_selection :
    ∀ (N : ℕ) (s : Finset (Euclidean N)) (d : ℝ), 2 ≤ s.card → 0 < d → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖) → (∃ y ∈ s, ∃ y' ∈ s, y ≠ y' ∧ ‖y - y'‖ ≤ d) → ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ s ∧ Z.card < s.card ∧ 0 ≤ S ∧ S ≤ (10 * (s.card : ℝ)) ^ s.card * d ∧ (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖ := by
  intro N s d hk hd _ hclose
  classical
  -- Step 1: admissible pairs `(Z, S)` with `#Z = m`.
  let Adm : ℕ → Prop := fun m ↦ ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ s ∧ Z.Nonempty ∧
    Z.card = m ∧ m < s.card ∧ 0 ≤ S ∧ (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧
    S ≤ d * ((5 : ℝ) ^ (s.card - m) - 1) / 2
  -- Step 2: `(s ∖ {y₁}, d)` is admissible.
  obtain ⟨y₀, hy₀, y₁, hy₁, hne, hdist⟩ := hclose
  have hstart : Adm (s.card - 1) := by
    refine ⟨s.erase y₁, d, Finset.erase_subset _ _, ⟨y₀, Finset.mem_erase.2 ⟨hne, hy₀⟩⟩,
      Finset.card_erase_of_mem hy₁, by omega, hd.le, fun y hy ↦ ?_, ?_⟩
    · by_cases hyy : y = y₁
      · rw [hyy]
        exact ⟨y₀, Finset.mem_erase.2 ⟨hne, hy₀⟩, by rw [norm_sub_rev]; exact hdist⟩
      · exact ⟨y, Finset.mem_erase.2 ⟨hyy, hy⟩, by simpa using hd.le⟩
    · rw [show s.card - (s.card - 1) = 1 by omega]
      linarith
  have hex : ∃ m, Adm m := ⟨_, hstart⟩
  -- Step 3: an admissible pair with `#Z` minimal.
  obtain ⟨Z, S, hZs, ⟨z₀, hz₀⟩, hZcard, hmk, hS0, hcov, hSb⟩ := Nat.find_spec hex
  have hm1 : 1 ≤ Nat.find hex := hZcard ▸ Finset.card_pos.2 ⟨z₀, hz₀⟩
  -- Step 4: separation, since otherwise `(Z ∖ {z'}, 2d + 5S)` is admissible with `#Z - 1` points.
  have hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖ := by
    intro z hz z' hz' hzz'
    refine le_of_not_gt fun hlt ↦ ?_
    have hadm : Adm (Nat.find hex - 1) := by
      refine ⟨Z.erase z', 2 * d + 5 * S, (Finset.erase_subset _ _).trans hZs,
        ⟨z, Finset.mem_erase.2 ⟨hzz', hz⟩⟩, by rw [Finset.card_erase_of_mem hz', hZcard],
        by omega, by linarith, fun y hy ↦ ?_, ?_⟩
      · obtain ⟨z'', hz'', hyz''⟩ := hcov y hy
        by_cases h : z'' = z'
        · rw [h] at hyz''
          refine ⟨z, Finset.mem_erase.2 ⟨hzz', hz⟩, ?_⟩
          calc ‖y - z‖ = ‖(y - z') + (z' - z)‖ := by rw [sub_add_sub_cancel]
            _ ≤ ‖y - z'‖ + ‖z' - z‖ := norm_add_le _ _
            _ ≤ 2 * d + 5 * S := by rw [norm_sub_rev z' z]; linarith
        · exact ⟨z'', Finset.mem_erase.2 ⟨h, hz''⟩, by linarith⟩
      · rw [show s.card - (Nat.find hex - 1) = (s.card - Nat.find hex) + 1 by omega, pow_succ]
        linarith
    have := Nat.find_min' hex hadm
    omega
  -- Step 5: conclusion, with `S ≤ d (5^{#s - #Z} - 1) / 2 ≤ 5^{#s} d ≤ (10 #s)^{#s} d`.
  refine ⟨Z, S, hZs, hZcard ▸ hmk, hS0, ?_, hcov, hsep⟩
  have h5 : (5 : ℝ) ^ (s.card - Nat.find hex) ≤ 5 ^ s.card :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h10 : (5 : ℝ) ^ s.card ≤ (10 * (s.card : ℝ)) ^ s.card := by
    refine pow_le_pow_left₀ (by norm_num) ?_ _
    have : (2 : ℝ) ≤ s.card := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) ≤ 5 ^ s.card := by positivity
  nlinarith

/-- **Simon Ch. 8, proof of 5.10, printed (8), pp. 222–223** (child `cylinder_cluster_bound` of
`allard_lemma`): at points `y` of one fibre `p_P(y) = x` with `|y - p_P(y)| < ε`, the monotonicity
(M_y) and the cylinder comparison (C_y) give
`Σ_{y ∈ s} μ(U^τ_σ(y)) / σ^n ≤ (1 + c δ²) μ(B_1(x)) + c δ²` whenever `#s ≤ m`, `σ ≤ δ²`,
`2δ²σ ≤ τ` and `4τ ≤ |y - y'|` for distinct points.  The proof is the book's induction on the
number of points, with the constants defined by recursion on `m`: `c_0 = 0`, `δ_0 = 1/2` and, for
`a = 4(10(m+1))^{m+1}`, `b = (2^n - 1)a`,
`c_{m+1} = max{2^{n+2}, b + c_m + b c_m, (1 + b)c_m + (m+1)K}`, `δ_{m+1} = min{δ_m, 1/a}`.
At most one point is the monotonicity bound (`intcpt_allard_ccb_one_point_ball_bound`, as
`U^τ_σ(y) ⊆ B_σ(y)`).  For at least two points, `intcpt_allard_ccb_reduction_step` (the
grouping estimate `intcpt_allard_ccb_cylinder_grouping` applied to the clusters of
`intcpt_allard_cluster_selection`) passes to `Z ⊆ s` with `#Z ≤ m` and admissible scales
`(σ', τ')` at the cost `Σ_s ≤ (1 + bδ²) Σ_Z + (m+1)Kδ²`; the induction hypothesis bounds `Σ_Z`,
and `intcpt_allard_ccb_affine_combine` composes the two affine bounds in `[0, ∞]`. -/
theorem Submission.intcpt_allard_cylinder_cluster_bound :
    ∀ (N n : ℕ) (K : ℝ) (m : ℕ), 0 ≤ K → ∃ c δm : ℝ, 0 ≤ c ∧ 0 < δm ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δm → 0 < ε → ε ≤ δ ^ 4 → ∀ (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)), s.card ≤ m → (∀ y ∈ s, Grassmannian.project P y = x ∧ ‖y - Grassmannian.project P y‖ < ε ∧ MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * μ (closedBall y r) / ENNReal.ofReal r ^ n) (Ioo 0 1) ∧ ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) + ENNReal.ofReal (c * δ ^ 2) := by
  intro N n K m hK
  induction m with
  | zero =>
    -- `#s ≤ 0` forces `s = ∅`, so the sum vanishes.
    refine ⟨0, 1 / 2, le_rfl, by norm_num, ?_⟩
    intro δ ε _ _ _ _ μ P x s hs _ σ τ _ _ _ _
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)]
    simp
  | succ m ih =>
    obtain ⟨c, δm, hc, hδm, H⟩ := ih
    -- The constants: `a = 4(10(m+1))^{m+1} ≥ 40`, `b = (2^n - 1)a ≥ 0`,
    -- `c' = max{2^{n+2}, b + c + bc, (1 + b)c + (m+1)K}` and `δ' = min{δm, 1/a}`.
    obtain ⟨a, ha⟩ : ∃ a : ℝ, 4 * (10 * ((m : ℝ) + 1)) ^ (m + 1) = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, (2 ^ n - 1) * a = b := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c' : ℝ,
        max (2 ^ (n + 2)) (max (b + c + b * c) ((1 + b) * c + ((m : ℝ) + 1) * K)) = c' :=
      ⟨_, rfl⟩
    have ha40 : 40 ≤ a := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h10 : (10 : ℝ) ≤ 10 * ((m : ℝ) + 1) := by linarith
      have hpow : 10 * ((m : ℝ) + 1) ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) :=
        le_self_pow₀ (by linarith) (Nat.succ_ne_zero m)
      rw [← ha]
      linarith
    have hb0 : 0 ≤ b := by
      rw [← hb]
      exact mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (by linarith)
    have hk0 : 0 ≤ ((m : ℝ) + 1) * K := mul_nonneg (by positivity) hK
    have h2n : (2 : ℝ) ^ (n + 2) ≤ c' := by
      rw [← hc']
      exact le_max_left _ _
    have hc'1 : b + c + b * c ≤ c' := by
      rw [← hc']
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hc'2 : (1 + b) * c + ((m : ℝ) + 1) * K ≤ c' := by
      rw [← hc']
      exact (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨c', min δm (1 / a), (by positivity : (0 : ℝ) ≤ 2 ^ (n + 2)).trans h2n,
      lt_min hδm (one_div_pos.mpr (by linarith)), ?_⟩
    intro δ ε hδ hδle hε hεle μ P x s hs hpt σ τ hσ hσle hτ hsep
    have hδa : δ ≤ 1 / a := hδle.trans (min_le_right _ _)
    have hδhalf : δ ≤ 1 / 2 := hδa.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
    have hδ2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le (by linarith)
    rcases Nat.lt_or_ge s.card 2 with hs2 | hs2
    · -- At most one point: `U^τ_σ(y) ⊆ B_σ(y)` and the one-point monotonicity bound.
      rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · simp
      have hsy : s = {y} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hy, fun y' hy' ↦ Finset.card_le_one.mp (by omega) y' hy' y hy⟩
      obtain ⟨hpy, hyε, hmono, -⟩ := hpt y hy
      rw [hsy, Finset.sum_singleton]
      calc μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
            ENNReal.ofReal σ ^ n
          ≤ μ (closedBall y σ) / ENNReal.ofReal σ ^ n :=
            ENNReal.div_le_div_right (measure_mono inter_subset_left) _
        _ ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1) :=
            Submission.intcpt_allard_ccb_one_point_ball_bound N n μ x y δ ε σ hδ hδhalf hε hεle
              (by rw [← hpy]; exact hyε) hmono hσ hσle
        _ ≤ ENNReal.ofReal (1 + c' * δ ^ 2) * μ (closedBall x 1) := by gcongr
        _ ≤ _ := le_self_add
    · -- At least two points: one reduction step to `Z ⊆ s` with `#Z ≤ m`, the induction
      -- hypothesis on `Z` at the scales `(σ', τ')`, and the composition of the two bounds.
      obtain ⟨Z, σ', τ', hZs, hZm, hσ'0, hσ'le, hτ', hsepZ, hred⟩ :=
        Submission.intcpt_allard_ccb_reduction_step N n K m
          (Submission.intcpt_allard_cluster_selection N) hK δ ε hδ (by rw [ha]; exact hδa) hε
          hεle μ P x s hs2 hs (fun y hy ↦ ⟨(hpt y hy).1, (hpt y hy).2.1, (hpt y hy).2.2.2⟩)
          σ τ hσ hσle hτ hsep
      rw [ha, hb] at hred
      exact Submission.intcpt_allard_ccb_affine_combine b c c' (((m : ℝ) + 1) * K) δ _ _ _ hb0 hc
        hk0 hδ2 hc'1 hc'2 hred (H δ ε hδ (hδle.trans (min_le_left _ _)) hε hεle μ P x Z hZm
          (fun y hy ↦ hpt y (hZs hy)) σ' τ' hσ'0 hσ'le hτ' hsepZ)

/-- **Simon Ch. 8, proof of 5.10, printed (6) and (8) (p. 222), and Remark 5.11(∗) (p. 220)**
(child `fibre_density_sum_bound` of `allard_lemma`): uniformly over fibres with at most `M`
points, if each `y ∈ s` lies over `x`, in `B_2(0)`, within `ε` of `P` and satisfies printed (1)
and (2), then `Σ_{y ∈ s} Θ^n(μ_W, y) ≤ (1 + δ) ω_n^{-1} μ_W(B_1(x)) + δ`.  Erratum (E2): the book
states (6)–(7) for `y ∈ B^n_1(0) ∖ p(A_1 ∪ A_2)`, but they are used, and proved, for points
satisfying (1) and (2); the rescaling by `3/2` is replaced by working with `B_1(x)` directly. -/
theorem Submission.intcpt_allard_fibre_density_sum_bound :
    MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ Λ → ∀ M : ℕ, ∃ δ' : ℝ, 0 < δ' ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δ' → 0 < ε → ε ≤ δ ^ 4 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → ∀ (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞), s.card ≤ M → (∀ y ∈ s, Grassmannian.project P y = x ∧ y ∈ closedBall (0 : Euclidean N) 2 ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) ∧ ‖y - Grassmannian.project P y‖ < ε ∧ HasDensity n W.weight y (Θ y)) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
  intro hMF N n Λ hΛ M
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  -- Step 0: `C` from `cylinder_monotonicity`, `K_C = C(1 + eΛ)`, `(c, δ_M)` from
  -- `cylinder_cluster_bound` with `m = M`, `A = 2 + 2c + 2c/ω_n + 2M K_C/ω_n` and
  -- `δ' = min{δ_M, 1/2, 2^{-(n+2)}, 1/A}`.
  obtain ⟨C, hC0, hcyl⟩ := Submission.intcpt_allard_cylinder_monotonicity N n
  set KC : ℝ := C * (1 + Real.exp 1 * Λ)
  have hKC0 : 0 ≤ KC :=
    mul_nonneg hC0 (add_nonneg zero_le_one (mul_nonneg (Real.exp_pos 1).le hΛ0))
  obtain ⟨c, δM, hc0, hδM0, hclu⟩ := Submission.intcpt_allard_cylinder_cluster_bound N n KC M hKC0
  set A : ℝ := 2 + 2 * c + 2 * c / (unitBallVolume n).toReal +
    2 * (M : ℝ) * KC / (unitBallVolume n).toReal
  have hA0 : 0 < A := by
    have h1 : 0 ≤ 2 * c / (unitBallVolume n).toReal :=
      div_nonneg (mul_nonneg zero_le_two hc0) ENNReal.toReal_nonneg
    have h2 : 0 ≤ 2 * (M : ℝ) * KC / (unitBallVolume n).toReal :=
      div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg M)) hKC0)
        ENNReal.toReal_nonneg
    linarith
  refine ⟨min (min δM (1 / 2)) (min (1 / 2 ^ (n + 2)) (1 / A)),
    lt_min (lt_min hδM0 (by norm_num)) (lt_min (by positivity) (one_div_pos.2 hA0)), ?_⟩
  intro δ ε hδ0 hδ' hε0 hεδ U W P hU hW hWΛ x s Θ hcard hs
  have hδM : δ ≤ δM := hδ'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ 1 / 2 := hδ'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδn : 2 ^ (n + 2) * δ ≤ 1 :=
    (le_div_iff₀' (by positivity)).1 (hδ'.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδA : A * δ ≤ 1 :=
    (le_div_iff₀' hA0).1 (hδ'.trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- `ε ≤ δ⁴ ≤ 1/16`, so `ε ≤ 1` and `e^ε ≤ 1 + 2ε ≤ 2`.
  have hε16 : ε ≤ 1 / 16 := hεδ.trans ((pow_le_pow_left₀ hδ0.le hδ2 4).trans (by norm_num))
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  have hexp : Real.exp ε ≤ 2 := by
    have h := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε0]; exact hε1)
    rw [abs_of_pos hε0] at h
    linarith [le_abs_self (Real.exp ε - 1)]
  -- Step 1: the facts at each `y ∈ s`: `|y - x| < ε`, the monotonicity (M_y), the density bound
  -- for `Θ(y)` and the cylinder monotonicity (C_y) with constant `K_C`.
  have hpt : ∀ y ∈ s, ‖y - x‖ < ε ∧
      MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * W.weight (closedBall y r) /
        ENNReal.ofReal r ^ n) (Ioo 0 1) ∧
      (∀ σ : ℝ, 0 < σ → σ < 1 →
        Θ y ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n W.weight y σ) ∧
      ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 →
        W.weight (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
            ENNReal.ofReal σ ^ n ≤
          W.weight (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) /
            ENNReal.ofReal ρ ^ n + ENNReal.ofReal (KC * ε * ρ / τ) := by
    intro y hy
    obtain ⟨hpy, hy2, hvar, htilt, hyP, hΘ⟩ := hs y hy
    -- `B°_1(y) ⊆ B°_3(0) ⊆ U`, since `|y| ≤ 2`.
    have hsub : ball y 1 ⊆ ball (0 : Euclidean N) 3 :=
      ball_subset_ball' (by rw [mem_closedBall] at hy2; linarith)
    obtain ⟨hmono, ⟨θ, hθ, -, hθle⟩, hgrow⟩ :=
      Submission.intcpt_allard_good_point_monotonicity hMF N n U W y ε Λ hW (hsub.trans hU)
        hε0.le ((measure_mono hsub).trans hWΛ) hvar
    -- `Θ(y) = θ_y`, by uniqueness of limits along `𝓝[>] 0`.
    have hΘθ : Θ y = θ := tendsto_nhds_unique hΘ hθ
    refine ⟨by rw [← hpy]; exact hyP, hmono, by rw [hΘθ]; exact hθle, ?_⟩
    -- `μ_W(B_r(y)) ≤ e^ε Λ r^n ≤ eΛ r^n`, so `cylinder_monotonicity` applies with `K = eΛ`.
    exact hcyl U W P y ε (Real.exp 1 * Λ) hW (hsub.trans hU) hε0
      (mul_nonneg (Real.exp_pos 1).le hΛ0) hvar htilt fun r hr0 hr1 ↦ (hgrow r hr0 hr1).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hε1) hΛ0) (pow_nonneg hr0.le n)))
  -- Steps 3–5: the cases `#s = 0`, `#s = 1` and `#s ≥ 2`.
  obtain hs0 | hs1 | hs2 : s.card = 0 ∨ s.card = 1 ∨ 2 ≤ s.card := by omega
  · rw [Finset.card_eq_zero.1 hs0, Finset.sum_empty]
    exact zero_le
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 hs1
    obtain ⟨hyx, -, hD, -⟩ := hpt y (Finset.mem_singleton_self y)
    rw [Finset.sum_singleton]
    exact (Submission.intcpt_allard_fdsb_one_point_bound N n W.weight x y (Θ y) δ ε hδ0 hδ2 hδn
      hε0 hεδ hyx hD).trans le_self_add
  · -- The per-point bound is `density_cylinder_bound` (printed (6)); the cluster bound (8) is
    -- `cylinder_cluster_bound` at `(δ, ε, μ_W, P, x, s)`.
    exact Submission.intcpt_allard_fdsb_separated_sum_bound N n W.weight P x s Θ KC c δ ε M hKC0
      hc0 hδ0 hδ2 hε0 hεδ hδA hs2 hcard
      (fun y hy ↦ ⟨(hpt y hy).1, Submission.intcpt_allard_fdsb_density_cylinder_bound N n W.weight
        P y (Θ y) ε KC hε0.le hexp hKC0 (hpt y hy).2.2.1 (hpt y hy).2.2.2⟩)
      (hclu δ ε hδ0 hδM hε0 hεδ W.weight P x s hcard fun y hy ↦
        ⟨(hs y hy).1, (hs y hy).2.2.2.2.1, (hpt y hy).2.1, (hpt y hy).2.2.2⟩)

/-- **Simon Ch. 8, Lemma 5.10 and Remark 5.11, pp. 219–223** (child `allard_lemma` of
`integral_compactness`): for `0 < δ ≤ δ̄` and `0 < ε ≤ δ⁴`, if `μ_W(B°_3(0)) ≤ Λ`,
`‖δW‖(B°_3(0)) < ε²` and `∫_{B°_3(0) × G} ‖p_S - p_P‖ dW < ε²`, then (a) the points of
`B_2(0) ∩ spt μ_W` where printed (1) or (2) fails have `μ_W`-measure at most `c₀ ε`
(`intcpt_allard_bad_set_bound`), and (b) on a fibre `p_P(y) = x`, `|x| < 1`, the points satisfying
(1) and (2) with `|y - p_P(y)| < ε` and `Θ^n(μ_W, y) ≥ 1` have
`Σ_y Θ^n(μ_W, y) ≤ (1 + δ) ω_n^{-1} μ_W(B_1(x)) + δ`.  For (b), Remark 5.11: with
`m₀ = ⌈(3/2) Λ / ω_n⌉ + 1` and `δ̄ = min{δ'_{m₀}, 1/2}` (`intcpt_allard_fibre_density_sum_bound`
with `M = m₀`), `m₀` such points would give `m₀ ≤ Σ Θ ≤ (3/2) Λ / ω_n + 1/2 < m₀`, as
`B_1(x) ⊆ B°_3(0)`; so a fibre has at most `m₀` of them and the fibre bound applies.  Integrality
of `W` is not used. -/
theorem Submission.intcpt_allard_integrality_lemma :
    MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ n → 1 ≤ Λ → ∃ δbar c₀ : ℝ, 0 < δbar ∧ 0 ≤ c₀ ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δbar → 0 < ε → ε ≤ δ ^ 4 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → variationMeasure W (ball (0 : Euclidean N) 3) < ENNReal.ofReal (ε ^ 2) → (∫⁻ z in ball (0 : Euclidean N) 3 ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) < ENNReal.ofReal (ε ^ 2) → W.weight {y | y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ ¬ ((∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)))} ≤ ENNReal.ofReal (c₀ * ε) ∧ ∀ (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞), x ∈ P.plane → ‖x‖ < 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) ∧ ‖y - Grassmannian.project P y‖ < ε ∧ HasDensity n W.weight y (Θ y) ∧ 1 ≤ Θ y) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
  intro hMF N n Λ _ hΛ
  -- Step 0: `c₀` from `bad_set_bound`; `ω := ω_n ∈ (0, ∞)`; `m₀ = ⌈(3/2) Λ / ω⌉ + 1`; `δ'` from
  -- `fibre_density_sum_bound` with `M = m₀`; and `δ̄ = min{δ', 1/2}`.
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  obtain ⟨c₀, hc₀, hbad⟩ := Submission.intcpt_allard_bad_set_bound hMF N n Λ hΛ
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨ω, hω_def⟩ : ∃ ω, (unitBallVolume n).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos hω0 hωtop
  have hωW : ENNReal.ofReal ω = unitBallVolume n := hω_def ▸ ENNReal.ofReal_toReal hωtop
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ⌈3 / 2 * Λ / ω⌉₊ + 1 = m₀ := ⟨_, rfl⟩
  obtain ⟨δ', hδ'0, hfib⟩ := Submission.intcpt_allard_fibre_density_sum_bound hMF N n Λ hΛ m₀
  refine ⟨min δ' (1 / 2), c₀, lt_min hδ'0 (by norm_num), hc₀, ?_⟩
  intro δ ε hδ0 hδle hε0 hεδ U W P hU hW hWΛ hvar htilt
  have hδ' : δ ≤ δ' := hδle.trans (min_le_left _ _)
  have hδ2 : δ ≤ 1 / 2 := hδle.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := hεδ.trans (pow_le_one₀ hδ0.le (by linarith))
  -- Step 1: (a) is `bad_set_bound` (`ε ≤ δ⁴ ≤ 1`).
  refine ⟨hbad ε hε0 hε1 U W P hU hW hWΛ hvar htilt, ?_⟩
  intro x s Θ _ hx hs
  -- Step 2: `fibre_density_sum_bound` applies to every `t ⊆ s` with at most `m₀` points.
  have hsub : ∀ t ⊆ s, t.card ≤ m₀ → ∑ y ∈ t, Θ y ≤
      ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
    intro t hts htm
    refine hfib δ ε hδ0 hδ' hε0 hεδ U W P hU hW hWΛ x t Θ htm fun y hy ↦ ?_
    obtain ⟨h1, h2, -, h4, h5, h6, h7, -⟩ := hs y (hts hy)
    exact ⟨h1, h2, h4, h5, h6, h7⟩
  -- Step 3 (Remark 5.11): `B_1(x) ⊆ B°_3(0)`, so the right side is at most
  -- `(3/2) Λ / ω_n + 1/2 < m₀`.
  have hB : ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n +
      ENNReal.ofReal δ < m₀ := by
    have hμ : W.weight (closedBall x 1) ≤ ENNReal.ofReal Λ :=
      (measure_mono (closedBall_subset_ball' (by rw [dist_zero_right]; linarith))).trans hWΛ
    have hceil : 3 / 2 * Λ / ω ≤ ⌈3 / 2 * Λ / ω⌉₊ := Nat.le_ceil _
    calc ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ
        ≤ ENNReal.ofReal (3 / 2) * ENNReal.ofReal Λ / ENNReal.ofReal ω +
            ENNReal.ofReal (1 / 2) := by
          rw [hωW]
          gcongr
          all_goals first | exact hμ | linarith
      _ = ENNReal.ofReal (3 / 2 * Λ / ω + 1 / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos hω,
            ENNReal.ofReal_add (div_nonneg (mul_nonneg (by norm_num) hΛ0) hω.le) (by norm_num)]
      _ < ENNReal.ofReal m₀ := by
          have hm₀pos : (0 : ℝ) < m₀ := by rw [← hm₀]; positivity
          rw [ENNReal.ofReal_lt_ofReal_iff hm₀pos, ← hm₀]
          push_cast
          linarith
      _ = m₀ := ENNReal.ofReal_natCast m₀
  -- Step 4: at most `m₀` points, since `m₀` of them would give `m₀ ≤ Σ Θ < m₀`.
  by_cases hcard : s.card ≤ m₀
  · exact hsub s subset_rfl hcard
  · exfalso
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (show m₀ ≤ s.card by omega)
    have hlow : (m₀ : ℝ≥0∞) ≤ ∑ y ∈ t, Θ y := by
      calc (m₀ : ℝ≥0∞) = ∑ _y ∈ t, (1 : ℝ≥0∞) := by simp [htcard]
        _ ≤ ∑ y ∈ t, Θ y := Finset.sum_le_sum fun y hy ↦ (hs y (hts hy)).2.2.2.2.2.2.2
    exact absurd (hlow.trans (hsub t hts htcard.le)) (not_le.2 hB)
/-- Hausdorff measure of an `L`-Lipschitz graph piece over an `n`-plane (a step in the proof of
Simon Ch. 8, 5.9): if `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ A` and `L ≥ 0`, then
`p_P` is injective on `A` with a `(1 + L²)^{1/2}`-Lipschitz inverse on `p_P(A)`, so
`H^n(A) ≤ (1 + L²)^{n/2} H^n(p_P(A))`.  `A` need not be closed or measurable. -/
theorem Submission.intcpt_graph_hausdorff_le_projection :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (A : Set (Euclidean N)), 0 ≤ L → (∀ y ∈ A, ∀ z ∈ A, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → (μHE[n] : Measure (Euclidean N)) A ≤ ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) * (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' A) := by
  intro N n P L A hL hgraph
  -- Step 1: `p_P` is linear, symmetric and idempotent, so `|v|² = |p_P v|² + |v - p_P v|²`.
  have hsub : ∀ u v : Euclidean N,
      Grassmannian.project P (u - v) = Grassmannian.project P u - Grassmannian.project P v :=
    fun u v ↦ map_sub P.projectionLinearMap u v
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
  -- Step 2: on `A`, `|y - z|² ≤ (1 + L²) |p_P(y - z)|²`, i.e.
  -- `|y - z| ≤ (1 + L²)^{1/2} |p_P y - p_P z|`.
  have hkey : ∀ y ∈ A, ∀ z ∈ A, ‖y - z‖ ≤
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
  -- Step 3: `p_P` is injective on `A`, and `h = invFunOn p_P A` has `h (p_P y) = y` for `y ∈ A`.
  have hinj : InjOn (Grassmannian.project P) A := by
    intro y hy z hz hyz
    have h := hkey y hy z hz
    rw [hyz, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hleft : ∀ y ∈ A,
      Function.invFunOn (Grassmannian.project P) A (Grassmannian.project P y) = y :=
    fun y hy ↦ hinj.leftInvOn_invFunOn hy
  -- Step 4: `h` is `(1 + L²)^{1/2}`-Lipschitz on `p_P(A)`.
  have hinv : LipschitzOnWith (Real.toNNReal (Real.sqrt (1 + L ^ 2)))
      (Function.invFunOn (Grassmannian.project P) A) (Grassmannian.project P '' A) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [hleft y hy, hleft z hz, dist_eq_norm, dist_eq_norm]
    exact hkey y hy z hz
  -- Step 5: `A = h(p_P(A))` and the Lipschitz image bound for `μH[n]`, with
  -- `((1 + L²)^{1/2})^n = (1 + L²)^{n/2}` in `[0, ∞]`.
  have hpow : (Real.toNNReal (Real.sqrt (1 + L ^ 2)) : ℝ≥0∞) ^ (n : ℝ) =
      ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) := by
    change ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ (n : ℝ) = _
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n),
      Real.rpow_div_two_eq_sqrt _ (by positivity)]
  have hH : (μH[(n : ℝ)] : Measure (Euclidean N)) A ≤
      ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) *
        (μH[(n : ℝ)] : Measure (Euclidean N)) (Grassmannian.project P '' A) := by
    calc (μH[(n : ℝ)] : Measure (Euclidean N)) A
        = (μH[(n : ℝ)] : Measure (Euclidean N))
            (Function.invFunOn (Grassmannian.project P) A '' (Grassmannian.project P '' A)) := by
          rw [hinj.invFunOn_image subset_rfl]
      _ ≤ (Real.toNNReal (Real.sqrt (1 + L ^ 2)) : ℝ≥0∞) ^ (n : ℝ) *
            (μH[(n : ℝ)] : Measure (Euclidean N)) (Grassmannian.project P '' A) :=
          hinv.hausdorffMeasure_image_le (Nat.cast_nonneg n)
      _ = ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) *
            (μH[(n : ℝ)] : Measure (Euclidean N)) (Grassmannian.project P '' A) := by
          rw [hpow]
  -- Step 6: `μHE[n] = c • μH[n]` with `c = addHaarScalarFactor volume μH[n]`; multiply by `c`.
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] :
          ℝ≥0∞) * (ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) *
            (μH[(n : ℝ)] : Measure (Euclidean N)) (Grassmannian.project P '' A)) := by
        gcongr
    _ = _ := mul_left_comm _ _ _
/-- Child `graph_projection_null_measurable` of the graph fibre bound (Simon Ch. 8, proof of 5.9):
the projection `p = Grassmannian.project P` of an `H^n`-null-measurable `L`-Lipschitz graph `A`
over `P` is `H^n`-null-measurable.  The graph inequality makes `p` injective on `A`, and
`‖p v‖² = ⟪v, p v⟫` makes `p` `1`-Lipschitz.  Writing `A = B ∪ (A ∖ B)` with `B ⊆ A` Borel and
`A ∖ B` null, `p '' B` is Borel by Lusin–Souslin and `p '' (A ∖ B)` is null by the Lipschitz
image bound for `μH[n]`. -/
theorem Submission.intcpt_graph_projection_nullMeasurableSet :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (A : Set (Euclidean N)), 0 ≤ L →
      (∀ y ∈ A, ∀ z ∈ A, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤
        L * ‖Grassmannian.project P (y - z)‖) →
      NullMeasurableSet A (μHE[n] : Measure (Euclidean N)) →
      NullMeasurableSet (Grassmannian.project P '' A) (μHE[n] : Measure (Euclidean N)) := by
  intro N n P L A _ hgraph hA
  -- `p = Grassmannian.project P` is the linear map `P.projectionLinearMap`.
  have hsub : ∀ y z : Euclidean N,
      Grassmannian.project P (y - z) = Grassmannian.project P y - Grassmannian.project P z :=
    fun y z ↦ map_sub P.projectionLinearMap y z
  -- Step 1: the graph inequality makes `p` injective on `A`.
  have hinj : InjOn (Grassmannian.project P) A := by
    intro y hy z hz hyz
    have h := hgraph y hy z hz
    rw [hsub, hyz, sub_self, norm_zero, mul_zero, sub_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- Step 2: `‖p v‖² = ⟪v, p v⟫ ≤ ‖v‖ ‖p v‖`, so `p` is `1`-Lipschitz.
  have hnorm : ∀ v : Euclidean N, ‖Grassmannian.project P v‖ ≤ ‖v‖ := by
    intro v
    have hsq : ‖Grassmannian.project P v‖ ^ 2 = inner ℝ v (Grassmannian.project P v) := by
      rw [← real_inner_self_eq_norm_sq]
      calc inner ℝ (Grassmannian.project P v) (Grassmannian.project P v)
          = inner ℝ v (Grassmannian.project P (Grassmannian.project P v)) :=
            P.projectionLinearMap_isSymmetric v (Grassmannian.project P v)
        _ = inner ℝ v (Grassmannian.project P v) := by rw [Grassmannian.project_project]
    have hle := real_inner_le_norm v (Grassmannian.project P v)
    nlinarith [norm_nonneg (Grassmannian.project P v), norm_nonneg v]
  have hlip : LipschitzWith 1 (Grassmannian.project P) := by
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← hsub]
    exact hnorm (y - z)
  -- Step 3: `A = B ∪ (A ∖ B)` with `B ⊆ A` Borel and `A ∖ B` null.
  obtain ⟨B, hBA, hBm, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hY : (μHE[n] : Measure (Euclidean N)) (A \ B) = 0 := (ae_eq_set.mp hBae).2
  have himage : Grassmannian.project P '' A =
      Grassmannian.project P '' B ∪ Grassmannian.project P '' (A \ B) := by
    rw [← image_union, union_sdiff_cancel hBA]
  -- Step 4: Lusin–Souslin, `p '' B` is Borel.
  have hBimg : MeasurableSet (Grassmannian.project P '' B) :=
    hBm.image_of_continuousOn_injOn hlip.continuous.continuousOn (hinj.mono hBA)
  -- Step 5: the `1`-Lipschitz image of the null set `A ∖ B` is null.
  have hYimg : (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' (A \ B)) = 0 := by
    have hH : (μH[n] : Measure (Euclidean N)) (Grassmannian.project P '' (A \ B)) ≤
        μH[n] (A \ B) := by
      simpa using hlip.hausdorffMeasure_image_le (Nat.cast_nonneg n) (A \ B)
    have hle : (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' (A \ B)) ≤
        μHE[n] (A \ B) := by
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
        ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
      gcongr
    exact nonpos_iff_eq_zero.mp (hle.trans_eq hY)
  -- Step 6: a Borel set union a null set is null-measurable.
  rw [himage]
  exact hBimg.nullMeasurableSet.union_null hYimg

/-- **Fibre bound for one Lipschitz graph piece** (Simon Ch. 8, 5.9; child `graph_piece_fibre_bound`
of `graph_fibre_bound`, steps (iii)–(iv) of B6 in the proof of the integral compactness theorem).
Let `A` be an `H^n`-measurable `L`-Lipschitz graph over the `n`-plane `P`
(`|q(y - z)| ≤ L |p(y - z)|` on `A`, where `p` is the orthogonal projection onto `P` and
`q = id - p`) and `g : ℝ^N → [0,∞]` arbitrary.  Then
`∫⁻_A g dH^n ≤ (1 + L²)^{n/2} ∫⁻_P (Σ_{y ∈ A, p(y) = a} g(y)) dH^n(a)`.  For a
Borel simple `s ≤ g` the level pieces `A_c = s⁻¹{c} ∩ A` are `L`-graphs, so
`H^n(A_c) ≤ (1 + L²)^{n/2} H^n(p(A_c))` (`intcpt_graph_hausdorff_le_projection`) with `p(A_c)`
`H^n`-measurable (`intcpt_graph_projection_nullMeasurableSet`); as `p` is injective on `A`,
`Σ_c c 1_{p(A_c)}` is at most the fibre sum on `P`.  The lower integral is the supremum over such
`s`, so no measurability of `g` is needed. -/
theorem Submission.intcpt_graph_piece_lintegral_le_fibre_sum :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (A : Set (Euclidean N)) (g : Euclidean N → ℝ≥0∞), 0 ≤ L → (∀ y ∈ A, ∀ z ∈ A, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → NullMeasurableSet A (μHE[n] : Measure (Euclidean N)) → ∫⁻ y in A, g y ∂(μHE[n] : Measure (Euclidean N)) ≤ ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) * ∫⁻ a in (P.plane : Set (Euclidean N)), (∑' y : {y : Euclidean N // y ∈ A ∧ Grassmannian.project P y = a}, g y) ∂(μHE[n] : Measure (Euclidean N)) := by
  intro N n P L A g hL hgraph hA
  classical
  set μ : Measure (Euclidean N) := μHE[n]
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2))
  set F : Euclidean N → ℝ≥0∞ := fun a ↦
    ∑' y : {y : Euclidean N // y ∈ A ∧ Grassmannian.project P y = a}, g y
  -- Step 1: `p` is injective on `A` (if `p(y) = p(z)` the graph inequality forces `y = z`), it
  -- maps into `P`, and the finite-dimensional subspace `P` is closed, hence Borel.
  have hinj : InjOn (Grassmannian.project P) A := by
    intro y hy z hz hyz
    have h0 : Grassmannian.project P (y - z) = 0 := by
      change P.projectionLinearMap (y - z) = 0
      rw [map_sub, sub_eq_zero]
      exact hyz
    have h := hgraph y hy z hz
    rwa [h0, norm_zero, mul_zero, sub_zero, norm_le_zero_iff, sub_eq_zero] at h
  have hmem : ∀ y, Grassmannian.project P y ∈ (P.plane : Set (Euclidean N)) :=
    fun y ↦ LinearMap.mem_range_self P.projectionLinearMap y
  have hplane : MeasurableSet (P.plane : Set (Euclidean N)) :=
    (Submodule.closed_of_finiteDimensional P.plane).measurableSet
  -- Steps 2–6: the bound for every Borel simple function `s ≤ g`.
  have key : ∀ s : SimpleFunc (Euclidean N) ℝ≥0∞, ⇑s ≤ g →
      s.lintegral (μ.restrict A) ≤ C * ∫⁻ a in (P.plane : Set (Euclidean N)), F a ∂μ := by
    intro s hsg
    -- Step 2: the level pieces `A_c = s⁻¹{c} ∩ A` are `H^n`-measurable `L`-graphs over `P`, so
    -- `p(A_c)` is `H^n`-measurable and `H^n(A_c) ≤ C H^n(p(A_c))`.
    have hgr : ∀ c, ∀ y ∈ s ⁻¹' {c} ∩ A, ∀ z ∈ s ⁻¹' {c} ∩ A,
        ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖ :=
      fun c y hy z hz ↦ hgraph y hy.2 z hz.2
    have hnull : ∀ c, NullMeasurableSet (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)) μ :=
      fun c ↦ Submission.intcpt_graph_projection_nullMeasurableSet N n P L _ hL (hgr c)
        ((s.measurableSet_fiber c).nullMeasurableSet.inter hA)
    have hbound : ∀ c, μ (s ⁻¹' {c} ∩ A) ≤ C * μ (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)) :=
      fun c ↦ Submission.intcpt_graph_hausdorff_le_projection N n P L _ hL (hgr c)
    -- Step 5: pointwise, `Σ_c c 1_{p(A_c)} ≤ 1_P F`.
    have hpt : ∀ a, ∑ c ∈ s.range,
        (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)).indicator (fun _ ↦ c) a ≤
          (P.plane : Set (Euclidean N)).indicator F a := by
      intro a
      by_cases ha : a ∈ Grassmannian.project P '' A
      · -- (ii) `a = p(y₀)` with `y₀ ∈ A`: by injectivity `a ∈ p(A_c)` iff `s(y₀) = c`, so the sum
        -- is `s(y₀) ≤ g(y₀)`, one term of the fibre sum `F(a)`; and `a ∈ P`.
        obtain ⟨y₀, hy₀, rfl⟩ := ha
        have hterm : ∀ c ∈ s.range,
            (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)).indicator (fun _ ↦ c)
              (Grassmannian.project P y₀) = if s y₀ = c then c else 0 := by
          intro c _
          by_cases hc : s y₀ = c
          · rw [ite_eq_left hc, Set.indicator_of_mem]
            exact ⟨y₀, ⟨hc, hy₀⟩, rfl⟩
          · rw [ite_eq_right hc, Set.indicator_of_notMem]
            rintro ⟨y, ⟨hyc, hyA⟩, hyp⟩
            obtain rfl := hinj hyA hy₀ hyp
            exact hc hyc
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq_of_mem _ _ _ (s.mem_range_self y₀),
          Set.indicator_of_mem (hmem y₀)]
        exact (hsg y₀).trans (ENNReal.le_tsum (f := fun y : {y : Euclidean N //
          y ∈ A ∧ Grassmannian.project P y = Grassmannian.project P y₀} ↦ g y) ⟨y₀, hy₀, rfl⟩)
      · -- (i) `a ∉ p(A)`: then `a ∉ p(A_c) ⊆ p(A)` for every `c`, so the sum vanishes.
        have hzero : ∀ c ∈ s.range,
            (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)).indicator (fun _ ↦ c) a = 0 :=
          fun c _ ↦ Set.indicator_of_notMem (fun h ↦ ha (image_mono inter_subset_right h)) _
        rw [Finset.sum_eq_zero hzero]
        exact zero_le
    -- Steps 3, 4 and 6: `∫ s d(H^n ⌞ A) = Σ_c c H^n(A_c) ≤ C Σ_c c H^n(p(A_c))
    -- = C ∫ Σ_c c 1_{p(A_c)} dH^n ≤ C ∫_P F dH^n`.
    calc s.lintegral (μ.restrict A) = ∑ c ∈ s.range, c * μ (s ⁻¹' {c} ∩ A) := by
          simp only [SimpleFunc.lintegral, Measure.restrict_apply (s.measurableSet_fiber _)]
      _ ≤ ∑ c ∈ s.range, c * (C * μ (Grassmannian.project P '' (s ⁻¹' {c} ∩ A))) :=
          Finset.sum_le_sum fun c _ ↦ mul_le_mul_right (hbound c) c
      _ = C * ∑ c ∈ s.range,
            ∫⁻ a, (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)).indicator (fun _ ↦ c) a ∂μ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ ↦ ?_
          rw [lintegral_indicator_const₀ (hnull c), mul_left_comm]
      _ = C * ∫⁻ a, ∑ c ∈ s.range,
            (Grassmannian.project P '' (s ⁻¹' {c} ∩ A)).indicator (fun _ ↦ c) a ∂μ := by
          rw [lintegral_finsetSum' _ fun c _ ↦ aemeasurable_const.indicator₀ (hnull c)]
      _ ≤ C * ∫⁻ a, (P.plane : Set (Euclidean N)).indicator F a ∂μ :=
          mul_le_mul_right (lintegral_mono hpt) C
      _ = C * ∫⁻ a in (P.plane : Set (Euclidean N)), F a ∂μ := by
          rw [lintegral_indicator hplane]
  -- Step 7: the lower integral `∫⁻_A g` is the supremum of `∫ s d(H^n ⌞ A)` over Borel simple
  -- `s ≤ g`.
  calc ∫⁻ y in A, g y ∂μ
      = ⨆ (s : SimpleFunc (Euclidean N) ℝ≥0∞) (_ : ⇑s ≤ g), s.lintegral (μ.restrict A) := by
        rw [MeasureTheory.lintegral]
    _ ≤ C * ∫⁻ a in (P.plane : Set (Euclidean N)), F a ∂μ := iSup₂_le key

/-- **Fibre bound over countably many Lipschitz graphs** (Simon Ch. 8, 5.9; child
`graph_fibre_bound` of `integral_compactness`, the inequality of step B6 (iii)–(iv) of its proof,
used there instead of the mapping formula in (5)–(6) of the book's proof).  Let `Γ_i` (`i ∈ ℕ`) be
closed `L`-Lipschitz graphs over the `n`-plane `P` (`|q(y - z)| ≤ L |p(y - z)|` on each `Γ_i`, where
`p` is the orthogonal projection onto `P` and `q = id - p`), `G ⊆ ⋃_i Γ_i` an `H^n`-measurable set
and `g : ℝ^N → [0,∞]` arbitrary.  Then
`∫⁻_G g dH^n ≤ (1 + L²)^{n/2} ∫⁻_P (Σ_{y ∈ G, p(y) = a} g(y)) dH^n(a)`.  The pieces
`A_i = G ∩ (Γ_i ∖ ⋃_{j<i} Γ_j)` are pairwise disjoint `H^n`-measurable `L`-graphs with union `G`;
the one-piece bound `intcpt_graph_piece_lintegral_le_fibre_sum` is summed over `i` by countable
superadditivity of the lower integral, and over each `a` the fibres of the `A_i` are disjoint parts
of the fibre of `G`. -/
theorem Submission.intcpt_lipschitz_graph_fibre_bound :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (Γ : ℕ → Set (Euclidean N)) (G : Set (Euclidean N)) (g : Euclidean N → ℝ≥0∞), 0 ≤ L → (∀ i, IsClosed (Γ i)) → (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → G ⊆ ⋃ i, Γ i → NullMeasurableSet G (μHE[n] : Measure (Euclidean N)) → ∫⁻ y in G, g y ∂(μHE[n] : Measure (Euclidean N)) ≤ ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2)) * ∫⁻ a in (P.plane : Set (Euclidean N)), (∑' y : {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a}, g y) ∂(μHE[n] : Measure (Euclidean N)) := by
  intro N n P L Γ G g hL hΓ hΓL hGΓ hG
  set μ : Measure (Euclidean N) := μHE[n]
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 + L ^ 2) ^ ((n : ℝ) / 2))
  -- Step 1: the pieces `A_i = G ∩ (Γ_i ∖ ⋃_{j<i} Γ_j)` are pairwise disjoint `H^n`-measurable
  -- `L`-graphs over `P` with union `G`.
  set A : ℕ → Set (Euclidean N) := fun i ↦ G ∩ disjointed Γ i
  have hAG : ∀ i, A i ⊆ G := fun i ↦ inter_subset_left
  have hAΓ : ∀ i, A i ⊆ Γ i := fun i ↦ inter_subset_right.trans (disjointed_subset Γ i)
  have hAm : ∀ i, NullMeasurableSet (A i) μ := fun i ↦
    hG.inter (MeasurableSet.disjointed (fun j ↦ (hΓ j).measurableSet) i).nullMeasurableSet
  have hAd : Pairwise (Function.onFun Disjoint A) := fun i j hij ↦
    (disjoint_disjointed Γ hij).mono inter_subset_right inter_subset_right
  have hAU : ⋃ i, A i = G := by
    show ⋃ i, G ∩ disjointed Γ i = G
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.2 hGΓ]
  -- Step 2: the lower integral is countably superadditive (no measurability is needed).
  have hsup : ∀ (ν : Measure (Euclidean N)) (f : ℕ → Euclidean N → ℝ≥0∞),
      ∑' i, ∫⁻ a, f i a ∂ν ≤ ∫⁻ a, ∑' i, f i a ∂ν := by
    intro ν f
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun m ↦ le_trans ?_
      (lintegral_mono fun a ↦ ENNReal.sum_le_tsum (f := fun i ↦ f i a) (Finset.range m))
    induction m with
    | zero => simp
    | succ m ih =>
      calc ∑ i ∈ Finset.range (m + 1), ∫⁻ a, f i a ∂ν
          = ∑ i ∈ Finset.range m, ∫⁻ a, f i a ∂ν + ∫⁻ a, f m a ∂ν := Finset.sum_range_succ _ _
        _ ≤ ∫⁻ a, ∑ i ∈ Finset.range m, f i a ∂ν + ∫⁻ a, f m a ∂ν := by gcongr
        _ ≤ ∫⁻ a, (∑ i ∈ Finset.range m, f i a + f m a) ∂ν := le_lintegral_add _ _
        _ = ∫⁻ a, ∑ i ∈ Finset.range (m + 1), f i a ∂ν := by simp only [Finset.sum_range_succ]
  -- Step 3: over each `a`, the fibres of the `A_i` are disjoint parts of the fibre of `G`.
  have hfib : ∀ a : Euclidean N,
      ∑' i, ∑' y : {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}, g y ≤
        ∑' y : {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a}, g y := by
    intro a
    let φ : (Σ i, {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}) →
        {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a} :=
      fun q ↦ ⟨q.2.1, hAG q.1 q.2.2.1, q.2.2.2⟩
    have hφ : Function.Injective φ := by
      rintro ⟨i, y, hyi, hya⟩ ⟨j, z, hzj, hza⟩ h
      obtain rfl : y = z := congrArg Subtype.val h
      obtain rfl : i = j := by
        by_contra hij
        exact Set.disjoint_left.1 (hAd hij) hyi hzj
      rfl
    calc ∑' i, ∑' y : {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}, g y
        = ∑' q, g (φ q) := (ENNReal.tsum_sigma' fun q ↦ g (φ q)).symm
      _ ≤ ∑' y : {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a}, g y :=
        ENNReal.tsum_comp_le_tsum_of_injective hφ fun y ↦ g y
  -- Step 4: split `∫⁻_G` over the pieces, apply the one-piece bound and recombine.
  calc ∫⁻ y in G, g y ∂μ = ∑' i, ∫⁻ y in A i, g y ∂μ := by
        rw [← lintegral_iUnion₀ hAm hAd.aedisjoint g, hAU]
    _ ≤ ∑' i, C * ∫⁻ a in (P.plane : Set (Euclidean N)),
          (∑' y : {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}, g y) ∂μ :=
        ENNReal.tsum_le_tsum fun i ↦ Submission.intcpt_graph_piece_lintegral_le_fibre_sum N n P L
          (A i) g hL (fun y hy z hz ↦ hΓL i y (hAΓ i hy) z (hAΓ i hz)) (hAm i)
    _ = C * ∑' i, ∫⁻ a in (P.plane : Set (Euclidean N)),
          (∑' y : {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}, g y) ∂μ :=
        ENNReal.tsum_mul_left
    _ ≤ C * ∫⁻ a in (P.plane : Set (Euclidean N)),
          ∑' i, (∑' y : {y : Euclidean N // y ∈ A i ∧ Grassmannian.project P y = a}, g y) ∂μ :=
        mul_le_mul_right (hsup _ _) C
    _ ≤ C * ∫⁻ a in (P.plane : Set (Euclidean N)),
          (∑' y : {y : Euclidean N // y ∈ G ∧ Grassmannian.project P y = a}, g y) ∂μ :=
        mul_le_mul_right (lintegral_mono hfib) C

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
