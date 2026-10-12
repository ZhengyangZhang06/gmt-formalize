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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
