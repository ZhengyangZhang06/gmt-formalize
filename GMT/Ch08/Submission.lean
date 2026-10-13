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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
