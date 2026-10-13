import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.Submanifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Poincare.SimonGMT.Chapter08.StationaryMonotonicity

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

/-- **Simon Ch. 8, 3.3, 3.4 and 3.6** (child `monotonicity_density` of `main_theorem`): the
monotonicity formula under `‖δV‖ ≤ Λ μ_V` (3.3), the stationary monotonicity identity (3.4), and
the `μ_V`-a.e. existence and finiteness of `Θ^n(μ_V, ·)` with a Borel representative (3.6).
Each conjunct is its own child theorem; 3.6 is derived there from 3.3 and the a.e. bound 3.1. -/
theorem Submission.monotonicity_and_density_theorems :
    MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE :=
  ⟨Submission.monotonicity_formula_8_3_3, Submission.stationary_monotonicity_identity_8_3_4,
    Submission.density_exists_ae_8_3_6⟩

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
