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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
