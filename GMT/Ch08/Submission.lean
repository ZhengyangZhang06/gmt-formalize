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
