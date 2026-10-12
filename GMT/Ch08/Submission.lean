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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
