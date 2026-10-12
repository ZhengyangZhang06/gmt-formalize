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

/-- Weight form of flat convergence (Simon Ch. 8, proof of 5.9, pp. 218–219): if
`∫ f dW_k → θ₀ ∫ f dv(P)` for every `f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ B°_5(0) × G(N,n)`, then
`∫ g dμ_{W_k} → θ₀ ∫_P g dH^n` for every `g ∈ C_c(ℝ^N)` with `spt g ⊆ B°_5(0)`. -/
theorem Submission.intcpt_fli_weight_integral_tendsto :
    ∀ (N n : ℕ) (P : Grassmannian N n) (θ₀ : ℝ) (W : ℕ → Varifold N n (ball (0 : Euclidean N) 5)), (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))) → ∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclidean N) 5 → Tendsto (fun k ↦ ∫ x, g x ∂(W k).weight) atTop (𝓝 (θ₀ * ∫ x in (P.plane : Set (Euclidean N)), g x ∂(μHE[n] : Measure (Euclidean N)))) := by
  intro N n P θ₀ W hconv g hg hgc hg5
  -- Steps 1–3: the lift `F (z, S) = g z` has `tsupport F ⊆ spt g × G(N,n)`, a compact set as
  -- `G(N,n)` is compact, so `F ∈ C_c(ℝ^N × G(N,n))`.
  have hFsupp : tsupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1) ⊆
      tsupport g ×ˢ (univ : Set (Grassmannian N n)) :=
    closure_minimal (fun z hz ↦ ⟨subset_tsupport g hz, mem_univ _⟩)
      ((isClosed_tsupport g).prod isClosed_univ)
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    { toFun := fun z ↦ g z.1
      continuous_toFun := hg.comp continuous_fst
      hasCompactSupport' :=
        (hgc.isCompact.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _) hFsupp }
  -- Step 4: `tsupport f ⊆ B°_5(0) × G(N,n)`, so the hypothesis applies to `f`.
  have hlim := hconv f (hFsupp.trans (Set.prod_mono hg5 subset_rfl))
  -- Step 5: `∫ f dW_k = ∫ g dμ_{W_k}`, by `integral_map` along `Prod.fst`.
  have hleft : ∀ k, ∫ z, f z ∂(W k).measure = ∫ x, g x ∂(W k).weight := fun k ↦ by
    rw [Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
    rfl
  -- Step 6: `∫ f dv(P) = ∫_P g dH^n`, by `integral_map` along `y ↦ (y, P)`.
  have hright : ∫ z, f z ∂(planeVarifoldMeasure P) =
      ∫ x in (P.plane : Set (Euclidean N)), g x ∂(μHE[n] : Measure (Euclidean N)) := by
    rw [planeVarifoldMeasure, integral_map measurable_prodMk_right.aemeasurable
      (map_continuous f).aestronglyMeasurable]
    rfl
  -- Step 7: substitute steps 5 and 6 into step 4.
  simpa only [hleft, hright] using hlim

/-- **Dimension `0`: flat limits of integral `0`-varifolds have integer multiplicity** (child
`dim_zero` of `flat_limit_integer`, step 1 of its proof; Simon Ch. 8, proof of 5.9).  For `n = 0`
the plane `P` is `{0}` and `H^0` is counting measure, so `∫_P g dH^0 = g(0)`.  Each `W_k = v(M, θ)`
is carried by a countable set `M` with `θ ∈ ℕ` on `M`, so `μ_{W_k}(B_{1/2}(0)) ∈ ℕ ∪ {∞}`.
Cut-offs `g₁ ≤ 1_{B_{1/2}(0)} ≤ g₂` with `g₁(0) = g₂(0) = 1` and `weight_tendsto` give
`μ_{W_k}(B_{1/2}(0)) → θ₀`; as `ℕ` is closed in `ℝ`, `θ₀ ∈ ℕ`. -/
theorem Submission.intcpt_fli_dim_zero_integer :
    ∀ (N : ℕ) (P : Grassmannian N 0) (θ₀ : ℝ) (W : ℕ → Varifold N 0 (ball (0 : Euclidean N) 5)), 0 < θ₀ → (∀ k, IsIntegral (W k)) → (∀ f : C_c(Euclidean N × Grassmannian N 0, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N 0)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))) → ∃ m : ℕ, θ₀ = m := by
  intro N P θ₀ W hθ₀ hint hconv
  -- Step 1: `dim P.plane = 0`, so `P.plane = ⊥`, i.e. `{0}` as a set.
  have hplane : (P.plane : Set (Euclidean N)) = {0} := by
    rw [Submodule.finrank_eq_zero.1 (Grassmannian.finrank_plane P), Submodule.bot_coe]
  -- Step 2: `H^0 = μH[0]` gives every point mass `1`, hence `∫_P g dH^0 = g(0)`.
  have hH0 : ∀ x : Euclidean N, (μHE[0] : Measure (Euclidean N)) {x} = 1 := fun x ↦ by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hplane_int : ∀ g : Euclidean N → ℝ,
      ∫ x in (P.plane : Set (Euclidean N)), g x ∂(μHE[0] : Measure (Euclidean N)) = g 0 := by
    intro g
    rw [hplane, integral_singleton, measureReal_def, hH0, ENNReal.toReal_one, one_smul]
  -- Step 3: the real parts of the masses `μ_{W_k}(B_{1/2}(0))` are natural numbers.
  have hnat : ∀ k, ∃ m : ℕ, ((W k).weight (closedBall (0 : Euclidean N) (1 / 2))).toReal = m := by
    intro k
    -- Step 3a: `W_k = v(M, θ)` with `θ ∈ ℕ` at `(H^0 ⌞ M)`-a.e. point.
    obtain ⟨M, θ, hVM, hθ⟩ := hint k
    -- Step 3b: `M` is countable: the `H^0`-null part `M₀` of its Lipschitz cover is empty (points
    -- have `H^0`-measure `1`), and each image of the one-point space `ℝ^0` is a single point.
    have hMc : M.Countable := by
      obtain ⟨M₀, hM₀, F, -, hcover⟩ := hVM.2.2.1
      have hM₀e : M₀ = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦ by
        have h := measure_mono (μ := (μHE[0] : Measure (Euclidean N))) (singleton_subset_iff.2 hx)
        rw [hH0, hM₀] at h
        exact absurd h (by norm_num)
      rw [hM₀e, empty_union] at hcover
      exact (countable_iUnion fun j ↦ countable_range (F j)).mono hcover
    -- Step 3c: `θ(x) ∈ ℕ` for every `x ∈ M`: a point of `M` where this fails would be a set of
    -- `H^0`-measure `1` inside the `(H^0 ⌞ M)`-null exceptional set.
    have hθM : ∀ x ∈ M, ∃ j : ℕ, θ x = j := fun x hx ↦ by
      by_contra hcon
      have h : (μHE[0] : Measure (Euclidean N)) {x} ≤ 0 :=
        (measure_mono (singleton_subset_iff.2
          (show x ∈ {y | ¬∃ j : ℕ, θ y = j} ∩ M from ⟨hcon, hx⟩))).trans
          ((Measure.le_restrict_apply M _).trans_eq (ae_iff.1 hθ))
      rw [hH0] at h
      exact absurd h (by norm_num)
    -- Step 3d: `μ_{W_k}(B_{1/2}(0)) = ∫⁻_S θ dH^0` for a set `S ⊆ M`, hence countable, so it is the
    -- sum `Σ_{x ∈ S} θ(x)` of natural numbers.
    set S := {x | x ∈ M ∧ ∃ T : Grassmannian N 0,
      Chapter03.HasWeightedApproximateTangentSpaceAt 0 M θ x T.plane ∧
        (x, T) ∈ closedBall (0 : Euclidean N) (1 / 2) ×ˢ (univ : Set (Grassmannian N 0))} with hS
    have hSc : S.Countable := hMc.mono fun x hx ↦ hx.1
    have hw : (W k).weight (closedBall (0 : Euclidean N) (1 / 2)) =
        ∑' x : S, ((⌊θ x⌋₊ : ℕ) : ℝ≥0∞) := by
      rw [Varifold.weight_apply _ measurableSet_closedBall,
        hVM.2.2.2.2.2 _ (measurableSet_closedBall.prod MeasurableSet.univ),
        lintegral_countable _ hSc]
      refine tsum_congr fun x ↦ ?_
      obtain ⟨j, hj⟩ := hθM x x.2.1
      rw [hH0, mul_one, hj, Nat.floor_natCast, ENNReal.ofReal_natCast]
    -- Step 3e: an infinite sum has real part `0`; a finite one has only finitely many terms
    -- `≥ 1`, the others vanish, so it is the cast of a finite sum of natural numbers.
    rw [hw]
    by_cases htop : ∑' x : S, ((⌊θ x⌋₊ : ℕ) : ℝ≥0∞) = ∞
    · exact ⟨0, by rw [htop, ENNReal.toReal_top, Nat.cast_zero]⟩
    have hfin : {x : S | (1 : ℝ≥0∞) ≤ ((⌊θ x⌋₊ : ℕ) : ℝ≥0∞)}.Finite :=
      ENNReal.finite_const_le_of_tsum_ne_top htop one_ne_zero
    have hzero : ∀ x ∉ hfin.toFinset, ((⌊θ x⌋₊ : ℕ) : ℝ≥0∞) = 0 := fun x hx ↦ by
      have h : ((⌊θ x⌋₊ : ℕ) : ℝ≥0∞) < 1 := not_le.1 fun h ↦ hx (hfin.mem_toFinset.2 h)
      rw [Nat.cast_lt_one.1 h, Nat.cast_zero]
    refine ⟨∑ x ∈ hfin.toFinset, ⌊θ x⌋₊, ?_⟩
    rw [tsum_eq_sum hzero, ← Nat.cast_sum, ENNReal.toReal_natCast]
  -- Step 4: cut-offs `g₁ ≤ 1_{B_{1/2}(0)} ≤ g₂`: continuous, `[0,1]`-valued, vanishing off
  -- `B_{3/4}(0)` (a compact subset of `B°_5(0)`), with `g₁(0) = g₂(0) = 1`.
  set g₁ : Euclidean N → ℝ := fun x ↦ max 0 (min 1 (2 - 4 * ‖x‖)) with hg₁
  set g₂ : Euclidean N → ℝ := fun x ↦ max 0 (min 1 (3 - 4 * ‖x‖)) with hg₂
  have hg₁c : Continuous g₁ := by simp only [hg₁]; fun_prop
  have hg₂c : Continuous g₂ := by simp only [hg₂]; fun_prop
  have hg₁0 : ∀ x, 0 ≤ g₁ x := fun x ↦ le_max_left _ _
  have hg₂0 : ∀ x, 0 ≤ g₂ x := fun x ↦ le_max_left _ _
  have hg₁1 : ∀ x, g₁ x ≤ 1 := fun x ↦ max_le zero_le_one (min_le_left _ _)
  have hg₂1 : ∀ x, g₂ x ≤ 1 := fun x ↦ max_le zero_le_one (min_le_left _ _)
  have hg₁z : ∀ x, 1 / 2 ≤ ‖x‖ → g₁ x = 0 := fun x hx ↦
    max_eq_left ((min_le_right _ _).trans (by linarith))
  have hg₂z : ∀ x, 3 / 4 ≤ ‖x‖ → g₂ x = 0 := fun x hx ↦
    max_eq_left ((min_le_right _ _).trans (by linarith))
  have hg₂one : ∀ x, ‖x‖ ≤ 1 / 2 → g₂ x = 1 := fun x hx ↦ by
    simp only [hg₂]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hg₁at0 : g₁ 0 = 1 := by norm_num [hg₁]
  have hg₂at0 : g₂ 0 = 1 := hg₂one 0 (by norm_num)
  have hsupp : ∀ g : Euclidean N → ℝ, (∀ x, 3 / 4 ≤ ‖x‖ → g x = 0) →
      tsupport g ⊆ closedBall (0 : Euclidean N) (3 / 4) := fun g hg ↦
    closure_minimal (fun x hx ↦ mem_closedBall_zero_iff.2
      (not_lt.1 fun h ↦ hx (hg x h.le))) isClosed_closedBall
  have hs₁ := hsupp g₁ fun x hx ↦ hg₁z x (by linarith)
  have hs₂ := hsupp g₂ hg₂z
  have hcs₁ : HasCompactSupport g₁ :=
    (isCompact_closedBall (0 : Euclidean N) (3 / 4)).of_isClosed_subset (isClosed_tsupport _) hs₁
  have hcs₂ : HasCompactSupport g₂ :=
    (isCompact_closedBall (0 : Euclidean N) (3 / 4)).of_isClosed_subset (isClosed_tsupport _) hs₂
  have h5 : closedBall (0 : Euclidean N) (3 / 4) ⊆ ball 0 5 := closedBall_subset_ball (by norm_num)
  -- Step 5: by `weight_tendsto` and step 2, `∫ g_i dμ_{W_k} → θ₀ g_i(0) = θ₀`.
  have hl₁ := Submission.intcpt_fli_weight_integral_tendsto N 0 P θ₀ W hconv g₁ hg₁c hcs₁
    (hs₁.trans h5)
  have hl₂ := Submission.intcpt_fli_weight_integral_tendsto N 0 P θ₀ W hconv g₂ hg₂c hcs₂
    (hs₂.trans h5)
  rw [hplane_int, hg₁at0, mul_one] at hl₁
  rw [hplane_int, hg₂at0, mul_one] at hl₂
  -- Step 6: `μ_{W_k}(B_{3/4}(0)) < ∞`, so the `g_i` are `μ_{W_k}`-integrable, and
  -- `∫ g₁ dμ_{W_k} ≤ μ_{W_k}(B_{1/2}(0)) ≤ ∫ g₂ dμ_{W_k}` in `[0, ∞]`.
  have hint_g : ∀ k, ∀ g : Euclidean N → ℝ, Continuous g → (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
      tsupport g ⊆ closedBall (0 : Euclidean N) (3 / 4) → Integrable g (W k).weight := by
    intro k g hg hg0 hg1 hgs
    have hon : IntegrableOn g (closedBall (0 : Euclidean N) (3 / 4)) (W k).weight :=
      Measure.integrableOn_of_bounded (M := 1)
        (Varifold.weight_finite_on_compact (W k) _ (isCompact_closedBall _ _) h5)
        hg.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
          exact hg1 x)
    exact (integrableOn_iff_integrable_of_support_subset ((subset_tsupport g).trans hgs)).1 hon
  have hlow : ∀ k, ENNReal.ofReal (∫ x, g₁ x ∂(W k).weight) ≤
      (W k).weight (closedBall (0 : Euclidean N) (1 / 2)) := by
    intro k
    rw [ofReal_integral_eq_lintegral_ofReal (hint_g k g₁ hg₁c hg₁0 hg₁1 hs₁)
      (Eventually.of_forall hg₁0), ← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ closedBall (0 : Euclidean N) (1 / 2)
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hg₁1 x)
    · rw [indicator_of_notMem hx, hg₁z x (not_le.1 (mt mem_closedBall_zero_iff.2 hx)).le,
        ENNReal.ofReal_zero]
  have hup : ∀ k, (W k).weight (closedBall (0 : Euclidean N) (1 / 2)) ≤
      ENNReal.ofReal (∫ x, g₂ x ∂(W k).weight) := by
    intro k
    rw [ofReal_integral_eq_lintegral_ofReal (hint_g k g₂ hg₂c hg₂0 hg₂1 hs₂)
      (Eventually.of_forall hg₂0), ← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ closedBall (0 : Euclidean N) (1 / 2)
    · rw [indicator_of_mem hx, Pi.one_apply, hg₂one x (mem_closedBall_zero_iff.1 hx),
        ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx]
      exact zero_le
  -- Step 7: squeeze: `μ_{W_k}(B_{1/2}(0)) → θ₀` in `[0, ∞]`, hence its real part tends to `θ₀`.
  have hlim : Tendsto (fun k ↦ (W k).weight (closedBall (0 : Euclidean N) (1 / 2))) atTop
      (𝓝 (ENNReal.ofReal θ₀)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le ((ENNReal.continuous_ofReal.tendsto θ₀).comp hl₁)
      ((ENNReal.continuous_ofReal.tendsto θ₀).comp hl₂) hlow hup
  have hlimR : Tendsto (fun k ↦ ((W k).weight (closedBall (0 : Euclidean N) (1 / 2))).toReal)
      atTop (𝓝 θ₀) := by
    have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hlim
    rwa [ENNReal.toReal_ofReal hθ₀.le] at h
  -- Step 8: the terms lie in the closed set `ℕ ⊆ ℝ` (step 3), hence so does the limit `θ₀`.
  obtain ⟨m, hm⟩ : θ₀ ∈ range ((↑) : ℕ → ℝ) :=
    Nat.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto hlimR
      (Eventually.of_forall fun k ↦ (hnat k).imp fun m hm ↦ hm.symm)
  exact ⟨m, hm.symm⟩

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
