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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
