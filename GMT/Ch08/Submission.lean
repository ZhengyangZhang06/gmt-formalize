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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
