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

/-- Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(y,S) = g(y)`):
if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`,
`t^{-n} ∫ g(t^{-1}(y - x)) dμ_V(y) → θ ∫_T g dH^n` as `t ↓ 0`. -/
theorem Submission.tgc_weight_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ y, g (t⁻¹ • (y - x)) ∂V.weight) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)))) := by
  intro N n U V x T θ hT g
  -- Step 1: the lifted test function `f(y, S) = g(y)` is compactly supported, `G(N,n)` being
  -- compact (it vanishes off `tsupport g ×ˢ univ`).
  have hf : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1) :=
    HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) fun z hz ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨h, mem_univ _⟩
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    ⟨⟨fun z ↦ g z.1, (map_continuous g).comp continuous_fst⟩, hf⟩
  have hfc : Continuous (f : Euclidean N × Grassmannian N n → ℝ) := map_continuous f
  -- Step 2: the convergence clause of Definition 1.1 applied to `f`.
  have hlim := hT.2.2 f
  -- Step 3: the limit, `∫ f dv(T) = ∫_T g dH^n` (push-forward along `y ↦ (y, T)`).
  have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
      ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) := by
    rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T)) (by fun_prop)
      hfc.aestronglyMeasurable]
    rfl
  rw [hplane] at hlim
  -- Step 4: for `t > 0`, `∫ f dV_{x,t} = t^{-n} ∫ g(t^{-1}(y - x)) dμ_V(y)`; step 5: these agree
  -- on `Ioi 0 ∈ 𝓝[>] 0`, so the limit transfers.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (le_of_lt ht)) n
  have hg : Continuous fun y : Euclidean N ↦ g (t⁻¹ • (y - x)) := by fun_prop
  rw [rescaledMeasure, integral_smul_measure,
    integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2))
      (by fun_prop) hfc.aestronglyMeasurable, ENNReal.toReal_ofReal ht', smul_eq_mul,
    Varifold.weight, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  rfl
/-- `H^n(T ∩ B_r(0)) = ω_n r^n` for an `n`-plane `T ∈ G(N,n)` and every `r ≥ 0` (step (1.2) of
the tangent graph cover proof): an isometric parametrization of `T` by `ℝ^n` carries `H^n` on `T`
to Lebesgue measure on `ℝ^n`. -/
theorem Submission.tgc_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: an orthonormal basis of `T.plane` indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  -- Step 2: the linear isometry `J : ℝ^n → ℝ^N`, with range `T.plane`.
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  -- Step 3: `J (B_r(0)) = T.plane ∩ B_r(0)`.
  have himg : J '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(b.repr.symm u).2, ?_⟩
      rw [mem_closedBall_zero_iff, J.norm_map]
      exact mem_closedBall_zero_iff.mp hu
    · rintro ⟨hy, hyr⟩
      exact ⟨b.repr ⟨y, hy⟩, by simpa using hyr, by simp [J]⟩
  -- Steps 4–6: isometry invariance, `μHE[n] = volume` on `ℝ^n`, and the Haar closed-ball formula.
  rw [← himg, J.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hr,
    finrank_euclideanSpace_fin, unitBallVolume, ENNReal.ofReal_pow hr, mul_comm]

/-- **Lower mass bound at a tangent point** (child `lower_mass_bound` of `tangent_graph_cover`,
step (1.3) of its proof, in eventual form): if `V` has tangent plane `T` with multiplicity `θ` at
`x`, then for every `c < θ ω_n` we have `c t^n ≤ μ_V(B_t(x))` for all small `t > 0`.  Choose
`κ ∈ (0,1)` with `c < θ ω_n κ^n` and the cut-off `g = min(1, max(0, (1 - |v|)/(1 - κ)))`, so that
`1_{B_κ(0)} ≤ g ≤ 1_{B_1(0)}`.  Then `θ ∫_T g dH^n ≥ θ H^n(T ∩ B_κ(0)) = θ ω_n κ^n > c`
(`plane_ball_measure`), the weight blow-ups `t^{-n} ∫ g((y - x)/t) dμ_V(y)` tend to
`θ ∫_T g dH^n` (`weight_blowup`), and each of them is at most `t^{-n} μ_V(B_t(x))`. -/
theorem Submission.tgc_tangent_weight_lower_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ c : ℝ≥0∞, c < ENNReal.ofReal θ * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ V.weight (closedBall x t) := by
  intro N n U V x T θ hT c hc
  -- Step 1: `θ > 0` and `ω_n < ∞`, so `c < θ ω_n < ∞`; pass to real numbers.
  have hθ : 0 < θ := hT.2.1
  have hω : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcr : c.toReal < θ * (unitBallVolume n).toReal := by
    have h := (ENNReal.toReal_lt_toReal hc_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 2: choose `κ ∈ (0,1)` with `c < θ ω_n κ^n`, by continuity of `κ ↦ θ ω_n κ^n` at `1`.
  have hcont : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    have h := ((continuous_pow n).tendsto (1 : ℝ)).const_mul (θ * (unitBallVolume n).toReal)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hκ01 : ∀ᶠ κ in 𝓝[<] (1 : ℝ), κ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨κ, hκc, hκ0, hκ1⟩ := ((hcont.eventually (eventually_gt_nhds hcr)).and hκ01).exists
  have h1κ : 0 < 1 - κ := sub_pos.2 hκ1
  -- Step 3: the cut-off `g(v) = min(1, max(0, (1 - |v|)/(1 - κ)))` lies in `C_c(ℝ^N)`, and
  -- `1_{B_κ(0)} ≤ g ≤ 1_{B_1(0)}`.
  have hcut : ∀ v : Euclidean N, 1 ≤ ‖v‖ → min 1 (max 0 ((1 - ‖v‖) / (1 - κ))) = 0 :=
    fun v hv ↦ by
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) h1κ.le),
        min_eq_right zero_le_one]
  have hout : ∀ v : Euclidean N, v ∉ closedBall (0 : Euclidean N) 1 → 1 ≤ ‖v‖ := fun v hv ↦
    (not_le.1 (mt mem_closedBall_zero_iff.2 hv)).le
  let g : C_c(Euclidean N, ℝ) :=
    ⟨⟨fun v ↦ min 1 (max 0 ((1 - ‖v‖) / (1 - κ))), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 1) fun v hv ↦ hcut v (hout v hv)⟩
  have hg : ∀ v, g v = min 1 (max 0 ((1 - ‖v‖) / (1 - κ))) := fun _ ↦ rfl
  have hg_nonneg : ∀ v, 0 ≤ g v := fun _ ↦ le_min zero_le_one (le_max_left _ _)
  have hg_le : ∀ v, g v ≤ 1 := fun _ ↦ min_le_left _ _
  have hg_one : ∀ v : Euclidean N, ‖v‖ ≤ κ → g v = 1 := fun v hv ↦ by
    have h : 1 ≤ (1 - ‖v‖) / (1 - κ) := (one_le_div h1κ).2 (by linarith)
    rw [hg, max_eq_right (zero_le_one.trans h), min_eq_left h]
  -- Step 4: `θ ∫_T g dH^n ≥ θ H^n(T ∩ B_κ(0)) = θ ω_n κ^n > c` (`plane_ball_measure`).
  set ν := (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hνB : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n :=
    fun r hr ↦ by
      rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact Submission.tgc_plane_closedBall_hausdorff N n T r hr
  have hνB_ne : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) ≠ ∞ := fun r hr ↦ by
    rw [hνB r hr]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hg_int : Integrable g ν :=
    (integrableOn_iff_integrable_of_support_subset fun v hv ↦
        by_contra fun hv' ↦ hv ((hg v).trans (hcut v (hout v hv')))).1
      (Measure.integrableOn_of_bounded (M := 1) (hνB_ne 1 zero_le_one)
        (map_continuous g).aestronglyMeasurable
        (ae_of_all _ fun v ↦ (Real.norm_of_nonneg (hg_nonneg v)).trans_le (hg_le v)))
  have hκ_int : Integrable ((closedBall (0 : Euclidean N) κ).indicator fun _ ↦ (1 : ℝ)) ν :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const (hνB_ne κ hκ0.le))
  have hκ_le : (closedBall (0 : Euclidean N) κ).indicator (fun _ ↦ (1 : ℝ)) ≤ g := fun v ↦ by
    by_cases hv : v ∈ closedBall (0 : Euclidean N) κ
    · rw [indicator_of_mem hv, hg_one v (mem_closedBall_zero_iff.1 hv)]
    · rw [indicator_of_notMem hv]
      exact hg_nonneg v
  have hint : (unitBallVolume n).toReal * κ ^ n ≤
      ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) := by
    have h := integral_mono hκ_int hg_int hκ_le
    rwa [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      measureReal_def, hνB κ hκ0.le, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hκ0.le] at h
  have hℓ : c.toReal <
      θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) :=
    calc c.toReal < θ * (unitBallVolume n).toReal * κ ^ n := hκc
      _ = θ * ((unitBallVolume n).toReal * κ ^ n) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hint hθ.le
  -- Step 5: by `weight_blowup`, `t^{-n} ∫ g((y - x)/t) dμ_V(y) > c` for all small `t > 0`.
  filter_upwards [(Submission.tgc_weight_blowup_tendsto N n U V x T θ hT g).eventually
    (eventually_gt_nhds hℓ), self_mem_nhdsWithin] with t ht ht0
  replace ht0 : 0 < t := ht0
  -- Step 6: `g((y - x)/t) ≤ 1_{B_t(x)}(y)`, so the blow-up integral is at most `μ_V(B_t(x))`.
  rcases eq_or_ne (V.weight (closedBall x t)) ∞ with hB | hB
  · rw [hB]
    exact le_top
  have hle : ∀ y, g (t⁻¹ • (y - x)) ≤ (closedBall x t).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ closedBall x t
    · rw [indicator_of_mem hy]
      exact hg_le _
    · rw [mem_closedBall, not_le] at hy
      have h : 1 ≤ ‖t⁻¹ • (y - x)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_eq_div,
          one_le_div ht0, ← dist_eq_norm]
        exact hy.le
      rw [indicator_of_notMem (by rwa [mem_closedBall, not_le]), hg, hcut _ h]
  have hcmp : ∫ y, g (t⁻¹ • (y - x)) ∂V.weight ≤ (V.weight (closedBall x t)).toReal := by
    have h : ∫ y, g (t⁻¹ • (y - x)) ∂V.weight ≤
        ∫ y, (closedBall x t).indicator (fun _ ↦ (1 : ℝ)) y ∂V.weight :=
      integral_mono_of_nonneg (ae_of_all _ fun y ↦ hg_nonneg _)
        ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hB))
        (ae_of_all _ hle)
    rwa [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      measureReal_def] at h
  -- Step 7: back in `[0, ∞]`, `c < t^{-n} μ_V(B_t(x))`; multiply by `t^n`.
  have htn : 0 ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 ht0.le) n
  have hlt : c < ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall x t) := by
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
      (ht.trans_le (mul_le_mul_of_nonneg_left hcmp htn))
    rwa [ENNReal.ofReal_toReal hc_top, ENNReal.ofReal_mul htn, ENNReal.ofReal_toReal hB] at h
  calc c * ENNReal.ofReal t ^ n
      ≤ ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall x t) * ENNReal.ofReal t ^ n :=
        mul_le_mul_left hlt.le _
    _ = V.weight (closedBall x t) := by
        rw [mul_right_comm, ← ENNReal.ofReal_pow ht0.le, ← ENNReal.ofReal_mul htn, ← mul_pow,
          inv_mul_cancel₀ ht0.ne', one_pow, ENNReal.ofReal_one, one_mul]
/-- **Cone decay at a tangent point** (child `cone_decay` of `tangent_graph_cover`, step (1.4) of
its proof; the varifold form of the second limit in Simon Ch. 3, Remark 1.5(3), for a tangent plane
as in Ch. 8, 1.1): if `V` has tangent plane `T` with multiplicity `θ` at `x` and `n ≥ 1`, then for
every `β > 0` the cone section `{y ∈ B_t(x) : β|y - x| ≤ |(y - x) - p_T(y - x)|}` has `μ_V`-mass
`o(t^n)` as `t ↓ 0`.  The rescaled section `C` meets `T` only at `0`, an `H^n`-null set, so a
cut-off `g ≥ 1_C` has `θ ∫_T g dH^n` as small as we like, and the weight blow-ups of `g` bound
`t^{-n}` times the `μ_V`-mass of the section. -/
theorem Submission.tgc_tangent_cone_weight_decay :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), 0 < n → HasTangentPlane V x T θ → ∀ β : ℝ, 0 < β → ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), V.weight {y | y ∈ closedBall x t ∧ β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤ ε * ENNReal.ofReal t ^ n := by
  intro N n U V x T θ hn hT β hβ ε hε
  have hblow := Submission.tgc_weight_blowup_tendsto N n U V x T θ hT
  have hplane := Submission.tgc_plane_closedBall_hausdorff N n T
  -- Step 1: the case `ε = ∞` is trivial; otherwise `ε = ofReal e` with `e > 0`.
  by_cases hεtop : ε = ∞
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hεtop, ENNReal.top_mul (pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne')]
    exact le_top
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 < e ∧ ε = ENNReal.ofReal e :=
    ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεtop, (ENNReal.ofReal_toReal hεtop).symm⟩
  obtain ⟨hxU, hθ, -⟩ := hT
  set ν : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hp_cont : Continuous (Grassmannian.project T) :=
    T.projectionLinearMap.continuous_of_finiteDimensional
  have hp_smul : ∀ (c : ℝ) (v : Euclidean N),
      Grassmannian.project T (c • v) = c • Grassmannian.project T v :=
    fun c v ↦ T.projectionLinearMap.map_smul c v
  -- Step 2: the rescaled cone section `C`; it is closed, lies in `B_1(0)`, contains `0`, and
  -- `t⁻¹ • (y - x) ∈ C` for every `y` in the cone section at scale `t`.
  set C : Set (Euclidean N) := {w | ‖w‖ ≤ 1 ∧ β * ‖w‖ ≤ ‖w - Grassmannian.project T w‖}
  have hC_closed : IsClosed C :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le (continuous_const.mul continuous_norm) (continuous_id.sub hp_cont).norm)
  have hC_ball : C ⊆ closedBall 0 1 := fun w hw ↦ by simpa using hw.1
  have hC0 : (0 : Euclidean N) ∈ C := by
    refine ⟨by simp, ?_⟩
    rw [norm_zero, mul_zero]
    exact norm_nonneg _
  have hC_scale : ∀ t : ℝ, 0 < t → ∀ y : Euclidean N, y ∈ closedBall x t →
      β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖ → t⁻¹ • (y - x) ∈ C := by
    intro t ht y hyB hyβ
    have hti : 0 ≤ t⁻¹ := inv_nonneg.2 ht.le
    have hyx : ‖y - x‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hyB
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg hti]
      calc t⁻¹ * ‖y - x‖ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hyx hti
        _ = 1 := inv_mul_cancel₀ ht.ne'
    · rw [hp_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hti]
      calc β * (t⁻¹ * ‖y - x‖) = t⁻¹ * (β * ‖y - x‖) := by ring
        _ ≤ t⁻¹ * ‖(y - x) - Grassmannian.project T (y - x)‖ :=
          mul_le_mul_of_nonneg_left hyβ hti
  -- Step 3: `C ∩ T ⊆ {0} = T ∩ B_0(0)`, which is `H^n`-null since `n ≥ 1`; so `ν C = 0`.
  have hνC : ν C = 0 := by
    rw [hν, Measure.restrict_apply hC_closed.measurableSet]
    refine measure_mono_null (t := (T.plane : Set (Euclidean N)) ∩ closedBall 0 0) ?_ ?_
    · rintro w ⟨hwC, hwT⟩
      have hpw : Grassmannian.project T w = w := T.projectionLinearMap_apply_of_mem hwT
      have h0 : β * ‖w‖ ≤ β * 0 := by
        have := hwC.2
        rwa [hpw, sub_self, norm_zero, ← mul_zero β] at this
      refine ⟨hwT, mem_closedBall.2 ?_⟩
      rw [dist_zero_right]
      exact le_of_mul_le_mul_left h0 hβ
    · rw [hplane 0 le_rfl, ENNReal.ofReal_zero, zero_pow hn.ne', mul_zero]
  -- Step 4: thickenings of `C` lie in `B_2(0)`, which has finite `ν`-measure; choose `κ ∈ (0,1]`
  -- with `ν (cthickening κ C) < e / θ`.
  have hthick : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → cthickening r C ⊆ closedBall 0 2 := by
    intro r hr0 hr1
    calc cthickening r C ⊆ cthickening r (closedBall (0 : Euclidean N) 1) :=
          cthickening_subset_of_subset r hC_ball
      _ = closedBall 0 (r + 1) := cthickening_closedBall hr0 zero_le_one 0
      _ ⊆ closedBall 0 2 := closedBall_subset_closedBall (by linarith)
  have hν2 : ν (closedBall 0 2) ≠ ∞ := by
    rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane 2 zero_le_two]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hν1 : ν (cthickening 1 C) ≠ ∞ :=
    ne_top_of_le_ne_top hν2 (measure_mono (hthick 1 zero_le_one le_rfl))
  have htend : Tendsto (fun r ↦ ν (cthickening r C)) (𝓝 0) (𝓝 0) := by
    rw [← hνC]
    exact tendsto_measure_cthickening_of_isClosed ⟨1, one_pos, hν1⟩ hC_closed
  have heθ : 0 < e / θ := div_pos he hθ
  obtain ⟨δ, hδ, hδν⟩ :=
    Metric.eventually_nhds_iff.1 (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 heθ)))
  set κ : ℝ := min (δ / 2) 1
  have hκ0 : 0 < κ := lt_min (half_pos hδ) one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκν : ν (cthickening κ C) < ENNReal.ofReal (e / θ) := by
    refine hδν ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hκ0]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hκfin : ν (cthickening κ C) ≠ ∞ := (hκν.trans ENNReal.ofReal_lt_top).ne
  have hκreal : (ν (cthickening κ C)).toReal < e / θ := by
    have := (ENNReal.toReal_lt_toReal hκfin ENNReal.ofReal_ne_top).2 hκν
    rwa [ENNReal.toReal_ofReal heθ.le] at this
  -- Step 5: the cut-off `g = max(0, 1 - dist(·, C)/κ)`: continuous, `0 ≤ g ≤ 1`, `g = 1` on `C`,
  -- `g = 0` off `cthickening κ C ⊆ B_2(0)`; hence `g ∈ C_c(ℝ^N)`.
  set g₀ : Euclidean N → ℝ := fun v ↦ max 0 (1 - infDist v C / κ)
  have hg₀_cont : Continuous g₀ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt C).div_const κ))
  have hg₀_nonneg : ∀ v, 0 ≤ g₀ v := fun v ↦ le_max_left _ _
  have hg₀_le_one : ∀ v, g₀ v ≤ 1 := fun v ↦
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hκ0.le))
  have hg₀_one : ∀ v ∈ C, g₀ v = 1 := fun v hv ↦ by
    simp only [g₀, infDist_zero_of_mem hv, zero_div, sub_zero]
    exact max_eq_right zero_le_one
  have hg₀_zero : ∀ v, v ∉ cthickening κ C → g₀ v = 0 := by
    intro v hv
    have hge : κ ≤ infDist v C := by
      by_contra hlt
      obtain ⟨w, hwC, hvw⟩ := (infDist_lt_iff ⟨0, hC0⟩).1 (not_le.1 hlt)
      exact hv (mem_cthickening_of_dist_le v w κ C hwC hvw.le)
    refine max_eq_left ?_
    rw [sub_nonpos, le_div_iff₀ hκ0, one_mul]
    exact hge
  have hg₀_supp : HasCompactSupport g₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) 2) fun v hv ↦
      hg₀_zero v fun h ↦ hv (hthick κ hκ0.le hκ1 h)
  let g : C_c(Euclidean N, ℝ) := ⟨⟨g₀, hg₀_cont⟩, hg₀_supp⟩
  -- Step 6: `θ ∫_T g dH^n ≤ θ ν(cthickening κ C) < e`, so eventually the blow-ups are `< e`.
  have hint_le : ∫ v, g v ∂ν ≤ (ν (cthickening κ C)).toReal := by
    have hmeas : MeasurableSet (cthickening κ C) := isClosed_cthickening.measurableSet
    calc ∫ v, g v ∂ν ≤ ∫ v, (cthickening κ C).indicator (fun _ ↦ (1 : ℝ)) v ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun v ↦ hg₀_nonneg v)
            ((integrable_indicator_iff hmeas).2 (integrableOn_const hκfin))
            (ae_of_all _ fun v ↦ ?_)
          by_cases hv : v ∈ cthickening κ C
          · rw [indicator_of_mem hv]
            exact hg₀_le_one v
          · rw [indicator_of_notMem hv]
            exact (hg₀_zero v hv).le
      _ = (ν (cthickening κ C)).toReal := by
          rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one, measureReal_def]
  have hℓ : θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂(μHE[n] : Measure (Euclidean N)) < e :=
    calc θ * ∫ v, g v ∂ν ≤ θ * (ν (cthickening κ C)).toReal :=
          mul_le_mul_of_nonneg_left hint_le hθ.le
      _ < θ * (e / θ) := mul_lt_mul_of_pos_left hκreal hθ
      _ = e := by field_simp
  have hev := (hblow g).eventually (gt_mem_nhds hℓ)
  -- Step 7: `B_{R/2}(x)` is a compact subset of `U`, so it has finite `μ_V`-measure.
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hxU
  have hμR : V.weight (closedBall x (R / 2)) ≠ ∞ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x _)
      ((closedBall_subset_ball (half_lt_self hR)).trans hRU)
  -- Step 8: for `0 < t ≤ R/4` with blow-up `< e`, compare the cone section `S` with the
  -- rescaled cut-off `k y = g(t⁻¹ • (y - x))`.
  filter_upwards [hev, Ioc_mem_nhdsGT (by positivity : (0 : ℝ) < R / 4)] with t hFt ht
  obtain ⟨ht0, htR⟩ := ht
  set S : Set (Euclidean N) :=
    {y | y ∈ closedBall x t ∧ β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖}
  set k : Euclidean N → ℝ := fun y ↦ g₀ (t⁻¹ • (y - x))
  have hk_cont : Continuous k := hg₀_cont.comp (by fun_prop)
  -- (a) `k` vanishes off `B_{R/2}(x)`.
  have hk_supp : Function.support k ⊆ closedBall x (R / 2) := by
    intro y hy
    have hmem : t⁻¹ • (y - x) ∈ cthickening κ C := by
      by_contra hn'
      exact hy (hg₀_zero _ hn')
    have hnorm : ‖t⁻¹ • (y - x)‖ ≤ 2 := by
      simpa using hthick κ hκ0.le hκ1 hmem
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_le_iff₀ ht0] at hnorm
    rw [mem_closedBall, dist_eq_norm]
    linarith
  -- (b) `k` is `μ_V`-integrable.
  have hk_int : Integrable k V.weight := by
    refine (integrableOn_iff_integrable_of_support_subset hk_supp).1 ?_
    refine Measure.integrableOn_of_bounded (M := 1) hμR hk_cont.aestronglyMeasurable
      (ae_of_all _ fun y ↦ ?_)
    rw [Real.norm_of_nonneg (hg₀_nonneg _)]
    exact hg₀_le_one _
  -- (c) `1_S ≤ k`, so `μ_V(S) ≤ ∫ k dμ_V`.
  have hS_meas : MeasurableSet S :=
    (isClosed_closedBall.inter (isClosed_le (continuous_const.mul (continuous_id.sub
      continuous_const).norm) ((continuous_id.sub continuous_const).sub
        (hp_cont.comp (continuous_id.sub continuous_const))).norm)).measurableSet
  have hmass : V.weight S ≤ ENNReal.ofReal (∫ y, k y ∂V.weight) := by
    rw [← lintegral_indicator_one hS_meas,
      ofReal_integral_eq_lintegral_ofReal hk_int (ae_of_all _ fun y ↦ hg₀_nonneg _)]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ S
    · have hky : k y = 1 := hg₀_one _ (hC_scale t ht0 y hy.1 hy.2)
      rw [indicator_of_mem hy, Pi.one_apply, hky, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hy]
      exact zero_le
  -- Step 9: `μ_V(S) ≤ ∫ k dμ_V = t^n · (t⁻¹^n ∫ k dμ_V) ≤ t^n e`.
  have hFt' : t⁻¹ ^ n * ∫ y, k y ∂V.weight < e := hFt
  have hI : ∫ y, k y ∂V.weight ≤ t ^ n * e := by
    have htn : ∫ y, k y ∂V.weight = t ^ n * (t⁻¹ ^ n * ∫ y, k y ∂V.weight) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht0.ne', one_pow, one_mul]
    rw [htn]
    exact mul_le_mul_of_nonneg_left hFt'.le (pow_nonneg ht0.le n)
  refine hmass.trans ((ENNReal.ofReal_le_ofReal hI).trans_eq ?_)
  rw [ENNReal.ofReal_mul (pow_nonneg ht0.le n), ENNReal.ofReal_pow ht0.le, mul_comm]

/-- **Dimension `0`: tangent points are atoms of `μ_V`** (child `dim_zero_countable` of
`tangent_graph_cover`, step 2 of its proof).  If the `0`-varifold `V` has a tangent plane with
multiplicity `θ` at `x`, then for `0 < c < θ ω_0` the lower mass bound gives `c ≤ μ_V(B_t(x))` for
all small `t > 0`; `μ_V` is finite on a small closed ball about `x ∈ U`, and `B_t(x) ↓ {x}` as
`t ↓ 0`, so `μ_V({x}) ≥ c > 0`.  The σ-finite measure `μ_V` has only countably many atoms. -/
theorem Submission.tgc_dim_zero_tangent_points_countable :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (V : Varifold N 0 U),
      {x : Euclidean N | ∃ (T : Grassmannian N 0) (θ : ℝ), HasTangentPlane V x T θ}.Countable := by
  intro N U V
  -- Step 1: the atoms `{y | 0 < μ_V({y})}` of the σ-finite measure `μ_V` form a countable set.
  refine (Measure.countable_meas_pos_of_disjoint_iUnion (μ := V.weight)
    (As := fun y : Euclidean N ↦ ({y} : Set (Euclidean N))) (fun y ↦ measurableSet_singleton y)
    fun y z hyz ↦ Set.disjoint_singleton.2 hyz).mono ?_
  rintro x ⟨T, θ, hx⟩
  show 0 < V.weight {x}
  -- Step 2: for `0 < c < θ ω_0`, the lower mass bound with `n = 0` gives `c ≤ μ_V(B_t(x))` for all
  -- small `t > 0`.
  have hω : unitBallVolume 0 ≠ 0 :=
    (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 0))) 0 one_pos).ne'
  obtain ⟨c, hc0, hc⟩ := exists_between (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hx.2.1).ne' hω)
  have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ), c ≤ V.weight (closedBall x t) := by
    filter_upwards [Submission.tgc_tangent_weight_lower_bound N 0 U V x T θ hx c hc] with t ht
    rwa [pow_zero, mul_one] at ht
  -- Step 3: `x ∈ U` with `U` open, so a small closed ball about `x` is a compact subset of `U` and
  -- has finite mass.
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hx.1
  have hfin : ∃ r > 0, V.weight (cthickening r {x}) ≠ ∞ := by
    refine ⟨R / 2, half_pos hR, ?_⟩
    rw [cthickening_singleton x (half_pos hR).le]
    exact V.weight_finite_on_compact _ (isCompact_closedBall x _)
      ((closedBall_subset_ball (half_lt_self hR)).trans hRU)
  -- Step 4: continuity from above, `μ_V(B_t(x)) → μ_V({x})` as `t ↓ 0`, so `c ≤ μ_V({x})`.
  have hlim : Tendsto (fun t : ℝ ↦ V.weight (closedBall x t)) (𝓝[>] 0) (𝓝 (V.weight {x})) := by
    refine ((tendsto_measure_cthickening_of_isClosed hfin isClosed_singleton).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [cthickening_singleton x (mem_Ioi.1 ht).le]
  exact hc0.trans_le (ge_of_tendsto hlim hlow)

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
