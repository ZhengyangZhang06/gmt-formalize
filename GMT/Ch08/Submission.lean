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

/-- Cylinder grouping (Simon Ch. 8, proof of 5.10 (8), steps (b)–(d)): for a `d`-separated finite
set `s` in one fibre of `p = Grassmannian.project P`, the cylinders `U^{d/2}_ρ(y)`, `y ∈ s`, are
disjoint and lie in the enlarged cylinders `U^{d/2+S}_{ρ+S}(z)` about representatives `z ∈ Z`
within distance `S`; hence the `ρ^{-n}`-normalized sum over `s` is at most `1 + (2^n - 1) u` times
the `(ρ + S)^{-n}`-normalized sum over `Z`, when `S ≤ u ρ` and `u ≤ 1`. -/
theorem Submission.intcpt_allard_ccb_cylinder_grouping :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s Z : Finset (Euclidean N)) (d ρ S u : ℝ), (∀ y ∈ s, Grassmannian.project P y = x) → Z ⊆ s → 0 < d → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖) → 0 < ρ → 0 ≤ S → S ≤ u * ρ → u ≤ 1 → (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) → ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) / ENNReal.ofReal ρ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * u) * ∑ y ∈ Z, μ (closedBall y (ρ + S) ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2 + S}) / ENNReal.ofReal (ρ + S) ^ n := by
  intro N n μ P x s Z d ρ S u hpx hZs hd hsep hρ hS hSu hu1 hcov
  classical
  -- Step 0: `p = Grassmannian.project P` is linear and continuous, and `p (y - y') = 0` on `s`.
  have hsub : ∀ a b : Euclidean N,
      Grassmannian.project P (a - b) = Grassmannian.project P a - Grassmannian.project P b :=
    fun a b ↦ map_sub (Grassmannian.projectionLinearMap P) a b
  have hadd : ∀ a b : Euclidean N,
      Grassmannian.project P (a + b) = Grassmannian.project P a + Grassmannian.project P b :=
    fun a b ↦ map_add (Grassmannian.projectionLinearMap P) a b
  have hcont : Continuous (Grassmannian.project P) :=
    (Grassmannian.projectionLinearMap P).continuous_of_finiteDimensional
  have hfibre : ∀ y ∈ s, ∀ y' ∈ s, Grassmannian.project P (y - y') = 0 := fun y hy y' hy' ↦ by
    rw [hsub, hpx y hy, hpx y' hy', sub_self]
  have hu0 : 0 ≤ u := by nlinarith
  -- Step 1: representatives `r y ∈ Z` with `‖y - r y‖ ≤ S`.
  choose! r hrZ hrS using hcov
  -- Steps 2–5: the disjoint Borel cylinders about the fibre `{y ∈ s | r y = w}` lie in the
  -- enlarged cylinder about `w`.
  have hfib : ∀ w ∈ Z, ∑ y ∈ s with r y = w,
      μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) ≤
        μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) := by
    intro w hw
    rw [← measure_biUnion_finset]
    · -- Step 4: inclusion, by the triangle inequality and `q (z - r y) = q (z - y) + (y - r y)`.
      refine measure_mono (iUnion₂_subset fun y hy z hz ↦ ?_)
      obtain ⟨hys, rfl⟩ := Finset.mem_filter.1 hy
      have hws : r y ∈ s := hZs (hrZ y hys)
      obtain ⟨hzball, hzcyl⟩ := hz
      rw [mem_closedBall, dist_eq_norm] at hzball
      have hq : (z - r y) - Grassmannian.project P (z - r y) =
          ((z - y) - Grassmannian.project P (z - y)) + (y - r y) := by
        have h1 : z - r y = (z - y) + (y - r y) := by abel
        rw [h1, hadd, hfibre y hys (r y) hws, add_zero]
        abel
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm]
        calc ‖z - r y‖ = ‖(z - y) + (y - r y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖y - r y‖ := norm_add_le _ _
          _ ≤ ρ + S := add_le_add hzball (hrS y hys)
      · show ‖(z - r y) - Grassmannian.project P (z - r y)‖ < d / 2 + S
        rw [hq]
        calc _ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ + ‖y - r y‖ := norm_add_le _ _
          _ < d / 2 + S := add_lt_add_of_lt_of_le hzcyl (hrS y hys)
    · -- Step 3: disjointness, as `y - y' = q (z - y') - q (z - y)` would have norm `< d`.
      intro y hy y' hy' hne
      have hys : y ∈ s := (Finset.mem_filter.1 hy).1
      have hy's : y' ∈ s := (Finset.mem_filter.1 hy').1
      refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
      have h1 : ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2 := hz.2
      have h2 : ‖(z - y') - Grassmannian.project P (z - y')‖ < d / 2 := hz'.2
      have hkey : y - y' = ((z - y') - Grassmannian.project P (z - y')) -
          ((z - y) - Grassmannian.project P (z - y)) := by
        have h3 : Grassmannian.project P (z - y') - Grassmannian.project P (z - y) =
            Grassmannian.project P (y - y') := by
          rw [← hsub]
          congr 1
          abel
        rw [hfibre y hys y' hy's, sub_eq_zero] at h3
        rw [h3]
        abel
      have h4 : ‖y - y'‖ < d := by
        rw [hkey]
        calc _ ≤ ‖(z - y') - Grassmannian.project P (z - y')‖ +
              ‖(z - y) - Grassmannian.project P (z - y)‖ := norm_sub_le _ _
          _ < d / 2 + d / 2 := add_lt_add h2 h1
          _ = d := add_halves d
      linarith [hsep y hys y' hy's hne]
    · -- Step 2: each cylinder is a closed ball intersected with an open set.
      intro y _
      refine measurableSet_closedBall.inter (IsOpen.measurableSet ?_)
      exact isOpen_lt (by fun_prop) continuous_const
  -- Step 6: `(1 + u)^k ≤ 1 + (2^k - 1) u` for `0 ≤ u ≤ 1`.
  have hF1 : ∀ k : ℕ, (1 + u) ^ k ≤ 1 + (2 ^ k - 1) * u := by
    intro k
/-- One-point bound from monotonicity (Simon Ch. 8, 5.10, proof of (8), one point): if
`‖y - x‖ < ε ≤ δ⁴`, `0 < δ ≤ 1/2`, `0 < σ ≤ δ²` and `r ↦ e^{εr} μ(B_r(y)) / r^n` is non-decreasing
on `(0,1)`, then `μ(B_σ(y)) / σ^n ≤ (1 + 2^{n+2} δ²) μ(B_1(x))`. -/
theorem Submission.intcpt_allard_ccb_one_point_ball_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (δ ε σ : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * μ (closedBall y r) / ENNReal.ofReal r ^ n) (Ioo 0 1) → 0 < σ → σ ≤ δ ^ 2 → μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1) := by
  intro N n μ x y δ ε σ hδ hδ2 hε hεδ hyx hmono hσ hσδ
  -- Step 1: `ε ≤ δ⁴ ≤ δ² ≤ 1/4`, so `σ, 1 - ε ∈ (0,1)` and `σ ≤ 1 - ε`.
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
  have hεδ2 : ε ≤ δ ^ 2 := hεδ.trans hδ4
  have hε4 : ε ≤ 1 / 4 := hεδ2.trans hδsq
  have hσ1 : σ < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have h1ε1 : 1 - ε < 1 := by linarith
  have hσle : σ ≤ 1 - ε := by linarith
  -- Step 2: monotonicity `f(σ) ≤ f(1 - ε)`.
  have hf : ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤
      ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
        ENNReal.ofReal (1 - ε) ^ n :=
    hmono ⟨hσ, hσ1⟩ ⟨h1ε, h1ε1⟩ hσle
  -- Step 3: `e^{εσ} ≥ 1`, so `μ(B_σ(y)) / σ^n ≤ f(σ)`.
  have hlow : μ (closedBall y σ) / ENNReal.ofReal σ ^ n ≤
      ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n := by
    refine ENNReal.div_le_div_right ?_ _
    calc μ (closedBall y σ) = 1 * μ (closedBall y σ) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) :=
        mul_le_mul' (ENNReal.one_le_ofReal.2 (Real.one_le_exp (by positivity))) le_rfl
  -- Step 4: `B_{1-ε}(y) ⊆ B_1(x)` and `e^{ε(1-ε)} ≤ e^ε`.
  have hball : closedBall y (1 - ε) ⊆ closedBall x 1 := by
    apply closedBall_subset_closedBall'
    rw [dist_eq_norm]
    linarith
  have hexp : ENNReal.ofReal (Real.exp (ε * (1 - ε))) ≤ ENNReal.ofReal (Real.exp ε) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have hup : ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
        ENNReal.ofReal (1 - ε) ^ n ≤
      ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n :=
    ENNReal.div_le_div_right (mul_le_mul' hexp (measure_mono hball)) _
  -- Step 5: `ofReal(e^ε) μ(B_1(x)) / ofReal(1 - ε)^n = ofReal(e^ε / (1 - ε)^n) μ(B_1(x))`.
  have hrw : ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n =
      ENNReal.ofReal (Real.exp ε / (1 - ε) ^ n) * μ (closedBall x 1) := by
    rw [ENNReal.mul_div_right_comm, ← ENNReal.ofReal_pow h1ε.le,
      ← ENNReal.ofReal_div_of_pos (pow_pos h1ε n)]
  -- Step 6: the real inequality `e^ε / (1 - ε)^n ≤ 1 + 2^{n+2} δ²`.
  -- (F1) `(1 + u)^k ≤ 1 + (2^k - 1) u` for `0 ≤ u ≤ 1`, by induction on `k`.
  have hF1 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ k : ℕ, (1 + u) ^ k ≤ 1 + (2 ^ k - 1) * u := by
    intro u hu0 hu1 k
    induction k with
    | zero => simp
    | succ k ih =>
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      calc (1 + u) ^ (k + 1) = (1 + u) ^ k * (1 + u) := pow_succ _ _
        _ ≤ (1 + (2 ^ k - 1) * u) * (1 + u) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + (2 ^ (k + 1) - 1) * u := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h2k) hu0) (sub_nonneg.2 hu1)]
  -- Step 7: rescaling, `X / ρ^n ≤ κ (X / (ρ + S)^n)` with `κ = ofReal (1 + (2^n - 1) u)`.
  have hk1 : (1 : ℝ) ≤ 1 + (2 ^ n - 1) * u := by
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hreal : (ρ + S) ^ n ≤ (1 + (2 ^ n - 1) * u) * ρ ^ n := by
    calc (ρ + S) ^ n ≤ ((1 + u) * ρ) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (1 + u) ^ n * ρ ^ n := mul_pow _ _ _
      _ ≤ (1 + (2 ^ n - 1) * u) * ρ ^ n :=
          mul_le_mul_of_nonneg_right (hF1 n) (pow_nonneg hρ.le n)
  have hκ : ENNReal.ofReal (ρ + S) ^ n ≤
      ENNReal.ofReal (1 + (2 ^ n - 1) * u) * ENNReal.ofReal ρ ^ n := by
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hκ0 : ENNReal.ofReal (1 + (2 ^ n - 1) * u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hresc : ∀ X : ℝ≥0∞, X / ENNReal.ofReal ρ ^ n ≤
      ENNReal.ofReal (1 + (2 ^ n - 1) * u) * (X / ENNReal.ofReal (ρ + S) ^ n) := by
    intro X
    rw [← ENNReal.mul_div_mul_left X (ENNReal.ofReal ρ ^ n) hκ0 ENNReal.ofReal_ne_top,
      ← mul_div_assoc]
    exact ENNReal.div_le_div_left hκ _
  -- Step 8: group the sum over `s` by representatives, then rescale.
  calc ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
        ENNReal.ofReal ρ ^ n
      = ∑ w ∈ Z, ∑ y ∈ s with r y = w,
          μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
            ENNReal.ofReal ρ ^ n :=
        (Finset.sum_fiberwise_of_maps_to hrZ _).symm
    _ = ∑ w ∈ Z, (∑ y ∈ s with r y = w,
          μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2})) /
            ENNReal.ofReal ρ ^ n := by
        simp_rw [ENNReal.sum_div]
    _ ≤ ∑ w ∈ Z, μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) / ENNReal.ofReal ρ ^ n :=
        Finset.sum_le_sum fun w hw ↦ ENNReal.div_le_div_right (hfib w hw) _
    _ ≤ ∑ w ∈ Z, ENNReal.ofReal (1 + (2 ^ n - 1) * u) * (μ (closedBall w (ρ + S) ∩
          {z | ‖(z - w) - Grassmannian.project P (z - w)‖ < d / 2 + S}) /
            ENNReal.ofReal (ρ + S) ^ n) :=
        Finset.sum_le_sum fun w _ ↦ hresc _
    _ = _ := (Finset.mul_sum _ _ _).symm
        _ = 1 + 2 ^ k * u + (2 ^ k - 1) * u ^ 2 := by ring
        _ ≤ 1 + 2 ^ k * u + (2 ^ k - 1) * u := by
          have hu2 : u ^ 2 ≤ u := by nlinarith
          have := mul_le_mul_of_nonneg_left hu2 (sub_nonneg.2 h2k)
          linarith
        _ = 1 + (2 ^ (k + 1) - 1) * u := by ring
  -- (F2) `e^ε ≤ 1 / (1 - ε) ≤ 1 + 2ε`.
  have hinv : 1 / (1 - ε) ≤ 1 + 2 * ε := by
    rw [div_le_iff₀ h1ε]
    nlinarith
  have hF2 : Real.exp ε ≤ 1 + 2 * ε :=
    (Real.exp_bound_div_one_sub_of_interval hε.le (by linarith)).trans hinv
  have hpow : 1 / (1 - ε) ^ n ≤ 1 + (2 ^ n - 1) * (2 * ε) := by
    calc 1 / (1 - ε) ^ n = (1 / (1 - ε)) ^ n := (one_div_pow _ _).symm
      _ ≤ (1 + 2 * ε) ^ n := pow_le_pow_left₀ (one_div_nonneg.2 h1ε.le) hinv n
      _ ≤ 1 + (2 ^ n - 1) * (2 * ε) := hF1 (2 * ε) (by linarith) (by linarith) n
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hreal : Real.exp ε / (1 - ε) ^ n ≤ 1 + 2 ^ (n + 2) * δ ^ 2 := by
    calc Real.exp ε / (1 - ε) ^ n = Real.exp ε * (1 / (1 - ε) ^ n) := (mul_one_div _ _).symm
      _ ≤ (1 + 2 * ε) * (1 + (2 ^ n - 1) * (2 * ε)) :=
        mul_le_mul hF2 hpow (one_div_nonneg.2 (pow_nonneg h1ε.le n)) (by linarith)
      _ = 1 + 2 ^ n * (2 * ε) + (2 ^ n - 1) * (4 * ε ^ 2) := by ring
      _ ≤ 1 + 2 ^ n * (2 * ε) + 2 ^ n * (4 * ε ^ 2) := by
        have := mul_le_mul_of_nonneg_right (sub_le_self (2 ^ n : ℝ) zero_le_one)
          (by positivity : (0 : ℝ) ≤ 4 * ε ^ 2)
        linarith
      _ ≤ 1 + 2 ^ n * (2 * ε) + 2 ^ n * (2 * ε) := by
        have h4 : 4 * ε ^ 2 ≤ 2 * ε := by nlinarith
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 ^ n)
        linarith
      _ = 1 + 2 ^ (n + 2) * ε := by ring
      _ ≤ 1 + 2 ^ (n + 2) * δ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hεδ2 (by positivity : (0 : ℝ) ≤ 2 ^ (n + 2))
        linarith
  -- Step 7: chain the estimates.
  calc μ (closedBall y σ) / ENNReal.ofReal σ ^ n
      ≤ ENNReal.ofReal (Real.exp (ε * σ)) * μ (closedBall y σ) / ENNReal.ofReal σ ^ n := hlow
    _ ≤ ENNReal.ofReal (Real.exp (ε * (1 - ε))) * μ (closedBall y (1 - ε)) /
          ENNReal.ofReal (1 - ε) ^ n := hf
    _ ≤ ENNReal.ofReal (Real.exp ε) * μ (closedBall x 1) / ENNReal.ofReal (1 - ε) ^ n := hup
    _ = ENNReal.ofReal (Real.exp ε / (1 - ε) ^ n) * μ (closedBall x 1) := hrw
    _ ≤ ENNReal.ofReal (1 + 2 ^ (n + 2) * δ ^ 2) * μ (closedBall x 1) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- Reduction step (Simon Ch. 8, proof of 5.10 (8), inductive step for `#s ≥ 2`): let `s` be a
`4τ`-separated set of `2 ≤ #s ≤ m + 1` points in one fibre of `p = Grassmannian.project P`, each
within `ε` of that plane and satisfying the comparison (C_y).  Cluster selection (CS) at the minimal
distance `d` of `s` gives `Z ⊆ s` with `#Z ≤ m` and admissible scales `σ' = ρ + S`, `τ' = d/2 + S`
(`ρ = d/(4δ²)`) such that the `σ^{-n}`-normalized cylinder sum over `s` is at most
`1 + (2^n - 1) a δ²` times the `σ'^{-n}`-normalized sum over `Z`, plus `(m + 1) K δ²`, where
`a = 4 (10 (m + 1))^{m + 1}`. -/
theorem Submission.intcpt_allard_ccb_reduction_step :
    ∀ (N n : ℕ) (K : ℝ) (m : ℕ), (∀ (t : Finset (Euclidean N)) (d : ℝ), 2 ≤ t.card → 0 < d → (∀ y ∈ t, ∀ y' ∈ t, y ≠ y' → d ≤ ‖y - y'‖) → (∃ y ∈ t, ∃ y' ∈ t, y ≠ y' ∧ ‖y - y'‖ ≤ d) → ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ t ∧ Z.card < t.card ∧ 0 ≤ S ∧ S ≤ (10 * (t.card : ℝ)) ^ t.card * d ∧ (∀ y ∈ t, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖) → 0 ≤ K → ∀ δ ε : ℝ, 0 < δ → δ ≤ 1 / (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) → 0 < ε → ε ≤ δ ^ 4 → ∀ (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)), 2 ≤ s.card → s.card ≤ m + 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ ‖y - Grassmannian.project P y‖ < ε ∧ ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∃ (Z : Finset (Euclidean N)) (σ' τ' : ℝ), Z ⊆ s ∧ Z.card ≤ m ∧ 0 < σ' ∧ σ' ≤ δ ^ 2 ∧ 2 * δ ^ 2 * σ' ≤ τ' ∧ (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 4 * τ' ≤ ‖z - z'‖) ∧ ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) * δ ^ 2) * ∑ y ∈ Z, μ (closedBall y σ' ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ'}) / ENNReal.ofReal σ' ^ n + ENNReal.ofReal (((m : ℝ) + 1) * K * δ ^ 2) := by
  intro N n K m hCS hK δ ε hδ hδa hε hεδ μ P x s hs2 hsm hy σ τ hσ hσδ hστ hsep
  classical
  -- Step 0: elementary bounds, with `a = 4 (10 (m + 1))^{m + 1} ≥ 40` and `u = a δ² ≤ 1`.
  set a : ℝ := 4 * (10 * ((m : ℝ) + 1)) ^ (m + 1) with ha_def
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ 10 * ((m : ℝ) + 1) := by linarith
  have hpow : 10 * ((m : ℝ) + 1) ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) := by
    calc 10 * ((m : ℝ) + 1) = (10 * ((m : ℝ) + 1)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hm1 (by omega)
  have ha40 : 40 ≤ a := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have haδ : a * δ ≤ 1 := by
    rw [le_div_iff₀ ha0] at hδa
    linarith [mul_comm a δ]
  have h40δ : 40 * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha40 hδ.le
    linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hδ2le : δ ^ 2 ≤ δ := by rw [sq]; exact mul_le_of_le_one_left hδ.le hδ1
  have h2δ2 : 2 * δ ^ 2 ≤ 1 := by linarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by
    have : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left hδ2pos.le (hδ2le.trans hδ1)
  have hu1 : a * δ ^ 2 ≤ 1 := by
    have : a * δ ^ 2 = (a * δ) * δ := by ring
    rw [this]
    calc (a * δ) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right haδ hδ.le
      _ ≤ 1 := by linarith
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hστ
  have hyx : ∀ y ∈ s, ‖y - x‖ < ε := fun y hys ↦ by
    have h := hy y hys
    rw [← h.1]; exact h.2.1
  -- Step 1: the minimal distance `d` of `s`, attained at a pair `q`; `4τ ≤ d < 2ε`.
  have hne : s.offDiag.Nonempty := by
    obtain ⟨y, hys, y', hy's, hyy'⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    exact ⟨(y, y'), Finset.mem_offDiag.2 ⟨hys, hy's, hyy'⟩⟩
  obtain ⟨q, hq, hqmin⟩ := Finset.exists_min_image s.offDiag (fun q ↦ ‖q.1 - q.2‖) hne
  obtain ⟨hq1, hq2, hq12⟩ := Finset.mem_offDiag.1 hq
  set d : ℝ := ‖q.1 - q.2‖ with hd_def
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hq12)
  have hdmin : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖ := fun y hys y' hy's hyy' ↦
    hqmin (y, y') (Finset.mem_offDiag.2 ⟨hys, hy's, hyy'⟩)
  have hd2ε : d < 2 * ε := by
    have h1 := hyx q.1 hq1
    have h2 := hyx q.2 hq2
    calc d = ‖(q.1 - x) - (q.2 - x)‖ := by rw [hd_def]; congr 1; abel
      _ ≤ ‖q.1 - x‖ + ‖q.2 - x‖ := norm_sub_le _ _
      _ < 2 * ε := by linarith
  have h4τd : 4 * τ ≤ d := hsep q.1 hq1 q.2 hq2 hq12
  -- Step 2: the scale `ρ = d / (4δ²)`, with `σ ≤ ρ < δ²/2 < 1` and `0 < d/4 ≤ 1`.
  set ρ : ℝ := d / (4 * δ ^ 2) with hρ_def
  have hρ0 : 0 < ρ := by positivity
  have hdρ : d = 4 * δ ^ 2 * ρ := by
    rw [hρ_def]; field_simp
  have hσρ : σ ≤ ρ := by
    have h1 : δ ^ 2 * (2 * σ) ≤ δ ^ 2 * ρ := by linarith
    have h2 : 2 * σ ≤ ρ := le_of_mul_le_mul_left h1 hδ2pos
    linarith
  have hρδ : ρ < δ ^ 2 / 2 := by
    have : 4 * δ ^ 2 * ρ < 4 * δ ^ 2 * (δ ^ 2 / 2) := by
      calc 4 * δ ^ 2 * ρ = d := hdρ.symm
        _ < 2 * ε := hd2ε
        _ ≤ 2 * δ ^ 4 := by linarith
        _ = 4 * δ ^ 2 * (δ ^ 2 / 2) := by ring
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hρ1 : ρ < 1 := by linarith
  have hd4pos : 0 < d / 4 := by positivity
  have hd4le : d / 4 ≤ 1 := by linarith
  -- Step 3: (C_y) at `(d/4, σ, ρ)`, after enlarging `τ` to `d/4`; its error is at most `K δ²`.
  have hstep3 : ∀ y ∈ s,
      μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
          ENNReal.ofReal σ ^ n ≤
        μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * δ ^ 2) := by
    intro y hys
    have hC := (hy y hys).2.2 (d / 4) σ ρ hd4pos hd4le hσ hσρ hρ1
    have h2 : 2 * (d / 4) = d / 2 := by ring
    rw [h2] at hC
    have hsub : closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ} ⊆
        closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4} := by
      refine inter_subset_inter_right _ fun z hz ↦ ?_
      have hz' : ‖(z - y) - Grassmannian.project P (z - y)‖ < τ := hz
      show ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4
      linarith
    have herr : K * ε * ρ / (d / 4) ≤ K * δ ^ 2 := by
      rw [div_le_iff₀ hd4pos]
      have hKε : K * ε ≤ K * δ ^ 4 := mul_le_mul_of_nonneg_left hεδ hK
      have : K * δ ^ 2 * (d / 4) = K * δ ^ 4 * ρ := by rw [hdρ]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hKε hρ0.le
    calc _ ≤ μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 4}) /
          ENNReal.ofReal σ ^ n := ENNReal.div_le_div_right (measure_mono hsub) _
      _ ≤ _ := hC
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal herr)
  -- Step 4: summation over `s`, with `#s · K δ² ≤ (m + 1) K δ²`.
  have hstep4 : ∑ y ∈ s,
      μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) /
          ENNReal.ofReal σ ^ n ≤
        ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (((m : ℝ) + 1) * K * δ ^ 2) := by
    calc _ ≤ ∑ y ∈ s, (μ (closedBall y ρ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) /
          ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * δ ^ 2)) := Finset.sum_le_sum hstep3
      _ = _ + s.card • ENNReal.ofReal (K * δ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const]
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hsm
          have hKδ : 0 ≤ K * δ ^ 2 := by positivity
          calc (s.card : ℝ) * (K * δ ^ 2) ≤ ((m : ℝ) + 1) * (K * δ ^ 2) :=
                mul_le_mul_of_nonneg_right hcard hKδ
            _ = ((m : ℝ) + 1) * K * δ ^ 2 := by ring
  -- Step 5: clusters from (CS) at scale `d`, with `S ≤ (10 (m + 1))^{m + 1} d = a δ² ρ`.
  obtain ⟨Z, S, hZs, hZcard, hS0, hSd, hcov, hZsep⟩ :=
    hCS s d hs2 hd0 hdmin ⟨q.1, hq1, q.2, hq2, hq12, le_refl _⟩
  have hcardpow : (10 * (s.card : ℝ)) ^ s.card ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) := by
    have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hsm
    calc (10 * (s.card : ℝ)) ^ s.card ≤ (10 * ((m : ℝ) + 1)) ^ s.card :=
          pow_le_pow_left₀ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hm1 hsm
  have hSu : S ≤ a * δ ^ 2 * ρ := by
    calc S ≤ (10 * (s.card : ℝ)) ^ s.card * d := hSd
      _ ≤ (10 * ((m : ℝ) + 1)) ^ (m + 1) * d := mul_le_mul_of_nonneg_right hcardpow hd0.le
      _ = a * δ ^ 2 * ρ := by rw [hdρ, ha_def]; ring
  -- Step 6: grouping (the accepted sibling `cylinder_grouping`) with `u = a δ²`.
  have hpx : ∀ y ∈ s, Grassmannian.project P y = x := fun y hys ↦ (hy y hys).1
  have hgroup := Submission.intcpt_allard_ccb_cylinder_grouping N n μ P x s Z d ρ S (a * δ ^ 2)
    hpx hZs hd0 hdmin hρ0 hS0 hSu hu1 hcov
  -- Step 7: the witnesses `Z`, `σ' = ρ + S ≤ 2ρ < δ²` and `τ' = d/2 + S`.
  refine ⟨Z, ρ + S, d / 2 + S, hZs, by omega, by linarith, ?_, ?_, ?_, ?_⟩
  · have hSρ : a * δ ^ 2 * ρ ≤ ρ := mul_le_of_le_one_left hρ0.le hu1
    linarith
  · have h1 : 2 * δ ^ 2 * S ≤ S := mul_le_of_le_one_left hS0 h2δ2
    have h2 : 2 * δ ^ 2 * (ρ + S) = d / 2 + 2 * δ ^ 2 * S := by rw [hdρ]; ring
    rw [h2]
    linarith
  · intro z hz z' hz' hzz'
    have := hZsep z hz z' hz' hzz'
    linarith
  -- Step 8: chain steps 4 and 6.
  have hcoef : (1 + (2 ^ n - 1) * (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) * δ ^ 2) =
      1 + (2 ^ n - 1) * (a * δ ^ 2) := by rw [ha_def]; ring
  rw [hcoef]
  calc _ ≤ _ := hstep4
    _ ≤ _ := add_le_add hgroup le_rfl

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
