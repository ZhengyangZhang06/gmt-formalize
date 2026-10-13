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

/-- `H^n` of the balls of an `n`-plane centred on the plane (step 0(c) of the flat-limit step of
Simon Ch. 8, 5.9): for `T ∈ G(N,n)`, `a ∈ T` and `r > 0`, both `T ∩ B_r(a)` and `T ∩ B°_r(a)`
have `H^n`-measure `ω_n r^n`. -/
theorem Submission.intcpt_fli_plane_ball_measure :
    ∀ (N n : ℕ) (T : Grassmannian N n) (a : Euclidean N) (r : ℝ), a ∈ T.plane → 0 < r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall a r) = unitBallVolume n * ENNReal.ofReal r ^ n ∧ (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ ball a r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T a r ha hr
  -- Step 1: an orthonormal basis `B` of `T.plane` indexed by `Fin n` (`dim T.plane = n`) gives a
  -- linear isometry `L : ℝ^n → ℝ^N` with values in `T.plane` and `L (B.repr v) = v`.
  let B : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr (Grassmannian.finrank_plane T))
  let L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp B.repr.symm.toLinearIsometry
  have hLrepr : ∀ v : T.plane, L (B.repr v) = v := fun v ↦ by simp [L]
  -- Step 2: `ι x = a + L x` is an isometry with `ι 0 = a`.
  let ι : EuclideanSpace ℝ (Fin n) → Euclidean N := fun x ↦ a + L x
  have hι : Isometry ι := Isometry.of_dist_eq fun x y ↦ by
    simp only [ι, dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub, L.norm_map]
  have hι0 : ι 0 = a := by simp [ι]
  -- Step 3: `ι` maps onto `T.plane` (`y = ι (B.repr (y - a))` for `y ∈ T.plane`), so it maps
  -- `B_r(0) = ι⁻¹(B_r(a))` onto `T.plane ∩ B_r(a)`, and likewise for open balls.
  have hrange : range ι = (T.plane : Set (Euclidean N)) := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨B.repr ⟨y - a, T.plane.sub_mem hy ha⟩, by simp [ι, hLrepr]⟩⟩
    rintro ⟨x, rfl⟩
    exact T.plane.add_mem ha (B.repr.symm x).2
  -- Step 4: `μHE[n]` is isometry invariant and equals `volume` on `ℝ^n`.
  have hvol : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      (μHE[n] : Measure (Euclidean N)) (ι '' S) = volume S := fun S ↦ by
    rw [hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Steps 5–6: Haar scaling of balls in `ℝ^n` (no nontriviality is needed, so `n = 0` is
  -- included) and `ofReal (r ^ n) = (ofReal r) ^ n`.
  constructor
  · rw [← hrange, inter_comm, ← hι0, ← image_preimage_eq_inter_range, hι.preimage_closedBall,
      hvol, Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, unitBallVolume,
      ENNReal.ofReal_pow hr.le, mul_comm]
  · rw [← hrange, inter_comm, ← hι0, ← image_preimage_eq_inter_range, hι.preimage_ball, hvol,
      Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin, unitBallVolume,
      ENNReal.ofReal_pow hr.le, mul_comm]
/-- Tilt cutoffs are test functions (the cutoff `χ(z) t_P(S)` of the flat-limit step of Simon
Ch. 8, 5.9): for `P ∈ G(N,n)` and continuous compactly supported `χ` on `ℝ^N`, the function
`(z,S) ↦ χ(z) ‖p_S - p_P‖` lies in `C_c(ℝ^N × G(N,n))` and has support in `spt χ × G(N,n)`. -/
theorem Submission.intcpt_fli_tilt_cutoff_cc :
    ∀ (N n : ℕ) (P : Grassmannian N n) (χ : Euclidean N → ℝ), Continuous χ → HasCompactSupport χ → ∃ f : C_c(Euclidean N × Grassmannian N n, ℝ), (∀ (z : Euclidean N) (S : Grassmannian N n), f (z, S) = χ z * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖) ∧ tsupport f ⊆ tsupport χ ×ˢ (univ : Set (Grassmannian N n)) := by
  intro N n P χ hχ hχcs
  -- Step 1: `Φ = toContinuousLinearMap ∘ (toMatrix b b)⁻¹` is linear on the finite-dimensional
  -- matrix space, hence continuous.
  let b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  let Φ : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N) :=
    (LinearMap.toContinuousLinearMap :
      (Euclidean N →ₗ[ℝ] Euclidean N) ≃ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N)).toLinearMap ∘ₗ
      (LinearMap.toMatrix b b).symm.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  -- Step 2: `p_S = (toMatrix b b)⁻¹ S`, so by linearity
  -- `toContinuousLinearMap (p_S - p_P) = Φ (S - P)`.
  have heq : ∀ S : Grassmannian N n, LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P) = Φ (S.1 - P.1) := by
    intro S
    have h : (LinearMap.toMatrix b b).symm (S.1 - P.1) =
        Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P := by
      rw [map_sub]
      rfl
    rw [← h]
    rfl
  -- Step 3: `t_P(S) = ‖Φ (S - P)‖` is continuous in `S`.
  have ht : Continuous fun S : Grassmannian N n ↦ ‖LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ := by
    simp only [heq]
    exact (hΦ.comp (continuous_subtype_val.sub continuous_const)).norm
  -- Step 4: `F(z,S) = χ(z) t_P(S)` is continuous.
  let F : Euclidean N × Grassmannian N n → ℝ := fun z ↦ χ z.1 * ‖LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
  have hF : Continuous F := (hχ.comp continuous_fst).mul (ht.comp continuous_snd)
  -- Step 5: `support F ⊆ support χ × G ⊆ tsupport χ × G`, which is closed.
  have hFsupp : tsupport F ⊆ tsupport χ ×ˢ (univ : Set (Grassmannian N n)) := by
    refine closure_minimal (fun z hz ↦ ⟨subset_tsupport χ fun h ↦ hz ?_, mem_univ _⟩)
      ((isClosed_tsupport χ).prod isClosed_univ)
    simp only [F, h, zero_mul]
  -- Step 6: `tsupport χ × G` is compact (`G` is compact), so `F ∈ C_c(ℝ^N × G)`.
  have hFcs : HasCompactSupport F :=
    (hχcs.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFsupp
  exact ⟨⟨⟨F, hF⟩, hFcs⟩, fun z S ↦ rfl, hFsupp⟩

/-- Tangent planes at points of small tilt excess are close to `P` (Simon Ch. 8, proof of 5.9,
pp. 218–221: step 7 of the proof that flat limits of integral varifolds have integer multiplicity,
at points satisfying the tilt bound (2) of the proof of 5.10, p. 221; child `tangent_tilt_bound`
of `flat_limit_integer`).  If `W` has tangent plane `T` with multiplicity `θ ≥ 1` at `y` and
`∫_{Gₙ(B_ρ(y))} ‖p_S - p_P‖ dW(z,S) ≤ ε ρ^n` for `0 < ρ < 1`, then
`‖p_T - p_P‖ ≤ ε / ω_n`: testing the tangent-plane convergence against `χ_κ(z) ‖p_S - p_P‖`
(`tilt_cutoff`), with a cutoff `χ_κ = 1` on `B_κ(0)` and `χ_κ = 0` off `B°_1(0)`, gives
`θ ω_n κ^n ‖p_T - p_P‖ ≤ ε` (`plane_ball_measure`), and then `κ ↑ 1`. -/
theorem Submission.intcpt_fli_tangent_tilt_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P T : Grassmannian N n) (y : Euclidean N) (θ ε : ℝ), HasTangentPlane W y T θ → 1 ≤ θ → 0 ≤ ε → (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) → ∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ ε / (unitBallVolume n).toReal * ‖v‖ := by
  intro N n U W P T y θ ε hT hθ1 hε htilt v
  -- Step 1: `ω = ω_n ∈ (0, ∞)`, and `t(S) = ‖p_S - p_P‖ ≥ 0`.
  have hωne : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact (measure_ball_lt_top (μ := volume)).ne
  have hωpos : 0 < (unitBallVolume n).toReal := by
    unfold unitBallVolume
    exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne'
      (measure_ball_lt_top (μ := volume)).ne
  set ω := (unitBallVolume n).toReal
  set t : Grassmannian N n → ℝ := fun S ↦ ‖LinearMap.toContinuousLinearMap
    (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖
  have ht0 : ∀ S, 0 ≤ t S := fun S ↦ norm_nonneg _
  have h0T : (0 : Euclidean N) ∈ T.plane := T.plane.zero_mem
  have hTmeas : MeasurableSet (T.plane : Set (Euclidean N)) :=
    (Submodule.closed_of_finiteDimensional _).measurableSet
  -- Step 2: `t(T) ω κ^n ≤ ε` for every `κ ∈ (0, 1)`.
  have hκ : ∀ κ : ℝ, 0 < κ → κ < 1 → t T * (ω * κ ^ n) ≤ ε := by
    intro κ hκ0 hκ1
    -- Step 2a: `χ_κ(z) = max(0, min(1, (1 - |z|) / (1 - κ)))` is continuous, `[0, 1]`-valued,
    -- `= 1` on `B_κ(0)` and `= 0` off `B°_1(0)`; `tilt_cutoff` gives `f ∈ C_c(ℝ^N × G(N,n))`
    -- with `f(z, S) = χ_κ(z) t(S)`.
    set χ : Euclidean N → ℝ := fun z ↦ max 0 (min 1 ((1 - ‖z‖) / (1 - κ))) with hχdef
    have hκ' : 0 < 1 - κ := by linarith
    have hχcont : Continuous χ := by
      simp only [hχdef]
      fun_prop
    have hχ0 : ∀ z, 0 ≤ χ z := fun z ↦ le_max_left _ _
    have hχ1 : ∀ z, χ z ≤ 1 := fun z ↦ max_le zero_le_one (min_le_left _ _)
    have hχzero : ∀ z, 1 ≤ ‖z‖ → χ z = 0 := by
      intro z hz
      simp only [hχdef]
      apply max_eq_left
      refine (min_le_right _ _).trans ?_
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hκ'.le
    have hχone : ∀ z, ‖z‖ ≤ κ → χ z = 1 := by
      intro z hz
      simp only [hχdef]
      rw [min_eq_left, max_eq_right zero_le_one]
      rw [le_div_iff₀ hκ']
      linarith
    have hχcs : HasCompactSupport χ :=
      HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz ↦ by
        apply hχzero
        rw [mem_closedBall, dist_zero_right, not_le] at hz
        exact hz.le
    obtain ⟨f, hf, -⟩ := Submission.intcpt_fli_tilt_cutoff_cc N n P χ hχcont hχcs
    -- Steps 2b–2d: `∫ f dW_{y,ρ} ≤ ε` for every `ρ ∈ (0, 1)`.
    have hbound : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∫ z, f z ∂(rescaledMeasure W y ρ) ≤ ε := by
      intro ρ hρ0 hρ1
      -- Step 2b: `∫ f dW_{y,ρ} = ρ^{-n} ∫ h dW` with `h(z) = χ_κ(ρ^{-1}(z.1 - y)) t(z.2) ≥ 0`.
      unfold rescaledMeasure
      rw [integral_smul_measure, integral_map (μ := W.measure)
        (φ := fun z : Euclidean N × Grassmannian N n ↦ (ρ⁻¹ • (z.1 - y), z.2)) (by fun_prop)
        (map_continuous f).aestronglyMeasurable]
      set h : Euclidean N × Grassmannian N n → ℝ := fun z ↦ f (ρ⁻¹ • (z.1 - y), z.2) with hhdef
      have hh0 : ∀ z, 0 ≤ h z := by
        intro z
        simp only [hhdef, hf]
        exact mul_nonneg (hχ0 _) (ht0 _)
      -- Step 2c: `ofReal(h(z)) ≤ 1_{B_ρ(y) × G(N,n)}(z) ofReal(t(z.2))`, as `χ_κ ≤ 1` and
      -- `χ_κ(ρ^{-1}(z.1 - y)) = 0` when `|z.1 - y| > ρ`.
      have hhle : ∀ z, ENNReal.ofReal (h z) ≤
          (closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))).indicator
            (fun z ↦ ENNReal.ofReal (t z.2)) z := by
        intro z
        by_cases hz : z ∈ closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))
        · rw [indicator_of_mem hz]
          apply ENNReal.ofReal_le_ofReal
          simp only [hhdef, hf]
          exact mul_le_of_le_one_left (ht0 _) (hχ1 _)
        · rw [indicator_of_notMem hz]
          have hzy : ρ < ‖z.1 - y‖ := by
            simp only [mem_prod, mem_closedBall, mem_univ, and_true, not_le, dist_eq_norm] at hz
            exact hz
          have hχz : χ (ρ⁻¹ • (z.1 - y)) = 0 := by
            apply hχzero
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ0, inv_mul_eq_div,
              le_div_iff₀ hρ0, one_mul]
            exact hzy.le
          simp only [hhdef, hf, hχz, zero_mul, ENNReal.ofReal_zero, le_refl]
      -- Step 2d: by the tilt hypothesis `∫ h dW ≤ ε ρ^n`, so `∫ f dW_{y,ρ} ≤ ρ^{-n} ε ρ^n = ε`.
      have hlint : ∫⁻ z, ENNReal.ofReal (h z) ∂W.measure ≤ ENNReal.ofReal (ε * ρ ^ n) := by
        calc ∫⁻ z, ENNReal.ofReal (h z) ∂W.measure
            ≤ ∫⁻ z, (closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))).indicator
                (fun z ↦ ENNReal.ofReal (t z.2)) z ∂W.measure := lintegral_mono hhle
          _ = ∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)),
                ENNReal.ofReal (t z.2) ∂W.measure :=
              lintegral_indicator (measurableSet_closedBall.prod MeasurableSet.univ) _
          _ ≤ ENNReal.ofReal (ε * ρ ^ n) := htilt ρ hρ0 hρ1
      have hhcont : Continuous h := f.continuous.comp (by fun_prop)
      have hint_eq : ∫ z, h z ∂W.measure = (∫⁻ z, ENNReal.ofReal (h z) ∂W.measure).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hh0) hhcont.aestronglyMeasurable
      have hint_le : ∫ z, h z ∂W.measure ≤ ε * ρ ^ n := by
        rw [hint_eq]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
      rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      calc ρ⁻¹ ^ n * ∫ z, h z ∂W.measure ≤ ρ⁻¹ ^ n * (ε * ρ ^ n) := by gcongr
        _ = ε := by
          have hρn : ρ ^ n ≠ 0 := pow_ne_zero n hρ0.ne'
          rw [inv_pow, mul_comm ε, ← mul_assoc, inv_mul_cancel₀ hρn, one_mul]
    -- Step 2e: `∫ f dW_{y,ρ} → θ ∫ f dv(T)` as `ρ ↓ 0` (`HasTangentPlane`), so `θ ∫ f dv(T) ≤ ε`.
    have hle : θ * ∫ z, f z ∂(planeVarifoldMeasure T) ≤ ε := by
      apply le_of_tendsto (hT.2.2 f)
      filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ hρ
      exact hbound ρ hρ.1 hρ.2
    -- Step 2f: `∫ f dv(T) = t(T) J` with `J = ∫_T χ_κ dH^n`, by `integral_map` along `z ↦ (z, T)`.
    have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
        t T * ∫ z in (T.plane : Set (Euclidean N)), χ z ∂(μHE[n] : Measure (Euclidean N)) := by
      unfold planeVarifoldMeasure
      rw [integral_map
        (μ := (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)))
        (φ := fun z : Euclidean N ↦ (z, T)) (by fun_prop) (map_continuous f).aestronglyMeasurable]
      simp only [hf]
      rw [integral_mul_const, mul_comm]
    -- Step 2g: `J ≥ ω κ^n`: `1_{B_κ(0)} ≤ χ_κ ≤ 1_{B_1(0)}` and `H^n(T ∩ B_r(0)) = ω_n r^n`
    -- (`plane_ball_measure` with `a = 0`).
    have hballfin : (μHE[n] : Measure (Euclidean N))
        ((T.plane : Set (Euclidean N)) ∩ closedBall 0 1) ≠ ∞ := by
      rw [(Submission.intcpt_fli_plane_ball_measure N n T 0 1 h0T one_pos).1]
      exact ENNReal.mul_ne_top hωne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have hχle_ind : ∀ z, χ z ≤ (closedBall (0 : Euclidean N) 1).indicator 1 z := by
      intro z
      by_cases hz : z ∈ closedBall (0 : Euclidean N) 1
      · rw [indicator_of_mem hz]
        exact hχ1 z
      · rw [indicator_of_notMem hz]
        rw [mem_closedBall, dist_zero_right, not_le] at hz
        rw [hχzero z hz.le]
    have hχint : IntegrableOn χ (T.plane : Set (Euclidean N)) μHE[n] := by
      have hfin : ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)))
          (closedBall 0 1) ≠ ∞ := by
        rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
        exact hballfin
      refine Integrable.mono' (g := (closedBall (0 : Euclidean N) 1).indicator 1) ?_
        hχcont.aestronglyMeasurable ?_
      · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin)
      · exact Eventually.of_forall fun z ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]
          exact hχle_ind z
    have hχlow : ω * κ ^ n ≤
        ∫ z in (T.plane : Set (Euclidean N)), χ z ∂(μHE[n] : Measure (Euclidean N)) := by
      have hle' : ∀ z, (closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ) z
          ≤ χ z := by
        intro z
        by_cases hz : z ∈ closedBall (0 : Euclidean N) κ
        · rw [indicator_of_mem hz, hχone z (by simpa [mem_closedBall, dist_zero_right] using hz)]
          rfl
        · rw [indicator_of_notMem hz]
          exact hχ0 z
      have h1 : ∫ z in (T.plane : Set (Euclidean N)),
          (closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ) z
            ∂(μHE[n] : Measure (Euclidean N)) ≤
          ∫ z in (T.plane : Set (Euclidean N)), χ z ∂(μHE[n] : Measure (Euclidean N)) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun z ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) z)
          hχint (Eventually.of_forall hle')
      have h2 : ∫ z in (T.plane : Set (Euclidean N)),
          (closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ) z
            ∂(μHE[n] : Measure (Euclidean N)) = ω * κ ^ n := by
        rw [integral_indicator_one measurableSet_closedBall, Measure.real,
          Measure.restrict_apply measurableSet_closedBall, inter_comm,
          (Submission.intcpt_fli_plane_ball_measure N n T 0 κ h0T hκ0).1,
          ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hκ0.le]
      linarith
    -- Step 2h: as `t(T) ≥ 0`, `J ≥ 0` and `θ ≥ 1`, `t(T) ω κ^n ≤ t(T) J ≤ θ t(T) J ≤ ε`.
    rw [hplane] at hle
    have hint0 : 0 ≤ ∫ z in (T.plane : Set (Euclidean N)), χ z
        ∂(μHE[n] : Measure (Euclidean N)) :=
      setIntegral_nonneg hTmeas fun z _ ↦ hχ0 z
    have hA : t T * (ω * κ ^ n) ≤ t T *
        ∫ z in (T.plane : Set (Euclidean N)), χ z ∂(μHE[n] : Measure (Euclidean N)) :=
      mul_le_mul_of_nonneg_left hχlow (ht0 T)
    have hB : t T * ∫ z in (T.plane : Set (Euclidean N)), χ z ∂(μHE[n] : Measure (Euclidean N))
        ≤ θ * (t T * ∫ z in (T.plane : Set (Euclidean N)), χ z
          ∂(μHE[n] : Measure (Euclidean N))) :=
      le_mul_of_one_le_left (mul_nonneg (ht0 T) hint0) hθ1
    linarith
  -- Step 3: letting `κ ↑ 1` in step 2 gives `t(T) ω ≤ ε`.
  have hmain : t T * ω ≤ ε := by
    have hc : Continuous fun κ : ℝ ↦ t T * (ω * κ ^ n) := by fun_prop
    have hlim : Tendsto (fun κ : ℝ ↦ t T * (ω * κ ^ n)) (𝓝[<] 1) (𝓝 (t T * ω)) := by
      have := hc.tendsto 1
      simp only [one_pow, mul_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT one_pos] with κ hκ'
    exact hκ κ hκ'.1 hκ'.2
  -- Step 4: `p_T v - p_P v = (p_T - p_P) v`, so `‖p_T v - p_P v‖ ≤ t(T) ‖v‖ ≤ (ε / ω) ‖v‖`.
  have hop : Grassmannian.project T v - Grassmannian.project P v =
      (LinearMap.toContinuousLinearMap
        (Grassmannian.projectionLinearMap T - Grassmannian.projectionLinearMap P)) v := by
    simp [Grassmannian.project]
  rw [hop]
  calc ‖(LinearMap.toContinuousLinearMap
        (Grassmannian.projectionLinearMap T - Grassmannian.projectionLinearMap P)) v‖
      ≤ t T * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε / ω * ‖v‖ := by
        gcongr
        rw [le_div_iff₀ hωpos]
        exact hmain
/-- Canonical integer representation of an integral varifold, with mass domination (step 6 of the
flat-limit integer multiplicity argument for Simon Ch. 8, 5.9): given a.e. positive integer
densities of integral varifolds (hD) and the canonical tangent-plane representation (hC), an
integral `W` with locally bounded first variation is `v(M, θ)` for
`M = {x ∈ spt μ_W : W has a tangent plane at x}`, `θ` is a positive integer `H^n`-a.e. on `M`, and
`∫ u dμ_W ≤ ∫_{M ∩ K} u θ dH^n` for Borel `u ≥ 0` vanishing off a compact `K ⊆ U`. -/
theorem Submission.intcpt_fli_integral_canonical_domination :
    (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), IsIntegral V → ∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ HasDensity n V.weight x (k : ℝ≥0∞)) → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 0 < θ) → ∃ θ : Euclidean N → ℝ, IsVarifoldOf V {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'} θ ∧ (∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane V x T (θ x)) ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) ∧ ∀ Z ⊆ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, V.weight Z = 0 → (μHE[n] : Measure (Euclidean N)) Z = 0) → ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U), IsIntegral W → W.HasLocallyBoundedFirstVariation → ∃ θ : Euclidean N → ℝ, IsVarifoldOf W {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} θ ∧ (∀ x ∈ {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane W x T (θ x)) ∧ HasDensity n W.weight x (ENNReal.ofReal (θ x))) ∧ (μHE[n] : Measure (Euclidean N)) {x | x ∈ {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ θ x = m} = 0 ∧ ∀ (K : Set (Euclidean N)) (u : Euclidean N → ℝ≥0∞), IsCompact K → K ⊆ U → Measurable u → (∀ x, x ∉ K → u x = 0) → ∫⁻ x, u x ∂W.weight ≤ ∫⁻ x in {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} ∩ K, u x * ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Euclidean N)) := by
  intro hD hC N n U W hint hlbfv
  -- Step 1: by (hD), `Θ^n(μ_W, x)` is an integer `k ≥ 1` for `μ_W`-a.e. `x`, so (hC) applies.
  have hdens := hD N n U W hint
  have hpos : ∀ᵐ x ∂W.weight, ∃ θ : ℝ≥0∞, HasDensity n W.weight x θ ∧ 0 < θ := by
    filter_upwards [hdens] with x hx
    obtain ⟨k, hk1, hk⟩ := hx
    exact ⟨k, hk, by exact_mod_cast hk1⟩
  -- Step 2: (hC) gives `θ` with the representation and tangent/density conclusions.
  obtain ⟨θ, hvarOf, htan, hnull⟩ := hC N n U W hlbfv hpos
  refine ⟨θ, hvarOf, htan, ?_, ?_⟩
  -- Step 3: the points of `M` where `θ` is not a positive integer form a `μ_W`-null set (density
  -- limits along `𝓝[>] 0` are unique), hence an `H^n`-null set by the null transfer property.
  · apply hnull
    · intro x hx; exact hx.1
    · apply measure_eq_zero_iff_ae_notMem.2
      filter_upwards [hdens] with x hx hxZ
      obtain ⟨k, hk1, hk⟩ := hx
      obtain ⟨hxM, hnot⟩ := hxZ
      have hθx := (htan x hxM).2
      have heq : ENNReal.ofReal (θ x) = (k : ℝ≥0∞) := tendsto_nhds_unique hθx hk
      have hθpos : 0 < θ x := hvarOf.2.2.2.1 x hxM
      apply hnot
      refine ⟨k, hk1, ?_⟩
      have := congrArg ENNReal.toReal heq
      rwa [ENNReal.toReal_ofReal hθpos.le, ENNReal.toReal_natCast] at this
  -- Step 4: domination. `θ` is `H^n`-integrable on `M ∩ K`, so `ofReal ∘ θ` is a.e.-measurable there.
  · intro K u hK hKU hu huK
    have hθint := hvarOf.2.2.2.2.1 K hK hKU
    have hθae : AEMeasurable (fun x => ENNReal.ofReal (θ x))
        ((μHE[n] : Measure (Euclidean N)).restrict
          ({x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
            HasTangentPlane W x T θ'} ∩ K)) :=
      hθint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    -- Step 5: `μ_W ⌞ K ≤ (H^n ⌞ (M ∩ K)).withDensity (ofReal ∘ θ)`, tested on Borel sets `B` via
    -- `IsVarifoldOf` applied to `(B ∩ K) × G(N,n)`.
    have hle : W.weight.restrict K ≤ ((μHE[n] : Measure (Euclidean N)).restrict
        ({x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
          HasTangentPlane W x T θ'} ∩ K)).withDensity (fun x => ENNReal.ofReal (θ x)) := by
      refine Measure.le_iff.2 (fun B hB => ?_)
      rw [Measure.restrict_apply hB, withDensity_apply _ hB, Measure.restrict_restrict hB,
        Varifold.weight_apply W (hB.inter hKmeas),
        hvarOf.2.2.2.2.2 _ ((hB.inter hKmeas).prod MeasurableSet.univ)]
      apply lintegral_mono_set
      intro x hx
      obtain ⟨hxM, S, _, hxS⟩ := hx
      exact ⟨hxS.1.1, hxM, hxS.1.2⟩
    -- Step 6: integrate `u` (supported in `K`) against this inequality.
    have hsupp : Function.support u ⊆ K := by
      intro x hx
      by_contra hxK
      exact hx (huK x hxK)
    calc ∫⁻ x, u x ∂W.weight = ∫⁻ x in K, u x ∂W.weight :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ x, u x ∂(((μHE[n] : Measure (Euclidean N)).restrict
          ({x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
            HasTangentPlane W x T θ'} ∩ K)).withDensity (fun x => ENNReal.ofReal (θ x))) :=
          lintegral_mono' hle le_rfl
      _ = ∫⁻ x in {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ),
            HasTangentPlane W x T θ'} ∩ K, ENNReal.ofReal (θ x) * u x
            ∂(μHE[n] : Measure (Euclidean N)) :=
          lintegral_withDensity_eq_lintegral_mul₀ hθae hu.aemeasurable
      _ = _ := by simp_rw [mul_comm]

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
