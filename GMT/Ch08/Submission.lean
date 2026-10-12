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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
