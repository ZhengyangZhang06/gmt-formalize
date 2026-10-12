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

/-- The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane
`T ∈ G(N,n)` is `ω_n r^n` (Simon Ch. 3, Remark 1.8(2); step 3 of the tangent-plane density proof
for Simon Ch. 8, 1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric
parametrization of `T`. -/
theorem Submission.frt_td_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: orthonormal coordinates `e : ℝ^n ≃ₗᵢ T.plane`, since `finrank T.plane = n`.
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] T.plane :=
    ((stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)).repr.symm
  -- Step 2: the isometric embedding `ι : ℝ^n → ℝ^N`, `ι v = e v`.
  let ι : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp e.toLinearIsometry
  -- Step 3: `ι '' B_r(0) = T.plane ∩ B_r(0)`.
  have himage : ι '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(e v).2, ?_⟩
      rw [mem_closedBall_zero_iff] at hv ⊢
      rwa [ι.norm_map]
    · rintro ⟨hy, hyr⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff] at hyr ⊢
        rwa [e.symm.norm_map]
      · change ((e (e.symm ⟨y, hy⟩) : T.plane) : Euclidean N) = y
        rw [e.apply_symm_apply]
  -- Steps 4–5: `H^n` is invariant under the isometry `ι`, and `H^n = vol` on `ℝ^n`.
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Steps 6–7: Haar scaling `vol (B_r(0)) = r^n vol (B°_1(0))` (`r ≥ 0`; no `0 < n` needed).
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr,
    unitBallVolume, mul_comm]

/-- Lower ball-mass bound from weight blow-ups (Simon Ch. 3, Remark 1.8(2), lower cutoff): if
`t^{-n} ∫ g(t^{-1}(z - x)) dμ(z) → θ ∫_T g dH^n` as `t ↓ 0` for every `g ∈ C_c(ℝ^N)`, then for
every `c < θ ω_n` we have `c t^n ≤ μ(B_t(x))` for all small `t > 0`. -/
theorem Submission.frt_td_ball_mass_lower_of_blowup :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), 0 < θ → (∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) → ∀ c : ℝ≥0∞, c < ENNReal.ofReal θ * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t) := by
  intro N n μ x T θ hθ hblow c hc
  -- Steps 1–2: `ω_n < ∞`, hence `c < ∞` and `c.toReal < θ ω_n`.
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcθ : c.toReal < θ * (unitBallVolume n).toReal := by
    have h := (ENNReal.toReal_lt_toReal hc_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 3: choose `κ ∈ (0, 1)` with `c.toReal < θ ω_n κ^n`, by continuity of `κ ↦ κ^n` at `1`.
  have hlim : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[<] 1)
      (𝓝 (θ * (unitBallVolume n).toReal)) := by
    have h := ((continuous_pow n).tendsto (1 : ℝ)).const_mul (θ * (unitBallVolume n).toReal)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hκ01 : ∀ᶠ κ in 𝓝[<] (1 : ℝ), κ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨κ, hκc, hκ0, hκ1⟩ := ((hlim.eventually (lt_mem_nhds hcθ)).and hκ01).exists
  have h1κ : 0 < 1 - κ := sub_pos.2 hκ1
  -- Step 4: the cutoff `χ(y) = max(0, min(1, (1 - ‖y‖)/(1 - κ)))`.
  let χ : Euclidean N → ℝ := fun y ↦ max 0 (min 1 ((1 - ‖y‖) / (1 - κ)))
  have hχ_zero : ∀ y : Euclidean N, 1 ≤ ‖y‖ → χ y = 0 := fun y hy ↦ by
    have h : (1 - ‖y‖) / (1 - κ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h1κ.le
    simp only [χ]
    rw [min_eq_right (h.trans zero_le_one), max_eq_left h]
  have hχ_one : ∀ y : Euclidean N, ‖y‖ ≤ κ → χ y = 1 := fun y hy ↦ by
    have h : 1 ≤ (1 - ‖y‖) / (1 - κ) := (one_le_div h1κ).2 (by linarith)
    simp only [χ]
    rw [min_eq_left h, max_eq_right zero_le_one]
  let g : C_c(Euclidean N, ℝ) :=
    ⟨⟨χ, by fun_prop⟩, HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) 1)
      fun y hy ↦ hχ_zero y (not_le.1 fun h ↦ hy (mem_closedBall_zero_iff.2 h)).le⟩
  have hg_nonneg : ∀ y, 0 ≤ g y := fun _ ↦ le_max_left _ _
  have hg_le : ∀ y, g y ≤ 1 := fun _ ↦ max_le zero_le_one (min_le_left _ _)
  -- Step 5: plane side, `ω_n κ^n ≤ ∫_T g dH^n`.
  set ν : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hν
  have hνB : ∀ r : ℝ, 0 ≤ r → ν (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n :=
    fun r hr ↦ by
      rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact Submission.frt_td_plane_closedBall_hausdorff N n T r hr
  have hν1 : ν (closedBall 0 1) ≠ ∞ := by
    rw [hνB 1 zero_le_one]
    exact ENNReal.mul_ne_top hω (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hg_int : Integrable (fun y ↦ g y) ν := by
    refine ((integrableOn_const (C := (1 : ℝ)) hν1).integrable_indicator
      measurableSet_closedBall).mono' (map_continuous g).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg y)]
    by_cases hy : y ∈ closedBall (0 : Euclidean N) 1
    · rw [indicator_of_mem hy]
      exact hg_le y
    · rw [indicator_of_notMem hy]
      exact (hχ_zero y (not_le.1 fun h ↦ hy (mem_closedBall_zero_iff.2 h)).le).le
  have hplane : (unitBallVolume n).toReal * κ ^ n ≤ ∫ y, g y ∂ν := by
    have hle : ∀ y, (closedBall (0 : Euclidean N) κ).indicator 1 y ≤ g y := fun y ↦ by
      by_cases hy : y ∈ closedBall (0 : Euclidean N) κ
      · rw [indicator_of_mem hy, Pi.one_apply]
        exact (hχ_one y (mem_closedBall_zero_iff.1 hy)).ge
      · rw [indicator_of_notMem hy]
        exact hg_nonneg y
    have h := integral_mono_of_nonneg (f := (closedBall (0 : Euclidean N) κ).indicator 1)
      (Eventually.of_forall (indicator_nonneg fun _ _ ↦ zero_le_one)) hg_int
      (Eventually.of_forall hle)
    rwa [integral_indicator_one measurableSet_closedBall, measureReal_def,
      hνB κ hκ0.le, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hκ0.le] at h
  -- Step 6: the blow-up limit `θ ∫_T g dH^n` exceeds `c.toReal`.
  have hlt : c.toReal < θ * ∫ y, g y ∂ν :=
    calc c.toReal < θ * (unitBallVolume n).toReal * κ ^ n := hκc
      _ = θ * ((unitBallVolume n).toReal * κ ^ n) := mul_assoc _ _ _
      _ ≤ θ * ∫ y, g y ∂ν := mul_le_mul_of_nonneg_left hplane hθ.le
  filter_upwards [(hblow g).eventually (lt_mem_nhds hlt), self_mem_nhdsWithin] with t ht ht0
  have ht0 : 0 < t := ht0
  -- Step 7: comparison with the ball mass.
  rcases eq_or_ne (μ (closedBall x t)) ∞ with hμt | hμt
  · rw [hμt]
    exact le_top
  have hcmp : ∫ z, g (t⁻¹ • (z - x)) ∂μ ≤ μ.real (closedBall x t) := by
    rw [← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ hg_nonneg _)
      ((integrableOn_const (C := (1 : ℝ)) hμt).integrable_indicator measurableSet_closedBall)
      (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ closedBall x t
    · rw [indicator_of_mem hz]
      exact hg_le _
    · rw [indicator_of_notMem hz]
      refine (hχ_zero _ ?_).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0), one_le_inv_mul₀ ht0,
        ← dist_eq_norm]
      exact (not_le.1 fun h ↦ hz (mem_closedBall.2 h)).le
  -- Step 8: conclusion.
  have hfin : c.toReal * t ^ n < μ.real (closedBall x t) := by
    have htn : t⁻¹ ^ n * t ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ ht0.ne', one_pow]
    calc c.toReal * t ^ n < (t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) * t ^ n :=
          mul_lt_mul_of_pos_right ht (pow_pos ht0 n)
      _ = ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
          rw [mul_comm, ← mul_assoc, mul_comm (t ^ n), htn, one_mul]
      _ ≤ μ.real (closedBall x t) := hcmp
  calc c * ENNReal.ofReal t ^ n = ENNReal.ofReal (c.toReal * t ^ n) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_pow ht0.le,
          ENNReal.ofReal_toReal hc_top]
    _ ≤ ENNReal.ofReal (μ.real (closedBall x t)) := ENNReal.ofReal_le_ofReal hfin.le
    _ = μ (closedBall x t) := ofReal_measureReal hμt
/-- Upper ball-mass bound from the blow-up limit (Simon Ch. 8, 1.2, Steps 2, 4 and 6; the upper
cutoff of Simon Ch. 3, Remark 1.8(2)): if `t⁻ⁿ ∫ g(t⁻¹(z - x)) dμ(z) → θ ∫_T g dHⁿ` for every
`g ∈ C_c(ℝ^N)` and `μ(B_{r₀}(x)) < ∞`, then `μ(B_t(x)) ≤ c tⁿ` for all small `t > 0` whenever
`θ ωₙ < c`.  The test function is a cutoff equal to `1` on `B_1(0)` and to `0` off `B_κ(0)`,
with `κ > 1` chosen so that `θ ωₙ κⁿ < c`. -/
theorem Submission.frt_td_ball_mass_upper_of_blowup :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (T : Grassmannian N n) (θ r₀ : ℝ), 0 < θ → 0 < r₀ → μ (closedBall x r₀) ≠ ⊤ → (∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) → ∀ c : ℝ≥0∞, ENNReal.ofReal θ * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n := by
  intro N n μ x T θ r₀ hθ hr₀ hμr₀ hblow c hc
  -- Step 1: `ωₙ < ∞`.
  have hωtop : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin n)))).ne
  -- Step 2: the case `c = ∞` is trivial.
  rcases eq_or_ne c ∞ with rfl | hctop
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [ENNReal.top_mul (pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne')]
    exact le_top
  -- Step 3: `θ ωₙ < c` in `ℝ`.
  have hθω : θ * (unitBallVolume n).toReal < c.toReal := by
    have h := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop) hctop).2 hc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at h
  -- Step 4: choose `κ > 1` with `θ ωₙ κⁿ < c`, by continuity of `κ ↦ θ ωₙ κⁿ` at `κ = 1`.
  obtain ⟨κ, hκc, hκ1⟩ : ∃ κ : ℝ, θ * (unitBallVolume n).toReal * κ ^ n < c.toReal ∧ 1 < κ := by
    have hcont : Tendsto (fun κ : ℝ ↦ θ * (unitBallVolume n).toReal * κ ^ n) (𝓝[>] 1)
        (𝓝 (θ * (unitBallVolume n).toReal * 1 ^ n)) :=
      (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
    rw [one_pow, mul_one] at hcont
    exact ((hcont.eventually (gt_mem_nhds hθω)).and self_mem_nhdsWithin).exists
  have hκ0 : 0 < κ := zero_lt_one.trans hκ1
  -- Step 5: the cutoff `g(y) = max 0 (min 1 ((κ - ‖y‖)/(κ - 1)))`: `0 ≤ g ≤ 1`, `g = 1` on
  -- `B_1(0)` and `g = 0` off `B°_κ(0)`, so `g ∈ C_c(ℝ^N)`.
  obtain ⟨χ, hχ⟩ : ∃ χ : Euclidean N → ℝ, χ = fun y ↦ max 0 (min 1 ((κ - ‖y‖) / (κ - 1))) :=
    ⟨_, rfl⟩
  have hχcont : Continuous χ := by
    rw [hχ]
    fun_prop
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ by
    rw [hχ]
    exact le_max_left _ _
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ by
    rw [hχ]
    exact max_le zero_le_one (min_le_left _ _)
  have hχ_one : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦ by
    have h : 1 ≤ (κ - ‖y‖) / (κ - 1) := by
      rw [le_div_iff₀ (sub_pos.2 hκ1)]
      linarith
    simp only [hχ, min_eq_left h, max_eq_right zero_le_one]
  have hχ_zero : ∀ y, κ ≤ ‖y‖ → χ y = 0 := fun y hy ↦ by
    have h : (κ - ‖y‖) / (κ - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [hχ]
    exact max_eq_left ((min_le_right _ _).trans h)
  have hχsupp : HasCompactSupport χ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) κ) fun y hy ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact hχ_zero y hy.le
  let g : C_c(Euclidean N, ℝ) := ⟨⟨χ, hχcont⟩, hχsupp⟩
  have hg0 : ∀ y, 0 ≤ g y := hχ0
  have hg1 : ∀ y, g y ≤ 1 := hχ1
  have hg_one : ∀ y, ‖y‖ ≤ 1 → g y = 1 := hχ_one
  have hg_zero : ∀ y, κ ≤ ‖y‖ → g y = 0 := hχ_zero
  -- Step 6: `∫_T g dHⁿ ≤ Hⁿ(T ∩ B_κ(0)) = ωₙ κⁿ`, by the sibling plane-ball formula.
  have hνball : ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)))
      (closedBall 0 κ) = unitBallVolume n * ENNReal.ofReal κ ^ n := by
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.frt_td_plane_closedBall_hausdorff N n T κ hκ0.le
  have hplane : ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] ≤
      (unitBallVolume n).toReal * κ ^ n := by
    have hind : Integrable ((closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ))
        ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))) := by
      refine (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const ?_)
      rw [hνball]
      exact ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    calc ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]
        ≤ ∫ y in (T.plane : Set (Euclidean N)),
            (closedBall (0 : Euclidean N) κ).indicator (1 : Euclidean N → ℝ) y ∂μHE[n] := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y ↦ hg0 y) hind
            (Eventually.of_forall fun y ↦ ?_)
          by_cases hy : y ∈ closedBall (0 : Euclidean N) κ
          · rw [indicator_of_mem hy, Pi.one_apply]
            exact hg1 y
          · have hκy : κ ≤ ‖y‖ := by
              rw [mem_closedBall_zero_iff, not_le] at hy
              exact hy.le
            rw [indicator_of_notMem hy, hg_zero y hκy]
      _ = ((μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N))).real
            (closedBall 0 κ) := integral_indicator_one measurableSet_closedBall
      _ = (unitBallVolume n).toReal * κ ^ n := by
          rw [measureReal_def, hνball, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal hκ0.le]
  -- Step 7: eventually `t⁻ⁿ ∫ g(t⁻¹(z - x)) dμ < c` and `t ∈ (0, r₀/κ)`.
  have hlim : θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] < c.toReal :=
    (mul_le_mul_of_nonneg_left hplane hθ.le).trans_lt (by rwa [← mul_assoc])
  filter_upwards [(hblow g).eventually (gt_mem_nhds hlim), Ioo_mem_nhdsGT (div_pos hr₀ hκ0)]
    with t hlt ⟨ht0, htr⟩
  -- Step 8: `B_t(x) ⊆ B_{κt}(x) ⊆ B_{r₀}(x)` have finite mass.
  have hκt : κ * t ≤ r₀ := by
    rw [lt_div_iff₀ hκ0] at htr
    linarith
  have hfinκt : μ (closedBall x (κ * t)) ≠ ∞ :=
    ne_top_of_le_ne_top hμr₀ (measure_mono (closedBall_subset_closedBall hκt))
  have hfint : μ (closedBall x t) ≠ ∞ :=
    ne_top_of_le_ne_top hfinκt
      (measure_mono (closedBall_subset_closedBall (le_mul_of_one_le_left ht0.le hκ1.le)))
  -- Step 9: `z ↦ g(t⁻¹(z - x))` is `μ`-integrable, being bounded by `1_{B_{κt}(x)}`.
  have hnorm : ∀ z, ‖t⁻¹ • (z - x)‖ = ‖z - x‖ / t := fun z ↦ by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_eq_div]
  have hint : Integrable (fun z ↦ g (t⁻¹ • (z - x))) μ := by
    have hind : Integrable ((closedBall x (κ * t)).indicator (1 : Euclidean N → ℝ)) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfinκt)
    refine hind.mono' ((map_continuous g).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_of_nonneg (hg0 _)]
    by_cases hz : z ∈ closedBall x (κ * t)
    · rw [indicator_of_mem hz, Pi.one_apply]
      exact hg1 _
    · have hκz : κ ≤ ‖t⁻¹ • (z - x)‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [hnorm, le_div_iff₀ ht0]
        exact hz.le
      rw [indicator_of_notMem hz, hg_zero _ hκz]
  -- Step 10: `μ(B_t(x)) ≤ ∫ g(t⁻¹(z - x)) dμ`, as `1_{B_t(x)} ≤ g(t⁻¹(· - x))`.
  have hcmp : μ.real (closedBall x t) ≤ ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
    rw [← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ ?_) hint
      (Eventually.of_forall fun z ↦ ?_)
    · exact indicator_nonneg (fun _ _ ↦ zero_le_one) z
    · dsimp only
      by_cases hz : z ∈ closedBall x t
      · have hle : ‖t⁻¹ • (z - x)‖ ≤ 1 := by
          rw [hnorm, div_le_one ht0, ← dist_eq_norm]
          exact hz
        rw [indicator_of_mem hz, Pi.one_apply, hg_one _ hle]
      · rw [indicator_of_notMem hz]
        exact hg0 _
  -- Step 11: `μ(B_t(x)) ≤ c.toReal tⁿ`, and back to `ℝ≥0∞` using `μ(B_t(x)) < ∞`.
  have hreal : μ.real (closedBall x t) ≤ c.toReal * t ^ n := by
    have heq : (t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂μ) * t ^ n = ∫ z, g (t⁻¹ • (z - x)) ∂μ := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ ht0.ne', one_pow, one_mul]
    rw [← heq] at hcmp
    exact hcmp.trans (mul_le_mul_of_nonneg_right hlt.le (pow_nonneg ht0.le n))
  calc μ (closedBall x t) = ENNReal.ofReal (μ.real (closedBall x t)) :=
        (ENNReal.ofReal_toReal hfint).symm
    _ ≤ ENNReal.ofReal (c.toReal * t ^ n) := ENNReal.ofReal_le_ofReal hreal
    _ = c * ENNReal.ofReal t ^ n := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hctop,
          ENNReal.ofReal_pow ht0.le]
/-- Density squeeze (Simon Ch. 3, Remark 1.8(2), last step): if, as `t ↓ 0`, eventually
`c t^n ≤ μ(B_t(x))` for every `c < a ω_n` and eventually `μ(B_t(x)) ≤ c t^n` for every
`c > a ω_n`, then `Θ^n(μ, x) = a`. -/
theorem Submission.frt_td_hasDensity_of_ball_mass_bounds :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (a : ℝ≥0∞), (∀ c : ℝ≥0∞, c < a * unitBallVolume n → ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) → (∀ c : ℝ≥0∞, a * unitBallVolume n < c → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (closedBall x t) ≤ c * ENNReal.ofReal t ^ n) → HasDensity n μ x a := by
  intro N n μ x a hlow hup
  -- Step 1: `0 < ω_n < ∞`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (x := 0)
      (r := 1)).ne
  -- Step 3: by `tendsto_order`, squeeze the density ratio from below and from above.
  rw [HasDensity, tendsto_order]
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- Step 4: for `b < b' < a`, eventually `b' ω_n t^n ≤ μ(B_t(x))`, so `b' ≤ densityRatio`.
    obtain ⟨b', hbb', hb'a⟩ := exists_between hb
    filter_upwards [hlow _ (ENNReal.mul_lt_mul_left hω0 hωt hb'a), self_mem_nhdsWithin]
      with t ht (htpos : (0 : ℝ) < t)
    -- Step 2: for `t > 0` the normalizer `ω_n t^n` is nonzero and finite.
    have hD0 : unitBallVolume n * ENNReal.ofReal t ^ n ≠ 0 :=
      mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 htpos).ne')
    have hDt : unitBallVolume n * ENNReal.ofReal t ^ n ≠ ∞ :=
      ENNReal.mul_ne_top hωt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    refine hbb'.trans_le ?_
    rw [densityRatio, ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDt), ← mul_assoc]
    exact ht
  · -- Step 5: for `a < b' < b`, eventually `μ(B_t(x)) ≤ b' ω_n t^n`, so `densityRatio ≤ b'`.
    obtain ⟨b', hab', hb'b⟩ := exists_between hb
    filter_upwards [hup _ (ENNReal.mul_lt_mul_left hω0 hωt hab')] with t ht
    exact (ENNReal.div_le_of_le_mul (by rwa [← mul_assoc])).trans_lt hb'b
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
/-- Density at a tangent point (Simon Ch. 8, 1.2, step (0c); Ch. 3, Remark 1.8(2)): if `V` has
tangent plane `T` with multiplicity `θ` at `x`, then `Θ^n(μ_V, x) = θ`, i.e.
`μ_V(B_t(x)) / (ω_n t^n) → θ` as `t ↓ 0`. -/
theorem Submission.frt_tangent_plane_hasDensity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → HasDensity n V.weight x (ENNReal.ofReal θ) := by
  intro N n U V x T θ hT
  -- Step 1: `x ∈ U` and `θ > 0`; as `U` is open, some `B_{r₀}(x) ⊆ U` has finite `μ_V`-mass.
  have hθ : 0 < θ := hT.2.1
  obtain ⟨r₀, hr₀, hr₀U⟩ := nhds_basis_closedBall.mem_iff.1 (V.isOpen_domain.mem_nhds hT.1)
  have hμr₀ : V.weight (closedBall x r₀) ≠ ⊤ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x r₀) hr₀U
  -- Step 2: `t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` for every `g ∈ C_c(ℝ^N)`.
  have hblow := Submission.frt_weight_blowup_tendsto N n U V x T θ hT
  -- Steps 3–4: `c t^n ≤ μ_V(B_t(x))` eventually for `c < θ ω_n` and `μ_V(B_t(x)) ≤ c t^n`
  -- eventually for `c > θ ω_n`; the density squeeze then gives `Θ^n(μ_V, x) = θ`.
  exact Submission.frt_td_hasDensity_of_ball_mass_bounds N n V.weight x (ENNReal.ofReal θ)
    (Submission.frt_td_ball_mass_lower_of_blowup N n V.weight x T θ hθ hblow)
    (Submission.frt_td_ball_mass_upper_of_blowup N n V.weight x T θ r₀ hθ hr₀ hμr₀ hblow)

/-- **Simon Ch. 8, Definition 1.1: the tangent space and its multiplicity are unique** (child
`tangent_unique` of `first_rectifiability`: step (0d) of the parent's proof of 1.2; cf. Ch. 3,
Remark 1.5(1)).  If `V` has tangent space `T` with multiplicity `θ` and `T'` with multiplicity
`θ'` at `x`, then `T' = T` and `θ' = θ`.  Both multiplicities are the density `Θ^n(μ_V, x)`; the
weight blow-ups then give `∫ g dH^n⌞T' = ∫ g dH^n⌞T` for every `g ∈ C_c(ℝ^N)`, so the regular
measures `H^n⌞T'` and `H^n⌞T` agree, hence so do their supports `T'` and `T`; a projection matrix
is determined by its range. -/
theorem Submission.frt_tangent_plane_unique :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N)
      (T T' : Grassmannian N n) (θ θ' : ℝ),
      HasTangentPlane V x T θ → HasTangentPlane V x T' θ' → T' = T ∧ θ' = θ := by
  intro N n U V x T T' θ θ' hT hT'
  -- Step 1: `θ'` and `θ` are both the limit of the density ratio along `𝓝[>] 0`.
  have hθ : θ' = θ :=
    (ENNReal.ofReal_eq_ofReal_iff hT'.2.1.le hT.2.1.le).mp
      (tendsto_nhds_unique (Submission.frt_tangent_plane_hasDensity N n U V x T' θ' hT')
        (Submission.frt_tangent_plane_hasDensity N n U V x T θ hT))
  refine ⟨?_, hθ⟩
  -- Steps 2–3: `H^n⌞T'` and `H^n⌞T` are regular with the same `C_c` integrals (cancel `θ > 0`).
  have hmeasure : (μHE[n] : Measure (Euclidean N)).restrict (T'.plane : Set (Euclidean N)) =
      (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) := by
    have := Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane
    have := Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ ?_
    have h := tendsto_nhds_unique (Submission.frt_weight_blowup_tendsto N n U V x T' θ' hT' g)
      (Submission.frt_weight_blowup_tendsto N n U V x T θ hT g)
    rw [hθ] at h
    exact mul_left_cancel₀ hT.2.1.ne' h
  -- Step 4: the support of `H^n⌞P` is the `n`-plane `P`.
  have hplane : T'.plane = T.plane := by
    apply SetLike.ext'
    rw [← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T'.finrank_plane,
      ← Chapter03.support_euclideanHausdorffMeasure_restrict_submodule T.finrank_plane, hmeasure]
  -- Step 5: `p_S` is symmetric and idempotent, hence the orthogonal projection onto its range
  -- `S.plane`, and `S` is the matrix of `p_S`.
  have hproj : ∀ S : Grassmannian N n,
      S.projectionLinearMap = S.plane.starProjection.toLinearMap := by
    intro S
    obtain ⟨_, hS⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
      ⟨S.projectionLinearMap_comp_self, S.projectionLinearMap_isSymmetric⟩
    exact hS
  apply Subtype.ext
  rw [← T'.toMatrix_projectionLinearMap, ← T.toMatrix_projectionLinearMap, hproj T', hproj T,
    hplane]
/-- The net-of-planes step of Simon Ch. 3, proof of Theorem 1.6 "⇐" (p. 73), for the tangent
points of a varifold (Ch. 8, 1.2): suppose that for every `L ∈ (0,1]` and every plane `P` there are
closed `L`-graphs `Γ_0, Γ_1, …` over `P` (`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for
`y, z ∈ Γ_i`) containing every `x` at which `V` has a tangent plane `T` with
`|p_T v - p_P v| ≤ (L/4)|v|`.  Then for every `L ∈ (0,1]` countably many closed `L`-graphs, each
paired with its base plane, cover all points at which `V` has a tangent plane.  A countable dense set
of planes replaces the book's finite net: `S ↦ p_S` is continuous into operators, so every plane is
within operator distance `L/4` of a plane of the dense set. -/
theorem Submission.frt_tangent_points_flat_graph_cover :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), (∀ L : ℝ, 0 < L → L ≤ 1 → ∀ P : Grassmannian N n, ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) → ∃ i, x ∈ Γ i) → ∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ} ⊆ ⋃ c ∈ C, c.2 := by
  intro N n U V hcov L hL0 hL1
  -- Step 2: `Φ S = p_S`, as a continuous linear operator, depends continuously on `S`, being a
  -- linear function of the projection matrix `S.1`.
  let Φ : Grassmannian N n → (Euclidean N →L[ℝ] Euclidean N) := fun S ↦
    LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S)
  have hΦ : Continuous Φ := by
    let F : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N) :=
      (LinearMap.toContinuousLinearMap :
          (Euclidean N →ₗ[ℝ] Euclidean N) ≃ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N)).toLinearMap ∘ₗ
        (LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
          Grassmannian.coordinateBasis.toBasis).symm.toLinearMap
    exact F.continuous_of_finiteDimensional.comp continuous_subtype_val
  have hΦapp : ∀ S v, Φ S v = Grassmannian.project S v := fun _ _ ↦ rfl
  -- Step 3: a countable dense set `D` of planes is an `L/4`-net in operator norm.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Grassmannian N n)
  have hnet : ∀ T : Grassmannian N n, ∃ P ∈ D, ∀ v : Euclidean N,
      ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖ := by
    intro T
    have hopen : IsOpen {S | ‖Φ S - Φ T‖ < L / 4} :=
      isOpen_lt (continuous_norm.comp (hΦ.sub continuous_const)) continuous_const
    obtain ⟨P, hPD, hP⟩ := hDd.exists_mem_open hopen ⟨T, by simpa using div_pos hL0 four_pos⟩
    refine ⟨P, hPD, fun v ↦ ?_⟩
    have hTP : ‖Φ T - Φ P‖ ≤ L / 4 := by
      rw [norm_sub_rev]
      exact le_of_lt hP
    simpa [hΦapp] using (Φ T - Φ P).le_of_opNorm_le hTP v
  -- Step 4: choose the covers `Γ P` supplied for the planes `P ∈ D` and collect them over `D × ℕ`.
  choose Γ hΓc hΓg hΓx using hcov L hL0 hL1
  refine ⟨(fun p : Grassmannian N n × ℕ ↦ (p.1, Γ p.1 p.2)) '' (D ×ˢ univ),
    (hDc.prod countable_univ).image _, ?_, ?_⟩
  · -- Step 5: each member is a closed `L`-graph over its plane.
    rintro c ⟨⟨P, i⟩, -, rfl⟩
    exact ⟨hΓc P i, hΓg P i⟩
  · -- Step 6: a tangent point with plane `T` lies in a graph over a plane `P ∈ D` near `T`.
    rintro x ⟨T, θ, hx⟩
    obtain ⟨P, hPD, hP⟩ := hnet T
    obtain ⟨i, hi⟩ := hΓx P x T θ hx hP
    exact mem_iUnion₂.2 ⟨(P, Γ P i), ⟨(P, i), ⟨hPD, mem_univ i⟩, rfl⟩, hi⟩

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
