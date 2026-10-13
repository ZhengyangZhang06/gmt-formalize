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

/-- **Simon Ch. 8, 5.2, the cylinder cut-off** (child `cylinder_cutoff` of `limit_ball_mass`):
for `a < b` one `F ∈ C_c(ℝ^N × G(N,n), ℝ)`, chosen before the measure, satisfies
`ν(B_a(0) × G(N,n)) ≤ ∫ F dν ≤ ν(B_b(0) × G(N,n))` for every `ν` with `ν(B_b(0) × G(N,n)) < ∞`.
Take the ramp `F(y, S) = min 1 (max 0 ((b - |y|) / (b - a)))`: it is continuous, `0 ≤ F ≤ 1`,
`F = 1` on `B_a(0) × G(N,n)` and `F = 0` off the compact `B_b(0) × G(N,n)`.  Then
`|F| ≤ 1_{B_b(0) × G(N,n)}` gives integrability, so `ofReal (∫ F dν) = ∫⁻ ofReal ∘ F dν`, and
`1_{B_a(0) × G(N,n)} ≤ ofReal ∘ F ≤ 1_{B_b(0) × G(N,n)}` gives both bounds. -/
theorem Submission.varifold_tangents_lbm_exists_cylinder_cutoff :
    ∀ (N n : ℕ) (a b : ℝ), a < b → ∃ F : C_c(Euclidean N × Grassmannian N n, ℝ), ∀ ν : Measure (Euclidean N × Grassmannian N n), ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → ν (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ ENNReal.ofReal (∫ z, F z ∂ν) ∧ ENNReal.ofReal (∫ z, F z ∂ν) ≤ ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n a b hab
  have hd : 0 < b - a := sub_pos.2 hab
  set Ka := closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))
  set Kb := closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)) with hKb
  -- The ramp `h(y, S) = min 1 (max 0 ((b - ‖y‖) / (b - a)))`: `0 ≤ h ≤ 1`, `h = 1` on `Ka`,
  -- `h = 0` off `Kb`.
  set h : Euclidean N × Grassmannian N n → ℝ := fun z ↦ min 1 (max 0 ((b - ‖z.1‖) / (b - a)))
  have hcont : Continuous h :=
    continuous_const.min (continuous_const.max
      ((continuous_const.sub (continuous_norm.comp continuous_fst)).div_const _))
  have h_nonneg : ∀ z, 0 ≤ h z := fun z ↦ le_min zero_le_one (le_max_left _ _)
  have h_le_one : ∀ z, h z ≤ 1 := fun z ↦ min_le_left _ _
  have h_one : ∀ z ∈ Ka, h z = 1 := by
    rintro ⟨y, S⟩ ⟨hy, -⟩
    rw [mem_closedBall, dist_zero_right] at hy
    have h1 : 1 ≤ (b - ‖y‖) / (b - a) := by
      rw [le_div_iff₀ hd]
      linarith
    show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 1
    rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  have h_zero : ∀ z ∉ Kb, h z = 0 := by
    rintro ⟨y, S⟩ hz
    have hy : b < ‖y‖ := by
      simpa [hKb, mem_prod, mem_closedBall, dist_zero_right] using hz
    have h0 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 0
    rw [max_eq_left h0, min_eq_right zero_le_one]
  -- `Kb` is compact (`ℝ^N` is proper and `G(N,n)` is compact), so `h ∈ C_c`.
  have hKb_cpt : IsCompact Kb := (isCompact_closedBall 0 b).prod isCompact_univ
  refine ⟨⟨⟨h, hcont⟩, HasCompactSupport.intro hKb_cpt h_zero⟩, fun ν hν ↦ ?_⟩
  have hFz : ∀ z, (⟨⟨h, hcont⟩, HasCompactSupport.intro hKb_cpt h_zero⟩ :
      C_c(Euclidean N × Grassmannian N n, ℝ)) z = h z := fun z ↦ rfl
  simp only [hFz]
  have hmeasA : MeasurableSet Ka := measurableSet_closedBall.prod MeasurableSet.univ
  have hmeasB : MeasurableSet Kb := measurableSet_closedBall.prod MeasurableSet.univ
  -- `|h| ≤ 1_{Kb}` and `ν(Kb) < ∞`, so `h` is `ν`-integrable.
  have hint : Integrable h ν := by
    refine Integrable.mono' ((integrable_indicator_iff hmeasB).2
      (integrableOn_const (C := (1 : ℝ)) hν)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ Kb
    · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (h_nonneg z)]
      exact h_le_one z
    · rw [indicator_of_notMem hz, h_zero z hz, norm_zero]
  -- `ofReal (∫ h dν) = ∫⁻ ofReal ∘ h dν`, and `1_{Ka} ≤ ofReal ∘ h ≤ 1_{Kb}` pointwise.
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall h_nonneg)]
  constructor
  · calc ν Ka = ∫⁻ z, Ka.indicator 1 z ∂ν := (lintegral_indicator_one hmeasA).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂ν := lintegral_mono fun z ↦ by
        by_cases hz : z ∈ Ka
        · rw [indicator_of_mem hz, Pi.one_apply, h_one z hz, ENNReal.ofReal_one]
        · rw [indicator_of_notMem hz]
          exact zero_le
  · calc ∫⁻ z, ENNReal.ofReal (h z) ∂ν ≤ ∫⁻ z, Kb.indicator 1 z ∂ν := lintegral_mono fun z ↦ by
          by_cases hz : z ∈ Kb
          · rw [indicator_of_mem hz, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (h_le_one z)
          · rw [indicator_of_notMem hz, h_zero z hz, ENNReal.ofReal_zero]
      _ = ν Kb := lintegral_indicator_one hmeasB

/-- **Simon Ch. 8, 5.2, vague-limit cylinder bounds** (child `vague_cylinder_bounds` of
`limit_ball_mass`): if `μs j → μ` vaguely, `a < b`, `μ(B_b(0) × G(N,n)) < ∞`,
`μs j (B_a(0) × G(N,n)) → La` and `μs j (B_b(0) × G(N,n)) → Lb < ∞`, then
`μ(B_a(0) × G(N,n)) ≤ Lb` and `La ≤ μ(B_b(0) × G(N,n))`.
Take the cut-off `F` of `varifold_tangents_lbm_exists_cylinder_cutoff` for `a < b`: it puts
`ofReal (∫ F dμ)` between `μ(B_a(0) × G(N,n))` and `μ(B_b(0) × G(N,n))`, and, as `Lb < ∞`,
eventually puts `ofReal (∫ F dμs j)` between `μs j (B_a(0) × G(N,n))` and `μs j (B_b(0) × G(N,n))`.
Vague convergence gives `ofReal (∫ F dμs j) → ofReal (∫ F dμ)`, so passing to the limit gives
`ofReal (∫ F dμ) ≤ Lb` and `La ≤ ofReal (∫ F dμ)`. -/
theorem Submission.varifold_tangents_lbm_vague_cylinder_bounds :
    ∀ (N n : ℕ) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (a b : ℝ) (La Lb : ℝ≥0∞), VagueConverges μs μ → a < b → μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 La) → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 Lb) → Lb ≠ ∞ → μ (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ Lb ∧ La ≤ μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n μs μ a b La Lb hconv hab hμb hLa hLb hLb_ne
  obtain ⟨F, hF⟩ := Submission.varifold_tangents_lbm_exists_cylinder_cutoff N n a b hab
  -- The cut-off bounds `ofReal (∫ F dμ)`, and, since `μs j (B_b(0) × G(N,n)) → Lb ≠ ∞`, eventually
  -- also `ofReal (∫ F dμs j)`.
  obtain ⟨hμa, hμF⟩ := hF μ hμb
  have hev := (hLb.eventually_ne hLb_ne).mono fun j hj ↦ hF (μs j) hj
  -- Vague convergence at `F`, composed with the continuous `ENNReal.ofReal`.
  have hFlim := ENNReal.tendsto_ofReal (hconv F)
  exact ⟨hμa.trans (le_of_tendsto_of_tendsto hFlim hLb (hev.mono fun j hj ↦ hj.2)),
    (le_of_tendsto_of_tendsto hLa hFlim (hev.mono fun j hj ↦ hj.1)).trans hμF⟩
/-- **Simon Ch. 8, 5.1–5.2, the ball-mass computation** (child `rescaled_ball_mass` of
`varifold_tangents`): if `Θ^n(μ_V, x) = θ`, then `V_{x,t}(B_R(0) × G(N,n)) → θ ω_n R^n` as `t ↓ 0`.
For `t > 0` the preimage of `B_R(0) × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is
`B_{tR}(x) × G(N,n)`, so `V_{x,t}(B_R(0) × G(N,n)) = t^{-n} μ_V(B_{tR}(x))`, which equals
`densityRatio n μ_V x (tR) · ω_n R^n` because `0 < ω_n < ∞`; then compose `HasDensity` with
`t ↦ tR` (as in SimonGMT's `Varifold.tendsto_blowUpWeight_closedBall_of_density`). -/
theorem Submission.varifold_tangents_rescaled_ball_mass_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ : ℝ≥0∞) (R : ℝ), HasDensity n V.weight x θ → 0 < R → Tendsto (fun t : ℝ ↦ rescaledMeasure V x t (closedBall (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)))) (𝓝[>] 0) (𝓝 (θ * unitBallVolume n * ENNReal.ofReal R ^ n)) := by
  intro N n U V x θ R hθ hR
  have hθ' : Tendsto (densityRatio n V.weight x) (𝓝[>] 0) (𝓝 θ) := hθ
  -- `c = ω_n R^n` is a positive finite constant.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : unitBallVolume n * ENNReal.ofReal R ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne')
  have hctop : unitBallVolume n * ENNReal.ofReal R ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- `t ↦ tR` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have hs : Tendsto (fun t : ℝ ↦ t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [zero_mul, id_eq] using
        ((tendsto_id.mono_left inf_le_left : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0)).mul_const R)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hR
  rw [mul_assoc]
  refine (ENNReal.Tendsto.mul_const (hθ'.comp hs) (Or.inr hctop)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  -- `V_{x,t}(B_R(0) × G) = t^{-n} μ_V(B_{tR}(x))`.
  have hpre : (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) ⁻¹'
      (closedBall (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) =
      closedBall x (t * R) ×ˢ univ := by
    ext z
    simp only [mem_preimage, mem_prod, mem_closedBall, dist_eq_norm, sub_zero, mem_univ,
      and_true, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
    exact inv_mul_le_iff₀ ht
  have hmeas : Measurable (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) := by
    fun_prop
  rw [Function.comp_apply, densityRatio, rescaledMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hmeas (measurableSet_closedBall.prod MeasurableSet.univ), hpre,
    ← V.weight_apply measurableSet_closedBall]
  -- `μ / (ω (tR)^n) · (ω R^n) = t^{-n} μ`, cancelling the positive finite `ω R^n`.
  have ha0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne'
  have hatop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul ht.le, mul_pow, mul_left_comm (unitBallVolume n),
    ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
  calc (ENNReal.ofReal t ^ n)⁻¹ * (unitBallVolume n * ENNReal.ofReal R ^ n)⁻¹ *
        V.weight (closedBall x (t * R)) * (unitBallVolume n * ENNReal.ofReal R ^ n)
      = (ENNReal.ofReal t ^ n)⁻¹ * V.weight (closedBall x (t * R)) *
          ((unitBallVolume n * ENNReal.ofReal R ^ n)⁻¹ *
            (unitBallVolume n * ENNReal.ofReal R ^ n)) := by ring
    _ = (ENNReal.ofReal t ^ n)⁻¹ * V.weight (closedBall x (t * R)) := by
      rw [ENNReal.inv_mul_cancel hc0 hctop, mul_one]
/-- Simon Ch. 8, 5.1–5.2 (p. 215), the change of variables behind the first variation of the
rescaled varifold `V_{x,t} = η_{x,t #} V`: for a `C¹` field `X` and `t > 0`,
`∫ div_S X dV_{x,t} = t⁻ⁿ δV(Y)` with `Y(z) = t X(t⁻¹(z - x))`, since `DY(z) = DX(t⁻¹(z - x))`. -/
theorem Submission.varifold_tangents_rdb_rescaled_integral_eq :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t : ℝ) (X : Euclidean N → Euclidean N), 0 < t → ContDiff ℝ 1 X → ∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x t) = t⁻¹ ^ n * V.firstVariation (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) := by
  intro N n U V x t X ht hX
  -- Step 1: `D(t X(t⁻¹(· - x)))(w) = t (DX(t⁻¹(w - x)) ∘ t⁻¹ id) = DX(t⁻¹(w - x))`.
  have hfderiv : ∀ w : Euclidean N,
      fderiv ℝ (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) w = fderiv ℝ X (t⁻¹ • (w - x)) := by
    intro w
    have hψ : HasFDerivAt (fun z : Euclidean N ↦ t⁻¹ • (z - x))
        (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N)) w :=
      ((hasFDerivAt_id w).sub_const x).const_smul t⁻¹
    have hXψ : HasFDerivAt X (fderiv ℝ X (t⁻¹ • (w - x))) (t⁻¹ • (w - x)) :=
      (hX.differentiable one_ne_zero _).hasFDerivAt
    have hY : HasFDerivAt (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x)))
        (t • (fderiv ℝ X (t⁻¹ • (w - x))).comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N))) w :=
      (hXψ.comp w hψ).const_smul t
    rw [hY.fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [smul_smul, mul_inv_cancel₀ ht.ne']
  -- Step 2: hence `div_S Y(z) = div_S X(t⁻¹(z - x))` for every `(z, S)`.
  have hdiv : ∀ z : Euclidean N × Grassmannian N n,
      Varifold.tangentialDivergence X (t⁻¹ • (z.1 - x)) z.2 =
        Varifold.tangentialDivergence (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) z.1 z.2 := by
    intro z
    simp only [Varifold.tangentialDivergence, Varifold.jacobian, hfderiv]
  -- Steps 3–5: pull out the factor `t⁻ⁿ`, then change variables along `(z, S) ↦ (t⁻¹(z - x), S)`.
  have hφ : Measurable (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) :=
    ((measurable_fst.sub_const x).const_smul t⁻¹).prodMk measurable_snd
  rw [rescaledMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    integral_map hφ.aemeasurable (Varifold.continuous_tangentialDivergence hX).aestronglyMeasurable]
  simp only [hdiv]
  rfl
/-- **Simon Ch. 8, 2.5 (p. 209), the supremum bound** (child `first_variation_sup_bound` of the
rescaled divergence bound for varifold tangents).  If `V` has locally bounded first variation,
`W ⊂⊂ U` is open and `Y` is a `C¹` field with `spt Y ⊆ W` and `|Y| ≤ K`, then
`|δV(Y)| ≤ K ‖δV‖(W)`: `Y` is a test field, `‖δV‖(W)` is the supremum in 2.5
(`firstVariationRieszMeasure_eq_norm`), and `K⁻¹ Y` is admissible in that supremum. -/
theorem Submission.varifold_tangents_rdb_firstVariation_le_variationMeasure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (W : Set (Euclidean N)) (Y : Euclidean N → Euclidean N) (K : ℝ), V.HasLocallyBoundedFirstVariation → IsOpen W → IsCompact (closure W) → closure W ⊆ U → ContDiff ℝ 1 Y → tsupport Y ⊆ W → (∀ z, ‖Y z‖ ≤ K) → ENNReal.ofReal |V.firstVariation Y| ≤ ENNReal.ofReal K * variationMeasure V W := by
  intro N n U V W Y K hV hW hWc hWU hY hYW hYK
  -- Step 1: `spt Y ⊆ W ⊆ closure W`, which is compact and contained in `U`, so `Y` is a test field.
  have hYc : HasCompactSupport Y :=
    hWc.of_isClosed_subset (isClosed_tsupport Y) (hYW.trans subset_closure)
  let Y' : Varifold.TestVectorField U := ⟨Y, hY, hYc, (hYW.trans subset_closure).trans hWU⟩
  -- Step 2: `‖δV‖(W)` is the supremum in 2.5.
  have hμW : variationMeasure V W = V.firstVariationNormOn W := by
    rw [variationMeasure, dite_eq_left hV]
    exact V.firstVariationRieszMeasure_eq_norm hV W hW ⟨hWc, hWU⟩
  rw [hμW]
  -- Step 3: `0 ≤ ‖Y 0‖ ≤ K`.
  have hK : 0 ≤ K := (norm_nonneg _).trans (hYK 0)
  rcases hK.eq_or_lt with rfl | hKpos
  · -- Step 4: if `K = 0` then `Y = 0` and `δV(Y) = 0`.
    have hY0 : Y = fun _ ↦ 0 := funext fun z ↦ norm_le_zero_iff.mp (hYK z)
    rw [hY0, V.firstVariation_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  · -- Step 5: `K⁻¹ Y` is a unit test field supported in `W`, so it enters the supremum.
    have hunit : (Y'.scale K⁻¹).UnitSupportedIn W := by
      refine ⟨(Y'.tsupport_scale_subset _).trans hYW, fun z ↦ ?_⟩
      change ‖K⁻¹ • Y z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKpos)]
      calc K⁻¹ * ‖Y z‖ ≤ K⁻¹ * K := mul_le_mul_of_nonneg_left (hYK z) (inv_nonneg.mpr hK)
        _ = 1 := inv_mul_cancel₀ hKpos.ne'
    have hle := V.le_firstVariationNormOn W _ hunit
    -- Step 6: `δV(K⁻¹ Y) = K⁻¹ δV(Y)`.
    change ENNReal.ofReal |V.firstVariation (K⁻¹ • Y)| ≤ _ at hle
    rw [V.firstVariation_const_smul K⁻¹ hY hYc, abs_mul, abs_of_pos (inv_pos.mpr hKpos)] at hle
    -- Step 7: `|δV(Y)| = K (K⁻¹ |δV(Y)|)`.
    calc ENNReal.ofReal |V.firstVariation Y|
        = ENNReal.ofReal K * ENNReal.ofReal (K⁻¹ * |V.firstVariation Y|) := by
          rw [← ENNReal.ofReal_mul hK, ← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul]
      _ ≤ ENNReal.ofReal K * V.firstVariationNormOn W := mul_le_mul_right hle _

/-- **Simon Ch. 8, 5.1–5.2, the first-variation bound for `V_{x,t}`** (child
`rescaled_divergence_bound` of `varifold_tangents`): if `X` is `C¹`, `spt X ⊆ B°_R(0)` and
`|X| ≤ M`, then `|∫ div_S X dV_{x,t}| ≤ M R^{n-1} (tR)^{1-n} ‖δV‖(B_{tR}(x))`.
With `ψ(z) = t⁻¹(z - x)` and `Y(z) = t X(ψ z)`, `∫ div_S X dV_{x,t} = t^{-n} δV(Y)`
(`varifold_tangents_rdb_rescaled_integral_eq`).  `Y` is `C¹`, `|Y| ≤ tM` and
`spt Y ⊆ ψ⁻¹(B°_R(0)) = B°_{tR}(x)`, an open set with compact closure inside `B_{tR}(x) ⊆ U`, so 2.5
gives `|δV(Y)| ≤ tM ‖δV‖(B°_{tR}(x))` (`varifold_tangents_rdb_firstVariation_le_variationMeasure`).
The rest is `ℝ≥0∞` arithmetic: `t^{-n} · tM · A = M (R^n / R) (tR · A / (tR)^n)`. -/
theorem Submission.varifold_tangents_rescaled_divergence_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R M : ℝ) (X : Euclidean N → Euclidean N), V.HasLocallyBoundedFirstVariation → 0 < t → 0 < R → closedBall x (t * R) ⊆ U → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball (0 : Euclidean N) R → (∀ y, ‖X y‖ ≤ M) → ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x t)| ≤ ENNReal.ofReal M * (ENNReal.ofReal R ^ n / ENNReal.ofReal R) * (ENNReal.ofReal (t * R) * variationMeasure V (closedBall x (t * R)) / ENNReal.ofReal (t * R) ^ n) := by
  intro N n U V x t R M X hV ht hR hBU hX _ hXR hXM
  rw [Submission.varifold_tangents_rdb_rescaled_integral_eq N n U V x t X ht hX]
  -- The pulled-back field `Y(z) = t X(t⁻¹(z - x))`: `C¹`, `|Y| ≤ tM`, `spt Y ⊆ B°_{tR}(x)`.
  have hψ : Continuous (fun z : Euclidean N ↦ t⁻¹ • (z - x)) := by fun_prop
  have hY : ContDiff ℝ 1 (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) := by fun_prop
  have hYM : ∀ z, ‖t • X (t⁻¹ • (z - x))‖ ≤ t * M := fun z ↦ by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (hXM _) ht.le
  have hYW : tsupport (fun z : Euclidean N ↦ t • X (t⁻¹ • (z - x))) ⊆ ball x (t * R) := by
    refine (tsupport_smul_subset_right (fun _ ↦ t) _).trans
      ((tsupport_comp_subset_preimage X hψ).trans fun z hz ↦ ?_)
    have hz' := mem_ball_zero_iff.1 (hXR hz)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht] at hz'
    exact mem_ball_iff_norm.2 hz'
  -- `W = B°_{tR}(x)` is open with compact closure inside `B_{tR}(x) ⊆ U`: 2.5 with `K = tM`.
  have hWcl : closure (ball x (t * R)) ⊆ closedBall x (t * R) := closure_ball_subset_closedBall
  have hδ := Submission.varifold_tangents_rdb_firstVariation_le_variationMeasure N n U V
    (ball x (t * R)) _ (t * M) hV isOpen_ball
    ((isCompact_closedBall x (t * R)).of_isClosed_subset isClosed_closure hWcl)
    (hWcl.trans hBU) hY hYW hYM
  -- `ℝ≥0∞` arithmetic: `ofReal t, ofReal R ∈ (0, ∞)`; insert `(R R⁻¹)(R R⁻¹)^n = 1`, rearrange.
  have htn : 0 ≤ t⁻¹ ^ n := pow_nonneg (inv_nonneg.2 ht.le) n
  have hr : ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top
  rw [abs_mul, abs_of_nonneg htn, ENNReal.ofReal_mul htn, ENNReal.ofReal_pow (inv_nonneg.2 ht.le),
    ENNReal.ofReal_inv_of_pos ht, ENNReal.ofReal_mul ht.le, mul_pow, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 ht).ne'))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), ENNReal.inv_pow, ENNReal.inv_pow]
  calc (ENNReal.ofReal t)⁻¹ ^ n * ENNReal.ofReal |V.firstVariation fun z ↦ t • X (t⁻¹ • (z - x))|
      ≤ (ENNReal.ofReal t)⁻¹ ^ n *
          (ENNReal.ofReal t * ENNReal.ofReal M * variationMeasure V (closedBall x (t * R))) := by
        gcongr
        rw [← ENNReal.ofReal_mul ht.le]
        refine hδ.trans ?_
        gcongr
        exact ball_subset_closedBall
    _ = (ENNReal.ofReal t)⁻¹ ^ n *
          (ENNReal.ofReal t * ENNReal.ofReal M * variationMeasure V (closedBall x (t * R))) *
          (ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹ *
            (ENNReal.ofReal R * (ENNReal.ofReal R)⁻¹) ^ n) := by
        rw [hr, one_pow, mul_one, mul_one]
    _ = _ := by ring

/-- **Simon Ch. 8, 5.4 (p. 215), varifold tangents are stationary** (child `limit_stationary` of
`varifold_tangents`): if `V` has locally bounded first variation, `x ∈ U`,
`γ(ρ) = ρ^{1-n} ‖δV‖(B_ρ(x)) → 0` as `ρ ↓ 0` (5.1) and `C ∈ VarTan(V, x)`, then `C` is stationary.
For `X ∈ K(ℝ^N;ℝ^N)`, `div_S X` is continuous with compact support, so vague convergence gives
`I_j = ∫ div_S X dV_{x,t_j} → δC(X)`.  With `spt X ⊆ B°_R(0)`, `|X| ≤ M` and `B_r(x) ⊆ U`, for large
`j` the rescaled divergence bound (`varifold_tangents_rescaled_divergence_bound`) gives
`|I_j| ≤ M (R^n / R) γ(t_j R) → 0`, hence `δC(X) = 0`. -/
theorem Submission.varifold_tangents_limit_stationary :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (C : Varifold N n (univ : Set (Euclidean N))), V.HasLocallyBoundedFirstVariation → x ∈ U → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → IsVarifoldTangent V x C → C.Stationary := by
  rintro N n U V x C hV hx h51 ⟨t, ht, ht0, hconv⟩ X
  -- Step 1: `div_S X ∈ C_c(Gₙ(ℝ^N))`, so `I_j = ∫ div_S X dV_{x,t_j} → δC(X)`.
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    ⟨⟨fun z ↦ Varifold.tangentialDivergence X z.1 z.2,
      Varifold.continuous_tangentialDivergence X.contDiff⟩,
      Varifold.hasCompactSupport_tangentialDivergence X X.compactSupport⟩
  have hI : Tendsto (fun j ↦ ∫ z, Varifold.tangentialDivergence X z.1 z.2
      ∂(rescaledMeasure V x (t j))) atTop (𝓝 (C.firstVariation X)) := hconv f
  -- Step 2: `spt X ⊆ B°_R(0)` with `R > 0`, `|X| ≤ M`, and `B_r(x) ⊆ U` with `r > 0`.
  obtain ⟨R, hR, hXR⟩ := X.compactSupport.isBounded.subset_ball_lt 0 0
  obtain ⟨M, hM⟩ := X.compactSupport.exists_bound_of_continuous X.contDiff.continuous
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (V.isOpen_domain.mem_nhds hx)
  -- Step 3: `t_j R → 0`, so for large `j`, `B_{t_j R}(x) ⊆ U` and `ofReal |I_j| ≤ K γ(t_j R)`.
  have htR : Tendsto (fun j ↦ t j * R) atTop (𝓝 0) := by
    simpa using ht0.mul_const R
  obtain ⟨K, hK, hbound⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ᶠ j in atTop,
      ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x (t j))| ≤
        K * (ENNReal.ofReal (t j * R) * variationMeasure V (closedBall x (t j * R)) /
          ENNReal.ofReal (t j * R) ^ n) := by
    refine ⟨ENNReal.ofReal M * (ENNReal.ofReal R ^ n / ENNReal.ofReal R),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.ofReal_pos.2 hR).ne'), ?_⟩
    filter_upwards [htR.eventually (eventually_lt_nhds hr)] with j hj
    exact Submission.varifold_tangents_rescaled_divergence_bound N n U V x (t j) R M X hV (ht j) hR
      ((closedBall_subset_closedBall hj.le).trans hrU) X.contDiff X.compactSupport hXR hM
  -- Step 4: `t_j R → 0⁺`, so `K γ(t_j R) → K · 0 = 0` by (5.1); squeeze, then `|I_j| → 0`.
  have hγ := h51.comp (tendsto_nhdsWithin_iff.2
    ⟨htR, Eventually.of_forall fun j ↦ mul_pos (ht j) hR⟩)
  have hKγ := ENNReal.Tendsto.const_mul hγ (Or.inr hK)
  rw [mul_zero] at hKγ
  have habs := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKγ
    (Eventually.of_forall fun _ ↦ zero_le) hbound
  have habs' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp habs
  rw [ENNReal.toReal_zero] at habs'
  have hI0 : Tendsto (fun j ↦ ∫ z, Varifold.tangentialDivergence X z.1 z.2
      ∂(rescaledMeasure V x (t j))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j ↦ (Real.norm_eq_abs _).le)
      (habs'.congr fun j ↦ ENNReal.toReal_ofReal (abs_nonneg _))
  -- Step 5: uniqueness of limits in `ℝ`.
  exact tendsto_nhds_unique hI hI0

/-- **Simon Ch. 8, 5.2 (centre corrected to `0`), ball masses of a varifold tangent** (child
`limit_ball_mass` of `varifold_tangents`): if `Θ^n(μ_V, x) = θ₀` and `C ∈ VarTan(V, x)`, then
`μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every `ρ > 0`.
Write `L(r) = θ₀ ω_n r^n` and `K_r = B_r(0) × G(N,n)`.  For the radii `t_j > 0`, `t_j → 0` of `C`,
`varifold_tangents_rescaled_ball_mass_tendsto` gives `V_{x,t_j}(K_r) → L(r) < ∞` for `r > 0`.  As
`C(K_ρ') = μ_C(B_ρ'(0)) < ∞`, `varifold_tangents_lbm_vague_cylinder_bounds` (with `a = ρ`, `b = ρ'`)
gives `μ_C(B_ρ(0)) ≤ L(ρ')` and `L(ρ) ≤ μ_C(B_ρ'(0))` for every `ρ' > ρ`.  Let `ρ' ↓ ρ`: `L` is
continuous, and `μ_C(B_ρ'(0)) → μ_C(B_ρ(0))` by continuity from above, since
`⋂_{ρ' > ρ} B_ρ'(0) = B_ρ(0)`. -/
theorem Submission.varifold_tangents_limit_ball_mass :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (θ₀ : ℝ) (C : Varifold N n (univ : Set (Euclidean N))), HasDensity n V.weight x (ENNReal.ofReal θ₀) → IsVarifoldTangent V x C → ∀ ρ : ℝ, 0 < ρ → C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n := by
  intro N n U V x θ₀ C hθ hC ρ hρ
  obtain ⟨t, ht_pos, ht_lim, hconv⟩ := hC
  set L : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal r ^ n
  -- `t j → 0⁺`, so `V_{x,t_j}(B_r(0) × G(N,n)) → L r < ∞` for every `r > 0`.
  have ht : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨ht_lim, Eventually.of_forall ht_pos⟩
  have hmass : ∀ r : ℝ, 0 < r → Tendsto (fun j ↦ rescaledMeasure V x (t j)
      (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 (L r)) :=
    fun r hr ↦ (Submission.varifold_tangents_rescaled_ball_mass_tendsto N n U V x _ r hθ hr).comp ht
  have hc : ENNReal.ofReal θ₀ * unitBallVolume n ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hL : ∀ r, L r ≠ ∞ := fun r ↦ ENNReal.mul_ne_top hc (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- `C(B_r(0) × G(N,n)) = μ_C(B_r(0)) < ∞`, as `B_r(0)` is compact.
  have hCK : ∀ r : ℝ, C.measure (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n)))
      = C.weight (closedBall 0 r) := fun r ↦ (C.weight_apply measurableSet_closedBall).symm
  have hCtop : ∀ r : ℝ, C.weight (closedBall 0 r) ≠ ∞ :=
    fun r ↦ C.weight_finite_on_compact _ (isCompact_closedBall 0 r) (subset_univ _)
  -- For `ρ' > ρ`: `μ_C(B_ρ(0)) ≤ L ρ'` and `L ρ ≤ μ_C(B_ρ'(0))`.
  have hbd : ∀ ρ' > ρ, C.weight (closedBall 0 ρ) ≤ L ρ' ∧ L ρ ≤ C.weight (closedBall 0 ρ') := by
    intro ρ' hρ'
    have := Submission.varifold_tangents_lbm_vague_cylinder_bounds N n _ C.measure ρ ρ' (L ρ)
      (L ρ') hconv hρ' (hCK ρ' ▸ hCtop ρ') (hmass ρ hρ) (hmass ρ' (hρ.trans hρ')) (hL ρ')
    rwa [hCK, hCK] at this
  -- Let `ρ' ↓ ρ`: `L` is continuous and `r ↦ μ_C(B_r(0))` is continuous from the right.
  have hLlim : Tendsto L (𝓝[>] ρ) (𝓝 (L ρ)) :=
    ((ENNReal.continuous_const_mul hc).comp
      ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hClim : Tendsto (fun r ↦ C.weight (closedBall (0 : Euclidean N) r)) (𝓝[>] ρ)
      (𝓝 (C.weight (closedBall 0 ρ))) := by
    have := tendsto_measure_biInter_gt (μ := C.weight) (s := closedBall (0 : Euclidean N)) (a := ρ)
      (fun r _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun i j _ hij ↦ closedBall_subset_closedBall hij) ⟨ρ + 1, by linarith, hCtop _⟩
    rwa [biInter_gt_closedBall] at this
  have hev : ∀ᶠ ρ' in 𝓝[>] ρ, ρ < ρ' := self_mem_nhdsWithin
  exact le_antisymm (ge_of_tendsto hLlim (hev.mono fun ρ' h ↦ (hbd ρ' h).1))
    (ge_of_tendsto hClim (hev.mono fun ρ' h ↦ (hbd ρ' h).2))

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
