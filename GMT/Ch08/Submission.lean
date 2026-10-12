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

/-- Integration against a measure that is `θ H^n ⌞ M` on Borel sets (used in the proof of Simon
Ch. 8, 1.2, where `μ_V = θ H^n ⌞ M`): if `μ B = ∫⁻_{B ∩ M} θ dH^n` for every Borel set `B`,
`θ > 0` on `M`, `θ` is `H^n`-integrable on `M ∩ K` for a Borel set `K` and `h` vanishes off `K`,
then `∫ h dμ = ∫_M h θ dH^n`.  `h` is arbitrary: no measurability or integrability is assumed. -/
theorem Submission.frt_wat_integral_eq_setIntegral_mul :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M K : Set (Euclidean N)) (θ h : Euclidean N → ℝ), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → MeasurableSet K → IntegrableOn θ (M ∩ K) μHE[n] → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ y in B ∩ M, ENNReal.ofReal (θ y) ∂μHE[n]) → (∀ z, z ∉ K → h z = 0) → ∫ z, h z ∂μ = ∫ z in M, h z * θ z ∂μHE[n] := by
  intro N n μ M K θ h hM hθ hK hθK hμ hh
  -- Step 1: `μ ⌞ K = (H^n ⌞ (M ∩ K)).withDensity (ofReal ∘ θ)`, compared on Borel sets `B`.
  have hrestr : μ.restrict K =
      ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ K)).withDensity
        (fun y ↦ ENNReal.ofReal (θ y)) := by
    ext B hB
    rw [Measure.restrict_apply hB, hμ _ (hB.inter hK), withDensity_apply _ hB,
      Measure.restrict_restrict hB, inter_assoc, inter_comm K M]
  -- `M ∩ K` is `H^n`-null-measurable, so `H^n ⌞ (M ∩ K)`-a.e. point lies in `M ∩ K`.
  have hMK : NullMeasurableSet (M ∩ K) (μHE[n] : Measure (Euclidean N)) :=
    hM.inter hK.nullMeasurableSet
  calc ∫ z, h z ∂μ = ∫ z in K, h z ∂μ :=
        -- Step 2: `h = 0` off `K`.
        (setIntegral_eq_integral_of_forall_compl_eq_zero hh).symm
    _ = ∫ z, (ENNReal.ofReal (θ z)).toReal • h z
          ∂((μHE[n] : Measure (Euclidean N)).restrict (M ∩ K)) := by
        -- Step 3: the density `ofReal ∘ θ` is a.e.-measurable (`θ` is integrable) and finite.
        rw [hrestr, integral_withDensity_eq_integral_toReal_smul₀
          (Integrable.aemeasurable hθK).ennreal_ofReal
          (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    _ = ∫ z in M ∩ K, h z * θ z ∂μHE[n] := by
        -- Step 4: `(ofReal (θ z)).toReal = θ z` for a.e. `z ∈ M ∩ K`, as `θ > 0` on `M`.
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem₀ hMK] with z hz
        rw [ENNReal.toReal_ofReal (hθ z hz.1).le, smul_eq_mul, mul_comm]
    _ = ∫ z in M, h z * θ z ∂μHE[n] :=
        -- Step 5: `h θ = 0` on `M \ (M ∩ K)` and `M` is null-measurable.
        (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM inter_subset_left
          (Eventually.of_forall fun z hz ↦ by
            rw [hh z fun hzK ↦ hz.2 ⟨hz.1, hzK⟩, zero_mul])).symm
/-- Dilation change of variables for `H^n` set integrals over blow-up images (the homothety step
behind Simon Ch. 8, 1.2 with Ch. 3, 1.7): for `r > 0`, `η = η_{x,r}` (`η y = r⁻¹ • (y - x)`), an
arbitrary set `M` and an arbitrary `F : ℝ^N → ℝ`, `∫_{η(M)} F dH^n = r⁻¹ ^ n ∫_M F ∘ η dH^n`. -/
theorem Submission.frt_wat_setIntegral_blowUpMap_image :
    ∀ (N n : ℕ) (x : Euclidean N) (r : ℝ) (M : Set (Euclidean N)) (F : Euclidean N → ℝ), 0 < r → ∫ y in Chapter03.blowUpMap x r '' M, F y ∂μHE[n] = r⁻¹ ^ n * ∫ z in M, F (Chapter03.blowUpMap x r z) ∂μHE[n] := by
  intro N n x r M F hr
  -- Step 1: `η = blowUpMap x r` is a homeomorphism (inverse `y ↦ x + r • y`), hence an
  -- injective measurable embedding.
  let η : Euclidean N ≃ₜ Euclidean N :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hη : (η : Euclidean N → Euclidean N) = Chapter03.blowUpMap x r := rfl
  have hemb : MeasurableEmbedding η := η.measurableEmbedding
  -- Step 2: `H^n(η⁻¹ S) = r ^ n H^n(S)` for every set `S`, as `η⁻¹ S = x + r • S`.
  have hpre : ∀ S : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) (η ⁻¹' S) =
      ENNReal.ofReal (r ^ n) * μHE[n] S := by
    intro S
    have hS : (η : Euclidean N → Euclidean N) ⁻¹' S = (fun y ↦ x + y) '' (r • S) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_smul_set]
      constructor
      · intro h
        refine ⟨r • (r⁻¹ • (y - x)), ⟨_, h, rfl⟩, ?_⟩
        simp [smul_smul, mul_inv_cancel₀ hr.ne']
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        simpa [η, smul_smul, inv_mul_cancel₀ hr.ne'] using hs
    rw [hS, (isometry_add_left x).euclideanHausdorffMeasure_image,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne', ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr.le, ENNReal.ofReal_pow hr.le]
  -- Step 3: `H^n.map η = r ^ n • H^n` (`Measure.ext` on Borel sets).
  have hmap : (μHE[n] : Measure (Euclidean N)).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)) := by
    ext S hS
    rw [Measure.map_apply hemb.measurable hS, hpre, Measure.smul_apply, smul_eq_mul]
  -- Step 4: `(H^n ⌞ M).map η = r ^ n • H^n ⌞ η(M)`, using `η⁻¹(η(M)) = M`.
  have hres : ((μHE[n] : Measure (Euclidean N)).restrict M).map η =
      ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Euclidean N)).restrict (η '' M) := by
    rw [← Measure.restrict_smul, ← hmap, hemb.restrict_map, Set.preimage_image_eq M η.injective]
  -- Step 5: `∫_M F ∘ η dH^n = r ^ n ∫_{η(M)} F dH^n` (no measurability of `M` or `F` needed).
  have hcov : ∫ z in M, F (η z) ∂μHE[n] = r ^ n * ∫ y in η '' M, F y ∂μHE[n] := by
    rw [← hemb.integral_map, hres, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_nonneg hr.le n), smul_eq_mul]
  -- Step 6: multiply by `r⁻¹ ^ n`, using `r⁻¹ ^ n * r ^ n = 1`.
  rw [← hη, hcov, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
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

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
