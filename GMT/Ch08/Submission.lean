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

/-- Lebesgue density one of `H^n` on an arbitrary subset `T` of an `n`-plane (Simon Ch. 8, proof of
1.2, via the Lebesgue density theorem in `ℝ^n`): outside an `H^n`-null set `Z`, every `a ∈ T` has
`Θ^n(H^n ⌞ T, a) = 1`. -/
theorem Submission.frt_plane_subset_hasDensity_one :
    ∀ (N n : ℕ) (P : Grassmannian N n) (T : Set (Euclidean N)), T ⊆ (P.plane : Set (Euclidean N)) → ∃ Z : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) Z = 0 ∧ ∀ a ∈ T, a ∉ Z → HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict T) a 1 := by
  intro N n P T hT
  -- Step 1: an isometry `ι : ℝ^n → ℝ^N` onto the plane, from an orthonormal basis of `P.plane`.
  obtain ⟨ι, hι, hsurj⟩ : ∃ ι : EuclideanSpace ℝ (Fin n) → Euclidean N, Isometry ι ∧
      ∀ a ∈ (P.plane : Set (Euclidean N)), ∃ y, ι y = a := by
    let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] P.plane :=
      ((stdOrthonormalBasis ℝ P.plane).reindex (finCongr P.finrank_plane)).repr.symm
    exact ⟨P.plane.subtypeₗᵢ.comp e.toLinearIsometry, LinearIsometry.isometry _,
      fun a ha ↦ ⟨e.symm ⟨a, ha⟩, by simp⟩⟩
  -- Step 2: `H^n(ι B) = L^n(B)` for every `B ⊆ ℝ^n`.
  have hmeas : ∀ B : Set (EuclideanSpace ℝ (Fin n)),
      (μHE[n] : Measure (Euclidean N)) (ι '' B) = volume B := fun B ↦ by
    rw [hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Step 3: `ι(ι⁻¹(T) ∩ B_s(y)) = B_s(ι y) ∩ T`.
  have himg : ∀ y s, ι '' (ι ⁻¹' T ∩ closedBall y s) = closedBall (ι y) s ∩ T := by
    intro y s
    ext a
    constructor
    · rintro ⟨z, ⟨hzT, hz⟩, rfl⟩
      exact ⟨mem_closedBall.mpr ((hι.dist_eq z y).trans_le (mem_closedBall.mp hz)), hzT⟩
    · rintro ⟨ha, haT⟩
      obtain ⟨z, rfl⟩ := hsurj a (hT haT)
      exact ⟨z, ⟨haT, mem_closedBall.mpr ((hι.dist_eq z y).symm.trans_le (mem_closedBall.mp ha))⟩,
        rfl⟩
  -- Step 4: Lebesgue density theorem for `ι⁻¹(T)`, and a measurable null hull `E` of its bad set.
  obtain ⟨E, hbad, hEm, hE0⟩ := exists_measurable_superset_of_null (ae_iff.mp
    (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (ι ⁻¹' T)))
  rw [Measure.restrict_apply hEm] at hE0
  -- Step 5: `Z = ι(E ∩ ι⁻¹(T))` is `H^n`-null.
  refine ⟨ι '' (E ∩ ι ⁻¹' T), (hmeas _).trans hE0, ?_⟩
  -- Step 6: at `a = ι y ∈ T ∖ Z` the density ratio is `L^n(ι⁻¹(T) ∩ B_s(y)) / L^n(B_s(y)) → 1`.
  intro a haT haZ
  obtain ⟨y, rfl⟩ := hsurj a (hT haT)
  have hy : Tendsto (fun r ↦ volume (ι ⁻¹' T ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1) := by
    by_contra h
    exact haZ ⟨y, ⟨hbad h, haT⟩, rfl⟩
  refine hy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [densityRatio, Measure.restrict_apply measurableSet_closedBall, ← himg y s, hmeas,
    Measure.addHaar_closedBall volume y hs.le, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hs.le,
    unitBallVolume, mul_comm (ENNReal.ofReal s ^ n)]
/-- Hausdorff-measure comparison between an `L`-graph and its projection (used for the density-one
property of `H^n` on the carrier in the proof of Simon Ch. 8, 1.2; cf. Ch. 3, 1.6): if
`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ S` and `β = (1 + L²)^{1/2}`, then `p_P` is
`1`-Lipschitz, and injective on `S` with a `β`-Lipschitz inverse, so for `x ∈ S` and `r ∈ ℝ`
`H^n(p_P(S) ∩ B_{r/β}(p_P x)) ≤ H^n(S ∩ B_r(x)) ≤ β^n H^n(p_P(S) ∩ B_r(p_P x))`, and
`H^n(S ∩ p_P⁻¹(Y)) ≤ β^n H^n(Y)` for every `Y ⊆ ℝ^N`. -/
theorem Submission.frt_lipschitz_graph_hausdorff_compare :
    ∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (S : Set (Euclidean N)), 0 ≤ L → (∀ y ∈ S, ∀ z ∈ S, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → (∀ x ∈ S, ∀ r : ℝ, (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2))) ≤ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ∧ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) r)) ∧ ∀ Y : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) (S ∩ Grassmannian.project P ⁻¹' Y) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
  intro N n P L S hL hgraph
  -- Step 1: `β = √(1 + L²)` satisfies `β ≥ 1 > 0`.
  have hβ0 : 0 < Real.sqrt (1 + L ^ 2) :=
    one_pos.trans_le (Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg L)))
  -- Step 2: `p_P` is linear.
  have hsub : ∀ u v : Euclidean N,
      Grassmannian.project P (u - v) = Grassmannian.project P u - Grassmannian.project P v :=
    fun u v ↦ map_sub P.projectionLinearMap u v
  -- Step 3: `p_P` is symmetric and idempotent, so `|v|² = |p_P v|² + |v - p_P v|²`; hence
  -- `|p_P v| ≤ |v|` and `p_P` is `1`-Lipschitz.
  have hpyth : ∀ v : Euclidean N,
      ‖v‖ ^ 2 = ‖Grassmannian.project P v‖ ^ 2 + ‖v - Grassmannian.project P v‖ ^ 2 := by
    intro v
    have hker : Grassmannian.project P (v - Grassmannian.project P v) = 0 := by
      rw [hsub, Grassmannian.project_project, sub_self]
    have horth : inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) = 0 := by
      rw [show inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) =
          inner ℝ v (Grassmannian.project P (v - Grassmannian.project P v)) from
        P.projectionLinearMap_isSymmetric v (v - Grassmannian.project P v), hker, inner_zero_right]
    have h := norm_add_sq_real (Grassmannian.project P v) (v - Grassmannian.project P v)
    rw [horth, add_sub_cancel] at h
    linarith
  have hnorm : ∀ v : Euclidean N, ‖Grassmannian.project P v‖ ≤ ‖v‖ := by
    intro v
    have h := hpyth v
    nlinarith [norm_nonneg v, norm_nonneg (Grassmannian.project P v),
      sq_nonneg ‖v - Grassmannian.project P v‖]
  have hlip : ∀ A : Set (Euclidean N), LipschitzOnWith 1 (Grassmannian.project P) A := by
    refine fun A ↦ LipschitzOnWith.mk_one fun u _ v _ ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← hsub]
    exact hnorm (u - v)
  -- Step 4: on `S`, `|y - z|² ≤ (1 + L²) |p_P(y - z)|²`, i.e. `|y - z| ≤ β |p_P y - p_P z|`.
  have hkey : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤
      Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P y - Grassmannian.project P z‖ := by
    intro y hy z hz
    rw [← hsub]
    have h1 := hpyth (y - z)
    have h2 := hgraph y hy z hz
    have h3 : ‖(y - z) - Grassmannian.project P (y - z)‖ ^ 2 ≤
        (L * ‖Grassmannian.project P (y - z)‖) ^ 2 := by
      gcongr
    have h4 : ‖y - z‖ ^ 2 ≤ (1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ ^ 2 := by
      nlinarith
    calc ‖y - z‖ = Real.sqrt (‖y - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ ^ 2) := Real.sqrt_le_sqrt h4
      _ = Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P (y - z)‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  -- Step 5: `p_P` is injective on `S`, and `h = invFunOn p_P S` is `β`-Lipschitz on `p_P(S)` with
  -- `h (p_P y) = y` for `y ∈ S`.
  have hinj : InjOn (Grassmannian.project P) S := by
    intro y hy z hz hyz
    have h := hkey y hy z hz
    rw [hyz, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hleft : ∀ y ∈ S,
      Function.invFunOn (Grassmannian.project P) S (Grassmannian.project P y) = y :=
    fun y hy ↦ hinj.leftInvOn_invFunOn hy
  have hinv : LipschitzOnWith (Real.toNNReal (Real.sqrt (1 + L ^ 2)))
      (Function.invFunOn (Grassmannian.project P) S) (Grassmannian.project P '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [hleft y hy, hleft z hz, dist_eq_norm, dist_eq_norm]
    exact hkey y hy z hz
  -- Steps 6–7 (b): `S ∩ p_P⁻¹(Y) = h(p_P(S ∩ p_P⁻¹(Y)))` and `p_P(S ∩ p_P⁻¹(Y)) ⊆ Y`, so the
  -- Lipschitz image bound for `h` gives `H^n(S ∩ p_P⁻¹(Y)) ≤ β^n H^n(Y)`.
  have hb : ∀ Y : Set (Euclidean N), (μHE[n] : Measure (Euclidean N))
      (S ∩ Grassmannian.project P ⁻¹' Y) ≤
        ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
    intro Y
    calc (μHE[n] : Measure (Euclidean N)) (S ∩ Grassmannian.project P ⁻¹' Y)
        = (μHE[n] : Measure (Euclidean N)) (Function.invFunOn (Grassmannian.project P) S ''
            (Grassmannian.project P '' (S ∩ Grassmannian.project P ⁻¹' Y))) := by
          rw [hinj.invFunOn_image inter_subset_left]
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N))
            (Grassmannian.project P '' (S ∩ Grassmannian.project P ⁻¹' Y)) :=
          Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hinv.mono (image_mono inter_subset_left))
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y := by
          gcongr
          exact (image_mono inter_subset_right).trans (image_preimage_subset _ _)
  refine ⟨fun x hx r ↦ ⟨?_, ?_⟩, hb⟩
  · -- Step 8: `p_P(S) ∩ B_{r/β}(p_P x) ⊆ p_P(S ∩ B_r(x))`, then the `1`-Lipschitz bound for `p_P`.
    have hsubset : Grassmannian.project P '' S ∩
        closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2)) ⊆
          Grassmannian.project P '' (S ∩ closedBall x r) := by
      rintro _ ⟨⟨z, hz, rfl⟩, hzr⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hzr ⊢
      calc ‖z - x‖
          ≤ Real.sqrt (1 + L ^ 2) * ‖Grassmannian.project P z - Grassmannian.project P x‖ :=
            hkey z hz x hx
        _ ≤ Real.sqrt (1 + L ^ 2) * (r / Real.sqrt (1 + L ^ 2)) :=
            mul_le_mul_of_nonneg_left hzr hβ0.le
        _ = r := mul_div_cancel₀ r hβ0.ne'
    calc (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' S ∩
          closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2)))
        ≤ (μHE[n] : Measure (Euclidean N)) (Grassmannian.project P '' (S ∩ closedBall x r)) :=
          measure_mono hsubset
      _ ≤ ((1 : NNReal) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) :=
          Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hlip _)
      _ = (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) := by
          rw [ENNReal.coe_one, one_pow, one_mul]
  · -- Step 9: `S ∩ B_r(x) ⊆ S ∩ p_P⁻¹(p_P(S) ∩ B_r(p_P x))`, as `|p_P z - p_P x| ≤ |z - x|`;
    -- then (b).
    have hsubset : S ∩ closedBall x r ⊆ S ∩ Grassmannian.project P ⁻¹'
        (Grassmannian.project P '' S ∩ closedBall (Grassmannian.project P x) r) := by
      rintro z ⟨hz, hzr⟩
      refine ⟨hz, mem_image_of_mem _ hz, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzr ⊢
      rw [← hsub]
      exact (hnorm (z - x)).trans hzr
    exact (measure_mono hsubset).trans (hb _)

/-- Two-sided density bounds on a closed Lipschitz-graph piece (Simon Ch. 8, proof of 1.2, the
density-one step for `H^n ⌞ A` on one graph piece `Γ`): let `H^n(A) < ∞` with `A` `H^n`-measurable,
`L ≥ 0`, `β = (1 + L²)^{1/2}`, and let `Γ` be closed with `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|`
for `y, z ∈ Γ`.  Then for `(H^n ⌞ A) ⌞ Γ`-a.e. `x`, with `λ = H^n ⌞ A`,
`β^{-n} ≤ liminf_{r↓0} λ(B_r(x)) / (ω_n r^n)` and `limsup_{r↓0} λ(B_r(x)) / (ω_n r^n) ≤ β^n`. -/
theorem Submission.frt_graph_piece_density_bounds :
    ∀ (N n : ℕ) (A Γ : Set (Euclidean N)) (P : Grassmannian N n) (L : ℝ), μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → 0 ≤ L → IsClosed Γ → (∀ y ∈ Γ, ∀ z ∈ Γ, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → ∀ᵐ x ∂((μHE[n] : Measure (Euclidean N)).restrict A).restrict Γ, (ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n)⁻¹ ≤ liminf (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ∧ limsup (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n := by
  intro N n A Γ P L hA hAm hL hΓ hgraph
  set H : Measure (Euclidean N) := (μHE[n] : Measure (Euclidean N))
  set β : ℝ := Real.sqrt (1 + L ^ 2)
  set c : ℝ≥0∞ := ENNReal.ofReal β ^ n with hc
  set ω : ℝ≥0∞ := unitBallVolume n
  set lam : Measure (Euclidean N) := H.restrict A with hlam
  -- Step 1: `β > 0`, so `c = β^n ∈ (0, ∞)`; and `λ = H^n ⌞ A` is a finite measure.
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hc0 : c ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hβ0).ne'
  have hctop : c ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 hA
  -- Step 2: `A_c = A ∩ Γ` is an `L`-graph, and `T = p_P(A_c)` lies in `P.plane`.
  set Ac : Set (Euclidean N) := A ∩ Γ with hAc
  set T : Set (Euclidean N) := Grassmannian.project P '' Ac
  have hTP : T ⊆ (P.plane : Set (Euclidean N)) := by
    rintro _ ⟨y, -, rfl⟩
    exact LinearMap.mem_range_self _ y
  -- Steps 3–4: the plane density result gives an `H^n`-null `Z` off which `H^n ⌞ T` has density
  -- one on `T`; the graph comparison gives the ball bounds (i)/(ii) for `A_c`, and
  -- `H^n(A_c ∩ p_P⁻¹(Z)) ≤ c H^n(Z) = 0`.
  obtain ⟨Z, hZ0, hZ⟩ := Submission.frt_plane_subset_hasDensity_one N n P T hTP
  obtain ⟨hball, hpre⟩ := Submission.frt_lipschitz_graph_hausdorff_compare N n P L Ac hL
    (fun y hy z hz ↦ hgraph y hy.2 z hz.2)
  have hX0 : H (Ac ∩ Grassmannian.project P ⁻¹' Z) = 0 := by
    have h := hpre Z
    rw [hZ0, mul_zero] at h
    exact le_antisymm h bot_le
  -- Step 5: Besicovitch differentiation, `λ(Γ ∩ B_r(x)) / λ(B_r(x)) → 1` for `λ ⌞ Γ`-a.e. `x`.
  have hbes := Besicovitch.ae_tendsto_measure_inter_div lam Γ
  -- Step 6: `λ ⌞ Γ = H^n ⌞ (Γ ∩ A)`, so `λ ⌞ Γ`-a.e. `x` lies in `A_c` and off `A_c ∩ p_P⁻¹(Z)`.
  have hrr : lam.restrict Γ = H.restrict (Γ ∩ A) := Measure.restrict_restrict hΓ.measurableSet
  have hmem : ∀ᵐ x ∂lam.restrict Γ, x ∈ Γ ∩ A := by
    rw [hrr]
    exact ae_restrict_mem₀ (hΓ.measurableSet.nullMeasurableSet.inter hAm)
  have hnotX : ∀ᵐ x ∂lam.restrict Γ, x ∉ Ac ∩ Grassmannian.project P ⁻¹' Z := by
    rw [hrr]
    exact ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hX0)
  filter_upwards [hbes, hmem, hnotX] with x hq hxm hxX
  have hxAc : x ∈ Ac := ⟨hxm.2, hxm.1⟩
  -- Step 7: `a = p_P x ∈ T ∖ Z`, so `g(s) = H^n(T ∩ B_s(a)) / (ω_n s^n) → 1` as `s ↓ 0`.
  set a := Grassmannian.project P x
  have hg : Tendsto (densityRatio n (H.restrict T) a) (𝓝[>] 0) (𝓝 1) :=
    hZ a ⟨x, hxAc, rfl⟩ fun h ↦ hxX ⟨hxAc, h⟩
  have hgeq : ∀ s, densityRatio n (H.restrict T) a s =
      H (T ∩ closedBall a s) / (ω * ENNReal.ofReal s ^ n) := by
    intro s
    rw [densityRatio, Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- Step 8: the key identity `λ(Γ ∩ B_r(x)) = H^n(A_c ∩ B_r(x))`.
  have hkey : ∀ r, lam (Γ ∩ closedBall x r) = H (Ac ∩ closedBall x r) := by
    intro r
    rw [hlam, Measure.restrict_apply (hΓ.measurableSet.inter measurableSet_closedBall)]
    congr 1
    ext y
    simp only [mem_inter_iff, hAc]
    tauto
  constructor
  · -- Step 9: for `r > 0`, `densityRatio n λ x r ≥ c⁻¹ g(r/β)`, since `ω_n r^n = c ω_n (r/β)^n`
    -- and `λ(B_r(x)) ≥ H^n(A_c ∩ B_r(x)) ≥ H^n(T ∩ B_{r/β}(a))`; and `c⁻¹ g(r/β) → c⁻¹`.
    have hdiv : Tendsto (fun r : ℝ ↦ r / β) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun r : ℝ ↦ r / β) (𝓝 0) (𝓝 (0 / β)) := tendsto_id.div_const β
        rw [zero_div] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using div_pos hr hβ0
    have hlim : Tendsto (fun r ↦ c⁻¹ * densityRatio n (H.restrict T) a (r / β)) (𝓝[>] 0)
        (𝓝 (c⁻¹ * 1)) :=
      ENNReal.Tendsto.const_mul (hg.comp hdiv) (Or.inr (ENNReal.inv_ne_top.2 hc0))
    rw [mul_one] at hlim
    have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        c⁻¹ * densityRatio n (H.restrict T) a (r / β) ≤ densityRatio n lam x r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hgeq]
      have hnorm : ω * ENNReal.ofReal r ^ n = c * (ω * ENNReal.ofReal (r / β) ^ n) := by
        have h : ENNReal.ofReal r = ENNReal.ofReal β * ENNReal.ofReal (r / β) := by
          rw [← ENNReal.ofReal_mul hβ0.le, mul_div_cancel₀ r hβ0.ne']
        rw [h, mul_pow, hc]
        ring
      have hnum : H (T ∩ closedBall a (r / β)) ≤ lam (closedBall x r) :=
        calc H (T ∩ closedBall a (r / β)) ≤ H (Ac ∩ closedBall x r) := (hball x hxAc r).1
          _ = lam (Γ ∩ closedBall x r) := (hkey r).symm
          _ ≤ lam (closedBall x r) := measure_mono inter_subset_right
      calc c⁻¹ * (H (T ∩ closedBall a (r / β)) / (ω * ENNReal.ofReal (r / β) ^ n))
          = H (T ∩ closedBall a (r / β)) / (c * (ω * ENNReal.ofReal (r / β) ^ n)) := by
            generalize H (T ∩ closedBall a (r / β)) = M
            generalize ω * ENNReal.ofReal (r / β) ^ n = D
            rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
            ring
        _ = H (T ∩ closedBall a (r / β)) / (ω * ENNReal.ofReal r ^ n) := by rw [hnorm]
        _ ≤ lam (closedBall x r) / (ω * ENNReal.ofReal r ^ n) := by gcongr
        _ = densityRatio n lam x r := rfl
    calc c⁻¹ = liminf (fun r ↦ c⁻¹ * densityRatio n (H.restrict T) a (r / β)) (𝓝[>] 0) :=
          hlim.liminf_eq.symm
      _ ≤ liminf (densityRatio n lam x) (𝓝[>] 0) := liminf_le_liminf hle
  · -- Step 10: eventually `q_x(r) ≠ 0`, and then `λ(B_r(x)) = q_x(r)⁻¹ λ(Γ ∩ B_r(x))` with
    -- `λ(Γ ∩ B_r(x)) = H^n(A_c ∩ B_r(x)) ≤ c H^n(T ∩ B_r(a))`, so
    -- `densityRatio n λ x r ≤ q_x(r)⁻¹ (c g(r)) → 1⁻¹ (c · 1) = c`.
    have hne : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (Γ ∩ closedBall x r) / lam (closedBall x r) ≠ 0 :=
      hq.eventually_ne one_ne_zero
    have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), densityRatio n lam x r ≤
        (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
          (c * densityRatio n (H.restrict T) a r) := by
      filter_upwards [hne] with r hr
      have hΓB0 : lam (Γ ∩ closedBall x r) ≠ 0 := by
        intro h
        apply hr
        rw [h, ENNReal.zero_div]
      have hΓBtop : lam (Γ ∩ closedBall x r) ≠ ∞ := measure_ne_top _ _
      have hBtop : lam (closedBall x r) ≠ ∞ := measure_ne_top _ _
      have hB0 : lam (closedBall x r) ≠ 0 := fun h ↦
        hΓB0 (measure_mono_null inter_subset_right h)
      have hinv : (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ =
          lam (closedBall x r) / lam (Γ ∩ closedBall x r) :=
        ENNReal.inv_div (Or.inl hBtop) (Or.inl hB0)
      have hBeq : lam (closedBall x r) =
          (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * lam (Γ ∩ closedBall x r) := by
        rw [hinv, ENNReal.div_mul_cancel hΓB0 hΓBtop]
      rw [hgeq]
      calc densityRatio n lam x r = lam (closedBall x r) / (ω * ENNReal.ofReal r ^ n) := rfl
        _ = (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * lam (Γ ∩ closedBall x r) /
              (ω * ENNReal.ofReal r ^ n) := by rw [← hBeq]
        _ ≤ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ * (c * H (T ∩ closedBall a r)) /
              (ω * ENNReal.ofReal r ^ n) := by
            gcongr
            rw [hkey r]
            exact (hball x hxAc r).2
        _ = _ := by rw [mul_div_assoc, mul_div_assoc]
    have hlim : Tendsto (fun r ↦ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
        (c * densityRatio n (H.restrict T) a r)) (𝓝[>] 0) (𝓝 (1⁻¹ * (c * 1))) :=
      ENNReal.Tendsto.mul (tendsto_inv_iff.2 hq) (Or.inl (by simp))
        (ENNReal.Tendsto.const_mul hg (Or.inl one_ne_zero)) (Or.inl (by simp [hc0]))
    rw [inv_one, mul_one, one_mul] at hlim
    calc limsup (densityRatio n lam x) (𝓝[>] 0)
        ≤ limsup (fun r ↦ (lam (Γ ∩ closedBall x r) / lam (closedBall x r))⁻¹ *
            (c * densityRatio n (H.restrict T) a r)) (𝓝[>] 0) := limsup_le_limsup hle
      _ = c := hlim.limsup_eq

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
