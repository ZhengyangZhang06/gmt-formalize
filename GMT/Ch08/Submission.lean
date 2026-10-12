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

/-- **Simon Ch. 2, 4.3** (child `classical_tangent` of the constancy theorem): at a point `φ a`
of a `C²` local representation, the classical tangent space (velocities of `C¹` curves in `M`) is
the range of `L = Dφ(a)`.  `⊇`: the curve `t ↦ φ (a + (ε sin (t/ε)) w)` stays in the chart and has
velocity `L w`.  `⊆`: relative properness makes the chart parameter `β t` of `γ t` tend to `a`,
`L` is antilipschitz so `β t - a = O(t)`, and then the component of `γ` normal to `range L` has
derivative `0` at `0`. -/
theorem Submission.simon_chart_classicalTangentSpace_eq_range :
    ∀ (N n : ℕ) (M W : Set (Euclidean N)) (D : Set (Euclidean n)) (φ : Euclidean n → Euclidean N)
      (a : Euclidean n), Chapter02.IsSimonLocalRepresentation 2 M D W φ → a ∈ D →
      classicalTangentSpace M (φ a) = Set.range (fderiv ℝ φ a) := by
  intro N n M W D φ a hφ ha
  have hφ1 : ContDiffOn ℝ 1 φ D := hφ.contDiffOn.of_le (by norm_num)
  have hL : HasFDerivAt φ (fderiv ℝ φ a) a :=
    ((hφ1.contDiffAt (hφ.isOpen_source.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
  ext ξ
  constructor
  · rintro ⟨γ, -, hmaps, hγ0, hder⟩
    have hφa : φ a ∈ W ∩ M := hφ.image_eq ▸ Set.mem_image_of_mem φ ha
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hφ.isOpen_target (φ a) hφa.1
    have hKW : closedBall (φ a) (r / 2) ⊆ W :=
      (closedBall_subset_ball (half_lt_self hr)).trans hrW
    have hS : IsCompact (D ∩ φ ⁻¹' closedBall (φ a) (r / 2)) :=
      hφ.isCompact_source_inter_preimage _ (isCompact_closedBall _ _) hKW
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ closedBall (φ a) (r / 2) ∧ γ t ∈ M := by
      filter_upwards [hder.continuousAt.preimage_mem_nhds
          (by rw [hγ0]; exact closedBall_mem_nhds _ (half_pos hr)),
        Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht1 ht2
      exact ⟨ht1, hmaps ht2⟩
    -- `β t` is the chart parameter of `γ t`; it exists for `t` near `0`.
    set β : ℝ → Euclidean n := fun t ↦ Function.invFunOn φ D (γ t)
    have hβ : ∀ᶠ t in 𝓝 (0 : ℝ), β t ∈ D ∩ φ ⁻¹' closedBall (φ a) (r / 2) ∧ φ (β t) = γ t := by
      filter_upwards [hev] with t ht
      have hex : γ t ∈ φ '' D := hφ.image_eq ▸ ⟨hKW ht.1, ht.2⟩
      obtain ⟨h1, h2⟩ := Function.invFunOn_pos hex
      exact ⟨⟨h1, by rw [Set.mem_preimage, h2]; exact ht.1⟩, h2⟩
    -- Relative properness: `β t → a`.
    have hβa : Tendsto β (𝓝 0) (𝓝 a) := by
      refine hS.tendsto_nhds_of_unique_mapClusterPt (hβ.mono fun t ht ↦ ht.1) fun b hb hcl ↦ ?_
      have hφb : ContinuousAt φ b :=
        hφ.contDiffOn.continuousOn.continuousAt (hφ.isOpen_source.mem_nhds hb.1)
      have h1 : MapClusterPt (φ b) (𝓝 0) (φ ∘ β) := hcl.continuousAt_comp hφb
      have h2 : ClusterPt (φ b) (map γ (𝓝 0)) := by
        rw [← Filter.map_congr (hβ.mono fun t ht ↦ ht.2)]
        exact h1
      have h3 : φ b = γ 0 := eq_of_nhds_neBot (h2.mono hder.continuousAt.tendsto).neBot
      exact hφ.injOn hb.1 ha (h3.trans hγ0)
    -- `L = Dφ(a)` is injective, hence antilipschitz, so `β t - a = O(t)`.
    obtain ⟨C, -, hC⟩ := (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr (hφ.injective_fderiv ha))
    have hrev : (fun u ↦ u - a) =O[𝓝 a] fun u ↦ φ u - φ a := by
      have A : (fun u ↦ u - a) =O[𝓝 a] fun u ↦ fderiv ℝ φ a (u - a) :=
        Asymptotics.isBigO_iff.mpr ⟨C, Eventually.of_forall fun u ↦ by
          have := hC.le_mul_dist 0 (u - a)
          rwa [map_zero, dist_zero_left, dist_zero_left] at this⟩
      have B : Asymptotics.IsEquivalent (𝓝 a) (fun u ↦ φ u - φ a)
          fun u ↦ fderiv ℝ φ a (u - a) :=
        hL.isLittleO.trans_isBigO A
      exact A.trans B.isBigO_symm
    have hγφ : (fun t ↦ φ (β t) - φ a) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ γ t - γ 0 := by
      filter_upwards [hβ] with t ht
      rw [ht.2, hγ0]
    have hβO : (fun t ↦ β t - a) =O[𝓝 (0 : ℝ)] fun t ↦ t := by
      have h1 : (fun t ↦ β t - a) =O[𝓝 (0 : ℝ)] fun t ↦ φ (β t) - φ a := hrev.comp_tendsto hβa
      have h2 : (fun t ↦ γ t - γ 0) =O[𝓝 (0 : ℝ)] fun t ↦ t - 0 := hder.isBigO_sub
      simpa only [sub_zero] using (h1.congr' EventuallyEq.rfl hγφ).trans h2
    -- The normal part `Q = id - P_{range L}` of `γ` has zero derivative at `0`.
    set K : Submodule ℝ (Euclidean N) :=
      LinearMap.range (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N)
    set Q : Euclidean N →L[ℝ] Euclidean N := ContinuousLinearMap.id ℝ _ - K.starProjection with hQ
    have hQL : Q.comp (fderiv ℝ φ a) = 0 := by
      ext1 v
      have hv : K.starProjection (fderiv ℝ φ a v) = fderiv ℝ φ a v :=
        Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ v)
      simp [hQ, hv]
    have hQφ : (fun u ↦ Q (φ u) - Q (φ a)) =o[𝓝 a] fun u ↦ u - a := by
      simpa [hQL] using (Q.hasFDerivAt.comp a hL).isLittleO
    have hQγ : HasDerivAt (fun t ↦ Q (γ t)) 0 0 := by
      refine hasDerivAt_iff_isLittleO.mpr ?_
      have h1 := (hQφ.comp_tendsto hβa).trans_isBigO hβO
      have h2 : (fun t ↦ Q (φ (β t)) - Q (φ a)) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ Q (γ t) - Q (γ 0) := by
        filter_upwards [hβ] with t ht
        rw [ht.2, hγ0]
      simpa using h1.congr' h2 EventuallyEq.rfl
    have hQξ : Q ξ = 0 := (Q.hasFDerivAt.comp_hasDerivAt 0 hder).unique hQγ
    have hξK : ξ ∈ K := by
      rw [← Submodule.starProjection_eq_self_iff]
      have : ξ - K.starProjection ξ = 0 := by simpa [hQ] using hQξ
      exact (sub_eq_zero.mp this).symm
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hξK
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hφ.isOpen_source a ha
    have hw1 : 0 < ‖w‖ + 1 := by positivity
    set ε : ℝ := r / (‖w‖ + 1) with hε
    have hε0 : 0 < ε := div_pos hr hw1
    -- `c t = a + (ε sin (t / ε)) w` stays in `B(a, r) ⊆ D` and has velocity `w` at `0`.
    have hcD : ∀ t : ℝ, a + (ε * Real.sin (t / ε)) • w ∈ D := by
      intro t
      apply hrD
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_of_pos hε0]
      calc ε * |Real.sin (t / ε)| * ‖w‖ ≤ ε * 1 * ‖w‖ := by
            gcongr
            exact Real.abs_sin_le_one _
        _ < r := by
            rw [mul_one, hε, div_mul_eq_mul_div, div_lt_iff₀ hw1]
            nlinarith [norm_nonneg w]
    have hcd : ContDiff ℝ 1 fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w :=
      contDiff_const.add <|
        (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ε))).smul contDiff_const
    have hcder : HasDerivAt (fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w) w 0 := by
      have hdiv : HasDerivAt (fun t : ℝ ↦ t / ε) (1 / ε) 0 := (hasDerivAt_id (0 : ℝ)).div_const ε
      have hsin : HasDerivAt (fun t : ℝ ↦ ε * Real.sin (t / ε))
          (ε * (Real.cos (0 / ε) * (1 / ε))) 0 :=
        hdiv.sin.const_mul ε
      have h1 : ε * (Real.cos (0 / ε) * (1 / ε)) = 1 := by
        rw [zero_div, Real.cos_zero]
        field_simp
      rw [h1] at hsin
      simpa using (hsin.smul_const w).const_add a
    refine ⟨φ ∘ fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w, ?_, ?_, ?_, ?_⟩
    · exact (hφ1.comp_contDiff hcd hcD).contDiffOn
    · intro t _
      exact (hφ.image_eq ▸ Set.mem_image_of_mem φ (hcD t) : φ _ ∈ W ∩ M).2
    · simp
    · have hL' : HasFDerivAt φ (fderiv ℝ φ a)
          ((fun t : ℝ ↦ a + (ε * Real.sin (t / ε)) • w) 0) := by
        simpa using hL
      exact hL'.comp_hasDerivAt 0 hcder

theorem Submission.stationary_constancy_tangentGraph_measure :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)),
      V.Stationary → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M →
      U ∩ V.weight.support ⊆ M → IsPreconnected (M ∩ U) → M.Nonempty →
      ∃ (c : ℝ≥0∞) (T : Euclidean N → Grassmannian N n), c ≠ ∞ ∧ Measurable T ∧
        V.measure = (c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).map
          (fun x ↦ (x, T x)) ∧
        (c ≠ 0 → ∀ x ∈ M ∩ U, ((T x).plane : Set (Euclidean N)) = classicalTangentSpace M x) := by
  intro N n U V M hV hSM hM hconn hne
  -- smooth cut-offs of maps that are smooth on an open set
  have GCut : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (k : ℕ∞) (χ : X → ℝ) (g : X → Y) (O : Set X), IsOpen O →
      ContDiff ℝ k χ → ContDiffOn ℝ k g O → tsupport χ ⊆ O → ContDiff ℝ k (fun x ↦ χ x • g x) := by
    intro X Y _ _ _ _ k χ g O hO hχ hg hs
    refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hg.contDiffAt (hO.mem_nhds hx))
    · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ ↦ (0 : Y)) ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hx (hs h)] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  -- a `C²` left inverse `ψ` of a chart near a chart point
  have GI : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (M W : Set F) (D : Set E) (φ : E → F) (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
      (a : E) (ha : a ∈ D),
      ∃ (ψ : F → E) (T₀ : Set F), IsOpen T₀ ∧ φ a ∈ T₀ ∧ ContDiffOn ℝ 2 ψ T₀ ∧ MapsTo ψ T₀ D ∧
        ∀ y ∈ M ∩ T₀, φ (ψ y) = y := by
    intro E F _ _ _ _ _ _ M W D φ hφ a ha
    obtain ⟨hDo, hWo, hφc, hφi, hφim, hφp, hφd⟩ := hφ
    obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ a := ⟨_, rfl⟩
    obtain ⟨P', hP'⟩ := (L : E →ₗ[ℝ] F).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hL ▸ hφd a ha))
    obtain ⟨P, hPL⟩ : ∃ P : F →L[ℝ] E, ∀ x, P (L x) = x :=
      ⟨LinearMap.toContinuousLinearMap P', fun x ↦ LinearMap.congr_fun hP' x⟩
    have hφa : ContDiffAt ℝ 2 φ a := hφc.contDiffAt (hDo.mem_nhds ha)
    -- the straightening map `Φ z = φ (a + P z) + (z - L (P z))`, with `DΦ(0) = id`
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : F → F, Φ = fun z ↦ φ (a + P z) + (z - L (P z)) := ⟨_, rfl⟩
    have hA : HasFDerivAt (fun z : F ↦ a + P z) P 0 := (P.hasFDerivAt).const_add a
    have hφa' : ContDiffAt ℝ 2 φ (a + P 0) := by rw [map_zero, add_zero]; exact hφa
    have hΦc : ContDiffAt ℝ 2 Φ 0 := by
      rw [hΦ]
      exact (hφa'.comp (0 : F) (contDiffAt_const.add P.contDiff.contDiffAt)).add
        (contDiffAt_id.sub (L.contDiff.comp P.contDiff).contDiffAt)
    have hΦd : HasFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ F : F ≃L[ℝ] F) : F →L[ℝ] F) 0 := by
      have h1 : HasFDerivAt (fun z : F ↦ φ (a + P z)) (L.comp P) 0 := by
        have : HasFDerivAt φ L (a + P 0) := by
          rw [map_zero, add_zero, hL]; exact (hφa.differentiableAt (by norm_num)).hasFDerivAt
        exact this.comp (0 : F) hA
      rw [hΦ]
      refine (h1.add ((hasFDerivAt_id (0 : F)).sub (L.comp P).hasFDerivAt)).congr_fderiv ?_
      ext z
      simp
    have hstrict := hΦc.hasStrictFDerivAt' hΦd (by norm_num)
    set e := hstrict.toOpenPartialHomeomorph Φ with he
    have h0s : (0 : F) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
    have hΦ0 : Φ 0 = φ a := by rw [hΦ]; simp
    have hφat : φ a ∈ e.target := hΦ0 ▸ hstrict.image_mem_toOpenPartialHomeomorph_target
    have hsymm : e.symm (φ a) = 0 := by rw [← hΦ0]; exact e.left_inv h0s
    -- the inverse is `C²` near `φ a`
    have hΨ : ContDiffAt ℝ 2 e.symm (φ a) := by
      refine e.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ F) hφat ?_ ?_
      · rw [hsymm]; exact hΦd
      · rw [hsymm]; exact hΦc
    obtain ⟨O₁, hO₁, hO₁o, hφaO₁⟩ := _root_.mem_nhds_iff.mp
      (inter_mem (hΨ.eventually (by norm_num)) (e.open_target.mem_nhds hφat))
    -- `ψ y = a + P (e.symm y)`; on the chart, `ψ (φ w) = w`
    obtain ⟨ψ, hψ⟩ : ∃ ψ : F → E, ψ = fun y ↦ a + P (e.symm y) := ⟨_, rfl⟩
    have hψc : ContDiffOn ℝ 2 ψ O₁ := by
      rw [hψ]
      exact fun y hy ↦ (contDiffAt_const.add (P.contDiff.contDiffAt.comp y
        (show ContDiffAt ℝ 2 e.symm y from (hO₁ hy).1))).contDiffWithinAt
    -- a ball `B(a, r)` in `D` whose linearized image lies in `e.source`
    obtain ⟨r, hr, hrD⟩ : ∃ r > 0, ball a r ⊆ D ∩ (fun w ↦ L (w - a)) ⁻¹' e.source := by
      refine Metric.isOpen_iff.mp (hDo.inter (e.open_source.preimage
        (L.continuous.comp (continuous_id.sub continuous_const)))) a ⟨ha, ?_⟩
      show L (a - a) ∈ e.source
      rw [sub_self, map_zero]; exact h0s
    have hψφ : ∀ w ∈ ball a r, ψ (φ w) = w := by
      intro w hw
      have hsrc := (hrD hw).2
      have hΦw : Φ (L (w - a)) = φ w := by
        rw [hΦ]; simp only [hPL, add_sub_cancel, sub_self, add_zero]
      rw [hψ, ← hΦw]
      show a + P (e.symm (e (L (w - a)))) = w
      rw [e.left_inv hsrc, hPL, add_sub_cancel]
    -- relative properness: near `φ a`, `M` is covered by `φ (B(a, r))`
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hWo (φ a) (hφim ▸ mem_image_of_mem φ ha).1
    have hK : IsCompact ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r) :=
      (hφp _ (isCompact_closedBall _ _) ((closedBall_subset_ball (half_lt_self hρ)).trans hρW)).diff
        isOpen_ball
    have hKφ : φ a ∉ φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r) := by
      rintro ⟨w, ⟨⟨hwD, _⟩, hwB⟩, hw⟩
      exact hwB (hφi hwD ha hw ▸ mem_ball_self hr)
    have hKc : IsClosed (φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r)) :=
      (hK.image_of_continuousOn (hφc.continuousOn.mono fun w hw ↦ hw.1.1)).isClosed
    set O₂ := ball (φ a) (ρ / 2) \ φ '' ((D ∩ φ ⁻¹' closedBall (φ a) (ρ / 2)) \ ball a r)
    have hO₂ : IsOpen O₂ := isOpen_ball.sdiff hKc
    have hMO₂ : ∀ y ∈ M ∩ O₂, ∃ w ∈ ball a r, φ w = y := by
      rintro y ⟨hyM, hyB, hyK⟩
      have hyW : y ∈ W := hρW (ball_subset_ball (half_le_self hρ.le) hyB)
      obtain ⟨w, hwD, rfl⟩ : y ∈ φ '' D := hφim ▸ ⟨hyW, hyM⟩
      refine ⟨w, ?_, rfl⟩
      by_contra hwB
      exact hyK ⟨w, ⟨⟨hwD, ball_subset_closedBall hyB⟩, hwB⟩, rfl⟩
    -- the final neighbourhood
    refine ⟨ψ, O₁ ∩ O₂ ∩ ψ ⁻¹' ball a r, ?_, ⟨⟨hφaO₁, mem_ball_self (half_pos hρ), hKφ⟩,
      by rw [mem_preimage, hψφ a (mem_ball_self hr)]; exact mem_ball_self hr⟩,
      hψc.mono fun y hy ↦ hy.1.1, fun y hy ↦ (hrD hy.2).1, ?_⟩
    · exact (hψc.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hO₁o.inter hO₂)
        isOpen_ball
    · rintro y ⟨hyM, ⟨_, hyO₂⟩, _⟩
      obtain ⟨w, hw, rfl⟩ := hMO₂ y ⟨hyM, hyO₂⟩
      rw [hψφ w hw]
  -- `normDet` is continuous, and `C¹` at injective maps
  have GNg : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (NJ : (E →L[ℝ] F) → ℝ) (hNJ : ∀ T, NJ T = (T : E →ₗ[ℝ] F).normDet),
      Continuous NJ ∧ ∀ T : E →L[ℝ] F, Function.Injective T → ContDiffAt ℝ 1 NJ T := by
    intro E F _ _ _ _ _ _ NJ hNJ
    set b := stdOrthonormalBasis ℝ E
    have hN : NJ = fun S ↦ Real.sqrt (Matrix.gram ℝ (fun i ↦ S (b i))).det := by
      funext S
      have h := LinearMap.normDet_sq_eq_det_gram (S : E →ₗ[ℝ] F) b
      rw [RCLike.ofReal_real_eq_id, id] at h
      simp only [ContinuousLinearMap.coe_coe] at h
      rw [hNJ, ← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
    have hg : ∀ i j, ContDiff ℝ 1 (fun S : E →L[ℝ] F ↦ inner ℝ (S (b i)) (S (b j))) :=
      fun i j ↦ (ContinuousLinearMap.apply ℝ F (b i)).contDiff.inner ℝ
        (ContinuousLinearMap.apply ℝ F (b j)).contDiff
    have hd : ContDiff ℝ 1 (fun S : E →L[ℝ] F ↦ (Matrix.gram ℝ (fun i ↦ S (b i))).det) := by
      simp only [Matrix.det_apply, Matrix.gram_apply]
      fun_prop
    refine ⟨hN ▸ Real.continuous_sqrt.comp hd.continuous, fun T hT ↦ ?_⟩
    rw [hN]
    refine hd.contDiffAt.sqrt fun h0 ↦ ?_
    have h1 : NJ T = 0 := by rw [hN]; show Real.sqrt _ = 0; rw [h0, Real.sqrt_zero]
    rw [hNJ] at h1
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h1) (LinearMap.ker_eq_bot.mpr hT)
  -- weighted distributional constancy on a ball
  have G4wg : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (vol : Measure E) [vol.IsAddHaarMeasure]
      (ϑ : Measure E) [IsFiniteMeasure ϑ] (J : E → ℝ) (a : E) (R m : ℝ) (hR : 0 < R) (hm : 0 < m)
      (hJ : Measurable J) (hJm : ∀ᵐ u ∂ϑ, m ≤ J u)
      (h : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v,
        ∫ u, (1 / J u) * fderiv ℝ ζ u v ∂ϑ = 0),
      ∃ c : ℝ, ϑ.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
        (vol.restrict (ball a (R / 2 / 2 / 2))).withDensity (fun u ↦ ENNReal.ofReal (J u)) := by
    intro E _ _ _ _ _ vol _ ϑ _ J a R m hR hm hJ hJm h
    have P4 : ∀ (ν : Measure E) [IsFiniteMeasure ν],
        (∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v, ∫ u, fderiv ℝ ζ u v ∂ν = 0) →
        ∃ c : ℝ, ν.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
            vol.restrict (ball a (R / 2 / 2 / 2)) := by
      intro ν _ h
      have h2 : 0 < R / 2 := half_pos hR
      have h4 : 0 < R / 2 / 2 := half_pos h2
      have h8 : 0 < R / 2 / 2 / 2 := half_pos h4
      -- Step A: translation invariance.
      have hA : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2) →
          ∀ h₀ ∈ ball (0 : E) (R / 2), ∫ y, ζ (y - h₀) ∂ν = ∫ y, ζ y ∂ν := by
        intro ζ hζ hs
        have hc : HasCompactSupport ζ :=
          (isCompact_closedBall a (R / 2)).of_isClosed_subset (isClosed_tsupport ζ)
            (hs.trans ball_subset_closedBall)
        have hζ' := hζ.continuous_fderiv one_ne_zero
        obtain ⟨C, hC⟩ := hζ'.bounded_above_of_compact_support (hc.fderiv ℝ)
        have hD : ∀ y h : E, HasFDerivAt (fun h ↦ ζ (y - h)) (-fderiv ℝ ζ (y - h)) h := by
          intro y h
          exact ((hζ.differentiable one_ne_zero (y - h)).hasFDerivAt.comp h
            ((hasFDerivAt_id h).const_sub y)).congr_fderiv
                (by rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id])
        have hF : ∀ h₀ : E, HasFDerivAt (fun h ↦ ∫ y, ζ (y - h) ∂ν)
            (∫ y, -fderiv ℝ ζ (y - h₀) ∂ν) h₀ := fun h₀ ↦
          hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun h y ↦ ζ (y - h))
            (F' := fun h y ↦ -fderiv ℝ ζ (y - h)) (bound := fun _ ↦ C) Filter.univ_mem
            (Eventually.of_forall fun h ↦
              (hζ.continuous.comp (continuous_sub_right h)).aestronglyMeasurable)
            ((hζ.continuous.comp (continuous_sub_right h₀)).integrable_of_hasCompactSupport
              (hc.comp_homeomorph (Homeomorph.subRight h₀)))
            ((hζ'.comp (continuous_sub_right h₀)).neg.aestronglyMeasurable)
            (Eventually.of_forall fun y h _ ↦ (norm_neg _).trans_le (hC _))
            (integrable_const C) (Eventually.of_forall fun y h _ ↦ hD y h)
        have h0 : ∀ h₀ ∈ ball (0 : E) (R / 2),
            fderiv ℝ (fun h ↦ ∫ y, ζ (y - h) ∂ν) h₀ = 0 := by
          intro h₀ hh₀
          rw [(hF h₀).fderiv]
          ext v
          rw [ContinuousLinearMap.integral_apply (φ := fun y ↦ -fderiv ℝ ζ (y - h₀))
            ((hζ'.comp (continuous_sub_right h₀)).neg.integrable_of_hasCompactSupport
              ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.subRight h₀)).neg) v]
          have := h (fun y ↦ ζ (y - h₀)) (hζ.comp (contDiff_id.sub contDiff_const)) ?_ v
          · simp only [fderiv_comp_sub, ContinuousLinearMap.neg_apply, integral_neg,
              ContinuousLinearMap.zero_apply, neg_eq_zero] at this ⊢
            exact this
          · refine (tsupport_comp_subset_preimage _ (continuous_sub_right h₀)).trans ?_
            intro y hy
            have h1 := hs hy
            rw [mem_ball, dist_eq_norm] at h1 ⊢
            rw [mem_ball, dist_zero_right] at hh₀
            calc ‖y - a‖ = ‖(y - h₀ - a) + h₀‖ := by rw [sub_right_comm, sub_add_cancel]
              _ ≤ ‖y - h₀ - a‖ + ‖h₀‖ := norm_add_le _ _
              _ < R / 2 + R / 2 := add_lt_add h1 hh₀
              _ = R := add_halves R
        intro h₀ hh₀
        have := isOpen_ball.is_const_of_fderiv_eq_zero
          (convex_ball (0 : E) (R / 2)).isPreconnected
          (fun h _ ↦ (hF h).differentiableAt.differentiableWithinAt) h0 hh₀
          (mem_ball_self (half_pos hR))
        simpa only [sub_zero] using this
      -- integrability on products of functions supported over a compact set
      have hI : ∀ f : E × E → ℝ, Continuous f → ∀ K : Set (E),
          IsCompact K → (∀ p, p.1 ∉ K → f p = 0) → (∃ C, ∀ p, ‖f p‖ ≤ C) →
          Integrable f (vol.prod ν) := by
        intro f hf K hK hfK ⟨C, hC⟩
        have hfin : (vol.prod ν) (K ×ˢ univ) ≠ ∞ := by
          rw [Measure.prod_prod]
          exact ENNReal.mul_ne_top hK.measure_lt_top.ne (measure_ne_top _ _)
        refine (integrableOn_iff_integrable_of_support_subset (s := K ×ˢ univ) ?_).mp
          (Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
            (Eventually.of_forall fun p ↦ hC p))
        intro p hp
        by_contra hpK
        exact hp (hfK p fun h1 ↦ hpK ⟨h1, mem_univ _⟩)
      -- Step B: a bump `ρ` and its integral `m > 0`.
      let ρb : ContDiffBump (0 : E) := ⟨R / 2 / 2 / 2, R / 2 / 2, h8, half_lt_self h4⟩
      obtain ⟨ρ, hρdef⟩ : ∃ ρ : E → ℝ, ρ = ρb := ⟨_, rfl⟩
      have hρc : ContDiff ℝ 1 ρ := hρdef ▸ ρb.contDiff
      have hρs : tsupport ρ = closedBall 0 (R / 2 / 2) := hρdef ▸ ρb.tsupport_eq
      have hρ0 : ∀ x, 0 ≤ ρ x := fun x ↦ by rw [hρdef]; exact ρb.nonneg
      have hρcs : HasCompactSupport ρ := by
        rw [HasCompactSupport, hρs]; exact isCompact_closedBall _ _
      obtain ⟨Cρ, hCρ⟩ := hρc.continuous.bounded_above_of_compact_support hρcs
      set m := ∫ x, ρ x ∂vol with hm
      have hm0 : 0 < m := by
        rw [hm, integral_pos_iff_support_of_nonneg hρ0
          (hρc.continuous.integrable_of_hasCompactSupport hρcs), hρdef, ρb.support_eq]
        exact measure_ball_pos _ _ h4
      set c₀ := (∫ y, ρ (y - a) ∂ν) / m with hc₀
      have hρa : ∀ x ∈ ball a (R / 2 / 2), ∫ y, ρ (y - x) ∂ν = ∫ y, ρ (y - a) ∂ν := by
        intro x hx
        have hx' : x - a ∈ ball (0 : E) (R / 2) := by
          rw [mem_ball, dist_zero_right, ← dist_eq_norm]
          exact (mem_ball.mp hx).trans (half_lt_self h2)
        have := hA (fun y ↦ ρ (y - a)) (hρc.comp (contDiff_id.sub contDiff_const)) ?_ (x - a) hx'
        · simpa only [sub_sub, sub_add_cancel] using this
        · refine (tsupport_comp_subset_preimage _ (continuous_sub_right a)).trans ?_
          intro y hy
          rw [mem_preimage, hρs, mem_closedBall, dist_zero_right] at hy
          rw [mem_ball, dist_eq_norm]
          exact hy.trans_lt (half_lt_self h2)
      have hB : ∀ ζ : E → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2 / 2) →
          ∫ y, ζ y ∂ν = c₀ * ∫ x, ζ x ∂vol := by
        intro ζ hζ hs
        have hc : HasCompactSupport ζ :=
          (isCompact_closedBall a (R / 2 / 2)).of_isClosed_subset (isClosed_tsupport ζ)
            (hs.trans ball_subset_closedBall)
        obtain ⟨Cζ, hCζ⟩ := hζ.continuous.bounded_above_of_compact_support hc
        have hs2 : tsupport ζ ⊆ ball a (R / 2) := hs.trans (ball_subset_ball (half_le_self h2.le))
        have hbd : ∀ (u w : E), ‖ρ u * ζ w‖ ≤ Cρ * Cζ := fun u w ↦ by
          rw [norm_mul]
          exact mul_le_mul (hCρ u) (hCζ w) (norm_nonneg _) ((norm_nonneg _).trans (hCρ u))
        have i1 : Integrable (fun p : E × E ↦ ρ p.1 * ζ (p.2 - p.1))
            (vol.prod ν) :=
          hI _ ((hρc.continuous.comp continuous_fst).mul
            (hζ.continuous.comp (continuous_snd.sub continuous_fst))) _ hρcs.isCompact
            (fun p hp ↦ by rw [image_eq_zero_of_notMem_tsupport hp, zero_mul])
            ⟨_, fun p ↦ hbd _ _⟩
        have i2 : Integrable (fun p : E × E ↦ ρ (p.2 - p.1) * ζ p.1)
            (vol.prod ν) :=
          hI _ ((hρc.continuous.comp (continuous_snd.sub continuous_fst)).mul
            (hζ.continuous.comp continuous_fst)) _ hc.isCompact
            (fun p hp ↦ by rw [image_eq_zero_of_notMem_tsupport hp, mul_zero])
            ⟨_, fun p ↦ hbd _ _⟩
        rw [hc₀, div_mul_eq_mul_div, eq_div_iff hm0.ne']
        calc (∫ y, ζ y ∂ν) * m = ∫ h, ρ h * ∫ y, ζ y ∂ν ∂vol := by rw [integral_mul_const, mul_comm]
          _ = ∫ h, ρ h * ∫ y, ζ (y - h) ∂ν ∂vol := by
              refine integral_congr_ae (Eventually.of_forall fun h ↦ ?_)
              by_cases hh : ρ h = 0
              · simp only [hh, zero_mul]
              · have hh' : h ∈ ball (0 : E) (R / 2) := by
                  have := subset_tsupport ρ hh
                  rw [hρs] at this
                  exact closedBall_subset_ball (half_lt_self h2) this
                simp only
                rw [hA ζ hζ hs2 h hh']
          _ = ∫ y, ∫ h, ρ h * ζ (y - h) ∂vol ∂ν := by
              simp_rw [← integral_const_mul]
              exact integral_integral_swap i1
          _ = ∫ y, ∫ x, ρ (y - x) * ζ x ∂vol ∂ν := by
              refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
              have := integral_sub_left_eq_self (fun h ↦ ρ h * ζ (y - h)) (vol : Measure (E)) y
              simpa only [sub_sub_cancel] using this.symm
          _ = ∫ x, ∫ y, ρ (y - x) * ζ x ∂ν ∂vol := integral_integral_swap
              (f := fun y x ↦ ρ (y - x) * ζ x) i2.swap
          _ = ∫ x, (∫ y, ρ (y - a) ∂ν) * ζ x ∂vol := by
              refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
              simp only
              rw [integral_mul_const]
              by_cases hx : ζ x = 0
              · rw [hx, mul_zero, mul_zero]
              · rw [hρa x (hs (subset_tsupport _ hx))]
          _ = (∫ y, ρ (y - a) ∂ν) * ∫ x, ζ x ∂vol := integral_const_mul _ _
      -- Step C: the measures agree on open subsets of `ball a (R / 2 / 2 / 2)`, hence on that ball.
      have hc0 : 0 ≤ c₀ := div_nonneg (integral_nonneg fun y ↦ hρ0 _) hm0.le
      have hO : ∀ O : Set E, IsOpen O → O ⊆ ball a (R / 2 / 2 / 2) →
          ν O = ENNReal.ofReal c₀ * vol O := by
        intro O hO hOs
        obtain ⟨f, hfs, hfc, hfr⟩ := hO.exists_contDiff_support_eq (n := 1)
        have hf0 : ∀ x, 0 ≤ f x := fun x ↦ (hfr ⟨x, rfl⟩).1
        set g : ℕ → E → ℝ := fun k x ↦ Real.smoothTransition ((k : ℝ) * f x) with hgdef
        have hg : ∀ k, ContDiff ℝ 1 (g k) := fun k ↦
          Real.smoothTransition.contDiff.comp (contDiff_const.mul hfc)
        have hsupp : ∀ k, Function.support (g k) ⊆ O := by
          intro k x hx
          rw [← hfs]
          intro hfx
          exact hx (by simp only [hgdef, hfx, mul_zero, Real.smoothTransition.zero])
        have hgs : ∀ k, tsupport (g k) ⊆ ball a (R / 2 / 2) := fun k ↦
          (closure_mono ((hsupp k).trans hOs)).trans (closure_ball_subset_closedBall.trans
            (closedBall_subset_ball (half_lt_self h4)))
        have hlim : ∀ x, Tendsto (fun k ↦ g k x) atTop (𝓝 (O.indicator 1 x)) := by
          intro x
          by_cases hx : x ∈ O
          · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm (by rw [← hfs] at hx; exact hx))
            rw [indicator_of_mem hx, Pi.one_apply]
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const hfx).eventually_ge_atTop 1]
              with k hk
            exact (Real.smoothTransition.one_of_one_le hk).symm
          · have hfx : f x = 0 := by
              by_contra h'
              exact hx (hfs ▸ h')
            rw [indicator_of_notMem hx]
            refine tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦ ?_)
            simp only [hgdef, hfx, mul_zero, Real.smoothTransition.zero]
        have hb : ∀ k x, ‖g k x‖ ≤ 1 := fun k x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
        have h1 : Tendsto (fun k ↦ ∫ x, g k x ∂ν) atTop (𝓝 (ν.real O)) := by
          rw [← integral_indicator_one hO.measurableSet]
          exact tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
            (fun k ↦ (hg k).continuous.aestronglyMeasurable) (integrable_const 1)
            (fun k ↦ Eventually.of_forall (hb k)) (Eventually.of_forall hlim)
        have h2 : Tendsto (fun k ↦ ∫ x, g k x ∂vol) atTop (𝓝 (vol.real O)) := by
          rw [← integral_indicator_one hO.measurableSet]
          refine tendsto_integral_of_dominated_convergence ((ball a (R / 2 / 2)).indicator 1)
            (fun k ↦ (hg k).continuous.aestronglyMeasurable)
            ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball)
            (fun k ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall hlim)
          by_cases hx : x ∈ ball a (R / 2 / 2)
          · rw [indicator_of_mem hx]; exact hb k x
          · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs k h),
              norm_zero]
        have h3 : ν.real O = c₀ * vol.real O := tendsto_nhds_unique h1
          ((h2.const_mul c₀).congr fun k ↦ (hB _ (hg k) (hgs k)).symm)
        have hvO : vol O ≠ ∞ := ((measure_mono (hOs.trans ball_subset_closedBall)).trans_lt
          (isCompact_closedBall a _).measure_lt_top).ne
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν O), ← measureReal_def, h3,
          ENNReal.ofReal_mul hc0, measureReal_def, ENNReal.ofReal_toReal hvO]
      refine ⟨c₀, ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
        (fun s hs ↦ ?_) ?_⟩
      · rw [Measure.restrict_apply (IsOpen.measurableSet hs), Measure.smul_apply,
          Measure.restrict_apply (IsOpen.measurableSet hs), smul_eq_mul]
        exact hO _ ((IsOpen.inter hs isOpen_ball)) inter_subset_right
      · rw [Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ,
          smul_eq_mul]
        exact hO _ isOpen_ball subset_rfl

    have hJ' : Measurable fun u ↦ ENNReal.ofReal (1 / J u) :=
        (measurable_const.div hJ).ennreal_ofReal
    have hν : IsFiniteMeasure (ϑ.withDensity fun u ↦ ENNReal.ofReal (1 / J u)) := by
      refine ⟨?_⟩
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine (lintegral_mono_ae (g := fun _ ↦ ENNReal.ofReal (1 / m)) ?_).trans_lt ?_
      · filter_upwards [hJm] with u hu
        exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hm hu)
      · rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    obtain ⟨c, hc⟩ := P4 _ fun ζ hζ hs v ↦ by
      rw [integral_withDensity_eq_integral_toReal_smul hJ' (Eventually.of_forall fun _ ↦
        ENNReal.ofReal_lt_top)]
      refine (integral_congr_ae ?_).trans (h ζ hζ hs v)
      filter_upwards [hJm] with u hu
      rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr (hm.le.trans hu)), smul_eq_mul]
    refine ⟨c, ?_⟩
    have hϑ : ϑ = (ϑ.withDensity fun u ↦ ENNReal.ofReal (1 / J u)).withDensity
        fun u ↦ ENNReal.ofReal (J u) := by
      rw [← withDensity_mul _ hJ' hJ.ennreal_ofReal]
      conv_lhs => rw [← withDensity_one (μ := ϑ)]
      refine withDensity_congr_ae ?_
      filter_upwards [hJm] with u hu
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (one_div_nonneg.mpr (hm.le.trans hu)),
        one_div_mul_cancel (hm.trans_le hu).ne', ENNReal.ofReal_one, Pi.one_apply]
    rw [hϑ, restrict_withDensity measurableSet_ball, hc, withDensity_smul_measure]
  -- the area formula on a chart ball
  have G5g : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      (φ : E → F) (ψ : F → E) (b : E) (r : ℝ) (K : NNReal)
      (hφ : ∀ u ∈ ball b r, ContDiffAt ℝ 1 φ u)
      (hinj : ∀ u ∈ ball b r, Function.Injective (fderiv ℝ φ u))
      (hψφ : ∀ u ∈ ball b r, ψ (φ u) = u) (hK : LipschitzOnWith K φ (ball b r))
      (hm : MeasurableSet (φ '' ball b r)) (hψ : ContinuousOn ψ (φ '' ball b r)),
      ((μHE[Module.finrank ℝ E] : Measure F).restrict (φ '' ball b r)).map ψ =
        ((μHE[Module.finrank ℝ E] : Measure E).restrict (ball b r)).withDensity
          (fun u ↦ ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet) := by
    intro E F _ _ _ _ _ _ _ _ _ _ φ ψ b r K hφ hinj hψφ hK hm hψ
    set d := Module.finrank ℝ E
    have hψm : AEMeasurable ψ ((μHE[d] : Measure F).restrict (φ '' ball b r)) := hψ.aemeasurable hm
    obtain ⟨ν, hνdef⟩ : ∃ ν, ν = ((μHE[d] : Measure F).restrict (φ '' ball b r)).map ψ := ⟨_, rfl⟩
    rw [← hνdef]
    have himg : ∀ A : Set E, ψ ⁻¹' A ∩ φ '' ball b r = φ '' (ball b r ∩ A) := by
      intro A; ext y; constructor
      · rintro ⟨hyA, u, hu, rfl⟩
        exact ⟨u, ⟨hu, by rwa [mem_preimage, hψφ u hu] at hyA⟩, rfl⟩
      · rintro ⟨u, ⟨hu, huA⟩, rfl⟩
        exact ⟨by rwa [mem_preimage, hψφ u hu], u, hu, rfl⟩
    have hν : ∀ A, MeasurableSet A → ν A = μHE[d] (φ '' (ball b r ∩ A)) := fun A hA ↦ by
      rw [hνdef, Measure.map_apply_of_aemeasurable hψm hA, Measure.restrict_apply' hm, himg]
    have hνle : ∀ A, MeasurableSet A → ν A ≤ (K : ℝ≥0∞) ^ d * μHE[d] (ball b r ∩ A) :=
      fun A hA ↦ (hν A hA).trans_le
        (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d (hK.mono inter_subset_left))
    have : IsFiniteMeasure ν := ⟨(hνle univ MeasurableSet.univ).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
        ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top))⟩
    have hac : ν ≪ μHE[d] := Measure.AbsolutelyContinuous.mk fun A hA h0 ↦
      le_antisymm ((hνle A hA).trans (by rw [measure_mono_null inter_subset_right h0, mul_zero]))
        bot_le
    have hνB : ν (ball b r)ᶜ = 0 := by
      rw [hν _ measurableSet_ball.compl, inter_compl_self, image_empty, measure_empty]
    -- the density at every point of the ball
    have hpt : ∀ u ∈ ball b r, ∀ D : ℝ≥0∞,
        Tendsto (fun s ↦ ν (closedBall u s) / μHE[d] (closedBall u s)) (𝓝[>] 0) (𝓝 D) →
        D = ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet := by
      intro u hu D hD
      obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ u := ⟨_, rfl⟩
      rw [← hL]
      have hker : LinearMap.ker (L : E →ₗ[ℝ] F) = ⊥ := LinearMap.ker_eq_bot.mpr (hL ▸ hinj u hu)
      obtain ⟨P', hP'⟩ := (L : E →ₗ[ℝ] F).exists_leftInverse_of_injective hker
      have hPL : ∀ x, P' (L x) = x := fun x ↦ LinearMap.congr_fun hP' x
      obtain ⟨κ, -, hκ⟩ := (L : E →ₗ[ℝ] F).exists_antilipschitzWith hker
      have hxy : ∀ x y : E, ‖x - y‖ ≤ κ * ‖L x - L y‖ := fun x y ↦ by
        have h := hκ.le_mul_dist x y
        rwa [dist_eq_norm, dist_eq_norm] at h
      set J := (L : E →ₗ[ℝ] F).normDet with hJ
      have hJ0 : 0 ≤ J := LinearMap.normDet_nonneg _
      have hstrict : HasStrictFDerivAt φ L u := hL ▸ (hφ u hu).hasStrictFDerivAt one_ne_zero
      have hlin : ∀ t, μHE[d] ((L : E →ₗ[ℝ] F) '' closedBall u t) =
          ENNReal.ofReal J * μHE[d] (closedBall u t) :=
        fun t ↦ (L : E →ₗ[ℝ] F).euclideanHausdorffMeasure_image _
      have hκ1 : (0 : ℝ) < κ + 1 := add_pos_of_nonneg_of_pos κ.2 one_pos
      have key : ∀ δ : ℝ, 0 < δ → δ < 1 →
          D ≤ ENNReal.ofReal ((1 + δ) ^ d * J) ∧ ENNReal.ofReal ((1 - δ) ^ d * J) ≤ D := by
        intro δ hδ hδ1
        have h1δ : 0 < 1 + δ := add_pos one_pos hδ
        have h1δ' : 0 < 1 - δ := sub_pos.mpr hδ1
        obtain ⟨c, hc⟩ : ∃ c : NNReal, c = Real.toNNReal (δ / (κ + 1)) := ⟨_, rfl⟩
        have hc0 : 0 < c := hc ▸ Real.toNNReal_pos.mpr (div_pos hδ hκ1)
        have hcκ : (c : ℝ) * κ ≤ δ := by
          rw [hc, Real.coe_toNNReal _ (div_nonneg hδ.le hκ1.le), div_mul_eq_mul_div,
            div_le_iff₀ hκ1]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le
        obtain ⟨s, hs, hA⟩ := hstrict.approximates_deriv_on_nhds (Or.inr hc0)
        have hA' : ∀ x ∈ s, ∀ y ∈ s, ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖L x - L y‖ := by
          intro x hx y hy
          calc ‖φ x - φ y - (L x - L y)‖ = ‖φ x - φ y - L (x - y)‖ := by rw [map_sub]
            _ ≤ c * ‖x - y‖ := hA x hx y hy
            _ ≤ c * (κ * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hxy x y) c.2
            _ ≤ δ * ‖L x - L y‖ := by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcκ (norm_nonneg _)
        obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (isOpen_ball.mem_nhds hu))
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ closedBall u t ⊆ s ∩ ball b r := by
          filter_upwards [Ioo_mem_nhdsGT hε] with t ht
          exact ⟨ht.1, (closedBall_subset_ball ht.2).trans hεs⟩
        have hνt : ∀ t, closedBall u t ⊆ s ∩ ball b r →
            ν (closedBall u t) = μHE[d] (φ '' closedBall u t) := fun t ht ↦ by
          rw [hν _ measurableSet_closedBall, inter_eq_right.mpr (ht.trans inter_subset_right)]
        constructor
        · refine le_of_tendsto hD ?_
          filter_upwards [hev] with t ht
          refine ENNReal.div_le_of_le_mul ?_
          rw [hνt t ht.2]
          have himg' : φ '' closedBall u t = (fun p ↦ φ (P' p)) ''
              ((L : E →ₗ[ℝ] F) '' closedBall u t) := by
            rw [image_image]
            exact image_congr fun x _ ↦ by rw [ContinuousLinearMap.coe_coe, hPL]
          rw [himg']
          refine (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
            (K := Real.toNNReal (1 + δ)) d ?_).trans ?_
          · refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
            obtain ⟨x, hx, rfl⟩ := hp
            obtain ⟨y, hy, rfl⟩ := hq
            rw [ContinuousLinearMap.coe_coe, hPL, hPL, dist_eq_norm, dist_eq_norm,
              Real.coe_toNNReal _ h1δ.le]
            have h1 := hA' x (ht.2 hx).1 y (ht.2 hy).1
            calc ‖φ x - φ y‖ = ‖(φ x - φ y - (L x - L y)) + (L x - L y)‖ := by rw [sub_add_cancel]
              _ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_add_le _ _
              _ ≤ δ * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add h1 le_rfl
              _ = (1 + δ) * ‖L x - L y‖ := by rw [add_comm, one_add_mul]
          · rw [hlin, ← mul_assoc, ENNReal.ofReal_mul (pow_pos h1δ d).le,
              ENNReal.ofReal_pow h1δ.le]
            rfl
        · refine ge_of_tendsto hD ?_
          filter_upwards [hev] with t ht
          rw [ENNReal.le_div_iff_mul_le (Or.inl (measure_closedBall_pos _ u ht.1).ne')
            (Or.inl measure_closedBall_lt_top.ne), hνt t ht.2]
          have himg' : (L : E →ₗ[ℝ] F) '' closedBall u t = (fun p ↦ L (ψ p)) ''
              (φ '' closedBall u t) := by
            rw [image_image]
            exact image_congr fun x hx ↦ by rw [hψφ x (ht.2 hx).2]; rfl
          have hle : μHE[d] ((L : E →ₗ[ℝ] F) '' closedBall u t) ≤
              (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ d * μHE[d] (φ '' closedBall u t) := by
            rw [himg']
            refine Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d
              (LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_)
            obtain ⟨x, hx, rfl⟩ := hp
            obtain ⟨y, hy, rfl⟩ := hq
            rw [hψφ x (ht.2 hx).2, hψφ y (ht.2 hy).2, dist_eq_norm, dist_eq_norm,
              Real.coe_toNNReal _ (inv_nonneg.mpr h1δ'.le), ← div_eq_inv_mul, le_div_iff₀ h1δ',
              mul_sub, mul_one, sub_le_iff_le_add]
            have h1 := hA' x (ht.2 hx).1 y (ht.2 hy).1
            have h2 : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
              calc ‖L x - L y‖ = ‖(φ x - φ y) - (φ x - φ y - (L x - L y))‖ := by rw [sub_sub_cancel]
                _ ≤ _ := norm_sub_le _ _
            exact h2.trans (add_le_add le_rfl (h1.trans_eq (mul_comm _ _)))
          rw [hlin] at hle
          calc ENNReal.ofReal ((1 - δ) ^ d * J) * μHE[d] (closedBall u t)
              = ENNReal.ofReal ((1 - δ) ^ d) * (ENNReal.ofReal J * μHE[d] (closedBall u t)) := by
                rw [ENNReal.ofReal_mul (pow_pos h1δ' d).le, mul_assoc]
            _ ≤ ENNReal.ofReal ((1 - δ) ^ d) *
                ((Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ d * μHE[d] (φ '' closedBall u t)) :=
                mul_le_mul' le_rfl hle
            _ = μHE[d] (φ '' closedBall u t) := by
                rw [← mul_assoc, show (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) =
                    ENNReal.ofReal (1 - δ)⁻¹ from rfl,
                  ← ENNReal.ofReal_pow (inv_nonneg.mpr h1δ'.le), ← ENNReal.ofReal_mul
                  (pow_pos h1δ' d).le, ← mul_pow, mul_inv_cancel₀ h1δ'.ne', one_pow,
                  ENNReal.ofReal_one, one_mul]
      apply le_antisymm
      · have ht : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal ((1 + δ) ^ d * J)) (𝓝[>] 0)
            (𝓝 (ENNReal.ofReal J)) := by
          have h : Tendsto (fun δ : ℝ ↦ (1 + δ) ^ d * J) (𝓝 0) (𝓝 ((1 + 0) ^ d * J)) :=
            ((tendsto_const_nhds.add tendsto_id).pow d).mul tendsto_const_nhds
          rw [add_zero, one_pow, one_mul] at h
          exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
        refine ge_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ hδ
        exact (key δ hδ.1 hδ.2).1
      · have ht : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal ((1 - δ) ^ d * J)) (𝓝[>] 0)
            (𝓝 (ENNReal.ofReal J)) := by
          have h : Tendsto (fun δ : ℝ ↦ (1 - δ) ^ d * J) (𝓝 0) (𝓝 ((1 - 0) ^ d * J)) :=
            ((tendsto_const_nhds.sub tendsto_id).pow d).mul tendsto_const_nhds
          rw [sub_zero, one_pow, one_mul] at h
          exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
        refine le_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ hδ
        exact (key δ hδ.1 hδ.2).2
    have hae : ∀ᵐ u ∂((μHE[d] : Measure E).restrict (ball b r)),
        ν.rnDeriv μHE[d] u = ENNReal.ofReal (fderiv ℝ φ u : E →ₗ[ℝ] F).normDet := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν (μHE[d] : Measure E)] with u hu hub
      exact hpt u hub _ hu
    calc ν = ν.restrict (ball b r) :=
          (Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hνB)).symm
      _ = ((μHE[d] : Measure E).withDensity (ν.rnDeriv μHE[d])).restrict (ball b r) := by
          rw [Measure.withDensity_rnDeriv_eq ν _ hac]
      _ = ((μHE[d] : Measure E).restrict (ball b r)).withDensity (ν.rnDeriv μHE[d]) :=
          restrict_withDensity measurableSet_ball _
      _ = _ := withDensity_congr_ae hae
  -- the calculus half of the coordinate divergence identity
  have GPx : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (NJ : (E →L[ℝ] F) → ℝ) (φ : E → F) (ζ : E → ℝ) (u v : E) (Y : E → E)
      (hφ : ContDiffAt ℝ 2 φ u) (hN : DifferentiableAt ℝ NJ (fderiv ℝ φ u))
      (hN0 : NJ (fderiv ℝ φ u) ≠ 0) (hζ : DifferentiableAt ℝ ζ u)
      (hY : ∀ w, Y w = (ζ w / NJ (fderiv ℝ φ w)) • v),
      ∃ ℓ : E →L[ℝ] ℝ,
        HasDerivAt (fun t : ℝ ↦ NJ (fderiv ℝ φ u + t • fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) u))
          (fderiv ℝ ζ u v - NJ (fderiv ℝ φ u) * ℓ v +
            fderiv ℝ NJ (fderiv ℝ φ u) (ℓ.smulRight (fderiv ℝ φ u v))) 0 ∧
        HasDerivAt (fun t : ℝ ↦ NJ (fderiv ℝ φ u + t • ℓ.smulRight (fderiv ℝ φ u v)))
          (fderiv ℝ NJ (fderiv ℝ φ u) (ℓ.smulRight (fderiv ℝ φ u v))) 0 := by
    intro E F _ _ _ _ _ _ NJ φ ζ u v Y hφ hN hN0 hζ hY
    have hNd := hN.hasFDerivAt
    have hDφd := ((hφ.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt
      one_ne_zero).hasFDerivAt
    have hJd := hNd.comp u hDφd
    obtain ⟨ℓ, hgd⟩ : ∃ ℓ, HasFDerivAt (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) ℓ u :=
      ⟨_, (hζ.mul (hJd.differentiableAt.inv hN0)).hasFDerivAt⟩
    refine ⟨ℓ, (hNd.hasLineDerivAt _).congr_deriv ?_, hNd.hasLineDerivAt _⟩
    have hfun : (fun w ↦ fderiv ℝ φ w (Y w)) =
        (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) • fun w ↦ fderiv ℝ φ w v :=
      funext fun w ↦ by rw [hY, map_smul]; rfl
    have hsym := hφ.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le
    have hKe : fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) u =
        (ζ u / NJ (fderiv ℝ φ u)) • fderiv ℝ (fderiv ℝ φ) u v + ℓ.smulRight (fderiv ℝ φ u v) := by
      have hWd : HasFDerivAt (fun w ↦ fderiv ℝ φ w v)
          ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) u)) u :=
        (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp u hDφd
      rw [hfun, (hgd.smul hWd).fderiv]
      congr 2
      ext w
      exact hsym w v
    have hev2 : ζ =ᶠ[𝓝 u] (fun w ↦ ζ w / NJ (fderiv ℝ φ w)) * (NJ ∘ fderiv ℝ φ) := by
      filter_upwards [hJd.continuousAt.eventually_ne hN0] with w hw
      exact (div_mul_cancel₀ _ hw).symm
    rw [hKe, map_add, map_smul, smul_eq_mul, hev2.fderiv_eq, (hgd.mul hJd).fderiv]
    exact congrArg (· + _) (add_sub_cancel_right (G := ℝ) _ _).symm
  -- `normDet` on charts
  obtain ⟨NJ, hNJ⟩ : ∃ NJ : (Euclidean n →L[ℝ] Euclidean N) → ℝ,
      ∀ T, NJ T = (T : Euclidean n →ₗ[ℝ] Euclidean N).normDet := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hNc, GN⟩ := GNg _ _ NJ hNJ
  have hNpos : ∀ T : Euclidean n →L[ℝ] Euclidean N, Function.Injective T → 0 < NJ T := by
    intro T hT
    rw [hNJ]
    exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm (mt
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp (not_not.mpr (LinearMap.ker_eq_bot.mpr hT))))
  have hN0 : ∀ T, 0 ≤ NJ T := fun T ↦ by rw [hNJ]; exact LinearMap.normDet_nonneg _
  have G4w : ∀ (ϑ : Measure (Euclidean n)) [IsFiniteMeasure ϑ] (J : Euclidean n → ℝ)
      (a : Euclidean n) (R m : ℝ), 0 < R → 0 < m → Measurable J → (∀ᵐ u ∂ϑ, m ≤ J u) →
      (∀ ζ : Euclidean n → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a R → ∀ v,
        ∫ u, (1 / J u) * fderiv ℝ ζ u v ∂ϑ = 0) →
      ∃ c : ℝ, ϑ.restrict (ball a (R / 2 / 2 / 2)) = ENNReal.ofReal c •
        (volume.restrict (ball a (R / 2 / 2 / 2))).withDensity (fun u ↦ ENNReal.ofReal (J u)) := by
    intro ϑ _ J a R m hR hm hJ hJm h
    exact G4wg _ volume ϑ J a R m hR hm hJ hJm h
  have G5 : ∀ (φ : Euclidean n → Euclidean N) (ψ : Euclidean N → Euclidean n) (b : Euclidean n)
      (r : ℝ) (K : NNReal), (∀ u ∈ ball b r, ContDiffAt ℝ 1 φ u) →
      (∀ u ∈ ball b r, Function.Injective (fderiv ℝ φ u)) →
      (∀ u ∈ ball b r, ψ (φ u) = u) → LipschitzOnWith K φ (ball b r) →
      MeasurableSet (φ '' ball b r) → ContinuousOn ψ (φ '' ball b r) →
      ((μHE[n] : Measure (Euclidean N)).restrict (φ '' ball b r)).map ψ =
        (volume.restrict (ball b r)).withDensity (fun u ↦ ENNReal.ofReal (NJ (fderiv ℝ φ u))) := by
    intro φ ψ b r K hφ hinj hψφ hK hm hψ
    have h := G5g _ _ φ ψ b r K hφ hinj hψφ hK hm hψ
    rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
    rw [h]
    congr 1
    funext u
    rw [hNJ]
  -- basic facts
  have hU : IsOpen U := V.isOpen_domain
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = V.weight := ⟨_, rfl⟩
  rw [← hμ] at hM
  have hμU : μ Uᶜ = 0 := by rw [hμ, V.weight_apply hU.measurableSet.compl]; exact V.supported
  have hμM : μ (M ∩ U)ᶜ = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hμU μ.measure_compl_support)
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hx ⟨hM ⟨h.1, h.2⟩, h.1⟩
  have hVM : ∀ᵐ z ∂V.measure, z.1 ∈ M ∩ U :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [← Varifold.weight, ← hμ]; exact hμM)
  have hfst : ∀ z ∈ V.measure.support, z.1 ∈ μ.support := fun z hz ↦
    Measure.support_subset_of_isClosed (μ.isClosed_support.preimage continuous_fst)
      (ae_of_ae_map measurable_fst.aemeasurable
        (by rw [← Varifold.weight, ← hμ]; exact μ.support_mem_ae)) hz
  -- the tangential divergence as a trace
  have hTD : ∀ (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n),
      Varifold.tangentialDivergence X x S = LinearMap.trace ℝ (Euclidean N)
        (S.projectionLinearMap ∘ₗ (fderiv ℝ X x : Euclidean N →ₗ[ℝ] Euclidean N)) := by
    intro X x S
    rw [Varifold.tangentialDivergence, LinearMap.trace_eq_matrix_trace ℝ
      Grassmannian.coordinateBasis.toBasis, LinearMap.toMatrix_comp
        Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis]
    simp [Varifold.jacobian_eq_toMatrix]
  -- P1: every support plane is the chart tangent plane
  have hP1 : ∀ z ∈ V.measure.support, z.1 ∈ U → ∀ (D : Set (Euclidean n)) (W : Set (Euclidean N))
      (φ : Euclidean n → Euclidean N), Chapter02.IsSimonLocalRepresentation 2 M D W φ →
      ∀ a ∈ D, φ a = z.1 →
        z.2.plane = LinearMap.range (fderiv ℝ φ a : Euclidean n →ₗ[ℝ] Euclidean N) := by
    intro z hz hzU D W φ hφ a ha hφa
    obtain ⟨ψ, T₀, hT₀o, hφaT₀, hψc, hψD, hψM⟩ := GI _ _ M W D φ hφ a ha
    obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ φ a := ⟨_, rfl⟩
    rw [← hL]
    have hzM : z.1 ∈ M := hM ⟨hzU, hfst z hz⟩
    have hψa : ψ z.1 = a := hφ.injOn (hψD (hφa ▸ hφaT₀)) ha (by
      rw [hψM z.1 ⟨hzM, hφa ▸ hφaT₀⟩, hφa])
    have key : ∀ e ∈ (LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N))ᗮ,
        z.2.projectionLinearMap e = 0 := by
      intro e he
      obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp (hT₀o.inter hU) z.1 ⟨hφa ▸ hφaT₀, hzU⟩
      let χ : ContDiffBump z.1 :=
          ⟨r / 2 / 2, r / 2, half_pos (half_pos hr), half_lt_self (half_pos hr)⟩
      have hχs : tsupport χ ⊆ T₀ ∩ U := by
        rw [χ.tsupport_eq]; exact (closedBall_subset_ball (half_lt_self hr)).trans hrT
      have hφc2 : ContDiffOn ℝ 2 φ D := hφ.contDiffOn
      have hg : ContDiffOn ℝ 2 (fun y ↦ inner ℝ e (y - φ (ψ y))) T₀ :=
        (contDiffOn_const.inner ℝ (contDiffOn_id.sub (hφc2.comp hψc hψD)))
      obtain ⟨f, hfdef⟩ : ∃ f : Euclidean N → ℝ, f = fun y ↦ χ y • inner ℝ e (y - φ (ψ y)) :=
        ⟨_, rfl⟩
      have hf : ContDiff ℝ 2 f := hfdef ▸ GCut _ _ 2 χ _ T₀ hT₀o χ.contDiff hg
        (hχs.trans inter_subset_left)
      have hfs : tsupport f ⊆ T₀ ∩ U := hfdef ▸ (tsupport_smul_subset_left _ _).trans hχs
      have hfc : HasCompactSupport f := hfdef ▸ χ.hasCompactSupport.smul_right
      have hfM : ∀ y ∈ M, f y = 0 := by
        intro y hy
        by_cases hyT : y ∈ T₀
        · rw [hfdef]; simp only [hψM y ⟨hy, hyT⟩, sub_self, inner_zero_right, smul_zero]
        · exact image_eq_zero_of_notMem_tsupport fun h ↦ hyT (hfs h).1
      obtain ⟨G, hGdef⟩ : ∃ G : Euclidean N → Euclidean N,
          G = fun y ↦ (InnerProductSpace.toDual ℝ (Euclidean N)).symm (fderiv ℝ f y) := ⟨_, rfl⟩
      have hG : ContDiff ℝ 1 G := hGdef ▸
        (InnerProductSpace.toDual ℝ (Euclidean N)).symm.contDiff.comp
          (hf.fderiv_right one_add_one_eq_two.le)
      have hfd : ∀ y, HasFDerivAt f (fderiv ℝ f y) y := fun y ↦
        (hf.differentiable two_ne_zero y).hasFDerivAt
      -- the gradient at the base point is `e`
      have hGz : G z.1 = e := by
        have hψd : DifferentiableAt ℝ ψ z.1 :=
          (hψc.contDiffAt (hT₀o.mem_nhds (hφa ▸ hφaT₀))).differentiableAt two_ne_zero
        have hφd : HasFDerivAt φ L (ψ z.1) := by
          rw [hψa, hL]
          exact ((hφc2.contDiffAt (hφ.isOpen_source.mem_nhds ha)).differentiableAt
            two_ne_zero).hasFDerivAt
        have hgd : HasFDerivAt (fun y ↦ inner ℝ e (y - φ (ψ y)))
            ((innerSL ℝ e).comp (ContinuousLinearMap.id ℝ _ - L.comp (fderiv ℝ ψ z.1))) z.1 :=
          (innerSL ℝ e).hasFDerivAt.comp z.1
            ((hasFDerivAt_id z.1).sub (hφd.comp z.1 hψd.hasFDerivAt))
        have hχd := (χ.contDiff (n := 1)).differentiable one_ne_zero z.1
        have h1 := hχd.hasFDerivAt.smul hgd
        rw [show ((χ : Euclidean N → ℝ) • fun y ↦ inner ℝ e (y - φ (ψ y))) = f from hfdef.symm]
            at h1
        have h2 : fderiv ℝ f z.1 = innerSL ℝ e := by
          rw [h1.fderiv]
          ext v
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
            χ.one_of_mem_closedBall (mem_closedBall_self (half_pos (half_pos hr)).le), one_smul,
            innerSL_apply_apply, hψa, hφa, sub_self, inner_zero_right, smul_eq_mul,
            mul_zero, add_zero, inner_sub_right]
          rw [show inner ℝ e (L ((fderiv ℝ ψ z.1) v)) = 0 from
            (Submodule.mem_orthogonal' _ e).mp he _
              (LinearMap.mem_range_self (L : Euclidean n →ₗ[ℝ] Euclidean N) _), sub_zero]
        rw [hGdef]
        simp only [h2]
        exact (InnerProductSpace.toDual ℝ (Euclidean N)).symm_apply_apply e
      -- the test field `f ∇f`
      let X : Varifold.TestVectorField (N := N) U :=
        ⟨fun y ↦ f y • G y, (hf.of_le one_le_two).smul hG, hfc.smul_right,
          (tsupport_smul_subset_left _ _).trans (hfs.trans inter_subset_right)⟩
      have hdiv : ∀ (y : Euclidean N) (S : Grassmannian N n), f y = 0 →
          Varifold.tangentialDivergence X y S = ‖S.projectionLinearMap (G y)‖ ^ 2 := by
        intro y S hy
        have hd := ((hfd y).smul (hG.differentiable one_ne_zero y).hasFDerivAt).fderiv
        rw [hy, zero_smul, zero_add] at hd
        change Varifold.tangentialDivergence (f • G) y S = _
        rw [hTD, hd, show S.projectionLinearMap ∘ₗ
            (((fderiv ℝ f y).smulRight (G y) : Euclidean N →L[ℝ] Euclidean N) :
              Euclidean N →ₗ[ℝ] Euclidean N) =
            (fderiv ℝ f y : Euclidean N →ₗ[ℝ] ℝ).smulRight (S.projectionLinearMap (G y)) from
          LinearMap.ext fun v ↦ map_smul S.projectionLinearMap (fderiv ℝ f y v) (G y),
          LinearMap.trace_smulRight]
        have hG' : fderiv ℝ f y (S.projectionLinearMap (G y)) =
            inner ℝ (G y) (S.projectionLinearMap (G y)) := by
          rw [hGdef]; exact (InnerProductSpace.toDual_symm_apply).symm
        rw [ContinuousLinearMap.coe_coe, hG']
        calc inner ℝ (G y) (S.projectionLinearMap (G y))
            = inner ℝ (G y) (S.projectionLinearMap (S.projectionLinearMap (G y))) := by
              rw [← LinearMap.comp_apply, S.projectionLinearMap_comp_self]
          _ = inner ℝ (S.projectionLinearMap (G y)) (S.projectionLinearMap (G y)) :=
              (S.projectionLinearMap_isSymmetric _ _).symm
          _ = ‖S.projectionLinearMap (G y)‖ ^ 2 := real_inner_self_eq_norm_sq _
      have hint : ∫ z', Varifold.tangentialDivergence X z'.1 z'.2 ∂V.measure = 0 := hV X
      have hnn : 0 ≤ᵐ[V.measure] fun z' ↦ Varifold.tangentialDivergence X z'.1 z'.2 := by
        filter_upwards [hVM] with z' hz'
        rw [hdiv _ _ (hfM _ hz'.1)]
        exact sq_nonneg _
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
        (V.integrable_tangentialDivergence X X.contDiff X.compactSupport X.support_subset)).mp hint
      have hz0 : Varifold.tangentialDivergence X z.1 z.2 = 0 :=
        Measure.support_subset_of_isClosed
          (isClosed_eq (Varifold.continuous_tangentialDivergence X.contDiff) continuous_const)
          hae hz
      rw [hdiv _ _ (hfM _ hzM), hGz] at hz0
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz0)
    have hle : z.2.plane ≤ LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N) := by
      intro s hs
      rw [← Submodule.orthogonal_orthogonal (LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N))]
      intro e he
      rw [← z.2.projectionLinearMap_apply_of_mem hs, ← z.2.projectionLinearMap_isSymmetric,
        key e he, inner_zero_left]
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [z.2.finrank_plane, LinearMap.finrank_range_of_inj (hL ▸ hφ.injective_fderiv ha),
        finrank_euclideanSpace_fin])
  -- P2: the plane field `T`
  have hGext : ∀ S₁ S₂ : Grassmannian N n, S₁.plane = S₂.plane → S₁ = S₂ := by
    intro S₁ S₂ h
    rw [← Grassmannian.ofSubmodule_plane S₁, ← Grassmannian.ofSubmodule_plane S₂]
    congr 1
  obtain ⟨P₀⟩ : Nonempty (Grassmannian N n) := by
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨D₀, W₀, φ₀, hxW₀, hφ₀⟩ := hSM.exists_localRepresentation hx₀
    obtain ⟨a₀, ha₀, -⟩ : x₀ ∈ φ₀ '' D₀ := hφ₀.image_eq ▸ ⟨hxW₀, hx₀⟩
    exact ⟨Grassmannian.ofSubmodule (LinearMap.range (fderiv ℝ φ₀ a₀ :
      Euclidean n →ₗ[ℝ] Euclidean N)) (by rw [LinearMap.finrank_range_of_inj
        (hφ₀.injective_fderiv ha₀), finrank_euclideanSpace_fin])⟩
  have hfib : ∀ x ∈ μ.support, ∃ S, (x, S) ∈ V.measure.support := by
    intro x hx
    by_contra h
    simp only [not_exists] at h
    obtain ⟨O, Q, hO, -, hxO, hQ, hOQ⟩ := generalized_tube_lemma isCompact_singleton
      isCompact_univ V.measure.isOpen_compl_support
      (fun p hp ↦ by
        obtain ⟨y, S⟩ := p
        obtain rfl : y = x := hp.1
        exact h S)
    refine ((Measure.mem_support_iff_forall x).mp hx O (hO.mem_nhds (hxO rfl))).ne' ?_
    rw [hμ, V.weight_apply hO.measurableSet]
    exact measure_mono_null (fun p hp ↦ hOQ ⟨hp.1, hQ (mem_univ _)⟩)
      V.measure.measure_compl_support
  classical
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclidean N → Grassmannian N n, ∀ x ∈ μ.support,
      (x, τ x) ∈ V.measure.support :=
    ⟨fun x ↦ if h : ∃ S, (x, S) ∈ V.measure.support then h.choose else P₀,
      fun x hx ↦ by simp only [dif_pos (hfib x hx)]; exact (hfib x hx).choose_spec⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Euclidean N → Grassmannian N n,
      T = (U ∩ μ.support).piecewise τ (fun _ ↦ P₀) := ⟨_, rfl⟩
  have hTτ : ∀ x ∈ U ∩ μ.support, T x = τ x := fun x hx ↦ by
    rw [hTdef]; exact piecewise_eq_of_mem _ _ _ hx
  have hTspt : ∀ x ∈ U ∩ μ.support, (x, T x) ∈ V.measure.support := fun x hx ↦
    hTτ x hx ▸ hτ x hx.2
  have hTuniq : ∀ z ∈ V.measure.support, z.1 ∈ U → z.2 = T z.1 := by
    intro z hz hzU
    have hx : z.1 ∈ U ∩ μ.support := ⟨hzU, hfst z hz⟩
    obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation (hM hx)
    obtain ⟨a, ha, hφa⟩ : z.1 ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hM hx⟩
    exact hGext _ _ ((hP1 z hz hzU D W φ hφ a ha hφa).trans
      (hP1 (z.1, T z.1) (hTspt z.1 hx) hzU D W φ hφ a ha hφa).symm)
  have hTc : ContinuousOn T (U ∩ μ.support) := by
    intro x hx
    rw [ContinuousWithinAt, _root_.tendsto_nhds]
    intro Q hQ hTxQ
    obtain ⟨O, Q', hO, -, hxO, hQQ', hOQ'⟩ := generalized_tube_lemma isCompact_singleton
      hQ.isClosed_compl.isCompact V.measure.isOpen_compl_support (by
        rintro ⟨y, S⟩ ⟨hy, hS⟩ hyS
        obtain rfl : y = x := hy
        exact hS ((congrArg (· ∈ Q) (hTuniq (y, S) hyS hx.1)).mpr hTxQ))
    filter_upwards [inter_mem_nhdsWithin _ (hO.mem_nhds (hxO rfl))] with y hy
    by_contra hyQ
    exact hOQ' (show (y, T y) ∈ O ×ˢ Q' from ⟨hy.2, hQQ' hyQ⟩) (hTspt y hy.1)
  have hTm : Measurable T := by
    have h := ContinuousOn.measurable_piecewise (f := τ) (g := fun _ ↦ P₀)
      (hTc.congr fun x hx ↦ (hTτ x hx).symm) continuousOn_const
      (hU.measurableSet.inter μ.isClosed_support.measurableSet)
    rwa [← hTdef] at h
  have hgm : Measurable fun x : Euclidean N ↦ (x, T x) := measurable_id.prodMk hTm
  have hVT : V.measure = μ.map (fun x ↦ (x, T x)) := by
    rw [hμ, Varifold.weight, Measure.map_map (show Measurable fun x : Euclidean N ↦ (x, T x) from
      measurable_id.prodMk hTm) measurable_fst,
      Measure.map_congr (g := id) ?_, Measure.map_id]
    filter_upwards [V.measure.support_mem_ae, hVM] with z hz hzM
    exact Prod.ext rfl (hTuniq z hz hzM.2).symm
  -- the Euclidean half of the coordinate divergence identity
  have hGE : ∀ (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
      (L : Euclidean n →L[ℝ] Euclidean N), DifferentiableAt ℝ X x →
      S.plane = LinearMap.range (L : Euclidean n →ₗ[ℝ] Euclidean N) →
      HasDerivAt (fun t : ℝ ↦ NJ (L + t • (fderiv ℝ X x).comp L))
        (Varifold.tangentialDivergence X x S * NJ L) 0 := by
    intro X x S L hX hS
    refine ((Varifold.hasDerivAt_tangentialJacobianReal_id_add_smul X x S hX).mul_const
      (NJ L)).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    have hd := HasFDerivAt.fderiv (f := fun y ↦ y + t • X y)
      ((hasFDerivAt_id x).add (hX.hasFDerivAt.const_smul t))
    simp only [Varifold.tangentialJacobianReal, Varifold.tangentialDerivative, hd, hNJ]
    have hdr : ∀ (g : Euclidean N →ₗ[ℝ] Euclidean N) (p q : Submodule ℝ (Euclidean N)), p = q →
        (g.domRestrict p).normDet = (g.domRestrict q).normDet := by rintro g p q rfl; rfl
    rw [hdr _ _ _ hS, ← LinearMap.normDet_comp]
    congr 1
  -- local constancy
  have hLC : ∀ x₀ ∈ M ∩ U, ∃ O : Set (Euclidean N), IsOpen O ∧ x₀ ∈ O ∧ O ⊆ U ∧ ∃ c : ℝ≥0∞,
      c ≠ ∞ ∧ μ.restrict O = c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ O) ∧
      μHE[n] (M ∩ O) ≠ ∞ ∧ ∀ O', IsOpen O' → x₀ ∈ O' → 0 < μHE[n] (M ∩ O' ∩ O) := by
    intro x₀ hx₀
    obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx₀.1
    obtain ⟨a, ha, hφa⟩ : x₀ ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hx₀.1⟩
    obtain ⟨ψ, T₀, hT₀o, hφaT₀, hψc, hψD, hψM⟩ := GI _ _ M W D φ hφ a ha
    have hx₀T : x₀ ∈ T₀ := hφa ▸ hφaT₀
    have hDo : IsOpen D := hφ.isOpen_source
    have hφc2 : ContDiffOn ℝ 2 φ D := hφ.contDiffOn
    have hφM : ∀ w ∈ D, φ w ∈ M := fun w hw ↦ (hφ.image_eq ▸ mem_image_of_mem φ hw).2
    have hψφ : ∀ w ∈ D, φ w ∈ T₀ → ψ (φ w) = w := fun w hw hwT ↦
      hφ.injOn (hψD hwT) hw (hψM _ ⟨hφM w hw, hwT⟩)
    have hψa : ψ x₀ = a := by rw [← hφa]; exact hψφ a ha hφaT₀
    obtain ⟨ρ, hρ, hρT⟩ := Metric.isOpen_iff.mp (hT₀o.inter hU) x₀ ⟨hx₀T, hx₀.2⟩
    have hK₀ : closedBall x₀ (ρ / 2) ⊆ T₀ ∩ U :=
      (closedBall_subset_ball (half_lt_self hρ)).trans hρT
    have hρ2 : 0 < ρ / 2 := half_pos hρ
    have hρ8 : 0 < ρ / 2 / 2 / 2 := half_pos (half_pos hρ2)
    obtain ⟨R, hR, hRD⟩ : ∃ R > 0, ball a R ⊆ D ∩ φ ⁻¹' ball x₀ (ρ / 2 / 2 / 2) :=
      Metric.mem_nhds_iff.mp (inter_mem (hDo.mem_nhds ha)
        ((hφc2.continuousOn.continuousAt (hDo.mem_nhds ha)).preimage_mem_nhds
          (by rw [hφa]; exact ball_mem_nhds x₀ hρ8)))
    have hDφ := hφc2.fderiv_of_isOpen hDo (m := 1) one_add_one_eq_two.le
    have hJc : ContDiffOn ℝ 1 (fun w ↦ NJ (fderiv ℝ φ w)) D := fun w hw ↦
      ((GN _ (hφ.injective_fderiv hw)).comp w (hDφ.contDiffAt (hDo.mem_nhds hw))).contDiffWithinAt
    have hJpos : ∀ w ∈ D, 0 < NJ (fderiv ℝ φ w) := fun w hw ↦ hNpos _ (hφ.injective_fderiv hw)
    -- a positive lower bound for `J ∘ ψ` near `x₀`
    have hψK : ∀ x ∈ closedBall x₀ (ρ / 2), ψ x ∈ D := fun x hx ↦ hψD (hK₀ hx).1
    obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x₀ (ρ / 2)).exists_isMinOn
      ⟨x₀, mem_closedBall_self hρ2.le⟩
      (hJc.continuousOn.comp (hψc.continuousOn.mono fun x hx ↦ (hK₀ hx).1) hψK)
    have hm : 0 < NJ (fderiv ℝ φ (ψ xm)) := hJpos _ (hψK xm hxm)
    -- the weighted pulled-back measure
    have hψB : ContinuousOn ψ (ball x₀ (ρ / 2)) :=
      hψc.continuousOn.mono fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).1
    have hψm : AEMeasurable ψ (μ.restrict (ball x₀ (ρ / 2))) := hψB.aemeasurable measurableSet_ball
    have hμK : μ (closedBall x₀ (ρ / 2)) ≠ ∞ := by
      rw [hμ]; exact V.weight_finite_on_compact _ (isCompact_closedBall _ _)
          (hK₀.trans inter_subset_right)
    obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : Measure (Euclidean n), ϑ = (μ.restrict (ball x₀ (ρ / 2))).map ψ :=
        ⟨_, rfl⟩
    have hϑfin : ϑ univ < ∞ := by
      rw [hϑ, Measure.map_apply_of_aemeasurable hψm MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt (lt_top_iff_ne_top.mpr hμK)
    have hJm : Measurable (fun u ↦ NJ (fderiv ℝ φ u)) := hNc.measurable.comp (measurable_fderiv ℝ φ)
    have hϑm : ∀ᵐ u ∂ϑ, NJ (fderiv ℝ φ (ψ xm)) ≤ NJ (fderiv ℝ φ u) := by
      rw [hϑ, ae_map_iff hψm (measurableSet_le measurable_const hJm),
        ae_restrict_iff' measurableSet_ball]
      exact Eventually.of_forall fun x hx ↦ (isMinOn_iff.mp hmin) x (ball_subset_closedBall hx)
    -- the hypothesis of the distributional constancy lemma, from tangent test fields
    have hT₀B : ball x₀ (ρ / 2) ⊆ T₀ := fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).1
    have hMU : M ∩ U ∈ ae μ := mem_ae_iff.mpr hμM
    have hG4h : ∀ ζ : Euclidean n → ℝ, ContDiff ℝ 1 ζ → tsupport ζ ⊆ ball a (R / 2) → ∀ v,
        ∫ u, (1 / NJ (fderiv ℝ φ u)) * fderiv ℝ ζ u v ∂ϑ = 0 := by
      intro ζ hζ hζs v
      obtain ⟨Y, hY⟩ : ∃ Y : Euclidean n → Euclidean n,
          ∀ w, Y w = (ζ w / NJ (fderiv ℝ φ w)) • v := ⟨_, fun _ ↦ rfl⟩
      have hYc : ContDiffOn ℝ 1 Y D := by
        rw [funext hY]
        exact (hζ.contDiffOn.div hJc fun w hw ↦ (hJpos w hw).ne').smul contDiffOn_const
      have hY0 : ∀ w, w ∉ ball a (R / 2) → Y w = 0 := fun w hw ↦ by
        rw [hY, image_eq_zero_of_notMem_tsupport (fun h ↦ hw (hζs h)), zero_div, zero_smul]
      let χ : ContDiffBump x₀ := ⟨ρ / 2 / 2 / 2, ρ / 2 / 2, hρ8, half_lt_self (half_pos hρ2)⟩
      have hχs : tsupport χ ⊆ ball x₀ (ρ / 2) := by
        rw [χ.tsupport_eq]; exact closedBall_subset_ball (half_lt_self hρ2)
      obtain ⟨Xf, hXf⟩ : ∃ Xf : Euclidean N → Euclidean N,
          Xf = fun y ↦ χ y • fderiv ℝ φ (ψ y) (Y (ψ y)) := ⟨_, rfl⟩
      have hψ1 : ContDiffOn ℝ 1 ψ T₀ := hψc.of_le one_le_two
      have hXc : ContDiff ℝ 1 Xf := by
        rw [hXf]
        exact GCut _ _ 1 χ _ T₀ hT₀o χ.contDiff ((hDφ.comp hψ1 hψD).clm_apply
          (hYc.comp hψ1 hψD)) (hχs.trans hT₀B)
      have hXs : tsupport Xf ⊆ ball x₀ (ρ / 2) := by
        rw [hXf]; exact (tsupport_smul_subset_left _ _).trans hχs
      let X : Varifold.TestVectorField (N := N) U := ⟨Xf, hXc,
        (isCompact_closedBall x₀ (ρ / 2)).of_isClosed_subset (isClosed_tsupport _)
          (hXs.trans ball_subset_closedBall),
        hXs.trans fun x hx ↦ (hK₀ (ball_subset_closedBall hx)).2⟩
      -- the coordinate divergence identity at chart points
      have hdiv : ∀ x ∈ ball x₀ (ρ / 2), x ∈ M → x ∈ μ.support →
          Varifold.tangentialDivergence Xf x (T x) =
            (1 / NJ (fderiv ℝ φ (ψ x))) * fderiv ℝ ζ (ψ x) v := by
        intro x hxB hxM hxs
        have hxT : x ∈ T₀ := hT₀B hxB
        have hxU : x ∈ U := (hK₀ (ball_subset_closedBall hxB)).2
        have hu : ψ x ∈ D := hψD hxT
        have hφu : φ (ψ x) = x := hψM x ⟨hxM, hxT⟩
        have hplane := hP1 (x, T x) (hTspt x ⟨hxU, hxs⟩) hxU D W φ hφ (ψ x) hu hφu
        have hev : (fun w ↦ Xf (φ w)) =ᶠ[𝓝 (ψ x)] fun w ↦ fderiv ℝ φ w (Y w) := by
          filter_upwards [hDo.mem_nhds hu,
            (hφc2.continuousOn.continuousAt (hDo.mem_nhds hu)).preimage_mem_nhds
              (hT₀o.mem_nhds (by rw [hφu]; exact hxT))] with w hw hwT
          rw [hXf]
          simp only [hψφ w hw hwT]
          by_cases hwB : w ∈ ball a (R / 2)
          · rw [χ.one_of_mem_closedBall (ball_subset_closedBall
              (hRD (ball_subset_ball (half_le_self hR.le) hwB)).2), one_smul]
          · rw [hY0 w hwB, map_zero, smul_zero]
        have hφd : DifferentiableAt ℝ φ (ψ x) :=
          (hφc2.contDiffAt (hDo.mem_nhds hu)).differentiableAt two_ne_zero
        have hK : (fderiv ℝ Xf x).comp (fderiv ℝ φ (ψ x)) =
            fderiv ℝ (fun w ↦ fderiv ℝ φ w (Y w)) (ψ x) := by
          rw [← hev.fderiv_eq]
          have := fderiv_comp (ψ x) (hXc.differentiable one_ne_zero (φ (ψ x))) hφd
          rw [hφu] at this
          exact this.symm
        have h1 := hGE Xf x (T x) (fderiv ℝ φ (ψ x)) (hXc.differentiable one_ne_zero x) hplane
        rw [hK] at h1
        -- the calculus half of the identity, from the generic lemma
        obtain ⟨ℓ, hK1, hK2⟩ := GPx _ _ NJ φ ζ (ψ x) v Y (hφc2.contDiffAt (hDo.mem_nhds hu))
          ((GN _ (hφ.injective_fderiv hu)).differentiableAt one_ne_zero) (hJpos _ hu).ne'
          (hζ.differentiable one_ne_zero _) hY
        have e1 := h1.unique hK1
        -- the rank-one part, through `hGE` for an auxiliary linear field
        obtain ⟨P', hP'⟩ :=
            ((fderiv ℝ φ (ψ x)) : Euclidean n →ₗ[ℝ] Euclidean N).exists_leftInverse_of_injective
          (LinearMap.ker_eq_bot.mpr (hφ.injective_fderiv hu))
        obtain ⟨Pl, hPl⟩ : ∃ Pl : Euclidean N →L[ℝ] Euclidean n, ∀ w, Pl (fderiv ℝ φ (ψ x) w) = w :=
          ⟨LinearMap.toContinuousLinearMap P', fun w ↦ LinearMap.congr_fun hP' w⟩
        obtain ⟨X₂, hX₂⟩ : ∃ X₂ : Euclidean N →L[ℝ] Euclidean N,
            X₂ = (ℓ.comp Pl).smulRight (fderiv ℝ φ (ψ x) v) := ⟨_, rfl⟩
        have h4 := hGE X₂ x (T x) (fderiv ℝ φ (ψ x)) X₂.differentiableAt hplane
        rw [X₂.fderiv, show X₂.comp (fderiv ℝ φ (ψ x)) = ℓ.smulRight (fderiv ℝ φ (ψ x) v) from
          ContinuousLinearMap.ext fun w ↦ by
            rw [hX₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
              ContinuousLinearMap.comp_apply, hPl, ContinuousLinearMap.smulRight_apply]] at h4
        have e3 := h4.unique hK2
        have e4 : Varifold.tangentialDivergence X₂ x (T x) = ℓ v := by
          rw [hTD, X₂.fderiv, show
              (T x).projectionLinearMap ∘ₗ (X₂ : Euclidean N →ₗ[ℝ] Euclidean N) =
              ((ℓ.comp Pl : Euclidean N →L[ℝ] ℝ) : Euclidean N →ₗ[ℝ] ℝ).smulRight
                ((T x).projectionLinearMap (fderiv ℝ φ (ψ x) v)) from
            LinearMap.ext fun w ↦ by rw [hX₂]; exact map_smul (T x).projectionLinearMap _ _,
            LinearMap.trace_smulRight, (T x).projectionLinearMap_apply_of_mem
              (hplane ▸ LinearMap.mem_range_self _ v)]
          show ℓ (Pl (fderiv ℝ φ (ψ x) v)) = ℓ v
          rw [hPl]
        rw [one_div, inv_mul_eq_div, eq_div_iff (hJpos _ hu).ne', e1, ← e3, e4, mul_comm (ℓ v),
          sub_add_cancel]
      have h0 : ∫ z, Varifold.tangentialDivergence Xf z.1 z.2 ∂V.measure = 0 := hV X
      rw [hVT, integral_map hgm.aemeasurable
        (Varifold.continuous_tangentialDivergence hXc).aestronglyMeasurable,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball x₀ (ρ / 2)) (fun x hx ↦ by
          simp only [hTD, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hXs h)),
            ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, map_zero]),
        setIntegral_congr_ae measurableSet_ball (Eventually.mono (inter_mem hMU μ.support_mem_ae)
          fun x hx hxB ↦ hdiv x hxB hx.1.1 hx.2)] at h0
      rw [hϑ, integral_map (f := fun u ↦ (1 / NJ (fderiv ℝ φ u)) * fderiv ℝ ζ u v) hψm
        ((measurable_const.div hJm).mul ((hζ.continuous_fderiv
          one_ne_zero).clm_apply continuous_const).measurable).aestronglyMeasurable]
      exact h0
    obtain ⟨c, hc⟩ := @G4w ϑ ⟨hϑfin⟩ (fun u ↦ NJ (fderiv ℝ φ u)) a (R / 2) _ (half_pos hR) hm hJm
        hϑm hG4h
    -- the chart ball `ball a r` and the matching open set `O`
    have hR2 : 0 < R / 2 := half_pos hR
    have hR4 : 0 < R / 2 / 2 := half_pos hR2
    have hR8' : 0 < R / 2 / 2 / 2 := half_pos hR4
    have hR8 : 0 < R / 2 / 2 / 2 / 2 := half_pos hR8'
    have hrR : closedBall a (R / 2 / 2 / 2 / 2) ⊆ ball a R := closedBall_subset_ball
      ((half_lt_self hR8').trans ((half_lt_self hR4).trans ((half_lt_self hR2).trans
        (half_lt_self hR))))
    have hBD : ∀ w ∈ ball a (R / 2 / 2 / 2 / 2), w ∈ D ∧ φ w ∈ ball x₀ (ρ / 2) := fun w hw ↦
      ⟨(hRD (hrR (ball_subset_closedBall hw))).1,
        ball_subset_ball ((half_le_self (half_pos hρ2).le).trans (half_le_self hρ2.le))
          (hRD (hrR (ball_subset_closedBall hw))).2⟩
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Euclidean N),
        O = ball x₀ (ρ / 2) ∩ ψ ⁻¹' ball a (R / 2 / 2 / 2 / 2) := ⟨_, rfl⟩
    have hOB : O ⊆ ball x₀ (ρ / 2) := hOdef ▸ inter_subset_left
    have hOo : IsOpen O := hOdef ▸ hψB.isOpen_inter_preimage isOpen_ball isOpen_ball
    have hψO : ContinuousOn ψ O := hψB.mono hOB
    have hMO : φ '' ball a (R / 2 / 2 / 2 / 2) = M ∩ O := by
      rw [hOdef]; ext y; constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨hwD, hwB⟩ := hBD w hw
        exact ⟨hφM w hwD, hwB, by rw [mem_preimage, hψφ w hwD (hT₀B hwB)]; exact hw⟩
      · rintro ⟨hyM, hyB, hyr⟩
        exact ⟨ψ y, hyr, hψM y ⟨hyM, hT₀B hyB⟩⟩
    have hMOm : MeasurableSet (M ∩ O) := by
      have hgc : ContinuousOn (fun y ↦ φ (ψ y) - y) O :=
        ((hφc2.continuousOn.comp hψB fun y hy ↦ hψK y (ball_subset_closedBall hy)).sub
          continuousOn_id).mono hOB
      have e : M ∩ O = O \ (O ∩ (fun y ↦ φ (ψ y) - y) ⁻¹' {0}ᶜ) := by
        ext y; constructor
        · rintro ⟨hyM, hyO⟩
          exact ⟨hyO, fun h ↦ h.2 (sub_eq_zero.mpr (hψM y ⟨hyM, hT₀B (hOB hyO)⟩))⟩
        · rintro ⟨hyO, hy⟩
          refine ⟨?_, hyO⟩
          have e' : φ (ψ y) = y := by_contra fun h ↦ hy ⟨hyO, sub_ne_zero.mpr h⟩
          rw [← e']; exact hφM _ (hψD (hT₀B (hOB hyO)))
      rw [e]
      exact hOo.measurableSet.diff
          (hgc.isOpen_inter_preimage hOo isOpen_compl_singleton).measurableSet
    -- a Lipschitz bound for `φ` on the chart ball
    obtain ⟨C, hC⟩ := (isCompact_closedBall a (R / 2 / 2 / 2 / 2)).exists_bound_of_continuousOn
      (hDφ.continuousOn.mono fun w hw ↦ (hRD (hrR hw)).1)
    have hK : LipschitzOnWith (Real.toNNReal C) φ (ball a (R / 2 / 2 / 2 / 2)) :=
      (convex_ball a _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun w hw ↦
        ((hφc2.contDiffAt (hDo.mem_nhds (hBD w hw).1)).differentiableAt
            two_ne_zero).hasFDerivAt.hasFDerivWithinAt)
        fun w hw ↦ by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
          exact le_max_of_le_left (hC w (ball_subset_closedBall hw))
    have h5 := G5 φ ψ a (R / 2 / 2 / 2 / 2) _
        (fun u hu ↦ (hφc2.contDiffAt (hDo.mem_nhds (hBD u hu).1)).of_le
      one_le_two) (fun u hu ↦ hφ.injective_fderiv (hBD u hu).1)
      (fun u hu ↦ hψφ u (hBD u hu).1 (hT₀B (hBD u hu).2)) hK (hMO ▸ hMOm)
      (hMO ▸ hψO.mono inter_subset_right)
    rw [hMO] at h5
    -- the pushforwards to the chart agree
    have hpush : (μ.restrict O).map ψ =
        ENNReal.ofReal c • ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ O)).map ψ := by
      rw [h5, ← hc, hϑ, Measure.restrict_map_of_aemeasurable hψm measurableSet_ball,
        Measure.restrict_restrict' measurableSet_ball, hOdef, inter_comm]
    have hφB : AEMeasurable φ ((volume.restrict (ball a (R / 2 / 2 / 2 / 2))).withDensity
        fun u ↦ ENNReal.ofReal (NJ (fderiv ℝ φ u))) :=
      ((hφc2.continuousOn.mono fun w hw ↦ (hBD w hw).1).aemeasurable measurableSet_ball).mono_ac
        (withDensity_absolutelyContinuous _ _)
    have hpull : ∀ ϖ : Measure (Euclidean N), ϖ (M ∩ O)ᶜ = 0 → AEMeasurable ψ ϖ →
        AEMeasurable φ (ϖ.map ψ) → (ϖ.map ψ).map φ = ϖ := by
      intro ϖ h0 hψ' hφ'
      rw [AEMeasurable.map_map_of_aemeasurable hφ' hψ', Measure.map_congr (g := id) ?_,
        Measure.map_id]
      filter_upwards [mem_ae_iff.mpr h0] with y hy
      exact hψM y ⟨hy.1, hT₀B (hOB hy.2)⟩
    have e1 := hpull (μ.restrict O) (by
        rw [Measure.restrict_apply' hOo.measurableSet]
        refine measure_mono_null (fun y hy ↦ ?_) hμM
        exact fun h ↦ hy.1 ⟨h.1, hy.2⟩)
      (hψO.aemeasurable hOo.measurableSet) (by rw [hpush, h5]; exact hφB.smul_measure _)
    have e2 := hpull ((μHE[n] : Measure (Euclidean N)).restrict (M ∩ O)) (by
        rw [Measure.restrict_apply' hMOm, compl_inter_self, measure_empty])
      ((hψO.mono inter_subset_right).aemeasurable hMOm) (by rw [h5]; exact hφB)
    refine ⟨O, hOo, ?_, fun y hy ↦ (hK₀ (ball_subset_closedBall (hOB hy))).2,
      ENNReal.ofReal c, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
    · rw [hOdef]
      exact ⟨mem_ball_self hρ2, by rw [mem_preimage, hψa]; exact mem_ball_self hR8⟩
    · rw [← e1, hpush, Measure.map_smul _ (by rw [h5]; exact hφB), e2]
    · rw [← hMO]
      refine ne_top_of_le_ne_top ?_
          (Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hK)
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_ball_lt_top.ne
    · intro O' hO' hxO'
      obtain ⟨s', hs', hsB⟩ : ∃ s' > 0, ball a s' ⊆ ball a (R / 2 / 2 / 2 / 2) ∩ φ ⁻¹' O' :=
        Metric.mem_nhds_iff.mp (inter_mem (ball_mem_nhds a hR8)
          ((hφc2.continuousOn.continuousAt (hDo.mem_nhds ha)).preimage_mem_nhds
            (hO'.mem_nhds (by rw [hφa]; exact hxO'))))
      refine lt_of_lt_of_le ?_ (measure_mono (s := ψ ⁻¹' ball a s' ∩ (M ∩ O)) ?_)
      · rw [← Measure.restrict_apply' hMOm, ← Measure.map_apply_of_aemeasurable
          ((hψO.mono inter_subset_right).aemeasurable hMOm) measurableSet_ball, h5,
          withDensity_apply _ measurableSet_ball, setLIntegral_pos_iff hJm.ennreal_ofReal,
          Measure.restrict_apply' measurableSet_ball]
        refine lt_of_lt_of_le (measure_ball_pos volume a hs') (measure_mono fun u hu ↦ ?_)
        exact ⟨⟨(ENNReal.ofReal_pos.mpr (hJpos u (hBD u (hsB hu).1).1)).ne', hu⟩, (hsB hu).1⟩
      · rintro y ⟨hys, hyM, hyO⟩
        refine ⟨⟨hyM, ?_⟩, hyO⟩
        rw [← hψM y ⟨hyM, hT₀B (hOB hyO)⟩]
        exact (hsB hys).2
  -- gluing: one constant on `M ∩ U`
  have hglue : ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U) := by
    choose! O hO hxO hOU c hc hμO hfinO hposO using hLC
    have hcc : ∀ x ∈ M ∩ U, ∀ y ∈ M ∩ U, y ∈ O x → c y = c x := by
      intro x hx y hy hyx
      have h1 : μ (O x ∩ O y) = c y * μHE[n] (O x ∩ (M ∩ O y)) := by
        rw [← Measure.restrict_apply (hO x hx).measurableSet, hμO y hy, Measure.smul_apply,
          Measure.restrict_apply (hO x hx).measurableSet, smul_eq_mul]
      have h2 : μ (O y ∩ O x) = c x * μHE[n] (O y ∩ (M ∩ O x)) := by
        rw [← Measure.restrict_apply (hO y hy).measurableSet, hμO x hx, Measure.smul_apply,
          Measure.restrict_apply (hO y hy).measurableSet, smul_eq_mul]
      rw [inter_comm (O y) (O x), show O y ∩ (M ∩ O x) = O x ∩ (M ∩ O y) from
        Set.ext fun _ ↦ ⟨fun h ↦ ⟨h.2.2, h.2.1, h.1⟩, fun h ↦ ⟨h.2.2, h.2.1, h.1⟩⟩] at h2
      have hpos : μHE[n] (O x ∩ (M ∩ O y)) ≠ 0 := by
        refine ((hposO y hy (O x) (hO x hx) hyx).trans_le (measure_mono ?_)).ne'
        exact fun _ h ↦ ⟨h.1.2, h.1.1, h.2⟩
      exact (ENNReal.mul_left_inj hpos (ne_top_of_le_ne_top (hfinO y hy)
        (measure_mono inter_subset_right))).mp (h1.symm.trans h2)
    by_cases hne' : (M ∩ U).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne'
      have hall : ∀ y ∈ M ∩ U, c y = c x₀ := by
        have hsplit := isPreconnected_iff_subset_of_disjoint.mp hconn
          (⋃ x ∈ {x | x ∈ M ∩ U ∧ c x = c x₀}, O x) (⋃ x ∈ {x | x ∈ M ∩ U ∧ c x ≠ c x₀}, O x)
          (isOpen_biUnion fun x hx ↦ hO x hx.1) (isOpen_biUnion fun x hx ↦ hO x hx.1)
          (fun y hy ↦ by
            by_cases h : c y = c x₀
            · exact Or.inl (mem_biUnion (x := y) ⟨hy, h⟩ (hxO y hy))
            · exact Or.inr (mem_biUnion (x := y) ⟨hy, h⟩ (hxO y hy)))
          (by
            refine eq_empty_iff_forall_notMem.mpr fun y ⟨hy, h₁, h₂⟩ ↦ ?_
            obtain ⟨x, ⟨hx, hcx⟩, hyx⟩ := mem_iUnion₂.mp h₁
            obtain ⟨x', ⟨hx', hcx'⟩, hyx'⟩ := mem_iUnion₂.mp h₂
            exact hcx' ((hcc x' hx' y hy hyx').symm.trans ((hcc x hx y hy hyx).trans hcx)))
        intro y hy
        rcases hsplit with h | h
        · obtain ⟨x, ⟨hx, hcx⟩, hyx⟩ := mem_iUnion₂.mp (h hy)
          exact (hcc x hx y hy hyx).trans hcx
        · obtain ⟨x, ⟨hx, hcx⟩, hx₀x⟩ := mem_iUnion₂.mp (h hx₀)
          exact absurd (hcc x hx x₀ hx₀ hx₀x).symm hcx
      obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable
        (fun x : ↥(M ∩ U) ↦ O x) (fun x ↦ hO x x.2)
      have hcov : M ∩ U ⊆ ⋃ x ∈ S, O x := by
        intro y hy
        rw [hSU]
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxO y hy⟩
      have : Countable S := hSc.to_subtype
      have hres : μ.restrict (⋃ x : S, O x) =
          (c x₀ • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).restrict (⋃ x : S, O x) := by
        refine Measure.restrict_iUnion_congr.mpr fun x ↦ ?_
        rw [hμO x x.1.2, hall x x.1.2, Measure.restrict_smul,
          Measure.restrict_restrict (hO x x.1.2).measurableSet]
        congr 2
        ext y
        exact ⟨fun h ↦ ⟨h.2, h.1, hOU x x.1.2 h.2⟩, fun h ↦ ⟨h.2.1, h.1⟩⟩
      have hcov' : M ∩ U ⊆ ⋃ x : S, O x := fun y hy ↦ by
        obtain ⟨x, hxS, hyx⟩ := mem_iUnion₂.mp (hcov hy)
        exact mem_iUnion.mpr ⟨⟨x, hxS⟩, hyx⟩
      have hUo : MeasurableSet (⋃ x : S, O x) := (isOpen_iUnion fun x ↦ hO _ x.1.2).measurableSet
      have h1 : μ.restrict (⋃ x : S, O x) = μ :=
        Measure.restrict_eq_self_of_ae_mem (mem_of_superset (mem_ae_iff.mpr hμM) hcov')
      rw [h1, Measure.restrict_smul, Measure.restrict_restrict hUo, inter_eq_right.mpr hcov']
          at hres
      exact ⟨c x₀, hc x₀ hx₀, hres⟩
    · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
      rw [zero_smul]
      have h0 : M ∩ U = ∅ := not_nonempty_iff_eq_empty.mp hne'
      rw [h0, compl_empty] at hμM
      exact Measure.measure_univ_eq_zero.mp hμM
  -- assembly
  obtain ⟨c, hc, hμc⟩ := hglue
  refine ⟨c, T, hc, hTm, by rw [hVT, hμc], fun hc0 x hx ↦ ?_⟩
  have hxs : x ∈ μ.support := by
    rw [Measure.mem_support_iff_forall]
    intro O' hO'
    obtain ⟨O'', hO''O', hO''o, hxO''⟩ := _root_.mem_nhds_iff.mp hO'
    obtain ⟨O, -, -, hOU, -, -, -, -, hposO⟩ := hLC x hx
    refine lt_of_lt_of_le ?_ (measure_mono hO''O')
    rw [hμc, Measure.smul_apply, Measure.restrict_apply hO''o.measurableSet, smul_eq_mul]
    exact ENNReal.mul_pos hc0 ((hposO O'' hO''o hxO'').trans_le
      (measure_mono (s := M ∩ O'' ∩ O) (t := O'' ∩ (M ∩ U))
        fun y hy ↦ ⟨hy.1.2, hy.1.1, hOU hy.2⟩)).ne'
  obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx.1
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := hφ.image_eq ▸ ⟨hxW, hx.1⟩
  rw [Submission.simon_chart_classicalTangentSpace_eq_range N n M W D φ a hφ ha,
    hP1 (φ a, T (φ a)) (hTspt (φ a) ⟨hx.2, hxs⟩) hx.2 D W φ hφ a ha rfl]
  exact LinearMap.coe_range _

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
