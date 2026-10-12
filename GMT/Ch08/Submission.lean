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

/-- The monotonicity identity 3.4 at every centre of a stationary varifold `C` on `ℝ^N` (Simon
Ch. 8, as used in the proof of 5.5): applying 3.4 with `U = ℝ^N` and `ρ₀ = k + 1` gives `θ_k` with
`θ_k + ω_n^{-1} ∫_{Gₙ(B_ρ(y))} r^{-n-2}|p_{S^⊥}(x-y)|² dC = μ_C(B_ρ(y))/(ω_n ρ^n)` for
`0 < ρ < k + 1`.  Limits along `ρ ↓ 0` are unique, so `θ_k = θ_0` and the identity holds for every
`ρ > 0`; the defect integral is monotone in the ball, so the density ratio is non-decreasing. -/
theorem Submission.allard_tc_scf_monotonicity_identity :
    StationaryMonotonicityIdentity → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))), C.Stationary → ∀ y : Euclidean N, (∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ∀ ρ : ℝ, 0 < ρ → θ + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) = densityRatio n C.weight y ρ) ∧ MonotoneOn (densityRatio n C.weight y) (Ioi 0) := by
  intro hSMI N n C hC y
  -- Step 1: 3.4 with `U = ℝ^N` and `ρ₀ = k + 1`; global stationarity gives the local premise.
  have hlocal : ∀ k : ℕ, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < (k : ℝ) + 1 →
        θ + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) =
          densityRatio n C.weight y ρ := fun k ↦
    hSMI N n univ C y ((k : ℝ) + 1) (by positivity) (subset_univ _) (fun X _ ↦ hC X)
  choose θ hθ hid using hlocal
  -- Step 2: limits along `𝓝[>] 0` are unique, so `θ_k = θ_0`.
  have hθk : ∀ k, θ k = θ 0 := fun k ↦ tendsto_nhds_unique (hθ k) (hθ 0)
  -- Step 3: every `ρ > 0` lies below some `k + 1`.
  have hall : ∀ ρ : ℝ, 0 < ρ →
      θ 0 + (unitBallVolume n)⁻¹ * normalDefect C y (closedBall y ρ) =
        densityRatio n C.weight y ρ := by
    intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_gt ρ
    rw [← hθk k]
    exact hid k ρ hρ (by linarith)
  refine ⟨⟨θ 0, hθ 0, hall⟩, ?_⟩
  -- Step 4: `B_ρ(y) ⊆ B_ρ'(y)`, and a set lintegral is monotone in the set.
  intro ρ hρ ρ' hρ' hle
  rw [← hall ρ hρ, ← hall ρ' hρ']
  gcongr
  exact lintegral_mono_set (prod_mono (closedBall_subset_closedBall hle) subset_rfl)
/-- Density ratios are bounded by the ball-mass constant about `0` (Simon Ch. 8, the display before
5.5(2)): if `ρ ↦ μ(B_ρ(y))/(ω_n ρ^n)` is non-decreasing on `(0,∞)` for every `y` and
`μ(B_ρ(0)) = a ω_n ρ^n` for every `ρ > 0`, then for `ρ' ≥ ρ`, using `B_{ρ'}(y) ⊆ B_{ρ'+|y|}(0)`,
`μ(B_ρ(y))/(ω_n ρ^n) ≤ μ(B_{ρ'}(y))/(ω_n ρ'^n) ≤ a (1 + |y|/ρ')^n → a` as `ρ' → ∞`. -/
theorem Submission.allard_tc_scf_ratio_le :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (a : ℝ≥0∞), (∀ y : Euclidean N, MonotoneOn (densityRatio n μ y) (Ioi 0)) → (∀ ρ : ℝ, 0 < ρ → μ (closedBall 0 ρ) = a * unitBallVolume n * ENNReal.ofReal ρ ^ n) → ∀ (y : Euclidean N) (ρ : ℝ), 0 < ρ → densityRatio n μ y ρ ≤ a := by
  intro N n μ a hmono hball y ρ hρ
  -- Step 1: `ω_n ∈ (0, ∞)`.
  have hω₀ : unitBallVolume n ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hω : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Steps 2–4: for every `ρ' ≥ ρ`, `R(y, ρ) ≤ R(y, ρ') ≤ a (1 + |y|/ρ')^n`.
  have hbound : ∀ ρ' : ℝ, ρ ≤ ρ' →
      densityRatio n μ y ρ ≤ a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n) := by
    intro ρ' hρρ'
    have hρ' : 0 < ρ' := hρ.trans_le hρρ'
    have hsub : closedBall y ρ' ⊆ closedBall 0 (ρ' + ‖y‖) :=
      closedBall_subset_closedBall' (by rw [dist_zero_right])
    have hmass : μ (closedBall y ρ') ≤ a * unitBallVolume n * ENNReal.ofReal (ρ' + ‖y‖) ^ n :=
      (measure_mono hsub).trans_eq (hball _ (by positivity))
    calc densityRatio n μ y ρ ≤ densityRatio n μ y ρ' := hmono y hρ hρ' hρρ'
      _ ≤ a * unitBallVolume n * ENNReal.ofReal (ρ' + ‖y‖) ^ n /
            (unitBallVolume n * ENNReal.ofReal ρ' ^ n) := ENNReal.div_le_div_right hmass _
      _ = a * (ENNReal.ofReal (ρ' + ‖y‖) ^ n / ENNReal.ofReal ρ' ^ n) := by
        rw [mul_comm a, mul_assoc, ENNReal.mul_div_mul_left _ _ hω₀ hω, mul_div_assoc]
      _ = a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hρ'.le,
          ← ENNReal.ofReal_div_of_pos (pow_pos hρ' n), ← div_pow, add_div, div_self hρ'.ne']
  -- Step 6: `a (1 + |y|/ρ')^n → a` as `ρ' → ∞`.
  have hlim : Tendsto (fun ρ' : ℝ ↦ a * ENNReal.ofReal ((1 + ‖y‖ / ρ') ^ n)) atTop (𝓝 a) := by
    have h : Tendsto (fun ρ' : ℝ ↦ (1 + ‖y‖ / ρ') ^ n) atTop (𝓝 ((1 + 0) ^ n)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).pow n
    rw [add_zero, one_pow] at h
    have h' := ENNReal.Tendsto.const_mul (a := a) (ENNReal.tendsto_ofReal h)
      (Or.inl (by rw [ENNReal.ofReal_one]; exact one_ne_zero))
    rwa [ENNReal.ofReal_one, mul_one] at h'
  -- Steps 5 and 7: `R(y, ρ)` is eventually below a quantity tending to `a`.
  exact ge_of_tendsto hlim ((eventually_ge_atTop ρ).mono hbound)
/-- Density ratios at points of `spt μ` are bounded below by an a.e. lower bound of the density
(the step "(and hence for every `y ∈ spt μ_C` by 3.4)" after Simon Ch. 8, 5.5(7)): if `μ` is finite
on closed balls, `ρ ↦ R(x, ρ) = μ(B_ρ(x))/(ω_n ρ^n)` is non-decreasing on `(0, ∞)` for every `x`
and `Θ^n(μ, x) ≥ a` for `μ`-a.e. `x`, then `a ≤ R(y, ρ)` for `y ∈ spt μ` and `ρ > 0`.  Each open
ball of radius `1/(k+1)` about `y` contains a point `y_k` with
`a ≤ Θ^n(μ, y_k) ≤ R(y_k, ρ) ≤ μ(B_{ρ+1/(k+1)}(y))/(ω_n ρ^n)`, and continuity from above for the
decreasing closed balls `B_{ρ+1/(k+1)}(y)` lets `k → ∞`. -/
theorem Submission.allard_tc_scf_ratio_ge_on_support :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (a : ℝ≥0∞), (∀ (y : Euclidean N) (ρ : ℝ), μ (closedBall y ρ) ≠ ∞) → (∀ y : Euclidean N, MonotoneOn (densityRatio n μ y) (Ioi 0)) → (∀ᵐ y ∂μ, ∃ θ : ℝ≥0∞, HasDensity n μ y θ ∧ a ≤ θ) → ∀ y ∈ μ.support, ∀ ρ : ℝ, 0 < ρ → a ≤ densityRatio n μ y ρ := by
  intro N n μ a hfin hmono hae y hy ρ hρ
  -- Step 1: `c = ω_n ρ^n ∈ (0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ 0 :=
    mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ).ne')
  have hct : unitBallVolume n * ENNReal.ofReal ρ ^ n ≠ ∞ :=
    ENNReal.mul_ne_top hωt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- Step 2: the density at any point is at most its density ratio at radius `ρ`.
  have hdens : ∀ (x : Euclidean N) (θ : ℝ≥0∞), HasDensity n μ x θ →
      θ ≤ densityRatio n μ x ρ := by
    intro x θ hx
    refine le_of_tendsto hx ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with s hs
    exact hmono x hs.1 hρ hs.2.le
  -- Steps 3–5: a point `z ∈ B°_{1/(k+1)}(y)` of density `θ ≥ a` exists since `y ∈ spt μ`, and
  -- `a ≤ θ ≤ R(z, ρ) ≤ μ(B_{ρ+1/(k+1)}(y))/c`.
  have hk : ∀ k : ℕ, a * (unitBallVolume n * ENNReal.ofReal ρ ^ n) ≤
      μ (closedBall y (ρ + 1 / ((k : ℝ) + 1))) := by
    intro k
    have hr : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨z, hz, θ, hzθ, haθ⟩ : ∃ z ∈ ball y (1 / ((k : ℝ) + 1)), ∃ θ : ℝ≥0∞,
        HasDensity n μ z θ ∧ a ≤ θ := by
      by_contra hcon
      have h0 : μ (ball y (1 / ((k : ℝ) + 1))) = 0 :=
        measure_mono_null (fun z hz hzθ ↦ hcon ⟨z, hz, hzθ⟩) (ae_iff.1 hae)
      exact ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hr)).ne' h0
    rw [← ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc a ≤ θ := haθ
      _ ≤ densityRatio n μ z ρ := hdens z θ hzθ
      _ ≤ μ (closedBall y (ρ + 1 / ((k : ℝ) + 1))) /
          (unitBallVolume n * ENNReal.ofReal ρ ^ n) :=
        ENNReal.div_le_div_right (measure_mono (closedBall_subset_closedBall'
          (add_le_add le_rfl (mem_ball.1 hz).le))) _
  -- Step 6: continuity from above for the decreasing closed balls `B_{ρ+1/(k+1)}(y)`.
  have hinter : (⋂ k : ℕ, closedBall y (ρ + 1 / ((k : ℝ) + 1))) = closedBall y ρ := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    refine ⟨fun h ↦ ?_, fun h k ↦ h.trans (le_add_of_nonneg_right Nat.one_div_pos_of_nat.le)⟩
    by_contra hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hlt))
    linarith [h k]
  have htend : Tendsto (fun k : ℕ ↦ μ (closedBall y (ρ + 1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (μ (closedBall y ρ))) := by
    rw [← hinter]
    exact tendsto_measure_iInter_atTop (fun _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun i j hij ↦ closedBall_subset_closedBall
        (add_le_add le_rfl (Nat.one_div_le_one_div hij))) ⟨0, hfin _ _⟩
  -- Step 7: pass to the limit and divide by `c`.
  exact (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).2 (ge_of_tendsto' htend hk)
/-- Vanishing normal defect about `y` gives `x - y ∈ S` at every `(x, S) ∈ spt V` (Simon Ch. 8,
proof of 5.5, p. 217, display (8)): if `∫_{Gₙ(B_ρ(y))} |x - y|^{-n-2} |p_{S^⊥}(x - y)|² dV = 0` for
every `ρ > 0`, then `p_{S^⊥}(x - y) = 0` for `V`-a.e. `(x, S)`, hence, by continuity of
`p_{S^⊥}(x - y)` in `(x, S)`, at every point of `spt V`. -/
theorem Submission.allard_tc_scf_zero_defect_mem_plane :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (y : Euclidean N), (∀ ρ : ℝ, 0 < ρ → normalDefect V y (closedBall y ρ) = 0) → ∀ z ∈ V.measure.support, z.1 - y ∈ z.2.plane := by
  intro N n U V y h z hz
  -- Step 1: `(S, v) ↦ p_S(v)` is continuous (`S ↦ p_S` is the restriction to `G(N,n)` of a linear
  -- map on the finite-dimensional matrix space), so `w(x, S) = (x - y) - p_S(x - y)` is too.
  let Φ : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N) :=
    (LinearMap.toContinuousLinearMap :
        (Euclidean N →ₗ[ℝ] Euclidean N) ≃ₗ[ℝ] (Euclidean N →L[ℝ] Euclidean N)).toLinearMap.comp
      (LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis).symm.toLinearMap
  have hp : Continuous (fun p : Grassmannian N n × Euclidean N ↦ Grassmannian.project p.1 p.2) :=
    (Φ.continuous_of_finiteDimensional.comp (continuous_subtype_val.comp continuous_fst)).clm_apply
      continuous_snd
  have hg : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (z.2, z.1 - y)) :=
    continuous_snd.prodMk (continuous_fst.sub continuous_const)
  have hpg := hp.comp hg
  have hw : Continuous (fun z : Euclidean N × Grassmannian N n ↦
      (z.1 - y) - Grassmannian.project z.2 (z.1 - y)) :=
    (continuous_fst.sub continuous_const).sub hpg
  -- Step 2: the defect integrand is measurable.
  have hmeas : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      ENNReal.ofReal (‖(z.1 - y) - Grassmannian.project z.2 (z.1 - y)‖ ^ 2 /
        ‖z.1 - y‖ ^ (n + 2))) :=
    ENNReal.measurable_ofReal.comp ((hw.norm.pow 2).measurable.div
      ((continuous_fst.sub continuous_const).norm.pow (n + 2)).measurable)
  -- Steps 3–4: for each `k`, `w = 0` at `V`-a.e. point of `B_{k+1}(y) × G(N,n)`.
  have hball : ∀ k : ℕ, ∀ᵐ z ∂V.measure,
      z ∈ closedBall y ((k : ℝ) + 1) ×ˢ (univ : Set (Grassmannian N n)) →
        (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 := by
    intro k
    have h0 := (lintegral_eq_zero_iff hmeas).mp (h ((k : ℝ) + 1) (by positivity))
    filter_upwards [(ae_restrict_iff' (measurableSet_closedBall.prod MeasurableSet.univ)).mp h0]
      with z hzero hzk
    by_cases hzy : z.1 - y = 0
    · -- At `x = y`: `w = 0 - p_S(0) = 0`.
      rw [hzy, sub_eq_zero]
      exact (map_zero z.2.projectionLinearMap).symm
    · -- Off `x = y`: `|w|² / |x - y|^{n+2} ≤ 0` with a positive denominator, so `|w|² ≤ 0`.
      have hpos : 0 < ‖z.1 - y‖ ^ (n + 2) := pow_pos (norm_pos_iff.mpr hzy) _
      have hle := ENNReal.ofReal_eq_zero.mp (hzero hzk)
      rw [div_le_iff₀ hpos, zero_mul] at hle
      exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hle (sq_nonneg _)))
  -- Step 5: the balls `B_{k+1}(y)` exhaust `ℝ^N`, so `w = 0` `V`-a.e.
  have hae : ∀ᵐ z ∂V.measure, (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 := by
    filter_upwards [ae_all_iff.mpr hball] with z hzero
    obtain ⟨k, hk⟩ := exists_nat_ge ‖z.1 - y‖
    refine hzero k ⟨?_, mem_univ _⟩
    rw [mem_closedBall, dist_eq_norm]
    linarith
  -- Step 6: `{w = 0}` is closed and of full measure, so it contains `spt V`.
  have hz0 : (z.1 - y) - Grassmannian.project z.2 (z.1 - y) = 0 :=
    Measure.support_subset_of_isClosed (isClosed_eq hw continuous_const) hae hz
  -- Step 7: `p_S(x - y) = x - y`, so `x - y` lies in the range of `p_S`, which is `S.plane`.
  exact ⟨z.1 - y, (sub_eq_zero.mp hz0).symm⟩
/-- A linear subspace `P` of `ℝ^N` with `dim P = n` is an `n`-dimensional `C²` submanifold in
Simon's sense (Ch. 2, §4), so the Constancy Theorem 4.1 applies with `M = P` (step 7(b) of the proof
that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`, used for Simon Ch. 8, 5.5): a linear
isometry `J : ℝ^n → ℝ^N` with range `P` is a single global chart `(ℝ^n, ℝ^N, J)`. -/
theorem Submission.allard_tc_scf_subspace_submanifold :
    ∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)), Module.finrank ℝ P = n → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 (P : Set (Euclidean N)) := by
  intro N n P hP
  -- Step 1: a linear isometry `J : ℝ^n → ℝ^N` with range `P`, from an orthonormal basis of `P`
  -- indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ P := (stdOrthonormalBasis ℝ P).reindex (finCongr hP)
  let e : Euclidean n ≃ₗᵢ[ℝ] P := b.repr.symm
  let J : Euclidean n →L[ℝ] Euclidean N := P.subtypeL.comp (e : Euclidean n →L[ℝ] P)
  have hJ : Isometry J :=
    AddMonoidHomClass.isometry_of_norm J fun x ↦ (Submodule.norm_coe (e x)).trans (e.norm_map x)
  have hrange : range J = (P : Set (Euclidean N)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hw
      exact ⟨e.symm ⟨w, hw⟩, by simp [J]⟩
  -- Steps 2–3: `1 ≤ 2`, and the single global chart `(V', W, φ) = (ℝ^n, ℝ^N, J)` at every `y ∈ P`.
  refine ⟨by norm_num, fun y _ ↦ ⟨univ, univ, J, mem_univ y, isOpen_univ, isOpen_univ,
    J.contDiff.contDiffOn, hJ.injective.injOn, ?_, ?_, ?_⟩⟩
  · -- (d) `J(ℝ^n) = range J = P = ℝ^N ∩ P`.
    rw [image_univ, hrange, univ_inter]
  · -- (e) `J` is proper: an isometry is a closed embedding, so compact sets have compact preimages.
    intro K hK _
    rw [univ_inter]
    exact hJ.isClosedEmbedding.isCompact_preimage hK
  · -- (f) `DJ(x) = J` is injective.
    intro x _
    rw [J.fderiv]
    exact hJ.injective
/-- **Simon Ch. 8, proof of 5.5, p. 215, the plane's classical tangent space** (child
`subspace_tangent` of `stationary_cone_flat`, step 7): for a linear subspace `P` of `ℝ^N` and
`y ∈ P`, the classical tangent space `T_y P` (Ch. 2, §4) is `P` itself. A velocity `γ'(0)` is the
limit of the difference quotients `t⁻¹(γ(t) - y) ∈ P` and `P` is closed (finite-dimensional);
conversely `ξ ∈ P` is the velocity of the line `s ↦ y + sξ`, which stays in `P`. -/
theorem Submission.allard_tc_scf_subspace_classical_tangent :
    ∀ (N : ℕ) (P : Submodule ℝ (Euclidean N)) (y : Euclidean N), y ∈ P →
      classicalTangentSpace (P : Set (Euclidean N)) y = (P : Set (Euclidean N)) := by
  intro N P y hy
  ext ξ
  constructor
  · rintro ⟨γ, -, hγP, hγ0, hγ⟩
    -- `t⁻¹ • (γ t - γ 0) → ξ` as `t → 0`, `t ≠ 0`; for `t ∈ (-1,1)` these quotients lie in `P`,
    -- and `P` is closed.
    refine P.closed_of_finiteDimensional.mem_of_tendsto hγ.tendsto_slope_zero ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)]
      with t ht
    rw [zero_add, hγ0]
    exact P.smul_mem _ (P.sub_mem (hγP ht) hy)
  · intro hξ
    -- The line `s ↦ y + s • ξ` lies in `P` and has velocity `ξ`.
    refine ⟨fun s ↦ y + s • ξ, ?_, fun s _ ↦ P.add_mem hy (P.smul_mem s hξ), by simp, ?_⟩
    · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add y
/-- **Simon Ch. 8, 4.1 for a plane** (child `constancy_plane` of `stationary_cone_flat`; the step
"`C = θ₀ v(T)` by Constancy 4.1" in the proof of 5.5): a stationary `n`-varifold `C` on `ℝ^N` with
`spt μ_C ⊆ T` is `θ v(T)` for a constant `θ ≥ 0`.  `ConstancyTheorem` applies with `U = ℝ^N` and
`M = T`: `T` is a `C²` submanifold (`allard_tc_scf_subspace_submanifold`) and `T ∩ ℝ^N = T` is
convex, hence connected.  Since `T_x T = T` (`allard_tc_scf_subspace_classical_tangent`) and a point
of `G(N,n)` is determined by its plane, the constancy set of `A` is `{x ∈ T : (x, T) ∈ A}`, whose
`H^n`-measure is `v(T)(A)`. -/
theorem Submission.allard_tc_scf_constancy_plane :
    ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N)))
      (T : Grassmannian N n), C.Stationary → C.weight.support ⊆ (T.plane : Set (Euclidean N)) →
      ∃ θ : ℝ, 0 ≤ θ ∧ C.measure = ENNReal.ofReal θ • planeVarifoldMeasure T := by
  intro hconst N n C T hC hspt
  obtain ⟨θ, hθ, hA⟩ := hconst N n univ C (T.plane : Set (Euclidean N)) hC
    (Submission.allard_tc_scf_subspace_submanifold N n T.plane T.finrank_plane)
    (fun x hx ↦ hspt hx.2)
    (by rw [inter_univ]; exact T.plane.convex.isPreconnected)
  refine ⟨θ, hθ, Measure.ext fun A hA' ↦ ?_⟩
  have hmeas : Measurable fun y : Euclidean N ↦ (y, T) := measurable_prodMk_right
  rw [hA A hA', Measure.smul_apply, smul_eq_mul, planeVarifoldMeasure,
    Measure.map_apply hmeas hA', Measure.restrict_apply (hmeas hA')]
  -- The constancy set of `A` is `{x ∈ T : (x, T) ∈ A}`.
  congr 2
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_univ, and_true, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, S, hS, hxS⟩
    rw [Submission.allard_tc_scf_subspace_classical_tangent N T.plane x hx] at hS
    -- A point of `G(N,n)` is determined by its plane: `S = ofSubmodule S.plane = T`.
    have hST : S = T := by
      rw [← S.ofSubmodule_plane, ← T.ofSubmodule_plane]
      congr 1
      exact SetLike.coe_injective hS
    rw [hST] at hxS
    exact ⟨hxS, hx⟩
  · rintro ⟨hxT, hx⟩
    exact ⟨hx, T, (Submission.allard_tc_scf_subspace_classical_tangent N T.plane x hx).symm, hxT⟩
/-- The plane varifold `v(T)` of an `n`-plane `T ∈ G(N,n)` has mass `ω_n r^n` over the cylinder
`B_r(0) × G(N,n)` (step 8 of the proof that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`,
used for Simon Ch. 8, 5.5): `v(T)(B_r(0) × G(N,n)) = H^n(B_r(0) ∩ T)`, and `H^n` is transported to
Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`. -/
theorem Submission.allard_tc_scf_plane_ball_mass :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 < r → planeVarifoldMeasure T (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n))) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: `v(T)(B_r(0) × G(N,n)) = H^n(B_r(0) ∩ T)`, by `map_apply` and `restrict_apply`.
  rw [planeVarifoldMeasure, Measure.map_apply measurable_prodMk_right
      (measurableSet_closedBall.prod MeasurableSet.univ), mk_preimage_prod_left (mem_univ T),
    Measure.restrict_apply measurableSet_closedBall]
  -- Step 2: a linear isometry `J : ℝ^n → ℝ^N` with range `T`, from an orthonormal basis of `T`
  -- indexed by `Fin n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  have hrange : range J = (T.plane : Set (Euclidean N)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact (b.repr.symm x).2
    · intro hw
      exact ⟨b.repr ⟨w, hw⟩, by simp [J]⟩
  -- Step 3: `H^n(B_r(0) ∩ T) = H^n(J⁻¹(B_r(0)))` and `J⁻¹(B_r(0)) = B_r(0) ⊆ ℝ^n`.
  have hpre : J ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext x
    simp
  rw [← hrange, ← J.isometry.euclideanHausdorffMeasure_preimage, hpre]
  -- Steps 4–6: `H^n` is Lebesgue measure on `ℝ^n` and `vol(B_r(0)) = ω_n r^n`.
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hr.le,
    finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le, unitBallVolume, mul_comm]
/-- **Simon Ch. 8, proof of 5.5, pp. 216–217: a stationary cone with density `≥ θ₀` a.e. is
`θ₀ v(T)`.** Let `C` be a stationary `n`-varifold on `ℝ^N` with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every
`ρ > 0` (printed (1)) and `Θ^n(μ_C, y) ≥ θ₀` for `μ_C`-a.e. `y` (printed (7)). By 3.4 at every
centre, `R(y, ρ) = μ_C(B_ρ(y))/(ω_n ρ^n) ≤ θ₀` for all `y` (printed (2)) and `R(y, ρ) ≥ θ₀` for
`y ∈ spt μ_C`, so `Θ^n(μ_C, y) = θ₀` and the normal defect about `y` vanishes; hence `x - y ∈ S` for
`y ∈ spt μ_C` and `(x, S) ∈ spt C` (printed (8)). As `0 ∈ spt μ_C = π(spt C)`, some `(0, T)` lies in
`spt C`, so `spt μ_C ⊆ T`; Constancy 4.1 gives `C = θ v(T)`, and the mass of `B_1(0)` gives
`θ = θ₀`. -/
theorem Submission.allard_tc_stationary_cone_flat :
    StationaryMonotonicityIdentity → ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (θ₀ : ℝ), 0 < θ₀ → C.Stationary → (∀ ρ : ℝ, 0 < ρ → C.weight (closedBall 0 ρ) = ENNReal.ofReal θ₀ * unitBallVolume n * ENNReal.ofReal ρ ^ n) → (∀ᵐ y ∂C.weight, ∃ θ : ℝ≥0∞, HasDensity n C.weight y θ ∧ ENNReal.ofReal θ₀ ≤ θ) → ∃ T : Grassmannian N n, C.measure = ENNReal.ofReal θ₀ • planeVarifoldMeasure T := by
  intro hSMI hconst N n C θ₀ hθ₀ hC hball hae
  -- Step 0: `θ₀` and `ω_n` lie in `(0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have ha0 : ENNReal.ofReal θ₀ ≠ 0 := (ENNReal.ofReal_pos.2 hθ₀).ne'
  -- Step 1: the monotonicity identity 3.4 at every centre; density ratios are non-decreasing.
  have hMI := Submission.allard_tc_scf_monotonicity_identity hSMI N n C hC
  have hmono : ∀ y, MonotoneOn (densityRatio n C.weight y) (Ioi 0) := fun y ↦ (hMI y).2
  -- Step 2: `R(y, ρ) ≤ θ₀` everywhere (printed (2)) and `θ₀ ≤ R(y, ρ)` on `spt μ_C` (by (7)).
  have hle := Submission.allard_tc_scf_ratio_le N n C.weight (ENNReal.ofReal θ₀) hmono hball
  have hge := Submission.allard_tc_scf_ratio_ge_on_support N n C.weight (ENNReal.ofReal θ₀)
    (fun y ρ ↦ C.weight_finite_on_compact _ (isCompact_closedBall y ρ) (subset_univ _)) hmono hae
  -- Step 3: at `y ∈ spt μ_C`, `R(y, ·) ≡ θ₀`, so `Θ^n(μ_C, y) = θ₀` and 3.4 reads
  -- `θ₀ + ω_n⁻¹ D_y(ρ) = θ₀`; as `θ₀ < ∞` and `ω_n⁻¹ ≠ 0`, the normal defect `D_y(ρ)` vanishes.
  have hdefect : ∀ y ∈ C.weight.support, ∀ ρ : ℝ, 0 < ρ →
      normalDefect C y (closedBall y ρ) = 0 := by
    intro y hy ρ hρ
    obtain ⟨θ, hθ, hid⟩ := (hMI y).1
    have hR : ∀ r : ℝ, 0 < r → densityRatio n C.weight y r = ENNReal.ofReal θ₀ := fun r hr ↦
      le_antisymm (hle y r hr) (hge y hy r hr)
    have hθa : θ = ENNReal.ofReal θ₀ := by
      refine tendsto_nhds_unique hθ (tendsto_const_nhds.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hR r hr).symm
    have h := hid ρ hρ
    rw [hθa, hR ρ hρ, ← add_zero (ENNReal.ofReal θ₀), add_assoc, zero_add,
      ENNReal.add_right_inj ENNReal.ofReal_ne_top] at h
    exact (mul_eq_zero.1 h).resolve_left (ENNReal.inv_ne_zero.2 hωt)
  -- Step 4: printed (8), `x - y ∈ S` for `y ∈ spt μ_C` and `(x, S) ∈ spt C`.
  have h8 : ∀ y ∈ C.weight.support, ∀ z ∈ C.measure.support, z.1 - y ∈ z.2.plane :=
    fun y hy ↦ Submission.allard_tc_scf_zero_defect_mem_plane N n univ C y (hdefect y hy)
  -- Step 5: `0 ∈ spt μ_C`, since every ball about `0` has mass `θ₀ ω_n ρ^n > 0`.
  have h0 : (0 : Euclidean N) ∈ C.weight.support := by
    rw [Measure.mem_support_iff_forall]
    intro s hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
    refine lt_of_lt_of_le ?_ (measure_mono ((closedBall_subset_ball (half_lt_self hε)).trans hεs))
    rw [hball _ (half_pos hε)]
    exact pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero ha0 hω0)
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 (half_pos hε)).ne'))
  -- Step 6: `spt μ_C ⊆ π(spt C)`, as `π(spt C)` is closed (`G(N,n)` is compact) and `μ_C`-conull;
  -- so some `(0, T)` lies in `spt C`.
  obtain ⟨T, hT⟩ : ∃ T : Grassmannian N n, ((0 : Euclidean N), T) ∈ C.measure.support := by
    have hc : IsClosed (Prod.fst '' C.measure.support) :=
      isClosedMap_fst_of_compactSpace _ C.measure.isClosed_support
    have hsub : C.weight.support ⊆ Prod.fst '' C.measure.support := by
      refine Measure.support_subset_of_isClosed hc ?_
      change ∀ᵐ x ∂C.measure.map Prod.fst, x ∈ Prod.fst '' C.measure.support
      refine (ae_map_iff measurable_fst.aemeasurable hc.measurableSet).2 ?_
      filter_upwards [C.measure.support_mem_ae] with z hz
      exact mem_image_of_mem Prod.fst hz
    obtain ⟨⟨x, S⟩, hS, hx⟩ := hsub h0
    obtain rfl : x = 0 := hx
    exact ⟨S, hS⟩
  -- Step 7: `spt μ_C ⊆ T`, since (8) at `(x, S) = (0, T)` gives `-y ∈ T`.
  have hspt : C.weight.support ⊆ (T.plane : Set (Euclidean N)) := by
    intro y hy
    have h : (0 : Euclidean N) - y ∈ T.plane := h8 y hy ((0 : Euclidean N), T) hT
    rw [zero_sub] at h
    simpa using T.plane.neg_mem h
  -- Step 8: Constancy 4.1 gives `C = θ v(T)` with `θ ≥ 0`.
  obtain ⟨θ, -, hCθ⟩ := Submission.allard_tc_scf_constancy_plane hconst N n C T hC hspt
  -- Step 9: `μ_C(B_1(0)) = θ ω_n = θ₀ ω_n` and `ω_n ∈ (0, ∞)`, so `θ = θ₀`.
  have h1 := hball 1 one_pos
  rw [C.weight_apply measurableSet_closedBall, hCθ, Measure.smul_apply, smul_eq_mul,
    Submission.allard_tc_scf_plane_ball_mass N n T 1 one_pos, ENNReal.ofReal_one, one_pow,
    mul_one, mul_one, ENNReal.mul_left_inj hω0 hωt] at h1
  exact ⟨T, by rw [hCθ, h1]⟩
/-- Lebesgue density theorem for a measure `μ` on `ℝ^N` that vanishes off an open set `U` and is
finite on compact subsets of `U` (Simon Ch. 8, Remark 5.6(iii), localized as in Simon Ch. 1, 3.23):
for measurable `A` and `μ`-a.e. `x`, `μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 1_A(x)` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_dbd_lebesgue_density :
    ∀ (N : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → ∀ A : Set (Euclidean N), MeasurableSet A → ∀ᵐ x ∂μ, Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (A.indicator 1 x)) := by
  intro N U μ hU hUc hK A hA
  -- Step 1: the countable family of compact balls `K_i = B_r(q) ⊆ U`, `i = (q, r) ∈ I`, with `q`
  -- in a countable dense set `D` and `r ∈ ℚ_{>0}`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euclidean N)
  let I : Set (Euclidean N × ℚ) := {i | i.1 ∈ D ∧ 0 < i.2 ∧ closedBall i.1 (i.2 : ℝ) ⊆ U}
  have hIc : I.Countable :=
    (hDc.prod (countable_univ (α := ℚ))).mono fun i hi ↦ mem_prod.2 ⟨hi.1, mem_univ _⟩
  -- Steps 3–4: Besicovitch differentiation for each finite measure `μ ⌞ K_i`, off one `μ`-null set.
  have hball : ∀ᵐ x ∂μ, ∀ i ∈ I, x ∈ closedBall i.1 (i.2 : ℝ) →
      Tendsto (fun ρ : ℝ ↦ μ.restrict (closedBall i.1 (i.2 : ℝ)) (A ∩ closedBall x ρ) /
          μ.restrict (closedBall i.1 (i.2 : ℝ)) (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (A.indicator 1 x)) := by
    refine (ae_ball_iff hIc).2 fun i hi ↦ ?_
    have : IsFiniteMeasure (μ.restrict (closedBall i.1 (i.2 : ℝ))) :=
      isFiniteMeasure_restrict.2 (hK _ (isCompact_closedBall _ _) hi.2.2)
    exact (ae_restrict_iff' measurableSet_closedBall).1
      (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _ hA)
  filter_upwards [hball, mem_ae_iff.2 hUc] with x hx hxU
  -- Steps 2 and 5: some `i = (q, r) ∈ I` with `dist x q < r`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (half_pos hε)
  obtain ⟨q, hqD, hqx⟩ := hDd.exists_mem_open isOpen_ball ⟨x, mem_ball_self hr0⟩
  have hxq : dist x q < r := by rw [dist_comm]; exact mem_ball.1 hqx
  have hi : (q, r) ∈ I := by
    have h1 : (r : ℝ) + dist q x < ε := by linarith [mem_ball.1 hqx]
    exact ⟨hqD, Rat.cast_pos.1 hr0, (closedBall_subset_ball' h1).trans hεU⟩
  -- Step 6: for `0 < ρ < r - dist x q`, `B_ρ(x) ⊆ K_i`, so the two ratios agree near `0`.
  refine (hx (q, r) hi (mem_closedBall.2 hxq.le)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hxq)] with ρ hρ
  have hsub : closedBall x ρ ⊆ closedBall q r := closedBall_subset_closedBall' (by linarith [hρ.2])
  rw [Measure.restrict_apply' measurableSet_closedBall,
    Measure.restrict_apply' measurableSet_closedBall, inter_assoc, inter_eq_left.2 hsub]
/-- Relative density zero at a point of finite density gives `o(ρ^n)` mass (closing steps 8–9 of
the density blow-up decay for Simon Ch. 8, 5.6(iii)): if `Θ^n(μ, x) = θ < ∞`,
`μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 0` as `ρ ↓ 0` and `μ`-a.e. point of `E` lies in `A`, then
`μ(B_ρ(x) ∩ E) / ρ^n → 0` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_dbd_relative_decay :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞) (A E : Set (Euclidean N)), HasDensity n μ x θ → θ ≠ ∞ → Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → (∀ᵐ y ∂μ, y ∈ E → y ∈ A) → Tendsto (fun ρ : ℝ ↦ μ (closedBall x ρ ∩ E) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro N n μ x θ A E hθ hθ_ne hκ hAE
  -- Step 1: `0 < ω_n < ∞`.
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- Step 2: `μ(B_ρ) / ρ^n = ω_n · densityRatio ρ → ω_n θ ≠ ∞`.
  have hf_eq : ∀ ρ : ℝ, μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n =
      unitBallVolume n * densityRatio n μ x ρ := fun ρ ↦ by
    rw [densityRatio, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hω0 hωtop]
  have hf : Tendsto (fun ρ : ℝ ↦ μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0)
      (𝓝 (unitBallVolume n * θ)) := by
    simp_rw [hf_eq]
    exact ENNReal.Tendsto.const_mul hθ (Or.inr hωtop)
  have hωθ : unitBallVolume n * θ ≠ ∞ := ENNReal.mul_ne_top hωtop hθ_ne
  -- Step 3: `κ(ρ) · μ(B_ρ) / ρ^n → 0 · ω_n θ = 0`.
  have hprod : Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) *
      (μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul hκ (Or.inr hωθ) hf (Or.inr ENNReal.zero_ne_top)
  -- Step 4: eventually `μ(B_ρ) / ρ^n < ∞`.
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall x ρ) / ENNReal.ofReal ρ ^ n < ∞ :=
    hf.eventually (gt_mem_nhds hωθ.lt_top)
  -- Step 6: squeeze `0 ≤ μ(B_ρ ∩ E) / ρ^n ≤ κ(ρ) · μ(B_ρ) / ρ^n`, the upper bound holding for
  -- every `ρ` of step 4.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hev] with ρ hρ
  -- Step 4, continued: `ρ^n ≠ ∞`, hence `μ(B_ρ) ≠ ∞`.
  have hP : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hB : μ (closedBall x ρ) ≠ ∞ := fun h ↦ by
    rw [h, ENNReal.top_div_of_ne_top hP] at hρ
    exact lt_irrefl _ hρ
  -- Step 5(a): `μ(B_ρ ∩ E) ≤ μ(A ∩ B_ρ)`, since `B_ρ ∩ E ⊆ A ∩ B_ρ` up to a `μ`-null set.
  have ha : μ (closedBall x ρ ∩ E) ≤ μ (A ∩ closedBall x ρ) :=
    measure_mono_ae (hAE.mono fun y hy hyBE ↦ ⟨hy hyBE.2, hyBE.1⟩)
  -- Step 5(b): `μ(A ∩ B_ρ) ≤ κ(ρ) · μ(B_ρ)`, the case `μ(B_ρ) = 0` separately.
  have hb : μ (A ∩ closedBall x ρ) ≤
      μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) * μ (closedBall x ρ) := by
    by_cases h0 : μ (closedBall x ρ) = 0
    · rw [h0, mul_zero]
      exact (measure_mono inter_subset_right).trans h0.le
    · exact (ENNReal.div_mul_cancel h0 hB).ge
  -- Step 5(c): divide by `ρ^n`.
  calc μ (closedBall x ρ ∩ E) / ENNReal.ofReal ρ ^ n
      ≤ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ) * μ (closedBall x ρ) /
          ENNReal.ofReal ρ ^ n := ENNReal.div_le_div_right (ha.trans hb) _
    _ = _ := mul_div_assoc _ _ _

/-- Density blow-up decay (Simon Ch. 8, Remark 5.6(iii) and (3)–(4) in the proof of 5.5): assuming
3.6, if `V` has locally bounded first variation, then for `μ_V`-a.e. `x`, whenever
`Θ^n(μ_V, x) = θ₀` and `τ < θ₀`, `ρ^{-n} μ_V({y ∈ B_ρ(x) : not (Θ^n(μ_V, y) exists and is ≥ τ)})`
tends to `0` as `ρ ↓ 0`. -/
theorem Submission.allard_tc_density_blowup_decay :
    DensityExistsAE → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → ∀ᵐ x ∂V.weight, ∀ θ₀ τ : ℝ, HasDensity n V.weight x (ENNReal.ofReal θ₀) → τ < θ₀ → Tendsto (fun ρ : ℝ ↦ V.weight {y | y ∈ closedBall x ρ ∧ ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ} / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro hD N n U V hV
  -- Step 1: a Borel `Θ̃`, finite and equal to the density off a `μ_V`-null set.
  obtain ⟨Θ, hΘm, hΘ⟩ := hD N n U V hV
  -- Step 2: `μ_V(Uᶜ) = 0`.
  have hUc : V.weight Uᶜ = 0 := by
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  -- Steps 3–4: off one `μ_V`-null set, `x` is a Lebesgue density point of every
  -- `A_p = {Θ̃ < p}`, `p ∈ ℚ`.
  have hLeb : ∀ᵐ x ∂V.weight, ∀ p : ℚ,
      Tendsto (fun ρ : ℝ ↦ V.weight ({y | Θ y < ENNReal.ofReal p} ∩ closedBall x ρ) /
          V.weight (closedBall x ρ))
        (𝓝[>] 0) (𝓝 ({y | Θ y < ENNReal.ofReal p}.indicator 1 x)) :=
    ae_all_iff.2 fun p ↦ Submission.allard_tc_dbd_lebesgue_density N U V.weight V.isOpen_domain
      hUc V.weight_finite_on_compact _ (measurableSet_lt hΘm measurable_const)
  filter_upwards [hΘ, hLeb] with x hx hxL
  intro θ₀ τ hθ₀ hτ
  -- Step 5: `Θ̃(x) = θ₀`, so a rational `p ∈ (τ, θ₀)` has `x ∉ A_p`.
  have heq : Θ x = ENNReal.ofReal θ₀ := tendsto_nhds_unique hx.2 hθ₀
  obtain ⟨p, hτp, hpθ⟩ := exists_rat_btwn hτ
  have hxA : x ∉ {y | Θ y < ENNReal.ofReal p} := by
    rw [Set.mem_ofPred_eq, not_lt, heq]
    exact ENNReal.ofReal_le_ofReal hpθ.le
  -- Step 7: `μ_V(A_p ∩ B_ρ(x)) / μ_V(B_ρ(x)) → 0`.
  have hκ := hxL p
  rw [Set.indicator_of_notMem hxA] at hκ
  -- Steps 8–9: the relative decay, applied with `A = A_p` and `E = E_τ`.
  refine Submission.allard_tc_dbd_relative_decay N n V.weight x (ENNReal.ofReal θ₀)
    {y | Θ y < ENNReal.ofReal p}
    {y | ¬ ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ ENNReal.ofReal τ ≤ θ}
    hθ₀ ENNReal.ofReal_ne_top hκ ?_
  -- Step 6: `E_τ ⊆ Z ∪ A_p`.
  filter_upwards [hΘ] with y hy hyE
  by_contra hyA
  exact hyE ⟨Θ y, hy.2, (ENNReal.ofReal_le_ofReal hτp.le).trans (not_lt.1 hyA)⟩

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
