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

/-- Densities transfer under ball-mass scaling (steps 6 and 9 of the blow-up density lower bound
used in Simon Ch. 8, 5.5 and 5.7): if `t > 0`, `c ≠ ∞` and `ν(B_ρ(y)) = c t^{-n} μ(B_{tρ}(z))` for
`0 < ρ < δ`, then `Θ^n(μ, z) = θ` implies `Θ^n(ν, y) = c θ`. -/
theorem Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling :
    ∀ (N n : ℕ) (μ ν : Measure (Euclidean N)) (y z : Euclidean N) (t δ : ℝ) (c θ : ℝ≥0∞), 0 < t → 0 < δ → c ≠ ∞ → (∀ ρ : ℝ, 0 < ρ → ρ < δ → ν (closedBall y ρ) = c * (ENNReal.ofReal (t⁻¹ ^ n) * μ (closedBall z (t * ρ)))) → HasDensity n μ z θ → HasDensity n ν y (c * θ) := by
  intro N n μ ν y z t δ c θ ht hδ hc hscale hμ
  -- Step 1: `ω_n = unitBallVolume n` lies in `(0, ∞)`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_ne_top
  -- Step 2: `ρ ↦ t ρ` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have hs : Tendsto (fun ρ : ℝ ↦ t * ρ) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul t).tendsto' 0 0 (mul_zero t)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun ρ hρ ↦ mul_pos ht hρ⟩
  -- Step 3: `c · densityRatio n μ z (t ρ) → c θ` as `ρ ↓ 0`, since `c ≠ ∞`.
  have hlim : Tendsto (fun ρ ↦ c * densityRatio n μ z (t * ρ)) (𝓝[>] 0) (𝓝 (c * θ)) :=
    ENNReal.Tendsto.const_mul (Tendsto.comp hμ hs) (Or.inr hc)
  -- Step 5: it suffices that the two quotients agree on `(0, δ) ∈ 𝓝[>] 0`.
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  -- Step 4: with `T = ofReal t ^ n ∈ (0, ∞)`, `ofReal (t⁻¹ ^ n) = T⁻¹` and
  -- `ofReal (t ρ) ^ n = T · ofReal ρ ^ n`; then distribute the inverses.
  have hT0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero n (ENNReal.ofReal_pos.2 ht).ne'
  have hTtop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [densityRatio, densityRatio, hscale ρ hρ.1 hρ.2, ENNReal.ofReal_mul ht.le, mul_pow,
    ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop),
    ENNReal.mul_inv (Or.inl hT0) (Or.inl hTtop), ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop)]
  ring
/-- **Masses of the rescaled varifold on cylinders and closed balls** (child `rescaled_mass_formula`
of `varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): for every real `t` and Borel
`A ⊆ ℝ^N`, `V_{x,t}(A × G(N,n)) = t^{-n} μ_V({z : t⁻¹(z - x) ∈ A})`, because the preimage of
`A × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is `{z : t⁻¹(z - x) ∈ A} × G(N,n)`; and for `t > 0`,
`V_{x,t}(B_ρ(y) × G(N,n)) = t^{-n} μ_V(B_{tρ}(x + ty))`, because
`t⁻¹(w - x) - y = t⁻¹(w - (x + ty))` gives `{w : t⁻¹(w - x) ∈ B_ρ(y)} = B_{tρ}(x + ty)`. -/
theorem Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t : ℝ), (∀ A : Set (Euclidean N), MeasurableSet A → rescaledMeasure V x t (A ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | t⁻¹ • (z - x) ∈ A}) ∧ (0 < t → ∀ (y : Euclidean N) (ρ : ℝ), rescaledMeasure V x t (closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall (x + t • y) (t * ρ))) := by
  intro N n U V x t
  -- Step 1: the dilation `z ↦ t⁻¹ • (z - x)` and `φ (z, S) = (t⁻¹ • (z - x), S)` are measurable.
  have hη : Measurable fun z : Euclidean N ↦ t⁻¹ • (z - x) := by fun_prop
  have hφ : Measurable fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2) := by
    fun_prop
  -- Step 2 (part (i)): `φ⁻¹(A × G) = {z | t⁻¹ • (z - x) ∈ A} × G`, a measurable cylinder.
  have hcyl : ∀ A : Set (Euclidean N), MeasurableSet A →
      rescaledMeasure V x t (A ×ˢ (univ : Set (Grassmannian N n))) =
        ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | t⁻¹ • (z - x) ∈ A} := by
    intro A hA
    have hA' : MeasurableSet {z : Euclidean N | t⁻¹ • (z - x) ∈ A} := hη hA
    rw [rescaledMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hφ (hA.prod MeasurableSet.univ), V.weight_apply hA']
    rfl
  refine ⟨hcyl, fun ht y ρ ↦ ?_⟩
  -- Step 3 (part (ii)): for `t > 0`, `{w | t⁻¹ • (w - x) ∈ B_ρ(y)} = B_{tρ}(x + t • y)`, since
  -- `t⁻¹ • (w - x) - y = t⁻¹ • (w - (x + t • y))` and `t⁻¹ * d ≤ ρ ↔ d ≤ t * ρ`.
  have hball : {z : Euclidean N | t⁻¹ • (z - x) ∈ closedBall y ρ} =
      closedBall (x + t • y) (t * ρ) := by
    ext w
    have hw : t⁻¹ • (w - x) - y = t⁻¹ • (w - (x + t • y)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rw [mem_ofPred_eq, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, hw, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht]
  rw [hcyl _ measurableSet_closedBall, hball]
/-- **Simon Ch. 8, proofs of 5.5 and 5.7, restricted varifolds** (child `restricted_varifold` of the
density lower bound for varifold tangents): the construction of `W_j = τ⁻¹ V_{x,λ_j} ⌞ Gₙ(Ω)` and
`C_Ω = τ⁻¹ C ⌞ Gₙ(Ω)`, for a general measure `μ`.  If `Ω` is open, `c < ∞` and `μ(K × G(N,n)) < ∞`
for every compact `K ⊆ Ω`, then `c • μ ⌞ (Ω × G(N,n))` vanishes on `Ωᶜ × G(N,n)` (disjoint from
`Ω × G(N,n)`) and is finite on `K × G(N,n)` for compact `K ⊆ Ω`, so it is a varifold on `Ω`. -/
theorem Submission.varifold_tangents_dlb_exists_restricted_varifold :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μ : Measure (Euclidean N × Grassmannian N n)) (c : ℝ≥0∞), IsOpen Ω → c ≠ ∞ → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ Ω → μ (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞) → ∃ W : Varifold N n Ω, W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) := by
  intro N n Ω μ c hΩ hc hμ
  -- Step 1: `W` has the four fields of `Varifold N n Ω`, with measure `c • μ ⌞ (Ω × G(N,n))`.
  refine ⟨⟨hΩ, c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))), ?_, ?_⟩, rfl⟩
  · -- Step 2: `(Ωᶜ × G) ∩ (Ω × G) = ∅`, and `Ωᶜ × G` is measurable since `Ω` is open.
    rw [Measure.smul_apply, Measure.restrict_apply (hΩ.measurableSet.compl.prod MeasurableSet.univ),
      prod_inter_prod, compl_inter_self, empty_prod, measure_empty, smul_zero]
  · -- Step 3: `c • μ ⌞ (Ω × G)(K × G) ≤ c · μ(K × G) < ∞` for compact `K ⊆ Ω`.
    intro K hK hKΩ
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top hc
      (ne_top_of_le_ne_top (hμ K hK hKΩ) (Measure.restrict_apply_le _ _))
/-- **Simon Ch. 8, proof of 5.5, step 5** (child `first_variation_control` of
`density_lower_bound`): if `W = c · μ ⌞ Gₙ(Ω)` with `c < ∞` and `|∫ div_S X dμ| ≤ β < ∞` for every
`C¹` field `X` with `|X| ≤ 1` and compact support in `Ω`, then `W` has locally bounded first
variation and `‖δW‖(O) ≤ c β` for every open `O ⊂⊂ Ω`.  On test fields `div_S X` vanishes off
`Gₙ(Ω)`, so `δW(X) = c ∫ div_S X dμ`; every term of the supremum (8.2.5) is then at most `c β`, and
on `O ⊂⊂ Ω` that supremum is `‖δW‖(O)` (`firstVariationRieszMeasure_eq_norm`). -/
theorem Submission.varifold_tangents_dlb_restricted_firstVariation_control :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μ : Measure (Euclidean N × Grassmannian N n)) (W : Varifold N n Ω) (c β : ℝ≥0∞), c ≠ ∞ → β ≠ ∞ → W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → (∀ X : Euclidean N → Euclidean N, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ Ω → (∀ y, ‖X y‖ ≤ 1) → ENNReal.ofReal |∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂μ| ≤ β) → W.HasLocallyBoundedFirstVariation ∧ ∀ O : Set (Euclidean N), IsRelCompactOpenIn O Ω → variationMeasure W O ≤ c * β := by
  intro N n Ω μ W c β hc hβ hW hdiv
  -- Step 1: for a test field `X` on `Ω`, `δW(X) = c ∫ div_S X dμ`, since `div_S X` vanishes off
  -- `tsupport X × G(N,n) ⊆ Ω × G(N,n)`.
  have hfv : ∀ X : Varifold.TestVectorField Ω,
      W.firstVariation X = c.toReal * ∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂μ := by
    intro X
    rw [Varifold.firstVariation, hW, integral_smul_measure, smul_eq_mul,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    by_contra hne
    exact hz ⟨X.support_subset (Varifold.support_tangentialDivergence_subset X hne).1, mem_univ _⟩
  -- Step 2: every term of the supremum (8.2.5) defining `firstVariationNormOn O` is at most `c β`.
  have hnorm : ∀ O : Set (Euclidean N), W.firstVariationNormOn O ≤ c * β := by
    intro O
    rw [Varifold.firstVariationNormOn]
    refine iSup_le fun X ↦ ?_
    split_ifs with hXO
    · rw [hfv X, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
      gcongr
      exact hdiv X X.contDiff X.compactSupport X.support_subset hXO.2
    · exact zero_le
  -- Step 3: `c β < ∞`, so `W` has locally bounded first variation.
  have hW' : W.HasLocallyBoundedFirstVariation := fun O _ _ ↦
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hβ) (hnorm O)
  -- Step 4: for open `O ⊂⊂ Ω`, `‖δW‖(O)` is the supremum (8.2.5), hence at most `c β`.
  refine ⟨hW', fun O hO ↦ ?_⟩
  rw [variationMeasure, dite_eq_left hW', W.firstVariationRieszMeasure_eq_norm hW' O hO.1 hO.2]
  exact hnorm O

/-- Bad-set mass in the restricted blow-up (step 7 of the parent `density_lower_bound` proof, Simon
Ch. 8, 5.5 and 5.7, for one scale `t`): if `W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and
`O ⊆ B°_R(0)`, then `μ_W({y : x + t y ∈ E} ∩ O) ≤ c R^n μ_V(B_{tR}(x) ∩ E) / (tR)^n`, the
measures being applied to arbitrary sets as outer measures. -/
theorem Submission.varifold_tangents_dlb_restricted_bad_set_weight_le :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R : ℝ) (c : ℝ≥0∞) (W : Varifold N n (ball (0 : Euclidean N) R)) (E O : Set (Euclidean N)), 0 < t → 0 < R → W.measure = c • (rescaledMeasure V x t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) → O ⊆ ball (0 : Euclidean N) R → W.weight ({y | x + t • y ∈ E} ∩ O) ≤ c * (ENNReal.ofReal R ^ n * (V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} / ENNReal.ofReal (t * R) ^ n)) := by
  intro N n U V x t R c W E O ht hR hW hO
  -- Step 1: a Borel hull `Eh` of `E' = B_{tR}(x) ∩ E` with `μ_V(Eh) = μ_V(E')`, and the Borel set
  -- `A = {y : x + t y ∈ Eh}`.
  obtain ⟨Eh, hEEh, hEhm, hμEh⟩ : ∃ Eh : Set (Euclidean N),
      {z | z ∈ closedBall x (t * R) ∧ z ∈ E} ⊆ Eh ∧ MeasurableSet Eh ∧
        V.weight Eh = V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} :=
    ⟨_, subset_toMeasurable _ _, measurableSet_toMeasurable _ _, measure_toMeasurable _⟩
  have hAm : MeasurableSet {y : Euclidean N | x + t • y ∈ Eh} :=
    hEhm.preimage (measurable_const.add (measurable_id.const_smul t))
  -- Step 2: `{y : x + t y ∈ E} ∩ O ⊆ A`, since `|y| < R` gives `x + t y ∈ B_{tR}(x)`.
  have hsub : {y | x + t • y ∈ E} ∩ O ⊆ {y | x + t • y ∈ Eh} := by
    rintro y ⟨hyE, hyO⟩
    refine hEEh ⟨?_, hyE⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 (hO hyO)).le ht.le
  -- Step 4: `{z : t⁻¹ (z - x) ∈ A} = Eh`, as `x + t (t⁻¹ (z - x)) = z`.
  have hpre : {z | t⁻¹ • (z - x) ∈ {y | x + t • y ∈ Eh}} = Eh := by
    ext z
    simp only [mem_ofPred_eq, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
  -- Step 5: `ofReal(t⁻¹ⁿ) M = Rⁿ (M / (tR)ⁿ)`, with `T = tⁿ` and `Q = Rⁿ` in `(0, ∞)`.
  have harith : ∀ M : ℝ≥0∞, ENNReal.ofReal (t⁻¹ ^ n) * M =
      ENNReal.ofReal R ^ n * (M / ENNReal.ofReal (t * R) ^ n) := by
    intro M
    have hT0 : ENNReal.ofReal t ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne'
    have hTtop : ENNReal.ofReal t ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hQ0 : ENNReal.ofReal R ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne'
    have hQtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_pow (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ← ENNReal.inv_pow,
      ENNReal.ofReal_mul ht.le, mul_pow, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl hT0) (Or.inl hTtop)]
    calc (ENNReal.ofReal t ^ n)⁻¹ * M
        = (ENNReal.ofReal t ^ n)⁻¹ * M * (ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹) := by
          rw [ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
      _ = ENNReal.ofReal R ^ n * ((ENNReal.ofReal t ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * M) := by
          ring
  -- Steps 3, 4 and 6: monotonicity, `restrict ≤ self`, and the sibling rescaled mass formula.
  calc W.weight ({y | x + t • y ∈ E} ∩ O)
      ≤ W.weight {y | x + t • y ∈ Eh} := measure_mono hsub
    _ = W.measure ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := W.weight_apply hAm
    _ = c * (rescaledMeasure V x t).restrict
          (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)))
          ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := by
        rw [hW, Measure.smul_apply, smul_eq_mul]
    _ ≤ c * rescaledMeasure V x t ({y | x + t • y ∈ Eh} ×ˢ (univ : Set (Grassmannian N n))) := by
        gcongr
        exact Measure.restrict_le_self
    _ = c * (ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E}) := by
        rw [(Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ N n U V x t).1 _ hAm,
          hpre, hμEh]
    _ = c * (ENNReal.ofReal R ^ n *
          (V.weight {z | z ∈ closedBall x (t * R) ∧ z ∈ E} / ENNReal.ofReal (t * R) ^ n)) := by
        rw [harith]

/-- **Densities of the restricted blow-up** (child `restricted_density` of
`varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): if `t > 0`, `c ≠ ∞`,
`W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and `Θ^n(μ_V, x + ty) = θ` at a point `y ∈ B°_R(0)`, then
`Θ^n(μ_W, y) = cθ`.  For `0 < ρ < R - |y|` the closed ball `B_ρ(y)` lies in `B°_R(0)`, so the
restriction does not cut it and `μ_W(B_ρ(y)) = c t^{-n} μ_V(B_{tρ}(x + ty))` by the rescaled mass
formula; the scaling lemma for densities (with centre `z = x + ty`) then gives the density. -/
theorem Submission.varifold_tangents_dlb_restricted_hasDensity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R : ℝ) (c θ : ℝ≥0∞) (W : Varifold N n (ball (0 : Euclidean N) R)) (y : Euclidean N), 0 < t → c ≠ ∞ → W.measure = c • (rescaledMeasure V x t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) → y ∈ ball (0 : Euclidean N) R → HasDensity n V.weight (x + t • y) θ → HasDensity n W.weight y (c * θ) := by
  intro N n U V x t R c θ W y ht hc hW hy hθ
  -- Step 1: `δ := R - ‖y‖ > 0`, because `y ∈ B°_R(0)`.
  have hδ : 0 < R - ‖y‖ := sub_pos.2 (mem_ball_zero_iff.1 hy)
  -- Step 4: the scaling lemma with `z = x + t • y`; its ball-mass hypothesis is steps 2–3.
  refine Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling N n V.weight W.weight
    y (x + t • y) t (R - ‖y‖) c θ ht hδ hc (fun ρ _ hρδ ↦ ?_) hθ
  -- Step 2: for `ρ < δ`, `B_ρ(y) ⊆ B°_R(0)`, since `‖w‖ ≤ ‖w - y‖ + ‖y‖ ≤ ρ + ‖y‖ < R`.
  have hsub : closedBall y ρ ⊆ ball (0 : Euclidean N) R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
      _ < R := by linarith
  -- Step 3: `μ_W(B_ρ(y)) = c V_{x,t}((B_ρ(y) × G) ∩ (B°_R(0) × G)) = c V_{x,t}(B_ρ(y) × G)`,
  -- which is `c (t^{-n} μ_V(B_{tρ}(x + t • y)))` by part (ii) of the rescaled mass formula.
  rw [W.weight_apply measurableSet_closedBall, hW, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_closedBall.prod MeasurableSet.univ),
    Set.inter_eq_left.2 (Set.prod_mono hsub subset_rfl),
    (Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ N n U V x t).2 ht y ρ]

/-- **Simon Ch. 8, step 9 of the use of 3.7 in 5.5 and 5.7** (child `density_pullback` of
`density_lower_bound`): if `μ_W = c μ_V ⌞ Ω` with `0 < c < ∞` (`W.measure = c V ⌞ (Ω × G)`) and
`Θ^n(μ_W, ·) ≥ 1` holds `μ_W`-a.e., then `Θ^n(μ_V, ·) ≥ c⁻¹` holds `μ_V`-a.e. on `Ω`.  Near a
good `y ∈ Ω`, `μ_V(B_ρ(y)) = c⁻¹ μ_W(B_ρ(y))` for small `ρ`, so `density_scaling` with `t = 1`
gives `Θ^n(μ_V, y) = c⁻¹ Θ^n(μ_W, y) ≥ c⁻¹`. -/
theorem Submission.varifold_tangents_dlb_ae_hasDensity_of_restricted :
    ∀ (N n : ℕ) (U Ω : Set (Euclidean N)) (V : Varifold N n U) (W : Varifold N n Ω) (c : ℝ≥0∞), c ≠ 0 → c ≠ ∞ → W.measure = c • V.measure.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → (∀ᵐ y ∂W.weight, ∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ 1 ≤ θ) → ∀ᵐ y ∂V.weight, y ∈ Ω → ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ c⁻¹ ≤ θ := by
  intro N n U Ω V W c hc0 hctop hW hdens
  have hΩ : MeasurableSet Ω := W.isOpen_domain.measurableSet
  -- Step 2: `μ_W = c • (μ_V ⌞ Ω)`, checked on Borel sets.
  have hweight : W.weight = c • V.weight.restrict Ω := by
    ext A hA
    rw [W.weight_apply hA, hW, Measure.smul_apply,
      Measure.restrict_apply (hA.prod MeasurableSet.univ), prod_inter_prod, inter_univ,
      Measure.smul_apply, Measure.restrict_apply hA, V.weight_apply (hA.inter hΩ)]
  -- Step 3: `μ_V ⌞ Ω ≪ μ_W` as `c ≠ 0`, so `W` has a density `≥ 1` at `μ_V`-a.e. `y ∈ Ω`.
  have hac : V.weight.restrict Ω ≪ W.weight := by
    rw [hweight]
    exact Measure.absolutelyContinuous_smul hc0
  filter_upwards [(ae_restrict_iff' hΩ).1 (hac.ae_le hdens)] with y hy hyΩ
  obtain ⟨θ, hθ, h1θ⟩ := hy hyΩ
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 W.isOpen_domain y hyΩ
  -- Step 5: `density_scaling` with `(μ, ν, z, t, c) = (μ_W, μ_V, y, 1, c⁻¹)`.
  refine ⟨c⁻¹ * θ, Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling N n W.weight
    V.weight y y 1 δ c⁻¹ θ one_pos hδ (ENNReal.inv_ne_top.2 hc0) (fun ρ _ hρδ ↦ ?_) hθ, ?_⟩
  · -- Step 4: `B_ρ(y) ⊆ Ω` for `ρ < δ`, so `μ_V(B_ρ(y)) = c⁻¹ μ_W(B_ρ(y))`.
    rw [inv_one, one_pow, ENNReal.ofReal_one, one_mul, one_mul, hweight, Measure.smul_apply,
      Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.2 ((closedBall_subset_ball hρδ).trans hδΩ), smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  · calc c⁻¹ = c⁻¹ * 1 := (mul_one _).symm
      _ ≤ c⁻¹ * θ := by gcongr
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
/-- Restricting vague convergence to an open set (step B2 of the proof of Simon Ch. 8, 5.4): if
`μ_i → μ` as Radon measures on `Gₙ(ℝ^{n+ℓ})` and `W_i = c μ_i ⌞ Gₙ(Ω)`, `W = c μ ⌞ Gₙ(Ω)` are
varifolds on `Ω`, then `W_i → W` as Radon measures on `Gₙ(Ω)`. -/
theorem Submission.varifold_tangents_restricted_radon_converges :
    ∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (Ws : ℕ → Varifold N n Ω) (W : Varifold N n Ω) (c : ℝ≥0∞), VagueConverges μs μ → c ≠ ∞ → (∀ i, (Ws i).measure = c • (μs i).restrict (Ω ×ˢ (univ : Set (Grassmannian N n)))) → W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → Varifold.RadonConverges Ws W := by
  intro N n Ω μs μ Ws W c hμ _ hWs hW f
  -- Step 1: `P = Ω × G(N,n)` is open (`Ω` is the open domain of `W`), hence measurable.
  have hPopen : IsOpen (Ω ×ˢ (univ : Set (Grassmannian N n))) := W.isOpen_domain.prod isOpen_univ
  have hPmeas : MeasurableSet (Ω ×ˢ (univ : Set (Grassmannian N n))) := hPopen.measurableSet
  -- Step 2: the zero extension `F` of `f` is continuous with compact support on `ℝ^N × G(N,n)`;
  -- it agrees with `f` on `P` and vanishes off `P`.
  let F : C_c(Euclidean N × Grassmannian N n, ℝ) :=
    { toFun := Subtype.val.extend f 0
      continuous_toFun :=
        HasCompactSupport.continuous_extend_zero hPopen f.continuous f.hasCompactSupport
      hasCompactSupport' := f.hasCompactSupport.extend_zero continuous_subtype_val }
  have hF : ∀ z : Ω ×ˢ (univ : Set (Grassmannian N n)), F z = f z :=
    Subtype.val_injective.extend_apply f 0
  have hF0 : ∀ x ∉ Ω ×ˢ (univ : Set (Grassmannian N n)), F x = 0 := fun x hx ↦
    Function.extend_apply' _ _ _ fun ⟨z, hz⟩ ↦ hx (hz ▸ z.2)
  -- Steps 3–4: `∫ f dZ_dom = c ∫ F dν` for every varifold `Z = c ν ⌞ P` on `Ω`.
  have key : ∀ (Z : Varifold N n Ω) (ν : Measure (Euclidean N × Grassmannian N n)),
      Z.measure = c • ν.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) →
        ∫ z, f z ∂Z.domainMeasure = c.toReal * ∫ x, F x ∂ν := by
    intro Z ν hZ
    calc ∫ z, f z ∂Z.domainMeasure = ∫ z, F z ∂Z.domainMeasure := by simp only [hF]
      _ = ∫ x, F x ∂Z.domainMeasure.map Subtype.val :=
        ((MeasurableEmbedding.subtype_coe hPmeas).integral_map _).symm
      _ = c.toReal * ∫ x in Ω ×ˢ (univ : Set (Grassmannian N n)), F x ∂ν := by
        rw [Z.map_domainMeasure, hZ, integral_smul_measure, smul_eq_mul]
      _ = c.toReal * ∫ x, F x ∂ν := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  -- Step 5: vague convergence tested on `F`, multiplied by the constant `c`.
  have hlim := (hμ F).const_mul c.toReal
  rw [← key W μ hW] at hlim
  exact hlim.congr fun i ↦ (key (Ws i) (μs i) (hWs i)).symm

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
