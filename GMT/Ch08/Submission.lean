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

/-- A compact exhaustion of an open `U ⊆ ℝ^N` (preamble of the proof of Simon Ch. 8, 1.2): compact
`K_p ⊆ U`, `p ∈ ℕ`, with `K_p ⊆ interior K_{p+1}`, increasing in `p`, and `⋃_p K_p = U`.  If
`U = ℝ^N` then `K_p = B_{p+1}(0)`; otherwise, with `F = ℝ^N ∖ U`,
`K_p = {x : |x| ≤ p + 1, dist(x, F) ≥ 1/(p + 1)}`. -/
theorem Submission.frt_weq_open_compact_exhaustion :
    ∀ (N : ℕ) (U : Set (Euclidean N)), IsOpen U → ∃ K : ℕ → Set (Euclidean N), (∀ p, IsCompact (K p)) ∧ (∀ p, K p ⊆ U) ∧ (∀ p, K p ⊆ interior (K (p + 1))) ∧ Monotone K ∧ ⋃ p, K p = U := by
  intro N U hU
  by_cases hUu : U = univ
  · -- Case 1: `U = ℝ^N`; take `K_p = B_{p+1}(0)`.
    subst hUu
    refine ⟨fun p : ℕ ↦ closedBall (0 : Euclidean N) ((p : ℝ) + 1),
      fun p ↦ isCompact_closedBall _ _, fun p ↦ subset_univ _, fun p ↦ ?_, fun p q hpq ↦ ?_, ?_⟩
    · -- `B_{p+1}(0) ⊆ U_{p+2}(0) = interior B_{p+2}(0)`.
      rw [interior_closedBall _ (by positivity)]
      exact closedBall_subset_ball (by push_cast; linarith)
    · -- The radii increase with `p`.
      exact closedBall_subset_closedBall (by simpa using hpq)
    · -- Every `x` lies in `B_{q+1}(0)` once `q ≥ |x|`.
      refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
      obtain ⟨q, hq⟩ := exists_nat_ge ‖x‖
      exact ⟨q, mem_closedBall_zero_iff.2 (by linarith)⟩
  · -- Case 2: `F = ℝ^N ∖ U` is closed and nonempty;
    -- take `K_p = {x : |x| ≤ p + 1, dist(x, F) ≥ 1/(p + 1)}`.
    have hF : (Uᶜ).Nonempty := nonempty_compl.2 hUu
    have hFc : IsClosed Uᶜ := hU.isClosed_compl
    let K : ℕ → Set (Euclidean N) := fun p ↦
      {x | ‖x‖ ≤ (p : ℝ) + 1 ∧ 1 / ((p : ℝ) + 1) ≤ infDist x Uᶜ}
    -- (a) `K_p` is closed and lies in the compact ball `B_{p+1}(0)`.
    have hKc : ∀ p, IsCompact (K p) := fun p ↦
      (isCompact_closedBall (0 : Euclidean N) ((p : ℝ) + 1)).of_isClosed_subset
        ((isClosed_le continuous_norm continuous_const).inter
          (isClosed_le continuous_const (continuous_infDist_pt _)))
        fun x hx ↦ mem_closedBall_zero_iff.2 hx.1
    -- (b) `K_p` misses `F`, as `dist(x, F) = 0 < 1/(p + 1)` for `x ∈ F`.
    have hKU : ∀ p, K p ⊆ U := by
      intro p x hx
      by_contra hxU
      have h0 : infDist x Uᶜ = 0 := infDist_zero_of_mem hxU
      have hpos : (0 : ℝ) < 1 / ((p : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith [hx.2]
    -- (c) The open set `O_p = {|x| < p + 2, dist(x, F) > 1/(p + 2)}` contains `K_p` and lies in
    -- `K_{p+1}`, hence in `interior K_{p+1}`.
    have hKint : ∀ p, K p ⊆ interior (K (p + 1)) := by
      intro p
      have hO : IsOpen {x : Euclidean N | ‖x‖ < (p : ℝ) + 2 ∧ 1 / ((p : ℝ) + 2) < infDist x Uᶜ} :=
        (isOpen_lt continuous_norm continuous_const).inter
          (isOpen_lt continuous_const (continuous_infDist_pt _))
      have hOK : {x : Euclidean N | ‖x‖ < (p : ℝ) + 2 ∧ 1 / ((p : ℝ) + 2) < infDist x Uᶜ} ⊆
          K (p + 1) := by
        intro x hx
        refine ⟨?_, ?_⟩
        · push_cast; linarith [hx.1]
        · push_cast
          have : (p : ℝ) + 1 + 1 = (p : ℝ) + 2 := by ring
          rw [this]; exact hx.2.le
      refine Subset.trans ?_ (interior_maximal hOK hO)
      intro x hx
      refine ⟨by linarith [hx.1], lt_of_lt_of_le ?_ hx.2⟩
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    -- (d) Monotonicity, by induction from `K_p ⊆ interior K_{p+1} ⊆ K_{p+1}`.
    have hKmono : Monotone K := monotone_nat_of_le_succ fun p ↦ (hKint p).trans interior_subset
    refine ⟨K, hKc, hKU, hKint, hKmono, ?_⟩
    -- (e) Each `x ∈ U` has `dist(x, F) > 0`, so `x ∈ K_m` with `m = max p q` for `p, q` below.
    refine Subset.antisymm (iUnion_subset hKU) fun x hx ↦ ?_
    have hδ : 0 < infDist x Uᶜ := (hFc.notMem_iff_infDist_pos hF).1 fun h ↦ h hx
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt hδ
    obtain ⟨q, hq⟩ := exists_nat_ge ‖x‖
    have hpm : (p : ℝ) ≤ (max p q : ℕ) := by exact_mod_cast le_max_left p q
    have hqm : (q : ℝ) ≤ (max p q : ℕ) := by exact_mod_cast le_max_right p q
    refine mem_iUnion.2 ⟨max p q, ?_, ?_⟩
    · linarith
    · have : 1 / (((max p q : ℕ) : ℝ) + 1) ≤ 1 / ((p : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
/-- A Borel representative of the `n`-density (Step 1 of the proof of Simon Ch. 8, 1.2): for an
s-finite `μ` on `ℝ^N`, `g(x) = liminf_k μ(B_{1/(k+1)}(x)) / (ω_n (k+1)^{-n})` is Borel and
`g(x) = Θ^n(μ, x)` at every `x` where `Θ^n(μ, x)` exists. -/
theorem Submission.frt_weq_density_borel_representative :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) [SFinite μ], ∃ g : Euclidean N → ℝ≥0∞, Measurable g ∧ ∀ (x : Euclidean N) (t : ℝ≥0∞), HasDensity n μ x t → g x = t := by
  intro N n μ _
  -- Step 1: `x ↦ μ(B_r(x))` is Borel, as `B_r(x)` is the section at `x` of the closed set
  -- `{(x, y) : dist y x ≤ r}`.
  have hball : ∀ r : ℝ, Measurable fun x : Euclidean N ↦ μ (closedBall x r) := fun r ↦
    measurable_measure_prodMk_left (ν := μ)
      (s := {p : Euclidean N × Euclidean N | dist p.2 p.1 ≤ r})
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  -- Step 2: hence so is `x ↦ densityRatio n μ x r`, a constant multiple of it.
  have hratio : ∀ r : ℝ, Measurable fun x ↦ densityRatio n μ x r := fun r ↦
    (hball r).div_const _
  -- Step 3: `g(x) = liminf_k densityRatio n μ x (1/(k+1))` is Borel.
  refine ⟨fun x ↦ liminf (fun k : ℕ ↦ densityRatio n μ x (1 / ((k : ℝ) + 1))) atTop,
    Measurable.liminf fun k ↦ hratio _, fun x t ht ↦ ?_⟩
  -- Step 4: `ρ_k = 1/(k+1) → 0⁺`, so the ratios along `ρ_k` tend to `t` and their liminf is `t`.
  have hρ : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun _ ↦ Set.mem_Ioi.2 Nat.one_div_pos_of_nat⟩
  have ht' : Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 t) := ht
  exact (ht'.comp hρ).liminf_eq
/-- Upper-density comparison with `H^n` (Simon Ch. 1, 3.3, in the form used for Ch. 8, 1.2): if `W`
is open, `A ⊆ W` and `t ≤ limsup_{ρ↓0} μ(B_ρ(x))/(ω_n ρ^n)` for every `x ∈ A`, then
`t H^n(A) ≤ μ(W)`.  Mathlib's `μHE[n]` is `c • μH[n]` for a Haar scalar `c`; the isodiametric
inequality (Simon Ch. 1, 2.10, by Steiner symmetrization) gives `c 2^n ≤ ω_n`, and Vitali's covering
lemma with Simon's finite-tail argument bounds `μH[n](A)` by the radii of disjoint good balls. -/
theorem Submission.frt_weq_mul_hausdorff_le_of_upper_density :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (t : ℝ≥0∞), IsOpen W → A ⊆ W → (∀ x ∈ A, t ≤ limsup (densityRatio n μ x) (𝓝[>] 0)) → t * μHE[n] A ≤ μ W := by
  intro N n μ W A t hW hAW hden
  -- Step 1a: two nonempty real sets at mutual distance `≤ d` have total length `≤ 2d`.
  have hcross1 : ∀ {P Q : Set ℝ}, P.Nonempty → Q.Nonempty → ∀ {d : ℝ},
      (∀ a ∈ P, ∀ b ∈ Q, dist a b ≤ d) → volume P + volume Q ≤ ENNReal.ofReal (2 * d) := by
    intro P Q hP hQ d hcross
    obtain ⟨a₀, ha₀⟩ := hP
    obtain ⟨b₀, hb₀⟩ := hQ
    have hdist (a : ℝ) (ha : a ∈ P) (b : ℝ) (hb : b ∈ Q) : a - b ≤ d ∧ b - a ≤ d :=
      abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
    have hPl : BddBelow P := ⟨b₀ - d, fun a ha => by linarith [(hdist a ha b₀ hb₀).2]⟩
    have hPu : BddAbove P := ⟨b₀ + d, fun a ha => by linarith [(hdist a ha b₀ hb₀).1]⟩
    have hQl : BddBelow Q := ⟨a₀ - d, fun b hb => by linarith [(hdist a₀ ha₀ b hb).1]⟩
    have hQu : BddAbove Q := ⟨a₀ + d, fun b hb => by linarith [(hdist a₀ ha₀ b hb).2]⟩
    have hPQ : sSup P ≤ d + sInf Q := by
      apply csSup_le ⟨a₀, ha₀⟩
      intro a ha
      have h : a - d ≤ sInf Q :=
        le_csInf ⟨b₀, hb₀⟩ fun b hb => by linarith [(hdist a ha b hb).1]
      linarith
    have hQP : sSup Q ≤ d + sInf P := by
      apply csSup_le ⟨b₀, hb₀⟩
      intro b hb
      have h : b - d ≤ sInf P :=
        le_csInf ⟨a₀, ha₀⟩ fun a ha => by linarith [(hdist a ha b hb).2]
      linarith
    have hwidthP : 0 ≤ sSup P - sInf P :=
      sub_nonneg.mpr ((csInf_le hPl ha₀).trans (le_csSup hPu ha₀))
    have hwidthQ : 0 ≤ sSup Q - sInf Q :=
      sub_nonneg.mpr ((csInf_le hQl hb₀).trans (le_csSup hQu hb₀))
    calc
      volume P + volume Q ≤ volume (Icc (sInf P) (sSup P)) + volume (Icc (sInf Q) (sSup Q)) :=
        add_le_add (measure_mono (subset_Icc_csInf_csSup hPl hPu))
          (measure_mono (subset_Icc_csInf_csSup hQl hQu))
      _ = ENNReal.ofReal ((sSup P - sInf P) + (sSup Q - sInf Q)) := by
        rw [Real.volume_Icc, Real.volume_Icc, ENNReal.ofReal_add hwidthP hwidthQ]
      _ ≤ ENNReal.ofReal (2 * d) := ENNReal.ofReal_le_ofReal (by linarith)
  -- Step 1: the isodiametric inequality `|C| ≤ ω_n (diam C / 2)^n` on `ℝ^n` (Simon Ch. 1, 2.10).
  have hiso : ∀ C : Set (EuclideanSpace ℝ (Fin n)),
      volume C ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (ediam C / 2) ^ n := by
    intro C
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hball : (ball (0 : EuclideanSpace ℝ (Fin 0)) 1) = univ := by
        ext x
        simp [Subsingleton.elim x 0]
      rw [pow_zero, mul_one, hball]
      exact measure_mono (subset_univ C)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    -- Step 1b: Steiner symmetrization in the coordinate `j`, followed by closure, keeps a compact
    -- set compact, does not increase its diameter or decrease its volume, makes it symmetric under
    -- the reflection `x_j ↦ -x_j` and keeps its symmetry under the other coordinate reflections.
    have hstep : ∀ (j : Fin (m + 1)) (K : Set (EuclideanSpace ℝ (Fin (m + 1)))), IsCompact K →
        ∃ K' : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K' ∧ ediam K' ≤ ediam K ∧
          volume K ≤ volume K' ∧
          (∀ x ∈ K', WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ K') ∧
          (∀ i, i ≠ j → (∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K) →
            ∀ x ∈ K', WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K') := by
      intro j K hK
      -- The centred interval replacing a slice, the slice through `x`, and the symmetrized set.
      set cen : Set ℝ → Set ℝ := fun T => {s | T.Nonempty ∧ |s| ≤ (volume T).toReal / 2}
        with hcen
      set sl : EuclideanSpace ℝ (Fin (m + 1)) → Set ℝ :=
        fun x => {t | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ K} with hsl
      set S : Set (EuclideanSpace ℝ (Fin (m + 1))) := {x | x j ∈ cen (sl x)} with hS
      have hrefl_cont : ∀ i : Fin (m + 1), Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
          WithLp.toLp 2 (Function.update x.ofLp i (-x i)) := by
        intro i
        apply (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp
        apply continuous_pi
        intro k
        by_cases hki : k = i
        · subst k
          simpa only [Function.update_self] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => -x i) by fun_prop)
        · simpa only [Function.update_of_ne hki] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x k) by fun_prop)
      -- The diameter does not increase.
      have hdiamS : ediam S ≤ ediam K := by
        by_cases hfin : ediam K = ∞
        · rw [hfin]
          exact le_top
        have hbounded : Bornology.IsBounded K := isBounded_iff_ediam_ne_top.mpr hfin
        have hdiam : ediam S ≤ ENNReal.ofReal (diam K) := by
          apply ediam_le_of_forall_dist_le
          intro x hx y hy
          have hx' : x j ∈ cen (sl x) := hx
          have hy' : y j ∈ cen (sl y) := hy
          let D : ℝ := diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2
          have hupd : ∀ a b : ℝ,
              dist (WithLp.toLp 2 (Function.update x.ofLp j a) : EuclideanSpace ℝ (Fin (m + 1)))
                (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
                dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
            intro a b
            rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
            have hsum := Finset.sum_erase_add Finset.univ
              (fun i : Fin (m + 1) => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
            have hsum' := Finset.sum_erase_add Finset.univ
              (fun i : Fin (m + 1) => dist (Function.update x.ofLp j a i)
                (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
            have hrest : (∑ i ∈ Finset.univ.erase j,
                dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
                ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
            rw [hrest, Function.update_self, Function.update_self] at hsum'
            simp only
            linarith
          have hsq (a : ℝ) (ha : a ∈ sl x) (b : ℝ) (hb : b ∈ sl y) :
              dist a b ^ 2 ≤ D := by
            have hsq' := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hbounded ha hb) 2
            rw [hupd] at hsq'
            dsimp [D]
            linarith
          have hD : 0 ≤ D := by
            obtain ⟨a, ha⟩ := hx'.1
            obtain ⟨b, hb⟩ := hy'.1
            exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
          have hsqrt := Real.sq_sqrt hD
          have hcross : ∀ a ∈ sl x, ∀ b ∈ sl y, dist a b ≤ Real.sqrt D := by
            intro a ha b hb
            have h := hsq a ha b hb
            nlinarith [dist_nonneg (x := a) (y := b), Real.sqrt_nonneg D]
          have hsum := hcross1 hx'.1 hy'.1 hcross
          have hfin' : volume (sl x) + volume (sl y) ≠ ∞ :=
            ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
          have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
          rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp hfin').1 (ENNReal.add_ne_top.mp hfin').2,
            ENNReal.toReal_ofReal (by positivity)] at hreal
          have hcentered : dist (x j) (y j) ≤ Real.sqrt D := by
            calc
              dist (x j) (y j) = |x j - y j| := Real.dist_eq _ _
              _ ≤ |x j| + |y j| := abs_sub _ _
              _ ≤ (volume (sl x)).toReal / 2 + (volume (sl y)).toReal / 2 :=
                add_le_add hx'.2 hy'.2
              _ ≤ Real.sqrt D := by linarith
          have hcentered_sq : dist (x j) (y j) ^ 2 ≤ D := by
            nlinarith [dist_nonneg (x := x j) (y := y j), Real.sqrt_nonneg D]
          dsimp [D] at hcentered_sq
          nlinarith [dist_nonneg (x := x) (y := y), diam_nonneg (s := K)]
        simpa only [diam, ENNReal.ofReal_toReal hfin] using hdiam
      -- The volume does not decrease (Fubini along the `j`-th coordinate).
      have hvolS : volume K ≤ volume S := by
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
        let φ : ℝ × (Fin m → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) :=
          fun p => WithLp.toLp 2 (e.symm p)
        have hφ : MeasurePreserving φ volume volume :=
          (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
            (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
        have hφcoord (t : ℝ) (z : Fin m → ℝ) : φ (t, z) j = t :=
          Fin.insertNth_apply_same (α := fun _ : Fin (m + 1) => ℝ) j t z
        let T := toMeasurable volume S
        have hT : MeasurableSet T := measurableSet_toMeasurable volume S
        have hTS : S ⊆ T := subset_toMeasurable volume S
        have hslice (t : ℝ) (z : Fin m → ℝ) : sl (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' K := by
          ext s
          change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ K) ↔
            WithLp.toLp 2 (j.insertNth s z) ∈ K
          rw [Fin.update_insertNth]
        have hfinite (z : Fin m → ℝ) : volume ((fun t => φ (t, z)) ⁻¹' K) ≠ ∞ := by
          have hproj : IsCompact ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x j) '' K) :=
            hK.image (by fun_prop)
          have hsub : (fun t => φ (t, z)) ⁻¹' K ⊆
              (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x j) '' K :=
            fun t ht => ⟨φ (t, z), ht, hφcoord t z⟩
          exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
        have hcenvol : ∀ U : Set ℝ, volume U ≠ ∞ → volume (cen U) = volume U := by
          intro U hfin
          rcases U.eq_empty_or_nonempty with rfl | hU
          · simp [hcen]
          · have hinterval : cen U = Icc (-(volume U).toReal / 2) ((volume U).toReal / 2) := by
              ext x
              simp [hcen, hU, abs_le, neg_div]
            rw [hinterval, Real.volume_Icc]
            convert ENNReal.ofReal_toReal hfin using 1
            congr 1
            ring
        calc
          volume K = volume (φ ⁻¹' K) :=
            (hφ.measure_preimage hK.measurableSet.nullMeasurableSet).symm
          _ = ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' K) :=
            Measure.prod_apply_symm (hK.measurableSet.preimage hφ.measurable)
          _ = ∫⁻ z : Fin m → ℝ, volume (cen ((fun t => φ (t, z)) ⁻¹' K)) :=
            lintegral_congr fun z => (hcenvol _ (hfinite z)).symm
          _ ≤ ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
            apply lintegral_mono
            intro z
            apply measure_mono
            intro t ht
            apply hTS
            change φ (t, z) j ∈ cen (sl (φ (t, z)))
            rw [hφcoord, hslice]
            exact ht
          _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
          _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
          _ = volume S := measure_toMeasurable S
      -- Symmetry under the reflection in the `j`-th coordinate.
      have hsymS : ∀ x ∈ S, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ S := by
        intro x hx
        have hx' : x j ∈ cen (sl x) := hx
        show (WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :
            EuclideanSpace ℝ (Fin (m + 1))) j ∈
          cen (sl (WithLp.toLp 2 (Function.update x.ofLp j (-x j))))
        have hsl : sl (WithLp.toLp 2 (Function.update x.ofLp j (-x j))) = sl x := by
          ext t
          simp only [hsl, mem_ofPred_eq, Function.update_idem]
        rw [hsl]
        simp only [Function.update_self]
        exact ⟨hx'.1, by simpa only [abs_neg] using hx'.2⟩
      -- Symmetry under the reflection in another coordinate `i ≠ j` is preserved.
      have hpresS : ∀ i, i ≠ j →
          (∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K) →
          ∀ x ∈ S, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ S := by
        intro i hij hKi x hx
        have hx' : x j ∈ cen (sl x) := hx
        show (WithLp.toLp 2 (Function.update x.ofLp i (-x i)) :
            EuclideanSpace ℝ (Fin (m + 1))) j ∈
          cen (sl (WithLp.toLp 2 (Function.update x.ofLp i (-x i))))
        have hcomm : ∀ t : ℝ,
            (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x.ofLp i (-x i)) :
                EuclideanSpace ℝ (Fin (m + 1))).ofLp j t) : EuclideanSpace ℝ (Fin (m + 1))) =
            WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x.ofLp j t) : EuclideanSpace ℝ (Fin (m + 1))).ofLp i
              (-(WithLp.toLp 2 (Function.update x.ofLp j t) :
                EuclideanSpace ℝ (Fin (m + 1))) i)) := by
          intro t
          ext k
          by_cases hki : k = i
          · subst k
            simp [hij]
          · by_cases hkj : k = j
            · subst k
              simp [Function.update_apply, hki]
            · simp [Function.update_apply, hki, hkj]
        have hsl : sl (WithLp.toLp 2 (Function.update x.ofLp i (-x i))) = sl x := by
          ext t
          simp only [hsl, mem_ofPred_eq]
          rw [hcomm t]
          constructor
          · intro h
            convert hKi _ h using 1
            ext k
            by_cases hki : k = i
            · subst k
              simp [hij]
            · simp [Function.update_apply, hki]
          · exact hKi _
        rw [hsl]
        simpa only [WithLp.ofLp_toLp, Function.update_of_ne (Ne.symm hij)] using hx'
      refine ⟨closure S, ?_, ?_, ?_, ?_, ?_⟩
      · apply Bornology.IsBounded.isCompact_closure
        apply isBounded_iff_ediam_ne_top.mpr
        exact ne_top_of_le_ne_top hK.isBounded.ediam_ne_top hdiamS
      · rw [ediam_closure]
        exact hdiamS
      · exact hvolS.trans (measure_mono subset_closure)
      · intro x hx
        have hsub : S ⊆ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
            WithLp.toLp 2 (Function.update x.ofLp j (-x j))) ⁻¹' closure S :=
          fun y hy => subset_closure (hsymS y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (hrefl_cont j)) hx
      · intro i hij hKi x hx
        have hsub : S ⊆ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
            WithLp.toLp 2 (Function.update x.ofLp i (-x i))) ⁻¹' closure S :=
          fun y hy => subset_closure (hpresS i hij hKi y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (hrefl_cont i)) hx
    by_cases hfin : ediam C = ∞
    · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        ENNReal.top_pow (Nat.succ_ne_zero m),
        ENNReal.mul_top (measure_ball_pos volume _ one_pos).ne']
      exact le_top
    have hbounded : Bornology.IsBounded C := isBounded_iff_ediam_ne_top.mpr hfin
    -- Step 1c: symmetrizing `closure C` in every coordinate gives a compact `K` with
    -- `diam K ≤ diam C`, `|C| ≤ |K|`, symmetric under every coordinate reflection.
    have hiter : ∀ s : Finset (Fin (m + 1)), ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))),
        IsCompact K ∧ ediam K ≤ ediam C ∧ volume C ≤ volume K ∧
        ∀ i ∈ s, ∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ K := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨closure C, hbounded.isCompact_closure, (ediam_closure C).le,
          measure_mono subset_closure, by simp⟩
      | @insert i s hi ih =>
        obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
        obtain ⟨K', hK', hdiam', hvol', hsym', hpres'⟩ := hstep i K hK
        refine ⟨K', hK', hdiam'.trans hdiam, hvol.trans hvol', ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hsym'
        · exact hpres' k (fun h => hi (h ▸ hk)) (hsym k hk)
    obtain ⟨K, hK, hdiam, hvol, hsym⟩ := hiter Finset.univ
    -- Step 1d: `K` is centrally symmetric, hence `K ⊆ B_{diam K / 2}(0)`.
    have hneg : ∀ x ∈ K, -x ∈ K := by
      intro x hx
      have hmem (s : Finset (Fin (m + 1))) :
          WithLp.toLp 2 (fun k => if k ∈ s then -x k else x k) ∈ K := by
        induction s using Finset.induction_on with
        | empty => simpa using hx
        | @insert i s hi ih =>
          convert hsym i (Finset.mem_univ i) _ ih using 1
          ext k
          by_cases hki : k = i
          · subst k
            simp [hi]
          · simp [hki]
      have heq : (WithLp.toLp 2 fun k => -x k) = -x := by
        ext k
        rfl
      simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
    have hKb : Bornology.IsBounded K := hK.isBounded
    have hsub : K ⊆ closedBall 0 (diam K / 2) := by
      intro x hx
      have hdist := dist_le_diam_of_mem hKb hx (hneg x hx)
      rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
      norm_num at hdist
      rw [mem_closedBall, dist_zero_right]
      linarith
    calc volume C ≤ volume K := hvol
      _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) (diam K / 2)) :=
          measure_mono hsub
      _ = ENNReal.ofReal ((diam K / 2) ^ (m + 1)) *
            volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
          rw [Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin]
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) * (ediam K / 2) ^ (m + 1) := by
          rw [mul_comm, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by norm_num),
            ENNReal.ofReal_ofNat, diam, ENNReal.ofReal_toReal hKb.ediam_ne_top]
      _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) * (ediam C / 2) ^ (m + 1) := by
          gcongr
  -- Step 2: the Haar scalar `c` with `μHE[n] = c • μH[n]` satisfies `c 2^n ≤ ω_n`: by Step 1,
  -- `volume ≤ (ω_n / 2^n) • μH[n]` on `ℝ^n`, and `volume = c • μH[n]`; compare on the unit ball.
  have hnorm : ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
      ℝ≥0∞) * 2 ^ n ≤ unitBallVolume n := by
    have hω0 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      (measure_ball_pos volume _ one_pos).ne'
    have hωtop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ∞ := measure_ball_lt_top.ne
    have h2n0 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2ntop : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] •
          μH[(n:ℝ)] :=
      Measure.isAddLeftInvariant_eq_smul _ _
    have h1 : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
        Measure.mkMetric ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
          fun r : ℝ≥0∞ => r ^ (n:ℝ)) := by
      apply Measure.le_mkMetric _ _ 1 one_pos
      intro s _
      calc volume s ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (ediam s / 2) ^ n :=
            hiso s
        _ = ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
              fun r : ℝ≥0∞ => r ^ (n:ℝ)) (ediam s) := by
          simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast, div_eq_mul_inv, mul_pow,
            ENNReal.inv_pow]
          ring
    have h2 : (Measure.mkMetric ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) •
          fun r : ℝ≥0∞ => r ^ (n:ℝ)) : Measure (EuclideanSpace ℝ (Fin n))) ≤
        (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) • μH[(n:ℝ)] :=
      Measure.mkMetric_mono_smul (ENNReal.div_ne_top hωtop h2n0)
        (ENNReal.div_pos hω0 h2ntop).ne' (Eventually.of_forall fun _ => le_rfl)
    have hB : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n *
          μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      simpa only [Measure.smul_apply, smul_eq_mul] using
        (h1.trans h2) (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    have hcB : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
          ℝ≥0∞) * μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using
        congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin n)) => ν (ball 0 1)) hvol
    have h2le : (2 : ℝ≥0∞) ^ n ≤ μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      have hmul : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n ≤
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        calc volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n
            ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n *
                μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * 2 ^ n := by gcongr
          _ = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
                μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
            rw [mul_right_comm, ENNReal.div_mul_cancel h2n0 h2ntop]
      exact (ENNReal.mul_le_mul_iff_right hω0 hωtop).mp hmul
    calc ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
          ℝ≥0∞) * 2 ^ n
        ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor μH[(n:ℝ)] :
            ℝ≥0∞) * μH[(n:ℝ)] (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by gcongr
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcB.symm
  -- Step 3: the covering argument (Simon's proof of 3.3).  If every `x ∈ A` is the centre of
  -- arbitrarily small balls `B` with `τ ω_n r^n ≤ μ(B)`, then `τ c μH[n](A) ≤ μ(W)`.
  have hcov : ∀ τ c : ℝ≥0∞, c * 2 ^ n ≤ unitBallVolume n → τ ≠ 0 → μ W ≠ ∞ →
      (∀ x ∈ A, ∀ ε > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < ε ∧
        τ * (unitBallVolume n * ENNReal.ofReal r ^ n) ≤ μ (closedBall x r)) →
      τ * (c * μH[(n:ℝ)] A) ≤ μ W := by
    intro τ c hc hτ0 hμW hball
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
    have hH : μH[(n:ℝ)] A = ⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ),
        OuterMeasure.mkMetric'.pre (fun s : Set (Euclidean N) => ediam s ^ (n:ℝ)) δ A := by
      rw [← Measure.toOuterMeasure_apply, Measure.hausdorffMeasure,
        Measure.mkMetric_toOuterMeasure, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
        OuterMeasure.iSup_apply]
      simp only [OuterMeasure.iSup_apply]
    rw [hH, ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun δ => ?_
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun hδ => ?_
    obtain ⟨R₀, -, hR₀, hR₀δ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
    have hR : 0 < R₀ / 6 := by
      have := ENNReal.ofReal_pos.mp hR₀
      positivity
    set R := R₀ / 6 with hRdef
    -- Step 3a: the fine family `G` of good balls of radius `≤ R` inside `W`.
    set G : Set (Euclidean N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ R ∧
        closedBall p.1 p.2 ⊆ W ∧ τ * (unitBallVolume n * ENNReal.ofReal p.2 ^ n) ≤
          μ (closedBall p.1 p.2)} with hG
    have hfine : ∀ x ∈ A, ∀ ε > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < ε ∧ (x, r) ∈ G := by
      intro x hx ε hε
      obtain ⟨ε', hε', hε'W⟩ := Metric.isOpen_iff.mp hW x (hAW hx)
      obtain ⟨r, hr0, hrlt, hr⟩ := hball x hx (min ε (min R (ε' / 2))) (by positivity)
      have h1 : r < ε := hrlt.trans_le (min_le_left _ _)
      have h2 : r < R := hrlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h3 : r < ε' / 2 := hrlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      refine ⟨r, hr0, h1, hx, hr0, h2.le, ?_, hr⟩
      exact (closedBall_subset_ball (h3.trans (half_lt_self hε'))).trans hε'W
    -- Step 3b: Vitali's lemma gives a countable disjoint subfamily `u` such that every ball of
    -- `G` meets a ball of `u` of at least half its radius.
    obtain ⟨u, huG, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun p : Euclidean N × ℝ => closedBall p.1 p.2) G (fun p => p.2) 2 one_lt_two
      (fun p hp => hp.2.1.le) R (fun p hp => hp.2.2.1)
      (fun p hp => nonempty_closedBall.mpr hp.2.1.le)
    have hucount : u.Countable := by
      refine Set.PairwiseDisjoint.countable_of_nonempty_interior (α := Euclidean N) hudisj ?_
      intro p hp
      exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huG hp).2.1)⟩
    have : Countable u := hucount.to_subtype
    set w : u → ℝ≥0∞ := fun p => ENNReal.ofReal p.1.2 ^ n with hw
    have hsum : τ * unitBallVolume n * ∑' p, w p ≤ μ W := by
      calc τ * unitBallVolume n * ∑' p, w p = ∑' p : u, τ * (unitBallVolume n * w p) := by
            rw [← ENNReal.tsum_mul_left]
            congr 1
            funext p
            ring
        _ ≤ ∑' p : u, μ (closedBall p.1.1 p.1.2) :=
            ENNReal.tsum_le_tsum fun p => (huG p.2).2.2.2.2
        _ = μ (⋃ p : u, closedBall p.1.1 p.1.2) :=
            (measure_iUnion (fun (p q : u) hpq => hudisj p.2 q.2 (Subtype.coe_ne_coe.mpr hpq))
              fun (p : u) => measurableSet_closedBall).symm
        _ ≤ μ W := measure_mono (iUnion_subset fun p => (huG p.2).2.2.2.1)
    have hSfin : ∑' p, w p ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.mul_top (mul_ne_zero hτ0 hω0)] at hsum
      exact hμW (top_le_iff.mp hsum)
    -- Step 3c: for every finite `F ⊆ u`, the balls of `F` and the tripled balls of `u ∖ F`
    -- cover `A`.
    have hrem : ∀ F : Finset u, A ⊆ (⋃ p ∈ F, closedBall p.1.1 p.1.2) ∪
        ⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2) := by
      intro F x hx
      by_cases hxF : x ∈ ⋃ p ∈ F, closedBall p.1.1 p.1.2
      · exact Or.inl hxF
      right
      have hclosed : IsClosed (⋃ p ∈ F, closedBall p.1.1 p.1.2) :=
        isClosed_biUnion_finset fun p _ => isClosed_closedBall
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hxF
      obtain ⟨r, hr0, hrε, hrG⟩ := hfine x hx (ε / 2) (half_pos hε)
      obtain ⟨b, hbu, ⟨z, hz1, hz2⟩, hrb⟩ := hucov (x, r) hrG
      simp only [mem_closedBall] at hz1 hz2 hrb
      have hbF : (⟨b, hbu⟩ : u) ∉ F := by
        intro hbF
        have hzF : z ∈ ⋃ p ∈ F, closedBall p.1.1 p.1.2 :=
          mem_iUnion₂.mpr ⟨⟨b, hbu⟩, hbF, mem_closedBall.mpr hz2⟩
        have hzball : z ∈ ball x ε := by
          rw [mem_ball]
          linarith
        exact hεsub hzball hzF
      refine mem_iUnion.mpr ⟨⟨⟨b, hbu⟩, hbF⟩, ?_⟩
      rw [mem_closedBall]
      have := dist_triangle x z b.1
      rw [dist_comm] at hz1
      simp only
      linarith
    -- Step 3d: estimate the size-`δ` approximation of `μH[n]` and let `F` exhaust `u`.
    set pre := OuterMeasure.mkMetric'.pre (fun s : Set (Euclidean N) => ediam s ^ (n:ℝ)) δ
      with hpre
    have hpreball : ∀ (x : Euclidean N) (r : ℝ), 0 ≤ r → r ≤ 3 * R →
        pre (closedBall x r) ≤ ENNReal.ofReal (2 * r) ^ n := by
      intro x r hr hrR
      have hd : ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
        ediam_le_of_forall_dist_le fun y hy z hz => by
          have := dist_triangle_right y z x
          rw [mem_closedBall] at hy hz
          linarith
      have hδ' : ENNReal.ofReal (2 * r) ≤ δ :=
        (ENNReal.ofReal_le_ofReal (by rw [hRdef] at hrR; linarith)).trans hR₀δ.le
      refine (OuterMeasure.mkMetric'.pre_le (hd.trans hδ')).trans ?_
      rw [ENNReal.rpow_natCast]
      exact pow_le_pow_left' hd n
    have hbound : ∀ F : Finset u,
        pre A ≤ 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p := by
      intro F
      have hsmall : ∀ p : u, pre (closedBall p.1.1 p.1.2) ≤ 2 ^ n * w p := by
        intro p
        have hp := huG p.2
        refine (hpreball _ _ hp.2.1.le (by linarith [hp.2.2.1])).trans_eq ?_
        rw [ENNReal.ofReal_mul (by norm_num), mul_pow, ENNReal.ofReal_ofNat]
      have hlarge : ∀ p : {p : u // p ∉ F},
          pre (closedBall p.1.1.1 (3 * p.1.1.2)) ≤ 6 ^ n * w p.1 := by
        intro p
        have hp := huG p.1.2
        refine (hpreball _ _ (by linarith [hp.2.1]) (by linarith [hp.2.2.1])).trans_eq ?_
        rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num), mul_pow]
        norm_num
        rfl
      calc pre A ≤ pre ((⋃ p ∈ F, closedBall p.1.1 p.1.2) ∪
            ⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2)) := measure_mono (hrem F)
        _ ≤ pre (⋃ p ∈ F, closedBall p.1.1 p.1.2) +
            pre (⋃ p : {p : u // p ∉ F}, closedBall p.1.1.1 (3 * p.1.1.2)) :=
            measure_union_le _ _
        _ ≤ (∑ p ∈ F, 2 ^ n * w p) + ∑' p : {p : u // p ∉ F}, 6 ^ n * w p.1 := by
            gcongr
            · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun p _ => hsmall p)
            · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun p => hlarge p)
        _ ≤ 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p := by
            rw [← Finset.mul_sum, ENNReal.tsum_mul_left]
            gcongr
            exact ENNReal.sum_le_tsum F
    have hlim : Tendsto
        (fun F : Finset u => 2 ^ n * ∑' p, w p + 6 ^ n * ∑' p : {p : u // p ∉ F}, w p)
        atTop (𝓝 (2 ^ n * ∑' p, w p)) := by
      have h0 := ENNReal.tendsto_tsum_compl_atTop_zero hSfin
      have h6 : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      simpa using (tendsto_const_nhds (x := (2 : ℝ≥0∞) ^ n * ∑' p, w p)).add
        (ENNReal.Tendsto.const_mul (a := (6 : ℝ≥0∞) ^ n) h0 (Or.inr h6))
    have hpreA : pre A ≤ 2 ^ n * ∑' p, w p := ge_of_tendsto' hlim hbound
    calc τ * (c * pre A) ≤ τ * (c * (2 ^ n * ∑' p, w p)) := by gcongr
      _ = τ * (c * 2 ^ n) * ∑' p, w p := by ring
      _ ≤ τ * unitBallVolume n * ∑' p, w p := by gcongr
      _ ≤ μ W := hsum
  -- Step 4: for `0 < τ < t` the density hypothesis yields the good balls of Step 3; take the
  -- supremum over `τ`.
  by_cases hμW : μ W = ∞
  · rw [hμW]
    exact le_top
  have hHE : μHE[n] A = ((volume : Measure (EuclideanSpace ℝ (Fin n))).addHaarScalarFactor
      μH[(n:ℝ)] : ℝ≥0∞) * μH[(n:ℝ)] A := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hHE]
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  rw [ENNReal.iSup_mul]
  refine iSup_le fun τ => ?_
  rw [ENNReal.iSup_mul]
  refine iSup_le fun hτ => ?_
  rcases eq_or_ne τ 0 with rfl | hτ0
  · simp
  refine hcov τ _ hnorm hτ0 hμW fun x hx ε hε => ?_
  have hlt : τ < limsup (densityRatio n μ x) (𝓝[>] 0) := hτ.trans_le (hden x hx)
  obtain ⟨r, hqr, hr⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hlt).and_eventually
    (Ioo_mem_nhdsGT hε)).exists
  refine ⟨r, hr.1, hr.2, ?_⟩
  have hne0 : unitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
    mul_ne_zero (measure_ball_pos volume _ one_pos).ne'
      (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr.1).ne')
  have hnetop : unitBallVolume n * ENNReal.ofReal r ^ n ≠ ∞ :=
    ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).mp hqr).le

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
