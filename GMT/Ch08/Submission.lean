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

/-- Simon Ch. 8, proof of Lemma 5.10, printed (6): if `θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for
`σ ∈ (0,1)` (D) and the cylinder ratios satisfy the comparison (C) with error `Kερ/τ`, then for
`τ ∈ (0,1/4]` and `σ ∈ (0,1)`, `θ ≤ (e^ε μ(U^{4τ}_σ(y))/σ^n + Kεσ/τ)/ω_n`, where
`U^t_r(y) = B_r(y) ∩ {z : |q(z - y)| < t}` and `q(v) = v - p_P(v)`.  Since `|q(v)| ≤ |v|`, the
ball `B_r(y)` lies in `U^t_r(y)` for `r < t`; for `σ ≤ τ` apply (D) at `σ`, and for `τ < σ` apply
(D) at `τ` and then (C) with parameter `2τ` and radii `τ ≤ σ`, using `e^ε ≤ 2`. -/
theorem Submission.intcpt_allard_fdsb_density_cylinder_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (θ : ℝ≥0∞) (ε K : ℝ), 0 ≤ ε → Real.exp ε ≤ 2 → 0 ≤ K → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → (∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → θ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
  intro N n μ P y θ ε K hε hexp hK hD hC τ σ hτ hτ4 hσ hσ1
  -- Step 1: `|q(v)| ≤ |v|`, by Pythagoras, as `p = p_P` is symmetric and idempotent.
  have hq : ∀ v : Euclidean N, ‖v - Grassmannian.project P v‖ ≤ ‖v‖ := by
    intro v
    have hpp : inner ℝ (Grassmannian.project P v) (Grassmannian.project P v) =
        inner ℝ (Grassmannian.project P v) v := by
      calc inner ℝ (Grassmannian.project P v) (Grassmannian.project P v)
          = inner ℝ (Grassmannian.project P (Grassmannian.project P v)) v :=
            (Grassmannian.projectionLinearMap_isSymmetric P _ _).symm
        _ = inner ℝ (Grassmannian.project P v) v := by rw [Grassmannian.project_project]
    have h0 : inner ℝ (Grassmannian.project P v) (v - Grassmannian.project P v) = (0 : ℝ) := by
      rw [inner_sub_right, hpp, sub_self]
    have h := norm_add_sq_real (Grassmannian.project P v) (v - Grassmannian.project P v)
    rw [add_sub_cancel, h0, mul_zero, add_zero] at h
    nlinarith [norm_nonneg v, norm_nonneg (v - Grassmannian.project P v),
      sq_nonneg ‖Grassmannian.project P v‖]
  -- Step 2: `B_r(y) ⊆ U^t_r(y)` whenever `r < t`.
  have hball : ∀ r t : ℝ, r < t →
      closedBall y r ⊆ closedBall y r ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < t} := by
    intro r t hrt z hz
    refine ⟨hz, ?_⟩
    show ‖(z - y) - Grassmannian.project P (z - y)‖ < t
    calc ‖(z - y) - Grassmannian.project P (z - y)‖ ≤ ‖z - y‖ := hq _
      _ = dist z y := (dist_eq_norm z y).symm
      _ ≤ r := mem_closedBall.mp hz
      _ < t := hrt
  -- Steps 3–4: by (D), `θ ≤ e^ε (μ(B_r(y))/r^n)/ω_n` for `r ∈ (0,1)`.
  have hθ : ∀ r : ℝ, 0 < r → r < 1 → θ ≤ ENNReal.ofReal (Real.exp ε) *
      (μ (closedBall y r) / ENNReal.ofReal r ^ n) / unitBallVolume n := by
    intro r hr hr1
    have hrn0 : ENNReal.ofReal r ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne'
    have hrnt : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hdr : densityRatio n μ y r =
        μ (closedBall y r) / ENNReal.ofReal r ^ n / unitBallVolume n := by
      rw [densityRatio, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inr hrnt) (Or.inr hrn0)]
      ring
    have hexp_le : ENNReal.ofReal (Real.exp (ε * r)) ≤ ENNReal.ofReal (Real.exp ε) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    calc θ ≤ ENNReal.ofReal (Real.exp (ε * r)) * densityRatio n μ y r := hD r hr hr1
      _ ≤ ENNReal.ofReal (Real.exp ε) * densityRatio n μ y r := by gcongr
      _ = ENNReal.ofReal (Real.exp ε) * (μ (closedBall y r) / ENNReal.ofReal r ^ n) /
          unitBallVolume n := by rw [hdr, mul_div_assoc]
  rcases le_or_gt σ τ with hστ | hτσ
  · -- Step 5, case `σ ≤ τ`: (D) at `σ`, and `B_σ(y) ⊆ U^{4τ}_σ(y)`.
    calc θ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ) / ENNReal.ofReal σ ^ n) /
          unitBallVolume n := hθ σ hσ hσ1
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) /
          unitBallVolume n := by
        gcongr
        exact hball σ (4 * τ) (by linarith)
      _ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        gcongr
        exact le_self_add
  · -- Step 6, case `τ < σ`: (D) at `τ`, `B_τ(y) ⊆ U^{2τ}_τ(y)`, and (C) with parameter `2τ` and
    -- radii `τ ≤ σ`; the error is `e^ε Kεσ/(2τ) ≤ Kεσ/τ` as `e^ε ≤ 2`.
    have hC' := hC (2 * τ) τ σ (by linarith) (by linarith) hτ hτσ.le hσ1
    rw [show (2 : ℝ) * (2 * τ) = 4 * τ by ring] at hC'
    have herr : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (K * ε * σ / (2 * τ)) ≤
        ENNReal.ofReal (K * ε * σ / τ) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      apply ENNReal.ofReal_le_ofReal
      have hA : 0 ≤ K * ε * σ / τ := by positivity
      rw [show K * ε * σ / (2 * τ) = K * ε * σ / τ / 2 by rw [div_div, mul_comm τ 2]]
      nlinarith
    calc θ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y τ) / ENNReal.ofReal τ ^ n) /
          unitBallVolume n := hθ τ hτ (hτσ.trans hσ1)
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y τ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal τ ^ n) /
          unitBallVolume n := by
        gcongr
        exact hball τ (2 * τ) (by linarith)
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n +
          ENNReal.ofReal (K * ε * σ / (2 * τ))) / unitBallVolume n := by
        gcongr
      _ = (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (K * ε * σ / (2 * τ))) /
          unitBallVolume n := by rw [mul_add]
      _ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
            {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        gcongr
/-- Simon Ch. 8, proof of Lemma 5.10 (one-point case of Remark 5.11 (∗)): if
`θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for every `σ ∈ (0,1)`, where `0 < δ ≤ 1/2`, `2^{n+2} δ ≤ 1`,
`0 < ε ≤ δ⁴` and `|y - x| < ε`, then `θ ≤ (1 + δ) μ(B_1(x))/ω_n`.  Take `σ = 1 - ε`, so that
`B_σ(y) ⊆ B_1(x)`; then `e^{ε(1-ε)} ≤ e^ε ≤ 1 + 2ε`, `(1 - ε)^{-n} ≤ (1 + 2ε)^n ≤ 1 + (2^n - 1)2ε`,
and `e^{ε(1-ε)} (1 - ε)^{-n} ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ`. -/
theorem Submission.intcpt_allard_fdsb_one_point_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (θ : ℝ≥0∞) (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 2 ^ (n + 2) * δ ≤ 1 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → θ ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n := by
  intro N n μ x y θ δ ε hδ hδ2 hnδ hε hε4 hyx hD
  -- Step 1: `ε ≤ δ⁴ ≤ δ² ≤ 1/4`.
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hεδ : ε ≤ δ ^ 2 := hε4.trans (by nlinarith [pow_pos hδ 2])
  have hε14 : ε ≤ 1 / 4 := hεδ.trans hδsq
  -- Step 2: `σ = 1 - ε ∈ (0,1)` and `B_{1-ε}(y) ⊆ B_1(x)`.
  have hσ : 0 < 1 - ε := by linarith
  have hball : closedBall y (1 - ε) ⊆ closedBall x 1 :=
    closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith)
  -- Step 3: `e^{ε(1-ε)} ≤ e^ε ≤ 1 + 2ε`, by `|e^t - 1| ≤ 2|t|` for `|t| ≤ 1`.
  have hexp : Real.exp (ε * (1 - ε)) ≤ 1 + 2 * ε := by
    have h1 : Real.exp (ε * (1 - ε)) ≤ Real.exp ε := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε]; linarith)
    rw [abs_of_pos hε] at h2
    linarith [le_abs_self (Real.exp ε - 1)]
  -- Step 4: `(1 - ε)⁻¹ ≤ 1 + 2ε`, as `(1 - ε)(1 + 2ε) = 1 + ε(1 - 2ε) ≥ 1`.
  have hinv : (1 - ε)⁻¹ ≤ 1 + 2 * ε := by
    rw [inv_eq_one_div, div_le_iff₀ hσ]
    nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
  -- Step 5: `(1 + u)^m ≤ 1 + (2^m - 1)u` for `u = 2ε ∈ [0,1]`, by induction on `m`.
  have hbern : ∀ m : ℕ, (1 + 2 * ε) ^ m ≤ 1 + (2 ^ m - 1) * (2 * ε) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      calc (1 + 2 * ε) ^ (k + 1) = (1 + 2 * ε) ^ k * (1 + 2 * ε) := pow_succ _ _
        _ ≤ (1 + (2 ^ k - 1) * (2 * ε)) * (1 + 2 * ε) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + (2 ^ (k + 1) - 1) * (2 * ε) := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2k) hε.le)
            (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
  -- Step 6: `((1 - ε)^n)⁻¹ = ((1 - ε)⁻¹)^n ≤ (1 + 2ε)^n ≤ 1 + (2^n - 1)2ε`.
  have hpowinv : ((1 - ε) ^ n)⁻¹ ≤ 1 + (2 ^ n - 1) * (2 * ε) := by
    rw [← inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hσ.le) hinv n).trans (hbern n)
  -- Step 7: `e^{ε(1-ε)}/(1 - ε)^n ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ`.
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [show (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n by ring] at hnδ
  have hreal : Real.exp (ε * (1 - ε)) / (1 - ε) ^ n ≤ 1 + δ := by
    rw [div_eq_mul_inv]
    calc Real.exp (ε * (1 - ε)) * ((1 - ε) ^ n)⁻¹
        ≤ (1 + 2 * ε) * (1 + (2 ^ n - 1) * (2 * ε)) :=
          mul_le_mul hexp hpowinv (inv_nonneg.mpr (pow_nonneg hσ.le n)) (by linarith)
      _ ≤ 1 + 4 * 2 ^ n * ε := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ n) hε.le)
            (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
      _ ≤ 1 + δ := by
          nlinarith [mul_le_mul_of_nonneg_left hεδ (by linarith : (0 : ℝ) ≤ 4 * 2 ^ n)]
  -- Step 8: the density bound at `σ = 1 - ε`, rearranged in `[0,∞]`: `densityRatio` is
  -- `μ(B_σ(y)) ω_n⁻¹ (σ^n)⁻¹` as `σ^n ∈ (0,∞)`, and `e^{εσ}/σ^n` is a single `ofReal`.
  have hRn0 : ENNReal.ofReal (1 - ε) ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hσ).ne'
  have hRnt : ENNReal.ofReal (1 - ε) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hfac : ENNReal.ofReal (Real.exp (ε * (1 - ε))) * (ENNReal.ofReal (1 - ε) ^ n)⁻¹ =
      ENNReal.ofReal (Real.exp (ε * (1 - ε)) / (1 - ε) ^ n) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hσ n), ENNReal.ofReal_pow hσ.le, div_eq_mul_inv]
  calc θ ≤ ENNReal.ofReal (Real.exp (ε * (1 - ε))) * densityRatio n μ y (1 - ε) :=
        hD (1 - ε) hσ (by linarith)
    _ = ENNReal.ofReal (Real.exp (ε * (1 - ε))) * (ENNReal.ofReal (1 - ε) ^ n)⁻¹ *
          μ (closedBall y (1 - ε)) / unitBallVolume n := by
      simp only [densityRatio, div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inr hRnt) (Or.inr hRn0)]
      ring
    _ = ENNReal.ofReal (Real.exp (ε * (1 - ε)) / (1 - ε) ^ n) * μ (closedBall y (1 - ε)) /
          unitBallVolume n := by rw [hfac]
    _ ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n := by
      gcongr
/-- Density sum over a fibre with at least two points (Simon Ch. 8, 5.11(∗) from (8), in the proof
of 5.9): with `d` the minimal distance between distinct points of `s`, the per-point bounds at
`τ = d/16`, `σ = d/(8δ²)` and the cluster bound at `(σ, d/4)` sum to
`Σ_{y∈s} Θ(y) ≤ (1 + δ) μ(B_1(x))/ω_n + δ`, the constants being absorbed by `Aδ ≤ 1`. -/
theorem Submission.intcpt_allard_fdsb_separated_sum_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞) (K c δ ε : ℝ) (M : ℕ), 0 ≤ K → 0 ≤ c → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → (2 + 2 * c + 2 * c / (unitBallVolume n).toReal + 2 * (M : ℝ) * K / (unitBallVolume n).toReal) * δ ≤ 1 → 2 ≤ s.card → s.card ≤ M → (∀ y ∈ s, ‖y - x‖ < ε ∧ ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → Θ y ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n) → (∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) + ENNReal.ofReal (c * δ ^ 2)) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
  intro N n μ P x s Θ K c δ ε M hK hc hδ hδh hε hεδ hA hs2 hsM hpt hCB
  -- Step 0: `ω_n ∈ (0, ∞)`; `ω := ω_n.toReal` is positive with `ofReal ω = ω_n`.
  have hω0 : unitBallVolume n ≠ 0 :=
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨ω, hω_def⟩ : ∃ ω, (unitBallVolume n).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos hω0 hωtop
  have hωW : ENNReal.ofReal ω = unitBallVolume n := hω_def ▸ ENNReal.ofReal_toReal hωtop
  rw [hω_def] at hA
  -- `δ² ≤ 1/4`, `ε ≤ δ⁴ ≤ δ²` and `e^ε ≤ 1 + 2ε ≤ 1 + 2δ²`.
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hδ2 hδ2pos.le]
  have hexp : Real.exp ε ≤ 1 + 2 * δ ^ 2 := by
    have h := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε]; linarith)
    rw [abs_of_pos hε] at h
    linarith [le_abs_self (Real.exp ε - 1)]
  -- Step 1: the minimal distance `d` between distinct points of `s`; `0 < d < 2ε`.
  obtain ⟨p, hp, hpmin⟩ := s.offDiag.exists_min_image (fun q ↦ ‖q.1 - q.2‖) (by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    exact ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩⟩)
  obtain ⟨hp1, hp2, hp12⟩ := Finset.mem_offDiag.1 hp
  obtain ⟨d, hd_def⟩ : ∃ d, ‖p.1 - p.2‖ = d := ⟨_, rfl⟩
  have hdmin : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖ := by
    intro y hy y' hy' h
    rw [← hd_def]
    exact hpmin (y, y') (Finset.mem_offDiag.2 ⟨hy, hy', h⟩)
  have hd : 0 < d := hd_def ▸ norm_pos_iff.2 (sub_ne_zero.2 hp12)
  have hdε : d < 2 * ε := by
    rw [← hd_def]
    calc ‖p.1 - p.2‖ = ‖(p.1 - x) - (p.2 - x)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖p.1 - x‖ + ‖p.2 - x‖ := norm_sub_le _ _
      _ < ε + ε := add_lt_add (hpt _ hp1).1 (hpt _ hp2).1
      _ = 2 * ε := by ring
  -- Step 2: the scales `τ = d/16` and `σ = d/(8δ²)`.
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = d / 16 := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = d / (8 * δ ^ 2) := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd.ne'
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 / 4 := by rw [hτ]; linarith
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσδ : σ ≤ δ ^ 2 := by
    rw [hσ, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hδ 4]
  have hσ1 : σ < 1 := by linarith
  have hστ : 2 * δ ^ 2 * σ ≤ 4 * τ := le_of_eq (by rw [hσ, hτ]; field_simp; ring)
  have hsep : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * (4 * τ) ≤ ‖y - y'‖ := by
    intro y hy y' hy' h
    rw [hτ]
    linarith [hdmin y hy y' hy' h]
  have hk : K * ε * σ / τ ≤ 2 * K * δ ^ 2 := by
    have e : K * ε * σ / τ = 2 * K * ε / δ ^ 2 := by
      rw [hσ, hτ]; field_simp; ring
    rw [e, div_le_iff₀ hδ2pos]
    nlinarith [mul_le_mul_of_nonneg_left hεδ hK]
  -- Step 6: the real absorption inequalities, from `Aδ ≤ 1`.
  have ha : 0 ≤ 2 * c / ω := by positivity
  have hb : 0 ≤ 2 * (M : ℝ) * K / ω := by positivity
  have hA1 : (2 + 2 * c) * δ ≤ 1 := by
    nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le]
  have hA2 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * c) hδ.le]
  have hi : Real.exp ε * (1 + c * δ ^ 2) ≤ 1 + δ := by
    have h1 : Real.exp ε * (1 + c * δ ^ 2) ≤ (1 + 2 * δ ^ 2) * (1 + c * δ ^ 2) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    have h2 : (2 + 2 * c) * δ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hA1 hδ.le
    have h3 : 0 ≤ c * (δ ^ 2 * (1 - 2 * δ ^ 2)) :=
      mul_nonneg hc (mul_nonneg hδ2pos.le (by linarith))
    nlinarith [h1, h2, h3]
  have hii : Real.exp ε * (c * δ ^ 2) + (M : ℝ) * (2 * K * δ ^ 2) ≤ δ * ω := by
    have h1 : Real.exp ε * (c * δ ^ 2) ≤ 2 * (c * δ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ * (δ * ω) ≤ 1 * (δ * ω) :=
      mul_le_mul_of_nonneg_right hA2 (by positivity)
    have h3 : (2 * c / ω + 2 * (M : ℝ) * K / ω) * δ * (δ * ω) =
        (2 * c + 2 * (M : ℝ) * K) * δ ^ 2 := by
      field_simp
    nlinarith [h1, h2, h3]
  -- Steps 3–5: sum the per-point bounds at `(τ, σ)` and apply (CB) at `(σ, 4τ)`, `#s ≤ M`.
  have hCB' := hCB σ (4 * τ) hσ0 hσδ hστ hsep
  have hfin : ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
        ENNReal.ofReal (c * δ ^ 2)) + (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2) ≤
      ENNReal.ofReal (1 + δ) * μ (closedBall x 1) + ENNReal.ofReal δ * unitBallVolume n := by
    have e1 : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (1 + c * δ ^ 2) ≤
        ENNReal.ofReal (1 + δ) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal hi
    have h1 : 0 ≤ Real.exp ε * (c * δ ^ 2) := by positivity
    have h2 : 0 ≤ (M : ℝ) * (2 * K * δ ^ 2) := by positivity
    have e2 : ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (c * δ ^ 2) +
        (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2) ≤ ENNReal.ofReal δ * unitBallVolume n := by
      rw [← hωW, ← ENNReal.ofReal_mul (Real.exp_pos ε).le, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add h1 h2,
        ← ENNReal.ofReal_mul hδ.le]
      exact ENNReal.ofReal_le_ofReal hii
    calc _ = ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
          (ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (c * δ ^ 2) +
            (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_left e1 _) e2
  calc ∑ y ∈ s, Θ y
      ≤ ∑ y ∈ s, (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩
          {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) +
          ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n :=
        Finset.sum_le_sum fun y hy ↦ (hpt y hy).2 τ σ hτ0 hτ1 hσ0 hσ1
    _ = (ENNReal.ofReal (Real.exp ε) * ∑ y ∈ s, μ (closedBall y σ ∩
          {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n +
          (s.card : ℝ≥0∞) * ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n := by
        rw [← ENNReal.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ (ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) +
          ENNReal.ofReal (c * δ ^ 2)) + (M : ℝ≥0∞) * ENNReal.ofReal (2 * K * δ ^ 2)) /
          unitBallVolume n :=
        ENNReal.div_le_div_right (add_le_add (mul_le_mul_right hCB' _)
          (mul_le_mul' (by exact_mod_cast hsM) (ENNReal.ofReal_le_ofReal hk))) _
    _ ≤ (ENNReal.ofReal (1 + δ) * μ (closedBall x 1) + ENNReal.ofReal δ * unitBallVolume n) /
          unitBallVolume n := ENNReal.div_le_div_right hfin _
    _ = ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ := by
        rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hω0 hωtop]
/-- **Simon Ch. 8, proof of 5.10, printed (3), p. 221** (child `good_point_monotonicity` of
`allard_lemma`): if `B°_1(y) ⊆ U`, `μ_W(B°_1(y)) ≤ Λ` and `‖δW‖(B_ρ(y)) ≤ ε μ_W(B_ρ(y))` for
`0 < ρ < 1` (printed (1)), the monotonicity formula 3.3 with `ρ₀ = 1` shows that
`e^{ερ} ρ^{-n} μ_W(B_ρ(y))` is increasing on `(0, 1)` and that `Θ^n(μ_W, y)` exists, is finite and
is at most `e^{εσ} ω_n^{-1} σ^{-n} μ_W(B_σ(y))`.  Hence `μ_W(B_σ(y)) ≤ e^ε Λ ρ^{-n} σ^n` for
`0 < σ < ρ < 1`, and letting `ρ ↑ 1` gives `μ_W(B_σ(y)) ≤ e^ε Λ σ^n`. -/
theorem Submission.intcpt_allard_good_point_monotonicity :
    MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (ε Λ : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 ≤ ε → W.weight (ball y 1) ≤ ENNReal.ofReal Λ → (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) → MonotoneOn (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (ε * ρ)) * W.weight (closedBall y ρ) / ENNReal.ofReal ρ ^ n) (Ioo 0 1) ∧ (∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ θ ≠ ∞ ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n W.weight y σ) ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → W.weight (closedBall y σ) ≤ ENNReal.ofReal (Real.exp ε * Λ * σ ^ n) := by
  intro hMF N n U W y ε Λ hW hball hε hΛ hratio
  -- The monotonicity and density statements are 3.3 with `ρ₀ = 1`, `Λ = ε` (and `ρ = σ`).
  obtain ⟨hmono, θ, hθ, hθfin, hθle⟩ := hMF N n U W y 1 ε hW one_pos hball hε hratio
  refine ⟨hmono, ⟨θ, hθ, hθfin, fun σ hσ0 hσ1 ↦ (hθle σ σ hσ0 le_rfl hσ1).1⟩, ?_⟩
  intro σ hσ0 hσ1
  -- For `σ < ρ < 1`: `μ_W(B_σ(y)) ≤ e^{εσ} μ_W(B_σ(y)) ≤ e^{ερ} μ_W(B_ρ(y)) σ^n / ρ^n`
  -- `≤ e^ε Λ σ^n / ρ^n`, using `B_ρ(y) ⊆ B°_1(y)`.
  have key : ∀ ρ ∈ Ioo σ 1,
      W.weight (closedBall y σ) ≤ ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n) := by
    rintro ρ ⟨hσρ, hρ1⟩
    have hρ0 : 0 < ρ := hσ0.trans hσρ
    have hs0 : ENNReal.ofReal σ ^ n ≠ 0 := pow_ne_zero n (ENNReal.ofReal_pos.mpr hσ0).ne'
    have hsT : ENNReal.ofReal σ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hexp : ENNReal.ofReal (Real.exp (ε * ρ)) ≤ ENNReal.ofReal (Real.exp ε) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_of_le_one_right hε hρ1.le))
    have hμ : W.weight (closedBall y ρ) ≤ ENNReal.ofReal Λ :=
      (measure_mono (closedBall_subset_ball hρ1)).trans hΛ
    calc W.weight (closedBall y σ)
        ≤ ENNReal.ofReal (Real.exp (ε * σ)) * W.weight (closedBall y σ) :=
          le_mul_of_one_le_left zero_le
            (ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg hε hσ0.le)))
      _ = ENNReal.ofReal (Real.exp (ε * σ)) * W.weight (closedBall y σ) / ENNReal.ofReal σ ^ n *
            ENNReal.ofReal σ ^ n := (ENNReal.div_mul_cancel hs0 hsT).symm
      _ ≤ ENNReal.ofReal (Real.exp (ε * ρ)) * W.weight (closedBall y ρ) / ENNReal.ofReal ρ ^ n *
            ENNReal.ofReal σ ^ n := mul_le_mul_left (hmono ⟨hσ0, hσ1⟩ ⟨hρ0, hρ1⟩ hσρ.le) _
      _ ≤ ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal Λ / ENNReal.ofReal ρ ^ n *
            ENNReal.ofReal σ ^ n :=
          mul_le_mul_left (ENNReal.div_le_div_right (mul_le_mul' hexp hμ) _) _
      _ = ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n) := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hσ0.le n), ENNReal.ofReal_div_of_pos (pow_pos hρ0 n),
            ENNReal.ofReal_mul (Real.exp_pos ε).le, ENNReal.ofReal_pow hρ0.le,
            ENNReal.ofReal_pow hσ0.le]
  -- Let `ρ ↑ 1`.
  have hlim : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp ε * Λ / ρ ^ n * σ ^ n)) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (Real.exp ε * Λ * σ ^ n))) := by
    have h : Tendsto (fun ρ : ℝ ↦ Real.exp ε * Λ / ρ ^ n * σ ^ n) (𝓝 1)
        (𝓝 (Real.exp ε * Λ / 1 ^ n * σ ^ n)) :=
      (tendsto_const_nhds.div ((continuous_pow n).tendsto 1) (by simp)).mul tendsto_const_nhds
    rw [one_pow, div_one] at h
    exact ENNReal.tendsto_ofReal (h.mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT hσ1) key)

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
