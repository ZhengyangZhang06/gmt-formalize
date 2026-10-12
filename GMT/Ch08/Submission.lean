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
/-- Cylinder cut-off weight (Simon Ch. 8, proof of Lemma 5.10, displays (6)–(7): the `h` used in
3.5, `h(z) = f(|q(z - y)|)` with `f ≡ 1` on `[0, τ)`, `f ≡ 0` on `(2τ, ∞)`).  With
`M₀ = 4 sup |st'|` (`st = Real.smoothTransition`), `h(z) = st(4 - ‖q(z - y)‖²/τ²)` is `C¹`, takes
values in `[0, 1]`, equals `1` where `‖q(z - y)‖ < τ` and `0` where `‖q(z - y)‖ ≥ 2τ`
(`q = id - p_P`), and `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ) ‖p_S - p_P‖ ‖z - y‖`. -/
theorem Submission.intcpt_allard_cm_cylinder_weight :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (N n : ℕ) (P : Grassmannian N n) (y : Euclidean N) (τ : ℝ), 0 < τ → ∃ h : Euclidean N → ℝ, ContDiff ℝ 1 h ∧ (∀ z, 0 ≤ h z ∧ h z ≤ 1) ∧ (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) ∧ (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) ∧ ∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M₀ / τ * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖ := by
  -- Step 1: `deriv smoothTransition` vanishes off `[0, 1]`, where `smoothTransition` is locally
  -- constant (`0` on `(-∞, 0)`, `1` on `(1, ∞)`).
  have hst'_zero : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition u = 0 := by
    intro u hu
    rcases lt_or_ge u 0 with hu0 | hu0
    · have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hu0] with v hv
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hv)
      rw [hev.deriv_eq, deriv_const]
    · have hu1 : 1 < u := lt_of_not_ge fun h1 ↦ hu ⟨hu0, h1⟩
      have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu1] with v hv
        exact Real.smoothTransition.one_of_one_le (le_of_lt hv)
      rw [hev.deriv_eq, deriv_const]
  -- Step 2: `deriv smoothTransition` is continuous with compact support, hence bounded by some
  -- `L ≥ 0`; take `M₀ := 4 L`.
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨L, hL⟩ :=
    (HasCompactSupport.intro isCompact_Icc hst'_zero).exists_bound_of_continuous hcont
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨4 * L, by positivity, ?_⟩
  intro N n P y τ hτ
  -- Step 3: `Q = id - p_P` as a continuous linear map, and
  -- `h z = smoothTransition (4 - ‖Q (z - y)‖² / τ²)`.
  obtain ⟨Q, hQ⟩ : ∃ Q : Euclidean N →L[ℝ] Euclidean N,
      ∀ v, Q v = v - Grassmannian.project P v :=
    ⟨LinearMap.toContinuousLinearMap (LinearMap.id - Grassmannian.projectionLinearMap P),
      fun v ↦ rfl⟩
  have hτ2 : 0 < τ ^ 2 := by positivity
  refine ⟨fun z ↦ Real.smoothTransition (4 - ‖Q (z - y)‖ ^ 2 / τ ^ 2), ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 4: `h` is `C^∞`, in particular `C¹`.
    exact (Real.smoothTransition.contDiff (n := 1)).comp
      (contDiff_const.sub
        (((Q.contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ).div_const _))
  · -- Step 5: values in `[0, 1]`.
    exact fun z ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · -- Step 6: `‖q(z - y)‖ < τ` gives `4 - F(z) > 3 ≥ 1`, so `h z = 1`.
    intro z hz
    apply Real.smoothTransition.one_of_one_le
    have h1 : ‖Q (z - y)‖ ^ 2 < τ ^ 2 := by
      rw [hQ]
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    have h2 : ‖Q (z - y)‖ ^ 2 / τ ^ 2 < 1 := (div_lt_one hτ2).2 h1
    linarith
  · -- Step 7: `‖q(z - y)‖ ≥ 2τ` gives `4 - F(z) ≤ 0`, so `h z = 0`.
    intro z hz
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : (2 * τ) ^ 2 ≤ ‖Q (z - y)‖ ^ 2 := by
      rw [hQ]
      exact pow_le_pow_left₀ (by positivity) hz 2
    have h2 : 4 ≤ ‖Q (z - y)‖ ^ 2 / τ ^ 2 := by
      rw [le_div_iff₀ hτ2]
      nlinarith
    linarith
  · intro z S
    -- Step 8: chain rule.  `z' ↦ Q (z' - y)` has derivative `Q`, so with
    -- `G z' = 4 - ‖Q (z' - y)‖² (τ²)⁻¹` we get `Dh(z) = st'(G z) • DG(z)`.
    have hQd : HasFDerivAt (fun z' ↦ Q (z' - y)) Q z := by
      have h1 := Q.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
      rwa [ContinuousLinearMap.comp_id] at h1
    have hGd := (hQd.norm_sq.mul_const ((τ ^ 2)⁻¹)).const_sub (4 : ℝ)
    have hst : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (4 - ‖Q (z - y)‖ ^ 2 * (τ ^ 2)⁻¹))
        (4 - ‖Q (z - y)‖ ^ 2 * (τ ^ 2)⁻¹) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hfun : (fun z' ↦ Real.smoothTransition (4 - ‖Q (z' - y)‖ ^ 2 / τ ^ 2)) =
        Real.smoothTransition ∘ fun z' ↦ 4 - ‖Q (z' - y)‖ ^ 2 * (τ ^ 2)⁻¹ := by
      funext z'
      simp only [Function.comp_apply, div_eq_mul_inv]
    rw [hfun, (hst.comp_hasFDerivAt z hGd).fderiv]
    simp only [_root_.smul_apply, _root_.neg_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    -- Step 9: `p_P (Q w) = 0`, and self-adjointness of `p_P`, `p_S` gives
    -- `⟪Q w, Q (p_S w)⟫ = ⟪(p_S - p_P) (Q w), w⟫` with `w = z - y`.
    have hpa : Grassmannian.projectionLinearMap P (Q (z - y)) = 0 := by
      have h1 := Grassmannian.project_project P (z - y)
      simp only [Grassmannian.project] at h1
      rw [hQ, Grassmannian.project, map_sub, h1, sub_self]
    have hkey : inner ℝ (Q (z - y)) (Q (Grassmannian.project S (z - y))) =
        inner ℝ (LinearMap.toContinuousLinearMap
          (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P) (Q (z - y)))
          (z - y) := by
      rw [LinearMap.coe_toContinuousLinearMap', LinearMap.sub_apply, hpa, sub_zero,
        hQ (Grassmannian.project S (z - y)), inner_sub_right]
      simp only [Grassmannian.project]
      rw [← Grassmannian.projectionLinearMap_isSymmetric P (Q (z - y)), hpa, inner_zero_left,
        sub_zero, Grassmannian.projectionLinearMap_isSymmetric S (Q (z - y)) (z - y)]
    rw [hkey]
    -- Step 10: if `G z < 0` then `st'(G z) = 0`; otherwise `‖Q w‖ ≤ 2τ`, and
    -- `|Dh(z)[p_S w]| ≤ L (2/τ²) ‖T‖ (2τ) ‖w‖ = (4L/τ) ‖T‖ ‖w‖`.
    set T := LinearMap.toContinuousLinearMap
      (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)
    set a := Q (z - y)
    set w := z - y
    have hRHS : 0 ≤ 4 * L / τ * ‖T‖ * ‖w‖ := by positivity
    rcases lt_or_ge (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹) 0 with hneg | hnn
    · rw [hst'_zero _ fun hmem ↦ (not_le.2 hneg) hmem.1, zero_mul, abs_zero]
      exact hRHS
    · have ha2 : ‖a‖ ≤ 2 * τ := by
        rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hτ2] at hnn
        nlinarith [norm_nonneg a]
      have hd : |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)| ≤ L := by
        simpa only [Real.norm_eq_abs] using hL (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)
      have hX : |inner ℝ (T a) w| ≤ ‖T‖ * (2 * τ) * ‖w‖ :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right ((T.le_opNorm a).trans
            (mul_le_mul_of_nonneg_left ha2 (norm_nonneg _))) (norm_nonneg _))
      calc |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹) *
            -((τ ^ 2)⁻¹ * (2 * inner ℝ (T a) w))|
          = |deriv Real.smoothTransition (4 - ‖a‖ ^ 2 * (τ ^ 2)⁻¹)| *
            ((τ ^ 2)⁻¹ * (2 * |inner ℝ (T a) w|)) := by
            rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hτ2), abs_two]
        _ ≤ L * ((τ ^ 2)⁻¹ * (2 * (‖T‖ * (2 * τ) * ‖w‖))) := by
            gcongr
        _ = 4 * L / τ * ‖T‖ * ‖w‖ := by
            field_simp
            ring
/-- **Simon Ch. 8, proof of 5.10, p. 221, the radial cutoffs** (child `radial_cutoff` of
`cylinder_monotonicity`, step 1): for `A > 1`, `φ(s) = st((A² - s)/(A² - 1))`, with `st` Mathlib's
`Real.smoothTransition`, is a `C¹` non-increasing function with values in `[0,1]` that is `1` on
`(-∞, 1]` and `0` on `[A², ∞)`. -/
theorem Submission.intcpt_allard_cm_radial_cutoff :
    ∀ A : ℝ, 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) ∧
      (∀ s, s ≤ 1 → φ s = 1) ∧ (∀ s, A ^ 2 ≤ s → φ s = 0) := by
  intro A hA
  -- `d = A² - 1 > 0`, so `s ↦ (A² - s)/d` is a decreasing affine map.
  have hd : 0 < A ^ 2 - 1 := by nlinarith
  refine ⟨fun s ↦ Real.smoothTransition ((A ^ 2 - s) / (A ^ 2 - 1)), ?_, fun s s' hs ↦ ?_,
    fun s ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, fun s hs ↦ ?_,
    fun s hs ↦ ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hd.le)
  · -- `s ≤ 1` gives `(A² - s)/d ≥ 1`.
    exact Real.smoothTransition.one_of_one_le ((one_le_div₀ hd).2 (by linarith))
  · -- `A² ≤ s` gives `(A² - s)/d ≤ 0`.
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
/-- Dominated convergence for shrinking radial cutoffs (step 4 of the cylinder monotonicity used
for Simon Ch. 8, 5.9): if `φ_j = 1` on `(-∞, 1]`, `φ_j = 0` on `[A_j², ∞)`, `0 ≤ φ_j ≤ 1`,
`A_j → 1` and `μ(B_R(y)) < ∞` with `t A_j ≤ R`, then
`∫ φ_j(|z - y|²/t²) h(z) dμ(z) → ∫_{B_t(y)} h dμ` for measurable `0 ≤ h ≤ 1`. -/
theorem Submission.intcpt_allard_cm_cutoff_integral_tendsto :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℕ → ℝ → ℝ) (A : ℕ → ℝ) (t R : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ j, Measurable (φ j)) → (∀ j s, 0 ≤ φ j s ∧ φ j s ≤ 1) → (∀ j s, s ≤ 1 → φ j s = 1) → (∀ j s, A j ^ 2 ≤ s → φ j s = 0) → (∀ j, 0 < A j) → Tendsto A atTop (𝓝 1) → 0 < t → (∀ j, t * A j ≤ R) → μ (closedBall y R) ≠ ∞ → Tendsto (fun j ↦ ∫ z, φ j (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) atTop (𝓝 (∫ z in closedBall y t, h z ∂μ)) := by
  intro N μ y h φ A t R hh h01 hφm hφ01 hφ1 hφ0 hA hAlim ht htR hμR
  -- Step 1: `∫_{B_t(y)} h dμ = ∫ 1_{B_t(y)} h dμ`; dominated convergence with bound `1_{B_R(y)}`.
  rw [← integral_indicator measurableSet_closedBall]
  refine tendsto_integral_filter_of_dominated_convergence
    ((closedBall y R).indicator fun _ ↦ (1 : ℝ)) ?_ ?_ ?_ ?_
  -- Step 2: every `F_j` is measurable.
  · have hmeas : Measurable fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2 := by fun_prop
    exact Eventually.of_forall fun j ↦ (((hφm j).comp hmeas).mul hh).aestronglyMeasurable
  -- Step 3: domination `‖F_j z‖ ≤ 1_{B_R(y)} z`.
  · refine Eventually.of_forall fun j ↦ ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ closedBall y R
    · rw [indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hφ01 j _).1 (h01 z).1)]
      exact (mul_le_of_le_one_left (h01 z).1 (hφ01 j _).2).trans (h01 z).2
    · have hRz : R < ‖z - y‖ := by rwa [mem_closedBall, dist_eq_norm, not_le] at hz
      have hAz : A j ≤ ‖z - y‖ / t := by
        rw [le_div_iff₀ ht]
        linarith [htR j, mul_comm (A j) t]
      have hs : A j ^ 2 ≤ ‖z - y‖ ^ 2 / t ^ 2 := by
        rw [← div_pow]
        exact pow_le_pow_left₀ (hA j).le hAz 2
      rw [indicator_of_notMem hz, hφ0 j _ hs, zero_mul, norm_zero]
  -- Step 4: `1_{B_R(y)}` is integrable since `μ(B_R(y)) < ∞`.
  · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hμR)
  -- Step 5: pointwise convergence `F_j z → 1_{B_t(y)} h z`.
  · refine ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ closedBall y t
    · have hzt : ‖z - y‖ ≤ t := by rwa [mem_closedBall, dist_eq_norm] at hz
      have hs : ‖z - y‖ ^ 2 / t ^ 2 ≤ 1 := by
        rw [div_le_one₀ (pow_pos ht 2)]
        exact pow_le_pow_left₀ (norm_nonneg _) hzt 2
      rw [indicator_of_mem hz]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      rw [hφ1 j _ hs, one_mul]
    · have hzt : t < ‖z - y‖ := by rwa [mem_closedBall, dist_eq_norm, not_le] at hz
      have hs : 1 < ‖z - y‖ ^ 2 / t ^ 2 := by
        rw [one_lt_div₀ (pow_pos ht 2)]
        exact pow_lt_pow_left₀ hzt ht.le two_ne_zero
      have hA2 : Tendsto (fun j ↦ A j ^ 2) atTop (𝓝 1) := by simpa using hAlim.pow 2
      rw [indicator_of_notMem hz]
      refine tendsto_const_nhds.congr' ((hA2.eventually_le_const hs).mono fun j hj ↦ ?_)
      dsimp only
      rw [hφ0 j _ hj, zero_mul]
/-- Cylinder masses from cut-off ball integrals (Simon Ch. 8, proof of Lemma 5.10, display (7):
the last step after integrating 3.5 from `σ` to `ρ`).  Let `0 ≤ h ≤ 1` be measurable with `h = 1`
where `‖q(z - y)‖ < τ` and `h = 0` where `‖q(z - y)‖ ≥ 2τ` (`q = id - p_P`), `0 < σ ≤ ρ` and
`μ(B_ρ(y)) < ∞`.  If `σ^{-n} ∫_{B_σ(y)} h dμ ≤ ρ^{-n} ∫_{B_ρ(y)} h dμ + E`, then in `[0, ∞]`
`σ^{-n} μ(U^τ_σ(y)) ≤ ρ^{-n} μ(U^{2τ}_ρ(y)) + max(E, 0)`, where
`U^τ_r(y) = B_r(y) ∩ {z : ‖q(z - y)‖ < τ}`. -/
theorem Submission.intcpt_allard_cm_cylinder_mass_bound :
    ∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (h : Euclidean N → ℝ) (τ σ ρ E : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) → (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) → 0 < σ → σ ≤ ρ → μ (closedBall y ρ) ≠ ∞ → (∫ z in closedBall y σ, h z ∂μ) / σ ^ n ≤ (∫ z in closedBall y ρ, h z ∂μ) / ρ ^ n + E → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal E := by
  intro N n μ P y h τ σ ρ E hmeas hbd h1 h0 hσ hσρ hfin hineq
  -- Step 1: `z ↦ ‖q(z - y)‖` is continuous (`p_P` is linear on `ℝ^N`), so the cylinders
  -- `S₁ = {‖q(z - y)‖ < τ}` and `S₂ = {‖q(z - y)‖ < 2τ}` are open, hence measurable.
  have hcont : Continuous fun z : Euclidean N ↦ ‖(z - y) - Grassmannian.project P (z - y)‖ := by
    have hP : Continuous (Grassmannian.project P) :=
      (Grassmannian.projectionLinearMap P).continuous_of_finiteDimensional
    exact ((continuous_id.sub continuous_const).sub
      (hP.comp (continuous_id.sub continuous_const))).norm
  have hS₁ : MeasurableSet {z : Euclidean N | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ} :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hS₂ : MeasurableSet
      {z : Euclidean N | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ} :=
    (isOpen_lt hcont continuous_const).measurableSet
  -- Step 2: `B_σ(y) ⊆ B_ρ(y)`, so `B_σ(y)`, `U₁ = B_σ(y) ∩ S₁` and `U₂ = B_ρ(y) ∩ S₂` have finite
  -- measure.
  have hρ : 0 < ρ := lt_of_lt_of_le hσ hσρ
  have hfinσ : μ (closedBall y σ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall hσρ))
  have hU₁fin : μ (closedBall y σ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) ≠ ∞ :=
    ne_top_of_le_ne_top hfinσ (measure_mono inter_subset_left)
  have hU₂fin : μ (closedBall y ρ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  -- Step 3: `h` is measurable with `|h| ≤ 1`, hence integrable on every set of finite measure.
  have hint : ∀ s, μ s ≠ ∞ → IntegrableOn h s μ := fun s hs ↦
    Measure.integrableOn_of_bounded hs hmeas.aestronglyMeasurable (M := 1)
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hbd z).1], (hbd z).2⟩)
  -- Step 4: `h = 1` on `U₁` and `h ≥ 0`, so `μ(U₁) = ∫_{U₁} h dμ ≤ ∫_{B_σ(y)} h dμ`.
  have hlow : μ.real (closedBall y σ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) ≤ ∫ z in closedBall y σ, h z ∂μ := by
    have heq : ∫ z in closedBall y σ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}, h z ∂μ =
        μ.real (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) := by
      rw [setIntegral_congr_fun (measurableSet_closedBall.inter hS₁) (g := fun _ ↦ (1 : ℝ))
        (fun z hz ↦ h1 z hz.2)]
      exact setIntegral_one_eq_measureReal
    rw [← heq]
    exact setIntegral_mono_set (hint _ hfinσ) (Eventually.of_forall fun z ↦ (hbd z).1)
      (Eventually.of_forall fun z hz ↦ hz.1)
  -- Step 5: `h = 0` on `B_ρ(y) ∖ S₂` and `h ≤ 1`, so `∫_{B_ρ(y)} h dμ = ∫_{U₂} h dμ ≤ μ(U₂)`.
  have hup : ∫ z in closedBall y ρ, h z ∂μ ≤ μ.real (closedBall y ρ ∩
      {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) := by
    rw [← integral_inter_add_sdiff hS₂ (hint _ hfin)]
    have hzero : ∫ z in closedBall y ρ \
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}, h z ∂μ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ h0 z (not_lt.mp hz.2)
    rw [hzero, add_zero, ← setIntegral_one_eq_measureReal]
    exact setIntegral_mono_on (hint _ hU₂fin) (integrableOn_const hU₂fin)
      (measurableSet_closedBall.inter hS₂) fun z _ ↦ (hbd z).2
  -- Step 6: the real inequality `μ(U₁)/σ^n ≤ μ(U₂)/ρ^n + E`.
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  have hreal : μ.real (closedBall y σ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / σ ^ n ≤
      μ.real (closedBall y ρ ∩
        {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ρ ^ n + E :=
    calc _ ≤ (∫ z in closedBall y σ, h z ∂μ) / σ ^ n := div_le_div_of_nonneg_right hlow hσn.le
      _ ≤ (∫ z in closedBall y ρ, h z ∂μ) / ρ ^ n + E := hineq
      _ ≤ _ := by gcongr
  -- Step 7: for `r > 0` and `μ s < ∞`, `μ s / ofReal r ^ n = ofReal (μ.real s / r ^ n)`; conclude
  -- with monotonicity of `ofReal` and `ofReal (a + E) ≤ ofReal a + ofReal E`.
  have hconv : ∀ (s : Set (Euclidean N)) (r : ℝ), 0 < r → μ s ≠ ∞ →
      μ s / ENNReal.ofReal r ^ n = ENNReal.ofReal (μ.real s / r ^ n) := by
    intro s r hr hs
    rw [ENNReal.ofReal_div_of_pos (pow_pos hr n), ENNReal.ofReal_pow hr.le, measureReal_def,
      ENNReal.ofReal_toReal hs]
  rw [hconv _ σ hσ hU₁fin, hconv _ ρ hρ hU₂fin]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
/-- Differentiation of the radial cutoff mass under the integral sign (step 5 of the weighted
radial monotonicity argument, Simon Ch. 8, §3): if `φ` is `C¹` with `φ = 0` on `[A², ∞)`, `h` is
continuous and `μ(B_R(y)) < ∞`, then for `t₀ > 0` with `t₀ A < R` the map
`t ↦ ∫ φ(|z - y|²/t²) h(z) dμ(z)` has derivative `∫ φ'(|z - y|²/t₀²)(-2|z - y|²/t₀³) h(z) dμ(z)`
at `t₀`. -/
theorem Submission.intcpt_allard_wrm_cutoff_mass_hasDerivAt :
    ∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A R t₀ : ℝ), Continuous h → ContDiff ℝ 1 φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → μ (closedBall y R) ≠ ∞ → 0 < t₀ → t₀ * A < R → HasDerivAt (fun t : ℝ ↦ ∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) (∫ z, deriv φ (‖z - y‖ ^ 2 / t₀ ^ 2) * (-2 * ‖z - y‖ ^ 2 / t₀ ^ 3) * h z ∂μ) t₀ := by
  intro N μ y h φ A R t₀ hh hφ hA hφA hμ ht₀ htR
  -- Step 1: `a := t₀ / 2 < t₀ < b := (t₀ + R / A) / 2` with `b * A < R`; `K := B_R(y)`.
  have hRA : t₀ < R / A := (lt_div_iff₀ hA).2 htR
  obtain ⟨a, b, ha, hat, htb, hbA⟩ : ∃ a b : ℝ, 0 < a ∧ a < t₀ ∧ t₀ < b ∧ b * A < R :=
    ⟨t₀ / 2, (t₀ + R / A) / 2, half_pos ht₀, half_lt_self ht₀, by linarith,
      (lt_div_iff₀ hA).1 (by linarith)⟩
  have hKc : IsCompact (closedBall y R) := isCompact_closedBall y R
  have hKm : MeasurableSet (closedBall y R) := measurableSet_closedBall
  -- Step 2 (i): `φ' = 0` on `(A², ∞)`.
  have hφ'0 : ∀ s, A ^ 2 < s → deriv φ s = 0 := by
    intro s hs
    have hev : φ =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun u hu ↦ hφA u (le_of_lt hu)
    rw [hev.deriv_eq, deriv_const]
  -- Step 2 (ii): for `t ∈ [a, b]` and `z ∉ K`, `‖z - y‖² / t² > A²`.
  have hout : ∀ t, a ≤ t → t ≤ b → ∀ z, z ∉ closedBall y R → A ^ 2 < ‖z - y‖ ^ 2 / t ^ 2 := by
    intro t hat htb z hz
    have ht : 0 < t := lt_of_lt_of_le ha hat
    have hzR : R < ‖z - y‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      exact hz
    have htA : t * A < ‖z - y‖ := by nlinarith
    have hsq : (t * A) ^ 2 < ‖z - y‖ ^ 2 := pow_lt_pow_left₀ htA (by positivity) two_ne_zero
    rw [lt_div_iff₀ (by positivity)]
    linarith [hsq, show (t * A) ^ 2 = A ^ 2 * t ^ 2 by ring]
  -- Step 3: continuity.
  have hFc : ∀ t : ℝ, Continuous fun z : Euclidean N ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z := fun t ↦
    (hφ.continuous.comp (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).mul hh
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hF'c : ContinuousOn (fun p : ℝ × Euclidean N ↦
      deriv φ (‖p.2 - y‖ ^ 2 / p.1 ^ 2) * (-2 * ‖p.2 - y‖ ^ 2 / p.1 ^ 3) * h p.2)
      (Icc a b ×ˢ closedBall y R) := by
    have hne : ∀ p ∈ Icc a b ×ˢ closedBall y R, p.1 ≠ 0 := fun p hp ↦
      (lt_of_lt_of_le ha hp.1.1).ne'
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (hh.comp continuous_snd).continuousOn
    · exact hφ'c.comp_continuousOn
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ pow_ne_zero _ (hne p hp))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ pow_ne_zero _ (hne p hp)
  -- Step 4: domination by `C · 1_K`.
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hKc).exists_bound_of_continuousOn hF'c
  have h_bound : ∀ᵐ z ∂μ, ∀ t ∈ Ioo a b,
      ‖deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z‖ ≤
        (closedBall y R).indicator (fun _ ↦ C) z := by
    refine Eventually.of_forall fun z t ht ↦ ?_
    by_cases hz : z ∈ closedBall y R
    · rw [indicator_of_mem hz]
      exact hC (t, z) ⟨Ioo_subset_Icc_self ht, hz⟩
    · rw [indicator_of_notMem hz, hφ'0 _ (hout t ht.1.le ht.2.le z hz)]
      simp
  have hbound_int : Integrable ((closedBall y R).indicator fun _ ↦ C) μ :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hμ)
  -- Step 5: integrability of `F(t₀, ·)`.
  have hF_int : Integrable (fun z ↦ φ (‖z - y‖ ^ 2 / t₀ ^ 2) * h z) μ := by
    obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn (hFc t₀).continuousOn
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (Measure.integrableOn_of_bounded hμ (hFc t₀).aestronglyMeasurable
        (ae_restrict_of_forall_mem hKm hC₀)) fun z hz ↦ ?_
    rw [hφA _ (hout t₀ hat.le htb.le z hz).le, zero_mul]
  have hF'meas : AEStronglyMeasurable
      (fun z ↦ deriv φ (‖z - y‖ ^ 2 / t₀ ^ 2) * (-2 * ‖z - y‖ ^ 2 / t₀ ^ 3) * h z) μ :=
    ((hφ'c.comp (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).mul
      ((((continuous_id.sub continuous_const).norm.pow 2).const_mul (-2)).div_const _)).mul
      hh |>.aestronglyMeasurable
  -- Step 6: pointwise derivative in `t`.
  have h_diff : ∀ᵐ z ∂μ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z)
        (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z) t := by
    refine Eventually.of_forall fun z t ht ↦ ?_
    have ht0 : t ≠ 0 := (lt_trans ha ht.1).ne'
    have hs : HasDerivAt (fun t ↦ ‖z - y‖ ^ 2 / t ^ 2) (-2 * ‖z - y‖ ^ 2 / t ^ 3) t :=
      ((hasDerivAt_const t (‖z - y‖ ^ 2)).div (hasDerivAt_pow 2 t)
        (pow_ne_zero 2 ht0)).congr_deriv (by field_simp; ring)
    exact ((hφ.differentiable one_ne_zero _).hasDerivAt.comp t hs).mul_const (h z)
  -- Step 7: differentiation under the integral sign on `(a, b) ∋ t₀`.
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z ↦ φ (‖z - y‖ ^ 2 / t ^ 2) * h z)
    (F' := fun t z ↦ deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z)
    (Ioo_mem_nhds hat htb) (Eventually.of_forall fun t ↦ (hFc t).aestronglyMeasurable) hF_int
    hF'meas h_bound hbound_int h_diff).2
/-- Weighted radial first-variation inequality at a fixed radius (Simon Ch. 8, 3.5, with the sign
of `δV(X)` corrected): for `X_t(z) = h(z) φ(|z - y|²/t²) (z - y)`,
`n Ĩ(t) - t J(t) + G(t) ≤ δW(X_t)`, because the dropped normal term is nonnegative (`h ≥ 0`,
`φ' ≤ 0` and `⟨w, p_S w⟩ ≤ |w|²`).  The divergence of `X_t` is supplied by hypothesis (Div). -/
theorem Submission.intcpt_allard_wrm_first_variation_lower_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A t : ℝ), (∀ (a : Euclidean N → ℝ) (c z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - c)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - c))) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z) → ContDiff ℝ 1 φ → Antitone φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → 0 < t → closedBall y (t * A) ⊆ U → (n : ℝ) * (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) - t * (∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) + (∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure) ≤ W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) := by
  intro N n U W y h φ A t hDiv hh hh0 hφ hφa hA hcut ht hU
  -- Step 1: with `s(z) = ‖z - y‖²/t²`, `φ(s(z)) = φ'(s(z)) = 0` off `K = B_{tA}(y)`.
  have hKc : IsCompact (closedBall y (t * A)) := isCompact_closedBall y (t * A)
  have hout : ∀ z : Euclidean N, z ∉ closedBall y (t * A) → A ^ 2 < ‖z - y‖ ^ 2 / t ^ 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos ht hA]
  have hφ0 : ∀ z : Euclidean N, z ∉ closedBall y (t * A) → φ (‖z - y‖ ^ 2 / t ^ 2) = 0 :=
    fun z hz ↦ hcut _ (hout z hz).le
  have hdφ0 : ∀ z : Euclidean N, z ∉ closedBall y (t * A) →
      deriv φ (‖z - y‖ ^ 2 / t ^ 2) = 0 := by
    intro z hz
    have hev : φ =ᶠ[𝓝 (‖z - y‖ ^ 2 / t ^ 2)] fun _ ↦ 0 :=
      (eventually_gt_nhds (hout z hz)).mono fun s hs ↦ hcut s hs.le
    rw [hev.deriv_eq, deriv_const]
  -- Step 2: `s`, `a = h · (φ ∘ s)` and `X_t = a · (· - y)` are `C¹`.
  have hs : ContDiff ℝ 1 (fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2) :=
    ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _
  have ha : ContDiff ℝ 1 (fun z ↦ h z * φ (‖z - y‖ ^ 2 / t ^ 2)) := hh.mul (hφ.comp hs)
  have hX : ContDiff ℝ 1 (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) :=
    ha.smul (contDiff_id.sub contDiff_const)
  -- Step 3: `tsupport X_t ⊆ K ⊆ U`, so `div_S X_t` is `W`-integrable (step 7a).
  have hXK : tsupport (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) ⊆
      closedBall y (t * A) := by
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    by_contra hzK
    exact hz (by simp only [hφ0 z hzK, mul_zero, zero_smul])
  have hdiv := W.integrable_tangentialDivergence _ hX
    (hKc.of_isClosed_subset (isClosed_tsupport _) hXK) (hXK.trans hU)
  -- Step 7: a continuous integrand vanishing off `K × G` is `W`-integrable, as `W(K × G) < ∞`.
  have hint : ∀ F : Euclidean N × Grassmannian N n → ℝ, Continuous F →
      (∀ p : Euclidean N × Grassmannian N n, p.1 ∉ closedBall y (t * A) → F p = 0) →
      Integrable F W.measure := by
    intro F hF hF0
    have hKG : IsCompact (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))) :=
      hKc.prod isCompact_univ
    obtain ⟨C, hC⟩ := hKG.exists_bound_of_continuousOn hF.continuousOn
    have hOn : IntegrableOn F (closedBall y (t * A) ×ˢ univ) W.measure :=
      Measure.integrableOn_of_bounded (W.finite_on_compact _ hKc hU) hF.aestronglyMeasurable
        ((ae_restrict_iff' (isClosed_closedBall.measurableSet.prod MeasurableSet.univ)).mpr
          (Eventually.of_forall hC))
    exact hOn.integrable_of_forall_notMem_eq_zero fun p hp ↦ hF0 p fun h1 ↦ hp ⟨h1, mem_univ _⟩
  have hhc : Continuous h := hh.continuous
  have hφs : Continuous (fun z : Euclidean N ↦ φ (‖z - y‖ ^ 2 / t ^ 2)) :=
    hφ.continuous.comp hs.continuous
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hf1 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) W.measure :=
    hint _ ((hφs.mul hhc).comp continuous_fst) fun p hp ↦ by rw [hφ0 p.1 hp, zero_mul]
  have hf2 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) W.measure :=
    hint _ (by fun_prop) fun p hp ↦ by rw [hdφ0 p.1 hp, zero_mul, zero_mul]
  -- (Div) with `a = h` writes the gradient term through the continuous `div_S (h · (· - y))`.
  have hG : ∀ p : Euclidean N × Grassmannian N n,
      fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) =
        Varifold.tangentialDivergence (fun w ↦ h w • (w - y)) p.1 p.2 - n * h p.1 := fun p ↦ by
    rw [hDiv h y p.1 p.2 (hh.differentiable_one p.1)]
    ring
  have hf3 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)))
      W.measure := by
    refine hint _ ?_ fun p hp ↦ by rw [hφ0 p.1 hp, zero_mul]
    simp_rw [hG]
    exact (hφs.comp continuous_fst).mul
      ((Varifold.continuous_tangentialDivergence (hh.smul (contDiff_id.sub contDiff_const))).sub
        (continuous_const.mul (hhc.comp continuous_fst)))
  -- Steps 4–6: the pointwise inequality `E ≤ div_S X_t`.
  have hpt : ∀ p : Euclidean N × Grassmannian N n,
      (n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
          t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) +
          φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ≤
        Varifold.tangentialDivergence (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))
          p.1 p.2 := by
    rintro ⟨z, S⟩
    dsimp only
    -- Step 2: `Da(z) = h(z) φ'(s) (2/t²) ⟨z - y, ·⟩ + φ(s) Dh(z)`; then (Div) with `c = y`.
    have hg : HasFDerivAt (fun x : Euclidean N ↦ ‖x - y‖ ^ 2)
        (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N))) z :=
      ((hasFDerivAt_id z).sub_const y).norm_sq
    have hη : HasDerivAt (fun r : ℝ ↦ φ (r / t ^ 2))
        (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) (‖z - y‖ ^ 2) :=
      HasDerivAt.comp (h₂ := φ) (h := fun r : ℝ ↦ r / t ^ 2) (‖z - y‖ ^ 2)
        (hφ.differentiable_one _).hasDerivAt ((hasDerivAt_id' _).div_const _)
    have hcomp : HasFDerivAt ((fun r : ℝ ↦ φ (r / t ^ 2)) ∘ fun x : Euclidean N ↦ ‖x - y‖ ^ 2)
        ((deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) •
          (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N)))) z :=
      hη.comp_hasFDerivAt z hg
    have hfd : HasFDerivAt (fun x ↦ h x * φ (‖x - y‖ ^ 2 / t ^ 2))
        (h z • ((deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) •
          (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ (Euclidean N)))) +
          φ (‖z - y‖ ^ 2 / t ^ 2) • fderiv ℝ h z) z :=
      (hh.differentiable_one z).hasFDerivAt.fun_mul hcomp
    rw [hDiv _ y z S (ha.differentiable_one z), hfd.fderiv]
    -- Step 5: `⟨w, p_S w⟩ = ‖p_S w‖² ≤ ‖w‖²` (`p_S` is symmetric and idempotent).
    have hP : inner ℝ (S.project (z - y)) (S.project (z - y)) =
        inner ℝ (z - y) (S.project (z - y)) := by
      rw [show inner ℝ (S.project (z - y)) (S.project (z - y)) =
          inner ℝ (z - y) (S.project (S.project (z - y))) from
        Grassmannian.projectionLinearMap_isSymmetric S (z - y) (S.projectionLinearMap (z - y)),
        Grassmannian.project_project]
    have hip : inner ℝ (z - y) (S.project (z - y)) ≤ ‖z - y‖ ^ 2 := by
      linarith [norm_sub_sq_real (z - y) (S.project (z - y)),
        real_inner_self_eq_norm_sq (S.project (z - y)), sq_nonneg ‖z - y - S.project (z - y)‖]
    -- Step 6: `div_S X_t - E = (2/t²) h(z) (-φ'(s)) (‖w‖² - ⟨w, p_S w⟩) ≥ 0`.
    have hnn : 0 ≤ h z * -deriv φ (‖z - y‖ ^ 2 / t ^ 2) *
        (‖z - y‖ ^ 2 - inner ℝ (z - y) (S.project (z - y))) / t ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (hh0 z) (neg_nonneg.mpr hφa.deriv_nonpos))
        (sub_nonneg.mpr hip)) (by positivity)
    have ht3 : t * (deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z) =
        deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 2) * h z := by
      field_simp
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    rw [ht3, ← sub_nonneg]
    convert mul_nonneg zero_le_two hnn using 1
    ring
  -- Steps 8–9: integrate (`μ_W = π_# W` for the first two integrals) and use `integral_mono`.
  have hw1 : ∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight =
      ∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1 ∂W.measure :=
    integral_map measurable_fst.aemeasurable (hφs.mul hhc).aestronglyMeasurable
  have hw2 : ∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight =
      ∫ p, deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1 ∂W.measure :=
    integral_map measurable_fst.aemeasurable (by fun_prop : Continuous fun z : Euclidean N ↦
      deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z).aestronglyMeasurable
  have hf12 : Integrable (fun p : Euclidean N × Grassmannian N n ↦
      (n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
        t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1)) W.measure :=
    (hf1.const_mul _).sub (hf2.const_mul _)
  calc _ = ∫ p, ((n : ℝ) * (φ (‖p.1 - y‖ ^ 2 / t ^ 2) * h p.1) -
          t * (deriv φ (‖p.1 - y‖ ^ 2 / t ^ 2) * (-2 * ‖p.1 - y‖ ^ 2 / t ^ 3) * h p.1) +
          φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)))
          ∂W.measure := by
        rw [integral_add hf12 hf3, integral_sub (hf1.const_mul _) (hf2.const_mul _),
          integral_const_mul, integral_const_mul, hw1, hw2]
    _ ≤ _ := integral_mono (hf12.add hf3) hdiv hpt
/-- The gradient term `G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)` of the weighted radial
monotonicity argument (Simon Ch. 8, 3.3–3.5; tilt-excess estimate) satisfies
`|G(t)| ≤ M A^{n+1} ε t^{n+1}`: off `B_{tA}(y) × G(N,n)` the cutoff vanishes, on it the integrand is
at most `M (tA) ‖p_S - p_P‖`, and the tilt-excess hypothesis bounds the integral of `‖p_S - p_P‖`. -/
theorem Submission.intcpt_allard_wrm_gradient_term_bound :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε M A t : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), 0 ≤ ε → 0 ≤ M → 0 < A → 0 < t → (∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * (t * A) ^ n) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → (∀ s, A ^ 2 ≤ s → φ s = 0) → |∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure| ≤ M * A ^ (n + 1) * ε * t ^ (n + 1) := by
  intro N n U W P y ε M A t h φ hε hM hA ht htilt hgrad hφ hφA
  have htA : 0 < t * A := mul_pos ht hA
  have hMtA : 0 ≤ M * (t * A) := mul_nonneg hM htA.le
  -- Step 1: pointwise, `|g| ≤ 1_K · M (tA) ‖p_S - p_P‖` with `K = B_{tA}(y) × G(N,n)`.
  have hpt : ∀ p : Euclidean N × Grassmannian N n,
      ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
          fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ≤
        (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))).indicator
          (fun z ↦ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖) p := by
    intro p
    by_cases hp : p ∈ closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))
    · -- On `K`: `|φ| ≤ 1` and (grad) with `|z - y| ≤ tA`.
      rw [Set.indicator_of_mem hp, ← ENNReal.ofReal_mul hMtA]
      apply ENNReal.ofReal_le_ofReal
      have hdist : ‖p.1 - y‖ ≤ t * A := by
        have h1 := hp.1
        rwa [mem_closedBall, dist_eq_norm] at h1
      have hφ1 : |φ (‖p.1 - y‖ ^ 2 / t ^ 2)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hφ (‖p.1 - y‖ ^ 2 / t ^ 2)]
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ (‖p.1 - y‖ ^ 2 / t ^ 2)| * |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))|
          ≤ 1 * |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))| :=
            mul_le_mul_of_nonneg_right hφ1 (abs_nonneg _)
        _ = |fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))| := one_mul _
        _ ≤ M * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ *
              ‖p.1 - y‖ := hgrad p.1 p.2
        _ ≤ M * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ *
              (t * A) := mul_le_mul_of_nonneg_left hdist (mul_nonneg hM (norm_nonneg _))
        _ = M * (t * A) * ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap p.2 - Grassmannian.projectionLinearMap P)‖ := by
            ring
    · -- Off `K`: `|z - y| > tA`, so `|z - y|²/t² > A²` and the cutoff vanishes.
      rw [Set.indicator_of_notMem hp]
      have hdist : t * A < ‖p.1 - y‖ := by
        have h1 : p.1 ∉ closedBall y (t * A) := fun h1 ↦ hp ⟨h1, mem_univ _⟩
        rwa [mem_closedBall, dist_eq_norm, not_le] at h1
      have hs : A ^ 2 ≤ ‖p.1 - y‖ ^ 2 / t ^ 2 := by
        rw [le_div_iff₀ (pow_pos ht 2)]
        calc A ^ 2 * t ^ 2 = (t * A) ^ 2 := by ring
          _ ≤ ‖p.1 - y‖ ^ 2 := pow_le_pow_left₀ htA.le hdist.le 2
      rw [hφA _ hs, zero_mul, norm_zero, ENNReal.ofReal_zero]
  -- Step 2: `∫⁻ |g| ≤ ofReal (M tA) · ∫⁻_K ‖p_S - p_P‖ ≤ ofReal (M tA · ε (tA)^n)`.
  have hlint : ∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure ≤
      ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n)) := by
    calc ∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
          fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure
        ≤ ∫⁻ p, (closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n))).indicator
          (fun z ↦ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖) p
            ∂W.measure := lintegral_mono hpt
      _ ≤ ∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)),
          ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal
            ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
            ∂W.measure := lintegral_indicator_le _ _
      _ = ENNReal.ofReal (M * (t * A)) *
          ∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)),
            ENNReal.ofReal ‖LinearMap.toContinuousLinearMap
              (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖
            ∂W.measure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * (t * A)) * ENNReal.ofReal (ε * (t * A) ^ n) := by gcongr
      _ = ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n)) :=
          (ENNReal.ofReal_mul hMtA).symm
  -- Step 3: `|∫ g| ≤ (∫⁻ |g|).toReal ≤ M tA · ε (tA)^n = M A^{n+1} ε t^{n+1}`.
  calc |∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure|
      = ‖∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ p, ENNReal.ofReal ‖φ (‖p.1 - y‖ ^ 2 / t ^ 2) *
        fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y))‖ ∂W.measure).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (M * (t * A) * (ε * (t * A) ^ n))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = M * (t * A) * (ε * (t * A) ^ n) :=
        ENNReal.toReal_ofReal (mul_nonneg hMtA (mul_nonneg hε (pow_nonneg htA.le n)))
    _ = M * A ^ (n + 1) * ε * t ^ (n + 1) := by ring
/-- **Simon Ch. 8, 2.5–2.6, as used in the proof of 5.10 (printed (7))** (child
`first_variation_bound` of `allard_lemma`): if `W` has locally bounded first variation, `K ⊆ U` is
compact and `X` is a `C¹` field with `spt X ⊆ K` and `|X| ≤ B`, then `|δW(X)| ≤ B ‖δW‖(K)`.
Write `δW(X) = -∫ ν·X d‖δW‖` with `|ν| = 1` `‖δW‖`-a.e. (2.6); the integrand is bounded by `B`
on `K` and vanishes off `K`. -/
theorem Submission.intcpt_allard_first_variation_le_sup_mul :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (X : Euclidean N → Euclidean N) (K : Set (Euclidean N)) (B : ℝ), W.HasLocallyBoundedFirstVariation → ContDiff ℝ 1 X → IsCompact K → K ⊆ U → tsupport X ⊆ K → (∀ z, ‖X z‖ ≤ B) → ENNReal.ofReal |W.firstVariation X| ≤ ENNReal.ofReal B * variationMeasure W K := by
  intro N n U W X K B hW hX hK hKU hXK hXB
  -- `X` is a test field of `U`: `C¹`, with compact support `spt X ⊆ K ⊆ U`.
  let T : Varifold.TestVectorField U :=
    ⟨X, hX, hK.of_isClosed_subset (isClosed_tsupport X) hXK, hXK.trans hKU⟩
  -- `‖δW‖` is the Riesz measure `μ`, with polar field `ν`, `|ν| = 1` `μ`-a.e. (2.6).
  have hμ : variationMeasure W = W.firstVariationRieszMeasure hW := by
    simp only [variationMeasure, dite_eq_left hW]
  set μ := W.firstVariationRieszMeasure hW
  set ν := W.firstVariationPolarField hW
  have hrep : W.IsFirstVariationPolarRepresentation μ ν :=
    W.isFirstVariationPolarRepresentation_riesz hW
  have hfv : W.firstVariation X = -∫ x, inner ℝ (ν x) (X x) ∂μ := (hrep.2.2 T).2
  rw [hμ, hfv, abs_neg, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ x, inner ℝ (ν x) (X x) ∂μ‖ₑ ≤ ∫⁻ x, ‖inner ℝ (ν x) (X x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator (fun _ ↦ ENNReal.ofReal B) x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hrep.2.1] with x hx
        by_cases hxK : x ∈ K
        · -- On `K`: `|ν·X| ≤ |ν| |X| = |X| ≤ B`.
          rw [indicator_of_mem hxK, Real.enorm_eq_ofReal_abs]
          apply ENNReal.ofReal_le_ofReal
          have hb := norm_inner_le_norm (𝕜 := ℝ) (ν x) (X x)
          rw [Real.norm_eq_abs, hx, one_mul] at hb
          exact hb.trans (hXB x)
        · -- Off `K ⊇ spt X` the field vanishes.
          have hz : X x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hxK (hXK h)
          simp only [hz, inner_zero_right, enorm_zero, indicator_of_notMem hxK, le_refl]
    _ = ENNReal.ofReal B * μ K := lintegral_indicator_const hK.measurableSet _
/-- The tangential divergence of the radial-type field `Y(w) = a(w) (w - y)` (the pointwise
computation behind Simon Ch. 8, 3.2–3.5): if `a` is differentiable at `z`, then
`div_S Y(z) = n a(z) + Da(z)[p_S(z - y)]`, via `DY(z) = a(z) id + Da(z) ⊗ (z - y)`,
`div_S Y(z) = trace (p_S ∘ DY(z))`, `trace p_S = n` and `trace (ℓ ⊗ u) = ℓ(u)`. -/
theorem Submission.intcpt_allard_radial_field_divergence :
    ∀ (N n : ℕ) (a : Euclidean N → ℝ) (y z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - y)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - y)) := by
  intro N n a y z S ha
  -- Step 1: the product rule, `DY(z) = a(z) • id + Da(z).smulRight (z - y)`.
  have hD : fderiv ℝ (fun w ↦ a w • (w - y)) z =
      a z • ContinuousLinearMap.id ℝ (Euclidean N) + (fderiv ℝ a z).smulRight (z - y) := by
    have hsub : DifferentiableAt ℝ (fun w : Euclidean N ↦ w - y) z :=
      differentiableAt_fun_id.sub_const y
    rw [fderiv_fun_smul ha hsub, fderiv_sub_const, fderiv_fun_id]
  -- Step 2: `div_S Y(z) = trace (S.1 * jacobian Y z) = trace (p_S ∘ DY(z))`, since `S.1` and
  -- `jacobian Y z` are the matrices of `p_S` and `DY(z)` in the standard basis.
  have htr : Varifold.tangentialDivergence (fun w ↦ a w • (w - y)) z S =
      LinearMap.trace ℝ (Euclidean N)
        (S.projectionLinearMap ∘ₗ (fderiv ℝ (fun w ↦ a w • (w - y)) z).toLinearMap) := by
    rw [Varifold.tangentialDivergence, LinearMap.trace_eq_matrix_trace ℝ
      Grassmannian.coordinateBasis.toBasis, LinearMap.toMatrix_comp
      Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis, Grassmannian.toMatrix_projectionLinearMap,
      Varifold.jacobian_eq_toMatrix]
  -- Step 3: `p_S ∘ DY(z) = a(z) • p_S + Da(z).smulRight (p_S (z - y))`.
  have hcomp : S.projectionLinearMap ∘ₗ (fderiv ℝ (fun w ↦ a w • (w - y)) z).toLinearMap =
      a z • S.projectionLinearMap +
        (fderiv ℝ a z).toLinearMap.smulRight (Grassmannian.project S (z - y)) := by
    ext v
    simp [hD, Grassmannian.project]
  -- Step 4: `trace p_S = trace S.1 = n` and `trace (ℓ.smulRight u) = ℓ u`.
  have hP : LinearMap.trace ℝ (Euclidean N) S.projectionLinearMap = n := by
    rw [LinearMap.trace_eq_matrix_trace ℝ Grassmannian.coordinateBasis.toBasis,
      Grassmannian.toMatrix_projectionLinearMap, Grassmannian.trace_eq]
  rw [htr, hcomp, map_add, map_smul, hP, LinearMap.trace_smulRight, smul_eq_mul, mul_comm,
    ContinuousLinearMap.coe_coe]

/-- Integrated weighted monotonicity (Simon Ch. 8, 3.5 integrated from `σ` to `ρ`, as for (6)–(7)
in the proof of 5.10): if (1r)–(3r) hold on `B_r(y)` for `0 < r < 1`, then for `0 < σ ≤ ρ` with
`ρA < 1` and `Ĩ(t) = ∫ φ(|z - y|²/t²) h(z) dμ_W(z)`, `Ĩ(σ)/σ^n ≤ Ĩ(ρ)/ρ^n + 2^{n+1}(M + K)ερ`.
For `t ∈ [σ, ρ]`, `tĨ'(t) - nĨ(t) ≥ G(t) - δW(X_t)`, where `X_t(z) = h(z)φ(|z - y|²/t²)(z - y)` and
`G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)`, and
`|G(t)| + |δW(X_t)| ≤ A^{n+1}(M + K)εt^{n+1}`; so `t ↦ Ĩ(t)/t^n + 2^{n+1}(M + K)εt` is
nondecreasing on `[σ, ρ]`. -/
theorem Submission.intcpt_allard_weighted_radial_monotonicity :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K M A : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → 0 ≤ M → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → ContDiff ℝ 1 φ → Antitone φ → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → 0 < A → A ≤ 2 → (∀ s, A ^ 2 ≤ s → φ s = 0) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ * A < 1 → (∫ z, φ (‖z - y‖ ^ 2 / σ ^ 2) * h z ∂W.weight) / σ ^ n ≤ (∫ z, φ (‖z - y‖ ^ 2 / ρ ^ 2) * h z ∂W.weight) / ρ ^ n + 2 ^ (n + 1) * (M + K) * ε * ρ := by
  intro N n U W P y ε K M A h φ hW hU hε hK hM hvar htilt hmass hh hh01 hDh hφ hφanti hφ01 hA
    hA2 hφA σ ρ hσ hσρ hρA
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 ^ (n + 1) * (M + K) * ε := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; exact mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (add_nonneg hM hK)) hε.le
  -- Step 2: a radius `R` with `ρA < R < 1`, so `B_R(y) ⊆ B°_1(y) ⊆ U` has finite `μ_W`-mass.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (ρ * A + 1) / 2 := ⟨_, rfl⟩
  have hρAR : ρ * A < R := by rw [hR]; linarith
  have hRfin : W.weight (closedBall y R) ≠ ∞ :=
    W.weight_finite_on_compact _ (isCompact_closedBall y R)
      ((closedBall_subset_ball (by rw [hR]; linarith)).trans hU)
  -- Steps 3–7: for `t ∈ [σ, ρ]`, `tĨ'(t) - nĨ(t) ≥ G(t) - δW(X_t) ≥ -2^{n+1}(M + K)εt^{n+1}`.
  have key : ∀ t, σ ≤ t → t ≤ ρ →
      -(C * t ^ (n + 1)) ≤
        t * (∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) -
          n * (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) := by
    intro t hσt htρ
    have ht0 : 0 < t := hσ.trans_le hσt
    have htA0 : 0 < t * A := mul_pos ht0 hA
    have htA1 : t * A < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right htρ hA.le) hρA
    have hball : closedBall y (t * A) ⊆ U := (closedBall_subset_ball htA1).trans hU
    -- The weighted radial inequality (Simon 8.3.5 with the normal term dropped).
    have hlow := Submission.intcpt_allard_wrm_first_variation_lower_bound N n U W y h φ A t
      (Submission.intcpt_allard_radial_field_divergence N n) hh (fun z ↦ (hh01 z).1) hφ hφanti
      hA hφA ht0 hball
    -- (b): `|G(t)| ≤ M A^{n+1} ε t^{n+1}`, from (2r) at radius `tA`.
    have hgrad := Submission.intcpt_allard_wrm_gradient_term_bound N n U W P y ε M A t h φ hε.le
      hM hA ht0 (htilt (t * A) htA0 htA1) hDh hφ01 hφA
    -- (a): `|δW(X_t)| ≤ K A^{n+1} ε t^{n+1}`, from (1r) and (3r) at radius `tA`.
    have hvanish : ∀ z : Euclidean N, t * A ≤ ‖z - y‖ → φ (‖z - y‖ ^ 2 / t ^ 2) = 0 := by
      intro z hz
      apply hφA
      rw [le_div_iff₀ (pow_pos ht0 2)]
      calc A ^ 2 * t ^ 2 = (t * A) ^ 2 := by ring
        _ ≤ ‖z - y‖ ^ 2 := pow_le_pow_left₀ htA0.le hz 2
    have hX1 : ContDiff ℝ 1 (fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) := by
      have hsq : ContDiff ℝ 1 (fun z : Euclidean N ↦ ‖z - y‖ ^ 2 / t ^ 2) :=
        ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _
      exact (hh.mul (hφ.comp hsq)).smul (contDiff_id.sub contDiff_const)
    have hsupp : tsupport (fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) ⊆
        closedBall y (t * A) := by
      refine closure_minimal ?_ isClosed_closedBall
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      by_contra hlt
      exact hz (by simp [hvanish z (not_le.mp hlt).le])
    have hbound : ∀ z, ‖(fun z : Euclidean N ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) z‖ ≤
        t * A := by
      intro z
      by_cases hz : t * A ≤ ‖z - y‖
      · simp [hvanish z hz, htA0.le]
      · have h1 : |h z * φ (‖z - y‖ ^ 2 / t ^ 2)| ≤ 1 := by
          rw [abs_of_nonneg (mul_nonneg (hh01 z).1 (hφ01 _).1)]
          calc h z * φ (‖z - y‖ ^ 2 / t ^ 2) ≤ 1 * 1 :=
                mul_le_mul (hh01 z).2 (hφ01 _).2 (hφ01 _).1 zero_le_one
            _ = 1 := one_mul 1
        show ‖(h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)‖ ≤ t * A
        rw [norm_smul, Real.norm_eq_abs]
        calc |h z * φ (‖z - y‖ ^ 2 / t ^ 2)| * ‖z - y‖ ≤ 1 * (t * A) :=
              mul_le_mul h1 (not_le.mp hz).le (norm_nonneg _) zero_le_one
          _ = t * A := one_mul _
    have hδ : |W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))| ≤
        K * A ^ (n + 1) * ε * t ^ (n + 1) := by
      have hfv := Submission.intcpt_allard_first_variation_le_sup_mul N n U W
        (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y)) (closedBall y (t * A)) (t * A) hW hX1
        (isCompact_closedBall y (t * A)) hball hsupp hbound
      have hchain : ENNReal.ofReal |W.firstVariation
          (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))| ≤
          ENNReal.ofReal (t * A * (ε * (K * (t * A) ^ n))) := by
        calc ENNReal.ofReal |W.firstVariation
              (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))|
            ≤ ENNReal.ofReal (t * A) * variationMeasure W (closedBall y (t * A)) := hfv
          _ ≤ ENNReal.ofReal (t * A) * (ENNReal.ofReal ε * W.weight (closedBall y (t * A))) :=
            mul_le_mul_of_nonneg_left (hvar (t * A) htA0 htA1) zero_le
          _ ≤ ENNReal.ofReal (t * A) * (ENNReal.ofReal ε * ENNReal.ofReal (K * (t * A) ^ n)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hmass (t * A) htA0 htA1) zero_le) zero_le
          _ = ENNReal.ofReal (t * A * (ε * (K * (t * A) ^ n))) := by
            rw [ENNReal.ofReal_mul htA0.le, ENNReal.ofReal_mul hε.le]
      calc |W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))|
          ≤ t * A * (ε * (K * (t * A) ^ n)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg htA0.le (mul_nonneg hε.le
              (mul_nonneg hK (pow_nonneg htA0.le n))))).mp hchain
        _ = K * A ^ (n + 1) * ε * t ^ (n + 1) := by ring
    -- (c): combine, using `A^{n+1} ≤ 2^{n+1}`.
    have hA' : (M + K) * ε * t ^ (n + 1) * A ^ (n + 1) ≤
        (M + K) * ε * t ^ (n + 1) * 2 ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hA2 (n + 1))
        (mul_nonneg (mul_nonneg (add_nonneg hM hK) hε.le) (pow_nonneg ht0.le _))
    have hG := (abs_le.mp hgrad).1
    have hδ' := (abs_le.mp hδ).2
    rw [hC]
    linarith
  -- The derivative of `F(t) = Ĩ(t)/t^n + Ct` is `(tĨ'(t) - nĨ(t))/t^{n+1} + C ≥ 0`.
  have alg : ∀ t I J : ℝ, 0 < t → -(C * t ^ (n + 1)) ≤ t * J - n * I →
      0 ≤ (J * t ^ n - I * (n * t ^ (n - 1))) / (t ^ n) ^ 2 + C * 1 := by
    intro t I J ht0 hk
    have hpow : ∀ m : ℕ, (m : ℝ) * t ^ (m - 1) * t = m * t ^ m := by
      intro m
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        ring
    have htn : 0 < t ^ n := pow_pos ht0 n
    have h1 : t ^ n * (-(C * t ^ (n + 1))) ≤ t ^ n * (t * J - n * I) :=
      mul_le_mul_of_nonneg_left hk htn.le
    have h2 : -C * (t ^ n) ^ 2 * t ≤ (J * t ^ n - I * (n * t ^ (n - 1))) * t := by
      have e1 : -C * (t ^ n) ^ 2 * t = t ^ n * (-(C * t ^ (n + 1))) := by ring
      have e2 : (J * t ^ n - I * (n * t ^ (n - 1))) * t = t ^ n * (t * J - n * I) := by
        calc (J * t ^ n - I * (n * t ^ (n - 1))) * t =
            J * t ^ n * t - I * ((n : ℝ) * t ^ (n - 1) * t) := by ring
          _ = t ^ n * (t * J - n * I) := by rw [hpow n]; ring
      rw [e1, e2]
      exact h1
    have h3 : -C ≤ (J * t ^ n - I * (n * t ^ (n - 1))) / (t ^ n) ^ 2 := by
      rw [le_div_iff₀ (pow_pos htn 2)]
      exact le_of_mul_le_mul_right h2 ht0
    linarith
  -- Step 5: `Ĩ` is differentiable on `[σ, ρ]`, hence so is `F`.
  have hderiv : ∀ t, σ ≤ t → t ≤ ρ →
      HasDerivAt (fun s ↦ (∫ z, φ (‖z - y‖ ^ 2 / s ^ 2) * h z ∂W.weight) / s ^ n + C * s)
        (((∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) *
            t ^ n - (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) * (n * t ^ (n - 1))) /
          (t ^ n) ^ 2 + C * 1) t := by
    intro t hσt htρ
    have ht0 : 0 < t := hσ.trans_le hσt
    have hI := Submission.intcpt_allard_wrm_cutoff_mass_hasDerivAt N W.weight y h φ A R t
      hh.continuous hφ hA hφA hRfin ht0
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right htρ hA.le) hρAR)
    exact (hI.div (hasDerivAt_pow n t) (pow_ne_zero n ht0.ne')).add
      ((hasDerivAt_id' t).const_mul C)
  -- Step 8: `F` is monotone on `[σ, ρ]`, so `F(σ) ≤ F(ρ)`.
  have hmono : MonotoneOn
      (fun s ↦ (∫ z, φ (‖z - y‖ ^ 2 / s ^ 2) * h z ∂W.weight) / s ^ n + C * s) (Icc σ ρ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc σ ρ)
      (fun t ht ↦ (hderiv t ht.1 ht.2).continuousAt.continuousWithinAt) (fun t ht ↦ ?_)
      (fun t ht ↦ ?_)
    · rw [interior_Icc] at ht
      exact (hderiv t ht.1.le ht.2.le).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hderiv t ht.1.le ht.2.le).deriv]
      exact alg t _ _ (hσ.trans ht.1) (key t ht.1.le ht.2.le)
  have hF := hmono ⟨le_rfl, hσρ⟩ ⟨hσρ, le_rfl⟩ hσρ
  have hCσ : 0 ≤ C * σ := mul_nonneg hC0 hσ.le
  simp only at hF
  rw [← hC]
  linarith

/-- Cylinder monotonicity (Simon Ch. 8, (7) in the proof of 5.10, "proved by simply integrating
3.5"): under (1r)–(3r) on `B_r(y)` for `0 < r < 1`, for `0 < τ ≤ 1` and `0 < σ ≤ ρ < 1`,
`μ_W(U^τ_σ(y))/σ^n ≤ μ_W(U^{2τ}_ρ(y))/ρ^n + C(1 + K)ερ/τ` with `C = 2^{n+1}(M₀ + 1)`, where
`U^τ_r(y) = B_r(y) ∩ {z : |q(z - y)| < τ}` and `q = id - p_P`.  The integrated weighted
monotonicity is applied to a cylindrical weight `h` (`1` where `|q(z - y)| < τ`, `0` where
`|q(z - y)| ≥ 2τ`, `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ)|p_S - p_P||z - y|`) and radial cutoffs `φ_j` with
`A_j ↓ 1`; letting `j → ∞` gives the inequality for `∫_{B_t(y)} h dμ_W`, which bounds the
cylinder masses. -/
theorem Submission.intcpt_allard_cylinder_monotonicity :
    ∀ (N n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → W.weight (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ W.weight (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (C * (1 + K) * ε * ρ / τ) := by
  intro N n
  -- Step 0: `C = 2^{n+1}(M₀ + 1)`, where `M₀/τ` is the gradient constant of the cylindrical weight.
  obtain ⟨M₀, hM₀, hweight⟩ := Submission.intcpt_allard_cm_cylinder_weight
  refine ⟨2 ^ (n + 1) * (M₀ + 1), mul_nonneg (pow_nonneg zero_le_two _) (by linarith), ?_⟩
  intro U W P y ε K hW hU hε hK hvar htilt hmass τ σ ρ hτ hτ1 hσ hσρ hρ
  have hρ0 : 0 < ρ := hσ.trans_le hσρ
  -- Step 2: the cylindrical weight `h`.
  obtain ⟨h, hh, hh01, hh1, hh0, hDh⟩ := hweight N n P y τ hτ
  have hhm : Measurable h := hh.continuous.measurable
  -- Step 1: `A_j = 1 + (1 - ρ)/(2(j + 1)) ↓ 1`, with `A_j ≤ 2` and `ρA_j ≤ R := (1 + ρ)/2 < 1`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hR1 : R < 1 := by rw [hR]; linarith
  obtain ⟨A, hA1, hA2, hρA, hAlim⟩ : ∃ A : ℕ → ℝ, (∀ j, 1 < A j) ∧ (∀ j, A j ≤ 2) ∧
      (∀ j, ρ * A j ≤ R) ∧ Tendsto A atTop (𝓝 1) := by
    have hx : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) ∧ 1 / ((j : ℝ) + 1) ≤ 1 := fun j ↦
      ⟨by positivity, (div_le_one₀ (by positivity)).2 (by linarith [j.cast_nonneg (α := ℝ)])⟩
    refine ⟨fun j ↦ 1 + (1 - ρ) / 2 * (1 / ((j : ℝ) + 1)), fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
    · nlinarith [mul_pos (sub_pos.2 hρ) (hx j).1]
    · nlinarith [mul_nonneg hρ0.le (hx j).1.le, (hx j).2]
    · rw [hR]
      nlinarith [mul_nonneg (sub_nonneg.2 hρ.le) (sub_nonneg.2 hρ.le),
        mul_nonneg (mul_nonneg hρ0.le (sub_nonneg.2 hρ.le)) (sub_nonneg.2 (hx j).2)]
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((1 - ρ) / 2)).const_add 1
  have hA0 : ∀ j, 0 < A j := fun j ↦ zero_lt_one.trans (hA1 j)
  -- The radial cutoffs `φ_j`: `1` on `(-∞, 1]`, `0` on `[A_j², ∞)`.
  choose φ hφ hφanti hφ01 hφ1 hφ0 using fun j ↦
    Submission.intcpt_allard_cm_radial_cutoff (A j) (hA1 j)
  -- Step 3: for each `j`, the integrated weighted monotonicity with `M = M₀/τ`.
  have hj : ∀ j, (∫ z, φ j (‖z - y‖ ^ 2 / σ ^ 2) * h z ∂W.weight) / σ ^ n ≤
      (∫ z, φ j (‖z - y‖ ^ 2 / ρ ^ 2) * h z ∂W.weight) / ρ ^ n +
        2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ := fun j ↦
    Submission.intcpt_allard_weighted_radial_monotonicity N n U W P y ε K (M₀ / τ) (A j) h (φ j)
      hW hU hε hK (div_nonneg hM₀ hτ.le) hvar htilt hmass hh hh01 hDh (hφ j) (hφanti j) (hφ01 j)
      (hA0 j) (hA2 j) (hφ0 j) σ ρ hσ hσρ ((hρA j).trans_lt hR1)
  -- Step 4: let `j → ∞`; `B_R(y) ⊆ B°_1(y) ⊆ U` is compact, so `μ_W(B_R(y)) < ∞`.
  have hRfin : W.weight (closedBall y R) ≠ ∞ :=
    W.weight_finite_on_compact _ (isCompact_closedBall y R) ((closedBall_subset_ball hR1).trans hU)
  have hlim : ∀ t, 0 < t → t ≤ ρ →
      Tendsto (fun j ↦ ∫ z, φ j (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) atTop
        (𝓝 (∫ z in closedBall y t, h z ∂W.weight)) := fun t ht htρ ↦
    Submission.intcpt_allard_cm_cutoff_integral_tendsto N W.weight y h φ A t R hhm hh01
      (fun j ↦ (hφ j).continuous.measurable) hφ01 hφ1 hφ0 hA0 hAlim ht
      (fun j ↦ (mul_le_mul_of_nonneg_right htρ (hA0 j).le).trans (hρA j)) hRfin
  have hI : (∫ z in closedBall y σ, h z ∂W.weight) / σ ^ n ≤
      (∫ z in closedBall y ρ, h z ∂W.weight) / ρ ^ n + 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ :=
    le_of_tendsto_of_tendsto' ((hlim σ hσ hσρ).div_const _)
      (((hlim ρ hρ0 le_rfl).div_const _).add_const _) hj
  -- `2^{n+1}(M₀/τ + K)ερ ≤ C(1 + K)ερ/τ`, since `τ ≤ 1` gives `M₀ + Kτ ≤ (M₀ + 1)(1 + K)`.
  have hMK : M₀ / τ + K ≤ (M₀ + 1) * (1 + K) / τ := by
    rw [div_add' _ _ _ hτ.ne', div_le_div_iff_of_pos_right hτ]
    nlinarith [mul_nonneg hM₀ hK, mul_nonneg hK (sub_nonneg.2 hτ1)]
  have hE : 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ ≤
      2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ :=
    calc 2 ^ (n + 1) * (M₀ / τ + K) * ε * ρ = 2 ^ (n + 1) * ε * ρ * (M₀ / τ + K) := by ring
      _ ≤ 2 ^ (n + 1) * ε * ρ * ((M₀ + 1) * (1 + K) / τ) :=
        mul_le_mul_of_nonneg_left hMK (mul_pos (mul_pos (pow_pos two_pos _) hε) hρ0).le
      _ = 2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ := by ring
  -- Step 5: compare the ball integrals of `h` with the cylinder masses.
  exact Submission.intcpt_allard_cm_cylinder_mass_bound N n W.weight P y h τ σ ρ
    (2 ^ (n + 1) * (M₀ + 1) * (1 + K) * ε * ρ / τ) hhm hh01 hh1 hh0 hσ hσρ
    (W.weight_finite_on_compact _ (isCompact_closedBall y ρ) ((closedBall_subset_ball hρ).trans hU))
    (by linarith)

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
