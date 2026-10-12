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

/-- Simon Ch. 8, Definition 1.1 tested on a product function: if `V` has tangent plane `T` with
multiplicity `θ` at `x`, then for `g ∈ C_c(ℝ^N)` and continuous `β` on `G(N,n)`,
`t^{-n} ∫ g(t⁻¹(y - x)) β(S) dV(y,S) → θ β(T) ∫_T g dH^n` as `t ↓ 0` (the test function is
`f(y,S) = g(y) β(S)`; used for the tangent-ball averages in the proof of 1.2). -/
theorem Submission.frt_vgm_tba_product_blowup_tendsto :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ (g : C_c(Euclidean N, ℝ)) (β : C(Grassmannian N n, ℝ)), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z.1 - x)) * β z.2 ∂V.measure) (𝓝[>] 0) (𝓝 (θ * (β T * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))) := by
  intro N n U V x T θ hT g β
  -- Step 1: the product test function `f(y,S) = g(y) β(S)` lies in `C_c(ℝ^N × G(N,n))`: it is
  -- continuous and vanishes off the compact set `tsupport g × G(N,n)`.
  have hcont : Continuous (fun z : Euclidean N × Grassmannian N n ↦ g z.1 * β z.2) :=
    (g.continuous.comp continuous_fst).mul (β.continuous.comp continuous_snd)
  have hsupp : HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦ g z.1 * β z.2) := by
    refine HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod isCompact_univ) ?_
    intro z hz
    have hz1 : z.1 ∉ tsupport g := fun h ↦ hz ⟨h, mem_univ _⟩
    simp [image_eq_zero_of_notMem_tsupport hz1]
  let f : C_c(Euclidean N × Grassmannian N n, ℝ) := ⟨⟨_, hcont⟩, hsupp⟩
  -- Step 2: Def. 1.1 applied to `f`.
  have h := hT.2.2 f
  -- Step 3: the plane side, `∫ f dv(T) = β(T) ∫_T g dH^n`.
  have hplane : ∫ z, f z ∂(planeVarifoldMeasure T) =
      β T * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] := by
    rw [planeVarifoldMeasure, integral_map (φ := fun y : Euclidean N ↦ (y, T))
      (continuous_id.prodMk continuous_const).aemeasurable (map_continuous f).aestronglyMeasurable]
    change ∫ y in (T.plane : Set (Euclidean N)), g y * β T ∂μHE[n] = _
    rw [integral_mul_const, mul_comm]
  -- Step 4: the rescaled side, `∫ f dV_{x,t} = t^{-n} ∫ g(t⁻¹(y - x)) β(S) dV` for `t > 0`.
  have hresc : ∀ t ∈ Ioi (0 : ℝ), ∫ z, f z ∂(rescaledMeasure V x t) =
      t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z.1 - x)) * β z.2 ∂V.measure := by
    intro t ht
    rw [rescaledMeasure, integral_smul_measure,
      integral_map (φ := fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2))
        (show Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - x), z.2)) by
          fun_prop).aemeasurable (map_continuous f).aestronglyMeasurable,
      ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (mem_Ioi.mp ht).le) n), smul_eq_mul]
    rfl
  -- Step 5: the two sides agree on `(0, ∞) ∈ 𝓝[>] 0`, so the limit transfers.
  rw [hplane] at h
  exact h.congr' (eventually_nhdsWithin_of_forall hresc)
/-- The cut-off sandwich for a ball (steps 2 and 7 of the tangent-ball average used for Simon
Ch. 8, 1.2): with `χ⁻ = max(0, min(1, (1 - |w|)/κ))`, `χ⁺ = max(0, min(1, (1 + κ - |w|)/κ))` and
`w = t⁻¹(y - x)`, `∫ χ⁻ β dV ≤ ∫_{B_t(x) × G} β dV ≤ ∫ χ⁺ β dV` for `β ≥ 0`, since
`χ⁻(w) β ≤ 1_{B_t(x) × G} β ≤ χ⁺(w) β` pointwise and all three integrands are bounded, measurable
and vanish off `B_{2t}(x) × G`, which has finite `V`-measure. -/
theorem Submission.frt_vgm_tba_ball_cutoff_sandwich :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (β : C(Grassmannian N n, ℝ)) (κ t : ℝ), 0 < κ → κ < 1 → 0 < t → closedBall x (2 * t) ⊆ U → (∀ S, 0 ≤ β S) → (∫ z, max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure) ≤ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ∧ ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure ≤ ∫ z, max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 ∂V.measure := by
  intro N n U V x β κ t hκ hκ1 ht hU hβ
  -- Step 1: `V(B_{2t}(x) × G) < ∞` (`B_{2t}(x)` is a compact subset of `U`), and
  -- `B = B_t(x) × G` is Borel.
  have hK : V.measure (closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ :=
    V.finite_on_compact _ (isCompact_closedBall x (2 * t)) hU
  have hB : MeasurableSet (closedBall x t ×ˢ (univ : Set (Grassmannian N n))) :=
    measurableSet_closedBall.prod MeasurableSet.univ
  -- Step 2: `|β| ≤ ‖β‖` on the compact Grassmannian.
  have hβb : ∀ S, ‖β S‖ ≤ ‖β‖ := β.norm_coe_le_norm
  -- Step 3: `|t⁻¹(y - x)| = dist(y, x)/t`; hence `z ∈ B ↔ |w(z)| ≤ 1`, and `|w(z)| > 2` off
  -- `B_{2t}(x) × G`.
  have hw : ∀ y : Euclidean N, ‖t⁻¹ • (y - x)‖ = dist y x / t := fun y ↦ by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), dist_eq_norm, inv_mul_eq_div]
  have hin : ∀ z : Euclidean N × Grassmannian N n,
      z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n)) ↔ ‖t⁻¹ • (z.1 - x)‖ ≤ 1 := fun z ↦ by
    rw [mem_prod, mem_closedBall, hw, div_le_one ht, and_iff_left (mem_univ _)]
  have hfar : ∀ z : Euclidean N × Grassmannian N n,
      z ∉ closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n)) → 2 < ‖t⁻¹ • (z.1 - x)‖ := by
    intro z hz
    rw [mem_prod, mem_closedBall, and_iff_left (mem_univ _), not_le] at hz
    rw [hw, lt_div_iff₀ ht]
    exact hz
  -- Step 4: cut-off facts for `χ_a(w) = max(0, min(1, (a - |w|)/κ))`.
  have hχ0 : ∀ a r : ℝ, 0 ≤ max 0 (min 1 ((a - r) / κ)) := fun a r ↦ le_max_left _ _
  have hχ1 : ∀ a r : ℝ, max 0 (min 1 ((a - r) / κ)) ≤ 1 := fun a r ↦
    max_le zero_le_one (min_le_left _ _)
  have hχz : ∀ a r : ℝ, a ≤ r → max 0 (min 1 ((a - r) / κ)) = 0 := fun a r h ↦
    max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) hκ.le))
  have hχo : ∀ a r : ℝ, r ≤ a - κ → max 0 (min 1 ((a - r) / κ)) = 1 := fun a r h ↦ by
    rw [min_eq_left ((one_le_div hκ).2 (by linarith)), max_eq_right zero_le_one]
  -- Step 5: a measurable function bounded by `‖β‖` and vanishing off `B_{2t}(x) × G` is
  -- `V`-integrable.
  have hint : ∀ k : Euclidean N × Grassmannian N n → ℝ, AEStronglyMeasurable k V.measure →
      (∀ z, ‖k z‖ ≤ ‖β‖) →
      (∀ z, z ∉ closedBall x (2 * t) ×ˢ (univ : Set (Grassmannian N n)) → k z = 0) →
      Integrable k V.measure := fun k hk hb h0 ↦
    (Measure.integrableOn_of_bounded hK hk (ae_of_all _ hb)).integrable_of_forall_notMem_eq_zero h0
  have hβc : Continuous fun z : Euclidean N × Grassmannian N n ↦ β z.2 :=
    β.continuous.comp continuous_snd
  have hbd : ∀ (a : ℝ) (z : Euclidean N × Grassmannian N n),
      ‖max 0 (min 1 ((a - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2‖ ≤ ‖β‖ := fun a z ↦ by
    rw [norm_mul, Real.norm_of_nonneg (hχ0 _ _)]
    exact (mul_le_mul (hχ1 _ _) (hβb _) (norm_nonneg _) zero_le_one).trans (one_mul _).le
  have hm : Integrable (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (hbd 1) fun z hz ↦ ?_
    rw [hχz 1 _ (by linarith [hfar z hz]), zero_mul]
  have hp : Integrable (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) V.measure := by
    refine hint _ (Continuous.aestronglyMeasurable (by fun_prop)) (hbd (1 + κ)) fun z hz ↦ ?_
    rw [hχz (1 + κ) _ (by linarith [hfar z hz]), zero_mul]
  have hi : Integrable ((closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator
      fun z : Euclidean N × Grassmannian N n ↦ β z.2) V.measure := by
    refine hint _ (hβc.aestronglyMeasurable.indicator hB)
      (fun z ↦ (norm_indicator_le_norm_self _ z).trans (hβb _)) fun z hz ↦ ?_
    refine indicator_of_notMem (fun hzB ↦ hz ?_) _
    exact ⟨mem_closedBall.2 ((mem_closedBall.1 hzB.1).trans (by linarith)), mem_univ _⟩
  -- Step 6: the pointwise sandwich `χ⁻(w) β ≤ 1_B β ≤ χ⁺(w) β`.
  have hle₁ : (fun z : Euclidean N × Grassmannian N n ↦
      max 0 (min 1 ((1 - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2) ≤
      (closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator fun z ↦ β z.2 := by
    intro z
    dsimp only
    by_cases hz : z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n))
    · rw [indicator_of_mem hz]
      exact mul_le_of_le_one_left (hβ _) (hχ1 _ _)
    · rw [indicator_of_notMem hz, hχz 1 _ (not_le.1 (mt (hin z).2 hz)).le, zero_mul]
  have hle₂ : (closedBall x t ×ˢ (univ : Set (Grassmannian N n))).indicator
      (fun z : Euclidean N × Grassmannian N n ↦ β z.2) ≤
      fun z ↦ max 0 (min 1 ((1 + κ - ‖t⁻¹ • (z.1 - x)‖) / κ)) * β z.2 := by
    intro z
    dsimp only
    by_cases hz : z ∈ closedBall x t ×ˢ (univ : Set (Grassmannian N n))
    · rw [indicator_of_mem hz, hχo (1 + κ) _ (by linarith [(hin z).1 hz]), one_mul]
    · rw [indicator_of_notMem hz]
      exact mul_nonneg (hχ0 _ _) (hβ _)
  -- Step 7: integrate, using `∫ 1_B β dV = ∫_B β dV`.
  rw [← integral_indicator hB]
  exact ⟨integral_mono hm hi hle₁, integral_mono hi hp hle₂⟩
/-- The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane
`T ∈ G(N,n)` is `ω_n r^n` (step 5, plane balls, of the tangent-ball average proof for Simon Ch. 8,
1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`. -/
theorem Submission.frt_vgm_tba_plane_closedBall_hausdorff :
    ∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  intro N n T r hr
  -- Step 1: an orthonormal basis `b` of `T.plane` indexed by `Fin n`, since `finrank T.plane = n`.
  let b : OrthonormalBasis (Fin n) ℝ T.plane :=
    (stdOrthonormalBasis ℝ T.plane).reindex (finCongr T.finrank_plane)
  -- Step 2: the isometric parametrization `ι : ℝ^n → ℝ^N`, `ι v = b.repr.symm v ∈ T.plane`.
  let ι : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] Euclidean N :=
    T.plane.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  -- Step 3: `ι '' B_r(0) = T.plane ∩ B_r(0)`.
  have himage : ι '' closedBall 0 r = (T.plane : Set (Euclidean N)) ∩ closedBall 0 r := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(b.repr.symm v).2, ?_⟩
      rw [mem_closedBall_zero_iff] at hv ⊢
      rwa [ι.norm_map]
    · rintro ⟨hw, hwr⟩
      refine ⟨b.repr ⟨w, hw⟩, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff] at hwr ⊢
        rwa [b.repr.norm_map]
      · change ((b.repr.symm (b.repr ⟨w, hw⟩) : T.plane) : Euclidean N) = w
        rw [b.repr.symm_apply_apply]
  -- Step 4: `H^n` is invariant under the isometry `ι`, and `H^n = vol` on `ℝ^n`.
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- Step 5: Haar scaling `vol (B_r(0)) = r^n vol (B°_1(0))` (`r ≥ 0`; no `0 < n` needed).
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr,
    unitBallVolume, mul_comm]

/-- The plane integrals of the radial cut-offs `χ⁻ = χ_{1-κ,1}` and `χ⁺ = χ_{1,1+κ}`, where
`χ_{a,b}(y) = max(0, min(1, (b - |y|)/(b - a)))`, over an `n`-plane `T ∈ G(N,n)` satisfy
`ω_n (1-κ)^n ≤ ∫_T χ⁻ dH^n` and `∫_T χ⁺ dH^n ≤ ω_n (1+κ)^n` for `0 < κ < 1` (step 6 of the
tangent-ball average in the proof of Simon Ch. 8, 1.2): `1_{B_{1-κ}(0)} ≤ χ⁻` and
`χ⁺ ≤ 1_{B_{1+κ}(0)}`, while `H^n(T ∩ B_r(0)) = ω_n r^n`
(`frt_vgm_tba_plane_closedBall_hausdorff`). -/
theorem Submission.frt_vgm_tba_plane_cutoff_bounds :
    ∀ (N n : ℕ) (T : Grassmannian N n) (κ : ℝ), 0 < κ → κ < 1 → (unitBallVolume n).toReal * (1 - κ) ^ n ≤ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n] ∧ ∫ y in (T.plane : Set (Euclidean N)), max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n] ≤ (unitBallVolume n).toReal * (1 + κ) ^ n := by
  intro N n T κ hκ hκ1
  set μ : Measure (Euclidean N) :=
    (μHE[n] : Measure (Euclidean N)).restrict (T.plane : Set (Euclidean N)) with hμ
  -- Step 1: `μ(B_r(0)) = ω_n r^n < ∞` for `r ≥ 0`, from `frt_vgm_tba_plane_closedBall_hausdorff`.
  have hball : ∀ r : ℝ, 0 ≤ r → μ (closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
    intro r hr
    rw [hμ, Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.frt_vgm_tba_plane_closedBall_hausdorff N n T r hr
  have hfin : ∀ r : ℝ, 0 ≤ r → μ (closedBall 0 r) ≠ ∞ := by
    intro r hr
    rw [hball r hr]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hreal : ∀ r : ℝ, 0 ≤ r → μ.real (closedBall 0 r) = (unitBallVolume n).toReal * r ^ n := by
    intro r hr
    rw [measureReal_def, hball r hr, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr]
  -- Step 2: the cut-off `χ_a(y) = max(0, min(1, (a - |y|)/κ))` takes values in `[0,1]`, vanishes
  -- where `|y| ≥ a` and equals `1` where `|y| ≤ a - κ`.
  have hχ0 : ∀ (a : ℝ) (y : Euclidean N), 0 ≤ max 0 (min 1 ((a - ‖y‖) / κ)) :=
    fun a y ↦ le_max_left _ _
  have hχ1 : ∀ (a : ℝ) (y : Euclidean N), max 0 (min 1 ((a - ‖y‖) / κ)) ≤ 1 :=
    fun a y ↦ max_le zero_le_one (min_le_left _ _)
  have hχ_out : ∀ (a : ℝ) (y : Euclidean N), a ≤ ‖y‖ → max 0 (min 1 ((a - ‖y‖) / κ)) = 0 :=
    fun a y hy ↦ max_eq_left
      ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hy) hκ.le))
  have hχ_in : ∀ (a : ℝ) (y : Euclidean N), ‖y‖ ≤ a - κ → max 0 (min 1 ((a - ‖y‖) / κ)) = 1 := by
    intro a y hy
    rw [min_eq_left ((le_div_iff₀ hκ).2 (by linarith)), max_eq_right zero_le_one]
  -- Step 3: `χ_a` (`a ≤ 2`) and the ball indicators are `μ`-integrable.
  have hχ_int : ∀ a : ℝ, a ≤ 2 →
      Integrable (fun y : Euclidean N ↦ max 0 (min 1 ((a - ‖y‖) / κ))) μ := by
    intro a ha
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := closedBall (0 : Euclidean N) 2) ?_ fun y hy ↦ hχ_out a y ?_
    · refine Measure.integrableOn_of_bounded (M := 1) (hfin 2 zero_le_two) (by fun_prop) ?_
      exact Eventually.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hχ0 a y)]; exact hχ1 a y
    · rw [mem_closedBall_zero_iff, not_le] at hy
      linarith
  have hind_int : ∀ r : ℝ, 0 ≤ r → Integrable ((closedBall (0 : Euclidean N) r).indicator 1) μ :=
    fun r hr ↦ (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (C := (1 : ℝ)) (hfin r hr))
  constructor
  · -- Step 4: `1_{B_{1-κ}(0)} ≤ χ⁻`, so `ω_n (1-κ)^n = μ(B_{1-κ}(0)) ≤ ∫ χ⁻ dμ`.
    rw [← hreal (1 - κ) (by linarith), ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono (hind_int (1 - κ) (by linarith)) (hχ_int 1 (by norm_num)) fun y ↦ ?_
    by_cases hy : y ∈ closedBall (0 : Euclidean N) (1 - κ)
    · rw [indicator_of_mem hy, Pi.one_apply, hχ_in 1 y (mem_closedBall_zero_iff.1 hy)]
    · rw [indicator_of_notMem hy]
      exact hχ0 1 y
  · -- Step 5: `χ⁺ ≤ 1_{B_{1+κ}(0)}`, so `∫ χ⁺ dμ ≤ μ(B_{1+κ}(0)) = ω_n (1+κ)^n`.
    rw [← hreal (1 + κ) (by linarith), ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono (hχ_int (1 + κ) (by linarith)) (hind_int (1 + κ) (by linarith))
      fun y ↦ ?_
    by_cases hy : y ∈ closedBall (0 : Euclidean N) (1 + κ)
    · rw [indicator_of_mem hy, Pi.one_apply]
      exact hχ1 (1 + κ) y
    · rw [indicator_of_notMem hy, hχ_out (1 + κ) y (not_le.1 (mt mem_closedBall_zero_iff.2 hy)).le]

/-- Ball integrals at a tangent plane for `β ≥ 0` (the step "`ν_V^{(x)}(β) = θ(x) β(T_x)`" in the
proof of Simon Ch. 8, 1.2, p. 207, for the ratios of 1.3): if `V` has tangent space `T` with
multiplicity `θ` at `x` (1.1), then `t^{-n} ∫_{B_t(x) × G(N,n)} β(S) dV(y,S) → θ ω_n β(T)` as
`t ↓ 0` for every continuous `β ≥ 0` on `G(N,n)`. -/
theorem Submission.frt_vgm_tba_nonneg_ball_limit :
    ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ β : C(Grassmannian N n, ℝ), (∀ S, 0 ≤ β S) → Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z in closedBall x t ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) (𝓝[>] 0) (𝓝 (θ * (unitBallVolume n).toReal * β T)) := by
  intro N n U V x T θ hT β hβ
  -- `J(t) = t^{-n} ∫_{B_t(x) × G(N,n)} β dV` is to tend to `c = θ β(T) ω_n`; here `θ β(T) ≥ 0`
  -- since `θ > 0` and `β ≥ 0`.
  have hθβ : 0 ≤ θ * β T := mul_nonneg hT.2.1.le (hβ T)
  set c : ℝ := θ * β T * (unitBallVolume n).toReal with hc
  -- Step 1: `x ∈ U` and `U` is open, so eventually as `t → 0⁺`, `t > 0` and `B_{2t}(x) ⊆ U`.
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 V.isOpen_domain x hT.1
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ closedBall x (2 * t) ⊆ U := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ)] with t ht
    exact ⟨ht.1, (closedBall_subset_ball (by linarith [ht.2])).trans hδU⟩
  -- Step 2: the cut-off `χ_a(y) = max(0, min(1, (a - |y|)/κ))` is continuous and vanishes off the
  -- compact ball `B_a(0)`, so it is an element of `C_c(ℝ^N)`.
  have hcut : ∀ a κ : ℝ, 0 < κ →
      ∃ g : C_c(Euclidean N, ℝ), ∀ y, g y = max 0 (min 1 ((a - ‖y‖) / κ)) := by
    intro a κ hκ
    refine ⟨⟨⟨fun y ↦ max 0 (min 1 ((a - ‖y‖) / κ)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean N) a) fun y hy ↦ ?_⟩,
      fun _ ↦ rfl⟩
    have hay : a < ‖y‖ := by simpa using hy
    exact max_eq_left ((min_le_right _ _).trans (div_neg_of_neg_of_pos (by linarith) hκ).le)
  -- Step 3: by `tendsto_order`, show that eventually `a' < J(t)` for each `a' < c`, and
  -- `J(t) < b'` for each `b' > c`.
  rw [show θ * (unitBallVolume n).toReal * β T = c by rw [hc]; ring]
  refine tendsto_order.2 ⟨fun a' ha' ↦ ?_, fun b' hb' ↦ ?_⟩
  · -- Step 4: with `ε = c - a'`, fix `κ ∈ (0,1)` such that `c (1 - κ)^n > c - ε/2`.
    have hε : 0 < c - a' := sub_pos.2 ha'
    have hcont : Tendsto (fun κ : ℝ ↦ c * (1 - κ) ^ n) (𝓝[>] 0) (𝓝 c) := by
      have h : Continuous fun κ : ℝ ↦ c * (1 - κ) ^ n := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨κ, hκc, hκ⟩ := ((hcont.eventually (lt_mem_nhds (sub_lt_self c (half_pos hε)))).and
      (Ioo_mem_nhdsGT one_pos)).exists
    -- (a) `I⁻(t) = t^{-n} ∫ χ⁻(t⁻¹(y - x)) β(S) dV → θ β(T) c⁻` with `c⁻ = ∫_T χ⁻ dHⁿ`.
    obtain ⟨g, hg⟩ := hcut 1 κ hκ.1
    have hlim := Submission.frt_vgm_tba_product_blowup_tendsto N n U V x T θ hT g β
    simp only [hg] at hlim
    -- (b) `c (1 - κ)^n ≤ θ β(T) c⁻`, from `ω_n (1 - κ)^n ≤ c⁻`.
    have hL : c * (1 - κ) ^ n ≤ θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
        max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n]) := by
      calc c * (1 - κ) ^ n = θ * β T * ((unitBallVolume n).toReal * (1 - κ) ^ n) := by
            rw [hc]; ring
        _ ≤ θ * β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 - ‖y‖) / κ)) ∂μHE[n] :=
          mul_le_mul_of_nonneg_left
            (Submission.frt_vgm_tba_plane_cutoff_bounds N n T κ hκ.1 hκ.2).1 hθβ
        _ = _ := mul_assoc _ _ _
    -- (c), (d): eventually `a' < I⁻(t) ≤ J(t)`, the second by the ball cut-off sandwich.
    filter_upwards [hlim.eventually (lt_mem_nhds (sub_lt_self _ (half_pos hε))), hgood]
      with t hI ht
    have hJ := mul_le_mul_of_nonneg_left
      (Submission.frt_vgm_tba_ball_cutoff_sandwich N n U V x β κ t hκ.1 hκ.2 ht.1 ht.2 hβ).1
      (pow_nonneg (inv_nonneg.2 ht.1.le) n)
    linarith
  · -- Step 5: with `ε = b' - c`, fix `κ ∈ (0,1)` such that `c (1 + κ)^n < c + ε/2`.
    have hε : 0 < b' - c := sub_pos.2 hb'
    have hcont : Tendsto (fun κ : ℝ ↦ c * (1 + κ) ^ n) (𝓝[>] 0) (𝓝 c) := by
      have h : Continuous fun κ : ℝ ↦ c * (1 + κ) ^ n := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨κ, hκc, hκ⟩ := ((hcont.eventually
      (gt_mem_nhds (lt_add_of_pos_right c (half_pos hε)))).and (Ioo_mem_nhdsGT one_pos)).exists
    -- (a) `I⁺(t) = t^{-n} ∫ χ⁺(t⁻¹(y - x)) β(S) dV → θ β(T) c⁺` with `c⁺ = ∫_T χ⁺ dHⁿ`.
    obtain ⟨g, hg⟩ := hcut (1 + κ) κ hκ.1
    have hlim := Submission.frt_vgm_tba_product_blowup_tendsto N n U V x T θ hT g β
    simp only [hg] at hlim
    -- (b) `θ β(T) c⁺ ≤ c (1 + κ)^n`, from `c⁺ ≤ ω_n (1 + κ)^n`.
    have hU : θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
        max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n]) ≤ c * (1 + κ) ^ n := by
      calc θ * (β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n])
          = θ * β T * ∫ y in (T.plane : Set (Euclidean N)),
            max 0 (min 1 ((1 + κ - ‖y‖) / κ)) ∂μHE[n] := (mul_assoc _ _ _).symm
        _ ≤ θ * β T * ((unitBallVolume n).toReal * (1 + κ) ^ n) :=
          mul_le_mul_of_nonneg_left
            (Submission.frt_vgm_tba_plane_cutoff_bounds N n T κ hκ.1 hκ.2).2 hθβ
        _ = c * (1 + κ) ^ n := by rw [hc]; ring
    -- (c), (d): eventually `J(t) ≤ I⁺(t) < b'`, the first by the ball cut-off sandwich.
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε))), hgood]
      with t hI ht
    have hJ := mul_le_mul_of_nonneg_left
      (Submission.frt_vgm_tba_ball_cutoff_sandwich N n U V x β κ t hκ.1 hκ.2 ht.1 ht.2 hβ).2
      (pow_nonneg (inv_nonneg.2 ht.1.le) n)
    linarith

theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧ FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧ TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧ IntegralCompactnessTheorem := by sorry

end GMT.Ch08
