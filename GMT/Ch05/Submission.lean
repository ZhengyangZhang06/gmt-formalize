import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Simon, *Introduction to GMT*, Chapter 5: The Allard Regularity Theorem (pp. 103–130)

Frozen problem statement.  Conventions (Simon's "Notation", p. ix):
* `B_ρ(y)` is the **closed** ball (`Metric.closedBall`), `B̆_ρ(y)` the open ball (`Metric.ball`);
* `ℝ^{n+ℓ}` is `EuclideanSpace ℝ (Fin (n + ℓ))`, whose first `n` coordinates span `ℝⁿ × {0}`;
* `Hⁿ` is Mathlib's `μHE[n]` (normalized so that `Hⁿ = Lⁿ` on `n`-planes, as in Simon);
* `ω_n = π^{n/2}/Γ(n/2+1)`;
* `|A|` for a linear map is the inner-product (Hilbert–Schmidt) norm `(Σ_{ij} A_{ij}²)^{1/2}`
  (Simon p. ix and footnote 2 on p. 115).
* All results are stated for `n ≥ 1` (the book's `n`-dimensional setting) and arbitrary `ℓ`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GMT.Ch05

/-- Ambient space `ℝ^{n+ℓ}`. -/
abbrev Amb (n ℓ : ℕ) := EuclideanSpace ℝ (Fin (n + ℓ))

/-- Euclidean space `ℝᵐ`. -/
abbrev Rn (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- `ω_n = π^{n/2} / Γ(n/2 + 1)` (Simon, Notation p. ix): the volume of the unit ball of `ℝⁿ`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)

/-- Squared Hilbert–Schmidt ("inner product") norm `|A|² = Σ_i |A eᵢ|² = Σ_{i,j} A_{ji}²`
(Simon, Notation p. ix; Ch. 5 footnote 2 p. 115 and Remark 4.4). -/
noncomputable def hsNormSq {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  ∑ i : Fin m, ‖A (EuclideanSpace.single i 1)‖ ^ 2

/-- Hilbert–Schmidt norm `|A| = (Σ_{i,j} A_{ji}²)^{1/2}`; for `A = Du` this is Simon's `|Du|`. -/
noncomputable def hsNorm {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  Real.sqrt (hsNormSq A)

/-- The point `(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}` (first `n` coordinates `x`, last `ℓ` coordinates `y`). -/
noncomputable def graphPoint {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ) : Amb n ℓ :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

/-- `graph u = {(x, u(x)) : x ∈ D} ⊆ ℝ^{n+ℓ}` for `u : D ⊆ ℝⁿ → ℝ^ℓ`. -/
noncomputable def graphOver {n ℓ : ℕ} (u : Rn n → Rn ℓ) (D : Set (Rn n)) : Set (Amb n ℓ) :=
  (fun x => graphPoint x (u x)) '' D

/-- The coordinate plane `ℝⁿ × {0} ⊆ ℝ^{n+ℓ}`. -/
noncomputable def horizontalPlane (n ℓ : ℕ) : Submodule ℝ (Amb n ℓ) :=
  Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))

/-- The rotated plane `q(ℝⁿ × {0})` for a linear isometry `q` of `ℝ^{n+ℓ}`. -/
noncomputable def rotatedPlane {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) : Submodule ℝ (Amb n ℓ) :=
  (horizontalPlane n ℓ).map q.toLinearEquiv.toLinearMap

/-- Simon Ch. 2 §4 (p. 55), definition preceding 4.1, with `r = 1`: `S ⊆ ℝ^N` is an
`m`-dimensional `C¹` submanifold if each `y ∈ S` has open `V ⊆ ℝᵐ`, `W ∋ y` and a 1:1 `C¹` map
`φ : V → W` with `φ(V) = W ∩ S`, `φ` proper (`K ⊆ W` compact ⇒ `φ⁻¹(K)` compact in `V`) and
`Dφ(x)` of rank `m` (injective) for all `x ∈ V`. -/
def IsC1Submanifold (m : ℕ) {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ y ∈ S, ∃ (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N)))
    (φ : Rn m → EuclideanSpace ℝ (Fin N)),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 φ V ∧ InjOn φ V ∧ φ '' V = W ∩ S ∧
    (∀ K, IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) ∧
    ∀ x ∈ V, Function.Injective (fderiv ℝ φ x)

/-- `u ∈ C^{k,α}(W)` for open `W`: `u` is `C^k` on `W`, all derivatives of order `≤ k` are bounded on
`W`, and the `k`-th derivative is `α`-Hölder on `W` (finite global seminorm).  Used for the
qualitative Hölder classes of Theorem 7.1 (any fixed norm on multilinear maps gives the same class). -/
def IsHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (u : Rn m → Rn k) (W : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j u W ∧
  (∃ B : ℝ, ∀ i ≤ j, ∀ x ∈ W, ‖iteratedFDeriv ℝ i u x‖ ≤ B) ∧
  ∃ K : ℝ, ∀ x ∈ W, ∀ y ∈ W,
    ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ ≤ K * ‖x - y‖ ^ α

/-- `h` is `C^{k,α}` in the open set `U` (locally): `C^k` on `U`, and the `k`-th derivative is
`α`-Hölder on each compact subset of `U` (Simon 7.1, "a `C^{q,α}` function in `U`"). -/
def IsLocallyHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (h : Rn m → Rn k) (U : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j h U ∧
  ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α

/-- A rectifiable `n`-varifold `V = v(M, θ)` in the open set `U ⊆ ℝ^{n+ℓ}`
(Simon Ch. 4, introduction p. 85, and 3.14): only the primitive data `M ⊆ U` and `θ`, with
* `M` countably `n`-rectifiable (Ch. 3, 1.1; SimonGMT `Chapter03.CountablyRectifiable`) and
  `Hⁿ`-measurable;
* `θ` positive on `M`, `Hⁿ`-measurable, and locally `Hⁿ`-integrable on `M` in `U`.
No tangent-plane data is stored: tangent planes are *defined* below (`tangentProj`) as approximate
tangent spaces where they exist (their a.e. existence is Ch. 3, 1.9, a theorem). -/
structure RectifiableVarifold (n ℓ : ℕ) (U : Set (Amb n ℓ)) where
  /-- The carrier `M`. -/
  carrier : Set (Amb n ℓ)
  /-- The multiplicity function `θ` (its values off `M` are irrelevant). -/
  mult : Amb n ℓ → ℝ
  carrier_subset : carrier ⊆ U
  nullMeasurableSet_carrier : NullMeasurableSet carrier (μHE[n] : Measure (Amb n ℓ))
  countablyRectifiable : Poincare.SimonGMT.Chapter03.CountablyRectifiable n carrier
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  aemeasurable_mult : AEMeasurable mult ((μHE[n] : Measure (Amb n ℓ)).restrict carrier)
  integrableOn_mult : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U →
    IntegrableOn mult (carrier ∩ K) (μHE[n] : Measure (Amb n ℓ))

namespace RectifiableVarifold

variable {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)

/-- Simon Ch. 4, 1.1: the weight measure `μ_V = Hⁿ ⌞ θ` (with `θ = 0` off `M`). -/
noncomputable def weight : Measure (Amb n ℓ) :=
  ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
    (fun x => ENNReal.ofReal (V.mult x))

/-- Simon Ch. 4, 1.4: `spt V = spt μ_V`, taken inside the open set `U` where `V` lives. -/
def support : Set (Amb n ℓ) := U ∩ V.weight.support

open Classical in
/-- Orthogonal projection `p_{T_x M}` onto the tangent space `T_x V` (Simon Ch. 4, 1.3): the
approximate tangent space of `M` with respect to `θ` (Ch. 3, 1.7/1.9; SimonGMT
`Chapter03.HasWeightedApproximateTangentSpaceAt`) **where it exists**, and `0` elsewhere.  It is
unique on `M` (where `θ > 0`) and exists `μ_V`-a.e. by Ch. 3, 1.9 — a theorem, not an assumption. -/
noncomputable def tangentProj (x : Amb n ℓ) : Amb n ℓ →L[ℝ] Amb n ℓ :=
  if h : ∃ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
  then (Classical.choose h).starProjection else 0

/-- Tangential divergence `div_M X (x) = Σ_{i,j} e^{ij}(x) D_i X^j(x) = trace(DX(x) ∘ p_{T_x M})`
(Simon Ch. 2, 4.18; Ch. 4, 2.3). -/
noncomputable def divM (X : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ) : ℝ :=
  LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap)

/-- Simon Ch. 4, Definition 3.14: `V` has generalized mean curvature `H` in `U` if
`∫ div_M X dμ_V = -∫ X · H dμ_V` for all `X ∈ C¹_c(U; ℝ^{n+ℓ})`; the implicit requirement that the
right side exist for every such `X` is the local `μ_V`-integrability of `H` on `U`. -/
def HasGeneralizedMeanCurvature (H : Amb n ℓ → Amb n ℓ) : Prop :=
  LocallyIntegrableOn H U V.weight ∧
  ∀ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    ∫ x, V.divM X x ∂V.weight = -∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- `H` is locally in `Lᵖ(μ_V)` in `U`: `∫_K |H|ᵖ dμ_V < ∞` for every compact `K ⊆ U`. -/
def LocallyLp (H : Amb n ℓ → Amb n ℓ) (p : ℝ) : Prop :=
  ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight < ∞

/-- `Θⁿ(μ_V, x) = t`: `μ_V(B_r(x)) / (ω_n rⁿ) → t` as `r ↓ 0` (Simon Ch. 1 §3; Ch. 4). -/
def HasDensity (x : Amb n ℓ) (t : ℝ) : Prop :=
  Tendsto (fun r : ℝ => V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal t))

/-- Simon Ch. 5, 4.1 (p. 115): tilt-excess
`E(ξ, σ, T) = σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_T|² dμ_V` (Hilbert–Schmidt norm, **no** factor `1/2`;
`B_σ(ξ)` closed).  Defined by the book only when `B_σ(ξ) ⊆ U`. -/
noncomputable def tiltExcess (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  (σ ^ n)⁻¹ * ∫ x in closedBall ξ σ, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight

/-- `(σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}` as an extended real (no junk value when infinite). -/
noncomputable def scaledLpNorm (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (σ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (σ ^ (p - n)) * ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)

/-- Simon Ch. 5, p. 116 (before 4.5):
`E_*(ξ, σ, T) = max{E(ξ, σ, T), δ⁻¹ (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{2/p}}`, `δ` as in 2.3. -/
noncomputable def tiltExcessStar (H : Amb n ℓ → Amb n ℓ) (p δ : ℝ) (ξ : Amb n ℓ) (σ : ℝ)
    (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  max (V.tiltExcess ξ σ T) (δ⁻¹ * (V.scaledLpNorm H p ξ σ).toReal ^ 2)

/-- `sup {dist(x − ξ, T) : x ∈ spt V ∩ B_σ(ξ)}` (Simon 2.5), as an extended real. -/
noncomputable def heightSup (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ≥0∞ :=
  ⨆ x ∈ V.support ∩ closedBall ξ σ, ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ)))

/-- The standing hypotheses 2.3 = 5.1 of Simon Ch. 5 (pp. 108, 121), for `V` with generalized
mean curvature `H` in `U`:
`θ ≥ 1 μ_V-a.e.`, `0 ∈ spt V`, `B_ρ(0) ⊆ U`, `ω_n⁻¹ ρ⁻ⁿ μ_V(B_ρ(0)) ≤ 1 + δ`,
`(ρ^{p−n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ` (and `ρ > 0`). -/
def AllardHypotheses (H : Amb n ℓ → Amb n ℓ) (p δ ρ : ℝ) : Prop :=
  0 < ρ ∧ V.HasGeneralizedMeanCurvature H ∧ (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) ∧
  (0 : Amb n ℓ) ∈ V.support ∧ closedBall (0 : Amb n ℓ) ρ ⊆ U ∧
  V.weight (closedBall 0 ρ) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) ∧
  V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ

/-- Simon Ch. 5, 7.2 (p. 128): `ξ ∈ spt V` is a regular point if `B̆_ρ(ξ) ∩ spt V` is an
`n`-dimensional `C¹` submanifold of `ℝ^{n+ℓ}` for some `ρ > 0`; `reg V` is the set of regular points
(and `sing V = spt V \ reg V`). -/
def regularSet : Set (Amb n ℓ) :=
  {ξ | ξ ∈ V.support ∧ ∃ ρ > 0, IsC1Submanifold n (ball ξ ρ ∩ V.support)}

end RectifiableVarifold

open RectifiableVarifold

/-- `ρ⁻¹ sup_B |u| + sup_B |Du| + ρ^α sup_{x ≠ y ∈ B} |x − y|^{−α} |Du(x) − Du(y)|` on a set `B`
(the quantity estimated in Simon 5.2), with `Du` the derivative within `B` and `|·|` the
Hilbert–Schmidt norm; as an extended real, so suprema never take junk values. -/
noncomputable def scaledC1AlphaNorm {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B : Set (Rn n)) (α ρ : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal ρ⁻¹ * (⨆ x ∈ B, ‖u x‖ₑ) +
  (⨆ x ∈ B, ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x))) +
  ENNReal.ofReal (ρ ^ α) * ⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)

/-- The conclusion of Simon 5.2 for radius `γρ` and constant `C`: there are a linear isometry `q`
of `ℝ^{n+ℓ}` and `u ∈ C^{1,1−n/p}(B_{γρ}(0); ℝ^ℓ)` (closed ball) with `u(0) = 0`, `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`, and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} [Du]_{1−n/p} ≤ C δ^{1/(2n+2)}`. -/
def AllardConclusion {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (p δ ρ γ C : ℝ) : Prop :=
  ∃ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (closedBall 0 (γ * ρ)) ∧ u 0 = 0 ∧
    fderivWithin ℝ u (closedBall 0 (γ * ρ)) 0 = 0 ∧
    V.support ∩ closedBall 0 (γ * ρ) =
      q '' graphOver u (closedBall 0 (γ * ρ)) ∩ closedBall 0 (γ * ρ) ∧
    scaledC1AlphaNorm u (closedBall 0 (γ * ρ)) (1 - n / p) ρ ≤
      ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- `W^{1,2}(Ω)` with weak gradient `g` (Simon, Notation p. ix): `f, g ∈ L²(Ω)` and
`∫_Ω f ∇ζ = −∫_Ω ζ g` for every `ζ ∈ C^∞_c(Ω)`. -/
def IsW12WithGradient {n : ℕ} (f : Rn n → ℝ) (g : Rn n → Rn n) (Ω : Set (Rn n)) : Prop :=
  MemLp f 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
    ∫ x in Ω, f x • gradient ζ x = -∫ x in Ω, ζ x • g x

/-! ## Headline results -/

/-- **Simon Ch. 5, Lemma 2.1 (p. 107).**  Let `V = v(M, θ)` have generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}` (no lower bound on `θ` is needed).  If `B_ρ(ξ) ⊆ U`, then for every
`n`-dimensional subspace `T`,
`E(ξ, ρ/2, T) ≤ C ρ⁻ⁿ ∫_{B_ρ(ξ)} (dist(x − ξ, T)/ρ)² dμ_V + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ_V`,
with `C = C(n)` (independent of `ℓ`).  The `|H|²` term is an extended-real integral (it may be
infinite, in which case the inequality is trivial). -/
def TiltExcessHeightEstimate : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
  ∀ (ξ : Amb n ℓ) (ρ : ℝ), 0 < ρ → closedBall ξ ρ ⊆ U →
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
    ENNReal.ofReal (V.tiltExcess ξ (ρ / 2) T) ≤
      ENNReal.ofReal (C * (ρ ^ n)⁻¹ *
        ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight) +
      ENNReal.ofReal (C * ρ ^ ((2 : ℝ) - n)) * ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)**, `p > n` (standing assumption of
the chapter).  There is `C = C(n, ℓ, p) > 0` such that if `δ ∈ (0, 1/4]` and 2.3 holds, then for each
`ξ ∈ spt V ∩ B_{δρ}(0)` and `σ ∈ (0, 2δρ]` there is an `n`-dimensional subspace `T` with
`C⁻¹ (σ⁻ⁿ ∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² dμ_V)^{1/2}
   ≤ σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} + (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}`
and `σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} ≤ C δ^{1/(2n+2)}`.

*Correction:* the printed first inequality of (‡) omits the mean-curvature term
`(σ^{p−n}∫|H|ᵖ)^{1/p}`; the book derives it "directly from Remark 2.2", which contains exactly this
term, so we state the inequality that the cited argument proves.  (Since this term is `≤ δ`, it
still gives the tilt bound `σ⁻ⁿ∫_{B_{σ/2}(ξ)}|p_{T_xM} − p_T|² ≤ C δ^{1/(n+1)}` used later.) -/
def AffineApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ →
  ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ →
  ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
    ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ *
        ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
      ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ ∧
    ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T ≤ ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- **Simon Ch. 5, Lemma 2.6 (Lipschitz Approximation Lemma, p. 110)**, `p > n`.  There are
`β = β(n, ℓ, p) ∈ (0, 1/4]` and `C = C(n, ℓ, p)` such that: let `L ∈ (0, 1]`,
`δ ∈ (0, (βL)^{2n+2}]`, 2.3 hold, `σ₀ = δρ`, and let `T₀ = q(ℝⁿ × {0})` (`q` a linear isometry) be a
plane with `dist(x, T₀) ≤ K δ^{1/(2n+2)} σ₀` for `x ∈ spt V ∩ B_{2σ₀}(0)`.  Then there is
`f : Bⁿ_{σ₀/2}(0) → ℝ^ℓ` with `Lip f ≤ L`, `sup |f| ≤ K δ^{1/(2n+2)} σ₀` and
`μ_V(B_{σ₀/2}(0) ∩ (spt V \ q(graph f))) + Hⁿ(B_{σ₀/2}(0) ∩ (q(graph f) \ spt V))
   ≤ C L⁻² ∫_{B_{σ₀}(0)} |p_{T_x M} − p_{T₀}|² dμ_V`.

The book takes (w.l.o.g., after a rotation) `T₀ = T(2σ₀, 0) = ℝⁿ × {0}` from Lemma 2.5, which
satisfies the height hypothesis with `K = 2C₂.₅`; we state the rotation explicitly and allow any
such plane. The statement remains true for every `K` with `β, C` independent of `K`: if the tilt of
`T₀` on `B_{σ₀}` exceeds `c²L²` the estimate holds with `f = 0`; otherwise `T₀` is `CL`-close to
`T(2σ₀, 0)` and the book's construction applies relative to `T₀`.
*Correction:* printed `sup|f| ≤ Cδ^{1/(2n+2)}` lacks the scale factor `σ₀` (cf. 2.7 and proof (7)). -/
def LipschitzApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β C : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 2)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 2),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.weight (closedBall 0 (δ * ρ / 2) ∩
        (V.support \ q '' graphOver f (closedBall 0 (δ * ρ / 2)))) +
      (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (δ * ρ / 2) ∩
        (q '' graphOver f (closedBall 0 (δ * ρ / 2)) \ V.support)) ≤
      ENNReal.ofReal (C * (L ^ 2)⁻¹ * ∫ x in closedBall 0 (δ * ρ),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight)

/-- **Simon Ch. 5, Corollary 2.7 (p. 113)**, `p > n`.  With the notation and assumptions of
Lemma 2.6 (as formalized in `LipschitzApproximationLemma`), `β = β(n, ℓ, p)` can be chosen so that
`sup_{ξ ∈ spt V ∩ B_{σ₀/2}(0), σ ∈ (0, σ₀/2]} σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_{T₀}|² dμ_V ≤ β² L²`
implies `spt V ∩ B_{σ₀/4}(0) = q(graph f) ∩ B_{σ₀/4}(0)` for some `f : Bⁿ_{σ₀/4}(0) → ℝ^ℓ` with
`Lip f ≤ L` and `sup |f| ≤ K δ^{1/(2n+2)} σ₀` (book: `C δ^{1/(2n+2)} σ₀`). -/
def LipschitzGraphCorollary : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
    (∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 →
      V.tiltExcess ξ σ (rotatedPlane q) ≤ β ^ 2 * L ^ 2) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 4)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 4),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.support ∩ closedBall 0 (δ * ρ / 4) =
      q '' graphOver f (closedBall 0 (δ * ρ / 4)) ∩ closedBall 0 (δ * ρ / 4)

/-- **Simon Ch. 5, Lemma 3.1 (Harmonic approximation, p. 114).**  Given `ε > 0` there is
`δ = δ(n, ε) > 0` such that if `f ∈ W^{1,2}(B)`, `B = B̆₁(0)` the open unit ball of `ℝⁿ`, satisfies
`∫_B |∇f|² ≤ 1` and `|∫_B ∇f · ∇ζ dLⁿ| ≤ δ sup |∇ζ|` for every `ζ ∈ C^∞_c(B)`, then there is a
harmonic function `u` on `B` with `∫_B |∇u|² ≤ 1` and `∫_B (u − f)² ≤ ε`.
(`sup|∇ζ| ≤ M` is expressed by quantifying over all bounds `M`; the energy integrals of `u` and
`u − f` are extended-real integrals.) -/
def HarmonicApproximationLemma : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) →
    ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 →
    (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 →
      ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x)| ≤ δ * M) →
    ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - f x‖ₑ ^ 2 ≤ ENNReal.ofReal ε

/-- **Simon Ch. 5, Theorem 4.5 (Tilt-excess Decay Theorem, p. 116)**, `p > n`.  There are
`η, δ₀ ∈ (0, 1/4]` depending only on `n, ℓ, p` such that if 2.3 holds for some `δ ∈ (0, δ₀]`, if
`σ ∈ (0, δρ/2]`, `ξ ∈ spt μ_V ∩ B_{δρ}(0)`, and `T` is any `n`-dimensional subspace, then
`E_*(ξ, ησ, S) ≤ η^{2(1−n/p)} E_*(ξ, σ, T)` for some `n`-dimensional subspace `S`. -/
def TiltExcessDecayTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
  ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ),
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
  ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧
    V.tiltExcessStar H p δ ξ (η * σ) S ≤ η ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ T

/-- **Simon Ch. 5, Theorem 5.2 (Allard Regularity Theorem, p. 121).**  If `p > n` is arbitrary,
then there are `δ₀ = δ₀(n, ℓ, p)`, `γ = γ(n, ℓ, p) ∈ (0, 1)` and `C = C(n, ℓ, p)` such that the
hypotheses 5.1 (`AllardHypotheses`) with `δ ≤ δ₀` imply the existence of a linear isometry `q` of
`ℝ^{n+ℓ}` and `u = (u¹, …, u^ℓ) ∈ C^{1,1−n/p}(Bⁿ_{γρ}(0); ℝ^ℓ)` with `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)` and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} sup_{x ≠ y ∈ Bⁿ_{γρ}(0)} |x − y|^{−(1−n/p)} |Du(x) − Du(y)|
   ≤ C δ^{1/(2n+2)}`
(balls closed; see `AllardConclusion`, which also records `u(0) = 0`, automatic since `0 ∈ spt V`).
`δ > 0` is the book's standing convention for 2.3. -/
def AllardRegularityTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ δ₀ γ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 < γ ∧ γ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Remark 5.3 (p. 122) — the extension of Allard's theorem announced for §6.**
For every `γ ∈ (0, 1)` there is `δ₀ = δ₀(γ, n, ℓ, p) ∈ (0, 1)` such that the hypotheses 5.1 with
`δ ≤ δ₀` imply the conclusion of Theorem 5.2 on `B_{γρ}(0)`.  The constant `C` of the estimate is
allowed to depend on `γ` as well (the remark does not specify it; this is the weaker reading). -/
def AllardRegularityAnyRadius : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ : ℝ, 0 < γ → γ < 1 →
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Theorem 6.1 (Conical approximation, p. 124).**  Suppose `Λ > 0`,
`λ, θ, δ ∈ (0, 1/4)`, `ξ ∈ ∂B_{1−θ}(0)`, `V = v(M, θ_V)` has generalized mean curvature
`H ∈ L¹_loc(μ)` in an open `U ⊇ B₁(0)`, `μ = μ_V`,
`|μ(B₁(0))/ω_n − μ(B_λ(0))/(ω_n λⁿ)| + sup_{r ∈ [λ,1]} r^{1−n} ∫_{B_r(0)} |H| dμ ≤ δ`
and `μ(B₁(0)) ≤ Λ`.  Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`
`μ(B_{(1−δ^{1/4})ρ}(ξ)) − Cδ^{1/4}|log λ| ≤ τ⁻ⁿ μ(B_{τρ}(τξ)) ≤ μ(B_{(1+δ^{1/4})ρ}(ξ)) + Cδ^{1/4}|log λ|`
with `C = C(n, ℓ, Λ)`.  (The supremum condition is written pointwise in `r`; the conclusion is in
`[0, ∞]`, where `a − c ≤ b` is written `a ≤ b + c`.) -/
def ConicalApproximationTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ Λ : ℝ, 0 < Λ → ∃ C : ℝ,
  ∀ (lam θ δ : ℝ), 0 < lam → lam < 1 / 4 → 0 < θ → θ < 1 / 4 → 0 < δ → δ < 1 / 4 →
  ∀ ξ : Amb n ℓ, ‖ξ‖ = 1 - θ →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → closedBall 0 1 ⊆ U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
    (∀ r ∈ Icc lam 1,
      |(V.weight (closedBall 0 1)).toReal / unitBallVolume n -
          (V.weight (closedBall 0 lam)).toReal / (unitBallVolume n * lam ^ n)| +
        r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖H x‖ ∂V.weight ≤ δ) →
    V.weight (closedBall 0 1) ≤ ENNReal.ofReal Λ →
  ∀ ρ ∈ Ioc 0 θ, ∀ τ ∈ Icc (2 * lam) 1,
    V.weight (closedBall ξ ((1 - δ ^ (1 / 4 : ℝ)) * ρ)) ≤
        ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|) ∧
      ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) ≤
        V.weight (closedBall ξ ((1 + δ ^ (1 / 4 : ℝ)) * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|)

/-- **Simon Ch. 5, Theorem 7.1, first assertion (p. 127).**  If `V = v(M, θ)` has generalized mean
curvature `H` in the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`,
`θ ≥ 1 μ_V`-a.e. in `U`, and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then there are `ρ > 0` and an orthogonal
`Q` of `ℝ^{n+ℓ}` such that, up to a set of `Hⁿ`-measure zero, `Q ∘ τ(M) ∩ B̆_ρ(0) = graph u`
(`τ(x) = x − ξ`), where `u : W → ℝ^ℓ`, `W ∋ 0` open in `ℝⁿ`, is `C^{1,1−n/p}(W; ℝ^ℓ)` with
`u(0) = 0`, `Du(0) = 0`.  (*Erratum:* printed target `ℝ^k` means `ℝ^ℓ`.) -/
def DensityOneRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα 1 (1 - n / p) u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0

/-- **Simon Ch. 5, Theorem 7.1, second assertion (p. 127).**  In the situation of the first
assertion, if moreover `θ` is positive integer-valued `μ_V`-a.e. in `U` and `H = h` on `spt V`
(`μ_V`-a.e.) for some `h ∈ C^{q,α}` in `U` (`q ∈ {0,1,2,…}`, `α ∈ (0,1)`), then for sufficiently
small `ρ > 0` the function `u` is `C^{q+2,α}(W)` and `Θⁿ(μ_V, x) = 1` on `B̆_ρ(ξ) ∩ spt V`.
(The hypotheses `H ∈ Lᵖ_loc`, `θ ≥ 1` of the first assertion are implied here.
*Erratum:* printed "`Θⁿ(μ_V, x) ≡ 1` on `B̆_ρ(ξ)`" must be restricted to `spt μ_V`, as in the third
assertion.  The third assertion (stationarity in a `C^{q+3}` submanifold `N`) is not included: as
printed, `N` is `(n+ℓ)`-dimensional in `ℝ^{n+ℓ}`, hence open, and it reduces to this one with
`h = 0`.) -/
def DensityOneHigherRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), 0 < α → α < 1 →
    V.HasGeneralizedMeanCurvature H →
    (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα (q + 2) α u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0 ∧
    ∀ x ∈ ball ξ ρ ∩ V.support, V.HasDensity x 1

/-- **Simon Ch. 5, Corollary 7.3 (p. 128).**  If `V = v(M, θ)` has generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`, and `θ` is positive
integer-valued `μ_V`-a.e. in `spt V`, then `reg V` is a relatively open dense subset of `spt V`:
it is open in `spt V`, and `spt V` is the closure, taken in `U`, of `reg V` (equivalently,
`sing V` is nowhere dense in `spt V`). -/
def RegularSetOpenDense : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p →
    (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    (∃ O : Set (Amb n ℓ), IsOpen O ∧ V.regularSet = O ∩ V.support) ∧
      V.support = closure V.regularSet ∩ U

namespace Submission

/-- **Simon Ch. 1, Upper Density Theorem 3.6** (cited fact (H2) of the a.e. tangent-plane proof),
in Mathlib's normalization `Hⁿ = μHE[n]`: if `A ⊆ ℝ^{n+ℓ}` is Borel and `ν(A) < ∞`, then
`ν(A ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0` for `Hⁿ`-a.e. `x ∉ A`.

Simon's proof, inline (SimonGMT's `Chapter01.ae_dimensionalUpperDensity_eq_zero_outside` is outside
the frozen import closure).  Fix `k` and let `Bad k` be the set of `x ∉ A` with
`ν(A ∩ B_r(x)) / rⁿ > k⁻¹` for arbitrarily small `r > 0`.  Given a closed `F ⊆ A` (closed inner
regularity of the finite measure `ν ⌞ A`) and a scale `ρ > 0`, each `x ∈ Bad k` has a radius
`r_x ∈ (0, ρ]` with `B_{r_x}(x) ∩ F = ∅` and `r_xⁿ ≤ k ν((A \ F) ∩ B_{r_x}(x))`.  The Vitali
covering lemma gives a disjoint, hence countable, subfamily `{B_{r_b}(b)}_{b ∈ u}` with
`Bad k ⊆ ⋃_{b ∈ u} B_{5 r_b}(b)`, so `Σ_b diam(B_{5 r_b}(b))ⁿ ≤ 10ⁿ k ν(A \ F)`.  Letting
`ρ → 0` and `ν(A \ F) → 0` gives `μH[n](Bad k) = 0`, hence `Hⁿ(Bad k) = 0`, and outside
`⋃_k Bad k` the quotient tends to `0`. -/
theorem aetp_upper_density_zero_ae : ∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), MeasurableSet A → ν A < ⊤ → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∉ A → Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν A hA hνA
  -- `Bad k`: points outside `A` whose density quotient exceeds `k⁻¹` at arbitrarily small radii.
  set Bad : ℕ → Set (Amb n ℓ) := fun k => {x | x ∉ A ∧ ∃ᶠ r in 𝓝[>] (0 : ℝ),
    (k : ℝ≥0∞)⁻¹ < ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)}
  -- Closed inner regularity of the finite measure `ν ⌞ A`.
  have : IsFiniteMeasure (ν.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hF : ∀ j : ℕ, ∃ F ⊆ A, IsClosed F ∧ ν (A \ F) < (j : ℝ≥0∞)⁻¹ := by
    intro j
    obtain ⟨F, hFA, hFc, hFlt⟩ := hA.exists_isClosed_sdiff_lt (μ := ν.restrict A)
      (measure_ne_top _ _) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
    refine ⟨F, hFA, hFc, ?_⟩
    rwa [Measure.restrict_apply (hA.diff hFc.measurableSet), inter_eq_left.2 sdiff_subset] at hFlt
  choose F hFA hFc hFν using hF
  -- Vitali covering of `Bad k` at scale `ρ`, avoiding a closed `G ⊆ A`.
  have hcover : ∀ (k : ℕ) (G : Set (Amb n ℓ)), G ⊆ A → IsClosed G → ∀ ρ : ℝ, 0 < ρ →
      ∃ (u : Set (Amb n ℓ)) (r : Amb n ℓ → ℝ), u.Countable ∧ (∀ b ∈ u, 0 < r b ∧ r b ≤ ρ) ∧
        Bad k ⊆ ⋃ b ∈ u, closedBall b (5 * r b) ∧
        ∑' b : u, ENNReal.ofReal (r b) ^ n ≤ k * ν (A \ G) := by
    intro k G hGA hGc ρ hρ
    have hpick : ∀ x ∈ Bad k, ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
        ENNReal.ofReal r ^ n ≤ k * ν ((A \ G) ∩ closedBall x r) := by
      rintro x ⟨hxA, hfreq⟩
      have hxG : x ∈ Gᶜ := fun hx => hxA (hGA hx)
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl x hxG
      obtain ⟨r, hlt, hr⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hρ))).exists
      refine ⟨r, hr.1, (hr.2.trans_le (min_le_right _ _)).le, ?_⟩
      have hsub : A ∩ closedBall x r = (A \ G) ∩ closedBall x r := by
        ext y
        constructor
        · rintro ⟨hyA, hyr⟩
          exact ⟨⟨hyA, fun hyG =>
            hball (closedBall_subset_ball (hr.2.trans_le (min_le_left _ _)) hyr) hyG⟩, hyr⟩
        · rintro ⟨⟨hyA, -⟩, hyr⟩
          exact ⟨hyA, hyr⟩
      rw [hsub] at hlt
      have hpos : ENNReal.ofReal (r ^ n) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact pow_pos hr.1 n
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hlt
      rw [← ENNReal.ofReal_pow hr.1.le]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Nat.cast_zero, ENNReal.inv_zero, ENNReal.top_mul hpos] at hlt
        exact absurd hlt not_top_lt
      · have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
        calc ENNReal.ofReal (r ^ n) = k * ((k : ℝ≥0∞)⁻¹ * ENNReal.ofReal (r ^ n)) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k), one_mul]
          _ ≤ k * ν ((A \ G) ∩ closedBall x r) := mul_le_mul_right hlt.le _
    choose! r hr0 hrρ hrν using hpick
    obtain ⟨u, huB, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Bad k) (fun x => x) r ρ
        hrρ 5 (by norm_num)
    have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
      ⟨b, Metric.ball_subset_interior_closedBall (mem_ball_self (hr0 b (huB hb)))⟩
    refine ⟨u, r, hucount, fun b hb => ⟨hr0 b (huB hb), hrρ b (huB hb)⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, hab⟩ := hucov a ha
      exact mem_biUnion hbu (hab (mem_closedBall_self (hr0 a ha).le))
    · calc ∑' b : u, ENNReal.ofReal (r b) ^ n
          ≤ ∑' b : u, (k : ℝ≥0∞) * ν ((A \ G) ∩ closedBall (b : Amb n ℓ) (r b)) :=
            ENNReal.tsum_le_tsum fun b => hrν b (huB b.2)
        _ = k * ∑' b : u, ν ((A \ G) ∩ closedBall (b : Amb n ℓ) (r b)) := ENNReal.tsum_mul_left
        _ = k * ν (⋃ b ∈ u, (A \ G) ∩ closedBall b (r b)) := by
            rw [measure_biUnion hucount (hudisj.mono fun b => inter_subset_right)
              fun b _ => (hA.diff hGc.measurableSet).inter measurableSet_closedBall]
        _ ≤ k * ν (A \ G) :=
            mul_le_mul_right (measure_mono (iUnion₂_subset fun b _ => inter_subset_left)) _
  -- `μH[n] (Bad k) = 0`: covers at scales `1/(j+1)` avoiding `F j`.
  have hnull : ∀ k : ℕ, (μH[n] : Measure (Amb n ℓ)) (Bad k) = 0 := by
    intro k
    choose u r hucount hur hcov hsum using fun j : ℕ =>
      hcover k (F j) (hFA j) (hFc j) (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    have hle := Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) (Bad k) (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (10 * (1 / ((j : ℝ) + 1)))) ?_
      (fun j (b : u j) => closedBall (b : Amb n ℓ) (5 * r j b)) ?_ ?_
    · have h1 : Tendsto (fun j : ℕ => (k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.natCast_ne_top k))
        rwa [mul_zero] at this
      have h2 : Tendsto (fun j : ℕ => (10 : ℝ≥0∞) ^ n * ((k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹)) atTop
          (𝓝 0) := by
        have h10 : (10 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
        have := ENNReal.Tendsto.const_mul h1 (Or.inr h10)
        rwa [mul_zero] at this
      refine nonpos_iff_eq_zero.1 (hle.trans ((liminf_le_liminf
        (Eventually.of_forall fun j => ?_)).trans h2.liminf_eq.le))
      calc ∑' b : u j, ediam (closedBall (b : Amb n ℓ) (5 * r j b)) ^ (n : ℝ)
          ≤ ∑' b : u j, (10 : ℝ≥0∞) ^ n * ENNReal.ofReal (r j b) ^ n := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            calc ediam (closedBall (b : Amb n ℓ) (5 * r j b)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (10 * r j b) ^ (n : ℝ) := by
                  refine ENNReal.rpow_le_rpow
                    (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) (Nat.cast_nonneg n)
                  have := dist_triangle_right x y b
                  rw [mem_closedBall] at hx hy
                  linarith
              _ = (10 : ℝ≥0∞) ^ n * ENNReal.ofReal (r j b) ^ n := by
                  rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul (by norm_num), mul_pow,
                    ENNReal.ofReal_ofNat]
        _ = (10 : ℝ≥0∞) ^ n * ∑' b : u j, ENNReal.ofReal (r j b) ^ n := ENNReal.tsum_mul_left
        _ ≤ (10 : ℝ≥0∞) ^ n * ((k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹) := by
            gcongr
            exact (hsum j).trans (mul_le_mul_right (hFν j).le _)
    · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10
      rw [mul_zero] at h0
      have h1 := ENNReal.tendsto_ofReal h0
      rwa [ENNReal.ofReal_zero] at h1
    · refine Eventually.of_forall fun j b => Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
      have := dist_triangle_right x y b
      have hb := (hur j b b.2).2
      rw [mem_closedBall] at hx hy
      linarith
    · refine Eventually.of_forall fun j x hx => ?_
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (hcov j hx)
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩
  -- `μHE[n] = c • μH[n]`, so `μH[n]`-null sets are `Hⁿ`-null.
  have hHE : ∀ s : Set (Amb n ℓ), (μH[n] : Measure (Amb n ℓ)) s = 0 →
      (μHE[n] : Measure (Amb n ℓ)) s = 0 := by
    intro s hs
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hs, smul_zero]
  rw [ae_iff]
  refine hHE _ (measure_mono_null ?_ (measure_iUnion_null hnull))
  intro x hx
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxA, hnt⟩ := hx
  rw [ENNReal.tendsto_nhds_zero] at hnt
  push Not at hnt
  obtain ⟨ε, hε, hfreq⟩ := hnt
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  exact mem_iUnion.2 ⟨k, hxA, hfreq.mono fun r hr => hk.trans hr⟩
/-- **Simon Ch. 3, Remark 1.8(1)** (with the boundedness of Remark 1.5(3)).  Let `V = v(M, θ)` be a
rectifiable `n`-varifold in the open set `U`, `K ⊆ M` compact with `θ|K` continuous, `x ∈ K`, and
`P` the approximate tangent space of `K` at `x` (Ch. 3, 1.4).  If
`μ_V((M \ K) ∩ B_{Rλ}(x)) / λⁿ → 0` as `λ ↓ 0` for every `R > 0`, then `P` is the approximate
tangent space of `M` with respect to `θ` at `x` (Ch. 3, 1.7). -/
theorem aetp_weightedTangent_of_lusin_compact : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (K : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), IsCompact K → K ⊆ V.carrier → x ∈ K → ContinuousOn V.mult K → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n K x P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
  intro n ℓ U hU V K x P hK hKM hxK hθK hdens hT
  refine ⟨hT.1, fun f => ?_⟩
  -- Step 1: a closed ball `B_ρ(x) ⊆ U`, bounds for `f`, and the radius `R` of its support.
  have hxU : x ∈ U := V.carrier_subset (hKM hxK)
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ > 0, closedBall x ρ ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ y, ‖f y‖ ≤ C :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  -- A cutoff `g ∈ C_c` with `0 ≤ g ≤ 1` and `g = 1` on `B_R(0)`.
  obtain ⟨g₀, hg₀1, -, hg₀cs, hg₀01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Amb n ℓ) R)
    (isOpen_ball (x := (0 : Amb n ℓ)) (ε := R + 1)).isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith)))
  let g : CompactlySupportedContinuousMap (Amb n ℓ) ℝ := ⟨g₀, hg₀cs⟩
  have hg01 : ∀ y, g y ∈ Icc (0 : ℝ) 1 := hg₀01
  -- Step 2: `Hⁿ(K) < ∞`, since `θ ≥ θ(z₀) > 0` on `K` and `θ` is integrable on `K`.
  have hθKint : IntegrableOn V.mult K (μHE[n] : Measure (Amb n ℓ)) := by
    have h := V.integrableOn_mult K hK (hKM.trans V.carrier_subset)
    rwa [inter_eq_right.mpr hKM] at h
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hK.exists_isMinOn ⟨x, hxK⟩ hθK
  have hc : 0 < V.mult z₀ := V.mult_pos z₀ (hKM hz₀K)
  have hμK : (μHE[n] : Measure (Amb n ℓ)) K < ∞ := by
    have h1 : ∫⁻ _ in K, ENNReal.ofReal (V.mult z₀) ∂(μHE[n] : Measure (Amb n ℓ)) ≤
        ∫⁻ z in K, ‖V.mult z‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) := by
      apply setLIntegral_mono' hKmeas
      intro z hz
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal ((hz₀min hz).trans (le_abs_self _))
    rw [setLIntegral_const] at h1
    exact ENNReal.lt_top_of_mul_ne_top_right (h1.trans_lt hθKint.2).ne
      (ENNReal.ofReal_pos.mpr hc).ne'
  -- Step 3: change of variables for the blow-up `η_r = blowUpMap x r`.
  have hcont : ∀ r : ℝ, Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    intro r
    show Continuous fun y => r⁻¹ • (y - x)
    fun_prop
  have hemb : ∀ r : ℝ, 0 < r → MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap x r) :=
    fun r hr => ((Homeomorph.subRight x).trans
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))).measurableEmbedding
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        ENNReal.ofReal r⁻¹ ^ n * (μHE[n] : Measure (Amb n ℓ)) T := by
    intro r hr T
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y => y - x) '' T) := by
      rw [Set.image_image]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    have hiso : Isometry (fun y : Amb n ℓ => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hmap : ∀ r : ℝ, 0 < r → ∀ S : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
        ENNReal.ofReal r⁻¹ ^ n • ((μHE[n] : Measure (Amb n ℓ)).restrict S).map
          (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    intro r hr S
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (hcont r).measurable hA,
      Measure.restrict_apply ((hcont r).measurable hA), ← hscale r hr,
      inter_comm _ S, Set.image_inter_preimage, inter_comm]
  have hcv : ∀ r : ℝ, 0 < r → ∀ (S : Set (Amb n ℓ)) (G : Amb n ℓ → ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, G y ∂(μHE[n] : Measure (Amb n ℓ)) =
        r⁻¹ ^ n * ∫ z in S, G (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro r hr S G
    rw [hmap r hr S, integral_smul_measure, (hemb r hr).integral_map, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), smul_eq_mul]
  -- Step 4: `f ∘ η_r` vanishes off `B_{Rr}(x)`, and `g ∘ η_r = 1` on `B_{Rr}(x)`.
  have hnorm : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro r hr z
    show ‖r⁻¹ • (z - x)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hf0 : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ, R * r ≤ ‖z - x‖ →
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
    intro r hr z hz
    apply hfR
    rw [hnorm r hr z, le_inv_mul_iff₀ hr]
    linarith
  have hg1 : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ, ‖z - x‖ ≤ R * r →
      g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 1 := by
    intro r hr z hz
    apply hg₀1
    rw [mem_closedBall, dist_zero_right, hnorm r hr z, inv_mul_le_iff₀ hr]
    linarith
  -- Step 5: integrability of the three integrands.
  have hfK : ∀ r : ℝ, IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) K
      (μHE[n] : Measure (Amb n ℓ)) := fun r =>
    Measure.integrableOn_of_bounded hμK.ne
      ((map_continuous f).comp (hcont r)).aestronglyMeasurable
      (M := Cf) (Eventually.of_forall fun z => hCf _)
  have hgK : ∀ r : ℝ, IntegrableOn (fun z => g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) K
      (μHE[n] : Measure (Amb n ℓ)) := fun r =>
    Measure.integrableOn_of_bounded hμK.ne
      ((map_continuous g).comp (hcont r)).aestronglyMeasurable
      (M := 1) (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (hg01 _).1]
        exact (hg01 _).2)
  have hhM : ∀ r : ℝ, 0 < r → R * r ≤ ρ →
      IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) V.carrier
        (μHE[n] : Measure (Amb n ℓ)) := by
    intro r hr hRr
    have hθint : IntegrableOn V.mult (closedBall x ρ)
        ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
      have h := V.integrableOn_mult (closedBall x ρ) (isCompact_closedBall x ρ) hρU
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact h
    have hind : (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) =
        (closedBall x ρ).indicator
          (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) := by
      funext z
      by_cases hz : z ∈ closedBall x ρ
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, hf0 r hr z ?_, zero_mul]
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        linarith
    rw [IntegrableOn, hind, integrable_indicator_iff measurableSet_closedBall]
    exact hθint.bdd_mul ((map_continuous f).comp (hcont r)).aestronglyMeasurable
      (Eventually.of_forall fun z => hCf _)
  -- Step 6: the splitting `∫_{η_r(M)} f θ(x + r ·) = θ(x) I₁ + I₂ + I₃`.
  have hdecomp : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, f y * V.mult (x + r • y)
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        V.mult x * (r⁻¹ ^ n * ∫ z in K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ))) +
        r⁻¹ ^ n * ∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z))
          ∂(μHE[n] : Measure (Amb n ℓ)) +
        r⁻¹ ^ n * ∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hRr : R * r ≤ ρ := by
      rw [lt_div_iff₀ hR] at hrρ
      linarith
    rw [hcv r hr0]
    have hback : ∀ z : Amb n ℓ, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := by
      intro z
      show x + r • (r⁻¹ • (z - x)) = z
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
    simp only [hback]
    have hint := hhM r hr0 hRr
    rw [← integral_inter_add_sdiff hKmeas hint, inter_eq_right.mpr hKM,
      integral_sub (hint.mono_set hKM) ((hfK r).const_mul (V.mult x)), integral_const_mul]
    ring
  -- Step 7: the main term converges by `T_x K = P`.
  have hT1 : Tendsto (fun r : ℝ => V.mult x * (r⁻¹ ^ n * ∫ z in K,
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))))
      (𝓝[>] 0) (𝓝 (V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)))) := by
    apply Tendsto.const_mul
    apply (hT.2 f).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hcv r hr K f
  -- Step 8: the oscillation term `I₂` tends to `0` by continuity of `θ|K` at `x`.
  have hT2 : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in K,
      (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
        V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ)))
      (𝓝[>] 0) (𝓝 0) := by
    set Lg := ∫ y in (P : Set (Amb n ℓ)), g y ∂(μHE[n] : Measure (Amb n ℓ))
    have hglim : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in K,
        g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ)))
        (𝓝[>] 0) (𝓝 Lg) := by
      apply (hT.2 g).congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hcv r hr K g
    have hgev := hglim.eventually_lt_const (lt_add_one Lg)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ Cf * ε' * (|Lg| + 1) < ε := by
      refine ⟨ε / (2 * (Cf * (|Lg| + 1) + 1)), by positivity, ?_⟩
      have hA : 0 ≤ Cf * (|Lg| + 1) := by positivity
      rw [show Cf * (ε / (2 * (Cf * (|Lg| + 1) + 1))) * (|Lg| + 1) =
          ε * (Cf * (|Lg| + 1)) / (2 * (Cf * (|Lg| + 1) + 1)) by ring,
        div_lt_iff₀ (by positivity)]
      nlinarith
    obtain ⟨δ, hδ, hθδ⟩ := Metric.continuousOn_iff.mp hθK x hxK ε' hε'0
    filter_upwards [hgev, Ioo_mem_nhdsGT (div_pos hδ hR)] with r hgr hr
    obtain ⟨hr0, hrδ⟩ := hr
    have hRr : R * r < δ := by
      rw [lt_div_iff₀ hR] at hrδ
      linarith
    have hbound : ‖∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
        V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ))‖ ≤
        ∫ z in K, Cf * ε' * g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
      apply norm_integral_le_of_norm_le ((hgK r).const_mul (Cf * ε'))
      apply ae_restrict_of_forall_mem hKmeas
      intro z hz
      have heq : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) =
          f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (V.mult z - V.mult x) := by ring
      rw [heq, norm_mul]
      by_cases hzb : ‖z - x‖ ≤ R * r
      · rw [hg1 r hr0 z hzb, mul_one]
        have h1 : dist (V.mult z) (V.mult x) < ε' :=
          hθδ z hz (by rw [dist_eq_norm]; linarith)
        rw [dist_eq_norm] at h1
        exact mul_le_mul (hCf _) h1.le (norm_nonneg _) hCf0
      · rw [not_le] at hzb
        rw [hf0 r hr0 z hzb.le, norm_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hCf0 hε'0.le) (hg01 _).1
    rw [integral_const_mul] at hbound
    have hpow : 0 ≤ r⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hr0.le) n
    rw [dist_zero_right, norm_mul, Real.norm_of_nonneg hpow]
    calc r⁻¹ ^ n * ‖∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ))‖
        ≤ r⁻¹ ^ n * (Cf * ε' * ∫ z in K, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[n] : Measure (Amb n ℓ))) := mul_le_mul_of_nonneg_left hbound hpow
      _ = Cf * ε' * (r⁻¹ ^ n * ∫ z in K, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[n] : Measure (Amb n ℓ))) := by ring
      _ ≤ Cf * ε' * (|Lg| + 1) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCf0 hε'0.le)
          linarith [le_abs_self Lg]
      _ < ε := hε'
  -- Step 9: the term `I₃` over `M \ K` tends to `0` by the density hypothesis.
  have hT3 : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in V.carrier \ K,
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂(μHE[n] : Measure (Amb n ℓ)))
      (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_iff_edist_tendsto_0]
    simp only [edist_zero_right]
    have hlim := ENNReal.Tendsto.const_mul (hdens R hR) (Or.inr (ENNReal.ofReal_ne_top (r := Cf)))
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hpt : ∀ᵐ z ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict (V.carrier \ K),
        ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun z => ENNReal.ofReal Cf * ENNReal.ofReal (V.mult z)) z := by
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem₀ V.nullMeasurableSet_carrier)] with z hz
      by_cases hzb : z ∈ closedBall x (R * r)
      · rw [indicator_of_mem hzb, enorm_mul, Real.enorm_of_nonneg (V.mult_pos z hz).le,
          ← ofReal_norm]
        gcongr
        exact hCf _
      · rw [mem_closedBall, dist_eq_norm, not_le] at hzb
        rw [hf0 r hr0 z hzb.le, zero_mul, enorm_zero]
        exact zero_le
    have hint : ‖∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
        ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ ≤
        ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) :=
      calc ‖∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
            ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ
          ≤ ∫⁻ z in V.carrier \ K, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ
            ∂(μHE[n] : Measure (Amb n ℓ)) := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ z in V.carrier \ K, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ
            ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
            rw [Measure.restrict_restrict_of_subset sdiff_subset]
        _ ≤ ∫⁻ z in V.carrier \ K, (closedBall x (R * r)).indicator
              (fun z => ENNReal.ofReal Cf * ENNReal.ofReal (V.mult z)) z
            ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := lintegral_mono_ae hpt
        _ = ENNReal.ofReal Cf * ∫⁻ z in (V.carrier \ K) ∩ closedBall x (R * r),
              ENNReal.ofReal (V.mult z) ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
            rw [lintegral_indicator measurableSet_closedBall,
              Measure.restrict_restrict measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, inter_comm (closedBall x (R * r))]
        _ ≤ ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) := by
            gcongr
            exact withDensity_apply_le _ _
    calc ‖r⁻¹ ^ n * ∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) *
          V.mult z ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ
        = (ENNReal.ofReal (r ^ n))⁻¹ * ‖∫ z in V.carrier \ K,
            f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
            ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ := by
          rw [enorm_mul, Real.enorm_of_nonneg (pow_nonneg (inv_nonneg.mpr hr0.le) n), inv_pow,
            ENNReal.ofReal_inv_of_pos (pow_pos hr0 n)]
      _ ≤ (ENNReal.ofReal (r ^ n))⁻¹ *
          (ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r))) := by
          gcongr
      _ = ENNReal.ofReal Cf * (V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) /
          ENNReal.ofReal (r ^ n)) := by
          rw [div_eq_mul_inv]
          ring
  -- Step 10: conclusion.
  have hsum := (hT1.add hT2).add hT3
  rw [add_zero, add_zero] at hsum
  exact hsum.congr' (hdecomp.mono fun r hr => hr.symm)
/-- Simon Ch. 3, Theorem 1.9 (measurability of `x ↦ p_{T_x M}`, used for Ch. 5, Lemma 2.1): for
injective `L : ℝⁿ → ℝ^{n+ℓ}` the orthogonal projection onto `L(ℝⁿ)` is `L (Lᵀ L)⁻¹ Lᵀ`, hence it
depends continuously on `L`.  Here `Lᵀ w = Σᵢ ⟨L eᵢ, w⟩ eᵢ` is the transpose, `Lᵀ L` is a unit of
`End(ℝⁿ)` because `⟨Lᵀ L v, v⟩ = |L v|²`, inversion is continuous at units, and
`w − L (Lᵀ L)⁻¹ Lᵀ w ⊥ L(ℝⁿ)` identifies the formula with `p_{L(ℝⁿ)}`. -/
theorem aetp_starProjection_range_continuousOn : ∀ (n ℓ : ℕ), ContinuousOn (fun L : Rn n →L[ℝ] Amb n ℓ => (LinearMap.range L.toLinearMap).starProjection) {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} := by
  intro n ℓ
  -- The transpose `T L = Lᵀ`, built from the standard basis `e i` of `ℝⁿ`.
  let e : Fin n → Rn n := fun i => EuclideanSpace.single i (1 : ℝ)
  let T : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Rn n) :=
    fun L => ∑ i, (innerSL ℝ (L (e i))).smulRight (e i)
  have hT : ∀ L (w : Amb n ℓ) (v : Rn n), inner ℝ (T L w) v = inner ℝ w (L v) := by
    intro L w v
    have hv : v = ∑ i, v i • e i := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
    have hTw : T L w = ∑ i, inner ℝ (L (e i)) w • e i := by
      simp [T]
    rw [hTw]
    conv_rhs => rw [hv]
    simp only [sum_inner, inner_sum, map_sum, map_smul, real_inner_smul_left,
      real_inner_smul_right, e, EuclideanSpace.inner_single_left, one_mul, map_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    ring
  have hTc : Continuous T := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun L : Rn n →L[ℝ] Amb n ℓ => innerSL ℝ (L (e i)) :=
      (innerSL ℝ).continuous.comp (continuous_id.clm_apply continuous_const)
    exact ((ContinuousLinearMap.smulRightL ℝ (Amb n ℓ) (Rn n)).continuous.comp h1).clm_apply
      continuous_const
  -- The Gram operator `A L = Lᵀ L` and the candidate projection `Q L = L (Lᵀ L)⁻¹ Lᵀ`.
  let A : (Rn n →L[ℝ] Amb n ℓ) → (Rn n →L[ℝ] Rn n) := fun L => (T L).comp L
  let Q : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ) :=
    fun L => L.comp ((Ring.inverse (A L)).comp (T L))
  -- `A L` is a unit for injective `L`: `A L v = 0` gives `|L v|² = ⟨A L v, v⟩ = 0`.
  have hA : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → IsUnit (A L) := by
    intro L hL
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro v hv
    have h0 : T L (L v) = 0 := hv
    have h1 : inner ℝ (L v) (L v) = 0 := by
      rw [← hT, h0, inner_zero_left]
    exact hL (by rw [inner_self_eq_zero.mp h1, map_zero])
  -- `Q L = p_{L(ℝⁿ)}` for injective `L`: `Q L w ∈ L(ℝⁿ)` and `Lᵀ (w − Q L w) = 0`.
  have hQ : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L →
      (LinearMap.range L.toLinearMap).starProjection = Q L := by
    intro L hL
    ext1 w
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro _ ⟨v, rfl⟩
      have h1 : T L (L (Ring.inverse (A L) (T L w))) = T L w := by
        have h2 := congrArg (fun S : Rn n →L[ℝ] Rn n => S (T L w))
          (Ring.mul_inverse_cancel _ (hA L hL))
        simpa [A] using h2
      rw [inner_sub_left, ContinuousLinearMap.coe_coe, ← hT, ← hT]
      simp only [Q, ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [h1, sub_self]
  -- `Q` is continuous at every injective `L`, since inversion is continuous at units.
  have hQc : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → ContinuousAt Q L := by
    intro L hL
    have hAc : Continuous A := hTc.clm_comp continuous_id
    obtain ⟨u, hu⟩ := hA L hL
    have hinv : ContinuousAt (fun L => Ring.inverse (A L)) L := by
      have h1 := NormedRing.inverse_continuousAt u
      rw [hu] at h1
      exact h1.comp hAc.continuousAt
    exact continuous_id.continuousAt.clm_comp (hinv.clm_comp hTc.continuousAt)
  intro L hL
  exact (hQc L hL).continuousWithinAt.congr (fun L' hL' => hQ L' hL') (hQ L hL)
/-- **Simon Ch. 3, Remark 1.8(1), first assertion** (Lusin exhaustion of a rectifiable varifold):
the carrier `M` of `V = v(M, θ)` is, up to an `Hⁿ`-null set, a countable union of compact sets
`K ⊆ M` of finite `Hⁿ`-measure on each of which `θ` is continuous.  Proof: pass to a Borel
representative `f` of `θ` and a Borel `G ⊆ M` of full measure on which `θ = f`; exhaust `U` by
compact sets `Q i`; the Borel pieces `B i k = G ∩ Q i ∩ {f > 1/(k+1)}` have finite `Hⁿ`-measure
because `θ` is integrable on `M ∩ Q i`; Lusin's theorem (Simon 1.17, proved inline through a
countable basis of `ℝ` and closed inner regularity of finite measures) gives closed, hence
compact, `C i k m ⊆ B i k` with `Hⁿ(B i k \ C i k m) < 1/m` on which `f = θ` is continuous. -/
theorem aetp_lusin_compact_exhaustion : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), ∃ K : ℕ → Set (Amb n ℓ), (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ V.carrier) ∧ (∀ m, ContinuousOn V.mult (K m)) ∧ (∀ m, (μHE[n] : Measure (Amb n ℓ)) (K m) < ⊤) ∧ (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ m, K m) = 0 := by
  intro n ℓ U hU V
  -- A Borel representative `f` of `θ`.
  set f : Amb n ℓ → ℝ := V.aemeasurable_mult.mk V.mult
  have hfm : Measurable f := V.aemeasurable_mult.measurable_mk
  have hfae : V.mult =ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier] f :=
    V.aemeasurable_mult.ae_eq_mk
  -- A Borel `G ⊆ M` of full `Hⁿ`-measure in `M` on which `θ = f`.
  obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfae)
  rw [Measure.restrict_apply hTm] at hT0
  set G : Set (Amb n ℓ) := M₁ \ T
  have hGm : MeasurableSet G := hM₁m.diff hTm
  have hGM : G ⊆ V.carrier := sdiff_subset.trans hM₁M
  have hGf : ∀ x ∈ G, V.mult x = f x := fun x hx => by_contra fun h => hx.2 (hTsub h)
  have hMG : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ G) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hM₁ae).2 hT0)
    by_cases hx₁ : x ∈ M₁
    · exact Or.inr ⟨by_contra fun h => hx.2 ⟨hx₁, h⟩, hx.1⟩
    · exact Or.inl ⟨hx.1, hx₁⟩
  -- Compact exhaustion `Q i` of `U`.
  set Q : ℕ → Set (Amb n ℓ) :=
    fun i => closedBall 0 (i : ℝ) ∩ {x | (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ}
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_infEDist)
  have hQU : ∀ i, Q i ⊆ U := by
    intro i x hx
    by_contra hxU
    have h0 : (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ := hx.2
    rw [infEDist_zero_of_mem (show x ∈ Uᶜ from hxU)] at h0
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i) (le_antisymm h0 bot_le)
  have hUQ : ∀ x ∈ U, ∃ i, x ∈ Q i := by
    intro x hx
    have h0 : infEDist x Uᶜ ≠ 0 :=
      (infEDist_pos_iff_notMem_closure.2 (by rw [hU.isClosed_compl.closure_eq]; exact fun h => h hx)).ne'
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt h0
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    refine ⟨max j k, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact hj.trans (Nat.cast_le.2 (le_max_left j k))
    · exact (ENNReal.inv_le_inv.2 (Nat.cast_le.2 (le_max_right j k))).trans hk.le
  -- Lusin's theorem (Simon 1.17) for `f` and a finite Borel measure.
  have lusin : ∀ (ν : Measure (Amb n ℓ)), IsFiniteMeasure ν → ∀ A : Set (Amb n ℓ), MeasurableSet A →
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε ∧ ContinuousOn f C := by
    intro ν hν A hA ε hε
    have : ν.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
    obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × ℚ)
    -- For each rational interval, closed sets inside the parts of `A` where `f` is in / not in it.
    have hsplit : ∀ q : ℚ × ℚ, ∃ F ⊆ A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F ∧
        ∃ F' ⊆ A \ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F' ∧ ν (A \ (F ∪ F')) ≤ δ q := by
      intro q
      have hP : MeasurableSet (A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.inter (hfm measurableSet_Ioo)
      have hN : MeasurableSet (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.diff (hfm measurableSet_Ioo)
      have hδ2 : (δ q : ℝ≥0∞) / 2 ≠ 0 :=
        (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos q).ne')).ne'
      obtain ⟨F, hFP, hFc, hF⟩ := hP.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      obtain ⟨F', hFN, hF'c, hF'⟩ := hN.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      refine ⟨F, hFP, hFc, F', hFN, hF'c, ?_⟩
      calc ν (A \ (F ∪ F'))
          ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F ∪ (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') := by
            refine measure_mono fun x hx => ?_
            by_cases hfx : f x ∈ Ioo (q.1 : ℝ) q.2
            · exact Or.inl ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inr h)⟩
        _ ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F) + ν ((A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') :=
            measure_union_le _ _
        _ ≤ δ q / 2 + δ q / 2 := add_le_add hF.le hF'.le
        _ = δ q := ENNReal.add_halves _
    choose F hFP hFc F' hFN hF'c hFF' using hsplit
    refine ⟨⋂ q, (F q ∪ F' q), fun x hx => ?_, isClosed_iInter fun q => (hFc q).union (hF'c q),
      ?_, ?_⟩
    · rcases mem_iInter.1 hx (0, 0) with h | h
      · exact (hFP _ h).1
      · exact (hFN _ h).1
    · rw [sdiff_iInter]
      calc ν (⋃ q, A \ (F q ∪ F' q)) ≤ ∑' q, ν (A \ (F q ∪ F' q)) := measure_iUnion_le _
        _ ≤ ∑' q, (δ q : ℝ≥0∞) := ENNReal.tsum_le_tsum hFF'
        _ < ε := hδsum
    · rw [Metric.continuousOn_iff]
      intro x hx e he
      obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show f x - e < f x by linarith)
      obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show f x < f x + e by linarith)
      have hxF' : x ∉ F' (a, b) := fun h => (hFN _ h).2 ⟨ha₂, hb₁⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hF'c (a, b)).isOpen_compl x hxF'
      refine ⟨r, hr, fun y hy hyx => ?_⟩
      have hyF : y ∈ F (a, b) := by
        rcases mem_iInter.1 hy (a, b) with h | h
        · exact h
        · exact absurd h (hball (mem_ball.2 hyx))
      obtain ⟨hy₁, hy₂⟩ := (hFP _ hyF).2
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
  -- The Borel pieces `B i k` have finite `Hⁿ`-measure.
  set B : ℕ → ℕ → Set (Amb n ℓ) := fun i k => G ∩ Q i ∩ {x | 1 / ((k : ℝ) + 1) < f x}
  have hBm : ∀ i k, MeasurableSet (B i k) := fun i k =>
    (hGm.inter (hQc i).isClosed.measurableSet).inter (measurableSet_lt measurable_const hfm)
  have hBfin : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k) < ⊤ := by
    intro i k
    have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hint : ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) < ⊤ :=
      Integrable.lintegral_lt_top (V.integrableOn_mult (Q i) (hQc i) (hQU i))
    have hle : ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k) ≤
        ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
      calc ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k)
          = ∫⁻ _ in B i k, ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in B i k, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            setLIntegral_mono' (hBm i k) fun x hx =>
              ENNReal.ofReal_le_ofReal (by rw [hGf x hx.1.1]; exact hx.2.le)
        _ ≤ ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            lintegral_mono_set fun x hx => ⟨hGM hx.1.1, hx.1.2⟩
    exact ENNReal.lt_top_of_mul_ne_top_right (hle.trans_lt hint).ne (ENNReal.ofReal_pos.2 hc).ne'
  -- Lusin pieces `C i k m ⊆ B i k`.
  have hC : ∀ i k m : ℕ, ∃ C ⊆ B i k, IsClosed C ∧
      (μHE[n] : Measure (Amb n ℓ)) (B i k \ C) < (m : ℝ≥0∞)⁻¹ ∧ ContinuousOn f C := by
    intro i k m
    obtain ⟨C, hCB, hCc, hCμ, hCf⟩ := lusin ((μHE[n] : Measure (Amb n ℓ)).restrict (B i k))
      (isFiniteMeasure_restrict.2 (hBfin i k).ne) (B i k) (hBm i k) (m : ℝ≥0∞)⁻¹
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    refine ⟨C, hCB, hCc, ?_, hCf⟩
    rwa [Measure.restrict_apply ((hBm i k).diff hCc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hCμ
  choose C hCB hCc hCμ hCf using hC
  have hBnull : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k \ ⋃ m, C i k m) = 0 := by
    intro i k
    by_contra h
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm hm ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ m))).trans_lt
      (hCμ i k m))
  -- Enumerate the pieces.
  refine ⟨fun j => C (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
    (Nat.unpair (Nat.unpair j).2).2, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · exact (hQc _).of_isClosed_subset (hCc _ _ _) ((hCB _ _ _).trans fun x hx => hx.1.2)
  · exact (hCB _ _ _).trans fun x hx => hGM hx.1.1
  · exact (hCf _ _ _).congr fun x hx => hGf x (hCB _ _ _ hx).1.1
  · exact (measure_mono (hCB _ _ _)).trans_lt (hBfin _ _)
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMG
      (measure_iUnion_null fun i => measure_iUnion_null fun k => hBnull i k))
    by_cases hxG : x ∈ G
    · obtain ⟨i, hi⟩ := hUQ x (V.carrier_subset hx.1)
      have hfx : 0 < f x := by rw [← hGf x hxG]; exact V.mult_pos x hx.1
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hfx
      refine Or.inr (mem_iUnion₂.2 ⟨i, k, ⟨⟨hxG, hi⟩, hk⟩, fun hxC => ?_⟩)
      obtain ⟨m, hm⟩ := mem_iUnion.1 hxC
      refine hx.2 (mem_iUnion.2 ⟨Nat.pair i (Nat.pair k m), ?_⟩)
      simpa only [Nat.unpair_pair] using hm
    · exact Or.inl ⟨hx.1, hxG⟩
/-- **Blow-up change of variables** (Simon Ch. 3, Remark 1.8(2)).  For `η = η_{x,r}`,
`η(z) = r⁻¹(z − x)`, with `r > 0`, any set `M` and any `f, θ`:
`∫_{η(M)} f(y) θ(x + r y) dHⁿ(y) = r⁻ⁿ ∫_M f(η z) θ(z) dHⁿ(z)`.  As `η` is a homeomorphism and
`Hⁿ(η(S)) = r⁻ⁿ Hⁿ(S)` for every `S`, `Hⁿ ⌞ η(M) = r⁻ⁿ η_#(Hⁿ ⌞ M)`; no integrability is needed. -/
theorem rsod_blowUp_setIntegral_eq : ∀ (n ℓ : ℕ) (M : Set (Amb n ℓ)) (f θ : Amb n ℓ → ℝ) (x : Amb n ℓ) (r : ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) = (r ^ n)⁻¹ * ∫ z in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * θ z ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ M f θ x r hr
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  -- `η` is the homeomorphism `z ↦ r⁻¹ • (z - x)`, hence a measurable embedding.
  let e : Amb n ℓ ≃ₜ Amb n ℓ :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = η := rfl
  have hemb : MeasurableEmbedding η := he ▸ e.toMeasurableEquiv.measurableEmbedding
  have hinj : Function.Injective η := he ▸ e.injective
  have hsurj : Function.Surjective η := he ▸ e.surjective
  -- `Hⁿ(η(S)) = (r⁻¹)ⁿ Hⁿ(S)` for every set `S`: a translation followed by a homothety.
  have hscale : ∀ S : Set (Amb n ℓ), μ (η '' S) = ENNReal.ofReal r⁻¹ ^ n * μ S := by
    intro S
    have hshift : Isometry (fun y : Amb n ℓ => y - x) :=
      Isometry.of_dist_eq fun a b => by simp only [dist_eq_norm, sub_sub_sub_cancel_right]
    have himage : η '' S = AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [hη, Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
      ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  -- `Hⁿ ⌞ η(M) = (r⁻¹)ⁿ η_#(Hⁿ ⌞ M)`, checked on measurable `A` via `A ∩ η(M) = η(η⁻¹(A) ∩ M)`.
  have hmeas : μ.restrict (η '' M) = (ENNReal.ofReal r⁻¹ ^ n) • (μ.restrict M).map η := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply hemb.measurable hA,
      Measure.restrict_apply (hemb.measurable hA), smul_eq_mul, ← hscale, image_inter hinj,
      image_preimage_eq A hsurj]
  -- Transfer the integral and simplify `x + r • η z = z`.
  rw [hmeas, integral_smul_measure, hemb.integral_map, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (inv_pos.mpr hr).le, inv_pow, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul, add_sub_cancel]

set_option maxHeartbeats 400000000 in
/-- **Simon Ch. 5, Theorem 6.1 (Conical approximation).**  Write `μ = μ_V`, `p_x = p_{T_x M}`,
`x^⊥ = x - p_x x`, `d = δ^{1/4}` and `L = |log λ| > 1`.

* (F1), (F2): `p_x` is `μ`-a.e. the projection onto an `n`-plane and is `μ`-a.e. strongly measurable
  (Simon Ch. 3, 1.9; the local steps of the accepted candidate for `lgc_tangent_plane_ae`, which use the
  accepted children `aetp_*` and `rsod_blowUp_setIntegral_eq`).
* (P1) For `g ∈ C¹_c` and `τ ∈ (0, 1]`, the field `X(x) = F(x) x` with `F(x) = ∫_1^{1/τ} s^{n-1} g(s x) ds`
  is admissible and `div_M X = τ⁻ⁿ g(x/τ) - g(x) - ∫_1^{1/τ} sⁿ Dg(s x)(x^⊥) ds` a.e. (fundamental theorem of
  calculus in `s`), so `∫ (τ⁻ⁿ g(x/τ) - g) dμ = ∫∫ sⁿ Dg(s x)(x^⊥) ds dμ - ∫ F ⟨x, H⟩ dμ`.
* (P2) Radial cutoffs `g_k → 1_{B_1}` in (P1) with `τ = σ` and dominated convergence give the monotonicity
  identity (3.18): `|(μ(B_1) - σ⁻ⁿ μ(B_σ)) - ∫_{B_1 \ B_σ} |x^⊥|² |x|^{-n-2} dμ| ≤ δ (2 + log σ⁻¹)`;
  (P3) is the layer-cake bound (4.11).
* (P4) For `g(y) = χ(|y|) φ(|y - ξ|)` supported in the annulus, `|J| ≤ 2|x^⊥|²|x|^{-n-2} + 4κ|x^⊥||x|^{-n-1}`
  (total variation of `χ` and length `≤ 4ρ/|x|` of the ray segment in `B_{2ρ}(ξ)`), and
  `|F| ≤ 4ρ|x|^{-n}`.
* Assembly: if `dL > 1` both inequalities follow from `μ(B_1) ≤ Λ` and (3.18).  Otherwise (P2), (P3) bound
  the three annular integrals by `C δ L`, `C L`, `δ L`, and (P4) with `φ = S((ρ - t)/(dρ))`, `χ ≡ 1` gives the
  first inequality; with `φ = S(((1+d)ρ - t)/(dρ))` and `χ_k(u) = S(k(u - 1/2)) S(k(b - u))`, `k → ∞`
  gives the second (the only boundary point of `B_{τρ}(τξ)` with `|x| = τ b` is `μ`-null).

Each of the six lemmas and the assembly is closed by the core tactic `as_aux_lemma`, which stores the
finished subproof as an auxiliary theorem (as `omega` does for its proofs); this keeps the
elaborator's memory within the bounds of the verification sandbox. -/
theorem conical_approximation_theorem : ConicalApproximationTheorem := by
  -- (P1) first variation of `X(x) = F(x) x`, `F(x) = ∫_1^{1/τ} s^{n-1} g(s x) ds`.
  have conical_P1 : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H) (hT1 : AEStronglyMeasurable V.tangentProj V.weight) (hT2 : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) (hPx : ∀ x, ‖x - V.tangentProj x x‖ ≤ ‖x‖) (g : Amb n ℓ → ℝ) (β τ : ℝ) (hg : ContDiff ℝ 1 g) (hgs : tsupport g ⊆ closedBall 0 β) (hβU : closedBall (0 : Amb n ℓ) β ⊆ U) (hτ : 0 < τ) (hτ1 : τ ≤ 1),
      ∫ x, ((τ ^ n)⁻¹ * g (τ⁻¹ • x) - g x) ∂V.weight =
            ∫ x, (∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) (x - V.tangentProj x x)) ∂V.weight -
            ∫ x, (∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)) * inner ℝ x (H x) ∂V.weight := by
    as_aux_lemma =>
      intro n ℓ hn U V H hH hT1 hT2 hPx g β τ hg hgs hβU hτ hτ1
      have hτ1' : (1 : ℝ) ≤ τ⁻¹ := one_le_inv_iff₀.2 ⟨hτ, hτ1⟩
      have hn0 : n ≠ 0 := by omega
      -- regularity of `g`
      have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
      have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
      have hgcs : HasCompactSupport g :=
        (isCompact_closedBall (0 : Amb n ℓ) β).of_isClosed_subset (isClosed_tsupport g) hgs
      obtain ⟨Cg, hCg⟩ := hg.continuous.bounded_above_of_compact_support hgcs
      obtain ⟨Cg', hCg'⟩ := hg'c.bounded_above_of_compact_support (hgcs.fderiv ℝ)
      -- outside `B_β`, `g` and `Dg` vanish
      have hg0 : ∀ y : Amb n ℓ, β < ‖y‖ → g y = 0 := by
        intro y hy
        apply image_eq_zero_of_notMem_tsupport
        intro hy'
        have := hgs hy'
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      have hg'0 : ∀ y : Amb n ℓ, β < ‖y‖ → fderiv ℝ g y = 0 := by
        intro y hy
        apply fderiv_of_notMem_tsupport
        intro hy'
        have := hgs hy'
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      have hsx : ∀ (s : ℝ) (x : Amb n ℓ), 1 ≤ s → ‖x‖ ≤ ‖s • x‖ := by
        intro s x hs
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        nlinarith [norm_nonneg x]
      -- the radial potential `F` and its derivative `F'`
      set F : Amb n ℓ → ℝ := fun x => ∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x) with hFdef
      set F' : Amb n ℓ → (Amb n ℓ →L[ℝ] ℝ) :=
        fun x => ∫ s in (1 : ℝ)..τ⁻¹, (s ^ n) • fderiv ℝ g (s • x) with hF'def
      have hF'int : ∀ x, IntervalIntegrable (fun s : ℝ => (s ^ n) • fderiv ℝ g (s • x)) volume 1 τ⁻¹ := by
        intro x
        apply Continuous.intervalIntegrable
        exact (continuous_pow n).smul (hg'c.comp (continuous_id.smul continuous_const))
      have hFderiv : ∀ x, HasFDerivAt F (F' x) x := by
        intro x
        have hpt : ∀ (s : ℝ) (y : Amb n ℓ), HasFDerivAt (fun y => s ^ (n - 1) * g (s • y))
            ((s ^ n) • fderiv ℝ g (s • y)) y := by
          intro s y
          have h1 : HasFDerivAt (fun y : Amb n ℓ => s • y) (s • ContinuousLinearMap.id ℝ (Amb n ℓ)) y :=
            (hasFDerivAt_id y).const_smul s
          have h2 := ((hgd (s • y)).hasFDerivAt.comp y h1).const_mul (s ^ (n - 1))
          refine h2.congr_fderiv ?_
          ext v
          simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
            Function.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]
          rw [← pow_sub_one_mul hn0 s]
          ring
        have hIoc : ∀ y : Amb n ℓ, F y = ∫ s in Ioc (1 : ℝ) τ⁻¹, s ^ (n - 1) * g (s • y) :=
          fun y => intervalIntegral.integral_of_le hτ1'
        have hIoc' : F' x = ∫ s in Ioc (1 : ℝ) τ⁻¹, (s ^ n) • fderiv ℝ g (s • x) :=
          intervalIntegral.integral_of_le hτ1'
        have hFeq : F = fun y => ∫ s in Ioc (1 : ℝ) τ⁻¹, s ^ (n - 1) * g (s • y) := funext hIoc
        rw [hFeq, hIoc']
        have hfin : volume (Ioc (1 : ℝ) τ⁻¹) < ⊤ := measure_Ioc_lt_top
        have : IsFiniteMeasure (volume.restrict (Ioc (1 : ℝ) τ⁻¹)) := isFiniteMeasure_restrict.2 hfin.ne
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le
          (μ := volume.restrict (Ioc (1 : ℝ) τ⁻¹)) (F := fun y s => s ^ (n - 1) * g (s • y))
          (F' := fun y s => (s ^ n) • fderiv ℝ g (s • y)) (x₀ := x) (s := univ)
          (bound := fun _ => (τ⁻¹) ^ n * Cg') Filter.univ_mem
          (Eventually.of_forall fun y => (Continuous.aestronglyMeasurable (by fun_prop)))
          ?_ ?_ ?_ (integrable_const _) ?_
        · exact (Continuous.integrableOn_Ioc (by fun_prop))
        · exact Continuous.aestronglyMeasurable
            ((continuous_pow n).smul (hg'c.comp (continuous_id.smul continuous_const)))
        · refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs y _ => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (by linarith [hs.1])]
          exact mul_le_mul (pow_le_pow_left₀ (by linarith [hs.1]) hs.2 n) (hCg' _)
            (norm_nonneg _) (pow_nonneg (by linarith [hτ1']) n)
        · exact Eventually.of_forall fun s y _ => hpt s y
      -- `F` is `C¹`
      have hF'cont : Continuous F' := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x s => (s ^ n) • fderiv ℝ g (s • x))
        exact ((continuous_pow n).comp continuous_snd).smul
          (hg'c.comp (continuous_snd.smul continuous_fst))
      have hFcd : ContDiff ℝ 1 F := by
        rw [contDiff_one_iff_fderiv]
        refine ⟨fun x => (hFderiv x).differentiableAt, ?_⟩
        have : fderiv ℝ F = F' := funext fun x => (hFderiv x).fderiv
        rw [this]; exact hF'cont
      -- the vector field `X(x) = F(x) x`
      set X : Amb n ℓ → Amb n ℓ := fun x => F x • x with hXdef
      have hXcd : ContDiff ℝ 1 X := hFcd.smul contDiff_id
      have hXderiv : ∀ x, HasFDerivAt X
          (F x • ContinuousLinearMap.id ℝ (Amb n ℓ) + (F' x).smulRight x) x :=
        fun x => (hFderiv x).smul (hasFDerivAt_id x)
      -- support of `X`, `F`, `F'`
      have hF0 : ∀ x : Amb n ℓ, β < ‖x‖ → F x = 0 := by
        intro x hx
        simp only [hFdef]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
        intro s hs
        rw [uIcc_of_le hτ1'] at hs
        simp only
        rw [hg0 _ (lt_of_lt_of_le hx (hsx s x hs.1)), mul_zero]
      have hF'0 : ∀ x : Amb n ℓ, β < ‖x‖ → F' x = 0 := by
        intro x hx
        simp only [hF'def]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : Amb n ℓ →L[ℝ] ℝ)) ?_,
          intervalIntegral.integral_zero]
        intro s hs
        rw [uIcc_of_le hτ1'] at hs
        simp only
        rw [hg'0 _ (lt_of_lt_of_le hx (hsx s x hs.1)), smul_zero]
      have hXsupp : tsupport X ⊆ closedBall 0 β := by
        refine closure_minimal (fun x hx => ?_) isClosed_closedBall
        rw [mem_closedBall, dist_zero_right]
        by_contra h
        push Not at h
        exact hx (by simp only [hXdef, hF0 x h, zero_smul])
      have hXcs : HasCompactSupport X :=
        (isCompact_closedBall 0 β).of_isClosed_subset (isClosed_tsupport X) hXsupp
      have key := hH.2 X hXcd hXcs (hXsupp.trans hβU)
      -- traces
      have htrP : ∀ P : Submodule ℝ (Amb n ℓ),
          LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
        intro P
        rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
        have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
            LinearMap.id := by
          ext x; simp
        rw [hcomp, LinearMap.trace_id]
      have htr : ∀ (P : Submodule ℝ (Amb n ℓ)) (a : ℝ) (φ : Amb n ℓ →L[ℝ] ℝ) (u : Amb n ℓ),
          LinearMap.trace ℝ (Amb n ℓ) ((a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
              φ.smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap) =
            a * Module.finrank ℝ P + φ (P.starProjection u) := by
        intro P a φ u
        have hcomp : (a • ContinuousLinearMap.id ℝ (Amb n ℓ) + φ.smulRight u).toLinearMap ∘ₗ
              P.starProjection.toLinearMap =
            a • P.starProjection.toLinearMap +
              (φ.toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight u := by
          ext w; simp
        rw [hcomp, map_add, map_smul, LinearMap.trace_smulRight, htrP]
        simp
      -- the fundamental theorem of calculus in `s`
      have hFTC : ∀ x : Amb n ℓ, (τ ^ n)⁻¹ * g (τ⁻¹ • x) - g x = n * F x + F' x x := by
        intro x
        have hd : ∀ s ∈ uIcc (1 : ℝ) τ⁻¹, HasDerivAt (fun s : ℝ => s ^ n * g (s • x))
            ((n : ℝ) * s ^ (n - 1) * g (s • x) + s ^ n * fderiv ℝ g (s • x) x) s := by
          intro s _
          have h1 : HasDerivAt (fun s : ℝ => g (s • x)) (fderiv ℝ g (s • x) x) s := by
            have := (hgd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
            rw [one_smul] at this
            exact this
          have h2 := (hasDerivAt_pow n s).mul h1
          convert h2 using 1
        have hint1 : IntervalIntegrable (fun s : ℝ => (n : ℝ) * (s ^ (n - 1) * g (s • x))) volume 1 τ⁻¹ :=
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        have hint2 : IntervalIntegrable (fun s : ℝ => s ^ n * fderiv ℝ g (s • x) x) volume 1 τ⁻¹ :=
          Continuous.intervalIntegrable ((continuous_pow n).mul
            ((hg'c.comp (continuous_id.smul continuous_const)).clm_apply continuous_const)) _ _
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
          have := hint1.add hint2
          refine this.congr ?_
          intro s _
          simp only
          ring)
        have happ : F' x x = ∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) x := by
          simp only [hF'def]
          rw [ContinuousLinearMap.intervalIntegral_apply (hF'int x) x]
          simp
        rw [happ, show (n : ℝ) * F x = ∫ s in (1 : ℝ)..τ⁻¹, (n : ℝ) * (s ^ (n - 1) * g (s • x)) by
          simp only [hFdef]; rw [intervalIntegral.integral_const_mul],
          ← intervalIntegral.integral_add hint1 hint2]
        rw [show (fun s : ℝ => (n : ℝ) * (s ^ (n - 1) * g (s • x)) + s ^ n * fderiv ℝ g (s • x) x) =
            fun s : ℝ => (n : ℝ) * s ^ (n - 1) * g (s • x) + s ^ n * fderiv ℝ g (s • x) x by
          funext s; ring, hftc]
        simp [inv_pow]
      -- finiteness of the weight of `B_β`
      have hμβ : V.weight (closedBall 0 β) < ⊤ := by
        rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
          Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
        exact (V.integrableOn_mult _ (isCompact_closedBall 0 β) hβU).setLIntegral_lt_top
      -- measurability of `x ↦ x - p_x x`
      have happ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × Amb n ℓ => p.1 p.2) :=
        isBoundedBilinearMap_apply.continuous
      have hperp_meas : AEStronglyMeasurable (fun x => x - V.tangentProj x x) V.weight :=
        aestronglyMeasurable_id.sub
          (happ.comp_aestronglyMeasurable (hT1.prodMk aestronglyMeasurable_id))
      set J : Amb n ℓ → ℝ :=
        fun x => ∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) (x - V.tangentProj x x) with hJdef
      have hJeq : ∀ x, J x = F' x (x - V.tangentProj x x) := by
        intro x
        simp only [hJdef, hF'def]
        rw [ContinuousLinearMap.intervalIntegral_apply (hF'int x)]
        simp
      set L : Amb n ℓ → ℝ := fun x => (τ ^ n)⁻¹ * g (τ⁻¹ • x) - g x with hLdef
      -- integrability
      have hLsupp : Function.support L ⊆ closedBall 0 β := by
        intro x hx
        rw [mem_closedBall, dist_zero_right]
        by_contra h
        push Not at h
        apply hx
        simp only [hLdef]
        rw [hg0 x h, hg0 (τ⁻¹ • x) (lt_of_lt_of_le h (hsx _ x hτ1'))]
        simp
      have hL_int : Integrable L V.weight := by
        rw [← integrableOn_iff_integrable_of_support_subset hLsupp]
        refine Measure.integrableOn_of_bounded (M := (τ ^ n)⁻¹ * Cg + Cg) hμβ.ne
          (Continuous.aestronglyMeasurable (by simp only [hLdef]; fun_prop))
          (Eventually.of_forall fun x => ?_)
        simp only [hLdef]
        calc ‖(τ ^ n)⁻¹ * g (τ⁻¹ • x) - g x‖ ≤ ‖(τ ^ n)⁻¹ * g (τ⁻¹ • x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ (τ ^ n)⁻¹ * Cg + Cg := by
            rw [norm_mul, Real.norm_of_nonneg (by positivity)]
            exact add_le_add (mul_le_mul_of_nonneg_left (hCg _) (by positivity)) (hCg _)
      have hF'bound : ∀ x, ‖F' x‖ ≤ (τ⁻¹) ^ n * Cg' * |τ⁻¹ - 1| := by
        intro x
        simp only [hF'def]
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [uIoc_of_le hτ1'] at hs
        rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (by linarith [hs.1])]
        exact mul_le_mul (pow_le_pow_left₀ (by linarith [hs.1]) hs.2 n) (hCg' _) (norm_nonneg _)
          (pow_nonneg (by linarith [hτ1']) n)
      have hJsupp : Function.support J ⊆ closedBall 0 β := by
        intro x hx
        rw [mem_closedBall, dist_zero_right]
        by_contra h
        push Not at h
        apply hx
        rw [hJeq, hF'0 x h]
        simp
      have hJ_int : Integrable J V.weight := by
        rw [← integrableOn_iff_integrable_of_support_subset hJsupp]
        have hJm : AEStronglyMeasurable J V.weight := by
          have : J = fun x => F' x (x - V.tangentProj x x) := funext hJeq
          rw [this]
          exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
            (hF'cont.aestronglyMeasurable.prodMk hperp_meas)
        refine Measure.integrableOn_of_bounded (M := (τ⁻¹) ^ n * Cg' * |τ⁻¹ - 1| * β) hμβ.ne hJm ?_
        refine (ae_restrict_mem measurableSet_closedBall).mono fun x hx => ?_
        rw [hJeq]
        calc ‖F' x (x - V.tangentProj x x)‖ ≤ ‖F' x‖ * ‖x - V.tangentProj x x‖ := (F' x).le_opNorm _
          _ ≤ (τ⁻¹) ^ n * Cg' * |τ⁻¹ - 1| * β := by
            apply mul_le_mul (hF'bound x) _ (norm_nonneg _) (le_trans (norm_nonneg _) (hF'bound x))
            rw [mem_closedBall, dist_zero_right] at hx
            exact (hPx x).trans hx
      -- the tangential divergence of `X`
      have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = L x - J x := by
        filter_upwards [hT2] with x hx
        obtain ⟨Q, hQn, hQx⟩ := hx
        rw [RectifiableVarifold.divM, (hXderiv x).fderiv, hQx, htr, hQn, hJeq, hQx]
        have := hFTC x
        simp only [hLdef]
        rw [this, map_sub]
        ring
      have hXH : ∀ x, inner ℝ (X x) (H x) = F x * inner ℝ x (H x) := by
        intro x
        simp only [hXdef]
        exact real_inner_smul_left _ _ _
      have hint_div : ∫ x, V.divM X x ∂V.weight = ∫ x, L x ∂V.weight - ∫ x, J x ∂V.weight := by
        rw [integral_congr_ae hdiv, integral_sub hL_int hJ_int]
      have key' := key
      simp only [hXH] at key'
      linarith
  -- (P3) layer cake (Simon Ch. 4, 4.11).
  have conical_P3 : ∀ {n ℓ : ℕ} (ν : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (m : ℕ) (a R K : ℝ) (ha : 0 < a) (haR : a ≤ R) (hνR : ν (closedBall 0 R) < ⊤) (hw0 : ∀ x, 0 ≤ w x) (hw : IntegrableOn w (closedBall 0 R) ν) (hK : ∀ t ∈ Icc a R, ∫ x in closedBall (0 : Amb n ℓ) t, w x ∂ν ≤ K * t ^ m),
      ∫ x in closedBall (0 : Amb n ℓ) R \ closedBall 0 a, (‖x‖ ^ m)⁻¹ * w x ∂ν ≤
            K * (1 + m * Real.log (R / a)) := by
    as_aux_lemma =>
      intro n ℓ ν w m a R K ha haR hνR hw0 hw hK
      set A := closedBall (0 : Amb n ℓ) R \ closedBall 0 a with hA
      have hR : 0 < R := lt_of_lt_of_le ha haR
      have hAm : MeasurableSet A := measurableSet_closedBall.diff measurableSet_closedBall
      have hAR : A ⊆ closedBall 0 R := sdiff_subset
      have hwA : IntegrableOn w A ν := hw.mono_set hAR
      have hK0 : 0 ≤ K := by
        have h1 := hK a ⟨le_rfl, haR⟩
        have h2 : 0 ≤ ∫ x in closedBall (0 : Amb n ℓ) a, w x ∂ν := setIntegral_nonneg
          measurableSet_closedBall fun x _ => hw0 x
        have h3 : 0 < a ^ m := pow_pos ha m
        by_contra hneg
        push Not at hneg
        have : K * a ^ m < 0 := mul_neg_of_neg_of_pos hneg h3
        linarith
      -- `f(x, t) = m t^{-m-1}` if `‖x‖ < t`
      set f : Amb n ℓ → ℝ → ℝ := fun x t => if ‖x‖ < t then (m : ℝ) * (t ^ (m + 1))⁻¹ else 0
        with hfdef
      -- the pointwise identity `‖x‖^{-m} = R^{-m} + ∫_{(a, R]} f(x, t) dt` on `A`
      have hpt : ∀ x ∈ A, (‖x‖ ^ m)⁻¹ = (R ^ m)⁻¹ + ∫ t in Ioc a R, f x t := by
        intro x hx
        rw [hA, Set.mem_sdiff, mem_closedBall, dist_zero_right, mem_closedBall, dist_zero_right,
          not_le] at hx
        have hx0 : 0 < ‖x‖ := lt_trans ha hx.2
        have hset : ∫ t in Ioc a R, f x t = ∫ t in Ioc ‖x‖ R, (m : ℝ) * (t ^ (m + 1))⁻¹ := by
          rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
          congr 1
          funext t
          simp only [indicator, mem_Ioc, hfdef]
          by_cases h1 : ‖x‖ < t
          · by_cases h2 : t ≤ R
            · simp [h1, h2, lt_trans hx.2 h1]
            · simp [h2]
          · simp [h1]
        rw [hset, ← intervalIntegral.integral_of_le hx.1]
        have hd : ∀ t ∈ uIcc ‖x‖ R, HasDerivAt (fun t : ℝ => -(t ^ m)⁻¹) ((m : ℝ) * (t ^ (m + 1))⁻¹) t := by
          intro t ht
          rw [uIcc_of_le hx.1] at ht
          have ht0 : t ≠ 0 := (lt_of_lt_of_le hx0 ht.1).ne'
          have h := ((hasDerivAt_pow m t).inv (pow_ne_zero m ht0)).neg
          convert h using 1
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; simp
          · rw [neg_div, neg_neg, ← pow_mul, show m * 2 = (m - 1) + (m + 1) by omega, pow_add]
            have h1 : t ^ (m - 1) ≠ 0 := pow_ne_zero _ ht0
            have h2 : t ^ (m + 1) ≠ 0 := pow_ne_zero _ ht0
            field_simp
            rw [← pow_succ, ← pow_add]
            congr 1
            omega
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
        · ring
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.inv₀ (continuousOn_pow _)
          intro t ht
          rw [uIcc_of_le hx.1] at ht
          exact pow_ne_zero _ (lt_of_lt_of_le hx0 ht.1).ne'
      -- bounds on `f`
      have hc0 : 0 ≤ (m : ℝ) * (a ^ (m + 1))⁻¹ :=
        mul_nonneg (Nat.cast_nonneg m) (inv_nonneg.2 (pow_nonneg ha.le _))
      have hνA : IsFiniteMeasure (ν.restrict A) :=
        ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact (measure_mono hAR).trans_lt hνR⟩
      have hfb : ∀ x t, t ∈ Ioc a R → 0 ≤ f x t ∧ f x t ≤ (m : ℝ) * (a ^ (m + 1))⁻¹ := by
        intro x t ht
        simp only [hfdef]
        split_ifs
        · refine ⟨mul_nonneg (Nat.cast_nonneg m) (inv_nonneg.2 (pow_nonneg (lt_trans ha ht.1).le _)), ?_⟩
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
          exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le ht.1.le _)
        · exact ⟨le_rfl, hc0⟩
      have hfm : Measurable (Function.uncurry f) := by
        simp only [hfdef, Function.uncurry_def]
        refine Measurable.ite (measurableSet_lt (measurable_norm.comp measurable_fst) measurable_snd)
          ?_ measurable_const
        exact measurable_const.mul ((measurable_snd.pow_const _).inv)
      have hfin : IsFiniteMeasure (volume.restrict (Ioc a R)) :=
        isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      -- integrability on the product
      have hprod : Integrable (Function.uncurry fun x t => f x t * w x)
          ((ν.restrict A).prod (volume.restrict (Ioc a R))) := by
        have hG : Integrable (fun z : Amb n ℓ × ℝ => ((m : ℝ) * (a ^ (m + 1))⁻¹ * w z.1) * (1 : ℝ))
            ((ν.restrict A).prod (volume.restrict (Ioc a R))) :=
          (hwA.const_mul _).mul_prod (integrable_const (1 : ℝ))
        refine hG.mono' ?_ ?_
        · exact hfm.aestronglyMeasurable.mul hwA.aestronglyMeasurable.comp_fst
        · have hmem : ∀ᵐ z ∂((ν.restrict A).prod (volume.restrict (Ioc a R))), z.2 ∈ Ioc a R := by
            rw [Measure.ae_prod_iff_ae_ae]
            · exact Eventually.of_forall fun x => ae_restrict_mem measurableSet_Ioc
            · exact measurable_snd measurableSet_Ioc
          filter_upwards [hmem] with z hz
          rw [show Function.uncurry (fun x t => f x t * w x) z = f z.1 z.2 * w z.1 from rfl, mul_one,
            Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfb z.1 z.2 hz).1 (hw0 z.1))]
          exact mul_le_mul_of_nonneg_right (hfb z.1 z.2 hz).2 (hw0 z.1)
      -- splitting off the constant term
      have hint1 : IntegrableOn (fun x => (∫ t in Ioc a R, f x t) * w x) A ν := by
        refine Integrable.mono' (hwA.const_mul ((m : ℝ) * (a ^ (m + 1))⁻¹ * (R - a))) ?_ ?_
        · exact (hprod.integral_prod_left.congr (Eventually.of_forall fun x => by
            simp only [Function.uncurry_apply_pair]
            exact integral_mul_const _ _)).aestronglyMeasurable
        · refine Eventually.of_forall fun x => ?_
          rw [norm_mul, Real.norm_of_nonneg (hw0 x)]
          apply mul_le_mul_of_nonneg_right _ (hw0 x)
          calc ‖∫ t in Ioc a R, f x t‖ ≤ (m : ℝ) * (a ^ (m + 1))⁻¹ * volume.real (Ioc a R) := by
                apply norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top
                intro t ht
                rw [Real.norm_of_nonneg (hfb x t ht).1]
                exact (hfb x t ht).2
            _ = (m : ℝ) * (a ^ (m + 1))⁻¹ * (R - a) := by
                rw [Real.volume_real_Ioc_of_le haR]
      have hsplit : ∫ x in A, (‖x‖ ^ m)⁻¹ * w x ∂ν =
          (R ^ m)⁻¹ * ∫ x in A, w x ∂ν + ∫ x in A, (∫ t in Ioc a R, f x t) * w x ∂ν := by
        rw [← integral_const_mul, ← integral_add (hwA.const_mul _) hint1]
        apply setIntegral_congr_fun hAm
        intro x hx
        simp only
        rw [hpt x hx]
        ring
      have hfub : ∫ x in A, (∫ t in Ioc a R, f x t) * w x ∂ν =
          ∫ t in Ioc a R, (∫ x in A, f x t * w x ∂ν) := by
        have : ∀ x, (∫ t in Ioc a R, f x t) * w x = ∫ t in Ioc a R, f x t * w x :=
          fun x => (integral_mul_const _ _).symm
        simp_rw [this]
        exact integral_integral_swap hprod
      -- the inner bound `∫_A f(x, t) w(x) dν ≤ m K / t`
      have hinner : ∀ t ∈ Ioc a R, ∫ x in A, f x t * w x ∂ν ≤ (m : ℝ) * K * t⁻¹ := by
        intro t ht
        have ht0 : 0 < t := lt_trans ha ht.1
        have hBt : closedBall (0 : Amb n ℓ) t ⊆ closedBall 0 R := closedBall_subset_closedBall ht.2
        calc ∫ x in A, f x t * w x ∂ν
            ≤ ∫ x in closedBall (0 : Amb n ℓ) t, (m : ℝ) * (t ^ (m + 1))⁻¹ * w x ∂ν := by
              rw [← integral_indicator hAm, ← integral_indicator measurableSet_closedBall]
              apply integral_mono_of_nonneg
              · refine Eventually.of_forall fun x => ?_
                simp only [indicator]
                split_ifs
                · exact mul_nonneg (hfb x t ht).1 (hw0 x)
                · exact le_rfl
              · rw [integrable_indicator_iff measurableSet_closedBall]
                exact (hw.mono_set hBt).const_mul _
              · refine Eventually.of_forall fun x => ?_
                simp only [indicator, hfdef]
                by_cases hxA : x ∈ A
                · by_cases hxt : ‖x‖ < t
                  · have : x ∈ closedBall (0 : Amb n ℓ) t := by
                      rw [mem_closedBall, dist_zero_right]; exact hxt.le
                    simp [hxA, hxt, this]
                  · simp [hxA, hxt]
                    split_ifs
                    · exact mul_nonneg (by positivity) (hw0 x)
                    · exact le_rfl
                · simp only [hxA, ite_false]
                  split_ifs
                  · exact mul_nonneg (by positivity) (hw0 x)
                  · exact le_rfl
          _ = (m : ℝ) * (t ^ (m + 1))⁻¹ * ∫ x in closedBall (0 : Amb n ℓ) t, w x ∂ν :=
              integral_const_mul _ _
          _ ≤ (m : ℝ) * (t ^ (m + 1))⁻¹ * (K * t ^ m) :=
              mul_le_mul_of_nonneg_left (hK t ⟨ht.1.le, ht.2⟩) (by positivity)
          _ = (m : ℝ) * K * t⁻¹ := by
              rw [pow_succ]
              field_simp
      have hwAR : ∫ x in A, w x ∂ν ≤ K * R ^ m :=
        (setIntegral_mono_set hw (Eventually.of_forall fun x => hw0 x)
          (Eventually.of_forall hAR)).trans (hK R ⟨haR, le_rfl⟩)
      calc ∫ x in A, (‖x‖ ^ m)⁻¹ * w x ∂ν
          = (R ^ m)⁻¹ * ∫ x in A, w x ∂ν + ∫ t in Ioc a R, (∫ x in A, f x t * w x ∂ν) := by
            rw [hsplit, hfub]
        _ ≤ (R ^ m)⁻¹ * (K * R ^ m) + ∫ t in Ioc a R, (m : ℝ) * K * t⁻¹ := by
            apply add_le_add (mul_le_mul_of_nonneg_left hwAR (by positivity))
            apply integral_mono_of_nonneg
            · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
              exact integral_nonneg fun x => mul_nonneg (hfb x t ht).1 (hw0 x)
            · apply ContinuousOn.integrableOn_Icc (continuousOn_const.mul (continuousOn_inv₀.mono
                fun t ht => (lt_of_lt_of_le ha ht.1).ne')) |>.mono_set Ioc_subset_Icc_self
            · exact (ae_restrict_mem measurableSet_Ioc).mono hinner
        _ = K * (1 + m * Real.log (R / a)) := by
            rw [← intervalIntegral.integral_of_le haR, intervalIntegral.integral_const_mul,
              integral_inv_of_pos ha hR]
            field_simp
  -- `d/ds (sⁿ g(s x)) = n s^{n-1} g(s x) + sⁿ Dg(s x) x`, integrated over `[1, 1/τ]`.
  have conical_FTC : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) (g : Amb n ℓ → ℝ) (hg : ContDiff ℝ 1 g) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (x : Amb n ℓ),
      (τ ^ n)⁻¹ * g (τ⁻¹ • x) - g x = n * (∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)) +
            ∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) x := by
    as_aux_lemma =>
      intro n ℓ hn g hg τ hτ hτ1 x
      have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
      have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
      have hd : ∀ s ∈ uIcc (1 : ℝ) τ⁻¹, HasDerivAt (fun s : ℝ => s ^ n * g (s • x))
          ((n : ℝ) * s ^ (n - 1) * g (s • x) + s ^ n * fderiv ℝ g (s • x) x) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ => g (s • x)) (fderiv ℝ g (s • x) x) s := by
          have := (hgd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
          rw [one_smul] at this
          exact this
        have h2 := (hasDerivAt_pow n s).mul h1
        convert h2 using 1
      have hint1 : IntervalIntegrable (fun s : ℝ => (n : ℝ) * (s ^ (n - 1) * g (s • x))) volume 1 τ⁻¹ :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      have hint2 : IntervalIntegrable (fun s : ℝ => s ^ n * fderiv ℝ g (s • x) x) volume 1 τ⁻¹ :=
        Continuous.intervalIntegrable ((continuous_pow n).mul
          ((hg'c.comp (continuous_id.smul continuous_const)).clm_apply continuous_const)) _ _
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
        have := hint1.add hint2
        refine this.congr ?_
        intro s _
        simp only
        ring)
      rw [show (n : ℝ) * (∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)) =
          ∫ s in (1 : ℝ)..τ⁻¹, (n : ℝ) * (s ^ (n - 1) * g (s • x)) by
        rw [intervalIntegral.integral_const_mul], ← intervalIntegral.integral_add hint1 hint2]
      rw [show (fun s : ℝ => (n : ℝ) * (s ^ (n - 1) * g (s • x)) + s ^ n * fderiv ℝ g (s • x) x) =
          fun s : ℝ => (n : ℝ) * s ^ (n - 1) * g (s • x) + s ^ n * fderiv ℝ g (s • x) x by
        funext s; ring, hftc]
      simp [inv_pow]
  -- (P2) the monotonicity identity (Simon Ch. 4, 3.18) on `B_1 \ B_σ`.
  have conical_P2 : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) {U : Set (Amb n ℓ)} (hU : IsOpen U) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H) (hT1 : AEStronglyMeasurable V.tangentProj V.weight) (hT2 : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) (hPx : ∀ x, ‖x - V.tangentProj x x‖ ≤ ‖x‖) (hPi : ∀ x, inner ℝ x (x - V.tangentProj x x) = ‖x - V.tangentProj x x‖ ^ 2) (hB1 : closedBall (0 : Amb n ℓ) 1 ⊆ U) (σ δ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hHδ : ∀ t ∈ Icc σ 1, ∫ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ ∂V.weight ≤ δ * t ^ (n - 1)),
      |((V.weight (closedBall 0 1)).toReal - (V.weight (closedBall 0 σ)).toReal / σ ^ n) -
            ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
              ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight| ≤
            δ * (2 + Real.log σ⁻¹) := by
    as_aux_lemma =>
      intro n ℓ hn U hU V H hH hT1 hT2 hPx hPi hB1 σ δ hσ hσ1 hHδ
      have hσ1' : (1 : ℝ) ≤ σ⁻¹ := one_le_inv_iff₀.2 ⟨hσ, hσ1⟩
      have hn0 : n ≠ 0 := by omega
      -- Step 0: a slightly larger closed ball `B_{R'}` inside `U`
      obtain ⟨ε, hε, hεU⟩ :=
        (isCompact_closedBall (0 : Amb n ℓ) 1).exists_cthickening_subset_open hU hB1
      rw [cthickening_closedBall hε.le zero_le_one] at hεU
      set R' : ℝ := ε + 1 with hR'
      have hR'1 : 1 < R' := by linarith
      have hμR' : V.weight (closedBall 0 R') < ⊤ := by
        rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
          Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
        exact (V.integrableOn_mult _ (isCompact_closedBall 0 R') hεU).setLIntegral_lt_top
      have hμ1 : V.weight (closedBall 0 1) < ⊤ :=
        (measure_mono (closedBall_subset_closedBall hR'1.le)).trans_lt hμR'
      have hHint : IntegrableOn H (closedBall 0 R') V.weight :=
        hH.1.integrableOn_compact_subset hεU (isCompact_closedBall 0 R')
      -- Step 1: the radial cutoffs `γ_k`, equal to `1` on `(-∞, 1]` and `0` on `[1 + η_k, ∞)`
      obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun k : ℕ => ε / ((k : ℝ) + 1) := ⟨_, rfl⟩
      have hη : ∀ k, 0 < η k := fun k => by rw [hηdef]; exact div_pos hε (by positivity)
      have hηε : ∀ k, η k ≤ ε := fun k => by
        rw [hηdef]; exact div_le_self hε.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      obtain ⟨γ, hγdef⟩ : ∃ γ : ℕ → ℝ → ℝ, γ = fun k u => 1 - Real.smoothTransition ((u - 1) / η k) :=
        ⟨_, rfl⟩
      have hγ1 : ∀ k u, u ≤ 1 → γ k u = 1 := by
        intro k u hu
        simp only [hγdef]
        rw [Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) (hη k).le)]
        ring
      have hγ0 : ∀ k u, 1 + η k ≤ u → γ k u = 0 := by
        intro k u hu
        simp only [hγdef]
        rw [Real.smoothTransition.one_of_one_le ((one_le_div (hη k)).2 (by linarith))]
        ring
      have hγb : ∀ k u, 0 ≤ γ k u ∧ γ k u ≤ 1 := by
        intro k u
        simp only [hγdef]
        constructor <;> linarith [Real.smoothTransition.le_one ((u - 1) / η k),
          Real.smoothTransition.nonneg ((u - 1) / η k)]
      obtain ⟨γi, hγidef⟩ : ∃ γi : ℝ → ℝ, γi = fun u => if u ≤ 1 then 1 else 0 := ⟨_, rfl⟩
      have hγlim : ∀ u, Tendsto (fun k => γ k u) atTop (𝓝 (γi u)) := by
        intro u
        by_cases hu : u ≤ 1
        · simp only [hγidef, hu, ite_true]
          exact tendsto_const_nhds.congr (fun k => (hγ1 k u hu).symm)
        · push Not at hu
          simp only [hγidef, not_le.2 hu, ite_false]
          apply tendsto_const_nhds.congr'
          have hev : ∀ᶠ k : ℕ in atTop, η k ≤ u - 1 := by
            obtain ⟨N, hN⟩ := exists_nat_gt (ε / (u - 1))
            filter_upwards [eventually_ge_atTop N] with k hk
            simp only [hηdef]
            have hk' : (N : ℝ) ≤ k := Nat.cast_le.2 hk
            rw [div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ (by linarith)] at hN
            nlinarith
          filter_upwards [hev] with k hk
          exact (hγ0 k u (by linarith)).symm
      have hγcd : ∀ k, ContDiff ℝ 1 (γ k) := by
        intro k
        simp only [hγdef]
        exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
          ((contDiff_id.sub contDiff_const).div_const _))
      obtain ⟨g, hgdef⟩ : ∃ g : ℕ → Amb n ℓ → ℝ, g = fun k y => γ k ‖y‖ := ⟨_, rfl⟩
      have hgcd : ∀ k, ContDiff ℝ 1 (g k) := by
        intro k
        rw [contDiff_iff_contDiffAt]
        intro y
        by_cases hy : y = 0
        · apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
          filter_upwards [ball_mem_nhds y one_pos] with z hz
          rw [hy, mem_ball, dist_zero_right] at hz
          simp only [hgdef]
          exact hγ1 k _ hz.le
        · rw [hgdef]
          exact (hγcd k).contDiffAt.comp y (contDiffAt_norm ℝ hy)
      have hgb : ∀ k y, 0 ≤ g k y ∧ g k y ≤ 1 := fun k y => by rw [hgdef]; exact hγb k ‖y‖
      have hglim : ∀ y, Tendsto (fun k => g k y) atTop (𝓝 (γi ‖y‖)) := fun y => by
        simp only [hgdef]; exact hγlim ‖y‖
      have hg0 : ∀ k (y : Amb n ℓ), R' < ‖y‖ → g k y = 0 := by
        intro k y hy
        simp only [hgdef]
        exact hγ0 k _ (by linarith [hηε k])
      have hgsupp : ∀ k, tsupport (g k) ⊆ closedBall 0 R' := by
        intro k
        refine closure_minimal (fun y hy => ?_) isClosed_closedBall
        rw [mem_closedBall, dist_zero_right]
        by_contra h
        push Not at h
        exact hy (hg0 k y h)
      -- derivative of the norm and of `g k` away from the origin
      have hnormd : ∀ y : Amb n ℓ, y ≠ 0 →
          HasFDerivAt (fun z : Amb n ℓ => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
        intro y hy
        have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
        have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt y
          (hasFDerivAt_id y).norm_sq
        convert h using 1
        · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
        · ext v; simp [Real.sqrt_sq hr.le]; field_simp
      have hgderiv : ∀ k (y : Amb n ℓ), y ≠ 0 → ∀ v,
          fderiv ℝ (g k) y v = deriv (γ k) ‖y‖ * (‖y‖⁻¹ * inner ℝ y v) := by
        intro k y hy v
        have h1 : HasDerivAt (γ k) (deriv (γ k) ‖y‖) ‖y‖ :=
          ((hγcd k).differentiable one_ne_zero _).hasDerivAt
        have h2 := h1.comp_hasFDerivAt y (hnormd y hy)
        rw [show g k = γ k ∘ (fun z => ‖z‖) by rw [hgdef]; rfl, h2.fderiv]
        simp [smul_eq_mul]
      -- Step 2: the first variation identity for each `g k`
      obtain ⟨q, hqdef⟩ : ∃ q : Amb n ℓ → ℝ, q = fun x => ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ 2 :=
        ⟨_, rfl⟩
      set L : ℕ → Amb n ℓ → ℝ := fun k x => (σ ^ n)⁻¹ * g k (σ⁻¹ • x) - g k x with hLdef
      set F : ℕ → Amb n ℓ → ℝ := fun k x => ∫ s in (1 : ℝ)..σ⁻¹, s ^ (n - 1) * g k (s • x)
        with hFdef
      have hJ : ∀ k x,
          (∫ s in (1 : ℝ)..σ⁻¹, s ^ n * fderiv ℝ (g k) (s • x) (x - V.tangentProj x x)) =
            q x * (L k x - n * F k x) := by
        intro k x
        have hftc := conical_FTC hn (g k) (hgcd k) σ hσ hσ1 x
        simp only [hLdef, hFdef]
        rw [hftc, add_sub_cancel_left]
        by_cases hx : x = 0
        · subst hx
          simp [hqdef]
        · rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hσ1'] at hs
          have hs0 : 0 < s := by linarith [hs.1]
          have hsx : s • x ≠ 0 := smul_ne_zero hs0.ne' hx
          have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
          simp only
          rw [hgderiv k _ hsx, hgderiv k _ hsx, norm_smul, Real.norm_of_nonneg hs0.le,
            real_inner_smul_left, real_inner_smul_left, hPi x, real_inner_self_eq_norm_sq]
          simp only [hqdef]
          field_simp
      have hid : ∀ k, ∫ x, L k x ∂V.weight =
          ∫ x, q x * (L k x - n * F k x) ∂V.weight - ∫ x, F k x * inner ℝ x (H x) ∂V.weight := by
        intro k
        have h := conical_P1 hn V H hH hT1 hT2 hPx (g k) R' σ (hgcd k) (hgsupp k) hεU hσ hσ1
        simp only [hJ] at h
        exact h
      -- Step 3: the limits `k → ∞`
      set Li : Amb n ℓ → ℝ := fun x => (σ ^ n)⁻¹ * γi ‖σ⁻¹ • x‖ - γi ‖x‖ with hLidef
      set Fi : Amb n ℓ → ℝ := fun x => ∫ s in (1 : ℝ)..σ⁻¹, s ^ (n - 1) * γi ‖s • x‖ with hFidef
      have hgc : ∀ k, Continuous (g k) := fun k => (hgcd k).continuous
      have hpb : ∀ k (x : Amb n ℓ) (s : ℝ), s ∈ uIoc (1 : ℝ) σ⁻¹ →
          ‖s ^ (n - 1) * g k (s • x)‖ ≤ (σ⁻¹) ^ (n - 1) := by
        intro k x s hs
        rw [uIoc_of_le hσ1'] at hs
        rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (by linarith [hs.1]) _),
          Real.norm_of_nonneg (hgb k _).1]
        calc s ^ (n - 1) * g k (s • x) ≤ (σ⁻¹) ^ (n - 1) * 1 :=
              mul_le_mul (pow_le_pow_left₀ (by linarith [hs.1]) hs.2 _) (hgb k _).2 (hgb k _).1
                (by positivity)
          _ = _ := mul_one _
      have hLlim : ∀ x, Tendsto (fun k => L k x) atTop (𝓝 (Li x)) := fun x =>
        ((hglim _).const_mul _).sub (hglim _)
      have hFlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (Fi x)) := by
        intro x
        apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (fun _ => (σ⁻¹) ^ (n - 1))
        · exact Eventually.of_forall fun k => (Continuous.aestronglyMeasurable
            ((continuous_pow _).mul ((hgc k).comp (continuous_id.smul continuous_const))))
        · exact Eventually.of_forall fun k => Eventually.of_forall fun s hs => hpb k x s hs
        · exact intervalIntegrable_const
        · exact Eventually.of_forall fun s _ => (hglim _).const_mul _
      set CF : ℝ := (σ⁻¹) ^ (n - 1) * (σ⁻¹ - 1) with hCF
      have hLb : ∀ k x, |L k x| ≤ (σ ^ n)⁻¹ + 1 := by
        intro k x
        simp only [hLdef]
        have h1 := hgb k (σ⁻¹ • x)
        have h2 := hgb k x
        have hσn : 0 < (σ ^ n)⁻¹ := by positivity
        calc |(σ ^ n)⁻¹ * g k (σ⁻¹ • x) - g k x| ≤ |(σ ^ n)⁻¹ * g k (σ⁻¹ • x)| + |g k x| := by
              simpa only [Real.norm_eq_abs] using norm_sub_le ((σ ^ n)⁻¹ * g k (σ⁻¹ • x)) (g k x)
          _ ≤ (σ ^ n)⁻¹ + 1 := by
              rw [abs_mul, abs_of_pos hσn, abs_of_nonneg h1.1, abs_of_nonneg h2.1]
              exact add_le_add (mul_le_of_le_one_right hσn.le h1.2) h2.2
      have hFb : ∀ k x, |F k x| ≤ CF := by
        intro k x
        simp only [hFdef]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := σ⁻¹)
          (C := (σ⁻¹) ^ (n - 1)) (f := fun s => s ^ (n - 1) * g k (s • x))
          (fun s hs => hpb k x s hs)
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ⁻¹ - 1)] at this
        exact this
      have hsx : ∀ (s : ℝ) (x : Amb n ℓ), 1 ≤ s → ‖x‖ ≤ ‖s • x‖ := by
        intro s x hs
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        calc ‖x‖ = 1 * ‖x‖ := (one_mul _).symm
          _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg x)
      have hL0 : ∀ k x, R' < ‖x‖ → L k x = 0 := by
        intro k x hx
        simp only [hLdef]
        rw [hg0 k x hx, hg0 k _ (lt_of_lt_of_le hx (hsx _ x hσ1'))]
        ring
      have hF0 : ∀ k x, R' < ‖x‖ → F k x = 0 := by
        intro k x hx
        simp only [hFdef]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
        intro s hs
        rw [uIcc_of_le hσ1'] at hs
        simp only
        rw [hg0 k _ (lt_of_lt_of_le hx (hsx s x hs.1)), mul_zero]
      have hq1 : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := by
        intro x
        simp only [hqdef]
        refine ⟨by positivity, ?_⟩
        rcases eq_or_ne x 0 with hx | hx
        · subst hx; simp
        · rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hPx x) 2
      -- measurability
      have happ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × Amb n ℓ => p.1 p.2) :=
        isBoundedBilinearMap_apply.continuous
      have hperp_meas : AEStronglyMeasurable (fun x => x - V.tangentProj x x) V.weight :=
        aestronglyMeasurable_id.sub
          (happ.comp_aestronglyMeasurable (hT1.prodMk aestronglyMeasurable_id))
      have hq_meas : AEStronglyMeasurable q V.weight := by
        simp only [hqdef]
        exact ((hperp_meas.aemeasurable.norm.pow_const 2).div
          (measurable_norm.pow_const 2).aemeasurable).aestronglyMeasurable
      have hLc : ∀ k, Continuous (L k) := fun k => by
        have hgck := hgc k
        simp only [hLdef]
        fun_prop
      have hFc : ∀ k, Continuous (F k) := fun k => by
        simp only [hFdef]
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x s => s ^ (n - 1) * g k (s • x))
        exact ((continuous_pow _).comp continuous_snd).mul
          ((hgc k).comp (continuous_snd.smul continuous_fst))
      have hind : ∀ c : ℝ, Integrable ((closedBall (0 : Amb n ℓ) R').indicator (fun _ => c))
          V.weight := by
        intro c
        rw [integrable_indicator_iff measurableSet_closedBall]
        exact integrableOn_const hμR'.ne
      -- dominated convergence for the three integrals
      have hlim1 : Tendsto (fun k => ∫ x, L k x ∂V.weight) atTop (𝓝 (∫ x, Li x ∂V.weight)) := by
        apply tendsto_integral_of_dominated_convergence
          ((closedBall (0 : Amb n ℓ) R').indicator (fun _ => (σ ^ n)⁻¹ + 1))
        · exact fun k => (hLc k).aestronglyMeasurable
        · exact hind _
        · intro k
          refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ closedBall (0 : Amb n ℓ) R'
          · rw [indicator_of_mem hx, Real.norm_eq_abs]
            exact hLb k x
          · rw [indicator_of_notMem hx]
            rw [mem_closedBall, dist_zero_right, not_le] at hx
            rw [hL0 k x hx, norm_zero]
        · exact Eventually.of_forall hLlim
      have hlim2 : Tendsto (fun k => ∫ x, q x * (L k x - n * F k x) ∂V.weight) atTop
          (𝓝 (∫ x, q x * (Li x - n * Fi x) ∂V.weight)) := by
        apply tendsto_integral_of_dominated_convergence
          ((closedBall (0 : Amb n ℓ) R').indicator (fun _ => (σ ^ n)⁻¹ + 1 + n * CF))
        · exact fun k => hq_meas.mul ((hLc k).sub (continuous_const.mul (hFc k))).aestronglyMeasurable
        · exact hind _
        · intro k
          refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ closedBall (0 : Amb n ℓ) R'
          · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
            have h1 := hq1 x
            have h2 : |L k x - n * F k x| ≤ (σ ^ n)⁻¹ + 1 + n * CF := by
              calc |L k x - n * F k x| ≤ |L k x| + |n * F k x| := by
                    simpa only [Real.norm_eq_abs] using norm_sub_le (L k x) (n * F k x)
                _ ≤ (σ ^ n)⁻¹ + 1 + n * CF := by
                  rw [abs_mul (n : ℝ) (F k x), Nat.abs_cast]
                  exact add_le_add (hLb k x) (mul_le_mul_of_nonneg_left (hFb k x) (Nat.cast_nonneg n))
            rw [abs_of_nonneg h1.1]
            calc q x * |L k x - n * F k x| ≤ 1 * ((σ ^ n)⁻¹ + 1 + n * CF) :=
                  mul_le_mul h1.2 h2 (abs_nonneg _) zero_le_one
              _ = _ := one_mul _
          · rw [indicator_of_notMem hx]
            rw [mem_closedBall, dist_zero_right, not_le] at hx
            rw [hL0 k x hx, hF0 k x hx]
            simp
        · exact Eventually.of_forall fun x => ((hLlim x).sub ((hFlim x).const_mul _)).const_mul _
      have hlim3 : Tendsto (fun k => ∫ x, F k x * inner ℝ x (H x) ∂V.weight) atTop
          (𝓝 (∫ x, Fi x * inner ℝ x (H x) ∂V.weight)) := by
        apply tendsto_integral_of_dominated_convergence
          ((closedBall (0 : Amb n ℓ) R').indicator (fun x => CF * (R' * ‖H x‖)))
        · intro k
          have heq : (fun x => F k x * inner ℝ x (H x)) =
              (closedBall (0 : Amb n ℓ) R').indicator (fun x => F k x * inner ℝ x (H x)) := by
            funext x
            by_cases hx : x ∈ closedBall (0 : Amb n ℓ) R'
            · rw [indicator_of_mem hx]
            · rw [indicator_of_notMem hx]
              rw [mem_closedBall, dist_zero_right, not_le] at hx
              rw [hF0 k x hx, zero_mul]
          rw [heq, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
          exact (hFc k).aestronglyMeasurable.mul (continuous_inner.comp_aestronglyMeasurable
            (aestronglyMeasurable_id.prodMk hHint.aestronglyMeasurable))
        · rw [integrable_indicator_iff measurableSet_closedBall]
          exact (hHint.norm.const_mul R').const_mul CF
        · intro k
          refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ closedBall (0 : Amb n ℓ) R'
          · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs]
            have hxR : ‖x‖ ≤ R' := by rwa [mem_closedBall, dist_zero_right] at hx
            apply mul_le_mul (hFb k x) _ (norm_nonneg _) (le_trans (abs_nonneg _) (hFb k x))
            calc ‖inner ℝ x (H x)‖ ≤ ‖x‖ * ‖H x‖ := norm_inner_le_norm _ _
              _ ≤ R' * ‖H x‖ := mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
          · rw [indicator_of_notMem hx]
            rw [mem_closedBall, dist_zero_right, not_le] at hx
            rw [hF0 k x hx]
            simp
        · exact Eventually.of_forall fun x => (hFlim x).mul_const _
      have hlimid : ∫ x, Li x ∂V.weight = ∫ x, q x * (Li x - n * Fi x) ∂V.weight -
          ∫ x, Fi x * inner ℝ x (H x) ∂V.weight := by
        have h' : Tendsto (fun k => ∫ x, L k x ∂V.weight) atTop
            (𝓝 (∫ x, q x * (Li x - n * Fi x) ∂V.weight - ∫ x, Fi x * inner ℝ x (H x) ∂V.weight)) :=
          (hlim2.sub hlim3).congr (fun k => (hid k).symm)
        exact tendsto_nhds_unique hlim1 h'
      -- Step 4: evaluation of the limit integrals
      have hnorm : ∀ (s : ℝ) (x : Amb n ℓ), 0 ≤ s → ‖s • x‖ = s * ‖x‖ := fun s x hs => by
        rw [norm_smul, Real.norm_of_nonneg hs]
      have hFi_c : ∀ (x : Amb n ℓ) (c : ℝ), 1 ≤ c → c ≤ σ⁻¹ →
          (∀ s, 1 < s → s ≤ c → s * ‖x‖ ≤ 1) → (∀ s, c < s → s ≤ σ⁻¹ → 1 < s * ‖x‖) →
          Fi x = (c ^ n - 1) / n := by
        intro x c hc1 hcσ h1 h2
        simp only [hFidef]
        rw [intervalIntegral.integral_of_le hσ1']
        have hcongr : ∫ s in Ioc (1 : ℝ) σ⁻¹, s ^ (n - 1) * γi ‖s • x‖ =
            ∫ s in Ioc (1 : ℝ) σ⁻¹, (Ioc (1 : ℝ) c).indicator (fun s => s ^ (n - 1)) s := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          simp only [hγidef]
          by_cases hsc : s ≤ c
          · rw [indicator_of_mem (show s ∈ Ioc (1 : ℝ) c from ⟨hs.1, hsc⟩), hnorm s x (by linarith [hs.1]),
              if_pos (h1 s hs.1 hsc), mul_one]
          · rw [indicator_of_notMem (fun h => hsc h.2), hnorm s x (by linarith [hs.1]),
              if_neg (not_le.2 (h2 s (not_le.1 hsc) hs.2)), mul_zero]
        rw [hcongr, setIntegral_indicator measurableSet_Ioc,
          inter_eq_right.2 (Ioc_subset_Ioc_right hcσ), ← intervalIntegral.integral_of_le hc1,
          integral_pow, Nat.sub_add_cancel hn, one_pow, Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
      have hFi_formula : ∀ x : Amb n ℓ, Fi x = if ‖x‖ ≤ σ then ((σ⁻¹) ^ n - 1) / n
          else if ‖x‖ ≤ 1 then ((‖x‖⁻¹) ^ n - 1) / n else 0 := by
        intro x
        split_ifs with hxσ hx1
        · exact hFi_c x σ⁻¹ hσ1' le_rfl
            (fun s _ hs => by
              calc s * ‖x‖ ≤ σ⁻¹ * σ := mul_le_mul hs hxσ (norm_nonneg _) (by positivity)
                _ = 1 := inv_mul_cancel₀ hσ.ne')
            (fun s hs1 hs2 => absurd hs2 (not_le.2 hs1))
        · push Not at hxσ
          have hx0 : 0 < ‖x‖ := lt_trans hσ hxσ
          exact hFi_c x ‖x‖⁻¹ (one_le_inv_iff₀.2 ⟨hx0, hx1⟩) (inv_anti₀ hσ hxσ.le)
            (fun s _ hs => by
              calc s * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
                _ = 1 := inv_mul_cancel₀ hx0.ne')
            (fun s hs1 _ => by
              calc (1 : ℝ) = ‖x‖⁻¹ * ‖x‖ := (inv_mul_cancel₀ hx0.ne').symm
                _ < s * ‖x‖ := mul_lt_mul_of_pos_right hs1 hx0)
        · push Not at hxσ hx1
          have h := hFi_c x 1 le_rfl hσ1' (fun s hs1 hs2 => absurd hs2 (not_le.2 hs1))
            (fun s hs1 _ => by
              calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
                _ < s * ‖x‖ := mul_lt_mul'' hs1 hx1 zero_le_one zero_le_one)
          rw [h, one_pow, sub_self, zero_div]
      have hLi_formula : ∀ x : Amb n ℓ, Li x =
          (σ ^ n)⁻¹ * (if ‖x‖ ≤ σ then 1 else 0) - (if ‖x‖ ≤ 1 then 1 else 0) := by
        intro x
        simp only [hLidef, hγidef, hnorm _ x (inv_nonneg.2 hσ.le), inv_mul_le_iff₀ hσ, mul_one]
      have hint_ind : ∀ r, r ≤ R' →
          IntegrableOn (fun _ => (1 : ℝ)) (closedBall (0 : Amb n ℓ) r) V.weight := fun r hr =>
        integrableOn_const ((measure_mono (closedBall_subset_closedBall hr)).trans_lt hμR').ne
      have hLi_int : ∫ x, Li x ∂V.weight =
          (σ ^ n)⁻¹ * (V.weight (closedBall 0 σ)).toReal - (V.weight (closedBall 0 1)).toReal := by
        have heq : Li = fun x => (σ ^ n)⁻¹ *
            (closedBall (0 : Amb n ℓ) σ).indicator (fun _ => (1 : ℝ)) x -
            (closedBall (0 : Amb n ℓ) 1).indicator (fun _ => (1 : ℝ)) x := by
          funext x
          rw [hLi_formula x]
          simp only [indicator, mem_closedBall, dist_zero_right]
        rw [heq, integral_sub, integral_const_mul, integral_indicator measurableSet_closedBall,
          integral_indicator measurableSet_closedBall, setIntegral_const, setIntegral_const]
        · simp [Measure.real]
        · exact ((integrable_indicator_iff measurableSet_closedBall).2
            (hint_ind σ (by linarith))).const_mul _
        · exact (integrable_indicator_iff measurableSet_closedBall).2 (hint_ind 1 hR'1.le)
      obtain ⟨Iann, hIanndef⟩ : ∃ Iann : Amb n ℓ → ℝ,
          Iann = fun x => ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) := ⟨_, rfl⟩
      have hAnnm : MeasurableSet (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ) :=
        measurableSet_closedBall.diff measurableSet_closedBall
      have hpt : ∀ x, q x * (Li x - n * Fi x) =
          -((closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ).indicator Iann x) := by
        intro x
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
        rw [hLi_formula x, hFi_formula x]
        by_cases hxσ : ‖x‖ ≤ σ
        · have hxA : x ∉ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ := fun h =>
            h.2 (by rw [mem_closedBall, dist_zero_right]; exact hxσ)
          rw [if_pos hxσ, if_pos hxσ, if_pos (le_trans hxσ hσ1), indicator_of_notMem hxA, inv_pow]
          field_simp
          ring
        · by_cases hx1 : ‖x‖ ≤ 1
          · have hx0 : 0 < ‖x‖ := lt_trans hσ (not_le.1 hxσ)
            have hxA : x ∈ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ :=
              ⟨by rw [mem_closedBall, dist_zero_right]; exact hx1,
                by rw [mem_closedBall, dist_zero_right]; exact hxσ⟩
            rw [if_neg hxσ, if_neg hxσ, if_pos hx1, if_pos hx1, indicator_of_mem hxA]
            simp only [hqdef, hIanndef]
            rw [pow_add, inv_pow]
            field_simp
            ring
          · have hxA : x ∉ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ := fun h =>
              hx1 (by have := h.1; rwa [mem_closedBall, dist_zero_right] at this)
            rw [if_neg hxσ, if_neg hxσ, if_neg hx1, if_neg hx1, indicator_of_notMem hxA]
            ring
      have hq_int : ∫ x, q x * (Li x - n * Fi x) ∂V.weight =
          -∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ, Iann x ∂V.weight := by
        rw [integral_congr_ae (Eventually.of_forall hpt), integral_neg, integral_indicator hAnnm]
      -- Step 5: the curvature term
      have hδ0 : 0 ≤ δ := by
        have h1 := hHδ σ ⟨le_rfl, hσ1⟩
        have h2 : 0 ≤ ∫ x in closedBall (0 : Amb n ℓ) σ, ‖H x‖ ∂V.weight :=
          setIntegral_nonneg measurableSet_closedBall fun x _ => norm_nonneg _
        have h3 : 0 < σ ^ (n - 1) := pow_pos hσ _
        by_contra h
        push Not at h
        have : δ * σ ^ (n - 1) < 0 := mul_neg_of_neg_of_pos h h3
        linarith
      have hHB1 : IntegrableOn (fun x => ‖H x‖) (closedBall (0 : Amb n ℓ) 1) V.weight :=
        (hHint.mono_set (closedBall_subset_closedBall hR'1.le)).norm
      have hP3 := conical_P3 V.weight (fun x => ‖H x‖) (n - 1) σ 1 δ hσ hσ1 hμ1
        (fun x => norm_nonneg _) hHB1 hHδ
      have hb1 : IntegrableOn (fun x => (σ ^ n)⁻¹ * σ / n * ‖H x‖) (closedBall (0 : Amb n ℓ) σ)
          V.weight :=
        ((hHint.mono_set (closedBall_subset_closedBall (by linarith))).norm.const_mul
          ((σ ^ n)⁻¹ * σ / n))
      have hb2 : IntegrableOn (fun x => (‖x‖ ^ (n - 1))⁻¹ / n * ‖H x‖)
          (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ) V.weight := by
        refine Integrable.mono' ((hHB1.mono_set sdiff_subset).const_mul ((σ ^ (n - 1))⁻¹ / n)) ?_ ?_
        · exact (((measurable_norm.pow_const _).inv.div_const _).aestronglyMeasurable).mul
            (hHB1.mono_set sdiff_subset).aestronglyMeasurable
        · refine (ae_restrict_mem hAnnm).mono fun x hx => ?_
          have hxσ : σ < ‖x‖ := by
            have := hx.2
            rwa [mem_closedBall, dist_zero_right, not_le] at this
          rw [norm_mul, Real.norm_of_nonneg (by positivity), norm_norm]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
          exact inv_anti₀ (pow_pos hσ _) (pow_le_pow_left₀ hσ.le hxσ.le _)
      obtain ⟨b, hbdef⟩ : ∃ b : Amb n ℓ → ℝ, b = fun x =>
          (closedBall (0 : Amb n ℓ) σ).indicator (fun x => (σ ^ n)⁻¹ * σ / n * ‖H x‖) x +
          (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ).indicator
            (fun x => (‖x‖ ^ (n - 1))⁻¹ / n * ‖H x‖) x := ⟨_, rfl⟩
      have hb_int : Integrable b V.weight := by
        rw [hbdef]
        exact ((integrable_indicator_iff measurableSet_closedBall).2 hb1).add
          ((integrable_indicator_iff hAnnm).2 hb2)
      have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      have hFi_nonneg : ∀ x, 0 ≤ Fi x := by
        intro x
        rw [hFi_formula x]
        split_ifs with h1 h2
        · apply div_nonneg _ hn'.le
          rw [sub_nonneg]
          exact one_le_pow₀ hσ1'
        · push Not at h1
          apply div_nonneg _ hn'.le
          rw [sub_nonneg]
          exact one_le_pow₀ (one_le_inv_iff₀.2 ⟨lt_trans hσ h1, h2⟩)
        · exact le_rfl
      have hbpt : ∀ x, ‖Fi x * inner ℝ x (H x)‖ ≤ b x := by
        intro x
        rw [norm_mul, Real.norm_of_nonneg (hFi_nonneg x)]
        have hin : ‖inner ℝ x (H x)‖ ≤ ‖x‖ * ‖H x‖ := norm_inner_le_norm _ _
        rw [hbdef]
        by_cases hxσ : ‖x‖ ≤ σ
        · have hmem : x ∈ closedBall (0 : Amb n ℓ) σ := by
            rw [mem_closedBall, dist_zero_right]; exact hxσ
          have hnmem : x ∉ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ := fun h => h.2 hmem
          simp only [indicator_of_mem hmem, indicator_of_notMem hnmem, add_zero]
          rw [hFi_formula x, if_pos hxσ]
          calc ((σ⁻¹) ^ n - 1) / n * ‖inner ℝ x (H x)‖ ≤ ((σ⁻¹) ^ n) / n * (σ * ‖H x‖) := by
                apply mul_le_mul (div_le_div_of_nonneg_right (by linarith) hn'.le)
                  (hin.trans (mul_le_mul_of_nonneg_right hxσ (norm_nonneg _))) (norm_nonneg _)
                  (by positivity)
            _ = (σ ^ n)⁻¹ * σ / n * ‖H x‖ := by rw [inv_pow]; ring
        · push Not at hxσ
          by_cases hx1 : ‖x‖ ≤ 1
          · have hx0 : 0 < ‖x‖ := lt_trans hσ hxσ
            have hmem : x ∈ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ :=
              ⟨by rw [mem_closedBall, dist_zero_right]; exact hx1,
                by rw [mem_closedBall, dist_zero_right, not_le]; exact hxσ⟩
            have hnmem : x ∉ closedBall (0 : Amb n ℓ) σ := fun h => hmem.2 h
            simp only [indicator_of_mem hmem, indicator_of_notMem hnmem, zero_add]
            rw [hFi_formula x, if_neg (not_le.2 hxσ), if_pos hx1]
            calc ((‖x‖⁻¹) ^ n - 1) / n * ‖inner ℝ x (H x)‖ ≤
                  ((‖x‖⁻¹) ^ n) / n * (‖x‖ * ‖H x‖) := by
                  apply mul_le_mul (div_le_div_of_nonneg_right (by linarith) hn'.le) hin
                    (norm_nonneg _) (by positivity)
              _ = (‖x‖ ^ (n - 1))⁻¹ / n * ‖H x‖ := by
                  rw [inv_pow]
                  have : ‖x‖ ^ n = ‖x‖ ^ (n - 1) * ‖x‖ := (pow_sub_one_mul hn0 _).symm
                  rw [this]
                  field_simp
          · push Not at hx1
            have hnmem1 : x ∉ closedBall (0 : Amb n ℓ) σ := fun h => by
              rw [mem_closedBall, dist_zero_right] at h; linarith
            have hnmem2 : x ∉ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ := fun h => by
              have := h.1; rw [mem_closedBall, dist_zero_right] at this; linarith
            simp only [indicator_of_notMem hnmem1, indicator_of_notMem hnmem2, add_zero]
            rw [hFi_formula x, if_neg (not_le.2 hxσ), if_neg (not_le.2 hx1)]
            simp
      have hlog : 0 ≤ Real.log σ⁻¹ := Real.log_nonneg hσ1'
      have hbint_val : ∫ x, b x ∂V.weight ≤ δ * (2 + Real.log σ⁻¹) := by
        rw [hbdef, integral_add ((integrable_indicator_iff measurableSet_closedBall).2 hb1)
          ((integrable_indicator_iff hAnnm).2 hb2), integral_indicator measurableSet_closedBall,
          integral_indicator hAnnm]
        have e1 : ∫ x in closedBall (0 : Amb n ℓ) σ, (σ ^ n)⁻¹ * σ / n * ‖H x‖ ∂V.weight ≤ δ / n := by
          rw [integral_const_mul]
          calc (σ ^ n)⁻¹ * σ / n * ∫ x in closedBall (0 : Amb n ℓ) σ, ‖H x‖ ∂V.weight ≤
                (σ ^ n)⁻¹ * σ / n * (δ * σ ^ (n - 1)) :=
                mul_le_mul_of_nonneg_left (hHδ σ ⟨le_rfl, hσ1⟩) (by positivity)
            _ = δ / n := by
              have : σ ^ n = σ ^ (n - 1) * σ := (pow_sub_one_mul hn0 σ).symm
              rw [this]
              field_simp
        have e2 : ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
            (‖x‖ ^ (n - 1))⁻¹ / n * ‖H x‖ ∂V.weight ≤
            δ * (1 + ((n - 1 : ℕ) : ℝ) * Real.log σ⁻¹) / n := by
          have hfun : (fun x : Amb n ℓ => (‖x‖ ^ (n - 1))⁻¹ / n * ‖H x‖) =
              fun x => (1 / (n : ℝ)) * ((‖x‖ ^ (n - 1))⁻¹ * ‖H x‖) := by
            funext x; ring
          rw [hfun, integral_const_mul]
          have h := hP3
          rw [one_div σ] at h
          calc 1 / (n : ℝ) * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
                (‖x‖ ^ (n - 1))⁻¹ * ‖H x‖ ∂V.weight ≤
                1 / (n : ℝ) * (δ * (1 + ((n - 1 : ℕ) : ℝ) * Real.log σ⁻¹)) :=
                mul_le_mul_of_nonneg_left h (by positivity)
            _ = _ := by ring
        have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
        calc _ ≤ δ / n + δ * (1 + ((n - 1 : ℕ) : ℝ) * Real.log σ⁻¹) / n := add_le_add e1 e2
          _ ≤ δ * (2 + Real.log σ⁻¹) := by
            rw [Nat.cast_sub hn, Nat.cast_one, ← add_div, div_le_iff₀ hn']
            have hkey : (2 + Real.log σ⁻¹) * n - (2 + (n - 1) * Real.log σ⁻¹) =
                2 * n - 2 + Real.log σ⁻¹ := by ring
            have hle : 2 + (n - 1) * Real.log σ⁻¹ ≤ (2 + Real.log σ⁻¹) * n := by linarith
            calc δ + δ * (1 + (n - 1) * Real.log σ⁻¹) = δ * (2 + (n - 1) * Real.log σ⁻¹) := by ring
              _ ≤ δ * ((2 + Real.log σ⁻¹) * n) := mul_le_mul_of_nonneg_left hle hδ0
              _ = δ * (2 + Real.log σ⁻¹) * n := by ring
      have hE : |∫ x, Fi x * inner ℝ x (H x) ∂V.weight| ≤ δ * (2 + Real.log σ⁻¹) := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_of_norm_le hb_int (Eventually.of_forall hbpt)).trans hbint_val
      rw [hLi_int, hq_int] at hlimid
      have hIeq : ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
          ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight =
          ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ, Iann x ∂V.weight := by
        rw [hIanndef]
      rw [hIeq, div_eq_inv_mul]
      have hfinal : ((V.weight (closedBall 0 1)).toReal - (σ ^ n)⁻¹ * (V.weight (closedBall 0 σ)).toReal) -
          ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ, Iann x ∂V.weight =
          ∫ x, Fi x * inner ℝ x (H x) ∂V.weight := by linarith
      rw [hfinal]
      exact hE
  -- (P4) comparison of `τ⁻ⁿ ∫ g(x/τ) dμ` and `∫ g dμ` for the conical test functions.
  have conical_P4 : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H) (hT1 : AEStronglyMeasurable V.tangentProj V.weight) (hT2 : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) (hPx : ∀ x, ‖x - V.tangentProj x x‖ ≤ ‖x‖) (hPi : ∀ x, inner ℝ x (x - V.tangentProj x x) = ‖x - V.tangentProj x x‖ ^ 2) (hB1 : closedBall (0 : Amb n ℓ) 1 ⊆ U) (lam a b τ ρ κ ε : ℝ) (ξ : Amb n ℓ) (hlam : 0 < lam) (hlama : lam ≤ τ * a) (hb1 : b ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ) (hε : 0 < ε) (χ φ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (hφ : ContDiff ℝ 1 φ) (hχb : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (hTV : ∀ α β, α ≤ β → ∫ u in α..β, |deriv χ u| ≤ 2) (hφ' : ∀ t, |deriv φ t| ≤ κ / ρ) (hφ2 : ∀ t, 2 * ρ ≤ t → φ t = 0) (hgcd : ContDiff ℝ 1 (fun y : Amb n ℓ => χ ‖y‖ * φ ‖y - ξ‖)) (hgs : ∀ y : Amb n ℓ, χ ‖y‖ * φ ‖y - ξ‖ ≠ 0 → a < ‖y‖ ∧ ‖y‖ < b),
      |(τ ^ n)⁻¹ * ∫ x, χ ‖τ⁻¹ • x‖ * φ ‖τ⁻¹ • x - ξ‖ ∂V.weight -
              ∫ x, χ ‖x‖ * φ ‖x - ξ‖ ∂V.weight| ≤
            (2 + 2 * κ * ε) * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
                ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight +
            2 * κ / ε * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam, (‖x‖ ^ n)⁻¹ ∂V.weight +
            4 * ρ * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
                (‖x‖ ^ (n - 1))⁻¹ * ‖H x‖ ∂V.weight := by
    as_aux_lemma =>
      intro n ℓ hn U V H hH hT1 hT2 hPx hPi hB1 lam a b τ ρ κ ε ξ hlam hlama hb1 hτ hτ1 hρ hε χ φ hχ hφ hχb hφb hTV hφ' hφ2 hgcd hgs
      have hτ1' : (1 : ℝ) ≤ τ⁻¹ := one_le_inv_iff₀.2 ⟨hτ, hτ1⟩
      have hn0 : n ≠ 0 := by omega
      have ha : 0 < a := by
        have : 0 < τ * a := lt_of_lt_of_le hlam hlama
        exact pos_of_mul_pos_right this hτ.le
      have hlama' : τ⁻¹ * lam ≤ a := by
        rw [inv_mul_le_iff₀ hτ]; exact hlama
      have hκ : 0 ≤ κ := by
        have h2 : 0 ≤ κ / ρ := le_trans (abs_nonneg _) (hφ' 0)
        rcases div_nonneg_iff.1 h2 with h | h
        · exact h.1
        · exact absurd h.2 (not_le.2 hρ)
      obtain ⟨g, hgdef⟩ : ∃ g : Amb n ℓ → ℝ, g = fun y => χ ‖y‖ * φ ‖y - ξ‖ := ⟨_, rfl⟩
      have hgcd' : ContDiff ℝ 1 g := by rw [hgdef]; exact hgcd
      have hgc : Continuous g := hgcd'.continuous
      have hgs' : ∀ y, g y ≠ 0 → a < ‖y‖ ∧ ‖y‖ < b ∧ ‖y - ξ‖ < 2 * ρ := by
        intro y hy
        rw [hgdef] at hy
        refine ⟨(hgs y hy).1, (hgs y hy).2, ?_⟩
        by_contra h
        push Not at h
        exact hy (by simp only; rw [hφ2 _ h, mul_zero])
      have hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1 := by
        intro y
        rw [hgdef]
        exact ⟨mul_nonneg (hχb _).1 (hφb _).1,
          mul_le_one₀ (hχb _).2 (hφb _).1 (hφb _).2⟩
      -- the topological support of `g` lies in the shell `a ≤ ‖y‖ ≤ b`
      have htsupp : tsupport g ⊆ {y : Amb n ℓ | a ≤ ‖y‖ ∧ ‖y‖ ≤ b} := by
        refine closure_minimal (fun y hy => ?_)
          ((isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const))
        have := hgs' y hy
        exact ⟨this.1.le, this.2.1.le⟩
      have htsuppb : tsupport g ⊆ closedBall 0 b := fun y hy => by
        rw [mem_closedBall, dist_zero_right]; exact (htsupp hy).2
      have hballb : closedBall (0 : Amb n ℓ) b ⊆ U :=
        (closedBall_subset_closedBall hb1).trans hB1
      -- Fermat: a nonnegative `C¹` function has vanishing derivative at its zeros
      have hFermat : ∀ f : ℝ → ℝ, (∀ t, 0 ≤ f t) → ∀ t, deriv f t ≠ 0 → f t ≠ 0 := by
        intro f hf t hd hft
        apply hd
        apply IsLocalMin.deriv_eq_zero
        exact Filter.Eventually.of_forall fun u => by rw [hft]; exact hf u
      -- derivative of the norm away from the origin
      have hnormd : ∀ y : Amb n ℓ, y ≠ 0 →
          HasFDerivAt (fun z : Amb n ℓ => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
        intro y hy
        have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
        have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt y
          (hasFDerivAt_id y).norm_sq
        convert h using 1
        · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
        · ext v; simp [Real.sqrt_sq hr.le]; field_simp
      have hχd : Differentiable ℝ χ := hχ.differentiable one_ne_zero
      have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
      have hgderiv : ∀ y : Amb n ℓ, y ≠ 0 → y ≠ ξ → ∀ v, fderiv ℝ g y v =
          deriv χ ‖y‖ * φ ‖y - ξ‖ * (‖y‖⁻¹ * inner ℝ y v) +
            χ ‖y‖ * (deriv φ ‖y - ξ‖ * (‖y - ξ‖⁻¹ * inner ℝ (y - ξ) v)) := by
        intro y hy0 hyξ v
        have h1 : HasFDerivAt (fun z : Amb n ℓ => χ ‖z‖) (deriv χ ‖y‖ • (‖y‖⁻¹ • innerSL ℝ y)) y :=
          (hχd ‖y‖).hasDerivAt.comp_hasFDerivAt y (hnormd y hy0)
        have h2' : HasFDerivAt (fun z : Amb n ℓ => ‖z - ξ‖)
            ((‖y - ξ‖⁻¹ • innerSL ℝ (y - ξ)).comp (ContinuousLinearMap.id ℝ (Amb n ℓ))) y :=
          (hnormd (y - ξ) (sub_ne_zero.2 hyξ)).comp y (hasFDerivAt_sub_const ξ)
        have h2 : HasFDerivAt (fun z : Amb n ℓ => φ ‖z - ξ‖)
            (deriv φ ‖y - ξ‖ • ((‖y - ξ‖⁻¹ • innerSL ℝ (y - ξ)).comp
              (ContinuousLinearMap.id ℝ (Amb n ℓ)))) y :=
          (hφd ‖y - ξ‖).hasDerivAt.comp_hasFDerivAt y h2'
        have h3 : HasFDerivAt g (χ ‖y‖ • (deriv φ ‖y - ξ‖ • ((‖y - ξ‖⁻¹ • innerSL ℝ (y - ξ)).comp
              (ContinuousLinearMap.id ℝ (Amb n ℓ)))) +
            φ ‖y - ξ‖ • (deriv χ ‖y‖ • (‖y‖⁻¹ • innerSL ℝ y))) y := by
          rw [hgdef]; exact h1.mul h2
        rw [h3.fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply]
        ring
      -- the first variation identity
      have hP1 := conical_P1 hn V H hH hT1 hT2 hPx g b τ hgcd' htsuppb hballb hτ hτ1
      -- finiteness and integrability on `B_1`
      have hAm : MeasurableSet (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam) :=
        measurableSet_closedBall.diff measurableSet_closedBall
      have hμ1 : V.weight (closedBall 0 1) < ⊤ := by
        rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
          Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
        exact (V.integrableOn_mult _ (isCompact_closedBall 0 1) hB1).setLIntegral_lt_top
      have hμA : V.weight (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam) < ⊤ :=
        (measure_mono sdiff_subset).trans_lt hμ1
      have hHB1 : IntegrableOn H (closedBall (0 : Amb n ℓ) 1) V.weight :=
        hH.1.integrableOn_compact_subset hB1 (isCompact_closedBall 0 1)
      -- rays meet `B_{2ρ}(ξ)` in a parameter interval of length `4ρ/|x|`
      have hray : ∀ (x : Amb n ℓ), x ≠ 0 → ∀ s : ℝ, ‖s • x - ξ‖ < 2 * ρ →
          s ∈ Ioo (inner ℝ x ξ / ‖x‖ ^ 2 - 2 * ρ / ‖x‖) (inner ℝ x ξ / ‖x‖ ^ 2 + 2 * ρ / ‖x‖) := by
        intro x hx s hs
        have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
        have h1 : |inner ℝ (s • x - ξ) x| ≤ ‖s • x - ξ‖ * ‖x‖ := abs_real_inner_le_norm _ _
        have h2 : inner ℝ (s • x - ξ) x = ‖x‖ ^ 2 * (s - inner ℝ x ξ / ‖x‖ ^ 2) := by
          rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm]
          field_simp
        rw [h2, abs_mul, abs_of_pos (pow_pos hr 2)] at h1
        have h3 : ‖x‖ * (|s - inner ℝ x ξ / ‖x‖ ^ 2| * ‖x‖) < ‖x‖ * (2 * ρ) := by
          calc ‖x‖ * (|s - inner ℝ x ξ / ‖x‖ ^ 2| * ‖x‖) =
                ‖x‖ ^ 2 * |s - inner ℝ x ξ / ‖x‖ ^ 2| := by ring
            _ ≤ ‖s • x - ξ‖ * ‖x‖ := h1
            _ < 2 * ρ * ‖x‖ := mul_lt_mul_of_pos_right hs hr
            _ = ‖x‖ * (2 * ρ) := by ring
        have h4 : |s - inner ℝ x ξ / ‖x‖ ^ 2| < 2 * ρ / ‖x‖ := by
          rw [lt_div_iff₀ hr]
          exact lt_of_mul_lt_mul_left h3 hr.le
        rw [abs_lt] at h4
        constructor <;> linarith [h4.1, h4.2]
      have hind_int : ∀ (c R : ℝ), 0 ≤ R → ∫ s in (1 : ℝ)..τ⁻¹,
          (Ioo (c - R) (c + R)).indicator (fun _ => (1 : ℝ)) s ≤ 2 * R := by
        intro c R hR
        rw [intervalIntegral.integral_of_le hτ1', setIntegral_indicator measurableSet_Ioo,
          setIntegral_const, smul_eq_mul, mul_one]
        calc volume.real (Ioc 1 τ⁻¹ ∩ Ioo (c - R) (c + R)) ≤ volume.real (Ioo (c - R) (c + R)) :=
              measureReal_mono inter_subset_right measure_Ioo_lt_top.ne
          _ = 2 * R := by rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
      have hind_ii : ∀ (c R : ℝ), IntervalIntegrable
          ((Ioo (c - R) (c + R)).indicator (fun _ => (1 : ℝ))) volume 1 τ⁻¹ := by
        intro c R
        rw [intervalIntegrable_iff, uIoc_of_le hτ1']
        exact (integrableOn_const measure_Ioc_lt_top.ne).indicator measurableSet_Ioo
      have hχ'c : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
      have hTVr : ∀ r : ℝ, 0 < r → ∫ s in (1 : ℝ)..τ⁻¹, |deriv χ (r * s)| ≤ 2 / r := by
        intro r hr
        rw [intervalIntegral.integral_comp_mul_left (fun u => |deriv χ u|) hr.ne', smul_eq_mul]
        calc r⁻¹ * ∫ u in r * 1..r * τ⁻¹, |deriv χ u| ≤ r⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left (hTV _ _ (mul_le_mul_of_nonneg_left hτ1' hr.le))
                (by positivity)
          _ = 2 / r := by ring
      have hsle : ∀ s r : ℝ, 0 < r → s * r ≤ 1 → s ≤ r⁻¹ := by
        intro s r hr h
        calc s = s * r / r := by field_simp
          _ ≤ 1 / r := div_le_div_of_nonneg_right h hr.le
          _ = r⁻¹ := one_div r
      -- pointwise bound for the tangential term `J`
      have hJb : ∀ x : Amb n ℓ,
          ‖∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) (x - V.tangentProj x x)‖ ≤
          (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam).indicator (fun x =>
            (2 + 2 * κ * ε) * (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) +
              2 * κ / ε * (‖x‖ ^ n)⁻¹) x := by
        intro x
        by_cases hxA : x ∈ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam
        · rw [indicator_of_mem hxA]
          have hx1 : ‖x‖ ≤ 1 := by
            have := hxA.1; rwa [mem_closedBall, dist_zero_right] at this
          have hxl : lam < ‖x‖ := by
            have := hxA.2; rwa [mem_closedBall, dist_zero_right, not_le] at this
          have hr : 0 < ‖x‖ := lt_trans hlam hxl
          have hx0 : x ≠ 0 := norm_pos_iff.1 hr
          obtain ⟨xp, hxpdef⟩ : ∃ xp : Amb n ℓ, xp = x - V.tangentProj x x := ⟨_, rfl⟩
          rw [← hxpdef]
          have hxpi : inner ℝ x xp = ‖xp‖ ^ 2 := by rw [hxpdef]; exact hPi x
          have hxpn : ‖xp‖ ≤ ‖x‖ := by rw [hxpdef]; exact hPx x
          obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = inner ℝ x ξ / ‖x‖ ^ 2 := ⟨_, rfl⟩
          obtain ⟨ind, hinddef⟩ : ∃ ind : ℝ → ℝ, ind =
              (Ioo (c - 2 * ρ / ‖x‖) (c + 2 * ρ / ‖x‖)).indicator (fun _ => (1 : ℝ)) := ⟨_, rfl⟩
          have hind0 : ∀ s, 0 ≤ ind s := fun s => by
            rw [hinddef]; exact indicator_nonneg (fun _ _ => zero_le_one) _
          have hDg : ∀ s : ℝ, 0 < s → s • x ≠ ξ →
              |fderiv ℝ g (s • x) xp| ≤ |deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) +
                κ / ρ * ‖xp‖ * ind s := by
            intro s hs0 hsξ
            have hnsx : ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hs0.le]
            have e1 : ‖s • x‖⁻¹ * inner ℝ (s • x) xp = ‖xp‖ ^ 2 / ‖x‖ := by
              rw [hnsx, real_inner_smul_left, hxpi]
              field_simp
            have hne : 0 < ‖s • x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hsξ)
            have e2 : |‖s • x - ξ‖⁻¹ * inner ℝ (s • x - ξ) xp| ≤ ‖xp‖ := by
              rw [abs_mul, abs_of_pos (inv_pos.2 hne)]
              calc ‖s • x - ξ‖⁻¹ * |inner ℝ (s • x - ξ) xp| ≤
                    ‖s • x - ξ‖⁻¹ * (‖s • x - ξ‖ * ‖xp‖) :=
                    mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
                _ = ‖xp‖ := by field_simp
            have e3 : |deriv φ ‖s • x - ξ‖| ≤ κ / ρ * ind s := by
              by_cases hd : deriv φ ‖s • x - ξ‖ = 0
              · rw [hd, abs_zero]
                exact mul_nonneg (div_nonneg hκ hρ.le) (hind0 s)
              · have hφne := hFermat φ (fun t => (hφb t).1) _ hd
                have hlt : ‖s • x - ξ‖ < 2 * ρ := by
                  by_contra h
                  push Not at h
                  exact hφne (hφ2 _ h)
                have hmem := hray x hx0 s hlt
                rw [← hcdef] at hmem
                rw [hinddef, indicator_of_mem hmem, mul_one]
                exact hφ' _
            rw [hgderiv (s • x) (smul_ne_zero hs0.ne' hx0) hsξ xp, e1]
            calc |deriv χ ‖s • x‖ * φ ‖s • x - ξ‖ * (‖xp‖ ^ 2 / ‖x‖) +
                  χ ‖s • x‖ * (deriv φ ‖s • x - ξ‖ * (‖s • x - ξ‖⁻¹ * inner ℝ (s • x - ξ) xp))| ≤
                  |deriv χ ‖s • x‖ * φ ‖s • x - ξ‖ * (‖xp‖ ^ 2 / ‖x‖)| +
                  |χ ‖s • x‖ * (deriv φ ‖s • x - ξ‖ * (‖s • x - ξ‖⁻¹ * inner ℝ (s • x - ξ) xp))| :=
                  abs_add_le _ _
              _ ≤ |deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) + κ / ρ * ‖xp‖ * ind s := by
                  apply add_le_add
                  · rw [abs_mul, abs_mul, abs_of_nonneg (hφb _).1,
                      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖xp‖ ^ 2 / ‖x‖), hnsx, mul_comm s]
                    calc |deriv χ (‖x‖ * s)| * φ ‖s • x - ξ‖ * (‖xp‖ ^ 2 / ‖x‖) ≤
                          |deriv χ (‖x‖ * s)| * 1 * (‖xp‖ ^ 2 / ‖x‖) := by
                          gcongr
                          exact (hφb _).2
                      _ = _ := by ring
                  · rw [abs_mul, abs_mul, abs_of_nonneg (hχb _).1]
                    calc χ ‖s • x‖ * (|deriv φ ‖s • x - ξ‖| *
                          |‖s • x - ξ‖⁻¹ * inner ℝ (s • x - ξ) xp|) ≤
                          1 * ((κ / ρ * ind s) * ‖xp‖) :=
                          mul_le_mul (hχb _).2 (mul_le_mul e3 e2 (abs_nonneg _)
                            (mul_nonneg (div_nonneg hκ hρ.le) (hind0 s))) (by positivity) zero_le_one
                      _ = κ / ρ * ‖xp‖ * ind s := by ring
          have hpt : ∀ᵐ s ∂volume, s ∈ Ioc (1 : ℝ) τ⁻¹ → ‖s ^ n * fderiv ℝ g (s • x) xp‖ ≤
              (‖x‖ ^ n)⁻¹ * (|deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) + κ / ρ * ‖xp‖ * ind s) := by
            have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ {s : ℝ | s • x = ξ} := by
              have hsub : {s : ℝ | s • x = ξ}.Subsingleton := by
                intro s1 hs1 s2 hs2
                have h : s1 • x = s2 • x := by rw [mem_setOf_eq] at hs1 hs2; rw [hs1, hs2]
                exact smul_left_injective ℝ hx0 h
              exact measure_eq_zero_iff_ae_notMem.1 (hsub.measure_zero volume)
            filter_upwards [hnull] with s hsξ hs
            have hs0 : 0 < s := by linarith [hs.1]
            have hB0 : 0 ≤ (‖x‖ ^ n)⁻¹ * (|deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) +
                κ / ρ * ‖xp‖ * ind s) := by
              apply mul_nonneg (by positivity)
              exact add_nonneg (by positivity) (mul_nonneg (by positivity) (hind0 s))
            by_cases hsupp : s • x ∈ tsupport g
            · have hnsx : ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hs0.le]
              have hsr : s * ‖x‖ ≤ 1 := by
                have := (htsupp hsupp).2
                rw [hnsx] at this
                linarith
              have hsn : s ^ n ≤ (‖x‖ ^ n)⁻¹ := by
                rw [← inv_pow]
                exact pow_le_pow_left₀ hs0.le (hsle s ‖x‖ hr hsr) n
              rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hs0.le n), Real.norm_eq_abs]
              exact mul_le_mul hsn (hDg s hs0 hsξ) (abs_nonneg _) (by positivity)
            · rw [fderiv_of_notMem_tsupport ℝ hsupp]
              simpa using hB0
          have hbii : IntervalIntegrable (fun s => (‖x‖ ^ n)⁻¹ *
              (|deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) + κ / ρ * ‖xp‖ * ind s)) volume 1 τ⁻¹ := by
            apply IntervalIntegrable.const_mul
            apply IntervalIntegrable.add
            · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
            · rw [hinddef]; exact (hind_ii _ _).const_mul _
          have hJx := intervalIntegral.norm_integral_le_of_norm_le hτ1' hpt hbii
          have hbval : ∫ s in (1 : ℝ)..τ⁻¹, (‖x‖ ^ n)⁻¹ *
              (|deriv χ (‖x‖ * s)| * (‖xp‖ ^ 2 / ‖x‖) + κ / ρ * ‖xp‖ * ind s) ≤
              (‖x‖ ^ n)⁻¹ * (‖xp‖ ^ 2 / ‖x‖ * (2 / ‖x‖) + κ / ρ * ‖xp‖ * (2 * (2 * ρ / ‖x‖))) := by
            rw [intervalIntegral.integral_const_mul]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
              (by rw [hinddef]; exact (hind_ii _ _).const_mul _),
              intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
            apply add_le_add
            · rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (hTVr _ hr) (by positivity)
            · apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [hinddef]
              exact hind_int c _ (by positivity)
          refine hJx.trans (hbval.trans ?_)
          -- `2u² + 4κu ≤ (2 + 2κε)u² + 2κ/ε` with `u = |xp|/|x|`
          obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = ‖xp‖ / ‖x‖ := ⟨_, rfl⟩
          have hu : ‖xp‖ = u * ‖x‖ := by rw [hudef]; field_simp
          rw [hu]
          have hL : (‖x‖ ^ n)⁻¹ * ((u * ‖x‖) ^ 2 / ‖x‖ * (2 / ‖x‖) +
              κ / ρ * (u * ‖x‖) * (2 * (2 * ρ / ‖x‖))) = (‖x‖ ^ n)⁻¹ * (2 * u ^ 2 + 4 * κ * u) := by
            field_simp
            ring
          have hR : (2 + 2 * κ * ε) * ((u * ‖x‖) ^ 2 / ‖x‖ ^ (n + 2)) + 2 * κ / ε * (‖x‖ ^ n)⁻¹ =
              (‖x‖ ^ n)⁻¹ * ((2 + 2 * κ * ε) * u ^ 2 + 2 * κ / ε) := by
            rw [pow_add]
            field_simp
          rw [hL, hR]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsq : (2 + 2 * κ * ε) * u ^ 2 + 2 * κ / ε - (2 * u ^ 2 + 4 * κ * u) =
              2 * κ * (ε * u - 1) ^ 2 / ε := by
            field_simp
            ring
          have : 0 ≤ 2 * κ * (ε * u - 1) ^ 2 / ε := by positivity
          linarith
        · rw [indicator_of_notMem hxA]
          rw [norm_le_zero_iff]
          rw [Set.mem_sdiff, mem_closedBall, dist_zero_right, mem_closedBall, dist_zero_right,
            not_and, not_not] at hxA
          by_cases hx1 : ‖x‖ ≤ 1
          · have hxl := hxA hx1
            rw [intervalIntegral.integral_of_le hτ1', integral_Ioc_eq_integral_Ioo]
            apply setIntegral_eq_zero_of_forall_eq_zero
            intro s hs
            have hs0 : 0 < s := by linarith [hs.1]
            have hnot : s • x ∉ tsupport g := by
              intro h
              have h1 := (htsupp h).1
              rw [norm_smul, Real.norm_of_nonneg hs0.le] at h1
              have h2 : s * ‖x‖ < τ⁻¹ * lam := by
                calc s * ‖x‖ ≤ s * lam := mul_le_mul_of_nonneg_left hxl hs0.le
                  _ < τ⁻¹ * lam := mul_lt_mul_of_pos_right hs.2 hlam
              linarith
            rw [fderiv_of_notMem_tsupport ℝ hnot]
            simp
          · push Not at hx1
            rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
            intro s hs
            rw [uIcc_of_le hτ1'] at hs
            have hs0 : 0 < s := by linarith [hs.1]
            have hnot : s • x ∉ tsupport g := by
              intro h
              have h1 := (htsupp h).2
              rw [norm_smul, Real.norm_of_nonneg hs0.le] at h1
              have h2 : 1 < s * ‖x‖ := by
                calc (1 : ℝ) < ‖x‖ := hx1
                  _ = 1 * ‖x‖ := (one_mul _).symm
                  _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)
              linarith
            simp only
            rw [fderiv_of_notMem_tsupport ℝ hnot]
            simp
      -- pointwise bound for the curvature term
      have hFb : ∀ x : Amb n ℓ,
          ‖(∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)) * inner ℝ x (H x)‖ ≤
          (closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam).indicator
            (fun x => 4 * ρ * ((‖x‖ ^ (n - 1))⁻¹ * ‖H x‖)) x := by
        intro x
        by_cases hxA : x ∈ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam
        · rw [indicator_of_mem hxA, norm_mul]
          have hxl : lam < ‖x‖ := by
            have := hxA.2; rwa [mem_closedBall, dist_zero_right, not_le] at this
          have hr : 0 < ‖x‖ := lt_trans hlam hxl
          have hx0 : x ≠ 0 := norm_pos_iff.1 hr
          obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = inner ℝ x ξ / ‖x‖ ^ 2 := ⟨_, rfl⟩
          have hpt : ∀ᵐ s ∂volume, s ∈ Ioc (1 : ℝ) τ⁻¹ → ‖s ^ (n - 1) * g (s • x)‖ ≤
              (‖x‖ ^ (n - 1))⁻¹ *
                (Ioo (c - 2 * ρ / ‖x‖) (c + 2 * ρ / ‖x‖)).indicator (fun _ => (1 : ℝ)) s := by
            refine Eventually.of_forall fun s hs => ?_
            have hs0 : 0 < s := by linarith [hs.1]
            by_cases hgz : g (s • x) = 0
            · rw [hgz, mul_zero, norm_zero]
              exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
            · have hsupp := hgs' _ hgz
              have hnsx : ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hs0.le]
              have hsr : s * ‖x‖ ≤ 1 := by rw [← hnsx]; linarith [hsupp.2.1]
              have hmem := hray x hx0 s hsupp.2.2
              rw [← hcdef] at hmem
              rw [indicator_of_mem hmem, mul_one, norm_mul, Real.norm_of_nonneg (pow_nonneg hs0.le _),
                Real.norm_of_nonneg (hgb _).1]
              calc s ^ (n - 1) * g (s • x) ≤ (‖x‖ ^ (n - 1))⁻¹ * 1 := by
                    apply mul_le_mul _ (hgb _).2 (hgb _).1 (by positivity)
                    rw [← inv_pow]
                    exact pow_le_pow_left₀ hs0.le (hsle s ‖x‖ hr hsr) _
                _ = _ := mul_one _
          have hFx := intervalIntegral.norm_integral_le_of_norm_le hτ1' hpt
            ((hind_ii _ _).const_mul _)
          rw [intervalIntegral.integral_const_mul] at hFx
          have hFx' : ‖∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)‖ ≤
              (‖x‖ ^ (n - 1))⁻¹ * (2 * (2 * ρ / ‖x‖)) :=
            hFx.trans (mul_le_mul_of_nonneg_left (hind_int c _ (by positivity)) (by positivity))
          calc ‖∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)‖ * ‖inner ℝ x (H x)‖ ≤
                (‖x‖ ^ (n - 1))⁻¹ * (2 * (2 * ρ / ‖x‖)) * (‖x‖ * ‖H x‖) :=
                mul_le_mul hFx' (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
            _ = 4 * ρ * ((‖x‖ ^ (n - 1))⁻¹ * ‖H x‖) := by
                field_simp
                ring
        · rw [indicator_of_notMem hxA]
          rw [Set.mem_sdiff, mem_closedBall, dist_zero_right, mem_closedBall, dist_zero_right,
            not_and, not_not] at hxA
          have hzero : ∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x) = 0 := by
            rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_,
              intervalIntegral.integral_zero]
            intro s hs
            rw [uIcc_of_le hτ1'] at hs
            have hs0 : 0 < s := by linarith [hs.1]
            have hgz : g (s • x) = 0 := by
              by_contra h
              have hsupp := hgs' _ h
              rw [norm_smul, Real.norm_of_nonneg hs0.le] at hsupp
              by_cases hx1 : ‖x‖ ≤ 1
              · have hxl := hxA hx1
                have : s * ‖x‖ ≤ τ⁻¹ * lam := mul_le_mul hs.2 hxl (norm_nonneg _) (by positivity)
                linarith [hsupp.1, hlama']
              · push Not at hx1
                have : 1 < s * ‖x‖ := by
                  calc (1 : ℝ) < ‖x‖ := hx1
                    _ = 1 * ‖x‖ := (one_mul _).symm
                    _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)
                linarith [hsupp.2.1]
            simp only
            rw [hgz, mul_zero]
          rw [hzero, zero_mul, norm_zero]
      -- integrability of the comparison integrands on the annulus
      have happ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × Amb n ℓ => p.1 p.2) :=
        isBoundedBilinearMap_apply.continuous
      have hperp_meas : AEStronglyMeasurable (fun x => x - V.tangentProj x x) V.weight :=
        aestronglyMeasurable_id.sub
          (happ.comp_aestronglyMeasurable (hT1.prodMk aestronglyMeasurable_id))
      have hf1m : AEStronglyMeasurable (fun x => ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2))
          V.weight :=
        ((hperp_meas.aemeasurable.norm.pow_const 2).div
          (measurable_norm.pow_const _).aemeasurable).aestronglyMeasurable
      have hbound_lam : ∀ x ∈ closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
          (‖x‖ ^ n)⁻¹ ≤ (lam ^ n)⁻¹ := by
        intro x hx
        have hxl : lam < ‖x‖ := by
          have := hx.2; rwa [mem_closedBall, dist_zero_right, not_le] at this
        exact inv_anti₀ (pow_pos hlam n) (pow_le_pow_left₀ hlam.le hxl.le n)
      have hf2int : IntegrableOn (fun x : Amb n ℓ => (‖x‖ ^ n)⁻¹)
          (closedBall 0 1 \ closedBall 0 lam) V.weight :=
        Measure.integrableOn_of_bounded (M := (lam ^ n)⁻¹) hμA.ne
          ((measurable_norm.pow_const n).inv.aestronglyMeasurable)
          ((ae_restrict_mem hAm).mono fun x hx => by
            rw [Real.norm_of_nonneg (by positivity)]; exact hbound_lam x hx)
      have hf1int : IntegrableOn (fun x => ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2))
          (closedBall 0 1 \ closedBall 0 lam) V.weight :=
        Measure.integrableOn_of_bounded (M := (lam ^ n)⁻¹) hμA.ne hf1m
          ((ae_restrict_mem hAm).mono fun x hx => by
            have hxl : lam < ‖x‖ := by
              have := hx.2; rwa [mem_closedBall, dist_zero_right, not_le] at this
            have hr : 0 < ‖x‖ := lt_trans hlam hxl
            rw [Real.norm_of_nonneg (by positivity)]
            calc ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ ‖x‖ ^ 2 / ‖x‖ ^ (n + 2) :=
                  div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hPx x) 2)
                    (by positivity)
              _ = (‖x‖ ^ n)⁻¹ := by rw [pow_add]; field_simp
              _ ≤ (lam ^ n)⁻¹ := hbound_lam x hx)
      have hf3int : IntegrableOn (fun x => (‖x‖ ^ (n - 1))⁻¹ * ‖H x‖)
          (closedBall 0 1 \ closedBall 0 lam) V.weight := by
        refine Integrable.mono' ((hHB1.mono_set sdiff_subset).norm.const_mul ((lam ^ (n - 1))⁻¹)) ?_ ?_
        · exact ((measurable_norm.pow_const _).inv.aestronglyMeasurable).mul
            (hHB1.mono_set sdiff_subset).norm.aestronglyMeasurable
        · refine (ae_restrict_mem hAm).mono fun x hx => ?_
          have hxl : lam < ‖x‖ := by
            have := hx.2; rwa [mem_closedBall, dist_zero_right, not_le] at this
          rw [norm_mul, Real.norm_of_nonneg (by positivity), norm_norm]
          exact mul_le_mul_of_nonneg_right
            (inv_anti₀ (pow_pos hlam _) (pow_le_pow_left₀ hlam.le hxl.le _)) (norm_nonneg _)
      -- assembly
      have hgint : Integrable g V.weight := by
        have hsupp : Function.support g ⊆ closedBall 0 1 := fun y hy => by
          have := hgs' y hy
          rw [mem_closedBall, dist_zero_right]
          linarith [this.2.1]
        rw [← integrableOn_iff_integrable_of_support_subset hsupp]
        exact Measure.integrableOn_of_bounded (M := 1) hμ1.ne hgc.aestronglyMeasurable
          (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hgb y).1]; exact (hgb y).2)
      have hgτint : Integrable (fun x => g (τ⁻¹ • x)) V.weight := by
        have hsupp : Function.support (fun x => g (τ⁻¹ • x)) ⊆ closedBall 0 1 := fun y hy => by
          have := hgs' _ hy
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ.le)] at this
          rw [mem_closedBall, dist_zero_right]
          have h1 : τ⁻¹ * ‖y‖ < 1 := lt_of_lt_of_le this.2.1 hb1
          rw [inv_mul_lt_iff₀ hτ, mul_one] at h1
          linarith
        rw [← integrableOn_iff_integrable_of_support_subset hsupp]
        exact Measure.integrableOn_of_bounded (M := 1) hμ1.ne
          (Continuous.aestronglyMeasurable (by fun_prop))
          (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hgb _).1]; exact (hgb _).2)
      have e1 : (fun x : Amb n ℓ => χ ‖τ⁻¹ • x‖ * φ ‖τ⁻¹ • x - ξ‖) = fun x => g (τ⁻¹ • x) := by
        rw [hgdef]
      have e2 : (fun x : Amb n ℓ => χ ‖x‖ * φ ‖x - ξ‖) = g := hgdef.symm
      rw [e1, e2, ← integral_const_mul, ← integral_sub (hgτint.const_mul _) hgint, hP1]
      have hJint : ‖∫ x, (∫ s in (1 : ℝ)..τ⁻¹, s ^ n * fderiv ℝ g (s • x) (x - V.tangentProj x x))
          ∂V.weight‖ ≤
          (2 + 2 * κ * ε) * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
              ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight +
          2 * κ / ε * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam, (‖x‖ ^ n)⁻¹ ∂V.weight := by
        refine (norm_integral_le_of_norm_le ((integrable_indicator_iff hAm).2
          ((hf1int.const_mul _).add (hf2int.const_mul _))) (Eventually.of_forall hJb)).trans
          (le_of_eq ?_)
        rw [integral_indicator hAm]
        simp only [Pi.add_apply]
        rw [integral_add (hf1int.const_mul _) (hf2int.const_mul _),
          integral_const_mul, integral_const_mul]
      have hFint : ‖∫ x, (∫ s in (1 : ℝ)..τ⁻¹, s ^ (n - 1) * g (s • x)) * inner ℝ x (H x)
          ∂V.weight‖ ≤
          4 * ρ * ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
              (‖x‖ ^ (n - 1))⁻¹ * ‖H x‖ ∂V.weight := by
        refine (norm_integral_le_of_norm_le ((integrable_indicator_iff hAm).2
          (hf3int.const_mul _)) (Eventually.of_forall hFb)).trans (le_of_eq ?_)
        rw [integral_indicator hAm, integral_const_mul]
      rw [← Real.norm_eq_abs]
      exact (norm_sub_le _ _).trans (add_le_add hJint hFint)
  -- (F1), (F2): `μ_V`-a.e. tangent planes and measurability of `p_{T_x M}` (Simon Ch. 3, 1.9 with
  -- Remark 1.8(1)); local steps of the accepted candidate for `lgc_tangent_plane_ae`.
  have lemmaT : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight ∧ ∀ᵐ x ∂V.weight, ∃ T : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x T ∧ V.tangentProj x = T.starProjection := by
    as_aux_lemma =>
      intro n ℓ hn U hU V
      have area_measure_eq : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) (hinj : InjOn F A),
          (μHE[n] : Measure (Amb n ℓ)).restrict (F '' A) = ((volume.restrict A).withDensity (fun b => ((Poincare.SimonGMT.Chapter02.areaJacobianAt F b).toNNReal : ℝ≥0∞))).map F := by
        intro F K hF A hA hinj
        ext B hB
        have hFB : MeasurableSet (F ⁻¹' B) := hF.continuous.measurable hB
        rw [Measure.restrict_apply hB, Measure.map_apply hF.continuous.measurable hB,
          withDensity_apply _ hFB]
        have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hA hinj
          (B.indicator 1)
        rw [finrank_euclideanSpace_fin] at h
        rw [lintegral_indicator_one hB, Measure.restrict_apply hB] at h
        rw [h, ← lintegral_indicator hFB]
        refine lintegral_congr fun b => ?_
        by_cases hb : F b ∈ B
        · simp [hb, ENNReal.ofReal]
        · simp [hb]
      have linear_area_measure_eq : ∀ (L : Rn n →L[ℝ] Amb n ℓ),
          (μHE[n] : Measure (Amb n ℓ)).restrict (Set.range L) = (ENNReal.ofReal (L : Rn n →ₗ[ℝ] Amb n ℓ).normDet • (volume : Measure (Rn n))).map L := by
        intro L
        ext B hB
        have hLB : MeasurableSet (L ⁻¹' B) := L.continuous.measurable hB
        rw [Measure.restrict_apply hB, Measure.map_apply L.continuous.measurable hB,
          Measure.smul_apply, smul_eq_mul]
        have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
          (L : Rn n →ₗ[ℝ] Amb n ℓ) (L ⁻¹' B)
        rw [finrank_euclideanSpace_fin] at h
        rw [← h]
        congr 1
        ext y
        simp only [mem_inter_iff, mem_range, mem_image, mem_preimage, ContinuousLinearMap.coe_coe]
        constructor
        · rintro ⟨hy, c, rfl⟩
          exact ⟨c, hy, rfl⟩
        · rintro ⟨c, hc, rfl⟩
          exact ⟨hc, c, rfl⟩
      have blowup_area_tendsto : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) {lam : ℝ} (hlam : 0 < lam) (hbi : ∀ a ∈ A, ∀ b ∈ A, lam * ‖a - b‖ ≤ ‖F a - F b‖) (hgint : ∀ (c : Rn n) (t : ℝ), IntegrableOn (A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F)) (closedBall c t) volume) {a : Rn n} (ha : a ∈ A) (hdiff : DifferentiableAt ℝ F a) (hLinj : Function.Injective (fderiv ℝ F a)) (hleb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in closedBall a (ρ * r), ‖A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F) y - A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F) a‖) (𝓝[>] 0) (𝓝 0)) (f : Amb n ℓ → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f),
          Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ y in Set.range (fderiv ℝ F a), f y ∂(μHE[n] : Measure (Amb n ℓ)))) := by
        intro F K hF A hA lam hlam hbi hgint a ha hdiff hLinj hleb f hfc hfs
        set J := Poincare.SimonGMT.Chapter02.areaJacobianAt F with hJ
        set g : Rn n → ℝ := A.indicator J with hg
        set L := fderiv ℝ F a with hL
        have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
            Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
        have hinj : InjOn F A := fun b hb c hc h => by
          have h1 := hbi b hb c hc
          rw [h, sub_self, norm_zero] at h1
          have h2 : ‖b - c‖ ≤ 0 := by nlinarith [norm_nonneg (b - c)]
          exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
        have hJm : Measurable J := Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
        have hJnn : ∀ b, 0 ≤ J b := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
        set Ja : ℝ := J a with hJa
        have hJa_nn : 0 ≤ Ja := hJnn a
        have hga : g a = Ja := by rw [hg, Set.indicator_of_mem ha]
        -- Step 1: the blown-up area integral as an integral over the parameter space
        have hLHS : ∀ r : ℝ, ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)
            ∂(μHE[n] : Measure (Amb n ℓ)) = ∫ b, g b * f (r⁻¹ • (F b - F a)) := by
          intro r
          rw [area_measure_eq F hF A hA hinj, integral_map hF.continuous.aemeasurable
            (by simp only [hη]; fun_prop : Continuous fun z =>
              f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)).aestronglyMeasurable,
            integral_withDensity_eq_integral_smul hJm.real_toNNReal, ← integral_indicator hA]
          congr 1
          ext b
          by_cases hb : b ∈ A
          · simp only [Set.indicator_of_mem hb, hg, hη, NNReal.smul_def, smul_eq_mul,
              Real.coe_toNNReal _ (hJnn b)]
          · simp [Set.indicator_of_notMem hb, hg]
        -- Step 2: the plane integral
        have hJL : (L : Rn n →ₗ[ℝ] Amb n ℓ).normDet = Ja := rfl
        have hRHS : ∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)) = Ja * ∫ c, f (L c) := by
          rw [linear_area_measure_eq L, integral_map L.continuous.aemeasurable
            hfc.aestronglyMeasurable, integral_smul_measure, hJL, ENNReal.toReal_ofReal hJa_nn,
            smul_eq_mul]
        have hscale : ∀ r : ℝ, 0 < r →
            ∫ c, f (L c) = (r ^ n)⁻¹ * ∫ b, f (r⁻¹ • L (b - a)) := by
          intro r hr
          have h1 : ∫ b, f (r⁻¹ • L (b - a)) = ∫ c, f (L (r⁻¹ • c)) := by
            have := integral_sub_right_eq_self (μ := (volume : Measure (Rn n)))
              (fun c => f (L (r⁻¹ • c))) a
            simpa only [map_smul] using this
          rw [h1, Measure.integral_comp_smul (volume : Measure (Rn n)) (fun c => f (L c)) r⁻¹,
            finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr n), smul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ (pow_pos hr n).ne', one_mul]
        -- bounds for `f`
        obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hfs
        have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
        obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
          obtain ⟨R₀, hR₀⟩ := hfs.isCompact.isBounded.subset_closedBall 0
          refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
          apply image_eq_zero_of_notMem_tsupport
          intro hyt
          have h1 := hR₀ hyt
          rw [mem_closedBall, dist_zero_right] at h1
          linarith [le_max_left R₀ 1]
        -- a lower bound for the injective derivative
        obtain ⟨KL, hKLpos, hKL⟩ :=
          (LinearMap.injective_iff_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ)).1 hLinj
        set lamL : ℝ := ((KL : ℝ))⁻¹ with hlamL_def
        have hKL0 : (0 : ℝ) < KL := by exact_mod_cast hKLpos
        have hlamL : 0 < lamL := inv_pos.2 hKL0
        have hLlow : ∀ v, lamL * ‖v‖ ≤ ‖L v‖ := by
          intro v
          have h1 := hKL.le_mul_dist v 0
          simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
          rw [hlamL_def, inv_mul_le_iff₀ hKL0]
          exact h1
        set ρ : ℝ := (R + 1) / lam + (R + 1) / lamL with hρ_def
        have hρ : 0 < ρ := by positivity
        -- outside `B_{ρ r}(a)` both integrands vanish
        have hsupp1 : ∀ r : ℝ, 0 < r → ∀ b, b ∉ closedBall a (ρ * r) →
            g b * f (r⁻¹ • (F b - F a)) = 0 := by
          intro r hr b hb
          by_cases hbA : b ∈ A
          · rw [hR _ ?_, mul_zero]
            rw [mem_closedBall, dist_eq_norm, not_le] at hb
            have h1 := hbi b hbA a ha
            rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
            have h2 : (R + 1) / lam * r ≤ ρ * r :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hr.le
            have h3 : lam * ((R + 1) / lam * r) = (R + 1) * r := by field_simp
            nlinarith
          · rw [hg, Set.indicator_of_notMem hbA, zero_mul]
        have hsupp2 : ∀ r : ℝ, 0 < r → ∀ b, b ∉ closedBall a (ρ * r) →
            f (r⁻¹ • L (b - a)) = 0 := by
          intro r hr b hb
          apply hR
          rw [mem_closedBall, dist_eq_norm, not_le] at hb
          have h1 := hLlow (b - a)
          rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
          have h2 : (R + 1) / lamL * r ≤ ρ * r :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hr.le
          have h3 : lamL * ((R + 1) / lamL * r) = (R + 1) * r := by field_simp
          nlinarith
        -- integrability of both integrands
        have hint1 : ∀ r : ℝ, 0 < r → Integrable (fun b => g b * f (r⁻¹ • (F b - F a))) := by
          intro r hr
          refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ (hsupp1 r hr)
          refine (hgint a (ρ * r)).mul_bdd (c := Cf) ?_ (Eventually.of_forall fun b => hCf _)
          exact (hfc.comp ((hF.continuous.sub continuous_const).const_smul r⁻¹)).aestronglyMeasurable
        have hint2 : ∀ r : ℝ, 0 < r → Integrable (fun b => Ja * f (r⁻¹ • L (b - a))) := by
          intro r hr
          refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
          exact HasCompactSupport.intro (isCompact_closedBall a (ρ * r))
            fun b hb => by rw [hsupp2 r hr b hb, mul_zero]
        -- the difference as one integral
        have hdiffint : ∀ r : ℝ, 0 < r →
            (r ^ n)⁻¹ * ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)
              ∂(μHE[n] : Measure (Amb n ℓ)) - ∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)) =
            (r ^ n)⁻¹ * ∫ b, (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))) := by
          intro r hr
          rw [hLHS, hRHS, hscale r hr, integral_sub (hint1 r hr) (hint2 r hr), integral_const_mul]
          ring
        -- volume of the balls
        set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
        have hvol : ∀ t : ℝ, 0 ≤ t → (volume (closedBall a t)).toReal = t ^ n * c₁ := by
          intro t ht
          rw [Measure.addHaar_closedBall' volume a ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal
            (pow_nonneg ht _), finrank_euclideanSpace_fin]
        have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
        -- the estimate
        have hmain : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ b,
            (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a)))) (𝓝[>] 0) (𝓝 0) := by
          rw [Metric.tendsto_nhds]
          intro ε hε
          set ε₁ : ℝ := ε / (2 * (Ja * ρ ^ n * c₁ + 1)) with hε₁
          have hε₁0 : 0 < ε₁ := by positivity
          obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
            (hfs.uniformContinuous_of_continuous hfc) ε₁ hε₁0
          have hlo := (hdiff.hasFDerivAt.isLittleO).def (show (0 : ℝ) < δ / (2 * ρ) by positivity)
          obtain ⟨η, hη0, hηb⟩ := Metric.eventually_nhds_iff.1 hlo
          have hleb' := (Metric.tendsto_nhds.1 (hleb ρ hρ)) (ε / (2 * (Cf + 1))) (by positivity)
          filter_upwards [hleb', Ioo_mem_nhdsGT (show (0 : ℝ) < η / ρ by positivity)] with r hr1 hr2
          have hr : 0 < r := hr2.1
          have hρr : ρ * r < η := by
            have := hr2.2
            rw [lt_div_iff₀ hρ] at this
            linarith
          rw [Real.dist_eq, sub_zero] at hr1 ⊢
          -- pointwise bound
          have hpt : ∀ b, ‖g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))‖ ≤
              (closedBall a (ρ * r)).indicator (fun b => Cf * ‖g b - g a‖ + Ja * ε₁) b := by
            intro b
            by_cases hb : b ∈ closedBall a (ρ * r)
            · rw [Set.indicator_of_mem hb]
              have hba : ‖b - a‖ ≤ ρ * r := by rwa [mem_closedBall, dist_eq_norm] at hb
              have hdist : dist (r⁻¹ • (F b - F a)) (r⁻¹ • L (b - a)) < δ := by
                rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le]
                have h1 : ‖F b - F a - L (b - a)‖ ≤ δ / (2 * ρ) * ‖b - a‖ :=
                  hηb (by rw [dist_eq_norm]; linarith)
                have h2 : δ / (2 * ρ) * ‖b - a‖ ≤ δ / (2 * ρ) * (ρ * r) :=
                  mul_le_mul_of_nonneg_left hba (by positivity)
                have h3 : δ / (2 * ρ) * (ρ * r) = δ / 2 * r := by field_simp
                rw [← div_eq_inv_mul, div_lt_iff₀ hr]
                nlinarith
              have hfd := hδ hdist
              rw [Real.dist_eq] at hfd
              calc ‖g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))‖
                  = ‖(g b - g a) * f (r⁻¹ • (F b - F a)) +
                      Ja * (f (r⁻¹ • (F b - F a)) - f (r⁻¹ • L (b - a)))‖ := by
                    rw [hga]; ring_nf
                _ ≤ ‖g b - g a‖ * Cf + Ja * ε₁ := by
                    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
                    · rw [norm_mul]
                      exact mul_le_mul_of_nonneg_left (hCf _) (norm_nonneg _)
                    · rw [norm_mul, Real.norm_of_nonneg hJa_nn, Real.norm_eq_abs]
                      exact mul_le_mul_of_nonneg_left hfd.le hJa_nn
                _ = Cf * ‖g b - g a‖ + Ja * ε₁ := by ring
            · rw [Set.indicator_of_notMem hb, hsupp1 r hr b hb, hsupp2 r hr b hb, mul_zero,
                sub_zero, norm_zero]
          have hb1 : IntegrableOn (fun b => Cf * ‖g b - g a‖) (closedBall a (ρ * r)) :=
            ((hgint a (ρ * r)).sub (integrableOn_const (measure_closedBall_lt_top).ne)).norm.const_mul Cf
          have hb2 : IntegrableOn (fun _ : Rn n => Ja * ε₁) (closedBall a (ρ * r)) :=
            integrableOn_const (measure_closedBall_lt_top).ne
          have hb3 : IntegrableOn (fun b => Cf * ‖g b - g a‖ + Ja * ε₁) (closedBall a (ρ * r)) :=
            hb1.add hb2
          have hI := norm_integral_le_of_norm_le
            ((integrable_indicator_iff measurableSet_closedBall).2 hb3)
            (Eventually.of_forall hpt)
          have hsplit : ∫ b in closedBall a (ρ * r), (Cf * ‖g b - g a‖ + Ja * ε₁) =
              Cf * (∫ b in closedBall a (ρ * r), ‖g b - g a‖) + (ρ * r) ^ n * c₁ * (Ja * ε₁) := by
            rw [integral_add hb1 hb2, integral_const_mul, setIntegral_const, smul_eq_mul,
              measureReal_def, hvol (ρ * r) (by positivity)]
          rw [integral_indicator measurableSet_closedBall] at hI
          beta_reduce at hI
          rw [hsplit] at hI
          have hrn : 0 < r ^ n := pow_pos hr n
          rw [abs_mul, abs_of_pos (inv_pos.2 hrn)]
          calc (r ^ n)⁻¹ * |∫ b, (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a)))|
              ≤ (r ^ n)⁻¹ * (Cf * (∫ b in closedBall a (ρ * r), ‖g b - g a‖) +
                  (ρ * r) ^ n * c₁ * (Ja * ε₁)) :=
                mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hI) (inv_pos.2 hrn).le
            _ = Cf * ((r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖) +
                  Ja * ρ ^ n * c₁ * ε₁ := by
                rw [mul_pow]; field_simp
            _ < ε / 2 + ε / 2 := by
                refine add_lt_add_of_le_of_lt ?_ ?_
                · have hX : (r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖ ≤
                      ε / (2 * (Cf + 1)) := (le_abs_self _).trans hr1.le
                  calc Cf * ((r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖)
                      ≤ Cf * (ε / (2 * (Cf + 1))) := mul_le_mul_of_nonneg_left hX hCf0
                    _ ≤ ε / 2 := by
                      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
                      nlinarith
                · rw [hε₁, mul_div_assoc']
                  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
                  nlinarith [mul_nonneg (mul_nonneg hJa_nn (pow_nonneg hρ.le n)) hc₁0]
            _ = ε := add_halves ε
        have hfin := hmain.congr' (by
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact (hdiffint r hr).symm)
        simpa using hfin.add_const (∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)))
      have jac_integrableOn : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) (hinj : InjOn F A) (c : Rn n) (t : ℝ),
          IntegrableOn (A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F)) (closedBall c t) volume := by
        intro F K hF A hA hinj c t
        have hJm := Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
        have hJnn := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
        rw [IntegrableOn, integrable_indicator_iff hA, IntegrableOn,
          Measure.restrict_restrict hA]
        refine ⟨hJm.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hJnn)]
        have h := Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitz hF
          (hA.inter (measurableSet_closedBall (x := c) (ε := t))) (hinj.mono inter_subset_left)
        rw [finrank_euclideanSpace_fin] at h
        rw [← h]
        calc (μHE[n] : Measure (Amb n ℓ)) (F '' (A ∩ closedBall c t))
            ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A ∩ closedBall c t) :=
              Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
                hF.lipschitzOnWith
          _ < ⊤ := by
              have hH : (μHE[n] : Measure (Rn n)) = volume := by
                have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
                rwa [finrank_euclideanSpace_fin] at this
              rw [hH]
              exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
                ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top)
      have leb_points : ∀ (g : Rn n → ℝ) (hg : ∀ (c : Rn n) (t : ℝ), IntegrableOn g (closedBall c t) volume),
          ∀ᵐ a ∂(volume : Measure (Rn n)), ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in closedBall a (ρ * r), ‖g y - g a‖) (𝓝[>] 0) (𝓝 0) := by
        intro g hg
        have hloc : LocallyIntegrable g volume := fun x =>
          ⟨closedBall x 1, closedBall_mem_nhds x one_pos, hg x 1⟩
        filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1] with a ha ρ hρ
        have hρt : Tendsto (fun r : ℝ => ρ * r) (𝓝[>] 0) (𝓝[>] 0) := by
          apply tendsto_nhdsWithin_iff.mpr
          constructor
          · simpa only [mul_zero, id_eq] using
              ((tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul ρ)
          · filter_upwards [self_mem_nhdsWithin] with r hr
            exact mul_pos hρ hr
        have h1 := ha (fun _ => a) (fun r => ρ * r) hρt (by
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact mem_closedBall_self (by rw [one_mul]; exact (mul_pos hρ hr).le))
        set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
        have hvol : ∀ t : ℝ, 0 ≤ t → (volume (closedBall a t)).toReal = t ^ n * c₁ := by
          intro t ht
          rw [Measure.addHaar_closedBall' volume a ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal
            (pow_nonneg ht _), finrank_euclideanSpace_fin]
        have hc₁0 : 0 < c₁ := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
          measure_closedBall_lt_top.ne
        have h2 := h1.const_mul (ρ ^ n * c₁)
        rw [mul_zero] at h2
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [setAverage_eq, measureReal_def, hvol _ (mul_pos hρ hr).le, smul_eq_mul, mul_pow]
        field_simp
      set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
      have hHRn : (μHE[n] : Measure (Rn n)) = volume := by
        have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
        rwa [finrank_euclideanSpace_fin] at this
      -- (UD) the upper density theorem (Simon Ch. 1, 3.6): accepted `aetp_upper_density_zero_ae`
      have ud_tendsto : ∀ (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), MeasurableSet A →
          ν A < ⊤ → ∀ᵐ x ∂H, x ∉ A →
            Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) :=
        fun ν A hA hfin => aetp_upper_density_zero_ae n ℓ ν A hA hfin
      -- `r⁻ⁿ μ_V((M \ K) ∩ B_{Rr}(x)) → 0` for `Hⁿ`-a.e. `x` in a compact `K ⊆ U`
      have wdoc : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → ∀ᵐ x ∂H, x ∈ K → ∀ R : ℝ, 0 < R →
          Tendsto (fun r : ℝ => V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) /
            ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
        intro K hK hKU
        obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
        set A : Set (Amb n ℓ) := thickening δ K \ K with hAdef
        have hAm : MeasurableSet A := isOpen_thickening.measurableSet.diff hK.measurableSet
        have hc : IsCompact (cthickening δ K) := hK.cthickening
        have hfin : V.weight A < ⊤ := by
          have h1 : V.weight A ≤ V.weight (cthickening δ K) :=
            measure_mono (sdiff_subset.trans (thickening_subset_cthickening δ K))
          refine h1.trans_lt ?_
          calc V.weight (cthickening δ K)
              = ∫⁻ x in cthickening δ K, ENNReal.ofReal (V.mult x) ∂(H.restrict V.carrier) := by
                rw [RectifiableVarifold.weight, withDensity_apply _ hc.measurableSet]
            _ = ∫⁻ x in V.carrier ∩ cthickening δ K, ENNReal.ofReal (V.mult x) ∂H := by
                rw [Measure.restrict_restrict hc.measurableSet, inter_comm]
            _ < ⊤ := (V.integrableOn_mult _ hc hδU).lintegral_lt_top
        filter_upwards [ud_tendsto V.weight A hAm hfin] with x hx hxK R hR
        have hxA : x ∉ A := fun h => h.2 hxK
        have h0 := hx hxA
        -- rescale `s = R r`
        have hscale : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · simpa using (continuous_const_mul R).tendsto' 0 0 (by simp) |>.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hR hr
        have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal (R ^ n) *
            (V.weight (A ∩ closedBall x (R * r)) / ENNReal.ofReal ((R * r) ^ n))) (𝓝[>] 0) (𝓝 0) := by
          have := (h0.comp hscale)
          simpa using ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofReal_ne_top)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
          (Eventually.of_forall fun _ => bot_le) ?_
        have hδR : (0 : ℝ) < δ / R := div_pos hδ hR
        filter_upwards [Ioo_mem_nhdsGT hδR] with r hr
        have hsub : (V.carrier \ K) ∩ closedBall x (R * r) ⊆ A ∩ closedBall x (R * r) := by
          rintro y ⟨⟨_, hyK⟩, hy⟩
          refine ⟨⟨?_, hyK⟩, hy⟩
          rw [mem_closedBall] at hy
          have : R * r < δ := by
            have h2 := (lt_div_iff₀ hR).1 hr.2
            linarith
          exact mem_thickening_iff.2 ⟨x, hxK, lt_of_le_of_lt hy this⟩
        have hpow : ENNReal.ofReal ((R * r) ^ n) = ENNReal.ofReal (R ^ n) * ENNReal.ofReal (r ^ n) := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hR.le n)]
        have hRn : ENNReal.ofReal (R ^ n) ≠ 0 := by
          rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hR n
        calc V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) / ENNReal.ofReal (r ^ n)
            ≤ V.weight (A ∩ closedBall x (R * r)) / ENNReal.ofReal (r ^ n) := by
              gcongr
          _ = ENNReal.ofReal (R ^ n) *
                (V.weight (A ∩ closedBall x (R * r)) / ENNReal.ofReal ((R * r) ^ n)) := by
              rw [hpow, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hRn ENNReal.ofReal_ne_top]
      -- tangent locality (proof of Simon 1.6): blow-ups of `A` and `N` have the same limits where
      -- `A \ N` and `N \ A` have `Hⁿ`-density zero
      have tangent_locality : ∀ (A N : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)),
          MeasurableSet A → MeasurableSet N → H A < ⊤ → H N < ⊤ →
          Tendsto (fun r : ℝ => H ((A \ N) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) →
          Tendsto (fun r : ℝ => H ((N \ A) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) →
          Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x P →
          Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x P := by
        intro A N x P hA hN hAfin hNfin q1 q2 hT
        obtain ⟨hdim, hlim⟩ := hT
        refine ⟨hdim, fun f => ?_⟩
        -- a bound for `f` and a radius containing its support
        obtain ⟨C₀, hC₀⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
        set C : ℝ := max C₀ 0 with hCdef
        have hC : ∀ y, ‖f y‖ ≤ C := fun y => (hC₀ y).trans (le_max_left _ _)
        obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
        set R : ℝ := max R₀ 1 with hRdef
        have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
        have hfz : ∀ y, R < ‖y‖ → f y = 0 := by
          intro y hy
          apply image_eq_zero_of_notMem_tsupport
          intro hyt
          have := hR₀ hyt
          rw [mem_closedBall, dist_zero_right] at this
          linarith [le_max_left R₀ 1]
        -- rescaled density quotients tend to zero
        have hscale : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) :=
              (continuous_id.mul continuous_const).tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hr hR
        have hdens : ∀ S : Set (Amb n ℓ), H S < ⊤ →
            Tendsto (fun s : ℝ => H (S ∩ closedBall x s) / ENNReal.ofReal (s ^ n)) (𝓝[>] 0) (𝓝 0) →
            Tendsto (fun r : ℝ => (r ^ n)⁻¹ * H.real (S ∩ closedBall x (r * R))) (𝓝[>] 0) (𝓝 0) := by
          intro S hSfin hq
          have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hq.comp hscale)
          have h4 := h3.const_mul (R ^ n)
          rw [ENNReal.toReal_zero, mul_zero] at h4
          refine h4.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          have hr' : (0 : ℝ) < r := hr
          simp only [Function.comp_apply, ENNReal.toReal_div]
          rw [ENNReal.toReal_ofReal (pow_nonneg (mul_pos hr' hR).le n), Measure.real, mul_pow]
          have hRn : (0 : ℝ) < R ^ n := pow_pos hR n
          have hrn : (0 : ℝ) < r ^ n := pow_pos hr' n
          field_simp
        have hd1 := hdens (A \ N) ((measure_mono sdiff_subset).trans_lt hAfin) q1
        have hd2 := hdens (N \ A) ((measure_mono sdiff_subset).trans_lt hNfin) q2
        -- the blown-up integrals over `A` and `N` differ by terms controlled by the two quotients
        have hdiff : ∀ r : ℝ, 0 < r →
            ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂H) -
                ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' N, f y ∂H‖ ≤
              C * ((r ^ n)⁻¹ * H.real ((A \ N) ∩ closedBall x (r * R)) +
                (r ^ n)⁻¹ * H.real ((N \ A) ∩ closedBall x (r * R))) := by
          intro r hr
          set g : Amb n ℓ → ℝ := fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) with hgdef
          have hcv : ∀ S : Set (Amb n ℓ),
              (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂H) =
                (r ^ n)⁻¹ * ∫ z in S, g z ∂H := by
            intro S
            have := rsod_blowUp_setIntegral_eq n ℓ S f (fun _ => 1) x r hr
            simpa only [mul_one] using this
          have hgc : Continuous g := by
            simp only [hgdef, Poincare.SimonGMT.Chapter03.blowUpMap]
            exact f.continuous.comp (by fun_prop)
          have hgb : ∀ z, ‖g z‖ ≤ C := fun z => hC _
          have hgz : ∀ z, z ∉ closedBall x (r * R) → g z = 0 := by
            intro z hz
            apply hfz
            rw [mem_closedBall, not_le, dist_eq_norm] at hz
            simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs,
              abs_of_pos hr]
            rw [lt_inv_mul_iff₀ hr]
            linarith
          have hint : ∀ S : Set (Amb n ℓ), H S < ⊤ → IntegrableOn g S H := fun S hS =>
            Measure.integrableOn_of_bounded hS.ne hgc.aestronglyMeasurable
              (Eventually.of_forall hgb)
          have hbound : ∀ S : Set (Amb n ℓ), MeasurableSet S → H S < ⊤ →
              ‖∫ z in S, g z ∂H‖ ≤ C * H.real (S ∩ closedBall x (r * R)) := by
            intro S hS hSfin
            rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_left
              (fun z hz => hgz z (fun h => hz.2 ⟨hz.1, h⟩))]
            exact norm_setIntegral_le_of_norm_le_const
              ((measure_mono inter_subset_left).trans_lt hSfin) (fun z _ => hgb z)
          have hsplitA := integral_inter_add_sdiff hN (hint A hAfin)
          have hsplitN := integral_inter_add_sdiff hA (hint N hNfin)
          rw [inter_comm N A] at hsplitN
          rw [hcv A, hcv N, ← mul_sub, ← hsplitA, ← hsplitN, add_sub_add_left_eq_sub, norm_mul,
            norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hr]
          have hb1 := hbound (A \ N) (hA.diff hN) ((measure_mono sdiff_subset).trans_lt hAfin)
          have hb2 := hbound (N \ A) (hN.diff hA) ((measure_mono sdiff_subset).trans_lt hNfin)
          have hrn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
          calc (r ^ n)⁻¹ * ‖(∫ z in A \ N, g z ∂H) - ∫ z in N \ A, g z ∂H‖
              ≤ (r ^ n)⁻¹ * (‖∫ z in A \ N, g z ∂H‖ + ‖∫ z in N \ A, g z ∂H‖) :=
                mul_le_mul_of_nonneg_left (norm_sub_le _ _) hrn
            _ ≤ (r ^ n)⁻¹ * (C * H.real ((A \ N) ∩ closedBall x (r * R)) +
                  C * H.real ((N \ A) ∩ closedBall x (r * R))) :=
                mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hrn
            _ = C * ((r ^ n)⁻¹ * H.real ((A \ N) ∩ closedBall x (r * R)) +
                  (r ^ n)⁻¹ * H.real ((N \ A) ∩ closedBall x (r * R))) := by ring
        have hzero : Tendsto (fun r : ℝ =>
            (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂H) -
              ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' N, f y ∂H) (𝓝[>] 0) (𝓝 0) := by
          have hsum := (hd1.add hd2).const_mul C
          rw [add_zero, mul_zero] at hsum
          refine squeeze_zero_norm' ?_ hsum
          filter_upwards [self_mem_nhdsWithin] with r hr using hdiff r hr
        have := (hlim f).add hzero
        rw [add_zero] at this
        refine this.congr' (Eventually.of_forall fun r => ?_)
        show (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' N, f y ∂H) +
            ((∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂H) -
              ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' N, f y ∂H) =
            ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂H
        ring
      -- a Borel extension of `L ↦ p_{L(ℝⁿ)}`, continuous on injective `L`
      -- (accepted `aetp_starProjection_range_continuousOn`)
      obtain ⟨Ψ, hΨm, hΨeq⟩ : ∃ Ψ : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ), Measurable Ψ ∧
          ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L →
            Ψ L = (LinearMap.range L.toLinearMap).starProjection := by
        classical
        exact ⟨_, ContinuousOn.measurable_piecewise (aetp_starProjection_range_continuousOn n ℓ)
          (continuousOn_const (c := (0 : Amb n ℓ →L[ℝ] Amb n ℓ)))
          ContinuousLinearMap.isOpen_injective.measurableSet,
          fun L hL => Set.piecewise_eq_of_mem _ _ _ hL⟩
      -- Lusin pieces
      obtain ⟨Kp, hKc, hKM, hKcont, hKfin, hKnull⟩ := Submission.aetp_lusin_compact_exhaustion n ℓ U hU V
      -- the rectifiable cover
      obtain ⟨M₀, hM₀, F, hFlip, hcover⟩ := V.countablyRectifiable
      choose KF hKF using hFlip
      -- lower bounds for injective linear maps
      have hcLex : ∀ L : Rn n →L[ℝ] Amb n ℓ, ∃ c : ℝ≥0, 0 < c ∧
          (Function.Injective L → ∀ v, (c : ℝ) * ‖v‖ ≤ ‖L v‖) := by
        intro L
        by_cases hL : Function.Injective L
        · obtain ⟨K, hKpos, hK⟩ :=
            (LinearMap.injective_iff_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ)).1 hL
          refine ⟨K⁻¹, inv_pos.2 hKpos, fun _ v => ?_⟩
          have h1 := hK.le_mul_dist v 0
          simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
          rw [NNReal.coe_inv, inv_mul_le_iff₀ (by exact_mod_cast hKpos)]
          exact h1
        · exact ⟨1, one_pos, fun h => absurd h hL⟩
      choose cL hcLpos hcL using hcLex
      -- the pieces of the parameter domains
      set s : ℕ → ℕ → Set (Rn n) := fun j k =>
        Poincare.SimonGMT.Chapter02.areaRegularSet (F j) ∩ ball 0 k with hsdef
      have hpart : ∀ j k, ∃ (t : ℕ → Set (Rn n)) (Lp : ℕ → Rn n →L[ℝ] Amb n ℓ),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ i, MeasurableSet (t i)) ∧ (s j k ⊆ ⋃ i, t i) ∧
          (∀ i, ApproximatesLinearOn (F j) (Lp i) (s j k ∩ t i) (cL (Lp i) / 2)) ∧
          ((s j k).Nonempty → ∀ i, ∃ y ∈ s j k, Lp i = fderiv ℝ (F j) y) := fun j k =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) (s j k) (fderiv ℝ (F j))
          (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun L => cL L / 2)
          (fun L => (div_pos (hcLpos L) two_pos).ne')
      choose t Lp _hdisj htm hcovt happ hact using hpart
      set A : ℕ → ℕ → ℕ → Set (Rn n) := fun j k i => s j k ∩ t j k i with hAdef
      have hAm : ∀ j k i, MeasurableSet (A j k i) := fun j k i =>
        ((Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet (F j)).inter measurableSet_ball).inter
          (htm j k i)
      have hAreg : ∀ j k i, ∀ a ∈ A j k i, DifferentiableAt ℝ (F j) a ∧
          Function.Injective (fderiv ℝ (F j) a) := fun j k i a ha => ha.1.1
      have hAbi : ∀ j k i, ∃ lam : ℝ, 0 < lam ∧ ∀ a ∈ A j k i, ∀ b ∈ A j k i,
          lam * ‖a - b‖ ≤ ‖F j a - F j b‖ := by
        intro j k i
        by_cases hne : (s j k).Nonempty
        · obtain ⟨y, hy, hLy⟩ := hact j k hne i
          have hinjL : Function.Injective (Lp j k i) := hLy ▸ hy.1.2
          refine ⟨(cL (Lp j k i) : ℝ) / 2, by have := hcLpos (Lp j k i); positivity,
            fun a ha b hb => ?_⟩
          have h1 := happ j k i a ha b hb
          have h2 := hcL (Lp j k i) hinjL (a - b)
          have h3 : ‖(Lp j k i) (a - b)‖ ≤ ‖F j a - F j b‖ +
              ‖F j a - F j b - (Lp j k i) (a - b)‖ := by
            have := norm_sub_le (F j a - F j b) (F j a - F j b - (Lp j k i) (a - b))
            rwa [sub_sub_cancel] at this
          push_cast at h1
          linarith
        · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha.1⟩ hne⟩
      choose lam hlam hbi using hAbi
      have hinj : ∀ j k i, InjOn (F j) (A j k i) := fun j k i b hb c hc h => by
        have h1 := hbi j k i b hb c hc
        rw [h, sub_self, norm_zero] at h1
        have h2 : ‖b - c‖ ≤ 0 := by nlinarith [norm_nonneg (b - c), hlam j k i]
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
      -- measurable inverses on the pieces
      have hGex : ∀ j k i, ∃ G : Amb n ℓ → Rn n, Measurable G ∧ ∀ a ∈ A j k i, G (F j a) = a := by
        intro j k i
        have hemb := ContinuousOn.measurableEmbedding (hAm j k i) (hKF j).continuous.continuousOn
          (hinj j k i)
        obtain ⟨G, hGm, hGeq⟩ := hemb.exists_measurable_extend (g := (Subtype.val : A j k i → Rn n))
          measurable_subtype_coe (fun _ => ⟨0⟩)
        exact ⟨G, hGm, fun a ha => congrFun hGeq ⟨a, ha⟩⟩
      choose G hGm hGa using hGex
      set T : ℕ → ℕ → ℕ → Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun j k i x =>
        Ψ (fderiv ℝ (F j) (G j k i x)) with hTdef
      have hTm : ∀ j k i, Measurable (T j k i) := fun j k i =>
        hΨm.comp ((measurable_fderiv ℝ (F j)).comp (hGm j k i))
      -- good points of each piece
      have hgood : ∀ m j k i, ∀ᵐ x ∂H, x ∈ Kp m ∩ F j '' A j k i →
          (∃ P : Submodule ℝ (Amb n ℓ),
            Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
          V.tangentProj x = T j k i x := by
        intro m j k i
        set S := F j '' A j k i with hSdef
        have hSm : MeasurableSet S :=
          (hAm j k i).image_of_continuousOn_injOn (hKF j).continuous.continuousOn (hinj j k i)
        have hSfin : H S < ⊤ := by
          calc H S ≤ (KF j : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A j k i) :=
                Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
                  (hKF j).lipschitzOnWith
            _ < ⊤ := by
                rw [hHRn]
                exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
                  ((measure_mono (inter_subset_left.trans inter_subset_right)).trans_lt
                    measure_ball_lt_top)
        set J := Poincare.SimonGMT.Chapter02.areaJacobianAt (F j) with hJ
        have hgint := jac_integrableOn (F j) (hKF j) (A j k i) (hAm j k i) (hinj j k i)
        have hleb := leb_points ((A j k i).indicator J) hgint
        set N : Set (Rn n) := {a | ¬ ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
          ∫ y in closedBall a (ρ * r), ‖(A j k i).indicator J y - (A j k i).indicator J a‖)
            (𝓝[>] 0) (𝓝 0)} with hN
        have hN0 : volume N = 0 := ae_iff.1 hleb
        have hFN : H (F j '' N) = 0 := by
          have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
            (A := N) n (hKF j).lipschitzOnWith
          rw [hHRn, hN0, mul_zero] at this
          exact le_antisymm this bot_le
        have hKS : H (Kp m \ S) < ⊤ := (measure_mono sdiff_subset).trans_lt (hKfin m)
        have hSK : H (S \ Kp m) < ⊤ := (measure_mono sdiff_subset).trans_lt hSfin
        filter_upwards [wdoc (Kp m) (hKc m) ((hKM m).trans V.carrier_subset),
          ud_tendsto H (Kp m \ S) ((hKc m).measurableSet.diff hSm) hKS,
          ud_tendsto H (S \ Kp m) (hSm.diff (hKc m).measurableSet) hSK,
          measure_eq_zero_iff_ae_notMem.1 hFN] with x hx3 hx4 hx5 hxN hxmem
        obtain ⟨hxK, a, ha, rfl⟩ := hxmem
        have hLeb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
            ∫ y in closedBall a (ρ * r), ‖(A j k i).indicator J y - (A j k i).indicator J a‖)
              (𝓝[>] 0) (𝓝 0) := by
          by_contra h
          exact hxN ⟨a, h, rfl⟩
        set L := fderiv ℝ (F j) a with hL
        have hLinj : Function.Injective L := (hAreg j k i a ha).2
        set P : Submodule ℝ (Amb n ℓ) := LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) with hPdef
        have hPset : (P : Set (Amb n ℓ)) = Set.range L := by
          rw [hPdef, LinearMap.coe_range, ContinuousLinearMap.coe_coe]
        have hPn : Module.finrank ℝ P = n :=
          (LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj).trans
            finrank_euclideanSpace_fin
        -- `P = DF(a)(ℝⁿ)` is the approximate tangent space of `S = F(A)` at `F(a)`
        have hStan : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S (F j a) P := by
          refine ⟨hPn, fun f => ?_⟩
          rw [hPset]
          refine (blowup_area_tendsto (F j) (hKF j) (A j k i) (hAm j k i) (hlam j k i) (hbi j k i)
            hgint ha (hAreg j k i a ha).1 hLinj hLeb f f.continuous f.hasCompactSupport).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          have h1 := rsod_blowUp_setIntegral_eq n ℓ S f (fun _ => 1) (F j a) r hr
          simp only [mul_one] at h1
          exact h1.symm
        -- hence of the Lusin piece `K`
        have hKtan : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (Kp m) (F j a) P :=
          tangent_locality (Kp m) S (F j a) P (hKc m).measurableSet hSm (hKfin m) hSfin
            (hx4 fun h => h.2 ⟨a, ha, rfl⟩) (hx5 fun h => h.2 hxK) hStan
        -- the weighted tangent plane (accepted `aetp_weightedTangent_of_lusin_compact`)
        have hW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
            (F j a) P :=
          aetp_weightedTangent_of_lusin_compact n ℓ U hU V (Kp m) (F j a) P (hKc m) (hKM m) hxK
            (hKcont m) (hx3 hxK) hKtan
        refine ⟨⟨P, hW⟩, ?_⟩
        have hex : ∃ P : Submodule ℝ (Amb n ℓ),
            Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
              (F j a) P := ⟨P, hW⟩
        have huniq : Classical.choose hex = P :=
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
            (V.mult_pos _ (hKM m hxK)).ne' (Classical.choose_spec hex) hW
        have hkey : ∀ Q : Submodule ℝ (Amb n ℓ), Q = P → Q.starProjection = P.starProjection := by
          rintro Q rfl; rfl
        rw [RectifiableVarifold.tangentProj, dite_eq_left hex, hkey _ huniq]
        refine (hΨeq L hLinj).symm.trans ?_
        simp only [hTdef, hGa j k i a ha, hL]
      -- almost every point of the carrier lies in some piece
      have hcovae : ∀ᵐ x ∂(H.restrict V.carrier), ∃ m j k i, x ∈ Kp m ∩ F j '' A j k i := by
        have hN3 : ∀ j, H (F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j))) = 0 := by
          intro j
          have := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero (hKF j) univ
          rwa [finrank_euclideanSpace_fin] at this
        have hnull : H ((V.carrier \ ⋃ m, Kp m) ∪ M₀ ∪
            ⋃ j, F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j))) = 0 :=
          measure_union_null (measure_union_null hKnull hM₀) (measure_iUnion_null hN3)
        rw [ae_restrict_iff'₀ V.nullMeasurableSet_carrier]
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
        have hxK : ∃ m, x ∈ Kp m := by
          by_contra h
          exact hx (Or.inl (Or.inl ⟨hxM, fun hmem => h (mem_iUnion.1 hmem)⟩))
        obtain ⟨m, hm⟩ := hxK
        rcases hcover hxM with hx0 | hxr
        · exact absurd (Or.inl (Or.inr hx0)) hx
        obtain ⟨j, b, rfl⟩ := mem_iUnion.1 hxr
        have hb : b ∈ Poincare.SimonGMT.Chapter02.areaRegularSet (F j) := by
          by_contra h
          exact hx (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, h⟩, rfl⟩))
        obtain ⟨k, hk⟩ := exists_nat_gt ‖b‖
        have hbs : b ∈ s j k := ⟨hb, by rwa [mem_ball, dist_zero_right]⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hcovt j k hbs)
        exact ⟨m, j, k, i, hm, b, ⟨hbs, hi⟩, rfl⟩
      have hall : ∀ᵐ x ∂(H.restrict V.carrier), ∃ m j k i, x ∈ Kp m ∩ F j '' A j k i ∧
          (∃ P : Submodule ℝ (Amb n ℓ),
            Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
          V.tangentProj x = T j k i x := by
        have h1 : ∀ᵐ x ∂(H.restrict V.carrier), ∀ m j k i, x ∈ Kp m ∩ F j '' A j k i →
            (∃ P : Submodule ℝ (Amb n ℓ),
              Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
            V.tangentProj x = T j k i x := by
          rw [ae_all_iff]; intro m
          rw [ae_all_iff]; intro j
          rw [ae_all_iff]; intro k
          rw [ae_all_iff]; intro i
          exact ae_restrict_of_ae (hgood m j k i)
        filter_upwards [h1, hcovae] with x hx1 hx2
        obtain ⟨m, j, k, i, hmem⟩ := hx2
        exact ⟨m, j, k, i, hmem, hx1 m j k i hmem⟩
      have hac : V.weight ≪ H.restrict V.carrier := withDensity_absolutelyContinuous _ _
      have hallμ := hac.ae_le hall
      refine ⟨?_, ?_⟩
      · -- (a) measurability
        set Pc : ℕ × ℕ × ℕ × ℕ → Set (Amb n ℓ) := fun ι =>
          Kp ι.1 ∩ F ι.2.1 '' A ι.2.1 ι.2.2.1 ι.2.2.2 with hPc
        have hPcm : ∀ ι, MeasurableSet (Pc ι) := fun ι =>
          (hKc ι.1).measurableSet.inter ((hAm _ _ _).image_of_continuousOn_injOn
            (hKF _).continuous.continuousOn (hinj _ _ _))
        have hcovμ : ∀ᵐ x ∂V.weight, x ∈ ⋃ ι, Pc ι := by
          filter_upwards [hallμ] with x hx
          obtain ⟨m, j, k, i, hxm, -⟩ := hx
          exact mem_iUnion.2 ⟨(m, j, k, i), hxm⟩
        rw [← Measure.restrict_eq_self_of_ae_mem hcovμ, aestronglyMeasurable_iUnion_iff]
        rintro ⟨m, j, k, i⟩
        refine (hTm j k i).aestronglyMeasurable.congr ?_
        have hac' : V.weight.restrict (Pc (m, j, k, i)) ≪ H :=
          ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac).trans
            (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
        filter_upwards [hac'.ae_le (hgood m j k i), ae_restrict_mem (hPcm (m, j, k, i))] with x hx hxP
        exact (hx hxP).2.symm
      · -- (b) weighted tangent planes
        filter_upwards [hallμ] with x hx
        obtain ⟨m, j, k, i, -, hex, -⟩ := hx
        refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
        rw [RectifiableVarifold.tangentProj, dite_eq_left hex]
  -- the assembly (Simon 6.1, steps 0-7)
  as_aux_lemma =>
    intro n ℓ hn Λ hΛ
    -- a bound for the derivative of the smooth step
    obtain ⟨KS, hKS0, hKS⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv Real.smoothTransition t| ≤ K := by
      have hc : Continuous (deriv Real.smoothTransition) :=
        (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
      obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        hc.continuousOn
      refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · exact (Real.norm_eq_abs _ ▸ hK t ht).trans (le_max_left _ _)
      · have hd : deriv Real.smoothTransition t = 0 := by
          rw [mem_Icc, not_and_or] at ht
          rcases ht with h | h
          · push Not at h
            have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
              filter_upwards [Iio_mem_nhds h] with u hu
              exact Real.smoothTransition.zero_of_nonpos hu.le
            rw [hev.deriv_eq]
            simp
          · push Not at h
            have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
              filter_upwards [Ioi_mem_nhds h] with u hu
              exact Real.smoothTransition.one_of_one_le hu.le
            rw [hev.deriv_eq]
            simp
        rw [hd, abs_zero]
        exact le_max_right _ _
    have hω : 0 < unitBallVolume n := by
      unfold unitBallVolume
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = unitBallVolume n := ⟨_, rfl⟩
    rw [← hωdef] at hω
    refine ⟨Λ + 3 + (2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n), ?_⟩
    intro lam θ δ hlam hlam4 hθ hθ4 hδ hδ4 ξ hξ U hU hB1 V H hH hhyp hΛV ρ hρ τ hτ
    rw [← hωdef] at hhyp
    obtain ⟨hρ0, hρθ⟩ := hρ
    obtain ⟨hτlam, hτ1⟩ := hτ
    have hlam1 : lam < 1 := by linarith
    have hτ0 : 0 < τ := by linarith
    have hlamτ : lam ≤ τ := by linarith
    -- tangent planes (facts (F1), (F2))
    obtain ⟨hT1, hT2w⟩ := lemmaT n ℓ hn U hU V
    have hT2 : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧
        V.tangentProj x = P.starProjection :=
      hT2w.mono fun x ⟨T, hT, hTx⟩ => ⟨T, hT.1, hTx⟩
    have hPcases : ∀ x, V.tangentProj x = 0 ∨
        ∃ Q : Submodule ℝ (Amb n ℓ), V.tangentProj x = Q.starProjection := by
      intro x
      unfold RectifiableVarifold.tangentProj
      split_ifs with h
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    have hPx : ∀ x, ‖x - V.tangentProj x x‖ ≤ ‖x‖ := by
      intro x
      rcases hPcases x with h | ⟨Q, h⟩
      · rw [h]; simp
      · rw [h]
        have h0 : inner ℝ (x - Q.starProjection x) (Q.starProjection x) = 0 :=
          Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
        have h2 : ‖x‖ ^ 2 = ‖x - Q.starProjection x‖ ^ 2 + ‖Q.starProjection x‖ ^ 2 := by
          have := norm_add_sq_real (x - Q.starProjection x) (Q.starProjection x)
          rw [sub_add_cancel, h0] at this
          linarith
        have h3 : ‖x - Q.starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
          rw [h2]; exact le_add_of_nonneg_right (sq_nonneg _)
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
    have hPi : ∀ x, inner ℝ x (x - V.tangentProj x x) = ‖x - V.tangentProj x x‖ ^ 2 := by
      intro x
      rcases hPcases x with h | ⟨Q, h⟩
      · rw [h]; simp
      · rw [h]
        have h0 : inner ℝ (x - Q.starProjection x) (Q.starProjection x) = 0 :=
          Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
        calc inner ℝ x (x - Q.starProjection x) =
              inner ℝ ((x - Q.starProjection x) + Q.starProjection x) (x - Q.starProjection x) := by
              rw [sub_add_cancel]
          _ = ‖x - Q.starProjection x‖ ^ 2 := by
              rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_comm, h0, add_zero]
    -- `d = δ^{1/4}` and `L = |log λ|`
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = δ ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
    rw [← hddef]
    have hd0 : 0 < d := by rw [hddef]; exact Real.rpow_pos_of_pos hδ _
    have hd4 : d ^ 4 = δ := by
      rw [hddef, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num
    have hd1 : d < 1 := by
      rw [hddef]; exact Real.rpow_lt_one hδ.le (by linarith) (by norm_num)
    have hδd : δ ≤ d := by
      rw [← hd4]
      calc d ^ 4 ≤ d ^ 1 := pow_le_pow_of_le_one hd0.le hd1.le (by norm_num)
        _ = d := pow_one d
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = |Real.log lam| := ⟨_, rfl⟩
    rw [← hLdef]
    have hLeq : L = Real.log lam⁻¹ := by
      rw [hLdef, Real.log_inv, abs_of_neg (Real.log_neg hlam hlam1)]
    have hL1 : 1 < L := by
      rw [hLeq]
      have h4 : (4 : ℝ) < lam⁻¹ := by
        rw [lt_inv_comm₀ (by norm_num) hlam]; linarith
      have h5 : Real.log 4 < Real.log lam⁻¹ := Real.log_lt_log (by norm_num) h4
      have hlog4 : 1 < Real.log 4 := by
        have h1 : (1 / 2 : ℝ) < Real.exp (-1 / 2) := by
          have := Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)
          linarith
        have h2 : Real.exp (1 / 2) < 2 := by
          have he : Real.exp (1 / 2) = (Real.exp (-1 / 2))⁻¹ := by
            rw [← Real.exp_neg]; norm_num
          rw [he, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
          linarith
        have h3 : Real.exp 1 < 4 := by
          have he : Real.exp 1 = Real.exp (1 / 2) ^ 2 := by
            rw [← Real.exp_nat_mul]; norm_num
          rw [he]
          have h0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
          calc Real.exp (1 / 2) ^ 2 = Real.exp (1 / 2) * Real.exp (1 / 2) := sq _
            _ < 2 * 2 := mul_lt_mul'' h2 h2 h0.le h0.le
            _ = 4 := by norm_num
        have := Real.log_lt_log (Real.exp_pos 1) h3
        rwa [Real.log_exp] at this
      linarith
    -- masses
    have hμB : ∀ r, r ≤ 1 → V.weight (closedBall 0 r) < ⊤ := by
      intro r hr
      have hBr : closedBall (0 : Amb n ℓ) r ⊆ U := (closedBall_subset_closedBall hr).trans hB1
      rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
      exact (V.integrableOn_mult _ (isCompact_closedBall 0 r) hBr).setLIntegral_lt_top
    have hμ1 : V.weight (closedBall 0 1) < ⊤ := hμB 1 le_rfl
    have hμsub : ∀ S, S ⊆ closedBall (0 : Amb n ℓ) 1 → V.weight S < ⊤ := fun S hS =>
      (measure_mono hS).trans_lt hμ1
    have hΛ1 : (V.weight (closedBall 0 1)).toReal ≤ Λ := ENNReal.toReal_le_of_le_ofReal hΛ.le hΛV
    -- the hypotheses, unpacked
    have hrpow : ∀ t : ℝ, 0 < t → t ^ (1 - (n : ℝ)) = (t ^ (n - 1))⁻¹ := by
      intro t ht
      rw [show (1 - (n : ℝ)) = -((n - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hn]; push_cast; ring,
        Real.rpow_neg ht.le, Real.rpow_natCast]
    have hHr : ∀ t ∈ Icc lam 1,
        ∫ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ ∂V.weight ≤ δ * t ^ (n - 1) := by
      intro t ht
      have h := hhyp t ht
      have ht0 : 0 < t := lt_of_lt_of_le hlam ht.1
      have habs := abs_nonneg ((V.weight (closedBall 0 1)).toReal / ω -
        (V.weight (closedBall 0 lam)).toReal / (ω * lam ^ n))
      rw [hrpow t ht0] at h
      have h2 : (t ^ (n - 1))⁻¹ * ∫ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ ∂V.weight ≤ δ := by
        linarith
      rw [inv_mul_le_iff₀ (pow_pos ht0 _)] at h2
      calc _ ≤ t ^ (n - 1) * δ := h2
        _ = δ * t ^ (n - 1) := mul_comm _ _
    have hpinch : |(V.weight (closedBall 0 1)).toReal -
        (V.weight (closedBall 0 lam)).toReal / lam ^ n| ≤ ω * δ := by
      have h := hhyp 1 ⟨hlam1.le, le_rfl⟩
      have hnn : 0 ≤ (1 : ℝ) ^ (1 - (n : ℝ)) *
          ∫ x in closedBall (0 : Amb n ℓ) 1, ‖H x‖ ∂V.weight := by
        rw [Real.one_rpow, one_mul]
        exact setIntegral_nonneg measurableSet_closedBall fun x _ => norm_nonneg _
      have h1 : |(V.weight (closedBall 0 1)).toReal / ω -
          (V.weight (closedBall 0 lam)).toReal / (ω * lam ^ n)| ≤ δ := by linarith
      have heq : (V.weight (closedBall 0 1)).toReal / ω -
          (V.weight (closedBall 0 lam)).toReal / (ω * lam ^ n) =
          ((V.weight (closedBall 0 1)).toReal - (V.weight (closedBall 0 lam)).toReal / lam ^ n) /
            ω := by
        field_simp
      rw [heq, abs_div, abs_of_pos hω, div_le_iff₀ hω] at h1
      linarith
    -- monotonicity identity (3.18) at `(σ, 1)`
    have hP2 : ∀ σ, lam ≤ σ → σ ≤ 1 →
        |((V.weight (closedBall 0 1)).toReal - (V.weight (closedBall 0 σ)).toReal / σ ^ n) -
          ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
            ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight| ≤ δ * (2 + Real.log σ⁻¹) :=
      fun σ hσ hσ1 => conical_P2 hn hU V H hH hT1 hT2 hPx hPi hB1 σ δ (lt_of_lt_of_le hlam hσ)
        hσ1 (fun t ht => hHr t ⟨le_trans hσ ht.1, ht.2⟩)
    have hI_nonneg : ∀ σ, 0 ≤ ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 σ,
        ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight :=
      fun σ => setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
        fun x _ => by positivity
    have hlogσ : ∀ σ, lam ≤ σ → Real.log σ⁻¹ ≤ L := by
      intro σ hσ
      rw [hLeq]
      exact Real.log_le_log (inv_pos.2 (lt_of_lt_of_le hlam hσ)) (inv_anti₀ hlam hσ)
    have hdens : ∀ σ, lam ≤ σ → σ ≤ 1 →
        (V.weight (closedBall 0 σ)).toReal / σ ^ n ≤ Λ + 3 * δ * L := by
      intro σ hσ hσ1
      have h := hP2 σ hσ hσ1
      rw [abs_le] at h
      have h0 := hI_nonneg σ
      have h1 : δ * Real.log σ⁻¹ ≤ δ * L := mul_le_mul_of_nonneg_left (hlogσ σ hσ) hδ.le
      have h2 : 2 * δ ≤ 2 * δ * L := le_mul_of_one_le_right (by positivity) hL1.le
      have e : δ * (2 + Real.log σ⁻¹) = 2 * δ + δ * Real.log σ⁻¹ := by ring
      have e2 : 3 * δ * L = 2 * δ * L + δ * L := by ring
      linarith [h.1]
    have hA1 : ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
        ‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2) ∂V.weight ≤ (ω + 3) * δ * L := by
      have h := hP2 lam le_rfl hlam1.le
      rw [abs_le] at h
      have h1 : δ * Real.log lam⁻¹ = δ * L := by rw [hLeq]
      have h2 : ω * δ ≤ ω * δ * L := le_mul_of_one_le_right (by positivity) hL1.le
      have h3 : 2 * δ ≤ 2 * δ * L := le_mul_of_one_le_right (by positivity) hL1.le
      have e : δ * (2 + Real.log lam⁻¹) = 2 * δ + δ * Real.log lam⁻¹ := by ring
      have e2 : (ω + 3) * δ * L = ω * δ * L + 2 * δ * L + δ * L := by ring
      rw [abs_le] at hpinch
      linarith [hpinch.1, hpinch.2, h.1, h.2]
    -- geometry
    have hξ0 : 0 < ‖ξ‖ := by rw [hξ]; linarith
    have hball1 : ∀ r, r ≤ ρ → closedBall ξ r ⊆ closedBall (0 : Amb n ℓ) 1 := by
      intro r hr y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right]
      calc ‖y‖ = ‖ξ + (y - ξ)‖ := by rw [add_sub_cancel]
        _ ≤ ‖ξ‖ + ‖y - ξ‖ := norm_add_le _ _
        _ ≤ 1 := by rw [hξ]; linarith
    have hballτ : closedBall (τ • ξ) (τ * ρ) ⊆ closedBall (0 : Amb n ℓ) τ := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right]
      calc ‖y‖ = ‖τ • ξ + (y - τ • ξ)‖ := by rw [add_sub_cancel]
        _ ≤ ‖τ • ξ‖ + ‖y - τ • ξ‖ := norm_add_le _ _
        _ ≤ τ * (1 - θ) + τ * ρ := by
            rw [norm_smul, Real.norm_of_nonneg hτ0.le, hξ]
            linarith
        _ ≤ τ := by
            have he : τ * (1 - θ) + τ * ρ = τ * (1 - θ + ρ) := by ring
            rw [he]
            exact mul_le_of_le_one_right hτ0.le (by linarith)
    have hτB1 : closedBall (τ • ξ) (τ * ρ) ⊆ closedBall (0 : Amb n ℓ) 1 :=
      hballτ.trans (closedBall_subset_closedBall hτ1)
    -- conversion to `[0, ∞]`
    have hconv : ∀ (S1 S2 : Set (Amb n ℓ)) (c e : ℝ), V.weight S1 < ⊤ → V.weight S2 < ⊤ →
        0 ≤ c → 0 ≤ e → (V.weight S1).toReal ≤ c * (V.weight S2).toReal + e →
        V.weight S1 ≤ ENNReal.ofReal c * V.weight S2 + ENNReal.ofReal e := by
      intro S1 S2 c e h1 h2 hc he h
      rw [← ENNReal.ofReal_toReal h1.ne, ← ENNReal.ofReal_toReal h2.ne, ← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_add (mul_nonneg hc ENNReal.toReal_nonneg) he]
      exact ENNReal.ofReal_le_ofReal h
    have hconv2 : ∀ (S2 S3 : Set (Amb n ℓ)) (c e : ℝ), V.weight S2 < ⊤ →
        V.weight (S3 ∩ closedBall 0 1) < ⊤ → 0 ≤ c → 0 ≤ e →
        c * (V.weight S2).toReal ≤ (V.weight (S3 ∩ closedBall 0 1)).toReal + e →
        ENNReal.ofReal c * V.weight S2 ≤ V.weight S3 + ENNReal.ofReal e := by
      intro S2 S3 c e h2 h3 hc he h
      calc ENNReal.ofReal c * V.weight S2 = ENNReal.ofReal (c * (V.weight S2).toReal) := by
            rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal h2.ne]
        _ ≤ ENNReal.ofReal ((V.weight (S3 ∩ closedBall 0 1)).toReal + e) :=
            ENNReal.ofReal_le_ofReal h
        _ = V.weight (S3 ∩ closedBall 0 1) + ENNReal.ofReal e := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg he, ENNReal.ofReal_toReal h3.ne]
        _ ≤ V.weight S3 + ENNReal.ofReal e := add_le_add (measure_mono inter_subset_left) le_rfl
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Λ + 3 + (2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n) :=
      ⟨_, rfl⟩
    rw [← hCdef]
    have hC : Λ + 3 ≤ C := by
      rw [hCdef]
      have : 0 ≤ 2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n := by positivity
      linarith
    have hCdL0 : 0 ≤ C * d * L := by
      have : 0 ≤ C := by linarith
      positivity
    have hdensτ := hdens τ hlamτ hτ1
    have h1dρ : (1 - d) * ρ ≤ ρ := by
      have := mul_le_mul_of_nonneg_right (show 1 - d ≤ 1 by linarith) hρ0.le
      linarith
    by_cases htriv : 1 < d * L
    · -- the trivial case `δ^{1/4} |log λ| > 1`
      have hCdL : Λ + 3 ≤ C * d * L := by
        calc Λ + 3 ≤ C := hC
          _ = C * 1 := (mul_one C).symm
          _ ≤ C * (d * L) := mul_le_mul_of_nonneg_left htriv.le (by linarith)
          _ = C * d * L := by ring
      constructor
      · apply hconv _ _ _ _ (hμsub _ (hball1 _ h1dρ)) (hμsub _ hτB1)
          (inv_nonneg.2 (pow_nonneg hτ0.le n)) hCdL0
        have h1 : (V.weight (closedBall ξ ((1 - d) * ρ))).toReal ≤
            (V.weight (closedBall 0 1)).toReal :=
          ENNReal.toReal_mono hμ1.ne (measure_mono (hball1 _ h1dρ))
        have h2 : 0 ≤ (τ ^ n)⁻¹ * (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal := by positivity
        linarith
      · apply hconv2 _ _ _ _ (hμsub _ hτB1) (hμsub _ inter_subset_right)
          (inv_nonneg.2 (pow_nonneg hτ0.le n)) hCdL0
        have h1 : (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal ≤
            (V.weight (closedBall 0 τ)).toReal :=
          ENNReal.toReal_mono (hμB τ hτ1).ne (measure_mono hballτ)
        have h2 : (τ ^ n)⁻¹ * (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal ≤
            (V.weight (closedBall 0 τ)).toReal / τ ^ n := by
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : 3 * δ * L ≤ 3 * d * L := by
          have := mul_le_mul_of_nonneg_right hδd (by linarith : (0 : ℝ) ≤ L)
          linarith
        have h4 : Λ + 3 * d * L ≤ (Λ + 3) * (d * L) := by
          have e : (Λ + 3) * (d * L) - (Λ + 3 * d * L) = Λ * (d * L - 1) := by ring
          have : 0 ≤ Λ * (d * L - 1) := mul_nonneg hΛ.le (by linarith)
          linarith
        have h5 : 0 ≤ (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal :=
          ENNReal.toReal_nonneg
        have h6 : (Λ + 3) * (d * L) ≤ C * d * L := by
          have := mul_le_mul_of_nonneg_right hC (mul_nonneg hd0.le (by linarith : (0 : ℝ) ≤ L))
          have e : C * d * L = C * (d * L) := by ring
          linarith
        linarith
    · push Not at htriv
      have hL0 : 0 ≤ L := by linarith
      have hδL : δ * L ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hδd hL0) htriv
      have hmass : ∀ t ∈ Icc lam 1, (V.weight (closedBall 0 t)).toReal ≤ (Λ + 3) * t ^ n := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hlam ht.1
        have h := hdens t ht.1 ht.2
        rw [div_le_iff₀ (pow_pos ht0 n)] at h
        have h' : Λ + 3 * δ * L ≤ Λ + 3 := by
          have : 3 * δ * L = 3 * (δ * L) := by ring
          linarith
        calc _ ≤ (Λ + 3 * δ * L) * t ^ n := h
          _ ≤ (Λ + 3) * t ^ n := mul_le_mul_of_nonneg_right h' (pow_nonneg ht0.le n)
      -- the layer-cake bounds (4.11)
      have hI2 : ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam, (‖x‖ ^ n)⁻¹ ∂V.weight ≤
          (Λ + 3) * (1 + n * L) := by
        have h := conical_P3 V.weight (fun _ => (1 : ℝ)) n lam 1 (Λ + 3) hlam hlam1.le hμ1
          (fun _ => zero_le_one) (integrableOn_const hμ1.ne) (fun t ht => by
            rw [setIntegral_const, smul_eq_mul, mul_one]
            exact hmass t ht)
        simp only [mul_one, one_div] at h
        rwa [← hLeq] at h
      have hHB1 : IntegrableOn (fun x => ‖H x‖) (closedBall (0 : Amb n ℓ) 1) V.weight :=
        (hH.1.integrableOn_compact_subset hB1 (isCompact_closedBall 0 1)).norm
      have hI3 : ∫ x in closedBall (0 : Amb n ℓ) 1 \ closedBall 0 lam,
          (‖x‖ ^ (n - 1))⁻¹ * ‖H x‖ ∂V.weight ≤ δ * (1 + ((n - 1 : ℕ) : ℝ) * L) := by
        have h := conical_P3 V.weight (fun x => ‖H x‖) (n - 1) lam 1 δ hlam hlam1.le hμ1
          (fun x => norm_nonneg _) hHB1 hHr
        simp only [one_div] at h
        rwa [← hLeq] at h
      -- the constants `κ = K_S / d`, `ε = d⁻²` and the error bound `E ≤ C' d L`
      obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = KS / d := ⟨_, rfl⟩
      obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (d ^ 2)⁻¹ := ⟨_, rfl⟩
      have hκ0 : 0 ≤ κ := by rw [hκdef]; exact div_nonneg hKS0 hd0.le
      have hε0 : 0 < ε := by rw [hεdef]; positivity
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
      have hρ1 : ρ ≤ 1 := by linarith
      have hE : ∀ (I1 I2 I3 : ℝ), I1 ≤ (ω + 3) * δ * L → I2 ≤ (Λ + 3) * (1 + n * L) →
          I3 ≤ δ * (1 + ((n - 1 : ℕ) : ℝ) * L) →
          (2 + 2 * κ * ε) * I1 + 2 * κ / ε * I2 + 4 * ρ * I3 ≤
            (2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n) * d * L := by
        intro I1 I2 I3 h1 h2 h3
        have e1 : κ * ε * δ = KS * d := by
          rw [hκdef, hεdef, ← hd4]; field_simp
        have e2 : 2 * κ / ε = 2 * KS * d := by
          rw [hκdef, hεdef]; field_simp
        have hc1 : 0 ≤ 2 + 2 * κ * ε := by positivity
        have hc2 : 0 ≤ 2 * κ / ε := by positivity
        have hc3 : 0 ≤ 4 * ρ := by positivity
        have t1 : (2 + 2 * κ * ε) * ((ω + 3) * δ * L) ≤ 2 * (ω + 3) * (1 + KS) * d * L := by
          calc (2 + 2 * κ * ε) * ((ω + 3) * δ * L) =
                2 * (ω + 3) * δ * L + 2 * (ω + 3) * L * (κ * ε * δ) := by ring
            _ = 2 * (ω + 3) * δ * L + 2 * (ω + 3) * L * (KS * d) := by rw [e1]
            _ ≤ 2 * (ω + 3) * d * L + 2 * (ω + 3) * L * (KS * d) := by
                have := mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hδd (by positivity : (0 : ℝ) ≤ 2 * (ω + 3))) hL0
                linarith
            _ = 2 * (ω + 3) * (1 + KS) * d * L := by ring
        have t2 : 2 * κ / ε * ((Λ + 3) * (1 + n * L)) ≤ 2 * KS * (Λ + 3) * (n + 1) * d * L := by
          have hnL : 1 + n * L ≤ (n + 1) * L := by
            have : (n + 1) * L - (1 + n * L) = L - 1 := by ring
            linarith
          calc 2 * κ / ε * ((Λ + 3) * (1 + n * L)) = 2 * KS * d * (Λ + 3) * (1 + n * L) := by
                rw [e2]; ring
            _ ≤ 2 * KS * d * (Λ + 3) * ((n + 1) * L) :=
                mul_le_mul_of_nonneg_left hnL (by positivity)
            _ = 2 * KS * (Λ + 3) * (n + 1) * d * L := by ring
        have t3 : 4 * ρ * (δ * (1 + ((n - 1 : ℕ) : ℝ) * L)) ≤ 4 * n * d * L := by
          have hnL : 1 + ((n - 1 : ℕ) : ℝ) * L ≤ n * L := by
            rw [Nat.cast_sub hn, Nat.cast_one]
            have : n * L - (1 + (n - 1) * L) = L - 1 := by ring
            linarith
          have hnn : 0 ≤ 1 + ((n - 1 : ℕ) : ℝ) * L :=
            add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hL0)
          calc 4 * ρ * (δ * (1 + ((n - 1 : ℕ) : ℝ) * L)) ≤ (4 * 1) * (d * (n * L)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hρ1 (by norm_num))
                  (mul_le_mul hδd hnL hnn hd0.le) (mul_nonneg hδ.le hnn) (by norm_num)
            _ = 4 * n * d * L := by ring
        have u1 := mul_le_mul_of_nonneg_left h1 hc1
        have u2 := mul_le_mul_of_nonneg_left h2 hc2
        have u3 := mul_le_mul_of_nonneg_left h3 hc3
        have e3 : (2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n) * d * L =
            2 * (ω + 3) * (1 + KS) * d * L + 2 * KS * (Λ + 3) * (n + 1) * d * L + 4 * n * d * L := by
          ring
        linarith
      have hEC : (2 * (ω + 3) * (1 + KS) + 2 * KS * (Λ + 3) * (n + 1) + 4 * n) * d * L ≤
          C * d * L := by
        apply mul_le_mul_of_nonneg_right _ hL0
        apply mul_le_mul_of_nonneg_right _ hd0.le
        rw [hCdef]
        linarith
      -- the radial profiles `φ_c(t) = S((c - t)/(dρ))`
      have hdρ : 0 < d * ρ := mul_pos hd0 hρ0
      have hprof : ∀ c : ℝ,
          ContDiff ℝ 1 (fun t => Real.smoothTransition ((c - t) / (d * ρ))) ∧
          (∀ t, 0 ≤ Real.smoothTransition ((c - t) / (d * ρ)) ∧
            Real.smoothTransition ((c - t) / (d * ρ)) ≤ 1) ∧
          (∀ t, t ≤ c - d * ρ → Real.smoothTransition ((c - t) / (d * ρ)) = 1) ∧
          (∀ t, c ≤ t → Real.smoothTransition ((c - t) / (d * ρ)) = 0) ∧
          (∀ t, |deriv (fun t => Real.smoothTransition ((c - t) / (d * ρ))) t| ≤ κ / ρ) := by
        intro c
        refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _),
          fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
          fun t ht => Real.smoothTransition.one_of_one_le ((one_le_div hdρ).2 (by linarith)),
          fun t ht => Real.smoothTransition.zero_of_nonpos
            (div_nonpos_of_nonpos_of_nonneg (by linarith) hdρ.le), fun t => ?_⟩
        have hin : HasDerivAt (fun t : ℝ => (c - t) / (d * ρ)) (-1 / (d * ρ)) t := by
          have := ((hasDerivAt_id t).const_sub c).div_const (d * ρ)
          simpa using this
        have hS : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((c - t) / (d * ρ)))
            ((c - t) / (d * ρ)) :=
          ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
        have hcomp0 := HasDerivAt.comp t hS hin
        have hcomp : HasDerivAt (fun t => Real.smoothTransition ((c - t) / (d * ρ)))
            (deriv Real.smoothTransition ((c - t) / (d * ρ)) * (-1 / (d * ρ))) t := hcomp0
        rw [hcomp.deriv, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hdρ, hκdef]
        calc |deriv Real.smoothTransition ((c - t) / (d * ρ))| * (1 / (d * ρ)) ≤
              KS * (1 / (d * ρ)) := mul_le_mul_of_nonneg_right (hKS _) (by positivity)
          _ = KS / d / ρ := by field_simp
      have hprofcd : ∀ c : ℝ, 0 < c - d * ρ →
          ContDiff ℝ 1 (fun y : Amb n ℓ => Real.smoothTransition ((c - ‖y - ξ‖) / (d * ρ))) := by
        intro c hc
        rw [contDiff_iff_contDiffAt]
        intro y
        by_cases hy : y = ξ
        · apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
          filter_upwards [ball_mem_nhds y hc] with z hz
          rw [hy, mem_ball, dist_eq_norm] at hz
          exact (hprof c).2.2.1 _ hz.le
        · exact (hprof c).1.contDiffAt.comp y
            ((contDiffAt_norm ℝ (sub_ne_zero.2 hy)).comp y (contDiffAt_id.sub contDiffAt_const))
      -- the annulus `1/2 < |y| < b` with `b = |ξ| + ρ`
      have hlamτ2 : lam ≤ τ * (1 / 2) := by linarith
      have hb1 : ‖ξ‖ + ρ ≤ 1 := by rw [hξ]; linarith
      have hhalf : 1 / 2 < ‖ξ‖ - ρ := by rw [hξ]; linarith
      have hnorm_lo : ∀ y : Amb n ℓ, ‖ξ‖ - ‖y - ξ‖ ≤ ‖y‖ := by
        intro y
        have := norm_sub_norm_le ξ y
        rw [norm_sub_rev ξ y] at this
        linarith
      have hnorm_hi : ∀ y : Amb n ℓ, ‖y‖ ≤ ‖ξ‖ + ‖y - ξ‖ := by
        intro y
        calc ‖y‖ = ‖ξ + (y - ξ)‖ := by rw [add_sub_cancel]
          _ ≤ ‖ξ‖ + ‖y - ξ‖ := norm_add_le _ _
      -- integrals of functions squeezed against indicators
      have hint_le_ind : ∀ (f : Amb n ℓ → ℝ) (S : Set (Amb n ℓ)), MeasurableSet S →
          S ⊆ closedBall 0 1 → Continuous f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ S.indicator 1 x) →
          ∫ x, f x ∂V.weight ≤ (V.weight S).toReal := by
        intro f S hS hS1 hf hf0 hfS
        have hint : Integrable (S.indicator (1 : Amb n ℓ → ℝ)) V.weight := by
          rw [integrable_indicator_iff hS]
          exact integrableOn_const (hμsub S hS1).ne
        have hfint : Integrable f V.weight := hint.mono' hf.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hf0 x)]; exact hfS x)
        calc ∫ x, f x ∂V.weight ≤ ∫ x, S.indicator 1 x ∂V.weight :=
              integral_mono hfint hint hfS
          _ = (V.weight S).toReal := by rw [integral_indicator_one hS, measureReal_def]
      have hind_le_int : ∀ (f : Amb n ℓ → ℝ) (S : Set (Amb n ℓ)), MeasurableSet S →
          S ⊆ closedBall 0 1 → Integrable f V.weight → (∀ x, S.indicator 1 x ≤ f x) →
          (V.weight S).toReal ≤ ∫ x, f x ∂V.weight := by
        intro f S hS hS1 hfint hfS
        have hint : Integrable (S.indicator (1 : Amb n ℓ → ℝ)) V.weight := by
          rw [integrable_indicator_iff hS]
          exact integrableOn_const (hμsub S hS1).ne
        calc (V.weight S).toReal = ∫ x, S.indicator 1 x ∂V.weight := by
              rw [integral_indicator_one hS, measureReal_def]
          _ ≤ ∫ x, f x ∂V.weight := integral_mono hint hfint hfS
      -- the first inequality: `χ ≡ 1`, `φ = φ_ρ`
      have hφρcd := hprofcd ρ (by
        have e : ρ - d * ρ = (1 - d) * ρ := by ring
        rw [e]; exact mul_pos (by linarith) hρ0)
      have hP4a := conical_P4 hn V H hH hT1 hT2 hPx hPi hB1 lam (1 / 2) (‖ξ‖ + ρ) τ ρ κ ε ξ hlam
        hlamτ2 hb1 hτ0 hτ1 hρ0 hε0 (fun _ => (1 : ℝ))
        (fun t => Real.smoothTransition ((ρ - t) / (d * ρ)))
        contDiff_const (hprof ρ).1 (fun _ => ⟨zero_le_one, le_rfl⟩) (hprof ρ).2.1
        (fun α β _ => by simp) (hprof ρ).2.2.2.2
        (fun t ht => (hprof ρ).2.2.2.1 t (by linarith)) (contDiff_const.mul hφρcd)
        (fun y hy => by
          have hne : Real.smoothTransition ((ρ - ‖y - ξ‖) / (d * ρ)) ≠ 0 := by
            intro h; apply hy; rw [h, mul_zero]
          have hlt : ‖y - ξ‖ < ρ := by
            by_contra h
            push Not at h
            exact hne ((hprof ρ).2.2.2.1 _ h)
          exact ⟨by linarith [hnorm_lo y], by linarith [hnorm_hi y]⟩)
      have hEa := hE _ _ _ hA1 hI2 hI3
      simp only [one_mul] at hP4a
      have hlow : (V.weight (closedBall ξ ((1 - d) * ρ))).toReal ≤
          ∫ x, Real.smoothTransition ((ρ - ‖x - ξ‖) / (d * ρ)) ∂V.weight := by
        apply hind_le_int _ _ measurableSet_closedBall (hball1 _ h1dρ)
        · have hint : Integrable ((closedBall ξ ρ).indicator (1 : Amb n ℓ → ℝ)) V.weight := by
            rw [integrable_indicator_iff measurableSet_closedBall]
            exact integrableOn_const (hμsub _ (hball1 ρ le_rfl)).ne
          refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
          refine Eventually.of_forall fun x => ?_
          rw [Real.norm_of_nonneg ((hprof ρ).2.1 _).1]
          by_cases hx : x ∈ closedBall ξ ρ
          · rw [indicator_of_mem hx, Pi.one_apply]; exact ((hprof ρ).2.1 _).2
          · rw [indicator_of_notMem hx]
            rw [mem_closedBall, dist_eq_norm, not_le] at hx
            rw [(hprof ρ).2.2.2.1 _ hx.le]
        · intro x
          by_cases hx : x ∈ closedBall ξ ((1 - d) * ρ)
          · rw [indicator_of_mem hx, Pi.one_apply]
            rw [mem_closedBall, dist_eq_norm] at hx
            rw [(hprof ρ).2.2.1 _ (by linarith)]
          · rw [indicator_of_notMem hx]; exact ((hprof ρ).2.1 _).1
      have hup : ∫ x, Real.smoothTransition ((ρ - ‖τ⁻¹ • x - ξ‖) / (d * ρ)) ∂V.weight ≤
          (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal := by
        apply hint_le_ind _ _ measurableSet_closedBall hτB1 (by fun_prop)
          (fun x => ((hprof ρ).2.1 _).1)
        intro x
        by_cases hx : ‖τ⁻¹ • x - ξ‖ < ρ
        · have hmem : x ∈ closedBall (τ • ξ) (τ * ρ) := by
            rw [mem_closedBall, dist_eq_norm]
            have he : x - τ • ξ = τ • (τ⁻¹ • x - ξ) := by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ0.ne', one_smul]
            rw [he, norm_smul, Real.norm_of_nonneg hτ0.le]
            exact mul_le_mul_of_nonneg_left hx.le hτ0.le
          rw [indicator_of_mem hmem, Pi.one_apply]; exact ((hprof ρ).2.1 _).2
        · push Not at hx
          rw [(hprof ρ).2.2.2.1 _ hx]
          exact indicator_nonneg (fun _ _ => zero_le_one) _
      have hfirst : (V.weight (closedBall ξ ((1 - d) * ρ))).toReal ≤
          (τ ^ n)⁻¹ * (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal + C * d * L := by
        rw [abs_le] at hP4a
        have h1 := mul_le_mul_of_nonneg_left hup (inv_nonneg.2 (pow_nonneg hτ0.le n))
        linarith [hP4a.1]
      refine ⟨hconv _ _ _ _ (hμsub _ (hball1 _ h1dρ)) (hμsub _ hτB1)
        (inv_nonneg.2 (pow_nonneg hτ0.le n)) hCdL0 hfirst, ?_⟩
      -- the second inequality: `χ_k(u) = S(k(u - 1/2)) S(k(b - u))`, `φ = φ_{(1+d)ρ}`
      have hk : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
      obtain ⟨χk, hχkdef⟩ : ∃ χk : ℕ → ℝ → ℝ, χk = fun (j : ℕ) (u : ℝ) =>
          Real.smoothTransition (((j : ℝ) + 1) * (u - 1 / 2)) *
            Real.smoothTransition (((j : ℝ) + 1) * (‖ξ‖ + ρ - u)) := ⟨_, rfl⟩
      have hf1cd : ∀ j : ℕ, ContDiff ℝ 1 (fun u : ℝ => Real.smoothTransition (((j : ℝ) + 1) * (u - 1 / 2))) :=
        fun j => Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
      have hf2cd : ∀ j : ℕ, ContDiff ℝ 1 (fun u : ℝ => Real.smoothTransition (((j : ℝ) + 1) * (‖ξ‖ + ρ - u))) :=
        fun j => Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
      have hχcd : ∀ j, ContDiff ℝ 1 (χk j) := by
        intro j
        rw [hχkdef]
        exact (hf1cd j).mul (hf2cd j)
      have hχb : ∀ j u, 0 ≤ χk j u ∧ χk j u ≤ 1 := by
        intro j u
        rw [hχkdef]
        exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
          mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
            (Real.smoothTransition.le_one _)⟩
      have hχ0 : ∀ j u, u ≤ 1 / 2 → χk j u = 0 := by
        intro j u hu
        have h0 : ((j : ℝ) + 1) * (u - 1 / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hk j).le (by linarith)
        rw [hχkdef]
        simp only
        rw [Real.smoothTransition.zero_of_nonpos h0, zero_mul]
      have hχsupp : ∀ j u, χk j u ≠ 0 → 1 / 2 < u ∧ u < ‖ξ‖ + ρ := by
        intro j u h
        constructor
        · by_contra hu
          push Not at hu
          exact h (hχ0 j u hu)
        · by_contra hu
          push Not at hu
          apply h
          have h0 : ((j : ℝ) + 1) * (‖ξ‖ + ρ - u) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (hk j).le (by linarith)
          rw [hχkdef]
          simp only
          rw [Real.smoothTransition.zero_of_nonpos h0, mul_zero]
      have hχlim : ∀ u, Tendsto (fun j => χk j u) atTop
          (𝓝 (if 1 / 2 < u ∧ u < ‖ξ‖ + ρ then 1 else 0)) := by
        intro u
        split_ifs with hu
        · apply tendsto_const_nhds.congr'
          have hu1 : 0 < u - 1 / 2 := by linarith [hu.1]
          have hu2 : 0 < ‖ξ‖ + ρ - u := by linarith [hu.2]
          obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / (u - 1 / 2)) (1 / (‖ξ‖ + ρ - u)))
          filter_upwards [eventually_ge_atTop N] with j hj
          have hj' : (N : ℝ) ≤ j := Nat.cast_le.2 hj
          have h1 : 1 ≤ ((j : ℝ) + 1) * (u - 1 / 2) := by
            have : 1 / (u - 1 / 2) < (j : ℝ) + 1 :=
              lt_of_le_of_lt (le_max_left _ _) (by linarith)
            rw [div_lt_iff₀ hu1] at this
            linarith
          have h2 : 1 ≤ ((j : ℝ) + 1) * (‖ξ‖ + ρ - u) := by
            have : 1 / (‖ξ‖ + ρ - u) < (j : ℝ) + 1 :=
              lt_of_le_of_lt (le_max_right _ _) (by linarith)
            rw [div_lt_iff₀ hu2] at this
            linarith
          rw [hχkdef]
          simp only
          rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
            mul_one]
        · apply tendsto_const_nhds.congr
          intro j
          by_contra h
          exact hu (hχsupp j u (Ne.symm h))
      -- total variation of `χ_k` is at most `2`
      have hχTV : ∀ j α β, α ≤ β → ∫ u in α..β, |deriv (χk j) u| ≤ 2 := by
        intro j α β hαβ
        obtain ⟨f₁, hf₁⟩ : ∃ f : ℝ → ℝ, f = fun u => Real.smoothTransition (((j : ℝ) + 1) * (u - 1 / 2)) :=
          ⟨_, rfl⟩
        obtain ⟨f₂, hf₂⟩ : ∃ f : ℝ → ℝ, f = fun u => Real.smoothTransition (((j : ℝ) + 1) * (‖ξ‖ + ρ - u)) :=
          ⟨_, rfl⟩
        have hc₁ : ContDiff ℝ 1 f₁ := by rw [hf₁]; exact hf1cd j
        have hc₂ : ContDiff ℝ 1 f₂ := by rw [hf₂]; exact hf2cd j
        have hm₁ : Monotone f₁ := by
          rw [hf₁]
          intro u v huv
          exact Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left (by linarith) (hk j).le)
        have ha₂ : Antitone f₂ := by
          rw [hf₂]
          intro u v huv
          exact Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left (by linarith) (hk j).le)
        have hb₁ : ∀ u, 0 ≤ f₁ u ∧ f₁ u ≤ 1 := fun u => by
          rw [hf₁]; exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
        have hb₂ : ∀ u, 0 ≤ f₂ u ∧ f₂ u ≤ 1 := fun u => by
          rw [hf₂]; exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
        have hχeq : χk j = fun u => f₁ u * f₂ u := by rw [hχkdef, hf₁, hf₂]
        have hderiv : ∀ u, deriv (χk j) u = deriv f₁ u * f₂ u + f₁ u * deriv f₂ u := by
          intro u
          rw [hχeq]
          exact deriv_mul (hc₁.differentiable one_ne_zero u) (hc₂.differentiable one_ne_zero u)
        have hbound : ∀ u, |deriv (χk j) u| ≤ deriv f₁ u - deriv f₂ u := by
          intro u
          rw [hderiv u]
          have h1 : 0 ≤ deriv f₁ u := hm₁.deriv_nonneg
          have h2 : deriv f₂ u ≤ 0 := ha₂.deriv_nonpos
          have p1 : deriv f₁ u * f₂ u ≤ deriv f₁ u := mul_le_of_le_one_right h1 (hb₂ u).2
          have p2 : 0 ≤ deriv f₁ u * f₂ u := mul_nonneg h1 (hb₂ u).1
          have p3 : f₁ u * deriv f₂ u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hb₁ u).1 h2
          have p4 : deriv f₂ u ≤ f₁ u * deriv f₂ u := le_mul_of_le_one_left h2 (hb₁ u).2
          rw [abs_le]
          constructor <;> linarith
        have hd₁ : Continuous (deriv f₁) := hc₁.continuous_deriv le_rfl
        have hd₂ : Continuous (deriv f₂) := hc₂.continuous_deriv le_rfl
        calc ∫ u in α..β, |deriv (χk j) u| ≤ ∫ u in α..β, (deriv f₁ u - deriv f₂ u) :=
              intervalIntegral.integral_mono_on hαβ
                (((hχcd j).continuous_deriv le_rfl).abs.intervalIntegrable _ _)
                ((hd₁.sub hd₂).intervalIntegrable _ _) (fun u _ => hbound u)
          _ = (f₁ β - f₁ α) - (f₂ β - f₂ α) := by
              rw [intervalIntegral.integral_sub (hd₁.intervalIntegrable _ _)
                (hd₂.intervalIntegrable _ _),
                intervalIntegral.integral_deriv_eq_sub
                  (fun u _ => hc₁.differentiable one_ne_zero u) (hd₁.intervalIntegrable _ _),
                intervalIntegral.integral_deriv_eq_sub
                  (fun u _ => hc₂.differentiable one_ne_zero u) (hd₂.intervalIntegrable _ _)]
          _ ≤ 2 := by linarith [hb₁ α, hb₁ β, hb₂ α, hb₂ β]
      -- the test functions `g_k`
      have hφ2cd := hprofcd ((1 + d) * ρ) (by
        have e : (1 + d) * ρ - d * ρ = ρ := by ring
        rw [e]; exact hρ0)
      have hgkcd : ∀ j, ContDiff ℝ 1 (fun y : Amb n ℓ => χk j ‖y‖ *
          Real.smoothTransition (((1 + d) * ρ - ‖y - ξ‖) / (d * ρ))) := by
        intro j
        rw [contDiff_iff_contDiffAt]
        intro y
        by_cases hy : ‖y‖ < 1 / 2
        · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
          rw [hχ0 j _ (le_of_lt hz), zero_mul]
        · have hy0 : y ≠ 0 := by
            intro h
            rw [h, norm_zero] at hy
            norm_num at hy
          exact ((hχcd j).contDiffAt.comp y (contDiffAt_norm ℝ hy0)).mul hφ2cd.contDiffAt
      have hEb := hE _ _ _ hA1 hI2 hI3
      have hP4b : ∀ j : ℕ, (τ ^ n)⁻¹ * ∫ x, χk j ‖τ⁻¹ • x‖ *
          Real.smoothTransition (((1 + d) * ρ - ‖τ⁻¹ • x - ξ‖) / (d * ρ)) ∂V.weight ≤
          (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal + C * d * L := by
        intro j
        have h := conical_P4 hn V H hH hT1 hT2 hPx hPi hB1 lam (1 / 2) (‖ξ‖ + ρ) τ ρ κ ε ξ hlam
          hlamτ2 hb1 hτ0 hτ1 hρ0 hε0 (χk j)
          (fun t => Real.smoothTransition (((1 + d) * ρ - t) / (d * ρ)))
          (hχcd j) (hprof _).1 (hχb j) (hprof _).2.1 (hχTV j) (hprof _).2.2.2.2
          (fun t ht => (hprof _).2.2.2.1 t (by
            have : (1 + d) * ρ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ0.le
            linarith)) (hgkcd j)
          (fun y hy => hχsupp j _ (left_ne_zero_of_mul hy))
        have hgk_le : ∫ x, χk j ‖x‖ * Real.smoothTransition (((1 + d) * ρ - ‖x - ξ‖) / (d * ρ))
            ∂V.weight ≤ (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal := by
          apply hint_le_ind _ _ (measurableSet_closedBall.inter measurableSet_closedBall)
            inter_subset_right (hgkcd j).continuous
            (fun x => mul_nonneg (hχb j _).1 ((hprof _).2.1 _).1)
          intro x
          by_cases hx : χk j ‖x‖ * Real.smoothTransition (((1 + d) * ρ - ‖x - ξ‖) / (d * ρ)) = 0
          · rw [hx]
            exact indicator_nonneg (fun _ _ => zero_le_one) _
          · have h1 := hχsupp j _ (left_ne_zero_of_mul hx)
            have h2 : ‖x - ξ‖ < (1 + d) * ρ := by
              by_contra hh
              push Not at hh
              exact hx (by rw [(hprof _).2.2.2.1 _ hh, mul_zero])
            have hmem : x ∈ closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1 :=
              ⟨by rw [mem_closedBall, dist_eq_norm]; exact h2.le,
                by rw [mem_closedBall, dist_zero_right]; linarith [h1.2]⟩
            rw [indicator_of_mem hmem, Pi.one_apply]
            exact mul_le_one₀ (hχb j _).2 ((hprof _).2.1 _).1 ((hprof _).2.1 _).2
        rw [abs_le] at h
        linarith [h.2]
      -- the limit `k → ∞`
      obtain ⟨G, hGdef⟩ : ∃ G : Amb n ℓ → ℝ, G = fun x =>
          (if 1 / 2 < ‖τ⁻¹ • x‖ ∧ ‖τ⁻¹ • x‖ < ‖ξ‖ + ρ then 1 else 0) *
            Real.smoothTransition (((1 + d) * ρ - ‖τ⁻¹ • x - ξ‖) / (d * ρ)) := ⟨_, rfl⟩
      obtain ⟨gk, hgkdef⟩ : ∃ gk : ℕ → Amb n ℓ → ℝ, gk = fun j y =>
          χk j ‖y‖ * Real.smoothTransition (((1 + d) * ρ - ‖y - ξ‖) / (d * ρ)) := ⟨_, rfl⟩
      have hgkc : ∀ j, Continuous (gk j) := fun j => by rw [hgkdef]; exact (hgkcd j).continuous
      have hP4b' : ∀ j : ℕ, (τ ^ n)⁻¹ * ∫ x, gk j (τ⁻¹ • x) ∂V.weight ≤
          (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal + C * d * L := by
        intro j
        rw [hgkdef]
        exact hP4b j
      have hgkm : ∀ j : ℕ, AEStronglyMeasurable (fun x : Amb n ℓ => gk j (τ⁻¹ • x)) V.weight :=
        fun j => by
          have hc := hgkc j
          exact Continuous.aestronglyMeasurable (by fun_prop)
      have hGlim : ∀ x, Tendsto (fun j : ℕ => gk j (τ⁻¹ • x)) atTop (𝓝 (G x)) := by
        intro x
        rw [hgkdef, hGdef]
        exact (hχlim _).mul_const _
      have hB1int : Integrable ((closedBall (0 : Amb n ℓ) 1).indicator (1 : Amb n ℓ → ℝ))
          V.weight := by
        rw [integrable_indicator_iff measurableSet_closedBall]
        exact integrableOn_const hμ1.ne
      have hgkb : ∀ j : ℕ, ∀ x : Amb n ℓ, ‖gk j (τ⁻¹ • x)‖ ≤
          (closedBall (0 : Amb n ℓ) 1).indicator 1 x := by
        intro j x
        rw [hgkdef]
        simp only
        by_cases hx : χk j ‖τ⁻¹ • x‖ *
            Real.smoothTransition (((1 + d) * ρ - ‖τ⁻¹ • x - ξ‖) / (d * ρ)) = 0
        · rw [hx, norm_zero]
          exact indicator_nonneg (fun _ _ => zero_le_one) _
        · have h1 := hχsupp j _ (left_ne_zero_of_mul hx)
          have hmem : x ∈ closedBall (0 : Amb n ℓ) 1 := by
            rw [mem_closedBall, dist_zero_right]
            have h2 := h1.2
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ0.le)] at h2
            have h3 : τ⁻¹ * ‖x‖ < 1 := lt_of_lt_of_le h2 hb1
            rw [inv_mul_lt_iff₀ hτ0, mul_one] at h3
            linarith
          have hχn := hχb j ‖τ⁻¹ • x‖
          have hφn := (hprof ((1 + d) * ρ)).2.1 ‖τ⁻¹ • x - ξ‖
          rw [indicator_of_mem hmem, Pi.one_apply, Real.norm_of_nonneg (mul_nonneg hχn.1 hφn.1)]
          exact mul_le_one₀ hχn.2 hφn.1 hφn.2
      have hlimG : Tendsto (fun j : ℕ => ∫ x, gk j (τ⁻¹ • x) ∂V.weight) atTop
          (𝓝 (∫ x, G x ∂V.weight)) :=
        tendsto_integral_of_dominated_convergence _ hgkm hB1int
          (fun j => Eventually.of_forall (hgkb j)) (Eventually.of_forall hGlim)
      have hGle : (τ ^ n)⁻¹ * ∫ x, G x ∂V.weight ≤
          (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal + C * d * L :=
        le_of_tendsto' (hlimG.const_mul _) hP4b'
      -- `∫ G ≥ μ(B_{τρ}(τξ))`: the only bad point of the ball is `τ (1 + ρ/|ξ|) ξ`
      have hstrict : ∀ y : Amb n ℓ, ‖y - ξ‖ ≤ ρ → ‖y‖ = ‖ξ‖ + ρ → y = (1 + ρ / ‖ξ‖) • ξ := by
        intro y hy1 hy2
        obtain ⟨w, hwdef⟩ : ∃ w : Amb n ℓ, w = y - ξ := ⟨_, rfl⟩
        have hyw : y = ξ + w := by rw [hwdef]; abel
        have hw1 : ‖w‖ = ρ := by
          have h := hnorm_hi y
          rw [← hwdef] at h hy1
          linarith
        have hsq : ‖ξ + w‖ ^ 2 = (‖ξ‖ + ‖w‖) ^ 2 := by rw [← hyw, hy2, hw1]
        have hinner : inner ℝ ξ w = ‖ξ‖ * ‖w‖ := by
          rw [norm_add_sq_real] at hsq
          linear_combination hsq / 2
        have h2 := inner_eq_norm_mul_iff_real.1 hinner
        rw [hw1] at h2
        have hw' : w = (ρ / ‖ξ‖) • ξ := by
          have h3 : (‖ξ‖)⁻¹ • (‖ξ‖ • w) = (‖ξ‖)⁻¹ • (ρ • ξ) := by rw [h2]
          rw [smul_smul, inv_mul_cancel₀ hξ0.ne', one_smul, smul_smul] at h3
          rw [h3, div_eq_inv_mul]
        rw [hyw, hw', add_smul, one_smul]
      have hpt0 : ∀ p : Amb n ℓ, V.weight {p} = 0 := by
        intro p
        have hH0 : (μHE[n] : Measure (Amb n ℓ)) {p} = 0 := by
          rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
          have hnull := MeasureTheory.Measure.nullSingletonClass_hausdorff (X := Amb n ℓ)
            (d := (n : ℝ)) (Nat.cast_pos.2 (by omega))
          rw [hnull.measure_singleton p, smul_zero]
        rw [RectifiableVarifold.weight, withDensity_apply _ (measurableSet_singleton p)]
        apply setLIntegral_measure_zero
        rw [Measure.restrict_apply (measurableSet_singleton p)]
        exact measure_mono_null inter_subset_left hH0
      have hGm : AEStronglyMeasurable G V.weight :=
        aestronglyMeasurable_of_tendsto_ae _ hgkm (Eventually.of_forall hGlim)
      have hGint : Integrable G V.weight :=
        hB1int.mono' hGm (Eventually.of_forall fun x =>
          le_of_tendsto' ((hGlim x).norm) fun j => hgkb j x)
      have hGlow : (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal ≤ ∫ x, G x ∂V.weight := by
        obtain ⟨p, hpdef⟩ : ∃ p : Amb n ℓ, p = τ • ((1 + ρ / ‖ξ‖) • ξ) := ⟨_, rfl⟩
        have hsplit : V.weight (closedBall (τ • ξ) (τ * ρ) \ {p}) =
            V.weight (closedBall (τ • ξ) (τ * ρ)) := measure_diff_null (hpt0 p)
        rw [← hsplit]
        apply hind_le_int _ _ (measurableSet_closedBall.diff (measurableSet_singleton p))
          (sdiff_subset.trans hτB1) hGint
        intro x
        by_cases hx : x ∈ closedBall (τ • ξ) (τ * ρ) \ {p}
        · rw [indicator_of_mem hx, Pi.one_apply]
          have hx1 := hx.1
          have hx2 := hx.2
          have hyξ : ‖τ⁻¹ • x - ξ‖ ≤ ρ := by
            rw [mem_closedBall, dist_eq_norm] at hx1
            have he : x - τ • ξ = τ • (τ⁻¹ • x - ξ) := by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ0.ne', one_smul]
            rw [he, norm_smul, Real.norm_of_nonneg hτ0.le] at hx1
            exact le_of_mul_le_mul_left hx1 hτ0
          have hylo : 1 / 2 < ‖τ⁻¹ • x‖ := by linarith [hnorm_lo (τ⁻¹ • x)]
          have hyhi : ‖τ⁻¹ • x‖ < ‖ξ‖ + ρ := by
            rcases lt_or_eq_of_le (show ‖τ⁻¹ • x‖ ≤ ‖ξ‖ + ρ by linarith [hnorm_hi (τ⁻¹ • x)])
              with h | h
            · exact h
            · exfalso
              apply hx2
              have h' := hstrict _ hyξ h
              rw [mem_singleton_iff, hpdef, ← h', smul_smul, mul_inv_cancel₀ hτ0.ne', one_smul]
          have hφ1 : Real.smoothTransition (((1 + d) * ρ - ‖τ⁻¹ • x - ξ‖) / (d * ρ)) = 1 :=
            (hprof _).2.2.1 _ (by
              have e : (1 + d) * ρ - d * ρ = ρ := by ring
              linarith)
          rw [hGdef]
          simp only
          rw [if_pos ⟨hylo, hyhi⟩, hφ1, one_mul]
        · rw [indicator_of_notMem hx, hGdef]
          simp only
          exact mul_nonneg (by split_ifs <;> norm_num) ((hprof _).2.1 _).1
      have hsecond : (τ ^ n)⁻¹ * (V.weight (closedBall (τ • ξ) (τ * ρ))).toReal ≤
          (V.weight (closedBall ξ ((1 + d) * ρ) ∩ closedBall 0 1)).toReal + C * d * L :=
        (mul_le_mul_of_nonneg_left hGlow (inv_nonneg.2 (pow_nonneg hτ0.le n))).trans hGle
      exact hconv2 _ _ _ _ (hμsub _ hτB1) (hμsub _ inter_subset_right)
        (inv_nonneg.2 (pow_nonneg hτ0.le n)) hCdL0 hsecond

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
