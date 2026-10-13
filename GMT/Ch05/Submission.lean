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

/-- Choice of the constants `δ_P, C_P` for the density bounds in the proof of Simon Ch. 5, 5.2
(pure real analysis; `κ > 0`, `ω > 0` arbitrary).  With `Λ = t/κ` and `q = (1 + t)/(1 − 3t)ⁿ`, the
functions `G₊ = e^{2Λ} qω + 2e^Λ Λ`, `G₋ = e^{−Λ}(ω − Λ)` and `G_c = e^Λ(e^Λ qω + Λ − ω)` are `C¹` on
`(−1/24, 1/4)` (where `1 − 3t > 1/4`) with `G₊(0) = G₋(0) = ω`, `G_c(0) = 0`; bounding their
derivatives by `A` on `[0, t₀]`, `t₀ = min{1/8, κ}`, the mean value theorem gives the three bounds
for `0 < t ≤ δ_P` with `C_P = max{1, A/ω}` and `δ_P = min{t₀, 1/(2C_P)}`. -/
theorem allard52_density_constants : ∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ δP ≤ κ ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δP → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + CP * t) * ω ∧ (1 - CP * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω) ≤ CP * ω * t := by
  intro n κ ω hκ hω
  -- The radius `t₀ = min (1/8) κ`; `[0, t₀]` sits inside the open interval `I = (-1/24, 1/4)`,
  -- on which `1 - 3 t > 1/4 > 0`.
  obtain ⟨t₀, ht₀pos, ht₀le, ht₀κ⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 / 8 ∧ t₀ ≤ κ :=
    ⟨min (1 / 8) κ, lt_min (by norm_num) hκ, min_le_left _ _, min_le_right _ _⟩
  have hsub : Icc (0 : ℝ) t₀ ⊆ Ioo (-1 / 24 : ℝ) (1 / 4) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- Mean value inequality for a `C¹` function on `I`: its derivative is bounded on the compact
  -- `[0, t₀]` by some `A`, hence `|G t - G 0| ≤ A t` for `t ∈ [0, t₀]`.
  have key : ∀ G : ℝ → ℝ, ContDiffOn ℝ 1 G (Ioo (-1 / 24 : ℝ) (1 / 4)) →
      ∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) t₀, |G t - G 0| ≤ A * t := by
    intro G hG
    have hcont : ContinuousOn (deriv G) (Ioo (-1 / 24 : ℝ) (1 / 4)) :=
      hG.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t₀)).exists_bound_of_continuousOn
      (hcont.mono hsub)
    refine ⟨A, fun t ht => ?_⟩
    have hdiff : ∀ x ∈ Icc (0 : ℝ) t₀, DifferentiableAt ℝ G x := fun x hx =>
      (hG.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
    have h := (convex_Icc (0 : ℝ) t₀).norm_image_sub_le_of_norm_deriv_le hdiff hA
      (left_mem_Icc.2 ht₀pos.le) ht
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
  -- Smoothness of `G₊`, `G₋`, `G_c` on `I`: the denominator `(1 - 3 t)ⁿ` has no zero there.
  have hden : ∀ x ∈ Ioo (-1 / 24 : ℝ) (1 / 4), (1 - 3 * x) ^ n ≠ 0 := fun x hx =>
    pow_ne_zero _ (by linarith [hx.2] : (0 : ℝ) < 1 - 3 * x).ne'
  have hR : ContDiffOn ℝ 1 (fun t : ℝ => (1 + t) / (1 - 3 * t) ^ n * ω)
      (Ioo (-1 / 24 : ℝ) (1 / 4)) := by
    apply ContDiffOn.mul _ contDiffOn_const
    exact ContDiffOn.fun_div (by fun_prop) (by fun_prop) hden
  have hE : ContDiff ℝ 1 (fun t : ℝ => Real.exp (t / κ)) := by fun_prop
  have hE2 : ContDiff ℝ 1 (fun t : ℝ => Real.exp (2 * (t / κ))) := by fun_prop
  obtain ⟨A₁, hA₁⟩ := key (fun t => Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) +
      2 * Real.exp (t / κ) * (t / κ)) ((hE2.contDiffOn.mul hR).add (by fun_prop))
  obtain ⟨A₂, hA₂⟩ := key (fun t => Real.exp (-(t / κ)) * (ω - t / κ)) (by fun_prop)
  obtain ⟨A₃, hA₃⟩ := key (fun t => Real.exp (t / κ) *
      (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))
    (hE.contDiffOn.mul (((hE.contDiffOn.mul hR).add (by fun_prop)).sub contDiffOn_const))
  -- The constants: one bound `A` for the three derivatives, `C_P = max 1 (A/ω)` and
  -- `δ_P = min t₀ (1/(2 C_P))`.
  obtain ⟨A, hA1, hA2, hA3⟩ : ∃ A : ℝ, A₁ ≤ A ∧ A₂ ≤ A ∧ A₃ ≤ A :=
    ⟨max (max A₁ A₂) A₃, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨CP, hCP1, hCPA⟩ : ∃ CP : ℝ, 1 ≤ CP ∧ A ≤ CP * ω :=
    ⟨max 1 (A / ω), le_max_left _ _, (div_le_iff₀ hω).1 (le_max_right _ _)⟩
  have hCPpos : 0 < CP := lt_of_lt_of_le one_pos hCP1
  refine ⟨min t₀ (1 / (2 * CP)), CP, lt_min ht₀pos (by positivity),
    le_trans (min_le_left _ _) ht₀le, le_trans (min_le_left _ _) ht₀κ, hCPpos, ?_, ?_⟩
  · calc CP * min t₀ (1 / (2 * CP)) ≤ CP * (1 / (2 * CP)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCPpos.le
      _ = 1 / 2 := by field_simp
  · intro t ht htδ
    have htI : t ∈ Icc (0 : ℝ) t₀ := ⟨ht.le, le_trans htδ (min_le_left _ _)⟩
    have h1 := hA₁ t htI
    have h2 := hA₂ t htI
    have h3 := hA₃ t htI
    -- Values at `0`: `G₊(0) = G₋(0) = ω` and `G_c(0) = 0`.
    simp only [zero_div, mul_zero, neg_zero, Real.exp_zero, add_zero, sub_zero, one_pow, div_one,
      one_mul, mul_one, sub_self] at h1 h2 h3
    have hAt : A * t ≤ CP * ω * t := mul_le_mul_of_nonneg_right hCPA ht.le
    have h1' : A₁ * t ≤ A * t := mul_le_mul_of_nonneg_right hA1 ht.le
    have h2' : A₂ * t ≤ A * t := mul_le_mul_of_nonneg_right hA2 ht.le
    have h3' : A₃ * t ≤ A * t := mul_le_mul_of_nonneg_right hA3 ht.le
    refine ⟨?_, ?_, ?_⟩
    · linarith [(abs_le.1 h1).2]
    · linarith [(abs_le.1 h2).1]
    · linarith [le_abs_self (Real.exp (t / κ) *
        (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))]
/-- Simon Ch. 5, hypotheses 2.3 restricted to a sub-ball `B_r(z) ⊆ B_ρ(0)` with `0 < r ≤ ρ`:
`B_r(z) ⊆ U`, `∫_{B_r(z)} |H|ᵖ dμ_V < ∞`, `(r^{p−n} ∫_{B_r(z)} |H|ᵖ dμ_V)^{1/p} ≤ δ` and
`μ_V(B_r(z)) ≤ (1 + δ) ω_n ρⁿ`.  Since `p > n ≥ 0`, both exponents `p − n` and `1/p` are positive,
so the scaled `Lᵖ` norm is monotone under shrinking the ball, and its finiteness on `B_ρ(0)` with
`ρ^{p−n} > 0` forces `∫_{B_ρ(0)} |H|ᵖ dμ_V < ∞`. -/
theorem aal_allard_subball_bounds : ∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), V.AllardHypotheses H p δ ρ → ∀ (z : Amb n ℓ) (r : ℝ), 0 < r → r ≤ ρ → closedBall z r ⊆ closedBall 0 ρ → closedBall z r ⊆ U ∧ ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight < ⊤ ∧ V.scaledLpNorm H p z r ≤ ENNReal.ofReal δ ∧ V.weight (closedBall z r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) := by
  intro n ℓ p hp U V H δ ρ hA z r hr hrρ hball
  obtain ⟨hρ, -, -, -, hU, hmass, hK⟩ := hA
  -- `p > n ≥ 0`, so `p - n > 0` and `1 / p > 0`.
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp' : 0 < 1 / p := one_div_pos.mpr ((Nat.cast_nonneg n).trans_lt hp)
  -- `I(z, r) ≤ I(0, ρ)` by monotonicity of the lower integral in the domain.
  have hI : ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight ≤
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight := lintegral_mono_set hball
  -- `K(0, ρ) = (ρ^{p−n} I(0, ρ))^{1/p} ≤ δ < ∞` forces `ρ^{p−n} I(0, ρ) < ∞`.
  have hK' : (ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤ ENNReal.ofReal δ := hK
  have hfin : ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos hp').mp (hK'.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hball.trans hU, ?_, ?_, (measure_mono hball).trans hmass⟩
  · -- Since `ρ^{p−n} > 0`, `I(0, ρ) < ∞`, hence `I(z, r) < ∞`.
    exact hI.trans_lt (ENNReal.lt_top_of_mul_ne_top_right hfin.ne
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _)).ne')
  · -- `r^{p−n} ≤ ρ^{p−n}` and `I(z, r) ≤ I(0, ρ)` give `K(z, r) ≤ K(0, ρ) ≤ δ`.
    refine le_trans ?_ hK'
    exact ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hr.le hrρ hpn.le)) hI) hp'.le
/-- **Simon Ch. 4, 3.14 and 4.1** (radial first variation, keeping the conical term).  Let `V` have
generalized mean curvature `H` in `U`, let `B_R(y) ⊆ U`, and let `μ_V`-a.e. `x ∈ B̆_R(y)` have
`p_{T_x M} = p_P` for an `n`-dimensional subspace `P`.  If `φ ∈ C¹(ℝ)`, `φ = 1` on `(-∞, 1]`,
`φ = 0` on `[T, ∞)`, `ρ > 0` and `Tρ < R`, then with `r = |x − y|` (and `0/0 = 0` at `x = y`)
`∫ (n φ(r/ρ) + (r/ρ) φ'(r/ρ) (1 − |(x − y) − p_{T_x M}(x − y)|²/r²)) dμ_V
   = −∫ φ(r/ρ) (x − y) · H(x) dμ_V`.
Proof: test 3.14 with `X(x) = φ(r/ρ)(x − y)`, a `C¹` field supported in `B_{Tρ}(y) ⊆ U`.  For
`x ≠ y`, `DX(x) = φ(r/ρ) I + (φ'(r/ρ)/(ρr)) (x − y) ⊗ (x − y)`, and `DX = I` near `y`; tracing
against `p_P` gives the left integrand on `B̆_R(y)` off a `μ_V`-null set, while off `B̆_R(y)` both
vanish.  Integrals of `μ_V`-a.e. equal functions agree, so no integrability is needed. -/
theorem allard52_am_radial_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R : ℝ), closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH y R hR hP φ T ρ hφ hφ1 hφT hρ hTR
  -- Step 1: `φ' = 0` on `(T, ∞)`, where `φ` is constant.
  have hφ'T : ∀ u, T < u → deriv φ u = 0 := by
    intro u hu
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      exact hφT t (le_of_lt ht)
    rw [h.deriv_eq]
    simp
  have hU : closedBall y (T * ρ) ⊆ U := (closedBall_subset_closedBall hTR.le).trans hR
  -- Step 2: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, X = fun x => φ (‖x - y‖ / ρ) • (x - y) := ⟨_, rfl⟩
  have hXball : ∀ x ∈ ball y ρ, X =ᶠ[𝓝 x] fun z => z - y := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    have : ‖z - y‖ / ρ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      rw [div_le_one hρ]; exact hz.le
    simp [hX, hφ1 _ this]
  have hXcd : ContDiff ℝ 1 X := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxy : x = y
    · exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq
        (hXball x (by rw [hxy]; exact mem_ball_self hρ))
    · rw [hX]
      have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hxy)
      have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
        hφ.contDiffAt.comp x (h1.div_const ρ)
      exact h2.smul (contDiffAt_id.sub contDiffAt_const)
  -- `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
  have hXzero : ∀ z, T * ρ < ‖z - y‖ → X z = 0 := by
    intro z hz
    have hT : T ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; exact hz.le
    rw [hX]; simp [hφT _ hT]
  have hsupp : tsupport X ⊆ closedBall y (T * ρ) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    exact hz (hXzero z h)
  have hXcs : HasCompactSupport X :=
    (isCompact_closedBall y (T * ρ)).of_isClosed_subset (isClosed_tsupport X) hsupp
  -- Step 3: first variation.
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  have hRHS : (fun x => inner ℝ (X x) (H x)) =
      fun x => φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) := by
    funext x; rw [hX]; exact real_inner_smul_left _ _ _
  rw [hRHS] at key
  -- Step 4: for `x ≠ y`, `DX(x) = φ(r/ρ) id + ρ⁻¹ r⁻¹ φ'(r/ρ) ((x - y) · ⬝) (x - y)`.
  have hXderiv : ∀ x, x ≠ y → HasFDerivAt X
      (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (deriv φ (‖x - y‖ / ρ) / (ρ * ‖x - y‖)) • (innerSL ℝ (x - y)).smulRight (x - y)) x := by
    intro x hxy
    have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hnorm : HasFDerivAt (fun z : Amb n ℓ => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
      have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt x
        (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y).norm_sq
      convert h using 1
      · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
      · ext v; simp [Real.sqrt_sq hr.le]; field_simp
    have hcomp : HasDerivAt (fun t => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) / ρ) ‖x - y‖ :=
      (((hφ.differentiable one_ne_zero) (‖x - y‖ / ρ)).hasDerivAt.comp ‖x - y‖
        ((hasDerivAt_id' ‖x - y‖).div_const ρ)).congr_deriv (mul_one_div _ _)
    have hc := (hcomp.comp_hasFDerivAt x hnorm).smul (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    have hfun : X = ((fun t => φ (t / ρ)) ∘ fun z : Amb n ℓ => ‖z - y‖) • fun z => z - y := by
      rw [hX]; rfl
    rw [hfun]
    refine hc.congr_fderiv ?_
    ext v
    simp
    ring
  -- Step 5: trace facts.
  have htrP : ∀ P : Submodule ℝ (Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    intro P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.trace_id]
  have htr : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (u : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) ((a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        a * Module.finrank ℝ P + c * inner ℝ u (P.starProjection u) := by
    intro P a c u
    have hcomp : (a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap =
        a • P.starProjection.toLinearMap +
          c • ((innerSL ℝ u).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight u := by
      ext w; simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrP]
    simp
  -- Step 6: `div_M X = G` off a `μ_V`-null set.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    by_cases hxB : x ∈ ball y R
    · obtain ⟨P, hPn, hPx⟩ := hx hxB
      rw [RectifiableVarifold.divM, hPx]
      by_cases hxy : x = y
      · have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
          rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
          exact (hasFDerivAt_sub_const y).fderiv
        rw [hfd]
        simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
        subst hxy
        simp [hφ1 0 zero_le_one]
      · rw [(hXderiv x hxy).fderiv, htr, hPn]
        have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
        have h0 : inner ℝ ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y)) = 0 :=
          Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
        have h1 : inner ℝ (x - y) (P.starProjection (x - y)) = ‖P.starProjection (x - y)‖ ^ 2 := by
          calc inner ℝ (x - y) (P.starProjection (x - y))
              = inner ℝ (((x - y) - P.starProjection (x - y)) + P.starProjection (x - y))
                  (P.starProjection (x - y)) := by rw [sub_add_cancel]
            _ = ‖P.starProjection (x - y)‖ ^ 2 := by
              rw [inner_add_left, h0, zero_add, real_inner_self_eq_norm_sq]
        have h2 : ‖x - y‖ ^ 2 =
            ‖(x - y) - P.starProjection (x - y)‖ ^ 2 + ‖P.starProjection (x - y)‖ ^ 2 := by
          have := norm_add_sq_real ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y))
          rw [sub_add_cancel, h0] at this
          linarith
        rw [h1]
        field_simp
        linear_combination (deriv φ (‖x - y‖ / ρ)) * h2
    · -- Outside `B̆_R(y)`: `X = 0` near `x`, and `φ = φ' = 0` at `r/ρ > T`.
      have hr : T * ρ < ‖x - y‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hxB; linarith
      have hfd : fderiv ℝ X x = 0 := by
        have h : X =ᶠ[𝓝 x] fun _ => (0 : Amb n ℓ) := by
          filter_upwards [(isOpen_lt continuous_const
            ((continuous_id.sub continuous_const).norm)).mem_nhds hr] with z hz
          exact hXzero z hz
        rw [h.fderiv_eq]
        simp
      have hu : T < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; exact hr
      rw [RectifiableVarifold.divM, hfd]
      simp [hφT _ hu.le, hφ'T _ hu]
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
/-- **Simon Ch. 4, §3 (p. 90) and 4.7 (p. 94)**: the radial cutoffs of the monotonicity argument,
with `ε ↓ 0`.  There are `C¹` nonincreasing `φ k : ℝ → [0, 1]` with `φ k = 1` on `(-∞, 1]` and
`φ k = 0` on `[1 + ε k, ∞)`, where `0 < ε k ≤ 1` and `ε k → 0`.
With `S = Real.smoothTransition` (`C^∞`, monotone, `[0, 1]`-valued, `0` on `(-∞, 0]` and `1` on
`[1, ∞)`) take `ε k = 1 / (k + 2)` and `φ k u = 1 - S ((u - 1) (k + 2))`: the argument
`(u - 1) (k + 2)` is `≤ 0` for `u ≤ 1` and `≥ 1` for `u ≥ 1 + ε k`. -/
theorem allard52_amcl_cutoff_sequence : ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) ∧ (∀ k u, u ≤ 1 → φ k u = 1) ∧ (∀ k u, 1 + ε k ≤ u → φ k u = 0) := by
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  refine ⟨fun k u => 1 - Real.smoothTransition ((u - 1) * ((k : ℝ) + 2)),
    fun k => 1 / ((k : ℝ) + 2), fun k => ⟨by positivity, ?_⟩, ?_, fun k => ?_, fun k u v huv => ?_,
    fun k u => ⟨?_, ?_⟩, fun k u hu => ?_, fun k u hu => ?_⟩
  -- (a) `ε k ≤ 1 / 2 ≤ 1`
  · rw [div_le_one (hk k)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- (b) `ε k → 0` since `k + 2 → ∞`
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- (c) a constant minus `S` composed with an affine map
  · exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).mul contDiff_const))
  -- (d) `u ≤ v` gives `(u - 1) (k + 2) ≤ (v - 1) (k + 2)`, and `S` is monotone
  · exact sub_le_sub_left (Real.smoothTransition.monotone
      (mul_le_mul_of_nonneg_right (sub_le_sub_right huv 1) (hk k).le)) 1
  -- (e) `0 ≤ S ≤ 1`
  · exact sub_nonneg.2 (Real.smoothTransition.le_one _)
  · exact sub_le_self _ (Real.smoothTransition.nonneg _)
  -- (f) `u ≤ 1` makes the argument `≤ 0`, where `S = 0`
  · dsimp only
    rw [Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) (hk k).le), sub_zero]
  -- (g) `u ≥ 1 + ε k` makes the argument `≥ 1`, where `S = 1`
  · dsimp only at hu ⊢
    have h1 : 1 / ((k : ℝ) + 2) ≤ u - 1 := by linarith
    rw [div_le_iff₀ (hk k)] at h1
    rw [Real.smoothTransition.one_of_one_le h1, sub_self]
/-- **Simon Ch. 4, 4.7–4.8 (p. 94)**: the `ε ↓ 0` limit of the cutoff integrals over `(0, t]`.
With `β = n / p ∈ [0, 1)` and `κ = (p - n) / (4p)`, the majorant `2κΛR⁻¹ (τ / R)^{-β}` equals
`C τ^{-β}` with `C = 2κΛR⁻¹ R^β`; it is integrable on `[0, t]` with integral
`C t^{1-β} / (1 - β) = (Λ / 2) (t / R)^{1-β}`, since `2κ / (1 - β) = 1 / 2`.  Dominated convergence
gives the limit, and the eventual bound `|∫₀ᵗ a k| ≤ ∫₀ᵗ C τ^{-β}` passes to it. -/
theorem allard52_amcl_interval_limit : ∀ (n : ℕ) (p R Λ t : ℝ) (a : ℕ → ℝ → ℝ) (g : ℝ → ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < t → (∀ᶠ k in atTop, ∀ τ : ℝ, 0 < τ → τ ≤ t → ContinuousAt (a k) τ ∧ |a k τ| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-((n : ℝ) / p))) → (∀ τ : ℝ, 0 < τ → τ ≤ t → Tendsto (fun k => a k τ) atTop (𝓝 (g τ))) → Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (∫ τ in (0)..t, g τ)) ∧ |∫ τ in (0)..t, g τ| ≤ Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p) := by
  intro n p R Λ t a g hnp hR _hΛ ht hev hlim
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  set β : ℝ := (n : ℝ) / p with hβ
  have hβ1 : β < 1 := (div_lt_one hp).2 hnp
  set C : ℝ := 2 * ((p - n) / (4 * p)) * Λ / R * R ^ β with hC
  -- (1) the majorant is `C τ^{-β}` for `τ ≥ 0`
  have hb_eq : ∀ τ : ℝ, 0 ≤ τ →
      2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-β) = C * τ ^ (-β) := by
    intro τ hτ
    rw [Real.div_rpow hτ hR.le, Real.rpow_neg hR.le, div_inv_eq_mul, hC]
    ring
  have hI : uIoc (0 : ℝ) t = Ioc 0 t := uIoc_of_le ht.le
  -- (2) `C τ^{-β}` is integrable on `[0, t]` since `-β > -1`
  have hb_int : IntervalIntegrable (fun τ => C * τ ^ (-β)) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  -- (3) its integral is `C t^{1-β} / (1 - β) = (Λ / 2) (t / R)^{1-β}`, as `0^{1-β} = 0`
  have hb_val : ∫ τ in (0 : ℝ)..t, C * τ ^ (-β) = Λ / 2 * (t / R) ^ (1 - β) := by
    have h1β : 1 - β ≠ 0 := by linarith
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), neg_add_eq_sub,
      Real.zero_rpow h1β, sub_zero, Real.div_rpow ht.le hR.le, Real.rpow_sub hR, Real.rpow_one, hC]
    have hpn : p - n ≠ 0 := by linarith
    have h1β' : 1 - β = (p - n) / p := by rw [hβ]; field_simp
    rw [h1β']
    have hRβ : R ^ β ≠ 0 := (Real.rpow_pos_of_pos hR β).ne'
    generalize t ^ ((p - n) / p) = T
    field_simp
    ring
  -- (4) dominated convergence on `Ι 0 t = (0, t]`: eventually `a k` is continuous there, hence
  -- measurable, and dominated by `C τ^{-β}`
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (a k) (volume.restrict (uIoc 0 t)) := by
    filter_upwards [hev] with k hk
    rw [hI]
    exact ContinuousOn.aestronglyMeasurable
      (fun τ hτ => (hk τ hτ.1 hτ.2).1.continuousWithinAt) measurableSet_Ioc
  have hbound : ∀ᶠ k in atTop, ∀ᵐ τ ∂volume, τ ∈ uIoc 0 t → ‖a k τ‖ ≤ C * τ ^ (-β) := by
    filter_upwards [hev] with k hk
    refine Eventually.of_forall (fun τ hτ => ?_)
    rw [hI] at hτ
    rw [Real.norm_eq_abs, ← hb_eq τ hτ.1.le]
    exact (hk τ hτ.1 hτ.2).2
  have hlim' : ∀ᵐ τ ∂volume, τ ∈ uIoc 0 t → Tendsto (fun k => a k τ) atTop (𝓝 (g τ)) := by
    refine Eventually.of_forall (fun τ hτ => ?_)
    rw [hI] at hτ
    exact hlim τ hτ.1 hτ.2
  have hT : Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (∫ τ in (0)..t, g τ)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hb_int hlim'
  refine ⟨hT, ?_⟩
  -- (5) eventually `|∫₀ᵗ a k| ≤ ∫₀ᵗ C τ^{-β}`, and this passes to the limit
  have hk_le : ∀ᶠ k in atTop, |∫ τ in (0)..t, a k τ| ≤ ∫ τ in (0 : ℝ)..t, C * τ ^ (-β) := by
    filter_upwards [hbound] with k hk
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht.le ?_ hb_int
    filter_upwards [hk] with τ hτ h
    exact hτ (hI ▸ h)
  rw [← hb_val]
  exact le_of_tendsto hT.abs hk_le
/-- **Simon Ch. 4, 4.7 (p. 94)**: the limit `ε ↓ 0` of "integrating from `σ` to `ρ` and letting
`ε ↓ 0`", for any `g : ℝ^{n+ℓ} → [0, ∞]` (no measurability is needed).  If `s > 0`, `ε k → 0`,
`c k → L` and eventually `∫_{B_r(y) \ B̆_{(1 + ε k) s}(y)} g dμ ≤ c k`, then
`∫_{B_r(y) \ B_s(y)} g dμ ≤ L`.
The sets `D j = B_r(y) \ B̆_{(1 + 1 / (j + 1)) s}(y)` increase to `B_r(y) \ B_s(y)` (Archimedean
property), and each `D j` eventually lies in `B_r(y) \ B̆_{(1 + ε k) s}(y)`, so `∫_{D j} g ≤ L`;
the lower integral is continuous along directed countable unions
(`setLIntegral_iUnion_of_directed`). -/
theorem allard52_amcl_annular_lintegral_le : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ≥0∞) (y : Amb n ℓ) (ε c : ℕ → ℝ) (s r L : ℝ), 0 < s → Tendsto ε atTop (𝓝 0) → Tendsto c atTop (𝓝 L) → (∀ᶠ k in atTop, ∫⁻ x in closedBall y r \ ball y ((1 + ε k) * s), g x ∂μ ≤ ENNReal.ofReal (c k)) → ∫⁻ x in closedBall y r \ closedBall y s, g x ∂μ ≤ ENNReal.ofReal L := by
  intro n ℓ μ g y ε c s r L hs hε hc hbound
  set D : ℕ → Set (Amb n ℓ) := fun j => closedBall y r \ ball y ((1 + 1 / ((j : ℝ) + 1)) * s)
  -- the `D j` increase, since `1 / (j + 1)` decreases
  have hmono : Monotone D := by
    intro i j hij x hx
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_lt] at hx ⊢
    refine ⟨hx.1, le_trans ?_ hx.2⟩
    gcongr
  -- `⋃ j, D j = B_r(y) \ B_s(y)`: if `s < |x - y|`, pick `1 / (j + 1) < (|x - y| - s) / s`
  have hU : closedBall y r \ closedBall y s = ⋃ j, D j := by
    ext x
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_le, not_lt, mem_iUnion]
    constructor
    · rintro ⟨hxr, hxs⟩
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 hxs) hs)
      refine ⟨j, hxr, ?_⟩
      rw [lt_div_iff₀ hs] at hj
      linarith
    · rintro ⟨j, hxr, hxj⟩
      refine ⟨hxr, lt_of_lt_of_le ?_ hxj⟩
      have : 0 < 1 / ((j : ℝ) + 1) := by positivity
      nlinarith
  rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun j => ?_
  have hδ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  -- eventually `ε k < 1 / (j + 1)`, so `D j ⊆ B_r(y) \ B̆_{(1 + ε k) s}(y)`
  have hev : ∀ᶠ k in atTop, ∫⁻ x in D j, g x ∂μ ≤ ENNReal.ofReal (c k) := by
    filter_upwards [hbound, hε.eventually (eventually_lt_nhds hδ)] with k hk hεk
    refine le_trans (lintegral_mono_set ?_) hk
    intro x hx
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_lt] at hx ⊢
    refine ⟨hx.1, le_trans ?_ hx.2⟩
    gcongr
  -- `ofReal (c k) → ofReal L`
  exact ge_of_tendsto (ENNReal.tendsto_ofReal hc) hev
/-- **Simon Ch. 4, 4.2** (the scaled `Lᵖ` condition on the mean curvature).  Let `p > n`,
`R, Λ > 0`, `t ≤ R`, `κ = (p − n)/(4p)` and `Q_s = ∫_{B_s(y)} |H|ᵖ dμ ∈ [0, ∞]`.  If
`(R^{p−n} Q_R)^{1/p} ≤ κ Λ` in `[0, ∞]`, then `Q_t < ∞` and `Q_t^{1/p} ≤ κ Λ R^{n/p − 1}`.
Proof: `Q_R < ∞`, since otherwise the left side is `∞^{1/p} = ∞`; in real numbers the hypothesis
reads `R^{1 − n/p} Q_R^{1/p} ≤ κ Λ`; and `Q_t ≤ Q_R` by monotonicity in the domain. -/
theorem allard52_am_fc_lp_scale : ∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ t : ℝ), 0 < R → 0 < Λ → t ≤ R → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ ∧ (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1) := by
  intro n ℓ p hnp μ H y R Λ t hR hΛ htR hLp
  -- Notation: `Q_s = ∫_{B_s(y)} |H|ᵖ dμ`, `c = R^{p−n}` and `κ = (p − n)/(4p)`.
  set QR : ℝ≥0∞ := ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ
  set Qt : ℝ≥0∞ := ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ
  set c : ℝ := R ^ (p - n) with hc
  set κ : ℝ := (p - n) / (4 * p)
  -- Step 0: constants.
  have hp : 0 < p := (Nat.cast_nonneg n).trans_lt hnp
  have hp1 : 0 < 1 / p := one_div_pos.2 hp
  have hc0 : 0 < c := Real.rpow_pos_of_pos hR _
  have hκΛ : 0 ≤ κ * Λ := mul_nonneg (div_nonneg (sub_pos.2 hnp).le (by positivity)) hΛ.le
  -- Step 1: `Q_R < ∞`; otherwise `(c Q_R)^{1/p} = ∞^{1/p} = ∞`, as `c > 0`.
  have hcQ : ENNReal.ofReal c * QR ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos hp1] at hLp
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hLp)
  have hQRfin : QR ≠ ⊤ := by
    intro h
    apply hcQ
    rw [h]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne'
  -- Step 2: the hypothesis in real numbers.
  have hreal : (c * QR.toReal) ^ (1 / p) ≤ κ * Λ := by
    rwa [← ENNReal.ofReal_toReal hQRfin, ← ENNReal.ofReal_mul hc0.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc0.le ENNReal.toReal_nonneg) hp1.le,
      ENNReal.ofReal_le_ofReal_iff hκΛ] at hLp
  -- Step 3: factoring, `(R^{p−n})^{1/p} = R^{1 − n/p}`.
  have hfac : (c * QR.toReal) ^ (1 / p) = R ^ (1 - n / p) * QR.toReal ^ (1 / p) := by
    rw [Real.mul_rpow hc0.le ENNReal.toReal_nonneg, hc, ← Real.rpow_mul hR.le]
    congr 2
    field_simp
  -- Step 4: dividing by `R^{1 − n/p} > 0`.
  have hRpos : 0 < R ^ (1 - n / p) := Real.rpow_pos_of_pos hR _
  have hN : QR.toReal ^ (1 / p) ≤ κ * Λ * R ^ ((n : ℝ) / p - 1) := by
    have hinv : R ^ ((n : ℝ) / p - 1) = (R ^ (1 - n / p))⁻¹ := by
      rw [← Real.rpow_neg hR.le, neg_sub]
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hRpos, mul_comm, ← hfac]
    exact hreal
  -- Step 5: the sub-ball, `Q_t ≤ Q_R`.
  have hQle : Qt ≤ QR := lintegral_mono_set (closedBall_subset_closedBall htR)
  refine ⟨hQle.trans_lt (lt_top_iff_ne_top.2 hQRfin), ?_⟩
  calc Qt.toReal ^ (1 / p) ≤ QR.toReal ^ (1 / p) :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_mono hQRfin hQle) hp1.le
    _ ≤ κ * Λ * R ^ ((n : ℝ) / p - 1) := hN
/-- **Simon Ch. 4, between 4.2 and 4.3** (the Hölder absorption in the monotonicity estimate).  Let
`1 ≤ n < p`, `R > 0`, `t > 0`, `I ≥ 0`, `N ≥ 0` and `0 < ε ≤ 1`, and write `κ = (p − n)/(4p)`.  If
`N ≤ κ Λ R^{n/p − 1}` and `|E| ≤ (1 + ε) t N I^{1 − 1/p}`, then
`|E / tⁿ⁺¹ / (1 + I/tⁿ)| ≤ 2 κ Λ R⁻¹ (t/R)^{−n/p}`.
Proof: with `A = I/tⁿ`, `I^{1 − 1/p} = A^{1 − 1/p} t^{n − n/p}` and `A^{1 − 1/p} ≤ 1 + A` (split at
`A = 1`, using `0 ≤ 1 − 1/p ≤ 1`).  With `1 + ε ≤ 2` this gives `|E| ≤ 2 N t^{−n/p} tⁿ⁺¹ (1 + A)`;
then insert the bound on `N` and use `R^{n/p − 1} t^{−n/p} = R⁻¹ (t/R)^{−n/p}`. -/
theorem allard52_am_fc_a_bound : ∀ (n : ℕ), 1 ≤ n → ∀ (p R Λ ε t I E N : ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → 0 < t → 0 ≤ I → 0 ≤ N → N ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1) → |E| ≤ (1 + ε) * t * N * I ^ (1 - 1 / p) → |E / t ^ (n + 1) / (1 + I / t ^ n)| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
  intro n hn p R Λ ε t I E N hnp hR hΛ hε hε1 ht hI hN hNb hE
  -- Step 0: `p > 1`, so `γ = 1 - 1/p` satisfies `0 ≤ γ ≤ 1`; and `tⁿ > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    linarith
  have hγ1 : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := by positivity
    linarith
  have htn : 0 < t ^ n := pow_pos ht n
  -- Step 1: with `A = I/tⁿ ≥ 0`, `I^γ = A^γ (tⁿ)^γ = A^γ t^(n - n/p)`.
  set A := I / t ^ n with hA
  have hA0 : 0 ≤ A := div_nonneg hI htn.le
  have hIγ : I ^ (1 - 1 / p) = A ^ (1 - 1 / p) * t ^ ((n : ℝ) - n / p) := by
    have hIA : I = A * t ^ n := by rw [hA, div_mul_cancel₀ _ htn.ne']
    rw [hIA, Real.mul_rpow hA0 htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  -- Step 2: absorption `A^γ ≤ 1 + A`, splitting into `A ≤ 1` and `A ≥ 1`.
  have habs : A ^ (1 - 1 / p) ≤ 1 + A := by
    rcases le_total A 1 with h | h
    · calc A ^ (1 - 1 / p) ≤ 1 := Real.rpow_le_one hA0 h hγ0
        _ ≤ 1 + A := by linarith
    · calc A ^ (1 - 1 / p) ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hγ1
        _ = A := Real.rpow_one A
        _ ≤ 1 + A := by linarith
  -- Step 3: `t t^(n - n/p) = t^(-n/p) tⁿ⁺¹`; with `1 + ε ≤ 2`,
  -- `|E| ≤ 2 N t^(-n/p) (tⁿ⁺¹ (1 + A))`, so `|E/tⁿ⁺¹/(1 + A)| ≤ 2 N t^(-n/p)`.
  have hpow : t * t ^ ((n : ℝ) - n / p) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
    rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht, mul_comm t,
      ← Real.rpow_add_one ht.ne']
    congr 1
    push_cast
    ring
  have hE2 : |E| ≤ 2 * N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + A)) :=
    calc |E| ≤ (1 + ε) * t * N * I ^ (1 - 1 / p) := hE
      _ = (1 + ε) * (N * (t * t ^ ((n : ℝ) - n / p))) * A ^ (1 - 1 / p) := by
          rw [hIγ]
          ring
      _ ≤ 2 * (N * (t * t ^ ((n : ℝ) - n / p))) * (1 + A) := by
          gcongr
          linarith
      _ = 2 * N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + A)) := by
          rw [hpow]
          ring
  have hden : 0 < t ^ (n + 1) * (1 + A) := by positivity
  -- Steps 4–5: insert `N ≤ κ Λ R^(n/p - 1)` and rewrite
  -- `R^(n/p - 1) t^(-n/p) = R^(n/p) t^(-n/p) / R = R⁻¹ (t/R)^(-n/p)`.
  calc |E / t ^ (n + 1) / (1 + A)| = |E| / (t ^ (n + 1) * (1 + A)) := by
        rw [div_div, abs_div, abs_of_pos hden]
    _ ≤ 2 * N * t ^ (-((n : ℝ) / p)) := by
        rw [div_le_iff₀ hden]
        exact hE2
    _ ≤ 2 * ((p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1)) * t ^ (-((n : ℝ) / p)) := by
        gcongr
    _ = 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
        rw [Real.div_rpow ht.le hR.le, Real.rpow_sub_one hR.ne', Real.rpow_neg hR.le,
          div_inv_eq_mul]
        ring
/-- **Simon Ch. 4, after 4.4** (the primitive of the mean-curvature coefficient).  Let `p > n`,
`R, Λ, ε > 0`, `κ = (p − n)/(4p)`, and let `a` be continuous with
`|a(τ)| ≤ 2κΛR⁻¹ (τ/R)^{−n/p}` at every `τ > 0` with `(1 + ε)τ < R`.  Then for each such `t` the
primitive `G(u) = ∫₀ᵘ a` is continuous at `t` and `|G(t)| ≤ Λ/2`.
Proof: as `−n/p > −1`, the bound is integrable near `0`, so `a` is interval integrable on `[0, t]`
and the fundamental theorem of calculus applies at `t`; and
`|G(t)| ≤ ∫₀ᵗ 2κΛR⁻¹ (τ/R)^{−n/p} dτ = (2κ/(1 − n/p)) Λ (t/R)^{1−n/p} = (Λ/2) (t/R)^{1−n/p} ≤ Λ/2`,
since `t ≤ R`. -/
theorem allard52_am_fc_primitive : ∀ (n : ℕ) (p R Λ ε : ℝ) (a : ℝ → ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < ε → (∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧ |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))) → ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt (fun u => ∫ τ in (0)..u, a τ) t ∧ |∫ τ in (0)..t, a τ| ≤ Λ / 2 := by
  intro n p R Λ ε a hnp hR hΛ hε ha t ht htR
  -- Notation: `β = n/p ∈ [0, 1)`, `c = 2κΛ/R`, and the bound `g(τ) = c (τ/R)^{−β}`.
  set β : ℝ := (n : ℝ) / p with hβ
  set c : ℝ := 2 * ((p - n) / (4 * p)) * Λ / R with hc
  have hp : 0 < p := (Nat.cast_nonneg n).trans_lt hnp
  have hβ1 : β < 1 := (div_lt_one hp).2 hnp
  -- Step 0: `t ≤ R`, and `a` is continuous on the open set `U = {τ | 0 < τ ∧ (1 + ε)τ < R}`,
  -- which contains `(0, t]`.
  have htR' : t ≤ R := by nlinarith
  set U : Set ℝ := {τ | 0 < τ ∧ (1 + ε) * τ < R}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const)
  have haU : ContinuousOn a U := fun τ hτ => (ha τ hτ.1 hτ.2).1.continuousWithinAt
  have hIoc : Ioc 0 t ⊆ U := fun τ hτ =>
    ⟨hτ.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hτ.2 (by linarith)) htR⟩
  -- Step 1: `g` is interval integrable on `[0, t]`, since `−β > −1` (rescale `τ ↦ τ/R`).
  have hg0 : IntervalIntegrable (fun τ => (τ / R) ^ (-β)) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t / R)
      (r := -β) (by linarith)).comp_mul_right (c := R⁻¹)
    simpa [div_eq_mul_inv, hR.ne'] using h
  have hg : IntervalIntegrable (fun τ => c * (τ / R) ^ (-β)) volume 0 t := hg0.const_mul c
  -- Step 2: `|a| ≤ g` on `(0, t]`.
  have hle : ∀ τ ∈ Ioc 0 t, ‖a τ‖ ≤ c * (τ / R) ^ (-β) := fun τ hτ => by
    rw [Real.norm_eq_abs]
    exact (ha τ (hIoc hτ).1 (hIoc hτ).2).2
  -- Step 3: by domination, `a` is interval integrable on `[0, t]`.
  have haI : IntervalIntegrable a volume 0 t := by
    refine hg.mono_fun' ?_ ?_
    · rw [uIoc_of_le ht.le]
      exact (haU.mono hIoc).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.le]
      exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hle)
  refine ⟨?_, ?_⟩
  -- Step 4: FTC at `t`, where `a` is continuous and strongly measurable near `t`.
  · exact (intervalIntegral.integral_hasDerivAt_right haI
      (haU.stronglyMeasurableAtFilter hUo t ⟨ht, htR⟩) (ha t ht htR).1).continuousAt
  -- Step 5: `|G(t)| ≤ ∫₀ᵗ g = c R (t/R)^{1−β}/(1 − β) = (Λ/2)(t/R)^{1−β} ≤ Λ/2`.
  · have h1 : |∫ τ in (0)..t, a τ| ≤ ∫ τ in (0)..t, c * (τ / R) ^ (-β) := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_of_norm_le ht.le (Eventually.of_forall hle) hg
    have h2 : ∫ τ in (0)..t, c * (τ / R) ^ (-β) =
        c * (R * ((t / R) ^ (-β + 1) / (-β + 1))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_div (fun x => x ^ (-β)) hR.ne',
        integral_rpow (Or.inl (by linarith)), zero_div, Real.zero_rpow (by linarith), sub_zero,
        smul_eq_mul]
    -- `2κ/(1 − β) = 1/2`.
    have h3 : c * (R * ((t / R) ^ (-β + 1) / (-β + 1))) = Λ / 2 * (t / R) ^ (-β + 1) := by
      have hβ' : -β + 1 = (p - n) / p := by rw [hβ]; field_simp; ring
      have hpn : p - n ≠ 0 := (sub_pos.2 hnp).ne'
      generalize (t / R) ^ (-β + 1) = X
      rw [hβ', hc]
      field_simp
      ring
    have hX : (t / R) ^ (-β + 1) ≤ 1 :=
      Real.rpow_le_one (div_nonneg ht.le hR.le) ((div_le_one hR).2 htR') (by linarith)
    calc |∫ τ in (0)..t, a τ| ≤ ∫ τ in (0)..t, c * (τ / R) ^ (-β) := h1
      _ = Λ / 2 * (t / R) ^ (-β + 1) := by rw [h2, h3]
      _ ≤ Λ / 2 * 1 := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = Λ / 2 := mul_one _
/-- **Simon Ch. 4, 4.1** (cf. 3.14–3.16; the radial split of the first-variation integrand for one
cutoff, as used in 4.1–4.5).
Let `μ(B_R(y)) < ∞`, let `w` be a.e. strongly measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e.
there, and let `φ` be a nonincreasing `C¹` function with `φ = 1` on `(-∞, 1]` and `φ = 0` on
`[1 + ε, ∞)`.  For `t > 0` with `(1 + ε) t < R`, writing `r = |x − y|`:
`∫ (n φ(r/t) + (r/t) φ'(r/t) (1 − w)) dμ`
`= n ∫ φ(r/t) dμ + ∫ (r/t) φ'(r/t) dμ − ∫ (r/t) φ'(r/t) w dμ`,
`∫ φ(r/t) dμ ≥ 0` and `∫ (r/t) φ'(r/t) w dμ ≤ 0`.
Proof: as in `allard52_am_fc_cutoff_facts` (derived directly here), `0 ≤ φ ≤ 1`, `φ' ≤ 0`,
`φ' = 0` on `(1 + ε, ∞)`, and `φ'` is continuous and bounded.  The three integrands vanish off
`B = B_{(1+ε)t}(y) ⊆ B̆_R(y)`, which has finite measure, and are bounded and a.e. strongly
measurable on `B`, hence integrable; linearity gives the split, `φ ≥ 0` the second claim, and
`(r/t) φ'(r/t) w ≤ 0` `μ`-a.e. the third. -/
theorem allard52_am_fc_radial_split : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R ε : ℝ) (φ : ℝ → ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ = (n : ℝ) * ∫ x, φ (‖x - y‖ / t) ∂μ + ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ - ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ∧ 0 ≤ ∫ x, φ (‖x - y‖ / t) ∂μ ∧ ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ≤ 0 := by
  intro n ℓ μ w y R ε φ hε hμR hw hw01 hφC hφA hφ1 hφ0 t ht htR
  -- Step 1: `0 ≤ φ ≤ 1`, `φ' ≤ 0`, `φ' = 0` on `(1 + ε, ∞)`, `φ'` continuous and `|φ'| ≤ C`
  -- (the facts of `allard52_am_fc_cutoff_facts`, derived directly).
  -- `0 ≤ φ ≤ 1` by monotonicity and the boundary values `φ (1 + ε) = 0`, `φ 1 = 1`.
  have hφ01 : ∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1 := by
    intro u
    constructor
    · rcases le_total (1 + ε) u with hu | hu
      · rw [hφ0 u hu]
      · rw [← hφ0 (1 + ε) le_rfl]
        exact hφA hu
    · rcases le_total u 1 with hu | hu
      · rw [hφ1 u hu]
      · rw [← hφ1 1 le_rfl]
        exact hφA hu
  -- `φ' ≤ 0` because `φ` is nonincreasing.
  have hdφ : ∀ u : ℝ, deriv φ u ≤ 0 := fun u => hφA.deriv_nonpos
  -- `φ' = 0` on `(1 + ε, ∞)` and on `(-∞, 1)`, where `φ` is locally constant.
  have hdφ0 : ∀ u : ℝ, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) (fun v hv => hφ0 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  have hdφ1 : ∀ u : ℝ, u < 1 → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu) (fun v hv => hφ1 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  -- `φ'` is continuous because `φ` is `C¹`; its support lies in `[1, 1 + ε]`, so it is bounded.
  have hdφc : Continuous (deriv φ) := hφC.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, |deriv φ u| ≤ C := by
    have hsupp : HasCompactSupport (deriv φ) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a := 1) (b := 1 + ε)) ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact ⟨not_lt.mp fun h => hu (hdφ1 u h), not_lt.mp fun h => hu (hdφ0 u h)⟩
    obtain ⟨C, hC⟩ := hdφc.bounded_above_of_compact_support hsupp
    exact ⟨C, fun u => by rw [← Real.norm_eq_abs]; exact hC u⟩
  -- Step 2: `B = B_{(1+ε)t}(y)` lies in `B̆_R(y)`, so `μ(B) < ∞`; `r/t ≤ 1 + ε` on `B` and
  -- `r/t > 1 + ε` off `B`.
  have hBm : MeasurableSet (closedBall y ((1 + ε) * t)) := measurableSet_closedBall
  have hBR : closedBall y ((1 + ε) * t) ⊆ ball y R := closedBall_subset_ball htR
  have hμB : μ (closedBall y ((1 + ε) * t)) < ⊤ :=
    (measure_mono (hBR.trans ball_subset_closedBall)).trans_lt hμR
  have hr0 : ∀ x : Amb n ℓ, 0 ≤ ‖x - y‖ / t := fun x => div_nonneg (norm_nonneg _) ht.le
  have hin : ∀ x ∈ closedBall y ((1 + ε) * t), ‖x - y‖ / t ≤ 1 + ε := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact (div_le_iff₀ ht).2 hx
  have hout : ∀ x, x ∉ closedBall y ((1 + ε) * t) → 1 + ε < ‖x - y‖ / t := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact (lt_div_iff₀ ht).2 hx
  -- Step 3: `φ(r/t)` and `(r/t) φ'(r/t)` are continuous; all three integrands vanish off `B`.
  have hrc : Continuous fun x : Amb n ℓ => ‖x - y‖ / t :=
    (continuous_id.sub continuous_const).norm.div_const t
  have hf1c : Continuous fun x : Amb n ℓ => φ (‖x - y‖ / t) := hφC.continuous.comp hrc
  have hf2c : Continuous fun x : Amb n ℓ => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) :=
    hrc.mul (hdφc.comp hrc)
  have hf1B : ∀ x, x ∉ closedBall y ((1 + ε) * t) → φ (‖x - y‖ / t) = 0 :=
    fun x hx => hφ0 _ (hout x hx).le
  have hf2B : ∀ x, x ∉ closedBall y ((1 + ε) * t) →
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) = 0 :=
    fun x hx => by rw [hdφ0 _ (hout x hx), mul_zero]
  have hf3B : ∀ x, x ∉ closedBall y ((1 + ε) * t) →
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x = 0 :=
    fun x hx => by rw [hf2B x hx, zero_mul]
  -- Step 4 (i): `|φ(r/t)| ≤ 1`, so `φ(r/t)` is integrable on `B`, hence on the whole space.
  have hi1 : Integrable (fun x => φ (‖x - y‖ / t)) μ := by
    refine (Measure.integrableOn_of_bounded (M := 1) hμB.ne hf1c.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)).integrable_of_forall_notMem_eq_zero hf1B
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 _).1]
    exact (hφ01 _).2
  -- Step 4 (ii): `|(r/t) φ'(r/t)| ≤ (1 + ε) C` on `B`.
  have hi2 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ := by
    refine (Measure.integrableOn_of_bounded (M := (1 + ε) * C) hμB.ne
      hf2c.aestronglyMeasurable ?_).integrable_of_forall_notMem_eq_zero hf2B
    filter_upwards [ae_restrict_mem hBm] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 x)]
    exact mul_le_mul (hin x hx) (hC _) (abs_nonneg _) (by linarith)
  -- Step 4 (iii): `w` is a.e. strongly measurable on `B ⊆ B̆_R(y)`, and `0 ≤ w ≤ 1` `μ`-a.e. on `B`
  -- gives `|(r/t) φ'(r/t) w| ≤ |(r/t) φ'(r/t)|` there.
  have hi3 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) μ := by
    have hwB : AEStronglyMeasurable w (μ.restrict (closedBall y ((1 + ε) * t))) :=
      hw.mono_set hBR
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hf3B
    refine Integrable.mono' hi2.integrableOn.norm (hf2c.aestronglyMeasurable.fun_mul hwB) ?_
    filter_upwards [ae_restrict_mem hBm, ae_restrict_of_ae hw01] with x hxB hx
    obtain ⟨h0, h1⟩ := hx (hBR hxB)
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  -- Step 6 (`∫ φ(r/t) dμ ≥ 0` since `φ ≥ 0`) is the middle component.
  refine ⟨?_, integral_nonneg fun x => (hφ01 _).1, integral_nonpos_of_ae ?_⟩
  -- Step 5: the splitting identity, by linearity of the integral.
  · have hi12 : Integrable (fun x => (n : ℝ) * φ (‖x - y‖ / t) +
        ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ := (hi1.const_mul _).add hi2
    calc ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ
        = ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) -
            ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) ∂μ := by
          congr 1
          funext x
          ring
      _ = (n : ℝ) * ∫ x, φ (‖x - y‖ / t) ∂μ + ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ -
            ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ := by
          rw [integral_sub hi12 hi3, integral_add (hi1.const_mul _) hi2, integral_const_mul]
  -- Step 7: `(r/t) φ'(r/t) w ≤ 0` `μ`-a.e.: on `B̆_R(y)` since `r/t ≥ 0`, `φ' ≤ 0` and `w ≥ 0`;
  -- off `B̆_R(y)` the point is off `B`, where the integrand vanishes.
  · filter_upwards [hw01] with x hx
    by_cases hxR : x ∈ ball y R
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (hr0 x) (hdφ _)) (hx hxR).1
    · exact (hf3B x fun hxB => hxR (hBR hxB)).le
/-- **Simon Ch. 4, 4.2–4.3** (the Hölder step for the mean-curvature term).  Let `p > 1`, let `μ`
be a measure on `ℝ^{n+ℓ}` with `μ(B_t(y)) < ∞`, let `H` be `μ`-integrable on `B_t(y)` with
`∫_{B_t(y)} |H|ᵖ dμ < ∞`, and let `ψ` be a.e. strongly measurable with `0 ≤ ψ ≤ 1` and `ψ = 0` off
`B_t(y)`.  Then `|∫ ψ(x) (x − y) · H(x) dμ| ≤ t (∫_{B_t(y)} |H|ᵖ dμ)^{1/p} (∫ ψ dμ)^{1 − 1/p}`.
Proof: on `B_t(y)`, `|ψ(x) (x − y) · H(x)| ≤ t ψ(x) |H(x)|` by Cauchy–Schwarz, and the pairing
vanishes off `B_t(y)`; Hölder on `B_t(y)` with `q = p/(p − 1)` and `ψ^q ≤ ψ` bound
`∫_{B_t(y)} ψ |H| dμ`.  The estimate is carried out in `[0, ∞]`, where every factor on the right is
finite, and then converted to real numbers. -/
theorem aal_curvature_pairing_holder_bound : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  intro n ℓ p hp μ H ψ y t ht hμB hHint hHp hψm hψ01 hψt
  -- Notation: `B = B_t(y)` and the conjugate exponent `q = p/(p - 1)`, with `1/q = 1 - 1/p`.
  set B : Set (Amb n ℓ) := closedBall y t
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp⟩
  have hq1 : 1 - 1 / p = 1 / q := by rw [one_div, one_div, hpq.one_sub_inv]
  -- Step 1: `ψ` vanishes off `B`; it is integrable because `0 ≤ ψ ≤ 1_B` and `μ(B) < ∞`.
  have hψB : ∀ x, x ∉ B → ψ x = 0 := by
    intro x hx
    apply hψt x
    simpa [B, mem_closedBall, dist_eq_norm] using hx
  have hψe : ∀ x, ‖ψ x‖ₑ = ENNReal.ofReal (ψ x) := fun x => Real.enorm_of_nonneg (hψ01 x).1
  have hψle : ∀ x, ‖ψ x‖ₑ ≤ 1 := fun x => (hψe x).trans_le (ENNReal.ofReal_le_one.2 (hψ01 x).2)
  have hψind : ∀ x, ‖ψ x‖ₑ ≤ B.indicator 1 x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact hψle x
    · rw [hψB x hx, enorm_zero]
      exact zero_le
  have hψlin : ∫⁻ x, ‖ψ x‖ₑ ∂μ < ∞ :=
    calc ∫⁻ x, ‖ψ x‖ₑ ∂μ ≤ ∫⁻ x, B.indicator 1 x ∂μ := lintegral_mono hψind
      _ = μ B := lintegral_indicator_one hBm
      _ < ∞ := hμB
  have hψint : Integrable ψ μ := ⟨hψm, hψlin⟩
  have hψI : ∫⁻ x, ‖ψ x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all _ fun x => (hψ01 x).1)]
    exact lintegral_congr hψe
  have hψnn : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
  -- Step 2: on `B`, `|ψ(x)(x - y)·H(x)| ≤ t ψ(x)|H(x)|` (Cauchy–Schwarz and `|x - y| ≤ t`);
  -- off `B` the pairing vanishes.
  have hpt : ∀ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ≤
      B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      have hxy : ‖x - y‖ ≤ t := by simpa [B, mem_closedBall, dist_eq_norm] using hx
      have hreal : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
        rw [norm_mul, Real.norm_of_nonneg (hψ01 x).1]
        calc ψ x * ‖inner ℝ (x - y) (H x)‖ ≤ ψ x * (‖x - y‖ * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hψ01 x).1
          _ ≤ ψ x * (t * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
                (hψ01 x).1
          _ = t * (‖H x‖ * ψ x) := by ring
      calc ‖ψ x * inner ℝ (x - y) (H x)‖ₑ = ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ :=
            (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, hψe]
    · rw [indicator_of_notMem hx, hψB x hx, zero_mul, enorm_zero]
  -- Step 3: Hölder on `(B, μ⌞B)` with exponents `p` and `q`.
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq
    hHint.aestronglyMeasurable.enorm hψm.restrict.enorm
  simp only [Pi.mul_apply] at hHolder
  -- Step 4: `ψ^q ≤ ψ` since `0 ≤ ψ ≤ 1` and `q ≥ 1`; so `∫_B ψ^q ≤ ∫ ψ`.
  have hψq : ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) :=
    calc ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ∫⁻ x in B, ‖ψ x‖ₑ ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one (hψle x) hpq.symm.lt.le
      _ ≤ ∫⁻ x, ‖ψ x‖ₑ ∂μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, ψ x ∂μ) := hψI
  -- The estimate in `[0, ∞]`.
  have key : ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ ≤ ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) :=
    calc ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ
        ≤ ∫⁻ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) ∂μ := lintegral_indicator hBm _
      _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ‖ψ x‖ₑ ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * (∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * ?_
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * (_ * ?_)
          exact ENNReal.rpow_le_rpow hψq hpq.symm.one_div_nonneg
  -- Step 5: back to real numbers; every factor on the right is finite.
  have hfin : ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hHp.ne)
        (ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top))
  have h := ENNReal.toReal_mono hfin key
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hψnn,
    Real.norm_eq_abs] at h
  rw [hq1, mul_assoc]
  exact h
/-- Continuity in the scale of a radial-profile integral (step 2(c) of the annular monotonicity
proof, parts (a) and (b) of `allard52_am_cutoff_integral_calculus`): if `f` is `μ`-integrable on
`B_S(y)`, `g` is continuous with `g = 0` on `(T, ∞)`, `T > 0`, `t > 0` and `T t < S`, then
`s ↦ ∫ g(‖x − y‖/s) f(x) dμ` is continuous at `t`.  For `0 < s < S/T` the integrand vanishes off
`B_S(y)`, so the integral is taken against `μ ⌞ B_S(y)`; there `|g| ≤ C` on `[0, ∞)` gives the
dominating function `C |f|`, and dominated convergence applies. -/
theorem allard52_am_cc_profile_integral_continuousAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (g : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → Continuous g → 0 < T → (∀ u : ℝ, T < u → g u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, g (‖x - y‖ / s) * f x ∂μ) t := by
  intro n ℓ μ y f g S T t hf hg hT hg0 ht htS
  have hfν : Integrable f (μ.restrict (closedBall y S)) := hf
  -- Step 1: `t < S/T`, so `(0, S/T)` is a neighbourhood of `t`.
  have htR : t < S / T := by
    rw [lt_div_iff₀ hT]
    linarith
  -- Step 2: for `s ∈ (0, S/T)` and `x ∉ B_S(y)`, `‖x − y‖/s > T`, so the integrand vanishes
  -- off `B_S(y)` and the `μ`-integral is the `μ ⌞ B_S(y)`-integral.
  have hconv : ∀ s ∈ Ioo 0 (S / T),
      ∫ x, g (‖x - y‖ / s) * f x ∂(μ.restrict (closedBall y S)) =
        ∫ x, g (‖x - y‖ / s) * f x ∂μ := by
    rintro s ⟨hs, hsR⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hT] at hsR
    have h1 : T < ‖x - y‖ / s := by
      rw [lt_div_iff₀ hs]
      nlinarith
    rw [hg0 _ h1, zero_mul]
  -- Step 3: `|g u| ≤ C` for `u ≥ 0`, with `C` a bound for `|g|` on `[0, T]`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hg.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hg0 u h, abs_zero]
      exact le_max_right _ _
  -- Steps 4-6: dominated convergence for `μ ⌞ B_S(y)` at `t`, with bound `C ‖f‖`.
  have hmain : ContinuousAt (fun s =>
      ∫ x, g (‖x - y‖ / s) * f x ∂(μ.restrict (closedBall y S))) t := by
    refine continuousAt_of_dominated (bound := fun x => C * ‖f x‖) ?_ ?_
      (hfν.norm.const_mul C) ?_
    · -- Step 4: `x ↦ g(‖x − y‖/s)` is continuous and `f` is a.e. strongly measurable.
      refine Eventually.of_forall fun s => ?_
      exact (hg.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / s)
        ).aestronglyMeasurable.mul hfν.aestronglyMeasurable
    · -- Step 3: for `s > 0`, `‖x − y‖/s ≥ 0`, so `|g(‖x − y‖/s) f(x)| ≤ C ‖f(x)‖`.
      filter_upwards [lt_mem_nhds ht] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC _ (div_nonneg (norm_nonneg _) hs.le)) (norm_nonneg _)
    · -- Step 5: `s ↦ g(‖x − y‖/s) f(x)` is continuous at `t ≠ 0`.
      refine Eventually.of_forall fun x => ?_
      exact (hg.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')).mul
        continuousAt_const
  -- Step 7: both functions agree on the neighbourhood `(0, S/T)` of `t`.
  exact hmain.congr (Filter.eventually_of_mem (Ioo_mem_nhds ht htR) hconv)

/-- Differentiation in the scale of a radial cutoff integral (step 2(c) of the annular
monotonicity proof, part (c) of `allard52_am_cutoff_integral_calculus`): if `f` is
`μ`-integrable on `B_S(y)`, `φ` is `C¹` with `φ = 0` on `[T, ∞)`, `T > 0`, `t > 0` and `T t < S`,
then `s ↦ ∫ φ(‖x − y‖/s) f(x) dμ` has derivative `-(∫ (‖x − y‖/t) φ'(‖x − y‖/t) f(x) dμ)/t` at `t`.
For `0 < s < S/T` the integrands vanish off `B_S(y)`; on `(t/2, S/T)` the `s`-derivatives are
bounded by `(2 C₁/t) |f|` with `C₁ = max_{[0,T]} |u φ'(u)|`, and one differentiates under the
integral sign against `μ ⌞ B_S(y)`. -/
theorem allard52_am_cc_cutoff_integral_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t := by
  intro n ℓ μ y f φ S T t hf hφ hT hφ0 ht htS
  set K : Set (Amb n ℓ) := closedBall y S with hK
  set ν : Measure (Amb n ℓ) := μ.restrict K with hν
  have hfν : Integrable f ν := hf
  have hφc : Continuous φ := hφ.continuous
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
  -- Step 2: `φ' = 0` on `(T, ∞)`.
  have hdzero : ∀ u, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφ0 v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  -- Step 3: `|φ u| ≤ C₀` and `|u φ'(u)| ≤ C₁` for `u ≥ 0`.
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hφc.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hφ0 u h.le, abs_zero]
      exact le_max_right _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → |u * deriv φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuous_id.mul hdφc).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hdzero u h, mul_zero, abs_zero]
      exact le_max_right _ _
  -- Step 5: `d/ds φ(r/s) = -(r/s) φ'(r/s) / s` for `s ≠ 0`.
  have hderiv : ∀ (r s : ℝ), s ≠ 0 →
      HasDerivAt (fun u => φ (r / u)) (-(r / s * deriv φ (r / s)) / s) s := by
    intro r s hs
    have h1 : HasDerivAt (fun u : ℝ => r / u) (r * -(s ^ 2)⁻¹) s := by
      have := (hasDerivAt_inv hs).const_mul r
      convert this using 1
      funext u
      exact div_eq_mul_inv r u
    have h2 := ((hφ.differentiable (by simp) (r / s)).hasDerivAt).comp s h1
    have heq : -(r / s * deriv φ (r / s)) / s = deriv φ (r / s) * (r * -(s ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  -- Step 1: `t < R := S / T`; we work on the neighbourhood `(t/2, R)` of `t`.
  set R : ℝ := S / T with hR
  have hRiff : ∀ s : ℝ, s < R ↔ T * s < S := fun s => by
    rw [hR, lt_div_iff₀ hT, mul_comm]
  have htR : t < R := (hRiff t).2 htS
  -- Step 2: for `0 < s < R` the integrands vanish off `K = B_S(y)`.
  have hout : ∀ s, 0 < s → s < R → ∀ x, x ∉ K → T < ‖x - y‖ / s := by
    intro s hs hsR x hx
    have hxS : S < ‖x - y‖ := by
      simpa [hK, mem_closedBall, dist_eq_norm, not_le] using hx
    rw [lt_div_iff₀ hs]
    linarith [(hRiff s).1 hsR]
  have hconv : ∀ s, 0 < s → s < R →
      ∫ x, φ (‖x - y‖ / s) * f x ∂μ = ∫ x, φ (‖x - y‖ / s) * f x ∂ν := by
    intro s hs hsR
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hφ0 _ (hout s hs hsR x hx).le, zero_mul]
  have hconv' : ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ =
      ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂ν := by
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hdzero _ (hout t ht htR x hx), mul_zero, zero_mul]
  -- Step 4: measurability, and integrability of the integrand at `t`, for `ν`.
  have hmeas : ∀ s, AEStronglyMeasurable (fun x => φ (‖x - y‖ / s) * f x) ν := fun s =>
    (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / s)).aestronglyMeasurable.mul
      hfν.aestronglyMeasurable
  have hint : Integrable (fun x => φ (‖x - y‖ / t) * f x) ν := by
    refine Integrable.mono' (hfν.norm.const_mul C₀) (hmeas t) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC₀ _ (div_nonneg (norm_nonneg _) ht.le)) (norm_nonneg _)
  -- Step 6: differentiation under the integral sign for `ν` on `(t/2, R)`, bound `(2C₁/t)‖f‖`.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s x => φ (‖x - y‖ / s) * f x)
    (F' := fun s x => -(‖x - y‖ / s * deriv φ (‖x - y‖ / s)) / s * f x)
    (x₀ := t) (bound := fun x => 2 * C₁ / t * ‖f x‖) (s := Ioo (t / 2) R)
    (Ioo_mem_nhds (half_lt_self ht) htR) (Eventually.of_forall hmeas) hint ?_ ?_
    (hfν.norm.const_mul _) ?_
  -- Step 7: evaluate the derivative and transfer from `ν` back to `μ` near `t`.
  · have hderivν := key.2
    have heq : (∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t * f x ∂ν) =
        -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t := by
      rw [hconv', ← integral_neg, ← integral_div]
      congr 1
      funext x
      ring
    rw [heq] at hderivν
    refine hderivν.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht htR] with s hs
    exact hconv s hs.1 hs.2
  · exact (by fun_prop : Continuous fun x : Amb n ℓ =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t).aestronglyMeasurable.mul hfν.aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs0]
    have h1 : |‖x - y‖ / s * deriv φ (‖x - y‖ / s)| / s ≤ 2 * C₁ / t := by
      rw [div_le_div_iff₀ hs0 ht]
      have := hC₁ _ (div_nonneg (norm_nonneg (x - y)) hs0.le)
      nlinarith [hs.1]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    exact (hderiv ‖x - y‖ s hs0.ne').mul_const (f x)

/-- **Simon Ch. 4, 3.3–3.4 and 4.1** (step 2(c) of the annular monotonicity argument: calculus in
the scale of radial cutoff integrals, where `s ∂ₛ φ(r/s) = -(r/s) φ'(r/s)`).  Let `f` be
`μ`-integrable on `B_S(y)`, let `φ` be `C¹` with `φ = 0` on `[T, ∞)`, `T > 0`, and let `t > 0`
with `T t < S`; write `r = ‖x − y‖`.  Then
(a) `s ↦ ∫ φ(r/s) f dμ` and (b) `s ↦ ∫ (r/s) φ'(r/s) f dμ` are continuous at `t`, and
(c) `s ↦ ∫ φ(r/s) f dμ` has derivative `-(∫ (r/t) φ'(r/t) f dμ)/t` at `t`.
(a) and (b) are `allard52_am_cc_profile_integral_continuousAt` for the continuous profiles
`g = φ` and `g(u) = u φ'(u)`, both zero on `(T, ∞)` (`φ'` vanishes there because `φ` vanishes on
that open set); (c) is `allard52_am_cc_cutoff_integral_hasDerivAt`. -/
theorem allard52_am_cutoff_integral_calculus : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) t ∧ ContinuousAt (fun s => ∫ x, ‖x - y‖ / s * deriv φ (‖x - y‖ / s) * f x ∂μ) t ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t := by
  intro n ℓ μ y f φ S T t hf hφ hT hφT ht hTt
  -- `φ' = 0` on `(T, ∞)`: near each `u > T`, `φ` agrees with the zero function.
  have hdφT : ∀ u : ℝ, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφT v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  refine ⟨?_, ?_, ?_⟩
  -- (a): the profile `g = φ`, continuous as `φ` is `C¹`, and zero on `(T, ∞) ⊆ [T, ∞)`.
  · exact Submission.allard52_am_cc_profile_integral_continuousAt n ℓ μ y f φ S T t hf
      hφ.continuous hT (fun u hu => hφT u hu.le) ht hTt
  -- (b): the profile `g(u) = u φ'(u)`, continuous as `φ'` is; `g(r/s) f` is the integrand.
  · exact Submission.allard52_am_cc_profile_integral_continuousAt n ℓ μ y f
      (fun u => u * deriv φ u) S T t hf (continuous_id.mul hφ.continuous_deriv_one) hT
      (fun u hu => (congrArg (u * ·) (hdφT u hu)).trans (mul_zero u)) ht hTt
  -- (c): differentiation in the scale under the integral sign.
  · exact Submission.allard52_am_cc_cutoff_integral_hasDerivAt n ℓ μ y f φ S T t hf hφ hT hφT
      ht hTt
/-- **Simon Ch. 4, 4.3–4.4** (the integrating factor for the radial first-variation identity).
Let `β < 1` and suppose that on `(0, R)`: `I` is differentiable with `I ≥ 0`, `E` and `Q` are
continuous, `n I − t I' + t Q = −E`, and `|a(t)| ≤ M t^{−β}`, where `a = E/t^{n+1}/(1 + I/tⁿ)`.
Then for `0 < s ≤ r < R`, with `G(t) = ∫₀ᵗ a`,
`e^{−G(r)} (1 + I(r)/rⁿ) − e^{−G(s)} (1 + I(s)/sⁿ) = ∫ₛʳ e^{−G(t)} Q(t)/tⁿ dt`.
Proof: `a` is continuous on `(0, R)` (since `1 + I/tⁿ ≥ 1`) and dominated by `M τ^{−β}`, which is
integrable at `0`, so `G' = a` on `(0, R)`.  The hypothesis gives
`(1 + I/tⁿ)' = (t I' − n I)/t^{n+1} = Q/tⁿ + a (1 + I/tⁿ)`, hence
`(e^{−G} (1 + I/tⁿ))' = e^{−G} Q/tⁿ`, and the fundamental theorem of calculus on `[s, r]`
concludes. -/
theorem allard52_am_integrating_factor : ∀ (n : ℕ) (I I' E Q a : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t ∈ Ioo 0 R, HasDerivAt I (I' t) t) → (∀ t ∈ Ioo 0 R, ContinuousAt E t) → (∀ t ∈ Ioo 0 R, ContinuousAt Q t) → (∀ t ∈ Ioo 0 R, 0 ≤ I t) → (∀ t ∈ Ioo 0 R, (n : ℝ) * I t - t * I' t + t * Q t = -E t) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t ∈ Ioo 0 R, |a t| ≤ M * t ^ (-β)) → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) = ∫ t in s..r, Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n) := by
  intro n I I' E Q a R M β hβ hI hE hQ hI0 hid ha hab s r hs hsr hrR
  -- Notation: `Ψ(t) = 1 + I(t)/tⁿ`; on `(0, R)` we have `Ψ ≥ 1 > 0`.
  have hΨpos : ∀ t ∈ Ioo 0 R, 0 < 1 + I t / t ^ n := by
    intro t ht
    have : 0 ≤ I t / t ^ n := div_nonneg (hI0 t ht) (pow_nonneg ht.1.le n)
    linarith
  -- Step 1: `a` is continuous on `(0, R)`.
  have hac : ∀ t ∈ Ioo 0 R, ContinuousAt a t := by
    intro t ht
    have ha' : a = fun t => E t / t ^ (n + 1) / (1 + I t / t ^ n) := funext ha
    rw [ha']
    exact ((hE t ht).div (continuous_pow (n + 1)).continuousAt (pow_ne_zero _ ht.1.ne')).div
      (continuousAt_const.add ((hI t ht).continuousAt.div (continuous_pow n).continuousAt
        (pow_ne_zero _ ht.1.ne'))) (hΨpos t ht).ne'
  have hacon : ContinuousOn a (Ioo 0 R) := fun t ht => (hac t ht).continuousWithinAt
  -- Step 2: `a` is integrable on `[0, t]` for `t ∈ (0, R)`: `|a(τ)| ≤ M τ^{−β}` and `−β > −1`.
  have haint : ∀ t ∈ Ioo 0 R, IntervalIntegrable a volume 0 t := by
    intro t ht
    have hsub : Ioc 0 t ⊆ Ioo 0 R := fun x hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
    refine ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -β)).const_mul
      M).mono_fun' ?_ ?_
    · rw [uIoc_of_le ht.1.le]
      exact (hacon.mono hsub).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.1.le]
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
      simpa only [Real.norm_eq_abs] using hab x (hsub hx)
  -- Step 3: `G(t) = ∫₀ᵗ a` has `G' = a` on `(0, R)`.
  have hG : ∀ t ∈ Ioo 0 R, HasDerivAt (fun u => ∫ τ in (0)..u, a τ) (a t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (haint t ht)
      (hacon.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hac t ht)
  -- Steps 4–5: `Ψ' = (t I' − n I)/t^{n+1} = Q/tⁿ + E/t^{n+1} = Q/tⁿ + a Ψ` on `(0, R)`.
  have hΨ : ∀ t ∈ Ioo 0 R,
      HasDerivAt (fun u => 1 + I u / u ^ n) (Q t / t ^ n + a t * (1 + I t / t ^ n)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have htn : t ^ n ≠ 0 := pow_ne_zero n ht0
    refine (((hI t ht).div (hasDerivAt_pow n t) htn).const_add 1).congr_deriv ?_
    have hpow : (n : ℝ) * t ^ (n - 1) = n * t ^ n / t := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [eq_div_iff ht0, mul_assoc, pow_sub_one_mul hn.ne']
    have hEt : E t = t * I' t - n * I t - t * Q t := by linarith [hid t ht]
    rw [ha t, div_mul_cancel₀ _ (hΨpos t ht).ne', hpow, pow_succ, hEt]
    field_simp
    ring
  -- Step 6: `Φ(t) = exp(−G(t)) Ψ(t)` has `Φ' = exp(−G) Q/tⁿ` on `(0, R)`.
  have hΦ : ∀ t ∈ Ioo 0 R, HasDerivAt
      (fun u => Real.exp (-∫ τ in (0)..u, a τ) * (1 + I u / u ^ n))
      (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) t := by
    intro t ht
    refine ((hG t ht).neg.exp.mul (hΨ t ht)).congr_deriv ?_
    rw [Pi.neg_apply]
    ring
  -- Step 7: FTC on `[s, r] ⊆ (0, R)`.
  have hsub : uIcc s r ⊆ Ioo 0 R := by
    rw [uIcc_of_le hsr]
    exact fun x hx => ⟨hs.trans_le hx.1, hx.2.trans_lt hrR⟩
  have hcont : ContinuousOn
      (fun t => Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) (uIcc s r) := by
    intro t ht
    have ht' := hsub ht
    exact ((hG t ht').continuousAt.neg.rexp.mul ((hQ t ht').div
      (continuous_pow n).continuousAt (pow_ne_zero n ht'.1.ne'))).continuousWithinAt
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΦ t (hsub ht))
    hcont.intervalIntegrable).symm
/-- **Cutoff-kernel lower bound** (the cutoff form of Simon Ch. 4, 4.7: step 6 of the proof of
`allard52_am_annular_tonelli`, for one fixed `c ∈ [(1 + ε)s, r]`).  For a `C¹` nonincreasing
cutoff `φ` (`φ = 1` on `(−∞, 1]`, `φ = 0` on `[1 + ε, ∞)`), `0 < s` and `(1 + ε)s ≤ c ≤ r`,
`c⁻ⁿ ≤ ∫ₛʳ −((c/t) φ'(c/t))/t · t⁻ⁿ dt`.
Proof: the kernel `k(t) = −((c/t) φ'(c/t))/t` is the derivative of `t ↦ φ(c/t)` and is `≥ 0`
on `[s, r]`, so `∫ₛʳ k = φ(c/r) − φ(c/s) = 1 − 0 = 1`.  Where `k(t) ≠ 0` we have `φ'(c/t) ≠ 0`,
hence `c/t ≥ 1`, i.e. `t ≤ c`, and `k(t) c⁻ⁿ ≤ k(t) t⁻ⁿ`; integrate. -/
theorem allard52_amt_kernel_lower_bound : ∀ (n : ℕ) (φ : ℝ → ℝ) (ε s r c : ℝ), 0 < ε → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → (1 + ε) * s ≤ c → c ≤ r → 1 / c ^ n ≤ ∫ t in s..r, -(c / t * deriv φ (c / t)) / t / t ^ n := by
  intro n φ ε s r c hε hφ hanti hone hzero hs hsc hcr
  -- step 1: `0 < s ≤ c ≤ r`
  have hc : 0 < c := by nlinarith
  have hsr : s ≤ r := by nlinarith
  have hr : 0 < r := hc.trans_le hcr
  have hpos : ∀ t ∈ Icc s r, 0 < t := fun t ht => hs.trans_le ht.1
  -- step 2: `φ'` is continuous, `φ' ≤ 0`, and `φ' = 0` on `(−∞, 1)`
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hdcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hdnp : ∀ u, deriv φ u ≤ 0 := fun u => hanti.deriv_nonpos
  have hdlo : ∀ u, u < 1 → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact hone v hv.le
    exact h.deriv_eq.trans (deriv_const u 1)
  -- step 3: the kernel `k` is continuous and nonnegative on `[s, r]`
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => -(c / t * deriv φ (c / t)) / t := ⟨_, rfl⟩
  have hct : ContinuousOn (fun t : ℝ => c / t) (Icc s r) :=
    continuousOn_const.div continuousOn_id fun t ht => (hpos t ht).ne'
  have hkcont : ContinuousOn k (Icc s r) := by
    rw [hk]
    exact ((hct.mul (hdcont.comp_continuousOn hct)).neg).div continuousOn_id
      fun t ht => (hpos t ht).ne'
  have hknn : ∀ t ∈ Icc s r, 0 ≤ k t := by
    intro t ht
    have ht0 := hpos t ht
    rw [hk]
    exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg hc.le ht0.le) (hdnp _))) ht0.le
  -- step 4: `∫ₛʳ k = φ(c/r) − φ(c/s) = 1`
  have hderiv : ∀ t ∈ uIcc s r, HasDerivAt (fun t => φ (c / t)) (k t) t := by
    intro t ht
    rw [uIcc_of_le hsr] at ht
    have ht0 := hpos t ht
    have h1 : HasDerivAt (fun t => c / t) (c * -(t ^ 2)⁻¹) t := by
      simpa only [div_eq_mul_inv] using (hasDerivAt_inv ht0.ne').const_mul c
    have h2 : HasDerivAt (fun t => φ (c / t)) (deriv φ (c / t) * (c * -(t ^ 2)⁻¹)) t :=
      (hdiff (c / t)).hasDerivAt.comp t h1
    convert h2 using 1
    rw [hk]
    field_simp
  have hkint : IntervalIntegrable k volume s r := hkcont.intervalIntegrable_of_Icc hsr
  have hint1 : ∫ t in s..r, k t = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkint,
      hone _ ((div_le_one hr).mpr hcr), hzero _ ((le_div_iff₀ hs).mpr hsc), sub_zero]
  -- step 5: `k(t) c⁻ⁿ ≤ k(t) t⁻ⁿ` on `[s, r]`
  have hpt : ∀ t ∈ Icc s r, k t * (1 / c ^ n) ≤ k t * (1 / t ^ n) := by
    intro t ht
    have ht0 := hpos t ht
    by_cases hk0 : k t = 0
    · rw [hk0, zero_mul, zero_mul]
    · have hd : deriv φ (c / t) ≠ 0 := by
        intro hd
        apply hk0
        rw [hk]
        simp only [hd, mul_zero, neg_zero, zero_div]
      have h1 : 1 ≤ c / t := by
        by_contra hlt
        push Not at hlt
        exact hd (hdlo _ hlt)
      have htc : t ≤ c := by
        rwa [le_div_iff₀ ht0, one_mul] at h1
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (pow_pos ht0 n) (pow_le_pow_left₀ ht0.le htc n)) (hknn t ht)
  -- step 6: integrate
  have hint2 : IntervalIntegrable (fun t => k t * (1 / t ^ n)) volume s r := by
    refine ContinuousOn.intervalIntegrable_of_Icc hsr (hkcont.mul ?_)
    exact continuousOn_const.div (continuousOn_id.pow n) fun t ht => (pow_pos (hpos t ht) n).ne'
  have hmono := intervalIntegral.integral_mono_on hsr (hkint.mul_const (1 / c ^ n)) hint2 hpt
  rw [intervalIntegral.integral_mul_const, hint1, one_mul] at hmono
  refine hmono.trans_eq (intervalIntegral.integral_congr fun t _ => ?_)
  simp only [hk]
  ring
/-- **Tonelli identity for the cutoff kernel** (the cutoff form of Simon Ch. 4, 4.7: steps 1–5 and
8 of the proof of `allard52_am_annular_tonelli`).  Let `μ(B_R(y)) < ∞`, let `w` be a.e. strongly
measurable for `μ ⌞ B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. on `B̆_R(y)`, let `φ` be `C¹` and
nonincreasing with `φ = 0` on `[1 + ε, ∞)`, and let `0 < s ≤ r`, `(1 + ε)r < R`.  With
`r_x = |x − y|` and `H(x) = ∫ₛʳ −((r_x/t) φ'(r_x/t))/t · t⁻ⁿ dt`, the lower integral of `w H`
against `μ` is `∫ₛʳ −(∫ (r_x/t) φ'(r_x/t) w dμ)/t · t⁻ⁿ dt`.
Proof: for `t ∈ [s, r]` the kernel vanishes off `B = B_{(1+ε)r}(y) ⊆ B̆_R(y)`, so both sides only
see the finite measure `ν = μ ⌞ B`, and `H ≥ 0` since `φ' ≤ 0`.  The integrand
`−((r_x/t) φ'(r_x/t))/t · t⁻ⁿ · w(x)` is a.e. strongly measurable and bounded on `[s, r] × B`, hence
integrable for `𝓛¹ ⌞ (s, r] × ν`; Fubini swaps the integrals, and `w H ≥ 0` `ν`-a.e. turns the
Bochner integral into the lower integral. -/
theorem allard52_amt_fubini_lintegral : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (R ε s r : ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → s ≤ r → (1 + ε) * r < R → ∫⁻ x, ENNReal.ofReal (w x * (∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ = ENNReal.ofReal (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) := by
  intro n ℓ μ w y φ R ε s r hε hμR hw hw01 hφ hφanti hφzero hs hsr hR
  -- step 1: `B = B_{(1+ε)r}(y) ⊆ B̆_R(y)`, `ν = μ ⌞ B` and `𝓛¹ ⌞ (s, r]` are finite; facts on `φ'`
  have hBball : closedBall y ((1 + ε) * r) ⊆ ball y R := closedBall_subset_ball hR
  have hBmeas : MeasurableSet (closedBall y ((1 + ε) * r)) := isClosed_closedBall.measurableSet
  have : IsFiniteMeasure (μ.restrict (closedBall y ((1 + ε) * r))) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (hBball.trans ball_subset_closedBall)).trans_lt hμR).ne
  have : IsFiniteMeasure (volume.restrict (uIoc s r)) := isFiniteMeasure_restrict.mpr (by
    rw [uIoc_of_le hsr, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hdcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hdnonpos : ∀ u, deriv φ u ≤ 0 := fun u => hφanti.deriv_nonpos
  have hdzero : ∀ u, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv => hφzero v (le_of_lt hv)
    rw [h.deriv_eq, deriv_const]
  -- step 2: the kernel `a(t, x) = (r_x/t) φ'(r_x/t)` vanishes for `t ∈ [s, r]` and `x ∉ B`
  have hvan : ∀ t ∈ Icc s r, ∀ x ∉ closedBall y ((1 + ε) * r),
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) = 0 := by
    intro t ht x hx
    have ht0 : 0 < t := hs.trans_le ht.1
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have h1 : (1 + ε) * t < ‖x - y‖ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 (by linarith)) hx
    rw [hdzero _ ((lt_div_iff₀ ht0).mpr h1), mul_zero]
  -- step 3: `H(x) ≥ 0`
  have hHnn : ∀ x, 0 ≤ ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    intro x
    refine intervalIntegral.integral_nonneg hsr fun t ht => ?_
    have ht0 : 0 < t := hs.trans_le ht.1
    exact div_nonneg (div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (norm_nonneg _) ht0.le) (hdnonpos _))) ht0.le) (pow_pos ht0 n).le
  -- step 4: the left side only sees `B`, since `H = 0` off `B`
  have hLHS : ∫⁻ x, ENNReal.ofReal (w x * (∫ t in s..r,
        -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ
      = ∫⁻ x in closedBall y ((1 + ε) * r), ENNReal.ofReal (w x * (∫ t in s..r,
        -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ := by
    refine (setLIntegral_eq_of_support_subset
      (Function.support_subset_iff'.mpr fun x hx => ?_)).symm
    have h0 : EqOn (fun t => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)
        (fun _ => (0 : ℝ)) (uIcc s r) := by
      intro t ht
      rw [uIcc_of_le hsr] at ht
      simp only [hvan t ht x hx, neg_zero, zero_div]
    rw [intervalIntegral.integral_congr h0]
    simp
  -- step 5: each inner `μ`-integral is the `ν`-integral of `F(t, x) = −a(t, x)/t · t⁻ⁿ · w(x)`
  have hRHS : EqOn (fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n)
      (fun t => ∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x
        ∂(μ.restrict (closedBall y ((1 + ε) * r)))) (uIcc s r) := by
    intro t ht
    rw [uIcc_of_le hsr] at ht
    have h1 : ∀ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x
        = (-1 / t / t ^ n) * (‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) := fun x => by ring
    simp only [h1, integral_const_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hvan t ht x hx, zero_mul]]
    ring
  -- step 6: `F` is integrable for `𝓛¹ ⌞ (s, r] × ν`: measurable kernel times `w ∘ snd`, bounded
  have hKmeas : Measurable fun p : ℝ × Amb n ℓ =>
      -(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n := by
    have hu : Measurable fun p : ℝ × Amb n ℓ => ‖p.2 - y‖ / p.1 :=
      (measurable_snd.sub_const y).norm.div measurable_fst
    exact ((hu.mul ((measurable_deriv φ).comp hu)).neg.div measurable_fst).div
      (measurable_fst.pow_const n)
  have hwν : AEStronglyMeasurable w (μ.restrict (closedBall y ((1 + ε) * r))) :=
    hw.mono_measure (Measure.restrict_mono hBball le_rfl)
  have hKcont : ContinuousOn (fun p : ℝ × Amb n ℓ =>
      -(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n)
      (Icc s r ×ˢ closedBall y ((1 + ε) * r)) := by
    have h1 : ∀ p ∈ Icc s r ×ˢ closedBall y ((1 + ε) * r), p.1 ≠ 0 :=
      fun p hp => (hs.trans_le hp.1.1).ne'
    have hu : ContinuousOn (fun p : ℝ × Amb n ℓ => ‖p.2 - y‖ / p.1)
        (Icc s r ×ˢ closedBall y ((1 + ε) * r)) :=
      ContinuousOn.div (by fun_prop) continuousOn_fst h1
    exact ((hu.mul (hdcont.comp_continuousOn hu)).neg.div continuousOn_fst h1).div
      (continuousOn_fst.pow n) fun p hp => pow_ne_zero n (h1 p hp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
    (isCompact_closedBall y ((1 + ε) * r))).exists_bound_of_continuousOn hKcont
  have hae1 : ∀ᵐ p ∂((volume.restrict (uIoc s r)).prod
      (μ.restrict (closedBall y ((1 + ε) * r)))), p.1 ∈ Ioc s r := by
    have h : ∀ᵐ t ∂(volume.restrict (uIoc s r)), t ∈ Ioc s r := by
      rw [uIoc_of_le hsr]; exact ae_restrict_mem measurableSet_Ioc
    exact Measure.quasiMeasurePreserving_fst.ae h
  have hae2 : ∀ᵐ p ∂((volume.restrict (uIoc s r)).prod
      (μ.restrict (closedBall y ((1 + ε) * r)))),
      p.2 ∈ closedBall y ((1 + ε) * r) ∧ (p.2 ∈ ball y R → 0 ≤ w p.2 ∧ w p.2 ≤ 1) := by
    have h : ∀ᵐ x ∂(μ.restrict (closedBall y ((1 + ε) * r))),
        x ∈ closedBall y ((1 + ε) * r) ∧ (x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) :=
      (ae_restrict_mem hBmeas).and (ae_restrict_of_ae hw01)
    exact Measure.quasiMeasurePreserving_snd.ae h
  have hFint : Integrable (Function.uncurry fun t x =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x)
      ((volume.restrict (uIoc s r)).prod (μ.restrict (closedBall y ((1 + ε) * r)))) := by
    refine Integrable.mono' (integrable_const C)
      (hKmeas.aestronglyMeasurable.mul hwν.comp_snd) ?_
    filter_upwards [hae1, hae2] with p hp1 hp2
    have hpK := hC p ⟨Ioc_subset_Icc_self hp1, hp2.1⟩
    have hw1 := hp2.2 (hBball hp2.1)
    show ‖-(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n * w p.2‖ ≤ C
    rw [norm_mul]
    have hwn : ‖w p.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hw1.1, hw1.2]
    calc _ ≤ ‖-(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n‖ * 1 :=
          mul_le_mul_of_nonneg_left hwn (norm_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hpK
  -- step 7: Fubini; the inner `t`-integral of `F(·, x)` is `w(x) H(x)`, which is `ν`-integrable
  have hswap := intervalIntegral_integral_swap hFint
  have hinner : ∀ x, (∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x)
      = w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    intro x
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  have hint : Integrable
      (fun x => w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)
      (μ.restrict (closedBall y ((1 + ε) * r))) := by
    refine hFint.integral_prod_right.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← hinner x, intervalIntegral.integral_of_le hsr, uIoc_of_le hsr]
  -- step 8: `w H ≥ 0` `ν`-a.e.
  have hnn : 0 ≤ᵐ[μ.restrict (closedBall y ((1 + ε) * r))]
      fun x => w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    filter_upwards [ae_restrict_mem hBmeas, ae_restrict_of_ae hw01] with x hxB hx
    exact mul_nonneg (hx (hBball hxB)).1 (hHnn x)
  -- step 9: assemble
  rw [hLHS, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    intervalIntegral.integral_congr hRHS, hswap]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => (hinner x).symm)
/-- **Simon Ch. 4, 3.4–3.5 and 4.7** (the Tonelli step for one fixed cutoff `φ`).  Let `ε > 0`,
`μ(B_R(y)) < ∞`, `w` a.e.-strongly measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. there, and `φ`
a nonincreasing `C¹` function with `φ = 1` on `(−∞, 1]` and `φ = 0` on `[1 + ε, ∞)`.  If
`0 < s ≤ r` and `(1 + ε) r < R`, then with `r_x = |x − y|` and
`Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w(x) dμ`,
`∫_{B_r(y) \ B̆_{(1+ε)s}(y)} w r_x⁻ⁿ dμ ≤ ∫ₛʳ Q(t) t⁻ⁿ dt`.
Proof: for `x` in the annulus, `c = r_x ∈ [(1 + ε) s, r]`, so the kernel bound
`c⁻ⁿ ≤ h(c) = ∫ₛʳ −(c/t φ'(c/t))/t/tⁿ dt` and `w(x) ≥ 0` give `w r_x⁻ⁿ ≤ w h(r_x)`; enlarging the
domain to `ℝ^{n+ℓ}` and Tonelli, `∫ w h(r_x) dμ = ∫ₛʳ Q(t)/tⁿ dt`, conclude. -/
theorem allard52_am_annular_tonelli : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (R ε s r : ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → s ≤ r → (1 + ε) * r < R → ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) := by
  intro n ℓ μ w y φ R ε s r hε hμ hw hw01 hφ hanti hφ1 hφ0 hs hsr hrR
  -- Step 1: `r < (1 + ε) r < R`, so the annulus `A = B_r(y) \ B̆_{(1+ε)s}(y)` lies in `B̆_R(y)`.
  have hrR' : r < R := by nlinarith [mul_pos hε (hs.trans_le hsr)]
  calc ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ
      ≤ ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal
          (w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n) ∂μ := by
        -- Step 2: on `A`, `w ≥ 0` a.e. and `r_x⁻ⁿ ≤ h(r_x)` (kernel bound with `c = r_x`).
        refine setLIntegral_mono_ae' (measurableSet_closedBall.diff measurableSet_ball) ?_
        filter_upwards [hw01] with x hx hxA
        have hxr : ‖x - y‖ ≤ r := mem_closedBall_iff_norm.1 hxA.1
        have hxs : (1 + ε) * s ≤ ‖x - y‖ := not_lt.1 fun h => hxA.2 (mem_ball_iff_norm.2 h)
        have hw0 : 0 ≤ w x := (hx (mem_ball_iff_norm.2 (hxr.trans_lt hrR'))).1
        refine ENNReal.ofReal_le_ofReal ((div_eq_mul_one_div _ _).trans_le ?_)
        exact mul_le_mul_of_nonneg_left (Submission.allard52_amt_kernel_lower_bound n φ ε s r
          ‖x - y‖ hε hφ hanti hφ1 hφ0 hs hxs hxr) hw0
    _ ≤ ∫⁻ x, ENNReal.ofReal
          (w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n) ∂μ :=
        setLIntegral_le_lintegral _ _
    -- Step 3: Tonelli, `∫ w h(r_x) dμ = ∫ₛʳ Q(t)/tⁿ dt`.
    _ = ENNReal.ofReal
          (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) :=
        Submission.allard52_amt_fubini_lintegral n ℓ μ w y φ R ε s r hε hμ hw hw01 hφ hanti hφ0
          hs hsr hrR
/-- **Simon Ch. 4, 4.8–4.9** (density at the centre, for an abstract measure `μ`).  Let `R, α > 0`,
`μ(B_R(y)) < ∞`, and on `(0, R)` let `e^{-Λ} ≤ F(r) ≤ e^Λ` and `|F(r) − 1| ≤ Λ (r/R)^α`.  If
`Φ(r) = F(r) r⁻ⁿ μ(B_r(y)) + F(r) − 1` is nondecreasing on `(0, R)`, then there is `t ≥ 0` with
`μ(B_r(y)) / (ω_n rⁿ) → t` as `r ↓ 0`, and `ω_n t ≤ Φ(r)` for every `r ∈ (0, R)`.
Proof: `F → 1` as `r ↓ 0`; `Φ ≥ e^{-Λ} − 1` is monotone, so it tends to `L = inf Φ`; hence
`r⁻ⁿ μ(B_r(y)) = (Φ(r) + 1)/F(r) − 1 → L ≥ 0`, and `t = L/ω_n` works since `ω_n > 0`. -/
theorem allard52_am_center_density : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (F : ℝ → ℝ) (R Λ α : ℝ), 0 < R → 0 < α → μ (closedBall y R) < ⊤ → (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ α) → (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) → ∃ t : ℝ, 0 ≤ t ∧ Tendsto (fun r : ℝ => μ (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * t ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 := by
  intro n ℓ μ y F R Λ α hR hα hfin hF hmono0
  -- Notation: `Φ(r) = F(r) r⁻ⁿ m(r) + F(r) − 1` with `m(r) = μ(B_r(y))`.
  set Φ := fun r : ℝ => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 with hΦ
  have hmono : MonotoneOn Φ (Ioo 0 R) := fun s hs r hr hsr => hmono0 s r hs.1 hsr hr.2
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
  -- Step 1: on `(0, R)`, `μ(B_r(y)) ≤ μ(B_R(y)) < ∞` and `F(r) ≥ e^{-Λ} > 0`.
  have hmfin : ∀ r ∈ Ioo 0 R, μ (closedBall y r) ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hfin.ne (measure_mono (closedBall_subset_closedBall hr.2.le))
  have hFpos : ∀ r ∈ Ioo 0 R, 0 < F r := fun r hr => (Real.exp_pos _).trans_le (hF r hr).1
  -- Step 2: `F → 1` as `r ↓ 0`, squeezing `|F(r) − 1| ≤ Λ (r/R)^α → Λ 0^α = 0` (`α > 0`).
  have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    have hlim : Tendsto (fun r : ℝ => Λ * (r / R) ^ α) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => Λ * (r / R) ^ α) (𝓝 0) (𝓝 (Λ * (0 / R) ^ α)) :=
        ((tendsto_id.div_const R).rpow_const (Or.inr hα.le)).const_mul Λ
      rw [zero_div, Real.zero_rpow hα.ne', mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    rw [Real.norm_eq_abs]
    exact (hF r hr).2.2
  -- Step 3: `Φ(r) ≥ F(r) − 1 ≥ e^{-Λ} − 1` on `(0, R)`; the monotone `Φ` tends to `L = inf Φ`.
  have hbdd : BddBelow (Φ '' Ioo 0 R) := by
    refine ⟨Real.exp (-Λ) - 1, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have h1 := (hF r hr).1
    have h2 : 0 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
      mul_nonneg (mul_nonneg (hFpos r hr).le (inv_nonneg.2 (pow_nonneg hr.1.le n)))
        ENNReal.toReal_nonneg
    simp only [hΦ]
    linarith
  set L := sInf (Φ '' Ioo 0 R)
  have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := hmono.tendsto_nhdsWithin_Ioo_right hne hbdd
  -- Step 4: `r⁻ⁿ m(r) = (Φ(r) + 1)/F(r) − 1 → (L + 1)/1 − 1 = L`, and `L ≥ 0`.
  set g := fun r : ℝ => (r ^ n)⁻¹ * (μ (closedBall y r)).toReal with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 L) := by
    have h := ((hΦL.add_const 1).div hF1 one_ne_zero).sub_const 1
    have heq : (fun r => (Φ r + 1) / F r - 1) =ᶠ[𝓝[>] 0] g := by
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      have hFr : F r ≠ 0 := (hFpos r hr).ne'
      simp only [hΦ, hg_def]
      field_simp
      ring
    simpa using h.congr' heq
  have hL0 : 0 ≤ L := by
    apply ge_of_tendsto hg
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg (le_of_lt hr) n)) ENNReal.toReal_nonneg
  -- Step 5: `ω_n = π^{n/2}/Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Step 6: `t = L/ω_n`; on `(0, R)`, `μ(B_r(y)) / ofReal(ω_n rⁿ) = ofReal(r⁻ⁿ m(r)/ω_n)`.
  refine ⟨L / unitBallVolume n, div_nonneg hL0 hω.le, ?_, ?_⟩
  · have h := ENNReal.tendsto_ofReal (hg.div_const (unitBallVolume n))
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    have hr0 : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr.1 n)
    rw [← ENNReal.ofReal_toReal (hmfin r hr), ← ENNReal.ofReal_div_of_pos hr0]
    congr 1
    simp only [hg_def]
    field_simp
  -- Step 7: `ω_n t = L ≤ Φ(r)` for every `r ∈ (0, R)`.
  · intro r hr
    rw [mul_div_cancel₀ _ hω.ne']
    exact csInf_le hbdd ⟨r, hr, rfl⟩
/-- Simon Ch. 5, 2.4 at one centre `y` (abstract form): pinched mass and conical-excess bounds from
the monotonicity data.  Write `B_r = B_r(y)` (closed) and `Φ(r) = F(r) r⁻ⁿ μ(B_r) + F(r) − 1`, and
assume, for `r ∈ (0, R)`, `μ(B_r) ≤ M`, `e^{−Λ} ≤ F(r) ≤ e^Λ` and `|F(r) − 1| ≤ Λ`, and, for
`0 < s ≤ r < R`, `Φ(s) ≤ Φ(r)` and `∫_{B_r \ B_s} g dμ ≤ e^Λ (Φ(r) − Φ(s))`.  Letting `r ↑ R` in
`Φ(s) ≤ Φ(r) ≤ e^Λ r⁻ⁿ M + Λ` gives `Φ(s) ≤ e^Λ M/Rⁿ + Λ`, hence for `s ∈ (0, R)`:
`μ(B_s) ≤ (e^{2Λ} M/Rⁿ + 2e^Λ Λ) sⁿ`; and if `ω ≤ Φ` on `(0, R)`, also
`e^{−Λ} (ω − Λ) sⁿ ≤ μ(B_s)` and `∫_{B_s} g dμ ≤ e^Λ (e^Λ M/Rⁿ + Λ − ω)`, the latter by exhausting
`B_s \ {y}` with the annuli `B_s \ B_{s/(k+2)}` (the centre contributes nothing as `g(y) = 0`). -/
theorem allard52_center_density_bounds : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (F : ℝ → ℝ) (y : Amb n ℓ) (ω R Λ M : ℝ), 0 < R → 0 < Λ → 0 ≤ M → g y = 0 → (∀ r ∈ Ioo 0 R, μ (closedBall y r) ≤ ENNReal.ofReal M) → (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ) → (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1)))) → ∀ s : ℝ, 0 < s → s < R → μ (closedBall y s) ≤ ENNReal.ofReal ((Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n) ∧ ((∀ t ∈ Ioo 0 R, ω ≤ F t * (t ^ n)⁻¹ * (μ (closedBall y t)).toReal + F t - 1) → ENNReal.ofReal (Real.exp (-Λ) * (ω - Λ) * s ^ n) ≤ μ (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω))) := by
  intro n ℓ μ g F y ω R Λ M hR _hΛ hM hgy hμ hF hΦ s hs hsR
  have hsI : s ∈ Ioo 0 R := ⟨hs, hsR⟩
  have hexp_pos : 0 < Real.exp Λ := Real.exp_pos Λ
  have hexpn_pos : 0 < Real.exp (-Λ) := Real.exp_pos (-Λ)
  -- Step 1: on `(0, R)`, `μ(B_r) ≤ M < ∞`, so `μ(B_r) = ofReal m(r)` with `0 ≤ m(r) ≤ M`.
  have hfin : ∀ r ∈ Ioo 0 R, μ (closedBall y r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμ r hr)
  have hmM : ∀ r ∈ Ioo 0 R, (μ (closedBall y r)).toReal ≤ M := fun r hr =>
    ENNReal.toReal_le_of_le_ofReal hM (hμ r hr)
  have hm0 : ∀ r, 0 ≤ (μ (closedBall y r)).toReal := fun r => ENNReal.toReal_nonneg
  -- Step 2: `Φ(r) ≤ e^Λ r⁻ⁿ M + Λ` on `(0, R)`, as `0 ≤ F(r) ≤ e^Λ` and `F(r) − 1 ≤ Λ`.
  have hΦup : ∀ r ∈ Ioo 0 R, F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1
      ≤ Real.exp Λ * (r ^ n)⁻¹ * M + Λ := by
    intro r hr
    obtain ⟨-, hF2, hF3⟩ := hF r hr
    have hrn : 0 < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr.1 n)
    have h1 : F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal ≤ Real.exp Λ * (r ^ n)⁻¹ * M :=
      calc F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal
          ≤ Real.exp Λ * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF2 hrn.le) (hm0 r)
        _ ≤ Real.exp Λ * (r ^ n)⁻¹ * M :=
            mul_le_mul_of_nonneg_left (hmM r hr) (mul_pos hexp_pos hrn).le
    have h2 : F r - 1 ≤ Λ := le_trans (le_abs_self _) hF3
    linarith
  -- Step 2 (†): letting `r ↑ R` in `Φ(s) ≤ Φ(r) ≤ e^Λ r⁻ⁿ M + Λ` gives `Φ(s) ≤ e^Λ M/Rⁿ + Λ`.
  have hd : F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1
      ≤ Real.exp Λ * (M / R ^ n) + Λ := by
    have hlim0 : Tendsto (fun r : ℝ => Real.exp Λ * (r ^ n)⁻¹ * M + Λ) (𝓝 R)
        (𝓝 (Real.exp Λ * (R ^ n)⁻¹ * M + Λ)) :=
      ((tendsto_const_nhds.mul (((continuous_pow n).tendsto R).inv₀
        (pow_ne_zero _ hR.ne'))).mul tendsto_const_nhds).add tendsto_const_nhds
    have hlim : Tendsto (fun r : ℝ => Real.exp Λ * (r ^ n)⁻¹ * M + Λ) (𝓝[<] R)
        (𝓝 (Real.exp Λ * (M / R ^ n) + Λ)) := by
      rw [show Real.exp Λ * (M / R ^ n) + Λ = Real.exp Λ * (R ^ n)⁻¹ * M + Λ by
        rw [div_eq_mul_inv]; ring]
      exact tendsto_nhdsWithin_of_tendsto_nhds hlim0
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hsR] with r hr
    exact le_trans (hΦ s r hs hr.1.le hr.2).1 (hΦup r ⟨lt_trans hs hr.1, hr.2⟩)
  obtain ⟨hF1, hF2, hF3⟩ := hF s hsI
  have hsn : 0 < s ^ n := pow_pos hs n
  have hx0 : 0 ≤ (s ^ n)⁻¹ * (μ (closedBall y s)).toReal :=
    mul_nonneg (inv_pos.mpr hsn).le (hm0 s)
  have hcancel : ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n
      = (μ (closedBall y s)).toReal := by
    field_simp
  refine ⟨?_, ?_⟩
  · -- Step 3 (i): `F(s) s⁻ⁿ m(s) ≤ e^Λ M/Rⁿ + 2Λ` by (†) and `1 − F(s) ≤ Λ`; divide by
    -- `F(s) ≥ e^{−Λ}` and multiply by `sⁿ`.
    have h1 : 1 - F s ≤ Λ := by
      have := neg_abs_le (F s - 1)
      linarith
    have hA : F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)
        ≤ Real.exp Λ * (M / R ^ n) + 2 * Λ := by
      have : F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
          = F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by ring
      linarith
    have hB : (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
        ≤ Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ) := by
      have hC : Real.exp (-Λ) * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)
          ≤ Real.exp Λ * (M / R ^ n) + 2 * Λ :=
        le_trans (mul_le_mul_of_nonneg_right hF1 hx0) hA
      have hexpinv : Real.exp Λ * Real.exp (-Λ) = 1 := by
        rw [← Real.exp_add]; simp
      calc (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
          = Real.exp Λ * (Real.exp (-Λ) * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)) := by
            rw [← mul_assoc, hexpinv, one_mul]
        _ ≤ Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ) :=
            mul_le_mul_of_nonneg_left hC hexp_pos.le
    have h2Λ : Real.exp (2 * Λ) = Real.exp Λ * Real.exp Λ := by
      rw [two_mul, Real.exp_add]
    have hmain : (μ (closedBall y s)).toReal
        ≤ (Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n := by
      calc (μ (closedBall y s)).toReal
          = ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n := hcancel.symm
        _ ≤ (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ)) * s ^ n :=
            mul_le_mul_of_nonneg_right hB hsn.le
        _ = (Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n := by
            rw [h2Λ]; ring
    exact (ENNReal.ofReal_toReal (hfin s hsI)).symm.trans_le (ENNReal.ofReal_le_ofReal hmain)
  · intro hω
    have hωs := hω s hsI
    refine ⟨?_, ?_⟩
    · -- Step 4 (ii): `ω − Λ ≤ Φ(s) − (F(s) − 1) ≤ F(s) s⁻ⁿ m(s) ≤ e^Λ s⁻ⁿ m(s)`.
      have h2 : F s - 1 ≤ Λ := le_trans (le_abs_self _) hF3
      have hA : ω - Λ ≤ F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by
        have : F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
            = F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by ring
        linarith
      have hC : ω - Λ ≤ Real.exp Λ * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) :=
        le_trans hA (mul_le_mul_of_nonneg_right hF2 hx0)
      have hexpinv : Real.exp (-Λ) * Real.exp Λ = 1 := by
        rw [← Real.exp_add]; simp
      have hB : Real.exp (-Λ) * (ω - Λ) ≤ (s ^ n)⁻¹ * (μ (closedBall y s)).toReal := by
        calc Real.exp (-Λ) * (ω - Λ)
            ≤ Real.exp (-Λ) * (Real.exp Λ * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)) :=
              mul_le_mul_of_nonneg_left hC hexpn_pos.le
          _ = (s ^ n)⁻¹ * (μ (closedBall y s)).toReal := by
              rw [← mul_assoc, hexpinv, one_mul]
      have hmain : Real.exp (-Λ) * (ω - Λ) * s ^ n ≤ (μ (closedBall y s)).toReal := by
        calc Real.exp (-Λ) * (ω - Λ) * s ^ n
            ≤ ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n :=
              mul_le_mul_of_nonneg_right hB hsn.le
          _ = (μ (closedBall y s)).toReal := hcancel
      exact (ENNReal.ofReal_le_ofReal hmain).trans_eq (ENNReal.ofReal_toReal (hfin s hsI))
    · -- Step 5 (iii): each annulus `B_s \ B_t`, `t ∈ (0, s)`, carries at most
      -- `e^Λ (Φ(s) − Φ(t)) ≤ e^Λ (e^Λ M/Rⁿ + Λ − ω)`.
      have hpiece : ∀ t : ℝ, 0 < t → t < s →
          ∫⁻ x in closedBall y s \ closedBall y t, ENNReal.ofReal (g x) ∂μ
            ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
        intro t ht hts
        refine le_trans (hΦ t s ht hts.le hsR).2 (ENNReal.ofReal_le_ofReal ?_)
        have hωt := hω t ⟨ht, lt_trans hts hsR⟩
        apply mul_le_mul_of_nonneg_left _ hexp_pos.le
        linarith
      -- The annuli `B_s \ B_{s/(k+2)}` increase to `B_s \ {y}`.
      have hmono : Monotone (fun k : ℕ => closedBall y s \ closedBall y (s / ((k : ℝ) + 2))) := by
        intro i j hij
        apply sdiff_subset_sdiff_right
        apply closedBall_subset_closedBall
        have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
        apply div_le_div_of_nonneg_left hs.le (by positivity)
        linarith
      have hUnion : (⋃ k : ℕ, closedBall y s \ closedBall y (s / ((k : ℝ) + 2)))
          = closedBall y s \ {y} := by
        ext x
        simp only [mem_iUnion, Set.mem_sdiff, mem_closedBall, mem_singleton_iff, not_le]
        constructor
        · rintro ⟨k, hx1, hx2⟩
          refine ⟨hx1, fun h => ?_⟩
          have : 0 < s / ((k : ℝ) + 2) := by positivity
          rw [h, dist_self] at hx2
          linarith
        · rintro ⟨hx1, hx2⟩
          have hpos : 0 < dist x y := dist_pos.mpr hx2
          obtain ⟨k, hk⟩ := exists_nat_gt (s / dist x y)
          refine ⟨k, hx1, ?_⟩
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hk
          nlinarith
      -- Directed exhaustion: the lower integral over `B_s \ {y}` is the supremum over the annuli.
      have hmain : ∫⁻ x in closedBall y s \ {y}, ENNReal.ofReal (g x) ∂μ
          ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
        rw [← hUnion, setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal (g x))
          hmono.directed_le]
        refine iSup_le fun k => hpiece _ (by positivity) (div_lt_self hs ?_)
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      -- The centre contributes `ofReal (g y) μ {y} = 0`.
      have hsingle : ∫⁻ x in ({y} : Set (Amb n ℓ)), ENNReal.ofReal (g x) ∂μ = 0 := by
        simp [hgy]
      calc ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ
          ≤ ∫⁻ x in (closedBall y s \ {y}) ∪ {y}, ENNReal.ofReal (g x) ∂μ := by
            apply lintegral_mono_set
            intro x hx
            by_cases h : x = y
            · exact Or.inr h
            · exact Or.inl ⟨hx, h⟩
        _ ≤ ∫⁻ x in closedBall y s \ {y}, ENNReal.ofReal (g x) ∂μ
            + ∫⁻ x in ({y} : Set (Amb n ℓ)), ENNReal.ofReal (g x) ∂μ :=
            lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
            rw [hsingle, add_zero]; exact hmain
/-- The linear algebra in the proof of Simon Ch. 5, Lemma 2.1 (p. 107): (i) the operator norm of a
linear map is at most its Hilbert–Schmidt norm `|A|`; (ii) `|p_{T⊥} v| = dist(v, T)`; and
(iii) display (2) of the proof, `trace(p_{T⊥} ∘ p_P) = ½ |p_P − p_T|²` when `dim P = dim T`. -/
theorem hsNorm_starProjection_trace_identities : (∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A) ∧ (∀ (m : ℕ) (T : Submodule ℝ (Rn m)) (v : Rn m), ‖Tᗮ.starProjection v‖ = Metric.infDist v (T : Set (Rn m))) ∧ ∀ (m : ℕ) (P T : Submodule ℝ (Rn m)), Module.finrank ℝ P = Module.finrank ℝ T → LinearMap.trace ℝ (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
    intro m k A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  · -- (ii) `p_{T⊥} v = v − p_T v`, and `p_T v` is the point of `T` nearest to `v`.
    intro m T v
    rw [Submodule.starProjection_orthogonal_val, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist]
  · -- (iii) Compute both sides in the standard orthonormal basis `eᵢ`.
    intro m P T hPT
    -- The trace is the sum of the diagonal entries `⟪eᵢ, f eᵢ⟫`.
    have htr : ∀ f : Rn m →ₗ[ℝ] Rn m, LinearMap.trace ℝ (Rn m) f =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (f (EuclideanSpace.single i 1)) := by
      intro f
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f,
        Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
    -- The trace of an orthogonal projection is the dimension of its range.
    have hproj : ∀ W : Submodule ℝ (Rn m),
        LinearMap.trace ℝ (Rn m) W.starProjection.toLinearMap = Module.finrank ℝ W := fun W =>
      LinearMap.IsProj.trace
        ⟨W.starProjection_apply_mem, fun _ hx => W.starProjection_eq_self_iff.2 hx⟩
    -- `‖p_W x‖² = ⟪x, p_W x⟫`, since `p_W` is self-adjoint and idempotent.
    have hsq : ∀ (W : Submodule ℝ (Rn m)) (x : Rn m),
        ‖W.starProjection x‖ ^ 2 = inner ℝ x (W.starProjection x) := by
      intro W x
      rw [← real_inner_self_eq_norm_sq, W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.2 (W.starProjection_apply_mem x)]
    -- Pointwise, `2 ⟪x, (I − q) p x⟫ = ‖(p − q) x‖² + ⟪x, p x⟫ − ⟪x, q x⟫`.
    have hterm : ∀ x : Rn m, 2 * inner ℝ x (Tᗮ.starProjection (P.starProjection x)) =
        ‖(P.starProjection - T.starProjection) x‖ ^ 2 + inner ℝ x (P.starProjection x) -
          inner ℝ x (T.starProjection x) := by
      intro x
      rw [Submodule.starProjection_orthogonal_val, sub_apply, norm_sub_sq_real, hsq P, hsq T,
        inner_sub_right, ← T.inner_starProjection_left_eq_right,
        real_inner_comm (T.starProjection x)]
      ring
    -- `trace p_P = dim P = dim T = trace p_T`.
    have hdim : ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (P.starProjection (EuclideanSpace.single i 1)) =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (T.starProjection (EuclideanSpace.single i 1)) := by
      have h := hproj P
      rw [hPT, ← hproj T, htr, htr] at h
      exact h
    rw [htr, hsNormSq, eq_div_iff two_ne_zero, mul_comm, Finset.mul_sum]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [Finset.sum_congr rfl fun i _ => hterm (EuclideanSpace.single i 1), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hdim, add_sub_cancel_right]
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): the Hilbert–Schmidt norm
`|A| = (Σᵢ |A eᵢ|²)^{1/2}` of `A : ℝᵐ → ℝᵏ` is comparable with the operator norm,
`‖A‖ ≤ |A| ≤ √m ‖A‖`, and satisfies the triangle inequality `|A + B| ≤ |A| + |B|`. -/
theorem allard52_gpa_hsNorm_bounds : ∀ (m k : ℕ) (A B : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A ∧ hsNorm A ≤ Real.sqrt m * ‖A‖ ∧ hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  intro m k A B
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  · -- (ii) `|A eᵢ| ≤ ‖A‖ ‖eᵢ‖ = ‖A‖` for each of the `m` unit vectors, so `|A|² ≤ m ‖A‖²`.
    have h1 : hsNormSq A ≤ m * ‖A‖ ^ 2 := by
      calc hsNormSq A = ∑ i : Fin m, ‖A (EuclideanSpace.single i 1)‖ ^ 2 := rfl
        _ ≤ ∑ _i : Fin m, ‖A‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            simpa using A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
        _ = m * ‖A‖ ^ 2 := by simp
    calc hsNorm A = √(hsNormSq A) := rfl
      _ ≤ √(m * ‖A‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt m * ‖A‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  · -- (iii) `|X|` is the norm of `(X eᵢ)ᵢ` in `L²(Fin m; ℝᵏ)`, and `X ↦ (X eᵢ)ᵢ` is additive.
    let F : (Rn m →L[ℝ] Rn k) → PiLp 2 (fun _ : Fin m => Rn k) :=
      fun X => WithLp.toLp 2 fun i => X (EuclideanSpace.single i 1)
    have hF : ∀ X, hsNorm X = ‖F X‖ := fun X => by
      rw [PiLp.norm_eq_of_L2]; rfl
    rw [hF, hF, hF]
    exact norm_add_le (F A) (F B)
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the profile of the cutoff `ζ(x) = φ(|x − ξ|/ρ)` with
`ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B_ρ(ξ)` and `|∇ζ| ≤ 3/ρ`.  With `S = smoothTransition`,
the bump `g(t) = S(12(t − 1/2)) S(12(1 − t)) ∈ [0, 1]` vanishes for `t ≤ 1/2` and for `t ≥ 1` and
equals `1` on `[7/12, 11/12]`, so `c = ∫_{1/2}^1 g ≥ 1/3`; then `φ(t) = 1 − c⁻¹ ∫_{1/2}^t g` is
`C^∞` with `|φ'| = c⁻¹ g ≤ 3`. -/
theorem exists_smooth_step_profile_lipschitz_three : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
  -- The bump `g`: smooth, with values in `[0, 1]`, zero off `(1/2, 1)`, one on `[7/12, 11/12]`.
  set g : ℝ → ℝ := fun t =>
    Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
    have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg_cont.intervalIntegrable a b
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
      (Real.smoothTransition.le_one _)
  have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
  have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
    simp only [hg_def]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  -- The normalizing constant `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`.
  set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
  have hc_ge : 1 / 3 ≤ c := by
    have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        norm_num
      · intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        exact hg_mid s hs.1 hs.2
    rw [← h]
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (ae_of_all _ hg_nonneg) (hg_int _ _)
  have hc_pos : 0 < c := by linarith
  have hcinv_le : c⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hc_pos (by norm_num)]
    linarith
  -- The primitive `F(t) = ∫_{1/2}^t g`: `F' = g` (FTC), so `F` is smooth; `0 ≤ F ≤ c`,
  -- `F = 0` on `(-∞, 1/2]` and `F = c` on `[1, ∞)`.
  set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
    (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
      (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
  have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
    simp only [hF_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hg_left s hs.2
  have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
    simp only [hF_def, hc_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
    have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_le ht] at hs
        exact hg_right s hs.1
    rw [h, add_zero]
  have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hF_left t ht]
      exact ⟨le_rfl, hc_pos.le⟩
    rcases le_total 1 t with ht' | ht'
    · rw [hF_right t ht']
      exact ⟨hc_pos.le, le_rfl⟩
    exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
      intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
  -- The profile `φ = 1 − c⁻¹ F`, with `φ' = −c⁻¹ g`.
  have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
    simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
  refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h₀, h₁⟩ := hF_bounds t
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
    have h : c⁻¹ * F t ≤ 1 := by
      calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
        _ = 1 := inv_mul_cancel₀ hc_pos.ne'
    exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
  · intro t ht
    simp only [hF_left t ht, mul_zero, sub_zero]
  · intro t ht
    simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
  · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
    rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
    calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
      _ ≤ 3 := by rw [mul_one]; exact hcinv_le
      _ = ((3 : ℝ≥0) : ℝ) := by norm_num
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), smoothness of the cutoff: if `φ` is `C^∞` with
`φ ≡ 1` on `(-∞, 1/2]` and `ρ > 0`, then `ζ(x) = φ(‖x − ξ‖/ρ)` is `C^∞` on `ℝᵐ`.  Near `ξ`,
`ζ ≡ 1` on `B̆_{ρ/2}(ξ)`; at `x ≠ ξ` the norm is `C^∞` at `x − ξ ≠ 0`. -/
theorem contDiff_radial_profile_of_eq_one_le_half : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (φ : ℝ → ℝ), 0 < ρ → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ t, t ≤ 1 / 2 → φ t = 1) → ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn m => φ (‖x - ξ‖ / ρ)) := by
  intro m ξ ρ φ hρ hφ hφ1
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x ξ with rfl | hx
  · -- `ζ ≡ 1` on the open ball `B̆_{ρ/2}(ξ)`, a neighbourhood of `ξ`.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds x (half_pos hρ)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hφ1 _ ((div_le_iff₀ hρ).2 (by linarith))
  · -- `y ↦ ‖y − ξ‖/ρ` is `C^∞` at `x` since `x − ξ ≠ 0`; compose with `φ`.
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Rn m => ‖y - ξ‖ / ρ) x :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const ρ
    exact hφ.contDiffAt.comp x h
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff gradient bound `|∇ζ| ≤ 3/ρ`, for a general
Lipschitz constant `K` in place of `3`.  If `φ` is `K`-Lipschitz and `ρ > 0`, then
`ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality, so
`‖Dζ(x)‖ ≤ K/ρ` at every `x` (where `ζ` is not differentiable, `fderiv ℝ ζ x = 0`). -/
theorem norm_fderiv_radial_profile_le_of_lipschitzWith : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (K : ℝ≥0) (φ : ℝ → ℝ), 0 < ρ → LipschitzWith K φ → ∀ x : Rn m, ‖fderiv ℝ (fun y : Rn m => φ (‖y - ξ‖ / ρ)) x‖ ≤ (K : ℝ) / ρ := by
  intro m ξ ρ K φ hρ hφ x
  -- `ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality.
  have hKρ : ((K / ρ.toNNReal : ℝ≥0) : ℝ) = K / ρ := by
    rw [NNReal.coe_div, Real.coe_toNNReal ρ hρ.le]
  have hlip : LipschitzWith (K / ρ.toNNReal) fun y : Rn m => φ (‖y - ξ‖ / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKρ]
    calc dist (φ (‖y - ξ‖ / ρ)) (φ (‖z - ξ‖ / ρ))
        ≤ K * dist (‖y - ξ‖ / ρ) (‖z - ξ‖ / ρ) := hφ.dist_le_mul _ _
      _ = K / ρ * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]; ring
      _ ≤ K / ρ * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = K / ρ * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- A `C`-Lipschitz function has `‖Dζ(x)‖ ≤ C` (and `fderiv ℝ ζ x = 0` where not differentiable).
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq hKρ
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
/-- **Simon Ch. 1, Theorem 3.6 (Upper Density Theorem)** in the contract normalization: for a
`ν`-null-measurable `A` with `ν A < ∞`, the upper density `Θ*ⁿ(ν, A, x)` vanishes for
`Hⁿ`-a.e. `x ∉ A`.  Simon's printed proof: on the level set `S_t = {x ∉ A : Θ*ⁿ > t}` and for
closed `C ⊆ A`, Vitali's covering lemma gives the comparison bound 3.3 for `ν ⌞ (A \ C)` (with
the non-sharp constant `8ⁿ / ω_n`, enough for null sets); `ν (A \ C)` is small by 1.15(2).  The
levels `t = 1/(k+1)` exhaust `Θ*ⁿ ≠ 0`, and `μHE[n]` is a multiple of `μH[n]`. -/
theorem upperDensity_ne_zero_outside_hausdorff_null : ∀ {n ℓ : ℕ} (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), NullMeasurableSet A ν → ν A < ∞ → (μHE[n] : Measure (Amb n ℓ)) {x | x ∉ A ∧ limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) ≠ 0} = 0 := by
  intro n ℓ ν A hA hAfin
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Simon 1.15(2): `A` contains closed sets `C` with `ν (A \ C)` arbitrarily small.
  have hreg : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε := by
    intro ε hε
    obtain ⟨A', hA'A, hA'm, hA'eq⟩ := hA.exists_measurable_subset_ae_eq
    have : IsFiniteMeasure (ν.restrict A') :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hAfin.ne (measure_mono hA'A))
    obtain ⟨C, hCA', hC, hCε⟩ :=
      hA'm.exists_isClosed_sdiff_lt (μ := ν.restrict A') (measure_ne_top _ _) hε
    refine ⟨C, hCA'.trans hA'A, hC, ?_⟩
    rw [Measure.restrict_apply (hA'm.diff hC.measurableSet), inter_eq_left.2 sdiff_subset] at hCε
    rwa [measure_congr (hA'eq.symm.diff (EventuallyEq.refl _ C))]
  -- The level set `S_t` is `μH[n]`-null for every `t > 0`.
  have hlevel : ∀ t : ℝ, 0 < t → μH[(n : ℝ)] {x : Amb n ℓ | x ∉ A ∧ ENNReal.ofReal t <
      limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0)} = 0 := by
    intro t ht
    set S := {x : Amb n ℓ | x ∉ A ∧ ENNReal.ofReal t <
      limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0)} with hS
    have hKnn : (0 : ℝ) ≤ 8 ^ n / unitBallVolume n / t :=
      div_nonneg (div_nonneg (by positivity) hω.le) ht.le
    set K : ℝ≥0∞ := ENNReal.ofReal (8 ^ n / unitBallVolume n / t) with hK
    -- Simon 3.3 for `ν ⌞ (A \ C)`, `C ⊆ A` closed, via Vitali's covering lemma.
    have hcomp : ∀ C ⊆ A, IsClosed C → μH[(n : ℝ)] S ≤ K * ν (A \ C) := by
      intro C hCA hC
      have hcov : ∀ R : ℝ, 0 < R → ∃ u : Set (Amb n ℓ × ℝ), u.Countable ∧
          u.PairwiseDisjoint (fun b => closedBall b.1 b.2) ∧
          (∀ b ∈ u, 0 < b.2 ∧ b.2 ≤ R ∧
            ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * b.2 ^ n) ≤
              ν.restrict (A \ C) (closedBall b.1 b.2)) ∧
          S ⊆ ⋃ b ∈ u, closedBall b.1 (4 * b.2) := by
        intro R hR
        obtain ⟨u, huT, hud, hucov⟩ :=
          Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
            {b : Amb n ℓ × ℝ | b.1 ∈ S ∧ 0 < b.2 ∧ b.2 ≤ R ∧
              ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * b.2 ^ n) ≤
                ν.restrict (A \ C) (closedBall b.1 b.2)}
            Prod.fst Prod.snd R (fun b hb => hb.2.2.1) 4 (by norm_num)
        refine ⟨u, hud.countable_of_nonempty_interior fun b hb =>
          ⟨b.1, ball_subset_interior_closedBall (mem_ball_self (huT hb).2.1)⟩, hud,
          fun b hb => (huT hb).2, fun x hx => ?_⟩
        -- A small ball around `x ∉ C` on which the density quotient exceeds `t`.
        obtain ⟨ρ, hρ, hρC⟩ := nhds_basis_closedBall.mem_iff.1
          (hC.isOpen_compl.mem_nhds fun h => hx.1 (hCA h))
        obtain ⟨r, hr, hrI⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hx.2).and_eventually
          (Ioo_mem_nhdsGT (lt_min hR hρ))).exists
        have hr0 : 0 < r := hrI.1
        have hmass : ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * r ^ n) ≤
            ν.restrict (A \ C) (closedBall x r) := by
          rw [Measure.restrict_apply measurableSet_closedBall]
          have hset : closedBall x r ∩ (A \ C) = A ∩ closedBall x r := by
            ext y
            constructor
            · rintro ⟨hy1, hy2, -⟩
              exact ⟨hy2, hy1⟩
            · rintro ⟨hy1, hy2⟩
              exact ⟨hy2, hy1,
                hρC (closedBall_subset_closedBall (hrI.2.le.trans (min_le_right _ _)) hy2)⟩
          rw [hset]
          exact ((ENNReal.lt_div_iff_mul_lt
            (Or.inl (ENNReal.ofReal_pos.2 (mul_pos hω (pow_pos hr0 n))).ne')
            (Or.inl ENNReal.ofReal_ne_top)).1 hr).le
        obtain ⟨b, hbu, hsub⟩ := hucov (x, r) ⟨hx, hr0, hrI.2.le.trans (min_le_left _ _), hmass⟩
        exact mem_biUnion hbu (hsub (mem_closedBall_self hr0.le))
      -- Covers by the enlarged balls at scales `1/(k+1) → 0`.
      choose u hu using fun k : ℕ => hcov (1 / ((k : ℝ) + 1)) (by positivity)
      have : ∀ k, Countable (u k) := fun k => (hu k).1.to_subtype
      have hH := Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) S (l := atTop)
        (fun k : ℕ => ENNReal.ofReal (8 * (1 / ((k : ℝ) + 1))))
        (by simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 8))
        (fun k (b : u k) => closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2))
        (Eventually.of_forall fun k b => ediam_le_of_forall_dist_le fun y hy z hz => by
          have h1 := dist_triangle_right y z (b : Amb n ℓ × ℝ).1
          have h2 := ((hu k).2.2.1 b b.2).2.1
          rw [mem_closedBall] at hy hz
          linarith)
        (Eventually.of_forall fun k x hx => by
          obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 ((hu k).2.2.2 hx)
          exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
      refine hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
      calc ∑' b : u k, ediam (closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2)) ^ (n : ℝ)
          ≤ ∑' b : u k,
              K * ν.restrict (A \ C) (closedBall (b : Amb n ℓ × ℝ).1 (b : Amb n ℓ × ℝ).2) := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            obtain ⟨hb0, -, hbm⟩ := (hu k).2.2.1 b b.2
            calc ediam (closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (8 * (b : Amb n ℓ × ℝ).2) ^ (n : ℝ) := by
                  gcongr
                  exact ediam_le_of_forall_dist_le fun y hy z hz => by
                    have h1 := dist_triangle_right y z (b : Amb n ℓ × ℝ).1
                    rw [mem_closedBall] at hy hz
                    linarith
              _ = K * (ENNReal.ofReal t *
                    ENNReal.ofReal (unitBallVolume n * (b : Amb n ℓ × ℝ).2 ^ n)) := by
                  rw [hK, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul hKnn,
                    ENNReal.rpow_natCast,
                    ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 8 * (b : Amb n ℓ × ℝ).2)]
                  congr 1
                  field_simp
                  ring
              _ ≤ K * ν.restrict (A \ C) (closedBall (b : Amb n ℓ × ℝ).1 (b : Amb n ℓ × ℝ).2) := by
                  gcongr
        _ = K * ν.restrict (A \ C) (⋃ b ∈ u k, closedBall b.1 b.2) := by
            rw [ENNReal.tsum_mul_left,
              measure_biUnion (hu k).1 (hu k).2.1 fun b _ => measurableSet_closedBall]
        _ ≤ K * ν (A \ C) := by
            refine mul_le_mul_right ?_ K
            exact (measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ _)
    -- Letting `ν (A \ C) → 0`.
    have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
    refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_) bot_le
    obtain ⟨ε, hε0, hεc⟩ := ENNReal.exists_nnreal_pos_mul_lt hKtop hc.ne'
    obtain ⟨C, hCA, hC, hCε⟩ := hreg ε (by exact_mod_cast hε0.ne')
    calc μH[(n : ℝ)] S ≤ K * ν (A \ C) := hcomp C hCA hC
      _ ≤ K * ε := by gcongr
      _ = ε * K := mul_comm _ _
      _ ≤ c := hεc.le
  -- The levels `t = 1/(k+1)` exhaust the positive upper densities.
  have hE : μH[(n : ℝ)] {x : Amb n ℓ | x ∉ A ∧ limsup (fun r : ℝ => ν (A ∩ closedBall x r) /
      ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) ≠ 0} = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null fun k : ℕ => hlevel (1 / ((k : ℝ) + 1)) (by positivity))
    obtain ⟨s, -, hs0, hs⟩ := ENNReal.lt_iff_exists_real_btwn.1 (pos_iff_ne_zero.2 hx.2)
    have hs0' : 0 < s := ENNReal.ofReal_pos.1 hs0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hs0'
    exact mem_iUnion.2 ⟨k, hx.1, ((ENNReal.ofReal_lt_ofReal_iff hs0').2 hk).trans hs⟩
  -- `μHE[n]` is a scalar multiple of `μH[n]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hE, smul_zero]

set_option maxHeartbeats 10000000 in
open scoped CompactlySupported in
/-- **Simon Ch. 3, 1.6–1.9 and Rem. 1.8** for a rectifiable varifold `V = v(M, θ)`: the weighted
approximate tangent plane exists `μ_V`-a.e., `V.tangentProj` is `μ_V`-a.e. strongly measurable, and
`Θⁿ(μ_V, x) = θ(x)` `μ_V`-a.e.  Proof: up to an `Hⁿ`-null set, `M` is covered by the compact Lusin
pieces `K` of `θ` and by images `S = F(A)` of bounded Borel pieces `A` of the parameter domains of
the Lipschitz charts on which `F` approximates an injective linear map (Federer's partition), so `F`
is bi-Lipschitz on `A`.  The area formula `Hⁿ ⌞ F(A) = F_#(J_F 𝓛ⁿ ⌞ A)` and the Lebesgue point
property of `1_A J_F` give the blow-up of `Hⁿ ⌞ S` at `F(a)` (limit `Hⁿ ⌞ DF(a)(ℝⁿ)`); the upper
density theorem for `μ_V ⌞ (M \ K)`, `Hⁿ ⌞ (K \ S)`, `Hⁿ ⌞ (S \ K)` and the continuity of `θ` on
`K` then give the weighted tangent plane.  Squeezing with cutoffs gives the density, and
`p_{range L} = L (L* L)⁻¹ L*` composed with a Borel inverse of `F` on `A` gives measurability. -/
theorem allard52_tangent_ae : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ V : RectifiableVarifold n ℓ U, AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) := by
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
  have weighted_tangent_at : ∀ (Kset : Set (Amb n ℓ)) (hKc : IsCompact Kset) (hKM : Kset ⊆ V.carrier) (hKcont : ContinuousOn V.mult Kset) (hKfin : (μHE[n] : Measure (Amb n ℓ)) Kset < ⊤) (S : Set (Amb n ℓ)) (hSm : MeasurableSet S) (x : Amb n ℓ) (hxK : x ∈ Kset) (P : Submodule ℝ (Amb n ℓ)) (hP : Module.finrank ℝ P = n) (hblow : ∀ f : Amb n ℓ → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ))))) (C : ℝ) (hC : 0 ≤ C) (hSball : ∀ r : ℝ, 0 < r → (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall x r) ≤ ENNReal.ofReal (C * r ^ n)) (hG3 : Tendsto (fun r : ℝ => V.weight (closedBall x r \ Kset) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) (hG4 : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((Kset \ S) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) (hG5 : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((S \ Kset) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
    intro Kset hKc hKM hKcont hKfin S hSm x hxK P hP hblow C hC hSball hG3 hG4 hG5
    have hrsod := Submission.rsod_blowUp_setIntegral_eq
    set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
    set μ : Measure (Amb n ℓ) := V.weight with hμ
    have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
        Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
    have hKm : MeasurableSet Kset := hKc.isClosed.measurableSet
    -- `∫ g dμ_V = ∫_M g θ dHⁿ`
    have hweight : ∀ g : Amb n ℓ → ℝ, ∫ z, g z ∂μ = ∫ z in V.carrier, g z * V.mult z ∂H := by
      intro g
      rw [hμ, RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
        V.aemeasurable_mult.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z hz).le, smul_eq_mul, mul_comm]
    -- conversion of an `r⁻ⁿ`-density statement to real numbers at scale `R r`
    have hconv : ∀ φ : ℝ → ℝ≥0∞, Tendsto (fun r : ℝ => φ r / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) →
        ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (φ (R * r)).toReal) (𝓝[>] 0) (𝓝 0) := by
      intro φ hφ R hR
      have hRt : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · simpa only [mul_zero, id_eq] using
            ((tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul R)
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hR hr
      have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hφ.comp hRt)).const_mul (R ^ n)
      rw [ENNReal.toReal_zero, mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      simp only [Function.comp_apply, ENNReal.toReal_div]
      rw [ENNReal.toReal_ofReal (pow_nonneg (mul_pos hR hr').le n), mul_pow]
      field_simp
    refine ⟨hP, fun f => ?_⟩
    -- data about the test function
    obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
    obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hyt
      have h1 := hR₀ hyt
      rw [mem_closedBall, dist_zero_right] at h1
      linarith [le_max_left R₀ 1]
    set g : ℝ → Amb n ℓ → ℝ := fun r z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) with hg
    have hg0 : ∀ r : ℝ, 0 < r → ∀ z, z ∉ closedBall x (R * r) → g r z = 0 := by
      intro r hr z hz
      apply hR
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
      linarith
    have hgc : ∀ r : ℝ, Continuous (g r) := fun r => by
      simp only [hg, hη]
      exact f.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
    have hgb : ∀ r z, ‖g r z‖ ≤ Cf := fun r z => hCf _
    -- `‖∫_T g_r dν‖ ≤ C_f ν(B_{Rr}(x) ∩ T)`
    have hsetbound : ∀ (ν : Measure (Amb n ℓ)) (T : Set (Amb n ℓ)) (r : ℝ), 0 < r →
        ν (closedBall x (R * r) ∩ T) < ⊤ →
        ‖∫ z in T, g r z ∂ν‖ ≤ Cf * (ν (closedBall x (R * r) ∩ T)).toReal := by
      intro ν T r hr hfin
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν.restrict T) (hg0 r hr),
        Measure.restrict_restrict measurableSet_closedBall]
      have : IsFiniteMeasure (ν.restrict (closedBall x (R * r) ∩ T)) :=
        isFiniteMeasure_restrict.2 hfin.ne
      refine (MeasureTheory.norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun z => hgb r z)).trans_eq ?_
      rw [measureReal_def, Measure.restrict_apply_univ]
    -- a compact neighbourhood of `K` inside `U`
    obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hKc.exists_cthickening_subset_open hU (hKM.trans V.carrier_subset)
    have hLc : IsCompact (cthickening δ₀ Kset) := hKc.cthickening
    have hμL : μ (cthickening δ₀ Kset) < ⊤ := by
      calc μ (cthickening δ₀ Kset)
          = ∫⁻ z in cthickening δ₀ Kset, ENNReal.ofReal (V.mult z) ∂(H.restrict V.carrier) := by
            rw [hμ, RectifiableVarifold.weight, withDensity_apply _ isClosed_cthickening.measurableSet]
        _ = ∫⁻ z in V.carrier ∩ cthickening δ₀ Kset, ENNReal.ofReal (V.mult z) ∂H := by
            rw [Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        _ < ⊤ := (V.integrableOn_mult _ hLc hδ₀U).lintegral_lt_top
    have hBL : ∀ r : ℝ, R * r < δ₀ → closedBall x (R * r) ⊆ cthickening δ₀ Kset :=
      fun r h => (closedBall_subset_closedBall h.le).trans (closedBall_subset_cthickening hxK δ₀)
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ R * r < δ₀ := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / R by positivity)] with r hr
      exact ⟨hr.1, by have := hr.2; rw [lt_div_iff₀ hR0] at this; linarith⟩
    -- `μ_V` on `K` is `θ Hⁿ`
    have hKweight : ∀ φ : Amb n ℓ → ℝ, ∫ z in Kset, φ z ∂μ = ∫ z in Kset, φ z * V.mult z ∂H := by
      intro φ
      have hres : μ.restrict Kset = (H.restrict Kset).withDensity (fun z => ENNReal.ofReal (V.mult z)) := by
        rw [hμ, RectifiableVarifold.weight, restrict_withDensity hKm, Measure.restrict_restrict hKm,
          inter_eq_left.2 hKM]
      rw [hres, integral_withDensity_eq_integral_toReal_smul₀
        ((V.aemeasurable_mult.mono_measure (Measure.restrict_mono hKM le_rfl)).ennreal_ofReal)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hKm] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z (hKM hz)).le, smul_eq_mul, mul_comm]
    have hθK : IntegrableOn V.mult Kset H := by
      have := V.integrableOn_mult Kset hKc (hKM.trans V.carrier_subset)
      rwa [inter_eq_right.2 hKM] at this
    have hgK : ∀ r, IntegrableOn (g r) Kset H := fun r =>
      Measure.integrableOn_of_bounded hKfin.ne (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)
    have hgθK : ∀ r, IntegrableOn (fun z => g r z * V.mult z) Kset H := fun r =>
      hθK.bdd_mul (hgc r).aestronglyMeasurable (Eventually.of_forall fun z => hgb r z)
    have hθx : 0 ≤ V.mult x := (V.mult_pos x (hKM hxK)).le
    have hμB : ∀ r : ℝ, R * r < δ₀ → μ (closedBall x (R * r)) < ⊤ := fun r h =>
      (measure_mono (hBL r h)).trans_lt hμL
    have hSB : ∀ r : ℝ, 0 < r → H (closedBall x (R * r) ∩ S) < ⊤ := fun r hr => by
      rw [inter_comm]
      exact (hSball (R * r) (mul_pos hR0 hr)).trans_lt ENNReal.ofReal_lt_top
    -- integrability of `g_r` for `μ` and on `S`
    have hgμ : ∀ r : ℝ, 0 < r → R * r < δ₀ → Integrable (g r) μ := fun r hr h =>
      (Measure.integrableOn_of_bounded (hμB r h).ne (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)).integrable_of_forall_notMem_eq_zero (hg0 r hr)
    have hgS : ∀ r : ℝ, 0 < r → IntegrableOn (g r) S H := fun r hr => by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall x (R * r)) ?_ (hg0 r hr)
      refine Measure.integrableOn_of_bounded ?_ (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)
      rw [Measure.restrict_apply measurableSet_closedBall]
      exact (hSB r hr).ne
    -- the decomposition
    set E1 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * ∫ z in Ksetᶜ, g r z ∂μ with hE1def
    set E2 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ z in Kset, g r z * V.mult z ∂H -
      V.mult x * ∫ z in Kset, g r z ∂H) with hE2def
    set E3 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ z in Kset, g r z ∂H - ∫ z in S, g r z ∂H) with hE3def
    set E4 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * ∫ z in S, g r z ∂H with hE4def
    have hident : ∀ᶠ r in 𝓝[>] (0 : ℝ), E1 r + E2 r + V.mult x * E3 r + V.mult x * E4 r =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, f y * V.mult (x + r • y) ∂H := by
      filter_upwards [hev] with r hr
      rw [hrsod n ℓ V.carrier f V.mult x r hr.1]
      have h1 : ∫ z in V.carrier, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂H =
          ∫ z in Kset, g r z ∂μ + ∫ z in Ksetᶜ, g r z ∂μ := by
        rw [integral_add_compl hKm (hgμ r hr.1 hr.2), hweight]
      rw [h1, hKweight]
      simp only [hE1def, hE2def, hE3def, hE4def]
      ring
    -- the limits of the four pieces
    have hE1 : Tendsto E1 (𝓝[>] 0) (𝓝 0) := by
      have hlim := (hconv (fun r => μ (closedBall x r \ Kset)) hG3 R hR0).const_mul Cf
      rw [mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [hev] with r hr
      rw [hE1def]
      beta_reduce
      rw [norm_mul, Real.norm_of_nonneg (inv_pos.2 (pow_pos hr.1 n)).le]
      have hb := hsetbound μ Ksetᶜ r hr.1 ((measure_mono inter_subset_left).trans_lt (hμB r hr.2))
      rw [← sdiff_eq] at hb
      calc (r ^ n)⁻¹ * ‖∫ z in Ksetᶜ, g r z ∂μ‖
          ≤ (r ^ n)⁻¹ * (Cf * (μ (closedBall x (R * r) \ Kset)).toReal) :=
            mul_le_mul_of_nonneg_left hb (inv_pos.2 (pow_pos hr.1 n)).le
        _ = Cf * ((r ^ n)⁻¹ * (μ (closedBall x (R * r) \ Kset)).toReal) := by ring
    have hG4' := hconv (fun r => H ((Kset \ S) ∩ closedBall x r)) hG4 R hR0
    have hG5' := hconv (fun r => H ((S \ Kset) ∩ closedBall x r)) hG5 R hR0
    have hE3 : Tendsto E3 (𝓝[>] 0) (𝓝 0) := by
      have hlim := (hG4'.add hG5').const_mul Cf
      rw [add_zero, mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [hev] with r hr
      have hsplit : ∫ z in Kset, g r z ∂H - ∫ z in S, g r z ∂H =
          ∫ z in Kset \ S, g r z ∂H - ∫ z in S \ Kset, g r z ∂H := by
        rw [← integral_inter_add_sdiff hSm (hgK r), ← integral_inter_add_sdiff hKm (hgS r hr.1),
          inter_comm S Kset]
        ring
      have hb1 := hsetbound H (Kset \ S) r hr.1
        ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt hKfin)
      have hb2 := hsetbound H (S \ Kset) r hr.1
        ((measure_mono (inter_subset_inter_right _ sdiff_subset)).trans_lt (hSB r hr.1))
      rw [inter_comm] at hb1 hb2
      rw [hE3def]
      beta_reduce
      rw [hsplit, norm_mul, Real.norm_of_nonneg (inv_pos.2 (pow_pos hr.1 n)).le]
      calc (r ^ n)⁻¹ * ‖∫ z in Kset \ S, g r z ∂H - ∫ z in S \ Kset, g r z ∂H‖
          ≤ (r ^ n)⁻¹ * (Cf * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal +
              Cf * (H ((S \ Kset) ∩ closedBall x (R * r))).toReal) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hb1 hb2))
              (inv_pos.2 (pow_pos hr.1 n)).le
        _ = Cf * ((r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal +
              (r ^ n)⁻¹ * (H ((S \ Kset) ∩ closedBall x (R * r))).toReal) := by ring
    have hE2 : Tendsto E2 (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      set M₀ : ℝ := 1 + C * R ^ n with hM₀
      have hM₀pos : 0 < M₀ := by
        have := mul_nonneg hC (pow_nonneg hR0.le n); rw [hM₀]; linarith
      set ε' : ℝ := ε / (2 * (Cf + 1) * M₀) with hε'
      have hε'0 : 0 < ε' := by positivity
      obtain ⟨δθ, hδθ, hθδ⟩ := Metric.continuousWithinAt_iff.1 (hKcont x hxK) ε' hε'0
      have hG4ev := (Metric.tendsto_nhds.1 hG4') 1 one_pos
      filter_upwards [hev, hG4ev, Ioo_mem_nhdsGT (show (0 : ℝ) < δθ / R by positivity)]
        with r hr hr4 hr5
      have hrn : 0 < r ^ n := pow_pos hr.1 n
      have hRr : R * r < δθ := by have := hr5.2; rw [lt_div_iff₀ hR0] at this; linarith
      rw [Real.dist_eq, sub_zero] at hr4 ⊢
      -- pointwise bound on `K`
      have hpt : ∀ᵐ z ∂H.restrict Kset, ‖g r z * V.mult z - V.mult x * g r z‖ ≤
          (closedBall x (R * r)).indicator (fun _ => Cf * ε') z := by
        filter_upwards [ae_restrict_mem hKm] with z hz
        by_cases hzB : z ∈ closedBall x (R * r)
        · rw [Set.indicator_of_mem hzB]
          have hd : dist (V.mult z) (V.mult x) < ε' := hθδ hz (lt_of_le_of_lt hzB hRr)
          rw [Real.dist_eq] at hd
          calc ‖g r z * V.mult z - V.mult x * g r z‖ = ‖g r z‖ * |V.mult z - V.mult x| := by
                rw [show g r z * V.mult z - V.mult x * g r z = g r z * (V.mult z - V.mult x) by ring,
                  norm_mul, Real.norm_eq_abs (V.mult z - V.mult x)]
            _ ≤ Cf * ε' := mul_le_mul (hgb r z) hd.le (abs_nonneg _) hCf0
        · rw [Set.indicator_of_notMem hzB, hg0 r hr.1 z hzB]
          simp
      have hKBfin : H (closedBall x (R * r) ∩ Kset) < ⊤ :=
        (measure_mono inter_subset_right).trans_lt hKfin
      have hint_ind : Integrable ((closedBall x (R * r)).indicator (fun _ => Cf * ε')) (H.restrict Kset) := by
        rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall]
        exact hKBfin.ne
      have hI := norm_integral_le_of_norm_le hint_ind hpt
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
        measureReal_def, Measure.restrict_apply measurableSet_closedBall] at hI
      have hdiffK : ∫ z in Kset, g r z * V.mult z ∂H - V.mult x * ∫ z in Kset, g r z ∂H =
          ∫ z in Kset, (g r z * V.mult z - V.mult x * g r z) ∂H := by
        rw [integral_sub (hgθK r) ((hgK r).const_mul _), integral_const_mul]
      -- mass of `K` in the ball
      have hKB : (H (closedBall x (R * r) ∩ Kset)).toReal ≤
          (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n := by
        have h1 : H (closedBall x (R * r) ∩ Kset) ≤
            H ((Kset \ S) ∩ closedBall x (R * r)) + H (S ∩ closedBall x (R * r)) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro z hz
          by_cases hzS : z ∈ S
          · exact Or.inr ⟨hzS, hz.1⟩
          · exact Or.inl ⟨⟨hz.2, hzS⟩, hz.1⟩
        have h2 := hSball (R * r) (mul_pos hR0 hr.1)
        have hfin1 : H ((Kset \ S) ∩ closedBall x (R * r)) ≠ ⊤ :=
          ((measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt hKfin).ne
        calc (H (closedBall x (R * r) ∩ Kset)).toReal
            ≤ (H ((Kset \ S) ∩ closedBall x (R * r)) + H (S ∩ closedBall x (R * r))).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1,
                (h2.trans_lt ENNReal.ofReal_lt_top).ne⟩) h1
          _ = (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + (H (S ∩ closedBall x (R * r))).toReal :=
              ENNReal.toReal_add hfin1 (h2.trans_lt ENNReal.ofReal_lt_top).ne
          _ ≤ (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n := by
              gcongr
              exact ENNReal.toReal_le_of_le_ofReal
                (mul_nonneg hC (pow_nonneg (mul_pos hR0 hr.1).le n)) h2
      have hX : (r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal < 1 :=
        (le_abs_self _).trans_lt hr4
      rw [hE2def]
      beta_reduce
      rw [hdiffK, abs_mul, abs_of_pos (inv_pos.2 hrn)]
      calc (r ^ n)⁻¹ * |∫ z in Kset, (g r z * V.mult z - V.mult x * g r z) ∂H|
          ≤ (r ^ n)⁻¹ * ((H (closedBall x (R * r) ∩ Kset)).toReal * (Cf * ε')) :=
            mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hI) (inv_pos.2 hrn).le
        _ = Cf * ε' * ((r ^ n)⁻¹ * (H (closedBall x (R * r) ∩ Kset)).toReal) := by ring
        _ ≤ Cf * ε' * ((r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * R ^ n) := by
            gcongr
            calc (r ^ n)⁻¹ * (H (closedBall x (R * r) ∩ Kset)).toReal
                ≤ (r ^ n)⁻¹ * ((H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n) :=
                  mul_le_mul_of_nonneg_left hKB (inv_pos.2 hrn).le
              _ = (r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * R ^ n := by
                  rw [mul_pow]; field_simp
        _ ≤ Cf * ε' * M₀ := by
            gcongr
            rw [hM₀]; linarith
        _ < ε := by
            rw [hε']
            rw [show Cf * (ε / (2 * (Cf + 1) * M₀)) * M₀ = ε * (Cf / (2 * (Cf + 1))) by
              field_simp]
            have : Cf / (2 * (Cf + 1)) < 1 := by
              rw [div_lt_one (by positivity)]; linarith
            nlinarith
    have hE4 : Tendsto E4 (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), f y ∂H)) :=
      hblow f f.continuous f.hasCompactSupport
    have hlim := ((hE1.add hE2).add (hE3.const_mul (V.mult x))).add (hE4.const_mul (V.mult x))
    have h0 : (0 : ℝ) + 0 + V.mult x * 0 + V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂H =
        V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂H := by ring
    rw [h0] at hlim
    exact hlim.congr' hident
  have plane_ball : ∀ (P : Submodule ℝ (Amb n ℓ)) (hP : Module.finrank ℝ P = n) (t : ℝ) (ht : 0 ≤ t),
      ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) (closedBall 0 t) = ENNReal.ofReal (unitBallVolume n * t ^ n) := by
    intro P hP t ht
    have : Nontrivial P := Module.nontrivial_of_finrank_pos (by rw [hP]; omega)
    have hrange : range (P.subtypeₗᵢ : P → Amb n ℓ) = (P : Set (Amb n ℓ)) := by ext x; simp
    rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
    have hpre : (P.subtypeₗᵢ : P → Amb n ℓ) ⁻¹' closedBall (0 : Amb n ℓ) t = closedBall (0 : P) t := by
      ext x
      simp [mem_closedBall, dist_eq_norm]
    have hHP : (μHE[n] : Measure P) = volume := by
      have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P)
      rwa [hP] at this
    rw [hpre, hHP, InnerProductSpace.volume_closedBall, hP, ← ENNReal.ofReal_pow ht,
      ← ENNReal.ofReal_mul (pow_nonneg ht _)]
    congr 1
    rw [unitBallVolume, mul_comm]
    congr 2
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  have cutoff_exists : ∀ (a b : ℝ) (ha : 0 < a) (hab : a < b),
      ∃ c : C_c(Amb n ℓ, ℝ), (∀ y, 0 ≤ c y ∧ c y ≤ 1) ∧ (∀ y, ‖y‖ ≤ a → c y = 1) ∧ (∀ y, b ≤ ‖y‖ → c y = 0) := by
    intro a b ha hab
    have hba : 0 < b - a := sub_pos.2 hab
    refine ⟨⟨⟨fun y => min 1 (max 0 ((b - ‖y‖) / (b - a))), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall (0 : Amb n ℓ) b) fun y hy => ?_⟩, ?_, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, not_le] at hy
      have : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      simp [max_eq_left this]
    · intro y
      exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · intro y hy
      have : 1 ≤ (b - ‖y‖) / (b - a) := by rw [le_div_iff₀ hba]; linarith
      show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 1
      rw [max_eq_right (by linarith), min_eq_left this]
    · intro y hy
      have : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 0
      rw [max_eq_left this, min_eq_right zero_le_one]
  have density_of_tangent : ∀ (x : Amb n ℓ) (hxM : x ∈ V.carrier) (P : Submodule ℝ (Amb n ℓ)) (hP : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P),
      V.HasDensity x (V.mult x) := by
    intro x hxM P hP
    have hrsod := Submission.rsod_blowUp_setIntegral_eq
    set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
    set μ : Measure (Amb n ℓ) := V.weight with hμ
    have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
        Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
    have hweight : ∀ g : Amb n ℓ → ℝ, ∫ z, g z ∂μ = ∫ z in V.carrier, g z * V.mult z ∂H := by
      intro g
      rw [hμ, RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
        V.aemeasurable_mult.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z hz).le, smul_eq_mul, mul_comm]
    set ω : ℝ := unitBallVolume n with hωdef
    have hω : 0 < ω :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    set θx : ℝ := V.mult x with hθxdef
    have hθx : 0 < θx := V.mult_pos x hxM
    have hPn : Module.finrank ℝ P = n := hP.1
    -- local finiteness of `μ_V` near `x`
    obtain ⟨δ₀, hδ₀, hδ₀U⟩ : ∃ δ > 0, closedBall x δ ⊆ U :=
      nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (V.carrier_subset hxM))
    have hμfin : ∀ t : ℝ, t ≤ δ₀ → μ (closedBall x t) < ⊤ := by
      intro t ht
      calc μ (closedBall x t) ≤ μ (closedBall x δ₀) := measure_mono (closedBall_subset_closedBall ht)
        _ = ∫⁻ z in closedBall x δ₀, ENNReal.ofReal (V.mult z) ∂(H.restrict V.carrier) := by
            rw [hμ, RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall]
        _ = ∫⁻ z in V.carrier ∩ closedBall x δ₀, ENNReal.ofReal (V.mult z) ∂H := by
            rw [Measure.restrict_restrict measurableSet_closedBall, inter_comm]
        _ < ⊤ := (V.integrableOn_mult _ (isCompact_closedBall x δ₀) hδ₀U).lintegral_lt_top
    -- rescaled cutoff integrals converge
    have hlimc : ∀ c : C_c(Amb n ℓ, ℝ), Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
        ∫ z, c (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂μ) (𝓝[>] 0)
        (𝓝 (θx * ∫ y in (P : Set (Amb n ℓ)), c y ∂H)) := by
      intro c
      refine (hP.2 c).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hrsod n ℓ V.carrier c V.mult x r hr, hweight]
    -- integrability of a cutoff with support in `B_s`
    have hcint : ∀ (c : C_c(Amb n ℓ, ℝ)) (s : ℝ), 0 < s → (∀ y, s ≤ ‖y‖ → c y = 0) →
        (∀ y, 0 ≤ c y ∧ c y ≤ 1) → ∀ r : ℝ, 0 < r → s * r ≤ δ₀ →
        Integrable (fun z => c (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) μ := by
      intro c s hs hcs hc01 r hr hsr
      refine (Measure.integrableOn_of_bounded (s := closedBall x (s * r)) (hμfin _ hsr).ne
        (by simp only [hη]; fun_prop : Continuous fun z =>
          c (Poincare.SimonGMT.Chapter03.blowUpMap x r z)).aestronglyMeasurable
        (M := 1) (Eventually.of_forall fun z => ?_)).integrable_of_forall_notMem_eq_zero ?_
      · rw [Real.norm_of_nonneg (hc01 _).1]; exact (hc01 _).2
      · intro z hz
        apply hcs
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, le_div_iff₀ hr]
        exact hz.le
    -- integrability of cutoffs on the plane
    have hPint : ∀ (c : C_c(Amb n ℓ, ℝ)) (s : ℝ), 0 < s → (∀ y, s ≤ ‖y‖ → c y = 0) →
        (∀ y, 0 ≤ c y ∧ c y ≤ 1) → Integrable c (H.restrict (P : Set (Amb n ℓ))) := by
      intro c s hs hcs hc01
      refine (Measure.integrableOn_of_bounded (s := closedBall (0 : Amb n ℓ) s)
        (by rw [plane_ball P hPn s hs.le]; exact ENNReal.ofReal_ne_top)
        c.continuous.aestronglyMeasurable (M := 1)
        (Eventually.of_forall fun y => ?_)).integrable_of_forall_notMem_eq_zero ?_
      · exact (show ‖c y‖ ≤ 1 by rw [Real.norm_of_nonneg (hc01 y).1]; exact (hc01 y).2)
      · intro y hy
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hcs y hy.le
    have hPreal : ∀ t : ℝ, 0 ≤ t → (H.restrict (P : Set (Amb n ℓ))).real (closedBall 0 t) = ω * t ^ n := by
      intro t ht
      rw [measureReal_def, plane_ball P hPn t ht, ENNReal.toReal_ofReal (by positivity)]
    have hindP : ∀ t : ℝ, 0 ≤ t → Integrable ((closedBall (0 : Amb n ℓ) t).indicator (fun _ => (1 : ℝ)))
        (H.restrict (P : Set (Amb n ℓ))) := by
      intro t ht
      rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [plane_ball P hPn t ht]; exact ENNReal.ofReal_ne_top
    have hindμ : ∀ r : ℝ, r ≤ δ₀ → Integrable ((closedBall x r).indicator (fun _ => (1 : ℝ))) μ := by
      intro r hr
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const (hμfin r hr).ne
    have hφ : Tendsto (fun t : ℝ => θx * (ω * t ^ n)) (𝓝 1) (𝓝 (θx * ω)) := by
      have := (((continuous_pow n).tendsto (1 : ℝ)).const_mul ω).const_mul θx
      simpa using this
    have hreal : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * μ.real (closedBall x r)) (𝓝[>] 0)
        (𝓝 (θx * ω)) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        obtain ⟨t, ht1, ht2⟩ : ∃ t, t ∈ Ioo (1 / 2 : ℝ) 1 ∧ a < θx * (ω * t ^ n) :=
          ((show ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (1 / 2 : ℝ) 1 from
            Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)).and
            ((hφ.eventually (lt_mem_nhds ha)).filter_mono nhdsWithin_le_nhds)).exists
        have ht0 : 0 < t := by linarith [ht1.1]
        obtain ⟨c, hc01, hc1, hc0⟩ := cutoff_exists t 1 ht0 ht1.2
        have hPc : ω * t ^ n ≤ ∫ y in (P : Set (Amb n ℓ)), c y ∂H := by
          rw [← hPreal t ht0.le, ← integral_indicator_one measurableSet_closedBall]
          refine integral_mono (hindP t ht0.le) (hPint c 1 one_pos hc0 hc01) fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Amb n ℓ) t
          · rw [Set.indicator_of_mem hy, Pi.one_apply,
              hc1 y (by rwa [mem_closedBall, dist_zero_right] at hy)]
          · rw [Set.indicator_of_notMem hy]; exact (hc01 y).1
        have hev := (tendsto_order.1 (hlimc c)).1 a
          (lt_of_lt_of_le ht2 (mul_le_mul_of_nonneg_left hPc hθx.le))
        filter_upwards [hev, Ioo_mem_nhdsGT hδ₀] with r hr1 hr2
        refine lt_of_lt_of_le hr1 (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hr2.1.le n)))
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono (hcint c 1 one_pos hc0 hc01 r hr2.1 (by linarith [hr2.2]))
          (hindμ r hr2.2.le) fun z => ?_
        by_cases hz : z ∈ closedBall x r
        · rw [Set.indicator_of_mem hz, Pi.one_apply]; exact (hc01 _).2
        · rw [Set.indicator_of_notMem hz]
          refine (hc0 _ ?_).le
          rw [mem_closedBall, dist_eq_norm, not_le] at hz
          rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr2.1).le, ← div_eq_inv_mul,
            le_div_iff₀ hr2.1, one_mul]
          exact hz.le
      · intro b hb
        obtain ⟨s, hs1, hs2⟩ : ∃ s, s ∈ Ioo (1 : ℝ) 2 ∧ θx * (ω * s ^ n) < b :=
          ((show ∀ᶠ s in 𝓝[>] (1 : ℝ), s ∈ Ioo (1 : ℝ) 2 from
            Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)).and
            ((hφ.eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds)).exists
        have hs0 : 0 < s := by linarith [hs1.1]
        obtain ⟨c, hc01, hc1, hc0⟩ := cutoff_exists 1 s one_pos hs1.1
        have hPc : ∫ y in (P : Set (Amb n ℓ)), c y ∂H ≤ ω * s ^ n := by
          rw [← hPreal s hs0.le, ← integral_indicator_one measurableSet_closedBall]
          refine integral_mono (hPint c s hs0 hc0 hc01) (hindP s hs0.le) fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Amb n ℓ) s
          · rw [Set.indicator_of_mem hy, Pi.one_apply]; exact (hc01 y).2
          · rw [Set.indicator_of_notMem hy]
            refine (hc0 y ?_).le
            rw [mem_closedBall, dist_zero_right, not_le] at hy
            exact hy.le
        have hev := (tendsto_order.1 (hlimc c)).2 b
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hPc hθx.le) hs2)
        filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / 2 by positivity)] with r hr1 hr2
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hr2.1.le n))) hr1
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono (hindμ r (by linarith [hr2.2]))
          (hcint c s hs0 hc0 hc01 r hr2.1 (by nlinarith [hr2.2, hr2.1, hs1.2])) fun z => ?_
        by_cases hz : z ∈ closedBall x r
        · rw [Set.indicator_of_mem hz, Pi.one_apply, hc1]
          rw [mem_closedBall, dist_eq_norm] at hz
          rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr2.1).le, ← div_eq_inv_mul,
            div_le_one hr2.1]
          exact hz
        · rw [Set.indicator_of_notMem hz]; exact (hc01 _).1
    have h2 := hreal.div_const ω
    rw [mul_div_assoc, div_self hω.ne', mul_one] at h2
    refine (ENNReal.tendsto_ofReal h2).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with r hr
    have hfin := hμfin r hr.2.le
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_div_of_pos (mul_pos hω (pow_pos hr.1 n)),
      measureReal_def]
    congr 1
    field_simp
  have Phi_measurable : Measurable (fun L : Rn n →L[ℝ] Amb n ℓ => L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L)) := by
    classical
    have hinv : Measurable (Ring.inverse : (Rn n →L[ℝ] Rn n) → (Rn n →L[ℝ] Rn n)) := by
      have h := ContinuousOn.measurable_piecewise (s := {x : Rn n →L[ℝ] Rn n | IsUnit x})
        (f := Ring.inverse) (g := Ring.inverse)
        (fun x hx => by
          have := NormedRing.inverse_continuousAt (hx : IsUnit x).unit
          rw [IsUnit.unit_spec] at this
          exact this.continuousWithinAt)
        ((continuousOn_const (c := (0 : Rn n →L[ℝ] Rn n))).congr fun x hx =>
          Ring.inverse_non_unit x hx)
        Units.isOpen.measurableSet
      rwa [Set.piecewise_same] at h
    have hadj : Continuous (fun L : Rn n →L[ℝ] Amb n ℓ => ContinuousLinearMap.adjoint L) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Amb n ℓ)).continuous
    have hcomp : Continuous (fun p : (Rn n →L[ℝ] Amb n ℓ) × (Rn n →L[ℝ] Rn n) ×
        (Amb n ℓ →L[ℝ] Rn n) => p.1 ∘L p.2.1 ∘L p.2.2) := by
      exact continuous_fst.clm_comp (continuous_snd.fst.clm_comp continuous_snd.snd)
    have hm : Measurable (fun L : Rn n →L[ℝ] Amb n ℓ =>
        (L, Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L), ContinuousLinearMap.adjoint L)) :=
      measurable_id.prodMk ((hinv.comp (hadj.clm_comp continuous_id).measurable).prodMk
        hadj.measurable)
    exact hcomp.measurable.comp hm
  have Phi_eq : ∀ (L : Rn n →L[ℝ] Amb n ℓ) (hL : Function.Injective L),
      (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ)).starProjection = L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L) := by
    intro L hL
    set G : Rn n →L[ℝ] Rn n := (ContinuousLinearMap.adjoint L) ∘L L with hG
    have hGinj : Function.Injective G := by
      intro c d hcd
      have h1 : G (c - d) = 0 := by rw [map_sub, hcd, sub_self]
      have h2 : inner ℝ (L (c - d)) (L (c - d)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        change inner ℝ (G (c - d)) (c - d) = 0
        rw [h1, inner_zero_left]
      rw [inner_self_eq_zero] at h2
      exact sub_eq_zero.1 (hL (by rw [h2, map_zero]))
    have hGunit : IsUnit G := by
      let e : Rn n ≃L[ℝ] Rn n :=
        (LinearEquiv.ofInjectiveEndo (G : Rn n →ₗ[ℝ] Rn n) hGinj).toContinuousLinearEquiv
      have he : (e : Rn n →L[ℝ] Rn n) = G := by ext c; rfl
      refine ⟨⟨G, (e.symm : Rn n →L[ℝ] Rn n), ?_, ?_⟩, rfl⟩
      · rw [← he]; ext c; simp
      · rw [← he]; ext c; simp
    have hGG : G ∘L Ring.inverse G = 1 := Ring.mul_inverse_cancel G hGunit
    refine ContinuousLinearMap.ext fun u => ?_
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro w ⟨c, rfl⟩
      rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
      have h3 : (ContinuousLinearMap.adjoint L) ((L ∘L Ring.inverse G ∘L
          ContinuousLinearMap.adjoint L) u) = (ContinuousLinearMap.adjoint L) u := by
        have := congrArg (fun T : Rn n →L[ℝ] Rn n => T ((ContinuousLinearMap.adjoint L) u)) hGG
        simpa [hG] using this
      rw [h3, sub_self, inner_zero_left]
  set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
  have hHRn : (μHE[n] : Measure (Rn n)) = volume := by
    have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
    rwa [finrank_euclideanSpace_fin] at this
  -- (UD) in the `r⁻ⁿ` form
  have ud_tendsto : ∀ (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), NullMeasurableSet A ν →
      ν A < ∞ → ∀ᵐ x ∂H, x ∉ A →
        Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
    intro ν A hA hfin
    have h0 := Submission.upperDensity_ne_zero_outside_hausdorff_null ν A hA hfin
    rw [measure_eq_zero_iff_ae_notMem] at h0
    have hω : 0 < unitBallVolume n :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    filter_upwards [h0] with x hx hxA
    have hls : limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) = 0 := by
      by_contra hne
      exact hx ⟨hxA, hne⟩
    have hq : Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hlt : limsup (fun r : ℝ => ν (A ∩ closedBall x r) /
          ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) < ε := by
        rw [hls]; exact hε
      exact (eventually_lt_of_limsup_lt hlt).mono fun r hr => hr.le
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (unitBallVolume n) *
        (ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hq (Or.inr ENNReal.ofReal_ne_top)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ENNReal.ofReal_mul hω.le, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hω).ne' ENNReal.ofReal_ne_top]
  -- `r⁻ⁿ μ_V(B_r(x) \ K) → 0` a.e. on a compact `K ⊆ M`
  have wdoc : ∀ Kset : Set (Amb n ℓ), IsCompact Kset → Kset ⊆ V.carrier →
      ∀ᵐ x ∂H, x ∈ Kset → Tendsto (fun r : ℝ => V.weight (closedBall x r \ Kset) /
        ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
    intro Kset hK hKM
    obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU (hKM.trans V.carrier_subset)
    have hLc : IsCompact (cthickening δ Kset) := hK.cthickening
    set A : Set (Amb n ℓ) := (V.carrier \ Kset) ∩ cthickening δ Kset with hAdef
    have hac : V.weight ≪ H :=
      (withDensity_absolutelyContinuous _ _).trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hA : NullMeasurableSet A V.weight :=
      ((V.nullMeasurableSet_carrier.diff hK.isClosed.measurableSet.nullMeasurableSet).inter
        isClosed_cthickening.measurableSet.nullMeasurableSet).mono_ac hac
    have hAfin : V.weight A < ∞ := by
      calc V.weight A ≤ V.weight (cthickening δ Kset) := measure_mono inter_subset_right
        _ = ∫⁻ x in cthickening δ Kset, ENNReal.ofReal (V.mult x) ∂(H.restrict V.carrier) :=
            withDensity_apply _ isClosed_cthickening.measurableSet
        _ = ∫⁻ x in V.carrier ∩ cthickening δ Kset, ENNReal.ofReal (V.mult x) ∂H := by
            rw [Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        _ < ∞ := (V.integrableOn_mult _ hLc hδU).lintegral_lt_top
    have hMc : V.weight V.carrierᶜ = 0 := by
      have h1 : (H.restrict V.carrier) V.carrierᶜ = 0 :=
        ae_iff.1 (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
      exact withDensity_absolutelyContinuous _ _ h1
    filter_upwards [ud_tendsto V.weight A hA hAfin] with x hx hxK
    have hxA : x ∉ A := fun h => h.1.2 hxK
    refine (hx hxA).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hball : closedBall x r ⊆ cthickening δ Kset :=
      (closedBall_subset_closedBall hr.2.le).trans (closedBall_subset_cthickening hxK δ)
    have hset : A ∩ closedBall x r = (closedBall x r \ Kset) ∩ V.carrier := by
      ext y
      simp only [hAdef, mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨⟨⟨hyM, hyK⟩, _⟩, hyB⟩
        exact ⟨⟨hyB, hyK⟩, hyM⟩
      · rintro ⟨⟨hyB, hyK⟩, hyM⟩
        exact ⟨⟨⟨hyM, hyK⟩, hball hyB⟩, hyB⟩
    rw [hset, measure_inter_conull hMc]
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
  set Φ : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun L =>
    L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L)
    with hΦ
  set T : ℕ → ℕ → ℕ → Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun j k i x =>
    Φ (fderiv ℝ (F j) (G j k i x)) with hTdef
  have hTm : ∀ j k i, Measurable (T j k i) := fun j k i =>
    Phi_measurable.comp ((measurable_fderiv ℝ (F j)).comp (hGm j k i))
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
    filter_upwards [wdoc (Kp m) (hKc m) (hKM m),
      ud_tendsto H (Kp m \ S) ((hKc m).measurableSet.diff hSm).nullMeasurableSet hKS,
      ud_tendsto H (S \ Kp m) (hSm.diff (hKc m).measurableSet).nullMeasurableSet hSK,
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
    -- the density bound for `S`
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
    have hlam0 := hlam j k i
    set C : ℝ := (KF j : ℝ) ^ n * c₁ / lam j k i ^ n with hCdef
    have hC : 0 ≤ C := by positivity
    have hSball : ∀ r : ℝ, 0 < r → H (S ∩ closedBall (F j a) r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro r hr
      have hsub : S ∩ closedBall (F j a) r ⊆ F j '' (A j k i ∩ closedBall a (r / lam j k i)) := by
        rintro _ ⟨⟨b, hb, rfl⟩, hbr⟩
        refine ⟨b, ⟨hb, ?_⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm] at hbr ⊢
        have := hbi j k i b hb a ha
        rw [le_div_iff₀ hlam0, mul_comm]
        linarith
      have hvol1 : volume (closedBall (0 : Rn n) 1) = ENNReal.ofReal c₁ :=
        (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
      have hval : (KF j : ℝ≥0∞) ^ n * (ENNReal.ofReal ((r / lam j k i) ^ n) * ENNReal.ofReal c₁) =
          ENNReal.ofReal (C * r ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_pow (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hCdef, div_pow]
        field_simp
      calc H (S ∩ closedBall (F j a) r) ≤ H (F j '' (A j k i ∩ closedBall a (r / lam j k i))) :=
            measure_mono hsub
        _ ≤ (KF j : ℝ≥0∞) ^ n *
              (μHE[n] : Measure (Rn n)) (A j k i ∩ closedBall a (r / lam j k i)) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hKF j).lipschitzOnWith
        _ ≤ (KF j : ℝ≥0∞) ^ n * volume (closedBall a (r / lam j k i)) := by
            rw [hHRn]; gcongr; exact inter_subset_right
        _ = ENNReal.ofReal (C * r ^ n) := by
            rw [Measure.addHaar_closedBall' volume a (div_pos hr hlam0).le,
              finrank_euclideanSpace_fin, hvol1, hval]
    have hW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
        (F j a) P := by
      refine weighted_tangent_at (Kp m) (hKc m) (hKM m) (hKcont m) (hKfin m) S hSm (F j a)
        hxK P hPn (fun f hfc hfs => ?_) C hC hSball (hx3 hxK)
        (hx4 fun h => h.2 ⟨a, ha, rfl⟩) (hx5 fun h => h.2 hxK)
      rw [hPset]
      exact blowup_area_tendsto (F j) (hKF j) (A j k i) (hAm j k i) hlam0 (hbi j k i) hgint ha
        (hAreg j k i a ha).1 hLinj hLeb f hfc hfs
    refine ⟨⟨P, hW⟩, ?_⟩
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (F j a) P := ⟨P, hW⟩
    have huniq : Classical.choose hex = P :=
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
        (V.mult_pos _ (hKM m hxK)).ne' (Classical.choose_spec hex) hW
    have hkey : ∀ Q : Submodule ℝ (Amb n ℓ), Q = P → Q.starProjection = P.starProjection := by
      rintro Q rfl; rfl
    rw [RectifiableVarifold.tangentProj, dif_pos hex, hkey _ huniq]
    refine (Phi_eq L hLinj).trans ?_
    simp only [hTdef, hΦ, hGa j k i a ha, hL]
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
      push_neg at h
      exact hx (Or.inl (Or.inl ⟨hxM, by simpa using h⟩))
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
  have hmem : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    hac.ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  refine ⟨?_, ?_, ?_⟩
  · -- (i) measurability
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
  · -- (ii) tangent planes
    filter_upwards [hallμ] with x hx
    obtain ⟨m, j, k, i, -, hex, -⟩ := hx
    refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
    rw [RectifiableVarifold.tangentProj, dif_pos hex]
  · -- (iii) density
    filter_upwards [hallμ, hmem] with x hx hxM
    obtain ⟨m, j, k, i, -, ⟨P, hP⟩, -⟩ := hx
    exact density_of_tangent x hxM P hP
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), in the `L¹` form used for Theorem 5.2: if
`dist(x − z, T) ≤ h` for `x ∈ spt V ∩ B_r(z)`, then
`∫_{B_{r/2}(z)} |p_{T_x M} − p_T|² dμ_V
   ≤ C r⁻² ∫_{B_r(z)} dist(x − z, T)² dμ_V + C h ∫_{B_r(z)} |H| dμ_V`
with `C = 144`.  Test the first variation with `X = ζ² p_{T⊥}(x − z)`, `ζ(x) = φ(|x − z|/r)`;
tangent planes exist `μ_V`-a.e. by `allard52_tangent_ae` (Ch. 3, 1.9). -/
theorem allard52_tilt_height_l1 : ∀ (n ℓ : ℕ), 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → 0 ≤ h → closedBall z r ⊆ U → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ C * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + C * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
  intro n ℓ hn
  refine ⟨144, by norm_num, ?_⟩
  intro U hU V H hH z r h hr hh hBU T hT hheight
  -- (T) a.e. tangent planes and measurability of `x ↦ p_x` (sibling `allard52_tangent_ae`).
  obtain ⟨hmeas, hae, -⟩ := Submission.allard52_tangent_ae n ℓ hn U hU V
  -- Step 1: the cutoff `ζ(x) = φ(|x - z|/r)` with `φ` the accepted 3-Lipschitz step profile.
  obtain ⟨φ, hφs, hφ01, hφ1, hφ0, hφL⟩ := exists_smooth_step_profile_lipschitz_three
  obtain ⟨ζ, hζs, hζ01, hζ1, hζ0, hζd⟩ : ∃ ζ : Amb n ℓ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall z (r / 2), ζ x = 1) ∧
      (∀ x, r ≤ dist x z → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := by
    refine ⟨fun x => φ (‖x - z‖ / r),
      contDiff_radial_profile_of_eq_one_le_half (n + ℓ) z r φ hr hφs hφ1,
      fun x => hφ01 _, fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · apply hφ1
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [div_le_iff₀ hr]
      linarith
    · apply hφ0
      rw [dist_eq_norm] at hx
      rw [le_div_iff₀ hr]
      linarith
    · have h3 := norm_fderiv_radial_profile_le_of_lipschitzWith (n + ℓ) z r 3 φ hr hφL x
      simpa using h3
  have hζC1 : ContDiff ℝ 1 ζ := hζs.of_le (by exact_mod_cast le_top)
  -- (F2) finite weight on compact subsets of `U`, and `μ`-a.e. point lies in `spt V`.
  have hfin : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → V.weight K < ⊤ := by
    intro K hK hKU
    have hint := V.integrableOn_mult K hK hKU
    rw [RectifiableVarifold.weight, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    exact hint.lintegral_lt_top
  have hsupp : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have hUc : V.weight Uᶜ = 0 := by
      rw [RectifiableVarifold.weight, withDensity_apply _ hU.isClosed_compl.measurableSet,
        Measure.restrict_restrict hU.isClosed_compl.measurableSet]
      have hempty : Uᶜ ∩ V.carrier = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun hxU hxM => hxU (V.carrier_subset hxM)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    have h1 : ∀ᵐ x ∂V.weight, x ∈ U := by
      rw [ae_iff]
      simpa [compl_def] using hUc
    filter_upwards [h1, Measure.support_mem_ae (μ := V.weight)] with x hx1 hx2
    show x ∈ U ∩ V.weight.support
    exact ⟨hx1, hx2⟩
  have hopHS : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, ‖A‖ ≤ hsNorm A := fun A =>
    hsNorm_starProjection_trace_identities.1 (n + ℓ) (n + ℓ) A
  have hperp : ∀ v : Amb n ℓ, ‖Tᗮ.starProjection v‖ = infDist v (T : Set (Amb n ℓ)) :=
    fun v => hsNorm_starProjection_trace_identities.2.1 (n + ℓ) T v
  -- Step 3: `div_M X = ζ² |p_P - p_T|²/2 + 2ζ ∇ζ · (p_P - p_T) x'` where `p_x = p_P`, `dim P = n`.
  have hdivpt : ∀ (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ P = n →
      V.tangentProj x = P.starProjection →
      V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z)) x =
        ζ x ^ 2 * (hsNormSq (V.tangentProj x - T.starProjection) / 2) +
          2 * ζ x * fderiv ℝ ζ x
            ((V.tangentProj x - T.starProjection) (Tᗮ.starProjection (x - z))) := by
    intro x P hP hV
    have hζx : DifferentiableAt ℝ ζ x := hζC1.differentiable one_ne_zero x
    have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
      simpa using hζx.hasFDerivAt.pow 2
    have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - z)) Tᗮ.starProjection x :=
      (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have hX := hsq.fun_smul hlin
    have hx' : T.starProjection (Tᗮ.starProjection (x - z)) = 0 :=
      (T.starProjection_apply_eq_zero_iff).mpr (Tᗮ.starProjection_apply_mem _)
    have htr : LinearMap.trace ℝ (Amb n ℓ)
        (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
          hsNormSq (P.starProjection - T.starProjection) / 2 :=
      hsNorm_starProjection_trace_identities.2.2 (n + ℓ) P T (hP.trans hT.symm)
    have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - z))).toLinearMap ∘ₗ
        P.starProjection.toLinearMap =
          (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
            (Tᗮ.starProjection (x - z)) := by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
    rw [RectifiableVarifold.divM, hX.fderiv, hV, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
      map_smul, htr, LinearMap.trace_smulRight]
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      smul_apply, smul_eq_mul, sub_apply, hx', sub_zero]
  -- Notation: `g = |p_x - p_T|²`, `w = x' = p_{T⊥}(x - z)`, the drift term `b`, the field `X`.
  obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ, ∀ x, g x = hsNormSq (V.tangentProj x - T.starProjection) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → Amb n ℓ, ∀ x, w x = Tᗮ.starProjection (x - z) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Amb n ℓ → ℝ,
      ∀ x, b x = 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, ∀ x, X x = ζ x ^ 2 • w x := ⟨_, fun _ => rfl⟩
  have hζcont : Continuous ζ := hζC1.continuous
  have hDζcont : Continuous (fderiv ℝ ζ) := hζC1.continuous_fderiv one_ne_zero
  have hwcont : Continuous w := by
    rw [show w = fun x => Tᗮ.starProjection (x - z) from funext hw]
    fun_prop
  have hXcont : Continuous X := by
    rw [show X = fun x => ζ x ^ 2 • w x from funext hX]
    exact (hζcont.pow 2).smul hwcont
  have hζout : ∀ x, x ∉ closedBall z r → ζ x = 0 := fun x hx =>
    hζ0 x (not_le.1 fun h' => hx (mem_closedBall.2 h')).le
  have hw_le : ∀ x, ‖w x‖ ≤ ‖x - z‖ := by
    intro x
    rw [hw]
    calc ‖Tᗮ.starProjection (x - z)‖ ≤ ‖Tᗮ.starProjection‖ * ‖x - z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - z‖ := by gcongr; exact Submodule.starProjection_norm_le _
      _ = ‖x - z‖ := one_mul _
  have hwB : ∀ x ∈ closedBall z r, ‖w x‖ ≤ r := fun x hx =>
    (hw_le x).trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hx)
  have hPnorm : ∀ x, ‖V.tangentProj x‖ ≤ 1 := by
    intro x
    unfold RectifiableVarifold.tangentProj
    split_ifs
    · exact Submodule.starProjection_norm_le _
    · simp
  have hA2 : ∀ x, ‖V.tangentProj x - T.starProjection‖ ≤ 2 := fun x =>
    (norm_sub_le _ _).trans (by linarith [hPnorm x, Submodule.starProjection_norm_le T])
  have hhs0 : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, 0 ≤ hsNormSq A := fun A => by
    unfold hsNormSq
    positivity
  have hhs_le : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, hsNormSq A ≤ (n + ℓ : ℕ) * ‖A‖ ^ 2 := by
    intro A
    unfold hsNormSq
    calc ∑ i : Fin (n + ℓ), ‖A (EuclideanSpace.single i 1)‖ ^ 2
        ≤ ∑ _i : Fin (n + ℓ), ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = (n + ℓ : ℕ) * ‖A‖ ^ 2 := by simp
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hg]; exact hhs0 _
  have hgle : ∀ x, g x ≤ (n + ℓ : ℕ) * 4 := fun x => by
    rw [hg]
    refine (hhs_le _).trans ?_
    gcongr
    nlinarith [hA2 x, norm_nonneg (V.tangentProj x - T.starProjection)]
  -- `μ_V(B_r(z)) < ∞`.
  have hμB : V.weight (closedBall z r) < ∞ := hfin _ (isCompact_closedBall z r) hBU
  have : IsFiniteMeasure (V.weight.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.2 hμB.ne
  -- Measurability.
  have hPm : AEStronglyMeasurable (fun x => V.tangentProj x - T.starProjection)
      (V.weight.restrict (closedBall z r)) :=
    hmeas.restrict.sub aestronglyMeasurable_const
  have hgm : AEStronglyMeasurable g (V.weight.restrict (closedBall z r)) := by
    rw [show g = fun x => hsNormSq (V.tangentProj x - T.starProjection) from funext hg]
    have hcont : Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq A := by
      unfold hsNormSq
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).norm).pow 2
    exact hcont.comp_aestronglyMeasurable hPm
  have hbm : AEStronglyMeasurable b (V.weight.restrict (closedBall z r)) := by
    rw [show b = fun x => 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))
      from funext hb]
    have happ : Continuous (Function.uncurry
        fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => A v) :=
      continuous_fst.clm_apply continuous_snd
    have happ' : Continuous (Function.uncurry
        fun (L : Amb n ℓ →L[ℝ] ℝ) (v : Amb n ℓ) => L v) :=
      continuous_fst.clm_apply continuous_snd
    exact (continuous_const.mul hζcont).aestronglyMeasurable.mul
      (happ'.comp_aestronglyMeasurable₂ hDζcont.aestronglyMeasurable
        (happ.comp_aestronglyMeasurable₂ hPm hwcont.aestronglyMeasurable))
  -- Step 4: integrability on `B_r(z)`.
  have hHint : Integrable H (V.weight.restrict (closedBall z r)) :=
    hH.1.integrableOn_compact_subset hBU (isCompact_closedBall z r)
  have hzg : Integrable (fun x => ζ x ^ 2 * g x) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound ((hζcont.pow 2).aestronglyMeasurable.mul hgm) ((n + ℓ : ℕ) * 4)
      (ae_of_all _ fun x => ?_)
    obtain ⟨hz0, hz1⟩ := hζ01 x
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
    calc ζ x ^ 2 * g x ≤ 1 * ((n + ℓ : ℕ) * 4) :=
          mul_le_mul (by nlinarith) (hgle x) (hg0 x) zero_le_one
      _ = (n + ℓ : ℕ) * 4 := one_mul _
  have hbi : Integrable b (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound hbm 12
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hD : ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖ ≤ 3 / r * (2 * r) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hA2 x) (hwB x hx) (norm_nonneg _) zero_le_two)
    rw [hb, norm_mul, norm_mul, Real.norm_of_nonneg hz0, Real.norm_of_nonneg zero_le_two]
    calc 2 * ζ x * ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖
        ≤ 2 * 1 * (3 / r * (2 * r)) := by gcongr
      _ = 12 := by field_simp; norm_num
  have hh2 : Integrable (fun x => ‖w x‖ ^ 2) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound (hwcont.norm.pow 2).aestronglyMeasurable (r ^ 2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwB x hx) 2
  have hXH : Integrable (fun x => inner ℝ (X x) (H x)) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.mono' (hHint.norm.const_mul r)
      (continuous_inner.comp_aestronglyMeasurable
        (hXcont.aestronglyMeasurable.prodMk hHint.aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * r := mul_le_mul hz2 (hwB x hx) (norm_nonneg _) zero_le_one
      _ = r := one_mul _
  -- Step 2: the test field `X = ζ² x'` is admissible.
  have hX1 : ContDiff ℝ 1 X := by
    rw [show X = fun x => ζ x ^ 2 • Tᗮ.starProjection (x - z) from funext fun x => by
      rw [hX, hw]]
    exact (hζC1.pow 2).smul ((Tᗮ.starProjection).contDiff.comp (contDiff_id.sub contDiff_const))
  have hXout : ∀ x, x ∉ closedBall z r → X x = 0 := fun x hx => by
    rw [hX, hζout x hx]
    simp
  have hXcs : HasCompactSupport X := HasCompactSupport.intro (isCompact_closedBall z r) hXout
  have hXts : tsupport X ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hBU
    by_contra h'
    exact hx (hXout x h')
  -- Step 3 at `μ`-a.e. point.
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = 1 / 2 * (ζ x ^ 2 * g x) + b x := by
    filter_upwards [hae] with x hx
    obtain ⟨P, hP, hPx⟩ := hx
    rw [show X = fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z) from funext fun y => by
      rw [hX, hw]]
    rw [hdivpt x P hP hPx, hg, hb, hw]
    ring
  -- The first variation identity, localized to `B_r(z)`.
  have hFV := hH.2 X hX1 hXcs hXts
  have hL : ∫ x, V.divM X x ∂V.weight =
      ∫ x in closedBall z r, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight := by
    rw [integral_congr_ae hdiv]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [hb, hζout x hx]
    ring
  have hR : ∫ x, inner ℝ (X x) (H x) ∂V.weight =
      ∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hXout x hx, inner_zero_left]).symm
  -- Step 5: absorption (AM-GM) for the drift term.
  have hb_bd : ∀ x, -b x ≤ 1 / 4 * (ζ x ^ 2 * g x) + 36 / r ^ 2 * ‖w x‖ ^ 2 := by
    intro x
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hsq : Real.sqrt (g x) ^ 2 = g x := Real.sq_sqrt (hg0 x)
    have hD : |fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))| ≤
        3 / r * (Real.sqrt (g x) * ‖w x‖) := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [hg]
      exact hopHS _
    have h1 : -b x ≤ 2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) := by
      rw [hb]
      calc -(2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)))
          = 2 * ζ x * -fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) := by ring
        _ ≤ 2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) :=
          mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hD) (by positivity)
    have e : 1 / 4 * (ζ x ^ 2 * g x) + 36 / r ^ 2 * ‖w x‖ ^ 2 -
        2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) =
        (ζ x * Real.sqrt (g x) / 2 - 6 / r * ‖w x‖) ^ 2 := by
      linear_combination (-(1 / 4) * ζ x ^ 2) * hsq
    linarith [sq_nonneg (ζ x * Real.sqrt (g x) / 2 - 6 / r * ‖w x‖)]
  -- Step 6: the mean curvature term, using the height bound at `μ`-a.e. point of `B_r(z)`.
  have hXH_bd : ∀ᵐ x ∂(V.weight.restrict (closedBall z r)),
      -inner ℝ (X x) (H x) ≤ h * ‖H x‖ := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
      with x hxs hxB
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    have hwx : ‖w x‖ ≤ h := by
      rw [hw, hperp]
      exact hheight x ⟨hxs, hxB⟩
    refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ * ‖H x‖ ≤ 1 * h * ‖H x‖ := by gcongr
      _ = h * ‖H x‖ := by ring
  have e1 : ∫ x in closedBall z r, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight =
      1 / 2 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        ∫ x in closedBall z r, b x ∂V.weight := by
    rw [integral_add (hzg.const_mul _) hbi, integral_const_mul]
  have e2 : -∫ x in closedBall z r, b x ∂V.weight ≤
      1 / 4 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        36 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight := by
    have h' := integral_mono hbi.neg ((hzg.const_mul (1 / 4)).add (hh2.const_mul (36 / r ^ 2)))
      hb_bd
    simp only [Pi.neg_apply, Pi.add_apply] at h'
    rwa [integral_neg, integral_add (hzg.const_mul _) (hh2.const_mul _), integral_const_mul,
      integral_const_mul] at h'
  have e3 : -∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight ≤
      h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono_ae hXH.neg (hHint.norm.const_mul h) hXH_bd
  have key : ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight ≤
      144 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight +
        4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    have hid := hFV
    rw [hL, hR, e1] at hid
    have r1 : 144 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight =
        4 * (36 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight) := by ring
    have r2 : 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight =
        4 * (h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight) := by ring
    linarith
  -- `ζ = 1` on `B_{r/2}(z)`.
  have hB2 : ∫ x in closedBall z (r / 2), g x ∂V.weight ≤
      ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight := by
    calc ∫ x in closedBall z (r / 2), g x ∂V.weight
        = ∫ x in closedBall z (r / 2), ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [hζ1 x hx]; ring
      _ ≤ ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_mono_set hzg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hg0 x))
            (closedBall_subset_closedBall (by linarith)).eventuallyLE
  have hId : ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight =
      ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight := by
    congr 1
    funext x
    rw [hw, hperp]
  have hHn0 : 0 ≤ ∫ x in closedBall z r, ‖H x‖ ∂V.weight := integral_nonneg fun x => norm_nonneg _
  simp_rw [← hg]
  rw [hId]
  have hfin' := hB2.trans key
  have hc : 144 / r ^ 2 = 144 * (r ^ 2)⁻¹ := by ring
  rw [hc] at hfin'
  nlinarith [mul_nonneg hh hHn0]
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): every `n`-dimensional subspace `T` of `ℝ^{n+ℓ}` is
a rotated coordinate plane `T = q(ℝⁿ × {0})` for some linear isometry `q` of `ℝ^{n+ℓ}`. -/
theorem allard52_gpa_exists_rotatedPlane_eq : ∀ (n ℓ : ℕ) (T : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ T = n → ∃ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, rotatedPlane q = T := by
  intro n ℓ T hT
  -- An orthonormal basis `u₀, …, u_{n-1}` of `T`.
  let u : OrthonormalBasis (Fin n) ℝ T := (stdOrthonormalBasis ℝ T).reindex (finCongr hT)
  -- Put `uᵢ` at the first `n` indices and extend to an orthonormal basis `b` of `ℝ^{n+ℓ}`.
  let v : Fin (n + ℓ) → Amb n ℓ := Fin.addCases (fun i => (u i : Amb n ℓ)) fun _ => 0
  have hv : Orthonormal ℝ ((Set.range (Fin.castAdd ℓ)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro x y
    obtain ⟨i, hi⟩ := x.2
    obtain ⟨j, hj⟩ := y.2
    have hxy : x = y ↔ i = j := by
      rw [Subtype.ext_iff, ← hi, ← hj, Fin.castAdd_inj]
    simp only [Set.domRestrict_apply, ← hi, ← hj, v, Fin.addCases_left, hxy]
    rw [← Submodule.coe_inner, orthonormal_iff_ite.mp u.orthonormal i j]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hv
  -- `q = b.repr.symm` sends `e_{castAdd i}` to `b (castAdd i) = uᵢ`, so `q(ℝⁿ × {0}) = span{uᵢ} = T`.
  refine ⟨b.repr.symm, ?_⟩
  have hq : ∀ i : Fin n,
      b.repr.symm (EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) = (u i : Amb n ℓ) := by
    intro i
    rw [b.repr_symm_single, hb _ (Set.mem_range_self i)]
    simp [v]
  rw [rotatedPlane, horizontalPlane, Submodule.map_span, ← Set.range_comp]
  have hcomp : (b.repr.symm.toLinearEquiv.toLinearMap ∘ fun i : Fin n =>
      EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) = T.subtype ∘ u := by
    funext i
    exact hq i
  rw [hcomp, Set.range_comp, Submodule.span_image, ← u.coe_toBasis, u.toBasis.span_eq,
    Submodule.map_subtype_top]
/-- Simon Ch. 5, proof of Theorem 5.2 (pp. 123–124), estimate (Nor): for a linear isometry `q` of
`ℝ^{n+ℓ}` and a linear map `A : ℝⁿ → ℝ^ℓ` with `‖A‖ ≤ 1`, the vertical deviation `|y − A x|` of
`(x, y)` from the graph plane `Γ_A = {(v, A v) : v ∈ ℝⁿ}` is at most twice the distance from
`q(x, y)` to `q(Γ_A)`.  Since `Γ_A` is the range of the linear map `v ↦ (v, A v)`, the projection
of `q(x, y)` onto `q(Γ_A)` is `q(v, A v)` for some `v`, so (as `q` is an isometry) this distance
is `d = |(x − v, y − A v)|` with `d² = |x − v|² + |y − A v|²` (`Fin.append_left`/`right`,
`Fin.sum_univ_add`).  Then `|y − A x| ≤ |y − A v| + |A (v − x)| ≤ |y − A v| + |x − v| ≤ √2 d ≤ 2 d`,
using `‖A‖ ≤ 1` and `2 a c ≤ a² + c²`. -/
theorem allard52_gpa_graph_normal_bound : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (y : Rn ℓ), ‖A‖ ≤ 1 → ‖y - A x‖ ≤ 2 * ‖q (graphPoint x y) - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection (q (graphPoint x y))‖ := by
  intro n ℓ q A x y hA
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- `graphPoint` is jointly linear
  have hadd : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b' := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.add_apply, hl]
    · simp only [PiLp.add_apply, hr]
  have hsmul : ∀ (c : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (c • a) (c • b) = c • graphPoint a b := by
    intro c a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.smul_apply, hl]
    · simp only [PiLp.smul_apply, hr]
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  -- Pythagoras: `|(a, b)|² = |a|² + |b|²`
  have hnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- the graph plane is the range of the linear map `J v = (v, A v)`
  let J : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (A v)
      map_add' := fun a a' => by
        simp only [map_add]
        exact hadd a a' (A a) (A a')
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        exact hsmul c a (A a) }
  have hspan : Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)) =
      LinearMap.range J := by
    rw [← Submodule.span_eq (LinearMap.range J), LinearMap.coe_range]
    rfl
  -- the projection of `q (x, y)` onto `q(Γ_A)` is `q (v, A v)` for some `v`
  obtain ⟨z, hz, hzw⟩ := Submodule.mem_map.mp
    (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map
      q.toLinearEquiv.toLinearMap).starProjection_apply_mem (q (graphPoint x y)))
  rw [hspan] at hz
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hz
  rw [← hzw]
  -- its distance to `q (x, y)` is `|(x − v, y − A v)|`, since `q` is an isometry
  have hd : ‖q (graphPoint x y) - q.toLinearEquiv.toLinearMap (J v)‖ =
      ‖graphPoint (x - v) (y - A v)‖ := by
    change ‖q (graphPoint x y) - q (graphPoint v (A v))‖ = _
    rw [← map_sub, LinearIsometryEquiv.norm_map, hsub]
  rw [hd]
  -- `|y − A x| ≤ |y − A v| + |A (v − x)| ≤ |y − A v| + |x − v|` as `‖A‖ ≤ 1`
  have h1 : ‖y - A x‖ ≤ ‖y - A v‖ + ‖x - v‖ := by
    have e : y - A x = (y - A v) + A (v - x) := by
      rw [map_sub]
      abel
    calc ‖y - A x‖ = ‖(y - A v) + A (v - x)‖ := by rw [e]
      _ ≤ ‖y - A v‖ + ‖A (v - x)‖ := norm_add_le _ _
      _ ≤ ‖y - A v‖ + ‖x - v‖ := by
        gcongr
        calc ‖A (v - x)‖ ≤ ‖A‖ * ‖v - x‖ := A.le_opNorm _
          _ ≤ 1 * ‖v - x‖ := by gcongr
          _ = ‖x - v‖ := by rw [one_mul, norm_sub_rev]
  -- `c + a ≤ 2 d` from `d² = a² + c²` and `2 a c ≤ a² + c²`
  have h2 : ‖y - A v‖ + ‖x - v‖ ≤ 2 * ‖graphPoint (x - v) (y - A v)‖ := by
    have hsq := hnorm (x - v) (y - A v)
    have ha := norm_nonneg (x - v)
    have hc := norm_nonneg (y - A v)
    have hdn := norm_nonneg (graphPoint (x - v) (y - A v))
    nlinarith [sq_nonneg (‖x - v‖ - ‖y - A v‖)]
  linarith
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): for a linear isometry `q` of `ℝ^{n+ℓ}`, the
orthogonal projection onto `q(K)` is `q ∘ p_K ∘ q⁻¹`, and conjugation by `q` preserves the
Hilbert–Schmidt norm.  With the rows `w_j = Xᵀ e_j = Σ_k ⟨X e_k, e_j⟩ e_k` of `X`, Parseval gives
`Σ_i |X b_i|² = Σ_i Σ_j ⟨w_j, b_i⟩² = Σ_j |w_j|²` for every orthonormal basis `b`; apply this to
`b = q⁻¹ e` and to `b = e`. -/
theorem allard52_gpa_isometry_conj : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ K : Submodule ℝ (Amb n ℓ), (K.map q.toLinearEquiv.toLinearMap).starProjection = q.toLinearIsometry.toContinuousLinearMap ∘L K.starProjection ∘L q.symm.toLinearIsometry.toContinuousLinearMap) ∧ ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, hsNormSq (q.toLinearIsometry.toContinuousLinearMap ∘L X ∘L q.symm.toLinearIsometry.toContinuousLinearMap) = hsNormSq X := by
  intro n ℓ q
  -- `p_{q(K)} z = q (p_K (q⁻¹ z))` for every `z`.
  refine ⟨fun K => ContinuousLinearMap.ext fun z => Submodule.starProjection_map_apply q K z, ?_⟩
  intro X
  -- The standard basis `e` and the rows `w j = Xᵀ e_j = Σ_k ⟨X e_k, e_j⟩ e_k` of `X`.
  let e := EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ
  let w : Fin (n + ℓ) → Amb n ℓ := fun j => ∑ k, inner ℝ (X (e k)) (e j) • e k
  have hw : ∀ j v, inner ℝ (X v) (e j) = inner ℝ (w j) v := by
    intro j v
    conv_lhs => rw [← e.sum_repr' v]
    simp only [w, map_sum, map_smul, sum_inner, real_inner_smul_left]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- Parseval twice: `Σ_i |X b_i|² = Σ_j |w_j|²` for every orthonormal basis `b`.
  have key : ∀ b : OrthonormalBasis (Fin (n + ℓ)) ℝ (Amb n ℓ),
      ∑ i, ‖X (b i)‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    intro b
    calc ∑ i, ‖X (b i)‖ ^ 2 = ∑ i, ∑ j, inner ℝ (w j) (b i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← e.sum_sq_inner_left]
          simp only [hw]
      _ = ∑ j, ∑ i, inner ℝ (w j) (b i) ^ 2 := Finset.sum_comm
      _ = ∑ j, ‖w j‖ ^ 2 := Finset.sum_congr rfl fun j _ => b.sum_sq_inner_left (w j)
  -- `|q X q⁻¹ e_i| = |X (q⁻¹ e_i)|`, and `q⁻¹ e` is again an orthonormal basis.
  have h1 : hsNormSq (q.toLinearIsometry.toContinuousLinearMap ∘L X ∘L
      q.symm.toLinearIsometry.toContinuousLinearMap) = ∑ i, ‖X (e.map q.symm i)‖ ^ 2 := by
    simp only [hsNormSq, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map,
      OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply, e]
  have h2 : hsNormSq X = ∑ i, ‖X (e i)‖ ^ 2 := by
    simp only [hsNormSq, EuclideanSpace.basisFun_apply, e]
  rw [h1, h2, key, key]
/-- The graph of the zero map `ℝⁿ → ℝ^ℓ` spans the coordinate plane `ℝⁿ × {0}`.  Comparing
coordinates (`Fin.addCases`; `Fin.append_left`/`Fin.append_right`),
`graphPoint v 0 = Σᵢ vᵢ e_{castAdd ℓ i}`: at `castAdd ℓ j` both sides equal `v j` (`castAdd ℓ` is
injective), at `natAdd n j` both vanish (`castAdd ℓ i < n ≤ natAdd n j`).  So every generator of the
left span lies in `horizontalPlane n ℓ`, and conversely `e_{castAdd ℓ i} = graphPoint eᵢ 0` is a
generator of the left span; conclude by `Submodule.span_le` and antisymmetry. -/
theorem allard52_gpa_span_graph_zero : ∀ (n ℓ : ℕ),
    Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v ((0 : Rn n →L[ℝ] Rn ℓ) v)) =
      horizontalPlane n ℓ := by
  intro n ℓ
  have hsum : ∀ v : Rn n, graphPoint v ((0 : Rn n →L[ℝ] Rn ℓ) v) =
      ∑ i : Fin n, v i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
    intro v
    ext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp [graphPoint, Pi.single_apply]
    · have hne : ∀ i : Fin n, Fin.natAdd n j ≠ Fin.castAdd ℓ i := by
        intro i h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [graphPoint, hne]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    dsimp only
    rw [hsum v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [horizontalPlane, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨EuclideanSpace.single i 1, ?_⟩
    dsimp only
    rw [hsum]
    simp
/-- `graphPoint` is linear in the pair `(x, y)`: `(x, y) = ι x + κ y` in `ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ`, with
`ι = Φ ∘ inl`, `κ = Φ ∘ inr` and `Φ` the inverse of Mathlib's `EuclideanSpace.finAddEquivProd`.
Coordinatewise (`Fin.addCases`), `graphPoint x y = Φ (x, y)`; then `(x, y) = (x, 0) + (0, y)`. -/
theorem allard52_gfz_graphPoint_split : ∀ (n ℓ : ℕ), ∃ (ι : Rn n →L[ℝ] Amb n ℓ) (κ : Rn ℓ →L[ℝ] Amb n ℓ), ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y = ι x + κ y := by
  intro n ℓ
  let Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ :=
    ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
      Rn n × Rn ℓ →L[ℝ] Amb n ℓ)
  refine ⟨Φ ∘L ContinuousLinearMap.inl ℝ (Rn n) (Rn ℓ),
    Φ ∘L ContinuousLinearMap.inr ℝ (Rn n) (Rn ℓ), fun x y => ?_⟩
  have hΦ : graphPoint x y = Φ (x, y) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [graphPoint, Φ]
    · simp [graphPoint, Φ]
  rw [hΦ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    add_zero, zero_add]
/-- Inner product of graph points: `⟨(x, y), (x', y')⟩ = ⟨x, x'⟩ + ⟨y, y'⟩` in `ℝ^{n+ℓ}`.  Each inner
product of `EuclideanSpace` is the coordinate sum (`PiLp.inner_apply`); split the sum over
`Fin (n + ℓ)` into its `Fin.castAdd ℓ` and `Fin.natAdd n` parts (`Fin.sum_univ_add`), where the
coordinates of `graphPoint x y` are `x i`, resp. `y j` (`Fin.append_left`/`Fin.append_right`). -/
theorem allard52_gfz_graphPoint_inner : ∀ (n ℓ : ℕ) (x x' : Rn n) (y y' : Rn ℓ),
    inner ℝ (graphPoint x y) (graphPoint x' y') = inner ℝ x x' + inner ℝ y y' := by
  intro n ℓ x x' y y'
  simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
/-- Derivative at `0` of the Gram-formula projection `F(A) = J_A (τ(J_A) J_A)⁻¹ τ(J_A)`, where
`J_A = ι + κ ∘ A`, `τ` is an abstract transpose (`⟪τ L w, v⟫ = ⟪w, L v⟫`), `ι` is isometric and
`κ` has range orthogonal to that of `ι`.  Testing against every `u` (`ext_inner_right`) gives, for
`π = τ ι`: `π ∘ ι = 1`, `π ∘ κ = 0` and `τ(κ ∘ H') ∘ ι = 0`.  As `A ↦ J_A` has derivative
`compL κ`, the product rule (`HasFDerivAt.clm_comp`) shows that the Gram map `G_A = τ(J_A) ∘ J_A`
has derivative `H' ↦ π ∘ κ ∘ H' + τ(κ ∘ H') ∘ ι = 0` at `0`, and `G_0 = 1`.  `Ring.inverse` is
differentiable at the unit `1` (`differentiableAt_inverse`), so `A ↦ G_A⁻¹` has derivative `0`
and value `1` at `0`; the product rule twice gives `ι ∘ τ(κ ∘ H) + κ ∘ H ∘ π`. -/
theorem allard52_gfz_gram_fderiv_zero : ∀ (n ℓ : ℕ) (ι : Rn n →L[ℝ] Amb n ℓ)
    (κ : Rn ℓ →L[ℝ] Amb n ℓ) (τ : (Rn n →L[ℝ] Amb n ℓ) →L[ℝ] (Amb n ℓ →L[ℝ] Rn n)),
    (∀ (L : Rn n →L[ℝ] Amb n ℓ) (w : Amb n ℓ) (v : Rn n), inner ℝ (τ L w) v = inner ℝ w (L v)) →
    (∀ v u : Rn n, inner ℝ (ι v) (ι u) = inner ℝ v u) →
    (∀ (v : Rn n) (z : Rn ℓ), inner ℝ (ι v) (κ z) = 0) → ∀ H : Rn n →L[ℝ] Rn ℓ,
    fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ =>
      (ι + κ ∘L A) ∘L Ring.inverse (τ (ι + κ ∘L A) ∘L (ι + κ ∘L A)) ∘L τ (ι + κ ∘L A)) 0 H =
      ι ∘L τ (κ ∘L H) + κ ∘L H ∘L τ ι := by
  intro n ℓ ι κ τ hT hI hO H
  have hπι : τ ι ∘L ι = 1 := by
    ext1 v
    refine ext_inner_right ℝ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, hT, hI, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply]
  have hπκ : ∀ z : Rn ℓ, τ ι (κ z) = 0 := fun z =>
    ext_inner_right ℝ fun u => by rw [hT, real_inner_comm, hO, inner_zero_left]
  have hτκι : ∀ (H' : Rn n →L[ℝ] Rn ℓ) (v : Rn n), τ (κ ∘L H') (ι v) = 0 := fun H' v =>
    ext_inner_right ℝ fun u => by rw [hT, ContinuousLinearMap.comp_apply, hO, inner_zero_left]
  set K := ContinuousLinearMap.compL ℝ (Rn n) (Rn ℓ) (Amb n ℓ) κ with hK
  have hJ : HasFDerivAt (fun A : Rn n →L[ℝ] Rn ℓ => ι + κ ∘L A) K 0 :=
    K.hasFDerivAt.const_add ι
  have hτJ : HasFDerivAt (fun A : Rn n →L[ℝ] Rn ℓ => τ (ι + κ ∘L A)) (τ ∘L K) 0 :=
    τ.hasFDerivAt.comp (0 : Rn n →L[ℝ] Rn ℓ) hJ
  have hG : HasFDerivAt (fun A : Rn n →L[ℝ] Rn ℓ => τ (ι + κ ∘L A) ∘L (ι + κ ∘L A))
      (0 : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] Rn n →L[ℝ] Rn n) 0 := by
    convert hτJ.clm_comp hJ using 1
    ext H' v
    simp [hK, hπκ, hτκι]
  have hG0 : τ (ι + κ ∘L (0 : Rn n →L[ℝ] Rn ℓ)) ∘L (ι + κ ∘L 0) = 1 := by
    rw [ContinuousLinearMap.comp_zero, add_zero, hπι]
  have hR : HasFDerivAt (fun A : Rn n →L[ℝ] Rn ℓ =>
      Ring.inverse (τ (ι + κ ∘L A) ∘L (ι + κ ∘L A)))
      (0 : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] Rn n →L[ℝ] Rn n) 0 := by
    have hinv : DifferentiableAt ℝ (Ring.inverse : (Rn n →L[ℝ] Rn n) → (Rn n →L[ℝ] Rn n))
        (τ (ι + κ ∘L (0 : Rn n →L[ℝ] Rn ℓ)) ∘L (ι + κ ∘L 0)) := by
      rw [hG0]
      exact differentiableAt_inverse isUnit_one
    have := hinv.hasFDerivAt.comp (0 : Rn n →L[ℝ] Rn ℓ) hG
    rwa [ContinuousLinearMap.comp_zero] at this
  have hF := hJ.clm_comp (hR.clm_comp hτJ)
  rw [hF.fderiv]
  ext v
  simp [hK, hπι]
/-- Coordinate formula for a transpose (step 6(b) of the derivative of the graph-plane projection
at `0`, Simon Ch. 5, p. 123, for an arbitrary `L` in place of `κ ∘ H`): if `T : ℝᵐ → ℝⁿ` satisfies
`⟨T w, v⟩ = ⟨w, L v⟩` for all `w`, `v`, then `T w = Σᵢ ⟨L eᵢ, w⟩ eᵢ`.  By nondegeneracy of the inner
product (`ext_inner_right`) pair both sides with `u = Σᵢ uᵢ eᵢ` (`OrthonormalBasis.sum_repr` for
`EuclideanSpace.basisFun`): the left side is `⟨w, L u⟩ = Σᵢ uᵢ ⟨w, L eᵢ⟩`, the right side is
`Σᵢ ⟨L eᵢ, w⟩ ⟨eᵢ, u⟩ = Σᵢ ⟨L eᵢ, w⟩ uᵢ` (`EuclideanSpace.inner_single_left`), and the two sums agree
termwise by `real_inner_comm`. -/
theorem allard52_gfz_transpose_eq_sum : ∀ (n m : ℕ) (L : Rn n →L[ℝ] Rn m) (T : Rn m →L[ℝ] Rn n), (∀ (w : Rn m) (v : Rn n), inner ℝ (T w) v = inner ℝ w (L v)) → ∀ w : Rn m, T w = ∑ i : Fin n, inner ℝ (L (EuclideanSpace.single i 1)) w • EuclideanSpace.single i 1 := by
  intro n m L T hT w
  refine ext_inner_right ℝ fun u => ?_
  have hu : u = ∑ i, u i • EuclideanSpace.single i (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u).symm
  rw [hT]
  conv_lhs => rw [hu]
  simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]
  ring
/-- Simon Ch. 5, p. 123 (the matrix of `p_{T G(f)}` in the proof of Theorem 5.2), step 1 of the
graph-projection computation: the transpose `Lᵀ w = Σᵢ ⟨L eᵢ, w⟩ eᵢ` of `L : ℝⁿ → ℝᵐ`, built from
the standard basis `eᵢ` of `ℝⁿ` (`ContinuousLinearMap.adjoint` is outside the import closure).
`L ↦ Lᵀ` is linear because `⟨L eᵢ, w⟩` is linear in `L`, hence continuous since `L(ℝⁿ, ℝᵐ)` is
finite-dimensional, and expanding `v = Σᵢ vᵢ eᵢ` gives `⟨Lᵀ w, v⟩ = Σᵢ ⟨L eᵢ, w⟩ vᵢ = ⟨w, L v⟩`. -/
theorem allard52_gps_transpose_exists : ∀ (n m : ℕ), ∃ τ : (Rn n →L[ℝ] Rn m) →L[ℝ] (Rn m →L[ℝ] Rn n), ∀ (L : Rn n →L[ℝ] Rn m) (w : Rn m) (v : Rn n), inner ℝ (τ L w) v = inner ℝ w (L v) := by
  intro n m
  -- The standard basis `e i` of `ℝⁿ`.
  let e : Fin n → Rn n := fun i => EuclideanSpace.single i (1 : ℝ)
  -- `τ₀ L = Lᵀ`, linear in `L` since `⟨L eᵢ, w⟩` is.
  let τ₀ : (Rn n →L[ℝ] Rn m) →ₗ[ℝ] (Rn m →L[ℝ] Rn n) :=
    { toFun := fun L => ∑ i, (innerSL ℝ (L (e i))).smulRight (e i)
      map_add' := fun L L' => by
        ext1 w
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c L => by
        ext1 w
        simp [smul_smul, Finset.smul_sum] }
  -- `L(ℝⁿ, ℝᵐ)` is finite-dimensional, so `τ₀` is continuous.
  refine ⟨LinearMap.toContinuousLinearMap τ₀, fun L w v => ?_⟩
  have hv : v = ∑ i, v i • e i := by
    simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
  have hτ : LinearMap.toContinuousLinearMap τ₀ L w = ∑ i, inner ℝ (L (e i)) w • e i := by
    simp [τ₀]
  rw [hτ]
  conv_rhs => rw [hv]
  simp only [sum_inner, inner_sum, map_sum, map_smul, real_inner_smul_left,
    real_inner_smul_right, e, EuclideanSpace.inner_single_left, one_mul, map_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]
  ring
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): the orthogonal projection onto the graph plane
`Γ_A = span {(v, A v) : v ∈ ℝⁿ}` is the Gram formula `J (T J)⁻¹ T`, for any parametrization
`J v = (v, A v)` of `Γ_A` and any transpose `T` of `J` (`⟨T w, v⟩ = ⟨w, J v⟩`).  `J` is injective
(the first `n` coordinates of `J v` are those of `v`), so `T J` is a unit of `End(ℝⁿ)` because
`⟨T J v, v⟩ = |J v|²`.  With `R = (T J)⁻¹`, `J R T w ∈ Γ_A` and `⟨w − J R T w, J v⟩ =
⟨T w − T J R T w, v⟩ = 0`, so `J R T w = p_{Γ_A} w` (`eq_starProjection_of_mem_of_inner_eq_zero`). -/
theorem allard52_gps_starProjection_eq_gram : ∀ (n ℓ : ℕ) (A : Rn n →L[ℝ] Rn ℓ) (J : Rn n →L[ℝ] Amb n ℓ) (T : Amb n ℓ →L[ℝ] Rn n), (∀ v : Rn n, J v = graphPoint v (A v)) → (∀ (w : Amb n ℓ) (v : Rn n), inner ℝ (T w) v = inner ℝ w (J v)) → IsUnit (T ∘L J) ∧ (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection = J ∘L Ring.inverse (T ∘L J) ∘L T := by
  intro n ℓ A J T hJ hT
  -- `J` is injective: the coordinate of `graphPoint v (A v)` at `Fin.castAdd ℓ i` is `v i`.
  have hJinj : Function.Injective J := by
    intro v v' h
    rw [hJ, hJ] at h
    ext i
    simpa [graphPoint] using congrArg (fun z : Amb n ℓ => z (Fin.castAdd ℓ i)) h
  -- `T ∘L J` is a unit: `T (J v) = 0` gives `|J v|² = ⟨T (J v), v⟩ = 0`, so `v = 0`.
  have hU : IsUnit (T ∘L J) := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro v hv
    have h0 : T (J v) = 0 := hv
    have h1 : inner ℝ (J v) (J v) = 0 := by
      rw [← hT, h0, inner_zero_left]
    exact hJinj (by rw [inner_self_eq_zero.mp h1, map_zero])
  refine ⟨hU, ?_⟩
  -- `T (J (R u)) = u` for `R = Ring.inverse (T ∘L J)`.
  have hTJR : ∀ u : Rn n, T (J (Ring.inverse (T ∘L J) u)) = u := by
    intro u
    simpa using congrArg (fun S : Rn n →L[ℝ] Rn n => S u) (Ring.mul_inverse_cancel _ hU)
  -- `Γ_A ⊆ J(ℝⁿ)`: every element of the span has the form `J v`.
  have hle : Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)) ≤
      LinearMap.range J.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨v, hJ v⟩
  -- `p = J (R (T w)) ∈ Γ_A` and `w - p ⊥ J v` for all `v`, so `p` is the projection of `w`.
  ext1 w
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.subset_span ⟨Ring.inverse (T ∘L J) (T w), (hJ _).symm⟩
  · intro z hz
    obtain ⟨v, rfl⟩ := hle hz
    rw [inner_sub_left, ContinuousLinearMap.coe_coe, ← hT, ← hT]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hTJR, sub_self]
/-- Simon Ch. 5, p. 123 (smooth dependence of `p_{T G(f)}` on `Df`): the orthogonal projection
`Π(A)` onto the graph plane `Γ_A = {(v, A v) : v ∈ ℝⁿ}` is a `C²` function of `A ∈ L(ℝⁿ, ℝ^ℓ)`
(operator norms).  With `Φ = finAddEquivProd⁻¹ : ℝⁿ × ℝ^ℓ → ℝ^{n+ℓ}`, `ι = Φ ∘ inl` and
`κ = Φ ∘ inr` we have `graphPoint x y = ι x + κ y`, so `J_A = ι + κ ∘ A` parametrizes `Γ_A`.  For
the transpose `τ` of `allard52_gps_transpose_exists`, `allard52_gps_starProjection_eq_gram` gives
`Π(A) = J_A (τ(J_A) J_A)⁻¹ τ(J_A)` with `τ(J_A) J_A` a unit.  `A ↦ J_A` is affine, `τ` is
continuous linear, operator composition is bounded bilinear and `Ring.inverse` is `C²` at every
unit (`contDiffAt_ringInverse`), so this formula is `C²` in `A`. -/
theorem allard52_gps_contDiff : ∀ (n ℓ : ℕ), ContDiff ℝ 2 (fun A : Rn n →L[ℝ] Rn ℓ => (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) := by
  intro n ℓ
  -- Step 1: `graphPoint x y = Φ (x, y) = ι x + κ y`.
  let Φ : (Rn n × Rn ℓ) ≃L[ℝ] Amb n ℓ :=
    (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm
  let ι : Rn n →L[ℝ] Amb n ℓ :=
    (Φ : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ).comp (ContinuousLinearMap.inl ℝ (Rn n) (Rn ℓ))
  let κ : Rn ℓ →L[ℝ] Amb n ℓ :=
    (Φ : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ).comp (ContinuousLinearMap.inr ℝ (Rn n) (Rn ℓ))
  have hΦ : ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y = Φ (x, y) := by
    intro x y
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [graphPoint, Φ]
    · simp [graphPoint, Φ]
  have hgp : ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y = ι x + κ y := by
    intro x y
    have hxy : ((x, y) : Rn n × Rn ℓ) = (x, 0) + (0, y) := by simp
    rw [hΦ, hxy, map_add]
    rfl
  -- Step 2: the transpose `τ`, for `m = n + ℓ` (`Amb n ℓ` is `Rn (n + ℓ)`).
  obtain ⟨τ, hτ⟩ := Submission.allard52_gps_transpose_exists n (n + ℓ)
  -- Step 3: the parametrization `J_A = ι + κ ∘ A` of `Γ_A`, and `T_A = τ(J_A)`.
  let J : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ) := fun A => ι + κ.comp A
  let T : (Rn n →L[ℝ] Rn ℓ) → (Amb n ℓ →L[ℝ] Rn n) := fun A => τ (J A)
  have hJ : ∀ (A : Rn n →L[ℝ] Rn ℓ) (v : Rn n), J A v = graphPoint v (A v) := by
    intro A v
    rw [hgp]
    rfl
  -- Step 4: `Π(A) = J_A (T_A J_A)⁻¹ T_A` with `T_A J_A` a unit, by the Gram projection child.
  have hP : ∀ A : Rn n →L[ℝ] Rn ℓ, IsUnit (T A ∘L J A) ∧
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection =
        J A ∘L Ring.inverse (T A ∘L J A) ∘L T A :=
    fun A => Submission.allard52_gps_starProjection_eq_gram n ℓ A (J A) (T A) (hJ A)
      (fun w v => hτ (J A) w v)
  -- Step 5: `A ↦ J_A`, `A ↦ T_A` and `A ↦ G_A = T_A J_A` are `C²`.
  have hJc : ContDiff ℝ 2 J := contDiff_const.add (contDiff_const.clm_comp contDiff_id)
  have hTc : ContDiff ℝ 2 T := τ.contDiff.comp hJc
  have hGc : ContDiff ℝ 2 fun A => T A ∘L J A := hTc.clm_comp hJc
  -- Step 6: `A ↦ G_A⁻¹` is `C²`, since `Ring.inverse` is `C²` at the unit `G_A`.
  have hIc : ContDiff ℝ 2 fun A => Ring.inverse (T A ∘L J A) := by
    rw [contDiff_iff_contDiffAt]
    intro A
    obtain ⟨u, hu⟩ := (hP A).1
    have h := contDiffAt_ringInverse ℝ (n := 2) u
    rw [hu] at h
    exact h.comp A hGc.contDiffAt
  -- Step 7: `F(A) = J_A (G_A⁻¹ T_A)` is `C²`, and `Π = F`.
  have hF : ContDiff ℝ 2 fun A => J A ∘L Ring.inverse (T A ∘L J A) ∘L T A :=
    hJc.clm_comp (hIc.clm_comp hTc)
  have hPF : (fun A : Rn n →L[ℝ] Rn ℓ =>
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) =
        fun A => J A ∘L Ring.inverse (T A ∘L J A) ∘L T A :=
    funext fun A => (hP A).2
  rw [hPF]
  exact hF

/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): the derivative at `A = 0` of the projection
`Π(A) = p_{Γ_A}` onto the graph plane `Γ_A = span {(v, A v) : v ∈ ℝⁿ}` is
`DΠ(0)[H] (x, y) = (Hᵀ y, H x)` with `Hᵀ y = Σᵢ ⟨H eᵢ, y⟩ eᵢ`, i.e. `DΠ(0)[H] = [[0, Hᵀ], [H, 0]]`.
Write `(x, y) = ι x + κ y` and take a transpose `τ`.  Then `Π(A) = J_A (τ(J_A) J_A)⁻¹ τ(J_A)` for
`J_A = ι + κ ∘ A`, so `DΠ(0)[H] = ι ∘ τ(κ ∘ H) + κ ∘ H ∘ τ(ι)`, and on `(x, y)` one has
`τ(ι) (x, y) = x` and `τ(κ ∘ H) (x, y) = Hᵀ y` by `⟨(x, y), (x', y')⟩ = ⟨x, x'⟩ + ⟨y, y'⟩`. -/
theorem allard52_gps_fderiv_zero_apply : ∀ (n ℓ : ℕ) (H : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (y : Rn ℓ), fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ => (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) 0 H (graphPoint x y) = graphPoint (∑ i : Fin n, inner ℝ (H (EuclideanSpace.single i 1)) y • EuclideanSpace.single i 1) (H x) := by
  intro n ℓ H x y
  -- Step 1: `graphPoint x y = ι x + κ y`, so `ι v = (v, 0)` and `κ z = (0, z)`.
  obtain ⟨ι, κ, hgp⟩ := Submission.allard52_gfz_graphPoint_split n ℓ
  have hι : ∀ v : Rn n, ι v = graphPoint v 0 := fun v => by
    rw [hgp, map_zero, add_zero]
  have hκ : ∀ z : Rn ℓ, κ z = graphPoint 0 z := fun z => by
    rw [hgp, map_zero, zero_add]
  -- Step 2: `ι` is isometric and `ι ⊥ κ`, since `⟨(x, y), (x', y')⟩ = ⟨x, x'⟩ + ⟨y, y'⟩`.
  have hI : ∀ v u : Rn n, inner ℝ (ι v) (ι u) = inner ℝ v u := fun v u => by
    rw [hι, hι, Submission.allard52_gfz_graphPoint_inner, inner_zero_left, add_zero]
  have hO : ∀ (v : Rn n) (z : Rn ℓ), inner ℝ (ι v) (κ z) = 0 := fun v z => by
    rw [hι, hκ, Submission.allard52_gfz_graphPoint_inner, inner_zero_right, inner_zero_left,
      add_zero]
  -- Step 3: a transpose `τ`, for `m = n + ℓ` (`Amb n ℓ` is `Rn (n + ℓ)`).
  obtain ⟨τ, hτ⟩ : ∃ τ : (Rn n →L[ℝ] Amb n ℓ) →L[ℝ] (Amb n ℓ →L[ℝ] Rn n),
      ∀ (L : Rn n →L[ℝ] Amb n ℓ) (w : Amb n ℓ) (v : Rn n), inner ℝ (τ L w) v = inner ℝ w (L v) :=
    allard52_gps_transpose_exists n (n + ℓ)
  -- Step 4: `Π(A) = J_A (τ(J_A) J_A)⁻¹ τ(J_A)` with `J_A = ι + κ ∘ A`, by the Gram formula.
  have hP : (fun A : Rn n →L[ℝ] Rn ℓ =>
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) =
        fun A => (ι + κ ∘L A) ∘L Ring.inverse (τ (ι + κ ∘L A) ∘L (ι + κ ∘L A)) ∘L
          τ (ι + κ ∘L A) :=
    funext fun A => (allard52_gps_starProjection_eq_gram n ℓ A (ι + κ ∘L A) (τ (ι + κ ∘L A))
      (fun v => (hgp v (A v)).symm) (hτ (ι + κ ∘L A))).2
  -- Step 5: `DΠ(0)[H] = ι ∘ τ(κ ∘ H) + κ ∘ H ∘ τ(ι)`.
  rw [hP, Submission.allard52_gfz_gram_fderiv_zero n ℓ ι κ τ hτ hI hO H]
  -- Step 6: on `(x, y)`, `τ(ι) (x, y) = x` and `τ(κ ∘ H) (x, y) = Σᵢ ⟨H eᵢ, y⟩ eᵢ = Hᵀ y`.
  have hπ : τ ι (graphPoint x y) = x := ext_inner_right ℝ fun u => by
    rw [hτ, hι, Submission.allard52_gfz_graphPoint_inner, inner_zero_right, add_zero]
  have hHt : τ (κ ∘L H) (graphPoint x y) =
      ∑ i : Fin n, inner ℝ (H (EuclideanSpace.single i 1)) y • EuclideanSpace.single i 1 := by
    rw [Submission.allard52_gfz_transpose_eq_sum n (n + ℓ) (κ ∘L H) (τ (κ ∘L H)) (hτ (κ ∘L H))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply, hκ, Submission.allard52_gfz_graphPoint_inner,
      inner_zero_left, zero_add]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [hπ, hHt, hgp]
/-- Hilbert–Schmidt norm of the block operator `D = [[0, Hᵀ], [H, 0]]` on `ℝ^{n+ℓ}`:
`|D|² = 2|H|²`.  Since `‖graphPoint x y‖² = ‖x‖² + ‖y‖²` and the standard basis vectors of
`ℝ^{n+ℓ}` are `E_{castAdd i} = graphPoint eᵢ 0`, `E_{natAdd j} = graphPoint 0 f_j`
(`Fin.addCases`; `castAdd ℓ i ≠ natAdd n j` by comparing values), split `hsNormSq D` over the
`castAdd`/`natAdd` indices (`Fin.sum_univ_add`).  The column `D E_{castAdd i} = graphPoint 0 (H eᵢ)`
contributes `‖H eᵢ‖²`; the column `D E_{natAdd j} = graphPoint (∑ᵢ (H eᵢ)_j eᵢ) 0` contributes
`∑ᵢ (H eᵢ)_j²` (`EuclideanSpace.inner_single_right`).  Exchanging the finite sums
(`Finset.sum_comm`) gives `hsNormSq H + hsNormSq H`. -/
theorem allard52_gps_hsNormSq_swap : ∀ (n ℓ : ℕ) (H : Rn n →L[ℝ] Rn ℓ)
    (D : Amb n ℓ →L[ℝ] Amb n ℓ), (∀ (x : Rn n) (y : Rn ℓ), D (graphPoint x y) =
      graphPoint (∑ i : Fin n, inner ℝ (H (EuclideanSpace.single i 1)) y •
        EuclideanSpace.single i 1) (H x)) → hsNormSq D = 2 * hsNormSq H := by
  intro n ℓ H D hD
  have hnorm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]
    simp [graphPoint]
  have hE₁ : ∀ i : Fin n, (EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) : Amb n ℓ) =
      graphPoint (EuclideanSpace.single i 1) 0 := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · simp [graphPoint, Pi.single_apply]
    · have h : Fin.natAdd n j' ≠ Fin.castAdd ℓ i := by
        rw [Ne, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
        have := i.isLt
        omega
      simp [graphPoint, h]
  have hE₂ : ∀ j : Fin ℓ, (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) : Amb n ℓ) =
      graphPoint 0 (EuclideanSpace.single j 1) := by
    intro j
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · have h : Fin.castAdd ℓ i' ≠ Fin.natAdd n j := by
        rw [Ne, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
        have := i'.isLt
        omega
      simp [graphPoint, h]
    · simp [graphPoint, Pi.single_apply]
  have hcol₁ : ∀ i : Fin n, ‖D (EuclideanSpace.single (Fin.castAdd ℓ i) 1)‖ ^ 2 =
      ‖H (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    rw [hE₁, hD, hnorm]
    simp
  have hcol₂ : ∀ j : Fin ℓ, ‖D (EuclideanSpace.single (Fin.natAdd n j) 1)‖ ^ 2 =
      ∑ i : Fin n, (H (EuclideanSpace.single i 1) j) ^ 2 := by
    intro j
    rw [hE₂, hD, hnorm, map_zero, norm_zero, EuclideanSpace.real_norm_sq_eq]
    simp [EuclideanSpace.inner_single_right, Pi.single_apply]
  unfold hsNormSq
  rw [Fin.sum_univ_add]
  simp_rw [hcol₁, hcol₂]
  rw [Finset.sum_comm]
  simp_rw [← EuclideanSpace.real_norm_sq_eq]
  ring
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123): the orthogonal projection `Π(A) = p_{Γ_A}` onto the
graph plane `Γ_A = {(v, A v) : v ∈ ℝⁿ}` is a `C²` function of `A ∈ L(ℝⁿ, ℝ^ℓ)`, and
`|DΠ(0)[H]|² = 2|H|²` (Hilbert–Schmidt norms).  Smoothness is `allard52_gps_contDiff`
(`Π(A) = J_A (J_Aᵀ J_A)⁻¹ J_Aᵀ` with `J_A v = (v, A v)`, and inversion is smooth at units).
By `allard52_gps_fderiv_zero_apply`, `DΠ(0)[H] (x, y) = (Hᵀ y, H x)`, i.e. `DΠ(0)[H]` is the block
operator `[[0, Hᵀ], [H, 0]]`, whose squared Hilbert–Schmidt norm is `|Hᵀ|² + |H|² = 2|H|²` by
`allard52_gps_hsNormSq_swap`. -/
theorem allard52_gpa_graphProj_smooth : ∀ (n ℓ : ℕ), ContDiff ℝ 2 (fun A : Rn n →L[ℝ] Rn ℓ => (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) ∧ ∀ H : Rn n →L[ℝ] Rn ℓ, hsNormSq (fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ => (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) 0 H) = 2 * hsNormSq H := by
  intro n ℓ
  exact ⟨Submission.allard52_gps_contDiff n ℓ, fun H =>
    Submission.allard52_gps_hsNormSq_swap n ℓ H _ (Submission.allard52_gps_fderiv_zero_apply n ℓ H)⟩

/-- Simon Ch. 5, proof of Theorem 5.2 (p. 123), (Gp) with `q = id`: for `|A|, |B| ≤ L₀` the
orthogonal projections `p_{Γ_A}`, `p_{Γ_B}` onto the graph planes satisfy
`|A − B|² ≤ |p_{Γ_A} − p_{Γ_B}|² ≤ 3 |A − B|²` (Hilbert–Schmidt norms), `L₀ = L₀(n, ℓ) ∈ (0, 1/4]`. -/
theorem allard52_gpa_graphProj_bilipschitz : ∀ (n ℓ : ℕ), ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 / 4 ∧ ∀ (A B : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNorm B ≤ L₀ → hsNormSq (A - B) ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection - (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection) ∧ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection - (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection) ≤ 3 * hsNormSq (A - B) := by
  -- Steps 1 and 4 for any `C²` map: `‖f X - f Y - Df(0)(X - Y)‖ ≤ K r ‖X - Y‖` on `B_r(0)`, `r ≤ 1`
  -- (`Df` is `K`-Lipschitz on the compact convex `B_1(0)`; mean value inequality on `B_r(0)`).
  have remainder : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F), ContDiff ℝ 2 f → ∃ K : ℝ, 0 ≤ K ∧
      ∀ r : ℝ, r ≤ 1 → ∀ X Y : E, ‖X‖ ≤ r → ‖Y‖ ≤ r →
        ‖f X - f Y - fderiv ℝ f 0 (X - Y)‖ ≤ K * r * ‖X - Y‖ := by
    intro E F _ _ _ _ _ f hf
    have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    obtain ⟨K, hK⟩ := (hf'.contDiffOn (s := closedBall (0 : E) 1)).exists_lipschitzOnWith
      one_ne_zero (convex_closedBall 0 1) (isCompact_closedBall 0 1)
    refine ⟨K, K.coe_nonneg, fun r hr X Y hX hY => ?_⟩
    have hdiff : ∀ x ∈ closedBall (0 : E) r, DifferentiableAt ℝ f x :=
      fun x _ => hf.differentiable (by norm_num) x
    have hbound : ∀ x ∈ closedBall (0 : E) r, ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ K * r := fun x hx =>
      hK.norm_sub_le_of_le (closedBall_subset_closedBall hr hx)
        (mem_closedBall_self zero_le_one) (by simpa using hx)
    exact (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound
      (mem_closedBall_zero_iff.2 hY) (mem_closedBall_zero_iff.2 hX)
  -- Steps 0 and 6–8: `|X|² = 2|Z|²` and `|Y| ≤ (√3 - √2)|Z|` give `|Z|² ≤ |X + Y|² ≤ 3|Z|²`,
  -- since `(2√2 - √3)|Z| ≤ |X + Y| ≤ √3 |Z|` and `2√2 - √3 ≥ 1`.
  have perturb : ∀ (m k p q : ℕ) (X Y : Rn m →L[ℝ] Rn k) (Z : Rn p →L[ℝ] Rn q),
      hsNormSq X = 2 * hsNormSq Z → hsNorm Y ≤ (Real.sqrt 3 - Real.sqrt 2) * hsNorm Z →
        hsNormSq Z ≤ hsNormSq (X + Y) ∧ hsNormSq (X + Y) ≤ 3 * hsNormSq Z := by
    intro m k p q X Y Z hX hY
    have hsq : ∀ {a b : ℕ} (T : Rn a →L[ℝ] Rn b), hsNorm T ^ 2 = hsNormSq T :=
      fun T => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hneg : hsNorm (-Y) = hsNorm Y := by simp [hsNorm, hsNormSq]
    have hz : 0 ≤ hsNorm Z := Real.sqrt_nonneg _
    have hx : hsNorm X = Real.sqrt 2 * hsNorm Z := by
      rw [hsNorm, hX, Real.sqrt_mul (by norm_num)]; rfl
    have tri1 := (allard52_gpa_hsNorm_bounds m k X Y).2.2
    have tri2 := (allard52_gpa_hsNorm_bounds m k (X + Y) (-Y)).2.2
    rw [add_neg_cancel_right, hneg] at tri2
    have ha : 0 ≤ hsNorm (X + Y) := Real.sqrt_nonneg _
    have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have s3le : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have key : 1 ≤ 2 * Real.sqrt 2 - Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
    have up : hsNorm (X + Y) ≤ Real.sqrt 3 * hsNorm Z := by linarith
    have low : hsNorm Z ≤ hsNorm (X + Y) := by nlinarith
    rw [← hsq (X + Y), ← hsq Z]
    exact ⟨pow_le_pow_left₀ hz low 2, (pow_le_pow_left₀ ha up 2).trans_eq (by rw [mul_pow, s3])⟩
  intro n ℓ
  -- [S2]: `Π` is `C²` and `|DΠ(0) H|² = 2 |H|²`.
  obtain ⟨hC2, hD⟩ := Submission.allard52_gpa_graphProj_smooth n ℓ
  obtain ⟨K, hK0, hK⟩ := remainder _ hC2
  set D := fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ =>
    (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) 0 with hDdef
  -- Step 2: `C_g = 1 + √(n + ℓ) K` and `L₀ = min {1/4, (√3 - √2)/C_g}`.
  have h23 : Real.sqrt 2 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set Cg : ℝ := 1 + Real.sqrt ((n + ℓ : ℕ) : ℝ) * K with hCg
  have hCg1 : 1 ≤ Cg := by
    have := mul_nonneg (Real.sqrt_nonneg ((n + ℓ : ℕ) : ℝ)) hK0
    linarith
  set L₀ : ℝ := min (1 / 4) ((Real.sqrt 3 - Real.sqrt 2) / Cg) with hL₀
  have hL₀pos : 0 < L₀ := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have hL₀1 : L₀ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hCgL : Cg * L₀ ≤ Real.sqrt 3 - Real.sqrt 2 := by
    have := mul_le_mul_of_nonneg_left (min_le_right (1 / 4 : ℝ) ((Real.sqrt 3 - Real.sqrt 2) / Cg))
      (show (0 : ℝ) ≤ Cg by linarith)
    rwa [mul_div_cancel₀ _ (by linarith : Cg ≠ 0)] at this
  refine ⟨L₀, hL₀pos, min_le_left _ _, fun A B hA hB => ?_⟩
  -- Step 3: `‖A‖ ≤ |A| ≤ L₀` and `‖B‖ ≤ L₀` [S1].
  have hA' : ‖A‖ ≤ L₀ := (allard52_gpa_hsNorm_bounds n ℓ A B).1.trans hA
  have hB' : ‖B‖ ≤ L₀ := (allard52_gpa_hsNorm_bounds n ℓ B A).1.trans hB
  -- Step 4: the remainder `R = Π(A) - Π(B) - D(A - B)` has `‖R‖ ≤ K L₀ ‖A - B‖`.
  have hR := hK L₀ hL₀1 A B hA' hB'
  set R : Amb n ℓ →L[ℝ] Amb n ℓ :=
    (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection -
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection - D (A - B)
    with hRdef
  -- Step 5: `|R| ≤ √(n + ℓ) ‖R‖ ≤ √(n + ℓ) K L₀ |A - B| ≤ (√3 - √2) |A - B|` [S1].
  have hRb : hsNorm R ≤ (Real.sqrt 3 - Real.sqrt 2) * hsNorm (A - B) := by
    have hs0 : 0 ≤ Real.sqrt ((n + ℓ : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hh0 : 0 ≤ hsNorm (A - B) := Real.sqrt_nonneg _
    calc hsNorm R ≤ Real.sqrt ((n + ℓ : ℕ) : ℝ) * ‖R‖ :=
          (allard52_gpa_hsNorm_bounds (n + ℓ) (n + ℓ) R R).2.1
      _ ≤ Real.sqrt ((n + ℓ : ℕ) : ℝ) * (K * L₀ * ‖A - B‖) := by gcongr
      _ ≤ Real.sqrt ((n + ℓ : ℕ) : ℝ) * (K * L₀ * hsNorm (A - B)) := by
          gcongr; exact (allard52_gpa_hsNorm_bounds n ℓ (A - B) (A - B)).1
      _ = (Real.sqrt ((n + ℓ : ℕ) : ℝ) * K) * L₀ * hsNorm (A - B) := by ring
      _ ≤ Cg * L₀ * hsNorm (A - B) := by gcongr; linarith
      _ ≤ (Real.sqrt 3 - Real.sqrt 2) * hsNorm (A - B) := by gcongr
  -- Steps 6–8: `Π(A) - Π(B) = D(A - B) + R` with `|D(A - B)|² = 2|A - B|²` [S2].
  have hsum : (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection -
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection =
      D (A - B) + R := by
    rw [hRdef]; abel
  rw [hsum]
  exact perturb (n + ℓ) (n + ℓ) n ℓ (D (A - B)) R (A - B) (hD (A - B)) hRb
/-- Simon Ch. 5, proof of Theorem 5.2 (pp. 123–124): the linear algebra of graph planes.  For
`n ≥ 1` there is `L₀ = L₀(n, ℓ) ∈ (0, 1/4]` such that, with `P_q(A)` the orthogonal projection onto
`q(Γ_A)`, `Γ_A = {(v, A v) : v ∈ ℝⁿ}`, `|·|` the Hilbert–Schmidt norm and `‖·‖` the operator norm:
(1) (Gp) `|A − B|² ≤ |P_q(A) − P_q(B)|² ≤ 3 |A − B|²` if `|A|, |B| ≤ L₀`;
(2) `|A|² ≤ |P_q(A) − p_{q(ℝⁿ × {0})}|²` if `|A| ≤ L₀`;
(3) (Nor) `|y − A x| ≤ 2 |w − P_q(A) w|` for `w = q(x, y)` if `‖A‖ ≤ 1`;
(4) `‖A‖ ≤ |A| ≤ √n ‖A‖`; (5) every `n`-plane is `q(ℝⁿ × {0})` for some `q`;
(6) `A ↦ P_q(A)` is continuous.
`L₀` is the constant of the bi-Lipschitz estimate for the unrotated projection `Π(A) = p_{Γ_A}`.
Since `P_q(A) = q Π(A) q⁻¹` and conjugation by `q` preserves `|·|`, that estimate gives (1), and
(2) is its case `B = 0`, as `Γ_0 = ℝⁿ × {0}`; (6) holds because `Π` is `C²`. -/
theorem allard52_graph_plane_algebra : ∀ (n ℓ : ℕ), 1 ≤ n → ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 / 4 ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A B : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNorm B ≤ L₀ → hsNormSq (A - B) ≤ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map q.toLinearEquiv.toLinearMap).starProjection) ∧ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map q.toLinearEquiv.toLinearMap).starProjection) ≤ 3 * hsNormSq (A - B)) ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNormSq A ≤ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - (rotatedPlane q).starProjection)) ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (y : Rn ℓ), ‖A‖ ≤ 1 → ‖y - A x‖ ≤ 2 * ‖q (graphPoint x y) - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection (q (graphPoint x y))‖) ∧ (∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ hsNorm A ∧ hsNorm A ≤ Real.sqrt n * ‖A‖) ∧ (∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ∃ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, rotatedPlane q = T) ∧ (∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, Continuous fun A : Rn n →L[ℝ] Rn ℓ => ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection) := by
  intro n ℓ _
  -- `L₀` from the bi-Lipschitz estimate for the unrotated graph projection `Π(A) = p_{Γ_A}`.
  obtain ⟨L₀, hL₀, hL₀le, hbil⟩ := Submission.allard52_gpa_graphProj_bilipschitz n ℓ
  -- `p_{q(K)} − p_{q(K')} = q (p_K − p_{K'}) q⁻¹` has the Hilbert–Schmidt norm of `p_K − p_{K'}`.
  have hconj : ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (K K' : Submodule ℝ (Amb n ℓ)),
      hsNormSq ((K.map q.toLinearEquiv.toLinearMap).starProjection -
        (K'.map q.toLinearEquiv.toLinearMap).starProjection) =
      hsNormSq (K.starProjection - K'.starProjection) := by
    intro q K K'
    obtain ⟨hmap, hhs⟩ := Submission.allard52_gpa_isometry_conj n ℓ q
    rw [hmap, hmap, ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp, hhs]
  refine ⟨L₀, hL₀, hL₀le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) (Gp) for `P_q`, from (Gp) for `Π`.
    intro q A B hA hB
    rw [hconj]
    exact hbil A B hA hB
  · -- (2) `q(ℝⁿ × {0}) = q(Γ_0)` and `|0| = 0 ≤ L₀`, so this is (Gp) with `B = 0`.
    intro q A hA
    have h0 : hsNorm (0 : Rn n →L[ℝ] Rn ℓ) ≤ L₀ := by
      simpa [hsNorm, hsNormSq] using hL₀.le
    have h := (hbil A 0 hA h0).1
    rw [sub_zero] at h
    rw [rotatedPlane, ← Submission.allard52_gpa_span_graph_zero n ℓ, hconj]
    exact h
  · -- (3) (Nor)
    exact Submission.allard52_gpa_graph_normal_bound n ℓ
  · -- (4) `‖A‖ ≤ |A| ≤ √n ‖A‖`
    intro A
    obtain ⟨h1, h2, -⟩ := Submission.allard52_gpa_hsNorm_bounds n ℓ A 0
    exact ⟨h1, h2⟩
  · -- (5) every `n`-plane is a rotated coordinate plane
    exact Submission.allard52_gpa_exists_rotatedPlane_eq n ℓ
  · -- (6) `P_q(A) = q Π(A) q⁻¹`, and `Π` is continuous (indeed `C²`).
    intro q
    obtain ⟨hmap, -⟩ := Submission.allard52_gpa_isometry_conj n ℓ q
    exact (continuous_const.clm_comp
      ((Submission.allard52_gpa_graphProj_smooth n ℓ).1.continuous.clm_comp continuous_const)).congr
      fun A => (hmap _).symm

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

theorem allard52_amcl_radial_cutoff_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ) (R t : ℝ), 0 < t → t < R → IntegrableOn f (closedBall y R) μ → (∀ k, Continuous (φ k)) → (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) → (∀ k u, u ≤ 1 → φ k u = 1) → (∀ k u, 1 + ε k ≤ u → φ k u = 0) → Tendsto ε atTop (𝓝 0) → Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * f x ∂μ) atTop (𝓝 (∫ x in closedBall y t, f x ∂μ)) := by
  intro n ℓ μ f y φ ε R t ht htR hf hφc hφb hφ1 hφ0 hε
  -- Step 1: eventually `ε k < R / t - 1`, i.e. `(1 + ε k) t < R`.
  have hδ : 0 < R / t - 1 := by
    rw [sub_pos, one_lt_div ht]
    exact htR
  have hev : ∀ᶠ k in atTop, ε k < R / t - 1 := hε.eventually (gt_mem_nhds hδ)
  -- Step 2: for such `k` the integrand vanishes off `B_R(y)`, so the whole-space integral is the
  -- integral against `ν = μ ⌞ B_R(y)` (no integrability needed).
  have heq : ∀ᶠ k in atTop, ∫ x in closedBall y R, φ k (‖x - y‖ / t) * f x ∂μ =
      ∫ x, φ k (‖x - y‖ / t) * f x ∂μ := by
    filter_upwards [hev] with k hk
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have hkt : (1 + ε k) * t < R := (lt_div_iff₀ ht).1 (by linarith)
    have hk1 : 1 + ε k ≤ ‖x - y‖ / t := by
      rw [le_div_iff₀ ht]
      linarith
    rw [hφ0 k _ hk1, zero_mul]
  -- Step 3: the target is the `ν`-integral of `1_{B_t(y)} f`, since `B_t(y) ⊆ B_R(y)`.
  have htarget : ∫ x in closedBall y R, (closedBall y t).indicator f x ∂μ =
      ∫ x in closedBall y t, f x ∂μ := by
    rw [integral_indicator measurableSet_closedBall,
      Measure.restrict_restrict_of_subset (closedBall_subset_closedBall htR.le)]
  -- Steps 4-5: dominated convergence for `ν` with dominating function `‖f‖`.
  have hdct : Tendsto (fun k => ∫ x in closedBall y R, φ k (‖x - y‖ / t) * f x ∂μ) atTop
      (𝓝 (∫ x in closedBall y R, (closedBall y t).indicator f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) (fun k => ?_) hf.norm
      (fun k => ?_) ?_
    · -- (b) measurability: `x ↦ φ k (‖x - y‖ / t)` is continuous and `f` is `ν`-integrable.
      exact (((hφc k).comp ((continuous_norm.comp
        (continuous_id.sub continuous_const)).div_const t)).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
    · -- (c) domination: `0 ≤ φ k ≤ 1`.
      refine Eventually.of_forall (fun x => ?_)
      have hb := hφb k (‖x - y‖ / t)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2
    · -- (d) pointwise limit `1_{B_t(y)} f`.
      refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ closedBall y t
      · rw [indicator_of_mem hx]
        rw [mem_closedBall, dist_eq_norm] at hx
        have hle : ‖x - y‖ / t ≤ 1 := (div_le_one ht).2 hx
        have h1 : ∀ k, φ k (‖x - y‖ / t) * f x = f x := fun k => by
          rw [hφ1 k _ hle, one_mul]
        simp only [h1]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem hx]
        rw [mem_closedBall, dist_eq_norm, not_le] at hx
        have hu : 1 < ‖x - y‖ / t := (one_lt_div ht).2 hx
        have hev2 : ∀ᶠ k in atTop, ε k < ‖x - y‖ / t - 1 :=
          hε.eventually (gt_mem_nhds (by linarith))
        apply tendsto_const_nhds.congr'
        filter_upwards [hev2] with k hk
        rw [hφ0 k _ (by linarith), zero_mul]
  -- Step 6: conclusion.
  rw [← htarget]
  exact hdct.congr' heq
theorem allard52_am_fc_cutoff_facts : ∀ (φ : ℝ → ℝ) (ε : ℝ), 0 < ε → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u : ℝ, deriv φ u ≤ 0) ∧ (∀ u : ℝ, 1 + ε < u → deriv φ u = 0) ∧ Continuous (deriv φ) ∧ ∃ C : ℝ, ∀ u : ℝ, |deriv φ u| ≤ C := by
  intro φ ε hε hφ hanti h1 h0
  -- Step 1: `0 ≤ φ ≤ 1`, by monotonicity and the boundary values `φ (1 + ε) = 0`, `φ 1 = 1`.
  have hbd : ∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1 := by
    intro u
    constructor
    · rcases le_total (1 + ε) u with hu | hu
      · rw [h0 u hu]
      · rw [← h0 (1 + ε) le_rfl]
        exact hanti hu
    · rcases le_total u 1 with hu | hu
      · rw [h1 u hu]
      · rw [← h1 1 le_rfl]
        exact hanti hu
  -- Step 2: `φ' ≤ 0` because `φ` is nonincreasing.
  have hneg : ∀ u : ℝ, deriv φ u ≤ 0 := fun u => hanti.deriv_nonpos
  -- Step 3: `φ' = 0` on `(1 + ε, ∞)` and on `(-∞, 1)`, where `φ` is locally constant.
  have hright : ∀ u : ℝ, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) (fun v hv => h0 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  have hleft : ∀ u : ℝ, u < 1 → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu) (fun v hv => h1 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  -- Step 4: `φ'` is continuous because `φ` is `C¹`.
  have hcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- Step 5: `φ'` is continuous with support in `[1, 1 + ε]`, hence bounded.
  have hsupp : HasCompactSupport (deriv φ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 1) (b := 1 + ε)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact ⟨not_lt.mp fun h => hu (hleft u h), not_lt.mp fun h => hu (hright u h)⟩
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨hbd, hneg, hright, hcont, C, fun u => ?_⟩
  rw [← Real.norm_eq_abs]
  exact hC u
theorem allard52_am_fc_ball_integrable : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R S : ℝ), S < R → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ ∧ IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y S) μ ∧ IntegrableOn w (closedBall y S) μ := by
  intro n ℓ μ H w y R S hSR hR hH hw hwb
  -- Step 1: `B_S(y) ⊆ B̆_R(y) ⊆ B_R(y)`, so `μ(B_S(y)) < ∞`.
  have hSball : closedBall y S ⊆ ball y R := closedBall_subset_ball hSR
  have hSR' : closedBall y S ⊆ closedBall y R := closedBall_subset_closedBall hSR.le
  have hS : μ (closedBall y S) ≠ ⊤ := (lt_of_le_of_lt (measure_mono hSR') hR).ne
  -- Step 2: the constant `1` is integrable on a set of finite measure.
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ := integrableOn_const hS
  refine ⟨h1, ?_, ?_⟩
  · -- Step 3: `|(x - y) · H(x)| ≤ R |H(x)|` on `B_S(y)`, and `R |H|` is integrable there.
    have hHS : IntegrableOn H (closedBall y S) μ := hH.mono_set hSR'
    have hmeas : AEStronglyMeasurable (fun x => inner ℝ (x - y) (H x))
        (μ.restrict (closedBall y S)) :=
      Continuous.comp_aestronglyMeasurable₂ (g := fun u v : Amb n ℓ => inner ℝ u v)
        continuous_inner (continuous_id.sub continuous_const).aestronglyMeasurable
        hHS.aestronglyMeasurable
    refine Integrable.mono' (hHS.norm.const_mul R) hmeas ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall (fun x hx => ?_)
    rw [mem_closedBall, dist_eq_norm] at hx
    calc ‖inner ℝ (x - y) (H x)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
      _ ≤ R * ‖H x‖ := mul_le_mul_of_nonneg_right (hx.trans hSR.le) (norm_nonneg _)
  · -- Step 4: `w` is a.e.-strongly measurable on `B_S(y)` and `|w| ≤ 1` a.e. there.
    have hwS : AEStronglyMeasurable w (μ.restrict (closedBall y S)) :=
      hw.mono_measure (Measure.restrict_mono hSball le_rfl)
    refine Integrable.mono' h1 hwS ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    filter_upwards [hwb] with x hx hxS
    obtain ⟨hw0, hw1⟩ := hx (hSball hxS)
    rw [Real.norm_eq_abs, abs_of_nonneg hw0]
    exact hw1

/-- **Simon Ch. 4, 4.1–4.5** (monotonicity and the annular conical estimate for one fixed cutoff).
Let `1 ≤ n < p`, `R, Λ > 0`, `0 < ε ≤ 1` and `κ = (p − n)/(4p)`.  Let `μ(B_R(y)) < ∞`, let `H` be
`μ`-integrable on `B_R(y)` with `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ κΛ`, let `w` be a.e. strongly
measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. there, and let `φ` be a nonincreasing `C¹` cutoff
(`φ = 1` on `(−∞, 1]`, `φ = 0` on `[1 + ε, ∞)`) satisfying the radial first-variation identity at
every `ρ > 0` with `(1 + ε)ρ < R`.  Write `r_x = |x − y|`, `I(t) = ∫ φ(r_x/t) dμ`,
`E(t) = ∫ φ(r_x/t) (x − y) · H dμ`, `a = E/t^{n+1}/(1 + I/tⁿ)`, `G(t) = ∫₀ᵗ a` and
`Φ(t) = e^{−G(t)} (1 + I(t)/tⁿ)`.  Then
(1) for `t > 0` with `(1 + ε)t < R`, `a` is continuous at `t` and `|a(t)| ≤ 2κΛR⁻¹ (t/R)^{−n/p}`;
(2) for `0 < s ≤ r` with `(1 + ε)r < R`, `Φ(s) ≤ Φ(r)` and
`∫_{B_r(y) \ B̆_{(1+ε)s}(y)} w r_x⁻ⁿ dμ ≤ e^{Λ/2} (Φ(r) − Φ(s))`.
Proof: the cutoff calculus makes `I` differentiable and `E` and
`Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w dμ ≥ 0` continuous, and the radial identity, split by
linearity, reads `n I − t I' + t Q = −E`.  Hölder at radius `(1 + ε)t` and the absorption
`A^{1−1/p} ≤ 1 + A` give (1).  The integrating factor gives `Φ(r) − Φ(s) = ∫ₛʳ e^{−G} Q/tⁿ ≥ 0`;
as `|G| ≤ Λ/2`, `∫ₛʳ Q/tⁿ ≤ e^{Λ/2} (Φ(r) − Φ(s))`, and the annular Tonelli bound concludes. -/
theorem allard52_am_fixed_cutoff : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ ε : ℝ) (φ : ℝ → ℝ) (I E a : ℝ → ℝ), 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ ρ : ℝ, 0 < ρ → (1 + ε) * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t, E t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧ |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → (1 + ε) * r < R → Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) ≤ Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) ∧ ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n))) := by
  intro n ℓ hn p hnp μ H w y R Λ ε φ I E a hR hΛ hε hε1 hμR hHR hLp hw hw01 hφ hanti hφ1 hφ0
    hrad hI hE ha
  -- Notation: `r_x = ‖x − y‖`, `I'(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) dμ` and
  -- `Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w dμ`.
  set I' : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t with hI'
  set Q : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t with hQ
  -- Step 0: constants, `1 < p` and `1 + ε > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := by linarith
  have hp : 0 < p := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  -- Step 1: cutoff facts, `0 ≤ φ ≤ 1`.
  obtain ⟨hφ01, -, -, -, -⟩ :=
    Submission.allard52_am_fc_cutoff_facts φ ε hε hφ hanti hφ1 hφ0
  -- Steps 3(c), 5, 6: the radial split, `I ≥ 0` and `∫ (r_x/t) φ'(r_x/t) w dμ ≤ 0`.
  have hsplit := Submission.allard52_am_fc_radial_split n ℓ μ w y R ε φ hε hμR hw hw01 hφ hanti
    hφ1 hφ0
  -- Step 4: regularity from the cutoff calculus at `t ∈ (0, R/(1 + ε))`, with
  -- `S = ((1 + ε) t + R)/2` and `T = 1 + ε`, for `f = 1`, `(x − y) · H` and `w`.
  have hcalc : ∀ t, 0 < t → (1 + ε) * t < R →
      HasDerivAt I (I' t) t ∧ ContinuousAt E t ∧ ContinuousAt Q t := by
    intro t ht htR
    have hSR : ((1 + ε) * t + R) / 2 < R := by linarith
    have htS : (1 + ε) * t < ((1 + ε) * t + R) / 2 := by linarith
    obtain ⟨h1, hinner, hwS⟩ := Submission.allard52_am_fc_ball_integrable n ℓ μ H w y R
      (((1 + ε) * t + R) / 2) hSR hμR hHR hw hw01
    have hd1 : HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * 1 ∂μ)
        (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * 1 ∂μ) / t) t :=
      (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y (fun _ => (1 : ℝ)) φ
        (((1 + ε) * t + R) / 2) (1 + ε) t h1 hφ h1ε hφ0 ht htS).2.2
    simp only [mul_one] at hd1
    refine ⟨?_, ?_, ?_⟩
    · rw [show I = fun s => ∫ x, φ (‖x - y‖ / s) ∂μ from funext hI]
      exact hd1
    · rw [show E = fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ from funext hE]
      exact (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y
        (fun x => inner ℝ (x - y) (H x)) φ (((1 + ε) * t + R) / 2) (1 + ε) t hinner hφ h1ε hφ0
        ht htS).1
    · exact (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y w φ
        (((1 + ε) * t + R) / 2) (1 + ε) t hwS hφ h1ε hφ0 ht htS).2.1.neg.div continuousAt_id
        ht.ne'
  -- Step 8: the bound on `a` and its continuity, which is (1).
  have hbound : ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧
      |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
    intro t ht htR
    have hI0 : 0 ≤ I t := by
      rw [hI t]
      exact (hsplit t ht htR).2.1
    have hpos : 0 < 1 + I t / t ^ n := by
      have : 0 ≤ I t / t ^ n := div_nonneg hI0 (pow_nonneg ht.le n)
      linarith
    refine ⟨?_, ?_⟩
    · rw [show a = fun t => E t / t ^ (n + 1) / (1 + I t / t ^ n) from funext ha]
      exact ((hcalc t ht htR).2.1.div (continuous_pow (n + 1)).continuousAt
        (pow_ne_zero _ ht.ne')).div (continuousAt_const.add
          ((hcalc t ht htR).1.continuousAt.div (continuous_pow n).continuousAt
            (pow_ne_zero _ ht.ne'))) hpos.ne'
    -- Steps 2 and 7: Hölder at radius `(1 + ε) t ≤ R` with `ψ(x) = φ(r_x/t)`.
    · have ht1 : (1 + ε) * t ≤ R := htR.le
      have hBR : closedBall y ((1 + ε) * t) ⊆ closedBall y R := closedBall_subset_closedBall ht1
      obtain ⟨hHfin, hNb⟩ :=
        Submission.allard52_am_fc_lp_scale n ℓ p hnp μ H y R Λ ((1 + ε) * t) hR hΛ ht1 hLp
      have hhol : |E t| ≤ (1 + ε) * t *
          (∫⁻ x in closedBall y ((1 + ε) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) *
            I t ^ (1 - 1 / p) := by
        rw [hE t, hI t]
        refine Submission.aal_curvature_pairing_holder_bound n ℓ p hp1 μ H
          (fun x => φ (‖x - y‖ / t)) y ((1 + ε) * t) (mul_nonneg h1ε.le ht.le)
          ((measure_mono hBR).trans_lt hμR) (hHR.mono_set hBR) hHfin
          (hφ.continuous.comp ((continuous_id.sub continuous_const).norm.div_const t)
            ).aestronglyMeasurable (fun x => hφ01 _) (fun x hx => hφ0 _ ?_)
        exact (le_div_iff₀ ht).2 hx.le
      rw [ha t]
      exact Submission.allard52_am_fc_a_bound n hn p R Λ ε t (I t) (E t) _ hnp hR hΛ hε hε1 ht
        hI0 (Real.rpow_nonneg ENNReal.toReal_nonneg _) hNb hhol
  refine ⟨hbound, ?_⟩
  intro s r hs hsr hrR
  -- Step 9: the integrating factor on `(0, R/(1 + ε))`, with `β = n/p` and
  -- `M = 2κΛR⁻¹/R^{−n/p}`, so that `M t^{−β} = 2κΛR⁻¹ (t/R)^{−n/p}`.
  have hmem : ∀ t, t ∈ Ioo 0 (R / (1 + ε)) → 0 < t ∧ (1 + ε) * t < R := fun t ht =>
    ⟨ht.1, by rw [mul_comm]; exact (lt_div_iff₀ h1ε).1 ht.2⟩
  have hab : ∀ t ∈ Ioo 0 (R / (1 + ε)),
      |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R / R ^ (-((n : ℝ) / p)) * t ^ (-((n : ℝ) / p)) := by
    intro t ht
    obtain ⟨ht0, htR⟩ := hmem t ht
    calc |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) :=
          (hbound t ht0 htR).2
      _ = _ := by
          rw [Real.div_rpow ht0.le hR.le]
          ring
  have hIF := Submission.allard52_am_integrating_factor n I I' E Q a (R / (1 + ε))
    (2 * ((p - n) / (4 * p)) * Λ / R / R ^ (-((n : ℝ) / p))) ((n : ℝ) / p)
    ((div_lt_one hp).2 hnp)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).1)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).2.1)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).2.2)
    (fun t ht => by rw [hI t]; exact (hsplit t (hmem t ht).1 (hmem t ht).2).2.1)
    (fun t ht => by
      obtain ⟨ht0, htR⟩ := hmem t ht
      have h := hrad t ht0 htR
      rw [(hsplit t ht0 htR).1] at h
      rw [hI t, hE t, ← h, hI', hQ]
      field_simp
      ring)
    ha hab s r hs hsr (by rw [lt_div_iff₀ h1ε, mul_comm]; exact hrR)
  -- On `[s, r]`: `0 < t`, `(1 + ε) t < R`, and `Q(t)/tⁿ ≥ 0` (step 6).
  have hIcc : ∀ t ∈ Icc s r, 0 < t ∧ (1 + ε) * t < R := fun t ht =>
    ⟨hs.trans_le ht.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 h1ε.le) hrR⟩
  have hQnn : ∀ t ∈ Icc s r, 0 ≤ Q t / t ^ n := fun t ht => by
    obtain ⟨ht0, htR⟩ := hIcc t ht
    exact div_nonneg (div_nonneg (neg_nonneg.2 (hsplit t ht0 htR).2.2) ht0.le)
      (pow_nonneg ht0.le n)
  refine ⟨?_, ?_⟩
  -- Step 11: monotonicity, as the integrand `exp(−G) Q/tⁿ` is `≥ 0` on `[s, r]`.
  · rw [← sub_nonneg, hIF]
    exact intervalIntegral.integral_nonneg hsr fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hQnn t ht)
  -- Step 12: `|G| ≤ Λ/2` (step 10) gives `Q/tⁿ ≤ e^{Λ/2} e^{−G} Q/tⁿ` on `[s, r]`; integrate and
  -- apply the annular Tonelli bound.
  · have hG := Submission.allard52_am_fc_primitive n p R Λ ε a hnp hR hΛ hε hbound
    have hcQ : ContinuousOn (fun t => Q t / t ^ n) (uIcc s r) := by
      rw [uIcc_of_le hsr]
      intro t ht
      obtain ⟨ht0, htR⟩ := hIcc t ht
      exact ((hcalc t ht0 htR).2.2.div (continuous_pow n).continuousAt
        (pow_ne_zero n ht0.ne')).continuousWithinAt
    have hcGQ : ContinuousOn (fun t => Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n))
        (uIcc s r) := by
      rw [uIcc_of_le hsr]
      intro t ht
      obtain ⟨ht0, htR⟩ := hIcc t ht
      exact ((hG t ht0 htR).1.neg.rexp.mul ((hcalc t ht0 htR).2.2.div
        (continuous_pow n).continuousAt (pow_ne_zero n ht0.ne'))).continuousWithinAt
    have hmono : ∫ t in s..r, Q t / t ^ n ≤
        ∫ t in s..r, Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) := by
      refine intervalIntegral.integral_mono_on hsr hcQ.intervalIntegrable
        (hcGQ.intervalIntegrable.const_mul _) fun t ht => ?_
      obtain ⟨ht0, htR⟩ := hIcc t ht
      have h1 : 1 ≤ Real.exp (Λ / 2) * Real.exp (-∫ τ in (0)..t, a τ) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [le_abs_self (∫ τ in (0)..t, a τ), (hG t ht0 htR).2])
      calc Q t / t ^ n = 1 * (Q t / t ^ n) := (one_mul _).symm
        _ ≤ Real.exp (Λ / 2) * Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n) :=
          mul_le_mul_of_nonneg_right h1 (hQnn t ht)
        _ = Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) := mul_assoc _ _ _
    rw [intervalIntegral.integral_const_mul, ← hIF] at hmono
    exact (Submission.allard52_am_annular_tonelli n ℓ μ w y φ R ε s r hε hμR hw hw01 hφ hanti hφ1
      hφ0 hs hsr hrR).trans (ENNReal.ofReal_le_ofReal hmono)

/-- **Simon Ch. 4, 4.5–4.8** (steps 1 and 5–9 of the annular monotonicity argument: the passage
`ε → 0` in the radial cutoff).  Let `n ≥ 1`, `p > n`, `R > 0`, `0 < Λ ≤ 1`, `κ = (p − n)/(4p)`;
let `μ(B_R(y)) < ∞`, `H` be `μ`-integrable on `B_R(y)` with `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ κΛ`,
`0 ≤ w ≤ 1` `μ`-a.e. in `B̆_R(y)`, and assume the radial first-variation identity for all `C¹`
cutoffs.  Then some `F` (here `F = exp(−G)`, `G(t) = ∫₀ᵗ a₀`,
`a₀(t) = t^{−n−1} ∫_{B_t(y)} (x − y)·H dμ / (1 + t^{−n} μ(B_t(y)))`) satisfies, with
`Φ(r) = F(r) r^{−n} μ(B_r(y)) + F(r) − 1`:
(i) `e^{−Λ} ≤ F ≤ e^{Λ}` and `|F(r) − 1| ≤ Λ (r/R)^{1−n/p}` on `(0, R)`;
(ii) `Φ` is nondecreasing on `(0, R)`, and
`∫_{B_r(y) \ B_s(y)} w/|x − y|ⁿ dμ ≤ e^{Λ} (Φ(r) − Φ(s))` for `0 < s ≤ r < R`.
Proof: `allard52_am_fixed_cutoff` for the cutoffs `φ k` of `allard52_amcl_cutoff_sequence`
gives the bound `|a_k| ≤ 2κΛR⁻¹(τ/R)^{−n/p}`, the monotonicity of
`Φ̃_k = exp(−∫₀ a_k)(1 + I_k/tⁿ)` and the per-`k` annular estimate; dominated convergence
(`allard52_amcl_radial_cutoff_tendsto`) gives `I_k(t) → μ(B_t(y))`, `E_k(t) → E₀(t)`, hence
`a_k(t) → a₀(t)`; `allard52_amcl_interval_limit` gives `∫₀ᵗ a_k → G(t)` and
`|G(t)| ≤ (Λ/2)(t/R)^{1−n/p}`, whence (i) by `|eᶻ − 1| ≤ 2|z|`; the monotonicity passes to the
limit, and Fatou's lemma (`allard52_amcl_annular_lintegral_le`) gives the annular bound with
`e^{Λ/2} ≤ e^{Λ}`. -/
theorem allard52_am_cutoff_limit : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1)))) := by
  intro n ℓ hn p hp μ H w y R Λ hR hΛ hΛ1 hμR hH hHp hw hw01 hrad
  -- Steps 1–2: `C¹` nonincreasing cutoffs, `1` on `(-∞, 1]` and `0` on `[1 + ε k, ∞)`, `ε k → 0`.
  obtain ⟨φ, ε, hε, hεt, hφC, hφA, hφ01, hφ1, hφ0⟩ := Submission.allard52_amcl_cutoff_sequence
  -- The cutoff quantities `I_k, E_k, a_k` and their limits `m, E₀, a₀, G` and `F = exp(−G)`.
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ → ℝ, ∀ k t,
      E k t = ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t = E k t / t ^ (n + 1) / (1 + I k t / t ^ n) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = (μ (closedBall y t)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ → ℝ, ∀ t,
      E₀ t = ∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ := ⟨_, fun _ => rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t = E₀ t / t ^ (n + 1) / (1 + m t / t ^ n) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ∫ τ in (0)..t, a₀ τ := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t, F t = Real.exp (-G t) := ⟨_, fun _ => rfl⟩
  -- Step 3: `fixed_cutoff` for every `k`, the radial identity being the hypothesis at `T = 1 + ε k`.
  have hfix := fun k => Submission.allard52_am_fixed_cutoff n ℓ hn p hp μ H w y R Λ (ε k) (φ k)
    (I k) (E k) (a k) hR hΛ (hε k).1 (hε k).2 hμR hH hHp hw hw01 (hφC k) (hφA k) (hφ1 k)
    (hφ0 k) (fun ρ hρ hρR => hrad (φ k) (1 + ε k) ρ (hφC k) (hφ1 k) (hφ0 k) hρ hρR) (hI k)
    (hE k) (ha k)
  -- `(1 + ε k) t < R` for all large `k`, whenever `t < R`.
  have hev : ∀ t, t < R → ∀ᶠ k in atTop, (1 + ε k) * t < R := by
    intro t ht
    have h : Tendsto (fun k => (1 + ε k) * t) atTop (𝓝 ((1 + 0) * t)) :=
      (hεt.const_add 1).mul_const t
    rw [add_zero, one_mul] at h
    exact h.eventually (eventually_lt_nhds ht)
  -- Step 5: dominated convergence at a fixed radius `t ∈ (0, R)`.
  have hint1 : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y R) μ := integrableOn_const hμR.ne
  have hintH : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y R) μ := by
    refine Integrable.mono' ((Integrable.norm hH).const_mul R)
      ((continuous_inner (𝕜 := ℝ)).comp_aestronglyMeasurable
        ((continuous_sub_right y).aestronglyMeasurable.prodMk
          (Integrable.aestronglyMeasurable hH))) ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hxR : ‖x - y‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
  have hIlim : ∀ t, 0 < t → t < R → Tendsto (fun k => I k t) atTop (𝓝 (m t)) := by
    intro t ht htR
    have h := Submission.allard52_amcl_radial_cutoff_tendsto n ℓ μ (fun _ => 1) y φ ε R t ht htR
      hint1 (fun k => (hφC k).continuous) hφ01 hφ1 hφ0 hεt
    simp only [mul_one, setIntegral_const, smul_eq_mul, measureReal_def] at h
    simpa only [hI, hm] using h
  have hElim : ∀ t, 0 < t → t < R → Tendsto (fun k => E k t) atTop (𝓝 (E₀ t)) := by
    intro t ht htR
    simpa only [hE, hE₀] using Submission.allard52_amcl_radial_cutoff_tendsto n ℓ μ
      (fun x => inner ℝ (x - y) (H x)) y φ ε R t ht htR hintH (fun k => (hφC k).continuous)
      hφ01 hφ1 hφ0 hεt
  have halim : ∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
    intro t ht htR
    have hm0 : 0 ≤ m t / t ^ n := div_nonneg (by rw [hm]; exact ENNReal.toReal_nonneg)
      (pow_nonneg ht.le n)
    rw [show (fun k => a k t) = fun k => E k t / t ^ (n + 1) / (1 + I k t / t ^ n) from
      funext fun k => ha k t, ha₀]
    exact ((hElim t ht htR).div_const (t ^ (n + 1))).div
      (((hIlim t ht htR).div_const (t ^ n)).const_add 1) (by linarith)
  -- Step 6: `∫₀ᵗ a_k → G(t)`, with `|G(t)| ≤ (Λ/2)(t/R)^{1−n/p}`, and `Φ̃_k(t) → F(t)(1 + m(t)/tⁿ)`.
  have hGlim : ∀ t, 0 < t → t < R → Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (G t)) ∧
      |G t| ≤ Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p) := by
    intro t ht htR
    rw [hG]
    refine Submission.allard52_amcl_interval_limit n p R Λ t a a₀ hp hR hΛ ht ?_
      (fun τ hτ hτt => halim τ hτ (lt_of_le_of_lt hτt htR))
    filter_upwards [hev t htR] with k hk
    intro τ hτ hτt
    exact (hfix k).1 τ hτ
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hτt (by linarith [(hε k).1])) hk)
  have hΦlim : ∀ t, 0 < t → t < R → Tendsto (fun k => Real.exp (-∫ τ in (0)..t, a k τ) *
      (1 + I k t / t ^ n)) atTop (𝓝 (F t * (1 + m t / t ^ n))) := by
    intro t ht htR
    rw [hF]
    exact (hGlim t ht htR).1.neg.rexp.mul (((hIlim t ht htR).div_const _).const_add 1)
  refine ⟨F, ?_, ?_⟩
  -- Step 7: conclusion (i).
  · rintro r ⟨hr0, hrR⟩
    have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
    have hrR1 : 0 ≤ r / R ∧ r / R ≤ 1 := ⟨div_nonneg hr0.le hR.le, (div_le_one hR).2 hrR.le⟩
    have hpow1 : (r / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one hrR1.1 hrR1.2 (sub_nonneg.2 ((div_le_one hp0).2 hp.le))
    have hGr := (hGlim r hr0 hrR).2
    have hGr' : |G r| ≤ Λ / 2 :=
      hGr.trans ((mul_le_mul_of_nonneg_left hpow1 (by linarith)).trans (mul_one _).le)
    obtain ⟨hGl, hGu⟩ := abs_le.1 hGr'
    rw [hF]
    refine ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith), ?_⟩
    calc |Real.exp (-G r) - 1| ≤ 2 * |-G r| :=
          Real.abs_exp_sub_one_le (by rw [abs_neg]; linarith)
      _ = 2 * |G r| := by rw [abs_neg]
      _ ≤ 2 * (Λ / 2 * (r / R) ^ (1 - (n : ℝ) / p)) := by linarith
      _ = Λ * (r / R) ^ (1 - (n : ℝ) / p) := by ring
  -- Steps 8–9: conclusion (ii).
  · intro s r hs hsr hrR
    have hsR : s < R := lt_of_le_of_lt hsr hrR
    have hr0 : 0 < r := lt_of_lt_of_le hs hsr
    -- Monotonicity of `Φ̃_k` passes to the limit.
    have hmono : F s * (1 + m s / s ^ n) ≤ F r * (1 + m r / r ^ n) :=
      le_of_tendsto_of_tendsto (hΦlim s hs hsR) (hΦlim r hr0 hrR) (by
        filter_upwards [hev r hrR] with k hk
        exact ((hfix k).2 s r hs hsr hk).1)
    have hD : (F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) -
        (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1) =
        F r * (1 + m r / r ^ n) - F s * (1 + m s / s ^ n) := by
      rw [hm, hm]; ring
    refine ⟨by linarith, ?_⟩
    -- Fatou's lemma along the annuli `B_r(y) \ B̆_{(1 + ε k) s}(y)`.
    have hann := Submission.allard52_amcl_annular_lintegral_le n ℓ μ
      (fun x => ENNReal.ofReal (w x / ‖x - y‖ ^ n)) y ε
      (fun k => Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..r, a k τ) * (1 + I k r / r ^ n) -
        Real.exp (-∫ τ in (0)..s, a k τ) * (1 + I k s / s ^ n))) s r
      (Real.exp (Λ / 2) * (F r * (1 + m r / r ^ n) - F s * (1 + m s / s ^ n))) hs hεt
      (((hΦlim r hr0 hrR).sub (hΦlim s hs hsR)).const_mul _) (by
        filter_upwards [hev r hrR] with k hk
        exact ((hfix k).2 s r hs hsr hk).2)
    rw [hD]
    exact hann.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (by linarith)) (sub_nonneg.2 hmono)))

/-- **Simon Ch. 4, 4.1–4.9 with the conical term (annular monotonicity; Ch. 5, 2.4).**  Let
`1 ≤ n < p`, let `V` have generalized mean curvature `H` in the open set `U`, let `R > 0` with
`B_R(y) ⊆ U`, and assume that `μ_V`-a.e. on `B̆_R(y)` the tangent projection `p_x` is the orthogonal
projection onto an `n`-plane, that `x ↦ p_x` is a.e. strongly measurable on `B̆_R(y)`, `0 < Λ ≤ 1`
and `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ_V)^{1/p} ≤ κΛ` with `κ = (p − n)/(4p)`.  Then there is `F` with
`e^{−Λ} ≤ F ≤ e^Λ` and `|F(r) − 1| ≤ Λ (r/R)^{1−n/p}` on `(0, R)` such that
`Φ(r) = F(r) r⁻ⁿ μ_V(B_r(y)) + F(r) − 1` is nondecreasing on `(0, R)`,
`∫_{B_r(y) \ B_s(y)} |x − y − p_x(x − y)|² / |x − y|^{n+2} dμ_V ≤ e^Λ (Φ(r) − Φ(s))`, and the
density `Θⁿ(μ_V, y) = t` exists with `ω_n t ≤ Φ(r)` for every `r ∈ (0, R)`.
Proof: `μ_V(B_R(y)) < ∞` and `H ∈ L¹(μ_V⌞B_R(y))` because `B_R(y) ⊆ U` is compact.  The conical
weight `ν(x) = |x − y − p_x(x − y)|² / |x − y|²` is a.e. strongly measurable on `B̆_R(y)`, and
`0 ≤ ν ≤ 1` there since `v − p_P v = p_{P^⊥} v`.  The radial first-variation identity
`allard52_am_radial_identity` is then the hypothesis of the cutoff limit
`allard52_am_cutoff_limit` for `μ = μ_V` and `w = ν`, which gives (i) and (ii) because
`ν(x) |x − y|⁻ⁿ = |x − y − p_x(x − y)|² / |x − y|^{n+2}`; `allard52_am_center_density` with
`α = 1 − n/p > 0` gives (iii). -/
theorem allard52_annular_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1)))) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * t ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1 := by
  intro n ℓ hn p hp U _hU V H hH y R Λ hR hBR hrank hmeas hΛ hΛ1 hsmall
  -- Step 0(a): `μ_V(B_R(y)) < ∞`, since `B_R(y)` is a compact subset of `U` and `θ` is integrable
  -- on `M ∩ B_R(y)`.
  have hfin : V.weight (closedBall y R) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y R) hBR).setLIntegral_lt_top
  -- Step 0(b): `H` is `μ_V`-integrable on the compact set `B_R(y) ⊆ U`.
  have hHint : IntegrableOn H (closedBall y R) V.weight :=
    hH.1.integrableOn_compact_subset hBR (isCompact_closedBall y R)
  -- The conical weight `ν(x) = |x − y − p_x(x − y)|² / |x − y|²` (with `ν(y) = 0`).
  set w : Amb n ℓ → ℝ := fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 with hw
  -- Step 0(e): `ν` is a.e. strongly measurable on `B̆_R(y)`, because `x ↦ p_x` is.
  have hwm : AEStronglyMeasurable w (V.weight.restrict (ball y R)) := by
    have hd : AEStronglyMeasurable (fun x : Amb n ℓ => x - y) (V.weight.restrict (ball y R)) :=
      (continuous_sub_right y).aestronglyMeasurable
    have hpx : AEStronglyMeasurable (fun x => V.tangentProj x (x - y))
        (V.weight.restrict (ball y R)) :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => A v)
        isBoundedBilinearMap_apply.continuous hmeas hd
    exact ((hd.sub hpx).norm.pow 2).div₀ (hd.norm.pow 2)
  -- Step 0(d): `0 ≤ ν ≤ 1` a.e. on `B̆_R(y)`: where `p_x = p_P`, `v − p_P v = p_{P^⊥} v` has
  -- `|p_{P^⊥} v| ≤ |v|`.
  have hw01 : ∀ᵐ x ∂V.weight, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1 := by
    filter_upwards [hrank] with x hx hxB
    obtain ⟨P, -, hP⟩ := hx hxB
    have hle : ‖(x - y) - V.tangentProj x (x - y)‖ ≤ ‖x - y‖ := by
      rw [hP, ← Submodule.starProjection_orthogonal_val]
      exact Pᗮ.norm_starProjection_apply_le _
    refine ⟨by positivity, div_le_one_of_le₀ ?_ (by positivity)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- Steps 1–8: the cutoff limit, fed with the radial first-variation identity of step 2.
  obtain ⟨F, hF, hΦ⟩ := Submission.allard52_am_cutoff_limit n ℓ hn p hp V.weight H w y R Λ hR hΛ
    hΛ1 hfin hHint hsmall hwm hw01
    (Submission.allard52_am_radial_identity n ℓ U V H hH y R hBR hrank)
  -- Step 9: the density at the centre, with the decay exponent `α = 1 − n/p > 0`.
  have hα : 0 < 1 - (n : ℝ) / p := by
    have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
    rw [sub_pos, div_lt_one hp0]
    exact hp
  obtain ⟨t, ht0, hdens, htΦ⟩ := Submission.allard52_am_center_density n ℓ V.weight y F R Λ
    (1 - (n : ℝ) / p) hR hα hfin hF fun s r hs hsr hr => (hΦ s r hs hsr hr).1
  refine ⟨F, hF, fun s r hs hsr hr => ⟨(hΦ s r hs hsr hr).1, ?_⟩, t, ht0, hdens, htΦ⟩
  -- Step 8: the integrands agree, `ν(x) |x − y|⁻ⁿ = |x − y − p_x(x − y)|² / |x − y|^{n+2}`
  -- (both sides vanish at `x = y`).
  have hg : ∀ x, ‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) =
      w x / ‖x - y‖ ^ n := fun x => by
    rw [hw, div_div, ← pow_add, add_comm 2 n]
  simp_rw [hg]
  exact (hΦ s r hs hsr hr).2

/-- Simon Ch. 4, 4.9 and 4.10(1), under the hypotheses 2.3 with `0 < δ ≤ κ = (p − n)/(4p)` and
`μ_V`-a.e. `n`-dimensional, strongly measurable tangent planes: every density value
`Θⁿ(μ_V, y) = t` at a point `y ∈ spt V ∩ B̆_ρ(0)` satisfies `t ≥ 1`.  With `Λ = δ/κ ∈ (0, 1]` and
`α = 1 − n/p`, the annular monotonicity at each `x ∈ B̆_ρ(0)` and radius `R ≤ ρ − |x|` gives a density
`Θ(x)` with `ω_n Θ(x) ≤ (1 + Λ (r/R)^α) r⁻ⁿ μ_V(B_r(x)) + Λ (r/R)^α` for `0 < r < R`.  Hence `Θ` is
upper semicontinuous on `B̆_ρ(0)`, `Θ = θ ≥ 1` `μ_V`-a.e., and an open ball about `y` on which
`Θ < 1` would be `μ_V`-null, contradicting `y ∈ spt μ_V`. -/
theorem allard52_support_density_ge_one : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ (p - n) / (4 * p) → V.AllardHypotheses H p δ ρ → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) → ∀ y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ, ∀ t : ℝ, V.HasDensity y t → 1 ≤ t := by
  intro n ℓ hn p hp U hU V H δ ρ hδ hδκ hA hmeas htan hdens y hy t ht
  /- Step 1: uniqueness of densities, and `ω_n > 0`. -/
  have hunique : ∀ (x : Amb n ℓ) (a b : ℝ), V.HasDensity x a → V.HasDensity x b →
      ENNReal.ofReal a = ENNReal.ofReal b :=
    fun _ _ _ ha hb => tendsto_nhds_unique ha hb
  have hdeq : ∀ (x : Amb n ℓ) (a b : ℝ), V.HasDensity x a → V.HasDensity x b → 0 ≤ a → 0 ≤ b →
      a = b :=
    fun x a b ha hb ha0 hb0 => (ENNReal.ofReal_eq_ofReal_iff ha0 hb0).1 (hunique x a b ha hb)
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    positivity
  /- Constants: `κ = (p - n)/(4p)`, `Λ = δ/κ ∈ (0, 1]`, `α = 1 - n/p ∈ (0, 1)`. -/
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hκ : 0 < (p - n) / (4 * p) := div_pos (by linarith) (by linarith)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = δ / ((p - n) / (4 * p)) := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by
    rw [hΛdef]
    exact div_pos hδ hκ
  have hΛ1 : Λ ≤ 1 := by
    rw [hΛdef]
    exact (div_le_one hκ).2 hδκ
  have hκΛ : (p - n) / (4 * p) * Λ = δ := by
    rw [hΛdef]
    exact mul_div_cancel₀ δ hκ.ne'
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - (n : ℝ) / p := ⟨_, rfl⟩
  have hα : 0 < α := by
    rw [hαdef, sub_pos, div_lt_one hp0]
    exact hp
  have hfin : V.weight (closedBall 0 ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA.2.2.2.2.2.1
  /- Step 2: the monotonicity inequality (2.1) at points of `B̆_ρ(0)`, for every admissible
  radius `R ≤ ρ - ‖x‖`, from the sibling subball bounds and annular monotonicity. -/
  have hmono : ∀ (x : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ - ‖x‖ →
      ∃ θ : ℝ, 0 ≤ θ ∧ V.HasDensity x θ ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * θ ≤
        (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R) ^ α := by
    intro x R hR hRx
    have hRρ : R ≤ ρ := by linarith [norm_nonneg x]
    have hsub : closedBall x R ⊆ closedBall 0 ρ := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall_zero_iff]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ρ := by linarith
    obtain ⟨hU', -, hLp, -⟩ :=
      Submission.aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA x R hR hRρ hsub
    obtain ⟨F, hF, -, θ, hθ0, hθd, hθ⟩ :=
      Submission.allard52_annular_monotonicity n ℓ hn p hp U hU V H hA.2.1 x R Λ hR hU'
        (htan.mono fun z hz _ => hz) hmeas.restrict hΛ0 hΛ1 (by rw [hκΛ]; exact hLp)
    rw [← hαdef] at hF
    refine ⟨θ, hθ0, hθd, fun r hr => ?_⟩
    obtain ⟨-, -, hFr⟩ := hF r hr
    have hm : 0 ≤ (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal := by
      have := hr.1
      positivity
    have hFle : F r ≤ 1 + Λ * (r / R) ^ α := by
      linarith [le_abs_self (F r - 1)]
    calc unitBallVolume n * θ
        ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal + F r - 1 := hθ r hr
      _ = F r * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) + (F r - 1) := by ring
      _ ≤ (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
            Λ * (r / R) ^ α :=
          add_le_add (mul_le_mul_of_nonneg_right hFle hm) (by linarith [le_abs_self (F r - 1)])
  -- existence of a (nonnegative) density at every point of `B̆_ρ(0)`
  have hex : ∀ x : Amb n ℓ, x ∈ ball (0 : Amb n ℓ) ρ → ∃ θ : ℝ, 0 ≤ θ ∧ V.HasDensity x θ := by
    intro x hx
    have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
    obtain ⟨θ, hθ0, hθ, -⟩ := hmono x (ρ - ‖x‖) (by linarith) le_rfl
    exact ⟨θ, hθ0, hθ⟩
  -- (2.1) holds for *every* nonnegative density value, by uniqueness
  have hineq : ∀ (x : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ - ‖x‖ → ∀ θ : ℝ, 0 ≤ θ →
      V.HasDensity x θ → ∀ r ∈ Ioo 0 R, unitBallVolume n * θ ≤
        (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R) ^ α := by
    intro x R hR hRx θ hθ0 hθ r hr
    obtain ⟨θ₁, hθ₁0, hθ₁, hθ₁ineq⟩ := hmono x R hR hRx
    rw [hdeq x θ θ₁ hθ hθ₁ hθ0 hθ₁0]
    exact hθ₁ineq r hr
  /- Step 3: upper semicontinuity of the density on `B̆_ρ(0)`. -/
  have husc : ∀ x : Amb n ℓ, x ∈ ball (0 : Amb n ℓ) ρ → ∀ θ : ℝ, 0 ≤ θ → V.HasDensity x θ →
      ∀ η : ℝ, 0 < η → ∃ d > 0, ∀ x' ∈ ball x d, x' ∈ ball (0 : Amb n ℓ) ρ ∧
        ∀ θ' : ℝ, 0 ≤ θ' → V.HasDensity x' θ' → θ' < θ + η := by
    intro x hx θ hθ0 hθ η hη
    have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
    set R₀ := (ρ - ‖x‖) / 3 with hR₀def
    have hR₀ : 0 < R₀ := by rw [hR₀def]; linarith
    -- finiteness of the masses of the balls `B_s(x)`, `s ≤ 2 R₀`
    have hfin' : ∀ s, s ≤ 2 * R₀ → V.weight (closedBall x s) ≠ ⊤ := by
      intro s hs
      refine ne_top_of_le_ne_top hfin (measure_mono ?_)
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall_zero_iff]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hR₀def] at hs; linarith
    -- (a) the error term `c(r) = Λ (r/R₀)^α` tends to `0`
    have hc : Tendsto (fun r : ℝ => Λ * (r / R₀) ^ α) (𝓝[>] 0) (𝓝 0) := by
      have h2 : ContinuousAt (fun r : ℝ => Λ * (r / R₀) ^ α) 0 := by
        apply ContinuousAt.mul continuousAt_const
        exact ContinuousAt.rpow_const (continuousAt_id.div_const R₀) (Or.inr hα.le)
      have h3 := h2.tendsto
      simp only [zero_div, Real.zero_rpow hα.ne', mul_zero] at h3
      exact h3.mono_left nhdsWithin_le_nhds
    -- the normalized masses `r⁻ⁿ μ(B_r(x))` converge to `ω θ`
    have hlimm : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal)
        (𝓝[>] 0) (𝓝 (unitBallVolume n * θ)) := by
      have hθ' : Tendsto (fun r : ℝ => V.weight (closedBall x r) /
          ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) := hθ
      have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hθ'
      rw [ENNReal.toReal_ofReal hθ0] at h1
      have h2 := h1.const_mul (unitBallVolume n)
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      have hrn : 0 < r ^ n := pow_pos hr' n
      simp only [Function.comp_apply, ENNReal.toReal_div]
      rw [ENNReal.toReal_ofReal (mul_pos hω hrn).le]
      field_simp
    have hE : Tendsto (fun r : ℝ => (1 + Λ * (r / R₀) ^ α) *
        ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) + Λ * (r / R₀) ^ α) (𝓝[>] 0)
        (𝓝 (unitBallVolume n * θ)) := by
      have h := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).add
        hc).mul hlimm).add hc
      simp only [add_zero, one_mul] at h
      exact h
    have hlt : unitBallVolume n * θ < unitBallVolume n * θ + unitBallVolume n * η / 2 := by
      have := mul_pos hω hη
      linarith
    obtain ⟨r, hrE, hr⟩ :=
      ((hE.eventually (gt_mem_nhds hlt)).and
        (Ioo_mem_nhdsGT hR₀ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 R₀)).exists
    -- (b) continuity from above of `s ↦ μ(B_s(x))` at `r`
    have hcont : Tendsto (fun s => V.weight (closedBall x s)) (𝓝[>] r)
        (𝓝 (V.weight (closedBall x r))) := by
      have h := tendsto_measure_biInter_gt (μ := V.weight) (s := closedBall x) (a := r)
        (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
        (fun _ _ _ hij => closedBall_subset_closedBall hij)
        ⟨2 * R₀, by linarith [hr.2], hfin' _ le_rfl⟩
      rw [biInter_gt_closedBall] at h
      exact h
    have hcont' : Tendsto (fun s => (V.weight (closedBall x s)).toReal) (𝓝[>] r)
        (𝓝 (V.weight (closedBall x r)).toReal) :=
      (ENNReal.tendsto_toReal (hfin' r (by linarith [hr.2]))).comp hcont
    have hE2 : Tendsto (fun s => (1 + Λ * (r / R₀) ^ α) *
        ((r ^ n)⁻¹ * (V.weight (closedBall x s)).toReal) + Λ * (r / R₀) ^ α) (𝓝[>] r)
        (𝓝 ((1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R₀) ^ α)) :=
      ((hcont'.const_mul _).const_mul _).add_const _
    have hlt2 : (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
        Λ * (r / R₀) ^ α < unitBallVolume n * θ + unitBallVolume n * η := by
      have := mul_pos hω hη
      linarith
    obtain ⟨r', hr'E, hr'⟩ :=
      ((hE2.eventually (gt_mem_nhds hlt2)).and
        (Ioo_mem_nhdsGT (show r < 2 * R₀ by linarith [hr.2]) :
          ∀ᶠ s in 𝓝[>] r, s ∈ Ioo r (2 * R₀))).exists
    -- (c) on `B̆_d(x)`, `d = min R₀ (r' - r)`, the density is `< θ + η`
    refine ⟨min R₀ (r' - r), lt_min hR₀ (by linarith [hr'.1]), fun x' hx' => ?_⟩
    have hd1 : dist x' x < R₀ := lt_of_lt_of_le hx' (min_le_left _ _)
    have hd2 : dist x' x < r' - r := lt_of_lt_of_le hx' (min_le_right _ _)
    have hnx' : ‖x'‖ < ‖x‖ + R₀ := by
      rw [dist_eq_norm] at hd1
      calc ‖x'‖ = ‖(x' - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' - x‖ + ‖x‖ := norm_add_le _ _
        _ < ‖x‖ + R₀ := by linarith
    refine ⟨mem_ball_zero_iff.2 (by rw [hR₀def] at hnx'; linarith), fun θ' hθ'0 hθ' => ?_⟩
    have key := hineq x' R₀ hR₀ (by rw [hR₀def] at hnx' ⊢; linarith) θ' hθ'0 hθ' r hr
    have hball : closedBall x' r ⊆ closedBall x r' := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      calc dist z x ≤ dist z x' + dist x' x := dist_triangle _ _ _
        _ ≤ r' := by linarith
    have hmono' : (V.weight (closedBall x' r)).toReal ≤ (V.weight (closedBall x r')).toReal :=
      ENNReal.toReal_mono (hfin' r' hr'.2.le) (measure_mono hball)
    have hr0 : 0 < r := hr.1
    have hc0 : 0 ≤ Λ * (r / R₀) ^ α := by
      have := hΛ0.le
      positivity
    have h3 : (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x' r)).toReal) ≤
        (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r')).toReal) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hmono' (by positivity)
    have h4 : unitBallVolume n * θ' < unitBallVolume n * (θ + η) := by
      rw [mul_add]
      linarith
    exact lt_of_mul_lt_mul_left h4 hω.le
  /- Step 4: `μ`-a.e. every density value is `≥ 1`. -/
  have hae : ∀ᵐ x ∂V.weight, ∀ θ' : ℝ, V.HasDensity x θ' → 1 ≤ θ' := by
    filter_upwards [hdens, hA.2.2.1] with x hx1 hx2 θ' hθ'
    have h1 : 1 ≤ ENNReal.ofReal θ' := by
      rw [hunique x θ' (V.mult x) hθ' hx1]
      exact ENNReal.one_le_ofReal.2 hx2
    exact ENNReal.one_le_ofReal.1 h1
  /- Step 5: a ball about `y` on which the density is `< 1` would be `μ`-null. -/
  have hysupp : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hy.1).2
  obtain ⟨θ, hθ0, hθ⟩ := hex y hy.2
  have hθ1 : 1 ≤ θ := by
    by_contra hlt
    have hlt : θ < 1 := not_le.1 hlt
    obtain ⟨d, hd, hball⟩ := husc y hy.2 θ hθ0 hθ ((1 - θ) / 2) (by linarith)
    have hzero : V.weight (ball y d) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with x hx hxb
      obtain ⟨hxW, hlt'⟩ := hball x hxb
      obtain ⟨θ', hθ'0, hθ'⟩ := hex x hxW
      have h1 := hx θ' hθ'
      have h2 := hlt' θ' hθ'0 hθ'
      linarith
    have hpos := (Measure.mem_support_iff_forall y).1 hysupp (ball y d) (ball_mem_nhds y hd)
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  have h1 : 1 ≤ ENNReal.ofReal t := by
    rw [hunique y t θ ht hθ]
    exact ENNReal.one_le_ofReal.2 hθ1
  exact ENNReal.one_le_ofReal.1 h1

/-- **Simon Ch. 5, 2.4 with explicit constants** (pinched mass and conical bounds near `0`).  For
`n ≥ 1` and `p > n` there are `δ_P ∈ (0, 1/8]` and `C_P > 0` with `C_P δ_P ≤ 1/2`, depending only
on `n, p` (the same for every codimension `ℓ`), such that if 2.3 holds with `0 < δ ≤ δ_P`, then for
`|y| ≤ 3δρ` and `0 < s ≤ ρ/2`: `μ_V(B_s(y)) ≤ (1 + C_P δ) ω_n sⁿ`; and if `y ∈ spt V`, also
`μ_V(B_s(y)) ≥ (1 − C_P δ) ω_n sⁿ` and `∫_{B_s(y)} |x − y − p_x(x − y)|² |x − y|^{−n−2} dμ_V ≤
C_P ω_n δ` (the integrand is `0` at `x = y`).

Proof: `δ_P, C_P` come from `allard52_density_constants` with `κ = (p − n)/(4p)` and `ω = ω_n`,
before `ℓ` is chosen.  With `Λ = δ/κ ∈ (0, 1]` and `R = (1 − 3δ)ρ ∈ (s, ρ]`, `B_R(y) ⊆ B_ρ(0)`, so
`aal_allard_subball_bounds` gives `B_R(y) ⊆ U`, `K(y, R) ≤ δ = κΛ` and
`μ_V(B_r(y)) ≤ M = (1 + δ) ω_n ρⁿ`.  The tangent facts of `allard52_tangent_ae` feed
`allard52_annular_monotonicity` at `(y, R, Λ)`, whose data drive
`allard52_center_density_bounds`; at support points `allard52_support_density_ge_one` gives
`Θⁿ(μ_V, y) ≥ 1`, i.e. `ω_n ≤ Φ` on `(0, R)`.  As `M/Rⁿ = (1 + δ)(1 − 3δ)⁻ⁿ ω_n`, the three
inequalities of `allard52_density_constants` at `t = δ` are exactly the claimed bounds. -/
theorem allard52_density_bounds : ∀ (n : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + CP * δ) * (unitBallVolume n * s ^ n)) ∧ (y ∈ V.support → ENNReal.ofReal ((1 - CP * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (CP * unitBallVolume n * δ)) := by
  intro n hn p hp
  -- Step 1: `δ_P, C_P` from `κ = (p − n)/(4p)` and `ω_n` alone, before `ℓ` is chosen.
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  have hκ : 0 < (p - n) / (4 * p) := div_pos (sub_pos.2 hp) (by positivity)
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨δP, CP, hδP0, hδP8, hδPκ, hCP0, hCPδP, hineq⟩ :=
    Submission.allard52_density_constants n ((p - n) / (4 * p)) (unitBallVolume n) hκ hω
  refine ⟨δP, CP, hδP0, hδP8, hCP0, hCPδP, ?_⟩
  intro ℓ U hU V H δ ρ hδ hδδP hA y hy s hs hsρ
  have hρ : 0 < ρ := hA.1
  have hδ8 : δ ≤ 1 / 8 := hδδP.trans hδP8
  have hδκ : δ ≤ (p - n) / (4 * p) := hδδP.trans hδPκ
  obtain ⟨hia, hib, hic⟩ := hineq δ hδ hδδP
  -- Step 5: `Λ = δ/κ ∈ (0, 1]`, `R = (1 − 3δ)ρ` with `s < R ≤ ρ` and `B_R(y) ⊆ B_ρ(0)`.
  set Λ := δ / ((p - n) / (4 * p))
  have hΛ0 : 0 < Λ := div_pos hδ hκ
  have hΛ1 : Λ ≤ 1 := (div_le_one hκ).2 hδκ
  have hκΛ : (p - n) / (4 * p) * Λ = δ := mul_div_cancel₀ δ hκ.ne'
  set R := (1 - 3 * δ) * ρ with hR
  have hR0 : 0 < R := mul_pos (by linarith) hρ
  have hsR : s < R := by rw [hR]; nlinarith
  have hRρ : R ≤ ρ := by rw [hR]; nlinarith
  have hball : closedBall y R ⊆ closedBall 0 ρ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 3 * δ * ρ := add_le_add hz hy
      _ = ρ := by rw [hR]; ring
  -- Step 2: `B_R(y) ⊆ U`, `K(y, R) ≤ δ`, and `μ_V(B_r(y)) ≤ M` for `r < R`.
  obtain ⟨hRU, -, hK, -⟩ :=
    Submission.aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y R hR0 hRρ hball
  set M := (1 + δ) * (unitBallVolume n * ρ ^ n) with hM
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) (mul_nonneg hω.le (pow_nonneg hρ.le n))
  have hμ : ∀ r ∈ Ioo 0 R, V.weight (closedBall y r) ≤ ENNReal.ofReal M := fun r hr =>
    (measure_mono ((closedBall_subset_closedBall hr.2.le).trans hball)).trans hA.2.2.2.2.2.1
  -- Step 3: the monotonicity data `(M)` at `y` with radius `R`, from the tangent facts `(T)`.
  obtain ⟨hmeas, htan, hdens⟩ := Submission.allard52_tangent_ae n ℓ hn U hU V
  obtain ⟨F, hF, hΦ, t, -, htd, htΦ⟩ :=
    Submission.allard52_annular_monotonicity n ℓ hn p hp U hU V H hA.2.1 y R Λ hR0 hRU
      (htan.mono fun x hx _ => hx) hmeas.restrict hΛ0 hΛ1 (by rw [hκΛ]; exact hK)
  -- `(r/R)^{1 − n/p} ≤ 1` on `(0, R)`, so `|F − 1| ≤ Λ` there.
  have hα : 0 ≤ 1 - (n : ℝ) / p := sub_nonneg.2 ((div_le_one hp0).2 hp.le)
  have hF' : ∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hF r hr
    exact ⟨h1, h2, h3.trans (mul_le_of_le_one_right hΛ0.le
      (Real.rpow_le_one (div_nonneg hr.1.le hR0.le) ((div_le_one hR0).2 hr.2.le) hα))⟩
  -- Steps 6–8 at `y`, with `g(x) = |x − y − p_x(x − y)|²/|x − y|^{n+2}`, so `g(y) = 0`.
  obtain ⟨hi, hii⟩ := Submission.allard52_center_density_bounds n ℓ V.weight
    (fun x => ‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) F y (unitBallVolume n)
    R Λ M hR0 hΛ0 hM0 (by simp) hμ hF' hΦ s hs hsR
  have hMR : M / R ^ n = (1 + δ) / (1 - 3 * δ) ^ n * unitBallVolume n := by
    have h1 : (1 - 3 * δ) ^ n ≠ 0 := pow_ne_zero n (by linarith)
    have h2 : ρ ^ n ≠ 0 := pow_ne_zero n hρ.ne'
    rw [hM, hR, mul_pow]
    field_simp
  rw [hMR] at hi hii
  have hsn : 0 ≤ s ^ n := pow_nonneg hs.le n
  -- (P.i) is inequality (a) of `allard52_density_constants` at `t = δ`.
  refine ⟨hi.trans (ENNReal.ofReal_le_ofReal ?_), fun hys => ?_⟩
  · calc (Real.exp (2 * Λ) * ((1 + δ) / (1 - 3 * δ) ^ n * unitBallVolume n) +
          2 * Real.exp Λ * Λ) * s ^ n
        ≤ (1 + CP * δ) * unitBallVolume n * s ^ n := mul_le_mul_of_nonneg_right hia hsn
      _ = (1 + CP * δ) * (unitBallVolume n * s ^ n) := mul_assoc _ _ _
  -- Step 4: `|y| ≤ 3δρ < ρ`, so the density `t` of `(M.iii)` is `≥ 1` and `ω_n ≤ ω_n t ≤ Φ`.
  have hyρ : ‖y‖ < ρ := by nlinarith
  have ht1 : 1 ≤ t := Submission.allard52_support_density_ge_one n ℓ hn p hp U hU V H δ ρ hδ hδκ hA
    hmeas htan hdens y ⟨hys, mem_ball_zero_iff.2 hyρ⟩ t htd
  obtain ⟨hii1, hii2⟩ := hii fun r hr => (le_mul_of_one_le_right hω.le ht1).trans (htΦ r hr)
  -- (P.ii) and (P.iii) are inequalities (b) and (c) of `allard52_density_constants` at `t = δ`.
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) hii1, hii2.trans (ENNReal.ofReal_le_ofReal hic)⟩
  calc (1 - CP * δ) * (unitBallVolume n * s ^ n) = (1 - CP * δ) * unitBallVolume n * s ^ n :=
        (mul_assoc _ _ _).symm
    _ ≤ Real.exp (-Λ) * (unitBallVolume n - Λ) * s ^ n := mul_le_mul_of_nonneg_right hib hsn

end Submission

end GMT.Ch05
