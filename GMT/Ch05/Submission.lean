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

/-- Simon Ch. 5, proof of Lemma 2.5 (p. 109): a maximal family of centres in `S` with pairwise
disjoint closed balls `B_r(z)` is a finite `2r`-net of `S`.  If every `B_r(y)`, `y ∈ S`, lies in `E`
and has `μ(B_r(y)) ≥ a > 0`, while `μ(E) ≤ b`, then such a family `G` has
`#G · a ≤ Σ_{z ∈ G} μ(B_r(z)) = μ(⋃_{z ∈ G} B_r(z)) ≤ μ(E) ≤ b`.  Take one, `F`, of maximal
cardinality; if `dist(y, z) > 2r` for all `z ∈ F`, then `F ∪ {y}` would be a larger such family. -/
theorem aal_packing_finite_net : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (S E : Set X) (r a b : ℝ), 0 < r → 0 < a → 0 ≤ b → μ E ≤ ENNReal.ofReal b → (∀ y ∈ S, closedBall y r ⊆ E ∧ ENNReal.ofReal a ≤ μ (closedBall y r)) → ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ (F.card : ℝ) * a ≤ b ∧ ∀ y ∈ S, ∃ z ∈ F, dist y z ≤ 2 * r := by
  intro X _ _ _ μ S E r a b hr ha hb hE hS
  classical
  -- Packing bound: if `G ⊆ S` has pairwise disjoint closed `r`-balls, then `#G · a ≤ b`.
  have hbound : ∀ G : Finset X, (↑G : Set X) ⊆ S →
      (↑G : Set X).PairwiseDisjoint (fun z => closedBall z r) → (G.card : ℝ) * a ≤ b := by
    intro G hGS hGd
    have key : (G.card : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal b :=
      calc (G.card : ℝ≥0∞) * ENNReal.ofReal a = ∑ _z ∈ G, ENNReal.ofReal a := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ z ∈ G, μ (closedBall z r) := Finset.sum_le_sum fun z hz => (hS z (hGS hz)).2
        _ = μ (⋃ z ∈ G, closedBall z r) :=
            (measure_biUnion_finset hGd fun z _ => measurableSet_closedBall).symm
        _ ≤ μ E := measure_mono (Set.iUnion₂_subset fun z hz => (hS z (hGS hz)).1)
        _ ≤ ENNReal.ofReal b := hE
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at key
    exact (ENNReal.ofReal_le_ofReal_iff hb).1 key
  -- The cardinalities of admissible sets form a nonempty set of naturals bounded by `⌊b / a⌋`.
  let C : Set ℕ := {k | ∃ G : Finset X, (↑G : Set X) ⊆ S ∧
    (↑G : Set X).PairwiseDisjoint (fun z => closedBall z r) ∧ G.card = k}
  have hCne : C.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hCbdd : BddAbove C := by
    refine ⟨⌊b / a⌋₊, ?_⟩
    rintro k ⟨G, hGS, hGd, rfl⟩
    exact Nat.le_floor ((le_div_iff₀ ha).2 (hbound G hGS hGd))
  -- An admissible `F` of maximal cardinality.
  obtain ⟨F, hFS, hFd, hFcard⟩ := Nat.sSup_mem hCne hCbdd
  refine ⟨F, hFS, hbound F hFS hFd, ?_⟩
  -- Net property: otherwise `insert y F` would be admissible of larger cardinality.
  intro y hy
  by_contra! hfar
  have hyF : y ∉ F := fun h => by
    have := hfar y h
    rw [dist_self] at this
    linarith
  have hmem : (insert y F).card ∈ C := by
    refine ⟨insert y F, ?_, ?_, rfl⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hy hFS
    · rw [Finset.coe_insert]
      exact hFd.insert fun z hz _ => closedBall_disjoint_closedBall (by linarith [hfar z hz])
  have hle := le_csSup hCbdd hmem
  rw [Finset.card_insert_of_notMem hyF, hFcard] at hle
  omega
/-- Simon Ch. 5, proof of Lemma 2.5 (p. 109), (1), first inequality: for any measure `μ` and any
map `x ↦ P x`, on `B_s(y)` we have `|v(x)|² = |x - y|^{n+2} · |v(x)|² |x - y|^{-n-2}
≤ s^{n+2} · |v(x)|² |x - y|^{-n-2}` with `v(x) = (x - y) - P x (x - y)` (both sides vanish at
`x = y`), hence `∫_{B_s(y)} |v|² dμ ≤ s^{n+2} ∫_{B_s(y)} |v|² |x - y|^{-n-2} dμ`. -/
theorem aal_normal_sq_lintegral_le_conical : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (P : Amb n ℓ → Amb n ℓ →L[ℝ] Amb n ℓ) (y : Amb n ℓ) (s : ℝ), 0 < s → ∫⁻ x in closedBall y s, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ ≤ ENNReal.ofReal (s ^ (n + 2)) * ∫⁻ x in closedBall y s, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ := by
  intro n ℓ μ P y s hs
  -- Move the finite constant `ofReal (s ^ (n + 2))` inside and compare integrands on the ball.
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_closedBall fun x hx => ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hs.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_ne x y with rfl | hxy
  · -- At `x = y` both sides vanish, since `P x 0 = 0`.
    simp
  · -- For `0 < |x - y| ≤ s`: `|v|² = |x - y|^{n+2} (|v|² / |x - y|^{n+2}) ≤ s^{n+2} (|v|² / |x - y|^{n+2})`.
    have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hds : ‖x - y‖ ≤ s := by rwa [mem_closedBall, dist_eq_norm] at hx
    have hpow : 0 < ‖x - y‖ ^ (n + 2) := pow_pos hd _
    calc ‖(x - y) - P x (x - y)‖ ^ 2
        = ‖x - y‖ ^ (n + 2) * (‖(x - y) - P x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) :=
          (mul_div_cancel₀ _ hpow.ne').symm
      _ ≤ s ^ (n + 2) * (‖(x - y) - P x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le hds _)
            (div_nonneg (sq_nonneg _) hpow.le)
/-- Simon Ch. 5, proof of Lemma 2.5 (p. 109), (4)–(5): Chebyshev selection of a good point.  If
`∫_{B_R(ξ)} |p_x^⊥(x - y)|² dμ ≤ K` for every `y ∈ F` and `#F · K < λ μ(B_s(ξ))` with `s ≤ R`,
then some `x₀ ∈ B_s(ξ)` at which `P x₀ = p_T` for an `n`-plane `T` has `|p_T^⊥(x₀ - y)|² < λ` for
all `y ∈ F`.  Otherwise `Σ_{y ∈ F} |p_x^⊥(x - y)|² ≥ λ` `μ`-a.e. on `B_s(ξ)`, and integrating gives
`λ μ(B_s(ξ)) ≤ #F · K`. -/
theorem aal_good_tangent_point : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (P : Amb n ℓ → Amb n ℓ →L[ℝ] Amb n ℓ), AEStronglyMeasurable P μ → (∀ᵐ x ∂μ, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ P x = T.starProjection) → ∀ (ξ : Amb n ℓ) (s R K lam : ℝ) (F : Finset (Amb n ℓ)), 0 < lam → s ≤ R → (∀ y ∈ F, ∫⁻ x in closedBall ξ R, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ ≤ ENNReal.ofReal K) → ENNReal.ofReal ((F.card : ℝ) * K) < ENNReal.ofReal lam * μ (closedBall ξ s) → ∃ x₀ ∈ closedBall ξ s, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ P x₀ = T.starProjection ∧ ∀ y ∈ F, ‖(x₀ - y) - T.starProjection (x₀ - y)‖ ^ 2 < lam := by
  intro n ℓ μ P hP hT ξ s R K lam F hlam hsR hK hlt
  by_contra! hcon
  -- `h y x = ofReal |(x - y) - P(x)(x - y)|²`, a.e. measurable since evaluation is bilinear.
  have hmeas : ∀ y : Amb n ℓ,
      AEMeasurable (fun x => ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2)) μ := by
    intro y
    have hPy : AEStronglyMeasurable (fun x => P x (x - y)) μ :=
      (ContinuousLinearMap.id ℝ (Amb n ℓ →L[ℝ] Amb n ℓ)).aestronglyMeasurable_comp₂ hP
        (continuous_id.sub continuous_const).aestronglyMeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_id.sub continuous_const).aestronglyMeasurable.sub hPy).norm.aemeasurable.pow_const 2)
  -- `∫_{B_R(ξ)} Σ_y h_y dμ = Σ_y ∫_{B_R(ξ)} h_y dμ ≤ #F · K`.
  have hsum : ∫⁻ x in closedBall ξ R, ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal ((F.card : ℝ) * K) := by
    rw [lintegral_finsetSum' F fun y _ => (hmeas y).restrict,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    calc ∑ y ∈ F, ∫⁻ x in closedBall ξ R, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ
        ≤ ∑ _y ∈ F, ENNReal.ofReal K := Finset.sum_le_sum hK
      _ = F.card * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
  -- If no good point exists, then `Σ_y h_y ≥ λ` a.e. on `B_s(ξ)`.
  have hae : ∀ᵐ x ∂μ.restrict (closedBall ξ s),
      ENNReal.ofReal lam ≤ ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae hT, ae_restrict_mem measurableSet_closedBall]
      with x ⟨T, hTn, hPT⟩ hx
    obtain ⟨y, hyF, hy⟩ := hcon x hx T hTn hPT
    calc ENNReal.ofReal lam ≤ ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) := by
          rw [hPT]; exact ENNReal.ofReal_le_ofReal hy
      _ ≤ ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) :=
          Finset.single_le_sum (f := fun y => ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2))
            (fun _ _ => zero_le) hyF
  -- Chebyshev: `λ μ(B_s(ξ)) ≤ ∫_{B_s(ξ)} Σ_y h_y ≤ ∫_{B_R(ξ)} Σ_y h_y ≤ #F · K`, contradicting (H2).
  refine absurd hlt (not_lt.mpr ?_)
  calc ENNReal.ofReal lam * μ (closedBall ξ s)
      = ∫⁻ _ in closedBall ξ s, ENNReal.ofReal lam ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in closedBall ξ s, ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ :=
        lintegral_mono_ae hae
    _ ≤ ∫⁻ x in closedBall ξ R, ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ :=
        lintegral_mono_set (closedBall_subset_closedBall hsR)
    _ ≤ ENNReal.ofReal ((F.card : ℝ) * K) := hsum
/-- Simon Ch. 5, proof of Lemma 2.5 (pp. 109–110), (5)–(6): if `|x₀ − ξ| ≤ a`, every net point
`y ∈ F` has `|p_{T⊥}(x₀ − y)| ≤ b`, and `F` is an `a`-net of `S`, then
`dist(x − ξ, T) ≤ b + 2a` for every `x ∈ S`. -/
theorem aal_height_of_net_plane : ∀ (n ℓ : ℕ) (T : Submodule ℝ (Amb n ℓ)) (ξ x₀ : Amb n ℓ) (S : Set (Amb n ℓ)) (F : Finset (Amb n ℓ)) (a b : ℝ), ‖x₀ - ξ‖ ≤ a → (∀ y ∈ F, ‖(x₀ - y) - T.starProjection (x₀ - y)‖ ≤ b) → (∀ x ∈ S, ∃ y ∈ F, dist x y ≤ a) → ∀ x ∈ S, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ b + 2 * a := by
  intro n ℓ T ξ x₀ S F a b hx₀ hF hS x hx
  -- Step 1: a net point `y ∈ F` with `|x − y| ≤ a`.
  obtain ⟨y, hyF, hxy⟩ := hS x hx
  -- Step 2: `t = −p_T(x₀ − y) ∈ T`.
  have ht : -T.starProjection (x₀ - y) ∈ T := T.neg_mem (T.starProjection_apply_mem _)
  -- Step 3: `(x − ξ) − t = (x − y) + (x₀ − ξ) − ((x₀ − y) − p_T(x₀ − y))`.
  have hid : (x - ξ) - -T.starProjection (x₀ - y) =
      (x - y) + (x₀ - ξ) - ((x₀ - y) - T.starProjection (x₀ - y)) := by abel
  -- Step 5: the triangle inequality and the three hypotheses.
  have h₁ := norm_sub_le ((x - y) + (x₀ - ξ)) ((x₀ - y) - T.starProjection (x₀ - y))
  have h₂ := norm_add_le (x - y) (x₀ - ξ)
  rw [dist_eq_norm] at hxy
  have h₃ := hF y hyF
  -- Steps 4 and 6: `dist(x − ξ, T) ≤ |(x − ξ) − t| ≤ a + a + b`.
  calc infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ dist (x - ξ) (-T.starProjection (x₀ - y)) :=
        infDist_le_dist_of_mem ht
    _ = ‖(x - y) + (x₀ - ξ) - ((x₀ - y) - T.starProjection (x₀ - y))‖ := by
        rw [dist_eq_norm, hid]
    _ ≤ b + 2 * a := by linarith
/-- Simon Ch. 5, 2.4, the elementary inequalities (E1)–(E5) behind the pinched density bounds, with
`κ > 0` and `ω > 0` arbitrary: put `e = exp 1`, `A = 1 + n 2^{n+4}`, `B = (9/8) 2ⁿ`,
`C₊ = A + (2e²B + 2e/ω)/κ`, `C₋ = (1 + 1/ω)/κ`, `C_c = eA + (e²B + e/ω)/κ`,
`C_P = max {1, C₊, C₋, C_c}` and `δ_P = min {1/8, κ, 1/(2C_P)}`.  For `t ∈ (0, δ_P]`, with
`Λ = t/κ ∈ (0, 1]` and `a = (1 + t)/(1 − 4t)ⁿ`, the bounds `1 − Λ ≤ e^{−Λ} ≤ 1`, `e^Λ ≤ e`,
`e^Λ ≤ 1 + eΛ`, `e^{2Λ} ≤ 1 + 2e²Λ` (from `1 + x ≤ eˣ` and monotonicity of `exp`) and
`0 ≤ a ≤ 1 + At`, `a ≤ B` (Bernoulli and `(1 − 4t)ⁿ ≥ 2⁻ⁿ`) give the three inequalities. -/
theorem aal_pinched_constants : ∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ Cp δp : ℝ, 1 ≤ Cp ∧ 0 < δp ∧ δp ≤ 1 / 8 ∧ δp ≤ κ ∧ Cp * δp ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δp → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 4 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + Cp * t) * ω ∧ (1 - Cp * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 4 * t) ^ n * ω) + t / κ - ω) ≤ Cp * ω * t := by
  intro n κ ω hκ hω
  -- Step 1: the constants `e = exp 1`, `A = 1 + n 2^{n+4}`, `B = (9/8) 2ⁿ`, `C₊`, `C₋`, `C_c`.
  set e : ℝ := Real.exp 1 with he_def
  set A : ℝ := 1 + (n : ℝ) * 2 ^ (n + 4) with hA_def
  set B : ℝ := 9 / 8 * 2 ^ n with hB_def
  have he : 0 < e := Real.exp_pos 1
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  clear_value e A B
  -- `C_P = max {1, C₊, C₋, C_c}` dominates `1`, `C₊`, `C₋` and `C_c`.
  obtain ⟨Cp, hCp1, hCplus, hCminus, hCc⟩ : ∃ Cp : ℝ, 1 ≤ Cp ∧
      A + (2 * e ^ 2 * B + 2 * e / ω) / κ ≤ Cp ∧ (1 + 1 / ω) / κ ≤ Cp ∧
      e * A + (e ^ 2 * B + e / ω) / κ ≤ Cp :=
    ⟨max (max 1 (A + (2 * e ^ 2 * B + 2 * e / ω) / κ))
        (max ((1 + 1 / ω) / κ) (e * A + (e ^ 2 * B + e / ω) / κ)),
      (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hCp0 : 0 < Cp := by linarith
  -- `δ_P = min {1/8, κ, 1/(2 C_P)}`: positive, `≤ 1/8`, `≤ κ` and `C_P δ_P ≤ 1/2`.
  refine ⟨Cp, min (min (1 / 8) κ) (1 / (2 * Cp)), hCp1,
    lt_min (lt_min (by norm_num) hκ) (div_pos one_pos (mul_pos two_pos hCp0)),
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_, ?_⟩
  · calc Cp * min (min (1 / 8) κ) (1 / (2 * Cp)) ≤ Cp * (1 / (2 * Cp)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCp0.le
      _ = 1 / 2 := by field_simp
  intro t ht htδ
  have ht8 : t ≤ 1 / 8 := htδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htκ : t ≤ κ := htδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- Step 2: `Λ = t/κ ∈ (0, 1]`.
  set Λ : ℝ := t / κ with hΛ_def
  have hΛ0 : 0 < Λ := div_pos ht hκ
  have hΛ1 : Λ ≤ 1 := (div_le_one hκ).mpr htκ
  clear_value Λ
  -- Step 3 (E1): exponential bounds from `1 + x ≤ eˣ` and monotonicity of `exp`.
  have hEm_lb : 1 - Λ ≤ Real.exp (-Λ) := Real.one_sub_le_exp_neg Λ
  have hEm_le : Real.exp (-Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE_le : Real.exp Λ ≤ e := by rw [he_def]; exact Real.exp_le_exp.mpr hΛ1
  have hE_pos : 0 < Real.exp Λ := Real.exp_pos Λ
  -- `e^Λ (1 − Λ) ≤ e^Λ e^{−Λ} = 1`, so `e^Λ ≤ 1 + Λ e^Λ ≤ 1 + eΛ`.
  have hE_lin : Real.exp Λ ≤ 1 + e * Λ := by
    have h1 : Real.exp Λ * (1 - Λ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hEm_lb hE_pos.le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    linarith [mul_le_mul_of_nonneg_left hE_le hΛ0.le]
  -- `e^{2Λ} (1 − 2Λ) ≤ 1` and `e^{2Λ} ≤ e²`, so `e^{2Λ} ≤ 1 + 2Λ e^{2Λ} ≤ 1 + 2e²Λ`.
  have hE2 : Real.exp (2 * Λ) ≤ 1 + 2 * e ^ 2 * Λ := by
    have h1 : Real.exp (2 * Λ) * (1 - 2 * Λ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (2 * Λ))
        (Real.exp_pos (2 * Λ)).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    have h2 : Real.exp (2 * Λ) ≤ e ^ 2 := by
      rw [he_def, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    linarith [mul_le_mul_of_nonneg_left h2 hΛ0.le]
  -- Step 4 (E2): bounds on `a = (1 + t)/(1 − 4t)ⁿ`; note `1 − 4t ≥ 1/2`.
  set P : ℝ := (1 - 4 * t) ^ n with hP_def
  have hP0 : 0 < P := pow_pos (by linarith) n
  -- (a) Bernoulli: `(1 − 4t)ⁿ ≥ 1 − 4nt`.
  have hBern : 1 - 4 * n * t ≤ P := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -4 * t by linarith) n
    rw [hP_def, show (1 : ℝ) - 4 * t = 1 + -4 * t by ring]
    linarith
  -- (b) `2ⁿ (1 − 4t)ⁿ = (2 − 8t)ⁿ ≥ 1`, i.e. `1/(1 − 4t)ⁿ ≤ 2ⁿ`.
  have hQP : 1 ≤ 2 ^ n * P := by
    rw [hP_def, ← mul_pow]
    exact one_le_pow₀ (by linarith)
  clear_value P
  have h4 : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; norm_num; ring
  have h16 : (2 : ℝ) ^ (n + 4) = 16 * 2 ^ n := by rw [pow_add]; norm_num; ring
  -- (c) With `c = n 2^{n+2}`: `(1 + ct)(1 − 4t)ⁿ ≥ (1 − 4nt) + 4nt = 1`.
  have hc0 : 0 ≤ (n : ℝ) * 2 ^ (n + 2) := by positivity
  have hc : 1 ≤ (1 + (n : ℝ) * 2 ^ (n + 2) * t) * P := by
    rw [h4]
    linarith [mul_le_mul_of_nonneg_left hQP (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * n) ht.le)]
  -- (d) `a ≤ (1 + t)(1 + ct) ≤ 1 + At`, since `ct² ≤ 3ct` and `4c = n 2^{n+4}`.
  set a : ℝ := (1 + t) / P with ha_def
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hP0.le
  clear_value a
  have haA : a ≤ 1 + A * t := by
    rw [ha_def, div_le_iff₀ hP0, hA_def, h16]
    have hct : 0 ≤ (n : ℝ) * 2 ^ (n + 2) * t * (3 - t) * P :=
      mul_nonneg (mul_nonneg (mul_nonneg hc0 ht.le) (by linarith)) hP0.le
    have hmul := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 + t by linarith)
    rw [h4] at hct hmul
    linarith
  -- (e) `a ≤ (9/8) 2ⁿ = B`, since `1 + t ≤ 9/8` and `2ⁿ (1 − 4t)ⁿ ≥ 1`.
  have haB : a ≤ B := by
    rw [ha_def, div_le_iff₀ hP0, hB_def]
    linarith
  have haω0 : 0 ≤ a * ω := mul_nonneg ha0 hω.le
  have haωA : a * ω ≤ ω + A * t * ω := by linarith [mul_le_mul_of_nonneg_right haA hω.le]
  have haωB : a * ω ≤ B * ω := mul_le_mul_of_nonneg_right haB hω.le
  have htω : 0 ≤ t * ω := mul_nonneg ht.le hω.le
  refine ⟨?_, ?_, ?_⟩
  · -- (E3): `e^{2Λ}(aω) + 2e^Λ Λ ≤ ω + Atω + 2e²BΛω + 2eΛ = (1 + C₊ t) ω ≤ (1 + C_P t) ω`.
    have hid : (A + (2 * e ^ 2 * B + 2 * e / ω) / κ) * (t * ω) =
        A * t * ω + 2 * e ^ 2 * B * Λ * ω + 2 * e * Λ := by
      rw [hΛ_def]; field_simp; ring
    have h1 := mul_le_mul_of_nonneg_right hE2 haω0
    have h2 := mul_le_mul_of_nonneg_left haωB (mul_nonneg (by positivity : 0 ≤ 2 * e ^ 2) hΛ0.le)
    have h3 := mul_le_mul_of_nonneg_right hE_le hΛ0.le
    have h4 := mul_le_mul_of_nonneg_right hCplus htω
    linarith
  · -- (E4): `(1 − C_P t) ω ≤ (1 − C₋ t) ω = ω − Λω − Λ ≤ e^{−Λ}(ω − Λ)`.
    have hid : (1 + 1 / ω) / κ * (t * ω) = Λ * ω + Λ := by
      rw [hΛ_def]; field_simp
    have h1 := mul_le_mul_of_nonneg_right hCminus htω
    have h2 : ω - Λ * ω - Λ ≤ Real.exp (-Λ) * (ω - Λ) := by
      rcases le_or_gt 0 (ω - Λ) with hc' | hc'
      · linarith [mul_le_mul_of_nonneg_right hEm_lb hc', sq_nonneg Λ]
      · linarith [mul_le_mul_of_nonpos_right hEm_le hc'.le, mul_pos hΛ0 hω]
    linarith
  · -- (E5): with `b = e^Λ(aω) + Λ − ω ≤ b' = Atω + eΛBω + Λ`, `e^Λ b ≤ e b' = C_c ω t ≤ C_P ω t`.
    have hid : (e * A + (e ^ 2 * B + e / ω) / κ) * (ω * t) =
        e * (A * t * ω + e * Λ * B * ω + Λ) := by
      rw [hΛ_def]; field_simp; ring
    have hb : Real.exp Λ * (a * ω) + Λ - ω ≤ A * t * ω + e * Λ * B * ω + Λ := by
      linarith [mul_le_mul_of_nonneg_right hE_lin haω0,
        mul_le_mul_of_nonneg_left haωB (mul_nonneg he.le hΛ0.le)]
    have hb' : 0 ≤ A * t * ω + e * Λ * B * ω + Λ :=
      add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hA0 ht.le) hω.le)
        (mul_nonneg (mul_nonneg (mul_nonneg he.le hΛ0.le) hB0) hω.le)) hΛ0.le
    have h1 : Real.exp Λ * (Real.exp Λ * (a * ω) + Λ - ω) ≤
        e * (A * t * ω + e * Λ * B * ω + Λ) := by
      rcases le_or_gt 0 (Real.exp Λ * (a * ω) + Λ - ω) with hb0 | hb0
      · calc Real.exp Λ * (Real.exp Λ * (a * ω) + Λ - ω)
            ≤ e * (Real.exp Λ * (a * ω) + Λ - ω) := mul_le_mul_of_nonneg_right hE_le hb0
          _ ≤ e * (A * t * ω + e * Λ * B * ω + Λ) := mul_le_mul_of_nonneg_left hb he.le
      · linarith [mul_neg_of_pos_of_neg hE_pos hb0, mul_nonneg he.le hb']
    have h2 := mul_le_mul_of_nonneg_right hCc (mul_nonneg hω.le ht.le)
    linarith
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
/-- Simon Ch. 5, 2.4, step (5.1) of the lower density bound, abstracted: put
`Φ(u) = F(u) (m(u)/uⁿ) + (F(u) − 1)`.  If `|F(u) − 1| ≤ Λ (u/R)^α` on `(0, R]` with `α > 0`, `Φ` is
nondecreasing on `(0, R]`, and for every `ε > 0` eventually `(1 − ε) ω uⁿ ≤ m(u)` as `u ↓ 0`, then
`ω ≤ Φ(t)` for every `t ∈ (0, R]` (let `u ↓ 0` in `Φ(u) ≤ Φ(t)`, using `F(u) → 1`). -/
theorem aal_monotone_quantity_ge_density : ∀ (n : ℕ) (α ω R Λ : ℝ) (m F : ℝ → ℝ), 0 < α → 0 < ω → 0 < R → (∀ u : ℝ, 0 < u → u ≤ R → |F u - 1| ≤ Λ * (u / R) ^ α) → (∀ u t : ℝ, 0 < u → u ≤ t → t ≤ R → F u * (m u / u ^ n) + (F u - 1) ≤ F t * (m t / t ^ n) + (F t - 1)) → (∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[>] (0 : ℝ), (1 - ε) * (ω * u ^ n) ≤ m u) → ∀ t : ℝ, 0 < t → t ≤ R → ω ≤ F t * (m t / t ^ n) + (F t - 1) := by
  intro n α ω R Λ m F hα hω hR hF hmono hlow t ht htR
  -- `Λ (u/R)^α → 0` as `u → 0+`, since `x ↦ x^α` is continuous at `0` with `0^α = 0` (`α > 0`).
  have hlim : Tendsto (fun u : ℝ => Λ * (u / R) ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ => Λ * (u / R) ^ α) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const R).rpow_const (Or.inr hα.le))
    have h := hc.tendsto
    simp only [zero_div, Real.zero_rpow hα.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Suppose `Φ(t) < ω` and pick `η ∈ (0, 1/2]` with `η (2ω + 1) ≤ (ω − Φ(t))/2`.
  refine not_lt.mp fun hcon => ?_
  obtain ⟨η, hη0, hη2, hηd⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
      η * (2 * (2 * ω + 1)) ≤ ω - (F t * (m t / t ^ n) + (F t - 1)) := by
    refine ⟨min (1 / 2) ((ω - (F t * (m t / t ^ n) + (F t - 1))) / (2 * (2 * ω + 1))),
      lt_min (by norm_num) (div_pos (sub_pos.mpr hcon) (by positivity)), min_le_left _ _, ?_⟩
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_right _ _
  -- A small radius `u ∈ (0, t)` with `Λ (u/R)^α < η` and `(1 − η) ω uⁿ ≤ m(u)`.
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  obtain ⟨u, ⟨hu0, hut⟩, huΛ, hum⟩ :=
    (hsmall.and ((hlim.eventually (gt_mem_nhds hη0)).and (hlow η hη0))).exists
  -- `|F(u) − 1| < η`, so `F(u) > 1 − η ≥ 1/2`.
  have hFu : 1 - η < F u := by
    have h := (abs_lt.mp ((hF u hu0 (hut.le.trans htR)).trans_lt huΛ)).1
    linarith
  -- `m(u)/uⁿ ≥ (1 − η) ω ≥ 0`, hence `F(u) (m(u)/uⁿ) ≥ (1 − η)² ω`.
  have hmu : (1 - η) * ω ≤ m u / u ^ n := by
    rw [le_div_iff₀ (pow_pos hu0 n)]
    linarith
  have hprod : (1 - η) * ((1 - η) * ω) ≤ F u * (m u / u ^ n) :=
    mul_le_mul hFu.le hmu (mul_nonneg (by linarith) hω.le) (by linarith)
  -- `Φ(u) ≥ (1 − η)² ω − η ≥ ω − η (2ω + 1) > Φ(t)`, contradicting `Φ(u) ≤ Φ(t)`.
  have hmon := hmono u t hu0 hut.le htR
  linarith [mul_nonneg (sq_nonneg η) hω.le]
/-- **Lower integral over a closed ball from uniform annular bounds** (Simon Ch. 5, proof of
Lemma 2.5, inequality (1), which follows from Ch. 4, 4.7 and 2.4: the monotone-convergence step
from the annuli `B_s(y) \ B_t(y)` to the ball as `t ↓ 0`).  If `g ≥ 0`, `g(y) = 0` and, for every
`t ∈ (0, s)`, `g` is `μ`-integrable on the annulus `B_s(y) \ B_t(y)` with
`∫_{B_s(y) \ B_t(y)} g dμ ≤ M`, then `∫⁻_{B_s(y)} g dμ ≤ M`.

Proof: for `ν = μ.withDensity g` the annuli `A_k = B_s(y) \ B_{s/(k+2)}(y)` increase, satisfy
`ν(A_k) = ∫_{A_k} g dμ ≤ M` and cover `B_s(y) \ {y}`, while `ν {y} = g(y) μ {y} = 0`; continuity
from below gives `ν(B_s(y)) ≤ M`. -/
theorem aal_lintegral_closedBall_le_of_annuli : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (y : Amb n ℓ) (s M : ℝ), 0 < s → (∀ x, 0 ≤ g x) → g y = 0 → (∀ t : ℝ, 0 < t → t < s → IntegrableOn g (closedBall y s \ closedBall y t) μ ∧ ∫ x in closedBall y s \ closedBall y t, g x ∂μ ≤ M) → ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal M := by
  intro n ℓ μ g y s M hs hg0 hgy hann
  set ν : Measure (Amb n ℓ) := μ.withDensity (fun x => ENNReal.ofReal (g x)) with hν
  set A : ℕ → Set (Amb n ℓ) := fun k => closedBall y s \ closedBall y (s / ((k : ℝ) + 2)) with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_closedBall.diff measurableSet_closedBall
  -- The annuli increase, since the inner radii `s / (k + 2)` decrease.
  have hAmono : Monotone A := by
    intro i j hij
    refine Set.sdiff_subset_sdiff_right (closedBall_subset_closedBall ?_)
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact div_le_div_of_nonneg_left hs.le (by positivity) (by linarith)
  -- `ν(A_k) = ∫_{A_k} g dμ ≤ M`, by the hypothesis with `t = s / (k + 2) ∈ (0, s)`.
  have hAle : ∀ k, ν (A k) ≤ ENNReal.ofReal M := by
    intro k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have ht0 : 0 < s / ((k : ℝ) + 2) := div_pos hs hk2
    have hts : s / ((k : ℝ) + 2) < s := by
      rw [div_lt_iff₀ hk2]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    obtain ⟨hint, hle⟩ := hann _ ht0 hts
    rw [hν, withDensity_apply _ (hAmeas k),
      ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => hg0 x)]
    exact ENNReal.ofReal_le_ofReal hle
  -- Every `x ∈ B_s(y) \ {y}` lies in `A_k` as soon as `k > s / |x - y|`.
  have hcover : closedBall y s ⊆ (⋃ k, A k) ∪ {y} := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inr hxy
    · refine Or.inl (mem_iUnion.2 ?_)
      have hd : 0 < dist x y := dist_pos.2 hxy
      obtain ⟨k, hk⟩ := exists_nat_gt (s / dist x y)
      refine ⟨k, hx, ?_⟩
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      rw [mem_closedBall, not_le, div_lt_iff₀ hk2]
      rw [div_lt_iff₀ hd] at hk
      nlinarith
  -- The center carries no `ν`-mass because `g(y) = 0`.
  have hy : ν {y} = 0 := by
    rw [hν, withDensity_apply _ (measurableSet_singleton y), lintegral_singleton, hgy,
      ENNReal.ofReal_zero, zero_mul]
  calc ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ = ν (closedBall y s) := by
        rw [hν, withDensity_apply _ measurableSet_closedBall]
    _ ≤ ν ((⋃ k, A k) ∪ {y}) := measure_mono hcover
    _ ≤ ν (⋃ k, A k) + ν {y} := measure_union_le _ _
    _ = ν (⋃ k, A k) := by rw [hy, add_zero]
    _ = ⨆ k, ν (A k) := hAmono.measure_iUnion
    _ ≤ ENNReal.ofReal M := iSup_le hAle
/-- Simon Ch. 4, 3.9–3.10 and 4.5–4.9 (the step `ω_n Θ ≤ Φ(t)` behind Ch. 4, Remark 4.10(1)), for
an arbitrary measure `μ`: write `c(t) = A (t/R)^β` with `β > 0` and
`Φ(s) = F(s) s⁻ⁿ μ(B_s(x)) + (F(s) − 1)`.  If `|F − 1| ≤ c` on `(0, R]`, `Φ` is nondecreasing on
`(0, R]` and `μ(B_r(x)) / (ω rⁿ) → θ₀` as `r ↓ 0`, then `F(s) → 1` and `Φ(s) → ω θ₀` as `s ↓ 0`, so
`ω θ₀ ≤ Φ(t) ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)` for every `t ∈ (0, R]`. -/
theorem aal_dge1_density_le_monotone_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (x : Amb n ℓ) (ω R A β θ₀ : ℝ) (F : ℝ → ℝ), 0 < ω → 0 < R → 0 < β → 0 ≤ θ₀ → (∀ t : ℝ, 0 < t → t ≤ R → |F t - 1| ≤ A * (t / R) ^ β) → (∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R → F s * ((μ (closedBall x s)).toReal / s ^ n) + (F s - 1) ≤ F t * ((μ (closedBall x t)).toReal / t ^ n) + (F t - 1)) → Tendsto (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (ω * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ₀)) → ∀ t : ℝ, 0 < t → t ≤ R → ω * θ₀ ≤ (1 + A * (t / R) ^ β) * ((μ (closedBall x t)).toReal / t ^ n) + A * (t / R) ^ β := by
  intro n ℓ μ x ω R A β θ₀ F hω hR hβ hθ₀ hF hmono hdens t ht htR
  -- Step 1: `c(s) = A (s/R)^β → A 0^β = 0` as `s ↓ 0`, since `β > 0`.
  have hc : Tendsto (fun s : ℝ => A * (s / R) ^ β) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => A * (s / R) ^ β) (𝓝 0) (𝓝 (A * ((0 : ℝ) / R) ^ β)) :=
      (((continuous_id.div_const R).tendsto 0).rpow_const (Or.inr hβ.le)).const_mul A
    rw [zero_div, Real.zero_rpow hβ.ne', mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  -- `(0, t)` is a right neighbourhood of `0` inside `(0, R]`.
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  -- Step 2: `F(s) → 1` as `s ↓ 0`, squeezing `0 ≤ |F(s) − 1| ≤ c(s)`.
  have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hc
    filter_upwards [hev] with s hs
    rw [Real.norm_eq_abs]
    exact hF s hs.1 (hs.2.le.trans htR)
  -- Step 3: `s⁻ⁿ μ(B_s(x)) = ω · toReal (μ(B_s(x)) / ofReal (ω sⁿ)) → ω θ₀`, since `toReal` is
  -- continuous at the finite limit `ofReal θ₀`.
  have hm : Tendsto (fun s : ℝ => (μ (closedBall x s)).toReal / s ^ n) (𝓝[>] 0) (𝓝 (ω * θ₀)) := by
    have h1 : Tendsto (fun s => (μ (closedBall x s) / ENNReal.ofReal (ω * s ^ n)).toReal)
        (𝓝[>] 0) (𝓝 θ₀) := by
      have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hdens
      rwa [ENNReal.toReal_ofReal hθ₀] at this
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ω * (μ (closedBall x s) / ENNReal.ofReal (ω * s ^ n)).toReal =
        (μ (closedBall x s)).toReal / s ^ n := by
      filter_upwards [hev] with s hs
      have hs0 : 0 < s ^ n := pow_pos hs.1 n
      rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity)]
      field_simp
    exact (h1.const_mul ω).congr' h2
  -- Step 4: `Φ(s) → 1 · ω θ₀ + (1 − 1) = ω θ₀` as `s ↓ 0`.
  have hΦ : Tendsto (fun s => F s * ((μ (closedBall x s)).toReal / s ^ n) + (F s - 1)) (𝓝[>] 0)
      (𝓝 (ω * θ₀)) := by
    have := (hF1.mul hm).add (hF1.sub_const 1)
    simpa using this
  -- Step 5: `ω θ₀ ≤ Φ(t)`, letting `s ↓ 0` in `Φ(s) ≤ Φ(t)` for `s ∈ (0, t)`.
  have hle : ω * θ₀ ≤ F t * ((μ (closedBall x t)).toReal / t ^ n) + (F t - 1) := by
    apply le_of_tendsto hΦ
    filter_upwards [hev] with s hs
    exact hmono s t hs.1 hs.2.le htR
  -- Step 6: `F(t) − 1 ≤ c(t)` and `t⁻ⁿ μ(B_t(x)) ≥ 0` give
  -- `Φ(t) ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)`.
  have hFt := hF t ht htR
  have hmt : 0 ≤ (μ (closedBall x t)).toReal / t ^ n :=
    div_nonneg ENNReal.toReal_nonneg (by positivity)
  have hFle : F t ≤ 1 + A * (t / R) ^ β := by linarith [le_abs_self (F t - 1)]
  have := mul_le_mul_of_nonneg_right hFle hmt
  linarith [le_abs_self (F t - 1)]
/-- Simon Ch. 4, 3.11 and Remark 4.10(1), for an arbitrary measure `μ`: let `y ∈ spt μ` with
`μ(B_{2r}(y)) < ∞`, let `c ≥ 0` on `(0, r]` with `c(t) → 0` as `t ↓ 0`, and suppose that for
`μ`-a.e. `x ∈ B̆_r(y)` the estimate `ω ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)` holds for every
`t ∈ (0, r]`.  Every neighbourhood of `y` has positive measure, so it contains such a good point
`x`; `B_t(x) ⊆ B_u(y)` when `|x − y| < u − t`, and `μ(B_u(y)) → μ(B_t(y))` as `u ↓ t`, so the
estimate also holds at `y`.  Since `c(s) → 0`, this gives `μ(B_s(y)) ≥ (1 − ε) ω sⁿ` for all small
`s > 0`. -/
theorem aal_dge1_support_density_lower_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (ω r : ℝ) (c : ℝ → ℝ), 0 < ω → 0 < r → y ∈ μ.support → μ (closedBall y (2 * r)) < ⊤ → (∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t) → Tendsto c (𝓝[>] 0) (𝓝 0) → (∀ᵐ x ∂μ, x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r → ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) → ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (ω * s ^ n)) ≤ μ (closedBall y s) := by
  intro n ℓ μ y ω r c hω hr hy hfin hc0 hc hae ε hε
  -- Step 1: `μ(B_u(y)) ≤ μ(B_{2r}(y)) < ∞` for `u ≤ 2r`.
  have hfin' : ∀ u : ℝ, u ≤ 2 * r → μ (closedBall y u) ≠ ⊤ := fun u hu =>
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall hu)) hfin).ne
  -- Steps 2–4: the estimate also holds at `y`, for every `t ∈ (0, r]`.
  have hA : ∀ t : ℝ, 0 < t → t ≤ r →
      ω ≤ (1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t := by
    intro t ht htr
    have hct : 0 ≤ c t := hc0 t ht htr
    have htn : 0 < t ^ n := pow_pos ht n
    -- Steps 2–3: for `u ∈ (t, t + r)`, `B̆_{u−t}(y)` has positive measure, so it is not inside the
    -- null set of bad points; a good point `x` in it has `B_t(x) ⊆ B_u(y)`.
    have hu : ∀ u : ℝ, t < u → u < t + r →
        ω ≤ (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t := by
      intro u htu hut
      have hη : 0 < u - t := sub_pos.mpr htu
      have hpos : 0 < μ (ball y (u - t)) :=
        (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hη)
      obtain ⟨x, hxb, hx⟩ : ∃ x ∈ ball y (u - t), (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
          ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) := by
        by_contra hcon
        have hsub : ball y (u - t) ⊆ {x | ¬ (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
            ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t)} := by
          intro x hx hgood
          exact hcon ⟨x, hx, hgood⟩
        exact absurd (measure_mono_null hsub (ae_iff.mp hae)) hpos.ne'
      have hxr : x ∈ ball y r := ball_subset_ball (by linarith) hxb
      have h1 := hx hxr t ht htr
      have hsub : closedBall x t ⊆ closedBall y u := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [mem_ball] at hxb
        linarith [dist_triangle z x y]
      have hle : (μ (closedBall x t)).toReal ≤ (μ (closedBall y u)).toReal :=
        ENNReal.toReal_mono (hfin' u (by linarith)) (measure_mono hsub)
      have : (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) ≤
          (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_right hle htn.le
      linarith
    -- Step 4: `μ(B_u(y)) → μ(B_t(y))` as `u ↓ t`, by continuity from above
    -- (`⋂_{u > t} B_u(y) = B_t(y)` and `μ(B_{2r}(y)) < ∞`); pass to the limit in Step 3.
    have hlim : Tendsto (fun u => (μ (closedBall y u)).toReal) (𝓝[>] t)
        (𝓝 ((μ (closedBall y t)).toReal)) := by
      have h1 := tendsto_measure_biInter_gt (μ := μ) (s := fun u => closedBall y u) (a := t)
        (fun u _ => measurableSet_closedBall.nullMeasurableSet)
        (fun i j _ hij => closedBall_subset_closedBall hij)
        ⟨2 * r, by linarith, hfin.ne⟩
      rw [biInter_gt_closedBall] at h1
      exact (ENNReal.tendsto_toReal (hfin' t (by linarith))).comp h1
    have hlim2 : Tendsto (fun u => (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t)
        (𝓝[>] t) (𝓝 ((1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t)) :=
      ((hlim.div_const _).const_mul _).add_const _
    apply ge_of_tendsto hlim2
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + r)] with u hu'
    exact hu u hu'.1 hu'.2
  rcases le_or_gt 1 ε with h1 | h1
  -- Step 5: for `ε ≥ 1` the left side is `ofReal` of a nonpositive number, i.e. `0`.
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0:ℝ) < s := hs
    have : (1 - ε) * (ω * s ^ n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [ENNReal.ofReal_of_nonpos this]
    exact zero_le
  -- Step 6: for `0 < ε < 1` put `γ = εω/(1 + ω)`.  Once `c(s) < γ` and `s < r`, the estimate at `y`
  -- gives `ω ≤ (1 + γ) q + γ` for `q = s⁻ⁿ μ(B_s(y))`, which forces `q ≥ (1 − ε) ω`.
  · set γ := ε * ω / (1 + ω) with hγ_def
    have hγ : 0 < γ := by positivity
    have hγ' : γ * (1 + ω) = ε * ω := by rw [hγ_def]; field_simp
    have hev1 : ∀ᶠ s in 𝓝[>] (0:ℝ), c s < γ := hc.eventually (gt_mem_nhds hγ)
    have hev2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
    filter_upwards [hev1, hev2] with s hcs hs
    have hA' := hA s hs.1 hs.2.le
    have hsn : 0 < s ^ n := pow_pos hs.1 n
    have hcs0 : 0 ≤ c s := hc0 s hs.1 hs.2.le
    set q := (μ (closedBall y s)).toReal / s ^ n with hq_def
    have hq : 0 ≤ q := div_nonneg ENNReal.toReal_nonneg hsn.le
    have h2 : ω ≤ (1 + γ) * q + γ := by nlinarith
    have key : (1 - ε) * ω ≤ q := by
      by_contra hlt
      push Not at hlt
      have h3 : (1 + γ) * q < (1 + γ) * ((1 - ε) * ω) := mul_lt_mul_of_pos_left hlt (by linarith)
      have h4 : 0 < γ * ε * ω := by positivity
      nlinarith [hγ']
    have key2 : (1 - ε) * (ω * s ^ n) ≤ (μ (closedBall y s)).toReal := by
      have h5 : (μ (closedBall y s)).toReal = q * s ^ n := by
        rw [hq_def, div_mul_cancel₀ _ hsn.ne']
      rw [h5]
      nlinarith [mul_le_mul_of_nonneg_right key hsn.le]
    rw [← ENNReal.ofReal_toReal (hfin' s (by linarith [hs.2]))]
    exact ENNReal.ofReal_le_ofReal key2
/-- **Simon Ch. 4, 3.2–3.3 and 4.1** (first variation of the radial cutoff fields).  Let `V` have
generalized mean curvature `H` in `U`, with `p_{T_x M}` the projection onto an `n`-plane for
`μ_V`-a.e. `x`.  Let `φ ∈ C¹(ℝ)` with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[T, ∞)`, let `ρ > 0`, and
let `B_{Tρ}(y) ⊆ U`.  Then `X(x) = φ(r/ρ)(x − y)`, `r = |x − y|`, is admissible in 3.14, and
`div_M X = n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − |(x − y) − p_{T_x M}(x − y)|²/r²)` `μ_V`-a.e.
(both sides equal `n` at `x = y`).  So `∫ div_M X dμ_V = −∫ X · H dμ_V` is the stated identity. -/
theorem aal_radial_first_variation_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (y : Amb n ℓ) (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → closedBall y (T * ρ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH hP y φ T ρ hφ hφ1 hφT hρ hU
  -- Step 1: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
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
  -- Step 2: `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
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
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  -- Step 3: `X · H = φ(r/ρ)(x - y) · H`.
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
    -- `D|· - y|(x) = r⁻¹ (x - y) · ⬝`, from `|z - y| = √(|z - y|²)`.
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
  -- Step 5: `trace p_P = dim P` and `trace ((a id + c (u · ⬝) u) ∘ p_P) = a dim P + c u · p_P u`.
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
  -- Step 6: `div_M X` equals the integrand at every `x` where `p_{T_x M}` projects onto an
  -- `n`-plane `P`.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    obtain ⟨P, hPn, hPx⟩ := hx
    rw [RectifiableVarifold.divM, hPx]
    by_cases hxy : x = y
    · -- At the center `DX(y) = id`, so `div_M X(y) = n = n φ(0)`.
      have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
        rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
        exact (hasFDerivAt_sub_const y).fderiv
      rw [hfd]
      simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
      subst hxy
      simp [hφ1 0 zero_le_one]
    · -- Away from it, `(x - y) · p_P (x - y) = |p_P (x - y)|²` and Pythagoras.
      rw [(hXderiv x hxy).fderiv, htr, hPn]
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
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
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
/-- **Simon Ch. 4, 3.4** (differentiating a scaled radial cutoff integral with a bounded weight).
Let `φ` be `C¹` and nonincreasing with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[1 + ε, ∞)`, let
`μ(B_S(y)) < ∞`, and let `q` be a.e. strongly measurable with `|q| ≤ B` a.e.; write
`r = ‖x − y‖`.  If `0 < t` and `(1 + ε) t < S`, then `φ(r/t) q` and `(r/t) φ'(r/t) q` are
`μ`-integrable, and `s ↦ ∫ φ(r/s) q dμ` has derivative `-(1/t) ∫ (r/t) φ'(r/t) q dμ` at `t`.
For `0 < s < S/(1 + ε)` the integrands vanish off `B_S(y)`, so the integrals may be taken against
the finite measure `μ ⌞ B_S(y)`.  There `|u φ'(u)| ≤ C` for `u ≥ 0` bounds the `s`-derivatives by
`2CB/t` on `(t/2, S/(1 + ε))`, and one differentiates under the integral sign. -/
theorem aal_cfs_hasDerivAt_cutoff_integral : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (q : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S ε B t : ℝ), 0 < ε → μ (closedBall y S) < ⊤ → AEStronglyMeasurable q μ → (∀ᵐ x ∂μ, |q x| ≤ B) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, 1 + ε ≤ s → φ s = 0) → 0 < t → (1 + ε) * t < S → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ ∧ Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x) μ ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * q x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂μ) / t) t := by
  intro n ℓ μ q y φ S ε B t hε hμS hq hqB hφ hanti hone hzero ht htS
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  -- Step 1: `0 ≤ φ ≤ 1`, `φ` and `φ'` are continuous, `φ' = 0` on `(1 + ε, ∞)`, and
  -- `|u φ'(u)| ≤ C` for `u ≥ 0`.
  have hφc : Continuous φ := hφ.continuous
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hφnn : ∀ s, 0 ≤ φ s := fun s => by
    have h := hanti (le_max_left s (1 + ε))
    rwa [hzero _ (le_max_right _ _)] at h
  have hφle : ∀ s, φ s ≤ 1 := fun s => by
    have h := hanti (min_le_left s 1)
    rwa [hone _ (min_le_right _ _)] at h
  have hdzero : ∀ s, 1 + ε < s → deriv φ s = 0 := fun s hs => by
    have h : φ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hs] with u hu
      exact hzero u hu.le
    exact h.deriv_eq.trans (deriv_const s 0)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → |u * deriv φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 + ε)).exists_bound_of_continuousOn
      (continuous_id.mul hdφc).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    rcases le_or_gt u (1 + ε) with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hdzero u h, mul_zero, abs_zero]
      exact le_max_right _ _
  -- Step 2: for `s ≠ 0`, `d/ds φ(r/s) = -(r/s) φ'(r/s) / s`.
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
  -- Step 3: for `0 < s < R = S/(1 + ε)` the integrands vanish off `K = B_S(y)`, so their
  -- `μ`-integrals are integrals for the finite measure `ν = μ ⌞ K`.
  set K : Set (Amb n ℓ) := closedBall y S with hKdef
  set ν : Measure (Amb n ℓ) := μ.restrict K with hνdef
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hμS.ne
  set R : ℝ := S / (1 + ε) with hRdef
  have hRiff : ∀ s : ℝ, s < R ↔ (1 + ε) * s < S := fun s => by
    rw [hRdef, lt_div_iff₀ hε1, mul_comm]
  have htR : t < R := (hRiff t).2 htS
  have hout : ∀ s, 0 < s → s < R → ∀ x, x ∉ K → 1 + ε < ‖x - y‖ / s := by
    intro s hs hsR x hx
    have hxS : S < ‖x - y‖ := by
      simpa [hKdef, mem_closedBall, dist_eq_norm, not_le] using hx
    rw [lt_div_iff₀ hs]
    linarith [(hRiff s).1 hsR]
  have hconv : ∀ s, 0 < s → s < R →
      ∫ x, φ (‖x - y‖ / s) * q x ∂μ = ∫ x, φ (‖x - y‖ / s) * q x ∂ν := by
    intro s hs hsR
    rw [hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hzero _ (hout s hs hsR x hx).le, zero_mul]
  have hconv' : ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂μ =
      ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂ν := by
    rw [hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hdzero _ (hout t ht htR x hx), mul_zero, zero_mul]
  -- Step 4: the integrands are bounded by `B` and `C B` on the finite measure `ν`, hence
  -- `ν`-integrable; vanishing off `K`, they are `μ`-integrable.
  have hqν : AEStronglyMeasurable q ν := hq.restrict
  have hqBν : ∀ᵐ x ∂ν, |q x| ≤ B := ae_restrict_of_ae hqB
  have hint1 : ∀ s, Integrable (fun x => φ (‖x - y‖ / s) * q x) ν := by
    intro s
    refine Integrable.of_bound ((hφc.comp (by fun_prop :
      Continuous fun x : Amb n ℓ => ‖x - y‖ / s)).aestronglyMeasurable.mul hqν) B ?_
    filter_upwards [hqBν] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφnn _)]
    calc φ (‖x - y‖ / s) * |q x| ≤ 1 * |q x| :=
          mul_le_mul_of_nonneg_right (hφle _) (abs_nonneg _)
      _ ≤ B := by rw [one_mul]; exact hx
  have hint2 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x) ν := by
    refine Integrable.of_bound ((by fun_prop : Continuous fun x : Amb n ℓ =>
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t)).aestronglyMeasurable.mul hqν) (C * B) ?_
    filter_upwards [hqBν] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hC _ (div_nonneg (norm_nonneg _) ht.le)) hx (abs_nonneg _) hC0
  have hμint : ∀ f : Amb n ℓ → ℝ, Integrable f ν → (∀ x, x ∉ K → f x = 0) → Integrable f μ := by
    intro f hf hf0
    refine (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp hf
    intro x hx
    by_contra h
    exact hx (hf0 x h)
  refine ⟨hμint _ (hint1 t) (fun x hx => by rw [hzero _ (hout t ht htR x hx).le, zero_mul]),
    hμint _ hint2 (fun x hx => by rw [hdzero _ (hout t ht htR x hx), mul_zero, zero_mul]), ?_⟩
  -- Step 5: differentiate under the integral sign for `ν` on `U = (t/2, R)`, with the
  -- integrable constant bound `2 C B / t`.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s x => φ (‖x - y‖ / s) * q x)
    (F' := fun s x => -(‖x - y‖ / s * deriv φ (‖x - y‖ / s)) / s * q x)
    (x₀ := t) (bound := fun _ => 2 * C * B / t) (s := Ioo (t / 2) R)
    (Ioo_mem_nhds (half_lt_self ht) htR) ?_ (hint1 t) ?_ ?_ (integrable_const _) ?_
  -- Step 6: the `ν`- and `μ`-integrals agree near `t`, so the derivative transfers to `μ`.
  · have hderivν := key.2
    have heq : (∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t * q x ∂ν) =
        -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂μ) / t := by
      rw [hconv', ← integral_neg, ← integral_div]
      congr 1
      funext x
      ring
    rw [heq] at hderivν
    refine hderivν.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht htR] with s hs
    exact hconv s hs.1 hs.2
  · exact Eventually.of_forall fun s => (hφc.comp (by fun_prop :
      Continuous fun x : Amb n ℓ => ‖x - y‖ / s)).aestronglyMeasurable.mul hqν
  · exact (by fun_prop : Continuous fun x : Amb n ℓ =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t).aestronglyMeasurable.mul hqν
  · filter_upwards [hqBν] with x hx s hs
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    have hB : 0 ≤ B := (abs_nonneg _).trans hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs0]
    calc |‖x - y‖ / s * deriv φ (‖x - y‖ / s)| / s * |q x| ≤ C / s * B :=
          mul_le_mul (div_le_div_of_nonneg_right
            (hC _ (div_nonneg (norm_nonneg _) hs0.le)) hs0.le) hx (abs_nonneg _)
            (div_nonneg hC0 hs0.le)
      _ ≤ 2 * C * B / t := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hs0 ht]
          nlinarith [hs.1, mul_nonneg hC0 hB]
  · filter_upwards with x s hs
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    exact (hderiv ‖x - y‖ s hs0.ne').mul_const (q x)

/-- Simon Ch. 4, 4.1–4.3 (continuity in the scale of the cutoff pairing): let `φ` be `C¹` and
nonincreasing with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[1 + ε, ∞)`, and let `H` be
`μ`-integrable on `B_S(y)`.  Then `L(s) = ∫ φ(‖x − y‖/s) (x − y)·H(x) dμ(x)` is continuous at
every `t > 0` with `(1 + ε) t < S`.  For `0 < s < S/(1 + ε)` the integrand vanishes off
`B_S(y)` and is bounded there by `S ‖H‖`, so dominated convergence applies to `μ ⌞ B_S(y)`. -/
theorem aal_cfs_cutoff_pairing_continuousAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S ε t : ℝ), 0 < ε → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, 1 + ε ≤ s → φ s = 0) → 0 < t → (1 + ε) * t < S → ContinuousAt (fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ) t := by
  intro n ℓ μ H y φ S ε t hε hH hφ hanti hone hzero ht htS
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hHν : Integrable H (μ.restrict (closedBall y S)) := hH
  -- Step 1: `φ` is continuous, and `0 ≤ φ ≤ 1` because `φ` is nonincreasing.
  have hφc : Continuous φ := hφ.continuous
  have hφnn : ∀ s, 0 ≤ φ s := fun s => by
    have h := hanti (le_max_left s (1 + ε))
    rwa [hzero _ (le_max_right _ _)] at h
  have hφle : ∀ s, φ s ≤ 1 := fun s => by
    have h := hanti (min_le_left s 1)
    rwa [hone _ (min_le_right _ _)] at h
  -- `t < R* := S/(1 + ε)`.
  have htR : t < S / (1 + ε) := by
    rw [lt_div_iff₀ hε1]
    linarith
  -- Step 2: for `s ∈ (0, R*)` the integrand vanishes off `B_S(y)` (there `‖x − y‖/s ≥ 1 + ε`),
  -- so `L(s)` is the integral against `μ ⌞ B_S(y)`.
  have hconv : ∀ s ∈ Ioo 0 (S / (1 + ε)),
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S)) =
        ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ := by
    rintro s ⟨hs, hsR⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hε1] at hsR
    have h1 : 1 + ε ≤ ‖x - y‖ / s := by
      rw [le_div_iff₀ hs]
      linarith
    rw [hzero _ h1, zero_mul]
  -- Step 3: dominated convergence for the `μ ⌞ B_S(y)`-integral at `t`, with bound `S ‖H‖`.
  have hmain : ContinuousAt (fun s =>
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S))) t := by
    refine continuousAt_of_dominated (bound := fun x => S * ‖H x‖) ?_ ?_
      (hHν.norm.const_mul S) ?_
    · -- Measurability: `x ↦ φ(‖x − y‖/s)` is continuous and `x ↦ (x − y)·H(x)` is
      -- a.e. strongly measurable.
      refine Eventually.of_forall fun s => ?_
      have hcut : Continuous fun x : Amb n ℓ => φ (‖x - y‖ / s) := hφc.comp (by fun_prop)
      exact hcut.aestronglyMeasurable.mul
        (continuous_inner.comp_aestronglyMeasurable
          ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
            hHν.aestronglyMeasurable))
    · -- Domination: on `B_S(y)`, `|φ(‖x − y‖/s) (x − y)·H(x)| ≤ ‖x − y‖ ‖H x‖ ≤ S ‖H x‖`.
      refine Eventually.of_forall fun s => ?_
      rw [ae_restrict_iff' measurableSet_closedBall]
      refine Eventually.of_forall fun x hx => ?_
      rw [mem_closedBall, dist_eq_norm] at hx
      calc ‖φ (‖x - y‖ / s) * inner ℝ (x - y) (H x)‖
          = φ (‖x - y‖ / s) * ‖inner ℝ (x - y) (H x)‖ := by
            rw [norm_mul, Real.norm_of_nonneg (hφnn _)]
        _ ≤ 1 * (‖x - y‖ * ‖H x‖) :=
            mul_le_mul (hφle _) (norm_inner_le_norm _ _) (norm_nonneg _) zero_le_one
        _ ≤ S * ‖H x‖ := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · -- Pointwise continuity in `s` at `t ≠ 0`, since `φ` is continuous.
      refine Eventually.of_forall fun x => ?_
      exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')).mul
        continuousAt_const
  -- Step 4: both functions agree on the neighbourhood `(0, R*)` of `t`.
  exact hmain.congr (Filter.eventually_of_mem (Ioo_mem_nhds ht htR) hconv)

/-- Simon Ch. 4, (4.3)–(4.4), in abstract form (`P = I'`, and `Q` plays the role of `J'`): if on
`(0, R)` we have `I' = P`, `L` continuous, `I ≥ 0`, `nI − tP + tQ = −L`,
`a = (L/t^{n+1})/(1 + I/tⁿ)` and `|a| ≤ M t^{−β}` with `β < 1`, then
`Ψ(s) = exp(−∫₀ˢ a)(1 + I(s)/sⁿ)` satisfies `Ψ'(t) = exp(−∫₀ᵗ a) Q(t)/tⁿ`, and
`exp(−∫₀^ρ |a|) ≤ exp(−∫₀ᵗ a) ≤ exp(∫₀^ρ |a|)` for `0 < t ≤ ρ < R`. -/
theorem aal_cfs_integrating_factor_deriv : ∀ (n : ℕ) (I L a P Q : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t : ℝ, 0 < t → t < R → HasDerivAt I (P t) t) → (∀ t : ℝ, 0 < t → t < R → ContinuousAt L t) → (∀ t : ℝ, 0 < t → t < R → 0 ≤ I t) → (∀ t : ℝ, 0 < t → t < R → (n : ℝ) * I t - t * P t + t * Q t = -L t) → (∀ t : ℝ, 0 < t → t < R → a t = L t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → (∀ t : ℝ, 0 < t → t < R → HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n)) (Real.exp (-∫ u in (0)..t, a u) * (Q t / t ^ n)) t) ∧ (∀ t ρ : ℝ, 0 < t → t ≤ ρ → ρ < R → Real.exp (-∫ u in (0)..ρ, |a u|) ≤ Real.exp (-∫ u in (0)..t, a u) ∧ Real.exp (-∫ u in (0)..t, a u) ≤ Real.exp (∫ u in (0)..ρ, |a u|)) := by
  intro n I L a P Q R M β hβ hIder hLc hInn hid ha hab
  have hden : ∀ t, 0 < t → t < R → 1 ≤ 1 + I t / t ^ n := fun t ht htR => by
    have := div_nonneg (hInn t ht htR) (pow_pos ht n).le
    linarith
  -- `a` is continuous on `(0, R)`
  have hacontAt : ∀ t, 0 < t → t < R → ContinuousAt a t := by
    intro t ht htR
    have hev : (fun s => L s / s ^ (n + 1) / (1 + I s / s ^ n)) =ᶠ[𝓝 t] a := by
      filter_upwards [Ioo_mem_nhds ht htR] with s hs
      exact (ha s hs.1 hs.2).symm
    refine ContinuousAt.congr ?_ hev
    exact ((hLc t ht htR).div ((continuous_pow (n + 1)).continuousAt)
      (pow_ne_zero _ ht.ne')).div
      (continuousAt_const.add ((hIder t ht htR).continuousAt.div
        ((continuous_pow n).continuousAt) (pow_ne_zero _ ht.ne')))
      (by linarith [hden t ht htR])
  have hacont : ContinuousOn a (Ioo 0 R) := fun t ht =>
    (hacontAt t ht.1 ht.2).continuousWithinAt
  -- `a` is integrable on `[0, t]`, by the bound `|a s| ≤ M s^(-β)` with `β < 1`
  have haint : ∀ t, 0 < t → t < R → IntervalIntegrable a volume 0 t := by
    intro t ht htR
    refine IntervalIntegrable.mono_fun' (g := fun s => M * s ^ (-β)) ?_ ?_ ?_
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
    · rw [uIoc_of_le ht.le]
      exact (hacont.mono (Ioc_subset_Ioo_right htR)).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
      show ‖a s‖ ≤ M * s ^ (-β)
      rw [Real.norm_eq_abs]
      exact hab s hs.1 (lt_of_le_of_lt hs.2 htR)
  -- the fundamental theorem of calculus for `∫₀ᵗ a`
  have hGderiv : ∀ t, 0 < t → t < R → HasDerivAt (fun u => ∫ s in (0)..u, a s) (a t) t := by
    intro t ht htR
    exact intervalIntegral.integral_hasDerivAt_right (haint t ht htR)
      (hacont.stronglyMeasurableAtFilter isOpen_Ioo t ⟨ht, htR⟩) (hacontAt t ht htR)
  refine ⟨fun t ht htR => ?_, fun t ρ ht htρ hρR => ?_⟩
  · have hd := ((hGderiv t ht htR).neg.exp).mul ((hasDerivAt_const t (1 : ℝ)).add
      ((hIder t ht htR).div (hasDerivAt_pow n t) (pow_ne_zero n ht.ne')))
    have hd' : HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n))
        (Real.exp (-∫ u in (0)..t, a u) * -a t * (1 + I t / t ^ n) +
          Real.exp (-∫ u in (0)..t, a u) *
            (0 + (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2)) t := hd
    convert hd' using 1
    set E := Real.exp (-∫ u in (0)..t, a u) with hEdef
    have hP : 0 < t ^ n := pow_pos ht n
    have hden' : 1 + I t / t ^ n ≠ 0 := by linarith [hden t ht htR]
    have haL : a t * (1 + I t / t ^ n) = L t / (t ^ n * t) := by
      rw [ha t ht htR, div_mul_cancel₀ _ hden', pow_succ]
    have hnpow : (n : ℝ) * t ^ (n - 1) = n * t ^ n / t := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [eq_div_iff ht.ne', mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    have hq : (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2 =
        (t * P t - n * I t) / (t ^ n * t) := by
      rw [hnpow]
      field_simp
    have hidt : t * P t - n * I t = t * Q t + L t := by linarith [hid t ht htR]
    have hQ : (t * Q t + L t) / (t ^ n * t) = Q t / t ^ n + L t / (t ^ n * t) := by
      field_simp
    rw [hq, hidt, hQ]
    linear_combination E * haL
  · have hiρ := haint ρ (ht.trans_le htρ) hρR
    have h1 : |∫ u in (0)..t, a u| ≤ ∫ u in (0)..t, |a u| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    have h2 : ∫ u in (0)..t, |a u| ≤ ∫ u in (0)..ρ, |a u| :=
      intervalIntegral.integral_mono_interval le_rfl ht.le htρ
        (Eventually.of_forall fun u => abs_nonneg _) hiρ.abs
    have h3 := abs_le.mp (h1.trans h2)
    exact ⟨Real.exp_le_exp.mpr (by linarith [h3.2]), Real.exp_le_exp.mpr (by linarith [h3.1])⟩

/-- **Integrated squeeze from the derivative comparison** (Simon Ch. 4, 3.4 → 3.5 "by
integration in 3.4", with the prefactors of 3.5 in corrected order).  Write `r = |x − y|` and,
for `t > 0`, `J'(t) = −t⁻¹ ∫ (r/t) φ'(r/t) w dμ`.  If `0 ≤ w ≤ 1` a.e., `φ` is a `C¹`
nonincreasing cutoff (`φ = 1` on `(−∞, 1]`, `φ = 0` on `[1 + ε, ∞)`), `0 < σ ≤ ρ`,
`(1 + ε)ρ < S`, `μ(B_S(y)) < ∞`, and on `[σ, ρ]` both `e^{−c} ≤ F ≤ e^c` and `Ψ' = F J'/tⁿ`,
then with `A = ∫ (φ(r/ρ) − φ(r/σ)) w / rⁿ dμ`,
`e^{−c} A ≤ Ψ(ρ) − Ψ(σ) ≤ e^c (1 + ε)ⁿ A`.
Proof: take the comparison weight `q = w / max(σ, r)ⁿ` and `G(t) = ∫ φ(r/t) q dμ`, whose
derivative `G'` comes from `aal_cfs_hasDerivAt_cutoff_integral`.  Where `∂ₜ φ(r/t) ≠ 0` we have
`t ≤ r ≤ (1 + ε)t` and `q = w/rⁿ`, so integrating in `x` gives `0 ≤ G' ≤ J'/tⁿ ≤ (1 + ε)ⁿ G'` on
`[σ, ρ]`.  Hence `Ψ − e^{−c} G` and `e^c (1 + ε)ⁿ G − Ψ` have nonnegative derivatives there and
are monotone (mean value theorem), and `G(ρ) − G(σ) = A`. -/
theorem aal_cfs_squeeze_of_deriv : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ Ψ F : ℝ → ℝ) (S ε c σ ρ : ℝ), 0 < ε → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ s : ℝ, s ≤ 1 → φ s = 1) → (∀ s : ℝ, 1 + ε ≤ s → φ s = 0) → 0 < σ → σ ≤ ρ → (1 + ε) * ρ < S → (∀ t : ℝ, σ ≤ t → t ≤ ρ → Real.exp (-c) ≤ F t ∧ F t ≤ Real.exp c) → (∀ t : ℝ, σ ≤ t → t ≤ ρ → HasDerivAt Ψ (F t * ((-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t) / t ^ n)) t) → Real.exp (-c) * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ ≤ Ψ ρ - Ψ σ ∧ Ψ ρ - Ψ σ ≤ Real.exp c * (1 + ε) ^ n * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ := by
  intro n ℓ μ w y φ Ψ F S ε c σ ρ hε hμS hw hw01 hφ hanti hone hzero hσ hσρ hρS hF hΨ
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  -- `φ' = 0` off `[1, 1 + ε]`, and `φ' ≤ 0`
  have hdlo : ∀ s, s < 1 → deriv φ s = 0 := fun s hs => by
    have h : φ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [gt_mem_nhds hs] with u hu
      exact hone u hu.le
    exact h.deriv_eq.trans (deriv_const s 1)
  have hdhi : ∀ s, 1 + ε < s → deriv φ s = 0 := fun s hs => by
    have h : φ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hs] with u hu
      exact hzero u hu.le
    exact h.deriv_eq.trans (deriv_const s 0)
  have hdnp : ∀ s, deriv φ s ≤ 0 := fun s => hanti.deriv_nonpos
  -- the radii `t ∈ [σ, ρ]` are admissible for `aal_cfs_hasDerivAt_cutoff_integral`
  have hadm : ∀ t, σ ≤ t → t ≤ ρ → 0 < t ∧ (1 + ε) * t < S := fun t h1 h2 =>
    ⟨hσ.trans_le h1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 hε1.le) hρS⟩
  -- the comparison weight `q = w / max(σ, r)ⁿ`, bounded by `σ⁻ⁿ`
  set q : Amb n ℓ → ℝ := fun x => w x / (max σ ‖x - y‖) ^ n with hqdef
  have hq : AEStronglyMeasurable q μ :=
    hw.div₀ (by fun_prop : Continuous fun x : Amb n ℓ => (max σ ‖x - y‖) ^ n).aestronglyMeasurable
  have hqB : ∀ᵐ x ∂μ, |q x| ≤ 1 / σ ^ n := by
    filter_upwards [hw01] with x hx
    have hm : 0 < max σ ‖x - y‖ := lt_of_lt_of_le hσ (le_max_left _ _)
    rw [hqdef, abs_div, abs_of_nonneg hx.1, abs_of_pos (pow_pos hm n),
      div_le_div_iff₀ (pow_pos hm n) (pow_pos hσ n)]
    calc w x * σ ^ n ≤ 1 * σ ^ n := mul_le_mul_of_nonneg_right hx.2 (pow_pos hσ n).le
      _ ≤ 1 * (max σ ‖x - y‖) ^ n := by
        gcongr
        exact le_max_left _ _
  have hw1 : ∀ᵐ x ∂μ, |w x| ≤ 1 :=
    hw01.mono fun x hx => abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  -- the sibling cutoff derivative, with the weights `q` and `w`
  have hG := fun t (h1 : σ ≤ t) (h2 : t ≤ ρ) =>
    Submission.aal_cfs_hasDerivAt_cutoff_integral n ℓ μ q y φ S ε (1 / σ ^ n) t hε hμS hq hqB
      hφ hanti hone hzero (hadm t h1 h2).1 (hadm t h1 h2).2
  have hJ := fun t (h1 : σ ≤ t) (h2 : t ≤ ρ) =>
    Submission.aal_cfs_hasDerivAt_cutoff_integral n ℓ μ w y φ S ε 1 t hε hμS hw hw1
      hφ hanti hone hzero (hadm t h1 h2).1 (hadm t h1 h2).2
  set G : ℝ → ℝ := fun s => ∫ x, φ (‖x - y‖ / s) * q x ∂μ with hGdef
  set G' : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * q x ∂μ) / t
    with hG'eq
  set N : ℝ → ℝ := fun t => (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t) / t ^ n
    with hNdef
  -- pointwise, then integrated, comparison of the scale derivatives
  have hcmp : ∀ t, σ ≤ t → t ≤ ρ → G' t ≤ N t ∧ N t ≤ (1 + ε) ^ n * G' t ∧ 0 ≤ G' t := by
    intro t h1 h2
    have ht : 0 < t := (hadm t h1 h2).1
    set D : Amb n ℓ → ℝ := fun x => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t with hDdef
    have eG : G' t = ∫ x, D x * q x ∂μ := by
      rw [hG'eq, hDdef]
      dsimp only
      rw [← integral_neg, ← integral_div]
      congr 1
      funext x
      ring
    have eN : N t = ∫ x, D x * w x / t ^ n ∂μ := by
      rw [hNdef, hDdef]
      dsimp only
      rw [← integral_neg, ← integral_div, ← integral_div]
      congr 1
      funext x
      ring
    have intG : Integrable (fun x => D x * q x) μ := by
      have h := ((hG t h1 h2).2.1.const_mul (-1 / t))
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [hDdef]
      ring
    have intN : Integrable (fun x => D x * w x / t ^ n) μ := by
      have h := ((hJ t h1 h2).2.1.const_mul (-1 / t / t ^ n))
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [hDdef]
      ring
    have hpt : ∀ᵐ x ∂μ, D x * q x ≤ D x * w x / t ^ n ∧
        D x * w x / t ^ n ≤ (1 + ε) ^ n * (D x * q x) ∧ 0 ≤ D x * q x := by
      filter_upwards [hw01] with x hx
      have hD0 : 0 ≤ D x := by
        simp only [hDdef]
        apply div_nonneg _ ht.le
        rw [neg_nonneg]
        exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (norm_nonneg _) ht.le) (hdnp _)
      by_cases hd : deriv φ (‖x - y‖ / t) = 0
      · have hD : D x = 0 := by simp only [hDdef, hd, mul_zero, neg_zero, zero_div]
        simp [hD]
      · -- here `1 ≤ r/t ≤ 1 + ε`, so `σ ≤ t ≤ r ≤ (1 + ε)t` and `q = w/rⁿ`
        have hlo : 1 ≤ ‖x - y‖ / t := by
          by_contra h
          exact hd (hdlo _ (lt_of_not_ge h))
        have hhi : ‖x - y‖ / t ≤ 1 + ε := by
          by_contra h
          exact hd (hdhi _ (lt_of_not_ge h))
        have htr : t ≤ ‖x - y‖ := by rwa [le_div_iff₀ ht, one_mul] at hlo
        have hrt : ‖x - y‖ ≤ (1 + ε) * t := by rwa [div_le_iff₀ ht] at hhi
        have hr : 0 < ‖x - y‖ := ht.trans_le htr
        have hqx : q x = w x / ‖x - y‖ ^ n := by
          simp only [hqdef, max_eq_right (h1.trans htr)]
        have hDw : 0 ≤ D x * w x := mul_nonneg hD0 hx.1
        have hrn : 0 < ‖x - y‖ ^ n := pow_pos hr n
        have htn : 0 < t ^ n := pow_pos ht n
        rw [hqx, ← mul_div_assoc]
        refine ⟨div_le_div_of_nonneg_left hDw htn (pow_le_pow_left₀ ht.le htr n), ?_,
          div_nonneg hDw hrn.le⟩
        have hpow : ‖x - y‖ ^ n ≤ (1 + ε) ^ n * t ^ n := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ hr.le hrt n
        calc D x * w x / t ^ n = (D x * w x) * (1 / t ^ n) := by ring
          _ ≤ (D x * w x) * ((1 + ε) ^ n / ‖x - y‖ ^ n) := by
              apply mul_le_mul_of_nonneg_left _ hDw
              rw [div_le_div_iff₀ htn hrn]
              linarith [hpow]
          _ = (1 + ε) ^ n * (D x * w x / ‖x - y‖ ^ n) := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [eG, eN]
      exact integral_mono_ae intG intN (hpt.mono fun x hx => hx.1)
    · rw [eN, eG, ← integral_const_mul]
      exact integral_mono_ae intN (intG.const_mul _) (hpt.mono fun x hx => hx.2.1)
    · rw [eG]
      exact integral_nonneg_of_ae (hpt.mono fun x hx => hx.2.2)
  have hGder : ∀ t, σ ≤ t → t ≤ ρ → HasDerivAt G (G' t) t := fun t h1 h2 => (hG t h1 h2).2.2
  -- a function with nonnegative derivative at every point of `[σ, ρ]` increases from `σ` to `ρ`
  have hmono : ∀ (f : ℝ → ℝ) (f' : ℝ → ℝ), (∀ t, σ ≤ t → t ≤ ρ → HasDerivAt f (f' t) t) →
      (∀ t, σ ≤ t → t ≤ ρ → 0 ≤ f' t) → f σ ≤ f ρ := by
    intro f f' hf hf'
    have hm : MonotoneOn f (Icc σ ρ) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc σ ρ)
      · intro t ht
        exact (hf t ht.1 ht.2).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hf t ht.1.le ht.2.le).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hf t ht.1.le ht.2.le).deriv]
        exact hf' t ht.1.le ht.2.le
    exact hm ⟨le_rfl, hσρ⟩ ⟨hσρ, le_rfl⟩ hσρ
  -- `e^{−c} G' ≤ Ψ' ≤ e^c (1 + ε)ⁿ G'` on `[σ, ρ]`, integrated
  have hlow := hmono (fun t => Ψ t - Real.exp (-c) * G t)
    (fun t => F t * N t - Real.exp (-c) * G' t)
    (fun t h1 h2 => (hΨ t h1 h2).sub ((hGder t h1 h2).const_mul _))
    (fun t h1 h2 => by
      obtain ⟨hc1, -, hc3⟩ := hcmp t h1 h2
      obtain ⟨hF1, -⟩ := hF t h1 h2
      have hN0 : 0 ≤ N t := hc3.trans hc1
      have := mul_le_mul hF1 hc1 hc3 ((Real.exp_pos _).le.trans hF1)
      linarith)
  have hup := hmono (fun t => Real.exp c * (1 + ε) ^ n * G t - Ψ t)
    (fun t => Real.exp c * (1 + ε) ^ n * G' t - F t * N t)
    (fun t h1 h2 => ((hGder t h1 h2).const_mul _).sub (hΨ t h1 h2))
    (fun t h1 h2 => by
      obtain ⟨hc1, hc2, hc3⟩ := hcmp t h1 h2
      obtain ⟨-, hF2⟩ := hF t h1 h2
      have hN0 : 0 ≤ N t := hc3.trans hc1
      have h1' := mul_le_mul_of_nonneg_right hF2 hN0
      have h2' := mul_le_mul_of_nonneg_left hc2 (Real.exp_pos c).le
      nlinarith)
  -- the increment of `G` is the annular integral `A`
  have hA : G ρ - G σ = ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ := by
    rw [hGdef]
    dsimp only
    rw [← integral_sub (hG ρ hσρ le_rfl).1 (hG σ le_rfl hσρ).1]
    congr 1
    funext x
    by_cases hr : ‖x - y‖ ≤ σ
    · have h1 : ‖x - y‖ / σ ≤ 1 := (div_le_one hσ).mpr hr
      have h2 : ‖x - y‖ / ρ ≤ 1 := (div_le_one (hσ.trans_le hσρ)).mpr (hr.trans hσρ)
      rw [hone _ h1, hone _ h2]
      ring
    · have hmax : max σ ‖x - y‖ = ‖x - y‖ := max_eq_right (le_of_lt (lt_of_not_ge hr))
      simp only [hqdef, hmax]
      ring
  rw [← hA]
  beta_reduce at hlow hup
  constructor <;> nlinarith [hlow, hup]

/-- **Integrating-factor squeeze for one cutoff** (Simon Ch. 4, 3.4–3.5 and 4.3–4.4, with the
weight `|D^⊥ r|²` replaced by an abstract `w`, `0 ≤ w ≤ 1`, and the Hölder bound 3.1 by
`|a(t)| ≤ M t^{−β}`, `β < 1`).  Write `r = |x − y|`, `I(t) = ∫ φ(r/t) dμ`,
`L(t) = ∫ φ(r/t) (x − y)·H dμ` and `a(t) = t^{−(n+1)} L(t) / (1 + t^{−n} I(t))`.  If the radial
identity `∫ (n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − w)) dμ = −L(ρ)` holds whenever `0 < ρ`,
`(1 + ε)ρ ≤ S`, then for `0 < σ ≤ ρ`, `(1 + ε)ρ < S`, with `F(t) = exp(−∫_0^t a)`,
`c = ∫_0^ρ |a|` and `A = ∫ (φ(r/ρ) − φ(r/σ)) w / rⁿ dμ`,
`e^{−c} A ≤ F(ρ)(1 + ρ^{−n} I(ρ)) − F(σ)(1 + σ^{−n} I(σ)) ≤ e^c (1 + ε)ⁿ A`.

With `P(t) = I'(t)` and `Q(t) = J'(t)` (`J(t) = ∫ φ(r/t) w dμ`) from
`aal_cfs_hasDerivAt_cutoff_integral`, the radial identity splits into
`n I(t) − t P(t) + t Q(t) = −L(t)`; `L` is continuous by `aal_cfs_cutoff_pairing_continuousAt`.
`aal_cfs_integrating_factor_deriv` turns this into `(F (1 + t^{−n} I))' = F Q / tⁿ` and
`e^{−c} ≤ F ≤ e^c` on `(0, ρ]`, and `aal_cfs_squeeze_of_deriv` integrates the squeeze. -/
theorem aal_cutoff_integrating_factor_squeeze : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (S ε M β : ℝ), 0 < ε → β < 1 → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, 1 + ε ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → (1 + ε) * ρ ≤ S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → (1 + ε) * t < S → |a t| ≤ M * t ^ (-β)) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → (1 + ε) * ρ < S → Real.exp (-∫ t in (0)..ρ, |a t|) * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ ≤ Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n) - Real.exp (-∫ t in (0)..σ, a t) * (1 + I σ / σ ^ n) ∧ Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n) - Real.exp (-∫ t in (0)..σ, a t) * (1 + I σ / σ ^ n) ≤ Real.exp (∫ t in (0)..ρ, |a t|) * (1 + ε) ^ n * ∫ x, (φ (‖x - y‖ / ρ) - φ (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ := by
  intro n ℓ μ H w y φ I a S ε M β hε hβ hμS hw hw01 hH hφ hanti hone hzero hrad hI ha hab
    σ ρ hσ hσρ hρS
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  -- All radii used below lie in `(0, S / (1 + ε))`, i.e. `0 < t` and `(1 + ε) t < S`.
  have hRiff : ∀ t : ℝ, t < S / (1 + ε) ↔ (1 + ε) * t < S := fun t => by
    rw [lt_div_iff₀ hε1, mul_comm]
  have hρR : ρ < S / (1 + ε) := (hRiff ρ).2 hρS
  -- `0 ≤ φ`, so `I ≥ 0`; `|w| ≤ 1` a.e.
  have hφnn : ∀ s, 0 ≤ φ s := fun s => by
    have h := hanti (le_max_left s (1 + ε))
    rwa [hzero _ (le_max_right _ _)] at h
  have hw1 : ∀ᵐ x ∂μ, |w x| ≤ 1 :=
    hw01.mono fun x hx => abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hc1 : ∀ᵐ x ∂μ, |(fun _ : Amb n ℓ => (1 : ℝ)) x| ≤ 1 :=
    Eventually.of_forall fun x => by simp
  -- The cutoff derivative with weight `1`: integrability and `I' = P`.
  have hB1 : ∀ t : ℝ, 0 < t → (1 + ε) * t < S →
      Integrable (fun x => φ (‖x - y‖ / t)) μ ∧
        Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧
        HasDerivAt I (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t) t := by
    intro t ht htS
    have h := Submission.aal_cfs_hasDerivAt_cutoff_integral n ℓ μ (fun _ => 1) y φ S ε 1 t hε
      hμS aestronglyMeasurable_const hc1 hφ hanti hone hzero ht htS
    simp only [mul_one] at h
    refine ⟨h.1, h.2.1, ?_⟩
    rw [show I = fun s => ∫ x, φ (‖x - y‖ / s) ∂μ from funext hI]
    exact h.2.2
  -- The cutoff derivative with weight `w`: integrability of `(r/t) φ'(r/t) w`.
  have hBw := fun t (ht : 0 < t) (htS : (1 + ε) * t < S) =>
    Submission.aal_cfs_hasDerivAt_cutoff_integral n ℓ μ w y φ S ε 1 t hε hμS hw hw1 hφ hanti
      hone hzero ht htS
  -- The integrating factor `F` and its bounds, from the differential identity
  -- `n I(t) − t P(t) + t Q(t) = −L(t)` (the radial identity split into integrable pieces).
  obtain ⟨hD1, hD2⟩ := Submission.aal_cfs_integrating_factor_deriv n I
    (fun t => ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) a
    (fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t)
    (fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t)
    (S / (1 + ε)) M β hβ
    (fun t ht htR => (hB1 t ht ((hRiff t).1 htR)).2.2)
    (fun t ht htR => Submission.aal_cfs_cutoff_pairing_continuousAt n ℓ μ H y φ S ε t hε hH hφ
      hanti hone hzero ht ((hRiff t).1 htR))
    (fun t _ _ => by
      rw [hI t]
      exact integral_nonneg fun x => hφnn _)
    (fun t ht htR => by
      have htS := (hRiff t).1 htR
      obtain ⟨h1f, h1d, -⟩ := hB1 t ht htS
      obtain ⟨-, hwd, -⟩ := hBw t ht htS
      have hR := hrad t ht htS.le
      have e1 : ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) +
            ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ =
          ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) +
            (‖x - y‖ / t * deriv φ (‖x - y‖ / t) -
              ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x)) ∂μ := by
        congr 1
        funext x
        ring
      have h2 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) -
          ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) μ := h1d.sub hwd
      rw [e1, integral_add (h1f.const_mul _) h2, integral_const_mul,
        integral_sub h1d hwd, ← hI t] at hR
      have ht0 : t ≠ 0 := ht.ne'
      have key : ∀ z : ℝ, t * (-z / t) = -z := fun z => by field_simp
      rw [key, key]
      linarith)
    (fun t _ _ => ha t)
    (fun t ht htR => hab t ht ((hRiff t).1 htR))
  -- Integrate the squeeze `e^{−c} ≤ F ≤ e^c` against `Q / tⁿ = J' / tⁿ` over `[σ, ρ]`.
  exact Submission.aal_cfs_squeeze_of_deriv n ℓ μ w y φ
    (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n))
    (fun t => Real.exp (-∫ u in (0)..t, a u)) S ε (∫ t in (0)..ρ, |a t|) σ ρ hε hμS hw hw01
    hφ hanti hone hzero hσ hσρ hρS
    (fun t hσt htρ => hD2 t ρ (hσ.trans_le hσt) htρ hρR)
    (fun t hσt htρ => hD1 t (hσ.trans_le hσt) (htρ.trans_lt hρR))
/-- **Simon Ch. 4, 3.6 and 4.5–4.7** (monotonicity from the radial first-variation identity, with
`κ = (p − n)/(4p)`).  Let `p > n ≥ 1`, `0 < R < S`, `Λ > 0`, `μ(B_S(y)) < ∞`, `0 ≤ w ≤ 1` `μ`-a.e.,
`H` integrable on `B_S(y)` with `∫_{B_S(y)} |H|ᵖ dμ < ∞` and `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ κΛ`,
and suppose `∫ (n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − w)) dμ = −∫ φ(r/ρ) (x − y)·H dμ`, `r = |x − y|`, for every
`C¹` cutoff `φ` (`φ = 1` on `(−∞, 1]`, `φ = 0` on `[T, ∞)`) and `ρ > 0` with `Tρ ≤ S`.

Proof: for `φ_k = 1 − smoothTransition((· − 1)/ε_k)` with `ε_k ↓ 0`, the Hölder bound
`Submission.aal_curvature_pairing_holder_bound` gives `|a_k(t)| ≤ 2‖H‖_{Lᵖ(B_S)} t^{−n/p}` for
`a_k(t) = t^{−n−1} ∫ φ_k(r/t)(x − y)·H dμ / (1 + t^{−n} ∫ φ_k(r/t) dμ)`, and
`Submission.aal_cutoff_integrating_factor_squeeze` gives the squeeze for each `k`.  Dominated
convergence (in `x` and in `t`) passes to `k → ∞`: with
`a₀(t) = t^{−n−1} ∫_{B_t(y)} (x − y)·H dμ / (1 + t^{−n} μ(B_t(y)))`, the Hölder bound for `1_{B_t(y)}` gives
`∫₀ʳ |a₀| ≤ (Λ/4)(r/R)^{1−n/p}`, so `F(t) = exp(−∫₀ᵗ a₀)` satisfies the bounds on `(0, R]`, and
`Φ(t) = F(t) t⁻ⁿ μ(B_t(y)) + F(t) − 1` satisfies
`e^{−Λ} ∫_{B_r(y)∖B_s(y)} w/rⁿ dμ ≤ Φ(r) − Φ(s) ≤ e^{Λ} ∫_{B_r(y)∖B_s(y)} w/rⁿ dμ` for `0 < s ≤ r ≤ R`. -/
theorem aal_monotonicity_of_radial_identity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn H (closedBall y S) μ → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂μ < ⊤ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ ≤ S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → IntegrableOn (fun x => w x / ‖x - y‖ ^ n) (closedBall y r \ closedBall y s) μ ∧ Real.exp (-Λ) * ∫ x in closedBall y r \ closedBall y s, w x / ‖x - y‖ ^ n ∂μ ≤ (F r * ((μ (closedBall y r)).toReal / r ^ n) + (F r - 1)) - (F s * ((μ (closedBall y s)).toReal / s ^ n) + (F s - 1)) ∧ (F r * ((μ (closedBall y r)).toReal / r ^ n) + (F r - 1)) - (F s * ((μ (closedBall y s)).toReal / s ^ n) + (F s - 1)) ≤ Real.exp Λ * ∫ x in closedBall y r \ closedBall y s, w x / ‖x - y‖ ^ n ∂μ) := by
  -- Steps 3-4: C^1 cutoffs φ k s = 1 - smoothTransition ((s - 1) / ε k) with ε k = ε₁ / (k + 1) → 0.
  have hCutoffSeq : ∀ ε₁ : ℝ, 0 < ε₁ → ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ ε₁) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) ∧ (∀ k s, s ≤ 1 → φ k s = 1) ∧ (∀ k s, 1 + ε k ≤ s → φ k s = 0) ∧ (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0) := by
    intro ε₁ hε₁
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun k : ℕ => ε₁ / ((k : ℝ) + 1) := ⟨_, rfl⟩
    have hεpos : ∀ k, 0 < ε k := fun k => by
      rw [hεdef]
      exact div_pos hε₁ (by positivity)
    have hεle : ∀ k, ε k ≤ ε₁ := fun k => by
      rw [hεdef]
      exact div_le_self hε₁.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε₁
      rw [mul_zero] at h
      refine h.congr fun k => ?_
      rw [hεdef]
      ring
    refine ⟨fun k s => 1 - Real.smoothTransition ((s - 1) / ε k), ε,
      fun k => ⟨hεpos k, hεle k⟩, hεlim, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
    · intro k s t hst
      have h1 : (s - 1) / ε k ≤ (t - 1) / ε k :=
        div_le_div_of_nonneg_right (by linarith) (hεpos k).le
      have := Real.smoothTransition.monotone h1
      show 1 - Real.smoothTransition ((t - 1) / ε k) ≤ 1 - Real.smoothTransition ((s - 1) / ε k)
      linarith
    · intro k s
      have h0 := Real.smoothTransition.nonneg ((s - 1) / ε k)
      have h1 := Real.smoothTransition.le_one ((s - 1) / ε k)
      show 0 ≤ 1 - Real.smoothTransition ((s - 1) / ε k) ∧ 1 - Real.smoothTransition ((s - 1) / ε k) ≤ 1
      constructor <;> linarith
    · intro k s hs
      have h1 : (s - 1) / ε k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (hεpos k).le
      show 1 - Real.smoothTransition ((s - 1) / ε k) = 1
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
    · intro k s hs
      have h1 : 1 ≤ (s - 1) / ε k := by
        rw [le_div_iff₀ (hεpos k)]
        linarith
      show 1 - Real.smoothTransition ((s - 1) / ε k) = 0
      rw [Real.smoothTransition.one_of_one_le h1, sub_self]
    · intro s hs
      have hev : ∀ᶠ k in atTop, ε k ≤ s - 1 :=
        hεlim.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < s - 1))
      filter_upwards [hev] with k hk
      have h1 : 1 ≤ (s - 1) / ε k := by
        rw [le_div_iff₀ (hεpos k)]
        linarith
      show 1 - Real.smoothTransition ((s - 1) / ε k) = 0
      rw [Real.smoothTransition.one_of_one_le h1, sub_self]
  -- Helper for steps 5 and 9: b ^ e ≤ 1 + b for b ≥ 0 and 0 ≤ e ≤ 1.
  have hRpowLeOneAdd : ∀ {b e : ℝ}, 0 ≤ b → 0 ≤ e → e ≤ 1 → b ^ e ≤ 1 + b := by
    intro b e hb he0 he1
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h he0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h he1
      rw [Real.rpow_one] at this
      linarith
  -- Steps 5 and 9 (algebra): |L| ≤ t N I ^ (1 - 1/p) gives |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ N t ^ (-n/p).
  have hCoeffBound : ∀ (n : ℕ) (p t N I L : ℝ), 1 < p → 0 < t → 0 ≤ N → 0 ≤ I → |L| ≤ t * N * I ^ (1 - 1 / p) → |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ N * t ^ (-((n : ℝ) / p)) := by
    intro n p t N I L hp ht hN hI hL
    have hp0 : 0 < p := by linarith
    have htn : 0 < t ^ n := pow_pos ht n
    set b := I / t ^ n with hbdef
    have hb : 0 ≤ b := div_nonneg hI htn.le
    have hIb : I = b * t ^ n := by
      rw [hbdef, div_mul_cancel₀ _ htn.ne']
    have he0 : 0 ≤ 1 - 1 / p := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    have he1 : 1 - 1 / p ≤ 1 := by
      have : 0 < 1 / p := by positivity
      linarith
    have hpow : I ^ (1 - 1 / p) = b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p)) := by
      rw [hIb, Real.mul_rpow hb htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    have hbe := hRpowLeOneAdd hb he0 he1
    have hden : 0 < 1 + b := by linarith
    have hL' : |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by
      calc |L| ≤ t * N * I ^ (1 - 1 / p) := hL
        _ = t * N * (b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p))) := by rw [hpow]
        _ ≤ t * N * ((1 + b) * t ^ ((n : ℝ) * (1 - 1 / p))) := by
            gcongr
        _ = N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by ring
    have hexp : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
      rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht]
      have h1 : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ ((1 : ℝ) + (n : ℝ) * (1 - 1 / p)) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      rw [h1]
      congr 1
      push_cast
      field_simp
      ring
    rw [abs_div, abs_div, abs_of_pos (pow_pos ht (n + 1)), abs_of_pos hden, div_div,
      div_le_iff₀ (mul_pos (pow_pos ht (n + 1)) hden)]
    calc |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := hL'
      _ = N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + b)) := by rw [hexp]; ring
  -- Step 8: radial cutoff integrals are continuous in the radius on (0, R] (dominated continuity).
  have hCutoffIntCont : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T R : ℝ), 0 < T → T * R ≤ S → IntegrableOn g (closedBall y S) μ → Continuous φ → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → (∀ s, T ≤ s → φ s = 0) → ContinuousOn (fun t => ∫ x, φ (‖x - y‖ / t) * g x ∂μ) (Ioc 0 R) := by
    intro n ℓ μ g y φ S T R hT hTR hg hφc hφ01 hφ0
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y S) := ⟨_, rfl⟩
    have hgν : Integrable g ν := by rw [hν]; exact hg
    have hout : ∀ t ∈ Ioc (0 : ℝ) R, ∀ x, x ∉ closedBall y S → φ (‖x - y‖ / t) * g x = 0 := by
      intro t ht x hx
      have hxS : S < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      have hTt : T * t ≤ T * R := mul_le_mul_of_nonneg_left ht.2 hT.le
      have : T ≤ ‖x - y‖ / t := by
        rw [le_div_iff₀ ht.1]
        linarith
      rw [hφ0 _ this, zero_mul]
    have heq : ∀ t ∈ Ioc (0 : ℝ) R,
        ∫ x, φ (‖x - y‖ / t) * g x ∂μ = ∫ x, φ (‖x - y‖ / t) * g x ∂ν := by
      intro t ht
      rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hout t ht x hx)]
    refine ContinuousOn.congr ?_ heq
    refine continuousOn_of_dominated (bound := fun x => ‖g x‖) ?_ ?_ hgν.norm ?_
    · intro t _
      exact (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable.mul
        hgν.aestronglyMeasurable
    · intro t _
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 _).2
    · refine Eventually.of_forall fun x => ?_
      apply ContinuousOn.mul _ continuousOn_const
      apply hφc.comp_continuousOn
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht
      exact ht.1.ne'
  -- Step 7: radial cutoff integrals converge to closed-ball integrals (dominated convergence).
  have hCutoffIntLim : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (S T t : ℝ), 0 < t → 1 ≤ T → T * t ≤ S → IntegrableOn g (closedBall y S) μ → (∀ k, Continuous (φ k)) → (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) → (∀ k s, s ≤ 1 → φ k s = 1) → (∀ k s, T ≤ s → φ k s = 0) → (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0) → Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * g x ∂μ) atTop (𝓝 (∫ x in closedBall y t, g x ∂μ)) := by
    intro n ℓ μ g y φ S T t ht hT hTt hg hφc hφ01 hφone hφ0 hφev
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y S) := ⟨_, rfl⟩
    have hgν : Integrable g ν := by rw [hν]; exact hg
    have htS : t ≤ S := by nlinarith
    have hout : ∀ k, ∀ x, x ∉ closedBall y S → φ k (‖x - y‖ / t) * g x = 0 := by
      intro k x hx
      have hxS : S < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      have : T ≤ ‖x - y‖ / t := by
        rw [le_div_iff₀ ht]
        linarith
      rw [hφ0 k _ this, zero_mul]
    have heq : ∀ k, ∫ x, φ k (‖x - y‖ / t) * g x ∂μ = ∫ x, φ k (‖x - y‖ / t) * g x ∂ν := by
      intro k
      rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hout k x hx)]
    have hlimeq : ∫ x in closedBall y t, g x ∂μ = ∫ x, (closedBall y t).indicator g x ∂ν := by
      rw [hν, integral_indicator measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall,
        inter_eq_left.mpr (closedBall_subset_closedBall htS)]
    rw [hlimeq]
    refine (tendsto_congr heq).mpr ?_
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖) ?_ hgν.norm ?_ ?_
    · intro k
      exact ((hφc k).comp
        (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable.mul
        hgν.aestronglyMeasurable
    · intro k
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 k _).2
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ closedBall y t
      · rw [indicator_of_mem hx]
        have hle : ‖x - y‖ / t ≤ 1 := by
          rw [div_le_one ht]
          simpa [mem_closedBall, dist_eq_norm] using hx
        have : (fun k => φ k (‖x - y‖ / t) * g x) = fun _ => g x := by
          funext k
          rw [hφone k _ hle, one_mul]
        rw [this]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem hx]
        have hlt : 1 < ‖x - y‖ / t := by
          rw [one_lt_div ht]
          simpa [mem_closedBall, dist_eq_norm, not_le] using hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hφev _ hlt] with k hk
        rw [hk, zero_mul]
  -- Steps 1 and 12: annular integrability, nonnegativity and convergence of the annular cutoff integrals.
  have hAnnularLim : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (S T σ ρ : ℝ), 0 < σ → σ ≤ ρ → 1 ≤ T → T * ρ ≤ S → μ (closedBall y S) < ⊤ → AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, 0 ≤ w x ∧ w x ≤ 1) → (∀ k, Continuous (φ k)) → (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) → (∀ k s, s ≤ 1 → φ k s = 1) → (∀ k s, T ≤ s → φ k s = 0) → (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0) → IntegrableOn (fun x => w x / ‖x - y‖ ^ n) (closedBall y ρ \ closedBall y σ) μ ∧ 0 ≤ ∫ x in closedBall y ρ \ closedBall y σ, w x / ‖x - y‖ ^ n ∂μ ∧ Tendsto (fun k => ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ) atTop (𝓝 (∫ x in closedBall y ρ \ closedBall y σ, w x / ‖x - y‖ ^ n ∂μ)) := by
    intro n ℓ μ w y φ S T σ ρ hσ hσρ hT hTρ hμS hwm hw01 hφc hφ01 hφone hφ0 hφev
    have hρ : 0 < ρ := lt_of_lt_of_le hσ hσρ
    have hρS : ρ ≤ S := by nlinarith
    obtain ⟨A, hA⟩ : ∃ A : Set (Amb n ℓ), A = closedBall y ρ \ closedBall y σ := ⟨_, rfl⟩
    rw [← hA]
    have hAm : MeasurableSet A := by
      rw [hA]
      exact measurableSet_closedBall.diff measurableSet_closedBall
    have hAS : A ⊆ closedBall y S := by
      rw [hA]
      exact sdiff_subset.trans (closedBall_subset_closedBall hρS)
    have hμA : μ A < ⊤ := lt_of_le_of_lt (measure_mono hAS) hμS
    have hfm : AEStronglyMeasurable (fun x => w x / ‖x - y‖ ^ n) μ :=
      hwm.div₀ (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ ^ n).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂μ, σ < ‖x - y‖ → ‖w x / ‖x - y‖ ^ n‖ ≤ (σ ^ n)⁻¹ := by
      filter_upwards [hw01] with x hx hxσ
      have hpos : 0 < ‖x - y‖ ^ n := pow_pos (hσ.trans hxσ) n
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hx.1, abs_of_pos hpos]
      calc w x / ‖x - y‖ ^ n ≤ 1 / ‖x - y‖ ^ n := div_le_div_of_nonneg_right hx.2 hpos.le
        _ ≤ 1 / σ ^ n :=
            one_div_le_one_div_of_le (pow_pos hσ n) (pow_le_pow_left₀ hσ.le hxσ.le n)
        _ = (σ ^ n)⁻¹ := one_div _
    have hmemA : ∀ x, x ∈ A ↔ ‖x - y‖ ≤ ρ ∧ σ < ‖x - y‖ := by
      intro x
      rw [hA]
      simp [mem_closedBall, dist_eq_norm, not_le]
    have hint : IntegrableOn (fun x => w x / ‖x - y‖ ^ n) A μ := by
      refine Measure.integrableOn_of_bounded (M := (σ ^ n)⁻¹) hμA.ne hfm ?_
      rw [ae_restrict_iff' hAm]
      filter_upwards [hbd] with x hx hxA
      exact hx ((hmemA x).mp hxA).2
    refine ⟨hint, ?_, ?_⟩
    · apply setIntegral_nonneg_of_ae_restrict
      filter_upwards [ae_restrict_of_ae hw01] with x hx
      exact div_nonneg hx.1 (pow_nonneg (norm_nonneg _) n)
    · obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y S) := ⟨_, rfl⟩
      have hνfin : IsFiniteMeasure ν := by
        rw [hν]
        exact isFiniteMeasure_restrict.mpr hμS.ne
      have hout : ∀ k x, x ∉ closedBall y S →
          (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) = 0 := by
        intro k x hx
        have hxS : S < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
        have h1 : T ≤ ‖x - y‖ / ρ := by
          rw [le_div_iff₀ hρ]
          linarith
        have h2 : T ≤ ‖x - y‖ / σ := by
          rw [le_div_iff₀ hσ]
          have : T * σ ≤ T * ρ := mul_le_mul_of_nonneg_left hσρ (by linarith)
          linarith
        rw [hφ0 k _ h1, hφ0 k _ h2, sub_self, zero_mul]
      have heq : ∀ k, ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ =
          ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂ν := by
        intro k
        rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hout k x hx)]
      have hlimeq : ∫ x in A, w x / ‖x - y‖ ^ n ∂μ =
          ∫ x, A.indicator (fun x => w x / ‖x - y‖ ^ n) x ∂ν := by
        rw [hν, integral_indicator hAm, Measure.restrict_restrict hAm, inter_eq_left.mpr hAS]
      rw [hlimeq]
      refine (tendsto_congr heq).mpr ?_
      refine tendsto_integral_of_dominated_convergence (fun _ => (σ ^ n)⁻¹) ?_
        (integrable_const _) ?_ ?_
      · intro k
        have h1 : Continuous fun x : Amb n ℓ => φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ) := by
          have := hφc k
          fun_prop
        have hfmν : AEStronglyMeasurable (fun x => w x / ‖x - y‖ ^ n) ν := by
          rw [hν]
          exact hfm.restrict
        exact h1.aestronglyMeasurable.mul hfmν
      · intro k
        have hbdν : ∀ᵐ x ∂ν, σ < ‖x - y‖ → ‖w x / ‖x - y‖ ^ n‖ ≤ (σ ^ n)⁻¹ := by
          rw [hν]
          exact ae_restrict_of_ae hbd
        filter_upwards [hbdν] with x hx
        by_cases hxσ : σ < ‖x - y‖
        · rw [norm_mul]
          have hd : ‖φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)‖ ≤ 1 := by
            rw [Real.norm_eq_abs, abs_le]
            have := hφ01 k (‖x - y‖ / ρ)
            have := hφ01 k (‖x - y‖ / σ)
            constructor <;> linarith
          calc ‖φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)‖ * ‖w x / ‖x - y‖ ^ n‖
              ≤ 1 * (σ ^ n)⁻¹ := mul_le_mul hd (hx hxσ) (norm_nonneg _) zero_le_one
            _ = (σ ^ n)⁻¹ := one_mul _
        · rw [not_lt] at hxσ
          have h1 : ‖x - y‖ / ρ ≤ 1 := by
            rw [div_le_one hρ]
            linarith
          have h2 : ‖x - y‖ / σ ≤ 1 := by
            rw [div_le_one hσ]
            exact hxσ
          rw [hφone k _ h1, hφone k _ h2, sub_self, zero_mul, norm_zero]
          positivity
      · refine Eventually.of_forall fun x => ?_
        by_cases hxσ : ‖x - y‖ ≤ σ
        · have hxA : x ∉ A := fun h => (not_le.mpr ((hmemA x).mp h).2) hxσ
          rw [indicator_of_notMem hxA]
          have h1 : ‖x - y‖ / ρ ≤ 1 := by
            rw [div_le_one hρ]
            linarith
          have h2 : ‖x - y‖ / σ ≤ 1 := by
            rw [div_le_one hσ]
            exact hxσ
          have : (fun k => (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n)) =
              fun _ => 0 := by
            funext k
            rw [hφone k _ h1, hφone k _ h2, sub_self, zero_mul]
          rw [this]
          exact tendsto_const_nhds
        · rw [not_le] at hxσ
          have h2 : 1 < ‖x - y‖ / σ := by
            rw [one_lt_div hσ]
            exact hxσ
          by_cases hxρ : ‖x - y‖ ≤ ρ
          · have hxA : x ∈ A := (hmemA x).mpr ⟨hxρ, hxσ⟩
            rw [indicator_of_mem hxA]
            have h1 : ‖x - y‖ / ρ ≤ 1 := by
              rw [div_le_one hρ]
              exact hxρ
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [hφev _ h2] with k hk
            rw [hφone k _ h1, hk, sub_zero, one_mul]
          · rw [not_le] at hxρ
            have hxA : x ∉ A := fun h => (not_le.mpr hxρ) ((hmemA x).mp h).1
            rw [indicator_of_notMem hxA]
            have h1 : 1 < ‖x - y‖ / ρ := by
              rw [one_lt_div hρ]
              exact hxρ
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [hφev _ h1, hφev _ h2] with k hk1 hk2
            rw [hk1, hk2, sub_self, zero_mul]
  -- Step 11: elementary bounds for exp u when |u| ≤ (Λ / 4) q.
  have hExpBounds : ∀ (Λ q u : ℝ), 0 < Λ → 0 ≤ q → q ≤ 1 → |u| ≤ Λ / 4 * q → Real.exp (-Λ) ≤ Real.exp u ∧ Real.exp u ≤ Real.exp Λ ∧ |Real.exp u - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * q ∧ (Λ ≤ 1 → |Real.exp u - 1| ≤ Λ * q) := by
    intro Λ q u hΛ hq0 hq1 hu
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Λ / 4 * q := ⟨_, rfl⟩
    rw [← hb] at hu
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hbΛ : b ≤ Λ / 4 := by
      rw [hb]
      calc Λ / 4 * q ≤ Λ / 4 * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
        _ = Λ / 4 := mul_one _
    have hu' := abs_le.mp hu
    -- `|exp u - 1| ≤ exp b * b`
    have hkey : |Real.exp u - 1| ≤ Real.exp b * b := by
      rcases le_total 0 u with h | h
      · have h1 : 0 ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
        rw [abs_of_nonneg h1]
        have h2 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
        have h3 : Real.exp u * Real.exp (-u) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have h4 : Real.exp u - 1 ≤ u * Real.exp u := by
          have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos u).le
          nlinarith
        have h5 : u ≤ b := by linarith
        calc Real.exp u - 1 ≤ u * Real.exp u := h4
          _ ≤ b * Real.exp b := mul_le_mul h5 (Real.exp_le_exp.mpr h5) (Real.exp_pos u).le hb0
          _ = Real.exp b * b := mul_comm _ _
      · have h1 : Real.exp u - 1 ≤ 0 := by
          have := Real.exp_le_one_iff.mpr h
          linarith
        rw [abs_of_nonpos h1]
        have h2 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        have h5 : -u ≤ b := by linarith
        have h6 : 1 ≤ Real.exp b := Real.one_le_exp hb0
        nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact Real.exp_le_exp.mpr (by linarith)
    · have h1 : Real.exp (Λ / 4) ≤ Real.exp (Λ / 2) := Real.exp_le_exp.mpr (by linarith)
      have hΛq : 0 ≤ Λ * q := by positivity
      calc |Real.exp u - 1| ≤ Real.exp b * b := hkey
        _ ≤ Real.exp (Λ / 4) * b := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbΛ) hb0
        _ = Real.exp (Λ / 4) / 4 * (Λ * q) := by rw [hb]; ring
        _ ≤ Real.exp (Λ / 2) / 2 * (Λ * q) := by
            apply mul_le_mul_of_nonneg_right _ hΛq
            have := Real.exp_pos (Λ / 4)
            linarith
        _ = Real.exp (Λ / 2) / 2 * Λ * q := by ring
    · intro hΛ1
      have hq4 : Real.exp (1 / 4) ≤ 4 := by
        have h1 : -(1 / 4 : ℝ) + 1 ≤ Real.exp (-(1 / 4)) := Real.add_one_le_exp _
        have h2 : Real.exp (1 / 4) * Real.exp (-(1 / 4)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have h3 := Real.exp_pos (1 / 4 : ℝ)
        nlinarith
      calc |Real.exp u - 1| ≤ Real.exp b * b := hkey
        _ ≤ Real.exp (1 / 4) * b :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hb0
        _ ≤ 4 * b := mul_le_mul_of_nonneg_right hq4 hb0
        _ = Λ * q := by rw [hb]; ring
  -- Steps 9 (bound D.3) and 10-12: passage to the limit k → ∞ in the fixed-cutoff squeeze (D.2).
  have hFactorLimit : ∀ (R β M K Λ : ℝ) (a : ℕ → ℝ → ℝ) (a₀ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (Q₀ : ℝ → ℝ) (A : ℕ → ℝ → ℝ → ℝ) (A₀ : ℝ → ℝ → ℝ) (e : ℕ → ℝ), 0 < R → β < 1 → 0 < Λ → K * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → (∀ k, AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 R))) → (∀ k t, 0 < t → t ≤ R → |a k t| ≤ M * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) → (∀ t, 0 < t → t ≤ R → |a₀ t| ≤ K * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => Q k t) atTop (𝓝 (Q₀ t))) → (∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R → Tendsto (fun k => A k σ ρ) atTop (𝓝 (A₀ σ ρ))) → (∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R → 0 ≤ A₀ σ ρ) → Tendsto e atTop (𝓝 1) → (∀ k σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R → Real.exp (-∫ t in (0)..ρ, |a k t|) * A k σ ρ ≤ Real.exp (-∫ t in (0)..ρ, a k t) * Q k ρ - Real.exp (-∫ t in (0)..σ, a k t) * Q k σ ∧ Real.exp (-∫ t in (0)..ρ, a k t) * Q k ρ - Real.exp (-∫ t in (0)..σ, a k t) * Q k σ ≤ Real.exp (∫ t in (0)..ρ, |a k t|) * e k * A k σ ρ) → (∀ r, 0 < r → r ≤ R → Real.exp (-Λ) ≤ Real.exp (-∫ t in (0)..r, a₀ t) ∧ Real.exp (-∫ t in (0)..r, a₀ t) ≤ Real.exp Λ ∧ |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - β) ∧ (Λ ≤ 1 → |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Λ * (r / R) ^ (1 - β))) ∧ (∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R → Real.exp (-Λ) * A₀ σ ρ ≤ Real.exp (-∫ t in (0)..ρ, a₀ t) * Q₀ ρ - Real.exp (-∫ t in (0)..σ, a₀ t) * Q₀ σ ∧ Real.exp (-∫ t in (0)..ρ, a₀ t) * Q₀ ρ - Real.exp (-∫ t in (0)..σ, a₀ t) * Q₀ σ ≤ Real.exp Λ * A₀ σ ρ) := by
    intro R β M K Λ a a₀ Q Q₀ A A₀ e hR hβ hΛ hK hameas hab halim ha₀b hQlim hAlim hA₀ he hsq
    have hβ1 : 0 < 1 - β := by linarith
    have hgint : ∀ (C ρ : ℝ), IntervalIntegrable (fun t => C * t ^ (-β)) volume 0 ρ := fun C ρ =>
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
    have hameas' : ∀ k ρ, ρ ≤ R → AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 ρ)) :=
      fun k ρ hρR => (hameas k).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hρR) le_rfl)
    -- convergence of the integrals of `a k` and `|a k|`
    have hGlim : ∀ ρ, 0 < ρ → ρ ≤ R →
        Tendsto (fun k => ∫ t in (0)..ρ, a k t) atTop (𝓝 (∫ t in (0)..ρ, a₀ t)) := by
      intro ρ hρ hρR
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => M * t ^ (-β)) ?_ ?_ (hgint M ρ) ?_
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => hameas' k ρ hρR
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact hab k t ht.1 (ht.2.trans hρR)
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun t ht => halim t ht.1 (ht.2.trans hρR)
    have hClim : ∀ ρ, 0 < ρ → ρ ≤ R →
        Tendsto (fun k => ∫ t in (0)..ρ, |a k t|) atTop (𝓝 (∫ t in (0)..ρ, |a₀ t|)) := by
      intro ρ hρ hρR
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => M * t ^ (-β)) ?_ ?_ (hgint M ρ) ?_
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => (hameas' k ρ hρR).norm
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs, abs_abs]
          exact hab k t ht.1 (ht.2.trans hρR)
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun t ht =>
          (continuous_abs.tendsto _).comp (halim t ht.1 (ht.2.trans hρR))
    -- the bound (D.3)
    have hCb : ∀ ρ, 0 < ρ → ρ ≤ R → ∫ t in (0)..ρ, |a₀ t| ≤ Λ / 4 * (ρ / R) ^ (1 - β) := by
      intro ρ hρ hρR
      have h1 : ‖∫ t in (0)..ρ, |a₀ t|‖ ≤ ∫ t in (0)..ρ, K * t ^ (-β) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hρ.le ?_ (hgint K ρ)
        exact Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs, abs_abs]
          exact ha₀b t ht.1 (ht.2.trans hρR)
      have h2 : ∫ t in (0)..ρ, K * t ^ (-β) = K * ρ ^ (1 - β) / (1 - β) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h3 : -β + 1 = 1 - β := by ring
        rw [h3, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]
      have h3 : K * ρ ^ (1 - β) / (1 - β) = K * R ^ (1 - β) / (1 - β) * (ρ / R) ^ (1 - β) := by
        rw [Real.div_rpow hρ.le hR.le]
        have : 0 < R ^ (1 - β) := Real.rpow_pos_of_pos hR _
        field_simp
      have h4 : 0 ≤ (ρ / R) ^ (1 - β) := Real.rpow_nonneg (div_nonneg hρ.le hR.le) _
      calc ∫ t in (0)..ρ, |a₀ t| ≤ ‖∫ t in (0)..ρ, |a₀ t|‖ := by
            rw [Real.norm_eq_abs]
            exact le_abs_self _
        _ ≤ K * ρ ^ (1 - β) / (1 - β) := h1.trans_eq h2
        _ = K * R ^ (1 - β) / (1 - β) * (ρ / R) ^ (1 - β) := h3
        _ ≤ Λ / 4 * (ρ / R) ^ (1 - β) := mul_le_mul_of_nonneg_right hK h4
    have hq1 : ∀ ρ, 0 < ρ → ρ ≤ R → (ρ / R) ^ (1 - β) ≤ 1 := fun ρ hρ hρR =>
      Real.rpow_le_one (div_nonneg hρ.le hR.le) ((div_le_one hR).mpr hρR) hβ1.le
    refine ⟨?_, ?_⟩
    · intro r hr hrR
      have hu : |-∫ t in (0)..r, a₀ t| ≤ Λ / 4 * (r / R) ^ (1 - β) := by
        rw [abs_neg]
        exact (intervalIntegral.abs_integral_le_integral_abs hr.le).trans (hCb r hr hrR)
      exact hExpBounds Λ ((r / R) ^ (1 - β)) _ hΛ
        (Real.rpow_nonneg (div_nonneg hr.le hR.le) _) (hq1 r hr hrR) hu
    · intro σ ρ hσ hσρ hρR
      have hσR : σ ≤ R := hσρ.trans hρR
      have hρ : 0 < ρ := hσ.trans_le hσρ
      have hmid : Tendsto (fun k => Real.exp (-∫ t in (0)..ρ, a k t) * Q k ρ -
          Real.exp (-∫ t in (0)..σ, a k t) * Q k σ) atTop
          (𝓝 (Real.exp (-∫ t in (0)..ρ, a₀ t) * Q₀ ρ - Real.exp (-∫ t in (0)..σ, a₀ t) * Q₀ σ)) := by
        have h1 := ((Real.continuous_exp.tendsto _).comp (hGlim ρ hρ hρR).neg).mul (hQlim ρ hρ hρR)
        have h2 := ((Real.continuous_exp.tendsto _).comp (hGlim σ hσ hσR).neg).mul (hQlim σ hσ hσR)
        exact h1.sub h2
      have hlo : Tendsto (fun k => Real.exp (-∫ t in (0)..ρ, |a k t|) * A k σ ρ) atTop
          (𝓝 (Real.exp (-∫ t in (0)..ρ, |a₀ t|) * A₀ σ ρ)) :=
        ((Real.continuous_exp.tendsto _).comp (hClim ρ hρ hρR).neg).mul (hAlim σ ρ hσ hσρ hρR)
      have hhi : Tendsto (fun k => Real.exp (∫ t in (0)..ρ, |a k t|) * e k * A k σ ρ) atTop
          (𝓝 (Real.exp (∫ t in (0)..ρ, |a₀ t|) * 1 * A₀ σ ρ)) :=
        (((Real.continuous_exp.tendsto _).comp (hClim ρ hρ hρR)).mul he).mul (hAlim σ ρ hσ hσρ hρR)
      have hL := le_of_tendsto_of_tendsto' hlo hmid (fun k => (hsq k σ ρ hσ hσρ hρR).1)
      have hU := le_of_tendsto_of_tendsto' hmid hhi (fun k => (hsq k σ ρ hσ hσρ hρR).2)
      have hc : ∫ t in (0)..ρ, |a₀ t| ≤ Λ := by
        have h1 := hCb ρ hρ hρR
        have h2 : Λ / 4 * (ρ / R) ^ (1 - β) ≤ Λ / 4 * 1 :=
          mul_le_mul_of_nonneg_left (hq1 ρ hρ hρR) (by positivity)
        linarith
      have hA := hA₀ σ ρ hσ hσρ hρR
      constructor
      · refine le_trans ?_ hL
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hA
      · refine hU.trans ?_
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) hA
  -- Assembly (steps 1-13 of the supplied proof).
  intro n ℓ hn p hnp μ H w y R S Λ hR hRS hΛ hμS hwm hw01 hH hHpS hsmall hrad
  -- basic constants
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hβ1 : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hnp
  have hβpos : 0 < 1 - (n : ℝ) / p := by linarith
  have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ.le
  -- Step 2: smallness
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ := ⟨_, rfl⟩
  have hJne : J ≠ ⊤ := by
    rw [hJ]
    exact (lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall hRS.le)) hHpS).ne
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
    ⟨_, rfl⟩
  have hKR : K * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := by
    have hRp : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
    have hp1' : 0 < 1 / p := by positivity
    have h := hsmall
    rw [← hJ] at h
    have hJ' : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJne).symm
    rw [hJ', ← ENNReal.ofReal_mul hRp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRp.le ENNReal.toReal_nonneg) hp1'.le,
      ENNReal.ofReal_le_ofReal_iff hκ] at h
    rw [Real.mul_rpow hRp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hR.le] at h
    have he : (p - n) * (1 / p) = 1 - (n : ℝ) / p := by
      field_simp
    rw [he] at h
    rw [hKdef, ← hJ]
    linarith
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hKR' : K * R ^ (1 - (n : ℝ) / p) / (1 - (n : ℝ) / p) ≤ Λ / 4 := by
    rw [div_le_iff₀ hβpos]
    calc K * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := hKR
      _ = Λ / 4 * (1 - (n : ℝ) / p) := by
          field_simp
  obtain ⟨KS, hKSdef⟩ : ∃ KS : ℝ,
      KS = (∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) := ⟨_, rfl⟩
  have hKS0 : 0 ≤ KS := by
    rw [hKSdef]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hJt : ∀ t, t ≤ S → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ) < ⊤ := fun t htS =>
    lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall htS)) hHpS
  have hNmono : ∀ t t', t ≤ t' → t' ≤ S →
      (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤
        (∫⁻ x in closedBall y t', ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) := by
    intro t t' htt' ht'S
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (hJt t' ht'S).ne
        (lintegral_mono_set (closedBall_subset_closedBall htt'))) (by positivity)
  have hμsub : ∀ t, t ≤ S → μ (closedBall y t) < ⊤ := fun t htS =>
    lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall htS)) hμS
  have hHsub : ∀ t, t ≤ S → IntegrableOn H (closedBall y t) μ := fun t htS =>
    hH.mono_set (closedBall_subset_closedBall htS)
  -- Steps 3-4: the cutoff sequence
  obtain ⟨ε₁, hε₁pos, hε₁le, hε₁R⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ (1 + ε₁) * R < S := by
    refine ⟨min 1 ((S - R) / (2 * R)), lt_min one_pos (div_pos (by linarith) (by linarith)),
      min_le_left _ _, ?_⟩
    have h1 : min 1 ((S - R) / (2 * R)) * R ≤ (S - R) / (2 * R) * R :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    have h2 : (S - R) / (2 * R) * R = (S - R) / 2 := by
      field_simp
    nlinarith
  obtain ⟨φ, ε, hε, hεlim, hφC, hφanti, hφ01, hφone, hφzero, hφev⟩ :=
    hCutoffSeq ε₁ hε₁pos
  have hφc : ∀ k, Continuous (φ k) := fun k => (hφC k).continuous
  have hφzero₁ : ∀ k s, 1 + ε₁ ≤ s → φ k s = 0 := fun k s hs =>
    hφzero k s (le_trans (by linarith [(hε k).2]) hs)
  have hεR : ∀ k, (1 + ε k) * R < S := fun k =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith [(hε k).2]) hR.le) hε₁R
  -- the cutoff quantities
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
    ⟨fun k t => ∫ x, φ k (‖x - y‖ / t) ∂μ, fun _ _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ → ℝ,
      ∀ k t, L k t = ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ :=
    ⟨fun k t => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t = L k t / t ^ (n + 1) / (1 + I k t / t ^ n) :=
    ⟨fun k t => L k t / t ^ (n + 1) / (1 + I k t / t ^ n), fun _ _ => rfl⟩
  have hInn : ∀ k t, 0 ≤ I k t := fun k t => by
    rw [hI]
    exact integral_nonneg fun x => (hφ01 k _).1
  -- Step 5: the bound (D.1) on `a k`
  have hab : ∀ k t, 0 < t → (1 + ε k) * t < S → |a k t| ≤ 2 * KS * t ^ (-((n : ℝ) / p)) := by
    intro k t ht htS
    have hεk := hε k
    have ht' : 0 ≤ (1 + ε k) * t := by
      have : 0 < 1 + ε k := by linarith
      positivity
    have hhol := Submission.aal_curvature_pairing_holder_bound n ℓ p hp1 μ H
      (fun x => φ k (‖x - y‖ / t)) y ((1 + ε k) * t) ht' (hμsub _ htS.le) (hHsub _ htS.le)
      (hJt _ htS.le)
      ((hφc k).comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
      (fun x => hφ01 k _) (fun x hx => hφzero k _ (by
        rw [le_div_iff₀ ht]
        exact hx.le))
    have hN : (∫⁻ x in closedBall y ((1 + ε k) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ KS := by
      rw [hKSdef]
      exact hNmono _ S htS.le le_rfl
    have hNn : 0 ≤ (∫⁻ x in closedBall y ((1 + ε k) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hIp : 0 ≤ I k t ^ (1 - 1 / p) := Real.rpow_nonneg (hInn k t) _
    have hLb : |L k t| ≤ t * (2 * KS) * I k t ^ (1 - 1 / p) := by
      rw [hL]
      rw [← hI] at hhol
      refine hhol.trans ?_
      apply mul_le_mul_of_nonneg_right _ hIp
      have h2 : 1 + ε k ≤ 2 := by linarith
      calc (1 + ε k) * t * (∫⁻ x in closedBall y ((1 + ε k) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p)
          ≤ 2 * t * KS := by
            have := mul_le_mul h2 hN hNn (by norm_num)
            nlinarith
        _ = t * (2 * KS) := by ring
    rw [ha]
    exact hCoeffBound n p t (2 * KS) (I k t) (L k t) hp1 ht (by positivity)
      (hInn k t) hLb
  -- Step 6: the fixed-cutoff squeeze (D.2)
  have hsq : ∀ k σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
      Real.exp (-∫ t in (0)..ρ, |a k t|) *
          ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ ≤
        Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n) -
          Real.exp (-∫ t in (0)..σ, a k t) * (1 + I k σ / σ ^ n) ∧
      Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n) -
          Real.exp (-∫ t in (0)..σ, a k t) * (1 + I k σ / σ ^ n) ≤
        Real.exp (∫ t in (0)..ρ, |a k t|) * (1 + ε k) ^ n *
          ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ := by
    intro k σ ρ hσ hσρ hρR
    have hρS : (1 + ε k) * ρ < S :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hρR (by linarith [(hε k).1])) (hεR k)
    exact Submission.aal_cutoff_integrating_factor_squeeze n ℓ μ H w y (φ k) (I k) (a k) S (ε k)
      (2 * KS) ((n : ℝ) / p) (hε k).1 hβ1 hμS hwm hw01 hH (hφC k) (hφanti k) (hφone k)
      (hφzero k)
      (fun ρ' hρ' hρ'S => hrad (φ k) (1 + ε k) ρ' (hφC k) (hφone k) (hφzero k) hρ' hρ'S)
      (hI k) (fun t => by rw [ha, hL]) (hab k) σ ρ hσ hσρ hρS
  -- Step 8: continuity, hence measurability, of `a k` on `(0, R]`
  have hgint : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y S) μ := by
    refine Integrable.mono' (hH.norm.const_mul S) ?_ ?_
    · exact continuous_inner.comp_aestronglyMeasurable
        ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
          hH.aestronglyMeasurable)
    · rw [ae_restrict_iff' measurableSet_closedBall]
      refine Eventually.of_forall fun x hx => ?_
      have hxS : ‖x - y‖ ≤ S := by simpa [mem_closedBall, dist_eq_norm] using hx
      calc ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
        _ ≤ S * ‖H x‖ := mul_le_mul_of_nonneg_right hxS (norm_nonneg _)
  have h1int : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ :=
    integrableOn_const hμS.ne
  have hIcont : ∀ k, ContinuousOn (I k) (Ioc 0 R) := by
    intro k
    have h := hCutoffIntCont n ℓ μ (fun _ => (1 : ℝ)) y (φ k) S
      (1 + ε k) R (by linarith [(hε k).1]) (hεR k).le h1int (hφc k) (hφ01 k) (hφzero k)
    simp only [mul_one] at h
    exact h.congr fun t _ => hI k t
  have hLcont : ∀ k, ContinuousOn (L k) (Ioc 0 R) := by
    intro k
    have h := hCutoffIntCont n ℓ μ (fun x => inner ℝ (x - y) (H x)) y
      (φ k) S (1 + ε k) R (by linarith [(hε k).1]) (hεR k).le hgint (hφc k) (hφ01 k) (hφzero k)
    exact h.congr fun t _ => hL k t
  have hacont : ∀ k, ContinuousOn (a k) (Ioc 0 R) := by
    intro k
    have h : ContinuousOn (fun t => L k t / t ^ (n + 1) / (1 + I k t / t ^ n)) (Ioc 0 R) := by
      refine ((hLcont k).div (continuousOn_pow (n + 1)) ?_).div
        (continuousOn_const.add ((hIcont k).div (continuousOn_pow n) ?_)) ?_
      · intro t ht
        exact (pow_pos ht.1 _).ne'
      · intro t ht
        exact (pow_pos ht.1 _).ne'
      · intro t ht
        have := div_nonneg (hInn k t) (pow_pos ht.1 n).le
        linarith
    exact h.congr fun t _ => ha k t
  have hameas : ∀ k, AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 R)) := fun k =>
    (hacont k).aestronglyMeasurable measurableSet_Ioc
  -- Step 7: pointwise limits
  have hIlim : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun k => I k t) atTop (𝓝 ((μ (closedBall y t)).toReal)) := by
    intro t ht htR
    have h := hCutoffIntLim n ℓ μ (fun _ => (1 : ℝ)) y φ S (1 + ε₁) t ht
      (by linarith) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith)) hε₁R).le
      h1int hφc hφ01 hφone hφzero₁ hφev
    simp only [mul_one] at h
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real_def] at h
    exact h.congr fun k => (hI k t).symm
  have hLlim : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun k => L k t) atTop (𝓝 (∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ)) := by
    intro t ht htR
    have h := hCutoffIntLim n ℓ μ (fun x => inner ℝ (x - y) (H x)) y φ S
      (1 + ε₁) t ht (by linarith)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith)) hε₁R).le
      hgint hφc hφ01 hφone hφzero₁ hφev
    exact h.congr fun k => (hL k t).symm
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t =
      (∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) /
        (1 + (μ (closedBall y t)).toReal / t ^ n) := ⟨_, fun _ => rfl⟩
  have halim : ∀ t, 0 < t → t ≤ R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
    intro t ht htR
    have hden : 1 + (μ (closedBall y t)).toReal / t ^ n ≠ 0 := by
      have := div_nonneg (ENNReal.toReal_nonneg (a := μ (closedBall y t))) (pow_pos ht n).le
      linarith
    rw [ha₀]
    have h := ((hLlim t ht htR).div_const (t ^ (n + 1))).div
      (tendsto_const_nhds.add ((hIlim t ht htR).div_const (t ^ n))) hden
    exact h.congr fun k => (ha k t).symm
  -- Step 9: the bound (D.3) on `a₀`
  have ha₀b : ∀ t, 0 < t → t ≤ R → |a₀ t| ≤ K * t ^ (-((n : ℝ) / p)) := by
    intro t ht htR
    have htS : t ≤ S := by linarith
    have hhol := Submission.aal_curvature_pairing_holder_bound n ℓ p hp1 μ H
      ((closedBall y t).indicator (fun _ => (1 : ℝ))) y t ht.le (hμsub t htS) (hHsub t htS)
      (hJt t htS) (aestronglyMeasurable_const.indicator measurableSet_closedBall)
      (fun x => by
        by_cases hx : x ∈ closedBall y t
        · simp [hx]
        · simp [hx])
      (fun x hx => by
        have : x ∉ closedBall y t := by
          simpa [mem_closedBall, dist_eq_norm, not_le] using hx
        simp [this])
    have e1 : ∫ x, (closedBall y t).indicator (fun _ => (1 : ℝ)) x * inner ℝ (x - y) (H x) ∂μ =
        ∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      funext x
      by_cases hx : x ∈ closedBall y t
      · simp [hx]
      · simp [hx]
    have e2 : ∫ x, (closedBall y t).indicator (fun _ => (1 : ℝ)) x ∂μ =
        (μ (closedBall y t)).toReal := by
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real_def]
    rw [e1, e2] at hhol
    have hN : (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ K := by
      rw [hKdef]
      exact hNmono t R htR hRS.le
    have hLb : |∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ| ≤
        t * K * (μ (closedBall y t)).toReal ^ (1 - 1 / p) := by
      refine hhol.trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      exact mul_le_mul_of_nonneg_left hN ht.le
    rw [ha₀]
    exact hCoeffBound n p t K _ _ hp1 ht hK0 ENNReal.toReal_nonneg hLb
  -- the uniform bound on `(0, R]`
  have hab' : ∀ k t, 0 < t → t ≤ R → |a k t| ≤ 2 * KS * t ^ (-((n : ℝ) / p)) := by
    intro k t ht htR
    exact hab k t ht (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith [(hε k).1]))
      (hεR k))
  -- Step 12: the annular integrals
  have hann : ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
      IntegrableOn (fun x => w x / ‖x - y‖ ^ n) (closedBall y ρ \ closedBall y σ) μ ∧
      0 ≤ ∫ x in closedBall y ρ \ closedBall y σ, w x / ‖x - y‖ ^ n ∂μ ∧
      Tendsto (fun k => ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ)
        atTop (𝓝 (∫ x in closedBall y ρ \ closedBall y σ, w x / ‖x - y‖ ^ n ∂μ)) := by
    intro σ ρ hσ hσρ hρR
    exact hAnnularLim n ℓ μ w y φ S (1 + ε₁) σ ρ hσ hσρ (by linarith)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hρR (by linarith)) hε₁R).le hμS hwm hw01 hφc
      hφ01 hφone hφzero₁ hφev
  have he : Tendsto (fun k => (1 + ε k) ^ n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hεlim
    rw [add_zero] at h
    simpa using h.pow n
  -- Steps 10-12: passage to the limit
  have hQlim : ∀ t, 0 < t → t ≤ R → Tendsto (fun k => 1 + I k t / t ^ n) atTop
      (𝓝 (1 + (μ (closedBall y t)).toReal / t ^ n)) := fun t ht htR =>
    tendsto_const_nhds.add ((hIlim t ht htR).div_const _)
  obtain ⟨hi, hii⟩ := hFactorLimit R ((n : ℝ) / p) (2 * KS) K Λ a a₀
    (fun k t => 1 + I k t / t ^ n) (fun t => 1 + (μ (closedBall y t)).toReal / t ^ n)
    (fun k σ ρ => ∫ x, (φ k (‖x - y‖ / ρ) - φ k (‖x - y‖ / σ)) * (w x / ‖x - y‖ ^ n) ∂μ)
    (fun σ ρ => ∫ x in closedBall y ρ \ closedBall y σ, w x / ‖x - y‖ ^ n ∂μ)
    (fun k => (1 + ε k) ^ n) hR hβ1 hΛ hKR' hameas hab' halim ha₀b hQlim
    (fun σ ρ hσ hσρ hρR => (hann σ ρ hσ hσρ hρR).2.2)
    (fun σ ρ hσ hσρ hρR => (hann σ ρ hσ hσρ hρR).2.1) he hsq
  -- Step 13: conclusion
  refine ⟨fun t => Real.exp (-∫ s in (0)..t, a₀ s), hi, ?_⟩
  intro s r hs hsr hrR
  obtain ⟨hint, -, -⟩ := hann s r hs hsr hrR
  obtain ⟨h1, h2⟩ := hii s r hs hsr hrR
  exact ⟨hint, le_of_le_of_eq h1 (by ring), le_of_eq_of_le (by ring) h2⟩
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
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff `ζ` with `ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0`
outside `B̆_ρ(ξ)`, `0 ≤ ζ ≤ 1` and `|∇ζ| ≤ 3/ρ`.  Take `ζ(x) = φ(‖x − ξ‖/ρ)` for the `C^∞`,
`3`-Lipschitz step profile `φ` (`1` on `(-∞, 1/2]`, `0` on `[1, ∞)`); `ζ` is `C^∞`, hence `C¹`. -/
theorem aal_l1th_exists_cutoff : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ 1 ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ, hφ01, hφ1, hφ0, hφlip⟩ := exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    (contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ hφ1).of_le (by exact_mod_cast le_top),
    fun x => hφ01 _, fun x hx => hφ1 _ ?_, fun x hx => hφ0 _ ?_, fun x => ?_⟩
  · -- `‖x − ξ‖ ≤ ρ/2` gives `‖x − ξ‖/ρ ≤ 1/2`.
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ ‖x − ξ‖` gives `1 ≤ ‖x − ξ‖/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- `φ` is `3`-Lipschitz, so `‖Dζ(x)‖ ≤ 3/ρ`.
    exact_mod_cast norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφlip x
/-- **Simon Ch. 5, proof of Lemma 2.1** (projection algebra).
(i) The operator norm is at most the Hilbert–Schmidt norm: `‖A‖ ≤ |A|`.
(ii) If `dim P = dim T`, then `trace(p_{Tᗮ} ∘ p_P) = ½ |p_P − p_T|²` (display (2), p. 107:
`Σ_{i>n} e^{ii} = ½ |p_{T_x M} − p_{ℝⁿ}|²`).
Proof: (i) `|A v| ≤ Σ |vᵢ| |A eᵢ| ≤ |v| |A|` by the triangle and Cauchy–Schwarz inequalities.
(ii) With `p = p_P`, `q = p_T` and `trace C = Σ ⟨eᵢ, C eᵢ⟩`, self-adjointness and idempotence
give `|p − q|² = trace p − 2 trace(q p) + trace q`, while `p_{Tᗮ} = 1 − q` gives
`trace(p_{Tᗮ} p) = trace p − trace(q p)`; finally `trace p = dim P = dim T = trace q`. -/
theorem aal_l1th_projection_algebra : (∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A) ∧ ∀ (m : ℕ) (P T : Submodule ℝ (Rn m)), Module.finrank ℝ P = Module.finrank ℝ T → LinearMap.trace ℝ (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2 := by
  refine ⟨fun m k A => ?_, fun m P T hPT => ?_⟩
  · -- (i): `|A v| ≤ Σ |vᵢ| |A eᵢ| ≤ (Σ vᵢ²)^{1/2} (Σ |A eᵢ|²)^{1/2} = |v| |A|`.
    refine ContinuousLinearMap.opNorm_le_bound A (Real.sqrt_nonneg _) fun v => ?_
    have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v]
      simp
    calc ‖A v‖ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by
          conv_lhs => rw [hv]
          simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i • A (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ = ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ := by simp only [norm_smul]
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by
          rw [mul_comm, EuclideanSpace.norm_eq]
          rfl
  · -- (ii): `eᵢ = EuclideanSpace.single i 1`, `p = p_P`, `q = p_T`.
    -- The trace is the sum of the diagonal entries in the orthonormal basis `(eᵢ)`.
    have htr : ∀ f : Rn m →ₗ[ℝ] Rn m, LinearMap.trace ℝ (Rn m) f =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (f (EuclideanSpace.single i 1)) := by
      intro f
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f]
      refine Fintype.sum_congr _ _ fun i => ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        EuclideanSpace.basisFun_apply]
    -- The trace of an orthogonal projection is the dimension of its range.
    have hdim : ∀ W : Submodule ℝ (Rn m), ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (W.starProjection (EuclideanSpace.single i 1)) = Module.finrank ℝ W := by
      intro W
      rw [← LinearMap.IsProj.trace (f := (W.starProjection : Rn m →ₗ[ℝ] Rn m))
        ⟨fun x => W.starProjection_apply_mem x,
          fun x hx => Submodule.starProjection_eq_self_iff.mpr hx⟩, htr]
      rfl
    -- An orthogonal projection is self-adjoint and idempotent: `|p_W x|² = ⟨x, p_W x⟩`.
    have hsq : ∀ (W : Submodule ℝ (Rn m)) (x : Rn m),
        ‖W.starProjection x‖ ^ 2 = inner ℝ x (W.starProjection x) := by
      intro W x
      rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)]
    -- Pointwise identities for the two sides.
    have hL : ∀ x : Rn m, inner ℝ x (Tᗮ.starProjection (P.starProjection x)) =
        inner ℝ x (P.starProjection x) - inner ℝ x (T.starProjection (P.starProjection x)) := by
      intro x
      rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
    have hR : ∀ x : Rn m, ‖(P.starProjection - T.starProjection) x‖ ^ 2 =
        inner ℝ x (P.starProjection x) - 2 * inner ℝ x (T.starProjection (P.starProjection x)) +
          inner ℝ x (T.starProjection x) := by
      intro x
      rw [sub_apply, norm_sub_sq_real, hsq P, hsq T,
        ← Submodule.inner_starProjection_left_eq_right T,
        real_inner_comm x (T.starProjection (P.starProjection x))]
    -- Assemble: both sides equal `dim P − Σ ⟨eᵢ, q (p eᵢ)⟩`.
    rw [htr]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    simp only [hL]
    unfold hsNormSq
    simp only [hR]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hdim P, hdim T, hPT]
    ring
/-- Simon Ch. 5, proof of Lemma 2.1, displays (1)–(3) (p. 107): at a point `x` with tangent plane
`p_{T_x M} = p_P` (`dim P = dim T = n`), the test field `X(y) = ζ(y)² p_{T⊥}(y − z)` has
`div_M X(x) = ζ(x)² |p_P − p_T|²/2 + 2ζ(x) Dζ(x)((p_P − p_T) x')`, where `x' = p_{T⊥}(x − z)`. -/
theorem aal_l1th_test_field_divergence : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ζ : Amb n ℓ → ℝ) (z x : Amb n ℓ) (P T : Submodule ℝ (Amb n ℓ)), DifferentiableAt ℝ ζ x → Module.finrank ℝ P = n → Module.finrank ℝ T = n → V.tangentProj x = P.starProjection → V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z)) x = ζ x ^ 2 * (hsNormSq (V.tangentProj x - T.starProjection) / 2) + 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (Tᗮ.starProjection (x - z))) := by
  intro n ℓ U V ζ z x P T hζ hP hT hV
  -- `DX(x) = ζ(x)² p_{T⊥} + (2ζ(x) Dζ(x)).smulRight x'` by the product and chain rules.
  have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - z)) Tᗮ.starProjection x :=
    (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have hX : HasFDerivAt (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z))
      (ζ x ^ 2 • Tᗮ.starProjection +
        ((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - z))) x :=
    hsq.fun_smul hlin
  -- `(λ.smulRight x') ∘ p_P = (λ ∘ p_P).smulRight x'`, a rank-one map with trace `λ(p_P x')`.
  have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - z))).toLinearMap ∘ₗ
      P.starProjection.toLinearMap =
        (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
          (Tᗮ.starProjection (x - z)) :=
    LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
  -- `x' ∈ T⊥`, so `p_T x' = 0` and `p_P x' = (p_P − p_T) x'`.
  have hx' : T.starProjection (Tᗮ.starProjection (x - z)) = 0 :=
    T.starProjection_apply_eq_zero_iff.mpr (Tᗮ.starProjection_apply_mem _)
  -- `trace(p_{T⊥} ∘ p_P) = |p_P − p_T|²/2` as `dim P = dim T` (sibling `projection_algebra`).
  have htr : LinearMap.trace ℝ (Amb n ℓ)
      (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        hsNormSq (P.starProjection - T.starProjection) / 2 :=
    Submission.aal_l1th_projection_algebra.2 (n + ℓ) P T (hP.trans hT.symm)
  -- Linearity of the trace, then substitute the three identities above.
  rw [RectifiableVarifold.divM, hX.fderiv, hV, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
    map_smul, htr, LinearMap.trace_smulRight]
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, smul_apply,
    smul_eq_mul, sub_apply, hx', sub_zero]
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
/-- **Simon Ch. 2, Theorem 1.5 (C¹ approximation of Lipschitz functions).**  A Lipschitz
`f : ℝⁿ → ℝ` agrees with a `C¹` function outside a set of arbitrarily small Lebesgue measure.
Proof, following Simon's printed argument: by Rademacher `f` is differentiable off a Borel null
set; the Whitney quotients `σₖ(x) = sup {|f(x+v) - f(x) - Df(x) v| / |v| : 0 < |v| < 1/(k+1)}`
are lower semicontinuous in `(x, Df(x))`, hence Borel, and tend to `0` wherever `f` is
differentiable; Egorov's theorem on the balls `B(0, J)` with summable tolerances, together with
outer regularity, gives a closed `A` of small complement on whose compact subsets the
first-order Taylor remainder is uniformly small (this also makes `Df` continuous on `A`, so no
separate Lusin step is needed); Whitney's extension theorem (Simon Ch. 2, 1.6), proved inline
with Vitali-selected Whitney balls and a scaled-bump partition of unity, yields `g ∈ C¹` with
`g = f` on `A`. -/
theorem aetp_lipschitz_c1_approximation : ∀ (n : ℕ), 1 ≤ n → ∀ (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x} < ε := by
  intro n _
  -- Whitney's C¹ extension theorem (Simon Ch. 2, Theorem 1.6), in the local uniform form.
  have whitney : ∀ (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A →
      (∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ e) ∧
        ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ → |h c - h b - D b (c - b)| ≤ e * ‖c - b‖) →
      ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ x ∈ A, g x = h x := by
    intro A h D hA hW
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, contDiff_const, fun x hx => hx.elim⟩
    classical
    -- Whitney radius `r x = min 1 (dist (x, A)) / 100`.
    obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 := ⟨_, fun _ => rfl⟩
    have hr0 : ∀ x, 0 ≤ r x := fun x => by
      rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
    have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
      rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
    have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
      rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).1 hx)) (by norm_num)
    have hcomp : ∀ x c, dist x c ≤ r x + 10 * r c →
        r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
      have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := by
        intro x y
        have h1 := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
        simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h1
        rw [hr, hr]
        linarith [(abs_sub_le_iff.1 h1).1]
      intro x c hxc
      have h1 := hrlip x c
      have h2 := hrlip c x
      rw [dist_comm c x] at h2
      have h3 := hr0 x
      have h4 := hr0 c
      exact ⟨by linarith, by linarith, by linarith⟩
    -- Vitali: disjoint balls `B(c, r c)` whose fourfold enlargements cover `Aᶜ`.
    obtain ⟨Cs, hCsA, hCsdisj, hCscov⟩ : ∃ Cs : Set (Rn n), Cs ⊆ Aᶜ ∧
        Cs.PairwiseDisjoint (fun c => ball c (r c)) ∧ ∀ x ∉ A, ∃ c ∈ Cs, dist x c < 4 * r c := by
      have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
        rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball Aᶜ
        (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
      refine ⟨s, hs, hd, fun x hx => ?_⟩
      obtain ⟨c, hcs, hxc⟩ := hc x hx
      exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
    have hsep : ∀ c ∈ Cs, ∀ c' ∈ Cs, c ≠ c' → r c ≤ dist c c' := by
      intro c hc c' hc' hcc
      by_contra hlt
      exact Set.disjoint_left.1 (hCsdisj hc hc' hcc) (show c' ∈ ball c (r c) by
        rw [mem_ball, dist_comm]; exact not_le.1 hlt) (mem_ball_self (hrpos c' (hCsA hc')))
    -- A uniform packing bound for `1/2`-separated subsets of `B(0, 21)`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Rn n), s ⊆ closedBall 0 21 →
        s.Pairwise (fun y z => 1 / 2 ≤ dist y z) → s.Finite ∧ s.ncard ≤ N := by
      obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1
        (isCompact_closedBall (0 : Rn n) 21).totallyBounded (1 / 4) (by norm_num)
      refine ⟨t.ncard, fun s hs hs2 => ?_⟩
      have hc : ∀ x : s, ∃ y : t, dist (x : Rn n) y < 1 / 4 := by
        intro x
        obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (hcover (hs x.2))
        exact ⟨⟨y, hyt⟩, hxy⟩
      choose c hc using hc
      have hi : Function.Injective c := by
        intro x y hxy
        by_contra hne
        have hd := hs2 x.2 y.2 (fun h' => hne (Subtype.ext h'))
        have htri := dist_triangle (x : Rn n) (c x) y
        have hxc := hc x
        have hyc := hc y
        rw [← hxy, dist_comm (y : Rn n)] at hyc
        linarith
      have : Finite t := ht.to_subtype
      have : Finite s := Finite.of_injective c hi
      exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
    -- The finite sets `F x` of centres near `x ∉ A`.
    obtain ⟨F, hF⟩ : ∃ F : Rn n → Finset (Rn n), ∀ x, x ∉ A →
        (∀ c, c ∈ F x ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ (F x).card ≤ N := by
      have key : ∀ x, x ∉ A → ∃ s : Finset (Rn n),
          (∀ c, c ∈ s ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
        intro x hx
        have hrx := hrpos x hx
        set T : Set (Rn n) := {c | c ∈ Cs ∧ dist x c ≤ r x + 10 * r c} with hT
        obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n, ∀ c, φ c = (r x)⁻¹ • (c - x) := ⟨_, fun _ => rfl⟩
        have hφi : Function.Injective φ := by
          intro c d hcd
          rw [hφ, hφ] at hcd
          have := congrArg (fun z => r x • z) hcd
          simpa [smul_smul, hrx.ne'] using this
        have hnφ : ∀ c d, dist (φ c) (φ d) = dist c d / r x := by
          intro c d
          rw [hφ, hφ, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hrx.le), ← dist_eq_norm, inv_mul_eq_div]
        have hsub : φ '' T ⊆ closedBall 0 21 := by
          rintro _ ⟨c, hc, rfl⟩
          have h0 : φ x = 0 := by rw [hφ, sub_self, smul_zero]
          rw [mem_closedBall, ← h0, hnφ, div_le_iff₀ hrx, dist_comm]
          exact (hcomp x c hc.2).2.2
        have hsep' : (φ '' T).Pairwise (fun y z => 1 / 2 ≤ dist y z) := by
          rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
          have h1 := hsep c hc.1 d hd.1 (fun h' => hcd (congrArg φ h'))
          have h2 := (hcomp x c hc.2).1
          rw [hnφ, le_div_iff₀ hrx]
          linarith
        obtain ⟨hfin, hcard⟩ := hN (φ '' T) hsub hsep'
        have hTfin : T.Finite := hfin.of_finite_image hφi.injOn
        refine ⟨hTfin.toFinset, fun c => hTfin.mem_toFinset, ?_⟩
        rw [← Set.ncard_eq_toFinset_card T hTfin, ← Set.ncard_image_of_injective T hφi]
        exact hcard
      choose! F hF using key
      exact ⟨F, hF⟩
    -- A fixed bump `β`, equal to `1` on `B(0, 4)` and to `0` off `B(0, 8)`.
    obtain ⟨β, hβ0, hβ1, hβone, hβzero, hβs, L, hL⟩ : ∃ β : Rn n → ℝ, (∀ y, 0 ≤ β y) ∧
        (∀ y, β y ≤ 1) ∧ (∀ y, ‖y‖ ≤ 4 → β y = 1) ∧ (∀ y, 8 ≤ ‖y‖ → β y = 0) ∧
        ContDiff ℝ 1 β ∧ ∃ L : ℝ≥0, LipschitzWith L β := by
      let b : ContDiffBump (0 : Rn n) := ⟨4, 8, by norm_num, by norm_num⟩
      refine ⟨b, fun y => b.nonneg, fun y => b.le_one, fun y hy => b.one_of_mem_closedBall ?_,
        fun y hy => Function.notMem_support.1 ?_, b.contDiff (n := 1),
        ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (b.contDiff (n := 1))
          one_ne_zero⟩
      · rw [mem_closedBall, dist_zero_right]; exact hy
      · rw [b.support_eq, mem_ball, dist_zero_right]; exact not_lt.2 hy
    -- The rescaled bumps `ψ c y = β ((y - c) / r c)`.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Rn n → Rn n → ℝ, ∀ c y, ψ c y = β ((r c)⁻¹ • (y - c)) :=
      ⟨_, fun _ _ => rfl⟩
    have hnsc : ∀ c y, 0 < r c → ‖(r c)⁻¹ • (y - c)‖ = dist y c / r c := by
      intro c y hc
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, inv_mul_eq_div]
    have hψ0 : ∀ c y, 0 ≤ ψ c y := fun c y => by rw [hψ]; exact hβ0 _
    have hψone : ∀ c y, 0 < r c → dist y c ≤ 4 * r c → ψ c y = 1 := by
      intro c y hc hy; rw [hψ]; apply hβone; rw [hnsc c y hc, div_le_iff₀ hc]; exact hy
    have hψzero : ∀ c y, 0 < r c → 8 * r c ≤ dist y c → ψ c y = 0 := by
      intro c y hc hy; rw [hψ]; apply hβzero; rw [hnsc c y hc, le_div_iff₀ hc]; exact hy
    have hψs : ∀ c, ContDiff ℝ 1 (ψ c) := by
      intro c
      rw [show ψ c = fun y => β ((r c)⁻¹ • (y - c)) from funext (hψ c)]
      exact hβs.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hψd : ∀ c y, 0 < r c → ‖fderiv ℝ (ψ c) y‖ ≤ L / r c := by
      intro c y hc
      have hlip : LipschitzWith (L * (Real.toNNReal (r c))⁻¹) (ψ c) := by
        refine LipschitzWith.of_dist_le_mul fun y z => ?_
        rw [hψ, hψ, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le]
        refine (hL.dist_le_mul _ _).trans (le_of_eq ?_)
        rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, mul_assoc]
      have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
      rwa [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le, ← div_eq_mul_inv] at this
    -- The locally finite sum `S = ∑ c ∈ Cs, ψ c ≥ 1` on `Aᶜ`.
    obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ y, S y = ∑ᶠ c ∈ Cs, ψ c y := ⟨_, fun _ => rfl⟩
    have hψF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → ψ c y = 0 := by
      intro x hx y hy c hc hcF
      apply hψzero c y (hrpos c (hCsA hc))
      have h1 : ¬ dist x c ≤ r x + 10 * r c := fun h' => hcF (((hF x hx).1 c).2 ⟨hc, h'⟩)
      have h2 := dist_triangle x y c
      rw [dist_comm x y] at h2
      have h3 := hr0 c
      linarith
    have hSloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → S y = ∑ c ∈ F x, ψ c y := by
      intro x hx y hy
      rw [hS]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      exact ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 (hψF x hx y hy c hc.1 h'), hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
    have hS1 : ∀ x, x ∉ A → 1 ≤ S x := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hCscov x hx
      have hcF : c ∈ F x := ((hF x hx).1 c).2 ⟨hc, by linarith [hr0 x, hr0 c]⟩
      rw [hSloc x hx x (by rw [dist_self]; exact hrpos x hx)]
      calc (1 : ℝ) = ψ c x := (hψone c x (hrpos c (hCsA hc)) hxc.le).symm
        _ ≤ ∑ c ∈ F x, ψ c x := Finset.single_le_sum (fun c _ => hψ0 c x) hcF
    have hSc : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := by
      intro x hx
      refine (ContDiff.contDiffAt (ContDiff.sum (s := F x) fun c _ => hψs c)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hSloc x hx y hy
    have hnotA : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
      intro x hx y hy hyA
      have h1 := infDist_le_dist_of_mem (x := x) hyA
      rw [dist_comm] at h1
      linarith [hrd x, hr0 x]
    -- The partition of unity `φ c = ψ c / S` on `Aᶜ`.
    obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n → ℝ, ∀ c y, φ c y = ψ c y / S y := ⟨_, fun _ _ => rfl⟩
    have hφcd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (φ c) x := by
      intro c x hx
      rw [show φ c = ψ c / S from funext (hφ c)]
      exact (hψs c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
    have hφ0 : ∀ c y, y ∉ A → 0 ≤ φ c y := fun c y hy => by
      rw [hφ]; exact div_nonneg (hψ0 c y) (le_trans zero_le_one (hS1 y hy))
    have hφsum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ F x, φ c y = 1 := by
      intro x hx y hy
      simp only [hφ]
      rw [← Finset.sum_div, ← hSloc x hx y hy]
      exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hnotA x hx y hy))))
    have hφF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → φ c y = 0 := by
      intro x hx y hy c hc hcF
      rw [hφ, hψF x hx y hy c hc hcF, zero_div]
    have hφdsum : ∀ x, x ∉ A → ∑ c ∈ F x, fderiv ℝ (φ c) x = 0 := by
      intro x hx
      have heq : (fun y => ∑ c ∈ F x, φ c y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
        exact hφsum x hx y hy
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      rwa [fderiv_fun_const, Pi.zero_apply, fderiv_fun_sum fun c _ =>
        (hφcd c x hx).differentiableAt one_ne_zero] at h1
    -- `‖Dφ_c‖ ≤ ‖Dψ_c‖ + ‖DS‖` off `A` (quotient rule, `S ≥ 1`, `0 ≤ ψ_c ≤ 1`).
    have hφd : ∀ c x, x ∉ A → ‖fderiv ℝ (φ c) x‖ ≤ ‖fderiv ℝ (ψ c) x‖ + ‖fderiv ℝ S x‖ := by
      intro c x hx
      have hS1x := hS1 x hx
      have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
      have hb := ((hψs c).differentiable one_ne_zero x).hasFDerivAt
      have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
      have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
      have hder : fderiv ℝ (φ c) x =
          ψ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (ψ c) x := by
        rw [show φ c = fun y => ψ c y * ((fun t : ℝ => t⁻¹) ∘ S) y from
          funext fun y => by rw [hφ, div_eq_mul_inv]; rfl]
        exact (hb.fun_mul hi).fderiv
      have hp0 := hψ0 c x
      have hp1 : ψ c x ≤ 1 := by rw [hψ]; exact hβ1 _
      have hsi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
      have hsi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
      rw [hder]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg hp0,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), add_comm]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hsi)
        (mul_le_of_le_one_left (by positivity) hp1 |>.trans (mul_le_of_le_one_left (norm_nonneg _) hsi2))
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
        ∀ x, x ∉ A → ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ M / r x := by
      refine ⟨(N + 1) * (N * (2 * L)), by positivity, fun x hx => ?_⟩
      have hrx := hrpos x hx
      have hb : ∀ c ∈ F x, ‖fderiv ℝ (ψ c) x‖ ≤ 2 * L / r x := by
        intro c hc
        have hc' := ((hF x hx).1 c).1 hc
        have hrc := hrpos c (hCsA hc'.1)
        refine (hψd c x hrc).trans ?_
        rw [div_le_div_iff₀ hrc hrx]
        calc (L : ℝ) * r x ≤ L * (2 * r c) :=
              mul_le_mul_of_nonneg_left (by linarith [(hcomp x c hc'.2).1]) L.2
          _ = 2 * L * r c := by ring
      have hN' : ((F x).card : ℝ) ≤ N := by exact_mod_cast (hF x hx).2
      have hb0 : (0 : ℝ) ≤ 2 * L / r x := div_nonneg (by positivity) hrx.le
      have hSd : ‖fderiv ℝ S x‖ ≤ N * (2 * L / r x) := by
        have heq : S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, ψ c y := by
          filter_upwards [ball_mem_nhds x hrx] with y hy
          exact hSloc x hx y hy
        rw [heq.fderiv_eq, fderiv_fun_sum fun c _ => (hψs c).differentiable one_ne_zero x]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hN' hb0
      calc ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, (2 * L / r x + N * (2 * L / r x)) :=
            Finset.sum_le_sum fun c hc => (hφd c x hx).trans (add_le_add (hb c hc) hSd)
        _ = (F x).card * ((N + 1) * (2 * L / r x)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ N * ((N + 1) * (2 * L / r x)) := mul_le_mul_of_nonneg_right hN' (by positivity)
        _ = (N + 1) * (N * (2 * L)) / r x := by ring
    -- Nearest-point anchors and the affine jets `Q a y = h a + D a (y - a)`.
    obtain ⟨anc, hancA, hancd⟩ : ∃ anc : Rn n → Rn n, (∀ x, anc x ∈ A) ∧
        ∀ x, dist x (anc x) = infDist x A := by
      choose anc hanc using fun x => hA.exists_infDist_eq_dist hne x
      exact ⟨anc, fun x => (hanc x).1, fun x => (hanc x).2.symm⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Rn n → Rn n → ℝ, ∀ a y, Q a y = h a + (D a y - D a a) :=
      ⟨_, fun _ _ => rfl⟩
    have hQs : ∀ a, ContDiff ℝ 1 (Q a) := by
      intro a
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact contDiff_const.add ((D a).contDiff.sub contDiff_const)
    have hQd : ∀ a y, HasFDerivAt (Q a) (D a) y := by
      intro a y
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact ((D a).hasFDerivAt.sub_const _).const_add _
    have hQsub : ∀ a b y,
        |Q b y - Q a y| ≤ |h b - h a - D a (b - a)| + ‖D b - D a‖ * ‖y - b‖ := by
      intro a b y
      have e1 : Q b y - Q a y = (h b - h a - D a (b - a)) + (D b - D a) (y - b) := by
        rw [hQ, hQ]; simp only [map_sub, sub_apply]; ring
      rw [e1]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      have := (D b - D a).le_opNorm (y - b)
      rwa [Real.norm_eq_abs] at this
    have hancF : ∀ x, x ∉ A → ∀ c ∈ F x, dist x (anc c) ≤ 2 * infDist x A := by
      intro x hx c hc
      have h1 := (hcomp x c (((hF x hx).1 c).1 hc).2).2.2
      have h2 := hrd x
      have h3 := infDist_le_infDist_add_dist (s := A) (x := c) (y := x)
      have h4 := dist_triangle x c (anc c)
      rw [hancd c] at h4
      rw [dist_comm c x] at h3
      linarith [hr0 x]
    have hancP : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ F x, dist (anc c) a ≤ 3 * dist x a := by
      intro x hx a ha c hc
      have h1 := hancF x hx c hc
      have h2 := infDist_le_dist_of_mem (x := x) ha
      have h3 := dist_triangle (anc c) x a
      rw [dist_comm (anc c) x] at h3
      linarith
    -- The Whitney extension `g`.
    obtain ⟨g, hg⟩ : ∃ g : Rn n → ℝ, ∀ y,
        g y = if y ∈ A then h y else ∑ᶠ c ∈ Cs, φ c y * Q (anc c) y := ⟨_, fun _ => rfl⟩
    have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
    have hgloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx y hy
      rw [hg, ite_eq_right (hnotA x hx y hy)]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      refine ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 ?_, hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
      rw [hφF x hx y hy c hc.1 h', zero_mul]
    have hgev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hgloc x hx y hy
    have hgd : ∀ x, x ∉ A → HasFDerivAt g
        (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) x := by
      intro x hx
      refine HasFDerivAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact HasFDerivAt.fun_sum fun c _ =>
        ((hφcd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hQd (anc c) x)
    have hgcd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
      intro x hx
      refine ContDiffAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact ContDiffAt.sum fun c _ => (hφcd c x hx).mul (hQs (anc c)).contDiffAt
    -- `g` has derivative `D a` at each `a ∈ A`.
    have hgdA : ∀ a ∈ A, HasFDerivAt g (D a) a := by
      intro a ha
      refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun e he => ?_)
      obtain ⟨δ, hδ, -, hDd, hrem⟩ := hW a ha (e / 5) (by positivity)
      have haa : dist a a < δ := by rw [dist_self]; exact hδ
      filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
      have hxa : dist x a < δ / 4 := hx
      rw [hgA a ha]
      by_cases hxA : x ∈ A
      · rw [hgA x hxA, Real.norm_eq_abs]
        exact (hrem a ha haa x hxA (by linarith)).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      · have hx0 : dist x x < r x := by rw [dist_self]; exact hrpos x hxA
        have e1 : g x - h a - D a (x - a) = ∑ c ∈ F x, φ c x * (Q (anc c) x - Q a x) := by
          rw [hgloc x hxA x hx0]
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hφsum x hxA x hx0, one_mul, hQ a x,
            map_sub]
          ring
        rw [e1, Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ c ∈ F x, |φ c x * (Q (anc c) x - Q a x)| ≤ ∑ c ∈ F x, φ c x * (e * ‖x - a‖) := by
              refine Finset.sum_le_sum fun c hc => ?_
              rw [abs_mul, abs_of_nonneg (hφ0 c x hxA)]
              refine mul_le_mul_of_nonneg_left ?_ (hφ0 c x hxA)
              have hba := hancP x hxA a ha c hc
              have hxb : dist x (anc c) ≤ 2 * dist x a :=
                (hancF x hxA c hc).trans (by linarith [infDist_le_dist_of_mem (x := x) ha])
              have hbaδ : dist (anc c) a < δ := by linarith
              have h1 := hrem a ha haa (anc c) (hancA c) hbaδ
              have h2 := hDd (anc c) (hancA c) hbaδ
              rw [dist_eq_norm] at hba hxb
              refine (hQsub a (anc c) x).trans ?_
              calc |h (anc c) - h a - D a (anc c - a)| + ‖D (anc c) - D a‖ * ‖x - anc c‖
                  ≤ e / 5 * ‖anc c - a‖ + e / 5 * ‖x - anc c‖ :=
                    add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                _ ≤ e / 5 * (3 * ‖x - a‖) + e / 5 * (2 * ‖x - a‖) :=
                    add_le_add (mul_le_mul_of_nonneg_left hba (by positivity))
                      (mul_le_mul_of_nonneg_left hxb (by positivity))
                _ = e * ‖x - a‖ := by ring
          _ = e * ‖x - a‖ := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
    -- `Dg` is continuous at each `a ∈ A`.
    have hgcA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
      intro a ha
      rw [Metric.continuousAt_iff]
      intro e he
      obtain ⟨δ, hδ, hδ1, hDd, hrem⟩ := hW a ha (e / (2 * (1 + 700 * M))) (by positivity)
      set η := e / (2 * (1 + 700 * M)) with hη
      have hη0 : 0 < η := by positivity
      have hηM : η * (1 + 700 * M) = e / 2 := by rw [hη]; field_simp
      have hηM' := mul_nonneg hη0.le hM0
      refine ⟨δ / 4, by positivity, fun x hxa => ?_⟩
      rw [(hgdA a ha).fderiv, dist_eq_norm]
      by_cases hxA : x ∈ A
      · rw [(hgdA x hxA).fderiv]
        exact (hDd x hxA (by linarith)).trans_lt (by linarith)
      · have hrx := hrpos x hxA
        have hx0 : dist x x < r x := by rw [dist_self]; exact hrx
        have hbA : anc x ∈ A := hancA x
        have hdxa : infDist x A ≤ dist x a := infDist_le_dist_of_mem ha
        have hba : dist (anc x) a < δ := by
          have := dist_triangle (anc x) x a
          rw [dist_comm (anc x) x, hancd x] at this
          linarith
        have hd1 : infDist x A = 100 * r x := by
          rw [hr, min_eq_right (by linarith : infDist x A ≤ 1)]
          ring
        have hDb := hDd (anc x) hbA hba
        have e1 : (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) - D a =
            (∑ c ∈ F x, φ c x • (D (anc c) - D a)) +
              ∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x := by
          simp_rw [smul_sub, sub_smul]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_smul, ← Finset.smul_sum, hφsum x hxA x hx0, hφdsum x hxA, one_smul,
            smul_zero, sub_zero]
          abel
        rw [(hgd x hxA).fderiv, e1]
        have hT1 : ‖∑ c ∈ F x, φ c x • (D (anc c) - D a)‖ ≤ η := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖φ c x • (D (anc c) - D a)‖ ≤ ∑ c ∈ F x, φ c x * η :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_of_nonneg (hφ0 c x hxA)]
                  exact mul_le_mul_of_nonneg_left
                    (hDd (anc c) (hancA c) (by linarith [hancP x hxA a ha c hc])) (hφ0 c x hxA)
            _ = η := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
        have hT2 : ‖∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖ ≤
            700 * η * r x * (M / r x) := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖(Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖
              ≤ ∑ c ∈ F x, 700 * η * r x * ‖fderiv ℝ (φ c) x‖ :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_eq_abs]
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                  have hcaδ : dist (anc c) a < δ := by linarith [hancP x hxA a ha c hc]
                  have hxc := hancF x hxA c hc
                  have hcb : dist (anc c) (anc x) ≤ 3 * infDist x A := by
                    have := dist_triangle (anc c) x (anc x)
                    rw [dist_comm (anc c) x, hancd x] at this
                    linarith
                  have h1 := hrem (anc x) hbA hba (anc c) (hancA c) hcaδ
                  have h2 : ‖D (anc c) - D (anc x)‖ ≤ 2 * η := by
                    rw [← sub_sub_sub_cancel_right (D (anc c)) (D (anc x)) (D a)]
                    exact (norm_sub_le _ _).trans (by linarith [hDd (anc c) (hancA c) hcaδ])
                  rw [dist_eq_norm] at hcb hxc
                  refine (hQsub (anc x) (anc c) x).trans ?_
                  calc |h (anc c) - h (anc x) - D (anc x) (anc c - anc x)| +
                        ‖D (anc c) - D (anc x)‖ * ‖x - anc c‖
                      ≤ η * ‖anc c - anc x‖ + 2 * η * ‖x - anc c‖ :=
                        add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                    _ ≤ η * (3 * infDist x A) + 2 * η * (2 * infDist x A) :=
                        add_le_add (mul_le_mul_of_nonneg_left hcb hη0.le)
                          (mul_le_mul_of_nonneg_left hxc (by positivity))
                    _ = 700 * η * r x := by rw [hd1]; ring
            _ = 700 * η * r x * ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := by rw [Finset.mul_sum]
            _ ≤ 700 * η * r x * (M / r x) :=
                mul_le_mul_of_nonneg_left (hM x hxA) (mul_nonneg (by positivity) hrx.le)
        have hfin : 700 * η * r x * (M / r x) = 700 * (η * M) := by field_simp
        rw [hfin] at hT2
        exact (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨g, contDiff_one_iff_fderiv.2 ⟨fun x => ?_, continuous_iff_continuousAt.2 fun x => ?_⟩,
      hgA⟩
    · by_cases hx : x ∈ A
      · exact (hgdA x hx).differentiableAt
      · exact (hgd x hx).differentiableAt
    · by_cases hx : x ∈ A
      · exact hgcA x hx
      · exact (hgcd x hx).continuousAt_fderiv one_ne_zero
  intro f K hf ε hε
  have hfc : Continuous f := hf.continuous
  -- Rademacher: `f` is differentiable off a Borel null set.
  have hBm : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hB0 : volume {x | DifferentiableAt ℝ f x}ᶜ = 0 := by
    have h1 := hf.ae_differentiableAt (μ := (volume : Measure (Rn n)))
    rwa [ae_iff, ← Set.compl_ofPred] at h1
  -- Whitney quotients `σ k (x, L) = sup {|f (x + v) - f x - L v| / |v| : 0 < |v| < 1/(k+1)}`.
  obtain ⟨σ, hσ0, hσle, hσge, hσlsc⟩ : ∃ σ : ℕ → Rn n × (Rn n →L[ℝ] ℝ) → ℝ,
      (∀ k p, 0 ≤ σ k p) ∧
      (∀ (k : ℕ) p (v : Rn n), 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ σ k p * ‖v‖) ∧
      (∀ (k : ℕ) p (t : ℝ), 0 ≤ t → (∀ v : Rn n, 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ t * ‖v‖) → σ k p ≤ t) ∧
      ∀ k, LowerSemicontinuous (σ k) := by
    have hbdd : ∀ (k : ℕ) (p : Rn n × (Rn n →L[ℝ] ℝ)), BddAbove (range fun v :
        {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
          |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) := by
      intro k p
      refine ⟨K + ‖p.2‖, ?_⟩
      rintro _ ⟨v, rfl⟩
      rw [div_le_iff₀ v.2.1]
      have h1 := hf.dist_le_mul (p.1 + v) p.1
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1
      have h2 := p.2.le_opNorm v
      rw [Real.norm_eq_abs] at h2
      calc |f (p.1 + v) - f p.1 - p.2 v| ≤ |f (p.1 + v) - f p.1| + |p.2 v| := abs_sub _ _
        _ ≤ K * ‖(v : Rn n)‖ + ‖p.2‖ * ‖(v : Rn n)‖ := add_le_add h1 h2
        _ = (K + ‖p.2‖) * ‖(v : Rn n)‖ := by ring
    refine ⟨fun k p => ⨆ v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)},
      |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖, fun k p => Real.iSup_nonneg fun v =>
        div_nonneg (abs_nonneg _) (norm_nonneg _), fun k p v hv0 hv1 => ?_,
      fun k p t ht hle => Real.iSup_le (fun v => ?_) ht, fun k => ?_⟩
    · rw [← div_le_iff₀ hv0]
      exact le_ciSup (f := fun v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
        |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) (hbdd k p) ⟨v, hv0, hv1⟩
    · rw [div_le_iff₀ v.2.1]
      exact hle v v.2.1 v.2.2
    · refine lowerSemicontinuous_ciSup (hbdd k) fun v => Continuous.lowerSemicontinuous ?_
      exact (((hfc.comp (continuous_fst.add continuous_const)).sub (hfc.comp continuous_fst)).sub
        (continuous_snd.clm_apply continuous_const)).abs.div_const _
  have hσm : ∀ k, Measurable fun x => σ k (x, fderiv ℝ f x) := fun k =>
    (hσlsc k).measurable.comp (measurable_id.prodMk (measurable_fderiv ℝ f))
  have hσlim : ∀ x, DifferentiableAt ℝ f x →
      Tendsto (fun k => σ k (x, fderiv ℝ f x)) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro t ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 hx.hasFDerivAt.isLittleO (half_pos ht))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hρ
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ0 k _)]
    refine lt_of_le_of_lt (hσge k _ (t / 2) (by positivity) fun v hv0 hv1 => ?_) (half_lt_self ht)
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h1 := @hball (x + v) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rwa [add_sub_cancel_left, Real.norm_eq_abs] at h1
  -- Egorov on the balls `B(0, J)`, with summable tolerances.
  obtain ⟨δs, hδs0, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have hEg : ∀ J : ℕ, ∃ t ⊆ ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}, MeasurableSet t ∧
      volume t ≤ δs J ∧ TendstoUniformlyOn (fun k x => σ k (x, fderiv ℝ f x)) (fun _ => (0 : ℝ))
        atTop ((ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t) := fun J =>
    tendstoUniformlyOn_of_ae_tendsto (fun k => (hσm k).stronglyMeasurable) stronglyMeasurable_const
      (measurableSet_ball.inter hBm) ((measure_mono inter_subset_left).trans_lt
        measure_ball_lt_top).ne (Filter.Eventually.of_forall fun x hx => hσlim x hx.2)
      (by exact_mod_cast hδs0 J)
  choose t htsub _ htle htu using hEg
  -- An open `U` of measure `< ε` containing the bad set; `A = Uᶜ`.
  have hZ : volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J) < ε := by
    calc volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J)
        ≤ volume {x | DifferentiableAt ℝ f x}ᶜ + volume (⋃ J, t J) := measure_union_le _ _
      _ ≤ 0 + ∑' J, (δs J : ℝ≥0∞) :=
          add_le_add hB0.le ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum htle))
      _ < ε := by rw [zero_add]; exact hδsum
  obtain ⟨U, hZU, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ hZ
  -- Uniform first-order Taylor estimate on compact subsets of `Uᶜ`.
  have hunif : ∀ Q ⊆ Uᶜ, IsCompact Q → ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Q, ∀ v : Rn n, ‖v‖ < ρ → |f (x + v) - f x - fderiv ℝ f x v| ≤ s * ‖v‖ := by
    intro Q hQU hQ s hs
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball (0 : Rn n)
    obtain ⟨J, hJ⟩ := exists_nat_gt R
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 (htu J) s hs).exists
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hxU : x ∉ U := hQU hx
    have hxJ : x ∈ (ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t J :=
      ⟨⟨ball_subset_ball hJ.le (hR hx), Classical.byContradiction fun h' =>
        hxU (hZU (Or.inl h'))⟩, fun h' => hxU (hZU (Or.inr (mem_iUnion.2 ⟨J, h'⟩)))⟩
    have h1 := hk x hxJ
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hσ0 _ _)] at h1
    exact (hσle k (x, fderiv ℝ f x) v (norm_pos_iff.2 hv0) hv).trans
      (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  -- Whitney's hypothesis on `Uᶜ`, including continuity of `Df` there.
  have hW2 : ∀ a ∈ Uᶜ, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ Uᶜ, dist b a < δ → ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ e) ∧
      ∀ b ∈ Uᶜ, dist b a < δ → ∀ c ∈ Uᶜ, dist c a < δ →
        |f c - f b - fderiv ℝ f b (c - b)| ≤ e * ‖c - b‖ := by
    intro a ha e he
    obtain ⟨ρ, hρ, hρU⟩ := hunif (Uᶜ ∩ closedBall a 1) inter_subset_left
      ((isCompact_closedBall a 1).inter_left hUo.isClosed_compl) (e / 4) (by positivity)
    have hK : (0 : ℝ) ≤ K := K.2
    set δ := min (min 1 (ρ / 2)) (e * ρ / (8 * K + 1)) with hδ
    have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hδρ : δ ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hδe : δ ≤ e * ρ / (8 * K + 1) := min_le_right _ _
    have haQ : a ∈ Uᶜ ∩ closedBall a 1 := ⟨ha, mem_closedBall_self zero_le_one⟩
    refine ⟨δ, lt_min (lt_min one_pos (half_pos hρ)) (by positivity), hδ1, fun b hb hba => ?_,
      fun b hb hba c hc hca => ?_⟩
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hd : dist b a * (8 * K + 1) ≤ e * ρ := by
        rw [← le_div_iff₀ (by positivity)]; linarith
      refine ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hρ he.le
        (by norm_num) fun w hw1 hw2 => ?_
      rw [Real.norm_two] at hw1
      have h1 := hρU b hbQ w hw2
      have h2 := hρU a haQ w hw2
      have h3 := hf.dist_le_mul (b + w) (a + w)
      have h4 := hf.dist_le_mul b a
      rw [Real.dist_eq, dist_add_right] at h3
      rw [Real.dist_eq] at h4
      have h5 : e * ρ ≤ e * (2 * ‖w‖) := mul_le_mul_of_nonneg_left (by linarith) he.le
      have h6 : 0 ≤ dist b a := dist_nonneg
      rw [sub_apply, Real.norm_eq_abs]
      have e1 : fderiv ℝ f b w - fderiv ℝ f a w = (f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w) + (f (a + w) - f a - fderiv ℝ f a w) := by ring
      rw [e1]
      have := abs_add_le ((f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w)) (f (a + w) - f a - fderiv ℝ f a w)
      have := abs_sub ((f (b + w) - f (a + w)) - (f b - f a)) (f (b + w) - f b - fderiv ℝ f b w)
      have := abs_sub (f (b + w) - f (a + w)) (f b - f a)
      linarith
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hcb : ‖c - b‖ < ρ := by
        have := dist_triangle c a b
        rw [dist_comm a b, dist_eq_norm] at this
        linarith
      have h1 := hρU b hbQ (c - b) hcb
      rw [add_sub_cancel] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨g, hg, hgA⟩ := whitney Uᶜ f (fderiv ℝ f) hUo.isClosed_compl hW2
  refine ⟨g, hg, (measure_mono fun x hx => ?_).trans_lt hUε⟩
  by_contra hxU
  exact hx (hgA x hxU).symm

/-- **Countably rectifiable sets are covered by `C¹` pieces with injective differential** (Simon
Ch. 3, proof of Lemma 1.2, "only if").  If `M ⊆ ℝ^{n+ℓ}` is countably `n`-rectifiable, then up to a
Borel `Hⁿ`-null set `Z₀` it is covered by countably many images `G_k(B̆_{r_k}(c_k))` of open balls
under `C¹` maps `G_k : ℝⁿ → ℝ^{n+ℓ}` whose differential is injective on the ball and which satisfy
the lower Lipschitz bound `σ_k |b₁ - b₂| ≤ |G_k b₁ - G_k b₂|` there.
Proof: approximate the coordinates of the Lipschitz maps `F_j` of Definition 1.1 by `C¹` functions
(Simon Ch. 2, Theorem 1.5, `aetp_lipschitz_c1_approximation`); the set where `F_j` differs from all
approximations is Lebesgue-null, so its image is `Hⁿ`-null.  The image of the critical set of a `C¹`
map `G : ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null: on a piece where `G` is `η`-close to a non-injective linear `A`
with kernel vector `u`, `G` factors through the linear map `Θ = id - (1 - η) u ⊗ u` (which has
determinant `η`) via an `(‖A‖ + 1)`-Lipschitz map, so the Lipschitz image bound gives
`Hⁿ(G(piece)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(piece)`.  Near a point with injective differential, the
differential is antilipschitz and the mean value inequality gives the injectivity and the lower
Lipschitz bound on a small ball; Lindelöf selects countably many such balls, which are enumerated
(padded with an injective linear map). -/
theorem aetp_rectifiable_c1_piece_cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ Z₀ : Set (Amb n ℓ), MeasurableSet Z₀ ∧ (μHE[n] : Measure (Amb n ℓ)) Z₀ = 0 ∧ ∃ (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (r σ : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, 0 < r k) ∧ (∀ k, 0 < σ k) ∧ (∀ k, ∀ b ∈ ball (c k) (r k), Function.Injective (fderiv ℝ (G k) b)) ∧ (∀ k, ∀ b₁ ∈ ball (c k) (r k), ∀ b₂ ∈ ball (c k) (r k), σ k * ‖b₁ - b₂‖ ≤ ‖G k b₁ - G k b₂‖) ∧ M ⊆ Z₀ ∪ ⋃ k, G k '' ball (c k) (r k) := by
  intro n ℓ hn M hM
  obtain ⟨M₀, hM₀, F, hF, hMcov⟩ := hM
  choose K hK using hF
  have hHvol : (μHE[n] : Measure (Rn n)) = volume := EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- The map squeezing the direction of a unit vector `u` by the factor `η` has determinant `η`.
  have hdet : ∀ (u : Rn n), ‖u‖ = 1 → ∀ (η : ℝ),
      LinearMap.det ((ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u :
        Rn n →L[ℝ] Rn n) : Rn n →ₗ[ℝ] Rn n) = η := by
    intro u hu η
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - η) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    set P : Submodule ℝ (Rn n) := ℝ ∙ u
    have hP : ∀ k ∈ P, Θ k = η • k := by
      intro k hk
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hk
      rw [hΘ]
      have : inner ℝ u (c • u) = c := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
      rw [this, smul_smul, ← sub_smul]; congr 1; ring
    have hP' : ∀ k ∈ Pᗮ, Θ k = k := by
      intro k hk
      rw [hΘ]
      have : inner ℝ u k = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hk
      simp [this]
    let e := P.prodEquivOfIsCompl Pᗮ P.isCompl_orthogonal
    have hconj : e.symm.toLinearMap ∘ₗ (Θ : Rn n →ₗ[ℝ] Rn n) ∘ₗ e.symm.symm.toLinearMap =
        LinearMap.prodMap (η • LinearMap.id) LinearMap.id := by
      refine LinearMap.ext fun p => ?_
      obtain ⟨k, k'⟩ := p
      have hep : e.symm.symm (k, k') = (k : Rn n) + k' := rfl
      have hΘp : Θ ((k : Rn n) + k') = e (η • k, k') := by
        rw [map_add, hP k k.2, hP' k' k'.2]; rfl
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, hep, hΘp,
        LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
    rw [← LinearMap.det_conj (Θ : Rn n →ₗ[ℝ] Rn n) e.symm, hconj, LinearMap.det_prodMap,
      LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, finrank_span_singleton hu0]
    ring
  -- On a set where `H` is `η`-approximated by a non-injective linear map `A`, the `Hⁿ`-measure of
  -- the image is at most `(‖A‖ + 1)ⁿ η Lⁿ`.
  have key : ∀ (H : Rn n → Amb n ℓ) (A : Rn n →L[ℝ] Amb n ℓ) (s : Set (Rn n)) (L : ℝ) (η : ℝ≥0),
      ¬ Function.Injective A → ‖A‖ ≤ L → η ≤ 1 → ApproximatesLinearOn H A s η →
      (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤ ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
    intro H A s L η hA hAL hη1 hHA
    obtain ⟨v, hv0, hAv⟩ : ∃ v, v ≠ 0 ∧ A v = 0 := by
      by_contra h
      push Not at h
      exact hA ((injective_iff_map_eq_zero A).2 fun v hv => by_contra fun hne => h v hne hv)
    set u : Rn n := ‖v‖⁻¹ • v with hu_def
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
    have hAu : A u = 0 := by rw [hu_def, map_smul, hAv, smul_zero]
    have hL0 : 0 ≤ L := (norm_nonneg A).trans hAL
    have hη0 : (0 : ℝ) ≤ η := η.2
    have hη1' : (η : ℝ) ≤ 1 := hη1
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - (η : ℝ)) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - (η : ℝ)) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hΘn : ∀ x, ‖A x‖ + η * ‖x‖ ≤ (L + 1) * ‖Θ x‖ := by
      intro x
      set a := inner ℝ u x with ha
      have ha2 : a ^ 2 ≤ ‖x‖ ^ 2 := by
        have := abs_real_inner_le_norm u x
        rw [hu, one_mul] at this
        exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
      have hΘsq : ‖Θ x‖ ^ 2 = ‖x‖ ^ 2 - (1 - (η : ℝ) ^ 2) * a ^ 2 := by
        rw [hΘ, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      set w := x - a • u with hw
      have hwsq : ‖w‖ ^ 2 = ‖x‖ ^ 2 - a ^ 2 := by
        rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      have hAx : A x = A w := by rw [hw, map_sub, map_smul, hAu, smul_zero, sub_zero]
      have h1 : ‖w‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hwsq, hΘsq]; nlinarith [sq_nonneg (η : ℝ), sq_nonneg a]
      have h2 : (η : ℝ) * ‖x‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hΘsq, mul_pow]
        have : 0 ≤ 1 - (η : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left ha2 this]
      calc ‖A x‖ + η * ‖x‖ = ‖A w‖ + η * ‖x‖ := by rw [hAx]
        _ ≤ L * ‖w‖ + ‖Θ x‖ :=
          add_le_add ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hAL (norm_nonneg w))) h2
        _ ≤ L * ‖Θ x‖ + ‖Θ x‖ := by gcongr
        _ = (L + 1) * ‖Θ x‖ := by ring
    have hHΘ : ∀ x ∈ s, ∀ y ∈ s, ‖H x - H y‖ ≤ (L + 1) * ‖Θ x - Θ y‖ := by
      intro x hx y hy
      have h := hHA x hx y hy
      calc ‖H x - H y‖ = ‖(H x - H y - A (x - y)) + A (x - y)‖ := by rw [sub_add_cancel]
        _ ≤ ‖H x - H y - A (x - y)‖ + ‖A (x - y)‖ := norm_add_le _ _
        _ ≤ η * ‖x - y‖ + ‖A (x - y)‖ := by gcongr
        _ = ‖A (x - y)‖ + η * ‖x - y‖ := add_comm _ _
        _ ≤ (L + 1) * ‖Θ (x - y)‖ := hΘn (x - y)
        _ = (L + 1) * ‖Θ x - Θ y‖ := by rw [map_sub]
    classical
    let Φ : Rn n → Amb n ℓ := fun y => H (Function.invFunOn Θ s y)
    have hΦ : ∀ x ∈ s, Φ (Θ x) = H x := by
      intro x hx
      have hex : ∃ a ∈ s, Θ a = Θ x := ⟨x, hx, rfl⟩
      have h1 := Function.invFunOn_mem hex
      have h2 := Function.invFunOn_eq hex
      have := hHΘ _ h1 x hx
      rw [h2, sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have hΦlip : LipschitzOnWith (Real.toNNReal (L + 1)) Φ (Θ '' s) := by
      refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_
      obtain ⟨x₁, hx₁, rfl⟩ := hy₁
      obtain ⟨x₂, hx₂, rfl⟩ := hy₂
      rw [hΦ x₁ hx₁, hΦ x₂ hx₂, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
      exact hHΘ x₁ hx₁ x₂ hx₂
    have himg : H '' s = Φ '' (Θ '' s) := by
      rw [image_image]; exact image_congr fun x hx => (hΦ x hx).symm
    have hvolΘ : (μHE[n] : Measure (Rn n)) (Θ '' s) = (η : ℝ≥0∞) * volume s := by
      rw [hHvol]
      have := MeasureTheory.Measure.addHaar_image_linearMap volume (Θ : Rn n →ₗ[ℝ] Rn n) s
      rw [ContinuousLinearMap.coe_coe] at this
      rw [this, hdet u hu, abs_of_nonneg hη0, ENNReal.ofReal_coe_nnreal]
    calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (Φ '' (Θ '' s)) := by rw [himg]
      _ ≤ (Real.toNNReal (L + 1) : ℝ≥0∞) ^ n * μHE[n] (Θ '' s) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hΦlip
      _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [hvolΘ]; rfl
  -- The image of the critical set of a `C¹` map `ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null.
  have sard : ∀ H : Rn n → Amb n ℓ, ContDiff ℝ 1 H →
      (μHE[n] : Measure (Amb n ℓ)) (H '' {b | ¬ Function.Injective (fderiv ℝ H b)}) = 0 := by
    intro H hH
    set C := {b | ¬ Function.Injective (fderiv ℝ H b)}
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hCclosed : IsClosed C := by
      have : IsOpen {b | Function.Injective (fderiv ℝ H b)} :=
        ContinuousLinearMap.isOpen_injective.preimage hcont
      exact this.isClosed_compl
    have hcov : H '' C ⊆ ⋃ R : ℕ, H '' (C ∩ closedBall 0 R) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_closedBall_zero_iff.2 hR⟩, rfl⟩
    refine measure_mono_null hcov (measure_iUnion_null fun R => ?_)
    set s := C ∩ closedBall (0 : Rn n) R
    obtain ⟨L, hL⟩ :=
      (isCompact_closedBall (0 : Rn n) R).exists_bound_of_continuousOn hcont.continuousOn
    have hsmeas : MeasurableSet s := (hCclosed.inter isClosed_closedBall).measurableSet
    have hbound : ∀ η : ℝ≥0, η ≤ 1 → 0 < η → (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤
        ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
      intro η hη1 hη0
      rcases s.eq_empty_or_nonempty with hse | hsne
      · simp [hse]
      obtain ⟨t, A, hdisj, htm, hst, hap, hA⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H s (fderiv ℝ H)
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) (fun _ => η) (fun _ => hη0.ne')
      have hsU : s = ⋃ m, s ∩ t m := by rw [← inter_iUnion]; exact (inter_eq_left.2 hst).symm
      calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (⋃ m, H '' (s ∩ t m)) := by
            rw [← image_iUnion, ← hsU]
        _ ≤ ∑' m, (μHE[n] : Measure (Amb n ℓ)) (H '' (s ∩ t m)) := measure_iUnion_le _
        _ ≤ ∑' m, ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (s ∩ t m)) := by
            refine ENNReal.tsum_le_tsum fun m => ?_
            obtain ⟨y, hy, hAy⟩ := hA hsne m
            refine key H (A m) (s ∩ t m) L η ?_ ?_ hη1 (hap m)
            · rw [hAy]; exact hy.1
            · rw [hAy]; exact hL y hy.2
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (⋃ m, s ∩ t m)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, measure_iUnion]
            · intro i j hij
              exact (hdisj hij).mono inter_subset_right inter_subset_right
            · exact fun m => hsmeas.inter (htm m)
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [← hsU]
    have hV : volume s ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    have hc : ENNReal.ofReal (L + 1) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hlim := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hV)) (Or.inr hc)
    rw [zero_mul, mul_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hm)
    have := hbound ((m : ℝ≥0)⁻¹) (inv_le_one_of_one_le₀ (by exact_mod_cast hm))
      (inv_pos.2 (Nat.cast_pos.2 hm))
    rwa [ENNReal.coe_inv hm0, ENNReal.coe_natCast] at this
  -- Near a point with injective differential: injectivity and a lower Lipschitz bound on a ball.
  have loc : ∀ (H : Rn n → Amb n ℓ), ContDiff ℝ 1 H → ∀ b, Function.Injective (fderiv ℝ H b) →
      ∃ ρ > 0, ∃ σ > 0, (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ H b')) ∧
        ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖H b₁ - H b₂‖ := by
    intro H hH b hinj
    set D := fderiv ℝ H b
    obtain ⟨Ka, hKpos, hKa⟩ := (LinearMap.injective_iff_antilipschitz (D : Rn n →ₗ[ℝ] Amb n ℓ)).1 hinj
    have hKpos' : (0 : ℝ) < Ka := hKpos
    have hlow : ∀ x, ‖x‖ ≤ Ka * ‖D x‖ := by
      intro x
      have := hKa.le_mul_dist x 0
      simpa [dist_eq_norm] using this
    set s₀ : ℝ := (Ka : ℝ)⁻¹ with hs₀
    have hs₀pos : 0 < s₀ := inv_pos.2 hKpos'
    have hlow' : ∀ x, s₀ * ‖x‖ ≤ ‖D x‖ := by
      intro x
      rw [hs₀, inv_mul_le_iff₀ hKpos']
      exact hlow x
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    obtain ⟨ρ, hρ, hρD⟩ := Metric.continuous_iff.1 hcont b (s₀ / 2) (by positivity)
    have hnear : ∀ b' ∈ ball b ρ, ‖fderiv ℝ H b' - D‖ < s₀ / 2 := fun b' hb' => by
      rw [← dist_eq_norm]; exact hρD b' hb'
    refine ⟨ρ, hρ, s₀ / 2, by positivity, ?_, ?_⟩
    · intro b' hb' x y hxy
      by_contra hne
      have hz : x - y ≠ 0 := sub_ne_zero.2 hne
      have h0 : fderiv ℝ H b' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : ‖fderiv ℝ H b' (x - y) - D (x - y)‖ ≤ ‖fderiv ℝ H b' - D‖ * ‖x - y‖ :=
        (fderiv ℝ H b' - D).le_opNorm (x - y)
      rw [h0, zero_sub, norm_neg] at h1
      have h2 := hlow' (x - y)
      have h3 := hnear b' hb'
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 hz
      nlinarith
    · intro b₁ hb₁ b₂ hb₂
      have hmv : ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ ≤ s₀ / 2 * ‖b₁ - b₂‖ := by
        have := (convex_ball b ρ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (f := fun x => H x - D x) (C := s₀ / 2) (fun x _ => (hdiff x).sub D.differentiableAt)
          (fun x hx => ?_) hb₂ hb₁
        · simpa using this
        · rw [fderiv_fun_sub (hdiff x) D.differentiableAt, ContinuousLinearMap.fderiv]
          exact (hnear x hx).le
      have h2 := hlow' (b₁ - b₂)
      have h3 : ‖D (b₁ - b₂)‖ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := by
        rw [map_sub]
        calc ‖D b₁ - D b₂‖ = ‖(H b₁ - H b₂) - ((H b₁ - D b₁) - (H b₂ - D b₂))‖ := by
              congr 1; abel
          _ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := norm_sub_le _ _
      linarith
  -- A `C¹` map with injective differential at `0`, used to pad the enumeration.
  obtain ⟨G₀, hG₀, hG₀inj⟩ :
      ∃ G₀ : Rn n → Amb n ℓ, ContDiff ℝ 1 G₀ ∧ Function.Injective (fderiv ℝ G₀ 0) := by
    let p : Fin (n + ℓ) → Fin n := fun q => ⟨q % n, Nat.mod_lt _ hn⟩
    have hp : Function.Surjective p := fun i => ⟨Fin.castAdd ℓ i, Fin.ext (Nat.mod_eq_of_lt i.2)⟩
    let E₀ : Rn n →ₗ[ℝ] Amb n ℓ := (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℝ ℝ p ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    have hE₀ : Function.Injective E₀ :=
      (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.injective.comp
        ((LinearMap.funLeft_injective_of_surjective ℝ ℝ p hp).comp
          (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
    refine ⟨LinearMap.toContinuousLinearMap E₀, (LinearMap.toContinuousLinearMap E₀).contDiff, ?_⟩
    rw [ContinuousLinearMap.fderiv]
    exact hE₀
  -- `C¹` approximation of the coordinates of the Lipschitz maps `F j`.
  have happrox : ∀ (i j : ℕ) (q : Fin (n + ℓ)), ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧
      volume {x | (F j x).ofLp q ≠ g x} < ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i j q
    exact aetp_lipschitz_c1_approximation n hn (fun x => (F j x).ofLp q) _
      ((EuclideanSpace.proj q : Amb n ℓ →L[ℝ] ℝ).lipschitzWith.comp (hK j)) _
      (ENNReal.inv_pos.2 (by simp))
  choose g hg hgvol using happrox
  let G : ℕ → ℕ → Rn n → Amb n ℓ := fun i j x => WithLp.toLp 2 (fun q => g i j q x)
  have hGC1 : ∀ i j, ContDiff ℝ 1 (G i j) := fun i j => contDiff_euclidean.2 fun q => hg i j q
  -- The points where `F j` differs from every approximation form a Lebesgue-null set.
  let Z : ℕ → Set (Rn n) := fun j => ⋂ i, {x | F j x ≠ G i j x}
  have hZvol : ∀ j, volume (Z j) = 0 := by
    intro j
    have hle : ∀ i : ℕ, volume (Z j) ≤ ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by
      intro i
      calc volume (Z j) ≤ volume (⋃ q, {x | (F j x).ofLp q ≠ g i j q x}) := by
            refine measure_mono fun x hx => ?_
            have hx' : F j x ≠ G i j x := mem_iInter.1 hx i
            by_contra hcon
            simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
            exact hx' (PiLp.ext fun q => hcon q)
        _ ≤ ∑ q, volume {x | (F j x).ofLp q ≠ g i j q x} := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _q : Fin (n + ℓ), ((i : ℝ≥0∞) + 1)⁻¹ :=
            Finset.sum_le_sum fun q _ => (hgvol i j q).le
        _ = ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by simp
    have h0 : Tendsto (fun i : ℕ => ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.natCast_ne_top (n + ℓ)))
    exact le_antisymm (ge_of_tendsto' h0 hle) zero_le
  have hFZ : ∀ j, (μHE[n] : Measure (Amb n ℓ)) (F j '' Z j) = 0 := by
    intro j
    refine le_antisymm ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      n ((hK j).lipschitzOnWith)).trans ?_) zero_le
    rw [hHvol, hZvol j, mul_zero]
  -- Radii and lower Lipschitz constants around the points with injective differential.
  have hloc' : ∀ (i j : ℕ) (b : Rn n), ∃ ρ : ℝ, 0 < ρ ∧ ∃ σ : ℝ, 0 < σ ∧
      (Function.Injective (fderiv ℝ (G i j) b) →
        (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ (G i j) b')) ∧
          ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖G i j b₁ - G i j b₂‖) := by
    intro i j b
    by_cases hb : Function.Injective (fderiv ℝ (G i j) b)
    · obtain ⟨ρ, hρ, σ, hσ, h1, h2⟩ := loc _ (hGC1 i j) b hb
      exact ⟨ρ, hρ, σ, hσ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, one_pos, 1, one_pos, fun h => absurd h hb⟩
  choose ρ hρ σ hσ hρσ using hloc'
  obtain ⟨ρ₀, hρ₀, σ₀, hσ₀, hG₀ball, hG₀low⟩ := loc G₀ hG₀ 0 hG₀inj
  -- Lindelöf: countably many of these balls cover the non-critical set of each `G i j`.
  have hT : ∀ i j, ∃ T : Set (Rn n), T.Countable ∧
      ⋃ b ∈ T, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) =
        ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
    fun i j => TopologicalSpace.isOpen_iUnion_countable _ fun b => isOpen_ball.inter isOpen_const
  choose T hTc hTU using hT
  -- Enumerate the countably many pieces.
  let S : Set (ℕ × ℕ × Rn n) := ⋃ i, ⋃ j, (fun b => (i, j, b)) '' T i j
  have hS : S.Countable := countable_iUnion fun i => countable_iUnion fun j => (hTc i j).image _
  obtain ⟨e, he⟩ := (hS.insert (0, 0, 0)).exists_eq_range (insert_nonempty _ _)
  classical
  let valid : ℕ → Prop := fun k => Function.Injective (fderiv ℝ (G (e k).1 (e k).2.1) (e k).2.2)
  let Gk : ℕ → Rn n → Amb n ℓ := fun k => if valid k then G (e k).1 (e k).2.1 else G₀
  let ck : ℕ → Rn n := fun k => if valid k then (e k).2.2 else 0
  let rk : ℕ → ℝ := fun k => if valid k then ρ (e k).1 (e k).2.1 (e k).2.2 else ρ₀
  let σk : ℕ → ℝ := fun k => if valid k then σ (e k).1 (e k).2.1 (e k).2.2 else σ₀
  -- The exceptional set and its Borel null hull.
  let Zbad : Set (Amb n ℓ) := M₀ ∪ (⋃ j, F j '' Z j) ∪
    ⋃ i, ⋃ j, G i j '' {b | ¬ Function.Injective (fderiv ℝ (G i j) b)}
  have hZbad : (μHE[n] : Measure (Amb n ℓ)) Zbad = 0 :=
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hFZ))
      (measure_iUnion_null fun i => measure_iUnion_null fun j => sard _ (hGC1 i j))
  refine ⟨toMeasurable μHE[n] Zbad, measurableSet_toMeasurable _ _,
    by rw [measure_toMeasurable]; exact hZbad, Gk, ck, rk, σk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases h : valid k
    · simp only [Gk, h, ↓reduceIte]; exact hGC1 _ _
    · simp only [Gk, h, ↓reduceIte]; exact hG₀
  · intro k
    by_cases h : valid k
    · simp only [rk, h, ↓reduceIte]; exact hρ _ _ _
    · simp only [rk, h, ↓reduceIte]; exact hρ₀
  · intro k
    by_cases h : valid k
    · simp only [σk, h, ↓reduceIte]; exact hσ _ _ _
    · simp only [σk, h, ↓reduceIte]; exact hσ₀
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).1
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact hG₀ball
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).2
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact hG₀low
  · intro x hx
    rcases hMcov hx with hx0 | hx1
    · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inl hx0)))
    · obtain ⟨j, z, rfl⟩ := mem_iUnion.1 hx1
      by_cases hz : z ∈ Z j
      · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inr (mem_iUnion.2 ⟨j, mem_image_of_mem _ hz⟩))))
      · simp only [Z, mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
        obtain ⟨i, hi⟩ := hz
        by_cases hzC : Function.Injective (fderiv ℝ (G i j) z)
        · have hzU : z ∈ ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
            mem_iUnion.2 ⟨z, mem_ball_self (hρ i j z), hzC⟩
          rw [← hTU i j] at hzU
          simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop] at hzU
          obtain ⟨b, hbT, hzb, hbinj⟩ := hzU
          have hmem : (i, j, b) ∈ range e := by
            rw [← he]
            exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_image_of_mem _ hbT⟩⟩)
          obtain ⟨k, hk⟩ := hmem
          have hv : valid k := by simp only [valid, hk]; exact hbinj
          refine Or.inr (mem_iUnion.2 ⟨k, ?_⟩)
          simp only [Gk, ck, rk, hv, ↓reduceIte, hk]
          exact ⟨z, hzb, hi.symm⟩
        · exact Or.inl (subset_toMeasurable _ _
            (Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, ⟨z, hzC, hi.symm⟩⟩⟩)))
/-- Simon Ch. 3, 1.4 for an embedded `C¹` piece: if `G : ℝⁿ → ℝ^{n+ℓ}` is `C¹` with injective
derivative on `B = B̆_r(c)` and `σ|b₁ - b₂| ≤ |G(b₁) - G(b₂)|` on `B` (`σ > 0`), then `N = G(B)` is
Borel with `Hⁿ(N) < ∞`, and `DG(b)(ℝⁿ)` is the approximate tangent space of `N` at every `G(b)`.
Borel: Lusin–Souslin.  Finite: `G` is Lipschitz on `B`.  Tangent: by strict differentiability,
`‖G u - G v - DG(b)(u - v)‖ ≤ η‖u - v‖` near `b`; with `L = DG(b)`, `K = B_{R/σ}(0)` and
`Γ_λ(z) = λ⁻¹(G(b + λz) - G(b))`, the map `Φ = Γ_λ ∘ L⁻¹` is `(1 ± δ)`-bi-Lipschitz from `L(K)`
onto a piece of `η_{G(b),λ}(N)` containing `η_{G(b),λ}(N) ∩ {f ≠ 0}`; hence
`(1 - δ)ⁿ Φ_#(Hⁿ ⌞ L(K)) ≤ Hⁿ ⌞ Φ(L(K)) ≤ (1 + δ)ⁿ Φ_#(Hⁿ ⌞ L(K))`, and `|f ∘ Φ - f|` is
uniformly small on `L(K)`, while `Hⁿ ⌞ L(K)` carries `∫_P f dHⁿ`. -/
theorem aetp_c1_piece_approxTangent : ∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ) (c : Rn n) (r σ : ℝ), ContDiff ℝ 1 G → 0 < σ → (∀ b ∈ ball c r, Function.Injective (fderiv ℝ G b)) → (∀ b₁ ∈ ball c r, ∀ b₂ ∈ ball c r, σ * ‖b₁ - b₂‖ ≤ ‖G b₁ - G b₂‖) → MeasurableSet (G '' ball c r) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c r) < ⊤ ∧ ∀ b ∈ ball c r, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c r) (G b) (LinearMap.range (fderiv ℝ G b).toLinearMap) := by
  intro n ℓ G c r σ hG hσ hinj hlow
  have hGc : Continuous G := hG.continuous
  -- `G` is injective on `B` by the lower bound.
  have hGinj : InjOn G (ball c r) := by
    intro b₁ h₁ b₂ h₂ heq
    have h := hlow b₁ h₁ b₂ h₂
    rw [heq, sub_self, norm_zero] at h
    have h' : ‖b₁ - b₂‖ ≤ 0 := le_of_mul_le_mul_left (by rwa [mul_zero]) hσ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  -- (i) Borel: Lusin–Souslin.
  have hNmeas : MeasurableSet (G '' ball c r) :=
    measurableSet_ball.image_of_continuousOn_injOn hGc.continuousOn hGinj
  refine ⟨hNmeas, ?_, ?_⟩
  · -- (ii) `G` is Lipschitz on the convex set `B`, so `Hⁿ(G(B)) ≤ Cⁿ Lⁿ(B) < ∞`.
    obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
      (hG.continuous_fderiv one_ne_zero).continuousOn
    have hlip : LipschitzOnWith (Real.toNNReal C) G (ball c r) := by
      refine (convex_ball c r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        (fun x _ => hG.differentiable one_ne_zero x) fun x hx => ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact le_max_of_le_left (hC x (ball_subset_closedBall hx))
    calc (μHE[n] : Measure (Amb n ℓ)) (G '' ball c r)
        ≤ (Real.toNNReal C : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (ball c r) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
      _ < ⊤ := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) measure_ball_lt_top
  · -- (iii) the approximate tangent space at `G b`.
    intro b hb
    set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G b
    have hLinj : Function.Injective L := hinj b hb
    refine ⟨?_, fun f => ?_⟩
    · rw [LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj,
        finrank_euclideanSpace_fin]
    -- Strict differentiability at `b`, in the form of a local two-point estimate.
    have hstrict : HasStrictFDerivAt G L b := hG.contDiffAt.hasStrictFDerivAt one_ne_zero
    have hloc : ∀ η > 0, ∃ ρ > 0, ball b ρ ⊆ ball c r ∧
        ∀ u ∈ ball b ρ, ∀ v ∈ ball b ρ, ‖G u - G v - L (u - v)‖ ≤ η * ‖u - v‖ := by
      intro η hη
      obtain ⟨ρ₁, hρ₁, h₁⟩ :=
        Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hstrict.isLittleO hη)
      obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.isOpen_iff.1 isOpen_ball b hb
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (ball_subset_ball (min_le_right _ _)).trans h₂, ?_⟩
      intro u hu v hv
      have hu' : dist u b < ρ₁ := lt_of_lt_of_le (mem_ball.1 hu) (min_le_left _ _)
      have hv' : dist v b < ρ₁ := lt_of_lt_of_le (mem_ball.1 hv) (min_le_left _ _)
      exact @h₁ (u, v) (by rw [Prod.dist_eq]; exact max_lt hu' hv')
    -- The lower bound passes to the derivative: `σ‖v‖ ≤ ‖L v‖`.
    have hLlow : ∀ v, σ * ‖v‖ ≤ ‖L v‖ := by
      intro v
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨ρ, hρ, hρB, hρest⟩ := hloc (ε / (‖v‖ + 1)) (by positivity)
      set t : ℝ := ρ / (2 * (‖v‖ + 1)) with ht
      have ht0 : 0 < t := by positivity
      have htv : t * ‖v‖ < ρ := by
        rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        exact mul_lt_mul_of_pos_left (by linarith only [norm_nonneg v]) hρ
      have hu : b + t • v ∈ ball b ρ := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
        exact htv
      have e1 := hlow (b + t • v) (hρB hu) b hb
      have e2 := hρest (b + t • v) hu b (mem_ball_self hρ)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le] at e1 e2
      rw [map_smul] at e2
      have e3 : ‖G (b + t • v) - G b‖ ≤ t * ‖L v‖ + ε / (‖v‖ + 1) * (t * ‖v‖) := by
        calc ‖G (b + t • v) - G b‖ = ‖(G (b + t • v) - G b - t • L v) + t • L v‖ := by
              congr 1; abel
          _ ≤ ‖G (b + t • v) - G b - t • L v‖ + ‖t • L v‖ := norm_add_le _ _
          _ ≤ ε / (‖v‖ + 1) * (t * ‖v‖) + t * ‖L v‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht0.le]; exact add_le_add e2 le_rfl
          _ = t * ‖L v‖ + ε / (‖v‖ + 1) * (t * ‖v‖) := by ring
      have e4 : t * (σ * ‖v‖) ≤ t * (‖L v‖ + ε / (‖v‖ + 1) * ‖v‖) := by
        linarith only [e1, e3]
      have e5 : σ * ‖v‖ ≤ ‖L v‖ + ε / (‖v‖ + 1) * ‖v‖ := le_of_mul_le_mul_left e4 ht0
      have e6 : ε / (‖v‖ + 1) * ‖v‖ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
      linarith only [e5, e6]
    -- A linear left inverse `M` of `L`.
    obtain ⟨Mlin, hMlin⟩ :=
      LinearMap.exists_leftInverse_of_injective (L : Rn n →ₗ[ℝ] Amb n ℓ)
        (LinearMap.ker_eq_bot.2 hLinj)
    have hML : ∀ z, Mlin (L z) = z := fun z => by
      simpa using LinearMap.congr_fun hMlin z
    have hMc : Continuous Mlin := LinearMap.continuous_of_finiteDimensional Mlin
    -- Data of the test function `f`.
    have hfc : Continuous f := map_continuous f
    have hfcs : HasCompactSupport f := f.hasCompactSupport
    obtain ⟨R₀, hR₀⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    set R : ℝ := max R₀ 1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsupp : ∀ y, f y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      have h := hR₀ (subset_tsupport f hy)
      rw [mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    obtain ⟨Mf₀, hMf₀⟩ := hfc.bounded_above_of_compact_support hfcs
    set Mf : ℝ := max Mf₀ 0
    have hMf0 : 0 ≤ Mf := le_max_right _ _
    have hfM : ∀ y, |f y| ≤ Mf := fun y => by
      rw [← Real.norm_eq_abs]; exact (hMf₀ y).trans (le_max_left _ _)
    have hfuc : UniformContinuous f := hfcs.uniformContinuous_of_continuous hfc
    -- The compact parameter set `K` and the plane piece `A = L(K)`.
    set R' : ℝ := R / σ with hR'
    have hR'0 : 0 < R' := div_pos hR0 hσ
    set K : Set (Rn n) := closedBall 0 R' with hK
    set A : Set (Amb n ℓ) := L '' K
    have hKc : IsCompact K := isCompact_closedBall 0 R'
    have hAc : IsCompact A := hKc.image L.continuous
    have hAmeas : MeasurableSet A := hAc.isClosed.measurableSet
    have hAfin : (μHE[n] : Measure (Amb n ℓ)) A < ⊤ := by
      calc (μHE[n] : Measure (Amb n ℓ)) A
          ≤ (‖L‖₊ : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) K :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              L.lipschitzWith.lipschitzOnWith
        _ < ⊤ := by
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
            exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hKc.measure_lt_top
    set HA : ℝ := ((μHE[n] : Measure (Amb n ℓ)) A).toReal
    have hHA0 : 0 ≤ HA := ENNReal.toReal_nonneg
    -- The limit integral lives on `A`.
    have hI0 : ∫ y in (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)), f y ∂μHE[n] =
        ∫ y in A, f y ∂μHE[n] := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      · exact (Submodule.closed_of_finiteDimensional _).measurableSet
      · rintro _ ⟨z, -, rfl⟩
        exact LinearMap.mem_range_self (L : Rn n →ₗ[ℝ] Amb n ℓ) z
      · rintro y ⟨hyP, hyA⟩
        by_contra hfy
        obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hyP
        apply hyA
        refine ⟨v, ?_, rfl⟩
        rw [hK, mem_closedBall, dist_zero_right, hR', le_div_iff₀ hσ]
        have h1 := hsupp _ hfy
        have h2 := hLlow v
        simp only [ContinuousLinearMap.coe_coe] at h1
        linarith
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- Choice of the parameters.
    obtain ⟨τ, hτ, hτf⟩ := Metric.uniformContinuous_iff.1 hfuc (ε / (2 * (HA + 1))) (by positivity)
    have hκcont : Tendsto (fun d : ℝ => (((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n) (𝓝 0) (𝓝 0) := by
      have h1 : ContinuousAt (fun d : ℝ => (1 - d)⁻¹) 0 :=
        ((continuous_const.sub continuous_id).continuousAt).inv₀ (by norm_num)
      have h2 : ContinuousAt (fun d : ℝ => (((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n) 0 :=
        ((h1.pow n).sub continuousAt_const).mul (h1.pow n)
      simpa using h2.tendsto
    obtain ⟨d₀, hd₀, hd₀'⟩ := Metric.eventually_nhds_iff.1
      (hκcont.eventually (eventually_lt_nhds
        (show (0 : ℝ) < ε / (4 * (Mf + 1) * (HA + 1)) by positivity)))
    set δ : ℝ := min (d₀ / 2) (1 / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
    set κ : ℝ := ((1 - δ)⁻¹) ^ n
    have hκbound : (κ - 1) * κ < ε / (4 * (Mf + 1) * (HA + 1)) := by
      apply hd₀'
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd₀)
    have hκ1 : 1 ≤ κ :=
      one_le_pow₀ ((one_le_inv₀ (by linarith only [hδ1])).2 (by linarith only [hδ0]))
    set η : ℝ := min (δ * σ) (τ / (2 * (R' + 1)))
    have hη0 : 0 < η := lt_min (by positivity) (by positivity)
    obtain ⟨ρ, hρ, hρB, hρest⟩ := hloc η hη0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / (R' + 1) by positivity)] with lam hlam
    obtain ⟨hlam0, hlam1⟩ := hlam
    -- The rescaled parametrization `Γ` and the comparison map `Φ = Γ ∘ M`.
    set Γ : Rn n → Amb n ℓ := fun z => lam⁻¹ • (G (b + lam • z) - G b) with hΓ
    set Φ : Amb n ℓ → Amb n ℓ := fun y => Γ (Mlin y) with hΦ
    have hΦL : ∀ z, Φ (L z) = Γ z := fun z => by
      simp only [hΦ, hML]
    have hΦc : Continuous Φ := by
      simp only [hΦ, hΓ]
      fun_prop
    have hΦm : Measurable Φ := hΦc.measurable
    have hball : ∀ z ∈ K, b + lam • z ∈ ball b ρ := by
      intro z hz
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam0.le]
      have hz' : ‖z‖ ≤ R' := mem_closedBall_zero_iff.1 hz
      have h1 : lam * (R' + 1) < ρ := by rwa [lt_div_iff₀ (by positivity)] at hlam1
      calc lam * ‖z‖ ≤ lam * (R' + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only [hz']) hlam0.le
        _ < ρ := h1
    have hΓest : ∀ z ∈ K, ∀ w ∈ K, ‖Γ z - Γ w - L (z - w)‖ ≤ η * ‖z - w‖ := by
      intro z hz w hw
      have h := hρest _ (hball z hz) _ (hball w hw)
      have heq : Γ z - Γ w - L (z - w) =
          lam⁻¹ • (G (b + lam • z) - G (b + lam • w) - L (lam • (z - w))) := by
        simp only [hΓ, map_sub, map_smul, smul_sub, inv_smul_smul₀ hlam0.ne']
        abel
      rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam0.le)]
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam0.le] at h
      calc lam⁻¹ * ‖G (b + lam • z) - G (b + lam • w) - L (lam • (z - w))‖
          ≤ lam⁻¹ * (η * (lam * ‖z - w‖)) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hlam0.le)
        _ = η * ‖z - w‖ := by rw [mul_left_comm, inv_mul_cancel_left₀ hlam0.ne']
    -- `Φ` is `(1 ± δ)`-bi-Lipschitz on `A`.
    have hΦest : ∀ p ∈ A, ∀ q ∈ A, ‖(Φ p - Φ q) - (p - q)‖ ≤ δ * ‖p - q‖ := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [hΦL, hΦL, ← map_sub]
      calc ‖Γ z - Γ w - L (z - w)‖ ≤ η * ‖z - w‖ := hΓest z hz w hw
        _ ≤ (δ * σ) * ‖z - w‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ = δ * (σ * ‖z - w‖) := mul_assoc _ _ _
        _ ≤ δ * ‖L (z - w)‖ := mul_le_mul_of_nonneg_left (hLlow _) hδ0.le
    have hΦup : ∀ p ∈ A, ∀ q ∈ A, dist (Φ p) (Φ q) ≤ (1 + δ) * dist p q := by
      intro p hp q hq
      rw [dist_eq_norm, dist_eq_norm]
      have h := hΦest p hp q hq
      calc ‖Φ p - Φ q‖ = ‖(Φ p - Φ q - (p - q)) + (p - q)‖ := by congr 1; abel
        _ ≤ ‖Φ p - Φ q - (p - q)‖ + ‖p - q‖ := norm_add_le _ _
        _ ≤ (1 + δ) * ‖p - q‖ := by linarith only [h]
    have hΦlow : ∀ p ∈ A, ∀ q ∈ A, (1 - δ) * dist p q ≤ dist (Φ p) (Φ q) := by
      intro p hp q hq
      rw [dist_eq_norm, dist_eq_norm]
      have h := hΦest p hp q hq
      have h2 : ‖p - q‖ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := by
        calc ‖p - q‖ = ‖(Φ p - Φ q) - (Φ p - Φ q - (p - q))‖ := by congr 1; abel
          _ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := norm_sub_le _ _
      linarith only [h, h2]
    have hlip1 : LipschitzOnWith (Real.toNNReal (1 + δ)) Φ A := by
      apply LipschitzOnWith.of_dist_le_mul
      intro p hp q hq
      rw [Real.coe_toNNReal _ (by linarith only [hδ0])]
      exact hΦup p hp q hq
    have hΦinj : InjOn Φ A := by
      intro p hp q hq hpq
      have h := hΦlow p hp q hq
      rw [hpq, dist_self] at h
      have h' : dist p q ≤ 0 :=
        le_of_mul_le_mul_left (by rwa [mul_zero]) (by linarith only [hδ1] : (0 : ℝ) < 1 - δ)
      exact dist_le_zero.1 h'
    set Ψ : Amb n ℓ → Amb n ℓ := Function.invFunOn Φ A
    have hΨΦ : LeftInvOn Ψ Φ A := hΦinj.leftInvOn_invFunOn
    have hlip2 : LipschitzOnWith (Real.toNNReal (1 - δ)⁻¹) Ψ (Φ '' A) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      rw [hΨΦ hp, hΨΦ hq, Real.coe_toNNReal _ (inv_nonneg.2 (by linarith only [hδ1])),
        le_inv_mul_iff₀ (by linarith only [hδ1])]
      exact hΦlow p hp q hq
    -- The three measures and their comparison.
    set μ₃ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict A with hμ₃
    set μ₂ : Measure (Amb n ℓ) := μ₃.map Φ with hμ₂
    set μ₁ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) with hμ₁
    set κ₁ : ℝ≥0∞ := (Real.toNNReal (1 + δ) : ℝ≥0∞) ^ n with hκ₁
    set κ₂ : ℝ≥0∞ := (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ n with hκ₂
    have hκ₁top : κ₁ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hκ₂top : κ₂ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hκ₁le : κ₁.toReal ≤ κ := by
      rw [hκ₁, ENNReal.toReal_pow, ENNReal.coe_toReal, Real.coe_toNNReal _ (by linarith only [hδ0])]
      apply pow_le_pow_left₀ (by linarith only [hδ0])
      rw [← one_div, le_div_iff₀ (by linarith only [hδ1])]
      linarith only [mul_self_nonneg δ]
    have hκ₂eq : κ₂.toReal = κ := by
      rw [hκ₂, ENNReal.toReal_pow, ENNReal.coe_toReal,
        Real.coe_toNNReal _ (inv_nonneg.2 (by linarith only [hδ1]))]
    have hμ12 : μ₁ ≤ κ₁ • μ₂ := by
      rw [Measure.le_iff]
      intro S hS
      rw [Measure.smul_apply, smul_eq_mul, hμ₂, Measure.map_apply hΦm hS, hμ₁, hμ₃,
        Measure.restrict_apply hS, Measure.restrict_apply (hS.preimage hΦm), ← image_preimage_inter]
      exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hlip1.mono inter_subset_right)
    have hμ21 : μ₂ ≤ κ₂ • μ₁ := by
      rw [Measure.le_iff]
      intro S hS
      rw [Measure.smul_apply, smul_eq_mul, hμ₂, Measure.map_apply hΦm hS, hμ₁, hμ₃,
        Measure.restrict_apply hS, Measure.restrict_apply (hS.preimage hΦm)]
      have hT : Ψ '' (Φ '' (Φ ⁻¹' S ∩ A)) = Φ ⁻¹' S ∩ A :=
        (hΨΦ.mono inter_subset_right).image_image
      calc (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A)
          = (μHE[n] : Measure (Amb n ℓ)) (Ψ '' (Φ '' (Φ ⁻¹' S ∩ A))) := by rw [hT]
        _ ≤ κ₂ * (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hlip2.mono (image_mono inter_subset_right))
        _ = κ₂ * (μHE[n] : Measure (Amb n ℓ)) (S ∩ Φ '' A) := by rw [image_preimage_inter]
    have hμ₃fin : IsFiniteMeasure μ₃ := ⟨by rw [hμ₃, Measure.restrict_apply_univ]; exact hAfin⟩
    have hμ₂fin : IsFiniteMeasure μ₂ := Measure.isFiniteMeasure_map μ₃ Φ
    have hμ₁fin : IsFiniteMeasure μ₁ := ⟨by
      calc μ₁ univ ≤ (κ₁ • μ₂) univ := hμ12 univ
        _ < ⊤ := by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hκ₁top) (measure_lt_top μ₂ univ)⟩
    have hμ₃univ : μ₃.real univ = HA := by
      rw [measureReal_def, hμ₃, Measure.restrict_apply_univ]
    have hμ₂univ : μ₂.real univ = HA := by
      rw [measureReal_def, hμ₂, Measure.map_apply hΦm MeasurableSet.univ, preimage_univ,
        ← measureReal_def, hμ₃univ]
    -- Sandwich estimate for nonnegative bounded continuous functions.
    have hsand : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ y, 0 ≤ g y) → (∀ y, g y ≤ Mf) →
        |∫ y, g y ∂μ₁ - ∫ y, g y ∂μ₂| ≤ (κ - 1) * κ * (Mf * HA) := by
      intro g hgc hg0 hgM
      have hgb : ∀ y, ‖g y‖ ≤ Mf := fun y => by rw [Real.norm_of_nonneg (hg0 y)]; exact hgM y
      have hg1 : Integrable g μ₁ :=
        Integrable.of_bound hgc.aestronglyMeasurable Mf (ae_of_all _ hgb)
      have hg2 : Integrable g μ₂ :=
        Integrable.of_bound hgc.aestronglyMeasurable Mf (ae_of_all _ hgb)
      have ha0 : 0 ≤ ∫ y, g y ∂μ₂ := integral_nonneg hg0
      have hb0 : 0 ≤ ∫ y, g y ∂μ₁ := integral_nonneg hg0
      have haM : ∫ y, g y ∂μ₂ ≤ Mf * HA := by
        have h := norm_integral_le_of_norm_le_const (μ := μ₂) (ae_of_all _ hgb)
        rwa [Real.norm_of_nonneg ha0, hμ₂univ] at h
      have h1 : ∫ y, g y ∂μ₁ ≤ κ * ∫ y, g y ∂μ₂ := by
        calc ∫ y, g y ∂μ₁ ≤ ∫ y, g y ∂(κ₁ • μ₂) :=
              integral_mono_measure hμ12 (ae_of_all _ hg0) (hg2.smul_measure hκ₁top)
          _ = κ₁.toReal * ∫ y, g y ∂μ₂ := by rw [integral_smul_measure, smul_eq_mul]
          _ ≤ κ * ∫ y, g y ∂μ₂ := mul_le_mul_of_nonneg_right hκ₁le ha0
      have h2 : ∫ y, g y ∂μ₂ ≤ κ * ∫ y, g y ∂μ₁ := by
        calc ∫ y, g y ∂μ₂ ≤ ∫ y, g y ∂(κ₂ • μ₁) :=
              integral_mono_measure hμ21 (ae_of_all _ hg0) (hg1.smul_measure hκ₂top)
          _ = κ₂.toReal * ∫ y, g y ∂μ₁ := by rw [integral_smul_measure, smul_eq_mul]
          _ = κ * ∫ y, g y ∂μ₁ := by rw [hκ₂eq]
      have hk0 : 0 ≤ κ - 1 := sub_nonneg.2 hκ1
      have h3 : (κ - 1) * ∫ y, g y ∂μ₁ ≤ (κ - 1) * (κ * ∫ y, g y ∂μ₂) :=
        mul_le_mul_of_nonneg_left h1 hk0
      have h4 : (κ - 1) * κ * ∫ y, g y ∂μ₂ ≤ (κ - 1) * κ * (Mf * HA) :=
        mul_le_mul_of_nonneg_left haM (mul_nonneg hk0 (zero_le_one.trans hκ1))
      have h5 : (κ - 1) * ∫ y, g y ∂μ₂ ≤ (κ - 1) * κ * ∫ y, g y ∂μ₂ := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ1 ha0) hk0
        linarith only [this]
      rw [abs_le]
      constructor <;> linarith only [h1, h2, h3, h4, h5]
    -- The blown-up piece: `η_{G b, λ}(N) ∩ {f ≠ 0} ⊆ Φ(A) ⊆ η_{G b, λ}(N)`.
    have hNlam :
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G b) lam '' (G '' ball c r), f y ∂μHE[n] =
          ∫ y, f y ∂μ₁ := by
      rw [hμ₁]
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      · rw [Set.image_eq_preimage_of_inverse (g := fun y => G b + lam • y)
          (fun w => by
            simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
            rw [smul_inv_smul₀ hlam0.ne', add_sub_cancel])
          (fun y => by
            simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
            rw [add_sub_cancel_left, inv_smul_smul₀ hlam0.ne'])]
        exact hNmeas.preimage (continuous_const.add (continuous_const_smul lam)).measurable
      · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        rw [hΦL]
        exact ⟨G (b + lam • z), ⟨b + lam • z, hρB (hball z hz), rfl⟩, rfl⟩
      · rintro y ⟨⟨_, ⟨b', hb', rfl⟩, rfl⟩, hyA⟩
        by_contra hfy
        apply hyA
        have hy := hsupp _ hfy
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hlam0.le)] at hy
        have h2 := hlow b' hb' b hb
        have hz : ‖lam⁻¹ • (b' - b)‖ ≤ R' := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam0.le), hR', le_div_iff₀ hσ]
          calc lam⁻¹ * ‖b' - b‖ * σ = lam⁻¹ * (σ * ‖b' - b‖) := by ring
            _ ≤ lam⁻¹ * ‖G b' - G b‖ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hlam0.le)
            _ ≤ R := hy
        refine ⟨L (lam⁻¹ • (b' - b)), ⟨lam⁻¹ • (b' - b), mem_closedBall_zero_iff.2 hz, rfl⟩, ?_⟩
        rw [hΦL]
        simp only [hΓ, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul,
          mul_inv_cancel₀ hlam0.ne', one_smul, add_sub_cancel]
    -- `f ∘ Φ` is uniformly close to `f` on `A`.
    have hclose : ∀ y ∈ A, |f (Φ y) - f y| < ε / (2 * (HA + 1)) := by
      rintro _ ⟨z, hz, rfl⟩
      have h0K : (0 : Rn n) ∈ K := mem_closedBall_self hR'0.le
      have h := hΓest z hz 0 h0K
      have hΓ0 : Γ 0 = 0 := by simp only [hΓ, smul_zero, add_zero, sub_self]
      rw [hΓ0, sub_zero, sub_zero] at h
      have hzR : ‖z‖ ≤ R' := mem_closedBall_zero_iff.1 hz
      have hηR : η * R' < τ := by
        have h1 : η ≤ τ / (2 * (R' + 1)) := min_le_right _ _
        have h2 : τ / (2 * (R' + 1)) * R' < τ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left (by linarith only [hR'0]) hτ
        calc η * R' ≤ τ / (2 * (R' + 1)) * R' := mul_le_mul_of_nonneg_right h1 hR'0.le
          _ < τ := h2
      have hd : dist (Φ (L z)) (L z) < τ := by
        rw [hΦL, dist_eq_norm]
        calc ‖Γ z - L z‖ ≤ η * ‖z‖ := h
          _ ≤ η * R' := mul_le_mul_of_nonneg_left hzR hη0.le
          _ < τ := hηR
      have h' := hτf hd
      rwa [Real.dist_eq] at h'
    have hfi : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ → ∀ g : Amb n ℓ → ℝ, Continuous g →
        (∀ y, |g y| ≤ Mf) → Integrable g μ := fun μ _ g hgc hgM =>
      Integrable.of_bound hgc.aestronglyMeasurable Mf
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hgM y)
    have hE1 : |∫ y, f (Φ y) ∂μ₃ - ∫ y, f y ∂μ₃| ≤ ε / (2 * (HA + 1)) * HA := by
      rw [← integral_sub (hfi μ₃ hμ₃fin (fun y => f (Φ y)) (hfc.comp hΦc) fun y => hfM _)
        (hfi μ₃ hμ₃fin _ hfc hfM)]
      have h := norm_integral_le_of_norm_le_const (μ := μ₃) (f := fun y => f (Φ y) - f y)
        (C := ε / (2 * (HA + 1)))
        ((ae_restrict_iff' hAmeas).2 (ae_of_all _ fun y hy => by
          rw [Real.norm_eq_abs]; exact (hclose y hy).le))
      rwa [Real.norm_eq_abs, hμ₃univ] at h
    have hE2 : |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| ≤ 2 * ((κ - 1) * κ * (Mf * HA)) := by
      have hpm : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ →
          ∫ y, f y ∂μ = ∫ y, max (f y) 0 ∂μ - ∫ y, max (-f y) 0 ∂μ := by
        intro μ hμ
        rw [← integral_sub]
        · congr 1
          funext y
          rw [max_zero_sub_max_neg_zero_eq_self]
        · exact hfi μ hμ _ (hfc.max continuous_const) fun y => by
            rw [abs_of_nonneg (le_max_right _ _)]
            exact max_le ((le_abs_self _).trans (hfM y)) hMf0
        · exact hfi μ hμ _ (hfc.neg.max continuous_const) fun y => by
            rw [abs_of_nonneg (le_max_right _ _)]
            exact max_le ((neg_le_abs _).trans (hfM y)) hMf0
      have e1 := hsand (fun y => max (f y) 0) (hfc.max continuous_const) (fun y => le_max_right _ _)
        fun y => max_le ((le_abs_self _).trans (hfM y)) hMf0
      have e2 := hsand (fun y => max (-f y) 0) (hfc.neg.max continuous_const)
        (fun y => le_max_right _ _) fun y => max_le ((neg_le_abs _).trans (hfM y)) hMf0
      rw [hpm μ₁ hμ₁fin, hpm μ₂ hμ₂fin]
      calc |(∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₁) -
            (∫ y, max (f y) 0 ∂μ₂ - ∫ y, max (-f y) 0 ∂μ₂)|
          = |(∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (f y) 0 ∂μ₂) -
            (∫ y, max (-f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₂)| := by congr 1; ring
        _ ≤ |∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (f y) 0 ∂μ₂| +
            |∫ y, max (-f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₂| := abs_sub _ _
        _ ≤ 2 * ((κ - 1) * κ * (Mf * HA)) := by linarith only [e1, e2]
    have hmap : ∫ y, f y ∂μ₂ = ∫ y, f (Φ y) ∂μ₃ :=
      integral_map hΦm.aemeasurable hfc.aestronglyMeasurable
    -- Conclusion.
    rw [Real.dist_eq, hNlam, show (LinearMap.range (fderiv ℝ G b).toLinearMap : Set (Amb n ℓ)) =
      (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) from rfl, hI0]
    have hX0 : 0 ≤ (κ - 1) * κ := mul_nonneg (sub_nonneg.2 hκ1) (zero_le_one.trans hκ1)
    have hX : (κ - 1) * κ * (4 * (Mf + 1) * (HA + 1)) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at hκbound
    have hMH : Mf * HA ≤ (Mf + 1) * (HA + 1) := by
      calc Mf * HA ≤ Mf * HA + (Mf + HA + 1) :=
            le_add_of_nonneg_right (by linarith only [hMf0, hHA0])
        _ = (Mf + 1) * (HA + 1) := by ring
    have hfin1 : 2 * ((κ - 1) * κ * (Mf * HA)) ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left hMH hX0
      linarith only [this, hX]
    have hfin2 : ε / (2 * (HA + 1)) * HA < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith only [hε]
    calc |∫ y, f y ∂μ₁ - ∫ y in A, f y ∂μHE[n]|
        ≤ |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| + |∫ y, f y ∂μ₂ - ∫ y in A, f y ∂μHE[n]| :=
          abs_sub_le _ _ _
      _ = |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| + |∫ y, f (Φ y) ∂μ₃ - ∫ y, f y ∂μ₃| := by
          rw [hmap]
      _ < ε := by linarith only [hE1, hE2, hfin1, hfin2]
/-- **Blow-up integrals over a set of zero `n`-density vanish** (the error estimate in Simon Ch. 3,
proof of Theorem 1.6 `⇒`): if `Hⁿ(S ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0`, then
`∫_{η_{x,r}(S)} f dHⁿ → 0` as `r ↓ 0` for every `f ∈ C_c(ℝ^{n+ℓ}, ℝ)`, where
`η_{x,r}(y) = r⁻¹(y − x)`.  No measurability or finiteness of `S` is needed.

Simon's estimate, inline (SimonGMT's `Chapter04.hausdorff_blowUp_image` is outside the frozen
import closure).  Choose `R > 0` with `f = 0` off `B_R(0)` and `C` with `|f| ≤ C`.  For `r > 0`,
`η_{x,r}` is a translation followed by the dilation by `r⁻¹`, so `Hⁿ(η_{x,r}(T)) = r⁻ⁿ Hⁿ(T)`;
since `η_{x,r}⁻¹(B_R(0)) = B_{rR}(x)`, this gives
`Hⁿ(η_{x,r}(S) ∩ B_R(0)) = r⁻ⁿ Hⁿ(S ∩ B_{rR}(x)) = Rⁿ · Hⁿ(S ∩ B_{rR}(x)) / (rR)ⁿ → 0`.  Hence
`|∫_{η_{x,r}(S)} f dHⁿ| = |∫_{B_R(0)} f d(Hⁿ ⌞ η_{x,r}(S))| ≤ C Hⁿ(η_{x,r}(S) ∩ B_R(0)) → 0`. -/
theorem aetp_blowUp_integral_tendsto_zero_of_density_zero : ∀ (n ℓ : ℕ) (x : Amb n ℓ) (S : Set (Amb n ℓ)), Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ x S hS f
  -- `f` vanishes off `B_R(0)` and `|f| ≤ C`.
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  obtain ⟨R, hRpos, hf0⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, y ∉ closedBall (0 : Amb n ℓ) R → f y = 0 :=
    ⟨max R₀ 1, zero_lt_one.trans_le (le_max_right _ _), fun y hy => by
      by_contra hfy
      exact hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ (subset_tsupport _ hfy)))⟩
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  -- Scaling: `Hⁿ(η_{x,r}(T)) = ofReal(rⁿ)⁻¹ Hⁿ(T)` for `r > 0`.
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        (ENNReal.ofReal (r ^ n))⁻¹ * (μHE[n] : Measure (Amb n ℓ)) T := by
    intro r hr T
    have h := Measure.euclideanHausdorffMeasure_smul₀ (E := Amb n ℓ) n (inv_ne_zero hr.ne')
      ((IsometryEquiv.subRight x) '' T)
    rw [← Set.image_smul, Set.image_image,
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul] at h
    refine Eq.trans h ?_
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos (pow_pos hr n), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow,
      coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_pow]
  -- Ball identity: `η_{x,r}⁻¹(B_R(0)) = B_{rR}(x)` for `r > 0`.
  have hpre : ∀ r : ℝ, 0 < r →
      Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' closedBall 0 R = closedBall x (r * R) := by
    intro r hr
    ext y
    simp only [Set.mem_preimage, mem_closedBall_iff_norm, sub_zero,
      Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_le_iff₀ hr
  -- `Hⁿ(η_{x,r}(S) ∩ B_R(0)) = ofReal(Rⁿ) · Hⁿ(S ∩ B_{rR}(x)) / ofReal((rR)ⁿ) → 0` as `r ↓ 0`.
  have hmul : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hg : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ))
      (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (hS.comp hmul) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (R ^ n))
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hR' : ENNReal.ofReal (R ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRpos n)).ne'
    rw [Function.comp_apply, ← Set.image_inter_preimage, hpre r hr, hscale r hr, mul_pow,
      ENNReal.ofReal_mul (pow_nonneg hr.le n), ← mul_div_assoc, mul_comm (ENNReal.ofReal (R ^ n)),
      ENNReal.mul_div_mul_right _ _ hR' ENNReal.ofReal_ne_top, ENNReal.div_eq_inv_mul]
  -- `|∫_{η_{x,r}(S)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(S) ∩ B_R(0))` once the latter is finite.
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂(μHE[n] : Measure (Amb n ℓ))‖ ≤
        C * ((μHE[n] : Measure (Amb n ℓ))
          (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal := by
    filter_upwards [hg.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with r hr
    have h2 : ((μHE[n] : Measure (Amb n ℓ)).restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S)) (closedBall 0 R) =
        (μHE[n] : Measure (Amb n ℓ))
          (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) := by
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf0, ← h2]
    exact norm_setIntegral_le_of_norm_le_const (h2 ▸ hr) (fun y _ => hC y)
  have hlim : Tendsto (fun r : ℝ => C * ((μHE[n] : Measure (Amb n ℓ))
      (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hg).const_mul C
  exact squeeze_zero_norm' hbound hlim
/-- **Simon Ch. 3, Remark 1.5(2) / proof of Theorem 1.6 "⇒" at a single point** (locality of the
approximate tangent space): let `A, N ⊆ ℝ^{n+ℓ}` be Borel with `Hⁿ(A), Hⁿ(N) < ∞`, such that
`A \ N` and `N \ A` both have `n`-density `0` at `x`.  If `Q` is the approximate tangent space of
`N` at `x`, then it is also the approximate tangent space of `A` at `x`.

Simon's proof, with `M ↦ A`, `N_j ↦ N`, `M_j ↦ A ∩ N`.  For `r > 0` the blow-up `η_{x,r}` is a
homeomorphism with inverse `z ↦ x + r • z` that scales `Hⁿ` by `r⁻ⁿ`.  So every `f ∈ C_c` is
integrable on the images of `A ∩ N`, `A \ N` and `N \ A`, and additivity gives
`∫_{η_r(A)} f = ∫_{η_r(N)} f - ∫_{η_r(N \ A)} f + ∫_{η_r(A \ N)} f`.  As `r ↓ 0` the first term
tends to `∫_Q f` by hypothesis, and the two error terms tend to `0` by
`aetp_blowUp_integral_tendsto_zero_of_density_zero`. -/
theorem aetp_approxTangent_of_density_zero_symmDiff : ∀ (n ℓ : ℕ) (A N : Set (Amb n ℓ)) (x : Amb n ℓ) (Q : Submodule ℝ (Amb n ℓ)), MeasurableSet A → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) A < ⊤ → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((A \ N) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((N \ A) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x Q → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x Q := by
  intro n ℓ A N x Q hA hN hAμ hNμ hAN hNA hNQ
  -- Step 1: `finrank Q = n` is part of the hypothesis on `N`; fix a test function `f`.
  refine ⟨hNQ.1, fun f => ?_⟩
  -- Step 2: `∫_{η_r(N)} f - ∫_{η_r(N \ A)} f + ∫_{η_r(A \ N)} f → ∫_Q f - 0 + 0`.
  have hlim := ((hNQ.2 f).sub
    (Submission.aetp_blowUp_integral_tendsto_zero_of_density_zero n ℓ x (N \ A) hNA f)).add
    (Submission.aetp_blowUp_integral_tendsto_zero_of_density_zero n ℓ x (A \ N) hAN f)
  rw [sub_zero, add_zero] at hlim
  -- Step 3: it suffices to prove the decomposition identity `(∗)` for each fixed `r > 0`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- Step 4: `η_r` has the continuous inverse `g z = x + r • z`, so `η_r(S) = g⁻¹(S)`: images of
  -- Borel sets are Borel, and unions and disjointness pass to images.
  set g : Amb n ℓ → Amb n ℓ := fun z => x + r • z
  have hg : Continuous g := continuous_const.add (continuous_const_smul r)
  have himg : ∀ S : Set (Amb n ℓ), Poincare.SimonGMT.Chapter03.blowUpMap x r '' S = g ⁻¹' S := by
    intro S
    refine congrFun (image_eq_preimage_of_inverse (fun y => ?_) (fun z => ?_)) S
    · simp [g, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
    · simp [g, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
  -- Step 5: `Hⁿ(η_r(T)) = r⁻ⁿ Hⁿ(T)` (an isometric translation followed by a homothety), so
  -- `η_r` preserves finiteness of `Hⁿ`.
  have hshift : Isometry fun y : Amb n ℓ => y - x := by
    apply Isometry.of_dist_eq
    intro y z
    simp only [dist_eq_norm]
    congr 1
    abel
  have hfin : ∀ T : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) T < ⊤ →
      (μHE[n] : Measure (Amb n ℓ)) (g ⁻¹' T) < ⊤ := by
    intro T hT
    have himage : g ⁻¹' T =
        AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y : Amb n ℓ => y - x) '' T) := by
      rw [← himg, ← image_comp]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hT
  -- Step 6: `f` is bounded, hence integrable on every set of finite measure.
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hint : ∀ T : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) T < ⊤ →
      IntegrableOn f (g ⁻¹' T) (μHE[n] : Measure (Amb n ℓ)) := fun T hT =>
    Measure.integrableOn_of_bounded (hfin T hT).ne f.continuous.aestronglyMeasurable
      (ae_of_all _ hC)
  have hANμ : (μHE[n] : Measure (Amb n ℓ)) (A ∩ N) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hAμ
  have hAdNμ : (μHE[n] : Measure (Amb n ℓ)) (A \ N) < ⊤ := (measure_mono sdiff_subset).trans_lt hAμ
  have hNdAμ : (μHE[n] : Measure (Amb n ℓ)) (N \ A) < ⊤ := (measure_mono sdiff_subset).trans_lt hNμ
  -- Step 7: additivity over `A = (A ∩ N) ∪ (A \ N)` and `N = (A ∩ N) ∪ (N \ A)`; eliminating
  -- `∫_{η_r(A ∩ N)} f` gives `(∗)`.
  have hAsplit : g ⁻¹' A = g ⁻¹' (A ∩ N) ∪ g ⁻¹' (A \ N) := by
    rw [← preimage_union, inter_union_sdiff]
  have hNsplit : g ⁻¹' N = g ⁻¹' (A ∩ N) ∪ g ⁻¹' (N \ A) := by
    rw [← preimage_union, inter_comm A N, inter_union_sdiff]
  simp only [himg]
  rw [hAsplit, hNsplit,
    setIntegral_union ((disjoint_sdiff_right.mono_left inter_subset_right).preimage g)
      (hg.measurable (hA.diff hN)) (hint _ hANμ) (hint _ hAdNμ),
    setIntegral_union ((disjoint_sdiff_right.mono_left inter_subset_left).preimage g)
      (hg.measurable (hN.diff hA)) (hint _ hANμ) (hint _ hNdAμ)]
  ring
/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces, from the proof of
Theorem 1.6 "⇒"): if `A, N ⊆ ℝ^{n+ℓ}` are Borel with `Hⁿ(A), Hⁿ(N) < ∞` and `P(x) = T_x N` for
every `x ∈ N`, then `P(x) = T_x A` for `Hⁿ`-a.e. `x ∈ A ∩ N`.

The Upper Density Theorem (`aetp_upper_density_zero_ae` with `ν = Hⁿ`) applied to `A \ N` and to
`N \ A` gives `Hⁿ((A \ N) ∩ B_r(x)) / rⁿ → 0` and `Hⁿ((N \ A) ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0` for
`Hⁿ`-a.e. `x` outside the respective set, hence for `Hⁿ`-a.e. `x ∈ A ∩ N`.  At such `x` the blow-ups
`η_{x,r}(A)` and `η_{x,r}(N)` differ by the images of these two sets, whose integrals vanish in the
limit, so `T_x A = T_x N = P(x)` (`aetp_approxTangent_of_density_zero_symmDiff`). -/
theorem aetp_approxTangent_ae_of_inter : ∀ (n ℓ : ℕ) (A N : Set (Amb n ℓ)) (P : Amb n ℓ → Submodule ℝ (Amb n ℓ)), MeasurableSet A → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) A < ⊤ → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → (∀ x ∈ N, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x (P x)) → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)).restrict (A ∩ N), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x (P x) := by
  intro n ℓ A N P hA hN hAfin hNfin hP
  -- Upper density zero for `A \ N` and `N \ A` (Borel, of finite `Hⁿ` measure), with `ν = Hⁿ`.
  have hAN := Submission.aetp_upper_density_zero_ae n ℓ (μHE[n]) (A \ N) (hA.diff hN)
    ((measure_mono sdiff_subset).trans_lt hAfin)
  have hNA := Submission.aetp_upper_density_zero_ae n ℓ (μHE[n]) (N \ A) (hN.diff hA)
    ((measure_mono sdiff_subset).trans_lt hNfin)
  -- A point of `A ∩ N` lies in neither `A \ N` nor `N \ A`, so both limits hold
  -- `Hⁿ ⌞ (A ∩ N)`-a.e.
  filter_upwards [ae_restrict_mem (hA.inter hN), ae_restrict_of_ae hAN, ae_restrict_of_ae hNA]
    with x hx hxAN hxNA
  -- At such `x ∈ N`, `T_x N = P(x)` transfers to `A`.
  exact Submission.aetp_approxTangent_of_density_zero_symmDiff n ℓ A N x (P x) hA hN hAfin hNfin
    (hxAN fun h => h.2 hx.2) (hxNA fun h => h.2 hx.1) (hP x hx.2)
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
/-- **Simon Ch. 3, Theorem 1.9** (with Lemma 1.2, Theorem 1.6 and Remark 1.8(1)).  For a rectifiable
`n`-varifold `V = v(M, θ)` in an open `U ⊆ ℝ^{n+ℓ}`, the approximate tangent space of `M` with
respect to `θ` exists for `μ_V`-a.e. `x`, so `V.tangentProj x` is then the orthogonal projection
onto an `n`-dimensional subspace; and `x ↦ V.tangentProj x` is `μ_V`-a.e. strongly measurable.

`M` is covered up to an `Hⁿ`-null set by embedded `C¹` pieces `N_k = G_k(B̆_{r_k}(c_k))`, whose
approximate tangent plane at `G_k(b)` is `DG_k(b)(ℝⁿ)`, and exhausted up to an `Hⁿ`-null set by
compacts `K_m` on which `θ` is continuous.  For `Hⁿ`-a.e. `x ∈ K_m ∩ N_k`, locality of approximate
tangent planes gives `T_x K_m = P_k(x) := DG_k(b_k(x))(ℝⁿ)`, and the upper density theorem (for
`μ_V` and `W ∖ K_m`, `W ⊇ K_m` open with compact closure in `U`) gives
`μ_V((M ∖ K_m) ∩ B_{Rλ}(x)) = o(λⁿ)`, so `P_k(x)` is the weighted tangent plane at `x`.  As
`μ_V ≪ Hⁿ` and `μ_V(Mᶜ) = 0`, this holds `μ_V`-a.e.; by uniqueness, `V.tangentProj = p_{P_k(·)}`
`μ_V`-a.e. on `N_k`, and `p_{P_k(·)}` is continuous on `N_k` since `b_k` is Lipschitz there. -/
theorem rectifiableVarifold_ae_tangentProj_starProjection : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ MeasureTheory.AEStronglyMeasurable V.tangentProj V.weight := by
  intro n ℓ hn U hU V
  -- Lemma 1.2: `M ⊆ Z₀ ∪ ⋃ k, N k`, `Hⁿ(Z₀) = 0`, with embedded `C¹` pieces `N k`.
  obtain ⟨Z₀, -, hZ₀, G, c, r, σ, hG, -, hσ, hDG, hlow, hcover⟩ :=
    Submission.aetp_rectifiable_c1_piece_cover n ℓ hn V.carrier V.countablyRectifiable
  set N : ℕ → Set (Amb n ℓ) := fun k => G k '' ball (c k) (r k)
  have hpiece : ∀ k, MeasurableSet (N k) ∧ (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤ ∧
      ∀ y ∈ ball (c k) (r k), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k)
        (G k y) (LinearMap.range (fderiv ℝ (G k) y).toLinearMap) := fun k =>
    Submission.aetp_c1_piece_approxTangent n ℓ (G k) (c k) (r k) (σ k) (hG k) (hσ k) (hDG k)
      (hlow k)
  -- the parameter `b k x ∈ B̆_{r_k}(c_k)` of a point `x ∈ N k`
  obtain ⟨b, hb⟩ : ∃ b : ℕ → Amb n ℓ → Rn n,
      ∀ k, ∀ x ∈ N k, b k x ∈ ball (c k) (r k) ∧ G k (b k x) = x :=
    ⟨fun k => Function.invFunOn (G k) (ball (c k) (r k)),
      fun k x hx => ⟨Function.invFunOn_mem hx, Function.invFunOn_eq hx⟩⟩
  have hNtan : ∀ k, ∀ x ∈ N k, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x
      (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap) := by
    intro k x hx
    have h := (hpiece k).2.2 (b k x) (hb k x hx).1
    rwa [(hb k x hx).2] at h
  -- Remark 1.8(1): compacts `K m ⊆ M`, with `θ` continuous on `K m`, exhaust `M` up to a null set.
  obtain ⟨K, hKc, hKM, hθK, hKfin, hKnull⟩ := Submission.aetp_lusin_compact_exhaustion n ℓ U hU V
  have hfin : ∀ L : Set (Amb n ℓ), IsCompact L → L ⊆ U → V.weight L < ⊤ := by
    intro L hL hLU
    rw [RectifiableVarifold.weight, withDensity_apply _ hL.isClosed.measurableSet,
      Measure.restrict_restrict hL.isClosed.measurableSet, inter_comm]
    exact (V.integrableOn_mult L hL hLU).lintegral_lt_top
  -- For `Hⁿ`-a.e. `x ∈ K m ∩ N k`, `DG_k(b_k(x))(ℝⁿ)` is the weighted tangent plane at `x`.
  have hloc : ∀ m k, ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ K m → x ∈ N k →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap) := by
    intro m k
    obtain ⟨L, hLc, hKL, hLU⟩ :=
      exists_compact_between (hKc m) hU ((hKM m).trans V.carrier_subset)
    have hA : MeasurableSet (interior L \ K m) :=
      isOpen_interior.measurableSet.diff (hKc m).isClosed.measurableSet
    have hAL : interior L \ K m ⊆ L := fun y hy => interior_subset hy.1
    have hAfin : V.weight (interior L \ K m) < ⊤ := (measure_mono hAL).trans_lt (hfin L hLc hLU)
    have htan := Submission.aetp_approxTangent_ae_of_inter n ℓ (K m) (N k)
      (fun x => LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)
      (hKc m).isClosed.measurableSet (hpiece k).1 (hKfin m) (hpiece k).2.1 (hNtan k)
    rw [ae_restrict_iff' ((hKc m).isClosed.measurableSet.inter (hpiece k).1)] at htan
    filter_upwards [htan, Submission.aetp_upper_density_zero_ae n ℓ V.weight _ hA hAfin]
      with x hxtan hxdens hxK hxN
    refine Submission.aetp_weightedTangent_of_lusin_compact n ℓ U hU V (K m) x _ (hKc m) (hKM m)
      hxK (hθK m) (fun R hR => ?_) (hxtan ⟨hxK, hxN⟩)
    -- `μ_V((M ∖ K m) ∩ B_{Rt}(x)) ≤ μ_V((W ∖ K m) ∩ B_{Rt}(x)) = o(tⁿ)`, `W = interior L`
    have hd := hxdens fun h => h.2 hxK
    have hRr : Tendsto (fun t : ℝ => R * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2
        ⟨?_, eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => mul_pos hR ht⟩
      have h0 : Tendsto (fun t : ℝ => R * t) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hsub : ∀ᶠ t in 𝓝[>] (0 : ℝ), closedBall x (R * t) ⊆ interior L :=
      (hRr.mono_right nhdsWithin_le_nhds).eventually
        (eventually_closedBall_subset (isOpen_interior.mem_nhds (hKL hxK)))
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (R ^ n) *
        (V.weight ((interior L \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal ((R * t) ^ n)))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hd.comp hRr)
        (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ n) ≠ ⊤))
      rw [mul_zero] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hsub] with t ht
    have hMA : (V.carrier \ K m) ∩ closedBall x (R * t) ⊆
        (interior L \ K m) ∩ closedBall x (R * t) := fun y hy => ⟨⟨ht hy.2, hy.1.2⟩, hy.2⟩
    calc V.weight ((V.carrier \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal (t ^ n)
        ≤ V.weight ((interior L \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal (t ^ n) :=
          ENNReal.div_le_div_right (measure_mono hMA) _
      _ = ENNReal.ofReal (R ^ n) * (V.weight ((interior L \ K m) ∩ closedBall x (R * t)) /
            ENNReal.ofReal ((R * t) ^ n)) := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hR.le n), ENNReal.div_eq_inv_mul,
            ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
              (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (pow_pos hR n)).ne'
              ENNReal.ofReal_ne_top, one_mul]
  -- Off an `Hⁿ`-null set, each `x ∈ M` lies in some `N k`, and for every `k` with `x ∈ N k` the
  -- plane `DG_k(b_k(x))(ℝⁿ)` is the weighted tangent plane at `x`.
  have hgoodH : ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ V.carrier →
      (∀ k, x ∈ N k → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult x (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)) ∧
      ∃ k, x ∈ N k := by
    filter_upwards [ae_all_iff.2 fun m => ae_all_iff.2 fun k => hloc m k,
      measure_eq_zero_iff_ae_notMem.1 hZ₀, measure_eq_zero_iff_ae_notMem.1 hKnull]
      with x hx hxZ hxK hxM
    obtain ⟨m, hm⟩ : ∃ m, x ∈ K m := by
      by_contra h
      exact hxK ⟨hxM, fun h' => h (mem_iUnion.1 h')⟩
    refine ⟨fun k hk => hx m k hm hk, ?_⟩
    rcases hcover hxM with h | h
    · exact absurd h hxZ
    · exact mem_iUnion.1 h
  -- `μ_V ≪ Hⁿ` and `μ_V(Mᶜ) = 0`
  have hμM : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hμH : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)) :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hgood : ∀ᵐ x ∂V.weight, x ∈ V.carrier ∧
      (∀ k, x ∈ N k → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult x (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)) ∧
      ∃ k, x ∈ N k := by
    filter_upwards [hμH.ae_le hgoodH, hμM] with x hx hxM
    exact ⟨hxM, hx hxM⟩
  -- A weighted tangent plane at `x ∈ M` is unique (`θ(x) > 0`), so it is the one in `tangentProj`.
  have hproj : ∀ x (Q : Submodule ℝ (Amb n ℓ)), x ∈ V.carrier →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x Q →
      V.tangentProj x = Q.starProjection := by
    intro x Q hxM hQ
    have h : ∃ P, Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult x P := ⟨Q, hQ⟩
    have hP : ∀ (A B : Submodule ℝ (Amb n ℓ)) [A.HasOrthogonalProjection]
        [B.HasOrthogonalProjection], A = B → A.starProjection = B.starProjection := by
      rintro A B _ _ rfl
      rfl
    rw [RectifiableVarifold.tangentProj, dite_eq_left h]
    exact hP _ _ (Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
      (V.mult_pos x hxM).ne' (Classical.choose_spec h) hQ)
  refine ⟨?_, ?_⟩
  · filter_upwards [hgood] with x hx
    obtain ⟨hxM, hW, k, hk⟩ := hx
    exact ⟨_, (hW k hk).1, hproj x _ hxM (hW k hk)⟩
  · -- `μ_V`-a.e. `x` lies in `⋃ k, N k`; on `N k`, `V.tangentProj = p_{DG_k(b_k(·))(ℝⁿ)}`
    -- `μ_V`-a.e., a map continuous on `N k`.
    have hcov : ∀ᵐ x ∂V.weight, x ∈ ⋃ k, N k := by
      filter_upwards [hgood] with x hx
      exact mem_iUnion.2 hx.2.2
    rw [← Measure.restrict_eq_self_of_ae_mem hcov, aestronglyMeasurable_iUnion_iff]
    intro k
    have hlip : LipschitzOnWith (Real.toNNReal (σ k)⁻¹) (b k) (N k) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have h := hlow k (b k x) (hb k x hx).1 (b k y) (hb k y hy).1
      rw [(hb k x hx).2, (hb k y hy).2] at h
      rw [Real.coe_toNNReal _ (inv_nonneg.2 (hσ k).le), dist_eq_norm, dist_eq_norm,
        inv_mul_eq_div, le_div_iff₀ (hσ k), mul_comm]
      exact h
    have hcont : ContinuousOn
        (fun x => (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap).starProjection) (N k) :=
      (Submission.aetp_starProjection_range_continuousOn n ℓ).comp
        (((hG k).continuous_fderiv one_ne_zero).comp_continuousOn hlip.continuousOn)
        fun x hx => hDG k (b k x) (hb k x hx).1
    refine (hcont.aestronglyMeasurable (hpiece k).1).congr ((ae_restrict_iff' (hpiece k).1).2 ?_)
    filter_upwards [hgood] with x hx hxN
    exact (hproj x _ hx.1 (hx.2.1 k hxN)).symm
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): a cutoff `ζ ∈ C^∞(ℝᵐ)` with `0 ≤ ζ ≤ 1`, `ζ ≡ 1` on
`B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B̆_ρ(ξ)` and `|Dζ| ≤ 3/ρ`.  Take `ζ(x) = φ(|x − ξ|/ρ)` for the smooth
`3`-Lipschitz step profile `φ` (`φ = 1` on `(-∞, 1/2]`, `φ = 0` on `[1, ∞)`): `ζ` is smooth since it
is constant near `ξ`, and the radial lift of a `3`-Lipschitz profile has `|Dζ| ≤ 3/ρ`. -/
theorem exists_smooth_cutoff_half_ball_grad_le : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Metric.closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ :=
    Submission.exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    Submission.contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ_smooth hφ_one,
    fun x => hφ_bounds _, fun x hx => hφ_one _ ?_, fun x hx => hφ_zero _ ?_, fun x => ?_⟩
  · -- `|x − ξ| ≤ ρ/2`, so `|x − ξ|/ρ ≤ 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ |x − ξ|`, so `1 ≤ |x − ξ|/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- The profile is `3`-Lipschitz, so `|Dζ(x)| ≤ 3/ρ`.
    have h := Submission.norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφ_lip x
    rwa [NNReal.coe_ofNat] at h
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
/-- Simon Ch. 5, proof of Lemma 2.1, (1)–(3) (p. 107): if `T_x V = P` and `P`, `T` are
`n`-dimensional, the height test field `X(y) = ζ(y)² p_{T⊥}(y − ξ)` has tangential divergence
`div_M X(x) = ζ(x)² |p_P − p_T|²/2 + 2ζ(x) Dζ(x)((p_P − p_T) p_{T⊥}(x − ξ))`
(`|·|` the Hilbert–Schmidt norm). -/
theorem divM_height_test_field_eq (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U)
    (ζ : Amb n ℓ → ℝ) (ξ x : Amb n ℓ) (P T : Submodule ℝ (Amb n ℓ))
    (hζ : DifferentiableAt ℝ ζ x) (hP : Module.finrank ℝ P = n) (hT : Module.finrank ℝ T = n)
    (hV : V.tangentProj x = P.starProjection) :
    V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - ξ)) x =
      ζ x ^ 2 * (hsNormSq (P.starProjection - T.starProjection) / 2) +
        2 * ζ x * fderiv ℝ ζ x
          ((P.starProjection - T.starProjection) (Tᗮ.starProjection (x - ξ))) := by
  -- `DX(x) = ζ(x)² p_{T⊥} + (2ζ(x) Dζ(x)).smulRight x'` with `x' = p_{T⊥}(x − ξ)`.
  have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - ξ)) Tᗮ.starProjection x :=
    (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const ξ)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have hX := hsq.fun_smul hlin
  -- `x' ∈ T⊥`, so `p_T x' = 0`.
  have hx' : T.starProjection (Tᗮ.starProjection (x - ξ)) = 0 :=
    (T.starProjection_apply_eq_zero_iff).mpr (Tᗮ.starProjection_apply_mem _)
  -- Projection algebra (iii), as `dim P = dim T`: `trace(p_{T⊥} ∘ p_P) = |p_P − p_T|²/2`.
  have htr : LinearMap.trace ℝ (Amb n ℓ)
      (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        hsNormSq (P.starProjection - T.starProjection) / 2 :=
    Submission.hsNorm_starProjection_trace_identities.2.2 (n + ℓ) P T (hP.trans hT.symm)
  -- The rank-one part: `(φ.smulRight x') ∘ p_P = (φ ∘ p_P).smulRight x'`.
  have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - ξ))).toLinearMap ∘ₗ
      P.starProjection.toLinearMap =
        (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
          (Tᗮ.starProjection (x - ξ)) := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
  rw [RectifiableVarifold.divM, hX.fderiv, hV, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
    map_smul, htr, LinearMap.trace_smulRight]
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, smul_apply,
    smul_eq_mul, sub_apply, hx', sub_zero]
/-- **Simon Ch. 5, Lemma 2.1** (tilt-excess/height estimate), with `C = 146 · 2^(n+1)`.

Test the first variation with `X = ζ² p_{T⊥}(x - ξ)`, where `ζ` is a cutoff equal to `1` on
`B_{ρ/2}(ξ)` and vanishing off `B̆_ρ(ξ)`; then absorb the drift term by Young's inequality. -/
theorem tilt_excess_height_estimate : TiltExcessHeightEstimate := by
  intro n hn
  refine ⟨146 * 2 ^ (n + 1), ?_⟩
  intro ℓ U hU V H hH ξ ρ hρ hBU T hT
  -- Step 1: if `∫_{B_ρ(ξ)} |H|² dμ_V = ∞`, the right-hand side is `∞`.
  by_cases hHinf : ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight = ∞
  · have hc : (0 : ℝ) < 146 * 2 ^ (n + 1) * ρ ^ ((2 : ℝ) - n) := by positivity
    rw [hHinf, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne', add_top]
    exact le_top
  have hHfin : ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight < ∞ := lt_top_iff_ne_top.2 hHinf
  -- The prerequisites: a.e. tangent planes, the cutoff, and the projection algebra.
  obtain ⟨hae, hmeas⟩ :=
    Submission.rectifiableVarifold_ae_tangentProj_starProjection n ℓ hn U hU V
  obtain ⟨ζ, hζs, hζ01, hζ1, hζ0, hζd⟩ : ∃ ζ : Amb n ℓ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall ξ (ρ / 2), ζ x = 1) ∧
      (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ :=
    Submission.exists_smooth_cutoff_half_ball_grad_le (n + ℓ) ξ ρ hρ
  have hopHS : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, ‖A‖ ≤ hsNorm A := fun A =>
    Submission.hsNorm_starProjection_trace_identities.1 (n + ℓ) (n + ℓ) A
  have hperp : ∀ v : Amb n ℓ, ‖Tᗮ.starProjection v‖ = infDist v (T : Set (Amb n ℓ)) :=
    fun v => Submission.hsNorm_starProjection_trace_identities.2.1 (n + ℓ) T v
  -- Notation: `g = |p_x - p_T|²`, `w = x' = p_{T⊥}(x - ξ)`, the drift term `b`, the field `X`.
  obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ, ∀ x, g x = hsNormSq (V.tangentProj x - T.starProjection) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → Amb n ℓ, ∀ x, w x = Tᗮ.starProjection (x - ξ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Amb n ℓ → ℝ,
      ∀ x, b x = 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, ∀ x, X x = ζ x ^ 2 • w x := ⟨_, fun _ => rfl⟩
  -- Pointwise facts.
  have hζC1 : ContDiff ℝ 1 ζ := hζs.of_le (by exact_mod_cast le_top)
  have hζcont : Continuous ζ := hζC1.continuous
  have hDζcont : Continuous (fderiv ℝ ζ) := hζC1.continuous_fderiv one_ne_zero
  have hwcont : Continuous w := by
    rw [show w = fun x => Tᗮ.starProjection (x - ξ) from funext hw]
    fun_prop
  have hXcont : Continuous X := by
    rw [show X = fun x => ζ x ^ 2 • w x from funext hX]
    exact (hζcont.pow 2).smul hwcont
  have hζout : ∀ x, x ∉ closedBall ξ ρ → ζ x = 0 := fun x hx =>
    hζ0 x (not_le.1 fun h => hx (mem_closedBall.2 h)).le
  have hw_le : ∀ x, ‖w x‖ ≤ ‖x - ξ‖ := by
    intro x
    rw [hw]
    calc ‖Tᗮ.starProjection (x - ξ)‖ ≤ ‖Tᗮ.starProjection‖ * ‖x - ξ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - ξ‖ := by gcongr; exact Submodule.starProjection_norm_le _
      _ = ‖x - ξ‖ := one_mul _
  have hwB : ∀ x ∈ closedBall ξ ρ, ‖w x‖ ≤ ρ := fun x hx =>
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
  -- `μ_V(B_ρ(ξ)) < ∞` (integrability of `θ` on compact subsets of `U`).
  have hμB : V.weight (closedBall ξ ρ) < ∞ := by
    have hint := V.integrableOn_mult (closedBall ξ ρ) (isCompact_closedBall ξ ρ) hBU
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hint.lintegral_lt_top
  have : IsFiniteMeasure (V.weight.restrict (closedBall ξ ρ)) :=
    isFiniteMeasure_restrict.2 hμB.ne
  -- Measurability.
  have hPm : AEStronglyMeasurable (fun x => V.tangentProj x - T.starProjection)
      (V.weight.restrict (closedBall ξ ρ)) :=
    hmeas.restrict.sub aestronglyMeasurable_const
  have hgm : AEStronglyMeasurable g (V.weight.restrict (closedBall ξ ρ)) := by
    rw [show g = fun x => hsNormSq (V.tangentProj x - T.starProjection) from funext hg]
    have hcont : Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq A := by
      unfold hsNormSq
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).norm).pow 2
    exact hcont.comp_aestronglyMeasurable hPm
  have hbm : AEStronglyMeasurable b (V.weight.restrict (closedBall ξ ρ)) := by
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
  -- Integrability on `B_ρ(ξ)`; `H ∈ L²(μ_V ⌞ B_ρ(ξ))` since the `|H|²` integral is finite.
  have hHint : Integrable H (V.weight.restrict (closedBall ξ ρ)) :=
    hH.1.integrableOn_compact_subset hBU (isCompact_closedBall ξ ρ)
  have hzg : Integrable (fun x => ζ x ^ 2 * g x) (V.weight.restrict (closedBall ξ ρ)) := by
    refine Integrable.of_bound ((hζcont.pow 2).aestronglyMeasurable.mul hgm) ((n + ℓ : ℕ) * 4)
      (ae_of_all _ fun x => ?_)
    obtain ⟨hz0, hz1⟩ := hζ01 x
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
    calc ζ x ^ 2 * g x ≤ 1 * ((n + ℓ : ℕ) * 4) :=
          mul_le_mul (by nlinarith) (hgle x) (hg0 x) zero_le_one
      _ = (n + ℓ : ℕ) * 4 := one_mul _
  have hbi : Integrable b (V.weight.restrict (closedBall ξ ρ)) := by
    refine Integrable.of_bound hbm 12
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hD : ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖ ≤ 3 / ρ * (2 * ρ) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hA2 x) (hwB x hx) (norm_nonneg _) zero_le_two)
    rw [hb, norm_mul, norm_mul, Real.norm_of_nonneg hz0, Real.norm_of_nonneg zero_le_two]
    calc 2 * ζ x * ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖
        ≤ 2 * 1 * (3 / ρ * (2 * ρ)) := by gcongr
      _ = 12 := by field_simp; norm_num
  have hh2 : Integrable (fun x => ‖w x‖ ^ 2) (V.weight.restrict (closedBall ξ ρ)) := by
    refine Integrable.of_bound (hwcont.norm.pow 2).aestronglyMeasurable (ρ ^ 2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwB x hx) 2
  have hk2 : Integrable (fun x => ‖H x‖ ^ 2) (V.weight.restrict (closedBall ξ ρ)) := by
    refine ⟨hHint.aestronglyMeasurable.norm.pow 2, ?_⟩
    simp only [HasFiniteIntegral, enorm_pow, enorm_norm]
    exact hHfin
  have hXH : Integrable (fun x => inner ℝ (X x) (H x)) (V.weight.restrict (closedBall ξ ρ)) := by
    refine Integrable.mono' (hHint.norm.const_mul ρ)
      (continuous_inner.comp_aestronglyMeasurable
        (hXcont.aestronglyMeasurable.prodMk hHint.aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * ρ := mul_le_mul hz2 (hwB x hx) (norm_nonneg _) zero_le_one
      _ = ρ := one_mul _
  -- Step 2: the test field `X = ζ² x'` is admissible.
  have hX1 : ContDiff ℝ 1 X := by
    rw [show X = fun x => ζ x ^ 2 • Tᗮ.starProjection (x - ξ) from funext fun x => by
      rw [hX, hw]]
    exact (hζC1.pow 2).smul ((Tᗮ.starProjection).contDiff.comp (contDiff_id.sub contDiff_const))
  have hXout : ∀ x, x ∉ closedBall ξ ρ → X x = 0 := fun x hx => by
    rw [hX, hζout x hx]
    simp
  have hXcs : HasCompactSupport X := HasCompactSupport.intro (isCompact_closedBall ξ ρ) hXout
  have hXts : tsupport X ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hBU
    by_contra h
    exact hx (hXout x h)
  -- Step 3: `div_M X = ζ² |p_x - p_T|²/2 + 2ζ ∇ζ · (p_x - p_T) x'` at a.e. point.
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = 1 / 2 * (ζ x ^ 2 * g x) + b x := by
    filter_upwards [hae] with x hx
    obtain ⟨P, hP, hPx⟩ := hx
    rw [show X = fun y => ζ y ^ 2 • Tᗮ.starProjection (y - ξ) from funext fun y => by
      rw [hX, hw]]
    rw [Submission.divM_height_test_field_eq n ℓ U V ζ ξ x P T
      (hζC1.differentiable one_ne_zero x) hP hT hPx, hg, hb, hw, hPx]
    ring
  -- Step 4: the first variation identity, localized to `B_ρ(ξ)`.
  have hFV := hH.2 X hX1 hXcs hXts
  have hL : ∫ x, V.divM X x ∂V.weight =
      ∫ x in closedBall ξ ρ, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight := by
    rw [integral_congr_ae hdiv]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [hb, hζout x hx]
    ring
  have hR : ∫ x, inner ℝ (X x) (H x) ∂V.weight =
      ∫ x in closedBall ξ ρ, inner ℝ (X x) (H x) ∂V.weight :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hXout x hx, inner_zero_left]).symm
  -- Step 5: Young's inequality for the drift term and for the mean curvature term.
  have hb_bd : ∀ x, -b x ≤ 1 / 4 * (ζ x ^ 2 * g x) + 36 / ρ ^ 2 * ‖w x‖ ^ 2 := by
    intro x
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hsq : Real.sqrt (g x) ^ 2 = g x := Real.sq_sqrt (hg0 x)
    have hD : |fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))| ≤
        3 / ρ * (Real.sqrt (g x) * ‖w x‖) := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [hg]
      exact hopHS _
    have h1 : -b x ≤ 2 * ζ x * (3 / ρ * (Real.sqrt (g x) * ‖w x‖)) := by
      rw [hb]
      calc -(2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)))
          = 2 * ζ x * -fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) := by ring
        _ ≤ 2 * ζ x * (3 / ρ * (Real.sqrt (g x) * ‖w x‖)) :=
          mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hD) (by positivity)
    have e : 1 / 4 * (ζ x ^ 2 * g x) + 36 / ρ ^ 2 * ‖w x‖ ^ 2 -
        2 * ζ x * (3 / ρ * (Real.sqrt (g x) * ‖w x‖)) =
        (ζ x * Real.sqrt (g x) / 2 - 6 / ρ * ‖w x‖) ^ 2 := by
      linear_combination (-(1 / 4) * ζ x ^ 2) * hsq
    linarith [sq_nonneg (ζ x * Real.sqrt (g x) / 2 - 6 / ρ * ‖w x‖)]
  have hXH_bd : ∀ x, -inner ℝ (X x) (H x) ≤
      1 / 2 / ρ ^ 2 * ‖w x‖ ^ 2 + ρ ^ 2 / 2 * ‖H x‖ ^ 2 := by
    intro x
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    have h1 : -inner ℝ (X x) (H x) ≤ ‖w x‖ * ‖H x‖ := by
      refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
      gcongr
      rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
      calc ζ x ^ 2 * ‖w x‖ ≤ 1 * ‖w x‖ := mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
        _ = ‖w x‖ := one_mul _
    have e : 1 / 2 / ρ ^ 2 * ‖w x‖ ^ 2 + ρ ^ 2 / 2 * ‖H x‖ ^ 2 - ‖w x‖ * ‖H x‖ =
        (‖w x‖ / ρ - ρ * ‖H x‖) ^ 2 / 2 := by
      field_simp
      ring
    linarith [sq_nonneg (‖w x‖ / ρ - ρ * ‖H x‖)]
  have e1 : ∫ x in closedBall ξ ρ, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight =
      1 / 2 * ∫ x in closedBall ξ ρ, ζ x ^ 2 * g x ∂V.weight +
        ∫ x in closedBall ξ ρ, b x ∂V.weight := by
    rw [integral_add (hzg.const_mul _) hbi, integral_const_mul]
  have e2 : -∫ x in closedBall ξ ρ, b x ∂V.weight ≤
      1 / 4 * ∫ x in closedBall ξ ρ, ζ x ^ 2 * g x ∂V.weight +
        36 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight := by
    have h := integral_mono hbi.neg ((hzg.const_mul (1 / 4)).add (hh2.const_mul (36 / ρ ^ 2)))
      hb_bd
    simp only [Pi.neg_apply, Pi.add_apply] at h
    rwa [integral_neg, integral_add (hzg.const_mul _) (hh2.const_mul _), integral_const_mul,
      integral_const_mul] at h
  have e3 : -∫ x in closedBall ξ ρ, inner ℝ (X x) (H x) ∂V.weight ≤
      1 / 2 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight +
        ρ ^ 2 / 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight := by
    have h := integral_mono hXH.neg
      ((hh2.const_mul (1 / 2 / ρ ^ 2)).add (hk2.const_mul (ρ ^ 2 / 2))) hXH_bd
    simp only [Pi.neg_apply, Pi.add_apply] at h
    rwa [integral_neg, integral_add (hh2.const_mul _) (hk2.const_mul _), integral_const_mul,
      integral_const_mul] at h
  have key : ∫ x in closedBall ξ ρ, ζ x ^ 2 * g x ∂V.weight ≤
      146 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight +
        2 * ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight := by
    have hid := hFV
    rw [hL, hR, e1] at hid
    have r1 : 146 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight =
        4 * (36 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) +
          4 * (1 / 2 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) := by ring
    have r2 : 2 * ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight =
        4 * (ρ ^ 2 / 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight) := by ring
    linarith
  -- Step 6: `ζ = 1` on `B_{ρ/2}(ξ)`.
  have hB2 : ∫ x in closedBall ξ (ρ / 2), g x ∂V.weight ≤
      ∫ x in closedBall ξ ρ, ζ x ^ 2 * g x ∂V.weight := by
    calc ∫ x in closedBall ξ (ρ / 2), g x ∂V.weight
        = ∫ x in closedBall ξ (ρ / 2), ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [hζ1 x hx]; ring
      _ ≤ ∫ x in closedBall ξ ρ, ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_mono_set hzg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hg0 x))
            (closedBall_subset_closedBall (by linarith)).eventuallyLE
  -- Step 7: rescale and pass to `ℝ≥0∞`.
  have hIk0 : 0 ≤ ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight :=
    integral_nonneg fun x => sq_nonneg _
  have hId : ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight =
      (∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) / ρ ^ 2 := by
    rw [← integral_div]
    congr 1
    funext x
    rw [hw, hperp, div_pow]
  have hk : ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight =
      ENNReal.ofReal (∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight) := by
    rw [ofReal_integral_eq_lintegral_ofReal hk2 (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hrpow : ρ ^ ((2 : ℝ) - n) = ρ ^ 2 / ρ ^ n := by
    rw [Real.rpow_sub hρ, Real.rpow_two, Real.rpow_natCast]
  have hreal : V.tiltExcess ξ (ρ / 2) T ≤
      146 * 2 ^ (n + 1) * (ρ ^ n)⁻¹ *
          ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight +
        146 * 2 ^ (n + 1) * ρ ^ ((2 : ℝ) - n) *
          ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight := by
    have hG := hB2.trans key
    have h2n : ((ρ / 2) ^ n)⁻¹ = 2 ^ n / ρ ^ n := by rw [div_pow, inv_div]
    rw [RectifiableVarifold.tiltExcess, h2n, hId, hrpow]
    simp_rw [← hg]
    calc 2 ^ n / ρ ^ n * ∫ x in closedBall ξ (ρ / 2), g x ∂V.weight
        ≤ 2 ^ n / ρ ^ n * (146 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight +
            2 * ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight) := by gcongr
      _ ≤ 146 * 2 ^ (n + 1) * (ρ ^ n)⁻¹ *
            ((∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) / ρ ^ 2) +
          146 * 2 ^ (n + 1) * (ρ ^ 2 / ρ ^ n) *
            ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight := by
        have h0 : 0 ≤ 2 ^ n / ρ ^ n *
            (146 * ((∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) / ρ ^ 2) +
              290 * (ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight)) := by positivity
        have e : 146 * 2 ^ (n + 1) * (ρ ^ n)⁻¹ *
              ((∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) / ρ ^ 2) +
            146 * 2 ^ (n + 1) * (ρ ^ 2 / ρ ^ n) * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight -
            2 ^ n / ρ ^ n * (146 / ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight +
              2 * ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight) =
            2 ^ n / ρ ^ n *
              (146 * ((∫ x in closedBall ξ ρ, ‖w x‖ ^ 2 ∂V.weight) / ρ ^ 2) +
                290 * (ρ ^ 2 * ∫ x in closedBall ξ ρ, ‖H x‖ ^ 2 ∂V.weight)) := by
          ring
        linarith
  have hC0 : 0 ≤ 146 * 2 ^ (n + 1) * ρ ^ ((2 : ℝ) - n) := by positivity
  have hT0 : 0 ≤ 146 * 2 ^ (n + 1) * (ρ ^ n)⁻¹ *
      ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight :=
    mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  rw [hk, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add hT0 (mul_nonneg hC0 hIk0)]
  exact ENNReal.ofReal_le_ofReal hreal
/-- **`Hⁿ ⌞ P` on balls about `0`** (the normalization `Hⁿ = Lⁿ` on `n`-planes, Simon's Notation
p. ix, with scaling).  If `P ⊆ ℝ^{n+ℓ}` is an `n`-dimensional subspace and `s ≥ 0`, then
`Hⁿ(P ∩ B_s(0)) = ω_n sⁿ`.  The inclusion `P → ℝ^{n+ℓ}` is an isometry, so `Hⁿ ⌞ P` is the image
of `Hⁿ` on `P`, which is Lebesgue measure of the `n`-dimensional inner product space `P`; there
`|B_s(0)| = sⁿ |B_1(0)|`.  Mathlib's value of `|B_1(0)|` lies outside the frozen import closure, so
it is computed here by evaluating `I = ∫_P e^{-|x|²} dx` twice: in orthonormal coordinates
`I = (∫_ℝ e^{-t²} dt)ⁿ = π^{n/2}` (Fubini), while the layer-cake formula with
`{e^{-|x|²} > t} = B_{√(-log t)}(0)` and the substitution `t = e^{-u}` give
`I = |B_1(0)| ∫_0^∞ u^{n/2} e^{-u} du = |B_1(0)| Γ(n/2 + 1)`. -/
theorem rsod_planeMeasure_closedBall : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (P : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ P = n → ∀ s : ℝ, 0 ≤ s → ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) (closedBall 0 s) = ENNReal.ofReal (unitBallVolume n * s ^ n) := by
  intro n ℓ hn P hP s hs
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- `Hⁿ ⌞ P` is the image of `Hⁿ` on `P` under the isometric inclusion `ι : P → ℝ^{n+ℓ}`, and
  -- `ι⁻¹(B_s(0))` is the closed ball `B_s(0)` of `P`.
  have hrange : range (P.subtypeₗᵢ : P → Amb n ℓ) = (P : Set (Amb n ℓ)) := by ext x; simp
  rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
    Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
  have hpre : (P.subtypeₗᵢ : P → Amb n ℓ) ⁻¹' closedBall (0 : Amb n ℓ) s =
      closedBall (0 : P) s := by
    ext x; simp [mem_closedBall, dist_eq_norm]
  -- On the `n`-dimensional inner product space `P`, `Hⁿ` is Lebesgue measure.
  have hvol : (μHE[n] : Measure P) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P); rwa [hP] at h
  -- `∫_ℝ e^{-t²} dt = √π`.
  have hA : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) = ENNReal.ofReal (√Real.pi) := by
    have h := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at h
    rw [← h, ofReal_integral_eq_lintegral_ofReal]
    · simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
    · exact ae_of_all _ (fun x => (Real.exp_pos _).le)
  -- Fubini, splitting off the first coordinate: `∫_{ℝᵐ} e^{-|y|²} dy = (√π)ᵐ`.
  have hB : ∀ m : ℕ, ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-∑ i, x i ^ 2)) =
      ENNReal.ofReal (√Real.pi) ^ m := by
    intro m
    induction m with
    | zero => simp [volume_pi]
    | succ m ih =>
      have e := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      have hf : Measurable fun p : ℝ × (Fin m → ℝ) =>
          ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)) := by
        fun_prop
      calc ∫⁻ x : Fin (m + 1) → ℝ, ENNReal.ofReal (Real.exp (-∑ i, x i ^ 2))
          = ∫⁻ x : Fin (m + 1) → ℝ, (fun p : ℝ × (Fin m → ℝ) =>
              ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)))
                (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 x) := by
            refine lintegral_congr fun x => ?_
            simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add]
            rfl
        _ = ∫⁻ p : ℝ × (Fin m → ℝ), ENNReal.ofReal (Real.exp (-p.1 ^ 2)) *
              ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)) := e.lintegral_comp hf
        _ = (∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-a ^ 2))) *
              ∫⁻ y : Fin m → ℝ, ENNReal.ofReal (Real.exp (-∑ i, y i ^ 2)) :=
            lintegral_prod_mul (f := fun a : ℝ => ENNReal.ofReal (Real.exp (-a ^ 2)))
              (g := fun y : Fin m → ℝ => ENNReal.ofReal (Real.exp (-∑ i, y i ^ 2)))
              (by fun_prop) (Measurable.aemeasurable (by fun_prop))
        _ = ENNReal.ofReal (√Real.pi) ^ (m + 1) := by rw [hA, ih, pow_succ']
  -- In orthonormal coordinates on `P`: `∫_P e^{-|x|²} dx = (√π)^{dim P}`.
  have hC : ∫⁻ x : P, ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
      ENNReal.ofReal (√Real.pi) ^ Module.finrank ℝ P := by
    have e := (PiLp.volume_preserving_ofLp (Fin (Module.finrank ℝ P))).comp
      (stdOrthonormalBasis ℝ P).measurePreserving_repr
    rw [← hB, ← e.lintegral_comp (by fun_prop)]
    refine lintegral_congr fun x => ?_
    rw [← (stdOrthonormalBasis ℝ P).repr.norm_map x, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  -- `t = e^{-u}`: `∫_0^∞ (√(-log t))^{dim P} dt = ∫_0^∞ u^{dim P/2} e^{-u} du = Γ(dim P/2 + 1)`.
  have hE : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(-Real.log t) ^ Module.finrank ℝ P) =
      ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1)) := by
    have himg : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
      rw [image_univ]; ext t; simp only [mem_range, mem_Ioi]
      constructor
      · rintro ⟨u, rfl⟩; exact Real.exp_pos _
      · intro ht; exact ⟨-Real.log t, by rw [neg_neg, Real.exp_log ht]⟩
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun u _ => (hasDerivAt_neg u).exp.hasDerivWithinAt)
        (fun u _ v _ h => by simpa using h), Measure.restrict_univ]
    simp only [mul_neg, mul_one, abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    rw [Real.Gamma_eq_integral (by positivity), ofReal_integral_eq_lintegral_ofReal
      (Real.GammaIntegral_convergent (by positivity))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
        have : 0 < u := hu
        positivity)]
    rw [← setLIntegral_eq_of_support_subset (s := Ioi 0)]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu : 0 < u := hu
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hu.le]
      congr 3
      ring
    · intro u hu
      by_contra h
      simp only [mem_Ioi, not_lt] at h
      apply hu
      simp [Real.sqrt_eq_zero'.2 h, zero_pow (by omega : Module.finrank ℝ P ≠ 0)]
  -- Layer cake: `{x ∈ P : e^{-|x|²} > t}` is the ball `B_{√(-log t)}(0)` of `P`.
  have hD : ∫⁻ x : P, ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
      ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1)) * volume (ball (0 : P) 1) := by
    rw [lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun x => (Real.exp_pos _).le)
      (by fun_prop), ← hE, ← lintegral_mul_const _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : 0 < t := ht
    have hset : {a : P | t < Real.exp (-‖a‖ ^ 2)} = ball (0 : P) √(-Real.log t) := by
      ext a
      rw [mem_ofPred_eq, mem_ball_zero_iff, ← Real.log_lt_iff_lt_exp ht,
        Real.lt_sqrt (norm_nonneg _)]
      constructor <;> intro h <;> linarith
    rw [hset, Measure.addHaar_ball volume 0 (Real.sqrt_nonneg _)]
  -- Hence `|B_1(0)| = (√π)ⁿ / Γ(n/2 + 1) = π^{n/2} / Γ(n/2 + 1) = ω_n`.
  have hΓ : 0 < Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hω : unitBallVolume n = √Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
    unfold unitBallVolume
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    ring
  have hball : volume (ball (0 : P) 1) = ENNReal.ofReal (unitBallVolume n) := by
    rw [hP] at hC hD hΓ
    rw [hω, ENNReal.ofReal_div_of_pos hΓ,
      ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hΓ).ne' ENNReal.ofReal_ne_top, ← hD, hC,
      ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  rw [hpre, hvol, Measure.addHaar_closedBall volume (0 : P) hs, hball, hP,
    ← ENNReal.ofReal_mul (pow_nonneg hs n), mul_comm]
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
set_option maxHeartbeats 10000000 in
/-- **Simon Ch. 3, Theorem 1.9 (⇒) with Remark 1.8(1)** (fact (F1) of the proof of Corollary 2.7):
for a rectifiable varifold `V = v(M, θ)`, `V.tangentProj` is `μ_V`-a.e. strongly measurable, and at
`μ_V`-a.e. `x` there is a weighted approximate tangent space `T` of `M` with respect to `θ`
(Simon 1.7), with `p_{T_x M} = p_T`.

Proof.  Up to an `Hⁿ`-null set, `M` is covered by the compact Lusin pieces `K` of `θ`
(`aetp_lusin_compact_exhaustion`) intersected with images `S = F(A)` of bounded Borel pieces `A` of
the parameter domains of the Lipschitz charts `F` of `M` on which `F` approximates an injective
linear map (Federer's partition, Mathlib `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`;
the points where `DF` is not injective have `Hⁿ`-null image by the area formula), so `F` is
bi-Lipschitz on `A`; this replaces the `C¹` approximation of Lemma 1.2.  The area formula
`Hⁿ ⌞ F(A) = F_#(J_F 𝓛ⁿ ⌞ A)` (SimonGMT Ch. 2), the Lebesgue points of `1_A J_F` and the blow-up
identity (`rsod_blowUp_setIntegral_eq`) give `DF(a)(ℝⁿ)` as the approximate tangent space of `S` at
`F(a)`.  The upper density theorem (`aetp_upper_density_zero_ae`) for `Hⁿ ⌞ (K \ S)` and
`Hⁿ ⌞ (S \ K)` makes it the approximate tangent space of `K` (proof of Simon 1.6), and for
`μ_V ⌞ (M \ K)` it gives the hypothesis of `aetp_weightedTangent_of_lusin_compact`, which yields the
weighted approximate tangent space (Remark 1.8(1)).  It is unique since `θ > 0` on `M`, so
`p_{T_x M} = p_{DF(a)(ℝⁿ)}`, and composing the continuous `L ↦ p_{L(ℝⁿ)}`
(`aetp_starProjection_range_continuousOn`) with a Borel inverse of `F` on `A` gives measurability.
The area-formula steps are those of the accepted candidate for `allard52_tangent_ae`. -/
theorem lgc_tangent_plane_ae : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight ∧ ∀ᵐ x ∂V.weight, ∃ T : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x T ∧ V.tangentProj x = T.starProjection := by
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
/-- **Blow-up test integrals versus normalized ball mass** (Simon Ch. 3, Remark 1.8(2)).  For
`η = η_{x,r}`, a Borel cut-off `0 ≤ φ ≤ 1` vanishing off `B_R(0)` with `B_{rR}(x) ⊆ U`, the blow-up
integral `I = ∫_{η(M)} φ(y) θ(x + r y) dHⁿ(y)` is nonnegative, and it bounds
`J = r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ` from above if `φ = 1` on `B_1(0)` and from below if `φ = 0` off
`B_1(0)`. -/
theorem rsod_blowUp_integral_ballMass_bounds : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (r R : ℝ) (φ : Amb n ℓ → ℝ), 0 < r → 1 ≤ R →
    closedBall x (r * R) ⊆ U → Measurable φ → (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) →
    (∀ y, y ∉ closedBall (0 : Amb n ℓ) R → φ y = 0) →
    0 ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier,
        φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) ∧
    ((∀ y ∈ closedBall (0 : Amb n ℓ) 1, φ y = 1) →
      (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ)) ≤
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier,
          φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ))) ∧
    ((∀ y, y ∉ closedBall (0 : Amb n ℓ) 1 → φ y = 0) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier,
          φ y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) ≤
        (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) := by
  intro n ℓ U V x r R φ hr hR hball hφm hφ01 hφsupp
  -- Step 1: change of variables, `I = r⁻ⁿ ∫_M φ(η z) θ(z) dHⁿ(z)`.
  rw [Submission.rsod_blowUp_setIntegral_eq n ℓ V.carrier φ V.mult x r hr]
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  have hrpos : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.mpr (pow_nonneg hr.le n)
  -- Step 2: `η z ∈ B_s(0) ↔ z ∈ B_{rs}(x)`.
  have hmem : ∀ z : Amb n ℓ, ∀ s : ℝ,
      η z ∈ closedBall (0 : Amb n ℓ) s ↔ z ∈ closedBall x (r * s) := by
    intro z s
    simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap, mem_closedBall, dist_eq_norm,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm s r]
  -- Step 3: `θ` is integrable on `M ∩ B_{rR}(x)` and on `M ∩ B_r(x)`, compact subsets of `U`.
  have hballr : closedBall x r ⊆ U :=
    (closedBall_subset_closedBall (le_mul_of_one_le_right hr.le hR)).trans hball
  have hintR : IntegrableOn V.mult (V.carrier ∩ closedBall x (r * R)) μ :=
    V.integrableOn_mult _ (isCompact_closedBall _ _) hball
  have hintr : IntegrableOn V.mult (V.carrier ∩ closedBall x r) μ :=
    V.integrableOn_mult _ (isCompact_closedBall _ _) hballr
  have hind : IntegrableOn ((closedBall x r).indicator V.mult) V.carrier μ := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hintr
  -- Step 4: `h = (φ ∘ η) θ` is integrable on `M`, being dominated by `1_{B_{rR}(x)} θ`.
  have hηm : Measurable η := by
    rw [hη]
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hh : IntegrableOn (fun z => φ (η z) * V.mult z) V.carrier μ := by
    have hg : Integrable ((closedBall x (r * R)).indicator V.mult) (μ.restrict V.carrier) := by
      rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact hintR
    refine hg.mono ((hφm.comp hηm).aestronglyMeasurable.mul
      V.aemeasurable_mult.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz, norm_mul]
      have h1 : ‖φ (η z)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (hφ01 _).1]
        exact (hφ01 _).2
      calc ‖φ (η z)‖ * ‖V.mult z‖ ≤ 1 * ‖V.mult z‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖V.mult z‖ := one_mul _
    · rw [indicator_of_notMem hz, hφsupp _ fun h => hz ((hmem z R).1 h), zero_mul, norm_zero]
  -- Step 5: `ν = Hⁿ ⌞ M`-a.e. point lies in `M`, where `θ > 0`.
  have hae : ∀ᵐ z ∂(μ.restrict V.carrier), z ∈ V.carrier :=
    ae_restrict_mem₀ V.nullMeasurableSet_carrier
  -- Step 7: `J = r⁻ⁿ ∫_M 1_{B_r(x)} θ dHⁿ`.
  have hJ : ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂μ =
      ∫ z in V.carrier, (closedBall x r).indicator V.mult z ∂μ :=
    (setIntegral_indicator measurableSet_closedBall).symm
  refine ⟨?_, ?_, ?_⟩
  · -- Step 6, (a): `h ≥ 0` a.e. on `M`.
    refine mul_nonneg hrpos (setIntegral_nonneg_of_ae_restrict ?_)
    filter_upwards [hae] with z hz
    exact mul_nonneg (hφ01 _).1 (V.mult_pos z hz).le
  · -- Step 8, (b): `1_{B_r(x)} θ ≤ h` a.e. on `M` when `φ = 1` on `B_1(0)`.
    intro hφ1
    rw [hJ]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_ae_restrict hind hh ?_) hrpos
    filter_upwards [hae] with z hz
    by_cases hzB : z ∈ closedBall x r
    · rw [indicator_of_mem hzB, hφ1 _ ((hmem z 1).2 (by rwa [mul_one])), one_mul]
    · rw [indicator_of_notMem hzB]
      exact mul_nonneg (hφ01 _).1 (V.mult_pos z hz).le
  · -- Step 9, (c): `h ≤ 1_{B_r(x)} θ` a.e. on `M` when `φ = 0` off `B_1(0)`.
    intro hφ0
    rw [hJ]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_ae_restrict hh hind ?_) hrpos
    filter_upwards [hae] with z hz
    by_cases hzB : z ∈ closedBall x r
    · rw [indicator_of_mem hzB]
      exact mul_le_of_le_one_left (V.mult_pos z hz).le (hφ01 _).2
    · rw [indicator_of_notMem hzB,
        hφ0 _ fun h => hzB (by simpa only [mul_one] using (hmem z 1).1 h), zero_mul]
/-- **Simon Ch. 3, Remark 1.8(2)** (weighted form) for `V = v(M, θ)`.  If `P` is the approximate
tangent space of `M` at `x ∈ U` with respect to `θ` (Ch. 3, Definition 1.7), then
`r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ → ω_n θ(x)` as `r ↓ 0`.  For `ε ∈ (0, 1)` take continuous cut-offs
`g_ε ≤ 1_{B_1(0)} ≤ f_ε` with `g_ε = 1` on `B_{1−ε}(0)` and `f_ε = 0` off `B_{1+ε}(0)`; for small
`r`, `∫_{η_{x,r}(M)} g_ε θ(x + r·) dHⁿ ≤ r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ ≤ ∫_{η_{x,r}(M)} f_ε θ(x + r·) dHⁿ`,
and the outer terms tend to `θ(x) ∫_P g_ε ≥ θ(x) ω_n (1 − ε)ⁿ` and `θ(x) ∫_P f_ε ≤ θ(x) ω_n (1 + ε)ⁿ`
(`θ(x) ≥ 0` follows from the lower comparison). -/
theorem rsod_tendsto_scaled_mult_integral : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), x ∈ U → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (unitBallVolume n * V.mult x)) := by
  intro n ℓ hn U hU V x P hx hP
  -- `ω_n = π^{n/2} / Γ(n/2 + 1) > 0`, and `B_{rR}(x) ⊆ B̆_e(x) ⊆ U` for `r < e / 2`, `R ≤ 2`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.1 hU x hx
  have hballU : ∀ r R : ℝ, 0 < r → r < e / 2 → R ≤ 2 → closedBall x (r * R) ⊆ U := by
    intro r R hr hre hR
    refine (closedBall_subset_ball ?_).trans heU
    calc r * R ≤ r * 2 := mul_le_mul_of_nonneg_left hR hr.le
      _ < e := by linarith
  -- Continuous compactly supported cut-offs: `0 ≤ φ ≤ 1`, `φ = 1` on `B_a(0)`, `φ = 0` off
  -- `B_b(0)`, namely `φ(y) = min 1 (max 0 ((b - ‖y‖) / (b - a)))`.
  have cutoff : ∀ a b : ℝ, a < b → ∃ φ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ,
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ closedBall (0 : Amb n ℓ) a, φ y = 1) ∧
        ∀ y, y ∉ closedBall (0 : Amb n ℓ) b → φ y = 0 := by
    intro a b hab
    have hba : 0 < b - a := sub_pos.2 hab
    let φ : Amb n ℓ → ℝ := fun y => min 1 (max 0 ((b - ‖y‖) / (b - a)))
    have hφc : Continuous φ :=
      continuous_const.min (continuous_const.max ((continuous_const.sub continuous_norm).div_const _))
    have hφ0 : ∀ y, y ∉ closedBall (0 : Amb n ℓ) b → φ y = 0 := by
      intro y hy
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      have hneg : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 0
      rw [max_eq_left hneg, min_eq_right zero_le_one]
    refine ⟨⟨⟨φ, hφc⟩, HasCompactSupport.intro (isCompact_closedBall 0 b) hφ0⟩,
      fun y => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩, fun y hy => ?_, hφ0⟩
    rw [mem_closedBall, dist_zero_right] at hy
    have hone : 1 ≤ (b - ‖y‖) / (b - a) := by
      rw [le_div_iff₀ hba]
      linarith
    show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 1
    rw [max_eq_right (zero_le_one.trans hone), min_eq_left hone]
  -- Plane integrals: `Hⁿ ⌞ P (B_s(0)) = ω_n sⁿ` (sibling `plane_ball_measure`).
  have hPdim : Module.finrank ℝ P = n := hP.1
  have hplane_ind : ∀ s : ℝ, 0 ≤ s →
      Integrable ((closedBall (0 : Amb n ℓ) s).indicator fun _ => (1 : ℝ))
        ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) ∧
      ∫ y, (closedBall (0 : Amb n ℓ) s).indicator (fun _ => (1 : ℝ)) y
          ∂((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) =
        unitBallVolume n * s ^ n := by
    intro s hs
    have hmeas := Submission.rsod_planeMeasure_closedBall n ℓ hn P hPdim s hs
    refine ⟨(integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (hmeas ▸ ENNReal.ofReal_ne_top)), ?_⟩
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one, measureReal_def,
      hmeas, ENNReal.toReal_ofReal (mul_nonneg hω.le (pow_nonneg hs n))]
  -- `0 ≤ φ ≤ 1_{B_b(0)}` gives `φ ∈ L¹(Hⁿ ⌞ P)` and `∫_P φ ≤ ω_n bⁿ`.
  have hplane_le : ∀ (φ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ) (b : ℝ), 0 ≤ b →
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) → (∀ y, y ∉ closedBall (0 : Amb n ℓ) b → φ y = 0) →
      Integrable φ ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) ∧
        ∫ y in (P : Set (Amb n ℓ)), φ y ∂(μHE[n] : Measure (Amb n ℓ)) ≤
          unitBallVolume n * b ^ n := by
    intro φ b hb hφ01 hφ0
    obtain ⟨hint, hval⟩ := hplane_ind b hb
    have hle : ∀ y, φ y ≤ (closedBall (0 : Amb n ℓ) b).indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ closedBall (0 : Amb n ℓ) b
      · rw [Set.indicator_of_mem hy]
        exact (hφ01 y).2
      · rw [Set.indicator_of_notMem hy, hφ0 y hy]
    have hφint : Integrable φ ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) :=
      hint.mono' (map_continuous φ).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hφ01 y).1]; exact hle y)
    exact ⟨hφint, (integral_mono hφint hint hle).trans_eq hval⟩
  -- `1_{B_a(0)} ≤ φ` (with `φ` as above) gives `ω_n aⁿ ≤ ∫_P φ`.
  have hplane_ge : ∀ (φ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ) (a b : ℝ), 0 ≤ a →
      0 ≤ b → (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) → (∀ y ∈ closedBall (0 : Amb n ℓ) a, φ y = 1) →
      (∀ y, y ∉ closedBall (0 : Amb n ℓ) b → φ y = 0) →
      unitBallVolume n * a ^ n ≤ ∫ y in (P : Set (Amb n ℓ)), φ y ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro φ a b ha hb hφ01 hφ1 hφ0
    obtain ⟨hint, hval⟩ := hplane_ind a ha
    have hle : ∀ y, (closedBall (0 : Amb n ℓ) a).indicator (fun _ => (1 : ℝ)) y ≤ φ y := by
      intro y
      by_cases hy : y ∈ closedBall (0 : Amb n ℓ) a
      · rw [Set.indicator_of_mem hy, hφ1 y hy]
      · rw [Set.indicator_of_notMem hy]
        exact (hφ01 y).1
    exact hval.symm.trans_le (integral_mono hint (hplane_le φ b hb hφ01 hφ0).1 hle)
  -- `θ(x) ≥ 0`: the blow-up integrals of `g = g_{1/2} ≥ 0` are `≥ 0` (sibling
  -- `blowup_ball_mass_bounds`) and tend to `θ(x) ∫_P g` with `∫_P g ≥ ω_n 2⁻ⁿ > 0`.
  have ht : 0 ≤ V.mult x := by
    obtain ⟨g, hg01, hg1, hg0⟩ := cutoff (1 / 2) 1 (by norm_num)
    have hpos : 0 < ∫ y in (P : Set (Amb n ℓ)), g y ∂(μHE[n] : Measure (Amb n ℓ)) :=
      (mul_pos hω (pow_pos (by norm_num) n)).trans_le
        (hplane_ge g (1 / 2) 1 (by norm_num) zero_le_one hg01 hg1 hg0)
    have hnonneg :
        0 ≤ V.mult x * ∫ y in (P : Set (Amb n ℓ)), g y ∂(μHE[n] : Measure (Amb n ℓ)) := by
      refine ge_of_tendsto (hP.2 g) ?_
      filter_upwards [Ioo_mem_nhdsGT (half_pos he)] with r hr
      exact (Submission.rsod_blowUp_integral_ballMass_bounds n ℓ U V x r 1 g hr.1 le_rfl
        (hballU r 1 hr.1 hr.2 one_le_two) (map_continuous g).measurable hg01 hg0).1
    exact nonneg_of_mul_nonneg_left hnonneg hpos
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Lower bound: pick `ε ∈ (0, 1)` with `a < θ(x) ω_n (1 - ε)ⁿ ≤ θ(x) ∫_P g_ε`.
    have hcont : Continuous fun ε : ℝ => V.mult x * (unitBallVolume n * (1 - ε) ^ n) := by
      fun_prop
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < V.mult x * (unitBallVolume n * (1 - ε) ^ n) :=
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).eventually_const_lt
        (by simpa [mul_comm] using ha)
    obtain ⟨ε, hεa, hε⟩ :=
      (hev.and (Ioo_mem_nhdsGT one_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1)).exists
    obtain ⟨g, hg01, hg1, hg0⟩ := cutoff (1 - ε) 1 (by linarith [hε.1])
    have hlt : a < V.mult x * ∫ y in (P : Set (Amb n ℓ)), g y ∂(μHE[n] : Measure (Amb n ℓ)) :=
      hεa.trans_le (mul_le_mul_of_nonneg_left
        (hplane_ge g (1 - ε) 1 (by linarith [hε.2]) zero_le_one hg01 hg1 hg0) ht)
    filter_upwards [(hP.2 g).eventually_const_lt hlt, Ioo_mem_nhdsGT (half_pos he)] with r hr hr'
    exact hr.trans_le ((Submission.rsod_blowUp_integral_ballMass_bounds n ℓ U V x r 1 g hr'.1
      le_rfl (hballU r 1 hr'.1 hr'.2 one_le_two) (map_continuous g).measurable hg01 hg0).2.2 hg0)
  · -- Upper bound: pick `ε ∈ (0, 1)` with `θ(x) ∫_P f_ε ≤ θ(x) ω_n (1 + ε)ⁿ < b`.
    have hcont : Continuous fun ε : ℝ => V.mult x * (unitBallVolume n * (1 + ε) ^ n) := by
      fun_prop
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), V.mult x * (unitBallVolume n * (1 + ε) ^ n) < b :=
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).eventually_lt_const
        (by simpa [mul_comm] using hb)
    obtain ⟨ε, hεb, hε⟩ :=
      (hev.and (Ioo_mem_nhdsGT one_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1)).exists
    obtain ⟨f, hf01, hf1, hf0⟩ := cutoff 1 (1 + ε) (by linarith [hε.1])
    have hlt : V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)) < b :=
      (mul_le_mul_of_nonneg_left (hplane_le f (1 + ε) (by linarith [hε.1]) hf01 hf0).2
        ht).trans_lt hεb
    filter_upwards [(hP.2 f).eventually_lt_const hlt, Ioo_mem_nhdsGT (half_pos he)] with r hr hr'
    exact ((Submission.rsod_blowUp_integral_ballMass_bounds n ℓ U V x r (1 + ε) f hr'.1
      (by linarith [hε.1]) (hballU r (1 + ε) hr'.1 hr'.2 (by linarith [hε.2]))
      (map_continuous f).measurable hf01 hf0).2.1 hf1).trans_lt hr
/-- **Weight of a ball as an integral of the multiplicity** (Simon Ch. 4, 1.1).  If
`B_r(x) ⊆ U`, then `μ_V(B_r(x)) = ∫_{M ∩ B_r(x)} θ dHⁿ`.  By definition
`μ_V(B_r(x)) = ∫⁻_{M ∩ B_r(x)} θ dHⁿ`; as `B_r(x)` is compact, `θ` is `Hⁿ`-integrable on
`M ∩ B_r(x)`, and `θ > 0` on `M`, so this lower integral is the (real) integral. -/
theorem rsod_weight_closedBall_eq_ofReal_integral : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (r : ℝ), closedBall x r ⊆ U → V.weight (closedBall x r) = ENNReal.ofReal (∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) := by
  intro n ℓ U V x r hU
  -- `θ` is integrable on `M ∩ B_r(x)` (the closed ball is compact and lies in `U`) ...
  have hint : IntegrableOn V.mult (V.carrier ∩ closedBall x r) (μHE[n] : Measure (Amb n ℓ)) :=
    V.integrableOn_mult _ (isCompact_closedBall x r) hU
  -- ... and nonnegative a.e. there, since a.e. point of `M ∩ B_r(x)` lies in `M`.
  have hnn : 0 ≤ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict (V.carrier ∩ closedBall x r)] V.mult := by
    filter_upwards [ae_restrict_mem₀
      (V.nullMeasurableSet_carrier.inter measurableSet_closedBall.nullMeasurableSet)] with z hz
    exact (V.mult_pos z hz.1).le
  rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
    Measure.restrict_restrict measurableSet_closedBall, inter_comm (closedBall x r) V.carrier,
    ofReal_integral_eq_lintegral_ofReal hint.integrable hnn]
/-- **Simon Ch. 3, Lemma 1.2, Theorem 1.9 and Remark 1.8(2)** for `V = v(M, θ)` in the open set
`U`: for `μ_V`-a.e. `x`, `p_{T_x M}` is the orthogonal projection onto an `n`-dimensional subspace,
`x ↦ p_{T_x M}` is `μ_V`-a.e. strongly measurable, and `Θⁿ(μ_V, x) = θ(x)`.  The first two
assertions are `lgc_tangent_plane_ae`: `μ_V`-a.e. `x` has a weighted approximate tangent space `P`
(of dimension `n` by Definition 1.7) with `p_{T_x M} = p_P`.  For the density, `μ_V ≪ Hⁿ ⌞ M`, so
`μ_V`-a.e. such `x` also lies in `M ⊆ U`; for small `r > 0`, `B_r(x) ⊆ U` gives
`μ_V(B_r(x)) = ∫_{M ∩ B_r(x)} θ dHⁿ` (`rsod_weight_closedBall_eq_ofReal_integral`), and
`r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ → ω_n θ(x)` (`rsod_tendsto_scaled_mult_integral`), so
`μ_V(B_r(x)) / (ω_n rⁿ) → θ(x)`. -/
theorem aal_tangent_structure : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ V : RectifiableVarifold n ℓ U, (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) := by
  intro n ℓ hn U hU V
  obtain ⟨hmeas, hae⟩ := Submission.lgc_tangent_plane_ae n ℓ hn U hU V
  refine ⟨?_, hmeas, ?_⟩
  · filter_upwards [hae] with x ⟨T, hT, hTp⟩
    exact ⟨T, hT.1, hTp⟩
  -- `μ_V`-a.e. point lies in `M`, since `μ_V ≪ Hⁿ ⌞ M`; and `ω_n > 0`.
  have hcar : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  filter_upwards [hae, hcar] with x ⟨T, hT, _⟩ hx
  obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.1 hU x (V.carrier_subset hx)
  -- `ω_n⁻¹ (r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ) → ω_n⁻¹ (ω_n θ(x)) = θ(x)`.
  have hlim := (Submission.rsod_tendsto_scaled_mult_integral n ℓ hn U hU V x T
    (V.carrier_subset hx) hT).const_mul (unitBallVolume n)⁻¹
  rw [inv_mul_cancel_left₀ hω.ne'] at hlim
  show Tendsto (fun r : ℝ => V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal (V.mult x)))
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  -- For `0 < r < e`, `B_r(x) ⊆ U`, so `μ_V(B_r(x)) / (ω_n rⁿ)` is the real quotient above.
  filter_upwards [Ioo_mem_nhdsGT he] with r hr
  rw [Submission.rsod_weight_closedBall_eq_ofReal_integral n ℓ U V x r
      ((closedBall_subset_ball hr.2).trans heU),
    ← ENNReal.ofReal_div_of_pos (mul_pos hω (pow_pos hr.1 n))]
  congr 1
  ring
/-- **`Lᵖ` monotonicity identity** (Simon Ch. 4, 3.2–3.6 and 4.1–4.8, with the constant
`κ = (p − n)/(4p)` in front of `Λ`).  Let `p > n`, `B_S(y) ⊆ U`, `∫_{B_S(y)} |H|ᵖ dμ_V < ∞` and
`(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ_V)^{1/p} ≤ κ Λ` with `0 < R < S`, `Λ > 0`.  Then there are `F` with
`e^{−Λ} ≤ F(r) ≤ e^Λ` and `|F(r) − 1| ≤ ½ e^{Λ/2} Λ (r/R)^{1−n/p}` (`≤ Λ (r/R)^{1−n/p}` if `Λ ≤ 1`)
for `0 < r ≤ R`, and `G` with `e^{−Λ} ≤ G(s, r) ≤ e^Λ` and
`Φ(r) − Φ(s) = G(s, r) ∫_{B_r(y) \ B_s(y)} |p_x^⊥(x − y)|² / |x − y|^{n+2} dμ_V` for `0 < s ≤ r ≤ R`,
where `Φ(t) = F(t) t⁻ⁿ μ_V(B_t(y)) + F(t) − 1`.

By `aal_tangent_structure`, `p_x` is `μ_V`-a.e. a rank-`n` orthogonal projection and `x ↦ p_x` is
a.e. strongly measurable, so `w(x) = |p_x^⊥(x − y)|² / |x − y|²` is a.e. strongly measurable with
`0 ≤ w ≤ 1` a.e.  `μ_V(B_S(y)) < ∞` and `H ∈ L¹(B_S(y))` because `B_S(y)` is a compact subset of
`U`.  `aal_radial_first_variation_identity` gives the radial identity for every cutoff profile, and
`aal_monotonicity_of_radial_identity` then yields `F` together with
`e^{−Λ} A ≤ Φ(r) − Φ(s) ≤ e^Λ A`, `A = ∫_{B_r(y) \ B_s(y)} w / |x − y|ⁿ dμ_V`; here
`w / |x − y|ⁿ = |p_x^⊥(x − y)|² / |x − y|^{n+2}`.  Finally `G(s, r) = (Φ(r) − Φ(s)) / A`, or `1`
if `A = 0` (then the squeeze forces `Φ(r) = Φ(s)`). -/
theorem aal_lp_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → closedBall y S ⊆ U → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂V.weight < ⊤ → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ), (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → Real.exp (-Λ) ≤ G s r ∧ G s r ≤ Real.exp Λ ∧ IntegrableOn (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) (closedBall y r \ closedBall y s) V.weight ∧ (F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1)) - (F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1)) = G s r * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight) := by
  intro n ℓ hn p hp U hU V H hH y R S Λ hR hRS hΛ hBS hHp hK
  -- Step 0: `p_x` is a.e. a rank-`n` orthogonal projection, and `x ↦ p_x` is a.e. measurable.
  obtain ⟨hproj, hmeas, -⟩ := Submission.aal_tangent_structure n ℓ hn U hU V
  -- `μ_V(B_S(y)) = ∫_{M ∩ B_S(y)} θ dHⁿ < ∞` and `H ∈ L¹(B_S(y))`, as `B_S(y) ⊆ U` is compact.
  have hμS : V.weight (closedBall y S) < ⊤ := by
    have hint := V.integrableOn_mult (closedBall y S) (isCompact_closedBall y S) hBS
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hint.setLIntegral_lt_top
  have hHS : IntegrableOn H (closedBall y S) V.weight :=
    hH.1.integrableOn_compact_subset hBS (isCompact_closedBall y S)
  -- The weight `w(x) = |p_x^⊥(x − y)|² / |x − y|²` is a.e. strongly measurable, with `0 ≤ w ≤ 1`.
  have hTm : AEStronglyMeasurable (fun x => V.tangentProj x (x - y)) V.weight := by
    have happ : Continuous (Function.uncurry
        fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => A v) :=
      continuous_fst.clm_apply continuous_snd
    exact happ.comp_aestronglyMeasurable₂ hmeas (continuous_sub_right y).aestronglyMeasurable
  have hwm : AEStronglyMeasurable
      (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) V.weight := by
    have h1 : AEStronglyMeasurable (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2)
        V.weight :=
      ((continuous_sub_right y).aestronglyMeasurable.sub hTm).norm.pow 2
    have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => ‖x - y‖ ^ 2) V.weight :=
      ((continuous_sub_right y).norm.pow 2).aestronglyMeasurable
    exact (h1.aemeasurable.div h2.aemeasurable).aestronglyMeasurable
  have hw01 : ∀ᵐ x ∂V.weight, 0 ≤ ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 ∧
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 ≤ 1 := by
    filter_upwards [hproj] with x hx
    obtain ⟨P, -, hP⟩ := hx
    refine ⟨by positivity, div_le_one_of_le₀ ?_ (sq_nonneg _)⟩
    rw [hP, ← Submodule.starProjection_orthogonal_val]
    exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2
  -- The radial first-variation identity for every cutoff profile with `B_{Tρ}(y) ⊆ B_S(y)`.
  have hrad : ∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) →
      (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ ≤ S →
      ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
        (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight =
      -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight :=
    fun φ T ρ hφ h1 h0 hρ hTρ =>
      Submission.aal_radial_first_variation_identity n ℓ U V H hH hproj y φ T ρ hφ h1 h0 hρ
        ((closedBall_subset_closedBall hTρ).trans hBS)
  -- The monotonicity squeeze for the abstract weight `w`.
  obtain ⟨F, hF1, hF2⟩ := Submission.aal_monotonicity_of_radial_identity n ℓ hn p hp V.weight H
    (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) y R S Λ hR hRS hΛ hμS hwm
    hw01 hHS hHp hK hrad
  -- `g_y = w / |x − y|ⁿ` (also at `x = y`, where both sides vanish).
  have hg : (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) =
      fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 / ‖x - y‖ ^ n := by
    funext x
    rw [div_div, ← pow_add, add_comm 2 n]
  -- A two-sided squeeze `e^{−Λ} A ≤ D ≤ e^Λ A` gives the ratio `G = D / A` (`1` if `A = 0`).
  have hratio : ∀ A D : ℝ, Real.exp (-Λ) * A ≤ D → D ≤ Real.exp Λ * A →
      Real.exp (-Λ) ≤ (if A = 0 then 1 else D / A) ∧ (if A = 0 then 1 else D / A) ≤ Real.exp Λ ∧
        D = (if A = 0 then 1 else D / A) * A := by
    intro A D hlo hhi
    have hexp : Real.exp (-Λ) < Real.exp Λ := Real.exp_lt_exp.2 (by linarith)
    split_ifs with h0
    · subst h0
      rw [mul_zero] at hlo hhi
      exact ⟨Real.exp_le_one_iff.2 (by linarith), Real.one_le_exp hΛ.le, by linarith⟩
    · have hA : 0 < A := by
        rcases lt_or_gt_of_ne h0 with h | h
        · nlinarith
        · exact h
      exact ⟨(le_div_iff₀ hA).2 hlo, (div_le_iff₀ hA).2 hhi, (div_mul_cancel₀ D h0).symm⟩
  refine ⟨F, fun s r =>
    if (∫ x in closedBall y r \ closedBall y s,
        ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight) = 0 then 1
    else ((F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1)) -
        (F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1))) /
      ∫ x in closedBall y r \ closedBall y s,
        ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight, hF1, ?_⟩
  intro s r hs hsr hrR
  obtain ⟨hint, hlo, hhi⟩ := hF2 s r hs hsr hrR
  have hlo' : Real.exp (-Λ) * ∫ x in closedBall y r \ closedBall y s,
        ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight ≤
      (F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1)) -
        (F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1)) := by
    rw [hg]
    exact hlo
  have hhi' : (F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1)) -
        (F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1)) ≤
      Real.exp Λ * ∫ x in closedBall y r \ closedBall y s,
        ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight := by
    rw [hg]
    exact hhi
  obtain ⟨hG1, hG2, hG3⟩ := hratio _ _ hlo' hhi'
  refine ⟨hG1, hG2, ?_, hG3⟩
  rw [hg]
  exact hint
/-- **Uniform mass upper bound** (step 1a of the proof of Simon 2.5, valid for every
`δ ∈ (0, 1/4]`): under 2.3, `μ_V(B_s(y)) ≤ C₀ ω_n sⁿ` whenever `|y| ≤ ρ/4` and `s ∈ (0, ρ/2]`,
with `C₀ = e^{2Λ₁}((3/2)ⁿ(5/4) + e^{Λ₁/2}Λ₁/ω_n)` and `Λ₁ = p/(p − n)`.
For `κ = (p − n)/(4p)` and `Λ = δ/κ ≤ Λ₁`, `aal_lp_monotonicity` at `y` with `R = 2ρ/3`,
`S = 3ρ/4` (so `B_S(y) ⊆ B_ρ(0)` and, for `K(z, t) = V.scaledLpNorm H p z t`,
`K(y, R) ≤ K(0, ρ) ≤ δ = κΛ`) gives `Φ(s) ≤ Φ(R)` for
`Φ(t) = F(t) t⁻ⁿ μ(B_t(y)) + F(t) − 1`.  Then `e^{−Λ} ≤ F ≤ e^Λ`, `|F − 1| ≤ e^{Λ/2}Λ/2` and
`μ(B_R(y)) ≤ μ(B_ρ(0)) ≤ (5/4) ω_n ρⁿ` give
`s⁻ⁿ μ(B_s(y)) ≤ e^{2Λ}(3/2)ⁿ(5/4) ω_n + e^{3Λ/2}Λ ≤ C₀ ω_n`. -/
theorem aal_mass_upper_bound : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → ∀ y : Amb n ℓ, ‖y‖ ≤ ρ / 4 →
    ∀ s : ℝ, 0 < s → s ≤ ρ / 2 →
      V.weight (closedBall y s) ≤ ENNReal.ofReal (C₀ * (unitBallVolume n * s ^ n)) := by
  intro n ℓ hn p hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hpn : 0 < p - n := sub_pos.2 hp
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Step 1: the constants `Λ₁ = (1/4)/κ = p/(p − n)` and `C₀`.
  obtain ⟨Λ₁, hΛ₁_def⟩ : ∃ Λ₁ : ℝ, Λ₁ = p / (p - n) := ⟨_, rfl⟩
  have hΛ₁ : 0 < Λ₁ := by rw [hΛ₁_def]; exact div_pos hp0 hpn
  obtain ⟨C₀, hC₀_def⟩ : ∃ C₀ : ℝ, C₀ = Real.exp (2 * Λ₁) *
      ((3 / 2) ^ n * (5 / 4) + Real.exp (Λ₁ / 2) * Λ₁ / unitBallVolume n) := ⟨_, rfl⟩
  have hC₀ : 0 < C₀ := by rw [hC₀_def]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro U hU V H δ ρ hδ hδ4 hA y hy s hs hsρ
  obtain ⟨hρ, hH, -, -, hBU, hmass, hK⟩ := hA
  -- Step 2: `Λ = δ/κ ∈ (0, Λ₁]` for `κ = (p − n)/(4p)`, and the radii `R = 2ρ/3 < S = 3ρ/4`.
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = 4 * p * δ / (p - n) := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by rw [hΛ_def]; exact div_pos (by positivity) hpn
  have hΛΛ₁ : Λ ≤ Λ₁ := by
    rw [hΛ_def, hΛ₁_def]
    exact div_le_div_of_nonneg_right (by nlinarith) hpn.le
  have hκΛ : (p - n) / (4 * p) * Λ = δ := by
    rw [hΛ_def]
    field_simp
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = 2 * ρ / 3 := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : ℝ, S = 3 * ρ / 4 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hR_def]; positivity
  have hRS : R < S := by rw [hR_def, hS_def]; linarith
  have hRρ : R ≤ ρ := by rw [hR_def]; linarith
  have hsR : s ≤ R := by rw [hR_def]; linarith
  -- `B_t(y) ⊆ B_ρ(0)` for `t ≤ S`, since `|y| ≤ ρ/4`; in particular `B_S(y) ⊆ U`.
  have hball : ∀ t : ℝ, t ≤ S → closedBall y t ⊆ closedBall (0 : Amb n ℓ) ρ := by
    intro t ht
    refine closedBall_subset_closedBall' ?_
    rw [dist_zero_right]
    rw [hS_def] at ht
    linarith
  have hSU : closedBall y S ⊆ U := (hball S le_rfl).trans hBU
  -- (A): `∫_{B_ρ(0)} |H|ᵖ dμ < ∞`, since `ρ^{p−n} > 0` and `K(0, ρ) ≤ δ < ∞`.
  have hI : ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ := by
    have h1 := hK.trans_lt ENNReal.ofReal_lt_top
    rw [RectifiableVarifold.scaledLpNorm,
      ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0 : ℝ) < 1 / p)] at h1
    rcases ENNReal.mul_lt_top_iff.1 h1 with h | h | h
    · exact h.2
    · exact absurd h (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hρ _)).ne'
    · rw [h]
      exact ENNReal.zero_lt_top
  have hIS : ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂V.weight < ⊤ :=
    (lintegral_mono_set (hball S le_rfl)).trans_lt hI
  -- (K-mono): `K(y, R) ≤ K(0, ρ) ≤ δ = κΛ`.
  have hKR : V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) := by
    rw [hκΛ]
    refine le_trans ?_ hK
    unfold RectifiableVarifold.scaledLpNorm
    refine ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
      (lintegral_mono_set (hball R hRS.le))) (by positivity)
    exact Real.rpow_le_rpow hR.le hRρ hpn.le
  -- Step 3: the `Lᵖ` monotonicity identity at `y`, between the radii `s ≤ R`.
  obtain ⟨F, G, hF, hG⟩ := Submission.aal_lp_monotonicity n ℓ hn p hp U hU V H hH y R S Λ hR hRS
    hΛ hSU hIS hKR
  obtain ⟨hFs, -, -, -⟩ := hF s hs hsR
  obtain ⟨-, hFR, -, -⟩ := hF R hR le_rfl
  obtain ⟨hGs, -, -, hid⟩ := hG s R hs hsR le_rfl
  -- `|F(t) − 1| ≤ e^{Λ/2}Λ/2` on `(0, R]`, because `(t/R)^{1−n/p} ≤ 1`.
  have hexp : 0 ≤ 1 - (n : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact hp.le
  have herr : ∀ t : ℝ, 0 < t → t ≤ R → |F t - 1| ≤ Real.exp (Λ / 2) * Λ / 2 := by
    intro t ht htR
    have h1 : (t / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one (div_nonneg ht.le hR.le) ((div_le_one hR).2 htR) hexp
    calc |F t - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (t / R) ^ (1 - (n : ℝ) / p) :=
          (hF t ht htR).2.2.1
      _ ≤ Real.exp (Λ / 2) / 2 * Λ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp (Λ / 2) * Λ / 2 := by ring
  obtain ⟨hR1, hR2⟩ := abs_le.1 (herr R hR le_rfl)
  obtain ⟨hs1, hs2⟩ := abs_le.1 (herr s hs hsR)
  -- `Φ(s) ≤ Φ(R)`: the annular integral is nonnegative and `G(s, R) ≥ e^{−Λ} > 0`.
  have hint : 0 ≤ ∫ x in closedBall y R \ closedBall y s,
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight :=
    integral_nonneg fun x => div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have hGI := mul_nonneg ((Real.exp_pos (-Λ)).le.trans hGs) hint
  -- Step 4: `R⁻ⁿ μ(B_R(y)) ≤ (5/4) ω_n (3/2)ⁿ`, from `μ(B_R(y)) ≤ μ(B_ρ(0)) ≤ (1 + δ) ω_n ρⁿ`.
  have hmass_le : ∀ t : ℝ, t ≤ S →
      V.weight (closedBall y t) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) :=
    fun t ht => (measure_mono (hball t ht)).trans hmass
  have h32 : (3 / 2) ^ n * R ^ n = ρ ^ n := by
    rw [← mul_pow, hR_def]
    congr 1
    ring
  have hqR0 : 0 ≤ (V.weight (closedBall y R)).toReal / R ^ n :=
    div_nonneg ENNReal.toReal_nonneg (pow_pos hR n).le
  have hqs0 : 0 ≤ (V.weight (closedBall y s)).toReal / s ^ n :=
    div_nonneg ENNReal.toReal_nonneg (pow_pos hs n).le
  have hqR : (V.weight (closedBall y R)).toReal / R ^ n ≤
      5 / 4 * unitBallVolume n * (3 / 2) ^ n := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) (hmass_le R hRS.le)
    rw [div_le_iff₀ (pow_pos hR n)]
    calc (V.weight (closedBall y R)).toReal ≤ (1 + δ) * (unitBallVolume n * ρ ^ n) := h1
      _ ≤ 5 / 4 * (unitBallVolume n * ρ ^ n) := by gcongr; linarith
      _ = 5 / 4 * unitBallVolume n * ((3 / 2) ^ n * R ^ n) := by rw [h32]; ring
      _ = 5 / 4 * unitBallVolume n * (3 / 2) ^ n * R ^ n := by ring
  -- `F(s) s⁻ⁿ μ(B_s(y)) ≤ Φ(R) + |F(s) − 1| ≤ e^Λ R⁻ⁿ μ(B_R(y)) + e^{Λ/2}Λ`.
  have hFq : F s * ((V.weight (closedBall y s)).toReal / s ^ n) ≤
      Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) + Real.exp (Λ / 2) * Λ := by
    have h1 : F R * ((V.weight (closedBall y R)).toReal / R ^ n) ≤
        Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) :=
      mul_le_mul hFR hqR hqR0 (Real.exp_pos Λ).le
    linarith
  -- Divide by `F(s) ≥ e^{−Λ}`.
  have hq : (V.weight (closedBall y s)).toReal / s ^ n ≤ Real.exp Λ *
      (Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) + Real.exp (Λ / 2) * Λ) := by
    calc (V.weight (closedBall y s)).toReal / s ^ n
        = Real.exp Λ * (Real.exp (-Λ) * ((V.weight (closedBall y s)).toReal / s ^ n)) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp Λ * (F s * ((V.weight (closedBall y s)).toReal / s ^ n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFs hqs0) (Real.exp_pos Λ).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hFq (Real.exp_pos Λ).le
  -- `e^{2Λ}(3/2)ⁿ(5/4) ω_n + e^{3Λ/2}Λ ≤ C₀ ω_n`, using `Λ ≤ Λ₁`.
  have hC : Real.exp Λ *
      (Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) + Real.exp (Λ / 2) * Λ) ≤
        C₀ * unitBallVolume n := by
    have e1 : Real.exp Λ * Real.exp Λ ≤ Real.exp (2 * Λ₁) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp Λ * Real.exp (Λ / 2) ≤ Real.exp (2 * Λ₁) * Real.exp (Λ₁ / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hX : 0 ≤ 5 / 4 * unitBallVolume n * (3 / 2) ^ n := by positivity
    calc Real.exp Λ *
          (Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) + Real.exp (Λ / 2) * Λ)
        = Real.exp Λ * Real.exp Λ * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) +
            Real.exp Λ * Real.exp (Λ / 2) * Λ := by ring
      _ ≤ Real.exp (2 * Λ₁) * (5 / 4 * unitBallVolume n * (3 / 2) ^ n) +
            Real.exp (2 * Λ₁) * Real.exp (Λ₁ / 2) * Λ₁ :=
          add_le_add (mul_le_mul_of_nonneg_right e1 hX)
            (mul_le_mul e2 hΛΛ₁ hΛ.le (by positivity))
      _ = C₀ * unitBallVolume n := by
          rw [hC₀_def]
          field_simp
  -- Conclusion: `μ(B_s(y)).toReal ≤ C₀ ω_n sⁿ`, and `μ(B_s(y)) < ∞`.
  have hms : (V.weight (closedBall y s)).toReal ≤ C₀ * (unitBallVolume n * s ^ n) := by
    have h1 := hq.trans hC
    rw [div_le_iff₀ (pow_pos hs n)] at h1
    calc (V.weight (closedBall y s)).toReal ≤ C₀ * unitBallVolume n * s ^ n := h1
      _ = C₀ * (unitBallVolume n * s ^ n) := mul_assoc _ _ _
  have hfin : V.weight (closedBall y s) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass_le s (by rw [hS_def]; linarith))
  exact (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2 hms
/-- Simon Ch. 5, proof of Lemma 2.1 (pp. 107–108), kept in `L¹` form (Lemma A in the proof of the
Affine Approximation Lemma 2.5): if `dist(x − z, T) ≤ h` for every `x ∈ spt V ∩ B_r(z)`, then
`∫_{B_{r/2}(z)} |p_{T_x M} − p_T|² dμ_V
   ≤ 144 r⁻² ∫_{B_r(z)} dist(x − z, T)² dμ_V + 4 h ∫_{B_r(z)} |H| dμ_V`.
Test the first variation with `X = ζ² x'`, `x' = p_{T⊥}(x − z)`, `ζ` the cutoff of
`aal_l1th_exists_cutoff`; absorb the gradient term by `2ab ≤ a²/4 + 4b²`, and bound the
mean-curvature term by `|x'| ≤ h` instead of Cauchy–Schwarz (so neither `|H|²` nor a lower bound on
`θ` is needed). -/
theorem aal_l1_tilt_height : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → closedBall z r ⊆ U → 0 ≤ h → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ 144 * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH z r h hr hBU hh T hT hheight
  -- Step 0: `p_x` is a rank-`n` orthogonal projection `μ`-a.e., and `x ↦ p_x` is measurable.
  obtain ⟨hae, hmeas, -⟩ := Submission.aal_tangent_structure n ℓ hn U hU V
  -- Step 1: the cutoff: `ζ = 1` on `B_{r/2}(z)`, `ζ = 0` where `|x - z| ≥ r`, `|Dζ| ≤ 3/r`.
  obtain ⟨ζ, hζC1, hζ01, hζ1, hζ0, hζd⟩ : ∃ ζ : Amb n ℓ → ℝ, ContDiff ℝ 1 ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall z (r / 2), ζ x = 1) ∧
      (∀ x, r ≤ dist x z → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r :=
    Submission.aal_l1th_exists_cutoff (n + ℓ) z r hr
  -- Step 0: `μ(B_r(z)) < ∞` since `θ` is locally integrable, and `μ`-a.e. point lies in `spt V`.
  have hμB : V.weight (closedBall z r) < ∞ := by
    have hint := V.integrableOn_mult _ (isCompact_closedBall z r) hBU
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hint.lintegral_lt_top
  have : IsFiniteMeasure (V.weight.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.2 hμB.ne
  have hsupp : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have hUc : V.weight Uᶜ = 0 := by
      rw [RectifiableVarifold.weight, withDensity_apply _ hU.isClosed_compl.measurableSet,
        Measure.restrict_restrict hU.isClosed_compl.measurableSet]
      have hempty : Uᶜ ∩ V.carrier = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun hxU hxM => hxU (V.carrier_subset hxM)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    have hUae : ∀ᵐ x ∂V.weight, x ∈ U := by
      rw [ae_iff]
      simpa [compl_def] using hUc
    filter_upwards [hUae, Measure.support_mem_ae (μ := V.weight)] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  -- Linear algebra: `‖A‖ ≤ |A|` (child `aal_l1th_projection_algebra`), `|p_{T⊥} v| = dist(v, T)`.
  have hopHS : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, ‖A‖ ≤ hsNorm A := fun A =>
    Submission.aal_l1th_projection_algebra.1 (n + ℓ) (n + ℓ) A
  have hperp : ∀ v : Amb n ℓ, ‖Tᗮ.starProjection v‖ = infDist v (T : Set (Amb n ℓ)) := by
    intro v
    rw [Submodule.starProjection_orthogonal_val, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist]
  -- Notation: `g = |p_x - p_T|² = 2s`, `w = x' = p_{T⊥}(x - z)`, the gradient term `b`, and the
  -- test field `X = ζ² x'`.
  obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ, ∀ x, g x = hsNormSq (V.tangentProj x - T.starProjection) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → Amb n ℓ, ∀ x, w x = Tᗮ.starProjection (x - z) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Amb n ℓ → ℝ,
      ∀ x, b x = 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, ∀ x, X x = ζ x ^ 2 • w x := ⟨_, fun _ => rfl⟩
  have hXeq : X = fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z) := funext fun y => by rw [hX, hw]
  -- Pointwise bounds: `0 ≤ ζ² ≤ 1`, `|x'| ≤ r` on `B_r(z)`, `‖p_x - p_T‖ ≤ 2`, `0 ≤ g ≤ 4(n + ℓ)`.
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
  have hζsq : ∀ x, ζ x ^ 2 ≤ 1 := fun x => by
    obtain ⟨hz0, hz1⟩ := hζ01 x
    nlinarith
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
  -- Measurability on `B_r(z)`, from the a.e. strong measurability of `x ↦ p_x`.
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
  -- Step 3: integrability on the finite-measure ball `B_r(z)`.
  have hHint : Integrable H (V.weight.restrict (closedBall z r)) :=
    hH.1.integrableOn_compact_subset hBU (isCompact_closedBall z r)
  have hzg : Integrable (fun x => ζ x ^ 2 * g x) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound ((hζcont.pow 2).aestronglyMeasurable.mul hgm) ((n + ℓ : ℕ) * 4)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
    calc ζ x ^ 2 * g x ≤ 1 * ((n + ℓ : ℕ) * 4) :=
          mul_le_mul (hζsq x) (hgle x) (hg0 x) zero_le_one
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
  have hw2 : Integrable (fun x => ‖w x‖ ^ 2) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound (hwcont.norm.pow 2).aestronglyMeasurable (r ^ 2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwB x hx) 2
  have hXH : Integrable (fun x => inner ℝ (X x) (H x)) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.mono' (hHint.norm.const_mul r)
      (continuous_inner.comp_aestronglyMeasurable
        (hXcont.aestronglyMeasurable.prodMk hHint.aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * r := mul_le_mul (hζsq x) (hwB x hx) (norm_nonneg _) zero_le_one
      _ = r := one_mul _
  -- Step 1: `X = ζ² x'` is `C¹` with compact support in `B_r(z) ⊆ U`, so it is admissible.
  have hX1 : ContDiff ℝ 1 X := by
    rw [hXeq]
    exact (hζC1.pow 2).smul ((Tᗮ.starProjection).contDiff.comp (contDiff_id.sub contDiff_const))
  have hXout : ∀ x, x ∉ closedBall z r → X x = 0 := fun x hx => by
    rw [hX, hζout x hx]
    simp
  have hXcs : HasCompactSupport X := HasCompactSupport.intro (isCompact_closedBall z r) hXout
  have hXts : tsupport X ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hBU
    by_contra h'
    exact hx (hXout x h')
  -- Step 2: `div_M X = ζ² s + 2ζ Dζ((p_x - p_T) x')` with `s = g/2`, at `μ`-a.e. point
  -- (child `aal_l1th_test_field_divergence`, where `p_x = p_P` with `dim P = n`).
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = 1 / 2 * (ζ x ^ 2 * g x) + b x := by
    filter_upwards [hae] with x hx
    obtain ⟨P, hP, hPx⟩ := hx
    rw [hXeq, Submission.aal_l1th_test_field_divergence n ℓ U V ζ z x P T
      (hζC1.differentiable one_ne_zero x) hP hT hPx, hg, hb, hw]
    ring
  -- Step 3: the first variation identity `∫ div_M X dμ = -∫ X · H dμ`, localized to `B_r(z)`.
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
  -- Step 4: absorption, `|b| ≤ 2ζ (3/r) |p_x - p_T| |x'| ≤ ζ² g/4 + 36 r⁻² |x'|²`.
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
  -- Step 5: the mean-curvature term, using `|x'| ≤ h` at `μ`-a.e. point of `B_r(z)` (such points
  -- lie in `spt V ∩ B_r(z)`).
  have hXH_bd : ∀ᵐ x ∂(V.weight.restrict (closedBall z r)),
      -inner ℝ (X x) (H x) ≤ h * ‖H x‖ := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
      with x hxs hxB
    have hz2 := hζsq x
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
    have h' := integral_mono hbi.neg ((hzg.const_mul (1 / 4)).add (hw2.const_mul (36 / r ^ 2)))
      hb_bd
    simp only [Pi.neg_apply, Pi.add_apply] at h'
    rwa [integral_neg, integral_add (hzg.const_mul _) (hw2.const_mul _), integral_const_mul,
      integral_const_mul] at h'
  have e3 : -∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight ≤
      h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono_ae hXH.neg (hHint.norm.const_mul h) hXH_bd
  -- `∫ ζ² g/2 = -∫ b - ∫ X · H ≤ ∫ ζ² g/4 + 36 r⁻² ∫ |x'|² + h ∫ |H|`, and `∫ ζ² g < ∞`.
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
  -- `ζ = 1` on `B_{r/2}(z)` and `ζ² g ≥ 0`.
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
  calc ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
      = ∫ x in closedBall z (r / 2), g x ∂V.weight := by simp_rw [hg]
    _ ≤ ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight := hB2
    _ ≤ 144 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight +
          4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := key
    _ = 144 * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight +
          4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
      rw [hId, div_eq_mul_inv]

/-- **Simon Ch. 4, 3.9–3.13, 4.9 and Remark 4.10(1)** (lower density bound on `spt V`).  Under the
hypotheses 2.3 (`AllardHypotheses`), every `y ∈ spt V` with `|y| < ρ` satisfies
`μ_V(B_s(y)) ≥ (1 − ε) ω_n sⁿ` for all small `s > 0`, for each `ε > 0`.  At `μ_V`-a.e. `x` near `y`
the `Lᵖ` monotonicity identity and `Θⁿ(μ_V, x) = θ(x) ≥ 1` give
`ω_n ≤ (1 + c(t)) t⁻ⁿ μ_V(B_t(x)) + c(t)` with `c(t) = A (t/r)^{1−n/p} → 0`; since
`y ∈ spt μ_V`, such points accumulate at `y`, which transfers the bound to `y`. -/
theorem aal_density_ge_one : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), V.AllardHypotheses H p δ ρ → ∀ y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ, ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) := by
  intro n ℓ hn p hp U hU V H δ ρ hA y hy ε hε
  obtain ⟨hρ, hH, hθ, -, hball0, -, hK0⟩ := hA
  have hysupp : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hy.1).2
  have hyρ : ‖y‖ < ρ := mem_ball_zero_iff.mp hy.2
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := lt_trans hn' hp
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- One radius `r = d/8`, `d = ρ - |y|`, for every point of `B̆_r(y)`.
  set d := ρ - ‖y‖ with hd_def
  have hd : 0 < d := by linarith
  set r := d / 8 with hr_def
  have hr : 0 < r := by positivity
  -- Balls `B_{2r}(x)`, `x ∈ B̆_r(y)`, stay inside `B_ρ(0) ⊆ U`.
  have hsub0 : ∀ x : Amb n ℓ, x ∈ ball y r → closedBall x (2 * r) ⊆ closedBall (0 : Amb n ℓ) ρ := by
    intro x hx z hz
    rw [mem_ball] at hx
    rw [mem_closedBall] at hz
    have h1 : dist z 0 ≤ dist z x + (dist x y + dist y 0) :=
      (dist_triangle z x 0).trans (add_le_add le_rfl (dist_triangle x y 0))
    simp only [dist_zero_right] at h1
    rw [mem_closedBall, dist_zero_right]
    linarith
  -- (F2): `μ_V(B_{2r}(y)) < ∞`, as `B_{2r}(y)` is a compact subset of `U`.
  have hfin2 : V.weight (closedBall y (2 * r)) < ⊤ := by
    have hKU : closedBall y (2 * r) ⊆ U := by
      intro z hz
      apply hball0
      rw [mem_closedBall] at hz ⊢
      have h1 := dist_triangle z y 0
      simp only [dist_zero_right] at h1 ⊢
      linarith
    have hKm : MeasurableSet (closedBall y (2 * r)) := measurableSet_closedBall
    unfold RectifiableVarifold.weight
    rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall _ _) hKU).lintegral_lt_top
  -- (A): `∫_{B_ρ(0)} |H|ᵖ dμ_V < ∞`, from `(ρ^{p-n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ`.
  have hI0 : ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ := by
    have h1 : V.scaledLpNorm H p 0 ρ < ⊤ := lt_of_le_of_lt hK0 ENNReal.ofReal_lt_top
    unfold RectifiableVarifold.scaledLpNorm at h1
    have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0 : ℝ) < 1 / p)).mp h1
    have ha : ENNReal.ofReal (ρ ^ (p - n)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hρ _
    rcases ENNReal.mul_lt_top_iff.mp h2 with h | h | h
    · exact h.2
    · exact absurd h ha
    · rw [h]; exact ENNReal.zero_lt_top
  -- Step 1: constants.  `κ = (p - n)/(4p)`, `Λ = max(δ, 0)/κ + 1` (so `δ ≤ κΛ`),
  -- `A = e^{Λ/2} Λ/2`, `β = 1 - n/p > 0` and `c(t) = A (t/r)^β`.
  set κ := (p - n) / (4 * p) with hκ_def
  have hκ : 0 < κ := div_pos (by linarith) (by linarith)
  set Λ := max δ 0 / κ + 1 with hΛ_def
  have hΛ : 0 < Λ := by positivity
  have hκΛ : δ ≤ κ * Λ := by
    have h1 : κ * (max δ 0 / κ) = max δ 0 := by field_simp
    have h2 : κ * Λ = max δ 0 + κ := by rw [hΛ_def, mul_add, h1, mul_one]
    have h3 := le_max_left δ 0
    linarith
  set A := Real.exp (Λ / 2) / 2 * Λ with hA_def
  have hA0 : 0 ≤ A := by positivity
  set β := 1 - (n : ℝ) / p with hβ_def
  have hβ : 0 < β := by
    have : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hp
    linarith
  set c : ℝ → ℝ := fun t => A * (t / r) ^ β with hc_def
  have hc0 : ∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t := fun t ht _ =>
    mul_nonneg hA0 (Real.rpow_nonneg (div_nonneg ht.le hr.le) _)
  have hclim : Tendsto c (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => A * (t / r) ^ β) (𝓝 0) (𝓝 (A * ((0 : ℝ) / r) ^ β)) := by
      apply Tendsto.const_mul
      apply Tendsto.rpow_const
      · exact (continuous_id.div_const r).tendsto 0
      · exact Or.inr hβ.le
    rw [zero_div, Real.zero_rpow hβ.ne', mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  -- Step 5: transfer the a.e. bound near `y` to the support point `y`.
  refine Submission.aal_dge1_support_density_lower_bound n ℓ V.weight y (unitBallVolume n) r c hω
    hr hysupp hfin2 hc0 hclim ?_ ε hε
  -- Step 4: `Θⁿ(μ_V, x) = θ(x) ≥ 1` for `μ_V`-a.e. `x`.
  have hts := (Submission.aal_tangent_structure n ℓ hn U hU V).2.2
  filter_upwards [hts, hθ] with x hxd hx1 hxy t ht htr
  -- Steps 2–3 at such `x ∈ B̆_r(y)`: the `Lᵖ` monotonicity identity on `(0, r]`, with `S = 2r`.
  have hsubx : closedBall x (2 * r) ⊆ U := (hsub0 x hxy).trans hball0
  have hfin : ∫⁻ z in closedBall x (2 * r), ‖H z‖ₑ ^ p ∂V.weight < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (hsub0 x hxy)) hI0
  -- (K-mono): `K(x, r) ≤ K(0, ρ) ≤ δ ≤ κΛ`.
  have hKx : V.scaledLpNorm H p x r ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) := by
    have hKmono : V.scaledLpNorm H p x r ≤ V.scaledLpNorm H p 0 ρ := by
      unfold RectifiableVarifold.scaledLpNorm
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact mul_le_mul'
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr.le (by linarith) (by linarith)))
        (lintegral_mono_set ((closedBall_subset_closedBall (by linarith)).trans (hsub0 x hxy)))
    exact hKmono.trans (hK0.trans (ENNReal.ofReal_le_ofReal hκΛ))
  obtain ⟨F, G, hF, hG⟩ := Submission.aal_lp_monotonicity n ℓ hn p hp U hU V H hH x r (2 * r) Λ
    hr (by linarith) hΛ hsubx hfin hKx
  -- `Φ(t) = F(t) t⁻ⁿ μ_V(B_t(x)) + F(t) - 1` is nondecreasing on `(0, r]`: `G > 0`, `∫ g ≥ 0`.
  have hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ r →
      F s * ((V.weight (closedBall x s)).toReal / s ^ n) + (F s - 1) ≤
        F t * ((V.weight (closedBall x t)).toReal / t ^ n) + (F t - 1) := by
    intro s t hs hst htr
    obtain ⟨hG1, -, -, hEq⟩ := hG s t hs hst htr
    have hint : 0 ≤ ∫ z in closedBall x t \ closedBall x s,
        ‖(z - x) - V.tangentProj z (z - x)‖ ^ 2 / ‖z - x‖ ^ (n + 2) ∂V.weight :=
      integral_nonneg fun z => by positivity
    have hGpos : 0 < G s t := lt_of_lt_of_le (Real.exp_pos _) hG1
    have := mul_nonneg hGpos.le hint
    linarith
  -- `ω_n θ(x) ≤ (1 + c(t)) t⁻ⁿ μ_V(B_t(x)) + c(t)`, and `ω_n ≤ ω_n θ(x)`.
  have key := Submission.aal_dge1_density_le_monotone_bound n ℓ V.weight x (unitBallVolume n) r A β
    (V.mult x) F hω hr hβ (by linarith) (fun t ht htr => (hF t ht htr).2.2.1) hmono hxd t ht htr
  have h1 : unitBallVolume n ≤ unitBallVolume n * V.mult x := le_mul_of_one_le_right hω.le hx1
  show unitBallVolume n ≤ (1 + c t) * ((V.weight (closedBall x t)).toReal / t ^ n) + c t
  simp only [hc_def]
  linarith
/-- **Tilt bounded by height and curvature** (Simon Ch. 5, Lemma 2.5: the first inequality of (‡),
with the mean-curvature term of the documented erratum, for **every** `n`-dimensional subspace `T`).
There is `C₂ > 0` such that if 2.3 holds with `δ ∈ (0, 1/4]`, `ξ ∈ spt V ∩ B_{δρ}(0)` and
`σ ∈ (0, 2δρ]`, then
`C₂⁻¹ (σ⁻ⁿ ∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² dμ_V)^{1/2}
   ≤ σ⁻¹ sup{dist(x − ξ, T) : x ∈ spt V ∩ B_σ(ξ)} + (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}`.
With `h` the height supremum and `k` the curvature term (both finite), the proof applies
`aal_l1_tilt_height` on `B_σ(ξ) ⊆ B_ρ(0)` and bounds the height integral by `h² μ_V(B_σ(ξ))`.
The mass bound `aal_mass_upper_bound` and Hölder's inequality then give
`∫_{B_σ(ξ)} |H| dμ_V ≤ (C₀ ω_n)^{1−1/p} k σ^{n−1}`. Hence
`C₂ = (max {144 C₀ ω_n, 2 (C₀ ω_n)^{1−1/p}})^{1/2}`. -/
theorem aal_tilt_height_curvature_bound : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall (0 : Amb n ℓ) (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ENNReal.ofReal (C₂⁻¹ * Real.sqrt ((σ ^ n)⁻¹ * ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤ ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ := by
  intro n ℓ hn p hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
    linarith
  -- Step 1: `c = C₀ ω_n`, `c' = c^{1−1/p}`, `D = max {144 c, 2 c'}` and `C₂ = √D`.
  obtain ⟨C₀, hC₀, hmass⟩ := Submission.aal_mass_upper_bound n ℓ hn p hp
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨c, hc, hc_def⟩ : ∃ c : ℝ, 0 < c ∧ c = C₀ * unitBallVolume n := ⟨_, mul_pos hC₀ hω, rfl⟩
  obtain ⟨c', hc', hc'_def⟩ : ∃ c' : ℝ, 0 < c' ∧ c' = c ^ (1 - 1 / p) :=
    ⟨_, Real.rpow_pos_of_pos hc _, rfl⟩
  obtain ⟨D, hD1, hD2⟩ : ∃ D : ℝ, 144 * c ≤ D ∧ 2 * c' ≤ D :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  refine ⟨Real.sqrt D, Real.sqrt_pos.2 hDpos, ?_⟩
  intro U hU V H δ ρ hδ hδ4 hA ξ hξ σ hσ hσρ T hT
  have hA' := hA
  obtain ⟨hρ, hGMC, -, -, hBU, -, hK0⟩ := hA'
  -- `B_σ(ξ) ⊆ B_ρ(0) ⊆ U` and `σ ≤ ρ/2`, since `|ξ| ≤ δρ ≤ ρ/4` and `σ ≤ 2δρ`.
  have hξn : ‖ξ‖ ≤ δ * ρ := by
    have := hξ.2
    rwa [mem_closedBall, dist_zero_right] at this
  have hδρ : δ * ρ ≤ ρ / 4 := by nlinarith
  have hσρ2 : σ ≤ ρ / 2 := by nlinarith
  have hBB : closedBall ξ σ ⊆ closedBall (0 : Amb n ℓ) ρ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - ξ) + ξ‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - ξ‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ σ + δ * ρ := add_le_add hx hξn
      _ ≤ ρ := by linarith
  -- Step 2: the height is finite: `heightSup ξ σ T = h` with `0 ≤ h` (indeed `h ≤ σ`).
  have hs_le : V.heightSup ξ σ T ≤ ENNReal.ofReal σ := by
    refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
    have hx2 : ‖x - ξ‖ ≤ σ := by
      have := hx.2
      rwa [mem_closedBall, dist_eq_norm] at this
    calc infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ dist (x - ξ) 0 :=
          infDist_le_dist_of_mem T.zero_mem
      _ = ‖x - ξ‖ := by rw [dist_zero_right]
      _ ≤ σ := hx2
  obtain ⟨h, hh0, hs_eq⟩ : ∃ h : ℝ, 0 ≤ h ∧ V.heightSup ξ σ T = ENNReal.ofReal h :=
    ⟨_, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs_le)).symm⟩
  have hpt : ∀ x ∈ V.support ∩ closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ h := by
    intro x hx
    have hle : ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ))) ≤ V.heightSup ξ σ T :=
      le_iSup₂ (f := fun x (_ : x ∈ V.support ∩ closedBall ξ σ) =>
        ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ)))) x hx
    rw [hs_eq] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hh0).1 hle
  -- Step 3: the curvature term is finite, `K(ξ, σ) ≤ K(0, ρ) ≤ δ`; write `k = K(ξ, σ)` and
  -- `A = ∫_{B_σ(ξ)} |H|ᵖ dμ_V`, so that `k = σ^{(p−n)/p} A^{1/p}`.
  set A := ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ^ p ∂V.weight with hA_def
  have hσp : 0 < σ ^ (p - n) := Real.rpow_pos_of_pos hσ _
  have hKmono : V.scaledLpNorm H p ξ σ ≤ V.scaledLpNorm H p 0 ρ := by
    unfold RectifiableVarifold.scaledLpNorm
    refine ENNReal.rpow_le_rpow (mul_le_mul' ?_ (lintegral_mono_set hBB)) (by positivity)
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hσ.le (by linarith) (sub_nonneg.2 hp.le))
  have hK_ne : V.scaledLpNorm H p ξ σ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKmono.trans hK0)
  have hA_ne : A ≠ ⊤ := by
    intro hAtop
    apply hK_ne
    unfold RectifiableVarifold.scaledLpNorm
    rw [← hA_def, hAtop, ENNReal.mul_top (by simpa using hσp)]
    exact ENNReal.top_rpow_of_pos (by positivity)
  have hKeq : (V.scaledLpNorm H p ξ σ).toReal = σ ^ ((p - n) / p) * A.toReal ^ (1 / p) := by
    unfold RectifiableVarifold.scaledLpNorm
    rw [← hA_def, ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hσp.le,
      Real.mul_rpow hσp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hσ.le]
    congr 2
    ring
  obtain ⟨k, hk0, hk_eq⟩ : ∃ k : ℝ, 0 ≤ k ∧ V.scaledLpNorm H p ξ σ = ENNReal.ofReal k :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hK_ne).symm⟩
  have hAk : A.toReal ^ (1 / p) = σ ^ ((n - p) / p) * k := by
    rw [hk_eq, ENNReal.toReal_ofReal hk0] at hKeq
    rw [hKeq, ← mul_assoc, ← Real.rpow_add hσ]
    have : (n - p) / p + (p - n) / p = 0 := by field_simp; ring
    rw [this, Real.rpow_zero, one_mul]
  -- Step 5: the mass bound `μ_V(B_σ(ξ)) ≤ c σⁿ` (`|ξ| ≤ ρ/4`, `σ ≤ ρ/2`).
  have hm : V.weight (closedBall ξ σ) ≤ ENNReal.ofReal (c * σ ^ n) := by
    have := hmass U hU V H δ ρ hδ hδ4 hA ξ (hξn.trans hδρ) σ hσ hσρ2
    rwa [hc_def, mul_assoc]
  have hfin : V.weight (closedBall ξ σ) < ⊤ := lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  have hm_le : (V.weight (closedBall ξ σ)).toReal ≤ c * σ ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hm
  -- Step 4: `aal_l1_tilt_height` on `B_σ(ξ)`, and `∫_{B_σ(ξ)} dist(x − ξ, T)² dμ_V ≤ h² c σⁿ`
  -- because `μ_V`-a.e. point lies in `spt V`, where `dist(x − ξ, T) ≤ h` on `B_σ(ξ)`.
  have hLA := Submission.aal_l1_tilt_height n ℓ hn U hU V H hGMC ξ σ h hσ (hBB.trans hBU) hh0 T hT
    hpt
  have hsupp : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
    have h2 : ∀ᵐ x ∂V.weight, x ∈ V.carrier := by
      have : ∀ᵐ x ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier), x ∈ V.carrier :=
        ae_restrict_mem₀ V.nullMeasurableSet_carrier
      exact (withDensity_absolutelyContinuous _ _).ae_le this
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨V.carrier_subset hx2, hx1⟩
  have hheight : ∫ x in closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight ≤
      h ^ 2 * (c * σ ^ n) := by
    have hae : ∀ᵐ x ∂(V.weight.restrict (closedBall ξ σ)), x ∈ V.support ∩ closedBall ξ σ := by
      filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
        with x hx1 hx2
      exact ⟨hx1, hx2⟩
    have : IsFiniteMeasure (V.weight.restrict (closedBall ξ σ)) :=
      isFiniteMeasure_restrict.2 hfin.ne
    calc ∫ x in closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight
        ≤ ∫ x in closedBall ξ σ, h ^ 2 ∂V.weight := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun x => sq_nonneg _
          · exact integrable_const _
          · filter_upwards [hae] with x hx
            exact pow_le_pow_left₀ infDist_nonneg (hpt x hx) 2
      _ = h ^ 2 * (V.weight (closedBall ξ σ)).toReal := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
      _ ≤ h ^ 2 * (c * σ ^ n) := mul_le_mul_of_nonneg_left hm_le (by positivity)
  -- Step 6: Hölder, `∫_{B_σ(ξ)} |H| dμ_V ≤ A^{1/p} μ_V(B_σ(ξ))^{1−1/p} ≤ c' k σ^{n−1}`.
  have hHolder : ∫ x in closedBall ξ σ, ‖H x‖ ∂V.weight ≤
      A.toReal ^ (1 / p) * (V.weight (closedBall ξ σ)).toReal ^ (1 - 1 / p) := by
    by_cases hg : AEStronglyMeasurable (fun x => ‖H x‖) (V.weight.restrict (closedBall ξ σ))
    · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _) hg]
      have hcongr : ∫⁻ x in closedBall ξ σ, ENNReal.ofReal ‖H x‖ ∂V.weight =
          ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ∂V.weight := by
        congr 1; ext x; exact ofReal_norm (H x)
      rw [hcongr]
      have key := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
        (μ := V.weight.restrict (closedBall ξ σ)) (f := fun x => ‖H x‖) one_pos
        (by linarith : (1 : ℝ) ≤ p) hg
      simp only [eLpNorm'_eq_lintegral_enorm, enorm_norm, ENNReal.rpow_one, div_one,
        Measure.restrict_apply_univ] at key
      rw [← hA_def] at key
      have hR : A ^ (1 / p) * V.weight (closedBall ξ σ) ^ (1 - 1 / p) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hA_ne)
          (ENNReal.rpow_ne_top_of_nonneg hq hfin.ne)
      calc (∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ∂V.weight).toReal
          ≤ (A ^ (1 / p) * V.weight (closedBall ξ σ) ^ (1 - 1 / p)).toReal :=
            ENNReal.toReal_mono hR key
        _ = A.toReal ^ (1 / p) * (V.weight (closedBall ξ σ)).toReal ^ (1 - 1 / p) := by
            rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
    · rw [integral_undef (fun hi => hg hi.aestronglyMeasurable)]
      positivity
  have hcurv : ∫ x in closedBall ξ σ, ‖H x‖ ∂V.weight ≤ c' * k * σ ^ (n - 1) := by
    calc ∫ x in closedBall ξ σ, ‖H x‖ ∂V.weight
        ≤ A.toReal ^ (1 / p) * (V.weight (closedBall ξ σ)).toReal ^ (1 - 1 / p) := hHolder
      _ ≤ A.toReal ^ (1 / p) * (c * σ ^ n) ^ (1 - 1 / p) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hm_le hq)
            (by positivity)
      _ = c' * k * σ ^ (n - 1) := by
          rw [hAk, hc'_def, Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast σ n,
            ← Real.rpow_mul hσ.le]
          have hpow : (σ : ℝ) ^ (n - 1 : ℕ) = σ ^ ((n : ℝ) - 1) := by
            rw [← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]
          rw [hpow]
          have : σ ^ ((n - p) / p) * k * (c ^ (1 - 1 / p) * σ ^ ((n : ℝ) * (1 - 1 / p)))
              = c ^ (1 - 1 / p) * k * (σ ^ ((n - p) / p) * σ ^ ((n : ℝ) * (1 - 1 / p))) := by
            ring
          rw [this, ← Real.rpow_add hσ]
          congr 2
          field_simp
          ring
  -- Step 7: with `X` the tilt integral and `a = σ⁻¹ h`,
  -- `σ⁻ⁿ X ≤ 144 c a² + 4 c' a k ≤ D (a + k)²`; take square roots.
  set X := ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
    with hX_def
  have hX : X ≤ 144 * (σ ^ 2)⁻¹ * (h ^ 2 * (c * σ ^ n)) + 4 * h * (c' * k * σ ^ (n - 1)) := by
    have h1 : 144 * (σ ^ 2)⁻¹ * ∫ x in closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ^ 2
        ∂V.weight ≤ 144 * (σ ^ 2)⁻¹ * (h ^ 2 * (c * σ ^ n)) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    have h2 : 4 * h * ∫ x in closedBall ξ σ, ‖H x‖ ∂V.weight ≤ 4 * h * (c' * k * σ ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left hcurv (by positivity)
    linarith
  obtain ⟨a, ha0, ha_def⟩ : ∃ a : ℝ, 0 ≤ a ∧ a = σ⁻¹ * h := ⟨_, by positivity, rfl⟩
  have hE : (σ ^ n)⁻¹ * (144 * (σ ^ 2)⁻¹ * (h ^ 2 * (c * σ ^ n)) + 4 * h * (c' * k * σ ^ (n - 1)))
      = 144 * c * a ^ 2 + 4 * c' * a * k := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [ha_def, Nat.add_sub_cancel]
    field_simp
    ring
  have hcomb : (σ ^ n)⁻¹ * X ≤ D * (a + k) ^ 2 := by
    calc (σ ^ n)⁻¹ * X
        ≤ (σ ^ n)⁻¹ * (144 * (σ ^ 2)⁻¹ * (h ^ 2 * (c * σ ^ n)) + 4 * h * (c' * k * σ ^ (n - 1))) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 144 * c * a ^ 2 + 4 * c' * a * k := hE
      _ ≤ D * (a + k) ^ 2 := by
          linarith [mul_nonneg (sub_nonneg.2 hD1) (sq_nonneg a),
            mul_nonneg (mul_nonneg (sub_nonneg.2 hD2) ha0) hk0, mul_nonneg hDpos.le (sq_nonneg k)]
  have hfinal : (Real.sqrt D)⁻¹ * Real.sqrt ((σ ^ n)⁻¹ * X) ≤ σ⁻¹ * h + k := by
    rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 hDpos), ← ha_def]
    calc Real.sqrt ((σ ^ n)⁻¹ * X) ≤ Real.sqrt (D * (a + k) ^ 2) := Real.sqrt_le_sqrt hcomb
      _ = Real.sqrt D * (a + k) := by
          rw [Real.sqrt_mul hDpos.le, Real.sqrt_sq (by positivity)]
  -- Step 8: back in `[0, ∞]`, `ofReal (σ⁻¹ h + k) = ofReal σ⁻¹ * heightSup + scaledLpNorm`.
  calc ENNReal.ofReal ((Real.sqrt D)⁻¹ * Real.sqrt ((σ ^ n)⁻¹ * X))
      ≤ ENNReal.ofReal (σ⁻¹ * h + k) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ := by
        rw [ENNReal.ofReal_add (by positivity) hk0, ENNReal.ofReal_mul (by positivity), hs_eq,
          hk_eq]

/-- **Simon Ch. 5, 2.4** (pinched density bounds, with explicit constants), `p > n`.  There are
`C_P ≥ 1` and `δ_P ∈ (0, 1/8]` with `C_P δ_P ≤ 1/2` such that if 2.3 holds with `δ ∈ (0, δ_P]`,
`|y| ≤ 3δρ` and `s ∈ (0, ρ/2]`, then `μ_V(B_s(y)) ≤ (1 + C_P δ) ω_n sⁿ`, and if `y ∈ spt V` also
`μ_V(B_s(y)) ≥ (1 − C_P δ) ω_n sⁿ` and `∫_{B_s(y)} |(x − y) − p_{T_xM}(x − y)|² / |x − y|^{n+2} dμ_V
≤ C_P ω_n δ`.  The `Lᵖ` monotonicity formula is applied at `y` with `Λ = δ/κ`, `κ = (p − n)/(4p)`,
and outer radius `R = (1 − 4δ)ρ`, inside `B_{(1−3δ)ρ}(y) ⊆ B_ρ(0)`: the monotone quantity
`Φ(t) = F(t) t⁻ⁿ μ_V(B_t(y)) + F(t) − 1` has `Φ(R) ≤ e^Λ (1 + δ)(1 − 4δ)⁻ⁿ ω_n + Λ`, and `Φ ≥ ω_n`
on `(0, R]` when `y ∈ spt V`, by the density lower bound at `y`. -/
theorem aal_pinched_density_bounds : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ Cp δp : ℝ, 1 ≤ Cp ∧ 0 < δp ∧ δp ≤ 1 / 8 ∧ Cp * δp ≤ 1 / 2 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δp → V.AllardHypotheses H p δ ρ → ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + Cp * δ) * (unitBallVolume n * s ^ n)) ∧ (y ∈ V.support → ENNReal.ofReal ((1 - Cp * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Cp * unitBallVolume n * δ)) := by
  intro n ℓ hn p hp
  have hp0 : 0 < p := (Nat.cast_pos.2 hn).trans hp
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = (p - n) / (4 * p) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκ_def]; exact div_pos (sub_pos.2 hp) (by linarith)
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hα : 0 < 1 - (n : ℝ) / p := sub_pos.2 ((div_lt_one₀ hp0).2 hp)
  -- Steps 1–2: the constants and the elementary inequalities (E3)–(E5) at `t = δ`.
  obtain ⟨Cp, δp, hCp, hδp, hδp8, hδpκ, hCpδp, hineq⟩ :=
    Submission.aal_pinched_constants n κ (unitBallVolume n) hκ hω
  refine ⟨Cp, δp, hCp, hδp, hδp8, hCpδp, ?_⟩
  intro U hU V H δ ρ hδ hδδp hA y hy s hs hsρ
  have hρ : 0 < ρ := hA.1
  have hδ8 : δ ≤ 1 / 8 := hδδp.trans hδp8
  have hδρ : 0 ≤ (1 / 8 - δ) * ρ := mul_nonneg (by linarith) hρ.le
  obtain ⟨hi, hii, hiii⟩ := hineq δ hδ hδδp
  -- Step 3: `Λ = δ/κ ∈ (0, 1]`, `R = (1 − 4δ)ρ < S = (1 − 3δ)ρ ≤ ρ`, and `s ≤ ρ/2 ≤ R`.
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = δ / κ := ⟨_, rfl⟩
  rw [← hΛ_def] at hi hii hiii
  have hΛ : 0 < Λ := by rw [hΛ_def]; exact div_pos hδ hκ
  have hΛ1 : Λ ≤ 1 := by rw [hΛ_def]; exact (div_le_one₀ hκ).2 (hδδp.trans hδpκ)
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = (1 - 4 * δ) * ρ := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : ℝ, S = (1 - 3 * δ) * ρ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hR_def]; exact mul_pos (by linarith) hρ
  have hRS : R < S := by rw [hR_def, hS_def]; linarith [mul_pos hδ hρ]
  have hSρ : S ≤ ρ := by rw [hS_def]; linarith [mul_pos hδ hρ]
  have hsR : s ≤ R := by rw [hR_def]; linarith
  -- `B_r(y) ⊆ B_ρ(0)` for `r ≤ S`, since `|y| ≤ 3δρ`.
  have hball : ∀ r, r ≤ S → closedBall y r ⊆ closedBall 0 ρ := fun r hr =>
    closedBall_subset_closedBall' (by rw [dist_zero_right]; rw [hS_def] at hr; linarith)
  obtain ⟨hSU, hHS, -, -⟩ := Submission.aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y S
    (hR.trans hRS) hSρ (hball S le_rfl)
  obtain ⟨-, -, hKR, hmR⟩ := Submission.aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y R hR
    (hRS.le.trans hSρ) (hball R hRS.le)
  have hKR' : V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) := by
    rwa [← hκ_def, hΛ_def, mul_div_cancel₀ δ hκ.ne']
  obtain ⟨F, G, hF, hG⟩ := Submission.aal_lp_monotonicity n ℓ hn p hp U hU V H hA.2.1 y R S Λ hR
    hRS hΛ hSU hHS hKR'
  -- `μ_V(B_t(y)) < ∞` for `t ≤ R`.
  have hfin : ∀ t, t ≤ R → V.weight (closedBall y t) ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono (closedBall_subset_closedBall ht)).trans hmR)
  -- `e^{−Λ} ≤ F ≤ e^Λ` and `|F − 1| ≤ Λ` on `(0, R]`.
  have hF' : ∀ r, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ := by
    intro r hr hrR
    obtain ⟨h1, h2, -, h4⟩ := hF r hr hrR
    exact ⟨h1, h2, (h4 hΛ1).trans (mul_le_of_le_one_right hΛ.le
      (Real.rpow_le_one (div_nonneg hr.le hR.le) ((div_le_one₀ hR).2 hrR) hα.le))⟩
  -- `Φ(t) = F(t) t⁻ⁿ μ_V(B_t(y)) + F(t) − 1` is nondecreasing on `(0, R]`.
  have hmono : ∀ u t : ℝ, 0 < u → u ≤ t → t ≤ R →
      F u * ((V.weight (closedBall y u)).toReal / u ^ n) + (F u - 1) ≤
        F t * ((V.weight (closedBall y t)).toReal / t ^ n) + (F t - 1) := by
    intro u t hu hut htR
    obtain ⟨hG1, -, -, hGeq⟩ := hG u t hu hut htR
    have hI : 0 ≤ ∫ x in closedBall y t \ closedBall y u,
        ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight :=
      integral_nonneg fun x => div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    linarith [mul_nonneg ((Real.exp_pos (-Λ)).le.trans hG1) hI]
  -- (3.1): `Φ(R) ≤ e^Λ (1 + δ)(1 − 4δ)⁻ⁿ ω_n + Λ`, from `μ_V(B_R(y)) ≤ (1 + δ) ω_n ρⁿ`.
  have hPhiR : F R * ((V.weight (closedBall y R)).toReal / R ^ n) + (F R - 1) ≤
      Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + Λ := by
    obtain ⟨-, hF2, hF3⟩ := hF' R hR le_rfl
    have h4 : 0 < 1 - 4 * δ := by linarith
    have hX0 : 0 ≤ (V.weight (closedBall y R)).toReal / R ^ n := by positivity
    have hX : (V.weight (closedBall y R)).toReal / R ^ n ≤
        (1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n := by
      have hRn : R ^ n = (1 - 4 * δ) ^ n * ρ ^ n := by rw [hR_def, mul_pow]
      rw [div_le_iff₀ (pow_pos hR n), hRn]
      calc (V.weight (closedBall y R)).toReal ≤ (1 + δ) * (unitBallVolume n * ρ ^ n) :=
            ENNReal.toReal_le_of_le_ofReal (by positivity) hmR
        _ = (1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n * ((1 - 4 * δ) ^ n * ρ ^ n) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero n h4.ne')]
            ring
    linarith [abs_le.1 hF3, mul_le_mul_of_nonneg_right hF2 hX0,
      mul_le_mul_of_nonneg_left hX (Real.exp_pos Λ).le]
  -- Step 4, (P.i): `s⁻ⁿ μ_V(B_s(y)) ≤ e^{2Λ} (1 + δ)(1 − 4δ)⁻ⁿ ω_n + 2 e^Λ Λ ≤ (1 + C_P δ) ω_n`.
  obtain ⟨hFs1, hFs2, hFs3⟩ := hF' s hs hsR
  have hXs0 : 0 ≤ (V.weight (closedBall y s)).toReal / s ^ n := by positivity
  have hXs : (V.weight (closedBall y s)).toReal / s ^ n ≤ (1 + Cp * δ) * unitBallVolume n := by
    refine le_trans ?_ hi
    have h1 : Real.exp (-Λ) * ((V.weight (closedBall y s)).toReal / s ^ n) ≤
        Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + 2 * Λ := by
      linarith [mul_le_mul_of_nonneg_right hFs1 hXs0, abs_le.1 hFs3, hmono s R hs hsR le_rfl]
    calc (V.weight (closedBall y s)).toReal / s ^ n
        = Real.exp Λ * (Real.exp (-Λ) * ((V.weight (closedBall y s)).toReal / s ^ n)) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp Λ * (Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + 2 * Λ) := by
          gcongr
      _ = Real.exp (2 * Λ) * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) +
            2 * Real.exp Λ * Λ := by
          rw [two_mul Λ, Real.exp_add]; ring
  refine ⟨?_, fun hysupp => ?_⟩
  · rw [div_le_iff₀ (pow_pos hs n), mul_assoc] at hXs
    rw [← ENNReal.ofReal_toReal (hfin s hsR)]
    exact ENNReal.ofReal_le_ofReal hXs
  -- Step 5: `Φ ≥ ω_n` on `(0, R]`, from the lower density bound at `y ∈ spt V ∩ B̆_ρ(0)`.
  have hy_mem : y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ :=
    ⟨hysupp, by rw [mem_ball, dist_zero_right]; linarith⟩
  have hPhi_ge : ∀ t, 0 < t → t ≤ R →
      unitBallVolume n ≤ F t * ((V.weight (closedBall y t)).toReal / t ^ n) + (F t - 1) := by
    intro t ht htR
    refine Submission.aal_monotone_quantity_ge_density n (1 - (n : ℝ) / p) (unitBallVolume n) R Λ
      (fun u => (V.weight (closedBall y u)).toReal) F hα hω hR
      (fun u hu huR => (hF u hu huR).2.2.2 hΛ1) hmono (fun ε hε => ?_) t ht htR
    filter_upwards [Submission.aal_density_ge_one n ℓ hn p hp U hU V H δ ρ hA y hy_mem ε hε,
      Ioo_mem_nhdsGT hR] with u hu hu'
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin u hu'.2.le)).1 hu
  refine ⟨?_, ?_⟩
  · -- Step 6, (P.ii): `s⁻ⁿ μ_V(B_s(y)) ≥ e^{−Λ} (ω_n − Λ) ≥ (1 − C_P δ) ω_n`.
    have hX : Real.exp (-Λ) * (unitBallVolume n - Λ) ≤
        (V.weight (closedBall y s)).toReal / s ^ n := by
      have h1 : unitBallVolume n - Λ ≤
          Real.exp Λ * ((V.weight (closedBall y s)).toReal / s ^ n) := by
        linarith [mul_le_mul_of_nonneg_right hFs2 hXs0, abs_le.1 hFs3, hPhi_ge s hs hsR]
      calc Real.exp (-Λ) * (unitBallVolume n - Λ)
          ≤ Real.exp (-Λ) * (Real.exp Λ * ((V.weight (closedBall y s)).toReal / s ^ n)) := by
            gcongr
        _ = (V.weight (closedBall y s)).toReal / s ^ n := by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hms := (le_div_iff₀ (pow_pos hs n)).1 (hii.trans hX)
    rw [mul_assoc] at hms
    rw [← ENNReal.ofReal_toReal (hfin s hsR)]
    exact ENNReal.ofReal_le_ofReal hms
  · -- Step 7, (P.iii): each annular integral is `≤ e^Λ (Φ(R) − ω_n) ≤ C_P ω_n δ`.
    refine Submission.aal_lintegral_closedBall_le_of_annuli n ℓ V.weight
      (fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) y s
      (Cp * unitBallVolume n * δ) hs
      (fun x => div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)) (by simp)
      fun t ht hts => ?_
    obtain ⟨hG1, -, hint, hGeq⟩ := hG t s ht hts.le hsR
    refine ⟨hint, ?_⟩
    beta_reduce
    set I := ∫ x in closedBall y s \ closedBall y t,
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight
    have hI : 0 ≤ I :=
      integral_nonneg fun x => div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have h1 : Real.exp (-Λ) * I ≤
        Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + Λ - unitBallVolume n := by
      linarith [mul_le_mul_of_nonneg_right hG1 hI, hmono s R hs hsR le_rfl,
        hPhi_ge t ht (hts.le.trans hsR)]
    calc I = Real.exp Λ * (Real.exp (-Λ) * I) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp Λ *
          (Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + Λ - unitBallVolume n) := by
          gcongr
      _ ≤ Cp * unitBallVolume n * δ := hiii
/-- Simon Ch. 5, proof of Lemma 2.5, steps (1)–(6) (pp. 109–110), with `α = 1/(2n+2)`: for
`δ ≤ δ₁ = δ_P` put `A = δ^α`.  A maximal disjoint family of balls `B_{Aσ/2}(y)` centred in
`spt V ∩ B_σ(ξ)` gives an `Aσ`-net `F` with `#F Aⁿ ≤ 4^{n+1}`; the conical-excess bound at the net
points and Chebyshev give `x₀ ∈ B_{Aσ}(ξ)` with tangent plane `T` and `|p_{T^⊥}(x₀ − y)| < C₆ Aσ`
for `y ∈ F`, so `dist(x − ξ, T) ≤ (C₆ + 2) Aσ` on `spt V ∩ B_σ(ξ)`. -/
theorem aal_height_bound_small_delta : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
    ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ 0 < C₁ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U →
    ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ →
    V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall (0 : Amb n ℓ) (δ * ρ),
    ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
    ∀ x ∈ V.support ∩ closedBall ξ σ,
      infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ C₁ * δ ^ (1 / (2 * (n : ℝ) + 2)) * σ := by
  intro n ℓ hn p hp
  -- Step 1: `δ₁ = δ_P`, `C₅ = 4^{n+1} 2^{n+2} C_P ω_n`, `C₆ = (4 C₅ / ω_n)^{1/2}`, `C₁ = C₆ + 2`.
  obtain ⟨Cp, δp, hCp1, hδp, hδp8, hCpδp, hpinch⟩ :=
    Submission.aal_pinched_density_bounds n ℓ hn p hp
  set ω : ℝ := unitBallVolume n
  have hω : 0 < ω :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hCp : 0 < Cp := by linarith
  set C₅ : ℝ := 4 ^ (n + 1) * 2 ^ (n + 2) * Cp * ω with hC₅_def
  have hC₅ : 0 < C₅ := by positivity
  set C₆ : ℝ := Real.sqrt (4 * C₅ / ω)
  have hC₆ : 0 < C₆ := Real.sqrt_pos.2 (by positivity)
  have hC₆sq : C₆ ^ 2 = 4 * C₅ / ω := Real.sq_sqrt (by positivity)
  refine ⟨δp, C₆ + 2, hδp, by positivity, ?_⟩
  intro U hU V H δ ρ hδ hδδp hyp ξ hξ σ hσ hσδ
  -- Step 2: the pinched bounds hold at centres in `B_σ(ξ)` (`|y| ≤ 3δρ`), radii `≤ 2σ ≤ ρ/2`.
  have hρ : 0 < ρ := hyp.1
  obtain ⟨hξS, hξB⟩ := hξ
  have hξn : ‖ξ‖ ≤ δ * ρ := mem_closedBall_zero_iff.1 hξB
  have hδ8 : δ ≤ 1 / 8 := hδδp.trans hδp8
  have hCpδ : Cp * δ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hδδp hCp.le).trans hCpδp
  have h2σ : 2 * σ ≤ ρ / 2 := by nlinarith [mul_le_mul_of_nonneg_right hδ8 hρ.le]
  set α : ℝ := 1 / (2 * (n : ℝ) + 2) with hα_def
  set A : ℝ := δ ^ α with hA_def
  have hA : 0 < A := Real.rpow_pos_of_pos hδ α
  have hA1 : A ≤ 1 := Real.rpow_le_one hδ.le (by linarith) (by positivity)
  have hAσ : A * σ ≤ σ := mul_le_of_le_one_left hσ.le hA1
  have hAδ : A ^ (2 * n + 2) = δ := by
    rw [hA_def, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    have : α * ((2 * n + 2 : ℕ) : ℝ) = 1 := by
      rw [hα_def]; push_cast; field_simp
    rw [this, Real.rpow_one]
  set S := V.support ∩ closedBall ξ σ
  have hball : ∀ y ∈ closedBall ξ σ, ‖y‖ ≤ 3 * δ * ρ := by
    intro y hy
    have hyξ : ‖y - ξ‖ ≤ σ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    linarith [norm_sub_norm_le y ξ]
  have hlow : ∀ y ∈ S, ∀ t : ℝ, 0 < t → t ≤ 2 * σ →
      ENNReal.ofReal (1 / 2 * (ω * t ^ n)) ≤ V.weight (closedBall y t) := by
    intro y hy t ht ht2
    refine (ENNReal.ofReal_le_ofReal ?_).trans
      ((hpinch U hU V H δ ρ hδ hδδp hyp y (hball y hy.2) t ht (by linarith)).2 hy.1).1
    have : 0 ≤ ω * t ^ n := by positivity
    nlinarith
  have hup : V.weight (closedBall ξ (2 * σ)) ≤ ENNReal.ofReal (2 * (ω * (2 * σ) ^ n)) := by
    refine (hpinch U hU V H δ ρ hδ hδδp hyp ξ (hball ξ (mem_closedBall_self hσ.le)) (2 * σ)
      (by linarith) h2σ).1.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ ω * (2 * σ) ^ n := by positivity
    nlinarith
  -- Step 3: for `y ∈ S`, `B_σ(ξ) ⊆ B_{2σ}(y)` and
  -- `∫_{B_{2σ}(y)} |p_x^⊥(x − y)|² dμ_V ≤ (2σ)^{n+2} C_P ω_n δ =: K`.
  set K : ℝ := (2 * σ) ^ (n + 2) * (Cp * ω * δ) with hK_def
  have hK : ∀ y ∈ S, ∫⁻ x in closedBall ξ σ,
      ENNReal.ofReal (‖(x - y) - V.tangentProj x (x - y)‖ ^ 2) ∂V.weight ≤ ENNReal.ofReal K := by
    intro y hy
    have hsub : closedBall ξ σ ⊆ closedBall y (2 * σ) :=
      closedBall_subset_closedBall' (by rw [dist_comm]; linarith [mem_closedBall.1 hy.2])
    calc ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (‖(x - y) - V.tangentProj x (x - y)‖ ^ 2)
          ∂V.weight
        ≤ ∫⁻ x in closedBall y (2 * σ),
            ENNReal.ofReal (‖(x - y) - V.tangentProj x (x - y)‖ ^ 2) ∂V.weight :=
          lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal ((2 * σ) ^ (n + 2)) * ∫⁻ x in closedBall y (2 * σ),
            ENNReal.ofReal (‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2))
              ∂V.weight :=
          Submission.aal_normal_sq_lintegral_le_conical n ℓ V.weight V.tangentProj y (2 * σ)
            (by linarith)
      _ ≤ ENNReal.ofReal ((2 * σ) ^ (n + 2)) * ENNReal.ofReal (Cp * ω * δ) := by
          gcongr
          exact ((hpinch U hU V H δ ρ hδ hδδp hyp y (hball y hy.2) (2 * σ) (by linarith)
            h2σ).2 hy.1).2
      _ = ENNReal.ofReal K := (ENNReal.ofReal_mul (by positivity)).symm
  -- Step 4: a maximal disjoint family of balls `B_{Aσ/2}(y)`, `y ∈ S`, is an `Aσ`-net of `S`
  -- with `#F (1/2) ω_n (Aσ/2)ⁿ ≤ μ_V(B_{2σ}(ξ)) ≤ 2 ω_n (2σ)ⁿ`, i.e. `#F Aⁿ ≤ 4^{n+1}`.
  obtain ⟨F, hFS, hcard, hnet⟩ := Submission.aal_packing_finite_net (Amb n ℓ) V.weight S
    (closedBall ξ (2 * σ)) (A * σ / 2) (1 / 2 * (ω * (A * σ / 2) ^ n)) (2 * (ω * (2 * σ) ^ n))
    (by positivity) (by positivity) (by positivity) hup fun y hy =>
      ⟨closedBall_subset_closedBall' (by linarith [mem_closedBall.1 hy.2]),
        hlow y hy _ (by positivity) (by linarith)⟩
  have hcardA : (F.card : ℝ) * A ^ n ≤ 4 ^ (n + 1) := by
    have hc : 0 < ω * σ ^ n / (2 * 2 ^ n) := by positivity
    refine le_of_mul_le_mul_right ?_ hc
    calc (F.card : ℝ) * A ^ n * (ω * σ ^ n / (2 * 2 ^ n))
        = (F.card : ℝ) * (1 / 2 * (ω * (A * σ / 2) ^ n)) := by rw [div_pow, mul_pow]; ring
      _ ≤ 2 * (ω * (2 * σ) ^ n) := hcard
      _ = 4 ^ (n + 1) * (ω * σ ^ n / (2 * 2 ^ n)) := by
        rw [show (4 : ℝ) ^ (n + 1) = 2 * 2 ^ n * (2 * 2 ^ n) by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_succ]; ring]
        field_simp
        ring
  -- Step 5: Chebyshev with `λ = (C₆ Aσ)² = (4 C₅ / ω_n) δ^{1 − 2αn} σ²`, using
  -- `#F K ≤ C₅ A^{n+2} σ^{n+2} < λ (1/2) ω_n (Aσ)ⁿ ≤ λ μ_V(B_{Aσ}(ξ))`.
  obtain ⟨hae, hmeas, -⟩ := Submission.aal_tangent_structure n ℓ hn U hU V
  set lam : ℝ := (C₆ * A * σ) ^ 2 with hlam_def
  have hlam : 0 < lam := by positivity
  have hcheb : ENNReal.ofReal ((F.card : ℝ) * K) <
      ENNReal.ofReal lam * V.weight (closedBall ξ (A * σ)) := by
    have hlt : (F.card : ℝ) * K < lam * (1 / 2 * (ω * (A * σ) ^ n)) := by
      have hY : 0 < 2 ^ (n + 2) * σ ^ (n + 2) * Cp * ω * A ^ (n + 2) := by positivity
      calc (F.card : ℝ) * K
          = (F.card : ℝ) * A ^ n * (2 ^ (n + 2) * σ ^ (n + 2) * Cp * ω * A ^ (n + 2)) := by
            rw [hK_def, ← hAδ]; ring
        _ ≤ 4 ^ (n + 1) * (2 ^ (n + 2) * σ ^ (n + 2) * Cp * ω * A ^ (n + 2)) :=
            mul_le_mul_of_nonneg_right hcardA hY.le
        _ = C₅ * (A ^ (n + 2) * σ ^ (n + 2)) := by rw [hC₅_def]; ring
        _ < 2 * C₅ * (A ^ (n + 2) * σ ^ (n + 2)) := by
            have : 0 < C₅ * (A ^ (n + 2) * σ ^ (n + 2)) := by positivity
            linarith
        _ = lam * (1 / 2 * (ω * (A * σ) ^ n)) := by
            rw [hlam_def, mul_pow, mul_pow, hC₆sq]
            field_simp
            ring
    calc ENNReal.ofReal ((F.card : ℝ) * K)
        < ENNReal.ofReal (lam * (1 / 2 * (ω * (A * σ) ^ n))) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt
      _ = ENNReal.ofReal lam * ENNReal.ofReal (1 / 2 * (ω * (A * σ) ^ n)) :=
          ENNReal.ofReal_mul hlam.le
      _ ≤ ENNReal.ofReal lam * V.weight (closedBall ξ (A * σ)) := by
          gcongr
          exact hlow ξ ⟨hξS, mem_closedBall_self hσ.le⟩ (A * σ) (by positivity) (by linarith)
  obtain ⟨x₀, hx₀, T, hT, -, hsmall⟩ := Submission.aal_good_tangent_point n ℓ V.weight
    V.tangentProj hmeas hae ξ (A * σ) σ K lam F hlam hAσ (fun y hy => hK y (hFS hy)) hcheb
  refine ⟨T, hT, ?_⟩
  -- Steps 6–7: `|p_{T^⊥}(x₀ − y)| ≤ C₆ Aσ` on the net and `|x₀ − ξ| ≤ Aσ`, so
  -- `dist(x − ξ, T) ≤ C₆ Aσ + 2Aσ = C₁ δ^{1/(2n+2)} σ` on `spt V ∩ B_σ(ξ)`.
  have hb : ∀ y ∈ F, ‖(x₀ - y) - T.starProjection (x₀ - y)‖ ≤ C₆ * A * σ := fun y hy =>
    ((pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (hsmall y hy)).le
  have hx₀ξ : ‖x₀ - ξ‖ ≤ A * σ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx₀
  have hnet' : ∀ x ∈ S, ∃ y ∈ F, dist x y ≤ A * σ := fun x hx => by
    obtain ⟨z, hz, hd⟩ := hnet x hx
    exact ⟨z, hz, by linarith⟩
  intro x hx
  calc infDist (x - ξ) (T : Set (Amb n ℓ))
      ≤ C₆ * A * σ + 2 * (A * σ) :=
        Submission.aal_height_of_net_plane n ℓ T ξ x₀ S F (A * σ) (C₆ * A * σ) hx₀ξ hb hnet' x hx
    _ = (C₆ + 2) * A * σ := by ring

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)**, corrected as in the contract.
Every `n`-plane satisfies the first inequality of (‡) with the constant `C₂` of
`aal_tilt_height_curvature_bound`.  For `δ ≤ δ₁` the plane of `aal_height_bound_small_delta` has
height `≤ C₁ δ^{1/(2n+2)} σ`; for `δ > δ₁` the plane `ℝⁿ × {0}` has height `≤ σ` and
`1 ≤ δ₁^{-1/(2n+2)} δ^{1/(2n+2)}`.  So any `C ≥ max {C₂, C₁, δ₁^{-1/(2n+2)}}` works. -/
theorem affine_approximation_lemma : AffineApproximationLemma := by
  intro n ℓ hn p hp
  obtain ⟨C₂, hC₂, htilt⟩ := Submission.aal_tilt_height_curvature_bound n ℓ hn p hp
  obtain ⟨δ₁, C₁, hδ₁, -, hheight⟩ := Submission.aal_height_bound_small_delta n ℓ hn p hp
  set a : ℝ := 1 / (2 * (n : ℝ) + 2) with ha_def
  have ha : 0 ≤ a := by rw [ha_def]; positivity
  have hδ₁a : 0 < δ₁ ^ a := Real.rpow_pos_of_pos hδ₁ a
  obtain ⟨C, hC₂C, hC₁C, hδ₁C⟩ : ∃ C : ℝ, C₂ ≤ C ∧ C₁ ≤ C ∧ (δ₁ ^ a)⁻¹ ≤ C :=
    ⟨max (max C₂ C₁) (δ₁ ^ a)⁻¹, le_max_of_le_left (le_max_left _ _),
      le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩
  refine ⟨C, hC₂.trans_le hC₂C, ?_⟩
  intro U hU V H δ ρ hδ hδ4 hA ξ hξ σ hσ hσδ
  -- Step 2: the first inequality holds for every `n`-plane, since `C⁻¹ ≤ C₂⁻¹`.
  have hfirst : ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
      ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ *
          ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
        ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ := fun T hT =>
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (inv_anti₀ hC₂ hC₂C)
      (Real.sqrt_nonneg _))).trans (htilt U hU V H δ ρ hδ hδ4 hA ξ hξ σ hσ hσδ T hT)
  -- A height bound `b` on `spt V ∩ B_σ(ξ)` gives `σ⁻¹ h ≤ σ⁻¹ b`.
  have hheight_le : ∀ (T : Submodule ℝ (Amb n ℓ)) (b : ℝ),
      (∀ x ∈ V.support ∩ closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ b) →
        ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T ≤ ENNReal.ofReal (σ⁻¹ * b) := by
    intro T b hb
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hσ.le)]
    gcongr
    exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (hb x hx)
  by_cases hsmall : δ ≤ δ₁
  · -- Steps 4–7 (`δ ≤ δ₁`): the plane of `aal_height_bound_small_delta`.
    obtain ⟨T, hT, hTh⟩ := hheight U hU V H δ ρ hδ hsmall hA ξ hξ σ hσ hσδ
    refine ⟨T, hT, hfirst T hT, (hheight_le T _ hTh).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [show σ⁻¹ * (C₁ * δ ^ a * σ) = C₁ * δ ^ a by field_simp]
    exact mul_le_mul_of_nonneg_right hC₁C (Real.rpow_nonneg hδ.le a)
  · -- Step 3 (`δ > δ₁`): `T = ℝⁿ × {0}`, whose height over `B_σ(ξ)` is at most `σ`.
    have hlarge : δ₁ < δ := not_le.1 hsmall
    have hfin : Module.finrank ℝ (horizontalPlane n ℓ) = n := by
      have hli : LinearIndependent ℝ
          (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) : Fin n → Amb n ℓ) := by
        simpa [Function.comp_def] using
          (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).orthonormal.linearIndependent.comp
            (Fin.castAdd ℓ) (Fin.castAdd_injective n ℓ)
      rw [horizontalPlane, finrank_span_eq_card hli, Fintype.card_fin]
    refine ⟨horizontalPlane n ℓ, hfin, hfirst _ hfin,
      (hheight_le _ σ fun x hx => ?_).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · calc infDist (x - ξ) (horizontalPlane n ℓ : Set (Amb n ℓ))
          ≤ dist (x - ξ) 0 := infDist_le_dist_of_mem (horizontalPlane n ℓ).zero_mem
        _ = dist x ξ := by rw [dist_zero_right, dist_eq_norm]
        _ ≤ σ := mem_closedBall.1 hx.2
    · rw [inv_mul_cancel₀ hσ.ne']
      calc (1 : ℝ) = (δ₁ ^ a)⁻¹ * δ₁ ^ a := (inv_mul_cancel₀ hδ₁a.ne').symm
        _ ≤ C * δ ^ a := mul_le_mul hδ₁C (Real.rpow_le_rpow hδ₁.le hlarge.le ha) hδ₁a.le
            (hC₂.le.trans hC₂C)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
