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
/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): graph coordinates on
`ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ` and the projection onto `T₀ = q(ℝⁿ × {0})`, the plane the book takes to be
`ℝⁿ × {0}` without loss of generality. For a linear isometry `q` of `ℝ^{n+ℓ}`:
(i) `(a, b) − (a', b') = (a − a', b − b')`; (ii) `|(a, b)|² = |a|² + |b|²`; (iii) every
`z ∈ ℝ^{n+ℓ}` is some `(a, b)`; (iv) `p_{T₀}(q(a, b)) = q(a, 0)`.
The coordinate of `(a, b)` at `castAdd ℓ i` is `a_i` and at `natAdd n j` is `b_j`, and every index
of `Fin (n + ℓ)` has one of these forms (`Fin.addCases`); this gives (i) and (iii), and (ii) by
splitting `Σ_k z_k²` with `Fin.sum_univ_add`. For (iv), `(a, 0) = Σ_i a_i e_{castAdd ℓ i}` lies in
`ℝⁿ × {0}`, `(0, b)` is orthogonal to every `e_{castAdd ℓ i}` and hence to `ℝⁿ × {0}`, and `q`
preserves inner products; so `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) = q(0, b) ⊥ T₀`, which
characterizes `q(a, 0)` as the orthogonal projection of `q(a, b)` onto `T₀`. -/
theorem lip_approx_graph_coordinates : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b')) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ z : Amb n ℓ, ∃ (a : Rn n) (b : Rn ℓ), z = graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a 0)) := by
  intro n ℓ q
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- (i): subtraction is coordinatewise
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  refine ⟨hsub, ?_, ?_, ?_⟩
  -- (ii): split `‖z‖² = Σ_k ‖z_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- (iii): read off `a` and `b` from the two blocks of coordinates of `z`
  · intro z
    refine ⟨WithLp.toLp 2 (fun i => z (Fin.castAdd ℓ i)),
      WithLp.toLp 2 (fun j => z (Fin.natAdd n j)), ?_⟩
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [hl]
    · rw [hr]
  -- (iv)
  · intro a b
    -- `graphPoint a 0 = Σ_i a_i e_{castAdd ℓ i}` lies in `ℝⁿ × {0}`
    have hmem : graphPoint a 0 ∈ horizontalPlane n ℓ := by
      have e : graphPoint a 0 =
          ∑ i : Fin n, a i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
        ext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [hl]
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
            Pi.smul_apply, Pi.single_apply, Fin.castAdd_inj, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · rw [hr]
          simp only [PiLp.zero_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (Finset.sum_eq_zero fun x _ => ?_).symm
          have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ x := by
            intro h
            have h' := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
            have := x.isLt
            omega
          rw [Pi.single_eq_of_ne hne, mul_zero]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `graphPoint 0 b` is orthogonal to every `e_{castAdd ℓ i}`, hence to `ℝⁿ × {0}`
    have horth : ∀ h ∈ horizontalPlane n ℓ, inner ℝ (graphPoint 0 b) h = 0 := by
      have hle : horizontalPlane n ℓ ≤ (ℝ ∙ graphPoint 0 b)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
          EuclideanSpace.inner_single_right, hl]
        simp
      intro h hh
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hh)
    -- `q(a, 0) ∈ T₀`, and `q(a, b) - q(a, 0) = q(0, b)` is orthogonal to `T₀ = q(ℝⁿ × {0})`
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
    intro w hw
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
    rw [← map_sub, hsub, sub_self, sub_zero]
    exact (q.inner_map_map _ _).trans (horth h hh)
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
/-- **Tilt-excess as a lower integral** (Simon Ch. 5, 4.1; proof of 5.2, (10)).  If
`y ↦ p_{T_y M}` is `μ_V`-a.e. strongly measurable and `μ_V(B_s(ζ)) < ∞`, then
`∫⁻_{B_s(ζ)} |p_{T_y M} − p_T|² dμ_V = sⁿ E(ζ, s, T)`.  Both projections have operator norm
`≤ 1`, so the integrand lies in `[0, 4(n + ℓ)]`; it is therefore integrable on the ball, and its
lower integral is the real integral `∫_{B_s(ζ)} |p_{T_y M} − p_T|² dμ_V = sⁿ E(ζ, s, T)`. -/
theorem allard52_cft_tilt_lintegral_eq : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ζ : Amb n ℓ) (s : ℝ) (T : Submodule ℝ (Amb n ℓ)), 0 < s → V.weight (closedBall ζ s) < ⊤ → ∫⁻ y in closedBall ζ s, ENNReal.ofReal (hsNormSq (V.tangentProj y - T.starProjection)) ∂V.weight = ENNReal.ofReal (s ^ n * V.tiltExcess ζ s T) := by
  intro n ℓ U V hmeas ζ s T hs hfin
  -- every tangent projection is an orthogonal projection or `0`, so has operator norm `≤ 1`
  have hp : ∀ y, ‖V.tangentProj y‖ ≤ 1 := by
    intro y
    rw [RectifiableVarifold.tangentProj]
    split
    · exact Submodule.starProjection_norm_le _
    · simp
  -- pointwise bounds `0 ≤ |p_y - p_T|² ≤ 4 (n + ℓ)`, from `‖p_y - p_T‖ ≤ 2` and `|eᵢ| = 1`
  have hbd : ∀ y, 0 ≤ hsNormSq (V.tangentProj y - T.starProjection) ∧
      hsNormSq (V.tangentProj y - T.starProjection) ≤ ∑ _i : Fin (n + ℓ), (2 : ℝ) ^ 2 := by
    intro y
    have hA : ‖V.tangentProj y - T.starProjection‖ ≤ 2 := by
      calc ‖V.tangentProj y - T.starProjection‖
          ≤ ‖V.tangentProj y‖ + ‖T.starProjection‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hp y) T.starProjection_norm_le
        _ = 2 := by norm_num
    refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, Finset.sum_le_sum fun i _ => ?_⟩
    have h1 := (V.tangentProj y - T.starProjection).le_opNorm (EuclideanSpace.single i 1)
    rw [PiLp.norm_single, norm_one, mul_one] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans hA) 2
  -- `A ↦ |A - p_T|²` is continuous, so `y ↦ |p_y - p_T|²` is a.e. strongly measurable; being
  -- bounded on the ball of finite measure, it is integrable there
  have hcont : Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq (A - T.starProjection) := by
    unfold hsNormSq
    fun_prop
  have hint : IntegrableOn (fun y => hsNormSq (V.tangentProj y - T.starProjection))
      (closedBall ζ s) V.weight :=
    Measure.integrableOn_of_bounded hfin.ne (hcont.comp_aestronglyMeasurable hmeas)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd y).1]
        exact (hbd y).2)
  -- `sⁿ E(ζ, s, T) = ∫_{B_s(ζ)} |p_y - p_T|² dμ_V`, and the integrand is nonnegative
  rw [RectifiableVarifold.tiltExcess, mul_inv_cancel_left₀ (pow_ne_zero n hs.ne'),
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => (hbd y).1)]

/-- Simon Ch. 5, proof of Theorem 5.2, (10)–(11): for `f` `1`-Lipschitz on `D ⊆ ℝⁿ` and a linear
isometry `q` of `ℝ^{n+ℓ}`, the graph map `F(x) = q(x, f(x))` is `√2`-Lipschitz on `D`, and
`|F(x)| ≤ √2 |x|` on `D` when `f(0) = 0` and `0 ∈ D`. By the graph coordinates
(`lip_approx_graph_coordinates` (i), (ii)) and since `q` is a linear isometry,
`|F(x) − F(x')|² = |x − x'|² + |f(x) − f(x')|² ≤ 2 |x − x'|²`; and `F(0) = q(0, 0) = 0`. -/
theorem allard52_cft_graph_map_sqrt_two : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)), LipschitzOnWith 1 f D → (∀ x ∈ D, ∀ x' ∈ D, ‖q (graphPoint x (f x)) - q (graphPoint x' (f x'))‖ ≤ Real.sqrt 2 * ‖x - x'‖) ∧ (f 0 = 0 → (0 : Rn n) ∈ D → ∀ x ∈ D, ‖q (graphPoint x (f x))‖ ≤ Real.sqrt 2 * ‖x‖) := by
  intro n ℓ q f D hf
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  have hlip : ∀ x ∈ D, ∀ x' ∈ D,
      ‖q (graphPoint x (f x)) - q (graphPoint x' (f x'))‖ ≤ Real.sqrt 2 * ‖x - x'‖ := by
    intro x hx x' hx'
    -- `|f(x) − f(x')| ≤ |x − x'|`
    have hf' : ‖f x - f x'‖ ≤ ‖x - x'‖ := by
      have h := hf.dist_le_mul x hx x' hx'
      rwa [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    -- `|F(x) − F(x')| = |(x − x', f(x) − f(x'))|`, whose square is at most `2 |x − x'|²`
    rw [← map_sub, q.norm_map, hsub]
    have hsq : ‖graphPoint (x - x') (f x - f x')‖ ^ 2 ≤ (Real.sqrt 2 * ‖x - x'‖) ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt zero_le_two, two_mul]
      exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hf' 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp hsq
  refine ⟨hlip, fun hf0 h0 x hx => ?_⟩
  -- `(0, 0) = (0, 0) − (0, 0) = 0`, so `F(0) = 0`; compare `F(x)` with `F(0)`
  have hzero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    have h := hsub 0 0 0 0
    rw [sub_self, sub_self, sub_self] at h
    exact h.symm
  have h := hlip x hx 0 h0
  rwa [hf0, hzero, map_zero, sub_zero, sub_zero] at h

/-- Simon Ch. 5, proof of Theorem 5.2, (10)–(11) (pp. 123–124): tilt-excess decay gives the
Campanato estimate for the tangent planes `G(x) = p_{q(graph Df(x))}` of the Lipschitz graph. Fix
`z ∈ Bⁿ_{R/4}(0)`, `0 < s ≤ R/4`, and put `ζ = q(z, f(z))`, `P = p_{S(ζ)}`, `D = Bⁿ_{s/2}(z)`,
`B = B_s(ζ)`. As `x ↦ q(x, f(x))` is `√2`-Lipschitz on `Bⁿ_R(0)` and vanishes at `0`:
`ζ ∈ spt V ∩ B_{R/2}(0)` (by the graph representation of `spt V`), `D ⊆ B̆ⁿ_{R/2}(0)`,
`q(x, f(x)) ∈ B` for `x ∈ D`, and `B ⊆ B_R(0) ⊆ U`, so `μ_V(B) < ∞` and
`∫⁻_B |p_{T_y M} − P|² dμ_V = sⁿ E(ζ, s, S(ζ)) ≤ A sⁿ (s/R)^e`. The comparison hypothesis with
`Φ(w, T) = 1_B(w) |T − P|²` bounds `∫⁻_D |G(x) − P|² dx` by
`∫⁻_{q(graph f|_D)} Φ(y, p_{T_y M}) dμ_V`, which is at most `∫⁻_B |p_{T_y M} − P|² dμ_V`. -/
theorem allard52_campanato_from_tilt : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (S : Amb n ℓ → Submodule ℝ (Amb n ℓ)) (R A e : ℝ), 0 < R → closedBall (0 : Amb n ℓ) R ⊆ U → f 0 = 0 → LipschitzOnWith 1 f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → AEStronglyMeasurable V.tangentProj V.weight → (∀ Φ : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) → ℝ≥0∞, Measurable (Function.uncurry Φ) → ∀ D : Set (Rn n), MeasurableSet D → D ⊆ ball 0 (R / 2) → ∫⁻ x in D, Φ (q (graphPoint x (f x))) ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection ≤ ∫⁻ y in q '' graphOver f D, Φ y (V.tangentProj y) ∂V.weight) → (∀ ζ ∈ V.support ∩ closedBall 0 (R / 2), ∀ s : ℝ, 0 < s → s ≤ R / 2 → V.tiltExcess ζ s (S ζ) ≤ A * (s / R) ^ e) → ∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection - (S (q (graphPoint z (f z)))).starProjection)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ e) := by
  intro n ℓ U V q f S R A e hR hRU hf0 hlip hspt hae hcomp htilt z hz s hs hsR
  set ζ : Amb n ℓ := q (graphPoint z (f z))
  -- the graph map `x ↦ q(x, f(x))` is `√2`-Lipschitz on `Bⁿ_R(0)` and `|q(x, f(x))| ≤ √2 |x|`
  obtain ⟨hlipF, hnormF⟩ :=
    Submission.allard52_cft_graph_map_sqrt_two n ℓ q f (closedBall 0 R) hlip
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hzn : ‖z‖ ≤ R / 4 := mem_closedBall_zero_iff.mp hz
  have hzR : z ∈ closedBall (0 : Rn n) R := mem_closedBall_zero_iff.mpr (by linarith)
  -- `|ζ| ≤ √2 |z| ≤ R/2`
  have hζn : ‖ζ‖ ≤ R / 2 :=
    calc ‖ζ‖ ≤ Real.sqrt 2 * ‖z‖ := hnormF hf0 (mem_closedBall_self hR.le) z hzR
      _ ≤ 2 * (R / 4) := mul_le_mul h2 hzn (norm_nonneg z) (by norm_num)
      _ = R / 2 := by ring
  -- `ζ ∈ spt V ∩ B_{R/2}(0)`, as `spt V ∩ B_R(0) = q(graph f) ∩ B_R(0)`
  have hζspt : ζ ∈ V.support ∩ closedBall 0 (R / 2) := by
    have hmem : ζ ∈ q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R :=
      ⟨Set.mem_image_of_mem q (Set.mem_image_of_mem (fun x => graphPoint x (f x)) hzR),
        mem_closedBall_zero_iff.mpr (by linarith)⟩
    rw [← hspt] at hmem
    exact ⟨hmem.1, mem_closedBall_zero_iff.mpr hζn⟩
  -- `D = Bⁿ_{s/2}(z) ⊆ B̆ⁿ_{R/2}(0)` and `D ⊆ Bⁿ_R(0)`
  have hDball : closedBall z (s / 2) ⊆ ball (0 : Rn n) (R / 2) :=
    closedBall_subset_ball' (by rw [dist_zero_right]; linarith)
  have hDR : closedBall z (s / 2) ⊆ closedBall (0 : Rn n) R :=
    closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  -- `q(x, f(x)) ∈ B = B_s(ζ)` for `x ∈ D`
  have hFB : ∀ x ∈ closedBall z (s / 2), q (graphPoint x (f x)) ∈ closedBall ζ s := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    have hxz : ‖x - z‖ ≤ s / 2 := by rw [← dist_eq_norm]; exact hx
    calc ‖q (graphPoint x (f x)) - ζ‖ ≤ Real.sqrt 2 * ‖x - z‖ := hlipF x (hDR hx) z hzR
      _ ≤ 2 * (s / 2) := mul_le_mul h2 hxz (norm_nonneg _) (by norm_num)
      _ = s := by ring
  -- `B ⊆ B_R(0) ⊆ U`, hence `μ_V(B) < ∞`
  have hBR : closedBall ζ s ⊆ closedBall (0 : Amb n ℓ) R :=
    closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  have hBfin : V.weight (closedBall ζ s) < ⊤ := by
    rw [rsod_weight_closedBall_eq_ofReal_integral n ℓ U V ζ s (hBR.trans hRU)]
    exact ENNReal.ofReal_lt_top
  -- `∫⁻_B |p_{T_y M} − P|² dμ_V = sⁿ E(ζ, s, S(ζ)) ≤ A sⁿ (s/R)^e`
  have hBbound : ∫⁻ y in closedBall ζ s,
      ENNReal.ofReal (hsNormSq (V.tangentProj y - (S ζ).starProjection)) ∂V.weight ≤
      ENNReal.ofReal (A * s ^ n * (s / R) ^ e) := by
    rw [Submission.allard52_cft_tilt_lintegral_eq n ℓ U V hae ζ s (S ζ) hs hBfin]
    refine ENNReal.ofReal_le_ofReal ?_
    calc s ^ n * V.tiltExcess ζ s (S ζ) ≤ s ^ n * (A * (s / R) ^ e) :=
          mul_le_mul_of_nonneg_left (htilt ζ hζspt s hs (by linarith)) (pow_pos hs n).le
      _ = A * s ^ n * (s / R) ^ e := by ring
  -- the test function `Φ(w, T) = 1_B(w) |T − P|²` is measurable
  have hg : Measurable fun T : Amb n ℓ →L[ℝ] Amb n ℓ =>
      ENNReal.ofReal (hsNormSq (T - (S ζ).starProjection)) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold hsNormSq
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_id.sub continuous_const).clm_apply continuous_const).norm.pow 2
  have hΦ : Measurable (Function.uncurry fun (w : Amb n ℓ) (T : Amb n ℓ →L[ℝ] Amb n ℓ) =>
      (closedBall ζ s).indicator
        (fun _ => ENNReal.ofReal (hsNormSq (T - (S ζ).starProjection))) w) :=
    (hg.comp measurable_snd).indicator (measurable_fst measurableSet_closedBall)
  have hcmp := hcomp _ hΦ (closedBall z (s / 2)) measurableSet_closedBall hDball
  refine le_trans (le_of_eq ?_) (hcmp.trans ((setLIntegral_le_lintegral _ _).trans
    (le_trans (le_of_eq ?_) hBbound)))
  -- on `D` the indicator is `1`, since the graph over `D` lies in `B`
  · exact setLIntegral_congr_fun measurableSet_closedBall fun x hx => by
      rw [Set.indicator_of_mem (hFB x hx)]
  -- `∫⁻ 1_B |p_{T_y M} − P|² dμ_V = ∫⁻_B |p_{T_y M} − P|² dμ_V`
  · refine (lintegral_congr fun y => ?_).trans (lintegral_indicator measurableSet_closedBall _)
    by_cases hy : y ∈ closedBall ζ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
/-- Lebesgue points of a bounded Borel operator field for the squared Hilbert–Schmidt
oscillation (used in the proof of Simon Ch. 5, Theorem 5.2, p. 123; Lebesgue's differentiation
theorem, Ch. 1, Theorem 3.23).  If `G : ℝⁿ → L(ℝᵐ, ℝᵏ)` is Borel with `‖G‖ ≤ B`, then for
`Lⁿ`-a.e. `z`,
`Lⁿ(B_t(z))⁻¹ ∫_{B_t(z)} |G(x) − G(z)|² dx → 0` as `t → 0⁺`.  Since `|A|² ≤ m ‖A‖²` and
`‖G(x) − G(z)‖ ≤ 2B`, the integrand is at most `2mB ‖G(x) − G(z)‖`, whose ball averages tend
to `0` at a.e. `z` by the differentiation theorem for the locally integrable `G` along the
Vitali family of the doubling measure `Lⁿ`. -/
theorem allard52_cae_hsNormSq_lebesgue_ae : ∀ (n m k : ℕ) (G : Rn n → (Rn m →L[ℝ] Rn k)) (B : ℝ), Measurable G → (∀ x, ‖G x‖ ≤ B) → ∀ᵐ z ∂(volume : Measure (Rn n)), Tendsto (fun t : ℝ => (volume (closedBall z t))⁻¹ * ∫⁻ x in closedBall z t, ENNReal.ofReal (hsNormSq (G x - G z))) (𝓝[>] 0) (𝓝 0) := by
  intro n m k G B hG hB
  -- A bounded Borel map into the finite-dimensional space `L(ℝᵐ, ℝᵏ)` is locally integrable.
  have hloc : LocallyIntegrable G (volume : Measure (Rn n)) :=
    locallyIntegrable_iff.2 fun K hK =>
      Measure.integrableOn_of_bounded hK.measure_lt_top.ne hG.aestronglyMeasurable
        (ae_of_all _ hB)
  -- Pointwise comparison: `|G(x) − G(z)|² ≤ m ‖G(x) − G(z)‖² ≤ 2mB ‖G(x) − G(z)‖`.
  have hpt : ∀ x z, ENNReal.ofReal (hsNormSq (G x - G z)) ≤
      ENNReal.ofReal (2 * m * B) * ‖G x - G z‖ₑ := by
    intro x z
    have hT : ‖G x - G z‖ ≤ 2 * B := by
      linarith [norm_sub_le (G x) (G z), hB x, hB z]
    have hsum : hsNormSq (G x - G z) ≤ m * ‖G x - G z‖ ^ 2 := by
      unfold hsNormSq
      calc ∑ i : Fin m, ‖(G x - G z) (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ _i : Fin m, ‖G x - G z‖ ^ 2 := by
            gcongr with i
            calc ‖(G x - G z) (EuclideanSpace.single i 1)‖
                ≤ ‖G x - G z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (G x - G z).le_opNorm _
              _ = ‖G x - G z‖ := by simp
        _ = m * ‖G x - G z‖ ^ 2 := by simp
    rw [← ofReal_norm, ← ENNReal.ofReal_mul' (norm_nonneg (G x - G z))]
    apply ENNReal.ofReal_le_ofReal
    have hm : (0 : ℝ) ≤ m * ‖G x - G z‖ := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hT hm]
  -- Lebesgue differentiation along the closed balls `B_t(z)`, `t → 0⁺`.
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Rn n)) 1).ae_tendsto_lintegral_enorm_sub_div hloc] with z hz
  have hballs : Tendsto (fun t : ℝ => closedBall z t) (𝓝[>] 0)
      ((IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Rn n)) 1).filterAt z) :=
    IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (volume : Measure (Rn n))
      (fun _ => z) id tendsto_id (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact mem_closedBall_self (by simpa using (Set.mem_Ioi.1 ht).le))
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * m * B)) (hz.comp hballs)
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun t => ?_
  -- Average the pointwise comparison over `B_t(z)`.
  calc (volume (closedBall z t))⁻¹ * ∫⁻ x in closedBall z t, ENNReal.ofReal (hsNormSq (G x - G z))
      ≤ (volume (closedBall z t))⁻¹ *
          ∫⁻ x in closedBall z t, ENNReal.ofReal (2 * m * B) * ‖G x - G z‖ₑ := by
        gcongr with x
        exact hpt x z
    _ = ENNReal.ofReal (2 * m * B) *
          ((∫⁻ x in closedBall z t, ‖G x - G z‖ₑ) / volume (closedBall z t)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.div_eq_inv_mul, mul_left_comm]
/-- At a quadratic Lebesgue point the Campanato centre is the value (Simon Ch. 5, proof of
Theorem 5.2, p. 123: where `σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x G(f)} − p_{S(ξ)}|² dHⁿ → 0`, `S(ξ)` is the
approximate tangent space).  If `⨍_{B_t(z)} |G(x) − G(z)|² dx → 0` as `t ↓ 0` and
`∫_{B_{s/2}(z)} |G(x) − T|² dx ≤ A sⁿ (s/R)^{2α}` for `0 < s ≤ s₀` (Hilbert–Schmidt norm), then
`G(z) = T`: averaging `|G(z) − T|² ≤ 2|G(x) − T|² + 2|G(x) − G(z)|²` over `B_{s/2}(z)`, of volume
`(s/2)ⁿ Lⁿ(B₁(0))`, gives
`|G(z) − T|² ≤ 2^{n+1} A (s/R)^{2α} / Lⁿ(B₁(0)) + 2 ⨍_{B_{s/2}(z)} |G(x) − G(z)|² dx → 0`. -/
theorem allard52_cae_center_eq_at_lebesgue_point : ∀ (n m k : ℕ) (G : Rn n → (Rn m →L[ℝ] Rn k)) (z : Rn n) (T : Rn m →L[ℝ] Rn k) (A R α s₀ : ℝ), 0 < R → 0 < α → 0 < s₀ → Measurable G → Tendsto (fun t : ℝ => (volume (closedBall z t))⁻¹ * ∫⁻ x in closedBall z t, ENNReal.ofReal (hsNormSq (G x - G z))) (𝓝[>] 0) (𝓝 0) → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - T)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → G z = T := by
  intro n m k G z T A R α s₀ _hR hα hs₀ hG hleb hcamp
  -- Hilbert–Schmidt facts: `|S|² ≥ 0`, `|S − S'|² ≤ 2|S|² + 2|S'|²`, `|S|² = 0 ⇒ S = 0`.
  have hs_nonneg : ∀ S : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq S := fun S =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs_sub : ∀ S S' : Rn m →L[ℝ] Rn k,
      hsNormSq (S - S') ≤ 2 * hsNormSq S + 2 * hsNormSq S' := by
    intro S S'
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sub_apply]
    have h1 := norm_sub_le (S (EuclideanSpace.single i 1)) (S' (EuclideanSpace.single i 1))
    have h2 := norm_nonneg (S (EuclideanSpace.single i 1) - S' (EuclideanSpace.single i 1))
    nlinarith [sq_nonneg (‖S (EuclideanSpace.single i 1)‖ - ‖S' (EuclideanSpace.single i 1)‖)]
  have hs_zero : ∀ S : Rn m →L[ℝ] Rn k, hsNormSq S = 0 → S = 0 := by
    intro S hS
    have hterm : ∀ i, S (EuclideanSpace.single i 1) = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg ‖S (EuclideanSpace.single i 1)‖)).1 hS i (Finset.mem_univ _)
      simpa using this
    ext1 w
    rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr w]
    simp [map_sum, map_smul, hterm]
  -- Measurability of `x ↦ |G(x) − T|²`.
  have hcont : Continuous fun S : Rn m →L[ℝ] Rn k => hsNormSq S := by
    unfold hsNormSq
    fun_prop
  have hmeasT : Measurable fun x => ENNReal.ofReal (hsNormSq (G x - T)) :=
    ENNReal.measurable_ofReal.comp
      ((hcont.comp (continuous_id.sub continuous_const)).measurable.comp hG)
  -- Ball volumes: `Lⁿ(B_t(z)) = tⁿ v` with `v = Lⁿ(B_1(0)) > 0`.
  set v : ℝ≥0∞ := volume (closedBall (0 : Rn n) 1)
  have hv0 : v ≠ 0 := (measure_closedBall_pos volume (0 : Rn n) one_pos).ne'
  have hvol : ∀ t : ℝ, 0 ≤ t → volume (closedBall z t) = ENNReal.ofReal (t ^ n) * v := by
    intro t ht
    rw [Measure.addHaar_closedBall' volume z ht, finrank_euclideanSpace_fin]
  -- Pointwise: `|G(z) − T|² ≤ 2|G(x) − T|² + 2|G(x) − G(z)|²`.
  set h : ℝ := hsNormSq (G z - T)
  have hpt : ∀ x, ENNReal.ofReal h ≤
      2 * ENNReal.ofReal (hsNormSq (G x - T)) + 2 * ENNReal.ofReal (hsNormSq (G x - G z)) := by
    intro x
    have h1 : h ≤ 2 * hsNormSq (G x - T) + 2 * hsNormSq (G x - G z) := by
      have := hs_sub (G x - T) (G x - G z)
      rwa [sub_sub_sub_cancel_left] at this
    calc ENNReal.ofReal h
        ≤ ENNReal.ofReal (2 * hsNormSq (G x - T) + 2 * hsNormSq (G x - G z)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = _ := by
          rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (hs_nonneg _))
              (mul_nonneg zero_le_two (hs_nonneg _)),
            ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  -- For `0 < s ≤ s₀`: `ofReal h ≤ 2 ofReal(2ⁿ A (s/R)^{2α}) v⁻¹ + 2 a(s/2)`.
  have hbound : ∀ s : ℝ, 0 < s → s ≤ s₀ → ENNReal.ofReal h ≤
      2 * ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * v⁻¹ +
        2 * ((volume (closedBall z (s / 2)))⁻¹ *
          ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z))) := by
    intro s hs hss
    have ht : 0 < s / 2 := half_pos hs
    set W : ℝ≥0∞ := volume (closedBall z (s / 2))
    have hW0 : W ≠ 0 := (measure_closedBall_pos volume z ht).ne'
    have hWtop : W ≠ ∞ := measure_closedBall_lt_top.ne
    have hint : ENNReal.ofReal h * W ≤ 2 * ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α)) +
        2 * ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z)) := by
      calc ENNReal.ofReal h * W = ∫⁻ _ in closedBall z (s / 2), ENNReal.ofReal h :=
            (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in closedBall z (s / 2), (2 * ENNReal.ofReal (hsNormSq (G x - T)) +
              2 * ENNReal.ofReal (hsNormSq (G x - G z))) := lintegral_mono hpt
        _ = 2 * (∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - T))) +
              2 * ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z)) := by
            rw [lintegral_add_left (hmeasT.const_mul 2), lintegral_const_mul 2 hmeasT,
              lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
        _ ≤ _ := by
            gcongr
            exact hcamp s hs hss
    -- `A sⁿ (s/R)^{2α} = (2ⁿ A (s/R)^{2α}) (s/2)ⁿ` and `W = ofReal((s/2)ⁿ) v`.
    have hsplit : ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α)) =
        ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * ENNReal.ofReal ((s / 2) ^ n) := by
      rw [← ENNReal.ofReal_mul' (pow_nonneg ht.le n)]
      congr 1
      have : s ^ n = 2 ^ n * (s / 2) ^ n := by
        rw [← mul_pow]
        congr 1
        ring
      rw [this]
      ring
    have hq0 : ENNReal.ofReal ((s / 2) ^ n) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos ht n
    have hqtop : ENNReal.ofReal ((s / 2) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have hWeq : W = ENNReal.ofReal ((s / 2) ^ n) * v := hvol _ ht.le
    have hfirst : ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α)) * W⁻¹ =
        ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * v⁻¹ := by
      rw [hsplit, hWeq, ENNReal.mul_inv (Or.inl hq0) (Or.inl hqtop), mul_assoc,
        ← mul_assoc (ENNReal.ofReal ((s / 2) ^ n)), ENNReal.mul_inv_cancel hq0 hqtop, one_mul]
    calc ENNReal.ofReal h = ENNReal.ofReal h * W * W⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hW0 hWtop, mul_one]
      _ ≤ (2 * ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α)) +
            2 * ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z))) * W⁻¹ := by
          gcongr
      _ = 2 * (ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α)) * W⁻¹) +
            2 * (W⁻¹ * ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z))) := by
          ring
      _ = _ := by
          rw [hfirst]
          ring
  -- The bound tends to `0` as `s → 0+`.
  have hlim : Tendsto (fun s : ℝ => 2 * ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * v⁻¹ +
      2 * ((volume (closedBall z (s / 2)))⁻¹ *
        ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z)))) (𝓝[>] 0) (𝓝 0) := by
    have hrpow : Tendsto (fun s : ℝ => (s / R) ^ (2 * α)) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun s : ℝ => (s / R) ^ (2 * α)) 0 :=
        (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp
          (continuous_id.div_const R).continuousAt
      simpa [Real.zero_rpow (show 2 * α ≠ 0 by positivity)] using hc.tendsto
    have hreal : Tendsto (fun s : ℝ => 2 ^ n * A * (s / R) ^ (2 * α)) (𝓝[>] 0) (𝓝 0) := by
      have := (hrpow.const_mul (2 ^ n * A)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have h1 : Tendsto (fun s : ℝ => 2 * ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * v⁻¹)
        (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hreal) (Or.inr ENNReal.ofNat_ne_top))
        (Or.inr (ENNReal.inv_ne_top.2 hv0)) (b := v⁻¹) (a := 2 * ENNReal.ofReal 0)
      simpa using this
    have hhalf : Tendsto (fun s : ℝ => s / 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ => s / 2) (𝓝 0) (𝓝 (0 / 2)) := tendsto_id.div_const 2
        rw [zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact half_pos (Set.mem_Ioi.mp hs)
    have h2 := ENNReal.Tendsto.const_mul (hleb.comp hhalf) (Or.inr ENNReal.ofNat_ne_top) (a := 2)
    simpa using h1.add h2
  -- Conclusion: `ofReal h ≤ 0`, so `h = 0` and `G z = T`.
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal h ≤
      2 * ENNReal.ofReal (2 ^ n * A * (s / R) ^ (2 * α)) * v⁻¹ +
        2 * ((volume (closedBall z (s / 2)))⁻¹ *
          ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - G z))) := by
    filter_upwards [Ioc_mem_nhdsGT hs₀] with s hs
    exact hbound s hs.1 hs.2
  have hle : ENNReal.ofReal h ≤ 0 := ge_of_tendsto hlim hev
  have hh0 : h = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.1 (nonpos_iff_eq_zero.1 hle)) (hs_nonneg _)
  exact sub_eq_zero.1 (hs_zero _ hh0)
/-- **Hölder continuity of Campanato centers** (Simon Ch. 5, proof of Theorem 5.2, the Hölder
step after (11)).  If `∫_{B_{s/2}(z)} |G − c(z)|² ≤ A sⁿ (s/R)^{2α}` for every `z ∈ B_{R/4}(0)` and
`s ∈ (0, R/4]`, then `|c(x) − c(y)| ≤ C √A (|x − y|/R)^α` for `x, y ∈ B̆_{R/16}(0)`, with
`C = (4^{n+2} / Lⁿ(B₁(0)))^{1/2}`.

For `x ≠ y` put `d = |x − y| < R/8` and `s = 2d`: the ball `B_{d/2}((x + y)/2)` lies in
`B_{s/2}(x) ∩ B_{s/2}(y)`, and averaging `|c(x) − c(y)|² ≤ 2|G − c(x)|² + 2|G − c(y)|²` over it
gives `|c(x) − c(y)|² (d/2)ⁿ Lⁿ(B₁(0)) ≤ 4A (2d)ⁿ (2d/R)^{2α} ≤ 4^{n+2} A (d/R)^{2α} (d/2)ⁿ`. -/
theorem allard52_campanato_center_holder : ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (m k : ℕ) (G c : Rn n → (Rn m →L[ℝ] Rn k)) (A R α : ℝ), 0 ≤ A → 0 < R → 0 < α → α ≤ 1 → Measurable G → (∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - c z)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → ∀ x ∈ ball (0 : Rn n) (R / 16), ∀ y ∈ ball (0 : Rn n) (R / 16), hsNorm (c x - c y) ≤ C * Real.sqrt A * (‖x - y‖ / R) ^ α := by
  intro n _
  -- `v = Lⁿ(B₁(0))`, positive and finite; `Lⁿ(B_t(w)) = tⁿ v`.
  set v : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hv_def
  have hV0 : volume (closedBall (0 : Rn n) 1) ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'
  have hVtop : volume (closedBall (0 : Rn n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
  have hv : 0 < v := ENNReal.toReal_pos hV0 hVtop
  refine ⟨Real.sqrt (4 ^ (n + 2) / v), Real.sqrt_nonneg _, ?_⟩
  intro m k G c A R α hA hR hα hα1 hG hcamp x hx y hy
  have hRHS : 0 ≤ Real.sqrt (4 ^ (n + 2) / v) * Real.sqrt A * (‖x - y‖ / R) ^ α :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (div_nonneg (norm_nonneg _) hR.le) _)
  -- Hilbert–Schmidt facts.
  have hHS0 : ∀ T : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq T := fun T =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHSsub : ∀ T T' : Rn m →L[ℝ] Rn k,
      hsNormSq (T - T') ≤ 2 * hsNormSq T + 2 * hsNormSq T' := by
    intro T T'
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sub_apply]
    have h1 := norm_sub_le (T (EuclideanSpace.single i 1)) (T' (EuclideanSpace.single i 1))
    have h2 := norm_nonneg (T (EuclideanSpace.single i 1) - T' (EuclideanSpace.single i 1))
    nlinarith [sq_nonneg (‖T (EuclideanSpace.single i 1)‖ - ‖T' (EuclideanSpace.single i 1)‖)]
  have hHScont : Continuous fun T : Rn m →L[ℝ] Rn k => hsNormSq T := by
    unfold hsNormSq
    fun_prop
  -- The case `x = y`.
  rcases eq_or_ne x y with rfl | hxy
  · have h0 : hsNorm (c x - c x) = 0 := by
      simp [hsNorm, hsNormSq]
    rw [h0]
    exact hRHS
  -- Geometry for `x ≠ y`: `d = ‖x - y‖ < R/8`, `s = 2d`, and the midpoint ball `B_{d/2}(m₀)`.
  set d := ‖x - y‖ with hd_def
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hxR : ‖x‖ < R / 16 := mem_ball_zero_iff.1 hx
  have hyR : ‖y‖ < R / 16 := mem_ball_zero_iff.1 hy
  have hdR : d < R / 8 := by
    calc d ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ < R / 16 + R / 16 := add_lt_add hxR hyR
      _ = R / 8 := by ring
  have hs0 : 0 < 2 * d := by positivity
  have hsR : 2 * d ≤ R / 4 := by linarith
  have hs2 : 2 * d / 2 = d := by ring
  have hxB : x ∈ closedBall (0 : Rn n) (R / 4) :=
    mem_closedBall_zero_iff.2 (by linarith)
  have hyB : y ∈ closedBall (0 : Rn n) (R / 4) :=
    mem_closedBall_zero_iff.2 (by linarith)
  set m₀ : Rn n := midpoint ℝ x y with hm₀
  have hm₀x : dist m₀ x = d / 2 := by
    rw [hm₀, dist_midpoint_left, dist_eq_norm, Real.norm_two]
    ring
  have hm₀y : dist m₀ y = d / 2 := by
    rw [hm₀, dist_midpoint_right, dist_eq_norm, Real.norm_two]
    ring
  have hBx : closedBall m₀ (d / 2) ⊆ closedBall x (2 * d / 2) := by
    rw [hs2]
    exact closedBall_subset_closedBall' (by rw [hm₀x]; linarith)
  have hBy : closedBall m₀ (d / 2) ⊆ closedBall y (2 * d / 2) := by
    rw [hs2]
    exact closedBall_subset_closedBall' (by rw [hm₀y]; linarith)
  -- Pointwise bound.
  have hpt : ∀ w, ENNReal.ofReal (hsNormSq (c x - c y)) ≤
      2 * ENNReal.ofReal (hsNormSq (G w - c x)) + 2 * ENNReal.ofReal (hsNormSq (G w - c y)) := by
    intro w
    have h := hHSsub (G w - c y) (G w - c x)
    rw [sub_sub_sub_cancel_left] at h
    calc ENNReal.ofReal (hsNormSq (c x - c y))
        ≤ ENNReal.ofReal (2 * hsNormSq (G w - c x) + 2 * hsNormSq (G w - c y)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 * ENNReal.ofReal (hsNormSq (G w - c x)) +
            2 * ENNReal.ofReal (hsNormSq (G w - c y)) := by
          rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (hHS0 _))
              (mul_nonneg zero_le_two (hHS0 _)),
            ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  -- Averaging over the midpoint ball.
  have hmeas : ∀ T₀ : Rn m →L[ℝ] Rn k, Measurable fun w => ENNReal.ofReal (hsNormSq (G w - T₀)) :=
    fun T₀ => ENNReal.measurable_ofReal.comp
      ((hHScont.comp (continuous_id.sub continuous_const)).measurable.comp hG)
  set K : ℝ := A * (2 * d) ^ n * (2 * d / R) ^ (2 * α) with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hint : ENNReal.ofReal (hsNormSq (c x - c y)) * volume (closedBall m₀ (d / 2)) ≤
      4 * ENNReal.ofReal K := by
    calc ENNReal.ofReal (hsNormSq (c x - c y)) * volume (closedBall m₀ (d / 2))
        = ∫⁻ _ in closedBall m₀ (d / 2), ENNReal.ofReal (hsNormSq (c x - c y)) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in closedBall m₀ (d / 2),
            (2 * ENNReal.ofReal (hsNormSq (G w - c x)) +
              2 * ENNReal.ofReal (hsNormSq (G w - c y))) := lintegral_mono fun w => hpt w
      _ = 2 * (∫⁻ w in closedBall m₀ (d / 2), ENNReal.ofReal (hsNormSq (G w - c x))) +
            2 * ∫⁻ w in closedBall m₀ (d / 2), ENNReal.ofReal (hsNormSq (G w - c y)) := by
          rw [lintegral_add_left ((hmeas (c x)).const_mul 2), lintegral_const_mul 2 (hmeas (c x)),
            lintegral_const_mul 2 (hmeas (c y))]
      _ ≤ 2 * (∫⁻ w in closedBall x (2 * d / 2), ENNReal.ofReal (hsNormSq (G w - c x))) +
            2 * ∫⁻ w in closedBall y (2 * d / 2), ENNReal.ofReal (hsNormSq (G w - c y)) := by
          gcongr
      _ ≤ 2 * ENNReal.ofReal K + 2 * ENNReal.ofReal K := by
          gcongr
          · exact hcamp x hxB (2 * d) hs0 hsR
          · exact hcamp y hyB (2 * d) hs0 hsR
      _ = 4 * ENNReal.ofReal K := by ring
  -- Arithmetic.
  have hvolB : volume (closedBall m₀ (d / 2)) = ENNReal.ofReal ((d / 2) ^ n * v) := by
    rw [Measure.addHaar_closedBall' volume m₀ (by positivity), finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity), hv_def, ENNReal.ofReal_toReal hVtop]
  rw [hvolB, ← ENNReal.ofReal_mul (hHS0 _), ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
  have hpow : (2 * d) ^ n = 4 ^ n * (d / 2) ^ n := by
    rw [← mul_pow]
    ring
  have hrpow : (2 * d / R) ^ (2 * α) ≤ 4 * (d / R) ^ (2 * α) := by
    rw [mul_div_assoc, Real.mul_rpow zero_le_two (by positivity)]
    gcongr
    calc (2 : ℝ) ^ (2 * α) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 4 := by norm_num [Real.rpow_two]
  have hsq : ((d / R) ^ α) ^ 2 = (d / R) ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
    norm_num
  have hdn : 0 < (d / 2) ^ n := by positivity
  have hmain : hsNormSq (c x - c y) ≤ 4 ^ (n + 2) / v * A * ((d / R) ^ α) ^ 2 := by
    rw [hsq, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hv]
    have h4 : 4 * K ≤ 4 ^ (n + 2) * A * (d / R) ^ (2 * α) * (d / 2) ^ n := by
      rw [hK_def, hpow]
      calc 4 * (A * (4 ^ n * (d / 2) ^ n) * (2 * d / R) ^ (2 * α))
          ≤ 4 * (A * (4 ^ n * (d / 2) ^ n) * (4 * (d / R) ^ (2 * α))) := by gcongr
        _ = 4 ^ (n + 2) * A * (d / R) ^ (2 * α) * (d / 2) ^ n := by ring
    have h5 : hsNormSq (c x - c y) * v * (d / 2) ^ n ≤
        4 ^ (n + 2) * A * (d / R) ^ (2 * α) * (d / 2) ^ n := by
      calc hsNormSq (c x - c y) * v * (d / 2) ^ n
          = hsNormSq (c x - c y) * ((d / 2) ^ n * v) := by ring
        _ ≤ 4 * K := hint
        _ ≤ _ := h4
    exact le_of_mul_le_mul_right h5 hdn
  -- Square roots.
  unfold hsNorm
  rw [Real.sqrt_le_left hRHS, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt hA]
  exact hmain
/-- **Campanato centres agree with `G` almost everywhere** (Simon Ch. 5, proof of Theorem 5.2:
identification of the centres by Lebesgue's differentiation theorem in the parameter domain `ℝⁿ`).
Let `G, c : ℝⁿ → L(ℝᵐ, ℝᵏ)` with `G` Borel and `‖G‖ ≤ B`, and suppose that for every
`z ∈ B_{R/4}(0)` and `s ∈ (0, R/4]`
`∫_{B_{s/2}(z)} |G(x) − c(z)|² dx ≤ A sⁿ (s/R)^{2α}` (Hilbert–Schmidt norm, `R, α > 0`).
Then `G(z) = c(z)` for `Lⁿ`-a.e. `z ∈ B̆_{R/4}(0)`.
Off the null set of `allard52_cae_hsNormSq_lebesgue_ae`, every `z` is a quadratic Lebesgue point
of `G`; for `z ∈ B̆_{R/4}(0) ⊆ B_{R/4}(0)` the Campanato bound at `z` is the hypothesis of
`allard52_cae_center_eq_at_lebesgue_point` with `T = c(z)` and `s₀ = R/4`. -/
theorem allard52_campanato_ae_center : ∀ (n m k : ℕ) (G c : Rn n → (Rn m →L[ℝ] Rn k)) (A R α B : ℝ), 1 ≤ n → 0 < R → 0 < α → Measurable G → (∀ x, ‖G x‖ ≤ B) → (∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - c z)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → ∀ᵐ z ∂(volume : Measure (Rn n)), z ∈ ball (0 : Rn n) (R / 4) → G z = c z := by
  intro n m k G c A R α B _hn hR hα hG hB hcamp
  filter_upwards [Submission.allard52_cae_hsNormSq_lebesgue_ae n m k G B hG hB] with z hz hzR
  exact Submission.allard52_cae_center_eq_at_lebesgue_point n m k G z (c z) A R α (R / 4) hR hα
    (by positivity) hG hz (hcamp z (ball_subset_closedBall hzR))
/-- Linear algebra for the `C¹` extension step in the proof of Simon Ch. 5, Theorem 5.2 (p. 121):
the operator norm of a linear map `A : ℝᵐ → ℝᵏ` is at most its Hilbert–Schmidt norm `|A|`, and
`A ↦ |A|` is continuous for the operator-norm topology. -/
theorem allard52_c1h_opNorm_le_hsNorm_continuous : ∀ (m k : ℕ), (∀ A : Rn m →L[ℝ] Rn k, ‖A‖ ≤ hsNorm A) ∧ Continuous (fun A : Rn m →L[ℝ] Rn k => hsNorm A) := by
  intro m k
  refine ⟨fun A => ?_, ?_⟩
  · -- `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
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
  · -- `|A| = √(Σᵢ ‖A eᵢ‖²)`, and each evaluation `A ↦ A eᵢ` is continuous.
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_id.clm_apply continuous_const).norm.pow 2).sqrt
/-- Continuous extension from a dense set with the same Hölder modulus, used for the `C^{1,α}`
conclusion in the proof of Simon Ch. 5, Theorem 5.2 (pp. 121–123).  Let `F : ℝⁿ → L(ℝᵐ, ℝᵏ)`
satisfy `|F(x) − F(y)| ≤ M (‖x − y‖/R)^α` on `Z` (Hilbert–Schmidt norm, `α > 0`), and let
`S ⊆ closure Z`.  Then `g = extendFrom Z F`, the limit of `F` along `Z`, is continuous on `S`,
agrees with `F` on `Z`, and satisfies the same bound on `S`.  Since `‖·‖ ≤ |·|` and
`κ(t) = M (t/R)^α` is continuous with `κ(0) = 0`, the image of `𝓝[Z] x` under `F` is Cauchy, so
it converges in the complete space `L(ℝᵐ, ℝᵏ)`; the bound passes to the limit along
`𝓝[Z] x ×ˢ 𝓝[Z] y` because `|·|` is continuous. -/
theorem allard52_c1h_holder_extension : ∀ (n m k : ℕ) (F : Rn n → (Rn m →L[ℝ] Rn k)) (S Z : Set (Rn n)) (M R α : ℝ), 0 ≤ M → 0 < R → 0 < α → S ⊆ closure Z → (∀ x ∈ Z, ∀ y ∈ Z, hsNorm (F x - F y) ≤ M * (‖x - y‖ / R) ^ α) → ∃ g : Rn n → (Rn m →L[ℝ] Rn k), ContinuousOn g S ∧ (∀ x ∈ Z, g x = F x) ∧ ∀ x ∈ S, ∀ y ∈ S, hsNorm (g x - g y) ≤ M * (‖x - y‖ / R) ^ α := by
  intro n m k F S Z M R α _hM _hR hα hSZ hF
  obtain ⟨hop, hcont⟩ := Submission.allard52_c1h_opNorm_le_hsNorm_continuous m k
  -- The modulus `κ(t) = M (t/R)^α` is continuous, and `κ(0) = 0` since `α ≠ 0`.
  have hκc : Continuous fun t : ℝ => M * (t / R) ^ α :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp (continuous_id.div_const R))
  have hκ0 : M * ((0 : ℝ) / R) ^ α = 0 := by rw [zero_div, Real.zero_rpow hα.ne', mul_zero]
  -- `κ(‖p₁ − p₂‖) → κ(‖x − y‖)` along `𝓝[Z] x ×ˢ 𝓝[Z] y = 𝓝[Z ×ˢ Z] (x, y)`.
  have hmod : ∀ x y : Rn n, Tendsto (fun p : Rn n × Rn n => M * (‖p.1 - p.2‖ / R) ^ α)
      (𝓝[Z] x ×ˢ 𝓝[Z] y) (𝓝 (M * (‖x - y‖ / R) ^ α)) := by
    intro x y
    rw [← nhdsWithin_prod_eq]
    exact ((hκc.comp (continuous_fst.sub continuous_snd).norm).tendsto (x, y)).mono_left
      nhdsWithin_le_nhds
  -- The hypothesis holds eventually along `𝓝[Z] x ×ˢ 𝓝[Z] y`, as `Z ×ˢ Z` belongs to it.
  have hZ : ∀ x y : Rn n, ∀ᶠ p in 𝓝[Z] x ×ˢ 𝓝[Z] y,
      hsNorm (F p.1 - F p.2) ≤ M * (‖p.1 - p.2‖ / R) ^ α := by
    intro x y
    filter_upwards [prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin] with p hp
    exact hF p.1 hp.1 p.2 hp.2
  -- At `x ∈ closure Z`, `dist (F p₁) (F p₂) ≤ |F p₁ − F p₂| ≤ κ(‖p₁ − p₂‖) → κ(0) = 0` along
  -- `𝓝[Z] x ×ˢ 𝓝[Z] x`, so `map F (𝓝[Z] x)` is Cauchy and converges.
  have hlim : ∀ x ∈ closure Z, ∃ A, Tendsto F (𝓝[Z] x) (𝓝 A) := by
    intro x hx
    have := mem_closure_iff_nhdsWithin_neBot.1 hx
    refine cauchy_map_iff_exists_tendsto.1 (cauchy_map_iff.2 ⟨inferInstance, ?_⟩)
    have h0 := hmod x x
    rw [sub_self, norm_zero, hκ0] at h0
    refine tendsto_uniformity_iff_dist_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ h0)
    filter_upwards [hZ x x] with p hp
    exact (dist_eq_norm _ _).trans_le ((hop _).trans hp)
  have hg : ∀ x ∈ closure Z, Tendsto F (𝓝[Z] x) (𝓝 (extendFrom Z F x)) := fun x hx =>
    tendsto_extendFrom (hlim x hx)
  refine ⟨extendFrom Z F, continuousOn_extendFrom hSZ fun x hx => hlim x (hSZ hx),
    fun x hx => ?_, fun x hx y hy => ?_⟩
  · -- On `Z`, `‖F z − F x‖ ≤ κ(‖z − x‖) → 0`, so `F → F x` along `𝓝[Z] x`.
    refine extendFrom_eq (subset_closure hx) (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
    have h0 : Tendsto (fun z : Rn n => M * (‖z - x‖ / R) ^ α) (𝓝[Z] x)
        (𝓝 (M * (‖x - x‖ / R) ^ α)) :=
      ((hκc.comp (continuous_id.sub continuous_const).norm).tendsto x).mono_left
        nhdsWithin_le_nhds
    rw [sub_self, norm_zero, hκ0] at h0
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hop _).trans (hF z hz x hx)
  · -- Pass to the limit in `|F p₁ − F p₂| ≤ κ(‖p₁ − p₂‖)` along `𝓝[Z] x ×ˢ 𝓝[Z] y`.
    have := mem_closure_iff_nhdsWithin_neBot.1 (hSZ hx)
    have := mem_closure_iff_nhdsWithin_neBot.1 (hSZ hy)
    exact le_of_tendsto_of_tendsto ((hcont.tendsto _).comp
      (((hg x (hSZ hx)).comp tendsto_fst).sub ((hg y (hSZ hy)).comp tendsto_snd)))
      (hmod x y) (hZ x y)
/-- Simon Ch. 5, proof of Theorem 5.2 (p. 124, "since `f` is Lipschitz it follows from this that
`f ∈ C^{1,1−n/p}`"), Fubini on lines: if `Lⁿ(N) = 0`, then for all `x, h ∈ ℝⁿ` and `Lⁿ`-a.e. `w`
the line `t ↦ x + w + t h` meets `N` in an `L¹`-null set.  Enclose `N` in a measurable null set
`N'`.  The set `E = {(w, t) : x + w + t h ∈ N'}` is measurable (a preimage under a continuous map),
and each `t`-section `{w : w + (x + t h) ∈ N'}` is a translate of `N'`, hence `Lⁿ`-null.  So
`(Lⁿ × L¹)(E) = 0` by Tonelli, almost every `w`-section of `E` is `L¹`-null, and monotonicity
passes this from `N'` to `N`. -/
theorem allard52_lad_segment_null : ∀ (n : ℕ) (N : Set (Rn n)), volume N = 0 → ∀ (x h : Rn n), ∀ᵐ w ∂(volume : Measure (Rn n)), volume {t : ℝ | x + w + t • h ∈ N} = 0 := by
  intro n N hN x h
  -- A measurable null envelope `N'` of `N`.
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  -- `E = {(w, t) : x + w + t h ∈ N'}` is measurable.
  set E : Set (Rn n × ℝ) := {p | x + p.1 + p.2 • h ∈ N'} with hE
  have hEm : MeasurableSet E :=
    (show Continuous fun p : Rn n × ℝ => x + p.1 + p.2 • h by fun_prop).measurable hN'm
  -- Each `t`-section of `E` is the translate `N' - (x + t h)`, hence null.
  have hsec : ∀ t : ℝ, (volume : Measure (Rn n)) ((fun w => (w, t)) ⁻¹' E) = 0 := by
    intro t
    have hset : (fun w => (w, t)) ⁻¹' E = (fun w => w + (x + t • h)) ⁻¹' N' := by
      ext w
      simp only [mem_preimage, hE, mem_ofPred_eq]
      rw [show x + w + t • h = w + (x + t • h) by abel]
    rw [hset, measure_preimage_add_right]
    exact hN'0
  -- Tonelli: `(Lⁿ × L¹)(E) = ∫⁻ Lⁿ(t-section of E) dt = 0`.
  have hprod : (volume : Measure (Rn n)).prod (volume : Measure ℝ) E = 0 := by
    rw [Measure.prod_apply_symm hEm]
    exact (lintegral_congr hsec).trans lintegral_zero
  -- Hence almost every `w`-section `{t : x + w + t h ∈ N'}` is `L¹`-null, and so is the smaller
  -- set `{t : x + w + t h ∈ N}`.
  rw [Measure.measure_prod_null hEm] at hprod
  filter_upwards [hprod] with w hw
  exact measure_mono_null (fun t ht => hNN' ht) hw

/-- Fundamental theorem of calculus for a Lipschitz curve with an a.e. derivative (node
`lipschitz_ftc` of `lipschitz_ae_derivative`): if `φ : ℝ → ℝ^ℓ` is `L`-Lipschitz on `[a, b]`, `k`
is continuous on `[a, b]` and `φ` has derivative `k(t)` at a.e. `t ∈ (a, b)`, then
`φ(b) - φ(a) = ∫_a^b k`.  The extension `ψ = φ ∘ projIcc a b` is `L`-Lipschitz on `ℝ`, so the
difference quotients `h⁻¹ (ψ(t + h) - ψ(t))` are bounded by `L`; as `h → 0⁺` they tend to `k(t)`
for a.e. `t ∈ (a, b]`, and dominated convergence gives convergence of their integrals over
`[a, b]` to `∫_a^b k`.  For a primitive `G` of the continuous `ψ` the same integrals equal
`h⁻¹ (G(b + h) - G(b)) - h⁻¹ (G(a + h) - G(a))`, which tend to `ψ(b) - ψ(a) = φ(b) - φ(a)`. -/
theorem allard52_lad_lipschitz_ftc : ∀ (ℓ : ℕ) (φ k : ℝ → Rn ℓ) (a b : ℝ) (L : ℝ≥0), a ≤ b → LipschitzOnWith L φ (Icc a b) → ContinuousOn k (Icc a b) → (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → HasDerivAt φ (k t) t) → φ b - φ a = ∫ t in a..b, k t := by
  intro ℓ φ k a b L hab hφ _ hderiv
  -- The extension `ψ = φ ∘ projIcc a b` is `L`-Lipschitz on `ℝ` and agrees with `φ` on `[a, b]`.
  set ψ : ℝ → Rn ℓ := fun t => φ (projIcc a b hab t) with hψ
  have hψL : LipschitzWith L ψ := by
    have h := hφ.to_restrict.comp (LipschitzWith.projIcc hab)
    rw [mul_one] at h
    exact h
  have hψc : Continuous ψ := hψL.continuous
  have hψa : ψ a = φ a := by
    simp only [hψ, projIcc_left]
  have hψb : ψ b = φ b := by
    simp only [hψ, projIcc_right]
  have hψeq : ∀ t ∈ Ioo a b, ψ =ᶠ[𝓝 t] φ := by
    intro t ht
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simp only [hψ, projIcc_of_mem hab hs]
  -- The difference quotients of `ψ` are bounded by `L`.
  have hbound : ∀ h : ℝ, 0 < h → ∀ t : ℝ, ‖h⁻¹ • (ψ (t + h) - ψ t)‖ ≤ L := by
    intro h hh t
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh, ← dist_eq_norm]
    have h1 := hψL.dist_le_mul (t + h) t
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh] at h1
    calc h⁻¹ * dist (ψ (t + h)) (ψ t) ≤ h⁻¹ * (L * h) := by gcongr
      _ = L := by field_simp
  -- Dominated convergence: the integrals of the difference quotients tend to `∫_a^b k`, since
  -- `ψ = φ` near every `t ∈ (a, b)` and `{b}` is null.
  have hlim1 : Tendsto (fun h : ℝ => ∫ t in a..b, h⁻¹ • (ψ (t + h) - ψ t)) (𝓝[>] 0)
      (𝓝 (∫ t in a..b, k t)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (L : ℝ))
      ?_ ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall (fun h => ?_)
      exact (((hψc.comp (continuous_id.add continuous_const)).sub hψc).const_smul
        h⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ae_of_all _ (fun t _ => hbound h hh t)
    · filter_upwards [hderiv, Measure.ae_ne volume b] with t ht htb htI
      rw [uIoc_of_le hab] at htI
      have htIoo : t ∈ Ioo a b := ⟨htI.1, lt_of_le_of_ne htI.2 htb⟩
      exact ((ht htIoo).congr_of_eventuallyEq (hψeq t htIoo)).tendsto_slope_zero_right
  -- The same integrals are difference quotients at `b` and at `a` of a primitive `G` of `ψ`.
  set G : ℝ → Rn ℓ := fun x => ∫ t in a..x, ψ t
  have hGd : ∀ x, HasDerivAt G (ψ x) x := fun x =>
    (hψc.integral_hasStrictDerivAt a x).hasDerivAt
  have hGint : ∀ u v, ∫ t in u..v, ψ t = G v - G u := fun u v =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hGd x) (hψc.intervalIntegrable u v)
  have hrepr : ∀ h : ℝ, ∫ t in a..b, h⁻¹ • (ψ (t + h) - ψ t) =
      h⁻¹ • (G (b + h) - G b) - h⁻¹ • (G (a + h) - G a) := by
    intro h
    have hint : IntervalIntegrable (fun t => ψ (t + h)) volume a b :=
      (hψc.comp (continuous_id.add continuous_const)).intervalIntegrable a b
    rw [intervalIntegral.integral_smul,
      intervalIntegral.integral_sub hint (hψc.intervalIntegrable a b),
      intervalIntegral.integral_comp_add_right ψ h, hGint (a + h) (b + h), hGint a b, ← smul_sub]
    congr 1
    abel
  have hlim2 : Tendsto (fun h : ℝ => ∫ t in a..b, h⁻¹ • (ψ (t + h) - ψ t)) (𝓝[>] 0)
      (𝓝 (ψ b - ψ a)) := by
    simp only [hrepr]
    exact (hGd b).tendsto_slope_zero_right.sub (hGd a).tendsto_slope_zero_right
  rw [← hψa, ← hψb]
  exact tendsto_nhds_unique hlim2 hlim1

/-- Simon Ch. 5, proof of Theorem 5.2 (p. 124, "since `f` is Lipschitz it follows from this that
`f ∈ C^{1,1−n/p}`"): continuity of the segment integral `I(a, b) = ∫₀¹ g(a + τ(b − a))(b − a) dτ`
on `U × U` for an operator field `g` continuous on an open convex `U`.  At `(a₀, b₀) ∈ U × U` the
segment `[a₀, b₀] ⊆ U` is compact, so a closed `δ`-thickening of it is a compact subset of `U` on
which `‖g‖ ≤ M`; it contains `[a, b]` whenever `‖a − a₀‖, ‖b − b₀‖ < δ`, and then
`‖b − a‖ ≤ ‖b₀ − a₀‖ + 2δ`.  Dominated convergence with the constant bound `M (‖b₀ − a₀‖ + 2δ)`
gives continuity at `(a₀, b₀)`. -/
theorem allard52_lad_segment_integral_continuousOn : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)), IsOpen U → Convex ℝ U → ContinuousOn g U → ContinuousOn (fun p : Rn n × Rn n => ∫ τ in (0:ℝ)..1, g (p.1 + τ • (p.2 - p.1)) (p.2 - p.1)) (U ×ˢ U) := by
  intro n ℓ g U hU hconv hg
  rintro ⟨a₀, b₀⟩ ⟨ha₀, hb₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  -- The segment `S₀ = [a₀, b₀]` is compact and lies in `U` by convexity.
  set S₀ : Set (Rn n) := (fun τ : ℝ => a₀ + τ • (b₀ - a₀)) '' Icc (0 : ℝ) 1
  have hS₀c : IsCompact S₀ := isCompact_Icc.image (by fun_prop)
  have hS₀U : S₀ ⊆ U := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hconv.add_smul_sub_mem ha₀ hb₀ hτ
  -- A closed `δ`-thickening `C` of `S₀` is a compact subset of `U`, on which `‖g‖ ≤ M`.
  obtain ⟨δ, hδ, hδU⟩ := hS₀c.exists_cthickening_subset_open hU hS₀U
  obtain ⟨M, hM⟩ := hS₀c.cthickening.exists_bound_of_continuousOn (hg.mono hδU)
  have hM0 : 0 ≤ M :=
    (norm_nonneg _).trans (hM a₀ (self_subset_cthickening S₀ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩))
  -- If `‖a - a₀‖, ‖b - b₀‖ < δ`, the whole segment `[a, b]` lies in `C`.
  have hmem : ∀ a b : Rn n, dist a a₀ < δ → dist b b₀ < δ → ∀ τ ∈ Icc (0 : ℝ) 1,
      a + τ • (b - a) ∈ cthickening δ S₀ := by
    intro a b ha hb τ hτ
    refine mem_cthickening_of_dist_le _ (a₀ + τ • (b₀ - a₀)) _ _ ⟨τ, hτ, rfl⟩ ?_
    have heq : a + τ • (b - a) - (a₀ + τ • (b₀ - a₀)) = (1 - τ) • (a - a₀) + τ • (b - b₀) := by
      module
    rw [dist_eq_norm] at ha hb ⊢
    rw [heq]
    calc ‖(1 - τ) • (a - a₀) + τ • (b - b₀)‖
        ≤ ‖(1 - τ) • (a - a₀)‖ + ‖τ • (b - b₀)‖ := norm_add_le _ _
      _ = (1 - τ) * ‖a - a₀‖ + τ * ‖b - b₀‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hτ.2),
          Real.norm_of_nonneg hτ.1]
      _ ≤ (1 - τ) * δ + τ * δ := by
        gcongr
        · exact sub_nonneg.2 hτ.2
        · exact hτ.1
      _ = δ := by ring
  -- ... and `‖b - a‖ ≤ ‖b₀ - a₀‖ + 2δ`.
  have hlen : ∀ a b : Rn n, dist a a₀ < δ → dist b b₀ < δ → ‖b - a‖ ≤ ‖b₀ - a₀‖ + 2 * δ := by
    intro a b ha hb
    rw [dist_eq_norm] at ha hb
    have heq : b - a = (b₀ - a₀) + (b - b₀) - (a - a₀) := by abel
    calc ‖b - a‖ = ‖(b₀ - a₀) + (b - b₀) - (a - a₀)‖ := by rw [heq]
      _ ≤ ‖(b₀ - a₀) + (b - b₀)‖ + ‖a - a₀‖ := norm_sub_le _ _
      _ ≤ ‖b₀ - a₀‖ + ‖b - b₀‖ + ‖a - a₀‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖b₀ - a₀‖ + 2 * δ := by linarith
  have hW : ∀ᶠ p : Rn n × Rn n in 𝓝 (a₀, b₀), dist p.1 a₀ < δ ∧ dist p.2 b₀ < δ := by
    filter_upwards [ball_mem_nhds (a₀, b₀) hδ] with p hp
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hp
    exact hp
  have hIoc : uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  -- Dominated convergence with the constant bound `M (‖b₀ - a₀‖ + 2δ)`.
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (p : Rn n × Rn n) (τ : ℝ) => g (p.1 + τ • (p.2 - p.1)) (p.2 - p.1))
    (bound := fun _ => M * (‖b₀ - a₀‖ + 2 * δ)) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hW] with p hp
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    exact hg.comp (by fun_prop) fun τ hτ => hδU (hmem p.1 p.2 hp.1 hp.2 τ (hIoc hτ))
  · filter_upwards [hW] with p hp
    refine ae_of_all _ fun τ hτ => ?_
    calc ‖g (p.1 + τ • (p.2 - p.1)) (p.2 - p.1)‖
        ≤ ‖g (p.1 + τ • (p.2 - p.1))‖ * ‖p.2 - p.1‖ := (g _).le_opNorm _
      _ ≤ M * (‖b₀ - a₀‖ + 2 * δ) :=
        mul_le_mul (hM _ (hmem p.1 p.2 hp.1 hp.2 τ (hIoc hτ))) (hlen p.1 p.2 hp.1 hp.2)
          (norm_nonneg _) hM0
  · refine ae_of_all _ fun τ hτ => ?_
    have hgτ : ContinuousAt g (a₀ + τ • (b₀ - a₀)) :=
      hg.continuousAt (hU.mem_nhds (hS₀U ⟨τ, hIoc hτ, rfl⟩))
    have hseg : ContinuousAt (fun p : Rn n × Rn n => p.1 + τ • (p.2 - p.1)) (a₀, b₀) := by
      fun_prop
    exact (hgτ.comp_of_eq hseg rfl).clm_apply (by fun_prop)

/-- Simon Ch. 5, end of the proof of Theorem 5.2 (p. 124: a Lipschitz `f` whose a.e. derivative
is continuous is `C¹`).  The integral mean-value formula
`f(y) − f(x) = ∫₀¹ g(x + τ(y − x))(y − x) dτ` for `x, y` in an open convex `U`, when `f` is
Lipschitz on `U`, `g` is continuous on `U` and `Df = g` a.e. in `U`.  Put
`F(w) = f(y + w) − f(x + w) − I(x + w, y + w)` with `I` the segment integral.  If the line
`t ↦ x + w + t(y − x)` meets the null set where `Df = g` fails in an `L¹`-null set, the Lipschitz
fundamental theorem of calculus along it gives `F(w) = 0`; by Fubini this holds for a.e. `w` near
`0`, and `F` is continuous there, so `F(0) = 0`. -/
theorem allard52_lad_line_integral_rep : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (K : ℝ≥0), IsOpen U → Convex ℝ U → LipschitzOnWith K f U → ContinuousOn g U → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ U → HasFDerivAt f (g x) x) → ∀ x ∈ U, ∀ y ∈ U, f y - f x = ∫ τ in (0:ℝ)..1, g (x + τ • (y - x)) (y - x) := by
  intro n ℓ f g U K hU hUc hf hg hae x hx y hy
  -- The bad set `N₀ = {p ∈ U : Df(p) ≠ g(p)}` is Lebesgue-null.
  let N₀ : Set (Rn n) := {p | ¬(p ∈ U → HasFDerivAt f (g p) p)}
  have hN₀ : volume N₀ = 0 := ae_iff.mp hae
  -- A ball `B̆_ρ(0)` of translations `w` with `x + w, y + w ∈ U`.
  obtain ⟨ρ₁, hρ₁, hxU⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨ρ₂, hρ₂, hyU⟩ := Metric.isOpen_iff.mp hU y hy
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hxw : ∀ w ∈ ball (0 : Rn n) (min ρ₁ ρ₂), x + w ∈ U := fun w hw =>
    hxU (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_zero_iff.mp hw).trans_le (min_le_left _ _))
  have hyw : ∀ w ∈ ball (0 : Rn n) (min ρ₁ ρ₂), y + w ∈ U := fun w hw =>
    hyU (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_zero_iff.mp hw).trans_le (min_le_right _ _))
  -- `F(w) = f(y + w) − f(x + w) − I(x + w, y + w)`; the claim is `F(0) = 0`.
  let I : Rn n × Rn n → Rn ℓ := fun p =>
    ∫ τ in (0:ℝ)..1, g (p.1 + τ • (p.2 - p.1)) (p.2 - p.1)
  let F : Rn n → Rn ℓ := fun w => f (y + w) - f (x + w) - I (x + w, y + w)
  -- `F(w) = 0` if `w ∈ B̆_ρ(0)` and the line `t ↦ x + w + t(y − x)` meets `N₀` in a null set.
  have hgood : ∀ w ∈ ball (0 : Rn n) (min ρ₁ ρ₂),
      volume {t : ℝ | x + w + t • (y - x) ∈ N₀} = 0 → F w = 0 := by
    intro w hw hnull
    have hseg : ∀ t ∈ Icc (0:ℝ) 1, x + w + t • (y - x) ∈ U := fun t ht => by
      simpa only [add_sub_add_right_eq_sub] using hUc.add_smul_sub_mem (hxw w hw) (hyw w hw) ht
    let φ : ℝ → Rn ℓ := fun t => f (x + w + t • (y - x))
    let k : ℝ → Rn ℓ := fun t => g (x + w + t • (y - x)) (y - x)
    -- `φ` is `K‖y − x‖`-Lipschitz on `[0, 1]`.
    have hφ : LipschitzOnWith (K * ‖y - x‖₊) φ (Icc 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun t ht t' ht' => ?_
      calc dist (φ t) (φ t')
          ≤ K * dist (x + w + t • (y - x)) (x + w + t' • (y - x)) :=
            hf.dist_le_mul _ (hseg t ht) _ (hseg t' ht')
        _ = ↑(K * ‖y - x‖₊) * dist t t' := by
            rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.dist_eq,
              Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm]
            ring
    -- `k` is continuous on `[0, 1]`.
    have hk : ContinuousOn k (Icc 0 1) :=
      (hg.comp (by fun_prop : Continuous fun t : ℝ => x + w + t • (y - x)).continuousOn
        fun t ht => hseg t ht).clm_apply continuousOn_const
    -- For a.e. `t ∈ (0, 1)`, `φ'(t) = k(t)` by the chain rule.
    have hderiv : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0:ℝ) 1 → HasDerivAt φ (k t) t := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htI
      have hfd : HasFDerivAt f (g (x + w + t • (y - x))) (x + w + t • (y - x)) :=
        not_not.mp ht (hseg t (Ioo_subset_Icc_self htI))
      have hσ : HasDerivAt (fun t : ℝ => x + w + t • (y - x)) (y - x) t := by
        simpa only [one_smul] using ((hasDerivAt_id' t).smul_const (y - x)).const_add (x + w)
      exact hfd.comp_hasDerivAt t hσ
    -- The Lipschitz fundamental theorem of calculus for `φ` on `[0, 1]`.
    have hftc := Submission.allard52_lad_lipschitz_ftc ℓ φ k 0 1 (K * ‖y - x‖₊) zero_le_one hφ
      hk hderiv
    have hyx : x + w + (y - x) = y + w := by abel
    simp only [φ, k, zero_smul, add_zero, one_smul, hyx] at hftc
    show f (y + w) - f (x + w) - I (x + w, y + w) = 0
    simp only [I, add_sub_add_right_eq_sub, ← hftc, sub_self]
  -- By Fubini (`segment_null`), `F = 0` a.e. on `B̆_ρ(0)`.
  have hFae : F =ᵐ[volume.restrict (ball (0 : Rn n) (min ρ₁ ρ₂))] 0 := by
    refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards [Submission.allard52_lad_segment_null n N₀ hN₀ x (y - x)] with w hw hwB
    exact hgood w hwB hw
  -- `F` is continuous on `B̆_ρ(0)`: `f` is Lipschitz and `I` is continuous on `U × U`.
  have hFc : ContinuousOn F (ball (0 : Rn n) (min ρ₁ ρ₂)) := by
    have hfU : ContinuousOn f U := hf.continuousOn
    have hIc : ContinuousOn I (U ×ˢ U) :=
      Submission.allard52_lad_segment_integral_continuousOn n ℓ g U hU hUc hg
    exact ((hfU.comp (by fun_prop : Continuous fun w : Rn n => y + w).continuousOn hyw).sub
      (hfU.comp (by fun_prop : Continuous fun w : Rn n => x + w).continuousOn hxw)).sub
      (hIc.comp (by fun_prop : Continuous fun w : Rn n => (x + w, y + w)).continuousOn
        fun w hw => ⟨hxw w hw, hyw w hw⟩)
  -- A continuous function vanishing a.e. on an open set vanishes there; evaluate at `w = 0`.
  have hF0 : F 0 = 0 :=
    Measure.eqOn_open_of_ae_eq hFae isOpen_ball hFc continuousOn_const (mem_ball_self hρ)
  simpa only [F, I, add_zero, sub_eq_zero] using hF0

/-- Simon Ch. 5, proof of Theorem 5.2 (p. 124, "since `f` is Lipschitz it follows from this that
`f ∈ C^{1,1−n/p}`"): Fréchet differentiability from the integral mean-value formula.  If `g` is
continuous on an open `U ∋ x` and `f(y) − f(x) = ∫₀¹ g(x + τ(y − x))(y − x) dτ` for all `y ∈ U`,
then `Df(x) = g(x)`.  Given `ε > 0`, pick `η > 0` with `B̆_η(x) ⊆ U` and `‖g(z) − g(x)‖ < ε` on
`B̆_η(x)`; for `‖h‖ < η` the segment `[x, x + h]` lies in `B̆_η(x)`, so the remainder
`f(x + h) − f(x) − g(x)h = ∫₀¹ (g(x + τh) − g(x))h dτ` has norm at most `ε‖h‖`. -/
theorem allard52_lad_hasFDerivAt_of_line_integral : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (x : Rn n), IsOpen U → x ∈ U → ContinuousOn g U → (∀ y ∈ U, f y - f x = ∫ τ in (0:ℝ)..1, g (x + τ • (y - x)) (y - x)) → HasFDerivAt f (g x) x := by
  intro n ℓ f g U x hU hx hg hf
  -- Little-o criterion: for each `ε > 0`, eventually `‖f(x + h) − f(x) − g(x)h‖ ≤ ε‖h‖`.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  -- Choose `η > 0` with `B̆_η(x) ⊆ U` and `‖g(z) − g(x)‖ < ε` for `z ∈ B̆_η(x)`.
  obtain ⟨η₁, hη₁, hη₁U⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨η₂, hη₂, hη₂g⟩ := Metric.continuousAt_iff.1 (hg.continuousAt (hU.mem_nhds hx)) ε hε
  obtain ⟨η, hη, hηη₁, hηη₂⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ η₂ :=
    ⟨min η₁ η₂, lt_min hη₁ hη₂, min_le_left _ _, min_le_right _ _⟩
  filter_upwards [ball_mem_nhds (0 : Rn n) hη] with h hh
  rw [mem_ball_zero_iff] at hh
  -- For `‖h‖ < η` the segment `x + τh`, `τ ∈ [0, 1]`, lies in `B̆_η(x) ⊆ U`.
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, dist (x + τ • h) x < η := by
    intro τ hτ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.1]
    calc τ * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg h)
      _ < η := by rwa [one_mul]
  have hsegU : MapsTo (fun τ : ℝ => x + τ • h) (Icc 0 1) U := fun τ hτ =>
    hη₁U (mem_ball.2 ((hseg τ hτ).trans_le hηη₁))
  have hfh := hf (x + h) (by simpa using hsegU ⟨zero_le_one, le_rfl⟩)
  rw [add_sub_cancel_left] at hfh
  -- The remainder is `∫₀¹ (g(x + τh)h − g(x)h) dτ`.
  have hint : IntervalIntegrable (fun τ : ℝ => g (x + τ • h) h) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hg.comp (by fun_prop) hsegU).clm_apply continuousOn_const
  have hrem : f (x + h) - f x - g x h = ∫ τ in (0:ℝ)..1, (g (x + τ • h) h - g x h) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hfh,
      intervalIntegral.integral_const, sub_zero, one_smul]
  -- On `uIoc 0 1` the integrand has norm `‖(g(x + τh) − g(x))h‖ ≤ ε‖h‖`.
  have hbound : ∀ τ ∈ uIoc (0 : ℝ) 1, ‖g (x + τ • h) h - g x h‖ ≤ ε * ‖h‖ := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    have hgτ : dist (g (x + τ • h)) (g x) < ε :=
      hη₂g ((hseg τ (Ioc_subset_Icc_self hτ)).trans_le hηη₂)
    rw [dist_eq_norm] at hgτ
    calc ‖g (x + τ • h) h - g x h‖ = ‖(g (x + τ • h) - g x) h‖ := by
          rw [sub_apply]
      _ ≤ ‖g (x + τ • h) - g x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hgτ.le (norm_nonneg h)
  rw [hrem]
  calc ‖∫ τ in (0:ℝ)..1, (g (x + τ • h) h - g x h)‖ ≤ ε * ‖h‖ * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε * ‖h‖ := by rw [sub_zero, abs_one, mul_one]

/-- Simon Ch. 5, proof of Theorem 5.2 (p. 124: "Since `f` is Lipschitz it follows from this that
`f ∈ C^{1,1−n/p}`"), for an arbitrary continuous a.e. derivative: if `f` is `K`-Lipschitz on the
open ball `B̆_r(c)`, `g` is continuous on `B̆_r(c)` and `Df(x) = g(x)` for `Lⁿ`-a.e.
`x ∈ B̆_r(c)`, then `Df(x) = g(x)` at every `x ∈ B̆_r(c)`.  The ball is open and convex, so
`f(y) − f(x) = ∫₀¹ g(x + τ(y − x))(y − x) dτ` for all `x, y ∈ B̆_r(c)`
(`allard52_lad_line_integral_rep`), and continuity of `g` at `x` turns this formula into
differentiability at `x` (`allard52_lad_hasFDerivAt_of_line_integral`). -/
theorem allard52_lipschitz_hasFDerivAt_of_ae : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (c : Rn n) (r : ℝ) (K : ℝ≥0), LipschitzOnWith K f (ball c r) → ContinuousOn g (ball c r) → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball c r → HasFDerivAt f (g x) x) → ∀ x ∈ ball c r, HasFDerivAt f (g x) x := by
  intro n ℓ f g c r K hf hg hae x hx
  -- Steps 0–3: the integral mean-value formula on the open convex ball.
  have hrep : ∀ y ∈ ball c r, f y - f x = ∫ τ in (0:ℝ)..1, g (x + τ • (y - x)) (y - x) :=
    Submission.allard52_lad_line_integral_rep n ℓ f g (ball c r) K isOpen_ball
      (convex_ball c r) hf hg hae x hx
  -- Step 4: continuity of `g` at `x` upgrades the formula to the Fréchet derivative `g x` at `x`.
  exact Submission.allard52_lad_hasFDerivAt_of_line_integral n ℓ f g (ball c r) x isOpen_ball hx
    hg hrep
/-- **A Lipschitz map whose derivative is Hölder on a full-measure set is `C¹` with the same
Hölder bound** (Simon Ch. 5, proof of Theorem 5.2: regularity of the graph function `u`).
Let `f` be `K`-Lipschitz on `B = B̆_r(c)`, differentiable at every point of `Z ⊆ B` with
`Lⁿ(B \ Z) = 0`, and `|Df(x) − Df(y)| ≤ M (|x − y|/R)^α` for `x, y ∈ Z` (Hilbert–Schmidt norm,
`M ≥ 0`, `R, α > 0`).  Then `f ∈ C¹(B)` and the same bound holds for all `x, y ∈ B`.
`B \ closure Z` is an open null set, hence empty, so `allard52_c1h_holder_extension` extends
`Df|_Z` to a map `g` which is continuous and satisfies the bound on `B`.  `f` has derivative
`g x` at every `x ∈ Z`, i.e. at a.e. `x ∈ B`, hence at every `x ∈ B` by
`allard52_lipschitz_hasFDerivAt_of_ae`; so `Df = g` on `B`. -/
theorem allard52_c1_holder_of_ae_fderiv : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (c : Rn n) (r : ℝ) (K : ℝ≥0) (Z : Set (Rn n)) (M R α : ℝ), 0 ≤ M → 0 < R → 0 < α → LipschitzOnWith K f (ball c r) → Z ⊆ ball c r → volume (ball c r \ Z) = 0 → (∀ x ∈ Z, DifferentiableAt ℝ f x) → (∀ x ∈ Z, ∀ y ∈ Z, hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ M * (‖x - y‖ / R) ^ α) → ContDiffOn ℝ 1 f (ball c r) ∧ ∀ x ∈ ball c r, ∀ y ∈ ball c r, hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ M * (‖x - y‖ / R) ^ α := by
  intro n ℓ f c r K Z M R α hM hR hα hf _hZ hnull hdiff hhol
  -- `Z` is dense in `B`: `B \ closure Z` is open and null, hence empty.
  have hdense : ball c r ⊆ closure Z :=
    sdiff_eq_empty.mp <| (isOpen_ball.sdiff isClosed_closure).eq_empty_of_measure_zero <|
      measure_mono_null (sdiff_subset_sdiff_right subset_closure) hnull
  obtain ⟨g, hg, hgZ, hgB⟩ := Submission.allard52_c1h_holder_extension n n ℓ (fderiv ℝ f)
    (ball c r) Z M R α hM hR hα hdense hhol
  -- `f` has derivative `g x` at every `x ∈ Z`, hence at a.e. `x ∈ B`.
  have hae : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball c r → HasFDerivAt f (g x) x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxB
    have hxZ : x ∈ Z := not_not.mp fun h => hx ⟨hxB, h⟩
    exact hgZ x hxZ ▸ (hdiff x hxZ).hasFDerivAt
  have hfd := Submission.allard52_lipschitz_hasFDerivAt_of_ae n ℓ f g c r K hf hg hae
  have hfg : EqOn (fderiv ℝ f) g (ball c r) := fun x hx => (hfd x hx).fderiv
  refine ⟨?_, fun x hx y hy => hfg hx ▸ hfg hy ▸ hgB x hx y hy⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  exact ⟨fun x hx => (hfd x hx).differentiableAt.differentiableWithinAt,
    fun h => absurd h WithTop.coe_ne_top, contDiffOn_zero.mpr (hg.congr hfg)⟩
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

/-- **Simon Ch. 5, proof of Theorem 5.2, steps (1)–(7) (pp. 122–123), with Remark 4.6 (p. 116).**
Assuming the Tilt-excess Decay Theorem 4.5, iterate it at the radii `η^j σ` to get `n`-planes `S_j`
with `E_*(ξ, η^j σ, S_j) ≤ η^{2(1−n/p)j} E_*(ξ, σ, S₀)`.  The density lower bound of
`allard52_density_bounds` gives `|p_{S_{j+1}} − p_{S_j}|² ≤ C η^{2(1−n/p)j} E_*(ξ, σ, S₀)`, so
`p_{S_j} → p_S` for an `n`-plane `S`; its upper bound interpolates between the radii `η^j σ`, giving
`E(ξ, s, S) ≤ C (s/σ)^{2(1−n/p)} E_*(ξ, σ, S₀)` for `0 < s ≤ σ`.  `δ₁ = min δ₀ δ_P` and `C`
depend only on `n, ℓ, p`. -/
theorem allard52_excess_iteration : TiltExcessDecayTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ S₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S₀ = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ hsNormSq (S.starProjection - S₀.starProjection) ≤ C * V.tiltExcessStar H p δ ξ σ S₀ ∧ ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess ξ s S ≤ C * (s / σ) ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ S₀ := by
  -- Step 0 (Hilbert–Schmidt norm facts): continuity of hsNormSq, 0 ≤ |X|², |X|² = hsNorm², |X − Y|² ≤ 2|X|² + 2|Y|², triangle inequality, ‖X‖ ≤ |X|.
  have hHS : ∀ (m k : ℕ), Continuous (fun X : Rn m →L[ℝ] Rn k => hsNormSq X) ∧ ∀ X Y : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq X ∧ hsNorm X ^ 2 = hsNormSq X ∧ hsNormSq (X - Y) ≤ 2 * hsNormSq X + 2 * hsNormSq Y ∧ hsNorm (X + Y) ≤ hsNorm X + hsNorm Y ∧ ‖X‖ ≤ hsNorm X := by
    intro m k
    -- the vector of columns, as an element of the L² product space
    let col : (Rn m →L[ℝ] Rn k) → PiLp 2 (fun _ : Fin m => Rn k) :=
      fun X => WithLp.toLp 2 (fun i => X (EuclideanSpace.single i 1))
    have hcol_norm : ∀ X : Rn m →L[ℝ] Rn k, ‖col X‖ = hsNorm X := by
      intro X
      simp only [col, hsNorm, hsNormSq, PiLp.norm_eq_of_L2]
    have hcol_add : ∀ X Y : Rn m →L[ℝ] Rn k, col (X + Y) = col X + col Y := by
      intro X Y
      rfl
    have hnonneg : ∀ X : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq X := by
      intro X
      unfold hsNormSq
      positivity
    refine ⟨?_, ?_⟩
    · unfold hsNormSq
      refine continuous_finsetSum _ (fun i _ => ?_)
      exact ((continuous_id.clm_apply continuous_const).norm).pow 2
    intro X Y
    have hsq : hsNorm X ^ 2 = hsNormSq X := by
      unfold hsNorm
      exact Real.sq_sqrt (hnonneg X)
    refine ⟨hnonneg X, hsq, ?_, ?_, ?_⟩
    · unfold hsNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      simp only [sub_apply]
      have h1 := norm_sub_le (X (EuclideanSpace.single i 1)) (Y (EuclideanSpace.single i 1))
      have h2 := norm_nonneg (X (EuclideanSpace.single i 1) - Y (EuclideanSpace.single i 1))
      nlinarith [sq_nonneg (‖X (EuclideanSpace.single i 1)‖ - ‖Y (EuclideanSpace.single i 1)‖),
        norm_nonneg (X (EuclideanSpace.single i 1)), norm_nonneg (Y (EuclideanSpace.single i 1))]
    · rw [← hcol_norm, ← hcol_norm, ← hcol_norm, hcol_add]
      exact norm_add_le _ _
    · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
      -- expand v in the standard basis
      have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hXv : X v = ∑ i, v i • X (EuclideanSpace.single i 1) := by
        conv_lhs => rw [hv]
        simp [map_sum, map_smul]
      calc ‖X v‖ = ‖∑ i, v i • X (EuclideanSpace.single i 1)‖ := by rw [hXv]
        _ ≤ ∑ i, ‖v i • X (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
        _ = ∑ i, |v i| * ‖X (EuclideanSpace.single i 1)‖ := by
            simp [norm_smul, Real.norm_eq_abs]
        _ ≤ Real.sqrt (∑ i, |v i| ^ 2) * Real.sqrt (∑ i, ‖X (EuclideanSpace.single i 1)‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = hsNorm X * ‖v‖ := by
            rw [mul_comm]
            congr 1
            rw [EuclideanSpace.norm_eq]
            simp [Real.norm_eq_abs]
  -- Step 1 (integrability; book Remark 4.6): on B_r(z) ⊆ U the tilt integrand is integrable, the integral is monotone in r, and the two integrated triangle inequalities hold.
  have hTI : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (z : Amb n ℓ) (r : ℝ), closedBall z r ⊆ U → ∀ T₁ T₂ : Submodule ℝ (Amb n ℓ), V.weight (closedBall z r) < ⊤ ∧ IntegrableOn (fun x => hsNormSq (V.tangentProj x - T₁.starProjection)) (closedBall z r) V.weight ∧ (∀ r' : ℝ, r' ≤ r → ∫ x in closedBall z r', hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight ≤ ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight) ∧ (V.weight (closedBall z r)).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) ≤ 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight + 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight ∧ ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight ≤ 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight + 2 * (V.weight (closedBall z r)).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) := by
    intro n ℓ U V hmeas z r hzr T₁ T₂
    have hA := hHS (n + ℓ) (n + ℓ)
    set B : Set (Amb n ℓ) := closedBall z r with hB_def
    have hBmeas : MeasurableSet B := measurableSet_closedBall
    -- Step 1: finite measure of the ball
    have hfin : V.weight B < ⊤ := by
      have hK : IsCompact B := isCompact_closedBall z r
      have hint := V.integrableOn_mult B hK hzr
      unfold RectifiableVarifold.weight
      rw [withDensity_apply _ hBmeas, Measure.restrict_restrict hBmeas]
      refine lt_of_le_of_lt ?_ hint.2
      rw [Set.inter_comm]
      refine lintegral_mono (fun x => ?_)
      exact ENNReal.ofReal_le_of_le_toReal (by simp [Real.norm_eq_abs, le_abs_self])
    -- Step 2: pointwise bound and integrability
    have hproj_le : ∀ x (v : Amb n ℓ), ‖V.tangentProj x v‖ ≤ ‖v‖ := by
      intro x v
      unfold RectifiableVarifold.tangentProj
      split_ifs with h
      · exact Submodule.norm_starProjection_apply_le _ v
      · simp
    have hbound : ∀ (x : Amb n ℓ) (T : Submodule ℝ (Amb n ℓ)),
        hsNormSq (V.tangentProj x - T.starProjection) ≤ 4 * (n + ℓ : ℕ) := by
      intro x T
      unfold hsNormSq
      calc ∑ i : Fin (n + ℓ), ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ _i : Fin (n + ℓ), (4 : ℝ) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have h1 := hproj_le x (EuclideanSpace.single i (1 : ℝ))
            have h2 := Submodule.norm_starProjection_apply_le T (EuclideanSpace.single i (1 : ℝ))
            rw [PiLp.norm_single, norm_one] at h1 h2
            rw [sub_apply]
            have h3 := norm_sub_le (V.tangentProj x (EuclideanSpace.single i 1))
              (T.starProjection (EuclideanSpace.single i 1))
            have h4 := norm_nonneg ((V.tangentProj x) (EuclideanSpace.single i 1) -
              T.starProjection (EuclideanSpace.single i 1))
            have h5 : ‖(V.tangentProj x) (EuclideanSpace.single i 1) -
                T.starProjection (EuclideanSpace.single i 1)‖ ≤ 2 := by
              linarith only [h1, h2, h3]
            calc ‖(V.tangentProj x) (EuclideanSpace.single i 1) -
                  T.starProjection (EuclideanSpace.single i 1)‖ ^ 2 ≤ 2 ^ 2 :=
                  pow_le_pow_left₀ h4 h5 2
              _ = 4 := by norm_num
        _ = 4 * (n + ℓ : ℕ) := by simp [mul_comm]
    have hint : ∀ T : Submodule ℝ (Amb n ℓ),
        IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) B V.weight := by
      intro T
      refine Measure.integrableOn_of_bounded (M := 4 * (n + ℓ : ℕ)) hfin.ne ?_ ?_
      · have h1 : AEStronglyMeasurable (fun x => V.tangentProj x - T.starProjection) V.weight :=
          hmeas.sub aestronglyMeasurable_const
        exact hA.1.comp_aestronglyMeasurable h1
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg ((hA.2 _ 0).1)]
        exact hbound x T
    have hconst : ∀ c : ℝ, IntegrableOn (fun _ : Amb n ℓ => c) B V.weight :=
      fun c => integrableOn_const hfin.ne
    refine ⟨hfin, hint T₁, ?_, ?_, ?_⟩
    · -- monotonicity in the radius
      intro r' hr'
      refine setIntegral_mono_set (hint T₁) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => (hA.2 _ 0).1)
      · exact Filter.Eventually.of_forall (closedBall_subset_closedBall hr')
    · -- two planes vs. one point
      have hpt : ∀ x, hsNormSq (T₁.starProjection - T₂.starProjection) ≤
          2 * hsNormSq (V.tangentProj x - T₁.starProjection) +
            2 * hsNormSq (V.tangentProj x - T₂.starProjection) := by
        intro x
        have h := (hA.2 (V.tangentProj x - T₂.starProjection) (V.tangentProj x - T₁.starProjection)).2.2.1
        have heq : (V.tangentProj x - T₂.starProjection) - (V.tangentProj x - T₁.starProjection) =
            T₁.starProjection - T₂.starProjection := sub_sub_sub_cancel_left _ _ _
        rw [heq] at h
        linarith only [h]
      calc (V.weight B).toReal * hsNormSq (T₁.starProjection - T₂.starProjection)
          = ∫ _x in B, hsNormSq (T₁.starProjection - T₂.starProjection) ∂V.weight := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def]
        _ ≤ ∫ x in B, (2 * hsNormSq (V.tangentProj x - T₁.starProjection) +
              2 * hsNormSq (V.tangentProj x - T₂.starProjection)) ∂V.weight :=
            setIntegral_mono (hconst _) (((hint T₁).const_mul 2).add ((hint T₂).const_mul 2)) hpt
        _ = 2 * ∫ x in B, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight +
              2 * ∫ x in B, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight := by
            rw [integral_add ((hint T₁).const_mul 2) ((hint T₂).const_mul 2), integral_const_mul,
              integral_const_mul]
    · -- changing the plane
      have hpt : ∀ x, hsNormSq (V.tangentProj x - T₁.starProjection) ≤
          2 * hsNormSq (V.tangentProj x - T₂.starProjection) +
            2 * hsNormSq (T₁.starProjection - T₂.starProjection) := by
        intro x
        have h := (hA.2 (V.tangentProj x - T₂.starProjection) (T₁.starProjection - T₂.starProjection)).2.2.1
        have heq : (V.tangentProj x - T₂.starProjection) - (T₁.starProjection - T₂.starProjection) =
            V.tangentProj x - T₁.starProjection := sub_sub_sub_cancel_right _ _ _
        rw [heq] at h
        linarith only [h]
      calc ∫ x in B, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight
          ≤ ∫ x in B, (2 * hsNormSq (V.tangentProj x - T₂.starProjection) +
              2 * hsNormSq (T₁.starProjection - T₂.starProjection)) ∂V.weight :=
            setIntegral_mono (hint T₁) (((hint T₂).const_mul 2).add (hconst _)) hpt
        _ = 2 * ∫ x in B, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight +
              2 * (V.weight B).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) := by
            rw [integral_add ((hint T₂).const_mul 2) (hconst _), integral_const_mul,
              setIntegral_const, smul_eq_mul, Measure.real_def]
            ring
  -- Step 4 (limit plane; book (4)–(6)): geometric increments give a Cauchy sequence of projections whose limit is p_T with dim T = n, with the tail bound.
  have hPL : ∀ (n ℓ : ℕ) (S : ℕ → Submodule ℝ (Amb n ℓ)) (b lam : ℝ), 0 ≤ b → 0 ≤ lam → lam < 1 → (∀ j : ℕ, Module.finrank ℝ (S j) = n) → (∀ j : ℕ, hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) ≤ b * lam ^ j) → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ ∀ k : ℕ, hsNormSq (T.starProjection - (S k).starProjection) ≤ b * lam ^ k / (1 - Real.sqrt lam) ^ 2 := by
    intro n ℓ S b lam hb hlam0 hlam1 hrank hstep
    have hA := hHS (n + ℓ) (n + ℓ)
    set q := Real.sqrt lam with hq_def
    set a := Real.sqrt b with ha_def
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq1 : q < 1 := by
      rw [hq_def, Real.sqrt_lt' one_pos]; simpa using hlam1
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hsq_a : a ^ 2 = b := Real.sq_sqrt hb
    have hsq_q : q ^ 2 = lam := Real.sq_sqrt hlam0
    let P : ℕ → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun j => (S j).starProjection
    -- Step 1: consecutive Hilbert–Schmidt distances
    have hstep' : ∀ j, hsNorm (P (j + 1) - P j) ≤ a * q ^ j := by
      intro j
      have h : hsNormSq (P (j + 1) - P j) ≤ (a * q ^ j) ^ 2 := by
        calc hsNormSq (P (j + 1) - P j) ≤ b * lam ^ j := hstep j
          _ = (a * q ^ j) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hsq_q, hsq_a]
      unfold hsNorm
      calc Real.sqrt (hsNormSq (P (j + 1) - P j)) ≤ Real.sqrt ((a * q ^ j) ^ 2) :=
            Real.sqrt_le_sqrt h
        _ = a * q ^ j := Real.sqrt_sq (by positivity)
    -- Step 2: Cauchy in operator norm, hence convergent
    have hdist : ∀ j, dist (P j) (P (j + 1)) ≤ a * q ^ j := by
      intro j
      rw [dist_eq_norm, norm_sub_rev]
      exact le_trans (hA.2 (P (j + 1) - P j) 0).2.2.2.2 (hstep' j)
    have hcauchy : CauchySeq P := cauchySeq_of_le_geometric q a hq1 hdist
    obtain ⟨Q, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
    -- Step 3: the limit is a star projection
    have hidem : IsIdempotentElem Q := by
      have h1 : Tendsto (fun j => P j * P j) atTop (𝓝 (Q * Q)) := hlim.mul hlim
      have h2 : (fun j => P j * P j) = P := by
        funext j
        exact (S j).isIdempotentElem_starProjection
      rw [h2] at h1
      exact tendsto_nhds_unique h1 hlim
    have hidemL : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, IsIdempotentElem X →
        IsIdempotentElem (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ) := by
      intro X hX
      unfold IsIdempotentElem at hX ⊢
      rw [← ContinuousLinearMap.toLinearMap_mul, hX]
    have hsym : (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ).IsSymmetric := by
      intro x y
      have hx : Tendsto (fun j => P j x) atTop (𝓝 (Q x)) :=
        ((continuous_id.clm_apply continuous_const).tendsto Q).comp hlim
      have hy : Tendsto (fun j => P j y) atTop (𝓝 (Q y)) :=
        ((continuous_id.clm_apply continuous_const).tendsto Q).comp hlim
      have h1 : Tendsto (fun j => inner ℝ (P j x) y) atTop (𝓝 (inner ℝ (Q x) y)) :=
        hx.inner tendsto_const_nhds
      have h2 : Tendsto (fun j => inner ℝ x (P j y)) atTop (𝓝 (inner ℝ x (Q y))) :=
        tendsto_const_nhds.inner hy
      have h3 : (fun j => inner ℝ (P j x) y) = fun j => inner ℝ x (P j y) := by
        funext j
        exact Submodule.inner_starProjection_left_eq_right (S j) x y
      rw [h3] at h1
      exact tendsto_nhds_unique h1 h2
    have hsp : (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ).IsSymmetricProjection := ⟨hidemL Q hidem, hsym⟩
    obtain ⟨hinst, hQeq'⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hsp
    have hQeq : Q = (LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ)).starProjection := by
      apply ContinuousLinearMap.coe_injective
      exact hQeq'
    -- Step 4: rank via the trace
    let trL : (Amb n ℓ →L[ℝ] Amb n ℓ) →ₗ[ℝ] ℝ :=
      (LinearMap.trace ℝ (Amb n ℓ)).comp (ContinuousLinearMap.coeLM ℝ)
    have htrL : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, trL X = LinearMap.trace ℝ (Amb n ℓ) (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ) :=
      fun X => rfl
    have htr_idem : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, IsIdempotentElem X →
        trL X = (Module.finrank ℝ (LinearMap.range (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ)) : ℝ) := by
      intro X hX
      rw [htrL]
      exact (LinearMap.IsIdempotentElem.isProj_range _ (hidemL X hX)).trace
    have htrP : ∀ j, trL (P j) = (n : ℝ) := by
      intro j
      rw [htr_idem _ (S j).isIdempotentElem_starProjection]
      have : LinearMap.range (P j : Amb n ℓ →ₗ[ℝ] Amb n ℓ) = S j := Submodule.range_starProjection (S j)
      rw [this, hrank j]
    have htrc : Continuous trL := LinearMap.continuous_of_finiteDimensional trL
    have htrQ : trL Q = (n : ℝ) := by
      have h1 : Tendsto (fun j => trL (P j)) atTop (𝓝 (trL Q)) := (htrc.tendsto Q).comp hlim
      have h2 : (fun j => trL (P j)) = fun _ => (n : ℝ) := funext htrP
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    refine ⟨LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ), ?_, ?_⟩
    · have h := htr_idem Q hidem
      rw [htrQ] at h
      exact_mod_cast h.symm
    -- Step 5: tail bound
    intro k
    have hTQ : (LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ)).starProjection = Q := hQeq.symm
    rw [hTQ]
    have hq1' : 0 < 1 - q := sub_pos.mpr hq1
    have hsum : ∀ N, k ≤ N → hsNorm (P N - P k) ≤ a * (q ^ k - q ^ N) / (1 - q) := by
      intro N hkN
      induction N, hkN using Nat.le_induction with
      | base => simp [hsNorm, hsNormSq]
      | succ N hkN ih =>
        calc hsNorm (P (N + 1) - P k) = hsNorm ((P (N + 1) - P N) + (P N - P k)) := by
              rw [sub_add_sub_cancel]
          _ ≤ hsNorm (P (N + 1) - P N) + hsNorm (P N - P k) := (hA.2 _ _).2.2.2.1
          _ ≤ a * q ^ N + a * (q ^ k - q ^ N) / (1 - q) := add_le_add (hstep' N) ih
          _ = a * (q ^ k - q ^ (N + 1)) / (1 - q) := by
              rw [eq_div_iff hq1'.ne', add_mul, div_mul_cancel₀ _ hq1'.ne']
              ring
    have hgeom : ∀ N, a * (q ^ k - q ^ N) / (1 - q) ≤ a * q ^ k / (1 - q) := fun N =>
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg hq0 N)) ha0) hq1'.le
    have hcont : Continuous (fun X : Amb n ℓ →L[ℝ] Amb n ℓ => hsNorm X) :=
      Real.continuous_sqrt.comp hA.1
    have hlimk : Tendsto (fun N => hsNorm (P N - P k)) atTop (𝓝 (hsNorm (Q - P k))) :=
      (hcont.tendsto _).comp (hlim.sub_const (P k))
    have hbound : hsNorm (Q - P k) ≤ a * q ^ k / (1 - q) := by
      refine le_of_tendsto hlimk ?_
      exact Filter.eventually_atTop.2 ⟨k, fun N hN => le_trans (hsum N hN) (hgeom N)⟩
    have hnn : 0 ≤ hsNorm (Q - P k) := Real.sqrt_nonneg _
    calc hsNormSq (Q - (S k).starProjection) = hsNorm (Q - P k) ^ 2 := ((hA.2 _ 0).2.1).symm
      _ ≤ (a * q ^ k / (1 - q)) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = b * lam ^ k / (1 - q) ^ 2 := by
          rw [div_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hsq_q, hsq_a]
  -- Step 2 (iteration of 4.5; book (1)): E_*(ξ, η^j σ, S_j) ≤ (η^{2(1−n/p)})^j E_*(ξ, σ, S₀), S 0 = S₀.
  have hDI : TiltExcessDecayTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ S₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S₀ = n → ∃ S : ℕ → Submodule ℝ (Amb n ℓ), S 0 = S₀ ∧ ∀ j : ℕ, Module.finrank ℝ (S j) = n ∧ V.tiltExcessStar H p δ ξ (η ^ j * σ) (S j) ≤ (η ^ (2 * (1 - n / p))) ^ j * V.tiltExcessStar H p δ ξ σ S₀ := by
    intro hTED n ℓ hn p hp
    obtain ⟨η, δ₀, hη0, hη14, hδ₀0, hδ₀14, hdec⟩ := hTED n ℓ hn p hp
    refine ⟨η, δ₀, hη0, hη14, hδ₀0, hδ₀14, ?_⟩
    intro U hU V H δ ρ hδ0 hδ1 hAH ξ hξ σ hσ0 hσ1 S₀ hS₀
    set lam := η ^ (2 * (1 - (n : ℝ) / p)) with hlam
    have hlam0 : 0 ≤ lam := Real.rpow_nonneg hη0.le _
    have hη1 : η ≤ 1 := by linarith
    have hex : ∀ j : ℕ, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
        V.tiltExcessStar H p δ ξ (η ^ j * σ) T ≤ lam ^ j * V.tiltExcessStar H p δ ξ σ S₀ := by
      intro j
      induction j with
      | zero => exact ⟨S₀, hS₀, by simp⟩
      | succ j ih =>
        obtain ⟨T, hT, hTb⟩ := ih
        have hσj0 : 0 < η ^ j * σ := mul_pos (pow_pos hη0 j) hσ0
        have hσj1 : η ^ j * σ ≤ δ * ρ / 2 :=
          le_trans (mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1)) hσ1
        obtain ⟨T', hT', hT'b⟩ := hdec U hU V H δ ρ hδ0 hδ1 hAH (η ^ j * σ) hσj0 hσj1 ξ hξ T hT
        refine ⟨T', hT', ?_⟩
        have heq : η ^ (j + 1) * σ = η * (η ^ j * σ) := by ring
        rw [heq]
        calc V.tiltExcessStar H p δ ξ (η * (η ^ j * σ)) T'
            ≤ lam * V.tiltExcessStar H p δ ξ (η ^ j * σ) T := hT'b
          _ ≤ lam * (lam ^ j * V.tiltExcessStar H p δ ξ σ S₀) := mul_le_mul_of_nonneg_left hTb hlam0
          _ = lam ^ (j + 1) * V.tiltExcessStar H p δ ξ σ S₀ := by ring
    choose T hT hTb using hex
    classical
    refine ⟨fun j => if j = 0 then S₀ else T j, by simp, fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj
      simp [hS₀]
    · beta_reduce
      rw [ite_eq_right_iff.mpr (fun h => absurd h hj)]
      exact ⟨hT j, hTb j⟩
  -- Step 3 (consecutive planes; book (3)): a density lower bound c gives |p_{S_{j+1}} − p_{S_j}|² ≤ 4 c⁻¹ η⁻ⁿ λ^j A.
  have hCP : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ξ : Amb n ℓ) (σ η c lam A : ℝ) (S : ℕ → Submodule ℝ (Amb n ℓ)), 0 < σ → closedBall ξ σ ⊆ U → 0 < η → η ≤ 1 → 0 < c → 0 ≤ lam → lam ≤ 1 → 0 ≤ A → (∀ j : ℕ, ENNReal.ofReal (c * (η ^ (j + 1) * σ) ^ n) ≤ V.weight (closedBall ξ (η ^ (j + 1) * σ))) → (∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤ lam ^ j * A) → ∀ j : ℕ, hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) ≤ 4 * c⁻¹ * (η ^ n)⁻¹ * lam ^ j * A := by
    intro n ℓ U V hmeas ξ σ η c lam A S hσ0 hσU hη0 hη1 hc0 hlam0 hlam1 hA0 hlow hE j
    have hr₀pos : 0 < η ^ j * σ := mul_pos (pow_pos hη0 j) hσ0
    have hr₁pos : 0 < η ^ (j + 1) * σ := mul_pos (pow_pos hη0 (j + 1)) hσ0
    have hr₁r₀ : η ^ (j + 1) * σ = η * (η ^ j * σ) := by ring
    have hr₁le : η ^ (j + 1) * σ ≤ η ^ j * σ := by
      rw [hr₁r₀]; exact mul_le_of_le_one_left hr₀pos.le hη1
    have hr₀σ : η ^ j * σ ≤ σ := mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1)
    have hU₀ : closedBall ξ (η ^ j * σ) ⊆ U := (closedBall_subset_closedBall hr₀σ).trans hσU
    have hU₁ : closedBall ξ (η ^ (j + 1) * σ) ⊆ U :=
      (closedBall_subset_closedBall (hr₁le.trans hr₀σ)).trans hσU
    obtain ⟨hfin₁, -, -, hcmp, -⟩ := hTI n ℓ U V hmeas ξ (η ^ (j + 1) * σ) hU₁ (S (j + 1)) (S j)
    obtain ⟨-, -, hmono₀, -, -⟩ := hTI n ℓ U V hmeas ξ (η ^ j * σ) hU₀ (S j) (S j)
    have hI₁ : ∫ x in closedBall ξ (η ^ (j + 1) * σ),
        hsNormSq (V.tangentProj x - (S (j + 1)).starProjection) ∂V.weight
          ≤ (η ^ (j + 1) * σ) ^ n * (lam ^ (j + 1) * A) := by
      have h := hE (j + 1)
      unfold RectifiableVarifold.tiltExcess at h
      rwa [inv_mul_le_iff₀ (pow_pos hr₁pos n)] at h
    have hI₀ : ∫ x in closedBall ξ (η ^ (j + 1) * σ),
        hsNormSq (V.tangentProj x - (S j).starProjection) ∂V.weight
          ≤ (η ^ j * σ) ^ n * (lam ^ j * A) := by
      have h := hE j
      unfold RectifiableVarifold.tiltExcess at h
      rw [inv_mul_le_iff₀ (pow_pos hr₀pos n)] at h
      exact le_trans (hmono₀ _ hr₁le) h
    have hmass : c * (η ^ (j + 1) * σ) ^ n ≤ (V.weight (closedBall ξ (η ^ (j + 1) * σ))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin₁.ne).mp (hlow j)
    have hmpos : 0 < (V.weight (closedBall ξ (η ^ (j + 1) * σ))).toReal :=
      lt_of_lt_of_le (mul_pos hc0 (pow_pos hr₁pos n)) hmass
    have hr₀n : (η ^ j * σ) ^ n = (η ^ n)⁻¹ * (η ^ (j + 1) * σ) ^ n := by
      rw [hr₁r₀, mul_pow η (η ^ j * σ) n, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hη0.ne'),
        one_mul]
    have hηn : 1 ≤ (η ^ n)⁻¹ := (one_le_inv₀ (pow_pos hη0 n)).mpr (pow_le_one₀ hη0.le hη1)
    have hlamj : lam ^ (j + 1) ≤ lam ^ j := pow_le_pow_of_le_one hlam0 hlam1 (Nat.le_succ j)
    have hK : 0 ≤ (η ^ (j + 1) * σ) ^ n * (lam ^ j * A) :=
      mul_nonneg (pow_nonneg hr₁pos.le n) (mul_nonneg (pow_nonneg hlam0 j) hA0)
    have e1 : (η ^ (j + 1) * σ) ^ n * (lam ^ (j + 1) * A) ≤ (η ^ (j + 1) * σ) ^ n * (lam ^ j * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlamj hA0) (pow_nonneg hr₁pos.le n)
    have e2 : (η ^ (j + 1) * σ) ^ n * (lam ^ j * A) ≤
        (η ^ n)⁻¹ * ((η ^ (j + 1) * σ) ^ n * (lam ^ j * A)) :=
      le_mul_of_one_le_left hK hηn
    rw [hr₀n] at hI₀
    have hX : hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) *
        (V.weight (closedBall ξ (η ^ (j + 1) * σ))).toReal ≤
          4 * (η ^ n)⁻¹ * lam ^ j * A * (η ^ (j + 1) * σ) ^ n := by
      linarith only [hcmp, hI₁, hI₀, e1, e2]
    have hnum : 0 ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * (η ^ (j + 1) * σ) ^ n :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (pow_nonneg hη0.le n))) (pow_nonneg hlam0 j)) hA0) (pow_nonneg hr₁pos.le n)
    calc hsNormSq ((S (j + 1)).starProjection - (S j).starProjection)
        ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * (η ^ (j + 1) * σ) ^ n /
            (V.weight (closedBall ξ (η ^ (j + 1) * σ))).toReal := (le_div_iff₀ hmpos).mpr hX
      _ ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * (η ^ (j + 1) * σ) ^ n / (c * (η ^ (j + 1) * σ) ^ n) :=
          div_le_div_of_nonneg_left hnum (mul_pos hc0 (pow_pos hr₁pos n)) hmass
      _ = 4 * c⁻¹ * (η ^ n)⁻¹ * lam ^ j * A := by
          rw [mul_div_mul_right _ _ (pow_pos hr₁pos n).ne']
          ring
  -- Step 5 (decay at all scales; book (7)): a density upper bound D gives E(ξ, s, T) ≤ (2η⁻ⁿ + 2DB)(η^β)⁻¹ (s/σ)^β A.
  have hAS : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ξ : Amb n ℓ) (σ η β D B A : ℝ) (S : ℕ → Submodule ℝ (Amb n ℓ)) (T : Submodule ℝ (Amb n ℓ)), 0 < σ → closedBall ξ σ ⊆ U → 0 < η → η < 1 → 0 ≤ β → 0 ≤ D → 0 ≤ B → 0 ≤ A → (∀ s : ℝ, 0 < s → s ≤ σ → V.weight (closedBall ξ s) ≤ ENNReal.ofReal (D * s ^ n)) → (∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤ (η ^ β) ^ j * A) → (∀ j : ℕ, hsNormSq (T.starProjection - (S j).starProjection) ≤ B * (η ^ β) ^ j * A) → ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * (η ^ β)⁻¹ * (s / σ) ^ β * A := by
    intro n ℓ U V hmeas ξ σ η β D B A S T hσ0 hσU hη0 hη1 hβ0 hD0 hB0 hA0 hup hE hT s hs0 hsσ
    have hA := hHS (n + ℓ) (n + ℓ)
    set lam := η ^ β with hlam
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hη0 β
    -- Step 1: the dyadic scale containing s
    have hex : ∃ k : ℕ, η ^ k * σ < s := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hs0 hσ0) hη1
      exact ⟨k, by rwa [lt_div_iff₀ hσ0] at hk⟩
    classical
    have hk : η ^ (Nat.find hex) * σ < s := Nat.find_spec hex
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, pow_zero, one_mul] at hk
      exact (not_lt.mpr hsσ) hk
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hjup : s ≤ η ^ j * σ := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      push Not at this
      exact this
    have hjlow : η ^ (j + 1) * σ < s := by rw [← hj]; exact hk
    set r := η ^ j * σ with hr
    have hrpos : 0 < r := mul_pos (pow_pos hη0 j) hσ0
    have hrσ : r ≤ σ := mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1.le)
    have hUr : closedBall ξ r ⊆ U := (closedBall_subset_closedBall hrσ).trans hσU
    have hUs : closedBall ξ s ⊆ U := (closedBall_subset_closedBall hsσ).trans hσU
    -- Step 2: integral estimate on B_s(ξ)
    obtain ⟨hfins, -, -, -, hchg⟩ := hTI n ℓ U V hmeas ξ s hUs T (S j)
    obtain ⟨-, -, hmonor, -, -⟩ := hTI n ℓ U V hmeas ξ r hUr (S j) (S j)
    have hIr : ∫ x in closedBall ξ r, hsNormSq (V.tangentProj x - (S j).starProjection) ∂V.weight
        ≤ r ^ n * (lam ^ j * A) := by
      have h := hE j
      unfold RectifiableVarifold.tiltExcess at h
      rwa [inv_mul_le_iff₀ (pow_pos hrpos n)] at h
    have hmass : (V.weight (closedBall ξ s)).toReal ≤ D * s ^ n :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hD0 (pow_nonneg hs0.le n)) (hup s hs0 hsσ)
    have hIs : ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤
        2 * (r ^ n * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := by
      have h1 := le_trans (hmonor s hjup) hIr
      have h2 : (V.weight (closedBall ξ s)).toReal * hsNormSq (T.starProjection - (S j).starProjection)
          ≤ (D * s ^ n) * (B * lam ^ j * A) :=
        mul_le_mul hmass (hT j) (hA.2 _ 0).1 (mul_nonneg hD0 (pow_nonneg hs0.le n))
      linarith only [hchg, h1, h2]
    -- Step 3: compare the radii
    have hrs : r ≤ s / η := by
      rw [le_div_iff₀ hη0]
      have : η ^ (j + 1) * σ = r * η := by rw [hr]; ring
      linarith only [this, hjlow]
    have hrn : r ^ n ≤ (η ^ n)⁻¹ * s ^ n := by
      calc r ^ n ≤ (s / η) ^ n := pow_le_pow_left₀ hrpos.le hrs n
        _ = (η ^ n)⁻¹ * s ^ n := by rw [div_pow]; ring
    have hsn : 0 < s ^ n := pow_pos hs0 n
    have hE1 : V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A := by
      unfold RectifiableVarifold.tiltExcess
      rw [inv_mul_le_iff₀ hsn]
      have hlj : 0 ≤ lam ^ j * A := mul_nonneg (pow_nonneg hlam0.le j) hA0
      calc ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
          ≤ 2 * (r ^ n * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := hIs
        _ ≤ 2 * (((η ^ n)⁻¹ * s ^ n) * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := by
            have := mul_le_mul_of_nonneg_right hrn hlj
            linarith only [this]
        _ = s ^ n * ((2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A) := by ring
    -- Step 4: from the dyadic power to (s/σ)^β
    have hpow : lam ^ j ≤ lam⁻¹ * (s / σ) ^ β := by
      have h1 : lam ^ (j + 1) = (η ^ (j + 1)) ^ β := by
        rw [hlam, Real.rpow_pow_comm hη0.le]
      have h2 : η ^ (j + 1) ≤ s / σ := by
        rw [le_div_iff₀ hσ0]; exact hjlow.le
      have h3 : (η ^ (j + 1)) ^ β ≤ (s / σ) ^ β :=
        Real.rpow_le_rpow (pow_nonneg hη0.le _) h2 hβ0
      rw [le_inv_mul_iff₀ hlam0]
      calc lam * lam ^ j = lam ^ (j + 1) := by ring
        _ ≤ (s / σ) ^ β := h1 ▸ h3
    have hcoef : 0 ≤ 2 * (η ^ n)⁻¹ + 2 * D * B :=
      add_nonneg (mul_nonneg zero_le_two (inv_nonneg.mpr (pow_nonneg hη0.le n)))
        (mul_nonneg (mul_nonneg zero_le_two hD0) hB0)
    calc V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A := hE1
      _ ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * (lam⁻¹ * (s / σ) ^ β) * A := by
          apply mul_le_mul_of_nonneg_right _ hA0
          exact mul_le_mul_of_nonneg_left hpow hcoef
      _ = (2 * (η ^ n)⁻¹ + 2 * D * B) * lam⁻¹ * (s / σ) ^ β * A := by ring
  -- Assembly (Simon 5.2, steps (1)–(7)): δ₁ = min δ₀ δP and C = max C_II C_III, where
  -- c = ω/2, D = 2ω, b = 4c⁻¹η⁻ⁿ, C_II = b/(1 − √λ)², C_III = (2η⁻ⁿ + 2 D C_II) λ⁻¹, λ = η^{2(1−n/p)}.
  intro hTED n ℓ hn p hp
  obtain ⟨η, δ₀, hη0, hη14, hδ₀0, hδ₀14, hiter⟩ := hDI hTED n ℓ hn p hp
  obtain ⟨δP, CP, hδP0, hδP8, hCP0, hCPδP, hdens⟩ := Submission.allard52_density_bounds n hn p hp
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hα : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hβ0 : 0 < 2 * (1 - (n : ℝ) / p) := mul_pos two_pos hα
  have hη1 : η < 1 := lt_of_le_of_lt hη14 (by norm_num)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = η ^ (2 * (1 - (n : ℝ) / p)) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact Real.rpow_pos_of_pos hη0 _
  have hlam1 : lam < 1 := by rw [hlam]; exact Real.rpow_lt_one hη0.le hη1 hβ0
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 4 * (unitBallVolume n / 2)⁻¹ * (η ^ n)⁻¹ := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (half_pos hω).le))
      (inv_nonneg.mpr (pow_nonneg hη0.le n))
  obtain ⟨CII, hCII⟩ : ∃ C : ℝ, C = b / (1 - Real.sqrt lam) ^ 2 := ⟨_, rfl⟩
  have hCII0 : 0 ≤ CII := by rw [hCII]; exact div_nonneg hb0 (sq_nonneg _)
  obtain ⟨CIII, hCIII⟩ : ∃ C : ℝ,
      C = (2 * (η ^ n)⁻¹ + 2 * (2 * unitBallVolume n) * CII) * lam⁻¹ := ⟨_, rfl⟩
  refine ⟨min δ₀ δP, max CII CIII, lt_min hδ₀0 hδP0, le_max_of_le_left hCII0, ?_⟩
  intro U hU V H δ ρ hδ0 hδ1 hAH ξ hξ σ hσ0 hσ1 S₀ hS₀
  have hδδ₀ : δ ≤ δ₀ := le_trans hδ1 (min_le_left _ _)
  have hδδP : δ ≤ δP := le_trans hδ1 (min_le_right _ _)
  have hρ0 : 0 < ρ := hAH.1
  have hballU : closedBall (0 : Amb n ℓ) ρ ⊆ U := hAH.2.2.2.2.1
  have hξsupp : ξ ∈ V.support := hξ.1
  have hξnorm : ‖ξ‖ ≤ δ * ρ := by
    have h := hξ.2
    rwa [mem_closedBall, dist_zero_right] at h
  have hδρ8 : δ * ρ ≤ ρ / 8 := by
    have h := mul_le_mul_of_nonneg_right (le_trans hδδP hδP8) hρ0.le
    linarith only [h]
  have hδρ : 0 < δ * ρ := mul_pos hδ0 hρ0
  have hξ3 : ‖ξ‖ ≤ 3 * δ * ρ := by
    rw [mul_assoc]
    linarith only [hξnorm, hδρ]
  have hσρ : σ ≤ ρ / 2 := by linarith only [hσ1, hδρ8, hρ0]
  have hσU : closedBall ξ σ ⊆ U := by
    intro x hx
    apply hballU
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hx
    have h1 : ‖x‖ ≤ ‖x - ξ‖ + ‖ξ‖ := by
      have h := norm_add_le (x - ξ) ξ
      rwa [sub_add_cancel] at h
    linarith only [h1, hx, hξnorm, hσ1, hδρ8, hρ0]
  have hmeas : AEStronglyMeasurable V.tangentProj V.weight :=
    (Submission.allard52_tangent_ae n ℓ hn U hU V).1
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = V.tiltExcessStar H p δ ξ σ S₀ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    simp only [RectifiableVarifold.tiltExcessStar]
    exact le_max_of_le_right (mul_nonneg (inv_nonneg.mpr hδ0.le) (sq_nonneg _))
  -- Step 2: the iterated planes S_j
  obtain ⟨S, hS0, hS⟩ := hiter U hU V H δ ρ hδ0 hδδ₀ hAH ξ hξ σ hσ0 hσ1 S₀ hS₀
  have hE : ∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤ lam ^ j * A := by
    intro j
    rw [hlam, hA]
    refine le_trans ?_ (hS j).2
    simp only [RectifiableVarifold.tiltExcessStar]
    exact le_max_left _ _
  have hCPδ : CP * δ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hδδP hCP0.le) hCPδP
  -- density lower bound at the radii η^(j+1) σ
  have hlow : ∀ j : ℕ, ENNReal.ofReal (unitBallVolume n / 2 * (η ^ (j + 1) * σ) ^ n) ≤
      V.weight (closedBall ξ (η ^ (j + 1) * σ)) := by
    intro j
    have hs0 : 0 < η ^ (j + 1) * σ := mul_pos (pow_pos hη0 _) hσ0
    have hsρ : η ^ (j + 1) * σ ≤ ρ / 2 :=
      le_trans (mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1.le)) hσρ
    have h := ((hdens ℓ U hU V H δ ρ hδ0 hδδP hAH ξ hξ3 (η ^ (j + 1) * σ) hs0 hsρ).2 hξsupp).1
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
    have hpos : 0 ≤ unitBallVolume n * (η ^ (j + 1) * σ) ^ n :=
      mul_nonneg hω.le (pow_nonneg hs0.le n)
    have h2 : (1 : ℝ) / 2 ≤ 1 - CP * δ := by linarith only [hCPδ]
    calc unitBallVolume n / 2 * (η ^ (j + 1) * σ) ^ n
        = 1 / 2 * (unitBallVolume n * (η ^ (j + 1) * σ) ^ n) := by ring
      _ ≤ (1 - CP * δ) * (unitBallVolume n * (η ^ (j + 1) * σ) ^ n) :=
        mul_le_mul_of_nonneg_right h2 hpos
  -- Step 3: consecutive planes
  have hcons := hCP n ℓ U V hmeas ξ σ η (unitBallVolume n / 2) lam A S hσ0 hσU hη0 hη1.le
    (half_pos hω) hlam0.le hlam1.le hA0 hlow hE
  -- Step 4: the limit plane T
  obtain ⟨T, hT, hTlim⟩ := hPL n ℓ S (b * A) lam (mul_nonneg hb0 hA0) hlam0.le hlam1
    (fun j => (hS j).1) (fun j => (hcons j).trans_eq (by rw [hb]; ring))
  have hTk : ∀ k : ℕ, hsNormSq (T.starProjection - (S k).starProjection) ≤ CII * lam ^ k * A :=
    fun k => (hTlim k).trans_eq (by rw [hCII]; ring)
  refine ⟨T, hT, ?_, ?_⟩
  · have h0 := hTk 0
    rw [hS0, pow_zero, mul_one] at h0
    rw [← hA]
    exact le_trans h0 (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0)
  · -- Step 5: decay at all scales
    have hup : ∀ s : ℝ, 0 < s → s ≤ σ →
        V.weight (closedBall ξ s) ≤ ENNReal.ofReal (2 * unitBallVolume n * s ^ n) := by
      intro s hs0 hsσ
      have h := (hdens ℓ U hU V H δ ρ hδ0 hδδP hAH ξ hξ3 s hs0 (le_trans hsσ hσρ)).1
      refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
      have hpos : 0 ≤ unitBallVolume n * s ^ n := mul_nonneg hω.le (pow_nonneg hs0.le n)
      have h2 : 1 + CP * δ ≤ 2 := by linarith only [hCPδ]
      calc (1 + CP * δ) * (unitBallVolume n * s ^ n) ≤ 2 * (unitBallVolume n * s ^ n) :=
            mul_le_mul_of_nonneg_right h2 hpos
        _ = 2 * unitBallVolume n * s ^ n := by ring
    have hE' : ∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤
        (η ^ (2 * (1 - (n : ℝ) / p))) ^ j * A := by
      rw [← hlam]; exact hE
    have hTk' : ∀ j : ℕ, hsNormSq (T.starProjection - (S j).starProjection) ≤
        CII * (η ^ (2 * (1 - (n : ℝ) / p))) ^ j * A := by
      rw [← hlam]; exact hTk
    have hall := hAS n ℓ U V hmeas ξ σ η (2 * (1 - (n : ℝ) / p)) (2 * unitBallVolume n) CII A S T
      hσ0 hσU hη0 hη1 hβ0.le (mul_pos two_pos hω).le hCII0 hA0 hup hE' hTk'
    intro s hs0 hsσ
    rw [← hA]
    refine (hall s hs0 hsσ).trans ?_
    rw [← hlam, ← hCIII]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (div_nonneg hs0.le hσ0.le) _)) hA0
/-- **Simon Ch. 5, proof of Theorem 5.2 (p. 123): comparing `μ_V` with the Lipschitz graph.**
The book passes from (7) and (9) to (10)–(11) by integrating over the graph of (9) instead of
over `spt V`; this inequality is what that passage uses.  Take `δ₂ = δ_P(n, p)` from
`allard52_density_bounds` (independent of `ℓ`).  If 2.3 holds with `δ ≤ δ₂` and
`spt V ∩ B_R(0) = q(graph f) ∩ B_R(0)` for a `1`-Lipschitz `f` with `f(0) = 0`, `R ≤ δρ`, then
`∫_A Φ(F(x), p_{q(graph Df(x))}) dLⁿ ≤ ∫_{F(A)} Φ(w, p_{T_wV}) dμ_V` for `A ⊆ B̆ⁿ_{R/2}(0)`, where
`F(x) = q(x, f(x))`.  Extending `f` to a Lipschitz `G` on `ℝⁿ`, the area formula (SimonGMT)
writes `μ_V` near the origin as the push-forward of `θ(F) J_F Lⁿ`; the lower density bound shows
that a.e. point of the graph lies in the carrier; blowing up at Lebesgue points of `θ(F) J_F`
identifies `T_{F(x)}V = q(graph Df(x))`; finally `J_F ≥ 1` and `θ ≥ 1` give
`Lⁿ⌞A ≤ J_F Lⁿ⌞A = F^*(Hⁿ⌞F(A))` and `Hⁿ⌞F(A) ≤ μ_V⌞F(A)`. -/
theorem allard52_graph_comparison : ∀ (n : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₂ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), 0 < R → R ≤ δ * ρ → f 0 = 0 → LipschitzOnWith 1 f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → ∀ Φ : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) → ℝ≥0∞, Measurable (Function.uncurry Φ) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ ball 0 (R / 2) → ∫⁻ x in A, Φ (q (graphPoint x (f x))) ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection ≤ ∫⁻ y in q '' graphOver f A, Φ y (V.tangentProj y) ∂V.weight := by
  intro n hn p hp
  obtain ⟨δP, CP, hδP0, hδP8, hCP0, hCPδP, hDB⟩ := Submission.allard52_density_bounds n hn p hp
  refine ⟨δP, hδP0, ?_⟩
  intro ℓ U hU V H δ ρ hδ0 hδle hAH q f R hR0 hRle hf0 hLip hgraph Φ hΦ A hAm hAsub
  have hAH' := hAH
  obtain ⟨hρ0, -, hθ1, -, hBρU, hmass, -⟩ := hAH'
  have hδ8 : δ ≤ 1 / 8 := hδle.trans hδP8
  have hRρ : R ≤ ρ / 8 := by linarith only [hRle, mul_le_mul_of_nonneg_right hδ8 hρ0.le]
  have hCPδ : CP * δ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hδle hCP0.le) hCPδP
  have hfr : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  -- Step 1: the linear algebra of `graphPoint`.
  have gp_norm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
    simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_add : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' := by
    intro x x' y y'
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_smul : ∀ (c : ℝ) (x : Rn n) (y : Rn ℓ), graphPoint (c • x) (c • y) = c • graphPoint x y := by
    intro c x y
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x - x') (y - y') = graphPoint x y - graphPoint x' y' := by
    intro x x' y y'
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_zero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  obtain ⟨Lc, hLc⟩ : ∃ Lc : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ, ∀ z, Lc z = graphPoint z.1 z.2 :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun z => graphPoint z.1 z.2
        map_add' := fun z z' => gp_add z.1 z'.1 z.2 z'.2
        map_smul' := fun c z => gp_smul c z.1 z.2 }, fun z => rfl⟩
  -- Step 2: a global Lipschitz extension `G` of `f` and the graph map `F`.
  obtain ⟨G, hGLip, hGeq⟩ := hLip.extend_finite_dimension
  obtain ⟨F, hFdef⟩ : ∃ F : Rn n → Amb n ℓ, F = fun x => q (graphPoint x (G x)) := ⟨_, rfl⟩
  have hF_apply : ∀ x, F x = q (graphPoint x (G x)) := fun x => by rw [hFdef]
  have hG0 : G 0 = 0 := by rw [← hGeq (mem_closedBall_self hR0.le), hf0]
  have hF0 : F 0 = 0 := by rw [hF_apply, hG0, gp_zero, map_zero]
  have hF_sub : ∀ x x', F x - F x' = q (graphPoint (x - x') (G x - G x')) := by
    intro x x'
    rw [hF_apply, hF_apply, ← map_sub, gp_sub]
  have hF_dist_sq : ∀ x x', ‖F x - F x'‖ ^ 2 = ‖x - x'‖ ^ 2 + ‖G x - G x'‖ ^ 2 := by
    intro x x'
    rw [hF_sub, LinearIsometryEquiv.norm_map, gp_norm]
  have hF_ge : ∀ x x', ‖x - x'‖ ≤ ‖F x - F x'‖ := by
    intro x x'
    have h := hF_dist_sq x x'
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [h]; exact le_add_of_nonneg_right (sq_nonneg _))
  have hG_le : ∀ x x', ‖G x - G x'‖ ≤ (lipschitzExtensionConstant (Rn ℓ) * 1 : ℝ≥0) * ‖x - x'‖ := by
    intro x x'
    simpa [dist_eq_norm] using hGLip.dist_le_mul x x'
  have hF_le : ∀ x x', ‖F x - F x'‖ ≤ ((1 + lipschitzExtensionConstant (Rn ℓ) * 1 : ℝ≥0) : ℝ) * ‖x - x'‖ := by
    intro x x'
    have h := hF_dist_sq x x'
    have h2 := hG_le x x'
    have h3 : ‖F x - F x'‖ ≤ ‖x - x'‖ + ‖G x - G x'‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp ?_
      rw [h, add_sq]
      linarith only [mul_nonneg (mul_nonneg zero_le_two (norm_nonneg (x - x')))
        (norm_nonneg (G x - G x'))]
    push_cast at h2 ⊢
    linarith only [h2, h3]
  have hFLip : LipschitzWith (1 + lipschitzExtensionConstant (Rn ℓ) * 1) F :=
    LipschitzWith.of_dist_le_mul fun x x' => by
      simpa [dist_eq_norm] using hF_le x x'
  have hFcont : Continuous F := hFLip.continuous
  have hFmeas : Measurable F := hFcont.measurable
  have hFinj : Function.Injective F := by
    intro x x' h
    have := hF_ge x x'
    rw [h, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hF_on : ∀ x ∈ closedBall (0 : Rn n) R, F x = q (graphPoint x (f x)) := by
    intro x hx
    rw [hF_apply, ← hGeq hx]
  have hF_norm_sq_le : ∀ x ∈ closedBall (0 : Rn n) R, ‖F x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    intro x hx
    have h := hF_dist_sq x 0
    rw [hF0, sub_zero, sub_zero, hG0, sub_zero, ← hGeq hx] at h
    have h2 : ‖f x‖ ≤ ‖x‖ := by
      have := hLip.dist_le_mul x hx 0 (mem_closedBall_self hR0.le)
      simpa [dist_eq_norm, hf0] using this
    rw [h, two_mul]
    exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  have hFA : q '' graphOver f A = F '' A := by
    rw [graphOver, image_image]
    refine image_congr fun x hx => ?_
    refine (hF_on x ?_).symm
    have := hAsub hx
    rw [mem_ball, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]; linarith only [this, hR0]
  have hFimg_meas : ∀ S : Set (Rn n), MeasurableSet S → MeasurableSet (F '' S) := fun S hS =>
    hS.image_of_continuousOn_injOn hFcont.continuousOn hFinj.injOn
  -- points of `spt V` near the origin lie on the graph
  have hsupp_range : ∀ w ∈ V.support, ‖w‖ ≤ R → w ∈ range F := by
    intro w hw hwR
    have hw' : w ∈ V.support ∩ closedBall 0 R := ⟨hw, by rw [mem_closedBall, dist_zero_right]; exact hwR⟩
    rw [hgraph] at hw'
    obtain ⟨⟨z, ⟨x, hx, rfl⟩, rfl⟩, -⟩ := hw'
    exact ⟨x, hF_on x hx⟩
  have hF_supp : ∀ x ∈ closedBall (0 : Rn n) R, ‖F x‖ ≤ R → F x ∈ V.support := by
    intro x hx hFx
    have : F x ∈ q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R :=
      ⟨⟨graphPoint x (f x), ⟨x, hx, rfl⟩, (hF_on x hx).symm⟩, by
        rw [mem_closedBall, dist_zero_right]; exact hFx⟩
    rw [← hgraph] at this
    exact this.1
  -- Step 3: a measurable piece `M₂` of the carrier on which `θ` agrees with a measurable `θ'`.
  obtain ⟨M₁, hM₁sub, hM₁meas, hM₁ae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
  obtain ⟨θ', hθ'meas, hθθ'⟩ : ∃ θ' : Amb n ℓ → ℝ, Measurable θ' ∧
      V.mult =ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier] θ' :=
    ⟨V.aemeasurable_mult.mk V.mult, V.aemeasurable_mult.measurable_mk, V.aemeasurable_mult.ae_eq_mk⟩
  obtain ⟨M₂, hM₂def⟩ : ∃ M₂ : Set (Amb n ℓ), M₂ = M₁ \ toMeasurable
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) {x | V.mult x ≠ θ' x} := ⟨_, rfl⟩
  have hM₂meas : MeasurableSet M₂ := by
    rw [hM₂def]; exact hM₁meas.diff (measurableSet_toMeasurable _ _)
  have hM₂sub : M₂ ⊆ V.carrier := by
    rw [hM₂def]; exact sdiff_subset.trans hM₁sub
  have hM₂θ : ∀ x ∈ M₂, V.mult x = θ' x := by
    intro x hx
    rw [hM₂def] at hx
    by_contra h
    exact hx.2 (subset_toMeasurable _ _ h)
  have hM₂pos : ∀ x ∈ M₂, 0 < θ' x := fun x hx => hM₂θ x hx ▸ V.mult_pos x (hM₂sub hx)
  have hM₂null : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ M₂) = 0 := by
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ M₁) = 0 := (ae_eq_set.mp hM₁ae).2
    have h2 : (μHE[n] : Measure (Amb n ℓ)) (toMeasurable ((μHE[n] : Measure (Amb n ℓ)).restrict
        V.carrier) {x | V.mult x ≠ θ' x} ∩ V.carrier) = 0 := by
      rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]
      exact ae_iff.mp hθθ'
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
    rw [hM₂def] at hx
    by_cases hx1 : x ∈ M₁
    · exact Or.inr ⟨not_not.mp fun h => hx.2 ⟨hx1, h⟩, hx.1⟩
    · exact Or.inl ⟨hx.1, hx1⟩
  have hrestr : (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier =
      (μHE[n] : Measure (Amb n ℓ)).restrict M₂ := by
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨hM₂null, ?_⟩)
    rw [sdiff_eq_empty.mpr hM₂sub, measure_empty]
  -- the weight in terms of `M₂` and `θ'`
  have hWGT : ∀ B, MeasurableSet B →
      V.weight B = ∫⁻ w in B ∩ M₂, ENNReal.ofReal (θ' w) ∂μHE[n] := by
    intro B hB
    rw [RectifiableVarifold.weight, withDensity_apply _ hB, hrestr, Measure.restrict_restrict hB]
    exact setLIntegral_congr_fun (hB.inter hM₂meas) (fun w hw => by rw [hM₂θ w hw.2])
  -- `μ_V`-null measurable sets meet `M₂` in `Hⁿ`-null sets
  have hLnull : ∀ S, MeasurableSet S → V.weight S = 0 →
      (μHE[n] : Measure (Amb n ℓ)) (S ∩ M₂) = 0 := by
    intro S hS h0
    rw [hWGT S hS, lintegral_eq_zero_iff hθ'meas.ennreal_ofReal] at h0
    have hfalse : ∀ᵐ w ∂(μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ M₂), False := by
      filter_upwards [h0, ae_restrict_mem (hS.inter hM₂meas)] with w hw hwS
      have := hM₂pos w hwS.2
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hw
      exact absurd hw (not_le.mpr this)
    rw [← Measure.restrict_eq_zero, ← ae_eq_bot]
    exact Filter.eventually_false_iff_eq_bot.mp hfalse
  -- the carrier outside `spt V` is `Hⁿ`-null
  have hsuppc_meas : MeasurableSet (V.weight.supportᶜ) :=
    (Measure.isClosed_support (μ := V.weight)).isOpen_compl.measurableSet
  have hC1 : (μHE[n] : Measure (Amb n ℓ)) (V.weight.supportᶜ ∩ M₂) = 0 :=
    hLnull _ hsuppc_meas Measure.measure_compl_support
  -- the measurable density on the parameter domain
  obtain ⟨g₀, hg₀def⟩ : ∃ g₀ : Rn n → ℝ≥0∞, g₀ = fun x =>
      ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
        M₂.indicator (fun w => ENNReal.ofReal (θ' w)) (F x) := ⟨_, rfl⟩
  have hg₀meas : Measurable g₀ := by
    rw [hg₀def]
    exact (Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F).ennreal_ofReal.mul
      ((Measurable.indicator hθ'meas.ennreal_ofReal hM₂meas).comp hFmeas)
  have hrange_meas : MeasurableSet (range F) := by
    rw [← image_univ]; exact hFimg_meas _ MeasurableSet.univ
  -- the area formula along the graph
  have hArea : ∀ (S : Set (Rn n)), MeasurableSet S → ∀ g : Amb n ℓ → ℝ≥0∞,
      ∫⁻ y in F '' S, g y ∂μHE[n] =
        ∫⁻ x in S, ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) * g (F x) := by
    intro S hS g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hFLip hS
      hFinj.injOn g
    rwa [hfr] at h
  -- Step 4: near the origin, `μ_V` is the pushforward of `g₀ Lⁿ` under `F`.
  have hREP : ∀ B, MeasurableSet B → B ⊆ ball 0 R → V.weight B = ∫⁻ x in F ⁻¹' B, g₀ x := by
    intro B hB hBR
    rw [hWGT B hB, ← lintegral_inter_add_sdiff _ (B ∩ M₂) hrange_meas]
    have hnull : (μHE[n] : Measure (Amb n ℓ)) ((B ∩ M₂) \ range F) = 0 := by
      refine measure_mono_null ?_ hC1
      intro w hw
      refine ⟨fun hws => hw.2 ?_, hw.1.2⟩
      have hwB := hBR hw.1.1
      rw [mem_ball, dist_zero_right] at hwB
      exact hsupp_range w ⟨V.carrier_subset (hM₂sub hw.1.2), hws⟩ hwB.le
    rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    have hset : B ∩ M₂ ∩ range F = M₂ ∩ F '' (F ⁻¹' B) := by
      rw [image_preimage_eq_inter_range, inter_assoc, inter_left_comm]
    rw [hset, ← setLIntegral_indicator hM₂meas, hArea _ (hFmeas hB), hg₀def]

  -- Step 5: the derivative of `F` and the graph planes.
  obtain ⟨DF, hDF, hFderiv⟩ : ∃ DF : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ),
      (∀ B v, DF B v = q (graphPoint v (B v))) ∧
      ∀ x, DifferentiableAt ℝ G x → HasFDerivAt F (DF (fderiv ℝ G x)) x := by
    refine ⟨fun B => (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      (Lc.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod B)), fun B v => by simp [hLc], ?_⟩
    intro x hx
    have h1 : HasFDerivAt (fun x => (x, G x))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ G x)) x :=
      (hasFDerivAt_id x).prodMk hx.hasFDerivAt
    have h2 := (Lc.hasFDerivAt).comp x h1
    have h3 := (q.toContinuousLinearEquiv.hasFDerivAt).comp x h2
    convert h3 using 1
    ext x'
    simp [hF_apply, hLc]
  have hDF_norm : ∀ B v, ‖v‖ ≤ ‖DF B v‖ := by
    intro B v
    rw [hDF, LinearIsometryEquiv.norm_map]
    have := gp_norm v (B v)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [this]; exact le_add_of_nonneg_right (sq_nonneg _))
  have hDF_inj : ∀ B, Function.Injective (DF B) := by
    intro B v v' h
    have := hDF_norm B (v - v')
    rw [map_sub, h, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hDF_range : ∀ B, LinearMap.range (DF B : Rn n →ₗ[ℝ] Amb n ℓ) =
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map
        q.toLinearEquiv.toLinearMap := by
    intro B
    have hspan : Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v)) =
        LinearMap.range ((Lc.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod B) :
          Rn n →L[ℝ] Amb n ℓ) : Rn n →ₗ[ℝ] Amb n ℓ) := by
      rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range]
      congr 1
      ext w
      simp [hLc]
    rw [hspan, ← LinearMap.range_comp]
    congr 1
    ext v
    simp [hDF, hLc]
  have hDF_finrank : ∀ B, Module.finrank ℝ (LinearMap.range (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) = n := by
    intro B
    rw [LinearMap.finrank_range_of_inj (hDF_inj B), hfr]
  have hvol_ball_pos : 0 < (volume : Measure (Rn n)) (closedBall 0 1) :=
    measure_closedBall_pos _ _ one_pos
  have hvol_ball_fin : (volume : Measure (Rn n)) (closedBall 0 1) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  have hball : (μHE[n] : Measure (Rn n)) (closedBall 0 1) = (volume : Measure (Rn n)) (closedBall 0 1) := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
    rw [hfr] at h
    rw [h]
  have hDF_normDet : ∀ B, 1 ≤ LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro B
    have himg := LinearMap.euclideanHausdorffMeasure_image (DF B : Rn n →ₗ[ℝ] Amb n ℓ)
      (closedBall (0 : Rn n) 1)
    rw [hfr, hball] at himg
    have hgLip : LipschitzOnWith 1 (Function.invFun (DF B)) (range (DF B)) := by
      refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
      obtain ⟨v, rfl⟩ := hw
      obtain ⟨v', rfl⟩ := hw'
      rw [Function.leftInverse_invFun (hDF_inj B) v, Function.leftInverse_invFun (hDF_inj B) v',
        dist_eq_norm, dist_eq_norm, ← map_sub]
      simpa using hDF_norm B (v - v')
    have hle : (μHE[n] : Measure (Rn n)) (closedBall 0 1) ≤
        (μHE[n] : Measure (Amb n ℓ)) (DF B '' closedBall 0 1) := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hgLip.mono (image_subset_range (DF B) (closedBall 0 1)))
      have hli : ∀ v, Function.invFun (DF B) (DF B v) = v := Function.leftInverse_invFun (hDF_inj B)
      rw [image_image] at h
      simpa only [hli, image_id', ENNReal.coe_one, one_pow, one_mul] using h
    have himg' : (μHE[n] : Measure (Amb n ℓ)) (DF B '' closedBall 0 1) =
        ENNReal.ofReal (LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) *
          (volume : Measure (Rn n)) (closedBall 0 1) := himg
    rw [himg', hball] at hle
    have h1 : 1 ≤ ENNReal.ofReal (LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) := by
      exact (ENNReal.mul_le_mul_iff_left hvol_ball_pos.ne' hvol_ball_fin).mp (by rwa [one_mul])
    exact ENNReal.one_le_ofReal.mp h1
  have hJ_eq : ∀ x, DifferentiableAt ℝ G x → Poincare.SimonGMT.Chapter02.areaJacobianAt F x =
      LinearMap.normDet (DF (fderiv ℝ G x) : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro x hx
    rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, (hFderiv x hx).fderiv]
  have hJ1 : ∀ x, DifferentiableAt ℝ G x → 1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt F x := by
    intro x hx
    rw [hJ_eq x hx]
    exact hDF_normDet _
  have hGdiff : ∀ᵐ x ∂(volume : Measure (Rn n)), DifferentiableAt ℝ G x :=
    hGLip.ae_differentiableAt
  -- on the open ball `f` and `G` have the same derivative
  have hfG_fderiv : ∀ x : Rn n, ‖x‖ < R → fderiv ℝ f x = fderiv ℝ G x := by
    intro x hx
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : Rn n) R by
      rwa [mem_ball, dist_zero_right])] with x' hx'
    exact hGeq (ball_subset_closedBall hx')

  -- Step 6: an integrable version `g₁` of the density, and its Lebesgue points.
  have hFimg_ball : ∀ x : Rn n, ‖x‖ < 2 * R / 3 → ‖F x‖ < R := by
    intro x hx
    have hx' : x ∈ closedBall (0 : Rn n) R := by
      rw [mem_closedBall, dist_zero_right]; linarith only [hx, hR0]
    have h := hF_norm_sq_le x hx'
    have hx2 : ‖x‖ * ‖x‖ < (2 * R / 3) * (2 * R / 3) := mul_self_lt_mul_self (norm_nonneg x) hx
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hR0.le two_ne_zero).mp
      (by linarith only [h, hx2, sq_nonneg R])
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : Rn n → ℝ,
      g₁ = (ball (0 : Rn n) (2 * R / 3)).indicator (fun x => (g₀ x).toReal) := ⟨_, rfl⟩
  have hg₀fin : ∀ x, g₀ x ≠ ∞ := by
    intro x
    rw [hg₀def]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    by_cases h : F x ∈ M₂
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  have hFball_sub : ∀ S : Set (Rn n), S ⊆ ball 0 (2 * R / 3) → F '' S ⊆ ball 0 R := by
    rintro S hS _ ⟨x, hx, rfl⟩
    have := hS hx
    rw [mem_ball, dist_zero_right] at this ⊢
    exact hFimg_ball x this
  have hg₀_lint : ∫⁻ x in ball (0 : Rn n) (2 * R / 3), g₀ x < ∞ := by
    have hS := hFimg_meas _ (measurableSet_ball : MeasurableSet (ball (0 : Rn n) (2 * R / 3)))
    have hsub := hFball_sub _ subset_rfl
    have h := hREP _ hS hsub
    rw [hFinj.preimage_image] at h
    rw [← h]
    calc V.weight (F '' ball 0 (2 * R / 3)) ≤ V.weight (closedBall 0 ρ) :=
          measure_mono (hsub.trans (ball_subset_closedBall.trans
            (closedBall_subset_closedBall (by linarith only [hRρ, hR0]))))
      _ ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) := hmass
      _ < ∞ := ENNReal.ofReal_lt_top
  have hg₁int : Integrable g₁ := by
    rw [hg₁def, integrable_indicator_iff measurableSet_ball]
    exact integrable_toReal_of_lintegral_ne_top hg₀meas.aemeasurable hg₀_lint.ne
  have hg₁nonneg : ∀ x, 0 ≤ g₁ x := by
    intro x
    rw [hg₁def]
    exact indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x
  have hg₀_g₁ : ∀ S : Set (Rn n), MeasurableSet S → S ⊆ ball 0 (2 * R / 3) →
      ∫⁻ x in S, g₀ x = ENNReal.ofReal (∫ x in S, g₁ x) := by
    intro S hS hSsub
    rw [ofReal_integral_eq_lintegral_ofReal hg₁int.integrableOn (ae_of_all _ hg₁nonneg)]
    refine setLIntegral_congr_fun hS (fun y hy => ?_)
    rw [hg₁def, indicator_of_mem (hSsub hy), ENNReal.ofReal_toReal (hg₀fin y)]
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure (Rn n))) hg₁int.locallyIntegrable 1
  -- Step 7: volumes of balls and the lower density bound (P.ii).
  have hωpos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hvol_ball : ∀ (x : Rn n) (s : ℝ), 0 ≤ s →
      (volume : Measure (Rn n)) (closedBall x s) = ENNReal.ofReal (unitBallVolume n * s ^ n) := by
    intro x s hs
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, unitBallVolume,
      ← ENNReal.ofReal_pow hs, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.pi ^ (1 / 2 : ℝ)) n,
      ← Real.rpow_mul Real.pi_pos.le, show (1 / 2 : ℝ) * n = n / 2 by ring]
    ring
  have hlow : ∀ y ∈ V.support, ‖y‖ ≤ R → ∀ s, 0 < s → s ≤ ρ / 2 →
      ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall y s) := by
    intro y hy hyR s hs hsρ
    have hy3 : ‖y‖ ≤ 3 * δ * ρ := by linarith only [hyR, hRle, mul_pos hδ0 hρ0]
    obtain ⟨-, h⟩ := hDB ℓ U hU V H δ ρ hδ0 hδle hAH y hy3 s hs hsρ
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h hy).1
    have : 0 < unitBallVolume n * s ^ n := mul_pos hωpos (pow_pos hs n)
    linarith only [mul_nonneg (sub_nonneg.mpr hCPδ) this.le]
  -- Step 8: `F(x) ∈ M₂` for a.e. `x` in `Bⁿ_{R/2}(0)` (the carrier fills the graph).
  have hE : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 → F x ∈ M₂ := by
    filter_upwards [hLeb] with x hx hxR
    by_contra hxM
    have hxB : x ∈ ball (0 : Rn n) (2 * R / 3) := by
      rw [mem_ball, dist_zero_right]; linarith only [hxR, hR0]
    have hg₁x : g₁ x = 0 := by
      rw [hg₁def, indicator_of_mem hxB, hg₀def]
      simp [indicator_of_notMem hxM]
    have hlim : Tendsto (fun s : ℝ => ⨍ y in closedBall x s, ‖g₁ y - g₁ x‖)
        (𝓝[>] 0) (𝓝 0) := by
      refine hx (fun _ => x) (fun s => s) tendsto_id ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      exact mem_closedBall_self (mul_nonneg zero_le_one hs.le)
    have hFxR : ‖F x‖ < R := hFimg_ball x (by linarith only [hxR, hR0])
    have hFx_supp : F x ∈ V.support :=
      hF_supp x (by rw [mem_closedBall, dist_zero_right]; linarith only [hxR, hR0]) hFxR.le
    set s₀ := min (R - ‖F x‖) (2 * R / 3 - ‖x‖) with hs₀
    have hs₀pos : 0 < s₀ := lt_min (sub_pos.mpr hFxR) (by linarith only [hxR, hR0])
    obtain ⟨s, hs_avg, hs_mem⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (Ioo_mem_nhdsGT hs₀pos)).exists
    have hs0 : 0 < s := hs_mem.1
    have hs1 : s < R - ‖F x‖ := lt_of_lt_of_le hs_mem.2 (min_le_left _ _)
    have hs2 : s < 2 * R / 3 - ‖x‖ := lt_of_lt_of_le hs_mem.2 (min_le_right _ _)
    -- upper bound for the mass of `B_s(F x)`
    have hball_sub : closedBall (F x) s ⊆ ball 0 R := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      calc ‖w‖ = ‖(w - F x) + F x‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - F x‖ + ‖F x‖ := norm_add_le _ _
        _ < R := by linarith only [hw, hs1]
    have hpre_sub : F ⁻¹' closedBall (F x) s ⊆ closedBall x s := by
      intro x' hx'
      rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx'
      rw [mem_closedBall, dist_eq_norm]
      exact (hF_ge x' x).trans hx'
    have hballx_sub : closedBall x s ⊆ ball (0 : Rn n) (2 * R / 3) := by
      intro x' hx'
      rw [mem_closedBall, dist_eq_norm] at hx'
      rw [mem_ball, dist_zero_right]
      calc ‖x'‖ = ‖(x' - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' - x‖ + ‖x‖ := norm_add_le _ _
        _ < 2 * R / 3 := by linarith only [hx', hs2]
    have hup : V.weight (closedBall (F x) s) ≤ ENNReal.ofReal (∫ y in closedBall x s, g₁ y) := by
      rw [hREP _ measurableSet_closedBall hball_sub,
        ← hg₀_g₁ _ measurableSet_closedBall hballx_sub]
      exact lintegral_mono_set hpre_sub
    have hlo := hlow (F x) hFx_supp hFxR.le s hs0
      (by linarith only [hs1, norm_nonneg (F x), hRρ, hρ0])
    -- the average bound
    have hvol := hvol_ball x s hs0.le
    have hpos : 0 < unitBallVolume n * s ^ n := mul_pos hωpos (pow_pos hs0 n)
    have havg : ⨍ y in closedBall x s, ‖g₁ y - g₁ x‖ =
        (unitBallVolume n * s ^ n)⁻¹ * ∫ y in closedBall x s, g₁ y := by
      rw [setAverage_eq, measureReal_def, hvol, ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hg₁x, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hg₁nonneg y)]
    rw [havg] at hs_avg
    have hint_lt : ∫ y in closedBall x s, g₁ y < unitBallVolume n * s ^ n / 2 := by
      have := (inv_mul_lt_iff₀ hpos).mp hs_avg
      linarith only [this]
    have := hlo.trans hup
    rw [ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg measurableSet_closedBall
      (fun y _ => hg₁nonneg y))] at this
    exact absurd this (not_le.mpr hint_lt)

  -- Step 9: `θ ≥ 1` along the graph, a.e.
  have hθge : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 → F x ∈ M₂ → 1 ≤ θ' (F x) := by
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Set (Amb n ℓ), S₁ = {w | w ∈ M₂ ∧ θ' w < 1} ∩ ball 0 R := ⟨_, rfl⟩
    have hS₁meas : MeasurableSet S₁ := by
      rw [hS₁]
      exact (hM₂meas.inter (measurableSet_lt hθ'meas measurable_const)).inter measurableSet_ball
    have hS₁null : V.weight S₁ = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hθ1)
      intro w hw
      rw [hS₁] at hw
      simp only [Set.mem_ofPred_eq, not_le]
      rw [hM₂θ w hw.1.1]
      exact hw.1.2
    have h := hREP S₁ hS₁meas (by rw [hS₁]; exact inter_subset_right)
    rw [hS₁null, eq_comm, lintegral_eq_zero_iff hg₀meas, Filter.EventuallyEq,
      ae_restrict_iff' (hFmeas hS₁meas)] at h
    filter_upwards [h, hGdiff] with x hx hxd hxR hxM
    by_contra hlt
    push Not at hlt
    have hmem : x ∈ F ⁻¹' S₁ := by
      rw [mem_preimage, hS₁]
      exact ⟨⟨hxM, hlt⟩, by
        rw [mem_ball, dist_zero_right]; exact hFimg_ball x (by linarith only [hxR, hR0])⟩
    have h0 := hx hmem
    rw [hg₀def] at h0
    simp only [Pi.zero_apply, indicator_of_mem hxM, mul_eq_zero, ENNReal.ofReal_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (not_le.mpr (lt_of_lt_of_le zero_lt_one (hJ1 x hxd)))
    · exact absurd h0 (not_le.mpr (hM₂pos (F x) hxM))
  -- integrals against the weight
  have hint_weight : ∀ h : Amb n ℓ → ℝ,
      ∫ w, h w ∂V.weight = ∫ w in V.carrier, h w * V.mult w ∂μHE[n] := by
    intro h
    rw [RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
      V.aemeasurable_mult.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with w hw
    rw [ENNReal.toReal_ofReal (V.mult_pos w hw).le, smul_eq_mul, mul_comm]
  -- the local representation as an identity of measures
  have hμν : V.weight.restrict (ball 0 R) =
      (Measure.map F ((volume : Measure (Rn n)).withDensity g₀)).restrict (ball 0 R) := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS,
      Measure.map_apply hFmeas (hS.inter measurableSet_ball),
      withDensity_apply _ (hFmeas (hS.inter measurableSet_ball)),
      hREP _ (hS.inter measurableSet_ball) inter_subset_right]
  -- change of variables `x' = x + r v` on `ℝⁿ`
  have hcov : ∀ (k : Rn n → ℝ) (x : Rn n) (r : ℝ), 0 < r →
      ∫ v, k (x + r • v) = (r⁻¹) ^ n * ∫ x', k x' := by
    intro k x r hr
    have h1 := Measure.integral_comp_smul (volume : Measure (Rn n)) (fun u => k (x + u)) r
    rw [hfr] at h1
    rw [h1, integral_add_left_eq_self, abs_of_pos (inv_pos.mpr (pow_pos hr n)), inv_pow,
      smul_eq_mul]
  -- Step 10: the approximate tangent planes along the graph.
  have hTan : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 →
      V.tangentProj (F x) =
        (LinearMap.range (DF (fderiv ℝ G x) : Rn n →ₗ[ℝ] Amb n ℓ)).starProjection := by
    filter_upwards [hLeb, hGdiff, hE] with x hxLeb hxd hxE hxR
    have hxM := hxE hxR
    obtain ⟨B, hB⟩ : ∃ B, B = fderiv ℝ G x := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D, D = DF B := ⟨_, rfl⟩
    rw [← hB, ← hD]
    have hDer : HasFDerivAt F D x := by rw [hD, hB]; exact hFderiv x hxd
    have hFxR : ‖F x‖ < 5 * R / 6 := by
      have hx' : x ∈ closedBall (0 : Rn n) R := by
        rw [mem_closedBall, dist_zero_right]; linarith only [hxR, hR0]
      have h := hF_norm_sq_le x hx'
      have hx2 : ‖x‖ * ‖x‖ < (R / 2) * (R / 2) := mul_self_lt_mul_self (norm_nonneg x) hxR
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by linarith only [hR0]) two_ne_zero).mp
        (by linarith only [h, hx2, sq_nonneg R])
    have hg₁x : g₁ x = LinearMap.normDet (D : Rn n →ₗ[ℝ] Amb n ℓ) * V.mult (F x) := by
      rw [hg₁def, indicator_of_mem (show x ∈ ball (0 : Rn n) (2 * R / 3) by
        rw [mem_ball, dist_zero_right]; linarith only [hxR, hR0]), hg₀def]
      simp only [indicator_of_mem hxM]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F x),
        ENNReal.toReal_ofReal (hM₂pos (F x) hxM).le, hJ_eq x hxd, hM₂θ (F x) hxM, ← hB, ← hD]
    have hHW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult (F x) (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ)) := by
      refine ⟨hD ▸ hDF_finrank B, fun φ => ?_⟩
      -- the support radius and a bound of the test function
      obtain ⟨Rφ, hRφ1, hRφ⟩ : ∃ Rφ : ℝ, 1 ≤ Rφ ∧ ∀ z : Amb n ℓ, Rφ < ‖z‖ → φ z = 0 := by
        obtain ⟨C, hC⟩ := (φ.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
        refine ⟨max C 1, le_max_right _ _, fun z hz => image_eq_zero_of_notMem_tsupport fun hzt => ?_⟩
        have := hC hzt
        rw [mem_closedBall, dist_zero_right] at this
        exact absurd (this.trans (le_max_left C 1)) (not_le.mpr hz)
      obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
      -- (a) the weighted blow-up as a rescaled integral against the weight
      have h6a : ∀ r : ℝ, 0 < r →
          ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F x) r '' V.carrier,
            φ z * V.mult (F x + r • z) ∂μHE[n] =
          (r⁻¹) ^ n * ∫ w, φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) ∂V.weight := by
        intro r hr
        rw [hint_weight, inv_pow]
        exact Submission.rsod_blowUp_setIntegral_eq n ℓ V.carrier (fun z => φ z) V.mult (F x) r hr
      -- (b) localisation: near `F x` the weight is the pushforward of `g₀ Lⁿ`
      have hcontψ : ∀ r : ℝ, Continuous (fun w : Amb n ℓ =>
          φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w)) := by
        intro r
        unfold Poincare.SimonGMT.Chapter03.blowUpMap
        fun_prop
      have h6b : ∀ r : ℝ, 0 < r → r * Rφ < R / 6 →
          ∫ w, φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) ∂V.weight =
          ∫ x', g₁ x' * φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x')) := by
        intro r hr hrR
        have hsupp : ∀ w, r * Rφ < ‖w - F x‖ →
            φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) = 0 := by
          intro w hw
          apply hRφ
          rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
            Real.norm_of_nonneg (inv_pos.mpr hr).le, lt_inv_mul_iff₀ hr]
          exact hw
        have hout : ∀ w ∉ ball (0 : Amb n ℓ) R,
            φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) = 0 := by
          intro w hw
          apply hsupp
          rw [mem_ball, dist_zero_right, not_lt] at hw
          have := norm_sub_norm_le w (F x)
          linarith only [this, hw, hFxR, hrR]
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, hμν,
          setIntegral_eq_integral_of_forall_compl_eq_zero hout,
          integral_map hFmeas.aemeasurable (hcontψ r).aestronglyMeasurable,
          integral_withDensity_eq_integral_toReal_smul₀ hg₀meas.aemeasurable
            (ae_of_all _ fun x' => (hg₀fin x').lt_top)]
        refine integral_congr_ae (ae_of_all _ fun x' => ?_)
        simp only [smul_eq_mul]
        by_cases hφ : φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x')) = 0
        · rw [hφ, mul_zero, mul_zero]
        · congr 1
          have h1 : ‖F x' - F x‖ ≤ r * Rφ := by
            by_contra h
            exact hφ (hsupp _ (not_le.mp h))
          have h2 := (hF_ge x' x).trans h1
          have h3 : x' ∈ ball (0 : Rn n) (2 * R / 3) := by
            rw [mem_ball, dist_zero_right]
            calc ‖x'‖ = ‖x + (x' - x)‖ := by rw [add_sub_cancel]
              _ ≤ ‖x‖ + ‖x' - x‖ := norm_add_le _ _
              _ < 2 * R / 3 := by linarith only [hxR, h2, hrR, hR0]
          rw [hg₁def, indicator_of_mem h3]
      -- (d) the blow-up limit on the parameter domain
      have hsuppQ : ∀ r : ℝ, 0 < r → ∀ v : Rn n, Rφ < ‖v‖ →
          φ (r⁻¹ • (F (x + r • v) - F x)) = 0 := by
        intro r hr v hv
        apply hRφ
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le, lt_inv_mul_iff₀ hr]
        have := hF_ge (x + r • v) x
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at this
        calc r * Rφ < r * ‖v‖ := mul_lt_mul_of_pos_left hv hr
          _ ≤ _ := this
      have hnotmem : ∀ v : Rn n, v ∉ closedBall (0 : Rn n) Rφ → Rφ < ‖v‖ := by
        intro v hv
        rwa [mem_closedBall, dist_zero_right, not_le] at hv
      have hcontQ : ∀ r : ℝ, Continuous (fun v : Rn n => φ (r⁻¹ • (F (x + r • v) - F x))) := by
        intro r
        have hφc := φ.continuous
        fun_prop
      have hintQ : ∀ r : ℝ, 0 < r → Integrable (fun v : Rn n => φ (r⁻¹ • (F (x + r • v) - F x))) := by
        intro r hr
        exact (hcontQ r).integrable_of_hasCompactSupport (HasCompactSupport.intro
          (isCompact_closedBall (0 : Rn n) Rφ) (fun v hv => hsuppQ r hr v (hnotmem v hv)))
      have hintg : ∀ r : ℝ, 0 < r → Integrable (fun v : Rn n => g₁ (x + r • v)) := by
        intro r hr
        exact (hg₁int.comp_add_left x).comp_smul hr.ne'
      have hT2 : Tendsto (fun r : ℝ => ∫ v, φ (r⁻¹ • (F (x + r • v) - F x))) (𝓝[>] 0)
          (𝓝 (∫ v, φ (D v))) := by
        refine tendsto_integral_filter_of_dominated_convergence
          ((closedBall (0 : Rn n) Rφ).indicator (fun _ => Cφ)) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun r => (hcontQ r).aestronglyMeasurable
        · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
          refine ae_of_all _ fun v => ?_
          by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
          · rw [indicator_of_mem hv]
            exact hCφ _
          · rw [indicator_of_notMem hv, hsuppQ r hr v (hnotmem v hv), norm_zero]
        · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
            measurableSet_closedBall
        · refine ae_of_all _ fun v => ?_
          have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
          have hD0 : HasFDerivAt F D (x + (0 : ℝ) • v) := by simpa using hDer
          have hcomp := (hD0.comp_hasDerivAt (0 : ℝ) hpath).tendsto_slope_zero_right
          simp only [zero_add, zero_smul, add_zero, Function.comp_def] at hcomp
          exact (φ.continuous.tendsto _).comp hcomp
      have hLebx : Tendsto (fun r : ℝ => ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖)
          (𝓝[>] 0) (𝓝 0) := by
        refine hxLeb (fun _ => x) (fun r => Rφ * r) ?_ ?_
        · refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have : Tendsto (fun r : ℝ => Rφ * r) (𝓝 0) (𝓝 (Rφ * 0)) :=
              (continuous_const.mul continuous_id).tendsto 0
            rw [mul_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
            exact mul_pos (zero_lt_one.trans_le hRφ1) hr
        · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
          exact mem_closedBall_self
            (mul_nonneg zero_le_one (mul_nonneg (zero_le_one.trans hRφ1) hr.le))
      have hT1 : Tendsto (fun r : ℝ => (∫ v, g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x))) -
          g₁ x * ∫ v, φ (r⁻¹ • (F (x + r • v) - F x))) (𝓝[>] 0) (𝓝 0) := by
        have hlim : Tendsto (fun r : ℝ => Cφ * (unitBallVolume n * Rφ ^ n) *
            ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖) (𝓝[>] 0) (𝓝 0) := by
          have h := hLebx.const_mul (Cφ * (unitBallVolume n * Rφ ^ n))
          rwa [mul_zero] at h
        refine squeeze_zero_norm' ?_ hlim
        filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        have hi1 : Integrable (fun v : Rn n => g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x))) :=
          (hintg r hr).mul_bdd (hcontQ r).aestronglyMeasurable (ae_of_all _ fun v => hCφ _)
        have hi2 : Integrable (fun v : Rn n => g₁ x * φ (r⁻¹ • (F (x + r • v) - F x))) :=
          (hintQ r hr).const_mul _
        rw [← integral_const_mul, ← integral_sub hi1 hi2]
        have hmem : ∀ v : Rn n, (x + r • v ∈ closedBall x (Rφ * r)) ↔ v ∈ closedBall (0 : Rn n) Rφ := by
          intro v
          rw [mem_closedBall, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hr.le, dist_zero_right, mul_comm Rφ r]
          exact ⟨fun h => le_of_mul_le_mul_left h hr, fun h => mul_le_mul_of_nonneg_left h hr.le⟩
        have hind : ∀ v : Rn n, (closedBall (0 : Rn n) Rφ).indicator
            (fun v => ‖g₁ (x + r • v) - g₁ x‖) v =
            (closedBall x (Rφ * r)).indicator (fun y => ‖g₁ y - g₁ x‖) (x + r • v) := by
          intro v
          by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
          · rw [indicator_of_mem hv, indicator_of_mem ((hmem v).mpr hv)]
          · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv ((hmem v).mp h))]
        have hbound_int : Integrable (fun v : Rn n => Cφ * (closedBall (0 : Rn n) Rφ).indicator
            (fun v => ‖g₁ (x + r • v) - g₁ x‖) v) := by
          refine Integrable.const_mul ?_ _
          refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
          exact ((hintg r hr).integrableOn.sub (integrableOn_const measure_closedBall_lt_top.ne)).norm
        have hpos : 0 < unitBallVolume n * (Rφ * r) ^ n :=
          mul_pos hωpos (pow_pos (mul_pos (zero_lt_one.trans_le hRφ1) hr) n)
        have havg : ∫ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ =
            unitBallVolume n * (Rφ * r) ^ n * ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ := by
          rw [setAverage_eq, measureReal_def, hvol_ball x (Rφ * r) (mul_nonneg (zero_le_one.trans hRφ1) hr.le),
            ENNReal.toReal_ofReal hpos.le, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        calc ‖∫ v, (g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x)) -
              g₁ x * φ (r⁻¹ • (F (x + r • v) - F x)))‖
            ≤ ∫ v, Cφ * (closedBall (0 : Rn n) Rφ).indicator
                (fun v => ‖g₁ (x + r • v) - g₁ x‖) v := by
              refine norm_integral_le_of_norm_le hbound_int (ae_of_all _ fun v => ?_)
              rw [← sub_mul, norm_mul]
              by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
              · rw [indicator_of_mem hv, mul_comm]
                exact mul_le_mul_of_nonneg_right (hCφ _) (norm_nonneg _)
              · rw [indicator_of_notMem hv, hsuppQ r hr v (hnotmem v hv), norm_zero, mul_zero,
                  mul_zero]
          _ = Cφ * (unitBallVolume n * Rφ ^ n) * ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ := by
              rw [integral_const_mul, funext hind,
                hcov (fun y => (closedBall x (Rφ * r)).indicator (fun y => ‖g₁ y - g₁ x‖) y) x r hr,
                integral_indicator measurableSet_closedBall, havg, mul_pow, inv_pow]
              have hrn : (r ^ n)⁻¹ * r ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero n hr.ne')
              calc Cφ * ((r ^ n)⁻¹ * (unitBallVolume n * (Rφ ^ n * r ^ n) *
                    ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖))
                  = Cφ * (unitBallVolume n * Rφ ^ n) *
                      (⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖) * ((r ^ n)⁻¹ * r ^ n) := by ring
                _ = _ := by rw [hrn, mul_one]
      have h6d : Tendsto (fun r : ℝ => ∫ v, g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x)))
          (𝓝[>] 0) (𝓝 (g₁ x * ∫ v, φ (D v))) := by
        have h := hT1.add (hT2.const_mul (g₁ x))
        rw [zero_add] at h
        exact h.congr' (Eventually.of_forall fun r => sub_add_cancel _ _)
      -- (e) the limit is `θ(F x)` times the plane integral
      have h6e : g₁ x * ∫ v, φ (D v) = V.mult (F x) *
          ∫ z in (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)), φ z ∂μHE[n] := by
        have hmeasP : (μHE[n] : Measure (Amb n ℓ)).restrict
            (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) =
            ENNReal.ofReal (LinearMap.normDet (D : Rn n →ₗ[ℝ] Amb n ℓ)) •
              Measure.map D (volume : Measure (Rn n)) := by
          ext S hS
          rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply D.continuous.measurable hS,
            smul_eq_mul]
          have h1 : S ∩ (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) =
              (D : Rn n →ₗ[ℝ] Amb n ℓ) '' ((D : Rn n →ₗ[ℝ] Amb n ℓ) ⁻¹' S) := by
            rw [image_preimage_eq_inter_range, LinearMap.coe_range]
          rw [h1]
          have h2 := LinearMap.euclideanHausdorffMeasure_image (D : Rn n →ₗ[ℝ] Amb n ℓ)
            ((D : Rn n →ₗ[ℝ] Amb n ℓ) ⁻¹' S)
          have h3 := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
          rw [hfr] at h2 h3
          rw [h3] at h2
          exact h2
        rw [hmeasP, integral_smul_measure,
          integral_map D.continuous.aemeasurable (map_continuous φ).aestronglyMeasurable,
          ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _), hg₁x, smul_eq_mul]
        ring
      rw [← h6e]
      refine h6d.congr' ?_
      have hRφ0 : 0 < Rφ := zero_lt_one.trans_le hRφ1
      have hr₀ : 0 < R / (6 * Rφ) := div_pos hR0 (mul_pos (by norm_num) hRφ0)
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      have hrR : r * Rφ < R / 6 := by
        have h := hr.2
        rw [lt_div_iff₀ (mul_pos (by norm_num) hRφ0)] at h
        linarith only [h]
      rw [h6a r hr.1, h6b r hr.1 hrR]
      exact hcov (fun x' => g₁ x' * φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x'))) x r hr.1
    have hθx : V.mult (F x) ≠ 0 := (V.mult_pos _ (hM₂sub hxM)).ne'
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (F x) P := ⟨_, hHW⟩
    have hch := Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique hθx
      (Classical.choose_spec hex) hHW
    unfold RectifiableVarifold.tangentProj
    rw [dite_eq_left hex]
    simp only [hch]

  -- Step 11: the comparison `Lⁿ⌞A ≤ (Jacobian) ≤ Hⁿ⌞F(A) ≤ μ_V⌞F(A)`.
  have hA_ball : ∀ x ∈ A, ‖x‖ < R / 2 := by
    intro x hx
    have := hAsub hx
    rwa [mem_ball, dist_zero_right] at this
  have hFA_sub : F '' A ⊆ ball 0 R :=
    hFball_sub A (fun x hx => by
      rw [mem_ball, dist_zero_right]; linarith only [hA_ball x hx, hR0])
  have hmeas_le : (μHE[n] : Measure (Amb n ℓ)).restrict (F '' A) ≤ V.weight.restrict (F '' A) := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS, inter_comm,
      ← image_inter_preimage]
    have hT : MeasurableSet (A ∩ F ⁻¹' S) := hAm.inter (hFmeas hS)
    rw [hREP _ (hFimg_meas _ hT) ((image_mono inter_subset_left).trans hFA_sub),
      hFinj.preimage_image]
    have h := hArea _ hT (fun _ => 1)
    rw [setLIntegral_one] at h
    rw [h]
    refine lintegral_mono_ae ((ae_restrict_iff' hT).mpr ?_)
    filter_upwards [hE, hθge] with x hxE hxθ hxT
    have hxR := hA_ball x hxT.1
    have hxM := hxE hxR
    rw [hg₀def, mul_one]
    simp only [indicator_of_mem hxM]
    exact le_mul_of_one_le_right zero_le (ENNReal.one_le_ofReal.mpr (hxθ hxR hxM))
  have hgood : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ A →
      Φ (q (graphPoint x (f x)))
        ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
          q.toLinearEquiv.toLinearMap).starProjection ≤
      ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
        Φ (F x) (V.tangentProj (F x)) := by
    filter_upwards [hTan, hGdiff] with x hxT hxd hxA
    have hxR := hA_ball x hxA
    have hproj : ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
        q.toLinearEquiv.toLinearMap).starProjection = V.tangentProj (F x) := by
      rw [hxT hxR, hfG_fderiv x (by linarith only [hxR, hR0])]
      simp only [hDF_range]
    rw [hproj, ← hF_on x (by rw [mem_closedBall, dist_zero_right]; linarith only [hxR, hR0])]
    exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr (hJ1 x hxd))
  calc ∫⁻ x in A, Φ (q (graphPoint x (f x)))
        ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
          q.toLinearEquiv.toLinearMap).starProjection
      ≤ ∫⁻ x in A, ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
          Φ (F x) (V.tangentProj (F x)) :=
        lintegral_mono_ae ((ae_restrict_iff' hAm).mpr hgood)
    _ = ∫⁻ y in F '' A, Φ y (V.tangentProj y) ∂μHE[n] :=
        (hArea A hAm (fun y => Φ y (V.tangentProj y))).symm
    _ ≤ ∫⁻ y in F '' A, Φ y (V.tangentProj y) ∂V.weight := lintegral_mono' hmeas_le le_rfl
    _ = ∫⁻ y in q '' graphOver f A, Φ y (V.tangentProj y) ∂V.weight := by rw [hFA]

/-- **Simon Ch. 5, proof of 5.2, (10)–(11) and the Hölder argument after (11)**: a Lipschitz graph
with decaying tilt-excess is `C^{1,1−n/p}`.  For `n ≥ 1` and `p > n` there are `L ∈ (0, 1/4]`,
`δ₃ > 0` and `C ≥ 0` (depending only on `n, ℓ, p`) such that, under 2.3 with `0 < δ ≤ δ₃`, if
`spt V ∩ B_R(0) = q(graph f) ∩ B_R(0)` with `0 < R ≤ δρ`, `f(0) = 0`, `Lip f ≤ L` on `Bⁿ_R(0)`, and
`A ≥ 0` and the `n`-planes `S(ζ)` satisfy `E(ζ, s, S(ζ)) ≤ A (s/R)^{2(1−n/p)}` for
`ζ ∈ spt V ∩ B_{R/2}(0)`, `0 < s ≤ R/2`, then `f` is `C¹` on `B̆ⁿ_{R/16}(0)`,
`|Df(x) − Df(y)| ≤ C √A (|x − y|/R)^{1−n/p}` there, and `q(graph Df(z)) = S(q(z, f(z)))` for every
`z` in that ball.

Proof: `L = L₀/√n` and `δ₃ = min{δ₂, 1/8}`, with `L₀` from `allard52_graph_plane_algebra` and `δ₂`
from `allard52_graph_comparison`; `C` is the constant of `allard52_campanato_center_holder`.  Then
`B_R(0) ⊆ B_ρ(0) ⊆ U` and `f` is 1-Lipschitz, so the graph comparison and the measurability of
`p_{T_x M}` (`allard52_tangent_ae`) turn the decay into the Campanato bound of
`allard52_campanato_from_tilt` for `G(x) = p_{q(graph Df(x))}` with centres
`c(z) = p_{S(q(z, f(z)))}`.  Hence `G = c` a.e. in `B̆ⁿ_{R/4}(0)` (`allard52_campanato_ae_center`)
and `c` is `(1 − n/p)`-Hölder in `B̆ⁿ_{R/16}(0)` (`allard52_campanato_center_holder`).  On the
full-measure set `Z` where `f` is differentiable (Rademacher) and `G = c`, `|Df| ≤ √n L = L₀`, so
`|Df(x) − Df(y)| ≤ |G(x) − G(y)| = |c(x) − c(y)|`, and `allard52_c1_holder_of_ae_fderiv` gives the
`C¹` and Hölder assertions.  Finally `G` (as `Df` is continuous) and `c` (Hölder) are continuous on
`B̆ⁿ_{R/16}(0)` and agree a.e., hence everywhere, and a subspace is the range of its orthogonal
projection. -/
theorem allard52_graph_campanato : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ L δ₃ C : ℝ, 0 < L ∧ L ≤ 1 / 4 ∧ 0 < δ₃ ∧ 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₃ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), 0 < R → R ≤ δ * ρ → f 0 = 0 → LipschitzOnWith (Real.toNNReal L) f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → ∀ (S : Amb n ℓ → Submodule ℝ (Amb n ℓ)) (A : ℝ), 0 ≤ A → (∀ ζ ∈ V.support ∩ closedBall 0 (R / 2), Module.finrank ℝ (S ζ) = n ∧ ∀ s : ℝ, 0 < s → s ≤ R / 2 → V.tiltExcess ζ s (S ζ) ≤ A * (s / R) ^ (2 * (1 - n / p))) → ContDiffOn ℝ 1 f (ball 0 (R / 16)) ∧ (∀ x ∈ ball (0 : Rn n) (R / 16), ∀ y ∈ ball (0 : Rn n) (R / 16), hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ C * Real.sqrt A * (‖x - y‖ / R) ^ (1 - n / p)) ∧ ∀ z ∈ ball (0 : Rn n) (R / 16), (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f z v))).map q.toLinearEquiv.toLinearMap = S (q (graphPoint z (f z))) := by
  intro n ℓ hn p hp
  -- Step 1: the constants `L = L₀/√n`, `δ₃ = min{δ₂, 1/8}` and `C = C₃`.
  obtain ⟨L₀, hL₀pos, hL₀le, hAlg1, -, -, hAlg4, -, hAlg6⟩ :=
    Submission.allard52_graph_plane_algebra n ℓ hn
  obtain ⟨δ₂, hδ₂pos, hCmp⟩ := Submission.allard52_graph_comparison n hn p hp
  obtain ⟨C₃, hC₃, hHolc⟩ := Submission.allard52_campanato_center_holder n hn
  have hsqrt_ge : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hsqrt_pos : 0 < Real.sqrt n := one_pos.trans_le hsqrt_ge
  have hLpos : 0 < L₀ / Real.sqrt n := div_pos hL₀pos hsqrt_pos
  have hLle : L₀ / Real.sqrt n ≤ 1 / 4 := (div_le_self hL₀pos.le hsqrt_ge).trans hL₀le
  refine ⟨L₀ / Real.sqrt n, min δ₂ (1 / 8), C₃, hLpos, hLle, lt_min hδ₂pos (by norm_num), hC₃, ?_⟩
  intro U hU V H δ ρ hδ hδle hAH q f R hR hRle hf0 hfL hgraph S A hA hdecay
  set α : ℝ := 1 - (n : ℝ) / p
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  have hα0 : 0 < α := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hα1 : α ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg n) hp0.le)
  -- Step 2: `R ≤ δρ ≤ ρ/8`, so `B_R(0) ⊆ B_ρ(0) ⊆ U`; `f` is 1-Lipschitz, and the graph
  -- comparison (with `δ ≤ δ₂`) and the measurability of `p_{T_x M}` are available.
  have hρ : 0 < ρ := hAH.1
  have hδ₂ : δ ≤ δ₂ := hδle.trans (min_le_left _ _)
  have hδ8 : δ ≤ 1 / 8 := hδle.trans (min_le_right _ _)
  have hRρ : R ≤ ρ := by nlinarith
  have hBRU : closedBall (0 : Amb n ℓ) R ⊆ U :=
    (closedBall_subset_closedBall hRρ).trans hAH.2.2.2.2.1
  have hL1 : Real.toNNReal (L₀ / Real.sqrt n) ≤ 1 := by
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal (hLle.trans (by norm_num))
  have hf1 : LipschitzOnWith 1 f (closedBall 0 R) := hfL.weaken hL1
  have hcmp := hCmp ℓ U hU V H δ ρ hδ hδ₂ hAH q f R hR hRle hf0 hf1 hgraph
  obtain ⟨hTmeas, -, -⟩ := Submission.allard52_tangent_ae n ℓ hn U hU V
  -- Step 3: the Campanato bound (book (10)–(11)) for `G = p_{q(graph Df)}` with centres
  -- `c(z) = p_{S(q(z, f(z)))}`.
  have hCamp := Submission.allard52_campanato_from_tilt n ℓ U V q f S R A (2 * α) hR hBRU hf0 hf1
    hgraph hTmeas hcmp fun ζ hζ => (hdecay ζ hζ).2
  set G : Rn n → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun x =>
    ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
      q.toLinearEquiv.toLinearMap).starProjection
  set c : Rn n → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun z => (S (q (graphPoint z (f z)))).starProjection
  have hGmeas : Measurable G := (hAlg6 q).measurable.comp (measurable_fderiv ℝ f)
  have hGbd : ∀ x, ‖G x‖ ≤ 1 := fun x => Submodule.starProjection_norm_le _
  -- Step 4: `G = c` a.e. in `B̆ⁿ_{R/4}(0)` and `c` is `α`-Hölder in `B̆ⁿ_{R/16}(0)`.
  have hGc := Submission.allard52_campanato_ae_center n (n + ℓ) (n + ℓ) G c A R α 1 hn hR hα0
    hGmeas hGbd hCamp
  have hcHol := hHolc (n + ℓ) (n + ℓ) G c A R α hA hR hα0 hα1 hGmeas hCamp
  -- Step 5: on the full-measure set `Z` of differentiability points (Rademacher) where `G = c`,
  -- `|Df| ≤ √n L = L₀`, so `|Df(x) − Df(y)| ≤ |G(x) − G(y)| = |c(x) − c(y)|`.
  have hsub : ball (0 : Rn n) (R / 16) ⊆ closedBall 0 R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hfLb : LipschitzOnWith (Real.toNNReal (L₀ / Real.sqrt n)) f (ball 0 (R / 16)) :=
    hfL.mono hsub
  have hRad : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball (0 : Rn n) (R / 16) →
      DifferentiableAt ℝ f x := by
    filter_upwards [hfLb.ae_differentiableWithinAt_of_mem] with x hx hxb
    exact (hx hxb).differentiableAt (isOpen_ball.mem_nhds hxb)
  set Z : Set (Rn n) := {x | x ∈ ball (0 : Rn n) (R / 16) ∧ DifferentiableAt ℝ f x ∧ G x = c x}
  have hZsub : Z ⊆ ball 0 (R / 16) := fun x hx => hx.1
  have hZnull : volume (ball (0 : Rn n) (R / 16) \ Z) = 0 := by
    have h1 : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball (0 : Rn n) (R / 16) → x ∈ Z := by
      filter_upwards [hRad, hGc] with x hx1 hx2 hxb
      exact ⟨hxb, hx1 hxb, hx2 (ball_subset_ball (by linarith) hxb)⟩
    rw [ae_iff] at h1
    refine measure_mono_null (fun x hx => ?_) h1
    exact fun h => hx.2 (h hx.1)
  have hDf : ∀ x ∈ ball (0 : Rn n) (R / 16), hsNorm (fderiv ℝ f x) ≤ L₀ := by
    intro x hx
    have h1 : ‖fderiv ℝ f x‖ ≤ L₀ / Real.sqrt n := by
      simpa only [Real.coe_toNNReal _ hLpos.le] using
        norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hx) hfLb
    calc hsNorm (fderiv ℝ f x) ≤ Real.sqrt n * ‖fderiv ℝ f x‖ := (hAlg4 _).2
      _ ≤ Real.sqrt n * (L₀ / Real.sqrt n) := by gcongr
      _ = L₀ := mul_div_cancel₀ L₀ hsqrt_pos.ne'
  have hZHol : ∀ x ∈ Z, ∀ y ∈ Z, hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤
      C₃ * Real.sqrt A * (‖x - y‖ / R) ^ α := by
    intro x hx y hy
    have h1 := (hAlg1 q (fderiv ℝ f x) (fderiv ℝ f y) (hDf x hx.1) (hDf y hy.1)).1
    have h2 : G x - G y = c x - c y := by rw [hx.2.2, hy.2.2]
    refine le_trans (Real.sqrt_le_sqrt ?_) (hcHol x hx.1 y hy.1)
    rw [← h2]
    exact h1
  -- The `C¹` and Hölder assertions.
  obtain ⟨hC1, hHol⟩ := Submission.allard52_c1_holder_of_ae_fderiv n ℓ f 0 (R / 16)
    (Real.toNNReal (L₀ / Real.sqrt n)) Z (C₃ * Real.sqrt A) R α
    (mul_nonneg hC₃ (Real.sqrt_nonneg A)) hR hα0 hfLb hZsub hZnull (fun x hx => hx.2.1) hZHol
  refine ⟨hC1, hHol, ?_⟩
  -- Step 6: `G` and `c` are continuous on `B̆ⁿ_{R/16}(0)` and agree a.e., hence everywhere.
  -- `‖T‖ ≤ |T|` for operators of `ℝ^{n+ℓ}` (`allard52_graph_plane_algebra` at `(n + ℓ, n + ℓ)`).
  obtain ⟨-, -, -, -, -, -, hAlg4', -, -⟩ :=
    Submission.allard52_graph_plane_algebra (n + ℓ) (n + ℓ) (by omega)
  have hGcont : ContinuousOn G (ball (0 : Rn n) (R / 16)) :=
    (hAlg6 q).comp_continuousOn (hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
  have hccont : ContinuousOn c (ball (0 : Rn n) (R / 16)) := by
    intro x hx
    have hlim : Tendsto (fun y : Rn n => C₃ * Real.sqrt A * (‖y - x‖ / R) ^ α) (𝓝 x) (𝓝 0) := by
      have h0 : Tendsto (fun y : Rn n => ‖y - x‖ / R) (𝓝 x) (𝓝 0) := by
        have h : Continuous fun y : Rn n => ‖y - x‖ / R := by fun_prop
        simpa using h.tendsto x
      have h1 := (Real.continuousAt_rpow_const 0 α (Or.inr hα0.le)).tendsto.comp h0
      rw [Real.zero_rpow hα0.ne'] at h1
      simpa using h1.const_mul (C₃ * Real.sqrt A)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds hlim)
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [norm_norm]
    exact (hAlg4' (c y - c x)).1.trans (hcHol y hy x hx)
  have hEq : EqOn G c (ball (0 : Rn n) (R / 16)) := by
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (Rn n))) ?_ isOpen_ball hGcont
      hccont
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hGc] with x hx hxb
    exact hx (ball_subset_ball (by linarith) hxb)
  -- A subspace is the range of its orthogonal projection.
  intro z hz
  have hPz : ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f z v))).map
      q.toLinearEquiv.toLinearMap).starProjection = (S (q (graphPoint z (f z)))).starProjection :=
    hEq hz
  rw [← Submodule.range_starProjection
      ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f z v))).map
        q.toLinearEquiv.toLinearMap), hPz, Submodule.range_starProjection]
theorem allard52_radial_height : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → Rn ℓ) (R δ : ℝ), 0 < R → 0 < δ → δ ≤ 1 → f 0 = 0 → ContDiffOn ℝ 1 f (ball 0 R) → LipschitzOnWith 1 f (ball 0 R) → (∀ x ∈ ball (0 : Rn n) R, hsNorm (fderiv ℝ f x) ≤ M * (‖x‖ / R) ^ α) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖f x - fderiv ℝ f x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal (A * δ) → ∀ x ∈ ball (0 : Rn n) R, ‖f x‖ ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖ := by
  have rayCS : ∀ (ℓ : ℕ) (φ φ' : ℝ → Rn ℓ) (a b : ℝ), 0 < a → a ≤ b → (∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Icc a b) → ENNReal.ofReal (‖φ b - φ a‖ ^ 2) ≤ ENNReal.ofReal (Real.log (b / a)) * ∫⁻ t in Ioo a b, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
    intro ℓ φ φ' a b ha hab hderiv hcont
    rcases hab.eq_or_lt with rfl | hab'
    · simp
    have hb : 0 < b := ha.trans hab'
    have hU : uIcc a b = Icc a b := uIcc_of_le hab
    have hpos : ∀ t ∈ Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
    have hcN : ContinuousOn (fun t => ‖φ' t‖) (Icc a b) := hcont.norm
    have hcI : ContinuousOn (fun t => t * ‖φ' t‖ ^ 2) (Icc a b) := continuousOn_id.mul (hcN.pow 2)
    have hcInv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
      continuousOn_inv₀.mono fun t ht => (hpos t ht).ne'
    have hint' : IntervalIntegrable φ' volume a b := (hU ▸ hcont).intervalIntegrable
    have hFTC : ∫ t in a..b, φ' t = φ b - φ a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [hU]) hint'
    set J := ∫ t in a..b, ‖φ' t‖ with hJdef
    set I := ∫ t in a..b, t * ‖φ' t‖ ^ 2 with hIdef
    set L := Real.log (b / a) with hLdef
    have hJ : ‖φ b - φ a‖ ≤ J := by
      rw [← hFTC]; exact intervalIntegral.norm_integral_le_integral_norm hab
    have hL : ∫ t in a..b, t⁻¹ = L := integral_inv_of_pos ha hb
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg _)
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hab (fun t ht =>
      mul_nonneg (hpos t ht).le (sq_nonneg _))
    have hLpos : 0 < L := Real.log_pos ((one_lt_div ha).mpr hab')
    have hlam : ∀ lam : ℝ, 0 < lam → 2 * lam * J ≤ lam ^ 2 * I + L := by
      intro lam hlampos
      have hmono : ∫ t in a..b, 2 * lam * ‖φ' t‖ ≤ ∫ t in a..b, (lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hU ▸ (hcN.const_smul (2 * lam))).intervalIntegrable
        · exact (hU ▸ ((hcI.const_smul (lam ^ 2)).add hcInv)).intervalIntegrable
        · intro t ht
          have ht0 := hpos t ht
          have e : lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹ - 2 * lam * ‖φ' t‖ = (lam * t * ‖φ' t‖ - 1) ^ 2 / t := by
            field_simp; ring
          have : 0 ≤ lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹ - 2 * lam * ‖φ' t‖ := by
            rw [e]; exact div_nonneg (sq_nonneg _) ht0.le
          exact sub_nonneg.mp this
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, hL] at hmono
      · exact hmono
      · exact (hU ▸ (hcI.const_smul (lam ^ 2))).intervalIntegrable
      · exact (hU ▸ hcInv).intervalIntegrable
    have hJ2 : J ^ 2 ≤ L * I := by
      rcases hI0.eq_or_lt with hI | hI
      · have hJz : J ≤ 0 := by
          by_contra h
          push Not at h
          have := hlam (L / J) (div_pos hLpos h)
          rw [← hI, mul_zero, zero_add] at this
          have e : 2 * (L / J) * J = 2 * L := by field_simp
          rw [e] at this
          linarith only [this, hLpos]
        have : J = 0 := le_antisymm hJz hJ0
        rw [this, ← hI]; simp
      · rcases hJ0.eq_or_lt with hJz | hJpos
        · rw [← hJz, sq, zero_mul]
          exact mul_nonneg hLpos.le hI.le
        obtain ⟨u, hu0, hu⟩ : ∃ u, 0 < u ∧ J = u * I :=
          ⟨J / I, div_pos hJpos hI, (div_mul_cancel₀ J hI.ne').symm⟩
        have h := hlam u hu0
        rw [hu] at h ⊢
        have h' : u ^ 2 * I ≤ L := by linarith only [h]
        calc (u * I) ^ 2 = u ^ 2 * I * I := by ring
          _ ≤ L * I := mul_le_mul_of_nonneg_right h' hI.le
    have hIlint : ENNReal.ofReal I = ∫⁻ t in Ioo a b, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
      rw [hIdef, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (hcI.integrableOn_Icc).mono_set Ioo_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have : 0 < t := ha.trans ht.1
        positivity
    calc ENNReal.ofReal (‖φ b - φ a‖ ^ 2) ≤ ENNReal.ofReal (L * I) := by
          apply ENNReal.ofReal_le_ofReal
          calc ‖φ b - φ a‖ ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hJ 2
            _ ≤ L * I := hJ2
      _ = ENNReal.ofReal L * ENNReal.ofReal I := ENNReal.ofReal_mul hLpos.le
      _ = _ := by rw [hIlint]
  have scale : ∀ (n : ℕ) (g : Rn n → ℝ≥0∞), Measurable g → ∀ t : ℝ, 0 < t →
    ∫⁻ y, g (t • y) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, g z := by
    intro n g hg t ht
    have hmap := Measure.map_addHaar_smul (volume : Measure (Rn n)) ht.ne'
    rw [finrank_euclideanSpace_fin] at hmap
    rw [← lintegral_map hg (measurable_const_smul t), hmap, lintegral_smul_measure,
      abs_of_pos (by positivity)]
    rfl
  have core : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (f : Rn n → Rn ℓ) (R r lam : ℝ) (Q : Set (Rn n)),
    0 < lam → lam ≤ 1 → 0 < r → r < R → ContDiffOn ℝ 1 f (ball 0 R) → MeasurableSet Q →
    (∀ y ∈ Q, y ≠ 0 ∧ ‖y‖ ≤ r) →
    ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) ≤
    ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
    (ENNReal.ofReal (r ^ (n + 2)) *
    ∫⁻ z in ball (0 : Rn n) R, ENNReal.ofReal (‖f z - fderiv ℝ f z z‖ ^ 2 / ‖z‖ ^ (n + 2)))) := by
    intro n ℓ hn f R r lam Q hlam hlam1 hr hrR hfC hQ hQy
    set G : Rn n → ℝ := fun y => ‖f y - fderiv ℝ f y y‖ ^ 2 / ‖y‖ ^ (n + 2) with hG
    set g : Rn n → ℝ≥0∞ := (ball (0 : Rn n) R).indicator (fun y => ENNReal.ofReal (G y)) with hg
    have hfc : ContinuousOn f (ball 0 R) := hfC.continuousOn
    have hDc : ContinuousOn (fderiv ℝ f) (ball 0 R) := hfC.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
    have hGc : ContinuousOn (fun y => ENNReal.ofReal (G y)) (ball (0 : Rn n) R \ {0}) := by
      apply ENNReal.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · exact ((hfc.mono sdiff_subset).sub ((hDc.mono sdiff_subset).clm_apply continuousOn_id)).norm.pow 2
      · exact (continuous_norm.pow _).continuousOn
      · intro y hy; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hy.2)
    have hG0 : G 0 = 0 := by simp [hG]
    have hgm : Measurable g := by
      classical
      have : g = (ball (0 : Rn n) R \ {0}).piecewise (fun y => ENNReal.ofReal (G y)) 0 := by
        ext y
        by_cases hy : y ∈ ball (0 : Rn n) R
        · by_cases hy0 : y = 0
          · subst hy0; simp [hg, hy, hG0]
          · simp [hg, hy, hy0, Set.piecewise]
        · simp [hg, hy, Set.piecewise]
      rw [this]
      exact hGc.measurable_piecewise continuousOn_const (measurableSet_ball.diff (measurableSet_singleton 0))
    have hL0 : 0 ≤ Real.log (1 / lam) := Real.log_nonneg (one_le_one_div hlam hlam1)
    have hray : ∀ y ∈ Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) ≤
        ENNReal.ofReal (Real.log (1 / lam)) *
          ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
      intro y hy
      obtain ⟨hy0, hyr⟩ := hQy y hy
      have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 → t • y ∈ ball (0 : Rn n) R := by
        intro t ht ht1
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        exact (mul_le_of_le_one_left (norm_nonneg y) ht1).trans_lt (hyr.trans_lt hrR)
      set φ : ℝ → Rn ℓ := fun t => t⁻¹ • f (t • y) with hφ
      set φ' : ℝ → Rn ℓ := fun t => t⁻¹ • (fderiv ℝ f (t • y)) y - (t ^ 2)⁻¹ • f (t • y) with hφ'
      have hderiv : ∀ t ∈ Icc lam 1, HasDerivAt φ (φ' t) t := by
        intro t ht
        have ht0 : 0 < t := hlam.trans_le ht.1
        have hfd : HasFDerivAt f (fderiv ℝ f (t • y)) (t • y) :=
          ((hfC.differentiableOn one_ne_zero).differentiableAt
            (isOpen_ball.mem_nhds (hmem t ht0 ht.2))).hasFDerivAt
        have hline : HasDerivAt (fun s : ℝ => s • y) y t := by
          simpa using (hasDerivAt_id t).smul_const y
        have hcomp : HasDerivAt (fun s => f (s • y)) (fderiv ℝ f (t • y) y) t :=
          hfd.comp_hasDerivAt t hline
        have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht0.ne'
        have h := hinv.smul hcomp
        convert h using 1
        simp only [hφ', neg_smul, sub_eq_add_neg]
      have hcont' : ContinuousOn φ' (Icc lam 1) := by
        have hpos : ∀ t ∈ Icc lam 1, t ≠ 0 := fun t ht => (hlam.trans_le ht.1).ne'
        have hin : MapsTo (fun t : ℝ => t • y) (Icc lam 1) (ball (0 : Rn n) R) :=
          fun t ht => hmem t (hlam.trans_le ht.1) ht.2
        have hlin : ContinuousOn (fun t : ℝ => t • y) (Icc lam 1) :=
          (continuous_id.smul continuous_const).continuousOn
        have hf' : ContinuousOn (fun t : ℝ => f (t • y)) (Icc lam 1) := hfc.comp hlin hin
        have hD' : ContinuousOn (fun t : ℝ => (fderiv ℝ f (t • y)) y) (Icc lam 1) :=
          (hDc.comp hlin hin).clm_apply continuousOn_const
        apply ContinuousOn.sub
        · exact (continuousOn_inv₀.mono fun t ht => hpos t ht).smul hD'
        · exact ((continuousOn_inv₀.comp (continuous_pow 2).continuousOn
            (fun t ht => pow_ne_zero 2 (hpos t ht))).smul hf')
      have hCS := rayCS ℓ φ φ' lam 1 hlam hlam1 hderiv hcont'
      have hend : φ 1 - φ lam = f y - lam⁻¹ • f (lam • y) := by simp [hφ]
      rw [hend] at hCS
      have hid : ∀ t ∈ Ioo lam 1, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) ≤
          ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
        intro t ht
        have ht0 : 0 < t := hlam.trans ht.1
        have hnorm : ‖t • y‖ = t * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        rw [hg, indicator_of_mem (hmem t ht0 ht.2.le), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        simp only [hG, hnorm]
        set L := fderiv ℝ f (t • y)
        have hL : L (t • y) = t • L y := L.map_smul t y
        have hφt : φ' t = (t ^ 2)⁻¹ • (L (t • y) - f (t • y)) := by
          simp only [hφ', hL, smul_sub, smul_smul]
          congr 1
          congr 1
          field_simp
        rw [hφt, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht0, norm_sub_rev]
        set E := ‖f (t • y) - L (t • y)‖ with hE
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have h1 : (t * ‖y‖) ^ (k + 1 + 2) ≤ (t * r) ^ (k + 1 + 2) :=
          pow_le_pow_left₀ (by positivity) (by gcongr) _
        have h2 : 0 < (t * ‖y‖) ^ (k + 1 + 2) := by positivity
        have hE0 : 0 ≤ E ^ 2 := sq_nonneg E
        calc t * ((t ^ 2)⁻¹ * E) ^ 2 = E ^ 2 * (t ^ k * r ^ (k + 1 + 2)) / (t * r) ^ (k + 1 + 2) := by
              field_simp
              ring
          _ ≤ E ^ 2 * (t ^ k * r ^ (k + 1 + 2)) / (t * ‖y‖) ^ (k + 1 + 2) :=
              div_le_div_of_nonneg_left (by positivity) h2 h1
          _ = t ^ k * r ^ (k + 1 + 2) * (E ^ 2 / (t * ‖y‖) ^ (k + 1 + 2)) := by ring
      calc ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2)
          ≤ ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
            simpa using hCS
        _ ≤ ENNReal.ofReal (Real.log (1 / lam)) *
              ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
            gcongr _ * ?_
            exact setLIntegral_mono' measurableSet_Ioo hid
    have hFm : Measurable (Function.uncurry fun (y : Rn n) (t : ℝ) =>
        ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y)) := by
      have : Measurable fun p : Rn n × ℝ => p.2 • p.1 := by fun_prop
      exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hgm.comp this)
    have hlogI : ∫⁻ t in Ioo lam 1, ENNReal.ofReal t⁻¹ = ENNReal.ofReal (Real.log (1 / lam)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlam1,
          integral_inv_of_pos hlam one_pos]
      · exact ((continuousOn_inv₀.mono fun t ht => (hlam.trans_le ht.1).ne').integrableOn_Icc).mono_set
          Ioo_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact inv_nonneg.mpr (hlam.trans ht.1).le
    calc ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2)
        ≤ ∫⁻ y in Q, ENNReal.ofReal (Real.log (1 / lam)) *
            ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) :=
          setLIntegral_mono' hQ hray
      _ = ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ y in Q,
            ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1,
            ∫⁻ y in Q, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
          rw [lintegral_lintegral_swap hFm.aemeasurable]
      _ ≤ ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1,
            ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z) := by
          gcongr _ * ?_
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ht
          have ht0 : 0 < t := hlam.trans ht.1
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * ∫⁻ y in Q, g (t • y)
              ≤ ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * ∫⁻ y, g (t • y) := by
                gcongr; exact Measure.restrict_le_self
            _ = ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * (ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, g z) := by
                rw [scale n g hgm t ht0]
            _ = ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z) := by
                rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 2
                obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
                simp only [Nat.add_sub_cancel]
                field_simp
                ring
      _ = ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
            (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z)) := by
          rw [lintegral_mul_const _ (by fun_prop), hlogI]
      _ = _ := by rw [hg, lintegral_indicator measurableSet_ball]
  have opHS : ∀ {m k : ℕ} (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A := by
    intro m k A
    have hS : 0 ≤ hsNormSq A := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      ext j; simp [Pi.single_apply]
    have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ := by
      conv_lhs => rw [hv]
      rw [map_sum]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, norm_smul, Real.norm_eq_abs]
    have h2 : ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ ≤
        Real.sqrt (∑ i, |v i| ^ 2) * Real.sqrt (∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have h3 : Real.sqrt (∑ i, |v i| ^ 2) = ‖v‖ := by
      rw [EuclideanSpace.norm_eq]; simp [sq_abs]
    calc ‖A v‖ ≤ _ := h1
      _ ≤ _ := h2
      _ = hsNorm A * ‖v‖ := by rw [h3, mul_comm]; rfl
  have small : ∀ (n ℓ : ℕ) (α M R : ℝ) (f : Rn n → Rn ℓ), 0 < α → 0 ≤ M → 0 < R → f 0 = 0 → ContDiffOn ℝ 1 f (ball 0 R) → (∀ x ∈ ball (0 : Rn n) R, hsNorm (fderiv ℝ f x) ≤ M * (‖x‖ / R) ^ α) → ∀ x ∈ ball (0 : Rn n) R, ‖f x‖ ≤ M * (‖x‖ / R) ^ α * ‖x‖ := by
    intro n ℓ α M R f hα hM hR hf0 hfC hDf x hx
    have hxR : ‖x‖ < R := by simpa using hx
    have hK : closedBall (0 : Rn n) ‖x‖ ⊆ ball (0 : Rn n) R := closedBall_subset_ball hxR
    have hdiff : ∀ y ∈ closedBall (0 : Rn n) ‖x‖, DifferentiableAt ℝ f y := by
      intro y hy
      exact (hfC.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (hK hy))
    have hbound : ∀ y ∈ closedBall (0 : Rn n) ‖x‖, ‖fderiv ℝ f y‖ ≤ M * (‖x‖ / R) ^ α := by
      intro y hy
      have hy' : ‖y‖ ≤ ‖x‖ := by simpa using hy
      calc ‖fderiv ℝ f y‖ ≤ hsNorm (fderiv ℝ f y) := opHS _
        _ ≤ M * (‖y‖ / R) ^ α := hDf y (hK hy)
        _ ≤ M * (‖x‖ / R) ^ α := by
            gcongr
    have hxK : x ∈ closedBall (0 : Rn n) ‖x‖ := mem_closedBall_zero_iff.mpr le_rfl
    have h := (convex_closedBall (0 : Rn n) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (mem_closedBall_self (norm_nonneg x)) hxK
    simpa [hf0] using h
  have logrem : ∀ (n : ℕ), 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2)) ≤ 64 * δ ^ (1 / (2 * (n : ℝ) + 2)) := by
    intro n hn δ hδ hδ1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hL0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1)
    have hq : 0 < δ ^ (-(1 / 8) : ℝ) := Real.rpow_pos_of_pos hδ _
    have hL8 : Real.log (1 / δ) ≤ 8 * δ ^ (-(1 / 8) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hq
      rw [Real.log_rpow hδ, one_div, Real.log_inv] at *
      linarith
    have hsq : Real.log (1 / δ) ^ 2 ≤ 64 * δ ^ (-(1 / 4) : ℝ) := by
      have e : δ ^ (-(1 / 4) : ℝ) = (δ ^ (-(1 / 8) : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num
      rw [e]
      calc Real.log (1 / δ) ^ 2 ≤ (8 * δ ^ (-(1 / 8) : ℝ)) ^ 2 := pow_le_pow_left₀ hL0 hL8 2
        _ = 64 * (δ ^ (-(1 / 8) : ℝ)) ^ 2 := by ring
    have hprod : δ * Real.log (1 / δ) ^ 2 ≤ 64 * δ ^ (3 / 4 : ℝ) := by
      have e : δ ^ (3 / 4 : ℝ) = δ * δ ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_one_add' hδ.le (by norm_num)]; norm_num
      rw [e]
      calc δ * Real.log (1 / δ) ^ 2 ≤ δ * (64 * δ ^ (-(1 / 4) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsq hδ.le
        _ = 64 * (δ * δ ^ (-(1 / 4) : ℝ)) := by ring
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    calc (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2))
        ≤ (64 * δ ^ (3 / 4 : ℝ)) ^ (1 / ((n : ℝ) + 2)) :=
          Real.rpow_le_rpow (by positivity) hprod hp.le
      _ = 64 ^ (1 / ((n : ℝ) + 2)) * δ ^ ((3 / 4 : ℝ) * (1 / ((n : ℝ) + 2))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le]
      _ ≤ 64 * δ ^ (1 / (2 * (n : ℝ) + 2)) := by
          have h64 : (64 : ℝ) ^ (1 / ((n : ℝ) + 2)) ≤ 64 := by
            calc (64 : ℝ) ^ (1 / ((n : ℝ) + 2)) ≤ 64 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num)
                    (by rw [div_le_one (by positivity)]; linarith)
              _ = 64 := Real.rpow_one 64
          have hexp : 1 / (2 * (n : ℝ) + 2) ≤ (3 / 4 : ℝ) * (1 / ((n : ℝ) + 2)) := by
            rw [div_le_iff₀ (by positivity)]
            field_simp
            linarith
          have hd : δ ^ ((3 / 4 : ℝ) * (1 / ((n : ℝ) + 2))) ≤ δ ^ (1 / (2 * (n : ℝ) + 2)) :=
            Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
          exact mul_le_mul h64 hd (by positivity) (by norm_num)
  have arith : ∀ (n : ℕ), 1 ≤ n → ∀ (m r V α A δ L : ℝ), 0 < m → 0 < r → 0 < V → 0 < α → 0 ≤ A → 0 < δ → δ ≤ 1 → 0 ≤ L → L ≤ (1 / α) * Real.log (1 / δ) → m ^ 2 / 4 * ((m / 8) ^ n * V) ≤ L * (L * (r ^ (n + 2) * (A * δ))) → m ≤ 64 * (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) * δ ^ (1 / (2 * (n : ℝ) + 2)) * r := by
    intro n hn m r V α A δ L hm hr hV hα hA hδ hδ1 hL0 hLle hreal
    have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1)
    have hL2 : L * L ≤ ((1 / α) * Real.log (1 / δ)) * ((1 / α) * Real.log (1 / δ)) :=
      mul_le_mul hLle hLle hL0 (le_trans hL0 hLle)
    have hc : 0 < V / (4 * 8 ^ n) := by positivity
    have h3 : m ^ (n + 2) * (V / (4 * 8 ^ n)) ≤
        ((1 / α) * Real.log (1 / δ)) * ((1 / α) * Real.log (1 / δ)) * (r ^ (n + 2) * (A * δ)) := by
      have e1 : m ^ 2 / 4 * ((m / 8) ^ n * V) = m ^ (n + 2) * (V / (4 * 8 ^ n)) := by
        rw [div_pow, pow_add]; ring
      rw [← e1]
      calc m ^ 2 / 4 * ((m / 8) ^ n * V) ≤ L * (L * (r ^ (n + 2) * (A * δ))) := hreal
        _ = (L * L) * (r ^ (n + 2) * (A * δ)) := by ring
        _ ≤ _ := by gcongr
    have hB0 : 0 ≤ 4 * 8 ^ n * A / (V * α ^ 2) := by positivity
    have hX0 : 0 ≤ δ * Real.log (1 / δ) ^ 2 := by positivity
    have hmpow : m ^ (n + 2) ≤ (4 * 8 ^ n * A / (V * α ^ 2)) * (δ * Real.log (1 / δ) ^ 2) * r ^ (n + 2) := by
      have h4 := (le_div_iff₀ hc).mpr h3
      calc m ^ (n + 2) ≤ _ := h4
        _ = _ := by field_simp
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hroot : ∀ z : ℝ, 0 ≤ z → z = (z ^ (n + 2)) ^ (1 / ((n : ℝ) + 2)) := by
      intro z hz
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
      push_cast
      rw [mul_one_div_cancel hn2.ne', Real.rpow_one]
    have hmle : m ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) *
        (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2)) * r := by
      rw [hroot m hm.le, hroot r hr.le, ← Real.mul_rpow hB0 hX0,
        ← Real.mul_rpow (mul_nonneg hB0 hX0) (pow_nonneg hr.le _)]
      exact Real.rpow_le_rpow (pow_nonneg hm.le _) hmpow (one_div_pos.mpr hn2).le
    have hK0 : 0 ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) := Real.rpow_nonneg hB0 _
    calc m ≤ _ := hmle
      _ ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) *
            (64 * δ ^ (1 / (2 * (n : ℝ) + 2))) * r := by
          gcongr; exact logrem n hn δ hδ hδ1
      _ = _ := by ring
  have ballgeom : ∀ (n : ℕ) (x : Rn n) (τ : ℝ), 0 < τ → τ ≤ ‖x‖ / 2 → ∀ y ∈ ball ((1 - τ / (2 * ‖x‖)) • x) (τ / 2), y ≠ 0 ∧ ‖y‖ ≤ ‖x‖ ∧ ‖y - x‖ < τ := by
    intro n x τ hτ hτr y hy
    have hr0 : 0 < ‖x‖ := by linarith only [hτ, hτr]
    have hcoef : 0 ≤ 1 - τ / (2 * ‖x‖) := by
      rw [sub_nonneg, div_le_one (mul_pos two_pos hr0)]; linarith only [hτr, hr0]
    have hcn : ‖(1 - τ / (2 * ‖x‖)) • x‖ = ‖x‖ - τ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]; field_simp
    have hcx : ‖(1 - τ / (2 * ‖x‖)) • x - x‖ = τ / 2 := by
      have hdiff : (1 - τ / (2 * ‖x‖)) • x - x = (-(τ / (2 * ‖x‖))) • x := by
        rw [sub_smul, one_smul, neg_smul]; abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]; field_simp
    rw [mem_ball, dist_eq_norm] at hy
    set c := (1 - τ / (2 * ‖x‖)) • x with hc
    have h1 : ‖y‖ ≤ ‖c‖ + ‖y - c‖ := by
      calc ‖y‖ = ‖c + (y - c)‖ := by rw [add_sub_cancel]
        _ ≤ ‖c‖ + ‖y - c‖ := norm_add_le _ _
    have h2 : ‖c‖ ≤ ‖y‖ + ‖y - c‖ := by
      calc ‖c‖ = ‖y - (y - c)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖ + ‖y - c‖ := norm_sub_le _ _
    have h3 : ‖y - x‖ ≤ ‖y - c‖ + ‖c - x‖ := by
      calc ‖y - x‖ = ‖(y - c) + (c - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - c‖ + ‖c - x‖ := norm_add_le _ _
    have hypos : 0 < ‖y‖ := by linarith only [h2, hcn, hy, hτr, hτ]
    exact ⟨norm_pos_iff.mp hypos, by linarith only [h1, hcn, hy], by linarith only [h3, hy, hcx]⟩
  have lip : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (R lam : ℝ), LipschitzOnWith 1 f (ball 0 R) → 0 < lam → lam ≤ 1 → ∀ y ∈ ball (0 : Rn n) R, ∀ y' ∈ ball (0 : Rn n) R, ‖(f y - lam⁻¹ • f (lam • y)) - (f y' - lam⁻¹ • f (lam • y'))‖ ≤ 2 * ‖y - y'‖ := by
    intro n ℓ f R lam hfL hlam0 hlam1 y hy y' hy'
    have hlamball : ∀ z ∈ ball (0 : Rn n) R, lam • z ∈ ball (0 : Rn n) R := by
      intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      exact (mul_le_of_le_one_left (norm_nonneg z) hlam1).trans_lt hz
    have e1 : ‖f y - f y'‖ ≤ ‖y - y'‖ := by
      have := hfL.dist_le_mul y hy y' hy'
      simpa [dist_eq_norm] using this
    have e2 : ‖f (lam • y) - f (lam • y')‖ ≤ lam * ‖y - y'‖ := by
      have := hfL.dist_le_mul _ (hlamball y hy) _ (hlamball y' hy')
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos hlam0] at this
      simpa using this
    have hsplit : (f y - lam⁻¹ • f (lam • y)) - (f y' - lam⁻¹ • f (lam • y')) =
        (f y - f y') - lam⁻¹ • (f (lam • y) - f (lam • y')) := by
      rw [smul_sub]; abel
    rw [hsplit]
    calc ‖(f y - f y') - lam⁻¹ • (f (lam • y) - f (lam • y'))‖
        ≤ ‖f y - f y'‖ + ‖lam⁻¹ • (f (lam • y) - f (lam • y'))‖ := norm_sub_le _ _
      _ = ‖f y - f y'‖ + lam⁻¹ * ‖f (lam • y) - f (lam • y')‖ := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
      _ ≤ ‖y - y'‖ + lam⁻¹ * (lam * ‖y - y'‖) := by gcongr
      _ = 2 * ‖y - y'‖ := by field_simp; ring
  intro n ℓ hn α M A hα hα1 hM hA
  have hnt : Nontrivial (Rn n) := by
    rw [← Module.finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]; omega
  set V : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hV
  have hVtop : volume (ball (0 : Rn n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hVpos : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : Rn n) one_pos).ne' hVtop
  set K : ℝ := (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg (by norm_num) n)) hA) (mul_nonneg hVpos.le (sq_nonneg α))) _
  refine ⟨M + 64 * K, add_nonneg hM (mul_nonneg (by norm_num) hK0), ?_⟩
  intro f R δ hR hδ hδ1 hf0 hfC hfL hDf hI x hx
  set e : ℝ := 1 / (2 * (n : ℝ) + 2) with he
  have hδe : δ ≤ δ ^ e := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ e := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
          (div_le_one_of_le₀ (by linarith only [hn0]) (by linarith only [hn0]))
  have hδe0 : 0 ≤ δ ^ e := Real.rpow_nonneg hδ.le _
  have hsmall := small n ℓ α M R f hα hM hR hf0 hfC hDf
  have hlin : ∀ y ∈ ball (0 : Rn n) R, ‖f y‖ ≤ ‖y‖ := by
    intro y hy
    have := hfL.dist_le_mul y hy 0 (mem_ball_self hR)
    simpa [hf0, dist_eq_norm] using this
  by_cases hx0 : x = 0
  · subst hx0; simp [hf0]
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  set r₁ : ℝ := δ ^ (1 / α) * R with hr₁
  have hr₁0 : 0 < r₁ := mul_pos (Real.rpow_pos_of_pos hδ _) hR
  have hr₁R' : (r₁ / R) ^ α = δ := by
    rw [hr₁, mul_div_assoc, div_self hR.ne', mul_one, ← Real.rpow_mul hδ.le, one_div,
      inv_mul_cancel₀ hα.ne', Real.rpow_one]
  by_cases hcase : ‖x‖ ≤ r₁
  · have h2 : (‖x‖ / R) ^ α ≤ δ := by
      rw [← hr₁R']
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hcase hR.le) hα.le
    calc ‖f x‖ ≤ M * (‖x‖ / R) ^ α * ‖x‖ := hsmall x hx
      _ ≤ M * δ ^ e * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2.trans hδe) hM) (norm_nonneg x)
      _ ≤ (M + 64 * K) * δ ^ e * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (mul_nonneg (by norm_num) hK0)) hδe0) (norm_nonneg x)
  push Not at hcase
  set lam : ℝ := r₁ / ‖x‖ with hlam
  have hlam0 : 0 < lam := div_pos hr₁0 hr0
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hr0]; exact hcase.le
  have hlamn : ‖lam • x‖ = r₁ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hlam, div_mul_cancel₀ _ hr0.ne']
  have hlamx : lam • x ∈ ball (0 : Rn n) R := by
    rw [mem_ball_zero_iff, hlamn]; exact hcase.trans hrR
  have hW : ‖lam⁻¹ • f (lam • x)‖ ≤ M * δ * ‖x‖ := by
    have h := hsmall (lam • x) hlamx
    rw [hlamn, hr₁R'] at h
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
    calc lam⁻¹ * ‖f (lam • x)‖ ≤ lam⁻¹ * (M * δ * r₁) := by gcongr
      _ = M * δ * ‖x‖ := by rw [hlam]; field_simp
  have hW1 : ‖lam⁻¹ • f (lam • x)‖ ≤ ‖x‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
    calc lam⁻¹ * ‖f (lam • x)‖ ≤ lam⁻¹ * ‖lam • x‖ := by gcongr; exact hlin _ hlamx
      _ = ‖x‖ := by rw [hlamn, hlam]; field_simp
  set m : ℝ := ‖f x - lam⁻¹ • f (lam • x)‖ with hm
  have hfx : ‖f x‖ ≤ m + M * δ * ‖x‖ := by
    calc ‖f x‖ = ‖(f x - lam⁻¹ • f (lam • x)) + lam⁻¹ • f (lam • x)‖ := by rw [sub_add_cancel]
      _ ≤ m + ‖lam⁻¹ • f (lam • x)‖ := norm_add_le _ _
      _ ≤ m + M * δ * ‖x‖ := add_le_add le_rfl hW
  have hmain : m ≤ 64 * K * δ ^ e * ‖x‖ := by
    rcases (norm_nonneg (f x - lam⁻¹ • f (lam • x))).eq_or_lt with hmz | hmpos
    · rw [hm, ← hmz]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hδe0) (norm_nonneg x)
    rw [← hm] at hmpos
    have hm2 : m ≤ 2 * ‖x‖ := by
      calc m ≤ ‖f x‖ + ‖lam⁻¹ • f (lam • x)‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := add_le_add (hlin x hx) hW1
        _ = 2 * ‖x‖ := by ring
    set Q : Set (Rn n) := ball ((1 - m / 4 / (2 * ‖x‖)) • x) (m / 4 / 2) with hQ
    have hQy := ballgeom n x (m / 4) (div_pos hmpos (by norm_num)) (by linarith only [hm2])
    have hQR : ∀ y ∈ Q, y ∈ ball (0 : Rn n) R := by
      intro y hy
      rw [mem_ball_zero_iff]
      exact (hQy y hy).2.1.trans_lt hrR
    have hlow : ∀ y ∈ Q, ENNReal.ofReal (m ^ 2 / 4) ≤
        ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) := by
      intro y hy
      have hL := lip n ℓ f R lam hfL hlam0 hlam1 x hx y (hQR y hy)
      have hrev := norm_sub_norm_le (f x - lam⁻¹ • f (lam • x)) (f y - lam⁻¹ • f (lam • y))
      have hyx : ‖x - y‖ < m / 4 := by rw [norm_sub_rev]; exact (hQy y hy).2.2
      have h1 : m / 2 ≤ ‖f y - lam⁻¹ • f (lam • y)‖ := by rw [hm]; linarith
      apply ENNReal.ofReal_le_ofReal
      calc m ^ 2 / 4 = (m / 2) ^ 2 := by ring
        _ ≤ ‖f y - lam⁻¹ • f (lam • y)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have hvolQ : volume Q = ENNReal.ofReal ((m / 8) ^ n) * volume (ball (0 : Rn n) 1) := by
      rw [hQ, Measure.addHaar_ball volume _ (div_nonneg (div_nonneg hmpos.le (by norm_num))
          (by norm_num) : (0 : ℝ) ≤ m / 4 / 2), finrank_euclideanSpace_fin]
      congr 2; ring
    have hup := core n ℓ hn f R ‖x‖ lam Q hlam0 hlam1 hr0 hrR hfC measurableSet_ball
      (fun y hy => ⟨(hQy y hy).1, (hQy y hy).2.1⟩)
    have hL0 : 0 ≤ Real.log (1 / lam) := Real.log_nonneg (one_le_one_div hlam0 hlam1)
    have hLle : Real.log (1 / lam) ≤ (1 / α) * Real.log (1 / δ) := by
      have h1 : Real.log (1 / lam) ≤ Real.log (R / r₁) := by
        apply Real.log_le_log (one_div_pos.mpr hlam0)
        rw [hlam, one_div_div]
        exact div_le_div_of_nonneg_right hrR.le hr₁0.le
      have h2 : R / r₁ = (1 / δ) ^ (1 / α) := by
        rw [hr₁, Real.div_rpow zero_le_one hδ.le, Real.one_rpow]
        field_simp
      rw [h2, Real.log_rpow (one_div_pos.mpr hδ)] at h1
      exact h1
    have hchain : ENNReal.ofReal (m ^ 2 / 4 * ((m / 8) ^ n * V)) ≤
        ENNReal.ofReal (Real.log (1 / lam) * (Real.log (1 / lam) * (‖x‖ ^ (n + 2) * (A * δ)))) := by
      calc ENNReal.ofReal (m ^ 2 / 4 * ((m / 8) ^ n * V))
          = ENNReal.ofReal (m ^ 2 / 4) * volume Q := by
            rw [hvolQ, ENNReal.ofReal_mul (div_nonneg (sq_nonneg m) (by norm_num)),
              ENNReal.ofReal_mul (pow_nonneg (div_nonneg hmpos.le (by norm_num)) n), hV,
              ENNReal.ofReal_toReal hVtop]
        _ = ∫⁻ y in Q, ENNReal.ofReal (m ^ 2 / 4) := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) :=
            setLIntegral_mono' measurableSet_ball hlow
        _ ≤ _ := hup
        _ ≤ ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
              (ENNReal.ofReal (‖x‖ ^ (n + 2)) * ENNReal.ofReal (A * δ))) := by gcongr
        _ = _ := by
            rw [← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg x) _), ← ENNReal.ofReal_mul hL0,
              ← ENNReal.ofReal_mul hL0]
    have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL0 (mul_nonneg hL0
      (mul_nonneg (pow_nonneg (norm_nonneg x) _) (mul_nonneg hA hδ.le))))).mp hchain
    have := arith n hn m ‖x‖ V α A δ (Real.log (1 / lam)) hmpos hr0 hVpos hα hA hδ hδ1 hL0 hLle hreal
    exact this
  calc ‖f x‖ ≤ m + M * δ * ‖x‖ := hfx
    _ ≤ 64 * K * δ ^ e * ‖x‖ + M * δ ^ e * ‖x‖ :=
        add_le_add hmain (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδe hM) (norm_nonneg x))
    _ = (M + 64 * K) * δ ^ e * ‖x‖ := by ring

end Submission

end GMT.Ch05
