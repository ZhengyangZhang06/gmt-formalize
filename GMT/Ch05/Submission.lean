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
/-- **Lemma A** of the tilt-excess decay (Simon Ch. 5, Lemma 2.1, p. 107, with an `L¹` curvature
term): if `spt V ∩ B_r(z)` lies within height `h` of `z + T`, `dim T = n`, then
`∫_{B_{r/2}(z)} |p_{T_x M} − p_T|² dμ_V ≤ 144 r⁻² ∫_{B_r(z)} dist(x − z, T)² dμ_V
  + 4h ∫_{B_r(z)} |H| dμ_V`.  Test the first variation with `X = ζ² p_{T⊥}(x − z)`, where
`ζ(x) = φ(|x − z|/r)`; then `div_M X = ζ² |p_x − p_T|²/2 + 2ζ ∇ζ · (p_x − p_T) x'` a.e., and the
cross term is absorbed by Young's inequality. -/
theorem ted_lemma_a_tilt_height : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → closedBall z r ⊆ U → 0 ≤ h → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ 144 * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH hmeas hae z r h hr hBU hh T hT hht
  -- Step 1: the cutoff `ζ(x) = φ(|x - z|/r)` from the reused profile and gradient lemmas.
  obtain ⟨φ, hφs, hφ01, hφ1, hφ0, hφL⟩ := Submission.exists_smooth_step_profile_lipschitz_three
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : Amb n ℓ → ℝ, ζ = fun x => φ (‖x - z‖ / r) := ⟨_, rfl⟩
  have hζs : ContDiff ℝ (⊤ : ℕ∞) ζ := by
    rw [hζdef]
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x = z
    · subst hx
      have hev : (fun y => φ (‖y - x‖ / r)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
        apply hφ1
        rw [mem_ball, dist_eq_norm] at hy
        rw [div_le_iff₀ hr]
        linarith
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hne : x - z ≠ 0 := sub_ne_zero.2 hx
      have hnx : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Amb n ℓ => ‖y - z‖) x :=
        (contDiffAt_norm ℝ hne).comp x (contDiffAt_id.sub contDiffAt_const)
      exact hφs.contDiffAt.comp x (hnx.div_const r)
  have hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1 := fun x => by rw [hζdef]; exact hφ01 _
  have hζ1 : ∀ x ∈ closedBall z (r / 2), ζ x = 1 := fun x hx => by
    rw [hζdef]
    apply hφ1
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hr]
    linarith
  have hζ0 : ∀ x, r ≤ dist x z → ζ x = 0 := fun x hx => by
    rw [hζdef]
    apply hφ0
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hr]
    linarith
  have hζd : ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := fun x => by
    rw [hζdef]
    simpa using Submission.norm_fderiv_radial_profile_le_of_lipschitzWith (n + ℓ) z r 3 φ hr hφL x
  -- The reused projection algebra: op-norm ≤ HS-norm, |p_{T⊥} v| = dist(v, T), trace identity.
  have hopHS : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, ‖A‖ ≤ hsNorm A := fun A =>
    Submission.hsNorm_starProjection_trace_identities.1 (n + ℓ) (n + ℓ) A
  have hperp : ∀ v : Amb n ℓ, ‖Tᗮ.starProjection v‖ = infDist v (T : Set (Amb n ℓ)) :=
    fun v => Submission.hsNorm_starProjection_trace_identities.2.1 (n + ℓ) T v
  -- Notation: `g = |p_x - p_T|²`, `w = x' = p_{T⊥}(x - z)`, the cross term `b`, the field `X`.
  obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ, ∀ x, g x = hsNormSq (V.tangentProj x - T.starProjection) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → Amb n ℓ, ∀ x, w x = Tᗮ.starProjection (x - z) :=
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
    rw [show w = fun x => Tᗮ.starProjection (x - z) from funext hw]
    fun_prop
  have hXcont : Continuous X := by
    rw [show X = fun x => ζ x ^ 2 • w x from funext hX]
    exact (hζcont.pow 2).smul hwcont
  have hζout : ∀ x, x ∉ closedBall z r → ζ x = 0 := fun x hx =>
    hζ0 x (not_le.1 fun hle => hx (mem_closedBall.2 hle)).le
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
  -- `μ_V(B_r(z)) < ∞` (integrability of `θ` on compact subsets of `U`).
  have hμB : V.weight (closedBall z r) < ∞ := by
    have hint := V.integrableOn_mult (closedBall z r) (isCompact_closedBall z r) hBU
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hint.lintegral_lt_top
  have : IsFiniteMeasure (V.weight.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.2 hμB.ne
  -- `μ_V`-a.e. point lies in `spt V = U ∩ spt μ_V`.
  have hsupp : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
    have h2 : ∀ᵐ x ∂V.weight, x ∈ U := by
      have hac : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
        withDensity_absolutelyContinuous _ _
      exact hac.ae_le ((ae_restrict_mem₀ V.nullMeasurableSet_carrier).mono
        fun x hx => V.carrier_subset hx)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx2, hx1⟩
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
  -- Integrability on `B_r(z)`.
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
    by_contra hcon
    exact hx (hXout x hcon)
  -- Step 3: `div_M X = ζ² |p_x - p_T|²/2 + 2ζ ∇ζ · (p_x - p_T) x'` at a.e. point.
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = 1 / 2 * (ζ x ^ 2 * g x) + b x := by
    filter_upwards [hae] with x hx
    obtain ⟨P, hP, hPx⟩ := hx
    rw [show X = fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z) from funext fun y => by
      rw [hX, hw]]
    -- `DX(x) = ζ(x)² p_{T⊥} + (2ζ(x) Dζ(x)).smulRight x'`; trace against `p_x = p_P`.
    have hζx : DifferentiableAt ℝ ζ x := hζC1.differentiable one_ne_zero x
    have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
      simpa using hζx.hasFDerivAt.pow 2
    have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - z)) Tᗮ.starProjection x :=
      (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have hXd := hsq.fun_smul hlin
    have hx' : T.starProjection (Tᗮ.starProjection (x - z)) = 0 :=
      (T.starProjection_apply_eq_zero_iff).mpr (Tᗮ.starProjection_apply_mem _)
    have htr : LinearMap.trace ℝ (Amb n ℓ)
        (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
          hsNormSq (P.starProjection - T.starProjection) / 2 :=
      Submission.hsNorm_starProjection_trace_identities.2.2 (n + ℓ) P T (hP.trans hT.symm)
    have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - z))).toLinearMap ∘ₗ
        P.starProjection.toLinearMap =
          (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
            (Tᗮ.starProjection (x - z)) := by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
    rw [RectifiableVarifold.divM, hXd.fderiv, hPx, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
      map_smul, htr, LinearMap.trace_smulRight, hg, hb, hw, hPx]
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, smul_apply,
      smul_eq_mul, sub_apply, hx', sub_zero]
    ring
  -- Step 5: the first variation identity, localized to `B_r(z)`.
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
  -- Step 6: absorb the cross term (Young), and bound the curvature term by the height.
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
  have hXH_bd : ∀ᵐ x ∂(V.weight.restrict (closedBall z r)),
      -inner ℝ (X x) (H x) ≤ h * ‖H x‖ := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
      with x hxs hxB
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    have hwh : ‖w x‖ ≤ h := by rw [hw, hperp]; exact hht x ⟨hxs, hxB⟩
    refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * h := mul_le_mul hz2 hwh (norm_nonneg _) zero_le_one
      _ = h := one_mul _
  have e1 : ∫ x in closedBall z r, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight =
      1 / 2 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        ∫ x in closedBall z r, b x ∂V.weight := by
    rw [integral_add (hzg.const_mul _) hbi, integral_const_mul]
  have e2 : -∫ x in closedBall z r, b x ∂V.weight ≤
      1 / 4 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        36 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight := by
    have hle := integral_mono hbi.neg ((hzg.const_mul (1 / 4)).add (hh2.const_mul (36 / r ^ 2)))
      hb_bd
    simp only [Pi.neg_apply, Pi.add_apply] at hle
    rwa [integral_neg, integral_add (hzg.const_mul _) (hh2.const_mul _), integral_const_mul,
      integral_const_mul] at hle
  have e3 : -∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight ≤
      h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    have hle := integral_mono_ae hXH.neg (hHint.norm.const_mul h) hXH_bd
    simp only [Pi.neg_apply] at hle
    rwa [integral_neg, integral_const_mul] at hle
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
  -- Step 7: `ζ = 1` on `B_{r/2}(z)`, then rescale.
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
  have hgoal : ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight =
      ∫ x in closedBall z (r / 2), g x ∂V.weight := by
    congr 1
    funext x
    rw [hg]
  rw [hgoal, hId, show (144 : ℝ) * (r ^ 2)⁻¹ = 144 / r ^ 2 by ring]
  exact hB2.trans key
/-- **Simon Ch. 3, Theorem 1.9 and Remark 1.8** for a rectifiable varifold `V = v(M, θ)` (fact (F1)
of the proof of Remark 5.3): for `μ_V`-a.e. `x` the weighted approximate tangent space of `M` with
respect to `θ` exists, is `n`-dimensional and has projection `V.tangentProj x`; `V.tangentProj` is
`μ_V`-a.e. strongly measurable; and `Θⁿ(μ_V, x) = θ(x)` `μ_V`-a.e.  Proof: `lgc_tangent_plane_ae`
gives the weighted tangent space `T` with `V.tangentProj x = p_T` and the measurability, and
`allard52_tangent_ae` gives an `n`-dimensional `P` with `V.tangentProj x = p_P` and the density.
Then `p_T = p_P`, so `T = P`: a subspace is the fixed-point set of its orthogonal projection. -/
theorem any_radius_tangent_ae : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P ∧ V.tangentProj x = P.starProjection) ∧ AEStronglyMeasurable V.tangentProj V.weight ∧ ∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x) := by
  intro n ℓ hn U hU V
  obtain ⟨hmeas, htan⟩ := lgc_tangent_plane_ae n ℓ hn U hU V
  obtain ⟨-, hdim, hdens⟩ := allard52_tangent_ae n ℓ hn U hU V
  refine ⟨?_, hmeas, hdens⟩
  filter_upwards [htan, hdim] with x ⟨T, hT, hTx⟩ ⟨P, hP, hPx⟩
  have hTP : T = P := by
    ext v
    rw [← Submodule.starProjection_eq_self_iff, ← Submodule.starProjection_eq_self_iff, ← hTx, hPx]
  subst hTP
  exact ⟨T, hP, hT, hTx⟩
/-- **Lemma A** of the any-radius Allard theorem (Simon Ch. 5, Lemma 2.1, p. 107, with an `L¹`
curvature term): if `spt V ∩ B_r(z)` lies within height `h` of `z + T`, `dim T = n`, then
`∫_{B_{r/2}(z)} |p_{T_x M} − p_T|² dμ_V ≤ 144 r⁻² ∫_{B_r(z)} dist(x − z, T)² dμ_V
  + 4h ∫_{B_r(z)} |H| dμ_V`.  By `allard52_tangent_ae`, `x ↦ p_x` is `μ_V`-a.e. strongly
measurable and `μ_V`-a.e. the projection onto an `n`-plane; the cutoff test field
`X = ζ² p_{T⊥}(x − z)`, the first variation and Young absorption are `ted_lemma_a_tilt_height`. -/
theorem any_radius_tilt_height_l1 : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → 0 ≤ h → closedBall z r ⊆ U → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ 144 * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH z r h hr hh hBU T hT hht
  -- Step 0 (child `tangent_ae`): `p_x` is `μ_V`-a.e. strongly measurable and `μ_V`-a.e. the
  -- orthogonal projection onto an `n`-dimensional subspace.
  obtain ⟨hmeas, hae, -⟩ := Submission.allard52_tangent_ae n ℓ hn U hU V
  -- Steps 1–6: cutoff `ζ = φ(|x − z|/r)`, test field `X = ζ² p_{T⊥}(x − z)`, `div_M X`, first
  -- variation, Young absorption, `ζ = 1` on `B_{r/2}(z)` and `|x'| ≤ h` `μ_V`-a.e. on `B_r(z)`.
  exact Submission.ted_lemma_a_tilt_height n ℓ hn U hU V H hH hmeas hae z r h hr hBU hh T hT hht
/-- **Radial height bound for general radii** (Simon Ch. 5, Remark 5.3; step 7(b) of the proof of
`AllardRegularityAnyRadius`).  There is `C = C(n) > 0`, independent of `ℓ`, such that if
`0 < r₁ < R`, `u` is `C¹` on `B̆_R(0)` with `u(0) = 0`, `‖Du‖ ≤ 1` there, `|u(x)| ≤ ε|x|` for
`|x| < r₁`, and `∫_{B̆_R(0)} |u(x) − Du(x)x|²/|x|^{n+2} dx ≤ m`, then
`|u(x)| ≤ (ε + C (log(R/r₁) m)^{1/(n+1)}) |x|` on `B̆_R(0)`.

Proof: `W(t, w) = u(tw)/t` satisfies `t |∂ₜW|² = g(tw) tⁿ⁻¹` with
`g(x) = |u(x) − Du(x)x|²/|x|^{n+2}`, so by the fundamental theorem of calculus and Cauchy–Schwarz
`D = W(r, ·) − W(r₁, ·)` has `|D(w)|² ≤ log(R/r₁) ∫ g(sy) sⁿ⁻¹ ds` along the ray through any `y`
in the shell `1/2 ≤ |y| ≤ 1` with direction `w`.  Integrating over the shell, Tonelli and the
scaling `y ↦ sy` (Jacobian `sⁿ`) give `∫_{shell} |D(y/|y|)|² ≤ log(R/r₁) m` (this replaces polar
coordinates).  `D` is `2`-Lipschitz on the sphere, and the shell points whose directions lie
within `t ≤ 1/2` of a unit vector have volume `≥ c tⁿ⁻¹` (they contain a box), so
`|D| ≤ C (log(R/r₁) m)^{1/(n+1)}`; finally `|W(r₁, ·)| ≤ ε` by continuity. -/
theorem any_radius_radial_height : ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u : Rn n → Rn ℓ) (R r₁ ε m : ℝ), 0 < r₁ → r₁ < R → 0 ≤ ε → 0 ≤ m → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ 1) → (∀ x ∈ ball (0 : Rn n) r₁, ‖u x‖ ≤ ε * ‖x‖) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal m → ∀ x ∈ ball (0 : Rn n) R, ‖u x‖ ≤ (ε + C * (Real.log (R / r₁) * m) ^ (1 / ((n : ℝ) + 1))) * ‖x‖ := by
  intro n hn
  -- Step 1 (cap estimate): the shell points `1/2 ≤ |x| ≤ 1` whose direction is within `t ≤ 1/2`
  -- of a unit vector `w₀` have volume `≥ c tⁿ⁻¹`: they contain a box of that volume.
  obtain ⟨c, hc, hcap⟩ : ∃ c : ℝ, 0 < c ∧ ∀ (w₀ : Rn n), ‖w₀‖ = 1 → ∀ (t : ℝ), 0 < t →
      t ≤ 1 / 2 → ENNReal.ofReal (c * t ^ (n - 1)) ≤
        volume {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    set N : ℝ := ((k + 1 : ℕ) : ℝ) with hN
    have hN1 : (1 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    refine ⟨1 / (4 * (4 * N) ^ k), by positivity, ?_⟩
    intro w₀ hw₀ t ht ht2
    rw [Nat.add_sub_cancel]
    set s : ℝ := t / (8 * N) with hs
    have hs0 : 0 < s := by positivity
    set e : Rn (k + 1) := EuclideanSpace.single 0 1 with he
    have he1 : ‖e‖ = 1 := by simp [he]
    set α : Fin (k + 1) → ℝ := Fin.cons (5/8 : ℝ) (fun _ : Fin k => -s) with hα
    set β : Fin (k + 1) → ℝ := Fin.cons (7/8 : ℝ) (fun _ : Fin k => s) with hβ
    set P : Set (Rn (k + 1)) := (WithLp.ofLp : Rn (k + 1) → (Fin (k + 1) → ℝ)) ⁻¹' (Icc α β)
      with hP
    have hPmeas : MeasurableSet P :=
      measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin (k + 1))).measurable
    -- the box `P` (around `(3/4) e`) lies in the sector around `e`
    have hPsub : ∀ x ∈ P, 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - e‖ < t := by
      intro x hx
      have hx' : α ≤ WithLp.ofLp x ∧ WithLp.ofLp x ≤ β := hx
      have h0 : 5/8 ≤ x 0 ∧ x 0 ≤ 7/8 := by
        have h1 := hx'.1 0
        have h2 := hx'.2 0
        simp only [hα, hβ, Fin.cons_zero] at h1 h2
        exact ⟨h1, h2⟩
      have hi : ∀ i : Fin k, |x i.succ| ≤ s := by
        intro i
        have h1 := hx'.1 i.succ
        have h2 := hx'.2 i.succ
        simp only [hα, hβ, Fin.cons_succ] at h1 h2
        exact abs_le.mpr ⟨h1, h2⟩
      set a := x 0 with ha
      set q := ∑ i : Fin k, (x i.succ) ^ 2 with hq
      have hnorm2 : ‖x‖ ^ 2 = a ^ 2 + q := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hqle : q ≤ t ^ 2 / 64 := by
        calc q ≤ ∑ _i : Fin k, s ^ 2 := Finset.sum_le_sum (fun i _ => by
                have h := hi i
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) h 2)
          _ = k * s ^ 2 := by simp
          _ ≤ N * s ^ 2 := by
                gcongr
                rw [hN]; push_cast; linarith
          _ = t ^ 2 / (64 * N) := by rw [hs]; field_simp; ring
          _ ≤ t ^ 2 / 64 := by
                apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
                linarith
      have ht2' : t ^ 2 ≤ 1 / 4 := (pow_le_pow_left₀ ht.le ht2 2).trans_eq (by norm_num)
      have hρa : a ≤ ‖x‖ := by
        have : a ^ 2 ≤ ‖x‖ ^ 2 := by rw [hnorm2]; linarith
        exact (sq_le_sq₀ (by linarith [h0.1]) (norm_nonneg x)).mp this
      have hρ0 : 0 < ‖x‖ := by linarith [h0.1]
      have hρ1 : ‖x‖ ≤ 1 := by
        have h7 : a ^ 2 ≤ 49 / 64 :=
          (pow_le_pow_left₀ (by linarith [h0.1]) h0.2 2).trans_eq (by norm_num)
        have hx2 : ‖x‖ ^ 2 ≤ 1 := by rw [hnorm2]; linarith
        exact (pow_le_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).mp hx2
      have hinner : @inner ℝ _ _ x e = a := by
        rw [he, EuclideanSpace.inner_single_right]; simp [ha]
      have hkey : ‖‖x‖⁻¹ • x - e‖ ^ 2 = 2 * (‖x‖ - a) / ‖x‖ := by
        rw [@norm_sub_sq_real, norm_smul, real_inner_smul_left, hinner, he1,
          Real.norm_eq_abs, abs_inv, abs_norm]
        field_simp
        ring
      have hlt : ‖‖x‖⁻¹ • x - e‖ ^ 2 < t ^ 2 := by
        rw [hkey, div_lt_iff₀ hρ0]
        have h1 : (‖x‖ - a) * (‖x‖ + a) = q := by linear_combination hnorm2
        have h2 : (‖x‖ - a) * (5/4) ≤ q := by
          rw [← h1]; exact mul_le_mul_of_nonneg_left (by linarith [h0.1]) (by linarith)
        have h5 : t ^ 2 * (5/8) ≤ t ^ 2 * ‖x‖ :=
          mul_le_mul_of_nonneg_left (by linarith [h0.1]) (sq_nonneg t)
        have h6 : 0 < t ^ 2 := by positivity
        linarith
      refine ⟨by linarith [h0.1], hρ1, ?_⟩
      exact lt_of_pow_lt_pow_left₀ 2 ht.le hlt
    -- the volume of the box
    have hvolP : volume P = ENNReal.ofReal (1 / (4 * (4 * N) ^ k) * t ^ k) := by
      rw [hP, (PiLp.volume_preserving_ofLp (Fin (k + 1))).measure_preimage
        measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Fin.prod_univ_succ]
      simp only [hα, hβ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      have hN0 : N ≠ 0 := (by linarith : (0:ℝ) < N).ne'
      rw [hs, show t / (8 * N) - -(t / (8 * N)) = t / (4 * N) by ring, div_pow, mul_pow]
      field_simp
      ring
    -- a reflection takes `w₀` to `e` and preserves volume
    set T : Rn (k + 1) ≃ₗᵢ[ℝ] Rn (k + 1) :=
      (Submodule.span ℝ {w₀ - e})ᗮ.reflection with hT
    have hTw : T w₀ = e := Submodule.reflection_sub (by rw [hw₀, he1])
    have hsub : T ⁻¹' P ⊆
        {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hPsub (T x) hx
      have hnT : ‖T x‖ = ‖x‖ := T.norm_map x
      rw [hnT] at h1 h2 h3
      refine ⟨h1, h2, ?_⟩
      have hmap : T (‖x‖⁻¹ • x - w₀) = ‖x‖⁻¹ • T x - e := by
        rw [map_sub, map_smul, hTw]
      rw [← T.norm_map, hmap]
      exact h3
    calc ENNReal.ofReal (1 / (4 * (4 * N) ^ k) * t ^ k) = volume P := hvolP.symm
      _ = volume (T ⁻¹' P) :=
          ((T.measurePreserving).measure_preimage hPmeas.nullMeasurableSet).symm
      _ ≤ _ := measure_mono hsub
  -- Step 2 (the constant `C = C(n)`): a `2`-Lipschitz `D` with `|D| ≤ 2` on the unit sphere and
  -- `∫_{shell} |D(x/|x|)|² ≤ m₁` satisfies `|D| ≤ C m₁^{1/(n+1)}` (`|D| ≥ M/2` on a cap).
  obtain ⟨C, hC, hsup⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (D : Rn n → Rn ℓ) (m₁ : ℝ), 0 ≤ m₁ →
      (∀ w w' : Rn n, ‖w‖ = 1 → ‖w'‖ = 1 → ‖D w - D w'‖ ≤ 2 * ‖w - w'‖) →
      (∀ w : Rn n, ‖w‖ = 1 → ‖D w‖ ≤ 2) →
      ∫⁻ x in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) ≤
        ENNReal.ofReal m₁ →
      ∀ w : Rn n, ‖w‖ = 1 → ‖D w‖ ≤ C * m₁ ^ (1 / ((n : ℝ) + 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    set C : ℝ := max (((4 : ℝ) ^ (k + 1) / c) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1))) 1 with hCdef
    refine ⟨C, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro ℓ D m₁ hm₁ hLip hb hint w₀ hw₀
    have hpowm : 0 ≤ m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := Real.rpow_nonneg hm₁ _
    rcases eq_or_lt_of_le (norm_nonneg (D w₀)) with hM0 | hMpos
    · rw [← hM0]
      exact mul_nonneg (lt_of_lt_of_le one_pos (le_max_right _ _)).le hpowm
    set M := ‖D w₀‖ with hM
    set t : ℝ := M / 4 with ht
    have ht0 : 0 < t := by positivity
    have hM2 : M ≤ 2 := hb w₀ hw₀
    have hthalf : t ≤ 1 / 2 := by rw [ht]; linarith
    set A : Set (Rn (k + 1)) := {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} with hA
    set K : Set (Rn (k + 1)) :=
      {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} with hK
    have hKA : K ⊆ A := fun x hx => ⟨hx.1, hx.2.1⟩
    have hKmeas : MeasurableSet K := by
      have hm1 : Measurable (fun x : Rn (k + 1) => ‖‖x‖⁻¹ • x - w₀‖) := by fun_prop
      have : K = {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖} ∩ ({x : Rn (k + 1) | ‖x‖ ≤ 1} ∩
          {x : Rn (k + 1) | ‖‖x‖⁻¹ • x - w₀‖ < t}) := rfl
      rw [this]
      exact (measurableSet_le measurable_const measurable_norm).inter
        ((measurableSet_le measurable_norm measurable_const).inter
          (measurableSet_lt hm1 measurable_const))
    have hlow : ∀ x ∈ K, ENNReal.ofReal ((M / 2) ^ 2) ≤ ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := by
      intro x hx
      have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx.1
      have hxn : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hx0.ne']
      have h1 : ‖D w₀ - D (‖x‖⁻¹ • x)‖ ≤ 2 * ‖w₀ - ‖x‖⁻¹ • x‖ := hLip _ _ hw₀ hxn
      have h2 : ‖w₀ - ‖x‖⁻¹ • x‖ < t := by rw [norm_sub_rev]; exact hx.2.2
      have h3 : M ≤ ‖D (‖x‖⁻¹ • x)‖ + ‖D w₀ - D (‖x‖⁻¹ • x)‖ := by
        rw [hM]; linarith [norm_sub_norm_le (D w₀) (D (‖x‖⁻¹ • x))]
      have h4 : M / 2 ≤ ‖D (‖x‖⁻¹ • x)‖ := by rw [ht] at h2; linarith
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) h4 2)
    have key : ENNReal.ofReal ((M / 2) ^ 2) * ENNReal.ofReal (c * t ^ (k + 1 - 1)) ≤
        ENNReal.ofReal m₁ :=
      calc ENNReal.ofReal ((M / 2) ^ 2) * ENNReal.ofReal (c * t ^ (k + 1 - 1))
          ≤ ENNReal.ofReal ((M / 2) ^ 2) * volume K := by
            gcongr
            exact hcap w₀ hw₀ t ht0 hthalf
        _ = ∫⁻ _ in K, ENNReal.ofReal ((M / 2) ^ 2) := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in K, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := setLIntegral_mono' hKmeas hlow
        _ ≤ ∫⁻ x in A, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := lintegral_mono_set hKA
        _ ≤ ENNReal.ofReal m₁ := hint
    have key' : (M / 2) ^ 2 * (c * t ^ (k + 1 - 1)) ≤ m₁ := by
      rw [← ENNReal.ofReal_mul (by positivity)] at key
      exact (ENNReal.ofReal_le_ofReal_iff hm₁).mp key
    have key2 : M ^ (k + 2) ≤ (4 : ℝ) ^ (k + 1) / c * m₁ := by
      have heq : (M / 2) ^ 2 * (c * t ^ (k + 1 - 1)) = c * M ^ (k + 2) / (4 : ℝ) ^ (k + 1) := by
        rw [ht, Nat.add_sub_cancel, div_pow, div_pow, pow_succ (4 : ℝ) k]
        field_simp
        ring
      rw [heq] at key'
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h4 : (0 : ℝ) < 4 ^ (k + 1) := by positivity
      rw [div_le_iff₀ h4] at key'
      linarith
    have hexp : (1 / (((k + 1 : ℕ) : ℝ) + 1)) = 1 / ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    have hMle : M ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
      rw [hexp]
      have hM0 : 0 ≤ M := norm_nonneg _
      calc M = (M ^ (k + 2)) ^ (1 / ((k + 2 : ℕ) : ℝ)) := by
            rw [one_div, Real.pow_rpow_inv_natCast hM0 (by omega)]
        _ ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / ((k + 2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (by positivity) key2 (by positivity)
    calc M ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := hMle
      _ = ((4 : ℝ) ^ (k + 1) / c) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) *
            m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) :=
          Real.mul_rpow (by positivity) hm₁
      _ ≤ C * m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
          gcongr
          exact le_max_left _ _
  -- Step 3 (radial integration, replacing polar coordinates): for measurable `h ≥ 0`,
  -- `∫_{shell} ∫_0^∞ h(sy) sⁿ⁻¹ ds dy ≤ ∫ h`, by Tonelli and the scaling `y ↦ sy`, since
  -- `∫_{|z|}^{2|z|} ds/s ≤ 1`.
  have hpolar : ∀ h : Rn n → ℝ≥0∞, Measurable h →
      ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
          ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) ≤ ∫⁻ z, h z := by
    intro h hh
    have hfin : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
    have hAm : MeasurableSet {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
      (measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    have hm1 : Measurable (Function.uncurry fun (y : Rn n) (s : ℝ) =>
        h (s • y) * ENNReal.ofReal (s ^ (n - 1))) :=
      (hh.comp (measurable_snd.smul measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _))
    have hm2 : Measurable (Function.uncurry fun (s : ℝ) (z : Rn n) =>
        ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) := by
      have hset : MeasurableSet {p : ℝ × Rn n | p.1 / 2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ p.1} :=
        (measurableSet_le (measurable_fst.div_const 2) measurable_snd.norm).inter
          (measurableSet_le measurable_snd.norm measurable_fst)
      have heq : (Function.uncurry fun (s : ℝ) (z : Rn n) =>
          ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) =
          fun p : ℝ × Rn n => ENNReal.ofReal p.1⁻¹ *
            {p : ℝ × Rn n | p.1 / 2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ p.1}.indicator (fun p => h p.2) p := by
        funext p
        rfl
      rw [heq]
      exact (ENNReal.measurable_ofReal.comp measurable_fst.inv).mul
        ((hh.comp measurable_snd).indicator hset)
    -- the inner integral over the shell, rescaled by `s`
    have hscale : ∀ s ∈ Ioi (0:ℝ), ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
        h (s • y) * ENNReal.ofReal (s ^ (n - 1)) =
          ∫⁻ z, ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z := by
      intro s hs
      have hs0 : (0:ℝ) < s := hs
      have hBm : MeasurableSet {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} :=
        (measurableSet_le measurable_const measurable_norm).inter
          (measurableSet_le measurable_norm measurable_const)
      have hGm : Measurable ({z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h) :=
        hh.indicator hBm
      have hind : ∀ y : Rn n,
          {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}.indicator (fun y => h (s • y)) y =
            {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h (s • y) := by
        intro y
        have hn : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
        by_cases hy : 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 1
        · have hsy : s / 2 ≤ ‖s • y‖ ∧ ‖s • y‖ ≤ s := by
            rw [hn]
            exact ⟨by linarith [mul_le_mul_of_nonneg_left hy.1 hs0.le],
              mul_le_of_le_one_right hs0.le hy.2⟩
          rw [Set.indicator_of_mem (show y ∈ {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} from hy),
            Set.indicator_of_mem (show s • y ∈ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsy)]
        · have hsy : ¬ (s / 2 ≤ ‖s • y‖ ∧ ‖s • y‖ ≤ s) := by
            rw [hn]
            rintro ⟨h1, h2⟩
            exact hy ⟨le_of_mul_le_mul_left (by linarith : s * (1 / 2) ≤ s * ‖y‖) hs0,
              le_of_mul_le_mul_left (by linarith : s * ‖y‖ ≤ s * 1) hs0⟩
          rw [Set.indicator_of_notMem (show y ∉ {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} from hy),
            Set.indicator_of_notMem (show s • y ∉ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsy)]
      have hconst : ENNReal.ofReal (s ^ (n - 1)) * ENNReal.ofReal |(s ^ n)⁻¹| =
          ENNReal.ofReal s⁻¹ := by
        rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
          ← pow_sub_one_mul (by omega : n ≠ 0) s, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
      calc ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, h (s • y) * ENNReal.ofReal (s ^ (n - 1))
          = ENNReal.ofReal (s ^ (n - 1)) *
              ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, h (s • y) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
        _ = ENNReal.ofReal (s ^ (n - 1)) *
              ∫⁻ y, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h (s • y) := by
            rw [← lintegral_indicator hAm, lintegral_congr hind]
        _ = ENNReal.ofReal (s ^ (n - 1)) * ∫⁻ z, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z
              ∂(Measure.map (fun y : Rn n => s • y) volume) := by
            rw [lintegral_map hGm (measurable_const_smul s)]
        _ = ENNReal.ofReal (s ^ (n - 1)) * (ENNReal.ofReal |(s ^ n)⁻¹| *
              ∫⁻ z, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) := by
            rw [Measure.map_addHaar_smul volume hs0.ne', hfin, lintegral_smul_measure, smul_eq_mul]
        _ = ∫⁻ z, ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z := by
            rw [← mul_assoc, hconst, lintegral_const_mul _ hGm]
    rw [lintegral_lintegral_swap hm1.aemeasurable, setLIntegral_congr_fun measurableSet_Ioi hscale,
      lintegral_lintegral_swap hm2.aemeasurable]
    apply lintegral_mono
    intro z
    calc ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z
        ≤ ∫⁻ s in Ioi (0:ℝ), (Icc ‖z‖ (2 * ‖z‖)).indicator
            (fun _ => ENNReal.ofReal ‖z‖⁻¹ * h z) s := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro s hs
          by_cases hsz : s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s
          · have hs0 : (0:ℝ) < s := hs
            have hz0 : 0 < ‖z‖ := by linarith [hsz.1]
            rw [Set.indicator_of_mem (show z ∈ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsz),
              Set.indicator_of_mem (show s ∈ Icc ‖z‖ (2 * ‖z‖) from ⟨hsz.2, by linarith [hsz.1]⟩)]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ hz0 hsz.2)) _
          · rw [Set.indicator_of_notMem (show z ∉ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsz),
              mul_zero]
            exact zero_le
      _ ≤ ∫⁻ s, (Icc ‖z‖ (2 * ‖z‖)).indicator (fun _ => ENNReal.ofReal ‖z‖⁻¹ * h z) s :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal ‖z‖⁻¹ * h z * volume (Icc ‖z‖ (2 * ‖z‖)) :=
          lintegral_indicator_const measurableSet_Icc _
      _ = h z * ENNReal.ofReal (‖z‖⁻¹ * ‖z‖) := by
          rw [Real.volume_Icc, show 2 * ‖z‖ - ‖z‖ = ‖z‖ by ring, mul_comm (ENNReal.ofReal _) (h z),
            mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg z))]
      _ ≤ h z * 1 := by
          gcongr
          rw [ENNReal.ofReal_le_one]
          rcases eq_or_ne ‖z‖ 0 with hz | hz
          · rw [hz]; norm_num
          · rw [inv_mul_cancel₀ hz]
      _ = h z := mul_one _
  refine ⟨C, hC, ?_⟩
  intro ℓ u R r₁ ε m hr₁ hr₁R hε hm hu hu0 hDu hnear hint x hx
  have hR : 0 < R := hr₁.trans hr₁R
  set L : ℝ := Real.log (R / r₁) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hr₁]; linarith)
  have hLm : 0 ≤ L * m := mul_nonneg hL0 hm
  have hCpow : 0 ≤ C * (L * m) ^ (1 / ((n : ℝ) + 1)) :=
    mul_nonneg hC.le (Real.rpow_nonneg hLm _)
  have hcont : ContinuousOn u (ball (0 : Rn n) R) := hu.continuousOn
  -- Step 4 (near zero): `|u(y)| ≤ ε|y|` also on the sphere `|y| = r₁`, by continuity.
  have hbd : ∀ y : Rn n, ‖y‖ = r₁ → ‖u y‖ ≤ ε * ‖y‖ := by
    intro y hy
    have hyR : y ∈ ball (0 : Rn n) R := by
      rw [mem_ball, dist_zero_right, hy]; exact hr₁R
    have hcl : y ∈ closure (ball (0 : Rn n) r₁) := by
      rw [closure_ball (0 : Rn n) hr₁.ne', mem_closedBall, dist_zero_right, hy]
    have hca : ContinuousAt u y := hcont.continuousAt (isOpen_ball.mem_nhds hyR)
    exact ContinuousWithinAt.closure_le hcl
      (continuous_norm.continuousAt.comp hca).continuousWithinAt
      (continuousAt_const.mul continuous_norm.continuousAt).continuousWithinAt hnear
  have hxR : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hx
  rcases lt_or_ge ‖x‖ r₁ with hxr | hxr
  · exact (hnear x (by simpa [mem_ball, dist_zero_right] using hxr)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpow) (norm_nonneg x))
  rcases eq_or_lt_of_le hxr with hxr | hxr
  · exact (hbd x hxr.symm).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpow) (norm_nonneg x))
  -- main case `r₁ < |x| < R`
  set r : ℝ := ‖x‖ with hr
  have hr0 : 0 < r := hr₁.trans hxr
  -- Step 5 (Lipschitz bounds): `W(t, ·) = u(t ·)/t` is `1`-Lipschitz on the sphere, `|W| ≤ 1`.
  have hdiff : ∀ z ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hz)
  have hfd : ContinuousOn (fderiv ℝ u) (ball (0 : Rn n) R) :=
    hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hmv : ∀ y ∈ ball (0 : Rn n) R, ∀ z ∈ ball (0 : Rn n) R, ‖u y - u z‖ ≤ ‖y - z‖ := by
    intro y hy z hz
    have := (convex_ball (0 : Rn n) R).norm_image_sub_le_of_norm_fderiv_le hdiff hDu hz hy
    simpa using this
  have hS5 : ∀ t : ℝ, 0 < t → t < R → ∀ w w' : Rn n, ‖w‖ = 1 → ‖w'‖ = 1 →
      ‖t⁻¹ • u (t • w) - t⁻¹ • u (t • w')‖ ≤ ‖w - w'‖ ∧ ‖t⁻¹ • u (t • w)‖ ≤ 1 := by
    intro t ht htR w w' hw hw'
    have hmem : ∀ v : Rn n, ‖v‖ = 1 → t • v ∈ ball (0 : Rn n) R := by
      intro v hv
      rw [mem_ball, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ht]
      exact htR
    have h0 : (0 : Rn n) ∈ ball (0 : Rn n) R := mem_ball_self (ht.trans htR)
    have htinv : ‖t⁻¹‖ = t⁻¹ := by rw [Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    constructor
    · rw [← smul_sub, norm_smul, htinv]
      calc t⁻¹ * ‖u (t • w) - u (t • w')‖ ≤ t⁻¹ * ‖t • w - t • w'‖ := by
            gcongr; exact hmv _ (hmem w hw) _ (hmem w' hw')
        _ = ‖w - w'‖ := by
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← mul_assoc,
              inv_mul_cancel₀ ht.ne', one_mul]
    · rw [norm_smul, htinv]
      calc t⁻¹ * ‖u (t • w)‖ = t⁻¹ * ‖u (t • w) - u 0‖ := by rw [hu0, sub_zero]
        _ ≤ t⁻¹ * ‖t • w - 0‖ := by gcongr; exact hmv _ (hmem w hw) _ h0
        _ = 1 := by
            rw [sub_zero, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos ht,
              inv_mul_cancel₀ ht.ne']
  set w : Rn n := r⁻¹ • x with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, inv_mul_cancel₀ hr0.ne']
  have hxw : x = r • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  set D : Rn n → Rn ℓ := fun v => r⁻¹ • u (r • v) - r₁⁻¹ • u (r₁ • v) with hD
  have hLip : ∀ v v' : Rn n, ‖v‖ = 1 → ‖v'‖ = 1 → ‖D v - D v'‖ ≤ 2 * ‖v - v'‖ := by
    intro v v' hv hv'
    have h1 := (hS5 r hr0 hxR v v' hv hv').1
    have h2 := (hS5 r₁ hr₁ hr₁R v v' hv hv').1
    calc ‖D v - D v'‖ = ‖(r⁻¹ • u (r • v) - r⁻¹ • u (r • v')) -
          (r₁⁻¹ • u (r₁ • v) - r₁⁻¹ • u (r₁ • v'))‖ := by
          congr 1; simp only [hD]; abel
      _ ≤ ‖r⁻¹ • u (r • v) - r⁻¹ • u (r • v')‖ + ‖r₁⁻¹ • u (r₁ • v) - r₁⁻¹ • u (r₁ • v')‖ :=
          norm_sub_le _ _
      _ ≤ 2 * ‖v - v'‖ := by linarith
  have hDb : ∀ v : Rn n, ‖v‖ = 1 → ‖D v‖ ≤ 2 := by
    intro v hv
    have h1 := (hS5 r hr0 hxR v v hv hv).2
    have h2 := (hS5 r₁ hr₁ hr₁R v v hv hv).2
    calc ‖D v‖ ≤ ‖r⁻¹ • u (r • v)‖ + ‖r₁⁻¹ • u (r₁ • v)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  set A : Set (Rn n) := {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} with hA
  have hAmeas : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  set g : Rn n → ℝ := fun z => ‖u z - fderiv ℝ u z z‖ ^ 2 / ‖z‖ ^ (n + 2) with hg
  set Ω : Set (Rn n) := ball (0 : Rn n) R \ {0} with hΩ
  classical
  set h : Rn n → ℝ≥0∞ := Ω.indicator (fun z => ENNReal.ofReal (g z)) with hh
  have hgcont : ContinuousOn g Ω := by
    have hsub : Ω ⊆ ball (0 : Rn n) R := sdiff_subset
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((hcont.mono hsub).sub ((hfd.mono hsub).clm_apply continuousOn_id)).norm.pow 2
    · exact (continuous_norm.pow _).continuousOn
    · intro z hz
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz.2)
  have hΩmeas : MeasurableSet Ω := measurableSet_ball.diff (measurableSet_singleton 0)
  have hhmeas : Measurable h := by
    have := ContinuousOn.measurable_piecewise (f := fun z => ENNReal.ofReal (g z))
      (g := fun _ => (0 : ℝ≥0∞)) (s := Ω)
      (ENNReal.continuous_ofReal.comp_continuousOn hgcont) continuousOn_const hΩmeas
    have heq : h = Ω.piecewise (fun z => ENNReal.ofReal (g z)) (fun _ => (0 : ℝ≥0∞)) := by
      ext z
      by_cases hz : z ∈ Ω <;> simp [hh, hz, Set.piecewise]
    rw [heq]
    exact this
  -- Step 6 (radial Cauchy–Schwarz along the ray through `y` in the shell, `ρ = |y|`):
  -- `|D(y/ρ)|² ≤ log(R/r₁) ∫_0^∞ h(sy) sⁿ⁻¹ ds`.
  have hpt : ∀ y ∈ A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2) ≤
      ENNReal.ofReal L * ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
    intro y hy
    have hρ0 : 0 < ‖y‖ := lt_of_lt_of_le (by norm_num) hy.1
    have hρ1 : ‖y‖ ≤ 1 := hy.2
    set ρ : ℝ := ‖y‖ with hρ
    set a : ℝ := r₁ / ρ with ha
    set b : ℝ := r / ρ with hb
    have ha0 : 0 < a := div_pos hr₁ hρ0
    have hab : a < b := div_lt_div_of_pos_right hxr hρ0
    have hab' : a ≤ b := hab.le
    have hpos : ∀ s ∈ Icc a b, 0 < s := fun s hs => ha0.trans_le hs.1
    have hnsy : ∀ s : ℝ, 0 < s → ‖s • y‖ = s * ρ := fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hmaps : MapsTo (fun s : ℝ => s • y) (Icc a b) (ball (0 : Rn n) R) := by
      intro s hs
      rw [mem_ball, dist_zero_right, hnsy s (hpos s hs)]
      calc s * ρ ≤ b * ρ := mul_le_mul_of_nonneg_right hs.2 hρ0.le
        _ = r := div_mul_cancel₀ r hρ0.ne'
        _ < R := hxR
    set V' : ℝ → Rn ℓ :=
      fun s => ρ⁻¹ • ((s ^ 2)⁻¹ • (fderiv ℝ u (s • y) (s • y) - u (s • y))) with hV'
    have hderiv : ∀ s ∈ uIcc a b,
        HasDerivAt (fun τ : ℝ => ρ⁻¹ • (τ⁻¹ • u (τ • y))) (V' s) s := by
      intro s hs
      rw [uIcc_of_le hab'] at hs
      have hs0 := hpos s hs
      have h1 : HasDerivAt (fun τ : ℝ => τ • y) y s := by
        simpa using (hasDerivAt_id s).smul_const y
      have h2 : HasDerivAt (fun τ : ℝ => u (τ • y)) (fderiv ℝ u (s • y) y) s :=
        (hdiff _ (hmaps hs)).hasFDerivAt.comp_hasDerivAt s h1
      have h3 : HasDerivAt (fun τ : ℝ => τ⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hs0.ne'
      have h4 := (h3.smul h2).const_smul ρ⁻¹
      convert h4 using 1
      rw [hV']
      dsimp only
      congr 1
      rw [ContinuousLinearMap.map_smul, smul_sub, smul_smul, neg_smul, ← sub_eq_add_neg]
      congr 2
      field_simp
    have hsm : Continuous (fun s : ℝ => s • y) := continuous_id.smul continuous_const
    have hc1 : ContinuousOn (fun s : ℝ => fderiv ℝ u (s • y)) (Icc a b) :=
      hfd.comp hsm.continuousOn hmaps
    have hc2 : ContinuousOn (fun s : ℝ => u (s • y)) (Icc a b) :=
      hcont.comp hsm.continuousOn hmaps
    have hc3 : ContinuousOn (fun s : ℝ => fderiv ℝ u (s • y) (s • y)) (Icc a b) :=
      hc1.clm_apply hsm.continuousOn
    have hc4 : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Icc a b) :=
      (continuous_pow 2).continuousOn.inv₀ (fun s hs => pow_ne_zero 2 (hpos s hs).ne')
    have hcV : ContinuousOn V' (Icc a b) := (hc4.smul (hc3.sub hc2)).const_smul ρ⁻¹
    have hFTC : ∫ s in a..b, V' s = ρ⁻¹ • (b⁻¹ • u (b • y)) - ρ⁻¹ • (a⁻¹ • u (a • y)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab']; exact hcV))
    have hend : ∀ τ : ℝ, 0 < τ →
        ρ⁻¹ • ((τ / ρ)⁻¹ • u ((τ / ρ) • y)) = τ⁻¹ • u (τ • (ρ⁻¹ • y)) := by
      intro τ hτ
      rw [show (τ / ρ) • y = τ • (ρ⁻¹ • y) by rw [div_eq_mul_inv, mul_smul], smul_smul,
        show ρ⁻¹ * (τ / ρ)⁻¹ = τ⁻¹ by field_simp]
    have hDeq : D (ρ⁻¹ • y) = ∫ s in a..b, V' s := by
      rw [hFTC, ha, hb, hend r hr0, hend r₁ hr₁]
    set J := ∫ s in a..b, ‖V' s‖ with hJ
    set I := ∫ s in a..b, s * ‖V' s‖ ^ 2 with hI
    set L' := Real.log (b / a) with hL'
    have hnorm_le : ‖D (ρ⁻¹ • y)‖ ≤ J := by
      rw [hDeq]; exact intervalIntegral.norm_integral_le_integral_norm hab'
    have hLint : ∫ s in a..b, s⁻¹ = L' := integral_inv_of_pos ha0 (ha0.trans hab)
    have hL'0 : 0 < L' := Real.log_pos ((one_lt_div ha0).mpr hab)
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hab' (fun s _ => norm_nonneg _)
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hab'
      (fun s hs => mul_nonneg (hpos s hs).le (sq_nonneg _))
    have hcN : ContinuousOn (fun s => ‖V' s‖) (Icc a b) := hcV.norm
    have hcI : ContinuousOn (fun s => s * ‖V' s‖ ^ 2) (Icc a b) := continuousOn_id.mul (hcN.pow 2)
    have hcinv : ContinuousOn (fun s : ℝ => s⁻¹) (Icc a b) :=
      continuousOn_id.inv₀ (fun s hs => (hpos s hs).ne')
    -- Cauchy–Schwarz, in the form `J ≤ (λ/2) L' + I/(2λ)`
    have key : ∀ lam : ℝ, 0 < lam → J ≤ lam / 2 * L' + 1 / (2 * lam) * I := by
      intro lam hlam
      rw [← hLint]
      have hi1 : IntervalIntegrable (fun s => ‖V' s‖) volume a b :=
        ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab']; exact hcN)
      have hi2 : IntervalIntegrable (fun s : ℝ => lam / 2 * s⁻¹) volume a b :=
        ContinuousOn.intervalIntegrable
          (by rw [uIcc_of_le hab']; exact continuousOn_const.mul hcinv)
      have hi3 : IntervalIntegrable (fun s : ℝ => 1 / (2 * lam) * (s * ‖V' s‖ ^ 2)) volume a b :=
        ContinuousOn.intervalIntegrable
          (by rw [uIcc_of_le hab']; exact continuousOn_const.mul hcI)
      calc J ≤ ∫ s in a..b, (lam / 2 * s⁻¹ + 1 / (2 * lam) * (s * ‖V' s‖ ^ 2)) := by
            apply intervalIntegral.integral_mono_on hab' hi1 (hi2.add hi3)
            intro s hs
            have hs0 := hpos s hs
            set q := ‖V' s‖
            rw [show lam / 2 * s⁻¹ + 1 / (2 * lam) * (s * q ^ 2) =
                (lam ^ 2 + s ^ 2 * q ^ 2) / (2 * lam * s) by field_simp,
              le_div_iff₀ (by positivity)]
            linear_combination sq_nonneg (lam - s * q)
        _ = lam / 2 * (∫ s in a..b, s⁻¹) + 1 / (2 * lam) * I := by
            rw [intervalIntegral.integral_add hi2 hi3, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    have hJ2 : J ^ 2 ≤ L' * I := by
      rcases eq_or_lt_of_le hJ0 with hJz | hJp
      · rw [← hJz]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg hL'0.le hI0
      · have hk := key (J / L') (by positivity)
        have h1 : J / L' / 2 * L' = J / 2 := by field_simp
        have h2 : 1 / (2 * (J / L')) * I = L' * I / (2 * J) := by field_simp
        rw [h1, h2] at hk
        have h3 : J / 2 ≤ L' * I / (2 * J) := by linarith
        rw [le_div_iff₀ (by positivity)] at h3
        linear_combination h3
    have hsq : ‖D (ρ⁻¹ • y)‖ ^ 2 ≤ L' * I :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2).trans hJ2
    -- `s |∂ₛ(ρ⁻¹ u(sy)/s)|² = ρⁿ g(sy) sⁿ⁻¹ ≤ g(sy) sⁿ⁻¹`
    have hIlin : ENNReal.ofReal I ≤ ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
      rw [hI, intervalIntegral.integral_of_le hab',
        ofReal_integral_eq_lintegral_ofReal ((hcI.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
            exact mul_nonneg (ha0.trans hs.1).le (sq_nonneg _))]
      calc ∫⁻ s in Ioc a b, ENNReal.ofReal (s * ‖V' s‖ ^ 2)
          ≤ ∫⁻ s in Ioc a b, h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro s hs
            have hs0 : 0 < s := ha0.trans hs.1
            have hsΩ : s • y ∈ Ω := by
              refine ⟨hmaps ⟨hs.1.le, hs.2⟩, ?_⟩
              intro h0
              have h00 : ‖s • y‖ = 0 := by rw [Set.mem_singleton_iff.mp h0, norm_zero]
              rw [hnsy s hs0] at h00
              exact (mul_pos hs0 hρ0).ne' h00
            have hg0 : 0 ≤ g (s • y) := div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
            rw [hh, Set.indicator_of_mem hsΩ, ← ENNReal.ofReal_mul hg0]
            apply ENNReal.ofReal_le_ofReal
            show s * ‖V' s‖ ^ 2 ≤
              ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖ ^ 2 / ‖s • y‖ ^ (n + 2) * s ^ (n - 1)
            have hV'n : ‖V' s‖ =
                ρ⁻¹ * ((s ^ 2)⁻¹ * ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖) := by
              show ‖ρ⁻¹ • ((s ^ 2)⁻¹ • (fderiv ℝ u (s • y) (s • y) - u (s • y)))‖ = _
              rw [norm_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
                abs_inv, abs_of_pos hρ0, abs_of_pos (by positivity : (0:ℝ) < s ^ 2)]
            rw [hV'n, hnsy s hs0]
            set E := ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖
            have hρpow : ρ ^ (n + 2) ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
            have hspow : s ^ (n + 2) = s ^ (n - 1) * s ^ 3 := by
              rw [← pow_add]; congr 1; omega
            rw [mul_pow s ρ (n + 2), hspow]
            have hs1 : 0 < s ^ (n - 1) := pow_pos hs0 _
            calc s * (ρ⁻¹ * ((s ^ 2)⁻¹ * E)) ^ 2 = E ^ 2 / (s ^ 3 * ρ ^ 2) := by
                  field_simp
              _ ≤ E ^ 2 / (s ^ 3 * ρ ^ (n + 2)) := by
                  apply div_le_div_of_nonneg_left (sq_nonneg E) (by positivity)
                  exact mul_le_mul_of_nonneg_left hρpow (by positivity)
              _ = E ^ 2 / (s ^ (n - 1) * s ^ 3 * ρ ^ (n + 2)) * s ^ (n - 1) := by
                  field_simp
        _ ≤ _ := lintegral_mono_set (fun s (hs : s ∈ Ioc a b) => (ha0.trans hs.1 : (0:ℝ) < s))
    have hLL : L' ≤ L := by
      have hba : b / a = r / r₁ := by rw [ha, hb]; field_simp
      rw [hL', hba]
      exact Real.log_le_log (div_pos hr0 hr₁) (div_le_div_of_nonneg_right hxR.le hr₁.le)
    calc ENNReal.ofReal (‖D (ρ⁻¹ • y)‖ ^ 2) ≤ ENNReal.ofReal (L' * I) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal L' * ENNReal.ofReal I := ENNReal.ofReal_mul hL'0.le
      _ ≤ ENNReal.ofReal L * ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hLL) hIlin
  -- Step 7 (integral bound on the sphere): `∫_{shell} |D(y/|y|)|² ≤ log(R/r₁) m`.
  have henergy : ∫⁻ y in A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2) ≤ ENNReal.ofReal (L * m) := by
    calc ∫⁻ y in A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2)
        ≤ ∫⁻ y in A, ENNReal.ofReal L *
            ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          setLIntegral_mono' hAmeas hpt
      _ = ENNReal.ofReal L *
            ∫⁻ y in A, ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal L * ∫⁻ z, h z := mul_le_mul_right (hpolar h hhmeas) _
      _ = ENNReal.ofReal L * ∫⁻ z in Ω, ENNReal.ofReal (g z) := by
          rw [hh, lintegral_indicator hΩmeas]
      _ ≤ ENNReal.ofReal L * ∫⁻ z in ball (0 : Rn n) R, ENNReal.ofReal (g z) :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal m := mul_le_mul_right hint _
      _ = ENNReal.ofReal (L * m) := (ENNReal.ofReal_mul hL0).symm
  -- Step 8 (conclusion): `|u(x)|/|x| ≤ |W(r₁, w)| + |D(w)| ≤ ε + C (log(R/r₁) m)^{1/(n+1)}`.
  have hDw := hsup ℓ D (L * m) hLm hLip hDb henergy w hwn
  have hW1 : ‖r₁⁻¹ • u (r₁ • w)‖ ≤ ε := by
    have hn1 : ‖r₁ • w‖ = r₁ := by
      rw [norm_smul, hwn, mul_one, Real.norm_eq_abs, abs_of_pos hr₁]
    have hb := hbd (r₁ • w) hn1
    rw [hn1] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr₁]
    calc r₁⁻¹ * ‖u (r₁ • w)‖ ≤ r₁⁻¹ * (ε * r₁) := by gcongr
      _ = ε := by field_simp
  have hux : u x = r • (r₁⁻¹ • u (r₁ • w) + D w) := by
    simp only [hD]
    rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, ← hxw]
  calc ‖u x‖ = r * ‖r₁⁻¹ • u (r₁ • w) + D w‖ := by
        rw [hux, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    _ ≤ r * (ε + C * (L * m) ^ (1 / ((n : ℝ) + 1))) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hW1 hDw)
    _ = (ε + C * (L * m) ^ (1 / ((n : ℝ) + 1))) * r := mul_comm _ _
/-- Campanato-type Hölder estimate (proof of Simon Ch. 5, Remark 5.3, step 7(e)).  Let `g` be
continuous on `B_{r+s₀}(0)` and suppose that for `Lⁿ`-a.e. `z ∈ B_r(0)` and all `s ∈ (0, s₀]`,
`∫_{B_{s/2}(z)} |g(x) − g(z)|² dx ≤ A s^{n+2α}` (Hilbert–Schmidt norm).  Then
`|g(x) − g(y)| ≤ (2^{2n+2+2α} A / ω_n)^{1/2} |x − y|^α` for `x, y ∈ B_r(0)` with `|x − y| ≤ s₀/2`.
For good points `x₁, x₂` at distance `d`, average
`|g(x₁) − g(x₂)|² ≤ 2|g(x) − g(x₁)|² + 2|g(x) − g(x₂)|²` over `B_{d/2}(m) ⊆ B_d(x₁) ∩ B_d(x₂)`
(`m` the midpoint, `Lⁿ(B_{d/2}(m)) = ω_n (d/2)ⁿ`) and apply the hypothesis with `s = 2d`; good
points are dense in `B_r(0)` and `g` is continuous.  The ball volume is computed inline from the
Gaussian integral (`∫ e^{−|z|²} = π^{n/2} = Lⁿ(B₁) Γ(n/2 + 1)`), since
`InnerProductSpace.volume_closedBall` lies outside the frozen imports. -/
theorem any_radius_campanato : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (r s₀ A α : ℝ), 0 < r → 0 < s₀ → 0 ≤ A → 0 < α → ContinuousOn g (closedBall 0 (r + s₀)) → (∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) r)), ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (g x - g z)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → ∀ x ∈ closedBall (0 : Rn n) r, ∀ y ∈ closedBall (0 : Rn n) r, ‖x - y‖ ≤ s₀ / 2 → hsNorm (g x - g y) ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) * ‖x - y‖ ^ α := by
  -- Ball volume: `Lⁿ(B_r(x)) = ω_n rⁿ`, from `Lⁿ(B_r(x)) = rⁿ Lⁿ(B₁(0))` and the Gaussian integral.
  have h_ball_volume : ∀ (n : ℕ) (x : Rn n) (r : ℝ), 0 ≤ r → (volume : Measure (Rn n)) (closedBall x r) = ENNReal.ofReal (unitBallVolume n * r ^ n) := by
    intro n x r hr
    set V : ℝ≥0∞ := (volume : Measure (Rn n)) (ball 0 1) with hV
    have hVpos : V ≠ 0 := (measure_ball_pos volume (0 : Rn n) one_pos).ne'
    have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
    -- Gaussian integral over `ℝⁿ`: `∫ e^{-|z|²} dz = π^{n/2}`, by Fubini over the coordinates.
    have hG1 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-t ^ 2)) = ENNReal.ofReal (√Real.pi) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        have := integral_gaussian 1
        simpa using this
      · simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
      · exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
    have hGpi : ∀ m : ℕ, ∫⁻ y : Fin m → ℝ, ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ m := by
      intro m
      induction m with
      | zero =>
        simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul, pow_zero]
        rw [volume_pi, Measure.pi_univ]
        simp
      | succ m ih =>
        have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hφ : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)) := by fun_prop
        rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        rw [Measure.volume_eq_prod]
        have : ∀ z : ℝ × (Fin m → ℝ),
            ∏ i, ENNReal.ofReal (Real.exp
              (-((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm z i) ^ 2)) =
              ENNReal.ofReal (Real.exp (-z.1 ^ 2)) *
                ∏ i : Fin m, ENNReal.ofReal (Real.exp (-(z.2 i) ^ 2)) := by
          intro z
          rw [Fin.prod_univ_succ]
          simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        simp_rw [this]
        have hψ : Measurable fun y : Fin m → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) := by
          fun_prop
        rw [lintegral_prod_mul (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)))
          (g := fun y : Fin m → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)))
          hφ.aemeasurable hψ.aemeasurable, hG1, ih, pow_succ, mul_comm]
    have hGauss : ∫⁻ z : Rn n, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ n := by
      rw [← hGpi n]
      have hmeas : Measurable fun y : Fin n → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) := by
        fun_prop
      rw [← (PiLp.volume_preserving_ofLp (Fin n)).lintegral_comp hmeas]
      refine lintegral_congr fun z => ?_
      show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ∏ i, ENNReal.ofReal (Real.exp (-(WithLp.ofLp z i) ^ 2))
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
        Finset.sum_neg_distrib, EuclideanSpace.norm_sq_eq]
      congr 3
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    -- Layer-cake identity (Tonelli): `∫ e^{-|z|²} dz = V Γ(n/2 + 1)` with `V = Lⁿ(B₁(0))`.
    have hexp : ∀ c : ℝ, ENNReal.ofReal (Real.exp (-c)) =
        ∫⁻ s, (Ioi c).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s := by
      intro c
      rw [lintegral_indicator measurableSet_Ioi, ← integral_exp_neg_Ioi c,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (by simpa using exp_neg_integrableOn_Ioi c one_pos :
          IntegrableOn (fun x => Real.exp (-x)) (Ioi c) volume)
      · exact (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun s _ => (Real.exp_pos _).le)
    have hball : ∀ s : ℝ, (volume : Measure (Rn n)) {z | ‖z‖ ^ 2 < s} =
        (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (√s ^ n) * V) s := by
      intro s
      rcases le_or_gt s 0 with hs | hs
      · rw [indicator_of_notMem (by simpa using hs)]
        have : {z : Rn n | ‖z‖ ^ 2 < s} = ∅ := by
          ext z
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
          exact hs.trans (sq_nonneg _)
        rw [this, measure_empty]
      · rw [indicator_of_mem (by simpa using hs)]
        have : {z : Rn n | ‖z‖ ^ 2 < s} = ball 0 (√s) := by
          ext z
          rw [mem_ofPred_eq, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg _)]
        rw [this, Measure.addHaar_ball_of_pos _ _ (Real.sqrt_pos.2 hs), finrank_euclideanSpace_fin]
    have hTonelli : ∫⁻ z : Rn n, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * (ENNReal.ofReal (√s ^ n) * V) := by
      rw [lintegral_congr fun z : Rn n => hexp (‖z‖ ^ 2)]
      rw [lintegral_lintegral_swap]
      · rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun s => ?_
        have : ∀ z : Rn n, (Ioi (‖z‖ ^ 2)).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s =
            {z : Rn n | ‖z‖ ^ 2 < s}.indicator (fun _ => ENNReal.ofReal (Real.exp (-s))) z := by
          intro z
          by_cases h : ‖z‖ ^ 2 < s
          · rw [indicator_of_mem (show s ∈ Ioi (‖z‖ ^ 2) from h),
              indicator_of_mem (show z ∈ {z : Rn n | ‖z‖ ^ 2 < s} from h)]
          · rw [indicator_of_notMem (show s ∉ Ioi (‖z‖ ^ 2) from h),
              indicator_of_notMem (show z ∉ {z : Rn n | ‖z‖ ^ 2 < s} from h)]
        simp_rw [this]
        rw [lintegral_indicator_const (measurableSet_lt (by fun_prop) measurable_const), hball]
        by_cases hs : s ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hs, indicator_of_mem hs]
        · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]
      · apply Measurable.aemeasurable
        have : Function.uncurry (fun (z : Rn n) (s : ℝ) =>
            (Ioi (‖z‖ ^ 2)).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s) =
            {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2}.indicator (fun p => ENNReal.ofReal (Real.exp (-p.2))) := by
          ext ⟨z, s⟩
          by_cases h : ‖z‖ ^ 2 < s
          · rw [Function.uncurry_apply_pair, indicator_of_mem (show s ∈ Ioi (‖z‖ ^ 2) from h),
              indicator_of_mem (show (z, s) ∈ {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2} from h)]
          · rw [Function.uncurry_apply_pair, indicator_of_notMem (show s ∉ Ioi (‖z‖ ^ 2) from h),
              indicator_of_notMem (show (z, s) ∉ {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2} from h)]
        rw [this]
        exact (by fun_prop : Measurable fun p : Rn n × ℝ => ENNReal.ofReal (Real.exp (-p.2))).indicator
          (measurableSet_lt (by fun_prop) (by fun_prop))
    have hGamma : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * (ENNReal.ofReal (√s ^ n) * V) =
        V * ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) := by
      have hpos : (0 : ℝ) < (n : ℝ) / 2 + 1 := by positivity
      rw [Real.Gamma_eq_integral hpos, ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent hpos)]
      · rw [← lintegral_const_mul' _ _ hVtop]
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
        have h1 : √s ^ n = s ^ ((n : ℝ) / 2 + 1 - 1) := by
          rw [add_sub_cancel_right, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs0]
          ring_nf
        rw [h1, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _))
    -- Solve for `V`: `V = π^{n/2} / Γ(n/2 + 1) = ω_n`.
    have hΓpos : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hVeq : V = ENNReal.ofReal (unitBallVolume n) := by
      have h := hGauss.symm.trans (hTonelli.trans hGamma)
      -- `h : ofReal √π ^ n = V * ofReal Γ`
      have hΓne : ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) ≠ 0 := by simpa using hΓpos
      have hV' : V = ENNReal.ofReal (√Real.pi) ^ n /
          ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) :=
        (ENNReal.eq_div_iff hΓne ENNReal.ofReal_ne_top).2 (by rw [mul_comm]; exact h.symm)
      rw [hV', ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_div_of_pos hΓpos]
      congr 1
      unfold unitBallVolume
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
      ring_nf
    -- Scale: `Lⁿ(B_r(x)) = rⁿ V`.
    rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ← hV, hVeq,
      ← ENNReal.ofReal_mul (pow_nonneg hr n), mul_comm]
  -- Step 1: `|A − B|² ≤ 2|C − A|² + 2|C − B|²`, columnwise for the Hilbert–Schmidt norm.
  have h_hs_sq_le : ∀ (m k : ℕ) (A B C : Rn m →L[ℝ] Rn k), hsNormSq (A - B) ≤ 2 * hsNormSq (C - A) + 2 * hsNormSq (C - B) := by
    intro m k A B C
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    set e : Rn m := EuclideanSpace.single i (1 : ℝ)
    have h : (A - B) e = (C - B) e - (C - A) e := by
      simp only [sub_apply]
      abel
    rw [h]
    have h1 := norm_sub_le ((C - B) e) ((C - A) e)
    have h2 := norm_nonneg ((C - B) e - (C - A) e)
    nlinarith [sq_nonneg (‖(C - B) e‖ - ‖(C - A) e‖), norm_nonneg ((C - B) e),
      norm_nonneg ((C - A) e)]
  -- Step 2: a property holding a.e. on `B_r(0)` holds at points of `B_r(0)` arbitrarily close
  -- to each `x ∈ B_r(0)`, since every ball meets `B_r(0)` in a set of positive measure.
  have h_ae_dense : ∀ (n : ℕ) (r : ℝ), 0 < r → ∀ (P : Rn n → Prop), (∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) r)), P z) → ∀ x ∈ closedBall (0 : Rn n) r, ∀ ε : ℝ, 0 < ε → ∃ z ∈ closedBall (0 : Rn n) r, P z ∧ ‖z - x‖ < ε := by
    intro n r hr P hP x hx ε hε
    rw [ae_restrict_iff' measurableSet_closedBall] at hP
    set t : ℝ := min 1 (ε / (4 * r)) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htr : t * r ≤ ε / 4 := by
      have : t ≤ ε / (4 * r) := min_le_right _ _
      calc t * r ≤ ε / (4 * r) * r := mul_le_mul_of_nonneg_right this hr.le
        _ = ε / 4 := by field_simp
    set c : Rn n := (1 - t) • x with hc
    have hxr : ‖x‖ ≤ r := by simpa using hx
    have hcn : ‖c‖ ≤ (1 - t) * r := by
      rw [hc, norm_smul, Real.norm_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left hxr (by linarith)
    have hcx : ‖c - x‖ ≤ t * r := by
      have : c - x = (-t) • x := by rw [hc]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left hxr ht0.le
    have hsub : ball c (t * r) ⊆ closedBall (0 : Rn n) r ∩ ball x ε := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      constructor
      · rw [mem_closedBall, dist_zero_right]
        calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ t * r + (1 - t) * r := by linarith
          _ = r := by ring
      · rw [mem_ball, dist_eq_norm]
        calc ‖z - x‖ = ‖(z - c) + (c - x)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - c‖ + ‖c - x‖ := norm_add_le _ _
          _ < ε := by linarith
    have hpos : 0 < (volume : Measure (Rn n)) (ball c (t * r)) :=
      measure_ball_pos _ _ (by positivity)
    by_contra hcon
    push Not at hcon
    have hnull : (volume : Measure (Rn n)) (ball c (t * r)) = 0 := by
      rw [ae_iff] at hP
      refine measure_mono_null (fun z hz => ?_) hP
      obtain ⟨hz1, hz2⟩ := hsub hz
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hz1, fun hPz => ?_⟩
      have := hcon z hz1 hPz
      rw [mem_ball, dist_eq_norm] at hz2
      linarith
    exact hpos.ne' hnull
  -- Steps 3–4: the estimate for two good points at distance `d ∈ (0, s₀/2]`, by averaging over
  -- the midpoint ball `B_{d/2}(m) ⊆ B_d(x₁) ∩ B_d(x₂)` and using the hypothesis with `s = 2d`.
  have h_pair : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (r s₀ A α : ℝ), 0 ≤ A → ContinuousOn g (closedBall 0 (r + s₀)) → ∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r, 0 < ‖x₁ - x₂‖ → ‖x₁ - x₂‖ ≤ s₀ / 2 → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall x₁ (s / 2), ENNReal.ofReal (hsNormSq (g x - g x₁)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall x₂ (s / 2), ENNReal.ofReal (hsNormSq (g x - g x₂)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → hsNorm (g x₁ - g x₂) ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) * ‖x₁ - x₂‖ ^ α := by
    intro n ℓ g r s₀ A α hA hg x₁ hx₁ x₂ hx₂ hd hds h₁ h₂
    set d := ‖x₁ - x₂‖ with hd_def
    set m : Rn n := (1 / 2 : ℝ) • (x₁ + x₂) with hm
    -- the midpoint ball lies in both balls of radius d and in the big ball
    have hm1 : ‖m - x₁‖ = d / 2 := by
      have : m - x₁ = (1 / 2 : ℝ) • (x₂ - x₁) := by rw [hm]; module
      rw [this, norm_smul, norm_sub_rev, Real.norm_of_nonneg (by norm_num)]
      ring
    have hm2 : ‖m - x₂‖ = d / 2 := by
      have : m - x₂ = (1 / 2 : ℝ) • (x₁ - x₂) := by rw [hm]; module
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]
      ring
    have hB1 : closedBall m (d / 2) ⊆ closedBall x₁ d := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      calc ‖z - x₁‖ = ‖(z - m) + (m - x₁)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - m‖ + ‖m - x₁‖ := norm_add_le _ _
        _ ≤ d := by rw [hm1]; linarith
    have hB2 : closedBall m (d / 2) ⊆ closedBall x₂ d := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      calc ‖z - x₂‖ = ‖(z - m) + (m - x₂)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - m‖ + ‖m - x₂‖ := norm_add_le _ _
        _ ≤ d := by rw [hm2]; linarith
    have hBbig : closedBall m (d / 2) ⊆ closedBall 0 (r + s₀) := by
      intro z hz
      have hz1 := hB1 hz
      rw [mem_closedBall, dist_eq_norm] at hz1
      rw [mem_closedBall, dist_zero_right]
      have hx₁r : ‖x₁‖ ≤ r := by simpa using hx₁
      calc ‖z‖ = ‖(z - x₁) + x₁‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x₁‖ + ‖x₁‖ := norm_add_le _ _
        _ ≤ r + s₀ := by linarith
    -- measurability of one integrand on the midpoint ball
    have hmeas : AEMeasurable (fun y => 2 * ENNReal.ofReal (hsNormSq (g y - g x₁)))
        (volume.restrict (closedBall m (d / 2))) := by
      have hcont : ContinuousOn (fun y => hsNormSq (g y - g x₁)) (closedBall m (d / 2)) := by
        have hgB : ContinuousOn g (closedBall m (d / 2)) := hg.mono hBbig
        unfold hsNormSq
        fun_prop
      exact ((hcont.aemeasurable measurableSet_closedBall).ennreal_ofReal).const_mul 2
    -- the hypotheses at s = 2 d
    have hs : 0 < 2 * d := by positivity
    have hs' : 2 * d ≤ s₀ := by linarith
    have hI1 := h₁ (2 * d) hs hs'
    have hI2 := h₂ (2 * d) hs hs'
    rw [show 2 * d / 2 = d by ring] at hI1 hI2
    set R := A * (2 * d) ^ ((n : ℝ) + 2 * α) with hR
    have hR0 : 0 ≤ R := mul_nonneg hA (Real.rpow_nonneg hs.le _)
    -- pointwise inequality
    set Q := hsNormSq (g x₁ - g x₂) with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpt : ∀ y, ENNReal.ofReal Q ≤
        2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) + 2 * ENNReal.ofReal (hsNormSq (g y - g x₂)) := by
      intro y
      have hle := h_hs_sq_le n ℓ (g x₁) (g x₂) (g y)
      have h0a : 0 ≤ hsNormSq (g y - g x₁) := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h0b : 0 ≤ hsNormSq (g y - g x₂) := Finset.sum_nonneg fun i _ => sq_nonneg _
      calc ENNReal.ofReal Q
          ≤ ENNReal.ofReal (2 * hsNormSq (g y - g x₁) + 2 * hsNormSq (g y - g x₂)) :=
            ENNReal.ofReal_le_ofReal hle
        _ = 2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) + 2 * ENNReal.ofReal (hsNormSq (g y - g x₂)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    -- integrate over the midpoint ball
    have hint : ENNReal.ofReal Q * (volume : Measure (Rn n)) (closedBall m (d / 2)) ≤
        ENNReal.ofReal (4 * R) := by
      calc ENNReal.ofReal Q * (volume : Measure (Rn n)) (closedBall m (d / 2))
          = ∫⁻ _ in closedBall m (d / 2), ENNReal.ofReal Q := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in closedBall m (d / 2), (2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) +
              2 * ENNReal.ofReal (hsNormSq (g y - g x₂))) := lintegral_mono hpt
        _ = 2 * (∫⁻ y in closedBall m (d / 2), ENNReal.ofReal (hsNormSq (g y - g x₁))) +
              2 * (∫⁻ y in closedBall m (d / 2), ENNReal.ofReal (hsNormSq (g y - g x₂))) := by
            rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * (∫⁻ y in closedBall x₁ d, ENNReal.ofReal (hsNormSq (g y - g x₁))) +
              2 * (∫⁻ y in closedBall x₂ d, ENNReal.ofReal (hsNormSq (g y - g x₂))) := by
            have h1 := lintegral_mono_set (μ := (volume : Measure (Rn n)))
              (f := fun y => ENNReal.ofReal (hsNormSq (g y - g x₁))) hB1
            have h2 := lintegral_mono_set (μ := (volume : Measure (Rn n)))
              (f := fun y => ENNReal.ofReal (hsNormSq (g y - g x₂))) hB2
            gcongr
        _ ≤ 2 * ENNReal.ofReal R + 2 * ENNReal.ofReal R := by gcongr
        _ = ENNReal.ofReal (4 * R) := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
              show ENNReal.ofReal 4 = 4 by norm_num]
            ring
    -- volume of the midpoint ball
    have hω : 0 < unitBallVolume n :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    set W := unitBallVolume n * (d / 2) ^ n with hW
    have hW0 : 0 < W := mul_pos hω (pow_pos (by positivity) n)
    rw [h_ball_volume n m (d / 2) (by positivity), ← ENNReal.ofReal_mul hQ0,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
    -- arithmetic: Q ≤ C * d^(2α)
    set C := 2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n with hC
    have hC0 : 0 ≤ C := div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hA) hω.le
    have hkey : 4 * R = C * d ^ (2 * α) * W := by
      have e1 : (2 * d) ^ ((n : ℝ) + 2 * α) = 2 ^ ((n : ℝ) + 2 * α) * (d ^ n * d ^ (2 * α)) := by
        rw [Real.mul_rpow (by norm_num) hd.le, Real.rpow_add hd, Real.rpow_natCast]
      have e2 : (2 : ℝ) ^ (2 * (n : ℝ) + 2 + 2 * α) = 2 ^ ((n : ℝ) + 2 * α) * 2 ^ n * 4 := by
        rw [show 2 * (n : ℝ) + 2 + 2 * α = ((n : ℝ) + 2 * α) + (n : ℝ) + 2 by ring,
          Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast,
          Real.rpow_two]
        norm_num
      rw [hR, hC, hW, e1, e2, div_pow]
      field_simp
    have hQle : Q ≤ C * d ^ (2 * α) := by
      have : Q * W ≤ C * d ^ (2 * α) * W := by rw [← hkey]; exact hint
      exact le_of_mul_le_mul_right this hW0
    -- square roots
    have hsq : Real.sqrt (d ^ (2 * α)) = d ^ α := by
      rw [show 2 * α = α * 2 by ring, Real.rpow_mul hd.le, Real.rpow_two,
        Real.sqrt_sq (Real.rpow_nonneg hd.le _)]
    calc hsNorm (g x₁ - g x₂) = Real.sqrt Q := rfl
      _ ≤ Real.sqrt (C * d ^ (2 * α)) := Real.sqrt_le_sqrt hQle
      _ = Real.sqrt C * d ^ α := by rw [Real.sqrt_mul hC0, hsq]
  -- Step 5: approximate `x, y` by good points and pass to the limit using continuity of `g`.
  intro n ℓ _hn g r s₀ A α hr hs₀ hA hα hg hae x hx y hy hxy
  set K := Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  by_cases hxy0 : x = y
  · subst hxy0
    have h0 : hsNorm (g x - g x) = 0 := by simp [hsNorm, hsNormSq]
    rw [h0, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero]
  set D := ‖x - y‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hxy0)
  -- the good-point predicate
  set P : Rn n → Prop := fun z => ∀ s : ℝ, 0 < s → s ≤ s₀ →
    ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (g x - g z)) ≤
      ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α)) with hP
  -- shrinking parameters
  set η : ℕ → ℝ := fun k => (1 / 5 : ℝ) * (1 / ((k : ℝ) + 1)) with hη
  have hηpos : ∀ k, 0 < η k := fun k => by simp only [hη]; positivity
  have hηle : ∀ k, η k ≤ 1 / 5 := fun k => by
    simp only [hη]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 5 : ℝ)
    simpa [hη] using this
  -- inner points
  set xk : ℕ → Rn n := fun k => x + η k • (y - x) with hxk
  set yk : ℕ → Rn n := fun k => y + η k • (x - y) with hyk
  have hxk_mem : ∀ k, xk k ∈ closedBall (0 : Rn n) r := fun k =>
    (convex_closedBall (0 : Rn n) r).add_smul_sub_mem hx hy ⟨(hηpos k).le, by linarith [hηle k]⟩
  have hyk_mem : ∀ k, yk k ∈ closedBall (0 : Rn n) r := fun k =>
    (convex_closedBall (0 : Rn n) r).add_smul_sub_mem hy hx ⟨(hηpos k).le, by linarith [hηle k]⟩
  have hxkyk : ∀ k, ‖xk k - yk k‖ = (1 - 2 * η k) * D := fun k => by
    have : xk k - yk k = (1 - 2 * η k) • (x - y) := by
      simp only [hxk, hyk]
      module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith [hηle k])]
  have hxk_x : ∀ k, ‖xk k - x‖ = η k * D := fun k => by
    simp only [hxk, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hηpos k).le]
    rw [norm_sub_rev]
  have hyk_y : ∀ k, ‖yk k - y‖ = η k * D := fun k => by
    simp only [hyk, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hηpos k).le]
    rfl
  -- good points approximating the inner points
  have hgood : ∀ k, ∃ p : Rn n × Rn n, (p.1 ∈ closedBall (0 : Rn n) r ∧ P p.1 ∧
      ‖p.1 - xk k‖ < η k * D / 2) ∧ (p.2 ∈ closedBall (0 : Rn n) r ∧ P p.2 ∧
      ‖p.2 - yk k‖ < η k * D / 2) := by
    intro k
    have hε : 0 < η k * D / 2 := by have := hηpos k; positivity
    obtain ⟨a, ha, hPa, hax⟩ :=
      h_ae_dense n r hr P hae (xk k) (hxk_mem k) _ hε
    obtain ⟨b, hb, hPb, hby⟩ :=
      h_ae_dense n r hr P hae (yk k) (hyk_mem k) _ hε
    exact ⟨(a, b), ⟨ha, hPa, hax⟩, ⟨hb, hPb, hby⟩⟩
  choose p hp1 hp2 using hgood
  -- pair estimate at the approximants
  have hbound : ∀ k, hsNorm (g (p k).1 - g (p k).2) ≤ K * D ^ α := by
    intro k
    obtain ⟨ha, hPa, hax⟩ := hp1 k
    obtain ⟨hb, hPb, hby⟩ := hp2 k
    have hη5 := hηle k
    have hη0 := hηpos k
    have hupper : ‖(p k).1 - (p k).2‖ ≤ D := by
      have h1 : ‖(p k).1 - (p k).2‖ ≤ ‖(p k).1 - xk k‖ + ‖xk k - yk k‖ + ‖yk k - (p k).2‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub ((p k).1) (xk k) ((p k).2)
        have h2 := norm_sub_le_norm_sub_add_norm_sub (xk k) (yk k) ((p k).2)
        linarith
      rw [hxkyk k, norm_sub_rev (yk k)] at h1
      nlinarith
    have hlower : 0 < ‖(p k).1 - (p k).2‖ := by
      have h1 : ‖xk k - yk k‖ ≤ ‖xk k - (p k).1‖ + ‖(p k).1 - (p k).2‖ + ‖(p k).2 - yk k‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (xk k) ((p k).1) (yk k)
        have h2 := norm_sub_le_norm_sub_add_norm_sub ((p k).1) ((p k).2) (yk k)
        linarith
      rw [hxkyk k, norm_sub_rev (xk k)] at h1
      nlinarith
    have hpair := h_pair n ℓ g r s₀ A α hA hg (p k).1 ha (p k).2 hb hlower
      (hupper.trans hxy) hPa hPb
    refine hpair.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    exact Real.rpow_le_rpow (norm_nonneg _) hupper hα.le
  -- convergence of the approximants
  have hbig : closedBall (0 : Rn n) r ⊆ closedBall 0 (r + s₀) :=
    closedBall_subset_closedBall (by linarith)
  have hconv1 : Tendsto (fun k => (p k).1) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k => (3 / 2 * D) * η k) atTop (𝓝 0) := by
      simpa using hηlim.const_mul (3 / 2 * D)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    have := norm_sub_le_norm_sub_add_norm_sub ((p k).1) (xk k) x
    rw [hxk_x k] at this
    have := (hp1 k).2.2
    nlinarith
  have hconv2 : Tendsto (fun k => (p k).2) atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k => (3 / 2 * D) * η k) atTop (𝓝 0) := by
      simpa using hηlim.const_mul (3 / 2 * D)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    have := norm_sub_le_norm_sub_add_norm_sub ((p k).2) (yk k) y
    rw [hyk_y k] at this
    have := (hp2 k).2.2
    nlinarith
  have hgx : Tendsto (fun k => g (p k).1) atTop (𝓝 (g x)) := by
    have h1 : Tendsto (fun k => (p k).1) atTop (𝓝[closedBall 0 (r + s₀)] x) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv1
        (Eventually.of_forall fun k => hbig (hp1 k).1)
    exact (hg.continuousWithinAt (hbig hx)).tendsto.comp h1
  have hgy : Tendsto (fun k => g (p k).2) atTop (𝓝 (g y)) := by
    have h1 : Tendsto (fun k => (p k).2) atTop (𝓝[closedBall 0 (r + s₀)] y) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv2
        (Eventually.of_forall fun k => hbig (hp2 k).1)
    exact (hg.continuousWithinAt (hbig hy)).tendsto.comp h1
  have hcontN : Continuous (fun B : Rn n →L[ℝ] Rn ℓ => hsNorm B) := by
    unfold hsNorm hsNormSq
    fun_prop
  have hlimit : Tendsto (fun k => hsNorm (g (p k).1 - g (p k).2)) atTop
      (𝓝 (hsNorm (g x - g y))) :=
    (hcontN.tendsto _).comp (hgx.sub hgy)
  exact le_of_tendsto' hlimit hbound

set_option maxHeartbeats 10000000 in
/-- **Graph rate** in the any-radius Allard theorem (Simon Ch. 5, Remark 5.3; step 7 of its proof),
for a graph piece over `B̆_{γ₂ρ}(0)`.  Assume Theorems 4.5 and 6.1, `p > n`, `0 < γ₁ < γ₂ < 1`,
`0 < c₁ < γ₂`, `C₀ ≥ 0`, and put `a = 1/(2n+2)`.  If 2.3 holds with `δ ∈ (0, δ_R]`, `u` is `C¹` on
`B̆_{γ₂ρ}(0)` with `u(0) = 0`, `‖Du‖ ≤ 1/7`, `spt V ∩ B̆_{γ₂ρ}(0) = q(graph u)` and
`|u(x)| ≤ C₀ δ^a |x|` for `|x| < c₁ρ`, then on `B_{γ₁ρ}(0)`: `|u(x)| ≤ C_R δ^a |x|`,
`|Du| ≤ C_R δ^a` and `|Du(x) − Du(y)| ≤ C_R δ^a (|x − y|/ρ)^{1−n/p}`.

Proof: monotonicity bounds the conical integral by `C δ`; the height transfer turns it into the
weighted `L²` bound for `u − Du·x`, and the radial height lemma gives `|u| ≤ C_H δ^a |x|`.  Lemma A
at a graph point `ζ = q(z, u(z))` with the Hölder bound for `|H|` gives `E(ζ, c_σ ρ, T₀) ≤ C δ^{2a}`.
Translating by `ζ`, pinching verifies 2.3 at scale `c_s ρ`, and the iteration of 4.5 (whose constants
are normalised to be `≥ 1`, using `E_* ≥ 0`) gives planes `S(ζ)` with `|p_S − p_{T₀}|² ≤ C δ^{2a}` and
`E(ζ, s, S) ≤ C (s/σ)^{2(1−n/p)} δ^{2a}`.  At Lebesgue points the tangent plane of the graph is
`S(ζ)`, so (Ang) bounds `Du` a.e., hence everywhere by continuity; (Gp) and the graph comparison give
the Campanato input, and `any_radius_campanato` the Hölder bound. -/
theorem any_radius_graph_rate : TiltExcessDecayTheorem → ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ₁ γ₂ c₁ C₀ : ℝ, 0 < γ₁ → γ₁ < γ₂ → γ₂ < 1 → 0 < c₁ → c₁ < γ₂ → 0 ≤ C₀ → ∃ δR CR : ℝ, 0 < δR ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δR → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 (γ₂ * ρ)) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) (γ₂ * ρ), ‖fderiv ℝ u x‖ ≤ 1 / 7) → q '' graphOver u (ball 0 (γ₂ * ρ)) ⊆ V.support ∩ ball 0 ρ → V.support ∩ ball 0 (γ₂ * ρ) ⊆ q '' graphOver u (ball 0 (γ₂ * ρ)) → (∀ x ∈ ball (0 : Rn n) (c₁ * ρ), ‖u x‖ ≤ C₀ * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖) → (∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), ‖u x‖ ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖) ∧ (∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), hsNorm (fderiv ℝ u x) ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2))) ∧ ∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), ∀ y ∈ closedBall (0 : Rn n) (γ₁ * ρ), hsNorm (fderiv ℝ u x - fderiv ℝ u y) ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2)) * (‖x - y‖ / ρ) ^ (1 - (n : ℝ) / p) := by
  intro hTED hCAT n ℓ hn p hp γ₁ γ₂ c₁ C₀ hγ₁ hγ₁₂ hγ₂ hc₁ hc₁₂ hC₀
  /- Step 1: the constants, chosen before `U, V, H, δ, ρ, q, u`.  `a = 1/(2n+2)`,
  `β = 1 - n/p`, `K₀ = 4p/(p - n)` (so that `Λ = 4pδ/(p - n) = K₀ δ`). -/
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hpn : 0 < p - n := by linarith
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  set ω : ℝ := unitBallVolume n with hω_def
  set β : ℝ := 1 - (n : ℝ) / p with hβ_def
  have hβ0 : 0 < β := by
    have : (n : ℝ) / p < 1 := (div_lt_one hp0).2 hp
    linarith
  set a : ℝ := 1 / (2 * (n : ℝ) + 2) with ha_def
  have ha0 : 0 < a := by positivity
  have ha_le : a ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have ha2 : a * 2 ≤ 1 := by
    rw [ha_def, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have ha1 : a ≤ 1 := by linarith
  set K₀ : ℝ := 4 * p / (p - n) with hK₀_def
  have hK₀ : 0 < K₀ := by positivity
  -- Constants of the prerequisites.
  obtain ⟨δE, hδE, hGC⟩ := Submission.any_radius_graph_comparison n ℓ hn p hp
  obtain ⟨Crad, hCrad, hRH⟩ := Submission.any_radius_radial_height n hn
  -- `C_c`, `C_u`: the conical and upper density constants of step 2 (here via `e^Λ ≤ 1 + 2Λ`).
  set Cc : ℝ := 2 * (ω * (2 * K₀ + 2) + K₀) with hCc_def
  have hCc : 0 ≤ Cc := by positivity
  set Cu : ℝ := 4 * (2 / (1 - γ₂)) ^ n + 1 / ω with hCu_def
  obtain ⟨δ₆, CII₀, CIII₀, hδ₆, hTI⟩ :=
    Submission.any_radius_tilt_iteration hTED n ℓ hn p hp (1 / 2) Cu (by norm_num)
  -- Normalised constants of `tilt_iteration`.
  set CII : ℝ := max CII₀ 1 with hCII_def
  set CIII : ℝ := max CIII₀ 1 with hCIII_def
  have hCII : 1 ≤ CII := le_max_right _ _
  have hCIII : 1 ≤ CIII := le_max_right _ _
  set ε₁ : ℝ := min (1 / 4) δ₆ with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) hδ₆
  have hε₁4 : ε₁ ≤ 1 / 4 := min_le_left _ _
  have hε₁6 : ε₁ ≤ δ₆ := min_le_right _ _
  obtain ⟨δP, cs, hδP, hcs, hcs16, hPin⟩ :=
    Submission.any_radius_pinching hCAT n ℓ hn p hp γ₂ ε₁ (hγ₁.trans hγ₁₂) hγ₂ hε₁ hε₁4
  set γ' : ℝ := (γ₁ + γ₂) / 2 with hγ'_def
  have hγ'1 : γ₁ < γ' := by rw [hγ'_def]; linarith
  have hγ'2 : γ' < γ₂ := by rw [hγ'_def]; linarith
  set cr : ℝ := min ((γ₂ - γ') / 4) ((1 - γ₂) / 4) with hcr_def
  have hcr : 0 < cr := lt_min (by linarith) (by linarith)
  have hcr1 : cr ≤ (γ₂ - γ') / 4 := min_le_left _ _
  have hcr2 : cr ≤ (1 - γ₂) / 4 := min_le_right _ _
  set csig : ℝ := min (cr / 2) (ε₁ * cs / 2) with hcsig_def
  have hcsig : 0 < csig := lt_min (by linarith) (by positivity)
  have hcsig1 : csig ≤ cr / 2 := min_le_left _ _
  have hcsig2 : csig ≤ ε₁ * cs / 2 := min_le_right _ _
  set cS : ℝ := min csig (γ' - γ₁) with hcS_def
  have hcS : 0 < cS := lt_min hcsig (by linarith)
  have hcS1 : cS ≤ csig := min_le_left _ _
  have hcS2 : cS ≤ γ' - γ₁ := min_le_right _ _
  set L : ℝ := Real.log (γ₂ / c₁) * 2 ^ (n + 4) * Cc with hL_def
  have hL : 0 ≤ L := by
    have : 0 ≤ Real.log (γ₂ / c₁) := Real.log_nonneg ((one_le_div hc₁).2 hc₁₂.le)
    positivity
  set CH : ℝ := C₀ + Crad * L ^ (1 / ((n : ℝ) + 1)) with hCH_def
  have hCH : 0 ≤ CH := by positivity
  set Kω : ℝ := (2 * ω) ^ (1 - 1 / p) with hKω_def
  have hKω : 0 ≤ Kω := by positivity
  -- `C₂` bounds `E_*` at scale `c_σ ρ` (steps 5–6); the fixed-scale tilt is estimated with
  -- `μ(B_{c_r ρ}(ζ)) ≤ μ(B_ρ(0)) ≤ 2ωρⁿ`.
  set C₂ : ℝ := max ((csig ^ n)⁻¹ * (1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH)) 1 with hC₂_def
  have hC₂ : 1 ≤ C₂ := le_max_right _ _
  set CD : ℝ := 2 * Real.sqrt n * Real.sqrt (CII * C₂) with hCD_def
  have hCD : 0 ≤ CD := by positivity
  set CHol : ℝ := Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * β) * (CIII * C₂) / ω) * (1 / csig) ^ β
    with hCHol_def
  set CR : ℝ := max CH (max CD (max CHol (2 * CD * (2 / cS) ^ β))) with hCR_def
  -- `δ^a ≤ X` gives `C_H δ^a ≤ c_r` and `C_D δ^a ≤ 1/4 = L₀` (the thresholds `δ_a`, `δ_L`).
  set X : ℝ := min (cr / max CH 1) (1 / (4 * max CD 1)) with hX_def
  have hX : 0 < X := lt_min (div_pos hcr (lt_max_of_lt_right one_pos)) (by positivity)
  set δR : ℝ := min (min (1 / 4) (ω / 3) / K₀)
    (min δE (min ε₁ (min δP (X ^ (2 * (n : ℝ) + 2))))) with hδR_def
  have hδR : 0 < δR :=
    lt_min (div_pos (lt_min (by norm_num) (by positivity)) hK₀)
      (lt_min hδE (lt_min hε₁ (lt_min hδP (Real.rpow_pos_of_pos hX _))))
  refine ⟨δR, CR, hδR, ?_⟩
  intro U hU V H δ ρ hδ hδR' hAH q u hu hu0 hDu hgraph hsub hnear
  have hAH₀ := hAH
  obtain ⟨hρ, hHGMC, hmult, h0spt, hBU, hmass, hLp⟩ := hAH₀
  -- The smallness conditions on `δ`.
  have hδl : δ ≤ min (1 / 4) (ω / 3) / K₀ := hδR'.trans (min_le_left _ _)
  have hδE' : δ ≤ δE := hδR'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ ≤ ε₁ :=
    hδR'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδP' : δ ≤ δP := hδR'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδX : δ ≤ X ^ (2 * (n : ℝ) + 2) := hδR'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδ4 : δ ≤ 1 / 4 := hδε.trans hε₁4
  have hδ1 : δ ≤ 1 := by linarith
  set t : ℝ := δ ^ a with ht_def
  have ht0 : 0 ≤ t := Real.rpow_nonneg hδ.le _
  have htX : t ≤ X := by
    calc t ≤ (X ^ (2 * (n : ℝ) + 2)) ^ a := Real.rpow_le_rpow hδ.le hδX ha0.le
      _ = X := by
        rw [← Real.rpow_mul hX.le, ha_def, mul_one_div_cancel (by positivity), Real.rpow_one]
  have hδt : δ ≤ t := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ t := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha1
  have hδt2 : δ ≤ t ^ 2 := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (a * (2 : ℕ)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by exact_mod_cast ha2)
      _ = t ^ 2 := Real.rpow_mul_natCast hδ.le a 2
  have hCHt : CH * t ≤ cr := by
    have h1 : t ≤ cr / max CH 1 := htX.trans (min_le_left _ _)
    have h2 : 0 < max CH 1 := lt_max_of_lt_right one_pos
    calc CH * t ≤ max CH 1 * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
      _ ≤ max CH 1 * (cr / max CH 1) := mul_le_mul_of_nonneg_left h1 h2.le
      _ = cr := by field_simp
  have hCDt : CD * t ≤ 1 / 4 := by
    have h1 : t ≤ 1 / (4 * max CD 1) := htX.trans (min_le_right _ _)
    have h2 : 0 < max CD 1 := lt_max_of_lt_right one_pos
    calc CD * t ≤ max CD 1 * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
      _ ≤ max CD 1 * (1 / (4 * max CD 1)) := mul_le_mul_of_nonneg_left h1 h2.le
      _ = 1 / 4 := by field_simp
  -- `Λ = 4pδ/(p - n) = K₀ δ ≤ min (1/4) (ω/3)`.
  set Λ : ℝ := 4 * p * δ / (p - n) with hΛ_def
  have hΛK : Λ = K₀ * δ := by rw [hΛ_def, hK₀_def]; ring
  have hΛ0 : 0 ≤ Λ := by rw [hΛK]; positivity
  have hΛmin : Λ ≤ min (1 / 4) (ω / 3) := by
    rw [hΛK]
    have := (le_div_iff₀ hK₀).1 hδl
    linarith
  have hΛ4 : Λ ≤ 1 / 4 := hΛmin.trans (min_le_left _ _)
  have hΛω : Λ ≤ ω / 3 := hΛmin.trans (min_le_right _ _)
  have hδκ : δ ≤ (p - n) / (4 * p) := by
    have h1 : (p - n) / (4 * p) * K₀ = 1 := by rw [hK₀_def]; field_simp
    have h2 : δ * K₀ ≤ (p - n) / (4 * p) * K₀ := by rw [h1]; linarith
    exact le_of_mul_le_mul_right h2 hK₀
  -- Scaled radii.
  have hγ₂0 : 0 < γ₂ := hγ₁.trans hγ₁₂
  have h1γ₂ : 0 < 1 - γ₂ := by linarith
  have hγ'lt1 : γ' < 1 := hγ'2.trans hγ₂
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hcr0 : cr ≠ 0 := hcr.ne'
  have hγ₁ρ : 0 < γ₁ * ρ := mul_pos hγ₁ hρ
  have hγ₁γ'ρ : γ₁ * ρ < γ' * ρ := mul_lt_mul_of_pos_right hγ'1 hρ
  have hγ'γ₂ρ : γ' * ρ < γ₂ * ρ := mul_lt_mul_of_pos_right hγ'2 hρ
  have hγ₂ρ : γ₂ * ρ < 1 * ρ := mul_lt_mul_of_pos_right hγ₂ hρ
  have hcrρ0 : 0 < cr * ρ := mul_pos hcr hρ
  have hcrρ1 : cr * ρ ≤ (γ₂ - γ') / 4 * ρ := mul_le_mul_of_nonneg_right hcr1 hρ.le
  have hcrρ2 : cr * ρ ≤ (1 - γ₂) / 4 * ρ := mul_le_mul_of_nonneg_right hcr2 hρ.le
  have hσ0 : 0 < csig * ρ := mul_pos hcsig hρ
  have hσ1 : csig * ρ ≤ cr / 2 * ρ := mul_le_mul_of_nonneg_right hcsig1 hρ.le
  have hσ2 : csig * ρ ≤ ε₁ * cs / 2 * ρ := mul_le_mul_of_nonneg_right hcsig2 hρ.le
  have hcSρ0 : 0 < cS * ρ := mul_pos hcS hρ
  have hcSρ1 : cS * ρ ≤ csig * ρ := mul_le_mul_of_nonneg_right hcS1 hρ.le
  have hcSρ2 : cS * ρ ≤ (γ' - γ₁) * ρ := mul_le_mul_of_nonneg_right hcS2 hρ.le
  have hcsρ0 : 0 < cs * ρ := mul_pos hcs hρ
  have hcsρ : cs * ρ ≤ (1 - γ₂) / 16 * ρ := mul_le_mul_of_nonneg_right hcs16 hρ.le
  have hγ'cr : cr * (γ' * ρ) ≤ cr * ρ :=
    mul_le_mul_of_nonneg_left (by linarith [mul_lt_mul_of_pos_right hγ'lt1 hρ]) hcr.le
  /- Step 2: density bounds and the conical integral, from `monotonicity_bounds`. -/
  obtain ⟨hM1, hM2, hM3⟩ :=
    Submission.any_radius_monotonicity_bounds n ℓ hn p hp U hU V H δ ρ hδ hδκ hAH
  rw [← hΛ_def] at hM1 hM2 hM3
  rw [← hω_def] at hM2 hM3
  try rw [← hω_def] at hmass
  have hexpΛ : Real.exp Λ ≤ 1 + 2 * Λ := by
    have h := Real.abs_exp_sub_one_le (x := Λ) (by rw [abs_of_nonneg hΛ0]; linarith)
    rw [abs_of_nonneg hΛ0] at h
    linarith [(abs_le.1 h).2]
  have hexp2Λ : Real.exp (2 * Λ) ≤ 2 := by
    have h2Λ : (0 : ℝ) ≤ 2 * Λ := by linarith
    have h := Real.abs_exp_sub_one_le (x := 2 * Λ) (by rw [abs_of_nonneg h2Λ]; linarith)
    rw [abs_of_nonneg h2Λ] at h
    linarith [(abs_le.1 h).2]
  have hexpnegΛ : 3 / 4 ≤ Real.exp (-Λ) := by
    have := Real.one_sub_le_exp_neg Λ
    linarith
  have hexp1 : 1 ≤ Real.exp Λ := Real.one_le_exp hΛ0
  have hμρ_fin : V.weight (closedBall 0 ρ) < ⊤ := lt_of_le_of_lt hmass ENNReal.ofReal_lt_top
  have hfin : ∀ (y : Amb n ℓ) (s : ℝ), closedBall y s ⊆ closedBall 0 ρ →
      V.weight (closedBall y s) < ⊤ :=
    fun y s h => lt_of_le_of_lt (measure_mono h) hμρ_fin
  have hμρ : (V.weight (closedBall 0 ρ)).toReal ≤ 2 * ω * ρ ^ n := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hmass
    have h2 : (1 + δ) * (ω * ρ ^ n) ≤ 2 * ω * ρ ^ n := by
      have : 0 ≤ ω * ρ ^ n := by positivity
      have := mul_le_mul_of_nonneg_right (show 1 + δ ≤ 2 by linarith) this
      linarith
    linarith
  have hμball : ∀ (y : Amb n ℓ) (s : ℝ), closedBall y s ⊆ closedBall 0 ρ →
      (V.weight (closedBall y s)).toReal ≤ 2 * ω * ρ ^ n :=
    fun y s h => (ENNReal.toReal_mono hμρ_fin.ne (measure_mono h)).trans hμρ
  -- Upper density bound `μ(B_s(y)) ≤ C_u ω sⁿ` for `|y| ≤ γ₂ρ`, `s ≤ (1 - γ₂)ρ/2`.
  have hup : ∀ y : Amb n ℓ, ‖y‖ ≤ γ₂ * ρ → ∀ s : ℝ, 0 < s → s ≤ (1 - γ₂) * ρ / 2 →
      (V.weight (closedBall y s)).toReal ≤ Cu * ω * s ^ n := by
    intro y hy s hs hsr
    have hR0 : 0 < (1 - γ₂) * ρ := mul_pos h1γ₂ hρ
    have hR : closedBall y ((1 - γ₂) * ρ) ⊆ closedBall 0 ρ :=
      closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
    have hr : (1 - γ₂) * ρ / 2 < (1 - γ₂) * ρ := by linarith
    have h1 := hM1 y ((1 - γ₂) * ρ) s ((1 - γ₂) * ρ / 2) hs hsr hr hR
    have hrpos : 0 < (1 - γ₂) * ρ / 2 := by linarith
    set Y := (V.weight (closedBall y ((1 - γ₂) * ρ / 2))).toReal / ((1 - γ₂) * ρ / 2) ^ n
      with hY_def
    have hY0 : 0 ≤ Y := by positivity
    have h2 : Y ≤ 2 * ω * (2 / (1 - γ₂)) ^ n := by
      rw [hY_def, div_le_iff₀ (pow_pos hrpos n)]
      calc _ ≤ 2 * ω * ρ ^ n :=
            hμball y _ ((closedBall_subset_closedBall (by linarith)).trans hR)
        _ = 2 * ω * (2 / (1 - γ₂)) ^ n * ((1 - γ₂) * ρ / 2) ^ n := by
          have e : 2 / (1 - γ₂) * ((1 - γ₂) * ρ / 2) = ρ := by
            field_simp [h1γ₂.ne']
          rw [mul_assoc (2 * ω), ← mul_pow, e]
    have h3 : (V.weight (closedBall y s)).toReal / s ^ n ≤
        4 * ω * (2 / (1 - γ₂)) ^ n + 3 / 4 := by
      have e1 : Real.exp (2 * Λ) * Y ≤ 2 * (2 * ω * (2 / (1 - γ₂)) ^ n) :=
        (mul_le_mul_of_nonneg_right hexp2Λ hY0).trans (by linarith)
      have e2 : Real.exp Λ * Λ ≤ 3 / 2 * Λ :=
        mul_le_mul_of_nonneg_right (by linarith) hΛ0
      linarith
    rw [div_le_iff₀ (pow_pos hs n)] at h3
    have hCuω : Cu * ω = 4 * (2 / (1 - γ₂)) ^ n * ω + 1 := by
      rw [hCu_def]; field_simp
    calc _ ≤ (4 * ω * (2 / (1 - γ₂)) ^ n + 3 / 4) * s ^ n := h3
      _ ≤ Cu * ω * s ^ n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hCuω]
        linarith
  -- Lower density bound `μ(B_s(y)) ≥ ω sⁿ/2` for `y ∈ spt V`, `|y| ≤ γ₂ρ`, `s < (1 - γ₂)ρ`.
  have hlow : ∀ y ∈ V.support, ‖y‖ ≤ γ₂ * ρ → ∀ s : ℝ, 0 < s → s < (1 - γ₂) * ρ →
      1 / 2 * ω * s ^ n ≤ (V.weight (closedBall y s)).toReal := by
    intro y hy hyn s hs hsR
    have hR : closedBall y ((1 - γ₂) * ρ) ⊆ closedBall 0 ρ :=
      closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
    have h1 := hM2 y hy ((1 - γ₂) * ρ) s hs hsR hR
    have h2 : 1 / 2 * ω ≤ Real.exp (-Λ) * (ω - Λ) := by
      have h0 : 0 ≤ ω - Λ := by linarith
      have := mul_le_mul_of_nonneg_right hexpnegΛ h0
      linarith
    calc 1 / 2 * ω * s ^ n ≤ Real.exp (-Λ) * (ω - Λ) * s ^ n :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := h1
  -- The conical integral is `≤ C_c δ`.
  have hcon : ∫⁻ x in ball (0 : Amb n ℓ) ρ,
      ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂V.weight ≤
        ENNReal.ofReal (Cc * δ) := by
    refine hM3.trans (ENNReal.ofReal_le_ofReal ?_)
    have hE32 : Real.exp Λ ≤ 3 / 2 := by linarith
    have hEa : Real.exp Λ * (1 + δ) - 1 ≤ 2 * Λ + 2 * δ := by
      have : Real.exp Λ * δ ≤ 3 / 2 * δ := mul_le_mul_of_nonneg_right hE32 hδ.le
      linarith
    have hEb : 1 ≤ Real.exp Λ * (1 + δ) := by
      have : 0 ≤ Real.exp Λ * δ := by positivity
      linarith
    have hinner0 : 0 ≤ ω * (Real.exp Λ * (1 + δ) - 1) + Λ := by
      have := mul_nonneg hω.le (sub_nonneg.2 hEb)
      linarith
    have hinner : ω * (Real.exp Λ * (1 + δ) - 1) + Λ ≤ ω * (2 * Λ + 2 * δ) + Λ := by
      have := mul_le_mul_of_nonneg_left hEa hω.le
      linarith
    calc Real.exp Λ * (Real.exp Λ * (1 + δ) * ω + Λ - ω)
        = Real.exp Λ * (ω * (Real.exp Λ * (1 + δ) - 1) + Λ) := by ring
      _ ≤ 3 / 2 * (ω * (2 * Λ + 2 * δ) + Λ) :=
          mul_le_mul hE32 hinner hinner0 (by norm_num)
      _ ≤ Cc * δ := by
        rw [hΛK, hCc_def]
        have h1 : 0 ≤ ω * K₀ * δ := by positivity
        have h2 : 0 ≤ ω * δ := by positivity
        have h3 : 0 ≤ K₀ * δ := by positivity
        linarith
  /- Step 3: graph facts. -/
  obtain ⟨-, htanM, -⟩ := Submission.any_radius_tangent_ae n ℓ hn U hU V
  obtain ⟨hE1, hE2, hE3⟩ :=
    hGC U hU V H δ ρ hδ hδE' hAH q u (ball 0 (γ₂ * ρ)) isOpen_ball hu hgraph
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9⟩ :=
    Submission.any_radius_gr_linear_algebra_basics n ℓ q
  obtain ⟨hP1, hP2, hP3, hP4⟩ := Submission.any_radius_gr_graph_plane_projections n ℓ q
  have hTF := fun (ζ : Amb n ℓ) (T : Submodule ℝ (Amb n ℓ)) =>
    Submission.any_radius_gr_tilt_integral_facts n ℓ U V htanM ζ T
  have hdiff : ∀ x ∈ ball (0 : Rn n) (γ₂ * ρ), DifferentiableAt ℝ u x := fun x hx =>
    (hu.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hlip : ∀ x ∈ ball (0 : Rn n) (γ₂ * ρ), ∀ y ∈ ball (0 : Rn n) (γ₂ * ρ),
      ‖u x - u y‖ ≤ 1 / 7 * ‖x - y‖ := fun x hx y hy =>
    (convex_ball (0 : Rn n) (γ₂ * ρ)).norm_image_sub_le_of_norm_fderiv_le hdiff hDu hy hx
  have hcontDu : ContinuousOn (fderiv ℝ u) (ball (0 : Rn n) (γ₂ * ρ)) :=
    hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hGnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖q (graphPoint a b)‖ ≤ ‖a‖ + ‖b‖ := by
    intro a b
    rw [LinearIsometryEquiv.norm_map]
    have hab : 0 ≤ ‖a‖ + ‖b‖ := by positivity
    have hsq : ‖graphPoint a b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
      rw [hL4 a b, add_sq]
      have := mul_nonneg (norm_nonneg a) (norm_nonneg b)
      linarith
    calc ‖graphPoint a b‖ = Real.sqrt (‖graphPoint a b‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((‖a‖ + ‖b‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖a‖ + ‖b‖ := Real.sqrt_sq hab
  have hFsub : ∀ x z : Rn n, q (graphPoint x (u x)) - q (graphPoint z (u z)) =
      q (graphPoint (x - z) (u x - u z)) := by
    intro x z
    rw [hL2, map_sub]
  have hFmem : ∀ z ∈ ball (0 : Rn n) (γ₂ * ρ), q (graphPoint z (u z)) ∈ V.support ∩ ball 0 ρ :=
    fun z hz => hgraph ⟨graphPoint z (u z), ⟨z, hz, rfl⟩, rfl⟩
  /- Step 4: the height bound `(H)`: `|u(x)| ≤ C_H δ^a |x|` on `B̆_{γ₂ρ}(0)`. -/
  have hgraphball : q '' graphOver u (ball 0 (γ₂ * ρ)) ⊆ ball 0 ρ := fun y hy => (hgraph hy).2
  have hHT := Submission.any_radius_gr_height_transfer n ℓ U V q u (γ₂ * ρ) ρ hu hu0 hDu
    hgraphball htanM (fun g hg => hE1 _ measurableSet_ball subset_rfl g hg) hE2
  have hint : ∫⁻ x in ball (0 : Rn n) (γ₂ * ρ),
      ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤
        ENNReal.ofReal (2 ^ (n + 4) * Cc * δ) := by
    have e : ENNReal.ofReal (2 ^ (n + 4) * Cc * δ) =
        ENNReal.ofReal (2 ^ (n + 4)) * ENNReal.ofReal (Cc * δ) := by
      rw [mul_assoc]
      exact ENNReal.ofReal_mul (by positivity)
    rw [e]
    exact hHT.trans (by gcongr)
  have hc₁ρ : 0 < c₁ * ρ := mul_pos hc₁ hρ
  have hc₁γ₂ : c₁ * ρ < γ₂ * ρ := mul_lt_mul_of_pos_right hc₁₂ hρ
  have hRH' := hRH ℓ u (γ₂ * ρ) (c₁ * ρ) (C₀ * t) (2 ^ (n + 4) * Cc * δ) hc₁ρ hc₁γ₂
    (by positivity) (by positivity) hu hu0 (fun x hx => (hDu x hx).trans (by norm_num)) hnear hint
  have hH : ∀ x ∈ ball (0 : Rn n) (γ₂ * ρ), ‖u x‖ ≤ CH * t * ‖x‖ := by
    intro x hx
    refine (hRH' x hx).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
    have hlog : Real.log (γ₂ * ρ / (c₁ * ρ)) * (2 ^ (n + 4) * Cc * δ) = L * δ := by
      rw [mul_div_mul_right _ _ hρ0, hL_def]; ring
    rw [hlog, Real.mul_rpow hL hδ.le, hCH_def]
    have h1 : δ ^ (1 / ((n : ℝ) + 1)) ≤ t := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha_le
    have h2 : 0 ≤ Crad * L ^ (1 / ((n : ℝ) + 1)) := mul_nonneg hCrad.le (Real.rpow_nonneg hL _)
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  /- Facts at the graph points `ζ = F(z)`, `|z| ≤ γ'ρ`. -/
  have hζfacts : ∀ z ∈ closedBall (0 : Rn n) (γ' * ρ), z ∈ ball (0 : Rn n) (γ₂ * ρ) ∧
      q (graphPoint z (u z)) ∈ V.support ∧ ‖q (graphPoint z (u z))‖ ≤ γ' * ρ + cr * ρ := by
    intro z hz
    have hzn : ‖z‖ ≤ γ' * ρ := mem_closedBall_zero_iff.1 hz
    have hzΩ : z ∈ ball (0 : Rn n) (γ₂ * ρ) := mem_ball_zero_iff.2 (by linarith)
    refine ⟨hzΩ, (hFmem z hzΩ).1, ?_⟩
    have h1 := hGnorm z (u z)
    have h2 := hH z hzΩ
    have h3 : CH * t * ‖z‖ ≤ cr * ρ :=
      (mul_le_mul hCHt hzn (norm_nonneg _) hcr.le).trans hγ'cr
    linarith
  have hBζ : ∀ z ∈ closedBall (0 : Rn n) (γ' * ρ), ∀ s : ℝ, s ≤ cr * ρ →
      closedBall (q (graphPoint z (u z))) s ⊆ closedBall 0 ρ := by
    intro z hz s hs
    obtain ⟨-, -, hζn⟩ := hζfacts z hz
    exact closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  /- Steps 5–6: tilt at the fixed scale `c_r ρ`, then translation, pinching and the tilt-excess
  iteration at every graph point `ζ = F(z)`, `|z| ≤ γ'ρ`. -/
  have hdecay : ∀ z ∈ closedBall (0 : Rn n) (γ' * ρ), ∃ S : Submodule ℝ (Amb n ℓ),
      hsNormSq (S.starProjection - (rotatedPlane q).starProjection) ≤ CII * (C₂ * t ^ 2) ∧
      ∀ s : ℝ, 0 < s → s ≤ csig * ρ → V.tiltExcess (q (graphPoint z (u z))) s S ≤
        CIII * (s / (csig * ρ)) ^ (2 * β) * (C₂ * t ^ 2) := by
    intro z hz
    obtain ⟨hzΩ, hζspt, hζn⟩ := hζfacts z hz
    have hBr := hBζ z hz (cr * ρ) le_rfl
    set ζ : Amb n ℓ := q (graphPoint z (u z)) with hζ_def
    have hζn2 : ‖ζ‖ ≤ γ₂ * ρ := by linarith
    -- Step 5: the height of `spt V ∩ B_{c_r ρ}(ζ)` over `ζ + T₀` is `≤ 2 C_H δ^a ρ`.
    have hheight : ∀ x ∈ V.support ∩ closedBall ζ (cr * ρ),
        infDist (x - ζ) (rotatedPlane q : Set (Amb n ℓ)) ≤ 2 * (CH * t) * ρ := by
      rintro x ⟨hxs, hxB⟩
      have hxn : ‖x‖ < γ₂ * ρ := by
        have := norm_le_of_mem_closedBall hxB
        linarith
      obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hsub ⟨hxs, mem_ball_zero_iff.2 hxn⟩
      rw [hζ_def, hFsub, hL6]
      have hx'n : ‖x'‖ ≤ ρ := by have := mem_ball_zero_iff.1 hx'; linarith
      have hzn : ‖z‖ ≤ ρ := by have := mem_ball_zero_iff.1 hzΩ; linarith
      have hCH0 : 0 ≤ CH * t := mul_nonneg hCH ht0
      calc ‖u x' - u z‖ ≤ ‖u x'‖ + ‖u z‖ := norm_sub_le _ _
        _ ≤ CH * t * ‖x'‖ + CH * t * ‖z‖ := add_le_add (hH x' hx') (hH z hzΩ)
        _ ≤ CH * t * ρ + CH * t * ρ :=
          add_le_add (mul_le_mul_of_nonneg_left hx'n hCH0) (mul_le_mul_of_nonneg_left hzn hCH0)
        _ = 2 * (CH * t) * ρ := by ring
    have hTH := Submission.any_radius_tilt_height_l1 n ℓ hn U hU V H hHGMC ζ (cr * ρ)
      (2 * (CH * t) * ρ) hcrρ0 (by positivity) (hBr.trans hBU) (rotatedPlane q) hL7 hheight
    have hfinr : V.weight (closedBall ζ (cr * ρ)) < ⊤ := hfin ζ _ hBr
    have : IsFiniteMeasure (V.weight.restrict (closedBall ζ (cr * ρ))) :=
      isFiniteMeasure_restrict.2 hfinr.ne
    set M : ℝ := (V.weight (closedBall ζ (cr * ρ))).toReal with hM_def
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hM : M ≤ 2 * ω * ρ ^ n := hμball ζ _ hBr
    have hI1 : ∫ x in closedBall ζ (cr * ρ), infDist (x - ζ) (rotatedPlane q : Set (Amb n ℓ)) ^ 2
        ∂V.weight ≤ (2 * (CH * t) * ρ) ^ 2 * M := by
      have hae : ∀ᵐ x ∂(V.weight.restrict (closedBall ζ (cr * ρ))),
          infDist (x - ζ) (rotatedPlane q : Set (Amb n ℓ)) ^ 2 ≤ (2 * (CH * t) * ρ) ^ 2 := by
        filter_upwards [ae_restrict_mem measurableSet_closedBall,
          ae_restrict_of_ae (Measure.support_mem_ae (μ := V.weight))] with x hxB hxs
        have := hheight x ⟨⟨hBU (hBr hxB), hxs⟩, hxB⟩
        exact pow_le_pow_left₀ infDist_nonneg this 2
      calc _ ≤ ∫ x in closedBall ζ (cr * ρ), (2 * (CH * t) * ρ) ^ 2 ∂V.weight :=
            integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
              (integrable_const _) hae
        _ = (2 * (CH * t) * ρ) ^ 2 * M := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
    have hI2 : ∫ x in closedBall ζ (cr * ρ), ‖H x‖ ∂V.weight ≤
        δ * ρ ^ ((n : ℝ) / p - 1) * M ^ (1 - 1 / p) :=
      (Submission.any_radius_gr_scaled_lp_ball_bounds n ℓ hn p hp U V H ζ (cr * ρ) ρ hcrρ0
        (by linarith) hBr).2 δ hδ.le hLp hfinr
    have hp1 : 0 ≤ 1 - 1 / p := by
      have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
      linarith
    have hMp : M ^ (1 - 1 / p) ≤ Kω * (ρ ^ n) ^ (1 - 1 / p) := by
      calc M ^ (1 - 1 / p) ≤ (2 * ω * ρ ^ n) ^ (1 - 1 / p) := Real.rpow_le_rpow hM0 hM hp1
        _ = Kω * (ρ ^ n) ^ (1 - 1 / p) := Real.mul_rpow (by positivity) (by positivity)
    have hρpow : ρ * ρ ^ ((n : ℝ) / p - 1) * (ρ ^ n) ^ (1 - 1 / p) = ρ ^ n := by
      have e1 : ρ * ρ ^ ((n : ℝ) / p - 1) = ρ ^ ((n : ℝ) / p) := by
        rw [Real.rpow_sub hρ, Real.rpow_one]
        field_simp
      have e2 : (ρ ^ n) ^ (1 - 1 / p) = ρ ^ ((n : ℝ) * (1 - 1 / p)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      rw [e1, e2, ← Real.rpow_add hρ, ← Real.rpow_natCast]
      congr 1
      ring
    have hhalf : ∫ x in closedBall ζ (cr * ρ / 2),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤
          (1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2 * ρ ^ n := by
      have h1 : 144 * ((cr * ρ) ^ 2)⁻¹ * ∫ x in closedBall ζ (cr * ρ),
          infDist (x - ζ) (rotatedPlane q : Set (Amb n ℓ)) ^ 2 ∂V.weight ≤
            1152 * ω / cr ^ 2 * CH ^ 2 * t ^ 2 * ρ ^ n := by
        calc _ ≤ 144 * ((cr * ρ) ^ 2)⁻¹ * ((2 * (CH * t) * ρ) ^ 2 * (2 * ω * ρ ^ n)) :=
              mul_le_mul_of_nonneg_left (hI1.trans (mul_le_mul_of_nonneg_left hM (by positivity)))
                (by positivity)
          _ = 1152 * ω / cr ^ 2 * CH ^ 2 * t ^ 2 * ρ ^ n := by
            field_simp
            ring
      have h2 : 4 * (2 * (CH * t) * ρ) * ∫ x in closedBall ζ (cr * ρ), ‖H x‖ ∂V.weight ≤
          8 * Kω * CH * t ^ 2 * ρ ^ n := by
        calc _ ≤ 4 * (2 * (CH * t) * ρ) *
              (δ * ρ ^ ((n : ℝ) / p - 1) * (Kω * (ρ ^ n) ^ (1 - 1 / p))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact hI2.trans (mul_le_mul_of_nonneg_left hMp (by positivity))
          _ = 8 * Kω * CH * t * δ * (ρ * ρ ^ ((n : ℝ) / p - 1) * (ρ ^ n) ^ (1 - 1 / p)) := by
            ring
          _ = 8 * Kω * CH * t * δ * ρ ^ n := by rw [hρpow]
          _ ≤ 8 * Kω * CH * t * t * ρ ^ n := by gcongr
          _ = 8 * Kω * CH * t ^ 2 * ρ ^ n := by ring
      calc _ ≤ _ := hTH
        _ ≤ 1152 * ω / cr ^ 2 * CH ^ 2 * t ^ 2 * ρ ^ n + 8 * Kω * CH * t ^ 2 * ρ ^ n :=
          add_le_add h1 h2
        _ = _ := by ring
    -- `E(ζ, c_σ ρ, T₀) ≤ C_E δ^{2a}` by monotonicity of the tilt integral in the radius.
    have hσr : csig * ρ ≤ cr * ρ / 2 := by linarith
    have hfin2 : V.weight (closedBall ζ (cr * ρ / 2)) < ⊤ :=
      hfin ζ _ ((closedBall_subset_closedBall (by linarith)).trans hBr)
    have hEσ : V.tiltExcess ζ (csig * ρ) (rotatedPlane q) ≤
        (csig ^ n)⁻¹ * (1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2 := by
      have h1 := (hTF ζ (rotatedPlane q)).2.1 (csig * ρ) (cr * ρ / 2) hσ0 hσr hfin2
      have h2 : (cr * ρ / 2) ^ n * V.tiltExcess ζ (cr * ρ / 2) (rotatedPlane q) =
          ∫ x in closedBall ζ (cr * ρ / 2),
            hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight := by
        rw [RectifiableVarifold.tiltExcess, ← mul_assoc, mul_inv_cancel₀ (by positivity),
          one_mul]
      rw [h2] at h1
      have h3 := h1.trans hhalf
      rw [mul_pow] at h3
      have hρn : 0 < ρ ^ n := pow_pos hρ n
      have h4 : csig ^ n * V.tiltExcess ζ (csig * ρ) (rotatedPlane q) ≤
          (1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2 := by
        have : (csig ^ n * V.tiltExcess ζ (csig * ρ) (rotatedPlane q)) * ρ ^ n ≤
            ((1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2) * ρ ^ n := by
          calc _ = csig ^ n * ρ ^ n * V.tiltExcess ζ (csig * ρ) (rotatedPlane q) := by ring
            _ ≤ _ := h3
        exact le_of_mul_le_mul_right this hρn
      have hcn : 0 < csig ^ n := pow_pos hcsig n
      calc V.tiltExcess ζ (csig * ρ) (rotatedPlane q)
          = (csig ^ n)⁻¹ * (csig ^ n * V.tiltExcess ζ (csig * ρ) (rotatedPlane q)) := by
            field_simp
        _ ≤ (csig ^ n)⁻¹ * ((1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    -- Step 6: translate `V` by `-ζ` (`rescaled_varifold` with `R = 1`).
    obtain ⟨V', -, hV'mult, hV'w, hV'supp, hV'tan, hV'H⟩ :=
      Submission.any_radius_rescaled_varifold n ℓ U hU V ζ 1 one_pos
    have hU' : IsOpen ((fun x => ζ + (1 : ℝ) • x) ⁻¹' U) := hU.preimage (by fun_prop)
    have hw' : V'.weight = V.weight.map (fun x => x - ζ) := by
      rw [hV'w]
      simp
    have hmult' : ∀ x, V'.mult x = V.mult (ζ + x) := fun x => by rw [hV'mult, one_smul]
    have htan' : ∀ x, V'.tangentProj x = V.tangentProj (ζ + x) := fun x => by
      rw [hV'tan, one_smul]
    obtain ⟨hR1, hR2, hR3, hR4⟩ :=
      Submission.any_radius_gr_translate_identities n ℓ U _ V V' ζ hw' hmult' htan'
    have hH' : V'.HasGeneralizedMeanCurvature (fun x => H (ζ + x)) := by
      have := hV'H H hHGMC
      simpa only [one_smul] using this
    have hcsB : closedBall ζ (cs * ρ) ⊆ closedBall 0 ρ :=
      closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
    have hσB : closedBall ζ (csig * ρ) ⊆ closedBall 0 ρ :=
      closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
    have hAH' : V'.AllardHypotheses (fun x => H (ζ + x)) p ε₁ (cs * ρ) := by
      refine ⟨hcsρ0, hH', hR4 hmult, ?_, ?_, ?_, ?_⟩
      · rw [hV'supp]
        simpa using hζspt
      · intro x hx
        simp only [mem_preimage, one_smul]
        apply hBU
        apply hcsB
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        simpa using hx
      · rw [hR1]
        have hζγ : ‖ζ‖ ≤ (1 + γ₂) / 2 * ρ := by
          have := mul_lt_mul_of_pos_right hγ₂ hρ
          linarith
        exact hPin U hU V H δ ρ hδ hδP' hAH ζ ⟨hζspt, mem_closedBall_zero_iff.2 hζγ⟩
      · rw [hR3]
        exact ((Submission.any_radius_gr_scaled_lp_ball_bounds n ℓ hn p hp U V H ζ (cs * ρ) ρ
          hcsρ0 (by linarith) hcsB).1.trans hLp).trans (ENNReal.ofReal_le_ofReal hδε)
    have hmassb : ∀ s : ℝ, 0 < s → s ≤ csig * ρ →
        1 / 2 * ω * s ^ n ≤ (V'.weight (closedBall 0 s)).toReal ∧
          (V'.weight (closedBall 0 s)).toReal ≤ Cu * ω * s ^ n := by
      intro s hs hsσ
      rw [hR1]
      exact ⟨hlow ζ hζspt hζn2 s hs (by linarith), hup ζ hζn2 s hs (by linarith)⟩
    obtain ⟨S, -, hS1, hS2⟩ := hTI _ hU' V' (fun x => H (ζ + x)) ε₁ (cs * ρ) (csig * ρ) hε₁ hε₁6
      hAH' hσ0 (by linarith) hmassb (rotatedPlane q) hL7
    -- The normalised excess `E₂ = E_*` of `V'` at scale `c_σ ρ`.
    have hE2eq : V'.tiltExcessStar (fun x => H (ζ + x)) p ε₁ 0 (csig * ρ) (rotatedPlane q) =
        max (V.tiltExcess ζ (csig * ρ) (rotatedPlane q))
          (ε₁⁻¹ * (V.scaledLpNorm H p ζ (csig * ρ)).toReal ^ 2) := by
      rw [RectifiableVarifold.tiltExcessStar, hR2, hR3]
    set E₂ := V'.tiltExcessStar (fun x => H (ζ + x)) p ε₁ 0 (csig * ρ) (rotatedPlane q)
      with hE₂_def
    have hE₂0 : 0 ≤ E₂ := by
      rw [hE2eq]
      exact le_max_of_le_right (by positivity)
    have hE₂ : E₂ ≤ C₂ * t ^ 2 := by
      rw [hE2eq]
      apply max_le
      · calc _ ≤ (csig ^ n)⁻¹ * (1152 * ω / cr ^ 2 * CH ^ 2 + 8 * Kω * CH) * t ^ 2 := hEσ
          _ ≤ C₂ * t ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · have hK : (V.scaledLpNorm H p ζ (csig * ρ)).toReal ≤ δ :=
          ENNReal.toReal_le_of_le_ofReal hδ.le
            ((Submission.any_radius_gr_scaled_lp_ball_bounds n ℓ hn p hp U V H ζ (csig * ρ) ρ
              hσ0 (by linarith) hσB).1.trans hLp)
        have hK0 : 0 ≤ (V.scaledLpNorm H p ζ (csig * ρ)).toReal := ENNReal.toReal_nonneg
        calc ε₁⁻¹ * (V.scaledLpNorm H p ζ (csig * ρ)).toReal ^ 2 ≤ ε₁⁻¹ * δ ^ 2 := by gcongr
          _ ≤ δ := by
            rw [inv_mul_le_iff₀ hε₁, sq]
            exact mul_le_mul_of_nonneg_right hδε hδ.le
          _ ≤ t ^ 2 := hδt2
          _ ≤ C₂ * t ^ 2 := le_mul_of_one_le_left (by positivity) hC₂
    refine ⟨S, ?_, ?_⟩
    · calc hsNormSq (S.starProjection - (rotatedPlane q).starProjection) ≤ CII₀ * E₂ := hS1
        _ ≤ CII * E₂ := mul_le_mul_of_nonneg_right (le_max_left _ _) hE₂0
        _ ≤ CII * (C₂ * t ^ 2) := mul_le_mul_of_nonneg_left hE₂ (by positivity)
    · intro s hs hsσ
      have hw0 : 0 ≤ (s / (csig * ρ)) ^ (2 * β) := Real.rpow_nonneg (by positivity) _
      rw [← hR2]
      calc V'.tiltExcess 0 s S ≤ CIII₀ * (s / (csig * ρ)) ^ (2 * β) * E₂ := hS2 s hs hsσ
        _ ≤ CIII * (s / (csig * ρ)) ^ (2 * β) * E₂ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0) hE₂0
        _ ≤ CIII * (s / (csig * ρ)) ^ (2 * β) * (C₂ * t ^ 2) :=
          mul_le_mul_of_nonneg_left hE₂ (by positivity)
  /- Step 7: at a.e. graph point the tangent plane is the decay plane `S(ζ)`. -/
  have hident : ∀ z ∈ closedBall (0 : Rn n) (γ' * ρ),
      V.tangentProj (q (graphPoint z (u z))) = (Submodule.map q.toLinearEquiv.toLinearMap
        (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u z v)))).starProjection →
      Tendsto (fun s : ℝ => (V.weight (closedBall (q (graphPoint z (u z))) s))⁻¹ *
        ∫⁻ y in closedBall (q (graphPoint z (u z))) s,
          ENNReal.ofReal (hsNormSq (V.tangentProj y - V.tangentProj (q (graphPoint z (u z)))))
            ∂V.weight) (𝓝[>] 0) (𝓝 0) →
      ∃ S : Submodule ℝ (Amb n ℓ), (Submodule.map q.toLinearEquiv.toLinearMap
          (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u z v)))).starProjection
            = S.starProjection ∧
        hsNormSq (S.starProjection - (rotatedPlane q).starProjection) ≤ CII * (C₂ * t ^ 2) ∧
        ∀ s : ℝ, 0 < s → s ≤ csig * ρ → V.tiltExcess (q (graphPoint z (u z))) s S ≤
          CIII * (s / (csig * ρ)) ^ (2 * β) * (C₂ * t ^ 2) := by
    intro z hz h2 h3
    obtain ⟨S, hS1, hS2⟩ := hdecay z hz
    refine ⟨S, ?_, hS1, hS2⟩
    rw [← h2]
    obtain ⟨-, hζspt, hζn⟩ := hζfacts z hz
    have hζn2 : ‖q (graphPoint z (u z))‖ ≤ γ₂ * ρ := by linarith
    have hT3 := (hTF (q (graphPoint z (u z))) S).2.2
    refine Submission.any_radius_gr_tangent_identification n ℓ U V htanM _ S (ω / 2) (csig * ρ)
      (by positivity) hσ0 ?_ h3 ?_
    · intro s hs hsσ
      have hfs := hfin _ s (hBζ z hz s (by linarith))
      refine ⟨?_, hfs⟩
      rw [← ENNReal.ofReal_toReal hfs.ne]
      apply ENNReal.ofReal_le_ofReal
      have := hlow _ hζspt hζn2 s hs (by linarith)
      linarith
    · have hlim : Tendsto (fun s : ℝ => CIII * (s / (csig * ρ)) ^ (2 * β) * (C₂ * t ^ 2))
          (𝓝[>] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun s : ℝ => (s / (csig * ρ)) ^ (2 * β)) 0 :=
          (continuousAt_id.div_const _).rpow_const (Or.inr (by positivity))
        have h0 : Tendsto (fun s : ℝ => (s / (csig * ρ)) ^ (2 * β)) (𝓝 0) (𝓝 0) := by
          have := hc.tendsto
          simp only [zero_div] at this
          rwa [Real.zero_rpow (by positivity)] at this
        have := (h0.const_mul CIII).mul_const (C₂ * t ^ 2)
        rw [mul_zero, zero_mul] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact hT3 s hs
      · filter_upwards [Ioc_mem_nhdsGT hσ0] with s hs
        exact hS2 s hs.1 hs.2
  /- Step 8: `|Du| ≤ C_D δ^a` on `B̆_{γ'ρ}(0)`: a.e. by (Ang), everywhere by continuity. -/
  have hO : ball (0 : Rn n) (γ' * ρ) ⊆ ball (0 : Rn n) (γ₂ * ρ) := ball_subset_ball hγ'γ₂ρ.le
  have hDuop : ∀ z ∈ ball (0 : Rn n) (γ' * ρ),
      ‖fderiv ℝ u z‖ ≤ 2 * (Real.sqrt (CII * C₂) * t) := by
    have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : Rn n) (γ' * ρ))),
        ‖fderiv ℝ u z‖ ≤ 2 * (Real.sqrt (CII * C₂) * t) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hO hE2,
        ae_restrict_of_ae_restrict_of_subset hO hE3, ae_restrict_mem measurableSet_ball]
        with z h2 h3 hzO
      obtain ⟨S, hGS, hS1, -⟩ := hident z (ball_subset_closedBall hzO) h2 h3
      have hAng := hP3 (fderiv ℝ u z)
      rw [hGS] at hAng
      have hop : ‖S.starProjection - (rotatedPlane q).starProjection‖ ≤
          Real.sqrt (CII * C₂) * t := by
        refine (hL8 (n + ℓ) (n + ℓ) (S.starProjection - (rotatedPlane q).starProjection)
          0).2.2.2.2.2.1.trans ?_
        calc hsNorm (S.starProjection - (rotatedPlane q).starProjection)
            = Real.sqrt (hsNormSq (S.starProjection - (rotatedPlane q).starProjection)) := rfl
          _ ≤ Real.sqrt (CII * C₂ * t ^ 2) := Real.sqrt_le_sqrt (by linarith)
          _ = Real.sqrt (CII * C₂) * t := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht0]
      have hDz : ‖fderiv ℝ u z‖ ≤ 1 / 7 := hDu z (hO hzO)
      have hsq : Real.sqrt (1 + ‖fderiv ℝ u z‖ ^ 2) ≤ 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, ?_⟩
        have := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ u z)) hDz 2
        linarith
      calc ‖fderiv ℝ u z‖ ≤ Real.sqrt (1 + ‖fderiv ℝ u z‖ ^ 2) *
            ‖S.starProjection - (rotatedPlane q).starProjection‖ := hAng
        _ ≤ 2 * (Real.sqrt (CII * C₂) * t) := mul_le_mul hsq hop (norm_nonneg _) (by norm_num)
    intro z₀ hz₀
    by_contra hle
    have hlt := not_le.1 hle
    have hcont : ContinuousOn (fun z => ‖fderiv ℝ u z‖) (ball (0 : Rn n) (γ' * ρ)) :=
      continuous_norm.comp_continuousOn (hcontDu.mono hO)
    have hBopen := hcont.isOpen_inter_preimage isOpen_ball
      (isOpen_Ioi (a := 2 * (Real.sqrt (CII * C₂) * t)))
    have hpos := hBopen.measure_pos volume ⟨z₀, hz₀, hlt⟩
    have hnull : (volume : Measure (Rn n)) (ball (0 : Rn n) (γ' * ρ) ∩
        (fun z => ‖fderiv ℝ u z‖) ⁻¹' Ioi (2 * (Real.sqrt (CII * C₂) * t))) = 0 := by
      rw [ae_restrict_iff' measurableSet_ball] at hae
      have : ∀ᵐ z ∂(volume : Measure (Rn n)), z ∉ ball (0 : Rn n) (γ' * ρ) ∩
          (fun z => ‖fderiv ℝ u z‖) ⁻¹' Ioi (2 * (Real.sqrt (CII * C₂) * t)) := by
        filter_upwards [hae] with z hz hzB
        exact absurd (hz hzB.1) (not_le.2 hzB.2)
      rw [ae_iff] at this
      exact measure_mono_null (fun z hz => not_not_intro hz) this
    exact hpos.ne' hnull
  have hDuO : ∀ z ∈ ball (0 : Rn n) (γ' * ρ), hsNorm (fderiv ℝ u z) ≤ CD * t := by
    intro z hz
    calc hsNorm (fderiv ℝ u z) ≤ Real.sqrt n * ‖fderiv ℝ u z‖ :=
          (hL8 n ℓ (fderiv ℝ u z) 0).2.2.2.2.2.2
      _ ≤ Real.sqrt n * (2 * (Real.sqrt (CII * C₂) * t)) :=
          mul_le_mul_of_nonneg_left (hDuop z hz) (Real.sqrt_nonneg _)
      _ = CD * t := by rw [hCD_def]; ring
  /- Step 9: the Campanato input `∫_{B_{s/2}(z)} |Du - Du(z)|² ≤ A s^{n + 2β}`. -/
  have h1Ω : closedBall (0 : Rn n) (γ₁ * ρ) ⊆ ball (0 : Rn n) (γ₂ * ρ) :=
    closedBall_subset_ball (hγ₁γ'ρ.trans hγ'γ₂ρ)
  set A : ℝ := CIII * (C₂ * t ^ 2) / (csig * ρ) ^ (2 * β) with hA_def
  have hσβ2 : 0 < (csig * ρ) ^ (2 * β) := Real.rpow_pos_of_pos hσ0 _
  have hA0 : 0 ≤ A := by positivity
  have hcampin : ∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) (γ₁ * ρ))), ∀ s : ℝ, 0 < s →
      s ≤ cS * ρ → ∫⁻ x in closedBall z (s / 2),
        ENNReal.ofReal (hsNormSq (fderiv ℝ u x - fderiv ℝ u z)) ≤
          ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * β)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h1Ω hE2,
      ae_restrict_of_ae_restrict_of_subset h1Ω hE3, ae_restrict_mem measurableSet_closedBall]
      with z h2 h3 hz
    have hzγ' : z ∈ closedBall (0 : Rn n) (γ' * ρ) := closedBall_subset_closedBall hγ₁γ'ρ.le hz
    obtain ⟨S, hGS, -, hS2⟩ := hident z hzγ' h2 h3
    obtain ⟨hzΩ, -, -⟩ := hζfacts z hzγ'
    intro s hs hsS
    have hzn : ‖z‖ ≤ γ₁ * ρ := mem_closedBall_zero_iff.1 hz
    have hBsub : closedBall z (s / 2) ⊆ ball (0 : Rn n) (γ' * ρ) := by
      intro x hx
      rw [mem_ball_zero_iff]
      have := norm_le_of_mem_closedBall hx
      linarith
    have hFlip : ∀ x ∈ closedBall z (s / 2),
        ‖q (graphPoint x (u x)) - q (graphPoint z (u z))‖ ≤ s := by
      intro x hx
      have hxz : ‖x - z‖ ≤ s / 2 := mem_closedBall_iff_norm.1 hx
      rw [hFsub]
      calc _ ≤ ‖x - z‖ + ‖u x - u z‖ := hGnorm _ _
        _ ≤ ‖x - z‖ + 1 / 7 * ‖x - z‖ := by
          have := hlip x (hO (hBsub hx)) z hzΩ
          linarith
        _ ≤ s := by
          have := norm_nonneg (x - z)
          linarith
    have hci := Submission.any_radius_gr_campanato_input n ℓ U V q u (ball 0 (γ₂ * ρ)) htanM
      hu.continuousOn hE1 hE2 S z (s / 2) s hs (hBsub.trans hO)
      (fun x hx => (hDuO x (hBsub hx)).trans hCDt) hFlip hGS
      (hfin _ s (hBζ z hzγ' s (by linarith)))
    refine hci.trans (ENNReal.ofReal_le_ofReal ?_)
    have hE := hS2 s hs (hsS.trans hcSρ1)
    calc s ^ n * V.tiltExcess (q (graphPoint z (u z))) s S ≤
          s ^ n * (CIII * (s / (csig * ρ)) ^ (2 * β) * (C₂ * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = A * s ^ ((n : ℝ) + 2 * β) := by
        rw [hA_def, Real.div_rpow hs.le hσ0.le, Real.rpow_add hs, Real.rpow_natCast]
        field_simp
  /- Step 10: the Campanato lemma. -/
  have hcontB : ContinuousOn (fderiv ℝ u) (closedBall 0 (γ₁ * ρ + cS * ρ)) :=
    hcontDu.mono (closedBall_subset_ball (by linarith))
  have hHol := Submission.any_radius_campanato n ℓ hn (fderiv ℝ u) (γ₁ * ρ) (cS * ρ) A β hγ₁ρ
    hcSρ0 hA0 hβ0 hcontB hcampin
  have hDu1 : ∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), hsNorm (fderiv ℝ u x) ≤ CD * t :=
    fun x hx => hDuO x (closedBall_subset_ball hγ₁γ'ρ hx)
  /- Step 11: conclusion. -/
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
  · calc ‖u x‖ ≤ CH * t * ‖x‖ := hH x (h1Ω hx)
      _ ≤ CR * t * ‖x‖ := by gcongr; exact le_max_left _ _
  · calc hsNorm (fderiv ℝ u x) ≤ CD * t := hDu1 x hx
      _ ≤ CR * t := by gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · have hw0 : 0 ≤ (‖x - y‖ / ρ) ^ β := by positivity
    by_cases hxy : ‖x - y‖ ≤ cS * ρ / 2
    · have h := hHol x hx y hy hxy
      have hσβ : 0 < (csig * ρ) ^ β := Real.rpow_pos_of_pos hσ0 β
      have e1 : (csig * ρ) ^ (2 * β) = ((csig * ρ) ^ β) ^ 2 := by
        rw [mul_comm 2 β, Real.rpow_mul hσ0.le, Real.rpow_two]
      have hK0 : 0 ≤ 2 ^ (2 * (n : ℝ) + 2 + 2 * β) * (CIII * C₂) / ω := by positivity
      have e2 : 2 ^ (2 * (n : ℝ) + 2 + 2 * β) * A / ω =
          (2 ^ (2 * (n : ℝ) + 2 + 2 * β) * (CIII * C₂) / ω) * (t / (csig * ρ) ^ β) ^ 2 := by
        rw [hA_def, e1]
        field_simp
      have e3 : (csig * ρ) ^ β * ((1 / csig) ^ β * (‖x - y‖ / ρ) ^ β) = ‖x - y‖ ^ β := by
        rw [← Real.mul_rpow (x := 1 / csig) (y := ‖x - y‖ / ρ) (by positivity) (by positivity),
          ← Real.mul_rpow (x := csig * ρ) (y := 1 / csig * (‖x - y‖ / ρ)) (by positivity)
            (by positivity)]
        congr 1
        field_simp
      have ht' : 0 ≤ t / (csig * ρ) ^ β := by positivity
      calc hsNorm (fderiv ℝ u x - fderiv ℝ u y)
          ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * β) * A / ω) * ‖x - y‖ ^ β := h
        _ = CHol * t * (‖x - y‖ / ρ) ^ β := by
          rw [e2, Real.sqrt_mul hK0, Real.sqrt_sq ht', ← e3, hCHol_def]
          field_simp
        _ ≤ CR * t * (‖x - y‖ / ρ) ^ β := by
          gcongr
          exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · have hxy := not_le.1 hxy
      have hDx := hDu1 x hx
      have hDy := hDu1 y hy
      have hfar : hsNorm (fderiv ℝ u x - fderiv ℝ u y) ≤ 2 * (CD * t) := by
        obtain ⟨-, hxsq, hadd, -, -, -, -⟩ := hL8 n ℓ (fderiv ℝ u x) (-(fderiv ℝ u y))
        obtain ⟨-, hysq, -, hyneg, -, -, -⟩ := hL8 n ℓ (fderiv ℝ u y) 0
        have hsx : hsNormSq (fderiv ℝ u x) ≤ (CD * t) ^ 2 := by
          rw [← hxsq]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hDx 2
        have hsy : hsNormSq (fderiv ℝ u y) ≤ (CD * t) ^ 2 := by
          rw [← hysq]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hDy 2
        have hsub2 : hsNormSq (fderiv ℝ u x - fderiv ℝ u y) ≤ (2 * (CD * t)) ^ 2 := by
          rw [sub_eq_add_neg]
          calc _ ≤ 2 * hsNormSq (fderiv ℝ u x) + 2 * hsNormSq (-(fderiv ℝ u y)) := hadd
            _ = 2 * hsNormSq (fderiv ℝ u x) + 2 * hsNormSq (fderiv ℝ u y) := by rw [hyneg]
            _ ≤ (2 * (CD * t)) ^ 2 := by linarith
        calc hsNorm (fderiv ℝ u x - fderiv ℝ u y)
            = Real.sqrt (hsNormSq (fderiv ℝ u x - fderiv ℝ u y)) := rfl
          _ ≤ Real.sqrt ((2 * (CD * t)) ^ 2) := Real.sqrt_le_sqrt hsub2
          _ = 2 * (CD * t) := Real.sqrt_sq (by positivity)
      have hm : (2 / cS) ^ β * (‖x - y‖ / ρ) ^ β = (2 / cS * (‖x - y‖ / ρ)) ^ β :=
        (Real.mul_rpow (by positivity) (by positivity)).symm
      have hge1 : 1 ≤ (2 / cS) ^ β * (‖x - y‖ / ρ) ^ β := by
        rw [hm]
        apply Real.one_le_rpow _ hβ0.le
        rw [div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
        linarith
      calc hsNorm (fderiv ℝ u x - fderiv ℝ u y) ≤ 2 * (CD * t) := hfar
        _ ≤ 2 * (CD * t) * ((2 / cS) ^ β * (‖x - y‖ / ρ) ^ β) :=
          le_mul_of_one_le_right (by positivity) hge1
        _ = 2 * CD * (2 / cS) ^ β * t * (‖x - y‖ / ρ) ^ β := by ring
        _ ≤ CR * t * (‖x - y‖ / ρ) ^ β := by
          gcongr
          exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
