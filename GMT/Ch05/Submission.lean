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
  -- (i): subtraction is coordinatewise
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

end GMT.Ch05
