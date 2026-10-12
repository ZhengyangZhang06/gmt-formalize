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
/-- The graph point `(x, y) ∈ ℝ^{n+ℓ}` is the inverse image of `(x, y)` under Mathlib's canonical
equivalence `EuclideanSpace.finAddEquivProd : ℝ^{n+ℓ} ≃L[ℝ] ℝⁿ × ℝ^ℓ` (reindexing by
`finSumFinEquiv.symm`, then splitting into the `Sum.inl`/`Sum.inr` parts).  Compare coordinates:
every index of `Fin (n + ℓ)` is `Fin.castAdd ℓ j` or `Fin.natAdd n k` (`Fin.addCases`); there both
sides equal `x j`, resp. `y k` (`Fin.append_left`/`Fin.append_right` on the left,
`finSumFinEquiv_symm_apply_castAdd`/`finSumFinEquiv_symm_apply_natAdd` on the right). -/
theorem rsod_graphPoint_eq_finAddEquivProd_symm : ∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ),
    graphPoint x y = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y) := by
  intro n ℓ x y
  ext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [graphPoint]
  · simp [graphPoint]

set_option maxHeartbeats 10000000 in
open scoped CompactlySupported in
/-- **Simon Ch. 3, 1.6–1.9 and Rem. 1.8, with the Lipschitz-graph form of Ch. 3, 1.9** for a
rectifiable varifold `V = v(M, θ)` in `U`, `μ = μ_V`: (0) the weighted approximate tangent plane
exists `μ`-a.e.; (1) `p_x = V.tangentProj x` is `μ`-a.e. the projection onto an `n`-plane; (2)
`x ↦ p_x` is `μ`-a.e. strongly measurable; (3) `Θⁿ(μ, x) = θ(x)` `μ`-a.e.; (4) on a rotated
Lipschitz graph `x = q(x', f(x'))`, `p_x` is `μ`-a.e. the projection onto
`q(graph Df(x'))` wherever `f` is differentiable.  Proof: `M` is covered, up to an `Hⁿ`-null set,
by compact Lusin pieces `K` of `θ` (Simon 1.17, proved inline) intersected with images `S = F(A)`
of bounded Borel pieces on which a Lipschitz chart `F` approximates an injective linear map
(`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`), hence is bi-Lipschitz; a rotated
Lipschitz graph `w ↦ q(w, f̃(w))` (`f̃` a Lipschitz extension of `f`) is globally bi-Lipschitz.
The injective Lipschitz area formula `Hⁿ ⌞ F(A) = F_#(J_F 𝓛ⁿ ⌞ A)`, Lebesgue points of `1_A J_F`
and the derivative of `F` give the blow-up of `Hⁿ ⌞ S` (limit `Hⁿ ⌞ DF(a)(ℝⁿ)`); the blow-up
identity `rsod_blowUp_setIntegral_eq`, the upper density theorem
`upperDensity_ne_zero_outside_hausdorff_null` (for `μ ⌞ (M \ K)`, `Hⁿ ⌞ (K \ S)`, `Hⁿ ⌞ (S \ K)`)
and continuity of `θ` on `K` give the weighted plane, unique as `θ > 0`; squeezing with cutoffs
gives the density, and `p_{range L} = L (L* L)⁻¹ L*` with a Borel inverse of `F` on `A` gives
measurability. -/
theorem ted_tangent_plane_facts : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ V : RectifiableVarifold n ℓ U, (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧ (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) ∧ ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ) (L : ℝ≥0), LipschitzOnWith L f (closedBall 0 R) → ∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) R, x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection := by
  intro n ℓ hn U hU V
  -- Simon Ch. 3, Remark 1.8(1): Lusin exhaustion of the carrier by compact pieces on which `θ`
  -- is continuous (Lusin's theorem, Simon 1.17, proved inline).
  have lusin_exhaustion : ∃ K : ℕ → Set (Amb n ℓ), (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ V.carrier) ∧ (∀ m, ContinuousOn V.mult (K m)) ∧ (∀ m, (μHE[n] : Measure (Amb n ℓ)) (K m) < ⊤) ∧ (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ m, K m) = 0 := by
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
  -- Lusin pieces
  obtain ⟨Kp, hKc, hKM, hKcont, hKfin, hKnull⟩ := lusin_exhaustion
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
  have hacH : V.weight ≪ H :=
    hac.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have proj_congr : ∀ P Q : Submodule ℝ (Amb n ℓ), P = Q → P.starProjection = Q.starProjection := by
    rintro P Q rfl; rfl
  -- `p_x` is the projection onto any weighted approximate tangent plane at `x ∈ M`
  have tangentProj_eq : ∀ x ∈ V.carrier, ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P →
      V.tangentProj x = P.starProjection := by
    intro x hxM P hW
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P :=
      ⟨P, hW⟩
    have huniq : Classical.choose hex = P :=
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
        (V.mult_pos _ hxM).ne' (Classical.choose_spec hex) hW
    rw [RectifiableVarifold.tangentProj, dif_pos hex, proj_congr _ _ huniq]
  -- good points of a globally bi-Lipschitz chart over a ball (rotated Lipschitz graphs)
  have graph_good : ∀ (G : Rn n → Amb n ℓ) (KG : ℝ≥0), LipschitzWith KG G →
      (∀ a b : Rn n, ‖a - b‖ ≤ ‖G a - G b‖) → ∀ (R : ℝ) (m : ℕ),
      ∀ᵐ x ∂H, x ∈ Kp m → ∀ a ∈ ball (0 : Rn n) R, G a = x → DifferentiableAt ℝ G a →
        Function.Injective (fderiv ℝ G a) →
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
          (LinearMap.range (fderiv ℝ G a : Rn n →ₗ[ℝ] Amb n ℓ)) := by
    intro G KG hG hlow R m
    set A : Set (Rn n) := ball (0 : Rn n) R with hAdef
    have hAm : MeasurableSet A := measurableSet_ball
    have hbiA : ∀ a ∈ A, ∀ b ∈ A, (1 : ℝ) * ‖a - b‖ ≤ ‖G a - G b‖ := fun a _ b _ => by
      rw [one_mul]; exact hlow a b
    have hinjA : InjOn G A := fun b _ c _ h => by
      have h1 := hlow b c
      rw [h, sub_self, norm_zero] at h1
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
    set S := G '' A with hSdef
    have hSm : MeasurableSet S :=
      hAm.image_of_continuousOn_injOn hG.continuous.continuousOn hinjA
    have hSfin : H S < ⊤ := by
      calc H S ≤ (KG : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) A :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              hG.lipschitzOnWith
        _ < ⊤ := by
            rw [hHRn]
            exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) measure_ball_lt_top
    set J := Poincare.SimonGMT.Chapter02.areaJacobianAt G with hJ
    have hgint := jac_integrableOn G hG A hAm hinjA
    have hleb := leb_points (A.indicator J) hgint
    set N : Set (Rn n) := {a | ¬ ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
      ∫ y in closedBall a (ρ * r), ‖A.indicator J y - A.indicator J a‖)
        (𝓝[>] 0) (𝓝 0)} with hN
    have hN0 : volume N = 0 := ae_iff.1 hleb
    have hFN : H (G '' N) = 0 := by
      have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (A := N) n hG.lipschitzOnWith
      rw [hHRn, hN0, mul_zero] at this
      exact le_antisymm this bot_le
    have hKS : H (Kp m \ S) < ⊤ := (measure_mono sdiff_subset).trans_lt (hKfin m)
    have hSK : H (S \ Kp m) < ⊤ := (measure_mono sdiff_subset).trans_lt hSfin
    filter_upwards [wdoc (Kp m) (hKc m) (hKM m),
      ud_tendsto H (Kp m \ S) ((hKc m).measurableSet.diff hSm).nullMeasurableSet hKS,
      ud_tendsto H (S \ Kp m) (hSm.diff (hKc m).measurableSet).nullMeasurableSet hSK,
      measure_eq_zero_iff_ae_notMem.1 hFN] with x hx3 hx4 hx5 hxN hxK a ha hGa hdiff hLinj
    subst hGa
    have hLeb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
        ∫ y in closedBall a (ρ * r), ‖A.indicator J y - A.indicator J a‖)
          (𝓝[>] 0) (𝓝 0) := by
      by_contra h
      exact hxN ⟨a, h, rfl⟩
    set L := fderiv ℝ G a with hL
    set P : Submodule ℝ (Amb n ℓ) := LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) with hPdef
    have hPset : (P : Set (Amb n ℓ)) = Set.range L := by
      rw [hPdef, LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    have hPn : Module.finrank ℝ P = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj).trans
        finrank_euclideanSpace_fin
    -- the density bound for `S`
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
    set C : ℝ := (KG : ℝ) ^ n * c₁ with hCdef
    have hC : 0 ≤ C := by positivity
    have hSball : ∀ r : ℝ, 0 < r → H (S ∩ closedBall (G a) r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro r hr
      have hsub : S ∩ closedBall (G a) r ⊆ G '' (A ∩ closedBall a r) := by
        rintro _ ⟨⟨b, hb, rfl⟩, hbr⟩
        refine ⟨b, ⟨hb, ?_⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm] at hbr ⊢
        exact (hlow b a).trans hbr
      have hvol1 : volume (closedBall (0 : Rn n) 1) = ENNReal.ofReal c₁ :=
        (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
      have hval : (KG : ℝ≥0∞) ^ n * (ENNReal.ofReal (r ^ n) * ENNReal.ofReal c₁) =
          ENNReal.ofReal (C * r ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_pow (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hCdef]
        ring
      calc H (S ∩ closedBall (G a) r) ≤ H (G '' (A ∩ closedBall a r)) := measure_mono hsub
        _ ≤ (KG : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A ∩ closedBall a r) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              hG.lipschitzOnWith
        _ ≤ (KG : ℝ≥0∞) ^ n * volume (closedBall a r) := by
            rw [hHRn]; gcongr; exact inter_subset_right
        _ = ENNReal.ofReal (C * r ^ n) := by
            rw [Measure.addHaar_closedBall' volume a hr.le, finrank_euclideanSpace_fin, hvol1,
              hval]
    refine weighted_tangent_at (Kp m) (hKc m) (hKM m) (hKcont m) (hKfin m) S hSm (G a)
      hxK P hPn (fun f hfc hfs => ?_) C hC hSball (hx3 hxK)
      (hx4 fun h => h.2 ⟨a, ha, rfl⟩) (hx5 fun h => h.2 hxK)
    rw [hPset]
    exact blowup_area_tendsto G hG A hAm one_pos hbiA hgint ha hdiff hLinj hLeb f hfc hfs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (0) existence of the weighted approximate tangent plane
    filter_upwards [hallμ] with x hx
    obtain ⟨m, j, k, i, -, hex, -⟩ := hx
    exact hex
  · -- (1) tangent planes
    filter_upwards [hallμ] with x hx
    obtain ⟨m, j, k, i, -, hex, -⟩ := hx
    refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
    rw [RectifiableVarifold.tangentProj, dif_pos hex]
  · -- (2) measurability
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
  · -- (3) density
    filter_upwards [hallμ, hmem] with x hx hxM
    obtain ⟨m, j, k, i, -, ⟨P, hP⟩, -⟩ := hx
    exact density_of_tangent x hxM P hP
  · -- (4) rotated Lipschitz graphs
    intro q f R L hfL
    obtain ⟨f', hf'L, hff'⟩ := hfL.extend_finite_dimension
    set K' : ℝ≥0 := lipschitzExtensionConstant (Rn ℓ) * L with hK'
    have hgp_sub : ∀ (a b : Rn n) (y z : Rn ℓ),
        graphPoint a y - graphPoint b z = graphPoint (a - b) (y - z) := by
      intro a b y z
      rw [rsod_graphPoint_eq_finAddEquivProd_symm, rsod_graphPoint_eq_finAddEquivProd_symm,
        rsod_graphPoint_eq_finAddEquivProd_symm, ← map_sub, Prod.mk_sub_mk]
    have hgp_norm : ∀ (a : Rn n) (y : Rn ℓ), ‖graphPoint a y‖ ^ 2 = ‖a‖ ^ 2 + ‖y‖ ^ 2 := by
      intro a y
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_add]
      simp [graphPoint]
    set G : Rn n → Amb n ℓ := fun w => q (graphPoint w (f' w)) with hGdef
    have hGsub : ∀ a b, G a - G b = q (graphPoint (a - b) (f' a - f' b)) := by
      intro a b
      simp only [hGdef, ← map_sub, hgp_sub]
    have hGlow : ∀ a b : Rn n, ‖a - b‖ ≤ ‖G a - G b‖ := by
      intro a b
      rw [hGsub, LinearIsometryEquiv.norm_map]
      have h := hgp_norm (a - b) (f' a - f' b)
      nlinarith [norm_nonneg (a - b), norm_nonneg (graphPoint (a - b) (f' a - f' b)),
        sq_nonneg ‖f' a - f' b‖]
    have hGlip : LipschitzWith (1 + K') G := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_eq_norm, dist_eq_norm, hGsub, LinearIsometryEquiv.norm_map]
      have h := hgp_norm (a - b) (f' a - f' b)
      have h2 : ‖f' a - f' b‖ ≤ K' * ‖a - b‖ := by
        have := hf'L.dist_le_mul a b
        rwa [dist_eq_norm, dist_eq_norm] at this
      have h3 : ‖graphPoint (a - b) (f' a - f' b)‖ ≤ ‖a - b‖ + ‖f' a - f' b‖ := by
        nlinarith [norm_nonneg (a - b), norm_nonneg (graphPoint (a - b) (f' a - f' b)),
          norm_nonneg (f' a - f' b)]
      push_cast
      nlinarith
    have hgg : ∀ᵐ x ∂V.weight, ∀ m, x ∈ Kp m → ∀ a ∈ ball (0 : Rn n) R, G a = x →
        DifferentiableAt ℝ G a → Function.Injective (fderiv ℝ G a) →
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
          (LinearMap.range (fderiv ℝ G a : Rn n →ₗ[ℝ] Amb n ℓ)) :=
      hacH.ae_le (ae_all_iff.2 fun m => graph_good G (1 + K') hGlip hGlow R m)
    filter_upwards [hgg, hallμ, hmem] with x hx hxall hxM x' hx' hxeq hdiff
    obtain ⟨m, j, k, i, ⟨hxm, -⟩, -⟩ := hxall
    have hev : f' =ᶠ[𝓝 x'] f := by
      filter_upwards [isOpen_ball.mem_nhds hx'] with w hw
      exact (hff' (ball_subset_closedBall hw)).symm
    have hdiff' : DifferentiableAt ℝ f' x' := hdiff.congr_of_eventuallyEq hev
    have hfd : fderiv ℝ f' x' = fderiv ℝ f x' := hev.fderiv_eq
    have hGx : G x' = x := by
      show q (graphPoint x' (f' x')) = x
      rw [← hff' (ball_subset_closedBall hx'), hxeq]
    -- the derivative of the graph map
    set DG : Rn n →L[ℝ] Amb n ℓ := (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      (((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
        Rn n × Rn ℓ →L[ℝ] Amb n ℓ).comp
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f x'))) with hDG
    have hGeq : G = fun w =>
        q ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (w, f' w)) := by
      funext w
      simp only [hGdef, rsod_graphPoint_eq_finAddEquivProd_symm]
    have hGd : HasFDerivAt G DG x' := by
      rw [hGeq]
      have h1 : HasFDerivAt (fun w : Rn n => (w, f' w))
          ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f x')) x' := by
        rw [← hfd]
        exact (hasFDerivAt_id x').prodMk hdiff'.hasFDerivAt
      exact q.toContinuousLinearEquiv.hasFDerivAt.comp x'
        ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm.hasFDerivAt.comp x' h1)
    have hDGv : ∀ v, DG v = q (graphPoint v (fderiv ℝ f x' v)) := by
      intro v
      rw [rsod_graphPoint_eq_finAddEquivProd_symm]
      rfl
    have hDGinj : Function.Injective DG := by
      intro v w hvw
      have h0 : DG (v - w) = 0 := by rw [map_sub, hvw, sub_self]
      rw [hDGv, LinearIsometryEquiv.map_eq_zero_iff] at h0
      have h := hgp_norm (v - w) (fderiv ℝ f x' (v - w))
      rw [h0, norm_zero] at h
      have h1 : ‖v - w‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖v - w‖, sq_nonneg ‖fderiv ℝ f x' (v - w)‖]
      exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1))
    have hW := hx m hxm x' hx' hGx hGd.differentiableAt (by rw [hGd.fderiv]; exact hDGinj)
    rw [hGd.fderiv] at hW
    rw [tangentProj_eq x hxM _ hW]
    refine proj_congr _ _ ?_
    have hfun : (fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v))) =
        ⇑(DG : Rn n →ₗ[ℝ] Amb n ℓ) := by
      funext v
      rw [ContinuousLinearMap.coe_coe, hDGv]
    rw [hfun, ← LinearMap.coe_range, Submodule.span_eq]
/-- **Affine approximation of almost-harmonic Lipschitz maps** (Simon Ch. 5, proof of
Theorem 4.5, steps (17)–(19)).  Assume the Harmonic Approximation Lemma 3.1.  For `n ≥ 1` and `ℓ`
there is `C = C(n, ℓ) > 0` such that for every `ε ∈ (0, 1)` there is `δ_ε > 0` with the following
property: if `f : ℝⁿ → ℝ^ℓ` is Lipschitz on `B_r(0)`, `|f| ≤ h` on `B̆_r(0)`,
`∫_{B̆_r} |Df|² ≤ E rⁿ` and `|∫_{B̆_r} ∇fʲ · ∇ζ| ≤ δ_ε √E sup|∇ζ| rⁿ` for all `ζ ∈ C^∞_c(B̆_r)`,
then there are `a ∈ ℝ^ℓ` and a linear `A` with `|A| ≤ C √E`, `|a| ≤ C (h + r √(εE))` and
`∫_{B̆_{er}} |f - (a + A x)|² ≤ C (ε + e^{n+4}) E r^{n+2}` for `e ∈ (0, 1/4]`.

Proof: rescale each component to `F_j(z) = fʲ(rz)/(r√E)`, apply Lemma 3.1 to get harmonic `u_j`,
and use interior estimates for harmonic functions, proved here from the mean value property
`∫ u(x + y) φ(y) dy = (∫ φ) u(x)` for a smooth radial kernel `φ` (scaling argument plus Lipschitz
integration by parts), to define `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0) · x)_j`. -/
theorem ted_harmonic_affine_approx : HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δε : ℝ, 0 < δε ∧ ∀ (r E h : ℝ) (f : Rn n → Rn ℓ) (L : ℝ≥0), 0 < r → 0 < E → 0 ≤ h → LipschitzOnWith L f (closedBall 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖f x‖ ≤ h) → ∫ x in ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ E * r ^ n → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 r → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) r, inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ δε * Real.sqrt E * M * r ^ n) → ∃ (a : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ C * Real.sqrt E ∧ ‖a‖ ≤ C * (h + r * Real.sqrt (ε * E)) ∧ ∀ e : ℝ, 0 < e → e ≤ 1 / 4 → ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
  intro hHAL n ℓ hn
  -- elementary inequalities, proved once in the small initial context
  have hsq2 : ∀ X Y D : ℝ, Y ^ 2 ≤ D ^ 2 → (X + Y) ^ 2 ≤ 2 * (X ^ 2 + D ^ 2) := fun X Y D h =>
    add_sq_le.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h) zero_le_two)
  have hKP : ∀ K P ε : ℝ, 0 ≤ K → 0 ≤ P → 0 ≤ ε → ε + K * P ≤ (1 + K) * (ε + P) :=
    fun K P ε hK hP hε => by
      calc ε + K * P ≤ ε + K * P + (P + K * ε) :=
            le_add_of_nonneg_right (add_nonneg hP (mul_nonneg hK hε))
        _ = (1 + K) * (ε + P) := by ring
  have hab : ∀ a b x y : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ x → 0 ≤ y → a * y + b * x ≤ (a + b) * (x + y) :=
    fun a b x y ha hb hx hy => by
      calc a * y + b * x ≤ a * y + b * x + (a * x + b * y) :=
            le_add_of_nonneg_right (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy))
        _ = (a + b) * (x + y) := by ring
  -- the Hilbert–Schmidt norm is controlled by the operator norm
  have hHS : ∀ A : Rn n →L[ℝ] Rn ℓ, hsNormSq A ≤ n * ‖A‖ ^ 2 := fun A => by
    unfold hsNormSq
    calc ∑ i : Fin n, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin n, ‖A‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            ((A.le_opNorm _).trans (by rw [EuclideanSpace.norm_single, norm_one, mul_one])) 2)
      _ = n * ‖A‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  /- Steps 1–5 (interior estimates for harmonic functions, Simon 3.2–3.4), proved from the mean
  value property for a smooth radial kernel. -/
  obtain ⟨C₁, C₃, hC₁, hC₃, HE⟩ : ∃ C₁ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₃ ∧
      ∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) →
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖u x‖ₑ ≤ ENNReal.ofReal M → |u 0| ≤ C₁ * M) ∧
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ≤ ENNReal.ofReal M →
        ‖gradient u 0‖ ≤ C₁ * M ∧
        ∀ z : Rn n, ‖z‖ ≤ 1/4 → |u z - u 0 - inner ℝ (gradient u 0) z| ≤ C₃ * M * ‖z‖ ^ 2) := by
    /- Step 1 (kernel).  `φ(y) = -64 τ'(1 - 32|y|²)` and its potential `Ψ(y) = τ(1 - 32|y|²)`
    (`τ` = `Real.smoothTransition`), so that `∂_v Ψ(y) = φ(y) ⟪y, v⟫`; both vanish off `B_{1/5}`. -/
    obtain ⟨φ, Ψ, Lφ, LΨ, Φ, hφc, hφ0, hφcs, hφL, hΦ, hc0, hΨL, hΨcs, hΨl, hΨ0⟩ :
        ∃ (φ Ψ : Rn n → ℝ) (Lφ LΨ : ℝ≥0) (Φ : ℝ), Continuous φ ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → φ y = 0) ∧ HasCompactSupport φ ∧ LipschitzWith Lφ φ ∧
          (∀ y, ‖φ y‖ ≤ Φ) ∧
          (∫ y, φ y) ≠ 0 ∧ LipschitzWith LΨ Ψ ∧ HasCompactSupport Ψ ∧
          (∀ y v : Rn n, HasLineDerivAt ℝ Ψ (φ y * inner ℝ y v) y v) ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → Ψ y = 0) := by
      have hτ : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
      have hτd : ∀ s, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
        fun s => ((hτ.differentiable (by simp)) s).hasDerivAt
      have hτ'0 : ∀ s : ℝ, s < 0 → deriv Real.smoothTransition s = 0 := fun s hs => by
        rw [(Filter.eventuallyEq_of_mem (Iio_mem_nhds hs)
          (fun z hz => Real.smoothTransition.zero_of_nonpos (le_of_lt hz))).deriv_eq]
        exact deriv_const s 0
      have hq : ∀ y : Rn n, 1/5 ≤ ‖y‖ → 1 - 32 * ‖y‖ ^ 2 < 0 := fun y hy => by nlinarith
      have hnsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => 1 - 32 * ‖y‖ ^ 2) :=
        contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
      have hφs : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Rn n => -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        contDiff_const.mul (((contDiff_infty_iff_deriv.1 hτ).2).comp hnsq)
      have hΨs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        hτ.comp hnsq
      have hφ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ →
          -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => by rw [hτ'0 _ (hq y hy), mul_zero]
      have hΨ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ → Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => Real.smoothTransition.zero_of_nonpos (hq y hy).le
      have hcs : ∀ g : Rn n → ℝ, (∀ y : Rn n, 1/5 ≤ ‖y‖ → g y = 0) → HasCompactSupport g :=
        fun g hg => HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1/5)) (fun y hy =>
          hg y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le))
      have hφcs := hcs _ hφ0
      have hΨcs := hcs _ hΨ0
      obtain ⟨Lφ, hφL⟩ := hφs.lipschitzWith_of_hasCompactSupport hφcs (by simp)
      obtain ⟨LΨ, hΨL⟩ := hΨs.lipschitzWith_of_hasCompactSupport hΨcs (by simp)
      obtain ⟨Φ, hΦ⟩ := hφcs.exists_bound_of_continuous hφs.continuous
      refine ⟨_, _, Lφ, LΨ, Φ, hφs.continuous, hφ0, hφcs, hφL, hΦ, ?_, hΨL, hΨcs, fun y v => ?_, hΨ0⟩
      · -- `∫ φ < 0`, since `-φ ≥ 0` and `τ'(c) = 1` for some `c ∈ (0, 1)`
        obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.smoothTransition
          (deriv Real.smoothTransition) (zero_lt_one' ℝ) hτ.continuous.continuousOn
          (fun x _ => hτd x)
        simp only [Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero, div_one] at hcd
        have hy1 : ‖Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ ^ 2
            = (1 - c) / 32 := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith [hc.2])]
        have hpos : 0 < ∫ y : Rn n, -(-64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
          Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (μ := (volume : Measure (Rn n)))
          (x := Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
          hφs.continuous.neg hφcs.neg
          (fun y => neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
            (Real.smoothTransition.monotone.deriv_nonneg)))
          (by
            show -(-64 * deriv Real.smoothTransition (1 - 32 * _)) ≠ 0
            rw [hy1, show (1:ℝ) - 32 * ((1 - c) / 32) = c by ring, hcd]
            norm_num)
        rw [integral_neg] at hpos
        exact (neg_pos.1 hpos).ne
      · -- the line derivative of `Ψ`
        refine HasDerivAt.congr_deriv (((hτd _).comp_hasFDerivAt y
          (((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (32:ℝ)).const_sub 1)).hasLineDerivAt
            v) ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
          innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        ring
    have hc0' : 0 < |∫ y, φ y| := abs_pos.2 hc0
    have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0)
    refine ⟨|∫ y, φ y|⁻¹ * Φ, |∫ y, φ y|⁻¹ * Lφ, mul_nonneg (inv_nonneg.2 hc0'.le) hΦ0,
      mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2, fun u hu => ?_⟩
    /- Step 2: smoothness of `u`, `Δu = 0`, and a bound for `Du` on `B_{9/10}`. -/
    have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
    have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
      ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
        |>.hasFDerivAt
    have hD1 : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).1 hC2).2.2
    have hD1c : ContinuousOn (fderiv ℝ u) (ball 0 1) := hD1.continuousOn
    have hD2 : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
      fun z hz => ((hD1.differentiableOn one_ne_zero) z hz).differentiableAt
        (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
    have hlap : ∀ z ∈ ball (0 : Rn n) 1, ∑ i, fderiv ℝ (fderiv ℝ u) z (b i) (b i) = 0 := by
      intro z hz
      have h0 : Laplacian.laplacian u z = 0 := (hu z hz).2.eq_of_nhds
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b] at h0
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using h0
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ z ∈ closedBall (0 : Rn n) (9/10), ‖fderiv ℝ u z‖ ≤ M1 :=
      (isCompact_closedBall 0 (9/10)).exists_bound_of_continuousOn
        (hD1c.mono (closedBall_subset_ball (by norm_num)))
    have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (mem_closedBall_self (by norm_num)))
    have huc : ContinuousOn u (ball 0 1) := hC2.continuousOn
    set B := closedBall (0 : Rn n) (1/5) with hB
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hφB : ∀ y ∉ B, φ y = 0 := fun y hy =>
      hφ0 y (by rw [hB, mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
    have h910 : closedBall (0 : Rn n) (9/10) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    have hgeo : ∀ x : Rn n, ‖x‖ < 1/2 → ∀ s : ℝ, |s| ≤ 2 → ∀ y ∈ B,
        x + s • y ∈ closedBall (0 : Rn n) (9/10) := by
      intro x hx s hs y hy
      rw [hB, mem_closedBall, dist_zero_right] at hy
      rw [mem_closedBall, dist_zero_right]
      calc ‖x + s • y‖ ≤ ‖x‖ + |s| * ‖y‖ := by
            rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
        _ ≤ 1/2 + 2 * (1/5) := add_le_add hx.le (mul_le_mul hs hy (norm_nonneg _) zero_le_two)
        _ = 9/10 := by norm_num
    have hpath1 : ∀ x : Rn n, ‖x‖ < 1/2 → MapsTo (fun y : Rn n => x + y) B (ball 0 1) :=
      fun x hx y hy => h910 (by have h := hgeo x hx 1 (by norm_num) y hy; rwa [one_smul] at h)
    have hsr : ∀ (L : Rn n →L[ℝ] ℝ) (w : Rn n), L w = ∑ i, inner ℝ (b i) w * L (b i) := by
      intro L w
      conv_lhs => rw [← b.sum_repr' w]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hpc1 : ∀ x' : Rn n, Continuous (fun y : Rn n => x' + y) := fun x' =>
      continuous_const.add continuous_id
    /- Step 3 (mean value property): `∫ φ(y) u(x + y) dy = (∫ φ) u(x)` for `‖x‖ < 1/2`.  The
    derivative of `t ↦ ∫_B φ(y) u(x + t y) dy` is `∫_B φ(y) Du(x + t y)[y] dy`, which vanishes by
    Lipschitz integration by parts against `Ψ` (`∂_v Ψ = φ ⟪·, v⟫`) and `Δu = 0`. -/
    have hMVP : ∀ x : Rn n, ‖x‖ < 1/2 → ∫ y, φ y * u (x + y) = (∫ y, φ y) * u x := by
      intro x hx
      have hpath : ∀ s : ℝ, |s| ≤ 2 → MapsTo (fun y : Rn n => x + s • y) B (ball 0 1) :=
        fun s hs y hy => h910 (hgeo x hx s hs y hy)
      have hpc : ∀ s : ℝ, ContDiff ℝ 1 (fun y : Rn n => x + s • y) := fun s =>
        contDiff_const.add (contDiff_id.const_smul s)
      have hcF : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * u (x + s • y)) B := fun s hs =>
        hφc.continuousOn.mul (huc.comp (hpc s).continuous.continuousOn (hpath s hs))
      have hcF' : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * fderiv ℝ u (x + s • y) y) B :=
        fun s hs => hφc.continuousOn.mul ((hD1c.comp (hpc s).continuous.continuousOn
          (hpath s hs)).clm_apply continuousOn_id)
      -- the radial derivative vanishes
      have hzero : ∀ t : ℝ, |t| ≤ 2 → ∫ y in B, φ y * fderiv ℝ u (x + t • y) y = 0 := by
        intro t ht
        have hin : ∀ y : Rn n, ‖y‖ ≤ 1/4 → x + t • y ∈ ball (0 : Rn n) 1 := fun y hy => by
          rw [mem_ball, dist_zero_right]
          calc ‖x + t • y‖ ≤ ‖x‖ + |t| * ‖y‖ := by
                rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
            _ ≤ ‖x‖ + 2 * (1/4) := add_le_add le_rfl (mul_le_mul ht hy (norm_nonneg _) zero_le_two)
            _ < 1 := by linarith
        have hext : ∀ i : Fin n, ∃ (K : ℝ≥0) (W : Rn n → ℝ), LipschitzWith K W ∧
            EqOn (fun y => fderiv ℝ u (x + t • y) (b i)) W (closedBall 0 (1/4)) := by
          intro i
          have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u (x + t • y) (b i)) (closedBall 0 (1/4)) :=
            (hD1.comp (hpc t).contDiffOn (fun y hy => hin y (mem_closedBall_zero_iff.1 hy))).clm_apply
              contDiffOn_const
          obtain ⟨K, hK⟩ := h2.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
            (isCompact_closedBall _ _)
          obtain ⟨W, hW, hEq⟩ := hK.extend_real
          exact ⟨_, W, hW, hEq⟩
        choose K W hWL hWeq using hext
        have hibp : ∀ i, ∫ y, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, lineDeriv ℝ Ψ y (-(b i)) * W i y :=
          fun i => (hWL i).integral_lineDeriv_mul_eq hΨL hΨcs (b i)
        have hL : ∀ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y = 0 := by
          intro y
          by_cases hy : ‖y‖ < 1/4
          · have hz := hin y hy.le
            have hnhd : closedBall (0 : Rn n) (1/4) ∈ 𝓝 y :=
              closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 hy)
            have hline : ∀ i, lineDeriv ℝ (W i) y (b i) =
                t * fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) := by
              intro i
              have hc := ((hD2 _ hz).comp y (((hasFDerivAt_id y).const_smul t).const_add x)).clm_apply
                (hasFDerivAt_const (b i) y)
              rw [((hc.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hnhd
                (fun z hz => (hWeq i hz).symm))).hasLineDerivAt (b i)).lineDeriv]
              simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
            simp only [hline]
            rw [← Finset.sum_mul, ← Finset.mul_sum, hlap _ hz, mul_zero, zero_mul]
          · simp only [hΨ0 y (le_trans (by norm_num) (not_lt.1 hy)), mul_zero, Finset.sum_const_zero]
        have hR : ∀ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y = -(φ y * fderiv ℝ u (x + t • y) y) := by
          intro y
          have hl : ∀ i, lineDeriv ℝ Ψ y (-(b i)) = -(φ y * inner ℝ y (b i)) := fun i => by
            rw [(hΨl y _).lineDeriv, inner_neg_right, mul_neg]
          simp only [hl]
          by_cases hy : ‖y‖ ≤ 1/4
          · have hWy : ∀ i, W i y = fderiv ℝ u (x + t • y) (b i) := fun i =>
              (hWeq i (mem_closedBall_zero_iff.2 hy)).symm
            simp only [hWy]
            rw [hsr (fderiv ℝ u (x + t • y)) y, Finset.mul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm]
            ring
          · simp only [hφ0 y (le_trans (by norm_num) (not_le.1 hy).le), zero_mul, neg_zero,
              Finset.sum_const_zero]
        have hΨi : Integrable Ψ := hΨL.continuous.integrable_of_hasCompactSupport hΨcs
        have hLi : ∀ i, Integrable (fun y => lineDeriv ℝ (W i) y (b i) * Ψ y) :=
          fun i => hΨi.mul_of_top_right ((hWL i).memLp_lineDeriv (b i))
        have hRi : ∀ i, Integrable (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) := by
          intro i
          have hfun : (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) =
              fun y => φ y * (inner ℝ y (-(b i)) * W i y) := by
            funext y; rw [(hΨl y _).lineDeriv, mul_assoc]
          rw [hfun]
          exact (hφc.mul ((continuous_id.inner continuous_const).mul (hWL i).continuous)
            ).integrable_of_hasCompactSupport hφcs.mul_right
        have h1 : ∫ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y := by
          rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
          exact Finset.sum_congr rfl (fun i _ => hibp i)
        simp only [hL, hR, integral_zero, integral_neg] at h1
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact neg_eq_zero.1 h1.symm
      -- differentiation under the integral sign
      have hIoo : ∀ s ∈ Ioo (-2:ℝ) 2, |s| ≤ 2 := fun s hs => abs_le.2 ⟨hs.1.le, hs.2.le⟩
      have hderiv : ∀ t ∈ Ioo (-2:ℝ) 2, HasDerivAt (fun t => ∫ y in B, φ y * u (x + t • y))
          (∫ y in B, φ y * fderiv ℝ u (x + t • y) y) t := by
        intro t ht
        refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
          (F := fun t y => φ y * u (x + t • y)) (F' := fun t y => φ y * fderiv ℝ u (x + t • y) y)
          (bound := fun _ => Φ * (M1 * (1/5))) ?_
          ((hcF t (hIoo t ht)).integrableOn_compact (isCompact_closedBall _ _))
          ((hcF' t (hIoo t ht)).aestronglyMeasurable measurableSet_closedBall) ?_
          (integrable_const _) ?_).2
        · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact (hcF s (hIoo s hs)).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          rw [norm_mul]
          exact mul_le_mul (hΦ y) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hM1 _ (hgeo x hx s (hIoo s hs) y hy)) (mem_closedBall_zero_iff.1 hy)
              (norm_nonneg _) hM1')) (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          exact ((hdiff _ (hpath s (hIoo s hs) hy)).comp_hasDerivAt s
            ((((hasDerivAt_id s).smul_const y).const_add x).congr_deriv (one_smul ℝ y))).const_mul
              (φ y)
      -- mean value theorem in `t`
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y in B, φ y * u (x + t • y))
        (fun t => ∫ y in B, φ y * fderiv ℝ u (x + t • y) y) (zero_lt_one' ℝ)
        (fun t ht => (hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
        (fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hcd
      rw [hzero c (abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩), integral_mul_const,
        setIntegral_eq_integral_of_forall_compl_eq_zero hφB,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])] at hcd
      exact sub_eq_zero.1 hcd.symm
    /- Step 4: differentiating the mean value identity, `(∫ φ) Du(x) = ∫ φ(y) Du(x + y) dy`. -/
    have hdMVP : ∀ x : Rn n, ‖x‖ < 1/2 →
        (∫ y, φ y) • fderiv ℝ u x = ∫ y, φ y • fderiv ℝ u (x + y) := by
      intro x hx
      have hδ : 0 < 1/2 - ‖x‖ := by linarith
      have hsm : ∀ x' ∈ ball x (1/2 - ‖x‖), ‖x'‖ < 1/2 := fun x' hx' => by
        rw [mem_ball, dist_eq_norm] at hx'
        linarith [norm_sub_norm_le x' x]
      have hcF : ∀ x' : Rn n, ‖x'‖ < 1/2 → ContinuousOn (fun y => φ y * u (x' + y)) B :=
        fun x' hx' => hφc.continuousOn.mul (huc.comp (hpc1 x').continuousOn (hpath1 x' hx'))
      have hP : HasFDerivAt (fun x' => ∫ y in B, φ y * u (x' + y))
          (∫ y in B, φ y • fderiv ℝ u (x + y)) x := by
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => Φ * M1)
          (F := fun x' y => φ y * u (x' + y)) (F' := fun x' y => φ y • fderiv ℝ u (x' + y))
          (ball_mem_nhds x hδ) ?_ ((hcF x hx).integrableOn_compact (isCompact_closedBall _ _)) ?_ ?_
          (integrable_const _) ?_
        · filter_upwards [ball_mem_nhds x hδ] with x' hx'
          exact (hcF x' (hsm x' hx')).aestronglyMeasurable measurableSet_closedBall
        · exact (hφc.continuousOn.smul (hD1c.comp (hpc1 x).continuousOn
            (hpath1 x hx))).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          rw [norm_smul]
          exact mul_le_mul (hΦ y) (hM1 _ (by
            have h := hgeo x' (hsm x' hx') 1 (by norm_num) y hy; rwa [one_smul] at h))
            (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          have h := ((hdiff _ (hpath1 x' (hsm x' hx') hy)).comp x'
            ((hasFDerivAt_id x').add_const y)).const_mul (φ y)
          rwa [ContinuousLinearMap.comp_id] at h
      have heq : (fun x' => ∫ y in B, φ y * u (x' + y)) =ᶠ[𝓝 x] fun x' => (∫ y, φ y) * u x' := by
        filter_upwards [ball_mem_nhds x hδ] with x' hx'
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact hMVP x' (hsm x' hx')
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (f := fun y => φ y • fderiv ℝ u (x + y)) (fun y hy => by rw [hφB y hy, zero_smul])]
      exact ((hdiff x (mem_ball_zero_iff.2 (by linarith))).const_mul (∫ y, φ y)).unique
        (hP.congr_of_eventuallyEq heq.symm)
    /- Step 5: the estimates. -/
    have hgen : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (ψ : Rn n → ℝ) (K : ℝ),
        0 ≤ K → (∀ y, ‖ψ y‖ ≤ K) → (∀ y ∉ ball (0 : Rn n) 1, ψ y = 0) →
        ∀ (G : Rn n → X) (M : ℝ), 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖G x‖ₑ ≤ ENNReal.ofReal M →
        ‖∫ y, ψ y • G y‖ ≤ K * M := by
      intro X _ _ ψ K hK hψ hψ0 G M hM hGM
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1)
        (fun y hy => by rw [hψ0 y hy, zero_smul])]
      refine (norm_integral_le_lintegral_norm _).trans
        (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hM) ?_)
      calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ‖ψ y • G y‖
          ≤ ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal K * ‖G y‖ₑ := by
            refine lintegral_mono (fun y => ?_)
            rw [norm_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm (G y)]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hψ y)) _
        _ = ENNReal.ofReal K * ∫⁻ y in ball (0 : Rn n) 1, ‖G y‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal M := mul_le_mul_right hGM _
        _ = ENNReal.ofReal (K * M) := (ENNReal.ofReal_mul hK).symm
    have hφ1 : ∀ y ∉ ball (0 : Rn n) 1, φ y = 0 := fun y hy =>
      hφ0 y (le_trans (by norm_num) (not_lt.1 (mt mem_ball_zero_iff.2 hy)))
    have h00 : ‖(0 : Rn n)‖ < 1/2 := by rw [norm_zero]; norm_num
    refine ⟨fun M hM huM => ?_, fun M hM huM => ?_⟩
    · -- the value at the origin
      have h1 := hMVP 0 h00
      have h2 := hgen φ Φ hΦ0 hΦ hφ1 u M hM huM
      simp only [zero_add, smul_eq_mul] at h1 h2
      rw [h1, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h2
      rw [mul_assoc, le_inv_mul_iff₀ hc0']
      exact h2
    · have hgn : ∀ x, ‖gradient u x‖ₑ = ‖fderiv ℝ u x‖ₑ := fun x => by
        rw [← ofReal_norm, ← ofReal_norm]
        exact congrArg ENNReal.ofReal ((InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _)
      simp only [hgn] at huM
      have hDu0 : ‖fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Φ * M := by
        have h1 := hdMVP 0 h00
        have h2 := hgen φ Φ hΦ0 hΦ hφ1 (fderiv ℝ u) M hM huM
        simp only [zero_add] at h1
        rw [← h1, norm_smul, Real.norm_eq_abs] at h2
        rw [mul_assoc, le_inv_mul_iff₀ hc0']
        exact h2
      have hint : ∀ z : Rn n, ‖z‖ < 1/2 → Integrable (fun w => φ (w - z) • fderiv ℝ u w) := by
        intro z hz
        have hc : ContinuousOn (fun y => φ y • fderiv ℝ u (z + y)) B :=
          hφc.continuousOn.smul (hD1c.comp (hpc1 z).continuousOn (hpath1 z hz))
        have h := (hc.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero
            (fun y hy => by rw [hφB y hy, zero_smul])
        simpa only [add_sub_cancel] using h.comp_sub_right z
      have hshift : ∀ z : Rn n, ∫ y, φ y • fderiv ℝ u (z + y) = ∫ w, φ (w - z) • fderiv ℝ u w := by
        intro z
        have h := integral_add_left_eq_self (μ := (volume : Measure (Rn n)))
          (fun w => φ (w - z) • fderiv ℝ u w) z
        simp only [add_sub_cancel_left] at h
        exact h
      have hLipD : ∀ z : Rn n, ‖z‖ ≤ 1/4 →
          ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ := by
        intro z hz
        have hz2 : ‖z‖ < 1/2 := by linarith
        have h1 := hdMVP z hz2
        have h0 := hdMVP 0 h00
        rw [hshift] at h1 h0
        have hdiffeq : (∫ y, φ y) • (fderiv ℝ u z - fderiv ℝ u 0) =
            ∫ w, (φ (w - z) - φ (w - 0)) • fderiv ℝ u w := by
          rw [smul_sub, h1, h0, ← integral_sub (hint z hz2) (hint 0 h00)]
          simp only [sub_smul]
        have hb := hgen (fun w => φ (w - z) - φ (w - 0)) (Lφ * ‖z‖)
          (mul_nonneg Lφ.2 (norm_nonneg _))
          (fun w => by
            have h := hφL.dist_le_mul (w - z) (w - 0)
            rwa [dist_eq_norm, dist_sub_left, dist_zero_right] at h)
          (fun w hw => by
            have hw1 : 1 ≤ ‖w‖ := not_lt.1 (mt mem_ball_zero_iff.2 hw)
            rw [hφ0 (w - z) (by linarith [norm_sub_norm_le w z]), sub_zero,
              hφ0 w (by linarith), sub_self])
          (fderiv ℝ u) M hM huM
        rw [← hdiffeq, norm_smul, Real.norm_eq_abs] at hb
        rw [show |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ = |∫ y, φ y|⁻¹ * (Lφ * ‖z‖ * M) by ring,
          le_inv_mul_iff₀ hc0']
        exact hb
      refine ⟨(InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _ ▸ hDu0, fun z hz => ?_⟩
      rw [show inner ℝ (gradient u 0) z = fderiv ℝ u 0 z from
        InnerProductSpace.toDual_symm_apply]
      have hK0 : 0 ≤ |∫ y, φ y|⁻¹ * Lφ * M := mul_nonneg (mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2) hM
      have hs : closedBall (0 : Rn n) ‖z‖ ⊆ ball 0 1 := closedBall_subset_ball (by linarith)
      have hmvt := (convex_closedBall (0 : Rn n) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun y => u y - fderiv ℝ u 0 y) (f' := fun y => fderiv ℝ u y - fderiv ℝ u 0)
        (C := |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖)
        (fun y hy => ((hdiff y (hs hy)).sub (fderiv ℝ u 0).hasFDerivAt).hasFDerivWithinAt)
        (fun y hy => (hLipD y ((mem_closedBall_zero_iff.1 hy).trans hz)).trans
          (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) hK0))
        (mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.2 le_rfl)
      simp only [map_zero, sub_zero, Real.norm_eq_abs] at hmvt
      rw [sub_right_comm, sq, ← mul_assoc]
      exact hmvt
  /- Step 6 (Cauchy–Schwarz on `B₁`): `∫_{B₁} g ≤ (ω_n S)^{1/2}` when `∫_{B₁} g² ≤ S`. -/
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (ball (0 : Rn n) 1)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ ENNReal.toReal_nonneg
  have CS : ∀ g : Rn n → ℝ≥0∞, AEMeasurable g (volume.restrict (ball (0 : Rn n) 1)) →
      ∀ S : ℝ, 0 ≤ S → ∫⁻ x in ball (0 : Rn n) 1, g x ^ 2 ≤ ENNReal.ofReal S →
      ∫⁻ x in ball (0 : Rn n) 1, g x ≤ ENNReal.ofReal (Real.sqrt V * Real.sqrt S) := by
    intro g hg S hS hgS
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball (0 : Rn n) 1))
      Real.HolderConjugate.two_two hg aemeasurable_const (f := g) (g := fun _ => (1 : ℝ≥0∞))
    simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.rpow_two, one_pow, one_mul] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm (ENNReal.ofReal _)]
    gcongr
    · calc (∫⁻ x in ball (0 : Rn n) 1, g x ^ 2) ^ (1 / (2 : ℝ))
          ≤ (ENNReal.ofReal S) ^ (1 / (2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (Real.sqrt S) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]
    · rw [hVdef, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num), ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  /- Step 7: the constant `C` (depending on `n, ℓ` only) and `δ_ε` (from Lemma 3.1). -/
  obtain ⟨C, hCpos, hC1, hC2, hC3⟩ : ∃ C : ℝ, 0 < C ∧
      Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) ≤ C ∧ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) ≤ C ∧
      2 * ℓ * (1 + C₃ ^ 2 * V ^ 2) ≤ C := by
    have h1 : 0 ≤ Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ (Real.sqrt_nonneg _)))
    have h2 : 0 ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₁) (add_nonneg (Real.sqrt_nonneg _) hV0)
    have h3 : 0 ≤ 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) :=
      mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
        (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact ⟨1 + Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) + Real.sqrt ℓ * C₁ * (Real.sqrt V + V) +
        2 * ℓ * (1 + C₃ ^ 2 * V ^ 2),
      add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos h1) h2) h3,
      ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right h2)).trans
        (le_add_of_nonneg_right h3),
      (le_add_of_nonneg_left (add_nonneg zero_le_one h1)).trans (le_add_of_nonneg_right h3),
      le_add_of_nonneg_left (add_nonneg (add_nonneg zero_le_one h1) h2)⟩
  refine ⟨C, hCpos, ?_⟩
  intro ε hε _hε1
  obtain ⟨δ, hδ, hHA⟩ := hHAL n hn ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r E h f L hr hE hh hLip hbound henergy halmost
  /- Step 8: for each component `j`, `F_j(z) = f(rz)_j / (r√E)` (extended from `B₁` as a
  Lipschitz function) satisfies the hypotheses of Lemma 3.1 (`W^{1,2}` with weak gradient,
  energy `≤ 1`, `δ`-almost harmonic), giving a harmonic `u_j` with `∫_{B₁}|∇u_j|² ≤ 1` and
  `∫_{B₁}|u_j - F_j|² ≤ ε`. -/
  have hcomp : ∀ j : Fin ℓ, ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - (r * Real.sqrt E)⁻¹ * f (r • x) j‖ₑ ^ 2 ≤
        ENNReal.ofReal ε := by
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
    have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
    have hcr : c * r = (Real.sqrt E)⁻¹ := by
      rw [hc, mul_inv, mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]
    have hsB : ∀ z ∈ closedBall (0 : Rn n) 1, r • z ∈ closedBall (0 : Rn n) r := fun z hz => by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.1 hz)
    have hsB' : ∀ z ∈ ball (0 : Rn n) 1, r • z ∈ ball (0 : Rn n) r := fun z hz => by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)
    have hgmeas : ∀ g : Rn n → ℝ, Measurable (gradient g) := fun g =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have hng : ∀ (g : Rn n → ℝ) (z : Rn n), ‖gradient g z‖ = ‖fderiv ℝ g z‖ := fun g z =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _
    have hig : ∀ (g : Rn n → ℝ) (z w : Rn n), inner ℝ (gradient g z) w = fderiv ℝ g z w :=
      fun g z w => InnerProductSpace.toDual_symm_apply
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    -- `|Df|²_{HS}` is integrable on `B_r` (it is bounded by `n L²`)
    have hHSint : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) r) := by
      have hcont : Continuous (fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A) :=
        continuous_finsetSum _ (fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2)
      refine Integrable.of_bound (hcont.measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable
        (n * L ^ 2) ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall
          (fun x hx => ?_)))
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      exact (hHS _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx) hLip) 2) (Nat.cast_nonneg _))
    -- `f` is differentiable a.e. on `B_r` (Rademacher)
    have hfdiff : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)), DifferentiableAt ℝ f x := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxB
      exact (hx (ball_subset_closedBall hxB)).differentiableAt (closedBall_mem_nhds_of_mem hxB)
    intro j
    obtain ⟨fj, hfj⟩ : ∃ g : Rn n → ℝ, g = fun y => f y j := ⟨_, rfl⟩
    have hcoord : ∀ v : Rn ℓ, |v j| ≤ ‖v‖ := fun v => by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    -- `F z = c fʲ(r z)` is Lipschitz on the closed unit ball; `Ft` is a Lipschitz extension
    have hK0 : 0 ≤ c * L * r := mul_nonneg (mul_nonneg hcpos.le L.2) hr.le
    have hFL : LipschitzOnWith ⟨c * L * r, hK0⟩ (fun z : Rn n => c * fj (r • z)) (closedBall 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      have h1 := hLip.dist_le_mul _ (hsB x hx) _ (hsB y hy)
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm] at h1
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hcpos, hfj]
      show c * |f (r • x) j - f (r • y) j| ≤ c * L * r * dist x y
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hcoord (f (r • x) - f (r • y))).trans h1) hcpos.le
    obtain ⟨Ft, hFtL, hFtEq⟩ := hFL.extend_real
    have hFtE : ∀ z ∈ closedBall (0 : Rn n) 1, Ft z = c * fj (r • z) := fun z hz => (hFtEq hz).symm
    have hFtc : Continuous Ft := hFtL.continuous
    -- gradient of `Ft` on the open ball
    have hgFt : ∀ z ∈ ball (0 : Rn n) 1, gradient Ft z = (Real.sqrt E)⁻¹ • gradient fj (r • z) := by
      intro z hz
      have heq : Ft =ᶠ[𝓝 z] fun z => c * fj (r • z) :=
        Filter.eventuallyEq_of_mem (closedBall_mem_nhds_of_mem hz) hFtE
      have h1 : fderiv ℝ (fun z : Rn n => c * fj (r • z)) z = (c * r) • fderiv ℝ fj (r • z) := by
        rw [show (fun z : Rn n => c * fj (r • z)) = c • fun z => fj (r • z) from rfl,
          fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul]
      rw [gradient, gradient, heq.fderiv_eq, h1, hcr, map_smul]
    have hFtb : ∀ z ∈ ball (0 : Rn n) 1, ‖Ft z‖ ≤ c * h := fun z hz => by
      rw [hFtE z (ball_subset_closedBall hz), hfj, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_left ((hcoord _).trans (hbound _ (hsB' z hz))) hcpos.le
    have hgFtb : ∀ z, ‖gradient Ft z‖ ≤ c * L * r := fun z =>
      (hng Ft z).trans_le (norm_fderiv_le_of_lipschitz ℝ hFtL)
    -- `Ft ∈ W^{1,2}(B)` with weak gradient `∇Ft` (Lipschitz integration by parts)
    have hW12 : IsW12WithGradient Ft (gradient Ft) (ball 0 1) := by
      refine ⟨MemLp.of_bound hFtc.aestronglyMeasurable (c * h)
          ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hFtb)),
        MemLp.of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
          (Filter.Eventually.of_forall hgFtb), fun ζ hζ hζcs hζsupp => ?_⟩
      obtain ⟨Lζ, hζL⟩ := hζ.lipschitzWith_of_hasCompactSupport hζcs (by simp)
      have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
      have hζout : ∀ x ∉ ball (0 : Rn n) 1, ζ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hζsupp h))
      have hdζout : ∀ x ∉ ball (0 : Rn n) 1, fderiv ℝ ζ x = 0 := fun x hx =>
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hζsupp h))
      have hgζ : Continuous (gradient ζ) :=
        (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv (by simp))
      have hgζcs : HasCompactSupport (gradient ζ) :=
        (hζcs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (Rn n)).symm) (map_zero _)
      have hI1 : Integrable (fun x => Ft x • gradient ζ x) :=
        (hFtc.smul hgζ).integrable_of_hasCompactSupport hgζcs.smul_left
      have hI2 : Integrable (fun x => ζ x • gradient Ft x) :=
        (hζ.continuous.integrable_of_hasCompactSupport hζcs).smul_of_top_left
          (memLp_top_of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
            (Filter.Eventually.of_forall hgFtb))
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [gradient, hdζout x hx, map_zero, smul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hζout x hx, zero_smul])]
      refine ext_inner_left ℝ (fun w => ?_)
      rw [inner_neg_right, ← innerSL_apply_apply (𝕜 := ℝ), ← innerSL_apply_apply (𝕜 := ℝ),
        ← (innerSL ℝ w).integral_comp_comm hI1, ← (innerSL ℝ w).integral_comp_comm hI2]
      simp only [innerSL_apply_apply, inner_smul_right]
      have hibp := hFtL.integral_lineDeriv_mul_eq (μ := volume) hζL hζcs w
      have hA : ∀ x, lineDeriv ℝ ζ x (-w) * Ft x = -(Ft x * inner ℝ w (gradient ζ x)) := fun x => by
        rw [(hζd x).lineDeriv_eq_fderiv, map_neg, real_inner_comm, hig, neg_mul, mul_comm]
      have hB : (fun x => lineDeriv ℝ Ft x w * ζ x) =ᵐ[volume]
          fun x => ζ x * inner ℝ w (gradient Ft x) := by
        filter_upwards [hFtL.ae_differentiableAt] with x hx
        rw [hx.lineDeriv_eq_fderiv, real_inner_comm, hig, mul_comm]
      rw [integral_congr_ae hB] at hibp
      simp only [hA, integral_neg] at hibp
      rw [hibp, neg_neg]
    -- energy: `∫_{B} |∇Ft|² = E⁻¹ r⁻ⁿ ∫_{B_r} |∇fʲ|² ≤ E⁻¹ r⁻ⁿ ∫_{B_r} |Df|² ≤ 1`
    have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)),
        ‖gradient fj x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
      filter_upwards [hfdiff] with x hdx
      have hh : HasFDerivAt (fun y => f y j) ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp
          (fderiv ℝ f x)) x := (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hdx.hasFDerivAt
      have hfd : ∀ v, fderiv ℝ fj x v = (fderiv ℝ f x v) j := fun v => by
        rw [hfj, hh.fderiv]
        rfl
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 : (gradient fj x) i = fderiv ℝ fj x (EuclideanSpace.single i 1) := by
        rw [← hig, EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real]
      rw [Real.norm_eq_abs, sq_abs, h1, hfd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord _) 2
    have henergyF : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 ≤ 1 := by
      have hint1 : Integrable (fun x => ‖gradient Ft x‖ ^ 2) (volume.restrict (ball (0 : Rn n) 1)) :=
        Integrable.of_bound ((hgmeas Ft).norm.pow_const 2).aestronglyMeasurable ((c * L * r) ^ 2)
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hgFtb x) 2))
      have heq : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 =
          ENNReal.ofReal (∫ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint1
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
        refine lintegral_congr (fun x => ?_)
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      rw [heq, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ∀ x ∈ ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2 = E⁻¹ * ‖gradient fj (r • x)‖ ^ 2 :=
        fun x hx => by
          rw [hgFt x hx, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hsE, inv_pow,
            Real.sq_sqrt hE.le]
      rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
        Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖gradient fj x‖ ^ 2) _ hr,
        smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul]
      have h3 := (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        hHSint hpt).trans henergy
      have hrn : 0 < r ^ n := pow_pos hr n
      calc E⁻¹ * ((r ^ n)⁻¹ * ∫ x in ball (0 : Rn n) r, ‖gradient fj x‖ ^ 2)
          ≤ E⁻¹ * ((r ^ n)⁻¹ * (E * r ^ n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hrn.le))
              (inv_nonneg.2 hE.le)
        _ = 1 := by rw [mul_comm E, ← mul_assoc (r ^ n)⁻¹, inv_mul_cancel₀ hrn.ne', one_mul,
            inv_mul_cancel₀ hE.ne']
    -- almost harmonicity, by scaling `ζ₀ = ζ(r⁻¹ ·)`
    have halmostF : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball 0 1 → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x)| ≤ δ * M := by
      intro ζ hζ hζcs hζsupp M hM
      have hζ0s : ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ (r⁻¹ • x)) := hζ.comp (contDiff_const_smul _)
      have hζ0cs : HasCompactSupport (fun x => ζ (r⁻¹ • x)) := hζcs.comp_smul (inv_ne_zero hr.ne')
      have hζ0supp : tsupport (fun x => ζ (r⁻¹ • x)) ⊆ ball 0 r := by
        rw [show (fun x => ζ (r⁻¹ • x)) = ζ ∘ (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
          from rfl, tsupport_comp_eq_preimage]
        intro x hx
        have hx' := mem_ball_zero_iff.1 (hζsupp hx)
        rw [Homeomorph.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
          inv_mul_lt_iff₀ hr, mul_one] at hx'
        exact mem_ball_zero_iff.2 hx'
      have hgζ0 : ∀ x, gradient (fun x => ζ (r⁻¹ • x)) x = r⁻¹ • gradient ζ (r⁻¹ • x) := fun x => by
        rw [gradient, gradient, fderiv_comp_smul, map_smul]
      have hM0 : ∀ x, ‖gradient (fun x => ζ (r⁻¹ • x)) x‖ ≤ r⁻¹ * M := fun x => by
        rw [hgζ0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hr.le)
      have hA := halmost _ hζ0s hζ0cs hζ0supp (r⁻¹ * M) hM0 j
      rw [← hfj] at hA
      have h1 : ∀ z ∈ ball (0 : Rn n) 1, inner ℝ (gradient Ft z) (gradient ζ z) =
          ((Real.sqrt E)⁻¹ * r) * inner ℝ (gradient fj (r • z))
            (gradient (fun x => ζ (r⁻¹ • x)) (r • z)) := fun z hz => by
        rw [hgFt z hz, hgζ0, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, real_inner_smul_left,
          real_inner_smul_right, mul_assoc, ← mul_assoc r, mul_inv_cancel₀ hr.ne', one_mul]
      have hrel : ∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x) =
          (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            ∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x) := by
        rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
          Measure.setIntegral_comp_smul_of_pos volume
            (fun x => inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)) _ hr,
          smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
          mul_comm ((Real.sqrt E)⁻¹ * r)]
      have hk0 : 0 ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) :=
        mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (mul_nonneg (inv_nonneg.2 hsE.le) hr.le)
      rw [hrel, abs_mul, abs_of_nonneg hk0]
      calc (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            |∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)|
          ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) * (δ * Real.sqrt E * (r⁻¹ * M) * r ^ n) :=
            mul_le_mul_of_nonneg_left hA hk0
        _ = δ * M := by
            field_simp
    obtain ⟨u, hu1, hu2, hu3⟩ := hHA Ft (gradient Ft) hW12 henergyF halmostF
    refine ⟨u, hu1, hu2, le_of_eq_of_le (setLIntegral_congr_fun measurableSet_ball (fun x hx => ?_)) hu3⟩
    rw [hFtE x (ball_subset_closedBall hx), hfj, ← hc]
  /- Step 9: `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0)·x)_j`, and the three estimates. -/
  choose u hu_harm hu_en hu_cl using hcomp
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
  have hrc : r * Real.sqrt E * c = 1 := by rw [hc]; exact mul_inv_cancel₀ (mul_pos hr hsE).ne'
  simp only [← hc] at hu_cl
  have hsV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have hfc : ∀ k : Fin ℓ, ContinuousOn (fun z : Rn n => c * f (r • z) k) (ball 0 1) := fun k =>
    continuousOn_const.mul ((EuclideanSpace.proj k : Rn ℓ →L[ℝ] ℝ).continuous.comp_continuousOn
      (hLip.continuousOn.comp (continuous_const_smul r).continuousOn (fun z hz => by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        exact mul_le_of_le_one_right hr.le (mem_ball_zero_iff.1 hz).le)))
  have hdm : ∀ k : Fin ℓ, AEStronglyMeasurable (fun z => u k z - c * f (r • z) k)
      (volume.restrict (ball (0 : Rn n) 1)) := fun k =>
    ((hu_harm k).continuousOn.sub (hfc k)).aestronglyMeasurable measurableSet_ball
  -- interior estimates for each `u k`
  have hest : ∀ k : Fin ℓ, ‖gradient (u k) 0‖ ≤ C₁ * Real.sqrt V ∧
      (∀ z : Rn n, ‖z‖ ≤ 1/4 →
        |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ C₃ * Real.sqrt V * ‖z‖ ^ 2) ∧
      |u k 0| ≤ C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
    intro k
    have hg := CS (fun x => ‖gradient (u k) x‖ₑ)
      ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (u k))).enorm.aemeasurable 1 zero_le_one
        (by rw [ENNReal.ofReal_one]; exact hu_en k)
    rw [Real.sqrt_one, mul_one] at hg
    have h1 := CS _ (hdm k).enorm ε hε.le (hu_cl k)
    have h2 : ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ ≤ ENNReal.ofReal (V * (c * h)) := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ
          ≤ ∫⁻ _ in ball (0 : Rn n) 1, ENNReal.ofReal (c * h) := by
            refine setLIntegral_mono measurable_const (fun z hz => ?_)
            rw [← ofReal_norm, norm_mul, Real.norm_eq_abs, abs_of_pos hcpos]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hcpos.le)
            exact (PiLp.norm_apply_le (f (r • z)) k).trans (hbound _ (by
              rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
              exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)))
        _ = ENNReal.ofReal (V * (c * h)) := by
          rw [setLIntegral_const, ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← hVdef,
            ← ENNReal.ofReal_mul (mul_nonneg hcpos.le hh), mul_comm (c * h) V]
    have hu1 : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x‖ₑ ≤
        ENNReal.ofReal (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
      rw [ENNReal.ofReal_add (mul_nonneg hsV (Real.sqrt_nonneg _))
        (mul_nonneg hV0 (mul_nonneg hcpos.le hh))]
      refine le_trans (lintegral_mono (fun x => ?_))
        ((lintegral_add_left' (hdm k).enorm _).trans_le (add_le_add h1 h2))
      calc ‖u k x‖ₑ = ‖(u k x - c * f (r • x) k) + c * f (r • x) k‖ₑ := by rw [sub_add_cancel]
        _ ≤ _ := enorm_add_le _ _
    obtain ⟨hg0, hT⟩ := (HE (u k) (hu_harm k)).2 _ hsV hg
    exact ⟨hg0, hT, (HE (u k) (hu_harm k)).1 _
      (add_nonneg (mul_nonneg hsV (Real.sqrt_nonneg _)) (mul_nonneg hV0 (mul_nonneg hcpos.le hh)))
      hu1⟩
  -- the affine map
  obtain ⟨a, ha⟩ : ∃ a : Rn ℓ, a = WithLp.toLp 2 (fun k => r * Real.sqrt E * u k 0) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Rn n →L[ℝ] Rn ℓ, A = ∑ k : Fin ℓ,
      (Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight (EuclideanSpace.single k (1:ℝ)) :=
    ⟨_, rfl⟩
  have haapply : ∀ k, a k = r * Real.sqrt E * u k 0 := fun k => by rw [ha]
  have hAapply : ∀ (x : Rn n) (k : Fin ℓ), (A x) k = Real.sqrt E * inner ℝ (gradient (u k) 0) x :=
    fun x k => by
      rw [hA]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Pi.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨a, A, ?_, ?_, ?_⟩
  · -- `|A| ≤ C √E`
    have hAn : ‖A‖ ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
      rw [hA]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k : Fin ℓ, ‖(Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight
            (EuclideanSpace.single k (1:ℝ))‖
          ≤ ∑ _k : Fin ℓ, (C₁ * Real.sqrt V) * Real.sqrt E := Finset.sum_le_sum (fun k _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply, EuclideanSpace.norm_single, norm_one,
              mul_one, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos hsE, mul_comm]
            exact mul_le_mul_of_nonneg_right (hest k).1 hsE.le)
        _ = ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
    have h0 : 0 ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ hsV)) hsE.le
    calc hsNorm A ≤ Real.sqrt (n * (ℓ * (C₁ * Real.sqrt V) * Real.sqrt E) ^ 2) :=
          Real.sqrt_le_sqrt ((hHS A).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hAn 2) (Nat.cast_nonneg _)))
      _ = Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) * Real.sqrt E := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0, ← mul_assoc]
      _ ≤ C * Real.sqrt E := mul_le_mul_of_nonneg_right hC1 hsE.le
  · -- `|a| ≤ C (h + r √(εE))`
    have hB0 : 0 ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) :=
      mul_nonneg hC₁ (add_nonneg (mul_nonneg hsV (mul_nonneg hr.le (Real.sqrt_nonneg _)))
        (mul_nonneg hV0 hh))
    have hak : ∀ k, |a k| ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) := fun k => by
      rw [haapply, abs_mul, abs_of_pos (mul_pos hr hsE), Real.sqrt_mul hε.le]
      calc r * Real.sqrt E * |u k 0| ≤ r * Real.sqrt E *
            (C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h))) :=
            mul_le_mul_of_nonneg_left (hest k).2.2 (mul_pos hr hsE).le
        _ = C₁ * (Real.sqrt V * (r * (Real.sqrt ε * Real.sqrt E)) +
            V * h * (r * Real.sqrt E * c)) := by ring
        _ = _ := by rw [hrc, mul_one]
    calc ‖a‖ = Real.sqrt (∑ k : Fin ℓ, ‖a k‖ ^ 2) := EuclideanSpace.norm_eq a
      _ ≤ Real.sqrt (∑ _k : Fin ℓ, (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2))
      _ = Real.sqrt ℓ * (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB0]
      _ ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hab _ _ _ _ hsV hV0 hh
            (mul_nonneg hr.le (Real.sqrt_nonneg _))) hC₁) (Real.sqrt_nonneg _)
      _ ≤ C * (h + r * Real.sqrt (ε * E)) :=
          mul_le_mul_of_nonneg_right hC2 (add_nonneg hh (mul_nonneg hr.le (Real.sqrt_nonneg _)))
  · -- the `L²` estimate
    intro e he he4
    have he1 : e ≤ 1 := he4.trans (by norm_num)
    have hrn : 0 < r ^ n := pow_pos hr n
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) e)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hcv : ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 =
        r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 := by
      have h := Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖f x - (a + A x)‖ ^ 2)
        (ball (0 : Rn n) e) hr
      rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_comm r e,
        finrank_euclideanSpace_fin, smul_eq_mul] at h
      rw [h, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
    rw [hcv]
    -- integrability and size of `(u_k - F_k)²`
    have hsq : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) ∧
        ∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2 ≤ ε := by
      intro k
      have hfi : ∫⁻ z in ball (0 : Rn n) 1, ‖(u k z - c * f (r • z) k) ^ 2‖ₑ =
          ∫⁻ z in ball (0 : Rn n) 1, ‖u k z - c * f (r • z) k‖ₑ ^ 2 :=
        lintegral_congr (fun z => enorm_pow _ _)
      have hi : IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) :=
        ⟨(hdm k).pow 2, by rw [HasFiniteIntegral, hfi]; exact (hu_cl k).trans_lt ENNReal.ofReal_lt_top⟩
      refine ⟨hi, (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        (Filter.Eventually.of_forall (ball_subset_ball he1))).trans ?_⟩
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        ((hdm k).pow 2)]
      refine ENNReal.toReal_le_of_le_ofReal hε.le (le_trans (le_of_eq ?_) (hu_cl k))
      refine lintegral_congr (fun z => ?_)
      rw [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₃ * Real.sqrt V * e ^ 2 := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := hD ▸ mul_nonneg (mul_nonneg hC₃ hsV) (sq_nonneg e)
    -- pointwise bound on `B_e`
    have hpt : ∀ z ∈ ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 ≤
        2 * (r ^ 2 * E) * ∑ k : Fin ℓ, ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by
      intro z hz
      have hz' : ‖z‖ ≤ 1/4 := (mem_ball_zero_iff.1 hz).le.trans he4
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hcomp : (f (r • z) - (a + A (r • z))) k = r * Real.sqrt E *
          (-(u k z - c * f (r • z) k) + (u k z - u k 0 - inner ℝ (gradient (u k) 0) z)) := by
        rw [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply, haapply, hAapply,
          real_inner_smul_right]
        linear_combination (-(f (r • z) k)) * hrc
      have hY : (u k z - u k 0 - inner ℝ (gradient (u k) 0) z) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs, hD]
        exact pow_le_pow_left₀ (abs_nonneg _) (((hest k).2.1 z hz').trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z)
            (mem_ball_zero_iff.1 hz).le 2) (mul_nonneg hC₃ hsV))) 2
      rw [Real.norm_eq_abs, sq_abs, hcomp, mul_pow, mul_pow, Real.sq_sqrt hE.le]
      calc r ^ 2 * E * (-(u k z - c * f (r • z) k) + (u k z - u k 0 -
            inner ℝ (gradient (u k) 0) z)) ^ 2
          ≤ r ^ 2 * E * (2 * ((-(u k z - c * f (r • z) k)) ^ 2 + D ^ 2)) :=
            mul_le_mul_of_nonneg_left (hsq2 _ _ _ hY) (mul_nonneg (sq_nonneg r) hE.le)
        _ = 2 * (r ^ 2 * E) * ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by ring
    have hint : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2 + D ^ 2)
        (ball (0 : Rn n) e) := fun k =>
      ((hsq k).1.mono_set (ball_subset_ball he1)).add (integrable_const _)
    have hvol : ∫ _ in ball (0 : Rn n) e, D ^ 2 = e ^ n * V * D ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Measure.addHaar_ball_of_pos volume _ he,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg he.le n),
        ← hVdef]
    have hP : e ^ n * V * D ^ 2 = C₃ ^ 2 * V ^ 2 * (e ^ n * e ^ 4) := by
      rw [hD, mul_pow, mul_pow, Real.sq_sqrt hV0]; ring
    have h2rE : 0 ≤ 2 * (r ^ 2 * E) := mul_nonneg zero_le_two (mul_nonneg (sq_nonneg r) hE.le)
    calc r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2
        ≤ r ^ n * ∫ z in ball (0 : Rn n) e, 2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _))
            ((integrable_finsetSum _ (fun k _ => hint k)).const_mul _)
            ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hpt))) hrn.le
      _ = r ^ n * (2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2) + e ^ n * V * D ^ 2)) := by
          rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
          congr 2
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [integral_add ((hsq k).1.mono_set (ball_subset_ball he1)) (integrable_const _), hvol]
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ, (ε + e ^ n * V * D ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => add_le_add (hsq k).2 le_rfl)) h2rE) hrn.le
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ,
          ((1 + C₃ ^ 2 * V ^ 2) * (ε + e ^ n * e ^ 4))) := by
          rw [hP]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => hKP _ _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (pow_nonneg he.le n) (pow_nonneg he.le 4)) hε.le)) h2rE) hrn.le
      _ = (2 * ℓ * (1 + C₃ ^ 2 * V ^ 2)) * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add,
            pow_add]
          ring
      _ ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3
            (add_nonneg hε.le (pow_nonneg he.le _))) hE.le) (pow_nonneg hr.le _)
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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
