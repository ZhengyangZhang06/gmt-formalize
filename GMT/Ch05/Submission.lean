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

/-- The Euclidean Hausdorff measure under the similarity `ψ(x) = c + R x` (`R > 0`):
`ψ_# Hⁿ = R⁻ⁿ Hⁿ`.  `ψ⁻¹B` is the preimage of `τ⁻¹B`, `τ(z) = c + z`, under the homothety
`x ↦ R • x`, and preimages under that homothety scale `Hⁿ` by `‖R‖₊⁻¹ ^ n = R⁻ⁿ`; the isometry
`τ` preserves `Hⁿ`. -/
theorem any_radius_rv_map_hausdorff : ∀ (n ℓ : ℕ) (c : Amb n ℓ) (R : ℝ), 0 < R → (μHE[n] : Measure (Amb n ℓ)).map (fun x => c + R • x) = (ENNReal.ofReal (R ^ n))⁻¹ • (μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ c R hR
  -- The constant: `(ofReal Rⁿ)⁻¹ = ‖R‖₊⁻¹ ^ n` since `R > 0`.
  have hκ : (ENNReal.ofReal (R ^ n))⁻¹ = ((‖R‖₊⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_inv_of_pos (pow_pos hR n), ← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.norm_of_nonneg hR.le, inv_pow]
  -- The translation `τ(z) = c + z` is an isometric equivalence, so it preserves `Hⁿ`.
  have hτ : MeasurePreserving (fun z : Amb n ℓ => c + z) μHE[n] μHE[n] :=
    (IsometryEquiv.addLeft c).measurePreserving_euclideanHausdorffMeasure n
  ext B hB
  -- `ψ⁻¹B` is the preimage of `τ⁻¹B` under the homothety `x ↦ R • x` (center `0`).
  have hpre : (fun x : Amb n ℓ => c + R • x) ⁻¹' B =
      AffineMap.homothety (0 : Amb n ℓ) R ⁻¹' ((fun z => c + z) ⁻¹' B) := by
    ext x
    simp [AffineMap.homothety_apply]
  rw [Measure.map_apply (by fun_prop) hB, Measure.smul_apply, hκ, hpre,
    euclideanHausdorffMeasure_homothety_preimage n 0 hR.ne',
    hτ.measure_preimage hB.nullMeasurableSet, ENNReal.smul_def]
/-- Rescaling a rectifiable varifold (used for the rescaled varifold in Simon Ch. 5, Remark 5.3):
for `ψ(x) = c + R x` with `R > 0`, `v(ψ⁻¹M, θ ∘ ψ)` is a rectifiable `n`-varifold in `ψ⁻¹U`.  `ψ` is
a homeomorphism (a dilation followed by a translation), hence a measurable embedding, and
`ψ_# Hⁿ = R⁻ⁿ Hⁿ` (`any_radius_rv_map_hausdorff`), so `ψ` is quasi-measure-preserving and pulls
`Hⁿ`-null sets back to `Hⁿ`-null sets.  Null-measurability, countable rectifiability (via `ψ⁻¹M₀`
and the Lipschitz maps `R⁻¹(F_j − c)`), a.e.-measurability of `θ ∘ ψ` on `ψ⁻¹M` and its
integrability on `ψ⁻¹M ∩ K` (through the compact set `ψ(K) ⊆ U`) all transfer. -/
theorem any_radius_rv_exists_structure : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (c : Amb n ℓ) (R : ℝ), 0 < R → ∃ W : RectifiableVarifold n ℓ ((fun x => c + R • x) ⁻¹' U), W.carrier = (fun x => c + R • x) ⁻¹' V.carrier ∧ ∀ x, W.mult x = V.mult (c + R • x) := by
  intro n ℓ U V c R hR
  -- `ψ(x) = c + R • x` is the homeomorphism `x ↦ R • x` followed by `z ↦ c + z`, hence a
  -- continuous measurable embedding.
  have hψ : Continuous (fun x : Amb n ℓ => c + R • x) :=
    ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft c)).continuous
  have hψe : MeasurableEmbedding (fun x : Amb n ℓ => c + R • x) :=
    ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft c)).measurableEmbedding
  -- `ψ_# Hⁿ = κ • Hⁿ` with `κ = R⁻ⁿ ≠ ∞`.
  have hmap : (μHE[n] : Measure (Amb n ℓ)).map (fun x => c + R • x) =
      (ENNReal.ofReal (R ^ n))⁻¹ • (μHE[n] : Measure (Amb n ℓ)) :=
    Submission.any_radius_rv_map_hausdorff n ℓ c R hR
  have hκ : (ENNReal.ofReal (R ^ n))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (pow_pos hR n)).ne'
  -- Hence `ψ` is quasi-measure-preserving and `ψ⁻¹` maps `Hⁿ`-null sets to `Hⁿ`-null sets.
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Amb n ℓ => c + R • x) μHE[n] μHE[n] :=
    ⟨hψe.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  have hnull : ∀ B : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) B = 0 →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => c + R • x) ⁻¹' B) = 0 := fun B hB => by
    rw [← hψe.map_apply, hmap, Measure.smul_apply, hB, smul_zero]
  refine ⟨{
    carrier := (fun x => c + R • x) ⁻¹' V.carrier
    mult := fun x => V.mult (c + R • x)
    carrier_subset := preimage_mono V.carrier_subset
    nullMeasurableSet_carrier := V.nullMeasurableSet_carrier.preimage hqmp
    countablyRectifiable := ?_
    mult_pos := fun x hx => V.mult_pos (c + R • x) hx
    aemeasurable_mult := ?_
    integrableOn_mult := ?_ }, rfl, fun x => rfl⟩
  · -- Pull back the null set `M₀` and compose the Lipschitz pieces `F j` with `ψ⁻¹`.
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := V.countablyRectifiable
    refine ⟨(fun x => c + R • x) ⁻¹' M₀, hnull M₀ hM₀, fun j z => R⁻¹ • (F j z - c),
      fun j => ?_, fun x hx => ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨‖R⁻¹‖₊ * (K + 0), (lipschitzWith_smul R⁻¹).comp (hK.sub (LipschitzWith.const c))⟩
    · rcases hcover hx with h | h
      · exact Or.inl h
      · obtain ⟨j, z, hz⟩ := mem_iUnion.1 h
        refine Or.inr (mem_iUnion.2 ⟨j, z, ?_⟩)
        simp only [hz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  · -- `ψ` maps `Hⁿ⌞ψ⁻¹M` to `κ • Hⁿ⌞M`, for which `θ` is a.e.-measurable.
    have h : AEMeasurable V.mult
        (((μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => c + R • x) ⁻¹' V.carrier)).map
          (fun x => c + R • x)) := by
      rw [← hψe.restrict_map, hmap, Measure.restrict_smul]
      exact V.aemeasurable_mult.smul_measure _
    exact h.comp_measurable hψe.measurable
  · -- `ψ(K)` is a compact subset of `U`, and `ψ⁻¹(M ∩ ψ(K)) = ψ⁻¹M ∩ K`.
    intro K hK hKU
    have h : IntegrableOn V.mult (V.carrier ∩ (fun x => c + R • x) '' K)
        ((μHE[n] : Measure (Amb n ℓ)).map (fun x => c + R • x)) := by
      rw [hmap, IntegrableOn, Measure.restrict_smul]
      exact (V.integrableOn_mult _ (hK.image hψ)
        (by rintro _ ⟨k, hk, rfl⟩; exact hKU hk)).smul_measure hκ
    have h' := hψe.integrableOn_map_iff.1 h
    rwa [preimage_inter, hψe.injective.preimage_image] at h'
/-- Weight of the rescaled varifold (the rescaling `ψ(x) = c + R x` behind Simon Ch. 5, Remark 5.3):
if `W = v(ψ⁻¹M, θ ∘ ψ)`, then `μ_W = R⁻ⁿ φ_# μ_V` with `φ(y) = R⁻¹(y − c)`.  On a measurable set
`A`, `A ∩ ψ⁻¹M = ψ⁻¹(φ⁻¹A ∩ M)` because `φ ∘ ψ = id`, so `μ_W(A) = ∫_{ψ⁻¹(φ⁻¹A ∩ M)} θ ∘ ψ dHⁿ`;
the change of variables `∫_{ψ⁻¹S} g ∘ ψ dHⁿ = R⁻ⁿ ∫_S g dHⁿ`, from `ψ_# Hⁿ = R⁻ⁿ Hⁿ`
(`any_radius_rv_map_hausdorff`), turns this into `R⁻ⁿ μ_V(φ⁻¹A)`. -/
theorem any_radius_rv_weight_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (c : Amb n ℓ) (R : ℝ), 0 < R → W.carrier = (fun x => c + R • x) ⁻¹' V.carrier → (∀ x, W.mult x = V.mult (c + R • x)) → W.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c)) := by
  intro n ℓ U U' V W c R hR hW hθ
  -- `ψ(x) = c + R x` is a measurable embedding, `φ(y) = R⁻¹(y − c)` is measurable, `φ ∘ ψ = id`.
  have hψ : MeasurableEmbedding (fun x : Amb n ℓ => c + R • x) :=
    (measurableEmbedding_addLeft c).comp (measurableEmbedding_const_smul₀ hR.ne')
  have hφ : Measurable (fun y : Amb n ℓ => R⁻¹ • (y - c)) :=
    ((continuous_id.sub continuous_const).const_smul R⁻¹).measurable
  have hφψ : ∀ x : Amb n ℓ, R⁻¹ • (c + R • x - c) = x := fun x => by
    rw [add_sub_cancel_left, inv_smul_smul₀ hR.ne']
  -- Change of variables: `∫_{ψ⁻¹S} g ∘ ψ dHⁿ = R⁻ⁿ ∫_S g dHⁿ`, from `ψ_# Hⁿ = R⁻ⁿ Hⁿ`.
  have hcv : ∀ (S : Set (Amb n ℓ)) (g : Amb n ℓ → ℝ≥0∞),
      ∫⁻ x in (fun x => c + R • x) ⁻¹' S, g (c + R • x) ∂(μHE[n] : Measure (Amb n ℓ)) =
        (ENNReal.ofReal (R ^ n))⁻¹ * ∫⁻ y in S, g y ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro S g
    have h := hψ.lintegral_map (μ := (μHE[n] : Measure (Amb n ℓ)).restrict
      ((fun x => c + R • x) ⁻¹' S)) g
    rw [← hψ.restrict_map, Submission.any_radius_rv_map_hausdorff n ℓ c R hR,
      Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Compare both measures on a measurable set `A`.
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply hφ hA, smul_eq_mul, RectifiableVarifold.weight,
    RectifiableVarifold.weight, withDensity_apply _ hA, withDensity_apply _ (hφ hA),
    Measure.restrict_restrict hA, Measure.restrict_restrict (hφ hA)]
  -- `A ∩ ψ⁻¹M = ψ⁻¹(φ⁻¹A ∩ M)` (as `φ ∘ ψ = id`) and `θ_W = θ ∘ ψ`.
  have hA' : A ∩ W.carrier =
      (fun x => c + R • x) ⁻¹' ((fun y => R⁻¹ • (y - c)) ⁻¹' A ∩ V.carrier) := by
    rw [hW, preimage_inter]
    congr 1
    ext x
    simp only [mem_preimage, hφψ]
  rw [hA']
  simp only [hθ]
  exact hcv _ fun y => ENNReal.ofReal (V.mult y)
/-- Support of a rescaled varifold (the rescaling `ψ(x) = c + R x` behind Simon Ch. 5, Remark 5.3):
if `μ_W = R⁻ⁿ φ_# μ_V` with `φ(y) = R⁻¹(y − c)`, then `spt W = ψ⁻¹(spt V)`.  `φ` is the inverse of
the homeomorphism `ψ`, so `μ_W(G) = R⁻ⁿ μ_V(φ⁻¹G)` for every set `G`; neighbourhoods of `x` and of
`ψ(x)` correspond under `ψ⁻¹` and `φ⁻¹`, and the factor `R⁻ⁿ ∈ (0, ∞)` does not change positivity. -/
theorem any_radius_rv_support_eq : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (c : Amb n ℓ) (R : ℝ), 0 < R → ∀ W : RectifiableVarifold n ℓ ((fun x => c + R • x) ⁻¹' U), W.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c)) → W.support = (fun x => c + R • x) ⁻¹' V.support := by
  intro n ℓ U V c R hR W hW
  have hR0 : R ≠ 0 := hR.ne'
  -- `κ = (Rⁿ)⁻¹ ≠ 0` in `[0, ∞]`, since `Rⁿ < ∞`.
  have hκ : (ENNReal.ofReal (R ^ n))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  -- `ψ(x) = c + R x` and `φ(y) = R⁻¹ (y − c)` are mutually inverse homeomorphisms.
  have hψφ : ∀ y : Amb n ℓ, c + R • (R⁻¹ • (y - c)) = y := fun y => by
    rw [smul_smul, mul_inv_cancel₀ hR0, one_smul, add_sub_cancel]
  have hφψ : ∀ x : Amb n ℓ, R⁻¹ • ((c + R • x) - c) = x := fun x => by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR0, one_smul]
  have hψc : Continuous fun x : Amb n ℓ => c + R • x := by fun_prop
  have hφc : Continuous fun y : Amb n ℓ => R⁻¹ • (y - c) := by fun_prop
  let e : Amb n ℓ ≃ₜ Amb n ℓ :=
    { toFun := fun y => R⁻¹ • (y - c)
      invFun := fun x => c + R • x
      left_inv := hψφ
      right_inv := hφψ
      continuous_toFun := hφc
      continuous_invFun := hψc }
  -- Hence `φ` is a measurable embedding and `μ_W(G) = κ μ_V(φ⁻¹G)` for every set `G`.
  have hφe : MeasurableEmbedding fun y : Amb n ℓ => R⁻¹ • (y - c) := e.measurableEmbedding
  have hWG : ∀ G : Set (Amb n ℓ),
      W.weight G = (ENNReal.ofReal (R ^ n))⁻¹ * V.weight ((fun y => R⁻¹ • (y - c)) ⁻¹' G) := by
    intro G
    rw [hW, Measure.smul_apply, hφe.map_apply, smul_eq_mul]
  -- `x ∈ spt μ_W ↔ ψ(x) ∈ spt μ_V`.
  have key : ∀ x : Amb n ℓ, x ∈ W.weight.support ↔ c + R • x ∈ V.weight.support := by
    intro x
    rw [Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
    constructor
    · -- `ψ⁻¹G` is a neighbourhood of `x`, and `φ⁻¹(ψ⁻¹G) = G`.
      intro h G hG
      have hpos := h _ (hψc.continuousAt.preimage_mem_nhds hG)
      have hpre : (fun y => R⁻¹ • (y - c)) ⁻¹' ((fun x => c + R • x) ⁻¹' G) = G := by
        ext y
        simp only [mem_preimage, hψφ]
      rw [hWG, hpre] at hpos
      exact (ENNReal.mul_pos_iff.1 hpos).2
    · -- `φ⁻¹G` is a neighbourhood of `ψ(x)`, since `φ(ψ(x)) = x`.
      intro h G hG
      rw [hWG]
      refine ENNReal.mul_pos hκ (h _ ?_).ne'
      refine hφc.continuousAt.preimage_mem_nhds ?_
      rw [hφψ]
      exact hG
  -- `spt W = ψ⁻¹U ∩ spt μ_W = ψ⁻¹U ∩ ψ⁻¹(spt μ_V) = ψ⁻¹(spt V)`.
  ext x
  simp only [RectifiableVarifold.support, mem_inter_iff, mem_preimage, key]
/-- Scaling invariance of tangent planes (Simon Ch. 3, 1.7; Ch. 4, 1.3): if
`W = v(ψ⁻¹ M, θ ∘ ψ)` with `ψ(x) = c + R x`, `R > 0`, then `η_{x,r}(ψ⁻¹ M) = η_{ψ x,R r}(M)` and
the blown-up multiplicities agree, and `r ↦ R r` preserves `𝓝[>] 0` (with inverse `s ↦ R⁻¹ s`), so
the weighted approximate tangent planes of `W` at `x` are those of `V` at `ψ x`, and `W`, `V` choose
the same tangent projection there. -/
theorem any_radius_rv_tangentProj_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (c : Amb n ℓ) (R : ℝ),
    0 < R → W.carrier = (fun x => c + R • x) ⁻¹' V.carrier →
    (∀ x, W.mult x = V.mult (c + R • x)) → ∀ x, W.tangentProj x = V.tangentProj (c + R • x) := by
  intro n ℓ U U' V W c R hR hc hm x
  have hR0 : R ≠ 0 := hR.ne'
  -- `η_{x,r}(ψ⁻¹ M) = η_{ψ x,R r}(M)`, since `ψ z - ψ x = R (z - x)` and `(R r)⁻¹ R = r⁻¹`.
  have himg : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap x r '' W.carrier =
      Poincare.SimonGMT.Chapter03.blowUpMap (c + R • x) (R * r) '' V.carrier := by
    intro r
    rw [hc]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨c + R • z, hz, ?_⟩
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
      rw [show c + R • z - (c + R • x) = R • (z - x) by rw [smul_sub]; abel, smul_smul,
        mul_inv_rev, mul_assoc, inv_mul_cancel₀ hR0, mul_one]
    · rintro ⟨m, hm', rfl⟩
      refine ⟨R⁻¹ • (m - c), ?_, ?_⟩
      · show c + R • R⁻¹ • (m - c) ∈ V.carrier
        rwa [smul_smul, mul_inv_cancel₀ hR0, one_smul, add_sub_cancel]
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
        rw [show R⁻¹ • (m - c) - x = R⁻¹ • (m - (c + R • x)) by
            rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hR0, one_smul]; abel,
          smul_smul, mul_inv_rev]
  -- `θ_W(x + r y) = θ(ψ x + (R r) y)`.
  have hmult : ∀ (r : ℝ) (y : Amb n ℓ), W.mult (x + r • y) = V.mult (c + R • x + (R * r) • y) := by
    intro r y
    rw [hm, smul_add, mul_smul, add_assoc]
  -- `r ↦ a r` maps `𝓝[>] 0` to `𝓝[>] 0` for `a > 0`.
  have hfil : ∀ a : ℝ, 0 < a → Tendsto (fun r : ℝ => a * r) (𝓝[>] 0) (𝓝[>] 0) := by
    intro a ha
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun r : ℝ => a * r) (𝓝 0) (𝓝 (a * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos ha hr
  -- Hence the limits along `r` and along `R r` agree, and the two predicates coincide.
  have key : ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult x P ↔
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
        (c + R • x) P := by
    intro P
    simp only [Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt]
    refine and_congr_right fun _ => forall_congr' fun f => ?_
    simp only [himg, hmult]
    rw [hm x]
    constructor
    · intro h
      refine (h.comp (hfil R⁻¹ (inv_pos.2 hR))).congr fun s => ?_
      simp only [Function.comp_apply, mul_inv_cancel_left₀ hR0]
    · intro h
      exact h.comp (hfil R hR)
  -- So `W` at `x` and `V` at `ψ x` choose the same tangent plane.
  have hchoose : ∀ (p q : Submodule ℝ (Amb n ℓ) → Prop) (h₁ : ∃ P, p P) (h₂ : ∃ P, q P),
      p = q → Classical.choose h₁ = Classical.choose h₂ := by
    rintro p q h₁ h₂ rfl
    rfl
  unfold RectifiableVarifold.tangentProj
  by_cases h₁ : ∃ P,
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult x P
  · have h₂ := (exists_congr key).1 h₁
    rw [dite_eq_left h₁, dite_eq_left h₂]
    congr 1
    exact hchoose _ _ h₁ h₂ (funext fun P => propext (key P))
  · have h₂ : ¬∃ P, Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult (c + R • x) P := fun h => h₁ ((exists_congr key).2 h)
    rw [dite_eq_right h₁, dite_eq_right h₂]
/-- **Generalized mean curvature of a rescaled varifold** (Simon Ch. 4, Definition 3.14; used for
the rescalings behind Ch. 5, Remark 5.3).  Let `ψ(x) = c + R x` and `φ(y) = R⁻¹ (y − c)`, `R > 0`.
If `μ_W = R⁻ⁿ φ_# μ_V` and `p_{T_x W} = p_{T_{ψ x} V}`, then `W` has generalized mean curvature
`R H ∘ ψ` in `ψ⁻¹ U`: neighbourhoods `t ∈ 𝓝[U] (ψ x)` pull back to `ψ⁻¹ t ∈ 𝓝[ψ⁻¹ U] x`, and for
`X ∈ C¹_c(ψ⁻¹ U)` the field `X̃ = R X ∘ φ ∈ C¹_c(U)` has `DX̃ = DX ∘ φ`, so `div_W X ∘ φ = div_V X̃`
and `X ∘ φ · R H = X̃ · H`; changing variables along `φ` turns the first variation of `W` at `X`
into `R⁻ⁿ` times that of `V` at `X̃`. -/
theorem any_radius_rv_meanCurvature : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (c : Amb n ℓ) (R : ℝ), 0 < R → ∀ W : RectifiableVarifold n ℓ ((fun x => c + R • x) ⁻¹' U), W.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c)) → (∀ x, W.tangentProj x = V.tangentProj (c + R • x)) → ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → W.HasGeneralizedMeanCurvature (fun x => R • H (c + R • x)) := by
  intro n ℓ U V c R hR W hw hT H hH
  obtain ⟨hHloc, hHfv⟩ := hH
  have hR0 : R ≠ 0 := hR.ne'
  -- `κ = R⁻ⁿ` is finite.
  have hκ : (ENNReal.ofReal (R ^ n))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (pow_pos hR n)).ne'
  -- `ψ (φ y) = y` and `φ (ψ x) = x`.
  have hψφ : ∀ y : Amb n ℓ, c + R • R⁻¹ • (y - c) = y := fun y => by
    rw [smul_smul, mul_inv_cancel₀ hR0, one_smul, add_sub_cancel]
  have hφψ : ∀ x : Amb n ℓ, R⁻¹ • (c + R • x - c) = x := fun x => by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR0, one_smul]
  have hψc : Continuous (fun x : Amb n ℓ => c + R • x) :=
    continuous_const.add (continuous_const_smul R)
  -- `φ` is a homeomorphism with inverse `ψ`; as a measurable equivalence, `μ_W = κ • φ_# μ_V`.
  let φ : Amb n ℓ ≃ₜ Amb n ℓ :=
    { toFun := fun y => R⁻¹ • (y - c)
      invFun := fun x => c + R • x
      left_inv := hψφ
      right_inv := hφψ
      continuous_toFun := (continuous_sub_right c).const_smul R⁻¹
      continuous_invFun := hψc }
  have hw' : W.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map φ.toMeasurableEquiv := hw
  refine ⟨?_, ?_⟩
  · -- Local integrability: transport `t ∈ 𝓝[U] (ψ x)` to `ψ⁻¹ t ∈ 𝓝[ψ⁻¹ U] x`.
    intro x hx
    obtain ⟨t, ht, hti⟩ := hHloc (c + R • x) hx
    refine ⟨(fun x => c + R • x) ⁻¹' t, ?_, ?_⟩
    · exact (hψc.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)) ht
    · -- `(κ • ν)⌞s = κ • ν⌞s` with `κ ≠ ∞`, and
      -- `IntegrableOn (R H ∘ ψ) (ψ⁻¹ t) (φ_# μ_V) ↔ IntegrableOn (R H) t μ_V`.
      rw [hw', IntegrableOn, Measure.restrict_smul]
      refine Integrable.smul_measure ?_ hκ
      change IntegrableOn _ _ (V.weight.map φ.toMeasurableEquiv)
      rw [integrableOn_map_equiv]
      have h1 : (fun x => R • H (c + R • x)) ∘ φ.toMeasurableEquiv = R • H := by
        funext y
        show R • H (c + R • R⁻¹ • (y - c)) = R • H y
        rw [hψφ]
      have h2 : φ.toMeasurableEquiv ⁻¹' ((fun x => c + R • x) ⁻¹' t) = t := by
        ext y
        show c + R • R⁻¹ • (y - c) ∈ t ↔ y ∈ t
        rw [hψφ]
      rw [h1, h2]
      exact Integrable.smul R hti
  · -- First variation: test `V` with the transported field `X̃(y) = R X(φ y)`.
    intro X hX hXc hXs
    have hXd : Differentiable ℝ X := hX.differentiable one_ne_zero
    have hX'c : ContDiff ℝ 1 (fun y => R • X (R⁻¹ • (y - c))) :=
      (hX.comp ((contDiff_id.sub contDiff_const).const_smul R⁻¹)).const_smul R
    have hX'cs : HasCompactSupport (fun y => R • X (R⁻¹ • (y - c))) :=
      (hXc.comp_homeomorph φ).comp_left (g := fun v : Amb n ℓ => R • v) (smul_zero R)
    -- `y ∈ tsupport X̃` gives `φ y ∈ tsupport X ⊆ ψ⁻¹ U`, i.e. `y = ψ (φ y) ∈ U`.
    have hX's : tsupport (fun y => R • X (R⁻¹ • (y - c))) ⊆ U := by
      intro y hy
      have h1 := tsupport_smul_subset_right (fun _ => R) (fun y => X (R⁻¹ • (y - c))) hy
      have h2 := hXs (tsupport_comp_subset_preimage X φ.continuous h1)
      have h3 : c + R • R⁻¹ • (y - c) ∈ U := h2
      rwa [hψφ] at h3
    have key := hHfv _ hX'c hX'cs hX's
    -- `DX̃(y) = R • (DX(φ y) ∘ R⁻¹ • id) = DX(φ y)`.
    have hder : ∀ y, fderiv ℝ (fun y => R • X (R⁻¹ • (y - c))) y =
        fderiv ℝ X (R⁻¹ • (y - c)) := by
      intro y
      have h1 : HasFDerivAt (fun y : Amb n ℓ => R⁻¹ • (y - c))
          (R⁻¹ • ContinuousLinearMap.id ℝ (Amb n ℓ)) y :=
        ((hasFDerivAt_id y).sub_const c).const_smul R⁻¹
      have h2 : HasFDerivAt (fun y => R • X (R⁻¹ • (y - c)))
          (R • ((fderiv ℝ X (R⁻¹ • (y - c))).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Amb n ℓ)))) y :=
        ((hXd (R⁻¹ • (y - c))).hasFDerivAt.comp y h1).const_smul R
      rw [h2.fderiv]
      refine ContinuousLinearMap.ext fun v => ?_
      rw [smul_apply, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.map_smul, smul_smul, mul_inv_cancel₀ hR0, one_smul]
    -- `div_W X (φ y) = div_V X̃ (y)`, by the tangent hypothesis and `ψ (φ y) = y`.
    have hdiv : ∀ y, W.divM X (R⁻¹ • (y - c)) = V.divM (fun y => R • X (R⁻¹ • (y - c))) y := by
      intro y
      simp only [RectifiableVarifold.divM, hT, hψφ, hder]
    -- `X (φ y) · R H (ψ (φ y)) = X̃ (y) · H (y)`.
    have hpair : ∀ y, inner ℝ (X (R⁻¹ • (y - c))) (R • H (c + R • R⁻¹ • (y - c))) =
        inner ℝ (R • X (R⁻¹ • (y - c))) (H y) := by
      intro y
      rw [hψφ, real_inner_smul_right, real_inner_smul_left]
    -- `∫ g dμ_W = κ.toReal • ∫ g ∘ φ dμ_V` on both sides, then the first variation of `V` at `X̃`.
    rw [hw', integral_smul_measure, integral_smul_measure, integral_map_equiv, integral_map_equiv]
    show (ENNReal.ofReal (R ^ n))⁻¹.toReal • ∫ y, W.divM X (R⁻¹ • (y - c)) ∂V.weight =
      -((ENNReal.ofReal (R ^ n))⁻¹.toReal •
        ∫ y, inner ℝ (X (R⁻¹ • (y - c))) (R • H (c + R • R⁻¹ • (y - c))) ∂V.weight)
    simp only [hdiv, hpair, key, smul_neg]
/-- **Translation and dilation of rectifiable varifolds** (fact (Inv) for Simon 5.3).  For
`ψ(x) = c + R x` with `R > 0`, there is a varifold `V' = v(ψ⁻¹M, θ ∘ ψ)` in `U' = ψ⁻¹(U)` with
weight `R⁻ⁿ φ_# μ_V` (`φ(y) = R⁻¹(y − c)`), support `ψ⁻¹(spt V)` and tangent projections
`p_{T_x M'} = p_{T_{ψ(x)} M}`; if `V` has generalized mean curvature `H` in `U`, then `V'` has
generalized mean curvature `R H ∘ ψ` in `U'`.
Proof: `any_radius_rv_exists_structure` gives `V'` with carrier `ψ⁻¹M` and multiplicity `θ ∘ ψ`.
These two identities give the weight (`any_radius_rv_weight_eq`) and the tangent projections
(`any_radius_rv_tangentProj_eq`), and the weight and tangent projections in turn give the support
(`any_radius_rv_support_eq`) and the mean curvature (`any_radius_rv_meanCurvature`). -/
theorem any_radius_rescaled_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (c : Amb n ℓ) (R : ℝ), 0 < R → ∃ V' : RectifiableVarifold n ℓ ((fun x => c + R • x) ⁻¹' U), V'.carrier = (fun x => c + R • x) ⁻¹' V.carrier ∧ (∀ x, V'.mult x = V.mult (c + R • x)) ∧ V'.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c)) ∧ V'.support = (fun x => c + R • x) ⁻¹' V.support ∧ (∀ x, V'.tangentProj x = V.tangentProj (c + R • x)) ∧ ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => R • H (c + R • x)) := by
  intro n ℓ U _ V c R hR
  -- Steps 1–2: `V' = v(ψ⁻¹M, θ ∘ ψ)` is a rectifiable varifold in `ψ⁻¹(U)`.
  obtain ⟨V', hcarrier, hmult⟩ := Submission.any_radius_rv_exists_structure n ℓ U V c R hR
  -- Step 3: `μ_{V'} = R⁻ⁿ φ_# μ_V`, by change of variables.
  have hweight := Submission.any_radius_rv_weight_eq n ℓ U _ V V' c R hR hcarrier hmult
  -- Step 5: the blow-ups of `(ψ⁻¹M, θ ∘ ψ)` at `x` are those of `(M, θ)` at `ψ(x)`.
  have htangent := Submission.any_radius_rv_tangentProj_eq n ℓ U _ V V' c R hR hcarrier hmult
  -- Steps 4 and 6: support and first variation depend only on the weight and tangent planes.
  exact ⟨V', hcarrier, hmult, hweight,
    Submission.any_radius_rv_support_eq n ℓ U V c R hR V' hweight, htangent,
    fun H hH => Submission.any_radius_rv_meanCurvature n ℓ U V c R hR V' hweight htangent H hH⟩
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

/-- **Monotonicity consequences of 2.3** (Simon Ch. 4, 4.1–4.10, with the coefficient
`κ = (p-n)/(4p)` in 4.2).  With `Λ = 4pδ/(p-n) ≤ 1`, `A = ‖H‖_{Lᵖ(B_ρ(0))}` (so `A ρ^α ≤ δ`,
`α = 1 - n/p`) and smooth cutoffs `χ_b` (`1` on `(-∞, 1]`, `0` on `[b, ∞)`), the first variation
of `V` applied to `X_σ(x) = χ_b(|x - y|²/σ²)(x - y)` gives, for `I(σ) = ∫ χ_b dμ_V` and any
weight `0 ≤ w ≤ |p_x^⊥(x - y)|²/|x - y|^(n+2)` with `L(σ) = ∫ χ_b w dμ_V`, the differential
inequality `L' ≤ (σ⁻ⁿI)' + b A σ^(α-1)(1 + σ⁻ⁿI)` (Hölder for the mean curvature term).  With
`w = 0` the integrating factor `exp(b A σ^α/α) ≤ e^(bΛ/4)` makes `(1 + σ⁻ⁿI) exp(b A σ^α/α)`
nondecreasing; letting `b ↓ 1` gives `1 + s⁻ⁿμ(B_s(y)) ≤ (1 + r⁻ⁿμ(B_r(y))) e^(Λ/4)`, hence (M1).
At points where `Θⁿ(μ_V, ·) = θ ≥ 1` (a.e., `any_radius_tangent_ae`) this gives the lower bound
`s⁻ⁿμ(B_s) ≥ (1 + ω_n)e^(-Λ/4) - 1`, which passes to every support point by approximation, hence
(M2).  With `w = 1_{|x| > t}|x - p_x x|²/|x|^(n+2)` and `y = 0` the same inequality bounds the
annular integrals, and monotone convergence over annuli exhausting `B̆_ρ(0) \ {0}` gives (M3). -/
theorem any_radius_monotonicity_bounds : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ (p - n) / (4 * p) → V.AllardHypotheses H p δ ρ → (∀ (y : Amb n ℓ) (R s r : ℝ), 0 < s → s ≤ r → r < R → closedBall y R ⊆ closedBall 0 ρ → (V.weight (closedBall y s)).toReal / s ^ n ≤ Real.exp (2 * (4 * p * δ / (p - n))) * ((V.weight (closedBall y r)).toReal / r ^ n) + 2 * Real.exp (4 * p * δ / (p - n)) * (4 * p * δ / (p - n))) ∧ (∀ y ∈ V.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ → Real.exp (-(4 * p * δ / (p - n))) * (unitBallVolume n - 4 * p * δ / (p - n)) * s ^ n ≤ (V.weight (closedBall y s)).toReal) ∧ ∫⁻ x in ball (0 : Amb n ℓ) ρ, ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp (4 * p * δ / (p - n)) * (Real.exp (4 * p * δ / (p - n)) * (1 + δ) * unitBallVolume n + 4 * p * δ / (p - n) - unitBallVolume n)) := by
  have key : ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), (n : ℝ) < p → ∀ (δ ρ : ℝ), 0 < δ →
      δ ≤ (p - n) / (4 * p) → 0 < ρ →
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        [MeasurableSpace E] [BorelSpace E]
        (μ : Measure E) (P : E → E →L[ℝ] E) (H : E → E) (θ : E → ℝ) (ω : ℝ), 0 < ω →
      μ (closedBall 0 ρ) ≤ ENNReal.ofReal ((1 + δ) * (ω * ρ ^ n)) →
      (∀ X : E → E, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ closedBall 0 ρ →
        ∫ x, LinearMap.trace ℝ E ((fderiv ℝ X x).toLinearMap ∘ₗ (P x).toLinearMap) ∂μ =
          -∫ x, inner ℝ (X x) (H x) ∂μ) →
      (∀ᵐ x ∂μ, ∃ T : Submodule ℝ E, Module.finrank ℝ T = n ∧ P x = T.starProjection) →
      AEStronglyMeasurable P μ → AEStronglyMeasurable H (μ.restrict (closedBall 0 ρ)) →
      (ENNReal.ofReal (ρ ^ (p - n)) * ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤
        ENNReal.ofReal δ →
      (∀ᵐ x ∂μ, Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (ω * r ^ n))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (θ x)))) →
      (∀ᵐ x ∂μ, 1 ≤ θ x) → (0 : E) ∈ μ.support → (∃ v : E, ‖v‖ = 1) →
      (∀ (y : E) (R s r : ℝ), 0 < s → s ≤ r → r < R → closedBall y R ⊆ closedBall 0 ρ →
        (μ (closedBall y s)).toReal / s ^ n ≤ Real.exp (2 * (4 * p * δ / (p - n))) *
          ((μ (closedBall y r)).toReal / r ^ n) + 2 * Real.exp (4 * p * δ / (p - n)) *
            (4 * p * δ / (p - n))) ∧
      (∀ y ∈ μ.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ →
        Real.exp (-(4 * p * δ / (p - n))) * (ω - 4 * p * δ / (p - n)) * s ^ n ≤
          (μ (closedBall y s)).toReal) ∧
      ∫⁻ x in ball (0 : E) ρ, ENNReal.ofReal (‖x - P x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂μ ≤
        ENNReal.ofReal (Real.exp (4 * p * δ / (p - n)) * (Real.exp (4 * p * δ / (p - n)) *
          (1 + δ) * ω + 4 * p * δ / (p - n) - ω)) := by
    intro n hn p hp δ ρ hδ hδκ hρ E _ _ _ _ _ μ P H θ ω hω hmass hFV htan hPm hHm hLp hdens hθ1
      h0supp hunit
    -- constants
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hp0 : 0 < p := hn0.trans hp
    have hpn : 0 < p - n := sub_pos.mpr hp
    have hp1 : 1 < p := (Nat.one_le_cast.mpr hn).trans_lt hp
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 4 * p * δ / (p - n) := ⟨_, rfl⟩
    rw [← hΛ]
    have hΛ0 : 0 < Λ := hΛ ▸ div_pos (mul_pos (mul_pos four_pos hp0) hδ) hpn
    have hΛ1 : Λ ≤ 1 := by
      rw [hΛ, div_le_one hpn]
      have h := (le_div_iff₀ (mul_pos four_pos hp0)).mp hδκ
      calc 4 * p * δ = δ * (4 * p) := by ring
        _ ≤ p - n := h
    obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (p - n) / p := ⟨_, rfl⟩
    have hα0 : 0 < α := hα ▸ div_pos hpn hp0
    have hδα : δ / α = Λ / 4 := by
      rw [hα, hΛ]
      field_simp
    -- the weight restricted to `B_ρ(0)`
    have hμρ : μ (closedBall (0 : E) ρ) < ∞ := hmass.trans_lt ENNReal.ofReal_lt_top
    obtain ⟨ν, hν⟩ : ∃ ν : Measure E, ν = μ.restrict (closedBall 0 ρ) := ⟨_, rfl⟩
    have : IsFiniteMeasure ν := by rw [hν]; exact isFiniteMeasure_restrict.mpr hμρ.ne
    have hHmν : AEStronglyMeasurable H ν := by rw [hν]; exact hHm
    have hPmν : AEStronglyMeasurable P ν := by rw [hν]; exact hPm.restrict
    -- the `Lᵖ` constant `A = ‖H‖_{Lᵖ(B_ρ(0))}`, with `A ρ^α ≤ δ`
    obtain ⟨JH, hJH⟩ : ∃ JH : ℝ≥0∞, JH = ∫⁻ x, ‖H x‖ₑ ^ p ∂ν := ⟨_, rfl⟩
    have hLp' : ENNReal.ofReal (ρ ^ α) * JH ^ (1 / p) ≤ ENNReal.ofReal δ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hρ.le _) (one_div_nonneg.mpr hp0.le),
        ← Real.rpow_mul hρ.le, ← div_eq_mul_one_div] at hLp
      rw [hα, hJH, hν]
      exact hLp
    have hJHfin : JH ^ (1 / p) ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ α)).ne'] at hLp'
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hLp')
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (JH ^ (1 / p)).toReal := ⟨_, rfl⟩
    have hA0 : 0 ≤ A := hA ▸ ENNReal.toReal_nonneg
    have hAδ : A * ρ ^ α ≤ δ := by
      rw [← ENNReal.ofReal_toReal hJHfin, ← hA, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _),
        ENNReal.ofReal_le_ofReal_iff hδ.le, mul_comm] at hLp'
      exact hLp'
    have hAΛ : ∀ r : ℝ, 0 ≤ r → r ≤ ρ → A * (r ^ α / α) ≤ Λ / 4 := by
      intro r hr hrρ
      rw [← hδα, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hr hrρ hα0.le) hA0).trans hAδ) hα0.le
    -- the cutoff `χ_b`: `1` on `(-∞, 1]`, `0` on `[b, ∞)`, nonincreasing
    obtain ⟨χ, hχC, hχ1, hχ0, hχ01, hχd0, hχsupp, hχB⟩ : ∃ χ : ℝ → ℝ → ℝ,
        (∀ b, ContDiff ℝ 1 (χ b)) ∧
        (∀ b, 1 < b → ∀ s, s ≤ 1 → χ b s = 1) ∧ (∀ b, 1 < b → ∀ s, b ≤ s → χ b s = 0) ∧
        (∀ b s, 0 ≤ χ b s ∧ χ b s ≤ 1) ∧ (∀ b, 1 < b → ∀ s, deriv (χ b) s ≤ 0) ∧
        (∀ b, 1 < b → ∀ s, deriv (χ b) s ≠ 0 → 1 ≤ s ∧ s ≤ b) ∧
        (∀ b, 1 < b → ∃ C, 0 ≤ C ∧ ∀ s, |deriv (χ b) s| ≤ C) := by
      have hC : ∀ b : ℝ, ContDiff ℝ 1 (fun s => Real.smoothTransition ((b - s) / (b - 1))) :=
        fun b => Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
      have hsupp : ∀ b : ℝ, 1 < b → ∀ s,
          deriv (fun s => Real.smoothTransition ((b - s) / (b - 1))) s ≠ 0 → 1 ≤ s ∧ s ≤ b := by
        intro b hb s hs
        by_contra hcon
        rw [not_and_or, not_le, not_le] at hcon
        apply hs
        rcases hcon with h | h
        · have : (fun s => Real.smoothTransition ((b - s) / (b - 1))) =ᶠ[𝓝 s] fun _ => 1 := by
            filter_upwards [Iio_mem_nhds h] with t ht
            exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hb)).mpr
              (by linarith only [show t < 1 from ht]))
          rw [this.deriv_eq, deriv_const]
        · have : (fun s => Real.smoothTransition ((b - s) / (b - 1))) =ᶠ[𝓝 s] fun _ => 0 := by
            filter_upwards [Ioi_mem_nhds h] with t ht
            exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
              (by linarith only [show b < t from ht]) (by linarith only [hb]))
          rw [this.deriv_eq, deriv_const]
      refine ⟨fun b s => Real.smoothTransition ((b - s) / (b - 1)), hC, fun b hb s hs => ?_,
        fun b hb s hs => ?_, fun b s => ⟨Real.smoothTransition.nonneg _,
          Real.smoothTransition.le_one _⟩, fun b hb s => ?_, hsupp, fun b hb => ?_⟩
      · exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hb)).mpr
          (by linarith only [hs]))
      · exact Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) (by linarith only [hb]))
      · exact Antitone.deriv_nonpos fun x y hxy => Real.smoothTransition.monotone
          (div_le_div_of_nonneg_right (by linarith only [hxy]) (by linarith only [hb]))
      · obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := b)).exists_bound_of_continuousOn
          ((hC b).continuous_deriv le_rfl).continuousOn
        refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
        by_cases hs : deriv (fun s => Real.smoothTransition ((b - s) / (b - 1))) s = 0
        · rw [hs, abs_zero]; exact le_max_right _ _
        · rw [← Real.norm_eq_abs]; exact (hCb s (hsupp b hb s hs)).trans (le_max_left _ _)
    -- `K b y σ x = χ_b(|x - y|²/σ²)` and `D b y σ x = χ_b'(|x - y|²/σ²)`
    obtain ⟨K, hK⟩ : ∃ K : ℝ → E → ℝ → E → ℝ, ∀ b y σ x, K b y σ x = χ b (‖x - y‖ ^ 2 / σ ^ 2) :=
      ⟨_, fun _ _ _ _ => rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℝ → E → ℝ → E → ℝ,
        ∀ b y σ x, D b y σ x = deriv (χ b) (‖x - y‖ ^ 2 / σ ^ 2) := ⟨_, fun _ _ _ _ => rfl⟩
    have hgc : ∀ (y : E) (σ : ℝ), Continuous fun x : E => ‖x - y‖ ^ 2 / σ ^ 2 := fun y σ =>
      ((continuous_id.sub continuous_const).norm.pow 2).div_const _
    have hKc : ∀ b y σ, Continuous (K b y σ) := fun b y σ => by
      rw [show K b y σ = _ from funext (hK b y σ)]; exact (hχC b).continuous.comp (hgc y σ)
    have hDc : ∀ b y σ, Continuous (D b y σ) := fun b y σ => by
      rw [show D b y σ = _ from funext (hD b y σ)]
      exact ((hχC b).continuous_deriv le_rfl).comp (hgc y σ)
    have hK01 : ∀ b y σ x, 0 ≤ K b y σ x ∧ K b y σ x ≤ 1 := fun b y σ x => by
      rw [hK]; exact hχ01 b _
    have hDneg : ∀ b, 1 < b → ∀ y σ x, D b y σ x ≤ 0 := fun b hb y σ x => by
      rw [hD]; exact hχd0 b hb _
    have hDsupp : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ) (x : E), 0 < σ → D b y σ x ≠ 0 →
        σ ^ 2 ≤ ‖x - y‖ ^ 2 ∧ ‖x - y‖ ^ 2 ≤ b * σ ^ 2 := by
      intro b hb y σ x hσ hd
      rw [hD] at hd
      obtain ⟨h1, h2⟩ := hχsupp b hb _ hd
      exact ⟨(one_le_div (pow_pos hσ 2)).mp h1, (div_le_iff₀ (pow_pos hσ 2)).mp h2⟩
    have hDB : ∀ b, 1 < b → ∃ C, 0 ≤ C ∧ ∀ y σ x, |D b y σ x| ≤ C := by
      intro b hb
      obtain ⟨C, hC0, hC⟩ := hχB b hb
      exact ⟨C, hC0, fun y σ x => by rw [hD]; exact hC _⟩
    have hK0 : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ) (x : E), 0 < σ → b * σ < ‖x - y‖ → K b y σ x = 0 := by
      intro b hb y σ x hσ hx
      rw [hK]
      apply hχ0 b hb
      rw [le_div_iff₀ (pow_pos hσ 2)]
      calc b * σ ^ 2 ≤ (b * σ) ^ 2 := by
            rw [mul_pow]; exact mul_le_mul_of_nonneg_right (le_self_pow₀ hb.le two_ne_zero)
              (sq_nonneg σ)
        _ ≤ ‖x - y‖ ^ 2 := (pow_lt_pow_left₀ hx (mul_pos (one_pos.trans hb) hσ).le two_ne_zero).le
    have hK1 : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ) (x : E), 0 < σ → ‖x - y‖ ≤ σ → K b y σ x = 1 := by
      intro b hb y σ x hσ hx
      rw [hK]
      exact hχ1 b hb _ ((div_le_one (pow_pos hσ 2)).mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2))
    have hKd : ∀ b (y x : E) (σ : ℝ), 0 < σ →
        HasDerivAt (fun τ => K b y τ x) (D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3)) σ := by
      intro b y x σ hσ
      have hq : HasDerivAt (fun τ => ‖x - y‖ ^ 2 / τ ^ 2) (-2 * ‖x - y‖ ^ 2 / σ ^ 3) σ := by
        refine ((hasDerivAt_const σ (‖x - y‖ ^ 2)).div (hasDerivAt_pow 2 σ)
          (pow_ne_zero 2 hσ.ne')).congr_deriv ?_
        rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hσ.ne')) (pow_ne_zero 3 hσ.ne')]
        ring
      rw [show (fun τ => K b y τ x) = fun τ => χ b (‖x - y‖ ^ 2 / τ ^ 2) from
        funext fun τ => hK b y τ x, hD]
      exact ((hχC b).differentiable one_ne_zero _).hasDerivAt.comp σ hq
    -- pointwise facts about the tangent projections
    have hPae : ∀ᵐ x ∂ν, ∀ v : E, ‖P x v‖ ≤ ‖v‖ ∧ ‖v - P x v‖ ≤ ‖v‖ ∧
        ‖P x v‖ ^ 2 = ‖v‖ ^ 2 - ‖v - P x v‖ ^ 2 := by
      filter_upwards [hν ▸ ae_restrict_of_ae htan] with x hx v
      obtain ⟨T, -, hT⟩ := hx
      rw [hT]
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
        (T.starProjection_inner_eq_zero v _ (T.starProjection_apply_mem v))
      rw [sub_add_cancel] at hpy
      refine ⟨T.norm_starProjection_apply_le v, ?_, ?_⟩
      · refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr ?_
        rw [hpy]
        exact le_add_of_nonneg_right (mul_self_nonneg _)
      · rw [sq, sq, sq, hpy]; ring
    -- radial first variation: `X_σ(x) = χ_b(|x-y|²/σ²)(x - y)` (Simon Ch. 4, 4.1 before `d/dσ`)
    have FV : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ), 0 < σ → closedBall y (b * σ) ⊆ closedBall 0 ρ →
        ∫ x, ((n : ℝ) * K b y σ x + 2 / σ ^ 2 * D b y σ x * ‖P x (x - y)‖ ^ 2) ∂ν =
          -∫ x, inner ℝ (K b y σ x • (x - y)) (H x) ∂ν := by
      intro b hb y σ hσ hsub
      have hXz : ∀ x, x ∉ closedBall y (b * σ) → K b y σ x • (x - y) = 0 := fun x hx => by
        rw [mem_closedBall, dist_eq_norm, not_le] at hx
        rw [hK0 b hb y σ x hσ hx, zero_smul]
      have hXc : ContDiff ℝ 1 (fun x => K b y σ x • (x - y)) := by
        rw [show K b y σ = _ from funext (hK b y σ)]
        exact ((hχC b).comp ((((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _)).smul
          (contDiff_id.sub contDiff_const)
      have hXts : tsupport (fun x => K b y σ x • (x - y)) ⊆ closedBall y (b * σ) :=
        closure_minimal (Function.support_subset_iff'.mpr hXz) isClosed_closedBall
      have hdiv0 : ∀ x, x ∉ closedBall (0 : E) ρ → LinearMap.trace ℝ E
          ((fderiv ℝ (fun x => K b y σ x • (x - y)) x).toLinearMap ∘ₗ (P x).toLinearMap) = 0 := by
        intro x hx
        have hfd : fderiv ℝ (fun x => K b y σ x • (x - y)) x = 0 := by
          by_contra hne
          exact hx (hsub (hXts (support_fderiv_subset ℝ hne)))
        rw [hfd, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_comp, map_zero]
      have hinn0 : ∀ x, x ∉ closedBall (0 : E) ρ → inner ℝ (K b y σ x • (x - y)) (H x) = 0 :=
        fun x hx => by rw [hXz x (fun h => hx (hsub h)), inner_zero_left]
      have hFV' := ((setIntegral_eq_integral_of_forall_compl_eq_zero hdiv0).trans
        (hFV _ hXc (HasCompactSupport.intro (isCompact_closedBall y (b * σ)) hXz)
          (hXts.trans hsub))).trans
        (congrArg Neg.neg (setIntegral_eq_integral_of_forall_compl_eq_zero hinn0).symm)
      rw [← hν] at hFV'
      refine Eq.trans (integral_congr_ae ?_) hFV'
      filter_upwards [hν ▸ ae_restrict_of_ae htan] with x hx
      obtain ⟨T, hTn, hTx⟩ := hx
      have hKf : HasFDerivAt (K b y σ) (D b y σ x • ((σ ^ 2)⁻¹ • (2 • (innerSL ℝ (x - y)).comp
          (ContinuousLinearMap.id ℝ E)))) x := by
        rw [show K b y σ = _ from funext (hK b y σ), hD]
        exact ((hχC b).differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x
          (((hasFDerivAt_sub_const y).norm_sq).mul_const ((σ ^ 2)⁻¹))
      have hX : HasFDerivAt (fun x => K b y σ x • (x - y)) (K b y σ x • ContinuousLinearMap.id ℝ E +
          (D b y σ x • ((σ ^ 2)⁻¹ • (2 • (innerSL ℝ (x - y)).comp
            (ContinuousLinearMap.id ℝ E)))).smulRight (x - y)) x :=
        hKf.smul (hasFDerivAt_sub_const y)
      rw [hX.fderiv, hTx]
      have hproj : LinearMap.IsProj T (T.starProjection : E →ₗ[ℝ] E) :=
        ⟨fun v => T.starProjection_apply_mem v, fun v hv => T.starProjection_eq_self_iff.mpr hv⟩
      have hcomp : ((K b y σ x • ContinuousLinearMap.id ℝ E +
          (D b y σ x • ((σ ^ 2)⁻¹ • (2 • (innerSL ℝ (x - y)).comp
            (ContinuousLinearMap.id ℝ E)))).smulRight (x - y) : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
          (T.starProjection : E →ₗ[ℝ] E) =
          K b y σ x • (T.starProjection : E →ₗ[ℝ] E) +
            (((D b y σ x • ((σ ^ 2)⁻¹ • (2 • (innerSL ℝ (x - y)).comp
            (ContinuousLinearMap.id ℝ E))) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) ∘ₗ
              (T.starProjection : E →ₗ[ℝ] E)).smulRight (x - y) :=
        LinearMap.ext fun w => rfl
      rw [hcomp, map_add, map_smul, LinearMap.trace_smulRight, hproj.trace, hTn]
      have hinner : inner ℝ (x - y) (T.starProjection (x - y)) = ‖T.starProjection (x - y)‖ ^ 2 := by
        have h0 := T.starProjection_inner_eq_zero (x - y) (T.starProjection (x - y))
          (T.starProjection_apply_mem _)
        rw [inner_sub_left, sub_eq_zero] at h0
        rw [h0, real_inner_self_eq_norm_sq]
      have hLv : (((D b y σ x • ((σ ^ 2)⁻¹ • (2 • (innerSL ℝ (x - y)).comp
            (ContinuousLinearMap.id ℝ E))) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) ∘ₗ
              (T.starProjection : E →ₗ[ℝ] E)) (x - y) =
          D b y σ x * ((σ ^ 2)⁻¹ * (2 • inner ℝ (x - y) (T.starProjection (x - y)))) := rfl
      rw [hLv, hinner, smul_eq_mul, nsmul_eq_mul, div_eq_mul_inv, Nat.cast_ofNat]
      ring
    -- Hölder (Simon Ch. 4, 4.3): `|∫ X_σ · H| ≤ b σ A (∫ χ)^(1 - 1/p)`
    have HOL : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ), 0 < σ →
        |∫ x, inner ℝ (K b y σ x • (x - y)) (H x) ∂ν| ≤
          b * σ * A * (∫ x, K b y σ x * 1 ∂ν) ^ (1 - 1 / p) := by
      intro b hb y σ hσ
      have hint : Integrable (fun x : E => K b y σ x * 1) ν :=
        Integrable.of_bound ((hKc b y σ).aestronglyMeasurable.mul_const 1) 1
          (Eventually.of_forall fun x => by
            rw [mul_one, Real.norm_of_nonneg (hK01 b y σ x).1]; exact (hK01 b y σ x).2)
      have hpq := Real.HolderConjugate.conjExponent hp1
      have hbσ : 0 ≤ b * σ := mul_nonneg (zero_le_one.trans hb.le) hσ.le
      have hpt : ∀ x, ENNReal.ofReal ‖inner ℝ (K b y σ x • (x - y)) (H x)‖ ≤
          ENNReal.ofReal (b * σ) * (‖H x‖ₑ * ENNReal.ofReal (K b y σ x * 1)) := by
        intro x
        have h1 : ‖x - y‖ * K b y σ x ≤ b * σ * K b y σ x := by
          rcases le_or_gt ‖x - y‖ (b * σ) with hx | hx
          · exact mul_le_mul_of_nonneg_right hx (hK01 b y σ x).1
          · rw [hK0 b hb y σ x hσ hx, mul_zero, mul_zero]
        rw [mul_one, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
          ← ENNReal.ofReal_mul hbσ]
        refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
        rw [norm_smul, Real.norm_of_nonneg (hK01 b y σ x).1, mul_comm (K b y σ x)]
        calc ‖x - y‖ * K b y σ x * ‖H x‖ ≤ b * σ * K b y σ x * ‖H x‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = b * σ * (‖H x‖ * K b y σ x) := by ring
      have hHol := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun x => ‖H x‖ₑ)
        (g := fun x => ENNReal.ofReal (K b y σ x * 1)) hHmν.enorm
        ((hKc b y σ).measurable.mul_const 1).ennreal_ofReal.aemeasurable
      have hq : ∫⁻ x, ENNReal.ofReal (K b y σ x * 1) ^ p.conjExponent ∂ν ≤
          ENNReal.ofReal (∫ x, K b y σ x * 1 ∂ν) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => mul_nonneg (hK01 b y σ x).1 zero_le_one)]
        exact lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one
          (ENNReal.ofReal_le_one.mpr ((mul_one _).trans_le (hK01 b y σ x).2)) hpq.symm.lt.le
      have hq' : 1 / p.conjExponent = 1 - 1 / p := by
        rw [one_div, one_div, ← hpq.one_sub_inv]
      have hθ0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr (div_le_one_of_le₀ hp1.le hp0.le)
      have hbound : ∫⁻ x, ENNReal.ofReal ‖inner ℝ (K b y σ x • (x - y)) (H x)‖ ∂ν ≤
          ENNReal.ofReal (b * σ) * (JH ^ (1 / p) *
            ENNReal.ofReal (∫ x, K b y σ x * 1 ∂ν) ^ (1 - 1 / p)) := by
        refine (lintegral_mono hpt).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hq', hJH]
        exact mul_le_mul_right ((hHol.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hq
          (by rw [hq']; exact hθ0)) _))) _
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_lintegral_norm _).trans ((ENNReal.toReal_mono (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hJHfin (ENNReal.rpow_ne_top_of_nonneg
          hθ0 ENNReal.ofReal_ne_top))) hbound).trans (le_of_eq ?_))
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← hA, ENNReal.toReal_ofReal hbσ,
        ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal
          (integral_nonneg fun x => mul_nonneg (hK01 b y σ x).1 zero_le_one)]
      exact (mul_assoc _ _ _).symm
    -- differentiation in `σ` under the integral sign
    have DIFF : ∀ b, 1 < b → ∀ (y : E) (w : E → ℝ) (W : ℝ), AEStronglyMeasurable w ν →
        (∀ᵐ x ∂ν, |w x| ≤ W) → ∀ σ : ℝ, 0 < σ →
        Integrable (fun x => D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x) ν ∧
        HasDerivAt (fun τ => ∫ x, K b y τ x * w x ∂ν)
          (∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x ∂ν) σ := by
      intro b hb y w W hw hW σ hσ
      obtain ⟨C, hC0, hC⟩ := hDB b hb
      have hb0 : 0 ≤ 4 * b / σ := div_nonneg (mul_nonneg zero_le_four (zero_le_one.trans hb.le)) hσ.le
      refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun τ x => K b y τ x * w x)
        (F' := fun τ x => D b y τ x * (-2 * ‖x - y‖ ^ 2 / τ ^ 3) * w x)
        (bound := fun _ => C * (4 * b / σ) * W)
        (Ioo_mem_nhds (half_lt_self hσ) (lt_two_mul_self hσ))
        (Eventually.of_forall fun τ => (hKc b y τ).aestronglyMeasurable.mul hw)
        (Integrable.of_bound ((hKc b y σ).aestronglyMeasurable.mul hw) W (hW.mono fun x hx => ?_))
        (((hDc b y σ).mul ((((continuous_id.sub continuous_const).norm.pow 2).const_mul
          (-2)).div_const _)).aestronglyMeasurable.mul hw)
        (hW.mono fun x hx τ hτ => ?_) (integrable_const _)
        (Eventually.of_forall fun x τ hτ => (hKd b y x τ ((half_pos hσ).trans hτ.1)).mul_const (w x))
      · rw [norm_mul, Real.norm_of_nonneg (hK01 b y σ x).1, Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hK01 b y σ x).2).trans hx
      · have hτ0 : 0 < τ := (half_pos hσ).trans hτ.1
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        by_cases hd : D b y τ x = 0
        · rw [hd, abs_zero, zero_mul, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 hb0) ((abs_nonneg _).trans hx)
        · have hle := (hDsupp b hb y τ x hτ0 hd).2
          have h2 : |-2 * ‖x - y‖ ^ 2 / τ ^ 3| ≤ 4 * b / σ := by
            rw [abs_div, abs_mul, abs_neg, abs_two, abs_of_nonneg (sq_nonneg ‖x - y‖),
              abs_of_pos (pow_pos hτ0 3), div_le_div_iff₀ (pow_pos hτ0 3) hσ]
            calc 2 * ‖x - y‖ ^ 2 * σ ≤ 2 * (b * τ ^ 2) * (2 * τ) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hle zero_le_two)
                    (by linarith only [hτ.1]) hσ.le
                    (mul_nonneg zero_le_two (mul_nonneg (zero_le_one.trans hb.le) (sq_nonneg τ)))
              _ = 4 * b * τ ^ 3 := by ring
          exact mul_le_mul (mul_le_mul (hC _ _ _) h2 (abs_nonneg _) hC0) hx (abs_nonneg _)
            (mul_nonneg hC0 hb0)
    -- the elementary inequality `S⁻¹ I^(1-1/p) ≤ σ^(α-1) (1 + S⁻¹ I)` for `S = σⁿ`
    have hq0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr (div_le_one_of_le₀ hp1.le hp0.le)
    have hq1 : 1 - 1 / p ≤ 1 := sub_le_self _ (one_div_nonneg.mpr hp0.le)
    have RI : ∀ σ : ℝ, 0 < σ → ∀ I : ℝ, 0 ≤ I →
        (σ ^ n)⁻¹ * I ^ (1 - 1 / p) ≤ σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I) := by
      intro σ hσ I hI
      have hS : 0 < (σ ^ n)⁻¹ := inv_pos.mpr (pow_pos hσ n)
      have hexp : ((σ ^ n)⁻¹) ^ (1 - (1 - 1 / p)) = σ ^ (α - 1) := by
        rw [Real.inv_rpow (pow_nonneg hσ.le n), ← Real.rpow_natCast, ← Real.rpow_mul hσ.le,
          ← Real.rpow_neg hσ.le, hα]
        congr 1
        field_simp
        ring
      have ht : ((σ ^ n)⁻¹ * I) ^ (1 - 1 / p) ≤ 1 + (σ ^ n)⁻¹ * I := by
        rcases le_or_gt ((σ ^ n)⁻¹ * I) 1 with h | h
        · exact (Real.rpow_le_one (mul_nonneg hS.le hI) h hq0).trans
            (le_add_of_nonneg_right (mul_nonneg hS.le hI))
        · exact ((Real.rpow_le_rpow_of_exponent_le h.le hq1).trans_eq (Real.rpow_one _)).trans
            (le_add_of_nonneg_left zero_le_one)
      calc (σ ^ n)⁻¹ * I ^ (1 - 1 / p)
          = ((σ ^ n)⁻¹) ^ (1 - (1 - 1 / p)) * ((σ ^ n)⁻¹ * I) ^ (1 - 1 / p) := by
            rw [Real.mul_rpow hS.le hI, ← mul_assoc, ← Real.rpow_add hS, sub_add_cancel,
              Real.rpow_one]
        _ ≤ σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I) := by
            rw [hexp]; exact mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hσ.le _)
    -- `d/dσ σ⁻ⁿ = -n σ⁻ⁿ/σ`
    have hpowd : ∀ σ : ℝ, 0 < σ →
        HasDerivAt (fun σ : ℝ => (σ ^ n)⁻¹) (-(n : ℝ) * (σ ^ n)⁻¹ / σ) σ := by
      intro σ hσ
      refine ((hasDerivAt_pow n σ).inv (pow_ne_zero n hσ.ne')).congr_deriv ?_
      have h1 : σ ^ (n - 1) * σ = σ ^ n := pow_sub_one_mul (Nat.one_le_iff_ne_zero.mp hn) σ
      have hσ' : σ ≠ 0 := hσ.ne'
      rw [← h1]
      field_simp
    -- the differential inequality (Simon Ch. 4, 4.1-4.3): with `I(σ) = ∫ χ_b(|x-y|²/σ²) dν` and
    -- `L(σ) = ∫ χ_b(|x-y|²/σ²) w dν`, `0 ≤ w ≤ |p^⊥(x-y)|²/|x-y|^(n+2)`:
    -- `L' ≤ (σ⁻ⁿ I)' + b A σ^(α-1) (1 + σ⁻ⁿ I)`
    have DI : ∀ b, 1 < b → ∀ (y : E) (σ : ℝ), 0 < σ → closedBall y (b * σ) ⊆ closedBall 0 ρ →
        ∀ (w : E → ℝ) (W : ℝ), AEStronglyMeasurable w ν → (∀ᵐ x ∂ν, |w x| ≤ W) →
        (∀ᵐ x ∂ν, 0 ≤ w x ∧ ‖x - y‖ ^ (n + 2) * w x ≤ ‖(x - y) - P x (x - y)‖ ^ 2) →
        ∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x ∂ν ≤
          (-(n : ℝ) * (σ ^ n)⁻¹ / σ * ∫ x, K b y σ x * 1 ∂ν +
            (σ ^ n)⁻¹ * ∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1 ∂ν) +
          b * A * σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * ∫ x, K b y σ x * 1 ∂ν) := by
      intro b hb y σ hσ hsub w W hw hW hwk
      obtain ⟨C, hC0, hC⟩ := hDB b hb
      have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
      have hS : 0 < σ ^ n := pow_pos hσ n
      have h2σ : 0 < 2 / σ ^ 2 := div_pos two_pos hσ2
      have hmP : AEStronglyMeasurable (fun x : E => ‖P x (x - y)‖ ^ 2) ν :=
        ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂ hPmν
          (continuous_id.sub continuous_const).aestronglyMeasurable).norm.pow 2
      have hint1 : Integrable (fun x : E => K b y σ x * 1) ν :=
        Integrable.of_bound ((hKc b y σ).aestronglyMeasurable.mul_const 1) 1
          (Eventually.of_forall fun x => by
            rw [mul_one, Real.norm_of_nonneg (hK01 b y σ x).1]; exact (hK01 b y σ x).2)
      have hint2 := (DIFF b hb y (fun _ => 1) 1 aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (abs_one).le) σ hσ).1
      have hint4 := (DIFF b hb y w W hw hW σ hσ).1
      have hint3 : Integrable (fun x => (n : ℝ) * K b y σ x +
          2 / σ ^ 2 * D b y σ x * ‖P x (x - y)‖ ^ 2) ν := by
        refine Integrable.of_bound (((hKc b y σ).aestronglyMeasurable.const_mul _).add
          (((hDc b y σ).aestronglyMeasurable.const_mul _).mul hmP))
          (n + 2 / σ ^ 2 * C * (b * σ ^ 2)) (hPae.mono fun x hx => ?_)
        rw [Real.norm_eq_abs]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, Nat.abs_cast, abs_of_nonneg (hK01 b y σ x).1]
          exact mul_le_of_le_one_right (Nat.cast_nonneg n) (hK01 b y σ x).2
        · rw [abs_mul, abs_mul, abs_of_pos h2σ, abs_of_nonneg (sq_nonneg ‖P x (x - y)‖)]
          by_cases hd : D b y σ x = 0
          · rw [hd, abs_zero, mul_zero, zero_mul]
            exact mul_nonneg (mul_nonneg h2σ.le hC0) (mul_nonneg (zero_le_one.trans hb.le) hσ2.le)
          · exact mul_le_mul (mul_le_mul_of_nonneg_left (hC _ _ _) h2σ.le)
              ((pow_le_pow_left₀ (norm_nonneg _) (hx (x - y)).1 2).trans
                (hDsupp b hb y σ x hσ hd).2) (sq_nonneg _) (mul_nonneg h2σ.le hC0)
      have algP : ∀ (d k w' q P2 : ℝ), σ * σ ^ n * (d * (-2 * q / σ ^ 3) * w') + n * (k * 1) -
          σ * (d * (-2 * q / σ ^ 3) * 1) =
          n * k + 2 / σ ^ 2 * d * P2 + 2 / σ ^ 2 * (-d) * (σ ^ n * q * w' - (q - P2)) := by
        intro d k w' q P2
        field_simp
        ring
      have hkey : σ * σ ^ n * (∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x ∂ν) +
          (n : ℝ) * (∫ x, K b y σ x * 1 ∂ν) -
          σ * (∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1 ∂ν) ≤
          |∫ x, inner ℝ (K b y σ x • (x - y)) (H x) ∂ν| := by
        have hlin : σ * σ ^ n * (∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x ∂ν) +
            (n : ℝ) * (∫ x, K b y σ x * 1 ∂ν) -
            σ * (∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1 ∂ν) =
            ∫ x, (σ * σ ^ n * (D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * w x) +
              n * (K b y σ x * 1) - σ * (D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1)) ∂ν := by
          rw [integral_sub, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
          · exact hint4.const_mul _
          · exact hint1.const_mul _
          · exact (hint4.const_mul _).add (hint1.const_mul _)
          · exact hint2.const_mul _
        rw [hlin]
        refine (integral_mono_ae (((hint4.const_mul _).add (hint1.const_mul _)).sub
          (hint2.const_mul _)) hint3 ?_).trans ((FV b hb y σ hσ hsub).trans_le (neg_le_abs _))
        filter_upwards [hPae, hwk] with x hx hwx
        dsimp only [Pi.add_apply, Pi.sub_apply]
        rw [algP]
        have h3 : 2 / σ ^ 2 * (-D b y σ x) * (σ ^ n * ‖x - y‖ ^ 2 * w x -
            (‖x - y‖ ^ 2 - ‖P x (x - y)‖ ^ 2)) ≤ 0 := by
          rw [(hx (x - y)).2.2, sub_sub_cancel]
          by_cases hd : D b y σ x = 0
          · rw [hd, neg_zero, mul_zero, zero_mul]
          · refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h2σ.le
              (neg_nonneg.mpr (hDneg b hb y σ x))) (sub_nonpos.mpr (le_trans ?_ hwx.2))
            have h2 : σ ≤ ‖x - y‖ := (pow_le_pow_iff_left₀ hσ.le (norm_nonneg _) two_ne_zero).mp
              (hDsupp b hb y σ x hσ hd).1
            rw [pow_add, mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ.le h2 n)
              (mul_nonneg (sq_nonneg ‖x - y‖) hwx.1)
        linarith only [h3]
      have hri := RI σ hσ (∫ x, K b y σ x * 1 ∂ν)
        (integral_nonneg fun x => mul_nonneg (hK01 b y σ x).1 zero_le_one)
      have alg : ∀ Iw I I' Ea : ℝ, σ * σ ^ n * Iw + n * I - σ * I' ≤ Ea →
          Ea ≤ b * σ * A * I ^ (1 - 1 / p) →
          (σ ^ n)⁻¹ * I ^ (1 - 1 / p) ≤ σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I) →
          Iw ≤ (-(n : ℝ) * (σ ^ n)⁻¹ / σ * I + (σ ^ n)⁻¹ * I') +
            b * A * σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I) := by
        intro Iw I I' Ea h1 h2 h3
        have hσS : 0 < σ * σ ^ n := mul_pos hσ hS
        have h4 := mul_le_mul_of_nonneg_left h3
          (mul_nonneg hσS.le (mul_nonneg (zero_le_one.trans hb.le) hA0))
        rw [← mul_le_mul_iff_of_pos_left hσS]
        have e : σ * σ ^ n * ((-(n : ℝ) * (σ ^ n)⁻¹ / σ * I + (σ ^ n)⁻¹ * I') +
            b * A * σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I)) =
            σ * I' - n * I + σ * σ ^ n * (b * A) * (σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * I)) := by
          field_simp
          ring
        have e2 : σ * σ ^ n * (b * A) * ((σ ^ n)⁻¹ * I ^ (1 - 1 / p)) =
            b * σ * A * I ^ (1 - 1 / p) := by
          field_simp
        rw [e]
        linarith only [h1, h2, h4, e2]
      exact alg _ _ _ _ hkey (HOL b hb y σ hσ) hri
    -- monotonicity (Simon Ch. 4, 4.4-4.5): `(1 + σ⁻ⁿ I(σ)) exp(b A σ^α/α)` is nondecreasing
    have P1b : ∀ b, 1 < b → ∀ (y : E) (R : ℝ), closedBall y R ⊆ closedBall 0 ρ →
        ∀ s r : ℝ, 0 < s → s ≤ r → b * r < R →
        1 + (s ^ n)⁻¹ * ∫ x, K b y s x * 1 ∂ν ≤
          (1 + (r ^ n)⁻¹ * ∫ x, K b y r x * 1 ∂ν) * Real.exp (b * A * (r ^ α / α)) := by
      intro b hb y R hR s r hs hsr hr
      have hb0 : 0 < b := one_pos.trans hb
      have hGd : ∀ σ ∈ Ioo 0 (R / b), ∃ g, HasDerivAt (fun σ => (1 + (σ ^ n)⁻¹ *
          ∫ x, K b y σ x * 1 ∂ν) * Real.exp (b * A * (σ ^ α / α))) g σ ∧ 0 ≤ g := by
        intro σ hσ
        have hσ0 : 0 < σ := hσ.1
        have hbσ : b * σ < R := by
          have h := hσ.2
          rwa [lt_div_iff₀ hb0, mul_comm] at h
        obtain ⟨-, hI⟩ := DIFF b hb y (fun _ => 1) 1 aestronglyMeasurable_const
          (Eventually.of_forall fun _ => (abs_one).le) σ hσ0
        have hF : HasDerivAt (fun σ => Real.exp (b * A * (σ ^ α / α)))
            (Real.exp (b * A * (σ ^ α / α)) * (b * A * σ ^ (α - 1))) σ := by
          refine ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hσ0.ne')).div_const α).const_mul
            (b * A)).exp).congr_deriv ?_
          rw [mul_div_cancel_left₀ _ hα0.ne']
        have hu : HasDerivAt (fun σ => 1 + (σ ^ n)⁻¹ * ∫ x, K b y σ x * 1 ∂ν)
            (-(n : ℝ) * (σ ^ n)⁻¹ / σ * ∫ x, K b y σ x * 1 ∂ν +
              (σ ^ n)⁻¹ * ∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1 ∂ν) σ :=
          ((hpowd σ hσ0).mul hI).const_add 1
        refine ⟨_, hu.mul hF, ?_⟩
        have hdi := DI b hb y σ hσ0 ((closedBall_subset_closedBall hbσ.le).trans hR) (fun _ => 0) 0
          aestronglyMeasurable_const (Eventually.of_forall fun _ => (abs_zero).le)
          (Eventually.of_forall fun x => ⟨le_rfl, by rw [mul_zero]; exact sq_nonneg _⟩)
        simp only [mul_zero, integral_zero] at hdi
        have hE := Real.exp_pos (b * A * (σ ^ α / α))
        calc (0 : ℝ) ≤ Real.exp (b * A * (σ ^ α / α)) * ((-(n : ℝ) * (σ ^ n)⁻¹ / σ *
              ∫ x, K b y σ x * 1 ∂ν + (σ ^ n)⁻¹ * ∫ x, D b y σ x * (-2 * ‖x - y‖ ^ 2 / σ ^ 3) * 1 ∂ν) +
              b * A * σ ^ (α - 1) * (1 + (σ ^ n)⁻¹ * ∫ x, K b y σ x * 1 ∂ν)) :=
            mul_nonneg hE.le (by linarith only [hdi])
          _ = _ := by ring
      have hmono : MonotoneOn (fun σ => (1 + (σ ^ n)⁻¹ * ∫ x, K b y σ x * 1 ∂ν) *
          Real.exp (b * A * (σ ^ α / α))) (Ioo 0 (R / b)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 (R / b))
          (fun σ hσ => (hGd σ hσ).choose_spec.1.continuousAt.continuousWithinAt) ?_ ?_
        · rw [interior_Ioo]
          exact fun σ hσ => (hGd σ hσ).choose_spec.1.differentiableAt.differentiableWithinAt
        · rw [interior_Ioo]
          intro σ hσ
          rw [(hGd σ hσ).choose_spec.1.deriv]
          exact (hGd σ hσ).choose_spec.2
      have hrR : r < R / b := by rw [lt_div_iff₀ hb0, mul_comm]; exact hr
      refine le_trans ?_ (hmono ⟨hs, hsr.trans_lt hrR⟩ ⟨hs.trans_le hsr, hrR⟩ hsr)
      exact le_mul_of_one_le_right (add_nonneg zero_le_one (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg hs.le n))
        (integral_nonneg fun x => mul_nonneg (hK01 b y s x).1 zero_le_one)))
        (Real.one_le_exp (mul_nonneg (mul_nonneg hb0.le hA0)
          (div_nonneg (Real.rpow_nonneg hs.le _) hα0.le)))
    -- `b_m = 1 + 1/(m+1) ↓ 1`, and `χ_{b_m}(|x-y|²/σ²) → 1_{B_σ(y)}`
    have hbm1 : ∀ m : ℕ, 1 < 1 + 1 / ((m : ℝ) + 1) := fun m =>
      lt_add_of_pos_right 1 Nat.one_div_pos_of_nat
    have hbm : Tendsto (fun m : ℕ => 1 + 1 / ((m : ℝ) + 1)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at h
    have LIM : ∀ (y : E) (w : E → ℝ) (W : ℝ), AEStronglyMeasurable w ν → (∀ᵐ x ∂ν, |w x| ≤ W) →
        ∀ σ : ℝ, 0 < σ → Tendsto (fun m : ℕ => ∫ x, K (1 + 1 / ((m : ℝ) + 1)) y σ x * w x ∂ν)
          atTop (𝓝 (∫ x, (closedBall y σ).indicator w x ∂ν)) := by
      intro y w W hw hW σ hσ
      refine tendsto_integral_of_dominated_convergence (fun _ => W)
        (fun m => (hKc _ y σ).aestronglyMeasurable.mul hw) (integrable_const W)
        (fun m => hW.mono fun x hx => ?_) (Eventually.of_forall fun x => ?_)
      · rw [norm_mul, Real.norm_of_nonneg (hK01 _ y σ x).1, Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hK01 _ y σ x).2).trans hx
      · by_cases hx : x ∈ closedBall y σ
        · rw [indicator_of_mem hx]
          refine tendsto_const_nhds.congr fun m => ?_
          rw [mem_closedBall, dist_eq_norm] at hx
          rw [hK1 _ (hbm1 m) y σ x hσ hx, one_mul]
        · rw [indicator_of_notMem hx]
          rw [mem_closedBall, dist_eq_norm, not_le] at hx
          have hev : ∀ᶠ m : ℕ in atTop, (1 + 1 / ((m : ℝ) + 1)) * σ < ‖x - y‖ :=
            (hbm.mul_const σ).eventually (gt_mem_nhds (by rwa [one_mul]))
          refine tendsto_const_nhds.congr' (hev.mono fun m hm => ?_)
          beta_reduce
          rw [hK0 _ (hbm1 m) y σ x hσ hm, zero_mul]
    -- a closed ball inside `B_ρ(0)` has radius `≤ ρ`
    obtain ⟨v, hv⟩ := hunit
    have hRρ : ∀ (y : E) (R : ℝ), 0 ≤ R → closedBall y R ⊆ closedBall 0 ρ → R ≤ ρ := by
      intro y R hR hsub
      have h1 := hsub (show y + R • v ∈ closedBall y R by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
          Real.norm_of_nonneg hR])
      have h2 := hsub (show y - R • v ∈ closedBall y R by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hv, mul_one,
          Real.norm_of_nonneg hR])
      rw [mem_closedBall_zero_iff] at h1 h2
      have h3 : ‖(y + R • v) - (y - R • v)‖ = 2 * R := by
        rw [add_sub_sub_cancel, ← two_smul ℝ (R • v), norm_smul, norm_smul, hv, mul_one,
          Real.norm_of_nonneg hR, Real.norm_two]
      linarith only [h1, h2, h3, norm_sub_le (y + R • v) (y - R • v)]
    have hνball : ∀ (y : E) (R σ : ℝ), closedBall y R ⊆ closedBall 0 ρ → σ ≤ R →
        ∫ x, (closedBall y σ).indicator (fun _ => (1 : ℝ)) x ∂ν = (μ (closedBall y σ)).toReal := by
      intro y R σ hR hσR
      refine (integral_indicator_one measurableSet_closedBall).trans ?_
      rw [measureReal_def, hν,
        Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.mpr ((closedBall_subset_closedBall hσR).trans hR)]
    -- the monotonicity inequality for the true masses (Simon Ch. 4, 4.6 with `|F - 1| ≤ Λ`)
    have P1 : ∀ (y : E) (R : ℝ), closedBall y R ⊆ closedBall 0 ρ → ∀ s r : ℝ, 0 < s → s ≤ r →
        r < R → 1 + (s ^ n)⁻¹ * (μ (closedBall y s)).toReal ≤
          (1 + (r ^ n)⁻¹ * (μ (closedBall y r)).toReal) * Real.exp (Λ / 4) := by
      intro y R hR s r hs hsr hrR
      have hr0 : 0 < r := hs.trans_le hsr
      have hrρ : r ≤ ρ := hrR.le.trans (hRρ y R (hr0.trans hrR).le hR)
      have hls := LIM y (fun _ => 1) 1 aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (abs_one).le) s hs
      have hlr := LIM y (fun _ => 1) 1 aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (abs_one).le) r hr0
      rw [hνball y R s hR (hsr.trans hrR.le)] at hls
      rw [hνball y R r hR hrR.le] at hlr
      have hexp : Tendsto (fun m : ℕ => Real.exp ((1 + 1 / ((m : ℝ) + 1)) * (Λ / 4))) atTop
          (𝓝 (Real.exp (Λ / 4))) := by
        have h := (hbm.mul_const (Λ / 4)).rexp
        rwa [one_mul] at h
      refine le_of_tendsto_of_tendsto ((hls.const_mul _).const_add 1)
        (((hlr.const_mul _).const_add 1).mul hexp) ?_
      filter_upwards [(hbm.mul_const r).eventually (gt_mem_nhds (by rwa [one_mul] : 1 * r < R))]
        with m hm
      refine (P1b _ (hbm1 m) y R hR s r hs hsr hm).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_)
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hAΛ r hr0.le hrρ) (zero_le_one.trans (hbm1 m).le)
      · exact add_nonneg zero_le_one (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le n))
          (integral_nonneg fun x => mul_nonneg (hK01 _ y r x).1 zero_le_one))
    -- exponential bounds
    have hE0 := Real.exp_pos Λ
    have hE4 : Real.exp (Λ / 4) ≤ Real.exp Λ := Real.exp_le_exp.mpr (by linarith only [hΛ0])
    have hEΛ : Real.exp Λ - 1 ≤ Λ * Real.exp Λ := by
      have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-Λ)) hE0.le
      rw [Real.exp_neg, mul_inv_cancel₀ hE0.ne'] at h
      linarith only [h]
    -- (M1)
    have M1 : ∀ (y : E) (R s r : ℝ), 0 < s → s ≤ r → r < R → closedBall y R ⊆ closedBall 0 ρ →
        (μ (closedBall y s)).toReal / s ^ n ≤ Real.exp (2 * Λ) *
          ((μ (closedBall y r)).toReal / r ^ n) + 2 * Real.exp Λ * Λ := by
      intro y R s r hs hsr hrR hR
      have h := P1 y R hR s r hs hsr hrR
      have hu0 : 0 ≤ (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (hs.le.trans hsr) n)) ENNReal.toReal_nonneg
      have h3 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hΛ0] :
        Λ / 4 ≤ 2 * Λ)) hu0
      rw [div_eq_inv_mul, div_eq_inv_mul]
      linarith only [h, h3, hE4, hEΛ, mul_pos hΛ0 hE0]
    -- lower density bound at points where `Θⁿ(μ, z) = θ(z) ≥ 1` (Simon Ch. 4, 4.7-4.8)
    have DENS : ∀ᵐ z ∂μ, ∀ R' s' : ℝ, 0 < s' → s' < R' → closedBall z R' ⊆ closedBall 0 ρ →
        (1 + ω) * Real.exp (-(Λ / 4)) - 1 ≤ (s' ^ n)⁻¹ * (μ (closedBall z s')).toReal := by
      filter_upwards [hdens, hθ1] with z hz hz1
      intro R' s' hs' hsR' hR'
      have hθ0 : 0 ≤ θ z := zero_le_one.trans hz1
      have hlim : Tendsto (fun t => (t ^ n)⁻¹ * (μ (closedBall z t)).toReal) (𝓝[>] 0)
          (𝓝 (ω * θ z)) := by
        have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hz
        rw [ENNReal.toReal_ofReal hθ0] at h1
        refine (h1.const_mul ω).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : 0 < t ^ n := pow_pos ht n
        rw [Function.comp_apply, ENNReal.toReal_div,
          ENNReal.toReal_ofReal (mul_nonneg hω.le ht0.le)]
        field_simp
      have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 + (t ^ n)⁻¹ * (μ (closedBall z t)).toReal ≤
          (1 + (s' ^ n)⁻¹ * (μ (closedBall z s')).toReal) * Real.exp (Λ / 4) := by
        filter_upwards [Ioc_mem_nhdsGT hs', self_mem_nhdsWithin] with t ht ht0
        exact P1 z R' hR' t s' ht0 ht.2 hsR'
      have h1 := le_of_tendsto (hlim.const_add 1) hle
      have h2 := le_mul_of_one_le_right hω.le hz1
      have h3 := Real.exp_pos (Λ / 4)
      rw [Real.exp_neg, ← div_eq_mul_inv, sub_le_iff_le_add, div_le_iff₀ h3]
      linarith only [h1, h2]
    -- every support point: `c₁ sⁿ ≤ μ(B_s(y))`, `c₁ = (1 + ω) e^(-Λ/4) - 1`
    have M2c : ∀ y ∈ μ.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ →
        ((1 + ω) * Real.exp (-(Λ / 4)) - 1) * s ^ n ≤ (μ (closedBall y s)).toReal := by
      intro y hy R s hs hsR hR
      have hfin : μ (closedBall y s) ≠ ∞ :=
        (measure_mono ((closedBall_subset_closedBall hsR.le).trans hR)).trans_lt hμρ |>.ne
      have hc : ∀ η : ℝ, 0 < η → η < s → ((1 + ω) * Real.exp (-(Λ / 4)) - 1) * (s - η) ^ n ≤
          (μ (closedBall y s)).toReal := by
        intro η hη hηs
        have hpos : 0 < μ (ball y η) := (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hη)
        obtain ⟨z, hz, hzd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
          (ae_restrict_of_ae DENS)
        have hzy : dist z y ≤ η := (mem_ball.mp hz).le
        have hsη : 0 < s - η := sub_pos.mpr hηs
        have h := hzd (R - η) (s - η) hsη (by linarith only [hsR])
          ((closedBall_subset_closedBall' (by linarith only [hzy])).trans hR)
        have hsub : closedBall z (s - η) ⊆ closedBall y s :=
          closedBall_subset_closedBall' (by linarith only [hzy])
        calc ((1 + ω) * Real.exp (-(Λ / 4)) - 1) * (s - η) ^ n
            ≤ ((s - η) ^ n)⁻¹ * (μ (closedBall z (s - η))).toReal * (s - η) ^ n :=
              mul_le_mul_of_nonneg_right h (pow_nonneg hsη.le n)
          _ = (μ (closedBall z (s - η))).toReal := by
              rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hsη.ne'), one_mul]
          _ ≤ (μ (closedBall y s)).toReal := ENNReal.toReal_mono hfin (measure_mono hsub)
      have hlim : Tendsto (fun η => ((1 + ω) * Real.exp (-(Λ / 4)) - 1) * (s - η) ^ n) (𝓝[>] 0)
          (𝓝 (((1 + ω) * Real.exp (-(Λ / 4)) - 1) * s ^ n)) := by
        have h : Tendsto (fun η : ℝ => ((1 + ω) * Real.exp (-(Λ / 4)) - 1) * (s - η) ^ n) (𝓝 0)
            (𝓝 (((1 + ω) * Real.exp (-(Λ / 4)) - 1) * (s - 0) ^ n)) :=
          ((tendsto_const_nhds.sub tendsto_id).pow n).const_mul _
        rw [sub_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto hlim (by
        filter_upwards [Ioo_mem_nhdsGT hs] with η hη
        exact hc η hη.1 hη.2)
    -- `e^(-Λ)(ω - Λ) ≤ c₁`
    have hc1 : Real.exp (-Λ) * (ω - Λ) ≤ (1 + ω) * Real.exp (-(Λ / 4)) - 1 := by
      have e1 : Real.exp (-Λ) ≤ Real.exp (-(Λ / 4)) := Real.exp_le_exp.mpr (by linarith only [hΛ0])
      have e2 : 1 - Λ / 4 ≤ Real.exp (-(Λ / 4)) := by linarith only [Real.add_one_le_exp (-(Λ / 4))]
      have e3 : 1 / 2 ≤ Real.exp (-(Λ / 2)) := by
        linarith only [Real.add_one_le_exp (-(Λ / 2)), hΛ1]
      have e4 : 1 / 4 ≤ Real.exp (-Λ) := by
        have h := mul_le_mul e3 e3 (by norm_num) (Real.exp_pos _).le
        rw [← Real.exp_add, show -(Λ / 2) + -(Λ / 2) = -Λ by ring] at h
        linarith only [h]
      linarith only [mul_le_mul_of_nonneg_left e1 hω.le, mul_le_mul_of_nonneg_left e4 hΛ0.le, e2]
    have M2 : ∀ y ∈ μ.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ →
        Real.exp (-Λ) * (ω - Λ) * s ^ n ≤ (μ (closedBall y s)).toReal := fun y hy R s hs hsR hR =>
      (mul_le_mul_of_nonneg_right hc1 (pow_nonneg hs.le n)).trans (M2c y hy R s hs hsR hR)
    -- (M3): the weights `w_t = 1_{|x| > t} |x - p_x x|²/|x|^(n+2)` (Simon Ch. 4, 4.9)
    obtain ⟨k, hk⟩ : ∃ k : E → ℝ, ∀ x, k x = ‖x - P x x‖ ^ 2 / ‖x‖ ^ (n + 2) := ⟨_, fun _ => rfl⟩
    have hk0 : ∀ x, 0 ≤ k x := fun x => by
      rw [hk]; exact div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have hSm : ∀ t : ℝ, MeasurableSet {x : E | t < ‖x‖} := fun t =>
      measurableSet_lt measurable_const continuous_norm.measurable
    have hwm : ∀ t : ℝ, AEStronglyMeasurable ({x : E | t < ‖x‖}.indicator k) ν := by
      intro t
      refine AEStronglyMeasurable.indicator ?_ (hSm t)
      rw [show k = fun x => ‖x - P x x‖ ^ 2 / ‖x‖ ^ (n + 2) from funext hk]
      exact ((aestronglyMeasurable_id.sub ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂
        hPmν aestronglyMeasurable_id)).norm.pow 2).div₀
        ((continuous_norm.pow (n + 2)).aestronglyMeasurable)
    have hwb : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂ν, |{x : E | t < ‖x‖}.indicator k x| ≤ (t ^ n)⁻¹ := by
      intro t ht
      filter_upwards [hPae] with x hx
      by_cases hxt : x ∈ {x : E | t < ‖x‖}
      · rw [indicator_of_mem hxt, abs_of_nonneg (hk0 x), hk]
        have hx0 : 0 < ‖x‖ := ht.trans hxt
        calc ‖x - P x x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ ‖x‖ ^ 2 / ‖x‖ ^ (n + 2) :=
              div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hx x).2.1 2)
                (pow_nonneg hx0.le _)
          _ = (‖x‖ ^ n)⁻¹ := by
              rw [pow_add, mul_comm, ← div_div, div_self (pow_ne_zero 2 hx0.ne'), one_div]
          _ ≤ (t ^ n)⁻¹ := inv_anti₀ (pow_pos ht n) (pow_le_pow_left₀ ht.le (le_of_lt hxt) n)
      · rw [indicator_of_notMem hxt, abs_zero]; exact inv_nonneg.mpr (pow_nonneg ht.le n)
    have hwk : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂ν, 0 ≤ {x : E | t < ‖x‖}.indicator k x ∧
        ‖x - 0‖ ^ (n + 2) * {x : E | t < ‖x‖}.indicator k x ≤ ‖(x - 0) - P x (x - 0)‖ ^ 2 := by
      intro t ht
      refine Eventually.of_forall fun x => ?_
      rw [sub_zero]
      by_cases hxt : x ∈ {x : E | t < ‖x‖}
      · rw [indicator_of_mem hxt, hk, mul_comm, div_mul_cancel₀ _
          (pow_ne_zero _ (ht.trans hxt).ne')]
        exact ⟨div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _), le_rfl⟩
      · rw [indicator_of_notMem hxt, mul_zero]; exact ⟨le_rfl, sq_nonneg _⟩
    -- the annular inequality for the cutoff `χ_b` (Simon Ch. 4, 4.7)
    have P2b : ∀ b, 1 < b → ∀ t r : ℝ, 0 < t → t ≤ r → b * r < ρ →
        ∫ x, K b 0 r x * {x : E | t < ‖x‖}.indicator k x ∂ν -
            ∫ x, K b 0 t x * {x : E | t < ‖x‖}.indicator k x ∂ν ≤
          ((r ^ n)⁻¹ * ∫ x, K b 0 r x * 1 ∂ν - (t ^ n)⁻¹ * ∫ x, K b 0 t x * 1 ∂ν) +
          (1 + (r ^ n)⁻¹ * ∫ x, K b 0 r x * 1 ∂ν) * Real.exp (b * A * (r ^ α / α)) *
            (b * A * (r ^ α / α)) := by
      intro b hb t r ht htr hr
      have hb0 : 0 < b := one_pos.trans hb
      obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + (r ^ n)⁻¹ * ∫ x, K b 0 r x * 1 ∂ν) *
          Real.exp (b * A * (r ^ α / α)) := ⟨_, rfl⟩
      have hGd : ∀ σ ∈ Icc t r, ∃ g, HasDerivAt (fun σ =>
          ∫ x, K b 0 σ x * {x : E | t < ‖x‖}.indicator k x ∂ν -
          (σ ^ n)⁻¹ * ∫ x, K b 0 σ x * 1 ∂ν - C * (b * A * (σ ^ α / α))) g σ ∧ g ≤ 0 := by
        intro σ hσ
        have hσ0 : 0 < σ := ht.trans_le hσ.1
        have hbσ : b * σ < ρ := (mul_le_mul_of_nonneg_left hσ.2 hb0.le).trans_lt hr
        obtain ⟨-, hL⟩ := DIFF b hb 0 _ _ (hwm t) (hwb t ht) σ hσ0
        obtain ⟨-, hI⟩ := DIFF b hb 0 (fun _ => 1) 1 aestronglyMeasurable_const
          (Eventually.of_forall fun _ => (abs_one).le) σ hσ0
        have hu : HasDerivAt (fun σ => (σ ^ n)⁻¹ * ∫ x, K b 0 σ x * 1 ∂ν)
            (-(n : ℝ) * (σ ^ n)⁻¹ / σ * ∫ x, K b 0 σ x * 1 ∂ν +
              (σ ^ n)⁻¹ * ∫ x, D b 0 σ x * (-2 * ‖x - 0‖ ^ 2 / σ ^ 3) * 1 ∂ν) σ :=
          (hpowd σ hσ0).mul hI
        have hF : HasDerivAt (fun σ => C * (b * A * (σ ^ α / α))) (C * (b * A * σ ^ (α - 1))) σ := by
          refine ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hσ0.ne')).div_const α).const_mul
            (b * A)).const_mul C).congr_deriv ?_
          rw [mul_div_cancel_left₀ _ hα0.ne']
        refine ⟨_, (hL.sub hu).sub hF, ?_⟩
        have hdi := DI b hb 0 σ hσ0 (closedBall_subset_closedBall hbσ.le) _ _ (hwm t) (hwb t ht)
          (hwk t ht)
        have hP := P1b b hb 0 ρ subset_rfl σ r hσ0 hσ.2 hr
        rw [← hC] at hP
        have h1 := mul_le_mul_of_nonneg_left hP
          (mul_nonneg (mul_nonneg hb0.le hA0) (Real.rpow_nonneg hσ0.le (α - 1)))
        linarith only [hdi, h1]
      have hanti : AntitoneOn (fun σ => ∫ x, K b 0 σ x * {x : E | t < ‖x‖}.indicator k x ∂ν -
          (σ ^ n)⁻¹ * ∫ x, K b 0 σ x * 1 ∂ν - C * (b * A * (σ ^ α / α))) (Icc t r) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc t r)
          (fun σ hσ => (hGd σ hσ).choose_spec.1.continuousAt.continuousWithinAt) ?_ ?_
        · rw [interior_Icc]
          exact fun σ hσ =>
            (hGd σ (Ioo_subset_Icc_self hσ)).choose_spec.1.differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro σ hσ
          rw [(hGd σ (Ioo_subset_Icc_self hσ)).choose_spec.1.deriv]
          exact (hGd σ (Ioo_subset_Icc_self hσ)).choose_spec.2
      have h := hanti ⟨le_rfl, htr⟩ ⟨htr, le_rfl⟩ htr
      have hC0 : 0 ≤ C := hC ▸ mul_nonneg (add_nonneg zero_le_one (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg (ht.le.trans htr) n))
        (integral_nonneg fun x => mul_nonneg (hK01 b 0 r x).1 zero_le_one))) (Real.exp_pos _).le
      have ht0 : 0 ≤ C * (b * A * (t ^ α / α)) := mul_nonneg hC0 (mul_nonneg
        (mul_nonneg hb0.le hA0) (div_nonneg (Real.rpow_nonneg ht.le _) hα0.le))
      rw [← hC]
      beta_reduce at h
      linarith only [h, ht0]
    -- letting `b ↓ 1`
    have P2 : ∀ t r : ℝ, 0 < t → t ≤ r → r < ρ →
        ∫ x, (closedBall (0 : E) r).indicator ({x : E | t < ‖x‖}.indicator k) x ∂ν ≤
          ((r ^ n)⁻¹ * (μ (closedBall 0 r)).toReal - (t ^ n)⁻¹ * (μ (closedBall 0 t)).toReal) +
          (1 + (r ^ n)⁻¹ * (μ (closedBall 0 r)).toReal) * Real.exp (Λ / 4) * (Λ / 4) := by
      intro t r ht htr hrρ
      have hr0 : 0 < r := ht.trans_le htr
      have hL := (LIM 0 _ _ (hwm t) (hwb t ht) r hr0).sub (LIM 0 _ _ (hwm t) (hwb t ht) t ht)
      have hzero : ∫ x, (closedBall (0 : E) t).indicator ({x : E | t < ‖x‖}.indicator k) x ∂ν = 0 := by
        rw [indicator_indicator, show closedBall (0 : E) t ∩ {x : E | t < ‖x‖} = ∅ from
          eq_empty_of_forall_notMem fun x hx => (not_lt.mpr (mem_closedBall_zero_iff.mp hx.1)) hx.2,
          indicator_empty, integral_zero]
      rw [hzero, sub_zero] at hL
      have hur := LIM 0 (fun _ => 1) 1 aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (abs_one).le) r hr0
      have hut := LIM 0 (fun _ => 1) 1 aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (abs_one).le) t ht
      rw [hνball 0 ρ r subset_rfl hrρ.le] at hur
      rw [hνball 0 ρ t subset_rfl (htr.trans hrρ.le)] at hut
      have hexp : Tendsto (fun m : ℕ => Real.exp ((1 + 1 / ((m : ℝ) + 1)) * (Λ / 4))) atTop
          (𝓝 (Real.exp (Λ / 4))) := by
        have h := (hbm.mul_const (Λ / 4)).rexp
        rwa [one_mul] at h
      have hbΛ : Tendsto (fun m : ℕ => (1 + 1 / ((m : ℝ) + 1)) * (Λ / 4)) atTop (𝓝 (Λ / 4)) := by
        have h := hbm.mul_const (Λ / 4)
        rwa [one_mul] at h
      refine le_of_tendsto_of_tendsto hL (((hur.const_mul _).sub (hut.const_mul _)).add
        ((((hur.const_mul _).const_add 1).mul hexp).mul hbΛ)) ?_
      filter_upwards [(hbm.mul_const r).eventually (gt_mem_nhds (by rwa [one_mul] : 1 * r < ρ))]
        with m hm
      refine (P2b _ (hbm1 m) t r ht htr hm).trans ?_
      have hb := hbm1 m
      have hA' : (1 + 1 / ((m : ℝ) + 1)) * A * (r ^ α / α) ≤ (1 + 1 / ((m : ℝ) + 1)) * (Λ / 4) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hAΛ r hr0.le hrρ.le) (zero_le_one.trans hb.le)
      have hu0 : 0 ≤ 1 + (r ^ n)⁻¹ * ∫ x, K (1 + 1 / ((m : ℝ) + 1)) 0 r x * 1 ∂ν :=
        add_nonneg zero_le_one (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le n))
          (integral_nonneg fun x => mul_nonneg (hK01 _ 0 r x).1 zero_le_one))
      have hx0 : 0 ≤ (1 + 1 / ((m : ℝ) + 1)) * A * (r ^ α / α) :=
        mul_nonneg (mul_nonneg (zero_le_one.trans hb.le) hA0)
          (div_nonneg (Real.rpow_nonneg hr0.le _) hα0.le)
      exact add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA') hu0)
        hA' hx0 (mul_nonneg hu0 (Real.exp_pos _).le))
    -- the bound for each annulus
    have hB : ∀ t r : ℝ, 0 < t → t ≤ r → r < ρ →
        ∫⁻ x in closedBall (0 : E) r ∩ {x : E | t < ‖x‖}, ENNReal.ofReal (k x) ∂ν ≤
          ENNReal.ofReal ((1 + δ) * ω * (ρ / r) ^ n - ((1 + ω) * Real.exp (-(Λ / 4)) - 1) +
            (1 + (1 + δ) * ω * (ρ / r) ^ n) * Real.exp (Λ / 4) * (Λ / 4)) := by
      intro t r ht htr hrρ
      have hr0 : 0 < r := ht.trans_le htr
      have hS : MeasurableSet (closedBall (0 : E) r ∩ {x : E | t < ‖x‖}) :=
        measurableSet_closedBall.inter (hSm t)
      have hint : IntegrableOn k (closedBall (0 : E) r ∩ {x : E | t < ‖x‖}) ν := by
        rw [← integrable_indicator_iff hS, ← indicator_indicator]
        exact Integrable.of_bound ((hwm t).indicator measurableSet_closedBall) (t ^ n)⁻¹
          ((hwb t ht).mono fun x hx => by
            rw [Real.norm_eq_abs]
            by_cases hxr : x ∈ closedBall (0 : E) r
            · rw [indicator_of_mem hxr]; exact hx
            · rw [indicator_of_notMem hxr, abs_zero]
              exact inv_nonneg.mpr (pow_nonneg ht.le n))
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => hk0 x),
        ← integral_indicator hS, ← indicator_indicator]
      refine ENNReal.ofReal_le_ofReal ((P2 t r ht htr hrρ).trans ?_)
      have hμr : (μ (closedBall (0 : E) r)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
        ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by linarith only [hδ])
          (mul_nonneg hω.le (pow_nonneg hρ.le n)))
          ((measure_mono (closedBall_subset_closedBall hrρ.le)).trans hmass)
      have hur : (r ^ n)⁻¹ * (μ (closedBall (0 : E) r)).toReal ≤ (1 + δ) * ω * (ρ / r) ^ n := by
        calc (r ^ n)⁻¹ * (μ (closedBall (0 : E) r)).toReal ≤ (r ^ n)⁻¹ * ((1 + δ) * (ω * ρ ^ n)) :=
              mul_le_mul_of_nonneg_left hμr (inv_nonneg.mpr (pow_nonneg hr0.le n))
          _ = (1 + δ) * ω * (ρ / r) ^ n := by rw [div_pow]; ring
      have hut : (1 + ω) * Real.exp (-(Λ / 4)) - 1 ≤ (t ^ n)⁻¹ * (μ (closedBall (0 : E) t)).toReal := by
        rw [le_inv_mul_iff₀ (pow_pos ht n), mul_comm]
        exact M2c 0 h0supp ρ t ht (htr.trans_lt hrρ) subset_rfl
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hur
        (Real.exp_pos (Λ / 4)).le) (by linarith only [hΛ0] : (0 : ℝ) ≤ Λ / 4)
      linarith only [hur, hut, h1]
    -- exhaust `B̆_ρ(0) \ {0}` by the annuli `A_m = {t_m < |x| ≤ ρ - t_m}`, `t_m = ρ/(2(m+1))`
    obtain ⟨tm, htm⟩ : ∃ tm : ℕ → ℝ, tm = fun m : ℕ => ρ / 2 * (1 / ((m : ℝ) + 1)) := ⟨_, rfl⟩
    have htm0 : ∀ m, 0 < tm m := fun m => by
      rw [htm]; exact mul_pos (half_pos hρ) Nat.one_div_pos_of_nat
    have htm2 : ∀ m, tm m ≤ ρ / 2 := fun m => by
      rw [htm]
      exact mul_le_of_le_one_right (half_pos hρ).le
        (div_le_one_of_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg m)) (by positivity))
    have htmlim : Tendsto tm atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ρ / 2)
      rwa [mul_zero, ← htm] at h
    have htmanti : Antitone tm := fun m m' h => by
      rw [htm]; exact mul_le_mul_of_nonneg_left (Nat.one_div_le_one_div h) (half_pos hρ).le
    have htmr : ∀ m, tm m ≤ ρ - tm m := fun m => by linarith only [htm2 m]
    have htmρ : ∀ m, ρ - tm m < ρ := fun m => sub_lt_self ρ (htm0 m)
    obtain ⟨Am, hAm⟩ : ∃ Am : ℕ → Set E,
        Am = fun m => closedBall (0 : E) (ρ - tm m) ∩ {x : E | tm m < ‖x‖} := ⟨_, rfl⟩
    have hAmeas : ∀ m, MeasurableSet (Am m) := fun m => by
      rw [hAm]; exact measurableSet_closedBall.inter (hSm _)
    have hAmono : Monotone Am := fun m m' h x hx => by
      rw [hAm] at hx ⊢
      exact ⟨mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.1).trans
        (sub_le_sub_left (htmanti h) ρ)), (htmanti h).trans_lt hx.2⟩
    have hcover : ball (0 : E) ρ ⊆ (⋃ m, Am m) ∪ {0} := by
      intro x hx
      rcases eq_or_ne x 0 with h0 | h0
      · exact Or.inr h0
      · left
        have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr h0
        have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
        obtain ⟨m, hm⟩ := (htmlim.eventually (gt_mem_nhds (lt_min hx0 (sub_pos.mpr hxρ)))).exists
        refine mem_iUnion.mpr ⟨m, ?_⟩
        rw [hAm]
        exact ⟨mem_closedBall_zero_iff.mpr (by linarith only [hm.trans_le (min_le_right _ _)]),
          hm.trans_le (min_le_left _ _)⟩
    -- the limit of the annular bounds
    have hBlim : Tendsto (fun m => (1 + δ) * ω * (ρ / (ρ - tm m)) ^ n -
        ((1 + ω) * Real.exp (-(Λ / 4)) - 1) +
        (1 + (1 + δ) * ω * (ρ / (ρ - tm m)) ^ n) * Real.exp (Λ / 4) * (Λ / 4)) atTop
        (𝓝 ((1 + δ) * ω * 1 - ((1 + ω) * Real.exp (-(Λ / 4)) - 1) +
          (1 + (1 + δ) * ω * 1) * Real.exp (Λ / 4) * (Λ / 4))) := by
      have h1 : Tendsto (fun m => (ρ / (ρ - tm m)) ^ n) atTop (𝓝 1) := by
        have h : Tendsto (fun m => (ρ / (ρ - tm m)) ^ n) atTop (𝓝 ((ρ / (ρ - 0)) ^ n)) :=
          (tendsto_const_nhds.div (tendsto_const_nhds.sub htmlim)
            (by rw [sub_zero]; exact hρ.ne')).pow n
        rwa [sub_zero, div_self hρ.ne', one_pow] at h
      exact ((h1.const_mul _).sub_const _).add ((((h1.const_mul _).const_add 1).mul_const _).mul_const _)
    -- `e^(-Λ/4) ≥ 1 - Λ/4` and the final numerical inequality
    have hBT : (1 + δ) * ω * 1 - ((1 + ω) * Real.exp (-(Λ / 4)) - 1) +
        (1 + (1 + δ) * ω * 1) * Real.exp (Λ / 4) * (Λ / 4) ≤
        Real.exp Λ * (Real.exp Λ * (1 + δ) * ω + Λ - ω) := by
      have e1 : 1 - Λ / 4 ≤ Real.exp (-(Λ / 4)) := by
        linarith only [Real.add_one_le_exp (-(Λ / 4))]
      have e2 : 1 + Λ ≤ Real.exp Λ := by linarith only [Real.add_one_le_exp Λ]
      have e3 : 1 ≤ Real.exp (Λ / 4) := Real.one_le_exp (by linarith only [hΛ0])
      have h2 : Real.exp Λ * Λ ≤ Real.exp Λ * (Real.exp Λ - 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [e2]) hE0.le
      have h3 : Real.exp (Λ / 4) * Λ ≤ Real.exp Λ * Λ := mul_le_mul_of_nonneg_right hE4 hΛ0.le
      have hEΛ0 := mul_pos hE0 hΛ0
      have h9 : Λ ≤ Real.exp Λ * Λ := le_mul_of_one_le_left hΛ0.le (by linarith only [e2, hΛ0])
      have h4 : 0 ≤ Real.exp Λ * Real.exp Λ - 1 - Real.exp (Λ / 4) * (Λ / 4) := by
        linarith only [h2, h3, e2, hΛ0, hEΛ0]
      have h5 := mul_le_mul_of_nonneg_left (mul_nonneg hδ.le hω.le) h4
      have h6 : 0 ≤ ω * (Real.exp Λ * Real.exp Λ - Real.exp Λ - Real.exp (Λ / 4) * (Λ / 4) - Λ / 4) :=
        mul_nonneg hω.le (by linarith only [h2, h3, h9, hEΛ0])
      have h7 := mul_le_mul_of_nonneg_left e1 hω.le
      have h8 : 0 ≤ Λ * (Real.exp Λ - Real.exp (Λ / 4) / 4 - 1 / 4) :=
        mul_nonneg hΛ0.le (by linarith only [hE4, e2, hΛ0])
      linarith only [h5, h6, h7, h8, e1]
    -- assemble
    have hzero0 : (ν.withDensity fun x => ENNReal.ofReal (k x)) {0} = 0 := by
      rw [withDensity_apply _ (measurableSet_singleton 0), lintegral_singleton]
      have hk00 : k 0 = 0 := by rw [hk, map_zero, sub_zero, norm_zero, zero_pow two_ne_zero, zero_div]
      rw [hk00, ENNReal.ofReal_zero, zero_mul]
    have hball : ∫⁻ x in ball (0 : E) ρ, ENNReal.ofReal (‖x - P x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂μ =
        (ν.withDensity fun x => ENNReal.ofReal (k x)) (ball 0 ρ) := by
      rw [withDensity_apply _ measurableSet_ball, hν, Measure.restrict_restrict measurableSet_ball,
        inter_eq_left.mpr ball_subset_closedBall]
      exact lintegral_congr fun x => by rw [hk]
    refine ⟨M1, M2, ?_⟩
    rw [hball]
    calc (ν.withDensity fun x => ENNReal.ofReal (k x)) (ball 0 ρ)
        ≤ (ν.withDensity fun x => ENNReal.ofReal (k x)) ((⋃ m, Am m) ∪ {0}) := measure_mono hcover
      _ ≤ (ν.withDensity fun x => ENNReal.ofReal (k x)) (⋃ m, Am m) +
          (ν.withDensity fun x => ENNReal.ofReal (k x)) {0} := measure_union_le _ _
      _ = ⨆ m, (ν.withDensity fun x => ENNReal.ofReal (k x)) (Am m) := by
          rw [hzero0, add_zero, hAmono.measure_iUnion]
      _ ≤ ENNReal.ofReal ((1 + δ) * ω * 1 - ((1 + ω) * Real.exp (-(Λ / 4)) - 1) +
          (1 + (1 + δ) * ω * 1) * Real.exp (Λ / 4) * (Λ / 4)) := by
          refine iSup_le fun m => ge_of_tendsto (ENNReal.tendsto_ofReal hBlim)
            (eventually_atTop.mpr ⟨m, fun m' hm' => (measure_mono (hAmono hm')).trans ?_⟩)
          rw [withDensity_apply _ (hAmeas m'), hAm]
          exact hB (tm m') (ρ - tm m') (htm0 m') (htmr m') (htmρ m')
      _ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (1 + δ) * ω + Λ - ω)) :=
          ENNReal.ofReal_le_ofReal hBT
  intro n ℓ hn p hp U hU V H δ ρ hδ hδκ hAllard
  obtain ⟨htan, htanm, hdens⟩ := any_radius_tangent_ae n ℓ hn U hU V
  obtain ⟨hρ, hH, hθ1, h0supp, hballU, hmass, hLp⟩ := hAllard
  obtain ⟨k1, k2, k3⟩ := key n hn p hp δ ρ hδ hδκ hρ V.weight V.tangentProj H V.mult
    (unitBallVolume n) (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.Gamma_pos_of_pos (by positivity))) hmass
    (fun X hX1 hX2 hX3 => hH.2 X hX1 hX2 (hX3.trans hballU))
    (htan.mono fun x hx => hx.imp fun T hT => ⟨hT.1, hT.2.2⟩) htanm
    (hH.1.integrableOn_compact_subset hballU (isCompact_closedBall 0 ρ)).aestronglyMeasurable
    hLp hdens hθ1 h0supp.2
    ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by rw [PiLp.norm_single, norm_one]⟩
  exact ⟨k1, fun y hy => k2 y hy.2, k3⟩

/-- **Mass-ratio pinching at a fixed scale** (node `root.allard_any_radius-a1.pinching-a1`;
Simon Ch. 5, Theorem 6.1 used for Remark 5.3).  Assuming Theorem 6.1, for `γ ∈ (0, 1)` and
`ε ∈ (0, 1/4]` there are `δP > 0` and `cs ∈ (0, (1 - γ)/16]` such that 2.3 with `δ ≤ δP` gives
`μ_V(B_{cs ρ}(y)) ≤ (1 + ε) ω_n (cs ρ)ⁿ` for every `y ∈ spt V ∩ B_{(1+γ)ρ/2}(0)`.

`any_radius_monotonicity_bounds` pinches `ω_n⁻¹ t⁻ⁿ μ_V(B_t(0))` between `Lo δ` and `Up δ`
(`0 < t < ρ`), and Hölder gives `t^{1-n} ∫_{B_t(0)} |H| dμ_V ≤ KH δ`.  If `|y| ≤ κ₀ ρ`, (M1) at `y`
with outer radius `(1 - κ₀) ρ` gives the bound.  Otherwise put `R = |y|/(1 - θ₀)`, dilate by
`any_radius_rescaled_varifold`, and apply 6.1 with `λ = δ̃ = lam δ = Up δ - Lo δ + KH δ`,
`ξ = y/R`, `ρ = θ₀`, `τ = 2λ`.  (M1) and the centre bounds control the comparison ball
`B_{2λθ₀R}(2λ y)`, and (M1) moves the pinching from `B_{(1-δ̃^{1/4})θ₀R}(y)` down to `B_{cs ρ}(y)`.
Every smallness condition on `δ` is a limit as `δ → 0⁺`; the `δ̃^{1/4} |log λ|` term uses
`tendsto_log_mul_rpow_nhdsGT_zero`.  The elementary inequalities are closed by explicit order
lemmas (or `linarith only`), which keeps the proof within the default heartbeat budget. -/
theorem any_radius_pinching : ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ ε : ℝ, 0 < γ → γ < 1 → 0 < ε → ε ≤ 1 / 4 → ∃ δP cs : ℝ, 0 < δP ∧ 0 < cs ∧ cs ≤ (1 - γ) / 16 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → ∀ y ∈ V.support ∩ closedBall 0 ((1 + γ) / 2 * ρ), V.weight (closedBall y (cs * ρ)) ≤ ENNReal.ofReal ((1 + ε) * (unitBallVolume n * (cs * ρ) ^ n)) := by
  intro h61 n ℓ hn p hp γ ε hγ0 hγ1 hε0 hε4
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hp1 : 1 < p := hn1.trans_lt hp
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hpn : 0 < p - n := sub_pos.mpr hp
  /- `ω = ω_n > 0`. -/
  have hω0' : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, unitBallVolume n = ω := ⟨_, rfl⟩
  have hω0 : 0 < ω := hω ▸ hω0'
  have h2ω : 0 < 2 * ω := mul_pos two_pos hω0
  rw [hω]
  /- The constant `C₉ = C(n, ℓ, 2ω_n)` of Theorem 6.1. -/
  obtain ⟨C₉, hC₉⟩ := h61 n ℓ hn (2 * ω) h2ω
  rw [hω] at hC₉
  /- `θ₀ = (1 - γ)/8`. -/
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, θ₀ = (1 - γ) / 8 := ⟨_, rfl⟩
  have hθ₀0 : 0 < θ₀ := by rw [hθ₀]; exact div_pos (sub_pos.mpr hγ1) (by norm_num)
  have hθ₀8 : θ₀ < 1 / 8 := by rw [hθ₀]; linarith only [hγ0]
  /- `κ₀ ∈ (0, 1/4]` with `(1 - κ₀)⁻ⁿ < 1 + ε`. -/
  obtain ⟨κ₀, hκ₀0, hκ₀4, hκ₀ε⟩ : ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 / 4 ∧ ((1 - κ₀) ^ n)⁻¹ < 1 + ε := by
    have h1 : Tendsto (fun k : ℝ => ((1 - k) ^ n)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have h : Tendsto (fun k : ℝ => ((1 - k) ^ n)⁻¹) (𝓝 0) (𝓝 (((1 - 0) ^ n)⁻¹)) :=
        ((tendsto_const_nhds.sub tendsto_id).pow n).inv₀ (by rw [sub_zero, one_pow]; exact one_ne_zero)
      rw [sub_zero, one_pow, inv_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := h1.eventually_lt_const (lt_add_of_pos_right 1 hε0)
    have h3 : ∀ᶠ k in 𝓝[>] (0 : ℝ), k < 1 / 4 :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually_lt_const (by norm_num)
    obtain ⟨k, hk1, hk2, hk3⟩ := (h2.and (h3.and eventually_mem_nhdsWithin)).exists
    exact ⟨k, hk3, hk2.le, hk1⟩
  have hκ1 : 0 < 1 - κ₀ := by linarith only [hκ₀4]
  /- `cs = κ₀ θ₀ / 2`. -/
  obtain ⟨cs, hcs⟩ : ∃ cs : ℝ, cs = κ₀ * θ₀ / 2 := ⟨_, rfl⟩
  have hcs0 : 0 < cs := by rw [hcs]; exact half_pos (mul_pos hκ₀0 hθ₀0)
  have hcs16 : cs ≤ (1 - γ) / 16 := by
    have h1 : κ₀ * θ₀ ≤ 1 / 4 * θ₀ := mul_le_mul_of_nonneg_right hκ₀4 hθ₀0.le
    rw [hcs]
    rw [hθ₀] at h1 ⊢
    linarith only [h1, hγ1]
  /- The quantities depending on `δ`: `Λ = 4pδ/(p - n) = δ/κ`, the monotonicity constants
  `e^{2Λ}` and `2e^Λ Λ`, the two-sided density bounds `Up`, `Lo` at the centre, the Hölder constant
  `KH = (2ω_n)^{1 - 1/p}`, and `lam = Up - Lo + KH δ` (used both as `λ` and as `δ` in 6.1). -/
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ → ℝ, ∀ d, Lam d = 4 * p * d / (p - n) := ⟨_, fun _ => rfl⟩
  obtain ⟨ea, hea⟩ : ∃ ea : ℝ → ℝ, ∀ d, ea d = Real.exp (2 * Lam d) := ⟨_, fun _ => rfl⟩
  obtain ⟨eb, heb⟩ : ∃ eb : ℝ → ℝ, ∀ d, eb d = 2 * Real.exp (Lam d) * Lam d := ⟨_, fun _ => rfl⟩
  obtain ⟨Up, hUp⟩ : ∃ Up : ℝ → ℝ, ∀ d, Up d = ea d * (1 + d) + eb d / ω := ⟨_, fun _ => rfl⟩
  obtain ⟨Lo, hLo⟩ : ∃ Lo : ℝ → ℝ, ∀ d, Lo d = Real.exp (-Lam d) * (ω - Lam d) / ω :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨KH, hKH⟩ : ∃ KH : ℝ, KH = (2 * ω) ^ (1 - 1 / p) := ⟨_, rfl⟩
  have hKH0 : 0 < KH := by rw [hKH]; exact Real.rpow_pos_of_pos h2ω _
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ → ℝ, ∀ d, lam d = Up d - Lo d + KH * d := ⟨_, fun _ => rfl⟩
  obtain ⟨qq, hqq⟩ : ∃ qq : ℝ → ℝ, ∀ d, qq d = lam d ^ (1 / 4 : ℝ) := ⟨_, fun _ => rfl⟩
  /- Elementary bounds for `d ≥ 0`. -/
  have hLam0 : ∀ d, 0 ≤ d → 0 ≤ Lam d := fun d hd => by
    rw [hLam]; exact div_nonneg (mul_nonneg (mul_nonneg zero_le_four hp0.le) hd) hpn.le
  have hea1 : ∀ d, 0 ≤ d → 1 ≤ ea d := fun d hd => by
    rw [hea]; exact Real.one_le_exp (mul_nonneg zero_le_two (hLam0 d hd))
  have heb0 : ∀ d, 0 ≤ d → 0 ≤ eb d := fun d hd => by
    rw [heb]; exact mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos _).le) (hLam0 d hd)
  have hUp1 : ∀ d, 0 ≤ d → 1 ≤ Up d := fun d hd => by
    rw [hUp]
    exact le_add_of_le_of_nonneg ((hea1 d hd).trans (le_mul_of_one_le_right
      (zero_le_one.trans (hea1 d hd)) (le_add_of_nonneg_right hd))) (div_nonneg (heb0 d hd) hω0.le)
  have hLo1 : ∀ d, 0 ≤ d → Lo d ≤ 1 := fun d hd => by
    rw [hLo, div_le_one hω0]
    have h1 := hLam0 d hd
    calc Real.exp (-Lam d) * (ω - Lam d) ≤ Real.exp (-Lam d) * ω :=
          mul_le_mul_of_nonneg_left (sub_le_self ω h1) (Real.exp_pos _).le
      _ ≤ 1 * ω :=
          mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr h1)) hω0.le
      _ = ω := one_mul ω
  have hlam_pos : ∀ d, 0 < d → 0 < lam d := fun d hd => by
    rw [hlam]
    have h1 := hUp1 d hd.le
    have h2 := hLo1 d hd.le
    have h3 : 0 < KH * d := mul_pos hKH0 hd
    linarith only [h1, h2, h3]
  /- Limits as `d → 0⁺`. -/
  have tid : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have tLam : Tendsto Lam (𝓝[>] 0) (𝓝 0) := by
    have h := (tid.const_mul (4 * p)).div_const (p - n)
    rw [mul_zero, zero_div] at h
    exact h.congr fun d => (hLam d).symm
  have tea : Tendsto ea (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun x : ℝ => Real.exp (2 * x) := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [mul_zero, Real.exp_zero] at h
    exact h.congr fun d => (hea d).symm
  have teb : Tendsto eb (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => 2 * Real.exp x * x := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [mul_zero] at h
    exact h.congr fun d => (heb d).symm
  have tUp : Tendsto Up (𝓝[>] 0) (𝓝 1) := by
    have h := (tea.mul (tid.const_add 1)).add (teb.div_const ω)
    rw [add_zero, mul_one, zero_div, add_zero] at h
    exact h.congr fun d => (hUp d).symm
  have tLo : Tendsto Lo (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun x : ℝ => Real.exp (-x) * (ω - x) / ω := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [neg_zero, Real.exp_zero, sub_zero, one_mul, div_self hω0.ne'] at h
    exact h.congr fun d => (hLo d).symm
  have tlam : Tendsto lam (𝓝[>] 0) (𝓝 0) := by
    have h := (tUp.sub tLo).add (tid.const_mul KH)
    rw [sub_self, mul_zero, add_zero] at h
    exact h.congr fun d => (hlam d).symm
  have tqq : Tendsto qq (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => x ^ (1 / 4 : ℝ) := Real.continuous_rpow_const (by norm_num)
    have h := (hc.tendsto 0).comp tlam
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.congr fun d => (hqq d).symm
  have tlog : Tendsto (fun d => qq d * |Real.log (lam d)|) (𝓝[>] 0) (𝓝 0) := by
    have tlam' : Tendsto lam (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tlam, eventually_mem_nhdsWithin.mono fun d hd => hlam_pos d hd⟩
    have h := ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 4)).comp tlam').abs
    rw [abs_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with d hd
    show |Real.log (lam d) * lam d ^ (1 / 4 : ℝ)| = qq d * |Real.log (lam d)|
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hlam_pos d hd).le _), hqq d, mul_comm]
  have tA : Tendsto (fun d => ea d * ((1 + d) * ω * ((1 - κ₀) ^ n)⁻¹) + eb d) (𝓝[>] 0)
      (𝓝 (ω * ((1 - κ₀) ^ n)⁻¹)) := by
    have h := (tea.mul (((tid.const_add 1).mul_const ω).mul_const ((1 - κ₀) ^ n)⁻¹)).add teb
    simp only [add_zero, one_mul] at h
    exact h
  have tB : Tendsto (fun d => ea d * (((1 - qq d) ^ n)⁻¹ * (ea d * (Up d * ω * (1 + 4 * lam d) ^ n) +
      eb d + max C₉ 0 * (qq d * |Real.log (lam d)|) / θ₀ ^ n)) + eb d) (𝓝[>] 0) (𝓝 ω) := by
    have h := (tea.mul ((((tqq.const_sub 1).pow n).inv₀ (by rw [sub_zero, one_pow]; exact one_ne_zero)).mul
      (((tea.mul ((tUp.mul_const ω).mul (((tlam.const_mul 4).const_add 1).pow n))).add teb).add
        ((tlog.const_mul (max C₉ 0)).div_const (θ₀ ^ n))))).add teb
    simp only [sub_zero, one_pow, inv_one, one_mul, mul_zero, add_zero, mul_one, zero_div] at h
    exact h
  /- The finitely many smallness conditions on `δ`, all of which hold for small `δ > 0`. -/
  obtain ⟨P, hP⟩ : ∃ P : ℝ → Prop, ∀ d, P d ↔ (d ≤ (p - n) / (4 * p) ∧ d ≤ 1 / 4 ∧ Up d ≤ 2 ∧
      lam d < 1 / 4 ∧ qq d ≤ 1 / 2 ∧
      ea d * ((1 + d) * ω * ((1 - κ₀) ^ n)⁻¹) + eb d ≤ (1 + ε) * ω ∧
      ea d * (((1 - qq d) ^ n)⁻¹ * (ea d * (Up d * ω * (1 + 4 * lam d) ^ n) + eb d +
        max C₉ 0 * (qq d * |Real.log (lam d)|) / θ₀ ^ n)) + eb d ≤ (1 + ε) * ω) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), P d := by
    have e1 := tid.eventually_lt_const (div_pos hpn (mul_pos four_pos hp0))
    have e2 := tid.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)
    have e3 := tUp.eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
    have e4 := tlam.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)
    have e5 := tqq.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
    have e6 := tA.eventually_lt_const (show ω * ((1 - κ₀) ^ n)⁻¹ < (1 + ε) * ω by
      rw [mul_comm]; exact mul_lt_mul_of_pos_right hκ₀ε hω0)
    have e7 := tB.eventually_lt_const (show ω < (1 + ε) * ω by
      have h := mul_pos hε0 hω0
      linarith only [h])
    filter_upwards [e1, e2, e3, e4, e5, e6, e7] with d h1 h2 h3 h4 h5 h6 h7
    exact (hP d).mpr ⟨h1.le, h2.le, h3.le, h4, h5.le, h6.le, h7.le⟩
  obtain ⟨δP, hδP0, hδP⟩ : ∃ δP > 0, ∀ d, 0 < d → d ≤ δP → P d := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr0, hr⟩ := hev
    refine ⟨r / 2, half_pos hr0, fun d hd0 hdP => hr ?_ hd0⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hd0]
    exact hdP.trans_lt (half_lt_self hr0)
  refine ⟨δP, cs, hδP0, hcs0, hcs16, ?_⟩
  /- Fix the data. -/
  intro U hU V H δ ρ hδ0 hδP' hA y hy
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := (hP δ).mp (hδP δ hδ0 hδP')
  obtain ⟨M1, M2, -⟩ := Submission.any_radius_monotonicity_bounds n ℓ hn p hp U hU V H δ ρ hδ0 c1 hA
  obtain ⟨hρ, hHmc, -, h0supp, hBU, hmass, hK⟩ := hA
  rw [← hLam δ, ← hea δ, ← heb δ] at M1
  rw [← hLam δ, hω] at M2
  rw [hω] at hmass
  have hea0 : 0 ≤ ea δ := zero_le_one.trans (hea1 δ hδ0.le)
  have heb0' : 0 ≤ eb δ := heb0 δ hδ0.le
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  /- Finiteness of masses of balls in `B_ρ(0)`. -/
  have hfinρ : V.weight (closedBall 0 ρ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hfin : ∀ x t, closedBall x t ⊆ closedBall 0 ρ → V.weight (closedBall x t) ≠ ⊤ :=
    fun x t h => ne_top_of_le_ne_top hfinρ (measure_mono h)
  have hmassR : (V.weight (closedBall 0 ρ)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (zero_le_one.trans (le_add_of_nonneg_right hδ0.le)) (mul_pos hω0 hρn).le) hmass
  /- (M1) with the outer radius included: `s⁻ⁿ μ(B_s(z)) ≤ e^{2Λ} R⁻ⁿ μ(B_R(z)) + 2e^Λ Λ`. -/
  have M1' : ∀ (z : Amb n ℓ) (Rz s : ℝ), 0 < s → s ≤ Rz → closedBall z Rz ⊆ closedBall 0 ρ →
      (V.weight (closedBall z s)).toReal / s ^ n ≤
        ea δ * ((V.weight (closedBall z Rz)).toReal / Rz ^ n) + eb δ := by
    intro z Rz s hs hsR hsub
    have hRz : 0 < Rz := hs.trans_le hsR
    rcases hsR.lt_or_eq with hlt | rfl
    · have hlim : Tendsto (fun r : ℝ => ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) + eb δ)
          (𝓝[<] Rz) (𝓝 (ea δ * ((V.weight (closedBall z Rz)).toReal / Rz ^ n) + eb δ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have hc : ContinuousAt (fun r : ℝ => ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) +
            eb δ) Rz := by
          fun_prop (disch := exact pow_ne_zero _ hRz.ne')
        exact hc.tendsto
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hlt] with r hr
      have hr0 : 0 < r := hs.trans hr.1
      calc (V.weight (closedBall z s)).toReal / s ^ n
          ≤ ea δ * ((V.weight (closedBall z r)).toReal / r ^ n) + eb δ :=
            M1 z Rz s r hs hr.1.le hr.2 hsub
        _ ≤ ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) + eb δ := by
            have hmono : (V.weight (closedBall z r)).toReal ≤ (V.weight (closedBall z Rz)).toReal :=
              ENNReal.toReal_mono (hfin z Rz hsub)
                (measure_mono (closedBall_subset_closedBall hr.2.le))
            exact add_le_add_left (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hmono (pow_pos hr0 n).le) hea0) _
    · have h1 : 0 ≤ (V.weight (closedBall z s)).toReal / s ^ n :=
        div_nonneg ENNReal.toReal_nonneg (pow_pos hs n).le
      calc (V.weight (closedBall z s)).toReal / s ^ n
          = 1 * ((V.weight (closedBall z s)).toReal / s ^ n) := (one_mul _).symm
        _ ≤ ea δ * ((V.weight (closedBall z s)).toReal / s ^ n) :=
          mul_le_mul_of_nonneg_right (hea1 δ hδ0.le) h1
        _ ≤ ea δ * ((V.weight (closedBall z s)).toReal / s ^ n) + eb δ :=
          le_add_of_nonneg_right heb0'
  /- Step 1a: two-sided density bounds at the centre. -/
  have hup : ∀ t, 0 < t → t ≤ ρ → (V.weight (closedBall 0 t)).toReal ≤ Up δ * ω * t ^ n := by
    intro t ht htρ
    have h1 := M1' 0 ρ t ht htρ subset_rfl
    have h2 : (V.weight (closedBall 0 ρ)).toReal / ρ ^ n ≤ (1 + δ) * ω := by
      rw [div_le_iff₀ hρn, mul_assoc]
      exact hmassR
    have h3 : (V.weight (closedBall 0 t)).toReal / t ^ n ≤ Up δ * ω := by
      calc (V.weight (closedBall 0 t)).toReal / t ^ n ≤ ea δ * ((1 + δ) * ω) + eb δ :=
            h1.trans (add_le_add_left (mul_le_mul_of_nonneg_left h2 hea0) _)
        _ = Up δ * ω := by
            rw [hUp, add_mul (ea δ * (1 + δ)), div_mul_cancel₀ _ hω0.ne', mul_assoc (ea δ)]
    rwa [div_le_iff₀ (pow_pos ht n)] at h3
  have hlo : ∀ t, 0 < t → t < ρ → Lo δ * ω * t ^ n ≤ (V.weight (closedBall 0 t)).toReal := by
    intro t ht htρ
    have h1 := M2 0 h0supp ρ t ht htρ subset_rfl
    rw [hLo, div_mul_cancel₀ _ hω0.ne']
    exact h1
  have hratio : ∀ t, 0 < t → t < ρ →
      Lo δ ≤ (V.weight (closedBall 0 t)).toReal / (ω * t ^ n) ∧
        (V.weight (closedBall 0 t)).toReal / (ω * t ^ n) ≤ Up δ := by
    intro t ht htρ
    have hωt : 0 < ω * t ^ n := mul_pos hω0 (pow_pos ht n)
    constructor
    · rw [le_div_iff₀ hωt, ← mul_assoc]
      exact hlo t ht htρ
    · rw [div_le_iff₀ hωt, ← mul_assoc]
      exact hup t ht htρ.le
  /- Step 1b: `t^{1-n} ∫_{B_t(0)} |H| dμ ≤ KH δ` for `0 < t ≤ ρ` (Hölder). -/
  have hHint : IntegrableOn H (closedBall 0 ρ) V.weight :=
    hHmc.1.integrableOn_compact_subset hBU (isCompact_closedBall 0 ρ)
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = (∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) :=
    ⟨_, rfl⟩
  have hJb : ENNReal.ofReal (ρ ^ (1 - n / p)) * J ≤ ENNReal.ofReal δ := by
    have hK' : (ENNReal.ofReal (ρ ^ (p - n)) * ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^
        (1 / p) ≤ ENNReal.ofReal δ := hK
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hρ.le _) (one_div_nonneg.mpr hp0.le),
      ← Real.rpow_mul hρ.le, sub_mul, mul_one_div_cancel hp0.ne', mul_one_div] at hK'
    rw [hJ]
    exact hK'
  have hJtop : J ≠ ⊤ := by
    intro hJt
    rw [hJt, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _)).ne'] at hJb
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hJb)
  have hJreal : ρ ^ (1 - n / p) * J.toReal ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hρ.le _),
      ENNReal.toReal_ofReal hδ0.le] at this
  have hexp : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact hp1.le
  have hHold : ∀ t, 0 < t → t ≤ ρ → ∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight ≤
      J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) := by
    intro t ht htρ
    have hsub : closedBall (0 : Amb n ℓ) t ⊆ closedBall 0 ρ := closedBall_subset_closedBall htρ
    have hmeas : AEStronglyMeasurable H (V.weight.restrict (closedBall 0 t)) :=
      hHint.aestronglyMeasurable.mono_set hsub
    have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ zero_lt_one hp1.le hmeas
    unfold eLpNorm' at h
    simp only [ENNReal.rpow_one, div_one, Measure.restrict_apply_univ] at h
    have h2t : 0 < 2 * ω * t ^ n := mul_pos h2ω (pow_pos ht n)
    have hμt : V.weight (closedBall 0 t) ≤ ENNReal.ofReal (2 * ω * t ^ n) := by
      rw [ENNReal.le_ofReal_iff_toReal_le (hfin 0 t hsub) h2t.le]
      exact (hup t ht htρ).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right c3 hω0.le) (pow_pos ht n).le)
    calc ∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight
        ≤ (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) *
            V.weight (closedBall 0 t) ^ (1 - 1 / p) := h
      _ ≤ J * ENNReal.ofReal (2 * ω * t ^ n) ^ (1 - 1 / p) := by
          rw [hJ]
          exact mul_le_mul' (ENNReal.rpow_le_rpow (lintegral_mono_set hsub)
            (one_div_nonneg.mpr hp0.le)) (ENNReal.rpow_le_rpow hμt hexp)
      _ = J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg h2t.le hexp]
  have hHbound : ∀ t, 0 < t → t ≤ ρ → (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight) ≠ ⊤ ∧
      t ^ (1 - (n : ℝ)) * (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal ≤ KH * δ := by
    intro t ht htρ
    have h1 := hHold t ht htρ
    have hne : J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) ≠ ⊤ :=
      ENNReal.mul_ne_top hJtop ENNReal.ofReal_ne_top
    refine ⟨ne_top_of_le_ne_top hne h1, ?_⟩
    have h2t : 0 ≤ 2 * ω * t ^ n := (mul_pos h2ω (pow_pos ht n)).le
    have h2 : (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal ≤
        J.toReal * (2 * ω * t ^ n) ^ (1 - 1 / p) := by
      have := ENNReal.toReal_mono hne h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg h2t _)] at this
    have hid : t ^ (1 - (n : ℝ)) * (2 * ω * t ^ n) ^ (1 - 1 / p) = KH * t ^ (1 - n / p) := by
      rw [hKH, Real.mul_rpow h2ω.le (pow_pos ht n).le, ← Real.rpow_natCast t n,
        ← Real.rpow_mul ht.le, mul_left_comm, ← Real.rpow_add ht]
      congr 2
      ring
    have htp : t ^ (1 - n / p) ≤ ρ ^ (1 - n / p) := by
      apply Real.rpow_le_rpow ht.le htρ
      rw [sub_nonneg, div_le_one hp0]
      exact hp.le
    calc t ^ (1 - (n : ℝ)) * (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal
        ≤ t ^ (1 - (n : ℝ)) * (J.toReal * (2 * ω * t ^ n) ^ (1 - 1 / p)) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.le _)
      _ = J.toReal * (KH * t ^ (1 - n / p)) := by rw [← hid, mul_left_comm]
      _ ≤ J.toReal * (KH * ρ ^ (1 - n / p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htp hKH0.le) ENNReal.toReal_nonneg
      _ = KH * (ρ ^ (1 - n / p) * J.toReal) := by rw [mul_comm J.toReal, mul_assoc]
      _ ≤ KH * δ := mul_le_mul_of_nonneg_left hJreal hKH0.le
  /- The point `y`. -/
  obtain ⟨-, hyB⟩ := hy
  rw [mem_closedBall_zero_iff] at hyB
  have hγρ : γ * ρ ≤ ρ := mul_le_of_le_one_left hρ.le hγ1.le
  have hyρ : ‖y‖ ≤ ρ := by linarith only [hyB, hγρ]
  have hcsρ : 0 < cs * ρ := mul_pos hcs0 hρ
  have hsubcs : closedBall y (cs * ρ) ⊆ closedBall 0 ρ := by
    apply closedBall_subset_closedBall'
    rw [dist_zero_right]
    have h1 : cs * ρ ≤ (1 - γ) / 16 * ρ := mul_le_mul_of_nonneg_right hcs16 hρ.le
    linarith only [h1, hyB, hγρ]
  suffices hreal : (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n ≤ (1 + ε) * ω by
    rw [ENNReal.le_ofReal_iff_toReal_le (hfin y _ hsubcs)
      (mul_nonneg (zero_le_one.trans (le_add_of_nonneg_right hε0.le))
        (mul_pos hω0 (pow_pos hcsρ n)).le)]
    rwa [div_le_iff₀ (pow_pos hcsρ n), mul_assoc] at hreal
  rcases le_or_gt ‖y‖ (κ₀ * ρ) with hya | hyb
  · /- Case (a): `|y| ≤ κ₀ ρ`; (M1) at `y` with outer radius `(1 - κ₀) ρ`. -/
    have hRa : 0 < (1 - κ₀) * ρ := mul_pos hκ1 hρ
    have hsubA : closedBall y ((1 - κ₀) * ρ) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right]
      linarith only [hya]
    have hcsRa : cs * ρ ≤ (1 - κ₀) * ρ := by
      have h1 : cs ≤ 1 - κ₀ := by
        have h2 : κ₀ * θ₀ ≤ 1 / 4 * (1 / 8) := mul_le_mul hκ₀4 hθ₀8.le hθ₀0.le (by norm_num)
        rw [hcs]
        linarith only [h2, hκ₀4]
      exact mul_le_mul_of_nonneg_right h1 hρ.le
    have h1 := M1' y ((1 - κ₀) * ρ) (cs * ρ) hcsρ hcsRa hsubA
    have h2 : (V.weight (closedBall y ((1 - κ₀) * ρ))).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
      (ENNReal.toReal_mono hfinρ (measure_mono hsubA)).trans hmassR
    have h3 : (V.weight (closedBall y ((1 - κ₀) * ρ))).toReal / ((1 - κ₀) * ρ) ^ n ≤
        (1 + δ) * ω * ((1 - κ₀) ^ n)⁻¹ := by
      rw [div_le_iff₀ (pow_pos hRa n), mul_pow, mul_assoc ((1 + δ) * ω),
        inv_mul_cancel_left₀ (pow_ne_zero n hκ1.ne'), mul_assoc]
      exact h2
    calc (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n
        ≤ ea δ * ((V.weight (closedBall y ((1 - κ₀) * ρ))).toReal / ((1 - κ₀) * ρ) ^ n) + eb δ := h1
      _ ≤ ea δ * ((1 + δ) * ω * ((1 - κ₀) ^ n)⁻¹) + eb δ :=
          add_le_add_left (mul_le_mul_of_nonneg_left h3 hea0) _
      _ ≤ (1 + ε) * ω := c6
  · /- Case (b): `|y| > κ₀ ρ`; dilate by `R = |y|/(1 - θ₀)` and apply Theorem 6.1. -/
    have hy0 : 0 < ‖y‖ := (mul_pos hκ₀0 hρ).trans hyb
    have hθ1 : 0 < 1 - θ₀ := by linarith only [hθ₀8]
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖y‖ / (1 - θ₀) := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hRdef]; exact div_pos hy0 hθ1
    have hRn : 0 < R ^ n := pow_pos hR0 n
    have hyR : ‖y‖ = (1 - θ₀) * R := by rw [hRdef, mul_div_cancel₀ _ hθ1.ne']
    have hRρ : R < ρ := by
      have h1 : (1 + γ) / 2 * ρ < (1 - θ₀) * ρ := by
        apply mul_lt_mul_of_pos_right _ hρ
        rw [hθ₀]
        linarith only [hγ1]
      exact lt_of_mul_lt_mul_left ((hyR.symm.trans_le hyB).trans_lt h1) hθ1.le
    have hκR : κ₀ * ρ < R := by
      have h1 : ‖y‖ ≤ R := by rw [hyR]; exact mul_le_of_le_one_left hR0.le (sub_le_self 1 hθ₀0.le)
      exact hyb.trans_le h1
    set l := lam δ
    have hl0 : 0 < l := hlam_pos δ hδ0
    have hl1 : l < 1 := c4.trans (by norm_num)
    have h2l : 0 < 2 * l := mul_pos two_pos hl0
    have hq0 : 0 ≤ qq δ := by rw [hqq]; exact Real.rpow_nonneg hl0.le _
    /- The dilated varifold `V'` (centre `0`, scale `R`). -/
    obtain ⟨V', -, -, hW, -, -, hHV'⟩ := Submission.any_radius_rescaled_varifold n ℓ U hU V 0 R hR0
    have hH' := hHV' H hHmc
    have hmeasg : Measurable (fun z : Amb n ℓ => R⁻¹ • (z - 0)) := by fun_prop
    have hpre : ∀ (x : Amb n ℓ) (t : ℝ),
        (fun z : Amb n ℓ => R⁻¹ • (z - 0)) ⁻¹' closedBall x t = closedBall (R • x) (R * t) := by
      intro x t
      ext z
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero]
      rw [show R⁻¹ • z - x = R⁻¹ • (z - R • x) by rw [smul_sub, inv_smul_smul₀ hR0.ne'],
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, inv_mul_le_iff₀ hR0]
    have hball : ∀ (x : Amb n ℓ) (t : ℝ), V'.weight (closedBall x t) =
        (ENNReal.ofReal (R ^ n))⁻¹ * V.weight (closedBall (R • x) (R * t)) := by
      intro x t
      rw [hW, Measure.smul_apply, Measure.map_apply hmeasg measurableSet_closedBall, hpre,
        smul_eq_mul]
    have hballR : ∀ (x : Amb n ℓ) (t : ℝ), (V'.weight (closedBall x t)).toReal =
        (R ^ n)⁻¹ * (V.weight (closedBall (R • x) (R * t))).toReal := by
      intro x t
      rw [hball, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hRn.le]
    have hinvne : (ENNReal.ofReal (R ^ n))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hRn).ne'
    have hballfin : ∀ (x : Amb n ℓ) (t : ℝ), closedBall (R • x) (R * t) ⊆ closedBall 0 ρ →
        V'.weight (closedBall x t) ≠ ⊤ := by
      intro x t h
      rw [hball]
      exact ENNReal.mul_ne_top hinvne (hfin _ _ h)
    /- Hypotheses of 6.1 for `V'`. -/
    have hξ : ‖R⁻¹ • y‖ = 1 - θ₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, hyR, mul_comm (1 - θ₀) R,
        inv_mul_cancel_left₀ hR0.ne']
    have hU'open : IsOpen ((fun x => (0 : Amb n ℓ) + R • x) ⁻¹' U) :=
      hU.preimage (by fun_prop)
    have hB1 : closedBall (0 : Amb n ℓ) 1 ⊆ (fun x => (0 : Amb n ℓ) + R • x) ⁻¹' U := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      simp only [mem_preimage, zero_add]
      apply hBU
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
      calc R * ‖x‖ ≤ R * 1 := mul_le_mul_of_nonneg_left hx hR0.le
        _ ≤ ρ := (mul_one R).le.trans hRρ.le
    have hmass' : V'.weight (closedBall 0 1) ≤ ENNReal.ofReal (2 * ω) := by
      rw [ENNReal.le_ofReal_iff_toReal_le
        (hballfin 0 1 (by rw [smul_zero, mul_one]; exact closedBall_subset_closedBall hRρ.le))
        h2ω.le, hballR, smul_zero, mul_one, inv_mul_le_iff₀ hRn, mul_comm (R ^ n)]
      exact (hup R hR0 hRρ.le).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right c3 hω0.le) hRn.le)
    have hpinch : ∀ r ∈ Icc l 1,
        |(V'.weight (closedBall 0 1)).toReal / ω -
            (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n)| +
          r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
          l := by
      intro r hr
      have hr0 : 0 < r := hl0.trans_le hr.1
      have hRr : R * r ≤ ρ := (mul_le_of_le_one_right hR0.le hr.2).trans hRρ.le
      have hRl : R * l < ρ := (mul_lt_of_lt_one_right hR0 hl1).trans hRρ
      have e1 : (V'.weight (closedBall 0 1)).toReal / ω =
          (V.weight (closedBall 0 R)).toReal / (ω * R ^ n) := by
        rw [hballR, smul_zero, mul_one, inv_mul_eq_div, div_div, mul_comm (R ^ n) ω]
      have e2 : (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n) =
          (V.weight (closedBall 0 (R * l))).toReal / (ω * (R * l) ^ n) := by
        rw [hballR, smul_zero, mul_pow, inv_mul_eq_div, div_div, mul_left_comm (R ^ n) ω (l ^ n)]
      obtain ⟨a1, a2⟩ := hratio R hR0 hRρ
      obtain ⟨b1, b2⟩ := hratio (R * l) (mul_pos hR0 hl0) hRl
      have habs : |(V'.weight (closedBall 0 1)).toReal / ω -
          (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n)| ≤ Up δ - Lo δ := by
        rw [e1, e2, abs_le]
        constructor
        · linarith only [a1, b2]
        · linarith only [a2, b1]
      /- The curvature term, transported back to `V`. -/
      obtain ⟨hfinH, hbH⟩ := hHbound (R * r) (mul_pos hR0 hr0) hRr
      have hlint : ∫⁻ x in closedBall (0 : Amb n ℓ) r, ENNReal.ofReal ‖R • H (0 + R • x)‖
          ∂V'.weight ≤ (ENNReal.ofReal (R ^ n))⁻¹ *
            (ENNReal.ofReal R * ∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight) := by
        rw [hW, Measure.restrict_smul, lintegral_smul_measure,
          Measure.restrict_map hmeasg measurableSet_closedBall, hpre, smul_zero, smul_eq_mul]
        refine mul_le_mul' le_rfl ?_
        refine (lintegral_map_le _ hmeasg.aemeasurable).trans (le_of_eq ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        simp only [sub_zero, zero_add, smul_inv_smul₀ hR0.ne', ofReal_norm, enorm_smul,
          Real.enorm_eq_ofReal hR0.le]
      have hne : (ENNReal.ofReal (R ^ n))⁻¹ *
          (ENNReal.ofReal R * ∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight) ≠ ⊤ :=
        ENNReal.mul_ne_top hinvne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinH)
      have hint : ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
          (R ^ n)⁻¹ * (R * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal) := by
        have h1 := norm_integral_le_lintegral_norm (μ := V'.weight.restrict (closedBall 0 r))
          (fun x => ‖R • H (0 + R • x)‖)
        simp only [norm_norm] at h1
        refine (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ h1).trans ?_)
        have h2 := ENNReal.toReal_mono hne hlint
        rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal hRn.le, ENNReal.toReal_ofReal hR0.le] at h2
      have hscale : r ^ (1 - (n : ℝ)) *
          ((R ^ n)⁻¹ * (R * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal)) =
          (R * r) ^ (1 - (n : ℝ)) * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal := by
        rw [Real.mul_rpow hR0.le hr0.le, Real.rpow_sub hR0, Real.rpow_one, Real.rpow_natCast]
        ring
      have hHr : r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖
          ∂V'.weight ≤ KH * δ :=
        (mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg hr0.le _)).trans (hscale.trans_le hbH)
      calc _ ≤ (Up δ - Lo δ) + KH * δ := add_le_add habs hHr
        _ = l := (hlam δ).symm
    /- Theorem 6.1 with `λ = δ̃ = l`, `θ = θ₀`, `ξ = y/R`, `ρ = θ₀`, `τ = 2l`. -/
    obtain ⟨hconc, -⟩ := hC₉ l θ₀ l hl0 c4 hθ₀0 (hθ₀8.trans (by norm_num)) hl0 c4 (R⁻¹ • y) hξ _
      hU'open hB1 V' _ hH' hpinch hmass' θ₀ ⟨hθ₀0, le_rfl⟩ (2 * l)
      ⟨le_rfl, by linarith only [c4]⟩
    rw [← hqq δ] at hconc
    /- Back to `V`. -/
    have hRξ : R • (R⁻¹ • y) = y := smul_inv_smul₀ hR0.ne' y
    have hRτξ : R • ((2 * l) • (R⁻¹ • y)) = (2 * l) • y := by
      rw [smul_comm, smul_inv_smul₀ hR0.ne']
    have hτy : ‖(2 * l) • y‖ ≤ 2 * l * ρ := by
      rw [norm_smul, Real.norm_of_nonneg h2l.le]
      exact mul_le_mul_of_nonneg_left hyρ h2l.le
    have h2lρ : 2 * l * ρ ≤ 1 / 2 * ρ :=
      mul_le_mul_of_nonneg_right (by linarith only [c4]) hρ.le
    have hsub2 : closedBall ((2 * l) • y) (ρ / 2) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right]
      linarith only [hτy, h2lρ]
    have h2lθ : 0 < (2 * l) * θ₀ := mul_pos h2l hθ₀0
    have hs2 : 0 < R * ((2 * l) * θ₀) := mul_pos hR0 h2lθ
    have hs2le : R * ((2 * l) * θ₀) ≤ ρ / 2 := by
      have h1 : (2 * l) * θ₀ ≤ 1 / 2 := by
        calc (2 * l) * θ₀ ≤ 1 / 2 * 1 :=
              mul_le_mul (by linarith only [c4]) (by linarith only [hθ₀8]) hθ₀0.le (by norm_num)
          _ = 1 / 2 := mul_one _
      calc R * ((2 * l) * θ₀) ≤ ρ * (1 / 2) := mul_le_mul hRρ.le h1 h2lθ.le hρ.le
        _ = ρ / 2 := mul_one_div ρ 2
    have hconcR : (R ^ n)⁻¹ * (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal ≤
        ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ *
          (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal) +
        max C₉ 0 * (qq δ * |Real.log l|) := by
      have hfin2 : V'.weight (closedBall ((2 * l) • (R⁻¹ • y)) ((2 * l) * θ₀)) ≠ ⊤ := by
        apply hballfin
        rw [hRτξ]
        exact (closedBall_subset_closedBall hs2le).trans hsub2
      have hne : ENNReal.ofReal ((2 * l) ^ n)⁻¹ *
          V'.weight (closedBall ((2 * l) • (R⁻¹ • y)) ((2 * l) * θ₀)) +
          ENNReal.ofReal (C₉ * qq δ * |Real.log l|) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2,
          ENNReal.ofReal_ne_top⟩
      have h := ENNReal.toReal_mono hne hconc
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2) ENNReal.ofReal_ne_top,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos h2l n).le),
        ENNReal.toReal_ofReal', hballR, hballR, hRξ, hRτξ] at h
      have hql : 0 ≤ qq δ * |Real.log l| := mul_nonneg hq0 (abs_nonneg _)
      refine h.trans (add_le_add_right ?_ _)
      apply max_le
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hql
      · exact mul_nonneg (le_max_right _ _) hql
    /- The comparison ball `B_{2lθ₀R}(2l y)`. -/
    have hm3 : (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal / (ρ / 2) ^ n ≤
        Up δ * ω * (1 + 4 * l) ^ n := by
      have hsub3 : closedBall ((2 * l) • y) (ρ / 2) ⊆ closedBall 0 (ρ / 2 + 2 * l * ρ) := by
        apply closedBall_subset_closedBall'
        rw [dist_zero_right]
        exact add_le_add_right hτy _
      have hle : ρ / 2 + 2 * l * ρ ≤ ρ := by linarith only [h2lρ]
      have h1 : (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal ≤
          Up δ * ω * (ρ / 2 + 2 * l * ρ) ^ n :=
        (ENNReal.toReal_mono (hfin 0 _ (closedBall_subset_closedBall hle))
          (measure_mono hsub3)).trans
          (hup _ (add_pos (half_pos hρ) (mul_pos h2l hρ)) hle)
      rw [div_le_iff₀ (pow_pos (half_pos hρ) n)]
      calc (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal
          ≤ Up δ * ω * (ρ / 2 + 2 * l * ρ) ^ n := h1
        _ = Up δ * ω * (1 + 4 * l) ^ n * (ρ / 2) ^ n := by
            rw [show ρ / 2 + 2 * l * ρ = (1 + 4 * l) * (ρ / 2) by ring, mul_pow,
              ← mul_assoc (Up δ * ω)]
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ea δ * (Up δ * ω * (1 + 4 * l) ^ n) + eb δ := ⟨_, rfl⟩
    have hm2 : (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal ≤
        (R * ((2 * l) * θ₀)) ^ n * X := by
      have h1 := M1' ((2 * l) • y) (ρ / 2) (R * ((2 * l) * θ₀)) hs2 hs2le hsub2
      have h2 : (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal /
          (R * ((2 * l) * θ₀)) ^ n ≤ X := by
        rw [hX]
        exact h1.trans (add_le_add_left (mul_le_mul_of_nonneg_left hm3 hea0) _)
      rw [div_le_iff₀ (pow_pos hs2 n)] at h2
      exact h2.trans_eq (mul_comm _ _)
    have hm1 : (R ^ n)⁻¹ * (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal ≤
        θ₀ ^ n * X + max C₉ 0 * (qq δ * |Real.log l|) := by
      refine hconcR.trans (add_le_add_left ?_ _)
      calc ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ *
            (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal)
          ≤ ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ * ((R * ((2 * l) * θ₀)) ^ n * X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 (inv_nonneg.mpr hRn.le))
              (inv_nonneg.mpr (pow_pos h2l n).le)
        _ = θ₀ ^ n * X := by
            rw [mul_pow R, mul_pow (2 * l) θ₀, mul_assoc (R ^ n),
              inv_mul_cancel_left₀ hRn.ne', mul_assoc ((2 * l) ^ n),
              inv_mul_cancel_left₀ (pow_pos h2l n).ne']
    /- Pinching at `y` on the scale `r_y = (1 - δ̃^{1/4}) θ₀ R`. -/
    have hq2 : 0 < 1 - qq δ := by linarith only [c5]
    have hry : 0 < R * ((1 - qq δ) * θ₀) := mul_pos hR0 (mul_pos hq2 hθ₀0)
    have hθn : 0 < θ₀ ^ n := pow_pos hθ₀0 n
    have hm1' : (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal /
        (R * ((1 - qq δ) * θ₀)) ^ n ≤
        ((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n) := by
      rw [mul_pow R, mul_pow (1 - qq δ) θ₀, ← div_div, div_eq_inv_mul _ (R ^ n),
        div_mul_eq_div_div_swap]
      calc (R ^ n)⁻¹ * (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal / θ₀ ^ n /
            (1 - qq δ) ^ n
          ≤ (θ₀ ^ n * X + max C₉ 0 * (qq δ * |Real.log l|)) / θ₀ ^ n / (1 - qq δ) ^ n :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hm1 hθn.le)
              (pow_pos hq2 n).le
        _ = ((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n) := by
            rw [add_div, mul_div_cancel_left₀ _ hθn.ne', div_eq_inv_mul _ ((1 - qq δ) ^ n)]
    have hsuby : closedBall y (R * ((1 - qq δ) * θ₀)) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right, hyR]
      have h1 : R * ((1 - qq δ) * θ₀) ≤ R * θ₀ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hθ₀0.le (sub_le_self 1 hq0)) hR0.le
      linarith only [h1, hRρ]
    have hcsry : cs * ρ ≤ R * ((1 - qq δ) * θ₀) := by
      rw [hcs]
      have h1 : κ₀ * ρ * θ₀ ≤ R * θ₀ := mul_le_mul_of_nonneg_right hκR.le hθ₀0.le
      have h2 : R * θ₀ * (1 / 2) ≤ R * θ₀ * (1 - qq δ) :=
        mul_le_mul_of_nonneg_left (by linarith only [c5]) (mul_pos hR0 hθ₀0).le
      linarith only [h1, h2]
    have hfinal := M1' y (R * ((1 - qq δ) * θ₀)) (cs * ρ) hcsρ hcsry hsuby
    calc (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n
        ≤ ea δ * ((V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal /
            (R * ((1 - qq δ) * θ₀)) ^ n) + eb δ := hfinal
      _ ≤ ea δ * (((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n)) +
            eb δ := add_le_add_left (mul_le_mul_of_nonneg_left hm1' hea0) _
      _ ≤ (1 + ε) * ω := by rw [hX]; exact c7

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
