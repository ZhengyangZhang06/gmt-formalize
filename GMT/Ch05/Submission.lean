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
import Poincare.SimonGMT.Chapter02.WeightedArea

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

/-- **Blow-ups of a set of zero `n`-density vanish** (Simon Ch. 3, proof of Theorem 1.6 "⇒").
If `Hⁿ(A) < ∞` and `ρ⁻ⁿ Hⁿ(A ∩ B_ρ(x)) → 0` as `ρ ↓ 0`, then `∫_{η_{x,r}(A)} f dHⁿ → 0` as
`r ↓ 0` for every `f ∈ C_c(ℝ^{n+ℓ}, ℝ)`: if `|f| ≤ M` and `spt f ⊆ B_R(0)`, then
`|∫_{η_{x,r}(A)} f dHⁿ| ≤ M r⁻ⁿ Hⁿ(A ∩ B_{rR}(x)) = M Rⁿ (rR)⁻ⁿ Hⁿ(A ∩ B_{rR}(x))`. -/
theorem rsod_blowUp_integral_tendsto_zero : ∀ (n ℓ : ℕ) (x : Amb n ℓ) (A : Set (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (A ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ x A hA hD f
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  -- `|f| ≤ M` everywhere, and `f = 0` off `B_R(0)` for some `R > 0`.
  obtain ⟨M, hM⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  obtain ⟨R, hR, hR₀R⟩ : ∃ R : ℝ, 0 < R ∧ R₀ ≤ R :=
    ⟨max R₀ 1, zero_lt_one.trans_le (le_max_right _ _), le_max_left _ _⟩
  have hfR : ∀ y, R < ‖y‖ → f y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport fun h => by
    have := mem_closedBall_zero_iff.mp (hR₀ h)
    linarith
  -- For `r > 0`, by the change of variables `η = η_{x,r}` and since `f ∘ η = 0` off `B_{rR}(x)`:
  -- `|∫_{η(A)} f| = r⁻ⁿ |∫_{A ∩ B_{rR}(x)} f ∘ η| ≤ M Rⁿ (rR)⁻ⁿ Hⁿ(A ∩ B_{rR}(x))`.
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μ‖ ≤
        M * R ^ n * (((r * R) ^ n)⁻¹ * μ.real (A ∩ closedBall x (r * R))) := by
    intro r hr
    set η := Poincare.SimonGMT.Chapter03.blowUpMap x r
    have hcv : ∫ y in η '' A, f y ∂μ = (r ^ n)⁻¹ * ∫ z in A, f (η z) ∂μ := by
      simpa only [mul_one] using rsod_blowUp_setIntegral_eq n ℓ A f (fun _ => 1) x r hr
    have hloc : ∫ z in A, f (η z) ∂μ = ∫ z in A ∩ closedBall x (r * R), f (η z) ∂μ := by
      rw [← setIntegral_indicator measurableSet_closedBall]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show f (η z) = (closedBall x (r * R)).indicator (fun z => f (η z)) z
      by_cases hz : z ∈ closedBall x (r * R)
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz]
        rw [mem_closedBall, not_le] at hz
        refine hfR _ ?_
        show R < ‖r⁻¹ • (z - x)‖
        rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), lt_inv_mul_iff₀ hr,
          ← dist_eq_norm]
    have hfin : μ (A ∩ closedBall x (r * R)) < ∞ := (measure_mono inter_subset_left).trans_lt hA
    rw [hcv, hloc, norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hr.le]
    calc (r ^ n)⁻¹ * ‖∫ z in A ∩ closedBall x (r * R), f (η z) ∂μ‖
        ≤ (r ^ n)⁻¹ * (M * μ.real (A ∩ closedBall x (r * R))) := by
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin fun z _ => hM _
      _ = M * R ^ n * (((r * R) ^ n)⁻¹ * μ.real (A ∩ closedBall x (r * R))) := by
          have hRn : R ^ n ≠ 0 := pow_ne_zero n hR.ne'
          rw [mul_pow, mul_inv]
          field_simp
  -- `r ↦ rR` maps `𝓝[>] 0` into itself, so the bound tends to `M Rⁿ · 0 = 0`.
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hr hR
  have htend := (hD.comp hmap).const_mul (M * R ^ n)
  rw [mul_zero] at htend
  refine squeeze_zero_norm' ?_ htend
  filter_upwards [self_mem_nhdsWithin] with r hr using hbound r hr
/-- **Transfer of approximate tangent spaces** (Simon Ch. 3, proof of Theorem 1.6 "⇒" and
Remark 1.5(2)).  Let `D ⊆ C ∩ N` be Borel with `Hⁿ(C), Hⁿ(N) < ∞`, and let `C \ D` and `N \ D`
have zero `n`-density at `x`.  If `T_x N = P`, then `T_x C = P`: for `η = η_{x,r}` with `r > 0`
and `f ∈ C_c`, splitting `C` and `N` along `D` before the change of variables gives
`∫_{η(C)} f = ∫_{η(N)} f − ∫_{η(N \ D)} f + ∫_{η(C \ D)} f`, and the last two terms tend to `0`. -/
theorem rsod_approxTangent_transfer : ∀ (n ℓ : ℕ) (C N D : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), MeasurableSet D → D ⊆ C → D ⊆ N → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → (μHE[n] : Measure (Amb n ℓ)) N < ∞ → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real ((C \ D) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real ((N \ D) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P := by
  intro n ℓ C N D x P hD hDC hDN hC hN hCD hND hT
  -- Step 1: `finrank P = n` is inherited from `T_x N = P`; fix a test function `f ∈ C_c`.
  refine ⟨hT.1, fun f => ?_⟩
  -- Step 2: `∫_{η(N)} f → ∫_P f`, while `∫_{η(N \ D)} f → 0` and `∫_{η(C \ D)} f → 0`.
  have hlim := ((hT.2 f).sub (Submission.rsod_blowUp_integral_tendsto_zero n ℓ x (N \ D)
      ((measure_mono sdiff_subset).trans_lt hN) hND f)).add
    (Submission.rsod_blowUp_integral_tendsto_zero n ℓ x (C \ D)
      ((measure_mono sdiff_subset).trans_lt hC) hCD f)
  rw [sub_zero, add_zero] at hlim
  -- Step 3: it suffices to prove `(∗)` `∫_{η(C)} f = ∫_{η(N)} f − ∫_{η(N \ D)} f + ∫_{η(C \ D)} f`
  -- for every `r > 0`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set g : Amb n ℓ → ℝ := fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
  -- Step 4: change of variables with `θ ≡ 1`: `∫_{η(S)} f = r⁻ⁿ ∫_S f ∘ η`.
  have hCV : ∀ S : Set (Amb n ℓ), ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂μ =
      (r ^ n)⁻¹ * ∫ z in S, g z ∂μ := fun S => by
    simpa only [mul_one] using
      Submission.rsod_blowUp_setIntegral_eq n ℓ S f (fun _ => 1) x r hr
  -- Step 5: `g = f ∘ η` is continuous and bounded, hence integrable on sets of finite measure.
  obtain ⟨B, hB⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hg : Continuous g := f.continuous.comp (by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop)
  have hint : ∀ S : Set (Amb n ℓ), μ S < ∞ → IntegrableOn g S μ := fun S hS =>
    Measure.integrableOn_of_bounded hS.ne hg.aestronglyMeasurable (ae_of_all _ fun z => hB _)
  -- Step 6: `∫_S g = ∫_{S \ D} g + ∫_D g` whenever `D ⊆ S` and `Hⁿ(S) < ∞`.
  have hsplit : ∀ S : Set (Amb n ℓ), D ⊆ S → μ S < ∞ →
      ∫ z in S, g z ∂μ = ∫ z in S \ D, g z ∂μ + ∫ z in D, g z ∂μ := fun S hDS hS => by
    conv_lhs => rw [← sdiff_union_of_subset hDS]
    exact setIntegral_union disjoint_sdiff_left hD
      (hint _ ((measure_mono sdiff_subset).trans_lt hS)) (hint _ ((measure_mono hDS).trans_lt hS))
  -- Step 7: the identity `(∗)`.
  rw [hCV C, hCV N, hCV (N \ D), hCV (C \ D), hsplit C hDC hC, hsplit N hDN hN]
  ring
/-- **Scaling of `Hⁿ` under the blow-up map** `η_{x,r}(y) = r⁻¹(y − x)` (`Chapter03.blowUpMap`;
Simon, Ch. 3, 1.4 and the proof of 1.9): for `r > 0` and **every** set `B ⊆ ℝ^{n+ℓ}` (no
measurability needed), (i) `rⁿ Hⁿ(η_{x,r}(B)) = Hⁿ(B)` and
(ii) `η_{x,r#}(Hⁿ ⌞ B) = rⁿ Hⁿ ⌞ η_{x,r}(B)`.
(1) `η_{x,r}(S) = τ(r⁻¹S)` for the translation `τ(z) = z − r⁻¹x`, an isometry, so
`Hⁿ(η_{x,r}(S)) = Hⁿ(r⁻¹S) = ‖r⁻¹‖ⁿ Hⁿ(S)` for every set `S`; since `rⁿ ‖r⁻¹‖ⁿ = 1`, this is (i).
(2) `η_{x,r}` is continuous, hence Borel, and `T ∩ η_{x,r}(B) = η_{x,r}(η_{x,r}⁻¹(T) ∩ B)`, so
by (1) both measures in (ii) give every Borel set `T` the value `Hⁿ(η_{x,r}⁻¹(T) ∩ B)`. -/
theorem rsod_blowUpMap_measure_scaling : ∀ (n ℓ : ℕ) (x : Amb n ℓ) (r : ℝ), 0 < r → ∀ B : Set (Amb n ℓ), ENNReal.ofReal (r ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B) = (μHE[n] : Measure (Amb n ℓ)) B ∧ ((μHE[n] : Measure (Amb n ℓ)).restrict B).map (Poincare.SimonGMT.Chapter03.blowUpMap x r) = ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Amb n ℓ)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B) := by
  intro n ℓ x r hr B
  -- Step (1), for every set `S`.
  have hscale : ∀ S : Set (Amb n ℓ), ENNReal.ofReal (r ^ n) *
      (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
      (μHE[n] : Measure (Amb n ℓ)) S := by
    intro S
    -- `η_{x,r}(S) = τ(r⁻¹S)` with `τ(z) = z + (−r⁻¹x)`.
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => z + -(r⁻¹ • x)) '' ((fun z => r⁻¹ • z) '' S) := by
      rw [Set.image_image]
      exact Set.image_congr fun y _ => by
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg, smul_add, smul_neg]
    -- `Hⁿ(r⁻¹S) = ‖r⁻¹‖₊ⁿ Hⁿ(S)`.
    have hsmul := Measure.euclideanHausdorffMeasure_smul₀ (E := Amb n ℓ) n (inv_ne_zero hr.ne') S
    -- `ofReal (rⁿ) · ‖r⁻¹‖₊ⁿ = ofReal ((r r⁻¹)ⁿ) = 1`.
    have hc : ENNReal.ofReal (r ^ n) * ((‖r⁻¹‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, ← ENNReal.ofReal_mul (pow_nonneg hr.le n), ← mul_pow,
        mul_inv_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one]
    rw [himage, (isometry_add_right _).euclideanHausdorffMeasure_image, Set.image_smul, hsmul,
      ENNReal.smul_def, smul_eq_mul, ← mul_assoc, hc, one_mul]
  refine ⟨hscale B, ?_⟩
  -- Step (2): both measures agree on Borel sets `T`.
  have hmeas : Measurable (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  ext T hT
  rw [Measure.map_apply hmeas hT, Measure.restrict_apply (hmeas hT), Measure.smul_apply,
    Measure.restrict_apply hT, smul_eq_mul, Set.inter_comm T, ← Set.image_inter_preimage,
    hscale, Set.inter_comm]
/-- **Upper Density Theorem** (Simon, *Introduction to GMT*, Ch. 1, Theorem 3.6), in the
`μHE[n]`-a.e. limit form used for the a.e. existence of approximate tangent spaces (Ch. 3, 1.9):
if `A` is a Borel set with `ν(A) < ∞`, then `ρ⁻ⁿ ν(A ∩ B_ρ(x)) → 0` as `ρ ↓ 0` for `Hⁿ`-a.e.
`x ∉ A`.  Proof as in Simon 3.3–3.6, with the crude constant `10ⁿ` in place of `1`:
(1) (3.3, via the 5-times covering lemma 3.4) If `μ(B_ρ(x)) > t ρⁿ` for arbitrarily small
`ρ > 0` at every `x ∈ C`, then `μH[n](C) ≤ (10ⁿ/t) μ(ℝ^{n+ℓ})`: for each `k`, Vitali's lemma
applied to these balls of radius `< 1/(k+1)` gives disjoint (hence countably many) balls
`B_{r_b}(x_b)` whose 5-fold enlargements cover `C`, and
`Σ_b diam(B_{5r_b}(x_b))ⁿ ≤ Σ_b (10 r_b)ⁿ ≤ (10ⁿ/t) Σ_b μ(B_{r_b}(x_b)) ≤ (10ⁿ/t) μ(ℝ^{n+ℓ})`.
(2) (3.6) Given `t, η > 0`, choose a closed `K ⊆ A` with `ν(A \ K) < η` (1.15(2)).  Small balls
about `x ∉ A` miss `K`, so there `ν(A ∩ B_ρ(x)) = ν⌞(A \ K)(B_ρ(x))`, and (1) bounds the
`μH[n]`-measure of `{x ∉ A : ν(A ∩ B_ρ(x)) > t ρⁿ for arbitrarily small ρ}` by `(10ⁿ/t) η`.
(3) Taking `t = 1/(j+1)`, the union of these sets is `μH[n]`-null, hence `μHE[n]`-null (a constant
multiple), and off it `0 ≤ ρ⁻ⁿ ν(A ∩ B_ρ(x)) ≤ 1/(j+1)` for small `ρ > 0`, for every `j`. -/
theorem rsod_ae_tendsto_density_zero_outside : ∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), MeasurableSet A → ν A < ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∉ A → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * ν.real (A ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν A hA hνA
  -- `diam B_{5r}(c) ≤ 10 r`.
  have hdiam : ∀ (c : Amb n ℓ) (r : ℝ),
      ediam (closedBall c (5 * r)) ≤ ENNReal.ofReal (10 * r) := by
    intro c r
    refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
    have hy' := mem_closedBall.1 hy
    have hz' := mem_closedBall.1 hz
    linarith [dist_triangle_right y z c]
  -- Step 1 (Simon 3.3 via the 5-times covering lemma 3.4, constant `10ⁿ`).
  have hcov : ∀ (μ : Measure (Amb n ℓ)) (t : ℝ), 0 < t → ∀ C : Set (Amb n ℓ),
      (∀ x ∈ C, ∀ δ : ℝ, 0 < δ → ∃ ρ, 0 < ρ ∧ ρ < δ ∧
        ENNReal.ofReal (t * ρ ^ n) < μ (closedBall x ρ)) →
      μH[(n : ℝ)] C ≤ ENNReal.ofReal (10 ^ n / t) * μ univ := by
    intro μ t ht C hC
    -- A selected ball `B_r(c)` with `μ(B_r(c)) > t rⁿ` has
    -- `diam(B_{5r}(c))ⁿ ≤ (10 r)ⁿ = (10ⁿ/t) · t rⁿ ≤ (10ⁿ/t) μ(B_r(c))`.
    have hterm : ∀ (c : Amb n ℓ) (r : ℝ), 0 < r →
        ENNReal.ofReal (t * r ^ n) < μ (closedBall c r) →
        ediam (closedBall c (5 * r)) ^ (n : ℝ) ≤
          ENNReal.ofReal (10 ^ n / t) * μ (closedBall c r) := by
      intro c r hr hrμ
      calc ediam (closedBall c (5 * r)) ^ (n : ℝ) ≤ ENNReal.ofReal (10 * r) ^ (n : ℝ) :=
            ENNReal.rpow_le_rpow (hdiam c r) (Nat.cast_nonneg n)
        _ = ENNReal.ofReal (10 ^ n / t) * ENNReal.ofReal (t * r ^ n) := by
            rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (p := 10 * r) (by positivity),
              ← ENNReal.ofReal_mul (p := 10 ^ n / t) (by positivity), mul_pow]
            congr 1
            field_simp
        _ ≤ ENNReal.ofReal (10 ^ n / t) * μ (closedBall c r) :=
            mul_le_mul_of_nonneg_left hrμ.le zero_le
    -- For each `k`, a disjoint Vitali subfamily of radii `< 1/(k+1)` whose 5-fold enlargements
    -- cover `C`; it is countable since the balls have nonempty interiors.
    have hV : ∀ k : ℕ, ∃ u : Set (Amb n ℓ × ℝ), u.Countable ∧
        (∀ b ∈ u, 0 < b.2 ∧ b.2 < 1 / ((k : ℝ) + 1) ∧
          ENNReal.ofReal (t * b.2 ^ n) < μ (closedBall b.1 b.2)) ∧
        u.PairwiseDisjoint (fun b => closedBall b.1 b.2) ∧
        C ⊆ ⋃ b : u, closedBall b.1.1 (5 * b.1.2) := by
      intro k
      obtain ⟨u, huT, hdisj, hcover⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
          {b : Amb n ℓ × ℝ | 0 < b.2 ∧ b.2 < 1 / ((k : ℝ) + 1) ∧
            ENNReal.ofReal (t * b.2 ^ n) < μ (closedBall b.1 b.2)}
          Prod.fst Prod.snd (1 / ((k : ℝ) + 1)) (fun b hb => hb.2.1.le) 5 (by norm_num)
      refine ⟨u, hdisj.countable_of_nonempty_interior fun b hb => ⟨b.1, ?_⟩,
        fun b hb => huT hb, hdisj, fun x hx => ?_⟩
      · exact mem_interior_iff_mem_nhds.2 (closedBall_mem_nhds _ (huT hb).1)
      · obtain ⟨ρ, hρ, hρk, hρμ⟩ := hC x hx (1 / ((k : ℝ) + 1)) (by positivity)
        obtain ⟨b, hbu, hb⟩ := hcover (x, ρ) ⟨hρ, hρk, hρμ⟩
        exact mem_iUnion.2 ⟨⟨b, hbu⟩, hb (mem_closedBall_self hρ.le)⟩
    choose u hu_count hu_mem hu_disj hu_cov using hV
    have : ∀ k, Countable (u k) := fun k => (hu_count k).to_subtype
    calc μH[(n : ℝ)] C
        ≤ liminf (fun k => ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)) atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) C
            (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) ?_
            (fun k (b : u k) => closedBall b.1.1 (5 * b.1.2)) ?_ (Eventually.of_forall hu_cov)
          · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10
            rw [mul_zero] at h
            rw [← ENNReal.ofReal_zero]
            exact ENNReal.tendsto_ofReal h
          · refine Eventually.of_forall fun k b => (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
            have hb := (hu_mem k b b.2).2.1
            linarith
      _ ≤ ENNReal.ofReal (10 ^ n / t) * μ univ := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          calc ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)
              ≤ ∑' b : u k, ENNReal.ofReal (10 ^ n / t) * μ (closedBall b.1.1 b.1.2) :=
                ENNReal.tsum_le_tsum fun b => hterm _ _ (hu_mem k b b.2).1 (hu_mem k b b.2).2.2
            _ = ENNReal.ofReal (10 ^ n / t) * μ (⋃ b ∈ u k, closedBall b.1 b.2) := by
                rw [ENNReal.tsum_mul_left, measure_biUnion (hu_count k) (hu_disj k)
                  fun b _ => measurableSet_closedBall]
            _ ≤ ENNReal.ofReal (10 ^ n / t) * μ univ :=
                mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) zero_le
  -- Step 2 (Simon 3.6): for each `t > 0` the set of `x ∉ A` with upper density `≥ t` is null.
  have hnull : ∀ t : ℝ, 0 < t → μH[(n : ℝ)] {x | x ∉ A ∧ ∀ δ : ℝ, 0 < δ → ∃ ρ, 0 < ρ ∧ ρ < δ ∧
      ENNReal.ofReal (t * ρ ^ n) < ν (A ∩ closedBall x ρ)} = 0 := by
    intro t ht
    set S : Set (Amb n ℓ) := {x | x ∉ A ∧ ∀ δ : ℝ, 0 < δ → ∃ ρ, 0 < ρ ∧ ρ < δ ∧
      ENNReal.ofReal (t * ρ ^ n) < ν (A ∩ closedBall x ρ)}
    by_contra hne
    obtain ⟨η, hη, hηlt⟩ := ENNReal.exists_nnreal_pos_mul_lt ENNReal.ofReal_ne_top hne
    have : IsFiniteMeasure (ν.restrict A) := isFiniteMeasure_restrict.2 hνA.ne
    obtain ⟨K, hKA, hK, hAK⟩ := hA.exists_isClosed_sdiff_lt (μ := ν.restrict A)
      (measure_ne_top _ _) (ε := (η : ℝ≥0∞)) (ENNReal.coe_ne_zero.2 hη.ne')
    rw [Measure.restrict_apply' hA, inter_eq_left.2 sdiff_subset] at hAK
    have hle := hcov (ν.restrict (A \ K)) t ht S fun x hx δ hδ => by
      obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK.isOpen_compl x fun hxK => hx.1 (hKA hxK)
      obtain ⟨ρ, hρ, hρδ, hρν⟩ := hx.2 (min δ ε) (lt_min hδ hε)
      refine ⟨ρ, hρ, hρδ.trans_le (min_le_left _ _), ?_⟩
      have hsub : closedBall x ρ ⊆ Kᶜ :=
        (closedBall_subset_ball (hρδ.trans_le (min_le_right _ _))).trans hεK
      have hset : closedBall x ρ ∩ (A \ K) = A ∩ closedBall x ρ := by
        ext y
        constructor
        · rintro ⟨hy1, hy2, -⟩
          exact ⟨hy2, hy1⟩
        · rintro ⟨hy1, hy2⟩
          exact ⟨hy2, hy1, hsub hy2⟩
      rw [Measure.restrict_apply measurableSet_closedBall, hset]
      exact hρν
    rw [Measure.restrict_apply_univ] at hle
    have hlt := calc μH[(n : ℝ)] S ≤ ENNReal.ofReal (10 ^ n / t) * ν (A \ K) := hle
      _ ≤ ENNReal.ofReal (10 ^ n / t) * η := mul_le_mul_of_nonneg_left hAK.le zero_le
      _ = η * ENNReal.ofReal (10 ^ n / t) := mul_comm _ _
      _ < μH[(n : ℝ)] S := hηlt
    exact lt_irrefl _ hlt
  -- Step 3: union over `t = 1/(j+1)`; `μHE[n]` is a constant multiple of `μH[n]`.
  have hbad : (μHE[n] : Measure (Amb n ℓ)) (⋃ j : ℕ, {x | x ∉ A ∧ ∀ δ : ℝ, 0 < δ → ∃ ρ, 0 < ρ ∧
      ρ < δ ∧ ENNReal.ofReal (1 / ((j : ℝ) + 1) * ρ ^ n) < ν (A ∩ closedBall x ρ)}) = 0 := by
    have h0 : μH[(n : ℝ)] (⋃ j : ℕ, {x | x ∉ A ∧ ∀ δ : ℝ, 0 < δ → ∃ ρ, 0 < ρ ∧
        ρ < δ ∧ ENNReal.ofReal (1 / ((j : ℝ) + 1) * ρ ^ n) < ν (A ∩ closedBall x ρ)}) = 0 :=
      measure_iUnion_null fun j => hnull _ (by positivity)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h0, smul_zero]
  refine (measure_eq_zero_iff_ae_notMem.1 hbad).mono fun x hx hxA => ?_
  simp only [mem_iUnion, mem_ofPred_eq] at hx
  push Not at hx
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact ha.trans_le
      (mul_nonneg (inv_nonneg.2 (pow_nonneg (mem_Ioi.1 hρ).le n)) measureReal_nonneg)
  · obtain ⟨j, hj⟩ := exists_nat_one_div_lt ha
    obtain ⟨δ, hδ, hδν⟩ := hx j hxA
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    have hρn : 0 < ρ ^ n := pow_pos hρ.1 n
    have h1 : ν.real (A ∩ closedBall x ρ) ≤ 1 / ((j : ℝ) + 1) * ρ ^ n :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by positivity) hρn.le) (hδν ρ hρ.1 hρ.2)
    calc (ρ ^ n)⁻¹ * ν.real (A ∩ closedBall x ρ)
        ≤ (ρ ^ n)⁻¹ * (1 / ((j : ℝ) + 1) * ρ ^ n) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hρn.le)
      _ = 1 / ((j : ℝ) + 1) := by rw [mul_left_comm, inv_mul_cancel₀ hρn.ne', mul_one]
      _ < a := hj
/-- **Embedded `C¹` submanifolds are Borel** (step 4 of the a.e. approximate-tangent argument
behind Simon Ch. 5, Corollary 7.3; cf. Ch. 3, 1.9).  If `S ⊆ ℝ^N` is an `m`-dimensional `C¹`
submanifold (`IsC1Submanifold`), then `S` is a Borel set.
Proof: let `(V, W, φ)` be a chart at `y ∈ S` and `z ∈ W ∩ closure S`.  For a closed ball
`K = B_{ε/2}(z) ⊆ W`, properness makes `φ(V ∩ φ⁻¹(K)) = W ∩ S ∩ K` compact, hence closed, and
`z ∈ closure (W ∩ S ∩ K)`, so `z ∈ S`.  Thus `W ∩ closure S ⊆ S`, whence `S = O ∩ closure S` with
`O = ⋃_{y ∈ S} W_y` open, and the intersection of an open and a closed set is Borel. -/
theorem rsod_isC1Submanifold_measurableSet : ∀ (m N : ℕ) (S : Set (EuclideanSpace ℝ (Fin N))), IsC1Submanifold m S → MeasurableSet S := by
  intro m N S hS
  -- Steps 1–3: each `y ∈ S` has an open `W ∋ y` with `W ∩ closure S ⊆ S`.
  have hloc : ∀ y ∈ S, ∃ W : Set (EuclideanSpace ℝ (Fin N)),
      IsOpen W ∧ y ∈ W ∧ W ∩ closure S ⊆ S := by
    intro y hy
    obtain ⟨V, W, φ, -, hW, hyW, hφ, -, himg, hprop, -⟩ := hS y hy
    refine ⟨W, hW, hyW, ?_⟩
    rintro z ⟨hzW, hzcl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW z hzW
    -- `K = B_{ε/2}(z)` is a compact subset of `W`, so `Q = V ∩ φ⁻¹(K)` is compact.
    have hKW : closedBall z (ε / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hball
    have hQ : IsCompact (V ∩ φ ⁻¹' closedBall z (ε / 2)) :=
      hprop _ (isCompact_closedBall z (ε / 2)) hKW
    -- `φ(Q) = φ(V) ∩ K = W ∩ S ∩ K` is compact, hence closed.
    have hφQ : IsCompact (φ '' (V ∩ φ ⁻¹' closedBall z (ε / 2))) :=
      hQ.image_of_continuousOn (hφ.continuousOn.mono inter_subset_left)
    rw [image_inter_preimage, himg] at hφQ
    -- `z ∈ closure (W ∩ S ∩ K)`: points of `S` in `B̆_{ε/2}(z)` lie in `W ∩ S ∩ K`.
    have hz : z ∈ closure (W ∩ S ∩ closedBall z (ε / 2)) := by
      refine closure_mono ?_ (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hε), hzcl⟩)
      rintro w ⟨hw, hwS⟩
      exact ⟨⟨hball (ball_subset_ball (by linarith) hw), hwS⟩, ball_subset_closedBall hw⟩
    rw [hφQ.isClosed.closure_eq] at hz
    exact hz.1.2
  -- Step 4: `S = O ∩ closure S` with `O = ⋃_{y ∈ S} W_y`.
  choose! W hWo hyW hWS using hloc
  have hSO : S = (⋃ y ∈ S, W y) ∩ closure S := by
    refine Subset.antisymm (fun z hz => ⟨mem_biUnion hz (hyW z hz), subset_closure hz⟩) ?_
    rintro z ⟨hzO, hzcl⟩
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hzO
    exact hWS y hy ⟨hzy, hzcl⟩
  -- Step 5: `O` is open and `closure S` is closed, so `S = O ∩ closure S` is Borel.
  rw [hSO]
  exact (isOpen_biUnion hWo).measurableSet.inter isClosed_closure.measurableSet
/-- Linear lower bound for a `C¹` chart near a point where its derivative is injective (used for
the `C¹` submanifold charts of Simon Ch. 2 §4).  If `V ⊆ ℝᵐ` is open, `φ` is `C¹` on `V`, `v₀ ∈ V`
and `Dφ(v₀)` is injective, then there are `c, δ > 0` with `B_δ(v₀) ⊆ V` and
`c ‖w‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖` whenever `‖w‖ ≤ δ`.  With `L = Dφ(v₀)` and `‖u‖ ≤ K ‖L u‖`, take
`c = 1/(2K)` and `δ` so small that `‖Dφ(v) − L‖ ≤ c` on `B_δ(v₀) ⊆ V`; the mean value inequality
gives `‖φ(v₀ + w) − φ(v₀) − L w‖ ≤ c ‖w‖`, and `2c ‖w‖ ≤ ‖L w‖` finishes. -/
theorem rsod_c1tan_chart_lower_bound : ∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m), IsOpen V → ContDiffOn ℝ 1 φ V → v₀ ∈ V → Function.Injective (fderiv ℝ φ v₀) → ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ closedBall v₀ δ ⊆ V ∧ ∀ w : Rn m, ‖w‖ ≤ δ → c * ‖w‖ ≤ ‖φ (v₀ + w) - φ v₀‖ := by
  intro m N V φ v₀ hV hφ hv₀ hinj
  set L := fderiv ℝ φ v₀ with hL
  -- Step 1: `‖u‖ ≤ K ‖L u‖` for some `K > 0`; put `c = 1/(2K)`, so `c K = 1/2`.
  obtain ⟨K, hK0, hK⟩ := (L : Rn m →ₗ[ℝ] EuclideanSpace ℝ (Fin N)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hinj)
  have hK0' : (0 : ℝ) < K := hK0
  have hLlow : ∀ u : Rn m, ‖u‖ ≤ K * ‖L u‖ := fun u => hK.le_mul_norm (map_zero _) u
  set c : ℝ := 1 / (2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hcK : c * K = 1 / 2 := by
    rw [hc]
    field_simp
  -- Step 2: `Dφ` is continuous at `v₀`; choose `δ < δ₁, δ₂` with `‖Dφ(v) − L‖ < c` for
  -- `dist(v, v₀) < δ₁` and `B̆_{δ₂}(v₀) ⊆ V`.
  have hcont : ContinuousAt (fderiv ℝ φ) v₀ :=
    (hφ.continuousOn_fderiv_of_isOpen hV le_rfl).continuousAt (hV.mem_nhds hv₀)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hcont c hc0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.mp hV v₀ hv₀
  set δ : ℝ := min δ₁ δ₂ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδlt₁ : δ < δ₁ := by
    have := min_le_left δ₁ δ₂
    rw [hδ]
    linarith
  have hδlt₂ : δ < δ₂ := by
    have := min_le_right δ₁ δ₂
    rw [hδ]
    linarith
  have hball : closedBall v₀ δ ⊆ V := (closedBall_subset_ball hδlt₂).trans hδ₂'
  refine ⟨c, hc0, δ, hδ0, hball, fun w hw => ?_⟩
  -- Step 3: on `B_δ(v₀)`, `φ` is differentiable and `‖Dφ(v) − L‖ ≤ c`.
  have hdiff : ∀ v ∈ closedBall v₀ δ, DifferentiableAt ℝ φ v := fun v hv =>
    (hφ.differentiableOn one_ne_zero v (hball hv)).differentiableAt (hV.mem_nhds (hball hv))
  have hbound : ∀ v ∈ closedBall v₀ δ, ‖fderiv ℝ φ v - L‖ ≤ c := fun v hv => by
    have h := hδ₁' (lt_of_le_of_lt (mem_closedBall.mp hv) hδlt₁)
    rw [dist_eq_norm] at h
    exact h.le
  -- Step 4: mean value inequality on the convex ball: `‖φ(v₀ + w) − φ(v₀) − L w‖ ≤ c ‖w‖`.
  have hmem : v₀ + w ∈ closedBall v₀ δ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hw
  have hmvt := (convex_closedBall v₀ δ).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound
    (mem_closedBall_self hδ0.le) hmem
  rw [add_sub_cancel_left] at hmvt
  -- Step 5: `2c ‖w‖ ≤ ‖L w‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖ + c ‖w‖`.
  have h1 : c * ‖w‖ ≤ ‖L w‖ / 2 := by
    calc c * ‖w‖ ≤ c * (K * ‖L w‖) := mul_le_mul_of_nonneg_left (hLlow w) hc0.le
      _ = ‖L w‖ / 2 := by rw [← mul_assoc, hcK]; ring
  have h2 : ‖L w‖ ≤ ‖φ (v₀ + w) - φ v₀‖ + ‖φ (v₀ + w) - φ v₀ - L w‖ := by
    have := norm_sub_le (φ (v₀ + w) - φ v₀) (φ (v₀ + w) - φ v₀ - L w)
    rwa [sub_sub_cancel] at this
  linarith
/-- Separation of remote chart parameters by properness and injectivity: if `φ` is continuous and
injective on `V`, `φ v₀ ∈ W` with `W` open, and `V ∩ φ⁻¹(K)` is compact for every compact `K ⊆ W`,
then for each `δ > 0` some `ε > 0` has `ε ≤ ‖φ v - φ v₀‖` whenever `v ∈ V`, `δ ≤ ‖v - v₀‖`.
Pick a closed ball `K₀ = B_{ε₀}(φ v₀) ⊆ W`; by properness `Q = (V ∩ φ⁻¹(K₀)) ∩ {δ ≤ ‖v - v₀‖}` is
compact, and `‖φ v - φ v₀‖ > 0` on `Q` by injectivity.  If `Q = ∅` take `ε = ε₀`; otherwise take
`ε = min(ε₀, min_Q ‖φ v - φ v₀‖)` (`IsCompact.exists_isMinOn`).  Points with `φ v ∉ K₀` are farther
than `ε₀` from `φ v₀`. -/
theorem rsod_c1tan_chart_separation : ∀ (m N : ℕ) (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N))) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m), IsOpen W → ContinuousOn φ V → InjOn φ V → v₀ ∈ V → φ v₀ ∈ W → (∀ K : Set (EuclideanSpace ℝ (Fin N)), IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ V, δ ≤ ‖v - v₀‖ → ε ≤ ‖φ v - φ v₀‖ := by
  intro m N V W φ v₀ hW hφ hinj hv₀ hφv₀ hprop δ hδ
  -- Step 1: a compact closed ball `K₀ = B_{ε₀}(φ v₀) ⊆ W`, with `ε₀ = ε₁ / 2`.
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp hW (φ v₀) hφv₀
  have hε₀ : 0 < ε₁ / 2 := half_pos hε₁
  have hK₀W : closedBall (φ v₀) (ε₁ / 2) ⊆ W :=
    (closedBall_subset_ball (half_lt_self hε₁)).trans hball
  -- Step 2: `Q = (V ∩ φ⁻¹(K₀)) ∩ {v | δ ≤ ‖v - v₀‖}` is compact, and `‖φ v - φ v₀‖` is continuous
  -- on `Q ⊆ V` and positive there by injectivity.
  have hQ : IsCompact ((V ∩ φ ⁻¹' closedBall (φ v₀) (ε₁ / 2)) ∩ {v | δ ≤ ‖v - v₀‖}) :=
    (hprop _ (isCompact_closedBall _ _) hK₀W).inter_right
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hcont : ContinuousOn (fun v => ‖φ v - φ v₀‖)
      ((V ∩ φ ⁻¹' closedBall (φ v₀) (ε₁ / 2)) ∩ {v | δ ≤ ‖v - v₀‖}) :=
    ((hφ.mono fun v hv => hv.1.1).sub continuousOn_const).norm
  have hpos : ∀ q ∈ (V ∩ φ ⁻¹' closedBall (φ v₀) (ε₁ / 2)) ∩ {v | δ ≤ ‖v - v₀‖},
      0 < ‖φ q - φ v₀‖ := by
    intro q hq
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun hEq => ?_)
    have hqv : q = v₀ := hinj hq.1.1 hv₀ hEq
    have hδq : δ ≤ ‖q - v₀‖ := hq.2
    rw [hqv, sub_self, norm_zero] at hδq
    exact absurd hδq (not_le.mpr hδ)
  rcases ((V ∩ φ ⁻¹' closedBall (φ v₀) (ε₁ / 2)) ∩ {v | δ ≤ ‖v - v₀‖}).eq_empty_or_nonempty
    with hQe | hQne
  · -- Step 4: `Q = ∅`; take `ε = ε₀`.
    refine ⟨ε₁ / 2, hε₀, fun v hv hvδ => ?_⟩
    by_contra hlt
    have hvK : φ v ∈ closedBall (φ v₀) (ε₁ / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      exact (not_le.mp hlt).le
    have hvQ : v ∈ (V ∩ φ ⁻¹' closedBall (φ v₀) (ε₁ / 2)) ∩ {v | δ ≤ ‖v - v₀‖} :=
      ⟨⟨hv, hvK⟩, hvδ⟩
    rw [hQe] at hvQ
    exact hvQ
  · -- Step 3: `Q ≠ ∅`; take `ε = min ε₀ ‖φ q - φ v₀‖` for a minimizer `q ∈ Q`.
    obtain ⟨q, hqQ, hqmin⟩ := hQ.exists_isMinOn hQne hcont
    refine ⟨min (ε₁ / 2) ‖φ q - φ v₀‖, lt_min hε₀ (hpos q hqQ), fun v hv hvδ => ?_⟩
    by_cases hvK : φ v ∈ closedBall (φ v₀) (ε₁ / 2)
    · exact (min_le_right _ _).trans (hqmin ⟨⟨hv, hvK⟩, hvδ⟩)
    · rw [mem_closedBall, dist_eq_norm, not_le] at hvK
      exact (min_le_left _ _).trans hvK.le
/-- The rescaled chart `ψ_r(u) = r⁻¹(φ(v₀ + ru) − φ(v₀))` on `U_r = {u | v₀ + ru ∈ V}` is an
injective parametrization of the blow-up `η_{φ(v₀),r}(φ(V))` (`Chapter03.blowUpMap`) of the chart
image, with the same derivative `Dψ_r(u) = Dφ(v₀ + ru)`, for any `r ≠ 0` and any `v₀`. -/
theorem rsod_c1tan_blowUp_chart_reparam : ∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m) (r : ℝ), IsOpen V → DifferentiableOn ℝ φ V → InjOn φ V → r ≠ 0 → IsOpen {u : Rn m | v₀ + r • u ∈ V} ∧ InjOn (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) {u : Rn m | v₀ + r • u ∈ V} ∧ (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) '' {u : Rn m | v₀ + r • u ∈ V} = Poincare.SimonGMT.Chapter03.blowUpMap (φ v₀) r '' (φ '' V) ∧ ∀ u ∈ {u : Rn m | v₀ + r • u ∈ V}, HasFDerivAt (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) (fderiv ℝ φ (v₀ + r • u)) u := by
  intro m N V φ v₀ r hV hφ hinj hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `U_r` is the preimage of `V` under the continuous affine map `u ↦ v₀ + r • u`.
    exact hV.preimage (continuous_const.add (continuous_const_smul r))
  · -- Injectivity: cancel `r⁻¹`, then use `InjOn φ V`, then cancel `v₀` and `r`.
    intro u₁ hu₁ u₂ hu₂ h
    have h₁ : φ (v₀ + r • u₁) = φ (v₀ + r • u₂) :=
      sub_left_injective (smul_right_injective _ (inv_ne_zero hr) h)
    exact smul_right_injective _ hr (add_left_cancel (hinj hu₁ hu₂ h₁))
  · -- `u ↦ v₀ + r • u` maps `U_r` onto `V`, with inverse `v ↦ r⁻¹ • (v - v₀)`.
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨φ (v₀ + r • u), ⟨v₀ + r • u, hu, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
      have hv' : v₀ + r • r⁻¹ • (v - v₀) = v := by
        rw [smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
      refine ⟨r⁻¹ • (v - v₀), ?_, ?_⟩
      · show v₀ + r • r⁻¹ • (v - v₀) ∈ V
        rw [hv']
        exact hv
      · show r⁻¹ • (φ (v₀ + r • r⁻¹ • (v - v₀)) - φ v₀) = r⁻¹ • (φ v - φ v₀)
        rw [hv']
  · -- Chain rule: `Dψ_r(u) = r⁻¹ • (Dφ(v₀ + r • u) ∘ (r • id)) = Dφ(v₀ + r • u)`.
    intro u hu
    have hd : HasFDerivAt φ (fderiv ℝ φ (v₀ + r • u)) (v₀ + r • u) :=
      ((hφ _ hu).differentiableAt (hV.mem_nhds hu)).hasFDerivAt
    have ha : HasFDerivAt (fun u : Rn m => v₀ + r • u) (r • ContinuousLinearMap.id ℝ (Rn m)) u :=
      ((hasFDerivAt_id u).const_smul r).const_add v₀
    have hL : r⁻¹ • (fderiv ℝ φ (v₀ + r • u)).comp (r • ContinuousLinearMap.id ℝ (Rn m)) =
        fderiv ℝ φ (v₀ + r • u) := by
      refine ContinuousLinearMap.ext fun w => ?_
      rw [smul_apply, ContinuousLinearMap.comp_apply,
        smul_apply, ContinuousLinearMap.id_apply, map_smul,
        inv_smul_smul₀ hr]
    exact (((hd.comp u ha).sub_const (φ v₀)).const_smul r⁻¹).congr_fderiv hL
/-- Simon Ch. 3, proof of Theorem 1.6 ("⇒"): the blow-up of a chart.  Let `φ` be continuous on the
open set `V ⊆ ℝᵐ` and differentiable at `v₀` with derivative `L`, with `B_δ(v₀) ⊆ V`,
`c‖w‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖` for `‖w‖ ≤ δ` and `ε ≤ ‖φ(v) − φ(v₀)‖` for `v ∈ V`, `‖v − v₀‖ ≥ δ`;
let `J` be continuous on `V` and `f ∈ C_c(ℝ^N)`.  Then, with `U_r = {u | v₀ + ru ∈ V}`,
`∫_{U_r} J(v₀ + ru) f(r⁻¹(φ(v₀ + ru) − φ(v₀))) dHᵐ(u) → ∫ J(v₀) f(Lu) dHᵐ(u)` as `r ↓ 0`.
Proof: dominated convergence (`Hᵐ = Lᵐ` on `ℝᵐ`).  If `spt f ⊆ B_R(0)` and `0 < r < ε/R`, the
integrand vanishes unless `‖ru‖ < δ`, and then `‖u‖ ≤ R/c`; so it is bounded by
`sup_{B_δ(v₀)} |J| · sup |f| · 1_{B_{R/c}(0)}`.  Pointwise, `v₀ + ru ∈ V` eventually and
`r⁻¹(φ(v₀ + ru) − φ(v₀)) → Lu` (`HasFDerivAt.lim`). -/
theorem rsod_c1tan_chart_blowUp_tendsto : ∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (J : Rn m → ℝ) (L : Rn m →L[ℝ] EuclideanSpace ℝ (Fin N)) (v₀ : Rn m) (c δ ε : ℝ) (f : EuclideanSpace ℝ (Fin N) → ℝ), IsOpen V → ContinuousOn φ V → ContinuousOn J V → HasFDerivAt φ L v₀ → 0 < c → 0 < δ → 0 < ε → closedBall v₀ δ ⊆ V → (∀ w : Rn m, ‖w‖ ≤ δ → c * ‖w‖ ≤ ‖φ (v₀ + w) - φ v₀‖) → (∀ v ∈ V, δ ≤ ‖v - v₀‖ → ε ≤ ‖φ v - φ v₀‖) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ u in {u : Rn m | v₀ + r • u ∈ V}, J (v₀ + r • u) * f (r⁻¹ • (φ (v₀ + r • u) - φ v₀)) ∂(μHE[m] : Measure (Rn m))) (𝓝[>] 0) (𝓝 (∫ u, J v₀ * f (L u) ∂(μHE[m] : Measure (Rn m)))) := by
  intro m N V φ J L v₀ c δ ε f hV hφ hJ hL hc hδ hε hball ha hb hf hfs
  -- Step 1: `Hᵐ = Lᵐ` on `ℝᵐ`, and `v₀ ∈ B_δ(v₀) ⊆ V`.
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hv₀ : v₀ ∈ V := hball (mem_closedBall_self hδ.le)
  -- Step 2: `f(y) ≠ 0 ⇒ ‖y‖ ≤ R`, `|f| ≤ M`, and `|J| ≤ Λ` on `B_δ(v₀)`.
  obtain ⟨R₀, hR₀⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  have hR : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ max R₀ 1 := fun y hy =>
    (mem_closedBall_zero_iff.mp (hR₀ (subset_tsupport f hy))).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall v₀ δ).exists_bound_of_continuousOn (hJ.mono hball)
  have hΛM : 0 ≤ Λ * M := mul_nonneg ((norm_nonneg _).trans (hΛ v₀ (mem_closedBall_self hδ.le)))
    ((norm_nonneg _).trans (hM 0))
  -- Step 3: `U_r = {u | v₀ + r u ∈ V}` is open, so `∫_{U_r} g_r = ∫ 1_{U_r} g_r`.
  have hcont : ∀ r : ℝ, Continuous fun u : Rn m => v₀ + r • u := fun r => by fun_prop
  have hUo : ∀ r : ℝ, IsOpen {u : Rn m | v₀ + r • u ∈ V} := fun r => hV.preimage (hcont r)
  have key : Tendsto (fun r : ℝ => ∫ u, {u : Rn m | v₀ + r • u ∈ V}.indicator
      (fun u => J (v₀ + r • u) * f (r⁻¹ • (φ (v₀ + r • u) - φ v₀))) u) (𝓝[>] 0)
      (𝓝 (∫ u, J v₀ * f (L u))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((closedBall (0 : Rn m) (max R₀ 1 / c)).indicator fun _ => Λ * M) ?_ ?_ ?_ ?_
    · -- Step 4: `g_r` is continuous on the open set `U_r`.
      refine Eventually.of_forall fun r => ?_
      rw [aestronglyMeasurable_indicator_iff (hUo r).measurableSet]
      refine ContinuousOn.aestronglyMeasurable ?_ (hUo r).measurableSet
      have hmaps : MapsTo (fun u : Rn m => v₀ + r • u) {u | v₀ + r • u ∈ V} V := fun u hu => hu
      exact (hJ.comp (hcont r).continuousOn hmaps).mul (hf.comp_continuousOn
        (((hφ.comp (hcont r).continuousOn hmaps).sub continuousOn_const).const_smul r⁻¹))
    · -- Step 5: for `0 < r < ε/R`, `|1_{U_r} g_r| ≤ ΛM 1_{B_{R/c}(0)}`.
      filter_upwards [Ioo_mem_nhdsGT (div_pos hε hR)] with r hr
      refine ae_of_all _ fun u => ?_
      obtain ⟨hr0, hrε⟩ := hr
      by_cases hu : u ∈ {u : Rn m | v₀ + r • u ∈ V}
      · rw [indicator_of_mem hu]
        by_cases hfz : f (r⁻¹ • (φ (v₀ + r • u) - φ v₀)) = 0
        · rw [hfz, mul_zero, norm_zero]
          exact indicator_nonneg (fun _ _ => hΛM) _
        · have hψ := hfR _ hfz
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0, inv_mul_le_iff₀ hr0] at hψ
          have hrR : r * max R₀ 1 < ε := (lt_div_iff₀ hR).mp hrε
          have hsmall : ‖r • u‖ < δ := by
            by_contra hcon
            have := hb (v₀ + r • u) hu (by rw [add_sub_cancel_left]; exact not_lt.mp hcon)
            linarith
          have hJb : ‖J (v₀ + r • u)‖ ≤ Λ := hΛ _ (by
            rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hsmall.le)
          have hlow := ha (r • u) hsmall.le
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at hlow
          have hu_le : ‖u‖ ≤ max R₀ 1 / c := by
            rw [le_div_iff₀ hc]
            refine le_of_mul_le_mul_left ?_ hr0
            calc r * (‖u‖ * c) = c * (r * ‖u‖) := by ring
              _ ≤ _ := hlow
              _ ≤ _ := hψ
          rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hu_le), norm_mul]
          exact mul_le_mul hJb (hM _) (norm_nonneg _) ((norm_nonneg _).trans hJb)
      · rw [indicator_of_notMem hu, norm_zero]
        exact indicator_nonneg (fun _ _ => hΛM) _
    · -- The bound is integrable: a constant on a closed ball.
      exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    · -- Step 6: pointwise convergence.
      refine ae_of_all _ fun u => ?_
      have hlin : Tendsto (fun r : ℝ => v₀ + r • u) (𝓝[>] 0) (𝓝 v₀) := by
        have : Tendsto (fun r : ℝ => v₀ + r • u) (𝓝 0) (𝓝 (v₀ + (0 : ℝ) • u)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hmem : ∀ᶠ r in 𝓝[>] (0 : ℝ), v₀ + r • u ∈ V := hlin.eventually (hV.mem_nhds hv₀)
      have hJlim : Tendsto (fun r : ℝ => J (v₀ + r • u)) (𝓝[>] 0) (𝓝 (J v₀)) :=
        (hJ.continuousAt (hV.mem_nhds hv₀)).tendsto.comp hlin
      have hnorm : Tendsto (fun r : ℝ => ‖r⁻¹‖) (𝓝[>] 0) atTop :=
        tendsto_abs_atTop_atTop.comp tendsto_inv_nhdsGT_zero
      have hψ : Tendsto (fun r : ℝ => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) (𝓝[>] 0) (𝓝 (L u)) := by
        simpa only [inv_inv] using hL.lim u hnorm
      refine (hJlim.mul ((hf.tendsto _).comp hψ)).congr' ?_
      filter_upwards [hmem] with r hr
      rw [indicator_of_mem (show u ∈ {u : Rn m | v₀ + r • u ∈ V} from hr)]
      rfl
  -- Step 7: conclude.
  exact key.congr fun r => integral_indicator (hUo r).measurableSet
/-- Simon Ch. 3, Definition 1.4 is local: if `S ∩ B̆_ε(x) = T ∩ B̆_ε(x)` for some `ε > 0`, then an
approximate tangent space of `T` at `x` is also one of `S` at `x`.  Proof: a test function
`f ∈ C_c(ℝ^N)` vanishes off `B = B_R(0)` for some `R > 0`, so
`∫_{η_{x,r}(A)} f = ∫_{η_{x,r}(A) ∩ B} f` for every set `A`; for `0 < r < ε/R`, `r⁻¹(z − x) ∈ B`
forces `|z − x| ≤ rR < ε`, hence `η_{x,r}(S) ∩ B = η_{x,r}(T) ∩ B`, and the blow-up integrals of
`S` and `T` agree eventually as `r ↓ 0`. -/
theorem rsod_c1tan_approxTangent_of_local_eq : ∀ (m N : ℕ) (S T : Set (EuclideanSpace ℝ (Fin N))) (x : EuclideanSpace ℝ (Fin N)) (ε : ℝ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))), 0 < ε → S ∩ ball x ε = T ∩ ball x ε → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m T x P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m S x P := by
  intro m N S T x ε P hε hST hT
  refine ⟨hT.1, fun f => ?_⟩
  -- Support radius: `f` vanishes off `B = B_R(0)` with `R = max R₀ 1 > 0`.
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin N))).1
    f.hasCompactSupport.isBounded
  have hR : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : Function.support f ⊆ closedBall 0 (max R₀ 1) :=
    (subset_tsupport f).trans (hR₀.trans (closedBall_subset_closedBall (le_max_left _ _)))
  -- Cutting off: `∫_A f = ∫_{A ∩ B} f` for every set `A` (only `B` needs to be measurable).
  have hcut : ∀ A : Set (EuclideanSpace ℝ (Fin N)),
      ∫ y in A, f y ∂μHE[m] = ∫ y in A ∩ closedBall 0 (max R₀ 1), f y ∂μHE[m] := by
    intro A
    rw [← setIntegral_indicator measurableSet_closedBall, Set.indicator_eq_self.2 hsupp]
  -- For `0 < r < ε / R`: `η_{x,r}(A) ∩ B ⊆ η_{x,r}(A') ∩ B` whenever `A ∩ B̆_ε(x) ⊆ A'`.
  have hmono : ∀ A A' : Set (EuclideanSpace ℝ (Fin N)), A ∩ ball x ε ⊆ A' →
      ∀ r ∈ Ioo 0 (ε / max R₀ 1),
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' A ∩ closedBall 0 (max R₀ 1) ⊆
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' A' ∩ closedBall 0 (max R₀ 1) := by
    rintro A A' hAA' r ⟨hr, hrR⟩ y ⟨⟨z, hz, rfl⟩, hy⟩
    refine ⟨⟨z, hAA' ⟨hz, ?_⟩, rfl⟩, hy⟩
    rw [mem_closedBall_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg hr.le] at hy
    rw [mem_ball, dist_eq_norm]
    calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
      _ ≤ r * max R₀ 1 := mul_le_mul_of_nonneg_left hy hr.le
      _ < ε := (lt_div_iff₀ hR).1 hrR
  -- Hence the blow-up integrals of `T` and `S` agree for `0 < r < ε / R`; the limit transfers.
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hR)] with r hr
  rw [hcut (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T),
    hcut (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S),
    (hmono T S (hST.symm.subset.trans inter_subset_left) r hr).antisymm
      (hmono S T (hST.subset.trans inter_subset_left) r hr)]
/-- **`C¹` submanifolds have approximate tangent spaces** (Simon Ch. 3, proof of Theorem 1.6 "⇒":
"`N_j` is a `C¹` submanifold, so `lim ∫_{η_{x,r}(N_j)} f dHⁿ = ∫_{T_x N_j} f dHⁿ`").  If `S` is an
`m`-dimensional `C¹` submanifold and `φ` is a chart of `S` with `φ(v₀) = x`, then `Dφ(v₀)(ℝᵐ)` is
the approximate tangent space of `S` at `x`.  Proof: the area formula for the rescaled chart
`ψ_r(u) = r⁻¹(φ(v₀ + ru) − x)` on `U_r = {u | v₀ + ru ∈ V}`, dominated convergence, the area
formula for `Dφ(v₀)`, and locality of Definition 1.4 (`S ∩ B̆_ε(x) = φ(V) ∩ B̆_ε(x)`). -/
theorem rsod_isC1Submanifold_approxTangent : ∀ (m N : ℕ), 1 ≤ m → ∀ (S : Set (EuclideanSpace ℝ (Fin N))), IsC1Submanifold m S → ∀ x ∈ S, ∃ P : Submodule ℝ (EuclideanSpace ℝ (Fin N)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m S x P := by
  intro m N _ S hS x hx
  obtain ⟨V, W, φ, hV, hW, hxW, hφ, hinj, himg, hprop, hder⟩ := hS x hx
  have hxV : x ∈ φ '' V := by
    rw [himg]
    exact ⟨hxW, hx⟩
  obtain ⟨v₀, hv₀, rfl⟩ := hxV
  have hdiff : DifferentiableOn ℝ φ V := hφ.differentiableOn one_ne_zero
  have hL : HasFDerivAt φ (fderiv ℝ φ v₀) v₀ :=
    (hdiff.differentiableAt (hV.mem_nhds hv₀)).hasFDerivAt
  -- `J_φ(v) = (Dφ(v)).normDet` (Simon (3.3)) is continuous on `V`.
  have hJ : ContinuousOn (Poincare.SimonGMT.Chapter02.areaJacobianAt φ) V :=
    (Poincare.SimonGMT.Chapter02.continuous_normDet.comp_continuousOn
      (hφ.continuousOn_fderiv_of_isOpen hV le_rfl)).congr fun v _ =>
        Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet φ v
  -- (a) `c‖w‖ ≤ ‖φ(v₀ + w) − x‖` for `‖w‖ ≤ δ`, and (b) `ε ≤ ‖φ(v) − x‖` for `v ∈ V` with
  -- `‖v − v₀‖ ≥ δ`.
  obtain ⟨c, hc, δ, hδ, hball, hlow⟩ :=
    Submission.rsod_c1tan_chart_lower_bound m N V φ v₀ hV hφ hv₀ (hder v₀ hv₀)
  obtain ⟨ε, hε, hsep⟩ := Submission.rsod_c1tan_chart_separation m N V W φ v₀ hW
    hφ.continuousOn hinj hv₀ hxW hprop δ hδ
  have hT : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m (φ '' V) (φ v₀)
      (LinearMap.range (fderiv ℝ φ v₀ : Rn m →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) := by
    refine ⟨?_, fun f => ?_⟩
    · rw [LinearMap.finrank_range_of_inj
        (f := (fderiv ℝ φ v₀ : Rn m →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) (hder v₀ hv₀),
        finrank_euclideanSpace_fin]
    -- For `r > 0`, the area formula for `ψ_r(u) = r⁻¹(φ(v₀ + ru) − x)` on
    -- `U_r = {u | v₀ + ru ∈ V}` gives `∫_{η_{x,r}(φ(V))} f = ∫_{U_r} J_φ(v₀ + ru) f(ψ_r(u))`.
    have hblow : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∫ u in {u : Rn m | v₀ + r • u ∈ V},
          Poincare.SimonGMT.Chapter02.areaJacobianAt φ (v₀ + r • u) *
            f (r⁻¹ • (φ (v₀ + r • u) - φ v₀)) ∂(μHE[m] : Measure (Rn m))) =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (φ v₀) r '' (φ '' V), f y ∂μHE[m] := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      obtain ⟨hU, hψinj, hψimg, hψ⟩ :=
        Submission.rsod_c1tan_blowUp_chart_reparam m N V φ v₀ r hV hdiff hinj (ne_of_gt hr)
      have harea := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
        hU.measurableSet (fun u hu => (hψ u hu).differentiableAt)
        (fun u hu => by rw [(hψ u hu).fderiv]; exact hder (v₀ + r • u) hu) hψinj ⇑f
      rw [finrank_euclideanSpace_fin] at harea
      rw [← hψimg, harea]
      refine setIntegral_congr_fun hU.measurableSet fun u hu => ?_
      simp only [smul_eq_mul, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet,
        (hψ u hu).fderiv]
    -- The area formula for `L = Dφ(v₀)` on `ℝᵐ`: `∫ J_L f(Lu) du = ∫_{L(ℝᵐ)} f`.
    have hlin : ∫ u, Poincare.SimonGMT.Chapter02.areaJacobianAt φ v₀ * f (fderiv ℝ φ v₀ u)
          ∂(μHE[m] : Measure (Rn m)) =
        ∫ y in (LinearMap.range (fderiv ℝ φ v₀ : Rn m →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) :
          Set (EuclideanSpace ℝ (Fin N))), f y ∂μHE[m] := by
      have harea := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
        (s := univ) (f := ⇑(fderiv ℝ φ v₀)) MeasurableSet.univ
        (fun u _ => (fderiv ℝ φ v₀).differentiableAt)
        (fun u _ => by rw [ContinuousLinearMap.fderiv]; exact hder v₀ hv₀)
        (hder v₀ hv₀).injOn ⇑f
      rw [finrank_euclideanSpace_fin, image_univ, setIntegral_univ] at harea
      rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, harea]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [smul_eq_mul, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet,
        ContinuousLinearMap.fderiv]
    rw [← hlin]
    exact (Submission.rsod_c1tan_chart_blowUp_tendsto m N V φ
      (Poincare.SimonGMT.Chapter02.areaJacobianAt φ) (fderiv ℝ φ v₀) v₀ c δ ε f hV
      hφ.continuousOn hJ hL hc hδ hε hball hlow hsep f.continuous
      f.hasCompactSupport).congr' hblow
  -- `S` and `φ(V) = W ∩ S` agree on a ball `B̆_{ε₀}(x) ⊆ W`.
  obtain ⟨ε₀, hε₀, hε₀W⟩ := Metric.isOpen_iff.1 hW (φ v₀) hxW
  refine ⟨_, Submission.rsod_c1tan_approxTangent_of_local_eq m N S (φ '' V) (φ v₀) ε₀ _ hε₀
    ?_ hT⟩
  rw [himg]
  ext y
  exact ⟨fun h => ⟨⟨hε₀W h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
