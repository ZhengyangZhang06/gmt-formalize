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

/-- Simon Ch. 2 §4: an open subset of an `m`-dimensional `C¹` submanifold is again one.  Given a
chart `(V, W, φ)` of `S` at `y ∈ B ∩ S`, the restricted chart `(V ∩ φ⁻¹(B), W ∩ B, φ)` works:
`φ(V ∩ φ⁻¹(B)) = φ(V) ∩ B`, and for compact `K ⊆ W ∩ B`,
`V ∩ φ⁻¹(B) ∩ φ⁻¹(K) = V ∩ φ⁻¹(K)`. -/
theorem rsod_isC1Submanifold_open_inter : ∀ (m N : ℕ) (S B : Set (EuclideanSpace ℝ (Fin N))),
    IsC1Submanifold m S → IsOpen B → IsC1Submanifold m (B ∩ S) := by
  intro m N S B hS hB y hy
  obtain ⟨V, W, φ, hV, hW, hyW, hφ, hinj, himg, hprop, hder⟩ := hS y hy.2
  refine ⟨V ∩ φ ⁻¹' B, W ∩ B, φ, hφ.continuousOn.isOpen_inter_preimage hV hB, hW.inter hB,
    ⟨hyW, hy.1⟩, hφ.mono inter_subset_left, hinj.mono inter_subset_left, ?_, ?_,
    fun x hx => hder x hx.1⟩
  · rw [image_inter_preimage, himg]
    ext z
    simp only [mem_inter_iff]
    tauto
  · intro K hK hKWB
    have hKV : V ∩ φ ⁻¹' B ∩ φ ⁻¹' K = V ∩ φ ⁻¹' K := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, (hKWB hx.2).2⟩, hx.2⟩⟩
    rw [hKV]
    exact hprop K hK fun z hz => (hKWB hz).1
/-- Pythagorean identity for graph points: `|(x, y)|² = |x|² + |y|²` for the point
`(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}`.  Expand the three squared Euclidean norms as sums of squared
coordinates (`EuclideanSpace.real_norm_sq_eq`), split the sum over `Fin (n + ℓ)` into the indices
`Fin.castAdd ℓ j` and `Fin.natAdd n k` (`Fin.sum_univ_add`), and read off the coordinates `x j`,
resp. `y k`, of `graphPoint x y` there (`Fin.append_left`/`Fin.append_right`). -/
theorem rsod_norm_graphPoint_sq : ∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ),
    ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  intro n ℓ x y
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]
  simp [graphPoint]
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

/-- The rotated, translated graph chart `φ x = q (graphPoint x (u x)) + x₀` of a map `u` that is
`C¹` on an open set `Ω ⊆ ℝⁿ` is injective on all of `ℝⁿ`, `C¹` on `Ω`, and has injective
derivative at every point of `Ω`.  By `rsod_graphPoint_eq_finAddEquivProd_symm`,
`φ x = A (x, u x) + x₀` for the injective continuous linear map `A = q ∘ E.symm`,
`E = EuclideanSpace.finAddEquivProd`.  Hence `φ x = φ x'` forces `(x, u x) = (x', u x')`; `φ` is
`C¹` on `Ω` as `A` after the `C¹` map `x ↦ (x, u x)`, plus a constant; and at `x ∈ Ω` (a
neighbourhood of `x`, so `u` is differentiable there) the chain rule gives
`Dφ(x) v = A (v, Du(x) v)`, which determines `v` since `A` is injective. -/
theorem rsod_graphChart_injective_contDiffOn_fderiv_injective : ∀ {n ℓ : ℕ}
    (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (x₀ : Amb n ℓ) (Ω : Set (Rn n)), IsOpen Ω →
    ContDiffOn ℝ 1 u Ω → Function.Injective (fun x => q (graphPoint x (u x)) + x₀) ∧
      ContDiffOn ℝ 1 (fun x => q (graphPoint x (u x)) + x₀) Ω ∧
      ∀ x ∈ Ω, Function.Injective (fderiv ℝ (fun x => q (graphPoint x (u x)) + x₀) x) := by
  intro n ℓ q u x₀ Ω hΩ hu
  let E : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  let A : Rn n × Rn ℓ →L[ℝ] Amb n ℓ := (q : Amb n ℓ →L[ℝ] Amb n ℓ).comp (E.symm : _ →L[ℝ] _)
  have hA : Function.Injective A := q.injective.comp E.symm.injective
  have hφ : (fun x => q (graphPoint x (u x)) + x₀) = fun x => A (x, u x) + x₀ := by
    funext x
    simp [A, E, rsod_graphPoint_eq_finAddEquivProd_symm]
  rw [hφ]
  refine ⟨fun x x' h => (Prod.ext_iff.mp (hA (add_right_cancel h))).1,
    (A.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)).add contDiffOn_const, fun x hx => ?_⟩
  have hux : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
  have hφx : HasFDerivAt (fun x => A (x, u x) + x₀)
      (A.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x))) x :=
    (A.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hux)).add_const x₀
  rw [hφx.fderiv]
  exact fun v w h => (Prod.ext_iff.mp (hA h)).1
/-- Fact (Gr) in the proof of Simon Ch. 5, Corollary 7.3, for the Ch. 2 §4 notion of a `C¹`
submanifold: if `u` is `C¹` on the closed ball `Bⁿ_s(0)` and `{y : y + x₀ ∈ S}` agrees with
`q(graph u)` in `B_s(0)`, then `B̆_s(x₀) ∩ S` is an `n`-dimensional `C¹` submanifold.  A single
chart `φ(x) = q(x, u(x)) + x₀` on `Ω = B̆ⁿ_s(0) ∩ φ⁻¹(B̆_s(x₀))` serves every point, because
`|x| ≤ |(x, u(x))| = |φ(x) - x₀|`; for compact `K ⊆ B̆_s(x₀)`, `Ω ∩ φ⁻¹(K) = Bⁿ_s(0) ∩ φ⁻¹(K)` is a
closed subset of the compact ball. -/
theorem rsod_isC1Submanifold_ball_inter_graph : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ)
    (u : Rn n → Rn ℓ) (x₀ : Amb n ℓ) (s : ℝ) (S : Set (Amb n ℓ)), 0 < s →
    ContDiffOn ℝ 1 u (closedBall 0 s) →
    (fun y => y + x₀) ⁻¹' S ∩ closedBall 0 s = q '' graphOver u (closedBall 0 s) ∩ closedBall 0 s →
    IsC1Submanifold n (ball x₀ s ∩ S) := by
  intro n ℓ q u x₀ s S _hs hu hS
  set φ : Rn n → Amb n ℓ := fun x => q (graphPoint x (u x)) + x₀
  -- Step 1: `|x| ≤ |(x, u(x))| = |φ(x) - x₀|`, so `φ(x) ∈ B̆_s(x₀)` forces `x ∈ B̆ⁿ_s(0)`.
  have hnorm : ∀ x : Rn n, ‖x‖ ≤ ‖graphPoint x (u x)‖ := fun x => by
    nlinarith [Submission.rsod_norm_graphPoint_sq x (u x), norm_nonneg x,
      norm_nonneg (graphPoint x (u x)), sq_nonneg ‖u x‖]
  have hdist : ∀ x : Rn n, dist (φ x) x₀ = ‖graphPoint x (u x)‖ := fun x => by
    rw [dist_eq_norm]
    show ‖q (graphPoint x (u x)) + x₀ - x₀‖ = _
    rw [add_sub_cancel_right, q.norm_map]
  have hball : ∀ x : Rn n, φ x ∈ ball x₀ s → x ∈ ball (0 : Rn n) s := fun x hx =>
    mem_ball_zero_iff.2 ((hnorm x).trans_lt ((hdist x).symm.trans_lt (mem_ball.1 hx)))
  -- Step 2: for `|z| ≤ s`, `z + x₀ ∈ S` iff `z = q(x, u(x))` for some `x ∈ Bⁿ_s(0)`.
  have hH : ∀ z : Amb n ℓ, ‖z‖ ≤ s →
      (z + x₀ ∈ S ↔ ∃ x ∈ closedBall (0 : Rn n) s, q (graphPoint x (u x)) = z) := by
    intro z hz
    have hz' : z ∈ closedBall (0 : Amb n ℓ) s := mem_closedBall_zero_iff.2 hz
    constructor
    · intro hzS
      have hzq : z ∈ q '' graphOver u (closedBall 0 s) ∩ closedBall 0 s := by
        rw [← hS]
        exact ⟨hzS, hz'⟩
      obtain ⟨⟨w, ⟨x, hx, rfl⟩, rfl⟩, -⟩ := hzq
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hzS : q (graphPoint x (u x)) ∈ (fun y => y + x₀) ⁻¹' S ∩ closedBall 0 s := by
        rw [hS]
        exact ⟨⟨graphPoint x (u x), ⟨x, hx, rfl⟩, rfl⟩, hz'⟩
      exact hzS.1
  -- Steps 3–6: `φ` is injective, and `C¹` with injective derivative on `B̆ⁿ_s(0)`; it is
  -- continuous on `Bⁿ_s(0)` because `(x, y) ↦ graphPoint x y` is a continuous linear map.
  obtain ⟨hinj, hC1, hder⟩ := Submission.rsod_graphChart_injective_contDiffOn_fderiv_injective
    q u x₀ (ball 0 s) isOpen_ball (hu.mono ball_subset_closedBall)
  have hcont : ContinuousOn φ (closedBall 0 s) := by
    have hG : ContinuousOn (fun x : Rn n => graphPoint x (u x)) (closedBall 0 s) := by
      simp_rw [Submission.rsod_graphPoint_eq_finAddEquivProd_symm]
      exact (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm.continuous
        |>.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)
    exact (q.continuous.comp_continuousOn hG).add continuousOn_const
  intro y hy
  refine ⟨ball 0 s ∩ φ ⁻¹' ball x₀ s, ball x₀ s, φ,
    (hcont.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball,
    isOpen_ball, hy.1, hC1.mono inter_subset_left, hinj.injOn, ?_, ?_,
    fun x hx => hder x hx.1⟩
  · -- Step 7: `φ(Ω) = B̆_s(x₀) ∩ S`.
    ext y'
    constructor
    · rintro ⟨x, ⟨hx, hφx⟩, rfl⟩
      refine ⟨hφx, hφx, (hH (q (graphPoint x (u x))) ?_).2 ⟨x, ball_subset_closedBall hx, rfl⟩⟩
      rw [q.norm_map, ← hdist]
      exact (mem_ball.1 hφx).le
    · rintro ⟨-, hy', hy'S⟩
      obtain ⟨x, -, hx⟩ := (hH (y' - x₀) (mem_ball_iff_norm.1 hy').le).1
        (by rwa [sub_add_cancel])
      have hφx : φ x = y' := by
        show q (graphPoint x (u x)) + x₀ = y'
        rw [hx, sub_add_cancel]
      have hφx' : φ x ∈ ball x₀ s := by
        rw [hφx]
        exact hy'
      exact ⟨x, ⟨hball x hφx', hφx'⟩, hφx⟩
  · -- Step 8: for compact `K ⊆ B̆_s(x₀)`, `Ω ∩ φ⁻¹(K) = Bⁿ_s(0) ∩ φ⁻¹(K)` is compact.
    intro K hK hKW
    have hset : ball 0 s ∩ φ ⁻¹' ball x₀ s ∩ φ ⁻¹' K = closedBall 0 s ∩ φ ⁻¹' K := by
      ext x
      exact ⟨fun hx => ⟨ball_subset_closedBall hx.1.1, hx.2⟩,
        fun hx => ⟨⟨hball x (hKW hx.2), hKW hx.2⟩, hx.2⟩⟩
    rw [hset]
    exact (isCompact_closedBall 0 s).of_isClosed_subset
      (hcont.preimage_isClosed_of_isClosed isClosed_closedBall hK.isClosed) inter_subset_left
/-- Localization and rescaling (Simon Ch. 5, proof of Corollary 7.3): for an open `B ⊆ U` and
`c > 0`, `v(M ∩ B, cθ)` is a rectifiable varifold in `B` with weight `c μ_V ⌞ B` and support
`B ∩ spt V`.  Approximate tangent planes are local and homogeneous in `θ`, so the tangential
divergences of the two varifolds agree on `B`; hence the first variation formula and `Lᵖ_loc`
bounds for `H` pass from `U` to `B`. -/
theorem rsod_exists_localized_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (B : Set (Amb n ℓ)) (c : ℝ), IsOpen B → B ⊆ U → 0 < c →
    ∃ W : RectifiableVarifold n ℓ B, W.carrier = V.carrier ∩ B ∧
      (∀ x, W.mult x = c * V.mult x) ∧ W.weight = ENNReal.ofReal c • V.weight.restrict B ∧
      W.support = B ∩ V.support ∧
      (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
        W.HasGeneralizedMeanCurvature H) ∧
      (∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ), V.LocallyLp H p → W.LocallyLp H p) := by
  intro n ℓ U V B c hB hBU hc
  have hBm : MeasurableSet B := hB.measurableSet
  -- The varifold `v(M ∩ B, cθ)` in `B`.
  obtain ⟨W, hWc, hWm⟩ : ∃ W : RectifiableVarifold n ℓ B,
      W.carrier = V.carrier ∩ B ∧ W.mult = fun x => c * V.mult x :=
    ⟨{ carrier := V.carrier ∩ B
       mult := fun x => c * V.mult x
       carrier_subset := inter_subset_right
       nullMeasurableSet_carrier := V.nullMeasurableSet_carrier.inter hBm.nullMeasurableSet
       countablyRectifiable := V.countablyRectifiable.mono inter_subset_left
       mult_pos := fun x hx => mul_pos hc (V.mult_pos x hx.1)
       aemeasurable_mult := (V.aemeasurable_mult.mono_measure
         (Measure.restrict_mono inter_subset_left le_rfl)).const_mul c
       integrableOn_mult := fun K hK hKB =>
         ((V.integrableOn_mult K hK (hKB.trans hBU)).mono_set
           fun x hx => ⟨hx.1.1, hx.2⟩).const_mul c }, rfl, rfl⟩
  -- `μ_W = c μ_V ⌞ B`.
  have hweight : W.weight = ENNReal.ofReal c • V.weight.restrict B := by
    simp only [RectifiableVarifold.weight, hWc, hWm]
    rw [restrict_withDensity hBm, Measure.restrict_restrict hBm, inter_comm B,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    exact ENNReal.ofReal_mul hc.le
  -- `spt W = B ∩ spt μ_V = B ∩ spt V`, since `B` is open.
  have hsupp : W.support = B ∩ V.support := by
    have hsmul : (ENNReal.ofReal c • V.weight.restrict B).support =
        (V.weight.restrict B).support :=
      Subset.antisymm Measure.smul_absolutelyContinuous.support_mono
        (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 hc).ne').support_mono
    rw [RectifiableVarifold.support, RectifiableVarifold.support, hweight, hsmul, ← inter_assoc,
      inter_eq_left.2 hBU]
    refine Subset.antisymm (fun x hx => ⟨hx.1, Measure.support_mono Measure.restrict_le_self hx.2⟩)
      fun x hx => ⟨hx.1, Measure.interior_inter_support ⟨by rw [hB.interior_eq]; exact hx.1, hx.2⟩⟩
  -- Approximate tangent planes are local and homogeneous in the multiplicity: at `x ∈ B` the
  -- blow-up integrals of `(M ∩ B, cθ)` are eventually `c` times those of `(M, θ)`.
  have key : ∀ x ∈ B, ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult x P ↔
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
    intro x hx P
    rw [hWc, hWm]
    obtain ⟨d, hd, hdB⟩ := Metric.isOpen_iff.1 hB x hx
    refine and_congr_right fun _ => forall_congr' fun f => ?_
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
    have hev : (fun r : ℝ =>
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (V.carrier ∩ B),
            f y * (c * V.mult (x + r • y)) ∂μHE[n]) =ᶠ[𝓝[>] 0]
        fun r => c * ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier,
          f y * V.mult (x + r • y) ∂μHE[n] := by
      filter_upwards [Ioo_mem_nhdsGT (div_pos hd hR)] with r hr
      have hr0 : r ≠ 0 := hr.1.ne'
      -- `η_{x,r}(S) = {y | x + r y ∈ S}`.
      have himg : ∀ S : Set (Amb n ℓ),
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' S = (fun y => x + r • y) ⁻¹' S :=
        fun S => congrFun (image_eq_preimage_of_inverse
          (fun y => by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr0])
          fun y => by simp [Poincare.SimonGMT.Chapter03.blowUpMap, hr0]) S
      have hBr : MeasurableSet ((fun y : Amb n ℓ => x + r • y) ⁻¹' B) :=
        (hB.preimage (by fun_prop)).measurableSet
      -- If `f y ≠ 0` then `‖y‖ ≤ R`, so `x + r y ∈ B̆_d(x) ⊆ B`.
      have hvan : ∀ y ∉ (fun y : Amb n ℓ => x + r • y) ⁻¹' B,
          f y * (c * V.mult (x + r • y)) = 0 := by
        intro y hy
        by_cases hfy : f y = 0
        · rw [hfy, zero_mul]
        · refine absurd ?_ hy
          have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hfR (subset_tsupport f hfy))
          apply hdB
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
          calc r * ‖y‖ ≤ r * R := mul_le_mul_of_nonneg_left hyR hr.1.le
            _ < d := (lt_div_iff₀ hR).1 hr.2
      rw [himg, himg, preimage_inter, inter_comm, ← Measure.restrict_restrict hBr,
        setIntegral_eq_integral_of_forall_compl_eq_zero hvan, ← integral_const_mul]
      congr 1
      funext y
      ring
    constructor
    · intro h
      simpa only [mul_assoc, inv_mul_cancel_left₀ hc.ne'] using (h.congr' hev).const_mul c⁻¹
    · intro h
      simpa only [mul_assoc] using (h.const_mul c).congr' hev.symm
  -- Hence `W` and `V` choose the same tangent plane at each `x ∈ B`.
  have htan : ∀ x ∈ B, W.tangentProj x = V.tangentProj x := by
    intro x hx
    have hchoose : ∀ (p q : Submodule ℝ (Amb n ℓ) → Prop) (h₁ : ∃ P, p P) (h₂ : ∃ P, q P),
        p = q → Classical.choose h₁ = Classical.choose h₂ := by
      rintro p q h₁ h₂ rfl
      rfl
    unfold RectifiableVarifold.tangentProj
    by_cases h₁ : ∃ P,
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult x P
    · have h₂ := (exists_congr (key x hx)).1 h₁
      simp only [dite_eq_left h₁, dite_eq_left h₂]
      congr 1
      exact hchoose _ _ h₁ h₂ (funext fun P => propext (key x hx P))
    · have h₂ : ¬∃ P,
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P :=
        fun h => h₁ ((exists_congr (key x hx)).2 h)
      simp only [dite_eq_right h₁, dite_eq_right h₂]
  have hdiv : ∀ (X : Amb n ℓ → Amb n ℓ), ∀ x ∈ B, W.divM X x = V.divM X x := by
    intro X x hx
    rw [RectifiableVarifold.divM, RectifiableVarifold.divM, htan x hx]
  -- Off `tsupport X`, `DX = 0` and hence `div_M X = 0`.
  have hdiv0 : ∀ (X : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ), x ∉ tsupport X → V.divM X x = 0 := by
    intro X x hx
    rw [RectifiableVarifold.divM, fderiv_of_notMem_tsupport ℝ hx]
    simp
  refine ⟨W, hWc, fun x => by rw [hWm], hweight, hsupp, fun H hH => ⟨fun x hx => ?_, ?_⟩, ?_⟩
  · -- `H ∈ L¹_loc(μ_W)` on `B`: `μ_W ≤ c μ_V` and `𝓝[B] x ≤ 𝓝[U] x`.
    obtain ⟨G, hG, hHG⟩ := hH.1 x (hBU hx)
    refine ⟨G, nhdsWithin_mono x hBU hG, ?_⟩
    rw [hweight, IntegrableOn, Measure.restrict_smul]
    exact (hHG.mono_measure Measure.restrict_le_self).smul_measure ENNReal.ofReal_ne_top
  · -- First variation: both integrands vanish off `tsupport X ⊆ B`.
    intro X hX hXc hXB
    have h1 : ∫ x in B, W.divM X x ∂V.weight = ∫ x, V.divM X x ∂V.weight := by
      rw [setIntegral_congr_fun hBm fun x hx => hdiv X x hx]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        hdiv0 X x fun h => hx (hXB h)
    have h2 : ∫ x in B, inner ℝ (X x) (H x) ∂V.weight = ∫ x, inner ℝ (X x) (H x) ∂V.weight :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hXB h), inner_zero_left]
    rw [hweight, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hc.le, h1, h2,
      hH.2 X hX hXc (hXB.trans hBU), smul_neg]
  · -- `∫_K |H|ᵖ dμ_W ≤ c ∫_K |H|ᵖ dμ_V < ∞`.
    intro H p hL K hK hKB
    rw [hweight, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt
      (lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl)
      (hL K hK (hKB.trans hBU)))
/-- Translating a rectifiable varifold (used for the translation `τ(x) = x − ξ` in Simon Ch. 5,
7.1–7.3): for `τ(y) = y + x₀`, `v(τ⁻¹M, θ ∘ τ)` is a rectifiable `n`-varifold in `τ⁻¹U`.  `τ` is an
isometry, so it preserves `Hⁿ`; null-measurability, countable rectifiability (via `τ⁻¹M₀` and the
Lipschitz maps `F_j − x₀`), a.e.-measurability of `θ ∘ τ` on `τ⁻¹M` and its integrability on
`τ⁻¹M ∩ K` (through the compact set `τ(K) ⊆ U`) all transfer. -/
theorem rsod_tv_exists_structure : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (x₀ : Amb n ℓ), ∃ W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U), W.carrier = (fun y => y + x₀) ⁻¹' V.carrier ∧ ∀ y, W.mult y = V.mult (y + x₀) := by
  intro n ℓ U V x₀
  -- `τ(y) = y + x₀` is an isometric equivalence, hence `Hⁿ`-measure preserving, and a
  -- measurable embedding.
  have hτ : MeasurePreserving (fun y : Amb n ℓ => y + x₀) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight x₀).measurePreserving_euclideanHausdorffMeasure n
  have hτe : MeasurableEmbedding (fun y : Amb n ℓ => y + x₀) := measurableEmbedding_addRight x₀
  refine ⟨{
    carrier := (fun y => y + x₀) ⁻¹' V.carrier
    mult := fun y => V.mult (y + x₀)
    carrier_subset := preimage_mono V.carrier_subset
    nullMeasurableSet_carrier := V.nullMeasurableSet_carrier.preimage hτ.quasiMeasurePreserving
    countablyRectifiable := ?_
    mult_pos := fun y hy => V.mult_pos (y + x₀) hy
    aemeasurable_mult := ?_
    integrableOn_mult := ?_ }, rfl, fun y => rfl⟩
  · -- Translate the null set `M₀` and the Lipschitz pieces `F j` by `-x₀`.
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := V.countablyRectifiable
    refine ⟨(fun y => y + x₀) ⁻¹' M₀, by rw [hτ.measure_preimage_emb hτe]; exact hM₀,
      fun j z => F j z - x₀, fun j => ?_, fun y hy => ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨K + 0, hK.sub (LipschitzWith.const x₀)⟩
    · rcases hcover hy with h | h
      · exact Or.inl h
      · obtain ⟨j, z, hz⟩ := mem_iUnion.1 h
        exact Or.inr (mem_iUnion.2 ⟨j, z, by simp [hz]⟩)
  · -- `τ` maps `Hⁿ⌞τ⁻¹M` to `Hⁿ⌞M`.
    exact ((hτ.restrict_preimage_emb hτe V.carrier).aemeasurable_comp_iff hτe).2
      V.aemeasurable_mult
  · -- `τ(K)` is a compact subset of `U`, and `τ⁻¹(M ∩ τ(K)) = τ⁻¹M ∩ K`.
    intro K hK hKU
    have h := (hτ.integrableOn_comp_preimage hτe).2 (V.integrableOn_mult
      ((fun y => y + x₀) '' K) (hK.image (continuous_add_const x₀))
      (by rintro _ ⟨k, hk, rfl⟩; exact hKU hk))
    rwa [preimage_inter, hτe.injective.preimage_image] at h
/-- **Weight of a translated varifold** (Simon Ch. 4, 1.1; Ch. 5, proof of Theorem 7.1, p. 127:
"after applying the appropriate translation"; used for Corollary 7.3).  Let `τ(y) = y + x₀` and
`σ(y) = y - x₀`.  If `W = v(τ⁻¹ M, θ ∘ τ)`, then `μ_W = σ_# μ_V`: `τ` preserves `Hⁿ` and is a
measurable embedding, and `τ⁻¹(σ⁻¹A ∩ M) = A ∩ τ⁻¹M`, so for measurable `A`
`μ_W(A) = ∫_{τ⁻¹(σ⁻¹A ∩ M)} θ ∘ τ dHⁿ = ∫_{σ⁻¹A ∩ M} θ dHⁿ = μ_V(σ⁻¹A)`. -/
theorem rsod_tv_weight_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (x₀ : Amb n ℓ),
    W.carrier = (fun y => y + x₀) ⁻¹' V.carrier → (∀ y, W.mult y = V.mult (y + x₀)) →
    W.weight = V.weight.map (fun y => y - x₀) := by
  intro n ℓ U U' V W x₀ hc hm
  -- `τ` is an `Hⁿ`-preserving measurable embedding (an isometry) and `σ` is measurable.
  have hτ : MeasurePreserving (fun y : Amb n ℓ => y + x₀) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight x₀).measurePreserving_euclideanHausdorffMeasure n
  have hτe : MeasurableEmbedding (fun y : Amb n ℓ => y + x₀) := measurableEmbedding_addRight x₀
  have hσ : Measurable (fun y : Amb n ℓ => y - x₀) := measurable_sub_const x₀
  -- It suffices to compare `μ_W(A)` and `(σ_# μ_V)(A) = μ_V(σ⁻¹A)` on measurable sets `A`.
  ext A hA
  -- `τ⁻¹(σ⁻¹A ∩ M) = A ∩ τ⁻¹M = A ∩ W.carrier`.
  have hset : (fun y => y + x₀) ⁻¹' ((fun y => y - x₀) ⁻¹' A ∩ V.carrier) = A ∩ W.carrier := by
    ext y
    simp [hc]
  -- Change of variables along `τ`: `∫_{A ∩ τ⁻¹M} θ ∘ τ dHⁿ = ∫_{σ⁻¹A ∩ M} θ dHⁿ`.
  have key := hτ.setLIntegral_comp_preimage_emb hτe (fun x => ENNReal.ofReal (V.mult x))
    ((fun y => y - x₀) ⁻¹' A ∩ V.carrier)
  rw [hset] at key
  -- Unfold both weights into set integrals; then `W.mult = θ ∘ τ` closes the goal.
  rw [Measure.map_apply hσ hA]
  simp only [RectifiableVarifold.weight]
  rw [withDensity_apply _ hA, withDensity_apply _ (hσ hA), Measure.restrict_restrict hA,
    Measure.restrict_restrict (hσ hA), ← key]
  simp only [hm]
/-- **Support of a translated varifold** (Simon Ch. 5, proof of Theorem 7.1, p. 127: "after
applying the appropriate translation"; used for Corollary 7.3).  Let `τ(y) = y + x₀`.  If `W` is a
rectifiable varifold in `τ⁻¹U` whose weight is the push-forward `μ_W = (· - x₀)_# μ_V`, then
`spt W = τ⁻¹(spt V)`: the translations are continuous and mutually inverse, so the neighbourhoods of
`y` are exactly the `τ`-preimages of the neighbourhoods of `y + x₀`. -/
theorem rsod_tv_support_eq : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U)
    (x₀ : Amb n ℓ) (W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U)),
    W.weight = V.weight.map (fun y => y - x₀) → W.support = (fun y => y + x₀) ⁻¹' V.support := by
  intro n ℓ U V x₀ W hw
  -- `σ = MeasurableEquiv.subRight x₀` is definitionally `y ↦ y - x₀`, so `(σ_# μ)(G) = μ(σ⁻¹G)`
  -- for every set `G`, measurable or not.
  have hσ : (fun y : Amb n ℓ => y - x₀) = ⇑(MeasurableEquiv.subRight x₀) := rfl
  have hσa : ∀ z : Amb n ℓ, MeasurableEquiv.subRight x₀ z = z - x₀ := fun _ => rfl
  -- `spt (σ_# μ_V) = τ⁻¹(spt μ_V)`, using `y ∈ spt μ ↔ ∀ G ∈ 𝓝 y, 0 < μ G`.
  have hsupp : (V.weight.map (fun y => y - x₀)).support =
      (fun y => y + x₀) ⁻¹' V.weight.support := by
    ext y
    rw [hσ, Set.mem_preimage, Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
    constructor
    · -- For `G ∈ 𝓝 (y + x₀)`: `τ⁻¹G ∈ 𝓝 y` and `σ⁻¹(τ⁻¹G) = G`.
      intro h G hG
      have hτG := h _ ((continuous_add_const x₀).continuousAt.preimage_mem_nhds hG)
      have hG' : MeasurableEquiv.subRight x₀ ⁻¹' ((fun z : Amb n ℓ => z + x₀) ⁻¹' G) = G := by
        ext z
        simp only [Set.mem_preimage, hσa, sub_add_cancel]
      rwa [MeasurableEquiv.map_apply, hG'] at hτG
    · -- For `G ∈ 𝓝 y`: `σ⁻¹G ∈ 𝓝 (y + x₀)` since `σ (y + x₀) = y`.
      intro h G hG
      rw [MeasurableEquiv.map_apply]
      refine h _ ((continuous_sub_right x₀).continuousAt.preimage_mem_nhds ?_)
      rwa [add_sub_cancel_right]
  -- `spt W = τ⁻¹U ∩ spt μ_W = τ⁻¹U ∩ τ⁻¹(spt μ_V) = τ⁻¹(U ∩ spt μ_V) = τ⁻¹(spt V)`.
  simp only [RectifiableVarifold.support, hw, hsupp, Set.preimage_inter]
/-- Translation invariance of tangent planes (Simon Ch. 3, 1.7; Ch. 4, 1.3): if
`W = v(τ⁻¹ M, θ ∘ τ)` with `τ(y) = y + x₀`, then `η_{y,r}(τ⁻¹ M) = η_{y + x₀,r}(M)` and the
blown-up multiplicities agree, so the weighted approximate tangent planes of `W` at `y` are those
of `V` at `y + x₀`, and `W`, `V` choose the same tangent projection there. -/
theorem rsod_tv_tangentProj_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (x₀ : Amb n ℓ),
    W.carrier = (fun y => y + x₀) ⁻¹' V.carrier → (∀ y, W.mult y = V.mult (y + x₀)) →
    ∀ y, W.tangentProj y = V.tangentProj (y + x₀) := by
  intro n ℓ U U' V W x₀ hc hm y
  -- `η_{y,r}(τ⁻¹ M) = η_{y + x₀,r}(M)`, since `z - y = (z + x₀) - (y + x₀)`.
  have himg : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap y r '' W.carrier =
      Poincare.SimonGMT.Chapter03.blowUpMap (y + x₀) r '' V.carrier := by
    intro r
    rw [hc]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z + x₀, hz, ?_⟩
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
      congr 1
      abel
    · rintro ⟨m, hm', rfl⟩
      refine ⟨m - x₀, by simpa using hm', ?_⟩
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
      congr 1
      abel
  -- `θ_W(y + r w) = θ((y + x₀) + r w)` and `θ_W(y) = θ(y + x₀)`, so the predicates agree.
  have hadd : ∀ (r : ℝ) (w : Amb n ℓ), y + r • w + x₀ = y + x₀ + r • w := fun r w =>
    add_right_comm y (r • w) x₀
  have key : ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult y P ↔
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
        (y + x₀) P := by
    intro P
    simp only [Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt, himg, hm, hadd]
  -- Hence `W` at `y` and `V` at `y + x₀` choose the same tangent plane.
  have hchoose : ∀ (p q : Submodule ℝ (Amb n ℓ) → Prop) (h₁ : ∃ P, p P) (h₂ : ∃ P, q P),
      p = q → Classical.choose h₁ = Classical.choose h₂ := by
    rintro p q h₁ h₂ rfl
    rfl
  unfold RectifiableVarifold.tangentProj
  by_cases h₁ : ∃ P,
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n W.carrier W.mult y P
  · have h₂ := (exists_congr key).1 h₁
    rw [dite_eq_left h₁, dite_eq_left h₂]
    congr 1
    exact hchoose _ _ h₁ h₂ (funext fun P => propext (key P))
  · have h₂ : ¬∃ P, Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult (y + x₀) P := fun h => h₁ ((exists_congr key).2 h)
    rw [dite_eq_right h₁, dite_eq_right h₂]
/-- **Generalized mean curvature of a translated varifold** (Simon Ch. 4, Definition 3.14; Ch. 5,
proof of Theorem 7.1, p. 127: "after applying the appropriate translation"; used for
Corollary 7.3).  Let `τ(y) = y + x₀` and `σ(y) = y - x₀`.  If `μ_W = σ_# μ_V` and
`p_{T_y W} = p_{T_{y + x₀} V}`, then `W` has generalized mean curvature `H ∘ τ` in `τ⁻¹ U`:
neighbourhoods `G ∈ 𝓝[U] (y + x₀)` pull back to `τ⁻¹ G ∈ 𝓝[τ⁻¹ U] y`, and for
`X ∈ C¹_c(τ⁻¹ U)` the field `X̃ = X ∘ σ ∈ C¹_c(U)` has `div_W X ∘ σ = div_V X̃`, so changing
variables along `σ` turns the first variation of `W` at `X` into that of `V` at `X̃`. -/
theorem rsod_tv_meanCurvature : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U)
    (x₀ : Amb n ℓ) (W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U)),
    W.weight = V.weight.map (fun y => y - x₀) → (∀ y, W.tangentProj y = V.tangentProj (y + x₀)) →
    ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
    W.HasGeneralizedMeanCurvature (fun y => H (y + x₀)) := by
  intro n ℓ U V x₀ W hw hT H hH
  obtain ⟨hHloc, hHfv⟩ := hH
  -- `σ(y) = y - x₀` as a measurable equivalence, so `μ_W = σ_# μ_V`.
  have hw' : W.weight = V.weight.map (MeasurableEquiv.subRight x₀) := hw
  refine ⟨?_, ?_⟩
  · -- Local integrability: transport `G ∈ 𝓝[U] (y + x₀)` to `τ⁻¹ G ∈ 𝓝[τ⁻¹ U] y`.
    intro y hy
    obtain ⟨G, hG, hGi⟩ := hHloc (y + x₀) hy
    refine ⟨(fun z => z + x₀) ⁻¹' G, ?_, ?_⟩
    · exact ((continuous_add_const x₀).continuousWithinAt.tendsto_nhdsWithin
        (mapsTo_preimage _ _)) hG
    · -- `IntegrableOn (H ∘ τ) (τ⁻¹ G) (σ_# μ_V) ↔ IntegrableOn (H ∘ τ ∘ σ) (σ⁻¹ τ⁻¹ G) μ_V`.
      rw [hw', integrableOn_map_equiv]
      have h1 : (fun z => H (z + x₀)) ∘ (MeasurableEquiv.subRight x₀) = H := by
        funext z
        show H (z - x₀ + x₀) = H z
        rw [sub_add_cancel]
      have h2 : (MeasurableEquiv.subRight x₀) ⁻¹' ((fun z => z + x₀) ⁻¹' G) = G := by
        ext z
        show z - x₀ + x₀ ∈ G ↔ z ∈ G
        rw [sub_add_cancel]
      rw [h1, h2]
      exact hGi
  · -- First variation: test `V` with the translated field `X̃(x) = X(x - x₀)`.
    intro X hX hXc hXs
    have hX'c : ContDiff ℝ 1 (fun x => X (x - x₀)) := hX.comp (contDiff_id.sub contDiff_const)
    have hX'cs : HasCompactSupport (fun x => X (x - x₀)) :=
      hXc.comp_homeomorph (IsometryEquiv.subRight x₀).toHomeomorph
    have hX's : tsupport (fun x => X (x - x₀)) ⊆ U := by
      intro x hx
      have h := hXs (tsupport_comp_subset_preimage X (continuous_sub_right x₀) hx)
      simpa using h
    have key := hHfv _ hX'c hX'cs hX's
    -- `div_W X (x - x₀) = div_V X̃ (x)`.
    have hdiv : ∀ x, W.divM X (x - x₀) = V.divM (fun x => X (x - x₀)) x := by
      intro x
      simp only [RectifiableVarifold.divM, hT, sub_add_cancel]
      rw [fderiv_comp_sub]
    -- Change variables along `σ` on both sides and apply the first variation of `V` at `X̃`.
    rw [hw', integral_map_equiv, integral_map_equiv]
    show ∫ x, W.divM X (x - x₀) ∂V.weight = -∫ x, inner ℝ (X (x - x₀)) (H (x - x₀ + x₀)) ∂V.weight
    simp only [hdiv, sub_add_cancel]
    exact key
/-- Translation of local `Lᵖ` bounds (translation step in the proof of Simon Ch. 5, Corollary 7.3,
p. 128).  If `μ_W = σ_# μ_V` for `σ(y) = y − x₀` and `∫_K |H|ᵖ dμ_V < ∞` for every compact
`K ⊆ U`, then `∫_K |H(y + x₀)|ᵖ dμ_W(y) < ∞` for every compact `K ⊆ U − x₀`: restriction and
`lintegral` commute with the push-forward by the measurable equivalence `σ`, so the integral equals
`∫_{σ⁻¹(K)} |H|ᵖ dμ_V`, and `σ⁻¹(K) = K + x₀` is a compact subset of `U`. -/
theorem rsod_tv_locallyLp : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (x₀ : Amb n ℓ) (W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U)), W.weight = V.weight.map (fun y => y - x₀) → ∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ), V.LocallyLp H p → W.LocallyLp (fun y => H (y + x₀)) p := by
  intro n ℓ U V x₀ W hw H p hV K hK hKU
  have hσ : (fun y : Amb n ℓ => y - x₀) = ⇑(MeasurableEquiv.subRight x₀) := rfl
  have hpre : ⇑(MeasurableEquiv.subRight x₀) ⁻¹' K = (fun y => y + x₀) '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨x - x₀, hx, sub_add_cancel x x₀⟩
    · rintro ⟨k, hk, rfl⟩
      show k + x₀ - x₀ ∈ K
      rwa [add_sub_cancel_right]
  have hsub : (fun y => y + x₀) '' K ⊆ U := by
    rintro _ ⟨k, hk, rfl⟩
    exact hKU hk
  -- `∫⁻_K f d(σ_# μ_V) = ∫⁻_{σ⁻¹(K)} f ∘ σ dμ_V`, and `f (σ x) = |H(x − x₀ + x₀)|ᵖ = |H x|ᵖ`.
  rw [hw, hσ, MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  refine lt_of_eq_of_lt (lintegral_congr fun x => ?_)
    (hV _ (hK.image (continuous_add_const x₀)) hsub)
  show ‖H (x - x₀ + x₀)‖ₑ ^ p = ‖H x‖ₑ ^ p
  rw [sub_add_cancel]
/-- **Translation of a rectifiable varifold** (Simon Ch. 5, proof of Theorem 7.1, p. 127: "after
applying the appropriate translation"; used for Corollary 7.3).  For `τ(y) = y + x₀`, the varifold
`W = v(τ⁻¹M, θ ∘ τ)` in `τ⁻¹U` has weight `μ_W = (· - x₀)_# μ_V`, support `spt W = τ⁻¹(spt V)`,
generalized mean curvature `H ∘ τ` whenever `V` has generalized mean curvature `H`, and `H ∘ τ`
is locally in `Lᵖ(μ_W)` whenever `H` is locally in `Lᵖ(μ_V)`. -/
theorem rsod_exists_translated_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (x₀ : Amb n ℓ),
    ∃ W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U),
      W.carrier = (fun y => y + x₀) ⁻¹' V.carrier ∧ (∀ y, W.mult y = V.mult (y + x₀)) ∧
      W.weight = V.weight.map (fun y => y - x₀) ∧
      W.support = (fun y => y + x₀) ⁻¹' V.support ∧
      (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
        W.HasGeneralizedMeanCurvature (fun y => H (y + x₀))) ∧
      (∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ), V.LocallyLp H p →
        W.LocallyLp (fun y => H (y + x₀)) p) := by
  intro n ℓ U V x₀
  -- Step 1: `W = v(τ⁻¹M, θ ∘ τ)` is a rectifiable varifold in `τ⁻¹U`.
  obtain ⟨W, hc, hm⟩ := Submission.rsod_tv_exists_structure n ℓ U V x₀
  -- Step 2: `μ_W = (· - x₀)_# μ_V` by change of variables along `τ`.
  have hw : W.weight = V.weight.map (fun y => y - x₀) :=
    Submission.rsod_tv_weight_eq n ℓ U _ V W x₀ hc hm
  -- Step 4: blow-ups of `τ⁻¹M` at `y` are those of `M` at `y + x₀`, so tangent planes translate.
  have hT : ∀ y, W.tangentProj y = V.tangentProj (y + x₀) :=
    Submission.rsod_tv_tangentProj_eq n ℓ U _ V W x₀ hc hm
  -- Steps 3, 5, 6: the support, the first variation and the local `Lᵖ` bounds transfer along `τ`.
  exact ⟨W, hc, hm, hw, Submission.rsod_tv_support_eq n ℓ U V x₀ W hw,
    Submission.rsod_tv_meanCurvature n ℓ U V x₀ W hw hT,
    Submission.rsod_tv_locallyLp n ℓ U V x₀ W hw⟩
/-- **Allard hypotheses at small scales** (Simon Ch. 5, proof of Theorem 7.1 and Corollary 7.3):
at a point `0 ∈ U` with `Θⁿ(μ_V, 0) = 1`, the hypotheses 5.1 hold for every `δ > 0` at all small
radii `ρ`.  Density one forces `0 ∈ spt μ_V` and `ω_n⁻¹ ρ⁻ⁿ μ_V(B_ρ(0)) < 1 + δ` for small `ρ`,
while `(ρ^{p−n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ (ρ^{p−n} ∫_{B_{ρ₁}(0)} |H|ᵖ dμ_V)^{1/p} → 0`
since `p > n` and `H ∈ Lᵖ_loc`. -/
theorem rsod_allardHypotheses_small_scale : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
    ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) →
    (0 : Amb n ℓ) ∈ U → V.HasDensity 0 1 → ∀ δ : ℝ, 0 < δ →
    ∃ ρ : ℝ, V.AllardHypotheses H p δ ρ := by
  intro n ℓ hn U hU V H p hp hH hLp hmult h0U hdens δ hδ
  -- `ω_n > 0`, so `ω_n rⁿ > 0` for `r > 0`.
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hpos : ∀ r : ℝ, 0 < r → ENNReal.ofReal (unitBallVolume n * r ^ n) ≠ 0 := fun r hr =>
    (ENNReal.ofReal_pos.2 (mul_pos hω (pow_pos hr n))).ne'
  unfold RectifiableVarifold.HasDensity at hdens
  rw [ENNReal.ofReal_one] at hdens
  -- `0 ∈ spt μ_V`: otherwise `μ_V(B_r(0)) = 0` for small `r`, and the density would be `0`.
  have hsupp : (0 : Amb n ℓ) ∈ V.weight.support := by
    by_contra h
    obtain ⟨G, hG, hG0⟩ := Measure.notMem_support_iff_exists.1 h
    obtain ⟨ε, hε, hεG⟩ := nhds_basis_closedBall.mem_iff.1 hG
    have h0 : Tendsto (fun r : ℝ => V.weight (closedBall 0 r) /
        ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hε] with r hr
      rw [measure_mono_null ((closedBall_subset_closedBall hr.2).trans hεG) hG0, ENNReal.zero_div]
    exact zero_ne_one (tendsto_nhds_unique h0 hdens)
  -- A closed ball `B_{ρ₁}(0) ⊆ U`; it is compact, so `∫_{B_{ρ₁}(0)} |H|ᵖ dμ_V < ∞`.
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds h0U)
  have hA := hLp _ (isCompact_closedBall 0 ρ₁) hρ₁U
  -- The mass ratio is eventually `< 1 + δ`.
  have hmass : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      V.weight (closedBall 0 r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + δ) := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
    filter_upwards [hdens.eventually_lt_const h1, self_mem_nhdsWithin] with r hr hr0
    rw [ENNReal.ofReal_mul (by linarith)]
    exact (ENNReal.div_le_iff (hpos r hr0) ENNReal.ofReal_ne_top).1 hr.le
  -- The scaled `Lᵖ` norm is eventually `≤ δ`, since `(r^{p−n} A)^{1/p} → 0` for `p > n`.
  have hlp : ∀ᶠ r in 𝓝[>] (0 : ℝ), V.scaledLpNorm H p 0 r ≤ ENNReal.ofReal δ := by
    have hpn : 0 < p - n := sub_pos.2 hp
    have hp0 : 0 < 1 / p := one_div_pos.2 ((Nat.cast_nonneg n).trans_lt hp)
    have h1 : Tendsto (fun r : ℝ => r ^ (p - n)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (p - n) (Or.inr hpn.le)).tendsto
      rw [Real.zero_rpow hpn.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hA.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    have h3 : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
        ∫⁻ x in closedBall 0 ρ₁, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp h2
      rwa [ENNReal.zero_rpow_of_pos hp0] at this
    filter_upwards [h3.eventually_lt_const (ENNReal.ofReal_pos.2 hδ), Ioc_mem_nhdsGT hρ₁]
      with r hr hrρ
    refine le_trans ?_ hr.le
    unfold RectifiableVarifold.scaledLpNorm
    gcongr
    exact hrρ.2
  -- Any radius in all three eventual sets works.
  obtain ⟨ρ, ⟨hρmass, hρlp⟩, hρ0, hρρ₁⟩ := ((hmass.and hlp).and (Ioc_mem_nhdsGT hρ₁)).exists
  exact ⟨ρ, hρ0, hH, hmult, ⟨h0U, hsupp⟩, (closedBall_subset_closedBall hρρ₁).trans hρ₁U,
    hρmass, hρlp⟩
/-- **Simon Ch. 5, Theorem 7.1, support form** (first paragraph of the printed proof, p. 127):
given Theorem 5.2, a point `x₀ ∈ U` with `Θⁿ(μ_V, x₀) = 1` is a regular point of `V`
(Definition 7.2).  The translate `W` of `V` by `-x₀` has density `1` at `0`, so 5.1 holds for `W`
with `δ = δ₀` at a small scale `ρ`; Theorem 5.2 makes `spt W ∩ B_{γρ}(0)` a rotated `C¹` graph
over `Bⁿ_{γρ}(0)`, hence `B̆_{γρ}(x₀) ∩ spt V` is an `n`-dimensional `C¹` submanifold. -/
theorem rsod_mem_regularSet_of_density_one : AllardRegularityTheorem → ∀ (n ℓ : ℕ), 1 ≤ n →
    ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H →
    V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ x₀ ∈ U, V.HasDensity x₀ 1 →
    x₀ ∈ V.regularSet := by
  intro hAllard n ℓ hn U hU V H p hp hH hLp hθ x₀ hx₀ hdens
  -- Step 1: the constants `δ₀, γ` of Theorem 5.2 for `n, ℓ, p`.
  obtain ⟨δ₀, γ, C, hδ₀, -, hγ, -, hallard⟩ := hAllard n ℓ hn p hp
  -- Steps 2–3: the translate `W` of `V` by `-x₀`, living in the open set `U - x₀ ∋ 0`.
  obtain ⟨W, -, hWmult, hWweight, hWspt, hWH, hWLp⟩ :=
    Submission.rsod_exists_translated_varifold n ℓ U V x₀
  have hU' : IsOpen ((fun y => y + x₀) ⁻¹' U) := hU.preimage (continuous_id.add_const x₀)
  have h0U' : (0 : Amb n ℓ) ∈ (fun y => y + x₀) ⁻¹' U := by simpa using hx₀
  -- Step 4: `μ_W(B_r(0)) = μ_V(B_r(x₀))`, so `Θⁿ(μ_W, 0) = Θⁿ(μ_V, x₀) = 1`.
  have hball (r : ℝ) : W.weight (closedBall 0 r) = V.weight (closedBall x₀ r) := by
    rw [hWweight, (measurableEmbedding_subRight x₀).map_apply]
    congr 1
    ext y
    simp [dist_eq_norm]
  have hWdens : W.HasDensity 0 1 := by
    unfold RectifiableVarifold.HasDensity at hdens ⊢
    simpa only [hball] using hdens
  -- Step 5: `θ_W ≥ 1` `μ_W`-a.e., since `θ_W(x - x₀) = θ_V(x)`.
  have hWθ : ∀ᵐ y ∂W.weight, 1 ≤ W.mult y := by
    rw [hWweight, (measurableEmbedding_subRight x₀).ae_map_iff]
    filter_upwards [hθ] with x hx
    rwa [hWmult, sub_add_cancel]
  -- Step 6: the hypotheses 5.1 for `W` with `δ = δ₀` at some scale `ρ`.
  obtain ⟨ρ, hρ⟩ := Submission.rsod_allardHypotheses_small_scale n ℓ hn _ hU' W
    (fun y => H (y + x₀)) p hp (hWH H hH) (hWLp H p hLp) hWθ h0U' hWdens δ₀ hδ₀
  -- Step 7: Theorem 5.2 for `W`: `spt W ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`, `u ∈ C¹`.
  obtain ⟨q, u, hu, -, -, hgraph, -⟩ := hallard _ hU' W _ δ₀ ρ hδ₀ le_rfl hρ
  obtain ⟨hρ, -, -, h0W, -⟩ := hρ
  rw [hWspt] at hgraph h0W
  -- Steps 8–9: `x₀ = 0 + x₀ ∈ spt V`, and `B̆_{γρ}(x₀) ∩ spt V` is an `n`-dimensional `C¹`
  -- submanifold by the graph lemma.
  refine ⟨by simpa using h0W, γ * ρ, mul_pos hγ hρ, ?_⟩
  exact Submission.rsod_isC1Submanifold_ball_inter_graph n ℓ q u x₀ (γ * ρ) V.support
    (mul_pos hγ hρ) hu hgraph
/-- **Simon Ch. 1, Theorem 1.17 (Lusin), as used in Ch. 3, Remark 1.8(1)**: a Borel set `A` with
`Hⁿ(A) < ∞` is, up to an `Hⁿ`-null set, a countable union of closed sets `C i ⊆ A` on each of which
the Borel function `ϑ` is continuous.  Proof: Lusin's theorem is proved inline (SimonGMT's
`Chapter01` Lusin theorem is not in the frozen import closure) for the finite, hence weakly regular,
measure `ν = Hⁿ ⌞ A`: for each rational interval `I_q` take closed `F_q ⊆ A ∩ ϑ⁻¹(I_q)` and
`F'_q ⊆ A \ ϑ⁻¹(I_q)` with `ν(A \ (F_q ∪ F'_q)) ≤ δ_q`, `∑ δ_q < 1/m`; `ϑ` is continuous on
`C m = ⋂_q (F_q ∪ F'_q)` and `Hⁿ(A \ C m) < 1/m`, so `Hⁿ(A \ ⋃ C m) = 0`. -/
theorem rsod_wfu_lusin_closed_exhaustion : ∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Measurable ϑ → ∃ C : ℕ → Set (Amb n ℓ), (∀ i, IsClosed (C i) ∧ C i ⊆ A ∧ ContinuousOn ϑ (C i)) ∧ (μHE[n] : Measure (Amb n ℓ)) (A \ ⋃ i, C i) = 0 := by
  intro n ℓ A ϑ hA hAfin hϑ
  -- Lusin's theorem (Simon 1.17) for `ϑ` on `A` and a finite Borel measure.
  have lusin : ∀ (ν : Measure (Amb n ℓ)), IsFiniteMeasure ν → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε ∧ ContinuousOn ϑ C := by
    intro ν hν ε hε
    have : ν.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
    obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × ℚ)
    -- For each rational interval, closed sets inside the parts of `A` where `ϑ` is in / not in it.
    have hsplit : ∀ q : ℚ × ℚ, ∃ F ⊆ A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F ∧
        ∃ F' ⊆ A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F' ∧ ν (A \ (F ∪ F')) ≤ δ q := by
      intro q
      have hP : MeasurableSet (A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.inter (hϑ measurableSet_Ioo)
      have hN : MeasurableSet (A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.diff (hϑ measurableSet_Ioo)
      have hδ2 : (δ q : ℝ≥0∞) / 2 ≠ 0 :=
        (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos q).ne')).ne'
      obtain ⟨F, hFP, hFc, hF⟩ := hP.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      obtain ⟨F', hFN, hF'c, hF'⟩ := hN.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      refine ⟨F, hFP, hFc, F', hFN, hF'c, ?_⟩
      calc ν (A \ (F ∪ F'))
          ≤ ν ((A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F ∪ (A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') := by
            refine measure_mono fun x hx => ?_
            by_cases hϑx : ϑ x ∈ Ioo (q.1 : ℝ) q.2
            · exact Or.inl ⟨⟨hx.1, hϑx⟩, fun h => hx.2 (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hϑx⟩, fun h => hx.2 (Or.inr h)⟩
        _ ≤ ν ((A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F) + ν ((A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') :=
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
      obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show ϑ x - e < ϑ x by linarith)
      obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show ϑ x < ϑ x + e by linarith)
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
  -- Closed `C m ⊆ A` with `ϑ` continuous on `C m` and `Hⁿ(A \ C m) < 1/m`, from `ν = Hⁿ ⌞ A`.
  have hC : ∀ m : ℕ, ∃ C ⊆ A, IsClosed C ∧
      (μHE[n] : Measure (Amb n ℓ)) (A \ C) < (m : ℝ≥0∞)⁻¹ ∧ ContinuousOn ϑ C := by
    intro m
    obtain ⟨C, hCA, hCc, hCμ, hCf⟩ := lusin ((μHE[n] : Measure (Amb n ℓ)).restrict A)
      (isFiniteMeasure_restrict.2 hAfin.ne) (m : ℝ≥0∞)⁻¹
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    refine ⟨C, hCA, hCc, ?_, hCf⟩
    rwa [Measure.restrict_apply (hA.diff hCc.measurableSet), inter_eq_left.2 sdiff_subset] at hCμ
  choose C hCA hCc hCμ hCf using hC
  refine ⟨C, fun i => ⟨hCc i, hCA i, hCf i⟩, ?_⟩
  by_contra h
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h
  exact lt_asymm hm ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion C m))).trans_lt (hCμ m))
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
/-- **Simon Ch. 3, Remark 1.8(2)** for `V = v(M, θ)`.  If `P` is the approximate tangent space of
`M` at `x ∈ U` with respect to `θ` (Ch. 3, Definition 1.7), then `Θⁿ(μ_V, x) = θ(x)`.  Indeed
`r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ → ω_n θ(x)` as `r ↓ 0`, and `μ_V(B_r(x)) = ∫_{M ∩ B_r(x)} θ dHⁿ` as soon
as `B_r(x) ⊆ U`, so `μ_V(B_r(x)) / (ω_n rⁿ) → θ(x)`. -/
theorem rsod_hasDensity_of_approxTangent : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), x ∈ U → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P → V.HasDensity x (V.mult x) := by
  intro n ℓ hn U hU V x P hx hP
  -- `ω_n = π^{n/2} / Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- `B̆_d(x) ⊆ U` for some `d > 0`.
  obtain ⟨d, hd, hdU⟩ := Metric.isOpen_iff.1 hU x hx
  -- `J(r) := r⁻ⁿ ∫_{M ∩ B_r(x)} θ dHⁿ → ω_n θ(x)`, hence `ofReal (J(r) / ω_n) → ofReal θ(x)`.
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹ *
      (∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) /
        unitBallVolume n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (V.mult x))) := by
    have hJ := (Submission.rsod_tendsto_scaled_mult_integral n ℓ hn U hU V x P hx hP).div_const
      (unitBallVolume n)
    rw [mul_div_cancel_left₀ _ hω.ne'] at hJ
    exact ENNReal.tendsto_ofReal hJ
  -- For `0 < r < d`, `B_r(x) ⊆ U`, so `μ_V(B_r(x)) / (ω_n rⁿ) = ofReal (J(r) / ω_n)`.
  have heq : ∀ r ∈ Ioo (0 : ℝ) d,
      ENNReal.ofReal ((r ^ n)⁻¹ *
          (∫ z in V.carrier ∩ closedBall x r, V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) /
            unitBallVolume n) =
        V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n) := by
    intro r hr
    rw [Submission.rsod_weight_closedBall_eq_ofReal_integral n ℓ U V x r
        ((closedBall_subset_ball hr.2).trans hdU),
      ← ENNReal.ofReal_div_of_pos (mul_pos hω (pow_pos hr.1 n))]
    congr 1
    ring
  unfold RectifiableVarifold.HasDensity
  exact hlim.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsGT hd) heq)

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
/-- **Ball-mass bound at an approximate tangent plane** (Simon Ch. 3, Remark 1.5(3)).  If
`Hⁿ(C) < ∞` and `T_x C = P`, then for each `R > 0` the ratios `r⁻ⁿ Hⁿ(C ∩ B_{rR}(x))` are
eventually bounded as `r ↓ 0`: test Definition 1.4 against a cutoff `g ∈ C_c` with `0 ≤ g ≤ 1`
and `g = 1` on `B_R(0)`, and pull `∫_{η(C)} g dHⁿ` back to `C` by the blow-up change of
variables. -/
theorem rsod_wfu_approxTangent_ballMass_bound : ∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) C < ∞ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → ∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ := by
  intro n ℓ C x P hC hT R _
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  -- The cutoff `g(y) = max(0, min(1, R + 1 - ‖y‖))`: continuous, `0 ≤ g ≤ 1`, `g = 1` on
  -- `B_R(0)` and `g = 0` off the compact ball `B_{R+1}(0)`.
  obtain ⟨g, hg_cont, hg_supp, hg_nonneg, hg_le_one, hg_one⟩ : ∃ g : Amb n ℓ → ℝ,
      Continuous g ∧ HasCompactSupport g ∧ (∀ y, 0 ≤ g y) ∧ (∀ y, g y ≤ 1) ∧
        ∀ y, ‖y‖ ≤ R → g y = 1 := by
    refine ⟨fun y => max 0 (min 1 (R + 1 - ‖y‖)),
      continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm)),
      HasCompactSupport.intro (isCompact_closedBall (0 : Amb n ℓ) (R + 1)) fun y hy => ?_,
      fun y => le_max_left _ _, fun y => max_le zero_le_one (min_le_left _ _), fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact max_eq_left ((min_le_right _ _).trans (by linarith))
    · show max 0 (min 1 (R + 1 - ‖y‖)) = 1
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- `T_x C = P` tested on `g`: eventually `∫_{η_r(C)} g dHⁿ < ∫_P g dHⁿ + 1`.
  have hlim : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' C, g y ∂μ)
      (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), g y ∂μ)) :=
    hT.2 ⟨⟨g, hg_cont⟩, hg_supp⟩
  refine ⟨(∫ y in (P : Set (Amb n ℓ)), g y ∂μ) + 1, ?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one _)), self_mem_nhdsWithin]
    with r hr (hr0 : 0 < r)
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  -- Change of variables with `θ ≡ 1`: `∫_{η(C)} g dHⁿ = r⁻ⁿ ∫_C g ∘ η dHⁿ`.
  have hcov := rsod_blowUp_setIntegral_eq n ℓ C g (fun _ => 1) x r hr0
  simp only [mul_one] at hcov
  -- `1_B ≤ g ∘ η` for `B = B_{rR}(x)`, since `‖η z‖ = r⁻¹ ‖z - x‖ ≤ R` on `B`.
  have hB : MeasurableSet (closedBall x (r * R)) := measurableSet_closedBall
  have hle : ∀ z, (closedBall x (r * R)).indicator 1 z ≤ g (η z) := by
    intro z
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz, Pi.one_apply, hg_one]
      rw [hη, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), ← dist_eq_norm]
      calc r⁻¹ * dist z x ≤ r⁻¹ * (r * R) :=
            mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) (inv_nonneg.mpr hr0.le)
        _ = R := inv_mul_cancel_left₀ hr0.ne' R
    · rw [indicator_of_notMem hz]
      exact hg_nonneg _
  -- Both sides are `Hⁿ ⌞ C`-integrable because `Hⁿ(C) < ∞`, so `Hⁿ(C ∩ B) ≤ ∫_C g ∘ η dHⁿ`.
  have hmass : μ.real (C ∩ closedBall x (r * R)) ≤ ∫ z in C, g (η z) ∂μ := by
    have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.ne
    have hηcont : Continuous η := (continuous_id.sub continuous_const).const_smul r⁻¹
    have h1 : Integrable ((closedBall x (r * R)).indicator (1 : Amb n ℓ → ℝ)) (μ.restrict C) :=
      (integrable_const (1 : ℝ)).indicator hB
    have h2 : Integrable (fun z => g (η z)) (μ.restrict C) :=
      (integrable_const (1 : ℝ)).mono' (hg_cont.comp hηcont).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_of_nonneg (hg_nonneg _)]; exact hg_le_one _)
    calc μ.real (C ∩ closedBall x (r * R))
        = ∫ z in C, (closedBall x (r * R)).indicator 1 z ∂μ := by
          rw [integral_indicator_one hB, measureReal_restrict_apply hB, inter_comm]
      _ ≤ ∫ z in C, g (η z) ∂μ := integral_mono h1 h2 hle
  calc (r ^ n)⁻¹ * μ.real (C ∩ closedBall x (r * R))
      ≤ (r ^ n)⁻¹ * ∫ z in C, g (η z) ∂μ :=
        mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr (pow_nonneg hr0.le n))
    _ = ∫ y in η '' C, g y ∂μ := hcov.symm
    _ ≤ (∫ y in (P : Set (Amb n ℓ)), g y ∂μ) + 1 := hr.le
/-- **Vanishing of the blow-up tail** (Simon Ch. 3, Remark 1.8(1), with Ch. 1, Thm 3.6).  If the
weighted measure `μ' = |ϑ| Hⁿ ⌞ A` satisfies `ρ⁻ⁿ μ'(S ∩ B_ρ(x)) → 0` as `ρ ↓ 0`, with `S ⊆ A` Borel
and `ϑ ∈ L¹(Hⁿ ⌞ A)`, then `r⁻ⁿ ∫_S f(η_{x,r} z) ϑ(z) dHⁿ(z) → 0` for every `f ∈ C_c`.  Indeed
`|f| ≤ M` and `f = 0` off `B_R(0)`, so the integral is bounded by `M μ'(S ∩ B_{rR}(x))`, and
`r⁻ⁿ M μ'(S ∩ B_{rR}(x)) = M Rⁿ (rR)⁻ⁿ μ'(S ∩ B_{rR}(x)) → 0`. -/
theorem rsod_wfu_blowUp_tail_tendsto_zero : ∀ (n ℓ : ℕ) (A S : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet S → S ⊆ A → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real (S ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ A S ϑ x hS hSA hϑ hdens f
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set μ' : Measure (Amb n ℓ) := (μ.restrict A).withDensity (fun z => ‖ϑ z‖ₑ) with hμ'
  -- `|f| ≤ M` everywhere, and `f = 0` off `B_R(0)` with `R > 0`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ y, ‖f y‖ ≤ M :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  set R : ℝ := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- `μ'(T) = ∫_T |ϑ| dHⁿ` for Borel `T ⊆ A`.
  have hreal : ∀ T : Set (Amb n ℓ), MeasurableSet T → T ⊆ A →
      ∫ z in T, ‖ϑ z‖ ∂μ = μ'.real T := by
    intro T hT hTA
    rw [measureReal_def, hμ', withDensity_apply _ hT, Measure.restrict_restrict hT,
      inter_eq_left.mpr hTA,
      integral_norm_eq_lintegral_enorm (hϑ.mono_set hTA).aestronglyMeasurable]
  -- Pointwise: `|f(η_r z) ϑ(z)| ≤ M 1_{B_{rR}(x)}(z) |ϑ(z)|`.
  have hpt : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ,
      ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z‖ ≤
        (closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖) z := by
    intro r hr z
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [indicator_of_notMem hz]
      have hf0 : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hz
        have h1 := hR₀ hmem
        rw [mem_closedBall_zero_iff] at h1
        rw [mem_closedBall, dist_eq_norm]
        have hzx : z - x = r • Poincare.SimonGMT.Chapter03.blowUpMap x r z := by
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
        calc r * ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ r * R₀ :=
              mul_le_mul_of_nonneg_left h1 hr.le
          _ ≤ r * R := mul_le_mul_of_nonneg_left (le_max_left _ _) hr.le
      rw [hf0, zero_mul, norm_zero]
  -- Integral bound: `|∫_S f(η_r z) ϑ(z) dHⁿ| ≤ M μ'(S ∩ B_{rR}(x))`.
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖ ≤
        M * μ'.real (S ∩ closedBall x (r * R)) := by
    intro r hr
    have hint : Integrable ((closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖))
        (μ.restrict S) :=
      ((hϑ.mono_set hSA).norm.const_mul M).indicator measurableSet_closedBall
    calc ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖
        ≤ ∫ z in S, (closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖) z ∂μ :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall (hpt r hr))
      _ = ∫ z in S ∩ closedBall x (r * R), M * ‖ϑ z‖ ∂μ :=
          setIntegral_indicator measurableSet_closedBall
      _ = M * ∫ z in S ∩ closedBall x (r * R), ‖ϑ z‖ ∂μ := integral_const_mul _ _
      _ = M * μ'.real (S ∩ closedBall x (r * R)) := by
          rw [hreal _ (hS.inter measurableSet_closedBall) (inter_subset_left.trans hSA)]
  -- Rescaling `ρ = rR` turns the density hypothesis into the decay of the bound.
  have hscale : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hlim := (hdens.comp hscale).const_mul (M * R ^ n)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hRn : R ^ n ≠ 0 := pow_ne_zero _ hRpos.ne'
  rw [norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hr.le]
  calc (r ^ n)⁻¹ * ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖
      ≤ (r ^ n)⁻¹ * (M * μ'.real (S ∩ closedBall x (r * R))) :=
        mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)
    _ = M * R ^ n * (((r * R) ^ n)⁻¹ * μ'.real (S ∩ closedBall x (r * R))) := by
        rw [mul_pow, mul_inv]
        field_simp
/-- **Freezing a relatively continuous weight in blow-ups** (Simon Ch. 3, Remark 1.8(1)).  Let `C`
be Borel with `Hⁿ(C) < ∞`, `ϑ` continuous at `x` relative to `C`, and `r⁻ⁿ Hⁿ(C ∩ B_{rR}(x))`
eventually bounded as `r ↓ 0` for each `R > 0`.  Then for `f ∈ C_c` and `η = η_{x,r}`,
`r⁻ⁿ ∫_C f(η z) (ϑ(z) − ϑ(x)) dHⁿ(z) → 0` as `r ↓ 0`.  With `|f| ≤ M` and `spt f ⊆ B_R(0)`, the
integrand vanishes off `B_{rR}(x)` and is at most `M ε'` on `C ∩ B_{rR}(x)` once `rR < δ`, so the
quantity is at most `M ε' Λ`. -/
theorem rsod_wfu_blowUp_freeze_weight_tendsto_zero : ∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet C → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → ContinuousWithinAt ϑ C x → (∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ C ϑ x hC hCfin hϑ hdens f
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  -- `|f| ≤ M`, and `f` vanishes outside `B_R(0)` with `R ≥ 1`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ y, ‖f y‖ ≤ M :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  set R := max R₀ 1
  have hR : 0 < R := lt_max_of_lt_right one_pos
  have hfR : ∀ y : Amb n ℓ, R < ‖y‖ → f y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hy' => ?_
    have := hR₀ hy'
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R₀ 1]
  -- Bounded density ratio at scale `R`.
  obtain ⟨Λ, hΛ⟩ := hdens R hR
  set Λ' := max Λ 0
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hCfin.ne
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / ((M + 1) * (Λ' + 1)) with hε'eq
  have hMΛ : 0 < (M + 1) * (Λ' + 1) := mul_pos (by linarith) (by linarith)
  have hε' : 0 < ε' := div_pos hε hMΛ
  obtain ⟨δ, hδ, hδϑ⟩ := Metric.continuousWithinAt_iff.mp hϑ ε' hε'
  filter_upwards [hΛ, Ioo_mem_nhdsGT (div_pos hδ hR)] with r hrΛ hr
  obtain ⟨hr0, hrδ⟩ := hr
  have hrRδ : r * R < δ := by rwa [lt_div_iff₀ hR] at hrδ
  -- Pointwise bound on `C` by `M ε'` times the indicator of `B_{rR}(x)`.
  have hpt : ∀ z ∈ C, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x)‖ ≤
      (closedBall x (r * R)).indicator (fun _ => M * ε') z := by
    intro z hz
    by_cases hzB : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hzB, norm_mul]
      have h2 : ‖ϑ z - ϑ x‖ ≤ ε' := by
        rw [← dist_eq_norm]
        exact (hδϑ hz (lt_of_le_of_lt (mem_closedBall.mp hzB) hrRδ)).le
      exact mul_le_mul (hM _) h2 (norm_nonneg _) hM0
    · rw [indicator_of_notMem hzB]
      have hf0 : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
        apply hfR
        rw [mem_closedBall, not_le] at hzB
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
          ← dist_eq_norm, lt_inv_mul_iff₀ hr0]
        exact hzB
      simp [hf0]
  -- Integral bound.
  have hint : ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖ ≤
      M * ε' * μ.real (C ∩ closedBall x (r * R)) := by
    calc ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖
        ≤ ∫ z in C, (closedBall x (r * R)).indicator (fun _ => M * ε') z ∂μ :=
          norm_integral_le_of_norm_le ((integrable_const _).indicator measurableSet_closedBall)
            (ae_restrict_of_forall_mem hC hpt)
      _ = M * ε' * μ.real (C ∩ closedBall x (r * R)) := by
          rw [integral_indicator_const _ measurableSet_closedBall,
            measureReal_restrict_apply measurableSet_closedBall, smul_eq_mul, mul_comm, inter_comm]
  -- Conclusion: `|E(r)| ≤ M ε' Λ' < ε`.
  have hrn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.mpr (pow_nonneg hr0.le n)
  rw [dist_zero_right, norm_mul, Real.norm_of_nonneg hrn]
  calc (r ^ n)⁻¹ * ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖
      ≤ (r ^ n)⁻¹ * (M * ε' * μ.real (C ∩ closedBall x (r * R))) :=
        mul_le_mul_of_nonneg_left hint hrn
    _ = M * ε' * ((r ^ n)⁻¹ * μ.real (C ∩ closedBall x (r * R))) := by ring
    _ ≤ M * ε' * Λ' :=
        mul_le_mul_of_nonneg_left (hrΛ.trans (le_max_left _ _)) (mul_nonneg hM0 hε'.le)
    _ < (M + 1) * (Λ' + 1) * ε' := by nlinarith
    _ = ε := by rw [hε'eq]; field_simp
/-- **Weighted tangent space from a good piece** (Simon Ch. 3, Remark 1.8(1)).  Let `A` be Borel
with `Hⁿ(A) < ∞`, `ϑ` integrable on `A`, and `C ⊆ A` Borel with `ϑ|C` continuous at `x`.  If
`T_x C = P` (Def. 1.4) and `ρ⁻ⁿ ∫_{(A \ C) ∩ B_ρ(x)} |ϑ| dHⁿ → 0` as `ρ ↓ 0`, then `T_x A = P` with
respect to `ϑ` (Def. 1.7).  For `f ∈ C_c`, `r > 0` and `G = f ∘ η_{x,r}`, the change of variables
gives `∫_{η(A)} f(y) ϑ(x + r y) dHⁿ(y)
  = ϑ(x) ∫_{η(C)} f dHⁿ + r⁻ⁿ ∫_C G (ϑ − ϑ(x)) dHⁿ + r⁻ⁿ ∫_{A \ C} G ϑ dHⁿ`,
and the three terms tend to `ϑ(x) ∫_P f dHⁿ`, `0` and `0`. -/
theorem rsod_wfu_weightedApproxTangent_of_closed_piece : ∀ (n ℓ : ℕ) (A C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → MeasurableSet C → C ⊆ A → ContinuousWithinAt ϑ C x → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real ((A \ C) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P := by
  intro n ℓ A C ϑ x P hA hAfin hϑ hC hCA hϑC hT htail
  -- `Hⁿ(C) ≤ Hⁿ(A) < ∞`.
  have hCfin : (μHE[n] : Measure (Amb n ℓ)) C < ∞ := (measure_mono hCA).trans_lt hAfin
  -- `finrank P = n` is part of `T_x C = P`; fix `f ∈ C_c`.
  refine ⟨hT.1, fun f => ?_⟩
  -- The three limits: `ϑ(x) ∫_{η(C)} f → ϑ(x) ∫_P f` as `T_x C = P`; the frozen-weight error on `C`
  -- tends to `0`, fed by the ball-mass bound for `C`; and so does the tail on `A \ C`.
  have hlim := (((hT.2 f).const_mul (ϑ x)).add
    (Submission.rsod_wfu_blowUp_freeze_weight_tendsto_zero n ℓ C ϑ x hC hCfin hϑC
      (Submission.rsod_wfu_approxTangent_ballMass_bound n ℓ C x P hCfin hT) f)).add
    (Submission.rsod_wfu_blowUp_tail_tendsto_zero n ℓ A (A \ C) ϑ x (hA.diff hC) sdiff_subset
      hϑ htail f)
  rw [add_zero, add_zero] at hlim
  -- It remains to prove the identity for every `r > 0`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `G = f ∘ η` is continuous and bounded, so `G ϑ` is integrable on `A` and `G` on `C`.
  have hGc : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) := by
    refine (map_continuous f).comp ?_
    show Continuous fun z : Amb n ℓ => r⁻¹ • (z - x)
    fun_prop
  obtain ⟨M, hM⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hGϑ : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z) A
      (μHE[n] : Measure (Amb n ℓ)) :=
    hϑ.bdd_mul hGc.aestronglyMeasurable (Eventually.of_forall fun z => hM _)
  have hG : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) C
      (μHE[n] : Measure (Amb n ℓ)) :=
    IntegrableOn.of_bound hCfin hGc.aestronglyMeasurable M (Eventually.of_forall fun z => hM _)
  -- Change of variables, with weight `ϑ` on `A` and weight `1` on `C`.
  have hI := Submission.rsod_blowUp_setIntegral_eq n ℓ A f ϑ x r hr
  have hTC := Submission.rsod_blowUp_setIntegral_eq n ℓ C f (fun _ => 1) x r hr
  simp only [mul_one] at hTC
  -- `∫_A = ∫_C + ∫_{A \ C}`, and `ϑ(x)` comes out of the frozen-weight integral.
  have hsplit : ∫ z in A, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
      ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) +
      ∫ z in A \ C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
    rw [← integral_inter_add_sdiff hC hGϑ, inter_eq_right.mpr hCA]
  have hfreeze : ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x)
      ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) -
      (∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))) *
        ϑ x := by
    rw [← integral_mul_const, ← integral_sub (hGϑ.mono_set hCA) (hG.mul_const (ϑ x))]
    simp_rw [mul_sub]
  rw [hI, hTC, hsplit, hfreeze]
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
/-- **Approximate tangent spaces a.e. on a set covered by `C¹` submanifolds** (Simon Ch. 3,
Remark 1.3 and the proof of Theorem 1.6 "⇒", which also gives Remark 1.5(2)).  Let `n ≥ 1`, `C`
Borel with `Hⁿ(C) < ∞`, `Hⁿ(Z) = 0`, and `C ⊆ Z ∪ ⋃_k N_k` with each `N_k` an `n`-dimensional `C¹`
submanifold with `Hⁿ(N_k) < ∞`.  Then `T_x C` exists for `Hⁿ`-a.e. `x ∈ C`.
(1) (1.3) Each `N_k` is Borel, so `C_k := (C ∩ N_k) \ ⋃_{i<k} N_i ⊆ C ∩ N_k` is Borel, and each
`x ∈ C \ Z` lies in `C_k` for the least `k` with `x ∈ N_k`.
(2) (Upper Density Theorem, Ch. 1, 3.6) Off an `Hⁿ`-null set `E_k`, every `x ∈ C_k` has
`ρ⁻ⁿ Hⁿ((C \ C_k) ∩ B_ρ(x)) → 0` and `ρ⁻ⁿ Hⁿ((N_k \ C_k) ∩ B_ρ(x)) → 0` as `ρ ↓ 0`.
(3) At such `x`, `T_x N_k = P` exists as `N_k` is a `C¹` submanifold, and `T_x C = P` since `C` and
`N_k` differ from `C_k` by sets of zero `n`-density at `x`.  The exceptional set lies in
`Z ∪ ⋃_k E_k`, which is `Hⁿ`-null. -/
theorem rsod_ae_approxTangent_of_c1Cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (C Z : Set (Amb n ℓ)) (N : ℕ → Set (Amb n ℓ)), MeasurableSet C → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → (μHE[n] : Measure (Amb n ℓ)) Z = 0 → (∀ k, IsC1Submanifold n (N k) ∧ (μHE[n] : Measure (Amb n ℓ)) (N k) < ∞) → C ⊆ Z ∪ ⋃ k, N k → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ C → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P := by
  intro n ℓ hn C Z N hC hCfin hZ hN hcov
  -- Step 1 (Remark 1.3): the Borel pieces `C_k = (C ∩ N_k) \ ⋃_{i<k} N_i`.
  have hNm : ∀ k, MeasurableSet (N k) := fun k =>
    Submission.rsod_isC1Submanifold_measurableSet n (n + ℓ) (N k) (hN k).1
  set D : ℕ → Set (Amb n ℓ) := fun k => (C ∩ N k) \ ⋃ i < k, N i
  have hDm : ∀ k, MeasurableSet (D k) := fun k =>
    (hC.inter (hNm k)).diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hNm i)
  -- Step 2 (Upper Density Theorem): `C \ C_k` and `N_k \ C_k` have zero `n`-density at
  -- `Hⁿ`-a.e. point outside them.
  have hdC : ∀ k, ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∉ C \ D k →
      Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ *
        (μHE[n] : Measure (Amb n ℓ)).real ((C \ D k) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) :=
    fun k => Submission.rsod_ae_tendsto_density_zero_outside n ℓ (μHE[n] : Measure (Amb n ℓ))
      (C \ D k) (hC.diff (hDm k)) ((measure_mono sdiff_subset).trans_lt hCfin)
  have hdN : ∀ k, ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∉ N k \ D k →
      Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ *
        (μHE[n] : Measure (Amb n ℓ)).real ((N k \ D k) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) :=
    fun k => Submission.rsod_ae_tendsto_density_zero_outside n ℓ (μHE[n] : Measure (Amb n ℓ))
      (N k \ D k) ((hNm k).diff (hDm k)) ((measure_mono sdiff_subset).trans_lt (hN k).2)
  -- Step 3: off `Z ∪ ⋃_k E_k`, each `x ∈ C` lies in `C_k` for the least `k` with `x ∈ N_k`.
  filter_upwards [ae_all_iff.2 hdC, ae_all_iff.2 hdN, measure_eq_zero_iff_ae_notMem.1 hZ]
    with x hxC' hxN' hxZ hxC
  have hex : ∃ k, x ∈ N k := by
    rcases hcov hxC with h | h
    · exact absurd h hxZ
    · exact mem_iUnion.1 h
  classical
  obtain ⟨k, hxk, hmin⟩ : ∃ k, x ∈ N k ∧ ∀ i < k, x ∉ N i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hxD : x ∈ D k := ⟨⟨hxC, hxk⟩, fun h => by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 h
    exact hmin i hi hxi⟩
  -- Step 4: `T_x N_k = P` (a `C¹` submanifold) transfers to `T_x C = P` (Remark 1.5(2)).
  obtain ⟨P, hP⟩ := Submission.rsod_isC1Submanifold_approxTangent n (n + ℓ) hn (N k) (hN k).1 x hxk
  exact ⟨P, Submission.rsod_approxTangent_transfer n ℓ C (N k) (D k) x P (hDm k)
    (fun y hy => hy.1.1) (fun y hy => hy.1.2) hCfin (hN k).2 (hxC' k fun h => h.2 hxD)
    (hxN' k fun h => h.2 hxD) hP⟩
/-- **Weighted approximate tangent spaces from unweighted ones** (Simon, *Introduction to GMT*,
Ch. 3, Remark 1.8(1)).  Let `A` be a Borel set with `Hⁿ(A) < ∞` and `ϑ` Borel and `Hⁿ`-integrable
on `A`.  If for every closed `K ⊆ A`, `Hⁿ`-a.e. `x ∈ K` has an approximate tangent space of `K`
(Def. 1.4), then `Hⁿ`-a.e. `x ∈ A` has an approximate tangent space of `A` with respect to `ϑ`
(Def. 1.7).
(1) (Lusin, Ch. 1, 1.17) There are closed `C_i ⊆ A` with `ϑ` continuous on `C_i` and
`Hⁿ(A \ ⋃ C_i) = 0`.
(2) `μ' = |ϑ| Hⁿ ⌞ A` is finite, so by the Upper Density Theorem (Ch. 1, 3.6)
`ρ⁻ⁿ μ'((A \ C_i) ∩ B_ρ(x)) → 0` for `Hⁿ`-a.e. `x ∉ A \ C_i`; by hypothesis, `Hⁿ`-a.e. `x ∈ C_i`
has an approximate tangent space `T_x C_i = P`.
(3) Off the countable union of these null sets and of `A \ ⋃ C_i`, each `x ∈ A` lies in some
`C_i`, and there `T_x C_i` is the approximate tangent space of `A` at `x` with respect to `ϑ`. -/
theorem rsod_ae_weightedApproxTangent_of_unweighted : ∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Measurable ϑ → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → (∀ K : Set (Amb n ℓ), IsClosed K → K ⊆ A → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ K → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n K x P) → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ A → ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P := by
  intro n ℓ A ϑ hA hAfin hϑ hint hK
  -- Step 1 (Lusin): closed `C i ⊆ A` with `ϑ` continuous on `C i` and `Hⁿ(A \ ⋃ C i) = 0`.
  obtain ⟨C, hC, hnull⟩ := Submission.rsod_wfu_lusin_closed_exhaustion n ℓ A ϑ hA hAfin hϑ
  -- Step 2: `μ' = |ϑ| Hⁿ ⌞ A` is a finite measure, since `ϑ` is integrable on `A`.
  have hμ' : ∀ S : Set (Amb n ℓ),
      ((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ) S < ∞ := by
    intro S
    refine (measure_mono (subset_univ S)).trans_lt ?_
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hasFiniteIntegral_iff_enorm.1 hint.integrable.hasFiniteIntegral
  -- Step 3: for `Hⁿ`-a.e. `x` and every `i`, the set `A \ C i` has zero `μ'`-density at `x` if
  -- `x ∉ A \ C i`, and `C i` has an approximate tangent space at `x` if `x ∈ C i`.
  have hdens := ae_all_iff.2 fun i => rsod_ae_tendsto_density_zero_outside n ℓ _ (A \ C i)
    (hA.diff (hC i).1.measurableSet) (hμ' _)
  have htan := ae_all_iff.2 fun i => hK (C i) (hC i).1 (hC i).2.1
  -- Step 4: off these null sets and `A \ ⋃ C i`, each `x ∈ A` lies in some `C i`, and the
  -- approximate tangent space of `C i` at `x` is the weighted one of `A`.
  filter_upwards [hdens, htan, measure_eq_zero_iff_ae_notMem.1 hnull] with x hxd hxt hxn hxA
  have hxU : x ∈ ⋃ i, C i := by
    by_contra h
    exact hxn ⟨hxA, h⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.1 hxU
  obtain ⟨P, hP⟩ := hxt i hxi
  exact ⟨P, Submission.rsod_wfu_weightedApproxTangent_of_closed_piece n ℓ A (C i) ϑ x P hA hAfin
    hint (hC i).1.measurableSet (hC i).2.1 ((hC i).2.2 x hxi) hP (hxd i fun h => h.2 hxi)⟩
/-- Simon Ch. 3, Definition 1.7 and Remark 1.8(1): the weighted approximate tangent space at `x`
only sees `A` and `ϑ` near `x` and up to an `Hⁿ`-null set.  If `A` is `Hⁿ`-measurable, `O ∋ x` is
open, `Hⁿ(Z) = 0`, `(A ∩ O) \ Z = (A' ∩ O) \ Z`, `ϑ = ϑ'` on `(A ∩ O) \ Z` and `ϑ(x) = ϑ'(x)`, then
`T_x A = P` with respect to `ϑ` implies `T_x A' = P` with respect to `ϑ'`.  For `f ∈ C_c` vanishing
off `B_R(0)` and `B̆_ρ(x) ⊆ O`, both blow-up integrals at `0 < r < ρ/R` reduce to
`η_{x,r}(A ∩ B_{rR}(x))`, which differs from `η_{x,r}(A' ∩ B_{rR}(x))` only inside the null set
`η_{x,r}(Z)` (`rsod_blowUpMap_measure_scaling`), and the weights agree off `η_{x,r}(Z)`. -/
theorem rsod_weightedApproxTangent_congr : ∀ (n ℓ : ℕ) (A A' O Z : Set (Amb n ℓ)) (ϑ ϑ' : Amb n ℓ → ℝ) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), NullMeasurableSet A (μHE[n] : Measure (Amb n ℓ)) → IsOpen O → x ∈ O → (μHE[n] : Measure (Amb n ℓ)) Z = 0 → (A ∩ O) \ Z = (A' ∩ O) \ Z → (∀ z ∈ (A ∩ O) \ Z, ϑ z = ϑ' z) → ϑ x = ϑ' x → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A' ϑ' x P := by
  intro n ℓ A A' O Z ϑ ϑ' x P hA hO hxO hZ hAA' hϑ hϑx hP
  refine ⟨hP.1, fun f => ?_⟩
  -- Step 1: `f = 0` off `B_R(0)` with `R = max R₀ 1 > 0`, and `B̆_ρ(x) ⊆ O`.
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  have hRpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ y, y ∉ closedBall (0 : Amb n ℓ) (max R₀ 1) → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ (subset_tsupport _ hne)))
  obtain ⟨ρ, hρpos, hρO⟩ := Metric.isOpen_iff.mp hO x hxO
  -- The two blow-up integrals agree for every `r ∈ (0, ρ/R)`.
  have hmain : ∀ r ∈ Ioo (0 : ℝ) (ρ / max R₀ 1),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y * ϑ (x + r • y)
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A', f y * ϑ' (x + r • y)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    rintro r ⟨hr0, hrρ⟩
    -- Step 2: `B_{rR}(x) ⊆ O`, `η⁻¹(B_R(0)) = B_{rR}(x)` and `x + r η(z) = z`.
    have hηapp : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap x r z = r⁻¹ • (z - x) := fun z => rfl
    have hback : ∀ z, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := by
      intro z
      rw [hηapp, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      abel
    have hrR : r * max R₀ 1 < ρ := by rwa [lt_div_iff₀ hRpos] at hrρ
    have hBxO : closedBall x (r * max R₀ 1) ⊆ O := (closedBall_subset_ball hrR).trans hρO
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' closedBall (0 : Amb n ℓ) (max R₀ 1)
        = closedBall x (r * max R₀ 1) := by
      ext z
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero, hηapp, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      rw [inv_mul_le_iff₀ hr0]
    -- Step 3: cut-off, `∫_{η(S)} f ψ(x + r·) = ∫_{η(S ∩ B_{rR}(x))} f ψ(x + r·)`.
    have hcut : ∀ (S : Set (Amb n ℓ)) (ψ : Amb n ℓ → ℝ),
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y * ψ (x + r • y)
            ∂(μHE[n] : Measure (Amb n ℓ)) =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * max R₀ 1)),
            f y * ψ (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) := by
      intro S ψ
      have h1 : (fun y => f y * ψ (x + r • y)) =
          (closedBall (0 : Amb n ℓ) (max R₀ 1)).indicator (fun y => f y * ψ (x + r • y)) := by
        funext y
        by_cases hy : y ∈ closedBall (0 : Amb n ℓ) (max R₀ 1)
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy, hfR y hy, zero_mul]
      have h2 := setIntegral_indicator (μ := (μHE[n] : Measure (Amb n ℓ)))
        (s := Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) (f := fun y => f y * ψ (x + r • y))
        (isClosed_closedBall (x := (0 : Amb n ℓ)) (ε := max R₀ 1)).measurableSet
      rw [← h1, ← image_inter_preimage, hpre] at h2
      exact h2
    -- Step 4: `η` maps `Hⁿ`-null sets to `Hⁿ`-null sets (blowup_scaling, part (i)).
    have hnull : ∀ S : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) S = 0 →
        (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
      intro S hS
      have h := (Submission.rsod_blowUpMap_measure_scaling n ℓ x r hr0 S).1
      rw [hS] at h
      have hne : ENNReal.ofReal (r ^ n) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      exact (mul_eq_zero.mp h).resolve_left hne
    -- Step 5: the cut sets `s = η(A ∩ B_{rR}(x))` and `s' = η(A' ∩ B_{rR}(x))` differ only
    -- inside `η(Z)`, so they are `Hⁿ`-a.e. equal.
    have hss' : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ closedBall x (r * max R₀ 1))
        =ᵐ[(μHE[n] : Measure (Amb n ℓ))]
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A' ∩ closedBall x (r * max R₀ 1)) := by
      rw [ae_eq_set]
      constructor
      · refine measure_mono_null ?_ (hnull Z hZ)
        rintro y ⟨⟨z, ⟨hzA, hzB⟩, rfl⟩, hy'⟩
        refine ⟨z, ?_, rfl⟩
        by_contra hzZ
        have hz' : z ∈ (A' ∩ O) \ Z := hAA' ▸ ⟨⟨hzA, hBxO hzB⟩, hzZ⟩
        exact hy' ⟨z, ⟨hz'.1.1, hzB⟩, rfl⟩
      · refine measure_mono_null ?_ (hnull Z hZ)
        rintro y ⟨⟨z, ⟨hzA, hzB⟩, rfl⟩, hy'⟩
        refine ⟨z, ?_, rfl⟩
        by_contra hzZ
        have hz' : z ∈ (A ∩ O) \ Z := hAA'.symm ▸ ⟨⟨hzA, hBxO hzB⟩, hzZ⟩
        exact hy' ⟨z, ⟨hz'.1.1, hzB⟩, rfl⟩
    -- Step 6: `s` is null-measurable: `η` is a measurable embedding, and `s` is the image of a
    -- Borel subset `T ⊆ A ∩ B_{rR}(x)` together with the image of a null set.
    have hηemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
      have h : Poincare.SimonGMT.Chapter03.blowUpMap x r =
          ⇑((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0.ne'))) := by
        funext z; rfl
      rw [h]
      exact Homeomorph.measurableEmbedding _
    have hsnm : NullMeasurableSet
        (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ closedBall x (r * max R₀ 1)))
        (μHE[n] : Measure (Amb n ℓ)) := by
      have hAB : NullMeasurableSet (A ∩ closedBall x (r * max R₀ 1)) (μHE[n] : Measure (Amb n ℓ)) :=
        hA.inter isClosed_closedBall.measurableSet.nullMeasurableSet
      obtain ⟨T, hTsub, hTmeas, hTae⟩ := hAB.exists_measurable_subset_ae_eq
      have hdiff : (μHE[n] : Measure (Amb n ℓ)) ((A ∩ closedBall x (r * max R₀ 1)) \ T) = 0 :=
        (ae_eq_set.mp hTae).2
      have hunion : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ closedBall x (r * max R₀ 1)) =
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∪
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' ((A ∩ closedBall x (r * max R₀ 1)) \ T) := by
        rw [← image_union, union_sdiff_cancel hTsub]
      rw [hunion]
      exact (hηemb.measurableSet_image.mpr hTmeas).nullMeasurableSet.union
        (NullMeasurableSet.of_null (hnull _ hdiff))
    -- Step 7: off `η(Z)`, a point `y = η(z)` of `s` has `z ∈ (A ∩ O) \ Z` and `x + r y = z`, so the
    -- integrands `f ϑ(x + r·)` and `f ϑ'(x + r·)` agree a.e. on `s`.
    have hae : ∀ᵐ y ∂(μHE[n] : Measure (Amb n ℓ)),
        y ∈ Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ closedBall x (r * max R₀ 1)) →
          f y * ϑ (x + r • y) = f y * ϑ' (x + r • y) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hnull Z hZ)] with y hyZ hy
      obtain ⟨z, ⟨hzA, hzB⟩, rfl⟩ := hy
      have hzZ : z ∉ Z := fun h => hyZ ⟨z, h, rfl⟩
      rw [hback z, hϑ z ⟨⟨hzA, hBxO hzB⟩, hzZ⟩]
    -- Step 8: combine the cut-off, the a.e. equal integrands and the a.e. equal sets.
    rw [hcut A ϑ, hcut A' ϑ']
    exact (setIntegral_congr_ae₀ hsnm hae).trans (setIntegral_congr_set hss')
  -- Step 1 (conclusion): the integrals agree on `(0, ρ/R) ∈ 𝓝[>] 0` and `ϑ(x) = ϑ'(x)`.
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A,
        f y * ϑ (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ))) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A',
        f y * ϑ' (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ))) :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT (div_pos hρpos hRpos)) hmain
  have h := (hP.2 f).congr' hev
  rwa [hϑx] at h
/-- **Lusin's theorem for Borel maps `ℝⁿ → L(ℝⁿ, ℝ)`** (Simon Ch. 1, Theorem 1.17; used in the
proof of Ch. 2, Theorem 1.5).  If `F : ℝⁿ → L(ℝⁿ, ℝ)` is Borel, `S ⊆ ℝⁿ` is Borel with
`Lⁿ(S) < ∞` and `δ > 0`, then there is a closed `C ⊆ S` with `Lⁿ(S \ C) < δ` on which `F` is
continuous.  Fix a countable basis `𝓑` of `L(ℝⁿ, ℝ)` and tolerances `ε_U > 0` (`U ∈ 𝓑`) with
`Σ ε_U < δ/4`.  Take a closed `K₀ ⊆ S` with `Lⁿ(S \ K₀) < δ/2` and, for `A_U = S ∩ F⁻¹(U)`, a
closed `K_U ⊆ A_U` and an open `O_U ⊇ A_U` with `Lⁿ(A_U \ K_U), Lⁿ(O_U \ A_U) < ε_U`.  Then
`C = K₀ ∩ ⋂_U (O_Uᶜ ∪ K_U)` is closed, `S \ C ⊆ (S \ K₀) ∪ ⋃_U (O_U \ K_U)` has measure `< δ`, and
`F⁻¹(U) ∩ C = O_U ∩ C` for every `U ∈ 𝓑`, so `F|_C` is continuous. -/
theorem rsod_c1ab_clm_lusin_closed : ∀ (n : ℕ) (F : Rn n → (Rn n →L[ℝ] ℝ)), Measurable F → ∀ S : Set (Rn n), MeasurableSet S → volume S ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ C : Set (Rn n), C ⊆ S ∧ IsClosed C ∧ volume (S \ C) < δ ∧ ContinuousOn F C := by
  intro n F hF S hS hSfin δ hδ
  -- A countable basis `𝓑` of the target space `L(ℝⁿ, ℝ)`.
  set 𝓑 := TopologicalSpace.countableBasis (Rn n →L[ℝ] ℝ)
  have h𝓑 : TopologicalSpace.IsTopologicalBasis 𝓑 := TopologicalSpace.isBasis_countableBasis _
  have : Countable 𝓑 := (TopologicalSpace.countable_countableBasis _).to_subtype
  -- Inner regularity: a closed `K₀ ⊆ S` with `Lⁿ(S \ K₀) < δ/2`.
  have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
  obtain ⟨K₀, hK₀S, hK₀, hK₀μ⟩ := hS.exists_isClosed_sdiff_lt hSfin hδ2
  -- Tolerances `ε_U > 0` with `Σ_U ε_U < δ/4`.
  obtain ⟨ε, hε, hεsum⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hδ2).ne' 𝓑
  -- `A_U = S ∩ F⁻¹(U)` is Borel of finite measure; approximate it from inside and outside.
  have hA : ∀ U : 𝓑, MeasurableSet (S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ))) := fun U =>
    hS.inter (hF (h𝓑.isOpen U.2).measurableSet)
  have hAfin : ∀ U : 𝓑, volume (S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ))) ≠ ∞ := fun U =>
    ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left)
  choose K hKA hK hKμ using fun U : 𝓑 =>
    (hA U).exists_isClosed_sdiff_lt (μ := volume) (hAfin U) (hε U).ne'
  choose O hAO hO _ hOμ using fun U : 𝓑 =>
    (hA U).exists_isOpen_sdiff_lt (μ := volume) (hAfin U) (hε U).ne'
  refine ⟨K₀ ∩ ⋂ U : 𝓑, ((O U)ᶜ ∪ K U), inter_subset_left.trans hK₀S,
    hK₀.inter (isClosed_iInter fun U => (hO U).isClosed_compl.union (hK U)), ?_, ?_⟩
  · -- `S \ C ⊆ (S \ K₀) ∪ ⋃_U (O_U \ K_U)` and `Lⁿ(O_U \ K_U) ≤ 2 ε_U`.
    have hsub : S \ (K₀ ∩ ⋂ U : 𝓑, ((O U)ᶜ ∪ K U)) ⊆ (S \ K₀) ∪ ⋃ U : 𝓑, (O U \ K U) := by
      rintro x ⟨hxS, hxC⟩
      by_cases hx0 : x ∈ K₀
      · refine Or.inr (mem_iUnion.2 ?_)
        by_contra hcon
        refine hxC ⟨hx0, mem_iInter.2 fun U => ?_⟩
        by_cases hxO : x ∈ O U
        · by_contra hxK
          exact hcon ⟨U, hxO, fun h => hxK (Or.inr h)⟩
        · exact Or.inl hxO
      · exact Or.inl ⟨hxS, hx0⟩
    have hOK : ∀ U : 𝓑, volume (O U \ K U) ≤ ε U + ε U := by
      intro U
      calc volume (O U \ K U)
          ≤ volume ((O U \ (S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ)))) ∪
              ((S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ))) \ K U)) := by
            refine measure_mono fun x hx => ?_
            by_cases hxA : x ∈ S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ))
            · exact Or.inr ⟨hxA, hx.2⟩
            · exact Or.inl ⟨hx.1, hxA⟩
        _ ≤ volume (O U \ (S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ)))) +
              volume ((S ∩ F ⁻¹' (U : Set (Rn n →L[ℝ] ℝ))) \ K U) := measure_union_le _ _
        _ ≤ ε U + ε U := add_le_add (hOμ U).le (hKμ U).le
    calc volume (S \ (K₀ ∩ ⋂ U : 𝓑, ((O U)ᶜ ∪ K U)))
        ≤ volume ((S \ K₀) ∪ ⋃ U : 𝓑, (O U \ K U)) := measure_mono hsub
      _ ≤ volume (S \ K₀) + volume (⋃ U : 𝓑, (O U \ K U)) := measure_union_le _ _
      _ ≤ volume (S \ K₀) + ∑' U : 𝓑, volume (O U \ K U) := by
          gcongr; exact measure_iUnion_le _
      _ ≤ volume (S \ K₀) + ∑' U : 𝓑, (ε U + ε U) := by
          gcongr with U; exact hOK U
      _ = volume (S \ K₀) + (∑' U : 𝓑, ε U + ∑' U : 𝓑, ε U) := by rw [ENNReal.tsum_add]
      _ < δ / 2 + (δ / 2 / 2 + δ / 2 / 2) :=
          ENNReal.add_lt_add hK₀μ (ENNReal.add_lt_add hεsum hεsum)
      _ = δ := by rw [ENNReal.add_halves, ENNReal.add_halves]
  · -- On `C`, `F⁻¹(U) = O_U` for every basic open `U`, so `F|_C` is continuous.
    rw [continuousOn_iff_continuous_domRestrict, h𝓑.continuous_iff]
    intro U hU
    refine Topology.IsInducing.subtypeVal.isOpen_iff.2 ⟨O ⟨U, hU⟩, hO _, ?_⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, domRestrict_apply]
    constructor
    · intro hxO
      rcases mem_iInter.1 hx.2 ⟨U, hU⟩ with h | h
      · exact absurd hxO h
      · exact (hKA _ h).2
    · intro hxU
      exact hAO _ ⟨hK₀S hx.1, hxU⟩
/-- Simon Ch. 2, proof of Theorem 1.5 (p. 44): **Egoroff's theorem with a closed good set** in `ℝⁿ`.
If `g_k : ℝⁿ → ℝ` are Borel measurable and `g_k → 0` pointwise on a measurable `C` with `Lⁿ(C) < ∞`,
then for every `δ > 0` there is a closed `A ⊆ C` with `Lⁿ(C \ A) < δ` on which `g_k → 0` uniformly:
Egoroff's theorem on `C` with tolerance `δ'/2`, then a closed subset of the good set by inner
regularity of `Lⁿ` with tolerance `δ'/2`, where `δ' = min δ 1`. -/
theorem rsod_c1ab_utr_closed_egoroff : ∀ (n : ℕ) (g : ℕ → Rn n → ℝ), (∀ k, Measurable (g k)) → ∀ C : Set (Rn n), MeasurableSet C → volume C ≠ ∞ → (∀ x ∈ C, Tendsto (fun k => g k x) atTop (𝓝 0)) → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ TendstoUniformlyOn g (fun _ => 0) atTop A := by
  intro n g hg C hC hCfin hconv δ hδ
  -- Step 1: the finite tolerance `δ' = min δ 1`, so `0 < δ'/2 < ∞` and `δ'/2 + δ'/2 = δ' ≤ δ`.
  set δ' : ℝ≥0∞ := min δ 1
  have hδ'0 : δ' ≠ 0 := (lt_min (pos_iff_ne_zero.2 hδ) one_pos).ne'
  have hδ'top : δ' ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right δ 1)
  have hhalf : 0 < δ' / 2 := ENNReal.half_pos hδ'0
  -- Step 2 (Egoroff): a measurable `t ⊆ C` with `Lⁿ(t) ≤ δ'/2` and `g_k → 0` uniformly on `C \ t`.
  obtain ⟨t, htC, htm, ht, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto (μ := volume)
    (fun k => (hg k).stronglyMeasurable) stronglyMeasurable_const hC hCfin
    (ae_of_all _ fun x hx => hconv x hx) hhalf
  -- Step 3 (inner regularity): a closed `A ⊆ C \ t` with `Lⁿ((C \ t) \ A) < δ'/2`.
  obtain ⟨A, hAsub, hAcl, hA⟩ := (hC.diff htm).exists_isClosed_sdiff_lt
    (ne_top_of_le_ne_top hCfin (measure_mono sdiff_subset)) hhalf.ne'
  -- Step 4: `A` is closed, `A ⊆ C \ t ⊆ C`, and the uniform convergence restricts to `A`.
  refine ⟨A, hAsub.trans sdiff_subset, hAcl, ?_, hunif.mono hAsub⟩
  -- Step 5: `C \ A ⊆ t ∪ ((C \ t) \ A)`, so `Lⁿ(C \ A) < δ'/2 + δ'/2 = δ' ≤ δ`.
  have hsub : C \ A ⊆ t ∪ ((C \ t) \ A) := by
    rintro x ⟨hxC, hxA⟩
    by_cases hxt : x ∈ t
    · exact Or.inl hxt
    · exact Or.inr ⟨⟨hxC, hxt⟩, hxA⟩
  calc volume (C \ A) ≤ volume (t ∪ ((C \ t) \ A)) := measure_mono hsub
    _ ≤ volume t + volume ((C \ t) \ A) := measure_union_le _ _
    _ < δ' / 2 + δ' / 2 := ENNReal.add_lt_add_of_le_of_lt
      (ne_top_of_le_ne_top (ENNReal.div_ne_top hδ'top two_ne_zero) ht) ht hA
    _ = δ' := ENNReal.add_halves δ'
    _ ≤ δ := min_le_left δ 1
/-- Simon Ch. 2, proof of Theorem 1.5 (p. 44): **sup-control of the Taylor remainder**.  For a
`K`-Lipschitz `f : ℝⁿ → ℝ` differentiable at every point of a closed `C`, with
`R(x, y) = f y - f x - Df(x)(y - x)`, the functions
`η_k(x) = 1_C(x) · sup {|R(x, q)|/|q - x| : q ∈ Q, 0 < |q - x| < 1/(k+1)}` (`Q ⊆ C` countable dense)
are Borel, tend to `0` on `C`, and satisfy `|R(x, y)| ≤ η_k(x)|y - x|` for `x, y ∈ C` with
`0 < |y - x| < 1/(k+1)`: by differentiability at `x` for the limit, and by continuity of
`q ↦ |R(x, q)|/|q - x|` at `y` along `Q` for the bound. -/
theorem rsod_c1ab_utr_remainder_sup_control : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ C : Set (Rn n), IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ∃ η : ℕ → Rn n → ℝ, (∀ k, Measurable (η k)) ∧ (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0)) ∧ ∀ k : ℕ, ∀ x ∈ C, ∀ y ∈ C, 0 < ‖y - x‖ → ‖y - x‖ < 1 / ((k : ℝ) + 1) → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η k x * ‖y - x‖ := by
  intro n f K hf C hC hdiff
  -- Step 1: `|f y - f x - Df(x)(y - x)| ≤ 2K|y - x|`, from the Lipschitz bound and `‖Df(x)‖ ≤ K`.
  have hrem : ∀ x y : Rn n, ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ 2 * (K : ℝ) * ‖y - x‖ := by
    intro x y
    have h1 : ‖f y - f x‖ ≤ K * ‖y - x‖ := hf.norm_sub_le y x
    have h2 : ‖fderiv ℝ f x (y - x)‖ ≤ K * ‖y - x‖ :=
      ((fderiv ℝ f x).le_opNorm (y - x)).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ K * ‖y - x‖ + K * ‖y - x‖ := add_le_add h1 h2
      _ = 2 * (K : ℝ) * ‖y - x‖ := by ring
  -- Step 2: a countable `Q ⊆ C` with `C ⊆ closure Q`.
  obtain ⟨Q, hQC, hQc, hCQ⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have : Countable Q := hQc.to_subtype
  -- Step 3: `ψ_{k,q}(x) = |R(x, q)|/|q - x|` on the window `0 < |q - x| < 1/(k+1)`, else `0`.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → Rn n → Rn n → ℝ, ∀ k q x, ψ k q x =
      if 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1) then
        ‖f q - f x - fderiv ℝ f x (q - x)‖ / ‖q - x‖ else 0 := ⟨_, fun _ _ _ => rfl⟩
  -- Step 4: `0 ≤ ψ_{k,q} ≤ 2K`, so the family `(ψ_{k,q}(x))_{q ∈ Q}` is bounded above.
  have hψ_nonneg : ∀ k q x, 0 ≤ ψ k q x := by
    intro k q x
    rw [hψ]
    split_ifs
    · positivity
    · exact le_rfl
  have hψ_le : ∀ k q x, ψ k q x ≤ 2 * (K : ℝ) := by
    intro k q x
    rw [hψ]
    split_ifs with h
    · rw [div_le_iff₀ h.1]
      exact hrem x q
    · positivity
  have hbdd : ∀ k x, BddAbove (Set.range fun q : Q => ψ k q x) := fun k x =>
    ⟨2 * (K : ℝ), by rintro _ ⟨q, rfl⟩; exact hψ_le k q x⟩
  -- `η_k = 1_C · sup_{q ∈ Q} ψ_{k,q}`.
  refine ⟨fun k => C.indicator (fun x => ⨆ q : Q, ψ k q x), ?_, ?_, ?_⟩
  · -- Step 5: each `η_k` is Borel.
    intro k
    refine Measurable.indicator (Measurable.iSup fun q => ?_) hC.measurableSet
    have hD : Measurable fun x => fderiv ℝ f x ((q : Rn n) - x) :=
      ContinuousLinearMap.measurable_apply₂.comp
        ((measurable_fderiv ℝ f).prodMk (measurable_const.sub measurable_id))
    have hU : IsOpen {x : Rn n | 0 < ‖(q : Rn n) - x‖ ∧ ‖(q : Rn n) - x‖ < 1 / ((k : ℝ) + 1)} :=
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).inter
        (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)
    show Measurable fun x => ψ k q x
    simp only [hψ]
    exact Measurable.ite hU.measurableSet
      (((measurable_const.sub hf.continuous.measurable).sub hD).norm.div
        (measurable_const.sub measurable_id).norm) measurable_const
  · -- Step 6: `η_k(x) → 0` for `x ∈ C`.
    intro x hx
    dsimp only
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
      ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos hε))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hr
    refine ⟨k₀, fun k hk => ?_⟩
    have hle : (⨆ q : Q, ψ k q x) ≤ ε / 2 := by
      refine Real.iSup_le (fun q => ?_) (half_pos hε).le
      rw [hψ]
      split_ifs with h
      · rw [div_le_iff₀ h.1]
        have hlt : dist (q : Rn n) x < r := by
          rw [dist_eq_norm]
          calc ‖(q : Rn n) - x‖ < 1 / ((k : ℝ) + 1) := h.2
            _ ≤ 1 / ((k₀ : ℝ) + 1) := by gcongr
            _ < r := hk₀
        exact hball hlt
      · exact (half_pos hε).le
    have hnn : 0 ≤ ⨆ q : Q, ψ k q x := Real.iSup_nonneg fun q => hψ_nonneg k q x
    rw [Set.indicator_of_mem hx, Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  · -- Step 7: `|R(x, y)| ≤ η_k(x)|y - x|` for `x, y ∈ C` with `0 < |y - x| < 1/(k+1)`.
    intro k x hx y hy hpos hlt
    dsimp only
    have hφ : ContinuousAt (fun q : Rn n => ‖f q - f x - fderiv ℝ f x (q - x)‖ / ‖q - x‖) y :=
      (((hf.continuous.sub continuous_const).sub ((fderiv ℝ f x).continuous.comp
        (continuous_id.sub continuous_const))).norm.continuousAt).div
        (continuous_id.sub continuous_const).norm.continuousAt hpos.ne'
    have hW : IsOpen {q : Rn n | 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1)} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    have : (𝓝[Q] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hCQ hy)
    have hle : ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖ ≤ ⨆ q : Q, ψ k q x := by
      refine le_of_tendsto (x := 𝓝[Q] y) (hφ.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hW.mem_nhds ⟨hpos, hlt⟩)]
        with q hqQ hqW
      calc ‖f q - f x - fderiv ℝ f x (q - x)‖ / ‖q - x‖ = ψ k q x := by rw [hψ, ite_eq_left hqW]
        _ ≤ ⨆ q' : Q, ψ k q' x := le_ciSup (hbdd k x) ⟨q, hqQ⟩
    rw [Set.indicator_of_mem hx]
    rwa [div_le_iff₀ hpos] at hle
/-- Simon Ch. 2, proof of Theorem 1.5 (p. 44), the uniform first-order Taylor estimate.  Let `f` be
`K`-Lipschitz on `ℝⁿ` and differentiable at every point of the closed set `C`, with `Lⁿ(C) < ∞`, and
let `δ > 0`.  Then there is a closed `A ⊆ C` with `Lⁿ(C \ A) < δ` such that for every `τ > 0` some
`ρ > 0` gives `|f(y) − f(x) − Df(x)(y − x)| ≤ τ |y − x|` for all `x, y ∈ A` with `|x − y| < ρ`.
Proof: the Borel majorants `η_k` of the normalised remainder tend to `0` pointwise on `C`
(`rsod_c1ab_utr_remainder_sup_control`).  Egoroff's theorem with inner regularity makes the
convergence uniform on a closed `A ⊆ C` with `Lⁿ(C \ A) < δ` (`rsod_c1ab_utr_closed_egoroff`).
Given `τ > 0`, take `k` with `η_k < τ` on `A` and put `ρ = 1/(k+1)`. -/
theorem rsod_c1ab_uniform_taylor_remainder : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ C : Set (Rn n), IsClosed C → volume C ≠ ∞ → (∀ x ∈ C, DifferentiableAt ℝ f x) → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ A, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ τ * ‖y - x‖ := by
  intro n f K hf C hC hCfin hdiff δ hδ
  -- Step 1: Borel `η_k` with `η_k → 0` pointwise on `C` and
  -- `|f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x) |y − x|` for `x, y ∈ C`, `0 < |y − x| < 1/(k+1)`.
  obtain ⟨η, hηm, hηlim, hηbd⟩ :=
    Submission.rsod_c1ab_utr_remainder_sup_control n f K hf C hC hdiff
  -- Step 2: a closed `A ⊆ C` with `Lⁿ(C \ A) < δ` and `η_k → 0` uniformly on `A`.
  obtain ⟨A, hAC, hAcl, hCA, hunif⟩ :=
    Submission.rsod_c1ab_utr_closed_egoroff n η hηm C hC.measurableSet hCfin hηlim δ hδ
  refine ⟨A, hAC, hAcl, hCA, fun τ hτ => ?_⟩
  -- Step 3: uniform convergence gives `k` with `|η_k| < τ` on `A`; take `ρ = 1/(k+1)`.
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif τ hτ).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx y hy hxy => ?_⟩
  -- Step 4: for `y = x` both sides vanish.
  rcases eq_or_ne y x with rfl | hyx
  · simp
  -- Step 5: for `y ≠ x`, `0 < |y − x| < 1/(k+1)`, so the bound of step 1 applies with `η_k(x) < τ`.
  have hηk : η k x < τ := by
    have h := hk x hx
    rw [dist_comm, Real.dist_0_eq_abs] at h
    exact (le_abs_self _).trans_lt h
  rw [dist_comm, dist_eq_norm] at hxy
  calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η k x * ‖y - x‖ :=
        hηbd k x (hAC hx) y (hAC hy) (norm_pos_iff.2 (sub_ne_zero.2 hyx)) hxy
    _ ≤ τ * ‖y - x‖ := mul_le_mul_of_nonneg_right hηk.le (norm_nonneg _)
/-- **Whitney's `C¹` extension theorem on `ℝⁿ`, value part** (Simon Ch. 2, Theorem 1.6, whose
proof Simon cites from [EG92] §6.5 and [Fed69] 3.1.14).  Let `A ⊆ ℝⁿ` be closed, and let
`h : ℝⁿ → ℝ` and `D : ℝⁿ → L(ℝⁿ, ℝ)` be continuous on `A`.  Suppose the first-order Taylor remainder
satisfies `|h y - h x - D x (y - x)| ≤ τ |y - x|` uniformly for `x` in each compact `Q ⊆ A` and
`y ∈ A` near `x`.  Then some `g ∈ C¹(ℝⁿ)` equals `h` on `A`.
Proof (the Evans–Gariepy/Federer construction):
* compactness of `A ∩ B(a, 1)` and continuity of `D` give a uniform estimate near each `a ∈ A`;
* Vitali selects Whitney balls `B(c, r c)`, `r = min 1 (dist (·, A)) / 100`, with bounded overlap;
* rescaled bumps give a smooth partition of unity `φ c` on `Aᶜ` with `∑ ‖Dφ c‖ ≤ M / r`;
* `g = ∑ φ c · (h b_c + D b_c (· - b_c))` off `A`, with nearest-point anchors `b_c`, and `g = h`
  on `A`.
Then `Dg(a) = D a` on `A`, `Dg` is continuous at points of `A`, and `g` is `C¹` off `A`. -/
theorem rsod_c1ab_whitney_c1_extension : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖h y - h x - D x (y - x)‖ ≤ τ * ‖y - x‖) → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ a ∈ A, g a = h a := by
  intro n A h D hA _ hDc hcpt
  -- The local uniform estimate near `a ∈ A`, from compactness of `A ∩ B(a, 1)`.
  have hW : ∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ e) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ → |h c - h b - D b (c - b)| ≤ e * ‖c - b‖ := by
    intro a ha e he
    obtain ⟨ρ, hρ, hρQ⟩ := hcpt (A ∩ closedBall a 1) ((isCompact_closedBall a 1).inter_left hA)
      inter_subset_left e he
    obtain ⟨η, hη, hηD⟩ := Metric.continuousOn_iff.1 hDc a ha e he
    obtain ⟨δ, hδ0, hδ1, hδη, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ η ∧ δ ≤ ρ / 3 :=
      ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    refine ⟨δ, hδ0, hδ1, fun b hb hba => ?_, fun b hb hba c hc hca => ?_⟩
    · rw [← dist_eq_norm]
      exact (hηD b hb (hba.trans_le hδη)).le
    · have hbc : dist b c < ρ := by
        have := dist_triangle b a c
        rw [dist_comm a c] at this
        linarith
      have h1 := hρQ b ⟨hb, mem_closedBall.2 (by linarith)⟩ c hc hbc
      rwa [Real.norm_eq_abs] at h1
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
/-- **Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 44)**, run inside `B = B_R(0)`.
If `f : ℝⁿ → ℝ` is Lipschitz, then for every `R` and `ε > 0` some `g ∈ C¹(ℝⁿ)` has
`Lⁿ(B_R(0) ∩ {f ≠ g}) < ε`.  Proof: `D = {x : f is differentiable at x}` is Borel with
`Lⁿ(ℝⁿ \ D) = 0` (Rademacher), and `Df` is Borel.  Lusin's theorem gives a closed `C ⊆ B ∩ D` with
`Df` continuous on `C` and `Lⁿ((B ∩ D) \ C) < ε/2`.  The Egoroff argument gives a closed `A ⊆ C`
with `Lⁿ(C \ A) < ε/2` on which `|f(y) − f(x) − Df(x)(y − x)| ≤ τ|y − x|` holds uniformly for
`|x − y| < ρ(τ)`.  Whitney's extension theorem then gives `g ∈ C¹` with `g = f` on `A`, and
`B ∩ {f ≠ g} ⊆ (ℝⁿ \ D) ∪ ((B ∩ D) \ C) ∪ (C \ A)`. -/
theorem rsod_lipschitz_c1_approx_closedBall : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ (R : ℝ) (ε : ℝ≥0∞), 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume (closedBall (0 : Rn n) R ∩ {x | f x ≠ g x}) < ε := by
  intro n f K hf R ε hε
  set B : Set (Rn n) := closedBall (0 : Rn n) R
  set D : Set (Rn n) := {x | DifferentiableAt ℝ f x}
  -- Step 1: `B` is compact, so `Lⁿ(B) < ∞`; the tolerance `ε/2` is positive.
  have hBfin : volume B < ∞ := measure_closedBall_lt_top
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  -- Step 2: `D` is Borel and, by Rademacher's theorem, `Lⁿ(ℝⁿ \ D) = 0`; `Df` is Borel.
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hDnull : volume Dᶜ = 0 := ae_iff.mp hf.ae_differentiableAt
  -- Step 3 (Lusin): a closed `C ⊆ B ∩ D` with `Df` continuous on `C`, `Lⁿ((B ∩ D) \ C) < ε/2`.
  obtain ⟨C, hCBD, hC, hBDC, hDfC⟩ :=
    Submission.rsod_c1ab_clm_lusin_closed n (fderiv ℝ f) (measurable_fderiv ℝ f) (B ∩ D)
      (measurableSet_closedBall.inter hDmeas)
      ((measure_mono inter_subset_left).trans_lt hBfin).ne (ε / 2) hε2
  -- Step 4 (Egoroff): a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` and a uniform Taylor estimate on `A`.
  obtain ⟨A, hAC, hA, hCA, hrem⟩ :=
    Submission.rsod_c1ab_uniform_taylor_remainder n f K hf C hC
      ((measure_mono (hCBD.trans inter_subset_left)).trans_lt hBfin).ne
      (fun x hx => (hCBD hx).2) (ε / 2) hε2
  -- Step 5 (Whitney): `f` and `Df` satisfy Whitney's `C¹` condition on `A`, so `f|A` extends to
  -- some `g ∈ C¹`; the uniform estimate on `A` gives the one on each compact `Q ⊆ A`.
  obtain ⟨g, hg, hgf⟩ :=
    Submission.rsod_c1ab_whitney_c1_extension n A f (fderiv ℝ f) hA hf.continuous.continuousOn
      (hDfC.mono hAC) fun Q _ hQA τ hτ => by
        obtain ⟨ρ, hρ, h⟩ := hrem τ hτ
        exact ⟨ρ, hρ, fun x hx y hy hxy => h x (hQA hx) y hy hxy⟩
  refine ⟨g, hg, ?_⟩
  -- Step 6: `B ∩ {f ≠ g} ⊆ (ℝⁿ \ D) ∪ ((B ∩ D) \ C) ∪ (C \ A)`, of measure `< 0 + ε/2 + ε/2`.
  have hsub : B ∩ {x | f x ≠ g x} ⊆ Dᶜ ∪ ((B ∩ D) \ C) ∪ (C \ A) := by
    rintro x ⟨hxB, hfg⟩
    by_cases hxD : x ∈ D
    · by_cases hxC : x ∈ C
      · exact Or.inr ⟨hxC, fun hxA => hfg (hgf x hxA).symm⟩
      · exact Or.inl (Or.inr ⟨⟨hxB, hxD⟩, hxC⟩)
    · exact Or.inl (Or.inl hxD)
  calc volume (B ∩ {x | f x ≠ g x})
      ≤ volume Dᶜ + volume ((B ∩ D) \ C) + volume (C \ A) :=
        (measure_mono hsub).trans
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ = volume ((B ∩ D) \ C) + volume (C \ A) := by rw [hDnull, zero_add]
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hBDC hCA
    _ = ε := ENNReal.add_halves ε
/-- **Simon Ch. 3, Lemma 1.2 ("only if"), first half.**  The range of a `K`-Lipschitz
`F : ℝⁿ → ℝ^{n+ℓ}` lies in `N₀ ∪ ⋃_k G_k(ℝⁿ)` with `Hⁿ(N₀) = 0` and every `G_k` of class `C¹`.
Each coordinate `F_c` is `K`-Lipschitz, so `rsod_lipschitz_c1_approx_closedBall` gives `C¹` maps
`g_{m,i,c}` with `Lⁿ(B_m(0) ∩ {F_c ≠ g_{m,i,c}}) < ((i + 1)(n + ℓ + 1))⁻¹`; the assembled maps
`G_{m,i} = (g_{m,i,c})_c` are `C¹` with `Lⁿ(B_m(0) ∩ {F ≠ G_{m,i}}) ≤ (i + 1)⁻¹`.  Hence
`Z = ⋃_m ⋂_i (B_m(0) ∩ {F ≠ G_{m,i}})` is `Lⁿ = Hⁿ`-null, so is the Lipschitz image `N₀ = F(Z)`,
and off `Z` each `F(x)` is some `G_{m,i}(x)`.  The `G_{m,i}` are enumerated through `Nat.unpair`. -/
theorem rsod_lipschitz_range_subset_c1_ranges : ∀ (n ℓ : ℕ) (F : Rn n → Amb n ℓ) (K : ℝ≥0), LipschitzWith K F → ∃ (N₀ : Set (Amb n ℓ)) (G : ℕ → Rn n → Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ range F ⊆ N₀ ∪ ⋃ k, range (G k) := by
  intro n ℓ F K hF
  -- Step 1: each coordinate `F_c` is `K`-Lipschitz.
  have hFc : ∀ c : Fin (n + ℓ), LipschitzWith K fun x => F x c := fun c =>
    LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (F x) (F y) c).trans (hF.dist_le_mul x y)
  -- Step 2: `C¹` maps `g_{m,i,c}` with `Lⁿ(B_m(0) ∩ {F_c ≠ g_{m,i,c}}) < ((i + 1)(n + ℓ + 1))⁻¹`.
  have hε : ∀ i : ℕ, (0 : ℝ≥0∞) < (((i : ℝ≥0∞) + 1) * (((n + ℓ : ℕ) : ℝ≥0∞) + 1))⁻¹ :=
    fun i => ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) (by simp))
  choose g hg hgF using fun (m i : ℕ) (c : Fin (n + ℓ)) =>
    Submission.rsod_lipschitz_c1_approx_closedBall n (fun x => F x c) K (hFc c) m _ (hε i)
  -- Step 3: the vector maps `G_{m,i} = (g_{m,i,c})_c` are `C¹`, and
  -- `Lⁿ(B_m(0) ∩ {F ≠ G_{m,i}}) ≤ (n + ℓ)((i + 1)(n + ℓ + 1))⁻¹ ≤ (i + 1)⁻¹`.
  let G' : ℕ → ℕ → Rn n → Amb n ℓ := fun m i x => WithLp.toLp 2 fun c => g m i c x
  have hG' : ∀ m i, ContDiff ℝ 1 (G' m i) := fun m i =>
    contDiff_piLp' (p := 2) fun c => by simpa [G'] using hg m i c
  have hG'F : ∀ m i : ℕ,
      volume (closedBall (0 : Rn n) m ∩ {x | F x ≠ G' m i x}) ≤ ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro m i
    calc volume (closedBall (0 : Rn n) m ∩ {x | F x ≠ G' m i x})
        ≤ volume (⋃ c : Fin (n + ℓ), closedBall (0 : Rn n) m ∩ {x | F x c ≠ g m i c x}) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨c, hc⟩ : ∃ c, F x c ≠ g m i c x := by
            by_contra! h
            exact hx.2 (PiLp.ext fun c => by simpa [G'] using h c)
          exact mem_iUnion.2 ⟨c, hx.1, hc⟩
      _ ≤ ∑ c : Fin (n + ℓ), volume (closedBall (0 : Rn n) m ∩ {x | F x c ≠ g m i c x}) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _c : Fin (n + ℓ), (((i : ℝ≥0∞) + 1) * (((n + ℓ : ℕ) : ℝ≥0∞) + 1))⁻¹ :=
          Finset.sum_le_sum fun c _ => (hgF m i c).le
      _ = ((i : ℝ≥0∞) + 1)⁻¹ * (((n + ℓ : ℕ) : ℝ≥0∞) * (((n + ℓ : ℕ) : ℝ≥0∞) + 1)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_left_comm]
      _ ≤ ((i : ℝ≥0∞) + 1)⁻¹ * 1 := by
          gcongr
          calc ((n + ℓ : ℕ) : ℝ≥0∞) * (((n + ℓ : ℕ) : ℝ≥0∞) + 1)⁻¹
              ≤ (((n + ℓ : ℕ) : ℝ≥0∞) + 1) * (((n + ℓ : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
                gcongr
                exact le_self_add
            _ ≤ 1 := ENNReal.mul_inv_le_one _
      _ = ((i : ℝ≥0∞) + 1)⁻¹ := mul_one _
  -- Step 4: `Z = ⋃_m ⋂_i (B_m(0) ∩ {F ≠ G_{m,i}})` is `Lⁿ`-null, since each `⋂_i` has measure
  -- `≤ (i + 1)⁻¹ ≤ i⁻¹` for every `i`.
  set Z : Set (Rn n) := ⋃ m : ℕ, ⋂ i : ℕ, closedBall (0 : Rn n) m ∩ {x | F x ≠ G' m i x}
  have hZ : volume Z = 0 := by
    refine measure_iUnion_null fun m => ?_
    by_contra h
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt h
    have hi' : ((i : ℝ≥0∞) + 1)⁻¹ ≤ (i : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact absurd ((measure_mono (iInter_subset
      (fun i : ℕ => closedBall (0 : Rn n) m ∩ {x | F x ≠ G' m i x}) i)).trans
        ((hG'F m i).trans hi')) (not_le.2 hi)
  -- Step 5: `Hⁿ = Lⁿ` on `ℝⁿ`, so the Lipschitz image `N₀ = F(Z)` is `Hⁿ`-null.
  have hN₀ : (μHE[n] : Measure (Amb n ℓ)) (F '' Z) = 0 := by
    refine nonpos_iff_eq_zero.1 ?_
    calc (μHE[n] : Measure (Amb n ℓ)) (F '' Z)
        ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) Z :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- Steps 6–7: off `Z`, `F(x) = G_{m,i}(x)` for some `i` (with `|x| ≤ m`); enumerate the
  -- `G_{m,i}` through `Nat.unpair`.
  refine ⟨F '' Z, fun k => G' k.unpair.1 k.unpair.2, hN₀, fun k => hG' _ _, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hxZ : x ∈ Z
  · exact Or.inl (mem_image_of_mem F hxZ)
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  have hxm : x ∈ closedBall (0 : Rn n) m := mem_closedBall_zero_iff.2 hm
  have hxZm : x ∉ ⋂ i : ℕ, closedBall (0 : Rn n) m ∩ {x | F x ≠ G' m i x} :=
    fun h => hxZ (mem_iUnion.2 ⟨m, h⟩)
  obtain ⟨i, hi⟩ := not_forall.1 (mt mem_iInter.2 hxZm)
  have hFx : F x = G' m i x := not_not.1 fun hne => hi ⟨hxm, hne⟩
  exact Or.inr (mem_iUnion.2 ⟨Nat.pair m i, x, by simp only [Nat.unpair_pair, hFx]⟩)
/-- **Simon Ch. 3, proof of Lemma 1.2 (p. 70, last paragraph)**: an immersed ball is a `C¹` chart.
If `G : ℝⁿ → ℝ^{n+ℓ}` is `C¹` and `DG(a)` is injective, then for some `σ > 0` the image
`G(B̆_σ(a))` is an `n`-dimensional `C¹` submanifold (`IsC1Submanifold`) of finite `Hⁿ`-measure.
Proof: `L = DG(a)` satisfies `c|v| ≤ |Lv|` for some `c > 0`; by continuity of `DG` choose `σ` with
`‖DG(z) − L‖ ≤ c/2` on `B_σ(a)`, so `DG(z)` is injective there and, by the mean value inequality
for `G − L`, `(c/2)|y − x| ≤ |G y − G x| ≤ (‖L‖ + c/2)|y − x|` on `B_σ(a)`.  The chart is
`V = B̆_σ(a)`, `W = ℝ^{n+ℓ} \ G(S_σ(a))`, `φ = G`; properness holds since
`V ∩ G⁻¹K = B_σ(a) ∩ G⁻¹K` for compact `K ⊆ W`.  Finally, with `Λ = ‖L‖ + c/2`,
`Hⁿ(G(B̆_σ(a))) ≤ Λⁿ Hⁿ(B̆_σ(a)) < ∞`. -/
theorem rsod_c1_immersion_ball_isC1Submanifold : ∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ) (a : Rn n), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G a) → ∃ σ : ℝ, 0 < σ ∧ IsC1Submanifold n (G '' ball a σ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball a σ) < ∞ := by
  intro n ℓ G a hG hinj
  set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G a
  -- Step 1: `c |v| ≤ |L v|` with `c = K⁻¹ > 0`, from the antilipschitz bound of the injective `L`.
  obtain ⟨K, hKpos, hK⟩ := (LinearMap.injective_iff_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ)).mp hinj
  have hKpos' : (0 : ℝ) < K := by exact_mod_cast hKpos
  set c : ℝ := (K : ℝ)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr hKpos'
  have hcv : ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
    intro v
    rw [hc, inv_mul_le_iff₀ hKpos']
    exact L.bound_of_antilipschitz hK v
  -- Step 2: choose `σ` with `‖DG(z) − L‖ ≤ c/2` on `B_σ(a)`.
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.mp (hG.continuous_fderiv one_ne_zero) a (c / 2) (half_pos hcpos)
  obtain ⟨σ, hσpos, hσδ⟩ : ∃ σ : ℝ, 0 < σ ∧ σ < δ := ⟨δ / 2, half_pos hδpos, half_lt_self hδpos⟩
  refine ⟨σ, hσpos, ?_⟩
  have hball_sub : ball a σ ⊆ closedBall a σ := ball_subset_closedBall
  have hDG : ∀ z ∈ closedBall a σ, ‖fderiv ℝ G z - L‖ ≤ c / 2 := by
    intro z hz
    have h := hδ z (lt_of_le_of_lt (mem_closedBall.mp hz) hσδ)
    rw [dist_eq_norm] at h
    exact h.le
  -- Step 3: `DG(z)` is injective on `B_σ(a)`: `c|v| ≤ |Lv| ≤ |DG(z)v| + (c/2)|v|`.
  have hDGinj : ∀ z ∈ closedBall a σ, Function.Injective (fderiv ℝ G z) := by
    intro z hz
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ‖L v‖ ≤ c / 2 * ‖v‖ := by
      have hLv : L v = -((fderiv ℝ G z - L) v) := by
        rw [sub_apply, hv, zero_sub, neg_neg]
      rw [hLv, norm_neg]
      exact ((fderiv ℝ G z - L).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDG z hz) (norm_nonneg v))
    have h2 := hcv v
    have h3 : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
    exact norm_le_zero_iff.mp h3
  -- Step 4: mean value inequality for `G − L` on the convex set `B_σ(a)`.
  have hMV : ∀ x ∈ closedBall a σ, ∀ y ∈ closedBall a σ,
      ‖G y - G x - L (y - x)‖ ≤ c / 2 * ‖y - x‖ := fun x hx y hy =>
    (convex_closedBall a σ).norm_image_sub_le_of_norm_fderiv_le' (fun z _ => hdiff z) hDG hx hy
  -- (a) `(c/2)|y − x| ≤ |G y − G x|`, so `G` is injective on `B_σ(a)`.
  have hlow : ∀ x ∈ closedBall a σ, ∀ y ∈ closedBall a σ, c / 2 * ‖y - x‖ ≤ ‖G y - G x‖ := by
    intro x hx y hy
    have h1 := hMV x hx y hy
    have h2 := hcv (y - x)
    have h3 : ‖L (y - x)‖ ≤ ‖G y - G x‖ + ‖G y - G x - L (y - x)‖ := by
      have h := norm_sub_le (G y - G x) (G y - G x - L (y - x))
      rwa [sub_sub_cancel] at h
    linarith
  have hinjOn : InjOn G (closedBall a σ) := by
    intro x hx y hy hxy
    have h := hlow x hx y hy
    rw [hxy, sub_self, norm_zero] at h
    have h' : ‖y - x‖ ≤ 0 := by nlinarith [norm_nonneg (y - x)]
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp h')).symm
  -- (b) `|G y − G x| ≤ (‖L‖ + c/2)|y − x|`, so `G` is Lipschitz on `B_σ(a)`.
  have hLip : LipschitzOnWith (Real.toNNReal (‖L‖ + c / 2)) G (closedBall a σ) := by
    refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := hMV y hy x hx
    have h2 := L.le_opNorm (x - y)
    have h3 : ‖G x - G y‖ ≤ ‖G x - G y - L (x - y)‖ + ‖L (x - y)‖ := by
      have h := norm_add_le (G x - G y - L (x - y)) (L (x - y))
      rwa [sub_add_cancel] at h
    linarith
  -- Step 5: the chart `V = B̆_σ(a)`, `W = ℝ^{n+ℓ} \ G(S_σ(a))`, `φ = G`.
  have hWopen : IsOpen (G '' sphere a σ)ᶜ :=
    ((isCompact_sphere a σ).image hG.continuous).isClosed.isOpen_compl
  -- A point of `B_σ(a)` whose image avoids `G(S_σ(a))` lies in `B̆_σ(a)`.
  have hmem_ball : ∀ x ∈ closedBall a σ, G x ∈ (G '' sphere a σ)ᶜ → x ∈ ball a σ := by
    intro x hx hGx
    rcases (mem_closedBall.mp hx).lt_or_eq with h | h
    · exact mem_ball.mpr h
    · exact absurd ⟨x, mem_sphere.mpr h, rfl⟩ hGx
  -- `G(B̆_σ(a)) ⊆ W` by injectivity of `G` on `B_σ(a)`.
  have himW : G '' ball a σ ⊆ (G '' sphere a σ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hzx' : z = x := hinjOn (sphere_subset_closedBall hz) (hball_sub hx) hzx
    rw [hzx'] at hz
    exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hz)
  refine ⟨?_, ?_⟩
  · intro y hy
    refine ⟨ball a σ, (G '' sphere a σ)ᶜ, G, isOpen_ball, hWopen, himW hy, hG.contDiffOn,
      hinjOn.mono hball_sub, (inter_eq_right.mpr himW).symm, ?_,
      fun x hx => hDGinj x (hball_sub hx)⟩
    intro K hK hKW
    have heq : ball a σ ∩ G ⁻¹' K = closedBall a σ ∩ G ⁻¹' K := by
      refine Subset.antisymm (inter_subset_inter_left _ hball_sub) ?_
      rintro x ⟨hx, hxK⟩
      exact ⟨hmem_ball x hx (hKW hxK), hxK⟩
    rw [heq]
    exact (isCompact_closedBall a σ).inter_right (hK.isClosed.preimage hG.continuous)
  -- Step 6: `μHE[n]` is a constant multiple of `μH[n]`, and `μH[n](G(B̆_σ(a))) ≤ Λⁿ μH[n](B̆_σ(a))`
  -- with `Λ = ‖L‖ + c/2`, which is finite since `μH[n]` is an additive Haar measure on `ℝⁿ`.
  · rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    refine ((hLip.mono hball_sub).hausdorffMeasure_image_le (Nat.cast_nonneg n)).trans_lt ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top)
      measure_ball_lt_top

/-- **Simon Ch. 3, proof of Lemma 1.2 (p. 70, last paragraph)**: the range of a `C¹` map
`G : ℝⁿ → ℝ^{n+ℓ}` lies in an `Hⁿ`-null set together with countably many `n`-dimensional `C¹`
submanifolds of finite `Hⁿ`-measure.
Proof: the critical values `N₀ = G({x | DG(x) not injective})` are `Hⁿ`-null.  Inside `B_R(0)`,
split the critical points into countably many disjoint pieces on which `G` is `ε`-close to a
linear map `A = DG(y)` (`y` critical, so `A u = 0` for a unit `u`, and `‖A‖ ≤ C` on `B_R(0)`).
For `B = id − (1 − ε) u ⊗ u` (so `det B = ε`, `A ∘ B = A` and `ε|w| ≤ |Bw|`), the map `G ∘ B⁻¹` is
`(C + 1)`-Lipschitz on the image of a piece under `B`, whence
`Hⁿ(G(piece)) ≤ (C + 1)ⁿ ε Hⁿ(piece)`; summing over the pieces and letting `ε → 0` gives
`Hⁿ(G(Crit ∩ B_R(0))) = 0`.  Each regular point `a` has a ball `B̆_{σ(a)}(a)` whose image is a
submanifold of finite measure (`rsod_c1_immersion_ball_isC1Submanifold`), and by Lindelöf
countably many of these balls cover the regular points. -/
theorem rsod_c1_range_subset_submanifold_cover : ∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ), ContDiff ℝ 1 G → ∃ (N₀ : Set (Amb n ℓ)) (N : ℕ → Set (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ q, IsC1Submanifold n (N q) ∧ (μHE[n] : Measure (Amb n ℓ)) (N q) < ∞) ∧ range G ⊆ N₀ ∪ ⋃ q, N q := by
  intro n ℓ G hG
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  -- Step 1 (critical values): `N₀ = G(Crit)` is `Hⁿ`-null.
  set Crit : Set (Rn n) := {x | DifferentiableAt ℝ G x ∧ ¬ Function.Injective (fderiv ℝ G x)}
  have hN₀ : (μHE[n] : Measure (Amb n ℓ)) (G '' Crit) = 0 := by
    -- `μHE[n]` is a constant multiple of `μH[n]`, and `Crit` is a countable union of bounded pieces.
    suffices h : (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' Crit) = 0 by
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h, smul_zero]
    have hcov : G '' Crit ⊆ ⋃ R : ℕ, G '' (Crit ∩ closedBall 0 R) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_closedBall_zero_iff.2 hR⟩, rfl⟩
    refine measure_mono_null hcov (measure_iUnion_null fun R => ?_)
    set s : Set (Rn n) := Crit ∩ closedBall 0 R with hs_def
    -- `‖DG‖ ≤ C` on `B_R(0)`; `K = C + 1` will be the Lipschitz constant.
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Rn n) R).exists_bound_of_continuousOn
      (hG.continuous_fderiv one_ne_zero).continuousOn
    set K : ℝ≥0 := Real.toNNReal (C + 1)
    have hK : C + 1 ≤ K := Real.le_coe_toNNReal _
    set D : ℝ≥0∞ := (K : ℝ≥0∞) ^ (n : ℝ) * (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R)
    -- Main estimate: `Hⁿ(G(s)) ≤ ε Kⁿ Hⁿ(B_R(0))` for every `ε ∈ (0, 1]`.
    have key : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
        (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' s) ≤ ε * D := by
      intro ε hε0 hε1
      rcases s.eq_empty_or_nonempty with hs | hs
      · rw [hs, image_empty, measure_empty]; exact zero_le
      -- Disjoint measurable pieces `s ∩ t k` on which `G` is `ε`-close to `A k = DG(y)`, `y ∈ s`.
      obtain ⟨t, A, htd, htm, hst, hA, hAy⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε0.ne')
      have piece : ∀ k, (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' (s ∩ t k)) ≤
          ε * ((K : ℝ≥0∞) ^ (n : ℝ) * (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R ∩ t k)) := by
        intro k
        obtain ⟨y, hy, hAk⟩ := hAy hs k
        have hAC : ‖A k‖ ≤ C := by rw [hAk]; exact hC y hy.2
        -- A unit vector `u` in the kernel of `A k = DG(y)`.
        obtain ⟨v, hv, hv0⟩ : ∃ v, A k v = 0 ∧ v ≠ 0 := by
          have h := hy.1.2
          rw [← hAk, injective_iff_map_eq_zero] at h
          obtain ⟨v, hv⟩ := not_forall.1 h
          exact ⟨v, not_imp.1 hv⟩
        set u : Rn n := ‖v‖⁻¹ • v
        have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
        have hAu : A k u = 0 := by simp [u, hv]
        have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
        have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
        have hε0' : (0 : ℝ) < ε := by exact_mod_cast hε0
        set c : ℝ := 1 - ε with hc_def
        have hc0 : 0 ≤ c := sub_nonneg.2 hε1'
        -- `B w = w − (1 − ε)⟨u, w⟩u` shrinks the kernel direction `u` by the factor `ε`.
        set B : Rn n →L[ℝ] Rn n :=
          ContinuousLinearMap.id ℝ (Rn n) - c • InnerProductSpace.rankOne ℝ u u
        have hB : ∀ w, B w = w - (c * inner ℝ u w) • u := by
          intro w
          simp [B, mul_smul]
        have hBinner : ∀ w, inner ℝ u (B w) = ε * inner ℝ u w := by
          intro w
          rw [hB, inner_sub_right, inner_smul_right, huu, hc_def]
          ring
        have hAB : ∀ w, A k (B w) = A k w := by
          intro w
          rw [hB, map_sub, map_smul, hAu, smul_zero, sub_zero]
        have hBlow : ∀ w, (ε : ℝ) * ‖w‖ ≤ ‖B w‖ := by
          intro w
          have h1 : ‖w‖ ≤ ‖B w‖ + c * |inner ℝ u w| := by
            have hw : w = B w + (c * inner ℝ u w) • u := by rw [hB]; abel
            calc ‖w‖ = ‖B w + (c * inner ℝ u w) • u‖ := congrArg norm hw
              _ ≤ ‖B w‖ + ‖(c * inner ℝ u w) • u‖ := norm_add_le _ _
              _ = ‖B w‖ + c * |inner ℝ u w| := by
                rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
          have h2 : (ε : ℝ) * |inner ℝ u w| ≤ ‖B w‖ := by
            have h := abs_real_inner_le_norm u (B w)
            rwa [hBinner, hu, one_mul, abs_mul, abs_of_pos hε0'] at h
          have h3 := mul_le_mul_of_nonneg_left h1 hε0'.le
          have h4 := mul_le_mul_of_nonneg_left h2 hc0
          nlinarith
        -- `Φ = G ∘ B⁻¹` is `K`-Lipschitz on `B(s ∩ t k)` and maps it onto `G(s ∩ t k)`.
        set Φ : Rn n → Amb n ℓ := fun z => G (z + (c / ε * inner ℝ u z) • u)
        have hΦ : ∀ x, Φ (B x) = G x := by
          intro x
          simp only [Φ]
          congr 1
          rw [hBinner, hB]
          have h : c / ε * (ε * inner ℝ u x) = c * inner ℝ u x := by
            field_simp
          rw [h, sub_add_cancel]
        have himage : G '' (s ∩ t k) = Φ '' (B '' (s ∩ t k)) := by
          rw [image_image]
          exact image_congr fun x _ => (hΦ x).symm
        have hLip : LipschitzOnWith K Φ (B '' (s ∩ t k)) := by
          refine LipschitzOnWith.of_dist_le_mul fun _ hx' _ hy' => ?_
          obtain ⟨x, hx, rfl⟩ := hx'
          obtain ⟨y, hy, rfl⟩ := hy'
          rw [hΦ, hΦ, dist_eq_norm, dist_eq_norm, ← map_sub]
          have happ : ‖G x - G y - A k (x - y)‖ ≤ ε * ‖x - y‖ := hA k x hx y hy
          have h1 : ‖G x - G y‖ ≤ ‖A k (x - y)‖ + ε * ‖x - y‖ := by
            have h := norm_add_le (G x - G y - A k (x - y)) (A k (x - y))
            rw [sub_add_cancel] at h
            linarith
          have h2 : ‖A k (x - y)‖ ≤ C * ‖B (x - y)‖ := by
            rw [← hAB]
            exact ((A k).le_opNorm _).trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg _))
          have h3 := hBlow (x - y)
          calc ‖G x - G y‖ ≤ (C + 1) * ‖B (x - y)‖ := by linarith
            _ ≤ K * ‖B (x - y)‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
        -- `det B = 1 − (1 − ε)|u|² = ε` (matrix determinant lemma in the standard basis).
        have hdet : LinearMap.det (B : Rn n →ₗ[ℝ] Rn n) = ε := by
          set b := EuclideanSpace.basisFun (Fin n) ℝ
          rw [← LinearMap.det_toMatrix b.toBasis]
          have h1 : LinearMap.toMatrix b.toBasis b.toBasis (B : Rn n →ₗ[ℝ] Rn n) =
              1 + Matrix.replicateCol Unit (fun i => -c * u i) *
                Matrix.replicateRow Unit (fun i => u i) := by
            ext i j
            rw [LinearMap.toMatrix_apply]
            simp [B, b, Matrix.one_apply, EuclideanSpace.inner_single_right, Matrix.replicateCol,
              Matrix.replicateRow, Matrix.mul_apply]
            ring
          rw [h1, Matrix.det_one_add_replicateCol_mul_replicateRow]
          have h2 : ∑ i, u i ^ 2 = 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
          simp only [dotProduct]
          have h3 : ∑ i, u i * (-c * u i) = -c * ∑ i, u i ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [h3, h2, hc_def]
          ring
        calc (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' (s ∩ t k))
            = (μH[(n : ℝ)] : Measure (Amb n ℓ)) (Φ '' (B '' (s ∩ t k))) := by rw [himage]
          _ ≤ (K : ℝ≥0∞) ^ (n : ℝ) * (μH[(n : ℝ)] : Measure (Rn n)) (B '' (s ∩ t k)) :=
            hLip.hausdorffMeasure_image_le (Nat.cast_nonneg n)
          _ = (K : ℝ≥0∞) ^ (n : ℝ) * (ε * (μH[(n : ℝ)] : Measure (Rn n)) (s ∩ t k)) := by
            rw [Measure.addHaar_image_continuousLinearMap, hdet, abs_of_nonneg ε.coe_nonneg,
              ENNReal.ofReal_coe_nnreal]
          _ ≤ (K : ℝ≥0∞) ^ (n : ℝ) *
              (ε * (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R ∩ t k)) := by
            gcongr
            exact inter_subset_right
          _ = ε * ((K : ℝ≥0∞) ^ (n : ℝ) *
              (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R ∩ t k)) := by
            ring
      calc (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' s)
          ≤ (μH[(n : ℝ)] : Measure (Amb n ℓ)) (⋃ k, G '' (s ∩ t k)) := by
            refine measure_mono ?_
            rintro _ ⟨x, hx, rfl⟩
            obtain ⟨k, hk⟩ := mem_iUnion.1 (hst hx)
            exact mem_iUnion.2 ⟨k, x, ⟨hx, hk⟩, rfl⟩
        _ ≤ ∑' k, (μH[(n : ℝ)] : Measure (Amb n ℓ)) (G '' (s ∩ t k)) := measure_iUnion_le _
        _ ≤ ∑' k, ε * ((K : ℝ≥0∞) ^ (n : ℝ) *
              (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R ∩ t k)) :=
            ENNReal.tsum_le_tsum piece
        _ = ε * ((K : ℝ≥0∞) ^ (n : ℝ) *
              (μH[(n : ℝ)] : Measure (Rn n)) (⋃ k, closedBall 0 R ∩ t k)) := by
            rw [measure_iUnion (fun i j hij => (htd hij).mono inter_subset_right inter_subset_right)
              (fun k => measurableSet_closedBall.inter (htm k)), ENNReal.tsum_mul_left,
              ENNReal.tsum_mul_left]
        _ ≤ ε * D := by
            show _ ≤ ε * ((K : ℝ≥0∞) ^ (n : ℝ) * (μH[(n : ℝ)] : Measure (Rn n)) (closedBall 0 R))
            gcongr
            exact iUnion_subset fun k => inter_subset_left
    -- Letting `ε → 0` gives `Hⁿ(G(s)) = 0`, since `D < ∞`.
    have hD : D ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top)
        measure_closedBall_lt_top.ne
    have hlim : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * D) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) :=
        (ENNReal.continuous_coe.tendsto' 0 0 ENNReal.coe_zero).mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hD)
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    exact key ε hε.1 hε.2
  -- Step 2 (regular points): the image of a small ball around each one is a submanifold patch.
  set Reg : Set (Rn n) := {x | Function.Injective (fderiv ℝ G x)}
  have hcrit : ∀ x, x ∉ Reg → G x ∈ G '' Crit := fun x hx => ⟨x, ⟨hdiff x, hx⟩, rfl⟩
  choose! σ hσ hσsub hσfin using fun a (ha : a ∈ Reg) =>
    Submission.rsod_c1_immersion_ball_isC1Submanifold n ℓ G a hG ha
  -- Step 3 (Lindelöf): countably many of the balls `B̆_{σ(a)}(a)`, `a ∈ Reg`, cover `Reg`.
  obtain ⟨T, hTReg, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun a => ball a (σ a)) (s := Reg)
    fun a ha => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (hσ a ha))
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- Step 4, no regular points: every value is critical, and the patches are empty.
    refine ⟨G '' Crit, fun _ => ∅, hN₀,
      fun _ => ⟨fun y hy => absurd hy (notMem_empty y), by simp⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine Or.inl (hcrit x fun hx => ?_)
    simpa [hT] using hcover hx
  · -- Step 4: enumerate the patches `G(B̆_{σ(a)}(a))`, `a ∈ T`; Step 5: they cover `G(Reg)`.
    obtain ⟨e, rfl⟩ := hTc.exists_eq_range hT
    refine ⟨G '' Crit, fun q => G '' ball (e q) (σ (e q)), hN₀,
      fun q => ⟨hσsub _ (hTReg (mem_range_self q)), hσfin _ (hTReg (mem_range_self q))⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ Reg
    · obtain ⟨_, ⟨q, rfl⟩, hxq⟩ := mem_iUnion₂.1 (hcover hx)
      exact Or.inr (mem_iUnion.2 ⟨q, mem_image_of_mem G hxq⟩)
    · exact Or.inl (hcrit x hx)
/-- **Simon Ch. 3, Lemma 1.2 ("only if").**  A countably `n`-rectifiable `M ⊆ ℝ^{n+ℓ}` lies in
`N₀ ∪ ⋃_j N_j` with `Hⁿ(N₀) = 0` and each `N_j` an `n`-dimensional `C¹` submanifold of finite
`Hⁿ`-measure.  Write `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `F_j` Lipschitz; each `F_j(ℝⁿ)`
lies in an `Hⁿ`-null set and countably many `C¹` images `G_{j,k}(ℝⁿ)`
(`rsod_lipschitz_range_subset_c1_ranges`, Simon 2.1.5 and the first half of 3.1.2), and each
`G_{j,k}(ℝⁿ)` lies in an `Hⁿ`-null set (critical values) and countably many finite-measure patches
`N^{j,k}_q` (`rsod_c1_range_subset_submanifold_cover`).  The patches are enumerated by
`p ↦ (j, (k, q))` through `Nat.unpair`. -/
theorem rsod_rectifiable_subset_c1_cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N₀ : Set (Amb n ℓ)) (N : ℕ → Set (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ j, IsC1Submanifold n (N j) ∧ (μHE[n] : Measure (Amb n ℓ)) (N j) < ∞) ∧ M ⊆ N₀ ∪ ⋃ j, N j := by
  intro n ℓ _ M hM
  -- Step 1: `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and every `F_j` Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hM
  choose K hK using hF
  -- Steps 2–3 (child `lipschitz_range_c1_cover`): `F_j(ℝⁿ) ⊆ Z_j ∪ ⋃_k G_{j,k}(ℝⁿ)`, `Hⁿ(Z_j) = 0`.
  choose Z G hZ hG hFG using fun j =>
    Submission.rsod_lipschitz_range_subset_c1_ranges n ℓ (F j) (K j) (hK j)
  -- Steps 4–6 (child `c1_range_submanifold_cover`): `G_{j,k}(ℝⁿ) ⊆ Y_{j,k} ∪ ⋃_q P_{j,k,q}`,
  -- `Hⁿ(Y_{j,k}) = 0`, each `P_{j,k,q}` a finite-measure `C¹` submanifold.
  choose Y P hY hP hGP using fun j k =>
    Submission.rsod_c1_range_subset_submanifold_cover n ℓ (G j k) (hG j k)
  -- Step 7: `N₀ = M₀ ∪ ⋃_j Z_j ∪ ⋃_{j,k} Y_{j,k}` and `N_p = P_{j,k,q}` for `p = ⟨j, ⟨k, q⟩⟩`.
  refine ⟨M₀ ∪ (⋃ j, Z j) ∪ ⋃ j, ⋃ k, Y j k,
    fun p => P p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2,
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hZ))
      (measure_iUnion_null fun j => measure_iUnion_null (hY j)),
    fun p => hP _ _ _, ?_⟩
  intro x hx
  rcases hMF hx with hx₀ | hx
  · exact Or.inl (Or.inl (Or.inl hx₀))
  obtain ⟨j, hj⟩ := mem_iUnion.1 hx
  rcases hFG j hj with hxZ | hx
  · exact Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨j, hxZ⟩)))
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  rcases hGP j k hk with hxY | hx
  · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨j, k, hxY⟩))
  obtain ⟨q, hq⟩ := mem_iUnion.1 hx
  refine Or.inr (mem_iUnion.2 ⟨Nat.pair j (Nat.pair k q), ?_⟩)
  simpa only [Nat.unpair_pair] using hq
/-- **Simon Ch. 3, Theorem 1.9 "⇒"** for `V = v(M, θ)` with `θ ≥ 1` `μ_V`-a.e.: `M` has an
approximate tangent space with respect to `θ` (Ch. 3, Definition 1.7) at `μ_V`-a.e. point.
Near each `y ∈ U` replace `M` by a Borel `A ⊆ M ∩ B_{ε/2}(y)` with `Hⁿ((M ∩ B_{ε/2}(y)) \ A) = 0`
(of finite measure, as `θ ≥ 1` is integrable there) and `θ` by a Borel representative `θ'`.  The
`C¹` cover of `M` (Lemma 1.2) gives unweighted tangent planes a.e. on closed subsets of `A`
(Theorem 1.6 "⇒"), Remark 1.8(1) gives the weighted ones for `(A, θ')`, and Definition 1.7 only
sees the germ at `x` modulo `Hⁿ`-null sets, so they are tangent planes of `(M, θ)` near `y`.
Second countability makes the exceptional set `Hⁿ`-null, and `μ_V ≪ Hⁿ ⌞ M`. -/
theorem rsod_ae_exists_approxTangent : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
  intro n ℓ hn U hU V hθ1
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set M := V.carrier
  set θ := V.mult
  have hM : NullMeasurableSet M μ := V.nullMeasurableSet_carrier
  -- `μ_V ≪ Hⁿ ⌞ M`, and `Hⁿ ⌞ M ≪ μ_V` because `θ > 0` on `M`; so `θ ≥ 1` `Hⁿ`-a.e. on `M`.
  have hac : V.weight ≪ μ.restrict M := withDensity_absolutelyContinuous _ _
  have hac' : μ.restrict M ≪ V.weight :=
    withDensity_absolutelyContinuous' V.aemeasurable_mult.ennreal_ofReal
      ((ae_restrict_mem₀ hM).mono fun x hx => (ENNReal.ofReal_pos.mpr (V.mult_pos x hx)).ne')
  have hθ1M : ∀ᵐ x ∂μ.restrict M, 1 ≤ θ x := hac'.ae_le hθ1
  -- A Borel representative `θ'` of `θ`; the two differ on `M` only in the null set `Z₁`.
  set θ' := V.aemeasurable_mult.mk θ
  have hθ'meas : Measurable θ' := V.aemeasurable_mult.measurable_mk
  have hθθ' : θ =ᵐ[μ.restrict M] θ' := V.aemeasurable_mult.ae_eq_mk
  set Z₁ := {x | θ x ≠ θ' x} ∩ M with hZ₁def
  have hZ₁ : μ Z₁ = 0 := by
    rw [hZ₁def, ← Measure.restrict_apply₀' hM]
    exact ae_iff.mp hθθ'
  -- Simon Ch. 3, Lemma 1.2: `M ⊆ N₀ ∪ ⋃ⱼ Nⱼ` with `Hⁿ(N₀) = 0` and `C¹` submanifolds `Nⱼ`.
  obtain ⟨N₀, N, hN₀, hN, hcover⟩ :=
    Submission.rsod_rectifiable_subset_c1_cover n ℓ hn M V.countablyRectifiable
  -- Each `y ∈ U` has an open neighbourhood `O` such that a.e. point of `M ∩ O` is good.
  have hloc : ∀ y ∈ U, ∃ O : Set (Amb n ℓ), IsOpen O ∧ y ∈ O ∧
      ∀ᵐ x ∂μ, x ∈ M → x ∈ O → ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P := by
    intro y hy
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y hy
    set L := closedBall y (ε / 2)
    set O := ball y (ε / 2)
    have hLU : L ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hOL : O ⊆ L := ball_subset_closedBall
    -- `Hⁿ(M ∩ L) ≤ ∫_{M ∩ L} θ dHⁿ < ∞`, since `θ ≥ 1` a.e. on `M`.
    have hint : IntegrableOn θ (M ∩ L) μ :=
      V.integrableOn_mult L (isCompact_closedBall y (ε / 2)) hLU
    have hfinML : μ (M ∩ L) < ∞ :=
      calc μ (M ∩ L) = ∫⁻ _, 1 ∂μ.restrict (M ∩ L) := by
            rw [lintegral_one, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ x, ENNReal.ofReal (θ x) ∂μ.restrict (M ∩ L) :=
          lintegral_mono_ae ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hθ1M).mono
            fun x hx => ENNReal.one_le_ofReal.mpr hx)
        _ < ∞ := hint.setLIntegral_lt_top
    -- A Borel `A ⊆ M ∩ L` with `Hⁿ((M ∩ L) \ A) = 0`; `θ'` is integrable on `A`.
    obtain ⟨A, hAsub, hAmeas, hAae⟩ :=
      (hM.inter measurableSet_closedBall.nullMeasurableSet).exists_measurable_subset_ae_eq
    have hdiff : μ ((M ∩ L) \ A) = 0 := ae_le_set.mp hAae.symm.le
    have hfinA : μ A < ∞ := (measure_mono hAsub).trans_lt hfinML
    have hintA : IntegrableOn θ' A μ :=
      (hint.congr_fun_ae (ae_restrict_of_ae_restrict_of_subset inter_subset_left hθθ')).mono_set
        hAsub
    -- Theorem 1.6 "⇒" on every closed `K ⊆ A`, then Remark 1.8(1) for `(A, θ')`.
    have hWA := Submission.rsod_ae_weightedApproxTangent_of_unweighted n ℓ A θ' hAmeas hfinA
      hθ'meas hintA fun K hK hKA =>
        Submission.rsod_ae_approxTangent_of_c1Cover n ℓ hn K N₀ N hK.measurableSet
          ((measure_mono hKA).trans_lt hfinA) hN₀ hN fun z hz => hcover (hAsub (hKA hz)).1
    -- Off the null set `Z`, `(A, θ')` and `(M, θ)` agree on `O`.
    set Z := ((M ∩ L) \ A) ∪ Z₁
    have hZ : μ Z = 0 := measure_union_null hdiff hZ₁
    have hmemA : ∀ z, z ∈ M → z ∈ O → z ∉ Z → z ∈ A := fun z hzM hzO hzZ => by
      by_contra hzA
      exact hzZ (Or.inl ⟨⟨hzM, hOL hzO⟩, hzA⟩)
    have heqθ : ∀ z, z ∈ M → z ∉ Z → θ' z = θ z := fun z hzM hzZ => by
      by_contra hne
      exact hzZ (Or.inr ⟨fun h => hne h.symm, hzM⟩)
    have hAM : (A ∩ O) \ Z = (M ∩ O) \ Z := by
      ext z
      constructor
      · rintro ⟨⟨hzA, hzO⟩, hzZ⟩
        exact ⟨⟨(hAsub hzA).1, hzO⟩, hzZ⟩
      · rintro ⟨⟨hzM, hzO⟩, hzZ⟩
        exact ⟨⟨hmemA z hzM hzO hzZ, hzO⟩, hzZ⟩
    refine ⟨O, isOpen_ball, mem_ball_self (half_pos hε), ?_⟩
    filter_upwards [hWA, measure_eq_zero_iff_ae_notMem.mp hZ] with x hxW hxZ hxM hxO
    obtain ⟨P, hP⟩ := hxW (hmemA x hxM hxO hxZ)
    exact ⟨P, Submission.rsod_weightedApproxTangent_congr n ℓ A M O Z θ' θ x P
      hAmeas.nullMeasurableSet isOpen_ball hxO hZ hAM
      (fun z hz => heqθ z (hAsub hz.1.1).1 hz.2) (heqθ x hxM hxZ) hP⟩
  -- The bad points of `M ⊆ U` are locally `Hⁿ`-null, hence `Hⁿ`-null (second countability).
  have hbad : μ {x | x ∈ M ∧ ¬∃ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P} = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨O, hO, hxO, hgood⟩ := hloc x (V.carrier_subset hx.1)
    refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds hxO), measure_mono_null ?_ (ae_iff.mp hgood)⟩
    rintro z ⟨⟨hzM, hzbad⟩, hzO⟩ hz
    exact hzbad (hz hzM hzO)
  -- So a.e. point of `M` is good for `Hⁿ ⌞ M`, hence for `μ_V ≪ Hⁿ ⌞ M`.
  refine hac.ae_le ((ae_restrict_iff'₀ hM).mpr (ae_iff.mpr (measure_mono_null ?_ hbad)))
  intro x hx
  exact not_imp.mp hx
/-- **Least integer density in a ball** (proof of Simon Ch. 5, Corollary 7.3, step 4: the choice
`N = min{j ≥ 1 : Θⁿ(μ_V, x) = j for some x ∈ B̆_r(ξ)}`).  If `Θⁿ(μ_V, x) = θ(x)` and `θ(x)` is a
positive integer for `μ_V`-a.e. `x`, then for `ξ ∈ spt V` and `r > 0` some `x₀ ∈ B̆_r(ξ)` has
`Θⁿ(μ_V, x₀) = N` for an integer `N ≥ 1` with `θ ≥ N` `μ_V`-a.e. on `B̆_r(ξ)`. -/
theorem rsod_exists_least_integer_density_point : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) →
    (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ V.support, ∀ r : ℝ, 0 < r →
    ∃ (N : ℕ) (x₀ : Amb n ℓ), 1 ≤ N ∧ x₀ ∈ ball ξ r ∧ V.HasDensity x₀ N ∧
      ∀ᵐ x ∂V.weight, x ∈ ball ξ r → (N : ℝ) ≤ V.mult x := by
  intro n ℓ U V hdens hint ξ hξ r hr
  classical
  -- `μ_V(B̆_r(ξ)) > 0`, since `ξ ∈ spt μ_V` and `B̆_r(ξ)` is a neighbourhood of `ξ`.
  have hpos : 0 < V.weight (ball ξ r) :=
    (Measure.mem_support_iff_forall ξ).1 hξ.2 _ (ball_mem_nhds ξ hr)
  -- Otherwise `μ_V`-a.e. point, having integer density `θ(x) ≥ 1`, would lie outside the ball.
  have hJ : ∃ k : ℕ, 1 ≤ k ∧ ∃ x ∈ ball ξ r, V.HasDensity x k := by
    by_contra hJ
    refine hpos.ne' (measure_eq_zero_iff_ae_notMem.2 ?_)
    filter_upwards [hdens, hint] with x hx ⟨k, hk, hxk⟩ hxB
    exact hJ ⟨k, hk, x, hxB, hxk ▸ hx⟩
  -- The least such `N` is attained at some `x₀`, and bounds `θ` below `μ_V`-a.e. on the ball.
  obtain ⟨hN, x₀, hx₀, hx₀N⟩ := Nat.find_spec hJ
  refine ⟨Nat.find hJ, x₀, hN, hx₀, hx₀N, ?_⟩
  filter_upwards [hdens, hint] with x hx ⟨k, hk, hxk⟩ hxB
  rw [hxk]
  exact Nat.cast_le.2 (Nat.find_min' hJ ⟨hk, x, hxB, hxk ▸ hx⟩)

/-- **Regular points are dense in `spt V`** (Simon Ch. 5, Corollary 7.3, density half, p. 129).
Assuming Allard's theorem 5.2: if `V = v(M, θ)` has generalized mean curvature `H` in the open set
`U`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`, and `θ` is a positive integer `μ_V`-a.e. on
`spt V`, then every open ball `B̆_r(ξ)` with `ξ ∈ spt V` meets `reg V`.  Normalize `V` by the least
integer density `N` in a smaller ball `B̆_{r'}(ξ) ⊆ U` and apply 7.1 at a point of density `1`. -/
theorem rsod_regularSet_meets_ball : AllardRegularityTheorem → ∀ (n ℓ : ℕ), 1 ≤ n →
    ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H →
    V.LocallyLp H p → (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    ∀ ξ ∈ V.support, ∀ r : ℝ, 0 < r → (V.regularSet ∩ ball ξ r).Nonempty := by
  intro hAllard n ℓ hn U hU V H p hp hH hLp hint ξ hξ r hr
  -- `μ_V ≪ Hⁿ ⌞ M` and `M ⊆ U`, so `μ_V`-a.e. point lies in `U ∩ spt μ_V = spt V`.
  have hM_ae : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hU_ae : ∀ᵐ x ∂V.weight, x ∈ U := hM_ae.mono fun _ hx => V.carrier_subset hx
  have hspt_ae : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    filter_upwards [hU_ae, Measure.support_mem_ae (μ := V.weight)] with x hxU hx
    exact ⟨hxU, hx⟩
  -- Hence `θ` is a positive integer `μ_V`-a.e.; in particular `θ ≥ 1` `μ_V`-a.e.
  have hI : ∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k := by
    filter_upwards [hint, hspt_ae] with x hx hxV using hx hxV
  have hθ : ∀ᵐ x ∂V.weight, 1 ≤ V.mult x := by
    filter_upwards [hI] with x ⟨k, hk, hxk⟩
    rw [hxk]
    exact_mod_cast hk
  -- `Θⁿ(μ_V, x) = θ(x)` `μ_V`-a.e., via approximate tangent planes (Ch. 3, 1.9 and Remark 1.8(2)).
  have hdens : ∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x) := by
    filter_upwards [Submission.rsod_ae_exists_approxTangent n ℓ hn U hU V hθ, hU_ae]
      with x ⟨P, hP⟩ hxU
    exact Submission.rsod_hasDensity_of_approxTangent n ℓ hn U hU V x P hxU hP
  -- Shrink the ball into `U`: `B = B̆_{r'}(ξ)` with `r' ≤ r` and `B ⊆ U`.
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU ξ hξ.1
  obtain ⟨r', hr', hr'r, hBU⟩ : ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ball ξ r' ⊆ U :=
    ⟨min r r₀, lt_min hr hr₀, min_le_left _ _, (ball_subset_ball (min_le_right _ _)).trans hr₀U⟩
  -- The least integer density `N ≥ 1` in `B` is attained at some `x₀ ∈ B`, and `θ ≥ N` a.e. on `B`.
  obtain ⟨N, x₀, hN, hx₀, hx₀N, hNθ⟩ :=
    Submission.rsod_exists_least_integer_density_point n ℓ U V hdens hI ξ hξ r' hr'
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast hN
  -- The normalized varifold `W = v(M ∩ B, θ / N)` in `B`.
  obtain ⟨W, -, hWmult, hWweight, hWsupp, hWH, hWLp⟩ :=
    Submission.rsod_exists_localized_varifold n ℓ U V (ball ξ r') (1 / (N : ℝ)) isOpen_ball hBU
      (one_div_pos.2 hN₀)
  -- `θ / N ≥ 1` `μ_W`-a.e.
  have hWθ : ∀ᵐ x ∂W.weight, 1 ≤ W.mult x := by
    rw [hWweight]
    refine Measure.ae_smul_measure ((ae_restrict_iff' measurableSet_ball).2 ?_) _
    filter_upwards [hNθ] with x hx hxB
    rw [hWmult, one_div_mul_eq_div, one_le_div₀ hN₀]
    exact hx hxB
  -- `B_s(x₀) ⊆ B` for `s < d`, so `μ_W(B_s(x₀)) = N⁻¹ μ_V(B_s(x₀))` and `Θⁿ(μ_W, x₀) = N / N = 1`.
  obtain ⟨d, hd, hdB⟩ := Metric.isOpen_iff.1 isOpen_ball x₀ hx₀
  have hWdens : W.HasDensity x₀ 1 := by
    have hc : ENNReal.ofReal (1 / (N : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlim := ENNReal.Tendsto.const_mul hx₀N (Or.inr hc)
    rw [← ENNReal.ofReal_mul (one_div_pos.2 hN₀).le, one_div_mul_cancel hN₀.ne'] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with s hs
    rw [hWweight, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.2 ((closedBall_subset_ball hs.2).trans hdB), mul_div_assoc]
  -- By 7.1 (via Allard's theorem) `x₀` is a regular point of `W`.
  obtain ⟨hx₀W, ρ, hρ, hC1⟩ :=
    Submission.rsod_mem_regularSet_of_density_one hAllard n ℓ hn (ball ξ r') isOpen_ball W H p hp
      (hWH H hH) (hWLp H p hLp) hWθ x₀ hx₀ hWdens
  rw [hWsupp] at hx₀W hC1
  -- Shrinking the radius to `min ρ d` transfers regularity from `W` to `V`.
  refine ⟨x₀, ⟨hx₀W.2, min ρ d, lt_min hρ hd, ?_⟩, ball_subset_ball hr'r hx₀⟩
  have hball : ball x₀ (min ρ d) ∩ V.support =
      ball x₀ (min ρ d) ∩ (ball x₀ ρ ∩ (ball ξ r' ∩ V.support)) := by
    ext y
    constructor
    · rintro ⟨hy, hyV⟩
      exact ⟨hy, ball_subset_ball (min_le_left _ _) hy,
        hdB (ball_subset_ball (min_le_right _ _) hy), hyV⟩
    · rintro ⟨hy, -, -, hyV⟩
      exact ⟨hy, hyV⟩
  rw [hball]
  exact Submission.rsod_isC1Submanifold_open_inter n (n + ℓ) _ _ hC1 isOpen_ball

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

/-- **Simon Ch. 5, 7.2** (p. 128): "by definition `reg V` is relatively open in `spt V`".  `O` is
the union of chosen regular balls `B̆_{ρ_y}(y)`, `y ∈ reg V`; a point `z ∈ B̆_{ρ_y}(y) ∩ spt V` is
regular with radius `ρ_y − |z − y|`, since `C¹` submanifolds restrict to open sets
(`rsod_isC1Submanifold_open_inter`). -/
theorem rsod_regularSet_relOpen : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U),
    ∃ O : Set (Amb n ℓ), IsOpen O ∧ V.regularSet = O ∩ V.support := by
  intro n ℓ U V
  -- Step 1: fix a regular radius `ρ y` at each `y ∈ reg V`; `O` is the union of these balls.
  have hreg : ∀ y ∈ V.regularSet, ∃ ρ > 0, IsC1Submanifold n (ball y ρ ∩ V.support) :=
    fun y hy => hy.2
  choose! ρ hρ hρreg using hreg
  refine ⟨⋃ y ∈ V.regularSet, ball y (ρ y), isOpen_biUnion fun y _ => isOpen_ball, ?_⟩
  ext z
  -- Step 2: `reg V ⊆ O ∩ spt V`, since `z ∈ B̆_{ρ z}(z)`.
  refine ⟨fun hz => ⟨mem_biUnion hz (mem_ball_self (hρ z hz)), hz.1⟩, ?_⟩
  -- Step 3: `z ∈ B̆_{ρ y}(y) ∩ spt V` is regular with radius `r = ρ y - dist z y`, because
  -- `B̆_r(z) ⊆ B̆_{ρ y}(y)` gives `B̆_r(z) ∩ spt V = B̆_r(z) ∩ (B̆_{ρ y}(y) ∩ spt V)`.
  rintro ⟨hzO, hz⟩
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzO
  have hsub : ball z (ρ y - dist z y) ⊆ ball y (ρ y) := ball_subset_ball' (sub_add_cancel _ _).le
  refine ⟨hz, ρ y - dist z y, sub_pos.2 (mem_ball.1 hzy), ?_⟩
  rw [← inter_eq_left.2 hsub, inter_assoc]
  exact Submission.rsod_isC1Submanifold_open_inter _ _ _ _ (hρreg y hy) isOpen_ball

end Submission

end GMT.Ch05
