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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
