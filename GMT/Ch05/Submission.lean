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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
