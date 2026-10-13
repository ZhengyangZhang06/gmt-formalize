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
