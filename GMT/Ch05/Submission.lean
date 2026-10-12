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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
