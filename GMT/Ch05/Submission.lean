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

/-- Choice of the constants `δ_P, C_P` for the density bounds in the proof of Simon Ch. 5, 5.2
(pure real analysis; `κ > 0`, `ω > 0` arbitrary).  With `Λ = t/κ` and `q = (1 + t)/(1 − 3t)ⁿ`, the
functions `G₊ = e^{2Λ} qω + 2e^Λ Λ`, `G₋ = e^{−Λ}(ω − Λ)` and `G_c = e^Λ(e^Λ qω + Λ − ω)` are `C¹` on
`(−1/24, 1/4)` (where `1 − 3t > 1/4`) with `G₊(0) = G₋(0) = ω`, `G_c(0) = 0`; bounding their
derivatives by `A` on `[0, t₀]`, `t₀ = min{1/8, κ}`, the mean value theorem gives the three bounds
for `0 < t ≤ δ_P` with `C_P = max{1, A/ω}` and `δ_P = min{t₀, 1/(2C_P)}`. -/
theorem allard52_density_constants : ∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ δP ≤ κ ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δP → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + CP * t) * ω ∧ (1 - CP * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω) ≤ CP * ω * t := by
  intro n κ ω hκ hω
  -- The radius `t₀ = min (1/8) κ`; `[0, t₀]` sits inside the open interval `I = (-1/24, 1/4)`,
  -- on which `1 - 3 t > 1/4 > 0`.
  obtain ⟨t₀, ht₀pos, ht₀le, ht₀κ⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 / 8 ∧ t₀ ≤ κ :=
    ⟨min (1 / 8) κ, lt_min (by norm_num) hκ, min_le_left _ _, min_le_right _ _⟩
  have hsub : Icc (0 : ℝ) t₀ ⊆ Ioo (-1 / 24 : ℝ) (1 / 4) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- Mean value inequality for a `C¹` function on `I`: its derivative is bounded on the compact
  -- `[0, t₀]` by some `A`, hence `|G t - G 0| ≤ A t` for `t ∈ [0, t₀]`.
  have key : ∀ G : ℝ → ℝ, ContDiffOn ℝ 1 G (Ioo (-1 / 24 : ℝ) (1 / 4)) →
      ∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) t₀, |G t - G 0| ≤ A * t := by
    intro G hG
    have hcont : ContinuousOn (deriv G) (Ioo (-1 / 24 : ℝ) (1 / 4)) :=
      hG.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t₀)).exists_bound_of_continuousOn
      (hcont.mono hsub)
    refine ⟨A, fun t ht => ?_⟩
    have hdiff : ∀ x ∈ Icc (0 : ℝ) t₀, DifferentiableAt ℝ G x := fun x hx =>
      (hG.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
    have h := (convex_Icc (0 : ℝ) t₀).norm_image_sub_le_of_norm_deriv_le hdiff hA
      (left_mem_Icc.2 ht₀pos.le) ht
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
  -- Smoothness of `G₊`, `G₋`, `G_c` on `I`: the denominator `(1 - 3 t)ⁿ` has no zero there.
  have hden : ∀ x ∈ Ioo (-1 / 24 : ℝ) (1 / 4), (1 - 3 * x) ^ n ≠ 0 := fun x hx =>
    pow_ne_zero _ (by linarith [hx.2] : (0 : ℝ) < 1 - 3 * x).ne'
  have hR : ContDiffOn ℝ 1 (fun t : ℝ => (1 + t) / (1 - 3 * t) ^ n * ω)
      (Ioo (-1 / 24 : ℝ) (1 / 4)) := by
    apply ContDiffOn.mul _ contDiffOn_const
    exact ContDiffOn.fun_div (by fun_prop) (by fun_prop) hden
  have hE : ContDiff ℝ 1 (fun t : ℝ => Real.exp (t / κ)) := by fun_prop
  have hE2 : ContDiff ℝ 1 (fun t : ℝ => Real.exp (2 * (t / κ))) := by fun_prop
  obtain ⟨A₁, hA₁⟩ := key (fun t => Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) +
      2 * Real.exp (t / κ) * (t / κ)) ((hE2.contDiffOn.mul hR).add (by fun_prop))
  obtain ⟨A₂, hA₂⟩ := key (fun t => Real.exp (-(t / κ)) * (ω - t / κ)) (by fun_prop)
  obtain ⟨A₃, hA₃⟩ := key (fun t => Real.exp (t / κ) *
      (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))
    (hE.contDiffOn.mul (((hE.contDiffOn.mul hR).add (by fun_prop)).sub contDiffOn_const))
  -- The constants: one bound `A` for the three derivatives, `C_P = max 1 (A/ω)` and
  -- `δ_P = min t₀ (1/(2 C_P))`.
  obtain ⟨A, hA1, hA2, hA3⟩ : ∃ A : ℝ, A₁ ≤ A ∧ A₂ ≤ A ∧ A₃ ≤ A :=
    ⟨max (max A₁ A₂) A₃, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨CP, hCP1, hCPA⟩ : ∃ CP : ℝ, 1 ≤ CP ∧ A ≤ CP * ω :=
    ⟨max 1 (A / ω), le_max_left _ _, (div_le_iff₀ hω).1 (le_max_right _ _)⟩
  have hCPpos : 0 < CP := lt_of_lt_of_le one_pos hCP1
  refine ⟨min t₀ (1 / (2 * CP)), CP, lt_min ht₀pos (by positivity),
    le_trans (min_le_left _ _) ht₀le, le_trans (min_le_left _ _) ht₀κ, hCPpos, ?_, ?_⟩
  · calc CP * min t₀ (1 / (2 * CP)) ≤ CP * (1 / (2 * CP)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCPpos.le
      _ = 1 / 2 := by field_simp
  · intro t ht htδ
    have htI : t ∈ Icc (0 : ℝ) t₀ := ⟨ht.le, le_trans htδ (min_le_left _ _)⟩
    have h1 := hA₁ t htI
    have h2 := hA₂ t htI
    have h3 := hA₃ t htI
    -- Values at `0`: `G₊(0) = G₋(0) = ω` and `G_c(0) = 0`.
    simp only [zero_div, mul_zero, neg_zero, Real.exp_zero, add_zero, sub_zero, one_pow, div_one,
      one_mul, mul_one, sub_self] at h1 h2 h3
    have hAt : A * t ≤ CP * ω * t := mul_le_mul_of_nonneg_right hCPA ht.le
    have h1' : A₁ * t ≤ A * t := mul_le_mul_of_nonneg_right hA1 ht.le
    have h2' : A₂ * t ≤ A * t := mul_le_mul_of_nonneg_right hA2 ht.le
    have h3' : A₃ * t ≤ A * t := mul_le_mul_of_nonneg_right hA3 ht.le
    refine ⟨?_, ?_, ?_⟩
    · linarith [(abs_le.1 h1).2]
    · linarith [(abs_le.1 h2).1]
    · linarith [le_abs_self (Real.exp (t / κ) *
        (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))]
/-- Simon Ch. 5, hypotheses 2.3 restricted to a sub-ball `B_r(z) ⊆ B_ρ(0)` with `0 < r ≤ ρ`:
`B_r(z) ⊆ U`, `∫_{B_r(z)} |H|ᵖ dμ_V < ∞`, `(r^{p−n} ∫_{B_r(z)} |H|ᵖ dμ_V)^{1/p} ≤ δ` and
`μ_V(B_r(z)) ≤ (1 + δ) ω_n ρⁿ`.  Since `p > n ≥ 0`, both exponents `p − n` and `1/p` are positive,
so the scaled `Lᵖ` norm is monotone under shrinking the ball, and its finiteness on `B_ρ(0)` with
`ρ^{p−n} > 0` forces `∫_{B_ρ(0)} |H|ᵖ dμ_V < ∞`. -/
theorem aal_allard_subball_bounds : ∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), V.AllardHypotheses H p δ ρ → ∀ (z : Amb n ℓ) (r : ℝ), 0 < r → r ≤ ρ → closedBall z r ⊆ closedBall 0 ρ → closedBall z r ⊆ U ∧ ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight < ⊤ ∧ V.scaledLpNorm H p z r ≤ ENNReal.ofReal δ ∧ V.weight (closedBall z r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) := by
  intro n ℓ p hp U V H δ ρ hA z r hr hrρ hball
  obtain ⟨hρ, -, -, -, hU, hmass, hK⟩ := hA
  -- `p > n ≥ 0`, so `p - n > 0` and `1 / p > 0`.
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp' : 0 < 1 / p := one_div_pos.mpr ((Nat.cast_nonneg n).trans_lt hp)
  -- `I(z, r) ≤ I(0, ρ)` by monotonicity of the lower integral in the domain.
  have hI : ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight ≤
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight := lintegral_mono_set hball
  -- `K(0, ρ) = (ρ^{p−n} I(0, ρ))^{1/p} ≤ δ < ∞` forces `ρ^{p−n} I(0, ρ) < ∞`.
  have hK' : (ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤ ENNReal.ofReal δ := hK
  have hfin : ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos hp').mp (hK'.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hball.trans hU, ?_, ?_, (measure_mono hball).trans hmass⟩
  · -- Since `ρ^{p−n} > 0`, `I(0, ρ) < ∞`, hence `I(z, r) < ∞`.
    exact hI.trans_lt (ENNReal.lt_top_of_mul_ne_top_right hfin.ne
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _)).ne')
  · -- `r^{p−n} ≤ ρ^{p−n}` and `I(z, r) ≤ I(0, ρ)` give `K(z, r) ≤ K(0, ρ) ≤ δ`.
    refine le_trans ?_ hK'
    exact ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hr.le hrρ hpn.le)) hI) hp'.le
/-- **Simon Ch. 4, 3.14 and 4.1** (radial first variation, keeping the conical term).  Let `V` have
generalized mean curvature `H` in `U`, let `B_R(y) ⊆ U`, and let `μ_V`-a.e. `x ∈ B̆_R(y)` have
`p_{T_x M} = p_P` for an `n`-dimensional subspace `P`.  If `φ ∈ C¹(ℝ)`, `φ = 1` on `(-∞, 1]`,
`φ = 0` on `[T, ∞)`, `ρ > 0` and `Tρ < R`, then with `r = |x − y|` (and `0/0 = 0` at `x = y`)
`∫ (n φ(r/ρ) + (r/ρ) φ'(r/ρ) (1 − |(x − y) − p_{T_x M}(x − y)|²/r²)) dμ_V
   = −∫ φ(r/ρ) (x − y) · H(x) dμ_V`.
Proof: test 3.14 with `X(x) = φ(r/ρ)(x − y)`, a `C¹` field supported in `B_{Tρ}(y) ⊆ U`.  For
`x ≠ y`, `DX(x) = φ(r/ρ) I + (φ'(r/ρ)/(ρr)) (x − y) ⊗ (x − y)`, and `DX = I` near `y`; tracing
against `p_P` gives the left integrand on `B̆_R(y)` off a `μ_V`-null set, while off `B̆_R(y)` both
vanish.  Integrals of `μ_V`-a.e. equal functions agree, so no integrability is needed. -/
theorem allard52_am_radial_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R : ℝ), closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH y R hR hP φ T ρ hφ hφ1 hφT hρ hTR
  -- Step 1: `φ' = 0` on `(T, ∞)`, where `φ` is constant.
  have hφ'T : ∀ u, T < u → deriv φ u = 0 := by
    intro u hu
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      exact hφT t (le_of_lt ht)
    rw [h.deriv_eq]
    simp
  have hU : closedBall y (T * ρ) ⊆ U := (closedBall_subset_closedBall hTR.le).trans hR
  -- Step 2: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, X = fun x => φ (‖x - y‖ / ρ) • (x - y) := ⟨_, rfl⟩
  have hXball : ∀ x ∈ ball y ρ, X =ᶠ[𝓝 x] fun z => z - y := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    have : ‖z - y‖ / ρ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      rw [div_le_one hρ]; exact hz.le
    simp [hX, hφ1 _ this]
  have hXcd : ContDiff ℝ 1 X := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxy : x = y
    · exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq
        (hXball x (by rw [hxy]; exact mem_ball_self hρ))
    · rw [hX]
      have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hxy)
      have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
        hφ.contDiffAt.comp x (h1.div_const ρ)
      exact h2.smul (contDiffAt_id.sub contDiffAt_const)
  -- `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
  have hXzero : ∀ z, T * ρ < ‖z - y‖ → X z = 0 := by
    intro z hz
    have hT : T ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; exact hz.le
    rw [hX]; simp [hφT _ hT]
  have hsupp : tsupport X ⊆ closedBall y (T * ρ) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    exact hz (hXzero z h)
  have hXcs : HasCompactSupport X :=
    (isCompact_closedBall y (T * ρ)).of_isClosed_subset (isClosed_tsupport X) hsupp
  -- Step 3: first variation.
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  have hRHS : (fun x => inner ℝ (X x) (H x)) =
      fun x => φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) := by
    funext x; rw [hX]; exact real_inner_smul_left _ _ _
  rw [hRHS] at key
  -- Step 4: for `x ≠ y`, `DX(x) = φ(r/ρ) id + ρ⁻¹ r⁻¹ φ'(r/ρ) ((x - y) · ⬝) (x - y)`.
  have hXderiv : ∀ x, x ≠ y → HasFDerivAt X
      (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (deriv φ (‖x - y‖ / ρ) / (ρ * ‖x - y‖)) • (innerSL ℝ (x - y)).smulRight (x - y)) x := by
    intro x hxy
    have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hnorm : HasFDerivAt (fun z : Amb n ℓ => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
      have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt x
        (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y).norm_sq
      convert h using 1
      · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
      · ext v; simp [Real.sqrt_sq hr.le]; field_simp
    have hcomp : HasDerivAt (fun t => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) / ρ) ‖x - y‖ :=
      (((hφ.differentiable one_ne_zero) (‖x - y‖ / ρ)).hasDerivAt.comp ‖x - y‖
        ((hasDerivAt_id' ‖x - y‖).div_const ρ)).congr_deriv (mul_one_div _ _)
    have hc := (hcomp.comp_hasFDerivAt x hnorm).smul (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    have hfun : X = ((fun t => φ (t / ρ)) ∘ fun z : Amb n ℓ => ‖z - y‖) • fun z => z - y := by
      rw [hX]; rfl
    rw [hfun]
    refine hc.congr_fderiv ?_
    ext v
    simp
    ring
  -- Step 5: trace facts.
  have htrP : ∀ P : Submodule ℝ (Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    intro P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.trace_id]
  have htr : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (u : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) ((a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        a * Module.finrank ℝ P + c * inner ℝ u (P.starProjection u) := by
    intro P a c u
    have hcomp : (a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap =
        a • P.starProjection.toLinearMap +
          c • ((innerSL ℝ u).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight u := by
      ext w; simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrP]
    simp
  -- Step 6: `div_M X = G` off a `μ_V`-null set.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    by_cases hxB : x ∈ ball y R
    · obtain ⟨P, hPn, hPx⟩ := hx hxB
      rw [RectifiableVarifold.divM, hPx]
      by_cases hxy : x = y
      · have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
          rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
          exact (hasFDerivAt_sub_const y).fderiv
        rw [hfd]
        simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
        subst hxy
        simp [hφ1 0 zero_le_one]
      · rw [(hXderiv x hxy).fderiv, htr, hPn]
        have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
        have h0 : inner ℝ ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y)) = 0 :=
          Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
        have h1 : inner ℝ (x - y) (P.starProjection (x - y)) = ‖P.starProjection (x - y)‖ ^ 2 := by
          calc inner ℝ (x - y) (P.starProjection (x - y))
              = inner ℝ (((x - y) - P.starProjection (x - y)) + P.starProjection (x - y))
                  (P.starProjection (x - y)) := by rw [sub_add_cancel]
            _ = ‖P.starProjection (x - y)‖ ^ 2 := by
              rw [inner_add_left, h0, zero_add, real_inner_self_eq_norm_sq]
        have h2 : ‖x - y‖ ^ 2 =
            ‖(x - y) - P.starProjection (x - y)‖ ^ 2 + ‖P.starProjection (x - y)‖ ^ 2 := by
          have := norm_add_sq_real ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y))
          rw [sub_add_cancel, h0] at this
          linarith
        rw [h1]
        field_simp
        linear_combination (deriv φ (‖x - y‖ / ρ)) * h2
    · -- Outside `B̆_R(y)`: `X = 0` near `x`, and `φ = φ' = 0` at `r/ρ > T`.
      have hr : T * ρ < ‖x - y‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hxB; linarith
      have hfd : fderiv ℝ X x = 0 := by
        have h : X =ᶠ[𝓝 x] fun _ => (0 : Amb n ℓ) := by
          filter_upwards [(isOpen_lt continuous_const
            ((continuous_id.sub continuous_const).norm)).mem_nhds hr] with z hz
          exact hXzero z hz
        rw [h.fderiv_eq]
        simp
      have hu : T < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; exact hr
      rw [RectifiableVarifold.divM, hfd]
      simp [hφT _ hu.le, hφ'T _ hu]
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
/-- **Simon Ch. 4, §3 (p. 90) and 4.7 (p. 94)**: the radial cutoffs of the monotonicity argument,
with `ε ↓ 0`.  There are `C¹` nonincreasing `φ k : ℝ → [0, 1]` with `φ k = 1` on `(-∞, 1]` and
`φ k = 0` on `[1 + ε k, ∞)`, where `0 < ε k ≤ 1` and `ε k → 0`.
With `S = Real.smoothTransition` (`C^∞`, monotone, `[0, 1]`-valued, `0` on `(-∞, 0]` and `1` on
`[1, ∞)`) take `ε k = 1 / (k + 2)` and `φ k u = 1 - S ((u - 1) (k + 2))`: the argument
`(u - 1) (k + 2)` is `≤ 0` for `u ≤ 1` and `≥ 1` for `u ≥ 1 + ε k`. -/
theorem allard52_amcl_cutoff_sequence : ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) ∧ (∀ k u, u ≤ 1 → φ k u = 1) ∧ (∀ k u, 1 + ε k ≤ u → φ k u = 0) := by
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  refine ⟨fun k u => 1 - Real.smoothTransition ((u - 1) * ((k : ℝ) + 2)),
    fun k => 1 / ((k : ℝ) + 2), fun k => ⟨by positivity, ?_⟩, ?_, fun k => ?_, fun k u v huv => ?_,
    fun k u => ⟨?_, ?_⟩, fun k u hu => ?_, fun k u hu => ?_⟩
  -- (a) `ε k ≤ 1 / 2 ≤ 1`
  · rw [div_le_one (hk k)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- (b) `ε k → 0` since `k + 2 → ∞`
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- (c) a constant minus `S` composed with an affine map
  · exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).mul contDiff_const))
  -- (d) `u ≤ v` gives `(u - 1) (k + 2) ≤ (v - 1) (k + 2)`, and `S` is monotone
  · exact sub_le_sub_left (Real.smoothTransition.monotone
      (mul_le_mul_of_nonneg_right (sub_le_sub_right huv 1) (hk k).le)) 1
  -- (e) `0 ≤ S ≤ 1`
  · exact sub_nonneg.2 (Real.smoothTransition.le_one _)
  · exact sub_le_self _ (Real.smoothTransition.nonneg _)
  -- (f) `u ≤ 1` makes the argument `≤ 0`, where `S = 0`
  · dsimp only
    rw [Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) (hk k).le), sub_zero]
  -- (g) `u ≥ 1 + ε k` makes the argument `≥ 1`, where `S = 1`
  · dsimp only at hu ⊢
    have h1 : 1 / ((k : ℝ) + 2) ≤ u - 1 := by linarith
    rw [div_le_iff₀ (hk k)] at h1
    rw [Real.smoothTransition.one_of_one_le h1, sub_self]
/-- **Simon Ch. 4, 4.7–4.8 (p. 94)**: the `ε ↓ 0` limit of the cutoff integrals over `(0, t]`.
With `β = n / p ∈ [0, 1)` and `κ = (p - n) / (4p)`, the majorant `2κΛR⁻¹ (τ / R)^{-β}` equals
`C τ^{-β}` with `C = 2κΛR⁻¹ R^β`; it is integrable on `[0, t]` with integral
`C t^{1-β} / (1 - β) = (Λ / 2) (t / R)^{1-β}`, since `2κ / (1 - β) = 1 / 2`.  Dominated convergence
gives the limit, and the eventual bound `|∫₀ᵗ a k| ≤ ∫₀ᵗ C τ^{-β}` passes to it. -/
theorem allard52_amcl_interval_limit : ∀ (n : ℕ) (p R Λ t : ℝ) (a : ℕ → ℝ → ℝ) (g : ℝ → ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < t → (∀ᶠ k in atTop, ∀ τ : ℝ, 0 < τ → τ ≤ t → ContinuousAt (a k) τ ∧ |a k τ| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-((n : ℝ) / p))) → (∀ τ : ℝ, 0 < τ → τ ≤ t → Tendsto (fun k => a k τ) atTop (𝓝 (g τ))) → Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (∫ τ in (0)..t, g τ)) ∧ |∫ τ in (0)..t, g τ| ≤ Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p) := by
  intro n p R Λ t a g hnp hR _hΛ ht hev hlim
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  set β : ℝ := (n : ℝ) / p with hβ
  have hβ1 : β < 1 := (div_lt_one hp).2 hnp
  set C : ℝ := 2 * ((p - n) / (4 * p)) * Λ / R * R ^ β with hC
  -- (1) the majorant is `C τ^{-β}` for `τ ≥ 0`
  have hb_eq : ∀ τ : ℝ, 0 ≤ τ →
      2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-β) = C * τ ^ (-β) := by
    intro τ hτ
    rw [Real.div_rpow hτ hR.le, Real.rpow_neg hR.le, div_inv_eq_mul, hC]
    ring
  have hI : uIoc (0 : ℝ) t = Ioc 0 t := uIoc_of_le ht.le
  -- (2) `C τ^{-β}` is integrable on `[0, t]` since `-β > -1`
  have hb_int : IntervalIntegrable (fun τ => C * τ ^ (-β)) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  -- (3) its integral is `C t^{1-β} / (1 - β) = (Λ / 2) (t / R)^{1-β}`, as `0^{1-β} = 0`
  have hb_val : ∫ τ in (0 : ℝ)..t, C * τ ^ (-β) = Λ / 2 * (t / R) ^ (1 - β) := by
    have h1β : 1 - β ≠ 0 := by linarith
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), neg_add_eq_sub,
      Real.zero_rpow h1β, sub_zero, Real.div_rpow ht.le hR.le, Real.rpow_sub hR, Real.rpow_one, hC]
    have hpn : p - n ≠ 0 := by linarith
    have h1β' : 1 - β = (p - n) / p := by rw [hβ]; field_simp
    rw [h1β']
    have hRβ : R ^ β ≠ 0 := (Real.rpow_pos_of_pos hR β).ne'
    generalize t ^ ((p - n) / p) = T
    field_simp
    ring
  -- (4) dominated convergence on `Ι 0 t = (0, t]`: eventually `a k` is continuous there, hence
  -- measurable, and dominated by `C τ^{-β}`
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (a k) (volume.restrict (uIoc 0 t)) := by
    filter_upwards [hev] with k hk
    rw [hI]
    exact ContinuousOn.aestronglyMeasurable
      (fun τ hτ => (hk τ hτ.1 hτ.2).1.continuousWithinAt) measurableSet_Ioc
  have hbound : ∀ᶠ k in atTop, ∀ᵐ τ ∂volume, τ ∈ uIoc 0 t → ‖a k τ‖ ≤ C * τ ^ (-β) := by
    filter_upwards [hev] with k hk
    refine Eventually.of_forall (fun τ hτ => ?_)
    rw [hI] at hτ
    rw [Real.norm_eq_abs, ← hb_eq τ hτ.1.le]
    exact (hk τ hτ.1 hτ.2).2
  have hlim' : ∀ᵐ τ ∂volume, τ ∈ uIoc 0 t → Tendsto (fun k => a k τ) atTop (𝓝 (g τ)) := by
    refine Eventually.of_forall (fun τ hτ => ?_)
    rw [hI] at hτ
    exact hlim τ hτ.1 hτ.2
  have hT : Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (∫ τ in (0)..t, g τ)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hb_int hlim'
  refine ⟨hT, ?_⟩
  -- (5) eventually `|∫₀ᵗ a k| ≤ ∫₀ᵗ C τ^{-β}`, and this passes to the limit
  have hk_le : ∀ᶠ k in atTop, |∫ τ in (0)..t, a k τ| ≤ ∫ τ in (0 : ℝ)..t, C * τ ^ (-β) := by
    filter_upwards [hbound] with k hk
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht.le ?_ hb_int
    filter_upwards [hk] with τ hτ h
    exact hτ (hI ▸ h)
  rw [← hb_val]
  exact le_of_tendsto hT.abs hk_le
/-- **Simon Ch. 4, 4.7 (p. 94)**: the limit `ε ↓ 0` of "integrating from `σ` to `ρ` and letting
`ε ↓ 0`", for any `g : ℝ^{n+ℓ} → [0, ∞]` (no measurability is needed).  If `s > 0`, `ε k → 0`,
`c k → L` and eventually `∫_{B_r(y) \ B̆_{(1 + ε k) s}(y)} g dμ ≤ c k`, then
`∫_{B_r(y) \ B_s(y)} g dμ ≤ L`.
The sets `D j = B_r(y) \ B̆_{(1 + 1 / (j + 1)) s}(y)` increase to `B_r(y) \ B_s(y)` (Archimedean
property), and each `D j` eventually lies in `B_r(y) \ B̆_{(1 + ε k) s}(y)`, so `∫_{D j} g ≤ L`;
the lower integral is continuous along directed countable unions
(`setLIntegral_iUnion_of_directed`). -/
theorem allard52_amcl_annular_lintegral_le : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ≥0∞) (y : Amb n ℓ) (ε c : ℕ → ℝ) (s r L : ℝ), 0 < s → Tendsto ε atTop (𝓝 0) → Tendsto c atTop (𝓝 L) → (∀ᶠ k in atTop, ∫⁻ x in closedBall y r \ ball y ((1 + ε k) * s), g x ∂μ ≤ ENNReal.ofReal (c k)) → ∫⁻ x in closedBall y r \ closedBall y s, g x ∂μ ≤ ENNReal.ofReal L := by
  intro n ℓ μ g y ε c s r L hs hε hc hbound
  set D : ℕ → Set (Amb n ℓ) := fun j => closedBall y r \ ball y ((1 + 1 / ((j : ℝ) + 1)) * s)
  -- the `D j` increase, since `1 / (j + 1)` decreases
  have hmono : Monotone D := by
    intro i j hij x hx
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_lt] at hx ⊢
    refine ⟨hx.1, le_trans ?_ hx.2⟩
    gcongr
  -- `⋃ j, D j = B_r(y) \ B_s(y)`: if `s < |x - y|`, pick `1 / (j + 1) < (|x - y| - s) / s`
  have hU : closedBall y r \ closedBall y s = ⋃ j, D j := by
    ext x
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_le, not_lt, mem_iUnion]
    constructor
    · rintro ⟨hxr, hxs⟩
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 hxs) hs)
      refine ⟨j, hxr, ?_⟩
      rw [lt_div_iff₀ hs] at hj
      linarith
    · rintro ⟨j, hxr, hxj⟩
      refine ⟨hxr, lt_of_lt_of_le ?_ hxj⟩
      have : 0 < 1 / ((j : ℝ) + 1) := by positivity
      nlinarith
  rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun j => ?_
  have hδ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  -- eventually `ε k < 1 / (j + 1)`, so `D j ⊆ B_r(y) \ B̆_{(1 + ε k) s}(y)`
  have hev : ∀ᶠ k in atTop, ∫⁻ x in D j, g x ∂μ ≤ ENNReal.ofReal (c k) := by
    filter_upwards [hbound, hε.eventually (eventually_lt_nhds hδ)] with k hk hεk
    refine le_trans (lintegral_mono_set ?_) hk
    intro x hx
    simp only [D, Set.mem_sdiff, mem_closedBall, mem_ball, not_lt] at hx ⊢
    refine ⟨hx.1, le_trans ?_ hx.2⟩
    gcongr
  -- `ofReal (c k) → ofReal L`
  exact ge_of_tendsto (ENNReal.tendsto_ofReal hc) hev
/-- **Simon Ch. 4, 4.2** (the scaled `Lᵖ` condition on the mean curvature).  Let `p > n`,
`R, Λ > 0`, `t ≤ R`, `κ = (p − n)/(4p)` and `Q_s = ∫_{B_s(y)} |H|ᵖ dμ ∈ [0, ∞]`.  If
`(R^{p−n} Q_R)^{1/p} ≤ κ Λ` in `[0, ∞]`, then `Q_t < ∞` and `Q_t^{1/p} ≤ κ Λ R^{n/p − 1}`.
Proof: `Q_R < ∞`, since otherwise the left side is `∞^{1/p} = ∞`; in real numbers the hypothesis
reads `R^{1 − n/p} Q_R^{1/p} ≤ κ Λ`; and `Q_t ≤ Q_R` by monotonicity in the domain. -/
theorem allard52_am_fc_lp_scale : ∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ t : ℝ), 0 < R → 0 < Λ → t ≤ R → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ ∧ (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1) := by
  intro n ℓ p hnp μ H y R Λ t hR hΛ htR hLp
  -- Notation: `Q_s = ∫_{B_s(y)} |H|ᵖ dμ`, `c = R^{p−n}` and `κ = (p − n)/(4p)`.
  set QR : ℝ≥0∞ := ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ
  set Qt : ℝ≥0∞ := ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ
  set c : ℝ := R ^ (p - n) with hc
  set κ : ℝ := (p - n) / (4 * p)
  -- Step 0: constants.
  have hp : 0 < p := (Nat.cast_nonneg n).trans_lt hnp
  have hp1 : 0 < 1 / p := one_div_pos.2 hp
  have hc0 : 0 < c := Real.rpow_pos_of_pos hR _
  have hκΛ : 0 ≤ κ * Λ := mul_nonneg (div_nonneg (sub_pos.2 hnp).le (by positivity)) hΛ.le
  -- Step 1: `Q_R < ∞`; otherwise `(c Q_R)^{1/p} = ∞^{1/p} = ∞`, as `c > 0`.
  have hcQ : ENNReal.ofReal c * QR ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos hp1] at hLp
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hLp)
  have hQRfin : QR ≠ ⊤ := by
    intro h
    apply hcQ
    rw [h]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne'
  -- Step 2: the hypothesis in real numbers.
  have hreal : (c * QR.toReal) ^ (1 / p) ≤ κ * Λ := by
    rwa [← ENNReal.ofReal_toReal hQRfin, ← ENNReal.ofReal_mul hc0.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc0.le ENNReal.toReal_nonneg) hp1.le,
      ENNReal.ofReal_le_ofReal_iff hκΛ] at hLp
  -- Step 3: factoring, `(R^{p−n})^{1/p} = R^{1 − n/p}`.
  have hfac : (c * QR.toReal) ^ (1 / p) = R ^ (1 - n / p) * QR.toReal ^ (1 / p) := by
    rw [Real.mul_rpow hc0.le ENNReal.toReal_nonneg, hc, ← Real.rpow_mul hR.le]
    congr 2
    field_simp
  -- Step 4: dividing by `R^{1 − n/p} > 0`.
  have hRpos : 0 < R ^ (1 - n / p) := Real.rpow_pos_of_pos hR _
  have hN : QR.toReal ^ (1 / p) ≤ κ * Λ * R ^ ((n : ℝ) / p - 1) := by
    have hinv : R ^ ((n : ℝ) / p - 1) = (R ^ (1 - n / p))⁻¹ := by
      rw [← Real.rpow_neg hR.le, neg_sub]
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hRpos, mul_comm, ← hfac]
    exact hreal
  -- Step 5: the sub-ball, `Q_t ≤ Q_R`.
  have hQle : Qt ≤ QR := lintegral_mono_set (closedBall_subset_closedBall htR)
  refine ⟨hQle.trans_lt (lt_top_iff_ne_top.2 hQRfin), ?_⟩
  calc Qt.toReal ^ (1 / p) ≤ QR.toReal ^ (1 / p) :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_mono hQRfin hQle) hp1.le
    _ ≤ κ * Λ * R ^ ((n : ℝ) / p - 1) := hN
/-- **Simon Ch. 4, between 4.2 and 4.3** (the Hölder absorption in the monotonicity estimate).  Let
`1 ≤ n < p`, `R > 0`, `t > 0`, `I ≥ 0`, `N ≥ 0` and `0 < ε ≤ 1`, and write `κ = (p − n)/(4p)`.  If
`N ≤ κ Λ R^{n/p − 1}` and `|E| ≤ (1 + ε) t N I^{1 − 1/p}`, then
`|E / tⁿ⁺¹ / (1 + I/tⁿ)| ≤ 2 κ Λ R⁻¹ (t/R)^{−n/p}`.
Proof: with `A = I/tⁿ`, `I^{1 − 1/p} = A^{1 − 1/p} t^{n − n/p}` and `A^{1 − 1/p} ≤ 1 + A` (split at
`A = 1`, using `0 ≤ 1 − 1/p ≤ 1`).  With `1 + ε ≤ 2` this gives `|E| ≤ 2 N t^{−n/p} tⁿ⁺¹ (1 + A)`;
then insert the bound on `N` and use `R^{n/p − 1} t^{−n/p} = R⁻¹ (t/R)^{−n/p}`. -/
theorem allard52_am_fc_a_bound : ∀ (n : ℕ), 1 ≤ n → ∀ (p R Λ ε t I E N : ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → 0 < t → 0 ≤ I → 0 ≤ N → N ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1) → |E| ≤ (1 + ε) * t * N * I ^ (1 - 1 / p) → |E / t ^ (n + 1) / (1 + I / t ^ n)| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
  intro n hn p R Λ ε t I E N hnp hR hΛ hε hε1 ht hI hN hNb hE
  -- Step 0: `p > 1`, so `γ = 1 - 1/p` satisfies `0 ≤ γ ≤ 1`; and `tⁿ > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    linarith
  have hγ1 : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := by positivity
    linarith
  have htn : 0 < t ^ n := pow_pos ht n
  -- Step 1: with `A = I/tⁿ ≥ 0`, `I^γ = A^γ (tⁿ)^γ = A^γ t^(n - n/p)`.
  set A := I / t ^ n with hA
  have hA0 : 0 ≤ A := div_nonneg hI htn.le
  have hIγ : I ^ (1 - 1 / p) = A ^ (1 - 1 / p) * t ^ ((n : ℝ) - n / p) := by
    have hIA : I = A * t ^ n := by rw [hA, div_mul_cancel₀ _ htn.ne']
    rw [hIA, Real.mul_rpow hA0 htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  -- Step 2: absorption `A^γ ≤ 1 + A`, splitting into `A ≤ 1` and `A ≥ 1`.
  have habs : A ^ (1 - 1 / p) ≤ 1 + A := by
    rcases le_total A 1 with h | h
    · calc A ^ (1 - 1 / p) ≤ 1 := Real.rpow_le_one hA0 h hγ0
        _ ≤ 1 + A := by linarith
    · calc A ^ (1 - 1 / p) ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hγ1
        _ = A := Real.rpow_one A
        _ ≤ 1 + A := by linarith
  -- Step 3: `t t^(n - n/p) = t^(-n/p) tⁿ⁺¹`; with `1 + ε ≤ 2`,
  -- `|E| ≤ 2 N t^(-n/p) (tⁿ⁺¹ (1 + A))`, so `|E/tⁿ⁺¹/(1 + A)| ≤ 2 N t^(-n/p)`.
  have hpow : t * t ^ ((n : ℝ) - n / p) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
    rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht, mul_comm t,
      ← Real.rpow_add_one ht.ne']
    congr 1
    push_cast
    ring
  have hE2 : |E| ≤ 2 * N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + A)) :=
    calc |E| ≤ (1 + ε) * t * N * I ^ (1 - 1 / p) := hE
      _ = (1 + ε) * (N * (t * t ^ ((n : ℝ) - n / p))) * A ^ (1 - 1 / p) := by
          rw [hIγ]
          ring
      _ ≤ 2 * (N * (t * t ^ ((n : ℝ) - n / p))) * (1 + A) := by
          gcongr
          linarith
      _ = 2 * N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + A)) := by
          rw [hpow]
          ring
  have hden : 0 < t ^ (n + 1) * (1 + A) := by positivity
  -- Steps 4–5: insert `N ≤ κ Λ R^(n/p - 1)` and rewrite
  -- `R^(n/p - 1) t^(-n/p) = R^(n/p) t^(-n/p) / R = R⁻¹ (t/R)^(-n/p)`.
  calc |E / t ^ (n + 1) / (1 + A)| = |E| / (t ^ (n + 1) * (1 + A)) := by
        rw [div_div, abs_div, abs_of_pos hden]
    _ ≤ 2 * N * t ^ (-((n : ℝ) / p)) := by
        rw [div_le_iff₀ hden]
        exact hE2
    _ ≤ 2 * ((p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1)) * t ^ (-((n : ℝ) / p)) := by
        gcongr
    _ = 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
        rw [Real.div_rpow ht.le hR.le, Real.rpow_sub_one hR.ne', Real.rpow_neg hR.le,
          div_inv_eq_mul]
        ring
/-- **Simon Ch. 4, after 4.4** (the primitive of the mean-curvature coefficient).  Let `p > n`,
`R, Λ, ε > 0`, `κ = (p − n)/(4p)`, and let `a` be continuous with
`|a(τ)| ≤ 2κΛR⁻¹ (τ/R)^{−n/p}` at every `τ > 0` with `(1 + ε)τ < R`.  Then for each such `t` the
primitive `G(u) = ∫₀ᵘ a` is continuous at `t` and `|G(t)| ≤ Λ/2`.
Proof: as `−n/p > −1`, the bound is integrable near `0`, so `a` is interval integrable on `[0, t]`
and the fundamental theorem of calculus applies at `t`; and
`|G(t)| ≤ ∫₀ᵗ 2κΛR⁻¹ (τ/R)^{−n/p} dτ = (2κ/(1 − n/p)) Λ (t/R)^{1−n/p} = (Λ/2) (t/R)^{1−n/p} ≤ Λ/2`,
since `t ≤ R`. -/
theorem allard52_am_fc_primitive : ∀ (n : ℕ) (p R Λ ε : ℝ) (a : ℝ → ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < ε → (∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧ |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))) → ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt (fun u => ∫ τ in (0)..u, a τ) t ∧ |∫ τ in (0)..t, a τ| ≤ Λ / 2 := by
  intro n p R Λ ε a hnp hR hΛ hε ha t ht htR
  -- Notation: `β = n/p ∈ [0, 1)`, `c = 2κΛ/R`, and the bound `g(τ) = c (τ/R)^{−β}`.
  set β : ℝ := (n : ℝ) / p with hβ
  set c : ℝ := 2 * ((p - n) / (4 * p)) * Λ / R with hc
  have hp : 0 < p := (Nat.cast_nonneg n).trans_lt hnp
  have hβ1 : β < 1 := (div_lt_one hp).2 hnp
  -- Step 0: `t ≤ R`, and `a` is continuous on the open set `U = {τ | 0 < τ ∧ (1 + ε)τ < R}`,
  -- which contains `(0, t]`.
  have htR' : t ≤ R := by nlinarith
  set U : Set ℝ := {τ | 0 < τ ∧ (1 + ε) * τ < R}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const)
  have haU : ContinuousOn a U := fun τ hτ => (ha τ hτ.1 hτ.2).1.continuousWithinAt
  have hIoc : Ioc 0 t ⊆ U := fun τ hτ =>
    ⟨hτ.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hτ.2 (by linarith)) htR⟩
  -- Step 1: `g` is interval integrable on `[0, t]`, since `−β > −1` (rescale `τ ↦ τ/R`).
  have hg0 : IntervalIntegrable (fun τ => (τ / R) ^ (-β)) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t / R)
      (r := -β) (by linarith)).comp_mul_right (c := R⁻¹)
    simpa [div_eq_mul_inv, hR.ne'] using h
  have hg : IntervalIntegrable (fun τ => c * (τ / R) ^ (-β)) volume 0 t := hg0.const_mul c
  -- Step 2: `|a| ≤ g` on `(0, t]`.
  have hle : ∀ τ ∈ Ioc 0 t, ‖a τ‖ ≤ c * (τ / R) ^ (-β) := fun τ hτ => by
    rw [Real.norm_eq_abs]
    exact (ha τ (hIoc hτ).1 (hIoc hτ).2).2
  -- Step 3: by domination, `a` is interval integrable on `[0, t]`.
  have haI : IntervalIntegrable a volume 0 t := by
    refine hg.mono_fun' ?_ ?_
    · rw [uIoc_of_le ht.le]
      exact (haU.mono hIoc).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.le]
      exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hle)
  refine ⟨?_, ?_⟩
  -- Step 4: FTC at `t`, where `a` is continuous and strongly measurable near `t`.
  · exact (intervalIntegral.integral_hasDerivAt_right haI
      (haU.stronglyMeasurableAtFilter hUo t ⟨ht, htR⟩) (ha t ht htR).1).continuousAt
  -- Step 5: `|G(t)| ≤ ∫₀ᵗ g = c R (t/R)^{1−β}/(1 − β) = (Λ/2)(t/R)^{1−β} ≤ Λ/2`.
  · have h1 : |∫ τ in (0)..t, a τ| ≤ ∫ τ in (0)..t, c * (τ / R) ^ (-β) := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_of_norm_le ht.le (Eventually.of_forall hle) hg
    have h2 : ∫ τ in (0)..t, c * (τ / R) ^ (-β) =
        c * (R * ((t / R) ^ (-β + 1) / (-β + 1))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_div (fun x => x ^ (-β)) hR.ne',
        integral_rpow (Or.inl (by linarith)), zero_div, Real.zero_rpow (by linarith), sub_zero,
        smul_eq_mul]
    -- `2κ/(1 − β) = 1/2`.
    have h3 : c * (R * ((t / R) ^ (-β + 1) / (-β + 1))) = Λ / 2 * (t / R) ^ (-β + 1) := by
      have hβ' : -β + 1 = (p - n) / p := by rw [hβ]; field_simp; ring
      have hpn : p - n ≠ 0 := (sub_pos.2 hnp).ne'
      generalize (t / R) ^ (-β + 1) = X
      rw [hβ', hc]
      field_simp
      ring
    have hX : (t / R) ^ (-β + 1) ≤ 1 :=
      Real.rpow_le_one (div_nonneg ht.le hR.le) ((div_le_one hR).2 htR') (by linarith)
    calc |∫ τ in (0)..t, a τ| ≤ ∫ τ in (0)..t, c * (τ / R) ^ (-β) := h1
      _ = Λ / 2 * (t / R) ^ (-β + 1) := by rw [h2, h3]
      _ ≤ Λ / 2 * 1 := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = Λ / 2 := mul_one _
/-- **Simon Ch. 4, 4.1** (cf. 3.14–3.16; the radial split of the first-variation integrand for one
cutoff, as used in 4.1–4.5).
Let `μ(B_R(y)) < ∞`, let `w` be a.e. strongly measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e.
there, and let `φ` be a nonincreasing `C¹` function with `φ = 1` on `(-∞, 1]` and `φ = 0` on
`[1 + ε, ∞)`.  For `t > 0` with `(1 + ε) t < R`, writing `r = |x − y|`:
`∫ (n φ(r/t) + (r/t) φ'(r/t) (1 − w)) dμ`
`= n ∫ φ(r/t) dμ + ∫ (r/t) φ'(r/t) dμ − ∫ (r/t) φ'(r/t) w dμ`,
`∫ φ(r/t) dμ ≥ 0` and `∫ (r/t) φ'(r/t) w dμ ≤ 0`.
Proof: as in `allard52_am_fc_cutoff_facts` (derived directly here), `0 ≤ φ ≤ 1`, `φ' ≤ 0`,
`φ' = 0` on `(1 + ε, ∞)`, and `φ'` is continuous and bounded.  The three integrands vanish off
`B = B_{(1+ε)t}(y) ⊆ B̆_R(y)`, which has finite measure, and are bounded and a.e. strongly
measurable on `B`, hence integrable; linearity gives the split, `φ ≥ 0` the second claim, and
`(r/t) φ'(r/t) w ≤ 0` `μ`-a.e. the third. -/
theorem allard52_am_fc_radial_split : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R ε : ℝ) (φ : ℝ → ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ = (n : ℝ) * ∫ x, φ (‖x - y‖ / t) ∂μ + ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ - ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ∧ 0 ≤ ∫ x, φ (‖x - y‖ / t) ∂μ ∧ ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ ≤ 0 := by
  intro n ℓ μ w y R ε φ hε hμR hw hw01 hφC hφA hφ1 hφ0 t ht htR
  -- Step 1: `0 ≤ φ ≤ 1`, `φ' ≤ 0`, `φ' = 0` on `(1 + ε, ∞)`, `φ'` continuous and `|φ'| ≤ C`
  -- (the facts of `allard52_am_fc_cutoff_facts`, derived directly).
  -- `0 ≤ φ ≤ 1` by monotonicity and the boundary values `φ (1 + ε) = 0`, `φ 1 = 1`.
  have hφ01 : ∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1 := by
    intro u
    constructor
    · rcases le_total (1 + ε) u with hu | hu
      · rw [hφ0 u hu]
      · rw [← hφ0 (1 + ε) le_rfl]
        exact hφA hu
    · rcases le_total u 1 with hu | hu
      · rw [hφ1 u hu]
      · rw [← hφ1 1 le_rfl]
        exact hφA hu
  -- `φ' ≤ 0` because `φ` is nonincreasing.
  have hdφ : ∀ u : ℝ, deriv φ u ≤ 0 := fun u => hφA.deriv_nonpos
  -- `φ' = 0` on `(1 + ε, ∞)` and on `(-∞, 1)`, where `φ` is locally constant.
  have hdφ0 : ∀ u : ℝ, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) (fun v hv => hφ0 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  have hdφ1 : ∀ u : ℝ, u < 1 → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu) (fun v hv => hφ1 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  -- `φ'` is continuous because `φ` is `C¹`; its support lies in `[1, 1 + ε]`, so it is bounded.
  have hdφc : Continuous (deriv φ) := hφC.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, |deriv φ u| ≤ C := by
    have hsupp : HasCompactSupport (deriv φ) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a := 1) (b := 1 + ε)) ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact ⟨not_lt.mp fun h => hu (hdφ1 u h), not_lt.mp fun h => hu (hdφ0 u h)⟩
    obtain ⟨C, hC⟩ := hdφc.bounded_above_of_compact_support hsupp
    exact ⟨C, fun u => by rw [← Real.norm_eq_abs]; exact hC u⟩
  -- Step 2: `B = B_{(1+ε)t}(y)` lies in `B̆_R(y)`, so `μ(B) < ∞`; `r/t ≤ 1 + ε` on `B` and
  -- `r/t > 1 + ε` off `B`.
  have hBm : MeasurableSet (closedBall y ((1 + ε) * t)) := measurableSet_closedBall
  have hBR : closedBall y ((1 + ε) * t) ⊆ ball y R := closedBall_subset_ball htR
  have hμB : μ (closedBall y ((1 + ε) * t)) < ⊤ :=
    (measure_mono (hBR.trans ball_subset_closedBall)).trans_lt hμR
  have hr0 : ∀ x : Amb n ℓ, 0 ≤ ‖x - y‖ / t := fun x => div_nonneg (norm_nonneg _) ht.le
  have hin : ∀ x ∈ closedBall y ((1 + ε) * t), ‖x - y‖ / t ≤ 1 + ε := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact (div_le_iff₀ ht).2 hx
  have hout : ∀ x, x ∉ closedBall y ((1 + ε) * t) → 1 + ε < ‖x - y‖ / t := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact (lt_div_iff₀ ht).2 hx
  -- Step 3: `φ(r/t)` and `(r/t) φ'(r/t)` are continuous; all three integrands vanish off `B`.
  have hrc : Continuous fun x : Amb n ℓ => ‖x - y‖ / t :=
    (continuous_id.sub continuous_const).norm.div_const t
  have hf1c : Continuous fun x : Amb n ℓ => φ (‖x - y‖ / t) := hφC.continuous.comp hrc
  have hf2c : Continuous fun x : Amb n ℓ => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) :=
    hrc.mul (hdφc.comp hrc)
  have hf1B : ∀ x, x ∉ closedBall y ((1 + ε) * t) → φ (‖x - y‖ / t) = 0 :=
    fun x hx => hφ0 _ (hout x hx).le
  have hf2B : ∀ x, x ∉ closedBall y ((1 + ε) * t) →
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) = 0 :=
    fun x hx => by rw [hdφ0 _ (hout x hx), mul_zero]
  have hf3B : ∀ x, x ∉ closedBall y ((1 + ε) * t) →
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x = 0 :=
    fun x hx => by rw [hf2B x hx, zero_mul]
  -- Step 4 (i): `|φ(r/t)| ≤ 1`, so `φ(r/t)` is integrable on `B`, hence on the whole space.
  have hi1 : Integrable (fun x => φ (‖x - y‖ / t)) μ := by
    refine (Measure.integrableOn_of_bounded (M := 1) hμB.ne hf1c.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)).integrable_of_forall_notMem_eq_zero hf1B
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 _).1]
    exact (hφ01 _).2
  -- Step 4 (ii): `|(r/t) φ'(r/t)| ≤ (1 + ε) C` on `B`.
  have hi2 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ := by
    refine (Measure.integrableOn_of_bounded (M := (1 + ε) * C) hμB.ne
      hf2c.aestronglyMeasurable ?_).integrable_of_forall_notMem_eq_zero hf2B
    filter_upwards [ae_restrict_mem hBm] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 x)]
    exact mul_le_mul (hin x hx) (hC _) (abs_nonneg _) (by linarith)
  -- Step 4 (iii): `w` is a.e. strongly measurable on `B ⊆ B̆_R(y)`, and `0 ≤ w ≤ 1` `μ`-a.e. on `B`
  -- gives `|(r/t) φ'(r/t) w| ≤ |(r/t) φ'(r/t)|` there.
  have hi3 : Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) μ := by
    have hwB : AEStronglyMeasurable w (μ.restrict (closedBall y ((1 + ε) * t))) :=
      hw.mono_set hBR
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hf3B
    refine Integrable.mono' hi2.integrableOn.norm (hf2c.aestronglyMeasurable.fun_mul hwB) ?_
    filter_upwards [ae_restrict_mem hBm, ae_restrict_of_ae hw01] with x hxB hx
    obtain ⟨h0, h1⟩ := hx (hBR hxB)
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  -- Step 6 (`∫ φ(r/t) dμ ≥ 0` since `φ ≥ 0`) is the middle component.
  refine ⟨?_, integral_nonneg fun x => (hφ01 _).1, integral_nonpos_of_ae ?_⟩
  -- Step 5: the splitting identity, by linearity of the integral.
  · have hi12 : Integrable (fun x => (n : ℝ) * φ (‖x - y‖ / t) +
        ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ := (hi1.const_mul _).add hi2
    calc ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * (1 - w x)) ∂μ
        = ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t) -
            ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) ∂μ := by
          congr 1
          funext x
          ring
      _ = (n : ℝ) * ∫ x, φ (‖x - y‖ / t) ∂μ + ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ -
            ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ := by
          rw [integral_sub hi12 hi3, integral_add (hi1.const_mul _) hi2, integral_const_mul]
  -- Step 7: `(r/t) φ'(r/t) w ≤ 0` `μ`-a.e.: on `B̆_R(y)` since `r/t ≥ 0`, `φ' ≤ 0` and `w ≥ 0`;
  -- off `B̆_R(y)` the point is off `B`, where the integrand vanishes.
  · filter_upwards [hw01] with x hx
    by_cases hxR : x ∈ ball y R
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (hr0 x) (hdφ _)) (hx hxR).1
    · exact (hf3B x fun hxB => hxR (hBR hxB)).le
/-- **Simon Ch. 4, 4.2–4.3** (the Hölder step for the mean-curvature term).  Let `p > 1`, let `μ`
be a measure on `ℝ^{n+ℓ}` with `μ(B_t(y)) < ∞`, let `H` be `μ`-integrable on `B_t(y)` with
`∫_{B_t(y)} |H|ᵖ dμ < ∞`, and let `ψ` be a.e. strongly measurable with `0 ≤ ψ ≤ 1` and `ψ = 0` off
`B_t(y)`.  Then `|∫ ψ(x) (x − y) · H(x) dμ| ≤ t (∫_{B_t(y)} |H|ᵖ dμ)^{1/p} (∫ ψ dμ)^{1 − 1/p}`.
Proof: on `B_t(y)`, `|ψ(x) (x − y) · H(x)| ≤ t ψ(x) |H(x)|` by Cauchy–Schwarz, and the pairing
vanishes off `B_t(y)`; Hölder on `B_t(y)` with `q = p/(p − 1)` and `ψ^q ≤ ψ` bound
`∫_{B_t(y)} ψ |H| dμ`.  The estimate is carried out in `[0, ∞]`, where every factor on the right is
finite, and then converted to real numbers. -/
theorem aal_curvature_pairing_holder_bound : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  intro n ℓ p hp μ H ψ y t ht hμB hHint hHp hψm hψ01 hψt
  -- Notation: `B = B_t(y)` and the conjugate exponent `q = p/(p - 1)`, with `1/q = 1 - 1/p`.
  set B : Set (Amb n ℓ) := closedBall y t
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp⟩
  have hq1 : 1 - 1 / p = 1 / q := by rw [one_div, one_div, hpq.one_sub_inv]
  -- Step 1: `ψ` vanishes off `B`; it is integrable because `0 ≤ ψ ≤ 1_B` and `μ(B) < ∞`.
  have hψB : ∀ x, x ∉ B → ψ x = 0 := by
    intro x hx
    apply hψt x
    simpa [B, mem_closedBall, dist_eq_norm] using hx
  have hψe : ∀ x, ‖ψ x‖ₑ = ENNReal.ofReal (ψ x) := fun x => Real.enorm_of_nonneg (hψ01 x).1
  have hψle : ∀ x, ‖ψ x‖ₑ ≤ 1 := fun x => (hψe x).trans_le (ENNReal.ofReal_le_one.2 (hψ01 x).2)
  have hψind : ∀ x, ‖ψ x‖ₑ ≤ B.indicator 1 x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact hψle x
    · rw [hψB x hx, enorm_zero]
      exact zero_le
  have hψlin : ∫⁻ x, ‖ψ x‖ₑ ∂μ < ∞ :=
    calc ∫⁻ x, ‖ψ x‖ₑ ∂μ ≤ ∫⁻ x, B.indicator 1 x ∂μ := lintegral_mono hψind
      _ = μ B := lintegral_indicator_one hBm
      _ < ∞ := hμB
  have hψint : Integrable ψ μ := ⟨hψm, hψlin⟩
  have hψI : ∫⁻ x, ‖ψ x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all _ fun x => (hψ01 x).1)]
    exact lintegral_congr hψe
  have hψnn : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
  -- Step 2: on `B`, `|ψ(x)(x - y)·H(x)| ≤ t ψ(x)|H(x)|` (Cauchy–Schwarz and `|x - y| ≤ t`);
  -- off `B` the pairing vanishes.
  have hpt : ∀ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ≤
      B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      have hxy : ‖x - y‖ ≤ t := by simpa [B, mem_closedBall, dist_eq_norm] using hx
      have hreal : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
        rw [norm_mul, Real.norm_of_nonneg (hψ01 x).1]
        calc ψ x * ‖inner ℝ (x - y) (H x)‖ ≤ ψ x * (‖x - y‖ * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hψ01 x).1
          _ ≤ ψ x * (t * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
                (hψ01 x).1
          _ = t * (‖H x‖ * ψ x) := by ring
      calc ‖ψ x * inner ℝ (x - y) (H x)‖ₑ = ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ :=
            (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, hψe]
    · rw [indicator_of_notMem hx, hψB x hx, zero_mul, enorm_zero]
  -- Step 3: Hölder on `(B, μ⌞B)` with exponents `p` and `q`.
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq
    hHint.aestronglyMeasurable.enorm hψm.restrict.enorm
  simp only [Pi.mul_apply] at hHolder
  -- Step 4: `ψ^q ≤ ψ` since `0 ≤ ψ ≤ 1` and `q ≥ 1`; so `∫_B ψ^q ≤ ∫ ψ`.
  have hψq : ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) :=
    calc ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ∫⁻ x in B, ‖ψ x‖ₑ ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one (hψle x) hpq.symm.lt.le
      _ ≤ ∫⁻ x, ‖ψ x‖ₑ ∂μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, ψ x ∂μ) := hψI
  -- The estimate in `[0, ∞]`.
  have key : ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ ≤ ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) :=
    calc ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ
        ≤ ∫⁻ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) ∂μ := lintegral_indicator hBm _
      _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ‖ψ x‖ₑ ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * (∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * ?_
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * (_ * ?_)
          exact ENNReal.rpow_le_rpow hψq hpq.symm.one_div_nonneg
  -- Step 5: back to real numbers; every factor on the right is finite.
  have hfin : ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hHp.ne)
        (ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top))
  have h := ENNReal.toReal_mono hfin key
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hψnn,
    Real.norm_eq_abs] at h
  rw [hq1, mul_assoc]
  exact h
/-- Continuity in the scale of a radial-profile integral (step 2(c) of the annular monotonicity
proof, parts (a) and (b) of `allard52_am_cutoff_integral_calculus`): if `f` is `μ`-integrable on
`B_S(y)`, `g` is continuous with `g = 0` on `(T, ∞)`, `T > 0`, `t > 0` and `T t < S`, then
`s ↦ ∫ g(‖x − y‖/s) f(x) dμ` is continuous at `t`.  For `0 < s < S/T` the integrand vanishes off
`B_S(y)`, so the integral is taken against `μ ⌞ B_S(y)`; there `|g| ≤ C` on `[0, ∞)` gives the
dominating function `C |f|`, and dominated convergence applies. -/
theorem allard52_am_cc_profile_integral_continuousAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (g : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → Continuous g → 0 < T → (∀ u : ℝ, T < u → g u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, g (‖x - y‖ / s) * f x ∂μ) t := by
  intro n ℓ μ y f g S T t hf hg hT hg0 ht htS
  have hfν : Integrable f (μ.restrict (closedBall y S)) := hf
  -- Step 1: `t < S/T`, so `(0, S/T)` is a neighbourhood of `t`.
  have htR : t < S / T := by
    rw [lt_div_iff₀ hT]
    linarith
  -- Step 2: for `s ∈ (0, S/T)` and `x ∉ B_S(y)`, `‖x − y‖/s > T`, so the integrand vanishes
  -- off `B_S(y)` and the `μ`-integral is the `μ ⌞ B_S(y)`-integral.
  have hconv : ∀ s ∈ Ioo 0 (S / T),
      ∫ x, g (‖x - y‖ / s) * f x ∂(μ.restrict (closedBall y S)) =
        ∫ x, g (‖x - y‖ / s) * f x ∂μ := by
    rintro s ⟨hs, hsR⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hT] at hsR
    have h1 : T < ‖x - y‖ / s := by
      rw [lt_div_iff₀ hs]
      nlinarith
    rw [hg0 _ h1, zero_mul]
  -- Step 3: `|g u| ≤ C` for `u ≥ 0`, with `C` a bound for `|g|` on `[0, T]`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hg.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hg0 u h, abs_zero]
      exact le_max_right _ _
  -- Steps 4-6: dominated convergence for `μ ⌞ B_S(y)` at `t`, with bound `C ‖f‖`.
  have hmain : ContinuousAt (fun s =>
      ∫ x, g (‖x - y‖ / s) * f x ∂(μ.restrict (closedBall y S))) t := by
    refine continuousAt_of_dominated (bound := fun x => C * ‖f x‖) ?_ ?_
      (hfν.norm.const_mul C) ?_
    · -- Step 4: `x ↦ g(‖x − y‖/s)` is continuous and `f` is a.e. strongly measurable.
      refine Eventually.of_forall fun s => ?_
      exact (hg.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / s)
        ).aestronglyMeasurable.mul hfν.aestronglyMeasurable
    · -- Step 3: for `s > 0`, `‖x − y‖/s ≥ 0`, so `|g(‖x − y‖/s) f(x)| ≤ C ‖f(x)‖`.
      filter_upwards [lt_mem_nhds ht] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC _ (div_nonneg (norm_nonneg _) hs.le)) (norm_nonneg _)
    · -- Step 5: `s ↦ g(‖x − y‖/s) f(x)` is continuous at `t ≠ 0`.
      refine Eventually.of_forall fun x => ?_
      exact (hg.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')).mul
        continuousAt_const
  -- Step 7: both functions agree on the neighbourhood `(0, S/T)` of `t`.
  exact hmain.congr (Filter.eventually_of_mem (Ioo_mem_nhds ht htR) hconv)

/-- Differentiation in the scale of a radial cutoff integral (step 2(c) of the annular
monotonicity proof, part (c) of `allard52_am_cutoff_integral_calculus`): if `f` is
`μ`-integrable on `B_S(y)`, `φ` is `C¹` with `φ = 0` on `[T, ∞)`, `T > 0`, `t > 0` and `T t < S`,
then `s ↦ ∫ φ(‖x − y‖/s) f(x) dμ` has derivative `-(∫ (‖x − y‖/t) φ'(‖x − y‖/t) f(x) dμ)/t` at `t`.
For `0 < s < S/T` the integrands vanish off `B_S(y)`; on `(t/2, S/T)` the `s`-derivatives are
bounded by `(2 C₁/t) |f|` with `C₁ = max_{[0,T]} |u φ'(u)|`, and one differentiates under the
integral sign against `μ ⌞ B_S(y)`. -/
theorem allard52_am_cc_cutoff_integral_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t := by
  intro n ℓ μ y f φ S T t hf hφ hT hφ0 ht htS
  set K : Set (Amb n ℓ) := closedBall y S with hK
  set ν : Measure (Amb n ℓ) := μ.restrict K with hν
  have hfν : Integrable f ν := hf
  have hφc : Continuous φ := hφ.continuous
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
  -- Step 2: `φ' = 0` on `(T, ∞)`.
  have hdzero : ∀ u, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφ0 v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  -- Step 3: `|φ u| ≤ C₀` and `|u φ'(u)| ≤ C₁` for `u ≥ 0`.
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hφc.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hφ0 u h.le, abs_zero]
      exact le_max_right _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → |u * deriv φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuous_id.mul hdφc).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hdzero u h, mul_zero, abs_zero]
      exact le_max_right _ _
  -- Step 5: `d/ds φ(r/s) = -(r/s) φ'(r/s) / s` for `s ≠ 0`.
  have hderiv : ∀ (r s : ℝ), s ≠ 0 →
      HasDerivAt (fun u => φ (r / u)) (-(r / s * deriv φ (r / s)) / s) s := by
    intro r s hs
    have h1 : HasDerivAt (fun u : ℝ => r / u) (r * -(s ^ 2)⁻¹) s := by
      have := (hasDerivAt_inv hs).const_mul r
      convert this using 1
      funext u
      exact div_eq_mul_inv r u
    have h2 := ((hφ.differentiable (by simp) (r / s)).hasDerivAt).comp s h1
    have heq : -(r / s * deriv φ (r / s)) / s = deriv φ (r / s) * (r * -(s ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  -- Step 1: `t < R := S / T`; we work on the neighbourhood `(t/2, R)` of `t`.
  set R : ℝ := S / T with hR
  have hRiff : ∀ s : ℝ, s < R ↔ T * s < S := fun s => by
    rw [hR, lt_div_iff₀ hT, mul_comm]
  have htR : t < R := (hRiff t).2 htS
  -- Step 2: for `0 < s < R` the integrands vanish off `K = B_S(y)`.
  have hout : ∀ s, 0 < s → s < R → ∀ x, x ∉ K → T < ‖x - y‖ / s := by
    intro s hs hsR x hx
    have hxS : S < ‖x - y‖ := by
      simpa [hK, mem_closedBall, dist_eq_norm, not_le] using hx
    rw [lt_div_iff₀ hs]
    linarith [(hRiff s).1 hsR]
  have hconv : ∀ s, 0 < s → s < R →
      ∫ x, φ (‖x - y‖ / s) * f x ∂μ = ∫ x, φ (‖x - y‖ / s) * f x ∂ν := by
    intro s hs hsR
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hφ0 _ (hout s hs hsR x hx).le, zero_mul]
  have hconv' : ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ =
      ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂ν := by
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hdzero _ (hout t ht htR x hx), mul_zero, zero_mul]
  -- Step 4: measurability, and integrability of the integrand at `t`, for `ν`.
  have hmeas : ∀ s, AEStronglyMeasurable (fun x => φ (‖x - y‖ / s) * f x) ν := fun s =>
    (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / s)).aestronglyMeasurable.mul
      hfν.aestronglyMeasurable
  have hint : Integrable (fun x => φ (‖x - y‖ / t) * f x) ν := by
    refine Integrable.mono' (hfν.norm.const_mul C₀) (hmeas t) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC₀ _ (div_nonneg (norm_nonneg _) ht.le)) (norm_nonneg _)
  -- Step 6: differentiation under the integral sign for `ν` on `(t/2, R)`, bound `(2C₁/t)‖f‖`.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s x => φ (‖x - y‖ / s) * f x)
    (F' := fun s x => -(‖x - y‖ / s * deriv φ (‖x - y‖ / s)) / s * f x)
    (x₀ := t) (bound := fun x => 2 * C₁ / t * ‖f x‖) (s := Ioo (t / 2) R)
    (Ioo_mem_nhds (half_lt_self ht) htR) (Eventually.of_forall hmeas) hint ?_ ?_
    (hfν.norm.const_mul _) ?_
  -- Step 7: evaluate the derivative and transfer from `ν` back to `μ` near `t`.
  · have hderivν := key.2
    have heq : (∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t * f x ∂ν) =
        -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t := by
      rw [hconv', ← integral_neg, ← integral_div]
      congr 1
      funext x
      ring
    rw [heq] at hderivν
    refine hderivν.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht htR] with s hs
    exact hconv s hs.1 hs.2
  · exact (by fun_prop : Continuous fun x : Amb n ℓ =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t).aestronglyMeasurable.mul hfν.aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs0]
    have h1 : |‖x - y‖ / s * deriv φ (‖x - y‖ / s)| / s ≤ 2 * C₁ / t := by
      rw [div_le_div_iff₀ hs0 ht]
      have := hC₁ _ (div_nonneg (norm_nonneg (x - y)) hs0.le)
      nlinarith [hs.1]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    exact (hderiv ‖x - y‖ s hs0.ne').mul_const (f x)

/-- **Simon Ch. 4, 3.3–3.4 and 4.1** (step 2(c) of the annular monotonicity argument: calculus in
the scale of radial cutoff integrals, where `s ∂ₛ φ(r/s) = -(r/s) φ'(r/s)`).  Let `f` be
`μ`-integrable on `B_S(y)`, let `φ` be `C¹` with `φ = 0` on `[T, ∞)`, `T > 0`, and let `t > 0`
with `T t < S`; write `r = ‖x − y‖`.  Then
(a) `s ↦ ∫ φ(r/s) f dμ` and (b) `s ↦ ∫ (r/s) φ'(r/s) f dμ` are continuous at `t`, and
(c) `s ↦ ∫ φ(r/s) f dμ` has derivative `-(∫ (r/t) φ'(r/t) f dμ)/t` at `t`.
(a) and (b) are `allard52_am_cc_profile_integral_continuousAt` for the continuous profiles
`g = φ` and `g(u) = u φ'(u)`, both zero on `(T, ∞)` (`φ'` vanishes there because `φ` vanishes on
that open set); (c) is `allard52_am_cc_cutoff_integral_hasDerivAt`. -/
theorem allard52_am_cutoff_integral_calculus : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) t ∧ ContinuousAt (fun s => ∫ x, ‖x - y‖ / s * deriv φ (‖x - y‖ / s) * f x ∂μ) t ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t := by
  intro n ℓ μ y f φ S T t hf hφ hT hφT ht hTt
  -- `φ' = 0` on `(T, ∞)`: near each `u > T`, `φ` agrees with the zero function.
  have hdφT : ∀ u : ℝ, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφT v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  refine ⟨?_, ?_, ?_⟩
  -- (a): the profile `g = φ`, continuous as `φ` is `C¹`, and zero on `(T, ∞) ⊆ [T, ∞)`.
  · exact Submission.allard52_am_cc_profile_integral_continuousAt n ℓ μ y f φ S T t hf
      hφ.continuous hT (fun u hu => hφT u hu.le) ht hTt
  -- (b): the profile `g(u) = u φ'(u)`, continuous as `φ'` is; `g(r/s) f` is the integrand.
  · exact Submission.allard52_am_cc_profile_integral_continuousAt n ℓ μ y f
      (fun u => u * deriv φ u) S T t hf (continuous_id.mul hφ.continuous_deriv_one) hT
      (fun u hu => (congrArg (u * ·) (hdφT u hu)).trans (mul_zero u)) ht hTt
  -- (c): differentiation in the scale under the integral sign.
  · exact Submission.allard52_am_cc_cutoff_integral_hasDerivAt n ℓ μ y f φ S T t hf hφ hT hφT
      ht hTt
/-- **Simon Ch. 4, 4.3–4.4** (the integrating factor for the radial first-variation identity).
Let `β < 1` and suppose that on `(0, R)`: `I` is differentiable with `I ≥ 0`, `E` and `Q` are
continuous, `n I − t I' + t Q = −E`, and `|a(t)| ≤ M t^{−β}`, where `a = E/t^{n+1}/(1 + I/tⁿ)`.
Then for `0 < s ≤ r < R`, with `G(t) = ∫₀ᵗ a`,
`e^{−G(r)} (1 + I(r)/rⁿ) − e^{−G(s)} (1 + I(s)/sⁿ) = ∫ₛʳ e^{−G(t)} Q(t)/tⁿ dt`.
Proof: `a` is continuous on `(0, R)` (since `1 + I/tⁿ ≥ 1`) and dominated by `M τ^{−β}`, which is
integrable at `0`, so `G' = a` on `(0, R)`.  The hypothesis gives
`(1 + I/tⁿ)' = (t I' − n I)/t^{n+1} = Q/tⁿ + a (1 + I/tⁿ)`, hence
`(e^{−G} (1 + I/tⁿ))' = e^{−G} Q/tⁿ`, and the fundamental theorem of calculus on `[s, r]`
concludes. -/
theorem allard52_am_integrating_factor : ∀ (n : ℕ) (I I' E Q a : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t ∈ Ioo 0 R, HasDerivAt I (I' t) t) → (∀ t ∈ Ioo 0 R, ContinuousAt E t) → (∀ t ∈ Ioo 0 R, ContinuousAt Q t) → (∀ t ∈ Ioo 0 R, 0 ≤ I t) → (∀ t ∈ Ioo 0 R, (n : ℝ) * I t - t * I' t + t * Q t = -E t) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t ∈ Ioo 0 R, |a t| ≤ M * t ^ (-β)) → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) = ∫ t in s..r, Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n) := by
  intro n I I' E Q a R M β hβ hI hE hQ hI0 hid ha hab s r hs hsr hrR
  -- Notation: `Ψ(t) = 1 + I(t)/tⁿ`; on `(0, R)` we have `Ψ ≥ 1 > 0`.
  have hΨpos : ∀ t ∈ Ioo 0 R, 0 < 1 + I t / t ^ n := by
    intro t ht
    have : 0 ≤ I t / t ^ n := div_nonneg (hI0 t ht) (pow_nonneg ht.1.le n)
    linarith
  -- Step 1: `a` is continuous on `(0, R)`.
  have hac : ∀ t ∈ Ioo 0 R, ContinuousAt a t := by
    intro t ht
    have ha' : a = fun t => E t / t ^ (n + 1) / (1 + I t / t ^ n) := funext ha
    rw [ha']
    exact ((hE t ht).div (continuous_pow (n + 1)).continuousAt (pow_ne_zero _ ht.1.ne')).div
      (continuousAt_const.add ((hI t ht).continuousAt.div (continuous_pow n).continuousAt
        (pow_ne_zero _ ht.1.ne'))) (hΨpos t ht).ne'
  have hacon : ContinuousOn a (Ioo 0 R) := fun t ht => (hac t ht).continuousWithinAt
  -- Step 2: `a` is integrable on `[0, t]` for `t ∈ (0, R)`: `|a(τ)| ≤ M τ^{−β}` and `−β > −1`.
  have haint : ∀ t ∈ Ioo 0 R, IntervalIntegrable a volume 0 t := by
    intro t ht
    have hsub : Ioc 0 t ⊆ Ioo 0 R := fun x hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
    refine ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -β)).const_mul
      M).mono_fun' ?_ ?_
    · rw [uIoc_of_le ht.1.le]
      exact (hacon.mono hsub).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.1.le]
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
      simpa only [Real.norm_eq_abs] using hab x (hsub hx)
  -- Step 3: `G(t) = ∫₀ᵗ a` has `G' = a` on `(0, R)`.
  have hG : ∀ t ∈ Ioo 0 R, HasDerivAt (fun u => ∫ τ in (0)..u, a τ) (a t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (haint t ht)
      (hacon.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hac t ht)
  -- Steps 4–5: `Ψ' = (t I' − n I)/t^{n+1} = Q/tⁿ + E/t^{n+1} = Q/tⁿ + a Ψ` on `(0, R)`.
  have hΨ : ∀ t ∈ Ioo 0 R,
      HasDerivAt (fun u => 1 + I u / u ^ n) (Q t / t ^ n + a t * (1 + I t / t ^ n)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have htn : t ^ n ≠ 0 := pow_ne_zero n ht0
    refine (((hI t ht).div (hasDerivAt_pow n t) htn).const_add 1).congr_deriv ?_
    have hpow : (n : ℝ) * t ^ (n - 1) = n * t ^ n / t := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [eq_div_iff ht0, mul_assoc, pow_sub_one_mul hn.ne']
    have hEt : E t = t * I' t - n * I t - t * Q t := by linarith [hid t ht]
    rw [ha t, div_mul_cancel₀ _ (hΨpos t ht).ne', hpow, pow_succ, hEt]
    field_simp
    ring
  -- Step 6: `Φ(t) = exp(−G(t)) Ψ(t)` has `Φ' = exp(−G) Q/tⁿ` on `(0, R)`.
  have hΦ : ∀ t ∈ Ioo 0 R, HasDerivAt
      (fun u => Real.exp (-∫ τ in (0)..u, a τ) * (1 + I u / u ^ n))
      (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) t := by
    intro t ht
    refine ((hG t ht).neg.exp.mul (hΨ t ht)).congr_deriv ?_
    rw [Pi.neg_apply]
    ring
  -- Step 7: FTC on `[s, r] ⊆ (0, R)`.
  have hsub : uIcc s r ⊆ Ioo 0 R := by
    rw [uIcc_of_le hsr]
    exact fun x hx => ⟨hs.trans_le hx.1, hx.2.trans_lt hrR⟩
  have hcont : ContinuousOn
      (fun t => Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) (uIcc s r) := by
    intro t ht
    have ht' := hsub ht
    exact ((hG t ht').continuousAt.neg.rexp.mul ((hQ t ht').div
      (continuous_pow n).continuousAt (pow_ne_zero n ht'.1.ne'))).continuousWithinAt
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΦ t (hsub ht))
    hcont.intervalIntegrable).symm
/-- **Cutoff-kernel lower bound** (the cutoff form of Simon Ch. 4, 4.7: step 6 of the proof of
`allard52_am_annular_tonelli`, for one fixed `c ∈ [(1 + ε)s, r]`).  For a `C¹` nonincreasing
cutoff `φ` (`φ = 1` on `(−∞, 1]`, `φ = 0` on `[1 + ε, ∞)`), `0 < s` and `(1 + ε)s ≤ c ≤ r`,
`c⁻ⁿ ≤ ∫ₛʳ −((c/t) φ'(c/t))/t · t⁻ⁿ dt`.
Proof: the kernel `k(t) = −((c/t) φ'(c/t))/t` is the derivative of `t ↦ φ(c/t)` and is `≥ 0`
on `[s, r]`, so `∫ₛʳ k = φ(c/r) − φ(c/s) = 1 − 0 = 1`.  Where `k(t) ≠ 0` we have `φ'(c/t) ≠ 0`,
hence `c/t ≥ 1`, i.e. `t ≤ c`, and `k(t) c⁻ⁿ ≤ k(t) t⁻ⁿ`; integrate. -/
theorem allard52_amt_kernel_lower_bound : ∀ (n : ℕ) (φ : ℝ → ℝ) (ε s r c : ℝ), 0 < ε → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → (1 + ε) * s ≤ c → c ≤ r → 1 / c ^ n ≤ ∫ t in s..r, -(c / t * deriv φ (c / t)) / t / t ^ n := by
  intro n φ ε s r c hε hφ hanti hone hzero hs hsc hcr
  -- step 1: `0 < s ≤ c ≤ r`
  have hc : 0 < c := by nlinarith
  have hsr : s ≤ r := by nlinarith
  have hr : 0 < r := hc.trans_le hcr
  have hpos : ∀ t ∈ Icc s r, 0 < t := fun t ht => hs.trans_le ht.1
  -- step 2: `φ'` is continuous, `φ' ≤ 0`, and `φ' = 0` on `(−∞, 1)`
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hdcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hdnp : ∀ u, deriv φ u ≤ 0 := fun u => hanti.deriv_nonpos
  have hdlo : ∀ u, u < 1 → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact hone v hv.le
    exact h.deriv_eq.trans (deriv_const u 1)
  -- step 3: the kernel `k` is continuous and nonnegative on `[s, r]`
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => -(c / t * deriv φ (c / t)) / t := ⟨_, rfl⟩
  have hct : ContinuousOn (fun t : ℝ => c / t) (Icc s r) :=
    continuousOn_const.div continuousOn_id fun t ht => (hpos t ht).ne'
  have hkcont : ContinuousOn k (Icc s r) := by
    rw [hk]
    exact ((hct.mul (hdcont.comp_continuousOn hct)).neg).div continuousOn_id
      fun t ht => (hpos t ht).ne'
  have hknn : ∀ t ∈ Icc s r, 0 ≤ k t := by
    intro t ht
    have ht0 := hpos t ht
    rw [hk]
    exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg hc.le ht0.le) (hdnp _))) ht0.le
  -- step 4: `∫ₛʳ k = φ(c/r) − φ(c/s) = 1`
  have hderiv : ∀ t ∈ uIcc s r, HasDerivAt (fun t => φ (c / t)) (k t) t := by
    intro t ht
    rw [uIcc_of_le hsr] at ht
    have ht0 := hpos t ht
    have h1 : HasDerivAt (fun t => c / t) (c * -(t ^ 2)⁻¹) t := by
      simpa only [div_eq_mul_inv] using (hasDerivAt_inv ht0.ne').const_mul c
    have h2 : HasDerivAt (fun t => φ (c / t)) (deriv φ (c / t) * (c * -(t ^ 2)⁻¹)) t :=
      (hdiff (c / t)).hasDerivAt.comp t h1
    convert h2 using 1
    rw [hk]
    field_simp
  have hkint : IntervalIntegrable k volume s r := hkcont.intervalIntegrable_of_Icc hsr
  have hint1 : ∫ t in s..r, k t = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkint,
      hone _ ((div_le_one hr).mpr hcr), hzero _ ((le_div_iff₀ hs).mpr hsc), sub_zero]
  -- step 5: `k(t) c⁻ⁿ ≤ k(t) t⁻ⁿ` on `[s, r]`
  have hpt : ∀ t ∈ Icc s r, k t * (1 / c ^ n) ≤ k t * (1 / t ^ n) := by
    intro t ht
    have ht0 := hpos t ht
    by_cases hk0 : k t = 0
    · rw [hk0, zero_mul, zero_mul]
    · have hd : deriv φ (c / t) ≠ 0 := by
        intro hd
        apply hk0
        rw [hk]
        simp only [hd, mul_zero, neg_zero, zero_div]
      have h1 : 1 ≤ c / t := by
        by_contra hlt
        push Not at hlt
        exact hd (hdlo _ hlt)
      have htc : t ≤ c := by
        rwa [le_div_iff₀ ht0, one_mul] at h1
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (pow_pos ht0 n) (pow_le_pow_left₀ ht0.le htc n)) (hknn t ht)
  -- step 6: integrate
  have hint2 : IntervalIntegrable (fun t => k t * (1 / t ^ n)) volume s r := by
    refine ContinuousOn.intervalIntegrable_of_Icc hsr (hkcont.mul ?_)
    exact continuousOn_const.div (continuousOn_id.pow n) fun t ht => (pow_pos (hpos t ht) n).ne'
  have hmono := intervalIntegral.integral_mono_on hsr (hkint.mul_const (1 / c ^ n)) hint2 hpt
  rw [intervalIntegral.integral_mul_const, hint1, one_mul] at hmono
  refine hmono.trans_eq (intervalIntegral.integral_congr fun t _ => ?_)
  simp only [hk]
  ring
/-- **Tonelli identity for the cutoff kernel** (the cutoff form of Simon Ch. 4, 4.7: steps 1–5 and
8 of the proof of `allard52_am_annular_tonelli`).  Let `μ(B_R(y)) < ∞`, let `w` be a.e. strongly
measurable for `μ ⌞ B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. on `B̆_R(y)`, let `φ` be `C¹` and
nonincreasing with `φ = 0` on `[1 + ε, ∞)`, and let `0 < s ≤ r`, `(1 + ε)r < R`.  With
`r_x = |x − y|` and `H(x) = ∫ₛʳ −((r_x/t) φ'(r_x/t))/t · t⁻ⁿ dt`, the lower integral of `w H`
against `μ` is `∫ₛʳ −(∫ (r_x/t) φ'(r_x/t) w dμ)/t · t⁻ⁿ dt`.
Proof: for `t ∈ [s, r]` the kernel vanishes off `B = B_{(1+ε)r}(y) ⊆ B̆_R(y)`, so both sides only
see the finite measure `ν = μ ⌞ B`, and `H ≥ 0` since `φ' ≤ 0`.  The integrand
`−((r_x/t) φ'(r_x/t))/t · t⁻ⁿ · w(x)` is a.e. strongly measurable and bounded on `[s, r] × B`, hence
integrable for `𝓛¹ ⌞ (s, r] × ν`; Fubini swaps the integrals, and `w H ≥ 0` `ν`-a.e. turns the
Bochner integral into the lower integral. -/
theorem allard52_amt_fubini_lintegral : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (R ε s r : ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → s ≤ r → (1 + ε) * r < R → ∫⁻ x, ENNReal.ofReal (w x * (∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ = ENNReal.ofReal (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) := by
  intro n ℓ μ w y φ R ε s r hε hμR hw hw01 hφ hφanti hφzero hs hsr hR
  -- step 1: `B = B_{(1+ε)r}(y) ⊆ B̆_R(y)`, `ν = μ ⌞ B` and `𝓛¹ ⌞ (s, r]` are finite; facts on `φ'`
  have hBball : closedBall y ((1 + ε) * r) ⊆ ball y R := closedBall_subset_ball hR
  have hBmeas : MeasurableSet (closedBall y ((1 + ε) * r)) := isClosed_closedBall.measurableSet
  have : IsFiniteMeasure (μ.restrict (closedBall y ((1 + ε) * r))) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (hBball.trans ball_subset_closedBall)).trans_lt hμR).ne
  have : IsFiniteMeasure (volume.restrict (uIoc s r)) := isFiniteMeasure_restrict.mpr (by
    rw [uIoc_of_le hsr, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hdcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hdnonpos : ∀ u, deriv φ u ≤ 0 := fun u => hφanti.deriv_nonpos
  have hdzero : ∀ u, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv => hφzero v (le_of_lt hv)
    rw [h.deriv_eq, deriv_const]
  -- step 2: the kernel `a(t, x) = (r_x/t) φ'(r_x/t)` vanishes for `t ∈ [s, r]` and `x ∉ B`
  have hvan : ∀ t ∈ Icc s r, ∀ x ∉ closedBall y ((1 + ε) * r),
      ‖x - y‖ / t * deriv φ (‖x - y‖ / t) = 0 := by
    intro t ht x hx
    have ht0 : 0 < t := hs.trans_le ht.1
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have h1 : (1 + ε) * t < ‖x - y‖ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 (by linarith)) hx
    rw [hdzero _ ((lt_div_iff₀ ht0).mpr h1), mul_zero]
  -- step 3: `H(x) ≥ 0`
  have hHnn : ∀ x, 0 ≤ ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    intro x
    refine intervalIntegral.integral_nonneg hsr fun t ht => ?_
    have ht0 : 0 < t := hs.trans_le ht.1
    exact div_nonneg (div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (norm_nonneg _) ht0.le) (hdnonpos _))) ht0.le) (pow_pos ht0 n).le
  -- step 4: the left side only sees `B`, since `H = 0` off `B`
  have hLHS : ∫⁻ x, ENNReal.ofReal (w x * (∫ t in s..r,
        -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ
      = ∫⁻ x in closedBall y ((1 + ε) * r), ENNReal.ofReal (w x * (∫ t in s..r,
        -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)) ∂μ := by
    refine (setLIntegral_eq_of_support_subset
      (Function.support_subset_iff'.mpr fun x hx => ?_)).symm
    have h0 : EqOn (fun t => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)
        (fun _ => (0 : ℝ)) (uIcc s r) := by
      intro t ht
      rw [uIcc_of_le hsr] at ht
      simp only [hvan t ht x hx, neg_zero, zero_div]
    rw [intervalIntegral.integral_congr h0]
    simp
  -- step 5: each inner `μ`-integral is the `ν`-integral of `F(t, x) = −a(t, x)/t · t⁻ⁿ · w(x)`
  have hRHS : EqOn (fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n)
      (fun t => ∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x
        ∂(μ.restrict (closedBall y ((1 + ε) * r)))) (uIcc s r) := by
    intro t ht
    rw [uIcc_of_le hsr] at ht
    have h1 : ∀ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x
        = (-1 / t / t ^ n) * (‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x) := fun x => by ring
    simp only [h1, integral_const_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hvan t ht x hx, zero_mul]]
    ring
  -- step 6: `F` is integrable for `𝓛¹ ⌞ (s, r] × ν`: measurable kernel times `w ∘ snd`, bounded
  have hKmeas : Measurable fun p : ℝ × Amb n ℓ =>
      -(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n := by
    have hu : Measurable fun p : ℝ × Amb n ℓ => ‖p.2 - y‖ / p.1 :=
      (measurable_snd.sub_const y).norm.div measurable_fst
    exact ((hu.mul ((measurable_deriv φ).comp hu)).neg.div measurable_fst).div
      (measurable_fst.pow_const n)
  have hwν : AEStronglyMeasurable w (μ.restrict (closedBall y ((1 + ε) * r))) :=
    hw.mono_measure (Measure.restrict_mono hBball le_rfl)
  have hKcont : ContinuousOn (fun p : ℝ × Amb n ℓ =>
      -(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n)
      (Icc s r ×ˢ closedBall y ((1 + ε) * r)) := by
    have h1 : ∀ p ∈ Icc s r ×ˢ closedBall y ((1 + ε) * r), p.1 ≠ 0 :=
      fun p hp => (hs.trans_le hp.1.1).ne'
    have hu : ContinuousOn (fun p : ℝ × Amb n ℓ => ‖p.2 - y‖ / p.1)
        (Icc s r ×ˢ closedBall y ((1 + ε) * r)) :=
      ContinuousOn.div (by fun_prop) continuousOn_fst h1
    exact ((hu.mul (hdcont.comp_continuousOn hu)).neg.div continuousOn_fst h1).div
      (continuousOn_fst.pow n) fun p hp => pow_ne_zero n (h1 p hp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
    (isCompact_closedBall y ((1 + ε) * r))).exists_bound_of_continuousOn hKcont
  have hae1 : ∀ᵐ p ∂((volume.restrict (uIoc s r)).prod
      (μ.restrict (closedBall y ((1 + ε) * r)))), p.1 ∈ Ioc s r := by
    have h : ∀ᵐ t ∂(volume.restrict (uIoc s r)), t ∈ Ioc s r := by
      rw [uIoc_of_le hsr]; exact ae_restrict_mem measurableSet_Ioc
    exact Measure.quasiMeasurePreserving_fst.ae h
  have hae2 : ∀ᵐ p ∂((volume.restrict (uIoc s r)).prod
      (μ.restrict (closedBall y ((1 + ε) * r)))),
      p.2 ∈ closedBall y ((1 + ε) * r) ∧ (p.2 ∈ ball y R → 0 ≤ w p.2 ∧ w p.2 ≤ 1) := by
    have h : ∀ᵐ x ∂(μ.restrict (closedBall y ((1 + ε) * r))),
        x ∈ closedBall y ((1 + ε) * r) ∧ (x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) :=
      (ae_restrict_mem hBmeas).and (ae_restrict_of_ae hw01)
    exact Measure.quasiMeasurePreserving_snd.ae h
  have hFint : Integrable (Function.uncurry fun t x =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x)
      ((volume.restrict (uIoc s r)).prod (μ.restrict (closedBall y ((1 + ε) * r)))) := by
    refine Integrable.mono' (integrable_const C)
      (hKmeas.aestronglyMeasurable.mul hwν.comp_snd) ?_
    filter_upwards [hae1, hae2] with p hp1 hp2
    have hpK := hC p ⟨Ioc_subset_Icc_self hp1, hp2.1⟩
    have hw1 := hp2.2 (hBball hp2.1)
    show ‖-(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n * w p.2‖ ≤ C
    rw [norm_mul]
    have hwn : ‖w p.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hw1.1, hw1.2]
    calc _ ≤ ‖-(‖p.2 - y‖ / p.1 * deriv φ (‖p.2 - y‖ / p.1)) / p.1 / p.1 ^ n‖ * 1 :=
          mul_le_mul_of_nonneg_left hwn (norm_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hpK
  -- step 7: Fubini; the inner `t`-integral of `F(·, x)` is `w(x) H(x)`, which is `ν`-integrable
  have hswap := intervalIntegral_integral_swap hFint
  have hinner : ∀ x, (∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n * w x)
      = w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    intro x
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  have hint : Integrable
      (fun x => w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n)
      (μ.restrict (closedBall y ((1 + ε) * r))) := by
    refine hFint.integral_prod_right.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← hinner x, intervalIntegral.integral_of_le hsr, uIoc_of_le hsr]
  -- step 8: `w H ≥ 0` `ν`-a.e.
  have hnn : 0 ≤ᵐ[μ.restrict (closedBall y ((1 + ε) * r))]
      fun x => w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n := by
    filter_upwards [ae_restrict_mem hBmeas, ae_restrict_of_ae hw01] with x hxB hx
    exact mul_nonneg (hx (hBball hxB)).1 (hHnn x)
  -- step 9: assemble
  rw [hLHS, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    intervalIntegral.integral_congr hRHS, hswap]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => (hinner x).symm)
/-- **Simon Ch. 4, 3.4–3.5 and 4.7** (the Tonelli step for one fixed cutoff `φ`).  Let `ε > 0`,
`μ(B_R(y)) < ∞`, `w` a.e.-strongly measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. there, and `φ`
a nonincreasing `C¹` function with `φ = 1` on `(−∞, 1]` and `φ = 0` on `[1 + ε, ∞)`.  If
`0 < s ≤ r` and `(1 + ε) r < R`, then with `r_x = |x − y|` and
`Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w(x) dμ`,
`∫_{B_r(y) \ B̆_{(1+ε)s}(y)} w r_x⁻ⁿ dμ ≤ ∫ₛʳ Q(t) t⁻ⁿ dt`.
Proof: for `x` in the annulus, `c = r_x ∈ [(1 + ε) s, r]`, so the kernel bound
`c⁻ⁿ ≤ h(c) = ∫ₛʳ −(c/t φ'(c/t))/t/tⁿ dt` and `w(x) ≥ 0` give `w r_x⁻ⁿ ≤ w h(r_x)`; enlarging the
domain to `ℝ^{n+ℓ}` and Tonelli, `∫ w h(r_x) dμ = ∫ₛʳ Q(t)/tⁿ dt`, conclude. -/
theorem allard52_am_annular_tonelli : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℝ → ℝ) (R ε s r : ℝ), 0 < ε → μ (closedBall y R) < ⊤ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → 0 < s → s ≤ r → (1 + ε) * r < R → ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) := by
  intro n ℓ μ w y φ R ε s r hε hμ hw hw01 hφ hanti hφ1 hφ0 hs hsr hrR
  -- Step 1: `r < (1 + ε) r < R`, so the annulus `A = B_r(y) \ B̆_{(1+ε)s}(y)` lies in `B̆_R(y)`.
  have hrR' : r < R := by nlinarith [mul_pos hε (hs.trans_le hsr)]
  calc ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ
      ≤ ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal
          (w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n) ∂μ := by
        -- Step 2: on `A`, `w ≥ 0` a.e. and `r_x⁻ⁿ ≤ h(r_x)` (kernel bound with `c = r_x`).
        refine setLIntegral_mono_ae' (measurableSet_closedBall.diff measurableSet_ball) ?_
        filter_upwards [hw01] with x hx hxA
        have hxr : ‖x - y‖ ≤ r := mem_closedBall_iff_norm.1 hxA.1
        have hxs : (1 + ε) * s ≤ ‖x - y‖ := not_lt.1 fun h => hxA.2 (mem_ball_iff_norm.2 h)
        have hw0 : 0 ≤ w x := (hx (mem_ball_iff_norm.2 (hxr.trans_lt hrR'))).1
        refine ENNReal.ofReal_le_ofReal ((div_eq_mul_one_div _ _).trans_le ?_)
        exact mul_le_mul_of_nonneg_left (Submission.allard52_amt_kernel_lower_bound n φ ε s r
          ‖x - y‖ hε hφ hanti hφ1 hφ0 hs hxs hxr) hw0
    _ ≤ ∫⁻ x, ENNReal.ofReal
          (w x * ∫ t in s..r, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t / t ^ n) ∂μ :=
        setLIntegral_le_lintegral _ _
    -- Step 3: Tonelli, `∫ w h(r_x) dμ = ∫ₛʳ Q(t)/tⁿ dt`.
    _ = ENNReal.ofReal
          (∫ t in s..r, -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t / t ^ n) :=
        Submission.allard52_amt_fubini_lintegral n ℓ μ w y φ R ε s r hε hμ hw hw01 hφ hanti hφ0
          hs hsr hrR
/-- **Simon Ch. 4, 4.8–4.9** (density at the centre, for an abstract measure `μ`).  Let `R, α > 0`,
`μ(B_R(y)) < ∞`, and on `(0, R)` let `e^{-Λ} ≤ F(r) ≤ e^Λ` and `|F(r) − 1| ≤ Λ (r/R)^α`.  If
`Φ(r) = F(r) r⁻ⁿ μ(B_r(y)) + F(r) − 1` is nondecreasing on `(0, R)`, then there is `t ≥ 0` with
`μ(B_r(y)) / (ω_n rⁿ) → t` as `r ↓ 0`, and `ω_n t ≤ Φ(r)` for every `r ∈ (0, R)`.
Proof: `F → 1` as `r ↓ 0`; `Φ ≥ e^{-Λ} − 1` is monotone, so it tends to `L = inf Φ`; hence
`r⁻ⁿ μ(B_r(y)) = (Φ(r) + 1)/F(r) − 1 → L ≥ 0`, and `t = L/ω_n` works since `ω_n > 0`. -/
theorem allard52_am_center_density : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (F : ℝ → ℝ) (R Λ α : ℝ), 0 < R → 0 < α → μ (closedBall y R) < ⊤ → (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ α) → (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) → ∃ t : ℝ, 0 ≤ t ∧ Tendsto (fun r : ℝ => μ (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * t ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 := by
  intro n ℓ μ y F R Λ α hR hα hfin hF hmono0
  -- Notation: `Φ(r) = F(r) r⁻ⁿ m(r) + F(r) − 1` with `m(r) = μ(B_r(y))`.
  set Φ := fun r : ℝ => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 with hΦ
  have hmono : MonotoneOn Φ (Ioo 0 R) := fun s hs r hr hsr => hmono0 s r hs.1 hsr hr.2
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
  -- Step 1: on `(0, R)`, `μ(B_r(y)) ≤ μ(B_R(y)) < ∞` and `F(r) ≥ e^{-Λ} > 0`.
  have hmfin : ∀ r ∈ Ioo 0 R, μ (closedBall y r) ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hfin.ne (measure_mono (closedBall_subset_closedBall hr.2.le))
  have hFpos : ∀ r ∈ Ioo 0 R, 0 < F r := fun r hr => (Real.exp_pos _).trans_le (hF r hr).1
  -- Step 2: `F → 1` as `r ↓ 0`, squeezing `|F(r) − 1| ≤ Λ (r/R)^α → Λ 0^α = 0` (`α > 0`).
  have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    have hlim : Tendsto (fun r : ℝ => Λ * (r / R) ^ α) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => Λ * (r / R) ^ α) (𝓝 0) (𝓝 (Λ * (0 / R) ^ α)) :=
        ((tendsto_id.div_const R).rpow_const (Or.inr hα.le)).const_mul Λ
      rw [zero_div, Real.zero_rpow hα.ne', mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    rw [Real.norm_eq_abs]
    exact (hF r hr).2.2
  -- Step 3: `Φ(r) ≥ F(r) − 1 ≥ e^{-Λ} − 1` on `(0, R)`; the monotone `Φ` tends to `L = inf Φ`.
  have hbdd : BddBelow (Φ '' Ioo 0 R) := by
    refine ⟨Real.exp (-Λ) - 1, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have h1 := (hF r hr).1
    have h2 : 0 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
      mul_nonneg (mul_nonneg (hFpos r hr).le (inv_nonneg.2 (pow_nonneg hr.1.le n)))
        ENNReal.toReal_nonneg
    simp only [hΦ]
    linarith
  set L := sInf (Φ '' Ioo 0 R)
  have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := hmono.tendsto_nhdsWithin_Ioo_right hne hbdd
  -- Step 4: `r⁻ⁿ m(r) = (Φ(r) + 1)/F(r) − 1 → (L + 1)/1 − 1 = L`, and `L ≥ 0`.
  set g := fun r : ℝ => (r ^ n)⁻¹ * (μ (closedBall y r)).toReal with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 L) := by
    have h := ((hΦL.add_const 1).div hF1 one_ne_zero).sub_const 1
    have heq : (fun r => (Φ r + 1) / F r - 1) =ᶠ[𝓝[>] 0] g := by
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      have hFr : F r ≠ 0 := (hFpos r hr).ne'
      simp only [hΦ, hg_def]
      field_simp
      ring
    simpa using h.congr' heq
  have hL0 : 0 ≤ L := by
    apply ge_of_tendsto hg
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg (le_of_lt hr) n)) ENNReal.toReal_nonneg
  -- Step 5: `ω_n = π^{n/2}/Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Step 6: `t = L/ω_n`; on `(0, R)`, `μ(B_r(y)) / ofReal(ω_n rⁿ) = ofReal(r⁻ⁿ m(r)/ω_n)`.
  refine ⟨L / unitBallVolume n, div_nonneg hL0 hω.le, ?_, ?_⟩
  · have h := ENNReal.tendsto_ofReal (hg.div_const (unitBallVolume n))
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    have hr0 : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr.1 n)
    rw [← ENNReal.ofReal_toReal (hmfin r hr), ← ENNReal.ofReal_div_of_pos hr0]
    congr 1
    simp only [hg_def]
    field_simp
  -- Step 7: `ω_n t = L ≤ Φ(r)` for every `r ∈ (0, R)`.
  · intro r hr
    rw [mul_div_cancel₀ _ hω.ne']
    exact csInf_le hbdd ⟨r, hr, rfl⟩

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

theorem allard52_amcl_radial_cutoff_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ) (R t : ℝ), 0 < t → t < R → IntegrableOn f (closedBall y R) μ → (∀ k, Continuous (φ k)) → (∀ k u, 0 ≤ φ k u ∧ φ k u ≤ 1) → (∀ k u, u ≤ 1 → φ k u = 1) → (∀ k u, 1 + ε k ≤ u → φ k u = 0) → Tendsto ε atTop (𝓝 0) → Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * f x ∂μ) atTop (𝓝 (∫ x in closedBall y t, f x ∂μ)) := by
  intro n ℓ μ f y φ ε R t ht htR hf hφc hφb hφ1 hφ0 hε
  -- Step 1: eventually `ε k < R / t - 1`, i.e. `(1 + ε k) t < R`.
  have hδ : 0 < R / t - 1 := by
    rw [sub_pos, one_lt_div ht]
    exact htR
  have hev : ∀ᶠ k in atTop, ε k < R / t - 1 := hε.eventually (gt_mem_nhds hδ)
  -- Step 2: for such `k` the integrand vanishes off `B_R(y)`, so the whole-space integral is the
  -- integral against `ν = μ ⌞ B_R(y)` (no integrability needed).
  have heq : ∀ᶠ k in atTop, ∫ x in closedBall y R, φ k (‖x - y‖ / t) * f x ∂μ =
      ∫ x, φ k (‖x - y‖ / t) * f x ∂μ := by
    filter_upwards [hev] with k hk
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have hkt : (1 + ε k) * t < R := (lt_div_iff₀ ht).1 (by linarith)
    have hk1 : 1 + ε k ≤ ‖x - y‖ / t := by
      rw [le_div_iff₀ ht]
      linarith
    rw [hφ0 k _ hk1, zero_mul]
  -- Step 3: the target is the `ν`-integral of `1_{B_t(y)} f`, since `B_t(y) ⊆ B_R(y)`.
  have htarget : ∫ x in closedBall y R, (closedBall y t).indicator f x ∂μ =
      ∫ x in closedBall y t, f x ∂μ := by
    rw [integral_indicator measurableSet_closedBall,
      Measure.restrict_restrict_of_subset (closedBall_subset_closedBall htR.le)]
  -- Steps 4-5: dominated convergence for `ν` with dominating function `‖f‖`.
  have hdct : Tendsto (fun k => ∫ x in closedBall y R, φ k (‖x - y‖ / t) * f x ∂μ) atTop
      (𝓝 (∫ x in closedBall y R, (closedBall y t).indicator f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) (fun k => ?_) hf.norm
      (fun k => ?_) ?_
    · -- (b) measurability: `x ↦ φ k (‖x - y‖ / t)` is continuous and `f` is `ν`-integrable.
      exact (((hφc k).comp ((continuous_norm.comp
        (continuous_id.sub continuous_const)).div_const t)).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
    · -- (c) domination: `0 ≤ φ k ≤ 1`.
      refine Eventually.of_forall (fun x => ?_)
      have hb := hφb k (‖x - y‖ / t)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2
    · -- (d) pointwise limit `1_{B_t(y)} f`.
      refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ closedBall y t
      · rw [indicator_of_mem hx]
        rw [mem_closedBall, dist_eq_norm] at hx
        have hle : ‖x - y‖ / t ≤ 1 := (div_le_one ht).2 hx
        have h1 : ∀ k, φ k (‖x - y‖ / t) * f x = f x := fun k => by
          rw [hφ1 k _ hle, one_mul]
        simp only [h1]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem hx]
        rw [mem_closedBall, dist_eq_norm, not_le] at hx
        have hu : 1 < ‖x - y‖ / t := (one_lt_div ht).2 hx
        have hev2 : ∀ᶠ k in atTop, ε k < ‖x - y‖ / t - 1 :=
          hε.eventually (gt_mem_nhds (by linarith))
        apply tendsto_const_nhds.congr'
        filter_upwards [hev2] with k hk
        rw [hφ0 k _ (by linarith), zero_mul]
  -- Step 6: conclusion.
  rw [← htarget]
  exact hdct.congr' heq
theorem allard52_am_fc_cutoff_facts : ∀ (φ : ℝ → ℝ) (ε : ℝ), 0 < ε → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u : ℝ, deriv φ u ≤ 0) ∧ (∀ u : ℝ, 1 + ε < u → deriv φ u = 0) ∧ Continuous (deriv φ) ∧ ∃ C : ℝ, ∀ u : ℝ, |deriv φ u| ≤ C := by
  intro φ ε hε hφ hanti h1 h0
  -- Step 1: `0 ≤ φ ≤ 1`, by monotonicity and the boundary values `φ (1 + ε) = 0`, `φ 1 = 1`.
  have hbd : ∀ u : ℝ, 0 ≤ φ u ∧ φ u ≤ 1 := by
    intro u
    constructor
    · rcases le_total (1 + ε) u with hu | hu
      · rw [h0 u hu]
      · rw [← h0 (1 + ε) le_rfl]
        exact hanti hu
    · rcases le_total u 1 with hu | hu
      · rw [h1 u hu]
      · rw [← h1 1 le_rfl]
        exact hanti hu
  -- Step 2: `φ' ≤ 0` because `φ` is nonincreasing.
  have hneg : ∀ u : ℝ, deriv φ u ≤ 0 := fun u => hanti.deriv_nonpos
  -- Step 3: `φ' = 0` on `(1 + ε, ∞)` and on `(-∞, 1)`, where `φ` is locally constant.
  have hright : ∀ u : ℝ, 1 + ε < u → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) (fun v hv => h0 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  have hleft : ∀ u : ℝ, u < 1 → deriv φ u = 0 := by
    intro u hu
    have hev : φ =ᶠ[𝓝 u] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu) (fun v hv => h1 v (le_of_lt hv))
    rw [hev.deriv_eq, deriv_const]
  -- Step 4: `φ'` is continuous because `φ` is `C¹`.
  have hcont : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- Step 5: `φ'` is continuous with support in `[1, 1 + ε]`, hence bounded.
  have hsupp : HasCompactSupport (deriv φ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 1) (b := 1 + ε)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact ⟨not_lt.mp fun h => hu (hleft u h), not_lt.mp fun h => hu (hright u h)⟩
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨hbd, hneg, hright, hcont, C, fun u => ?_⟩
  rw [← Real.norm_eq_abs]
  exact hC u
theorem allard52_am_fc_ball_integrable : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R S : ℝ), S < R → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ ∧ IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y S) μ ∧ IntegrableOn w (closedBall y S) μ := by
  intro n ℓ μ H w y R S hSR hR hH hw hwb
  -- Step 1: `B_S(y) ⊆ B̆_R(y) ⊆ B_R(y)`, so `μ(B_S(y)) < ∞`.
  have hSball : closedBall y S ⊆ ball y R := closedBall_subset_ball hSR
  have hSR' : closedBall y S ⊆ closedBall y R := closedBall_subset_closedBall hSR.le
  have hS : μ (closedBall y S) ≠ ⊤ := (lt_of_le_of_lt (measure_mono hSR') hR).ne
  -- Step 2: the constant `1` is integrable on a set of finite measure.
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ := integrableOn_const hS
  refine ⟨h1, ?_, ?_⟩
  · -- Step 3: `|(x - y) · H(x)| ≤ R |H(x)|` on `B_S(y)`, and `R |H|` is integrable there.
    have hHS : IntegrableOn H (closedBall y S) μ := hH.mono_set hSR'
    have hmeas : AEStronglyMeasurable (fun x => inner ℝ (x - y) (H x))
        (μ.restrict (closedBall y S)) :=
      Continuous.comp_aestronglyMeasurable₂ (g := fun u v : Amb n ℓ => inner ℝ u v)
        continuous_inner (continuous_id.sub continuous_const).aestronglyMeasurable
        hHS.aestronglyMeasurable
    refine Integrable.mono' (hHS.norm.const_mul R) hmeas ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall (fun x hx => ?_)
    rw [mem_closedBall, dist_eq_norm] at hx
    calc ‖inner ℝ (x - y) (H x)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
      _ ≤ R * ‖H x‖ := mul_le_mul_of_nonneg_right (hx.trans hSR.le) (norm_nonneg _)
  · -- Step 4: `w` is a.e.-strongly measurable on `B_S(y)` and `|w| ≤ 1` a.e. there.
    have hwS : AEStronglyMeasurable w (μ.restrict (closedBall y S)) :=
      hw.mono_measure (Measure.restrict_mono hSball le_rfl)
    refine Integrable.mono' h1 hwS ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    filter_upwards [hwb] with x hx hxS
    obtain ⟨hw0, hw1⟩ := hx (hSball hxS)
    rw [Real.norm_eq_abs, abs_of_nonneg hw0]
    exact hw1

/-- **Simon Ch. 4, 4.1–4.5** (monotonicity and the annular conical estimate for one fixed cutoff).
Let `1 ≤ n < p`, `R, Λ > 0`, `0 < ε ≤ 1` and `κ = (p − n)/(4p)`.  Let `μ(B_R(y)) < ∞`, let `H` be
`μ`-integrable on `B_R(y)` with `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ κΛ`, let `w` be a.e. strongly
measurable on `B̆_R(y)` with `0 ≤ w ≤ 1` `μ`-a.e. there, and let `φ` be a nonincreasing `C¹` cutoff
(`φ = 1` on `(−∞, 1]`, `φ = 0` on `[1 + ε, ∞)`) satisfying the radial first-variation identity at
every `ρ > 0` with `(1 + ε)ρ < R`.  Write `r_x = |x − y|`, `I(t) = ∫ φ(r_x/t) dμ`,
`E(t) = ∫ φ(r_x/t) (x − y) · H dμ`, `a = E/t^{n+1}/(1 + I/tⁿ)`, `G(t) = ∫₀ᵗ a` and
`Φ(t) = e^{−G(t)} (1 + I(t)/tⁿ)`.  Then
(1) for `t > 0` with `(1 + ε)t < R`, `a` is continuous at `t` and `|a(t)| ≤ 2κΛR⁻¹ (t/R)^{−n/p}`;
(2) for `0 < s ≤ r` with `(1 + ε)r < R`, `Φ(s) ≤ Φ(r)` and
`∫_{B_r(y) \ B̆_{(1+ε)s}(y)} w r_x⁻ⁿ dμ ≤ e^{Λ/2} (Φ(r) − Φ(s))`.
Proof: the cutoff calculus makes `I` differentiable and `E` and
`Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w dμ ≥ 0` continuous, and the radial identity, split by
linearity, reads `n I − t I' + t Q = −E`.  Hölder at radius `(1 + ε)t` and the absorption
`A^{1−1/p} ≤ 1 + A` give (1).  The integrating factor gives `Φ(r) − Φ(s) = ∫ₛʳ e^{−G} Q/tⁿ ≥ 0`;
as `|G| ≤ Λ/2`, `∫ₛʳ Q/tⁿ ≤ e^{Λ/2} (Φ(r) − Φ(s))`, and the annular Tonelli bound concludes. -/
theorem allard52_am_fixed_cutoff : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ ε : ℝ) (φ : ℝ → ℝ) (I E a : ℝ → ℝ), 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → ContDiff ℝ 1 φ → Antitone φ → (∀ u : ℝ, u ≤ 1 → φ u = 1) → (∀ u : ℝ, 1 + ε ≤ u → φ u = 0) → (∀ ρ : ℝ, 0 < ρ → (1 + ε) * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t, E t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧ |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → (1 + ε) * r < R → Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) ≤ Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) ∧ ∫⁻ x in closedBall y r \ ball y ((1 + ε) * s), ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n))) := by
  intro n ℓ hn p hnp μ H w y R Λ ε φ I E a hR hΛ hε hε1 hμR hHR hLp hw hw01 hφ hanti hφ1 hφ0
    hrad hI hE ha
  -- Notation: `r_x = ‖x − y‖`, `I'(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) dμ` and
  -- `Q(t) = −t⁻¹ ∫ (r_x/t) φ'(r_x/t) w dμ`.
  set I' : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t with hI'
  set Q : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * w x ∂μ) / t with hQ
  -- Step 0: constants, `1 < p` and `1 + ε > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := by linarith
  have hp : 0 < p := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  -- Step 1: cutoff facts, `0 ≤ φ ≤ 1`.
  obtain ⟨hφ01, -, -, -, -⟩ :=
    Submission.allard52_am_fc_cutoff_facts φ ε hε hφ hanti hφ1 hφ0
  -- Steps 3(c), 5, 6: the radial split, `I ≥ 0` and `∫ (r_x/t) φ'(r_x/t) w dμ ≤ 0`.
  have hsplit := Submission.allard52_am_fc_radial_split n ℓ μ w y R ε φ hε hμR hw hw01 hφ hanti
    hφ1 hφ0
  -- Step 4: regularity from the cutoff calculus at `t ∈ (0, R/(1 + ε))`, with
  -- `S = ((1 + ε) t + R)/2` and `T = 1 + ε`, for `f = 1`, `(x − y) · H` and `w`.
  have hcalc : ∀ t, 0 < t → (1 + ε) * t < R →
      HasDerivAt I (I' t) t ∧ ContinuousAt E t ∧ ContinuousAt Q t := by
    intro t ht htR
    have hSR : ((1 + ε) * t + R) / 2 < R := by linarith
    have htS : (1 + ε) * t < ((1 + ε) * t + R) / 2 := by linarith
    obtain ⟨h1, hinner, hwS⟩ := Submission.allard52_am_fc_ball_integrable n ℓ μ H w y R
      (((1 + ε) * t + R) / 2) hSR hμR hHR hw hw01
    have hd1 : HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * 1 ∂μ)
        (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * 1 ∂μ) / t) t :=
      (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y (fun _ => (1 : ℝ)) φ
        (((1 + ε) * t + R) / 2) (1 + ε) t h1 hφ h1ε hφ0 ht htS).2.2
    simp only [mul_one] at hd1
    refine ⟨?_, ?_, ?_⟩
    · rw [show I = fun s => ∫ x, φ (‖x - y‖ / s) ∂μ from funext hI]
      exact hd1
    · rw [show E = fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ from funext hE]
      exact (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y
        (fun x => inner ℝ (x - y) (H x)) φ (((1 + ε) * t + R) / 2) (1 + ε) t hinner hφ h1ε hφ0
        ht htS).1
    · exact (Submission.allard52_am_cutoff_integral_calculus n ℓ μ y w φ
        (((1 + ε) * t + R) / 2) (1 + ε) t hwS hφ h1ε hφ0 ht htS).2.1.neg.div continuousAt_id
        ht.ne'
  -- Step 8: the bound on `a` and its continuity, which is (1).
  have hbound : ∀ t : ℝ, 0 < t → (1 + ε) * t < R → ContinuousAt a t ∧
      |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) := by
    intro t ht htR
    have hI0 : 0 ≤ I t := by
      rw [hI t]
      exact (hsplit t ht htR).2.1
    have hpos : 0 < 1 + I t / t ^ n := by
      have : 0 ≤ I t / t ^ n := div_nonneg hI0 (pow_nonneg ht.le n)
      linarith
    refine ⟨?_, ?_⟩
    · rw [show a = fun t => E t / t ^ (n + 1) / (1 + I t / t ^ n) from funext ha]
      exact ((hcalc t ht htR).2.1.div (continuous_pow (n + 1)).continuousAt
        (pow_ne_zero _ ht.ne')).div (continuousAt_const.add
          ((hcalc t ht htR).1.continuousAt.div (continuous_pow n).continuousAt
            (pow_ne_zero _ ht.ne'))) hpos.ne'
    -- Steps 2 and 7: Hölder at radius `(1 + ε) t ≤ R` with `ψ(x) = φ(r_x/t)`.
    · have ht1 : (1 + ε) * t ≤ R := htR.le
      have hBR : closedBall y ((1 + ε) * t) ⊆ closedBall y R := closedBall_subset_closedBall ht1
      obtain ⟨hHfin, hNb⟩ :=
        Submission.allard52_am_fc_lp_scale n ℓ p hnp μ H y R Λ ((1 + ε) * t) hR hΛ ht1 hLp
      have hhol : |E t| ≤ (1 + ε) * t *
          (∫⁻ x in closedBall y ((1 + ε) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) *
            I t ^ (1 - 1 / p) := by
        rw [hE t, hI t]
        refine Submission.aal_curvature_pairing_holder_bound n ℓ p hp1 μ H
          (fun x => φ (‖x - y‖ / t)) y ((1 + ε) * t) (mul_nonneg h1ε.le ht.le)
          ((measure_mono hBR).trans_lt hμR) (hHR.mono_set hBR) hHfin
          (hφ.continuous.comp ((continuous_id.sub continuous_const).norm.div_const t)
            ).aestronglyMeasurable (fun x => hφ01 _) (fun x hx => hφ0 _ ?_)
        exact (le_div_iff₀ ht).2 hx.le
      rw [ha t]
      exact Submission.allard52_am_fc_a_bound n hn p R Λ ε t (I t) (E t) _ hnp hR hΛ hε hε1 ht
        hI0 (Real.rpow_nonneg ENNReal.toReal_nonneg _) hNb hhol
  refine ⟨hbound, ?_⟩
  intro s r hs hsr hrR
  -- Step 9: the integrating factor on `(0, R/(1 + ε))`, with `β = n/p` and
  -- `M = 2κΛR⁻¹/R^{−n/p}`, so that `M t^{−β} = 2κΛR⁻¹ (t/R)^{−n/p}`.
  have hmem : ∀ t, t ∈ Ioo 0 (R / (1 + ε)) → 0 < t ∧ (1 + ε) * t < R := fun t ht =>
    ⟨ht.1, by rw [mul_comm]; exact (lt_div_iff₀ h1ε).1 ht.2⟩
  have hab : ∀ t ∈ Ioo 0 (R / (1 + ε)),
      |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R / R ^ (-((n : ℝ) / p)) * t ^ (-((n : ℝ) / p)) := by
    intro t ht
    obtain ⟨ht0, htR⟩ := hmem t ht
    calc |a t| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p)) :=
          (hbound t ht0 htR).2
      _ = _ := by
          rw [Real.div_rpow ht0.le hR.le]
          ring
  have hIF := Submission.allard52_am_integrating_factor n I I' E Q a (R / (1 + ε))
    (2 * ((p - n) / (4 * p)) * Λ / R / R ^ (-((n : ℝ) / p))) ((n : ℝ) / p)
    ((div_lt_one hp).2 hnp)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).1)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).2.1)
    (fun t ht => (hcalc t (hmem t ht).1 (hmem t ht).2).2.2)
    (fun t ht => by rw [hI t]; exact (hsplit t (hmem t ht).1 (hmem t ht).2).2.1)
    (fun t ht => by
      obtain ⟨ht0, htR⟩ := hmem t ht
      have h := hrad t ht0 htR
      rw [(hsplit t ht0 htR).1] at h
      rw [hI t, hE t, ← h, hI', hQ]
      field_simp
      ring)
    ha hab s r hs hsr (by rw [lt_div_iff₀ h1ε, mul_comm]; exact hrR)
  -- On `[s, r]`: `0 < t`, `(1 + ε) t < R`, and `Q(t)/tⁿ ≥ 0` (step 6).
  have hIcc : ∀ t ∈ Icc s r, 0 < t ∧ (1 + ε) * t < R := fun t ht =>
    ⟨hs.trans_le ht.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 h1ε.le) hrR⟩
  have hQnn : ∀ t ∈ Icc s r, 0 ≤ Q t / t ^ n := fun t ht => by
    obtain ⟨ht0, htR⟩ := hIcc t ht
    exact div_nonneg (div_nonneg (neg_nonneg.2 (hsplit t ht0 htR).2.2) ht0.le)
      (pow_nonneg ht0.le n)
  refine ⟨?_, ?_⟩
  -- Step 11: monotonicity, as the integrand `exp(−G) Q/tⁿ` is `≥ 0` on `[s, r]`.
  · rw [← sub_nonneg, hIF]
    exact intervalIntegral.integral_nonneg hsr fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hQnn t ht)
  -- Step 12: `|G| ≤ Λ/2` (step 10) gives `Q/tⁿ ≤ e^{Λ/2} e^{−G} Q/tⁿ` on `[s, r]`; integrate and
  -- apply the annular Tonelli bound.
  · have hG := Submission.allard52_am_fc_primitive n p R Λ ε a hnp hR hΛ hε hbound
    have hcQ : ContinuousOn (fun t => Q t / t ^ n) (uIcc s r) := by
      rw [uIcc_of_le hsr]
      intro t ht
      obtain ⟨ht0, htR⟩ := hIcc t ht
      exact ((hcalc t ht0 htR).2.2.div (continuous_pow n).continuousAt
        (pow_ne_zero n ht0.ne')).continuousWithinAt
    have hcGQ : ContinuousOn (fun t => Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n))
        (uIcc s r) := by
      rw [uIcc_of_le hsr]
      intro t ht
      obtain ⟨ht0, htR⟩ := hIcc t ht
      exact ((hG t ht0 htR).1.neg.rexp.mul ((hcalc t ht0 htR).2.2.div
        (continuous_pow n).continuousAt (pow_ne_zero n ht0.ne'))).continuousWithinAt
    have hmono : ∫ t in s..r, Q t / t ^ n ≤
        ∫ t in s..r, Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) := by
      refine intervalIntegral.integral_mono_on hsr hcQ.intervalIntegrable
        (hcGQ.intervalIntegrable.const_mul _) fun t ht => ?_
      obtain ⟨ht0, htR⟩ := hIcc t ht
      have h1 : 1 ≤ Real.exp (Λ / 2) * Real.exp (-∫ τ in (0)..t, a τ) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [le_abs_self (∫ τ in (0)..t, a τ), (hG t ht0 htR).2])
      calc Q t / t ^ n = 1 * (Q t / t ^ n) := (one_mul _).symm
        _ ≤ Real.exp (Λ / 2) * Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n) :=
          mul_le_mul_of_nonneg_right h1 (hQnn t ht)
        _ = Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)) := mul_assoc _ _ _
    rw [intervalIntegral.integral_const_mul, ← hIF] at hmono
    exact (Submission.allard52_am_annular_tonelli n ℓ μ w y φ R ε s r hε hμR hw hw01 hφ hanti hφ1
      hφ0 hs hsr hrR).trans (ENNReal.ofReal_le_ofReal hmono)

/-- **Simon Ch. 4, 4.5–4.8** (steps 1 and 5–9 of the annular monotonicity argument: the passage
`ε → 0` in the radial cutoff).  Let `n ≥ 1`, `p > n`, `R > 0`, `0 < Λ ≤ 1`, `κ = (p − n)/(4p)`;
let `μ(B_R(y)) < ∞`, `H` be `μ`-integrable on `B_R(y)` with `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ κΛ`,
`0 ≤ w ≤ 1` `μ`-a.e. in `B̆_R(y)`, and assume the radial first-variation identity for all `C¹`
cutoffs.  Then some `F` (here `F = exp(−G)`, `G(t) = ∫₀ᵗ a₀`,
`a₀(t) = t^{−n−1} ∫_{B_t(y)} (x − y)·H dμ / (1 + t^{−n} μ(B_t(y)))`) satisfies, with
`Φ(r) = F(r) r^{−n} μ(B_r(y)) + F(r) − 1`:
(i) `e^{−Λ} ≤ F ≤ e^{Λ}` and `|F(r) − 1| ≤ Λ (r/R)^{1−n/p}` on `(0, R)`;
(ii) `Φ` is nondecreasing on `(0, R)`, and
`∫_{B_r(y) \ B_s(y)} w/|x − y|ⁿ dμ ≤ e^{Λ} (Φ(r) − Φ(s))` for `0 < s ≤ r < R`.
Proof: `allard52_am_fixed_cutoff` for the cutoffs `φ k` of `allard52_amcl_cutoff_sequence`
gives the bound `|a_k| ≤ 2κΛR⁻¹(τ/R)^{−n/p}`, the monotonicity of
`Φ̃_k = exp(−∫₀ a_k)(1 + I_k/tⁿ)` and the per-`k` annular estimate; dominated convergence
(`allard52_amcl_radial_cutoff_tendsto`) gives `I_k(t) → μ(B_t(y))`, `E_k(t) → E₀(t)`, hence
`a_k(t) → a₀(t)`; `allard52_amcl_interval_limit` gives `∫₀ᵗ a_k → G(t)` and
`|G(t)| ≤ (Λ/2)(t/R)^{1−n/p}`, whence (i) by `|eᶻ − 1| ≤ 2|z|`; the monotonicity passes to the
limit, and Fatou's lemma (`allard52_amcl_annular_lintegral_le`) gives the annular bound with
`e^{Λ/2} ≤ e^{Λ}`. -/
theorem allard52_am_cutoff_limit : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - w x)) ∂μ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (w x / ‖x - y‖ ^ n) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1)))) := by
  intro n ℓ hn p hp μ H w y R Λ hR hΛ hΛ1 hμR hH hHp hw hw01 hrad
  -- Steps 1–2: `C¹` nonincreasing cutoffs, `1` on `(-∞, 1]` and `0` on `[1 + ε k, ∞)`, `ε k → 0`.
  obtain ⟨φ, ε, hε, hεt, hφC, hφA, hφ01, hφ1, hφ0⟩ := Submission.allard52_amcl_cutoff_sequence
  -- The cutoff quantities `I_k, E_k, a_k` and their limits `m, E₀, a₀, G` and `F = exp(−G)`.
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ → ℝ, ∀ k t,
      E k t = ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t = E k t / t ^ (n + 1) / (1 + I k t / t ^ n) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = (μ (closedBall y t)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ → ℝ, ∀ t,
      E₀ t = ∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ := ⟨_, fun _ => rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t = E₀ t / t ^ (n + 1) / (1 + m t / t ^ n) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ∫ τ in (0)..t, a₀ τ := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t, F t = Real.exp (-G t) := ⟨_, fun _ => rfl⟩
  -- Step 3: `fixed_cutoff` for every `k`, the radial identity being the hypothesis at `T = 1 + ε k`.
  have hfix := fun k => Submission.allard52_am_fixed_cutoff n ℓ hn p hp μ H w y R Λ (ε k) (φ k)
    (I k) (E k) (a k) hR hΛ (hε k).1 (hε k).2 hμR hH hHp hw hw01 (hφC k) (hφA k) (hφ1 k)
    (hφ0 k) (fun ρ hρ hρR => hrad (φ k) (1 + ε k) ρ (hφC k) (hφ1 k) (hφ0 k) hρ hρR) (hI k)
    (hE k) (ha k)
  -- `(1 + ε k) t < R` for all large `k`, whenever `t < R`.
  have hev : ∀ t, t < R → ∀ᶠ k in atTop, (1 + ε k) * t < R := by
    intro t ht
    have h : Tendsto (fun k => (1 + ε k) * t) atTop (𝓝 ((1 + 0) * t)) :=
      (hεt.const_add 1).mul_const t
    rw [add_zero, one_mul] at h
    exact h.eventually (eventually_lt_nhds ht)
  -- Step 5: dominated convergence at a fixed radius `t ∈ (0, R)`.
  have hint1 : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y R) μ := integrableOn_const hμR.ne
  have hintH : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y R) μ := by
    refine Integrable.mono' ((Integrable.norm hH).const_mul R)
      ((continuous_inner (𝕜 := ℝ)).comp_aestronglyMeasurable
        ((continuous_sub_right y).aestronglyMeasurable.prodMk
          (Integrable.aestronglyMeasurable hH))) ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hxR : ‖x - y‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
  have hIlim : ∀ t, 0 < t → t < R → Tendsto (fun k => I k t) atTop (𝓝 (m t)) := by
    intro t ht htR
    have h := Submission.allard52_amcl_radial_cutoff_tendsto n ℓ μ (fun _ => 1) y φ ε R t ht htR
      hint1 (fun k => (hφC k).continuous) hφ01 hφ1 hφ0 hεt
    simp only [mul_one, setIntegral_const, smul_eq_mul, measureReal_def] at h
    simpa only [hI, hm] using h
  have hElim : ∀ t, 0 < t → t < R → Tendsto (fun k => E k t) atTop (𝓝 (E₀ t)) := by
    intro t ht htR
    simpa only [hE, hE₀] using Submission.allard52_amcl_radial_cutoff_tendsto n ℓ μ
      (fun x => inner ℝ (x - y) (H x)) y φ ε R t ht htR hintH (fun k => (hφC k).continuous)
      hφ01 hφ1 hφ0 hεt
  have halim : ∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
    intro t ht htR
    have hm0 : 0 ≤ m t / t ^ n := div_nonneg (by rw [hm]; exact ENNReal.toReal_nonneg)
      (pow_nonneg ht.le n)
    rw [show (fun k => a k t) = fun k => E k t / t ^ (n + 1) / (1 + I k t / t ^ n) from
      funext fun k => ha k t, ha₀]
    exact ((hElim t ht htR).div_const (t ^ (n + 1))).div
      (((hIlim t ht htR).div_const (t ^ n)).const_add 1) (by linarith)
  -- Step 6: `∫₀ᵗ a_k → G(t)`, with `|G(t)| ≤ (Λ/2)(t/R)^{1−n/p}`, and `Φ̃_k(t) → F(t)(1 + m(t)/tⁿ)`.
  have hGlim : ∀ t, 0 < t → t < R → Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (G t)) ∧
      |G t| ≤ Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p) := by
    intro t ht htR
    rw [hG]
    refine Submission.allard52_amcl_interval_limit n p R Λ t a a₀ hp hR hΛ ht ?_
      (fun τ hτ hτt => halim τ hτ (lt_of_le_of_lt hτt htR))
    filter_upwards [hev t htR] with k hk
    intro τ hτ hτt
    exact (hfix k).1 τ hτ
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hτt (by linarith [(hε k).1])) hk)
  have hΦlim : ∀ t, 0 < t → t < R → Tendsto (fun k => Real.exp (-∫ τ in (0)..t, a k τ) *
      (1 + I k t / t ^ n)) atTop (𝓝 (F t * (1 + m t / t ^ n))) := by
    intro t ht htR
    rw [hF]
    exact (hGlim t ht htR).1.neg.rexp.mul (((hIlim t ht htR).div_const _).const_add 1)
  refine ⟨F, ?_, ?_⟩
  -- Step 7: conclusion (i).
  · rintro r ⟨hr0, hrR⟩
    have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
    have hrR1 : 0 ≤ r / R ∧ r / R ≤ 1 := ⟨div_nonneg hr0.le hR.le, (div_le_one hR).2 hrR.le⟩
    have hpow1 : (r / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one hrR1.1 hrR1.2 (sub_nonneg.2 ((div_le_one hp0).2 hp.le))
    have hGr := (hGlim r hr0 hrR).2
    have hGr' : |G r| ≤ Λ / 2 :=
      hGr.trans ((mul_le_mul_of_nonneg_left hpow1 (by linarith)).trans (mul_one _).le)
    obtain ⟨hGl, hGu⟩ := abs_le.1 hGr'
    rw [hF]
    refine ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith), ?_⟩
    calc |Real.exp (-G r) - 1| ≤ 2 * |-G r| :=
          Real.abs_exp_sub_one_le (by rw [abs_neg]; linarith)
      _ = 2 * |G r| := by rw [abs_neg]
      _ ≤ 2 * (Λ / 2 * (r / R) ^ (1 - (n : ℝ) / p)) := by linarith
      _ = Λ * (r / R) ^ (1 - (n : ℝ) / p) := by ring
  -- Steps 8–9: conclusion (ii).
  · intro s r hs hsr hrR
    have hsR : s < R := lt_of_le_of_lt hsr hrR
    have hr0 : 0 < r := lt_of_lt_of_le hs hsr
    -- Monotonicity of `Φ̃_k` passes to the limit.
    have hmono : F s * (1 + m s / s ^ n) ≤ F r * (1 + m r / r ^ n) :=
      le_of_tendsto_of_tendsto (hΦlim s hs hsR) (hΦlim r hr0 hrR) (by
        filter_upwards [hev r hrR] with k hk
        exact ((hfix k).2 s r hs hsr hk).1)
    have hD : (F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) -
        (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1) =
        F r * (1 + m r / r ^ n) - F s * (1 + m s / s ^ n) := by
      rw [hm, hm]; ring
    refine ⟨by linarith, ?_⟩
    -- Fatou's lemma along the annuli `B_r(y) \ B̆_{(1 + ε k) s}(y)`.
    have hann := Submission.allard52_amcl_annular_lintegral_le n ℓ μ
      (fun x => ENNReal.ofReal (w x / ‖x - y‖ ^ n)) y ε
      (fun k => Real.exp (Λ / 2) * (Real.exp (-∫ τ in (0)..r, a k τ) * (1 + I k r / r ^ n) -
        Real.exp (-∫ τ in (0)..s, a k τ) * (1 + I k s / s ^ n))) s r
      (Real.exp (Λ / 2) * (F r * (1 + m r / r ^ n) - F s * (1 + m s / s ^ n))) hs hεt
      (((hΦlim r hr0 hrR).sub (hΦlim s hs hsR)).const_mul _) (by
        filter_upwards [hev r hrR] with k hk
        exact ((hfix k).2 s r hs hsr hk).2)
    rw [hD]
    exact hann.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (by linarith)) (sub_nonneg.2 hmono)))

/-- **Simon Ch. 4, 4.1–4.9 with the conical term (annular monotonicity; Ch. 5, 2.4).**  Let
`1 ≤ n < p`, let `V` have generalized mean curvature `H` in the open set `U`, let `R > 0` with
`B_R(y) ⊆ U`, and assume that `μ_V`-a.e. on `B̆_R(y)` the tangent projection `p_x` is the orthogonal
projection onto an `n`-plane, that `x ↦ p_x` is a.e. strongly measurable on `B̆_R(y)`, `0 < Λ ≤ 1`
and `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ_V)^{1/p} ≤ κΛ` with `κ = (p − n)/(4p)`.  Then there is `F` with
`e^{−Λ} ≤ F ≤ e^Λ` and `|F(r) − 1| ≤ Λ (r/R)^{1−n/p}` on `(0, R)` such that
`Φ(r) = F(r) r⁻ⁿ μ_V(B_r(y)) + F(r) − 1` is nondecreasing on `(0, R)`,
`∫_{B_r(y) \ B_s(y)} |x − y − p_x(x − y)|² / |x − y|^{n+2} dμ_V ≤ e^Λ (Φ(r) − Φ(s))`, and the
density `Θⁿ(μ_V, y) = t` exists with `ω_n t ≤ Φ(r)` for every `r ∈ (0, R)`.
Proof: `μ_V(B_R(y)) < ∞` and `H ∈ L¹(μ_V⌞B_R(y))` because `B_R(y) ⊆ U` is compact.  The conical
weight `ν(x) = |x − y − p_x(x − y)|² / |x − y|²` is a.e. strongly measurable on `B̆_R(y)`, and
`0 ≤ ν ≤ 1` there since `v − p_P v = p_{P^⊥} v`.  The radial first-variation identity
`allard52_am_radial_identity` is then the hypothesis of the cutoff limit
`allard52_am_cutoff_limit` for `μ = μ_V` and `w = ν`, which gives (i) and (ii) because
`ν(x) |x − y|⁻ⁿ = |x − y − p_x(x − y)|² / |x − y|^{n+2}`; `allard52_am_center_density` with
`α = 1 − n/p > 0` gives (iii). -/
theorem allard52_annular_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1)))) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * t ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1 := by
  intro n ℓ hn p hp U _hU V H hH y R Λ hR hBR hrank hmeas hΛ hΛ1 hsmall
  -- Step 0(a): `μ_V(B_R(y)) < ∞`, since `B_R(y)` is a compact subset of `U` and `θ` is integrable
  -- on `M ∩ B_R(y)`.
  have hfin : V.weight (closedBall y R) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y R) hBR).setLIntegral_lt_top
  -- Step 0(b): `H` is `μ_V`-integrable on the compact set `B_R(y) ⊆ U`.
  have hHint : IntegrableOn H (closedBall y R) V.weight :=
    hH.1.integrableOn_compact_subset hBR (isCompact_closedBall y R)
  -- The conical weight `ν(x) = |x − y − p_x(x − y)|² / |x − y|²` (with `ν(y) = 0`).
  set w : Amb n ℓ → ℝ := fun x => ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 with hw
  -- Step 0(e): `ν` is a.e. strongly measurable on `B̆_R(y)`, because `x ↦ p_x` is.
  have hwm : AEStronglyMeasurable w (V.weight.restrict (ball y R)) := by
    have hd : AEStronglyMeasurable (fun x : Amb n ℓ => x - y) (V.weight.restrict (ball y R)) :=
      (continuous_sub_right y).aestronglyMeasurable
    have hpx : AEStronglyMeasurable (fun x => V.tangentProj x (x - y))
        (V.weight.restrict (ball y R)) :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => A v)
        isBoundedBilinearMap_apply.continuous hmeas hd
    exact ((hd.sub hpx).norm.pow 2).div₀ (hd.norm.pow 2)
  -- Step 0(d): `0 ≤ ν ≤ 1` a.e. on `B̆_R(y)`: where `p_x = p_P`, `v − p_P v = p_{P^⊥} v` has
  -- `|p_{P^⊥} v| ≤ |v|`.
  have hw01 : ∀ᵐ x ∂V.weight, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1 := by
    filter_upwards [hrank] with x hx hxB
    obtain ⟨P, -, hP⟩ := hx hxB
    have hle : ‖(x - y) - V.tangentProj x (x - y)‖ ≤ ‖x - y‖ := by
      rw [hP, ← Submodule.starProjection_orthogonal_val]
      exact Pᗮ.norm_starProjection_apply_le _
    refine ⟨by positivity, div_le_one_of_le₀ ?_ (by positivity)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- Steps 1–8: the cutoff limit, fed with the radial first-variation identity of step 2.
  obtain ⟨F, hF, hΦ⟩ := Submission.allard52_am_cutoff_limit n ℓ hn p hp V.weight H w y R Λ hR hΛ
    hΛ1 hfin hHint hsmall hwm hw01
    (Submission.allard52_am_radial_identity n ℓ U V H hH y R hBR hrank)
  -- Step 9: the density at the centre, with the decay exponent `α = 1 − n/p > 0`.
  have hα : 0 < 1 - (n : ℝ) / p := by
    have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
    rw [sub_pos, div_lt_one hp0]
    exact hp
  obtain ⟨t, ht0, hdens, htΦ⟩ := Submission.allard52_am_center_density n ℓ V.weight y F R Λ
    (1 - (n : ℝ) / p) hR hα hfin hF fun s r hs hsr hr => (hΦ s r hs hsr hr).1
  refine ⟨F, hF, fun s r hs hsr hr => ⟨(hΦ s r hs hsr hr).1, ?_⟩, t, ht0, hdens, htΦ⟩
  -- Step 8: the integrands agree, `ν(x) |x − y|⁻ⁿ = |x − y − p_x(x − y)|² / |x − y|^{n+2}`
  -- (both sides vanish at `x = y`).
  have hg : ∀ x, ‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) =
      w x / ‖x - y‖ ^ n := fun x => by
    rw [hw, div_div, ← pow_add, add_comm 2 n]
  simp_rw [hg]
  exact (hΦ s r hs hsr hr).2

end Submission

end GMT.Ch05
