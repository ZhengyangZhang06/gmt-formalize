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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
