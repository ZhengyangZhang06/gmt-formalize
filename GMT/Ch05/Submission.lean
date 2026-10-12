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
/-- **Simon Ch. 4, 3.2–3.3 and 4.1** (first variation of the radial cutoff fields).  Let `V` have
generalized mean curvature `H` in `U`, with `p_{T_x M}` the projection onto an `n`-plane for
`μ_V`-a.e. `x`.  Let `φ ∈ C¹(ℝ)` with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[T, ∞)`, let `ρ > 0`, and
let `B_{Tρ}(y) ⊆ U`.  Then `X(x) = φ(r/ρ)(x − y)`, `r = |x − y|`, is admissible in 3.14, and
`div_M X = n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − |(x − y) − p_{T_x M}(x − y)|²/r²)` `μ_V`-a.e.
(both sides equal `n` at `x = y`).  So `∫ div_M X dμ_V = −∫ X · H dμ_V` is the stated identity. -/
theorem aal_radial_first_variation_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (y : Amb n ℓ) (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → closedBall y (T * ρ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH hP y φ T ρ hφ hφ1 hφT hρ hU
  -- Step 1: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
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
  -- Step 2: `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
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
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  -- Step 3: `X · H = φ(r/ρ)(x - y) · H`.
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
    -- `D|· - y|(x) = r⁻¹ (x - y) · ⬝`, from `|z - y| = √(|z - y|²)`.
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
  -- Step 5: `trace p_P = dim P` and `trace ((a id + c (u · ⬝) u) ∘ p_P) = a dim P + c u · p_P u`.
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
  -- Step 6: `div_M X` equals the integrand at every `x` where `p_{T_x M}` projects onto an
  -- `n`-plane `P`.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    obtain ⟨P, hPn, hPx⟩ := hx
    rw [RectifiableVarifold.divM, hPx]
    by_cases hxy : x = y
    · -- At the center `DX(y) = id`, so `div_M X(y) = n = n φ(0)`.
      have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
        rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
        exact (hasFDerivAt_sub_const y).fderiv
      rw [hfd]
      simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
      subst hxy
      simp [hφ1 0 zero_le_one]
    · -- Away from it, `(x - y) · p_P (x - y) = |p_P (x - y)|²` and Pythagoras.
      rw [(hXderiv x hxy).fderiv, htr, hPn]
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
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
/-- Simon Ch. 5, 2.4, step (5.1) of the lower density bound, abstracted: put
`Φ(u) = F(u) (m(u)/uⁿ) + (F(u) − 1)`.  If `|F(u) − 1| ≤ Λ (u/R)^α` on `(0, R]` with `α > 0`, `Φ` is
nondecreasing on `(0, R]`, and for every `ε > 0` eventually `(1 − ε) ω uⁿ ≤ m(u)` as `u ↓ 0`, then
`ω ≤ Φ(t)` for every `t ∈ (0, R]` (let `u ↓ 0` in `Φ(u) ≤ Φ(t)`, using `F(u) → 1`). -/
theorem aal_monotone_quantity_ge_density : ∀ (n : ℕ) (α ω R Λ : ℝ) (m F : ℝ → ℝ), 0 < α → 0 < ω → 0 < R → (∀ u : ℝ, 0 < u → u ≤ R → |F u - 1| ≤ Λ * (u / R) ^ α) → (∀ u t : ℝ, 0 < u → u ≤ t → t ≤ R → F u * (m u / u ^ n) + (F u - 1) ≤ F t * (m t / t ^ n) + (F t - 1)) → (∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[>] (0 : ℝ), (1 - ε) * (ω * u ^ n) ≤ m u) → ∀ t : ℝ, 0 < t → t ≤ R → ω ≤ F t * (m t / t ^ n) + (F t - 1) := by
  intro n α ω R Λ m F hα hω hR hF hmono hlow t ht htR
  -- `Λ (u/R)^α → 0` as `u → 0+`, since `x ↦ x^α` is continuous at `0` with `0^α = 0` (`α > 0`).
  have hlim : Tendsto (fun u : ℝ => Λ * (u / R) ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ => Λ * (u / R) ^ α) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const R).rpow_const (Or.inr hα.le))
    have h := hc.tendsto
    simp only [zero_div, Real.zero_rpow hα.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Suppose `Φ(t) < ω` and pick `η ∈ (0, 1/2]` with `η (2ω + 1) ≤ (ω − Φ(t))/2`.
  refine not_lt.mp fun hcon => ?_
  obtain ⟨η, hη0, hη2, hηd⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
      η * (2 * (2 * ω + 1)) ≤ ω - (F t * (m t / t ^ n) + (F t - 1)) := by
    refine ⟨min (1 / 2) ((ω - (F t * (m t / t ^ n) + (F t - 1))) / (2 * (2 * ω + 1))),
      lt_min (by norm_num) (div_pos (sub_pos.mpr hcon) (by positivity)), min_le_left _ _, ?_⟩
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_right _ _
  -- A small radius `u ∈ (0, t)` with `Λ (u/R)^α < η` and `(1 − η) ω uⁿ ≤ m(u)`.
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  obtain ⟨u, ⟨hu0, hut⟩, huΛ, hum⟩ :=
    (hsmall.and ((hlim.eventually (gt_mem_nhds hη0)).and (hlow η hη0))).exists
  -- `|F(u) − 1| < η`, so `F(u) > 1 − η ≥ 1/2`.
  have hFu : 1 - η < F u := by
    have h := (abs_lt.mp ((hF u hu0 (hut.le.trans htR)).trans_lt huΛ)).1
    linarith
  -- `m(u)/uⁿ ≥ (1 − η) ω ≥ 0`, hence `F(u) (m(u)/uⁿ) ≥ (1 − η)² ω`.
  have hmu : (1 - η) * ω ≤ m u / u ^ n := by
    rw [le_div_iff₀ (pow_pos hu0 n)]
    linarith
  have hprod : (1 - η) * ((1 - η) * ω) ≤ F u * (m u / u ^ n) :=
    mul_le_mul hFu.le hmu (mul_nonneg (by linarith) hω.le) (by linarith)
  -- `Φ(u) ≥ (1 − η)² ω − η ≥ ω − η (2ω + 1) > Φ(t)`, contradicting `Φ(u) ≤ Φ(t)`.
  have hmon := hmono u t hu0 hut.le htR
  linarith [mul_nonneg (sq_nonneg η) hω.le]

/-- **Simon Ch. 4, 3.1–3.6 and 4.1–4.10** (the `Lᵖ` monotonicity formula under 2.3), as used
in the Lipschitz approximation lemma 2.6.  Let `p > n ≥ 1`, 2.3 hold, `4pδ/(p − n) ≤ Λ ≤ 1`,
`B_R(y) ⊆ B_ρ(0)` and `0 < s ≤ r < R`.  Then, with `μ = μ_V` and closed balls,
`s⁻ⁿ μ(B_s(y)) ≤ e^{2Λ} r⁻ⁿ μ(B_r(y)) + 2e^Λ Λ`,
`r⁻ⁿ μ(B_r(y)) ≤ e^{2Λ} s⁻ⁿ μ(B_s(y)) + 2e^Λ Λ
  + e^{2Λ} ∫_{B_r(y) \ B_s(y)} |(x − y) − p_x(x − y)|² |x − y|^{−n−2} dμ`,
and `e^{−Λ}(ω_n − Λ) ≤ s⁻ⁿ μ(B_s(y))` if `y ∈ spt V`.  For a cutoff `φ` and the cutoff mass
`I(t) = ∫ φ(|x − z|/t) dμ`, the radial first variation gives `(t⁻ⁿ I)' = N + e` with `N ≥ 0`,
and Hölder with `κ = (p − n)/(4p)` gives `|e| ≤ λ'(1 + t⁻ⁿ I)`, `λ(t) = (Λ_z/2)(t/R_z)^{1−n/p}`.
Hence `e^{λ}(1 + t⁻ⁿ I)` is nondecreasing and `e^{−λ}(1 + t⁻ⁿ I) − (1 + ε)ⁿ ∫ w φ(|x − z|/t) dμ`
(`w` the annular weight) is nonincreasing; letting the cutoff tend to `1_{(−∞, 1]}` gives the
first two estimates.  The third follows from density points (`θ ≥ 1`) near `y` and
`aal_monotone_quantity_ge_density`. -/
theorem lip_approx_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ Λ : ℝ), 0 < δ → V.AllardHypotheses H p δ ρ → 4 * p * δ / (p - n) ≤ Λ → Λ ≤ 1 → ∀ (y : Amb n ℓ) (R : ℝ), 0 < R → closedBall y R ⊆ closedBall 0 ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → V.weight.real (closedBall y s) / s ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y r) / r ^ n) + 2 * Real.exp Λ * Λ ∧ V.weight.real (closedBall y r) / r ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y s) / s ^ n) + 2 * Real.exp Λ * Λ + Real.exp (2 * Λ) * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight ∧ (y ∈ V.support → Real.exp (-Λ) * (unitBallVolume n - Λ) ≤ V.weight.real (closedBall y s) / s ^ n) := by
  -- Step 1: a `C¹` cutoff profile, `φ = 1` on `(-∞, 1]`, `φ = 0` on `[1 + ε, ∞)`, `φ' ≤ 0`.
  have hcut : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ u, u ≤ 1 → φ u = 1) ∧
      (∀ u, 1 + ε ≤ u → φ u = 0) ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, deriv φ u ≤ 0) ∧
      (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < 1 + ε) ∧ ∃ C, 0 ≤ C ∧ ∀ u, |deriv φ u| ≤ C := by
    intro ε hε
    set φ : ℝ → ℝ := fun u => Real.smoothTransition ((1 + ε - u) / ε) with hφdef
    have hcd : ContDiff ℝ 1 φ :=
      Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε)
    have h1 : ∀ u, u ≤ 1 → φ u = 1 := by
      intro u hu
      exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)
    have h0 : ∀ u, 1 + ε ≤ u → φ u = 0 := by
      intro u hu
      exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith only [hu]) hε.le)
    have hrange : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1 := fun u =>
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hanti : Antitone φ := by
      intro a b hab
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hε.le)
    have hdz : ∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < 1 + ε := by
      intro u hu
      by_contra hcon
      rw [not_and_or, not_lt, not_lt] at hcon
      apply hu
      rcases hcon with hle | hge
      · -- `φ ≤ 1 = φ u`: a maximum.
        refine IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall fun v => ?_)
        rw [h1 u hle]; exact (hrange v).2
      · refine IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun v => ?_)
        rw [h0 u hge]; exact (hrange v).1
    have hbd : ∃ C, 0 ≤ C ∧ ∀ u, |deriv φ u| ≤ C := by
      have hcont : Continuous (deriv φ) := hcd.continuous_deriv le_rfl
      have hsupp : HasCompactSupport (deriv φ) :=
        HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 1 + ε)) fun u hu => by
          by_contra hne
          exact hu ⟨(hdz u hne).1.le, (hdz u hne).2.le⟩
      obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
      exact ⟨max C 0, le_max_right _ _, fun u => (hC u).trans (le_max_left _ _)⟩
    exact ⟨φ, hcd, h1, h0, hrange, fun u => hanti.deriv_nonpos, hdz, hbd⟩
  -- Step 2: differentiation under the integral sign, `d/dt ∫ w(x) φ(|x - z|/t) dμ`.
  have hderiv : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (z : Amb n ℓ) (φ : ℝ → ℝ) (ε Rz W C : ℝ)
      (hε : 0 < ε) (hφ : ContDiff ℝ 1 φ) (hφ0 : ∀ u, 1 + ε ≤ u → φ u = 0)
      (hφr : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1) (hdz : ∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < 1 + ε)
      (hC : ∀ u, |deriv φ u| ≤ C) (hfin : μ (closedBall z Rz) < ⊤) (w : Amb n ℓ → ℝ)
      (hw : AEStronglyMeasurable w μ) (hW : ∀ x, |w x| ≤ W) (t₀ : ℝ) (ht₀ : 0 < t₀)
      (htR : (1 + ε) * t₀ < Rz),
      HasDerivAt (fun t => ∫ x, w x * φ (‖x - z‖ / t) ∂μ)
        (∫ x, w x * (deriv φ (‖x - z‖ / t₀) * (-(‖x - z‖ / t₀ ^ 2))) ∂μ) t₀  := by
    clear hcut
    intro n ℓ μ z φ ε Rz W C hε hφ hφ0 hφr hdz hC hfin w hw hW t₀ ht₀ htR
    have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW z)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    set η : ℝ := min (t₀ / 2) (Rz / (1 + ε) - t₀) with hη
    have hε1 : 0 < 1 + ε := add_pos one_pos hε
    have hηpos : 0 < η := lt_min (by linarith) (by rw [sub_pos, lt_div_iff₀ hε1]; linarith)
    have hball : ∀ t ∈ ball t₀ η, t₀ / 2 < t ∧ (1 + ε) * t < Rz := by
      intro t ht
      rw [mem_ball, Real.dist_eq, abs_lt] at ht
      have h1 : η ≤ t₀ / 2 := min_le_left _ _
      have h2 : η ≤ Rz / (1 + ε) - t₀ := min_le_right _ _
      refine ⟨by linarith only [ht.1, h1], ?_⟩
      have : t < Rz / (1 + ε) := by linarith only [ht.2, h2]
      rw [lt_div_iff₀ hε1] at this; linarith only [this]
    have hfinB : IsFiniteMeasure (μ.restrict (closedBall z Rz)) :=
      isFiniteMeasure_restrict.mpr hfin.ne
    -- the indicator bound is integrable
    have hind : ∀ c : ℝ, Integrable ((closedBall z Rz).indicator fun _ => c) μ := fun c =>
      (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin.ne)
    have hφc : Continuous φ := hφ.continuous
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
    -- pointwise derivative
    have hpt : ∀ x : Amb n ℓ, ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t => w x * φ (‖x - z‖ / t))
        (w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2)))) t := by
      intro x t ht
      have hinv : HasDerivAt (fun t : ℝ => ‖x - z‖ / t) (-(‖x - z‖ / t ^ 2)) t :=
        ((hasDerivAt_const t ‖x - z‖).div (hasDerivAt_id t) ht).congr_deriv
          (show (0 * t - ‖x - z‖ * 1) / t ^ 2 = -(‖x - z‖ / t ^ 2) by ring)
      exact (((hφ.differentiable one_ne_zero) _).hasDerivAt.comp t hinv).const_mul (w x)
    -- zero outside the ball
    have hzero : ∀ x t, 0 < t → (1 + ε) * t < Rz → x ∉ closedBall z Rz → φ (‖x - z‖ / t) = 0 := by
      intro x t ht htR hx
      apply hφ0
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      rw [le_div_iff₀ ht]; exact (htR.trans hx).le
    have hzero' : ∀ x t, 0 < t → (1 + ε) * t < Rz → x ∉ closedBall z Rz →
        deriv φ (‖x - z‖ / t) = 0 := by
      intro x t ht htR hx
      by_contra hne
      have := (hdz _ hne).2
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      rw [div_lt_iff₀ ht] at this; linarith only [this, hx, htR]
    have hmeasF : ∀ t, AEStronglyMeasurable (fun x => w x * φ (‖x - z‖ / t)) μ := fun t =>
      hw.mul (hφc.comp ((continuous_id.sub continuous_const).norm.div_const t)).aestronglyMeasurable
    have hmeasF' : AEStronglyMeasurable
        (fun x => w x * (deriv φ (‖x - z‖ / t₀) * (-(‖x - z‖ / t₀ ^ 2)))) μ :=
      hw.mul ((hdc.comp ((continuous_id.sub continuous_const).norm.div_const t₀)).mul
        ((continuous_id.sub continuous_const).norm.div_const _).neg).aestronglyMeasurable
    have hint : Integrable (fun x => w x * φ (‖x - z‖ / t₀)) μ := by
      refine (hind W).mono' (hmeasF t₀) (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ closedBall z Rz
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        calc |w x| * |φ (‖x - z‖ / t₀)| ≤ W * 1 := by
              apply mul_le_mul (hW x) _ (abs_nonneg _) hW0
              rw [abs_of_nonneg (hφr _).1]; exact (hφr _).2
          _ = W := mul_one W
      · rw [indicator_of_notMem hx, hzero x t₀ ht₀ htR hx, mul_zero, norm_zero]
    have hbound : ∀ᵐ x ∂μ, ∀ t ∈ ball t₀ η,
        ‖w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2)))‖ ≤
          (closedBall z Rz).indicator (fun _ => W * (C * (4 * (1 + ε) / t₀))) x := by
      refine Filter.Eventually.of_forall fun x t ht => ?_
      obtain ⟨ht1, ht2⟩ := hball t ht
      have htpos : 0 < t := by linarith only [ht1, ht₀]
      by_cases hx : x ∈ closedBall z Rz
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_mul]
        apply mul_le_mul (hW x) _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hW0
        by_cases hd : deriv φ (‖x - z‖ / t) = 0
        · rw [hd, abs_zero, zero_mul]
          exact mul_nonneg hC0 (div_nonneg (mul_nonneg zero_le_four hε1.le) ht₀.le)
        · have hlt := (hdz _ hd).2
          rw [div_lt_iff₀ htpos] at hlt
          apply mul_le_mul (hC _) _ (abs_nonneg _) hC0
          rw [abs_neg, abs_of_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg _))]
          rw [div_le_div_iff₀ (pow_pos htpos 2) ht₀]
          have : ‖x - z‖ * t₀ ≤ (1 + ε) * t * (2 * t) :=
            mul_le_mul hlt.le (by linarith only [ht1]) ht₀.le (mul_pos hε1 htpos).le
          have h5 := mul_pos hε1 (mul_pos htpos htpos)
          linarith only [this, h5]
      · rw [indicator_of_notMem hx, hzero' x t htpos ht2 hx, zero_mul, mul_zero, norm_zero]
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun t x => w x * φ (‖x - z‖ / t))
      (F' := fun t x => w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2))))
      (ball_mem_nhds t₀ hηpos) (Filter.Eventually.of_forall hmeasF) hint hmeasF' hbound (hind _)
      (Filter.Eventually.of_forall fun x t ht =>
        hpt x t (ne_of_gt (by linarith only [(hball t ht).1, ht₀])))
    exact key.2
  -- Step 3 (Hölder): `|∫ φ(|x - z|/t) ⟨x - z, H⟩ dμ| ≤ (1 + ε) t L I(t)^{1 - 1/p}`.
  have hholder : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (z : Amb n ℓ)
      (p Rz L ε t : ℝ) (hp : 1 < p) (ht : 0 < t) (hε : 0 < ε) (htR : (1 + ε) * t < Rz)
      (hfin : μ (closedBall z Rz) < ⊤) (hHint : IntegrableOn H (closedBall z Rz) μ) (hL0 : 0 ≤ L)
      (hL : (∫⁻ x in closedBall z Rz, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal L) (φ : ℝ → ℝ)
      (hφc : Continuous φ) (hφ0 : ∀ u, 1 + ε ≤ u → φ u = 0) (hφr : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1),
      |∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂μ| ≤
        (1 + ε) * t * L * (∫ x, φ (‖x - z‖ / t) ∂μ) ^ (1 - 1 / p)  := by
    clear hcut hderiv
    intro n ℓ μ H z p Rz L ε t hp ht hε htR hfin hHint hL0 hL φ hφc hφ0 hφr
    set B := closedBall z Rz with hB
    set f : Amb n ℓ → ℝ := fun x => φ (‖x - z‖ / t) with hf
    have hfc : Continuous f := hφc.comp ((continuous_id.sub continuous_const).norm.div_const t)
    have hfzero : ∀ x, x ∉ B → f x = 0 := by
      intro x hx
      apply hφ0
      rw [hB, mem_closedBall, dist_eq_norm, not_le] at hx
      rw [le_div_iff₀ ht]; exact (htR.trans hx).le
    -- `f ≠ 0` forces `|x - z| < (1+ε) t`
    have hfsupp : ∀ x, f x ≠ 0 → ‖x - z‖ ≤ (1 + ε) * t := by
      intro x hx
      by_contra hcon
      rw [not_le] at hcon
      exact hx (hφ0 _ (by rw [le_div_iff₀ ht]; exact hcon.le))
    have hfint : Integrable f μ := by
      have hind : Integrable (B.indicator fun _ => (1 : ℝ)) μ :=
        (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin.ne)
      refine hind.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hφr _).1]; exact (hφr _).2
      · rw [indicator_of_notMem hx, hfzero x hx, norm_zero]
    have hεt : 0 ≤ (1 + ε) * t := (mul_pos (add_pos one_pos hε) ht).le
    have hq := Real.HolderConjugate.conjExponent hp
    set q := p.conjExponent with hqdef
    have hexp : 1 / q = 1 - 1 / p := by simpa only [one_div] using hq.one_sub_inv.symm
    -- pointwise bound
    have hpt : ∀ x, ‖f x * inner ℝ (x - z) (H x)‖ₑ ≤
        ENNReal.ofReal ((1 + ε) * t) * (‖H x‖ₑ * ENNReal.ofReal (f x)) := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_mul hεt]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_mul, abs_of_nonneg (hφr _).1]
      by_cases hx0 : f x = 0
      · have h0 : φ (‖x - z‖ / t) = 0 := hx0
        rw [h0, zero_mul]
        exact mul_nonneg hεt (mul_nonneg (norm_nonneg _) (hφr _).1)
      · calc f x * |inner ℝ (x - z) (H x)| ≤ f x * (‖x - z‖ * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hφr _).1
          _ ≤ f x * ((1 + ε) * t * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hfsupp x hx0) (norm_nonneg _))
                (hφr _).1
          _ = (1 + ε) * t * (‖H x‖ * f x) := by ring
    have hsupp : Function.support (fun x => ‖H x‖ₑ * ENNReal.ofReal (f x)) ⊆ B := by
      intro x hx
      by_contra hxB
      apply hx
      show ‖H x‖ₑ * ENNReal.ofReal (f x) = 0
      rw [hfzero x hxB, ENNReal.ofReal_zero, mul_zero]
    have hHm : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict B) :=
      hHint.aestronglyMeasurable.enorm
    have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) (μ.restrict B) :=
      (ENNReal.measurable_ofReal.comp hfc.measurable).aemeasurable
    have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hq hHm hfm
    have hq1 : 1 ≤ q := hq.symm.lt.le
    have hq0 : 0 ≤ 1 / q := (one_div_pos.mpr (zero_lt_one.trans_le hq1)).le
    have hfq : ∫⁻ x in B, ENNReal.ofReal (f x) ^ q ∂μ ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
      calc ∫⁻ x in B, ENNReal.ofReal (f x) ^ q ∂μ ≤ ∫⁻ x in B, ENNReal.ofReal (f x) ∂μ :=
            lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one
              (ENNReal.ofReal_le_one.mpr (hφr _).2) hq1
        _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ x, f x ∂μ) :=
            (ofReal_integral_eq_lintegral_ofReal hfint
              (Filter.Eventually.of_forall fun x => (hφr _).1)).symm
    have hI0 : 0 ≤ ∫ x, f x ∂μ := integral_nonneg fun x => (hφr _).1
    have key : ‖∫ x, f x * inner ℝ (x - z) (H x) ∂μ‖ₑ ≤
        ENNReal.ofReal ((1 + ε) * t * L * (∫ x, f x ∂μ) ^ (1 - 1 / p)) := by
      calc ‖∫ x, f x * inner ℝ (x - z) (H x) ∂μ‖ₑ
          ≤ ∫⁻ x, ‖f x * inner ℝ (x - z) (H x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ x, ENNReal.ofReal ((1 + ε) * t) * (‖H x‖ₑ * ENNReal.ofReal (f x)) ∂μ :=
            lintegral_mono hpt
        _ = ENNReal.ofReal ((1 + ε) * t) * ∫⁻ x, ‖H x‖ₑ * ENNReal.ofReal (f x) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal ((1 + ε) * t) * ∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (f x) ∂μ := by
            rw [setLIntegral_eq_of_support_subset hsupp]
        _ ≤ ENNReal.ofReal ((1 + ε) * t) * ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) *
              (∫⁻ x in B, ENNReal.ofReal (f x) ^ q ∂μ) ^ (1 / q)) := by
            exact mul_le_mul' le_rfl hhold
        _ ≤ ENNReal.ofReal ((1 + ε) * t) * (ENNReal.ofReal L *
              (ENNReal.ofReal (∫ x, f x ∂μ)) ^ (1 / q)) :=
            mul_le_mul' le_rfl (mul_le_mul' hL (ENNReal.rpow_le_rpow hfq hq0))
        _ = ENNReal.ofReal ((1 + ε) * t * L * (∫ x, f x ∂μ) ^ (1 - 1 / p)) := by
            rw [hexp, ENNReal.ofReal_rpow_of_nonneg hI0 (by rw [← hexp]; exact hq0),
              ← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_mul hεt, mul_assoc,
              mul_assoc, mul_assoc]
    rw [Real.enorm_eq_ofReal_abs] at key
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hεt hL0) (Real.rpow_nonneg hI0 _))).mp key
  -- Step 4: right-continuity of `t ↦ μ(B_t(z))` for closed balls of finite mass.
  have hball_rc : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (z : Amb n ℓ) (t T : ℝ), t < T →
      μ (closedBall z T) < ⊤ → Tendsto (fun u => μ.real (closedBall z u)) (𝓝[>] t)
        (𝓝 (μ.real (closedBall z t))) := by
    clear hcut hderiv hholder
    intro n ℓ μ z t T htT hfin
    have h1 : Tendsto (fun u => μ (closedBall z u)) (𝓝[>] t) (𝓝 (μ (closedBall z t))) := by
      have := tendsto_measure_biInter_gt (μ := μ) (s := fun u => closedBall z u) (a := t)
        (fun r _ => measurableSet_closedBall.nullMeasurableSet)
        (fun i j _ hij => closedBall_subset_closedBall hij) ⟨T, htT, hfin.ne⟩
      rwa [biInter_gt_closedBall] at this
    have hne : μ (closedBall z t) ≠ ⊤ :=
      (measure_mono (closedBall_subset_closedBall htT.le)).trans_lt hfin |>.ne
    exact (ENNReal.tendsto_toReal hne).comp h1
  have hscale_rc : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (z : Amb n ℓ) (t T : ℝ), 0 < t → t < T →
      μ (closedBall z T) < ⊤ → Tendsto (fun ε : ℝ => μ.real (closedBall z ((1 + ε) * t)))
        (𝓝[>] 0) (𝓝 (μ.real (closedBall z t))) := by
    clear hcut hderiv hholder
    intro n ℓ μ z t T ht htT hfin
    have h2 : Tendsto (fun ε : ℝ => (1 + ε) * t) (𝓝[>] 0) (𝓝[>] t) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => (1 + ε) * t) (𝓝 0) (𝓝 ((1 + 0) * t)) :=
          ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
        rw [add_zero, one_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        show t < (1 + ε) * t
        have : (0 : ℝ) < ε := hε
        linarith only [mul_pos this ht]
    exact (hball_rc μ z t T htT hfin).comp h2
  -- Step 5 (fixed cutoff): `e^{λ}(1 + t⁻ⁿ I)` is nondecreasing and
  -- `e^{-λ}(1 + t⁻ⁿ I) - (1 + ε)ⁿ ∫ w φ(|x - z|/t) dμ` is nonincreasing.
  have hcore_eps : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : (n : ℝ) < p) (U : Set (Amb n ℓ))
      (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H)
      (hPae : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧
        V.tangentProj x = P.starProjection) (hPm : AEStronglyMeasurable V.tangentProj V.weight)
      (hPle : ∀ x v, ‖v - V.tangentProj x v‖ ≤ ‖v‖) (z : Amb n ℓ) (Rz Λz : ℝ) (hRz : 0 < Rz)
      (hΛz : 0 ≤ Λz) (hU : closedBall z Rz ⊆ U) (hfin : V.weight (closedBall z Rz) < ⊤) (α c : ℝ)
      (hα : α = 1 - (n : ℝ) / p) (hc : c = Λz / (2 * Rz ^ α))
      (hL : (∫⁻ x in closedBall z Rz, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤
        ENNReal.ofReal ((p - n) / (4 * p) * Λz / Rz ^ α)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφ1 : ∀ u, u ≤ 1 → φ u = 1)
      (hφ0 : ∀ u, 1 + ε ≤ u → φ u = 0) (hφr : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1) (hφd : ∀ u, deriv φ u ≤ 0)
      (hdz : ∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < 1 + ε) (C : ℝ) (hC0 : 0 ≤ C)
      (hC : ∀ u, |deriv φ u| ≤ C) (I : ℝ → ℝ) (hI : ∀ t, I t = ∫ x, φ (‖x - z‖ / t) ∂V.weight)
      (s' r' : ℝ) (hs' : 0 < s') (hsr : s' ≤ r') (hrR : (1 + ε) * r' < Rz) (a w : Amb n ℓ → ℝ)
      (ha : ∀ x, a x = ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2))
      (hw : ∀ x, w x = {x | s' < ‖x - z‖}.indicator a x),
      Real.exp (c * s' ^ α) * (1 + I s' / s' ^ n) ≤ Real.exp (c * r' ^ α) * (1 + I r' / r' ^ n) ∧
      Real.exp (-(c * r' ^ α)) * (1 + I r' / r' ^ n) ≤
        Real.exp (-(c * s' ^ α)) * (1 + I s' / s' ^ n) +
        (1 + ε) ^ n * ((∫ x, w x * φ (‖x - z‖ / r') ∂V.weight) -
          (∫ x, w x * φ (‖x - z‖ / s') ∂V.weight))  := by
    clear hcut hball_rc hscale_rc
    intro n ℓ hn p hp U V H hH hPae hPm hPle z Rz Λz hRz hΛz hU hfin α c hα hc hL ε hε hε1 φ hφ hφ1
      hφ0 hφr hφd hdz C hC0 hC I hI s' r' hs' hsr hrR a w ha hw
    have hn0 : n ≠ 0 := by omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp1 : 1 < p := hnR.trans_lt hp
    have hp0 : 0 < p := zero_lt_one.trans hp1
    have hα0 : 0 < α := by rw [hα, sub_pos, div_lt_one hp0]; exact hp
    have hRα : 0 < Rz ^ α := Real.rpow_pos_of_pos hRz α
    have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg hΛz (mul_nonneg zero_le_two hRα.le)
    obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ,
        g = fun x => ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ 2 := ⟨_, rfl⟩
    have hε1' : 0 < 1 + ε := add_pos one_pos hε
    have hsn : 0 < s' ^ n := pow_pos hs' n
    have hsn' : 0 ≤ 1 / s' ^ n := (one_div_pos.mpr hsn).le
    have hC2 : 0 ≤ 2 * C := mul_nonneg zero_le_two hC0
    -- measurability
    have hvm : AEStronglyMeasurable (fun x => V.tangentProj x (x - z)) V.weight :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => L v)
        (continuous_fst.clm_apply continuous_snd) hPm
        (continuous_id.sub continuous_const).aestronglyMeasurable
    have hnm : AEStronglyMeasurable (fun x => ‖(x - z) - V.tangentProj x (x - z)‖) V.weight :=
      ((continuous_id.sub continuous_const).aestronglyMeasurable.sub hvm).norm
    have hgm : AEStronglyMeasurable g V.weight := by
      rw [hg]
      exact ((hnm.aemeasurable.pow_const 2).div
        ((continuous_id.sub continuous_const).norm.pow 2).measurable.aemeasurable
        ).aestronglyMeasurable
    have ham : AEStronglyMeasurable a V.weight := by
      rw [show a = fun x => ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2) from
        funext ha]
      exact ((hnm.aemeasurable.pow_const 2).div
        ((continuous_id.sub continuous_const).norm.pow (n + 2)).measurable.aemeasurable
        ).aestronglyMeasurable
    have hwm : AEStronglyMeasurable w V.weight := by
      rw [show w = {x | s' < ‖x - z‖}.indicator a from funext hw]
      exact ham.indicator (measurableSet_lt measurable_const
        (continuous_id.sub continuous_const).norm.measurable)
    -- bounds
    have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
      intro x
      rw [hg]
      dsimp only
      refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
      rcases eq_or_ne (‖x - z‖) 0 with h0 | h0
      · rw [h0, zero_pow two_ne_zero, div_zero]; exact zero_le_one
      · rw [div_le_one (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) 2)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hPle x (x - z)) 2
    have ha0 : ∀ x, 0 ≤ a x := fun x => by
      rw [ha]; exact div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have hw0 : ∀ x, 0 ≤ w x := fun x => by
      rw [hw]; exact indicator_nonneg (fun x _ => ha0 x) x
    have hwle : ∀ x, w x ≤ 1 / s' ^ n := by
      intro x
      by_cases hx : s' < ‖x - z‖
      · have hxpos : 0 < ‖x - z‖ := hs'.trans hx
        rw [hw, indicator_of_mem (show x ∈ {x | s' < ‖x - z‖} from hx), ha]
        calc ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2)
            ≤ ‖x - z‖ ^ 2 / ‖x - z‖ ^ (n + 2) :=
              div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hPle x (x - z)) 2)
                (pow_nonneg (norm_nonneg _) _)
          _ = 1 / ‖x - z‖ ^ n := by
              rw [pow_add, div_mul_cancel_right₀ (pow_ne_zero 2 hxpos.ne'), one_div]
          _ ≤ 1 / s' ^ n := one_div_le_one_div_of_le hsn (pow_le_pow_left₀ hs'.le hx.le n)
      · rw [hw, indicator_of_notMem (show x ∉ {x | s' < ‖x - z‖} from hx)]; exact hsn'
    have hwabs : ∀ x, |w x| ≤ 1 / s' ^ n := fun x => by
      rw [abs_of_nonneg (hw0 x)]; exact hwle x
    -- integrability of bounded functions vanishing off `B_{Rz}(z)`
    have hindB : ∀ k : ℝ, Integrable ((closedBall z Rz).indicator fun _ => k) V.weight := fun k =>
      (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin.ne)
    have hintB : ∀ (F : Amb n ℓ → ℝ) (K : ℝ), AEStronglyMeasurable F V.weight →
        (∀ x, |F x| ≤ K) → (∀ x, x ∉ closedBall z Rz → F x = 0) → Integrable F V.weight := by
      intro F K hFm hFK hF0
      refine (hindB K).mono' hFm (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ closedBall z Rz
      · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hFK x
      · rw [indicator_of_notMem hx, hF0 x hx, norm_zero]
    have hout : ∀ x t, 0 < t → (1 + ε) * t < Rz → x ∉ closedBall z Rz →
        φ (‖x - z‖ / t) = 0 ∧ deriv φ (‖x - z‖ / t) = 0 := by
      intro x t ht htR hx
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      have h1 : 1 + ε ≤ ‖x - z‖ / t := by rw [le_div_iff₀ ht]; exact (htR.trans hx).le
      refine ⟨hφ0 _ h1, ?_⟩
      by_contra hne
      exact absurd (hdz _ hne).2 (not_lt.mpr h1)
    have hφc : Continuous φ := hφ.continuous
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
    have hcr : ∀ t, Continuous (fun x : Amb n ℓ => ‖x - z‖ / t) := fun t =>
      (continuous_id.sub continuous_const).norm.div_const t
    have hf0int : ∀ t, 0 < t → (1 + ε) * t < Rz →
        Integrable (fun x => φ (‖x - z‖ / t)) V.weight := by
      intro t ht htR
      refine hintB _ 1 (hφc.comp (hcr t)).aestronglyMeasurable (fun x => ?_)
        (fun x hx => (hout x t ht htR hx).1)
      rw [abs_of_nonneg (hφr _).1]; exact (hφr _).2
    have hf1bd : ∀ t, 0 < t → ∀ x, |‖x - z‖ / t * deriv φ (‖x - z‖ / t)| ≤ 2 * C := by
      intro t ht x
      by_cases hd : deriv φ (‖x - z‖ / t) = 0
      · rw [hd, mul_zero, abs_zero]; exact hC2
      · rw [abs_mul, abs_of_nonneg (div_nonneg (norm_nonneg _) ht.le)]
        exact mul_le_mul ((hdz _ hd).2.le.trans (by linarith only [hε1])) (hC _) (abs_nonneg _)
          zero_le_two
    have hf1m : ∀ t, AEStronglyMeasurable (fun x => ‖x - z‖ / t * deriv φ (‖x - z‖ / t))
        V.weight := fun t => ((hcr t).mul (hdc.comp (hcr t))).aestronglyMeasurable
    have hf1int : ∀ t, 0 < t → (1 + ε) * t < Rz →
        Integrable (fun x => ‖x - z‖ / t * deriv φ (‖x - z‖ / t)) V.weight := by
      intro t ht htR
      exact hintB _ (2 * C) (hf1m t) (hf1bd t ht)
        (fun x hx => by rw [(hout x t ht htR hx).2, mul_zero])
    have hf1gint : ∀ t, 0 < t → (1 + ε) * t < Rz →
        Integrable (fun x => ‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) V.weight := by
      intro t ht htR
      refine hintB _ (2 * C) ((hf1m t).mul hgm) (fun x => ?_)
        (fun x hx => by rw [(hout x t ht htR hx).2, mul_zero, zero_mul])
      rw [abs_mul, abs_of_nonneg (hg01 x).1]
      calc _ ≤ 2 * C * 1 := mul_le_mul (hf1bd t ht x) (hg01 x).2 (hg01 x).1 hC2
        _ = 2 * C := mul_one _
    -- derivative of the cutoff mass `I`
    have hIder : ∀ t, 0 < t → (1 + ε) * t < Rz →
        HasDerivAt I (-(∫ x, ‖x - z‖ / t * deriv φ (‖x - z‖ / t) ∂V.weight) / t) t := by
      intro t ht htR
      have h := hderiv V.weight z φ ε Rz 1 C hε hφ hφ0 hφr hdz hC hfin (fun _ => 1)
        aestronglyMeasurable_const (fun x => (abs_one).le) t ht htR
      have hfun : (fun t => ∫ x, (fun _ => (1 : ℝ)) x * φ (‖x - z‖ / t) ∂V.weight) = I := by
        funext t; rw [hI]; simp only [one_mul]
      rw [hfun] at h
      refine h.congr_deriv ?_
      rw [← integral_neg, ← integral_div]
      congr 1; funext x; ring
    -- `M' = N + e` from the radial first-variation identity
    have hMder : ∀ t, 0 < t → (1 + ε) * t < Rz →
        HasDerivAt (fun t => I t / t ^ n)
          ((∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) +
            (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1)) t := by
      intro t ht htR
      have hball : closedBall z ((1 + ε) * t) ⊆ U :=
        (closedBall_subset_closedBall htR.le).trans hU
      have hrad := aal_radial_first_variation_identity n ℓ U V H hH hPae z φ (1 + ε) t hφ hφ1 hφ0
        ht hball
      have hsplit : ∫ x, ((n : ℝ) * φ (‖x - z‖ / t) + ‖x - z‖ / t * deriv φ (‖x - z‖ / t) *
          (1 - ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ 2)) ∂V.weight =
          (n : ℝ) * I t + (∫ x, ‖x - z‖ / t * deriv φ (‖x - z‖ / t) ∂V.weight) -
            ∫ x, ‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x ∂V.weight := by
        have h1 : (fun x => (n : ℝ) * φ (‖x - z‖ / t) + ‖x - z‖ / t * deriv φ (‖x - z‖ / t) *
            (1 - ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ 2)) =
            fun x => ((n : ℝ) * φ (‖x - z‖ / t) + ‖x - z‖ / t * deriv φ (‖x - z‖ / t)) -
              ‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x := by
          funext x; rw [hg]; ring
        have hA : Integrable (fun x => (n : ℝ) * φ (‖x - z‖ / t) +
            ‖x - z‖ / t * deriv φ (‖x - z‖ / t)) V.weight :=
          ((hf0int t ht htR).const_mul _).add (hf1int t ht htR)
        rw [h1, integral_sub hA (hf1gint t ht htR),
          integral_add ((hf0int t ht htR).const_mul _) (hf1int t ht htR), integral_const_mul, hI]
      rw [hsplit] at hrad
      have hd := (hIder t ht htR).div (hasDerivAt_pow n t) (pow_ne_zero n ht.ne')
      refine hd.congr_deriv ?_
      rw [integral_neg]
      generalize (∫ x, ‖x - z‖ / t * deriv φ (‖x - z‖ / t) ∂V.weight) = A at hrad ⊢
      generalize (∫ x, ‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x ∂V.weight) = G at hrad ⊢
      generalize (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) = E at hrad ⊢
      generalize I t = B at hrad ⊢
      have htn : t ^ n = t ^ (n - 1) * t := (pow_sub_one_mul hn0 t).symm
      have htn1 : t ^ (n + 1) = t ^ (n - 1) * t * t := by rw [pow_succ, htn]
      have htq : t ^ (n - 1) ≠ 0 := pow_ne_zero _ ht.ne'
      rw [htn1, htn]
      field_simp
      linear_combination -hrad
    -- the mean-curvature term: `|e| ≤ λ' (1 + M)`
    have hHint : IntegrableOn H (closedBall z Rz) V.weight :=
      hH.1.integrableOn_compact_subset hU (isCompact_closedBall z Rz)
    have hLnn : 0 ≤ (p - n) / (4 * p) * Λz / Rz ^ α :=
      div_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hp.le) (mul_nonneg zero_le_four hp0.le))
        hΛz) hRα.le
    have hrpow1 : ∀ x : ℝ, 0 ≤ x → x ^ (1 - 1 / p) ≤ 1 + x := by
      intro x hx
      have hp' : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
      have he0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp1.le)
      have he1 : 1 - 1 / p ≤ 1 := by linarith only [hp']
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_one hx hx1 he0).trans (by linarith only [hx])
      · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hx1) he1).trans (by linarith only)
    have hconst : (1 + ε) * ((p - n) / (4 * p) * Λz / Rz ^ α) ≤ c * α := by
      have hκ : (p - n) / (4 * p) = α / 4 := by
        rw [hα, mul_comm (4 : ℝ) p, ← div_div, sub_div, div_self hp0.ne']
      have hX : 0 ≤ α * Λz / Rz ^ α := div_nonneg (mul_nonneg hα0.le hΛz) hRα.le
      rw [hκ, hc]
      calc (1 + ε) * (α / 4 * Λz / Rz ^ α) = (1 + ε) / 4 * (α * Λz / Rz ^ α) := by ring
        _ ≤ 1 / 2 * (α * Λz / Rz ^ α) :=
            mul_le_mul_of_nonneg_right (by linarith only [hε1]) hX
        _ = Λz / (2 * Rz ^ α) * α := by ring
    have heb : ∀ t, 0 < t → (1 + ε) * t < Rz →
        |(∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1)| ≤
          c * (α * t ^ (α - 1)) * (1 + I t / t ^ n) := by
      intro t ht htR
      have hhol := hholder V.weight H z p Rz ((p - n) / (4 * p) * Λz / Rz ^ α) ε t hp1 ht hε
        htR hfin hHint hLnn hL φ hφc hφ0 hφr
      rw [← hI] at hhol
      have hI0 : 0 ≤ I t := by rw [hI]; exact integral_nonneg fun x => (hφr _).1
      have htn : 0 < t ^ n := pow_pos ht n
      have hM0 : 0 ≤ I t / t ^ n := div_nonneg hI0 htn.le
      have hrp : (I t) ^ (1 - 1 / p) = (t ^ n) ^ (1 - 1 / p) * (I t / t ^ n) ^ (1 - 1 / p) := by
        conv_lhs => rw [← mul_div_cancel₀ (I t) htn.ne']
        rw [Real.mul_rpow htn.le hM0]
      have hkey : t * (t ^ n) ^ (1 - 1 / p) = t ^ (α - 1) * t ^ (n + 1) := by
        calc t * (t ^ n) ^ (1 - 1 / p) = t ^ (1 : ℝ) * t ^ ((n : ℝ) * (1 - 1 / p)) := by
              rw [Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
          _ = t ^ (1 + (n : ℝ) * (1 - 1 / p)) := by rw [← Real.rpow_add ht]
          _ = t ^ ((α - 1) + ((n + 1 : ℕ) : ℝ)) := by congr 1; rw [hα]; push_cast; ring
          _ = t ^ (α - 1) * t ^ (n + 1) := by rw [Real.rpow_add ht, Real.rpow_natCast]
      rw [abs_div, abs_of_pos (pow_pos ht _), div_le_iff₀ (pow_pos ht _)]
      calc |∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight|
          ≤ (1 + ε) * t * ((p - n) / (4 * p) * Λz / Rz ^ α) * (I t) ^ (1 - 1 / p) := hhol
        _ = (1 + ε) * ((p - n) / (4 * p) * Λz / Rz ^ α) * (I t / t ^ n) ^ (1 - 1 / p) *
              (t * (t ^ n) ^ (1 - 1 / p)) := by rw [hrp]; ring
        _ ≤ c * α * (1 + I t / t ^ n) * (t * (t ^ n) ^ (1 - 1 / p)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hconst (hrpow1 _ hM0)
              (Real.rpow_nonneg hM0 _) (mul_nonneg hc0 hα0.le))
              (mul_nonneg ht.le (Real.rpow_nonneg htn.le _))
        _ = c * (α * t ^ (α - 1)) * (1 + I t / t ^ n) * t ^ (n + 1) := by rw [hkey]; ring
    -- `N ≥ 0`
    have hN0 : ∀ t, 0 < t →
        0 ≤ (∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) := by
      intro t ht
      refine div_nonneg (integral_nonneg fun x => ?_) (pow_pos ht _).le
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (norm_nonneg _) ht.le) (hφd _)) (hg01 x).1)
    -- derivative of the annular functional
    have hQder : ∀ t, 0 < t → (1 + ε) * t < Rz →
        HasDerivAt (fun t => ∫ x, w x * φ (‖x - z‖ / t) ∂V.weight)
          (∫ x, w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2))) ∂V.weight) t :=
      fun t ht htR => hderiv V.weight z φ ε Rz (1 / s' ^ n) C hε hφ hφ0 hφr hdz hC hfin
        w hwm hwabs t ht htR
    have hQint : ∀ t, 0 < t → (1 + ε) * t < Rz →
        Integrable (fun x => w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2)))) V.weight := by
      intro t ht htR
      have h2t : 0 ≤ 2 / t := div_nonneg zero_le_two ht.le
      refine hintB _ (1 / s' ^ n * (C * (2 / t))) (hwm.mul ((hdc.comp (hcr t)).mul
        ((continuous_id.sub continuous_const).norm.div_const _).neg).aestronglyMeasurable)
        (fun x => ?_) (fun x hx => by rw [(hout x t ht htR hx).2, zero_mul, mul_zero])
      rw [abs_mul, abs_mul, abs_neg]
      apply mul_le_mul (hwabs x) _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hsn'
      by_cases hd : deriv φ (‖x - z‖ / t) = 0
      · rw [hd, abs_zero, zero_mul]; exact mul_nonneg hC0 h2t
      · apply mul_le_mul (hC _) _ (abs_nonneg _) hC0
        have h1 := (hdz _ hd).2
        rw [div_lt_iff₀ ht] at h1
        have h2 : (1 + ε) * t ≤ 2 * t := mul_le_mul_of_nonneg_right (by linarith only [hε1]) ht.le
        rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg t)),
          div_le_div_iff₀ (pow_pos ht 2) ht]
        calc ‖x - z‖ * t ≤ (2 * t) * t := mul_le_mul_of_nonneg_right (h1.le.trans h2) ht.le
          _ = 2 * t ^ 2 := by ring
    have hNQ : ∀ t, s' ≤ t → (1 + ε) * t < Rz →
        (∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) ≤
          (1 + ε) ^ n * ∫ x, w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2))) ∂V.weight := by
      intro t hst htR
      have ht : 0 < t := hs'.trans_le hst
      rw [← integral_div, ← integral_const_mul]
      refine integral_mono ((hf1gint t ht htR).neg.div_const _) ((hQint t ht htR).const_mul _)
        fun x => ?_
      by_cases hd : deriv φ (‖x - z‖ / t) = 0
      · simp only [hd, mul_zero, zero_mul, neg_zero, zero_div, le_refl]
      · obtain ⟨h1, h2⟩ := hdz _ hd
        rw [lt_div_iff₀ ht, one_mul] at h1
        rw [div_lt_iff₀ ht] at h2
        have hr : 0 < ‖x - z‖ := ht.trans h1
        have hwx : w x = a x := by
          rw [hw, indicator_of_mem (show x ∈ {x | s' < ‖x - z‖} from hst.trans_lt h1)]
        have hdneg : deriv φ (‖x - z‖ / t) < 0 := lt_of_le_of_ne (hφd _) hd
        rw [hwx, ha, hg]
        dsimp only
        have hN2 : 0 ≤ ‖x - z - (V.tangentProj x) (x - z)‖ ^ 2 := sq_nonneg _
        generalize deriv φ (‖x - z‖ / t) = d at hdneg ⊢
        generalize ‖x - z - (V.tangentProj x) (x - z)‖ ^ 2 = N2 at hN2 ⊢
        generalize ‖x - z‖ = r at hr h1 h2 ⊢
        have hK : 0 ≤ -d * N2 := mul_nonneg (neg_nonneg.mpr hdneg.le) hN2
        have e1 : -(r / t * d * (N2 / r ^ 2)) / t ^ (n + 1) =
            (-d * N2) * (r / (t * r ^ 2 * t ^ (n + 1))) := by ring
        have e2 : (1 + ε) ^ n * (N2 / r ^ (n + 2) * (d * -(r / t ^ 2))) =
            (-d * N2) * ((1 + ε) ^ n * r / (r ^ (n + 2) * t ^ 2)) := by ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_left _ hK
        rw [div_le_div_iff₀ (mul_pos (mul_pos ht (pow_pos hr 2)) (pow_pos ht _))
          (mul_pos (pow_pos hr _) (pow_pos ht 2))]
        have hpow : r ^ n ≤ ((1 + ε) * t) ^ n := pow_le_pow_left₀ hr.le h2.le n
        calc r * (r ^ (n + 2) * t ^ 2) = r ^ n * (r ^ 3 * t ^ 2) := by ring
          _ ≤ ((1 + ε) * t) ^ n * (r ^ 3 * t ^ 2) :=
              mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg hr.le 3) (sq_nonneg t))
          _ = (1 + ε) ^ n * r * (t * r ^ 2 * t ^ (n + 1)) := by rw [mul_pow]; ring
    -- the integrating factors `exp(± c t^α)`
    have hlamder : ∀ t, 0 < t → HasDerivAt (fun t => c * t ^ α) (c * (α * t ^ (α - 1))) t :=
      fun t ht => (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul c
    have hIcc : ∀ t ∈ Icc s' r', 0 < t ∧ (1 + ε) * t < Rz := fun t ht =>
      ⟨hs'.trans_le ht.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hε1'.le) hrR⟩
    have hΦ : MonotoneOn (fun t => Real.exp (c * t ^ α) * (1 + I t / t ^ n)) (Icc s' r') := by
      have hder : ∀ t ∈ Icc s' r', HasDerivAt (fun t => Real.exp (c * t ^ α) * (1 + I t / t ^ n))
          (Real.exp (c * t ^ α) * (c * (α * t ^ (α - 1))) * (1 + I t / t ^ n) +
            Real.exp (c * t ^ α) *
              ((∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) +
                (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1))) t := by
        intro t ht
        obtain ⟨ht0, htR⟩ := hIcc t ht
        exact ((hlamder t ht0).exp).mul ((hMder t ht0 htR).const_add 1)
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s' r')
        (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt) fun t ht => ?_
      obtain ⟨ht0, htR⟩ := hIcc t (interior_subset ht)
      have h1 := (abs_le.mp (heb t ht0 htR)).1
      have h2 := hN0 t ht0
      have hexp := Real.exp_pos (c * t ^ α)
      generalize (∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) = N
        at h2 ⊢
      generalize (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1) = e
        at h1 ⊢
      generalize c * (α * t ^ (α - 1)) = d at h1 ⊢
      generalize Real.exp (c * t ^ α) = E at hexp ⊢
      calc (0 : ℝ) ≤ E * (d * (1 + I t / t ^ n) + e + N) :=
            mul_nonneg hexp.le (by linarith only [h1, h2])
        _ = E * d * (1 + I t / t ^ n) + E * (N + e) := by ring
    have hΨ : AntitoneOn (fun t => Real.exp (-(c * t ^ α)) * (1 + I t / t ^ n) -
        (1 + ε) ^ n * ((∫ x, w x * φ (‖x - z‖ / t) ∂V.weight) -
          ∫ x, w x * φ (‖x - z‖ / s') ∂V.weight)) (Icc s' r') := by
      have hder : ∀ t ∈ Icc s' r', HasDerivAt (fun t => Real.exp (-(c * t ^ α)) *
          (1 + I t / t ^ n) - (1 + ε) ^ n * ((∫ x, w x * φ (‖x - z‖ / t) ∂V.weight) -
            ∫ x, w x * φ (‖x - z‖ / s') ∂V.weight))
          (Real.exp (-(c * t ^ α)) * (-(c * (α * t ^ (α - 1)))) * (1 + I t / t ^ n) +
            Real.exp (-(c * t ^ α)) *
              ((∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) +
                (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1)) -
            (1 + ε) ^ n *
              ∫ x, w x * (deriv φ (‖x - z‖ / t) * (-(‖x - z‖ / t ^ 2))) ∂V.weight) t := by
        intro t ht
        obtain ⟨ht0, htR⟩ := hIcc t ht
        exact (((hlamder t ht0).neg.exp).mul ((hMder t ht0 htR).const_add 1)).sub
          (((hQder t ht0 htR).sub_const _).const_mul _)
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s' r')
        (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt) fun t ht => ?_
      obtain ⟨ht0, htR⟩ := hIcc t (interior_subset ht)
      have h1 := (abs_le.mp (heb t ht0 htR)).2
      have h2 := hN0 t ht0
      have h4 := hNQ t (interior_subset ht).1 htR
      have hlam0 : 0 ≤ c * t ^ α := mul_nonneg hc0 (Real.rpow_nonneg ht0.le α)
      have hexp := Real.exp_pos (-(c * t ^ α))
      have hexp1 : Real.exp (-(c * t ^ α)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlam0)
      generalize (∫ x, -(‖x - z‖ / t * deriv φ (‖x - z‖ / t) * g x) ∂V.weight) / t ^ (n + 1) = N
        at h2 h4 ⊢
      generalize (∫ x, φ (‖x - z‖ / t) * inner ℝ (x - z) (H x) ∂V.weight) / t ^ (n + 1) = e
        at h1 ⊢
      generalize c * (α * t ^ (α - 1)) = d at h1 ⊢
      generalize Real.exp (-(c * t ^ α)) = E at hexp hexp1 ⊢
      have h5 : E * (e - d * (1 + I t / t ^ n)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hexp.le (sub_nonpos.mpr h1)
      have h6 : E * N ≤ N := mul_le_of_le_one_left h2 hexp1
      linarith only [h4, h5, h6]
    have hi := hΦ (left_mem_Icc.mpr hsr) (right_mem_Icc.mpr hsr) hsr
    have hii := hΨ (left_mem_Icc.mpr hsr) (right_mem_Icc.mpr hsr) hsr
    simp only [sub_self, mul_zero, sub_zero] at hii
    exact ⟨hi, by linarith only [hii]⟩
  clear hderiv hholder
  -- Step 6: letting the cutoff tend to `1_{(-∞, 1]}`, the same estimates for `μ(B_t(z))`.
  have hcore : ∀ {n ℓ : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : (n : ℝ) < p) (U : Set (Amb n ℓ))
      (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H)
      (hPae : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧
        V.tangentProj x = P.starProjection) (hPm : AEStronglyMeasurable V.tangentProj V.weight)
      (hPle : ∀ x v, ‖v - V.tangentProj x v‖ ≤ ‖v‖) (z : Amb n ℓ) (Rz Λz : ℝ) (hRz : 0 < Rz)
      (hΛz : 0 ≤ Λz) (hU : closedBall z Rz ⊆ U) (hfin : V.weight (closedBall z Rz) < ⊤) (α c : ℝ)
      (hα : α = 1 - (n : ℝ) / p) (hc : c = Λz / (2 * Rz ^ α))
      (hL : (∫⁻ x in closedBall z Rz, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤
        ENNReal.ofReal ((p - n) / (4 * p) * Λz / Rz ^ α)) (s' r' : ℝ) (hs' : 0 < s') (hsr : s' ≤ r')
      (hrR : r' < Rz),
      Real.exp (c * s' ^ α) * (1 + V.weight.real (closedBall z s') / s' ^ n) ≤
        Real.exp (c * r' ^ α) * (1 + V.weight.real (closedBall z r') / r' ^ n) ∧
      Real.exp (-(c * r' ^ α)) * (1 + V.weight.real (closedBall z r') / r' ^ n) ≤
        Real.exp (-(c * s' ^ α)) * (1 + V.weight.real (closedBall z s') / s' ^ n) +
        ∫ x in closedBall z r' \ closedBall z s',
          ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2) ∂V.weight  := by
    clear hball_rc
    intro n ℓ hn p hp U V H hH hPae hPm hPle z Rz Λz hRz hΛz hU hfin α c hα hc hL s' r' hs' hsr hrR
    have hr' : 0 < r' := hs'.trans_le hsr
    obtain ⟨a, ha⟩ : ∃ a : Amb n ℓ → ℝ,
        a = fun x => ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → ℝ, w = {x | s' < ‖x - z‖}.indicator a := ⟨_, rfl⟩
    have ha0 : ∀ x, 0 ≤ a x := fun x => by
      rw [ha]; exact div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have hsn : 0 < s' ^ n := pow_pos hs' n
    have hsn' : 0 ≤ 1 / s' ^ n := (one_div_pos.mpr hsn).le
    have hw0 : ∀ x, 0 ≤ w x := fun x => by rw [hw]; exact indicator_nonneg (fun x _ => ha0 x) x
    have hale : ∀ x, s' < ‖x - z‖ → a x ≤ 1 / s' ^ n := by
      intro x hx
      have hxpos : 0 < ‖x - z‖ := hs'.trans hx
      rw [ha]
      calc ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2)
          ≤ ‖x - z‖ ^ 2 / ‖x - z‖ ^ (n + 2) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hPle x (x - z)) 2)
              (pow_nonneg (norm_nonneg _) _)
        _ = 1 / ‖x - z‖ ^ n := by
            rw [pow_add, div_mul_cancel_right₀ (pow_ne_zero 2 hxpos.ne'), one_div]
        _ ≤ 1 / s' ^ n := one_div_le_one_div_of_le hsn (pow_le_pow_left₀ hs'.le hx.le n)
    have hwle : ∀ x, w x ≤ 1 / s' ^ n := by
      intro x
      by_cases hx : s' < ‖x - z‖
      · rw [hw, indicator_of_mem (show x ∈ {x | s' < ‖x - z‖} from hx)]; exact hale x hx
      · rw [hw, indicator_of_notMem (show x ∉ {x | s' < ‖x - z‖} from hx)]; exact hsn'
    have hvm : AEStronglyMeasurable (fun x => V.tangentProj x (x - z)) V.weight :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => L v)
        (continuous_fst.clm_apply continuous_snd) hPm
        (continuous_id.sub continuous_const).aestronglyMeasurable
    have hnm : AEStronglyMeasurable (fun x => ‖(x - z) - V.tangentProj x (x - z)‖) V.weight :=
      ((continuous_id.sub continuous_const).aestronglyMeasurable.sub hvm).norm
    have ham : AEStronglyMeasurable a V.weight := by
      rw [ha]
      exact ((hnm.aemeasurable.pow_const 2).div ((continuous_id.sub continuous_const).norm.pow
        (n + 2)).measurable.aemeasurable).aestronglyMeasurable
    have hwm : AEStronglyMeasurable w V.weight := by
      rw [hw]
      exact ham.indicator (measurableSet_lt measurable_const
        (continuous_id.sub continuous_const).norm.measurable)
    have hfinB : ∀ t, t ≤ Rz → V.weight (closedBall z t) < ⊤ := fun t ht =>
      (measure_mono (closedBall_subset_closedBall ht)).trans_lt hfin
    -- the fixed-`ε` inequalities, for all small `ε`
    have hε₀ : 0 < min 1 (Rz / r' - 1) :=
      lt_min one_pos (by rw [sub_pos, one_lt_div hr']; exact hrR)
    have hfix : ∀ ε ∈ Ioo 0 (min 1 (Rz / r' - 1)),
        Real.exp (c * s' ^ α) * (1 + V.weight.real (closedBall z s') / s' ^ n) ≤
          Real.exp (c * r' ^ α) * (1 + V.weight.real (closedBall z ((1 + ε) * r')) / r' ^ n) ∧
        Real.exp (-(c * r' ^ α)) * (1 + V.weight.real (closedBall z r') / r' ^ n) ≤
          Real.exp (-(c * s' ^ α)) * (1 + V.weight.real (closedBall z ((1 + ε) * s')) / s' ^ n) +
          (1 + ε) ^ n * ((∫ x in closedBall z r' \ closedBall z s', a x ∂V.weight) +
            (V.weight.real (closedBall z ((1 + ε) * r')) - V.weight.real (closedBall z r')) /
              s' ^ n) := by
      intro ε hε
      have hε0 : 0 < ε := hε.1
      have hε1 : ε ≤ 1 := hε.2.le.trans (min_le_left _ _)
      have hεR : (1 + ε) * r' < Rz := by
        have h := hε.2.trans_le (min_le_right _ _)
        rw [lt_sub_iff_add_lt, lt_div_iff₀ hr'] at h
        linarith only [h]
      obtain ⟨φ, hφ, hφ1, hφ0, hφr, hφd, hdz, C, hC0, hC⟩ := hcut ε hε0
      have hcore := hcore_eps hn p hp U V H hH hPae hPm hPle z Rz Λz hRz hΛz hU hfin α c hα hc
        hL ε hε0 hε1 φ hφ hφ1 hφ0 hφr hφd hdz C hC0 hC (fun t => ∫ x, φ (‖x - z‖ / t) ∂V.weight)
        (fun t => rfl) s' r' hs' hsr hεR a w (fun x => by rw [ha]) (fun x => by rw [hw])
      have hφc : Continuous φ := hφ.continuous
      have hcr : ∀ t, Continuous (fun x : Amb n ℓ => ‖x - z‖ / t) := fun t =>
        (continuous_id.sub continuous_const).norm.div_const t
      have hindB : ∀ k : ℝ, Integrable ((closedBall z Rz).indicator fun _ => k) V.weight :=
        fun k => (integrable_indicator_iff measurableSet_closedBall).mpr
          (integrableOn_const hfin.ne)
      have hintB : ∀ (F : Amb n ℓ → ℝ) (K : ℝ), AEStronglyMeasurable F V.weight →
          (∀ x, |F x| ≤ K) → (∀ x, x ∉ closedBall z Rz → F x = 0) → Integrable F V.weight := by
        intro F K hFm hFK hF0
        refine (hindB K).mono' hFm (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ closedBall z Rz
        · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hFK x
        · rw [indicator_of_notMem hx, hF0 x hx, norm_zero]
      have hzero : ∀ x t, 0 < t → (1 + ε) * t < Rz → x ∉ closedBall z Rz →
          φ (‖x - z‖ / t) = 0 := by
        intro x t ht htR hx
        rw [mem_closedBall, dist_eq_norm, not_le] at hx
        exact hφ0 _ (by rw [le_div_iff₀ ht]; linarith)
      have hφint : ∀ t, 0 < t → (1 + ε) * t < Rz →
          Integrable (fun x => φ (‖x - z‖ / t)) V.weight := by
        intro t ht htR
        refine hintB _ 1 (hφc.comp (hcr t)).aestronglyMeasurable (fun x => ?_)
          (fun x hx => hzero x t ht htR hx)
        rw [abs_of_nonneg (hφr _).1]; exact (hφr _).2
      have hwφint : ∀ t, 0 < t → (1 + ε) * t < Rz →
          Integrable (fun x => w x * φ (‖x - z‖ / t)) V.weight := by
        intro t ht htR
        refine hintB _ (1 / s' ^ n) (hwm.mul (hφc.comp (hcr t)).aestronglyMeasurable) (fun x => ?_)
          (fun x hx => by rw [hzero x t ht htR hx, mul_zero])
        rw [abs_mul, abs_of_nonneg (hw0 x), abs_of_nonneg (hφr _).1]
        calc w x * φ (‖x - z‖ / t) ≤ 1 / s' ^ n * 1 :=
              mul_le_mul (hwle x) (hφr _).2 (hφr _).1 hsn'
          _ = 1 / s' ^ n := mul_one _
      -- `μ(B_t) ≤ I(t) ≤ μ(B_{(1+ε)t})`
      have hlow : ∀ t, 0 < t → (1 + ε) * t < Rz →
          V.weight.real (closedBall z t) ≤ ∫ x, φ (‖x - z‖ / t) ∂V.weight := by
        intro t ht htR
        have htR' : t ≤ Rz :=
          (le_mul_of_one_le_left ht.le (by linarith only [hε0])).trans htR.le
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono ((integrable_indicator_iff measurableSet_closedBall).mpr
          (integrableOn_const (hfinB t htR').ne)) (hφint t ht htR) fun x => ?_
        by_cases hx : x ∈ closedBall z t
        · rw [indicator_of_mem hx, Pi.one_apply, hφ1]
          rw [mem_closedBall, dist_eq_norm] at hx
          rw [div_le_one ht]; exact hx
        · rw [indicator_of_notMem hx]; exact (hφr _).1
      have hup : ∀ t, 0 < t → (1 + ε) * t < Rz →
          ∫ x, φ (‖x - z‖ / t) ∂V.weight ≤ V.weight.real (closedBall z ((1 + ε) * t)) := by
        intro t ht htR
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono (hφint t ht htR)
          ((integrable_indicator_iff measurableSet_closedBall).mpr
            (integrableOn_const (hfinB _ htR.le).ne)) fun x => ?_
        by_cases hx : x ∈ closedBall z ((1 + ε) * t)
        · rw [indicator_of_mem hx, Pi.one_apply]; exact (hφr _).2
        · rw [indicator_of_notMem hx, hφ0]
          rw [mem_closedBall, dist_eq_norm, not_le] at hx
          rw [le_div_iff₀ ht]; exact hx.le
      -- the annular bound
      have hsR : (1 + ε) * s' < Rz :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsr (by linarith only [hε0])) hεR
      have hA : MeasurableSet (closedBall z r' \ closedBall z s') :=
        measurableSet_closedBall.diff measurableSet_closedBall
      have hA' : MeasurableSet (closedBall z ((1 + ε) * r') \ closedBall z r') :=
        measurableSet_closedBall.diff measurableSet_closedBall
      have hsub : closedBall z r' ⊆ closedBall z ((1 + ε) * r') :=
        closedBall_subset_closedBall (le_mul_of_one_le_left hr'.le (by linarith only [hε0]))
      have hfinA : V.weight (closedBall z r' \ closedBall z s') < ⊤ :=
        (measure_mono (sdiff_subset.trans (closedBall_subset_closedBall hrR.le))).trans_lt hfin
      have intA : Integrable ((closedBall z r' \ closedBall z s').indicator a) V.weight := by
        rw [integrable_indicator_iff hA]
        have : IsFiniteMeasure (V.weight.restrict (closedBall z r' \ closedBall z s')) :=
          isFiniteMeasure_restrict.mpr hfinA.ne
        refine (integrable_const (1 / s' ^ n)).mono' ham.restrict
          ((ae_restrict_iff' hA).mpr (Filter.Eventually.of_forall fun x hx => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]
        apply hale x
        have := hx.2
        rw [mem_closedBall, dist_eq_norm, not_le] at this
        exact this
      have intA' : Integrable ((closedBall z ((1 + ε) * r') \ closedBall z r').indicator
          fun _ => 1 / s' ^ n) V.weight :=
        (integrable_indicator_iff hA').mpr (integrableOn_const
          ((measure_mono (sdiff_subset.trans (closedBall_subset_closedBall hεR.le))).trans_lt
            hfin).ne)
      have hann : (∫ x, w x * φ (‖x - z‖ / r') ∂V.weight) -
            (∫ x, w x * φ (‖x - z‖ / s') ∂V.weight) ≤
          (∫ x in closedBall z r' \ closedBall z s', a x ∂V.weight) +
            (V.weight.real (closedBall z ((1 + ε) * r')) - V.weight.real (closedBall z r')) /
              s' ^ n := by
        rw [← integral_sub (hwφint r' hr' hεR) (hwφint s' hs' hsR),
          ← measureReal_sdiff hsub measurableSet_closedBall (hfinB _ hεR.le).ne]
        have h2 : V.weight.real (closedBall z ((1 + ε) * r') \ closedBall z r') / s' ^ n =
            ∫ x, (closedBall z ((1 + ε) * r') \ closedBall z r').indicator
              (fun _ => 1 / s' ^ n) x ∂V.weight := by
          rw [integral_indicator_const _ hA', smul_eq_mul]; ring
        rw [h2, ← integral_indicator hA, ← integral_add intA intA']
        refine integral_mono ((hwφint r' hr' hεR).sub (hwφint s' hs' hsR)) (intA.add intA')
          fun x => ?_
        have hi1 : 0 ≤ (closedBall z r' \ closedBall z s').indicator a x :=
          indicator_nonneg (fun x _ => ha0 x) x
        have hi2 : 0 ≤ (closedBall z ((1 + ε) * r') \ closedBall z r').indicator
            (fun _ => 1 / s' ^ n) x := indicator_nonneg (fun _ _ => hsn') x
        have h1 : w x * φ (‖x - z‖ / r') - w x * φ (‖x - z‖ / s') ≤ w x * φ (‖x - z‖ / r') :=
          sub_le_self _ (mul_nonneg (hw0 x) (hφr _).1)
        refine h1.trans ?_
        by_cases hxs : s' < ‖x - z‖
        · have hwa : w x = a x := by
            rw [hw, indicator_of_mem (show x ∈ {x | s' < ‖x - z‖} from hxs)]
          by_cases hxr : ‖x - z‖ ≤ r'
          · have hxA : x ∈ closedBall z r' \ closedBall z s' :=
              ⟨by rw [mem_closedBall, dist_eq_norm]; exact hxr,
                by rw [mem_closedBall, dist_eq_norm, not_le]; exact hxs⟩
            rw [indicator_of_mem hxA, hwa]
            calc a x * φ (‖x - z‖ / r') ≤ a x * 1 :=
                  mul_le_mul_of_nonneg_left (hφr _).2 (ha0 x)
              _ = a x := mul_one _
              _ ≤ a x + _ := le_add_of_nonneg_right hi2
          · by_cases hxr2 : ‖x - z‖ ≤ (1 + ε) * r'
            · have hxA' : x ∈ closedBall z ((1 + ε) * r') \ closedBall z r' :=
                ⟨by rw [mem_closedBall, dist_eq_norm]; exact hxr2,
                  by rw [mem_closedBall, dist_eq_norm]; exact hxr⟩
              rw [indicator_of_mem hxA']
              calc w x * φ (‖x - z‖ / r') ≤ w x * 1 :=
                    mul_le_mul_of_nonneg_left (hφr _).2 (hw0 x)
                _ = w x := mul_one _
                _ ≤ 1 / s' ^ n := hwle x
                _ ≤ _ + 1 / s' ^ n := le_add_of_nonneg_left hi1
            · rw [not_le] at hxr2
              rw [hφ0 (‖x - z‖ / r') (by rw [le_div_iff₀ hr']; exact hxr2.le), mul_zero]
              exact add_nonneg hi1 hi2
        · rw [hw, indicator_of_notMem (show x ∉ {x | s' < ‖x - z‖} from hxs), zero_mul]
          exact add_nonneg hi1 hi2
      have hpos1 := Real.exp_pos (c * s' ^ α)
      have hpos2 := Real.exp_pos (c * r' ^ α)
      have hpos3 := Real.exp_pos (-(c * r' ^ α))
      have hpos4 := Real.exp_pos (-(c * s' ^ α))
      have hls := hlow s' hs' hsR
      have hlr := hlow r' hr' hεR
      have hus := hup s' hs' hsR
      have hur := hup r' hr' hεR
      have hpn : 0 ≤ (1 + ε) ^ n := pow_nonneg (by linarith only [hε0]) n
      have hrn : 0 ≤ r' ^ n := (pow_pos hr' n).le
      constructor
      · calc Real.exp (c * s' ^ α) * (1 + V.weight.real (closedBall z s') / s' ^ n)
            ≤ Real.exp (c * s' ^ α) * (1 + (∫ x, φ (‖x - z‖ / s') ∂V.weight) / s' ^ n) :=
              mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right hls hsn.le) 1)
                hpos1.le
          _ ≤ Real.exp (c * r' ^ α) * (1 + (∫ x, φ (‖x - z‖ / r') ∂V.weight) / r' ^ n) := hcore.1
          _ ≤ _ := mul_le_mul_of_nonneg_left
                (add_le_add_right (div_le_div_of_nonneg_right hur hrn) 1) hpos2.le
      · calc Real.exp (-(c * r' ^ α)) * (1 + V.weight.real (closedBall z r') / r' ^ n)
            ≤ Real.exp (-(c * r' ^ α)) * (1 + (∫ x, φ (‖x - z‖ / r') ∂V.weight) / r' ^ n) :=
              mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right hlr hrn) 1)
                hpos3.le
          _ ≤ _ := hcore.2
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
                (add_le_add_right (div_le_div_of_nonneg_right hus hsn.le) 1) hpos4.le)
                (mul_le_mul_of_nonneg_left hann hpn)
    -- `ε → 0`
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min 1 (Rz / r' - 1)) := Ioo_mem_nhdsGT hε₀
    have hTr := hscale_rc V.weight z r' Rz hr' hrR hfin
    have hTs := hscale_rc V.weight z s' Rz hs' (hsr.trans_lt hrR) hfin
    have hpow : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝 0) (𝓝 ((1 + 0) ^ n)) :=
        ((continuous_const.add continuous_id).pow n).tendsto 0
      rw [add_zero, one_pow] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hD : (∫ x in closedBall z r' \ closedBall z s', a x ∂V.weight) =
        ∫ x in closedBall z r' \ closedBall z s',
          ‖(x - z) - V.tangentProj x (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2) ∂V.weight := by
      rw [ha]
    rw [← hD]
    constructor
    · exact ge_of_tendsto ((((hTr.div_const (r' ^ n)).const_add 1).const_mul
        (Real.exp (c * r' ^ α)))) (by filter_upwards [hev] with ε hε; exact (hfix ε hε).1)
    · have hlim : Tendsto (fun ε : ℝ => Real.exp (-(c * s' ^ α)) *
            (1 + V.weight.real (closedBall z ((1 + ε) * s')) / s' ^ n) +
            (1 + ε) ^ n * ((∫ x in closedBall z r' \ closedBall z s', a x ∂V.weight) +
              (V.weight.real (closedBall z ((1 + ε) * r')) - V.weight.real (closedBall z r')) /
                s' ^ n)) (𝓝[>] 0)
          (𝓝 (Real.exp (-(c * s' ^ α)) * (1 + V.weight.real (closedBall z s') / s' ^ n) +
            1 * ((∫ x in closedBall z r' \ closedBall z s', a x ∂V.weight) +
              (V.weight.real (closedBall z r') - V.weight.real (closedBall z r')) / s' ^ n))) := by
        apply Tendsto.add
        · exact ((hTs.div_const _).const_add 1).const_mul _
        · exact hpow.mul (tendsto_const_nhds.add ((hTr.sub tendsto_const_nhds).div_const _))
      rw [sub_self, zero_div, add_zero, one_mul] at hlim
      exact ge_of_tendsto hlim (by filter_upwards [hev] with ε hε; exact (hfix ε hε).2)
  clear hcut hcore_eps hscale_rc
  -- Step 7: the three assertions at `y`.
  intro n ℓ hn p hp U hU V H δ ρ Λ hδ hA hΛδ hΛ1 y R hR hyR s r hs hsr hrR
  -- the tangent structure (sibling prerequisite)
  obtain ⟨hPm, -, hTS⟩ := Submission.lip_approx_tangent_structure n ℓ hn U hU V
  have hPae : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧
      V.tangentProj x = P.starProjection := hTS.mono fun x hx => hx.1
  -- `p_x` is `0` or an orthogonal projection, so `|v - p_x v| ≤ |v|`
  have hproj : ∀ (P : Submodule ℝ (Amb n ℓ)) (v : Amb n ℓ), ‖v - P.starProjection v‖ ≤ ‖v‖ := by
    intro P v
    have h0 : inner ℝ (v - P.starProjection v) (P.starProjection v) = 0 :=
      Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
    have h2 : ‖v‖ ^ 2 = ‖v - P.starProjection v‖ ^ 2 + ‖P.starProjection v‖ ^ 2 := by
      have := norm_add_sq_real (v - P.starProjection v) (P.starProjection v)
      rw [sub_add_cancel, h0] at this
      linarith only [this]
    have h3 : ‖v - P.starProjection v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [h2]; exact le_add_of_nonneg_right (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3
  have hPle : ∀ x v, ‖v - V.tangentProj x v‖ ≤ ‖v‖ := by
    intro x v
    unfold RectifiableVarifold.tangentProj
    split_ifs with h
    · exact hproj _ v
    · rw [zero_apply, sub_zero]
  have hA' := hA
  obtain ⟨hρ, hH, hθ, -, -, -, hK0⟩ := hA'
  -- constants
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := (zero_lt_one.trans_le hnR).trans hp
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp1p : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 - (n : ℝ) / p := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα, sub_pos, div_lt_one hp0]; exact hp
  have hexpα : (p - n) * (1 / p) = α := by rw [hα, mul_one_div, sub_div, div_self hp0.ne']
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (div_pos (mul_pos (mul_pos four_pos hp0) hδ) hpn) hΛδ
  have hκ0 : 0 ≤ (p - n) / (4 * p) := div_nonneg hpn.le (mul_nonneg zero_le_four hp0.le)
  have hδκ : δ ≤ (p - n) / (4 * p) * Λ := by
    rw [div_le_iff₀ hpn] at hΛδ
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos four_pos hp0)]
    linarith only [hΛδ]
  -- `B_t(z) ⊆ B_ρ(0)` gives `|z| + t ≤ ρ`
  have hgeom : ∀ (z : Amb n ℓ) (t : ℝ), 0 ≤ t → closedBall z t ⊆ closedBall 0 ρ →
      ‖z‖ + t ≤ ρ := by
    intro z t ht hsub
    by_cases hz : z = 0
    · have hne : (0 : ℕ) < n + ℓ := by omega
      have hv : ‖t • EuclideanSpace.single (⟨0, hne⟩ : Fin (n + ℓ)) (1 : ℝ)‖ = t := by
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
          abs_of_nonneg ht]
      have hmem := hsub (show t • EuclideanSpace.single (⟨0, hne⟩ : Fin (n + ℓ)) (1 : ℝ) ∈
          closedBall z t by rw [hz, mem_closedBall, dist_zero_right, hv])
      rw [mem_closedBall, dist_zero_right, hv] at hmem
      rw [hz, norm_zero, zero_add]; exact hmem
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hmem : z + (t / ‖z‖) • z ∈ closedBall z t := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg ht hzn.le), div_mul_cancel₀ _ hzn.ne']
      have h1 := hsub hmem
      rw [mem_closedBall, dist_zero_right] at h1
      have heq : z + (t / ‖z‖) • z = (1 + t / ‖z‖) • z := by rw [add_smul, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg zero_le_one (div_nonneg ht hzn.le))] at h1
      have h2 : (1 + t / ‖z‖) * ‖z‖ = ‖z‖ + t := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hzn.ne']
      linarith only [h1, h2]
  have hsubρ : ∀ (x : Amb n ℓ) (t : ℝ), ‖x‖ + t ≤ ρ → closedBall x t ⊆ closedBall 0 ρ := by
    intro x t h v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    rw [mem_closedBall, dist_zero_right]
    calc ‖v‖ = ‖(v - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ρ := by linarith only [hv, h]
  have hnorm_tri : ∀ x : Amb n ℓ, ‖x‖ ≤ ‖x - y‖ + ‖y‖ := fun x => by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  -- the curvature hypothesis in the form used by the core estimate
  have hLconv : ∀ (z : Amb n ℓ) (Rz k : ℝ), 0 < Rz → 0 ≤ k →
      V.scaledLpNorm H p z Rz ≤ ENNReal.ofReal k →
      (∫⁻ x in closedBall z Rz, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤
        ENNReal.ofReal (k / Rz ^ α) := by
    intro z Rz k hRz hk hK
    unfold RectifiableVarifold.scaledLpNorm at hK
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp1p,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hRz.le _) hp1p, ← Real.rpow_mul hRz.le,
      hexpα] at hK
    have hpos : 0 < Rz ^ α := Real.rpow_pos_of_pos hRz α
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr hpos).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hK
  -- `K(z, t) ≤ (t/ρ)^α δ` on sub-balls
  have hscaled : ∀ (z : Amb n ℓ) (t : ℝ), 0 < t → closedBall z t ⊆ closedBall 0 ρ →
      V.scaledLpNorm H p z t ≤ ENNReal.ofReal ((t / ρ) ^ α * δ) := by
    intro z t ht hsub
    have hK0' : (ENNReal.ofReal (ρ ^ (p - n)) *
        ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤ ENNReal.ofReal δ := hK0
    unfold RectifiableVarifold.scaledLpNorm
    have htρ : 0 ≤ t / ρ := div_nonneg ht.le hρ.le
    calc (ENNReal.ofReal (t ^ (p - n)) * ∫⁻ x in closedBall z t, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)
        ≤ (ENNReal.ofReal ((t / ρ) ^ (p - n)) * (ENNReal.ofReal (ρ ^ (p - n)) *
            ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight)) ^ (1 / p) := by
          apply ENNReal.rpow_le_rpow _ hp1p
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg htρ _),
            ← Real.mul_rpow htρ hρ.le, div_mul_cancel₀ _ hρ.ne']
          exact mul_le_mul' le_rfl (lintegral_mono_set hsub)
      _ = ENNReal.ofReal ((t / ρ) ^ α) * (ENNReal.ofReal (ρ ^ (p - n)) *
            ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp1p,
            ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg htρ _) hp1p,
            ← Real.rpow_mul htρ, hexpα]
      _ ≤ ENNReal.ofReal ((t / ρ) ^ α) * ENNReal.ofReal δ := mul_le_mul' le_rfl hK0'
      _ = ENNReal.ofReal ((t / ρ) ^ α * δ) := (ENNReal.ofReal_mul (Real.rpow_nonneg htρ _)).symm
  -- elementary exponential bounds
  have hexpb : ∀ x : ℝ, 0 ≤ x → Real.exp x - 1 ≤ x * Real.exp x := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
    have h2 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [h2] at h
    linarith only [h]
  -- the core estimate at `y`, radius `R`
  have hyRρ := hgeom y R hR.le hyR
  have hRρ : R ≤ ρ := by linarith only [hyRρ, norm_nonneg y]
  obtain ⟨hyU, -, hyK, hymass⟩ := aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y R hR hRρ hyR
  have hyfin : V.weight (closedBall y R) < ⊤ := hymass.trans_lt ENNReal.ofReal_lt_top
  have hyL := hLconv y R ((p - n) / (4 * p) * Λ) hR (mul_nonneg hκ0 hΛ0.le)
    (hyK.trans (ENNReal.ofReal_le_ofReal hδκ))
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Λ / (2 * R ^ α) := ⟨_, rfl⟩
  have hcore_y : ∀ s' r' : ℝ, 0 < s' → s' ≤ r' → r' < R →
      Real.exp (c * s' ^ α) * (1 + V.weight.real (closedBall y s') / s' ^ n) ≤
        Real.exp (c * r' ^ α) * (1 + V.weight.real (closedBall y r') / r' ^ n) ∧
      Real.exp (-(c * r' ^ α)) * (1 + V.weight.real (closedBall y r') / r' ^ n) ≤
        Real.exp (-(c * s' ^ α)) * (1 + V.weight.real (closedBall y s') / s' ^ n) +
        ∫ x in closedBall y r' \ closedBall y s',
          ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight :=
    fun s' r' hs' hsr' hrR' => hcore hn p hp U V H hH hPae hPm hPle y R Λ hR hΛ0.le hyU hyfin
      α c hα hc hyL s' r' hs' hsr' hrR'
  have hc0' : ∀ t, 0 < t → 0 ≤ c * t ^ α := fun t ht => by
    rw [hc]
    exact mul_nonneg (div_nonneg hΛ0.le (mul_nonneg zero_le_two (Real.rpow_nonneg hR.le α)))
      (Real.rpow_nonneg ht.le α)
  have hcle : ∀ t, 0 < t → t ≤ R → c * t ^ α ≤ Λ / 2 := by
    intro t ht htR
    rw [hc]
    have h1 : t ^ α ≤ R ^ α := Real.rpow_le_rpow ht.le htR hα0.le
    have h2 : 0 < R ^ α := Real.rpow_pos_of_pos hR α
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos two_pos h2)]
    calc Λ * t ^ α ≤ Λ * R ^ α := mul_le_mul_of_nonneg_left h1 hΛ0.le
      _ = Λ / 2 * (2 * R ^ α) := by ring
  have hMs0 : 0 ≤ V.weight.real (closedBall y s) / s ^ n :=
    div_nonneg measureReal_nonneg (pow_pos hs n).le
  have hMr0 : 0 ≤ V.weight.real (closedBall y r) / r ^ n :=
    div_nonneg measureReal_nonneg (pow_pos (hs.trans_le hsr) n).le
  have hD0 : 0 ≤ ∫ x in closedBall y r \ closedBall y s,
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight :=
    setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
      (fun x _ => div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))
  have hr0 : 0 < r := hs.trans_le hsr
  obtain ⟨h1, h2⟩ := hcore_y s r hs hsr hrR
  have hE := Real.exp_pos (Λ / 2)
  have hE1 : Real.exp (Λ / 2) ≤ Real.exp (2 * Λ) := Real.exp_le_exp.mpr (by linarith only [hΛ0])
  have hΛ2 : 0 ≤ Λ / 2 := div_nonneg hΛ0.le zero_le_two
  have hEb : Real.exp (Λ / 2) - 1 ≤ 2 * Real.exp Λ * Λ := by
    have h3 := hexpb (Λ / 2) hΛ2
    have h4 : Real.exp (Λ / 2) ≤ Real.exp Λ := Real.exp_le_exp.mpr (by linarith only [hΛ0])
    have h5 := mul_le_mul_of_nonneg_left h4 hΛ2
    have h6 := mul_nonneg hΛ0.le (Real.exp_pos Λ).le
    linarith only [h3, h5, h6]
  have hcr : Real.exp (c * r ^ α) ≤ Real.exp (Λ / 2) := Real.exp_le_exp.mpr (hcle r hr0 hrR.le)
  have hcs1 : 1 ≤ Real.exp (c * s ^ α) := Real.one_le_exp_iff.mpr (hc0' s hs)
  refine ⟨?_, ?_, ?_⟩
  · -- (I)
    generalize V.weight.real (closedBall y s) / s ^ n = Ms at h1 hMs0 ⊢
    generalize V.weight.real (closedBall y r) / r ^ n = Mr at h1 hMr0 ⊢
    have h5 : 1 + Ms ≤ Real.exp (Λ / 2) * (1 + Mr) := by
      calc 1 + Ms ≤ Real.exp (c * s ^ α) * (1 + Ms) :=
            le_mul_of_one_le_left (by linarith only [hMs0]) hcs1
        _ ≤ Real.exp (c * r ^ α) * (1 + Mr) := h1
        _ ≤ Real.exp (Λ / 2) * (1 + Mr) :=
            mul_le_mul_of_nonneg_right hcr (by linarith only [hMr0])
    linarith only [h5, mul_le_mul_of_nonneg_right hE1 hMr0, hEb]
  · -- (II)
    have hs1 : Real.exp (-(c * s ^ α)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hc0' s hs))
    have h6 : Real.exp (c * r ^ α) * Real.exp (-(c * r ^ α)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    generalize V.weight.real (closedBall y s) / s ^ n = Ms at h2 hMs0 ⊢
    generalize V.weight.real (closedBall y r) / r ^ n = Mr at h2 hMr0 ⊢
    generalize (∫ x in closedBall y r \ closedBall y s,
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight) = D at h2 hD0 ⊢
    have h5 : 1 + Mr ≤ Real.exp (Λ / 2) * ((1 + Ms) + D) := by
      calc 1 + Mr = Real.exp (c * r ^ α) * (Real.exp (-(c * r ^ α)) * (1 + Mr)) := by
            rw [← mul_assoc, h6, one_mul]
        _ ≤ Real.exp (c * r ^ α) * (Real.exp (-(c * s ^ α)) * (1 + Ms) + D) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ ≤ Real.exp (Λ / 2) * ((1 + Ms) + D) := by
            apply mul_le_mul hcr _ (add_nonneg (mul_nonneg (Real.exp_pos _).le
              (by linarith only [hMs0])) hD0) hE.le
            have := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 1 + Ms by linarith only [hMs0])
            linarith only [this]
    linarith only [h5, mul_le_mul_of_nonneg_right hE1 hMs0, mul_le_mul_of_nonneg_right hE1 hD0,
      hEb]
  · -- (III)
    intro hysupp
    have hymu : y ∈ V.weight.support := hysupp.2
    obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = unitBallVolume n := ⟨_, rfl⟩
    rw [← hω]
    have hω0 : 0 < ω := by
      rw [hω, unitBallVolume]
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos
        (add_pos_of_nonneg_of_pos (div_nonneg (Nat.cast_nonneg n) zero_le_two) one_pos))
    by_cases hωΛ : ω ≤ Λ
    · have : Real.exp (-Λ) * (ω - Λ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hωΛ)
      linarith only [this, hMs0]
    rw [not_le] at hωΛ
    -- lower density at `y`
    have hyρ : ‖y‖ < ρ := by linarith only [hyRρ, hR]
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℝ, τ₀ = (ρ - ‖y‖) / 4 := ⟨_, rfl⟩
    have hτ₀pos : 0 < τ₀ := by rw [hτ₀]; linarith only [hyρ]
    have hgood : ∀ᵐ x ∂V.weight, 1 ≤ V.mult x ∧ V.HasDensity x (V.mult x) :=
      (hθ.and hTS).mono fun x hx => ⟨hx.1, hx.2.2⟩
    have hlow : ∀ τ, 0 < τ → τ ≤ τ₀ →
        ω + 1 ≤ Real.exp (Λ * (2 * τ / ρ) ^ α / 2) *
          (1 + V.weight.real (closedBall y τ) / τ ^ n) := by
      intro τ hτ hττ₀
      obtain ⟨Λτ, hΛτ⟩ : ∃ Λτ : ℝ, Λτ = Λ * (2 * τ / ρ) ^ α := ⟨_, rfl⟩
      rw [← hΛτ]
      have h2τ : 0 < 2 * τ := by linarith only [hτ]
      have hΛτ0 : 0 ≤ Λτ := by
        rw [hΛτ]; exact mul_nonneg hΛ0.le (Real.rpow_nonneg (div_nonneg h2τ.le hρ.le) α)
      -- the estimate at density points `x` near `y`
      have hpt : ∀ x, ‖x - y‖ < τ → 1 ≤ V.mult x → V.HasDensity x (V.mult x) →
          ω + 1 ≤ Real.exp (Λτ / 2) * (1 + V.weight.real (closedBall x τ) / τ ^ n) := by
        intro x hxy hθx hdx
        have hxsub : closedBall x (2 * τ) ⊆ closedBall 0 ρ := by
          apply hsubρ
          have := hnorm_tri x
          rw [hτ₀] at hττ₀
          linarith only [this, hxy, hττ₀, hyρ]
        have h2τρ : 2 * τ ≤ ρ := by
          have := hgeom x (2 * τ) h2τ.le hxsub
          linarith only [this, norm_nonneg x]
        obtain ⟨hxU, -, -, hxmass⟩ :=
          aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA x (2 * τ) h2τ h2τρ hxsub
        have hxfin : V.weight (closedBall x (2 * τ)) < ⊤ := hxmass.trans_lt ENNReal.ofReal_lt_top
        have hxK : V.scaledLpNorm H p x (2 * τ) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λτ) := by
          refine (hscaled x (2 * τ) h2τ hxsub).trans (ENNReal.ofReal_le_ofReal ?_)
          rw [hΛτ]
          have : 0 ≤ (2 * τ / ρ) ^ α := Real.rpow_nonneg (div_nonneg h2τ.le hρ.le) α
          calc (2 * τ / ρ) ^ α * δ ≤ (2 * τ / ρ) ^ α * ((p - n) / (4 * p) * Λ) :=
                mul_le_mul_of_nonneg_left hδκ this
            _ = (p - n) / (4 * p) * (Λ * (2 * τ / ρ) ^ α) := by ring
        have hxL := hLconv x (2 * τ) _ h2τ (mul_nonneg hκ0 hΛτ0) hxK
        obtain ⟨cx, hcx⟩ : ∃ cx : ℝ, cx = Λτ / (2 * (2 * τ) ^ α) := ⟨_, rfl⟩
        have hxcore : ∀ t, 0 < t → t ≤ τ → 1 + V.weight.real (closedBall x t) / t ^ n ≤
            Real.exp (Λτ / 2) * (1 + V.weight.real (closedBall x τ) / τ ^ n) := by
          intro t ht htτ
          have hcc := (hcore hn p hp U V H hH hPae hPm hPle x (2 * τ) Λτ h2τ hΛτ0 hxU hxfin α
            cx hα hcx hxL t τ ht htτ (by linarith only [hτ])).1
          have hcx0 : 0 ≤ cx * t ^ α := by
            rw [hcx]
            exact mul_nonneg (div_nonneg hΛτ0 (mul_nonneg zero_le_two
              (Real.rpow_nonneg h2τ.le α))) (Real.rpow_nonneg ht.le α)
          have hcxτ : cx * τ ^ α ≤ Λτ / 2 := by
            rw [hcx]
            have h1 : τ ^ α ≤ (2 * τ) ^ α :=
              Real.rpow_le_rpow hτ.le (by linarith only [hτ]) hα0.le
            have h2 : 0 < (2 * τ) ^ α := Real.rpow_pos_of_pos h2τ α
            rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos two_pos h2)]
            calc Λτ * τ ^ α ≤ Λτ * (2 * τ) ^ α := mul_le_mul_of_nonneg_left h1 hΛτ0
              _ = Λτ / 2 * (2 * (2 * τ) ^ α) := by ring
          have hM0 : 0 ≤ V.weight.real (closedBall x t) / t ^ n :=
            div_nonneg measureReal_nonneg (pow_pos ht n).le
          calc 1 + V.weight.real (closedBall x t) / t ^ n
              ≤ Real.exp (cx * t ^ α) * (1 + V.weight.real (closedBall x t) / t ^ n) :=
                le_mul_of_one_le_left (by linarith only [hM0]) (Real.one_le_exp_iff.mpr hcx0)
            _ ≤ Real.exp (cx * τ ^ α) * (1 + V.weight.real (closedBall x τ) / τ ^ n) := hcc
            _ ≤ Real.exp (Λτ / 2) * (1 + V.weight.real (closedBall x τ) / τ ^ n) :=
                mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcxτ)
                  (add_nonneg zero_le_one (div_nonneg measureReal_nonneg (pow_pos hτ n).le))
        -- pass to the density `θ(x) ≥ 1`
        obtain ⟨Cτ, hCτ⟩ : ∃ Cτ : ℝ,
            Cτ = Real.exp (Λτ / 2) * (1 + V.weight.real (closedBall x τ) / τ ^ n) := ⟨_, rfl⟩
        rw [← hCτ]
        have hC1 : 1 ≤ Cτ := by
          have := hxcore τ hτ le_rfl
          have hM0 : 0 ≤ V.weight.real (closedBall x τ) / τ ^ n :=
            div_nonneg measureReal_nonneg (pow_pos hτ n).le
          rw [← hCτ] at this
          linarith only [this, hM0]
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), V.weight (closedBall x t) /
            ENNReal.ofReal (unitBallVolume n * t ^ n) ≤ ENNReal.ofReal ((Cτ - 1) / ω) := by
          filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
          have hb := hxcore t ht.1 ht.2.le
          rw [← hCτ] at hb
          have hfint : V.weight (closedBall x t) ≠ ⊤ :=
            ((measure_mono (closedBall_subset_closedBall (by linarith only [ht.2, hτ]))).trans_lt
              hxfin).ne
          have htn : 0 < t ^ n := pow_pos ht.1 n
          rw [← hω, ← ofReal_measureReal hfint, ← ENNReal.ofReal_div_of_pos (mul_pos hω0 htn)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_div_iff₀ (mul_pos hω0 htn) hω0]
          have : V.weight.real (closedBall x t) / t ^ n ≤ Cτ - 1 := by linarith only [hb]
          rw [div_le_iff₀ htn] at this
          calc V.weight.real (closedBall x t) * ω ≤ (Cτ - 1) * t ^ n * ω :=
                mul_le_mul_of_nonneg_right this hω0.le
            _ = (Cτ - 1) * (ω * t ^ n) := by ring
        have hlim := le_of_tendsto hdx hev
        rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg (sub_nonneg.mpr hC1) hω0.le),
          le_div_iff₀ hω0] at hlim
        have := mul_le_mul_of_nonneg_right hθx hω0.le
        linarith only [hlim, this]
      -- move from density points to `y`
      have hstep : ∀ η, 0 < η → η < τ → ω + 1 ≤ Real.exp (Λτ / 2) *
          (1 + V.weight.real (closedBall y (τ + η)) / τ ^ n) := by
        intro η hη hητ
        obtain ⟨x, hxy, hθx, hdx⟩ : ∃ x, ‖x - y‖ < η ∧ 1 ≤ V.mult x ∧
            V.HasDensity x (V.mult x) := by
          by_contra hcon
          simp only [not_exists, not_and] at hcon
          have hpos := (Measure.mem_support_iff_forall y).mp hymu (ball y η) (ball_mem_nhds y hη)
          have hnull : V.weight (ball y η) = 0 := by
            apply measure_mono_null _ (ae_iff.mp hgood)
            intro x hx
            rw [mem_ball, dist_eq_norm] at hx
            exact fun h => hcon x hx h.1 h.2
          rw [hnull] at hpos
          exact lt_irrefl _ hpos
        have h := hpt x (hxy.trans hητ) hθx hdx
        have hsub : closedBall x τ ⊆ closedBall y (τ + η) := by
          intro v hv
          rw [mem_closedBall, dist_eq_norm] at hv ⊢
          calc ‖v - y‖ = ‖(v - x) + (x - y)‖ := by congr 1; abel
            _ ≤ ‖v - x‖ + ‖x - y‖ := norm_add_le _ _
            _ ≤ τ + η := add_le_add hv hxy.le
        have hyτη : closedBall y (τ + η) ⊆ closedBall 0 ρ := by
          apply hsubρ
          rw [hτ₀] at hττ₀
          linarith only [hητ, hττ₀, hyρ]
        have hfin' : V.weight (closedBall y (τ + η)) ≠ ⊤ :=
          ((measure_mono hyτη).trans_lt ((aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA 0 ρ hρ
            le_rfl le_rfl).2.2.2.trans_lt ENNReal.ofReal_lt_top)).ne
        have hmono : V.weight.real (closedBall x τ) ≤ V.weight.real (closedBall y (τ + η)) :=
          measureReal_mono hsub hfin'
        calc ω + 1 ≤ _ := h
          _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right hmono
              (pow_pos hτ n).le) 1) (Real.exp_pos _).le
      -- `η → 0`
      have hfin2 : V.weight (closedBall y (2 * τ)) < ⊤ := by
        have hyτη : closedBall y (2 * τ) ⊆ closedBall 0 ρ := by
          apply hsubρ
          rw [hτ₀] at hττ₀
          linarith only [hττ₀, hyρ]
        exact (measure_mono hyτη).trans_lt ((aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA 0 ρ
          hρ le_rfl le_rfl).2.2.2.trans_lt ENNReal.ofReal_lt_top)
      have hshift : Tendsto (fun η : ℝ => τ + η) (𝓝[>] 0) (𝓝[>] τ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun η : ℝ => τ + η) (𝓝 0) (𝓝 (τ + 0)) :=
            (continuous_const.add continuous_id).tendsto 0
          rw [add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with η hη
          show τ < τ + η
          have : (0 : ℝ) < η := hη
          linarith only [this]
      have hT := (hball_rc V.weight y τ (2 * τ) (by linarith only [hτ]) hfin2).comp hshift
      exact ge_of_tendsto (((hT.div_const (τ ^ n)).const_add 1).const_mul (Real.exp (Λτ / 2)))
        (by filter_upwards [Ioo_mem_nhdsGT hτ] with η hη; exact hstep η hη.1 hη.2)
    -- (H3): `(1 - ε) ω uⁿ ≤ μ(B_u(y))` for small `u`
    have hH3 : ∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[>] (0 : ℝ),
        (1 - ε) * (ω * u ^ n) ≤ V.weight.real (closedBall y u) := by
      intro ε hε
      have hg : Tendsto (fun u : ℝ => (ω + 1) * Real.exp (-(Λ * (2 * u / ρ) ^ α / 2)) - 1)
          (𝓝[>] 0) (𝓝 ω) := by
        have hc : ContinuousAt
            (fun u : ℝ => (ω + 1) * Real.exp (-(Λ * (2 * u / ρ) ^ α / 2)) - 1) 0 :=
          (continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
            (((continuousAt_const.mul (((continuousAt_const.mul continuousAt_id).div_const
              ρ).rpow_const (Or.inr hα0.le))).div_const 2).neg))).sub continuousAt_const
        have h := hc.tendsto
        simp only [mul_zero, zero_div, Real.zero_rpow hα0.ne', neg_zero, Real.exp_zero, mul_one,
          add_sub_cancel_right] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hlt : (1 - ε) * ω < ω := by linarith only [mul_pos hε hω0]
      filter_upwards [hg.eventually (lt_mem_nhds hlt), Ioo_mem_nhdsGT hτ₀pos] with u hu hu0
      have hl := hlow u hu0.1 hu0.2.le
      have hexpi : Real.exp (-(Λ * (2 * u / ρ) ^ α / 2)) * Real.exp (Λ * (2 * u / ρ) ^ α / 2) =
          1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h1 := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-(Λ * (2 * u / ρ) ^ α / 2))).le
      rw [← mul_assoc, hexpi, one_mul] at h1
      have hun : 0 < u ^ n := pow_pos hu0.1 n
      have h3 : (1 - ε) * ω < V.weight.real (closedBall y u) / u ^ n := by
        linarith only [hu, h1]
      rw [lt_div_iff₀ hun] at h3
      calc (1 - ε) * (ω * u ^ n) = (1 - ε) * ω * u ^ n := by ring
        _ ≤ _ := h3.le
    -- (H1): `|F(u) - 1| ≤ Λ (u/s)^α`
    have hH1 : ∀ u : ℝ, 0 < u → u ≤ s → |Real.exp (c * u ^ α) - 1| ≤ Λ * (u / s) ^ α := by
      intro u hu hus
      have hx0 : 0 ≤ c * u ^ α := hc0' u hu
      have hx1 : c * u ^ α ≤ Λ / 2 := hcle u hu (hus.trans (hsr.trans hrR.le))
      rw [abs_of_nonneg (by linarith only [Real.add_one_le_exp (c * u ^ α), hx0])]
      have h2 : Real.exp (c * u ^ α) ≤ 2 := by
        have h3 : Real.exp (c * u ^ α) ≤ Real.exp (1 / 2) :=
          Real.exp_le_exp.mpr (by linarith only [hx1, hΛ1])
        have h4 := Real.exp_bound_div_one_sub_of_interval' (one_half_pos : (0 : ℝ) < 1 / 2)
          one_half_lt_one
        have h5 : (1 : ℝ) / (1 - 1 / 2) = 2 := by rw [sub_half, one_div_one_div]
        linarith only [h3, h4, h5]
      have h4 : 2 * (c * u ^ α) ≤ Λ * (u / s) ^ α := by
        rw [hc, Real.div_rpow hu.le hs.le]
        have hRs : s ^ α ≤ R ^ α := Real.rpow_le_rpow hs.le (hsr.trans hrR.le) hα0.le
        have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs α
        have hRpos : 0 < R ^ α := Real.rpow_pos_of_pos hR α
        calc 2 * (Λ / (2 * R ^ α) * u ^ α) = Λ * u ^ α / R ^ α := by
              rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]
          _ ≤ Λ * u ^ α / s ^ α :=
              div_le_div_of_nonneg_left (mul_nonneg hΛ0.le (Real.rpow_nonneg hu.le α)) hspos hRs
          _ = Λ * (u ^ α / s ^ α) := mul_div_assoc _ _ _
      calc Real.exp (c * u ^ α) - 1 ≤ c * u ^ α * Real.exp (c * u ^ α) := hexpb _ hx0
        _ ≤ c * u ^ α * 2 := mul_le_mul_of_nonneg_left h2 hx0
        _ = 2 * (c * u ^ α) := mul_comm _ _
        _ ≤ _ := h4
    -- (H2): monotonicity of `F(u) (m(u)/uⁿ) + (F(u) - 1)`
    have hH2 : ∀ u t : ℝ, 0 < u → u ≤ t → t ≤ s →
        Real.exp (c * u ^ α) * (V.weight.real (closedBall y u) / u ^ n) +
            (Real.exp (c * u ^ α) - 1) ≤
          Real.exp (c * t ^ α) * (V.weight.real (closedBall y t) / t ^ n) +
            (Real.exp (c * t ^ α) - 1) := by
      intro u t hu hut hts
      have h := (hcore_y u t hu hut (hts.trans_lt (hsr.trans_lt hrR))).1
      linarith only [h]
    have hres := aal_monotone_quantity_ge_density n α ω s Λ
      (fun u => V.weight.real (closedBall y u)) (fun u => Real.exp (c * u ^ α)) hα0 hω0 hs hH1
      hH2 hH3 s hs le_rfl
    -- final algebra
    have hFs2 : Real.exp (c * s ^ α) ≤ Real.exp (Λ / 2) :=
      Real.exp_le_exp.mpr (hcle s hs (hsr.trans hrR.le))
    have hE2 : Real.exp (Λ / 2) ≤ 1 + Λ := by
      have h1 := Real.exp_bound_div_one_sub_of_interval' (by linarith only [hΛ0] : 0 < Λ / 2)
        (by linarith only [hΛ1])
      have h2 : 1 / (1 - Λ / 2) ≤ 1 + Λ := by
        rw [div_le_iff₀ (by linarith only [hΛ1])]
        have := mul_le_mul_of_nonneg_left hΛ1 hΛ0.le
        linarith only [this]
      linarith only [h1, h2]
    have hE1 : 1 ≤ Real.exp (Λ / 2) := Real.one_le_exp_iff.mpr (by linarith only [hΛ0])
    have hω1 : ω + 1 ≤ Real.exp (Λ / 2) * (1 + V.weight.real (closedBall y s) / s ^ n) := by
      have := mul_le_mul_of_nonneg_right hFs2
        (show 0 ≤ 1 + V.weight.real (closedBall y s) / s ^ n by linarith only [hMs0])
      linarith only [hres, this]
    have hexpΛ : Real.exp Λ = Real.exp (Λ / 2) * Real.exp (Λ / 2) := by
      rw [← Real.exp_add, add_halves]
    have hinv : Real.exp (-Λ) * Real.exp Λ = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hkey : ω - Λ ≤ Real.exp Λ * (V.weight.real (closedBall y s) / s ^ n) := by
      rw [hexpΛ]
      have h1 : Real.exp (Λ / 2) * (ω + 1 - Real.exp (Λ / 2)) ≤
          Real.exp (Λ / 2) * (Real.exp (Λ / 2) * (V.weight.real (closedBall y s) / s ^ n)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hω1]) (by linarith only [hE1])
      have h2 : Λ * (Real.exp (Λ / 2) - 1) ≤ ω * (Real.exp (Λ / 2) - 1) :=
        mul_le_mul_of_nonneg_right hωΛ.le (by linarith only [hE1])
      have h3 : 0 ≤ Real.exp (Λ / 2) * (1 + Λ - Real.exp (Λ / 2)) :=
        mul_nonneg (by linarith only [hE1]) (by linarith only [hE2])
      linarith only [h1, h2, h3]
    calc Real.exp (-Λ) * (ω - Λ)
        ≤ Real.exp (-Λ) * (Real.exp Λ * (V.weight.real (closedBall y s) / s ^ n)) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
      _ = V.weight.real (closedBall y s) / s ^ n := by rw [← mul_assoc, hinv, one_mul]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
