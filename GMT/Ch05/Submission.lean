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

/-- Steps 2–3 of the uniform difference-quotient bounds, for one function `g`: if `g` is `C¹` on
an open `U ⊇ K` with `K` compact and `D¹g = iteratedFDeriv ℝ 1 g` is `α`-Hölder on `K` with some
constant `C`, then `Dg = fderiv ℝ g` is bounded on `K` by some `S ≥ 0` and is `α`-Hölder on `K`
with some constant `H ≥ 0`.  (`D¹g(z)` is the image of `Dg(z)` under the linear isometry
`(continuousMultilinearCurryFin1 ℝ E F).symm`; no condition on `α` is needed.) -/
theorem dohr_eb_lhr_dqub_fderiv_consts : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U K : Set E) (g : E → F), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ C * ‖x - y‖ ^ α) → ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ S) ∧ ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U K g hU hK hKU hg hC
  obtain ⟨C, hC⟩ := hC
  -- Step 1: `D¹g(z) = Ψ(Dg(z))` for the linear isometry `Ψ = (continuousMultilinearCurryFin1 ℝ E F).symm`.
  have h1 : ∀ z, iteratedFDeriv ℝ 1 g z = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g z) := by
    intro z
    ext m
    simp [iteratedFDeriv_one_apply]
  -- Step 2: `‖Dg(x) − Dg(y)‖ = ‖Ψ(Dg(x) − Dg(y))‖ = ‖D¹g(x) − D¹g(y)‖`.
  have h2 : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ = ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ := by
    intro x y
    rw [h1 x, h1 y, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 3: `Dg` is continuous on the open `U ⊇ K`, hence bounded by some `S₀` on the compact `K`.
  obtain ⟨S₀, hS₀⟩ := hK.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: `S = max S₀ 0` and `H = max C 0`, using `‖x − y‖^α ≥ 0`.
  refine ⟨max S₀ 0, max C 0, le_max_right _ _, le_max_right _ _,
    fun x hx => (hS₀ x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  rw [h2 x y]
  exact (hC x hx y hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference-quotient bounds.**
Let `g` be differentiable on an open `U ⊇ B_{4R}(x̄)` with `‖Dg‖ ≤ S` and
`‖Dg(z) − Dg(w)‖ ≤ H ‖z − w‖^α` on `B_{4R}(x̄)`.  If `‖e‖ ≤ 1` and `0 < |d| < R`, then on
`B̆_{2R}(x̄)` the difference quotient `d⁻¹ (g(x + d e) − g(x))` is bounded by `S` and is
`α`-Hölder with constant `H`.
Proof: for `z ∈ B̆_{2R}(x̄)` and `|s| ≤ |d|`, `z + s e ∈ B_{4R}(x̄) ⊆ U`.  The mean value inequality
on this convex ball gives `‖g(x + d e) − g(x)‖ ≤ S |d|`.  For the second bound,
`h(s) = g(x + s e) − g(y + s e)` has `‖h'(s)‖ = ‖(Dg(x + s e) − Dg(y + s e)) e‖ ≤ H ‖x − y‖^α`
for `s` between `0` and `d`, so `‖h(d) − h(0)‖ ≤ H ‖x − y‖^α |d|`; divide by `|d|`. -/
theorem dohr_eb_lhr_dqub_dq_mean_value : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U : Set E) (g : E → F) (xb e : E) (R S H d : ℝ), IsOpen U → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → DifferentiableOn ℝ g U → (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ g z‖ ≤ S) → (∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R), ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ H * ‖z - w‖ ^ α) → d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖d⁻¹ • (g (x + d • e) - g x)‖ ≤ S ∧ ‖d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y)‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U g xb e R S H d hU hKU he hg hS hH hd hdR x hx y hy
  have hdpos : 0 < |d| := abs_pos.mpr hd
  -- Step 2: for `z ∈ ball xb (2 * R)` and `|s| ≤ |d|`, `z + s • e ∈ closedBall xb (4 * R)`.
  have hgeo : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖e‖ ≤ |d| * 1 := mul_le_mul hs he (norm_nonneg e) (abs_nonneg d)
        _ = |d| := mul_one _
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by congr 1; abel
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith [abs_nonneg d]
  -- Step 3: `g` is differentiable at every point of `closedBall xb (4 * R) ⊆ U`.
  have hdiff : ∀ z ∈ closedBall xb (4 * R), DifferentiableAt ℝ g z := fun z hz =>
    (hg z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  have hx0 : x ∈ closedBall xb (4 * R) := by
    have h := hgeo x hx 0 (by simp)
    rwa [zero_smul, add_zero] at h
  constructor
  · -- Step 4: part (a), the mean value inequality on `closedBall xb (4 * R)`.
    have hmv : ‖g (x + d • e) - g x‖ ≤ S * ‖x + d • e - x‖ :=
      (convex_closedBall xb (4 * R)).norm_image_sub_le_of_norm_fderiv_le hdiff hS hx0
        (hgeo x hx d le_rfl)
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx0)
    have hde : ‖d • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg d) he
    rw [add_sub_cancel_left] at hmv
    rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖g (x + d • e) - g x‖ ≤ S * ‖d • e‖ := hmv
      _ ≤ S * |d| := mul_le_mul_of_nonneg_left hde hS0
      _ = |d| * S := mul_comm _ _
  · -- Steps 5–8: part (b), the mean value inequality for `s ↦ g (x + s • e) - g (y + s • e)`.
    have hI : ∀ s ∈ uIcc (0 : ℝ) d, |s| ≤ |d| := by
      intro s hs
      simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hlin : ∀ (z : E) (s : ℝ), HasDerivAt (fun σ : ℝ => z + σ • e) e s := by
      intro z s
      simpa using ((hasDerivAt_id s).smul_const e).const_add z
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) d, HasDerivWithinAt
        (fun σ : ℝ => g (x + σ • e) - g (y + σ • e))
        (fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e) (uIcc (0 : ℝ) d) s := by
      intro s hs
      have hxs := hdiff _ (hgeo x hx s (hI s hs))
      have hys := hdiff _ (hgeo y hy s (hI s hs))
      exact ((hxs.hasFDerivAt.comp_hasDerivAt s (hlin x s)).sub
        (hys.hasFDerivAt.comp_hasDerivAt s (hlin y s))).hasDerivWithinAt
    have hbound : ∀ s ∈ uIcc (0 : ℝ) d,
        ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖ ≤ H * ‖x - y‖ ^ α := by
      intro s hs
      have hxy : x + s • e - (y + s • e) = x - y := add_sub_add_right_eq_sub x y (s • e)
      calc ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖
          = ‖(fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)) e‖ := by rw [sub_apply]
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) he
        _ ≤ H * ‖x + s • e - (y + s • e)‖ ^ α :=
            hH _ (hgeo x hx s (hI s hs)) _ (hgeo y hy s (hI s hs))
        _ = H * ‖x - y‖ ^ α := by rw [hxy]
    have hmv := (convex_uIcc (0 : ℝ) d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at hmv
    have hrw : d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y) =
        d⁻¹ • ((g (x + d • e) - g (y + d • e)) - (g x - g y)) := by
      rw [← smul_sub]; congr 1; abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖(g (x + d • e) - g (y + d • e)) - (g x - g y)‖ ≤ H * ‖x - y‖ ^ α * |d| := hmv
      _ = |d| * (H * ‖x - y‖ ^ α) := mul_comm _ _
/-- Difference-quotient bounds in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second
assertion (p. 127): on a finite-dimensional real normed space `L`, real linear and bilinear forms
are bounded by `C` times their largest value on finitely many test vectors `b r`.  Take a basis
`b` of `L`; its coordinates `π r` are continuous, and `c = Σ_r ‖π r‖` gives
`|b.repr P r| ≤ c ‖P‖`.  Expanding `P` in the basis gives `|f P| ≤ N c m ‖P‖`, expanding in both
arguments gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`, and `C = N c + N² c²`. -/
theorem dohr_eb_lhr_dqub_form_coords : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (b : Fin N → L) (C : ℝ), 0 ≤ C ∧ (∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) → ∀ P, |f P| ≤ C * m * ‖P‖) ∧ ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) → (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) → ∀ Q P, |β Q P| ≤ C * m * ‖Q‖ * ‖P‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` indexed by `Fin N` (`N = finrank ℝ L`).
  obtain ⟨N, ⟨b⟩⟩ : ∃ N : ℕ, Nonempty (Module.Basis (Fin N) ℝ L) :=
    ⟨_, ⟨Module.finBasis ℝ L⟩⟩
  -- Step 2: the coordinates `π r = b.coord r` are continuous as `L` is finite-dimensional, and
  -- `c = Σ_r ‖π r‖` gives `|b.repr P r| ≤ c ‖P‖`.
  obtain ⟨c, hc0, hcoord⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ r P, |b.repr P r| ≤ c * ‖P‖ := by
    let π : Fin N → L →L[ℝ] ℝ := fun r => LinearMap.toContinuousLinearMap (b.coord r)
    refine ⟨∑ r, ‖π r‖, Finset.sum_nonneg fun r _ => norm_nonneg _, fun r P => ?_⟩
    have hπ : π r P = b.repr P r := by simp [π]
    calc |b.repr P r| = ‖π r P‖ := by rw [hπ, Real.norm_eq_abs]
      _ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ (∑ t, ‖π t‖) * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun t _ => norm_nonneg (π t)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: a linear `f` is determined by its basis values, `f P = Σ_r b.repr P r · f (b r)`.
  have hexp : ∀ f : L → ℝ, IsLinearMap ℝ f → ∀ P, f P = ∑ r, b.repr P r * f (b r) := by
    intro f hf P
    calc f P = IsLinearMap.mk' f hf (∑ r, b.repr P r • b r) := by
          rw [b.sum_repr, IsLinearMap.mk'_apply]
      _ = ∑ r, b.repr P r * f (b r) := by
          simp only [map_sum, map_smul, IsLinearMap.mk'_apply, smul_eq_mul]
  -- Step 4: the linear bound `|f P| ≤ N c m ‖P‖`.
  have hlin : ∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) →
      ∀ P, |f P| ≤ N * c * m * ‖P‖ := by
    intro f m hf hm hb P
    rw [hexp f hf P]
    calc |∑ r, b.repr P r * f (b r)| ≤ ∑ r, |b.repr P r * f (b r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin N, c * ‖P‖ * m := by
          gcongr with r
          rw [abs_mul]
          exact mul_le_mul (hcoord r P) (hb r) (abs_nonneg _) (by positivity)
      _ = N * c * m * ‖P‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Steps 5–6: expanding `β` in each argument, i.e. the linear bound for each `β (b r)` and then
  -- for `Q ↦ β Q P`, gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`.
  have hbil : ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) →
      (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) →
      ∀ Q P, |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by
    intro β m hβ₁ hβ₂ hm hb Q P
    have hr : ∀ r, |β (b r) P| ≤ N * c * m * ‖P‖ := fun r =>
      hlin (β (b r)) m (hβ₂ (b r)) hm (hb r) P
    calc |β Q P| ≤ N * c * (N * c * m * ‖P‖) * ‖Q‖ :=
          hlin (fun Q => β Q P) (N * c * m * ‖P‖) (hβ₁ P) (by positivity) hr Q
      _ = N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by ring
  -- Step 7: `C = N c + N² c²` serves for both bounds.
  refine ⟨N, b, N * c + N * c * (N * c), by positivity, fun f m hf hm hb P => ?_,
    fun β m hβ₁ hβ₂ hm hb Q P => ?_⟩
  · calc |f P| ≤ N * c * m * ‖P‖ := hlin f m hf hm hb P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖P‖ := by
          rw [add_mul, add_mul]
          exact le_add_of_nonneg_right (by positivity)
  · calc |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := hbil β m hβ₁ hβ₂ hm hb Q P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖Q‖ * ‖P‖ := by
          rw [add_mul, add_mul, add_mul]
          exact le_add_of_nonneg_left (by positivity)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a locally
`C^{1,α}` map.**  Let `v` be locally `C^{1,α}` on the open set `U ⊇ B_{4R}(xb)` and `‖e‖ ≤ 1`.
There is `S` such that for every `0 < |d| < R` the difference quotient
`w_d(z) = d⁻¹ (v(z + d e) − v(z))` satisfies the following on `B̆_{2R}(xb)`: `‖w_d‖ ≤ S`, `w_d` is
`C¹`, `Dw_d(x) = d⁻¹ (Dv(x + d e) − Dv(x))`, and `Dw_d` is `α`-Hölder.
Proof: `dohr_eb_lhr_dqub_fderiv_consts` on the compact set `K₀ = B_{4R}(xb)` gives a bound `S_v`
and a Hölder constant `H_v` for `Dv` on `K₀`; put `S = S_v`.  For `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`,
`‖z + s e − xb‖ < 2R + R ≤ 4R`, so `z` and `z + d e` lie in `K₀ ⊆ U`.  The bound on `w_d` is part
(a) of `dohr_eb_lhr_dqub_dq_mean_value`.  The `C¹` property and the derivative formula follow from
the chain rule for the translation `z ↦ z + d e`.  Finally
`Dw_d(x) − Dw_d(y) = d⁻¹ ((Dv(x + d e) − Dv(y + d e)) − (Dv(x) − Dv(y)))` has norm at most
`2 H_v |d|⁻¹ ‖x − y‖^α`. -/
theorem dohr_eb_lhr_dqub_wd_props : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → IsLocallyHolderCkα 1 α v U → ∃ S : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ S) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ ∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α := by
  intro n ℓ α U v xb e R hU hR hsub he hv
  -- Step 1: `v` is `C¹` on `U`, and `D¹v` is `α`-Hölder on the compact set `K₀ = B_{4R}(xb) ⊆ U`.
  have hC1 : ContDiffOn ℝ 1 v U := by simpa using hv.1
  have hK0 : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  -- Step 2: `‖Dv‖ ≤ S_v` and `‖Dv(z) − Dv(w)‖ ≤ H_v ‖z − w‖^α` on `K₀`.  The constant
  -- `S := S_v` does not depend on `d`.
  obtain ⟨Sv, Hv, -, -, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U (closedBall xb (4 * R)) v hU hK0
      hsub hC1 (hv.2 _ hK0 hsub)
  refine ⟨Sv, fun d hd hdR => ?_⟩
  -- Step 3: `z + s e ∈ K₀` for `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`; in particular `z, z + d e ∈ K₀`.
  have hgeom : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg s) he).trans hs
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by rw [sub_add_eq_add_sub]
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith
  have hz0 : ∀ z ∈ ball xb (2 * R), z ∈ closedBall xb (4 * R) := fun z hz => by
    simpa using hgeom z hz 0 (by simp)
  have hzd : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := fun z hz =>
    hgeom z hz d le_rfl
  -- Step 4: claim (i) is part (a) of `dohr_eb_lhr_dqub_dq_mean_value` (taking `y = x`).
  have hdiff : DifferentiableOn ℝ v U := hC1.differentiableOn one_ne_zero
  have hmv := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) (Rn ℓ) α U v xb e R Sv Hv d hU hsub
    he hdiff hSv hHv hd hdR
  -- Step 6: `w_d` has derivative `d⁻¹ (Dv(x + d e) − Dv(x))` at every `x ∈ B̆_{2R}(xb)`.
  have hderiv : ∀ x ∈ ball xb (2 * R), HasFDerivAt (fun z => d⁻¹ • (v (z + d • e) - v z))
      (d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) x := by
    intro x hx
    have hxU : x ∈ U := hsub (hz0 x hx)
    have hxdU : x + d • e ∈ U := hsub (hzd x hx)
    have hv0 : DifferentiableAt ℝ v x := (hdiff x hxU).differentiableAt (hU.mem_nhds hxU)
    have hv1 : DifferentiableAt ℝ v (x + d • e) :=
      (hdiff _ hxdU).differentiableAt (hU.mem_nhds hxdU)
    have hcomp : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (x + d • e)) x := by
      simpa [Function.comp_def] using
        hv1.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))
    exact (hcomp.sub hv0.hasFDerivAt).const_smul d⁻¹
  refine ⟨fun x hx => (hmv x hx x hx).1, ?_, fun x hx => (hderiv x hx).fderiv, ?_⟩
  · -- Step 5: claim (ii), since `w_d = d⁻¹ • (v ∘ τ − v)` for the translation `τ z = z + d e`.
    have hτ : ContDiffOn ℝ 1 (fun z : Rn n => z + d • e) (ball xb (2 * R)) :=
      (contDiff_id.add contDiff_const).contDiffOn
    have hτU : MapsTo (fun z : Rn n => z + d • e) (ball xb (2 * R)) U := fun z hz =>
      hsub (hzd z hz)
    have h1 : ContDiffOn ℝ 1 (fun z => v (z + d • e)) (ball xb (2 * R)) := hC1.comp hτ hτU
    have h2 : ContDiffOn ℝ 1 v (ball xb (2 * R)) := hC1.mono fun z hz => hsub (hz0 z hz)
    exact (h1.sub h2).const_smul d⁻¹
  · -- Step 7: claim (iv) with `K = 2 H_v |d|⁻¹`, using the Hölder bound of `Dv` at the four points
    -- `x, y, x + d e, y + d e ∈ K₀`.
    refine ⟨2 * Hv * |d|⁻¹, fun x hx y hy => ?_⟩
    rw [(hderiv x hx).fderiv, (hderiv y hy).fderiv]
    have heq : d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) -
        d⁻¹ • (fderiv ℝ v (y + d • e) - fderiv ℝ v y) =
        d⁻¹ • ((fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)) :=
      (smul_sub _ _ _).symm.trans (by rw [sub_sub_sub_comm])
    have h1 := hHv _ (hzd x hx) _ (hzd y hy)
    rw [add_sub_add_right_eq_sub] at h1
    have h2 := hHv _ (hz0 x hx) _ (hz0 y hy)
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |d|⁻¹ * ‖(fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)‖
        ≤ |d|⁻¹ * (Hv * ‖x - y‖ ^ α + Hv * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
            (inv_nonneg.2 (abs_nonneg d))
      _ = 2 * Hv * |d|⁻¹ * ‖x - y‖ ^ α := by ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `d`-uniform Hölder bound for the
forcing term of the difference-quotient system.**  Let `L = L(ℝⁿ, ℝ^ℓ)`, `U ⊇ B_{4R}(xb)` open,
`‖e‖ ≤ 1`, let the coefficients `x ↦ a(x)[P][Q]` and `x ↦ Φ(x)[P]` be `C^{1,α}` in `U` and `v` be
`C^{1,α}` in `U`.  For `0 < |d| < R` put
`F_d(x, P) = d⁻¹ (Φ(x + d e)[P] − Φ(x)[P])
  − d⁻¹ (a(x + d e)[Dv(x + d e)][P] − a(x)[Dv(x + d e)][P])`.
Then `|F_d(x, P) − F_d(y, P)| ≤ M ‖x − y‖^α ‖P‖` on `B̆_{2R}(xb)` with `M` independent of `d`.
Proof: `dohr_eb_lhr_dqub_form_coords` gives a spanning family `b` of `L` and a constant `C`
bounding linear and bilinear forms by their values on `b`.  On `K₀ = B_{4R}(xb)`,
`dohr_eb_lhr_dqub_fderiv_consts` gives a common bound `S'` and a common Hölder constant `H` for
the derivatives of the scalar coefficients `a(·)[b_r][b_t]`, `Φ(·)[b_r]`, and `S_v`, `H_v` for
`Dv`; put `M = C (H + H S_v + S' H_v)`.  The mean value inequality
`dohr_eb_lhr_dqub_dq_mean_value` bounds the difference quotients of these coefficients by `S'`
and their differences at `x, y` by `H ‖x − y‖^α`.  With
`Q_x = Dv(x + d e)` and `Q_y = Dv(y + d e)`,
`F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)` for the linear form `T` and the
bilinear forms `β₁`, `β₂` built from these difference quotients, and the coordinate bounds give
`|T(P)| + |β₁(Q_x, P)| + |β₂(Q_x − Q_y, P)| ≤ M ‖x − y‖^α ‖P‖`. -/
theorem dohr_eb_lhr_dqub_forcing_holder : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R hU hR hK0U he ha hΦ hv
  -- Step 1: a spanning family `b` of `L` and the coordinate constant `C`.
  obtain ⟨N, b, C, hC, hD1, hD2⟩ :=
    Submission.dohr_eb_lhr_dqub_form_coords (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: derivative bounds and Hölder constants of the components on `K₀ = B_{4R}(xb)`.
  have hK0c : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  have hAa : ∀ r t : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => a z (b r) (b t)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => a z (b r) (b t)) z - fderiv ℝ (fun z => a z (b r) (b t)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r t =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => a z (b r) (b t)) hU hK0c
      hK0U (ha (b r) (b t)).1 ((ha (b r) (b t)).2 _ hK0c hK0U)
  have hAΦ : ∀ r : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => Φ z (b r)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => Φ z (b r)) z - fderiv ℝ (fun z => Φ z (b r)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => Φ z (b r)) hU hK0c
      hK0U (hΦ (b r)).1 ((hΦ (b r)).2 _ hK0c hK0U)
  obtain ⟨Sv, Hv, hSv0, hHv0, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U _ v hU hK0c hK0U
      (by simpa using hv.1) (hv.2 _ hK0c hK0U)
  choose Sa Ha hSa0 hHa0 hSa hHa using hAa
  choose SΦ HΦ hSΦ0 hHΦ0 hSΦ hHΦ using hAΦ
  -- Step 3: uniform constants `S'`, `H` for all components; `M` is fixed before `d`.
  set S' : ℝ := ∑ r, ∑ t, Sa r t + ∑ r, SΦ r
  set H : ℝ := ∑ r, ∑ t, Ha r t + ∑ r, HΦ r
  have hSa_sum0 : 0 ≤ ∑ r, ∑ t, Sa r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t
  have hHa_sum0 : 0 ≤ ∑ r, ∑ t, Ha r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t
  have hSΦ_sum0 : 0 ≤ ∑ r, SΦ r := Finset.sum_nonneg fun r _ => hSΦ0 r
  have hHΦ_sum0 : 0 ≤ ∑ r, HΦ r := Finset.sum_nonneg fun r _ => hHΦ0 r
  have hS'0 : 0 ≤ S' := add_nonneg hSa_sum0 hSΦ_sum0
  have hH0 : 0 ≤ H := add_nonneg hHa_sum0 hHΦ_sum0
  have hSa_le : ∀ r t, Sa r t ≤ S' := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hSa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Sa r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hSΦ_sum0))
  have hHa_le : ∀ r t, Ha r t ≤ H := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hHa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Ha r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hHΦ_sum0))
  have hSΦ_le : ∀ r, SΦ r ≤ S' := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hSΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hSa_sum0)
  have hHΦ_le : ∀ r, HΦ r ≤ H := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hHΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hHa_sum0)
  refine ⟨C * (H + H * Sv + S' * Hv), ?_⟩
  intro d hd hdR x hx y hy P
  -- Step 4: `x + d e, y + d e ∈ K₀`, and the bounds on `Q_x = Dv(x + d e)`, `Q_y = Dv(y + d e)`.
  have hshift : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := by
    intro z hz
    rw [mem_closedBall]
    rw [mem_ball] at hz
    have h1 : dist (z + d • e) xb ≤ dist z xb + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖z + d • e - xb‖ = ‖(z - xb) + d • e‖ := by congr 1; abel
        _ ≤ ‖z - xb‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
        _ ≤ R := by linarith
    linarith
  have hxK := hshift x hx
  have hyK := hshift y hy
  set t : ℝ := ‖x - y‖ ^ α
  have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) α
  set Qx := fderiv ℝ v (x + d • e)
  set Qy := fderiv ℝ v (y + d • e)
  have hQxb : ‖Qx‖ ≤ Sv := hSv _ hxK
  have hQxy : ‖Qx - Qy‖ ≤ Hv * t := by
    have := hHv _ hxK _ hyK
    rwa [add_sub_add_right_eq_sub] at this
  -- Step 5: the scalar difference quotients of the components, by the mean value inequality
  -- `dohr_eb_lhr_dqub_dq_mean_value` with the common constants `S'` and `H`.
  have hBa : ∀ r t', |d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ S' ∧
      |d⁻¹ * (a (x + d • e) (b r) (b t') - a x (b r) (b t')) -
        d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ H * t := by
    intro r t'
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => a z (b r) (b t')) xb e R S' H d hU hK0U he
      ((ha (b r) (b t')).1.differentiableOn one_ne_zero)
      (fun z hz => (hSa r t' z hz).trans (hSa_le r t'))
      (fun z hz w hw => (hHa r t' z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHa_le r t') (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    refine ⟨?_, ?_⟩
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB y hy y hy).1
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  have hBΦ : ∀ r, |d⁻¹ * (Φ (x + d • e) (b r) - Φ x (b r)) -
      d⁻¹ * (Φ (y + d • e) (b r) - Φ y (b r))| ≤ H * t := by
    intro r
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => Φ z (b r)) xb e R S' H d hU hK0U he
      ((hΦ (b r)).1.differentiableOn one_ne_zero)
      (fun z hz => (hSΦ r z hz).trans (hSΦ_le r))
      (fun z hz w hw => (hHΦ r z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHΦ_le r) (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  -- Step 6: the linear form `T` and the bilinear forms `β₁`, `β₂`.
  let T : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P' =>
    d⁻¹ * (Φ (x + d • e) P' - Φ x P') - d⁻¹ * (Φ (y + d • e) P' - Φ y P')
  let β1 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (x + d • e) Q P' - a x Q P') - d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  let β2 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  have hTlin : IsLinearMap ℝ T := by
    constructor
    · intro P1 P2; simp only [T, map_add]; ring
    · intro c P1; simp only [T, map_smul, smul_eq_mul]; ring
  have hβ1l : ∀ P', IsLinearMap ℝ (fun Q => β1 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β1, map_add, add_apply]; ring
    · intro c Q1; simp only [β1, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ1r : ∀ Q, IsLinearMap ℝ (β1 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β1, map_add]; ring
    · intro c P1; simp only [β1, map_smul, smul_eq_mul]; ring
  have hβ2l : ∀ P', IsLinearMap ℝ (fun Q => β2 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β2, map_add, add_apply]; ring
    · intro c Q1; simp only [β2, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ2r : ∀ Q, IsLinearMap ℝ (β2 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β2, map_add]; ring
    · intro c P1; simp only [β2, map_smul, smul_eq_mul]; ring
  -- Step 7: coordinate bounds for `T(P)`, `β₁(Q_x, P)` and `β₂(Q_x − Q_y, P)`.
  have hT : |T P| ≤ C * (H * t) * ‖P‖ :=
    hD1 T (H * t) hTlin (mul_nonneg hH0 ht0) (fun r => hBΦ r) P
  have hβ1 : |β1 Qx P| ≤ C * (H * t) * ‖Qx‖ * ‖P‖ :=
    hD2 β1 (H * t) hβ1l hβ1r (mul_nonneg hH0 ht0) (fun r t' => (hBa r t').2) Qx P
  have hβ2 : |β2 (Qx - Qy) P| ≤ C * S' * ‖Qx - Qy‖ * ‖P‖ :=
    hD2 β2 S' hβ2l hβ2r hS'0 (fun r t' => (hBa r t').1) (Qx - Qy) P
  -- Step 8: `F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)`.
  have hid : (d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) Qx P - a x Qx P)) -
      (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) Qy P - a y Qy P)) =
      T P - β1 Qx P - β2 (Qx - Qy) P := by
    simp only [T, β1, β2, map_sub, sub_apply]; ring
  -- Step 9: the triangle inequality.
  rw [hid]
  have hP0 : 0 ≤ ‖P‖ := norm_nonneg P
  have hCH : 0 ≤ C * (H * t) := mul_nonneg hC (mul_nonneg hH0 ht0)
  have hCS : 0 ≤ C * S' := mul_nonneg hC hS'0
  have e1 : |β1 Qx P| ≤ C * (H * t) * Sv * ‖P‖ :=
    hβ1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxb hCH) hP0)
  have e2 : |β2 (Qx - Qy) P| ≤ C * S' * (Hv * t) * ‖P‖ :=
    hβ2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxy hCS) hP0)
  calc |T P - β1 Qx P - β2 (Qx - Qy) P|
      ≤ |T P - β1 Qx P| + |β2 (Qx - Qy) P| := abs_sub _ _
    _ ≤ |T P| + |β1 Qx P| + |β2 (Qx - Qy) P| := by
        gcongr; exact abs_sub _ _
    _ ≤ C * (H * t) * ‖P‖ + C * (H * t) * Sv * ‖P‖ + C * S' * (Hv * t) * ‖P‖ := by
        gcongr
    _ = C * (H + H * Sv + S' * Hv) * t * ‖P‖ := by ring
/-- Difference-quotient step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
`d`-uniform bounds for `w_d = d⁻¹ (v(· + d e) - v)` and for the forcing term `F_d` of its system on
`B̆_{2R}(xb)`.  Claims (i)–(iv) hold with the `d`-independent bound `S` of
`dohr_eb_lhr_dqub_wd_props`, claim (v) with the `d`-independent constant `M'` of
`dohr_eb_lhr_dqub_forcing_holder`; `M := max S M'` serves both, as `‖x - y‖ ^ α * ‖P‖ ≥ 0`. -/
theorem dohr_eb_lhr_dq_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), 0 < α → α ≤ 1 → IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ M) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ (∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α) ∧ ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R _ _ hU hR hBU he ha hΦ hv
  -- Steps 6–8: `w_d` is bounded by `S`, `C¹`, has the stated derivative, and `Dw_d` is Hölder.
  obtain ⟨S, hS⟩ := Submission.dohr_eb_lhr_dqub_wd_props n ℓ α U v xb e R hU hR hBU he hv
  -- Step 9: the forcing term is `α`-Hölder in `x` with the constant `M'`.
  obtain ⟨M', hM'⟩ :=
    Submission.dohr_eb_lhr_dqub_forcing_holder n ℓ α U a Φ v xb e R hU hR hBU he ha hΦ hv
  -- Step 10: `M := max S M'` does not depend on `d`.
  refine ⟨max S M', fun d hd hdR => ?_⟩
  obtain ⟨hw, hC1, hDw, hHol⟩ := hS d hd hdR
  refine ⟨fun x hx => (hw x hx).trans (le_max_left S M'), hC1, hDw, hHol,
    fun x hx y hy P => (hM' d hd hdR x hx y hy P).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right S M')
    (Real.rpow_nonneg (norm_nonneg (x - y)) α)) (norm_nonneg P)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
