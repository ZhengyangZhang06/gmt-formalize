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

/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (p. 127): if `H = h` `μ_V`-a.e. for some
`h` continuous on `U`, then `H` is locally in `Lᵖ(μ_V)` in `U` for every `p > 0`.  On a compact
`K ⊆ U`, `|h| ≤ A` and `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞`, so `∫_K |H|ᵖ dμ_V ≤ Aᵖ μ_V(K) < ∞`. -/
theorem dohr_locally_lp_of_continuous : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ), ContinuousOn h U → (∀ᵐ x ∂V.weight, H x = h x) → ∀ p : ℝ, 0 < p → V.LocallyLp H p := by
  intro n ℓ U V H h hh hHh p hp K hK hKU
  -- `|h| ≤ A` on the compact set `K ⊆ U`.
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hh.mono hKU)
  -- `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞` since `θ` is `Hⁿ`-integrable on `M ∩ K`.
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : V.weight K < ∞ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm]
    exact (V.integrableOn_mult K hK hKU).setLIntegral_lt_top
  calc ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight
      = ∫⁻ x in K, ‖h x‖ₑ ^ p ∂V.weight :=
        lintegral_congr_ae (by filter_upwards [ae_restrict_of_ae hHh] with x hx; rw [hx])
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal A ^ p ∂V.weight :=
        setLIntegral_mono measurable_const fun x hx => by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hA x hx)
    _ = ENNReal.ofReal A ^ p * V.weight K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top) hμK
/-- **Simon Ch. 5, Theorem 7.1, proof, first sentence (p. 127).**  If `H` is locally in `Lᵖ(μ_V)`
on the open set `U` for some `p > n` and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then `ξ ∈ spt V`, and for
every `δ > 0` there is `r > 0` with `B_r(ξ) ⊆ U`, `μ_V(B_r(ξ)) ≤ (1 + δ) ω_n rⁿ` and
`(r^{p−n} ∫_{B_r(ξ)} |H|ᵖ dμ_V)^{1/p} ≤ δ`. -/
theorem density_one_allard_scale : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (δ : ℝ), IsOpen U → (n : ℝ) < p →
    V.LocallyLp H p → ξ ∈ U → V.HasDensity ξ 1 → 0 < δ → ξ ∈ V.support ∧ ∃ r : ℝ, 0 < r ∧
      closedBall ξ r ⊆ U ∧
      V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) ∧
      V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ := by
  intro n ℓ U V H p ξ δ hU hp hLp hξU hξ hδ
  rw [RectifiableVarifold.HasDensity, ENNReal.ofReal_one] at hξ
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  -- A closed ball `B_{r₀}(ξ) ⊆ U`; it is compact, so `∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V < ∞`.
  obtain ⟨r₀, hr₀, hr₀U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hξU)
  have hA := hLp _ (isCompact_closedBall ξ r₀) hr₀U
  -- `(r^{p−n} ∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V)^{1/p} → 0` as `r ↓ 0`, since `p > n`.
  have hdecay : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
      ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ (p - n)) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (p - n) (Or.inr hpn.le)).tendsto
      rw [Real.zero_rpow hpn.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hA.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    have h3 : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
        ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 (0 ^ (1 / p))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h2
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at h3
  refine ⟨⟨hξU, nhds_basis_closedBall.mem_measureSupport.mpr fun ε hε => ?_⟩, ?_⟩
  · -- `ξ ∈ spt μ_V`: the density ratio tends to `1 > 0`, so `μ_V(B_ε(ξ)) > 0` for every `ε > 0`.
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ε ∧
        0 < V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) := by
      filter_upwards [Ioo_mem_nhdsGT hε, hξ.eventually_const_lt zero_lt_one] with r h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨r, hr, hQ⟩ := hev.exists
    have h0 : V.weight (closedBall ξ r) ≠ 0 := fun h0 => by simp [h0] at hQ
    exact (pos_iff_ne_zero.mpr h0).trans_le (measure_mono (closedBall_subset_closedBall hr.2.le))
  -- A radius `r ∈ (0, r₀)` below both the mass threshold and the `Lᵖ` threshold.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ ∧
      V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) <
        ENNReal.ofReal (1 + δ) ∧
      (ENNReal.ofReal (r ^ (p - n)) * ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) <
        ENNReal.ofReal δ := by
    filter_upwards [Ioo_mem_nhdsGT hr₀,
      hξ.eventually_lt_const (ENNReal.one_lt_ofReal.mpr (show (1 : ℝ) < 1 + δ by linarith)),
      hdecay.eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)] with r h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r, ⟨hr, hrr₀⟩, hQ, hS⟩ := hev.exists
  have hball : closedBall ξ r ⊆ closedBall ξ r₀ := closedBall_subset_closedBall hrr₀.le
  refine ⟨r, hr, hball.trans hr₀U, ?_, ?_⟩
  · have hv : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr n)
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + δ by linarith)]
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hv).ne' ENNReal.ofReal_ne_top).mp hQ.le
  · refine le_trans ?_ hS.le
    exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono_set hball))
      (one_div_pos.mpr hp0).le
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`.  If `V` has generalized mean curvature `H` in `U`,
then `V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`, and the hypotheses 5.1 of `V` in
`B_r(ξ)` become the hypotheses 5.1 (`AllardHypotheses`) of `V'` in `B_r(0)`. -/
theorem exists_translated_varifold_allardHypotheses : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ x, V'.mult x = V.mult (x + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ))) ∧ ∀ (H : Amb n ℓ → Amb n ℓ) (p δ r : ℝ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ξ ∈ V.support → 0 < r → closedBall ξ r ⊆ U → V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) → V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ → V'.AllardHypotheses (fun x => H (x + ξ)) p δ r := by
  intro n ℓ U V ξ
  -- Step 1: `τ = (· − ξ)` is an isometric measurable equivalence with inverse `(· + ξ)`; both
  -- preserve `Hⁿ`, and `τ(S) = (· + ξ)⁻¹(S)`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro hx
      exact ⟨x + ξ, hx, by simp⟩
  have hiso : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hmp_add : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hmp_sub : MeasurePreserving (fun x : Amb n ℓ => x - ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hme_add : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  have hme_sub : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  -- `τ⁻¹(K) ⊆ U` whenever `K ⊆ τ(U)`.
  have hpre_sub : ∀ K : Set (Amb n ℓ), K ⊆ (fun x => x - ξ) '' U → (fun x => x - ξ) ⁻¹' K ⊆ U := by
    intro K hKU y hy
    obtain ⟨u, hu, hu'⟩ := hKU hy
    have : u = y := by simpa using hu'
    exact this ▸ hu
  -- Step 2: the structure fields of `V' = v(τ(M), θ(· + ξ))` in `τ(U)`.
  have hc_meas : NullMeasurableSet ((fun x => x - ξ) '' V.carrier) (μHE[n] : Measure (Amb n ℓ)) := by
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hmp_add.quasiMeasurePreserving
  have hc_rect : Poincare.SimonGMT.Chapter03.CountablyRectifiable n
      ((fun x => x - ξ) '' V.carrier) := by
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j y => F j y - ξ, fun j => ?_, ?_⟩
    · rw [hiso.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨1 * K, hiso.lipschitzWith.comp hK⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, y, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, y, rfl⟩)
  have hm_pos : ∀ x ∈ (fun x => x - ξ) '' V.carrier, 0 < V.mult (x + ξ) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using V.mult_pos x hx
  have hm_aemeas : AEMeasurable (fun x => V.mult (x + ξ))
      ((μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier)) := by
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hmp_add.restrict_preimage_emb hme_add V.carrier).quasiMeasurePreserving
  have hm_int : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ (fun x => x - ξ) '' U →
      IntegrableOn (fun x => V.mult (x + ξ)) ((fun x => x - ξ) '' V.carrier ∩ K)
        (μHE[n] : Measure (Amb n ℓ)) := by
    intro K hK hKU
    have hK' : IsCompact ((fun x => x - ξ) ⁻¹' K) := (Homeomorph.subRight ξ).isCompact_preimage.2 hK
    have h := V.integrableOn_mult _ hK' (hpre_sub K hKU)
    rw [← hmp_add.integrableOn_comp_preimage hme_add] at h
    have hset : (fun x => x - ξ) '' V.carrier ∩ K =
        (fun x => x + ξ) ⁻¹' (V.carrier ∩ (fun x => x - ξ) ⁻¹' K) := by
      rw [himage]
      ext x
      simp
    rw [hset]
    exact h
  obtain ⟨V', hV'c, hV'm⟩ : ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U),
      V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ x, V'.mult x = V.mult (x + ξ) :=
    ⟨⟨(fun x => x - ξ) '' V.carrier, fun x => V.mult (x + ξ), image_mono V.carrier_subset,
      hc_meas, hc_rect, hm_pos, hm_aemeas, hm_int⟩, rfl, fun _ => rfl⟩
  have hV'mf : V'.mult = fun x => V.mult (x + ξ) := funext hV'm
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hweight : V'.weight = V.weight.map (fun x => x - ξ) := by
    have hres : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map (fun x => x - ξ) =
        (μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier) := by
      have h1 := hme_sub.restrict_map (μHE[n] : Measure (Amb n ℓ)) ((fun x => x - ξ) '' V.carrier)
      rw [hmp_sub.map_eq, preimage_image_eq _ hme_sub.injective] at h1
      exact h1.symm
    ext s hs
    rw [Measure.map_apply hme_sub.measurable hs]
    simp only [RectifiableVarifold.weight]
    rw [hV'c, hV'mf, withDensity_apply _ hs, withDensity_apply _ (hme_sub.measurable hs),
      ← hres, hme_sub.restrict_map, hme_sub.lintegral_map]
    simp
  -- Step 4: `spt V' = τ(spt V)`, since `spt(τ_# μ) = τ(spt μ)` for the homeomorphism `τ`.
  have hsupport : V'.support = (fun x => x - ξ) '' V.support := by
    have hspt : (V.weight.map (fun x => x - ξ)).support =
        (fun x => x - ξ) '' V.weight.support := by
      ext x
      rw [himage, mem_preimage, Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
      constructor
      · intro h N' hN'
        have hN : (fun y => y + ξ) ⁻¹' N' ∈ 𝓝 x :=
          (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hN'
        have := h _ hN
        rw [hme_sub.map_apply] at this
        convert this using 2
        ext y
        simp
      · intro h N hN
        have hN' : (fun y => y - ξ) ⁻¹' N ∈ 𝓝 (x + ξ) := by
          apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
          simpa using hN
        rw [hme_sub.map_apply]
        exact h _ hN'
    unfold RectifiableVarifold.support
    rw [hweight, hspt, image_inter hme_sub.injective]
  -- Step 5: weighted approximate tangent spaces, hence `tangentProj`, are translation equivariant.
  have htangent : ∀ x, V'.tangentProj x = V.tangentProj (x + ξ) := by
    intro x
    have hpred : (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V'.carrier V'.mult x P) =
        (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult (x + ξ) P) := by
      funext P
      have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap x r '' V'.carrier =
          Poincare.SimonGMT.Chapter03.blowUpMap (x + ξ) r '' V.carrier := by
        intro r
        rw [hV'c, image_image]
        congr 1
        funext m
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
        congr 1
        abel
      have hmult : ∀ (r : ℝ) (y : Amb n ℓ), V'.mult (x + r • y) = V.mult (x + ξ + r • y) := by
        intro r y
        rw [hV'm]
        congr 1
        abel
      unfold Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt
      simp only [hset, hmult, hV'm]
    have hchoose : ∀ {p q : Submodule ℝ (Amb n ℓ) → Prop} (h1 : ∃ P, p P) (h2 : ∃ P, q P),
        p = q → Classical.choose h1 = Classical.choose h2 := by
      intro p q h1 h2 h
      subst h
      rfl
    have hproj : ∀ {K L : Submodule ℝ (Amb n ℓ)} [K.HasOrthogonalProjection]
        [L.HasOrthogonalProjection], K = L → K.starProjection = L.starProjection := by
      intro K L _ _ h
      subst h
      rfl
    unfold RectifiableVarifold.tangentProj
    split_ifs with h1 h2 h2
    · exact hproj (hchoose h1 h2 hpred)
    · exact absurd (hpred ▸ h1) h2
    · exact absurd (hpred ▸ h2) h1
    · rfl
  -- Step 6: `div_{M'} X ∘ τ = div_M (X ∘ τ)`.
  have hdiv : ∀ (X : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ),
      V'.divM X (y - ξ) = V.divM (fun z => X (z - ξ)) y := by
    intro X y
    unfold RectifiableVarifold.divM
    rw [htangent, fderiv_comp_sub, sub_add_cancel]
  -- Step 7: generalized mean curvature transfers to `V'` with `H' = H(· + ξ)`.
  have hGMC : ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
      V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ)) := by
    intro H hH
    obtain ⟨hloc, hid⟩ := hH
    let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
    have he : (fun x : Amb n ℓ => x - ξ) = ⇑e := rfl
    refine ⟨?_, ?_⟩
    · rw [hweight]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨N, hN, hint⟩ := hloc y hy
      refine ⟨(fun x => x - ξ) '' N, ?_, ?_⟩
      · have hmap := (Homeomorph.subRight ξ).isEmbedding.map_nhdsWithin_eq U y
        simp only [Homeomorph.coe_subRight] at hmap
        rw [← hmap]
        exact image_mem_map hN
      · rw [he, integrableOn_map_equiv e, preimage_image_eq _ e.injective]
        convert hint using 1
        funext z
        show H (z - ξ + ξ) = H z
        rw [sub_add_cancel]
    · intro X hX hXc hXU
      rw [hweight]
      have hI1 : ∫ x, V'.divM X x ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, V'.divM X (y - ξ) ∂V.weight := integral_map_equiv e _
      have hI2 : ∫ x, inner ℝ (X x) (H (x + ξ)) ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, inner ℝ (X (y - ξ)) (H (y - ξ + ξ)) ∂V.weight :=
        integral_map_equiv e (fun x => inner ℝ (X x) (H (x + ξ)))
      rw [hI1, hI2]
      simp only [hdiv, sub_add_cancel]
      have hY1 : ContDiff ℝ 1 (fun z => X (z - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
      have hY2 : HasCompactSupport (fun z => X (z - ξ)) :=
        hXc.comp_homeomorph (Homeomorph.subRight ξ)
      have hY3 : tsupport (fun z => X (z - ξ)) ⊆ U := by
        have hts : tsupport (fun z => X (z - ξ)) = (fun z => z - ξ) ⁻¹' tsupport X := by
          have := (Homeomorph.subRight ξ).preimage_closure (Function.support X)
          simp only [Homeomorph.coe_subRight] at this
          rw [tsupport, tsupport, this]
          rfl
        rw [hts]
        exact hpre_sub _ hXU
      exact hid _ hY1 hY2 hY3
  refine ⟨V', hV'c, hV'm, hweight, hsupport, hGMC, ?_⟩
  -- Step 8: the hypotheses 5.1 of `V` in `B_r(ξ)` are those of `V'` in `B_r(0)`.
  intro H p δ r hH hθ hξ hr hball hmass hLp
  have hball_pre : (fun x => x - ξ) ⁻¹' closedBall (0 : Amb n ℓ) r = closedBall ξ r := by
    ext y
    simp [dist_eq_norm]
  refine ⟨hr, hGMC H hH, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hweight, hme_sub.ae_map_iff]
    filter_upwards [hθ] with y hy
    rw [hV'm, sub_add_cancel]
    exact hy
  · rw [hsupport]
    exact ⟨ξ, hξ, sub_self ξ⟩
  · intro z hz
    refine ⟨z + ξ, hball ?_, by simp⟩
    rw [← hball_pre]
    simpa using hz
  · rw [hweight, hme_sub.map_apply, hball_pre]
    exact hmass
  · unfold RectifiableVarifold.scaledLpNorm at hLp ⊢
    rw [hweight, hme_sub.restrict_map, hme_sub.lintegral_map, hball_pre]
    simpa using hLp
/-- In the proof of Simon 7.1 (p. 127), `u ∈ C^{1,1−n/p}` comes from the estimate of Theorem 5.2:
a finite scaled `C^{1,α}` norm on `B` puts `u` in the Hölder class `C^{1,α}(W)` for every
`W ⊆ int B`.  On `int B` the derivative within `B` is the derivative, and the operator norm of a
linear map is at most its Hilbert–Schmidt norm. -/
theorem isHolderCk_one_of_scaledC1AlphaNorm_ne_top : ∀ {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B W : Set (Rn n)) (α ρ : ℝ), 0 < α → 0 < ρ → ContDiffOn ℝ 1 u B → W ⊆ interior B → scaledC1AlphaNorm u B α ρ ≠ ∞ → IsHolderCkα 1 α u W := by
  intro n ℓ u B W α ρ hα hρ hu hW hN
  -- The operator norm is at most the Hilbert–Schmidt norm (Cauchy–Schwarz in the standard basis).
  have hop : ∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ hsNorm A := by
    intro A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  -- The three suprema in the scaled norm are finite, since `ρ⁻¹ > 0` and `ρ ^ α > 0`.
  rw [scaledC1AlphaNorm, ENNReal.add_ne_top, ENNReal.add_ne_top] at hN
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := hN
  replace h₀ : (⨆ x ∈ B, ‖u x‖ₑ) ≠ ∞ := fun h =>
    h₀ (ENNReal.mul_eq_top.2 (Or.inl ⟨(ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne', h⟩))
  replace h₂ : (⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
      ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)) ≠ ∞ :=
    fun h => h₂ (ENNReal.mul_eq_top.2
      (Or.inl ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hρ α)).ne', h⟩))
  -- Real bounds on `B` for `|u|`, `|D_B u|` and the Hölder quotients of `D_B u`.
  obtain ⟨s₀, hb₀⟩ : ∃ s : ℝ, ∀ x ∈ B, ‖u x‖ ≤ s :=
    ⟨_, fun x hx => (toReal_enorm (u x)).symm.trans_le
      (ENNReal.toReal_mono h₀ (le_iSup₂_of_le x hx le_rfl))⟩
  obtain ⟨s₁, hb₁⟩ : ∃ s : ℝ, ∀ x ∈ B, hsNorm (fderivWithin ℝ u B x) ≤ s :=
    ⟨_, fun x hx => (ENNReal.ofReal_le_iff_le_toReal h₁).1 (le_iSup₂_of_le x hx le_rfl)⟩
  obtain ⟨s₂, hb₂⟩ : ∃ s : ℝ, ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) ≤ s * ‖x - y‖ ^ α :=
    ⟨_, fun x hx y hy hxy =>
      (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) α)).1
        ((ENNReal.ofReal_le_iff_le_toReal h₂).1
          (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))))⟩
  -- On `W ⊆ int B` the derivative within `B` is the derivative.
  have hWB : W ⊆ B := hW.trans interior_subset
  have hD : ∀ x ∈ W, fderivWithin ℝ u B x = fderiv ℝ u x := fun x hx =>
    fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 (hW hx))
  refine ⟨?_, ⟨max s₀ s₁, ?_⟩, ⟨s₂, ?_⟩⟩
  · exact_mod_cast hu.mono hWB
  · intro i hi x hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · rw [norm_iteratedFDeriv_zero]
      exact (hb₀ x (hWB hx)).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one, ← hD x hx]
      exact ((hop _).trans (hb₁ x (hWB hx))).trans (le_max_right _ _)
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow hα.ne']
    · -- The first iterated derivative is the derivative, up to a linear isometry.
      have hD₁ : iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y =
          (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ u x - fderiv ℝ u y) := by
        ext m
        simp
      rw [hD₁, LinearIsometryEquiv.norm_map, ← hD x hx, ← hD y hy]
      exact (hop _).trans (hb₂ x (hWB hx) y (hWB hy) hxy)
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)`.  `τ` and its
inverse `σ = (· + ξ)` are isometries, so they preserve `Hⁿ`, and `τ(S) = σ⁻¹(S)` for every set `S`;
null-measurability, countable rectifiability (via `τ(M₀)` and the Lipschitz maps `F_j − ξ`),
positivity, a.e.-measurability of `θ ∘ σ` and its integrability on `τ(M) ∩ K` (through the compact
set `σ(K) ⊆ U`) all transfer along `σ`. -/
theorem dohr_tv_exists_translate : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ y, V'.mult y = V.mult (y + ξ) := by
  intro n ℓ U V ξ
  -- Step 0: `τ = (· − ξ)` is an isometry, `σ = (· + ξ)` is an `Hⁿ`-measure-preserving measurable
  -- embedding, and `τ(S) = σ⁻¹(S)` for every set `S`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + ξ, hy, add_sub_cancel_right y ξ⟩
  have hτ : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hσ : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hσe : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  -- Steps 1–2: `V' = v(τ(M), θ ∘ σ)`; the two required equalities hold by definition.
  refine ⟨{
    carrier := (fun x => x - ξ) '' V.carrier
    mult := fun y => V.mult (y + ξ)
    carrier_subset := image_mono V.carrier_subset
    nullMeasurableSet_carrier := ?_
    countablyRectifiable := ?_
    mult_pos := ?_
    aemeasurable_mult := ?_
    integrableOn_mult := ?_ }, rfl, fun y => rfl⟩
  · -- Step 3: `τ(M) = σ⁻¹(M)` and `σ` is quasi-measure-preserving.
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hσ.quasiMeasurePreserving
  · -- Step 4: translate the null set `M₀` and the Lipschitz pieces `F j` by `−ξ`.
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j z => F j z - ξ, fun j => ?_, ?_⟩
    · rw [hτ.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨K, LipschitzWith.of_dist_le_mul fun z w =>
        (dist_sub_right (F j z) (F j w) ξ).le.trans (hK.dist_le_mul z w)⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, z, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, z, rfl⟩)
  · -- Step 5: `θ(x − ξ + ξ) = θ(x) > 0` for `x ∈ M`.
    rintro _ ⟨x, hx, rfl⟩
    show 0 < V.mult (x - ξ + ξ)
    rw [sub_add_cancel]
    exact V.mult_pos x hx
  · -- Step 6: `σ` is measure preserving from `Hⁿ⌞σ⁻¹(M)` to `Hⁿ⌞M`.
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hσ.restrict_preimage_emb hσe V.carrier).quasiMeasurePreserving
  · -- Step 7: `σ(K)` is a compact subset of `U`, and `τ(M) ∩ K = σ⁻¹(M ∩ σ(K))`.
    intro K hK hKU
    have hσK : (fun x => x + ξ) '' K ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKU hy
      simpa using hx
    have h := (hσ.integrableOn_comp_preimage hσe).2
      (V.integrableOn_mult _ (hK.image (continuous_add_const ξ)) hσK)
    rwa [preimage_inter, hσe.injective.preimage_image, ← himage] at h
/-- **Weight of a translated varifold** (Simon Ch. 4, 1.1; Ch. 5, proof of Theorem 7.1, p. 127:
"after applying the appropriate translation").  Let `τ(x) = x - ξ`.  If `V' = v(τ(M), θ(· + ξ))`,
then `μ_{V'} = τ_# μ_V`: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ` and
`τ_#(Hⁿ ⌞ M) = Hⁿ ⌞ τ(M)`; for measurable `S`, changing variables along `τ` gives
`μ_{V'}(S) = ∫_{τ⁻¹S} θ(x - ξ + ξ) d(Hⁿ ⌞ M)(x) = μ_V(τ⁻¹S)`. -/
theorem dohr_tv_weight_eq_map : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ),
    V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) →
    V'.weight = V.weight.map (fun x => x - ξ) := by
  intro n ℓ U U' V V' ξ hc hm
  -- `τ(x) = x - ξ` as a measurable equivalence `e` (inverse `y ↦ y + ξ`).
  let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
  -- Step 1: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ`.
  have h1 : (μHE[n] : Measure (Amb n ℓ)).map e = μHE[n] :=
    ((IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n).map_eq
  -- Step 2: `Hⁿ ⌞ τ(M) = (τ_# Hⁿ) ⌞ τ(M) = τ_#(Hⁿ ⌞ τ⁻¹(τ(M))) = τ_#(Hⁿ ⌞ M)`.
  have h2 : (μHE[n] : Measure (Amb n ℓ)).restrict V'.carrier =
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map e := by
    have h := e.restrict_map (μHE[n] : Measure (Amb n ℓ)) (e '' V.carrier)
    rw [h1, Set.preimage_image_eq _ e.injective] at h
    rw [hc]
    exact h
  -- Step 3: compare `μ_{V'}` and `τ_# μ_V` on measurable sets `S`.
  show V'.weight = V.weight.map e
  ext S hS
  -- Step 4: `(τ_# μ_V)(S) = μ_V(τ⁻¹S) = ∫_{τ⁻¹S} θ d(Hⁿ ⌞ M)`.
  rw [e.map_apply]
  simp only [RectifiableVarifold.weight]
  rw [withDensity_apply _ (e.measurable hS)]
  -- Step 5: `μ_{V'}(S) = ∫_S θ' d(τ_#(Hⁿ ⌞ M)) = ∫_{τ⁻¹S} θ'(x - ξ) d(Hⁿ ⌞ M)(x)`.
  rw [withDensity_apply _ hS, h2, e.restrict_map, lintegral_map_equiv]
  -- Step 6: `θ'(x - ξ) = θ(x - ξ + ξ) = θ(x)`, so the two integrals agree.
  refine lintegral_congr fun x => ?_
  show ENNReal.ofReal (V'.mult (x - ξ)) = ENNReal.ofReal (V.mult x)
  rw [hm, sub_add_cancel]
/-- **Support of a translated measure** (used for Simon Ch. 5, Theorem 7.1, p. 127, where `V` is
translated by `τ(x) = x − ξ`).  For every measure `μ` on `ℝ^{n+ℓ}`, `spt (τ_# μ) = τ (spt μ)`.
`τ` is the measurable equivalence `MeasurableEquiv.subRight ξ`, so `(τ_# μ)(N) = μ(τ⁻¹ N)` for
every set `N`.  If `y ∈ spt (τ_# μ)` and `N` is a neighbourhood of `y + ξ`, then `σ⁻¹ N`
(`σ(x) = x + ξ`) is a neighbourhood of `y` and `μ N = (τ_# μ)(σ⁻¹ N) > 0`, so `y = τ(y + ξ)`
with `y + ξ ∈ spt μ`; conversely `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N`
of `τ(x)`. -/
theorem dohr_tv_support_map_sub : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (ξ : Amb n ℓ),
    (μ.map (fun x => x - ξ)).support = (fun x => x - ξ) '' μ.support := by
  intro n ℓ μ ξ
  -- `(τ_# μ)(N) = μ(τ⁻¹ N)` for every set `N`, measurable or not.
  have hmap : ∀ N : Set (Amb n ℓ), μ.map (fun x => x - ξ) N = μ ((fun x => x - ξ) ⁻¹' N) :=
    fun N => (MeasurableEquiv.subRight ξ).map_apply N
  ext y
  simp only [Measure.mem_support_iff_forall, hmap, mem_image]
  constructor
  · -- `y + ξ ∈ spt μ`: pull each neighbourhood `N` of `y + ξ` back along `σ`.
    intro hy
    refine ⟨y + ξ, fun N hN => ?_, add_sub_cancel_right y ξ⟩
    have h := hy ((fun x => x + ξ) ⁻¹' N)
      ((continuous_add_const ξ).continuousAt.preimage_mem_nhds hN)
    simpa [preimage_preimage] using h
  · -- `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N` of `τ(x)`.
    rintro ⟨x, hx, rfl⟩ N hN
    exact hx _ ((continuous_sub_right ξ).continuousAt.preimage_mem_nhds hN)
/-- Simon Ch. 5, proof of Theorem 7.1 (the translation `τ(x) = x − ξ` of `V = v(M, θ)`): if
`V'.carrier = τ(M)` and `V'.mult = θ(· + ξ)`, then `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` and
`V'.mult(y + r z) = θ((y + ξ) + r z)`, so the weighted approximate tangent predicates of `V'` at `y`
and of `V` at `y + ξ` coincide, and hence so do the classically chosen tangent projections. -/
theorem dohr_tv_tangentProj_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ), V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) → ∀ y, V'.tangentProj y = V.tangentProj (y + ξ) := by
  intro n ℓ U U' V V' ξ hM hθ y
  -- The blow-ups agree: `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` since `(x − ξ) − y = x − (y + ξ)`.
  have hblow : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap y r '' V'.carrier =
      Poincare.SimonGMT.Chapter03.blowUpMap (y + ξ) r '' V.carrier := by
    intro r
    rw [hM, Set.image_image]
    congr 1
    funext x
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, sub_sub, add_comm ξ y]
  -- The weights agree: `V'.mult(y + r z) = θ((y + ξ) + r z)`.
  have hw : ∀ (r : ℝ) (z : Amb n ℓ), V'.mult (y + r • z) = V.mult (y + ξ + r • z) := by
    intro r z
    rw [hθ, add_right_comm]
  -- Hence the weighted approximate tangent predicates of `V'` at `y` and of `V` at `y + ξ` agree.
  have hP :
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V'.carrier V'.mult y =
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (y + ξ) := by
    funext P
    simp only [Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt, hblow, hw, hθ y]
  -- `tangentProj` only sees the tangent predicate, so equal predicates give equal projections.
  have key : ∀ A B : Submodule ℝ (Amb n ℓ) → Prop, A = B →
      @dite _ (∃ P, A P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => (0 : Amb n ℓ →L[ℝ] Amb n ℓ)) =
        @dite _ (∃ P, B P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => 0) := by
    rintro A B rfl
    rfl
  exact key _ _ hP
/-- **Generalized mean curvature under the translation `τ(x) = x − ξ`** (Simon Ch. 4, 3.14).  Let
`V'` be a rectifiable varifold in `τ(U)` with `μ_{V'} = τ_# μ_V` and `p_{T_y V'} = p_{T_{y+ξ} V}`
for every `y`.  If `V` has generalized mean curvature `H` in `U`, then `V'` has generalized mean
curvature `y ↦ H(y + ξ)` in `τ(U)`.
Proof: `τ` is a homeomorphism and a measurable embedding.  Local integrability moves along `τ`,
because `τ` maps `𝓝[U] x` onto `𝓝[τ(U)] τ(x)` and `H(· + ξ) ∘ τ = H`.  For `X ∈ C¹_c(τ(U))` the
field `Y = X ∘ τ` lies in `C¹_c(U)`, and `div_{M'} X(τ(x)) = div_M Y(x)` because
`DY(x) = DX(τ(x))`.  Changing variables in both first-variation integrals then gives the identity
for `V'`. -/
theorem dohr_tv_gmc_transfer : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U)), V'.weight = V.weight.map (fun x => x - ξ) → (∀ y, V'.tangentProj y = V.tangentProj (y + ξ)) → ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ V' hw htp H hH
  obtain ⟨hloc, hvar⟩ := hH
  -- `τ(x) = x − ξ` is a measurable embedding and a topological embedding.
  have hτm : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  have hτe : Topology.IsEmbedding (fun x : Amb n ℓ => x - ξ) := (Homeomorph.subRight ξ).isEmbedding
  refine ⟨?_, fun X hX hXc hXs => ?_⟩
  · -- Step 1: `H(· + ξ)` is locally integrable on `τ(U)`.  At `τ(x)`, `x ∈ U`, the filter
    -- `𝓝[τ(U)] τ(x)` is the image of `𝓝[U] x` under `τ`, and `H(· + ξ) ∘ τ = H`.
    rintro _ ⟨x, hxU, rfl⟩
    rw [hw, ← hτe.map_nhdsWithin_eq, hτm.integrableAtFilter_map_iff]
    simpa only [Function.comp_def, sub_add_cancel] using hloc x hxU
  · -- Step 2: the first variation of `V'`, tested against `X`, via the field `Y = X ∘ τ` on `U`.
    have hY : ContDiff ℝ 1 (fun x => X (x - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
    have hYc : HasCompactSupport (fun x => X (x - ξ)) :=
      hXc.comp_homeomorph (Homeomorph.subRight ξ)
    have hYs : tsupport (fun x => X (x - ξ)) ⊆ U := by
      intro x hx
      have hx' : x - ξ ∈ tsupport X := by
        have h : x ∈ tsupport (X ∘ Homeomorph.subRight ξ) := hx
        rwa [tsupport_comp_eq_preimage] at h
      obtain ⟨u, hu, hux⟩ := hXs hx'
      rwa [← sub_left_injective hux]
    -- `div_{M'} X (x − ξ) = div_M Y x`: the tangent planes match and `DY(x) = DX(x − ξ)`.
    have hdiv : ∀ x, V'.divM X (x - ξ) = V.divM (fun x => X (x - ξ)) x := by
      intro x
      simp only [RectifiableVarifold.divM]
      rw [htp, sub_add_cancel, fderiv_comp_sub]
    calc ∫ y, V'.divM X y ∂V'.weight = ∫ x, V'.divM X (x - ξ) ∂V.weight := by
          rw [hw, hτm.integral_map]
      _ = ∫ x, V.divM (fun x => X (x - ξ)) x ∂V.weight := by simp only [hdiv]
      _ = -∫ x, inner ℝ (X (x - ξ)) (H x) ∂V.weight := hvar _ hY hYc hYs
      _ = -∫ y, inner ℝ (X y) (H (y + ξ)) ∂V'.weight := by
          rw [hw, hτm.integral_map]
          simp only [sub_add_cancel]
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one), steps 1–2: if
`Q(S − ξ) ∩ B̆_R(0) = Γ ∩ B̆_R(0)` for the graph `Γ = graph u` of a `C¹` map `u` on `B̆ⁿ_R(0)`
whose `Hⁿ`-density is `1` at each of its points, then `Hⁿ(S ∩ B̆_ρ(ξ)) < ∞` for `ρ < R` and `S`
has `Hⁿ`-density `1` at each point of `S ∩ B̆_R(ξ)`.  The isometry `T z = Q(z − ξ)` preserves
`Hⁿ`; `T(S ∩ B̆_ρ(ξ))` lies in the compact set `G(Bⁿ_ρ(0)) ⊆ Γ`, `G x = (x, u x)`, covered by
finitely many balls `B_r(G x)` with `Hⁿ(Γ ∩ B_r(G x)) < ∞`; and if `T y = G x`, then
`T(S ∩ B_r(y)) = Γ ∩ B_r(G x)` for `0 < r < R − |y − ξ|`. -/
theorem dohr_lmo_graph_support_density : ∀ n ℓ : ℕ, ∀ (S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ x ∈ ball (0 : Rn n) R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ ρ : ℝ, ρ < R → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball ξ ρ) < ⊤) ∧ ∀ y ∈ S ∩ ball ξ R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ S ξ R Q u hu hgraph hdens
  -- Step 0: `T z = Q (z - ξ)` is an isometry, so it preserves `Hⁿ`, and
  -- `T(S) ∩ B̆_R(0) = Γ ∩ B̆_R(0)` with `Γ = graph u`.
  have hT : ∀ X : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Q '' ((fun x => x - ξ) '' X)) = μHE[n] X := fun X => by
    rw [Q.isometry.euclideanHausdorffMeasure_image,
      (Isometry.of_dist_eq fun x y => dist_sub_right x y ξ).euclideanHausdorffMeasure_image]
  have hSΓ : ∀ z ∈ S, ‖z - ξ‖ < R → ∃ x ∈ ball (0 : Rn n) R, graphPoint x (u x) = Q (z - ξ) := by
    intro z hz hzR
    have hmem : Q (z - ξ) ∈ Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R :=
      ⟨⟨z - ξ, ⟨z, hz, rfl⟩, rfl⟩, by rwa [mem_ball_zero_iff, Q.norm_map]⟩
    rw [hgraph] at hmem
    exact hmem.1
  have hΓS : ∀ w ∈ graphOver u (ball 0 R), ‖w‖ < R → ∃ z ∈ S, Q (z - ξ) = w := by
    intro w hw hwR
    have hmem : w ∈ graphOver u (ball 0 R) ∩ ball 0 R := ⟨hw, mem_ball_zero_iff.2 hwR⟩
    rw [← hgraph] at hmem
    obtain ⟨⟨_, ⟨z, hz, rfl⟩, rfl⟩, -⟩ := hmem
    exact ⟨z, hz, rfl⟩
  refine ⟨fun ρ hρ => ?_, fun y hy => ?_⟩
  · -- (a) `T(S ∩ B̆_ρ(ξ)) ⊆ G(Bⁿ_ρ(0))` with `G x = (x, u x)`; this compact subset of `Γ` has
    -- finite measure since every point of it has a ball `B_r(G x)` with `Hⁿ(Γ ∩ B_r(G x)) < ∞`.
    have hKR : closedBall (0 : Rn n) ρ ⊆ ball 0 R := closedBall_subset_ball hρ
    have hnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖a‖ ≤ ‖graphPoint a b‖ := by
      intro a b
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_add]
      refine Real.sqrt_le_sqrt (le_add_of_le_of_nonneg (le_of_eq ?_)
        (Finset.sum_nonneg fun j _ => by positivity))
      simp [graphPoint]
    have hgp : Continuous fun p : Rn n × Rn ℓ => graphPoint p.1 p.2 := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      induction i using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
      | right j =>
        simp only [Fin.append_right]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
    have hGc : ContinuousOn (fun x => graphPoint x (u x)) (closedBall (0 : Rn n) ρ) :=
      hgp.comp_continuousOn (continuousOn_id.prodMk (hu.continuousOn.mono hKR))
    have hfin : (μHE[n] : Measure (Amb n ℓ))
        ((fun x => graphPoint x (u x)) '' closedBall (0 : Rn n) ρ) < ⊤ := by
      refine ((isCompact_closedBall 0 ρ).image_of_continuousOn hGc).measure_lt_top_of_nhdsWithin ?_
      rintro _ ⟨x, hxK, rfl⟩
      obtain ⟨r, hr2, hr0⟩ := (((hdens x (hKR hxK)).eventually_lt_const
        ENNReal.one_lt_two).and self_mem_nhdsWithin).exists
      refine ⟨graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r, ?_, ?_⟩
      · refine mem_nhdsWithin.2 ⟨ball (graphPoint x (u x)) r, isOpen_ball, mem_ball_self hr0, ?_⟩
        rintro _ ⟨hw, ⟨x', hx', rfl⟩⟩
        exact ⟨⟨x', hKR hx', rfl⟩, ball_subset_closedBall hw⟩
      · refine lt_top_iff_ne_top.2 fun htop => ?_
        rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
        exact not_top_lt hr2
    refine lt_of_le_of_lt ?_ hfin
    rw [← hT (S ∩ ball ξ ρ)]
    refine measure_mono ?_
    rintro _ ⟨_, ⟨z, ⟨hz, hzB⟩, rfl⟩, rfl⟩
    have hzρ : ‖z - ξ‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hzB
    obtain ⟨x, -, hxe⟩ := hSΓ z hz (hzρ.trans hρ)
    refine ⟨x, mem_closedBall_zero_iff.2 ?_, hxe⟩
    calc ‖x‖ ≤ ‖graphPoint x (u x)‖ := hnorm x (u x)
      _ = ‖z - ξ‖ := by rw [hxe, Q.norm_map]
      _ ≤ ρ := hzρ.le
  · -- (b) `T y = G x` with `x ∈ B̆ⁿ_R(0)`; for `0 < r < R - |y - ξ|`,
    -- `T(S ∩ B_r(y)) = Γ ∩ B_r(G x)`, so the density ratios agree near `0`.
    obtain ⟨hyS, hyB⟩ := hy
    have hyR : ‖y - ξ‖ < R := by rwa [mem_ball, dist_eq_norm] at hyB
    obtain ⟨x, hx, hxy⟩ := hSΓ y hyS hyR
    refine (hdens x hx).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hyR)] with r hr
    have hset : graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r =
        Q '' ((fun x => x - ξ) '' (S ∩ closedBall y r)) := by
      ext w
      constructor
      · rintro ⟨hwΓ, hwB⟩
        rw [mem_closedBall, hxy] at hwB
        have hwR : ‖w‖ < R := by
          calc ‖w‖ = dist w 0 := (dist_zero_right w).symm
            _ ≤ dist w (Q (y - ξ)) + dist (Q (y - ξ)) 0 := dist_triangle _ _ _
            _ = dist w (Q (y - ξ)) + ‖y - ξ‖ := by rw [dist_zero_right, Q.norm_map]
            _ < R := by linarith [hr.2]
        obtain ⟨z, hz, rfl⟩ := hΓS w hwΓ hwR
        refine ⟨z - ξ, ⟨z, ⟨hz, ?_⟩, rfl⟩, rfl⟩
        rw [mem_closedBall, ← dist_sub_right z y ξ, ← Q.dist_map]
        exact hwB
      · rintro ⟨_, ⟨z, ⟨hz, hzB⟩, rfl⟩, rfl⟩
        rw [mem_closedBall] at hzB
        have hzR : ‖z - ξ‖ < R := by
          calc ‖z - ξ‖ = dist z ξ := (dist_eq_norm z ξ).symm
            _ ≤ dist z y + dist y ξ := dist_triangle _ _ _
            _ = dist z y + ‖y - ξ‖ := by rw [dist_eq_norm y ξ]
            _ < R := by linarith [hr.2]
        obtain ⟨x', hx', hx'e⟩ := hSΓ z hz hzR
        refine ⟨⟨x', hx', hx'e⟩, ?_⟩
        show Q (z - ξ) ∈ closedBall (graphPoint x (u x)) r
        rw [mem_closedBall, hxy, Q.dist_map, dist_sub_right]
        exact hzB
    rw [hset, hT]
/-- Graph tangent planes are `n`-dimensional `μ_V`-a.e. in the graph region.  `μ_V`-a.e. `y` lies in
`spt μ_V` (`Measure.support_mem_ae`), so for `y ∈ B̆_R(ξ)` the point `Q(y − ξ)` lies on the graph:
`Q(y − ξ) = G(x)` with `x ∈ B̆ⁿ_R(0)`, `G(z) = graphPoint z (u z)`.  By (TP) the tangent projection
at `y` is the projection onto `Q⁻¹(range DG(x))`.  `G` is differentiable at `x` coordinatewise, and
its first `n` coordinates are those of `z`, so by uniqueness of derivatives the first `n`
coordinates of `DG(x) v` are those of `v`; hence `DG(x)` is injective, `range DG(x)` has dimension
`n`, and so has its image under the linear equivalence `Q⁻¹`. -/
theorem dohr_lmo_graph_tangent_rank : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ball ξ R ⊆ U → DifferentiableOn ℝ u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection) → ∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj y = P.starProjection := by
  intro n ℓ U V ξ R Q u hball hdiff hgraph hTP
  filter_upwards [hTP, Measure.support_mem_ae (μ := V.weight)] with y hTPy hy hyR
  have hmem : Q (y - ξ) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R := by
    refine ⟨⟨y - ξ, ⟨y, ⟨hball hyR, hy⟩, rfl⟩, rfl⟩, ?_⟩
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
    exact hyR
  rw [hgraph] at hmem
  obtain ⟨⟨x, hx, hxy⟩, -⟩ := hmem
  have hux : DifferentiableAt ℝ u x := hdiff.differentiableAt (isOpen_ball.mem_nhds hx)
  have hG : DifferentiableAt ℝ (fun z : Rn n => graphPoint z (u z)) x := by
    rw [differentiableAt_euclidean]
    intro i
    induction i using Fin.addCases with
    | left j =>
      simpa [graphPoint] using (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x j).differentiableAt
    | right k => simpa [graphPoint] using differentiableAt_euclidean.mp hux k
  have hcoord : ∀ (j : Fin n) (v : Rn n),
      fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x v (Fin.castAdd ℓ j) = v j := by
    intro j v
    have h1 := (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (graphPoint x (u x))
      (Fin.castAdd ℓ j)).hasFDerivAt.comp x hG.hasFDerivAt
    have h2 : HasFDerivAt (fun z : Rn n => graphPoint z (u z) (Fin.castAdd ℓ j))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j) x := by
      simpa [graphPoint] using (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x j).hasFDerivAt
    simpa using congrArg (fun L => L v) (h1.unique h2)
  have hinj : Function.Injective
      (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro v w hvw
    ext j
    rw [← hcoord j v, ← hcoord j w]
    exact congrArg (fun z : Amb n ℓ => z (Fin.castAdd ℓ j)) hvw
  refine ⟨_, ?_, hTPy hyR x hx hxy.symm⟩
  rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one): the `Lᵖ` monotonicity
formula `hM` with an error `Λ(t) → 0`, uniformly for centres near `ξ`.  Put `κ = (p − n)/(4p)`,
`a = (∫_{B_R(ξ)} |H|ᵖ dμ_V)^{1/p} < ∞`, `Λ(t) = max {t^{(p−n)/p} a/κ, t}`, and choose `t₁ ≤ R/8`
with `Λ ≤ 1` on `(0, t₁]`.  For `y ∈ B̆_{R/2}(ξ)`, `t ∈ (0, t₁]` and `z ∈ B_t(y)` the ball
`B_t(z)` lies in `B̆_R(ξ)`, so `(t^{p−n} ∫_{B_t(z)} |H|ᵖ dμ_V)^{1/p} ≤ t^{(p−n)/p} a ≤ κ Λ(t)`
and `hM` applies at `(z, t, Λ(t))`; as `Φ` is nondecreasing on `(0, t)` with `Φ(r) → ω_n Θ`,
`ω_n Θ ≤ Φ(r) ≤ e^{Λ(t)} r⁻ⁿ μ_V(B_r(z)) + Λ(t)` for `r ∈ (0, t)`. -/
theorem dohr_lmo_uniform_monotonicity_bound : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (R : ℝ), (n : ℝ) < p → 0 < R → closedBall ξ R ⊆ U → (∀ (y : Amb n ℓ) (R' Λ : ℝ), 0 < R' → closedBall y R' ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R' → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R')) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R' ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R', |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R') ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t))) → (∀ᵐ x ∂V.weight, x ∈ ball ξ R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball ξ R)) → ∫⁻ x in closedBall ξ R, ‖H x‖ₑ ^ p ∂V.weight < ⊤ → ∃ t₁ > 0, ∃ Λ : ℝ → ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 0) ∧ ∀ y ∈ ball ξ (R / 2), ∀ t ∈ Ioc 0 t₁, ∀ z ∈ closedBall y t, ∃ Θ : ℝ, 0 ≤ Θ ∧ V.HasDensity z Θ ∧ ∀ r ∈ Ioo 0 t, unitBallVolume n * Θ ≤ Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + Λ t := by
  intro n ℓ U V H p ξ R hp hR hBU hM hTP hmeas hLp
  -- Step 1: `κ = (p - n)/(4p) > 0`, `β = (p - n)/p > 0` and `a = A^{1/p}`, where
  -- `A = ∫_{B_R(ξ)} |H|ᵖ dμ_V < ∞`.
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  have hβ : 0 < (p - n) * (1 / p) := mul_pos hpn (by positivity)
  set κ : ℝ := (p - n) / (4 * p)
  have hκ : 0 < κ := div_pos hpn (by positivity)
  set A : ℝ≥0∞ := ∫⁻ x in closedBall ξ R, ‖H x‖ₑ ^ p ∂V.weight
  set a : ℝ := (A ^ (1 / p)).toReal
  have hAa : A ^ (1 / p) = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hp1 hLp.ne)).symm
  -- Step 2: `Λ(t) = max (t^β a/κ) t`, which tends to `max 0 0 = 0` as `t → 0+`.
  set Λ : ℝ → ℝ := fun t => max (t ^ ((p - n) * (1 / p)) * a / κ) t
  have hΛlim : Tendsto Λ (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ ((p - n) * (1 / p)) * a / κ) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ ((p - n) * (1 / p)) * a / κ)) :=
      (((Real.continuousAt_rpow_const 0 _ (Or.inr hβ.le)).tendsto).mul_const a).div_const κ
    have h2 := h1.max (tendsto_id (x := 𝓝 (0 : ℝ)))
    rw [Real.zero_rpow hβ.ne', zero_mul, zero_div, max_self] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  -- Step 3: `t₁ = min (R/8) (ε/2)`, where `Λ < 1` on `(0, ε)`.
  obtain ⟨ε, hε, hεsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hΛlim.eventually_lt_const one_pos)
  have hε0 : 0 < ε := hε
  refine ⟨min (R / 8) (ε / 2), lt_min (by positivity) (by positivity), Λ, hΛlim, ?_⟩
  intro y hy t ht z hz
  have ht0 : 0 < t := ht.1
  have htR : t ≤ R / 8 := ht.2.trans (min_le_left _ _)
  have htε : t < ε := lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)
  have hΛ0 : 0 < Λ t := lt_of_lt_of_le ht0 (le_max_right _ _)
  have hΛ1 : Λ t ≤ 1 := (show Λ t < 1 from hεsub ⟨ht0, htε⟩).le
  -- Step 4: `B_t(z) ⊆ B̆_R(ξ)`, since `t + t + R/2 ≤ R/4 + R/2 < R`.
  have hsub : closedBall z t ⊆ ball ξ R := by
    intro w hw
    rw [mem_closedBall] at hw hz
    rw [mem_ball] at hy ⊢
    calc dist w ξ ≤ dist w z + dist z y + dist y ξ := dist_triangle4 w z y ξ
      _ < R := by linarith
  have hsubU : closedBall z t ⊆ U := hsub.trans (ball_subset_closedBall.trans hBU)
  have hsubo : ball z t ⊆ ball ξ R := ball_subset_closedBall.trans hsub
  -- Step 5: the hypotheses of `hM` at `(z, t, Λ(t))`.
  have hTP' : ∀ᵐ x ∂V.weight, x ∈ ball z t → ∃ P : Submodule ℝ (Amb n ℓ),
      Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection :=
    hTP.mono fun x hx hxb => hx (hsubo hxb)
  have hmeas' : AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball z t)) :=
    hmeas.mono_measure (Measure.restrict_mono hsubo le_rfl)
  -- `(t^{p-n} ∫_{B_t(z)} |H|ᵖ dμ_V)^{1/p} ≤ (t^{p-n} A)^{1/p} = t^β a ≤ κ Λ(t)`.
  have hLp' : V.scaledLpNorm H p z t ≤ ENNReal.ofReal (κ * Λ t) := by
    have hI : ∫⁻ x in closedBall z t, ‖H x‖ₑ ^ p ∂V.weight ≤ A :=
      lintegral_mono_set (hsub.trans ball_subset_closedBall)
    have htn : 0 ≤ t ^ (p - n) := Real.rpow_nonneg ht0.le _
    calc V.scaledLpNorm H p z t
        = (ENNReal.ofReal (t ^ (p - n)) * ∫⁻ x in closedBall z t, ‖H x‖ₑ ^ p ∂V.weight) ^
            (1 / p) := rfl
      _ ≤ (ENNReal.ofReal (t ^ (p - n)) * A) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hI) hp1
      _ = ENNReal.ofReal (t ^ (p - n)) ^ (1 / p) * A ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ hp1
      _ = ENNReal.ofReal (t ^ ((p - n) * (1 / p)) * a) := by
          rw [ENNReal.ofReal_rpow_of_nonneg htn hp1, hAa,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg htn _), Real.rpow_mul ht0.le]
      _ ≤ ENNReal.ofReal (κ * Λ t) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : t ^ ((p - n) * (1 / p)) * a / κ ≤ Λ t := le_max_left _ _
          have h2 := (div_le_iff₀ hκ).mp h1
          linarith [mul_comm (Λ t) κ]
  -- Step 6: apply `hM` at `(z, t, Λ(t))`.
  obtain ⟨F, hFb, -, hFmono, Θ, hΘ0, hΘd, hΘlim⟩ :=
    hM z t (Λ t) ht0 hsubU hTP' hmeas' hΛ0 hΛ1 hLp'
  refine ⟨Θ, hΘ0, hΘd, fun r hr => ?_⟩
  -- Step 7: `ω_n Θ ≤ Φ(r)`, as `Φ` is nondecreasing on `(0, t)` and `Φ(r') → ω_n Θ` (`r' → 0+`).
  have h7 : unitBallVolume n * Θ ≤
      F r * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + F r - 1 := by
    refine le_of_tendsto hΘlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr.1] with r' hr'
    exact hFmono ⟨hr'.1, hr'.2.trans hr.2⟩ hr hr'.2.le
  -- Step 8: `Φ(r) ≤ e^{Λ(t)} r⁻ⁿ μ_V(B_r(z)) + Λ(t)`, by `F(r) ≤ e^{Λ(t)}`, `|F(r) - 1| ≤ Λ(t)`.
  obtain ⟨hF1, -, hF3⟩ := hFb r hr
  have hm : 0 ≤ (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.1.le n)) ENNReal.toReal_nonneg
  have h8 : F r * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal ≤
      Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hF3 hm
  linarith [le_abs_self (F r - 1)]
/-- Upper semicontinuity of the density at `y`, in the form used in steps 5 and 7 of the proof of
Simon Ch. 5, Theorem 7.1 (cf. Ch. 4, 3.11 and 4.9).  Put `ω = ω_n > 0`, `b = Θy + (c − Θy)/3` and
pick `ε ∈ (0, 1/2]` with `a := (1 + 2ε)ⁿ b < c`.  The density at `y` gives `σ₁ > 0` with
`μ_V(B_s(y)) ≤ b ω sⁿ` for `s ∈ (0, σ₁)`.  As `Λ(t) → 0`, some `t ∈ (0, t₁]` with `t < σ₁` has
`e^{Λ(t)} a + Λ(t)/ω < c`; take `d = εt`.  For `z ∈ B_d(y)`, the monotonicity bound at `z` with
`r = t/2` and `B_{t/2}(z) ⊆ B_{t/2 + εt}(y)` give
`ω Θ ≤ e^{Λ(t)} (t/2)⁻ⁿ μ_V(B_{t/2}(z)) + Λ(t) ≤ e^{Λ(t)} ω a + Λ(t)`, so `Θ < c`. -/
theorem dohr_lmo_density_usc : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y : Amb n ℓ) (t₁ : ℝ) (Λ : ℝ → ℝ), 0 < t₁ → Tendsto Λ (𝓝[>] 0) (𝓝 0) → (∀ t ∈ Ioc 0 t₁, ∀ z ∈ closedBall y t, ∃ Θ : ℝ, 0 ≤ Θ ∧ V.HasDensity z Θ ∧ ∀ r ∈ Ioo 0 t, unitBallVolume n * Θ ≤ Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + Λ t) → ∀ Θy : ℝ, 0 ≤ Θy → V.HasDensity y Θy → ∀ c : ℝ, Θy < c → ∃ d > 0, ∀ z ∈ closedBall y d, ∃ Θ : ℝ, Θ < c ∧ V.HasDensity z Θ := by
  intro n ℓ U V y t₁ Λ ht₁ hΛ hmon Θy hΘy hy c hc
  -- `ω_n > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    apply div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    apply Real.Gamma_pos_of_pos
    positivity
  -- The levels `Θy < b < a' < c` and `ε ∈ (0, 1/2]` with `a := (1 + 2ε)ⁿ b < a'`.
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = Θy + (c - Θy) / 3 := ⟨_, rfl⟩
  obtain ⟨a', ha'_def⟩ : ∃ a' : ℝ, a' = Θy + 2 * (c - Θy) / 3 := ⟨_, rfl⟩
  have hb_pos : 0 < b := by rw [hb_def]; linarith
  have hΘb : Θy < b := by rw [hb_def]; linarith
  have hba' : b < a' := by rw [hb_def, ha'_def]; linarith
  have ha'c : a' < c := by rw [ha'_def]; linarith
  have hcont : Tendsto (fun ε : ℝ => (1 + 2 * ε) ^ n * b) (𝓝[>] 0) (𝓝 b) := by
    have h : Continuous (fun ε : ℝ => (1 + 2 * ε) ^ n * b) := by fun_prop
    have h0 := h.tendsto 0
    simp only [mul_zero, add_zero, one_pow, one_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hεev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + 2 * ε) ^ n * b < a' ∧ ε ∈ Ioc 0 (1 / 2) :=
    (hcont.eventually (eventually_lt_nhds hba')).and (Ioc_mem_nhdsGT (by norm_num))
  obtain ⟨ε, hεa, hε⟩ := hεev.exists
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (1 + 2 * ε) ^ n * b := ⟨_, rfl⟩
  have hac : a < c := by rw [ha_def]; linarith
  -- Mass bound at `y`: `μ_V(B_s(y)) ≤ b ω_n sⁿ` for `s ∈ (0, σ₁)`, from the density at `y`.
  have hlt : ENNReal.ofReal Θy < ENNReal.ofReal b :=
    (ENNReal.ofReal_lt_ofReal_iff hb_pos).2 hΘb
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hy (Iio_mem_nhds hlt))
  have hσ₁pos' : (0 : ℝ) < σ₁ := hσ₁pos
  have hmass : ∀ s ∈ Ioo 0 σ₁,
      V.weight (closedBall y s) ≤ ENNReal.ofReal (b * (unitBallVolume n * s ^ n)) := by
    intro s hs
    have h := hσ₁ hs
    simp only [mem_preimage, mem_Iio] at h
    have hne0 : ENNReal.ofReal (unitBallVolume n * s ^ n) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos hω (pow_pos hs.1 n)
    rw [ENNReal.div_lt_iff (Or.inl hne0) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul hb_pos.le] at h
    exact h.le
  -- Choice of `t ∈ (0, t₁]` with `t < σ₁` and `e^{Λ(t)} a + Λ(t)/ω_n < c`; then `d := ε t`.
  have hlim : Tendsto (fun t => Real.exp (Λ t) * a + Λ t / unitBallVolume n) (𝓝[>] 0)
      (𝓝 (Real.exp 0 * a + 0 / unitBallVolume n)) :=
    (((Real.continuous_exp.tendsto 0).comp hΛ).mul_const a).add (hΛ.div_const _)
  rw [Real.exp_zero, one_mul, zero_div, add_zero] at hlim
  obtain ⟨t, ⟨htc, ht⟩, htσ⟩ :=
    (((hlim.eventually (eventually_lt_nhds hac)).and (Ioc_mem_nhdsGT ht₁)).and
      (Ioo_mem_nhdsGT hσ₁pos')).exists
  have ht0 : 0 < t := ht.1
  refine ⟨ε * t, mul_pos hε.1 ht0, ?_⟩
  -- For `z ∈ B_{εt}(y) ⊆ B_t(y)`: the monotonicity bound at `z` with `r := t/2`.
  intro z hz
  have hzy : dist z y ≤ ε * t := mem_closedBall.1 hz
  have hεt : ε * t ≤ t / 2 := by
    have := mul_le_mul_of_nonneg_right hε.2 ht0.le
    linarith
  have hzt : z ∈ closedBall y t := mem_closedBall.2 (by linarith)
  obtain ⟨Θ, -, hΘz, hΘbound⟩ := hmon t ht z hzt
  refine ⟨Θ, ?_, hΘz⟩
  have key := hΘbound (t / 2) ⟨by linarith, by linarith⟩
  -- `B_{t/2}(z) ⊆ B_s(y)` with `s := t/2 + εt = (1 + 2ε) t/2 ≤ t < σ₁`, so
  -- `(t/2)⁻ⁿ μ_V(B_{t/2}(z)) ≤ (t/2)⁻ⁿ b ω_n sⁿ = ω_n a`.
  have hs : t / 2 + ε * t ∈ Ioo 0 σ₁ := by
    have := mul_pos hε.1 ht0
    exact ⟨by linarith, by linarith [htσ.2]⟩
  have hsub : closedBall z (t / 2) ⊆ closedBall y (t / 2 + ε * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hle := (measure_mono hsub).trans (hmass _ hs)
  have hreal : (V.weight (closedBall z (t / 2))).toReal ≤
      b * (unitBallVolume n * (t / 2 + ε * t) ^ n) :=
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hb_pos.le (mul_nonneg hω.le (pow_nonneg hs.1.le n))) hle
  have hs_eq : (t / 2 + ε * t) ^ n = (t / 2) ^ n * (1 + 2 * ε) ^ n := by
    rw [← mul_pow]; congr 1; ring
  have hpow : 0 < (t / 2) ^ n := pow_pos (by linarith) n
  have h6 : ((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal ≤ unitBallVolume n * a := by
    rw [inv_mul_le_iff₀ hpow]
    calc (V.weight (closedBall z (t / 2))).toReal
        ≤ b * (unitBallVolume n * (t / 2 + ε * t) ^ n) := hreal
      _ = (t / 2) ^ n * (unitBallVolume n * a) := by rw [hs_eq, ha_def]; ring
  -- Hence `ω_n Θ ≤ e^{Λ(t)} ω_n a + Λ(t)`, i.e. `Θ ≤ e^{Λ(t)} a + Λ(t)/ω_n < c`.
  have h7 : unitBallVolume n * Θ ≤ Real.exp (Λ t) * (unitBallVolume n * a) + Λ t :=
    calc unitBallVolume n * Θ
        ≤ Real.exp (Λ t) * ((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal + Λ t := key
      _ = Real.exp (Λ t) * (((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal) + Λ t := by
          ring
      _ ≤ Real.exp (Λ t) * (unitBallVolume n * a) + Λ t := by
          gcongr
  have h8 : Θ ≤ Real.exp (Λ t) * a + Λ t / unitBallVolume n :=
    calc Θ ≤ (Real.exp (Λ t) * (unitBallVolume n * a) + Λ t) / unitBallVolume n :=
          (le_div_iff₀' hω).2 h7
      _ = Real.exp (Λ t) * a + Λ t / unitBallVolume n := by
          rw [add_div, mul_div_assoc, mul_div_cancel_left₀ a hω.ne']
  linarith
/-- **Besicovitch differentiation of a density measure against a gauge** (a step in the proof of
Simon Ch. 5, Theorem 7.1, second assertion: density equals multiplicity a.e.).  If `ν` is a locally
finite measure on `ℝ^{n+ℓ}`, `f` is `ν`-a.e. measurable and `ν ⌞ f` (`ν.withDensity f`) is locally
finite, then for `ν`-a.e. `y` and every gauge `c` with `ν(B_r(y)) / c(r) → 1` as `r ↓ 0`, also
`(ν ⌞ f)(B_r(y)) / c(r) → f(y)`.
Proof: Besicovitch differentiation gives `(ν ⌞ f)(B_r(y)) / ν(B_r(y)) → D_ν(ν ⌞ f)(y) = f(y)` for
`ν`-a.e. `y`.  For such `y`, eventually `ν(B_r(y)) / c(r) > 0`, so `ν(B_r(y)) ≠ 0`, while
`ν(B_r(y)) < ∞` (closed balls are compact); hence
`(ν ⌞ f)(B_r(y)) / c(r) = [(ν ⌞ f)(B_r(y)) / ν(B_r(y))] · [ν(B_r(y)) / c(r)] → f(y) · 1`. -/
theorem dohr_lmo_dema_withDensity_density_ae : ∀ n ℓ : ℕ, ∀ (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ≥0∞), IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure (ν.withDensity f) → AEMeasurable f ν → ∀ᵐ y ∂ν, ∀ c : ℝ → ℝ≥0∞, Tendsto (fun r : ℝ => ν (closedBall y r) / c r) (𝓝[>] 0) (𝓝 1) → Tendsto (fun r : ℝ => (ν.withDensity f) (closedBall y r) / c r) (𝓝[>] 0) (𝓝 (f y)) := by
  intro n ℓ ν f hν hρ hf
  -- Besicovitch differentiation of `ν ⌞ f` with respect to `ν` (σ-finite, being locally finite),
  -- and `D_ν(ν ⌞ f) = f` `ν`-a.e.
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.withDensity f) ν,
    Measure.rnDeriv_withDensity₀ ν hf] with y hy hfy c hc
  rw [hfy] at hy
  -- Eventually `ν(B_r(y)) / c(r) > 0`, so `0 < ν(B_r(y)) < ∞` and the ratio factors.
  have heq : (fun r : ℝ => (ν.withDensity f) (closedBall y r) / ν (closedBall y r) *
      (ν (closedBall y r) / c r)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun r : ℝ => (ν.withDensity f) (closedBall y r) / c r := by
    filter_upwards [hc.eventually (lt_mem_nhds zero_lt_one)] with r hr
    exact ENNReal.div_mul_div_cancel (ENNReal.div_pos_iff.1 hr).1 measure_closedBall_lt_top.ne
  -- The two factors tend to `f(y)` and `1`.
  have hlim := ENNReal.Tendsto.mul hy (Or.inr ENNReal.one_ne_top) hc (Or.inl one_ne_zero)
  rw [mul_one] at hlim
  exact hlim.congr' heq
/-- The weight measure restricted to a measurable `O ⊆ U` is `Hⁿ` on `spt V ∩ O` with density
`1_M θ`: `μ_V ⌞ O = (Hⁿ ⌞ (spt V ∩ O)).withDensity (ofReal ∘ 1_M θ)`.
Proof: `spt V ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is measurable since `spt μ_V` is closed, and
`μ_V((spt μ_V)ᶜ) = 0`, so `μ_V(S ∩ O) = μ_V(S ∩ (spt V ∩ O))` for measurable `S`.  Both sides then
equal `∫ θ dHⁿ` over `S ∩ (spt V ∩ O) ∩ M`, by `withDensity_apply`, `restrict_restrict` and, on
the right, `lintegral_indicator₀`/`restrict_restrict₀` for the `Hⁿ`-null-measurable carrier `M`. -/
theorem dohr_lmo_dema_weight_restrict_withDensity : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → O ⊆ U → V.weight.restrict O = ((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)).withDensity (fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)) := by
  intro n ℓ U V O hO hOU
  -- `spt V ∩ O = spt μ_V ∩ O` is measurable.
  have hA : V.support ∩ O = V.weight.support ∩ O := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hOU hx.2, hx.1⟩, hx.2⟩⟩
  have hAm : MeasurableSet (V.support ∩ O) := by
    rw [hA]
    exact V.weight.isClosed_support.measurableSet.inter hO
  ext S hS
  have hSA : MeasurableSet (S ∩ (V.support ∩ O)) := hS.inter hAm
  rw [Measure.restrict_apply hS, withDensity_apply _ hS, Measure.restrict_restrict hS]
  -- `μ_V` vanishes off its support, so `μ_V(S ∩ O) = μ_V(S ∩ (spt V ∩ O))`.
  have hSO : V.weight (S ∩ O) = V.weight (S ∩ (V.support ∩ O)) := by
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ inter_subset_right))
    calc V.weight (S ∩ O)
        ≤ V.weight (S ∩ (V.support ∩ O) ∪ V.weight.supportᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hx' : x ∈ V.weight.support
          · exact Or.inl ⟨hx.1, hA ▸ ⟨hx', hx.2⟩⟩
          · exact Or.inr hx'
      _ ≤ V.weight (S ∩ (V.support ∩ O)) + V.weight V.weight.supportᶜ := measure_union_le _ _
      _ = V.weight (S ∩ (V.support ∩ O)) := by rw [Measure.measure_compl_support, add_zero]
  rw [hSO, RectifiableVarifold.weight, withDensity_apply _ hSA, Measure.restrict_restrict hSA]
  -- On the right, `ofReal (1_M θ) = 1_M (ofReal ∘ θ)` and `M` is null-measurable.
  have hf : (fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)) =
      V.carrier.indicator (fun x => ENNReal.ofReal (V.mult x)) := by
    funext x
    by_cases hx : x ∈ V.carrier <;> simp [hx]
  have hM : NullMeasurableSet V.carrier
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ (V.support ∩ O))) :=
    V.nullMeasurableSet_carrier.mono Measure.restrict_le_self
  rw [hf, lintegral_indicator₀ hM, Measure.restrict_restrict₀ hM, inter_comm]
/-- Simon Ch. 5, 7.1, second assertion (local multiplicity step): **density equals multiplicity
almost everywhere**.  Let `O = B̆_{r₀}(y₀)` with `B_{r₀}(y₀) ⊆ U`, write `Σ = spt V`, and suppose
`Hⁿ(Σ ∩ O) < ∞` and `Hⁿ(Σ ∩ B_r(y)) / (ω_n rⁿ) → 1` as `r ↓ 0` for every `y ∈ Σ ∩ O`.  Then
(a) `Θⁿ(μ_V, y) = θ(y)` for `μ_V`-a.e. `y ∈ O`, and (b) `Θⁿ(μ_V, y) = 0` for `Hⁿ`-a.e.
`y ∈ (Σ ∩ O) \ M`.  With `ν = Hⁿ ⌞ (Σ ∩ O)` and `f = 1_M θ` we have `μ_V ⌞ O = ν ⌞ f`, so
Besicovitch differentiation together with the unit density of `ν` gives `Θⁿ(μ_V, y) = f(y)` for
`ν`-a.e. `y`; this is (b), and (a) follows because `μ_V ⌞ O ≪ ν` and `μ_V` is carried by `M`. -/
theorem dohr_lmo_density_eq_mult_ae : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y₀ : Amb n ℓ) (r₀ : ℝ), closedBall y₀ r₀ ⊆ U → (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ ball y₀ r₀) < ⊤ → (∀ y ∈ V.support ∩ ball y₀ r₀, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ᵐ y ∂V.weight, y ∈ ball y₀ r₀ → V.HasDensity y (V.mult y)) ∧ ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball y₀ r₀)), y ∉ V.carrier → V.HasDensity y 0 := by
  intro n ℓ U V y₀ r₀ hBU hfin hdens
  -- Notation: `O = B̆_{r₀}(y₀)`, `ν = Hⁿ ⌞ (Σ ∩ O)` and `f = ofReal ∘ 1_M θ`.
  set O : Set (Amb n ℓ) := ball y₀ r₀
  set ν : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O) with hν_def
  set f : Amb n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)
  have hOm : MeasurableSet O := measurableSet_ball
  have hOU : O ⊆ U := ball_subset_closedBall.trans hBU
  -- Step 1: `μ_V ⌞ O = ν ⌞ f`.
  have hrestr : V.weight.restrict O = ν.withDensity f :=
    Submission.dohr_lmo_dema_weight_restrict_withDensity n ℓ U V O hOm hOU
  -- Step 2: `ν` is finite by hypothesis, and `μ_V ⌞ O` is finite because `θ` is integrable on
  -- `M ∩ B_{r₀}(y₀)` (`B_{r₀}(y₀) ⊆ U` is compact); `f` is `ν`-a.e. measurable.
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin.ne
  have hBfin : V.weight (closedBall y₀ r₀) < ⊤ := by
    unfold RectifiableVarifold.weight
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall _ _) hBU).lintegral_lt_top
  have : IsFiniteMeasure (ν.withDensity f) := by
    rw [← hrestr]
    exact isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono ball_subset_closedBall) hBfin).ne
  have hfm : AEMeasurable f ν :=
    (((aemeasurable_indicator_iff₀ V.nullMeasurableSet_carrier).mpr
      V.aemeasurable_mult).mono_measure Measure.restrict_le_self).ennreal_ofReal
  -- `Σ ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is a Borel set.
  have hAm : MeasurableSet (V.support ∩ O) := by
    have hA : V.support ∩ O = V.weight.support ∩ O := by
      ext x
      simp only [RectifiableVarifold.support, mem_inter_iff]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hOU h.2, h.1⟩, h.2⟩⟩
    rw [hA]
    exact Measure.isClosed_support.measurableSet.inter hOm
  -- Step 3: `Θⁿ(μ_V, y) = f(y)` for `ν`-a.e. `y`, using the gauge `c(r) = ω_n rⁿ`: for
  -- `0 < r < r₀ - |y - y₀|` we have `B_r(y) ⊆ O`, so `ν(B_r(y)) = Hⁿ(Σ ∩ B_r(y))` and
  -- `(ν ⌞ f)(B_r(y)) = μ_V(B_r(y))`.
  have hmain : ∀ᵐ y ∂ν, V.HasDensity y (V.carrier.indicator V.mult y) := by
    filter_upwards [Submission.dohr_lmo_dema_withDensity_density_ae n ℓ ν f inferInstance
      inferInstance hfm, (ae_restrict_mem hAm : ∀ᵐ y ∂ν, y ∈ V.support ∩ O)] with y hy hyA
    have hδ : 0 < r₀ - dist y y₀ := sub_pos.mpr (mem_ball.mp hyA.2)
    have hsub : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall y r ⊆ O := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
      exact closedBall_subset_ball' (by linarith [hr.2])
    have hν1 : Tendsto (fun r : ℝ => ν (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) (𝓝 1) := by
      refine (hdens y hyA).congr' ?_
      filter_upwards [hsub] with r hr
      have hBr : closedBall y r ∩ (V.support ∩ O) = V.support ∩ closedBall y r := by
        ext x
        simp only [mem_inter_iff]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hr h.2⟩⟩
      rw [hν_def, Measure.restrict_apply measurableSet_closedBall, hBr]
    refine (hy (fun r : ℝ => ENNReal.ofReal (unitBallVolume n * r ^ n)) hν1).congr' ?_
    filter_upwards [hsub] with r hr
    rw [← hrestr, Measure.restrict_apply measurableSet_closedBall, Set.inter_eq_left.mpr hr]
  refine ⟨?_, ?_⟩
  · -- (a): `μ_V ⌞ O ≪ ν` transfers Step 3 to `μ_V`-a.e. `y ∈ O`, and `μ_V`-a.e. `y` lies in `M`.
    have hM : ∀ᵐ y ∂V.weight, y ∈ V.carrier :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
    have hO : ∀ᵐ y ∂V.weight.restrict O, V.HasDensity y (V.carrier.indicator V.mult y) := by
      rw [hrestr]
      exact (withDensity_absolutelyContinuous ν f).ae_le hmain
    filter_upwards [(ae_restrict_iff' hOm).mp hO, hM] with y hy hyM hyO
    have h := hy hyO
    rwa [Set.indicator_of_mem hyM] at h
  · -- (b): off `M` the density `1_M θ` vanishes.
    filter_upwards [hmain] with y hy hyM
    rwa [Set.indicator_of_notMem hyM] at hy
/-- `μ_V`-null subsets of the carrier are `Hⁿ`-null: if `A ⊆ M` and `μ_V(A) = 0`, then
`Hⁿ(A) = 0`.  `μ_V = Hⁿ ⌞ M` with density `θ`, so `μ_V(A) = 0` forces `θ = 0` `Hⁿ ⌞ M`-a.e. on `A`;
as `θ > 0` on `M ⊇ A`, the set `A` itself is `Hⁿ ⌞ M`-null, hence `Hⁿ`-null. -/
theorem dohr_lmo_hausdorff_null_of_weight_null : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (A : Set (Amb n ℓ)), A ⊆ V.carrier → V.weight A = 0 → (μHE[n] : Measure (Amb n ℓ)) A = 0 := by
  intro n ℓ U V A hA hw
  -- `μ_V(A) = 0` with the a.e.-measurable density `ofReal ∘ θ`: `{θ > 0} ∩ A` is `Hⁿ ⌞ M`-null.
  have h0 : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier)
      ({x | ENNReal.ofReal (V.mult x) ≠ 0} ∩ A) = 0 :=
    (withDensity_apply_eq_zero' V.aemeasurable_mult.ennreal_ofReal).mp hw
  -- `A` lies in this set and in `M`, since `A ⊆ M` and `θ > 0` on `M`.
  have hsub : A ⊆ ({x | ENNReal.ofReal (V.mult x) ≠ 0} ∩ A) ∩ V.carrier := fun x hx =>
    ⟨⟨(ENNReal.ofReal_pos.mpr (V.mult_pos x (hA hx))).ne', hx⟩, hA hx⟩
  exact measure_mono_null hsub (nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply _ _).trans h0.le))
/-- Carrier versus support (step 6 of the local multiplicity-one argument for Simon 7.1): let
`O ⊆ U` be measurable, let `Hⁿ`-a.e. point of `spt V ∩ O` off `M` have density `0`, and let
every point of `spt V ∩ O` have a density `Θ ≥ 1`. Then `Hⁿ((M ∩ O) ∆ (spt V ∩ O)) = 0`.
`(M ∩ O) \ spt V` lies outside `spt μ_V`, so it is `μ_V`-null; since it lies inside `M`, the
sibling `dohr_lmo_hausdorff_null_of_weight_null` makes it `Hⁿ`-null. On `(spt V ∩ O) \ M`,
`Hⁿ`-a.e. point would have both density `0` and density `Θ ≥ 1`, which uniqueness of limits
rules out. -/
theorem dohr_lmo_carrier_support_null : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → O ⊆ U → (∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)), y ∉ V.carrier → V.HasDensity y 0) → (∀ y ∈ V.support ∩ O, ∃ Θ : ℝ, 1 ≤ Θ ∧ V.HasDensity y Θ) → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ O) (V.support ∩ O)) = 0 := by
  intro n ℓ U V O hO hOU hzero hdens
  rw [Set.symmDiff_def]
  refine measure_union_null ?_ ?_
  · -- `(M ∩ O) \ (spt V ∩ O)` lies in `M` and, as `O ⊆ U`, outside `spt μ_V`.
    refine Submission.dohr_lmo_hausdorff_null_of_weight_null n ℓ U V _ (fun x hx => hx.1.1)
      (measure_mono_null ?_ (Measure.measure_compl_support (μ := V.weight)))
    rintro x ⟨⟨-, hxO⟩, hxS⟩ hxμ
    exact hxS ⟨⟨hOU hxO, hxμ⟩, hxO⟩
  · -- `spt V ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is measurable.
    have hmeas : MeasurableSet (V.support ∩ O) := by
      have h : V.support ∩ O = V.weight.support ∩ O := by
        ext x
        exact ⟨fun ⟨⟨_, hx⟩, hxO⟩ => ⟨hx, hxO⟩, fun ⟨hx, hxO⟩ => ⟨⟨hOU hxO, hx⟩, hxO⟩⟩
      rw [h]
      exact (Measure.isClosed_support (μ := V.weight)).measurableSet.inter hO
    -- A.e. point of `spt V ∩ O` lies in `M`: off `M` it would have densities `0` and `Θ ≥ 1`.
    have hae : ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)), y ∈ V.carrier := by
      filter_upwards [ae_restrict_mem hmeas, hzero] with y hy hy0
      by_contra hyM
      obtain ⟨Θ, hΘ, hyΘ⟩ := hdens y hy
      have h := tendsto_nhds_unique (hy0 hyM) hyΘ
      rw [ENNReal.ofReal_zero, eq_comm, ENNReal.ofReal_eq_zero] at h
      linarith
    refine measure_mono_null (t := V.carrierᶜ ∩ (V.support ∩ O)) ?_ ?_
    · rintro x ⟨hx, hxM⟩
      exact ⟨fun h => hxM ⟨h, hx.2⟩, hx⟩
    · exact nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans (ae_iff.1 hae).le)
/-- **`μ_V ⌞ O = Hⁿ ⌞ (spt V ∩ O)` where `θ = 1`** (node
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.weight_restrict_eq-a1`; step 10 of
`dohr_local_multiplicity_one`).  If `θ = 1` `μ_V`-a.e. on the measurable set `O` and
`Hⁿ((M ∩ O) ∆ (spt V ∩ O)) = 0`, then `μ_V ⌞ O = Hⁿ ⌞ (spt V ∩ O)`.

`N = {x ∈ M ∩ O : θ(x) ≠ 1}` is `μ_V`-null, hence `Hⁿ`-null by
`dohr_lmo_hausdorff_null_of_weight_null`.  For measurable `S`,
`μ_V(S ∩ O) = ∫_{S ∩ O ∩ M} θ dHⁿ = Hⁿ(S ∩ O ∩ M)` since `θ = 1` `Hⁿ`-a.e. on `S ∩ O ∩ M`, and
`Hⁿ(S ∩ O ∩ M) = Hⁿ(S ∩ (spt V ∩ O))` since `M ∩ O = spt V ∩ O` up to an `Hⁿ`-null set. -/
theorem dohr_lmo_weight_restrict_eq : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → (∀ᵐ x ∂V.weight, x ∈ O → V.mult x = 1) → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ O) (V.support ∩ O)) = 0 → V.weight.restrict O = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O) := by
  intro n ℓ U V O hO hθ hsd
  /- Step 1: `N = {x ∈ M ∩ O : θ(x) ≠ 1}` is `μ_V`-null, hence `Hⁿ`-null. -/
  have hNw : V.weight {x | x ∈ V.carrier ∩ O ∧ V.mult x ≠ 1} = 0 := by
    have hθ' := ae_iff.1 hθ
    refine measure_mono_null ?_ hθ'
    intro x hx
    show ¬(x ∈ O → V.mult x = 1)
    exact fun h' => hx.2 (h' hx.1.2)
  have hNH : (μHE[n] : Measure (Amb n ℓ)) {x | x ∈ V.carrier ∩ O ∧ V.mult x ≠ 1} = 0 :=
    Submission.dohr_lmo_hausdorff_null_of_weight_null n ℓ U V _ (fun x hx => hx.1.1) hNw
  ext S hS
  /- Step 2: `μ_V(S ∩ O) = ∫_{S ∩ O ∩ M} θ dHⁿ`. -/
  have hSO : MeasurableSet (S ∩ O) := hS.inter hO
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS, RectifiableVarifold.weight,
    withDensity_apply _ hSO, Measure.restrict_restrict hSO]
  /- Step 3: `θ = 1` `Hⁿ`-a.e. on `S ∩ O ∩ M`, so the integral is `Hⁿ(S ∩ O ∩ M)`. -/
  have hX : NullMeasurableSet (S ∩ O ∩ V.carrier) (μHE[n] : Measure (Amb n ℓ)) :=
    hSO.nullMeasurableSet.inter V.nullMeasurableSet_carrier
  have h1 : ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O ∩ V.carrier),
      ENNReal.ofReal (V.mult x) = 1 := by
    filter_upwards [ae_restrict_mem₀ hX,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hNH)] with x hxX hxN
    have hx1 : V.mult x = 1 := by
      by_contra h
      exact hxN ⟨⟨hxX.2, hxX.1.2⟩, h⟩
    rw [hx1, ENNReal.ofReal_one]
  rw [lintegral_congr_ae h1, setLIntegral_one]
  /- Steps 4–5: `S ∩ O ∩ M = S ∩ (spt V ∩ O)` up to the `Hⁿ`-null `(M ∩ O) ∆ (spt V ∩ O)`. -/
  have h2 : S ∩ (V.carrier ∩ O) =ᵐ[(μHE[n] : Measure (Amb n ℓ))] S ∩ (V.support ∩ O) :=
    EventuallyEqSet.rfl.inter (measure_symmDiff_eq_zero_iff.1 hsd)
  rw [inter_assoc, inter_comm O]
  exact measure_congr h2
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one): carrier versus graph on
`B̆_ρ(0)`.  Put `τ z = z − ξ`; `Q ∘ τ` is an isometry.  If `Q(τ(S)) ∩ B̆_R(0)` is the graph of `u`
over `B̆ⁿ_R(0)` (inside `B̆_R(0)`), `s ≤ R` and `Hⁿ((M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))) = 0`, then for
`ρ ∈ (0, s]` the set `Q(τ(M)) ∩ B̆_ρ(0)` agrees `Hⁿ`-a.e. with the graph of `u` over
`{x ∈ B̆ⁿ_ρ(0) : |(x, u(x))| < ρ}`: by `|x| ≤ |(x, u(x))|`, their symmetric difference lies in
`Q(τ((M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))))`, which is `Hⁿ`-null. -/
theorem dohr_lmo_carrier_graph_symmDiff : ∀ n ℓ : ℕ, ∀ (M S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R s : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), s ≤ R → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (M ∩ ball ξ s) (S ∩ ball ξ s)) = 0 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' M) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0 := by
  intro n ℓ M S ξ R s Q u hsR hgraph hnull ρ hρ hρs
  -- `‖x‖ ≤ ‖(x, y)‖`, since `‖(x, y)‖² = ‖x‖² + ‖y‖²`.
  have hnorm : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := by
    intro x y
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    rw [Fin.sum_univ_add]
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_left, Fin.append_right]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  -- `‖Q (z - ξ)‖ = ‖z - ξ‖`.
  have hQ : ∀ z : Amb n ℓ, ‖Q (z - ξ)‖ = ‖z - ξ‖ := fun z => Q.norm_map _
  -- The set in the claim lies in `Q (τ (Z))`, `Z = (M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))`, `τ z = z - ξ`.
  have hsub : symmDiff (Q '' ((fun x => x - ξ) '' M) ∩ ball 0 ρ)
      (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ}) ⊆
      Q '' ((fun x => x - ξ) '' symmDiff (M ∩ ball ξ s) (S ∩ ball ξ s)) := by
    intro w hw
    rcases mem_symmDiff.mp hw with ⟨⟨⟨_, ⟨z, hzM, rfl⟩, rfl⟩, hwρ⟩, hwG⟩ | ⟨⟨x, hxW, rfl⟩, hwM⟩
    · -- `w = Q (z - ξ)` with `z ∈ M`, `‖z - ξ‖ < ρ`, and `w` off the graph part.
      rw [mem_ball_zero_iff, hQ] at hwρ
      refine ⟨z - ξ, ⟨z, mem_symmDiff.mpr (Or.inl ⟨⟨hzM, ?_⟩, ?_⟩), rfl⟩, rfl⟩
      · exact mem_ball_iff_norm.mpr (hwρ.trans_le hρs)
      · rintro ⟨hzS, -⟩
        have hw : Q (z - ξ) ∈ Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R :=
          ⟨⟨z - ξ, ⟨z, hzS, rfl⟩, rfl⟩,
            mem_ball_zero_iff.mpr ((hQ z).trans_lt (hwρ.trans_le (hρs.trans hsR)))⟩
        rw [hgraph] at hw
        obtain ⟨⟨x, -, hx⟩, -⟩ := hw
        have hxρ : ‖graphPoint x (u x)‖ < ρ := by
          rw [show graphPoint x (u x) = Q (z - ξ) from hx, hQ]; exact hwρ
        exact hwG ⟨x, ⟨mem_ball_zero_iff.mpr ((hnorm x (u x)).trans_lt hxρ), hxρ⟩, hx⟩
    · -- `w = (x, u x)` with `‖x‖ < ρ`, `‖(x, u x)‖ < ρ`, and `w` off the carrier part.
      obtain ⟨hxρ, hGρ⟩ := hxW
      have hw : graphPoint x (u x) ∈ graphOver u (ball 0 R) ∩ ball 0 R :=
        ⟨⟨x, mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hxρ).trans_le (hρs.trans hsR)), rfl⟩,
          mem_ball_zero_iff.mpr (hGρ.trans_le (hρs.trans hsR))⟩
      rw [← hgraph] at hw
      obtain ⟨⟨_, ⟨z, hzS, rfl⟩, hz⟩, -⟩ := hw
      have hzρ : ‖z - ξ‖ < ρ := by rw [← hQ, hz]; exact hGρ
      refine ⟨z - ξ, ⟨z, mem_symmDiff.mpr (Or.inr ⟨⟨hzS, ?_⟩, ?_⟩), rfl⟩, hz⟩
      · exact mem_ball_iff_norm.mpr (hzρ.trans_le hρs)
      · rintro ⟨hzM, -⟩
        exact hwM ⟨⟨z - ξ, ⟨z, hzM, rfl⟩, hz⟩, mem_ball_zero_iff.mpr hGρ⟩
  -- `Q` and `τ` are isometries, so `Hⁿ(Q (τ (Z))) = Hⁿ(Z) = 0`.
  have hτ : Isometry (fun x : Amb n ℓ => x - ξ) :=
    Isometry.of_dist_eq fun a b => dist_sub_right a b ξ
  refine measure_mono_null hsub ?_
  rw [Q.isometry.euclideanHausdorffMeasure_image, hτ.euclideanHausdorffMeasure_image]
  exact hnull
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
/-- **Uniform first-order approximation of a `C¹` map** (step 2 of the density-one argument for
`C¹` graphs in Simon 7.1, in two-point form).  If `u` is `C¹` on the open set `U ⊆ ℝⁿ` and
`x₀ ∈ U`, then for every `ε > 0` there is `η > 0` with `B_η(x₀) ⊆ U` and
`|u(x) − u(y) − Du(x₀)(x − y)| ≤ ε |x − y|` for all `x, y ∈ B_η(x₀)`: by continuity of `Du` at `x₀`
choose `η` with `‖Du(z) − Du(x₀)‖ ≤ ε` on `B_η(x₀) ⊆ U`, and apply the mean value inequality on the
convex ball `B_η(x₀)`. -/
theorem dohr_c1_uniform_first_order : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiffOn ℝ 1 u U → ∀ x₀ ∈ U, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ closedBall x₀ η ⊆ U ∧ ∀ x ∈ closedBall x₀ η, ∀ y ∈ closedBall x₀ η, ‖u x - u y - fderiv ℝ u x₀ (x - y)‖ ≤ ε * ‖x - y‖ := by
  intro n ℓ U u hU hu x₀ hx₀ ε hε
  -- `u` is differentiable at every point of the open set `U`, and `Du` is continuous at `x₀`.
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hca : ContinuousAt (fderiv ℝ u) x₀ :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx₀)
  -- `B̆_{η₁}(x₀) ⊆ U`, `‖Du(z) − Du(x₀)‖ < ε` for `|z − x₀| < η₂`; take `η = min(η₁, η₂)/2`.
  obtain ⟨η₁, hη₁, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨η₂, hη₂, hclose⟩ := Metric.continuousAt_iff.1 hca ε hε
  have hη : min η₁ η₂ / 2 < min η₁ η₂ := half_lt_self (lt_min hη₁ hη₂)
  have hsub : closedBall x₀ (min η₁ η₂ / 2) ⊆ U := fun z hz =>
    hball (mem_ball.2 ((mem_closedBall.1 hz).trans_lt (hη.trans_le (min_le_left η₁ η₂))))
  refine ⟨min η₁ η₂ / 2, half_pos (lt_min hη₁ hη₂), hsub, fun x hx y hy => ?_⟩
  -- Mean value inequality on the convex ball, measured against the fixed linear map `Du(x₀)`.
  refine (convex_closedBall x₀ _).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hdiff z (hsub hz)).hasFDerivAt.hasFDerivWithinAt) (fun z hz => ?_) hy hx
  rw [← dist_eq_norm]
  exact (hclose ((mem_closedBall.1 hz).trans_lt (hη.trans_le (min_le_right η₁ η₂)))).le

/-- **Two-sided mass pinching for `C¹` graphs** (towards `Θⁿ = 1` on `C¹` graphs, for Simon Ch. 5,
Theorem 7.1).  If `u` is `C¹` on `B̆_R(0) ⊆ ℝⁿ`, `x ∈ B̆_R(0)` and `0 < ε < 1`, then for all small
`r > 0` the graph `Γ = graph(u|B̆_R(0))` satisfies
`((1-ε)/(1+ε))ⁿ ω_n rⁿ ≤ Hⁿ(Γ ∩ B_r((x, u(x)))) ≤ ((1+ε)/(1-ε))ⁿ ω_n rⁿ`.
With `G(z) = (z, u(z))` and the tangent map `L v = (v, Du(x) v)`, the uniform first-order estimate
gives `(1-ε)|L(z-z')| ≤ |G(z) - G(z')| ≤ (1+ε)|L(z-z')|` near `x`.  Hence `Γ ∩ B_r((x, u(x)))` is
squeezed between `G`-images of `x + E_{r/(1+ε)}` and `x + E_{r/(1-ε)}`, `E_t = {v : |L v| ≤ t}`,
and `L(E_t)` is the closed `t`-ball of the `n`-plane `range L`, of measure `ω_n tⁿ`.  The two
comparisons use `Hⁿ(f(S)) ≤ Kⁿ Hⁿ(S)` for the `K`-Lipschitz maps `w ↦ G(x + π w)` (`K = 1+ε`) and
`z ↦ L(π z - x)` (`K = (1-ε)⁻¹`), where `π` is the projection onto the first `n` coordinates. -/
theorem dohr_c1_graph_mass_pinching : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ η → ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) ≤ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ∧ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ≤ ENNReal.ofReal ((1 + ε) ^ n / (1 - ε) ^ n * (unitBallVolume n * r ^ n)) := by
  intro n ℓ hn R u hu x₀ hx₀ ε hε hε1
  set P : Rn n →L[ℝ] Rn ℓ := fderiv ℝ u x₀ with hP
  have h1ε : 0 < 1 - ε := by linarith
  -- (1) Graph-coordinate algebra: `(x, y)` is linear and `|(x, y)|² = |x|² + |y|²`.
  have gp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint x y - graphPoint x' y' = graphPoint (x - x') (y - y') := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_add : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_smul : ∀ (c : ℝ) (x : Rn n) (y : Rn ℓ),
      graphPoint (c • x) (c • y) = c • graphPoint x y := by
    intro c x y
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_norm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have gp_le : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := fun x y =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg ‖y‖)).trans (gp_norm x y).ge)
  have gp_zero : ∀ y : Rn ℓ, ‖graphPoint (0 : Rn n) y‖ = ‖y‖ := by
    intro y
    have h := gp_norm 0 y
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  -- (2) The first-coordinate projection `π` and the tangent map `L v = (v, P v)`.
  let π : Amb n ℓ → Rn n := fun w => WithLp.toLp 2 (fun i : Fin n => w (Fin.castAdd ℓ i))
  have hπ : ∀ (x : Rn n) (y : Rn ℓ), π (graphPoint x y) = x := by
    intro x y
    ext i
    simp [π, graphPoint]
  let L : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (P v)
      map_add' := fun v w => by
        simp only [map_add]
        exact gp_add v w (P v) (P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        exact gp_smul c v (P v) }
  have hL : ∀ v, L v = graphPoint v (P v) := fun v => rfl
  have hLle : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => gp_le v (P v)
  have hLinj : Function.Injective L := by
    intro v w h
    have := hLle (v - w)
    rw [map_sub, h, sub_self, norm_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hπL : ∀ v, π (L v) = v := fun v => hπ v (P v)
  let G : Rn n → Amb n ℓ := fun x => graphPoint x (u x)
  have hπG : ∀ x, π (G x) = x := fun x => hπ x (u x)
  have hGsub : ∀ x x', G x - G x' = graphPoint (x - x') (u x - u x') := fun x x' => gp_sub _ _ _ _
  have hGdist : ∀ x x', ‖x - x'‖ ≤ ‖G x - G x'‖ := by
    intro x x'
    rw [hGsub]
    exact gp_le _ _
  -- (3) First-order estimate on the closed ball `B = B_{η₀}(x₀)`:
  -- `(1-ε)|L(x-x')| ≤ |G(x) - G(x')| ≤ (1+ε)|L(x-x')|`.
  obtain ⟨η₀, hη₀, hB, hest⟩ :=
    Submission.dohr_c1_uniform_first_order n ℓ (ball 0 R) u isOpen_ball hu x₀ hx₀ ε hε
  have hGL : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x' - L (x - x')‖ ≤ ε * ‖L (x - x')‖ := by
    intro x hx x' hx'
    have h1 : G x - G x' - L (x - x') = graphPoint 0 (u x - u x' - P (x - x')) := by
      rw [hGsub, hL, gp_sub, sub_self]
    rw [h1, gp_zero]
    exact (hest x hx x' hx').trans (mul_le_mul_of_nonneg_left (hLle _) hε.le)
  have hup : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x'‖ ≤ (1 + ε) * ‖L (x - x')‖ := by
    intro x hx x' hx'
    calc ‖G x - G x'‖ = ‖(G x - G x' - L (x - x')) + L (x - x')‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - G x' - L (x - x')‖ + ‖L (x - x')‖ := norm_add_le _ _
      _ ≤ ε * ‖L (x - x')‖ + ‖L (x - x')‖ := by gcongr; exact hGL x hx x' hx'
      _ = (1 + ε) * ‖L (x - x')‖ := by ring
  have hlow : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      (1 - ε) * ‖L (x - x')‖ ≤ ‖G x - G x'‖ := by
    intro x hx x' hx'
    have : ‖L (x - x')‖ ≤ ‖G x - G x'‖ + ‖G x - G x' - L (x - x')‖ := by
      calc ‖L (x - x')‖ = ‖(G x - G x') - (G x - G x' - L (x - x'))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    nlinarith [hGL x hx x' hx']
  -- (4) Choice of `η = (1-ε)η₀`, localization `Γ ∩ B_r(G(x₀)) = G(D)` and the ellipsoid sandwich
  -- `x₀ + E_{r/(1+ε)} ⊆ D ⊆ x₀ + E_{r/(1-ε)}`.
  refine ⟨(1 - ε) * η₀, mul_pos h1ε hη₀, ?_⟩
  intro r hr hrη
  have hrη₀ : r / (1 - ε) ≤ η₀ := by rw [div_le_iff₀ h1ε]; linarith
  have hrη₀' : r / (1 + ε) ≤ η₀ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let D : Set (Rn n) := ball 0 R ∩ G ⁻¹' closedBall (G x₀) r
  have hΓ : graphOver u (ball 0 R) ∩ closedBall (graphPoint x₀ (u x₀)) r = G '' D := by
    rw [graphOver, ← Set.image_inter_preimage]
  let E : ℝ → Set (Rn n) := fun t => {v | ‖L v‖ ≤ t}
  have hEB : ∀ t, t ≤ η₀ → ∀ v ∈ E t, x₀ + v ∈ closedBall x₀ η₀ := by
    intro t ht v hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hLle v).trans (le_trans hv ht)
  have hx₀B : x₀ ∈ closedBall x₀ η₀ := mem_closedBall_self hη₀.le
  have hDB : D ⊆ closedBall x₀ η₀ := by
    rintro x ⟨-, hx⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm]
    have : r ≤ η₀ := by nlinarith
    linarith [hGdist x x₀]
  have hED : ∀ v ∈ E (r / (1 + ε)), x₀ + v ∈ D := by
    intro v hv
    have hxB := hEB _ hrη₀' v hv
    refine ⟨hB hxB, ?_⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm]
    have h := hup (x₀ + v) hxB x₀ hx₀B
    rw [add_sub_cancel_left] at h
    have hv' : ‖L v‖ ≤ r / (1 + ε) := hv
    calc ‖G (x₀ + v) - G x₀‖ ≤ (1 + ε) * ‖L v‖ := h
      _ ≤ (1 + ε) * (r / (1 + ε)) := by gcongr
      _ = r := by field_simp
  have hDE : ∀ x ∈ D, x - x₀ ∈ E (r / (1 - ε)) := by
    intro x hx
    have hxB := hDB hx
    have hx2 : ‖G x - G x₀‖ ≤ r := by
      have := hx.2
      rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
    show ‖L (x - x₀)‖ ≤ r / (1 - ε)
    rw [le_div_iff₀ h1ε]
    linarith [hlow x hxB x₀ hx₀B]
  -- (5) The images `L(E_t)` are the closed `t`-balls of the `n`-plane `range L`.
  have hrank : Module.finrank ℝ (LinearMap.range L) = n := by
    rw [LinearMap.finrank_range_of_inj hLinj, finrank_euclideanSpace_fin]
  have hplane : ∀ t, 0 ≤ t →
      (μHE[n] : Measure (Amb n ℓ)) (L '' E t) = ENNReal.ofReal (unitBallVolume n * t ^ n) := by
    intro t ht
    have hset : L '' E t = closedBall (0 : Amb n ℓ) t ∩
        ((LinearMap.range L : Submodule ℝ (Amb n ℓ)) : Set (Amb n ℓ)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨mem_closedBall_zero_iff.2 hv, LinearMap.mem_range_self L v⟩
      · rintro ⟨hy, ⟨v, rfl⟩⟩
        exact ⟨v, mem_closedBall_zero_iff.1 hy, rfl⟩
    rw [hset, ← Measure.restrict_apply measurableSet_closedBall]
    exact Submission.rsod_planeMeasure_closedBall n ℓ hn (LinearMap.range L) hrank t ht
  -- (6) Lipschitz images: `Hⁿ(f(S)) ≤ Kⁿ Hⁿ(S)` for `K`-Lipschitz `f`.
  have hlip : ∀ (K : ℝ≥0) (f : Amb n ℓ → Amb n ℓ) (s : Set (Amb n ℓ)), LipschitzOnWith K f s →
      (μHE[n] : Measure (Amb n ℓ)) (f '' s) ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) s := by
    intro K f s hf
    have h := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [ENNReal.rpow_natCast] at h
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
    calc _ ≤ _ * ((K : ℝ≥0∞) ^ n * μH[(n : ℝ)] s) := by gcongr
      _ = _ := by ring
  have hpow : ∀ c : ℝ, 0 ≤ c → ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) ^ n = ENNReal.ofReal (c ^ n) :=
    fun c hc => (ENNReal.ofReal_pow hc n).symm
  have hω : 0 ≤ unitBallVolume n := by
    unfold unitBallVolume
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [hΓ]
  constructor
  · -- Lower bound via `Ψ(z) = L(π z - x₀)`, which is `(1 - ε)⁻¹`-Lipschitz on `G(D)`.
    let Ψ : Amb n ℓ → Amb n ℓ := fun z => L (π z - x₀)
    have hΨlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Ψ (G '' D) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Ψ, hπG]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right,
        Real.coe_toNNReal _ (inv_nonneg.2 h1ε.le)]
      rw [inv_mul_eq_div, le_div_iff₀ h1ε, mul_comm]
      exact hlow x (hDB hx) x' (hDB hx')
    have himg : L '' E (r / (1 + ε)) ⊆ Ψ '' (G '' D) := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨G (x₀ + v), ⟨x₀ + v, hED v hv, rfl⟩, ?_⟩
      simp only [Ψ, hπG, add_sub_cancel_left]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 + ε))) ≤
        ((Real.toNNReal (1 - ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) (G '' D) :=
      (measure_mono himg).trans (hlip _ _ _ hΨlip)
    rw [hplane _ (by positivity), hpow _ (inv_nonneg.2 h1ε.le)] at h1
    have key : ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) =
        ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_pow]
      field_simp
    rw [key]
    calc ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n)
        ≤ ENNReal.ofReal ((1 - ε) ^ n) *
            (ENNReal.ofReal ((1 - ε)⁻¹ ^ n) * (μHE[n] : Measure (Amb n ℓ)) (G '' D)) := by
          gcongr
      _ = (μHE[n] : Measure (Amb n ℓ)) (G '' D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            mul_inv_cancel₀ h1ε.ne', one_pow, ENNReal.ofReal_one, one_mul]
  · -- Upper bound via `Φ(w) = G(x₀ + π w)`, which is `(1 + ε)`-Lipschitz on `L(E_{r/(1-ε)})`.
    let Φ : Amb n ℓ → Amb n ℓ := fun w => G (x₀ + π w)
    have hΦlip : LipschitzOnWith (Real.toNNReal (1 + ε)) Φ (L '' E (r / (1 - ε))) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
      simp only [Φ, hπL]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ (by linarith)]
      have h := hup (x₀ + v) (hEB _ hrη₀ v hv) (x₀ + v') (hEB _ hrη₀ v' hv')
      rwa [add_sub_add_left_eq_sub] at h
    have himg : G '' D ⊆ Φ '' (L '' E (r / (1 - ε))) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨L (x - x₀), ⟨x - x₀, hDE x hx, rfl⟩, ?_⟩
      simp only [Φ, hπL, add_sub_cancel]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (G '' D) ≤
        ((Real.toNNReal (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ n *
          (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 - ε))) :=
      (measure_mono himg).trans (hlip _ _ _ hΦlip)
    rw [hplane _ (by positivity), hpow _ (by linarith)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
/-- **Squeeze lemma for `[0, ∞]`-valued ratios as `r ↓ 0`.**  If for every `δ > 0`, eventually as
`r ↓ 0`, `g r > 0` and `ofReal((1 - δ) g r) ≤ f r ≤ ofReal((1 + δ) g r)`, then
`f r / ofReal(g r) → 1`.  Dividing by `ofReal(g r) ∈ (0, ∞)` gives
`ofReal(1 - δ) ≤ f r / ofReal(g r) ≤ ofReal(1 + δ)` eventually; by `tendsto_order`, a target
`a < 1` is beaten with `δ = (1 - a)/2`, and a target `b > 1` with `δ = (b - 1)/2` (`δ = 1` if
`b = ∞`). -/
theorem dohr_ratio_tendsto_one_of_pinching : ∀ (f : ℝ → ℝ≥0∞) (g : ℝ → ℝ), (∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < g r ∧ ENNReal.ofReal ((1 - δ) * g r) ≤ f r ∧ f r ≤ ENNReal.ofReal ((1 + δ) * g r)) → Tendsto (fun r => f r / ENNReal.ofReal (g r)) (𝓝[>] 0) (𝓝 1) := by
  intro f g h
  -- Pointwise: the bounds give `ofReal (1 - δ) ≤ f r / ofReal (g r) ≤ ofReal (1 + δ)`.
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 - δ) ≤ f r / ENNReal.ofReal (g r) ∧
        f r / ENNReal.ofReal (g r) ≤ ENNReal.ofReal (1 + δ) := by
    intro δ hδ
    filter_upwards [h δ hδ] with r ⟨hg, hlo, hhi⟩
    have hg0 : ENNReal.ofReal (g r) ≠ 0 := (ENNReal.ofReal_pos.2 hg).ne'
    have hgt : ENNReal.ofReal (g r) ≠ ∞ := ENNReal.ofReal_ne_top
    constructor
    · rcases le_or_gt (1 - δ) 0 with hd | hd
      · rw [ENNReal.ofReal_of_nonpos hd]
        exact zero_le
      · rw [ENNReal.le_div_iff_mul_le (Or.inl hg0) (Or.inl hgt), ← ENNReal.ofReal_mul hd.le]
        exact hlo
    · rw [ENNReal.div_le_iff hg0 hgt, ← ENNReal.ofReal_mul (by linarith)]
      exact hhi
  rw [tendsto_order]
  constructor
  · -- `a < 1`, so `a = ofReal a.toReal` with `0 ≤ a.toReal < 1`; take `δ = (1 - a.toReal)/2`.
    intro a ha
    have hat : a ≠ ∞ := ne_top_of_lt ha
    have ha' : a.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hat ENNReal.one_ne_top).2 ha
    have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hδ : 0 < (1 - a.toReal) / 2 := by linarith
    filter_upwards [key _ hδ] with r ⟨hlo, _⟩
    refine lt_of_lt_of_le ?_ hlo
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
      _ < ENNReal.ofReal (1 - (1 - a.toReal) / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · -- `b > 1`: if `b = ∞` take `δ = 1`; otherwise `1 < b.toReal`, take `δ = (b.toReal - 1)/2`.
    intro b hb
    rcases eq_or_ne b ∞ with rfl | hbt
    · filter_upwards [key 1 one_pos] with r ⟨_, hhi⟩
      exact lt_of_le_of_lt hhi ENNReal.ofReal_lt_top
    · have hb' : 1 < b.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hbt).2 hb
      have hδ : 0 < (b.toReal - 1) / 2 := by linarith
      filter_upwards [key _ hδ] with r ⟨_, hhi⟩
      refine lt_of_le_of_lt hhi ?_
      calc ENNReal.ofReal (1 + (b.toReal - 1) / 2) < ENNReal.ofReal b.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        _ = b := ENNReal.ofReal_toReal hbt

/-- **A `C¹` graph has `Hⁿ`-density one at each of its points** (Simon p. 128: "graph `u` is a
`C¹` submanifold so then `Θⁿ(μ_V, x) = 1` at every point of graph `u`").  If `n ≥ 1`, `u` is `C¹`
on the open ball `B̆_R(0) ⊆ ℝⁿ` and `x ∈ B̆_R(0)`, then
`Hⁿ(graph u|_{B̆_R(0)} ∩ B_r((x, u(x)))) / (ω_n rⁿ) → 1` as `r ↓ 0`.  Given `δ > 0`, continuity of
`ε ↦ (1 + ε)ⁿ / (1 − ε)ⁿ` at `0` gives `ε ∈ (0, 1)` with `(1 + ε)ⁿ / (1 − ε)ⁿ < 1 + δ`, hence
`(1 − ε)ⁿ / (1 + ε)ⁿ ≥ (1 + δ)⁻¹ ≥ 1 − δ`.  For small `r > 0` the graph mass in `B_r((x, u(x)))` lies
between `(1 − ε)ⁿ / (1 + ε)ⁿ · ω_n rⁿ` and `(1 + ε)ⁿ / (1 − ε)ⁿ · ω_n rⁿ`
(`dohr_c1_graph_mass_pinching`), so between `(1 ∓ δ) ω_n rⁿ` with `ω_n rⁿ > 0`, and the ratio
squeeze `dohr_ratio_tendsto_one_of_pinching` gives the limit. -/
theorem dohr_c1_graph_density_one : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ hn R u hu x hx
  -- `ω_n = π^{n/2} / Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  refine Submission.dohr_ratio_tendsto_one_of_pinching
    (fun r => (μHE[n] : Measure (Amb n ℓ))
      (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r))
    (fun r => unitBallVolume n * r ^ n) fun δ hδ => ?_
  -- Choose `ε ∈ (0, 1)` with `(1 + ε)ⁿ / (1 − ε)ⁿ < 1 + δ`, by continuity at `ε = 0`.
  have hcont : ContinuousAt (fun ε : ℝ => (1 + ε) ^ n / (1 - ε) ^ n) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε) ^ n / (1 - ε) ^ n < 1 + δ ∧ ε < 1 ∧ 0 < ε :=
    ((hcont.tendsto.eventually (gt_mem_nhds (a := 1 + δ) (by simp [hδ]))).filter_mono
      nhdsWithin_le_nhds).and (((gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨ε, hεδ, hε1, hε0⟩ := hev.exists
  -- `(1 − ε)ⁿ / (1 + ε)ⁿ = ((1 + ε)ⁿ / (1 − ε)ⁿ)⁻¹ ≥ (1 + δ)⁻¹ ≥ 1 − δ`.
  have hlower : 1 - δ ≤ (1 - ε) ^ n / (1 + ε) ^ n := by
    have h1e : 0 < 1 - ε := by linarith
    have h1 : (1 + δ)⁻¹ ≤ (1 - ε) ^ n / (1 + ε) ^ n := by
      rw [← inv_div]
      exact inv_anti₀ (by positivity) hεδ.le
    have h2 : 1 - δ ≤ (1 + δ)⁻¹ := by
      rw [← one_div, le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  -- The pinching bounds hold for `r ∈ (0, η]`, a right neighbourhood of `0`.
  obtain ⟨η, hη, hb⟩ := Submission.dohr_c1_graph_mass_pinching n ℓ hn R u hu x hx ε hε0 hε1
  filter_upwards [Ioc_mem_nhdsGT hη] with r ⟨hr0, hrη⟩
  have hg : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr0 n)
  obtain ⟨hlo, hhi⟩ := hb r hr0 hrη
  exact ⟨hg, (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlower hg.le)).trans hlo,
    hhi.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hεδ.le hg.le))⟩
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
/-- Two-point blow-up estimate for a `C¹` map `G` on an open `U ⊆ ℝⁿ` at `x ∈ U`: for all small
`t > 0`, `x + t • v ∈ U` for `v ∈ B_ρ(0)`, and `v ↦ t⁻¹ • G (x + t • v)` is `ε`-close to
`L = DG(x)` in Lipschitz norm on `B_ρ(0)`.  Choose `δ > 0` with `B̆_δ(x) ⊆ U` and
`‖DG(z) − L‖ ≤ ε` on `B̆_δ(x)` (`G` is differentiable on the open `U` and `DG` is continuous
there); for `0 < t < δ / (|ρ| + 1)` the points `x + t • v` lie in `B̆_δ(x)`.  By the chain rule
`h v = t⁻¹ • G (x + t • v) − L v` has derivative `DG(x + t • v) − L` (as `t⁻¹ • t = 1`), of norm
`≤ ε`, so the mean value inequality on the convex ball gives `‖h v − h v'‖ ≤ ε ‖v − v'‖`, which
is the claim by linearity. -/
theorem dohr_tp_gat_blowup_two_point : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (G : Rn n → Amb n ℓ) (x : Rn n) (ρ ε : ℝ), IsOpen U → ContDiffOn ℝ 1 G U → x ∈ U → 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ v ∈ closedBall (0 : Rn n) ρ, x + t • v ∈ U) ∧ ∀ v ∈ closedBall (0 : Rn n) ρ, ∀ v' ∈ closedBall (0 : Rn n) ρ, ‖t⁻¹ • (G (x + t • v) - G (x + t • v')) - fderiv ℝ G x (v - v')‖ ≤ ε * ‖v - v'‖ := by
  intro n ℓ U G x ρ ε hU hG hx hε
  -- `G` is differentiable on `U` and `z ↦ DG(z)` is continuous on `U`.
  have hdiff : DifferentiableOn ℝ G U := hG.differentiableOn one_ne_zero
  have hcont : ContinuousOn (fderiv ℝ G) U := hG.continuousOn_fderiv_of_isOpen hU le_rfl
  -- A ball `B̆_δ(x) ⊆ U`, `δ = min δ₀ δ₁`, on which `‖DG(z) − DG(x)‖ ≤ ε`.
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousOn_iff.mp hcont x hx ε hε
  have hδ : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
  have hsub : ball x (min δ₀ δ₁) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hball
  have hder : ∀ z ∈ ball x (min δ₀ δ₁), ‖fderiv ℝ G z - fderiv ℝ G x‖ ≤ ε := by
    intro z hz
    have h₁ := hδ₁' z (hsub hz) (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
    rw [dist_eq_norm] at h₁
    exact h₁.le
  -- The scales `0 < t < δ / (|ρ| + 1)`: then `x + t • v ∈ B̆_δ(x)` for `v ∈ B_ρ(0)`.
  have hρ : 0 < |ρ| + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hρ)] with t ht
  obtain ⟨ht0, htδ⟩ := ht
  have hmem : ∀ v ∈ closedBall (0 : Rn n) ρ, x + t • v ∈ ball x (min δ₀ δ₁) := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
    have hv' : ‖v‖ < |ρ| + 1 :=
      lt_of_le_of_lt ((mem_closedBall_zero_iff.mp hv).trans (le_abs_self ρ)) (lt_add_one _)
    calc t * ‖v‖ ≤ t * (|ρ| + 1) := mul_le_mul_of_nonneg_left hv'.le ht0.le
      _ < min δ₀ δ₁ := (lt_div_iff₀ hρ).mp htδ
  refine ⟨fun v hv => hsub (hmem v hv), ?_⟩
  -- `h w = t⁻¹ • G (x + t • w) - DG(x) w` has derivative `DG(x + t • v) − DG(x)` at `v`.
  have hderiv : ∀ v ∈ closedBall (0 : Rn n) ρ,
      HasFDerivWithinAt (fun w => t⁻¹ • G (x + t • w) - fderiv ℝ G x w)
        (fderiv ℝ G (x + t • v) - fderiv ℝ G x) (closedBall (0 : Rn n) ρ) v := by
    intro v hv
    have hGd : HasFDerivAt G (fderiv ℝ G (x + t • v)) (x + t • v) :=
      (hdiff.differentiableAt (hU.mem_nhds (hsub (hmem v hv)))).hasFDerivAt
    have haff : HasFDerivAt (fun w : Rn n => x + t • w) (t • ContinuousLinearMap.id ℝ (Rn n)) v :=
      ((ContinuousLinearMap.id ℝ (Rn n)).hasFDerivAt.const_smul t).const_add x
    have h₂ := ((hGd.comp v haff).const_smul t⁻¹).sub (fderiv ℝ G x).hasFDerivAt
    have heq : t⁻¹ • ((fderiv ℝ G (x + t • v)).comp (t • ContinuousLinearMap.id ℝ (Rn n))) -
        fderiv ℝ G x = fderiv ℝ G (x + t • v) - fderiv ℝ G x := by
      ext w
      simp [smul_smul, inv_mul_cancel₀ ht0.ne']
    rw [heq] at h₂
    exact h₂.hasFDerivWithinAt
  -- The mean value inequality on the convex ball `B_ρ(0)`, then linearity of `t⁻¹ • ·` and `DG(x)`.
  intro v hv v' hv'
  have key := (convex_closedBall (0 : Rn n) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv (fun w hw => hder _ (hmem w hw)) hv' hv
  have hrw : t⁻¹ • (G (x + t • v) - G (x + t • v')) - fderiv ℝ G x (v - v') =
      (t⁻¹ • G (x + t • v) - fderiv ℝ G x v) - (t⁻¹ • G (x + t • v') - fderiv ℝ G x v') := by
    rw [smul_sub, map_sub]
    abel
  rw [hrw]
  exact key

end Submission

namespace Submission

/-- Near-isometries change `Hⁿ` by at most the factor `(1 - δ)⁻ⁿ`: if `0 ≤ δ < 1`, `A` is
measurable and `‖Φ p - Φ q - (p - q)‖ ≤ δ‖p - q‖` on `A`, then
`Hⁿ ⌞ Φ(A) ≤ (1 - δ)⁻ⁿ Φ_#(Hⁿ ⌞ A)` and `Φ_#(Hⁿ ⌞ A) ≤ (1 - δ)⁻ⁿ Hⁿ ⌞ Φ(A)`.
`Φ` is `(1 + δ)`-Lipschitz on `A` and `invFunOn Φ A` is `(1 - δ)⁻¹`-Lipschitz on `Φ(A)`, while
`1 + δ ≤ (1 - δ)⁻¹`; so Simon Ch. 2, 1.8(i) (`Hⁿ(f(T)) ≤ (Lip f)ⁿ Hⁿ(T)`, any `T`), applied to
`Φ⁻¹(S) ∩ A` and to `Φ(Φ⁻¹(S) ∩ A) = S ∩ Φ(A)`, gives both inequalities on measurable `S`. -/
theorem dohr_tp_gat_bilip_measure_comparison : ∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (Φ : Amb n ℓ → Amb n ℓ) (δ : ℝ), MeasurableSet A → 0 ≤ δ → δ < 1 → (∀ p ∈ A, ∀ q ∈ A, ‖Φ p - Φ q - (p - q)‖ ≤ δ * ‖p - q‖) → (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ∧ Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) := by
  intro n ℓ A Φ δ hA hδ0 hδ1 hΦ
  have h1δ : 0 < 1 - δ := sub_pos.2 hδ1
  -- `(1 - δ)‖p - q‖ ≤ ‖Φ p - Φ q‖ ≤ (1 + δ)‖p - q‖` on `A`.
  have hup : ∀ p ∈ A, ∀ q ∈ A, ‖Φ p - Φ q‖ ≤ (1 + δ) * ‖p - q‖ := by
    intro p hp q hq
    calc ‖Φ p - Φ q‖ = ‖(Φ p - Φ q - (p - q)) + (p - q)‖ := by rw [sub_add_cancel]
      _ ≤ ‖Φ p - Φ q - (p - q)‖ + ‖p - q‖ := norm_add_le _ _
      _ ≤ δ * ‖p - q‖ + ‖p - q‖ := add_le_add (hΦ p hp q hq) le_rfl
      _ = (1 + δ) * ‖p - q‖ := by ring
  have hlow : ∀ p ∈ A, ∀ q ∈ A, (1 - δ) * ‖p - q‖ ≤ ‖Φ p - Φ q‖ := by
    intro p hp q hq
    have h : ‖p - q‖ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := by
      calc ‖p - q‖ = ‖(Φ p - Φ q) - (Φ p - Φ q - (p - q))‖ := by rw [sub_sub_cancel]
        _ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := norm_sub_le _ _
    linarith [hΦ p hp q hq]
  -- `Φ` is `(1 + δ)`-Lipschitz on `A`, hence a.e.-measurable for `Hⁿ ⌞ A`.
  have hLipΦ : LipschitzOnWith (Real.toNNReal (1 + δ)) Φ A := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
    exact hup p hp q hq
  have hΦm : AEMeasurable Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) :=
    hLipΦ.continuousOn.aemeasurable hA
  -- `Φ` is injective on `A`; `Ψ = invFunOn Φ A` is a `(1 - δ)⁻¹`-Lipschitz left inverse on `Φ(A)`.
  have hinj : InjOn Φ A := by
    intro p hp q hq hpq
    have h := hlow p hp q hq
    rw [hpq, sub_self, norm_zero] at h
    have h' : ‖p - q‖ ≤ 0 := nonpos_of_mul_nonpos_right h h1δ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have hleft : LeftInvOn (Function.invFunOn Φ A) Φ A := hinj.leftInvOn_invFunOn
  have hLipΨ : LipschitzOnWith (Real.toNNReal ((1 - δ)⁻¹)) (Function.invFunOn Φ A) (Φ '' A) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hleft hp, hleft hq, dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.2 h1δ.le), inv_mul_eq_div, le_div_iff₀ h1δ, mul_comm]
    exact hlow p hp q hq
  -- The constants: `κ̂ = ((1 - δ)⁻¹)ⁿ` in `[0, ∞]`, and `(1 + δ)ⁿ ≤ κ̂` since `(1 + δ)(1 - δ) ≤ 1`.
  have hκ : ENNReal.ofReal (((1 - δ)⁻¹) ^ n) = ((Real.toNNReal ((1 - δ)⁻¹) : ℝ≥0∞)) ^ n :=
    ENNReal.ofReal_pow (inv_nonneg.2 h1δ.le) n
  have hκ' : ((Real.toNNReal (1 + δ) : ℝ≥0∞)) ^ n ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) := by
    rw [hκ]
    gcongr
    rw [← one_div, le_div_iff₀ h1δ]
    nlinarith
  -- For measurable `S`: `Φ_#(Hⁿ ⌞ A)(S) = Hⁿ(Φ⁻¹(S) ∩ A)`, `(Hⁿ ⌞ Φ(A))(S) = Hⁿ(Φ(Φ⁻¹(S) ∩ A))`;
  -- the Lipschitz image bound (Simon Ch. 2, 1.8(i)) for `Φ` and for `Ψ` gives the two inequalities.
  refine ⟨Measure.le_iff.2 fun S hS => ?_, Measure.le_iff.2 fun S hS => ?_⟩
  · rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
      Measure.restrict_apply hS, ← image_preimage_inter, smul_eq_mul]
    calc (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A))
        ≤ ((Real.toNNReal (1 + δ) : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipΦ.mono inter_subset_right)
      _ ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A) := by
          gcongr
  · rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
      Measure.restrict_apply hS, ← image_preimage_inter, smul_eq_mul]
    calc (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A)
        = (μHE[n] : Measure (Amb n ℓ)) (Function.invFunOn Φ A '' (Φ '' (Φ ⁻¹' S ∩ A))) := by
          rw [hleft.image_image' inter_subset_right]
      _ ≤ ((Real.toNNReal ((1 - δ)⁻¹) : ℝ≥0∞)) ^ n *
            (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipΨ.mono (image_mono inter_subset_right))
      _ = ENNReal.ofReal (((1 - δ)⁻¹) ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) := by
          rw [hκ]
/-- Integral comparison for mutually bounded measures (the bi-Lipschitz sandwich step for
Simon Ch. 5, Theorem 7.1): if `μ₁ ≤ κ μ₂` and `μ₂ ≤ κ μ₁` with `κ ≥ 1`, `μ₂` is finite and `φ` is
continuous with `|φ| ≤ M`, then `|∫ φ dμ₁ - ∫ φ dμ₂| ≤ 2 (κ - 1) κ M μ₂(ℝ^{n+ℓ})`.
For continuous `g` with values in `[0, M]`, `a = ∫ g dμ₂ ∈ [0, M μ₂(ℝ^{n+ℓ})]` and `b = ∫ g dμ₁`
satisfy `b ≤ κ a` and `a ≤ κ b`, so `|b - a| ≤ (κ - 1) κ a`; apply this to `max φ 0` and
`max (-φ) 0`, whose difference is `φ`. -/
theorem dohr_tp_gat_bilip_integral_sandwich : ∀ (n ℓ : ℕ) (μ₁ μ₂ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (κ M : ℝ), IsFiniteMeasure μ₂ → Continuous φ → (∀ w, |φ w| ≤ M) → 1 ≤ κ → μ₁ ≤ ENNReal.ofReal κ • μ₂ → μ₂ ≤ ENNReal.ofReal κ • μ₁ → |∫ w, φ w ∂μ₁ - ∫ w, φ w ∂μ₂| ≤ 2 * ((κ - 1) * κ * (M * (μ₂ univ).toReal)) := by
  intro n ℓ μ₁ μ₂ φ κ M hμ₂ hφ hM hκ h12 h21
  have hκ0 : 0 ≤ κ := by linarith
  have hκ1 : 0 ≤ κ - 1 := by linarith
  have hκtop : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκreal : (ENNReal.ofReal κ).toReal = κ := ENNReal.toReal_ofReal hκ0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- `μ₁ ≤ κ μ₂` makes `μ₁` finite.
  have hμ₁ : IsFiniteMeasure μ₁ := by
    refine ⟨lt_of_le_of_lt (Measure.le_iff'.1 h12 univ) ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ₂ univ)
  -- The comparison for a continuous `g` with values in `[0, M]`.
  have key : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ w, 0 ≤ g w) → (∀ w, g w ≤ M) →
      |∫ w, g w ∂μ₁ - ∫ w, g w ∂μ₂| ≤ (κ - 1) * κ * (M * (μ₂ univ).toReal) := by
    intro g hg hg0 hgM
    have hgb : ∀ w, ‖g w‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
      exact hgM w
    have hi₁ : Integrable g μ₁ := Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ hgb)
    have hi₂ : Integrable g μ₂ := Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ hgb)
    have ha0 : 0 ≤ ∫ w, g w ∂μ₂ := integral_nonneg hg0
    have haM : ∫ w, g w ∂μ₂ ≤ M * (μ₂ univ).toReal := by
      have h := norm_integral_le_of_norm_le_const (μ := μ₂) (ae_of_all _ hgb)
      rw [Real.norm_eq_abs, measureReal_def] at h
      exact (le_abs_self _).trans h
    have hba : ∫ w, g w ∂μ₁ ≤ κ * ∫ w, g w ∂μ₂ :=
      calc ∫ w, g w ∂μ₁ ≤ ∫ w, g w ∂(ENNReal.ofReal κ • μ₂) :=
            integral_mono_measure h12 (ae_of_all _ hg0) (hi₂.smul_measure hκtop)
        _ = κ * ∫ w, g w ∂μ₂ := by rw [integral_smul_measure, hκreal, smul_eq_mul]
    have hab : ∫ w, g w ∂μ₂ ≤ κ * ∫ w, g w ∂μ₁ :=
      calc ∫ w, g w ∂μ₂ ≤ ∫ w, g w ∂(ENNReal.ofReal κ • μ₁) :=
            integral_mono_measure h21 (ae_of_all _ hg0) (hi₁.smul_measure hκtop)
        _ = κ * ∫ w, g w ∂μ₁ := by rw [integral_smul_measure, hκreal, smul_eq_mul]
    -- With `a = ∫ g dμ₂`, `b = ∫ g dμ₁`, `V = μ₂(ℝ^{n+ℓ})`:
    -- `b - a ≤ (κ - 1) a ≤ (κ - 1) κ a ≤ (κ - 1) κ M V` and
    -- `a - b ≤ (κ - 1) b ≤ (κ - 1) κ a ≤ (κ - 1) κ M V`.
    have h1 : 0 ≤ (κ - 1) * ((κ - 1) * ∫ w, g w ∂μ₂) := mul_nonneg hκ1 (mul_nonneg hκ1 ha0)
    have h2 : (κ - 1) * κ * ∫ w, g w ∂μ₂ ≤ (κ - 1) * κ * (M * (μ₂ univ).toReal) :=
      mul_le_mul_of_nonneg_left haM (mul_nonneg hκ1 hκ0)
    have h3 : (κ - 1) * ∫ w, g w ∂μ₁ ≤ (κ - 1) * (κ * ∫ w, g w ∂μ₂) :=
      mul_le_mul_of_nonneg_left hba hκ1
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- Split `φ = max φ 0 - max (-φ) 0`; both parts are continuous with values in `[0, M]`.
  have hp : Continuous fun w => max (φ w) 0 := hφ.max continuous_const
  have hn : Continuous fun w => max (-φ w) 0 := hφ.neg.max continuous_const
  have hp0 : ∀ w, 0 ≤ max (φ w) 0 := fun w => le_max_right _ _
  have hn0 : ∀ w, 0 ≤ max (-φ w) 0 := fun w => le_max_right _ _
  have hpM : ∀ w, max (φ w) 0 ≤ M := fun w => max_le ((le_abs_self _).trans (hM w)) hM0
  have hnM : ∀ w, max (-φ w) 0 ≤ M := fun w => max_le ((neg_le_abs _).trans (hM w)) hM0
  have hsplit : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ →
      ∫ w, φ w ∂μ = ∫ w, max (φ w) 0 ∂μ - ∫ w, max (-φ w) 0 ∂μ := by
    intro μ hμ
    have hpb : ∀ w, ‖max (φ w) 0‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 w)]
      exact hpM w
    have hnb : ∀ w, ‖max (-φ w) 0‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn0 w)]
      exact hnM w
    rw [← integral_sub (Integrable.of_bound hp.aestronglyMeasurable M (ae_of_all _ hpb))
      (Integrable.of_bound hn.aestronglyMeasurable M (ae_of_all _ hnb))]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  have hP : |∫ w, max (φ w) 0 ∂μ₁ - ∫ w, max (φ w) 0 ∂μ₂| ≤
      (κ - 1) * κ * (M * (μ₂ univ).toReal) := key _ hp hp0 hpM
  have hN : |∫ w, max (-φ w) 0 ∂μ₁ - ∫ w, max (-φ w) 0 ∂μ₂| ≤
      (κ - 1) * κ * (M * (μ₂ univ).toReal) := key _ hn hn0 hnM
  have e₁ := hsplit μ₁ hμ₁
  have e₂ := hsplit μ₂ hμ₂
  rw [abs_le] at hP hN ⊢
  constructor <;> linarith [hP.1, hP.2, hN.1, hN.2]

end Submission

/-- **Integrals over `C¹`-close bi-Lipschitz images of a compact parameter set converge**
(the blow-up step for approximate tangent planes of `C¹` graphs).  Let `K ⊆ ℝⁿ` be compact,
`pr ∘ L = id`, and suppose that, as `t → 0+`, eventually `pr ∘ F t = id` on `K`,
`‖F t v - F t v' - L (v - v')‖ ≤ ε ‖v - v'‖` on `K` (every `ε > 0`) and `F t → L` uniformly on `K`.
Then `∫_{F t(K)} φ dHⁿ → ∫_{L(K)} φ dHⁿ` for continuous compactly supported `φ`.  With
`Φ = F t ∘ pr`, `Φ` is a `δ`-near-isometry of `A = L(K)` onto `F t(K)`, so `Hⁿ ⌞ F t(K)` and
`Φ_#(Hⁿ ⌞ A)` agree up to the factor `κ = (1 - δ)⁻ⁿ`; the integrals of `φ` against them differ
by at most `2 (κ - 1) κ M Hⁿ(A)`, and `∫_A (φ ∘ Φ - φ) dHⁿ` is small by uniform continuity. -/
theorem Submission.dohr_tp_gat_bilip_setIntegral_tendsto : ∀ (n ℓ : ℕ) (K : Set (Rn n)) (pr : Amb n ℓ →L[ℝ] Rn n) (L : Rn n →L[ℝ] Amb n ℓ) (F : ℝ → Rn n → Amb n ℓ) (φ : Amb n ℓ → ℝ), IsCompact K → Continuous φ → HasCompactSupport φ → (∀ v, pr (L v) = v) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, pr (F t v) = v) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ∀ v' ∈ K, ‖F t v - F t v' - L (v - v')‖ ≤ ε * ‖v - v'‖) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ‖F t v - L v‖ ≤ ε) → Tendsto (fun t : ℝ => ∫ w in F t '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ w in L '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ)))) := by
  intro n ℓ K pr L F φ hK hφc hφs hprL hH1 hH2 hH3
  -- Step 1: `‖v‖ ≤ C ‖L v‖` with `C = ‖pr‖ + 1`, since `pr (L v) = v`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖pr‖ + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  have hLlow : ∀ v, ‖v‖ ≤ C * ‖L v‖ := by
    intro v
    calc ‖v‖ = ‖pr (L v)‖ := by rw [hprL]
      _ ≤ ‖pr‖ * ‖L v‖ := pr.le_opNorm _
      _ ≤ C * ‖L v‖ := by rw [hC]; gcongr; linarith
  -- Step 2: the plane piece `A = L(K)` is compact, hence measurable, and
  -- `Hⁿ(A) ≤ ‖L‖ⁿ Lⁿ(K) < ∞` by the Lipschitz image bound.
  have hA_meas : MeasurableSet (L '' K) := (hK.image L.continuous).isClosed.measurableSet
  have hA_fin : (μHE[n] : Measure (Amb n ℓ)) (L '' K) < ⊤ := by
    calc (μHE[n] : Measure (Amb n ℓ)) (L '' K)
        ≤ (‖L‖₊ : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) K :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            L.lipschitzWith.lipschitzOnWith
      _ < ⊤ := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hK.measure_lt_top
  have : IsFiniteMeasure ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    isFiniteMeasure_restrict.mpr hA_fin.ne
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ((μHE[n] : Measure (Amb n ℓ)) (L '' K)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact ENNReal.toReal_nonneg
  -- Step 3: `|φ| ≤ M` and `φ` is uniformly continuous.
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφs
  have hMabs : ∀ w, |φ w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
  have hUC : UniformContinuous φ := hφs.uniformContinuous_of_continuous hφc
  rw [Metric.tendsto_nhds]
  intro θ hθ
  -- Step 4: `τ` from uniform continuity, and `δ ∈ (0, 1)` with
  -- `2 (κ - 1) κ M V < θ / 2` for `κ = (1 - δ)⁻ⁿ`.
  obtain ⟨τ, hτ, hτφ⟩ := Metric.uniformContinuous_iff.mp hUC (θ / (2 * (V + 1))) (by positivity)
  have hg : ContinuousAt (fun d : ℝ => ((1 - d)⁻¹) ^ n) 0 :=
    ((continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)).pow n
  have hcont : ContinuousAt
      (fun d : ℝ => 2 * ((((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n * (M * V))) 0 :=
    continuousAt_const.mul (((hg.sub continuousAt_const).mul hg).mul continuousAt_const)
  have hlim : Tendsto (fun d : ℝ => 2 * ((((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n * (M * V)))
      (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto
  obtain ⟨δ, hδθ, hδ0, hδ1⟩ : ∃ δ : ℝ,
      2 * ((((1 - δ)⁻¹) ^ n - 1) * ((1 - δ)⁻¹) ^ n * (M * V)) < θ / 2 ∧ 0 < δ ∧ δ < 1 :=
    (((hlim.eventually (gt_mem_nhds (half_pos hθ))).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_set.mpr (Ioo_mem_nhdsGT one_pos))).exists
  have hκ1 : 1 ≤ ((1 - δ)⁻¹) ^ n :=
    one_le_pow₀ ((one_le_inv₀ (by linarith)).mpr (by linarith))
  have hδC : 0 < δ / C := div_pos hδ0 hC0
  -- Step 5: the scale `t`, with (H1), (H2) for `ε = δ / C` and (H3) for `ε = τ / 2`.
  filter_upwards [hH1, hH2 (δ / C) hδC, hH3 (τ / 2) (half_pos hτ)] with t h1 h2 h3
  -- Step 6: the comparison map `Φ = F t ∘ pr`, with `Φ (L z) = F t z` and `Φ(A) = F t '' K`.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Amb n ℓ → Amb n ℓ, Φ = fun y => F t (pr y) := ⟨_, rfl⟩
  have hΦL : ∀ z, Φ (L z) = F t z := fun z => by simp only [hΦ, hprL]
  have hΦA : Φ '' (L '' K) = F t '' K := by
    rw [Set.image_image]
    simp only [hΦL]
  -- Step 7: by (H2), `F t` is Lipschitz on `K`, so `Φ` is continuous on `A`.
  have hFlip : LipschitzOnWith (Real.toNNReal (δ / C + ‖L‖)) (F t) K := by
    refine LipschitzOnWith.of_dist_le' fun v hv v' hv' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖F t v - F t v'‖ = ‖(F t v - F t v' - L (v - v')) + L (v - v')‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖F t v - F t v' - L (v - v')‖ + ‖L (v - v')‖ := norm_add_le _ _
      _ ≤ δ / C * ‖v - v'‖ + ‖L‖ * ‖v - v'‖ := add_le_add (h2 v hv v' hv') (L.le_opNorm _)
      _ = (δ / C + ‖L‖) * ‖v - v'‖ := by ring
  have hΦcont : ContinuousOn Φ (L '' K) := by
    rw [hΦ]
    refine hFlip.continuousOn.comp pr.continuous.continuousOn ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [hprL]
    exact hz
  have hΦae : AEMeasurable Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    hΦcont.aemeasurable hA_meas
  -- Step 8: `Φ` is a `δ`-near-isometry on `A`, by (H2) and step 1.
  have hnear : ∀ p ∈ L '' K, ∀ q ∈ L '' K, ‖Φ p - Φ q - (p - q)‖ ≤ δ * ‖p - q‖ := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hΦL, hΦL, ← map_sub L z w]
    calc ‖F t z - F t w - L (z - w)‖ ≤ δ / C * ‖z - w‖ := h2 z hz w hw
      _ ≤ δ / C * (C * ‖L (z - w)‖) := by gcongr; exact hLlow _
      _ = δ * ‖L (z - w)‖ := by field_simp
  -- Step 9: `Hⁿ ⌞ Φ(A) ≤ κ Φ_#(Hⁿ ⌞ A)` and `Φ_#(Hⁿ ⌞ A) ≤ κ Hⁿ ⌞ Φ(A)`; the push-forward
  -- is finite with total mass `V`.
  obtain ⟨hle1, hle2⟩ :=
    Submission.dohr_tp_gat_bilip_measure_comparison n ℓ (L '' K) Φ δ hA_meas hδ0.le hδ1 hnear
  have hfin2 : IsFiniteMeasure
      (Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))) := inferInstance
  have hμ₂univ :
      (Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) univ).toReal = V := by
    rw [Measure.map_apply_of_aemeasurable hΦae MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, hV]
  -- Steps 10-11: `|∫ φ d(Hⁿ ⌞ Φ(A)) - ∫ φ dΦ_#(Hⁿ ⌞ A)| ≤ 2 (κ - 1) κ M V < θ / 2`.
  have hsw := Submission.dohr_tp_gat_bilip_integral_sandwich n ℓ _ _ φ (((1 - δ)⁻¹) ^ n) M
    hfin2 hφc hMabs hκ1 hle1 hle2
  rw [hμ₂univ] at hsw
  -- Step 12: `∫ φ dΦ_#(Hⁿ ⌞ A) = ∫_A φ ∘ Φ dHⁿ`.
  have hmap : ∫ w, φ w ∂(Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))) =
      ∫ y, φ (Φ y) ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    integral_map hΦae hφc.aestronglyMeasurable
  -- Step 13: by (H3), `|φ ∘ Φ - φ| ≤ θ / (2 (V + 1))` on `A`, so the integrals over `A`
  -- differ by less than `θ / 2`.
  have hint1 : Integrable (fun y => φ (Φ y)) ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    Integrable.of_bound ((hφc.comp_continuousOn hΦcont).aestronglyMeasurable hA_meas) M
      (ae_of_all _ fun y => hM (Φ y))
  have hint2 : Integrable φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    Integrable.of_bound hφc.aestronglyMeasurable M (ae_of_all _ hM)
  have hclose : ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)),
      ‖φ (Φ y) - φ y‖ ≤ θ / (2 * (V + 1)) := by
    rw [ae_restrict_iff' hA_meas]
    refine Filter.Eventually.of_forall ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← dist_eq_norm]
    refine (hτφ ?_).le
    rw [dist_eq_norm, hΦL]
    linarith [h3 z hz]
  have hdiff : |∫ y, φ (Φ y) ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) -
      ∫ y, φ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))| ≤ θ / (2 * (V + 1)) * V := by
    have h := norm_integral_le_of_norm_le_const hclose
    rwa [integral_sub hint1 hint2, measureReal_restrict_apply_univ, measureReal_def, ← hV,
      Real.norm_eq_abs] at h
  have hθV : θ / (2 * (V + 1)) * V < θ / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- Step 14: `F t '' K = Φ(A)` and the triangle inequality.
  have hA1 := abs_sub_lt_iff.mp (lt_of_le_of_lt hsw hδθ)
  have hA2 := abs_sub_lt_iff.mp (lt_of_le_of_lt hdiff hθV)
  rw [hmap] at hA1
  rw [Real.dist_eq, ← hΦA, abs_sub_lt_iff]
  constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2]

namespace Submission

/-- **Localizing set integrals to `B`.**  If `φ` vanishes off the measurable set `B`, then
`φ = B.indicator φ`, so `∫_X φ dμ = ∫_{X ∩ B} φ dμ` for every set `X` (`setIntegral_indicator`;
neither integrability of `φ` nor measurability of `X` is needed).  From `S ∩ B ⊆ T ⊆ S` we get
`S ∩ B = T ∩ B`, hence `∫_S φ dμ = ∫_T φ dμ`. -/
theorem dohr_tp_gat_setIntegral_eq_of_inter : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (S T B : Set (Amb n ℓ)), MeasurableSet B → (∀ w, w ∉ B → φ w = 0) → S ∩ B ⊆ T → T ⊆ S → ∫ w in S, φ w ∂μ = ∫ w in T, φ w ∂μ := by
  intro n ℓ μ φ S T B hB hφ hST hTS
  -- `φ = B.indicator φ`, since `φ` vanishes off `B`.
  have hind : B.indicator φ = φ := by
    funext w
    by_cases hw : w ∈ B
    · exact indicator_of_mem hw φ
    · rw [indicator_of_notMem hw, hφ w hw]
  -- `S ∩ B = T ∩ B`: `S ∩ B ⊆ T` gives `⊆`, and `T ⊆ S` gives `⊇`.
  have hinter : S ∩ B = T ∩ B :=
    Subset.antisymm (subset_inter hST inter_subset_right) (inter_subset_inter_left B hTS)
  calc ∫ w in S, φ w ∂μ = ∫ w in S, B.indicator φ w ∂μ := by rw [hind]
    _ = ∫ w in S ∩ B, φ w ∂μ := setIntegral_indicator hB
    _ = ∫ w in T ∩ B, φ w ∂μ := by rw [hinter]
    _ = ∫ w in T, B.indicator φ w ∂μ := (setIntegral_indicator hB).symm
    _ = ∫ w in T, φ w ∂μ := by rw [hind]

/-- Simon Ch. 3, Definition 1.4 for `C¹` graphs: if `u` is `C¹` on the open ball `B̆_R(0) ⊆ ℝⁿ`,
`G(z) = (z, u(z))` and `x ∈ B̆_R(0)`, then `τ = range DG(x)` is the approximate tangent space of
`graph u = G(B̆_R(0))` at `G(x)`.  The projection `π` onto the first `n` coordinates
(`rsod_graphPoint_eq_finAddEquivProd_symm`) is `1`-Lipschitz (`rsod_norm_graphPoint_sq`) and
inverts `G`, hence also `DG(x)` (chain rule for `π ∘ G = id`), so `DG(x)` is
injective and `dim τ = n`.  For `f ∈ C_c(ℝ^{n+ℓ})` vanishing off `B_ρ(0)`, the blow-ups
`F_t(v) = t⁻¹ (G(x + tv) − G(x))` satisfy `π ∘ F_t = id` and, by `dohr_tp_gat_blowup_two_point`,
the two-point and uniform estimates of `dohr_tp_gat_bilip_setIntegral_tendsto` on `K = B_ρ(0)`, so
`∫_{F_t(K)} f dHⁿ → ∫_{DG(x)(K)} f dHⁿ`.  As `|v| ≤ |F_t(v)|` and `|v| ≤ |DG(x) v|`,
`dohr_tp_gat_setIntegral_eq_of_inter` (with `B = B_ρ(0)`) identifies these integrals with
`∫_{η_{G(x),t}(graph u)} f dHⁿ` for small `t > 0` and with `∫_τ f dHⁿ`. -/
theorem dohr_tp_graph_approx_tangent : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R,
    Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (graphOver u (ball 0 R))
      (graphPoint x (u x))
      (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap) := by
  intro n ℓ _ R u hu x hx
  -- `graphPoint a b` corresponds to `(a, b)` under the splitting `ℝ^{n+ℓ} ≃ ℝⁿ × ℝ^ℓ`,
  -- and `|(a, b)|² = |a|² + |b|²`
  let e : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = e.symm (a, b) :=
    fun a b => Submission.rsod_graphPoint_eq_finAddEquivProd_symm a b
  have hgp_norm : ∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
    fun a b => Submission.rsod_norm_graphPoint_sq a b
  -- the projection `π` onto the first `n` coordinates
  let pr : Amb n ℓ →L[ℝ] Rn n :=
    (ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp (e : Amb n ℓ →L[ℝ] Rn n × Rn ℓ)
  have hpr_gp : ∀ (a : Rn n) (b : Rn ℓ), pr (graphPoint a b) = a := by
    intro a b
    simp [pr, hgp]
  have hpr_norm : ∀ w : Amb n ℓ, ‖pr w‖ ≤ ‖w‖ := by
    intro w
    have hw : graphPoint (e w).1 (e w).2 = w := by rw [hgp]; exact e.symm_apply_apply w
    have h2 := hgp_norm (e w).1 (e w).2
    rw [hw] at h2
    have h3 : ‖pr w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      have hpw : pr w = (e w).1 := rfl
      rw [hpw, h2]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
  set G : Rn n → Amb n ℓ := fun z => graphPoint z (u z)
  have hprG : ∀ z, pr (G z) = z := fun z => hpr_gp z (u z)
  have hGc : ContDiffOn ℝ 1 G (ball 0 R) := by
    have hGe : G = e.symm ∘ fun z => (z, u z) := funext fun z => hgp z (u z)
    rw [hGe]
    exact e.symm.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)
  have hGd : DifferentiableAt ℝ G x :=
    (hGc.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hx)
  set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G x
  have hprL : ∀ v, pr (L v) = v := by
    have h1 : HasFDerivAt (pr ∘ G) (pr.comp L) x := pr.hasFDerivAt.comp x hGd.hasFDerivAt
    have h2 : (pr ∘ G) = id := funext hprG
    rw [h2] at h1
    have h3 := h1.unique (hasFDerivAt_id x)
    intro v
    exact congrArg (fun T : Rn n →L[ℝ] Rn n => T v) h3
  have hLinj : Function.Injective L := fun v v' h => by rw [← hprL v, ← hprL v', h]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (f := L.toLinearMap) hLinj, finrank_euclideanSpace_fin]
  intro f
  -- a radius `ρ ≥ 0` outside of which `f` vanishes
  obtain ⟨ρ0, hρ0⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set ρ : ℝ := max ρ0 0
  have hρ_nn : 0 ≤ ρ := le_max_right _ _
  have hfz : ∀ w, w ∉ closedBall (0 : Amb n ℓ) ρ → f w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hw'
    exact hw (closedBall_subset_closedBall (le_max_left _ _) (hρ0 hw'))
  set K : Set (Rn n) := closedBall 0 ρ
  -- the blow-ups `F_t(v) = t⁻¹ (G(x + t v) - G(x))` of the graph map at `x`
  set F : ℝ → Rn n → Amb n ℓ := fun t v => t⁻¹ • (G (x + t • v) - G x) with hF
  have hprF : ∀ t : ℝ, t ≠ 0 → ∀ v, pr (F t v) = v := by
    intro t ht v
    simp only [hF, map_smul, map_sub, hprG, add_sub_cancel_left, inv_smul_smul₀ ht]
  have hF_blowUp : ∀ t : ℝ, t ≠ 0 → ∀ z,
      F t (t⁻¹ • (z - x)) = Poincare.SimonGMT.Chapter03.blowUpMap (G x) t (G z) := by
    intro t ht z
    simp only [hF, Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ ht, add_sub_cancel]
  have h_pr : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, pr (F t v) = v := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) v _
    exact hprF t ht.ne' v
  have h_two : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ∀ v' ∈ K,
      ‖F t v - F t v' - L (v - v')‖ ≤ ε * ‖v - v'‖ := by
    intro ε hε
    filter_upwards [Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ ε isOpen_ball
      hGc hx hε] with t ht v hv v' hv'
    have hsub : F t v - F t v' = t⁻¹ • (G (x + t • v) - G (x + t • v')) := by
      simp only [hF, ← smul_sub, sub_sub_sub_cancel_right]
    rw [hsub]
    exact ht.2 v hv v' hv'
  have h_one : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ‖F t v - L v‖ ≤ ε := by
    intro ε hε
    have hρ1 : (0 : ℝ) < ρ + 1 := by linarith
    have hε' : 0 < ε / (ρ + 1) := div_pos hε hρ1
    filter_upwards [Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ (ε / (ρ + 1))
      isOpen_ball hGc hx hε'] with t ht v hv
    have h1 := ht.2 v hv 0 (mem_closedBall_self hρ_nn)
    simp only [smul_zero, add_zero, sub_zero] at h1
    have hv' : ‖v‖ ≤ ρ := mem_closedBall_zero_iff.mp hv
    calc ‖F t v - L v‖ ≤ ε / (ρ + 1) * ‖v‖ := h1
      _ ≤ ε / (ρ + 1) * (ρ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
      _ = ε := div_mul_cancel₀ ε hρ1.ne'
  -- localize the blown-up graph to `F_t(K)` and the plane `τ` to `L(K)`
  have hloc1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∫ w in F t '' K, f w ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap (G x) t '' graphOver u (ball 0 R),
          f w ∂(μHE[n] : Measure (Amb n ℓ)) := by
    filter_upwards [self_mem_nhdsWithin,
      Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ 1 isOpen_ball hGc hx one_pos]
      with t (ht : 0 < t) hball
    symm
    refine Submission.dohr_tp_gat_setIntegral_eq_of_inter n ℓ _ f _ _ (closedBall 0 ρ)
      measurableSet_closedBall hfz ?_ ?_
    · rintro w ⟨⟨y, ⟨z, hz, rfl⟩, rfl⟩, hwB⟩
      refine ⟨t⁻¹ • (z - x), ?_, hF_blowUp t ht.ne' z⟩
      rw [mem_closedBall_zero_iff] at hwB ⊢
      calc ‖t⁻¹ • (z - x)‖ = ‖pr (F t (t⁻¹ • (z - x)))‖ := by rw [hprF t ht.ne']
        _ ≤ ‖F t (t⁻¹ • (z - x))‖ := hpr_norm _
        _ = ‖Poincare.SimonGMT.Chapter03.blowUpMap (G x) t (G z)‖ := by
          rw [hF_blowUp t ht.ne' z]
        _ ≤ ρ := hwB
    · rintro w ⟨v, hv, rfl⟩
      exact ⟨G (x + t • v), ⟨x + t • v, hball.1 v hv, rfl⟩, rfl⟩
  have hloc2 : ∫ w in L '' K, f w ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ w in (LinearMap.range L.toLinearMap : Set (Amb n ℓ)), f w
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
    symm
    refine Submission.dohr_tp_gat_setIntegral_eq_of_inter n ℓ _ f _ _ (closedBall 0 ρ)
      measurableSet_closedBall hfz ?_ ?_
    · rintro w ⟨hw, hwB⟩
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall_zero_iff] at hwB ⊢
      calc ‖v‖ = ‖pr (L v)‖ := by rw [hprL]
        _ ≤ ‖L v‖ := hpr_norm _
        _ ≤ ρ := hwB
    · rintro w ⟨v, -, rfl⟩
      exact LinearMap.mem_range_self _ v
  have hlim := Submission.dohr_tp_gat_bilip_setIntegral_tendsto n ℓ K pr L F f
    (isCompact_closedBall 0 ρ) (map_continuous f) f.hasCompactSupport hprL h_pr h_two h_one
  have h := hlim.congr' hloc1
  rw [hloc2] at h
  exact h
/-- **Approximate tangent spaces under rigid motions** (Simon Ch. 3, 1.4; used for the graph
tangent planes in the proof of 7.1).  If `P` is the approximate tangent space of `S` at `z`, then
for every linear isometry `Q` of `ℝ^{n+ℓ}` and every `ξ`, `Q(P)` is the approximate tangent space
of `ξ + Q(S)` at `ξ + Q z`.
Proof: `η_{ξ+Qz,r}(ξ + Q w) = Q(η_{z,r} w)` and `Q` preserves `Hⁿ`, so for `φ ∈ C_c` the blown-up
integrals of `φ` over `ξ + Q(S)` equal those of `φ ∘ Q ∈ C_c` over `S`, while
`∫_{Q(P)} φ dHⁿ = ∫_P φ ∘ Q dHⁿ`; and `dim Q(P) = dim P`. -/
theorem dohr_tp_approx_tangent_affine_isometry : ∀ (n ℓ : ℕ) (S : Set (Amb n ℓ)) (z ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S z P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n ((fun w => ξ + Q w) '' S) (ξ + Q z) (Submodule.map Q.toLinearEquiv.toLinearMap P) := by
  intro n ℓ S z ξ Q P hP
  obtain ⟨hdim, hconv⟩ := hP
  -- `Q` is an isometric equivalence: a measurable embedding preserving `μHE[n]`, so
  -- `∫_{Q '' X} φ dHⁿ = ∫_X φ ∘ Q dHⁿ` for every set `X`.
  have hmp : MeasurePreserving Q (μHE[n] : Measure (Amb n ℓ)) μHE[n] :=
    Q.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n
  have hme : MeasurableEmbedding Q := Q.toHomeomorph.measurableEmbedding
  refine ⟨(LinearEquiv.finrank_map_eq Q.toLinearEquiv P).trans hdim, fun φ => ?_⟩
  -- The test function `ψ = φ ∘ Q` is again in `C_c`.
  set ψ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ := φ.comp Q.toHomeomorph.toCocompactMap
  have hψ : ∀ X : Set (Amb n ℓ), ∫ y in Q '' X, φ y ∂μHE[n] = ∫ y in X, ψ y ∂μHE[n] :=
    fun X => hmp.setIntegral_image_emb hme φ X
  -- Blow-ups commute with `w ↦ ξ + Q w`: `η_{ξ+Qz,r}(ξ + Q w) = Q (η_{z,r} w)`.
  have himg : ∀ r : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap (ξ + Q z) r '' ((fun w => ξ + Q w) '' S) =
        Q '' (Poincare.SimonGMT.Chapter03.blowUpMap z r '' S) := by
    intro r
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun w _ => ?_
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_add_left_eq_sub, map_smul, map_sub]
  have hlim : ∫ y in (Submodule.map Q.toLinearEquiv.toLinearMap P : Set (Amb n ℓ)), φ y ∂μHE[n] =
      ∫ y in (P : Set (Amb n ℓ)), ψ y ∂μHE[n] := by
    rw [Submodule.map_coe]
    exact hψ P
  rw [hlim]
  refine (hconv ψ).congr fun r => ?_
  rw [himg r, hψ]
/-- `n`-dimensional growth of a compactly contained `C¹` graph piece: if `0 < ρ < R` and `u` is
`C¹` on `B̆_R(0)`, then `Hⁿ(graph u|B̆_ρ(0) ∩ B_r(z)) ≤ C rⁿ` for all `z` and all `r > 0`.  On the
compact convex ball `B_ρ(0) ⊆ B̆_R(0)` the map `u` is `K`-Lipschitz
(`ContDiffOn.exists_lipschitzOnWith`), so `G x = (x, u x)` satisfies
`|a - b| ≤ |G a - G b| ≤ (1 + K) |a - b|` there (`|G a - G b|² = |a - b|² + |u a - u b|²`, split the
coordinate sum with `Fin.sum_univ_add`).  Graph points in `B_r(z)` come from one parameter ball
`B_{2r}(a)`, and the Lipschitz image bound `LipschitzOnWith.hausdorffMeasure_image_le` (rescaled to
`μHE[n] = c • μH[n]`, which is Lebesgue measure on `ℝⁿ`) gives `C = (1 + K)ⁿ 2ⁿ Lⁿ(B_1(0))`. -/
theorem dohr_tp_graph_ball_growth : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R ρ : ℝ) (u : Rn n → Rn ℓ), 0 < ρ →
    ρ < R → ContDiffOn ℝ 1 u (ball 0 R) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
      (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 ρ) ∩ closedBall z r) ≤
        ENNReal.ofReal (C * r ^ n) := by
  intro n ℓ _ R ρ u _ hρR hu
  obtain ⟨K, hK⟩ := (hu.mono (closedBall_subset_ball hρR)).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall 0 ρ) (isCompact_closedBall 0 ρ)
  have hdist : ∀ a b : Rn n, dist (graphPoint a (u a)) (graphPoint b (u b)) ^ 2 =
      dist a b ^ 2 + dist (u a) (u b) ^ 2 := by
    intro a b
    simp only [EuclideanSpace.dist_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_add]
    simp [graphPoint]
  have hlow : ∀ a b : Rn n, dist a b ≤ dist (graphPoint a (u a)) (graphPoint b (u b)) := by
    intro a b
    nlinarith [hdist a b, dist_nonneg (x := a) (y := b), sq_nonneg (dist (u a) (u b)),
      dist_nonneg (x := graphPoint a (u a)) (y := graphPoint b (u b))]
  have hLip : LipschitzOnWith (1 + K) (fun x => graphPoint x (u x)) (closedBall 0 ρ) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hu' : dist (u a) (u b) ≤ K * dist a b := hK.dist_le_mul a ha b hb
    have h1 : dist (graphPoint a (u a)) (graphPoint b (u b)) ≤ dist a b + dist (u a) (u b) := by
      nlinarith [hdist a b, dist_nonneg (x := a) (y := b), dist_nonneg (x := u a) (y := u b),
        dist_nonneg (x := graphPoint a (u a)) (y := graphPoint b (u b))]
    push_cast
    linarith
  -- `μHE[n] = c • μH[n]` with the same `c` on every space, and `μHE[n] = volume` on `ℝⁿ`.
  have key : ∀ s : Set (Rn n), s ⊆ closedBall 0 ρ →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' s) ≤
        ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume s := by
    intro s hs
    have h1 := (hLip.mono hs).hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [ENNReal.rpow_natCast] at h1
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def,
      Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul]
    calc _ ≤ _ := by gcongr
      _ = _ := mul_left_comm _ _ _
  set ω : ℝ≥0∞ := volume (closedBall (0 : Rn n) 1)
  have hωtop : ω ≠ ∞ := measure_closedBall_lt_top.ne
  refine ⟨((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal, by positivity, fun z r hr => ?_⟩
  rcases (graphOver u (ball 0 ρ) ∩ closedBall z r).eq_empty_or_nonempty with hE | ⟨p, hp⟩
  · rw [hE, measure_empty]
    exact zero_le
  obtain ⟨⟨a, -, rfl⟩, hpz⟩ := hp
  have hX : graphOver u (ball 0 ρ) ∩ closedBall z r ⊆
      (fun x => graphPoint x (u x)) '' (ball 0 ρ ∩ closedBall a (2 * r)) := by
    rintro y ⟨⟨b, hb, rfl⟩, hyz⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    rw [mem_closedBall] at hyz hpz ⊢
    calc dist b a ≤ dist (graphPoint b (u b)) (graphPoint a (u a)) := hlow b a
      _ ≤ dist (graphPoint b (u b)) z + dist (graphPoint a (u a)) z := dist_triangle_right _ _ _
      _ ≤ 2 * r := by linarith
  calc (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 ρ) ∩ closedBall z r)
      ≤ (μHE[n] : Measure (Amb n ℓ))
          ((fun x => graphPoint x (u x)) '' (ball 0 ρ ∩ closedBall a (2 * r))) := measure_mono hX
    _ ≤ ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume (ball 0 ρ ∩ closedBall a (2 * r)) :=
        key _ (inter_subset_left.trans ball_subset_closedBall)
    _ ≤ ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume (closedBall a (2 * r)) := by
        gcongr
        exact inter_subset_right
    _ = ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * (ENNReal.ofReal ((2 * r) ^ n) * ω) := by
        rw [Measure.addHaar_closedBall' _ _ (by positivity), finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal * r ^ n) := by
        rw [show ((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal * r ^ n =
            ((1 + K : ℝ≥0) : ℝ) ^ n * ((2 * r) ^ n * ω.toReal) by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_toReal hωtop]
/-- Lebesgue points for a measure with `n`-dimensional growth: if `ν(B_r(z)) ≤ C rⁿ` for all `z`
and `r > 0` and `f` is `ν`-integrable, then for `ν`-a.e. `y`,
`r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν → 0` as `r ↓ 0`.  The growth bound makes `ν` locally finite, so the
Besicovitch differentiation theorem gives `ν(B_r(y))⁻¹ ∫_{B_r(y)} |f − f(y)| dν → 0`, and
`r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν ≤ C · ν(B_r(y))⁻¹ ∫_{B_r(y)} |f − f(y)| dν`. -/
theorem dohr_tp_ae_lebesgue_point_of_growth : ∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (C : ℝ), Integrable f ν → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → ν (closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂ν, Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν f C hf hgrowth
  -- The growth bound makes `ν` locally finite (hence σ-finite).
  have : IsLocallyFiniteMeasure ν :=
    ⟨fun y => ⟨closedBall y 1, closedBall_mem_nhds y one_pos,
      (hgrowth y 1 one_pos).trans_lt ENNReal.ofReal_lt_top⟩⟩
  -- Besicovitch differentiation: the averages of `|f − f(y)|` over `B_r(y)` tend to `0`.
  filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
    hf.locallyIntegrable] with y hy
  have hD := hy.comp (Besicovitch.tendsto_filterAt ν y)
  have hCD : Tendsto (fun r : ℝ => ENNReal.ofReal C *
      ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCD
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν ≤ C · (average)`, separating the case `ν(B_r(y)) = 0`.
  by_cases hm : ν (closedBall y r) = 0
  · rw [setLIntegral_measure_zero _ _ hm]
    simp
  have hmle := hgrowth y r hr
  have hmtop : ν (closedBall y r) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmle
  have hrn : 0 < r ^ n := pow_pos hr n
  calc ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν
      = ENNReal.ofReal ((r ^ n)⁻¹) * ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) /
          ν (closedBall y r) * ν (closedBall y r)) := by
        rw [ENNReal.div_mul_cancel hm hmtop]
    _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) /
          ν (closedBall y r) * ENNReal.ofReal (C * r ^ n)) := by
        gcongr
    _ = ENNReal.ofReal ((r ^ n)⁻¹ * (C * r ^ n)) *
          ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r)) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrn.le)]
        ring
    _ = ENNReal.ofReal C *
          ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r)) := by
        rw [mul_comm C, inv_mul_cancel_left₀ hrn.ne']
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
/-- **Rescaling the radius in a scaled Lebesgue-point limit.**  If `t⁻ⁿ L(t) → 0` in `[0, ∞]` as
`t ↓ 0` and `ρ > 0`, then `L(rρ) < ∞` for all small `r > 0` and `r⁻ⁿ L(rρ) → 0` in `ℝ` as `r ↓ 0`:
`r ↦ rρ` maps `𝓝[>] 0` into itself, `toReal` is continuous at `0`, and for `r > 0`
`r⁻ⁿ L(rρ) = ρⁿ ((rρ)⁻ⁿ L(rρ)).toReal`. -/
theorem dohr_tp_wtlp_rescaled_limit : ∀ (n : ℕ) (L : ℝ → ℝ≥0∞) (ρ : ℝ), 0 < ρ → Tendsto (fun t : ℝ => ENNReal.ofReal ((t ^ n)⁻¹) * L t) (𝓝[>] 0) (𝓝 0) → (∀ᶠ r in 𝓝[>] (0 : ℝ), L (r * ρ) ≠ ⊤) ∧ Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (L (r * ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
  intro n L ρ hρ hL
  -- `r ↦ r * ρ` maps `𝓝[>] 0` into `𝓝[>] 0`, so `((rρ)ⁿ)⁻¹ L(rρ) → 0` as `r ↓ 0`.
  have hmap : Tendsto (fun r : ℝ => r * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hr hρ
  have hF := hL.comp hmap
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  refine ⟨?_, ?_⟩
  · -- Eventually `((rρ)ⁿ)⁻¹ L(rρ) < 1`, while `L(rρ) = ∞` would make it `∞`.
    filter_upwards [hpos, hF.eventually (eventually_lt_nhds zero_lt_one)] with r hr hlt htop
    have hne : ENNReal.ofReal (((r * ρ) ^ n)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (mul_pos hr hρ) n))).ne'
    simp [htop, ENNReal.mul_top hne] at hlt
  · -- `ρⁿ (((rρ)ⁿ)⁻¹ L(rρ)).toReal → 0` and equals `(rⁿ)⁻¹ (L(rρ)).toReal` for `r > 0`.
    have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hF).const_mul (ρ ^ n)
    rw [ENNReal.toReal_zero, mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hpos] with r hr
    simp only [Function.comp_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (mul_pos hr hρ).le n))]
    rw [mul_pow, mul_inv, mul_comm ((r ^ n)⁻¹), ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hρ.ne'), one_mul]
/-- `Hⁿ`-a.e. on `M ∩ O`, approximate tangent planes of `S` are approximate tangent planes of `M`
with respect to `θ`, provided `Hⁿ((M ∩ O) \ S) = 0`, `θ` is integrable on `M ∩ O` and
`Hⁿ ⌞ (S ∩ O)` has `n`-dimensional growth.  `Hⁿ ⌞ (S ∩ O)`-a.e. point is a Lebesgue point of
`1_M θ` (`dohr_tp_ae_lebesgue_point_of_growth`); at such a point `y ∈ M ∩ O ∩ S` the small balls
`B_r(y)` lie in `O`, which turns this into the Lebesgue condition on `S` required by
`dohr_tp_weighted_tangent_of_lebesgue_point`. -/
theorem dohr_tp_ae_weighted_tangent_of_growth : ∀ (n ℓ : ℕ) (M S O : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (C : ℝ), IsOpen O → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → IntegrableOn θ (M ∩ O) (μHE[n] : Measure (Amb n ℓ)) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ O) \ S) = 0 → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → (μHE[n] : Measure (Amb n ℓ)) (S ∩ O ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict M), y ∈ O → ∀ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
  intro n ℓ M S O θ C hO hM hθ hθint hMS hgrowth
  -- Fixed-scale comparison: if `ψ` is measurable, `|ψ| ≤ K`, `ψ = 0` off the measurable set `B`,
  -- `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`, then
  -- `|∫_M ψ θ - c ∫_S ψ| ≤ K ∫_{S ∩ B} |1_M θ - c|` when the right side is finite: both integrals
  -- localize to `S ∩ B`, where the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
  have hcmp : ∀ (B : Set (Amb n ℓ)) (ψ : Amb n ℓ → ℝ) (c K : ℝ), MeasurableSet B →
      (μHE[n] : Measure (Amb n ℓ)) ((M ∩ B) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ B) ≠ ⊤ →
      Measurable ψ → (∀ w, |ψ w| ≤ K) → (∀ w, w ∉ B → ψ w = 0) →
      ∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) ≠ ⊤ →
      |∫ w in M, ψ w * θ w ∂(μHE[n] : Measure (Amb n ℓ)) -
          c * ∫ w in S, ψ w ∂(μHE[n] : Measure (Amb n ℓ))| ≤
        K * (∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))).toReal := by
    revert hM hθ
    generalize (μHE[n] : Measure (Amb n ℓ)) = μ
    intro hM hθ B ψ c K hB hMBS hSB hψ hψK hψB hΛ
    have hψK' : ∀ w, ‖ψ w‖ ≤ K := fun w => by rw [Real.norm_eq_abs]; exact hψK w
    -- The `S`-integral localizes to `S ∩ B`, as `ψ = 0` off `B`.
    have h1 : ∫ w in S, ψ w ∂μ = ∫ w in S ∩ B, ψ w ∂μ := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict S) hψB,
        Measure.restrict_restrict hB, inter_comm B S]
    -- The `M`-integral localizes to `M ∩ B =ᵐ M ∩ (S ∩ B)`, i.e. to the integral of `ψ · 1_M θ`
    -- over `S ∩ B`.
    have h2 : ∫ w in M, ψ w * θ w ∂μ = ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ := by
      have hae : (M ∩ B : Set (Amb n ℓ)) =ᵐ[μ] (M ∩ (S ∩ B) : Set (Amb n ℓ)) := by
        refine ae_eq_set.mpr ⟨measure_mono_null (fun w hw => ?_) hMBS, ?_⟩
        · exact ⟨hw.1, fun hS => hw.2 ⟨hw.1.1, hS, hw.1.2⟩⟩
        · rw [show (M ∩ (S ∩ B)) \ (M ∩ B) = ∅ from
            eq_empty_of_forall_notMem fun w hw => hw.2 ⟨hw.1.1, hw.1.2.2⟩, measure_empty]
      have hMν : NullMeasurableSet M (μ.restrict (S ∩ B)) := hM.mono Measure.restrict_le_self
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict M) (s := B)
          (f := fun w => ψ w * θ w) (fun w hw => by rw [hψB w hw, zero_mul]),
        Measure.restrict_restrict hB, inter_comm B M, setIntegral_congr_set hae,
        ← Measure.restrict_restrict₀ hMν, ← integral_indicator₀ hMν]
      congr 1
      funext w
      exact indicator_mul_right M ψ θ
    -- Integrability on `S ∩ B`, which has finite measure.
    have : IsFiniteMeasure (μ.restrict (S ∩ B)) := isFiniteMeasure_restrict.mpr hSB
    have hfB : AEStronglyMeasurable (M.indicator θ) (μ.restrict (S ∩ B)) :=
      ((aemeasurable_indicator_iff₀ hM).mpr hθ).restrict.aestronglyMeasurable
    have hfc : Integrable (fun w => M.indicator θ w - c) (μ.restrict (S ∩ B)) :=
      ⟨hfB.sub aestronglyMeasurable_const, hasFiniteIntegral_iff_enorm.mpr hΛ.lt_top⟩
    have hfi : Integrable (M.indicator θ) (μ.restrict (S ∩ B)) :=
      (hfc.add (integrable_const c)).congr (ae_of_all _ fun w => by simp)
    have hψb : ∀ᵐ w ∂(μ.restrict (S ∩ B)), ‖ψ w‖ ≤ K := ae_of_all _ hψK'
    have hψi : Integrable ψ (μ.restrict (S ∩ B)) :=
      (integrable_const K).mono' hψ.aestronglyMeasurable hψb
    have hψf : Integrable (fun w => ψ w * M.indicator θ w) (μ.restrict (S ∩ B)) :=
      hfi.bdd_mul hψ.aestronglyMeasurable hψb
    -- Linearity: the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
    have h6 : ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ - c * ∫ w in S ∩ B, ψ w ∂μ =
        ∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ := by
      rw [← integral_const_mul, ← integral_sub hψf (hψi.const_mul c)]
      congr 1
      funext w
      ring
    -- `|ψ (1_M θ - c)| ≤ K |1_M θ - c|`, and `∫ |1_M θ - c| = Λ.toReal`.
    have hle : ‖∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ‖ ≤
        ∫ w in S ∩ B, K * ‖M.indicator θ w - c‖ ∂μ :=
      norm_integral_le_of_norm_le (hfc.norm.const_mul K) (ae_of_all _ fun w => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hψK' w) (norm_nonneg _))
    rw [integral_const_mul, integral_norm_eq_lintegral_enorm hfc.aestronglyMeasurable] at hle
    rw [h2, h1, h6, ← Real.norm_eq_abs]
    exact hle
  -- Weighted approximate tangent space at a Lebesgue point (Simon Ch. 3, 1.4 ⇒ 1.7): if
  -- `Hⁿ((M ∩ B̆_ε(y)) \ S) = 0`, `Hⁿ(S ∩ B̆_ε(y)) < ∞`, `P` is the approximate tangent space of `S`
  -- at `y` and `r⁻ⁿ ∫_{S ∩ B_r(y)} |1_M θ − θ(y)| dHⁿ → 0`, then `P` is the approximate tangent
  -- space of `M` with respect to `θ` at `y`.
  have hPT : ∀ (y : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)) (ε : ℝ), 0 < ε →
      (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 →
      (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P →
      Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ w in S ∩ closedBall y r, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
        (𝓝[>] 0) (𝓝 0) →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
    intro y P ε hε hMSε hSfin hS hleb
    refine ⟨hS.1, fun φ => ?_⟩
    -- `φ` vanishes outside `B_ρ(0)` for some `ρ > 0`, and `|φ| ≤ K`.
    obtain ⟨ρ, hρ, hφρ⟩ := φ.hasCompactSupport.exists_pos_le_norm
    obtain ⟨K, hK⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
    -- The Lebesgue-point hypothesis along the radii `r ρ`: `L(r ρ) < ∞` and `r⁻ⁿ L(r ρ) → 0`.
    obtain ⟨hLfin, hLlim⟩ := Submission.dohr_tp_wtlp_rescaled_limit n
      (fun t => ∫⁻ w in S ∩ closedBall y t, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
      ρ hρ hleb
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * ρ < ε :=
      (((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).eventually
        (eventually_lt_nhds hε)).filter_mono nhdsWithin_le_nhds
    -- `I(r) - θ(y) J(r) → 0` for the weighted and unweighted blow-up integrals `I`, `J`.
    have key : Tendsto (fun r : ℝ =>
        (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' M, φ z * θ (y + r • z)
            ∂(μHE[n] : Measure (Amb n ℓ))) -
          θ y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, φ z
            ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
      have hlimK := hLlim.const_mul K
      rw [mul_zero] at hlimK
      refine squeeze_zero_norm' ?_ hlimK
      filter_upwards [self_mem_nhdsWithin, hsmall, hLfin] with r hr hrε hLr
      have hr' : (0 : ℝ) < r := hr
      have hBε : closedBall y (r * ρ) ⊆ ball y ε := closedBall_subset_ball hrε
      -- `ψ = φ ∘ η_{y,r}` is continuous, bounded by `K`, and vanishes off `B_{rρ}(y)`.
      have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
        show Continuous fun w : Amb n ℓ => r⁻¹ • (w - y) by fun_prop
      have hψ0 : ∀ w, w ∉ closedBall y (r * ρ) →
          φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w) = 0 := by
        intro w hw
        apply hφρ
        rw [mem_closedBall, not_le] at hw
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
          Real.norm_of_nonneg hr'.le, ← dist_eq_norm, le_inv_mul_iff₀ hr']
        exact hw.le
      -- The comparison on `B_{rρ}(y)`, using `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`.
      have hcmpr := hcmp (closedBall y (r * ρ))
        (fun w => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w)) (θ y) K measurableSet_closedBall
        (measure_mono_null (sdiff_subset_sdiff_left (inter_subset_inter_right M hBε)) hMSε)
        (ne_top_of_le_ne_top hSfin (measure_mono (inter_subset_inter_right S hBε)))
        ((map_continuous φ).comp hηc).measurable
        (fun w => by rw [← Real.norm_eq_abs]; exact hK _) hψ0 hLr
      -- Undo the blow-ups: `I(r) = r⁻ⁿ ∫_M ψ θ` and `J(r) = r⁻ⁿ ∫_S ψ`.
      have hJ := rsod_blowUp_setIntegral_eq n ℓ S φ (fun _ => 1) y r hr'
      simp only [mul_one] at hJ
      have hpos : (0 : ℝ) < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr' n)
      rw [rsod_blowUp_setIntegral_eq n ℓ M φ θ y r hr', hJ, Real.norm_eq_abs, mul_left_comm (θ y),
        ← mul_sub, abs_mul, abs_of_pos hpos, mul_left_comm K]
      exact mul_le_mul_of_nonneg_left hcmpr hpos.le
    -- `J(r) → ∫_P φ` by the tangent-space hypothesis on `S`, hence `I(r) → θ(y) ∫_P φ`.
    have h2 := key.add ((hS.2 φ).const_mul (θ y))
    rw [zero_add] at h2
    refine Tendsto.congr (fun r => ?_) h2
    exact sub_add_cancel _ _
  -- `ν = Hⁿ ⌞ (S ∩ O)` has `n`-dimensional growth and `f = 1_M θ` is `ν`-integrable.
  have hνgrowth : ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) (closedBall z r) ≤
        ENNReal.ofReal (C * r ^ n) := by
    intro z r hr
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm (closedBall z r)]
    exact hgrowth z r hr
  have hf : Integrable (M.indicator θ) ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) :=
    (integrableOn_indicator_iff hM).2
      (hθint.mono_set (inter_subset_inter_right M inter_subset_right))
  -- The points of `S ∩ O` that are not Lebesgue points of `f` form an `Hⁿ`-null set.
  have hbad := nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply (S ∩ O) _).trans
    (ae_iff.1 (Submission.dohr_tp_ae_lebesgue_point_of_growth n ℓ
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) (M.indicator θ) C hf hνgrowth)).le)
  -- Inside `M`, the conclusion can only fail on `((M ∩ O) \ S) ∪ (non-Lebesgue points ∩ S ∩ O)`.
  rw [ae_iff, Measure.restrict_apply₀' hM]
  refine measure_mono_null ?_ (measure_union_null hMS hbad)
  rintro y ⟨hy, hyM⟩
  have hyO : y ∈ O := by
    by_contra hyO
    exact hy fun h => absurd h hyO
  by_cases hyS : y ∈ S
  · refine Or.inr ⟨fun hyLeb => hy fun _ P hP => ?_, hyS, hyO⟩
    -- `y ∈ M ∩ O ∩ S` is a Lebesgue point: use a ball `B̆_ε(y) ⊆ O`.
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO y hyO
    have hMε : (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 :=
      measure_mono_null (Set.sdiff_subset_sdiff_left (inter_subset_inter_right M hεO)) hMS
    have hSε : (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono ?_).trans (hgrowth y ε hε))
      exact fun x hx => ⟨⟨hx.1, hεO hx.2⟩, ball_subset_closedBall hx.2⟩
    refine hPT y P ε hε hMε hSε hP (hyLeb.congr' ?_)
    -- For `r < ε`, `B_r(y) ∩ (S ∩ O) = S ∩ B_r(y)`, and `f y = θ y` since `y ∈ M`.
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    have hball : closedBall y r ∩ (S ∩ O) = S ∩ closedBall y r := by
      ext x
      exact ⟨fun hx => ⟨hx.2.1, hx.1⟩,
        fun hx => ⟨hx.2, hx.1, hεO (closedBall_subset_ball hr.2 hx.2)⟩⟩
    rw [Measure.restrict_restrict measurableSet_closedBall, hball, indicator_of_mem hyM]
  · exact Or.inl ⟨⟨hyM, hyO⟩, hyS⟩

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

/-- Simon Ch. 5, Theorem 7.1 (tangent planes of the rotated graph `Q(graph u)`): if `u` is `C¹` on
the open ball `B̆_R(0)` and `G z = (z, u z)`, then the projection `p_{Q(DG(x)(ℝⁿ))}` onto the rotated
tangent plane depends continuously on `x ∈ B̆_R(0)`.  By
`rsod_graphChart_injective_contDiffOn_fderiv_injective` (with `q = id`, `x₀ = 0`), `G` is `C¹` on
the ball with injective derivative there, so `x ↦ DG(x)` is continuous on the ball and
`aetp_starProjection_range_continuousOn` makes `x ↦ p_{DG(x)(ℝⁿ)}` continuous there.  Finally
`p_{Q K} = Q ∘ p_K ∘ Q⁻¹` (`Submodule.starProjection_map_apply`), and composing with the fixed
maps `Q`, `Q⁻¹` is continuous. -/
theorem dohr_tp_projection_continuousOn : ∀ (n ℓ : ℕ) (R : ℝ) (u : Rn n → Rn ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ContinuousOn (fun x : Rn n => (Submodule.map Q.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection) (ball 0 R) := by
  intro n ℓ R u Q hu
  -- The graph map `G z = (z, u z)` is `C¹` on the ball, with injective derivative there.
  obtain ⟨-, hGc, hGi⟩ := rsod_graphChart_injective_contDiffOn_fderiv_injective
    (LinearIsometryEquiv.refl ℝ (Amb n ℓ)) u 0 (ball 0 R) isOpen_ball hu
  have hG : (fun x => (LinearIsometryEquiv.refl ℝ (Amb n ℓ)) (graphPoint x (u x)) + 0) =
      fun z : Rn n => graphPoint z (u z) := by
    funext x
    simp
  rw [hG] at hGc hGi
  set G := fun z : Rn n => graphPoint z (u z)
  -- `x ↦ p_{DG(x)(ℝⁿ)}` is continuous on the ball.
  have hP : ContinuousOn (fun x => (LinearMap.range (fderiv ℝ G x).toLinearMap).starProjection)
      (ball 0 R) :=
    (aetp_starProjection_range_continuousOn n ℓ).comp
      (hGc.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl) fun x hx => hGi x hx
  -- Conjugation by `Q`: `p_{Q K} = Q ∘ p_K ∘ Q⁻¹`.
  let Qc : Amb n ℓ →L[ℝ] Amb n ℓ := Q.toContinuousLinearEquiv
  let Qs : Amb n ℓ →L[ℝ] Amb n ℓ := Q.symm.toContinuousLinearEquiv
  have hconj : ContinuousOn (fun x =>
      Qc.comp ((LinearMap.range (fderiv ℝ G x).toLinearMap).starProjection.comp Qs)) (ball 0 R) :=
    continuousOn_const.clm_comp (hP.clm_comp continuousOn_const)
  refine hconj.congr fun x _ => ?_
  ext1 w
  simp [Submodule.starProjection_map_apply, Qc, Qs]
/-- **Tangent planes of `V` where `spt V` is a `C¹` graph** (Simon Ch. 3, 1.4–1.9).  If
`Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)`, `u ∈ C¹(B̆_R(0))`, `B_s(ξ) ⊆ U` and `s ≤ R`, then
`p_{T_y V}` is the projection onto `Q⁻¹(range DG(x))` for `μ_V`-a.e. `y ∈ B̆_s(ξ)` and every `x`
with `Q(y − ξ) = G(x) = (x, u(x))`, and `y ↦ p_{T_y V}` is `μ_V ⌞ B̆_s(ξ)`-a.e. strongly measurable.
On `B̆_{s'}(ξ)`, `s' < s`, `M` lies in `S = ξ + Q⁻¹(graph u)` up to an `Hⁿ`-null set and `S` has
`n`-dimensional growth, so a.e. the plane `Q⁻¹(range DG(x))` of `S` at `y` is a weighted
approximate tangent plane of `(M, θ)`; uniqueness (`θ(y) > 0`) identifies `tangentProj`.  The
measurable representative is `y ↦ p(π(Q(y − ξ)))`, `π` the first `n` coordinates. -/
theorem dohr_graph_tangent_planes : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → AEStronglyMeasurable (fun y => V.tangentProj y) (V.weight.restrict (ball ξ s)) ∧ ∀ᵐ y ∂V.weight, y ∈ ball ξ s → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
  intro n ℓ hn U _ V ξ s R Q u hs hsR hBU hu hgraph
  -- `A w = ξ + Q⁻¹ w` is an isometry inverting `y ↦ Q (y - ξ)`.
  have hA : Isometry (fun w : Amb n ℓ => ξ + Q.symm w) :=
    Isometry.of_dist_eq fun a b => by rw [dist_add_left, Q.symm.dist_map]
  have hback : ∀ (y : Amb n ℓ) (x : Rn n), Q (y - ξ) = graphPoint x (u x) →
      ξ + Q.symm (graphPoint x (u x)) = y := by
    intro y x h
    rw [← h, LinearIsometryEquiv.symm_apply_apply, add_sub_cancel]
  -- `|a| ≤ |(a, b)|`.
  have hnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖a‖ ≤ ‖graphPoint a b‖ := by
    intro a b
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    rw [Fin.sum_univ_add]
    simp only [graphPoint, Fin.append_left]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  -- Points of `spt V` in `B̆_R(ξ)` lie on the graph after the motion `y ↦ Q (y - ξ)`.
  have hon : ∀ y ∈ V.support, y ∈ ball ξ R →
      ∃ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) := by
    intro y hy hyR
    have hmem : Q (y - ξ) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R :=
      ⟨⟨y - ξ, ⟨y, hy, rfl⟩, rfl⟩, by
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact hyR⟩
    rw [hgraph] at hmem
    obtain ⟨⟨x, hx, hxy⟩, -⟩ := hmem
    exact ⟨x, hx, hxy.symm⟩
  -- `μ_V` is carried by `spt μ_V` and by `M`, and `M \ spt μ_V` is `Hⁿ`-null.
  have hsupp : ∀ᵐ y ∂V.weight, y ∈ V.weight.support := Measure.support_mem_ae
  have hac : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
    withDensity_absolutelyContinuous _ _
  have hmemM : ∀ᵐ y ∂V.weight, y ∈ V.carrier :=
    hac.ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hMsupp : (μHE[n] : Measure (Amb n ℓ)) (V.carrier ∩ V.weight.supportᶜ) = 0 := by
    have h0 : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
        (fun x => ENNReal.ofReal (V.mult x)) V.weight.supportᶜ = 0 :=
      Measure.measure_compl_support
    rw [withDensity_apply_eq_zero' V.aemeasurable_mult.ennreal_ofReal,
      Measure.restrict_apply₀' V.nullMeasurableSet_carrier] at h0
    refine measure_mono_null ?_ h0
    rintro y ⟨hyM, hy⟩
    exact ⟨⟨(ENNReal.ofReal_pos.2 (V.mult_pos y hyM)).ne', hy⟩, hyM⟩
  -- `Q⁻¹(range DG(x))` is the approximate tangent space of `S = A(graph u)` at `A(G x)`.
  have htan : ∀ x ∈ ball (0 : Rn n) R,
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n
        ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) (ξ + Q.symm (graphPoint x (u x)))
        (Submodule.map Q.symm.toLinearEquiv.toLinearMap
          (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)) :=
    fun x hx => Submission.dohr_tp_approx_tangent_affine_isometry n ℓ _ _ ξ Q.symm _
      (Submission.dohr_tp_graph_approx_tangent n ℓ hn R u hu x hx)
  -- The claim on `B̆_{s'}(ξ)` for each `s' < s`.
  have hkey : ∀ s' : ℝ, 0 < s' → s' < s → ∀ᵐ y ∂V.weight, y ∈ ball ξ s' →
      ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) →
        V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
          (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
    intro s' hs' hs's
    have hball : ball ξ s' ⊆ closedBall ξ s :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall hs's.le)
    -- `n`-dimensional growth of `S ∩ B̆_{s'}(ξ)`, through the graph over `B̆_{s'}(0)`.
    obtain ⟨C, -, hC⟩ :=
      Submission.dohr_tp_graph_ball_growth n ℓ hn R s' u hs' (hs's.trans_le hsR) hu
    have hgrowth : ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
        (μHE[n] : Measure (Amb n ℓ)) ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R) ∩
          ball ξ s' ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro z r hr
      refine le_trans (measure_mono ?_) ((hA.euclideanHausdorffMeasure_image
        (graphOver u (ball 0 s') ∩ closedBall (Q (z - ξ)) r)).trans_le (hC (Q (z - ξ)) r hr))
      rintro y ⟨⟨⟨g, ⟨x, -, rfl⟩, rfl⟩, hyb⟩, hyz⟩
      refine ⟨graphPoint x (u x), ⟨⟨x, ?_, rfl⟩, ?_⟩, rfl⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map] at hyb
        rw [mem_ball_zero_iff]
        exact (hnorm x (u x)).trans_lt hyb
      · rw [mem_closedBall] at hyz ⊢
        rw [← Q.symm.dist_map, LinearIsometryEquiv.symm_apply_apply, ← dist_add_left ξ,
          add_sub_cancel]
        exact hyz
    -- `M ∩ B̆_{s'}(ξ)` lies in `S` up to an `Hⁿ`-null set.
    have hnull : (μHE[n] : Measure (Amb n ℓ))
        ((V.carrier ∩ ball ξ s') \ (fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) = 0 := by
      refine measure_mono_null ?_ hMsupp
      rintro y ⟨⟨hyM, hyb⟩, hyS⟩
      refine ⟨hyM, fun hy => hyS ?_⟩
      obtain ⟨x, hx, hxy⟩ :=
        hon y ⟨hBU (hball hyb), hy⟩ (ball_subset_ball (hs's.le.trans hsR) hyb)
      exact ⟨graphPoint x (u x), ⟨x, hx, rfl⟩, hback y x hxy⟩
    have hint : IntegrableOn V.mult (V.carrier ∩ ball ξ s') (μHE[n] : Measure (Amb n ℓ)) :=
      (V.integrableOn_mult _ (isCompact_closedBall ξ s) hBU).mono_set
        (inter_subset_inter_right _ hball)
    have h6 := Submission.dohr_tp_ae_weighted_tangent_of_growth n ℓ V.carrier
      ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) (ball ξ s') V.mult C isOpen_ball
      V.nullMeasurableSet_carrier V.aemeasurable_mult hint hnull hgrowth
    filter_upwards [hac.ae_le h6, hmemM] with y hy6 hyM hyb x hx hxy
    have hT := htan x hx
    rw [hback y x hxy] at hT
    have hW := hy6 hyb _ hT
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult y P :=
      ⟨_, hW⟩
    rw [RectifiableVarifold.tangentProj, dite_eq_left hex]
    congr 1
    exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
      (V.mult_pos y hyM).ne' (Classical.choose_spec hex) hW
  -- Exhaust `B̆_s(ξ)` by the balls `B̆_{s - s/(k+2)}(ξ)`.
  have hsecond : ∀ᵐ y ∂V.weight, y ∈ ball ξ s → ∀ x ∈ ball (0 : Rn n) R,
      Q (y - ξ) = graphPoint x (u x) →
        V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
          (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
    have hrad : ∀ k : ℕ, 0 < s - s / ((k : ℝ) + 2) ∧ s - s / ((k : ℝ) + 2) < s := fun k =>
      ⟨sub_pos.2 (div_lt_self hs (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])),
        sub_lt_self _ (by positivity)⟩
    filter_upwards [ae_all_iff.2 fun k : ℕ => hkey _ (hrad k).1 (hrad k).2] with y hy hys
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 (mem_ball.1 hys)) hs)
    refine hy k (mem_ball.2 ?_)
    have h1 : s / ((k : ℝ) + 2) < s / ((k : ℝ) + 1) :=
      div_lt_div_of_pos_left hs (by positivity) (by linarith)
    have h2 : s / ((k : ℝ) + 1) < s - dist y ξ := by
      rw [div_lt_div_iff₀ (by positivity) hs] at hk
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  refine ⟨?_, hsecond⟩
  -- Measurability: `tangentProj y = p (π (Q (y - ξ)))` a.e., with `p` continuous on `B̆_R(0)`.
  let π : Amb n ℓ → Rn n := fun w => WithLp.toLp 2 (fun i : Fin n => w (Fin.castAdd ℓ i))
  have hπ : Continuous π := by fun_prop
  have hπG : ∀ x : Rn n, π (graphPoint x (u x)) = x := by
    intro x
    ext i
    simp [π, graphPoint]
  let f : Amb n ℓ → Rn n := fun y => π (Q (y - ξ))
  have hf : Continuous f := hπ.comp (Q.continuous.comp (continuous_id.sub continuous_const))
  let p : Rn n → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun x =>
    (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
      (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection
  have hp : ContinuousOn p (ball 0 R) :=
    Submission.dohr_tp_projection_continuousOn n ℓ R u Q.symm hu
  have hae : ∀ᵐ y ∂V.weight.restrict (ball ξ s),
      y ∈ f ⁻¹' ball 0 R ∧ (p ∘ f) y = V.tangentProj y := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hsecond, hsupp] with y hy hyS hys
    obtain ⟨x, hx, hxy⟩ := hon y ⟨hBU (ball_subset_closedBall hys), hyS⟩ (ball_subset_ball hsR hys)
    have hfx : f y = x := by
      show π (Q (y - ξ)) = x
      rw [hxy, hπG]
    refine ⟨by rw [mem_preimage, hfx]; exact hx, ?_⟩
    rw [Function.comp_apply, hfx]
    exact (hy hys x hx hxy).symm
  have hmeas : AEStronglyMeasurable (p ∘ f)
      ((V.weight.restrict (ball ξ s)).restrict (f ⁻¹' ball 0 R)) :=
    (hp.comp hf.continuousOn (mapsTo_preimage f _)).aestronglyMeasurable
      (isOpen_ball.preimage hf).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (hae.mono fun y hy => hy.1)] at hmeas
  exact hmeas.congr (hae.mono fun y hy => hy.2)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): translation invariance (fact (Inv)).**  For
`τ(x) = x − ξ`, the translate `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`; if `V` has generalized mean curvature `H` in `U`, then
`V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`.

`V'` and its structure fields come from `dohr_tv_exists_translate`, the weight from
`dohr_tv_weight_eq_map`, the tangent projections `p_{T_y V'} = p_{T_{y+ξ} V}` from
`dohr_tv_tangentProj_eq`, and the first variation from `dohr_tv_gmc_transfer`.  For the support,
`spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V)` (`dohr_tv_support_map_sub`), which is
`τ(U ∩ spt μ_V)` because `τ` is injective. -/
theorem dohr_translate_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ y, V'.mult y = V.mult (y + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ
  -- Steps 1–2: the translate `V'` in `τ(U)` with carrier `τ(M)` and multiplicity `θ(· + ξ)`.
  obtain ⟨V', hc, hm⟩ := Submission.dohr_tv_exists_translate n ℓ U V ξ
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hw := Submission.dohr_tv_weight_eq_map n ℓ U _ V V' ξ hc hm
  -- Step 5: `p_{T_y V'} = p_{T_{y+ξ} V}` for every `y`.
  have ht := Submission.dohr_tv_tangentProj_eq n ℓ U _ V V' ξ hc hm
  -- Step 6 is `dohr_tv_gmc_transfer`; only the support (Step 4) remains.
  refine ⟨V', hc, hm, hw, ?_, Submission.dohr_tv_gmc_transfer n ℓ U V ξ V' hw ht⟩
  -- Step 4: `spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V) = τ(U ∩ spt μ_V)`.
  show (fun x => x - ξ) '' U ∩ V'.weight.support = (fun x => x - ξ) '' (U ∩ V.weight.support)
  rw [hw, Submission.dohr_tv_support_map_sub n ℓ V.weight ξ,
    Set.image_inter (sub_left_injective (b := ξ))]

/-- **Simon Ch. 5, Theorem 7.1, proof, first paragraph (p. 127).**  Assume Allard's theorem 5.2.
If `V` has generalized mean curvature `H` in the open set `U`, `H` is locally in `Lᵖ(μ_V)` for some
`p > n`, `θ ≥ 1` `μ_V`-a.e. and `Θⁿ(μ_V, ξ) = 1` at `ξ ∈ U`, then there are `R > 0` with
`B_R(ξ) ⊆ U`, a linear isometry `Q` and `u`, `C¹` on `B̆ⁿ_R(0)` with `(1 − n/p)`-Hölder `Du`,
`u(0) = 0` and `Du(0) = 0`, such that `Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)`. -/
theorem dohr_allard_graph_at_density_one : AllardRegularityTheorem → ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∃ R > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), closedBall ξ R ⊆ U ∧ ContDiffOn ℝ 1 u (ball 0 R) ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) R, ∀ y ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K * ‖x - y‖ ^ (1 - (n : ℝ) / p)) ∧ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R := by
  intro hAllard n ℓ hn U hU V H p hp hH hLp hθ ξ hξU hξ
  -- Step 1: Allard's constants `δ₀, γ, C` for `(n, ℓ, p)`; take `δ := δ₀`.
  obtain ⟨δ₀, γ, C, hδ₀, -, hγ, hγ1, hA⟩ := hAllard n ℓ hn p hp
  -- Steps 3–4: `ξ ∈ spt V`, and a scale `ρ` with `B_ρ(ξ) ⊆ U`, mass ratio at most `1 + δ₀` and
  -- scaled `Lᵖ` norm of `H` at most `δ₀`.
  obtain ⟨hξspt, ρ, hρ, hρU, hmass, hLpρ⟩ :=
    density_one_allard_scale V H p ξ δ₀ hU hp hLp hξU hξ hδ₀
  -- Steps 2 and 5: the translate `V'` of `V` by `−ξ`, in the open set `τ(U)`, has
  -- `spt V' = τ(spt V)` and satisfies the hypotheses 5.1 at `(p, δ₀, ρ)`; apply Theorem 5.2.
  obtain ⟨V', -, -, -, hspt, -, hAH⟩ := exists_translated_varifold_allardHypotheses V ξ
  obtain ⟨q, u, hu, hu0, hDu0, hgraph, hnorm⟩ :=
    hA _ (isOpenMap_sub_right ξ U hU) V' _ δ₀ ρ hδ₀ le_rfl
      (hAH H p δ₀ ρ hH hθ hξspt hρ hρU hmass hLpρ)
  -- Step 6: `R := γρ > 0` and `Q := q⁻¹`; the Hölder exponent `1 − n/p` is positive.
  have hR : 0 < γ * ρ := mul_pos hγ hρ
  have hα : 0 < 1 - (n : ℝ) / p := by
    rw [sub_pos, div_lt_one ((Nat.cast_nonneg n).trans_lt hp)]
    exact hp
  -- Steps 7–8: the finite scaled `C^{1,α}` norm makes `u` a `C^{1,α}` function on `B̆ⁿ_R(0)`.
  obtain ⟨hu', -, K, hK⟩ := isHolderCk_one_of_scaledC1AlphaNorm_ne_top u (closedBall 0 (γ * ρ))
    (ball 0 (γ * ρ)) (1 - (n : ℝ) / p) ρ hα hρ hu ball_subset_interior_closedBall
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm)
  -- The first iterated derivative is the derivative, up to a linear isometry.
  have hiter : ∀ z, iteratedFDeriv ℝ 1 u z =
      (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ u z) := by
    intro z
    ext m
    simp
  -- Step 9: `|(x, y)|² = |x|² + |y|²`, so a graph point in `B̆_R(0)` lies over `B̆ⁿ_R(0)`.
  have hsq : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have hle : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := fun x y =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg ‖y‖)).trans (hsq x y).ge)
  refine ⟨γ * ρ, hR, q.symm, u, ?_, by exact_mod_cast hu', hu0, ?_, ⟨K, fun x hx y hy => ?_⟩, ?_⟩
  · -- `B_R(ξ) ⊆ B_ρ(ξ) ⊆ U`, since `γ < 1`.
    exact (closedBall_subset_closedBall (mul_le_of_le_one_left hρ.le hγ1.le)).trans hρU
  · -- `B_R(0)` is a neighbourhood of `0`, so the derivative within it is the derivative.
    rw [← fderivWithin_of_mem_nhds (closedBall_mem_nhds (0 : Rn n) hR)]
    exact hDu0
  · have h := hK x hx y hy
    rwa [hiter, hiter, ← map_sub, LinearIsometryEquiv.norm_map] at h
  · -- Rotate the closed-ball identity of 5.2 back by `Q = q⁻¹` and pass to the open ball.
    rw [← hspt]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] at hz
      obtain ⟨⟨_, ⟨x, -, rfl⟩, rfl⟩, -⟩ : y ∈ q '' graphOver u (closedBall 0 (γ * ρ)) ∩
          closedBall 0 (γ * ρ) := hgraph ▸ ⟨hy, mem_closedBall_zero_iff.2 hz.le⟩
      rw [LinearIsometryEquiv.norm_map] at hz
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact ⟨⟨x, mem_ball_zero_iff.2 ((hle x (u x)).trans_lt hz), rfl⟩, mem_ball_zero_iff.2 hz⟩
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      rw [mem_ball_zero_iff] at hz
      have hq : q (graphPoint x (u x)) ∈ V'.support ∩ closedBall 0 (γ * ρ) := by
        rw [hgraph]
        exact ⟨⟨_, ⟨x, ball_subset_closedBall hx, rfl⟩, rfl⟩,
          mem_closedBall_zero_iff.2 ((q.norm_map _).trans_le hz.le)⟩
      exact ⟨⟨_, hq.1, q.symm_apply_apply _⟩, mem_ball_zero_iff.2 hz⟩
/-- **Fixed-scale comparison on a set carrying `M`.**  If `ψ` is measurable, `|ψ| ≤ K` and `ψ = 0`
off the measurable set `B`, and `Hⁿ ⌞ (M ∩ B)` is carried by `S` with `Hⁿ(S ∩ B) < ∞`, then
`|∫_M ψ θ dHⁿ - c ∫_S ψ dHⁿ| ≤ K ∫_{S ∩ B} |1_M θ - c| dHⁿ`, provided the right side is finite.
Both integrals localize to `S ∩ B`, where the difference is `∫_{S ∩ B} ψ (1_M θ - c) dHⁿ`. -/
theorem dohr_tp_wtlp_ball_comparison_le : ∀ (n ℓ : ℕ) (M S B : Set (Amb n ℓ)) (θ ψ : Amb n ℓ → ℝ) (c K : ℝ), MeasurableSet B → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ B) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ B) ≠ ⊤ → Measurable ψ → (∀ w, |ψ w| ≤ K) → (∀ w, w ∉ B → ψ w = 0) → ∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) ≠ ⊤ → |∫ w in M, ψ w * θ w ∂(μHE[n] : Measure (Amb n ℓ)) - c * ∫ w in S, ψ w ∂(μHE[n] : Measure (Amb n ℓ))| ≤ K * (∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))).toReal := by
  intro n ℓ M S B θ ψ c K
  generalize (μHE[n] : Measure (Amb n ℓ)) = μ
  intro hB hM hθ hMBS hSB hψ hψK hψB hΛ
  have hψK' : ∀ w, ‖ψ w‖ ≤ K := fun w => by rw [Real.norm_eq_abs]; exact hψK w
  -- The `S`-integral localizes to `S ∩ B`, as `ψ = 0` off `B`.
  have h1 : ∫ w in S, ψ w ∂μ = ∫ w in S ∩ B, ψ w ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict S) hψB,
      Measure.restrict_restrict hB, inter_comm B S]
  -- The `M`-integral localizes to `M ∩ B =ᵐ M ∩ (S ∩ B)`, i.e. to the integral of `ψ · 1_M θ`
  -- over `S ∩ B`.
  have h2 : ∫ w in M, ψ w * θ w ∂μ = ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ := by
    have hae : (M ∩ B : Set (Amb n ℓ)) =ᵐ[μ] (M ∩ (S ∩ B) : Set (Amb n ℓ)) := by
      refine ae_eq_set.mpr ⟨measure_mono_null (fun w hw => ?_) hMBS, ?_⟩
      · exact ⟨hw.1, fun hS => hw.2 ⟨hw.1.1, hS, hw.1.2⟩⟩
      · rw [show (M ∩ (S ∩ B)) \ (M ∩ B) = ∅ from
          eq_empty_of_forall_notMem fun w hw => hw.2 ⟨hw.1.1, hw.1.2.2⟩, measure_empty]
    have hMν : NullMeasurableSet M (μ.restrict (S ∩ B)) := hM.mono Measure.restrict_le_self
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict M) (s := B)
        (f := fun w => ψ w * θ w) (fun w hw => by rw [hψB w hw, zero_mul]),
      Measure.restrict_restrict hB, inter_comm B M, setIntegral_congr_set hae,
      ← Measure.restrict_restrict₀ hMν, ← integral_indicator₀ hMν]
    congr 1
    funext w
    exact indicator_mul_right M ψ θ
  -- Integrability on `S ∩ B`, which has finite measure.
  have : IsFiniteMeasure (μ.restrict (S ∩ B)) := isFiniteMeasure_restrict.mpr hSB
  have hf : AEStronglyMeasurable (M.indicator θ) (μ.restrict (S ∩ B)) :=
    ((aemeasurable_indicator_iff₀ hM).mpr hθ).restrict.aestronglyMeasurable
  have hfc : Integrable (fun w => M.indicator θ w - c) (μ.restrict (S ∩ B)) :=
    ⟨hf.sub aestronglyMeasurable_const, hasFiniteIntegral_iff_enorm.mpr hΛ.lt_top⟩
  have hfi : Integrable (M.indicator θ) (μ.restrict (S ∩ B)) :=
    (hfc.add (integrable_const c)).congr (ae_of_all _ fun w => by simp)
  have hψb : ∀ᵐ w ∂(μ.restrict (S ∩ B)), ‖ψ w‖ ≤ K := ae_of_all _ hψK'
  have hψi : Integrable ψ (μ.restrict (S ∩ B)) :=
    (integrable_const K).mono' hψ.aestronglyMeasurable hψb
  have hψf : Integrable (fun w => ψ w * M.indicator θ w) (μ.restrict (S ∩ B)) :=
    hfi.bdd_mul hψ.aestronglyMeasurable hψb
  -- Linearity: the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
  have h6 : ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ - c * ∫ w in S ∩ B, ψ w ∂μ =
      ∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hψf (hψi.const_mul c)]
    congr 1
    funext w
    ring
  -- `|ψ (1_M θ - c)| ≤ K |1_M θ - c|`, and `∫ |1_M θ - c| = Λ.toReal`.
  have hle : ‖∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ‖ ≤
      ∫ w in S ∩ B, K * ‖M.indicator θ w - c‖ ∂μ :=
    norm_integral_le_of_norm_le (hfc.norm.const_mul K) (ae_of_all _ fun w => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hψK' w) (norm_nonneg _))
  rw [integral_const_mul, integral_norm_eq_lintegral_enorm hfc.aestronglyMeasurable] at hle
  rw [h2, h1, h6, ← Real.norm_eq_abs]
  exact hle

/-- **Weighted approximate tangent space at a Lebesgue point** (Simon Ch. 3, 1.4 ⇒ 1.7).
Let `M` be `Hⁿ`-measurable, `θ` be `Hⁿ ⌞ M`-measurable, `Hⁿ((M ∩ B̆_ε(y)) \ S) = 0`,
`Hⁿ(S ∩ B̆_ε(y)) < ∞`, `P` the approximate tangent space of `S` at `y`, and
`r⁻ⁿ ∫_{S ∩ B_r(y)} |1_M θ − θ(y)| dHⁿ → 0`.  Then `P` is the approximate tangent space of `M`
with respect to `θ` at `y`.  For `φ ∈ C_c` vanishing off `B_ρ(0)` with `|φ| ≤ K`, undoing the
blow-up gives `I(r) − θ(y) J(r) = r⁻ⁿ (∫_M ψ θ − θ(y) ∫_S ψ)` with `ψ = φ ∘ η_{y,r}` supported in
`B_{rρ}(y)`, which is at most `K r⁻ⁿ ∫_{S ∩ B_{rρ}(y)} |1_M θ − θ(y)| dHⁿ → 0`. -/
theorem dohr_tp_weighted_tangent_of_lebesgue_point : ∀ (n ℓ : ℕ) (M S : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (y : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)) (ε : ℝ), 0 < ε → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in S ∩ closedBall y r, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
  intro n ℓ M S θ y P ε hε hM hθ hMS hSfin hS hleb
  refine ⟨hS.1, fun φ => ?_⟩
  -- `φ` vanishes outside `B_ρ(0)` for some `ρ > 0`, and `|φ| ≤ K`.
  obtain ⟨ρ, hρ, hφρ⟩ := φ.hasCompactSupport.exists_pos_le_norm
  obtain ⟨K, hK⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- The Lebesgue-point hypothesis along the radii `r ρ`: `L(r ρ) < ∞` and `r⁻ⁿ L(r ρ) → 0`.
  obtain ⟨hLfin, hLlim⟩ := Submission.dohr_tp_wtlp_rescaled_limit n
    (fun t => ∫⁻ w in S ∩ closedBall y t, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
    ρ hρ hleb
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * ρ < ε :=
    (((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).eventually
      (eventually_lt_nhds hε)).filter_mono nhdsWithin_le_nhds
  -- `I(r) - θ(y) J(r) → 0` for the weighted and unweighted blow-up integrals `I`, `J`.
  have key : Tendsto (fun r : ℝ =>
      (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' M, φ z * θ (y + r • z)
          ∂(μHE[n] : Measure (Amb n ℓ))) -
        θ y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, φ z
          ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
    have hlimK := hLlim.const_mul K
    rw [mul_zero] at hlimK
    refine squeeze_zero_norm' ?_ hlimK
    filter_upwards [self_mem_nhdsWithin, hsmall, hLfin] with r hr hrε hLr
    have hr' : (0 : ℝ) < r := hr
    have hBε : closedBall y (r * ρ) ⊆ ball y ε := closedBall_subset_ball hrε
    -- `ψ = φ ∘ η_{y,r}` is continuous, bounded by `K`, and vanishes off `B_{rρ}(y)`.
    have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
      show Continuous fun w : Amb n ℓ => r⁻¹ • (w - y) by fun_prop
    have hψ0 : ∀ w, w ∉ closedBall y (r * ρ) →
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w) = 0 := by
      intro w hw
      apply hφρ
      rw [mem_closedBall, not_le] at hw
      rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
        Real.norm_of_nonneg hr'.le, ← dist_eq_norm, le_inv_mul_iff₀ hr']
      exact hw.le
    -- The comparison on `B_{rρ}(y)`, using `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`.
    have hcmp := Submission.dohr_tp_wtlp_ball_comparison_le n ℓ M S (closedBall y (r * ρ)) θ
      (fun w => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w)) (θ y) K measurableSet_closedBall
      hM hθ (measure_mono_null (sdiff_subset_sdiff_left (inter_subset_inter_right M hBε)) hMS)
      (ne_top_of_le_ne_top hSfin (measure_mono (inter_subset_inter_right S hBε)))
      ((map_continuous φ).comp hηc).measurable
      (fun w => by rw [← Real.norm_eq_abs]; exact hK _) hψ0 hLr
    -- Undo the blow-ups: `I(r) = r⁻ⁿ ∫_M ψ θ` and `J(r) = r⁻ⁿ ∫_S ψ`.
    have hJ := rsod_blowUp_setIntegral_eq n ℓ S φ (fun _ => 1) y r hr'
    simp only [mul_one] at hJ
    have hpos : (0 : ℝ) < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr' n)
    rw [rsod_blowUp_setIntegral_eq n ℓ M φ θ y r hr', hJ, Real.norm_eq_abs, mul_left_comm (θ y),
      ← mul_sub, abs_mul, abs_of_pos hpos, mul_left_comm K]
    exact mul_le_mul_of_nonneg_left hcmp hpos.le
  -- `J(r) → ∫_P φ` by the tangent-space hypothesis on `S`, hence `I(r) → θ(y) ∫_P φ`.
  have h2 := key.add ((hS.2 φ).const_mul (θ y))
  rw [zero_add] at h2
  refine Tendsto.congr (fun r => ?_) h2
  exact sub_add_cancel _ _
theorem dohr_local_monotonicity : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
  have dohrLmonoRadialAux_hasFDerivAt_norm : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
    intro E _ _ y x hxy
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : HasFDerivAt (fun z : E => ‖z - y‖ ^ 2)
        (2 • (innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E)) x :=
      (hasFDerivAt_sub_const (𝕜 := ℝ) y).norm_sq
    have h2 := h1.sqrt (by positivity)
    have h3 : (fun z : E => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ := by
      funext z; exact Real.sqrt_sq (norm_nonneg _)
    rw [h3] at h2
    convert h2 using 1
    ext w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, Real.sqrt_sq hpos.le]
    rw [two_smul]
    field_simp
    ring
  have dohrLmonoRadialAux_hasFDerivAt : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : ℝ → ℝ), ContDiff ℝ 1 φ → ∀ (ρ : ℝ) (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => φ (‖z - y‖ / ρ) • (z - y))
        (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ E +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x := by
    intro E _ _ φ hφ ρ y x hxy
    have hsub : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x :=
      hasFDerivAt_sub_const y
    have hnorm := dohrLmonoRadialAux_hasFDerivAt_norm y x hxy
    have hφd : HasDerivAt φ (deriv φ (‖x - y‖ / ρ)) (‖x - y‖ / ρ) :=
      (hφ.differentiable one_ne_zero _).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) * (1 / ρ)) ‖x - y‖ :=
      hφd.comp (‖x - y‖) ((hasDerivAt_id' (‖x - y‖)).div_const ρ)
    have h2 := h1.comp_hasFDerivAt x hnorm
    exact h2.smul hsub
  have dohrLmonoRadialAux_trace : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : ℝ) (f : E →L[ℝ] ℝ) (v : E) (B : E →L[ℝ] E),
      LinearMap.trace ℝ E ((a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ
          B.toLinearMap) = a * LinearMap.trace ℝ E B.toLinearMap + f (B v) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt
    intro E _ _ _ a f v B
    have hcomp : (a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ B.toLinearMap =
        a • B.toLinearMap + (f.toLinearMap ∘ₗ B.toLinearMap).smulRight v := by
      ext w
      simp
    rw [hcomp, map_add, map_smul, LinearMap.trace_smulRight]
    simp
  have dohrLmonoRadialAux_trace_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E),
      LinearMap.trace ℝ E P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace
    intro E _ _ _ P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  have dohrLmonoRadialAux_inner_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E) (v : E),
      inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection
    intro E _ _ _ P v
    rw [← P.inner_starProjection_left_eq_right v v]
    simpa using P.re_inner_starProjection_eq_normSq v
  have dohrLmonoRadialAux_integrable : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ), Continuous f →
      ∀ (y : Amb n ℓ) (ρ : ℝ), μ (closedBall y ρ) < ∞ → (∀ x, ρ < ‖x - y‖ → f x = 0) →
        Integrable f μ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection
    intro n ℓ μ f hf y ρ hμ h0
    obtain ⟨C, hC⟩ := (isCompact_closedBall y ρ).exists_bound_of_continuousOn hf.continuousOn
    have hon : IntegrableOn f (closedBall y ρ) μ :=
      Measure.integrableOn_of_bounded (M := C) hμ.ne hf.aestronglyMeasurable
        (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx; exact hC x hx)
    have heq : (closedBall y ρ).indicator f = f := by
      funext x
      by_cases hx : x ∈ closedBall y ρ
      · simp [hx]
      · rw [indicator_of_notMem hx, h0 x (by rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx)]
    rw [← heq]
    exact hon.integrable_indicator measurableSet_closedBall
  have dohr_lmono_radial_inequality : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R : ℝ), closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → ∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂V.weight ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm
    intro n ℓ U V H hH y R hBR htan htm φ ρ hφ hanti hφ1 hφ0 hρ hρR
    -- basic facts about `φ`
    have hd_nonpos : ∀ t, deriv φ t ≤ 0 := fun t => hanti.deriv_nonpos
    have hd_zero : ∀ t, 1 < t → deriv φ t = 0 := by
      intro t ht
      have hzero : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [lt_mem_nhds ht] with u hu
        exact hφ0 u hu.le
      exact hzero.deriv_eq.trans (deriv_const t 0)
    have hφc : Continuous φ := hφ.continuous
    have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- the radial vector field
    set X : Amb n ℓ → Amb n ℓ := fun z => φ (‖z - y‖ / ρ) • (z - y) with hXdef
    have hX0 : ∀ z, ρ ≤ ‖z - y‖ → X z = 0 := by
      intro z hz
      have : 1 ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
      simp [hXdef, hφ0 _ this]
    have hXnear : X =ᶠ[𝓝 y] fun z => z - y := by
      filter_upwards [ball_mem_nhds y (half_pos hρ)] with z hz
      rw [mem_ball, dist_eq_norm] at hz
      have : ‖z - y‖ / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
      simp [hXdef, hφ1 _ this]
    have hXcd : ContDiff ℝ 1 X := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hxy : x = y
      · rw [hxy]
        exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq hXnear
      · have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
          (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hxy)
        have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
          hφ.contDiffAt.comp x (h1.div_const ρ)
        exact h2.smul (contDiffAt_id.sub contDiffAt_const)
    have hXsupp : Function.support X ⊆ closedBall y ρ := by
      intro z hz
      by_contra hzB
      rw [mem_closedBall, dist_eq_norm, not_le] at hzB
      exact hz (hX0 z hzB.le)
    have hXcs : HasCompactSupport X :=
      HasCompactSupport.intro (isCompact_closedBall y ρ) fun z hz => by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        exact hX0 z hz.le
    have hXts : tsupport X ⊆ U :=
      (closure_minimal hXsupp isClosed_closedBall).trans
        ((closedBall_subset_closedBall hρR.le).trans hBR)
    -- the generalized mean curvature identity
    have hGMC := hH.2 X hXcd hXcs hXts
    -- derivative of `X`
    have hDX : ∀ x, x ≠ y → HasFDerivAt X (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x :=
      fun x hxy => dohrLmonoRadialAux_hasFDerivAt φ hφ ρ y x hxy
    have hDXy : HasFDerivAt X (ContinuousLinearMap.id ℝ (Amb n ℓ)) y :=
      (hasFDerivAt_sub_const y).congr_of_eventuallyEq hXnear
    have hdiv_formula : ∀ x, x ≠ y → V.divM X x =
        φ (‖x - y‖ / ρ) * LinearMap.trace ℝ (Amb n ℓ) (V.tangentProj x).toLinearMap +
          deriv φ (‖x - y‖ / ρ) * (1 / ρ) *
            (‖x - y‖⁻¹ * inner ℝ (x - y) (V.tangentProj x (x - y))) := by
      intro x hxy
      rw [RectifiableVarifold.divM, (hDX x hxy).fderiv, dohrLmonoRadialAux_trace]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    have hdiv_zero : ∀ x, ρ < ‖x - y‖ → V.divM X x = 0 := by
      intro x hx
      have hxy : x ≠ y := by
        intro h
        rw [h, sub_self, norm_zero] at hx
        linarith
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      rw [hdiv_formula x hxy, hφ0 _ h1.le, hd_zero _ h1]
      ring
    -- the comparison functions
    set g : Amb n ℓ → ℝ := fun x =>
      (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) with hgdef
    set k : Amb n ℓ → ℝ := fun x => (n : ℝ) * φ (‖x - y‖ / ρ) with hkdef
    have hsand : ∀ᵐ x ∂V.weight, g x ≤ V.divM X x ∧ V.divM X x ≤ k x := by
      filter_upwards [htan] with x hx
      by_cases hxR : x ∈ ball y R
      · obtain ⟨P, hPn, hPx⟩ := hx hxR
        by_cases hxy : x = y
        · rw [hxy] at hPx ⊢
          have hdy : V.divM X y = n := by
            rw [RectifiableVarifold.divM, hDXy.fderiv, hPx]
            simp [dohrLmonoRadialAux_trace_starProjection, hPn]
          rw [hdy]
          simp [hgdef, hkdef, hφ1 0 (by norm_num)]
        · have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
          have hsr : ‖P.starProjection (x - y)‖ ≤ ‖x - y‖ := P.norm_starProjection_apply_le _
          have hs0 : 0 ≤ ‖P.starProjection (x - y)‖ := norm_nonneg _
          rw [hdiv_formula x hxy, hPx, dohrLmonoRadialAux_trace_starProjection, hPn,
            dohrLmonoRadialAux_inner_starProjection]
          simp only [hgdef, hkdef]
          have hd : deriv φ (‖x - y‖ / ρ) ≤ 0 := hd_nonpos _
          have h1 : ‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2 ≤ ‖x - y‖ := by
            rw [inv_mul_le_iff₀ hr]
            calc ‖P.starProjection (x - y)‖ ^ 2
                = ‖P.starProjection (x - y)‖ * ‖P.starProjection (x - y)‖ := sq _
              _ ≤ ‖x - y‖ * ‖x - y‖ := mul_self_le_mul_self hs0 hsr
          have hq : (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) ≤ ‖x - y‖ / ρ := by
            calc (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2)
                ≤ (1 / ρ) * ‖x - y‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = ‖x - y‖ / ρ := by ring
          have hq0 : 0 ≤ (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) := by positivity
          have e1 := mul_le_mul_of_nonpos_left hq hd
          have e2 := mul_nonpos_of_nonpos_of_nonneg hd hq0
          constructor
          · linarith
          · linarith
      · have hx' : ρ < ‖x - y‖ := by
          rw [mem_ball, dist_eq_norm, not_lt] at hxR
          linarith
        rw [hdiv_zero x hx']
        have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
        simp [hgdef, hkdef, hφ0 _ h1.le, hd_zero _ h1]
    -- finiteness of the weight on `closedBall y ρ`
    have hμρ : V.weight (closedBall y ρ) < ∞ := by
      have hBρ : closedBall y ρ ⊆ U := (closedBall_subset_closedBall hρR.le).trans hBR
      rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
      exact (V.integrableOn_mult _ (isCompact_closedBall y ρ) hBρ).setLIntegral_lt_top
    -- integrability of the comparison functions
    have hgc : Continuous g := by simp only [hgdef]; fun_prop
    have hkc : Continuous k := by simp only [hkdef]; fun_prop
    have hg_int : Integrable g V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight g hgc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hgdef, hφ0 _ h1.le, hd_zero _ h1]
    have hk_int : Integrable k V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight k hkc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hkdef, hφ0 _ h1.le]
    -- measurability of the tangential divergence
    have hΦ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
        LinearMap.trace ℝ (Amb n ℓ) (p.1.toLinearMap ∘ₗ p.2.toLinearMap)) := by
      have h1 : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
          p.1.comp p.2) :=
        isBoundedBilinearMap_comp.continuous
      have h2 : Continuous (fun A : Amb n ℓ →L[ℝ] Amb n ℓ =>
          LinearMap.trace ℝ (Amb n ℓ) A.toLinearMap) :=
        ((LinearMap.trace ℝ (Amb n ℓ)).comp
          (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
      exact h2.comp h1
    have hDXc : Continuous (fderiv ℝ X) := hXcd.continuous_fderiv one_ne_zero
    have hdivR : AEStronglyMeasurable (fun x => LinearMap.trace ℝ (Amb n ℓ)
        ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap))
        (V.weight.restrict (ball y R)) :=
      hΦ.comp_aestronglyMeasurable (hDXc.aestronglyMeasurable.prodMk htm)
    have hdiv_meas : AEStronglyMeasurable (V.divM X) V.weight := by
      have heq : V.divM X = (ball y R).indicator (V.divM X) := by
        funext x
        by_cases hx : x ∈ ball y R
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          apply hdiv_zero
          rw [mem_ball, dist_eq_norm, not_lt] at hx
          linarith
      rw [heq]
      exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hdivR
    have hdiv_int : Integrable (V.divM X) V.weight :=
      integrable_of_le_of_le hdiv_meas (hsand.mono fun x hx => hx.1)
        (hsand.mono fun x hx => hx.2) hg_int hk_int
    calc ∫ x, g x ∂V.weight ≤ ∫ x, V.divM X x ∂V.weight :=
          integral_mono_ae hg_int hdiv_int (hsand.mono fun x hx => hx.1)
      _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hGMC
      _ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp only [hXdef, real_inner_smul_left]
  have dohr_lmono_curvature_holder : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality
    intro n ℓ p hp μ H ψ y t ht hμB hH hHp hψm hψ01 hψ0
    set B : Set (Amb n ℓ) := closedBall y t with hBdef
    have hBm : MeasurableSet B := measurableSet_closedBall
    set q : ℝ := Real.conjExponent p with hqdef
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    have h1q : 1 / q = 1 - 1 / p := by
      rw [one_div, one_div, hpq.one_sub_inv]
    have hq1 : 1 ≤ q := hpq.symm.lt.le
    -- `ψ` vanishes off `B`
    have hψB : ∀ x, x ∉ B → ψ x = 0 := by
      intro x hx
      apply hψ0
      simpa [hBdef, mem_closedBall, dist_eq_norm, not_le] using hx
    -- `ψ` is integrable
    have hψint : Integrable ψ μ := by
      have h1 : Integrable (B.indicator ψ) μ := by
        refine IntegrableOn.integrable_indicator ?_ hBm
        refine Measure.integrableOn_of_bounded (M := 1) hμB.ne hψm ?_
        exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          exact (hψ01 x).2
      have h2 : B.indicator ψ = ψ := by
        funext x
        by_cases hx : x ∈ B
        · simp [hx]
        · simp [hx, hψB x hx]
      rwa [h2] at h1
    have hIψ : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
    -- pointwise bound
    have hpt : ∀ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ≤
        B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x := by
      intro x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        have hxt : ‖x - y‖ ≤ t := by
          simpa [hBdef, mem_closedBall, dist_eq_norm] using hx
        have hle : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          have h1 : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
          have h2 : ‖x - y‖ * ‖H x‖ ≤ t * ‖H x‖ :=
            mul_le_mul_of_nonneg_right hxt (norm_nonneg _)
          nlinarith [(hψ01 x).1, norm_nonneg (H x)]
        calc ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖
            ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) := by
            rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      · rw [indicator_of_notMem hx, hψB x hx]
        simp
    -- Hölder on `μ.restrict B`
    have hHmeas : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict B) := hH.aestronglyMeasurable.enorm
    have hψmeas : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) (μ.restrict B) :=
      hψm.restrict.aemeasurable.ennreal_ofReal
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq hHmeas hψmeas
    have hψq : (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) := by
      calc (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ)
          ≤ ∫⁻ x in B, ENNReal.ofReal (ψ x) ∂μ := by
            apply lintegral_mono
            intro x
            apply ENNReal.rpow_le_self_of_le_one _ hq1
            exact ENNReal.ofReal_le_one.mpr (hψ01 x).2
        _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ := setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ x, ψ x ∂μ) :=
            (ofReal_integral_eq_lintegral_ofReal hψint (Eventually.of_forall fun x => (hψ01 x).1)).symm
    set X : ℝ≥0∞ := ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ with hXdef
    have hXne : X ≠ ⊤ := hHp.ne
    have hlint : (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ) ≤
        ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
      calc (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ)
          ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x ∂μ :=
            lintegral_mono hpt
        _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) ∂μ :=
            lintegral_indicator hBm _
        _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
            gcongr ENNReal.ofReal t * ?_
            calc (∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ)
                ≤ (∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) *
                    (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ^ (1 / q) := hHolder
              _ ≤ X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q) := by
                  gcongr
    have hfin : ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hXne
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top
    calc |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ|
        = ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ).toReal :=
          norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q))).toReal :=
          ENNReal.toReal_mono hfin hlint
      _ = t * X.toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
            ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hIψ, h1q, mul_assoc]
  have dohrLmonoFixedCutoffAux_phi_nonneg : ∀ {φ : ℝ → ℝ}, Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ (s : ℝ), 0 ≤ φ s := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro φ hanti hcut s
    rcases le_total 1 s with h | h
    · rw [hcut s h]
    · rw [← hcut 1 le_rfl]
      exact hanti h
  have dohrLmonoFixedCutoffAux_deriv_zero : ∀ {φ : ℝ → ℝ}, (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ {s : ℝ}, 1 < s → deriv φ s = 0 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hcut s hs
    have hzero : φ =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hs] with u hu
      exact hcut u hu.le
    exact hzero.deriv_eq.trans (deriv_const s 0)
  have dohrLmonoFixedCutoffAux_deriv_bound : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → |s * deriv φ s| ≤ C := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hφ hcut
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hφ.continuous_deriv_one.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    rcases le_or_gt s 1 with h1 | h1
    · have h := hC s ⟨hs, h1⟩
      rw [Real.norm_eq_abs] at h
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |deriv φ s| ≤ 1 * |deriv φ s| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |deriv φ s| := one_mul _
        _ ≤ max C 0 := h.trans (le_max_left _ _)
    · rw [dohrLmonoFixedCutoffAux_deriv_zero hcut h1, mul_zero, abs_zero]
      exact le_max_right _ _
  have dohrLmonoFixedCutoffAux_hasDerivAt : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ (c : ℝ) {t : ℝ}, t ≠ 0 →
      HasDerivAt (fun u => φ (c / u)) (-(c / t * deriv φ (c / t)) / t) t := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound
    intro φ hφ c t ht
    have h1 : HasDerivAt (fun u : ℝ => c / u) (c * -(t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht).const_mul c
      convert this using 1
      funext u
      exact div_eq_mul_inv c u
    have h2 := ((hφ.differentiable (by simp) (c / t)).hasDerivAt).comp t h1
    have heq : -(c / t * deriv φ (c / t)) / t = deriv φ (c / t) * (c * -(t ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  have dohrLmonoFixedCutoffAux_npow : ∀ (n : ℕ) {ρ : ℝ}, ρ ≠ 0 → (n : ℝ) * ρ ^ (n - 1) = n * ρ ^ n / ρ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt
    intro n ρ hρ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [eq_div_iff hρ, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  have dohr_lmono_fixed_cutoff_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (R M β : ℝ), β < 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 R) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro n ℓ μ H y φ I a R M β hβ hμR hH hφ hanti hcut hrad hI ha hab
    -- the curvature integral `L`
    obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ,
        ∀ t, L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ := ⟨_, fun t => rfl⟩
    have ha' : ∀ t, a t = L t / t ^ (n + 1) / (1 + I t / t ^ n) := fun t => by
      rw [ha t, hL t]
    have hrad' : ∀ ρ : ℝ, 0 < ρ → ρ < R →
        ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -L ρ :=
      fun ρ h1 h2 => by rw [hL ρ]; exact hrad ρ h1 h2
    clear ha hrad
    set S : Set (Amb n ℓ) := closedBall y R with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    set ν : Measure (Amb n ℓ) := μ.restrict S with hνdef
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := hH
    have hφnn := dohrLmonoFixedCutoffAux_phi_nonneg hanti hcut
    obtain ⟨C, hC0, hC⟩ := dohrLmonoFixedCutoffAux_deriv_bound hφ hcut
    have hφc : Continuous φ := hφ.continuous
    have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- outside `S`, all the scaled profiles vanish
    have hout : ∀ t, 0 < t → t < R → ∀ x, x ∉ S → 1 < ‖x - y‖ / t := by
      intro t ht htR x hx
      have hRx : R < ‖x - y‖ := by
        simpa [hSdef, mem_closedBall, dist_eq_norm, not_le] using hx
      rw [lt_div_iff₀ ht]
      linarith
    -- conversion of the integrals to `ν`
    have hIν : ∀ t, 0 < t → t < R → I t = ∫ x, φ (‖x - y‖ / t) ∂ν := by
      intro t ht htR
      rw [hI t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hcut _ (hout t ht htR x hx).le
    have hLν : ∀ t, 0 < t → t < R →
        L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro t ht htR
      rw [hL t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hcut _ (hout t ht htR x hx).le, zero_mul]
    -- derivative of the profile in the scale variable
    set F' : ℝ → Amb n ℓ → ℝ := fun t x => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t
      with hF'eq
    have hIderiv : ∀ ρ, 0 < ρ → ρ < R → HasDerivAt I (∫ x, F' ρ x ∂ν) ρ := by
      intro ρ hρ hρR
      have hmain : HasDerivAt (fun t => ∫ x, φ (‖x - y‖ / t) ∂ν) (∫ x, F' ρ x ∂ν) ρ := by
        have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
          (F := fun t x => φ (‖x - y‖ / t)) (F' := F') (x₀ := ρ) (bound := fun _ => 2 * C / ρ)
          (Ioo_mem_nhds (half_lt_self hρ) hρR) ?_ ?_ ?_ ?_ ?_ ?_
        · exact key.2
        · exact Eventually.of_forall fun t =>
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        · refine Integrable.of_bound
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
            (φ 0) (Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (hφnn _)]
          exact hanti (div_nonneg (norm_nonneg _) hρ.le)
        · have hcont : Continuous (F' ρ) := by
            simp only [hF'eq]
            fun_prop
          exact hcont.aestronglyMeasurable
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          simp only [hF'eq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos ht0]
          calc |‖x - y‖ / t * deriv φ (‖x - y‖ / t)| / t ≤ C / t :=
                div_le_div_of_nonneg_right (hC _ (div_nonneg (norm_nonneg _) ht0.le)) ht0.le
            _ ≤ 2 * C / ρ := by
                rw [div_le_div_iff₀ ht0 hρ]
                nlinarith [ht.1]
        · exact integrable_const _
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          exact dohrLmonoFixedCutoffAux_hasDerivAt hφ ‖x - y‖ ht0.ne'
      refine hmain.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact hIν t ht.1 ht.2
    -- continuity of `L`
    have hLcont : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt L ρ := by
      intro ρ hρ hρR
      have hmain : ContinuousAt
          (fun t => ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν) ρ := by
        apply continuousAt_of_dominated (bound := fun x => φ 0 * (R * ‖H x‖))
        · refine Eventually.of_forall fun t => ?_
          have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ (‖x - y‖ / t)) ν :=
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
            continuous_inner.comp_aestronglyMeasurable
              ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
                hHν.aestronglyMeasurable)
          exact h1.mul h2
        · filter_upwards [Ioi_mem_nhds hρ] with t ht
          rw [hνdef, ae_restrict_iff' hSm]
          refine Eventually.of_forall fun x hx => ?_
          have hxR : ‖x - y‖ ≤ R := by
            simpa [hSdef, mem_closedBall, dist_eq_norm] using hx
          have hσ : 0 ≤ ‖x - y‖ / t := div_nonneg (norm_nonneg _) (le_of_lt ht)
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφnn _)]
          have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
            (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
          exact mul_le_mul (hanti hσ) hinner (norm_nonneg _) (hφnn 0)
        · exact (hHν.norm.const_mul R).const_mul (φ 0)
        · refine Eventually.of_forall fun x => ?_
          exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id hρ.ne')).mul
            continuousAt_const
      refine hmain.congr ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact (hLν t ht.1 ht.2).symm
    -- the key differential inequality
    have hkey : ∀ ρ, 0 < ρ → ρ < R → L ρ ≤ ρ * (∫ x, F' ρ x ∂ν) - n * I ρ := by
      intro ρ hρ hρR
      have h1 := hrad' ρ hρ hρR
      have hconv : ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ =
          ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂ν := by
        rw [hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        have h := hout ρ hρ hρR x hx
        rw [hcut _ h.le, dohrLmonoFixedCutoffAux_deriv_zero hcut h]
        ring
      have hint1 : Integrable (fun x => φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
          (φ 0) (Eventually.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (hφnn _)]
        exact hanti (div_nonneg (norm_nonneg _) hρ.le)
      have hint2 : Integrable (fun x => ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (by fun_prop : Continuous fun x : Amb n ℓ =>
            ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)).aestronglyMeasurable
          C (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hC _ (div_nonneg (norm_nonneg _) hρ.le)
      rw [hconv, integral_add (hint1.const_mul _) hint2, integral_const_mul,
        ← hIν ρ hρ hρR] at h1
      have hF'int : ∫ x, F' ρ x ∂ν = -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ := by
        simp only [hF'eq]
        rw [integral_div, integral_neg]
      rw [hF'int]
      have hρne : ρ ≠ 0 := hρ.ne'
      have hsimp : ρ * (-(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ) =
          -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) := by
        field_simp
      rw [hsimp]
      linarith
    -- basic facts on `I`
    have hInn : ∀ ρ, 0 ≤ I ρ := fun ρ => by
      rw [hI ρ]
      exact integral_nonneg fun x => hφnn _
    have hden : ∀ ρ, 0 < ρ → 1 ≤ 1 + I ρ / ρ ^ n := fun ρ h1 => by
      have := div_nonneg (hInn ρ) (pow_pos h1 n).le
      linarith
    -- continuity of `a`
    have hacontAt : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt a ρ := by
      intro ρ h1 h2
      have haeq : a = fun t => L t / t ^ (n + 1) / (1 + I t / t ^ n) := funext ha'
      rw [haeq]
      exact ((hLcont ρ h1 h2).div ((continuous_pow (n + 1)).continuousAt) (pow_ne_zero _ h1.ne')).div
        (continuousAt_const.add ((hIderiv ρ h1 h2).continuousAt.div ((continuous_pow n).continuousAt)
          (pow_ne_zero _ h1.ne')))
        (by linarith [hden ρ h1])
    have hacont : ContinuousOn a (Ioo 0 R) := fun ρ hρ =>
      (hacontAt ρ hρ.1 hρ.2).continuousWithinAt
    refine ⟨hacont, ?_⟩
    -- the fundamental theorem of calculus for `∫₀^ρ a`
    have hGderiv : ∀ ρ, 0 < ρ → ρ < R →
        HasDerivAt (fun u => ∫ t in (0)..u, a t) (a ρ) ρ := by
      intro ρ h1 h2
      apply intervalIntegral.integral_hasDerivAt_right
      · refine IntervalIntegrable.mono_fun' (g := fun t => M * t ^ (-β)) ?_ ?_ ?_
        · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
        · rw [uIoc_of_le h1.le]
          exact (hacont.mono (Ioc_subset_Ioo_right h2)).aestronglyMeasurable measurableSet_Ioc
        · rw [uIoc_of_le h1.le]
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
          show ‖a t‖ ≤ M * t ^ (-β)
          rw [Real.norm_eq_abs]
          exact hab t ht.1 (lt_of_le_of_lt ht.2 h2)
      · exact hacont.stronglyMeasurableAtFilter isOpen_Ioo ρ ⟨h1, h2⟩
      · exact hacontAt ρ h1 h2
    -- derivative of the monotone quantity
    have hΨ : ∀ ρ ∈ Ioo 0 R, ∃ D : ℝ,
        HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) D ρ ∧ 0 ≤ D := by
      rintro ρ ⟨h1, h2⟩
      have hG := hGderiv ρ h1 h2
      have hIρ := hIderiv ρ h1 h2
      have hd := (hG.neg.exp).mul
        ((hasDerivAt_const ρ (1 : ℝ)).add (hIρ.div (hasDerivAt_pow n ρ) (pow_ne_zero n h1.ne')))
      have hd' : HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n))
          (Real.exp (-∫ t in (0)..ρ, a t) * -a ρ * (1 + I ρ / ρ ^ n) +
            Real.exp (-∫ t in (0)..ρ, a t) * (0 + ((∫ x, F' ρ x ∂ν) * ρ ^ n -
              I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2)) ρ := hd
      refine ⟨_, hd', ?_⟩
      set E := Real.exp (-∫ t in (0)..ρ, a t) with hEdef
      set I' := ∫ x, F' ρ x ∂ν with hI'eq
      have hE : 0 < E := Real.exp_pos _
      have hP : 0 < ρ ^ n := pow_pos h1 n
      have hden' : 1 + I ρ / ρ ^ n ≠ 0 := by linarith [hden ρ h1]
      have haL : a ρ * (1 + I ρ / ρ ^ n) = L ρ / (ρ ^ n * ρ) := by
        rw [ha' ρ, div_mul_cancel₀ _ hden', pow_succ]
      have hq : (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2 =
          (ρ * I' - n * I ρ) / (ρ ^ n * ρ) := by
        rw [dohrLmonoFixedCutoffAux_npow n h1.ne']
        field_simp
      have hkeyρ := hkey ρ h1 h2
      have hnum : 0 ≤ (ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ) :=
        div_nonneg (by linarith) (by positivity)
      have hfinal : E * -a ρ * (1 + I ρ / ρ ^ n) +
          E * (0 + (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2) =
          E * ((ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ)) := by
        linear_combination (-E) * haL + E * hq
      rw [hfinal]
      exact mul_nonneg hE.le hnum
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 R)
    · intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, hD0⟩ := hΨ ρ hρ
      rw [hD.deriv]
      exact hD0
  have dohrLmonoOpenBallAux_cutoffs : ∃ φ : ℕ → ℝ → ℝ,
      (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧
      (∀ k (t : ℝ), t ≤ 1 / 2 → φ k t = 1) ∧ (∀ k (t : ℝ), 1 ≤ t → φ k t = 0) ∧
      (∀ k t, 0 ≤ φ k t ∧ φ k t ≤ 1) ∧
      (∀ s : ℝ, s < 1 → ∀ᶠ k in atTop, φ k s = 1) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone
    refine ⟨fun k s => 1 - Real.smoothTransition (((k : ℝ) + 3) * (s - 1) + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
    · intro k s t hst
      have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      have := Real.smoothTransition.monotone h1
      simp only
      linarith
    · intro k t ht
      have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have h1 : ((k : ℝ) + 3) * (t - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
    · intro k t ht
      have hk : (0 : ℝ) ≤ (k : ℝ) + 3 := by positivity
      have h1 : 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      simp only
      rw [Real.smoothTransition.one_of_one_le h1, sub_self]
    · intro k t
      have h0 := Real.smoothTransition.nonneg (((k : ℝ) + 3) * (t - 1) + 1)
      have h1 := Real.smoothTransition.le_one (((k : ℝ) + 3) * (t - 1) + 1)
      constructor <;> simp only <;> linarith
    · intro s hs
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (1 - s))
      rw [eventually_atTop]
      refine ⟨k₀, fun k hk => ?_⟩
      have hs1 : 0 < 1 - s := by linarith
      have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      have h2 : 1 / (1 - s) < (k : ℝ) + 3 := by linarith
      have h3 : 1 < ((k : ℝ) + 3) * (1 - s) := by
        rw [div_lt_iff₀ hs1] at h2
        linarith
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
  have dohrLmonoOpenBallAux_rpow_le : ∀ {b e : ℝ}, 0 ≤ b → 0 ≤ e → e ≤ 1 → b ^ e ≤ 1 + b := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
    intro b e hb he0 he1
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h he0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h he1
      rw [Real.rpow_one] at this
      linarith
  have dohrLmonoOpenBallAux_abound : ∀ (n : ℕ) {p t N I L : ℝ}, 1 < p → 0 < t → 0 ≤ N → 0 ≤ I →
      |L| ≤ t * N * I ^ (1 - 1 / p) →
        |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ N * t ^ (-((n : ℝ) / p)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
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
    have hbe := dohrLmonoOpenBallAux_rpow_le hb he0 he1
    have hden : 0 < 1 + b := by linarith
    have hT : 0 < t ^ ((n : ℝ) * (1 - 1 / p)) := Real.rpow_pos_of_pos ht _
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
  have dohrLmonoOpenBallAux_small : ∀ {n : ℕ} {p R κ : ℝ} {J : ℝ≥0∞}, 0 < p → 0 < R → 0 ≤ κ →
      (ENNReal.ofReal (R ^ (p - n)) * J) ^ (1 / p) ≤ ENNReal.ofReal κ →
        J ≠ ⊤ ∧ J.toReal ^ (1 / p) * R ^ (1 - (n : ℝ) / p) ≤ κ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound
    intro n p R κ J hp0 hR hκ h
    have hRp : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
    have hp1 : 0 < 1 / p := by positivity
    have hJ : J ≠ ⊤ := by
      intro hJ
      rw [hJ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hRp).ne', ENNReal.top_rpow_of_pos hp1,
        top_le_iff] at h
      exact ENNReal.ofReal_ne_top h
    refine ⟨hJ, ?_⟩
    have hJ' : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ).symm
    rw [hJ', ← ENNReal.ofReal_mul hRp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRp.le ENNReal.toReal_nonneg) hp1.le,
      ENNReal.ofReal_le_ofReal_iff hκ] at h
    rw [Real.mul_rpow hRp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hR.le] at h
    have he : (p - n) * (1 / p) = 1 - (n : ℝ) / p := by
      field_simp
    rw [he] at h
    linarith
  have dohrLmonoOpenBallAux_limit : ∀ (n : ℕ) {R Λ N β : ℝ}, 0 < R → β < 1 → 0 ≤ N →
      N * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → 0 < Λ → Λ ≤ 1 →
      ∀ (a : ℕ → ℝ → ℝ) (I : ℕ → ℝ → ℝ) (a₀ m : ℝ → ℝ),
      (∀ k, ContinuousOn (a k) (Ioo 0 R)) →
      (∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-β)) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => I k t) atTop (𝓝 (m t))) →
      (∀ k, MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n))
        (Ioo 0 R)) →
      ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧
        (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧
        Tendsto F (𝓝[>] 0) (𝓝 1) ∧
        MonotoneOn (fun r => F r * (r ^ n)⁻¹ * m r + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small
    intro n R Λ N β hR hβ1 hN hNR hΛ hΛ1 a I a₀ m hacont hab halim hIlim hmono
    -- the dominating function is integrable near `0`
    have hgint : ∀ ρ, IntervalIntegrable (fun t => N * t ^ (-β)) volume 0 ρ := fun ρ =>
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul N
    -- the bound passes to the limit
    have ha₀b : ∀ t, 0 < t → t < R → |a₀ t| ≤ N * t ^ (-β) := by
      intro t ht htR
      exact le_of_tendsto ((continuous_abs.tendsto _).comp (halim t ht htR))
        (Eventually.of_forall fun k => hab k t ht htR)
    -- measurability
    have hameas : ∀ k ρ, ρ < R → AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 ρ)) := by
      intro k ρ hρR
      exact ((hacont k).mono (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hρR⟩)).aestronglyMeasurable
        measurableSet_Ioc
    have ha₀meas : ∀ ρ, ρ < R → AEStronglyMeasurable a₀ (volume.restrict (Ioc 0 ρ)) := by
      intro ρ hρR
      refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => hameas k ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    have ha₀int : ∀ ρ, 0 ≤ ρ → ρ < R → IntegrableOn a₀ (Ioc 0 ρ) := by
      intro ρ hρ hρR
      have hg : IntegrableOn (fun t => N * t ^ (-β)) (Ioc 0 ρ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ).mp (hgint ρ)
      refine hg.mono' (ha₀meas ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
    -- convergence of the integrals
    have hGlim : ∀ ρ, 0 < ρ → ρ < R →
        Tendsto (fun k => ∫ t in (0)..ρ, a k t) atTop (𝓝 (∫ t in (0)..ρ, a₀ t)) := by
      intro ρ hρ hρR
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => N * t ^ (-β)) ?_ ?_ (hgint ρ) ?_
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => hameas k ρ hρR
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact hab k t ht.1 (lt_of_le_of_lt ht.2 hρR)
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    set G : ℝ → ℝ := fun ρ => ∫ t in (0)..ρ, a₀ t with hGdef
    -- bound on `G`
    have hGb : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ N * ρ ^ (1 - β) / (1 - β) := by
      intro ρ hρ hρR
      have h1 : ‖∫ t in (0)..ρ, a₀ t‖ ≤ ∫ t in (0)..ρ, N * t ^ (-β) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hρ.le ?_ (hgint ρ)
        exact Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
      have h2 : ∫ t in (0)..ρ, N * t ^ (-β) = N * ρ ^ (1 - β) / (1 - β) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h3 : -β + 1 = 1 - β := by ring
        rw [h3, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]
      rw [h2] at h1
      rw [← Real.norm_eq_abs]
      exact h1
    have hGΛ : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ Λ / 4 := by
      intro ρ hρ hρR
      refine (hGb ρ hρ hρR).trans (le_trans ?_ hNR)
      have h1β : 0 < 1 - β := by linarith
      apply div_le_div_of_nonneg_right _ h1β.le
      apply mul_le_mul_of_nonneg_left _ hN
      exact Real.rpow_le_rpow hρ.le hρR.le h1β.le
    set F : ℝ → ℝ := fun ρ => Real.exp (-G ρ) with hFdef
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · -- continuity
      intro ρ hρ
      have hρ1 : ρ < (ρ + R) / 2 := by linarith [hρ.2]
      have hρ1R : (ρ + R) / 2 < R := by linarith [hρ.2]
      have hρ0 : (0 : ℝ) ≤ (ρ + R) / 2 := by linarith [hρ.1]
      have hint : IntegrableOn a₀ (uIcc 0 ((ρ + R) / 2)) := by
        rw [uIcc_of_le hρ0, integrableOn_Icc_iff_integrableOn_Ioc]
        exact ha₀int _ hρ0 hρ1R
      have hc := intervalIntegral.continuousOn_primitive_interval hint
      have hmem : uIcc 0 ((ρ + R) / 2) ∈ 𝓝 ρ := by
        rw [uIcc_of_le hρ0]
        exact Icc_mem_nhds hρ.1 hρ1
      have hcG : ContinuousAt G ρ := hc.continuousAt hmem
      exact (Real.continuous_exp.continuousAt.comp hcG.neg).continuousWithinAt
    · intro r hr
      have h := hGΛ r hr.1 hr.2
      have h' := abs_le.mp h
      refine ⟨?_, ?_, ?_⟩
      · have h1 : |-G r| ≤ 1 := by rw [abs_neg]; linarith
        have h2 := Real.abs_exp_sub_one_le h1
        rw [abs_neg] at h2
        show |Real.exp (-G r) - 1| ≤ Λ
        linarith
      · show Real.exp (-Λ) ≤ Real.exp (-G r)
        exact Real.exp_le_exp.mpr (by linarith)
      · show Real.exp (-G r) ≤ Real.exp Λ
        exact Real.exp_le_exp.mpr (by linarith)
    · -- limit at `0`
      have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
        have hlim : Tendsto (fun ρ : ℝ => N * ρ ^ (1 - β) / (1 - β)) (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ρ : ℝ => ρ ^ (1 - β)) (𝓝 0) (𝓝 0) := by
            have := Real.continuousAt_rpow_const 0 (1 - β) (Or.inr (by linarith))
            rw [ContinuousAt, Real.zero_rpow (by linarith)] at this
            exact this
          have h2 := (h1.const_mul N).div_const (1 - β)
          rw [mul_zero, zero_div] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        refine squeeze_zero_norm' ?_ hlim
        have : Ioo (0 : ℝ) R ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hR
        filter_upwards [this] with ρ hρ
        rw [Real.norm_eq_abs]
        exact hGb ρ hρ.1 hρ.2
      have := (Real.continuous_exp.tendsto (-0)).comp hG0.neg
      rw [neg_zero, Real.exp_zero] at this
      exact this
    · -- monotonicity
      have hΨlim : ∀ ρ ∈ Ioo 0 R, Tendsto
          (fun k => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) atTop
          (𝓝 (F ρ * (1 + m ρ / ρ ^ n))) := by
        intro ρ hρ
        have h1 := (Real.continuous_exp.tendsto _).comp (hGlim ρ hρ.1 hρ.2).neg
        have h2 := (hIlim ρ hρ.1 hρ.2).div_const (ρ ^ n)
        exact h1.mul (tendsto_const_nhds.add h2)
      intro σ hσ ρ hρ hσρ
      have h := le_of_tendsto_of_tendsto' (hΨlim σ hσ) (hΨlim ρ hρ) (fun k => hmono k hσ hρ hσρ)
      have e : ∀ r, F r * (r ^ n)⁻¹ * m r + F r - 1 = F r * (1 + m r / r ^ n) - 1 := by
        intro r
        ring
      show F σ * (σ ^ n)⁻¹ * m σ + F σ - 1 ≤ F ρ * (ρ ^ n)⁻¹ * m ρ + F ρ - 1
      rw [e σ, e ρ]
      linarith
  have dohr_lmono_open_ball_monotone : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧ (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohrLmonoOpenBallAux_rpow_le
    intro n ℓ hn p hnp μ H y R Λ hR hΛ hΛ1 hμR hH hsmall hrad
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp1 : 1 < p := by linarith
    have hp0 : 0 < p := by linarith
    have hβ1 : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hnp
    have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
      mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ.le
    obtain ⟨hJ, hNR⟩ := dohrLmonoOpenBallAux_small hp0 hR hκ hsmall
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
      ⟨_, rfl⟩
    rw [← hNdef] at hNR
    have hN0 : 0 ≤ N := by
      rw [hNdef]
      exact Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hNR' : N * R ^ (1 - (n : ℝ) / p) / (1 - (n : ℝ) / p) ≤ Λ / 4 := by
      have h1 : 0 < 1 - (n : ℝ) / p := by linarith
      rw [div_le_iff₀ h1]
      calc N * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := hNR
        _ = Λ / 4 * (1 - (n : ℝ) / p) := by
            field_simp
    have hNt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ N := by
      intro t htR
      rw [hNdef]
      exact Real.rpow_le_rpow ENNReal.toReal_nonneg
        (ENNReal.toReal_mono hJ (lintegral_mono_set (closedBall_subset_closedBall htR)))
        (by positivity)
    have hJt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ) < ⊤ := fun t htR =>
      lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall htR)) hJ.lt_top
    -- the cutoffs
    obtain ⟨φ, hφC, hφanti, hφone, hφzero, hφ01, hφlim⟩ := dohrLmonoOpenBallAux_cutoffs
    have hφc : ∀ k, Continuous (φ k) := fun k => (hφC k).continuous
    -- the cutoff quantities
    obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t =
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I k t / t ^ n) :=
      ⟨_, fun _ _ => rfl⟩
    have hzero_far : ∀ k t, 0 < t → ∀ x : Amb n ℓ, t ≤ ‖x - y‖ → φ k (‖x - y‖ / t) = 0 := by
      intro k t ht x hx
      exact hφzero k _ ((one_le_div ht).mpr hx)
    have hInn : ∀ k t, 0 ≤ I k t := fun k t => by
      rw [hI]
      exact integral_nonneg fun x => (hφ01 k _).1
    -- the uniform curvature bound, from the Hölder sibling
    have hab : ∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-((n : ℝ) / p)) := by
      intro k t ht htR
      have hμt : μ (closedBall y t) < ⊤ :=
        lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall htR.le)) hμR
      have hHt : IntegrableOn H (closedBall y t) μ :=
        hH.mono_set (closedBall_subset_closedBall htR.le)
      have hhol : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) *
            (∫ x, φ k (‖x - y‖ / t) ∂μ) ^ (1 - 1 / p) :=
        dohr_lmono_curvature_holder n ℓ p hp1 μ H (fun x => φ k (‖x - y‖ / t)) y t ht.le hμt hHt
          (hJt t htR.le)
          ((hφc k).comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          (fun x => hφ01 k (‖x - y‖ / t)) (fun x hx => hzero_far k t ht x hx.le)
      have hL : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * N * I k t ^ (1 - 1 / p) := by
        refine hhol.trans ?_
        rw [← hI]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hNt t htR.le) ht.le)
          (Real.rpow_nonneg (hInn k t) _)
      rw [ha]
      exact dohrLmonoOpenBallAux_abound n hp1 ht hN0 (hInn k t) hL
    -- fixed-cutoff monotonicity, from the sibling
    have hfix : ∀ k, ContinuousOn (a k) (Ioo 0 R) ∧
        MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) (Ioo 0 R) :=
      fun k => dohr_lmono_fixed_cutoff_monotone n ℓ μ H y (φ k) (I k) (a k) R N ((n : ℝ) / p) hβ1
        hμR hH (hφC k) (hφanti k) (hφzero k)
        (fun ρ h1 h2 => hrad (φ k) ρ (hφC k) (hφanti k) (hφone k) (hφzero k) h1 h2) (hI k) (ha k)
        (hab k)
    -- passage to the limit `k → ∞` under the integral sign
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y R) := ⟨_, rfl⟩
    have hνfin : IsFiniteMeasure ν := by
      rw [hν]
      exact isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := by
      rw [hν]
      exact hH
    have hout : ∀ t, t < R → ∀ x, x ∉ closedBall y R → t ≤ ‖x - y‖ := by
      intro t htR x hx
      have : R < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      linarith
    have hIν : ∀ k t, 0 < t → t < R → I k t = ∫ x, φ k (‖x - y‖ / t) ∂ν := by
      intro k t ht htR
      rw [hI, hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hzero_far k t ht x (hout t htR x hx)
    have hLν : ∀ k t, 0 < t → t < R →
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro k t ht htR
      rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hzero_far k t ht x (hout t htR x hx), zero_mul]
    have hφpt : ∀ t, 0 < t → ∀ x : Amb n ℓ, Tendsto (fun k => φ k (‖x - y‖ / t)) atTop
        (𝓝 ((ball y t).indicator (fun _ => (1 : ℝ)) x)) := by
      intro t ht x
      by_cases hx : x ∈ ball y t
      · rw [indicator_of_mem hx]
        have hlt : ‖x - y‖ / t < 1 := by
          rw [div_lt_one ht]
          simpa [mem_ball, dist_eq_norm] using hx
        exact tendsto_const_nhds.congr' ((hφlim _ hlt).mono fun k hk => hk.symm)
      · rw [indicator_of_notMem hx]
        have hle : t ≤ ‖x - y‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
        have : (fun k => φ k (‖x - y‖ / t)) = fun _ => 0 :=
          funext fun k => hzero_far k t ht x hle
        rw [this]
        exact tendsto_const_nhds
    have hIlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => I k t) atTop (𝓝 ((μ (ball y t)).toReal)) := by
      intro t ht htR
      have hm : ∫ x, (ball y t).indicator (fun _ => (1 : ℝ)) x ∂ν = (μ (ball y t)).toReal := by
        rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one,
          Measure.real_def, hν, Measure.restrict_apply measurableSet_ball,
          inter_eq_left.mpr (ball_subset_closedBall.trans (closedBall_subset_closedBall htR.le))]
      rw [← hm]
      have hcongr : (fun k => I k t) = fun k => ∫ x, φ k (‖x - y‖ / t) ∂ν :=
        funext fun k => hIν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1)
        ?_ ?_
      · intro k
        exact ((hφc k).comp
          (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
      · intro k
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        exact (hφ01 k _).2
      · exact Eventually.of_forall fun x => hφpt t ht x
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t =
        (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν) / t ^ (n + 1) /
          (1 + (μ (ball y t)).toReal / t ^ n) := ⟨_, fun _ => rfl⟩
    have hLlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) atTop
          (𝓝 (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν)) := by
      intro t ht htR
      have hcongr : (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν :=
        funext fun k => hLν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun x => R * ‖H x‖) ?_
        (hHν.norm.const_mul R) ?_ ?_
      · intro k
        have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ k (‖x - y‖ / t)) ν :=
          ((hφc k).comp
            (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
          continuous_inner.comp_aestronglyMeasurable
            ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
              hHν.aestronglyMeasurable)
        exact h1.mul h2
      · intro k
        rw [hν, ae_restrict_iff' measurableSet_closedBall]
        refine Eventually.of_forall fun x hx => ?_
        have hxR : ‖x - y‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
        calc φ k (‖x - y‖ / t) * ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ 1 * (R * ‖H x‖) :=
              mul_le_mul (hφ01 k _).2 hinner (norm_nonneg _) zero_le_one
          _ = R * ‖H x‖ := one_mul _
      · refine Eventually.of_forall fun x => ?_
        have h := (hφpt t ht x).mul_const (inner ℝ (x - y) (H x))
        by_cases hx : x ∈ ball y t
        · simpa [indicator_of_mem hx] using h
        · simpa [indicator_of_notMem hx] using h
    have halim : ∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
      intro t ht htR
      have hm0 : 0 ≤ (μ (ball y t)).toReal := ENNReal.toReal_nonneg
      have hden : 1 + (μ (ball y t)).toReal / t ^ n ≠ 0 := by
        have := div_nonneg hm0 (pow_pos ht n).le
        linarith
      have hcongr : (fun k => a k t) = fun k =>
          (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) /
            (1 + I k t / t ^ n) :=
        funext fun k => ha k t
      rw [hcongr, ha₀]
      exact ((hLlim t ht htR).div_const _).div
        (tendsto_const_nhds.add ((hIlim t ht htR).div_const _)) hden
    exact dohrLmonoOpenBallAux_limit n hR hβ1 hN0 hNR' hΛ hΛ1 a I a₀
      (fun t => (μ (ball y t)).toReal) (fun k => (hfix k).1) hab halim hIlim (fun k => (hfix k).2)
  have dohr_lmono_closedBall_of_ball : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), μ (closedBall y R) < ⊤ → ContinuousOn F (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone
    intro n ℓ μ y R F hfin hFc hmono
    have hlim : ∀ r ∈ Ioo 0 R, Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1)
        (𝓝[>] r) (𝓝 (F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1)) := by
      intro r hr
      have hfin' : μ (ball y ((r + R) / 2)) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hr.2]))))
      have hμ : Tendsto (fun s => μ (ball y s)) (𝓝[>] r) (𝓝 (μ (closedBall y r))) := by
        have h := tendsto_measure_biInter_gt (μ := μ) (s := fun s => ball y s) (a := r)
          (fun s _ => measurableSet_ball.nullMeasurableSet)
          (fun i j _ hij => ball_subset_ball hij)
          ⟨(r + R) / 2, by linarith [hr.2], hfin'⟩
        rw [biInter_gt_ball] at h
        exact h
      have hμr : Tendsto (fun s => (μ (ball y s)).toReal) (𝓝[>] r) (𝓝 (μ (closedBall y r)).toReal) :=
        (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hfin.ne
          (measure_mono (closedBall_subset_closedBall hr.2.le)))).comp hμ
      have hF : Tendsto F (𝓝[>] r) (𝓝 (F r)) :=
        ((hFc r hr).continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.mono_left nhdsWithin_le_nhds
      have hpow : Tendsto (fun s : ℝ => (s ^ n)⁻¹) (𝓝[>] r) (𝓝 ((r ^ n)⁻¹)) :=
        (((continuous_pow n).tendsto r).inv₀ (pow_ne_zero n hr.1.ne')).mono_left nhdsWithin_le_nhds
      exact (((hF.mul hpow).mul hμr).add hF).sub_const 1
    intro a ha b hb hab
    rcases hab.lt_or_eq with hab | rfl
    · have h1 : ∀ s ∈ Ioo b R, F a * (a ^ n)⁻¹ * (μ (closedBall y a)).toReal + F a - 1 ≤
          F s * (s ^ n)⁻¹ * (μ (ball y s)).toReal + F s - 1 := by
        intro s hs
        apply le_of_tendsto (hlim a ha)
        filter_upwards [Ioo_mem_nhdsGT (hab.trans hs.1)] with u hu
        exact hmono ⟨ha.1.trans hu.1, hu.2.trans hs.2⟩ ⟨hb.1.trans hs.1, hs.2⟩ hu.2.le
      apply ge_of_tendsto (hlim b hb)
      filter_upwards [Ioo_mem_nhdsGT hb.2] with s hs
      exact h1 s hs
    · exact le_rfl
  have dohr_lmono_density_of_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), 0 < R → μ (closedBall y R) < ⊤ → (∀ r ∈ Ioo 0 R, 0 ≤ F r) → Tendsto F (𝓝[>] 0) (𝓝 1) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) → ∃ t : ℝ, 0 ≤ t ∧ Tendsto (fun r : ℝ => μ (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone dohr_lmono_closedBall_of_ball
    intro n ℓ μ y R F hR hfin hF0 hF1 hmono
    set Φ := fun r : ℝ => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 with hΦ
    have hne : (Ioo (0:ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
    have hbdd : BddBelow (Φ '' Ioo 0 R) := by
      refine ⟨-1, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have h1 := hF0 r hr
      have h2 : 0 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
        mul_nonneg (mul_nonneg h1 (inv_nonneg.2 (pow_nonneg hr.1.le n))) ENNReal.toReal_nonneg
      simp only [hΦ]
      linarith
    set L := sInf (Φ '' Ioo 0 R) with hL
    have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := hmono.tendsto_nhdsWithin_Ioo_right hne hbdd
    set g := fun r : ℝ => (r ^ n)⁻¹ * (μ (closedBall y r)).toReal with hg_def
    have hg : Tendsto g (𝓝[>] 0) (𝓝 L) := by
      have h := ((hΦL.sub hF1).add_const 1).div hF1 one_ne_zero
      have heq : (fun r => (Φ r - F r + 1) / F r) =ᶠ[𝓝[>] 0] g := by
        filter_upwards [hF1.eventually (lt_mem_nhds (by norm_num : (1:ℝ) / 2 < 1))] with r hr
        have hFr : F r ≠ 0 := by linarith
        simp only [hΦ, hg_def]
        field_simp
        ring
      simpa using h.congr' heq
    have hL0 : 0 ≤ L := by
      apply ge_of_tendsto hg
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_nonneg (inv_nonneg.2 (pow_nonneg (le_of_lt hr) n)) ENNReal.toReal_nonneg
    have hω : 0 < unitBallVolume n := by
      unfold unitBallVolume
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    refine ⟨L / unitBallVolume n, div_nonneg hL0 hω.le, ?_, ?_⟩
    · have h := ENNReal.tendsto_ofReal (hg.div_const (unitBallVolume n))
      apply h.congr'
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      have hmr : μ (closedBall y r) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (closedBall_subset_closedBall hr.2.le))
      have hr0 : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr.1 n)
      rw [← ENNReal.ofReal_toReal hmr, ← ENNReal.ofReal_div_of_pos hr0]
      congr 1
      simp only [hg_def]
      field_simp
    · rw [mul_div_cancel₀ _ hω.ne']
      exact hΦL
  clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit
  intro n ℓ hn U hU V H p hp hH y R Λ hR hBR hrank hmeas hΛ hΛ1 hsmall
  -- `μ_V(B_R(y)) < ∞`: `B_R(y)` is a compact subset of `U` and `θ` is integrable on `M ∩ B_R(y)`.
  have hfin : V.weight (closedBall y R) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y R) hBR).setLIntegral_lt_top
  -- `H` is `μ_V`-integrable on the compact set `B_R(y) ⊆ U`.
  have hHint : IntegrableOn H (closedBall y R) V.weight :=
    hH.1.integrableOn_compact_subset hBR (isCompact_closedBall y R)
  obtain ⟨F, hFc, hFb, hF1, hmono⟩ :=
    dohr_lmono_open_ball_monotone n ℓ hn p hp V.weight H y R Λ hR hΛ hΛ1 hfin hHint hsmall
      (dohr_lmono_radial_inequality n ℓ U V H hH y R hBR hrank hmeas)
  have hmono' := dohr_lmono_closedBall_of_ball n ℓ V.weight y R F hfin hFc hmono
  obtain ⟨t, ht0, hdens, hlim⟩ := dohr_lmono_density_of_monotone n ℓ V.weight y R F hR hfin
    (fun r hr => (Real.exp_pos _).le.trans (hFb r hr).2.1) hF1 hmono'
  exact ⟨F, hFb, hF1, hmono', t, ht0, hdens, hlim⟩

theorem dohr_local_multiplicity_one : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∀ (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < R → closedBall ξ R ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → ∃ s > 0, s ≤ R ∧ (∀ᵐ x ∂V.weight, x ∈ ball ξ s → V.mult x = 1) ∧ (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ ball ξ s) (V.support ∩ ball ξ s)) = 0 ∧ V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) ∧ (∀ y ∈ ball ξ s ∩ V.support, V.HasDensity y 1) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0 := by
  intro n ℓ hn U hU V H p hp hH hLp hint ξ _hξU hξ R Q u hR hBR hu hgraph
  -- Unit density of the graph, hence finiteness and unit density of `spt V` in `B̆_R(ξ)`.
  obtain ⟨hfin, hdensS⟩ :=
    Submission.dohr_lmo_graph_support_density n ℓ V.support ξ R Q u hu hgraph
      (Submission.dohr_c1_graph_density_one n ℓ hn R u hu)
  -- On `B̆_R(ξ)` the tangent projections are measurable and project onto `n`-planes.
  obtain ⟨hmeasTP, hTP⟩ :=
    Submission.dohr_graph_tangent_planes n ℓ hn U hU V ξ R R Q u hR le_rfl hBR hu hgraph
  have hrank := Submission.dohr_lmo_graph_tangent_rank n ℓ U V ξ R Q u
    (ball_subset_closedBall.trans hBR) hu.differentiableOn_one hgraph hTP
  -- The monotonicity formula with a vanishing error, uniformly near `B̆_{R/2}(ξ)`.
  obtain ⟨t₁, ht₁, Λ, hΛ, hunif⟩ :=
    Submission.dohr_lmo_uniform_monotonicity_bound n ℓ U V H p ξ R hp hR hBR
      (Submission.dohr_local_monotonicity n ℓ hn U hU V H p hp hH) hrank hmeasTP
      (hLp _ (isCompact_closedBall ξ R) hBR)
  -- Since `Θ(ξ) = 1 < 2`, every density near `ξ` is `< 2`.
  obtain ⟨d, hd, hd2⟩ :=
    Submission.dohr_lmo_density_usc n ℓ U V ξ t₁ Λ ht₁ hΛ
      (hunif ξ (mem_ball_self (half_pos hR))) 1 zero_le_one hξ 2 one_lt_two
  -- The radius `s`.
  obtain ⟨s, hs, hsR2, hsd⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ R / 2 ∧ s ≤ d :=
    ⟨min (R / 2) d, lt_min (half_pos hR) hd, min_le_left _ _, min_le_right _ _⟩
  have hsR : s ≤ R := hsR2.trans (half_le_self hR.le)
  have hBs : closedBall ξ s ⊆ U := (closedBall_subset_closedBall hsR).trans hBR
  -- `Θ = θ` `μ_V`-a.e. on `B̆_s(ξ)`, and `Θ = 0` at `Hⁿ`-a.e. point of `spt V \ M` there.
  obtain ⟨hΘθ, hΘ0⟩ :=
    Submission.dohr_lmo_density_eq_mult_ae n ℓ U V ξ s hBs
      (hfin s (hsR2.trans_lt (half_lt_self hR)))
      (fun y hy => hdensS y ⟨hy.1, ball_subset_ball hsR hy.2⟩)
  -- Densities are unique.
  have huniq : ∀ (z : Amb n ℓ) (a b : ℝ), V.HasDensity z a → V.HasDensity z b →
      ENNReal.ofReal a = ENNReal.ofReal b := fun _ _ _ ha hb => tendsto_nhds_unique ha hb
  -- `Θ ≥ 1` at every point of `spt V ∩ B̆_s(ξ)`.
  have hge1 : ∀ y ∈ V.support ∩ ball ξ s, ∃ Θ : ℝ, 1 ≤ Θ ∧ V.HasDensity y Θ := by
    rintro y ⟨hyS, hys⟩
    have hyR2 : y ∈ ball ξ (R / 2) := ball_subset_ball hsR2 hys
    obtain ⟨Θy, hΘy0, hΘy, -⟩ := hunif y hyR2 t₁ ⟨ht₁, le_rfl⟩ y (mem_closedBall_self ht₁.le)
    refine ⟨Θy, not_lt.1 fun hlt => ?_, hΘy⟩
    obtain ⟨d', hd', hd'1⟩ :=
      Submission.dohr_lmo_density_usc n ℓ U V y t₁ Λ ht₁ hΛ (hunif y hyR2) Θy hΘy0 hΘy 1 hlt
    have hpos : V.weight (ball y d' ∩ ball ξ s) ≠ 0 := by
      have hyW : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hyS).2
      exact ((Measure.mem_support_iff_forall y).1 hyW _
        (Filter.inter_mem (ball_mem_nhds y hd') (isOpen_ball.mem_nhds hys))).ne'
    obtain ⟨z, ⟨hzd, hzs⟩, hzΘ, k, hk, hzk⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hΘθ.and hint))
    obtain ⟨Θ, hΘ1, hΘ⟩ := hd'1 z (ball_subset_closedBall hzd)
    have heq := huniq z _ _ (hzΘ hzs) hΘ
    rw [hzk] at heq
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (k : ℝ) :=
      ENNReal.one_le_ofReal.2 (by exact_mod_cast hk)
    rw [heq] at h1
    exact absurd (ENNReal.ofReal_lt_one.2 hΘ1) (not_lt.2 h1)
  -- Carrier and support agree up to an `Hⁿ`-null set on `B̆_s(ξ)`.
  have hsymm := Submission.dohr_lmo_carrier_support_null n ℓ U V (ball ξ s) measurableSet_ball
    (ball_subset_closedBall.trans hBs) hΘ0 hge1
  -- Multiplicity one, since `θ` is an integer `≥ 1` equal to a density `< 2`.
  have hmult1 : ∀ᵐ x ∂V.weight, x ∈ ball ξ s → V.mult x = 1 := by
    filter_upwards [hΘθ, hint] with x hxΘ hxk hxs
    obtain ⟨k, hk, hxk⟩ := hxk
    obtain ⟨Θ, hΘ2, hΘ⟩ := hd2 x (ball_subset_closedBall (ball_subset_ball hsd hxs))
    have heq := huniq x _ _ (hxΘ hxs) hΘ
    rw [hxk] at heq ⊢
    have hk2 : (k : ℝ) < 2 := by
      have h : ENNReal.ofReal (k : ℝ) < ENNReal.ofReal 2 := by
        rw [heq]; exact (ENNReal.ofReal_lt_ofReal_iff two_pos).2 hΘ2
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg k)).1 h
    have hk1 : k = 1 := by
      have : k < 2 := by exact_mod_cast hk2
      omega
    simp [hk1]
  -- `μ_V ⌞ B̆_s(ξ) = Hⁿ ⌞ (spt V ∩ B̆_s(ξ))`.
  have hweight :=
    Submission.dohr_lmo_weight_restrict_eq n ℓ U V (ball ξ s) measurableSet_ball hmult1 hsymm
  -- Density one at every point of `spt V ∩ B̆_s(ξ)`.
  have hdens1 : ∀ y ∈ ball ξ s ∩ V.support, V.HasDensity y 1 := by
    rintro y ⟨hys, hyS⟩
    have hlim := hdensS y ⟨hyS, ball_subset_ball hsR hys⟩
    have hδ : 0 < s - dist y ξ := sub_pos.2 (mem_ball.1 hys)
    unfold RectifiableVarifold.HasDensity
    rw [ENNReal.ofReal_one]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hsub : closedBall y r ⊆ ball ξ s := by
      intro z hz
      rw [mem_ball]
      calc dist z ξ ≤ dist z y + dist y ξ := dist_triangle _ _ _
        _ ≤ r + dist y ξ := by gcongr; exact mem_closedBall.1 hz
        _ < s := by linarith [hr.2]
    congr 1
    rw [← Measure.restrict_eq_self V.weight hsub, hweight,
      Measure.restrict_apply measurableSet_closedBall]
    congr 1
    ext z
    constructor
    · rintro ⟨hzS, hzr⟩
      exact ⟨hzr, hzS, hsub hzr⟩
    · rintro ⟨hzr, hzS, -⟩
      exact ⟨hzS, hzr⟩
  -- Transport of the null symmetric difference to graph coordinates.
  exact ⟨s, hs, hsR, hmult1, hsymm, hweight, hdens1,
    Submission.dohr_lmo_carrier_graph_symmDiff n ℓ V.carrier V.support ξ R s Q u hsR hgraph
      hsymm⟩

end Submission

end GMT.Ch05
