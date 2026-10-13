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

/-- The weight `μ_V = Hⁿ ⌞ θ` of a rectifiable `n`-varifold `V = v(M, θ)` in `U` (steps 2(i), 2(ii)
and 8 of the proof of Simon Ch. 5, Theorem 4.5, pp. 118–119): `μ_V(K) < ∞` for compact `K ⊆ U`,
`μ_V` vanishes off `spt V`, and `μ_V ≪ Hⁿ` (every `Hⁿ`-null set, measurable or not, is
`μ_V`-null). -/
theorem gte_weight_null_finite : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → V.weight K < ⊤) ∧ V.weight (V.support)ᶜ = 0 ∧ ∀ Z : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) Z = 0 → V.weight Z = 0 := by
  intro n ℓ U V
  -- `μ_V = (Hⁿ ⌞ M).withDensity (ofReal ∘ θ) ≪ Hⁿ ⌞ M ≪ Hⁿ`
  have hM : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
    withDensity_absolutelyContinuous _ _
  have hH : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)) :=
    hM.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  refine ⟨fun K hK hKU => ?_, ?_, fun Z hZ => hH hZ⟩
  -- (i): `μ_V(K) = ∫⁻_{M ∩ K} ofReal θ dHⁿ ≤ ∫⁻_{M ∩ K} ‖θ‖ₑ dHⁿ < ∞`, `θ` integrable on `M ∩ K`
  · rw [RectifiableVarifold.weight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (lintegral_mono fun x => Real.ofReal_le_enorm (V.mult x)).trans_lt
      (V.integrableOn_mult K hK hKU).hasFiniteIntegral
  -- (ii): `(spt V)ᶜ = Uᶜ ∪ (spt μ_V)ᶜ`; `μ_V` is conull on its support, and `Hⁿ ⌞ M` vanishes
  -- on `Uᶜ` because `M ⊆ U`
  · rw [RectifiableVarifold.support, compl_inter]
    refine measure_union_null (hM ?_) Measure.measure_compl_support
    rw [Measure.restrict_apply₀' V.nullMeasurableSet_carrier]
    exact measure_mono_null (fun x hx => hx.1 (V.carrier_subset hx.2)) measure_empty
/-- Tangent projections and the integrands of the graph tangential estimate (steps 1(iii) and 3 of
its proof, for Simon Ch. 5, Theorem 4.5, displays (8)–(12)): `p_x = V.tangentProj x` satisfies
`‖p_x v‖ ≤ ‖v‖`, and if `x ↦ p_x` is `μ_V`-a.e. strongly measurable, then on each `S` with
`μ_V(S) < ∞` the functions `x ↦ ⟨p_x e, p_x g(x)⟩` (`g` a.e. strongly measurable, `‖g‖ ≤ C`) and
`x ↦ |p_x − p_T|²` are `μ_V`-integrable.  `p_x` is an orthogonal projection or `0`; each integrand
is a continuous function of `(p_x, g(x))`, resp. of `p_x`, bounded by `‖e‖ C`, resp. `4 (n + ℓ)`. -/
theorem gte_tangentProj_integrands : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ x v : Amb n ℓ, ‖V.tangentProj x v‖ ≤ ‖v‖) ∧ (AEStronglyMeasurable V.tangentProj V.weight → ∀ S : Set (Amb n ℓ), V.weight S < ⊤ → (∀ (e : Amb n ℓ) (g : Amb n ℓ → Amb n ℓ) (C : ℝ), AEStronglyMeasurable g V.weight → (∀ x, ‖g x‖ ≤ C) → IntegrableOn (fun x => inner ℝ (V.tangentProj x e) (V.tangentProj x (g x))) S V.weight) ∧ ∀ T : Submodule ℝ (Amb n ℓ), IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) S V.weight) := by
  intro n ℓ U V
  -- Step 1, (a): `p_x` is `K.starProjection` (operator norm `≤ 1`) or `0`.
  have ha : ∀ x v : Amb n ℓ, ‖V.tangentProj x v‖ ≤ ‖v‖ := by
    intro x v
    unfold RectifiableVarifold.tangentProj
    split_ifs with h
    · calc ‖(Classical.choose h).starProjection v‖
          ≤ ‖(Classical.choose h).starProjection‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖v‖ := by gcongr; exact Submodule.starProjection_norm_le _
        _ = ‖v‖ := one_mul _
    · simp
  -- Step 2: `x ↦ p_x` is a.e. strongly measurable and `μ_V(S) < ∞`.
  refine ⟨ha, fun hmeas S hS => ⟨?_, ?_⟩⟩
  · intro e g C hg hC
    -- Step 3: `(L, w) ↦ ⟨L e, L w⟩` is continuous, so the integrand is a.e. strongly measurable.
    have hcont : Continuous (fun (L : Amb n ℓ →L[ℝ] Amb n ℓ) (w : Amb n ℓ) =>
        inner ℝ (L e) (L w)).uncurry :=
      (continuous_fst.clm_apply continuous_const).inner (continuous_fst.clm_apply continuous_snd)
    -- Steps 4–5: the integrand is bounded by `‖e‖ C` (Cauchy–Schwarz and (a)).
    refine Measure.integrableOn_of_bounded (M := ‖e‖ * C) hS.ne
      (hcont.comp_aestronglyMeasurable₂ hmeas hg) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |inner ℝ (V.tangentProj x e) (V.tangentProj x (g x))|
        ≤ ‖V.tangentProj x e‖ * ‖V.tangentProj x (g x)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖e‖ * C :=
        mul_le_mul (ha x e) ((ha x (g x)).trans (hC x)) (norm_nonneg _) (norm_nonneg _)
  · intro T
    -- Step 6: `A ↦ hsNormSq A = Σᵢ ‖A eᵢ‖²` is continuous, so the integrand is a.e. strongly
    -- measurable.
    have hcont : Continuous (fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq A) := by
      unfold hsNormSq
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).norm).pow 2
    -- Steps 7–8: `0 ≤ hsNormSq (p_x − P_T) ≤ 4 (n + ℓ)`, since `‖(p_x − P_T) eᵢ‖ ≤ 2`.
    refine Measure.integrableOn_of_bounded (M := 4 * (n + ℓ)) hS.ne
      (hcont.comp_aestronglyMeasurable (hmeas.sub aestronglyMeasurable_const))
      (Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ hsNormSq (V.tangentProj x - T.starProjection) := by
      unfold hsNormSq; positivity
    rw [Real.norm_of_nonneg hnn]
    unfold hsNormSq
    have hterm : ∀ i : Fin (n + ℓ),
        ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2 ≤ 4 := by
      intro i
      have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Amb n ℓ)‖ = 1 := by simp
      have hp : ‖V.tangentProj x (EuclideanSpace.single i 1)‖ ≤ 1 := (ha x _).trans h1.le
      have hq : ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ≤ 1 :=
        calc ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖
            ≤ ‖T.starProjection‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Amb n ℓ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * 1 := by rw [h1]; gcongr; exact Submodule.starProjection_norm_le _
          _ = 1 := one_mul _
      have hd : ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ≤ 2 := by
        rw [sub_apply]
        calc _ ≤ ‖V.tangentProj x (EuclideanSpace.single i 1)‖
              + ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add hp hq
          _ = 2 := by norm_num
      have h0 := norm_nonneg ((V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1))
      nlinarith
    calc ∑ i : Fin (n + ℓ), ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2
        ≤ ∑ _i : Fin (n + ℓ), (4 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
      _ = 4 * (n + ℓ) := by simp [Finset.sum_const, Finset.card_univ]; ring
/-- Graph coordinates for the graph tangential estimate (steps 1(i), 1(ii) and 2(iii) of its proof,
for Simon Ch. 5, Theorem 4.5, displays (8)–(12)).  With `E = EuclideanSpace.finAddEquivProd` and
`a(z) = (E (q⁻¹ z)).1`: (i) `(x, y) ↦ graphPoint x y` is continuous; (ii) `a` is continuous;
(iii) `a(q(x, y)) = x`; (iv) if `f` is continuous on `B_R(0)` and `r ≤ R`, then
`q(graph f|B_R(0))` is compact and `q(graph f|B̆_r(0))` is Borel.  Comparing coordinates
(`Fin.addCases`), `graphPoint x y = E⁻¹(x, y)`, which gives (i)–(iii).  `q(graph f|B_R(0))` is the
image of the compact ball under `F x = q(x, f x)`, continuous on it; by (iii) and `r ≤ R`,
`q(graph f|B̆_r(0)) = q(graph f|B_R(0)) ∩ a⁻¹(B̆_r(0))`, the intersection of a closed and an open
set. -/
theorem gte_graph_image_geometry : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) ∧ Continuous (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) ∧ (∀ (x : Rn n) (y : Rn ℓ), (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x y)))).1 = x) ∧ ∀ (f : Rn n → Rn ℓ) (R r : ℝ), ContinuousOn f (closedBall 0 R) → r ≤ R → IsCompact (q '' graphOver f (closedBall 0 R)) ∧ MeasurableSet (q '' graphOver f (ball 0 r)) := by
  intro n ℓ q
  -- Step 1: `graphPoint x y = E⁻¹(x, y)`, comparing coordinates.
  have hgp : ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y =
      (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y) := by
    intro x y
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [graphPoint]
    · simp [graphPoint]
  -- Step 2, (i): `(x, y) ↦ graphPoint x y` is the continuous map `E⁻¹`.
  have hi : Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) := by
    have : (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) =
        (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm := by
      funext p
      exact hgp p.1 p.2
    rw [this]
    exact ContinuousLinearEquiv.continuous _
  -- Step 3, (ii): `a = Prod.fst ∘ E ∘ q⁻¹`.
  have hii : Continuous (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) :=
    continuous_fst.comp ((ContinuousLinearEquiv.continuous _).comp q.symm.continuous)
  -- Step 4, (iii): `a(q(x, y)) = (E (E⁻¹(x, y))).1 = x`.
  have hiii : ∀ (x : Rn n) (y : Rn ℓ),
      (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x y)))).1 = x := by
    intro x y
    rw [LinearIsometryEquiv.symm_apply_apply, hgp, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨hi, hii, hiii, ?_⟩
  intro f R r hf hrR
  -- Step 5, (iv) compactness: `q '' graphOver f D = F '' D`, and `F` is continuous on the compact
  -- ball `B_R(0)`.
  have himg : ∀ D : Set (Rn n), q '' graphOver f D = (fun x => q (graphPoint x (f x))) '' D := by
    intro D
    unfold graphOver
    rw [Set.image_image]
  have hFcont : ContinuousOn (fun x => q (graphPoint x (f x))) (closedBall 0 R) :=
    q.continuous.comp_continuousOn (hi.comp_continuousOn (continuousOn_id.prodMk hf))
  have hcpt : IsCompact (q '' graphOver f (closedBall 0 R)) := by
    rw [himg]
    exact (isCompact_closedBall 0 R).image_of_continuousOn hFcont
  refine ⟨hcpt, ?_⟩
  -- Step 6, (iv) Borel: `F(B̆_r(0)) = F(B_R(0)) ∩ a⁻¹(B̆_r(0))` by (iii) and `r ≤ R`.
  have heq : q '' graphOver f (ball 0 r) =
      q '' graphOver f (closedBall 0 R) ∩
        (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) ⁻¹' ball 0 r := by
    rw [himg, himg]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)) hx, rfl⟩, ?_⟩
      show (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x (f x))))).1 ∈ ball 0 r
      rw [hiii]
      exact hx
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      refine ⟨x, ?_, rfl⟩
      have hz' : (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x (f x))))).1 ∈ ball 0 r :=
        hz
      rwa [hiii] at hz'
  rw [heq]
  exact hcpt.isClosed.measurableSet.inter (isOpen_ball.preimage hii).measurableSet
/-- A map `f : ℝⁿ → ℝ^ℓ` that is `K`-Lipschitz on the closed ball `B_R(0)` (graph estimates in the
proof of Simon Ch. 5, Theorem 4.5, displays (8)–(12), pp. 118–119): the set of points of the open
ball `B̆_R(0)` where `f` is not differentiable is Borel and `Lⁿ`-null (Rademacher's theorem),
`‖Df(x)‖ ≤ K` on `B̆_R(0)`, and where `f` is differentiable the gradient of the coordinate
`fʲ = (y ↦ f(y)ⱼ)` represents the `j`-th row of `Df(x)`: `⟨∇fʲ(x), v⟩ = (Df(x) v)ⱼ`. -/
theorem gte_lipschitz_ball_calculus : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → MeasurableSet (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) ∧ volume (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) = 0 ∧ ∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ f x‖ ≤ K ∧ (DifferentiableAt ℝ f x → ∀ (j : Fin ℓ) (v : Rn n), inner ℝ (gradient (fun y => f y j) x) v = fderiv ℝ f x v j) := by
  intro n ℓ f K R hf
  -- (i): the differentiability set of any map into a complete space is Borel
  refine ⟨measurableSet_ball.inter (measurableSet_of_differentiableAt ℝ f).compl, ?_, ?_⟩
  -- (ii): Rademacher on the open ball, where differentiability within it is differentiability
  · have hae := (hf.mono ball_subset_closedBall).ae_differentiableWithinAt_of_mem
      (μ := (volume : Measure (Rn n)))
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxZ
    exact hxZ.2 ((hx hxZ.1).differentiableAt (isOpen_ball.mem_nhds hxZ.1))
  · intro x hx
    -- (iii): `B_R(0)` is a neighbourhood of `x` on which `f` is `K`-Lipschitz
    refine ⟨norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hf, ?_⟩
    -- gradient rows: `fʲ = proj_j ∘ f`, the chain rule, and `⟪(toDual)⁻¹ L, v⟫ = L v`
    intro hfx j v
    have hd : HasFDerivAt (fun y => f y j)
        ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
      (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hfx.hasFDerivAt
    rw [inner_gradient_left, hd.fderiv]
    rfl
/-- **Simon Ch. 5, proof of Theorem 4.5, displays (8)–(12) (pp. 118–119)**, localization step in an
abstract measure space.  If `Φ` is integrable on `B`, `|Φ| ≤ M` everywhere, `Φ` vanishes on
`(B \ G') ∩ G`, `μ((B \ G') \ G) ≤ m < ∞`, and `|Φ − φ| ≤ M ψ` a.e. on `G' ⊆ B ∩ B'` with `ψ ≥ 0`
integrable on `B'`, then `|∫_{G'} φ| ≤ |∫_B Φ| + M m + M ∫_{B'} ψ`.
Proof: splitting `∫_B Φ` along `G'` and then along `G` gives `∫_{G'} Φ = ∫_B Φ − ∫_{(B \ G') \ G} Φ`,
and the last integral is at most `M μ((B \ G') \ G) ≤ M m` in absolute value.  On `G'`, `Φ − φ` is
dominated by `M ψ`, so `φ` is integrable there and `|∫_{G'} Φ − ∫_{G'} φ| ≤ M ∫_{G'} ψ ≤ M ∫_{B'} ψ`;
conclude by the triangle inequality. -/
theorem gte_localized_comparison : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (B B' G G' : Set X) (Φ φ ψ : X → ℝ) (M : ℝ) (m : ℝ≥0∞), 0 ≤ M → MeasurableSet G → MeasurableSet G' → G' ⊆ B → G' ⊆ B' → IntegrableOn Φ B μ → (∀ x, |Φ x| ≤ M) → (∀ x ∈ (B \ G') ∩ G, Φ x = 0) → μ ((B \ G') \ G) ≤ m → m < ⊤ → AEStronglyMeasurable φ (μ.restrict G') → IntegrableOn ψ B' μ → (∀ x, 0 ≤ ψ x) → (∀ᵐ x ∂μ, x ∈ G' → |Φ x - φ x| ≤ M * ψ x) → |∫ x in G', φ x ∂μ| ≤ |∫ x in B, Φ x ∂μ| + M * m.toReal + M * ∫ x in B', ψ x ∂μ := by
  intro X _ μ B B' G G' Φ φ ψ M m hM hG hG' hG'B hG'B' hΦ hΦM hΦ0 hμm hm hφ hψ hψ0 hcmp
  -- Steps 1–3: split `∫_B Φ` along `G'` (`B ∩ G' = G'`) and then `∫_{B \ G'} Φ` along `G`; the
  -- `(B \ G') ∩ G` part vanishes, so `∫_{G'} Φ = ∫_B Φ − ∫_{(B \ G') \ G} Φ`.
  have h1 : ∫ x in B ∩ G', Φ x ∂μ + ∫ x in B \ G', Φ x ∂μ = ∫ x in B, Φ x ∂μ :=
    integral_inter_add_sdiff hG' hΦ
  rw [inter_eq_right.mpr hG'B] at h1
  have h2 : ∫ x in (B \ G') ∩ G, Φ x ∂μ + ∫ x in (B \ G') \ G, Φ x ∂μ =
      ∫ x in B \ G', Φ x ∂μ :=
    integral_inter_add_sdiff hG (hΦ.mono_set sdiff_subset)
  rw [setIntegral_eq_zero_of_forall_eq_zero hΦ0, zero_add] at h2
  -- Step 4: the off part is at most `M μ((B \ G') \ G) ≤ M m` in absolute value.
  have h4 : |∫ x in (B \ G') \ G, Φ x ∂μ| ≤ M * m.toReal := by
    have h := norm_setIntegral_le_of_norm_le_const (hμm.trans_lt hm)
      (fun x _ => (Real.norm_eq_abs (Φ x)).le.trans (hΦM x))
    rw [Real.norm_eq_abs, measureReal_def] at h
    exact h.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hm.ne hμm) hM)
  -- Step 5: `Φ − φ` is dominated by `M ψ` on `G'`, so `φ = Φ − (Φ − φ)` is integrable on `G'`.
  have hΦG' : Integrable Φ (μ.restrict G') := (hΦ.mono_set hG'B).integrable
  have hψG' : Integrable (fun x => M * ψ x) (μ.restrict G') :=
    (hψ.mono_set hG'B').integrable.const_mul M
  have hae : ∀ᵐ x ∂μ.restrict G', ‖Φ x - φ x‖ ≤ M * ψ x := by
    rw [ae_restrict_iff' hG']
    filter_upwards [hcmp] with x hx hxG'
    rw [Real.norm_eq_abs]
    exact hx hxG'
  have hdiff : Integrable (fun x => Φ x - φ x) (μ.restrict G') :=
    hψG'.mono' (hΦG'.aestronglyMeasurable.sub hφ) hae
  have hφG' : Integrable φ (μ.restrict G') :=
    (hΦG'.sub hdiff).congr (Eventually.of_forall fun x => sub_sub_cancel (Φ x) (φ x))
  -- Step 6: `|∫_{G'} Φ − ∫_{G'} φ| = |∫_{G'} (Φ − φ)| ≤ M ∫_{G'} ψ ≤ M ∫_{B'} ψ`.
  have h6 : |∫ x in G', Φ x ∂μ - ∫ x in G', φ x ∂μ| ≤ M * ∫ x in B', ψ x ∂μ := by
    rw [← integral_sub hΦG' hφG', ← Real.norm_eq_abs]
    calc ‖∫ x in G', (Φ x - φ x) ∂μ‖ ≤ ∫ x in G', M * ψ x ∂μ :=
          norm_integral_le_of_norm_le hψG' hae
      _ = M * ∫ x in G', ψ x ∂μ := integral_const_mul M _
      _ ≤ M * ∫ x in B', ψ x ∂μ :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hψ (Eventually.of_forall hψ0)
            (Eventually.of_forall hG'B')) hM
  -- Step 7: the triangle inequality.
  have hI := le_abs_self (∫ x in B, Φ x ∂μ)
  have hI' := neg_abs_le (∫ x in B, Φ x ∂μ)
  obtain ⟨h4l, h4r⟩ := abs_le.mp h4
  obtain ⟨h6l, h6r⟩ := abs_le.mp h6
  exact abs_le.mpr ⟨by linarith, by linarith⟩
/-- The linear algebra in the proof of Simon Ch. 5, Lemma 2.1 (p. 107): (i) the operator norm of a
linear map is at most its Hilbert–Schmidt norm `|A|`; (ii) `|p_{T⊥} v| = dist(v, T)`; and
(iii) display (2) of the proof, `trace(p_{T⊥} ∘ p_P) = ½ |p_P − p_T|²` when `dim P = dim T`. -/
theorem hsNorm_starProjection_trace_identities : (∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A) ∧ (∀ (m : ℕ) (T : Submodule ℝ (Rn m)) (v : Rn m), ‖Tᗮ.starProjection v‖ = Metric.infDist v (T : Set (Rn m))) ∧ ∀ (m : ℕ) (P T : Submodule ℝ (Rn m)), Module.finrank ℝ P = Module.finrank ℝ T → LinearMap.trace ℝ (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
    intro m k A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  · -- (ii) `p_{T⊥} v = v − p_T v`, and `p_T v` is the point of `T` nearest to `v`.
    intro m T v
    rw [Submodule.starProjection_orthogonal_val, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist]
  · -- (iii) Compute both sides in the standard orthonormal basis `eᵢ`.
    intro m P T hPT
    -- The trace is the sum of the diagonal entries `⟪eᵢ, f eᵢ⟫`.
    have htr : ∀ f : Rn m →ₗ[ℝ] Rn m, LinearMap.trace ℝ (Rn m) f =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (f (EuclideanSpace.single i 1)) := by
      intro f
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f,
        Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
    -- The trace of an orthogonal projection is the dimension of its range.
    have hproj : ∀ W : Submodule ℝ (Rn m),
        LinearMap.trace ℝ (Rn m) W.starProjection.toLinearMap = Module.finrank ℝ W := fun W =>
      LinearMap.IsProj.trace
        ⟨W.starProjection_apply_mem, fun _ hx => W.starProjection_eq_self_iff.2 hx⟩
    -- `‖p_W x‖² = ⟪x, p_W x⟫`, since `p_W` is self-adjoint and idempotent.
    have hsq : ∀ (W : Submodule ℝ (Rn m)) (x : Rn m),
        ‖W.starProjection x‖ ^ 2 = inner ℝ x (W.starProjection x) := by
      intro W x
      rw [← real_inner_self_eq_norm_sq, W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.2 (W.starProjection_apply_mem x)]
    -- Pointwise, `2 ⟪x, (I − q) p x⟫ = ‖(p − q) x‖² + ⟪x, p x⟫ − ⟪x, q x⟫`.
    have hterm : ∀ x : Rn m, 2 * inner ℝ x (Tᗮ.starProjection (P.starProjection x)) =
        ‖(P.starProjection - T.starProjection) x‖ ^ 2 + inner ℝ x (P.starProjection x) -
          inner ℝ x (T.starProjection x) := by
      intro x
      rw [Submodule.starProjection_orthogonal_val, sub_apply, norm_sub_sq_real, hsq P, hsq T,
        inner_sub_right, ← T.inner_starProjection_left_eq_right,
        real_inner_comm (T.starProjection x)]
      ring
    -- `trace p_P = dim P = dim T = trace p_T`.
    have hdim : ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (P.starProjection (EuclideanSpace.single i 1)) =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (T.starProjection (EuclideanSpace.single i 1)) := by
      have h := hproj P
      rw [hPT, ← hproj T, htr, htr] at h
      exact h
    rw [htr, hsNormSq, eq_div_iff two_ne_zero, mul_comm, Finset.mul_sum]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [Finset.sum_congr rfl fun i _ => hterm (EuclideanSpace.single i 1), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hdim, add_sub_cancel_right]
/-- Graph coordinates on `ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ`, used for the graph estimates behind Simon Ch. 5,
Remark 5.3 (p. 122): the point `(a, b) = graphPoint a b` has coordinate `a_i` at `castAdd ℓ i` and
`b_j` at `natAdd n j`; `(a, b)` is linear in the pair; `|(a, b)|² = |a|² + |b|²`; and
`⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`.
Every index of `Fin (n + ℓ)` is `castAdd ℓ i` or `natAdd n j` (`Fin.addCases`), so the linearity
identities hold coordinatewise, and the norm and the inner product split as sums over the two
blocks of indices (`Fin.sum_univ_add`). -/
theorem any_radius_gr_la_graphPoint_algebra : ∀ (n ℓ : ℕ), (∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i) ∧ (∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b') ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b') ∧ (∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b') := by
  intro n ℓ
  -- (C1), (C2): the coordinates of `graphPoint a b = toLp (Fin.append a b)`
  have hC1 : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_left]
  have hC2 : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_right]
  refine ⟨hC1, hC2, ?_, ?_, ?_, ?_, ?_⟩
  -- (L1)–(L3): compare the coordinates at every `castAdd ℓ i` and every `natAdd n j`
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.add_apply, hC1]
    · simp only [PiLp.add_apply, hC2]
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hC1]
    · simp only [PiLp.sub_apply, hC2]
  · intro t a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.smul_apply, hC1]
    · simp only [PiLp.smul_apply, hC2]
  -- (L4): split `‖x‖² = Σ_k ‖x_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hC1, hC2]
  -- (IP): split `⟪x, y⟫ = Σ_k ⟪x_k, y_k⟫` in the same way
  · intro a a' b b'
    rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
    simp only [hC1, hC2]
/-- The rotated plane `T₀ = q(ℝⁿ × {0})` of Simon Ch. 5, Lemma 2.6 (p. 110), in the graph estimates
behind Remark 5.3 (p. 122): for a linear isometry `q` of `ℝ^{n+ℓ}`, (L5) `p_{T₀}(q(a, b)) = q(a, 0)`,
(L6) `dist(q(a, b), T₀) = |b|` and (L7) `dim T₀ = n`.
Since `e_{castAdd ℓ i} = (eᵢ, 0)` and `c ↦ (c, 0)` is linear, `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, which
is orthogonal to `(0, b)`; as `q` preserves inner products, `q(a, 0) ∈ T₀` and
`q(a, b) − q(a, 0) = q(0, b) ⊥ T₀` characterize the projection, and the distance to `T₀` is attained
at the projection.  The `e_{castAdd ℓ i}` are independent and `q` preserves dimension. -/
theorem any_radius_gr_la_rotatedPlane_facts : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ))) ∧ (∀ (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖) ∧ Module.finrank ℝ (rotatedPlane q) = n := by
  intro n ℓ q
  -- (C1), (C2), (L1)–(L4) and (IP) for `graphPoint`
  obtain ⟨hC1, hC2, hadd, hsub, hsmul, hnorm, hinner⟩ :=
    Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  -- Step 1: `e_{castAdd ℓ i} = (eᵢ, 0)`; compare the coordinates at `castAdd ℓ i'` and `natAdd n j`
  have hbasis : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) =
      graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
    · rw [hC1]
      simp only [PiLp.single_apply, (Fin.castAdd_injective n ℓ).eq_iff]
    · rw [hC2]
      have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ i := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
  -- Step 2: `G c = (c, 0)` is linear, by (L1) and (L3)
  let G : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun c => graphPoint c (0 : Rn ℓ)
      map_add' := fun c c' => by simpa using hadd c c' (0 : Rn ℓ) (0 : Rn ℓ)
      map_smul' := fun t c => by simpa using hsmul t c (0 : Rn ℓ) }
  -- Step 3: `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, the image under `G` of the span of the `eᵢ`
  have hhor : horizontalPlane n ℓ = LinearMap.range G := by
    have hfun : (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) =
        G ∘ fun i : Fin n => EuclideanSpace.single i (1 : ℝ) := by
      funext i
      exact hbasis i
    have hspan :
        Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
      have hb : ⇑(EuclideanSpace.basisFun (Fin n) ℝ) = fun i => EuclideanSpace.single i (1 : ℝ) :=
        funext (EuclideanSpace.basisFun_apply (Fin n) ℝ)
      have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
      rwa [OrthonormalBasis.coe_toBasis, hb] at this
    rw [horizontalPlane, hfun, Set.range_comp, Submodule.span_image, hspan,
      LinearMap.range_eq_map]
  -- Step 4: `(0, b)` is orthogonal to `ℝⁿ × {0}`, by (IP)
  have horth : ∀ (b : Rn ℓ), ∀ h ∈ horizontalPlane n ℓ,
      inner ℝ (graphPoint (0 : Rn n) b) h = 0 := by
    intro b h hh
    rw [hhor] at hh
    obtain ⟨c, rfl⟩ := hh
    show inner ℝ (graphPoint 0 b) (graphPoint c 0) = 0
    rw [hinner]
    simp
  -- Step 6(ii): `q(a, b) − q(a, 0) = q(0, b)`, by (L2)
  have hdiff : ∀ (a : Rn n) (b : Rn ℓ),
      q (graphPoint a b) - q (graphPoint a 0) = q (graphPoint 0 b) := by
    intro a b
    rw [← map_sub, ← hsub]
    simp
  -- Step 6, (L5): `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) ⊥ T₀`, as `q` preserves inner products
  have hproj : ∀ (a : Rn n) (b : Rn ℓ),
      (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ)) := by
    intro a b
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (by rw [hhor]; exact ⟨a, rfl⟩)
    · intro w hw
      obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
      rw [hdiff]
      simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
      rw [LinearIsometryEquiv.inner_map_map]
      exact horth b h hh
  refine ⟨hproj, ?_, ?_⟩
  -- Step 8, (L6): `dist(v, T₀) = |v − p_{T₀} v| = |q(0, b)| = |(0, b)| = |b|`, by (L5) and (L4)
  · intro a b
    rw [← Submodule.dist_starProjection_eq_infDist, hproj, dist_eq_norm, hdiff,
      LinearIsometryEquiv.norm_map]
    have h := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- Step 9, (L7): the `e_{castAdd ℓ i}` are independent, and `q` preserves `finrank`
  · have hli : LinearIndependent ℝ
        (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) :=
      (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + ℓ))).linearIndependent.comp _
        (Fin.castAdd_injective n ℓ)
    rw [rotatedPlane, LinearEquiv.finrank_map_eq, horizontalPlane, finrank_span_eq_card hli,
      Fintype.card_fin]
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

/-- The rotated graph plane `q{(v, Av) : v ∈ ℝⁿ}` of a linear map `A : ℝⁿ → ℝ^ℓ` is
`n`-dimensional.  With `E = EuclideanSpace.finAddEquivProd`, `graphPoint v (A v) = E.symm (v, A v)`
(`rsod_graphPoint_eq_finAddEquivProd_symm`), so the generators are the values of the linear map
`Φ = q ∘ E.symm ∘ (id, A)` and their span is `range Φ` (`Submodule.span_eq`).  `Φ` is injective,
since `q` and `E.symm` are and `(v, A v)` determines `v`; hence
`finrank (range Φ) = finrank ℝⁿ = n` (`LinearMap.finrank_range_of_inj`). -/
theorem tdo_gpd_graph_plane_finrank : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ),
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))) = n := by
  intro n ℓ q A
  let E : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  let Φ : Rn n →ₗ[ℝ] Amb n ℓ := q.toLinearEquiv.toLinearMap ∘ₗ
    E.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id.prod A.toLinearMap
  have hΦ : ∀ v, Φ v = q (graphPoint v (A v)) := fun v => by
    rw [rsod_graphPoint_eq_finAddEquivProd_symm]
    rfl
  have hinj : Function.Injective Φ := fun v w hvw => by
    rw [hΦ, hΦ, rsod_graphPoint_eq_finAddEquivProd_symm,
      rsod_graphPoint_eq_finAddEquivProd_symm] at hvw
    exact (Prod.mk.inj (E.symm.injective (q.injective hvw))).1
  have hrange : (Set.range fun v : Rn n => q (graphPoint v (A v))) =
      (LinearMap.range Φ : Set (Amb n ℓ)) := by
    rw [LinearMap.coe_range]
    exact congrArg Set.range (funext fun v => (hΦ v).symm)
  rw [hrange, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]

/-- A step in the proof of Simon Ch. 5, Theorem 4.5 (displays (10)–(11)): for `u, w ∈ T`,
`|⟪p_S u, p_S w⟫ − ⟪u, w⟫| ≤ |p_S − p_T|² |u| |w|`, with `|p_S − p_T|` the Hilbert–Schmidt norm. -/
theorem gwe_gta_proj_inner_defect : ∀ (m : ℕ) (S T : Submodule ℝ (Rn m)) (u w : Rn m), u ∈ T → w ∈ T → |inner ℝ (S.starProjection u) (S.starProjection w) - inner ℝ u w| ≤ hsNormSq (S.starProjection - T.starProjection) * (‖u‖ * ‖w‖) := by
  intro m S T u w hu hw
  -- `p_T` fixes `u, w ∈ T`, so `(p_S − p_T) x = p_S x − x` for `x = u, w`.
  have hfix : ∀ x ∈ T, (S.starProjection - T.starProjection) x = S.starProjection x - x :=
    fun x hx => by rw [sub_apply, T.starProjection_eq_self_iff.2 hx]
  -- `p_S` is self-adjoint and idempotent, so `⟪p_S u, p_S w⟫ = ⟪u, p_S w⟫ = ⟪p_S u, w⟫`; hence
  -- `⟪p_S u, p_S w⟫ − ⟪u, w⟫ = −⟪(p_S − p_T) u, (p_S − p_T) w⟫`.
  have hid : inner ℝ (S.starProjection u) (S.starProjection w) - inner ℝ u w =
      -inner ℝ ((S.starProjection - T.starProjection) u)
        ((S.starProjection - T.starProjection) w) := by
    have h1 := S.inner_starProjection_left_eq_right u (S.starProjection w)
    have h2 := S.inner_starProjection_left_eq_right u w
    rw [S.starProjection_eq_self_iff.2 (S.starProjection_apply_mem w)] at h1
    rw [hfix u hu, hfix w hw, inner_sub_left, inner_sub_right, inner_sub_right]
    linarith
  -- `|⟪A x, A y⟫| ≤ ‖A x‖ ‖A y‖ ≤ ‖A‖² ‖x‖ ‖y‖ ≤ |A|² ‖x‖ ‖y‖`, since `‖A‖ ≤ |A|`.
  have key : ∀ (A : Rn m →L[ℝ] Rn m) (x y : Rn m),
      |inner ℝ (A x) (A y)| ≤ hsNormSq A * (‖x‖ * ‖y‖) := by
    intro A x y
    have hA : ‖A‖ ^ 2 ≤ hsNormSq A :=
      (Real.le_sqrt (norm_nonneg A) (Finset.sum_nonneg fun i _ => sq_nonneg _)).1
        (hsNorm_starProjection_trace_identities.1 m m A)
    calc |inner ℝ (A x) (A y)| ≤ ‖A x‖ * ‖A y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * (‖A‖ * ‖y‖) :=
          mul_le_mul (A.le_opNorm x) (A.le_opNorm y) (norm_nonneg _) (by positivity)
      _ = ‖A‖ ^ 2 * (‖x‖ * ‖y‖) := by ring
      _ ≤ hsNormSq A * (‖x‖ * ‖y‖) := by gcongr
  rw [hid, abs_neg]
  exact key _ u w
/-- Display 4.2 of Simon Ch. 5 (p. 115) for a rotated plane, as used in (9)–(13) of the proof of
Theorem 4.5: if `S ⊆ ℝ^{n+ℓ}` is an `n`-dimensional subspace and `T = q(ℝⁿ × {0})`, then
`Σ_j |p_S e'_j|² = ½ |p_S − p_T|²`, where `e'_j = q(0, d_j)` are the images under `q` of the last
`ℓ` standard basis vectors.
In the orthonormal basis `q(ε_k)`, `trace(p_{T⊥} ∘ p_S) = Σ_k ⟨p_{T⊥} q(ε_k), p_S q(ε_k)⟩`.  The
horizontal vectors `q(eᵢ, 0)` lie in `T` and contribute `0`, while `p_{T⊥} e'_j = e'_j` and
`⟨e'_j, p_S e'_j⟩ = |p_S e'_j|²`; finally `trace(p_{T⊥} ∘ p_S) = ½ |p_S − p_T|²` since
`dim S = n = dim T`. -/
theorem gwe_gta_vertical_trace_sum : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (S : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ S = n → ∑ j : Fin ℓ, ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 = hsNormSq (S.starProjection - (rotatedPlane q).starProjection) / 2 := by
  intro n ℓ q S hS
  -- (C1), (C2) and (L3) for `graphPoint`; (L5) and (L7) for `T = q(ℝⁿ × {0})`
  obtain ⟨hC1, hC2, -, -, hsmul, -, -⟩ := Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  obtain ⟨hproj, -, hdimT⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- Step 2: `ε_{castAdd ℓ i} = (eᵢ, 0)` and `ε_{natAdd n j} = (0, d_j)`, coordinatewise
  have hcast : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) =
      graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [hC1, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.castAdd_inj]
    · rw [hC2, PiLp.single_apply]
      have hne : Fin.natAdd n j' ≠ Fin.castAdd ℓ i := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
  have hnat : ∀ j : Fin ℓ, EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) =
      graphPoint (0 : Rn n) (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [hC1, PiLp.single_apply]
      have hne : Fin.castAdd ℓ i' ≠ Fin.natAdd n j := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
    · rw [hC2, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.natAdd_inj]
  -- Step 3: `(0, 0) = 0`, by (L3) with `t = 0`
  have hzero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    simpa using hsmul 0 0 0
  -- Steps 4–5: in the orthonormal basis `b_k = q(ε_k)`, `trace f = Σ_k ⟨b_k, f b_k⟩`
  let b : OrthonormalBasis (Fin (n + ℓ)) ℝ (Amb n ℓ) :=
    (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).map q
  have hb : ∀ k, b k = q (EuclideanSpace.single k 1) := by
    intro k
    simp [b, EuclideanSpace.basisFun_apply]
  have htrace : ∀ f : Amb n ℓ →ₗ[ℝ] Amb n ℓ,
      LinearMap.trace ℝ (Amb n ℓ) f = ∑ k, inner ℝ (b k) (f (b k)) := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis f, Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  -- Steps 6–7: `p_{T⊥}` is self-adjoint, and `p_{T⊥} q(eᵢ, 0) = 0` as `p_T q(eᵢ, 0) = q(eᵢ, 0)`
  have hterm_cast : ∀ i : Fin n, inner ℝ (b (Fin.castAdd ℓ i))
      ((rotatedPlane q)ᗮ.starProjection (S.starProjection (b (Fin.castAdd ℓ i)))) = 0 := by
    intro i
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hcast,
      Submodule.starProjection_orthogonal_val, hproj, sub_self, inner_zero_left]
  -- Step 8: `p_{T⊥} e'_j = e'_j − q(0, 0) = e'_j` and `⟨e'_j, p_S e'_j⟩ = |p_S e'_j|²`
  have hterm_nat : ∀ j : Fin ℓ, inner ℝ (b (Fin.natAdd n j))
      ((rotatedPlane q)ᗮ.starProjection (S.starProjection (b (Fin.natAdd n j)))) =
        ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 := by
    intro j
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hnat,
      Submodule.starProjection_orthogonal_val, hproj, hzero, map_zero, sub_zero,
      ← real_inner_self_eq_norm_sq, S.inner_starProjection_left_eq_right,
      S.starProjection_eq_self_iff.2 (S.starProjection_apply_mem _)]
  -- Step 10: `trace(p_{T⊥} ∘ p_S) = ½ |p_S − p_T|²`, since `dim S = n = dim T`
  have htr := (Submission.hsNorm_starProjection_trace_identities).2.2 (n + ℓ) S (rotatedPlane q)
    (by rw [hS, hdimT])
  -- Steps 9 and 11: split the trace over the indices `castAdd ℓ i` and `natAdd n j`
  rw [← htr, htrace, Fin.sum_univ_add]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_eq_zero fun i _ => hterm_cast i, zero_add]
  exact (Finset.sum_congr rfl fun j _ => hterm_nat j).symm

/-- Graph orthogonality behind Simon Ch. 5, Theorem 4.5 (p. 116), proof step (7):
`e_{n+j} − (∇f^j, 0)` is normal to the graph.  If `r` is the `j`-th row of `D`
(`⟨r, v⟩ = (D v)_j` for all `v`), then `q(0, e_j) − q(r, 0) = q(−r, e_j)` and
`⟨(−r, e_j), (v, D v)⟩ = −⟨r, v⟩ + (D v)_j = 0`, so this difference is orthogonal to every generator
`q(v, D v)` of `S`, hence lies in `Sᗮ`, and the orthogonal projection onto `S` takes the same value
at `q(0, e_j)` and at `q(r, 0)`. -/
theorem gwe_gta_graph_row_orthogonal : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ) (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint r 0)) := by
  have hGA := any_radius_gr_la_graphPoint_algebra
  intro n ℓ q D j r hr
  -- the difference `q(0, e_j) − q(r, 0) = q(0 − r, e_j − 0)`, by linearity of `q` and (L2)
  have hdiff : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) =
      q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)) := by
    rw [← map_sub, (hGA n ℓ).2.2.2.1]
  -- it is orthogonal to every generator `q(v, D v)`: by (IP), `⟪·, ·⟫ = −⟪r, v⟫ + (D v)_j = 0`
  have hgen : ∀ v : Rn n, inner ℝ (q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)))
      (q (graphPoint v (D v))) = 0 := by
    intro v
    rw [LinearIsometryEquiv.inner_map_map, (hGA n ℓ).2.2.2.2.2.2, zero_sub, sub_zero,
      inner_neg_left, hr v, EuclideanSpace.inner_single_left]
    simp
  -- hence it lies in `Sᗮ`: the span `S` of the generators lies in `(ℝ ∙ x)ᗮ`
  have hmem : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) ∈
      (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))))ᗮ := by
    rw [hdiff]
    have hle : Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))) ≤
        (ℝ ∙ q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)))ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hgen v)
    refine (Submodule.mem_orthogonal' _ _).mpr (fun u hu => ?_)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
  -- the orthogonal projection onto `S` vanishes on `Sᗮ`
  have h0 := (Submodule.starProjection_apply_eq_zero_iff _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0
/-- Rows of a linear map `D : ℝⁿ → ℝ^ℓ` (in the proof of Simon Ch. 5, Theorem 4.5, `D = Df(x)`,
whose rows are the gradients `∇f^j`): (i) every row `r` of `D`, i.e. `⟪r, v⟫ = (D v)_j` for all `v`,
has `|r| ≤ ‖D‖`; (ii) the rows `R_j` (Riesz representatives of `v ↦ (D v)_j`) satisfy
`Σ_j |R_j|² = |D|²`. -/
theorem gwe_gta_row_bounds : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), (∀ (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → ‖r‖ ≤ ‖D‖) ∧ ∃ R : Fin ℓ → Rn n, (∀ (j : Fin ℓ) (v : Rn n), inner ℝ (R j) v = D v j) ∧ ∑ j : Fin ℓ, ‖R j‖ ^ 2 = hsNormSq D := by
  intro n ℓ D
  refine ⟨?_, ?_⟩
  · -- (i) `|r|² = ⟪r, r⟫ = (D r)_j ≤ |D r| ≤ ‖D‖ |r|`; divide by `|r|` unless `r = 0`.
    intro j r hr
    have h1 : ‖r‖ ^ 2 ≤ ‖D‖ * ‖r‖ :=
      calc ‖r‖ ^ 2 = inner ℝ r r := (real_inner_self_eq_norm_sq r).symm
        _ = D r j := hr r
        _ ≤ |D r j| := le_abs_self _
        _ = ‖D r j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖D r‖ := PiLp.norm_apply_le (D r) j
        _ ≤ ‖D‖ * ‖r‖ := D.le_opNorm r
    rcases (norm_nonneg r).eq_or_lt with h | h
    · rw [← h]
      exact norm_nonneg D
    · nlinarith
  · -- (ii) `R_j` is the Riesz representative of `v ↦ (D v)_j`; its coordinates are `(D eᵢ)_j`.
    let R : Fin ℓ → Rn n := fun j =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm ((EuclideanSpace.proj j).comp D)
    have hR : ∀ (j : Fin ℓ) (v : Rn n), inner ℝ (R j) v = D v j := by
      intro j v
      simp only [R, InnerProductSpace.toDual_symm_apply]
      rfl
    refine ⟨R, hR, ?_⟩
    have hcoord : ∀ (j : Fin ℓ) (i : Fin n), R j i = D (EuclideanSpace.single i 1) j := by
      intro j i
      rw [← hR j (EuclideanSpace.single i 1), EuclideanSpace.inner_single_right]
      simp
    -- Parseval in `ℝⁿ` and in `ℝ^ℓ`, after exchanging the two finite sums.
    unfold hsNormSq
    calc ∑ j : Fin ℓ, ‖R j‖ ^ 2
        = ∑ j : Fin ℓ, ∑ i : Fin n, (D (EuclideanSpace.single i 1) j) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [EuclideanSpace.real_norm_sq_eq]
          exact Finset.sum_congr rfl fun i _ => by rw [hcoord]
      _ = ∑ i : Fin n, ∑ j : Fin ℓ, (D (EuclideanSpace.single i 1) j) ^ 2 := Finset.sum_comm
      _ = ∑ i : Fin n, ‖D (EuclideanSpace.single i 1)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [EuclideanSpace.real_norm_sq_eq]
/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): graph coordinates on
`ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ` and the projection onto `T₀ = q(ℝⁿ × {0})`, the plane the book takes to be
`ℝⁿ × {0}` without loss of generality. For a linear isometry `q` of `ℝ^{n+ℓ}`:
(i) `(a, b) − (a', b') = (a − a', b − b')`; (ii) `|(a, b)|² = |a|² + |b|²`; (iii) every
`z ∈ ℝ^{n+ℓ}` is some `(a, b)`; (iv) `p_{T₀}(q(a, b)) = q(a, 0)`.
The coordinate of `(a, b)` at `castAdd ℓ i` is `a_i` and at `natAdd n j` is `b_j`, and every index
of `Fin (n + ℓ)` has one of these forms (`Fin.addCases`); this gives (i) and (iii), and (ii) by
splitting `Σ_k z_k²` with `Fin.sum_univ_add`. For (iv), `(a, 0) = Σ_i a_i e_{castAdd ℓ i}` lies in
`ℝⁿ × {0}`, `(0, b)` is orthogonal to every `e_{castAdd ℓ i}` and hence to `ℝⁿ × {0}`, and `q`
preserves inner products; so `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) = q(0, b) ⊥ T₀`, which
characterizes `q(a, 0)` as the orthogonal projection of `q(a, b)` onto `T₀`. -/
theorem lip_approx_graph_coordinates : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b')) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ z : Amb n ℓ, ∃ (a : Rn n) (b : Rn ℓ), z = graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a 0)) := by
  intro n ℓ q
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- (i): subtraction is coordinatewise
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  refine ⟨hsub, ?_, ?_, ?_⟩
  -- (ii): split `‖z‖² = Σ_k ‖z_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- (iii): read off `a` and `b` from the two blocks of coordinates of `z`
  · intro z
    refine ⟨WithLp.toLp 2 (fun i => z (Fin.castAdd ℓ i)),
      WithLp.toLp 2 (fun j => z (Fin.natAdd n j)), ?_⟩
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [hl]
    · rw [hr]
  -- (iv)
  · intro a b
    -- `graphPoint a 0 = Σ_i a_i e_{castAdd ℓ i}` lies in `ℝⁿ × {0}`
    have hmem : graphPoint a 0 ∈ horizontalPlane n ℓ := by
      have e : graphPoint a 0 =
          ∑ i : Fin n, a i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
        ext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [hl]
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
            Pi.smul_apply, Pi.single_apply, Fin.castAdd_inj, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · rw [hr]
          simp only [PiLp.zero_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (Finset.sum_eq_zero fun x _ => ?_).symm
          have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ x := by
            intro h
            have h' := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
            have := x.isLt
            omega
          rw [Pi.single_eq_of_ne hne, mul_zero]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `graphPoint 0 b` is orthogonal to every `e_{castAdd ℓ i}`, hence to `ℝⁿ × {0}`
    have horth : ∀ h ∈ horizontalPlane n ℓ, inner ℝ (graphPoint 0 b) h = 0 := by
      have hle : horizontalPlane n ℓ ≤ (ℝ ∙ graphPoint 0 b)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
          EuclideanSpace.inner_single_right, hl]
        simp
      intro h hh
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hh)
    -- `q(a, 0) ∈ T₀`, and `q(a, b) - q(a, 0) = q(0, b)` is orthogonal to `T₀ = q(ℝⁿ × {0})`
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
    intro w hw
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
    rw [← map_sub, hsub, sub_self, sub_zero]
    exact (q.inner_map_map _ _).trans (horth h hh)
/-- Simon Ch. 5, proof of Theorem 4.5, step (1a): the weight `μ_V = (Hⁿ ⌞ M) ⌞ θ` of a
rectifiable varifold is concentrated on `spt V = U ∩ spt μ_V`. The support of a measure on the
second countable space `ℝ^{n+ℓ}` is conull (`Measure.support_mem_ae`), and `μ_V ≪ Hⁿ ⌞ M`
(`withDensity_absolutelyContinuous`), where `Hⁿ ⌞ M` is concentrated on the `Hⁿ`-null-measurable
carrier `M ⊆ U` (`ae_restrict_mem₀`). -/
theorem tdo_ghe_ae_mem_support : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), ∀ᵐ x ∂V.weight, x ∈ V.support := by
  intro n ℓ U V
  -- `μ_V`-a.e. point lies in `spt μ_V`
  have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
  -- `μ_V`-a.e. point lies in `M`, since `Hⁿ ⌞ M`-a.e. point does and `μ_V ≪ Hⁿ ⌞ M`
  have h2 : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨V.carrier_subset hx2, hx1⟩
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the profile of the cutoff `ζ(x) = φ(|x − ξ|/ρ)` with
`ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B_ρ(ξ)` and `|∇ζ| ≤ 3/ρ`.  With `S = smoothTransition`,
the bump `g(t) = S(12(t − 1/2)) S(12(1 − t)) ∈ [0, 1]` vanishes for `t ≤ 1/2` and for `t ≥ 1` and
equals `1` on `[7/12, 11/12]`, so `c = ∫_{1/2}^1 g ≥ 1/3`; then `φ(t) = 1 − c⁻¹ ∫_{1/2}^t g` is
`C^∞` with `|φ'| = c⁻¹ g ≤ 3`. -/
theorem exists_smooth_step_profile_lipschitz_three : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
  -- The bump `g`: smooth, with values in `[0, 1]`, zero off `(1/2, 1)`, one on `[7/12, 11/12]`.
  set g : ℝ → ℝ := fun t =>
    Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
    have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg_cont.intervalIntegrable a b
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
      (Real.smoothTransition.le_one _)
  have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
  have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
    simp only [hg_def]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  -- The normalizing constant `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`.
  set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
  have hc_ge : 1 / 3 ≤ c := by
    have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        norm_num
      · intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        exact hg_mid s hs.1 hs.2
    rw [← h]
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (ae_of_all _ hg_nonneg) (hg_int _ _)
  have hc_pos : 0 < c := by linarith
  have hcinv_le : c⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hc_pos (by norm_num)]
    linarith
  -- The primitive `F(t) = ∫_{1/2}^t g`: `F' = g` (FTC), so `F` is smooth; `0 ≤ F ≤ c`,
  -- `F = 0` on `(-∞, 1/2]` and `F = c` on `[1, ∞)`.
  set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
    (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
      (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
  have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
    simp only [hF_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hg_left s hs.2
  have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
    simp only [hF_def, hc_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
    have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_le ht] at hs
        exact hg_right s hs.1
    rw [h, add_zero]
  have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hF_left t ht]
      exact ⟨le_rfl, hc_pos.le⟩
    rcases le_total 1 t with ht' | ht'
    · rw [hF_right t ht']
      exact ⟨hc_pos.le, le_rfl⟩
    exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
      intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
  -- The profile `φ = 1 − c⁻¹ F`, with `φ' = −c⁻¹ g`.
  have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
    simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
  refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h₀, h₁⟩ := hF_bounds t
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
    have h : c⁻¹ * F t ≤ 1 := by
      calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
        _ = 1 := inv_mul_cancel₀ hc_pos.ne'
    exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
  · intro t ht
    simp only [hF_left t ht, mul_zero, sub_zero]
  · intro t ht
    simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
  · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
    rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
    calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
      _ ≤ 3 := by rw [mul_one]; exact hcinv_le
      _ = ((3 : ℝ≥0) : ℝ) := by norm_num
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), smoothness of the cutoff: if `φ` is `C^∞` with
`φ ≡ 1` on `(-∞, 1/2]` and `ρ > 0`, then `ζ(x) = φ(‖x − ξ‖/ρ)` is `C^∞` on `ℝᵐ`.  Near `ξ`,
`ζ ≡ 1` on `B̆_{ρ/2}(ξ)`; at `x ≠ ξ` the norm is `C^∞` at `x − ξ ≠ 0`. -/
theorem contDiff_radial_profile_of_eq_one_le_half : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (φ : ℝ → ℝ), 0 < ρ → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ t, t ≤ 1 / 2 → φ t = 1) → ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn m => φ (‖x - ξ‖ / ρ)) := by
  intro m ξ ρ φ hρ hφ hφ1
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x ξ with rfl | hx
  · -- `ζ ≡ 1` on the open ball `B̆_{ρ/2}(ξ)`, a neighbourhood of `ξ`.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds x (half_pos hρ)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hφ1 _ ((div_le_iff₀ hρ).2 (by linarith))
  · -- `y ↦ ‖y − ξ‖/ρ` is `C^∞` at `x` since `x − ξ ≠ 0`; compose with `φ`.
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Rn m => ‖y - ξ‖ / ρ) x :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const ρ
    exact hφ.contDiffAt.comp x h
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff gradient bound `|∇ζ| ≤ 3/ρ`, for a general
Lipschitz constant `K` in place of `3`.  If `φ` is `K`-Lipschitz and `ρ > 0`, then
`ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality, so
`‖Dζ(x)‖ ≤ K/ρ` at every `x` (where `ζ` is not differentiable, `fderiv ℝ ζ x = 0`). -/
theorem norm_fderiv_radial_profile_le_of_lipschitzWith : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (K : ℝ≥0) (φ : ℝ → ℝ), 0 < ρ → LipschitzWith K φ → ∀ x : Rn m, ‖fderiv ℝ (fun y : Rn m => φ (‖y - ξ‖ / ρ)) x‖ ≤ (K : ℝ) / ρ := by
  intro m ξ ρ K φ hρ hφ x
  -- `ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality.
  have hKρ : ((K / ρ.toNNReal : ℝ≥0) : ℝ) = K / ρ := by
    rw [NNReal.coe_div, Real.coe_toNNReal ρ hρ.le]
  have hlip : LipschitzWith (K / ρ.toNNReal) fun y : Rn m => φ (‖y - ξ‖ / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKρ]
    calc dist (φ (‖y - ξ‖ / ρ)) (φ (‖z - ξ‖ / ρ))
        ≤ K * dist (‖y - ξ‖ / ρ) (‖z - ξ‖ / ρ) := hφ.dist_le_mul _ _
      _ = K / ρ * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]; ring
      _ ≤ K / ρ * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = K / ρ * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- A `C`-Lipschitz function has `‖Dζ(x)‖ ≤ C` (and `fderiv ℝ ζ x = 0` where not differentiable).
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq hKρ
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): a cutoff `ζ ∈ C^∞(ℝᵐ)` with `0 ≤ ζ ≤ 1`, `ζ ≡ 1` on
`B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B̆_ρ(ξ)` and `|Dζ| ≤ 3/ρ`.  Take `ζ(x) = φ(|x − ξ|/ρ)` for the smooth
`3`-Lipschitz step profile `φ` (`φ = 1` on `(-∞, 1/2]`, `φ = 0` on `[1, ∞)`): `ζ` is smooth since it
is constant near `ξ`, and the radial lift of a `3`-Lipschitz profile has `|Dζ| ≤ 3/ρ`. -/
theorem exists_smooth_cutoff_half_ball_grad_le : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Metric.closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ :=
    Submission.exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    Submission.contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ_smooth hφ_one,
    fun x => hφ_bounds _, fun x hx => hφ_one _ ?_, fun x hx => hφ_zero _ ?_, fun x => ?_⟩
  · -- `|x − ξ| ≤ ρ/2`, so `|x − ξ|/ρ ≤ 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ |x − ξ|`, so `1 ≤ |x − ξ|/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- The profile is `3`-Lipschitz, so `|Dζ(x)| ≤ 3/ρ`.
    have h := Submission.norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφ_lip x
    rwa [NNReal.coe_ofNat] at h
/-- **Density of the varifold weight with respect to `Hⁿ`** (Simon Ch. 4, 1.1: `μ_V = Hⁿ ⌞ θ`,
with `θ = 0` off `M`).  Writing `g = 1_M θ`: (i) `g` has a Borel representative that is `≥ 0`
everywhere; (ii) `∫_S φ dμ_V = ∫_S g φ dHⁿ` for every Borel `S` and every `φ ≥ 0` (not necessarily
measurable).  `g ≥ 0` because `θ > 0` on `M`, and `g` is `Hⁿ`-a.e. measurable since `M` is
`Hⁿ`-null-measurable and `θ` is a.e. measurable on `M`; `max(mk g, 0)` is the representative.
For (ii), `μ_V⌞S = ((Hⁿ⌞M)⌞S) ⌞ ofReal ∘ θ`, the finite density can be multiplied in without
measurability of `φ`, `(Hⁿ⌞M)⌞S = (Hⁿ⌞S)⌞M`, and integrating over `M` is integrating `1_M`. -/
theorem gwe_vgt_weight_density : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∃ g : Amb n ℓ → ℝ, Measurable g ∧ (∀ y, 0 ≤ g y) ∧ g =ᵐ[(μHE[n] : Measure (Amb n ℓ))] V.carrier.indicator V.mult) ∧ ∀ S : Set (Amb n ℓ), MeasurableSet S → ∀ φ : Amb n ℓ → ℝ≥0∞, ∫⁻ y in S, φ y ∂V.weight = ∫⁻ y in S, ENNReal.ofReal (V.carrier.indicator V.mult y) * φ y ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ U V
  have hM : NullMeasurableSet V.carrier (μHE[n] : Measure (Amb n ℓ)) :=
    V.nullMeasurableSet_carrier
  -- `g = 1_M θ ≥ 0` everywhere, since `θ > 0` on `M`.
  have hg0 : ∀ y, 0 ≤ V.carrier.indicator V.mult y := by
    intro y
    by_cases hy : y ∈ V.carrier
    · rw [indicator_of_mem hy]
      exact (V.mult_pos y hy).le
    · rw [indicator_of_notMem hy]
  refine ⟨?_, ?_⟩
  · -- (i) `g` is `Hⁿ`-a.e. measurable; `max(mk g, 0)` is a nonnegative Borel representative.
    have hae : AEMeasurable (V.carrier.indicator V.mult) (μHE[n] : Measure (Amb n ℓ)) :=
      (aemeasurable_indicator_iff₀ hM).2 V.aemeasurable_mult
    refine ⟨fun y => max (hae.mk _ y) 0, hae.measurable_mk.max measurable_const,
      fun y => le_max_right _ _, ?_⟩
    filter_upwards [hae.ae_eq_mk] with y hy
    rw [← hy]
    exact max_eq_left (hg0 y)
  · -- (ii) Remove the finite density `ofReal ∘ θ`, then rearrange the restrictions.
    intro S hS φ
    have hρ : AEMeasurable (fun x => ENNReal.ofReal (V.mult x))
        (((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict S) :=
      V.aemeasurable_mult.ennreal_ofReal.restrict
    have hMS : NullMeasurableSet V.carrier ((μHE[n] : Measure (Amb n ℓ)).restrict S) :=
      hM.mono Measure.restrict_le_self
    rw [RectifiableVarifold.weight, restrict_withDensity hS,
      lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      Measure.restrict_restrict hS, inter_comm, ← Measure.restrict_restrict₀ hMS,
      ← lintegral_indicator₀ hMS]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ V.carrier
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
/-- **Measurability of the graph map and of the graph Jacobian** over a closed ball `B = B_R(0)`.
Let `F(x) = q(graphPoint x (f x))` with `f` continuous on `B`, and `J_f(x) =
√det(Iₙ + (⟨Df(x) e_a, Df(x) e_b⟩)_{a,b})`.  (i) `F(A)` is Borel for every Borel `A ⊆ B`:
`(a, b) ↦ graphPoint a b` is continuous coordinatewise, so `F` is continuous on `B`; `F` is
injective, since the first `n` coordinates of `F(x)` determine `x` after undoing `q`; apply
Lusin–Souslin.  (ii) `F` agrees on `B` with the Borel map `B.piecewise F 0` (`B` closed).
(iii) `J_f = Φ ∘ Df` with `Φ` continuous on `ℝⁿ →L[ℝ] ℝ^ℓ` and `Df` Borel. -/
theorem gwe_vgt_graph_measurability : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), ContinuousOn f (closedBall 0 R) → (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → MeasurableSet (q '' graphOver f A)) ∧ (∃ Fh : Rn n → Amb n ℓ, Measurable Fh ∧ ∀ x ∈ closedBall (0 : Rn n) R, Fh x = q (graphPoint x (f x))) ∧ Measurable (fun x : Rn n => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) := by
  intro n ℓ q f R hf
  -- `(a, b) ↦ graphPoint a b` is continuous: each coordinate is a coordinate of `a` or of `b`.
  have hgp : Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) := by
    unfold graphPoint
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [Fin.append_left]
      exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
    · simp only [Fin.append_right]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
  -- `F = q ∘ (x ↦ graphPoint x (f x))` is continuous on `B` and injective.
  have hFc : ContinuousOn (fun x => q (graphPoint x (f x))) (closedBall 0 R) :=
    q.continuous.comp_continuousOn (hgp.comp_continuousOn (continuousOn_id.prodMk hf))
  have hFi : Function.Injective (fun x => q (graphPoint x (f x))) := by
    intro x y hxy
    have h := congrArg (fun (z : Amb n ℓ) (j : Fin n) => z (Fin.castAdd ℓ j)) (q.injective hxy)
    ext j
    simpa [graphPoint] using congrFun h j
  refine ⟨fun A hA hAB => ?_, ?_, ?_⟩
  · -- (i) Lusin–Souslin for the continuous injective map `F` on the Borel set `A`.
    rw [graphOver, image_image]
    exact hA.image_of_continuousOn_injOn (hFc.mono hAB) hFi.injOn
  · -- (ii) `B.piecewise F 0` is Borel and equals `F` on `B`.
    classical
    exact ⟨(closedBall 0 R).piecewise (fun x => q (graphPoint x (f x))) fun _ => 0,
      hFc.measurable_piecewise continuousOn_const measurableSet_closedBall,
      fun x hx => piecewise_eq_of_mem _ _ _ hx⟩
  · -- (iii) `J_f = Φ ∘ fderiv ℝ f` with `Φ` continuous and `fderiv ℝ f` Borel.
    have hΦ : Continuous fun D : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det
        ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (D (EuclideanSpace.single a (1 : ℝ)))
            (D (EuclideanSpace.single b (1 : ℝ))))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_const.add
        (continuous_matrix fun a b => ?_)))
      simp only [Matrix.of_apply]
      exact (continuous_eval_const _).inner (continuous_eval_const _)
    exact hΦ.measurable.comp (measurable_fderiv ℝ f)

end Submission
/-- **Bochner and null-set transfer** (steps 5 and 6 of the varifold graph transfer).  The
`lintegral` transfer identity says `μ ⌞ S = G_#((Lⁿ ⌞ A) ⌞ W)`; pushing Bochner integrals through
`G` and the density `W ≥ 0` gives (i) for every Borel `φ`, and testing it on `φ = 1_{Z'}` for a Borel
`μ`-null `Z' ⊇ Z` gives `W = 0` a.e. on `A ∩ G⁻¹(Z)`. -/
theorem Submission.gwe_vgt_transfer_consequences : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (S : Set (Amb n ℓ)) (A : Set (Rn n)) (G : Rn n → Amb n ℓ) (W : Rn n → ℝ), MeasurableSet A → Measurable G → Measurable W → (∀ x, 0 ≤ W x) → (∀ φ : Amb n ℓ → ℝ≥0∞, Measurable φ → ∫⁻ y in S, φ y ∂μ = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (G x)) → (∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in S, φ y ∂μ = ∫ x in A, W x * φ (G x)) ∧ ∀ Z : Set (Amb n ℓ), μ Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ A → G x ∈ Z → W x = 0 := by
  intro n ℓ μ S A G W hA hG hW hW0 hT
  -- Step 1: `μ ⌞ S = G_# ν` with `ν = (Lⁿ ⌞ A).withDensity (ofReal ∘ W)`, tested on Borel `T`.
  have hpush : μ.restrict S =
      Measure.map G ((volume.restrict A).withDensity fun x => ENNReal.ofReal (W x)) := by
    ext T hTm
    calc μ.restrict S T = ∫⁻ y in S, T.indicator 1 y ∂μ := (lintegral_indicator_one hTm).symm
      _ = ∫⁻ x in A, ENNReal.ofReal (W x) * T.indicator 1 (G x) :=
          hT _ (measurable_one.indicator hTm)
      _ = ∫⁻ x in A, (G ⁻¹' T).indicator (fun x => ENNReal.ofReal (W x)) x := by
          refine lintegral_congr fun x => ?_
          by_cases hx : G x ∈ T <;> simp [hx]
      _ = ∫⁻ x in G ⁻¹' T, ENNReal.ofReal (W x) ∂(volume.restrict A) :=
          lintegral_indicator (hG hTm) _
      _ = Measure.map G ((volume.restrict A).withDensity fun x => ENNReal.ofReal (W x)) T := by
          rw [Measure.map_apply hG hTm, withDensity_apply _ (hG hTm)]
  refine ⟨fun φ hφ => ?_, fun Z hZ => ?_⟩
  · -- Step 2: push the Bochner integral through `G`, then through the density `ofReal ∘ W`.
    rw [hpush, integral_map hG.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hW.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hW0 x), smul_eq_mul]
  · -- Steps 3–5: test the identity on `1_{Z'}` for a Borel `μ`-null `Z' ⊇ Z`.
    obtain ⟨Z', hZZ', hZ'm, hZ'0⟩ := exists_measurable_superset_of_null hZ
    have hmeas : Measurable fun x => ENNReal.ofReal (W x) * Z'.indicator 1 (G x) :=
      hW.ennreal_ofReal.mul ((measurable_one.indicator hZ'm).comp hG)
    have h0 : ∫⁻ x in A, ENNReal.ofReal (W x) * Z'.indicator 1 (G x) = 0 := by
      rw [← hT _ (measurable_one.indicator hZ'm), lintegral_indicator_one hZ'm]
      exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hZ'0.le)
    filter_upwards [(ae_restrict_iff' hA).1 ((lintegral_eq_zero_iff hmeas).1 h0)]
      with x hx hxA hGx
    have h1 := hx hxA
    simp only [Set.indicator_of_mem (hZZ' hGx), Pi.one_apply, mul_one, Pi.zero_apply,
      ENNReal.ofReal_eq_zero] at h1
    exact le_antisymm h1 (hW0 x)

namespace Submission

/-- **The Gram matrix of a linear map** (Simon Ch. 5, proof of Theorem 4.5, p. 119: the graph
Jacobian `J_F = √det(δ_ij + D_i f · D_j f)`).  For `D : ℝⁿ →L[ℝ] ℝ^ℓ` let `G_ab = ⟨D e_a, D e_b⟩`.
Then (i) `G` is symmetric, since the real inner product is; (ii) `G` is positive semidefinite:
`x · Gx = Σ_{a,b} x_a x_b ⟨D e_a, D e_b⟩ = |Σ_a x_a D e_a|² ≥ 0` by bilinearity; and
(iii) `trace G = Σ_a |D e_a|² = |D|²` (`hsNormSq`). -/
theorem gwe_gjb_gram_symm_psd_trace : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), Matrix.IsSymm (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) ∧ (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x)) ∧ Matrix.trace (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) = hsNormSq D := by
  intro n ℓ D
  refine ⟨?_, fun x => ?_, ?_⟩
  · -- (i) `G_ba = ⟨D e_b, D e_a⟩ = ⟨D e_a, D e_b⟩ = G_ab`.
    refine Matrix.IsSymm.ext fun a b => ?_
    simp only [Matrix.of_apply]
    exact real_inner_comm _ _
  · -- (ii) `x · Gx = ⟨w, w⟩` for `w = Σ_a x_a • D e_a`, by bilinearity.
    have h : dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x) =
        inner ℝ (∑ a, x a • D (EuclideanSpace.single a (1 : ℝ)))
          (∑ b, x b • D (EuclideanSpace.single b (1 : ℝ))) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_comm (D (EuclideanSpace.single a (1 : ℝ)))]
      ring
    rw [h]
    exact real_inner_self_nonneg
  · -- (iii) `trace G = Σ_a ⟨D e_a, D e_a⟩ = Σ_a ‖D e_a‖² = hsNormSq D`.
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, hsNormSq, real_inner_self_eq_norm_sq]
/-- **Determinant bounds for `I + G`** (graph Jacobian bounds in the tilt-excess decay argument):
if `G` is a symmetric real `n × n` matrix with `0 ≤ x ⬝ᵥ G x` for all `x`, then
`1 ≤ det (I + G) ≤ exp (trace G)`.  By Gaussian elimination: `A = I + G` satisfies
`x ⬝ᵥ x ≤ x ⬝ᵥ A x`, so its pivot `a = A₀₀` is at least `1`, and clearing the first column gives
`det A = a * det S` for the Schur complement `S = C - a⁻¹ b bᵀ`.  `S` is again symmetric with
`x ⬝ᵥ x ≤ x ⬝ᵥ S x` (test `A` on `(-(b ⬝ᵥ x) / a, x)`) and `trace S ≤ trace A - a`, so induction
gives `1 ≤ det A ≤ exp (trace A - n)` using `a ≤ exp (a - 1)`; finally `trace (I + G) = n + trace G`.
-/
theorem gwe_gjb_det_one_add_bounds : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ), Matrix.IsSymm G → (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec G x)) → 1 ≤ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ∧ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ≤ Real.exp (Matrix.trace G) := by
  -- Induction on the size: a symmetric `A` with `x ⬝ᵥ x ≤ x ⬝ᵥ A x` for all `x` satisfies
  -- `1 ≤ det A ≤ exp (trace A - m)`.
  have key : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∀ i j, A j i = A i j) →
      (∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec A x)) →
      1 ≤ A.det ∧ A.det ≤ Real.exp (A.trace - m) := by
    intro m
    induction m with
    | zero =>
      intro A _ _
      simp [Matrix.det_fin_zero, Matrix.trace]
    | succ m ih =>
      intro A hA hq
      -- The pivot `a = A₀₀ = e₀ ⬝ᵥ A e₀` is at least `e₀ ⬝ᵥ e₀ = 1`.
      have ha : 1 ≤ A 0 0 := by
        have h := hq (Pi.single 0 1)
        simpa using h
      have ha0 : A 0 0 ≠ 0 := (by linarith : (0 : ℝ) < A 0 0).ne'
      -- The Schur complement `S = C - a⁻¹ b bᵀ` of the pivot.
      obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin m) ℝ,
          S = Matrix.of fun i j => A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ := ⟨_, rfl⟩
      have hSs : ∀ i j, S j i = S i j := by
        intro i j
        rw [hS, Matrix.of_apply, Matrix.of_apply, hA i.succ j.succ, hA 0 i.succ, hA 0 j.succ]
        ring
      -- `x ⬝ᵥ S x = y ⬝ᵥ A y` for `y = (-(b ⬝ᵥ x) / a, x)`, and `y ⬝ᵥ y ≥ x ⬝ᵥ x`.
      have hSq : ∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec S x) := by
        intro x
        obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∑ j : Fin m, A 0 j.succ * x j := ⟨_, rfl⟩
        obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ i : Fin m, x i * ∑ j : Fin m, A i.succ j.succ * x j :=
          ⟨_, rfl⟩
        have hrow : ∀ i : Fin m,
            Matrix.mulVec S x i = ∑ j, A i.succ j.succ * x j - A 0 i.succ / A 0 0 * b := by
          intro i
          simp only [Matrix.mulVec, dotProduct, hS, Matrix.of_apply]
          rw [hb, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hA 0 i.succ]
          ring
        have eS : dotProduct x (Matrix.mulVec S x) = Q - b * b / A 0 0 := by
          calc dotProduct x (Matrix.mulVec S x)
              = ∑ i, (x i * ∑ j, A i.succ j.succ * x j - A 0 i.succ * x i * (b / A 0 0)) := by
                simp only [dotProduct]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [hrow i]
                ring
            _ = Q - b * b / A 0 0 := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hQ, ← hb]
                ring
        have eA : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ)
            (Matrix.mulVec A (Fin.cons t x)) = A 0 0 * t * t + 2 * t * b + Q := by
          intro t
          simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          have h1 : ∑ i : Fin m, x i * (A i.succ 0 * t + ∑ j, A i.succ j.succ * x j) =
              t * b + Q := by
            rw [hb, hQ, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA 0 i.succ]
            ring
          rw [h1, ← hb]
          ring
        have eI : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ) (Fin.cons t x) =
            t * t + dotProduct x x := by
          intro t
          simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        have h := hq (Fin.cons (-b / A 0 0) x)
        rw [eA, eI] at h
        rw [eS]
        have e : A 0 0 * (-b / A 0 0) * (-b / A 0 0) + 2 * (-b / A 0 0) * b + Q =
            Q - b * b / A 0 0 := by
          field_simp
          ring
        nlinarith [mul_self_nonneg (-b / A 0 0)]
      -- Eliminating the first column below the pivot: `det A = a * det S`.
      have hdet : A.det = A 0 0 * S.det := by
        obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → ℝ,
            c = Fin.cons 0 (fun i : Fin m => A i.succ 0 / A 0 0) := ⟨_, rfl⟩
        obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
            E = Matrix.of fun i j => A i j - c i * A 0 j := ⟨_, rfl⟩
        have hc0 : c 0 = 0 := by rw [hc]; rfl
        have hE0 : ∀ j, E 0 j = A 0 j := by
          intro j
          rw [hE, Matrix.of_apply, hc0]
          ring
        have hAE : A.det = E.det :=
          Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 hc0 fun i j => by
            rw [hE0, hE, Matrix.of_apply]
            ring
        have hcol : ∀ i : Fin m, E i.succ 0 = 0 := by
          intro i
          rw [hE, Matrix.of_apply, hc, Fin.cons_succ, div_mul_cancel₀ _ ha0, sub_self]
        have hsub : E.submatrix Fin.succ Fin.succ = S := by
          ext i j
          simp only [Matrix.submatrix_apply, hE, hS, Matrix.of_apply, hc, Fin.cons_succ]
        rw [hAE, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
          pow_zero, one_mul, Fin.succAbove_zero, hE0, hsub]
      -- `trace A = a + trace S + Σᵢ bᵢ² / a`.
      have htr : A.trace = A 0 0 + S.trace + ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 := by
        simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, hS, Matrix.of_apply]
        rw [Finset.sum_sub_distrib]
        have e : ∀ i : Fin m, A i.succ 0 / A 0 0 * A 0 i.succ = A 0 i.succ ^ 2 / A 0 0 := by
          intro i
          rw [hA 0 i.succ]
          ring
        simp only [e]
        ring
      obtain ⟨h1, h2⟩ := ih S hSs hSq
      have hsum : 0 ≤ ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 :=
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (by linarith)
      have hexp : A 0 0 ≤ Real.exp (A 0 0 - 1) := by
        have := Real.add_one_le_exp (A 0 0 - 1)
        linarith
      refine ⟨?_, ?_⟩
      · rw [hdet]
        nlinarith
      · rw [hdet]
        calc A 0 0 * S.det ≤ Real.exp (A 0 0 - 1) * Real.exp (S.trace - m) :=
              mul_le_mul hexp h2 (by linarith) (Real.exp_pos _).le
          _ = Real.exp (A 0 0 - 1 + (S.trace - m)) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (A.trace - ↑(m + 1)) := by
              apply Real.exp_le_exp.mpr
              rw [htr]
              push_cast
              linarith
  intro n G hG hpos
  have hsymm : ∀ i j, ((1 : Matrix (Fin n) (Fin n) ℝ) + G) j i =
      ((1 : Matrix (Fin n) (Fin n) ℝ) + G) i j :=
    (Matrix.isSymm_one.add hG).apply
  have hquad : ∀ x : Fin n → ℝ,
      dotProduct x x ≤ dotProduct x (Matrix.mulVec ((1 : Matrix (Fin n) (Fin n) ℝ) + G) x) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    linarith [hpos x]
  obtain ⟨h1, h2⟩ := key n _ hsymm hquad
  refine ⟨h1, h2.trans_eq ?_⟩
  rw [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  congr 1
  ring
/-- **Scalar exponential bound** for the area Jacobian of a linear graph (used with `s = |D|²`,
`T = n` in `J(D) ≤ exp(|D|²/2) ≤ 1 + (e^{n/2}/2)|D|²`): for `0 ≤ s ≤ T`,
`exp(s/2) ≤ 1 + (exp(T/2)/2) s`.  With `t = s/2`, `1 - t ≤ exp(-t)` (`add_one_le_exp` at `-t`)
times `exp t > 0` gives `exp t ≤ 1 + t exp t`, and `t exp t ≤ t exp(T/2)` by monotonicity of
`exp` and `0 ≤ t ≤ T/2`. -/
theorem gwe_gjb_exp_half_le : ∀ (s T : ℝ), 0 ≤ s → s ≤ T → Real.exp (s / 2) ≤ 1 + Real.exp (T / 2) / 2 * s := by
  intro s T hs hsT
  -- `1 - s/2 ≤ exp (-(s/2))`: `add_one_le_exp` at `-(s/2)`.
  have h1 : 1 - s / 2 ≤ Real.exp (-(s / 2)) := by
    linarith [Real.add_one_le_exp (-(s / 2))]
  -- Multiply by `exp (s/2) > 0`, using `exp (-(s/2)) * exp (s/2) = exp 0 = 1`.
  have h2 : (1 - s / 2) * Real.exp (s / 2) ≤ 1 := by
    calc (1 - s / 2) * Real.exp (s / 2) ≤ Real.exp (-(s / 2)) * Real.exp (s / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- `exp` is monotone, `s/2 ≤ T/2` and `0 ≤ s/2`.
  have h4 : s / 2 * Real.exp (s / 2) ≤ s / 2 * Real.exp (T / 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith)
  -- `exp (s/2) ≤ 1 + (s/2) exp (s/2) ≤ 1 + (s/2) exp (T/2)`.
  linarith
/-- **Hilbert–Schmidt versus operator norm** (Simon, Notation p. ix), as used in the hole estimate
of the proof of Ch. 5, Corollary 2.7 (`‖A‖ ≤ |A|`).  For `A : ℝᵐ →L ℝᵏ` the squared Hilbert–Schmidt
norm `|A|² = Σᵢ |A eᵢ|²` is continuous in `A` (a finite sum of squared norms of the evaluations
`A ↦ A eᵢ`) and satisfies `0 ≤ |A|² ≤ m ‖A‖²` (`|A eᵢ| ≤ ‖A‖ |eᵢ| = ‖A‖`).  Moreover
`|A v|² ≤ |A|² |v|²`: expanding `v = Σᵢ vᵢ eᵢ` gives `|A v| ≤ Σᵢ |vᵢ| |A eᵢ|`, and Cauchy–Schwarz
bounds the square of the right side by `(Σᵢ |vᵢ|²)(Σᵢ |A eᵢ|²) = |v|² |A|²`. -/
theorem lgc_hsNormSq_bounds : ∀ (m k : ℕ), Continuous (fun A : Rn m →L[ℝ] Rn k => hsNormSq A) ∧ ∀ A : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq A ∧ hsNormSq A ≤ m * ‖A‖ ^ 2 ∧ ∀ v : Rn m, ‖A v‖ ^ 2 ≤ hsNormSq A * ‖v‖ ^ 2 := by
  intro m k
  refine ⟨?_, fun A => ⟨?_, ?_, fun v => ?_⟩⟩
  · -- Continuity: a finite sum of `‖A eᵢ‖ ^ 2`, each continuous in `A`.
    unfold hsNormSq
    fun_prop
  · unfold hsNormSq
    positivity
  · -- `‖A eᵢ‖ ≤ ‖A‖ ‖eᵢ‖ = ‖A‖` for each of the `m` summands.
    unfold hsNormSq
    calc ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin m, ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1:ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = m * ‖A‖ ^ 2 := by simp
  · unfold hsNormSq
    set e : Fin m → Rn m := fun i => EuclideanSpace.single i 1 with he
    -- Expand `v` in the standard basis and apply the triangle inequality.
    have hv : v = ∑ i, v i • e i := by
      ext j
      simp [he, Pi.single_apply]
    have hAv : A v = ∑ i, v i • A (e i) := by
      conv_lhs => rw [hv]
      simp [map_sum, map_smul]
    have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (e i)‖ := by
      rw [hAv]
      calc _ ≤ ∑ i, ‖v i • A (e i)‖ := norm_sum_le _ _
        _ = _ := by simp [norm_smul]
    -- Cauchy–Schwarz for the finite sums, and `‖v‖² = Σᵢ |vᵢ|²`.
    have h2 : (∑ i, |v i| * ‖A (e i)‖) ^ 2 ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ‖v‖ ^ 2 = ∑ i, |v i| ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [sq_abs]
    have h0 : 0 ≤ ‖A v‖ := norm_nonneg _
    calc ‖A v‖ ^ 2 ≤ (∑ i, |v i| * ‖A (e i)‖) ^ 2 := by gcongr
      _ ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) := h2
      _ = (∑ i, ‖A (e i)‖ ^ 2) * ‖v‖ ^ 2 := by rw [h3, mul_comm]

/-- **Area Jacobian of a linear graph** (Simon Ch. 5, proof of Theorem 4.5, p. 119:
`1 ≤ J_F ≤ 1 + C |∇f|²`).  For `D : ℝⁿ →L ℝ^ℓ` with Gram matrix `G = (⟨D eₐ, D e_b⟩)_{a,b}`, the
area Jacobian of `v ↦ (v, D v)` is `J(D) = √det(I + G)`; then `1 ≤ J(D)`, and `‖D‖ ≤ 1` implies
`J(D) ≤ 1 + (e^{n/2}/2) |D|²`.  `G` is symmetric positive semidefinite with `trace G = |D|²`, so
`1 ≤ det(I + G) ≤ exp |D|²` and `1 ≤ J(D) ≤ exp(|D|²/2)`.  If `‖D‖ ≤ 1` then `0 ≤ |D|² ≤ n ‖D‖² ≤ n`,
and `exp(s/2) ≤ 1 + (e^{T/2}/2) s` for `0 ≤ s ≤ T` (with `s = |D|²`, `T = n`). -/
theorem gwe_graph_jacobian_bounds : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), 1 ≤ Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ∧ (‖D‖ ≤ 1 → Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D) := by
  intro n ℓ D
  -- Steps 1, 2, 6: the Gram matrix `G` of `D` is symmetric positive semidefinite, `trace G = |D|²`.
  obtain ⟨hsymm, hpsd, htr⟩ := Submission.gwe_gjb_gram_symm_psd_trace n ℓ D
  -- Steps 3, 4, 7: `1 ≤ det(I + G) ≤ exp (trace G) = exp |D|²`.
  obtain ⟨hdet, hdet_le⟩ := Submission.gwe_gjb_det_one_add_bounds n _ hsymm hpsd
  rw [htr] at hdet_le
  refine ⟨?_, fun hD => ?_⟩
  · -- Step 5: `J(D) = √det(I + G) ≥ √1 = 1`.
    exact Real.one_le_sqrt.2 hdet
  · -- Step 9: `0 ≤ |D|² ≤ n ‖D‖² ≤ n`, since `‖D‖ ≤ 1`.
    obtain ⟨h0, hle, -⟩ := (Submission.lgc_hsNormSq_bounds n ℓ).2 D
    have hn : hsNormSq D ≤ n :=
      hle.trans (mul_le_of_le_one_right (Nat.cast_nonneg n) (pow_le_one₀ (norm_nonneg D) hD))
    -- Steps 8, 10, 11: `J(D) ≤ √(exp |D|²) = exp (|D|²/2) ≤ 1 + (e^{n/2}/2) |D|²`.
    calc Real.sqrt _ ≤ Real.sqrt (Real.exp (hsNormSq D)) := Real.sqrt_le_sqrt hdet_le
      _ = Real.exp (hsNormSq D / 2) := (Real.exp_half _).symm
      _ ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D := Submission.gwe_gjb_exp_half_le _ _ h0 hn
/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): graph coordinates on
`ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ` and the projection onto `T₀ = q(ℝⁿ × {0})`, the plane the book takes to be
`ℝⁿ × {0}` without loss of generality. For a linear isometry `q` of `ℝ^{n+ℓ}`:
(i) `(a, b) − (a', b') = (a − a', b − b')`; (ii) `|(a, b)|² = |a|² + |b|²`; (iii) every
`z ∈ ℝ^{n+ℓ}` is some `(a, b)`; (iv) `p_{T₀}(q(a, b)) = q(a, 0)`.
The coordinate of `(a, b)` at `castAdd ℓ i` is `a_i` and at `natAdd n j` is `b_j`, and every index
of `Fin (n + ℓ)` has one of these forms (`Fin.addCases`); this gives (i) and (iii), and (ii) by
splitting `Σ_k z_k²` with `Fin.sum_univ_add`. For (iv), `(a, 0) = Σ_i a_i e_{castAdd ℓ i}` lies in
`ℝⁿ × {0}`, `(0, b)` is orthogonal to every `e_{castAdd ℓ i}` and hence to `ℝⁿ × {0}`, and `q`
preserves inner products; so `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) = q(0, b) ⊥ T₀`, which
characterizes `q(a, 0)` as the orthogonal projection of `q(a, b)` onto `T₀`. -/
theorem lip_approx_graph_coordinates : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b')) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ z : Amb n ℓ, ∃ (a : Rn n) (b : Rn ℓ), z = graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a 0)) := by
  intro n ℓ q
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- (i): subtraction is coordinatewise
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  refine ⟨hsub, ?_, ?_, ?_⟩
  -- (ii): split `‖z‖² = Σ_k ‖z_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- (iii): read off `a` and `b` from the two blocks of coordinates of `z`
  · intro z
    refine ⟨WithLp.toLp 2 (fun i => z (Fin.castAdd ℓ i)),
      WithLp.toLp 2 (fun j => z (Fin.natAdd n j)), ?_⟩
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [hl]
    · rw [hr]
  -- (iv)
  · intro a b
    -- `graphPoint a 0 = Σ_i a_i e_{castAdd ℓ i}` lies in `ℝⁿ × {0}`
    have hmem : graphPoint a 0 ∈ horizontalPlane n ℓ := by
      have e : graphPoint a 0 =
          ∑ i : Fin n, a i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
        ext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [hl]
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
            Pi.smul_apply, Pi.single_apply, Fin.castAdd_inj, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · rw [hr]
          simp only [PiLp.zero_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (Finset.sum_eq_zero fun x _ => ?_).symm
          have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ x := by
            intro h
            have h' := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
            have := x.isLt
            omega
          rw [Pi.single_eq_of_ne hne, mul_zero]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `graphPoint 0 b` is orthogonal to every `e_{castAdd ℓ i}`, hence to `ℝⁿ × {0}`
    have horth : ∀ h ∈ horizontalPlane n ℓ, inner ℝ (graphPoint 0 b) h = 0 := by
      have hle : horizontalPlane n ℓ ≤ (ℝ ∙ graphPoint 0 b)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
          EuclideanSpace.inner_single_right, hl]
        simp
      intro h hh
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hh)
    -- `q(a, 0) ∈ T₀`, and `q(a, b) - q(a, 0) = q(0, b)` is orthogonal to `T₀ = q(ℝⁿ × {0})`
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
    intro w hw
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
    rw [← map_sub, hsub, sub_self, sub_zero]
    exact (q.inner_map_map _ _).trans (horth h hh)
/-- The linear algebra of Simon Ch. 5, proof of Theorem 4.5, displays (7), (10), (11) and (13)
(pp. 118–119). For a linear isometry `q` of `ℝ^{n+ℓ}` and a linear map `D : ℝⁿ → ℝ^ℓ` with
`‖D‖ ≤ 1`, let `p` be the orthogonal projection onto the rotated graph plane
`S = span{q(v, Dv) : v ∈ ℝⁿ}` and `P` the one onto `T = q(ℝⁿ × {0})`. Then
(a) `|D|² ≤ (ℓ + ½)|p − P|²`, and (b) `|⟨p e'_j, p q(w, 0)⟩ − ⟨r, w⟩| ≤ |p − P|² |w|` whenever `r`
is the `j`-th row of `D`, where `e'_j = q(0, ε_j)`.
The horizontal vectors `q(a, 0)` lie in `T`, with `|q(a, 0)| = |a|` and
`⟨q(a, 0), q(b, 0)⟩ = ⟨a, b⟩`. By (7), `p e'_j = p q(r, 0)`, so the projection defect (10)–(11)
on `T` bounds the error in (b) by `|p − P|² |r| |w|`, and `|r| ≤ ‖D‖ ≤ 1`. For (a), the same
bound with `u = w = q(r_j, 0)` gives `|r_j|² ≤ |p e'_j|² + |p − P|²`. Summing over `j` and using
`|D|² = Σ_j |r_j|²` and the trace identity `Σ_j |p e'_j|² = ½|p − P|²` (13), valid because
`dim S = n`, gives (a). -/
theorem gwe_graph_tilt_algebra : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ), ‖D‖ ≤ 1 → hsNormSq D ≤ ((ℓ : ℝ) + 1 / 2) * hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) ∧ ∀ (j : Fin ℓ) (r w : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → |inner ℝ ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint w 0))) - inner ℝ r w| ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) * ‖w‖ := by
  intro n ℓ q D hD
  -- (L4) and (IP) for graph points, and (L5) `P(q(a, b)) = q(a, 0)`
  obtain ⟨-, -, -, -, -, hnorm, hinner⟩ := Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  obtain ⟨hproj, -, -⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- the horizontal vectors `q(a, 0)` lie in `T`, have norm `|a|` and inner products `⟨a, b⟩`
  have hmem : ∀ a : Rn n, q (graphPoint a 0) ∈ rotatedPlane q := fun a =>
    Submodule.starProjection_eq_self_iff.mp (hproj a 0)
  have hnorm0 : ∀ a : Rn n, ‖q (graphPoint a 0)‖ = ‖a‖ := fun a => by
    have h := hnorm a 0
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have hinner0 : ∀ a b : Rn n,
      inner ℝ (q (graphPoint a 0)) (q (graphPoint b 0)) = inner ℝ a b := fun a b => by
    rw [LinearIsometryEquiv.inner_map_map, hinner, inner_zero_left, add_zero]
  -- the rows `R j` of `D`; Simon (7); the trace identity (13) for `S`, of dimension `n`; and the
  -- projection defect (10)–(11) for `S` and `T`
  obtain ⟨hrow, R, hR, hRsum⟩ := Submission.gwe_gta_row_bounds n ℓ D
  have horth := Submission.gwe_gta_graph_row_orthogonal n ℓ q D
  have hvert := Submission.gwe_gta_vertical_trace_sum n ℓ q _
    (Submission.tdo_gpd_graph_plane_finrank n ℓ q D)
  have hdefect := Submission.gwe_gta_proj_inner_defect (n + ℓ)
    (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))) (rotatedPlane q)
  generalize Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))) = S
    at horth hvert hdefect ⊢
  have hE : 0 ≤ hsNormSq (S.starProjection - (rotatedPlane q).starProjection) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  generalize hsNormSq (S.starProjection - (rotatedPlane q).starProjection) = E
    at hvert hdefect hE ⊢
  refine ⟨?_, ?_⟩
  -- (a): `|R j|² ≤ |p e'_j|² + E` for every row, and `Σ_j |p e'_j|² = E / 2`
  · have hj : ∀ j : Fin ℓ, ‖R j‖ ^ 2 ≤
        ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 + E := by
      intro j
      have h := hdefect _ _ (hmem (R j)) (hmem (R j))
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← horth j (R j) (hR j),
        hnorm0] at h
      have h1 : ‖R j‖ ≤ 1 := (hrow j (R j) (hR j)).trans hD
      have h2 : E * (‖R j‖ * ‖R j‖) ≤ E :=
        mul_le_of_le_one_right hE ((mul_le_of_le_one_left (norm_nonneg _) h1).trans h1)
      linarith [(abs_le.mp h).1]
    calc hsNormSq D = ∑ j : Fin ℓ, ‖R j‖ ^ 2 := hRsum.symm
      _ ≤ ∑ j : Fin ℓ,
            (‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 + E) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = E / 2 + ℓ * E := by
          rw [Finset.sum_add_distrib, hvert, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ = ((ℓ : ℝ) + 1 / 2) * E := by ring
  -- (b): by (7), `p e'_j = p q(r, 0)`; then the projection defect and `|r| ≤ ‖D‖ ≤ 1`
  · intro j r w hr
    rw [horth j r hr]
    have h := hdefect _ _ (hmem r) (hmem w)
    rw [hinner0, hnorm0, hnorm0] at h
    have h1 : ‖r‖ ≤ 1 := (hrow j r hr).trans hD
    exact h.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg w) h1) hE)

/-- Simon Ch. 2, 3.5 (area formula) for a rotated Lipschitz graph, as used in the proof of Ch. 5,
Theorem 4.5: if `f` is `K`-Lipschitz on `B_R(0)`, `A ⊆ B_R(0)` is Borel and `q` is a linear isometry
of `ℝ^{n+ℓ}`, then `∫_{q(graph f|A)} g dHⁿ = ∫_A J_f(x) g(q(x, f(x))) dx` for every `g ≥ 0`, where
`J_f = √det(I + (Df eₐ · Df e_b)_{a,b})`. Extend `f` to a globally Lipschitz `f'`; the graph map
`G x = q(x, f' x)` is injective, Lipschitz and does not decrease distances. For linear `D`, the map
`T_D v = q(v, D v)` is an isometry after an endomorphism `W` of `ℝⁿ` with `|det W| = J(D)`, so
`Hⁿ(T_D(s)) = J(D) Lⁿ(s)` (Simon (3.1)) and `J(D) ≥ 1`. Split a set of differentiability points
of `f'` into the cells `tᵐ ≤ J(Df') < tᵐ⁺¹` and these into pieces on which `G` is `δ`-close to
some `T_{Df'(y)}`: there `Hⁿ(G(·))` and `∫ J(Df')` agree up to `t²`. Letting `t → 1` and using
Rademacher, `Hⁿ(G(·)) = J(Df') Lⁿ`, which transfers to integrals along the embedding `G`.
Finally `f = f'` near almost every point of `A`, as the sphere `∂B_R(0)` is null. -/
theorem gwe_lipschitz_graph_area_formula : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ g : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ)) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) * g (q (graphPoint x (f x))) := by
  intro n ℓ hn q f K R hf A hA hAR g
  -- graph coordinates: `(a, b) - (a', b') = (a - a', b - b')`, `|(a, b)|² = |a|² + |b|²`
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  -- `⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`
  have hinner : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b' := by
    intro a a' b b'
    simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  -- `(a, b) ↦ graphPoint a b` is the linear isomorphism `ℝⁿ × ℝ^ℓ ≃ ℝ^{n+ℓ}`
  let Φ := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := ℓ)).symm
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = Φ (a, b) := by
    intro a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [Φ, graphPoint]
    · simp [Φ, graphPoint]
  -- the Jacobian `J(D) = √det(I + (⟨D eₐ, D e_b⟩))` of the graph of a linear map `D`
  obtain ⟨J, hJ⟩ : ∃ J : (Rn n →L[ℝ] Rn ℓ) → ℝ, ∀ D, J D = Real.sqrt (Matrix.det
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) :=
    ⟨_, fun _ => rfl⟩
  have hJcont : Continuous J := by
    rw [show J = _ from funext hJ]
    fun_prop
  -- the graph map `T D : v ↦ q(v, D v)` of a linear map `D`
  obtain ⟨T, hT⟩ : ∃ T : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ),
      ∀ D v, T D v = q (graphPoint v (D v)) :=
    ⟨fun D => (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ) ∘L
      ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ) ∘L ((ContinuousLinearMap.id ℝ (Rn n)).prod D)),
      fun D v => by simp [hgp]⟩
  have hTinner : ∀ D u w, inner ℝ (T D u) (T D w) = inner ℝ u w + inner ℝ (D u) (D w) := by
    intro D u w
    rw [hT, hT, LinearIsometryEquiv.inner_map_map, hinner]
  have hTnorm : ∀ D v, ‖v‖ ≤ ‖T D v‖ := by
    intro D v
    have h := hTinner D v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖D v‖])
  have hTinj : ∀ D, Function.Injective (T D) := by
    intro D x y hxy
    have h := hTnorm D (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- Simon (3.1), linear area formula: `Hⁿ(T D (s)) = J(D) Lⁿ(s)`
  have hlin : ∀ D (s : Set (Rn n)),
      (μHE[n] : Measure (Amb n ℓ)) (T D '' s) = ENNReal.ofReal (J D) * volume s := by
    intro D s
    have hTinj' : Function.Injective (T D : Rn n →ₗ[ℝ] Amb n ℓ) := hTinj D
    set V : Submodule ℝ (Amb n ℓ) := LinearMap.range (T D : Rn n →ₗ[ℝ] Amb n ℓ) with hVdef
    have hV : Module.finrank ℝ V = n := by
      rw [hVdef, LinearMap.finrank_range_of_inj hTinj', finrank_euclideanSpace_fin]
    set bV : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
    -- `T D = ι ∘ W` with `ι` a linear isometry and `W` an endomorphism of `ℝⁿ`
    set W : Rn n →ₗ[ℝ] Rn n := (bV.repr.toLinearEquiv : V →ₗ[ℝ] Rn n) ∘ₗ
      (T D : Rn n →ₗ[ℝ] Amb n ℓ).rangeRestrict
    set ι : Rn n →ₗᵢ[ℝ] Amb n ℓ := V.subtypeₗᵢ.comp bV.repr.symm.toLinearIsometry
    have hιW : ∀ v, ι (W v) = T D v := by
      intro v
      simp [ι, W]
    have himage : T D '' s = ι '' (W '' s) := by
      rw [Set.image_image]
      exact Set.image_congr fun v _ => (hιW v).symm
    rw [himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    congr 2
    -- `|det W| = √det(Wᵀ W)` and `Wᵀ W = I + (⟨D eₐ, D e_b⟩)`
    set M := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis W with hM
    have hWinner : ∀ u w, inner ℝ (W u) (W w) = inner ℝ (T D u) (T D w) := by
      intro u w
      rw [← hιW, ← hιW, LinearIsometry.inner_map_map]
    have hgram : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of (fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) =
        M.transpose * M := by
      ext a b
      have h1 := hWinner (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ))
      rw [hTinner, EuclideanSpace.inner_single_left, PiLp.inner_apply] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hM, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis,
        PiLp.basisFun_apply, PiLp.basisFun_repr]
      simp only [map_one, one_mul, PiLp.ofLp_single, Pi.single_apply, RCLike.inner_apply,
        conj_trivial] at h1
      rw [Finset.sum_congr rfl (fun x _ => mul_comm _ _), h1]
    rw [hJ, hgram, Matrix.det_mul, Matrix.det_transpose, hM, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- comparison of image measures through a pairwise distance bound
  have hcomp : ∀ (φ ψ : Rn n → Amb n ℓ) (s : Set (Rn n)) (c : ℝ≥0), Set.InjOn ψ s →
      (∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) ≤ c * dist (ψ x) (ψ y)) →
      (μHE[n] : Measure (Amb n ℓ)) (φ '' s) ≤ (c : ℝ≥0∞) ^ n * μHE[n] (ψ '' s) := by
    intro φ ψ s c hψ hd
    have hh : LipschitzOnWith c (φ ∘ Function.invFunOn ψ s) (ψ '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy]
        using hd x hx y hy
    have himage : (φ ∘ Function.invFunOn ψ s) '' (ψ '' s) = φ '' s := by
      rw [Set.image_comp, hψ.invFunOn_image Set.Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  -- `J(D) ≥ 1`: `T D` does not decrease distances
  have hJ1 : ∀ D, 1 ≤ J D := by
    intro D
    have hiso : Isometry (fun v : Rn n => q (graphPoint v 0)) := by
      refine Isometry.of_dist_eq fun x y => ?_
      have h := hnorm (x - y) 0
      rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_zero]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
    have hB := hcomp (fun v => q (graphPoint v 0)) (T D) (closedBall 0 1) 1 (hTinj D).injOn
      (fun x _ y _ => by
        rw [hiso.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
        exact hTnorm D (x - y))
    rw [hiso.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hlin, ENNReal.coe_one, one_pow, one_mul] at hB
    have hpos : volume (closedBall (0 : Rn n) 1) ≠ 0 :=
      (measure_closedBall_pos volume 0 one_pos).ne'
    have hfin : volume (closedBall (0 : Rn n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
    exact ENNReal.one_le_ofReal.mp
      ((ENNReal.mul_le_mul_iff_left hpos hfin).mp (by rwa [one_mul]))
  -- Step 1: extend `f` from `B_R(0)` to a globally Lipschitz map `f'`
  obtain ⟨f', hf'L, hf'eq⟩ := hf.extend_finite_dimension
  -- Step 2: the graph map `G x = q(x, f' x)` is Lipschitz, injective, and expands distances
  obtain ⟨G, hG⟩ : ∃ G : Rn n → Amb n ℓ, ∀ x, G x = q (graphPoint x (f' x)) :=
    ⟨_, fun _ => rfl⟩
  have hGL : LipschitzWith (1 * (‖(Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ)‖₊ *
      max 1 (lipschitzExtensionConstant (Rn ℓ) * K))) G := by
    have h := q.lipschitzWith.comp ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).lipschitzWith.comp
      (LipschitzWith.id.prodMk hf'L))
    convert h using 1
    funext x
    simp [hG, hgp]
  have hGdist : ∀ x y, dist x y ≤ dist (G x) (G y) := by
    intro x y
    have h := hnorm (x - y) (f' x - f' y)
    rw [dist_eq_norm, dist_eq_norm, hG, hG, ← map_sub, LinearIsometryEquiv.norm_map, hsub]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [h]; nlinarith [sq_nonneg ‖f' x - f' y‖])
  have hGinj : Function.Injective G := by
    intro x y hxy
    have h := hGdist x y
    rw [hxy, dist_self] at h
    exact dist_le_zero.mp h
  have hGemb : MeasurableEmbedding G := hGL.continuous.measurableEmbedding hGinj
  -- at a differentiability point of `f'`, `DG(x) v = q(v, Df'(x) v)`
  have hGd : ∀ x, DifferentiableAt ℝ f' x → HasFDerivAt G (T (fderiv ℝ f' x)) x := by
    intro x hdx
    have h1 : HasFDerivAt (fun y => (y, f' y))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f' x)) x :=
      (hasFDerivAt_id x).prodMk hdx.hasFDerivAt
    have h2 := (Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h1
    have h3 := (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h2
    convert h3 using 1
    · funext y
      simp [hG, hgp]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [hT, hgp]
  -- Step 3: the measures `ν(s) = Hⁿ(G(s))` and `ρ = J(Df') Lⁿ` on `ℝⁿ`
  set ν : Measure (Rn n) := Measure.comap G (μHE[n] : Measure (Amb n ℓ)) with hνdef
  have hν : ∀ s, ν s = (μHE[n] : Measure (Amb n ℓ)) (G '' s) := fun s =>
    hGemb.comap_apply _ s
  have hJm : Measurable fun x => J (fderiv ℝ f' x) :=
    hJcont.measurable.comp (measurable_fderiv ℝ f')
  have hjmeas : Measurable fun x => ENNReal.ofReal (J (fderiv ℝ f' x)) :=
    ENNReal.measurable_ofReal.comp hJm
  set ρ : Measure (Rn n) := (volume : Measure (Rn n)).withDensity
    (fun x => ENNReal.ofReal (J (fderiv ℝ f' x))) with hρdef
  have hρ : ∀ s, MeasurableSet s →
      ρ s = ∫⁻ x in s, ENNReal.ofReal (J (fderiv ℝ f' x)) := fun s hs =>
    withDensity_apply _ hs
  -- countable additivity transfers a ratio bound from a partition to its union
  have hsum : ∀ (μ₁ μ₂ : Measure (Rn n)) (c : ℝ≥0∞) (B : Set (Rn n)) (P : ℕ → Set (Rn n)),
      (∀ k, MeasurableSet (P k)) → Pairwise (Function.onFun Disjoint P) → B = ⋃ k, P k →
      (∀ k, μ₁ (P k) ≤ c * μ₂ (P k)) → μ₁ B ≤ c * μ₂ B := by
    intro μ₁ μ₂ c B P hPm hPd hB hle
    rw [hB, measure_iUnion hPd hPm, measure_iUnion hPd hPm, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hle
  -- Step 4: `ν ≤ t² ρ` and `ρ ≤ t² ν` on measurable sets of differentiability points, `t > 1`
  have hDmeas : MeasurableSet {x : Rn n | DifferentiableAt ℝ f' x} :=
    measurableSet_of_differentiableAt ℝ f'
  have hpiece : ∀ t : ℝ≥0, 1 < t → ∀ B, MeasurableSet B →
      B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} →
      ν B ≤ (t : ℝ≥0∞) ^ 2 * ρ B ∧ ρ B ≤ (t : ℝ≥0∞) ^ 2 * ν B := by
    intro t ht B hB hBD
    have ht' : (1 : ℝ) < t := by exact_mod_cast ht
    -- an approximation error `δ` with `(1 + δ)ⁿ ≤ t` and `(1 - δ)⁻ⁿ ≤ t`
    obtain ⟨δ, hδpos, hδ1, hδup, hδlow⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
        ((1 - δ)⁻¹) ^ n < t := by
      have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ < 1 := eventually_lt_nhds zero_lt_one
      have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ) ^ n < t :=
        ((continuousAt_const.add continuousAt_id).pow _).eventually_lt continuousAt_const
          (by simpa using ht)
      have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ)⁻¹) ^ n < t := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using ht)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub continuousAt_id
        · simp
      have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
          ((1 - δ)⁻¹) ^ n < t := by
        filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
          hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds]
          with δ h1 h2 h3 h4
        exact ⟨h1, h2, h3, h4⟩
      exact hevent.exists
    have hup : ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδup.le
    have hlow : (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlow.le
    have hpow : ∀ m : ℕ, ENNReal.ofReal ((t : ℝ) ^ m) = (t : ℝ≥0∞) ^ m := by
      intro m
      rw [ENNReal.ofReal_pow (NNReal.coe_nonneg t), ENNReal.ofReal_coe_nnreal]
    -- the cells `C m = {x ∈ B : tᵐ ≤ J(Df'(x)) < tᵐ⁺¹}` (recall `J ≥ 1`)
    obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (Rn n), ∀ m, C m = B ∩ {x | (t : ℝ) ^ m ≤ J (fderiv ℝ f' x) ∧
        J (fderiv ℝ f' x) < (t : ℝ) ^ (m + 1)} := ⟨_, fun _ => rfl⟩
    have hCmeas : ∀ m, MeasurableSet (C m) := fun m => by
      rw [hC]
      exact hB.inter ((measurableSet_le measurable_const hJm).inter
        (measurableSet_lt hJm measurable_const))
    have hCdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m m' hmm'
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rw [hC] at hx hx'
      have e1 : m < m' + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx.2.1.trans_lt hx'.2.2)
      have e2 : m' < m + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx'.2.1.trans_lt hx.2.2)
      exact hmm' (by omega)
    have hCcover : B = ⋃ m, C m := by
      ext x
      simp only [mem_iUnion, hC, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_pow_near (hJ1 (fderiv ℝ f' x)) ht'
        exact ⟨m, hx, hm⟩
      · rintro ⟨m, hx, -⟩
        exact hx
    have hcell : ∀ m, ν (C m) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m) ∧
        ρ (C m) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m) := by
      intro m
      rcases (C m).eq_empty_or_nonempty with hempty | hne
      · simp [hempty]
      have hCD : C m ⊆ {x : Rn n | DifferentiableAt ℝ f' x} := fun x hx => by
        rw [hC] at hx
        exact hBD hx.1
      -- pieces of `C m` on which `G` is `δ`-close to `T(Df'(y))` for some `y ∈ C m`
      obtain ⟨P, L, hPdisj, hPmeas, hPcover, hPapprox, hPL⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G (C m)
          (fun x => T (fderiv ℝ f' x))
          (fun x hx => (hGd x (hCD hx)).hasFDerivWithinAt) (fun _ => δ) (fun _ => hδpos.ne')
      have hQmeas : ∀ k, MeasurableSet (C m ∩ P k) := fun k => (hCmeas m).inter (hPmeas k)
      have hQdisj : Pairwise (Function.onFun Disjoint fun k => C m ∩ P k) := fun i j hij =>
        (hPdisj hij).mono inter_subset_right inter_subset_right
      have hQcover : C m = ⋃ k, C m ∩ P k := by
        rw [← inter_iUnion]
        exact (inter_eq_left.2 hPcover).symm
      have hpc : ∀ k, ν (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) ∧
          ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by
        intro k
        obtain ⟨y, hy, hLy⟩ := hPL hne k
        have hQ : ApproximatesLinearOn G (T (fderiv ℝ f' y)) (C m ∩ P k) δ := by
          have h := hPapprox k
          rwa [hLy] at h
        rw [hC] at hy
        have hJy1 : (t : ℝ≥0∞) ^ m ≤ ENNReal.ofReal (J (fderiv ℝ f' y)) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.1
        have hJy2 : ENNReal.ofReal (J (fderiv ℝ f' y)) ≤ (t : ℝ≥0∞) ^ (m + 1) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.2.le
        have hρlow : (t : ℝ≥0∞) ^ m * volume (C m ∩ P k) ≤ ρ (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono hjmeas fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.1
        have hρup : ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono measurable_const fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.2.le
        -- `G` and `T(Df'(y))` have comparable distances on the piece
        have hd1 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k, dist (G x) (G z) ≤
            ((1 + δ : ℝ≥0) : ℝ) * dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) := by
          intro x hx z hz
          have happ := hQ x hx z hz
          have hl := hTnorm (fderiv ℝ f' y) (x - z)
          rw [map_sub] at happ hl
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
          calc ‖G x - G z‖ ≤ ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := norm_le_norm_sub_add _ _
            _ ≤ δ * ‖x - z‖ + ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ ≤ δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ = (1 + δ) * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by ring
        have hd2 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k,
            dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) ≤
              (((1 - δ)⁻¹ : ℝ≥0) : ℝ) * dist (G x) (G z) := by
          intro x hx z hz
          have happ : ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ ≤
              δ * ‖x - z‖ := by
            simpa only [map_sub] using hQ x hx z hz
          have hl : ‖x - z‖ ≤ ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by
            simpa only [map_sub] using hTnorm (fderiv ℝ f' y) (x - z)
          have hδR : (δ : ℝ) < 1 := by exact_mod_cast hδ1
          have htri : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ := by
            have h := norm_sub_le (G x - G z)
              (G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z))
            rwa [sub_sub_cancel] at h
          have hm := mul_le_mul_of_nonneg_left hl (NNReal.coe_nonneg δ)
          have key : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by linarith
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ1.le, NNReal.coe_one,
            inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR), mul_sub, mul_one, mul_comm]
          linarith
        constructor
        · calc ν (C m ∩ P k) = μHE[n] (G '' (C m ∩ P k)) := hν _
            _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) :=
              hcomp G _ _ _ (hTinj _).injOn hd1
            _ = ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n *
                (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k)) := by gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) := by gcongr
        · calc ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := hρup
            _ = (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) * (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              gcongr
            _ = (t : ℝ≥0∞) * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) := by rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (G '' (C m ∩ P k))) := by
              gcongr
              exact hcomp _ G _ _ hGinj.injOn hd2
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) * ν (C m ∩ P k)) := by
              rw [hν]
              gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by ring
      exact ⟨hsum ν ρ _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).1,
        hsum ρ ν _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).2⟩
    exact ⟨hsum ν ρ _ B C hCmeas hCdisj hCcover fun m => (hcell m).1,
      hsum ρ ν _ B C hCmeas hCdisj hCcover fun m => (hcell m).2⟩
  -- Step 5: letting `t → 1`, `ν = ρ` on sets of differentiability points
  have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
    intro a
    have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
      (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [one_pow, one_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
  have hD : ∀ B, MeasurableSet B → B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} → ν B = ρ B := by
    intro B hB hBD
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).2
  -- Step 6: `ν = ρ`, as both vanish on the null set of nondifferentiability points (Rademacher)
  have hDnull : volume {x : Rn n | ¬ DifferentiableAt ℝ f' x} = 0 :=
    ae_iff.mp hf'L.ae_differentiableAt
  have hmain : ν = ρ := by
    ext B hB
    have h1 : ν (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 := by
      rw [hν]
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hGL.lipschitzOnWith (s := B \ {x : Rn n | DifferentiableAt ℝ f' x}))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        measure_mono_null (fun x hx => hx.2) hDnull, mul_zero] at h
      exact le_zero_iff.mp h
    have h2 : ρ (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null (fun x hx => hx.2) hDnull)
    rw [← measure_inter_add_sdiff B hDmeas, ← measure_inter_add_sdiff (μ := ρ) B hDmeas, h1, h2,
      hD _ (hB.inter hDmeas) inter_subset_right]
  -- Step 7: transfer the integral along the measurable embedding `G`
  have himg : q '' graphOver f A = G '' A := by
    rw [graphOver, Set.image_image]
    refine Set.image_congr fun x hx => ?_
    rw [hG, hf'eq (hAR hx)]
  have hGA : MeasurableSet (G '' A) := hGemb.measurableSet_image' hA
  have hpres : MeasurePreserving G ν ((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) :=
    ⟨hGemb.measurable, hGemb.map_comap _⟩
  calc ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ))
      = ∫⁻ y in G '' A, g y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) := by
        rw [himg, Measure.restrict_restrict hGA, inter_eq_left.2 (image_subset_range G A)]
    _ = ∫⁻ x in A, g (G x) ∂ν := (hpres.setLIntegral_comp_emb hGemb g A).symm
    _ = ∫⁻ x in A, g (G x) ∂ρ := by rw [hmain]
    _ = ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ f' x)) * g (G x) := by
        rw [hρdef, restrict_withDensity hA,
          lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hjmeas.aemeasurable
            (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ = _ := by
        -- a.e. on `A`, `x` is interior to `B_R(0)`, where `f = f'`
        refine setLIntegral_congr_fun_ae hA ?_
        have hnt : Nontrivial (Rn n) := by
          have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
          infer_instance
        have hsph : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∉ sphere (0 : Rn n) R :=
          measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 R)
        filter_upwards [hsph] with x hxs hxA
        have hxb : x ∈ ball (0 : Rn n) R := by
          have h1 := hAR hxA
          rw [mem_closedBall] at h1
          rw [mem_sphere] at hxs
          exact mem_ball.mpr (lt_of_le_of_ne h1 hxs)
        have hev : f =ᶠ[𝓝 x] f' :=
          Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxb) fun y hy =>
            hf'eq (ball_subset_closedBall hy)
        rw [hJ, hG, hev.fderiv_eq, hf'eq (hAR hxA)]
/-- **Pull-back of the varifold weight to the parameter domain of a 1-Lipschitz graph** (the
transfer step "from (12), (13) and the area formula" in the proof of Simon Ch. 5, 4.5).  With
`F(x) = q(x, f(x))`, `J = J_f` and `B = B_R(0)`, the weight `μ_V` restricted to `F(A)` has the Borel
density `W = J · g₂ ∘ F̂` over Borel `A ⊆ B`, where `g₂ ≥ 0` is a Borel version of `1_M θ`
(`gwe_vgt_weight_density`) and `F̂` a Borel version of `F` (`gwe_vgt_graph_measurability`).

Proof: `J ≥ 1` (`gwe_graph_jacobian_bounds`), so the area formula
(`gwe_lipschitz_graph_area_formula`, `K = 1`, `g = 1`) gives `Lⁿ(B') ≤ Hⁿ(F(B'))` for Borel
`B' ⊆ B`; hence `F` pulls `Hⁿ`-null sets back to `Lⁿ`-null subsets of `B`, and
`g₂(F̂ x) = 1_M θ (F x)` for a.e. `x ∈ B`, which is (c).  For (a),
`∫_{F(A)} φ dμ_V = ∫_{F(A)} 1_M θ φ dHⁿ = ∫_A J (1_M θ ∘ F) (φ ∘ F) dLⁿ` and the a.e. identity.
(b) and (d) follow from (a) with `F̂ = F` on `A` (`gwe_vgt_transfer_consequences`, `G = F̂`). -/
theorem gwe_varifold_graph_transfer : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), LipschitzOnWith 1 f (closedBall 0 R) → ∃ W : Rn n → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, φ y ∂V.weight = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (q (graphPoint x (f x)))) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in q '' graphOver f A, φ y ∂V.weight = ∫ x in A, W x * φ (q (graphPoint x (f x)))) ∧ (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 R → W x = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ))))) * V.carrier.indicator V.mult (q (graphPoint x (f x)))) ∧ ∀ Z : Set (Amb n ℓ), V.weight Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R → q (graphPoint x (f x)) ∈ Z → W x = 0 := by
  intro n ℓ hn U V q f R hf
  -- The graph Jacobian `J = J_f`; `J ≥ 1` by JB (i) with `D = Df(x)`.
  obtain ⟨J, hJ⟩ : ∃ J : Rn n → ℝ, ∀ x, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ))))) = J x :=
    ⟨_, fun _ => rfl⟩
  have hJ1 : ∀ x, 1 ≤ J x := fun x => by
    rw [← hJ x]
    exact (Submission.gwe_graph_jacobian_bounds n ℓ (fderiv ℝ f x)).1
  have hJ0 : ∀ x, 0 ≤ J x := fun x => zero_le_one.trans (hJ1 x)
  -- (P2)-(P4): `F(A)` is Borel, `F̂` is a Borel version of `F` on `B`, and `J` is Borel.
  obtain ⟨hFA, ⟨Fh, hFh, hFhF⟩, hJm⟩ :=
    Submission.gwe_vgt_graph_measurability n ℓ q f R hf.continuousOn
  simp only [hJ] at hJm
  -- AREA with `K = 1`.
  have harea := Submission.gwe_lipschitz_graph_area_formula n ℓ hn q f 1 R hf
  simp only [hJ] at harea
  -- (P5): `Lⁿ(B') ≤ Hⁿ(F(B'))` for Borel `B' ⊆ B`.
  have hP5 : ∀ B' : Set (Rn n), MeasurableSet B' → B' ⊆ closedBall 0 R →
      volume B' ≤ (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f B') := by
    intro B' hB' hB'R
    calc volume B' = ∫⁻ _ in B', 1 := (setLIntegral_one B').symm
      _ ≤ ∫⁻ x in B', ENNReal.ofReal (J x) * 1 := setLIntegral_mono' hB' fun x _ => by
          rw [mul_one]
          exact ENNReal.one_le_ofReal.2 (hJ1 x)
      _ = ∫⁻ _ in q '' graphOver f B', 1 ∂(μHE[n] : Measure (Amb n ℓ)) :=
          (harea B' hB' hB'R fun _ => 1).symm
      _ = (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f B') := setLIntegral_one _
  -- (P6): `F` pulls `Hⁿ`-null sets back to `Lⁿ`-null subsets of `B`.
  have hP6 : ∀ Y : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) Y = 0 →
      ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R → q (graphPoint x (f x)) ∉ Y := by
    intro Y hY
    obtain ⟨Y', hYY', hY'm, hY'0⟩ := exists_measurable_superset_of_null hY
    have hB'm : MeasurableSet (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y') :=
      measurableSet_closedBall.inter (hFh hY'm)
    have hB'0 : volume (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y') = 0 := by
      refine le_antisymm ?_ zero_le
      calc volume (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y')
          ≤ (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f (closedBall 0 R ∩ Fh ⁻¹' Y')) :=
            hP5 _ hB'm inter_subset_left
        _ ≤ (μHE[n] : Measure (Amb n ℓ)) Y' := by
            refine measure_mono ?_
            rintro _ ⟨_, ⟨x, ⟨hxB, hxY'⟩, rfl⟩, rfl⟩
            rw [mem_preimage, hFhF x hxB] at hxY'
            exact hxY'
        _ = 0 := hY'0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hB'0] with x hx hxB hxY
    exact hx ⟨hxB, by rw [mem_preimage, hFhF x hxB]; exact hYY' hxY⟩
  -- Step 1: a Borel version `g₂ ≥ 0` of `1_M θ`, and (*) `g₂ ∘ F̂ = 1_M θ ∘ F` a.e. on `B`.
  obtain ⟨⟨g₂, hg₂m, hg₂0, hg₂⟩, hdens⟩ := Submission.gwe_vgt_weight_density n ℓ U V
  have hstar : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R →
      g₂ (Fh x) = V.carrier.indicator V.mult (q (graphPoint x (f x))) := by
    filter_upwards [hP6 _ (ae_iff.1 hg₂)] with x hx hxB
    rw [hFhF x hxB]
    by_contra h
    exact hx hxB h
  -- Step 2: `W = J · g₂ ∘ F̂`.
  have hWm : Measurable fun x => J x * g₂ (Fh x) := hJm.mul (hg₂m.comp hFh)
  have hW0 : ∀ x, 0 ≤ J x * g₂ (Fh x) := fun x => mul_nonneg (hJ0 x) (hg₂0 _)
  -- (a): the density of `μ_V`, AREA applied to `1_M θ φ`, and (*).
  have ha : ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ≥0∞,
      ∫⁻ y in q '' graphOver f A, φ y ∂V.weight =
        ∫⁻ x in A, ENNReal.ofReal (J x * g₂ (Fh x)) * φ (q (graphPoint x (f x))) := by
    intro A hA hAR φ
    rw [hdens _ (hFA A hA hAR) φ, harea A hA hAR]
    refine setLIntegral_congr_fun_ae hA ?_
    filter_upwards [hstar] with x hx hxA
    rw [hx (hAR hxA), ENNReal.ofReal_mul (hJ0 x), mul_assoc]
  -- (b) and (d): `gwe_vgt_transfer_consequences` with `G = F̂`, which equals `F` on `A ⊆ B`.
  have htr := fun (A : Set (Rn n)) (hA : MeasurableSet A) (hAR : A ⊆ closedBall 0 R) =>
    Submission.gwe_vgt_transfer_consequences n ℓ V.weight (q '' graphOver f A) A Fh
      (fun x => J x * g₂ (Fh x)) hA hFh hWm hW0 fun φ _ => by
        rw [ha A hA hAR φ]
        exact setLIntegral_congr_fun hA fun x hx => by simp only [hFhF x (hAR hx)]
  refine ⟨fun x => J x * g₂ (Fh x), hWm, hW0, ha, ?_, ?_, ?_⟩
  · intro A hA hAR φ hφ
    rw [(htr A hA hAR).1 φ hφ]
    exact setIntegral_congr_fun hA fun x hx => by simp only [hFhF x (hAR hx)]
  · filter_upwards [hstar] with x hx hxR
    show J x * g₂ (Fh x) = _
    rw [hJ x, hx (ball_subset_closedBall hxR)]
  · intro Z hZ
    filter_upwards [(htr (closedBall 0 R) measurableSet_closedBall subset_rfl).2 Z hZ]
      with x hx hxB hxZ
    exact hx hxB (by rw [hFhF x hxB]; exact hxZ)
/-- The linear algebra of Simon Ch. 5, proof of Theorem 4.5, displays (7), (10), (11) and (13)
(pp. 118–119). For a linear isometry `q` of `ℝ^{n+ℓ}` and a linear map `D : ℝⁿ → ℝ^ℓ` with
`‖D‖ ≤ 1`, let `p` be the orthogonal projection onto the rotated graph plane
`S = span{q(v, Dv) : v ∈ ℝⁿ}` and `P` the one onto `T = q(ℝⁿ × {0})`. Then
(a) `|D|² ≤ (ℓ + ½)|p − P|²`, and (b) `|⟨p e'_j, p q(w, 0)⟩ − ⟨r, w⟩| ≤ |p − P|² |w|` whenever `r`
is the `j`-th row of `D`, where `e'_j = q(0, ε_j)`.
The horizontal vectors `q(a, 0)` lie in `T`, with `|q(a, 0)| = |a|` and
`⟨q(a, 0), q(b, 0)⟩ = ⟨a, b⟩`. By (7), `p e'_j = p q(r, 0)`, so the projection defect (10)–(11)
on `T` bounds the error in (b) by `|p − P|² |r| |w|`, and `|r| ≤ ‖D‖ ≤ 1`. For (a), the same
bound with `u = w = q(r_j, 0)` gives `|r_j|² ≤ |p e'_j|² + |p − P|²`. Summing over `j` and using
`|D|² = Σ_j |r_j|²` and the trace identity `Σ_j |p e'_j|² = ½|p − P|²` (13), valid because
`dim S = n`, gives (a). -/
theorem gwe_graph_tilt_algebra : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ), ‖D‖ ≤ 1 → hsNormSq D ≤ ((ℓ : ℝ) + 1 / 2) * hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) ∧ ∀ (j : Fin ℓ) (r w : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → |inner ℝ ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint w 0))) - inner ℝ r w| ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) * ‖w‖ := by
  intro n ℓ q D hD
  -- (L4) and (IP) for graph points, and (L5) `P(q(a, b)) = q(a, 0)`
  obtain ⟨-, -, -, -, -, hnorm, hinner⟩ := Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  obtain ⟨hproj, -, -⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- the horizontal vectors `q(a, 0)` lie in `T`, have norm `|a|` and inner products `⟨a, b⟩`
  have hmem : ∀ a : Rn n, q (graphPoint a 0) ∈ rotatedPlane q := fun a =>
    Submodule.starProjection_eq_self_iff.mp (hproj a 0)
  have hnorm0 : ∀ a : Rn n, ‖q (graphPoint a 0)‖ = ‖a‖ := fun a => by
    have h := hnorm a 0
/-- Simon Ch. 5, proof of Theorem 4.5, step (1a): the weight `μ_V = (Hⁿ ⌞ M) ⌞ θ` of a
rectifiable varifold is concentrated on `spt V = U ∩ spt μ_V`. The support of a measure on the
second countable space `ℝ^{n+ℓ}` is conull (`Measure.support_mem_ae`), and `μ_V ≪ Hⁿ ⌞ M`
(`withDensity_absolutelyContinuous`), where `Hⁿ ⌞ M` is concentrated on the `Hⁿ`-null-measurable
carrier `M ⊆ U` (`ae_restrict_mem₀`). -/
theorem tdo_ghe_ae_mem_support : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), ∀ᵐ x ∂V.weight, x ∈ V.support := by
  intro n ℓ U V
  -- `μ_V`-a.e. point lies in `spt μ_V`
  have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
  -- `μ_V`-a.e. point lies in `M`, since `Hⁿ ⌞ M`-a.e. point does and `μ_V ≪ Hⁿ ⌞ M`
  have h2 : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨V.carrier_subset hx2, hx1⟩
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the profile of the cutoff `ζ(x) = φ(|x − ξ|/ρ)` with
`ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B_ρ(ξ)` and `|∇ζ| ≤ 3/ρ`.  With `S = smoothTransition`,
the bump `g(t) = S(12(t − 1/2)) S(12(1 − t)) ∈ [0, 1]` vanishes for `t ≤ 1/2` and for `t ≥ 1` and
equals `1` on `[7/12, 11/12]`, so `c = ∫_{1/2}^1 g ≥ 1/3`; then `φ(t) = 1 − c⁻¹ ∫_{1/2}^t g` is
`C^∞` with `|φ'| = c⁻¹ g ≤ 3`. -/
theorem exists_smooth_step_profile_lipschitz_three : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
  -- The bump `g`: smooth, with values in `[0, 1]`, zero off `(1/2, 1)`, one on `[7/12, 11/12]`.
  set g : ℝ → ℝ := fun t =>
    Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
    have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg_cont.intervalIntegrable a b
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
      (Real.smoothTransition.le_one _)
  have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
  have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
    simp only [hg_def]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  -- The normalizing constant `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`.
  set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
  have hc_ge : 1 / 3 ≤ c := by
    have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        norm_num
      · intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        exact hg_mid s hs.1 hs.2
    rw [← h]
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (ae_of_all _ hg_nonneg) (hg_int _ _)
  have hc_pos : 0 < c := by linarith
  have hcinv_le : c⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hc_pos (by norm_num)]
    linarith
  -- The primitive `F(t) = ∫_{1/2}^t g`: `F' = g` (FTC), so `F` is smooth; `0 ≤ F ≤ c`,
  -- `F = 0` on `(-∞, 1/2]` and `F = c` on `[1, ∞)`.
  set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
    (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
      (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
  have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
    simp only [hF_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hg_left s hs.2
  have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
    simp only [hF_def, hc_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
    have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_le ht] at hs
        exact hg_right s hs.1
    rw [h, add_zero]
  have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hF_left t ht]
      exact ⟨le_rfl, hc_pos.le⟩
    rcases le_total 1 t with ht' | ht'
    · rw [hF_right t ht']
      exact ⟨hc_pos.le, le_rfl⟩
    exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
      intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
  -- The profile `φ = 1 − c⁻¹ F`, with `φ' = −c⁻¹ g`.
  have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
    simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
  refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h₀, h₁⟩ := hF_bounds t
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
    have h : c⁻¹ * F t ≤ 1 := by
      calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
        _ = 1 := inv_mul_cancel₀ hc_pos.ne'
    exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
  · intro t ht
    simp only [hF_left t ht, mul_zero, sub_zero]
  · intro t ht
    simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
  · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
    rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
    calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
      _ ≤ 3 := by rw [mul_one]; exact hcinv_le
      _ = ((3 : ℝ≥0) : ℝ) := by norm_num
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), smoothness of the cutoff: if `φ` is `C^∞` with
`φ ≡ 1` on `(-∞, 1/2]` and `ρ > 0`, then `ζ(x) = φ(‖x − ξ‖/ρ)` is `C^∞` on `ℝᵐ`.  Near `ξ`,
`ζ ≡ 1` on `B̆_{ρ/2}(ξ)`; at `x ≠ ξ` the norm is `C^∞` at `x − ξ ≠ 0`. -/
theorem contDiff_radial_profile_of_eq_one_le_half : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (φ : ℝ → ℝ), 0 < ρ → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ t, t ≤ 1 / 2 → φ t = 1) → ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn m => φ (‖x - ξ‖ / ρ)) := by
  intro m ξ ρ φ hρ hφ hφ1
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x ξ with rfl | hx
  · -- `ζ ≡ 1` on the open ball `B̆_{ρ/2}(ξ)`, a neighbourhood of `ξ`.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds x (half_pos hρ)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hφ1 _ ((div_le_iff₀ hρ).2 (by linarith))
  · -- `y ↦ ‖y − ξ‖/ρ` is `C^∞` at `x` since `x − ξ ≠ 0`; compose with `φ`.
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Rn m => ‖y - ξ‖ / ρ) x :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const ρ
    exact hφ.contDiffAt.comp x h
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff gradient bound `|∇ζ| ≤ 3/ρ`, for a general
Lipschitz constant `K` in place of `3`.  If `φ` is `K`-Lipschitz and `ρ > 0`, then
`ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality, so
`‖Dζ(x)‖ ≤ K/ρ` at every `x` (where `ζ` is not differentiable, `fderiv ℝ ζ x = 0`). -/
theorem norm_fderiv_radial_profile_le_of_lipschitzWith : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (K : ℝ≥0) (φ : ℝ → ℝ), 0 < ρ → LipschitzWith K φ → ∀ x : Rn m, ‖fderiv ℝ (fun y : Rn m => φ (‖y - ξ‖ / ρ)) x‖ ≤ (K : ℝ) / ρ := by
  intro m ξ ρ K φ hρ hφ x
  -- `ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality.
  have hKρ : ((K / ρ.toNNReal : ℝ≥0) : ℝ) = K / ρ := by
    rw [NNReal.coe_div, Real.coe_toNNReal ρ hρ.le]
  have hlip : LipschitzWith (K / ρ.toNNReal) fun y : Rn m => φ (‖y - ξ‖ / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKρ]
    calc dist (φ (‖y - ξ‖ / ρ)) (φ (‖z - ξ‖ / ρ))
        ≤ K * dist (‖y - ξ‖ / ρ) (‖z - ξ‖ / ρ) := hφ.dist_le_mul _ _
      _ = K / ρ * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]; ring
      _ ≤ K / ρ * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = K / ρ * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- A `C`-Lipschitz function has `‖Dζ(x)‖ ≤ C` (and `fderiv ℝ ζ x = 0` where not differentiable).
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq hKρ
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): a cutoff `ζ ∈ C^∞(ℝᵐ)` with `0 ≤ ζ ≤ 1`, `ζ ≡ 1` on
`B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B̆_ρ(ξ)` and `|Dζ| ≤ 3/ρ`.  Take `ζ(x) = φ(|x − ξ|/ρ)` for the smooth
`3`-Lipschitz step profile `φ` (`φ = 1` on `(-∞, 1/2]`, `φ = 0` on `[1, ∞)`): `ζ` is smooth since it
is constant near `ξ`, and the radial lift of a `3`-Lipschitz profile has `|Dζ| ≤ 3/ρ`. -/
theorem exists_smooth_cutoff_half_ball_grad_le : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Metric.closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ :=
    Submission.exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    Submission.contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ_smooth hφ_one,
    fun x => hφ_bounds _, fun x hx => hφ_one _ ?_, fun x hx => hφ_zero _ ?_, fun x => ?_⟩
  · -- `|x − ξ| ≤ ρ/2`, so `|x − ξ|/ρ ≤ 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ |x − ξ|`, so `1 ≤ |x − ξ|/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- The profile is `3`-Lipschitz, so `|Dζ(x)| ≤ 3/ρ`.
    have h := Submission.norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφ_lip x
    rwa [NNReal.coe_ofNat] at h
/-- Simon Ch. 5, proof of Theorem 4.5, step 1(v): a `C¹` function with `tsupport ζ ⊆ B̆_r(0)` and
`|∇ζ| ≤ M` satisfies `|ζ| ≤ M r`. For `|y| < r` pick a unit vector `w` with `|y − r w| ≤ r`
(`w = y/|y|`, or a standard basis vector if `y = 0`, which needs `n ≥ 1`); then `ζ(r w) = 0` and
the mean value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`, with
`‖Dζ‖ = ‖∇ζ‖` since the Riesz map is an isometry) gives `|ζ(y)| ≤ M |y − r w| ≤ M r`. -/
theorem gwe_vfv_abs_le_grad_bound_mul_radius : ∀ n : ℕ, 1 ≤ n → ∀ (ζ : Rn n → ℝ) (r M : ℝ), 0 ≤ r → Differentiable ℝ ζ → tsupport ζ ⊆ ball 0 r → (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ y, |ζ y| ≤ M * r := by
  intro n hn ζ r M hr hζ hsupp hM y
  -- `M ≥ ‖∇ζ(0)‖ ≥ 0`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- `ζ` vanishes off `B̆_r(0)`
  have hzero : ∀ z : Rn n, r ≤ ‖z‖ → ζ z = 0 := by
    intro z hz
    by_contra h
    have hz' := hsupp (subset_tsupport ζ h)
    rw [mem_ball_zero_iff] at hz'
    linarith
  -- `‖Dζ(x)‖ = ‖∇ζ(x)‖ ≤ M`, the Riesz map being a linear isometry equivalence
  have hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ M := by
    intro x
    have h := hM x
    rwa [gradient, LinearIsometryEquiv.norm_map] at h
  rcases le_or_gt r ‖y‖ with hy | hy
  · rw [hzero y hy, abs_zero]
    exact mul_nonneg hM0 hr
  -- a unit vector `w` with `‖y − r w‖ ≤ r`
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Rn n, ‖w‖ = 1 ∧ ‖y - r • w‖ ≤ r := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp, ?_⟩
      rw [hy0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      simp
    · have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy'.ne']
      · have hyw : y - r • (‖y‖⁻¹ • y) = (1 - r * ‖y‖⁻¹) • y := by
          rw [smul_smul, sub_smul, one_smul]
        have hc : 1 - r * ‖y‖⁻¹ ≤ 0 := by
          rw [sub_nonpos, ← div_eq_mul_inv, le_div_iff₀ hy', one_mul]
          exact hy.le
        rw [hyw, norm_smul, Real.norm_eq_abs, abs_of_nonpos hc, neg_sub, sub_mul, mul_assoc,
          inv_mul_cancel₀ hy'.ne', mul_one, one_mul]
        linarith
  -- `ζ(r w) = 0`, and the mean value inequality on `ℝⁿ`
  have hrw : ζ (r • w) = 0 :=
    hzero _ (by rw [norm_smul, hw1, Real.norm_eq_abs, abs_of_nonneg hr, mul_one])
  have hmv : ‖ζ y - ζ (r • w)‖ ≤ M * ‖y - r • w‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hζ x) (fun x _ => hD x)
      (mem_univ _) (mem_univ _)
  calc |ζ y| = ‖ζ y - ζ (r • w)‖ := by rw [hrw, sub_zero, Real.norm_eq_abs]
    _ ≤ M * ‖y - r • w‖ := hmv
    _ ≤ M * r := mul_le_mul_of_nonneg_left hw2 hM0

/-- Simon Ch. 5, proof of Theorem 4.5, display (5) (p. 117): `x` is no farther from the origin
than its coordinate along `T = q(ℝⁿ × {0})` plus its height over `T`. For a linear isometry `q` of
`ℝ^{n+ℓ}`, `|x| ≤ |a(x)| + dist(x, T)`, where `a(x) ∈ ℝⁿ` is the first block of `q⁻¹ x`.
Writing `q⁻¹ x = (a, b)`, `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so
`dist(x, T) = |p_{T⊥} x| = |(0, b)| = |b|`, while `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`. -/
theorem gwe_vfv_norm_le_first_block_add_infDist : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (x : Amb n ℓ), ‖x‖ ≤ ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ + infDist x (rotatedPlane q : Set (Amb n ℓ)) := by
  intro n ℓ q x
  obtain ⟨hsub, hnorm, hsurj, hproj⟩ := lip_approx_graph_coordinates n ℓ q
  -- write `q⁻¹ x = (a, b)`; its first block is `a`
  obtain ⟨a, b, hab⟩ := hsurj (q.symm x)
  have hx : x = q (graphPoint a b) := by rw [← hab, q.apply_symm_apply]
  have ha : (EuclideanSpace.finAddEquivProd (q.symm x)).1 = a := by
    rw [hab]
    ext i
    simp [graphPoint]
  -- `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so `dist(x, T) = |(0, b)| = |b|`
  have hb : infDist x (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖ := by
    have h0 := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h0
    rw [← hsNorm_starProjection_trace_identities.2.1 (n + ℓ) (rotatedPlane q) x,
      Submodule.starProjection_orthogonal_val, hx, hproj, ← map_sub, hsub, sub_self, sub_zero,
      q.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h0
  -- `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`
  have hxn : ‖x‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by rw [hx, q.norm_map, hnorm]
  rw [ha, hb]
  refine (pow_le_pow_iff_left₀ (norm_nonneg x) (add_nonneg (norm_nonneg a) (norm_nonneg b))
    two_ne_zero).1 ?_
  rw [hxn, add_sq]
  linarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
/-- Chain rule in rotated coordinates (step 1(ii) of the vertical first variation in Simon's proof
of 4.5): for `a(y) = (finAddEquivProd (q⁻¹ y)).1`, a continuous linear map,
`D(ζ ∘ a)(x) v = Dζ(a(x)) (a v) = ⟨∇ζ(a(x)), a v⟩ = ⟨graphPoint (∇ζ(a(x))) 0, q⁻¹ v⟩
= ⟨q (graphPoint (∇ζ(a(x))) 0), v⟩`. -/
theorem gwe_vfv_hasFDerivAt_comp_first_block : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (ζ : Rn n → ℝ) (x : Amb n ℓ), DifferentiableAt ℝ ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1 → HasFDerivAt (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) (innerSL ℝ (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) x := by
  intro n ℓ q ζ x hζ
  -- `a = fst ∘ finAddEquivProd ∘ q⁻¹` is a continuous linear map `L`.
  let L : Amb n ℓ →L[ℝ] Rn n := (ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp
    ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).toContinuousLinearMap.comp
      q.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hL : ∀ y, L y = (EuclideanSpace.finAddEquivProd (q.symm y)).1 := fun y => rfl
  -- `⟨graphPoint w 0, z⟩ = ⟨w, (finAddEquivProd z).1⟩`: split the sum over `Fin (n + ℓ)`.
  have hcoord : ∀ (w : Rn n) (z : Amb n ℓ),
      inner ℝ (graphPoint w (0 : Rn ℓ)) z = inner ℝ w (EuclideanSpace.finAddEquivProd z).1 := by
    intro w z
    simp only [graphPoint, WithLp.ofLp_zero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, WithLp.prodContinuousLinearEquiv_apply,
      PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
  -- Chain rule: `D(ζ ∘ L)(x) = Dζ(L x) ∘ L`.
  have hd : HasFDerivAt (fun y : Amb n ℓ => ζ (L y)) ((fderiv ℝ ζ (L x)).comp L) x :=
    hζ.hasFDerivAt.comp x L.hasFDerivAt
  -- `Dζ(L x) (L v) = ⟨∇ζ(L x), L v⟩ = ⟨graphPoint (∇ζ(L x)) 0, q⁻¹ v⟩ = ⟨q (graphPoint …), v⟩`.
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, LinearIsometryEquiv.inner_map_eq_flip,
    hcoord, gradient, InnerProductSpace.toDual_symm_apply, hL, hL]
/-- Rank-one tangential divergence (the trace computation in step (5) of Simon's proof of 4.5):
if `Df(x) = ⟨g, ·⟩`, then `div_M (f e)(x) = trace(v ↦ ⟨g, p_x v⟩ e) = ⟨g, p_x e⟩ = ⟨p_x e, p_x g⟩`,
because `p_x = p_{T_x M}` is an orthogonal projection (or `0`), hence self-adjoint and idempotent. -/
theorem gwe_vfv_divM_smul_const_eq_inner : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (f : Amb n ℓ → ℝ) (e g x : Amb n ℓ), HasFDerivAt f (innerSL ℝ g) x → V.divM (fun y => f y • e) x = inner ℝ (V.tangentProj x e) (V.tangentProj x g) := by
  intro n ℓ U V f e g x hf
  -- `⟨p u, p v⟩ = ⟨u, p v⟩` for `p = p_x`, an orthogonal projection or `0`.
  have hp : ∀ u v : Amb n ℓ,
      inner ℝ (V.tangentProj x u) (V.tangentProj x v) = inner ℝ u (V.tangentProj x v) := by
    intro u v
    rw [RectifiableVarifold.tangentProj]
    split_ifs with h
    · rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)]
    · simp
  -- `D(f e)(x) = ⟨g, ·⟩ e`, so `D(f e)(x) ∘ p = ⟨g, p ·⟩ e` has rank one.
  have hcomp : (fderiv ℝ (fun y => f y • e) x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap =
      ((innerSL ℝ g).comp (V.tangentProj x)).toLinearMap.smulRight e := by
    rw [(hf.smul_const e).fderiv]
    refine LinearMap.ext fun w => ?_
    simp
  -- Its trace is `⟨g, p e⟩ = ⟨p g, p e⟩ = ⟨p e, p g⟩`.
  rw [RectifiableVarifold.divM, hcomp, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hp g e, real_inner_comm]
/-- Simon Ch. 5, proof of Theorem 4.5, the identity before (6) (p. 117): the defining identity 3.14
of the generalized mean curvature, localized to `B_s(0)`.  If `φ ∈ C¹`, `2r ≤ R`, `r ≤ s ≤ R`,
`B_R(0) ⊆ U` and `spt V ∩ B_R(0) ∩ spt φ ⊆ B̆_r(0)`, then
`∫_{B_s(0)} div_M(φ e) dμ_V = −∫_{B_s(0)} φ e · H dμ_V`.  Test 3.14 with `X = χ φ e ∈ C¹_c(U)`,
where the cutoff `χ` (`ρ = 2r` in `exists_smooth_cutoff_half_ball_grad_le`) is `1` on `B_r(0)`
and `0` off `B̆_{2r}(0)`.  As `div_M` is local (`Filter.EventuallyEq.fderiv_eq`),
`div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H` on `spt V`: near `x`, `χ = 1`
if `|x| < r`, `φ = 0` if `r ≤ |x| ≤ R`, and `χ = 0` if `|x| > R`.  Finally `spt V` is
`μ_V`-conull (`tdo_ghe_ae_mem_support`). -/
theorem gwe_vfv_localized_first_variation : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (φ : Amb n ℓ → ℝ) (e : Amb n ℓ) (r s R : ℝ), ContDiff ℝ 1 φ → 0 < r → 2 * r ≤ R → r ≤ s → s ≤ R → closedBall (0 : Amb n ℓ) R ⊆ U → (∀ x ∈ V.support ∩ closedBall 0 R, x ∈ tsupport φ → ‖x‖ < r) → ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
  intro n ℓ U V H hH φ e r s R hφ hr h2r hrs hsR hRU hspt
  -- The cutoff `χ ∈ C^∞` with `χ = 1` on `B_r(0)` and `χ = 0` where `|y| ≥ 2r`.
  obtain ⟨χ, hχ, -, hχ1, hχ0, -⟩ :=
    Submission.exists_smooth_cutoff_half_ball_grad_le (n + ℓ) 0 (2 * r) (by positivity)
  have hχ1' : ∀ y : Amb n ℓ, ‖y‖ ≤ r → χ y = 1 := fun y hy =>
    hχ1 y (by rw [mem_closedBall, dist_zero_right]; linarith)
  have hχ0' : ∀ y : Amb n ℓ, 2 * r ≤ ‖y‖ → χ y = 0 := fun y hy =>
    hχ0 y (by rwa [dist_zero_right])
  -- The test field `X = χ φ e ∈ C¹_c(U)`, supported in `B_{2r}(0) ⊆ B_R(0) ⊆ U`.
  set X : Amb n ℓ → Amb n ℓ := fun y => (χ y * φ y) • e with hX_def
  have hX : ContDiff ℝ 1 X :=
    ((hχ.of_le (by exact_mod_cast le_top)).mul hφ).smul contDiff_const
  have hX_supp : tsupport X ⊆ closedBall 0 (2 * r) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (by simp only [hX_def, hχ0' y (by linarith), zero_mul, zero_smul])
  have hXc : HasCompactSupport X :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport X) hX_supp
  have hXU : tsupport X ⊆ U :=
    hX_supp.trans ((closedBall_subset_closedBall (by linarith)).trans hRU)
  -- The first variation formula 3.14 for `X`.
  have hfv := hH.2 X hX hXc hXU
  -- `div_M Y (x)` only depends on `Y` near `x`, and `div_M 0 = 0`.
  have hloc : ∀ (Y Z : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ), Y =ᶠ[𝓝 x] Z →
      V.divM Y x = V.divM Z x := fun Y Z x h => by
    simp only [RectifiableVarifold.divM, h.fderiv_eq (𝕜 := ℝ)]
  have hzero : ∀ x : Amb n ℓ, V.divM (fun _ => 0) x = 0 := fun x => by
    simp [RectifiableVarifold.divM]
  -- On `spt V`: `div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H`.
  have hpt : ∀ x ∈ V.support,
      V.divM X x =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => V.divM (fun y => φ y • e) x) x ∧
      inner ℝ (X x) (H x) =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => φ x * inner ℝ e (H x)) x := by
    intro x hx
    rcases lt_or_ge ‖x‖ r with h1 | h1
    · -- `|x| < r`: `X = φ e` on the neighbourhood `B̆_r(0)` of `x`, and `x ∈ B_s(0)`.
      have hxs : x ∈ closedBall (0 : Amb n ℓ) s := by
        rw [mem_closedBall, dist_zero_right]; linarith
      have hev : X =ᶠ[𝓝 x] fun y => φ y • e := by
        have hxr : x ∈ ball (0 : Amb n ℓ) r := by rwa [mem_ball, dist_zero_right]
        filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
        rw [mem_ball, dist_zero_right] at hy
        simp only [hX_def, hχ1' y hy.le, one_mul]
      rw [indicator_of_mem hxs, indicator_of_mem hxs]
      refine ⟨hloc _ _ x hev, ?_⟩
      simp only [hX_def, hχ1' x h1.le, one_mul, real_inner_smul_left]
    · rcases le_or_gt ‖x‖ R with h2 | h2
      · -- `r ≤ |x| ≤ R`: `x ∉ spt φ`, so `φ = 0` near `x`.
        have hφx : x ∉ tsupport φ := fun h =>
          absurd (hspt x ⟨hx, by rwa [mem_closedBall, dist_zero_right]⟩ h) (not_lt.2 h1)
        have hφ0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hφx
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hX_def, hy]
        have hφe0 : (fun y => φ y • e) =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hy]
        have hφx0 : φ x = 0 := hφ0.self_of_nhds
        refine ⟨?_, ?_⟩
        · rw [hloc _ _ x hX0, hzero]
          by_cases hxs : x ∈ closedBall (0 : Amb n ℓ) s
          · rw [indicator_of_mem hxs, hloc _ _ x hφe0, hzero]
          · rw [indicator_of_notMem hxs]
        · rw [indicator_apply_eq_zero.2 fun _ => by simp only [hφx0, zero_mul]]
          simp [hX_def, hφx0]
      · -- `|x| > R ≥ 2r`: `χ = 0` near `x`, and `x ∉ B_s(0)`.
        have hxs : x ∉ closedBall (0 : Amb n ℓ) s := by
          rw [mem_closedBall, dist_zero_right]; linarith
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := by
          have hxR : x ∈ {y : Amb n ℓ | R < ‖y‖} := h2
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxR] with y hy
          have hy' : R < ‖y‖ := hy
          simp [hX_def, hχ0' y (by linarith)]
        rw [indicator_of_notMem hxs, indicator_of_notMem hxs]
        refine ⟨by rw [hloc _ _ x hX0, hzero], ?_⟩
        simp [hX_def, hχ0' x (by linarith)]
  -- `μ_V`-a.e. point lies in `spt V`; integrate the pointwise identities.
  have hae := Submission.tdo_ghe_ae_mem_support n ℓ U V
  calc ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight
      = ∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => V.divM (fun y => φ y • e) x) x ∂V.weight :=
        (integral_indicator measurableSet_closedBall).symm
    _ = ∫ x, V.divM X x ∂V.weight :=
        integral_congr_ae (hae.mono fun x hx => (hpt x hx).1.symm)
    _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hfv
    _ = -∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => φ x * inner ℝ e (H x)) x ∂V.weight := by
        rw [integral_congr_ae (hae.mono fun x hx => (hpt x hx).2)]
    _ = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
        rw [integral_indicator measurableSet_closedBall]
/-- Simon Ch. 5, proof of Theorem 4.5, displays (5), (6) and the curvature term of (8)
(pp. 117–118), in the rotated frame `T = q(ℝⁿ × {0})`: with `e'_j = q(0, e_j)`, `a(x)` the first
block of `q⁻¹x` and `g(x) = q(∇ζ(a(x)), 0)`,
`|∫_{B_{σ/2}(0)} p_x e'_j · p_x g(x) dμ_V| ≤ M (σ/4) ∫_{B_{σ/2}(0)} |H| dμ_V`.
`ζ̃ = ζ ∘ a` has `Dζ̃(x) = ⟨g(x), ·⟩`, so the integrand is `div_M(ζ̃ e'_j)`.  On
`spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16 = 5σ/16`, so the first
variation formula localizes to `B_{σ/2}(0)`; then `|ζ| ≤ Mσ/4`, `|e'_j| = 1` and the integrability
of `|H|` on the compact `B_{σ/2}(0) ⊆ U` bound the curvature term. -/
theorem gwe_vertical_first_variation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in closedBall (0 : Amb n ℓ) (σ / 2), inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) (V.tangentProj x (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) ∂V.weight| ≤ M * (σ / 4) * ∫ x in closedBall (0 : Amb n ℓ) (σ / 2), ‖H x‖ ∂V.weight := by
  intro n ℓ hn U _hU V H hH σ hσ hσU q hheight ζ hζ _hζc hζσ M hM j
  -- `ζ̃ = ζ ∘ a` is `C¹`, since `a(y) = (q⁻¹y)₁` is continuous linear.
  have ha : Continuous fun y : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    continuous_fst.comp (EuclideanSpace.finAddEquivProd.continuous.comp q.symm.continuous)
  have hζ' : ContDiff ℝ 1 fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    hζ.comp (contDiff_fst.comp (EuclideanSpace.finAddEquivProd.contDiff.comp q.symm.contDiff))
  have hζd : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- The integrand is `div_M(ζ̃ e'_j)`: `Dζ̃(x) = ⟨g(x), ·⟩`, and the trace of the rank-one map.
  have hdiv : ∀ x, inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) =
      V.divM (fun y => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 •
        q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) x := fun x =>
    (Submission.gwe_vfv_divM_smul_const_eq_inner n ℓ U V _ _ _ x
      (Submission.gwe_vfv_hasFDerivAt_comp_first_block n ℓ q ζ x (hζd _))).symm
  -- Localization: on `spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16`.
  have hloc : ∀ x ∈ V.support ∩ closedBall 0 σ,
      x ∈ tsupport (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) →
      ‖x‖ < 5 * σ / 16 := by
    intro x hx hxζ
    have h₁ : ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ < σ / 4 :=
      mem_ball_zero_iff.1 (hζσ (tsupport_comp_subset_preimage ζ ha hxζ))
    linarith [hheight x hx, Submission.gwe_vfv_norm_le_first_block_add_infDist n ℓ q x]
  -- The first variation formula on `B_{σ/2}(0)`, with `r = 5σ/16` and `R = σ`.
  simp only [hdiv]
  rw [Submission.gwe_vfv_localized_first_variation n ℓ U V H hH _ _ (5 * σ / 16) (σ / 2) σ hζ'
      (by positivity) (by linarith) (by linarith) (by linarith) hσU hloc, abs_neg,
    ← Real.norm_eq_abs, ← integral_const_mul]
  -- `|ζ| ≤ Mσ/4`, `|e'_j| = 1`, and `|H|` is integrable on the compact `B_{σ/2}(0) ⊆ U`.
  have hζM : ∀ y, |ζ y| ≤ M * (σ / 4) :=
    Submission.gwe_vfv_abs_le_grad_bound_mul_radius n hn ζ (σ / 4) M (by positivity) hζd hζσ hM
  have he : ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ = 1 := by
    rw [q.norm_map, ← Real.sqrt_sq (norm_nonneg _),
      (Submission.lip_approx_graph_coordinates n ℓ q).2.1]
    simp
  have hH' : IntegrableOn H (closedBall 0 (σ / 2)) V.weight :=
    hH.1.integrableOn_compact_subset ((closedBall_subset_closedBall (by linarith)).trans hσU)
      (isCompact_closedBall 0 _)
  refine norm_integral_le_of_norm_le (hH'.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hζM _) ((abs_real_inner_le_norm _ _).trans_eq (by rw [he, one_mul]))
    (abs_nonneg _) ((abs_nonneg _).trans (hζM 0))

/-- Simon Ch. 5, proof of Theorem 4.5, (8)–(12) on the varifold side. Let `f` be `1`-Lipschitz on
`Bⁿ_{σ/2}(0)` with `|f| ≤ σ/16`, let `spt V ∩ B_σ(0)` lie within `σ/16` of `T = q(ℝⁿ × {0})`, and
let `p_x` be the graph plane of `Df(x')` at `μ_V`-a.e. `x = q(x', f x')` with `|x'| < σ/2` and `f`
differentiable at `x'`. For `ζ ∈ C¹_c(B̆ⁿ_{σ/4}(0))` with `|∇ζ| ≤ M`, `a(x)` the first `n`
coordinates of `q⁻¹x`,
`Γ = q(graph f|B_{σ/2})` and `Γ' = q(graph f|B̆_{σ/4})`,
`|∫_{Γ'} ∇fʲ(a x) · ∇ζ(a x) dμ_V| ≤ M μ_V(B_{σ/2}(0) ∩ (spt V \ Γ)) + M ∫_{B_σ(0)} |p_x − p_T|² dμ_V
  + M (σ/4) ∫_{B_{σ/2}(0)} |H| dμ_V`.
The integrand `Φ(x) = p_x e'_j · p_x q(∇ζ(a x), 0)` of the vertical first variation satisfies
`|∫_{B_{σ/2}(0)} Φ| ≤ M (σ/4) ∫ |H|` and `|Φ| ≤ M`. It vanishes at points of `Γ \ Γ'`, where
`∇ζ(a x) = 0`, and `B_{σ/2}(0) \ (Γ ∪ Γ')` has weight at most `μ_V(B_{σ/2}(0) ∩ (spt V \ Γ))`,
since `μ_V((spt V)ᶜ) = 0`. By the area formula and Rademacher's theorem, the points of `Γ'` over
non-differentiability points of `f` form an `Hⁿ`-null, hence `μ_V`-null, set. At `μ_V`-a.e. other
point of `Γ'`, the tilt algebra gives `|Φ − ∇fʲ · ∇ζ| ≤ M |p_x − p_T|²`; integrate over `Γ'`. -/
theorem gwe_graph_tangential_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → (∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16) → (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → (∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) (σ / 2), x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in q '' graphOver f (ball 0 (σ / 4)), inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1) (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) ∂V.weight| ≤ M * (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2))))).toReal + M * ∫ x in closedBall 0 σ, hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight + M * (σ / 4) * ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH hpm σ hσ hσU q f hf hfb hdist htan ζ hζ hζc hζs M hM j
  obtain ⟨hfin, hcompl, hnull⟩ := Submission.gte_weight_null_finite n ℓ U V
  obtain ⟨hproj, hint⟩ := Submission.gte_tangentProj_integrands n ℓ U V
  obtain ⟨hgpc, hac, hagp, himg⟩ := Submission.gte_graph_image_geometry n ℓ q
  obtain ⟨hZm, hZ0, hDf⟩ := Submission.gte_lipschitz_ball_calculus n ℓ f 1 (σ / 2) hf
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- Step 1: `|q(w, 0)| = |w|`, `|e'_j| = 1`, `(0, 0) = 0` and `|A|² ≥ 0`
  have hgp0 : ∀ w : Rn n, ‖q (graphPoint w (0 : Rn ℓ))‖ = ‖w‖ := by
    intro w
    have h := hnorm w 0
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have he : ‖q (graphPoint (0 : Rn n) (EuclideanSpace.single j (1 : ℝ)))‖ = 1 := by
    have h := hnorm 0 (EuclideanSpace.single j (1 : ℝ))
    have h1 : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    rw [norm_zero, zero_pow two_ne_zero, zero_add, h1] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h
  have hgp00 : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    have h := hsub 0 0 0 0
    simp only [sub_self] at h
    exact h.symm
  have hψ0 : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, 0 ≤ hsNormSq A := fun A =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Step 2: `Γ` is compact, `Γ'` is Borel, `Γ' ⊆ B_{σ/2}(0)`, and `μ_V(B_σ(0)) < ∞`
  obtain ⟨hΓc, hΓ'm⟩ := himg f (σ / 2) (σ / 4) hf.continuousOn (by linarith)
  have hΓm : MeasurableSet (q '' graphOver f (closedBall 0 (σ / 2))) := hΓc.measurableSet
  have hBσ : closedBall (0 : Amb n ℓ) (σ / 2) ⊆ closedBall 0 σ :=
    closedBall_subset_closedBall (by linarith)
  have hμB : V.weight (closedBall (0 : Amb n ℓ) (σ / 2)) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) (hBσ.trans hσU)
  have hμBσ : V.weight (closedBall (0 : Amb n ℓ) σ) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) hσU
  have hΓ'B : q '' graphOver f (ball 0 (σ / 4)) ⊆ closedBall (0 : Amb n ℓ) (σ / 2) := by
    rintro _ ⟨_, ⟨x', hx', rfl⟩, rfl⟩
    have hx'n : ‖x'‖ < σ / 4 := mem_ball_zero_iff.mp hx'
    have hfx : ‖f x'‖ ≤ σ / 16 :=
      hfb x' (ball_subset_closedBall (ball_subset_ball (by linarith) hx'))
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    -- `|(x', f x')|² = |x'|² + |f x'|² ≤ σ²/16 + σ²/256 ≤ σ²/4`
    have h2 : ‖graphPoint x' (f x')‖ ^ 2 ≤ (σ / 2) ^ 2 := by
      rw [hnorm]
      nlinarith [mul_le_mul hx'n.le hx'n.le (norm_nonneg _) (by linarith),
        mul_le_mul hfx hfx (norm_nonneg _) (by linarith), sq_nonneg σ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).mp h2
  -- Step 3: the first-variation integrand `Φ` is bounded by `M` and integrable on `B_{σ/2}(0)`
  have hgrad : Continuous (gradient ζ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv one_ne_zero)
  have hgcont : Continuous fun x : Amb n ℓ =>
      q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) (0 : Rn ℓ)) := by
    have hgp0c : Continuous fun w : Rn n => graphPoint w (0 : Rn ℓ) :=
      hgpc.comp (continuous_id.prodMk continuous_const)
    exact q.continuous.comp (hgp0c.comp (hgrad.comp hac))
  have hΦint : IntegrableOn (fun x => inner ℝ
      (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
      (closedBall 0 (σ / 2)) V.weight :=
    (hint hpm _ hμB).1 _ _ M hgcont.aestronglyMeasurable fun x => (hgp0 _).trans_le (hM _)
  have hΦle : ∀ x, |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)))| ≤ M := by
    intro x
    calc _ ≤ ‖V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ *
          ‖V.tangentProj x
            (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ *
          ‖q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)‖ :=
          mul_le_mul (hproj _ _) (hproj _ _) (norm_nonneg _) (norm_nonneg _)
      _ ≤ 1 * M := by
          rw [he, hgp0]
          exact mul_le_mul_of_nonneg_left (hM _) zero_le_one
      _ = M := one_mul M
  -- Step 4: `Φ = 0` at the points of `Γ` outside `Γ'`, where `∇ζ(a x) = 0`
  have hΦzero : ∀ x ∈ (closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) ∩
      q '' graphOver f (closedBall 0 (σ / 2)),
      inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) = 0 := by
    rintro x ⟨⟨-, hxG'⟩, ⟨_, ⟨x', -, rfl⟩, rfl⟩⟩
    have hx' : x' ∉ tsupport ζ := fun h => hxG' ⟨_, ⟨x', hζs h, rfl⟩, rfl⟩
    have hgrad0 : gradient ζ x' = 0 := by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx', map_zero]
    rw [hagp, hgrad0, hgp00, map_zero, map_zero, inner_zero_right]
  -- Step 5: off `Γ ∪ Γ'`, `B_{σ/2}(0)` has weight at most `μ_V(B_{σ/2}(0) ∩ (spt V \ Γ)) < ∞`
  have hmle : V.weight ((closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) \
      q '' graphOver f (closedBall 0 (σ / 2))) ≤
      V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) := by
    calc _ ≤ V.weight ((closedBall 0 (σ / 2) ∩
          (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) ∪ V.supportᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hs : x ∈ V.support
          · exact Or.inl ⟨hx.1.1, hs, hx.2⟩
          · exact Or.inr hs
      _ ≤ _ + V.weight V.supportᶜ := measure_union_le _ _
      _ = _ := by rw [hcompl, add_zero]
  have hmlt : V.weight (closedBall (0 : Amb n ℓ) (σ / 2) ∩
      (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hμB
  -- Step 6: `φ = ∇fʲ(a x) · ∇ζ(a x)` is Borel, and the tilt integrand is integrable on `B_σ(0)`
  have hφm : AEStronglyMeasurable (fun x => inner ℝ
      (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
      (V.weight.restrict (q '' graphOver f (ball 0 (σ / 4)))) := by
    have h1 : Measurable (gradient fun y => f y j) :=
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
    exact (Continuous.measurable2 (c := fun a b : Rn n => inner ℝ a b) continuous_inner
      (h1.comp hac.measurable) (hgrad.measurable.comp hac.measurable)).aestronglyMeasurable
  have hψint : IntegrableOn (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection))
      (closedBall 0 σ) V.weight :=
    (hint hpm _ hμBσ).2 _
  -- Step 7: the graph over the non-differentiability points of `f` is `Hⁿ`-null (area formula
  -- and Rademacher), hence `μ_V`-null
  have hZnull : V.weight (q '' graphOver f (ball (0 : Rn n) (σ / 2) ∩
      {x | ¬DifferentiableAt ℝ f x})) = 0 := by
    apply hnull
    have h := gwe_lipschitz_graph_area_formula n ℓ hn q f 1 (σ / 2) hf _ hZm
      (inter_subset_left.trans ball_subset_closedBall) (fun _ => 1)
    rw [setLIntegral_one, setLIntegral_measure_zero _ _ hZ0] at h
    exact h
  -- Step 8: a.e. on `Γ'`, `p_x` is the graph plane of `Df(a x)`, and the tilt algebra gives
  -- `|Φ - φ| ≤ |p_x - p_T|² |∇ζ(a x)| ≤ M |p_x - p_T|²`
  have hae : ∀ᵐ x ∂V.weight, x ∈ q '' graphOver f (ball 0 (σ / 4)) →
      |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) -
        inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
          (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1)| ≤
        M * hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) := by
    filter_upwards [htan, measure_eq_zero_iff_ae_notMem.mp hZnull] with x hxt hxZ hxG'
    obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hxG'
    have hx'2 : x' ∈ ball (0 : Rn n) (σ / 2) := ball_subset_ball (by linarith) hx'
    have hd : DifferentiableAt ℝ f x' := by
      by_contra hnd
      exact hxZ ⟨_, ⟨x', ⟨hx'2, hnd⟩, rfl⟩, rfl⟩
    obtain ⟨hD1, hgradf⟩ := hDf x' hx'2
    have hD : ‖fderiv ℝ f x'‖ ≤ 1 := by exact_mod_cast hD1
    have hTA := (Submission.gwe_graph_tilt_algebra n ℓ q (fderiv ℝ f x') hD).2 j _
      (gradient ζ x') (hgradf hd j)
    rw [hagp, hxt x' hx'2 rfl hd]
    exact hTA.trans ((mul_le_mul_of_nonneg_left (hM _) (hψ0 _)).trans_eq (mul_comm _ _))
  -- Step 9: combine the localized comparison with the vertical first-variation bound
  have hcmp := Submission.gte_localized_comparison V.weight (closedBall (0 : Amb n ℓ) (σ / 2))
    (closedBall 0 σ) (q '' graphOver f (closedBall 0 (σ / 2))) (q '' graphOver f (ball 0 (σ / 4)))
    (fun x => inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
    (fun x => inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
    (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection)) M
    (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))))
    hM0 hΓm hΓ'm hΓ'B (hΓ'B.trans hBσ) hΦint hΦle hΦzero hmle hmlt hφm hψint (fun _ => hψ0 _) hae
  have hfv := Submission.gwe_vertical_first_variation n ℓ hn U hU V H hH σ hσ hσU q hdist ζ hζ
    hζc hζs M hM j
  linarith
/-- Simon Ch. 5, proof of Theorem 4.5, step 1(v): a `C¹` function with `tsupport ζ ⊆ B̆_r(0)` and
`|∇ζ| ≤ M` satisfies `|ζ| ≤ M r`. For `|y| < r` pick a unit vector `w` with `|y − r w| ≤ r`
(`w = y/|y|`, or a standard basis vector if `y = 0`, which needs `n ≥ 1`); then `ζ(r w) = 0` and
the mean value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`, with
`‖Dζ‖ = ‖∇ζ‖` since the Riesz map is an isometry) gives `|ζ(y)| ≤ M |y − r w| ≤ M r`. -/
theorem gwe_vfv_abs_le_grad_bound_mul_radius : ∀ n : ℕ, 1 ≤ n → ∀ (ζ : Rn n → ℝ) (r M : ℝ), 0 ≤ r → Differentiable ℝ ζ → tsupport ζ ⊆ ball 0 r → (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ y, |ζ y| ≤ M * r := by
  intro n hn ζ r M hr hζ hsupp hM y
  -- `M ≥ ‖∇ζ(0)‖ ≥ 0`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- `ζ` vanishes off `B̆_r(0)`
  have hzero : ∀ z : Rn n, r ≤ ‖z‖ → ζ z = 0 := by
    intro z hz
    by_contra h
    have hz' := hsupp (subset_tsupport ζ h)
    rw [mem_ball_zero_iff] at hz'
    linarith
  -- `‖Dζ(x)‖ = ‖∇ζ(x)‖ ≤ M`, the Riesz map being a linear isometry equivalence
  have hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ M := by
    intro x
    have h := hM x
    rwa [gradient, LinearIsometryEquiv.norm_map] at h
  rcases le_or_gt r ‖y‖ with hy | hy
  · rw [hzero y hy, abs_zero]
    exact mul_nonneg hM0 hr
  -- a unit vector `w` with `‖y − r w‖ ≤ r`
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Rn n, ‖w‖ = 1 ∧ ‖y - r • w‖ ≤ r := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp, ?_⟩
      rw [hy0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      simp
    · have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy'.ne']
      · have hyw : y - r • (‖y‖⁻¹ • y) = (1 - r * ‖y‖⁻¹) • y := by
          rw [smul_smul, sub_smul, one_smul]
        have hc : 1 - r * ‖y‖⁻¹ ≤ 0 := by
          rw [sub_nonpos, ← div_eq_mul_inv, le_div_iff₀ hy', one_mul]
          exact hy.le
        rw [hyw, norm_smul, Real.norm_eq_abs, abs_of_nonpos hc, neg_sub, sub_mul, mul_assoc,
          inv_mul_cancel₀ hy'.ne', mul_one, one_mul]
        linarith
  -- `ζ(r w) = 0`, and the mean value inequality on `ℝⁿ`
  have hrw : ζ (r • w) = 0 :=
    hzero _ (by rw [norm_smul, hw1, Real.norm_eq_abs, abs_of_nonneg hr, mul_one])
  have hmv : ‖ζ y - ζ (r • w)‖ ≤ M * ‖y - r • w‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hζ x) (fun x _ => hD x)
      (mem_univ _) (mem_univ _)
  calc |ζ y| = ‖ζ y - ζ (r • w)‖ := by rw [hrw, sub_zero, Real.norm_eq_abs]
    _ ≤ M * ‖y - r • w‖ := hmv
    _ ≤ M * r := mul_le_mul_of_nonneg_left hw2 hM0

/-- Simon Ch. 5, proof of Theorem 4.5, display (5) (p. 117): `x` is no farther from the origin
than its coordinate along `T = q(ℝⁿ × {0})` plus its height over `T`. For a linear isometry `q` of
`ℝ^{n+ℓ}`, `|x| ≤ |a(x)| + dist(x, T)`, where `a(x) ∈ ℝⁿ` is the first block of `q⁻¹ x`.
Writing `q⁻¹ x = (a, b)`, `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so
`dist(x, T) = |p_{T⊥} x| = |(0, b)| = |b|`, while `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`. -/
theorem gwe_vfv_norm_le_first_block_add_infDist : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (x : Amb n ℓ), ‖x‖ ≤ ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ + infDist x (rotatedPlane q : Set (Amb n ℓ)) := by
  intro n ℓ q x
  obtain ⟨hsub, hnorm, hsurj, hproj⟩ := lip_approx_graph_coordinates n ℓ q
  -- write `q⁻¹ x = (a, b)`; its first block is `a`
  obtain ⟨a, b, hab⟩ := hsurj (q.symm x)
  have hx : x = q (graphPoint a b) := by rw [← hab, q.apply_symm_apply]
  have ha : (EuclideanSpace.finAddEquivProd (q.symm x)).1 = a := by
    rw [hab]
    ext i
    simp [graphPoint]
  -- `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so `dist(x, T) = |(0, b)| = |b|`
  have hb : infDist x (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖ := by
    have h0 := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h0
    rw [← hsNorm_starProjection_trace_identities.2.1 (n + ℓ) (rotatedPlane q) x,
      Submodule.starProjection_orthogonal_val, hx, hproj, ← map_sub, hsub, sub_self, sub_zero,
      q.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h0
  -- `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`
  have hxn : ‖x‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by rw [hx, q.norm_map, hnorm]
  rw [ha, hb]
  refine (pow_le_pow_iff_left₀ (norm_nonneg x) (add_nonneg (norm_nonneg a) (norm_nonneg b))
    two_ne_zero).1 ?_
  rw [hxn, add_sq]
  linarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
/-- Chain rule in rotated coordinates (step 1(ii) of the vertical first variation in Simon's proof
of 4.5): for `a(y) = (finAddEquivProd (q⁻¹ y)).1`, a continuous linear map,
`D(ζ ∘ a)(x) v = Dζ(a(x)) (a v) = ⟨∇ζ(a(x)), a v⟩ = ⟨graphPoint (∇ζ(a(x))) 0, q⁻¹ v⟩
= ⟨q (graphPoint (∇ζ(a(x))) 0), v⟩`. -/
theorem gwe_vfv_hasFDerivAt_comp_first_block : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (ζ : Rn n → ℝ) (x : Amb n ℓ), DifferentiableAt ℝ ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1 → HasFDerivAt (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) (innerSL ℝ (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) x := by
  intro n ℓ q ζ x hζ
  -- `a = fst ∘ finAddEquivProd ∘ q⁻¹` is a continuous linear map `L`.
  let L : Amb n ℓ →L[ℝ] Rn n := (ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp
    ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).toContinuousLinearMap.comp
      q.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hL : ∀ y, L y = (EuclideanSpace.finAddEquivProd (q.symm y)).1 := fun y => rfl
  -- `⟨graphPoint w 0, z⟩ = ⟨w, (finAddEquivProd z).1⟩`: split the sum over `Fin (n + ℓ)`.
  have hcoord : ∀ (w : Rn n) (z : Amb n ℓ),
      inner ℝ (graphPoint w (0 : Rn ℓ)) z = inner ℝ w (EuclideanSpace.finAddEquivProd z).1 := by
    intro w z
    simp only [graphPoint, WithLp.ofLp_zero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, WithLp.prodContinuousLinearEquiv_apply,
      PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
  -- Chain rule: `D(ζ ∘ L)(x) = Dζ(L x) ∘ L`.
  have hd : HasFDerivAt (fun y : Amb n ℓ => ζ (L y)) ((fderiv ℝ ζ (L x)).comp L) x :=
    hζ.hasFDerivAt.comp x L.hasFDerivAt
  -- `Dζ(L x) (L v) = ⟨∇ζ(L x), L v⟩ = ⟨graphPoint (∇ζ(L x)) 0, q⁻¹ v⟩ = ⟨q (graphPoint …), v⟩`.
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, LinearIsometryEquiv.inner_map_eq_flip,
    hcoord, gradient, InnerProductSpace.toDual_symm_apply, hL, hL]
/-- Rank-one tangential divergence (the trace computation in step (5) of Simon's proof of 4.5):
if `Df(x) = ⟨g, ·⟩`, then `div_M (f e)(x) = trace(v ↦ ⟨g, p_x v⟩ e) = ⟨g, p_x e⟩ = ⟨p_x e, p_x g⟩`,
because `p_x = p_{T_x M}` is an orthogonal projection (or `0`), hence self-adjoint and idempotent. -/
theorem gwe_vfv_divM_smul_const_eq_inner : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (f : Amb n ℓ → ℝ) (e g x : Amb n ℓ), HasFDerivAt f (innerSL ℝ g) x → V.divM (fun y => f y • e) x = inner ℝ (V.tangentProj x e) (V.tangentProj x g) := by
  intro n ℓ U V f e g x hf
  -- `⟨p u, p v⟩ = ⟨u, p v⟩` for `p = p_x`, an orthogonal projection or `0`.
  have hp : ∀ u v : Amb n ℓ,
      inner ℝ (V.tangentProj x u) (V.tangentProj x v) = inner ℝ u (V.tangentProj x v) := by
    intro u v
    rw [RectifiableVarifold.tangentProj]
    split_ifs with h
    · rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)]
    · simp
  -- `D(f e)(x) = ⟨g, ·⟩ e`, so `D(f e)(x) ∘ p = ⟨g, p ·⟩ e` has rank one.
  have hcomp : (fderiv ℝ (fun y => f y • e) x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap =
      ((innerSL ℝ g).comp (V.tangentProj x)).toLinearMap.smulRight e := by
    rw [(hf.smul_const e).fderiv]
    refine LinearMap.ext fun w => ?_
    simp
  -- Its trace is `⟨g, p e⟩ = ⟨p g, p e⟩ = ⟨p e, p g⟩`.
  rw [RectifiableVarifold.divM, hcomp, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hp g e, real_inner_comm]
/-- Simon Ch. 5, proof of Theorem 4.5, the identity before (6) (p. 117): the defining identity 3.14
of the generalized mean curvature, localized to `B_s(0)`.  If `φ ∈ C¹`, `2r ≤ R`, `r ≤ s ≤ R`,
`B_R(0) ⊆ U` and `spt V ∩ B_R(0) ∩ spt φ ⊆ B̆_r(0)`, then
`∫_{B_s(0)} div_M(φ e) dμ_V = −∫_{B_s(0)} φ e · H dμ_V`.  Test 3.14 with `X = χ φ e ∈ C¹_c(U)`,
where the cutoff `χ` (`ρ = 2r` in `exists_smooth_cutoff_half_ball_grad_le`) is `1` on `B_r(0)`
and `0` off `B̆_{2r}(0)`.  As `div_M` is local (`Filter.EventuallyEq.fderiv_eq`),
`div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H` on `spt V`: near `x`, `χ = 1`
if `|x| < r`, `φ = 0` if `r ≤ |x| ≤ R`, and `χ = 0` if `|x| > R`.  Finally `spt V` is
`μ_V`-conull (`tdo_ghe_ae_mem_support`). -/
theorem gwe_vfv_localized_first_variation : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (φ : Amb n ℓ → ℝ) (e : Amb n ℓ) (r s R : ℝ), ContDiff ℝ 1 φ → 0 < r → 2 * r ≤ R → r ≤ s → s ≤ R → closedBall (0 : Amb n ℓ) R ⊆ U → (∀ x ∈ V.support ∩ closedBall 0 R, x ∈ tsupport φ → ‖x‖ < r) → ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
  intro n ℓ U V H hH φ e r s R hφ hr h2r hrs hsR hRU hspt
  -- The cutoff `χ ∈ C^∞` with `χ = 1` on `B_r(0)` and `χ = 0` where `|y| ≥ 2r`.
  obtain ⟨χ, hχ, -, hχ1, hχ0, -⟩ :=
    Submission.exists_smooth_cutoff_half_ball_grad_le (n + ℓ) 0 (2 * r) (by positivity)
  have hχ1' : ∀ y : Amb n ℓ, ‖y‖ ≤ r → χ y = 1 := fun y hy =>
    hχ1 y (by rw [mem_closedBall, dist_zero_right]; linarith)
  have hχ0' : ∀ y : Amb n ℓ, 2 * r ≤ ‖y‖ → χ y = 0 := fun y hy =>
    hχ0 y (by rwa [dist_zero_right])
  -- The test field `X = χ φ e ∈ C¹_c(U)`, supported in `B_{2r}(0) ⊆ B_R(0) ⊆ U`.
  set X : Amb n ℓ → Amb n ℓ := fun y => (χ y * φ y) • e with hX_def
  have hX : ContDiff ℝ 1 X :=
    ((hχ.of_le (by exact_mod_cast le_top)).mul hφ).smul contDiff_const
  have hX_supp : tsupport X ⊆ closedBall 0 (2 * r) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (by simp only [hX_def, hχ0' y (by linarith), zero_mul, zero_smul])
  have hXc : HasCompactSupport X :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport X) hX_supp
  have hXU : tsupport X ⊆ U :=
    hX_supp.trans ((closedBall_subset_closedBall (by linarith)).trans hRU)
  -- The first variation formula 3.14 for `X`.
  have hfv := hH.2 X hX hXc hXU
  -- `div_M Y (x)` only depends on `Y` near `x`, and `div_M 0 = 0`.
  have hloc : ∀ (Y Z : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ), Y =ᶠ[𝓝 x] Z →
      V.divM Y x = V.divM Z x := fun Y Z x h => by
    simp only [RectifiableVarifold.divM, h.fderiv_eq (𝕜 := ℝ)]
  have hzero : ∀ x : Amb n ℓ, V.divM (fun _ => 0) x = 0 := fun x => by
    simp [RectifiableVarifold.divM]
  -- On `spt V`: `div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H`.
  have hpt : ∀ x ∈ V.support,
      V.divM X x =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => V.divM (fun y => φ y • e) x) x ∧
      inner ℝ (X x) (H x) =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => φ x * inner ℝ e (H x)) x := by
    intro x hx
    rcases lt_or_ge ‖x‖ r with h1 | h1
    · -- `|x| < r`: `X = φ e` on the neighbourhood `B̆_r(0)` of `x`, and `x ∈ B_s(0)`.
      have hxs : x ∈ closedBall (0 : Amb n ℓ) s := by
        rw [mem_closedBall, dist_zero_right]; linarith
      have hev : X =ᶠ[𝓝 x] fun y => φ y • e := by
        have hxr : x ∈ ball (0 : Amb n ℓ) r := by rwa [mem_ball, dist_zero_right]
        filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
        rw [mem_ball, dist_zero_right] at hy
        simp only [hX_def, hχ1' y hy.le, one_mul]
      rw [indicator_of_mem hxs, indicator_of_mem hxs]
      refine ⟨hloc _ _ x hev, ?_⟩
      simp only [hX_def, hχ1' x h1.le, one_mul, real_inner_smul_left]
    · rcases le_or_gt ‖x‖ R with h2 | h2
      · -- `r ≤ |x| ≤ R`: `x ∉ spt φ`, so `φ = 0` near `x`.
        have hφx : x ∉ tsupport φ := fun h =>
          absurd (hspt x ⟨hx, by rwa [mem_closedBall, dist_zero_right]⟩ h) (not_lt.2 h1)
        have hφ0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hφx
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hX_def, hy]
        have hφe0 : (fun y => φ y • e) =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hy]
        have hφx0 : φ x = 0 := hφ0.self_of_nhds
        refine ⟨?_, ?_⟩
        · rw [hloc _ _ x hX0, hzero]
          by_cases hxs : x ∈ closedBall (0 : Amb n ℓ) s
          · rw [indicator_of_mem hxs, hloc _ _ x hφe0, hzero]
          · rw [indicator_of_notMem hxs]
        · rw [indicator_apply_eq_zero.2 fun _ => by simp only [hφx0, zero_mul]]
          simp [hX_def, hφx0]
      · -- `|x| > R ≥ 2r`: `χ = 0` near `x`, and `x ∉ B_s(0)`.
        have hxs : x ∉ closedBall (0 : Amb n ℓ) s := by
          rw [mem_closedBall, dist_zero_right]; linarith
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := by
          have hxR : x ∈ {y : Amb n ℓ | R < ‖y‖} := h2
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxR] with y hy
          have hy' : R < ‖y‖ := hy
          simp [hX_def, hχ0' y (by linarith)]
        rw [indicator_of_notMem hxs, indicator_of_notMem hxs]
        refine ⟨by rw [hloc _ _ x hX0, hzero], ?_⟩
        simp [hX_def, hχ0' x (by linarith)]
  -- `μ_V`-a.e. point lies in `spt V`; integrate the pointwise identities.
  have hae := Submission.tdo_ghe_ae_mem_support n ℓ U V
  calc ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight
      = ∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => V.divM (fun y => φ y • e) x) x ∂V.weight :=
        (integral_indicator measurableSet_closedBall).symm
    _ = ∫ x, V.divM X x ∂V.weight :=
        integral_congr_ae (hae.mono fun x hx => (hpt x hx).1.symm)
    _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hfv
    _ = -∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => φ x * inner ℝ e (H x)) x ∂V.weight := by
        rw [integral_congr_ae (hae.mono fun x hx => (hpt x hx).2)]
    _ = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
        rw [integral_indicator measurableSet_closedBall]
/-- Simon Ch. 5, proof of Theorem 4.5, displays (5), (6) and the curvature term of (8)
(pp. 117–118), in the rotated frame `T = q(ℝⁿ × {0})`: with `e'_j = q(0, e_j)`, `a(x)` the first
block of `q⁻¹x` and `g(x) = q(∇ζ(a(x)), 0)`,
`|∫_{B_{σ/2}(0)} p_x e'_j · p_x g(x) dμ_V| ≤ M (σ/4) ∫_{B_{σ/2}(0)} |H| dμ_V`.
`ζ̃ = ζ ∘ a` has `Dζ̃(x) = ⟨g(x), ·⟩`, so the integrand is `div_M(ζ̃ e'_j)`.  On
`spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16 = 5σ/16`, so the first
variation formula localizes to `B_{σ/2}(0)`; then `|ζ| ≤ Mσ/4`, `|e'_j| = 1` and the integrability
of `|H|` on the compact `B_{σ/2}(0) ⊆ U` bound the curvature term. -/
theorem gwe_vertical_first_variation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in closedBall (0 : Amb n ℓ) (σ / 2), inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) (V.tangentProj x (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) ∂V.weight| ≤ M * (σ / 4) * ∫ x in closedBall (0 : Amb n ℓ) (σ / 2), ‖H x‖ ∂V.weight := by
  intro n ℓ hn U _hU V H hH σ hσ hσU q hheight ζ hζ _hζc hζσ M hM j
  -- `ζ̃ = ζ ∘ a` is `C¹`, since `a(y) = (q⁻¹y)₁` is continuous linear.
  have ha : Continuous fun y : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    continuous_fst.comp (EuclideanSpace.finAddEquivProd.continuous.comp q.symm.continuous)
  have hζ' : ContDiff ℝ 1 fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    hζ.comp (contDiff_fst.comp (EuclideanSpace.finAddEquivProd.contDiff.comp q.symm.contDiff))
  have hζd : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- The integrand is `div_M(ζ̃ e'_j)`: `Dζ̃(x) = ⟨g(x), ·⟩`, and the trace of the rank-one map.
  have hdiv : ∀ x, inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) =
      V.divM (fun y => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 •
        q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) x := fun x =>
    (Submission.gwe_vfv_divM_smul_const_eq_inner n ℓ U V _ _ _ x
      (Submission.gwe_vfv_hasFDerivAt_comp_first_block n ℓ q ζ x (hζd _))).symm
  -- Localization: on `spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16`.
  have hloc : ∀ x ∈ V.support ∩ closedBall 0 σ,
      x ∈ tsupport (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) →
      ‖x‖ < 5 * σ / 16 := by
    intro x hx hxζ
    have h₁ : ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ < σ / 4 :=
      mem_ball_zero_iff.1 (hζσ (tsupport_comp_subset_preimage ζ ha hxζ))
    linarith [hheight x hx, Submission.gwe_vfv_norm_le_first_block_add_infDist n ℓ q x]
  -- The first variation formula on `B_{σ/2}(0)`, with `r = 5σ/16` and `R = σ`.
  simp only [hdiv]
  rw [Submission.gwe_vfv_localized_first_variation n ℓ U V H hH _ _ (5 * σ / 16) (σ / 2) σ hζ'
      (by positivity) (by linarith) (by linarith) (by linarith) hσU hloc, abs_neg,
    ← Real.norm_eq_abs, ← integral_const_mul]
  -- `|ζ| ≤ Mσ/4`, `|e'_j| = 1`, and `|H|` is integrable on the compact `B_{σ/2}(0) ⊆ U`.
  have hζM : ∀ y, |ζ y| ≤ M * (σ / 4) :=
    Submission.gwe_vfv_abs_le_grad_bound_mul_radius n hn ζ (σ / 4) M (by positivity) hζd hζσ hM
  have he : ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ = 1 := by
    rw [q.norm_map, ← Real.sqrt_sq (norm_nonneg _),
      (Submission.lip_approx_graph_coordinates n ℓ q).2.1]
    simp
  have hH' : IntegrableOn H (closedBall 0 (σ / 2)) V.weight :=
    hH.1.integrableOn_compact_subset ((closedBall_subset_closedBall (by linarith)).trans hσU)
      (isCompact_closedBall 0 _)
  refine norm_integral_le_of_norm_le (hH'.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hζM _) ((abs_real_inner_le_norm _ _).trans_eq (by rw [he, one_mul]))
    (abs_nonneg _) ((abs_nonneg _).trans (hζM 0))
  -- Step 2: `Γ` is compact, `Γ'` is Borel, `Γ' ⊆ B_{σ/2}(0)`, and `μ_V(B_σ(0)) < ∞`
  obtain ⟨hΓc, hΓ'm⟩ := himg f (σ / 2) (σ / 4) hf.continuousOn (by linarith)
  have hΓm : MeasurableSet (q '' graphOver f (closedBall 0 (σ / 2))) := hΓc.measurableSet
  have hBσ : closedBall (0 : Amb n ℓ) (σ / 2) ⊆ closedBall 0 σ :=
    closedBall_subset_closedBall (by linarith)
  have hμB : V.weight (closedBall (0 : Amb n ℓ) (σ / 2)) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) (hBσ.trans hσU)
  have hμBσ : V.weight (closedBall (0 : Amb n ℓ) σ) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) hσU
  have hΓ'B : q '' graphOver f (ball 0 (σ / 4)) ⊆ closedBall (0 : Amb n ℓ) (σ / 2) := by
    rintro _ ⟨_, ⟨x', hx', rfl⟩, rfl⟩
    have hx'n : ‖x'‖ < σ / 4 := mem_ball_zero_iff.mp hx'
    have hfx : ‖f x'‖ ≤ σ / 16 :=
      hfb x' (ball_subset_closedBall (ball_subset_ball (by linarith) hx'))
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    -- `|(x', f x')|² = |x'|² + |f x'|² ≤ σ²/16 + σ²/256 ≤ σ²/4`
    have h2 : ‖graphPoint x' (f x')‖ ^ 2 ≤ (σ / 2) ^ 2 := by
      rw [hnorm]
      nlinarith [mul_le_mul hx'n.le hx'n.le (norm_nonneg _) (by linarith),
        mul_le_mul hfx hfx (norm_nonneg _) (by linarith), sq_nonneg σ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).mp h2
  -- Step 3: the first-variation integrand `Φ` is bounded by `M` and integrable on `B_{σ/2}(0)`
  have hgrad : Continuous (gradient ζ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv one_ne_zero)
  have hgcont : Continuous fun x : Amb n ℓ =>
      q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) (0 : Rn ℓ)) := by
    have hgp0c : Continuous fun w : Rn n => graphPoint w (0 : Rn ℓ) :=
      hgpc.comp (continuous_id.prodMk continuous_const)
    exact q.continuous.comp (hgp0c.comp (hgrad.comp hac))
  have hΦint : IntegrableOn (fun x => inner ℝ
      (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
      (closedBall 0 (σ / 2)) V.weight :=
    (hint hpm _ hμB).1 _ _ M hgcont.aestronglyMeasurable fun x => (hgp0 _).trans_le (hM _)
  have hΦle : ∀ x, |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)))| ≤ M := by
    intro x
    calc _ ≤ ‖V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ *
          ‖V.tangentProj x
            (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ *
          ‖q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)‖ :=
          mul_le_mul (hproj _ _) (hproj _ _) (norm_nonneg _) (norm_nonneg _)
      _ ≤ 1 * M := by
          rw [he, hgp0]
          exact mul_le_mul_of_nonneg_left (hM _) zero_le_one
      _ = M := one_mul M
  -- Step 4: `Φ = 0` at the points of `Γ` outside `Γ'`, where `∇ζ(a x) = 0`
  have hΦzero : ∀ x ∈ (closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) ∩
      q '' graphOver f (closedBall 0 (σ / 2)),
      inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) = 0 := by
    rintro x ⟨⟨-, hxG'⟩, ⟨_, ⟨x', -, rfl⟩, rfl⟩⟩
    have hx' : x' ∉ tsupport ζ := fun h => hxG' ⟨_, ⟨x', hζs h, rfl⟩, rfl⟩
    have hgrad0 : gradient ζ x' = 0 := by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx', map_zero]
    rw [hagp, hgrad0, hgp00, map_zero, map_zero, inner_zero_right]
  -- Step 5: off `Γ ∪ Γ'`, `B_{σ/2}(0)` has weight at most `μ_V(B_{σ/2}(0) ∩ (spt V \ Γ)) < ∞`
  have hmle : V.weight ((closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) \
      q '' graphOver f (closedBall 0 (σ / 2))) ≤
      V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) := by
    calc _ ≤ V.weight ((closedBall 0 (σ / 2) ∩
          (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) ∪ V.supportᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hs : x ∈ V.support
          · exact Or.inl ⟨hx.1.1, hs, hx.2⟩
          · exact Or.inr hs
      _ ≤ _ + V.weight V.supportᶜ := measure_union_le _ _
      _ = _ := by rw [hcompl, add_zero]
  have hmlt : V.weight (closedBall (0 : Amb n ℓ) (σ / 2) ∩
      (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hμB
  -- Step 6: `φ = ∇fʲ(a x) · ∇ζ(a x)` is Borel, and the tilt integrand is integrable on `B_σ(0)`
  have hφm : AEStronglyMeasurable (fun x => inner ℝ
      (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
      (V.weight.restrict (q '' graphOver f (ball 0 (σ / 4)))) := by
    have h1 : Measurable (gradient fun y => f y j) :=
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
    exact (Continuous.measurable2 (c := fun a b : Rn n => inner ℝ a b) continuous_inner
      (h1.comp hac.measurable) (hgrad.measurable.comp hac.measurable)).aestronglyMeasurable
  have hψint : IntegrableOn (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection))
      (closedBall 0 σ) V.weight :=
    (hint hpm _ hμBσ).2 _
  -- Step 7: the graph over the non-differentiability points of `f` is `Hⁿ`-null (area formula
  -- and Rademacher), hence `μ_V`-null
  have hZnull : V.weight (q '' graphOver f (ball (0 : Rn n) (σ / 2) ∩
      {x | ¬DifferentiableAt ℝ f x})) = 0 := by
    apply hnull
    have h := gwe_lipschitz_graph_area_formula n ℓ hn q f 1 (σ / 2) hf _ hZm
      (inter_subset_left.trans ball_subset_closedBall) (fun _ => 1)
    rw [setLIntegral_one, setLIntegral_measure_zero _ _ hZ0] at h
    exact h
  -- Step 8: a.e. on `Γ'`, `p_x` is the graph plane of `Df(a x)`, and the tilt algebra gives
  -- `|Φ - φ| ≤ |p_x - p_T|² |∇ζ(a x)| ≤ M |p_x - p_T|²`
  have hae : ∀ᵐ x ∂V.weight, x ∈ q '' graphOver f (ball 0 (σ / 4)) →
      |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) -
        inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
          (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1)| ≤
        M * hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) := by
    filter_upwards [htan, measure_eq_zero_iff_ae_notMem.mp hZnull] with x hxt hxZ hxG'
    obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hxG'
    have hx'2 : x' ∈ ball (0 : Rn n) (σ / 2) := ball_subset_ball (by linarith) hx'
    have hd : DifferentiableAt ℝ f x' := by
      by_contra hnd
      exact hxZ ⟨_, ⟨x', ⟨hx'2, hnd⟩, rfl⟩, rfl⟩
    obtain ⟨hD1, hgradf⟩ := hDf x' hx'2
    have hD : ‖fderiv ℝ f x'‖ ≤ 1 := by exact_mod_cast hD1
    have hTA := (Submission.gwe_graph_tilt_algebra n ℓ q (fderiv ℝ f x') hD).2 j _
      (gradient ζ x') (hgradf hd j)
    rw [hagp, hxt x' hx'2 rfl hd]
    exact hTA.trans ((mul_le_mul_of_nonneg_left (hM _) (hψ0 _)).trans_eq (mul_comm _ _))
  -- Step 9: combine the localized comparison with the vertical first-variation bound
  have hcmp := Submission.gte_localized_comparison V.weight (closedBall (0 : Amb n ℓ) (σ / 2))
    (closedBall 0 σ) (q '' graphOver f (closedBall 0 (σ / 2))) (q '' graphOver f (ball 0 (σ / 4)))
    (fun x => inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
    (fun x => inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
    (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection)) M
    (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))))
    hM0 hΓm hΓ'm hΓ'B (hΓ'B.trans hBσ) hΦint hΦle hΦzero hmle hmlt hφm hψint (fun _ => hψ0 _) hae
  have hfv := Submission.gwe_vertical_first_variation n ℓ hn U hU V H hH σ hσ hσU q hdist ζ hζ
    hζc hζs M hM j
/-- **Derivative bounds for a map that is `1`-Lipschitz on a closed ball** (Simon Ch. 5, proof of
4.5, (14)–(16), first step).  Let `f : ℝⁿ → ℝ^ℓ` be `1`-Lipschitz on `B_r(0)`, `|Df|² = hsNormSq Df`
and `fʲ = (f ·)_j`.  `x ↦ Df(x)` is measurable (`measurable_fderiv`) and `A ↦ |A|²` is continuous,
so `|Df|²` is measurable; so is `∇fʲ = (toDual)⁻¹ ∘ Dfʲ`.  `B_r(0)` is a neighbourhood of each point
of `B̆_r(0)`, so `‖Df‖ ≤ 1` there (`norm_fderiv_le_of_lipschitzOn`) and `|Df|² ≤ n`; each `fʲ` is
`1`-Lipschitz on `B_r(0)` as well (`|w_j| ≤ |w|`), so `|∇fʲ| = ‖Dfʲ‖ ≤ 1` on `B̆_r(0)`.  By
Rademacher's theorem `f` is differentiable at a.e. `x ∈ B̆_r(0)`; there `Dfʲ(x) = π_j ∘ Df(x)`, so
`|∇fʲ(x)|² = Σᵢ ((Df(x) eᵢ)_j)² ≤ Σᵢ |Df(x) eᵢ|² = |Df(x)|²`. -/
theorem gwe_wewe_lipschitz_fderiv_facts : ∀ (n ℓ : ℕ) (r : ℝ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 r) → Measurable (fun x => hsNormSq (fderiv ℝ f x)) ∧ (∀ j : Fin ℓ, Measurable (gradient (fun y => f y j))) ∧ (∀ x, 0 ≤ hsNormSq (fderiv ℝ f x)) ∧ (∀ x ∈ ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ n ∧ ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 r → ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
  intro n ℓ r f hf
  -- `B_r(0)` is a neighbourhood of every point of the open ball.
  have hnhds : ∀ x ∈ ball (0 : Rn n) r, closedBall (0 : Rn n) r ∈ 𝓝 x := fun x hx =>
    Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  -- Each coordinate `fʲ` is `1`-Lipschitz on `B_r(0)`, since `|w_j| ≤ |w|`.
  have hfj : ∀ j : Fin ℓ, LipschitzOnWith 1 (fun y => f y j) (closedBall 0 r) := by
    intro j
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    calc dist (f y j) (f z j) ≤ dist (f y) (f z) := PiLp.dist_apply_le _ _ _
      _ ≤ (1 : ℝ≥0) * dist y z := hf.dist_le_mul y hy z hz
  -- `|∇g(x)|² = Σᵢ (Dg(x) eᵢ)²`, since `(∇g(x))ᵢ = ⟪∇g(x), eᵢ⟫ = Dg(x) eᵢ`.
  have hgrad : ∀ (g : Rn n → ℝ) (x : Rn n),
      ‖gradient g x‖ ^ 2 = ∑ i, (fderiv ℝ g x (EuclideanSpace.single i 1)) ^ 2 := by
    intro g x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Rn n)
      (x := EuclideanSpace.single i 1) (y := fderiv ℝ g x)
    rw [EuclideanSpace.inner_single_right] at h
    rw [Real.norm_eq_abs, sq_abs]
    simpa [gradient] using congrArg (· ^ 2) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `|Df|²` is a continuous function of the measurable map `x ↦ Df(x)`.
    have hcont : Continuous fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A := by
      unfold hsNormSq
      fun_prop
    exact hcont.measurable.comp (measurable_fderiv ℝ f)
  · intro j
    exact (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (fun y => f y j))
  · intro x
    unfold hsNormSq
    positivity
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · -- `‖Df(x) eᵢ‖ ≤ ‖Df(x)‖ ‖eᵢ‖ ≤ 1` for each of the `n` summands.
      have h1 : ‖fderiv ℝ f x‖ ≤ 1 := by
        simpa using norm_fderiv_le_of_lipschitzOn ℝ (hnhds x hx) hf
      unfold hsNormSq
      calc ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ 1 := by
              calc _ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                    (fderiv ℝ f x).le_opNorm _
                _ ≤ 1 := by simpa using h1
            exact pow_le_one₀ (norm_nonneg _) this
        _ = n := by simp
    · -- The Riesz map `toDual` is an isometry, so `|∇fʲ(x)| = ‖Dfʲ(x)‖ ≤ 1`.
      have h1 : ‖fderiv ℝ (fun y => f y j) x‖ ≤ 1 := by
        simpa using norm_fderiv_le_of_lipschitzOn ℝ (hnhds x hx) (hfj j)
      simpa [gradient] using h1
  · -- Rademacher: `f` is differentiable within `B_r(0)`, hence at `x`, for a.e. `x ∈ B̆_r(0)`.
    filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxb j
    have hd : DifferentiableAt ℝ f x :=
      (hx (ball_subset_closedBall hxb)).differentiableAt (hnhds x hxb)
    have hfd : fderiv ℝ (fun y => f y j) x =
        (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp (fderiv ℝ f x) :=
      ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    rw [hgrad, hfd]
    unfold hsNormSq
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply, ← sq_abs]
    have h := PiLp.norm_apply_le (fderiv ℝ f x (EuclideanSpace.single i 1)) j
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
/-- Energy bound behind Simon Ch. 5, 4.5 (16), with the explicit constant `C_E = (1 + n) K0`.
Let `f : ℝⁿ → ℝ^ℓ` be `1`-Lipschitz on `closedBall 0 (σ / 2)`, `B1 = ball 0 (3σ/8)`, and `W`
measurable with `W = 0 ∨ 1 ≤ W` a.e. on `B1`, `Lⁿ(B1 ∩ {W = 0}) ≤ K0 E σⁿ` and
`∫⁻_{B1} |Df|² W ≤ K0 E σⁿ`.  Then `|Df|²` is integrable on `B1` and
`∫_{B1} |Df|² ≤ (1 + n) K0 E σⁿ`.
Since `0 ≤ |Df|² ≤ n` on `B1` (`lipschitz_fderiv_facts`), a.e. on `B1` we have
`|Df|² ≤ |Df|² W + n 1_{B1 ∩ {W = 0}}`; integrate and use the two hypotheses. -/
theorem gwe_wewe_energy_bound : ∀ (n ℓ : ℕ) (K0 σ E : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 ≤ K0 → 0 < σ → 0 ≤ E → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ 1 ≤ W x) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (3 * σ / 8)) ∧ ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ (1 + n) * K0 * E * σ ^ n := by
  intro n ℓ K0 σ E f W hK0 hσ hE hf hW hW01 hN hWE
  -- Step 1: `lipschitz_fderiv_facts` with `r = σ / 2`; since `B1 ⊆ ball 0 (σ / 2)`,
  -- `0 ≤ |Df|² ≤ n` on `B1`.
  obtain ⟨hmeas, -, hnonneg, hbound, -⟩ :=
    Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  set B1 : Set (Rn n) := ball (0 : Rn n) (3 * σ / 8)
  have hB1meas : MeasurableSet B1 := measurableSet_ball
  have hle : ∀ x ∈ B1, hsNormSq (fderiv ℝ f x) ≤ n := fun x hx =>
    (hbound x (ball_subset_ball (by linarith) hx)).1
  -- Step 2: `|Df|²` is measurable and bounded on the finite-measure ball `B1`.
  have hint : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) B1 := by
    refine Measure.integrableOn_of_bounded (M := n) measure_ball_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hB1meas] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact hle x hx
  refine ⟨hint, ?_⟩
  -- Step 3: `N = B1 ∩ {W = 0}` is a measurable subset of `B1`.
  set N : Set (Rn n) := B1 ∩ {x | W x = 0}
  have hNmeas : MeasurableSet N := hB1meas.inter (hW (measurableSet_singleton 0))
  have hNsub : N ⊆ B1 := inter_subset_left
  have ha : 0 ≤ K0 * E * σ ^ n := by positivity
  -- Step 4: a.e. on `B1`, `ofReal |Df|² ≤ ofReal (|Df|² W) + 1_N ofReal n`;
  -- split into the cases `W = 0` and `1 ≤ W`.
  have hpt : ∀ᵐ x ∂(volume.restrict B1), ENNReal.ofReal (hsNormSq (fderiv ℝ f x)) ≤
      ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) +
        N.indicator (fun _ => ENNReal.ofReal n) x := by
    rw [ae_restrict_iff' hB1meas]
    filter_upwards [hW01] with x hx hxB
    rcases hx hxB with h0 | h1
    · rw [indicator_of_mem (show x ∈ N from ⟨hxB, h0⟩)]
      exact le_add_left (ENNReal.ofReal_le_ofReal (hle x hxB))
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      calc hsNormSq (fderiv ℝ f x) = hsNormSq (fderiv ℝ f x) * 1 := (mul_one _).symm
        _ ≤ hsNormSq (fderiv ℝ f x) * W x := mul_le_mul_of_nonneg_left h1 (hnonneg x)
  -- Step 5: integrate over `B1`; (H3) and (H2) bound the two terms.
  have hlint : ∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x)) ≤
      ENNReal.ofReal ((1 + n) * K0 * E * σ ^ n) := by
    calc ∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x))
        ≤ ∫⁻ x in B1, (ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) +
            N.indicator (fun _ => ENNReal.ofReal n) x) := lintegral_mono_ae hpt
      _ = (∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x)) +
            ENNReal.ofReal n * volume N := by
          rw [lintegral_add_right _ (measurable_const.indicator hNmeas),
            lintegral_indicator_const hNmeas, Measure.restrict_apply hNmeas,
            inter_eq_left.mpr hNsub]
      _ ≤ ENNReal.ofReal (K0 * E * σ ^ n) + ENNReal.ofReal n * ENNReal.ofReal (K0 * E * σ ^ n) := by
          gcongr
      _ = ENNReal.ofReal ((1 + n) * K0 * E * σ ^ n) := by
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n),
            ← ENNReal.ofReal_add ha (mul_nonneg (Nat.cast_nonneg n) ha)]
          congr 1
          ring
  -- Step 6: `∫_{B1} |Df|² = (∫⁻_{B1} ofReal |Df|²).toReal ≤ (1 + n) K0 E σⁿ`.
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnonneg) hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
/-- Cauchy–Schwarz on a set of finite measure (Hölder with `p = q = 2` for `g` and `1` on
`ν = μ|_S`): if `0 ≤ g` and `g² ≤ D` a.e. on `S`, with `D` integrable on `S`, then
`∫_S g dμ ≤ (∫_S g² dμ)^{1/2} μ(S)^{1/2} ≤ μ(S)^{1/2} (∫_S D dμ)^{1/2}`. -/
theorem gwe_wewe_setIntegral_le_sqrt_mul_sqrt : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (g D : X → ℝ), μ S < ⊤ → AEStronglyMeasurable g (μ.restrict S) → IntegrableOn D S μ → (∀ᵐ x ∂(μ.restrict S), 0 ≤ g x ∧ g x ^ 2 ≤ D x) → ∫ x in S, g x ∂μ ≤ Real.sqrt (μ S).toReal * Real.sqrt (∫ x in S, D x ∂μ) := by
  intro X _ μ S g D hS hg hD hgD
  -- `ν = μ|_S` is a finite measure.
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  -- `g²` is `ν`-integrable, being dominated by the integrable `D`.
  have hg2 : Integrable (fun x => g x ^ 2) (μ.restrict S) :=
    Integrable.mono' hD (hg.pow 2)
      (hgD.mono fun x hx => (Real.norm_of_nonneg (sq_nonneg (g x))).le.trans hx.2)
  -- Hence `g ∈ L²(ν)`.
  have hgL2 : MemLp g (ENNReal.ofReal 2) (μ.restrict S) := by
    rw [← integrable_norm_rpow_iff hg (by simp) ENNReal.ofReal_ne_top]
    refine hg2.congr (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal zero_le_two, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  -- Hölder with `p = q = 2` for `g` and the constant `1 ∈ L²(ν)`.
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (f := g) (g := fun _ => (1 : ℝ))
    Real.HolderConjugate.two_two (hgD.mono fun x hx => hx.1) (ae_of_all _ fun _ => zero_le_one)
    hgL2 (memLp_const 1)
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply_univ, ← Real.sqrt_eq_rpow] at hH
  -- `∫_S g² ≤ ∫_S D`, and `√` is monotone.
  have hmono : ∫ x in S, g x ^ 2 ∂μ ≤ ∫ x in S, D x ∂μ :=
    integral_mono_ae hg2 hD (hgD.mono fun x hx => hx.2)
  calc ∫ x in S, g x ∂μ ≤ Real.sqrt (∫ x in S, g x ^ 2 ∂μ) * Real.sqrt (μ S).toReal := hH
    _ ≤ Real.sqrt (∫ x in S, D x ∂μ) * Real.sqrt (μ S).toReal :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)
    _ = Real.sqrt (μ S).toReal * Real.sqrt (∫ x in S, D x ∂μ) := mul_comm _ _
/-- Simon 4.5 (15): the error made by dropping the weight `W` in the weak equation
(steps 4-6 of `gwe_weighted_energy_weak_equation`). -/
theorem gwe_wewe_weight_error_bound : ∀ (n ℓ : ℕ) (cJ σ κ M : ℝ) (f : Rn n → Rn ℓ) (W ζ : Rn n → ℝ) (j : Fin ℓ), 0 ≤ cJ → 0 < σ → 0 ≤ κ → κ ≤ 1 → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → (∀ x, ‖gradient ζ x‖ ≤ M) → |(∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)) - ∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal + M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) + 2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
  intro n ℓ cJ σ κ M f W ζ j hcJ hσ hκ0 hκ1 hf hW hH1 hζ
  -- Sibling `lipschitz_fderiv_facts` with `r = σ / 2`.
  obtain ⟨hDm, hGm, hD0, hbd, -⟩ := Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  -- `B₂ = ball 0 (σ/4) ⊆ B₁ = ball 0 (3σ/8) ⊆ ball 0 (σ/2)`.
  have hB21 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (3 * σ / 8) := ball_subset_ball (by linarith)
  have hB1h : ball (0 : Rn n) (3 * σ / 8) ⊆ ball 0 (σ / 2) := ball_subset_ball (by linarith)
  have hB2fin : volume (ball (0 : Rn n) (σ / 4)) ≠ ∞ := measure_ball_lt_top.ne
  have hM : 0 ≤ M := (norm_nonneg _).trans (hζ 0)
  -- Measurability of `∇ζ = (toDual)⁻¹ ∘ Dζ` and of `u = ⟨∇f^j, ∇ζ⟩`.
  have hζm : Measurable (gradient ζ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ ζ)
  have hum : Measurable fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) :=
    continuous_inner.measurable.comp ((hGm j).prodMk hζm)
  -- `|u| ≤ M ‖∇f^j‖` (Cauchy–Schwarz).
  have hu_le : ∀ x, |inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤
      M * ‖gradient (fun y => f y j) x‖ := fun x =>
    (abs_real_inner_le_norm _ _).trans <| by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hζ x) (norm_nonneg _)
  -- Integrability on `B₂` of `u`, `‖∇f^j‖`, `|Df|²` and `M 𝟙_N`, `N = B₁ ∩ {W = 0}`.
  have hu_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x))
      (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := M) hB2fin hum.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs]
    exact (hu_le x).trans (mul_le_of_le_one_right hM ((hbd x (hB1h (hB21 hx))).2 j))
  have hG_int : IntegrableOn (fun x => ‖gradient (fun y => f y j) x‖)
      (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := 1) hB2fin (hGm j).norm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [norm_norm]
    exact (hbd x (hB1h (hB21 hx))).2 j
  have hD_int : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := n) hB2fin hDm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 x)]
    exact (hbd x (hB1h (hB21 hx))).1
  have hN : MeasurableSet (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) :=
    measurableSet_ball.inter (measurableSet_eq_fun hW measurable_const)
  have hI_int : IntegrableOn ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator fun _ => M)
      (ball (0 : Rn n) (σ / 4)) :=
    (integrableOn_const hB2fin).indicator hN
  have hIG_int : IntegrableOn (fun x => (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
      (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖) (ball (0 : Rn n) (σ / 4)) :=
    hI_int.add (hG_int.const_mul (M * κ))
  have hh_int : IntegrableOn (fun x => (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
      (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x))
      (ball (0 : Rn n) (σ / 4)) :=
    hIG_int.add (hD_int.const_mul (2 * cJ * M))
  -- Pointwise error: `|u - uW| ≤ M 𝟙_N + M κ ‖∇f^j‖ + 2 cJ M |Df|²` a.e. on `B₂`.
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (σ / 4))),
      ‖inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x‖ ≤
        (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x +
          M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hH1] with x hx hHx
    have hx1 : x ∈ ball (0 : Rn n) (3 * σ / 8) := hB21 hx
    have hG1 : ‖gradient (fun y => f y j) x‖ ≤ 1 := (hbd x (hB1h hx1)).2 j
    have hG0 : 0 ≤ ‖gradient (fun y => f y j) x‖ := norm_nonneg _
    have hDx : 0 ≤ hsNormSq (fderiv ℝ f x) := hD0 x
    have hux := hu_le x
    have hκG : 0 ≤ M * κ * ‖gradient (fun y => f y j) x‖ := by positivity
    have hcD : 0 ≤ 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by positivity
    rw [Real.norm_eq_abs]
    rcases hHx hx1 with h0 | ⟨h1, h2⟩
    · -- `W x = 0`: then `x ∈ N` and `|u - uW| = |u| ≤ M`.
      rw [indicator_of_mem (show x ∈ ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0} from ⟨hx1, h0⟩),
        h0, mul_zero, sub_zero]
      have hMG : M * ‖gradient (fun y => f y j) x‖ ≤ M := mul_le_of_le_one_right hM hG1
      linarith
    · -- `1 ≤ W x ≤ (1 + κ)(1 + cJ |Df|²)`: then `x ∉ N` and `|u - uW| = |u| (W - 1)`.
      rw [indicator_of_notMem (fun h : x ∈ ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0} => by
        have h' : W x = 0 := h.2
        linarith), zero_add]
      have hw1 : 0 ≤ W x - 1 := by linarith
      have hwκ : W x - 1 ≤ κ + 2 * cJ * hsNormSq (fderiv ℝ f x) := by
        nlinarith [mul_le_mul_of_nonneg_right (show 1 + κ ≤ 2 by linarith) (mul_nonneg hcJ hDx)]
      rw [show inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
            inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x =
          -(inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * (W x - 1)) by ring,
        abs_neg, abs_mul, abs_of_nonneg hw1]
      calc |inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| * (W x - 1)
          ≤ M * ‖gradient (fun y => f y j) x‖ * (κ + 2 * cJ * hsNormSq (fderiv ℝ f x)) :=
            mul_le_mul hux hwκ hw1 (mul_nonneg hM hG0)
        _ = M * κ * ‖gradient (fun y => f y j) x‖ +
              2 * cJ * M * hsNormSq (fderiv ℝ f x) * ‖gradient (fun y => f y j) x‖ := by ring
        _ ≤ M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by
            linarith [mul_le_of_le_one_right hcD hG1]
  -- `uW = u - (u - uW)` is integrable on `B₂`.
  have hdiff_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
      inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x) (ball (0 : Rn n) (σ / 4)) :=
    Integrable.mono' hh_int (hum.sub (hum.mul hW)).aestronglyMeasurable hpt
  have huW_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)
      (ball (0 : Rn n) (σ / 4)) := by
    refine (hu_int.sub hdiff_int).congr ?_
    filter_upwards with x
    simp
  -- The indicator term: `∫_{B₂} M 𝟙_N = M Lⁿ(N ∩ B₂) ≤ M Lⁿ(N)`.
  have hNfin : volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hI : ∫ x in ball (0 : Rn n) (σ / 4),
      (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x ≤
      M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal := by
    rw [integral_indicator_const M hN, measureReal_restrict_apply hN, smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_left hNfin) hM
  -- Integrate the pointwise error.
  calc |(∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)) -
        ∫ x in ball (0 : Rn n) (σ / 4),
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x|
      = ‖∫ x in ball (0 : Rn n) (σ / 4), (inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)‖ := by
        rw [integral_sub hu_int huW_int, Real.norm_eq_abs]
    _ ≤ ∫ x in ball (0 : Rn n) (σ / 4), ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
          (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖ +
          2 * cJ * M * hsNormSq (fderiv ℝ f x)) :=
        norm_integral_le_of_norm_le hh_int hpt
    _ = (∫ x in ball (0 : Rn n) (σ / 4),
          (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x) +
          M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) +
          2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
        rw [integral_add hIG_int (hD_int.const_mul (2 * cJ * M)),
          integral_add hI_int (hG_int.const_mul (M * κ)), integral_const_mul, integral_const_mul]
    _ ≤ M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal +
          M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) +
          2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
        linarith
/-- Simon Ch. 5, 4.5 (14)–(16) in the parameter domain: from the weighted estimates
`Lⁿ(B̆_{3σ/8} ∩ {W = 0}) ≤ K₀Eσⁿ` and `∫_{B̆_{3σ/8}} |Df|² W ≤ K₀Eσⁿ` to the unweighted energy
bound `∫_{B̆_{3σ/8}} |Df|² ≤ CEσⁿ` and the approximate weak equation
`|∫_{B̆_{σ/4}} ⟨∇fʲ, ∇ζ⟩| ≤ C(E + h + κ√E)Mσⁿ`.  The constant is
`C = max {C_E, 2K₀ + 2c_J C_E, √(ω C_E), 1}` with `C_E = (1 + n)K₀` and `ω = Lⁿ(B̆₁(0))`. -/
theorem gwe_weighted_energy_weak_equation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ K0 cJ : ℝ, 0 ≤ K0 → 0 ≤ cJ → ∃ C : ℝ, 0 < C ∧ ∀ (σ κ E h : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 < σ → 0 ≤ κ → κ ≤ 1 → 0 ≤ E → 0 ≤ h → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → (∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ C * E * σ ^ n) ∧ ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ K0 * (E + h) * M * σ ^ n → |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by
  intro n ℓ _ K0 cJ hK0 hcJ
  -- The constants depend only on `n`, `K0` and `cJ`.
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Rn n) 1)).toReal := ⟨_, rfl⟩
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = (1 + n) * K0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = max (max CE (2 * K0 + 2 * cJ * CE)) (max (Real.sqrt (ω * CE)) 1) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; exact ENNReal.toReal_nonneg
  have hCE0 : 0 ≤ CE := by rw [hCE]; positivity
  have hCEC : CE ≤ C := by rw [hC]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hKC : 2 * K0 + 2 * cJ * CE ≤ C := by
    rw [hC]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hsqC : Real.sqrt (ω * CE) ≤ C := by
    rw [hC]; exact (le_max_left _ _).trans (le_max_right _ _)
  have h1C : 1 ≤ C := by rw [hC]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hK0C : K0 ≤ C := by linarith [mul_nonneg hcJ hCE0]
  refine ⟨C, one_pos.trans_le h1C, ?_⟩
  intro σ κ E h f W hσ hκ0 hκ1 hE hh hf hW hH1 hH2 hH3
  have hσn : 0 ≤ σ ^ n := pow_nonneg hσ.le n
  have hKE : 0 ≤ K0 * E * σ ^ n := by positivity
  -- Step 1: derivative facts on `B̆_{σ/2}(0)`.
  obtain ⟨-, hGmeas, hDnn, -, hae⟩ := Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  -- Steps 2–3: the unweighted energy bound, with constant `C_E = (1 + n) K0`.
  have hH1' : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ 1 ≤ W x := by
    filter_upwards [hH1] with x hx hxB
    exact (hx hxB).imp id And.left
  obtain ⟨hDint, hEnergy⟩ :=
    Submission.gwe_wewe_energy_bound n ℓ K0 σ E f W hK0 hσ hE hf hW hH1' hH2 hH3
  refine ⟨?_, ?_⟩
  · calc ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x)
        ≤ (1 + n) * K0 * E * σ ^ n := hEnergy
      _ = CE * (E * σ ^ n) := by rw [hCE]; ring
      _ ≤ C * (E * σ ^ n) := mul_le_mul_of_nonneg_right hCEC (mul_nonneg hE hσn)
      _ = C * E * σ ^ n := by ring
  -- Steps 4–7: the weak equation.
  intro ζ _ _ _ M hM j hWeq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have herr := Submission.gwe_wewe_weight_error_bound n ℓ cJ σ κ M f W ζ j hcJ hσ hκ0 hκ1 hf hW
    hH1 hM
  have hN : (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal ≤ K0 * E * σ ^ n :=
    ENNReal.toReal_le_of_le_ofReal hKE hH2
  have hB21 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (3 * σ / 8) := ball_subset_ball (by linarith)
  have hB2 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (σ / 2) := ball_subset_ball (by linarith)
  have hD2 : ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) ≤ CE * E * σ ^ n :=
    calc ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)
        ≤ ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) :=
          setIntegral_mono_set hDint (ae_of_all _ hDnn) hB21.eventuallyLE
      _ ≤ (1 + n) * K0 * E * σ ^ n := hEnergy
      _ = CE * E * σ ^ n := by rw [hCE]
  -- Cauchy–Schwarz on `B̆_{σ/4}(0)`, with `‖∇fʲ‖² ≤ |Df|²` a.e.
  have hG : ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖ ≤
      Real.sqrt (volume (ball (0 : Rn n) (σ / 4))).toReal *
        Real.sqrt (∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)) := by
    refine Submission.gwe_wewe_setIntegral_le_sqrt_mul_sqrt (Rn n) volume (ball 0 (σ / 4))
      (fun x => ‖gradient (fun y => f y j) x‖) (fun x => hsNormSq (fderiv ℝ f x))
      measure_ball_lt_top (hGmeas j).norm.aestronglyMeasurable (hDint.mono_set hB21) ?_
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hae] with x hx hxB
    exact ⟨norm_nonneg _, hx (hB2 hxB) j⟩
  have hvol : (volume (ball (0 : Rn n) (σ / 4))).toReal ≤ ω * σ ^ n := by
    have hσ4 : (0 : ℝ) < σ / 4 := by positivity
    rw [Measure.addHaar_ball_of_pos volume (0 : Rn n) hσ4, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hσ4.le n), ← hω, mul_comm ω]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ4.le (by linarith) n) hω0
  have hGb : ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖ ≤
      Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E :=
    calc ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖
        ≤ Real.sqrt (volume (ball (0 : Rn n) (σ / 4))).toReal *
            Real.sqrt (∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)) := hG
      _ ≤ Real.sqrt (ω * σ ^ n) * Real.sqrt (CE * E * σ ^ n) :=
          mul_le_mul (Real.sqrt_le_sqrt hvol) (Real.sqrt_le_sqrt hD2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E := by
          rw [← Real.sqrt_mul (mul_nonneg hω0 hσn),
            show ω * σ ^ n * (CE * E * σ ^ n) = (σ ^ n) ^ 2 * (ω * CE * E) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσn, Real.sqrt_mul (mul_nonneg hω0 hCE0)]
          ring
  -- Collect the terms.
  have h1 := mul_le_mul_of_nonneg_left hN hM0
  have h2 := mul_le_mul_of_nonneg_left hGb (mul_nonneg hM0 hκ0)
  have h3 := mul_le_mul_of_nonneg_left hD2 (mul_nonneg (mul_nonneg zero_le_two hcJ) hM0)
  have hfinal : K0 * (E + h) * M * σ ^ n + (M * (K0 * E * σ ^ n) +
      M * κ * (Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E) + 2 * cJ * M * (CE * E * σ ^ n)) ≤
      C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by
    have e1 := mul_le_mul_of_nonneg_right hKC hE
    have e2 := mul_le_mul_of_nonneg_right hK0C hh
    have e3 := mul_le_mul_of_nonneg_right hsqC (mul_nonneg hκ0 (Real.sqrt_nonneg E))
    calc K0 * (E + h) * M * σ ^ n + (M * (K0 * E * σ ^ n) +
          M * κ * (Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E) + 2 * cJ * M * (CE * E * σ ^ n))
        = ((2 * K0 + 2 * cJ * CE) * E + K0 * h + Real.sqrt (ω * CE) * (κ * Real.sqrt E)) *
            (M * σ ^ n) := by ring
      _ ≤ C * (E + h + κ * Real.sqrt E) * (M * σ ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hM0 hσn)
      _ = C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by ring
  have key := abs_sub_abs_le_abs_sub
    (∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x))
    (∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)
  linarith

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
