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

/-- **Simon Ch. 1, Theorem 1.17 (Lusin), as used in Ch. 3, Remark 1.8(1)**: a Borel set `A` with
`Hⁿ(A) < ∞` is, up to an `Hⁿ`-null set, a countable union of closed sets `C i ⊆ A` on each of which
the Borel function `ϑ` is continuous.  Proof: Lusin's theorem is proved inline (SimonGMT's
`Chapter01` Lusin theorem is not in the frozen import closure) for the finite, hence weakly regular,
measure `ν = Hⁿ ⌞ A`: for each rational interval `I_q` take closed `F_q ⊆ A ∩ ϑ⁻¹(I_q)` and
`F'_q ⊆ A \ ϑ⁻¹(I_q)` with `ν(A \ (F_q ∪ F'_q)) ≤ δ_q`, `∑ δ_q < 1/m`; `ϑ` is continuous on
`C m = ⋂_q (F_q ∪ F'_q)` and `Hⁿ(A \ C m) < 1/m`, so `Hⁿ(A \ ⋃ C m) = 0`. -/
theorem rsod_wfu_lusin_closed_exhaustion : ∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Measurable ϑ → ∃ C : ℕ → Set (Amb n ℓ), (∀ i, IsClosed (C i) ∧ C i ⊆ A ∧ ContinuousOn ϑ (C i)) ∧ (μHE[n] : Measure (Amb n ℓ)) (A \ ⋃ i, C i) = 0 := by
  intro n ℓ A ϑ hA hAfin hϑ
  -- Lusin's theorem (Simon 1.17) for `ϑ` on `A` and a finite Borel measure.
  have lusin : ∀ (ν : Measure (Amb n ℓ)), IsFiniteMeasure ν → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε ∧ ContinuousOn ϑ C := by
    intro ν hν ε hε
    have : ν.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
    obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × ℚ)
    -- For each rational interval, closed sets inside the parts of `A` where `ϑ` is in / not in it.
    have hsplit : ∀ q : ℚ × ℚ, ∃ F ⊆ A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F ∧
        ∃ F' ⊆ A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F' ∧ ν (A \ (F ∪ F')) ≤ δ q := by
      intro q
      have hP : MeasurableSet (A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.inter (hϑ measurableSet_Ioo)
      have hN : MeasurableSet (A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.diff (hϑ measurableSet_Ioo)
      have hδ2 : (δ q : ℝ≥0∞) / 2 ≠ 0 :=
        (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos q).ne')).ne'
      obtain ⟨F, hFP, hFc, hF⟩ := hP.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      obtain ⟨F', hFN, hF'c, hF'⟩ := hN.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      refine ⟨F, hFP, hFc, F', hFN, hF'c, ?_⟩
      calc ν (A \ (F ∪ F'))
          ≤ ν ((A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F ∪ (A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') := by
            refine measure_mono fun x hx => ?_
            by_cases hϑx : ϑ x ∈ Ioo (q.1 : ℝ) q.2
            · exact Or.inl ⟨⟨hx.1, hϑx⟩, fun h => hx.2 (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hϑx⟩, fun h => hx.2 (Or.inr h)⟩
        _ ≤ ν ((A ∩ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F) + ν ((A \ ϑ ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') :=
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
      obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show ϑ x - e < ϑ x by linarith)
      obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show ϑ x < ϑ x + e by linarith)
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
  -- Closed `C m ⊆ A` with `ϑ` continuous on `C m` and `Hⁿ(A \ C m) < 1/m`, from `ν = Hⁿ ⌞ A`.
  have hC : ∀ m : ℕ, ∃ C ⊆ A, IsClosed C ∧
      (μHE[n] : Measure (Amb n ℓ)) (A \ C) < (m : ℝ≥0∞)⁻¹ ∧ ContinuousOn ϑ C := by
    intro m
    obtain ⟨C, hCA, hCc, hCμ, hCf⟩ := lusin ((μHE[n] : Measure (Amb n ℓ)).restrict A)
      (isFiniteMeasure_restrict.2 hAfin.ne) (m : ℝ≥0∞)⁻¹
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    refine ⟨C, hCA, hCc, ?_, hCf⟩
    rwa [Measure.restrict_apply (hA.diff hCc.measurableSet), inter_eq_left.2 sdiff_subset] at hCμ
  choose C hCA hCc hCμ hCf using hC
  refine ⟨C, fun i => ⟨hCc i, hCA i, hCf i⟩, ?_⟩
  by_contra h
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h
  exact lt_asymm hm ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion C m))).trans_lt (hCμ m))
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

/-- **Ball-mass bound at an approximate tangent plane** (Simon Ch. 3, Remark 1.5(3)).  If
`Hⁿ(C) < ∞` and `T_x C = P`, then for each `R > 0` the ratios `r⁻ⁿ Hⁿ(C ∩ B_{rR}(x))` are
eventually bounded as `r ↓ 0`: test Definition 1.4 against a cutoff `g ∈ C_c` with `0 ≤ g ≤ 1`
and `g = 1` on `B_R(0)`, and pull `∫_{η(C)} g dHⁿ` back to `C` by the blow-up change of
variables. -/
theorem rsod_wfu_approxTangent_ballMass_bound : ∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), (μHE[n] : Measure (Amb n ℓ)) C < ∞ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → ∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ := by
  intro n ℓ C x P hC hT R _
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  -- The cutoff `g(y) = max(0, min(1, R + 1 - ‖y‖))`: continuous, `0 ≤ g ≤ 1`, `g = 1` on
  -- `B_R(0)` and `g = 0` off the compact ball `B_{R+1}(0)`.
  obtain ⟨g, hg_cont, hg_supp, hg_nonneg, hg_le_one, hg_one⟩ : ∃ g : Amb n ℓ → ℝ,
      Continuous g ∧ HasCompactSupport g ∧ (∀ y, 0 ≤ g y) ∧ (∀ y, g y ≤ 1) ∧
        ∀ y, ‖y‖ ≤ R → g y = 1 := by
    refine ⟨fun y => max 0 (min 1 (R + 1 - ‖y‖)),
      continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm)),
      HasCompactSupport.intro (isCompact_closedBall (0 : Amb n ℓ) (R + 1)) fun y hy => ?_,
      fun y => le_max_left _ _, fun y => max_le zero_le_one (min_le_left _ _), fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact max_eq_left ((min_le_right _ _).trans (by linarith))
    · show max 0 (min 1 (R + 1 - ‖y‖)) = 1
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- `T_x C = P` tested on `g`: eventually `∫_{η_r(C)} g dHⁿ < ∫_P g dHⁿ + 1`.
  have hlim : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' C, g y ∂μ)
      (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), g y ∂μ)) :=
    hT.2 ⟨⟨g, hg_cont⟩, hg_supp⟩
  refine ⟨(∫ y in (P : Set (Amb n ℓ)), g y ∂μ) + 1, ?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one _)), self_mem_nhdsWithin]
    with r hr (hr0 : 0 < r)
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  -- Change of variables with `θ ≡ 1`: `∫_{η(C)} g dHⁿ = r⁻ⁿ ∫_C g ∘ η dHⁿ`.
  have hcov := rsod_blowUp_setIntegral_eq n ℓ C g (fun _ => 1) x r hr0
  simp only [mul_one] at hcov
  -- `1_B ≤ g ∘ η` for `B = B_{rR}(x)`, since `‖η z‖ = r⁻¹ ‖z - x‖ ≤ R` on `B`.
  have hB : MeasurableSet (closedBall x (r * R)) := measurableSet_closedBall
  have hle : ∀ z, (closedBall x (r * R)).indicator 1 z ≤ g (η z) := by
    intro z
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz, Pi.one_apply, hg_one]
      rw [hη, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), ← dist_eq_norm]
      calc r⁻¹ * dist z x ≤ r⁻¹ * (r * R) :=
            mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) (inv_nonneg.mpr hr0.le)
        _ = R := inv_mul_cancel_left₀ hr0.ne' R
    · rw [indicator_of_notMem hz]
      exact hg_nonneg _
  -- Both sides are `Hⁿ ⌞ C`-integrable because `Hⁿ(C) < ∞`, so `Hⁿ(C ∩ B) ≤ ∫_C g ∘ η dHⁿ`.
  have hmass : μ.real (C ∩ closedBall x (r * R)) ≤ ∫ z in C, g (η z) ∂μ := by
    have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.ne
    have hηcont : Continuous η := (continuous_id.sub continuous_const).const_smul r⁻¹
    have h1 : Integrable ((closedBall x (r * R)).indicator (1 : Amb n ℓ → ℝ)) (μ.restrict C) :=
      (integrable_const (1 : ℝ)).indicator hB
    have h2 : Integrable (fun z => g (η z)) (μ.restrict C) :=
      (integrable_const (1 : ℝ)).mono' (hg_cont.comp hηcont).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_of_nonneg (hg_nonneg _)]; exact hg_le_one _)
    calc μ.real (C ∩ closedBall x (r * R))
        = ∫ z in C, (closedBall x (r * R)).indicator 1 z ∂μ := by
          rw [integral_indicator_one hB, measureReal_restrict_apply hB, inter_comm]
      _ ≤ ∫ z in C, g (η z) ∂μ := integral_mono h1 h2 hle
  calc (r ^ n)⁻¹ * μ.real (C ∩ closedBall x (r * R))
      ≤ (r ^ n)⁻¹ * ∫ z in C, g (η z) ∂μ :=
        mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr (pow_nonneg hr0.le n))
    _ = ∫ y in η '' C, g y ∂μ := hcov.symm
    _ ≤ (∫ y in (P : Set (Amb n ℓ)), g y ∂μ) + 1 := hr.le
/-- **Vanishing of the blow-up tail** (Simon Ch. 3, Remark 1.8(1), with Ch. 1, Thm 3.6).  If the
weighted measure `μ' = |ϑ| Hⁿ ⌞ A` satisfies `ρ⁻ⁿ μ'(S ∩ B_ρ(x)) → 0` as `ρ ↓ 0`, with `S ⊆ A` Borel
and `ϑ ∈ L¹(Hⁿ ⌞ A)`, then `r⁻ⁿ ∫_S f(η_{x,r} z) ϑ(z) dHⁿ(z) → 0` for every `f ∈ C_c`.  Indeed
`|f| ≤ M` and `f = 0` off `B_R(0)`, so the integral is bounded by `M μ'(S ∩ B_{rR}(x))`, and
`r⁻ⁿ M μ'(S ∩ B_{rR}(x)) = M Rⁿ (rR)⁻ⁿ μ'(S ∩ B_{rR}(x)) → 0`. -/
theorem rsod_wfu_blowUp_tail_tendsto_zero : ∀ (n ℓ : ℕ) (A S : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet S → S ⊆ A → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real (S ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ A S ϑ x hS hSA hϑ hdens f
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set μ' : Measure (Amb n ℓ) := (μ.restrict A).withDensity (fun z => ‖ϑ z‖ₑ) with hμ'
  -- `|f| ≤ M` everywhere, and `f = 0` off `B_R(0)` with `R > 0`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ y, ‖f y‖ ≤ M :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  set R : ℝ := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- `μ'(T) = ∫_T |ϑ| dHⁿ` for Borel `T ⊆ A`.
  have hreal : ∀ T : Set (Amb n ℓ), MeasurableSet T → T ⊆ A →
      ∫ z in T, ‖ϑ z‖ ∂μ = μ'.real T := by
    intro T hT hTA
    rw [measureReal_def, hμ', withDensity_apply _ hT, Measure.restrict_restrict hT,
      inter_eq_left.mpr hTA,
      integral_norm_eq_lintegral_enorm (hϑ.mono_set hTA).aestronglyMeasurable]
  -- Pointwise: `|f(η_r z) ϑ(z)| ≤ M 1_{B_{rR}(x)}(z) |ϑ(z)|`.
  have hpt : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ,
      ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z‖ ≤
        (closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖) z := by
    intro r hr z
    by_cases hz : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [indicator_of_notMem hz]
      have hf0 : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hz
        have h1 := hR₀ hmem
        rw [mem_closedBall_zero_iff] at h1
        rw [mem_closedBall, dist_eq_norm]
        have hzx : z - x = r • Poincare.SimonGMT.Chapter03.blowUpMap x r z := by
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
        calc r * ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ r * R₀ :=
              mul_le_mul_of_nonneg_left h1 hr.le
          _ ≤ r * R := mul_le_mul_of_nonneg_left (le_max_left _ _) hr.le
      rw [hf0, zero_mul, norm_zero]
  -- Integral bound: `|∫_S f(η_r z) ϑ(z) dHⁿ| ≤ M μ'(S ∩ B_{rR}(x))`.
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖ ≤
        M * μ'.real (S ∩ closedBall x (r * R)) := by
    intro r hr
    have hint : Integrable ((closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖))
        (μ.restrict S) :=
      ((hϑ.mono_set hSA).norm.const_mul M).indicator measurableSet_closedBall
    calc ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖
        ≤ ∫ z in S, (closedBall x (r * R)).indicator (fun z => M * ‖ϑ z‖) z ∂μ :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall (hpt r hr))
      _ = ∫ z in S ∩ closedBall x (r * R), M * ‖ϑ z‖ ∂μ :=
          setIntegral_indicator measurableSet_closedBall
      _ = M * ∫ z in S ∩ closedBall x (r * R), ‖ϑ z‖ ∂μ := integral_const_mul _ _
      _ = M * μ'.real (S ∩ closedBall x (r * R)) := by
          rw [hreal _ (hS.inter measurableSet_closedBall) (inter_subset_left.trans hSA)]
  -- Rescaling `ρ = rR` turns the density hypothesis into the decay of the bound.
  have hscale : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hlim := (hdens.comp hscale).const_mul (M * R ^ n)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hRn : R ^ n ≠ 0 := pow_ne_zero _ hRpos.ne'
  rw [norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hr.le]
  calc (r ^ n)⁻¹ * ‖∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z ∂μ‖
      ≤ (r ^ n)⁻¹ * (M * μ'.real (S ∩ closedBall x (r * R))) :=
        mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)
    _ = M * R ^ n * (((r * R) ^ n)⁻¹ * μ'.real (S ∩ closedBall x (r * R))) := by
        rw [mul_pow, mul_inv]
        field_simp
/-- **Freezing a relatively continuous weight in blow-ups** (Simon Ch. 3, Remark 1.8(1)).  Let `C`
be Borel with `Hⁿ(C) < ∞`, `ϑ` continuous at `x` relative to `C`, and `r⁻ⁿ Hⁿ(C ∩ B_{rR}(x))`
eventually bounded as `r ↓ 0` for each `R > 0`.  Then for `f ∈ C_c` and `η = η_{x,r}`,
`r⁻ⁿ ∫_C f(η z) (ϑ(z) − ϑ(x)) dHⁿ(z) → 0` as `r ↓ 0`.  With `|f| ≤ M` and `spt f ⊆ B_R(0)`, the
integrand vanishes off `B_{rR}(x)` and is at most `M ε'` on `C ∩ B_{rR}(x)` once `rR < δ`, so the
quantity is at most `M ε' Λ`. -/
theorem rsod_wfu_blowUp_freeze_weight_tendsto_zero : ∀ (n ℓ : ℕ) (C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ), MeasurableSet C → (μHE[n] : Measure (Amb n ℓ)) C < ∞ → ContinuousWithinAt ϑ C x → (∀ R : ℝ, 0 < R → ∃ Λ : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ n)⁻¹ * (μHE[n] : Measure (Amb n ℓ)).real (C ∩ closedBall x (r * R)) ≤ Λ) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ C ϑ x hC hCfin hϑ hdens f
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  -- `|f| ≤ M`, and `f` vanishes outside `B_R(0)` with `R ≥ 1`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ y, ‖f y‖ ≤ M :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  set R := max R₀ 1
  have hR : 0 < R := lt_max_of_lt_right one_pos
  have hfR : ∀ y : Amb n ℓ, R < ‖y‖ → f y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hy' => ?_
    have := hR₀ hy'
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R₀ 1]
  -- Bounded density ratio at scale `R`.
  obtain ⟨Λ, hΛ⟩ := hdens R hR
  set Λ' := max Λ 0
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hCfin.ne
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / ((M + 1) * (Λ' + 1)) with hε'eq
  have hMΛ : 0 < (M + 1) * (Λ' + 1) := mul_pos (by linarith) (by linarith)
  have hε' : 0 < ε' := div_pos hε hMΛ
  obtain ⟨δ, hδ, hδϑ⟩ := Metric.continuousWithinAt_iff.mp hϑ ε' hε'
  filter_upwards [hΛ, Ioo_mem_nhdsGT (div_pos hδ hR)] with r hrΛ hr
  obtain ⟨hr0, hrδ⟩ := hr
  have hrRδ : r * R < δ := by rwa [lt_div_iff₀ hR] at hrδ
  -- Pointwise bound on `C` by `M ε'` times the indicator of `B_{rR}(x)`.
  have hpt : ∀ z ∈ C, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x)‖ ≤
      (closedBall x (r * R)).indicator (fun _ => M * ε') z := by
    intro z hz
    by_cases hzB : z ∈ closedBall x (r * R)
    · rw [indicator_of_mem hzB, norm_mul]
      have h2 : ‖ϑ z - ϑ x‖ ≤ ε' := by
        rw [← dist_eq_norm]
        exact (hδϑ hz (lt_of_le_of_lt (mem_closedBall.mp hzB) hrRδ)).le
      exact mul_le_mul (hM _) h2 (norm_nonneg _) hM0
    · rw [indicator_of_notMem hzB]
      have hf0 : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
        apply hfR
        rw [mem_closedBall, not_le] at hzB
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
          ← dist_eq_norm, lt_inv_mul_iff₀ hr0]
        exact hzB
      simp [hf0]
  -- Integral bound.
  have hint : ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖ ≤
      M * ε' * μ.real (C ∩ closedBall x (r * R)) := by
    calc ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖
        ≤ ∫ z in C, (closedBall x (r * R)).indicator (fun _ => M * ε') z ∂μ :=
          norm_integral_le_of_norm_le ((integrable_const _).indicator measurableSet_closedBall)
            (ae_restrict_of_forall_mem hC hpt)
      _ = M * ε' * μ.real (C ∩ closedBall x (r * R)) := by
          rw [integral_indicator_const _ measurableSet_closedBall,
            measureReal_restrict_apply measurableSet_closedBall, smul_eq_mul, mul_comm, inter_comm]
  -- Conclusion: `|E(r)| ≤ M ε' Λ' < ε`.
  have hrn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.mpr (pow_nonneg hr0.le n)
  rw [dist_zero_right, norm_mul, Real.norm_of_nonneg hrn]
  calc (r ^ n)⁻¹ * ‖∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x) ∂μ‖
      ≤ (r ^ n)⁻¹ * (M * ε' * μ.real (C ∩ closedBall x (r * R))) :=
        mul_le_mul_of_nonneg_left hint hrn
    _ = M * ε' * ((r ^ n)⁻¹ * μ.real (C ∩ closedBall x (r * R))) := by ring
    _ ≤ M * ε' * Λ' :=
        mul_le_mul_of_nonneg_left (hrΛ.trans (le_max_left _ _)) (mul_nonneg hM0 hε'.le)
    _ < (M + 1) * (Λ' + 1) * ε' := by nlinarith
    _ = ε := by rw [hε'eq]; field_simp
/-- **Weighted tangent space from a good piece** (Simon Ch. 3, Remark 1.8(1)).  Let `A` be Borel
with `Hⁿ(A) < ∞`, `ϑ` integrable on `A`, and `C ⊆ A` Borel with `ϑ|C` continuous at `x`.  If
`T_x C = P` (Def. 1.4) and `ρ⁻ⁿ ∫_{(A \ C) ∩ B_ρ(x)} |ϑ| dHⁿ → 0` as `ρ ↓ 0`, then `T_x A = P` with
respect to `ϑ` (Def. 1.7).  For `f ∈ C_c`, `r > 0` and `G = f ∘ η_{x,r}`, the change of variables
gives `∫_{η(A)} f(y) ϑ(x + r y) dHⁿ(y)
  = ϑ(x) ∫_{η(C)} f dHⁿ + r⁻ⁿ ∫_C G (ϑ − ϑ(x)) dHⁿ + r⁻ⁿ ∫_{A \ C} G ϑ dHⁿ`,
and the three terms tend to `ϑ(x) ∫_P f dHⁿ`, `0` and `0`. -/
theorem rsod_wfu_weightedApproxTangent_of_closed_piece : ∀ (n ℓ : ℕ) (A C : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → IntegrableOn ϑ A (μHE[n] : Measure (Amb n ℓ)) → MeasurableSet C → C ⊆ A → ContinuousWithinAt ϑ C x → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C x P → Tendsto (fun ρ : ℝ => (ρ ^ n)⁻¹ * (((μHE[n] : Measure (Amb n ℓ)).restrict A).withDensity (fun z => ‖ϑ z‖ₑ)).real ((A \ C) ∩ closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n A ϑ x P := by
  intro n ℓ A C ϑ x P hA hAfin hϑ hC hCA hϑC hT htail
  -- `Hⁿ(C) ≤ Hⁿ(A) < ∞`.
  have hCfin : (μHE[n] : Measure (Amb n ℓ)) C < ∞ := (measure_mono hCA).trans_lt hAfin
  -- `finrank P = n` is part of `T_x C = P`; fix `f ∈ C_c`.
  refine ⟨hT.1, fun f => ?_⟩
  -- The three limits: `ϑ(x) ∫_{η(C)} f → ϑ(x) ∫_P f` as `T_x C = P`; the frozen-weight error on `C`
  -- tends to `0`, fed by the ball-mass bound for `C`; and so does the tail on `A \ C`.
  have hlim := (((hT.2 f).const_mul (ϑ x)).add
    (Submission.rsod_wfu_blowUp_freeze_weight_tendsto_zero n ℓ C ϑ x hC hCfin hϑC
      (Submission.rsod_wfu_approxTangent_ballMass_bound n ℓ C x P hCfin hT) f)).add
    (Submission.rsod_wfu_blowUp_tail_tendsto_zero n ℓ A (A \ C) ϑ x (hA.diff hC) sdiff_subset
      hϑ htail f)
  rw [add_zero, add_zero] at hlim
  -- It remains to prove the identity for every `r > 0`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `G = f ∘ η` is continuous and bounded, so `G ϑ` is integrable on `A` and `G` on `C`.
  have hGc : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) := by
    refine (map_continuous f).comp ?_
    show Continuous fun z : Amb n ℓ => r⁻¹ • (z - x)
    fun_prop
  obtain ⟨M, hM⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hGϑ : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z) A
      (μHE[n] : Measure (Amb n ℓ)) :=
    hϑ.bdd_mul hGc.aestronglyMeasurable (Eventually.of_forall fun z => hM _)
  have hG : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) C
      (μHE[n] : Measure (Amb n ℓ)) :=
    IntegrableOn.of_bound hCfin hGc.aestronglyMeasurable M (Eventually.of_forall fun z => hM _)
  -- Change of variables, with weight `ϑ` on `A` and weight `1` on `C`.
  have hI := Submission.rsod_blowUp_setIntegral_eq n ℓ A f ϑ x r hr
  have hTC := Submission.rsod_blowUp_setIntegral_eq n ℓ C f (fun _ => 1) x r hr
  simp only [mul_one] at hTC
  -- `∫_A = ∫_C + ∫_{A \ C}`, and `ϑ(x)` comes out of the frozen-weight integral.
  have hsplit : ∫ z in A, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
      ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) +
      ∫ z in A \ C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
    rw [← integral_inter_add_sdiff hC hGϑ, inter_eq_right.mpr hCA]
  have hfreeze : ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (ϑ z - ϑ x)
      ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * ϑ z
        ∂(μHE[n] : Measure (Amb n ℓ)) -
      (∫ z in C, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))) *
        ϑ x := by
    rw [← integral_mul_const, ← integral_sub (hGϑ.mono_set hCA) (hG.mul_const (ϑ x))]
    simp_rw [mul_sub]
  rw [hI, hTC, hsplit, hfreeze]
  ring

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
