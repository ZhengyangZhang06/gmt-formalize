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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

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

end Submission

end GMT.Ch05
