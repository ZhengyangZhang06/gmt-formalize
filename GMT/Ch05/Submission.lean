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

/-- **Zero mean of a linear form of `Dζ`** (step (1a) of the Schauder estimate in the elliptic
bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  For a continuous linear form `c` on
`L(ℝⁿ, ℝ^ℓ)` and a compactly supported `C¹` map `ζ : ℝⁿ → ℝ^ℓ`, `∫ c(Dζ(x)) dx = 0`.
Proof: `Dζ` is continuous with compact support, hence integrable, and `∫ c(Dζ) = c(∫ Dζ)`.
By translation invariance of Lebesgue measure, `y ↦ ∫ ζ(x + y) dx` is constant; differentiating
it at `0` under the integral sign (the derivatives `Dζ(x + y)`, `|y| < 1`, are bounded by a
constant times the indicator of a fixed ball) gives `∫ Dζ = 0`. -/
theorem dohr_eb_sch_integral_clm_fderiv_eq_zero : ∀ (n ℓ : ℕ) (c : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, c (fderiv ℝ ζ x) = 0 := by
  intro n ℓ c ζ hζ hcs
  -- Step 1: `Dζ` is continuous with compact support, hence integrable.
  have hcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hcsD : HasCompactSupport (fderiv ℝ ζ) := hcs.fderiv ℝ
  have hint : Integrable (fderiv ℝ ζ) := hcont.integrable_of_hasCompactSupport hcsD
  -- Step 2: pull `c` out of the integral; it suffices that `∫ Dζ = 0`.
  rw [ContinuousLinearMap.integral_comp_comm c hint]
  suffices h : ∫ x, fderiv ℝ ζ x = 0 by rw [h, map_zero]
  -- Step 3: `‖Dζ‖ ≤ C` everywhere and `tsupport Dζ ⊆ B_R(0)`.
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcsD
  obtain ⟨R, hR⟩ := hcsD.isCompact.isBounded.subset_closedBall (0 : Rn n)
  -- Step 4: differentiate `y ↦ ∫ ζ(x + y) dx` at `0` under the integral sign.
  have hderiv : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (∫ x, fderiv ℝ ζ (x + 0)) 0 := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball (0 : Rn n) 1)
      (F' := fun y x => fderiv ℝ ζ (x + y))
      (bound := (closedBall (0 : Rn n) (R + 1)).indicator fun _ => C)
      (ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y =>
        (hζ.continuous.comp (continuous_add_const y)).aestronglyMeasurable
    · simpa using hζ.continuous.integrable_of_hasCompactSupport hcs
    · exact (hcont.comp (continuous_add_const 0)).aestronglyMeasurable
    · refine Eventually.of_forall fun x y hy => ?_
      show ‖fderiv ℝ ζ (x + y)‖ ≤ (closedBall (0 : Rn n) (R + 1)).indicator (fun _ => C) x
      by_cases hx : x ∈ closedBall (0 : Rn n) (R + 1)
      · rw [indicator_of_mem hx]
        exact hC _
      · have hxy : x + y ∉ tsupport (fderiv ℝ ζ) := fun h => hx (by
          have h1 := hR h
          rw [mem_closedBall_zero_iff] at h1 ⊢
          rw [mem_ball_zero_iff] at hy
          calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
            _ ≤ R + 1 := by linarith)
        rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hxy, norm_zero]
    · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    · exact Eventually.of_forall fun x y _ =>
        (hasFDerivAt_comp_add_left x).2 ((hζ.differentiable one_ne_zero (x + y)).hasFDerivAt)
  -- Step 5: by translation invariance that function is constant, so its derivative is `0`.
  have hzero : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (0 : Rn n →L[ℝ] Rn ℓ) 0 :=
    (hasFDerivAt_const (∫ x, ζ x) (0 : Rn n)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => integral_add_right_eq_self ζ y)
  simpa using hderiv.unique hzero

end Submission
/-- **Interpolation bound for `Dw`** (step (1b) of the Schauder estimate in the elliptic bootstrap
for Simon 7.1).  If `w` is `C¹` on `B̆_ρ(x)` with `|w| ≤ S` there and
`‖Dw(y) − Dw(z)‖ ≤ K |y − z|^α` for `y, z ∈ B̆_ρ(x)`, then `‖Dw(x)‖ ≤ 2S/t + t^α K` for every
`t ∈ (0, ρ)` (operator norm). -/
theorem Submission.dohr_eb_sch_fderiv_norm_interpolation : ∀ (n ℓ : ℕ) (w : Rn n → Rn ℓ) (x : Rn n) (ρ t α S K : ℝ), 0 ≤ α → 0 ≤ K → 0 < t → t < ρ → ContDiffOn ℝ 1 w (ball x ρ) → (∀ y ∈ ball x ρ, ‖w y‖ ≤ S) → (∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤ K * ‖y - z‖ ^ α) → ‖fderiv ℝ w x‖ ≤ 2 * S / t + t ^ α * K := by
  intro n ℓ w x ρ t α S K hα hK ht htρ hw hS hH
  -- Step 1: `S ≥ |w(x)| ≥ 0`, so `B = 2S/t + t^α K ≥ 0`.
  have hxB : x ∈ ball x ρ := mem_ball_self (ht.trans htρ)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hB : 0 ≤ 2 * S / t + t ^ α * K :=
    add_nonneg (div_nonneg (mul_nonneg zero_le_two hS0) ht.le)
      (mul_nonneg (Real.rpow_nonneg ht.le α) hK)
  -- Step 2: `B_t(x) ⊆ B̆_ρ(x)`, and `w` has derivative `Dw(y)` at every `y ∈ B_t(x)`.
  have hsub : closedBall x t ⊆ ball x ρ := closedBall_subset_ball htρ
  have hdiff : ∀ y ∈ closedBall x t, HasFDerivWithinAt w (fderiv ℝ w y) (closedBall x t) y :=
    fun y hy => (((hw.differentiableOn one_ne_zero) y (hsub hy)).differentiableAt
      (isOpen_ball.mem_nhds (hsub hy))).hasFDerivAt.hasFDerivWithinAt
  -- Step 3: `‖Dw(y) − Dw(x)‖ ≤ K t^α` on `B_t(x)`.
  have hbound : ∀ y ∈ closedBall x t, ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * t ^ α := by
    intro y hy
    calc ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * ‖y - x‖ ^ α := hH y (hsub hy) x hxB
      _ ≤ K * t ^ α := by
        gcongr
        exact mem_closedBall_iff_norm.mp hy
  -- Steps 4–5: `|Dw(x) e| ≤ B` for every unit vector `e`.
  have hunit : ∀ e : Rn n, ‖e‖ = 1 → ‖fderiv ℝ w x e‖ ≤ 2 * S / t + t ^ α * K := by
    intro e he
    have hte : ‖t • e‖ = t := by rw [norm_smul, he, Real.norm_of_nonneg ht.le, mul_one]
    have hxe : x + t • e ∈ closedBall x t := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, hte]
    -- Step 4: the mean value inequality for `h(y) = w(y) − Dw(x)(y − x)` on `B_t(x)` gives
    -- `|w(x + te) − w(x) − t Dw(x)e| ≤ K t^α · t`.
    have hmv := (convex_closedBall x t).norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff
      hbound (mem_closedBall_self ht.le) hxe
    rw [add_sub_cancel_left, hte, map_smul] at hmv
    -- Step 5: `t |Dw(x)e| ≤ |w(x + te) − w(x)| + |w(x + te) − w(x) − t Dw(x)e| ≤ 2S + K t^α t`.
    have h1 : ‖w (x + t • e)‖ ≤ S := hS _ (hsub hxe)
    have h2 : ‖w x‖ ≤ S := hS x hxB
    have key : t * ‖fderiv ℝ w x e‖ ≤ 2 * S + K * t ^ α * t :=
      calc t * ‖fderiv ℝ w x e‖ = ‖t • fderiv ℝ w x e‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht.le]
        _ = ‖(w (x + t • e) - w x) - (w (x + t • e) - w x - t • fderiv ℝ w x e)‖ := by
            congr 1; abel
        _ ≤ ‖w (x + t • e) - w x‖ + ‖w (x + t • e) - w x - t • fderiv ℝ w x e‖ :=
            norm_sub_le _ _
        _ ≤ (‖w (x + t • e)‖ + ‖w x‖) + K * t ^ α * t := add_le_add (norm_sub_le _ _) hmv
        _ ≤ 2 * S + K * t ^ α * t := by linarith
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  -- Step 6: `|Dw(x) v| = |v| |Dw(x)(v/|v|)| ≤ B |v|`, so `‖Dw(x)‖ ≤ B`.
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : fderiv ℝ w x v = ‖v‖ • fderiv ℝ w x (‖v‖⁻¹ • v) := by
    rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  rw [hv', norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
  exact (mul_le_mul_of_nonneg_left (hunit _ (norm_smul_inv_norm hv)) (norm_nonneg v)).trans_eq
    (mul_comm _ _)
namespace Submission

/-- **Affine rescaling of `C¹` weak solutions** (scaling step of the Schauder estimate in the
elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  Let `w` be `C¹` on the open
set `U` with `∫_U a(x)[Dw][Dζ] = ∫_U Φ(x)[Dζ]` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let
`B_{ρr}(y + ρz₀) ⊆ U`, `ρ > 0`.  Then `w̃(z) = w(y + ρz)` is `C¹` on `B_r(z₀)`,
`Dw̃(z) = ρ Dw(y + ρz)` there, and `∫_{B_r(z₀)} a(y + ρz)[Dw̃][Dζ] = ∫_{B_r(z₀)} (ρΦ(y + ρz))[Dζ]`
for every `ζ ∈ C¹_c(B_r(z₀); ℝ^ℓ)`.
Proof: with `T z = y + ρz`, the test function `ζ ∘ T⁻¹` is admissible on `U`; both integrands
are `ρ²` times the original ones composed with `T` and vanish off the supports, and
`∫ H(y + ρz) dz = ρ⁻ⁿ ∫ H` holds for every `H` (no integrability needed). -/
theorem dohr_eb_sch_weak_eq_affine_rescale : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (U : Set (Rn n)) (y z₀ : Rn n) (ρ r : ℝ), 0 < ρ → IsOpen U → ball (y + ρ • z₀) (ρ * r) ⊆ U → ContDiffOn ℝ 1 w U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiffOn ℝ 1 (fun z => w (y + ρ • z)) (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball z₀ r → ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
  intro n ℓ a Φ w U y z₀ ρ r hρ hU hball hw hweak
  have hρ0 : ρ ≠ 0 := hρ.ne'
  -- Step 0: `T z = y + ρ • z` maps `B_r(z₀)` into `B_{ρ r}(y + ρ z₀) ⊆ U`.
  have hT : MapsTo (fun z : Rn n => y + ρ • z) (ball z₀ r) U := by
    intro z hz
    apply hball
    show dist (y + ρ • z) (y + ρ • z₀) < ρ * r
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_mul_of_pos_left (mem_ball.mp hz) hρ
  -- `T` is affine with derivative `ρ • id` everywhere.
  have hTd : ∀ z : Rn n,
      HasFDerivAt (fun z : Rn n => y + ρ • z) (ρ • ContinuousLinearMap.id ℝ (Rn n)) z :=
    fun z => ((hasFDerivAt_id z).const_smul ρ).const_add y
  -- Step 1 (ii): chain rule at points of `B_r(z₀)`, where `w` is differentiable.
  have hderiv : ∀ z ∈ ball z₀ r,
      fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z) := by
    intro z hz
    have hwd : DifferentiableAt ℝ w (y + ρ • z) :=
      (hw.differentiableOn one_ne_zero _ (hT hz)).differentiableAt (hU.mem_nhds (hT hz))
    have h := hwd.hasFDerivAt.comp z (hTd z)
    rw [show (fun z => w (y + ρ • z)) = w ∘ (fun z : Rn n => y + ρ • z) from rfl, h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  have hTC : ContDiff ℝ 1 (fun z : Rn n => y + ρ • z) :=
    contDiff_const.add (contDiff_id.const_smul ρ)
  refine ⟨hw.comp hTC.contDiffOn hT, hderiv, ?_⟩
  -- Step 2: transfer the test function, `ζ' = ζ ∘ T⁻¹`.
  intro ζ hζ hζc hζs
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : Rn n → Rn ℓ, ζ' = fun x => ζ (ρ⁻¹ • (x - y)) := ⟨_, rfl⟩
  have hζ'T : ∀ z, ζ' (y + ρ • z) = ζ z := by
    intro z
    simp [hζ', inv_smul_smul₀ hρ0]
  have hζ'C : ContDiff ℝ 1 ζ' := by
    rw [hζ']
    exact hζ.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
  have hK : IsCompact ((fun z : Rn n => y + ρ • z) '' tsupport ζ) :=
    hζc.isCompact.image hTC.continuous
  have hζ'K : ∀ x, x ∉ (fun z : Rn n => y + ρ • z) '' tsupport ζ → ζ' x = 0 := by
    intro x hx
    rw [hζ']
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine ⟨ρ⁻¹ • (x - y), hmem, ?_⟩
    simp [smul_inv_smul₀ hρ0]
  have hζ'c : HasCompactSupport ζ' := HasCompactSupport.intro hK hζ'K
  have hζ'sK : tsupport ζ' ⊆ (fun z : Rn n => y + ρ • z) '' tsupport ζ :=
    closure_minimal (Function.support_subset_iff'.mpr hζ'K) hK.isClosed
  have hζ's : tsupport ζ' ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hζ'sK hx
    exact hT (hζs hz)
  have hweak' := hweak ζ' hζ'C hζ'c hζ's
  -- `Dζ(z) = ρ • Dζ'(T z)` for every `z`.
  have hζd : ∀ z, fderiv ℝ ζ z = ρ • fderiv ℝ ζ' (y + ρ • z) := by
    intro z
    have h := (hζ'C.differentiable one_ne_zero (y + ρ • z)).hasFDerivAt.comp z (hTd z)
    have hfun : ζ' ∘ (fun z : Rn n => y + ρ • z) = ζ := funext hζ'T
    rw [hfun] at h
    rw [h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  -- Step 3: the integrands over `U` vanish off `U`.
  have hF0 : ∀ x, x ∉ U → a x (fderiv ℝ w x) (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  have hG0 : ∀ x, x ∉ U → Φ x (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 4: pointwise identities.
  have hFt : ∀ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) =
      ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    by_cases hz : z ∈ ball z₀ r
    · rw [hderiv z hz, hζd z]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    · have h1 : fderiv ℝ ζ z = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h))
      have h2 : fderiv ℝ ζ' (y + ρ • z) = 0 := by
        have h3 := hζd z
        rw [h1] at h3
        exact (smul_eq_zero.mp h3.symm).resolve_left hρ0
      rw [h1, h2]
      simp
  have hGt : ∀ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) =
      ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    rw [hζd z]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  -- Step 5: change of variables, valid without integrability.
  have hcov : ∀ H : Rn n → ℝ,
      ∫ z, H (y + ρ • z) = |(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, H x := by
    intro H
    rw [Measure.integral_comp_smul volume (fun x => H (y + x)) ρ, integral_add_left_eq_self H y]
  -- Step 6: conclusion.
  calc ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z)
      = ∫ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]
    _ = ∫ z, ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
        congr 1
        funext z
        exact hFt z
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| •
          ∫ x, a x (fderiv ℝ w x) (fderiv ℝ ζ' x)) := by
        rw [integral_const_mul, hcov (fun x => a x (fderiv ℝ w x) (fderiv ℝ ζ' x))]
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, Φ x (fderiv ℝ ζ' x)) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0, hweak',
          setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
    _ = ∫ z, ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
        rw [integral_const_mul, hcov (fun x => Φ x (fderiv ℝ ζ' x))]
    _ = ∫ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        congr 1
        funext z
        exact (hGt z).symm
    _ = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]

end Submission

namespace Submission

/-- **Blow-up Hölder estimate on the unit ball** (L. Simon's scaling argument; step 5 of the
Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).
For `0 < α < 1`, `λ > 0`, `M` and `δ > 0` there is `C_δ ≥ 0` such that every `C¹` weak solution `w`
on `B₁ = B̆₁(0)` of `∫ a(x)[Dw][Dζ] = ∫ Φ(x)[Dζ]`, with `a` Legendre-elliptic (`λ`), bounded and
`α`-Hölder (`M`), `Φ` `α`-Hölder (`G ≥ 0`), `|w| ≤ S` and `[Dw]_{α;B₁} ≤ K`, satisfies
`‖Dw(x) − Dw(y)‖ ≤ (δK + C_δ(S + G))|x − y|^α` on `B̆_{1/2}(0)`.
Proof by contradiction: violating data for `C_δ = k` are normalized by the difference quotient
`σ_k = ‖Dw_k(x_k) − Dw_k(y_k)‖/ρ_k^α`, `ρ_k = |x_k − y_k|`; the interpolation bound gives
`‖Dw_k‖ = o(σ_k)` on `B̆_{1/2}(0)`, hence `ρ_k → 0`. The blow-ups
`W_k(z) = (σ_k ρ_k^{1+α})⁻¹ (w_k(x_k + ρ_k z) − w_k(x_k) − ρ_k Dw_k(x_k) z)` solve rescaled systems
(rescale, zero mean, affine subtraction) with `DW_k(0) = 0`, `[DW_k]_α ≤ δ⁻¹`,
`‖DW_k((y_k − x_k)/ρ_k)‖ = 1` and errors tending to `0`.  The blow-up limit is a global solution of a
constant-coefficient Legendre system with `DW(0) = 0`, `‖DW(e₀)‖ = 1` and `[DW]_α ≤ δ⁻¹`, whose
gradient is constant by the Liouville theorem: a contradiction. -/
theorem dohr_eb_sch_blowup_holder_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M δ : ℝ, 0 < lam → 0 < δ → ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (K S G : ℝ), 0 ≤ G → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ G * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ S) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ (δ * K + Cδ * (S + G)) * ‖x - y‖ ^ α := by
  -- Norms, subtraction and continuity on `L(ℝⁿ, ℝ^ℓ)` and its dual need a deeper instance search.
  set_option maxSynthPendingDepth 3 in
  intro n ℓ _hn α hα hα1 lam M δ hlam hδ
  -- Step (0b): `α`-Hölder dependence on the base point gives continuity of linear forms in
  -- operator norm, and joint continuity of `(z, P, Q) ↦ b(z)[P][Q]`.
  have hcontL : ∀ (f : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, |f z P - f z' P| ≤ C * ‖z - z'‖ ^ α * ‖P‖) →
      ContinuousOn f U := by
    intro f U C hf z₀ hz₀
    have hb : ∀ z ∈ U, ‖f z - f z₀‖ ≤ |C| * ‖z - z₀‖ ^ α := by
      intro z hz
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (norm_nonneg _) α)) fun P => ?_
      rw [sub_apply, Real.norm_eq_abs]
      calc |f z P - f z₀ P| ≤ C * ‖z - z₀‖ ^ α * ‖P‖ := hf z hz z₀ hz₀ P
        _ ≤ |C| * ‖z - z₀‖ ^ α * ‖P‖ := by gcongr; exact le_abs_self C
    have hg : Continuous fun z : Rn n => |C| * ‖z - z₀‖ ^ α :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)
    have hg0 : Tendsto (fun z : Rn n => |C| * ‖z - z₀‖ ^ α) (𝓝[U] z₀)
        (𝓝 (|C| * ‖z₀ - z₀‖ ^ α)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hg0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_nhdsWithin_of_forall hb) hg0)
  have hcontJ : ∀ (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P Q : Rn n →L[ℝ] Rn ℓ,
        |b z P Q - b z' P Q| ≤ C * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) →
      ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2) (U ×ˢ univ) := by
    intro b U C hb p₀ hp₀
    have hfr : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p₀.1 p.2.1 p.2.2 :=
      ((b p₀.1).continuous.comp continuous_snd.fst).clm_apply continuous_snd.snd
    have hg : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ :=
      ((continuous_const.mul ((continuous_fst.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)).mul continuous_snd.fst.norm).mul continuous_snd.snd.norm
    have hg0 : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖) (𝓝[U ×ˢ univ] p₀)
        (𝓝 (|C| * ‖p₀.1 - p₀.1‖ ^ α * ‖p₀.2.1‖ * ‖p₀.2.2‖)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, zero_mul, zero_mul] at hg0
    have hdiff : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2) (𝓝[U ×ˢ univ] p₀) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg0
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Real.norm_eq_abs]
      calc |b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2|
          ≤ C * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := hb _ hp.1 _ hp₀.1 _ _
        _ ≤ |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := by gcongr; exact le_abs_self C
    have hsum := hdiff.add hfr.continuousWithinAt
    simp only [sub_add_cancel, zero_add] at hsum
    exact hsum
  -- Step 1: contradiction hypothesis; for each `k` take violating data with `C_δ = k`.
  by_contra hcon
  push Not at hcon
  choose a Φ w K S G hG hell hbd haH hΦH hwS hwC hwH hweak x hx y hy hviol using
    fun k : ℕ => hcon (k : ℝ) (Nat.cast_nonneg k)
  have h0B : (0 : Rn n) ∈ ball (0 : Rn n) 1 := mem_ball_self one_pos
  have hx1 : ∀ k, x k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hx k)
  have hy1 : ∀ k, y k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hy k)
  have hxn : ∀ k, ‖x k‖ < 1 / 2 := fun k => mem_ball_zero_iff.mp (hx k)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ k, ρ k = ‖x k - y k‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℝ, ∀ k,
      N k = ‖fderiv ℝ (w k) (x k) - fderiv ℝ (w k) (y k)‖ := ⟨_, fun _ => rfl⟩
  have hviol' : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α < N k := fun k => by
    rw [hρ, hN]; exact hviol k
  -- `x_k ≠ y_k`, so `ρ_k > 0`; `K_k, S_k ≥ 0` and `N_k > 0`.
  have hρpos : ∀ k, 0 < ρ k := by
    intro k
    rw [hρ]
    refine norm_pos_iff.mpr fun hxy => ?_
    have h := hviol k
    rw [sub_eq_zero.mp hxy, sub_self, sub_self, norm_zero, norm_zero,
      Real.zero_rpow hα.ne', mul_zero] at h
    exact lt_irrefl 0 h
  have hραpos : ∀ k, 0 < ρ k ^ α := fun k => Real.rpow_pos_of_pos (hρpos k) α
  have hK0 : ∀ k, 0 ≤ K k := by
    intro k
    have h := hwH k (x k) (hx1 k) (y k) (hy1 k)
    rw [← hρ, ← hN] at h
    by_contra hneg
    push Not at hneg
    have h1 : K k * ρ k ^ α < 0 := mul_neg_of_neg_of_pos hneg (hραpos k)
    have h2 : 0 ≤ N k := by rw [hN]; exact norm_nonneg _
    linarith
  have hS0 : ∀ k, 0 ≤ S k := fun k => (norm_nonneg _).trans (hwS k 0 h0B)
  have hsplit : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α =
      δ * K k * ρ k ^ α + (k * S k * ρ k ^ α + k * G k * ρ k ^ α) := fun k => by ring
  have hKρ : ∀ k, 0 ≤ δ * K k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg hδ.le (hK0 k)) (hραpos k).le
  have hSρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * S k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hS0 k)) (hραpos k).le
  have hGρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * G k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hG k)) (hραpos k).le
  have hNpos : ∀ k, 0 < N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k, hGρ k]
  have hKN : ∀ k, δ * K k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hSρ k, hGρ k]
  have hSN : ∀ k : ℕ, (k : ℝ) * S k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hGρ k]
  have hGN : ∀ k : ℕ, (k : ℝ) * G k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k]
  -- Step 3: small gradients.  The interpolation bound with `t = k^{-1/2}` on `B̆_{1/2}(z)` gives
  -- `‖Dw_k(z)‖ ρ_k^α ≤ ε_k N_k` on `B̆_{1/2}(0)`, `ε_k = 2k^{-1/2} + k^{-α/2}/δ → 0`.
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ∀ k : ℕ,
      ε k = 2 / Real.sqrt k + (Real.sqrt k)⁻¹ ^ α / δ := ⟨_, fun _ => rfl⟩
  have hinterp : ∀ k : ℕ, 5 ≤ k → ∀ z ∈ ball (0 : Rn n) (1 / 2),
      ‖fderiv ℝ (w k) z‖ * ρ k ^ α ≤ ε k * N k := by
    intro k hk z hz
    have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
    have hsq2 : 2 < Real.sqrt k := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hsq : 0 < Real.sqrt k := by linarith
    have ht : 0 < (Real.sqrt k)⁻¹ := inv_pos.mpr hsq
    have ht2 : (Real.sqrt k)⁻¹ < 1 / 2 := by
      rw [one_div]; exact inv_strictAnti₀ (by norm_num) hsq2
    have hsub : ball z (1 / 2) ⊆ ball (0 : Rn n) 1 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith [mem_ball_zero_iff.mp hz])
    have hI := Submission.dohr_eb_sch_fderiv_norm_interpolation n ℓ (w k) z (1 / 2)
      (Real.sqrt k)⁻¹ α (S k) (K k) hα.le (hK0 k) ht ht2 ((hwC k).mono hsub)
      (fun y' hy' => hwS k y' (hsub hy'))
      (fun y' hy' z' hz' => hwH k y' (hsub hy') z' (hsub hz'))
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
    have e1 : 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α ≤ 2 / Real.sqrt k * N k := by
      rw [div_inv_eq_mul, div_mul_eq_mul_div, le_div_iff₀ hsq]
      calc 2 * S k * Real.sqrt k * ρ k ^ α * Real.sqrt k
          = 2 * ((Real.sqrt k * Real.sqrt k) * S k * ρ k ^ α) := by ring
        _ = 2 * ((k : ℝ) * S k * ρ k ^ α) := by rw [hkk]
        _ ≤ 2 * N k := by linarith [hSN k]
    have e2 : (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α ≤ (Real.sqrt k)⁻¹ ^ α / δ * N k := by
      have htα : 0 ≤ (Real.sqrt k)⁻¹ ^ α := Real.rpow_nonneg ht.le α
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      calc (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α * δ
          = (Real.sqrt k)⁻¹ ^ α * (δ * K k * ρ k ^ α) := by ring
        _ ≤ (Real.sqrt k)⁻¹ ^ α * N k := mul_le_mul_of_nonneg_left (hKN k) htα
    calc ‖fderiv ℝ (w k) z‖ * ρ k ^ α
        ≤ (2 * S k / (Real.sqrt k)⁻¹ + (Real.sqrt k)⁻¹ ^ α * K k) * ρ k ^ α :=
          mul_le_mul_of_nonneg_right hI (hραpos k).le
      _ = 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α + (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α := by ring
      _ ≤ 2 / Real.sqrt k * N k + (Real.sqrt k)⁻¹ ^ α / δ * N k := add_le_add e1 e2
      _ = ε k * N k := by rw [hε]; ring
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun k : ℕ => 2 / Real.sqrt k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul 2
    have h2 : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹ ^ α / δ) atTop (𝓝 0) := by
      have h3 := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hinv).div_const δ
      rw [Real.zero_rpow hα.ne', zero_div] at h3
      exact h3
    have h4 := h1.add h2
    rw [add_zero] at h4
    exact h4.congr fun k => (hε k).symm
  -- Step 4: the scale tends to `0`: `ρ_k^α = N_k/σ_k ≤ 2ε_k`.
  have hρα_le : ∀ k, 5 ≤ k → ρ k ^ α ≤ 2 * ε k := by
    intro k hk
    have h1 := hinterp k hk (x k) (hx k)
    have h2 := hinterp k hk (y k) (hy k)
    have h3 : N k ≤ ‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖ := by
      rw [hN]; exact norm_sub_le _ _
    have h4 : N k * ρ k ^ α ≤ N k * (2 * ε k) := by
      calc N k * ρ k ^ α
          ≤ (‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖) * ρ k ^ α :=
            mul_le_mul_of_nonneg_right h3 (hραpos k).le
        _ = ‖fderiv ℝ (w k) (x k)‖ * ρ k ^ α + ‖fderiv ℝ (w k) (y k)‖ * ρ k ^ α := by ring
        _ ≤ ε k * N k + ε k * N k := add_le_add h1 h2
        _ = N k * (2 * ε k) := by ring
    exact le_of_mul_le_mul_left h4 (hNpos k)
  have hραt : Tendsto (fun k => ρ k ^ α) atTop (𝓝 0) := by
    have h2ε : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hεt.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun k => (hραpos k).le) ?_ h2ε
    filter_upwards [eventually_ge_atTop 5] with k hk using hρα_le k hk
  have hρt : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (Real.continuousAt_rpow_const 0 α⁻¹ (Or.inr (inv_nonneg.mpr hα.le))).tendsto.comp
      hραt
    rw [Real.zero_rpow (inv_ne_zero hα.ne')] at h1
    exact h1.congr fun k => Real.rpow_rpow_inv (hρpos k).le hα.ne'
  have hρhalf : ∀ᶠ k in atTop, ρ k < 1 / 2 := hρt.eventually (Iio_mem_nhds (by norm_num))
  -- Step 5: the blow-up sequence on `D_k = B̆_{R_k}(0)`, `R_k = 1/(2ρ_k)`.
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k = (ρ k * N k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, ∀ k, R k = (2 * ρ k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ → (Rn n →L[ℝ] Rn ℓ), ∀ k,
      P₀ k = ρ k • fderiv ℝ (w k) (x k) := ⟨_, fun _ => rfl⟩
  obtain ⟨ah, hah⟩ : ∃ ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∀ k z, ah k z = a k (x k + ρ k • z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Rn n → Rn ℓ, ∀ k,
      W k = fun z => s k • (w k (x k + ρ k • z) - w k (x k) - P₀ k z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ k z,
      Ψ k z = s k • ((ρ k • Φ k (x k + ρ k • z) - ρ k • Φ k (x k)) -
        (ah k z (P₀ k) - a k (x k) (P₀ k))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → Rn n, ∀ k, e k = (ρ k)⁻¹ • (y k - x k) := ⟨_, fun _ => rfl⟩
  have hspos : ∀ k, 0 < s k := fun k => by
    rw [hs]; exact inv_pos.mpr (mul_pos (hρpos k) (hNpos k))
  have hsρ : ∀ k, s k * ρ k = (N k)⁻¹ := fun k => by
    rw [hs, mul_inv, mul_comm (ρ k)⁻¹, mul_assoc, inv_mul_cancel₀ (hρpos k).ne', mul_one]
  have hRpos : ∀ k, 0 < R k := fun k => by
    rw [hR]; exact inv_pos.mpr (mul_pos two_pos (hρpos k))
  have hρR : ∀ k, ρ k * R k = 1 / 2 := fun k => by
    rw [hR, mul_inv, ← mul_assoc, mul_comm (ρ k), mul_assoc, mul_inv_cancel₀ (hρpos k).ne',
      mul_one, one_div]
  have hmap : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), x k + ρ k • z ∈ ball (0 : Rn n) 1 := by
    intro k z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖x k + ρ k • z‖ ≤ ‖x k‖ + ‖ρ k • z‖ := norm_add_le _ _
      _ = ‖x k‖ + ρ k * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg (hρpos k).le]
      _ < 1 / 2 + ρ k * R k := add_lt_add (hxn k) (mul_lt_mul_of_pos_left hz (hρpos k))
      _ = 1 := by rw [hρR k]; norm_num
  have hscale : ∀ k (z z' : Rn n),
      ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α = ρ k ^ α * ‖z - z'‖ ^ α := by
    intro k z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (hρpos k).le,
      Real.mul_rpow (hρpos k).le (norm_nonneg _)]
  -- The rescaled maps `w_k(x_k + ρ_k ·)` solve the rescaled system on `D_k` (sibling rescale).
  have hres := fun k => Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ (a k) (Φ k) (w k)
    (ball 0 1) (x k) 0 (ρ k) (R k) (hρpos k) isOpen_ball
    (by
      rw [smul_zero, add_zero, hρR k]
      exact ball_subset_ball' (by rw [dist_zero_right]; linarith [hxn k]))
    (hwC k) (hweak k)
  -- Step (0b) for the rescaled coefficients.
  have hJ : ∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
      ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ) := by
    intro k
    refine hcontJ (ah k) (ball 0 (R k)) (M * ρ k ^ α) fun z hz z' hz' P Q => ?_
    rw [hah, hah]
    calc |a k (x k + ρ k • z) P Q - a k (x k + ρ k • z') P Q|
        ≤ M * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖ * ‖Q‖ :=
          haH k _ (hmap k z hz) _ (hmap k z' hz') P Q
      _ = M * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := by rw [hscale]; ring
  have hΘc : ∀ k, ContinuousOn (fun z => ρ k • Φ k (x k + ρ k • z)) (ball (0 : Rn n) (R k)) := by
    intro k
    refine hcontL _ (ball 0 (R k)) (ρ k * G k * ρ k ^ α) fun z hz z' hz' P => ?_
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (hρpos k)]
    calc ρ k * |Φ k (x k + ρ k • z) P - Φ k (x k + ρ k • z') P|
        ≤ ρ k * (G k * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖) :=
          mul_le_mul_of_nonneg_left (hΦH k _ (hmap k z hz) _ (hmap k z' hz') P) (hρpos k).le
      _ = ρ k * G k * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ := by rw [hscale]; ring
  -- Step 6: the blow-ups solve the rescaled system with error `Ψ_k`
  -- (sibling zero mean and child `weak_eq_sub_affine`).
  have hsub := fun k => Submission.dohr_eb_sch_bu_weak_eq_sub_affine n ℓ (ah k)
    (fun z => ρ k • Φ k (x k + ρ k • z)) (fun z => w k (x k + ρ k • z)) (ball 0 (R k))
    (a k (x k)) (ρ k • Φ k (x k)) (P₀ k) (w k (x k)) (s k) isOpen_ball (hJ k) (hΘc k)
    (hres k).1 (fun ζ hζ hζc hζs => by simpa only [hah] using (hres k).2.2 ζ hζ hζc hζs)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
  have hWC : ∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k)) := fun k => by
    rw [hW k]; exact (hsub k).1
  have hDW : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k),
      fderiv ℝ (W k) z = s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) := by
    intro k z hz
    rw [hW k, (hsub k).2.1 z hz, (hres k).2.1 z hz]
  have hW0 : ∀ k, W k 0 = 0 := fun k => by
    rw [hW k]; simp
  have hDW0 : ∀ k, fderiv ℝ (W k) 0 = 0 := fun k => by
    rw [hDW k 0 (mem_ball_self (hRpos k)), hP₀, smul_zero, add_zero, sub_self, smul_zero]
  have hWH : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ δ⁻¹ * ‖z - z'‖ ^ α := by
    intro k z hz z' hz'
    rw [hDW k z hz, hDW k z' hz']
    have h1 : s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) -
        s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z') - P₀ k) =
        (s k * ρ k) • (fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')) := by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, smul_smul]
    rw [h1, norm_smul, Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ]
    have h2 := hwH k _ (hmap k z hz) _ (hmap k z' hz')
    rw [hscale] at h2
    have h3 : (N k)⁻¹ * (K k * ρ k ^ α) ≤ δ⁻¹ := by
      rw [inv_mul_le_iff₀ (hNpos k), le_mul_inv_iff₀ hδ]
      calc K k * ρ k ^ α * δ = δ * K k * ρ k ^ α := by ring
        _ ≤ N k := hKN k
    calc (N k)⁻¹ * ‖fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')‖
        ≤ (N k)⁻¹ * (K k * (ρ k ^ α * ‖z - z'‖ ^ α)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (hNpos k).le)
      _ = (N k)⁻¹ * (K k * ρ k ^ α) * ‖z - z'‖ ^ α := by ring
      _ ≤ δ⁻¹ * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) α)
  -- Bounds for the frozen and rescaled coefficients and for the error `Ψ_k`.
  have hah0 : ∀ k, ah k 0 = a k (x k) := fun k => by rw [hah, smul_zero, add_zero]
  have hell0 : ∀ k (P : Rn n →L[ℝ] Rn ℓ), lam * ‖P‖ ^ 2 ≤ ah k 0 P P := fun k P => by
    rw [hah0]; exact hell k (x k) (hx1 k) P
  have hbd0 : ∀ k (P Q : Rn n →L[ℝ] Rn ℓ), |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖ := fun k P Q => by
    rw [hah0]; exact hbd k (x k) (hx1 k) P Q
  have hahb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah k z P Q - ah k 0 P Q| ≤ M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by
    intro k z hz P Q
    have h := haH k _ (hmap k z hz) _ (hmap k 0 (mem_ball_self (hRpos k))) P Q
    rw [hscale, sub_zero] at h
    rw [hah k z, hah k 0]
    calc _ ≤ M * (ρ k ^ α * ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by ring
  have hΨd : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q - Ψ k z' Q| ≤
        (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
    intro k z hz z' hz' Q
    have hΦ := hΦH k _ (hmap k z hz) _ (hmap k z' hz') Q
    have ha := haH k _ (hmap k z hz) _ (hmap k z' hz') (P₀ k) Q
    have hP : ‖P₀ k‖ = ρ k * ‖fderiv ℝ (w k) (x k)‖ := by
      rw [hP₀, norm_smul, Real.norm_of_nonneg (hρpos k).le]
    rw [hscale] at hΦ ha
    rw [hP] at ha
    have hexp : Ψ k z Q - Ψ k z' Q = s k * (ρ k * (Φ k (x k + ρ k • z) Q -
        Φ k (x k + ρ k • z') Q) - (a k (x k + ρ k • z) (P₀ k) Q -
        a k (x k + ρ k • z') (P₀ k) Q)) := by
      rw [hΨ, hΨ, hah, hah]
      simp only [smul_apply, sub_apply, smul_eq_mul]
      ring
    rw [hexp, abs_mul, abs_of_pos (hspos k)]
    have htri : |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
        (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)| ≤
        ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (hρpos k)]
      exact add_le_add (mul_le_mul_of_nonneg_left hΦ (hρpos k).le) ha
    calc s k * |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
          (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)|
        ≤ s k * (ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖) :=
          mul_le_mul_of_nonneg_left htri (hspos k).le
      _ = (s k * ρ k) * (G k + M * ‖fderiv ℝ (w k) (x k)‖) * ρ k ^ α * ‖z - z'‖ ^ α * ‖Q‖ := by
          ring
      _ = (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
          rw [hsρ]; ring
  have hΨc : ∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k)) := fun k => hcontL (Ψ k) _ _ (hΨd k)
  have hΨb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ,
      |Ψ k z Q| ≤ (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z‖ ^ α * ‖Q‖ := by
    intro k z hz Q
    have h := hΨd k z hz 0 (mem_ball_self (hRpos k)) Q
    have h0 : Ψ k 0 Q = 0 := by
      rw [hΨ, hah]
      simp
    rwa [h0, sub_zero, sub_zero] at h
  have hWeq : ∀ k (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Rn n) (R k) →
      ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) =
        ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z) := by
    intro k ζ hζ hζc hζs
    rw [hW k]
    simp only [hΨ]
    exact (hsub k).2.2 ζ hζ hζc hζs
  -- The unit vectors `e_k = (y_k − x_k)/ρ_k` with `‖DW_k(e_k)‖ = 1`.
  have he1 : ∀ k, ‖e k‖ = 1 := fun k => by
    rw [he, norm_smul, norm_inv, Real.norm_of_nonneg (hρpos k).le, norm_sub_rev, ← hρ,
      inv_mul_cancel₀ (hρpos k).ne']
  have hxe : ∀ k, x k + ρ k • e k = y k := fun k => by
    rw [he, smul_smul, mul_inv_cancel₀ (hρpos k).ne', one_smul, add_sub_cancel]
  have heN : ∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1 := by
    filter_upwards [hρhalf] with k hk
    have hek : e k ∈ ball (0 : Rn n) (R k) := by
      rw [mem_ball_zero_iff, he1, hR, one_lt_inv₀ (mul_pos two_pos (hρpos k))]
      linarith
    rw [hDW k (e k) hek, hxe, hP₀, ← smul_sub, smul_smul, norm_smul,
      Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ, norm_sub_rev, ← hN,
      inv_mul_cancel₀ (hNpos k).ne']
  -- Limits of the scale-dependent constants.
  have hRt : Tendsto R atTop atTop := by
    have h2ρ : Tendsto (fun k => 2 * ρ k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa using hρt.const_mul 2
      · exact mul_pos two_pos (hρpos k)
    exact (tendsto_inv_nhdsGT_zero.comp h2ρ).congr fun k => (hR k).symm
  have hct : Tendsto (fun k => M * ρ k ^ α) atTop (𝓝 0) := by
    simpa using hραt.const_mul M
  have hdt : Tendsto (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k))
      atTop (𝓝 0) := by
    have hG' : Tendsto (fun k => G k * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (hG k) (div_nonneg (hραpos k).le (hNpos k).le)) ?_
        tendsto_one_div_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [mul_div_assoc', div_le_div_iff₀ (hNpos k) hk', one_mul]
      calc G k * ρ k ^ α * k = k * G k * ρ k ^ α := by ring
        _ ≤ N k := hGN k
    have hD' : Tendsto (fun k => ‖fderiv ℝ (w k) (x k)‖ * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (norm_nonneg _) (div_nonneg (hραpos k).le (hNpos k).le)) ?_ hεt
      filter_upwards [eventually_ge_atTop 5] with k hk
      rw [mul_div_assoc', div_le_iff₀ (hNpos k)]
      exact hinterp k hk (x k) (hx k)
    have h := hG'.add (hD'.const_mul M)
    rw [mul_zero, add_zero] at h
    exact h.congr fun k => by ring
  -- Steps 7–8 (child `blowup_limit`) and step 9 (sibling Liouville theorem).
  obtain ⟨A, W', hA1, hA2, hW'C, hW'H, hW'eq, hW'0, e₀, he₀⟩ :=
    Submission.dohr_eb_sch_bu_blowup_limit n ℓ α lam M δ⁻¹ W ah Ψ e R (fun k => M * ρ k ^ α)
      (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k)) hα
      (inv_nonneg.mpr hδ.le) hRt hct hdt hWC hW0 hDW0 hWH hJ hΨc hell0 hbd0 hahb hΨb hWeq
      (fun k => (he1 k).le) heN
  have hconst := Submission.dohr_eb_sch_liouville_const_coeff n ℓ α lam M δ⁻¹ A W' hα hα1 hlam
    hA1 hA2 hW'C hW'H hW'eq e₀ 0
  rw [hconst, hW'0, norm_zero] at he₀
  exact zero_ne_one he₀

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
