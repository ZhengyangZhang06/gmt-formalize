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

set_option maxHeartbeats 800000 in
/-- **Simon Ch. 5, proof of Theorem 5.2, steps (1)–(7) (pp. 122–123), with Remark 4.6 (p. 116),
at `ξ = 0`.**  Assuming the Tilt-excess Decay Theorem 4.5, iterate it at the radii `η^j σ` to get
`n`-planes `S_j` with `E_*(0, η^j σ, S_j) ≤ η^{2(1−n/p)j} E_*(0, σ, S₀)`.  The lower density bound
`c_l ω_n sⁿ ≤ μ_V(B_s(0))` gives `|p_{S_{j+1}} − p_{S_j}|² ≤ C η^{2(1−n/p)j} E_*(0, σ, S₀)`, so
`p_{S_j} → p_S` for an `n`-plane `S` with `|p_S − p_{S₀}|² ≤ C_II E_*(0, σ, S₀)`; the upper bound
`μ_V(B_s(0)) ≤ c_u ω_n sⁿ` interpolates between the radii `η^j σ`, giving
`E(0, s, S) ≤ C_III (s/σ)^{2(1−n/p)} E_*(0, σ, S₀)` for `0 < s ≤ σ`.  `δ₆` is the `δ₀` of 4.5, and
`C_II, C_III` depend only on `n, ℓ, p, c_l, c_u`. -/
theorem any_radius_tilt_iteration : TiltExcessDecayTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ cl cu : ℝ, 0 < cl → ∃ δ₆ CII CIII : ℝ, 0 < δ₆ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ σ : ℝ), 0 < δ → δ ≤ δ₆ → V.AllardHypotheses H p δ ρ → 0 < σ → σ ≤ δ * ρ / 2 → (∀ s : ℝ, 0 < s → s ≤ σ → cl * unitBallVolume n * s ^ n ≤ (V.weight (closedBall 0 s)).toReal ∧ (V.weight (closedBall 0 s)).toReal ≤ cu * unitBallVolume n * s ^ n) → ∀ S₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S₀ = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ hsNormSq (S.starProjection - S₀.starProjection) ≤ CII * V.tiltExcessStar H p δ 0 σ S₀ ∧ ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess 0 s S ≤ CIII * (s / σ) ^ (2 * (1 - (n : ℝ) / p)) * V.tiltExcessStar H p δ 0 σ S₀ := by
  have htan := Submission.any_radius_tangent_ae
  have hsFacts : ∀ (m k : ℕ), Continuous (fun X : Rn m →L[ℝ] Rn k => hsNormSq X) ∧ ∀ X Y : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq X ∧ hsNorm X ^ 2 = hsNormSq X ∧ hsNormSq (X - Y) ≤ 2 * hsNormSq X + 2 * hsNormSq Y ∧ hsNorm (X + Y) ≤ hsNorm X + hsNorm Y ∧ ‖X‖ ≤ hsNorm X := by
    intro m k
    -- the vector of columns, as an element of the L² product space
    let col : (Rn m →L[ℝ] Rn k) → PiLp 2 (fun _ : Fin m => Rn k) :=
      fun X => WithLp.toLp 2 (fun i => X (EuclideanSpace.single i 1))
    have hcol_norm : ∀ X : Rn m →L[ℝ] Rn k, ‖col X‖ = hsNorm X := by
      intro X
      simp only [col, hsNorm, hsNormSq, PiLp.norm_eq_of_L2]
    have hcol_add : ∀ X Y : Rn m →L[ℝ] Rn k, col (X + Y) = col X + col Y := by
      intro X Y
      rfl
    have hnonneg : ∀ X : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq X := by
      intro X
      unfold hsNormSq
      positivity
    refine ⟨?_, ?_⟩
    · unfold hsNormSq
      refine continuous_finsetSum _ (fun i _ => ?_)
      exact ((continuous_id.clm_apply continuous_const).norm).pow 2
    intro X Y
    have hsq : hsNorm X ^ 2 = hsNormSq X := by
      unfold hsNorm
      exact Real.sq_sqrt (hnonneg X)
    refine ⟨hnonneg X, hsq, ?_, ?_, ?_⟩
    · unfold hsNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      simp only [sub_apply]
      have h1 := norm_sub_le (X (EuclideanSpace.single i 1)) (Y (EuclideanSpace.single i 1))
      have h2 := norm_nonneg (X (EuclideanSpace.single i 1) - Y (EuclideanSpace.single i 1))
      nlinarith [sq_nonneg (‖X (EuclideanSpace.single i 1)‖ - ‖Y (EuclideanSpace.single i 1)‖),
        norm_nonneg (X (EuclideanSpace.single i 1)), norm_nonneg (Y (EuclideanSpace.single i 1))]
    · rw [← hcol_norm, ← hcol_norm, ← hcol_norm, hcol_add]
      exact norm_add_le _ _
    · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
      -- expand v in the standard basis
      have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hXv : X v = ∑ i, v i • X (EuclideanSpace.single i 1) := by
        conv_lhs => rw [hv]
        simp [map_sum, map_smul]
      calc ‖X v‖ = ‖∑ i, v i • X (EuclideanSpace.single i 1)‖ := by rw [hXv]
        _ ≤ ∑ i, ‖v i • X (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
        _ = ∑ i, |v i| * ‖X (EuclideanSpace.single i 1)‖ := by
            simp [norm_smul, Real.norm_eq_abs]
        _ ≤ Real.sqrt (∑ i, |v i| ^ 2) * Real.sqrt (∑ i, ‖X (EuclideanSpace.single i 1)‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = hsNorm X * ‖v‖ := by
            rw [mul_comm]
            congr 1
            rw [EuclideanSpace.norm_eq]
            simp [Real.norm_eq_abs]
  have tiltFacts : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (z : Amb n ℓ) (r : ℝ), closedBall z r ⊆ U → ∀ T₁ T₂ : Submodule ℝ (Amb n ℓ), V.weight (closedBall z r) < ⊤ ∧ IntegrableOn (fun x => hsNormSq (V.tangentProj x - T₁.starProjection)) (closedBall z r) V.weight ∧ (∀ r' : ℝ, r' ≤ r → ∫ x in closedBall z r', hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight ≤ ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight) ∧ (V.weight (closedBall z r)).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) ≤ 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight + 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight ∧ ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight ≤ 2 * ∫ x in closedBall z r, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight + 2 * (V.weight (closedBall z r)).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) := by
    intro n ℓ U V hmeas z r hzr T₁ T₂
    have hA := hsFacts (n + ℓ) (n + ℓ)
    set B : Set (Amb n ℓ) := closedBall z r with hB_def
    have hBmeas : MeasurableSet B := measurableSet_closedBall
    -- Step 1: finite measure of the ball
    have hfin : V.weight B < ⊤ := by
      have hK : IsCompact B := isCompact_closedBall z r
      have hint := V.integrableOn_mult B hK hzr
      unfold RectifiableVarifold.weight
      rw [withDensity_apply _ hBmeas, Measure.restrict_restrict hBmeas]
      refine lt_of_le_of_lt ?_ hint.2
      rw [Set.inter_comm]
      refine lintegral_mono (fun x => ?_)
      exact ENNReal.ofReal_le_of_le_toReal (by simp [Real.norm_eq_abs, le_abs_self])
    -- Step 2: pointwise bound and integrability
    have hproj_le : ∀ x (v : Amb n ℓ), ‖V.tangentProj x v‖ ≤ ‖v‖ := by
      intro x v
      unfold RectifiableVarifold.tangentProj
      split_ifs with h
      · exact Submodule.norm_starProjection_apply_le _ v
      · simp
    have hbound : ∀ (x : Amb n ℓ) (T : Submodule ℝ (Amb n ℓ)),
        hsNormSq (V.tangentProj x - T.starProjection) ≤ 4 * (n + ℓ : ℕ) := by
      intro x T
      unfold hsNormSq
      calc ∑ i : Fin (n + ℓ), ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ _i : Fin (n + ℓ), (4 : ℝ) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have h1 := hproj_le x (EuclideanSpace.single i (1 : ℝ))
            have h2 := Submodule.norm_starProjection_apply_le T (EuclideanSpace.single i (1 : ℝ))
            rw [PiLp.norm_single, norm_one] at h1 h2
            rw [sub_apply]
            have h3 := norm_sub_le (V.tangentProj x (EuclideanSpace.single i 1))
              (T.starProjection (EuclideanSpace.single i 1))
            have h4 := norm_nonneg ((V.tangentProj x) (EuclideanSpace.single i 1) -
              T.starProjection (EuclideanSpace.single i 1))
            nlinarith
        _ = 4 * (n + ℓ : ℕ) := by simp [mul_comm]
    have hint : ∀ T : Submodule ℝ (Amb n ℓ),
        IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) B V.weight := by
      intro T
      refine Measure.integrableOn_of_bounded (M := 4 * (n + ℓ : ℕ)) hfin.ne ?_ ?_
      · have h1 : AEStronglyMeasurable (fun x => V.tangentProj x - T.starProjection) V.weight :=
          hmeas.sub aestronglyMeasurable_const
        exact hA.1.comp_aestronglyMeasurable h1
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg ((hA.2 _ 0).1)]
        exact hbound x T
    have hconst : ∀ c : ℝ, IntegrableOn (fun _ : Amb n ℓ => c) B V.weight :=
      fun c => integrableOn_const hfin.ne
    refine ⟨hfin, hint T₁, ?_, ?_, ?_⟩
    · -- monotonicity in the radius
      intro r' hr'
      refine setIntegral_mono_set (hint T₁) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => (hA.2 _ 0).1)
      · exact Filter.Eventually.of_forall (closedBall_subset_closedBall hr')
    · -- two planes vs. one point
      have hpt : ∀ x, hsNormSq (T₁.starProjection - T₂.starProjection) ≤
          2 * hsNormSq (V.tangentProj x - T₁.starProjection) +
            2 * hsNormSq (V.tangentProj x - T₂.starProjection) := by
        intro x
        have h := (hA.2 (V.tangentProj x - T₂.starProjection) (V.tangentProj x - T₁.starProjection)).2.2.1
        have heq : (V.tangentProj x - T₂.starProjection) - (V.tangentProj x - T₁.starProjection) =
            T₁.starProjection - T₂.starProjection := by abel
        rw [heq] at h
        linarith
      calc (V.weight B).toReal * hsNormSq (T₁.starProjection - T₂.starProjection)
          = ∫ _x in B, hsNormSq (T₁.starProjection - T₂.starProjection) ∂V.weight := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def]
        _ ≤ ∫ x in B, (2 * hsNormSq (V.tangentProj x - T₁.starProjection) +
              2 * hsNormSq (V.tangentProj x - T₂.starProjection)) ∂V.weight :=
            setIntegral_mono (hconst _) (((hint T₁).const_mul 2).add ((hint T₂).const_mul 2)) hpt
        _ = 2 * ∫ x in B, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight +
              2 * ∫ x in B, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight := by
            rw [integral_add ((hint T₁).const_mul 2) ((hint T₂).const_mul 2), integral_const_mul,
              integral_const_mul]
    · -- changing the plane
      have hpt : ∀ x, hsNormSq (V.tangentProj x - T₁.starProjection) ≤
          2 * hsNormSq (V.tangentProj x - T₂.starProjection) +
            2 * hsNormSq (T₁.starProjection - T₂.starProjection) := by
        intro x
        have h := (hA.2 (V.tangentProj x - T₂.starProjection) (T₁.starProjection - T₂.starProjection)).2.2.1
        have heq : (V.tangentProj x - T₂.starProjection) - (T₁.starProjection - T₂.starProjection) =
            V.tangentProj x - T₁.starProjection := by abel
        rw [heq] at h
        linarith
      calc ∫ x in B, hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight
          ≤ ∫ x in B, (2 * hsNormSq (V.tangentProj x - T₂.starProjection) +
              2 * hsNormSq (T₁.starProjection - T₂.starProjection)) ∂V.weight :=
            setIntegral_mono (hint T₁) (((hint T₂).const_mul 2).add (hconst _)) hpt
        _ = 2 * ∫ x in B, hsNormSq (V.tangentProj x - T₂.starProjection) ∂V.weight +
              2 * (V.weight B).toReal * hsNormSq (T₁.starProjection - T₂.starProjection) := by
            rw [integral_add ((hint T₂).const_mul 2) (hconst _), integral_const_mul,
              setIntegral_const, smul_eq_mul, Measure.real_def]
            ring
  have projLimit : ∀ (n ℓ : ℕ) (S : ℕ → Submodule ℝ (Amb n ℓ)) (b lam : ℝ), 0 ≤ b → 0 ≤ lam → lam < 1 → (∀ j : ℕ, Module.finrank ℝ (S j) = n) → (∀ j : ℕ, hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) ≤ b * lam ^ j) → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ ∀ k : ℕ, hsNormSq (T.starProjection - (S k).starProjection) ≤ b * lam ^ k / (1 - Real.sqrt lam) ^ 2 := by
    intro n ℓ S b lam hb hlam0 hlam1 hrank hstep
    have hA := hsFacts (n + ℓ) (n + ℓ)
    set q := Real.sqrt lam with hq_def
    set a := Real.sqrt b with ha_def
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq1 : q < 1 := by
      rw [hq_def, Real.sqrt_lt' one_pos]; simpa using hlam1
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hsq_a : a ^ 2 = b := Real.sq_sqrt hb
    have hsq_q : q ^ 2 = lam := Real.sq_sqrt hlam0
    let P : ℕ → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun j => (S j).starProjection
    -- Step 1: consecutive Hilbert–Schmidt distances
    have hstep' : ∀ j, hsNorm (P (j + 1) - P j) ≤ a * q ^ j := by
      intro j
      have h : hsNormSq (P (j + 1) - P j) ≤ (a * q ^ j) ^ 2 := by
        calc hsNormSq (P (j + 1) - P j) ≤ b * lam ^ j := hstep j
          _ = (a * q ^ j) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hsq_q, hsq_a]
      unfold hsNorm
      calc Real.sqrt (hsNormSq (P (j + 1) - P j)) ≤ Real.sqrt ((a * q ^ j) ^ 2) :=
            Real.sqrt_le_sqrt h
        _ = a * q ^ j := Real.sqrt_sq (by positivity)
    -- Step 2: Cauchy in operator norm, hence convergent
    have hdist : ∀ j, dist (P j) (P (j + 1)) ≤ a * q ^ j := by
      intro j
      rw [dist_eq_norm, norm_sub_rev]
      exact le_trans (hA.2 (P (j + 1) - P j) 0).2.2.2.2 (hstep' j)
    have hcauchy : CauchySeq P := cauchySeq_of_le_geometric q a hq1 hdist
    obtain ⟨Q, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
    -- Step 3: the limit is a star projection
    have hidem : IsIdempotentElem Q := by
      have h1 : Tendsto (fun j => P j * P j) atTop (𝓝 (Q * Q)) := hlim.mul hlim
      have h2 : (fun j => P j * P j) = P := by
        funext j
        exact (S j).isIdempotentElem_starProjection
      rw [h2] at h1
      exact tendsto_nhds_unique h1 hlim
    have hidemL : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, IsIdempotentElem X →
        IsIdempotentElem (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ) := by
      intro X hX
      unfold IsIdempotentElem at hX ⊢
      rw [← ContinuousLinearMap.toLinearMap_mul, hX]
    have hsym : (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ).IsSymmetric := by
      intro x y
      have hx : Tendsto (fun j => P j x) atTop (𝓝 (Q x)) :=
        ((ContinuousLinearMap.apply ℝ (Amb n ℓ) x).continuous.tendsto Q).comp hlim
      have hy : Tendsto (fun j => P j y) atTop (𝓝 (Q y)) :=
        ((ContinuousLinearMap.apply ℝ (Amb n ℓ) y).continuous.tendsto Q).comp hlim
      have h1 : Tendsto (fun j => inner ℝ (P j x) y) atTop (𝓝 (inner ℝ (Q x) y)) :=
        hx.inner tendsto_const_nhds
      have h2 : Tendsto (fun j => inner ℝ x (P j y)) atTop (𝓝 (inner ℝ x (Q y))) :=
        tendsto_const_nhds.inner hy
      have h3 : (fun j => inner ℝ (P j x) y) = fun j => inner ℝ x (P j y) := by
        funext j
        exact Submodule.inner_starProjection_left_eq_right (S j) x y
      rw [h3] at h1
      exact tendsto_nhds_unique h1 h2
    have hsp : (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ).IsSymmetricProjection := ⟨hidemL Q hidem, hsym⟩
    obtain ⟨hinst, hQeq'⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hsp
    have hQeq : Q = (LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ)).starProjection := by
      apply ContinuousLinearMap.coe_injective
      exact hQeq'
    -- Step 4: rank via the trace
    let trL : (Amb n ℓ →L[ℝ] Amb n ℓ) →ₗ[ℝ] ℝ :=
      (LinearMap.trace ℝ (Amb n ℓ)).comp (ContinuousLinearMap.coeLM ℝ)
    have htrL : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, trL X = LinearMap.trace ℝ (Amb n ℓ) (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ) :=
      fun X => rfl
    have htr_idem : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, IsIdempotentElem X →
        trL X = (Module.finrank ℝ (LinearMap.range (X : Amb n ℓ →ₗ[ℝ] Amb n ℓ)) : ℝ) := by
      intro X hX
      rw [htrL]
      exact (LinearMap.IsIdempotentElem.isProj_range _ (hidemL X hX)).trace
    have htrP : ∀ j, trL (P j) = (n : ℝ) := by
      intro j
      rw [htr_idem _ (S j).isIdempotentElem_starProjection]
      have : LinearMap.range (P j : Amb n ℓ →ₗ[ℝ] Amb n ℓ) = S j := Submodule.range_starProjection (S j)
      rw [this, hrank j]
    have htrc : Continuous trL := LinearMap.continuous_of_finiteDimensional trL
    have htrQ : trL Q = (n : ℝ) := by
      have h1 : Tendsto (fun j => trL (P j)) atTop (𝓝 (trL Q)) := (htrc.tendsto Q).comp hlim
      have h2 : (fun j => trL (P j)) = fun _ => (n : ℝ) := funext htrP
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    refine ⟨LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ), ?_, ?_⟩
    · have h := htr_idem Q hidem
      rw [htrQ] at h
      exact_mod_cast h.symm
    -- Step 5: tail bound
    intro k
    have hTQ : (LinearMap.range (Q : Amb n ℓ →ₗ[ℝ] Amb n ℓ)).starProjection = Q := hQeq.symm
    rw [hTQ]
    have hq1' : 0 < 1 - q := by linarith
    have hsum : ∀ N, k ≤ N → hsNorm (P N - P k) ≤ a * (q ^ k - q ^ N) / (1 - q) := by
      intro N hkN
      induction N, hkN using Nat.le_induction with
      | base => simp [hsNorm, hsNormSq]
      | succ N hkN ih =>
        calc hsNorm (P (N + 1) - P k) = hsNorm ((P (N + 1) - P N) + (P N - P k)) := by
              congr 1; abel
          _ ≤ hsNorm (P (N + 1) - P N) + hsNorm (P N - P k) := (hA.2 _ _).2.2.2.1
          _ ≤ a * q ^ N + a * (q ^ k - q ^ N) / (1 - q) := add_le_add (hstep' N) ih
          _ = a * (q ^ k - q ^ (N + 1)) / (1 - q) := by
              field_simp
              ring
    have hgeom : ∀ N, a * (q ^ k - q ^ N) / (1 - q) ≤ a * q ^ k / (1 - q) := by
      intro N
      apply div_le_div_of_nonneg_right _ hq1'.le
      have : 0 ≤ q ^ N := pow_nonneg hq0 N
      nlinarith
    have hcont : Continuous (fun X : Amb n ℓ →L[ℝ] Amb n ℓ => hsNorm X) :=
      Real.continuous_sqrt.comp hA.1
    have hlimk : Tendsto (fun N => hsNorm (P N - P k)) atTop (𝓝 (hsNorm (Q - P k))) :=
      (hcont.tendsto _).comp (hlim.sub_const (P k))
    have hbound : hsNorm (Q - P k) ≤ a * q ^ k / (1 - q) := by
      refine le_of_tendsto hlimk ?_
      exact Filter.eventually_atTop.2 ⟨k, fun N hN => le_trans (hsum N hN) (hgeom N)⟩
    have hnn : 0 ≤ hsNorm (Q - P k) := Real.sqrt_nonneg _
    calc hsNormSq (Q - (S k).starProjection) = hsNorm (Q - P k) ^ 2 := ((hA.2 _ 0).2.1).symm
      _ ≤ (a * q ^ k / (1 - q)) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = b * lam ^ k / (1 - q) ^ 2 := by
          rw [div_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hsq_q, hsq_a]
  have consPlanes : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ξ : Amb n ℓ) (σ η c lam A : ℝ) (S : ℕ → Submodule ℝ (Amb n ℓ)), 0 < σ → closedBall ξ σ ⊆ U → 0 < η → η ≤ 1 → 0 < c → 0 ≤ lam → lam ≤ 1 → 0 ≤ A → (∀ j : ℕ, ENNReal.ofReal (c * (η ^ (j + 1) * σ) ^ n) ≤ V.weight (closedBall ξ (η ^ (j + 1) * σ))) → (∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤ lam ^ j * A) → ∀ j : ℕ, hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) ≤ 4 * c⁻¹ * (η ^ n)⁻¹ * lam ^ j * A := by
    intro n ℓ U V hmeas ξ σ η c lam A S hσ0 hσU hη0 hη1 hc0 hlam0 hlam1 hA0 hlow hE j
    set r₀ := η ^ j * σ with hr₀
    set r₁ := η ^ (j + 1) * σ with hr₁
    have hr₀pos : 0 < r₀ := mul_pos (pow_pos hη0 j) hσ0
    have hr₁pos : 0 < r₁ := mul_pos (pow_pos hη0 (j + 1)) hσ0
    have hr₁r₀ : r₁ = η * r₀ := by rw [hr₁, hr₀]; ring
    have hr₁le : r₁ ≤ r₀ := by rw [hr₁r₀]; exact mul_le_of_le_one_left hr₀pos.le hη1
    have hr₀σ : r₀ ≤ σ := mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1)
    have hU₀ : closedBall ξ r₀ ⊆ U := (closedBall_subset_closedBall hr₀σ).trans hσU
    have hU₁ : closedBall ξ r₁ ⊆ U := (closedBall_subset_closedBall (hr₁le.trans hr₀σ)).trans hσU
    obtain ⟨hfin₁, -, -, hcmp, -⟩ :=
      tiltFacts n ℓ U V hmeas ξ r₁ hU₁ (S (j + 1)) (S j)
    obtain ⟨-, -, hmono₀, -, -⟩ := tiltFacts n ℓ U V hmeas ξ r₀ hU₀ (S j) (S j)
    have hI₁ : ∫ x in closedBall ξ r₁, hsNormSq (V.tangentProj x - (S (j + 1)).starProjection) ∂V.weight
        ≤ r₁ ^ n * (lam ^ (j + 1) * A) := by
      have h := hE (j + 1)
      unfold RectifiableVarifold.tiltExcess at h
      rwa [inv_mul_le_iff₀ (pow_pos hr₁pos n)] at h
    have hI₀ : ∫ x in closedBall ξ r₁, hsNormSq (V.tangentProj x - (S j).starProjection) ∂V.weight
        ≤ r₀ ^ n * (lam ^ j * A) := by
      have h := hE j
      unfold RectifiableVarifold.tiltExcess at h
      rw [inv_mul_le_iff₀ (pow_pos hr₀pos n)] at h
      exact le_trans (hmono₀ r₁ hr₁le) h
    have hmass : c * r₁ ^ n ≤ (V.weight (closedBall ξ r₁)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin₁.ne).mp (hlow j)
    have hmpos : 0 < (V.weight (closedBall ξ r₁)).toReal :=
      lt_of_lt_of_le (mul_pos hc0 (pow_pos hr₁pos n)) hmass
    set X := hsNormSq ((S (j + 1)).starProjection - (S j).starProjection) with hX_def
    have hX : (V.weight (closedBall ξ r₁)).toReal * X ≤
        2 * (r₁ ^ n * (lam ^ (j + 1) * A)) + 2 * (r₀ ^ n * (lam ^ j * A)) := by
      linarith [hcmp]
    have hr₀n : r₀ ^ n = (η ^ n)⁻¹ * r₁ ^ n := by
      rw [hr₁r₀, mul_pow η r₀ n, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hη0.ne'), one_mul]
    have hηn : 1 ≤ (η ^ n)⁻¹ := (one_le_inv₀ (pow_pos hη0 n)).mpr (pow_le_one₀ hη0.le hη1)
    have hlamj : lam ^ (j + 1) ≤ lam ^ j := pow_le_pow_of_le_one hlam0 hlam1 (Nat.le_succ j)
    have hK : 0 ≤ r₁ ^ n * (lam ^ j * A) := by positivity
    have hRHS : 2 * (r₁ ^ n * (lam ^ (j + 1) * A)) + 2 * (r₀ ^ n * (lam ^ j * A)) ≤
        4 * (η ^ n)⁻¹ * lam ^ j * A * r₁ ^ n := by
      have e1 : r₁ ^ n * (lam ^ (j + 1) * A) ≤ r₁ ^ n * (lam ^ j * A) := by
        apply mul_le_mul_of_nonneg_left _ (pow_pos hr₁pos n).le
        exact mul_le_mul_of_nonneg_right hlamj hA0
      have e2 : r₁ ^ n * (lam ^ j * A) ≤ (η ^ n)⁻¹ * (r₁ ^ n * (lam ^ j * A)) :=
        le_mul_of_one_le_left hK hηn
      rw [hr₀n]
      nlinarith [e1, e2]
    have hfinal : X ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * r₁ ^ n / (V.weight (closedBall ξ r₁)).toReal := by
      rw [le_div_iff₀ hmpos]
      linarith [hX, hRHS]
    calc X ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * r₁ ^ n / (V.weight (closedBall ξ r₁)).toReal := hfinal
      _ ≤ 4 * (η ^ n)⁻¹ * lam ^ j * A * r₁ ^ n / (c * r₁ ^ n) := by
          apply div_le_div_of_nonneg_left _ (mul_pos hc0 (pow_pos hr₁pos n)) hmass
          positivity
      _ = 4 * c⁻¹ * (η ^ n)⁻¹ * lam ^ j * A := by
          have : r₁ ^ n ≠ 0 := (pow_pos hr₁pos n).ne'
          field_simp
  have allScales : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ξ : Amb n ℓ) (σ η β D B A : ℝ) (S : ℕ → Submodule ℝ (Amb n ℓ)) (T : Submodule ℝ (Amb n ℓ)), 0 < σ → closedBall ξ σ ⊆ U → 0 < η → η < 1 → 0 ≤ β → 0 ≤ D → 0 ≤ B → 0 ≤ A → (∀ s : ℝ, 0 < s → s ≤ σ → V.weight (closedBall ξ s) ≤ ENNReal.ofReal (D * s ^ n)) → (∀ j : ℕ, V.tiltExcess ξ (η ^ j * σ) (S j) ≤ (η ^ β) ^ j * A) → (∀ j : ℕ, hsNormSq (T.starProjection - (S j).starProjection) ≤ B * (η ^ β) ^ j * A) → ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * (η ^ β)⁻¹ * (s / σ) ^ β * A := by
    intro n ℓ U V hmeas ξ σ η β D B A S T hσ0 hσU hη0 hη1 hβ0 hD0 hB0 hA0 hup hE hT s hs0 hsσ
    have hA := hsFacts (n + ℓ) (n + ℓ)
    set lam := η ^ β with hlam
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hη0 β
    -- Step 1: the dyadic scale containing s
    have hex : ∃ k : ℕ, η ^ k * σ < s := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hs0 hσ0) hη1
      exact ⟨k, by rwa [lt_div_iff₀ hσ0] at hk⟩
    classical
    have hk : η ^ (Nat.find hex) * σ < s := Nat.find_spec hex
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, pow_zero, one_mul] at hk
      linarith
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hjup : s ≤ η ^ j * σ := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      push Not at this
      exact this
    have hjlow : η ^ (j + 1) * σ < s := by rw [← hj]; exact hk
    set r := η ^ j * σ with hr
    have hrpos : 0 < r := mul_pos (pow_pos hη0 j) hσ0
    have hrσ : r ≤ σ := mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1.le)
    have hUr : closedBall ξ r ⊆ U := (closedBall_subset_closedBall hrσ).trans hσU
    have hUs : closedBall ξ s ⊆ U := (closedBall_subset_closedBall hsσ).trans hσU
    -- Step 2: integral estimate on B_s(ξ)
    obtain ⟨hfins, -, -, -, hchg⟩ := tiltFacts n ℓ U V hmeas ξ s hUs T (S j)
    obtain ⟨-, -, hmonor, -, -⟩ := tiltFacts n ℓ U V hmeas ξ r hUr (S j) (S j)
    have hIr : ∫ x in closedBall ξ r, hsNormSq (V.tangentProj x - (S j).starProjection) ∂V.weight
        ≤ r ^ n * (lam ^ j * A) := by
      have h := hE j
      unfold RectifiableVarifold.tiltExcess at h
      rwa [inv_mul_le_iff₀ (pow_pos hrpos n)] at h
    have hmass : (V.weight (closedBall ξ s)).toReal ≤ D * s ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hup s hs0 hsσ)
    have hIs : ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤
        2 * (r ^ n * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := by
      have h1 := le_trans (hmonor s hjup) hIr
      have h2 : (V.weight (closedBall ξ s)).toReal * hsNormSq (T.starProjection - (S j).starProjection)
          ≤ (D * s ^ n) * (B * lam ^ j * A) :=
        mul_le_mul hmass (hT j) (hA.2 _ 0).1 (by positivity)
      linarith [hchg]
    -- Step 3: compare the radii
    have hrs : r ≤ s / η := by
      rw [le_div_iff₀ hη0]
      have : η ^ (j + 1) * σ = r * η := by rw [hr]; ring
      linarith
    have hrn : r ^ n ≤ (η ^ n)⁻¹ * s ^ n := by
      calc r ^ n ≤ (s / η) ^ n := pow_le_pow_left₀ hrpos.le hrs n
        _ = (η ^ n)⁻¹ * s ^ n := by rw [div_pow]; ring
    have hsn : 0 < s ^ n := pow_pos hs0 n
    have hE1 : V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A := by
      unfold RectifiableVarifold.tiltExcess
      rw [inv_mul_le_iff₀ hsn]
      have hlj : 0 ≤ lam ^ j * A := by positivity
      calc ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
          ≤ 2 * (r ^ n * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := hIs
        _ ≤ 2 * (((η ^ n)⁻¹ * s ^ n) * (lam ^ j * A)) + 2 * ((D * s ^ n) * (B * lam ^ j * A)) := by
            have := mul_le_mul_of_nonneg_right hrn hlj
            linarith
        _ = s ^ n * ((2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A) := by ring
    -- Step 4: from the dyadic power to (s/σ)^β
    have hpow : lam ^ j ≤ lam⁻¹ * (s / σ) ^ β := by
      have h1 : lam ^ (j + 1) = (η ^ (j + 1)) ^ β := by
        rw [hlam, Real.rpow_pow_comm hη0.le]
      have h2 : η ^ (j + 1) ≤ s / σ := by
        rw [le_div_iff₀ hσ0]; exact hjlow.le
      have h3 : (η ^ (j + 1)) ^ β ≤ (s / σ) ^ β :=
        Real.rpow_le_rpow (pow_nonneg hη0.le _) h2 hβ0
      rw [le_inv_mul_iff₀ hlam0]
      calc lam * lam ^ j = lam ^ (j + 1) := by ring
        _ ≤ (s / σ) ^ β := h1 ▸ h3
    have hcoef : 0 ≤ 2 * (η ^ n)⁻¹ + 2 * D * B := by positivity
    calc V.tiltExcess ξ s T ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * lam ^ j * A := hE1
      _ ≤ (2 * (η ^ n)⁻¹ + 2 * D * B) * (lam⁻¹ * (s / σ) ^ β) * A := by
          apply mul_le_mul_of_nonneg_right _ hA0
          exact mul_le_mul_of_nonneg_left hpow hcoef
      _ = (2 * (η ^ n)⁻¹ + 2 * D * B) * lam⁻¹ * (s / σ) ^ β * A := by ring
  -- Main argument (Simon 5.2 proof steps (1)-(7) at ξ = 0)
  intro hTED n ℓ hn p hp cl cu hcl
  obtain ⟨η, δ₀, hη0, hη14, hδ₀0, hδ₀14, hdec⟩ := hTED n ℓ hn p hp
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    apply div_pos
    · exact Real.rpow_pos_of_pos Real.pi_pos _
    · exact Real.Gamma_pos_of_pos (by positivity)
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hα : 0 < 1 - (n : ℝ) / p := by
    have : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hp
    linarith
  have hβ0 : 0 < 2 * (1 - (n : ℝ) / p) := by positivity
  have hη1 : η < 1 := by linarith
  have hlam0 : 0 < η ^ (2 * (1 - (n : ℝ) / p)) := Real.rpow_pos_of_pos hη0 _
  have hlam1 : η ^ (2 * (1 - (n : ℝ) / p)) < 1 := Real.rpow_lt_one hη0.le hη1 hβ0
  -- Step 0: constants depending only on n, ℓ, p, cl, cu
  set ω : ℝ := unitBallVolume n with hω_def
  set lam : ℝ := η ^ (2 * (1 - (n : ℝ) / p)) with hlam_def
  set c : ℝ := cl * ω with hc_def
  have hc0 : 0 < c := mul_pos hcl hω
  set D : ℝ := cu * ω with hD_def
  set b : ℝ := 4 * c⁻¹ * (η ^ n)⁻¹ with hb_def
  have hb0 : 0 ≤ b := by positivity
  set CII : ℝ := b / (1 - Real.sqrt lam) ^ 2 with hCII_def
  have hCII0 : 0 ≤ CII := by positivity
  set CIII : ℝ := (2 * (η ^ n)⁻¹ + 2 * D * CII) * lam⁻¹ with hCIII_def
  refine ⟨δ₀, CII, CIII, hδ₀0, ?_⟩
  intro U hU V H δ ρ σ hδ0 hδ1 hAH hσ0 hσ1 hdens S₀ hS₀
  have hρ0 : 0 < ρ := hAH.1
  have hballU : closedBall (0 : Amb n ℓ) ρ ⊆ U := hAH.2.2.2.2.1
  have h0supp : (0 : Amb n ℓ) ∈ V.support := hAH.2.2.2.1
  have hδρ : 0 < δ * ρ := mul_pos hδ0 hρ0
  have h0mem : (0 : Amb n ℓ) ∈ V.support ∩ closedBall 0 (δ * ρ) :=
    ⟨h0supp, mem_closedBall_self hδρ.le⟩
  have hδ14 : δ ≤ 1 / 4 := le_trans hδ1 hδ₀14
  have hσρ : σ ≤ ρ := by nlinarith
  have hσU : closedBall (0 : Amb n ℓ) σ ⊆ U := (closedBall_subset_closedBall hσρ).trans hballU
  -- Step 1: measurability of the tangent projections (sibling tangent_ae)
  have hmeas : AEStronglyMeasurable V.tangentProj V.weight := (htan n ℓ hn U hU V).2.1
  set A : ℝ := V.tiltExcessStar H p δ 0 σ S₀ with hA_def
  have hA0 : 0 ≤ A := by
    simp only [hA_def, RectifiableVarifold.tiltExcessStar]
    exact le_max_of_le_right (mul_nonneg (inv_nonneg.mpr hδ0.le) (sq_nonneg _))
  -- Step 2: iterate 4.5 at ξ = 0 on the radii η^j σ
  have hex : ∀ j : ℕ, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
      V.tiltExcessStar H p δ 0 (η ^ j * σ) T ≤ lam ^ j * A := by
    intro j
    induction j with
    | zero => exact ⟨S₀, hS₀, by simp [hA_def]⟩
    | succ j ih =>
      obtain ⟨T, hT, hTb⟩ := ih
      have hσj0 : 0 < η ^ j * σ := mul_pos (pow_pos hη0 j) hσ0
      have hσj1 : η ^ j * σ ≤ δ * ρ / 2 :=
        le_trans (mul_le_of_le_one_left hσ0.le (pow_le_one₀ hη0.le hη1.le)) hσ1
      obtain ⟨T', hT', hT'b⟩ :=
        hdec U hU V H δ ρ hδ0 hδ1 hAH (η ^ j * σ) hσj0 hσj1 0 h0mem T hT
      refine ⟨T', hT', ?_⟩
      have heq : η ^ (j + 1) * σ = η * (η ^ j * σ) := by ring
      rw [heq]
      calc V.tiltExcessStar H p δ 0 (η * (η ^ j * σ)) T'
          ≤ lam * V.tiltExcessStar H p δ 0 (η ^ j * σ) T := hT'b
        _ ≤ lam * (lam ^ j * A) := mul_le_mul_of_nonneg_left hTb hlam0.le
        _ = lam ^ (j + 1) * A := by ring
  choose T hT hTb using hex
  classical
  obtain ⟨S, hS0, hS⟩ : ∃ S : ℕ → Submodule ℝ (Amb n ℓ), S 0 = S₀ ∧ ∀ j : ℕ,
      Module.finrank ℝ (S j) = n ∧ V.tiltExcessStar H p δ 0 (η ^ j * σ) (S j) ≤ lam ^ j * A := by
    refine ⟨fun j => if j = 0 then S₀ else T j, by simp, fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj
      simp [hS₀, hA_def]
    · beta_reduce
      rw [ite_eq_right_iff.mpr (fun h => absurd h hj)]
      exact ⟨hT j, hTb j⟩
  have hE : ∀ j : ℕ, V.tiltExcess 0 (η ^ j * σ) (S j) ≤ lam ^ j * A := by
    intro j
    refine le_trans ?_ (hS j).2
    simp only [RectifiableVarifold.tiltExcessStar]
    exact le_max_left _ _
  have hηpow : ∀ j : ℕ, η ^ j ≤ 1 := fun j => pow_le_one₀ hη0.le hη1.le
  -- Step 3: lower density bound at the radii η^(j+1) σ, then consecutive planes
  have hlow : ∀ j : ℕ, ENNReal.ofReal (c * (η ^ (j + 1) * σ) ^ n) ≤
      V.weight (closedBall 0 (η ^ (j + 1) * σ)) := by
    intro j
    have hs0 : 0 < η ^ (j + 1) * σ := mul_pos (pow_pos hη0 _) hσ0
    have hsσ : η ^ (j + 1) * σ ≤ σ := mul_le_of_le_one_left hσ0.le (hηpow _)
    have h := (hdens (η ^ (j + 1) * σ) hs0 hsσ).1
    apply ENNReal.ofReal_le_of_le_toReal
    calc c * (η ^ (j + 1) * σ) ^ n = cl * ω * (η ^ (j + 1) * σ) ^ n := by rw [hc_def]
      _ ≤ _ := h
  have hcons := consPlanes n ℓ U V hmeas 0 σ η c lam A S hσ0 hσU hη0 hη1.le hc0 hlam0.le
    hlam1.le hA0 hlow hE
  -- Step 4: limit plane
  obtain ⟨Tlim, hTlim, hTtail⟩ := projLimit n ℓ S (b * A) lam (mul_nonneg hb0 hA0)
    hlam0.le hlam1 (fun j => (hS j).1) (by
      intro j
      calc hsNormSq ((S (j + 1)).starProjection - (S j).starProjection)
          ≤ 4 * c⁻¹ * (η ^ n)⁻¹ * lam ^ j * A := hcons j
        _ = b * A * lam ^ j := by rw [hb_def]; ring)
  have hTk : ∀ k : ℕ, hsNormSq (Tlim.starProjection - (S k).starProjection) ≤
      CII * lam ^ k * A := by
    intro k
    calc hsNormSq (Tlim.starProjection - (S k).starProjection)
        ≤ b * A * lam ^ k / (1 - Real.sqrt lam) ^ 2 := hTtail k
      _ = CII * lam ^ k * A := by rw [hCII_def]; ring
  refine ⟨Tlim, hTlim, ?_, ?_⟩
  · have h0 := hTk 0
    rw [hS0, pow_zero, mul_one] at h0
    exact h0
  · -- Step 5: upper density bound and decay at all scales
    have hcu : 0 ≤ cu := by
      obtain ⟨hl, hu⟩ := hdens σ hσ0 le_rfl
      have hpos : 0 < ω * σ ^ n := mul_pos hω (pow_pos hσ0 n)
      have h1 : cl * (ω * σ ^ n) ≤ cu * (ω * σ ^ n) := by
        rw [← mul_assoc, ← mul_assoc]
        exact hl.trans hu
      have h2 : cl ≤ cu := le_of_mul_le_mul_right h1 hpos
      linarith
    have hD0 : 0 ≤ D := mul_nonneg hcu hω.le
    have hup : ∀ s : ℝ, 0 < s → s ≤ σ →
        V.weight (closedBall 0 s) ≤ ENNReal.ofReal (D * s ^ n) := by
      intro s hs0 hsσ
      obtain ⟨hl, hu⟩ := hdens s hs0 hsσ
      have hpos : 0 < (V.weight (closedBall 0 s)).toReal :=
        lt_of_lt_of_le (mul_pos (mul_pos hcl hω) (pow_pos hs0 n)) hl
      have hne : V.weight (closedBall 0 s) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hpos).2.ne
      rw [ENNReal.le_ofReal_iff_toReal_le hne (mul_nonneg hD0 (pow_pos hs0 n).le)]
      calc (V.weight (closedBall 0 s)).toReal ≤ cu * ω * s ^ n := hu
        _ = D * s ^ n := by rw [hD_def]
    have hall := allScales n ℓ U V hmeas 0 σ η (2 * (1 - (n : ℝ) / p)) D CII A S Tlim
      hσ0 hσU hη0 hη1 hβ0.le hD0 hCII0 hA0 hup hE hTk
    intro s hs0 hsσ
    calc V.tiltExcess 0 s Tlim
        ≤ (2 * (η ^ n)⁻¹ + 2 * D * CII) * lam⁻¹ * (s / σ) ^ (2 * (1 - (n : ℝ) / p)) * A :=
          hall s hs0 hsσ
      _ = CIII * (s / σ) ^ (2 * (1 - (n : ℝ) / p)) * A := by rw [hCIII_def]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
