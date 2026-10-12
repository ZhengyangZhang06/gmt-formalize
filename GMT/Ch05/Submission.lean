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

/-- **Rellich compactness on the unit ball** (Simon Ch. 5, fact (R) in the proof of Lemma 3.1;
Gilbarg–Trudinger, Thm. 7.26).  If `f k ∈ W^{1,2}(B̆₁(0))` with weak gradients `g k` and
`∫_B |f k|² ≤ A`, `∫_B |g k|² ≤ A` for all `k`, then a subsequence `f (φ k)` converges in
`L²(B̆₁(0))` to some `w ∈ L²(B̆₁(0))`.

Proof (parent-supplied natural proof, steps 0–6): pass to measurable representatives; mollify at
the scales `ε_m = 1/(m+2)` with the normalized tent kernel `max (ε - ‖z‖) 0 / I`.  By
`w12_ball_translation_estimate` the interior mollification error on `B̆_r(0)` is `≤ ε² A`.  For
fixed `m` the mollified functions are uniformly bounded and equi-Lipschitz, so a finite `δ`-net of
`B₁(0)` and Bolzano–Weierstrass in `ℝ^net` give, for every tolerance, a subsequence that is
uniformly Cauchy up to that tolerance; a diagonal argument over all pairs (scale, tolerance) gives
one subsequence `φ`.  `w12_ball_boundary_layer_estimate` controls the annulus
`B̆₁(0) \ B̆_r(0)`, so `f (φ k)` is Cauchy in `L²(B̆₁(0))`, and completeness of `L²` gives `w`. -/
theorem w12_ball_rellich_compactness : ∀ n : ℕ, 1 ≤ n → ∀ (A : ℝ) (f : ℕ → Rn n → ℝ) (g : ℕ → Rn n → Rn n), (∀ k, IsW12WithGradient (f k) (g k) (ball 0 1)) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖f k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖g k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → ∃ (φ : ℕ → ℕ) (w : Rn n → ℝ), StrictMono φ ∧ MemLp w 2 (volume.restrict (ball (0 : Rn n) 1)) ∧ Tendsto (fun k => ∫⁻ x in ball (0 : Rn n) 1, ‖f (φ k) x - w x‖ₑ ^ 2) atTop (𝓝 0) := by
  intro n hn
  -- Step 1 (and 3): a normalized tent kernel `ρ` supported in `B_ε(0)`, and uniform sup and
  -- Lipschitz bounds for `x ↦ ∫_B ρ (x - y) u y` in terms of `∫_B |u|²`.
  have hmol : ∀ ε : ℝ, 0 < ε → ∃ (ρ : Rn n → ℝ) (C : ℝ), Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      (∀ z, ε < ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 ∧ ∀ (a : ℝ) (u : Rn n → ℝ),
      MemLp u 2 (volume.restrict (ball (0 : Rn n) 1)) →
      ∫⁻ y in ball (0 : Rn n) 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal a → ∀ x x' : Rn n,
      |∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y| ≤ C * Real.sqrt a ∧
      |(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - ∫ y in ball (0 : Rn n) 1, ρ (x' - y) * u y| ≤
        C * Real.sqrt a * ‖x - x'‖ := by
    intro ε hε
    -- the tent `τ z = max (ε - ‖z‖) 0` and its integral `I > 0`
    let τ : Rn n → ℝ := fun z => max (ε - ‖z‖) 0
    have hτc : Continuous τ := (continuous_const.sub continuous_norm).max continuous_const
    have hτnn : ∀ z, 0 ≤ τ z := fun z => le_max_right _ _
    have hτ0 : ∀ z, ε < ‖z‖ → τ z = 0 := fun z hz => max_eq_right (by linarith)
    have hτint : Integrable τ := hτc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall 0 ε) fun z hz =>
        hτ0 z (by rwa [mem_closedBall_zero_iff, not_le] at hz))
    have hIpos : 0 < ∫ z, τ z := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hτnn z) hτint]
      refine lt_of_lt_of_le (measure_ball_pos volume (0 : Rn n) hε) (measure_mono fun z hz => ?_)
      rw [mem_ball_zero_iff] at hz
      exact (lt_max_of_lt_left (sub_pos.mpr hz)).ne'
    set I : ℝ := ∫ z, τ z with hI
    let ρ : Rn n → ℝ := fun z => τ z / I
    have hρc : Continuous ρ := hτc.div_const I
    have hM : ∀ z, |ρ z| ≤ ε / I := fun z => by
      show |τ z / I| ≤ ε / I
      rw [abs_of_nonneg (div_nonneg (hτnn z) hIpos.le)]
      exact div_le_div_of_nonneg_right (max_le (by linarith [norm_nonneg z]) hε.le) hIpos.le
    have hL : ∀ p q, |ρ p - ρ q| ≤ 1 / I * ‖p - q‖ := fun p q => by
      show |τ p / I - τ q / I| ≤ 1 / I * ‖p - q‖
      have h1 : |τ p - τ q| ≤ ‖p - q‖ := (abs_max_sub_max_le_abs _ _ _).trans (by
        rw [show ε - ‖p‖ - (ε - ‖q‖) = ‖q‖ - ‖p‖ by ring, abs_sub_comm]
        exact abs_norm_sub_norm_le p q)
      rw [← sub_div, abs_div, abs_of_pos hIpos, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right h1 hIpos.le
    set B : Set (Rn n) := ball (0 : Rn n) 1 with hB
    set V : ℝ := (volume B).toReal with hV
    have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin
    -- L¹ bound via Hölder (eLpNorm comparison)
    have hL1 : ∀ (a : ℝ) (u : Rn n → ℝ), MemLp u 2 (volume.restrict B) →
        ∫⁻ y in B, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal a →
        ∫ y in B, |u y| ≤ Real.sqrt V * Real.sqrt a := by
      intro a u hu ha
      have hum : AEStronglyMeasurable u (volume.restrict B) := hu.aestronglyMeasurable
      have key1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
        (μ := volume.restrict B) (by norm_num) hum
      rw [eLpNorm_one_eq_lintegral_enorm hum,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hum,
        Measure.restrict_apply_univ] at key1
      have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
      simp only [h2, ENNReal.toReal_one, ENNReal.rpow_two] at key1
      have key2 : ∫⁻ y in B, ‖u y‖ₑ ≤
          ENNReal.ofReal a ^ (1 / 2 : ℝ) * volume B ^ (1 / 2 : ℝ) := by
        refine key1.trans ?_
        have e : (1 / 1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
        rw [e]
        gcongr
      have hT : ∫ y in B, |u y| = (∫⁻ y in B, ‖u y‖ₑ).toReal := by
        simp_rw [← Real.norm_eq_abs]
        exact integral_norm_eq_lintegral_enorm hum
      rw [hT]
      have hfin : ENNReal.ofReal a ^ (1 / 2 : ℝ) * volume B ^ (1 / 2 : ℝ) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      refine (ENNReal.toReal_mono hfin key2).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← hV, mul_comm]
      congr 1
      rcases le_total 0 a with h | h
      · rw [ENNReal.toReal_ofReal h]
      · rw [ENNReal.ofReal_of_nonpos h, Real.sqrt_eq_zero_of_nonpos h]
        simp
    have hML : 0 ≤ max (ε / I) (1 / I) := le_max_of_le_right (by positivity)
    refine ⟨ρ, max (ε / I) (1 / I) * Real.sqrt V, hρc, fun z => div_nonneg (hτnn z) hIpos.le,
      fun z hz => by simp only [ρ, hτ0 z hz, zero_div], ?_, ?_⟩
    · show ∫ z, τ z / I = 1
      rw [integral_div, div_self hIpos.ne']
    intro a u hu ha x x'
    have hui : Integrable u (volume.restrict B) := hu.integrable (by norm_num)
    have hT := hL1 a u hu ha
    have hTnn : 0 ≤ ∫ y in B, |u y| := integral_nonneg (fun _ => abs_nonneg _)
    have hcomp : ∀ x0 : Rn n, Continuous (fun y => ρ (x0 - y)) :=
      fun x0 => hρc.comp (continuous_const.sub continuous_id)
    have hint : ∀ x0 : Rn n, Integrable (fun y => ρ (x0 - y) * u y) (volume.restrict B) :=
      fun x0 => hui.bdd_mul (c := ε / I) (hcomp x0).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM (x0 - y))
    have hbound : ∀ K : ℝ, ∫ y in B, K * |u y| = K * ∫ y in B, |u y| :=
      fun K => integral_const_mul K _
    constructor
    · have h1 : ‖∫ y in B, ρ (x - y) * u y‖ ≤ ∫ y in B, ε / I * |u y| :=
        norm_integral_le_of_norm_le (hui.abs.const_mul (ε / I)) (Eventually.of_forall fun y => by
          rw [norm_mul, Real.norm_eq_abs (u y), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hM (x - y)) (abs_nonneg _))
      rw [hbound, Real.norm_eq_abs] at h1
      calc |∫ y in B, ρ (x - y) * u y| ≤ ε / I * ∫ y in B, |u y| := h1
        _ ≤ max (ε / I) (1 / I) * ∫ y in B, |u y| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hTnn
        _ ≤ max (ε / I) (1 / I) * (Real.sqrt V * Real.sqrt a) := mul_le_mul_of_nonneg_left hT hML
        _ = max (ε / I) (1 / I) * Real.sqrt V * Real.sqrt a := by ring
    · rw [← integral_sub (hint x) (hint x')]
      have h1 : ‖∫ y in B, (ρ (x - y) * u y - ρ (x' - y) * u y)‖ ≤
          ∫ y in B, (1 / I * ‖x - x'‖) * |u y| :=
        norm_integral_le_of_norm_le (hui.abs.const_mul _) (Eventually.of_forall fun y => by
          rw [← sub_mul, norm_mul, Real.norm_eq_abs (u y), Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := hL (x - y) (x' - y)
          rwa [sub_sub_sub_cancel_right] at this)
      rw [hbound, Real.norm_eq_abs] at h1
      have hxx : 0 ≤ ‖x - x'‖ := norm_nonneg _
      calc |∫ y in B, (ρ (x - y) * u y - ρ (x' - y) * u y)|
          ≤ 1 / I * ‖x - x'‖ * ∫ y in B, |u y| := h1
        _ ≤ max (ε / I) (1 / I) * ‖x - x'‖ * ∫ y in B, |u y| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hxx) hTnn
        _ ≤ max (ε / I) (1 / I) * ‖x - x'‖ * (Real.sqrt V * Real.sqrt a) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg hML hxx)
        _ = max (ε / I) (1 / I) * Real.sqrt V * Real.sqrt a * ‖x - x'‖ := by ring
  -- Step 2: the interior mollification error, by Jensen for the probability density `ρ`,
  -- Tonelli, and a translation estimate.
  have hmolerr : ∀ (ρ u : Rn n → ℝ) (ε r : ℝ) (E : ℝ≥0∞), Continuous ρ → (∀ z, 0 ≤ ρ z) →
      (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → Measurable u → 0 < r → ε < 1 - r →
      (∀ z : Rn n, ‖z‖ < 1 - r →
        ∫⁻ x in ball (0 : Rn n) r, ‖u (x - z) - u x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖z‖ ^ 2) * E) →
      ∫⁻ x in ball (0 : Rn n) r, ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2 ≤
        ENNReal.ofReal (ε ^ 2) * E := by
    clear hmol
    intro ρ u ε r E hρc hρ0 hρsupp hρ1 hu hr hεr htrans
    -- preliminaries on ρ
    have hρint : Integrable ρ := by
      by_contra h
      rw [integral_undef h] at hρ1
      exact zero_ne_one hρ1
    have hρlint : ∫⁻ z, ENNReal.ofReal (ρ z) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hρint (Filter.Eventually.of_forall hρ0), hρ1,
        ENNReal.ofReal_one]
    have hsupp : ∀ z, ρ z ≠ 0 → ‖z‖ ≤ ε := by
      intro z hz
      by_contra h
      exact hz (hρsupp z (lt_of_not_ge h))
    have hρm : Measurable fun z => ENNReal.ofReal (ρ z) := hρc.measurable.ennreal_ofReal
    -- change of variables `y = x - z`
    have hconv : ∀ x ∈ ball (0 : Rn n) r,
        (∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) = ∫ z, ρ z * u (x - z) := by
      intro x hx
      rw [← integral_indicator measurableSet_ball,
        ← integral_sub_left_eq_self ((ball (0 : Rn n) 1).indicator (fun y => ρ (x - y) * u y))
          (volume : Measure (Rn n)) x]
      congr 1
      ext z
      by_cases hz : ρ z = 0
      · rw [hz, zero_mul]
        by_cases hm : x - z ∈ ball (0 : Rn n) 1
        · rw [indicator_of_mem hm, sub_sub_cancel, hz, zero_mul]
        · rw [indicator_of_notMem hm]
      · have hzε := hsupp z hz
        have hm : x - z ∈ ball (0 : Rn n) 1 := by
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le x z
            _ < r + (1 - r) := by linarith
            _ = 1 := by ring
        rw [indicator_of_mem hm, sub_sub_cancel]
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x ∈ ball (0 : Rn n) r,
        ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2 ≤
          ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 := by
      intro x hx
      rw [hconv x hx]
      set J := ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 with hJdef
      by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      have hDm : Measurable fun z => u (x - z) - u x :=
        (hu.comp (measurable_const.sub measurable_id)).sub measurable_const
      have hHol : ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ≤ J ^ (1 / 2 : ℝ) := by
        have := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
          (f := fun z => ENNReal.ofReal (ρ z))
          (g := fun z => ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2)
          hρm.aemeasurable (hρm.mul (hDm.enorm.pow_const 2)).aemeasurable
          (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
        rw [hρlint, ENNReal.one_rpow, one_mul] at this
        refine le_trans (le_of_eq ?_) this
        congr 1
        ext z
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
      have hfin : ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ < ⊤ :=
        lt_of_le_of_lt hHol (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ)
      have hnorm : ∀ z, ‖ρ z * (u (x - z) - u x)‖ₑ =
          ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ := by
        intro z
        rw [enorm_mul, Real.enorm_of_nonneg (hρ0 z)]
      have hint : Integrable (fun z => ρ z * (u (x - z) - u x)) := by
        refine ⟨(hρc.measurable.mul hDm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simp_rw [hnorm]
        exact hfin
      have hint2 : Integrable (fun z => ρ z * u (x - z)) := by
        refine (hint.add (hρint.mul_const (u x))).congr (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.add_apply]
        ring
      have heq : (∫ z, ρ z * u (x - z)) - u x = ∫ z, ρ z * (u (x - z) - u x) := by
        have h1 : ∫ z, ρ z * u x = u x := by rw [integral_mul_const, hρ1, one_mul]
        simp_rw [mul_sub]
        rw [integral_sub hint2 (hρint.mul_const (u x)), h1]
      rw [heq]
      calc ‖∫ z, ρ z * (u (x - z) - u x)‖ₑ ^ 2
          ≤ (∫⁻ z, ‖ρ z * (u (x - z) - u x)‖ₑ) ^ 2 := by
            gcongr
            exact enorm_integral_le_lintegral_enorm _
        _ = (∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ) ^ 2 := by simp_rw [hnorm]
        _ ≤ (J ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
        _ = J := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            norm_num
    -- integrate over `B̆_r(0)` and use Tonelli
    have hjm : Measurable (Function.uncurry fun (x z : Rn n) =>
        ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2) := by
      have h1 : Measurable fun p : Rn n × Rn n => ENNReal.ofReal (ρ p.2) :=
        (hρc.measurable.comp measurable_snd).ennreal_ofReal
      have h2 : Measurable fun p : Rn n × Rn n => ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2 :=
        ((hu.comp (measurable_fst.sub measurable_snd)).sub (hu.comp measurable_fst)).enorm.pow_const 2
      exact h1.mul h2
    calc ∫⁻ x in ball (0 : Rn n) r, ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2
        ≤ ∫⁻ x in ball (0 : Rn n) r, ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ∫⁻ z, ∫⁻ x in ball (0 : Rn n) r, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 :=
          lintegral_lintegral_swap hjm.aemeasurable
      _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ∫⁻ x in ball (0 : Rn n) r, ‖u (x - z) - u x‖ₑ ^ 2 := by
          congr 1
          ext z
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * (ENNReal.ofReal (ε ^ 2) * E) := by
          apply lintegral_mono
          intro z
          dsimp only
          by_cases hz : ρ z = 0
          · rw [hz, ENNReal.ofReal_zero, zero_mul, zero_mul]
          · have hzε := hsupp z hz
            gcongr
            calc _ ≤ ENNReal.ofReal (‖z‖ ^ 2) * E := htrans z (by linarith)
              _ ≤ _ := by gcongr
      _ = (∫⁻ z, ENNReal.ofReal (ρ z)) * (ENNReal.ofReal (ε ^ 2) * E) :=
          lintegral_mul_const _ hρm
      _ = ENNReal.ofReal (ε ^ 2) * E := by rw [hρlint, one_mul]
  -- Step 4a: for uniformly bounded, equi-Lipschitz functions on a compact set `K` and a tolerance
  -- `η > 0`, every subsequence has a further subsequence that is eventually `η`-close uniformly
  -- on `K` (a finite `δ`-net of `K` and Bolzano–Weierstrass in `ℝ^net`).
  have hAA : ∀ (K : Set (Rn n)) (h : ℕ → Rn n → ℝ) (M L : ℝ), IsCompact K →
      (∀ k, ∀ x ∈ K, |h k x| ≤ M) → (∀ k, ∀ x ∈ K, ∀ y ∈ K, |h k x - h k y| ≤ L * dist x y) →
      ∀ η : ℝ, 0 < η → ∀ ψ : ℕ → ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∀ x ∈ K, |h (ψ (σ k)) x - h (ψ (σ l)) x| ≤ η := by
    clear hmol hmolerr
    intro K h M L hK hM hL η hη ψ
    set L' : ℝ := max L 0 with hL'
    have hL'0 : 0 ≤ L' := le_max_right _ _
    set δ : ℝ := η / (3 * (L' + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδη : 3 * (L' + 1) * δ = η := by
      rw [hδ, mul_comm]
      exact div_mul_cancel₀ η (by positivity)
    obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK hδ0
    have : Fintype t := htfin.fintype
    let v : ℕ → (t → ℝ) := fun k y => h (ψ k) y
    have hvmem : ∀ k, v k ∈ Set.pi univ fun _ : t => Icc (-M) M := fun k y _ =>
      abs_le.mp (hM (ψ k) y (htK y.2))
    obtain ⟨a, -, σ, hσ, hlim⟩ :=
      (isCompact_univ_pi fun _ : t => isCompact_Icc (a := -M) (b := M)).tendsto_subseq hvmem
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq δ hδ0
    refine ⟨σ, hσ, N, fun k l hk hl x hx => ?_⟩
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    have hxy' : dist x y ≤ δ := (mem_ball.mp hxy).le
    have h1 : |h (ψ (σ k)) y - h (ψ (σ l)) y| ≤ δ := by
      have := (dist_le_pi_dist (v (σ k)) (v (σ l)) ⟨y, hyt⟩).trans (hN k hk l hl).le
      rwa [Real.dist_eq] at this
    have hLip : ∀ j, |h j x - h j y| ≤ L' * δ := fun j =>
      (hL j x hx y (htK hyt)).trans (mul_le_mul (le_max_left _ _) hxy' dist_nonneg hL'0)
    have h2 := hLip (ψ (σ k))
    have h3 := hLip (ψ (σ l))
    rw [abs_sub_comm] at h3
    calc |h (ψ (σ k)) x - h (ψ (σ l)) x|
        ≤ |h (ψ (σ k)) x - h (ψ (σ k)) y| + |h (ψ (σ k)) y - h (ψ (σ l)) y| +
            |h (ψ (σ l)) y - h (ψ (σ l)) x| := by
          have e1 := abs_sub_le (h (ψ (σ k)) x) (h (ψ (σ k)) y) (h (ψ (σ l)) x)
          have e2 := abs_sub_le (h (ψ (σ k)) y) (h (ψ (σ l)) y) (h (ψ (σ l)) x)
          linarith
      _ ≤ L' * δ + δ + L' * δ := by linarith
      _ ≤ η := by linarith [mul_nonneg hL'0 hδ0.le]
  -- Step 4b: the diagonal argument for countably many eventually-pairwise properties that can
  -- each be achieved along a further subsequence of any subsequence.
  have hdiag : ∀ R : ℕ → ℕ → ℕ → Prop, (∀ (j : ℕ) (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l → R j (ψ (σ k)) (ψ (σ l))) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l → R j (φ k) (φ l) := by
    clear hmol hmolerr hAA
    intro R hR
    choose s hs_mono hs_cauchy using hR
    -- `Σ_0 = id`, `Σ_{m+1} = Σ_m ∘ s m Σ_m`, in the subtype of strictly increasing maps
    obtain ⟨Sig, hSigS⟩ : ∃ Sig : ℕ → {ψ : ℕ → ℕ // StrictMono ψ},
        ∀ m, (Sig (m + 1)).1 = (Sig m).1 ∘ s m (Sig m).1 (Sig m).2 :=
      ⟨fun m => Nat.rec (motive := fun _ => {ψ : ℕ → ℕ // StrictMono ψ}) ⟨id, strictMono_id⟩
        (fun m Ψ => ⟨Ψ.1 ∘ s m Ψ.1 Ψ.2, Ψ.2.comp (hs_mono m Ψ.1 Ψ.2)⟩) m, fun _ => rfl⟩
    -- nesting: for `m ≤ k`, the value of `Σ_k` at `i` is a value of `Σ_m` at some `j ≥ i`
    have nest : ∀ m k, m ≤ k → ∀ i, ∃ j, i ≤ j ∧ (Sig k).1 i = (Sig m).1 j := by
      intro m k hmk
      induction k, hmk using Nat.le_induction with
      | base => exact fun i => ⟨i, le_rfl, rfl⟩
      | succ k _ ih =>
        intro i
        obtain ⟨j, hij, hj⟩ := ih (s k (Sig k).1 (Sig k).2 i)
        exact ⟨j, (hs_mono k _ _).le_apply.trans hij, by rw [hSigS]; exact hj⟩
    -- the diagonal map `φ k = Σ_k k`
    refine ⟨fun k => (Sig k).1 k, strictMono_nat_of_lt_succ fun k => ?_, fun m => ?_⟩
    · show (Sig k).1 k < (Sig (k + 1)).1 (k + 1)
      rw [hSigS]
      exact (Sig k).2 ((Nat.lt_succ_self k).trans_le (hs_mono k _ _).le_apply)
    · obtain ⟨N, hN⟩ := hs_cauchy m (Sig m).1 (Sig m).2
      refine ⟨max N (m + 1), fun k l hk hl => ?_⟩
      obtain ⟨a, hka, ha⟩ := nest (m + 1) k ((le_max_right _ _).trans hk) k
      obtain ⟨b, hlb, hb⟩ := nest (m + 1) l ((le_max_right _ _).trans hl) l
      show R m ((Sig k).1 k) ((Sig l).1 l)
      rw [ha, hb, hSigS]
      exact hN a b ((le_max_left _ _).trans (hk.trans hka)) ((le_max_left _ _).trans (hl.trans hlb))
  -- Step 5 (criterion): uniform smallness on the annulus plus uniform interior approximation by
  -- functions that are uniformly Cauchy gives the Cauchy property in `L²(B̆₁(0))`.
  have hcrit : ∀ u : ℕ → Rn n → ℝ,
      (∀ k, AEStronglyMeasurable (u k) (volume.restrict (ball (0 : Rn n) 1))) →
      (∀ η : ℝ, 0 < η → ∃ (r : ℝ) (v : ℕ → Rn n → ℝ), 0 < r ∧ r < 1 ∧
        (∀ k, AEStronglyMeasurable (v k) (volume.restrict (ball (0 : Rn n) r))) ∧
        (∀ k, ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x‖ₑ ^ 2 ≤ ENNReal.ofReal η) ∧
        (∀ k, ∫⁻ x in ball (0 : Rn n) r, ‖u k x - v k x‖ₑ ^ 2 ≤ ENNReal.ofReal η) ∧
        ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
          ∀ x ∈ ball (0 : Rn n) r, |v k x - v l x| ≤ θ) →
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2 ≤ ENNReal.ofReal η := by
    clear hmol hmolerr hAA hdiag
    intro u hu H η hη
    obtain ⟨r, v, hr0, hr1, hv, ha, hb, hc⟩ := H (η / 20) (by positivity)
    have hVfin : volume (ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
    set V : ℝ≥0∞ := volume (ball (0 : Rn n) 1) with hV
    have hVnn : 0 ≤ V.toReal := ENNReal.toReal_nonneg
    set θ : ℝ := Real.sqrt (η / (6 * (V.toReal + 1))) with hθdef
    have hθpos : 0 < θ := Real.sqrt_pos.mpr (by positivity)
    have hθsq : θ ^ 2 = η / (6 * (V.toReal + 1)) := Real.sq_sqrt (by positivity)
    set e : ℝ≥0∞ := ENNReal.ofReal (η / 20) with he
    obtain ⟨N, hN⟩ := hc θ hθpos
    refine ⟨N, fun k l hk hl => ?_⟩
    have hsq : ∀ s : ℝ, ‖s‖ₑ ^ 2 = ENNReal.ofReal (s ^ 2) := by
      intro s
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg s), sq_abs]
    have hpt2 : ∀ s t : ℝ, ‖s - t‖ₑ ^ 2 ≤ 2 * ‖s‖ₑ ^ 2 + 2 * ‖t‖ₑ ^ 2 := by
      intro s t
      rw [hsq, hsq, hsq]
      have key : (s - t) ^ 2 ≤ 2 * s ^ 2 + 2 * t ^ 2 := by linarith [sq_nonneg (s + t)]
      calc ENNReal.ofReal ((s - t) ^ 2) ≤ ENNReal.ofReal (2 * s ^ 2 + 2 * t ^ 2) :=
            ENNReal.ofReal_le_ofReal key
        _ = 2 * ENNReal.ofReal (s ^ 2) + 2 * ENNReal.ofReal (t ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp
    have hpt3 : ∀ a b c d : ℝ, |c - d| ≤ θ →
        ‖a - b‖ₑ ^ 2 ≤ 3 * ‖a - c‖ₑ ^ 2 + 3 * ‖b - d‖ₑ ^ 2 + ENNReal.ofReal (3 * θ ^ 2) := by
      intro a b c d hcd
      rw [hsq, hsq, hsq]
      have hY : (c - d) ^ 2 ≤ θ ^ 2 := sq_le_sq' (abs_le.mp hcd).1 (abs_le.mp hcd).2
      have key : (a - b) ^ 2 ≤ 3 * (a - c) ^ 2 + 3 * (b - d) ^ 2 + 3 * θ ^ 2 := by
        linarith [sq_nonneg ((a - c) - (c - d)), sq_nonneg ((c - d) - (d - b)),
          sq_nonneg ((a - c) - (d - b))]
      calc ENNReal.ofReal ((a - b) ^ 2)
          ≤ ENNReal.ofReal (3 * (a - c) ^ 2 + 3 * (b - d) ^ 2 + 3 * θ ^ 2) :=
            ENNReal.ofReal_le_ofReal key
        _ = 3 * ENNReal.ofReal ((a - c) ^ 2) + 3 * ENNReal.ofReal ((b - d) ^ 2)
              + ENNReal.ofReal (3 * θ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3) (q := (a - c) ^ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3) (q := (b - d) ^ 2)]
            simp
    have hBr : ball (0 : Rn n) r ⊆ ball (0 : Rn n) 1 := ball_subset_ball hr1.le
    -- splitting `B = B_r ∪ (B \ B_r)`
    have hsplit : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2 ≤
        (∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2) +
          ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2 := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2
          = ∫⁻ x in ball (0 : Rn n) r ∪ (ball (0 : Rn n) 1 \ ball 0 r),
              ‖u k x - u l x‖ₑ ^ 2 := by
            rw [Set.union_sdiff_cancel hBr]
        _ ≤ _ := lintegral_union_le _ _ _
    -- the annulus
    have hbd : ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2 ≤ 2 * e + 2 * e := by
      have hmk : AEMeasurable (fun x => 2 * ‖u k x‖ₑ ^ 2)
          (volume.restrict (ball (0 : Rn n) 1 \ ball 0 r)) :=
        ((((hu k).mono_set sdiff_subset).enorm).pow_const 2).const_mul 2
      calc ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2
          ≤ ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, (2 * ‖u k x‖ₑ ^ 2 + 2 * ‖u l x‖ₑ ^ 2) :=
            lintegral_mono fun x => hpt2 _ _
        _ = 2 * (∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x‖ₑ ^ 2) +
              2 * ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u l x‖ₑ ^ 2 := by
            rw [lintegral_add_left' hmk, lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * e + 2 * e := by
            gcongr
            · exact ha k
            · exact ha l
    -- the interior
    have hint : ∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2 ≤
        3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V := by
      have hmk : AEMeasurable (fun x => 3 * ‖u k x - v k x‖ₑ ^ 2)
          (volume.restrict (ball (0 : Rn n) r)) :=
        (((((hu k).mono_set hBr).sub (hv k)).enorm).pow_const 2).const_mul 3
      calc ∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2
          ≤ ∫⁻ x in ball (0 : Rn n) r,
              (3 * ‖u k x - v k x‖ₑ ^ 2 + 3 * ‖u l x - v l x‖ₑ ^ 2
                + ENNReal.ofReal (3 * θ ^ 2)) :=
            setLIntegral_mono' measurableSet_ball fun x hx => hpt3 _ _ _ _ (hN k l hk hl x hx)
        _ = 3 * (∫⁻ x in ball (0 : Rn n) r, ‖u k x - v k x‖ₑ ^ 2) +
              3 * (∫⁻ x in ball (0 : Rn n) r, ‖u l x - v l x‖ₑ ^ 2) +
              ENNReal.ofReal (3 * θ ^ 2) * volume (ball (0 : Rn n) r) := by
            rw [lintegral_add_right' _ aemeasurable_const, lintegral_add_left' hmk,
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
              setLIntegral_const]
        _ ≤ 3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V := by
            gcongr
            · exact hb k
            · exact hb l
            · exact measure_mono hBr
    have hθV : ENNReal.ofReal (3 * θ ^ 2) * V ≤ 10 * e := by
      rw [← ENNReal.ofReal_toReal hVfin, ← ENNReal.ofReal_mul (by positivity), he,
        show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [hθsq]
      have hq : 0 ≤ η / (6 * (V.toReal + 1)) := by positivity
      have hq1 : η / (6 * (V.toReal + 1)) * (V.toReal + 1) = η / 6 := by
        rw [← div_div, div_mul_cancel₀ _ (by positivity)]
      linarith
    have he20 : ENNReal.ofReal η = 20 * e := by
      rw [he, show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    calc ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2
        ≤ _ := hsplit
      _ ≤ (3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V) + (2 * e + 2 * e) :=
          add_le_add hint hbd
      _ ≤ (3 * e + 3 * e + 10 * e) + (2 * e + 2 * e) := by gcongr
      _ = 20 * e := by ring
      _ = ENNReal.ofReal η := he20.symm
  -- Step 6 (completeness): a sequence that is Cauchy in `L²(μ)` has a limit in `L²(μ)`.
  have hcomplete : ∀ (μ : Measure (Rn n)) (u : ℕ → Rn n → ℝ), (∀ k, MemLp (u k) 2 μ) →
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∫⁻ x, ‖u k x - u l x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal η) →
      ∃ w : Rn n → ℝ, MemLp w 2 μ ∧ Tendsto (fun k => ∫⁻ x, ‖u k x - w x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
    clear hmol hmolerr hAA hdiag hcrit
    intro μ u hu hC
    -- the norm identity `‖v‖₂ ^ 2 = ∫⁻ ‖v‖ₑ ^ 2` (for a.e.-strongly measurable `v`)
    have key : ∀ v : Rn n → ℝ, AEStronglyMeasurable v μ →
        ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ = eLpNorm v 2 μ ^ 2 := by
      intro v hv
      have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (μ := μ) two_ne_zero hv
      simpa using h.symm
    have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    -- the classes `G k` of `u k` in `L²(μ)` form a Cauchy sequence
    let G : ℕ → Lp ℝ 2 μ := fun k => (hu k).toLp (u k)
    have hG : CauchySeq G := by
      rw [EMetric.cauchySeq_iff]
      intro ε hε
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      have hr : 0 < r := ENNReal.ofReal_pos.1 hr1
      obtain ⟨N, hN⟩ := hC (r ^ 2) (by positivity)
      refine ⟨N, fun k hk l hl => ?_⟩
      calc edist (G k) (G l) = eLpNorm (u k - u l) 2 μ := Lp.edist_toLp_toLp _ _ _ _
        _ ≤ ENNReal.ofReal r := by
          rw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
            ← key _ ((hu k).aestronglyMeasurable.sub (hu l).aestronglyMeasurable),
            ← ENNReal.ofReal_pow hr0]
          exact hN k l hk hl
        _ < ε := hr2
    -- completeness of `L²(μ)` (Riesz–Fischer)
    obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete hG
    refine ⟨W, Lp.memLp W, ?_⟩
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hW
    have h2 : ∀ k, eLpNorm (⇑(G k) - ⇑W) 2 μ = eLpNorm (u k - ⇑W) 2 μ := fun k =>
      eLpNorm_congr_ae ((hu k).coeFn_toLp.sub EventuallyEq.rfl)
    have h3 : ∀ k, ∫⁻ x, ‖u k x - W x‖ₑ ^ 2 ∂μ = eLpNorm (u k - ⇑W) 2 μ ^ 2 := fun k =>
      key _ ((hu k).aestronglyMeasurable.sub (Lp.memLp W).aestronglyMeasurable)
    have h4 := ENNReal.Tendsto.pow (n := 2) hW
    simp only [h2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h4
    simpa only [h3] using h4
  -- Assembly.
  intro A f g hW hf hg
  -- Step 0: measurable representatives `F k` of `f k` on the unit ball.
  let F : ℕ → Rn n → ℝ := fun k => (hW k).1.aestronglyMeasurable.mk (f k)
  have hFmeas : ∀ k, Measurable (F k) := fun k =>
    (hW k).1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFae : ∀ k, f k =ᵐ[volume.restrict (ball (0 : Rn n) 1)] F k := fun k =>
    (hW k).1.aestronglyMeasurable.ae_eq_mk
  have hWF : ∀ k, IsW12WithGradient (F k) (g k) (ball 0 1) := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hW k
    refine ⟨h1.ae_eq (hFae k), h2, ?_⟩
    intro ζ hζ hζc hζB
    rw [← h3 ζ hζ hζc hζB]
    refine integral_congr_ae ?_
    filter_upwards [hFae k] with x hx
    rw [hx]
  have hFbd : ∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ^ 2 ≤ ENNReal.ofReal A := by
    intro k
    calc ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ^ 2 = ∫⁻ x in ball (0 : Rn n) 1, ‖f k x‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [hFae k] with x hx
          rw [hx]
      _ ≤ _ := hf k
  -- The sibling estimates R1 (boundary layer) and R2 (translation).
  obtain ⟨C1, hC1, hR1⟩ := Submission.w12_ball_boundary_layer_estimate n hn
  have hR2 := Submission.w12_ball_translation_estimate n hn
  -- Mollifiers at the scales `ε_m = 1/(m+2)` and the mollified functions `H m k`.
  choose ρ C hρc hρnn hρsupp hρint hρbd using fun m : ℕ => hmol (1 / ((m : ℝ) + 2)) (by positivity)
  let H : ℕ → ℕ → Rn n → ℝ := fun m k x => ∫ y in ball (0 : Rn n) 1, ρ m (x - y) * F k y
  have hHbd : ∀ m k x x', |H m k x| ≤ C m * Real.sqrt A ∧
      |H m k x - H m k x'| ≤ C m * Real.sqrt A * ‖x - x'‖ := fun m k x x' =>
    hρbd m A (F k) (hWF k).1 (hFbd k) x x'
  have hHcont : ∀ m k, Continuous (H m k) := by
    intro m k
    refine (LipschitzWith.of_dist_le' (K := C m * Real.sqrt A) fun x x' => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    exact (hHbd m k x x').2
  -- Step 4: one subsequence `φ` along which every `H m` is uniformly Cauchy on `B₁(0)`
  -- (diagonal argument over the pairs `(m, i) = Nat.unpair j`, tolerance `1/(i+1)`).
  obtain ⟨φ, hφmono, hφ⟩ := hdiag
    (fun j p q => ∀ x ∈ closedBall (0 : Rn n) 1,
      |H (Nat.unpair j).1 p x - H (Nat.unpair j).1 q x| ≤ 1 / (((Nat.unpair j).2 : ℝ) + 1))
    (fun j ψ _ => hAA (closedBall 0 1) (H (Nat.unpair j).1) (C (Nat.unpair j).1 * Real.sqrt A)
      (C (Nat.unpair j).1 * Real.sqrt A) (isCompact_closedBall 0 1)
      (fun k x _ => (hHbd _ k x x).1)
      (fun k x _ y _ => by rw [dist_eq_norm]; exact (hHbd _ k x y).2)
      _ (by positivity) ψ)
  have hφ' : ∀ (m : ℕ) (θ : ℝ), 0 < θ → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      ∀ x ∈ closedBall (0 : Rn n) 1, |H m (φ k) x - H m (φ l) x| ≤ θ := by
    intro m θ hθ
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hθ
    obtain ⟨N, hN⟩ := hφ (Nat.pair m i)
    refine ⟨N, fun k l hk hl x hx => ?_⟩
    have h := hN k l hk hl x hx
    simp only [Nat.unpair_pair] at h
    exact h.trans hi.le
  -- Step 5: the Cauchy criterion, applied to `u k = F (φ k)`.
  have hcauchy := hcrit (fun k => F (φ k)) (fun k => (hFmeas (φ k)).aestronglyMeasurable) (by
    intro η hη
    obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = max A 0 := ⟨_, rfl⟩
    have hA'0 : 0 ≤ A' := by rw [hA']; exact le_max_right A 0
    have hAA' : ENNReal.ofReal A ≤ ENNReal.ofReal A' := by
      rw [hA']; exact ENNReal.ofReal_le_ofReal (le_max_left A 0)
    -- the radius `r = 1 - t`
    have hden : 0 < 2 * C1 * A' + 1 := by positivity
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (1 / 2) ((η / (2 * C1 * A' + 1)) ^ 2) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
    have htsq : Real.sqrt t ≤ η / (2 * C1 * A' + 1) := by
      rw [Real.sqrt_le_left (by positivity), ht]
      exact min_le_right _ _
    -- the scale `ε_m`
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min ht0 (by positivity : 0 < η / (A' + 1)))
    have hεm : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hεt : 1 / ((m : ℝ) + 2) < t := lt_of_le_of_lt hεm (lt_of_lt_of_le hm (min_le_left _ _))
    have hεη : 1 / ((m : ℝ) + 2) < η / (A' + 1) :=
      lt_of_le_of_lt hεm (lt_of_lt_of_le hm (min_le_right _ _))
    have hε0 : 0 < 1 / ((m : ℝ) + 2) := by positivity
    have hε1 : 1 / ((m : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hεA : (1 / ((m : ℝ) + 2)) ^ 2 * A' ≤ η := by
      have h1 : (1 / ((m : ℝ) + 2)) ^ 2 ≤ 1 / ((m : ℝ) + 2) := by
        rw [sq]; exact mul_le_of_le_one_left hε0.le hε1
      have h2 : 1 / ((m : ℝ) + 2) * A' ≤ η / (A' + 1) * A' :=
        mul_le_mul_of_nonneg_right hεη.le hA'0
      have h3 : η / (A' + 1) * A' ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (by linarith) hη.le
      calc (1 / ((m : ℝ) + 2)) ^ 2 * A' ≤ 1 / ((m : ℝ) + 2) * A' :=
            mul_le_mul_of_nonneg_right h1 hA'0
        _ ≤ η := h2.trans h3
    refine ⟨1 - t, fun k => H m (φ k), by linarith, by linarith,
      fun k => (hHcont m (φ k)).aestronglyMeasurable, ?_, ?_, ?_⟩
    · -- (a) the annulus, from R1
      intro k
      have h := hR1 (F (φ k)) (g (φ k)) (hWF (φ k)) (1 - t) (by linarith) (by linarith)
      rw [sub_sub_cancel] at h
      refine h.trans ?_
      calc ENNReal.ofReal (C1 * Real.sqrt t) * ((∫⁻ x in ball (0 : Rn n) 1, ‖F (φ k) x‖ₑ ^ 2) +
            ∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2)
          ≤ ENNReal.ofReal (C1 * Real.sqrt t) * (ENNReal.ofReal A' + ENNReal.ofReal A') := by
            gcongr
            · exact (hFbd (φ k)).trans hAA'
            · exact (hg (φ k)).trans hAA'
        _ = ENNReal.ofReal (C1 * Real.sqrt t * (A' + A')) := by
            rw [← ENNReal.ofReal_add hA'0 hA'0, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal η := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : C1 * Real.sqrt t * (A' + A') ≤
                C1 * (η / (2 * C1 * A' + 1)) * (A' + A') := by
              gcongr
            have h2 : C1 * (η / (2 * C1 * A' + 1)) * (A' + A') ≤ η := by
              rw [mul_comm C1, mul_assoc, div_mul_eq_mul_div, div_le_iff₀ hden]
              exact mul_le_mul_of_nonneg_left (by linarith) hη.le
            exact h1.trans h2
    · -- (b) the interior mollification error, from Step 2 and R2
      intro k
      have h := hmolerr (ρ m) (F (φ k)) (1 / ((m : ℝ) + 2)) (1 - t)
        (∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2) (hρc m) (hρnn m) (hρsupp m) (hρint m)
        (hFmeas (φ k)) (by linarith) (by linarith)
        (fun z hz => hR2 (F (φ k)) (g (φ k)) (hWF (φ k)) (1 - t) z (by linarith) hz)
      calc ∫⁻ x in ball (0 : Rn n) (1 - t), ‖F (φ k) x - H m (φ k) x‖ₑ ^ 2
          = ∫⁻ x in ball (0 : Rn n) (1 - t), ‖H m (φ k) x - F (φ k) x‖ₑ ^ 2 :=
            lintegral_congr fun x => by rw [enorm_sub_rev]
        _ ≤ ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2) *
              ∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2 := h
        _ ≤ ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2) * ENNReal.ofReal A' := by
            gcongr; exact (hg (φ k)).trans hAA'
        _ = ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2 * A') := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεA
    · -- (c) the uniform Cauchy property of the mollified subsequence, from Step 4
      intro θ hθ
      obtain ⟨N, hN⟩ := hφ' m θ hθ
      exact ⟨N, fun k l hk hl x hx => hN k l hk hl x
        (ball_subset_closedBall (ball_subset_ball (by linarith) hx))⟩)
  -- Step 6: completeness of `L²(B̆₁(0))`, and back from `F` to `f`.
  obtain ⟨w, hw, hlim⟩ := hcomplete (volume.restrict (ball (0 : Rn n) 1)) (fun k => F (φ k))
    (fun k => (hWF (φ k)).1) hcauchy
  refine ⟨φ, w, hφmono, hw, Tendsto.congr (fun k => ?_) hlim⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hFae (φ k)] with x hx
  rw [hx]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
