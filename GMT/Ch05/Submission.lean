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

/-- Linear graph area formula.  For a linear map `P : ℝⁿ → ℝ^ℓ` put
`g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}`.  Then `det g(P) > 0` and the graph map `v ↦ (v, P v)` scales
`Hⁿ` by `√(det g(P))`: `Hⁿ({(v, P v) : v ∈ S}) = √(det g(P)) Lⁿ(S)` for every `S ⊆ ℝⁿ`.
Write `v ↦ (v, P v)` as `ι ∘ M`, with `ι` a linear isometry of `ℝⁿ` onto its range (orthonormal
coordinates) and `M` linear on `ℝⁿ`.  Then `g(P) = Mᵀ M`, so `det g(P) = (det M)² > 0`, and
`Hⁿ(ι(M S)) = Lⁿ(M S) = |det M| Lⁿ(S)` (`Isometry.euclideanHausdorffMeasure_image`,
`Measure.addHaar_image_linearMap`). -/
theorem dohr_vel_linear_graph_area : ∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, 0 < Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) ∧ ∀ S : Set (Rn n), (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) = ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) * (volume : Measure (Rn n)) S := by
  intro n ℓ P
  have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
      inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
    intro v v' w w'
    simp [graphPoint, PiLp.inner_apply, Fin.sum_univ_add]
  let Λ : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (P v)
      map_add' := by
        intro v w
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c v
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  have hΛ : ∀ v, Λ v = graphPoint v (P v) := fun v => rfl
  have hΛinj : Function.Injective Λ := by
    intro v w h
    have h' := congrArg (fun z : Amb n ℓ => (WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j)) : Rn n)) h
    simpa [hΛ, graphPoint] using h'
  have hW : Module.finrank ℝ (LinearMap.range Λ) = n := by
    rw [LinearMap.finrank_range_of_inj hΛinj, finrank_euclideanSpace_fin]
  let e : (LinearMap.range Λ) ≃ₗᵢ[ℝ] Rn n :=
    ((stdOrthonormalBasis ℝ (LinearMap.range Λ)).reindex (finCongr hW)).repr
  let M : Rn n →ₗ[ℝ] Rn n := e.toLinearEquiv.toLinearMap ∘ₗ Λ.rangeRestrict
  let ι : Rn n → Amb n ℓ := fun z => ((e.symm z : LinearMap.range Λ) : Amb n ℓ)
  have hι : Isometry ι := ((LinearMap.range Λ).subtypeₗᵢ.comp e.symm.toLinearIsometry).isometry
  have hΛM : ∀ v, ι (M v) = Λ v := by
    intro v
    simp [ι, M]
  have himage : ∀ S : Set (Rn n), (fun v => graphPoint v (P v)) '' S = ι '' (M '' S) := by
    intro S
    rw [Set.image_image]
    refine Set.image_congr (fun v _ => ?_)
    rw [hΛM, hΛ]
  have hinnerM : ∀ v w, inner ℝ (M v) (M w) = inner ℝ (Λ v) (Λ w) := by
    intro v w
    rw [← hΛM, ← hΛM]
    show inner ℝ (M v) (M w) = inner ℝ ((e.symm (M v) : LinearMap.range Λ) : Amb n ℓ) ((e.symm (M w) : LinearMap.range Λ) : Amb n ℓ)
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  let bs := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let Mm : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix bs bs M
  have hMm : ∀ k a, Mm k a = (M (EuclideanSpace.single a (1 : ℝ))) k := by
    intro k a
    simp [Mm, bs, LinearMap.toMatrix_apply]
  have hgm : ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
      inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) = Mm.transpose * Mm := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hMm]
    have h1 : ∑ k, (M (EuclideanSpace.single a (1 : ℝ))) k * (M (EuclideanSpace.single b (1 : ℝ))) k =
        inner ℝ (M (EuclideanSpace.single a (1 : ℝ))) (M (EuclideanSpace.single b (1 : ℝ))) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [h1, hinnerM, hΛ, hΛ, hinner, EuclideanSpace.inner_single_left, PiLp.single_apply]
    simp [Matrix.one_apply]
  have hdet : Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
      inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) = (LinearMap.det M) ^ 2 := by
    rw [hgm, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
    ring
  have hMinj : Function.Injective M := by
    intro v w h
    apply hΛinj
    rw [← hΛM, ← hΛM, h]
  have hdetM : LinearMap.det M ≠ 0 := by
    have hsurj : Function.Surjective M := LinearMap.injective_iff_surjective.mp hMinj
    let Me : Rn n ≃ₗ[ℝ] Rn n := LinearEquiv.ofBijective M ⟨hMinj, hsurj⟩
    have : LinearMap.det M = LinearMap.det (Me : Rn n →ₗ[ℝ] Rn n) := rfl
    rw [this]
    exact (LinearEquiv.isUnit_det' Me).ne_zero
  refine ⟨by rw [hdet]; positivity, fun S => ?_⟩
  rw [himage, hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_image_linearMap, hdet, Real.sqrt_sq_eq_abs]
theorem dohr_vel_graph_fderiv : ∀ n ℓ : ℕ, ∀ (u : Rn n → Rn ℓ) (x : Rn n), DifferentiableAt ℝ u x → DifferentiableAt ℝ (fun z : Rn n => graphPoint z (u z)) x ∧ ∀ v : Rn n, fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x v = graphPoint v (fderiv ℝ u x v) := by
  intro n ℓ u x hu
theorem dohr_vel_vertical_test_field : ∀ n ℓ : ℕ, ∀ (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (s r : ℝ) (u φ : Rn n → Rn ℓ), 0 < s → ContinuousOn u (ball 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖graphPoint x (u x)‖ < s) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∃ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ ball ξ s ∧ (∀ x : Rn n, X (ξ + Q.symm (graphPoint x (u x))) = Q.symm (graphPoint 0 (φ x))) ∧ ∀ (x v : Rn n) (w : Rn ℓ), fderiv ℝ X (ξ + Q.symm (graphPoint x (u x))) (Q.symm (graphPoint v w)) = Q.symm (graphPoint 0 (fderiv ℝ φ x v)) := by
  intro n ℓ ξ Q s r u φ hs hu hGs hφ hφc hφr
  -- the pairing map (v, w) ↦ graphPoint v w and the projection onto the first n coordinates
  let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  let Γ : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ := LinearMap.toContinuousLinearMap Γl
  have h1 : HasFDerivAt (fun z : Rn n => (z, u z))
      ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x)) x :=
    (hasFDerivAt_id x).prodMk hu.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Rn n => graphPoint z (u z))
      (Γ.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x))) x :=
    Γ.hasFDerivAt.comp x h1
  refine ⟨h2.differentiableAt, fun v => ?_⟩
  rw [h2.fderiv]
  rfl
theorem dohr_vel_holder_rigid_transport : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ) (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), IsLocallyHolderCkα q α h U → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U) := by
  intro n ℓ U hU h q α ξ Q hh
  obtain ⟨hhC, hhH⟩ := hh
  -- T and its inverse A
  have hTA : ∀ z, Q (ξ + Q.symm z - ξ) = z := fun z => by
    rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
  have hAT : ∀ y, ξ + Q.symm (Q (y - ξ)) = y := fun y => by
    rw [LinearIsometryEquiv.symm_apply_apply]
    abel
  have hO : (fun y => Q (y - ξ)) '' U = (fun z => ξ + Q.symm z) ⁻¹' U :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun y => Q (y - ξ)) (g := fun z => ξ + Q.symm z)
      (fun y => hAT y) (fun z => hTA z)) U
  have hAcont : Continuous (fun z : Amb n ℓ => ξ + Q.symm z) := continuous_const.add Q.symm.continuous
  refine ⟨?_, ?_, ?_⟩
  · rw [hO]
    exact hU.preimage hAcont
  · -- C^q on O
    rw [hO]
    have hA : ContDiff ℝ q (fun z : Amb n ℓ => ξ + Q.symm z) := contDiff_const.add Q.symm.contDiff
    have h1 : ContDiffOn ℝ q (h ∘ fun z : Amb n ℓ => ξ + Q.symm z) ((fun z => ξ + Q.symm z) ⁻¹' U) :=
      hhC.comp hA.contDiffOn (fun z hz => hz)
    exact Q.contDiff.comp_contDiffOn h1
  · -- Hölder bound on compact subsets
    intro K hK hKO
    -- formula for the iterated derivative at every point
    have hformula : ∀ z, iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) z =
        (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ q h (ξ + Q.symm z)).compContinuousLinearMap
            (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) := by
      intro z
      have e1 : (fun z => Q (h (ξ + Q.symm z))) =
          (Q.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) ∘ (fun z => h (ξ + Q.symm z)) := rfl
      rw [e1, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
      congr 1
      have e2 : (fun z => h (ξ + Q.symm z)) =
          (fun w => h (ξ + w)) ∘ (Q.symm.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) := rfl
      have h3 := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
        (Q.symm.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) (fun w => h (ξ + w))
        (s := Set.univ) uniqueDiffOn_univ (x := z) (Set.mem_univ _) q
      rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h3
      rw [e2, h3, iteratedFDeriv_comp_add_left]
      rfl
    have hnorm : ∀ z w, ‖iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) z -
        iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) w‖ =
        ‖iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)‖ := by
      intro z w
      have hsub : (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm z)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) -
          (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) =
          (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) := by
        ext v
        simp only [LinearIsometryEquiv.toContinuousLinearEquiv_symm, sub_apply,
          ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, PiLp.sub_apply, map_sub]
      rw [hformula, hformula, hsub]
      have hQ := LinearIsometry.norm_compContinuousMultilinearMap Q.toLinearIsometry
        ((iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
          (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ)))
      have hQs := ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv
        (iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)) (fun _ : Fin q => Q.symm)
      exact hQ.trans hQs
    -- the compact image A(K) ⊆ U
    have hAK : IsCompact ((fun z => ξ + Q.symm z) '' K) := hK.image hAcont
    have hAKU : (fun z => ξ + Q.symm z) '' K ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      have := hKO hz
      rw [hO] at this
      exact this
    obtain ⟨C, hC⟩ := hhH _ hAK hAKU
    refine ⟨C, fun z hz w hw => ?_⟩
    rw [hnorm]
    have := hC _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    have hdist : ‖ξ + Q.symm z - (ξ + Q.symm w)‖ = ‖z - w‖ := by
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    rwa [hdist] at this

/-- Derivative of the graph area integrand (Jacobi's formula).  For a linear map `P : ℝⁿ → ℝ^ℓ`
put `g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}` and `J(P) = √(det g(P))`.  Then `J` is differentiable at
`P` and `DJ(P)[Ψ] = J(P) Σ_{a,c} (g(P)⁻¹)_{ac} ⟨P e_c, Ψ eₐ⟩`.
The entries of `g` have derivative `E(Ψ)_{ab} = ⟨P eₐ, Ψ e_b⟩ + ⟨Ψ eₐ, P e_b⟩`, `det` is a
polynomial in the entries (Leibniz formula), and `D det(g)[E] = det g · tr(g⁻¹ E)` because
`det(g + s E) = det g · det(1 + s g⁻¹ E)` (`Matrix.det_one_add_smul`).  Since `det g > 0`
(`dohr_vel_linear_graph_area`) and `g⁻¹` is symmetric, `tr(g⁻¹ E(Ψ)) = 2 Σ_{a,c} (g⁻¹)_{ac} ⟨P e_c, Ψ eₐ⟩`,
and the chain rule for `√` at `det g > 0` gives the formula. -/
theorem dohr_vel_area_integrand_fderiv : ∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, DifferentiableAt ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P ∧ ∀ Ψ : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P Ψ = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))) * ∑ a : Fin n, ∑ c : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))⁻¹ a c * inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
  intro n ℓ P
  -- the Gram-type matrix as a map into the normed space of arrays, and det on arrays
  let Gm : (Rn n →L[ℝ] Rn ℓ) → (Fin n → Fin n → ℝ) := fun P' a b =>
    (1 : Matrix (Fin n) (Fin n) ℝ) a b +
      inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))
  let detPi : (Fin n → Fin n → ℝ) → ℝ := fun M => Matrix.det (Matrix.of M)
  have hJ : (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ)))
        (P' (EuclideanSpace.single b (1 : ℝ)))))) = fun P' => Real.sqrt (detPi (Gm P')) := rfl
  set g : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
    inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) with hg
  have hgG : Matrix.of (Gm P) = g := rfl
  -- g is positive definite, symmetric, invertible
  have hdetpos : 0 < g.det := (dohr_vel_linear_graph_area n ℓ P).1
  have hunit : IsUnit g.det := isUnit_iff_ne_zero.mpr hdetpos.ne'
  have hgT : g.transpose = g := by
    ext a c
    simp only [hg, Matrix.transpose_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    rw [real_inner_comm]
    by_cases hac : a = c
    · subst hac; rfl
    · rw [ite_eq_right hac, ite_eq_right (Ne.symm hac)]
  have hsymm : ∀ a c, g⁻¹ a c = g⁻¹ c a := by
    intro a c
    have h1 : (g⁻¹).transpose = g⁻¹ := by rw [Matrix.transpose_nonsing_inv, hgT]
    have h2 := congrFun (congrFun h1 c) a
    simpa [Matrix.transpose_apply] using h2
  -- derivative of Gm
  let Gd : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Fin n → Fin n → ℝ) :=
    ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      (fderivInnerCLM ℝ (P (EuclideanSpace.single a (1 : ℝ)), P (EuclideanSpace.single b (1 : ℝ)))).comp
        ((ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).prod
          (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))))
  have hGd : ∀ Ψ a b, Gd Ψ a b = inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (Ψ (EuclideanSpace.single b (1 : ℝ))) +
      inner ℝ (Ψ (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) := by
    intro Ψ a b
    simp [Gd, fderivInnerCLM_apply]
  have hGm : HasFDerivAt Gm Gd P := by
    refine hasFDerivAt_pi.mpr (fun a => hasFDerivAt_pi.mpr (fun b => ?_))
    have ha := (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).hasFDerivAt (x := P)
    have hb := (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).hasFDerivAt (x := P)
    exact (ha.inner ℝ hb).const_add _
  -- det is differentiable on arrays (Leibniz formula)
  have hdetDiff : Differentiable ℝ detPi := by
    have hform : detPi = fun M => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i := by
      funext M
      simp only [detPi, Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
    rw [hform]
    refine Differentiable.fun_sum (fun σ _ => ?_)
    refine Differentiable.const_mul (fun M => ?_) _
    have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt (fun M : Fin n → Fin n → ℝ => M (σ i) i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) (σ i))) M := fun i _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) (σ i))).hasFDerivAt
    exact (HasFDerivAt.finsetProd (g := fun i (M : Fin n → Fin n → ℝ) => M (σ i) i) hcoord).differentiableAt
  -- Jacobi's formula for the directional derivative of det at an invertible matrix
  have hdir : ∀ (G E : Fin n → Fin n → ℝ), IsUnit (Matrix.of G).det →
      fderiv ℝ detPi G E = (Matrix.of G).det * Matrix.trace ((Matrix.of G)⁻¹ * Matrix.of E) := by
    intro G E hG
    have h1 : HasDerivAt (fun s : ℝ => G + s • E) E 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add G
    have h0 : (fun s : ℝ => G + s • E) 0 = G := by simp
    have hline : HasDerivAt (fun s : ℝ => detPi (G + s • E)) (fderiv ℝ detPi G E) 0 := by
      have h2 := ((hdetDiff G).hasFDerivAt).comp_hasDerivAt_of_eq 0 h1 h0.symm
      exact h2
    set A : Matrix (Fin n) (Fin n) ℝ := (Matrix.of G)⁻¹ * Matrix.of E with hA
    set p2 : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det.divX.divX with hp2
    have heq : (fun s : ℝ => detPi (G + s • E)) =
        fun s => (Matrix.of G).det * (1 + A.trace * s + p2.eval s * s ^ 2) := by
      funext s
      have hm : Matrix.of (G + s • E) = Matrix.of G * (1 + s • A) := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hA, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
        rfl
      show Matrix.det (Matrix.of (G + s • E)) = _
      rw [hm, Matrix.det_mul, Matrix.det_one_add_smul]
    have hpoly : HasDerivAt (fun s : ℝ => (Matrix.of G).det * (1 + A.trace * s + p2.eval s * s ^ 2))
        ((Matrix.of G).det * A.trace) 0 := by
      have h3 : HasDerivAt (fun s : ℝ => 1 + A.trace * s + p2.eval s * s ^ 2)
          (A.trace * 1 + (p2.derivative.eval 0 * 0 ^ 2 + p2.eval 0 * (↑2 * 0 ^ (2 - 1)))) 0 :=
        (((hasDerivAt_id (0 : ℝ)).const_mul A.trace).const_add 1).add
          ((p2.hasDerivAt 0).mul (hasDerivAt_pow 2 (0 : ℝ)))
      have h4 := h3.const_mul (Matrix.of G).det
      convert h4 using 1
      simp
    rw [heq] at hline
    exact hline.unique hpoly
  -- assemble
  have hΔ : HasFDerivAt (fun P' => detPi (Gm P')) ((fderiv ℝ detPi (Gm P)).comp Gd) P :=
    (hdetDiff (Gm P)).hasFDerivAt.comp P hGm
  have hΔpos : 0 < detPi (Gm P) := hdetpos
  have hJd := hΔ.sqrt hΔpos.ne'
  rw [hJ]
  refine ⟨hJd.differentiableAt, fun Ψ => ?_⟩
  rw [hJd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hdir (Gm P) (Gd Ψ) (by rw [hgG]; exact hunit), hgG]
  have htr : Matrix.trace (g⁻¹ * Matrix.of (Gd Ψ)) =
      2 * ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
        inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hGd, mul_add,
      Finset.sum_add_distrib]
    have h2 : ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
          inner ℝ (Ψ (EuclideanSpace.single c (1 : ℝ))) (P (EuclideanSpace.single a (1 : ℝ))) =
        ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
          inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
      rw [hsymm c a, real_inner_comm]
    rw [h2]
    ring
  have hsq : Real.sqrt (detPi (Gm P)) ^ 2 = detPi (Gm P) := Real.sq_sqrt hΔpos.le
  have hsqpos : 0 < Real.sqrt (detPi (Gm P)) := Real.sqrt_pos.mpr hΔpos
  have hdg : detPi (Gm P) = g.det := rfl
  rw [htr, ← hdg]
  field_simp
  rw [hsq]

/-- Trace of a vertical map composed with the projection onto a rotated graph plane.
Put `b_a = L e_a = (e_a, P e_a)`, so `⟨b_a, b_c⟩ = g_{ac}` with `g = I + (⟨P e_a, P e_b⟩)_{a,b}`;
`g` is symmetric and invertible (`det g > 0` by `dohr_vel_linear_graph_area`).  The projection onto
`τ = range L` is `z ↦ Σ_{a,c} g^{ac} ⟨b_c, z⟩ b_a`
(`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`), and the projection onto `Q⁻¹ τ` is
`Q⁻¹ ∘ p_τ ∘ Q` (`Submodule.starProjection_map_apply`).  Hence `D ∘ p` is the rank-one sum
`z ↦ Σ_{a,c} g^{ac} ⟨Q⁻¹ b_c, z⟩ Q⁻¹(0, Ψ e_a)`, whose trace is `Σ_{a,c} g^{ac} ⟨P e_c, Ψ e_a⟩`
(`LinearMap.trace_smulRight`). -/
theorem dohr_vel_graph_projection_trace : ∀ n ℓ : ℕ, ∀ (P Ψ : Rn n →L[ℝ] Rn ℓ) (L : Rn n →L[ℝ] Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Amb n ℓ →L[ℝ] Amb n ℓ), (∀ v : Rn n, L v = graphPoint v (P v)) → (∀ (v : Rn n) (w : Rn ℓ), D (Q.symm (graphPoint v w)) = Q.symm (graphPoint 0 (Ψ v))) → LinearMap.trace ℝ (Amb n ℓ) (D.toLinearMap ∘ₗ (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range L.toLinearMap)).starProjection.toLinearMap) = ∑ a : Fin n, ∑ c : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))⁻¹ a c * inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
  intro n ℓ P Ψ L Q D hL hD
  have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
      inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
    intro v v' w w'
    simp only [graphPoint, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right]
  set g : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
    inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) with hg
  let bv : Fin n → Amb n ℓ := fun a => L (EuclideanSpace.single a (1 : ℝ))
  have hdet : g.det ≠ 0 := (dohr_vel_linear_graph_area n ℓ P).1.ne'
  have hunit : IsUnit g.det := isUnit_iff_ne_zero.mpr hdet
  have hinvg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hunit
  have hgT : g.transpose = g := by
    ext a c
    simp only [hg, Matrix.transpose_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    rw [real_inner_comm]
    by_cases hac : a = c
    · subst hac; rfl
    · rw [ite_eq_right hac, ite_eq_right (Ne.symm hac)]
  have hsymm : ∀ a c, g⁻¹ a c = g⁻¹ c a := by
    intro a c
    have h1 : (g⁻¹).transpose = g⁻¹ := by rw [Matrix.transpose_nonsing_inv, hgT]
    have h2 := congrFun (congrFun h1 c) a
    simpa [Matrix.transpose_apply] using h2
  -- the orthogonal projection onto the graph plane τ = range L
  have hproj : ∀ z, (LinearMap.range L.toLinearMap).starProjection z =
      ∑ a, ∑ c, (g⁻¹ a c * inner ℝ (bv c) z) • bv a := by
    intro z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ ?_))
      exact ⟨EuclideanSpace.single a (1 : ℝ), rfl⟩
    · have hd : ∀ d, inner ℝ (z - ∑ a, ∑ c, (g⁻¹ a c * inner ℝ (bv c) z) • bv a) (bv d) = 0 := by
        intro d
        have hgd : ∀ a, inner ℝ (bv a) (bv d) = g a d := fun a => by
          simp only [bv, hL, hinner, hg, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply,
            EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]
        rw [inner_sub_left, sum_inner]
        simp_rw [sum_inner, real_inner_smul_left, hgd]
        have hswap : ∑ a, ∑ c, g⁻¹ a c * inner ℝ (bv c) z * g a d =
            ∑ c, inner ℝ (bv c) z * ∑ a, g⁻¹ c a * g a d := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hsymm a c]
          ring
        rw [hswap]
        simp_rw [← Matrix.mul_apply, hinvg, Matrix.one_apply]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [real_inner_comm]
        exact sub_self _
      intro w hw
      obtain ⟨v, rfl⟩ := hw
      have hv : v = ∑ a, (v a) • EuclideanSpace.single a (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
        simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      have hLv : L.toLinearMap v = ∑ a, (v a) • bv a := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul, ContinuousLinearMap.coe_coe, bv]
      rw [hLv, inner_sum]
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [real_inner_smul_right, hd a, mul_zero]
  -- rotate the plane
  have hp : ∀ z, (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range L.toLinearMap)).starProjection z =
      Q.symm ((LinearMap.range L.toLinearMap).starProjection (Q z)) := by
    intro z
    have := Submodule.starProjection_map_apply Q.symm (LinearMap.range L.toLinearMap) z
    rw [LinearIsometryEquiv.symm_symm] at this
    exact this
  have hDb : ∀ a, D (Q.symm (bv a)) = Q.symm (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ)))) := by
    intro a
    simp only [bv, hL]
    exact hD _ _
  have hDp : D.toLinearMap ∘ₗ (Submodule.map Q.symm.toLinearEquiv.toLinearMap
        (LinearMap.range L.toLinearMap)).starProjection.toLinearMap =
      ∑ a, ∑ c, g⁻¹ a c • (innerₛₗ ℝ (Q.symm (bv c))).smulRight
        (Q.symm (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ))))) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hp, hproj, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, hDb]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, smul_smul]
  rw [hDp]
  simp only [map_sum, map_smul, LinearMap.trace_smulRight, innerₛₗ_apply_apply, LinearIsometryEquiv.inner_map_map,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
  show g⁻¹ a c * inner ℝ (L (EuclideanSpace.single c (1 : ℝ))) (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ)))) = _
  rw [hL, hinner, inner_zero_right, zero_add]

/-- Area formula for the graph of a `C¹` map.  Let `u` be `C¹` on the open set `D ⊆ ℝⁿ` and
`G(x) = (x, u x)`.  For measurable `A ⊆ D`, `Hⁿ(G(A)) = ∫_A √(det g(Du(x))) dx`, where
`g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}`.  Near `x₀ ∈ D`, `u` is `ε`-close to `P = Du(x₀)`
(`ApproximatesLinearOn`), so `G` and `v ↦ (v, P v)` are `(1+ε)`-Lipschitz equivalent on a small
ball (`LipschitzOnWith.hausdorffMeasure_image_le`) and `√(det g(Du))` stays within a factor `1+ε`
of `√(det g(P))`.  By `dohr_vel_linear_graph_area` both sides agree up to `(1+ε)^(n+1)` on each
piece of a countable disjoint ball cover of `A`; let `ε → 0`. -/
theorem dohr_vel_graph_area_formula : ∀ n ℓ : ℕ, ∀ (D : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen D → ContDiffOn ℝ 1 u D → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ D → (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ)))))) := by
  intro n ℓ D u hD hu A hA hAD
  have linArea := dohr_vel_linear_graph_area n ℓ
  have lipCompare : ∀ (u : Rn n → Rn ℓ) (P : Rn n →L[ℝ] Rn ℓ) (c : ℝ≥0) (S : Set (Rn n)),
    ApproximatesLinearOn u P S c →
    (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) ≤
        (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) ∧
      (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) ≤
        (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
    intro u P c S hS
    have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
        inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
      intro v v' w w'
      simp [graphPoint, PiLp.inner_apply, Fin.sum_univ_add]
    have hsub : ∀ (v v' : Rn n) (w w' : Rn ℓ), graphPoint v w - graphPoint v' w' = graphPoint (v - v') (w - w') := by
      intro v v' w w'
      ext i
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
    have hadd : ∀ (v v' : Rn n) (w w' : Rn ℓ), graphPoint v w + graphPoint v' w' = graphPoint (v + v') (w + w') := by
      intro v v' w w'
      ext i
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
    have hnorm_ge : ∀ (v : Rn n) (w : Rn ℓ), ‖v‖ ≤ ‖graphPoint v w‖ := by
      intro v w
      have h1 : ‖graphPoint v w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hinner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      nlinarith [norm_nonneg v, norm_nonneg w, norm_nonneg (graphPoint v w), sq_nonneg ‖w‖]
    have hnorm0 : ∀ w : Rn ℓ, ‖graphPoint (0 : Rn n) w‖ = ‖w‖ := by
      intro w
      have h1 : ‖graphPoint (0 : Rn n) w‖ ^ 2 = ‖w‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hinner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        simp
      rw [← Real.sqrt_sq (norm_nonneg (graphPoint (0 : Rn n) w)), h1, Real.sqrt_sq (norm_nonneg w)]
    let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
    have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
      intro x w
      simp [π, graphPoint]
    -- the key two-sided estimate on S
    have hkey : ∀ x ∈ S, ∀ x' ∈ S,
        ‖graphPoint x (u x) - graphPoint x' (u x')‖ ≤ (1 + (c : ℝ)) * ‖graphPoint x (P x) - graphPoint x' (P x')‖ ∧
        ‖graphPoint x (P x) - graphPoint x' (P x')‖ ≤ (1 + (c : ℝ)) * ‖graphPoint x (u x) - graphPoint x' (u x')‖ := by
      intro x hx x' hx'
      have happ : ‖u x - u x' - P (x - x')‖ ≤ (c : ℝ) * ‖x - x'‖ := hS x hx x' hx'
      have hdec : graphPoint (x - x') (u x - u x') =
          graphPoint (x - x') (P (x - x')) + graphPoint 0 (u x - u x' - P (x - x')) := by
        rw [hadd]
        congr 1 <;> abel
      have hP : graphPoint x (P x) - graphPoint x' (P x') = graphPoint (x - x') (P (x - x')) := by
        rw [hsub, map_sub]
      have hU : graphPoint x (u x) - graphPoint x' (u x') = graphPoint (x - x') (u x - u x') := by
        rw [hsub]
      have hc : (0 : ℝ) ≤ c := c.2
      have h1 := hnorm_ge (x - x') (P (x - x'))
      have h2 := hnorm_ge (x - x') (u x - u x')
      constructor
      · rw [hU, hP, hdec]
        calc ‖graphPoint (x - x') (P (x - x')) + graphPoint 0 (u x - u x' - P (x - x'))‖
            ≤ ‖graphPoint (x - x') (P (x - x'))‖ + ‖graphPoint (0 : Rn n) (u x - u x' - P (x - x'))‖ :=
              norm_add_le _ _
          _ ≤ ‖graphPoint (x - x') (P (x - x'))‖ + (c : ℝ) * ‖graphPoint (x - x') (P (x - x'))‖ := by
              rw [hnorm0]
              have := mul_le_mul_of_nonneg_left h1 hc
              linarith
          _ = (1 + (c : ℝ)) * ‖graphPoint (x - x') (P (x - x'))‖ := by ring
      · rw [hU, hP]
        have hdec' : graphPoint (x - x') (P (x - x')) =
            graphPoint (x - x') (u x - u x') - graphPoint 0 (u x - u x' - P (x - x')) := by
          rw [hdec]
          abel
        rw [hdec']
        calc ‖graphPoint (x - x') (u x - u x') - graphPoint 0 (u x - u x' - P (x - x'))‖
            ≤ ‖graphPoint (x - x') (u x - u x')‖ + ‖graphPoint (0 : Rn n) (u x - u x' - P (x - x'))‖ :=
              norm_sub_le _ _
          _ ≤ ‖graphPoint (x - x') (u x - u x')‖ + (c : ℝ) * ‖graphPoint (x - x') (u x - u x')‖ := by
              rw [hnorm0]
              have := mul_le_mul_of_nonneg_left h2 hc
              linarith
          _ = (1 + (c : ℝ)) * ‖graphPoint (x - x') (u x - u x')‖ := by ring
    -- Lipschitz maps between the two images
    have hψ : LipschitzOnWith (1 + c) (fun z => graphPoint (π z) (u (π z))) ((fun v => graphPoint v (P v)) '' S) := by
      refine LipschitzOnWith.of_dist_le_mul (fun y hy y' hy' => ?_)
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      simp only [hπG, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
      exact (hkey x hx x' hx').1
    have hφ : LipschitzOnWith (1 + c) (fun z => graphPoint (π z) (P (π z))) ((fun x => graphPoint x (u x)) '' S) := by
      refine LipschitzOnWith.of_dist_le_mul (fun y hy y' hy' => ?_)
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      simp only [hπG, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
      exact (hkey x hx x' hx').2
    have himg1 : (fun z => graphPoint (π z) (u (π z))) '' ((fun v => graphPoint v (P v)) '' S) =
        (fun x => graphPoint x (u x)) '' S := by
      rw [Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      simp only [hπG]
    have himg2 : (fun z => graphPoint (π z) (P (π z))) '' ((fun x => graphPoint x (u x)) '' S) =
        (fun v => graphPoint v (P v)) '' S := by
      rw [Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      simp only [hπG]
    have hscale : ∀ (f : Amb n ℓ → Amb n ℓ) (T : Set (Amb n ℓ)), LipschitzOnWith (1 + c) f T →
        (μHE[n] : Measure (Amb n ℓ)) (f '' T) ≤ (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) T := by
      intro f T hf
      have h := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
        ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
      rw [ENNReal.rpow_natCast] at h
      push_cast at h
      calc _ ≤ ((volume : Measure (Rn n)).addHaarScalarFactor μH[(n : ℝ)] : ℝ≥0∞) *
            ((1 + (c : ℝ≥0∞)) ^ n * μH[(n : ℝ)] T) := by gcongr
        _ = _ := by ring
    refine ⟨?_, ?_⟩
    · rw [← himg1]
      exact hscale _ _ hψ
    · rw [← himg2]
      exact hscale _ _ hφ
  set J : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
      (P (EuclideanSpace.single b (1 : ℝ))))) with hJdef
  have hJpos : ∀ P, 0 < J P := fun P => Real.sqrt_pos.mpr (linArea P).1
  have hJcont : Continuous J := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_matrix (fun a b => ?_)
    simp only [Matrix.add_apply, Matrix.of_apply]
    exact continuous_const.add (Continuous.inner
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).continuous
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).continuous)
  have hdiff : ∀ x ∈ D, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (hD.mem_nhds hx)
  have hfcont : ContinuousOn (fderiv ℝ u) D := hu.continuousOn_fderiv_of_isOpen hD le_rfl
  let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
    intro x w
    simp [π, graphPoint]
  have hGinj : Function.Injective (fun x : Rn n => graphPoint x (u x)) := by
    intro x y h
    have := congrArg π h
    simpa [hπG] using this
  have hGcont : ContinuousOn (fun x : Rn n => graphPoint x (u x)) D := by
    intro x hx
    let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
      { toFun := fun p => graphPoint p.1 p.2
        map_add' := by
          intro p q
          ext i
          refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
        map_smul' := by
          intro c p
          ext i
          refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
    have hΓ : Continuous (LinearMap.toContinuousLinearMap Γl) := (LinearMap.toContinuousLinearMap Γl).continuous
    exact (hΓ.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_id.prodMk ((hdiff x hx).continuousAt.continuousWithinAt)))
  -- local two-sided estimate
  have hloc : ∀ ε : ℝ, 0 < ε → ∀ x0 ∈ D, ∃ ρ > 0, ball x0 ρ ⊆ D ∧ ∀ S : Set (Rn n), MeasurableSet S →
      S ⊆ ball x0 ρ →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
    intro ε hε x0 hx0
    have hJP := hJpos (fderiv ℝ u x0)
    have hc2 : ContinuousAt (fderiv ℝ u) x0 := (hfcont x0 hx0).continuousAt (hD.mem_nhds hx0)
    have hc1 : ContinuousAt (fun x => J (fderiv ℝ u x)) x0 := hJcont.continuousAt.comp hc2
    obtain ⟨ρ1, hρ1, h1⟩ := Metric.continuousAt_iff.mp hc1 (ε / (1 + ε) * J (fderiv ℝ u x0)) (by positivity)
    obtain ⟨ρ2, hρ2, h2⟩ := Metric.continuousAt_iff.mp hc2 ε hε
    obtain ⟨ρ3, hρ3, h3⟩ := Metric.isOpen_iff.mp hD x0 hx0
    have hρ : 0 < min ρ1 (min ρ2 ρ3) := lt_min hρ1 (lt_min hρ2 hρ3)
    have hBD : ball x0 (min ρ1 (min ρ2 ρ3)) ⊆ D :=
      (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans h3
    refine ⟨min ρ1 (min ρ2 ρ3), hρ, hBD, fun S hS hSB => ?_⟩
    set c : ℝ≥0 := ⟨ε, hε.le⟩ with hc
    have hcR : (c : ℝ) = ε := rfl
    have hcE : (c : ℝ≥0∞) = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hε.le]
      rfl
    have happrox : ApproximatesLinearOn u (fderiv ℝ u x0) S c := by
      intro x hx y hy
      rw [hcR]
      have hconv : Convex ℝ (ball x0 (min ρ1 (min ρ2 ρ3))) := convex_ball _ _
      have hbound : ∀ z ∈ ball x0 (min ρ1 (min ρ2 ρ3)), ‖fderiv ℝ u z - fderiv ℝ u x0‖ ≤ ε := by
        intro z hz
        have hz' : dist z x0 < ρ2 := lt_of_lt_of_le (mem_ball.mp hz) ((min_le_right _ _).trans (min_le_left _ _))
        have := h2 hz'
        rw [dist_eq_norm] at this
        exact this.le
      have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun z hz => (hdiff z (hBD hz)).hasFDerivAt.hasFDerivWithinAt) hbound (hSB hy) (hSB hx)
      simpa using hmv
    have hJb : ∀ x ∈ S, J (fderiv ℝ u x0) ≤ (1 + ε) * J (fderiv ℝ u x) ∧
        J (fderiv ℝ u x) ≤ (1 + ε) * J (fderiv ℝ u x0) := by
      intro x hx
      have hx1 : dist x x0 < ρ1 := lt_of_lt_of_le (mem_ball.mp (hSB hx)) (min_le_left _ _)
      have hxd := h1 hx1
      rw [Real.dist_eq, abs_lt] at hxd
      have hJx := hJpos (fderiv ℝ u x)
      have key : ε / (1 + ε) * J (fderiv ℝ u x0) * (1 + ε) = ε * J (fderiv ℝ u x0) := by
        field_simp
      constructor
      · nlinarith
      · have : ε / (1 + ε) * J (fderiv ℝ u x0) ≤ ε * J (fderiv ℝ u x0) := by
          have h1e : (1 : ℝ) ≤ 1 + ε := by linarith
          have : ε / (1 + ε) ≤ ε := div_le_self hε.le h1e
          exact mul_le_mul_of_nonneg_right this hJP.le
        nlinarith
    obtain ⟨hLC1, hLC2⟩ := lipCompare u (fderiv ℝ u x0) c S happrox
    have hLA := (linArea (fderiv ℝ u x0)).2 S
    have hfac : (1 + (c : ℝ≥0∞)) ^ n = ENNReal.ofReal ((1 + ε) ^ n) := by
      rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_add zero_le_one hε.le, ENNReal.ofReal_one, hcE]
    have hfac2 : ENNReal.ofReal ((1 + ε) ^ (n + 1)) = ENNReal.ofReal ((1 + ε) ^ n) * ENNReal.ofReal (1 + ε) := by
      rw [pow_succ, ENNReal.ofReal_mul (by positivity)]
    have hconst : ∫⁻ _ in S, ENNReal.ofReal (J (fderiv ℝ u x0)) =
        ENNReal.ofReal (J (fderiv ℝ u x0)) * (volume : Measure (Rn n)) S := by
      rw [setLIntegral_const]
    constructor
    · calc (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S)
          ≤ ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal (J (fderiv ℝ u x0)) * (volume : Measure (Rn n)) S) := by
            rw [← hfac, ← hLA]; exact hLC1
        _ = ENNReal.ofReal ((1 + ε) ^ n) * ∫⁻ _ in S, ENNReal.ofReal (J (fderiv ℝ u x0)) := by rw [hconst]
        _ ≤ ENNReal.ofReal ((1 + ε) ^ n) * ∫⁻ x in S, ENNReal.ofReal (1 + ε) * ENNReal.ofReal (J (fderiv ℝ u x)) := by
            refine mul_le_mul' le_rfl (setLIntegral_mono' hS (fun x hx => ?_))
            rw [← ENNReal.ofReal_mul (by linarith)]
            exact ENNReal.ofReal_le_ofReal (hJb x hx).1
        _ = ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hfac2, mul_assoc]
    · calc ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x))
          ≤ ∫⁻ _ in S, ENNReal.ofReal (1 + ε) * ENNReal.ofReal (J (fderiv ℝ u x0)) := by
            refine setLIntegral_mono' hS (fun x hx => ?_)
            rw [← ENNReal.ofReal_mul (by linarith)]
            exact ENNReal.ofReal_le_ofReal (hJb x hx).2
        _ = ENNReal.ofReal (1 + ε) * (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (fderiv ℝ u x0 v)) '' S) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hconst, hLA]
        _ ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal ((1 + ε) ^ n) *
              (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S)) := by
            refine mul_le_mul' le_rfl ?_
            rw [← hfac]
            exact hLC2
        _ = ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
            rw [hfac2]
            ring
  -- global two-sided estimate on A
  have hglob : ∀ ε : ℝ, 0 < ε →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) := by
    intro ε hε
    choose! ρ hρpos hρD hρest using hloc ε hε
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : D => ball (x : Rn n) (ρ x)) (fun _ => isOpen_ball)
    have hDcov : D ⊆ ⋃ i ∈ T, ball ((i : D) : Rn n) (ρ i) := by
      intro x hx
      rw [hTU]
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρpos x hx)⟩
    rcases T.eq_empty_or_nonempty with hT | hT
    · have hA0 : A = ∅ := by
        apply Set.subset_eq_empty (hAD.trans hDcov)
        simp [hT]
      subst hA0
      simp
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hT
    let B : ℕ → Set (Rn n) := fun k => ball ((f k : D) : Rn n) (ρ (f k))
    have hAcov : A ⊆ ⋃ k, B k := by
      intro x hx
      have := hDcov (hAD hx)
      rw [hf] at this
      simp only [Set.mem_iUnion, Set.mem_range, exists_prop] at this
      obtain ⟨i, ⟨k, rfl⟩, hxi⟩ := this
      exact Set.mem_iUnion.mpr ⟨k, hxi⟩
    let C : ℕ → Set (Rn n) := fun k => A ∩ disjointed B k
    have hCmeas : ∀ k, MeasurableSet (C k) := fun k =>
      hA.inter (MeasurableSet.disjointed (fun j => measurableSet_ball) k)
    have hCdisj : Pairwise (Function.onFun Disjoint C) := by
      intro i j hij
      exact ((disjoint_disjointed B) hij).mono Set.inter_subset_right Set.inter_subset_right
    have hCunion : ⋃ k, C k = A := by
      simp only [C, ← Set.inter_iUnion, iUnion_disjointed]
      exact Set.inter_eq_left.mpr hAcov
    have hCB : ∀ k, C k ⊆ B k := fun k => Set.inter_subset_right.trans (disjointed_subset B k)
    have hGCmeas : ∀ k, MeasurableSet ((fun x => graphPoint x (u x)) '' C k) := fun k =>
      (hCmeas k).image_of_continuousOn_injOn (hGcont.mono ((Set.inter_subset_left).trans hAD))
        hGinj.injOn
    have hGCdisj : Pairwise (Function.onFun Disjoint (fun k => (fun x => graphPoint x (u x)) '' C k)) := by
      intro i j hij
      exact (Set.disjoint_image_iff hGinj).mpr (hCdisj hij)
    have hGA : (fun x => graphPoint x (u x)) '' A = ⋃ k, (fun x => graphPoint x (u x)) '' C k := by
      rw [← Set.image_iUnion, hCunion]
    have hmeasG : (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) =
        ∑' k, (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) := by
      rw [hGA, measure_iUnion hGCdisj hGCmeas]
    have hlintA : ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) =
        ∑' k, ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) := by
      conv_lhs => rw [← hCunion]
      exact lintegral_iUnion hCmeas hCdisj _
    have hk : ∀ k, (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) :=
      fun k => hρest (f k) (f k).2 (C k) (hCmeas k) (hCB k)
    constructor
    · rw [hmeasG, hlintA, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun k => (hk k).1)
    · rw [hmeasG, hlintA, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun k => (hk k).2)
  -- let ε → 0
  have hlim : ∀ X Y : ℝ≥0∞, (∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal ((1 + ε) ^ (n + 1)) * Y) → X ≤ Y := by
    intro X Y hXY
    by_cases hY : Y = ⊤
    · rw [hY]; exact le_top
    · have h0 : Tendsto (fun ε : ℝ => (1 + ε) ^ (n + 1)) (𝓝[>] 0) (𝓝 1) := by
        have hcont : Continuous (fun ε : ℝ => (1 + ε) ^ (n + 1)) := (continuous_const.add continuous_id).pow (n + 1)
        have h := hcont.tendsto (0 : ℝ)
        simp only [add_zero, one_pow] at h
        exact h.mono_left nhdsWithin_le_nhds
      have htend : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ (n + 1)) * Y) (𝓝[>] 0) (𝓝 (1 * Y)) := by
        refine ENNReal.Tendsto.mul_const ?_ (Or.inr hY)
        simpa using ENNReal.tendsto_ofReal h0
      rw [one_mul] at htend
      exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall (fun ε hε => hXY ε hε))
  exact le_antisymm (hlim _ _ (fun ε hε => (hglob ε hε).1)) (hlim _ _ (fun ε hε => (hglob ε hε).2))

/-- Area transport onto a graph piece of `spt V`: if `Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)` with
`u ∈ C¹(B̆ⁿ_R(0))`, `s ≤ R` and `μ_V ⌞ B̆_s(ξ) = Hⁿ ⌞ (spt V ∩ B̆_s(ξ))`, then for every `f`
`∫_{B̆_s(ξ)} f dμ_V = ∫_{D_s} J(Du) f(Φ(x)) dx`, where `D_s = {x ∈ B̆ⁿ_R(0) : |(x, u(x))| < s}`,
`Φ(x) = ξ + Q⁻¹(x, u(x))` and `J(P) = √det(I + PᵀP)`.  Proof: `spt V ∩ B̆_s(ξ) = Φ(D_s)`, and
`Φ|_{D_s}` is a measurable embedding pushing `J(Du) dx` forward to `Hⁿ ⌞ Φ(D_s)` by
`dohr_vel_graph_area_formula` and isometry invariance of `Hⁿ`. -/
theorem dohr_vel_graph_area_transport : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), s ≤ R → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) → ∀ f : Amb n ℓ → ℝ, ∫ y in ball ξ s, f y ∂V.weight = ∫ x in {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s}, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * f (ξ + Q.symm (graphPoint x (u x))) := by
  intro n ℓ U V ξ s R Q u hsR hu hgraph hmeas f
  -- `G(x) = (x, u(x))` is continuous on `B̆ⁿ_R(0)`; `π` recovers `x` from `G(x)`.
  have hdiff : ∀ x ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
    intro x w
    simp [π, graphPoint]
  let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  have hGc : ContinuousOn (fun z : Rn n => graphPoint z (u z)) (ball 0 R) := fun x hx =>
    ((LinearMap.toContinuousLinearMap Γl).continuous.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_id.prodMk ((hdiff x hx).continuousAt.continuousWithinAt)))
  -- Step 2: `D_s` is open and contained in `B̆ⁿ_R(0)`.
  set Ds := {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} with hDsdef
  have hDo : IsOpen Ds := by
    have := hGc.isOpen_inter_preimage isOpen_ball (isOpen_ball : IsOpen (ball (0 : Amb n ℓ) s))
    convert this using 1
    ext x
    simp [hDsdef]
  have hDsR : Ds ⊆ ball 0 R := fun x hx => hx.1
  -- Step 3: `Σ ∩ B̆_s(ξ) = Φ(D_s)` with `Φ(x) = ξ + Q⁻¹(G x)`.
  set Φ : Rn n → Amb n ℓ := fun x => ξ + Q.symm (graphPoint x (u x)) with hΦdef
  have hset : V.support ∩ ball ξ s = Φ '' Ds := by
    ext y
    constructor
    · rintro ⟨hyS, hyb⟩
      have hTy : Q (y - ξ) ∈ graphOver u (ball 0 R) ∩ ball 0 R := by
        rw [← hgraph]
        refine ⟨⟨y - ξ, ⟨y, hyS, rfl⟩, rfl⟩, ?_⟩
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact lt_of_lt_of_le (mem_ball.mp hyb) hsR
      obtain ⟨⟨x, hxR, hxG⟩, -⟩ := hTy
      have hxG' : graphPoint x (u x) = Q (y - ξ) := hxG
      refine ⟨x, ⟨hxR, ?_⟩, ?_⟩
      · rw [hxG', LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact mem_ball.mp hyb
      · show ξ + Q.symm (graphPoint x (u x)) = y
        rw [hxG', LinearIsometryEquiv.symm_apply_apply]
        abel
    · rintro ⟨x, ⟨hxR, hxs⟩, rfl⟩
      have hGx : graphPoint x (u x) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R := by
        rw [hgraph]
        exact ⟨⟨x, hxR, rfl⟩, by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hxs hsR⟩
      obtain ⟨⟨z, ⟨y, hyS, rfl⟩, hz⟩, -⟩ := hGx
      have hz' : Q (y - ξ) = graphPoint x (u x) := hz
      refine ⟨?_, ?_⟩
      · show ξ + Q.symm (graphPoint x (u x)) ∈ V.support
        rw [← hz', LinearIsometryEquiv.symm_apply_apply]
        simpa using hyS
      · rw [mem_ball, dist_eq_norm]
        show ‖ξ + Q.symm (graphPoint x (u x)) - ξ‖ < s
        rw [add_sub_cancel_left, LinearIsometryEquiv.norm_map]
        exact hxs
  -- Step 4: `Φ` is continuous and injective on `D_s`; `z ↦ ξ + Q⁻¹ z` is an isometry.
  have hΦcont : ContinuousOn Φ Ds :=
    (continuous_const.add Q.symm.continuous).comp_continuousOn (hGc.mono hDsR)
  have hΦinj : Set.InjOn Φ Ds := by
    intro x _ x' _ h
    have h1 : graphPoint x (u x) = graphPoint x' (u x') := Q.symm.injective (add_left_cancel h)
    have := congrArg π h1
    rwa [hπG, hπG] at this
  have hAisom : Isometry (fun z : Amb n ℓ => ξ + Q.symm z) := by
    refine Isometry.of_dist_eq (fun z z' => ?_)
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 5: set-level area formula `Hⁿ(Φ B) = ∫_B J(Du)` for measurable `B ⊆ D_s`.
  have hsetF : ∀ B : Set (Rn n), MeasurableSet B → B ⊆ Ds →
      (μHE[n] : Measure (Amb n ℓ)) (Φ '' B) =
        ∫⁻ x in B, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ)))))) := by
    intro B hB hBD
    have hΦB : Φ '' B = (fun z : Amb n ℓ => ξ + Q.symm z) '' ((fun x => graphPoint x (u x)) '' B) := by
      rw [Set.image_image]
    rw [hΦB, hAisom.euclideanHausdorffMeasure_image]
    exact Submission.dohr_vel_graph_area_formula n ℓ Ds u hDo (hu.mono hDsR) B hB hBD
  -- Step 6: the area density `J(Du)` is measurable and nonnegative.
  set Jf : Rn n → ℝ := fun x => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
      (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) with hJfdef
  have hJcont : Continuous (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
        (P (EuclideanSpace.single b (1 : ℝ)))))) := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_matrix (fun a b => ?_)
    simp only [Matrix.add_apply, Matrix.of_apply]
    exact continuous_const.add (Continuous.inner
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).continuous
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).continuous)
  have hJfmeas : Measurable Jf := hJcont.measurable.comp (measurable_fderiv ℝ u)
  have hJfnn : ∀ x, 0 ≤ Jf x := fun x => Real.sqrt_nonneg _
  -- Step 7: `Φ|_{D_s}` pushes `(J(Du) dx)|_{D_s}` forward to `Hⁿ ⌞ Φ(D_s)`.
  have hemb : MeasurableEmbedding (Ds.domRestrict Φ) := hΦcont.measurableEmbedding hDo.measurableSet hΦinj
  have hsub := MeasurableEmbedding.subtype_coe hDo.measurableSet
  have hmap : Measure.map (Ds.domRestrict Φ)
      (((volume : Measure (Rn n)).withDensity (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) =
      (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' Ds) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((Ds.domRestrict Φ) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((Ds.domRestrict Φ) ⁻¹' t) ⊆ Ds := by
      rintro x ⟨w, _, rfl⟩
      exact w.property
    rw [withDensity_apply _ hB, ← hsetF _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨hw, ⟨w, w.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  -- Step 8: transport the integral of an arbitrary `f`.
  calc ∫ y in ball ξ s, f y ∂V.weight
      = ∫ y in V.support ∩ ball ξ s, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by rw [hmeas]
    _ = ∫ y in Φ '' Ds, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by rw [hset]
    _ = ∫ z, f (Ds.domRestrict Φ z) ∂(((volume : Measure (Rn n)).withDensity
          (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) := by
        rw [← hmap, hemb.integral_map]
    _ = ∫ x in Ds, f (Φ x) ∂((volume : Measure (Rn n)).withDensity (fun x => ENNReal.ofReal (Jf x))) := by
        have h2 := hsub.integral_map (μ := ((volume : Measure (Rn n)).withDensity
          (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) (fun x => f (Φ x))
        rw [map_comap_subtype_coe hDo.measurableSet] at h2
        exact h2.symm
    _ = ∫ x in Ds, Jf x * f (Φ x) := by
        have h1 : (fun x => ENNReal.ofReal (Jf x)) = fun x => ((Real.toNNReal (Jf x) : ℝ≥0) : ℝ≥0∞) := rfl
        rw [h1, setIntegral_withDensity_eq_setIntegral_smul (hJfmeas.real_toNNReal) _ hDo.measurableSet]
        refine setIntegral_congr_fun hDo.measurableSet (fun x _ => ?_)
        rw [NNReal.smul_def, Real.coe_toNNReal _ (hJfnn x), smul_eq_mul]
  let ιL : Rn ℓ →L[ℝ] Amb n ℓ := Γ.comp (ContinuousLinearMap.inr ℝ (Rn n) (Rn ℓ))
  have hι : ∀ w, ιL w = graphPoint 0 w := fun w => rfl
  let πl : Amb n ℓ →ₗ[ℝ] Rn n :=
    { toFun := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
      map_add' := by intro z z'; rfl
      map_smul' := by intro c z; rfl }
  let πL : Amb n ℓ →L[ℝ] Rn n := LinearMap.toContinuousLinearMap πl
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), πL (graphPoint x w) = x := by
    intro x w
    show (WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp (graphPoint x w) (Fin.castAdd ℓ j)) : Rn n) = x
    simp [graphPoint]
  have hGc : ContinuousOn (fun x => graphPoint x (u x)) (ball 0 r) :=
    Γ.continuous.comp_continuousOn (continuousOn_id.prodMk hu)
  -- the compact image K of tsupport φ and the radii s' < s'' < s
  have hKc : IsCompact ((fun x => graphPoint x (u x)) '' tsupport φ) :=
    hφc.isCompact.image_of_continuousOn (hGc.mono hφr)
  have hKs : (fun x => graphPoint x (u x)) '' tsupport φ ⊆ ball 0 s := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_ball_zero_iff.mpr (hGs x (hφr hx))
  obtain ⟨s1, hs1, hKs1⟩ := exists_lt_subset_ball hKc.isClosed hKs
  have hs'pos : 0 < max s1 (s / 2) := lt_of_lt_of_le (half_pos hs) (le_max_right _ _)
  have hs's : max s1 (s / 2) < s := max_lt hs1 (half_lt_self hs)
  have hs's'' : max s1 (s / 2) < (max s1 (s / 2) + s) / 2 := by linarith
  have hs''s : (max s1 (s / 2) + s) / 2 < s := by linarith
  let ψ : ContDiffBump (0 : Amb n ℓ) := ⟨max s1 (s / 2), (max s1 (s / 2) + s) / 2, hs'pos, hs's''⟩
  have hKψ : (fun x => graphPoint x (u x)) '' tsupport φ ⊆ ball 0 (max s1 (s / 2)) :=
    hKs1.trans (ball_subset_ball (le_max_left _ _))
  have hψ1 : ∀ z ∈ ball (0 : Amb n ℓ) (max s1 (s / 2)), ψ z = 1 := fun z hz =>
    ψ.one_of_mem_closedBall (ball_subset_closedBall hz)
  -- the fields
  let Xt : Amb n ℓ → Amb n ℓ := fun z => ψ z • ιL (φ (πL z))
  let X : Amb n ℓ → Amb n ℓ := fun y => Q.symm (Xt (Q (y - ξ)))
  have hXt1 : ContDiff ℝ 1 Xt :=
    (ψ.contDiff (n := 1)).smul (ιL.contDiff.comp (hφ.comp πL.contDiff))
  have hX1 : ContDiff ℝ 1 X :=
    Q.symm.contDiff.comp (hXt1.comp (Q.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hsuppX : Function.support X ⊆ closedBall ξ ((max s1 (s / 2) + s) / 2) := by
    intro y hy
    have hψne : ψ (Q (y - ξ)) ≠ 0 := by
      intro h0
      apply hy
      show Q.symm (ψ (Q (y - ξ)) • ιL (φ (πL (Q (y - ξ))))) = 0
      rw [h0, zero_smul, map_zero]
    have hmem : Q (y - ξ) ∈ Function.support ψ := hψne
    rw [ψ.support_eq, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] at hmem
    rw [mem_closedBall, dist_eq_norm]
    exact hmem.le
  have htsuppX : tsupport X ⊆ closedBall ξ ((max s1 (s / 2) + s) / 2) :=
    closure_minimal hsuppX isClosed_closedBall
  -- derivative of Xt on the graph
  have hXtD : ∀ x : Rn n, HasFDerivAt Xt (ιL.comp ((fderiv ℝ φ x).comp πL)) (graphPoint x (u x)) := by
    intro x
    have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφ.differentiable one_ne_zero) y
    by_cases hx : x ∈ tsupport φ
    · have hGK : graphPoint x (u x) ∈ ball (0 : Amb n ℓ) (max s1 (s / 2)) := hKψ ⟨x, hx, rfl⟩
      have hh : HasFDerivAt (fun z => ιL (φ (πL z))) (ιL.comp ((fderiv ℝ φ x).comp πL)) (graphPoint x (u x)) := by
        have h1 := (hφd (πL (graphPoint x (u x)))).hasFDerivAt.comp (graphPoint x (u x)) πL.hasFDerivAt
        rw [hπG] at h1
        exact ιL.hasFDerivAt.comp (graphPoint x (u x)) h1
      refine hh.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hGK] with z hz
      show ψ z • ιL (φ (πL z)) = ιL (φ (πL z))
      rw [hψ1 z hz, one_smul]
    · have hdφ : fderiv ℝ φ x = 0 := by
        by_contra hne
        exact hx (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      rw [hdφ, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
      refine (hasFDerivAt_const (0 : Amb n ℓ) _).congr_of_eventuallyEq ?_
      have hN : IsOpen (πL ⁻¹' (tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl.preimage πL.continuous
      have hGN : graphPoint x (u x) ∈ πL ⁻¹' (tsupport φ)ᶜ := by
        show πL (graphPoint x (u x)) ∉ tsupport φ
        rw [hπG]
        exact hx
      filter_upwards [hN.mem_nhds hGN] with z hz
      show ψ z • ιL (φ (πL z)) = 0
      rw [image_eq_zero_of_notMem_tsupport hz, map_zero, smul_zero]
  refine ⟨X, hX1, ?_, htsuppX.trans (closedBall_subset_ball hs''s), ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall ξ ((max s1 (s / 2) + s) / 2))
      (fun y hy => by
        by_contra hne
        exact hy (hsuppX hne))
  · intro x
    show Q.symm (ψ (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)) • ιL (φ (πL (Q (ξ + Q.symm (graphPoint x (u x)) - ξ))))) =
      Q.symm (graphPoint 0 (φ x))
    rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, hπG]
    by_cases hx : x ∈ tsupport φ
    · rw [hψ1 _ (hKψ ⟨x, hx, rfl⟩), one_smul, hι]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h0, ← hι 0]
      simp
  · intro x v w
    have hT : HasFDerivAt (fun y => Q (y - ξ)) (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ)
        (ξ + Q.symm (graphPoint x (u x))) := by
      have := (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp
        (ξ + Q.symm (graphPoint x (u x))) ((hasFDerivAt_id _).sub_const ξ)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have hTx : Q (ξ + Q.symm (graphPoint x (u x)) - ξ) = graphPoint x (u x) := by
      rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
    have hXt' := hXtD x
    rw [← hTx] at hXt'
    have hX := (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp
      (ξ + Q.symm (graphPoint x (u x))) (hXt'.comp (ξ + Q.symm (graphPoint x (u x))) hT)
    have hXeq : X = (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ) ∘ (Xt ∘ fun y => Q (y - ξ)) := rfl
    rw [hXeq, hX.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    show Q.symm (ιL (fderiv ℝ φ x (πL (Q (Q.symm (graphPoint v w)))))) = Q.symm (graphPoint 0 (fderiv ℝ φ x v))
    rw [LinearIsometryEquiv.apply_symm_apply, hπG, hι]
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

end Submission

/-- Simon Ch. 5, proof of Theorem 7.1 (p. 128, system (2)), vertical first variation: if
`Q(spt V - ξ)` is the graph of a `C¹` function `u` over `B̆_R(0)` and `μ_V = Hⁿ ⌞ spt V` on
`B̆_s(ξ)`, then `u` weakly solves the Euler–Lagrange system of the area integrand
`J(P) = √det(I + PᵀP)` with right-hand side `J(Du) ⟨(0, φ), F(x, u(x))⟩`, `F = Q ∘ h ∘ (ξ + Q⁻¹ ·)`,
on a ball `B̆_r(0)`; moreover the rigidly moved data `O = Q(U - ξ)` and `F` stay open and
locally `C^{q,α}`. -/
theorem Submission.dohr_vertical_euler_lagrange : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), V.HasGeneralizedMeanCurvature H → IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) → ∀ (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U) ∧ ∃ r > 0, r ≤ R ∧ (∀ x ∈ ball (0 : Rn n) r, graphPoint x (u x) ∈ (fun y => Q (y - ξ)) '' U) ∧ ∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∫ x in ball (0 : Rn n) r, fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in ball (0 : Rn n) r, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
  intro n ℓ hn U hU V H h q α hH hh hHh ξ s R Q u hs hsR hball hu hu0 hgraph hmeas
  -- Step 1: `O = Q(U - ξ)` is open and `F = Q ∘ h ∘ (ξ + Q⁻¹ ·)` is locally `C^{q,α}` on `O`.
  obtain ⟨hO, hF⟩ := Submission.dohr_vel_holder_rigid_transport n ℓ U hU h q α ξ Q hh
  refine ⟨hO, hF, ?_⟩
  have hR : 0 < R := lt_of_lt_of_le hs hsR
  have huR : ∀ x ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hgp0 : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
  -- `pr` is the projection of `ℝ^{n+ℓ}` onto its first `n` coordinates: `pr (x, w) = x`.
  let pr : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hprG : ∀ (x : Rn n) (w : Rn ℓ), pr (graphPoint x w) = x := by
    intro x w
    simp [pr, graphPoint]
  -- Step 2: `G x = (x, u x)` is continuous at `0` with `G 0 = 0`; choose `r = min δ R` with
  -- `|G x| < s` on `B̆_r(0)`.
  have hGcont0 : ContinuousAt (fun z : Rn n => graphPoint z (u z)) 0 :=
    (Submission.dohr_vel_graph_fderiv n ℓ u 0 (huR 0 (mem_ball_self hR))).1.continuousAt
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hGcont0 s hs
  have hGs : ∀ x ∈ ball (0 : Rn n) (min δ R), ‖graphPoint x (u x)‖ < s := by
    intro x hx
    have hx' : dist x 0 < δ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
    have := hδG hx'
    simpa [hu0, hgp0, dist_zero_right] using this
  refine ⟨min δ R, lt_min hδ hR, min_le_right _ _, ?_, ?_⟩
  · -- `G x = Q ((ξ + Q⁻¹ G x) - ξ)` with `ξ + Q⁻¹ G x ∈ B_s(ξ) ⊆ U`.
    intro x hx
    refine ⟨ξ + Q.symm (graphPoint x (u x)), ?_, ?_⟩
    · apply hball
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
      exact (hGs x hx).le
    · simp
  · intro φ hφ1 hφc hφr
    have hrR : min δ R ≤ R := min_le_right _ _
    have hucont : ContinuousOn u (ball 0 (min δ R)) := hu.continuousOn.mono (ball_subset_ball hrR)
    -- Step 4: the vertical test field `X = Q⁻¹ ψ (0, φ ∘ pr) ∘ Q(· - ξ)`, admissible in `U`.
    obtain ⟨X, hX1, hXc, hXs, hXval, hXder⟩ :=
      Submission.dohr_vel_vertical_test_field n ℓ ξ Q s (min δ R) u φ hs hucont hGs hφ1 hφc hφr
    have hGMC := hH.2 X hX1 hXc (hXs.trans (ball_subset_closedBall.trans hball))
    -- (iii), (Iso) and (Area): `μ_V`-integrals over `B̆_s(ξ)` become integrals over
    -- `D_s = {x ∈ B̆_R(0) : |G x| < s}` with the area element `J(Du)`.
    have hE := Submission.dohr_vel_graph_area_transport n ℓ U V ξ s R Q u hsR hu hgraph hmeas
    -- Step 3: `μ_V`-a.e. on `B̆_s(ξ)` the tangent plane is `Q⁻¹` of the graph's tangent plane.
    obtain ⟨-, hTP⟩ :=
      Submission.dohr_graph_tangent_planes n ℓ hn U hU V ξ s R Q u hs hsR hball hu hgraph
    have hDs_open : IsOpen {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} := by
      have hGc : ContinuousOn (fun z : Rn n => graphPoint z (u z)) (ball 0 R) := fun x hx =>
        (Submission.dohr_vel_graph_fderiv n ℓ u x (huR x hx)).1.continuousAt.continuousWithinAt
      have := hGc.isOpen_inter_preimage isOpen_ball (isOpen_ball : IsOpen (ball (0 : Amb n ℓ) s))
      convert this using 1
      ext x
      simp
    have hrDs : ball (0 : Rn n) (min δ R) ⊆
        {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} :=
      fun x hx => ⟨ball_subset_ball hrR hx, hGs x hx⟩
    have hφzero : ∀ x ∉ ball (0 : Rn n) (min δ R), φ x = 0 ∧ fderiv ℝ φ x = 0 := by
      intro x hx
      have hxs : x ∉ tsupport φ := fun h' => hx (hφr h')
      refine ⟨image_eq_zero_of_notMem_tsupport hxs, ?_⟩
      by_contra hne
      exact hxs (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    -- Step 6, left side: `div_M X` vanishes off `tsupport X ⊆ B̆_s(ξ)`.
    have hL1 : ∫ y, V.divM X y ∂V.weight = ∫ y in ball ξ s, V.divM X y ∂V.weight := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      have hyX : y ∉ tsupport X := fun h' => hy (hXs h')
      have h0 : fderiv ℝ X y = 0 := by
        by_contra hne
        exact hyX (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      simp [RectifiableVarifold.divM, h0]
    have hSigmeas : MeasurableSet (V.support ∩ ball ξ s) :=
      (hU.measurableSet.inter Measure.isClosed_support.measurableSet).inter measurableSet_ball
    have hae_supp : ∀ᵐ y ∂(V.weight.restrict (ball ξ s)), y ∈ V.support ∩ ball ξ s := by
      rw [hmeas]
      exact ae_restrict_mem hSigmeas
    -- `div_M X (y) = trace (DX(y) ∘ p_{P_y})` for `μ_V`-a.e. `y ∈ B̆_s(ξ)`, where
    -- `P_y = Q⁻¹ (range DG(x))` and `x = pr (Q (y - ξ))` is the unique graph parameter of `y`.
    have hL2 : ∫ y in ball ξ s, V.divM X y ∂V.weight =
        ∫ y in ball ξ s, LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X y).toLinearMap ∘ₗ
          (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
            (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) (pr (Q (y - ξ)))).toLinearMap)).starProjection.toLinearMap)
          ∂V.weight := by
      apply integral_congr_ae
      filter_upwards [hae_supp, ae_restrict_of_ae hTP] with y hy hyTP
      obtain ⟨hySig, hyb⟩ := hy
      have hTy : Q (y - ξ) ∈ graphOver u (ball 0 R) ∩ ball 0 R := by
        rw [← hgraph]
        refine ⟨⟨y - ξ, ⟨y, hySig, rfl⟩, rfl⟩, ?_⟩
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact lt_of_lt_of_le (mem_ball.mp hyb) hsR
      obtain ⟨⟨x, hxR, hxG⟩, -⟩ := hTy
      have hprx : pr (Q (y - ξ)) = x := by
        rw [← hxG]
        exact hprG x (u x)
      have hproj := hyTP hyb x hxR hxG.symm
      show LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X y).toLinearMap ∘ₗ (V.tangentProj y).toLinearMap) = _
      rw [hprx, hproj]
    -- Step 5: `J(Du) · trace (DX ∘ p_{P_y}) = DJ(Du)[Dφ]` on `D_s` (Jacobi's formula).
    have hL4 : ∀ x ∈ {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s},
        Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) *
          LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X (ξ + Q.symm (graphPoint x (u x)))).toLinearMap ∘ₗ
            (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
              (fderiv ℝ (fun z : Rn n => graphPoint z (u z))
                (pr (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)))).toLinearMap)).starProjection.toLinearMap) =
        fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
            (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) := by
      intro x hx
      have hA := Submission.dohr_vel_graph_fderiv n ℓ u x (huR x hx.1)
      have hTx : pr (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)) = x := by
        rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, hprG]
      rw [hTx, Submission.dohr_vel_graph_projection_trace n ℓ (fderiv ℝ u x) (fderiv ℝ φ x)
        (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x) Q
        (fderiv ℝ X (ξ + Q.symm (graphPoint x (u x)))) hA.2 (hXder x),
        (Submission.dohr_vel_area_integrand_fderiv n ℓ (fderiv ℝ u x)).2 (fderiv ℝ φ x)]
    -- The integrand vanishes on `D_s \ B̆_r(0)`, where `Dφ = 0`.
    have hLHS : ∫ y, V.divM X y ∂V.weight = ∫ x in ball (0 : Rn n) (min δ R),
        fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
            (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) := by
      rw [hL1, hL2, hE, setIntegral_congr_fun hDs_open.measurableSet hL4]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hDs_open.measurableSet hrDs ?_
      intro x hx
      rw [(hφzero x hx.2).2, map_zero]
    -- Step 7, right side: `H = h` `μ_V`-a.e., `⟨X, h⟩` vanishes off `B̆_s(ξ)`, and on the graph
    -- `⟨X, h⟩ = ⟨Q⁻¹ (0, φ), h⟩ = ⟨(0, φ), Q h⟩`.
    have hR1 : ∫ y, inner ℝ (X y) (H y) ∂V.weight = ∫ y, inner ℝ (X y) (h y) ∂V.weight :=
      integral_congr_ae (hHh.mono fun y hy => by simp only [hy])
    have hR2 : ∫ y, inner ℝ (X y) (h y) ∂V.weight =
        ∫ y in ball ξ s, inner ℝ (X y) (h y) ∂V.weight := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      have hyX : y ∉ tsupport X := fun h' => hy (hXs h')
      rw [image_eq_zero_of_notMem_tsupport hyX, inner_zero_left]
    have hR4 : ∀ x : Rn n,
        inner ℝ (X (ξ + Q.symm (graphPoint x (u x)))) (h (ξ + Q.symm (graphPoint x (u x)))) =
          inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
      intro x
      rw [hXval x, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
    have hRHS : ∫ y, inner ℝ (X y) (H y) ∂V.weight = ∫ x in ball (0 : Rn n) (min δ R),
        Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) *
          inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
      rw [hR1, hR2, hE]
      simp_rw [hR4]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hDs_open.measurableSet hrDs ?_
      intro x hx
      rw [(hφzero x hx.2).1, hgp0, inner_zero_left, mul_zero]
    -- Step 8: the first variation identity `∫ div_M X dμ_V = -∫ ⟨X, H⟩ dμ_V`.
    rw [← hLHS, ← hRHS]
    exact hGMC

end GMT.Ch05
