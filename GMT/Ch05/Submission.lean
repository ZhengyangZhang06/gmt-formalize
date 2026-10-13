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

/-- Cutoff for the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): there is `K ≥ 0` such that for every `n`,
`y ∈ ℝⁿ` and `ρ > 0` some `C¹` function `η : ℝⁿ → [0, 1]` equals `1` on `B̆_ρ(y)`, has compact
support with `tsupport η ⊆ B̆_{2ρ}(y)`, and satisfies `‖Dη(x)‖ ≤ K/ρ`.  Here
`η(x) = ψ(‖x − y‖²/ρ²)` with `ψ(s) = S((3 − s)/2)`, `S = Real.smoothTransition`, and
`K = 4 sup |ψ'|`. -/
theorem dohr_eb_sch_cacc_exists_cutoff : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (y : Rn n) (ρ : ℝ), 0 < ρ → ∃ η : Rn n → ℝ, ContDiff ℝ 1 η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ ball y ρ, η x = 1) ∧ HasCompactSupport η ∧ tsupport η ⊆ ball y (2 * ρ) ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ K / ρ := by
  -- Step 1: the profile `ψ(s) = S((3 − s)/2)` is `C¹`; `ψ = 1` for `s ≤ 1`, `ψ = 0` for `s ≥ 3`.
  set ψ : ℝ → ℝ := fun s => Real.smoothTransition ((3 - s) / 2) with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    (Real.smoothTransition.contDiff (n := 1)).comp ((contDiff_const.sub contDiff_id).div_const _)
  -- Step 2: `ψ'` is continuous and vanishes off `[1, 3]`, so `|ψ'| ≤ cψ` with `cψ ≥ 0`;
  -- `K = 4 cψ`.
  have hψ'c : Continuous (deriv ψ) := hψc.continuous_deriv le_rfl
  have hψ'0 : ∀ s, s ∉ Icc (1 : ℝ) 3 → deriv ψ s = 0 := by
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.one_of_one_le (by linarith [mem_Iio.mp ht])
      rw [hev.deriv_eq, deriv_const]
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Ioi.mp ht])
      rw [hev.deriv_eq, deriv_const]
  obtain ⟨cψ, hcψ⟩ : ∃ cψ, ∀ s, ‖deriv ψ s‖ ≤ cψ := by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (hψ'c.continuousOn (s := Icc (1 : ℝ) 3))
    refine ⟨max C 0, fun s => ?_⟩
    by_cases hs : s ∈ Icc (1 : ℝ) 3
    · exact (hC s hs).trans (le_max_left _ _)
    · rw [hψ'0 s hs, norm_zero]
      exact le_max_right _ _
  have hcψ0 : 0 ≤ cψ := (norm_nonneg _).trans (hcψ 0)
  refine ⟨4 * cψ, by positivity, ?_⟩
  -- Step 3: for `n`, `y` and `ρ > 0` take `η(x) = ψ(‖x − y‖²/ρ²)`.
  intro n y ρ hρ
  have hρ2 : 0 < ρ ^ 2 := by positivity
  -- Step 4: `η(x) ≠ 0` forces `‖x − y‖² < 3ρ²`, so `tsupport η ⊆ B_{7ρ/4}(y)` (closed ball).
  have hsupp : Function.support (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆
      closedBall y (7 / 4 * ρ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [mem_closedBall, dist_eq_norm]
    by_contra hlt
    push Not at hlt
    apply hx
    simp only [hψ]
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : 3 * ρ ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith
    have h2 : 3 ≤ ‖x - y‖ ^ 2 / ρ ^ 2 := by
      rw [le_div_iff₀ hρ2]
      linarith
    linarith
  have htsupp : tsupport (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆ closedBall y (7 / 4 * ρ) :=
    closure_minimal hsupp isClosed_closedBall
  refine ⟨fun x => ψ (‖x - y‖ ^ 2 / ρ ^ 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `η` is `C¹`: `ψ` composed with the smooth map `x ↦ ‖x − y‖²/ρ²`.
  · exact hψc.comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)
  -- `0 ≤ η ≤ 1` since `0 ≤ S ≤ 1`.
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `η = 1` on `B̆_ρ(y)`: there `‖x − y‖²/ρ² < 1`.
  · intro x hx
    have hx' : ‖x - y‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hx
    have h1 : ‖x - y‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (x - y)]
    have h2 : ‖x - y‖ ^ 2 / ρ ^ 2 < 1 := by
      rw [div_lt_one hρ2]
      exact h1
    simp only [hψ]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  -- Compact support: `tsupport η` is a closed subset of the compact `B_{7ρ/4}(y)`.
  · exact (isCompact_closedBall y (7 / 4 * ρ)).of_isClosed_subset (isClosed_tsupport _) htsupp
  -- `tsupport η ⊆ B_{7ρ/4}(y) ⊆ B̆_{2ρ}(y)`.
  · refine htsupp.trans (closedBall_subset_ball ?_)
    linarith
  -- Step 5: by the chain rule `Dη(x) = ψ'(s) (2/ρ²) ⟨x − y, ·⟩` with `s = ‖x − y‖²/ρ²`, so
  -- `‖Dη(x)‖ = |ψ'(s)| (2/ρ²) ‖x − y‖`; this is `0` if `s > 3`, and if `s ≤ 3` then
  -- `‖x − y‖ ≤ 2ρ` and `‖Dη(x)‖ ≤ cψ (2/ρ²) (2ρ) = 4 cψ/ρ`.
  · intro x
    set s := ‖x - y‖ ^ 2 / ρ ^ 2 with hs
    have hf : HasFDerivAt (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2)
        (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y)) x := by
      have h0 : HasFDerivAt (fun x : Rn n => x - y) (ContinuousLinearMap.id ℝ (Rn n)) x :=
        (hasFDerivAt_id x).sub_const y
      have := h0.norm_sq.mul_const ((ρ ^ 2)⁻¹)
      simp only [div_eq_mul_inv]
      convert this using 1
      ext v
      simp
      ring
    have hψd : HasDerivAt ψ (deriv ψ s) s :=
      ((hψc.differentiable one_ne_zero) s).hasDerivAt
    have hη := hψd.comp_hasFDerivAt x hf
    rw [show (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) =
        ψ ∘ (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2) from rfl, hη.fderiv]
    by_cases h3 : 3 < s
    · rw [hψ'0 s (fun h => by linarith [h.2]), zero_smul, norm_zero]
      positivity
    · push Not at h3
      have hxy : ‖x - y‖ ≤ 2 * ρ := by
        have : ‖x - y‖ ^ 2 ≤ 3 * ρ ^ 2 := by
          have := (div_le_iff₀ hρ2).mp h3
          linarith
        nlinarith [norm_nonneg (x - y)]
      have hnorm : ‖deriv ψ s • (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y))‖ =
          ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖) := by
        rw [norm_smul, norm_smul, innerSL_apply_norm,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ * 2)]
      rw [hnorm]
      calc ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖)
          ≤ cψ * (((ρ ^ 2)⁻¹ * 2) * (2 * ρ)) := by
            gcongr
            exact hcψ s
        _ = 4 * cψ / ρ := by
            field_simp
            ring
/-- Test function of the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap
for Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if `U ⊆ ℝⁿ` is open, `V ∈ C¹(U; ℝ^ℓ)`,
`c ∈ ℝ^ℓ` and `η ∈ C¹_c(ℝⁿ)` with `spt η ⊆ U`, then `ζ = η² (V − c)` is `C¹` on `ℝⁿ` with compact
support in `U`, and `Dζ = η² DV + 2η (V − c) ⊗ Dη` at every point of `ℝⁿ` (off `U` both sides
vanish, whatever the junk value of `DV` there). -/
theorem dohr_eb_sch_cacc_test_function : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) ∧ HasCompactSupport (fun x => η x ^ 2 • (V x - c)) ∧ tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ U ∧ ∀ x, fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x = η x ^ 2 • fderiv ℝ V x + (2 * η x) • (fderiv ℝ η x).smulRight (V x - c) := by
  intro n ℓ U V η c hU hV hη hηc hηU
  -- Step 1: `support ζ ⊆ support η`, so `tsupport ζ ⊆ tsupport η ⊆ U` and `ζ` has compact support.
  -- (Bare `support` is `RectifiableVarifold.support` in this scope.)
  have hsupp : Function.support (fun x => η x ^ 2 • (V x - c)) ⊆ Function.support η := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have htsupp : tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ tsupport η := closure_mono hsupp
  have hcs : HasCompactSupport (fun x => η x ^ 2 • (V x - c)) := hηc.mono hsupp
  -- Step 2: `ζ` is `C¹` on `U`, as the product of `η² ∈ C¹(ℝⁿ)` and `V − c ∈ C¹(U)`.
  have h1 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) U :=
    ((hη.pow 2).contDiffOn).smul (hV.sub contDiffOn_const)
  -- Step 3: `ζ = 0` on the open set `W = (tsupport η)ᶜ`, so `ζ` is `C¹` on `W`.
  have h2 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
    have heq : EqOn (fun _ => (0 : Rn ℓ)) (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
      intro x hx
      have : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
    exact contDiffOn_const.congr (fun x hx => (heq hx).symm)
  -- Step 4: `U ∪ W = ℝⁿ` because `tsupport η ⊆ U`; gluing the two open pieces, `ζ ∈ C¹(ℝⁿ)`.
  have hcover : U ∪ (tsupport η)ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ tsupport η
    · exact Or.inl (hηU hx)
    · exact Or.inr hx
  have hcd : ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) :=
    contDiff_of_contDiffOn_union_of_isOpen h1 h2 hcover hU (isClosed_tsupport η).isOpen_compl
  refine ⟨hcd, hcs, htsupp.trans hηU, fun x => ?_⟩
  by_cases hx : x ∈ U
  -- Step 5: at `x ∈ U`, `D(η²)(x) = 2η(x) Dη(x)` and the product rule for `η² • (V − c)` give
  -- `Dζ(x) = η(x)² DV(x) + (2η(x) Dη(x)).smulRight (V(x) − c)`.
  · have hVd : HasFDerivAt V (fderiv ℝ V x) x :=
      (((hV.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hηd : HasFDerivAt η (fderiv ℝ η x) x := ((hη.differentiable one_ne_zero) x).hasFDerivAt
    have hsq : HasFDerivAt (fun x => η x ^ 2) ((2 * η x) • fderiv ℝ η x) x := by
      have := hηd.mul hηd
      convert this using 1
      · ext y; simp [sq]
      · rw [two_mul, add_smul]
    have hprod := hsq.smul (hVd.sub_const c)
    rw [show (fun x => η x ^ 2 • (V x - c)) = ((fun x => η x ^ 2) • fun x => V x - c) from rfl,
      hprod.fderiv]
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  -- Step 6: at `x ∉ U`, `x ∉ tsupport η ⊇ tsupport ζ`, so `Dζ(x) = 0`, `Dη(x) = 0` and `η(x) = 0`;
  -- both sides vanish.
  · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
    have hxζ : x ∉ tsupport (fun x => η x ^ 2 • (V x - c)) := fun h => hx' (htsupp h)
    rw [fderiv_of_notMem_tsupport ℝ hxζ, fderiv_of_notMem_tsupport ℝ hx',
      image_eq_zero_of_notMem_tsupport hx']
    ext v
    simp
/-- Energy (Caccioppoli) estimate for a constant-coefficient elliptic system.  Let `A` satisfy the
Legendre condition `A[P][P] ≥ λ‖P‖²` and the bound `|A[P][Q]| ≤ Λ‖P‖‖Q‖`, let `V` be `C¹` on the open
set `U` with `∫ A[DV][Dζ] = 0` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let `η ≥ 0` be a `C¹_c` cutoff with
`tsupport η ⊆ U`.  Then `∫ η²‖DV‖² ≤ (4Λ²/λ²) ∫ ‖V − c‖²‖Dη‖²` (lower integrals, in `[0, ∞]`).
Test with `ζ = η²(V − c)` and absorb the cross term by Young's inequality. -/
theorem dohr_eb_sch_cacc_energy_estimate :
    ∀ (n ℓ : ℕ) (lam Lam : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → (∀ x, 0 ≤ η x) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) * ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := by
  intro n ℓ lam Lam A U V η c hlam hcoer hbdd hU hV hη hηc hηU hη0 hweak
  -- the test function `ζ = η² (V - c)` is admissible
  obtain ⟨hζ1, hζc, hζU, hζd⟩ :=
    Submission.dohr_eb_sch_cacc_test_function n ℓ U V η c hU hV hη hηc hηU
  have h0 := hweak _ hζ1 hζc hζU
  -- continuity of the ingredients
  have hDVc : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  have hVc : ContinuousOn V U := hV.continuousOn
  have hDη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDζ : Continuous (fderiv ℝ (fun x => η x ^ 2 • (V x - c))) :=
    hζ1.continuous_fderiv one_ne_zero
  -- the three integrands
  set h : Rn n → ℝ := fun x => A (fderiv ℝ V x) (fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x)
    with hh
  set g1 : Rn n → ℝ := fun x => η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2 with hg1
  set g3 : Rn n → ℝ := fun x => ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 with hg3
  have hsupp_h : Function.support h ⊆ tsupport (fun x => η x ^ 2 • (V x - c)) := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hh, fderiv_of_notMem_tsupport ℝ hxs, map_zero]
  have hsupp_g1 : Function.support g1 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg1, image_eq_zero_of_notMem_tsupport hxs]
  have hsupp_g3 : Function.support g3 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg3, fderiv_of_notMem_tsupport ℝ hxs]
  -- continuous on `U` with `tsupport ⊆ U`, hence continuous with compact support
  have hcont_h : Continuous h := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_h (isClosed_tsupport _)).trans hζU)
    exact (A.continuous.comp_continuousOn hDVc).clm_apply hDζ.continuousOn
  have hcont_g1 : Continuous g1 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g1 (isClosed_tsupport _)).trans hηU)
    exact (hη.continuous.pow 2).continuousOn.mul (hDVc.norm.pow 2)
  have hcont_g3 : Continuous g3 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g3 (isClosed_tsupport _)).trans hηU)
    exact ((hVc.sub continuousOn_const).norm.pow 2).mul (hDη.norm.pow 2).continuousOn
  have hint_h : Integrable h := hcont_h.integrable_of_hasCompactSupport (hζc.mono' hsupp_h)
  have hint_g1 : Integrable g1 := hcont_g1.integrable_of_hasCompactSupport (hηc.mono' hsupp_g1)
  have hint_g3 : Integrable g3 := hcont_g3.integrable_of_hasCompactSupport (hηc.mono' hsupp_g3)
  -- pointwise lower bound: Legendre condition, bound on `A`, and Young's inequality
  have hpt : ∀ x, lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x ≤ h x := by
    intro x
    have hid : h x = η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) +
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      simp only [hh, hζd x, map_add, map_smul, smul_eq_mul]
    rw [hid]
    have hc := hcoer (fderiv ℝ V x)
    have hb := hbdd (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c))
    rw [ContinuousLinearMap.norm_smulRight_apply] at hb
    have hb' := (abs_le.mp hb).1
    set a := η x * ‖fderiv ℝ V x‖ with ha
    set b := ‖V x - c‖ * ‖fderiv ℝ η x‖ with hb_def
    have e1 : lam * a ^ 2 ≤ η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) := by
      rw [ha, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (η x))]
    have e2 : -(2 * Lam * (a * b)) ≤
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      have h2η : 0 ≤ 2 * η x := by linarith [hη0 x]
      have := mul_le_mul_of_nonneg_left hb' h2η
      rw [ha, hb_def]
      linarith [this]
    have e3 : 2 * Lam * (a * b) ≤ lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 := by
      have key : lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 - 2 * Lam * (a * b) =
          (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by positivity
      linarith
    have hg1x : g1 x = a ^ 2 := by rw [hg1, ha, mul_pow]
    have hg3x : g3 x = b ^ 2 := by rw [hg3, hb_def, mul_pow]
    rw [hg1x, hg3x]
    linarith
  -- integrate (`∫ h = 0`) and absorb
  have hint_lhs : Integrable (fun x => lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x) :=
    (hint_g1.const_mul _).sub (hint_g3.const_mul _)
  have hmono := integral_mono hint_lhs hint_h hpt
  rw [h0, integral_sub (hint_g1.const_mul _) (hint_g3.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have key : ∫ x, g1 x ≤ 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by
    have h2 : lam / 2 * ∫ x, g1 x ≤ 2 * Lam ^ 2 / lam * ∫ x, g3 x := by linarith
    have hlam2 : 0 < lam / 2 := by positivity
    calc ∫ x, g1 x = (lam / 2)⁻¹ * (lam / 2 * ∫ x, g1 x) := by field_simp
      _ ≤ (lam / 2)⁻¹ * (2 * Lam ^ 2 / lam * ∫ x, g3 x) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam2.le)
      _ = 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by field_simp; ring
  -- pass to lower integrals
  have hg1n : 0 ≤ᵐ[volume] g1 := ae_of_all _ (fun x => by positivity)
  have hg3n : 0 ≤ᵐ[volume] g3 := ae_of_all _ (fun x => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_g1 hg1n,
    ← ofReal_integral_eq_lintegral_ofReal hint_g3 hg3n, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
