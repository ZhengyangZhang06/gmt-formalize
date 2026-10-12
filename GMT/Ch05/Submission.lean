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

/-- **Simon Ch. 2, Theorem 1.5 (C¹ approximation of Lipschitz functions).**  A Lipschitz
`f : ℝⁿ → ℝ` agrees with a `C¹` function outside a set of arbitrarily small Lebesgue measure.
Proof, following Simon's printed argument: by Rademacher `f` is differentiable off a Borel null
set; the Whitney quotients `σₖ(x) = sup {|f(x+v) - f(x) - Df(x) v| / |v| : 0 < |v| < 1/(k+1)}`
are lower semicontinuous in `(x, Df(x))`, hence Borel, and tend to `0` wherever `f` is
differentiable; Egorov's theorem on the balls `B(0, J)` with summable tolerances, together with
outer regularity, gives a closed `A` of small complement on whose compact subsets the
first-order Taylor remainder is uniformly small (this also makes `Df` continuous on `A`, so no
separate Lusin step is needed); Whitney's extension theorem (Simon Ch. 2, 1.6), proved inline
with Vitali-selected Whitney balls and a scaled-bump partition of unity, yields `g ∈ C¹` with
`g = f` on `A`. -/
theorem aetp_lipschitz_c1_approximation : ∀ (n : ℕ), 1 ≤ n → ∀ (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x} < ε := by
  intro n _
  -- Whitney's C¹ extension theorem (Simon Ch. 2, Theorem 1.6), in the local uniform form.
  have whitney : ∀ (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A →
      (∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ e) ∧
        ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ → |h c - h b - D b (c - b)| ≤ e * ‖c - b‖) →
      ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ x ∈ A, g x = h x := by
    intro A h D hA hW
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, contDiff_const, fun x hx => hx.elim⟩
    classical
    -- Whitney radius `r x = min 1 (dist (x, A)) / 100`.
    obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 := ⟨_, fun _ => rfl⟩
    have hr0 : ∀ x, 0 ≤ r x := fun x => by
      rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
    have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
      rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
    have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
      rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).1 hx)) (by norm_num)
    have hcomp : ∀ x c, dist x c ≤ r x + 10 * r c →
        r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
      have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := by
        intro x y
        have h1 := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
        simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h1
        rw [hr, hr]
        linarith [(abs_sub_le_iff.1 h1).1]
      intro x c hxc
      have h1 := hrlip x c
      have h2 := hrlip c x
      rw [dist_comm c x] at h2
      have h3 := hr0 x
      have h4 := hr0 c
      exact ⟨by linarith, by linarith, by linarith⟩
    -- Vitali: disjoint balls `B(c, r c)` whose fourfold enlargements cover `Aᶜ`.
    obtain ⟨Cs, hCsA, hCsdisj, hCscov⟩ : ∃ Cs : Set (Rn n), Cs ⊆ Aᶜ ∧
        Cs.PairwiseDisjoint (fun c => ball c (r c)) ∧ ∀ x ∉ A, ∃ c ∈ Cs, dist x c < 4 * r c := by
      have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
        rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball Aᶜ
        (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
      refine ⟨s, hs, hd, fun x hx => ?_⟩
      obtain ⟨c, hcs, hxc⟩ := hc x hx
      exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
    have hsep : ∀ c ∈ Cs, ∀ c' ∈ Cs, c ≠ c' → r c ≤ dist c c' := by
      intro c hc c' hc' hcc
      by_contra hlt
      exact Set.disjoint_left.1 (hCsdisj hc hc' hcc) (show c' ∈ ball c (r c) by
        rw [mem_ball, dist_comm]; exact not_le.1 hlt) (mem_ball_self (hrpos c' (hCsA hc')))
    -- A uniform packing bound for `1/2`-separated subsets of `B(0, 21)`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Rn n), s ⊆ closedBall 0 21 →
        s.Pairwise (fun y z => 1 / 2 ≤ dist y z) → s.Finite ∧ s.ncard ≤ N := by
      obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1
        (isCompact_closedBall (0 : Rn n) 21).totallyBounded (1 / 4) (by norm_num)
      refine ⟨t.ncard, fun s hs hs2 => ?_⟩
      have hc : ∀ x : s, ∃ y : t, dist (x : Rn n) y < 1 / 4 := by
        intro x
        obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (hcover (hs x.2))
        exact ⟨⟨y, hyt⟩, hxy⟩
      choose c hc using hc
      have hi : Function.Injective c := by
        intro x y hxy
        by_contra hne
        have hd := hs2 x.2 y.2 (fun h' => hne (Subtype.ext h'))
        have htri := dist_triangle (x : Rn n) (c x) y
        have hxc := hc x
        have hyc := hc y
        rw [← hxy, dist_comm (y : Rn n)] at hyc
        linarith
      have : Finite t := ht.to_subtype
      have : Finite s := Finite.of_injective c hi
      exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
    -- The finite sets `F x` of centres near `x ∉ A`.
    obtain ⟨F, hF⟩ : ∃ F : Rn n → Finset (Rn n), ∀ x, x ∉ A →
        (∀ c, c ∈ F x ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ (F x).card ≤ N := by
      have key : ∀ x, x ∉ A → ∃ s : Finset (Rn n),
          (∀ c, c ∈ s ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
        intro x hx
        have hrx := hrpos x hx
        set T : Set (Rn n) := {c | c ∈ Cs ∧ dist x c ≤ r x + 10 * r c} with hT
        obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n, ∀ c, φ c = (r x)⁻¹ • (c - x) := ⟨_, fun _ => rfl⟩
        have hφi : Function.Injective φ := by
          intro c d hcd
          rw [hφ, hφ] at hcd
          have := congrArg (fun z => r x • z) hcd
          simpa [smul_smul, hrx.ne'] using this
        have hnφ : ∀ c d, dist (φ c) (φ d) = dist c d / r x := by
          intro c d
          rw [hφ, hφ, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hrx.le), ← dist_eq_norm, inv_mul_eq_div]
        have hsub : φ '' T ⊆ closedBall 0 21 := by
          rintro _ ⟨c, hc, rfl⟩
          have h0 : φ x = 0 := by rw [hφ, sub_self, smul_zero]
          rw [mem_closedBall, ← h0, hnφ, div_le_iff₀ hrx, dist_comm]
          exact (hcomp x c hc.2).2.2
        have hsep' : (φ '' T).Pairwise (fun y z => 1 / 2 ≤ dist y z) := by
          rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
          have h1 := hsep c hc.1 d hd.1 (fun h' => hcd (congrArg φ h'))
          have h2 := (hcomp x c hc.2).1
          rw [hnφ, le_div_iff₀ hrx]
          linarith
        obtain ⟨hfin, hcard⟩ := hN (φ '' T) hsub hsep'
        have hTfin : T.Finite := hfin.of_finite_image hφi.injOn
        refine ⟨hTfin.toFinset, fun c => hTfin.mem_toFinset, ?_⟩
        rw [← Set.ncard_eq_toFinset_card T hTfin, ← Set.ncard_image_of_injective T hφi]
        exact hcard
      choose! F hF using key
      exact ⟨F, hF⟩
    -- A fixed bump `β`, equal to `1` on `B(0, 4)` and to `0` off `B(0, 8)`.
    obtain ⟨β, hβ0, hβ1, hβone, hβzero, hβs, L, hL⟩ : ∃ β : Rn n → ℝ, (∀ y, 0 ≤ β y) ∧
        (∀ y, β y ≤ 1) ∧ (∀ y, ‖y‖ ≤ 4 → β y = 1) ∧ (∀ y, 8 ≤ ‖y‖ → β y = 0) ∧
        ContDiff ℝ 1 β ∧ ∃ L : ℝ≥0, LipschitzWith L β := by
      let b : ContDiffBump (0 : Rn n) := ⟨4, 8, by norm_num, by norm_num⟩
      refine ⟨b, fun y => b.nonneg, fun y => b.le_one, fun y hy => b.one_of_mem_closedBall ?_,
        fun y hy => Function.notMem_support.1 ?_, b.contDiff (n := 1),
        ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (b.contDiff (n := 1))
          one_ne_zero⟩
      · rw [mem_closedBall, dist_zero_right]; exact hy
      · rw [b.support_eq, mem_ball, dist_zero_right]; exact not_lt.2 hy
    -- The rescaled bumps `ψ c y = β ((y - c) / r c)`.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Rn n → Rn n → ℝ, ∀ c y, ψ c y = β ((r c)⁻¹ • (y - c)) :=
      ⟨_, fun _ _ => rfl⟩
    have hnsc : ∀ c y, 0 < r c → ‖(r c)⁻¹ • (y - c)‖ = dist y c / r c := by
      intro c y hc
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, inv_mul_eq_div]
    have hψ0 : ∀ c y, 0 ≤ ψ c y := fun c y => by rw [hψ]; exact hβ0 _
    have hψone : ∀ c y, 0 < r c → dist y c ≤ 4 * r c → ψ c y = 1 := by
      intro c y hc hy; rw [hψ]; apply hβone; rw [hnsc c y hc, div_le_iff₀ hc]; exact hy
    have hψzero : ∀ c y, 0 < r c → 8 * r c ≤ dist y c → ψ c y = 0 := by
      intro c y hc hy; rw [hψ]; apply hβzero; rw [hnsc c y hc, le_div_iff₀ hc]; exact hy
    have hψs : ∀ c, ContDiff ℝ 1 (ψ c) := by
      intro c
      rw [show ψ c = fun y => β ((r c)⁻¹ • (y - c)) from funext (hψ c)]
      exact hβs.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hψd : ∀ c y, 0 < r c → ‖fderiv ℝ (ψ c) y‖ ≤ L / r c := by
      intro c y hc
      have hlip : LipschitzWith (L * (Real.toNNReal (r c))⁻¹) (ψ c) := by
        refine LipschitzWith.of_dist_le_mul fun y z => ?_
        rw [hψ, hψ, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le]
        refine (hL.dist_le_mul _ _).trans (le_of_eq ?_)
        rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, mul_assoc]
      have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
      rwa [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le, ← div_eq_mul_inv] at this
    -- The locally finite sum `S = ∑ c ∈ Cs, ψ c ≥ 1` on `Aᶜ`.
    obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ y, S y = ∑ᶠ c ∈ Cs, ψ c y := ⟨_, fun _ => rfl⟩
    have hψF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → ψ c y = 0 := by
      intro x hx y hy c hc hcF
      apply hψzero c y (hrpos c (hCsA hc))
      have h1 : ¬ dist x c ≤ r x + 10 * r c := fun h' => hcF (((hF x hx).1 c).2 ⟨hc, h'⟩)
      have h2 := dist_triangle x y c
      rw [dist_comm x y] at h2
      have h3 := hr0 c
      linarith
    have hSloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → S y = ∑ c ∈ F x, ψ c y := by
      intro x hx y hy
      rw [hS]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      exact ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 (hψF x hx y hy c hc.1 h'), hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
    have hS1 : ∀ x, x ∉ A → 1 ≤ S x := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hCscov x hx
      have hcF : c ∈ F x := ((hF x hx).1 c).2 ⟨hc, by linarith [hr0 x, hr0 c]⟩
      rw [hSloc x hx x (by rw [dist_self]; exact hrpos x hx)]
      calc (1 : ℝ) = ψ c x := (hψone c x (hrpos c (hCsA hc)) hxc.le).symm
        _ ≤ ∑ c ∈ F x, ψ c x := Finset.single_le_sum (fun c _ => hψ0 c x) hcF
    have hSc : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := by
      intro x hx
      refine (ContDiff.contDiffAt (ContDiff.sum (s := F x) fun c _ => hψs c)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hSloc x hx y hy
    have hnotA : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
      intro x hx y hy hyA
      have h1 := infDist_le_dist_of_mem (x := x) hyA
      rw [dist_comm] at h1
      linarith [hrd x, hr0 x]
    -- The partition of unity `φ c = ψ c / S` on `Aᶜ`.
    obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n → ℝ, ∀ c y, φ c y = ψ c y / S y := ⟨_, fun _ _ => rfl⟩
    have hφcd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (φ c) x := by
      intro c x hx
      rw [show φ c = ψ c / S from funext (hφ c)]
      exact (hψs c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
    have hφ0 : ∀ c y, y ∉ A → 0 ≤ φ c y := fun c y hy => by
      rw [hφ]; exact div_nonneg (hψ0 c y) (le_trans zero_le_one (hS1 y hy))
    have hφsum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ F x, φ c y = 1 := by
      intro x hx y hy
      simp only [hφ]
      rw [← Finset.sum_div, ← hSloc x hx y hy]
      exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hnotA x hx y hy))))
    have hφF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → φ c y = 0 := by
      intro x hx y hy c hc hcF
      rw [hφ, hψF x hx y hy c hc hcF, zero_div]
    have hφdsum : ∀ x, x ∉ A → ∑ c ∈ F x, fderiv ℝ (φ c) x = 0 := by
      intro x hx
      have heq : (fun y => ∑ c ∈ F x, φ c y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
        exact hφsum x hx y hy
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      rwa [fderiv_fun_const, Pi.zero_apply, fderiv_fun_sum fun c _ =>
        (hφcd c x hx).differentiableAt one_ne_zero] at h1
    -- `‖Dφ_c‖ ≤ ‖Dψ_c‖ + ‖DS‖` off `A` (quotient rule, `S ≥ 1`, `0 ≤ ψ_c ≤ 1`).
    have hφd : ∀ c x, x ∉ A → ‖fderiv ℝ (φ c) x‖ ≤ ‖fderiv ℝ (ψ c) x‖ + ‖fderiv ℝ S x‖ := by
      intro c x hx
      have hS1x := hS1 x hx
      have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
      have hb := ((hψs c).differentiable one_ne_zero x).hasFDerivAt
      have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
      have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
      have hder : fderiv ℝ (φ c) x =
          ψ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (ψ c) x := by
        rw [show φ c = fun y => ψ c y * ((fun t : ℝ => t⁻¹) ∘ S) y from
          funext fun y => by rw [hφ, div_eq_mul_inv]; rfl]
        exact (hb.fun_mul hi).fderiv
      have hp0 := hψ0 c x
      have hp1 : ψ c x ≤ 1 := by rw [hψ]; exact hβ1 _
      have hsi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
      have hsi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
      rw [hder]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg hp0,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), add_comm]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hsi)
        (mul_le_of_le_one_left (by positivity) hp1 |>.trans (mul_le_of_le_one_left (norm_nonneg _) hsi2))
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
        ∀ x, x ∉ A → ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ M / r x := by
      refine ⟨(N + 1) * (N * (2 * L)), by positivity, fun x hx => ?_⟩
      have hrx := hrpos x hx
      have hb : ∀ c ∈ F x, ‖fderiv ℝ (ψ c) x‖ ≤ 2 * L / r x := by
        intro c hc
        have hc' := ((hF x hx).1 c).1 hc
        have hrc := hrpos c (hCsA hc'.1)
        refine (hψd c x hrc).trans ?_
        rw [div_le_div_iff₀ hrc hrx]
        calc (L : ℝ) * r x ≤ L * (2 * r c) :=
              mul_le_mul_of_nonneg_left (by linarith [(hcomp x c hc'.2).1]) L.2
          _ = 2 * L * r c := by ring
      have hN' : ((F x).card : ℝ) ≤ N := by exact_mod_cast (hF x hx).2
      have hb0 : (0 : ℝ) ≤ 2 * L / r x := div_nonneg (by positivity) hrx.le
      have hSd : ‖fderiv ℝ S x‖ ≤ N * (2 * L / r x) := by
        have heq : S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, ψ c y := by
          filter_upwards [ball_mem_nhds x hrx] with y hy
          exact hSloc x hx y hy
        rw [heq.fderiv_eq, fderiv_fun_sum fun c _ => (hψs c).differentiable one_ne_zero x]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hN' hb0
      calc ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, (2 * L / r x + N * (2 * L / r x)) :=
            Finset.sum_le_sum fun c hc => (hφd c x hx).trans (add_le_add (hb c hc) hSd)
        _ = (F x).card * ((N + 1) * (2 * L / r x)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ N * ((N + 1) * (2 * L / r x)) := mul_le_mul_of_nonneg_right hN' (by positivity)
        _ = (N + 1) * (N * (2 * L)) / r x := by ring
    -- Nearest-point anchors and the affine jets `Q a y = h a + D a (y - a)`.
    obtain ⟨anc, hancA, hancd⟩ : ∃ anc : Rn n → Rn n, (∀ x, anc x ∈ A) ∧
        ∀ x, dist x (anc x) = infDist x A := by
      choose anc hanc using fun x => hA.exists_infDist_eq_dist hne x
      exact ⟨anc, fun x => (hanc x).1, fun x => (hanc x).2.symm⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Rn n → Rn n → ℝ, ∀ a y, Q a y = h a + (D a y - D a a) :=
      ⟨_, fun _ _ => rfl⟩
    have hQs : ∀ a, ContDiff ℝ 1 (Q a) := by
      intro a
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact contDiff_const.add ((D a).contDiff.sub contDiff_const)
    have hQd : ∀ a y, HasFDerivAt (Q a) (D a) y := by
      intro a y
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact ((D a).hasFDerivAt.sub_const _).const_add _
    have hQsub : ∀ a b y,
        |Q b y - Q a y| ≤ |h b - h a - D a (b - a)| + ‖D b - D a‖ * ‖y - b‖ := by
      intro a b y
      have e1 : Q b y - Q a y = (h b - h a - D a (b - a)) + (D b - D a) (y - b) := by
        rw [hQ, hQ]; simp only [map_sub, sub_apply]; ring
      rw [e1]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      have := (D b - D a).le_opNorm (y - b)
      rwa [Real.norm_eq_abs] at this
    have hancF : ∀ x, x ∉ A → ∀ c ∈ F x, dist x (anc c) ≤ 2 * infDist x A := by
      intro x hx c hc
      have h1 := (hcomp x c (((hF x hx).1 c).1 hc).2).2.2
      have h2 := hrd x
      have h3 := infDist_le_infDist_add_dist (s := A) (x := c) (y := x)
      have h4 := dist_triangle x c (anc c)
      rw [hancd c] at h4
      rw [dist_comm c x] at h3
      linarith [hr0 x]
    have hancP : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ F x, dist (anc c) a ≤ 3 * dist x a := by
      intro x hx a ha c hc
      have h1 := hancF x hx c hc
      have h2 := infDist_le_dist_of_mem (x := x) ha
      have h3 := dist_triangle (anc c) x a
      rw [dist_comm (anc c) x] at h3
      linarith
    -- The Whitney extension `g`.
    obtain ⟨g, hg⟩ : ∃ g : Rn n → ℝ, ∀ y,
        g y = if y ∈ A then h y else ∑ᶠ c ∈ Cs, φ c y * Q (anc c) y := ⟨_, fun _ => rfl⟩
    have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
    have hgloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx y hy
      rw [hg, ite_eq_right (hnotA x hx y hy)]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      refine ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 ?_, hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
      rw [hφF x hx y hy c hc.1 h', zero_mul]
    have hgev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hgloc x hx y hy
    have hgd : ∀ x, x ∉ A → HasFDerivAt g
        (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) x := by
      intro x hx
      refine HasFDerivAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact HasFDerivAt.fun_sum fun c _ =>
        ((hφcd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hQd (anc c) x)
    have hgcd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
      intro x hx
      refine ContDiffAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact ContDiffAt.sum fun c _ => (hφcd c x hx).mul (hQs (anc c)).contDiffAt
    -- `g` has derivative `D a` at each `a ∈ A`.
    have hgdA : ∀ a ∈ A, HasFDerivAt g (D a) a := by
      intro a ha
      refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun e he => ?_)
      obtain ⟨δ, hδ, -, hDd, hrem⟩ := hW a ha (e / 5) (by positivity)
      have haa : dist a a < δ := by rw [dist_self]; exact hδ
      filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
      have hxa : dist x a < δ / 4 := hx
      rw [hgA a ha]
      by_cases hxA : x ∈ A
      · rw [hgA x hxA, Real.norm_eq_abs]
        exact (hrem a ha haa x hxA (by linarith)).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      · have hx0 : dist x x < r x := by rw [dist_self]; exact hrpos x hxA
        have e1 : g x - h a - D a (x - a) = ∑ c ∈ F x, φ c x * (Q (anc c) x - Q a x) := by
          rw [hgloc x hxA x hx0]
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hφsum x hxA x hx0, one_mul, hQ a x,
            map_sub]
          ring
        rw [e1, Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ c ∈ F x, |φ c x * (Q (anc c) x - Q a x)| ≤ ∑ c ∈ F x, φ c x * (e * ‖x - a‖) := by
              refine Finset.sum_le_sum fun c hc => ?_
              rw [abs_mul, abs_of_nonneg (hφ0 c x hxA)]
              refine mul_le_mul_of_nonneg_left ?_ (hφ0 c x hxA)
              have hba := hancP x hxA a ha c hc
              have hxb : dist x (anc c) ≤ 2 * dist x a :=
                (hancF x hxA c hc).trans (by linarith [infDist_le_dist_of_mem (x := x) ha])
              have hbaδ : dist (anc c) a < δ := by linarith
              have h1 := hrem a ha haa (anc c) (hancA c) hbaδ
              have h2 := hDd (anc c) (hancA c) hbaδ
              rw [dist_eq_norm] at hba hxb
              refine (hQsub a (anc c) x).trans ?_
              calc |h (anc c) - h a - D a (anc c - a)| + ‖D (anc c) - D a‖ * ‖x - anc c‖
                  ≤ e / 5 * ‖anc c - a‖ + e / 5 * ‖x - anc c‖ :=
                    add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                _ ≤ e / 5 * (3 * ‖x - a‖) + e / 5 * (2 * ‖x - a‖) :=
                    add_le_add (mul_le_mul_of_nonneg_left hba (by positivity))
                      (mul_le_mul_of_nonneg_left hxb (by positivity))
                _ = e * ‖x - a‖ := by ring
          _ = e * ‖x - a‖ := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
    -- `Dg` is continuous at each `a ∈ A`.
    have hgcA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
      intro a ha
      rw [Metric.continuousAt_iff]
      intro e he
      obtain ⟨δ, hδ, hδ1, hDd, hrem⟩ := hW a ha (e / (2 * (1 + 700 * M))) (by positivity)
      set η := e / (2 * (1 + 700 * M)) with hη
      have hη0 : 0 < η := by positivity
      have hηM : η * (1 + 700 * M) = e / 2 := by rw [hη]; field_simp
      have hηM' := mul_nonneg hη0.le hM0
      refine ⟨δ / 4, by positivity, fun x hxa => ?_⟩
      rw [(hgdA a ha).fderiv, dist_eq_norm]
      by_cases hxA : x ∈ A
      · rw [(hgdA x hxA).fderiv]
        exact (hDd x hxA (by linarith)).trans_lt (by linarith)
      · have hrx := hrpos x hxA
        have hx0 : dist x x < r x := by rw [dist_self]; exact hrx
        have hbA : anc x ∈ A := hancA x
        have hdxa : infDist x A ≤ dist x a := infDist_le_dist_of_mem ha
        have hba : dist (anc x) a < δ := by
          have := dist_triangle (anc x) x a
          rw [dist_comm (anc x) x, hancd x] at this
          linarith
        have hd1 : infDist x A = 100 * r x := by
          rw [hr, min_eq_right (by linarith : infDist x A ≤ 1)]
          ring
        have hDb := hDd (anc x) hbA hba
        have e1 : (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) - D a =
            (∑ c ∈ F x, φ c x • (D (anc c) - D a)) +
              ∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x := by
          simp_rw [smul_sub, sub_smul]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_smul, ← Finset.smul_sum, hφsum x hxA x hx0, hφdsum x hxA, one_smul,
            smul_zero, sub_zero]
          abel
        rw [(hgd x hxA).fderiv, e1]
        have hT1 : ‖∑ c ∈ F x, φ c x • (D (anc c) - D a)‖ ≤ η := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖φ c x • (D (anc c) - D a)‖ ≤ ∑ c ∈ F x, φ c x * η :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_of_nonneg (hφ0 c x hxA)]
                  exact mul_le_mul_of_nonneg_left
                    (hDd (anc c) (hancA c) (by linarith [hancP x hxA a ha c hc])) (hφ0 c x hxA)
            _ = η := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
        have hT2 : ‖∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖ ≤
            700 * η * r x * (M / r x) := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖(Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖
              ≤ ∑ c ∈ F x, 700 * η * r x * ‖fderiv ℝ (φ c) x‖ :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_eq_abs]
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                  have hcaδ : dist (anc c) a < δ := by linarith [hancP x hxA a ha c hc]
                  have hxc := hancF x hxA c hc
                  have hcb : dist (anc c) (anc x) ≤ 3 * infDist x A := by
                    have := dist_triangle (anc c) x (anc x)
                    rw [dist_comm (anc c) x, hancd x] at this
                    linarith
                  have h1 := hrem (anc x) hbA hba (anc c) (hancA c) hcaδ
                  have h2 : ‖D (anc c) - D (anc x)‖ ≤ 2 * η := by
                    rw [← sub_sub_sub_cancel_right (D (anc c)) (D (anc x)) (D a)]
                    exact (norm_sub_le _ _).trans (by linarith [hDd (anc c) (hancA c) hcaδ])
                  rw [dist_eq_norm] at hcb hxc
                  refine (hQsub (anc x) (anc c) x).trans ?_
                  calc |h (anc c) - h (anc x) - D (anc x) (anc c - anc x)| +
                        ‖D (anc c) - D (anc x)‖ * ‖x - anc c‖
                      ≤ η * ‖anc c - anc x‖ + 2 * η * ‖x - anc c‖ :=
                        add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                    _ ≤ η * (3 * infDist x A) + 2 * η * (2 * infDist x A) :=
                        add_le_add (mul_le_mul_of_nonneg_left hcb hη0.le)
                          (mul_le_mul_of_nonneg_left hxc (by positivity))
                    _ = 700 * η * r x := by rw [hd1]; ring
            _ = 700 * η * r x * ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := by rw [Finset.mul_sum]
            _ ≤ 700 * η * r x * (M / r x) :=
                mul_le_mul_of_nonneg_left (hM x hxA) (mul_nonneg (by positivity) hrx.le)
        have hfin : 700 * η * r x * (M / r x) = 700 * (η * M) := by field_simp
        rw [hfin] at hT2
        exact (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨g, contDiff_one_iff_fderiv.2 ⟨fun x => ?_, continuous_iff_continuousAt.2 fun x => ?_⟩,
      hgA⟩
    · by_cases hx : x ∈ A
      · exact (hgdA x hx).differentiableAt
      · exact (hgd x hx).differentiableAt
    · by_cases hx : x ∈ A
      · exact hgcA x hx
      · exact (hgcd x hx).continuousAt_fderiv one_ne_zero
  intro f K hf ε hε
  have hfc : Continuous f := hf.continuous
  -- Rademacher: `f` is differentiable off a Borel null set.
  have hBm : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hB0 : volume {x | DifferentiableAt ℝ f x}ᶜ = 0 := by
    have h1 := hf.ae_differentiableAt (μ := (volume : Measure (Rn n)))
    rwa [ae_iff, ← Set.compl_ofPred] at h1
  -- Whitney quotients `σ k (x, L) = sup {|f (x + v) - f x - L v| / |v| : 0 < |v| < 1/(k+1)}`.
  obtain ⟨σ, hσ0, hσle, hσge, hσlsc⟩ : ∃ σ : ℕ → Rn n × (Rn n →L[ℝ] ℝ) → ℝ,
      (∀ k p, 0 ≤ σ k p) ∧
      (∀ (k : ℕ) p (v : Rn n), 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ σ k p * ‖v‖) ∧
      (∀ (k : ℕ) p (t : ℝ), 0 ≤ t → (∀ v : Rn n, 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ t * ‖v‖) → σ k p ≤ t) ∧
      ∀ k, LowerSemicontinuous (σ k) := by
    have hbdd : ∀ (k : ℕ) (p : Rn n × (Rn n →L[ℝ] ℝ)), BddAbove (range fun v :
        {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
          |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) := by
      intro k p
      refine ⟨K + ‖p.2‖, ?_⟩
      rintro _ ⟨v, rfl⟩
      rw [div_le_iff₀ v.2.1]
      have h1 := hf.dist_le_mul (p.1 + v) p.1
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1
      have h2 := p.2.le_opNorm v
      rw [Real.norm_eq_abs] at h2
      calc |f (p.1 + v) - f p.1 - p.2 v| ≤ |f (p.1 + v) - f p.1| + |p.2 v| := abs_sub _ _
        _ ≤ K * ‖(v : Rn n)‖ + ‖p.2‖ * ‖(v : Rn n)‖ := add_le_add h1 h2
        _ = (K + ‖p.2‖) * ‖(v : Rn n)‖ := by ring
    refine ⟨fun k p => ⨆ v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)},
      |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖, fun k p => Real.iSup_nonneg fun v =>
        div_nonneg (abs_nonneg _) (norm_nonneg _), fun k p v hv0 hv1 => ?_,
      fun k p t ht hle => Real.iSup_le (fun v => ?_) ht, fun k => ?_⟩
    · rw [← div_le_iff₀ hv0]
      exact le_ciSup (f := fun v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
        |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) (hbdd k p) ⟨v, hv0, hv1⟩
    · rw [div_le_iff₀ v.2.1]
      exact hle v v.2.1 v.2.2
    · refine lowerSemicontinuous_ciSup (hbdd k) fun v => Continuous.lowerSemicontinuous ?_
      exact (((hfc.comp (continuous_fst.add continuous_const)).sub (hfc.comp continuous_fst)).sub
        (continuous_snd.clm_apply continuous_const)).abs.div_const _
  have hσm : ∀ k, Measurable fun x => σ k (x, fderiv ℝ f x) := fun k =>
    (hσlsc k).measurable.comp (measurable_id.prodMk (measurable_fderiv ℝ f))
  have hσlim : ∀ x, DifferentiableAt ℝ f x →
      Tendsto (fun k => σ k (x, fderiv ℝ f x)) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro t ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 hx.hasFDerivAt.isLittleO (half_pos ht))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hρ
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ0 k _)]
    refine lt_of_le_of_lt (hσge k _ (t / 2) (by positivity) fun v hv0 hv1 => ?_) (half_lt_self ht)
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h1 := @hball (x + v) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rwa [add_sub_cancel_left, Real.norm_eq_abs] at h1
  -- Egorov on the balls `B(0, J)`, with summable tolerances.
  obtain ⟨δs, hδs0, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have hEg : ∀ J : ℕ, ∃ t ⊆ ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}, MeasurableSet t ∧
      volume t ≤ δs J ∧ TendstoUniformlyOn (fun k x => σ k (x, fderiv ℝ f x)) (fun _ => (0 : ℝ))
        atTop ((ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t) := fun J =>
    tendstoUniformlyOn_of_ae_tendsto (fun k => (hσm k).stronglyMeasurable) stronglyMeasurable_const
      (measurableSet_ball.inter hBm) ((measure_mono inter_subset_left).trans_lt
        measure_ball_lt_top).ne (Filter.Eventually.of_forall fun x hx => hσlim x hx.2)
      (by exact_mod_cast hδs0 J)
  choose t htsub _ htle htu using hEg
  -- An open `U` of measure `< ε` containing the bad set; `A = Uᶜ`.
  have hZ : volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J) < ε := by
    calc volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J)
        ≤ volume {x | DifferentiableAt ℝ f x}ᶜ + volume (⋃ J, t J) := measure_union_le _ _
      _ ≤ 0 + ∑' J, (δs J : ℝ≥0∞) :=
          add_le_add hB0.le ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum htle))
      _ < ε := by rw [zero_add]; exact hδsum
  obtain ⟨U, hZU, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ hZ
  -- Uniform first-order Taylor estimate on compact subsets of `Uᶜ`.
  have hunif : ∀ Q ⊆ Uᶜ, IsCompact Q → ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Q, ∀ v : Rn n, ‖v‖ < ρ → |f (x + v) - f x - fderiv ℝ f x v| ≤ s * ‖v‖ := by
    intro Q hQU hQ s hs
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball (0 : Rn n)
    obtain ⟨J, hJ⟩ := exists_nat_gt R
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 (htu J) s hs).exists
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hxU : x ∉ U := hQU hx
    have hxJ : x ∈ (ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t J :=
      ⟨⟨ball_subset_ball hJ.le (hR hx), Classical.byContradiction fun h' =>
        hxU (hZU (Or.inl h'))⟩, fun h' => hxU (hZU (Or.inr (mem_iUnion.2 ⟨J, h'⟩)))⟩
    have h1 := hk x hxJ
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hσ0 _ _)] at h1
    exact (hσle k (x, fderiv ℝ f x) v (norm_pos_iff.2 hv0) hv).trans
      (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  -- Whitney's hypothesis on `Uᶜ`, including continuity of `Df` there.
  have hW2 : ∀ a ∈ Uᶜ, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ Uᶜ, dist b a < δ → ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ e) ∧
      ∀ b ∈ Uᶜ, dist b a < δ → ∀ c ∈ Uᶜ, dist c a < δ →
        |f c - f b - fderiv ℝ f b (c - b)| ≤ e * ‖c - b‖ := by
    intro a ha e he
    obtain ⟨ρ, hρ, hρU⟩ := hunif (Uᶜ ∩ closedBall a 1) inter_subset_left
      ((isCompact_closedBall a 1).inter_left hUo.isClosed_compl) (e / 4) (by positivity)
    have hK : (0 : ℝ) ≤ K := K.2
    set δ := min (min 1 (ρ / 2)) (e * ρ / (8 * K + 1)) with hδ
    have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hδρ : δ ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hδe : δ ≤ e * ρ / (8 * K + 1) := min_le_right _ _
    have haQ : a ∈ Uᶜ ∩ closedBall a 1 := ⟨ha, mem_closedBall_self zero_le_one⟩
    refine ⟨δ, lt_min (lt_min one_pos (half_pos hρ)) (by positivity), hδ1, fun b hb hba => ?_,
      fun b hb hba c hc hca => ?_⟩
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hd : dist b a * (8 * K + 1) ≤ e * ρ := by
        rw [← le_div_iff₀ (by positivity)]; linarith
      refine ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hρ he.le
        (by norm_num) fun w hw1 hw2 => ?_
      rw [Real.norm_two] at hw1
      have h1 := hρU b hbQ w hw2
      have h2 := hρU a haQ w hw2
      have h3 := hf.dist_le_mul (b + w) (a + w)
      have h4 := hf.dist_le_mul b a
      rw [Real.dist_eq, dist_add_right] at h3
      rw [Real.dist_eq] at h4
      have h5 : e * ρ ≤ e * (2 * ‖w‖) := mul_le_mul_of_nonneg_left (by linarith) he.le
      have h6 : 0 ≤ dist b a := dist_nonneg
      rw [sub_apply, Real.norm_eq_abs]
      have e1 : fderiv ℝ f b w - fderiv ℝ f a w = (f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w) + (f (a + w) - f a - fderiv ℝ f a w) := by ring
      rw [e1]
      have := abs_add_le ((f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w)) (f (a + w) - f a - fderiv ℝ f a w)
      have := abs_sub ((f (b + w) - f (a + w)) - (f b - f a)) (f (b + w) - f b - fderiv ℝ f b w)
      have := abs_sub (f (b + w) - f (a + w)) (f b - f a)
      linarith
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hcb : ‖c - b‖ < ρ := by
        have := dist_triangle c a b
        rw [dist_comm a b, dist_eq_norm] at this
        linarith
      have h1 := hρU b hbQ (c - b) hcb
      rw [add_sub_cancel] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨g, hg, hgA⟩ := whitney Uᶜ f (fderiv ℝ f) hUo.isClosed_compl hW2
  refine ⟨g, hg, (measure_mono fun x hx => ?_).trans_lt hUε⟩
  by_contra hxU
  exact hx (hgA x hxU).symm

/-- **Countably rectifiable sets are covered by `C¹` pieces with injective differential** (Simon
Ch. 3, proof of Lemma 1.2, "only if").  If `M ⊆ ℝ^{n+ℓ}` is countably `n`-rectifiable, then up to a
Borel `Hⁿ`-null set `Z₀` it is covered by countably many images `G_k(B̆_{r_k}(c_k))` of open balls
under `C¹` maps `G_k : ℝⁿ → ℝ^{n+ℓ}` whose differential is injective on the ball and which satisfy
the lower Lipschitz bound `σ_k |b₁ - b₂| ≤ |G_k b₁ - G_k b₂|` there.
Proof: approximate the coordinates of the Lipschitz maps `F_j` of Definition 1.1 by `C¹` functions
(Simon Ch. 2, Theorem 1.5, `aetp_lipschitz_c1_approximation`); the set where `F_j` differs from all
approximations is Lebesgue-null, so its image is `Hⁿ`-null.  The image of the critical set of a `C¹`
map `G : ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null: on a piece where `G` is `η`-close to a non-injective linear `A`
with kernel vector `u`, `G` factors through the linear map `Θ = id - (1 - η) u ⊗ u` (which has
determinant `η`) via an `(‖A‖ + 1)`-Lipschitz map, so the Lipschitz image bound gives
`Hⁿ(G(piece)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(piece)`.  Near a point with injective differential, the
differential is antilipschitz and the mean value inequality gives the injectivity and the lower
Lipschitz bound on a small ball; Lindelöf selects countably many such balls, which are enumerated
(padded with an injective linear map). -/
theorem aetp_rectifiable_c1_piece_cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ Z₀ : Set (Amb n ℓ), MeasurableSet Z₀ ∧ (μHE[n] : Measure (Amb n ℓ)) Z₀ = 0 ∧ ∃ (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (r σ : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, 0 < r k) ∧ (∀ k, 0 < σ k) ∧ (∀ k, ∀ b ∈ ball (c k) (r k), Function.Injective (fderiv ℝ (G k) b)) ∧ (∀ k, ∀ b₁ ∈ ball (c k) (r k), ∀ b₂ ∈ ball (c k) (r k), σ k * ‖b₁ - b₂‖ ≤ ‖G k b₁ - G k b₂‖) ∧ M ⊆ Z₀ ∪ ⋃ k, G k '' ball (c k) (r k) := by
  intro n ℓ hn M hM
  obtain ⟨M₀, hM₀, F, hF, hMcov⟩ := hM
  choose K hK using hF
  have hHvol : (μHE[n] : Measure (Rn n)) = volume := EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- The map squeezing the direction of a unit vector `u` by the factor `η` has determinant `η`.
  have hdet : ∀ (u : Rn n), ‖u‖ = 1 → ∀ (η : ℝ),
      LinearMap.det ((ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u :
        Rn n →L[ℝ] Rn n) : Rn n →ₗ[ℝ] Rn n) = η := by
    intro u hu η
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - η) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    set P : Submodule ℝ (Rn n) := ℝ ∙ u
    have hP : ∀ k ∈ P, Θ k = η • k := by
      intro k hk
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hk
      rw [hΘ]
      have : inner ℝ u (c • u) = c := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
      rw [this, smul_smul, ← sub_smul]; congr 1; ring
    have hP' : ∀ k ∈ Pᗮ, Θ k = k := by
      intro k hk
      rw [hΘ]
      have : inner ℝ u k = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hk
      simp [this]
    let e := P.prodEquivOfIsCompl Pᗮ P.isCompl_orthogonal
    have hconj : e.symm.toLinearMap ∘ₗ (Θ : Rn n →ₗ[ℝ] Rn n) ∘ₗ e.symm.symm.toLinearMap =
        LinearMap.prodMap (η • LinearMap.id) LinearMap.id := by
      refine LinearMap.ext fun p => ?_
      obtain ⟨k, k'⟩ := p
      have hep : e.symm.symm (k, k') = (k : Rn n) + k' := rfl
      have hΘp : Θ ((k : Rn n) + k') = e (η • k, k') := by
        rw [map_add, hP k k.2, hP' k' k'.2]; rfl
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, hep, hΘp,
        LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
    rw [← LinearMap.det_conj (Θ : Rn n →ₗ[ℝ] Rn n) e.symm, hconj, LinearMap.det_prodMap,
      LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, finrank_span_singleton hu0]
    ring
  -- On a set where `H` is `η`-approximated by a non-injective linear map `A`, the `Hⁿ`-measure of
  -- the image is at most `(‖A‖ + 1)ⁿ η Lⁿ`.
  have key : ∀ (H : Rn n → Amb n ℓ) (A : Rn n →L[ℝ] Amb n ℓ) (s : Set (Rn n)) (L : ℝ) (η : ℝ≥0),
      ¬ Function.Injective A → ‖A‖ ≤ L → η ≤ 1 → ApproximatesLinearOn H A s η →
      (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤ ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
    intro H A s L η hA hAL hη1 hHA
    obtain ⟨v, hv0, hAv⟩ : ∃ v, v ≠ 0 ∧ A v = 0 := by
      by_contra h
      push Not at h
      exact hA ((injective_iff_map_eq_zero A).2 fun v hv => by_contra fun hne => h v hne hv)
    set u : Rn n := ‖v‖⁻¹ • v with hu_def
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
    have hAu : A u = 0 := by rw [hu_def, map_smul, hAv, smul_zero]
    have hL0 : 0 ≤ L := (norm_nonneg A).trans hAL
    have hη0 : (0 : ℝ) ≤ η := η.2
    have hη1' : (η : ℝ) ≤ 1 := hη1
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - (η : ℝ)) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - (η : ℝ)) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hΘn : ∀ x, ‖A x‖ + η * ‖x‖ ≤ (L + 1) * ‖Θ x‖ := by
      intro x
      set a := inner ℝ u x with ha
      have ha2 : a ^ 2 ≤ ‖x‖ ^ 2 := by
        have := abs_real_inner_le_norm u x
        rw [hu, one_mul] at this
        exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
      have hΘsq : ‖Θ x‖ ^ 2 = ‖x‖ ^ 2 - (1 - (η : ℝ) ^ 2) * a ^ 2 := by
        rw [hΘ, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      set w := x - a • u with hw
      have hwsq : ‖w‖ ^ 2 = ‖x‖ ^ 2 - a ^ 2 := by
        rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      have hAx : A x = A w := by rw [hw, map_sub, map_smul, hAu, smul_zero, sub_zero]
      have h1 : ‖w‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hwsq, hΘsq]; nlinarith [sq_nonneg (η : ℝ), sq_nonneg a]
      have h2 : (η : ℝ) * ‖x‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hΘsq, mul_pow]
        have : 0 ≤ 1 - (η : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left ha2 this]
      calc ‖A x‖ + η * ‖x‖ = ‖A w‖ + η * ‖x‖ := by rw [hAx]
        _ ≤ L * ‖w‖ + ‖Θ x‖ :=
          add_le_add ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hAL (norm_nonneg w))) h2
        _ ≤ L * ‖Θ x‖ + ‖Θ x‖ := by gcongr
        _ = (L + 1) * ‖Θ x‖ := by ring
    have hHΘ : ∀ x ∈ s, ∀ y ∈ s, ‖H x - H y‖ ≤ (L + 1) * ‖Θ x - Θ y‖ := by
      intro x hx y hy
      have h := hHA x hx y hy
      calc ‖H x - H y‖ = ‖(H x - H y - A (x - y)) + A (x - y)‖ := by rw [sub_add_cancel]
        _ ≤ ‖H x - H y - A (x - y)‖ + ‖A (x - y)‖ := norm_add_le _ _
        _ ≤ η * ‖x - y‖ + ‖A (x - y)‖ := by gcongr
        _ = ‖A (x - y)‖ + η * ‖x - y‖ := add_comm _ _
        _ ≤ (L + 1) * ‖Θ (x - y)‖ := hΘn (x - y)
        _ = (L + 1) * ‖Θ x - Θ y‖ := by rw [map_sub]
    classical
    let Φ : Rn n → Amb n ℓ := fun y => H (Function.invFunOn Θ s y)
    have hΦ : ∀ x ∈ s, Φ (Θ x) = H x := by
      intro x hx
      have hex : ∃ a ∈ s, Θ a = Θ x := ⟨x, hx, rfl⟩
      have h1 := Function.invFunOn_mem hex
      have h2 := Function.invFunOn_eq hex
      have := hHΘ _ h1 x hx
      rw [h2, sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have hΦlip : LipschitzOnWith (Real.toNNReal (L + 1)) Φ (Θ '' s) := by
      refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_
      obtain ⟨x₁, hx₁, rfl⟩ := hy₁
      obtain ⟨x₂, hx₂, rfl⟩ := hy₂
      rw [hΦ x₁ hx₁, hΦ x₂ hx₂, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
      exact hHΘ x₁ hx₁ x₂ hx₂
    have himg : H '' s = Φ '' (Θ '' s) := by
      rw [image_image]; exact image_congr fun x hx => (hΦ x hx).symm
    have hvolΘ : (μHE[n] : Measure (Rn n)) (Θ '' s) = (η : ℝ≥0∞) * volume s := by
      rw [hHvol]
      have := MeasureTheory.Measure.addHaar_image_linearMap volume (Θ : Rn n →ₗ[ℝ] Rn n) s
      rw [ContinuousLinearMap.coe_coe] at this
      rw [this, hdet u hu, abs_of_nonneg hη0, ENNReal.ofReal_coe_nnreal]
    calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (Φ '' (Θ '' s)) := by rw [himg]
      _ ≤ (Real.toNNReal (L + 1) : ℝ≥0∞) ^ n * μHE[n] (Θ '' s) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hΦlip
      _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [hvolΘ]; rfl
  -- The image of the critical set of a `C¹` map `ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null.
  have sard : ∀ H : Rn n → Amb n ℓ, ContDiff ℝ 1 H →
      (μHE[n] : Measure (Amb n ℓ)) (H '' {b | ¬ Function.Injective (fderiv ℝ H b)}) = 0 := by
    intro H hH
    set C := {b | ¬ Function.Injective (fderiv ℝ H b)}
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hCclosed : IsClosed C := by
      have : IsOpen {b | Function.Injective (fderiv ℝ H b)} :=
        ContinuousLinearMap.isOpen_injective.preimage hcont
      exact this.isClosed_compl
    have hcov : H '' C ⊆ ⋃ R : ℕ, H '' (C ∩ closedBall 0 R) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_closedBall_zero_iff.2 hR⟩, rfl⟩
    refine measure_mono_null hcov (measure_iUnion_null fun R => ?_)
    set s := C ∩ closedBall (0 : Rn n) R
    obtain ⟨L, hL⟩ :=
      (isCompact_closedBall (0 : Rn n) R).exists_bound_of_continuousOn hcont.continuousOn
    have hsmeas : MeasurableSet s := (hCclosed.inter isClosed_closedBall).measurableSet
    have hbound : ∀ η : ℝ≥0, η ≤ 1 → 0 < η → (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤
        ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
      intro η hη1 hη0
      rcases s.eq_empty_or_nonempty with hse | hsne
      · simp [hse]
      obtain ⟨t, A, hdisj, htm, hst, hap, hA⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H s (fderiv ℝ H)
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) (fun _ => η) (fun _ => hη0.ne')
      have hsU : s = ⋃ m, s ∩ t m := by rw [← inter_iUnion]; exact (inter_eq_left.2 hst).symm
      calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (⋃ m, H '' (s ∩ t m)) := by
            rw [← image_iUnion, ← hsU]
        _ ≤ ∑' m, (μHE[n] : Measure (Amb n ℓ)) (H '' (s ∩ t m)) := measure_iUnion_le _
        _ ≤ ∑' m, ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (s ∩ t m)) := by
            refine ENNReal.tsum_le_tsum fun m => ?_
            obtain ⟨y, hy, hAy⟩ := hA hsne m
            refine key H (A m) (s ∩ t m) L η ?_ ?_ hη1 (hap m)
            · rw [hAy]; exact hy.1
            · rw [hAy]; exact hL y hy.2
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (⋃ m, s ∩ t m)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, measure_iUnion]
            · intro i j hij
              exact (hdisj hij).mono inter_subset_right inter_subset_right
            · exact fun m => hsmeas.inter (htm m)
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [← hsU]
    have hV : volume s ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    have hc : ENNReal.ofReal (L + 1) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hlim := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hV)) (Or.inr hc)
    rw [zero_mul, mul_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hm)
    have := hbound ((m : ℝ≥0)⁻¹) (inv_le_one_of_one_le₀ (by exact_mod_cast hm))
      (inv_pos.2 (Nat.cast_pos.2 hm))
    rwa [ENNReal.coe_inv hm0, ENNReal.coe_natCast] at this
  -- Near a point with injective differential: injectivity and a lower Lipschitz bound on a ball.
  have loc : ∀ (H : Rn n → Amb n ℓ), ContDiff ℝ 1 H → ∀ b, Function.Injective (fderiv ℝ H b) →
      ∃ ρ > 0, ∃ σ > 0, (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ H b')) ∧
        ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖H b₁ - H b₂‖ := by
    intro H hH b hinj
    set D := fderiv ℝ H b
    obtain ⟨Ka, hKpos, hKa⟩ := (LinearMap.injective_iff_antilipschitz (D : Rn n →ₗ[ℝ] Amb n ℓ)).1 hinj
    have hKpos' : (0 : ℝ) < Ka := hKpos
    have hlow : ∀ x, ‖x‖ ≤ Ka * ‖D x‖ := by
      intro x
      have := hKa.le_mul_dist x 0
      simpa [dist_eq_norm] using this
    set s₀ : ℝ := (Ka : ℝ)⁻¹ with hs₀
    have hs₀pos : 0 < s₀ := inv_pos.2 hKpos'
    have hlow' : ∀ x, s₀ * ‖x‖ ≤ ‖D x‖ := by
      intro x
      rw [hs₀, inv_mul_le_iff₀ hKpos']
      exact hlow x
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    obtain ⟨ρ, hρ, hρD⟩ := Metric.continuous_iff.1 hcont b (s₀ / 2) (by positivity)
    have hnear : ∀ b' ∈ ball b ρ, ‖fderiv ℝ H b' - D‖ < s₀ / 2 := fun b' hb' => by
      rw [← dist_eq_norm]; exact hρD b' hb'
    refine ⟨ρ, hρ, s₀ / 2, by positivity, ?_, ?_⟩
    · intro b' hb' x y hxy
      by_contra hne
      have hz : x - y ≠ 0 := sub_ne_zero.2 hne
      have h0 : fderiv ℝ H b' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : ‖fderiv ℝ H b' (x - y) - D (x - y)‖ ≤ ‖fderiv ℝ H b' - D‖ * ‖x - y‖ :=
        (fderiv ℝ H b' - D).le_opNorm (x - y)
      rw [h0, zero_sub, norm_neg] at h1
      have h2 := hlow' (x - y)
      have h3 := hnear b' hb'
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 hz
      nlinarith
    · intro b₁ hb₁ b₂ hb₂
      have hmv : ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ ≤ s₀ / 2 * ‖b₁ - b₂‖ := by
        have := (convex_ball b ρ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (f := fun x => H x - D x) (C := s₀ / 2) (fun x _ => (hdiff x).sub D.differentiableAt)
          (fun x hx => ?_) hb₂ hb₁
        · simpa using this
        · rw [fderiv_fun_sub (hdiff x) D.differentiableAt, ContinuousLinearMap.fderiv]
          exact (hnear x hx).le
      have h2 := hlow' (b₁ - b₂)
      have h3 : ‖D (b₁ - b₂)‖ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := by
        rw [map_sub]
        calc ‖D b₁ - D b₂‖ = ‖(H b₁ - H b₂) - ((H b₁ - D b₁) - (H b₂ - D b₂))‖ := by
              congr 1; abel
          _ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := norm_sub_le _ _
      linarith
  -- A `C¹` map with injective differential at `0`, used to pad the enumeration.
  obtain ⟨G₀, hG₀, hG₀inj⟩ :
      ∃ G₀ : Rn n → Amb n ℓ, ContDiff ℝ 1 G₀ ∧ Function.Injective (fderiv ℝ G₀ 0) := by
    let p : Fin (n + ℓ) → Fin n := fun q => ⟨q % n, Nat.mod_lt _ hn⟩
    have hp : Function.Surjective p := fun i => ⟨Fin.castAdd ℓ i, Fin.ext (Nat.mod_eq_of_lt i.2)⟩
    let E₀ : Rn n →ₗ[ℝ] Amb n ℓ := (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℝ ℝ p ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    have hE₀ : Function.Injective E₀ :=
      (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.injective.comp
        ((LinearMap.funLeft_injective_of_surjective ℝ ℝ p hp).comp
          (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
    refine ⟨LinearMap.toContinuousLinearMap E₀, (LinearMap.toContinuousLinearMap E₀).contDiff, ?_⟩
    rw [ContinuousLinearMap.fderiv]
    exact hE₀
  -- `C¹` approximation of the coordinates of the Lipschitz maps `F j`.
  have happrox : ∀ (i j : ℕ) (q : Fin (n + ℓ)), ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧
      volume {x | (F j x).ofLp q ≠ g x} < ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i j q
    exact aetp_lipschitz_c1_approximation n hn (fun x => (F j x).ofLp q) _
      ((EuclideanSpace.proj q : Amb n ℓ →L[ℝ] ℝ).lipschitzWith.comp (hK j)) _
      (ENNReal.inv_pos.2 (by simp))
  choose g hg hgvol using happrox
  let G : ℕ → ℕ → Rn n → Amb n ℓ := fun i j x => WithLp.toLp 2 (fun q => g i j q x)
  have hGC1 : ∀ i j, ContDiff ℝ 1 (G i j) := fun i j => contDiff_euclidean.2 fun q => hg i j q
  -- The points where `F j` differs from every approximation form a Lebesgue-null set.
  let Z : ℕ → Set (Rn n) := fun j => ⋂ i, {x | F j x ≠ G i j x}
  have hZvol : ∀ j, volume (Z j) = 0 := by
    intro j
    have hle : ∀ i : ℕ, volume (Z j) ≤ ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by
      intro i
      calc volume (Z j) ≤ volume (⋃ q, {x | (F j x).ofLp q ≠ g i j q x}) := by
            refine measure_mono fun x hx => ?_
            have hx' : F j x ≠ G i j x := mem_iInter.1 hx i
            by_contra hcon
            simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
            exact hx' (PiLp.ext fun q => hcon q)
        _ ≤ ∑ q, volume {x | (F j x).ofLp q ≠ g i j q x} := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _q : Fin (n + ℓ), ((i : ℝ≥0∞) + 1)⁻¹ :=
            Finset.sum_le_sum fun q _ => (hgvol i j q).le
        _ = ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by simp
    have h0 : Tendsto (fun i : ℕ => ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.natCast_ne_top (n + ℓ)))
    exact le_antisymm (ge_of_tendsto' h0 hle) zero_le
  have hFZ : ∀ j, (μHE[n] : Measure (Amb n ℓ)) (F j '' Z j) = 0 := by
    intro j
    refine le_antisymm ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      n ((hK j).lipschitzOnWith)).trans ?_) zero_le
    rw [hHvol, hZvol j, mul_zero]
  -- Radii and lower Lipschitz constants around the points with injective differential.
  have hloc' : ∀ (i j : ℕ) (b : Rn n), ∃ ρ : ℝ, 0 < ρ ∧ ∃ σ : ℝ, 0 < σ ∧
      (Function.Injective (fderiv ℝ (G i j) b) →
        (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ (G i j) b')) ∧
          ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖G i j b₁ - G i j b₂‖) := by
    intro i j b
    by_cases hb : Function.Injective (fderiv ℝ (G i j) b)
    · obtain ⟨ρ, hρ, σ, hσ, h1, h2⟩ := loc _ (hGC1 i j) b hb
      exact ⟨ρ, hρ, σ, hσ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, one_pos, 1, one_pos, fun h => absurd h hb⟩
  choose ρ hρ σ hσ hρσ using hloc'
  obtain ⟨ρ₀, hρ₀, σ₀, hσ₀, hG₀ball, hG₀low⟩ := loc G₀ hG₀ 0 hG₀inj
  -- Lindelöf: countably many of these balls cover the non-critical set of each `G i j`.
  have hT : ∀ i j, ∃ T : Set (Rn n), T.Countable ∧
      ⋃ b ∈ T, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) =
        ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
    fun i j => TopologicalSpace.isOpen_iUnion_countable _ fun b => isOpen_ball.inter isOpen_const
  choose T hTc hTU using hT
  -- Enumerate the countably many pieces.
  let S : Set (ℕ × ℕ × Rn n) := ⋃ i, ⋃ j, (fun b => (i, j, b)) '' T i j
  have hS : S.Countable := countable_iUnion fun i => countable_iUnion fun j => (hTc i j).image _
  obtain ⟨e, he⟩ := (hS.insert (0, 0, 0)).exists_eq_range (insert_nonempty _ _)
  classical
  let valid : ℕ → Prop := fun k => Function.Injective (fderiv ℝ (G (e k).1 (e k).2.1) (e k).2.2)
  let Gk : ℕ → Rn n → Amb n ℓ := fun k => if valid k then G (e k).1 (e k).2.1 else G₀
  let ck : ℕ → Rn n := fun k => if valid k then (e k).2.2 else 0
  let rk : ℕ → ℝ := fun k => if valid k then ρ (e k).1 (e k).2.1 (e k).2.2 else ρ₀
  let σk : ℕ → ℝ := fun k => if valid k then σ (e k).1 (e k).2.1 (e k).2.2 else σ₀
  -- The exceptional set and its Borel null hull.
  let Zbad : Set (Amb n ℓ) := M₀ ∪ (⋃ j, F j '' Z j) ∪
    ⋃ i, ⋃ j, G i j '' {b | ¬ Function.Injective (fderiv ℝ (G i j) b)}
  have hZbad : (μHE[n] : Measure (Amb n ℓ)) Zbad = 0 :=
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hFZ))
      (measure_iUnion_null fun i => measure_iUnion_null fun j => sard _ (hGC1 i j))
  refine ⟨toMeasurable μHE[n] Zbad, measurableSet_toMeasurable _ _,
    by rw [measure_toMeasurable]; exact hZbad, Gk, ck, rk, σk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases h : valid k
    · simp only [Gk, h, ↓reduceIte]; exact hGC1 _ _
    · simp only [Gk, h, ↓reduceIte]; exact hG₀
  · intro k
    by_cases h : valid k
    · simp only [rk, h, ↓reduceIte]; exact hρ _ _ _
    · simp only [rk, h, ↓reduceIte]; exact hρ₀
  · intro k
    by_cases h : valid k
    · simp only [σk, h, ↓reduceIte]; exact hσ _ _ _
    · simp only [σk, h, ↓reduceIte]; exact hσ₀
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).1
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact hG₀ball
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).2
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact hG₀low
  · intro x hx
    rcases hMcov hx with hx0 | hx1
    · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inl hx0)))
    · obtain ⟨j, z, rfl⟩ := mem_iUnion.1 hx1
      by_cases hz : z ∈ Z j
      · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inr (mem_iUnion.2 ⟨j, mem_image_of_mem _ hz⟩))))
      · simp only [Z, mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
        obtain ⟨i, hi⟩ := hz
        by_cases hzC : Function.Injective (fderiv ℝ (G i j) z)
        · have hzU : z ∈ ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
            mem_iUnion.2 ⟨z, mem_ball_self (hρ i j z), hzC⟩
          rw [← hTU i j] at hzU
          simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop] at hzU
          obtain ⟨b, hbT, hzb, hbinj⟩ := hzU
          have hmem : (i, j, b) ∈ range e := by
            rw [← he]
            exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_image_of_mem _ hbT⟩⟩)
          obtain ⟨k, hk⟩ := hmem
          have hv : valid k := by simp only [valid, hk]; exact hbinj
          refine Or.inr (mem_iUnion.2 ⟨k, ?_⟩)
          simp only [Gk, ck, rk, hv, ↓reduceIte, hk]
          exact ⟨z, hzb, hi.symm⟩
        · exact Or.inl (subset_toMeasurable _ _
            (Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, ⟨z, hzC, hi.symm⟩⟩⟩)))
/-- Simon Ch. 3, 1.4 for an embedded `C¹` piece: if `G : ℝⁿ → ℝ^{n+ℓ}` is `C¹` with injective
derivative on `B = B̆_r(c)` and `σ|b₁ - b₂| ≤ |G(b₁) - G(b₂)|` on `B` (`σ > 0`), then `N = G(B)` is
Borel with `Hⁿ(N) < ∞`, and `DG(b)(ℝⁿ)` is the approximate tangent space of `N` at every `G(b)`.
Borel: Lusin–Souslin.  Finite: `G` is Lipschitz on `B`.  Tangent: by strict differentiability,
`‖G u - G v - DG(b)(u - v)‖ ≤ η‖u - v‖` near `b`; with `L = DG(b)`, `K = B_{R/σ}(0)` and
`Γ_λ(z) = λ⁻¹(G(b + λz) - G(b))`, the map `Φ = Γ_λ ∘ L⁻¹` is `(1 ± δ)`-bi-Lipschitz from `L(K)`
onto a piece of `η_{G(b),λ}(N)` containing `η_{G(b),λ}(N) ∩ {f ≠ 0}`; hence
`(1 - δ)ⁿ Φ_#(Hⁿ ⌞ L(K)) ≤ Hⁿ ⌞ Φ(L(K)) ≤ (1 + δ)ⁿ Φ_#(Hⁿ ⌞ L(K))`, and `|f ∘ Φ - f|` is
uniformly small on `L(K)`, while `Hⁿ ⌞ L(K)` carries `∫_P f dHⁿ`. -/
theorem aetp_c1_piece_approxTangent : ∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ) (c : Rn n) (r σ : ℝ), ContDiff ℝ 1 G → 0 < σ → (∀ b ∈ ball c r, Function.Injective (fderiv ℝ G b)) → (∀ b₁ ∈ ball c r, ∀ b₂ ∈ ball c r, σ * ‖b₁ - b₂‖ ≤ ‖G b₁ - G b₂‖) → MeasurableSet (G '' ball c r) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c r) < ⊤ ∧ ∀ b ∈ ball c r, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c r) (G b) (LinearMap.range (fderiv ℝ G b).toLinearMap) := by
  intro n ℓ G c r σ hG hσ hinj hlow
  have hGc : Continuous G := hG.continuous
  -- `G` is injective on `B` by the lower bound.
  have hGinj : InjOn G (ball c r) := by
    intro b₁ h₁ b₂ h₂ heq
    have h := hlow b₁ h₁ b₂ h₂
    rw [heq, sub_self, norm_zero] at h
    have h' : ‖b₁ - b₂‖ ≤ 0 := le_of_mul_le_mul_left (by rwa [mul_zero]) hσ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  -- (i) Borel: Lusin–Souslin.
  have hNmeas : MeasurableSet (G '' ball c r) :=
    measurableSet_ball.image_of_continuousOn_injOn hGc.continuousOn hGinj
  refine ⟨hNmeas, ?_, ?_⟩
  · -- (ii) `G` is Lipschitz on the convex set `B`, so `Hⁿ(G(B)) ≤ Cⁿ Lⁿ(B) < ∞`.
    obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
      (hG.continuous_fderiv one_ne_zero).continuousOn
    have hlip : LipschitzOnWith (Real.toNNReal C) G (ball c r) := by
      refine (convex_ball c r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        (fun x _ => hG.differentiable one_ne_zero x) fun x hx => ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact le_max_of_le_left (hC x (ball_subset_closedBall hx))
    calc (μHE[n] : Measure (Amb n ℓ)) (G '' ball c r)
        ≤ (Real.toNNReal C : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (ball c r) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
      _ < ⊤ := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) measure_ball_lt_top
  · -- (iii) the approximate tangent space at `G b`.
    intro b hb
    set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G b
    have hLinj : Function.Injective L := hinj b hb
    refine ⟨?_, fun f => ?_⟩
    · rw [LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj,
        finrank_euclideanSpace_fin]
    -- Strict differentiability at `b`, in the form of a local two-point estimate.
    have hstrict : HasStrictFDerivAt G L b := hG.contDiffAt.hasStrictFDerivAt one_ne_zero
    have hloc : ∀ η > 0, ∃ ρ > 0, ball b ρ ⊆ ball c r ∧
        ∀ u ∈ ball b ρ, ∀ v ∈ ball b ρ, ‖G u - G v - L (u - v)‖ ≤ η * ‖u - v‖ := by
      intro η hη
      obtain ⟨ρ₁, hρ₁, h₁⟩ :=
        Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hstrict.isLittleO hη)
      obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.isOpen_iff.1 isOpen_ball b hb
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (ball_subset_ball (min_le_right _ _)).trans h₂, ?_⟩
      intro u hu v hv
      have hu' : dist u b < ρ₁ := lt_of_lt_of_le (mem_ball.1 hu) (min_le_left _ _)
      have hv' : dist v b < ρ₁ := lt_of_lt_of_le (mem_ball.1 hv) (min_le_left _ _)
      exact @h₁ (u, v) (by rw [Prod.dist_eq]; exact max_lt hu' hv')
    -- The lower bound passes to the derivative: `σ‖v‖ ≤ ‖L v‖`.
    have hLlow : ∀ v, σ * ‖v‖ ≤ ‖L v‖ := by
      intro v
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨ρ, hρ, hρB, hρest⟩ := hloc (ε / (‖v‖ + 1)) (by positivity)
      set t : ℝ := ρ / (2 * (‖v‖ + 1)) with ht
      have ht0 : 0 < t := by positivity
      have htv : t * ‖v‖ < ρ := by
        rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        exact mul_lt_mul_of_pos_left (by linarith only [norm_nonneg v]) hρ
      have hu : b + t • v ∈ ball b ρ := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
        exact htv
      have e1 := hlow (b + t • v) (hρB hu) b hb
      have e2 := hρest (b + t • v) hu b (mem_ball_self hρ)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le] at e1 e2
      rw [map_smul] at e2
      have e3 : ‖G (b + t • v) - G b‖ ≤ t * ‖L v‖ + ε / (‖v‖ + 1) * (t * ‖v‖) := by
        calc ‖G (b + t • v) - G b‖ = ‖(G (b + t • v) - G b - t • L v) + t • L v‖ := by
              congr 1; abel
          _ ≤ ‖G (b + t • v) - G b - t • L v‖ + ‖t • L v‖ := norm_add_le _ _
          _ ≤ ε / (‖v‖ + 1) * (t * ‖v‖) + t * ‖L v‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht0.le]; exact add_le_add e2 le_rfl
          _ = t * ‖L v‖ + ε / (‖v‖ + 1) * (t * ‖v‖) := by ring
      have e4 : t * (σ * ‖v‖) ≤ t * (‖L v‖ + ε / (‖v‖ + 1) * ‖v‖) := by
        linarith only [e1, e3]
      have e5 : σ * ‖v‖ ≤ ‖L v‖ + ε / (‖v‖ + 1) * ‖v‖ := le_of_mul_le_mul_left e4 ht0
      have e6 : ε / (‖v‖ + 1) * ‖v‖ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
      linarith only [e5, e6]
    -- A linear left inverse `M` of `L`.
    obtain ⟨Mlin, hMlin⟩ :=
      LinearMap.exists_leftInverse_of_injective (L : Rn n →ₗ[ℝ] Amb n ℓ)
        (LinearMap.ker_eq_bot.2 hLinj)
    have hML : ∀ z, Mlin (L z) = z := fun z => by
      simpa using LinearMap.congr_fun hMlin z
    have hMc : Continuous Mlin := LinearMap.continuous_of_finiteDimensional Mlin
    -- Data of the test function `f`.
    have hfc : Continuous f := map_continuous f
    have hfcs : HasCompactSupport f := f.hasCompactSupport
    obtain ⟨R₀, hR₀⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    set R : ℝ := max R₀ 1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsupp : ∀ y, f y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      have h := hR₀ (subset_tsupport f hy)
      rw [mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    obtain ⟨Mf₀, hMf₀⟩ := hfc.bounded_above_of_compact_support hfcs
    set Mf : ℝ := max Mf₀ 0
    have hMf0 : 0 ≤ Mf := le_max_right _ _
    have hfM : ∀ y, |f y| ≤ Mf := fun y => by
      rw [← Real.norm_eq_abs]; exact (hMf₀ y).trans (le_max_left _ _)
    have hfuc : UniformContinuous f := hfcs.uniformContinuous_of_continuous hfc
    -- The compact parameter set `K` and the plane piece `A = L(K)`.
    set R' : ℝ := R / σ with hR'
    have hR'0 : 0 < R' := div_pos hR0 hσ
    set K : Set (Rn n) := closedBall 0 R' with hK
    set A : Set (Amb n ℓ) := L '' K
    have hKc : IsCompact K := isCompact_closedBall 0 R'
    have hAc : IsCompact A := hKc.image L.continuous
    have hAmeas : MeasurableSet A := hAc.isClosed.measurableSet
    have hAfin : (μHE[n] : Measure (Amb n ℓ)) A < ⊤ := by
      calc (μHE[n] : Measure (Amb n ℓ)) A
          ≤ (‖L‖₊ : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) K :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              L.lipschitzWith.lipschitzOnWith
        _ < ⊤ := by
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
            exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hKc.measure_lt_top
    set HA : ℝ := ((μHE[n] : Measure (Amb n ℓ)) A).toReal
    have hHA0 : 0 ≤ HA := ENNReal.toReal_nonneg
    -- The limit integral lives on `A`.
    have hI0 : ∫ y in (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)), f y ∂μHE[n] =
        ∫ y in A, f y ∂μHE[n] := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      · exact (Submodule.closed_of_finiteDimensional _).measurableSet
      · rintro _ ⟨z, -, rfl⟩
        exact LinearMap.mem_range_self (L : Rn n →ₗ[ℝ] Amb n ℓ) z
      · rintro y ⟨hyP, hyA⟩
        by_contra hfy
        obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hyP
        apply hyA
        refine ⟨v, ?_, rfl⟩
        rw [hK, mem_closedBall, dist_zero_right, hR', le_div_iff₀ hσ]
        have h1 := hsupp _ hfy
        have h2 := hLlow v
        simp only [ContinuousLinearMap.coe_coe] at h1
        linarith
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- Choice of the parameters.
    obtain ⟨τ, hτ, hτf⟩ := Metric.uniformContinuous_iff.1 hfuc (ε / (2 * (HA + 1))) (by positivity)
    have hκcont : Tendsto (fun d : ℝ => (((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n) (𝓝 0) (𝓝 0) := by
      have h1 : ContinuousAt (fun d : ℝ => (1 - d)⁻¹) 0 :=
        ((continuous_const.sub continuous_id).continuousAt).inv₀ (by norm_num)
      have h2 : ContinuousAt (fun d : ℝ => (((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n) 0 :=
        ((h1.pow n).sub continuousAt_const).mul (h1.pow n)
      simpa using h2.tendsto
    obtain ⟨d₀, hd₀, hd₀'⟩ := Metric.eventually_nhds_iff.1
      (hκcont.eventually (eventually_lt_nhds
        (show (0 : ℝ) < ε / (4 * (Mf + 1) * (HA + 1)) by positivity)))
    set δ : ℝ := min (d₀ / 2) (1 / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
    set κ : ℝ := ((1 - δ)⁻¹) ^ n
    have hκbound : (κ - 1) * κ < ε / (4 * (Mf + 1) * (HA + 1)) := by
      apply hd₀'
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd₀)
    have hκ1 : 1 ≤ κ :=
      one_le_pow₀ ((one_le_inv₀ (by linarith only [hδ1])).2 (by linarith only [hδ0]))
    set η : ℝ := min (δ * σ) (τ / (2 * (R' + 1)))
    have hη0 : 0 < η := lt_min (by positivity) (by positivity)
    obtain ⟨ρ, hρ, hρB, hρest⟩ := hloc η hη0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / (R' + 1) by positivity)] with lam hlam
    obtain ⟨hlam0, hlam1⟩ := hlam
    -- The rescaled parametrization `Γ` and the comparison map `Φ = Γ ∘ M`.
    set Γ : Rn n → Amb n ℓ := fun z => lam⁻¹ • (G (b + lam • z) - G b) with hΓ
    set Φ : Amb n ℓ → Amb n ℓ := fun y => Γ (Mlin y) with hΦ
    have hΦL : ∀ z, Φ (L z) = Γ z := fun z => by
      simp only [hΦ, hML]
    have hΦc : Continuous Φ := by
      simp only [hΦ, hΓ]
      fun_prop
    have hΦm : Measurable Φ := hΦc.measurable
    have hball : ∀ z ∈ K, b + lam • z ∈ ball b ρ := by
      intro z hz
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam0.le]
      have hz' : ‖z‖ ≤ R' := mem_closedBall_zero_iff.1 hz
      have h1 : lam * (R' + 1) < ρ := by rwa [lt_div_iff₀ (by positivity)] at hlam1
      calc lam * ‖z‖ ≤ lam * (R' + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only [hz']) hlam0.le
        _ < ρ := h1
    have hΓest : ∀ z ∈ K, ∀ w ∈ K, ‖Γ z - Γ w - L (z - w)‖ ≤ η * ‖z - w‖ := by
      intro z hz w hw
      have h := hρest _ (hball z hz) _ (hball w hw)
      have heq : Γ z - Γ w - L (z - w) =
          lam⁻¹ • (G (b + lam • z) - G (b + lam • w) - L (lam • (z - w))) := by
        simp only [hΓ, map_sub, map_smul, smul_sub, inv_smul_smul₀ hlam0.ne']
        abel
      rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam0.le)]
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam0.le] at h
      calc lam⁻¹ * ‖G (b + lam • z) - G (b + lam • w) - L (lam • (z - w))‖
          ≤ lam⁻¹ * (η * (lam * ‖z - w‖)) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hlam0.le)
        _ = η * ‖z - w‖ := by rw [mul_left_comm, inv_mul_cancel_left₀ hlam0.ne']
    -- `Φ` is `(1 ± δ)`-bi-Lipschitz on `A`.
    have hΦest : ∀ p ∈ A, ∀ q ∈ A, ‖(Φ p - Φ q) - (p - q)‖ ≤ δ * ‖p - q‖ := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [hΦL, hΦL, ← map_sub]
      calc ‖Γ z - Γ w - L (z - w)‖ ≤ η * ‖z - w‖ := hΓest z hz w hw
        _ ≤ (δ * σ) * ‖z - w‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ = δ * (σ * ‖z - w‖) := mul_assoc _ _ _
        _ ≤ δ * ‖L (z - w)‖ := mul_le_mul_of_nonneg_left (hLlow _) hδ0.le
    have hΦup : ∀ p ∈ A, ∀ q ∈ A, dist (Φ p) (Φ q) ≤ (1 + δ) * dist p q := by
      intro p hp q hq
      rw [dist_eq_norm, dist_eq_norm]
      have h := hΦest p hp q hq
      calc ‖Φ p - Φ q‖ = ‖(Φ p - Φ q - (p - q)) + (p - q)‖ := by congr 1; abel
        _ ≤ ‖Φ p - Φ q - (p - q)‖ + ‖p - q‖ := norm_add_le _ _
        _ ≤ (1 + δ) * ‖p - q‖ := by linarith only [h]
    have hΦlow : ∀ p ∈ A, ∀ q ∈ A, (1 - δ) * dist p q ≤ dist (Φ p) (Φ q) := by
      intro p hp q hq
      rw [dist_eq_norm, dist_eq_norm]
      have h := hΦest p hp q hq
      have h2 : ‖p - q‖ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := by
        calc ‖p - q‖ = ‖(Φ p - Φ q) - (Φ p - Φ q - (p - q))‖ := by congr 1; abel
          _ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := norm_sub_le _ _
      linarith only [h, h2]
    have hlip1 : LipschitzOnWith (Real.toNNReal (1 + δ)) Φ A := by
      apply LipschitzOnWith.of_dist_le_mul
      intro p hp q hq
      rw [Real.coe_toNNReal _ (by linarith only [hδ0])]
      exact hΦup p hp q hq
    have hΦinj : InjOn Φ A := by
      intro p hp q hq hpq
      have h := hΦlow p hp q hq
      rw [hpq, dist_self] at h
      have h' : dist p q ≤ 0 :=
        le_of_mul_le_mul_left (by rwa [mul_zero]) (by linarith only [hδ1] : (0 : ℝ) < 1 - δ)
      exact dist_le_zero.1 h'
    set Ψ : Amb n ℓ → Amb n ℓ := Function.invFunOn Φ A
    have hΨΦ : LeftInvOn Ψ Φ A := hΦinj.leftInvOn_invFunOn
    have hlip2 : LipschitzOnWith (Real.toNNReal (1 - δ)⁻¹) Ψ (Φ '' A) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      rw [hΨΦ hp, hΨΦ hq, Real.coe_toNNReal _ (inv_nonneg.2 (by linarith only [hδ1])),
        le_inv_mul_iff₀ (by linarith only [hδ1])]
      exact hΦlow p hp q hq
    -- The three measures and their comparison.
    set μ₃ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict A with hμ₃
    set μ₂ : Measure (Amb n ℓ) := μ₃.map Φ with hμ₂
    set μ₁ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) with hμ₁
    set κ₁ : ℝ≥0∞ := (Real.toNNReal (1 + δ) : ℝ≥0∞) ^ n with hκ₁
    set κ₂ : ℝ≥0∞ := (Real.toNNReal (1 - δ)⁻¹ : ℝ≥0∞) ^ n with hκ₂
    have hκ₁top : κ₁ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hκ₂top : κ₂ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hκ₁le : κ₁.toReal ≤ κ := by
      rw [hκ₁, ENNReal.toReal_pow, ENNReal.coe_toReal, Real.coe_toNNReal _ (by linarith only [hδ0])]
      apply pow_le_pow_left₀ (by linarith only [hδ0])
      rw [← one_div, le_div_iff₀ (by linarith only [hδ1])]
      linarith only [mul_self_nonneg δ]
    have hκ₂eq : κ₂.toReal = κ := by
      rw [hκ₂, ENNReal.toReal_pow, ENNReal.coe_toReal,
        Real.coe_toNNReal _ (inv_nonneg.2 (by linarith only [hδ1]))]
    have hμ12 : μ₁ ≤ κ₁ • μ₂ := by
      rw [Measure.le_iff]
      intro S hS
      rw [Measure.smul_apply, smul_eq_mul, hμ₂, Measure.map_apply hΦm hS, hμ₁, hμ₃,
        Measure.restrict_apply hS, Measure.restrict_apply (hS.preimage hΦm), ← image_preimage_inter]
      exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hlip1.mono inter_subset_right)
    have hμ21 : μ₂ ≤ κ₂ • μ₁ := by
      rw [Measure.le_iff]
      intro S hS
      rw [Measure.smul_apply, smul_eq_mul, hμ₂, Measure.map_apply hΦm hS, hμ₁, hμ₃,
        Measure.restrict_apply hS, Measure.restrict_apply (hS.preimage hΦm)]
      have hT : Ψ '' (Φ '' (Φ ⁻¹' S ∩ A)) = Φ ⁻¹' S ∩ A :=
        (hΨΦ.mono inter_subset_right).image_image
      calc (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A)
          = (μHE[n] : Measure (Amb n ℓ)) (Ψ '' (Φ '' (Φ ⁻¹' S ∩ A))) := by rw [hT]
        _ ≤ κ₂ * (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hlip2.mono (image_mono inter_subset_right))
        _ = κ₂ * (μHE[n] : Measure (Amb n ℓ)) (S ∩ Φ '' A) := by rw [image_preimage_inter]
    have hμ₃fin : IsFiniteMeasure μ₃ := ⟨by rw [hμ₃, Measure.restrict_apply_univ]; exact hAfin⟩
    have hμ₂fin : IsFiniteMeasure μ₂ := Measure.isFiniteMeasure_map μ₃ Φ
    have hμ₁fin : IsFiniteMeasure μ₁ := ⟨by
      calc μ₁ univ ≤ (κ₁ • μ₂) univ := hμ12 univ
        _ < ⊤ := by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hκ₁top) (measure_lt_top μ₂ univ)⟩
    have hμ₃univ : μ₃.real univ = HA := by
      rw [measureReal_def, hμ₃, Measure.restrict_apply_univ]
    have hμ₂univ : μ₂.real univ = HA := by
      rw [measureReal_def, hμ₂, Measure.map_apply hΦm MeasurableSet.univ, preimage_univ,
        ← measureReal_def, hμ₃univ]
    -- Sandwich estimate for nonnegative bounded continuous functions.
    have hsand : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ y, 0 ≤ g y) → (∀ y, g y ≤ Mf) →
        |∫ y, g y ∂μ₁ - ∫ y, g y ∂μ₂| ≤ (κ - 1) * κ * (Mf * HA) := by
      intro g hgc hg0 hgM
      have hgb : ∀ y, ‖g y‖ ≤ Mf := fun y => by rw [Real.norm_of_nonneg (hg0 y)]; exact hgM y
      have hg1 : Integrable g μ₁ :=
        Integrable.of_bound hgc.aestronglyMeasurable Mf (ae_of_all _ hgb)
      have hg2 : Integrable g μ₂ :=
        Integrable.of_bound hgc.aestronglyMeasurable Mf (ae_of_all _ hgb)
      have ha0 : 0 ≤ ∫ y, g y ∂μ₂ := integral_nonneg hg0
      have hb0 : 0 ≤ ∫ y, g y ∂μ₁ := integral_nonneg hg0
      have haM : ∫ y, g y ∂μ₂ ≤ Mf * HA := by
        have h := norm_integral_le_of_norm_le_const (μ := μ₂) (ae_of_all _ hgb)
        rwa [Real.norm_of_nonneg ha0, hμ₂univ] at h
      have h1 : ∫ y, g y ∂μ₁ ≤ κ * ∫ y, g y ∂μ₂ := by
        calc ∫ y, g y ∂μ₁ ≤ ∫ y, g y ∂(κ₁ • μ₂) :=
              integral_mono_measure hμ12 (ae_of_all _ hg0) (hg2.smul_measure hκ₁top)
          _ = κ₁.toReal * ∫ y, g y ∂μ₂ := by rw [integral_smul_measure, smul_eq_mul]
          _ ≤ κ * ∫ y, g y ∂μ₂ := mul_le_mul_of_nonneg_right hκ₁le ha0
      have h2 : ∫ y, g y ∂μ₂ ≤ κ * ∫ y, g y ∂μ₁ := by
        calc ∫ y, g y ∂μ₂ ≤ ∫ y, g y ∂(κ₂ • μ₁) :=
              integral_mono_measure hμ21 (ae_of_all _ hg0) (hg1.smul_measure hκ₂top)
          _ = κ₂.toReal * ∫ y, g y ∂μ₁ := by rw [integral_smul_measure, smul_eq_mul]
          _ = κ * ∫ y, g y ∂μ₁ := by rw [hκ₂eq]
      have hk0 : 0 ≤ κ - 1 := sub_nonneg.2 hκ1
      have h3 : (κ - 1) * ∫ y, g y ∂μ₁ ≤ (κ - 1) * (κ * ∫ y, g y ∂μ₂) :=
        mul_le_mul_of_nonneg_left h1 hk0
      have h4 : (κ - 1) * κ * ∫ y, g y ∂μ₂ ≤ (κ - 1) * κ * (Mf * HA) :=
        mul_le_mul_of_nonneg_left haM (mul_nonneg hk0 (zero_le_one.trans hκ1))
      have h5 : (κ - 1) * ∫ y, g y ∂μ₂ ≤ (κ - 1) * κ * ∫ y, g y ∂μ₂ := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ1 ha0) hk0
        linarith only [this]
      rw [abs_le]
      constructor <;> linarith only [h1, h2, h3, h4, h5]
    -- The blown-up piece: `η_{G b, λ}(N) ∩ {f ≠ 0} ⊆ Φ(A) ⊆ η_{G b, λ}(N)`.
    have hNlam :
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G b) lam '' (G '' ball c r), f y ∂μHE[n] =
          ∫ y, f y ∂μ₁ := by
      rw [hμ₁]
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      · rw [Set.image_eq_preimage_of_inverse (g := fun y => G b + lam • y)
          (fun w => by
            simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
            rw [smul_inv_smul₀ hlam0.ne', add_sub_cancel])
          (fun y => by
            simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
            rw [add_sub_cancel_left, inv_smul_smul₀ hlam0.ne'])]
        exact hNmeas.preimage (continuous_const.add (continuous_const_smul lam)).measurable
      · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        rw [hΦL]
        exact ⟨G (b + lam • z), ⟨b + lam • z, hρB (hball z hz), rfl⟩, rfl⟩
      · rintro y ⟨⟨_, ⟨b', hb', rfl⟩, rfl⟩, hyA⟩
        by_contra hfy
        apply hyA
        have hy := hsupp _ hfy
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hlam0.le)] at hy
        have h2 := hlow b' hb' b hb
        have hz : ‖lam⁻¹ • (b' - b)‖ ≤ R' := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam0.le), hR', le_div_iff₀ hσ]
          calc lam⁻¹ * ‖b' - b‖ * σ = lam⁻¹ * (σ * ‖b' - b‖) := by ring
            _ ≤ lam⁻¹ * ‖G b' - G b‖ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hlam0.le)
            _ ≤ R := hy
        refine ⟨L (lam⁻¹ • (b' - b)), ⟨lam⁻¹ • (b' - b), mem_closedBall_zero_iff.2 hz, rfl⟩, ?_⟩
        rw [hΦL]
        simp only [hΓ, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul,
          mul_inv_cancel₀ hlam0.ne', one_smul, add_sub_cancel]
    -- `f ∘ Φ` is uniformly close to `f` on `A`.
    have hclose : ∀ y ∈ A, |f (Φ y) - f y| < ε / (2 * (HA + 1)) := by
      rintro _ ⟨z, hz, rfl⟩
      have h0K : (0 : Rn n) ∈ K := mem_closedBall_self hR'0.le
      have h := hΓest z hz 0 h0K
      have hΓ0 : Γ 0 = 0 := by simp only [hΓ, smul_zero, add_zero, sub_self]
      rw [hΓ0, sub_zero, sub_zero] at h
      have hzR : ‖z‖ ≤ R' := mem_closedBall_zero_iff.1 hz
      have hηR : η * R' < τ := by
        have h1 : η ≤ τ / (2 * (R' + 1)) := min_le_right _ _
        have h2 : τ / (2 * (R' + 1)) * R' < τ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left (by linarith only [hR'0]) hτ
        calc η * R' ≤ τ / (2 * (R' + 1)) * R' := mul_le_mul_of_nonneg_right h1 hR'0.le
          _ < τ := h2
      have hd : dist (Φ (L z)) (L z) < τ := by
        rw [hΦL, dist_eq_norm]
        calc ‖Γ z - L z‖ ≤ η * ‖z‖ := h
          _ ≤ η * R' := mul_le_mul_of_nonneg_left hzR hη0.le
          _ < τ := hηR
      have h' := hτf hd
      rwa [Real.dist_eq] at h'
    have hfi : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ → ∀ g : Amb n ℓ → ℝ, Continuous g →
        (∀ y, |g y| ≤ Mf) → Integrable g μ := fun μ _ g hgc hgM =>
      Integrable.of_bound hgc.aestronglyMeasurable Mf
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hgM y)
    have hE1 : |∫ y, f (Φ y) ∂μ₃ - ∫ y, f y ∂μ₃| ≤ ε / (2 * (HA + 1)) * HA := by
      rw [← integral_sub (hfi μ₃ hμ₃fin (fun y => f (Φ y)) (hfc.comp hΦc) fun y => hfM _)
        (hfi μ₃ hμ₃fin _ hfc hfM)]
      have h := norm_integral_le_of_norm_le_const (μ := μ₃) (f := fun y => f (Φ y) - f y)
        (C := ε / (2 * (HA + 1)))
        ((ae_restrict_iff' hAmeas).2 (ae_of_all _ fun y hy => by
          rw [Real.norm_eq_abs]; exact (hclose y hy).le))
      rwa [Real.norm_eq_abs, hμ₃univ] at h
    have hE2 : |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| ≤ 2 * ((κ - 1) * κ * (Mf * HA)) := by
      have hpm : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ →
          ∫ y, f y ∂μ = ∫ y, max (f y) 0 ∂μ - ∫ y, max (-f y) 0 ∂μ := by
        intro μ hμ
        rw [← integral_sub]
        · congr 1
          funext y
          rw [max_zero_sub_max_neg_zero_eq_self]
        · exact hfi μ hμ _ (hfc.max continuous_const) fun y => by
            rw [abs_of_nonneg (le_max_right _ _)]
            exact max_le ((le_abs_self _).trans (hfM y)) hMf0
        · exact hfi μ hμ _ (hfc.neg.max continuous_const) fun y => by
            rw [abs_of_nonneg (le_max_right _ _)]
            exact max_le ((neg_le_abs _).trans (hfM y)) hMf0
      have e1 := hsand (fun y => max (f y) 0) (hfc.max continuous_const) (fun y => le_max_right _ _)
        fun y => max_le ((le_abs_self _).trans (hfM y)) hMf0
      have e2 := hsand (fun y => max (-f y) 0) (hfc.neg.max continuous_const)
        (fun y => le_max_right _ _) fun y => max_le ((neg_le_abs _).trans (hfM y)) hMf0
      rw [hpm μ₁ hμ₁fin, hpm μ₂ hμ₂fin]
      calc |(∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₁) -
            (∫ y, max (f y) 0 ∂μ₂ - ∫ y, max (-f y) 0 ∂μ₂)|
          = |(∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (f y) 0 ∂μ₂) -
            (∫ y, max (-f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₂)| := by congr 1; ring
        _ ≤ |∫ y, max (f y) 0 ∂μ₁ - ∫ y, max (f y) 0 ∂μ₂| +
            |∫ y, max (-f y) 0 ∂μ₁ - ∫ y, max (-f y) 0 ∂μ₂| := abs_sub _ _
        _ ≤ 2 * ((κ - 1) * κ * (Mf * HA)) := by linarith only [e1, e2]
    have hmap : ∫ y, f y ∂μ₂ = ∫ y, f (Φ y) ∂μ₃ :=
      integral_map hΦm.aemeasurable hfc.aestronglyMeasurable
    -- Conclusion.
    rw [Real.dist_eq, hNlam, show (LinearMap.range (fderiv ℝ G b).toLinearMap : Set (Amb n ℓ)) =
      (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) from rfl, hI0]
    have hX0 : 0 ≤ (κ - 1) * κ := mul_nonneg (sub_nonneg.2 hκ1) (zero_le_one.trans hκ1)
    have hX : (κ - 1) * κ * (4 * (Mf + 1) * (HA + 1)) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at hκbound
    have hMH : Mf * HA ≤ (Mf + 1) * (HA + 1) := by
      calc Mf * HA ≤ Mf * HA + (Mf + HA + 1) :=
            le_add_of_nonneg_right (by linarith only [hMf0, hHA0])
        _ = (Mf + 1) * (HA + 1) := by ring
    have hfin1 : 2 * ((κ - 1) * κ * (Mf * HA)) ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left hMH hX0
      linarith only [this, hX]
    have hfin2 : ε / (2 * (HA + 1)) * HA < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith only [hε]
    calc |∫ y, f y ∂μ₁ - ∫ y in A, f y ∂μHE[n]|
        ≤ |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| + |∫ y, f y ∂μ₂ - ∫ y in A, f y ∂μHE[n]| :=
          abs_sub_le _ _ _
      _ = |∫ y, f y ∂μ₁ - ∫ y, f y ∂μ₂| + |∫ y, f (Φ y) ∂μ₃ - ∫ y, f y ∂μ₃| := by
          rw [hmap]
      _ < ε := by linarith only [hE1, hE2, hfin1, hfin2]
/-- **Blow-up integrals over a set of zero `n`-density vanish** (the error estimate in Simon Ch. 3,
proof of Theorem 1.6 `⇒`): if `Hⁿ(S ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0`, then
`∫_{η_{x,r}(S)} f dHⁿ → 0` as `r ↓ 0` for every `f ∈ C_c(ℝ^{n+ℓ}, ℝ)`, where
`η_{x,r}(y) = r⁻¹(y − x)`.  No measurability or finiteness of `S` is needed.

Simon's estimate, inline (SimonGMT's `Chapter04.hausdorff_blowUp_image` is outside the frozen
import closure).  Choose `R > 0` with `f = 0` off `B_R(0)` and `C` with `|f| ≤ C`.  For `r > 0`,
`η_{x,r}` is a translation followed by the dilation by `r⁻¹`, so `Hⁿ(η_{x,r}(T)) = r⁻ⁿ Hⁿ(T)`;
since `η_{x,r}⁻¹(B_R(0)) = B_{rR}(x)`, this gives
`Hⁿ(η_{x,r}(S) ∩ B_R(0)) = r⁻ⁿ Hⁿ(S ∩ B_{rR}(x)) = Rⁿ · Hⁿ(S ∩ B_{rR}(x)) / (rR)ⁿ → 0`.  Hence
`|∫_{η_{x,r}(S)} f dHⁿ| = |∫_{B_R(0)} f d(Hⁿ ⌞ η_{x,r}(S))| ≤ C Hⁿ(η_{x,r}(S) ∩ B_R(0)) → 0`. -/
theorem aetp_blowUp_integral_tendsto_zero_of_density_zero : ∀ (n ℓ : ℕ) (x : Amb n ℓ) (S : Set (Amb n ℓ)), Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → ∀ f : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ x S hS f
  -- `f` vanishes off `B_R(0)` and `|f| ≤ C`.
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  obtain ⟨R, hRpos, hf0⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, y ∉ closedBall (0 : Amb n ℓ) R → f y = 0 :=
    ⟨max R₀ 1, zero_lt_one.trans_le (le_max_right _ _), fun y hy => by
      by_contra hfy
      exact hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ (subset_tsupport _ hfy)))⟩
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  -- Scaling: `Hⁿ(η_{x,r}(T)) = ofReal(rⁿ)⁻¹ Hⁿ(T)` for `r > 0`.
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        (ENNReal.ofReal (r ^ n))⁻¹ * (μHE[n] : Measure (Amb n ℓ)) T := by
    intro r hr T
    have h := Measure.euclideanHausdorffMeasure_smul₀ (E := Amb n ℓ) n (inv_ne_zero hr.ne')
      ((IsometryEquiv.subRight x) '' T)
    rw [← Set.image_smul, Set.image_image,
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul] at h
    refine Eq.trans h ?_
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos (pow_pos hr n), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow,
      coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_pow]
  -- Ball identity: `η_{x,r}⁻¹(B_R(0)) = B_{rR}(x)` for `r > 0`.
  have hpre : ∀ r : ℝ, 0 < r →
      Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' closedBall 0 R = closedBall x (r * R) := by
    intro r hr
    ext y
    simp only [Set.mem_preimage, mem_closedBall_iff_norm, sub_zero,
      Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_le_iff₀ hr
  -- `Hⁿ(η_{x,r}(S) ∩ B_R(0)) = ofReal(Rⁿ) · Hⁿ(S ∩ B_{rR}(x)) / ofReal((rR)ⁿ) → 0` as `r ↓ 0`.
  have hmul : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hg : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ))
      (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (hS.comp hmul) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (R ^ n))
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hR' : ENNReal.ofReal (R ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRpos n)).ne'
    rw [Function.comp_apply, ← Set.image_inter_preimage, hpre r hr, hscale r hr, mul_pow,
      ENNReal.ofReal_mul (pow_nonneg hr.le n), ← mul_div_assoc, mul_comm (ENNReal.ofReal (R ^ n)),
      ENNReal.mul_div_mul_right _ _ hR' ENNReal.ofReal_ne_top, ENNReal.div_eq_inv_mul]
  -- `|∫_{η_{x,r}(S)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(S) ∩ B_R(0))` once the latter is finite.
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂(μHE[n] : Measure (Amb n ℓ))‖ ≤
        C * ((μHE[n] : Measure (Amb n ℓ))
          (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal := by
    filter_upwards [hg.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with r hr
    have h2 : ((μHE[n] : Measure (Amb n ℓ)).restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S)) (closedBall 0 R) =
        (μHE[n] : Measure (Amb n ℓ))
          (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) := by
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf0, ← h2]
    exact norm_setIntegral_le_of_norm_le_const (h2 ▸ hr) (fun y _ => hC y)
  have hlim : Tendsto (fun r : ℝ => C * ((μHE[n] : Measure (Amb n ℓ))
      (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hg).const_mul C
  exact squeeze_zero_norm' hbound hlim
/-- **Simon Ch. 3, Remark 1.5(2) / proof of Theorem 1.6 "⇒" at a single point** (locality of the
approximate tangent space): let `A, N ⊆ ℝ^{n+ℓ}` be Borel with `Hⁿ(A), Hⁿ(N) < ∞`, such that
`A \ N` and `N \ A` both have `n`-density `0` at `x`.  If `Q` is the approximate tangent space of
`N` at `x`, then it is also the approximate tangent space of `A` at `x`.

Simon's proof, with `M ↦ A`, `N_j ↦ N`, `M_j ↦ A ∩ N`.  For `r > 0` the blow-up `η_{x,r}` is a
homeomorphism with inverse `z ↦ x + r • z` that scales `Hⁿ` by `r⁻ⁿ`.  So every `f ∈ C_c` is
integrable on the images of `A ∩ N`, `A \ N` and `N \ A`, and additivity gives
`∫_{η_r(A)} f = ∫_{η_r(N)} f - ∫_{η_r(N \ A)} f + ∫_{η_r(A \ N)} f`.  As `r ↓ 0` the first term
tends to `∫_Q f` by hypothesis, and the two error terms tend to `0` by
`aetp_blowUp_integral_tendsto_zero_of_density_zero`. -/
theorem aetp_approxTangent_of_density_zero_symmDiff : ∀ (n ℓ : ℕ) (A N : Set (Amb n ℓ)) (x : Amb n ℓ) (Q : Submodule ℝ (Amb n ℓ)), MeasurableSet A → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) A < ⊤ → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((A \ N) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((N \ A) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x Q → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x Q := by
  intro n ℓ A N x Q hA hN hAμ hNμ hAN hNA hNQ
  -- Step 1: `finrank Q = n` is part of the hypothesis on `N`; fix a test function `f`.
  refine ⟨hNQ.1, fun f => ?_⟩
  -- Step 2: `∫_{η_r(N)} f - ∫_{η_r(N \ A)} f + ∫_{η_r(A \ N)} f → ∫_Q f - 0 + 0`.
  have hlim := ((hNQ.2 f).sub
    (Submission.aetp_blowUp_integral_tendsto_zero_of_density_zero n ℓ x (N \ A) hNA f)).add
    (Submission.aetp_blowUp_integral_tendsto_zero_of_density_zero n ℓ x (A \ N) hAN f)
  rw [sub_zero, add_zero] at hlim
  -- Step 3: it suffices to prove the decomposition identity `(∗)` for each fixed `r > 0`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- Step 4: `η_r` has the continuous inverse `g z = x + r • z`, so `η_r(S) = g⁻¹(S)`: images of
  -- Borel sets are Borel, and unions and disjointness pass to images.
  set g : Amb n ℓ → Amb n ℓ := fun z => x + r • z
  have hg : Continuous g := continuous_const.add (continuous_const_smul r)
  have himg : ∀ S : Set (Amb n ℓ), Poincare.SimonGMT.Chapter03.blowUpMap x r '' S = g ⁻¹' S := by
    intro S
    refine congrFun (image_eq_preimage_of_inverse (fun y => ?_) (fun z => ?_)) S
    · simp [g, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
    · simp [g, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
  -- Step 5: `Hⁿ(η_r(T)) = r⁻ⁿ Hⁿ(T)` (an isometric translation followed by a homothety), so
  -- `η_r` preserves finiteness of `Hⁿ`.
  have hshift : Isometry fun y : Amb n ℓ => y - x := by
    apply Isometry.of_dist_eq
    intro y z
    simp only [dist_eq_norm]
    congr 1
    abel
  have hfin : ∀ T : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) T < ⊤ →
      (μHE[n] : Measure (Amb n ℓ)) (g ⁻¹' T) < ⊤ := by
    intro T hT
    have himage : g ⁻¹' T =
        AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y : Amb n ℓ => y - x) '' T) := by
      rw [← himg, ← image_comp]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hT
  -- Step 6: `f` is bounded, hence integrable on every set of finite measure.
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hint : ∀ T : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) T < ⊤ →
      IntegrableOn f (g ⁻¹' T) (μHE[n] : Measure (Amb n ℓ)) := fun T hT =>
    Measure.integrableOn_of_bounded (hfin T hT).ne f.continuous.aestronglyMeasurable
      (ae_of_all _ hC)
  have hANμ : (μHE[n] : Measure (Amb n ℓ)) (A ∩ N) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hAμ
  have hAdNμ : (μHE[n] : Measure (Amb n ℓ)) (A \ N) < ⊤ := (measure_mono sdiff_subset).trans_lt hAμ
  have hNdAμ : (μHE[n] : Measure (Amb n ℓ)) (N \ A) < ⊤ := (measure_mono sdiff_subset).trans_lt hNμ
  -- Step 7: additivity over `A = (A ∩ N) ∪ (A \ N)` and `N = (A ∩ N) ∪ (N \ A)`; eliminating
  -- `∫_{η_r(A ∩ N)} f` gives `(∗)`.
  have hAsplit : g ⁻¹' A = g ⁻¹' (A ∩ N) ∪ g ⁻¹' (A \ N) := by
    rw [← preimage_union, inter_union_sdiff]
  have hNsplit : g ⁻¹' N = g ⁻¹' (A ∩ N) ∪ g ⁻¹' (N \ A) := by
    rw [← preimage_union, inter_comm A N, inter_union_sdiff]
  simp only [himg]
  rw [hAsplit, hNsplit,
    setIntegral_union ((disjoint_sdiff_right.mono_left inter_subset_right).preimage g)
      (hg.measurable (hA.diff hN)) (hint _ hANμ) (hint _ hAdNμ),
    setIntegral_union ((disjoint_sdiff_right.mono_left inter_subset_left).preimage g)
      (hg.measurable (hN.diff hA)) (hint _ hANμ) (hint _ hNdAμ)]
  ring
/-- **Simon Ch. 1, Upper Density Theorem 3.6** (cited fact (H2) of the a.e. tangent-plane proof),
in Mathlib's normalization `Hⁿ = μHE[n]`: if `A ⊆ ℝ^{n+ℓ}` is Borel and `ν(A) < ∞`, then
`ν(A ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0` for `Hⁿ`-a.e. `x ∉ A`.

Simon's proof, inline (SimonGMT's `Chapter01.ae_dimensionalUpperDensity_eq_zero_outside` is outside
the frozen import closure).  Fix `k` and let `Bad k` be the set of `x ∉ A` with
`ν(A ∩ B_r(x)) / rⁿ > k⁻¹` for arbitrarily small `r > 0`.  Given a closed `F ⊆ A` (closed inner
regularity of the finite measure `ν ⌞ A`) and a scale `ρ > 0`, each `x ∈ Bad k` has a radius
`r_x ∈ (0, ρ]` with `B_{r_x}(x) ∩ F = ∅` and `r_xⁿ ≤ k ν((A \ F) ∩ B_{r_x}(x))`.  The Vitali
covering lemma gives a disjoint, hence countable, subfamily `{B_{r_b}(b)}_{b ∈ u}` with
`Bad k ⊆ ⋃_{b ∈ u} B_{5 r_b}(b)`, so `Σ_b diam(B_{5 r_b}(b))ⁿ ≤ 10ⁿ k ν(A \ F)`.  Letting
`ρ → 0` and `ν(A \ F) → 0` gives `μH[n](Bad k) = 0`, hence `Hⁿ(Bad k) = 0`, and outside
`⋃_k Bad k` the quotient tends to `0`. -/
theorem aetp_upper_density_zero_ae : ∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), MeasurableSet A → ν A < ⊤ → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∉ A → Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν A hA hνA
  -- `Bad k`: points outside `A` whose density quotient exceeds `k⁻¹` at arbitrarily small radii.
  set Bad : ℕ → Set (Amb n ℓ) := fun k => {x | x ∉ A ∧ ∃ᶠ r in 𝓝[>] (0 : ℝ),
    (k : ℝ≥0∞)⁻¹ < ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)}
  -- Closed inner regularity of the finite measure `ν ⌞ A`.
  have : IsFiniteMeasure (ν.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hF : ∀ j : ℕ, ∃ F ⊆ A, IsClosed F ∧ ν (A \ F) < (j : ℝ≥0∞)⁻¹ := by
    intro j
    obtain ⟨F, hFA, hFc, hFlt⟩ := hA.exists_isClosed_sdiff_lt (μ := ν.restrict A)
      (measure_ne_top _ _) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
    refine ⟨F, hFA, hFc, ?_⟩
    rwa [Measure.restrict_apply (hA.diff hFc.measurableSet), inter_eq_left.2 sdiff_subset] at hFlt
  choose F hFA hFc hFν using hF
  -- Vitali covering of `Bad k` at scale `ρ`, avoiding a closed `G ⊆ A`.
  have hcover : ∀ (k : ℕ) (G : Set (Amb n ℓ)), G ⊆ A → IsClosed G → ∀ ρ : ℝ, 0 < ρ →
      ∃ (u : Set (Amb n ℓ)) (r : Amb n ℓ → ℝ), u.Countable ∧ (∀ b ∈ u, 0 < r b ∧ r b ≤ ρ) ∧
        Bad k ⊆ ⋃ b ∈ u, closedBall b (5 * r b) ∧
        ∑' b : u, ENNReal.ofReal (r b) ^ n ≤ k * ν (A \ G) := by
    intro k G hGA hGc ρ hρ
    have hpick : ∀ x ∈ Bad k, ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
        ENNReal.ofReal r ^ n ≤ k * ν ((A \ G) ∩ closedBall x r) := by
      rintro x ⟨hxA, hfreq⟩
      have hxG : x ∈ Gᶜ := fun hx => hxA (hGA hx)
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl x hxG
      obtain ⟨r, hlt, hr⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hρ))).exists
      refine ⟨r, hr.1, (hr.2.trans_le (min_le_right _ _)).le, ?_⟩
      have hsub : A ∩ closedBall x r = (A \ G) ∩ closedBall x r := by
        ext y
        constructor
        · rintro ⟨hyA, hyr⟩
          exact ⟨⟨hyA, fun hyG =>
            hball (closedBall_subset_ball (hr.2.trans_le (min_le_left _ _)) hyr) hyG⟩, hyr⟩
        · rintro ⟨⟨hyA, -⟩, hyr⟩
          exact ⟨hyA, hyr⟩
      rw [hsub] at hlt
      have hpos : ENNReal.ofReal (r ^ n) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact pow_pos hr.1 n
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hlt
      rw [← ENNReal.ofReal_pow hr.1.le]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Nat.cast_zero, ENNReal.inv_zero, ENNReal.top_mul hpos] at hlt
        exact absurd hlt not_top_lt
      · have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
        calc ENNReal.ofReal (r ^ n) = k * ((k : ℝ≥0∞)⁻¹ * ENNReal.ofReal (r ^ n)) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k), one_mul]
          _ ≤ k * ν ((A \ G) ∩ closedBall x r) := mul_le_mul_right hlt.le _
    choose! r hr0 hrρ hrν using hpick
    obtain ⟨u, huB, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Bad k) (fun x => x) r ρ
        hrρ 5 (by norm_num)
    have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
      ⟨b, Metric.ball_subset_interior_closedBall (mem_ball_self (hr0 b (huB hb)))⟩
    refine ⟨u, r, hucount, fun b hb => ⟨hr0 b (huB hb), hrρ b (huB hb)⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, hab⟩ := hucov a ha
      exact mem_biUnion hbu (hab (mem_closedBall_self (hr0 a ha).le))
    · calc ∑' b : u, ENNReal.ofReal (r b) ^ n
          ≤ ∑' b : u, (k : ℝ≥0∞) * ν ((A \ G) ∩ closedBall (b : Amb n ℓ) (r b)) :=
            ENNReal.tsum_le_tsum fun b => hrν b (huB b.2)
        _ = k * ∑' b : u, ν ((A \ G) ∩ closedBall (b : Amb n ℓ) (r b)) := ENNReal.tsum_mul_left
        _ = k * ν (⋃ b ∈ u, (A \ G) ∩ closedBall b (r b)) := by
            rw [measure_biUnion hucount (hudisj.mono fun b => inter_subset_right)
              fun b _ => (hA.diff hGc.measurableSet).inter measurableSet_closedBall]
        _ ≤ k * ν (A \ G) :=
            mul_le_mul_right (measure_mono (iUnion₂_subset fun b _ => inter_subset_left)) _
  -- `μH[n] (Bad k) = 0`: covers at scales `1/(j+1)` avoiding `F j`.
  have hnull : ∀ k : ℕ, (μH[n] : Measure (Amb n ℓ)) (Bad k) = 0 := by
    intro k
    choose u r hucount hur hcov hsum using fun j : ℕ =>
      hcover k (F j) (hFA j) (hFc j) (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    have hle := Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) (Bad k) (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (10 * (1 / ((j : ℝ) + 1)))) ?_
      (fun j (b : u j) => closedBall (b : Amb n ℓ) (5 * r j b)) ?_ ?_
    · have h1 : Tendsto (fun j : ℕ => (k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.natCast_ne_top k))
        rwa [mul_zero] at this
      have h2 : Tendsto (fun j : ℕ => (10 : ℝ≥0∞) ^ n * ((k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹)) atTop
          (𝓝 0) := by
        have h10 : (10 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
        have := ENNReal.Tendsto.const_mul h1 (Or.inr h10)
        rwa [mul_zero] at this
      refine nonpos_iff_eq_zero.1 (hle.trans ((liminf_le_liminf
        (Eventually.of_forall fun j => ?_)).trans h2.liminf_eq.le))
      calc ∑' b : u j, ediam (closedBall (b : Amb n ℓ) (5 * r j b)) ^ (n : ℝ)
          ≤ ∑' b : u j, (10 : ℝ≥0∞) ^ n * ENNReal.ofReal (r j b) ^ n := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            calc ediam (closedBall (b : Amb n ℓ) (5 * r j b)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (10 * r j b) ^ (n : ℝ) := by
                  refine ENNReal.rpow_le_rpow
                    (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) (Nat.cast_nonneg n)
                  have := dist_triangle_right x y b
                  rw [mem_closedBall] at hx hy
                  linarith
              _ = (10 : ℝ≥0∞) ^ n * ENNReal.ofReal (r j b) ^ n := by
                  rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul (by norm_num), mul_pow,
                    ENNReal.ofReal_ofNat]
        _ = (10 : ℝ≥0∞) ^ n * ∑' b : u j, ENNReal.ofReal (r j b) ^ n := ENNReal.tsum_mul_left
        _ ≤ (10 : ℝ≥0∞) ^ n * ((k : ℝ≥0∞) * (j : ℝ≥0∞)⁻¹) := by
            gcongr
            exact (hsum j).trans (mul_le_mul_right (hFν j).le _)
    · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10
      rw [mul_zero] at h0
      have h1 := ENNReal.tendsto_ofReal h0
      rwa [ENNReal.ofReal_zero] at h1
    · refine Eventually.of_forall fun j b => Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
      have := dist_triangle_right x y b
      have hb := (hur j b b.2).2
      rw [mem_closedBall] at hx hy
      linarith
    · refine Eventually.of_forall fun j x hx => ?_
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (hcov j hx)
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩
  -- `μHE[n] = c • μH[n]`, so `μH[n]`-null sets are `Hⁿ`-null.
  have hHE : ∀ s : Set (Amb n ℓ), (μH[n] : Measure (Amb n ℓ)) s = 0 →
      (μHE[n] : Measure (Amb n ℓ)) s = 0 := by
    intro s hs
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hs, smul_zero]
  rw [ae_iff]
  refine hHE _ (measure_mono_null ?_ (measure_iUnion_null hnull))
  intro x hx
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxA, hnt⟩ := hx
  rw [ENNReal.tendsto_nhds_zero] at hnt
  push Not at hnt
  obtain ⟨ε, hε, hfreq⟩ := hnt
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  exact mem_iUnion.2 ⟨k, hxA, hfreq.mono fun r hr => hk.trans hr⟩

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces, from the proof of
Theorem 1.6 "⇒"): if `A, N ⊆ ℝ^{n+ℓ}` are Borel with `Hⁿ(A), Hⁿ(N) < ∞` and `P(x) = T_x N` for
every `x ∈ N`, then `P(x) = T_x A` for `Hⁿ`-a.e. `x ∈ A ∩ N`.

The Upper Density Theorem (`aetp_upper_density_zero_ae` with `ν = Hⁿ`) applied to `A \ N` and to
`N \ A` gives `Hⁿ((A \ N) ∩ B_r(x)) / rⁿ → 0` and `Hⁿ((N \ A) ∩ B_r(x)) / rⁿ → 0` as `r ↓ 0` for
`Hⁿ`-a.e. `x` outside the respective set, hence for `Hⁿ`-a.e. `x ∈ A ∩ N`.  At such `x` the blow-ups
`η_{x,r}(A)` and `η_{x,r}(N)` differ by the images of these two sets, whose integrals vanish in the
limit, so `T_x A = T_x N = P(x)` (`aetp_approxTangent_of_density_zero_symmDiff`). -/
theorem aetp_approxTangent_ae_of_inter : ∀ (n ℓ : ℕ) (A N : Set (Amb n ℓ)) (P : Amb n ℓ → Submodule ℝ (Amb n ℓ)), MeasurableSet A → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) A < ⊤ → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → (∀ x ∈ N, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x (P x)) → ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)).restrict (A ∩ N), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n A x (P x) := by
  intro n ℓ A N P hA hN hAfin hNfin hP
  -- Upper density zero for `A \ N` and `N \ A` (Borel, of finite `Hⁿ` measure), with `ν = Hⁿ`.
  have hAN := Submission.aetp_upper_density_zero_ae n ℓ (μHE[n]) (A \ N) (hA.diff hN)
    ((measure_mono sdiff_subset).trans_lt hAfin)
  have hNA := Submission.aetp_upper_density_zero_ae n ℓ (μHE[n]) (N \ A) (hN.diff hA)
    ((measure_mono sdiff_subset).trans_lt hNfin)
  -- A point of `A ∩ N` lies in neither `A \ N` nor `N \ A`, so both limits hold
  -- `Hⁿ ⌞ (A ∩ N)`-a.e.
  filter_upwards [ae_restrict_mem (hA.inter hN), ae_restrict_of_ae hAN, ae_restrict_of_ae hNA]
    with x hx hxAN hxNA
  -- At such `x ∈ N`, `T_x N = P(x)` transfers to `A`.
  exact Submission.aetp_approxTangent_of_density_zero_symmDiff n ℓ A N x (P x) hA hN hAfin hNfin
    (hxAN fun h => h.2 hx.2) (hxNA fun h => h.2 hx.1) (hP x hx.2)
/-- **Simon Ch. 3, Remark 1.8(1)** (with the boundedness of Remark 1.5(3)).  Let `V = v(M, θ)` be a
rectifiable `n`-varifold in the open set `U`, `K ⊆ M` compact with `θ|K` continuous, `x ∈ K`, and
`P` the approximate tangent space of `K` at `x` (Ch. 3, 1.4).  If
`μ_V((M \ K) ∩ B_{Rλ}(x)) / λⁿ → 0` as `λ ↓ 0` for every `R > 0`, then `P` is the approximate
tangent space of `M` with respect to `θ` at `x` (Ch. 3, 1.7). -/
theorem aetp_weightedTangent_of_lusin_compact : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (K : Set (Amb n ℓ)) (x : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), IsCompact K → K ⊆ V.carrier → x ∈ K → ContinuousOn V.mult K → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n K x P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
  intro n ℓ U hU V K x P hK hKM hxK hθK hdens hT
  refine ⟨hT.1, fun f => ?_⟩
  -- Step 1: a closed ball `B_ρ(x) ⊆ U`, bounds for `f`, and the radius `R` of its support.
  have hxU : x ∈ U := V.carrier_subset (hKM hxK)
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ > 0, closedBall x ρ ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ y, ‖f y‖ ≤ C :=
    (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  -- A cutoff `g ∈ C_c` with `0 ≤ g ≤ 1` and `g = 1` on `B_R(0)`.
  obtain ⟨g₀, hg₀1, -, hg₀cs, hg₀01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Amb n ℓ) R)
    (isOpen_ball (x := (0 : Amb n ℓ)) (ε := R + 1)).isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith)))
  let g : CompactlySupportedContinuousMap (Amb n ℓ) ℝ := ⟨g₀, hg₀cs⟩
  have hg01 : ∀ y, g y ∈ Icc (0 : ℝ) 1 := hg₀01
  -- Step 2: `Hⁿ(K) < ∞`, since `θ ≥ θ(z₀) > 0` on `K` and `θ` is integrable on `K`.
  have hθKint : IntegrableOn V.mult K (μHE[n] : Measure (Amb n ℓ)) := by
    have h := V.integrableOn_mult K hK (hKM.trans V.carrier_subset)
    rwa [inter_eq_right.mpr hKM] at h
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hK.exists_isMinOn ⟨x, hxK⟩ hθK
  have hc : 0 < V.mult z₀ := V.mult_pos z₀ (hKM hz₀K)
  have hμK : (μHE[n] : Measure (Amb n ℓ)) K < ∞ := by
    have h1 : ∫⁻ _ in K, ENNReal.ofReal (V.mult z₀) ∂(μHE[n] : Measure (Amb n ℓ)) ≤
        ∫⁻ z in K, ‖V.mult z‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) := by
      apply setLIntegral_mono' hKmeas
      intro z hz
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal ((hz₀min hz).trans (le_abs_self _))
    rw [setLIntegral_const] at h1
    exact ENNReal.lt_top_of_mul_ne_top_right (h1.trans_lt hθKint.2).ne
      (ENNReal.ofReal_pos.mpr hc).ne'
  -- Step 3: change of variables for the blow-up `η_r = blowUpMap x r`.
  have hcont : ∀ r : ℝ, Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    intro r
    show Continuous fun y => r⁻¹ • (y - x)
    fun_prop
  have hemb : ∀ r : ℝ, 0 < r → MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap x r) :=
    fun r hr => ((Homeomorph.subRight x).trans
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))).measurableEmbedding
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        ENNReal.ofReal r⁻¹ ^ n * (μHE[n] : Measure (Amb n ℓ)) T := by
    intro r hr T
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y => y - x) '' T) := by
      rw [Set.image_image]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    have hiso : Isometry (fun y : Amb n ℓ => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hmap : ∀ r : ℝ, 0 < r → ∀ S : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
        ENNReal.ofReal r⁻¹ ^ n • ((μHE[n] : Measure (Amb n ℓ)).restrict S).map
          (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    intro r hr S
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (hcont r).measurable hA,
      Measure.restrict_apply ((hcont r).measurable hA), ← hscale r hr,
      inter_comm _ S, Set.image_inter_preimage, inter_comm]
  have hcv : ∀ r : ℝ, 0 < r → ∀ (S : Set (Amb n ℓ)) (G : Amb n ℓ → ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, G y ∂(μHE[n] : Measure (Amb n ℓ)) =
        r⁻¹ ^ n * ∫ z in S, G (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro r hr S G
    rw [hmap r hr S, integral_smul_measure, (hemb r hr).integral_map, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), smul_eq_mul]
  -- Step 4: `f ∘ η_r` vanishes off `B_{Rr}(x)`, and `g ∘ η_r = 1` on `B_{Rr}(x)`.
  have hnorm : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro r hr z
    show ‖r⁻¹ • (z - x)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hf0 : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ, R * r ≤ ‖z - x‖ →
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
    intro r hr z hz
    apply hfR
    rw [hnorm r hr z, le_inv_mul_iff₀ hr]
    linarith
  have hg1 : ∀ r : ℝ, 0 < r → ∀ z : Amb n ℓ, ‖z - x‖ ≤ R * r →
      g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 1 := by
    intro r hr z hz
    apply hg₀1
    rw [mem_closedBall, dist_zero_right, hnorm r hr z, inv_mul_le_iff₀ hr]
    linarith
  -- Step 5: integrability of the three integrands.
  have hfK : ∀ r : ℝ, IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) K
      (μHE[n] : Measure (Amb n ℓ)) := fun r =>
    Measure.integrableOn_of_bounded hμK.ne
      ((map_continuous f).comp (hcont r)).aestronglyMeasurable
      (M := Cf) (Eventually.of_forall fun z => hCf _)
  have hgK : ∀ r : ℝ, IntegrableOn (fun z => g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) K
      (μHE[n] : Measure (Amb n ℓ)) := fun r =>
    Measure.integrableOn_of_bounded hμK.ne
      ((map_continuous g).comp (hcont r)).aestronglyMeasurable
      (M := 1) (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (hg01 _).1]
        exact (hg01 _).2)
  have hhM : ∀ r : ℝ, 0 < r → R * r ≤ ρ →
      IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) V.carrier
        (μHE[n] : Measure (Amb n ℓ)) := by
    intro r hr hRr
    have hθint : IntegrableOn V.mult (closedBall x ρ)
        ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
      have h := V.integrableOn_mult (closedBall x ρ) (isCompact_closedBall x ρ) hρU
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact h
    have hind : (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) =
        (closedBall x ρ).indicator
          (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) := by
      funext z
      by_cases hz : z ∈ closedBall x ρ
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, hf0 r hr z ?_, zero_mul]
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        linarith
    rw [IntegrableOn, hind, integrable_indicator_iff measurableSet_closedBall]
    exact hθint.bdd_mul ((map_continuous f).comp (hcont r)).aestronglyMeasurable
      (Eventually.of_forall fun z => hCf _)
  -- Step 6: the splitting `∫_{η_r(M)} f θ(x + r ·) = θ(x) I₁ + I₂ + I₃`.
  have hdecomp : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, f y * V.mult (x + r • y)
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        V.mult x * (r⁻¹ ^ n * ∫ z in K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ))) +
        r⁻¹ ^ n * ∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z))
          ∂(μHE[n] : Measure (Amb n ℓ)) +
        r⁻¹ ^ n * ∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hRr : R * r ≤ ρ := by
      rw [lt_div_iff₀ hR] at hrρ
      linarith
    rw [hcv r hr0]
    have hback : ∀ z : Amb n ℓ, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := by
      intro z
      show x + r • (r⁻¹ • (z - x)) = z
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
    simp only [hback]
    have hint := hhM r hr0 hRr
    rw [← integral_inter_add_sdiff hKmeas hint, inter_eq_right.mpr hKM,
      integral_sub (hint.mono_set hKM) ((hfK r).const_mul (V.mult x)), integral_const_mul]
    ring
  -- Step 7: the main term converges by `T_x K = P`.
  have hT1 : Tendsto (fun r : ℝ => V.mult x * (r⁻¹ ^ n * ∫ z in K,
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))))
      (𝓝[>] 0) (𝓝 (V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)))) := by
    apply Tendsto.const_mul
    apply (hT.2 f).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hcv r hr K f
  -- Step 8: the oscillation term `I₂` tends to `0` by continuity of `θ|K` at `x`.
  have hT2 : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in K,
      (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
        V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ)))
      (𝓝[>] 0) (𝓝 0) := by
    set Lg := ∫ y in (P : Set (Amb n ℓ)), g y ∂(μHE[n] : Measure (Amb n ℓ))
    have hglim : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in K,
        g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ)))
        (𝓝[>] 0) (𝓝 Lg) := by
      apply (hT.2 g).congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hcv r hr K g
    have hgev := hglim.eventually_lt_const (lt_add_one Lg)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ Cf * ε' * (|Lg| + 1) < ε := by
      refine ⟨ε / (2 * (Cf * (|Lg| + 1) + 1)), by positivity, ?_⟩
      have hA : 0 ≤ Cf * (|Lg| + 1) := by positivity
      rw [show Cf * (ε / (2 * (Cf * (|Lg| + 1) + 1))) * (|Lg| + 1) =
          ε * (Cf * (|Lg| + 1)) / (2 * (Cf * (|Lg| + 1) + 1)) by ring,
        div_lt_iff₀ (by positivity)]
      nlinarith
    obtain ⟨δ, hδ, hθδ⟩ := Metric.continuousOn_iff.mp hθK x hxK ε' hε'0
    filter_upwards [hgev, Ioo_mem_nhdsGT (div_pos hδ hR)] with r hgr hr
    obtain ⟨hr0, hrδ⟩ := hr
    have hRr : R * r < δ := by
      rw [lt_div_iff₀ hR] at hrδ
      linarith
    have hbound : ‖∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
        V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ))‖ ≤
        ∫ z in K, Cf * ε' * g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
      apply norm_integral_le_of_norm_le ((hgK r).const_mul (Cf * ε'))
      apply ae_restrict_of_forall_mem hKmeas
      intro z hz
      have heq : f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) =
          f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (V.mult z - V.mult x) := by ring
      rw [heq, norm_mul]
      by_cases hzb : ‖z - x‖ ≤ R * r
      · rw [hg1 r hr0 z hzb, mul_one]
        have h1 : dist (V.mult z) (V.mult x) < ε' :=
          hθδ z hz (by rw [dist_eq_norm]; linarith)
        rw [dist_eq_norm] at h1
        exact mul_le_mul (hCf _) h1.le (norm_nonneg _) hCf0
      · rw [not_le] at hzb
        rw [hf0 r hr0 z hzb.le, norm_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hCf0 hε'0.le) (hg01 _).1
    rw [integral_const_mul] at hbound
    have hpow : 0 ≤ r⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hr0.le) n
    rw [dist_zero_right, norm_mul, Real.norm_of_nonneg hpow]
    calc r⁻¹ ^ n * ‖∫ z in K, (f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z -
          V.mult x * f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ∂(μHE[n] : Measure (Amb n ℓ))‖
        ≤ r⁻¹ ^ n * (Cf * ε' * ∫ z in K, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[n] : Measure (Amb n ℓ))) := mul_le_mul_of_nonneg_left hbound hpow
      _ = Cf * ε' * (r⁻¹ ^ n * ∫ z in K, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[n] : Measure (Amb n ℓ))) := by ring
      _ ≤ Cf * ε' * (|Lg| + 1) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCf0 hε'0.le)
          linarith [le_abs_self Lg]
      _ < ε := hε'
  -- Step 9: the term `I₃` over `M \ K` tends to `0` by the density hypothesis.
  have hT3 : Tendsto (fun r : ℝ => r⁻¹ ^ n * ∫ z in V.carrier \ K,
      f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂(μHE[n] : Measure (Amb n ℓ)))
      (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_iff_edist_tendsto_0]
    simp only [edist_zero_right]
    have hlim := ENNReal.Tendsto.const_mul (hdens R hR) (Or.inr (ENNReal.ofReal_ne_top (r := Cf)))
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hpt : ∀ᵐ z ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict (V.carrier \ K),
        ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun z => ENNReal.ofReal Cf * ENNReal.ofReal (V.mult z)) z := by
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem₀ V.nullMeasurableSet_carrier)] with z hz
      by_cases hzb : z ∈ closedBall x (R * r)
      · rw [indicator_of_mem hzb, enorm_mul, Real.enorm_of_nonneg (V.mult_pos z hz).le,
          ← ofReal_norm]
        gcongr
        exact hCf _
      · rw [mem_closedBall, dist_eq_norm, not_le] at hzb
        rw [hf0 r hr0 z hzb.le, zero_mul, enorm_zero]
        exact zero_le
    have hint : ‖∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
        ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ ≤
        ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) :=
      calc ‖∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
            ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ
          ≤ ∫⁻ z in V.carrier \ K, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ
            ∂(μHE[n] : Measure (Amb n ℓ)) := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ z in V.carrier \ K, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z‖ₑ
            ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
            rw [Measure.restrict_restrict_of_subset sdiff_subset]
        _ ≤ ∫⁻ z in V.carrier \ K, (closedBall x (R * r)).indicator
              (fun z => ENNReal.ofReal Cf * ENNReal.ofReal (V.mult z)) z
            ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := lintegral_mono_ae hpt
        _ = ENNReal.ofReal Cf * ∫⁻ z in (V.carrier \ K) ∩ closedBall x (R * r),
              ENNReal.ofReal (V.mult z) ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := by
            rw [lintegral_indicator measurableSet_closedBall,
              Measure.restrict_restrict measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, inter_comm (closedBall x (R * r))]
        _ ≤ ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) := by
            gcongr
            exact withDensity_apply_le _ _
    calc ‖r⁻¹ ^ n * ∫ z in V.carrier \ K, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) *
          V.mult z ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ
        = (ENNReal.ofReal (r ^ n))⁻¹ * ‖∫ z in V.carrier \ K,
            f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
            ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ := by
          rw [enorm_mul, Real.enorm_of_nonneg (pow_nonneg (inv_nonneg.mpr hr0.le) n), inv_pow,
            ENNReal.ofReal_inv_of_pos (pow_pos hr0 n)]
      _ ≤ (ENNReal.ofReal (r ^ n))⁻¹ *
          (ENNReal.ofReal Cf * V.weight ((V.carrier \ K) ∩ closedBall x (R * r))) := by
          gcongr
      _ = ENNReal.ofReal Cf * (V.weight ((V.carrier \ K) ∩ closedBall x (R * r)) /
          ENNReal.ofReal (r ^ n)) := by
          rw [div_eq_mul_inv]
          ring
  -- Step 10: conclusion.
  have hsum := (hT1.add hT2).add hT3
  rw [add_zero, add_zero] at hsum
  exact hsum.congr' (hdecomp.mono fun r hr => hr.symm)
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
/-- **Simon Ch. 3, Remark 1.8(1), first assertion** (Lusin exhaustion of a rectifiable varifold):
the carrier `M` of `V = v(M, θ)` is, up to an `Hⁿ`-null set, a countable union of compact sets
`K ⊆ M` of finite `Hⁿ`-measure on each of which `θ` is continuous.  Proof: pass to a Borel
representative `f` of `θ` and a Borel `G ⊆ M` of full measure on which `θ = f`; exhaust `U` by
compact sets `Q i`; the Borel pieces `B i k = G ∩ Q i ∩ {f > 1/(k+1)}` have finite `Hⁿ`-measure
because `θ` is integrable on `M ∩ Q i`; Lusin's theorem (Simon 1.17, proved inline through a
countable basis of `ℝ` and closed inner regularity of finite measures) gives closed, hence
compact, `C i k m ⊆ B i k` with `Hⁿ(B i k \ C i k m) < 1/m` on which `f = θ` is continuous. -/
theorem aetp_lusin_compact_exhaustion : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), ∃ K : ℕ → Set (Amb n ℓ), (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ V.carrier) ∧ (∀ m, ContinuousOn V.mult (K m)) ∧ (∀ m, (μHE[n] : Measure (Amb n ℓ)) (K m) < ⊤) ∧ (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ m, K m) = 0 := by
  intro n ℓ U hU V
  -- A Borel representative `f` of `θ`.
  set f : Amb n ℓ → ℝ := V.aemeasurable_mult.mk V.mult
  have hfm : Measurable f := V.aemeasurable_mult.measurable_mk
  have hfae : V.mult =ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier] f :=
    V.aemeasurable_mult.ae_eq_mk
  -- A Borel `G ⊆ M` of full `Hⁿ`-measure in `M` on which `θ = f`.
  obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfae)
  rw [Measure.restrict_apply hTm] at hT0
  set G : Set (Amb n ℓ) := M₁ \ T
  have hGm : MeasurableSet G := hM₁m.diff hTm
  have hGM : G ⊆ V.carrier := sdiff_subset.trans hM₁M
  have hGf : ∀ x ∈ G, V.mult x = f x := fun x hx => by_contra fun h => hx.2 (hTsub h)
  have hMG : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ G) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hM₁ae).2 hT0)
    by_cases hx₁ : x ∈ M₁
    · exact Or.inr ⟨by_contra fun h => hx.2 ⟨hx₁, h⟩, hx.1⟩
    · exact Or.inl ⟨hx.1, hx₁⟩
  -- Compact exhaustion `Q i` of `U`.
  set Q : ℕ → Set (Amb n ℓ) :=
    fun i => closedBall 0 (i : ℝ) ∩ {x | (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ}
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_infEDist)
  have hQU : ∀ i, Q i ⊆ U := by
    intro i x hx
    by_contra hxU
    have h0 : (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ := hx.2
    rw [infEDist_zero_of_mem (show x ∈ Uᶜ from hxU)] at h0
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i) (le_antisymm h0 bot_le)
  have hUQ : ∀ x ∈ U, ∃ i, x ∈ Q i := by
    intro x hx
    have h0 : infEDist x Uᶜ ≠ 0 :=
      (infEDist_pos_iff_notMem_closure.2 (by rw [hU.isClosed_compl.closure_eq]; exact fun h => h hx)).ne'
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt h0
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    refine ⟨max j k, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact hj.trans (Nat.cast_le.2 (le_max_left j k))
    · exact (ENNReal.inv_le_inv.2 (Nat.cast_le.2 (le_max_right j k))).trans hk.le
  -- Lusin's theorem (Simon 1.17) for `f` and a finite Borel measure.
  have lusin : ∀ (ν : Measure (Amb n ℓ)), IsFiniteMeasure ν → ∀ A : Set (Amb n ℓ), MeasurableSet A →
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε ∧ ContinuousOn f C := by
    intro ν hν A hA ε hε
    have : ν.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
    obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × ℚ)
    -- For each rational interval, closed sets inside the parts of `A` where `f` is in / not in it.
    have hsplit : ∀ q : ℚ × ℚ, ∃ F ⊆ A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F ∧
        ∃ F' ⊆ A \ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F' ∧ ν (A \ (F ∪ F')) ≤ δ q := by
      intro q
      have hP : MeasurableSet (A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.inter (hfm measurableSet_Ioo)
      have hN : MeasurableSet (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.diff (hfm measurableSet_Ioo)
      have hδ2 : (δ q : ℝ≥0∞) / 2 ≠ 0 :=
        (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos q).ne')).ne'
      obtain ⟨F, hFP, hFc, hF⟩ := hP.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      obtain ⟨F', hFN, hF'c, hF'⟩ := hN.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
      refine ⟨F, hFP, hFc, F', hFN, hF'c, ?_⟩
      calc ν (A \ (F ∪ F'))
          ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F ∪ (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') := by
            refine measure_mono fun x hx => ?_
            by_cases hfx : f x ∈ Ioo (q.1 : ℝ) q.2
            · exact Or.inl ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inr h)⟩
        _ ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F) + ν ((A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') :=
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
      obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show f x - e < f x by linarith)
      obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show f x < f x + e by linarith)
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
  -- The Borel pieces `B i k` have finite `Hⁿ`-measure.
  set B : ℕ → ℕ → Set (Amb n ℓ) := fun i k => G ∩ Q i ∩ {x | 1 / ((k : ℝ) + 1) < f x}
  have hBm : ∀ i k, MeasurableSet (B i k) := fun i k =>
    (hGm.inter (hQc i).isClosed.measurableSet).inter (measurableSet_lt measurable_const hfm)
  have hBfin : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k) < ⊤ := by
    intro i k
    have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hint : ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) < ⊤ :=
      Integrable.lintegral_lt_top (V.integrableOn_mult (Q i) (hQc i) (hQU i))
    have hle : ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k) ≤
        ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
      calc ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k)
          = ∫⁻ _ in B i k, ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in B i k, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            setLIntegral_mono' (hBm i k) fun x hx =>
              ENNReal.ofReal_le_ofReal (by rw [hGf x hx.1.1]; exact hx.2.le)
        _ ≤ ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
            lintegral_mono_set fun x hx => ⟨hGM hx.1.1, hx.1.2⟩
    exact ENNReal.lt_top_of_mul_ne_top_right (hle.trans_lt hint).ne (ENNReal.ofReal_pos.2 hc).ne'
  -- Lusin pieces `C i k m ⊆ B i k`.
  have hC : ∀ i k m : ℕ, ∃ C ⊆ B i k, IsClosed C ∧
      (μHE[n] : Measure (Amb n ℓ)) (B i k \ C) < (m : ℝ≥0∞)⁻¹ ∧ ContinuousOn f C := by
    intro i k m
    obtain ⟨C, hCB, hCc, hCμ, hCf⟩ := lusin ((μHE[n] : Measure (Amb n ℓ)).restrict (B i k))
      (isFiniteMeasure_restrict.2 (hBfin i k).ne) (B i k) (hBm i k) (m : ℝ≥0∞)⁻¹
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    refine ⟨C, hCB, hCc, ?_, hCf⟩
    rwa [Measure.restrict_apply ((hBm i k).diff hCc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hCμ
  choose C hCB hCc hCμ hCf using hC
  have hBnull : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k \ ⋃ m, C i k m) = 0 := by
    intro i k
    by_contra h
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm hm ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ m))).trans_lt
      (hCμ i k m))
  -- Enumerate the pieces.
  refine ⟨fun j => C (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
    (Nat.unpair (Nat.unpair j).2).2, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · exact (hQc _).of_isClosed_subset (hCc _ _ _) ((hCB _ _ _).trans fun x hx => hx.1.2)
  · exact (hCB _ _ _).trans fun x hx => hGM hx.1.1
  · exact (hCf _ _ _).congr fun x hx => hGf x (hCB _ _ _ hx).1.1
  · exact (measure_mono (hCB _ _ _)).trans_lt (hBfin _ _)
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMG
      (measure_iUnion_null fun i => measure_iUnion_null fun k => hBnull i k))
    by_cases hxG : x ∈ G
    · obtain ⟨i, hi⟩ := hUQ x (V.carrier_subset hx.1)
      have hfx : 0 < f x := by rw [← hGf x hxG]; exact V.mult_pos x hx.1
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hfx
      refine Or.inr (mem_iUnion₂.2 ⟨i, k, ⟨⟨hxG, hi⟩, hk⟩, fun hxC => ?_⟩)
      obtain ⟨m, hm⟩ := mem_iUnion.1 hxC
      refine hx.2 (mem_iUnion.2 ⟨Nat.pair i (Nat.pair k m), ?_⟩)
      simpa only [Nat.unpair_pair] using hm
    · exact Or.inl ⟨hx.1, hxG⟩
/-- **Simon Ch. 3, Theorem 1.9** (with Lemma 1.2, Theorem 1.6 and Remark 1.8(1)).  For a rectifiable
`n`-varifold `V = v(M, θ)` in an open `U ⊆ ℝ^{n+ℓ}`, the approximate tangent space of `M` with
respect to `θ` exists for `μ_V`-a.e. `x`, so `V.tangentProj x` is then the orthogonal projection
onto an `n`-dimensional subspace; and `x ↦ V.tangentProj x` is `μ_V`-a.e. strongly measurable.

`M` is covered up to an `Hⁿ`-null set by embedded `C¹` pieces `N_k = G_k(B̆_{r_k}(c_k))`, whose
approximate tangent plane at `G_k(b)` is `DG_k(b)(ℝⁿ)`, and exhausted up to an `Hⁿ`-null set by
compacts `K_m` on which `θ` is continuous.  For `Hⁿ`-a.e. `x ∈ K_m ∩ N_k`, locality of approximate
tangent planes gives `T_x K_m = P_k(x) := DG_k(b_k(x))(ℝⁿ)`, and the upper density theorem (for
`μ_V` and `W ∖ K_m`, `W ⊇ K_m` open with compact closure in `U`) gives
`μ_V((M ∖ K_m) ∩ B_{Rλ}(x)) = o(λⁿ)`, so `P_k(x)` is the weighted tangent plane at `x`.  As
`μ_V ≪ Hⁿ` and `μ_V(Mᶜ) = 0`, this holds `μ_V`-a.e.; by uniqueness, `V.tangentProj = p_{P_k(·)}`
`μ_V`-a.e. on `N_k`, and `p_{P_k(·)}` is continuous on `N_k` since `b_k` is Lipschitz there. -/
theorem rectifiableVarifold_ae_tangentProj_starProjection : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ MeasureTheory.AEStronglyMeasurable V.tangentProj V.weight := by
  intro n ℓ hn U hU V
  -- Lemma 1.2: `M ⊆ Z₀ ∪ ⋃ k, N k`, `Hⁿ(Z₀) = 0`, with embedded `C¹` pieces `N k`.
  obtain ⟨Z₀, -, hZ₀, G, c, r, σ, hG, -, hσ, hDG, hlow, hcover⟩ :=
    Submission.aetp_rectifiable_c1_piece_cover n ℓ hn V.carrier V.countablyRectifiable
  set N : ℕ → Set (Amb n ℓ) := fun k => G k '' ball (c k) (r k)
  have hpiece : ∀ k, MeasurableSet (N k) ∧ (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤ ∧
      ∀ y ∈ ball (c k) (r k), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k)
        (G k y) (LinearMap.range (fderiv ℝ (G k) y).toLinearMap) := fun k =>
    Submission.aetp_c1_piece_approxTangent n ℓ (G k) (c k) (r k) (σ k) (hG k) (hσ k) (hDG k)
      (hlow k)
  -- the parameter `b k x ∈ B̆_{r_k}(c_k)` of a point `x ∈ N k`
  obtain ⟨b, hb⟩ : ∃ b : ℕ → Amb n ℓ → Rn n,
      ∀ k, ∀ x ∈ N k, b k x ∈ ball (c k) (r k) ∧ G k (b k x) = x :=
    ⟨fun k => Function.invFunOn (G k) (ball (c k) (r k)),
      fun k x hx => ⟨Function.invFunOn_mem hx, Function.invFunOn_eq hx⟩⟩
  have hNtan : ∀ k, ∀ x ∈ N k, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x
      (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap) := by
    intro k x hx
    have h := (hpiece k).2.2 (b k x) (hb k x hx).1
    rwa [(hb k x hx).2] at h
  -- Remark 1.8(1): compacts `K m ⊆ M`, with `θ` continuous on `K m`, exhaust `M` up to a null set.
  obtain ⟨K, hKc, hKM, hθK, hKfin, hKnull⟩ := Submission.aetp_lusin_compact_exhaustion n ℓ U hU V
  have hfin : ∀ L : Set (Amb n ℓ), IsCompact L → L ⊆ U → V.weight L < ⊤ := by
    intro L hL hLU
    rw [RectifiableVarifold.weight, withDensity_apply _ hL.isClosed.measurableSet,
      Measure.restrict_restrict hL.isClosed.measurableSet, inter_comm]
    exact (V.integrableOn_mult L hL hLU).lintegral_lt_top
  -- For `Hⁿ`-a.e. `x ∈ K m ∩ N k`, `DG_k(b_k(x))(ℝⁿ)` is the weighted tangent plane at `x`.
  have hloc : ∀ m k, ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ K m → x ∈ N k →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap) := by
    intro m k
    obtain ⟨L, hLc, hKL, hLU⟩ :=
      exists_compact_between (hKc m) hU ((hKM m).trans V.carrier_subset)
    have hA : MeasurableSet (interior L \ K m) :=
      isOpen_interior.measurableSet.diff (hKc m).isClosed.measurableSet
    have hAL : interior L \ K m ⊆ L := fun y hy => interior_subset hy.1
    have hAfin : V.weight (interior L \ K m) < ⊤ := (measure_mono hAL).trans_lt (hfin L hLc hLU)
    have htan := Submission.aetp_approxTangent_ae_of_inter n ℓ (K m) (N k)
      (fun x => LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)
      (hKc m).isClosed.measurableSet (hpiece k).1 (hKfin m) (hpiece k).2.1 (hNtan k)
    rw [ae_restrict_iff' ((hKc m).isClosed.measurableSet.inter (hpiece k).1)] at htan
    filter_upwards [htan, Submission.aetp_upper_density_zero_ae n ℓ V.weight _ hA hAfin]
      with x hxtan hxdens hxK hxN
    refine Submission.aetp_weightedTangent_of_lusin_compact n ℓ U hU V (K m) x _ (hKc m) (hKM m)
      hxK (hθK m) (fun R hR => ?_) (hxtan ⟨hxK, hxN⟩)
    -- `μ_V((M ∖ K m) ∩ B_{Rt}(x)) ≤ μ_V((W ∖ K m) ∩ B_{Rt}(x)) = o(tⁿ)`, `W = interior L`
    have hd := hxdens fun h => h.2 hxK
    have hRr : Tendsto (fun t : ℝ => R * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2
        ⟨?_, eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => mul_pos hR ht⟩
      have h0 : Tendsto (fun t : ℝ => R * t) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hsub : ∀ᶠ t in 𝓝[>] (0 : ℝ), closedBall x (R * t) ⊆ interior L :=
      (hRr.mono_right nhdsWithin_le_nhds).eventually
        (eventually_closedBall_subset (isOpen_interior.mem_nhds (hKL hxK)))
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (R ^ n) *
        (V.weight ((interior L \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal ((R * t) ^ n)))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hd.comp hRr)
        (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ n) ≠ ⊤))
      rw [mul_zero] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hsub] with t ht
    have hMA : (V.carrier \ K m) ∩ closedBall x (R * t) ⊆
        (interior L \ K m) ∩ closedBall x (R * t) := fun y hy => ⟨⟨ht hy.2, hy.1.2⟩, hy.2⟩
    calc V.weight ((V.carrier \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal (t ^ n)
        ≤ V.weight ((interior L \ K m) ∩ closedBall x (R * t)) / ENNReal.ofReal (t ^ n) :=
          ENNReal.div_le_div_right (measure_mono hMA) _
      _ = ENNReal.ofReal (R ^ n) * (V.weight ((interior L \ K m) ∩ closedBall x (R * t)) /
            ENNReal.ofReal ((R * t) ^ n)) := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hR.le n), ENNReal.div_eq_inv_mul,
            ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
              (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (pow_pos hR n)).ne'
              ENNReal.ofReal_ne_top, one_mul]
  -- Off an `Hⁿ`-null set, each `x ∈ M` lies in some `N k`, and for every `k` with `x ∈ N k` the
  -- plane `DG_k(b_k(x))(ℝⁿ)` is the weighted tangent plane at `x`.
  have hgoodH : ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ V.carrier →
      (∀ k, x ∈ N k → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult x (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)) ∧
      ∃ k, x ∈ N k := by
    filter_upwards [ae_all_iff.2 fun m => ae_all_iff.2 fun k => hloc m k,
      measure_eq_zero_iff_ae_notMem.1 hZ₀, measure_eq_zero_iff_ae_notMem.1 hKnull]
      with x hx hxZ hxK hxM
    obtain ⟨m, hm⟩ : ∃ m, x ∈ K m := by
      by_contra h
      exact hxK ⟨hxM, fun h' => h (mem_iUnion.1 h')⟩
    refine ⟨fun k hk => hx m k hm hk, ?_⟩
    rcases hcover hxM with h | h
    · exact absurd h hxZ
    · exact mem_iUnion.1 h
  -- `μ_V ≪ Hⁿ` and `μ_V(Mᶜ) = 0`
  have hμM : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hμH : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)) :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hgood : ∀ᵐ x ∂V.weight, x ∈ V.carrier ∧
      (∀ k, x ∈ N k → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult x (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap)) ∧
      ∃ k, x ∈ N k := by
    filter_upwards [hμH.ae_le hgoodH, hμM] with x hx hxM
    exact ⟨hxM, hx hxM⟩
  -- A weighted tangent plane at `x ∈ M` is unique (`θ(x) > 0`), so it is the one in `tangentProj`.
  have hproj : ∀ x (Q : Submodule ℝ (Amb n ℓ)), x ∈ V.carrier →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x Q →
      V.tangentProj x = Q.starProjection := by
    intro x Q hxM hQ
    have h : ∃ P, Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult x P := ⟨Q, hQ⟩
    have hP : ∀ (A B : Submodule ℝ (Amb n ℓ)) [A.HasOrthogonalProjection]
        [B.HasOrthogonalProjection], A = B → A.starProjection = B.starProjection := by
      rintro A B _ _ rfl
      rfl
    rw [RectifiableVarifold.tangentProj, dite_eq_left h]
    exact hP _ _ (Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
      (V.mult_pos x hxM).ne' (Classical.choose_spec h) hQ)
  refine ⟨?_, ?_⟩
  · filter_upwards [hgood] with x hx
    obtain ⟨hxM, hW, k, hk⟩ := hx
    exact ⟨_, (hW k hk).1, hproj x _ hxM (hW k hk)⟩
  · -- `μ_V`-a.e. `x` lies in `⋃ k, N k`; on `N k`, `V.tangentProj = p_{DG_k(b_k(·))(ℝⁿ)}`
    -- `μ_V`-a.e., a map continuous on `N k`.
    have hcov : ∀ᵐ x ∂V.weight, x ∈ ⋃ k, N k := by
      filter_upwards [hgood] with x hx
      exact mem_iUnion.2 hx.2.2
    rw [← Measure.restrict_eq_self_of_ae_mem hcov, aestronglyMeasurable_iUnion_iff]
    intro k
    have hlip : LipschitzOnWith (Real.toNNReal (σ k)⁻¹) (b k) (N k) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have h := hlow k (b k x) (hb k x hx).1 (b k y) (hb k y hy).1
      rw [(hb k x hx).2, (hb k y hy).2] at h
      rw [Real.coe_toNNReal _ (inv_nonneg.2 (hσ k).le), dist_eq_norm, dist_eq_norm,
        inv_mul_eq_div, le_div_iff₀ (hσ k), mul_comm]
      exact h
    have hcont : ContinuousOn
        (fun x => (LinearMap.range (fderiv ℝ (G k) (b k x)).toLinearMap).starProjection) (N k) :=
      (Submission.aetp_starProjection_range_continuousOn n ℓ).comp
        (((hG k).continuous_fderiv one_ne_zero).comp_continuousOn hlip.continuousOn)
        fun x hx => hDG k (b k x) (hb k x hx).1
    refine (hcont.aestronglyMeasurable (hpiece k).1).congr ((ae_restrict_iff' (hpiece k).1).2 ?_)
    filter_upwards [hgood] with x hx hxN
    exact (hproj x _ hx.1 (hx.2.1 k hxN)).symm
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
/-- Simon Ch. 5, proof of Lemma 2.1, (1)–(3) (p. 107): if `T_x V = P` and `P`, `T` are
`n`-dimensional, the height test field `X(y) = ζ(y)² p_{T⊥}(y − ξ)` has tangential divergence
`div_M X(x) = ζ(x)² |p_P − p_T|²/2 + 2ζ(x) Dζ(x)((p_P − p_T) p_{T⊥}(x − ξ))`
(`|·|` the Hilbert–Schmidt norm). -/
theorem divM_height_test_field_eq (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U)
    (ζ : Amb n ℓ → ℝ) (ξ x : Amb n ℓ) (P T : Submodule ℝ (Amb n ℓ))
    (hζ : DifferentiableAt ℝ ζ x) (hP : Module.finrank ℝ P = n) (hT : Module.finrank ℝ T = n)
    (hV : V.tangentProj x = P.starProjection) :
    V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - ξ)) x =
      ζ x ^ 2 * (hsNormSq (P.starProjection - T.starProjection) / 2) +
        2 * ζ x * fderiv ℝ ζ x
          ((P.starProjection - T.starProjection) (Tᗮ.starProjection (x - ξ))) := by
  -- `DX(x) = ζ(x)² p_{T⊥} + (2ζ(x) Dζ(x)).smulRight x'` with `x' = p_{T⊥}(x − ξ)`.
  have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - ξ)) Tᗮ.starProjection x :=
    (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const ξ)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have hX := hsq.fun_smul hlin
  -- `x' ∈ T⊥`, so `p_T x' = 0`.
  have hx' : T.starProjection (Tᗮ.starProjection (x - ξ)) = 0 :=
    (T.starProjection_apply_eq_zero_iff).mpr (Tᗮ.starProjection_apply_mem _)
  -- Projection algebra (iii), as `dim P = dim T`: `trace(p_{T⊥} ∘ p_P) = |p_P − p_T|²/2`.
  have htr : LinearMap.trace ℝ (Amb n ℓ)
      (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        hsNormSq (P.starProjection - T.starProjection) / 2 :=
    Submission.hsNorm_starProjection_trace_identities.2.2 (n + ℓ) P T (hP.trans hT.symm)
  -- The rank-one part: `(φ.smulRight x') ∘ p_P = (φ ∘ p_P).smulRight x'`.
  have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - ξ))).toLinearMap ∘ₗ
      P.starProjection.toLinearMap =
        (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
          (Tᗮ.starProjection (x - ξ)) := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
  rw [RectifiableVarifold.divM, hX.fderiv, hV, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
    map_smul, htr, LinearMap.trace_smulRight]
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, smul_apply,
    smul_eq_mul, sub_apply, hx', sub_zero]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
