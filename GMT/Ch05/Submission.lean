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

/-- **Simon Ch. 4, 3.2–3.3 and 4.1** (first variation of the radial cutoff fields).  Let `V` have
generalized mean curvature `H` in `U`, with `p_{T_x M}` the projection onto an `n`-plane for
`μ_V`-a.e. `x`.  Let `φ ∈ C¹(ℝ)` with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[T, ∞)`, let `ρ > 0`, and
let `B_{Tρ}(y) ⊆ U`.  Then `X(x) = φ(r/ρ)(x − y)`, `r = |x − y|`, is admissible in 3.14, and
`div_M X = n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − |(x − y) − p_{T_x M}(x − y)|²/r²)` `μ_V`-a.e.
(both sides equal `n` at `x = y`).  So `∫ div_M X dμ_V = −∫ X · H dμ_V` is the stated identity. -/
theorem aal_radial_first_variation_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (y : Amb n ℓ) (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → closedBall y (T * ρ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH hP y φ T ρ hφ hφ1 hφT hρ hU
  -- Step 1: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, X = fun x => φ (‖x - y‖ / ρ) • (x - y) := ⟨_, rfl⟩
  have hXball : ∀ x ∈ ball y ρ, X =ᶠ[𝓝 x] fun z => z - y := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    have : ‖z - y‖ / ρ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      rw [div_le_one hρ]; exact hz.le
    simp [hX, hφ1 _ this]
  have hXcd : ContDiff ℝ 1 X := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxy : x = y
    · exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq
        (hXball x (by rw [hxy]; exact mem_ball_self hρ))
    · rw [hX]
      have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hxy)
      have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
        hφ.contDiffAt.comp x (h1.div_const ρ)
      exact h2.smul (contDiffAt_id.sub contDiffAt_const)
  -- Step 2: `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
  have hXzero : ∀ z, T * ρ < ‖z - y‖ → X z = 0 := by
    intro z hz
    have hT : T ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; exact hz.le
    rw [hX]; simp [hφT _ hT]
  have hsupp : tsupport X ⊆ closedBall y (T * ρ) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    exact hz (hXzero z h)
  have hXcs : HasCompactSupport X :=
    (isCompact_closedBall y (T * ρ)).of_isClosed_subset (isClosed_tsupport X) hsupp
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  -- Step 3: `X · H = φ(r/ρ)(x - y) · H`.
  have hRHS : (fun x => inner ℝ (X x) (H x)) =
      fun x => φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) := by
    funext x; rw [hX]; exact real_inner_smul_left _ _ _
  rw [hRHS] at key
  -- Step 4: for `x ≠ y`, `DX(x) = φ(r/ρ) id + ρ⁻¹ r⁻¹ φ'(r/ρ) ((x - y) · ⬝) (x - y)`.
  have hXderiv : ∀ x, x ≠ y → HasFDerivAt X
      (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (deriv φ (‖x - y‖ / ρ) / (ρ * ‖x - y‖)) • (innerSL ℝ (x - y)).smulRight (x - y)) x := by
    intro x hxy
    have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    -- `D|· - y|(x) = r⁻¹ (x - y) · ⬝`, from `|z - y| = √(|z - y|²)`.
    have hnorm : HasFDerivAt (fun z : Amb n ℓ => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
      have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt x
        (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y).norm_sq
      convert h using 1
      · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
      · ext v; simp [Real.sqrt_sq hr.le]; field_simp
    have hcomp : HasDerivAt (fun t => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) / ρ) ‖x - y‖ :=
      (((hφ.differentiable one_ne_zero) (‖x - y‖ / ρ)).hasDerivAt.comp ‖x - y‖
        ((hasDerivAt_id' ‖x - y‖).div_const ρ)).congr_deriv (mul_one_div _ _)
    have hc := (hcomp.comp_hasFDerivAt x hnorm).smul (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    have hfun : X = ((fun t => φ (t / ρ)) ∘ fun z : Amb n ℓ => ‖z - y‖) • fun z => z - y := by
      rw [hX]; rfl
    rw [hfun]
    refine hc.congr_fderiv ?_
    ext v
    simp
    ring
  -- Step 5: `trace p_P = dim P` and `trace ((a id + c (u · ⬝) u) ∘ p_P) = a dim P + c u · p_P u`.
  have htrP : ∀ P : Submodule ℝ (Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    intro P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.trace_id]
  have htr : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (u : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) ((a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        a * Module.finrank ℝ P + c * inner ℝ u (P.starProjection u) := by
    intro P a c u
    have hcomp : (a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap =
        a • P.starProjection.toLinearMap +
          c • ((innerSL ℝ u).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight u := by
      ext w; simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrP]
    simp
  -- Step 6: `div_M X` equals the integrand at every `x` where `p_{T_x M}` projects onto an
  -- `n`-plane `P`.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    obtain ⟨P, hPn, hPx⟩ := hx
    rw [RectifiableVarifold.divM, hPx]
    by_cases hxy : x = y
    · -- At the center `DX(y) = id`, so `div_M X(y) = n = n φ(0)`.
      have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
        rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
        exact (hasFDerivAt_sub_const y).fderiv
      rw [hfd]
      simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
      subst hxy
      simp [hφ1 0 zero_le_one]
    · -- Away from it, `(x - y) · p_P (x - y) = |p_P (x - y)|²` and Pythagoras.
      rw [(hXderiv x hxy).fderiv, htr, hPn]
      have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
      have h0 : inner ℝ ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y)) = 0 :=
        Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
      have h1 : inner ℝ (x - y) (P.starProjection (x - y)) = ‖P.starProjection (x - y)‖ ^ 2 := by
        calc inner ℝ (x - y) (P.starProjection (x - y))
            = inner ℝ (((x - y) - P.starProjection (x - y)) + P.starProjection (x - y))
                (P.starProjection (x - y)) := by rw [sub_add_cancel]
          _ = ‖P.starProjection (x - y)‖ ^ 2 := by
            rw [inner_add_left, h0, zero_add, real_inner_self_eq_norm_sq]
      have h2 : ‖x - y‖ ^ 2 =
          ‖(x - y) - P.starProjection (x - y)‖ ^ 2 + ‖P.starProjection (x - y)‖ ^ 2 := by
        have := norm_add_sq_real ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y))
        rw [sub_add_cancel, h0] at this
        linarith
      rw [h1]
      field_simp
      linear_combination (deriv φ (‖x - y‖ / ρ)) * h2
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
/-- **Simon Ch. 4, 4.2–4.3** (the Hölder step for the mean-curvature term).  Let `p > 1`, let `μ`
be a measure on `ℝ^{n+ℓ}` with `μ(B_t(y)) < ∞`, let `H` be `μ`-integrable on `B_t(y)` with
`J = ∫_{B_t(y)} |H|ᵖ dμ < ∞`, and let `ψ` be a.e. strongly measurable with `0 ≤ ψ ≤ 1` and `ψ = 0`
off `B_t(y)`.  Then `|∫ ψ(x) (x − y) · H(x) dμ| ≤ t J^{1/p} (∫ ψ dμ)^{1 − 1/p}`.
Proof: on `B_t(y)`, `|ψ(x) (x − y) · H(x)| ≤ t |H(x)| ψ(x)` by Cauchy–Schwarz, and the pairing
vanishes off `B_t(y)`.  Hölder on `B_t(y)` with `q = p/(p − 1)`, together with `ψ^q ≤ ψ`, bounds
`∫_{B_t(y)} |H| ψ dμ` by `J^{1/p} (∫ ψ dμ)^{1/q}`.  The estimate is proved in `[0, ∞]`, where the
bound is finite, and then converted to real numbers. -/
theorem ted_lpm_curvature_holder : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  intro n ℓ p hp μ H ψ y t ht hμB hHint hHp hψm hψ01 hψt
  -- Notation: `B = B_t(y)`, a closed (hence measurable) ball.
  set B : Set (Amb n ℓ) := closedBall y t
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- Step 1: the conjugate exponent `q = p/(p - 1)`, so `q > 1` and `1/q = 1 - 1/p`.
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q :=
    ⟨p / (p - 1), Real.HolderConjugate.conjExponent hp⟩
  have hq1 : 1 - 1 / p = 1 / q := by rw [one_div, one_div, hpq.one_sub_inv]
  -- Step 2: `ψ` vanishes off `B`.
  have hψB : ∀ x, x ∉ B → ψ x = 0 := fun x hx =>
    hψt x (by simpa [B, mem_closedBall, dist_eq_norm] using hx)
  -- Step 3: `ψ` is bounded by `1` on `B` and `μ(B) < ∞`, so `ψ` is integrable on `B`; it vanishes
  -- off `B`, so it is `μ`-integrable.  Its integral is nonnegative and equals `∫⁻ ‖ψ‖ₑ dμ`.
  have hψe : ∀ x, ‖ψ x‖ₑ = ENNReal.ofReal (ψ x) := fun x => Real.enorm_of_nonneg (hψ01 x).1
  have hψle : ∀ x, ‖ψ x‖ₑ ≤ 1 := fun x => (hψe x).trans_le (ENNReal.ofReal_le_one.2 (hψ01 x).2)
  have hψint : Integrable ψ μ :=
    (IntegrableOn.of_bound hμB hψm.restrict 1 (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (hψ01 x).1]
      exact (hψ01 x).2)).integrable_of_forall_notMem_eq_zero hψB
  have hψnn : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
  have hψI : ∫⁻ x, ‖ψ x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all _ fun x => (hψ01 x).1)]
    exact lintegral_congr hψe
  -- Step 4: on `B`, `|ψ(x)(x - y)·H(x)| ≤ t |H(x)| ψ(x)` by Cauchy–Schwarz and `|x - y| ≤ t`;
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
  -- Step 6: Hölder's inequality on `(B, μ⌞B)` with exponents `p` and `q`.
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq
    hHint.aestronglyMeasurable.enorm hψm.restrict.enorm
  simp only [Pi.mul_apply] at hHolder
  -- Step 7: `ψ^q ≤ ψ` since `0 ≤ ψ ≤ 1` and `q ≥ 1`, so `∫_B ψ^q ≤ ∫_B ψ ≤ ∫ ψ`.
  have hψq : ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) :=
    calc ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ∫⁻ x in B, ‖ψ x‖ₑ ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one (hψle x) hpq.symm.lt.le
      _ ≤ ∫⁻ x, ‖ψ x‖ₑ ∂μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, ψ x ∂μ) := hψI
  -- Steps 5 and 8: integrate the pointwise bound, then apply Steps 6 and 7, all in `[0, ∞]`.
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
  -- Step 9: the bound is finite (`J < ∞`), so `toReal` is monotone on it; `toReal` is
  -- multiplicative and commutes with real powers, and `1/q = 1 - 1/p` by Step 1.
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
/-- Simon Ch. 4, (4.3)–(4.4), in abstract form (`P = I'`, and `Q` plays the role of `J'`): if on
`(0, R)` we have `I' = P`, `L` continuous, `I ≥ 0`, `nI − tP + tQ = −L`,
`a = (L/t^{n+1})/(1 + I/tⁿ)` and `|a| ≤ M t^{−β}` with `β < 1`, then
`Ψ(s) = exp(−∫₀ˢ a)(1 + I(s)/sⁿ)` satisfies `Ψ'(t) = exp(−∫₀ᵗ a) Q(t)/tⁿ`, and
`exp(−∫₀^ρ |a|) ≤ exp(−∫₀ᵗ a) ≤ exp(∫₀^ρ |a|)` for `0 < t ≤ ρ < R`. -/
theorem aal_cfs_integrating_factor_deriv : ∀ (n : ℕ) (I L a P Q : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t : ℝ, 0 < t → t < R → HasDerivAt I (P t) t) → (∀ t : ℝ, 0 < t → t < R → ContinuousAt L t) → (∀ t : ℝ, 0 < t → t < R → 0 ≤ I t) → (∀ t : ℝ, 0 < t → t < R → (n : ℝ) * I t - t * P t + t * Q t = -L t) → (∀ t : ℝ, 0 < t → t < R → a t = L t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → (∀ t : ℝ, 0 < t → t < R → HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n)) (Real.exp (-∫ u in (0)..t, a u) * (Q t / t ^ n)) t) ∧ (∀ t ρ : ℝ, 0 < t → t ≤ ρ → ρ < R → Real.exp (-∫ u in (0)..ρ, |a u|) ≤ Real.exp (-∫ u in (0)..t, a u) ∧ Real.exp (-∫ u in (0)..t, a u) ≤ Real.exp (∫ u in (0)..ρ, |a u|)) := by
  intro n I L a P Q R M β hβ hIder hLc hInn hid ha hab
  have hden : ∀ t, 0 < t → t < R → 1 ≤ 1 + I t / t ^ n := fun t ht htR => by
    have := div_nonneg (hInn t ht htR) (pow_pos ht n).le
    linarith
  -- `a` is continuous on `(0, R)`
  have hacontAt : ∀ t, 0 < t → t < R → ContinuousAt a t := by
    intro t ht htR
    have hev : (fun s => L s / s ^ (n + 1) / (1 + I s / s ^ n)) =ᶠ[𝓝 t] a := by
      filter_upwards [Ioo_mem_nhds ht htR] with s hs
      exact (ha s hs.1 hs.2).symm
    refine ContinuousAt.congr ?_ hev
    exact ((hLc t ht htR).div ((continuous_pow (n + 1)).continuousAt)
      (pow_ne_zero _ ht.ne')).div
      (continuousAt_const.add ((hIder t ht htR).continuousAt.div
        ((continuous_pow n).continuousAt) (pow_ne_zero _ ht.ne')))
      (by linarith [hden t ht htR])
  have hacont : ContinuousOn a (Ioo 0 R) := fun t ht =>
    (hacontAt t ht.1 ht.2).continuousWithinAt
  -- `a` is integrable on `[0, t]`, by the bound `|a s| ≤ M s^(-β)` with `β < 1`
  have haint : ∀ t, 0 < t → t < R → IntervalIntegrable a volume 0 t := by
    intro t ht htR
    refine IntervalIntegrable.mono_fun' (g := fun s => M * s ^ (-β)) ?_ ?_ ?_
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
    · rw [uIoc_of_le ht.le]
      exact (hacont.mono (Ioc_subset_Ioo_right htR)).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
      show ‖a s‖ ≤ M * s ^ (-β)
      rw [Real.norm_eq_abs]
      exact hab s hs.1 (lt_of_le_of_lt hs.2 htR)
  -- the fundamental theorem of calculus for `∫₀ᵗ a`
  have hGderiv : ∀ t, 0 < t → t < R → HasDerivAt (fun u => ∫ s in (0)..u, a s) (a t) t := by
    intro t ht htR
    exact intervalIntegral.integral_hasDerivAt_right (haint t ht htR)
      (hacont.stronglyMeasurableAtFilter isOpen_Ioo t ⟨ht, htR⟩) (hacontAt t ht htR)
  refine ⟨fun t ht htR => ?_, fun t ρ ht htρ hρR => ?_⟩
  · have hd := ((hGderiv t ht htR).neg.exp).mul ((hasDerivAt_const t (1 : ℝ)).add
      ((hIder t ht htR).div (hasDerivAt_pow n t) (pow_ne_zero n ht.ne')))
    have hd' : HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n))
        (Real.exp (-∫ u in (0)..t, a u) * -a t * (1 + I t / t ^ n) +
          Real.exp (-∫ u in (0)..t, a u) *
            (0 + (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2)) t := hd
    convert hd' using 1
    set E := Real.exp (-∫ u in (0)..t, a u) with hEdef
    have hP : 0 < t ^ n := pow_pos ht n
    have hden' : 1 + I t / t ^ n ≠ 0 := by linarith [hden t ht htR]
    have haL : a t * (1 + I t / t ^ n) = L t / (t ^ n * t) := by
      rw [ha t ht htR, div_mul_cancel₀ _ hden', pow_succ]
    have hnpow : (n : ℝ) * t ^ (n - 1) = n * t ^ n / t := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [eq_div_iff ht.ne', mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    have hq : (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2 =
        (t * P t - n * I t) / (t ^ n * t) := by
      rw [hnpow]
      field_simp
    have hidt : t * P t - n * I t = t * Q t + L t := by linarith [hid t ht htR]
    have hQ : (t * Q t + L t) / (t ^ n * t) = Q t / t ^ n + L t / (t ^ n * t) := by
      field_simp
    rw [hq, hidt, hQ]
    linear_combination E * haL
  · have hiρ := haint ρ (ht.trans_le htρ) hρR
    have h1 : |∫ u in (0)..t, a u| ≤ ∫ u in (0)..t, |a u| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    have h2 : ∫ u in (0)..t, |a u| ≤ ∫ u in (0)..ρ, |a u| :=
      intervalIntegral.integral_mono_interval le_rfl ht.le htρ
        (Eventually.of_forall fun u => abs_nonneg _) hiρ.abs
    have h3 := abs_le.mp (h1.trans h2)
    exact ⟨Real.exp_le_exp.mpr (by linarith [h3.2]), Real.exp_le_exp.mpr (by linarith [h3.1])⟩
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

end Submission

namespace Submission

/-- Integrability of a continuous radial profile vanishing beyond `T` (the integrability parts (a)
and (b) of `ted_lpm_fcm_cutoff_mass_hasDerivAt`): if `μ(B_S(y)) < ∞`, `g` is continuous with
`g = 0` on `(T, ∞)`, `t > 0` and `T t < S`, then `x ↦ g(‖x − y‖/t)` is `μ`-integrable.
It is bounded by `K = max(max_{[0,T]} |g|, 0)`, hence integrable on `B_S(y)`, and it vanishes off
`B_S(y)`, where `‖x − y‖/t > S/t > T`. -/
theorem ted_lpm_fcm_cmd_radial_integrable : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (g : ℝ → ℝ) (S T t : ℝ), μ (closedBall y S) < ⊤ → Continuous g → (∀ u : ℝ, T < u → g u = 0) → 0 < t → T * t < S → Integrable (fun x => g (‖x - y‖ / t)) μ := by
  intro n ℓ μ y g S T t hμ hg hg0 ht htS
  -- Step 1: `|g u| ≤ K` for `u ≥ 0`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ K := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hg.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hg0 u h, abs_zero]
      exact le_max_right _ _
  -- Step 2: `x ↦ g(‖x − y‖/t)` is continuous, hence a.e.-strongly measurable.
  have hmeas : AEStronglyMeasurable (fun x => g (‖x - y‖ / t)) (μ.restrict (closedBall y S)) :=
    (hg.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
  -- Steps 3–4: it is bounded by `K`, hence integrable on `B_S(y)`, which has finite measure.
  have hon : IntegrableOn (fun x => g (‖x - y‖ / t)) (closedBall y S) μ := by
    refine IntegrableOn.of_bound hμ hmeas K (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hK _ (div_nonneg (norm_nonneg _) ht.le)
  -- Steps 5–6: off `B_S(y)` we have `‖x − y‖/t > T`, so the integrand vanishes there.
  refine hon.integrable_of_forall_notMem_eq_zero fun x hx => hg0 _ ?_
  have hxS : S < ‖x - y‖ := by
    simpa [mem_closedBall, dist_eq_norm, not_le] using hx
  rw [lt_div_iff₀ ht]
  linarith

end Submission

namespace Submission

/-- Derivative of the radial cutoff mass `I(s) = ∫ φ(‖x − y‖/s) dμ` (Simon Ch. 4, 4.3), together
with the integrability of its two radial profiles: if `μ(B_S(y)) < ∞`, `φ` is `C¹` with `φ = 0` on
`[T, ∞)`, `T > 0`, `t > 0` and `T t < S`, then `φ(‖x − y‖/t)` and `(‖x − y‖/t) φ'(‖x − y‖/t)` are
`μ`-integrable and `I'(t) = -(∫ (‖x − y‖/t) φ'(‖x − y‖/t) dμ)/t`.  The profiles `φ` and
`u ↦ u φ'(u)` are continuous and vanish on `(T, ∞)` (where `φ' = 0`), so
`ted_lpm_fcm_cmd_radial_integrable` gives both integrability statements; the derivative is the
weight-`1` case of `allard52_am_cc_cutoff_integral_hasDerivAt`, as `1` is integrable on the
finite-measure ball `B_S(y)`. -/
theorem ted_lpm_fcm_cutoff_mass_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T t : ℝ), 0 < T → μ (closedBall y S) < ⊤ → ContDiff ℝ 1 φ → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → Integrable (fun x => φ (‖x - y‖ / t)) μ ∧ Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t) t := by
  intro n ℓ μ y φ S T t hT hμ hφ hφ0 ht htS
  -- `φ' = 0` on `(T, ∞)`: near each such point `φ` is the zero function.
  have hdzero : ∀ u, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφ0 v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  refine ⟨?_, ?_, ?_⟩
  -- (a): the continuous profile `φ` vanishes on `(T, ∞)`.
  · exact ted_lpm_fcm_cmd_radial_integrable n ℓ μ y φ S T t hμ hφ.continuous
      (fun u hu => hφ0 u hu.le) ht htS
  -- (b): so does the continuous profile `u ↦ u φ'(u)`.
  · exact ted_lpm_fcm_cmd_radial_integrable n ℓ μ y (fun u => u * deriv φ u) S T t hμ
      (continuous_id.mul hφ.continuous_deriv_one) (fun u hu => by simp only [hdzero u hu, mul_zero])
      ht htS
  -- (c): the weighted cutoff derivative with weight `1`.
  · simpa only [mul_one] using allard52_am_cc_cutoff_integral_hasDerivAt n ℓ μ y
      (fun _ => 1) φ S T t (integrableOn_const hμ.ne) hφ hT hφ0 ht htS
/-- Simon Ch. 4, 4.3–4.4 (continuity in the scale of the cutoff pairing): let `φ` be continuous
with `φ = 0` on `[T, ∞)` for some `T > 0`, and let `H` be `μ`-integrable on `B_S(y)`.  Then
`L(s) = ∫ φ(‖x − y‖/s) (x − y)·H(x) dμ(x)` is continuous at every `t > 0` with `T t < S`.
`|φ| ≤ K` on `[0, ∞)` (a bound on the compact `[0, T]`); for `0 < s < S/T` the integrand vanishes
off `B_S(y)` and is bounded there by `K S ‖H‖`, so dominated convergence applies to `μ ⌞ B_S(y)`. -/
theorem ted_lpm_fcm_cutoff_pairing_continuousAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T t : ℝ), 0 < T → IntegrableOn H (closedBall y S) μ → Continuous φ → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ) t := by
  intro n ℓ μ H y φ S T t hT hH hφc hzero ht htS
  have hHν : Integrable H (μ.restrict (closedBall y S)) := hH
  -- Step 1: `|φ| ≤ K` on `[0, ∞)`: `φ` is bounded on the compact `[0, T]` and vanishes beyond `T`.
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφc.continuousOn (s := Icc 0 T))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT.le⟩)
  have hφK : ∀ u, 0 ≤ u → ‖φ u‖ ≤ K := fun u hu => by
    rcases le_or_gt u T with h | h
    · exact hK u ⟨hu, h⟩
    · rw [hzero u h.le, norm_zero]
      exact hK0
  -- `t < S/T`.
  have htR : t < S / T := by
    rw [lt_div_iff₀ hT]
    linarith
  -- Step 2: for `s ∈ (0, S/T)` the integrand vanishes off `B_S(y)` (there `‖x − y‖/s ≥ T`),
  -- so `L(s)` is the integral against `μ ⌞ B_S(y)`.
  have hconv : ∀ s ∈ Ioo 0 (S / T),
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S)) =
        ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ := by
    rintro s ⟨hs, hsR⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hT] at hsR
    have h1 : T ≤ ‖x - y‖ / s := by
      rw [le_div_iff₀ hs]
      linarith
    rw [hzero _ h1, zero_mul]
  -- Step 3: dominated convergence for the `μ ⌞ B_S(y)`-integral at `t`, with bound `K S ‖H‖`.
  have hmain : ContinuousAt (fun s =>
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S))) t := by
    refine continuousAt_of_dominated (bound := fun x => K * S * ‖H x‖) ?_ ?_
      (hHν.norm.const_mul (K * S)) ?_
    · -- Measurability: `x ↦ φ(‖x − y‖/s)` is continuous and `x ↦ (x − y)·H(x)` is
      -- a.e. strongly measurable.
      refine Eventually.of_forall fun s => ?_
      have hcut : Continuous fun x : Amb n ℓ => φ (‖x - y‖ / s) := hφc.comp (by fun_prop)
      exact hcut.aestronglyMeasurable.mul
        (continuous_inner.comp_aestronglyMeasurable
          ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
            hHν.aestronglyMeasurable))
    · -- Domination for `s > 0`: on `B_S(y)`,
      -- `|φ(‖x − y‖/s) (x − y)·H(x)| ≤ K ‖x − y‖ ‖H x‖ ≤ K S ‖H x‖`.
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [ae_restrict_iff' measurableSet_closedBall]
      refine Eventually.of_forall fun x hx => ?_
      rw [mem_closedBall, dist_eq_norm] at hx
      calc ‖φ (‖x - y‖ / s) * inner ℝ (x - y) (H x)‖
          = ‖φ (‖x - y‖ / s)‖ * ‖inner ℝ (x - y) (H x)‖ := norm_mul _ _
        _ ≤ K * (‖x - y‖ * ‖H x‖) :=
            mul_le_mul (hφK _ (div_nonneg (norm_nonneg _) (le_of_lt hs)))
              (norm_inner_le_norm _ _) (norm_nonneg _) hK0
        _ ≤ K * (S * ‖H x‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) hK0
        _ = K * S * ‖H x‖ := (mul_assoc _ _ _).symm
    · -- Pointwise continuity in `s` at `t ≠ 0`, since `φ` is continuous.
      refine Eventually.of_forall fun x => ?_
      exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')).mul
        continuousAt_const
  -- Step 4: both functions agree on the neighbourhood `(0, S/T)` of `t`.
  exact hmain.congr (Filter.eventually_of_mem (Ioo_mem_nhds ht htR) hconv)

/-- Simon Ch. 4, 3.4–3.5 and 4.3–4.4, for one fixed cutoff `φ` (`C¹`, nonincreasing, `φ = 0` on
`[T, ∞)`): if the radial inequality (R) holds on `(0, S/T)` and `|a(t)| ≤ M t^{−β}` with `β < 1`, where
`I(t) = ∫ φ(|x − y|/t) dμ` and `a = (L/t^{n+1})/(1 + I/tⁿ)` with `L(t) = ∫ φ(|x − y|/t)(x − y)·H dμ`,
then `a` is continuous on `(0, S/T)` and `Ψ(ρ) = exp(−∫₀^ρ a)(1 + I(ρ)/ρⁿ)` is nondecreasing there. -/
theorem ted_lpm_fixed_cutoff_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (T S M β : ℝ), 0 < T → β < 1 → μ (closedBall y S) < ⊤ → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, T ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → T * ρ < S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → T * t < S → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 (S / T)) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 (S / T)) := by
  intro n ℓ μ H y φ I a T S M β hT hβ hμS hH hφ hanti hφT hR hI ha hab
  -- `t < S/T` means `T t < S`
  have hTt : ∀ t, t < S / T → T * t < S := fun t htR => (lt_div_iff₀' hT).mp htR
  -- the pairing `L`, the derivative `P = I'` and the defect `Q = (t P − n I − L)/t`
  set L : ℝ → ℝ := fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ
  set P : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t with hP
  set Q : ℝ → ℝ := fun t => (t * P t - n * I t - L t) / t with hQ
  -- `φ ≥ 0` (it is nonincreasing and `φ(T) = 0`), hence `I ≥ 0`
  have hφnn : ∀ u, 0 ≤ φ u := fun u => by
    rcases le_total u T with h | h
    · simpa [hφT T le_rfl] using hanti h
    · exact le_of_eq (hφT u h).symm
  have hInn : ∀ t, 0 ≤ I t := fun t => by
    rw [hI t]
    exact integral_nonneg fun x => hφnn _
  -- the cutoff mass `I` is differentiable with `I' = P`, and the pairing `L` is continuous
  have hmass : ∀ t, 0 < t → t < S / T →
      Integrable (fun x => φ (‖x - y‖ / t)) μ ∧
        Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧
        HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) ∂μ) (P t) t := fun t ht htR =>
    Submission.ted_lpm_fcm_cutoff_mass_hasDerivAt n ℓ μ y φ S T t hT hμS hφ hφT ht (hTt t htR)
  have hIder : ∀ t, 0 < t → t < S / T → HasDerivAt I (P t) t := fun t ht htR => by
    rw [show I = fun s => ∫ x, φ (‖x - y‖ / s) ∂μ from funext hI]
    exact (hmass t ht htR).2.2
  have hLc : ∀ t, 0 < t → t < S / T → ContinuousAt L t := fun t ht htR =>
    Submission.ted_lpm_fcm_cutoff_pairing_continuousAt n ℓ μ H y φ S T t hT hH hφ.continuous hφT
      ht (hTt t htR)
  -- the radial inequality (R) reads `n I − t I' ≤ −L`, i.e. `Q ≥ 0`
  have hQnn : ∀ t, 0 < t → t < S / T → 0 ≤ Q t := fun t ht htR => by
    obtain ⟨h1, h2, -⟩ := hmass t ht htR
    have hRt : ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) ∂μ ≤
        -L t := hR t ht (hTt t htR)
    rw [integral_add (h1.const_mul (n : ℝ)) h2, integral_const_mul, ← hI t] at hRt
    have htP : t * P t = -∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ := by
      simp only [hP]
      field_simp
    simp only [hQ]
    refine div_nonneg ?_ ht.le
    rw [htP]
    linarith
  have hid : ∀ t, 0 < t → t < S / T → (n : ℝ) * I t - t * P t + t * Q t = -L t :=
    fun t ht _ => by
      have ht0 : t ≠ 0 := ht.ne'
      simp only [hQ]
      field_simp
      ring
  -- the integrating factor: `Ψ' = exp(−∫₀ᵗ a) Q(t)/tⁿ` on `(0, S/T)`
  obtain ⟨hΨ, -⟩ := aal_cfs_integrating_factor_deriv n I L a P Q (S / T) M β hβ hIder hLc
    (fun t _ _ => hInn t) hid (fun t _ _ => ha t) (fun t ht htR => hab t ht (hTt t htR))
  refine ⟨fun t ht => ?_, ?_⟩
  · -- `a = (L/t^{n+1})/(1 + I/tⁿ)` is continuous at every point of `(0, S/T)`
    have hden : 1 + I t / t ^ n ≠ 0 := by
      have := div_nonneg (hInn t) (pow_pos ht.1 n).le
      linarith
    rw [show a = fun s => L s / s ^ (n + 1) / (1 + I s / s ^ n) from funext ha]
    exact (((hLc t ht.1 ht.2).div (continuous_pow (n + 1)).continuousAt
      (pow_ne_zero _ ht.1.ne')).div (continuousAt_const.add ((hIder t ht.1 ht.2).continuousAt.div
        (continuous_pow n).continuousAt (pow_ne_zero _ ht.1.ne'))) hden).continuousWithinAt
  · -- `Ψ' ≥ 0` on the open interval `(0, S/T)`
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 (S / T))
      (fun t ht => (hΨ t ht.1 ht.2).continuousAt.continuousWithinAt) ?_ ?_ <;> rw [interior_Ioo]
    · exact fun t ht => (hΨ t ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hΨ t ht.1 ht.2).deriv]
      exact mul_nonneg (Real.exp_pos _).le (div_nonneg (hQnn t ht.1 ht.2) (pow_pos ht.1 n).le)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
