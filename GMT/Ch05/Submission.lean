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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
