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

/-- **Simon Ch. 5, Theorem 7.1, proof, first sentence (p. 127).**  If `H` is locally in `Lᵖ(μ_V)`
on the open set `U` for some `p > n` and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then `ξ ∈ spt V`, and for
every `δ > 0` there is `r > 0` with `B_r(ξ) ⊆ U`, `μ_V(B_r(ξ)) ≤ (1 + δ) ω_n rⁿ` and
`(r^{p−n} ∫_{B_r(ξ)} |H|ᵖ dμ_V)^{1/p} ≤ δ`. -/
theorem density_one_allard_scale : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (δ : ℝ), IsOpen U → (n : ℝ) < p →
    V.LocallyLp H p → ξ ∈ U → V.HasDensity ξ 1 → 0 < δ → ξ ∈ V.support ∧ ∃ r : ℝ, 0 < r ∧
      closedBall ξ r ⊆ U ∧
      V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) ∧
      V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ := by
  intro n ℓ U V H p ξ δ hU hp hLp hξU hξ hδ
  rw [RectifiableVarifold.HasDensity, ENNReal.ofReal_one] at hξ
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  -- A closed ball `B_{r₀}(ξ) ⊆ U`; it is compact, so `∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V < ∞`.
  obtain ⟨r₀, hr₀, hr₀U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hξU)
  have hA := hLp _ (isCompact_closedBall ξ r₀) hr₀U
  -- `(r^{p−n} ∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V)^{1/p} → 0` as `r ↓ 0`, since `p > n`.
  have hdecay : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
      ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ (p - n)) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (p - n) (Or.inr hpn.le)).tendsto
      rw [Real.zero_rpow hpn.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hA.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    have h3 : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
        ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 (0 ^ (1 / p))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h2
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at h3
  refine ⟨⟨hξU, nhds_basis_closedBall.mem_measureSupport.mpr fun ε hε => ?_⟩, ?_⟩
  · -- `ξ ∈ spt μ_V`: the density ratio tends to `1 > 0`, so `μ_V(B_ε(ξ)) > 0` for every `ε > 0`.
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ε ∧
        0 < V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) := by
      filter_upwards [Ioo_mem_nhdsGT hε, hξ.eventually_const_lt zero_lt_one] with r h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨r, hr, hQ⟩ := hev.exists
    have h0 : V.weight (closedBall ξ r) ≠ 0 := fun h0 => by simp [h0] at hQ
    exact (pos_iff_ne_zero.mpr h0).trans_le (measure_mono (closedBall_subset_closedBall hr.2.le))
  -- A radius `r ∈ (0, r₀)` below both the mass threshold and the `Lᵖ` threshold.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ ∧
      V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) <
        ENNReal.ofReal (1 + δ) ∧
      (ENNReal.ofReal (r ^ (p - n)) * ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) <
        ENNReal.ofReal δ := by
    filter_upwards [Ioo_mem_nhdsGT hr₀,
      hξ.eventually_lt_const (ENNReal.one_lt_ofReal.mpr (show (1 : ℝ) < 1 + δ by linarith)),
      hdecay.eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)] with r h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r, ⟨hr, hrr₀⟩, hQ, hS⟩ := hev.exists
  have hball : closedBall ξ r ⊆ closedBall ξ r₀ := closedBall_subset_closedBall hrr₀.le
  refine ⟨r, hr, hball.trans hr₀U, ?_, ?_⟩
  · have hv : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr n)
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + δ by linarith)]
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hv).ne' ENNReal.ofReal_ne_top).mp hQ.le
  · refine le_trans ?_ hS.le
    exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono_set hball))
      (one_div_pos.mpr hp0).le
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`.  If `V` has generalized mean curvature `H` in `U`,
then `V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`, and the hypotheses 5.1 of `V` in
`B_r(ξ)` become the hypotheses 5.1 (`AllardHypotheses`) of `V'` in `B_r(0)`. -/
theorem exists_translated_varifold_allardHypotheses : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ x, V'.mult x = V.mult (x + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ))) ∧ ∀ (H : Amb n ℓ → Amb n ℓ) (p δ r : ℝ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ξ ∈ V.support → 0 < r → closedBall ξ r ⊆ U → V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) → V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ → V'.AllardHypotheses (fun x => H (x + ξ)) p δ r := by
  intro n ℓ U V ξ
  -- Step 1: `τ = (· − ξ)` is an isometric measurable equivalence with inverse `(· + ξ)`; both
  -- preserve `Hⁿ`, and `τ(S) = (· + ξ)⁻¹(S)`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro hx
      exact ⟨x + ξ, hx, by simp⟩
  have hiso : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hmp_add : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hmp_sub : MeasurePreserving (fun x : Amb n ℓ => x - ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hme_add : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  have hme_sub : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  -- `τ⁻¹(K) ⊆ U` whenever `K ⊆ τ(U)`.
  have hpre_sub : ∀ K : Set (Amb n ℓ), K ⊆ (fun x => x - ξ) '' U → (fun x => x - ξ) ⁻¹' K ⊆ U := by
    intro K hKU y hy
    obtain ⟨u, hu, hu'⟩ := hKU hy
    have : u = y := by simpa using hu'
    exact this ▸ hu
  -- Step 2: the structure fields of `V' = v(τ(M), θ(· + ξ))` in `τ(U)`.
  have hc_meas : NullMeasurableSet ((fun x => x - ξ) '' V.carrier) (μHE[n] : Measure (Amb n ℓ)) := by
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hmp_add.quasiMeasurePreserving
  have hc_rect : Poincare.SimonGMT.Chapter03.CountablyRectifiable n
      ((fun x => x - ξ) '' V.carrier) := by
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j y => F j y - ξ, fun j => ?_, ?_⟩
    · rw [hiso.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨1 * K, hiso.lipschitzWith.comp hK⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, y, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, y, rfl⟩)
  have hm_pos : ∀ x ∈ (fun x => x - ξ) '' V.carrier, 0 < V.mult (x + ξ) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using V.mult_pos x hx
  have hm_aemeas : AEMeasurable (fun x => V.mult (x + ξ))
      ((μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier)) := by
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hmp_add.restrict_preimage_emb hme_add V.carrier).quasiMeasurePreserving
  have hm_int : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ (fun x => x - ξ) '' U →
      IntegrableOn (fun x => V.mult (x + ξ)) ((fun x => x - ξ) '' V.carrier ∩ K)
        (μHE[n] : Measure (Amb n ℓ)) := by
    intro K hK hKU
    have hK' : IsCompact ((fun x => x - ξ) ⁻¹' K) := (Homeomorph.subRight ξ).isCompact_preimage.2 hK
    have h := V.integrableOn_mult _ hK' (hpre_sub K hKU)
    rw [← hmp_add.integrableOn_comp_preimage hme_add] at h
    have hset : (fun x => x - ξ) '' V.carrier ∩ K =
        (fun x => x + ξ) ⁻¹' (V.carrier ∩ (fun x => x - ξ) ⁻¹' K) := by
      rw [himage]
      ext x
      simp
    rw [hset]
    exact h
  obtain ⟨V', hV'c, hV'm⟩ : ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U),
      V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ x, V'.mult x = V.mult (x + ξ) :=
    ⟨⟨(fun x => x - ξ) '' V.carrier, fun x => V.mult (x + ξ), image_mono V.carrier_subset,
      hc_meas, hc_rect, hm_pos, hm_aemeas, hm_int⟩, rfl, fun _ => rfl⟩
  have hV'mf : V'.mult = fun x => V.mult (x + ξ) := funext hV'm
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hweight : V'.weight = V.weight.map (fun x => x - ξ) := by
    have hres : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map (fun x => x - ξ) =
        (μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier) := by
      have h1 := hme_sub.restrict_map (μHE[n] : Measure (Amb n ℓ)) ((fun x => x - ξ) '' V.carrier)
      rw [hmp_sub.map_eq, preimage_image_eq _ hme_sub.injective] at h1
      exact h1.symm
    ext s hs
    rw [Measure.map_apply hme_sub.measurable hs]
    simp only [RectifiableVarifold.weight]
    rw [hV'c, hV'mf, withDensity_apply _ hs, withDensity_apply _ (hme_sub.measurable hs),
      ← hres, hme_sub.restrict_map, hme_sub.lintegral_map]
    simp
  -- Step 4: `spt V' = τ(spt V)`, since `spt(τ_# μ) = τ(spt μ)` for the homeomorphism `τ`.
  have hsupport : V'.support = (fun x => x - ξ) '' V.support := by
    have hspt : (V.weight.map (fun x => x - ξ)).support =
        (fun x => x - ξ) '' V.weight.support := by
      ext x
      rw [himage, mem_preimage, Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
      constructor
      · intro h N' hN'
        have hN : (fun y => y + ξ) ⁻¹' N' ∈ 𝓝 x :=
          (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hN'
        have := h _ hN
        rw [hme_sub.map_apply] at this
        convert this using 2
        ext y
        simp
      · intro h N hN
        have hN' : (fun y => y - ξ) ⁻¹' N ∈ 𝓝 (x + ξ) := by
          apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
          simpa using hN
        rw [hme_sub.map_apply]
        exact h _ hN'
    unfold RectifiableVarifold.support
    rw [hweight, hspt, image_inter hme_sub.injective]
  -- Step 5: weighted approximate tangent spaces, hence `tangentProj`, are translation equivariant.
  have htangent : ∀ x, V'.tangentProj x = V.tangentProj (x + ξ) := by
    intro x
    have hpred : (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V'.carrier V'.mult x P) =
        (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult (x + ξ) P) := by
      funext P
      have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap x r '' V'.carrier =
          Poincare.SimonGMT.Chapter03.blowUpMap (x + ξ) r '' V.carrier := by
        intro r
        rw [hV'c, image_image]
        congr 1
        funext m
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
        congr 1
        abel
      have hmult : ∀ (r : ℝ) (y : Amb n ℓ), V'.mult (x + r • y) = V.mult (x + ξ + r • y) := by
        intro r y
        rw [hV'm]
        congr 1
        abel
      unfold Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt
      simp only [hset, hmult, hV'm]
    have hchoose : ∀ {p q : Submodule ℝ (Amb n ℓ) → Prop} (h1 : ∃ P, p P) (h2 : ∃ P, q P),
        p = q → Classical.choose h1 = Classical.choose h2 := by
      intro p q h1 h2 h
      subst h
      rfl
    have hproj : ∀ {K L : Submodule ℝ (Amb n ℓ)} [K.HasOrthogonalProjection]
        [L.HasOrthogonalProjection], K = L → K.starProjection = L.starProjection := by
      intro K L _ _ h
      subst h
      rfl
    unfold RectifiableVarifold.tangentProj
    split_ifs with h1 h2 h2
    · exact hproj (hchoose h1 h2 hpred)
    · exact absurd (hpred ▸ h1) h2
    · exact absurd (hpred ▸ h2) h1
    · rfl
  -- Step 6: `div_{M'} X ∘ τ = div_M (X ∘ τ)`.
  have hdiv : ∀ (X : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ),
      V'.divM X (y - ξ) = V.divM (fun z => X (z - ξ)) y := by
    intro X y
    unfold RectifiableVarifold.divM
    rw [htangent, fderiv_comp_sub, sub_add_cancel]
  -- Step 7: generalized mean curvature transfers to `V'` with `H' = H(· + ξ)`.
  have hGMC : ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
      V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ)) := by
    intro H hH
    obtain ⟨hloc, hid⟩ := hH
    let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
    have he : (fun x : Amb n ℓ => x - ξ) = ⇑e := rfl
    refine ⟨?_, ?_⟩
    · rw [hweight]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨N, hN, hint⟩ := hloc y hy
      refine ⟨(fun x => x - ξ) '' N, ?_, ?_⟩
      · have hmap := (Homeomorph.subRight ξ).isEmbedding.map_nhdsWithin_eq U y
        simp only [Homeomorph.coe_subRight] at hmap
        rw [← hmap]
        exact image_mem_map hN
      · rw [he, integrableOn_map_equiv e, preimage_image_eq _ e.injective]
        convert hint using 1
        funext z
        show H (z - ξ + ξ) = H z
        rw [sub_add_cancel]
    · intro X hX hXc hXU
      rw [hweight]
      have hI1 : ∫ x, V'.divM X x ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, V'.divM X (y - ξ) ∂V.weight := integral_map_equiv e _
      have hI2 : ∫ x, inner ℝ (X x) (H (x + ξ)) ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, inner ℝ (X (y - ξ)) (H (y - ξ + ξ)) ∂V.weight :=
        integral_map_equiv e (fun x => inner ℝ (X x) (H (x + ξ)))
      rw [hI1, hI2]
      simp only [hdiv, sub_add_cancel]
      have hY1 : ContDiff ℝ 1 (fun z => X (z - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
      have hY2 : HasCompactSupport (fun z => X (z - ξ)) :=
        hXc.comp_homeomorph (Homeomorph.subRight ξ)
      have hY3 : tsupport (fun z => X (z - ξ)) ⊆ U := by
        have hts : tsupport (fun z => X (z - ξ)) = (fun z => z - ξ) ⁻¹' tsupport X := by
          have := (Homeomorph.subRight ξ).preimage_closure (Function.support X)
          simp only [Homeomorph.coe_subRight] at this
          rw [tsupport, tsupport, this]
          rfl
        rw [hts]
        exact hpre_sub _ hXU
      exact hid _ hY1 hY2 hY3
  refine ⟨V', hV'c, hV'm, hweight, hsupport, hGMC, ?_⟩
  -- Step 8: the hypotheses 5.1 of `V` in `B_r(ξ)` are those of `V'` in `B_r(0)`.
  intro H p δ r hH hθ hξ hr hball hmass hLp
  have hball_pre : (fun x => x - ξ) ⁻¹' closedBall (0 : Amb n ℓ) r = closedBall ξ r := by
    ext y
    simp [dist_eq_norm]
  refine ⟨hr, hGMC H hH, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hweight, hme_sub.ae_map_iff]
    filter_upwards [hθ] with y hy
    rw [hV'm, sub_add_cancel]
    exact hy
  · rw [hsupport]
    exact ⟨ξ, hξ, sub_self ξ⟩
  · intro z hz
    refine ⟨z + ξ, hball ?_, by simp⟩
    rw [← hball_pre]
    simpa using hz
  · rw [hweight, hme_sub.map_apply, hball_pre]
    exact hmass
  · unfold RectifiableVarifold.scaledLpNorm at hLp ⊢
    rw [hweight, hme_sub.restrict_map, hme_sub.lintegral_map, hball_pre]
    simpa using hLp
/-- In the proof of Simon 7.1 (p. 127), `u ∈ C^{1,1−n/p}` comes from the estimate of Theorem 5.2:
a finite scaled `C^{1,α}` norm on `B` puts `u` in the Hölder class `C^{1,α}(W)` for every
`W ⊆ int B`.  On `int B` the derivative within `B` is the derivative, and the operator norm of a
linear map is at most its Hilbert–Schmidt norm. -/
theorem isHolderCk_one_of_scaledC1AlphaNorm_ne_top : ∀ {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B W : Set (Rn n)) (α ρ : ℝ), 0 < α → 0 < ρ → ContDiffOn ℝ 1 u B → W ⊆ interior B → scaledC1AlphaNorm u B α ρ ≠ ∞ → IsHolderCkα 1 α u W := by
  intro n ℓ u B W α ρ hα hρ hu hW hN
  -- The operator norm is at most the Hilbert–Schmidt norm (Cauchy–Schwarz in the standard basis).
  have hop : ∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ hsNorm A := by
    intro A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  -- The three suprema in the scaled norm are finite, since `ρ⁻¹ > 0` and `ρ ^ α > 0`.
  rw [scaledC1AlphaNorm, ENNReal.add_ne_top, ENNReal.add_ne_top] at hN
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := hN
  replace h₀ : (⨆ x ∈ B, ‖u x‖ₑ) ≠ ∞ := fun h =>
    h₀ (ENNReal.mul_eq_top.2 (Or.inl ⟨(ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne', h⟩))
  replace h₂ : (⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
      ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)) ≠ ∞ :=
    fun h => h₂ (ENNReal.mul_eq_top.2
      (Or.inl ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hρ α)).ne', h⟩))
  -- Real bounds on `B` for `|u|`, `|D_B u|` and the Hölder quotients of `D_B u`.
  obtain ⟨s₀, hb₀⟩ : ∃ s : ℝ, ∀ x ∈ B, ‖u x‖ ≤ s :=
    ⟨_, fun x hx => (toReal_enorm (u x)).symm.trans_le
      (ENNReal.toReal_mono h₀ (le_iSup₂_of_le x hx le_rfl))⟩
  obtain ⟨s₁, hb₁⟩ : ∃ s : ℝ, ∀ x ∈ B, hsNorm (fderivWithin ℝ u B x) ≤ s :=
    ⟨_, fun x hx => (ENNReal.ofReal_le_iff_le_toReal h₁).1 (le_iSup₂_of_le x hx le_rfl)⟩
  obtain ⟨s₂, hb₂⟩ : ∃ s : ℝ, ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) ≤ s * ‖x - y‖ ^ α :=
    ⟨_, fun x hx y hy hxy =>
      (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) α)).1
        ((ENNReal.ofReal_le_iff_le_toReal h₂).1
          (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))))⟩
  -- On `W ⊆ int B` the derivative within `B` is the derivative.
  have hWB : W ⊆ B := hW.trans interior_subset
  have hD : ∀ x ∈ W, fderivWithin ℝ u B x = fderiv ℝ u x := fun x hx =>
    fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 (hW hx))
  refine ⟨?_, ⟨max s₀ s₁, ?_⟩, ⟨s₂, ?_⟩⟩
  · exact_mod_cast hu.mono hWB
  · intro i hi x hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · rw [norm_iteratedFDeriv_zero]
      exact (hb₀ x (hWB hx)).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one, ← hD x hx]
      exact ((hop _).trans (hb₁ x (hWB hx))).trans (le_max_right _ _)
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow hα.ne']
    · -- The first iterated derivative is the derivative, up to a linear isometry.
      have hD₁ : iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y =
          (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ u x - fderiv ℝ u y) := by
        ext m
        simp
      rw [hD₁, LinearIsometryEquiv.norm_map, ← hD x hx, ← hD y hy]
      exact (hop _).trans (hb₂ x (hWB hx) y (hWB hy) hxy)
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)`.  `τ` and its
inverse `σ = (· + ξ)` are isometries, so they preserve `Hⁿ`, and `τ(S) = σ⁻¹(S)` for every set `S`;
null-measurability, countable rectifiability (via `τ(M₀)` and the Lipschitz maps `F_j − ξ`),
positivity, a.e.-measurability of `θ ∘ σ` and its integrability on `τ(M) ∩ K` (through the compact
set `σ(K) ⊆ U`) all transfer along `σ`. -/
theorem dohr_tv_exists_translate : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ y, V'.mult y = V.mult (y + ξ) := by
  intro n ℓ U V ξ
  -- Step 0: `τ = (· − ξ)` is an isometry, `σ = (· + ξ)` is an `Hⁿ`-measure-preserving measurable
  -- embedding, and `τ(S) = σ⁻¹(S)` for every set `S`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + ξ, hy, add_sub_cancel_right y ξ⟩
  have hτ : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hσ : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hσe : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  -- Steps 1–2: `V' = v(τ(M), θ ∘ σ)`; the two required equalities hold by definition.
  refine ⟨{
    carrier := (fun x => x - ξ) '' V.carrier
    mult := fun y => V.mult (y + ξ)
    carrier_subset := image_mono V.carrier_subset
    nullMeasurableSet_carrier := ?_
    countablyRectifiable := ?_
    mult_pos := ?_
    aemeasurable_mult := ?_
    integrableOn_mult := ?_ }, rfl, fun y => rfl⟩
  · -- Step 3: `τ(M) = σ⁻¹(M)` and `σ` is quasi-measure-preserving.
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hσ.quasiMeasurePreserving
  · -- Step 4: translate the null set `M₀` and the Lipschitz pieces `F j` by `−ξ`.
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j z => F j z - ξ, fun j => ?_, ?_⟩
    · rw [hτ.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨K, LipschitzWith.of_dist_le_mul fun z w =>
        (dist_sub_right (F j z) (F j w) ξ).le.trans (hK.dist_le_mul z w)⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, z, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, z, rfl⟩)
  · -- Step 5: `θ(x − ξ + ξ) = θ(x) > 0` for `x ∈ M`.
    rintro _ ⟨x, hx, rfl⟩
    show 0 < V.mult (x - ξ + ξ)
    rw [sub_add_cancel]
    exact V.mult_pos x hx
  · -- Step 6: `σ` is measure preserving from `Hⁿ⌞σ⁻¹(M)` to `Hⁿ⌞M`.
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hσ.restrict_preimage_emb hσe V.carrier).quasiMeasurePreserving
  · -- Step 7: `σ(K)` is a compact subset of `U`, and `τ(M) ∩ K = σ⁻¹(M ∩ σ(K))`.
    intro K hK hKU
    have hσK : (fun x => x + ξ) '' K ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKU hy
      simpa using hx
    have h := (hσ.integrableOn_comp_preimage hσe).2
      (V.integrableOn_mult _ (hK.image (continuous_add_const ξ)) hσK)
    rwa [preimage_inter, hσe.injective.preimage_image, ← himage] at h
/-- **Weight of a translated varifold** (Simon Ch. 4, 1.1; Ch. 5, proof of Theorem 7.1, p. 127:
"after applying the appropriate translation").  Let `τ(x) = x - ξ`.  If `V' = v(τ(M), θ(· + ξ))`,
then `μ_{V'} = τ_# μ_V`: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ` and
`τ_#(Hⁿ ⌞ M) = Hⁿ ⌞ τ(M)`; for measurable `S`, changing variables along `τ` gives
`μ_{V'}(S) = ∫_{τ⁻¹S} θ(x - ξ + ξ) d(Hⁿ ⌞ M)(x) = μ_V(τ⁻¹S)`. -/
theorem dohr_tv_weight_eq_map : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ),
    V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) →
    V'.weight = V.weight.map (fun x => x - ξ) := by
  intro n ℓ U U' V V' ξ hc hm
  -- `τ(x) = x - ξ` as a measurable equivalence `e` (inverse `y ↦ y + ξ`).
  let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
  -- Step 1: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ`.
  have h1 : (μHE[n] : Measure (Amb n ℓ)).map e = μHE[n] :=
    ((IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n).map_eq
  -- Step 2: `Hⁿ ⌞ τ(M) = (τ_# Hⁿ) ⌞ τ(M) = τ_#(Hⁿ ⌞ τ⁻¹(τ(M))) = τ_#(Hⁿ ⌞ M)`.
  have h2 : (μHE[n] : Measure (Amb n ℓ)).restrict V'.carrier =
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map e := by
    have h := e.restrict_map (μHE[n] : Measure (Amb n ℓ)) (e '' V.carrier)
    rw [h1, Set.preimage_image_eq _ e.injective] at h
    rw [hc]
    exact h
  -- Step 3: compare `μ_{V'}` and `τ_# μ_V` on measurable sets `S`.
  show V'.weight = V.weight.map e
  ext S hS
  -- Step 4: `(τ_# μ_V)(S) = μ_V(τ⁻¹S) = ∫_{τ⁻¹S} θ d(Hⁿ ⌞ M)`.
  rw [e.map_apply]
  simp only [RectifiableVarifold.weight]
  rw [withDensity_apply _ (e.measurable hS)]
  -- Step 5: `μ_{V'}(S) = ∫_S θ' d(τ_#(Hⁿ ⌞ M)) = ∫_{τ⁻¹S} θ'(x - ξ) d(Hⁿ ⌞ M)(x)`.
  rw [withDensity_apply _ hS, h2, e.restrict_map, lintegral_map_equiv]
  -- Step 6: `θ'(x - ξ) = θ(x - ξ + ξ) = θ(x)`, so the two integrals agree.
  refine lintegral_congr fun x => ?_
  show ENNReal.ofReal (V'.mult (x - ξ)) = ENNReal.ofReal (V.mult x)
  rw [hm, sub_add_cancel]
/-- **Support of a translated measure** (used for Simon Ch. 5, Theorem 7.1, p. 127, where `V` is
translated by `τ(x) = x − ξ`).  For every measure `μ` on `ℝ^{n+ℓ}`, `spt (τ_# μ) = τ (spt μ)`.
`τ` is the measurable equivalence `MeasurableEquiv.subRight ξ`, so `(τ_# μ)(N) = μ(τ⁻¹ N)` for
every set `N`.  If `y ∈ spt (τ_# μ)` and `N` is a neighbourhood of `y + ξ`, then `σ⁻¹ N`
(`σ(x) = x + ξ`) is a neighbourhood of `y` and `μ N = (τ_# μ)(σ⁻¹ N) > 0`, so `y = τ(y + ξ)`
with `y + ξ ∈ spt μ`; conversely `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N`
of `τ(x)`. -/
theorem dohr_tv_support_map_sub : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (ξ : Amb n ℓ),
    (μ.map (fun x => x - ξ)).support = (fun x => x - ξ) '' μ.support := by
  intro n ℓ μ ξ
  -- `(τ_# μ)(N) = μ(τ⁻¹ N)` for every set `N`, measurable or not.
  have hmap : ∀ N : Set (Amb n ℓ), μ.map (fun x => x - ξ) N = μ ((fun x => x - ξ) ⁻¹' N) :=
    fun N => (MeasurableEquiv.subRight ξ).map_apply N
  ext y
  simp only [Measure.mem_support_iff_forall, hmap, mem_image]
  constructor
  · -- `y + ξ ∈ spt μ`: pull each neighbourhood `N` of `y + ξ` back along `σ`.
    intro hy
    refine ⟨y + ξ, fun N hN => ?_, add_sub_cancel_right y ξ⟩
    have h := hy ((fun x => x + ξ) ⁻¹' N)
      ((continuous_add_const ξ).continuousAt.preimage_mem_nhds hN)
    simpa [preimage_preimage] using h
  · -- `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N` of `τ(x)`.
    rintro ⟨x, hx, rfl⟩ N hN
    exact hx _ ((continuous_sub_right ξ).continuousAt.preimage_mem_nhds hN)
/-- Simon Ch. 5, proof of Theorem 7.1 (the translation `τ(x) = x − ξ` of `V = v(M, θ)`): if
`V'.carrier = τ(M)` and `V'.mult = θ(· + ξ)`, then `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` and
`V'.mult(y + r z) = θ((y + ξ) + r z)`, so the weighted approximate tangent predicates of `V'` at `y`
and of `V` at `y + ξ` coincide, and hence so do the classically chosen tangent projections. -/
theorem dohr_tv_tangentProj_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ), V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) → ∀ y, V'.tangentProj y = V.tangentProj (y + ξ) := by
  intro n ℓ U U' V V' ξ hM hθ y
  -- The blow-ups agree: `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` since `(x − ξ) − y = x − (y + ξ)`.
  have hblow : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap y r '' V'.carrier =
      Poincare.SimonGMT.Chapter03.blowUpMap (y + ξ) r '' V.carrier := by
    intro r
    rw [hM, Set.image_image]
    congr 1
    funext x
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, sub_sub, add_comm ξ y]
  -- The weights agree: `V'.mult(y + r z) = θ((y + ξ) + r z)`.
  have hw : ∀ (r : ℝ) (z : Amb n ℓ), V'.mult (y + r • z) = V.mult (y + ξ + r • z) := by
    intro r z
    rw [hθ, add_right_comm]
  -- Hence the weighted approximate tangent predicates of `V'` at `y` and of `V` at `y + ξ` agree.
  have hP :
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V'.carrier V'.mult y =
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (y + ξ) := by
    funext P
    simp only [Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt, hblow, hw, hθ y]
  -- `tangentProj` only sees the tangent predicate, so equal predicates give equal projections.
  have key : ∀ A B : Submodule ℝ (Amb n ℓ) → Prop, A = B →
      @dite _ (∃ P, A P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => (0 : Amb n ℓ →L[ℝ] Amb n ℓ)) =
        @dite _ (∃ P, B P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => 0) := by
    rintro A B rfl
    rfl
  exact key _ _ hP
/-- **Generalized mean curvature under the translation `τ(x) = x − ξ`** (Simon Ch. 4, 3.14).  Let
`V'` be a rectifiable varifold in `τ(U)` with `μ_{V'} = τ_# μ_V` and `p_{T_y V'} = p_{T_{y+ξ} V}`
for every `y`.  If `V` has generalized mean curvature `H` in `U`, then `V'` has generalized mean
curvature `y ↦ H(y + ξ)` in `τ(U)`.
Proof: `τ` is a homeomorphism and a measurable embedding.  Local integrability moves along `τ`,
because `τ` maps `𝓝[U] x` onto `𝓝[τ(U)] τ(x)` and `H(· + ξ) ∘ τ = H`.  For `X ∈ C¹_c(τ(U))` the
field `Y = X ∘ τ` lies in `C¹_c(U)`, and `div_{M'} X(τ(x)) = div_M Y(x)` because
`DY(x) = DX(τ(x))`.  Changing variables in both first-variation integrals then gives the identity
for `V'`. -/
theorem dohr_tv_gmc_transfer : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U)), V'.weight = V.weight.map (fun x => x - ξ) → (∀ y, V'.tangentProj y = V.tangentProj (y + ξ)) → ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ V' hw htp H hH
  obtain ⟨hloc, hvar⟩ := hH
  -- `τ(x) = x − ξ` is a measurable embedding and a topological embedding.
  have hτm : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  have hτe : Topology.IsEmbedding (fun x : Amb n ℓ => x - ξ) := (Homeomorph.subRight ξ).isEmbedding
  refine ⟨?_, fun X hX hXc hXs => ?_⟩
  · -- Step 1: `H(· + ξ)` is locally integrable on `τ(U)`.  At `τ(x)`, `x ∈ U`, the filter
    -- `𝓝[τ(U)] τ(x)` is the image of `𝓝[U] x` under `τ`, and `H(· + ξ) ∘ τ = H`.
    rintro _ ⟨x, hxU, rfl⟩
    rw [hw, ← hτe.map_nhdsWithin_eq, hτm.integrableAtFilter_map_iff]
    simpa only [Function.comp_def, sub_add_cancel] using hloc x hxU
  · -- Step 2: the first variation of `V'`, tested against `X`, via the field `Y = X ∘ τ` on `U`.
    have hY : ContDiff ℝ 1 (fun x => X (x - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
    have hYc : HasCompactSupport (fun x => X (x - ξ)) :=
      hXc.comp_homeomorph (Homeomorph.subRight ξ)
    have hYs : tsupport (fun x => X (x - ξ)) ⊆ U := by
      intro x hx
      have hx' : x - ξ ∈ tsupport X := by
        have h : x ∈ tsupport (X ∘ Homeomorph.subRight ξ) := hx
        rwa [tsupport_comp_eq_preimage] at h
      obtain ⟨u, hu, hux⟩ := hXs hx'
      rwa [← sub_left_injective hux]
    -- `div_{M'} X (x − ξ) = div_M Y x`: the tangent planes match and `DY(x) = DX(x − ξ)`.
    have hdiv : ∀ x, V'.divM X (x - ξ) = V.divM (fun x => X (x - ξ)) x := by
      intro x
      simp only [RectifiableVarifold.divM]
      rw [htp, sub_add_cancel, fderiv_comp_sub]
    calc ∫ y, V'.divM X y ∂V'.weight = ∫ x, V'.divM X (x - ξ) ∂V.weight := by
          rw [hw, hτm.integral_map]
      _ = ∫ x, V.divM (fun x => X (x - ξ)) x ∂V.weight := by simp only [hdiv]
      _ = -∫ x, inner ℝ (X (x - ξ)) (H x) ∂V.weight := hvar _ hY hYc hYs
      _ = -∫ y, inner ℝ (X y) (H (y + ξ)) ∂V'.weight := by
          rw [hw, hτm.integral_map]
          simp only [sub_add_cancel]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): translation invariance (fact (Inv)).**  For
`τ(x) = x − ξ`, the translate `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`; if `V` has generalized mean curvature `H` in `U`, then
`V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`.

`V'` and its structure fields come from `dohr_tv_exists_translate`, the weight from
`dohr_tv_weight_eq_map`, the tangent projections `p_{T_y V'} = p_{T_{y+ξ} V}` from
`dohr_tv_tangentProj_eq`, and the first variation from `dohr_tv_gmc_transfer`.  For the support,
`spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V)` (`dohr_tv_support_map_sub`), which is
`τ(U ∩ spt μ_V)` because `τ` is injective. -/
theorem dohr_translate_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ y, V'.mult y = V.mult (y + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ
  -- Steps 1–2: the translate `V'` in `τ(U)` with carrier `τ(M)` and multiplicity `θ(· + ξ)`.
  obtain ⟨V', hc, hm⟩ := Submission.dohr_tv_exists_translate n ℓ U V ξ
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hw := Submission.dohr_tv_weight_eq_map n ℓ U _ V V' ξ hc hm
  -- Step 5: `p_{T_y V'} = p_{T_{y+ξ} V}` for every `y`.
  have ht := Submission.dohr_tv_tangentProj_eq n ℓ U _ V V' ξ hc hm
  -- Step 6 is `dohr_tv_gmc_transfer`; only the support (Step 4) remains.
  refine ⟨V', hc, hm, hw, ?_, Submission.dohr_tv_gmc_transfer n ℓ U V ξ V' hw ht⟩
  -- Step 4: `spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V) = τ(U ∩ spt μ_V)`.
  show (fun x => x - ξ) '' U ∩ V'.weight.support = (fun x => x - ξ) '' (U ∩ V.weight.support)
  rw [hw, Submission.dohr_tv_support_map_sub n ℓ V.weight ξ,
    Set.image_inter (sub_left_injective (b := ξ))]

end Submission

end GMT.Ch05
