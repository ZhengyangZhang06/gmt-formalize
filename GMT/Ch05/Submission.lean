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

/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): chain rule and Schwarz symmetry.**
If `Ψ : L(ℝⁿ, ℝ^ℓ) → ℝ` is `C²` and `u` is `C²` on the open set `U ⊆ ℝⁿ`, then for every direction
`e` and every `y ∈ U`, `D(DΨ ∘ Du)(y) e = D²Ψ(Du(y))[Dv_e(y)]`, where `v_e(z) = Du(z) e`.
Proof: the chain rule gives `D(DΨ ∘ Du)(y) e = D²Ψ(Du(y))[D²u(y) e]`, and
`Dv_e(y) w = D²u(y)[w][e]`; these agree because `D²u(y)` is symmetric (Schwarz).  Given `ε > 0`,
pick `δ > 0` with `B̆_δ(y) ⊆ U` and `‖D²u(z) − D²u(y)‖ < ε` on `B̆_δ(y)`.  For
`h = δ/(2(|v| + |w| + 1))` the mean value inequality for `z ↦ u(z + hw) − u(z)` on `[y, y + hv]`
bounds the second difference `Δ = u(y + hv + hw) − u(y + hv) − u(y + hw) + u(y)` by
`|Δ − h² D²u(y)[w][v]| ≤ ε h² |v| |w|`, and swapping `v` and `w` gives
`|Δ − h² D²u(y)[v][w]| ≤ ε h² |v| |w|`.  Hence `|D²u(y)[v][w] − D²u(y)[w][v]| ≤ 2ε |v| |w|` for
every `ε > 0`. -/
theorem dohr_eb_ehs_del_chain_symm : ∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ∀ (e y : Rn n), y ∈ U → fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) y e = fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y) (fderiv ℝ (fun z => fderiv ℝ u z e) y) := by
  intro n ℓ Ψ U u hU hΨ hu e y hy
  have hUy : U ∈ 𝓝 y := hU.mem_nhds hy
  -- Step 1: `u` and `Du` are differentiable on `U`, and `D²u` is continuous on `U`.
  have hDu : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hdu : ∀ z ∈ U, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn two_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hdDu : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
    (hDu.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hDuy : DifferentiableAt ℝ (fderiv ℝ u) y := hdDu y hy
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) U :=
    hDu.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Step 2: `DΨ` is `C¹`, hence differentiable at `Du(y)`.
  have hDΨ : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hDΨd : DifferentiableAt ℝ (fderiv ℝ Ψ) (fderiv ℝ u y) :=
    hDΨ.differentiable one_ne_zero _
  -- Step 3: chain rule, `D(DΨ ∘ Du)(y) = D²Ψ(Du(y)) ∘ D²u(y)`.
  have h1 : fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) y =
      (fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y)).comp (fderiv ℝ (fderiv ℝ u) y) :=
    fderiv_fun_comp (𝕜 := ℝ) (x := y) (g := fderiv ℝ Ψ) (f := fun z => fderiv ℝ u z)
      hDΨd hDuy
  -- Step 4: `Dv_e(y) w = D²u(y)[w][e]`.
  have h2 : fderiv ℝ (fun z => fderiv ℝ u z e) y = (fderiv ℝ (fderiv ℝ u) y).flip e := by
    rw [fderiv_clm_apply hDuy (differentiableAt_const e)]
    simp
  -- Step 5: Schwarz symmetry of `A = D²u(y)`, via the mean value inequality for `Du`.
  have hsymm : ∀ v w : Rn n,
      fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v := by
    intro v w
    set A := fderiv ℝ (fderiv ℝ u) y
    have hbound : ∀ ε > 0, ‖A v w - A w v‖ ≤ 2 * ε * (‖v‖ * ‖w‖) := by
      intro ε hε
      -- `δ = min r δ'`: `B̆_δ(y) ⊆ U` and `‖D²u(z) − A‖ < ε` on `B̆_δ(y)`
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU y hy
      obtain ⟨δ', hδ', hδ'A⟩ := (NormedAddCommGroup.tendsto_nhds_nhds (E := Rn n)
        (F := Rn n →L[ℝ] Rn n →L[ℝ] Rn ℓ)).mp (hD2.continuousAt hUy) ε hε
      have hδ : 0 < min r δ' := lt_min hr hδ'
      have hball : ball y (min r δ') ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hrU
      -- mean value inequality for `Du` on `B̆_δ(y)` with the fixed linear map `A`
      have hmvt : ∀ a ∈ ball y (min r δ'), ∀ b ∈ ball y (min r δ'),
          ‖fderiv ℝ u b - fderiv ℝ u a - A (b - a)‖ ≤ ε * ‖b - a‖ := by
        intro a ha b hb
        refine (convex_ball y (min r δ')).norm_image_sub_le_of_norm_fderiv_le'
          (fun z hz => hdDu z (hball hz)) (fun z hz => ?_) ha hb
        have hzy : ‖z - y‖ < δ' := by
          rw [← dist_eq_norm]
          exact lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)
        exact (hδ'A z hzy).le
      -- second difference estimate: `z ↦ u(z + h b) − u(z)` on the segment `[y, y + h a]`
      have hsecond : ∀ (h : ℝ) (a b : Rn n), |h| * (‖a‖ + ‖b‖) < min r δ' →
          ‖(u (y + h • a + h • b) - u (y + h • a) - (u (y + h • b) - u y)) - (h ^ 2) • A b a‖
            ≤ ε * (|h| * ‖b‖) * (|h| * ‖a‖) := by
        intro h a b hab
        have hseg : ∀ z ∈ segment ℝ y (y + h • a),
            z ∈ ball y (min r δ') ∧ z + h • b ∈ ball y (min r δ') := by
          intro z hz
          have hz' : z ∈ closedBall y (|h| * ‖a‖) := by
            refine (convex_closedBall y _).segment_subset
              (mem_closedBall_self (by positivity)) ?_ hz
            rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          rw [mem_closedBall, dist_eq_norm] at hz'
          have hb0 : 0 ≤ |h| * ‖b‖ := by positivity
          constructor
          · rw [mem_ball, dist_eq_norm]
            linarith
          · rw [mem_ball, dist_eq_norm]
            calc ‖z + h • b - y‖ = ‖(z - y) + h • b‖ := by congr 1; abel
              _ ≤ ‖z - y‖ + ‖h • b‖ := norm_add_le _ _
              _ ≤ |h| * ‖a‖ + |h| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]; linarith
              _ = |h| * (‖a‖ + ‖b‖) := by ring
              _ < min r δ' := hab
        have hφd : ∀ z ∈ segment ℝ y (y + h • a),
            DifferentiableAt ℝ (fun x => u (x + h • b) - u x) z := fun z hz =>
          ((differentiableAt_comp_add_right (h • b)).mpr (hdu _ (hball (hseg z hz).2))).sub
            (hdu z (hball (hseg z hz).1))
        have hφ := (convex_segment y (y + h • a)).norm_image_sub_le_of_norm_fderiv_le'
          (φ := h • A b) (C := ε * (|h| * ‖b‖)) hφd (fun z hz => ?_)
          (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        · simp only [add_sub_cancel_left, smul_apply, map_smul, smul_smul,
            norm_smul, Real.norm_eq_abs] at hφ
          rw [pow_two]
          convert hφ using 2
        · rw [fderiv_fun_sub ((differentiableAt_comp_add_right (h • b)).mpr
            (hdu _ (hball (hseg z hz).2))) (hdu z (hball (hseg z hz).1)), fderiv_comp_add_right]
          have := hmvt z (hseg z hz).1 (z + h • b) (hseg z hz).2
          rwa [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs] at this
      -- a small step `h > 0`; compare the estimates for `(v, w)` and `(w, v)`
      set h : ℝ := min r δ' / (2 * (‖v‖ + ‖w‖ + 1)) with hh
      have hvw : 0 ≤ ‖v‖ + ‖w‖ := by positivity
      have hpos : 0 < h := by positivity
      have hsmall : ∀ a b : Rn n, ‖a‖ + ‖b‖ = ‖v‖ + ‖w‖ → |h| * (‖a‖ + ‖b‖) < min r δ' := by
        intro a b hab
        rw [hab, abs_of_pos hpos, hh, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have e1 := hsecond h v w (hsmall v w rfl)
      have e2 := hsecond h w v (hsmall w v (add_comm _ _))
      rw [add_right_comm y (h • w) (h • v)] at e2
      have hdiff : (h ^ 2) • (A v w - A w v) =
          ((u (y + h • v + h • w) - u (y + h • v) - (u (y + h • w) - u y)) - (h ^ 2) • A w v) -
          ((u (y + h • v + h • w) - u (y + h • w) - (u (y + h • v) - u y)) - (h ^ 2) • A v w) := by
        rw [smul_sub]; abel
      have hle : h ^ 2 * ‖A v w - A w v‖ ≤ h ^ 2 * (2 * ε * (‖v‖ * ‖w‖)) := by
        have := norm_sub_le
          ((u (y + h • v + h • w) - u (y + h • v) - (u (y + h • w) - u y)) - (h ^ 2) • A w v)
          ((u (y + h • v + h • w) - u (y + h • w) - (u (y + h • v) - u y)) - (h ^ 2) • A v w)
        rw [← hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
        rw [abs_of_pos hpos] at e1 e2
        nlinarith
      exact le_of_mul_le_mul_left hle (by positivity)
    -- let `ε → 0`
    refine eq_of_forall_dist_le fun ε hε => ?_
    rw [dist_eq_norm]
    have hK : 0 ≤ ‖v‖ * ‖w‖ := by positivity
    calc ‖A v w - A w v‖ ≤ 2 * (ε / (2 * (‖v‖ * ‖w‖ + 1))) * (‖v‖ * ‖w‖) :=
          hbound _ (by positivity)
      _ = ε * ((‖v‖ * ‖w‖) / (‖v‖ * ‖w‖ + 1)) := by field_simp
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = ε := mul_one ε
  -- Step 6: `Dv_e(y) = D²u(y) e`; substitute into the chain rule.
  have h3 : (fderiv ℝ (fderiv ℝ u) y).flip e = fderiv ℝ (fderiv ℝ u) y e := by
    ext w : 1
    rw [ContinuousLinearMap.flip_apply]
    exact hsymm w e
  rw [h1, h2, h3]
  rfl
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap, differentiated Euler–Lagrange
equation): uniform convergence of difference quotients.**
If `f : ℝⁿ → E` (`E` any real normed space) is `C¹` on an open `U` and `K ⊆ U` is compact, then for
every direction `e` the difference quotients `h⁻¹ (f(x + h e) − f(x))` converge to `Df(x) e`
uniformly on `K` as `h → 0`, `h ≠ 0`.
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Df` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Df(w) − Df(x)‖ < η/(‖e‖ + 1)` whenever
`w, x ∈ K_ε` and `‖w − x‖ < θ`.  For `0 < |h| < min(ε, θ)/(‖e‖ + 1)` and `x ∈ K`, the segment
`[x, x + h e]` lies in `B_{‖h e‖}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Df(x)` gives `‖f(x + h e) − f(x) − Df(x)(h e)‖ ≤ η |h| ‖e‖/(‖e‖ + 1)`; dividing by `|h|`,
`‖Df(x) e − h⁻¹ (f(x + h e) − f(x))‖ ≤ η ‖e‖/(‖e‖ + 1) < η`. -/
theorem dohr_eb_ehs_del_diffquot_uniform : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Rn n → E) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (h : ℝ) (x : Rn n) => h⁻¹ • (f (x + h • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K := by
  intro n E _ _ f U K e hU hf hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `f` is differentiable on `U` and `Df` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- Step 3: given `η > 0`, choose `θ` and restrict to `0 < |d| < min ε θ / (‖e‖ + 1)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  -- Step 4: the segment `[x, x + d • e]` lies in `closedBall x ‖d • e‖ ⊆ K_ε ⊆ U`.
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  -- Step 5: the mean value inequality with the fixed linear map `Df(x)`.
  have hmvt : ‖f (x + d • e) - f x - fderiv ℝ f x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  -- Step 6: divide by `d ≠ 0`.
  rw [dist_eq_norm]
  have hrw : fderiv ℝ f x e - d⁻¹ • (f (x + d • e) - f x) =
      -(d⁻¹ • (f (x + d • e) - f x - fderiv ℝ f x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (f (x + d • e) - f x) (d • fderiv ℝ f x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖f (x + d • e) - f x - fderiv ℝ f x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): limit of the left side of the
differenced Euler–Lagrange equation.**
Let `F : ℝⁿ → L*`, `L* = L(L(ℝⁿ, ℝ^ℓ), ℝ)`, be `C¹` on an open `U`, and let
`τ : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` be continuous with compact support `K = spt τ ⊆ U`.  Then for every
direction `e`, `∫_U F(x)[h⁻¹ (τ(x) − τ(x − h e))] dx → −∫_U DF(x)e[τ(x)] dx` as `h → 0`, `h ≠ 0`.
Proof: choose `δ > 0` with `cthickening δ K ⊆ U`.  For `|h| < δ/(|e| + 1)` the integrand vanishes
off `U`, every piece is continuous on a compact set and vanishes off it (hence integrable), and the
translation `x = y + h e` (Lebesgue measure is translation invariant) gives
`∫_U F(x)[h⁻¹ (τ(x) − τ(x − h e))] dx = −∫_K Q_h(y)[τ(y)] dy`, `Q_h(y) = h⁻¹ (F(y + h e) − F(y))`.
By `dohr_eb_ehs_del_diffquot_uniform`, `Q_h → DF(·)e` uniformly on `K`, so the integrands are
eventually bounded by `(sup_K |DF(·)e| + 1) sup |τ|` on the finite-measure set `K`, and dominated
convergence gives `∫_K Q_h[τ] → ∫_K DF(·)e[τ] = ∫_U DF(·)e[τ]`. -/
theorem dohr_eb_ehs_del_lhs_tendsto : ∀ n ℓ : ℕ, ∀ (F : Rn n → ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)) (τ : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 F U → Continuous τ → HasCompactSupport τ → tsupport τ ⊆ U → Tendsto (fun h : ℝ => ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e)))) (𝓝[≠] 0) (𝓝 (-∫ x in U, fderiv ℝ F x e (τ x))) := by
  intro n ℓ F τ U e hU hF hτ hτc hτU
  -- Step 1: `K = tsupport τ` is compact and has a closed thickening `cthickening δ K ⊆ U`.
  have hK : IsCompact (tsupport τ) := hτc
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hτU
  -- Step 2: `F` and `DF(·)e` are continuous on `U`; `‖τ‖ ≤ Cτ` everywhere, `‖DF(·)e‖ ≤ CD` on `K`.
  have hFc : ContinuousOn F U := hF.continuousOn
  have hDFe : ContinuousOn (fun y => fderiv ℝ F y e) U :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  obtain ⟨Cτ, hCτ⟩ := hτ.bounded_above_of_compact_support hτc
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn (f := fun y => fderiv ℝ F y e)
    (hDFe.mono hτU)
  -- Step 3: `h⁻¹ (F(y + h e) − F(y)) → DF(y)e` uniformly on `K` (sibling, with `E = L*`).
  have hUC := Submission.dohr_eb_ehs_del_diffquot_uniform n _ F U (tsupport τ) e hU hF hK hτU
  -- Step 1 (cont.): for `|h| < δ/(‖e‖ + 1)` and `y ∈ K`, `y + h e ∈ cthickening δ K ⊆ U`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  have hshift : ∀ h : ℝ, |h| < δ / (‖e‖ + 1) → ∀ y ∈ tsupport τ,
      y + h • e ∈ cthickening δ (tsupport τ) := by
    intro h hh y hy
    apply mem_cthickening_of_dist_le (y + h • e) y δ (tsupport τ) hy
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
      _ ≤ δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ he1.ne'
  have hτ0 : ∀ y, y ∉ tsupport τ → τ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- Step 5: the limit integral over `U` is the integral over `K`.
  have hRHS : ∫ x in U, fderiv ℝ F x e (τ x) = ∫ x in tsupport τ, fderiv ℝ F x e (τ x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hτU
      (fun x hx => by rw [hτ0 x hx.2, map_zero])
  -- Step 4: for `0 < |h| < δ/(‖e‖ + 1)` the left side is `−∫_K h⁻¹ (F(y + h e) − F(y))[τ(y)] dy`.
  have hEq : (fun h : ℝ => ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e)))) =ᶠ[𝓝[≠] 0]
      (fun h : ℝ => -∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y)) := by
    filter_upwards [hev] with h hh
    -- (b) `F(·)[τ]` and `F(· + h e)[τ]` are continuous on `K` and vanish off `K`.
    have hI1 : Integrable (fun x => F x (τ x)) := by
      apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport τ)
      · exact ((hFc.mono hτU).clm_apply hτ.continuousOn).integrableOn_compact hK
      · intro x hx; rw [hτ0 x hx, map_zero]
    have hI2 : Integrable (fun x => F (x + h • e) (τ x)) := by
      apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport τ)
      · apply ContinuousOn.integrableOn_compact hK
        apply ContinuousOn.clm_apply _ hτ.continuousOn
        exact hFc.comp (continuousOn_id.add continuousOn_const)
          (fun y hy => hδU (hshift h hh y hy))
      · intro x hx; rw [hτ0 x hx, map_zero]
    -- (a) the integrand vanishes off `U`, so `∫_U = ∫_{ℝⁿ}`.
    have hL : ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e))) =
        ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e))) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hxU
      have h1 : τ x = 0 := hτ0 x (fun hx => hxU (hτU hx))
      have h2 : τ (x - h • e) = 0 := by
        apply hτ0
        intro hx
        apply hxU
        have := hshift h hh (x - h • e) hx
        rw [sub_add_cancel] at this
        exact hδU this
      simp [h1, h2]
    -- (d) translation invariance: `∫ F(x)[τ(x − h e)] dx = ∫ F(y + h e)[τ(y)] dy`.
    have hT : ∫ x, F x (τ (x - h • e)) = ∫ y, F (y + h • e) (τ y) := by
      rw [← integral_add_right_eq_self (fun x => F x (τ (x - h • e))) (h • e)]
      simp only [add_sub_cancel_right]
    have hI3 : Integrable (fun x => F x (τ (x - h • e))) := by
      have := hI2.comp_sub_right (h • e)
      simpa only [sub_add_cancel] using this
    -- (c), (e) linearity of `F(x)` and of the integral.
    have hW : ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e))) =
        -∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
      calc ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e)))
          = ∫ x, h⁻¹ * (F x (τ x) - F x (τ (x - h • e))) := by
            congr 1; ext x; rw [map_smul, map_sub, smul_eq_mul]
        _ = h⁻¹ * ((∫ x, F x (τ x)) - ∫ x, F x (τ (x - h • e))) := by
            rw [integral_const_mul, integral_sub hI1 hI3]
        _ = h⁻¹ * ((∫ y, F y (τ y)) - ∫ y, F (y + h • e) (τ y)) := by rw [hT]
        _ = -∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
            rw [← integral_sub hI1 hI2, ← integral_const_mul, ← integral_neg]
            congr 1; ext y
            simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
            ring
    have hS : ∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) =
        ∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy; rw [hτ0 y hy, map_zero]
    rw [hL, hW, hS]
  -- Step 6: dominated convergence on `K`, with the bound `(CD + 1) Cτ` for small `h`.
  have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ y ∈ tsupport τ,
      ‖h⁻¹ • (F (y + h • e) - F y) - fderiv ℝ F y e‖ < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUC) 1 one_pos] with h hh y hy
    have := hh y hy
    rw [dist_comm, dist_eq_norm] at this
    exact this
  have hlim : Tendsto (fun h : ℝ => ∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y))
      (𝓝[≠] 0) (𝓝 (∫ y in tsupport τ, fderiv ℝ F y e (τ y))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (CD + 1) * Cτ)
    · filter_upwards [hev] with h hh
      apply ContinuousOn.aestronglyMeasurable _ hK.measurableSet
      -- The integrand is the real-valued `h⁻¹ (F(y + h e)[τ(y)] − F(y)[τ(y)])`, continuous on `K`.
      have hc : ContinuousOn (fun y => h⁻¹ * (F (y + h • e) (τ y) - F y (τ y))) (tsupport τ) :=
        continuousOn_const.mul
          (((hFc.comp (continuousOn_id.add continuousOn_const)
            (fun y hy => hδU (hshift h hh y hy))).clm_apply hτ.continuousOn).sub
            ((hFc.mono hτU).clm_apply hτ.continuousOn))
      refine hc.congr (fun y _ => ?_)
      simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
    · filter_upwards [hev1] with h hh
      apply ae_restrict_of_forall_mem hK.measurableSet
      intro y hy
      have hQ : ‖h⁻¹ • (F (y + h • e) - F y)‖ ≤ CD + 1 := by
        have h1 := norm_le_insert' (E := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
          (h⁻¹ • (F (y + h • e) - F y)) (fderiv ℝ F y e)
        linarith [hh y hy, hCD y hy]
      calc ‖(h⁻¹ • (F (y + h • e) - F y)) (τ y)‖
          ≤ ‖h⁻¹ • (F (y + h • e) - F y)‖ * ‖τ y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (CD + 1) * Cτ := by
            gcongr
            · linarith [norm_nonneg (fderiv ℝ F y e), hCD y hy]
            · exact hCτ y
    · exact integrableOn_const hK.measure_lt_top.ne
    · apply ae_restrict_of_forall_mem hK.measurableSet
      intro y hy
      exact ((ContinuousLinearMap.apply ℝ ℝ (τ y)).continuous.tendsto _).comp (hUC.tendsto_at hy)
  -- Step 7: conclusion.
  rw [hRHS]
  exact hlim.neg.congr' hEq.symm
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
admissibility of the difference-quotient test maps `φ_h(x) = h⁻¹ (ζ(x) − ζ(x − h e))`.  For
`ζ ∈ C¹_c` with `tsupport ζ ⊆ U` (`U` open), compactness gives `δ > 0` with
`K' = cthickening δ (tsupport ζ) ⊆ U`; for `|h| < δ / (‖e‖ + 1)` we have `‖h e‖ < δ`, so
`support φ_h ⊆ K'` and `φ_h` is `C¹`, compactly supported with `tsupport φ_h ⊆ K' ⊆ U`.  The chain
rule for the translation and linearity give `Dφ_h(y) = h⁻¹ (Dζ(y) − Dζ(y − h e))`. -/
theorem dohr_eb_ehs_del_test_admissible : ∀ n ℓ : ℕ, ∀ (ζ : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∀ᶠ h in 𝓝[≠] (0 : ℝ), ContDiff ℝ 1 (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ HasCompactSupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ U ∧ ∀ y, fderiv ℝ (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) y = h⁻¹ • (fderiv ℝ ζ y - fderiv ℝ ζ (y - h • e)) := by
  intro n ℓ ζ U e hU hζ hζc hζU
  -- Step 1 (margin): `K' = cthickening δ (tsupport ζ) ⊆ U`; restrict to `|h| < δ / (‖e‖ + 1)`.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [hev] with h hh
  have hdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  have hhe : ‖h • e‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
      _ < δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ he1.ne'
  -- Step 2 (support): if `φ_h(x) ≠ 0` then `x ∈ tsupport ζ` or `x − h e ∈ tsupport ζ`, so `x ∈ K'`.
  have hsupp : Function.support (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆
      cthickening δ (tsupport ζ) := by
    intro x hx
    by_contra hxK
    apply hx
    have h1 : ζ x = 0 := by
      by_contra h1
      exact hxK (self_subset_cthickening _ (subset_tsupport _ h1))
    have h2 : ζ (x - h • e) = 0 := by
      by_contra h2
      apply hxK
      apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
      rw [dist_eq_norm, sub_sub_cancel]
      exact hhe.le
    simp [h1, h2]
  have htsupp : tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ cthickening δ (tsupport ζ) :=
    closure_minimal hsupp isClosed_cthickening
  refine ⟨?_, ?_, htsupp.trans hδU, ?_⟩
  -- Step 3 (`C¹`): `ζ` composed with the translation, a difference and a constant multiple.
  · exact (hζ.sub (hζ.comp (contDiff_id.sub contDiff_const))).const_smul h⁻¹
  -- Step 4 (compact support): `tsupport φ_h` is closed inside the compact set `K'`.
  · exact IsCompact.of_isClosed_subset hζc.isCompact.cthickening (isClosed_tsupport _) htsupp
  -- Step 5 (derivative): chain rule for the translation (`hasFDerivAt_comp_sub`) and linearity.
  · intro y
    have hd1 : HasFDerivAt (fun x => ζ (x - h • e)) (fderiv ℝ ζ (y - h • e)) y :=
      (hasFDerivAt_comp_sub (h • e)).mpr (hdiff (y - h • e)).hasFDerivAt
    exact ((((hdiff y).hasFDerivAt).sub hd1).const_smul h⁻¹).fderiv

/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap, differentiated Euler–Lagrange
equation): limit of the right side.**
If `ζ : ℝⁿ → ℝ^ℓ` is `C¹` with compact support, `tsupport ζ ⊆ U` for an open `U`, and `g` is
continuous on `U`, then for every direction `e`, with `φ_h = h⁻¹ (ζ − ζ(· − h e))`,
`∫_U ⟨φ_h(x), g(x)⟩ dx → ∫_U ⟨Dζ(x) e, g(x)⟩ dx` as `h → 0`, `h ≠ 0`.
Proof: some `K' = cthickening δ (tsupport ζ)` is a compact subset of `U`, on which `‖g‖ ≤ C_g`
and `‖Dζ(·) e‖ ≤ C_ζ`.  Since `x − h e = x + h (−e)`, the uniform convergence of difference
quotients in the direction `−e` (`dohr_eb_ehs_del_diffquot_uniform`) gives `φ_h → Dζ(·) e`
uniformly on `K'` and pointwise everywhere.  For `0 < |h| < δ/(‖e‖ + 1)`, `φ_h` vanishes off `K'`,
so eventually `|⟨φ_h, g⟩| ≤ (C_ζ + 1) C_g 1_{K'}`, which is integrable; the integrands are
continuous on `U`, and dominated convergence along `𝓝[≠] 0` concludes. -/
theorem dohr_eb_ehs_del_rhs_tendsto : ∀ n ℓ : ℕ, ∀ (ζ g : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ContinuousOn g U → Tendsto (fun h : ℝ => ∫ x in U, inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)) (𝓝[≠] 0) (𝓝 (∫ x in U, inner ℝ (fderiv ℝ ζ x e) (g x))) := by
  intro n ℓ ζ g U e hU hζ hζc hζU hg
  -- Step 1: a compact margin `K' = cthickening δ (tsupport ζ) ⊆ U`, and bounds on `K'` for
  -- `‖g‖` and `‖Dζ(·) e‖`.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have hK' : IsCompact (cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
  obtain ⟨Cg, hCg⟩ := hK'.exists_bound_of_continuousOn (hg.mono hδU)
  have hDζc : Continuous (fun x => fderiv ℝ ζ x e) :=
    (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨Cz, hCz⟩ := hK'.exists_bound_of_continuousOn hDζc.continuousOn
  -- Step 2: uniform convergence of the difference quotients on `K'` in the direction `-e`,
  -- rewritten via `φ_h(x) = -(h⁻¹ (ζ(x + h (-e)) - ζ(x)))` and `Dζ(x) e = -(Dζ(x) (-e))`.
  have hUC := Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ
    (cthickening δ (tsupport ζ)) (-e) isOpen_univ hζ.contDiffOn hK' (subset_univ _)
  have hφ : ∀ (h : ℝ) (x : Rn n), h⁻¹ • (ζ x - ζ (x - h • e)) =
      -(h⁻¹ • (ζ (x + h • (-e)) - ζ x)) := by
    intro h x
    rw [smul_neg, ← sub_eq_add_neg, ← smul_neg, neg_sub]
  have hDneg : ∀ x, fderiv ℝ ζ x e = -(fderiv ℝ ζ x (-e)) := by
    intro x; simp
  -- Step 3: eventually `|h| < δ/(‖e‖ + 1)` and `‖φ_h - Dζ(·) e‖ < 1` on `K'`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ x ∈ cthickening δ (tsupport ζ),
      ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUC) 1 one_pos] with h hh x hx
    have := hh x hx
    rw [dist_eq_norm] at this
    rw [hφ, hDneg, neg_sub_neg]
    exact this
  -- Step 4: dominated convergence along `𝓝[≠] 0` with the bound `(C_ζ + 1) C_g 1_{K'}`.
  apply tendsto_integral_filter_of_dominated_convergence
    ((cthickening δ (tsupport ζ)).indicator (fun _ => (Cz + 1) * Cg))
  · -- The integrands are continuous on `U`.
    filter_upwards with h
    apply ContinuousOn.aestronglyMeasurable _ hU.measurableSet
    apply ContinuousOn.inner _ hg
    have hζ0 := hζ.continuous
    exact Continuous.continuousOn (by fun_prop)
  · -- Domination: on `K'` by the uniform estimate, off `K'` the difference quotient vanishes.
    filter_upwards [hev, hev1] with h hh hh1
    filter_upwards with x
    by_cases hx : x ∈ cthickening δ (tsupport ζ)
    · rw [indicator_of_mem hx]
      have h1 : ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ ≤ Cz + 1 := by
        have := hh1 x hx
        calc ‖h⁻¹ • (ζ x - ζ (x - h • e))‖
            = ‖(h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e) + fderiv ℝ ζ x e‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ + ‖fderiv ℝ ζ x e‖ :=
              norm_add_le _ _
          _ ≤ 1 + Cz := by linarith [hCz x hx]
          _ = Cz + 1 := by ring
      calc ‖inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)‖
          ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ * ‖g x‖ := norm_inner_le_norm _ _
        _ ≤ (Cz + 1) * Cg := by
            gcongr
            · linarith [norm_nonneg (fderiv ℝ ζ x e), hCz x hx]
            · exact hCg x hx
    · rw [indicator_of_notMem hx]
      have h1 : ζ x = 0 := by
        by_contra h1
        exact hx (self_subset_cthickening _ (subset_tsupport _ h1))
      have h2 : ζ (x - h • e) = 0 := by
        by_contra h2
        apply hx
        apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
        calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
          _ ≤ δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
          _ = δ := div_mul_cancel₀ _ he1.ne'
      simp [h1, h2]
  · -- The bound is integrable: a constant on the compact set `K'`.
    rw [integrable_indicator_iff hK'.isClosed.measurableSet]
    exact integrableOn_const (ne_of_lt (lt_of_le_of_lt
      (Measure.restrict_apply_le _ _) hK'.measure_lt_top))
  · -- Pointwise convergence, from the sibling applied to the compact set `{x}`.
    filter_upwards with x
    apply Tendsto.inner _ tendsto_const_nhds
    have hx := (Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ {x} (-e) isOpen_univ
      hζ.contDiffOn isCompact_singleton (subset_univ _)).tendsto_at (mem_singleton x)
    simp only [hφ, hDneg]
    exact hx.neg
/-- The weak Euler–Lagrange equation `∫_U DΨ(Du)[Dφ] = -∫_U ⟨φ, g⟩` (all `φ ∈ C¹_c(U; ℝ^ℓ)`),
differentiated in the direction `e`: `∫_U D²Ψ(Du)[Dv_e][Dζ] = ∫_U ⟨g, Dζ e⟩` with `v_e = Du(·) e`.
Test the equation with the difference quotients `φ_h = h⁻¹ (ζ − ζ(· − h e))`, which are admissible
for small `h ≠ 0`.  With `F = DΨ ∘ Du` (`C¹` on `U`) and `τ = Dζ`, the left side tends to
`−∫_U DF(x) e [Dζ(x)]` and the right side to `−∫_U ⟨Dζ(x) e, g(x)⟩` as `h → 0`; the limits agree, and
`DF(x) e = D²Ψ(Du(x))[Dv_e(x)]` on `U` by the chain rule and the symmetry of `D²u`. -/
theorem dohr_eb_ehs_differentiated_el : ∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u g : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ContinuousOn g U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ (e : Rn n) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x) (fderiv ℝ (fun z => fderiv ℝ u z e) x) (fderiv ℝ ζ x) = ∫ x in U, inner ℝ (g x) (fderiv ℝ ζ x e) := by
  intro n ℓ Ψ U u g hU hΨ hu hg hEL e ζ hζ hζc hζU
  -- `F = DΨ ∘ Du` is `C¹` on `U`; `τ = Dζ` is continuous with compact support inside `U`.
  have hF : ContDiffOn ℝ 1 (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) U :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).comp_contDiffOn
      (hu.fderiv_of_isOpen hU (m := 1) (by norm_num))
  have hτ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by norm_num)
  have hτc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv ℝ
  have hτU : tsupport (fderiv ℝ ζ) ⊆ U := (tsupport_fderiv_subset ℝ).trans hζU
  -- The two sides of the equation tested with `φ_h` and their limits as `h → 0`.
  have hL := Submission.dohr_eb_ehs_del_lhs_tendsto n ℓ (fun z => fderiv ℝ Ψ (fderiv ℝ u z))
    (fderiv ℝ ζ) U e hU hF hτ hτc hτU
  have hR := (Submission.dohr_eb_ehs_del_rhs_tendsto n ℓ ζ g U e hU hζ hζc hζU hg).neg
  -- For small `h ≠ 0`, `φ_h` is admissible and `Dφ_h = h⁻¹ (Dζ − Dζ(· − h e))`.
  have hLR : (fun h : ℝ => ∫ x in U,
        fderiv ℝ Ψ (fderiv ℝ u x) (h⁻¹ • (fderiv ℝ ζ x - fderiv ℝ ζ (x - h • e)))) =ᶠ[𝓝[≠] 0]
      fun h : ℝ => -∫ x in U, inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x) := by
    filter_upwards [Submission.dohr_eb_ehs_del_test_admissible n ℓ ζ U e hU hζ hζc hζU]
      with h ⟨h1, h2, h3, h4⟩
    have hEL_h := hEL _ h1 h2 h3
    simp only [h4] at hEL_h
    exact hEL_h
  -- Uniqueness of limits along `𝓝[≠] 0`.
  have key := neg_inj.mp (tendsto_nhds_unique_of_eventuallyEq hL hR hLR)
  calc ∫ x in U, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x) (fderiv ℝ (fun z => fderiv ℝ u z e) x)
        (fderiv ℝ ζ x)
      = ∫ x in U, fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) x e (fderiv ℝ ζ x) :=
        setIntegral_congr_fun hU.measurableSet fun x hx =>
          (DFunLike.congr_fun
            (Submission.dohr_eb_ehs_del_chain_symm n ℓ Ψ U u hU hΨ hu e x hx) _).symm
    _ = ∫ x in U, inner ℝ (fderiv ℝ ζ x e) (g x) := key
    _ = ∫ x in U, inner ℝ (g x) (fderiv ℝ ζ x e) :=
        integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if
`Ψ` is `C^∞` on `L = L(ℝⁿ, ℝ^ℓ)`, then for fixed `P, Q ∈ L` the Hessian component
`R ↦ D²Ψ(R)[P][Q]` is `C^∞`.  `A = DΨ` is `C^∞`, hence so is `a_Q(R) = A(R)[Q]` and its
derivative; `fderiv_clm_apply` with the constant `Q` gives `Da_Q(R)[P] = DA(R)[P][Q]`, so the map
is the `C^∞` derivative `Da_Q` evaluated at `P`. -/
theorem dohr_eb_ehs_hessian_apply_contDiff : ∀ n ℓ : ℕ, ∀ Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → ∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) (fun R : Rn n →L[ℝ] Rn ℓ => fderiv ℝ (fderiv ℝ Ψ) R P Q) := by
  intro n ℓ Ψ hΨ P Q
  -- Step 1: `A = DΨ` is `C^∞`.
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ).2
  -- Step 2: `a_Q(R) = A(R)[Q]` is `C^∞` (evaluation at `Q` is continuous linear), so is `Da_Q`.
  have haQ : ContDiff ℝ (⊤ : ℕ∞) (fun R => fderiv ℝ Ψ R Q) := hA.clm_apply contDiff_const
  have hDaQ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun R => fderiv ℝ Ψ R Q)) :=
    (contDiff_infty_iff_fderiv.1 haQ).2
  -- Step 3: `Da_Q(R)[P] = DA(R)[P][Q]`, by the product rule with the constant map `Q`.
  have heq : (fun R => fderiv ℝ (fderiv ℝ Ψ) R P Q)
      = fun R => fderiv ℝ (fun R' => fderiv ℝ Ψ R' Q) R P := by
    funext R
    rw [fderiv_clm_apply (hA.differentiable (by simp) R) (differentiableAt_const Q)]
    simp
  -- Step 4: the map is `Da_Q` followed by the continuous linear evaluation at `P`.
  rw [heq]
  exact hDaQ.clm_apply contDiff_const
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): pairing
with a fixed vector `w` preserves the local class `C^{m,α}`.  If `g` is `C^m` on the open set `U` and
`Dᵐg` is `α`-Hölder on every compact `K ⊆ U`, then so is `x ↦ ⟪g x, w⟫ = innerSL ℝ w ∘ g`: its
`m`-th derivative on `U` is `innerSL ℝ w` composed with `Dᵐg` (`iteratedFDeriv_comp_left`), so a
Hölder constant `C` of `Dᵐg` on `K` gives the constant `‖innerSL ℝ w‖ * C`. -/
theorem dohr_eb_ehs_inner_right_holder : ∀ (n ℓ m : ℕ) (α : ℝ) (U : Set (Rn n)) (g : Rn n → Rn ℓ) (w : Rn ℓ), IsOpen U → IsLocallyHolderCkα m α g U → ContDiffOn ℝ m (fun x => inner ℝ (g x) w) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x - iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ m α U g w hU hg
  -- Step 1: `x ↦ ⟪g x, w⟫` is `L ∘ g` for the continuous linear functional `L = ⟪w, ·⟫`.
  set L : Rn ℓ →L[ℝ] ℝ := innerSL ℝ w with hL
  have hfun : (fun z => inner ℝ (g z) w) = L ∘ g := by
    funext z; simp [hL, real_inner_comm]
  -- Step 2: on the open set `U`, `Dᵐ(L ∘ g) = L ∘ Dᵐg`.
  have hiter : ∀ x ∈ U, iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x) := by
    intro x hx
    rw [hfun]
    exact L.iteratedFDeriv_comp_left (hg.1.contDiffAt (hU.mem_nhds hx)) le_rfl
  -- Step 3: `L ∘ g` is `C^m` on `U`.
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact L.contDiff.comp_contDiffOn hg.1
  -- Step 4: by linearity and `‖L ∘ N‖ ≤ ‖L‖ ‖N‖`, a Hölder constant `C` of `Dᵐg` on `K`
  -- gives the Hölder constant `‖L‖ * C` of `Dᵐ(L ∘ g)`.
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hg.2 K hK hKU
    refine ⟨‖L‖ * C, fun x hx y hy => ?_⟩
    rw [hiter x (hKU hx), hiter y (hKU hy)]
    have hsub : L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x)
        - L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g y)
        = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y) := by
      ext v; simp
    rw [hsub]
    calc _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ :=
          L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * (C * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left (hC x hx y hy) (norm_nonneg _)
      _ = ‖L‖ * C * ‖x - y‖ ^ α := by ring

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
