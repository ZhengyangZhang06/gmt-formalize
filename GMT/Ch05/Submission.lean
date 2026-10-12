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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
