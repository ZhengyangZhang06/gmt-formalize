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

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

theorem allard52_radial_height : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → Rn ℓ) (R δ : ℝ), 0 < R → 0 < δ → δ ≤ 1 → f 0 = 0 → ContDiffOn ℝ 1 f (ball 0 R) → LipschitzOnWith 1 f (ball 0 R) → (∀ x ∈ ball (0 : Rn n) R, hsNorm (fderiv ℝ f x) ≤ M * (‖x‖ / R) ^ α) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖f x - fderiv ℝ f x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal (A * δ) → ∀ x ∈ ball (0 : Rn n) R, ‖f x‖ ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖ := by
  have rayCS : ∀ (ℓ : ℕ) (φ φ' : ℝ → Rn ℓ) (a b : ℝ), 0 < a → a ≤ b → (∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Icc a b) → ENNReal.ofReal (‖φ b - φ a‖ ^ 2) ≤ ENNReal.ofReal (Real.log (b / a)) * ∫⁻ t in Ioo a b, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
    intro ℓ φ φ' a b ha hab hderiv hcont
    rcases hab.eq_or_lt with rfl | hab'
    · simp
    have hb : 0 < b := ha.trans hab'
    have hU : uIcc a b = Icc a b := uIcc_of_le hab
    have hpos : ∀ t ∈ Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
    have hcN : ContinuousOn (fun t => ‖φ' t‖) (Icc a b) := hcont.norm
    have hcI : ContinuousOn (fun t => t * ‖φ' t‖ ^ 2) (Icc a b) := continuousOn_id.mul (hcN.pow 2)
    have hcInv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
      continuousOn_inv₀.mono fun t ht => (hpos t ht).ne'
    have hint' : IntervalIntegrable φ' volume a b := (hU ▸ hcont).intervalIntegrable
    have hFTC : ∫ t in a..b, φ' t = φ b - φ a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [hU]) hint'
    set J := ∫ t in a..b, ‖φ' t‖ with hJdef
    set I := ∫ t in a..b, t * ‖φ' t‖ ^ 2 with hIdef
    set L := Real.log (b / a) with hLdef
    have hJ : ‖φ b - φ a‖ ≤ J := by
      rw [← hFTC]; exact intervalIntegral.norm_integral_le_integral_norm hab
    have hL : ∫ t in a..b, t⁻¹ = L := integral_inv_of_pos ha hb
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg _)
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hab (fun t ht =>
      mul_nonneg (hpos t ht).le (sq_nonneg _))
    have hLpos : 0 < L := Real.log_pos ((one_lt_div ha).mpr hab')
    have hlam : ∀ lam : ℝ, 0 < lam → 2 * lam * J ≤ lam ^ 2 * I + L := by
      intro lam hlampos
      have hmono : ∫ t in a..b, 2 * lam * ‖φ' t‖ ≤ ∫ t in a..b, (lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hU ▸ (hcN.const_smul (2 * lam))).intervalIntegrable
        · exact (hU ▸ ((hcI.const_smul (lam ^ 2)).add hcInv)).intervalIntegrable
        · intro t ht
          have ht0 := hpos t ht
          have e : lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹ - 2 * lam * ‖φ' t‖ = (lam * t * ‖φ' t‖ - 1) ^ 2 / t := by
            field_simp; ring
          have : 0 ≤ lam ^ 2 * (t * ‖φ' t‖ ^ 2) + t⁻¹ - 2 * lam * ‖φ' t‖ := by
            rw [e]; exact div_nonneg (sq_nonneg _) ht0.le
          exact sub_nonneg.mp this
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, hL] at hmono
      · exact hmono
      · exact (hU ▸ (hcI.const_smul (lam ^ 2))).intervalIntegrable
      · exact (hU ▸ hcInv).intervalIntegrable
    have hJ2 : J ^ 2 ≤ L * I := by
      rcases hI0.eq_or_lt with hI | hI
      · have hJz : J ≤ 0 := by
          by_contra h
          push Not at h
          have := hlam (L / J) (div_pos hLpos h)
          rw [← hI, mul_zero, zero_add] at this
          have e : 2 * (L / J) * J = 2 * L := by field_simp
          rw [e] at this
          linarith only [this, hLpos]
        have : J = 0 := le_antisymm hJz hJ0
        rw [this, ← hI]; simp
      · rcases hJ0.eq_or_lt with hJz | hJpos
        · rw [← hJz, sq, zero_mul]
          exact mul_nonneg hLpos.le hI.le
        obtain ⟨u, hu0, hu⟩ : ∃ u, 0 < u ∧ J = u * I :=
          ⟨J / I, div_pos hJpos hI, (div_mul_cancel₀ J hI.ne').symm⟩
        have h := hlam u hu0
        rw [hu] at h ⊢
        have h' : u ^ 2 * I ≤ L := by linarith only [h]
        calc (u * I) ^ 2 = u ^ 2 * I * I := by ring
          _ ≤ L * I := mul_le_mul_of_nonneg_right h' hI.le
    have hIlint : ENNReal.ofReal I = ∫⁻ t in Ioo a b, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
      rw [hIdef, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (hcI.integrableOn_Icc).mono_set Ioo_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have : 0 < t := ha.trans ht.1
        positivity
    calc ENNReal.ofReal (‖φ b - φ a‖ ^ 2) ≤ ENNReal.ofReal (L * I) := by
          apply ENNReal.ofReal_le_ofReal
          calc ‖φ b - φ a‖ ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hJ 2
            _ ≤ L * I := hJ2
      _ = ENNReal.ofReal L * ENNReal.ofReal I := ENNReal.ofReal_mul hLpos.le
      _ = _ := by rw [hIlint]
  have scale : ∀ (n : ℕ) (g : Rn n → ℝ≥0∞), Measurable g → ∀ t : ℝ, 0 < t →
    ∫⁻ y, g (t • y) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, g z := by
    intro n g hg t ht
    have hmap := Measure.map_addHaar_smul (volume : Measure (Rn n)) ht.ne'
    rw [finrank_euclideanSpace_fin] at hmap
    rw [← lintegral_map hg (measurable_const_smul t), hmap, lintegral_smul_measure,
      abs_of_pos (by positivity)]
    rfl
  have core : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (f : Rn n → Rn ℓ) (R r lam : ℝ) (Q : Set (Rn n)),
    0 < lam → lam ≤ 1 → 0 < r → r < R → ContDiffOn ℝ 1 f (ball 0 R) → MeasurableSet Q →
    (∀ y ∈ Q, y ≠ 0 ∧ ‖y‖ ≤ r) →
    ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) ≤
    ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
    (ENNReal.ofReal (r ^ (n + 2)) *
    ∫⁻ z in ball (0 : Rn n) R, ENNReal.ofReal (‖f z - fderiv ℝ f z z‖ ^ 2 / ‖z‖ ^ (n + 2)))) := by
    intro n ℓ hn f R r lam Q hlam hlam1 hr hrR hfC hQ hQy
    set G : Rn n → ℝ := fun y => ‖f y - fderiv ℝ f y y‖ ^ 2 / ‖y‖ ^ (n + 2) with hG
    set g : Rn n → ℝ≥0∞ := (ball (0 : Rn n) R).indicator (fun y => ENNReal.ofReal (G y)) with hg
    have hfc : ContinuousOn f (ball 0 R) := hfC.continuousOn
    have hDc : ContinuousOn (fderiv ℝ f) (ball 0 R) := hfC.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
    have hGc : ContinuousOn (fun y => ENNReal.ofReal (G y)) (ball (0 : Rn n) R \ {0}) := by
      apply ENNReal.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · exact ((hfc.mono sdiff_subset).sub ((hDc.mono sdiff_subset).clm_apply continuousOn_id)).norm.pow 2
      · exact (continuous_norm.pow _).continuousOn
      · intro y hy; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hy.2)
    have hG0 : G 0 = 0 := by simp [hG]
    have hgm : Measurable g := by
      classical
      have : g = (ball (0 : Rn n) R \ {0}).piecewise (fun y => ENNReal.ofReal (G y)) 0 := by
        ext y
        by_cases hy : y ∈ ball (0 : Rn n) R
        · by_cases hy0 : y = 0
          · subst hy0; simp [hg, hy, hG0]
          · simp [hg, hy, hy0, Set.piecewise]
        · simp [hg, hy, Set.piecewise]
      rw [this]
      exact hGc.measurable_piecewise continuousOn_const (measurableSet_ball.diff (measurableSet_singleton 0))
    have hL0 : 0 ≤ Real.log (1 / lam) := Real.log_nonneg (one_le_one_div hlam hlam1)
    have hray : ∀ y ∈ Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) ≤
        ENNReal.ofReal (Real.log (1 / lam)) *
          ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
      intro y hy
      obtain ⟨hy0, hyr⟩ := hQy y hy
      have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 → t • y ∈ ball (0 : Rn n) R := by
        intro t ht ht1
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        exact (mul_le_of_le_one_left (norm_nonneg y) ht1).trans_lt (hyr.trans_lt hrR)
      set φ : ℝ → Rn ℓ := fun t => t⁻¹ • f (t • y) with hφ
      set φ' : ℝ → Rn ℓ := fun t => t⁻¹ • (fderiv ℝ f (t • y)) y - (t ^ 2)⁻¹ • f (t • y) with hφ'
      have hderiv : ∀ t ∈ Icc lam 1, HasDerivAt φ (φ' t) t := by
        intro t ht
        have ht0 : 0 < t := hlam.trans_le ht.1
        have hfd : HasFDerivAt f (fderiv ℝ f (t • y)) (t • y) :=
          ((hfC.differentiableOn one_ne_zero).differentiableAt
            (isOpen_ball.mem_nhds (hmem t ht0 ht.2))).hasFDerivAt
        have hline : HasDerivAt (fun s : ℝ => s • y) y t := by
          simpa using (hasDerivAt_id t).smul_const y
        have hcomp : HasDerivAt (fun s => f (s • y)) (fderiv ℝ f (t • y) y) t :=
          hfd.comp_hasDerivAt t hline
        have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht0.ne'
        have h := hinv.smul hcomp
        convert h using 1
        simp only [hφ', neg_smul, sub_eq_add_neg]
      have hcont' : ContinuousOn φ' (Icc lam 1) := by
        have hpos : ∀ t ∈ Icc lam 1, t ≠ 0 := fun t ht => (hlam.trans_le ht.1).ne'
        have hin : MapsTo (fun t : ℝ => t • y) (Icc lam 1) (ball (0 : Rn n) R) :=
          fun t ht => hmem t (hlam.trans_le ht.1) ht.2
        have hlin : ContinuousOn (fun t : ℝ => t • y) (Icc lam 1) :=
          (continuous_id.smul continuous_const).continuousOn
        have hf' : ContinuousOn (fun t : ℝ => f (t • y)) (Icc lam 1) := hfc.comp hlin hin
        have hD' : ContinuousOn (fun t : ℝ => (fderiv ℝ f (t • y)) y) (Icc lam 1) :=
          (hDc.comp hlin hin).clm_apply continuousOn_const
        apply ContinuousOn.sub
        · exact (continuousOn_inv₀.mono fun t ht => hpos t ht).smul hD'
        · exact ((continuousOn_inv₀.comp (continuous_pow 2).continuousOn
            (fun t ht => pow_ne_zero 2 (hpos t ht))).smul hf')
      have hCS := rayCS ℓ φ φ' lam 1 hlam hlam1 hderiv hcont'
      have hend : φ 1 - φ lam = f y - lam⁻¹ • f (lam • y) := by simp [hφ]
      rw [hend] at hCS
      have hid : ∀ t ∈ Ioo lam 1, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) ≤
          ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
        intro t ht
        have ht0 : 0 < t := hlam.trans ht.1
        have hnorm : ‖t • y‖ = t * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        rw [hg, indicator_of_mem (hmem t ht0 ht.2.le), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        simp only [hG, hnorm]
        set L := fderiv ℝ f (t • y)
        have hL : L (t • y) = t • L y := L.map_smul t y
        have hφt : φ' t = (t ^ 2)⁻¹ • (L (t • y) - f (t • y)) := by
          simp only [hφ', hL, smul_sub, smul_smul]
          congr 1
          congr 1
          field_simp
        rw [hφt, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht0, norm_sub_rev]
        set E := ‖f (t • y) - L (t • y)‖ with hE
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have h1 : (t * ‖y‖) ^ (k + 1 + 2) ≤ (t * r) ^ (k + 1 + 2) :=
          pow_le_pow_left₀ (by positivity) (by gcongr) _
        have h2 : 0 < (t * ‖y‖) ^ (k + 1 + 2) := by positivity
        have hE0 : 0 ≤ E ^ 2 := sq_nonneg E
        calc t * ((t ^ 2)⁻¹ * E) ^ 2 = E ^ 2 * (t ^ k * r ^ (k + 1 + 2)) / (t * r) ^ (k + 1 + 2) := by
              field_simp
              ring
          _ ≤ E ^ 2 * (t ^ k * r ^ (k + 1 + 2)) / (t * ‖y‖) ^ (k + 1 + 2) :=
              div_le_div_of_nonneg_left (by positivity) h2 h1
          _ = t ^ k * r ^ (k + 1 + 2) * (E ^ 2 / (t * ‖y‖) ^ (k + 1 + 2)) := by ring
      calc ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2)
          ≤ ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t * ‖φ' t‖ ^ 2) := by
            simpa using hCS
        _ ≤ ENNReal.ofReal (Real.log (1 / lam)) *
              ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
            gcongr _ * ?_
            exact setLIntegral_mono' measurableSet_Ioo hid
    have hFm : Measurable (Function.uncurry fun (y : Rn n) (t : ℝ) =>
        ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y)) := by
      have : Measurable fun p : Rn n × ℝ => p.2 • p.1 := by fun_prop
      exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hgm.comp this)
    have hlogI : ∫⁻ t in Ioo lam 1, ENNReal.ofReal t⁻¹ = ENNReal.ofReal (Real.log (1 / lam)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlam1,
          integral_inv_of_pos hlam one_pos]
      · exact ((continuousOn_inv₀.mono fun t ht => (hlam.trans_le ht.1).ne').integrableOn_Icc).mono_set
          Ioo_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact inv_nonneg.mpr (hlam.trans ht.1).le
    calc ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2)
        ≤ ∫⁻ y in Q, ENNReal.ofReal (Real.log (1 / lam)) *
            ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) :=
          setLIntegral_mono' hQ hray
      _ = ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ y in Q,
            ∫⁻ t in Ioo lam 1, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1,
            ∫⁻ y in Q, ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * g (t • y) := by
          rw [lintegral_lintegral_swap hFm.aemeasurable]
      _ ≤ ENNReal.ofReal (Real.log (1 / lam)) * ∫⁻ t in Ioo lam 1,
            ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z) := by
          gcongr _ * ?_
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ht
          have ht0 : 0 < t := hlam.trans ht.1
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * ∫⁻ y in Q, g (t • y)
              ≤ ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * ∫⁻ y, g (t • y) := by
                gcongr; exact Measure.restrict_le_self
            _ = ENNReal.ofReal (t ^ (n - 1) * r ^ (n + 2)) * (ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, g z) := by
                rw [scale n g hgm t ht0]
            _ = ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z) := by
                rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 2
                obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
                simp only [Nat.add_sub_cancel]
                field_simp
                ring
      _ = ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
            (ENNReal.ofReal (r ^ (n + 2)) * ∫⁻ z, g z)) := by
          rw [lintegral_mul_const _ (by fun_prop), hlogI]
      _ = _ := by rw [hg, lintegral_indicator measurableSet_ball]
  have opHS : ∀ {m k : ℕ} (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A := by
    intro m k A
    have hS : 0 ≤ hsNormSq A := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      ext j; simp [Pi.single_apply]
    have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ := by
      conv_lhs => rw [hv]
      rw [map_sum]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, norm_smul, Real.norm_eq_abs]
    have h2 : ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ ≤
        Real.sqrt (∑ i, |v i| ^ 2) * Real.sqrt (∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have h3 : Real.sqrt (∑ i, |v i| ^ 2) = ‖v‖ := by
      rw [EuclideanSpace.norm_eq]; simp [sq_abs]
    calc ‖A v‖ ≤ _ := h1
      _ ≤ _ := h2
      _ = hsNorm A * ‖v‖ := by rw [h3, mul_comm]; rfl
  have small : ∀ (n ℓ : ℕ) (α M R : ℝ) (f : Rn n → Rn ℓ), 0 < α → 0 ≤ M → 0 < R → f 0 = 0 → ContDiffOn ℝ 1 f (ball 0 R) → (∀ x ∈ ball (0 : Rn n) R, hsNorm (fderiv ℝ f x) ≤ M * (‖x‖ / R) ^ α) → ∀ x ∈ ball (0 : Rn n) R, ‖f x‖ ≤ M * (‖x‖ / R) ^ α * ‖x‖ := by
    intro n ℓ α M R f hα hM hR hf0 hfC hDf x hx
    have hxR : ‖x‖ < R := by simpa using hx
    have hK : closedBall (0 : Rn n) ‖x‖ ⊆ ball (0 : Rn n) R := closedBall_subset_ball hxR
    have hdiff : ∀ y ∈ closedBall (0 : Rn n) ‖x‖, DifferentiableAt ℝ f y := by
      intro y hy
      exact (hfC.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (hK hy))
    have hbound : ∀ y ∈ closedBall (0 : Rn n) ‖x‖, ‖fderiv ℝ f y‖ ≤ M * (‖x‖ / R) ^ α := by
      intro y hy
      have hy' : ‖y‖ ≤ ‖x‖ := by simpa using hy
      calc ‖fderiv ℝ f y‖ ≤ hsNorm (fderiv ℝ f y) := opHS _
        _ ≤ M * (‖y‖ / R) ^ α := hDf y (hK hy)
        _ ≤ M * (‖x‖ / R) ^ α := by
            gcongr
    have hxK : x ∈ closedBall (0 : Rn n) ‖x‖ := mem_closedBall_zero_iff.mpr le_rfl
    have h := (convex_closedBall (0 : Rn n) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (mem_closedBall_self (norm_nonneg x)) hxK
    simpa [hf0] using h
  have logrem : ∀ (n : ℕ), 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2)) ≤ 64 * δ ^ (1 / (2 * (n : ℝ) + 2)) := by
    intro n hn δ hδ hδ1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hL0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1)
    have hq : 0 < δ ^ (-(1 / 8) : ℝ) := Real.rpow_pos_of_pos hδ _
    have hL8 : Real.log (1 / δ) ≤ 8 * δ ^ (-(1 / 8) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hq
      rw [Real.log_rpow hδ, one_div, Real.log_inv] at *
      linarith
    have hsq : Real.log (1 / δ) ^ 2 ≤ 64 * δ ^ (-(1 / 4) : ℝ) := by
      have e : δ ^ (-(1 / 4) : ℝ) = (δ ^ (-(1 / 8) : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num
      rw [e]
      calc Real.log (1 / δ) ^ 2 ≤ (8 * δ ^ (-(1 / 8) : ℝ)) ^ 2 := pow_le_pow_left₀ hL0 hL8 2
        _ = 64 * (δ ^ (-(1 / 8) : ℝ)) ^ 2 := by ring
    have hprod : δ * Real.log (1 / δ) ^ 2 ≤ 64 * δ ^ (3 / 4 : ℝ) := by
      have e : δ ^ (3 / 4 : ℝ) = δ * δ ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_one_add' hδ.le (by norm_num)]; norm_num
      rw [e]
      calc δ * Real.log (1 / δ) ^ 2 ≤ δ * (64 * δ ^ (-(1 / 4) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsq hδ.le
        _ = 64 * (δ * δ ^ (-(1 / 4) : ℝ)) := by ring
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    calc (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2))
        ≤ (64 * δ ^ (3 / 4 : ℝ)) ^ (1 / ((n : ℝ) + 2)) :=
          Real.rpow_le_rpow (by positivity) hprod hp.le
      _ = 64 ^ (1 / ((n : ℝ) + 2)) * δ ^ ((3 / 4 : ℝ) * (1 / ((n : ℝ) + 2))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le]
      _ ≤ 64 * δ ^ (1 / (2 * (n : ℝ) + 2)) := by
          have h64 : (64 : ℝ) ^ (1 / ((n : ℝ) + 2)) ≤ 64 := by
            calc (64 : ℝ) ^ (1 / ((n : ℝ) + 2)) ≤ 64 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num)
                    (by rw [div_le_one (by positivity)]; linarith)
              _ = 64 := Real.rpow_one 64
          have hexp : 1 / (2 * (n : ℝ) + 2) ≤ (3 / 4 : ℝ) * (1 / ((n : ℝ) + 2)) := by
            rw [div_le_iff₀ (by positivity)]
            field_simp
            linarith
          have hd : δ ^ ((3 / 4 : ℝ) * (1 / ((n : ℝ) + 2))) ≤ δ ^ (1 / (2 * (n : ℝ) + 2)) :=
            Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
          exact mul_le_mul h64 hd (by positivity) (by norm_num)
  have arith : ∀ (n : ℕ), 1 ≤ n → ∀ (m r V α A δ L : ℝ), 0 < m → 0 < r → 0 < V → 0 < α → 0 ≤ A → 0 < δ → δ ≤ 1 → 0 ≤ L → L ≤ (1 / α) * Real.log (1 / δ) → m ^ 2 / 4 * ((m / 8) ^ n * V) ≤ L * (L * (r ^ (n + 2) * (A * δ))) → m ≤ 64 * (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) * δ ^ (1 / (2 * (n : ℝ) + 2)) * r := by
    intro n hn m r V α A δ L hm hr hV hα hA hδ hδ1 hL0 hLle hreal
    have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1)
    have hL2 : L * L ≤ ((1 / α) * Real.log (1 / δ)) * ((1 / α) * Real.log (1 / δ)) :=
      mul_le_mul hLle hLle hL0 (le_trans hL0 hLle)
    have hc : 0 < V / (4 * 8 ^ n) := by positivity
    have h3 : m ^ (n + 2) * (V / (4 * 8 ^ n)) ≤
        ((1 / α) * Real.log (1 / δ)) * ((1 / α) * Real.log (1 / δ)) * (r ^ (n + 2) * (A * δ)) := by
      have e1 : m ^ 2 / 4 * ((m / 8) ^ n * V) = m ^ (n + 2) * (V / (4 * 8 ^ n)) := by
        rw [div_pow, pow_add]; ring
      rw [← e1]
      calc m ^ 2 / 4 * ((m / 8) ^ n * V) ≤ L * (L * (r ^ (n + 2) * (A * δ))) := hreal
        _ = (L * L) * (r ^ (n + 2) * (A * δ)) := by ring
        _ ≤ _ := by gcongr
    have hB0 : 0 ≤ 4 * 8 ^ n * A / (V * α ^ 2) := by positivity
    have hX0 : 0 ≤ δ * Real.log (1 / δ) ^ 2 := by positivity
    have hmpow : m ^ (n + 2) ≤ (4 * 8 ^ n * A / (V * α ^ 2)) * (δ * Real.log (1 / δ) ^ 2) * r ^ (n + 2) := by
      have h4 := (le_div_iff₀ hc).mpr h3
      calc m ^ (n + 2) ≤ _ := h4
        _ = _ := by field_simp
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hroot : ∀ z : ℝ, 0 ≤ z → z = (z ^ (n + 2)) ^ (1 / ((n : ℝ) + 2)) := by
      intro z hz
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
      push_cast
      rw [mul_one_div_cancel hn2.ne', Real.rpow_one]
    have hmle : m ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) *
        (δ * Real.log (1 / δ) ^ 2) ^ (1 / ((n : ℝ) + 2)) * r := by
      rw [hroot m hm.le, hroot r hr.le, ← Real.mul_rpow hB0 hX0,
        ← Real.mul_rpow (mul_nonneg hB0 hX0) (pow_nonneg hr.le _)]
      exact Real.rpow_le_rpow (pow_nonneg hm.le _) hmpow (one_div_pos.mpr hn2).le
    have hK0 : 0 ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) := Real.rpow_nonneg hB0 _
    calc m ≤ _ := hmle
      _ ≤ (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) *
            (64 * δ ^ (1 / (2 * (n : ℝ) + 2))) * r := by
          gcongr; exact logrem n hn δ hδ hδ1
      _ = _ := by ring
  have ballgeom : ∀ (n : ℕ) (x : Rn n) (τ : ℝ), 0 < τ → τ ≤ ‖x‖ / 2 → ∀ y ∈ ball ((1 - τ / (2 * ‖x‖)) • x) (τ / 2), y ≠ 0 ∧ ‖y‖ ≤ ‖x‖ ∧ ‖y - x‖ < τ := by
    intro n x τ hτ hτr y hy
    have hr0 : 0 < ‖x‖ := by linarith only [hτ, hτr]
    have hcoef : 0 ≤ 1 - τ / (2 * ‖x‖) := by
      rw [sub_nonneg, div_le_one (mul_pos two_pos hr0)]; linarith only [hτr, hr0]
    have hcn : ‖(1 - τ / (2 * ‖x‖)) • x‖ = ‖x‖ - τ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]; field_simp
    have hcx : ‖(1 - τ / (2 * ‖x‖)) • x - x‖ = τ / 2 := by
      have hdiff : (1 - τ / (2 * ‖x‖)) • x - x = (-(τ / (2 * ‖x‖))) • x := by
        rw [sub_smul, one_smul, neg_smul]; abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]; field_simp
    rw [mem_ball, dist_eq_norm] at hy
    set c := (1 - τ / (2 * ‖x‖)) • x with hc
    have h1 : ‖y‖ ≤ ‖c‖ + ‖y - c‖ := by
      calc ‖y‖ = ‖c + (y - c)‖ := by rw [add_sub_cancel]
        _ ≤ ‖c‖ + ‖y - c‖ := norm_add_le _ _
    have h2 : ‖c‖ ≤ ‖y‖ + ‖y - c‖ := by
      calc ‖c‖ = ‖y - (y - c)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖ + ‖y - c‖ := norm_sub_le _ _
    have h3 : ‖y - x‖ ≤ ‖y - c‖ + ‖c - x‖ := by
      calc ‖y - x‖ = ‖(y - c) + (c - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - c‖ + ‖c - x‖ := norm_add_le _ _
    have hypos : 0 < ‖y‖ := by linarith only [h2, hcn, hy, hτr, hτ]
    exact ⟨norm_pos_iff.mp hypos, by linarith only [h1, hcn, hy], by linarith only [h3, hy, hcx]⟩
  have lip : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (R lam : ℝ), LipschitzOnWith 1 f (ball 0 R) → 0 < lam → lam ≤ 1 → ∀ y ∈ ball (0 : Rn n) R, ∀ y' ∈ ball (0 : Rn n) R, ‖(f y - lam⁻¹ • f (lam • y)) - (f y' - lam⁻¹ • f (lam • y'))‖ ≤ 2 * ‖y - y'‖ := by
    intro n ℓ f R lam hfL hlam0 hlam1 y hy y' hy'
    have hlamball : ∀ z ∈ ball (0 : Rn n) R, lam • z ∈ ball (0 : Rn n) R := by
      intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      exact (mul_le_of_le_one_left (norm_nonneg z) hlam1).trans_lt hz
    have e1 : ‖f y - f y'‖ ≤ ‖y - y'‖ := by
      have := hfL.dist_le_mul y hy y' hy'
      simpa [dist_eq_norm] using this
    have e2 : ‖f (lam • y) - f (lam • y')‖ ≤ lam * ‖y - y'‖ := by
      have := hfL.dist_le_mul _ (hlamball y hy) _ (hlamball y' hy')
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos hlam0] at this
      simpa using this
    have hsplit : (f y - lam⁻¹ • f (lam • y)) - (f y' - lam⁻¹ • f (lam • y')) =
        (f y - f y') - lam⁻¹ • (f (lam • y) - f (lam • y')) := by
      rw [smul_sub]; abel
    rw [hsplit]
    calc ‖(f y - f y') - lam⁻¹ • (f (lam • y) - f (lam • y'))‖
        ≤ ‖f y - f y'‖ + ‖lam⁻¹ • (f (lam • y) - f (lam • y'))‖ := norm_sub_le _ _
      _ = ‖f y - f y'‖ + lam⁻¹ * ‖f (lam • y) - f (lam • y')‖ := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
      _ ≤ ‖y - y'‖ + lam⁻¹ * (lam * ‖y - y'‖) := by gcongr
      _ = 2 * ‖y - y'‖ := by field_simp; ring
  intro n ℓ hn α M A hα hα1 hM hA
  have hnt : Nontrivial (Rn n) := by
    rw [← Module.finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]; omega
  set V : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hV
  have hVtop : volume (ball (0 : Rn n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hVpos : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : Rn n) one_pos).ne' hVtop
  set K : ℝ := (4 * 8 ^ n * A / (V * α ^ 2)) ^ (1 / ((n : ℝ) + 2)) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg (by norm_num) n)) hA) (mul_nonneg hVpos.le (sq_nonneg α))) _
  refine ⟨M + 64 * K, add_nonneg hM (mul_nonneg (by norm_num) hK0), ?_⟩
  intro f R δ hR hδ hδ1 hf0 hfC hfL hDf hI x hx
  set e : ℝ := 1 / (2 * (n : ℝ) + 2) with he
  have hδe : δ ≤ δ ^ e := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ e := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
          (div_le_one_of_le₀ (by linarith only [hn0]) (by linarith only [hn0]))
  have hδe0 : 0 ≤ δ ^ e := Real.rpow_nonneg hδ.le _
  have hsmall := small n ℓ α M R f hα hM hR hf0 hfC hDf
  have hlin : ∀ y ∈ ball (0 : Rn n) R, ‖f y‖ ≤ ‖y‖ := by
    intro y hy
    have := hfL.dist_le_mul y hy 0 (mem_ball_self hR)
    simpa [hf0, dist_eq_norm] using this
  by_cases hx0 : x = 0
  · subst hx0; simp [hf0]
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  set r₁ : ℝ := δ ^ (1 / α) * R with hr₁
  have hr₁0 : 0 < r₁ := mul_pos (Real.rpow_pos_of_pos hδ _) hR
  have hr₁R' : (r₁ / R) ^ α = δ := by
    rw [hr₁, mul_div_assoc, div_self hR.ne', mul_one, ← Real.rpow_mul hδ.le, one_div,
      inv_mul_cancel₀ hα.ne', Real.rpow_one]
  by_cases hcase : ‖x‖ ≤ r₁
  · have h2 : (‖x‖ / R) ^ α ≤ δ := by
      rw [← hr₁R']
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hcase hR.le) hα.le
    calc ‖f x‖ ≤ M * (‖x‖ / R) ^ α * ‖x‖ := hsmall x hx
      _ ≤ M * δ ^ e * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2.trans hδe) hM) (norm_nonneg x)
      _ ≤ (M + 64 * K) * δ ^ e * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (mul_nonneg (by norm_num) hK0)) hδe0) (norm_nonneg x)
  push Not at hcase
  set lam : ℝ := r₁ / ‖x‖ with hlam
  have hlam0 : 0 < lam := div_pos hr₁0 hr0
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hr0]; exact hcase.le
  have hlamn : ‖lam • x‖ = r₁ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hlam, div_mul_cancel₀ _ hr0.ne']
  have hlamx : lam • x ∈ ball (0 : Rn n) R := by
    rw [mem_ball_zero_iff, hlamn]; exact hcase.trans hrR
  have hW : ‖lam⁻¹ • f (lam • x)‖ ≤ M * δ * ‖x‖ := by
    have h := hsmall (lam • x) hlamx
    rw [hlamn, hr₁R'] at h
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
    calc lam⁻¹ * ‖f (lam • x)‖ ≤ lam⁻¹ * (M * δ * r₁) := by gcongr
      _ = M * δ * ‖x‖ := by rw [hlam]; field_simp
  have hW1 : ‖lam⁻¹ • f (lam • x)‖ ≤ ‖x‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0]
    calc lam⁻¹ * ‖f (lam • x)‖ ≤ lam⁻¹ * ‖lam • x‖ := by gcongr; exact hlin _ hlamx
      _ = ‖x‖ := by rw [hlamn, hlam]; field_simp
  set m : ℝ := ‖f x - lam⁻¹ • f (lam • x)‖ with hm
  have hfx : ‖f x‖ ≤ m + M * δ * ‖x‖ := by
    calc ‖f x‖ = ‖(f x - lam⁻¹ • f (lam • x)) + lam⁻¹ • f (lam • x)‖ := by rw [sub_add_cancel]
      _ ≤ m + ‖lam⁻¹ • f (lam • x)‖ := norm_add_le _ _
      _ ≤ m + M * δ * ‖x‖ := add_le_add le_rfl hW
  have hmain : m ≤ 64 * K * δ ^ e * ‖x‖ := by
    rcases (norm_nonneg (f x - lam⁻¹ • f (lam • x))).eq_or_lt with hmz | hmpos
    · rw [hm, ← hmz]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hδe0) (norm_nonneg x)
    rw [← hm] at hmpos
    have hm2 : m ≤ 2 * ‖x‖ := by
      calc m ≤ ‖f x‖ + ‖lam⁻¹ • f (lam • x)‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := add_le_add (hlin x hx) hW1
        _ = 2 * ‖x‖ := by ring
    set Q : Set (Rn n) := ball ((1 - m / 4 / (2 * ‖x‖)) • x) (m / 4 / 2) with hQ
    have hQy := ballgeom n x (m / 4) (div_pos hmpos (by norm_num)) (by linarith only [hm2])
    have hQR : ∀ y ∈ Q, y ∈ ball (0 : Rn n) R := by
      intro y hy
      rw [mem_ball_zero_iff]
      exact (hQy y hy).2.1.trans_lt hrR
    have hlow : ∀ y ∈ Q, ENNReal.ofReal (m ^ 2 / 4) ≤
        ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) := by
      intro y hy
      have hL := lip n ℓ f R lam hfL hlam0 hlam1 x hx y (hQR y hy)
      have hrev := norm_sub_norm_le (f x - lam⁻¹ • f (lam • x)) (f y - lam⁻¹ • f (lam • y))
      have hyx : ‖x - y‖ < m / 4 := by rw [norm_sub_rev]; exact (hQy y hy).2.2
      have h1 : m / 2 ≤ ‖f y - lam⁻¹ • f (lam • y)‖ := by rw [hm]; linarith
      apply ENNReal.ofReal_le_ofReal
      calc m ^ 2 / 4 = (m / 2) ^ 2 := by ring
        _ ≤ ‖f y - lam⁻¹ • f (lam • y)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have hvolQ : volume Q = ENNReal.ofReal ((m / 8) ^ n) * volume (ball (0 : Rn n) 1) := by
      rw [hQ, Measure.addHaar_ball volume _ (div_nonneg (div_nonneg hmpos.le (by norm_num))
          (by norm_num) : (0 : ℝ) ≤ m / 4 / 2), finrank_euclideanSpace_fin]
      congr 2; ring
    have hup := core n ℓ hn f R ‖x‖ lam Q hlam0 hlam1 hr0 hrR hfC measurableSet_ball
      (fun y hy => ⟨(hQy y hy).1, (hQy y hy).2.1⟩)
    have hL0 : 0 ≤ Real.log (1 / lam) := Real.log_nonneg (one_le_one_div hlam0 hlam1)
    have hLle : Real.log (1 / lam) ≤ (1 / α) * Real.log (1 / δ) := by
      have h1 : Real.log (1 / lam) ≤ Real.log (R / r₁) := by
        apply Real.log_le_log (one_div_pos.mpr hlam0)
        rw [hlam, one_div_div]
        exact div_le_div_of_nonneg_right hrR.le hr₁0.le
      have h2 : R / r₁ = (1 / δ) ^ (1 / α) := by
        rw [hr₁, Real.div_rpow zero_le_one hδ.le, Real.one_rpow]
        field_simp
      rw [h2, Real.log_rpow (one_div_pos.mpr hδ)] at h1
      exact h1
    have hchain : ENNReal.ofReal (m ^ 2 / 4 * ((m / 8) ^ n * V)) ≤
        ENNReal.ofReal (Real.log (1 / lam) * (Real.log (1 / lam) * (‖x‖ ^ (n + 2) * (A * δ)))) := by
      calc ENNReal.ofReal (m ^ 2 / 4 * ((m / 8) ^ n * V))
          = ENNReal.ofReal (m ^ 2 / 4) * volume Q := by
            rw [hvolQ, ENNReal.ofReal_mul (div_nonneg (sq_nonneg m) (by norm_num)),
              ENNReal.ofReal_mul (pow_nonneg (div_nonneg hmpos.le (by norm_num)) n), hV,
              ENNReal.ofReal_toReal hVtop]
        _ = ∫⁻ y in Q, ENNReal.ofReal (m ^ 2 / 4) := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal (‖f y - lam⁻¹ • f (lam • y)‖ ^ 2) :=
            setLIntegral_mono' measurableSet_ball hlow
        _ ≤ _ := hup
        _ ≤ ENNReal.ofReal (Real.log (1 / lam)) * (ENNReal.ofReal (Real.log (1 / lam)) *
              (ENNReal.ofReal (‖x‖ ^ (n + 2)) * ENNReal.ofReal (A * δ))) := by gcongr
        _ = _ := by
            rw [← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg x) _), ← ENNReal.ofReal_mul hL0,
              ← ENNReal.ofReal_mul hL0]
    have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL0 (mul_nonneg hL0
      (mul_nonneg (pow_nonneg (norm_nonneg x) _) (mul_nonneg hA hδ.le))))).mp hchain
    have := arith n hn m ‖x‖ V α A δ (Real.log (1 / lam)) hmpos hr0 hVpos hα hA hδ hδ1 hL0 hLle hreal
    exact this
  calc ‖f x‖ ≤ m + M * δ * ‖x‖ := hfx
    _ ≤ 64 * K * δ ^ e * ‖x‖ + M * δ ^ e * ‖x‖ :=
        add_le_add hmain (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδe hM) (norm_nonneg x))
    _ = (M + 64 * K) * δ ^ e * ‖x‖ := by ring

end Submission

end GMT.Ch05
