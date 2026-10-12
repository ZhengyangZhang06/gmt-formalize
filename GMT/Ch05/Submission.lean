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

end GMT.Ch05
