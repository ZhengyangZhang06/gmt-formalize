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

set_option maxHeartbeats 4000000 in
/-- **Simon Ch. 5, Theorem 5.2 (Allard Regularity Theorem, p. 121).**  Fix `δ₀ = δ₀(n, ℓ, p)` and
`γ = δ₀/8192`; 2.3 with `δ ≤ δ₀` implies 2.3 with `δ₀`.  Lemma 2.5 at `(0, 2δ₀ρ)` and the iteration
of 4.5 give planes `S(ξ)` with tilt decay at every `ξ ∈ spt V ∩ B_{δ₀ρ/2}(0)`, so Corollary 2.7
(with `T₀ = S(0)` and `L = min{L_c, L₀/√n}`) makes `spt V` a Lipschitz graph over `B_{δ₀ρ/4}(0)`;
the Campanato estimate makes it `C^{1,1−n/p}` with `Df(0) = 0`.  The conical excess at `0`
(monotonicity, with the true `δ`) bounds the height by `Cδ^{1/(2n+2)}|x|` (radial integration);
Lemma A then bounds the tilt at the fixed scale `R' = δ₀ρ/256` by `Cδ^{1/(n+1)}`, and restarting
the decay iteration there gives the `C^{1,1−n/p}` estimate with the rate `δ^{1/(2n+2)}`. -/
theorem allard_regularity_theorem : AllardRegularityTheorem := by
  intro n ℓ hn p hp
  /- Elementary facts about the exponents `1 − n/p` and `a = 1/(2n+2)`. -/
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hα0 : 0 < 1 - (n : ℝ) / p := by rw [sub_pos, div_lt_one hp0]; exact hp
  have hα1 : 1 - (n : ℝ) / p ≤ 1 := by
    have : 0 ≤ (n : ℝ) / p := div_nonneg (by linarith) hp0.le
    linarith
  have hrpow : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < x ^ (1 / (2 * (n : ℝ) + 2)) ∧
      x ^ (1 / (2 * (n : ℝ) + 2)) ≤ 1 ∧ x ≤ x ^ (1 / (2 * (n : ℝ) + 2)) ∧
      x ≤ (x ^ (1 / (2 * (n : ℝ) + 2))) ^ 2 := by
    intro x hx0 hx1
    have ha0 : 0 < 1 / (2 * (n : ℝ) + 2) := by positivity
    have ha1 : 2 * (1 / (2 * (n : ℝ) + 2)) ≤ 1 := by
      rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]; linarith
    refine ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_le_one hx0.le hx1 ha0.le, ?_, ?_⟩
    · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (1 / (2 * (n : ℝ) + 2)) := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (1 / (2 * (n : ℝ) + 2) * 2) :=
            Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
        _ = (x ^ (1 / (2 * (n : ℝ) + 2))) ^ 2 := by rw [Real.rpow_mul hx0.le, Real.rpow_two]
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  /- Elementary facts on Hilbert–Schmidt norms. -/
  have hs_nonneg : ∀ {m k : ℕ} (A : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq A := fun A =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs_add : ∀ {m k : ℕ} (A B : Rn m →L[ℝ] Rn k),
      hsNormSq (A + B) ≤ 2 * hsNormSq A + 2 * hsNormSq B := by
    intro m k A B
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [add_apply]
    have h1 := norm_add_le (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1))
    have h2 := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg (‖A (EuclideanSpace.single i 1)‖ - ‖B (EuclideanSpace.single i 1)‖)]
  have hs_symm : ∀ {m k : ℕ} (A B : Rn m →L[ℝ] Rn k), hsNormSq (A - B) = hsNormSq (B - A) := by
    intro m k A B
    unfold hsNormSq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_apply, sub_apply, norm_sub_rev]
  have hs_zero : ∀ {m k : ℕ}, hsNormSq (0 : Rn m →L[ℝ] Rn k) = 0 := by
    intro m k
    simp [hsNormSq]
  have hs_bound : ∀ {m : ℕ} (A B : Rn m →L[ℝ] Rn m), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
      hsNormSq (A - B) ≤ 4 * m := by
    intro m A B hA hB
    unfold hsNormSq
    calc ∑ i : Fin m, ‖(A - B) (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin m, (4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖(A - B) (EuclideanSpace.single i (1 : ℝ))‖ ≤ 2 := by
            calc _ ≤ ‖A - B‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ (‖A‖ + ‖B‖) * 1 := by
                  gcongr
                  · exact norm_sub_le _ _
                  · simp
              _ ≤ 2 := by linarith
          nlinarith [norm_nonneg ((A - B) (EuclideanSpace.single i (1 : ℝ)))]
      _ = 4 * m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsp_congr : ∀ (K₁ K₂ : Submodule ℝ (Amb n ℓ)) [K₁.HasOrthogonalProjection]
      [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection = K₂.starProjection := by
    intro K₁ K₂ _ _ h
    subst h
    rfl
  /- Elementary facts on graph points `(x, y) ∈ ℝⁿ × ℝ^ℓ`. -/
  have hgp_sq : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have hgp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x - x') (y - y') = graphPoint x y - graphPoint x' y' := by
    intro x x' y y'
    ext i
    induction i using Fin.addCases <;> simp [graphPoint]
  have hgp_zero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    ext i
    induction i using Fin.addCases <;> simp [graphPoint]
  have hgp_hor : ∀ x : Rn n, graphPoint x (0 : Rn ℓ) ∈ horizontalPlane n ℓ := by
    intro x
    have hx : graphPoint x (0 : Rn ℓ) =
        ∑ i : Fin n, x i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
      ext j
      induction j using Fin.addCases with
      | left k => simp [graphPoint, Pi.single_apply, Fin.castAdd_inj]
      | right k =>
        simp only [graphPoint, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
          Pi.smul_apply, Fin.append_right]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [Fin.ext_iff]
        omega
    rw [hx]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hgp_le1 : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := by
    intro x y
    have h := hgp_sq x y
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (graphPoint x y), sq_nonneg ‖y‖]
  have hgp_le2 : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ≤ ‖x‖ + ‖y‖ := by
    intro x y
    have h := hgp_sq x y
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (graphPoint x y),
      mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have hgp_norm0 : ∀ y : Rn ℓ, ‖graphPoint (0 : Rn n) y‖ = ‖y‖ := by
    intro y
    have h := hgp_sq 0 y
    rw [norm_zero] at h
    nlinarith [norm_nonneg y, norm_nonneg (graphPoint (0 : Rn n) y)]
  have hgp_eq0 : ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have h := hgp_sq x y
    rw [hxy, norm_zero] at h
    have hx : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    have hy : ‖y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    exact ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hx),
      norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)⟩
  /- Two real inequalities: Young's inequality `t ≤ c + c^{1-p} t^p`, and the comparison of the
  conical integrands in the parameter domain and on the graph. -/
  have young : ∀ s c : ℝ, 0 ≤ s → 0 < c → s ≤ c + c ^ (1 - p) * s ^ p := by
    intro s c hs hc
    rcases le_or_gt s c with hsc | hsc
    · have : 0 ≤ c ^ (1 - p) * s ^ p :=
        mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hs _)
      linarith
    · have hspos : 0 < s := hc.trans hsc
      have h1 : c ^ (p - 1) ≤ s ^ (p - 1) := Real.rpow_le_rpow hc.le hsc.le (by linarith)
      have h2 : s ^ (p - 1) * s = s ^ p := by rw [← Real.rpow_add_one hspos.ne', sub_add_cancel]
      have h3 : c ^ (1 - p) * c ^ (p - 1) = 1 := by
        rw [← Real.rpow_add hc, show 1 - p + (p - 1) = 0 by ring, Real.rpow_zero]
      have h4 : 0 ≤ c ^ (1 - p) := Real.rpow_nonneg hc.le _
      calc s = c ^ (1 - p) * c ^ (p - 1) * s := by rw [h3, one_mul]
        _ ≤ c ^ (1 - p) * s ^ (p - 1) * s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h4) hspos.le
        _ = c ^ (1 - p) * s ^ p := by rw [mul_assoc, h2]
        _ ≤ c + c ^ (1 - p) * s ^ p := by linarith
  have hcone_real : ∀ (a b u v : ℝ), 0 ≤ a → a ≤ 2 * b → 0 ≤ u → u ≤ v → v ≤ 2 * u →
      a ^ 2 / u ^ (n + 2) ≤ 2 ^ (n + 4) * (b ^ 2 / v ^ (n + 2)) := by
    intro a b u v ha hab hu huv hvu
    rcases hu.eq_or_lt with rfl | hu0
    · rw [zero_pow (by omega), div_zero]
      exact mul_nonneg (by positivity) (div_nonneg (sq_nonneg b) (pow_nonneg huv _))
    · have hv0 : 0 < v := hu0.trans_le huv
      have h1 : a ^ 2 ≤ (2 * b) ^ 2 := pow_le_pow_left₀ ha hab 2
      have h2 : v ^ (n + 2) ≤ 2 ^ (n + 2) * u ^ (n + 2) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hv0.le hvu _
      rw [div_le_iff₀ (pow_pos hu0 _)]
      calc a ^ 2 ≤ (2 * b) ^ 2 := h1
        _ = 2 ^ (n + 4) * (b ^ 2 / v ^ (n + 2)) * (v ^ (n + 2) / 2 ^ (n + 2)) := by
            field_simp; ring
        _ ≤ 2 ^ (n + 4) * (b ^ 2 / v ^ (n + 2)) * u ^ (n + 2) := by
            gcongr
            rw [div_le_iff₀ (by positivity)]; linarith
  /- The conical integrand is jointly measurable in the point and the plane. -/
  have hΦ : Measurable (Function.uncurry fun (w : Amb n ℓ) (P : Amb n ℓ →L[ℝ] Amb n ℓ) =>
      ENNReal.ofReal (‖w - P w‖ ^ 2 / ‖w‖ ^ (n + 2))) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)
    · exact ((continuous_fst.sub (continuous_snd.clm_apply continuous_fst)).norm.pow 2).measurable
    · exact (continuous_fst.norm.pow (n + 2)).measurable
  /- The siblings 2.5, 2.7 and the children of this node. -/
  obtain ⟨CA, hCA, hAff⟩ := Submission.affine_approximation_lemma n ℓ hn p hp
  obtain ⟨β, hβ0, hβ1, hLGC⟩ := Submission.lipschitz_graph_corollary n ℓ hn p hp
  obtain ⟨δI, CI, hδI, hCI, hIter⟩ :=
    Submission.allard52_excess_iteration Submission.tilt_excess_decay_theorem n ℓ hn p hp
  obtain ⟨δP, CP, hδP0, hδP1, hCP, hCPδP, hDens⟩ := Submission.allard52_density_bounds n hn p hp
  obtain ⟨δ₂, hδ₂, hComp⟩ := Submission.allard52_graph_comparison n hn p hp
  obtain ⟨Lc, δ₃, Cc, hLc0, hLc1, hδ₃, hCc, hCamp⟩ :=
    Submission.allard52_graph_campanato n ℓ hn p hp
  obtain ⟨CL, hCL, hLemA⟩ := Submission.allard52_tilt_height_l1 n ℓ hn
  obtain ⟨L₀, hL₀0, hL₀1, -, hGPA2, hGPA3, hGPA4, hGPA5, -⟩ :=
    Submission.allard52_graph_plane_algebra n ℓ hn
  /- The norm comparison `‖A‖ ≤ |A|` for maps of `ℝ^{n+ℓ}` (graph algebra in dimension `n + ℓ`). -/
  obtain ⟨-, -, -, -, -, -, hGPA4', -, -⟩ :=
    Submission.allard52_graph_plane_algebra (n + ℓ) (n + ℓ) (by omega)
  /- The Lipschitz constant `L = min{L_c, L₀/√n}` used in 2.7. -/
  obtain ⟨L, hL0, hLLc, hLL₀⟩ : ∃ L : ℝ, 0 < L ∧ L ≤ Lc ∧ Real.sqrt n * L ≤ L₀ := by
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    refine ⟨min Lc (L₀ / Real.sqrt n), lt_min hLc0 (div_pos hL₀0 hsn), min_le_left _ _, ?_⟩
    calc Real.sqrt n * min Lc (L₀ / Real.sqrt n) ≤ Real.sqrt n * (L₀ / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hsn.le
      _ = L₀ := by field_simp
  have hL14 : L ≤ 1 / 4 := hLLc.trans hLc1
  /- The constant of the radial height lemma (Part III). -/
  obtain ⟨CR, hCR, hRad⟩ := Submission.allard52_radial_height n ℓ hn (1 - (n : ℝ) / p)
    (Cc * Real.sqrt CI) (2 ^ (n + 4) * CP * unitBallVolume n) hα0 hα1 (by positivity)
    (by positivity)
  /- Choice of `δ₀` (the book's `δ` of 5.2 fixed in terms of `n, ℓ, p`). -/
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 4 ^ n * CA ^ 2 * (CA + 1) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = 2 * CI + 16 * unitBallVolume n * CI := ⟨_, rfl⟩
  have hC₂1 : 1 ≤ C₂ := by
    have : 0 ≤ 4 ^ n * CA ^ 2 * (CA + 1) ^ 2 := by positivity
    rw [hC₂]; linarith
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  obtain ⟨ε, hε0, hε1, hεβL, hεC₃, hεC₂⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ β * L ∧
      C₃ * (C₂ * ε ^ 2) ≤ β ^ 2 * L ^ 2 ∧ C₂ * ε ^ 2 ≤ 1 := by
    have hD : 1 ≤ C₃ * C₂ + C₂ + 1 := by
      have := mul_nonneg hC₃0 (by linarith : (0 : ℝ) ≤ C₂)
      linarith
    have hm0 : 0 < min 1 (β * L) := lt_min one_pos (mul_pos hβ0 hL0)
    have hεD : min 1 (β * L) / (C₃ * C₂ + C₂ + 1) * (C₃ * C₂ + C₂ + 1) = min 1 (β * L) := by
      field_simp
    have hεm : min 1 (β * L) / (C₃ * C₂ + C₂ + 1) ≤ min 1 (β * L) :=
      div_le_self hm0.le hD
    set e := min 1 (β * L) / (C₃ * C₂ + C₂ + 1) with he
    have he0 : 0 < e := div_pos hm0 (by linarith)
    have he1 : e ≤ 1 := hεm.trans (min_le_left _ _)
    have heβ : e ≤ β * L := hεm.trans (min_le_right _ _)
    refine ⟨e, he0, he1, heβ, ?_, ?_⟩
    · have h := mul_nonneg (by linarith : (0 : ℝ) ≤ C₂ + 1) (sq_nonneg e)
      calc C₃ * (C₂ * e ^ 2) ≤ C₃ * (C₂ * e ^ 2) + (C₂ + 1) * e ^ 2 := le_add_of_nonneg_right h
        _ = (e * (C₃ * C₂ + C₂ + 1)) * e := by ring
        _ = min 1 (β * L) * e := by rw [hεD]
        _ ≤ (β * L) * (β * L) := mul_le_mul (min_le_right _ _) heβ he0.le (by positivity)
        _ = β ^ 2 * L ^ 2 := by ring
    · have h := mul_nonneg (add_nonneg (mul_nonneg hC₃0 (by linarith : (0 : ℝ) ≤ C₂)) zero_le_one)
        (sq_nonneg e)
      calc C₂ * e ^ 2 ≤ C₂ * e ^ 2 + (C₃ * C₂ + 1) * e ^ 2 := le_add_of_nonneg_right h
        _ = (e * (C₃ * C₂ + C₂ + 1)) * e := by ring
        _ = min 1 (β * L) * e := by rw [hεD]
        _ ≤ 1 * 1 := mul_le_mul (min_le_left _ _) he1 he0.le zero_le_one
        _ = 1 := one_mul 1
  obtain ⟨δ₀, hδ₀0, hδ₀14, hδ₀P, hδ₀I, hδ₀2, hδ₀3, hδ₀ε⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧
      δ₀ ≤ δP ∧ δ₀ ≤ δI ∧ δ₀ ≤ δ₂ ∧ δ₀ ≤ δ₃ ∧ δ₀ ≤ ε ^ (2 * n + 2) :=
    ⟨min (min (min (1 / 4) δP) (min δI δ₂)) (min δ₃ (ε ^ (2 * n + 2))),
      lt_min (lt_min (lt_min (by norm_num) hδP0) (lt_min hδI hδ₂)) (lt_min hδ₃ (by positivity)),
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)),
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  /- `t₀ = δ₀^{1/(2n+2)} ≤ ε`. -/
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = δ₀ ^ (1 / (2 * (n : ℝ) + 2)) := ⟨_, rfl⟩
  obtain ⟨ht₀0, ht₀1, hδ₀t₀, hδ₀t₀2⟩ := hrpow δ₀ hδ₀0 (by linarith)
  rw [← ht₀] at ht₀0 ht₀1 hδ₀t₀ hδ₀t₀2
  have ht₀ε : t₀ ≤ ε := by
    have h1 : t₀ ≤ (ε ^ (2 * n + 2)) ^ (1 / (2 * (n : ℝ) + 2)) := by
      rw [ht₀]; exact Real.rpow_le_rpow hδ₀0.le hδ₀ε (by positivity)
    have h2 : (ε ^ (2 * n + 2)) ^ (1 / (2 * (n : ℝ) + 2)) = ε := by
      have : (1 / (2 * (n : ℝ) + 2)) = ((2 * n + 2 : ℕ) : ℝ)⁻¹ := by push_cast; ring
      rw [this, Real.pow_rpow_inv_natCast hε0.le (by omega)]
    rwa [h2] at h1
  have hδ₀β : δ₀ ≤ (β * L) ^ (2 * n + 2) := hδ₀ε.trans (pow_le_pow_left₀ hε0.le hεβL _)
  have ht₀sq : t₀ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ ht₀0.le ht₀ε 2
  have hE₁1 : C₂ * t₀ ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_left ht₀sq (by linarith)).trans hεC₂
  have hC₃E₁ : C₃ * (C₂ * t₀ ^ 2) ≤ β ^ 2 * L ^ 2 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht₀sq (by linarith)) hC₃0).trans hεC₃
  /- The constants of Part III and of the conclusion. -/
  obtain ⟨C₉, hC₉⟩ : ∃ C₉ : ℝ, C₉ = 8 * 2 ^ n * CL * CR ^ 2 * unitBallVolume n +
      4 * CL * CR * (2 * unitBallVolume n + 1) * (256 / δ₀) ^ n * (δ₀ / 256) := ⟨_, rfl⟩
  have hC₉0 : 0 ≤ C₉ := by rw [hC₉]; positivity
  obtain ⟨C₁₀, hC₁₀⟩ : ∃ C₁₀ : ℝ, C₁₀ = C₉ + δ₀⁻¹ := ⟨_, rfl⟩
  have hC₁₀0 : 0 ≤ C₁₀ := by rw [hC₁₀]; positivity
  refine ⟨δ₀, δ₀ / 8192, CR * (δ₀ / 8192) + Real.sqrt (CI * C₁₀) +
      Cc * Real.sqrt (CI * C₁₀) * (256 / δ₀) ^ (1 - (n : ℝ) / p),
    hδ₀0, by linarith, by positivity, by linarith, ?_⟩
  intro U hU V H δ ρ hδ hδδ₀ hyp
  obtain ⟨hρ, hHmc, hmult, h0spt, hBU, hmass, hKρ⟩ := id hyp
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ ^ (1 / (2 * (n : ℝ) + 2)) := ⟨_, rfl⟩
  obtain ⟨ht0, ht1, hδt, hδt2⟩ := hrpow δ hδ hδ1
  rw [← ht] at ht0 ht1 hδt hδt2
  /- 2.3 with `δ ≤ δ₀` implies 2.3 with `δ₀`. -/
  have hyp₀ : V.AllardHypotheses H p δ₀ ρ := by
    refine ⟨hρ, hHmc, hmult, h0spt, hBU, hmass.trans (ENNReal.ofReal_le_ofReal ?_),
      hKρ.trans (ENNReal.ofReal_le_ofReal hδδ₀)⟩
    have : 0 ≤ unitBallVolume n * ρ ^ n := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have hδρ : 0 < δ₀ * ρ := mul_pos hδ₀0 hρ
  have hδ₀ρ : δ₀ * ρ ≤ ρ / 4 := by
    calc δ₀ * ρ ≤ 1 / 4 * ρ := mul_le_mul_of_nonneg_right hδ₀14 hρ.le
      _ = ρ / 4 := by ring
  have hs_cont : ∀ (P : Amb n ℓ →L[ℝ] Amb n ℓ),
      Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq (A - P) := by
    intro P
    unfold hsNormSq
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_id.sub continuous_const).clm_apply continuous_const).norm).pow 2
  /- Tangent projections are bounded and measurable, so tilt integrands are integrable on sets of
  finite measure. -/
  have htp_norm : ∀ x, ‖V.tangentProj x‖ ≤ 1 := by
    intro x
    unfold RectifiableVarifold.tangentProj
    split_ifs with h
    · exact Submodule.starProjection_norm_le _
    · simp
  have htan_meas : AEStronglyMeasurable V.tangentProj V.weight :=
    (Submission.allard52_tangent_ae n ℓ hn U hU V).1
  have htilt_int : ∀ (P : Submodule ℝ (Amb n ℓ)) (s : Set (Amb n ℓ)), V.weight s ≠ ∞ →
      IntegrableOn (fun x => hsNormSq (V.tangentProj x - P.starProjection)) s V.weight := by
    intro P s hs
    refine Measure.integrableOn_of_bounded (M := 4 * ((n + ℓ : ℕ) : ℝ)) hs
      ((hs_cont P.starProjection).comp_aestronglyMeasurable htan_meas) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (hs_nonneg _)]
    exact hs_bound _ _ (htp_norm x) (Submodule.starProjection_norm_le _)
  /- `μ_V`-almost every point lies in `spt V`. -/
  have hae_spt : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
    have h2 : ∀ᵐ x ∂V.weight, x ∈ V.carrier := by
      have : ∀ᵐ x ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier), x ∈ V.carrier :=
        ae_restrict_mem₀ V.nullMeasurableSet_carrier
      exact (withDensity_absolutelyContinuous _ _).ae_le this
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨V.carrier_subset hx2, hx1⟩
  /- Balls. -/
  have hball_sub : ∀ (ξ : Amb n ℓ) (σ R : ℝ), ‖ξ‖ + σ ≤ R → closedBall ξ σ ⊆ closedBall 0 R :=
    fun ξ σ R h => closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  /- (P.i) with `δ₀`: masses of small balls near `0`. -/
  have hdens₀ := hDens ℓ U hU V H δ₀ ρ hδ₀0 hδ₀P hyp₀
  have hmeas_fin : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ₀ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 →
      V.weight (closedBall y s) ≠ ∞ := fun y hy s hs hsρ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdens₀ y hy s hs hsρ).1
  have hmeas_real : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ₀ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 →
      V.weight.real (closedBall y s) ≤ 2 * unitBallVolume n * s ^ n := by
    intro y hy s hs hsρ
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((hdens₀ y hy s hs hsρ).1.trans (ENNReal.ofReal_le_ofReal ?_))
    have h1 : CP * δ₀ ≤ 1 := (mul_le_mul_of_nonneg_left hδ₀P hCP.le).trans (by linarith)
    have : 0 ≤ unitBallVolume n * s ^ n := by positivity
    calc (1 + CP * δ₀) * (unitBallVolume n * s ^ n) ≤ 2 * (unitBallVolume n * s ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith) this
      _ = 2 * unitBallVolume n * s ^ n := by ring
  /- The scaled `Lᵖ` norm of `H` on balls inside `B_ρ(0)` is at most `δ`. -/
  have hKmono : ∀ (ξ : Amb n ℓ) (σ : ℝ), 0 < σ → σ ≤ ρ → closedBall ξ σ ⊆ closedBall 0 ρ →
      V.scaledLpNorm H p ξ σ ≤ ENNReal.ofReal δ := by
    intro ξ σ hσ hσρ hsub
    refine le_trans ?_ hKρ
    unfold RectifiableVarifold.scaledLpNorm
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hσ.le hσρ (by linarith)))
      (lintegral_mono_set hsub)
  have hEstar : ∀ (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) (X : ℝ), 0 < σ → σ ≤ ρ →
      closedBall ξ σ ⊆ closedBall 0 ρ → V.tiltExcess ξ σ T ≤ X →
      V.tiltExcessStar H p δ₀ ξ σ T ≤ max X (δ₀⁻¹ * δ ^ 2) := by
    intro ξ σ T X h1 h2 h3 hX
    unfold RectifiableVarifold.tiltExcessStar
    refine max_le_max hX (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal hδ.le (hKmono ξ σ h1 h2 h3)) 2
  /- Triangle inequality for the tilt-excess. -/
  have htri : ∀ (ξ : Amb n ℓ) (s : ℝ) (S₁ S₂ : Submodule ℝ (Amb n ℓ)), 0 < s →
      V.weight (closedBall ξ s) ≠ ∞ →
      V.tiltExcess ξ s S₂ ≤ 2 * V.tiltExcess ξ s S₁ +
        2 * ((s ^ n)⁻¹ * V.weight.real (closedBall ξ s)) *
          hsNormSq (S₁.starProjection - S₂.starProjection) := by
    intro ξ s S₁ S₂ hs hfin
    unfold RectifiableVarifold.tiltExcess
    have hint1 := htilt_int S₁ (closedBall ξ s) hfin
    have hint2 := htilt_int S₂ (closedBall ξ s) hfin
    have hconst : IntegrableOn (fun _ => hsNormSq (S₁.starProjection - S₂.starProjection))
        (closedBall ξ s) V.weight := integrableOn_const hfin
    have hle : ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - S₂.starProjection) ∂V.weight ≤
        ∫ x in closedBall ξ s, (2 * hsNormSq (V.tangentProj x - S₁.starProjection) +
          2 * hsNormSq (S₁.starProjection - S₂.starProjection)) ∂V.weight := by
      refine integral_mono hint2 ((hint1.const_mul 2).add (hconst.const_mul 2)) fun x => ?_
      have := hs_add (V.tangentProj x - S₁.starProjection) (S₁.starProjection - S₂.starProjection)
      rwa [sub_add_sub_cancel] at this
    rw [integral_add (hint1.const_mul 2) (hconst.const_mul 2), integral_const_mul,
      integral_const_mul, setIntegral_const, smul_eq_mul] at hle
    have hsn : 0 < s ^ n := pow_pos hs n
    calc (s ^ n)⁻¹ * ∫ x in closedBall ξ s, hsNormSq (V.tangentProj x - S₂.starProjection) ∂V.weight
        ≤ (s ^ n)⁻¹ * (2 * ∫ x in closedBall ξ s,
            hsNormSq (V.tangentProj x - S₁.starProjection) ∂V.weight +
            2 * (V.weight.real (closedBall ξ s) *
              hsNormSq (S₁.starProjection - S₂.starProjection))) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hsn.le)
      _ = _ := by ring
  /- **Step 2.** Lemma 2.5 at `(0, 2δ₀ρ)` gives the plane `T*`. -/
  have h0mem : (0 : Amb n ℓ) ∈ V.support ∩ closedBall 0 (δ₀ * ρ) :=
    ⟨h0spt, mem_closedBall_self hδρ.le⟩
  obtain ⟨Tst, hTst, hTst_tilt, hTst_ht⟩ :=
    hAff U hU V H δ₀ ρ hδ₀0 hδ₀14 hyp₀ 0 h0mem (2 * δ₀ * ρ) (by positivity) le_rfl
  rw [← ht₀] at hTst_ht
  have hTst_dist : ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ₀ * ρ)),
      infDist x (Tst : Set (Amb n ℓ)) ≤ 2 * CA * t₀ * (δ₀ * ρ) := by
    intro x hx
    have h1 : ENNReal.ofReal (infDist (x - 0) (Tst : Set (Amb n ℓ))) ≤
        V.heightSup 0 (2 * δ₀ * ρ) Tst := by
      unfold RectifiableVarifold.heightSup
      refine le_iSup₂_of_le (f := fun x (_ : x ∈ V.support ∩ closedBall 0 (2 * δ₀ * ρ)) =>
        ENNReal.ofReal (infDist (x - 0) (Tst : Set (Amb n ℓ)))) x ⟨hx.1, ?_⟩ le_rfl
      have := hx.2
      rwa [show 2 * (δ₀ * ρ) = 2 * δ₀ * ρ by ring] at this
    have h2 := (mul_le_mul_right h1 (ENNReal.ofReal (2 * δ₀ * ρ)⁻¹)).trans hTst_ht
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
      sub_zero, inv_mul_le_iff₀ (by positivity)] at h2
    calc infDist x (Tst : Set (Amb n ℓ)) ≤ 2 * δ₀ * ρ * (CA * t₀) := h2
      _ = 2 * CA * t₀ * (δ₀ * ρ) := by ring
  have hTst_X : ((2 * δ₀ * ρ) ^ n)⁻¹ * ∫ x in closedBall 0 (δ₀ * ρ),
      hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight ≤ (CA * (CA + 1) * t₀) ^ 2 := by
    have hK2 : V.scaledLpNorm H p 0 (2 * δ₀ * ρ) ≤ ENNReal.ofReal δ₀ :=
      (hKmono 0 (2 * δ₀ * ρ) (by positivity) (by linarith)
        (hball_sub 0 _ _ (by rw [norm_zero]; linarith))).trans (ENNReal.ofReal_le_ofReal hδδ₀)
    have h1 := hTst_tilt.trans (add_le_add hTst_ht hK2)
    rw [← ENNReal.ofReal_add (by positivity) hδ₀0.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity), show 2 * δ₀ * ρ / 2 = δ₀ * ρ by ring] at h1
    rw [inv_mul_le_iff₀ hCA] at h1
    refine (Real.sqrt_le_left (by positivity)).1 (h1.trans ?_)
    have : CA * (CA * t₀ + δ₀) ≤ CA * (CA * t₀ + t₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hCA.le
    linarith
  have hTst_E : ∀ ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2),
      V.tiltExcess ξ (δ₀ * ρ / 2) Tst ≤ 4 ^ n * (CA * (CA + 1) * t₀) ^ 2 := by
    intro ξ hξ
    have hξn : ‖ξ‖ ≤ δ₀ * ρ / 2 := mem_closedBall_zero_iff.1 hξ.2
    unfold RectifiableVarifold.tiltExcess
    have hsub : closedBall ξ (δ₀ * ρ / 2) ⊆ closedBall 0 (δ₀ * ρ) := hball_sub ξ _ _ (by linarith)
    have hint := htilt_int Tst (closedBall 0 (δ₀ * ρ))
      (hmeas_fin 0 (by rw [norm_zero]; positivity) _ hδρ (by linarith))
    have hmono : ∫ x in closedBall ξ (δ₀ * ρ / 2),
        hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight ≤
        ∫ x in closedBall 0 (δ₀ * ρ), hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight :=
      setIntegral_mono_set hint (Eventually.of_forall fun x => hs_nonneg _) hsub.eventuallyLE
    have hpow : (2 * δ₀ * ρ) ^ n = 4 ^ n * (δ₀ * ρ / 2) ^ n := by
      rw [← mul_pow]; congr 1; ring
    have hpos : 0 < (δ₀ * ρ / 2) ^ n := by positivity
    calc ((δ₀ * ρ / 2) ^ n)⁻¹ * ∫ x in closedBall ξ (δ₀ * ρ / 2),
          hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight
        ≤ ((δ₀ * ρ / 2) ^ n)⁻¹ * ∫ x in closedBall 0 (δ₀ * ρ),
          hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 4 ^ n * (((2 * δ₀ * ρ) ^ n)⁻¹ * ∫ x in closedBall 0 (δ₀ * ρ),
          hsNormSq (V.tangentProj x - Tst.starProjection) ∂V.weight) := by
          rw [hpow]; field_simp
      _ ≤ 4 ^ n * (CA * (CA + 1) * t₀) ^ 2 := mul_le_mul_of_nonneg_left hTst_X (by positivity)
  have hTst_Estar : ∀ ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2),
      V.tiltExcessStar H p δ₀ ξ (δ₀ * ρ / 2) Tst ≤ C₂ * t₀ ^ 2 := by
    intro ξ hξ
    have hξn : ‖ξ‖ ≤ δ₀ * ρ / 2 := mem_closedBall_zero_iff.1 hξ.2
    refine (hEstar ξ _ Tst _ (by positivity) (by linarith) (hball_sub ξ _ _ (by linarith))
      (hTst_E ξ hξ)).trans (max_le ?_ ?_)
    · have : C₂ * t₀ ^ 2 = 4 ^ n * (CA * (CA + 1) * t₀) ^ 2 + t₀ ^ 2 := by rw [hC₂]; ring
      rw [this]; linarith [sq_nonneg t₀]
    · have h1 : δ₀⁻¹ * δ ^ 2 ≤ δ₀ := by
        rw [inv_mul_le_iff₀ hδ₀0, sq]
        exact mul_le_mul hδδ₀ hδδ₀ hδ.le hδ₀0.le
      have h2 : t₀ ^ 2 ≤ C₂ * t₀ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hC₂1
      linarith
  /- **Step 3.** Iterating 4.5 at every `ξ ∈ spt V ∩ B_{δ₀ρ/2}(0)` gives the planes `S(ξ)`. -/
  have hIter₁ : ∀ ξ : Amb n ℓ, ∃ S : Submodule ℝ (Amb n ℓ),
      ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2) →
      Module.finrank ℝ S = n ∧
        hsNormSq (S.starProjection - Tst.starProjection) ≤ CI * (C₂ * t₀ ^ 2) ∧
      ∀ s : ℝ, 0 < s → s ≤ δ₀ * ρ / 2 →
        V.tiltExcess ξ s S ≤ CI * (s / (δ₀ * ρ / 2)) ^ (2 * (1 - (n : ℝ) / p)) * (C₂ * t₀ ^ 2) := by
    intro ξ
    by_cases hξ : ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2)
    · have hξ' : ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ) :=
        ⟨hξ.1, closedBall_subset_closedBall (by linarith) hξ.2⟩
      obtain ⟨S, hS1, hS2, hS3⟩ := hIter U hU V H δ₀ ρ hδ₀0 hδ₀I hyp₀ ξ hξ' (δ₀ * ρ / 2)
        (by positivity) le_rfl Tst hTst
      have hE := hTst_Estar ξ hξ
      exact ⟨S, fun _ => ⟨hS1, hS2.trans (mul_le_mul_of_nonneg_left hE hCI), fun s hs hs' =>
        (hS3 s hs hs').trans (mul_le_mul_of_nonneg_left hE
          (mul_nonneg hCI (Real.rpow_nonneg (by positivity) _)))⟩⟩
    · exact ⟨⊥, fun h => absurd h hξ⟩
  choose S hS using hIter₁
  have h0mem' : (0 : Amb n ℓ) ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2) :=
    ⟨h0spt, mem_closedBall_self (by positivity)⟩
  obtain ⟨hT₀dim, hT₀Tst, -⟩ := hS 0 h0mem'
  obtain ⟨q₀, hq₀⟩ := hGPA5 (S 0) hT₀dim
  have hCIC₂ : 0 ≤ CI * C₂ := mul_nonneg hCI (by linarith)
  have hheight : ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ₀ * ρ)),
      infDist x (rotatedPlane q₀ : Set (Amb n ℓ)) ≤
        (2 * CA + 2 * Real.sqrt (CI * C₂)) * δ₀ ^ (1 / (2 * (n : ℝ) + 2)) * (δ₀ * ρ) := by
    intro x hx
    rw [hq₀, ← ht₀]
    have hxn : ‖x‖ ≤ 2 * (δ₀ * ρ) := mem_closedBall_zero_iff.1 hx.2
    have h1 : infDist x (S 0 : Set (Amb n ℓ)) ≤ ‖x - (S 0).starProjection x‖ := by
      rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ((S 0).starProjection_apply_mem x)
    have h2 : ‖x - Tst.starProjection x‖ = infDist x (Tst : Set (Amb n ℓ)) := by
      rw [← dist_eq_norm]; exact Tst.dist_starProjection_eq_infDist x
    have h3 : ‖(Tst.starProjection - (S 0).starProjection) x‖ ≤
        Real.sqrt (CI * C₂) * t₀ * (2 * (δ₀ * ρ)) := by
      calc _ ≤ ‖Tst.starProjection - (S 0).starProjection‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ hsNorm (Tst.starProjection - (S 0).starProjection) * ‖x‖ := by
            gcongr; exact (hGPA4' _).1
        _ ≤ (Real.sqrt (CI * C₂) * t₀) * (2 * (δ₀ * ρ)) := by
            gcongr
            unfold hsNorm
            rw [hs_symm]
            calc Real.sqrt (hsNormSq ((S 0).starProjection - Tst.starProjection))
                ≤ Real.sqrt (CI * (C₂ * t₀ ^ 2)) := Real.sqrt_le_sqrt hT₀Tst
              _ = Real.sqrt (CI * C₂) * t₀ := by
                  rw [← mul_assoc, Real.sqrt_mul hCIC₂, Real.sqrt_sq ht₀0.le]
    have h4 := hTst_dist x hx
    calc infDist x (S 0 : Set (Amb n ℓ)) ≤ ‖x - (S 0).starProjection x‖ := h1
      _ = ‖(x - Tst.starProjection x) + (Tst.starProjection - (S 0).starProjection) x‖ := by
          rw [sub_apply]; congr 1; abel
      _ ≤ ‖x - Tst.starProjection x‖ + ‖(Tst.starProjection - (S 0).starProjection) x‖ :=
          norm_add_le _ _
      _ ≤ 2 * CA * t₀ * (δ₀ * ρ) + Real.sqrt (CI * C₂) * t₀ * (2 * (δ₀ * ρ)) := by
          rw [h2]; linarith
      _ = (2 * CA + 2 * Real.sqrt (CI * C₂)) * t₀ * (δ₀ * ρ) := by ring
  have htilt7 : ∀ ξ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ₀ * ρ / 2 →
      V.tiltExcess ξ σ (rotatedPlane q₀) ≤ β ^ 2 * L ^ 2 := by
    intro ξ hξ σ hσ hσ'
    rw [hq₀]
    have hξn : ‖ξ‖ ≤ δ₀ * ρ / 2 := mem_closedBall_zero_iff.1 hξ.2
    obtain ⟨-, hSξ2, hSξ3⟩ := hS ξ hξ
    have hfin := hmeas_fin ξ (by linarith) σ hσ (by linarith)
    have hreal := hmeas_real ξ (by linarith) σ hσ (by linarith)
    have h1 := htri ξ σ (S ξ) (S 0) hσ hfin
    have h2 : V.tiltExcess ξ σ (S ξ) ≤ CI * (C₂ * t₀ ^ 2) := by
      refine (hSξ3 σ hσ hσ').trans ?_
      have : (σ / (δ₀ * ρ / 2)) ^ (2 * (1 - (n : ℝ) / p)) ≤ 1 :=
        Real.rpow_le_one (by positivity) (by rw [div_le_one (by positivity)]; exact hσ')
          (by positivity)
      calc CI * (σ / (δ₀ * ρ / 2)) ^ (2 * (1 - (n : ℝ) / p)) * (C₂ * t₀ ^ 2)
          ≤ CI * 1 * (C₂ * t₀ ^ 2) := by gcongr
        _ = CI * (C₂ * t₀ ^ 2) := by ring
    have h3 : hsNormSq ((S ξ).starProjection - (S 0).starProjection) ≤
        4 * (CI * (C₂ * t₀ ^ 2)) := by
      have := hs_add ((S ξ).starProjection - Tst.starProjection)
        (Tst.starProjection - (S 0).starProjection)
      rw [sub_add_sub_cancel, hs_symm Tst.starProjection] at this
      linarith
    have h4 : (σ ^ n)⁻¹ * V.weight.real (closedBall ξ σ) ≤ 2 * unitBallVolume n := by
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    have h5 : 0 ≤ (σ ^ n)⁻¹ * V.weight.real (closedBall ξ σ) := by positivity
    calc V.tiltExcess ξ σ (S 0) ≤ 2 * V.tiltExcess ξ σ (S ξ) +
          2 * ((σ ^ n)⁻¹ * V.weight.real (closedBall ξ σ)) *
            hsNormSq ((S ξ).starProjection - (S 0).starProjection) := h1
      _ ≤ 2 * (CI * (C₂ * t₀ ^ 2)) + 2 * (2 * unitBallVolume n) * (4 * (CI * (C₂ * t₀ ^ 2))) := by
          gcongr
          · exact hs_nonneg _
      _ = C₃ * (C₂ * t₀ ^ 2) := by rw [hC₃]; ring
      _ ≤ β ^ 2 * L ^ 2 := hC₃E₁
  /- **Step 3, end.** Corollary 2.7 makes `spt V` a Lipschitz graph over `B_{δ₀ρ/4}`. -/
  obtain ⟨f, hfLip, -, hgraph⟩ := hLGC L (2 * CA + 2 * Real.sqrt (CI * C₂)) hL0 (by linarith)
    (by positivity) U hU V H δ₀ ρ hδ₀0 hδ₀β hyp₀ q₀ hheight htilt7
  /- Radii: `R₂ = δ₀ρ/4` (the graph), `R₃ = R₂/16`, `R' = R₃/4`. -/
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = δ₀ * ρ / 4 := ⟨_, rfl⟩
  rw [← hR₂] at hfLip hgraph
  have hR₂0 : 0 < R₂ := by rw [hR₂]; positivity
  have hR₂le : R₂ ≤ δ₀ * ρ := by rw [hR₂]; linarith
  /- **Step 4.** Properties of the Lipschitz graph. -/
  have hf0 : f 0 = 0 := by
    have h0in : (0 : Amb n ℓ) ∈ V.support ∩ closedBall 0 R₂ := ⟨h0spt, mem_closedBall_self hR₂0.le⟩
    rw [hgraph] at h0in
    obtain ⟨⟨w, ⟨x, -, rfl⟩, hw⟩, -⟩ := h0in
    have hg : graphPoint x (f x) = 0 := by
      have := congrArg q₀.symm hw
      simpa using this
    obtain ⟨hx0, hfx0⟩ := hgp_eq0 x (f x) hg
    rwa [hx0] at hfx0
  have hfLip1 : LipschitzOnWith 1 f (closedBall 0 R₂) :=
    hfLip.weaken (Real.toNNReal_le_one.2 (by linarith))
  have hfLipc : LipschitzOnWith (Real.toNNReal Lc) f (closedBall 0 R₂) :=
    hfLip.weaken (Real.toNNReal_le_toNNReal hLLc)
  have hfnorm : ∀ x ∈ closedBall (0 : Rn n) R₂, ‖f x‖ ≤ ‖x‖ := by
    intro x hx
    have := hfLip1.norm_sub_le hx (mem_closedBall_self hR₂0.le)
    rwa [hf0, sub_zero, sub_zero, NNReal.coe_one, one_mul] at this
  have hF : ∀ x ∈ closedBall (0 : Rn n) R₂,
      ‖x‖ ≤ ‖q₀ (graphPoint x (f x))‖ ∧ ‖q₀ (graphPoint x (f x))‖ ≤ 2 * ‖x‖ := by
    intro x hx
    rw [LinearIsometryEquiv.norm_map]
    exact ⟨hgp_le1 x (f x), (hgp_le2 x (f x)).trans (by linarith [hfnorm x hx])⟩
  have hDf : ∀ x ∈ ball (0 : Rn n) R₂, ‖fderiv ℝ f x‖ ≤ L := by
    intro x hx
    have := norm_fderiv_le_of_lipschitzOn ℝ
      (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hfLip
    rwa [Real.coe_toNNReal _ hL0.le] at this
  have hDfHS : ∀ x ∈ ball (0 : Rn n) R₂, hsNorm (fderiv ℝ f x) ≤ L₀ := fun x hx =>
    (hGPA4 _).2.trans ((mul_le_mul_of_nonneg_left (hDf x hx) (Real.sqrt_nonneg _)).trans hLL₀)
  have hgraph_pt : ∀ w ∈ V.support, ‖w‖ ≤ R₂ →
      ∃ x : Rn n, x ∈ closedBall 0 R₂ ∧ q₀ (graphPoint x (f x)) = w ∧ ‖x‖ ≤ ‖w‖ := by
    intro w hw hwn
    have hw' : w ∈ V.support ∩ closedBall 0 R₂ := ⟨hw, mem_closedBall_zero_iff.2 hwn⟩
    rw [hgraph] at hw'
    obtain ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, -⟩ := hw'
    exact ⟨x, hx, rfl, (hF x hx).1⟩
  have hgraph_mem : ∀ x ∈ closedBall (0 : Rn n) R₂, ‖q₀ (graphPoint x (f x))‖ ≤ R₂ →
      q₀ (graphPoint x (f x)) ∈ V.support := by
    intro x hx hxn
    have : q₀ (graphPoint x (f x)) ∈ q₀ '' graphOver f (closedBall 0 R₂) ∩ closedBall 0 R₂ :=
      ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, mem_closedBall_zero_iff.2 hxn⟩
    rw [← hgraph] at this
    exact this.1
  have hgraph_r : ∀ r : ℝ, r ≤ R₂ →
      V.support ∩ closedBall 0 r = q₀ '' graphOver f (closedBall 0 r) ∩ closedBall 0 r := by
    intro r hr
    ext w
    constructor
    · rintro ⟨hwV, hwr⟩
      have hwn : ‖w‖ ≤ r := mem_closedBall_zero_iff.1 hwr
      obtain ⟨x, -, rfl, hxw⟩ := hgraph_pt w hwV (hwn.trans hr)
      exact ⟨⟨_, ⟨x, mem_closedBall_zero_iff.2 (hxw.trans hwn), rfl⟩, rfl⟩, hwr⟩
    · rintro ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hwr⟩
      have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.1 hx
      exact ⟨hgraph_mem x (mem_closedBall_zero_iff.2 (hxr.trans hr))
        ((mem_closedBall_zero_iff.1 hwr).trans hr), hwr⟩
  have hgp_dist : ∀ (x : Rn n) (y : Rn ℓ),
      infDist (q₀ (graphPoint x y)) (S 0 : Set (Amb n ℓ)) ≤ ‖y‖ := by
    intro x y
    have hmem : q₀ (graphPoint x 0) ∈ (S 0 : Set (Amb n ℓ)) := by
      rw [← hq₀]
      exact Submodule.mem_map_of_mem (hgp_hor x)
    refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
    rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, ← hgp_sub, sub_self, sub_zero]
    exact hgp_norm0 y
  /- The first Campanato application (decay data from Part I with `A = C_I E₁`). -/
  have hcamp1_hyp : ∀ ζ ∈ V.support ∩ closedBall 0 (R₂ / 2), Module.finrank ℝ (S ζ) = n ∧
      ∀ s : ℝ, 0 < s → s ≤ R₂ / 2 →
        V.tiltExcess ζ s (S ζ) ≤ CI * (C₂ * t₀ ^ 2) * (s / R₂) ^ (2 * (1 - (n : ℝ) / p)) := by
    intro ζ hζ
    have hζ' : ζ ∈ V.support ∩ closedBall 0 (δ₀ * ρ / 2) :=
      ⟨hζ.1, closedBall_subset_closedBall (by rw [hR₂]; linarith) hζ.2⟩
    obtain ⟨h1, -, h3⟩ := hS ζ hζ'
    refine ⟨h1, fun s hs hs' => (h3 s hs (by rw [hR₂] at hs'; linarith)).trans ?_⟩
    have hle : (s / (δ₀ * ρ / 2)) ^ (2 * (1 - (n : ℝ) / p)) ≤
        (s / R₂) ^ (2 * (1 - (n : ℝ) / p)) :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hs.le hR₂0 (by rw [hR₂]; linarith)) (by positivity)
    calc CI * (s / (δ₀ * ρ / 2)) ^ (2 * (1 - (n : ℝ) / p)) * (C₂ * t₀ ^ 2)
        ≤ CI * (s / R₂) ^ (2 * (1 - (n : ℝ) / p)) * (C₂ * t₀ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hCI) (by positivity)
      _ = CI * (C₂ * t₀ ^ 2) * (s / R₂) ^ (2 * (1 - (n : ℝ) / p)) := by ring
  obtain ⟨hC1, hHol1, hPlane1⟩ := hCamp U hU V H δ₀ ρ hδ₀0 hδ₀3 hyp₀ q₀ f R₂ hR₂0 hR₂le hf0
    hfLipc hgraph S (CI * (C₂ * t₀ ^ 2)) (mul_nonneg hCI (by positivity)) hcamp1_hyp
  /- `Df(0) = 0`: the tangent plane at `0` is `S(0) = T₀ = q₀(ℝⁿ × {0})`. -/
  have hDf0 : fderiv ℝ f 0 = 0 := by
    have hpl := hPlane1 0 (mem_ball_self (by positivity))
    rw [hf0, hgp_zero, map_zero] at hpl
    have h1 := hGPA2 q₀ (fderiv ℝ f 0) (hDfHS 0 (mem_ball_self hR₂0))
    rw [hsp_congr _ _ hpl, hsp_congr _ _ hq₀, sub_self, hs_zero] at h1
    have h2 : hsNorm (fderiv ℝ f 0) = 0 := by
      unfold hsNorm; exact Real.sqrt_eq_zero'.2 h1
    have h3 := (hGPA4 (fderiv ℝ f 0)).1
    rw [h2] at h3
    exact norm_le_zero_iff.1 h3
  /- **Part III, steps 5–6.** The conical excess at `0` bounds the height of the graph. -/
  obtain ⟨R₃, hR₃⟩ : ∃ R₃ : ℝ, R₃ = R₂ / 16 := ⟨_, rfl⟩
  rw [← hR₃] at hC1 hHol1 hPlane1
  have hR₃0 : 0 < R₃ := by rw [hR₃]; positivity
  have hcomp := hComp ℓ U hU V H δ₀ ρ hδ₀0 hδ₀2 hyp₀ q₀ f R₂ hR₂0 hR₂le hf0 hfLip1 hgraph
    (fun w P => ENNReal.ofReal (‖w - P w‖ ^ 2 / ‖w‖ ^ (n + 2))) hΦ (ball 0 R₃) measurableSet_ball
    (ball_subset_ball (by rw [hR₃]; linarith))
  have hconical := ((hDens ℓ U hU V H δ ρ hδ (hδδ₀.trans hδ₀P) hyp 0
    (by rw [norm_zero]; positivity) (ρ / 2) (by positivity) le_rfl).2 h0spt).2
  simp only [sub_zero] at hconical
  have himg : q₀ '' graphOver f (ball 0 R₃) ⊆ closedBall 0 (ρ / 2) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxn : ‖x‖ < R₃ := mem_ball_zero_iff.1 hx
    have hxb : x ∈ closedBall (0 : Rn n) R₂ :=
      mem_closedBall_zero_iff.2 (by rw [hR₃] at hxn; linarith)
    rw [mem_closedBall_zero_iff]
    have := (hF x hxb).2
    rw [hR₃, hR₂] at hxn
    linarith
  have hpt : ∀ x ∈ ball (0 : Rn n) R₃,
      ENNReal.ofReal (‖f x - fderiv ℝ f x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤
        ENNReal.ofReal (2 ^ (n + 4)) * ENNReal.ofReal (‖q₀ (graphPoint x (f x)) -
          ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
            q₀.toLinearEquiv.toLinearMap).starProjection (q₀ (graphPoint x (f x)))‖ ^ 2 /
          ‖q₀ (graphPoint x (f x))‖ ^ (n + 2)) := by
    intro x hx
    have hxn : ‖x‖ < R₃ := mem_ball_zero_iff.1 hx
    have hxR₂ : x ∈ ball (0 : Rn n) R₂ := mem_ball_zero_iff.2 (by rw [hR₃] at hxn; linarith)
    have hxb : x ∈ closedBall (0 : Rn n) R₂ := ball_subset_closedBall hxR₂
    have h3 := hGPA3 q₀ (fderiv ℝ f x) x (f x) ((hDf x hxR₂).trans (by linarith))
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hcone_real _ _ _ _ (norm_nonneg _) h3 (norm_nonneg _)
      (hF x hxb).1 (hF x hxb).2)
  have hconeR : ∫⁻ x in ball (0 : Rn n) R₃,
      ENNReal.ofReal (‖f x - fderiv ℝ f x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤
        ENNReal.ofReal (2 ^ (n + 4) * CP * unitBallVolume n * δ) := by
    refine (setLIntegral_mono' measurableSet_ball hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right hcomp _).trans ?_
    refine (mul_le_mul_right (lintegral_mono_set himg) _).trans ?_
    refine (mul_le_mul_right hconical _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hDbound : ∀ x ∈ ball (0 : Rn n) R₃, hsNorm (fderiv ℝ f x) ≤
      Cc * Real.sqrt CI * (‖x‖ / R₃) ^ (1 - (n : ℝ) / p) := by
    intro x hx
    have h1 := hHol1 x hx 0 (mem_ball_self hR₃0)
    rw [hDf0] at h1
    simp only [sub_zero] at h1
    refine h1.trans ?_
    have hsq : Real.sqrt (CI * (C₂ * t₀ ^ 2)) ≤ Real.sqrt CI :=
      Real.sqrt_le_sqrt (by have := mul_le_mul_of_nonneg_left hE₁1 hCI; linarith)
    have hpow : (‖x‖ / R₂) ^ (1 - (n : ℝ) / p) ≤ (‖x‖ / R₃) ^ (1 - (n : ℝ) / p) :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left (norm_nonneg _) hR₃0 (by rw [hR₃]; linarith)) hα0.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsq hCc) hpow (by positivity) (by positivity)
  have hfLipR₃ : LipschitzOnWith 1 f (ball 0 R₃) :=
    hfLip1.mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by rw [hR₃]; linarith)))
  have hH := hRad f R₃ δ hR₃0 hδ hδ1 hf0 hC1 hfLipR₃ hDbound hconeR
  rw [← ht] at hH
  /- **Step 7.** Lemma A gives tilt `O(δ^{1/(n+1)})` at the fixed scale `R'`. -/
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = R₃ / 4 := ⟨_, rfl⟩
  have hR'0 : 0 < R' := by rw [hR']; positivity
  have hR'ρ : R' = δ₀ * ρ / 256 := by rw [hR', hR₃, hR₂]; ring
  have hR₃R' : R₃ = 4 * R' := by rw [hR']; ring
  have hHint : IntegrableOn H (closedBall 0 ρ) V.weight :=
    hHmc.1.integrableOn_compact_subset hBU (isCompact_closedBall _ _)
  have hHbound : ∫ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ ∂V.weight ≤
      (2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ := by
    obtain ⟨I, hIdef⟩ : ∃ I, I = ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight :=
      ⟨_, rfl⟩
    have hI : I ≤ ENNReal.ofReal (ρ ^ ((n : ℝ) - p) * δ ^ p) := by
      have h1 : ENNReal.ofReal (ρ ^ (p - n)) * I ≤ ENNReal.ofReal (δ ^ p) := by
        have := ENNReal.rpow_le_rpow hKρ hp0.le
        unfold RectifiableVarifold.scaledLpNorm at this
        rwa [one_div, ENNReal.rpow_inv_rpow hp0.ne', ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le,
          ← hIdef] at this
      calc I = ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * (ENNReal.ofReal (ρ ^ (p - n)) * I) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _), ← Real.rpow_add hρ,
              show (n : ℝ) - p + (p - n) = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * ENNReal.ofReal (δ ^ p) := mul_le_mul_right h1 _
        _ = ENNReal.ofReal (ρ ^ ((n : ℝ) - p) * δ ^ p) :=
            (ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)).symm
    have hc : 0 < δ / ρ := div_pos hδ hρ
    have hpt' : ∀ x, ENNReal.ofReal ‖H x‖ ≤
        ENNReal.ofReal (δ / ρ) + ENNReal.ofReal ((δ / ρ) ^ (1 - p)) * ‖H x‖ₑ ^ p := by
      intro x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← ENNReal.ofReal_add hc.le
          (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (norm_nonneg _) _))]
      exact ENNReal.ofReal_le_ofReal (young ‖H x‖ (δ / ρ) (norm_nonneg _) hc)
    have hrp : (δ / ρ) ^ (1 - p) * (ρ ^ ((n : ℝ) - p) * δ ^ p) = δ * ρ ^ n / ρ := by
      rw [Real.div_rpow hδ.le hρ.le]
      have e1 : δ ^ (1 - p) * δ ^ p = δ := by
        rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
      have e2 : ρ ^ ((n : ℝ) - p) / ρ ^ (1 - p) = ρ ^ n / ρ := by
        rw [← Real.rpow_sub hρ, show (n : ℝ) - p - (1 - p) = (n : ℝ) - 1 by ring,
          Real.rpow_sub_one hρ.ne', Real.rpow_natCast]
      calc δ ^ (1 - p) / ρ ^ (1 - p) * (ρ ^ ((n : ℝ) - p) * δ ^ p)
          = (δ ^ (1 - p) * δ ^ p) * (ρ ^ ((n : ℝ) - p) / ρ ^ (1 - p)) := by ring
        _ = δ * ρ ^ n / ρ := by rw [e1, e2]; ring
    have hlint : ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ENNReal.ofReal ‖H x‖ ∂V.weight ≤
        ENNReal.ofReal ((2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ) := by
      calc ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ENNReal.ofReal ‖H x‖ ∂V.weight
          ≤ ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, (ENNReal.ofReal (δ / ρ) +
              ENNReal.ofReal ((δ / ρ) ^ (1 - p)) * ‖H x‖ₑ ^ p) ∂V.weight :=
            lintegral_mono fun x => hpt' x
        _ = ENNReal.ofReal (δ / ρ) * V.weight (closedBall 0 ρ) +
              ENNReal.ofReal ((δ / ρ) ^ (1 - p)) * I := by
            rw [lintegral_add_left measurable_const, setLIntegral_const,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hIdef]
        _ ≤ ENNReal.ofReal (δ / ρ) * ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) +
              ENNReal.ofReal ((δ / ρ) ^ (1 - p)) * ENNReal.ofReal (ρ ^ ((n : ℝ) - p) * δ ^ p) :=
            add_le_add (mul_le_mul_right hmass _) (mul_le_mul_right hI _)
        _ = ENNReal.ofReal (δ / ρ * ((1 + δ) * (unitBallVolume n * ρ ^ n)) +
              (δ / ρ) ^ (1 - p) * (ρ ^ ((n : ℝ) - p) * δ ^ p)) := by
            rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal ((2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hrp]
            have h1 : δ / ρ * ((1 + δ) * (unitBallVolume n * ρ ^ n)) ≤
                2 * unitBallVolume n * δ * ρ ^ n / ρ := by
              rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hρ]
              have : 0 ≤ δ * (unitBallVolume n * ρ ^ n) := by positivity
              calc δ * ((1 + δ) * (unitBallVolume n * ρ ^ n))
                  = (1 + δ) * (δ * (unitBallVolume n * ρ ^ n)) := by ring
                _ ≤ 2 * (δ * (unitBallVolume n * ρ ^ n)) :=
                    mul_le_mul_of_nonneg_right (by linarith) this
                _ = 2 * unitBallVolume n * δ * ρ ^ n := by ring
            have h2 : (2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ =
                2 * unitBallVolume n * δ * ρ ^ n / ρ + δ * ρ ^ n / ρ := by ring
            linarith
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
      hHint.norm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
  have htiltA : ∀ ζ ∈ V.support ∩ closedBall 0 (R' / 2), V.tiltExcess ζ R' (S 0) ≤ C₉ * t ^ 2 := by
    intro ζ hζ
    have hζn : ‖ζ‖ ≤ R' / 2 := mem_closedBall_zero_iff.1 hζ.2
    have hsubρ : closedBall ζ (2 * R') ⊆ closedBall 0 ρ :=
      hball_sub ζ _ _ (by rw [hR'ρ] at hζn ⊢; linarith)
    have hheightA : ∀ x ∈ V.support ∩ closedBall ζ (2 * R'),
        infDist (x - ζ) (S 0 : Set (Amb n ℓ)) ≤ CR * t * R₃ := by
      intro x hx
      have hxn : ‖x‖ ≤ 5 * R' / 2 := by
        have h1 : ‖x - ζ‖ ≤ 2 * R' := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx.2
        have h2 := norm_le_insert' x ζ
        linarith [norm_sub_norm_le x ζ]
      obtain ⟨x', -, rfl, hx'n⟩ := hgraph_pt _ hx.1 (by linarith)
      obtain ⟨z', -, rfl, hz'n⟩ := hgraph_pt _ hζ.1 (by linarith)
      rw [← map_sub, ← hgp_sub]
      refine (hgp_dist _ _).trans ?_
      have h1 := hH x' (mem_ball_zero_iff.2 (by linarith))
      have h2 := hH z' (mem_ball_zero_iff.2 (by linarith))
      have hsum : ‖x'‖ + ‖z'‖ ≤ R₃ := by linarith
      have hCRt : 0 ≤ CR * t := by positivity
      calc ‖f x' - f z'‖ ≤ ‖f x'‖ + ‖f z'‖ := norm_sub_le _ _
        _ ≤ CR * t * ‖x'‖ + CR * t * ‖z'‖ := add_le_add h1 h2
        _ = CR * t * (‖x'‖ + ‖z'‖) := by ring
        _ ≤ CR * t * R₃ := mul_le_mul_of_nonneg_left hsum hCRt
    have hA := hLemA U hU V H hHmc ζ (2 * R') (CR * t * R₃) (by positivity) (by positivity)
      (hsubρ.trans hBU) (S 0) hT₀dim hheightA
    rw [show 2 * R' / 2 = R' by ring] at hA
    have hζ3 : ‖ζ‖ ≤ 3 * δ₀ * ρ := by rw [hR'ρ] at hζn; linarith
    have h2R' : 2 * R' ≤ ρ / 2 := by rw [hR'ρ]; linarith
    have hfinζ : V.weight (closedBall ζ (2 * R')) ≠ ∞ := hmeas_fin ζ hζ3 _ (by positivity) h2R'
    have hI1 : ∫ x in closedBall ζ (2 * R'), infDist (x - ζ) (S 0 : Set (Amb n ℓ)) ^ 2 ∂V.weight ≤
        (CR * t * R₃) ^ 2 * (2 * unitBallVolume n * (2 * R') ^ n) := by
      have h1 : ∫ x in closedBall ζ (2 * R'), infDist (x - ζ) (S 0 : Set (Amb n ℓ)) ^ 2 ∂V.weight ≤
          (CR * t * R₃) ^ 2 * V.weight.real (closedBall ζ (2 * R')) := by
        refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const_ae hfinζ.lt_top ?_)
        filter_upwards [ae_restrict_of_ae hae_spt, ae_restrict_mem measurableSet_closedBall]
          with x hx1 hx2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ infDist_nonneg (hheightA x ⟨hx1, hx2⟩) 2
      exact h1.trans (mul_le_mul_of_nonneg_left
        (hmeas_real ζ hζ3 _ (by positivity) h2R') (sq_nonneg _))
    have hI2 : ∫ x in closedBall ζ (2 * R'), ‖H x‖ ∂V.weight ≤
        (2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ :=
      (setIntegral_mono_set hHint.norm (Eventually.of_forall fun x => norm_nonneg _)
        hsubρ.eventuallyLE).trans hHbound
    have hρR' : ρ = 256 / δ₀ * R' := by rw [hR'ρ]; field_simp
    unfold RectifiableVarifold.tiltExcess
    calc (R' ^ n)⁻¹ * ∫ x in closedBall ζ R', hsNormSq (V.tangentProj x - (S 0).starProjection)
          ∂V.weight
        ≤ (R' ^ n)⁻¹ * (CL * ((2 * R') ^ 2)⁻¹ * ((CR * t * R₃) ^ 2 *
            (2 * unitBallVolume n * (2 * R') ^ n)) +
            CL * (CR * t * R₃) * ((2 * unitBallVolume n + 1) * δ * ρ ^ n / ρ)) := by
          refine mul_le_mul_of_nonneg_left (hA.trans (add_le_add ?_ ?_)) (by positivity)
          · exact mul_le_mul_of_nonneg_left hI1 (by positivity)
          · exact mul_le_mul_of_nonneg_left hI2 (by positivity)
      _ = 8 * 2 ^ n * CL * CR ^ 2 * unitBallVolume n * t ^ 2 +
            4 * CL * CR * (2 * unitBallVolume n + 1) * (256 / δ₀) ^ n * (δ₀ / 256) * (t * δ) := by
          rw [hR₃R', hρR']
          field_simp
          ring
      _ ≤ 8 * 2 ^ n * CL * CR ^ 2 * unitBallVolume n * t ^ 2 +
            4 * CL * CR * (2 * unitBallVolume n + 1) * (256 / δ₀) ^ n * (δ₀ / 256) * t ^ 2 := by
          have htδ : t * δ ≤ t ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hδt ht0.le
          gcongr
      _ = C₉ * t ^ 2 := by rw [hC₉]; ring
  /- **Step 8.** The decay iteration restarted at scale `R'` gives the rate. -/
  have hEstarζ : ∀ ζ ∈ V.support ∩ closedBall 0 (R' / 2),
      V.tiltExcessStar H p δ₀ ζ R' (S 0) ≤ C₁₀ * t ^ 2 := by
    intro ζ hζ
    have hζn : ‖ζ‖ ≤ R' / 2 := mem_closedBall_zero_iff.1 hζ.2
    refine (hEstar ζ R' (S 0) _ hR'0 (by rw [hR'ρ]; linarith)
      (hball_sub ζ _ _ (by rw [hR'ρ] at hζn ⊢; linarith)) (htiltA ζ hζ)).trans (max_le ?_ ?_)
    · have : 0 ≤ δ₀⁻¹ * t ^ 2 := by positivity
      rw [hC₁₀, add_mul]; linarith
    · have h1 : δ₀⁻¹ * δ ^ 2 ≤ δ₀⁻¹ * t ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδt 2) (by positivity)
      have h2 : 0 ≤ C₉ * t ^ 2 := by positivity
      rw [hC₁₀, add_mul]; linarith
  have hIter₂ : ∀ ζ : Amb n ℓ, ∃ S' : Submodule ℝ (Amb n ℓ),
      ζ ∈ V.support ∩ closedBall 0 (R' / 2) →
      Module.finrank ℝ S' = n ∧
        hsNormSq (S'.starProjection - (S 0).starProjection) ≤ CI * (C₁₀ * t ^ 2) ∧
        ∀ s : ℝ, 0 < s → s ≤ R' →
          V.tiltExcess ζ s S' ≤ CI * (s / R') ^ (2 * (1 - (n : ℝ) / p)) * (C₁₀ * t ^ 2) := by
    intro ζ
    by_cases hζ : ζ ∈ V.support ∩ closedBall 0 (R' / 2)
    · have hζn : ‖ζ‖ ≤ R' / 2 := mem_closedBall_zero_iff.1 hζ.2
      have hζ' : ζ ∈ V.support ∩ closedBall 0 (δ₀ * ρ) :=
        ⟨hζ.1, mem_closedBall_zero_iff.2 (by rw [hR'ρ] at hζn; linarith)⟩
      obtain ⟨S', h1, h2, h3⟩ := hIter U hU V H δ₀ ρ hδ₀0 hδ₀I hyp₀ ζ hζ' R' hR'0
        (by rw [hR'ρ]; linarith) (S 0) hT₀dim
      have hE := hEstarζ ζ hζ
      exact ⟨S', fun _ => ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hE hCI), fun s hs hs' =>
        (h3 s hs hs').trans (mul_le_mul_of_nonneg_left hE
          (mul_nonneg hCI (Real.rpow_nonneg (by positivity) _)))⟩⟩
    · exact ⟨⊥, fun h => absurd h hζ⟩
  choose S' hS' using hIter₂
  have hR'R₂ : R' ≤ R₂ := by rw [hR', hR₃]; linarith
  have hcamp2_hyp : ∀ ζ ∈ V.support ∩ closedBall 0 (R' / 2), Module.finrank ℝ (S' ζ) = n ∧
      ∀ s : ℝ, 0 < s → s ≤ R' / 2 →
        V.tiltExcess ζ s (S' ζ) ≤ CI * (C₁₀ * t ^ 2) * (s / R') ^ (2 * (1 - (n : ℝ) / p)) := by
    intro ζ hζ
    obtain ⟨h1, -, h3⟩ := hS' ζ hζ
    exact ⟨h1, fun s hs hs' => (h3 s hs (by linarith)).trans (le_of_eq (by ring))⟩
  obtain ⟨-, hHol2, hPlane2⟩ := hCamp U hU V H δ₀ ρ hδ₀0 hδ₀3 hyp₀ q₀ f R' hR'0
    (hR'R₂.trans hR₂le) hf0 (hfLipc.mono (closedBall_subset_closedBall hR'R₂))
    (hgraph_r R' hR'R₂) S' (CI * (C₁₀ * t ^ 2)) (by positivity) hcamp2_hyp
  have hsqA : Real.sqrt (CI * (C₁₀ * t ^ 2)) = Real.sqrt (CI * C₁₀) * t := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_sq ht0.le]
  rw [hsqA] at hHol2
  have hDsup : ∀ z ∈ ball (0 : Rn n) (R' / 16),
      hsNorm (fderiv ℝ f z) ≤ Real.sqrt (CI * C₁₀) * t := by
    intro z hz
    have hzn : ‖z‖ < R' / 16 := mem_ball_zero_iff.1 hz
    have hzR₂ : z ∈ ball (0 : Rn n) R₂ := mem_ball_zero_iff.2 (by linarith)
    have hzb : z ∈ closedBall (0 : Rn n) R₂ := ball_subset_closedBall hzR₂
    have hFz := hF z hzb
    have hFzmem : q₀ (graphPoint z (f z)) ∈ V.support ∩ closedBall 0 (R' / 2) :=
      ⟨hgraph_mem z hzb (by linarith), mem_closedBall_zero_iff.2 (by linarith)⟩
    have h1 := hGPA2 q₀ (fderiv ℝ f z) (hDfHS z hzR₂)
    rw [hsp_congr _ _ (hPlane2 z hz), hsp_congr _ _ hq₀] at h1
    have h2 := (hS' _ hFzmem).2.1
    unfold hsNorm
    rw [← hsqA]
    exact Real.sqrt_le_sqrt (h1.trans h2)
  /- **Step 9.** Conclusion on the closed ball `B_{γρ}(0)`, `γ = δ₀/8192`. -/
  have hγρ : δ₀ / 8192 * ρ = R' / 32 := by rw [hR'ρ]; ring
  have hγρ0 : 0 < δ₀ / 8192 * ρ := by positivity
  have hB16 : closedBall (0 : Rn n) (δ₀ / 8192 * ρ) ⊆ ball 0 (R' / 16) := by
    rw [hγρ]; exact closedBall_subset_ball (by linarith)
  have hBR₃ : ball (0 : Rn n) (R' / 16) ⊆ ball 0 R₃ := ball_subset_ball (by rw [hR']; linarith)
  have hdiffB : ∀ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ), DifferentiableAt ℝ f x :=
    fun x hx => (hC1.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (hBR₃ (hB16 hx)))
  have huniq : UniqueDiffOn ℝ (closedBall (0 : Rn n) (δ₀ / 8192 * ρ)) :=
    uniqueDiffOn_convex (convex_closedBall _ _)
      (by rw [interior_closedBall _ hγρ0.ne']; exact ⟨0, mem_ball_self hγρ0⟩)
  have hfdw : ∀ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ),
      fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) x = fderiv ℝ f x :=
    fun x hx => (hdiffB x hx).fderivWithin (huniq x hx)
  refine ⟨q₀, f, hC1.mono (hB16.trans hBR₃), hf0,
    by rw [hfdw 0 (mem_closedBall_self hγρ0.le), hDf0],
    hgraph_r _ (by rw [hγρ]; linarith), ?_⟩
  rw [← ht]
  unfold scaledC1AlphaNorm
  have h1 : (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ), ‖f x‖ₑ) ≤
      ENNReal.ofReal (CR * t * (δ₀ / 8192 * ρ)) := by
    refine iSup₂_le fun x hx => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hH x (hBR₃ (hB16 hx))).trans ?_)
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hx) (by positivity)
  have h2 : (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ),
      ENNReal.ofReal (hsNorm (fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) x))) ≤
      ENNReal.ofReal (Real.sqrt (CI * C₁₀) * t) := by
    refine iSup₂_le fun x hx => ?_
    rw [hfdw x hx]
    exact ENNReal.ofReal_le_ofReal (hDsup x (hB16 hx))
  have h3 : (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ),
      ⨆ y ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ), ⨆ (_ : x ≠ y),
        ENNReal.ofReal (hsNorm (fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) x -
          fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) y) / ‖x - y‖ ^ (1 - (n : ℝ) / p))) ≤
      ENNReal.ofReal (Cc * (Real.sqrt (CI * C₁₀) * t) / R' ^ (1 - (n : ℝ) / p)) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [hfdw x hx, hfdw y hy]
    apply ENNReal.ofReal_le_ofReal
    have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hdα : 0 < ‖x - y‖ ^ (1 - (n : ℝ) / p) := Real.rpow_pos_of_pos hd _
    have hR'α : 0 < R' ^ (1 - (n : ℝ) / p) := Real.rpow_pos_of_pos hR'0 _
    rw [div_le_div_iff₀ hdα hR'α]
    have h := hHol2 x (hB16 hx) y (hB16 hy)
    rw [Real.div_rpow (norm_nonneg _) hR'0.le] at h
    calc hsNorm (fderiv ℝ f x - fderiv ℝ f y) * R' ^ (1 - (n : ℝ) / p)
        ≤ Cc * (Real.sqrt (CI * C₁₀) * t) *
            (‖x - y‖ ^ (1 - (n : ℝ) / p) / R' ^ (1 - (n : ℝ) / p)) * R' ^ (1 - (n : ℝ) / p) :=
          mul_le_mul_of_nonneg_right h hR'α.le
      _ = Cc * (Real.sqrt (CI * C₁₀) * t) * ‖x - y‖ ^ (1 - (n : ℝ) / p) := by
          field_simp
  have hρR'α : ρ ^ (1 - (n : ℝ) / p) / R' ^ (1 - (n : ℝ) / p) =
      (256 / δ₀) ^ (1 - (n : ℝ) / p) := by
    rw [← Real.div_rpow hρ.le hR'0.le, hR'ρ]
    congr 1
    field_simp
  calc ENNReal.ofReal ρ⁻¹ * (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ), ‖f x‖ₑ) +
        (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ),
          ENNReal.ofReal (hsNorm (fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) x))) +
        ENNReal.ofReal (ρ ^ (1 - (n : ℝ) / p)) *
          (⨆ x ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ),
            ⨆ y ∈ closedBall (0 : Rn n) (δ₀ / 8192 * ρ), ⨆ (_ : x ≠ y),
              ENNReal.ofReal (hsNorm (fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) x -
                fderivWithin ℝ f (closedBall 0 (δ₀ / 8192 * ρ)) y) /
                ‖x - y‖ ^ (1 - (n : ℝ) / p)))
      ≤ ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (CR * t * (δ₀ / 8192 * ρ)) +
          ENNReal.ofReal (Real.sqrt (CI * C₁₀) * t) +
          ENNReal.ofReal (ρ ^ (1 - (n : ℝ) / p)) *
            ENNReal.ofReal (Cc * (Real.sqrt (CI * C₁₀) * t) / R' ^ (1 - (n : ℝ) / p)) := by
        gcongr
    _ = ENNReal.ofReal (ρ⁻¹ * (CR * t * (δ₀ / 8192 * ρ)) + Real.sqrt (CI * C₁₀) * t +
          ρ ^ (1 - (n : ℝ) / p) * (Cc * (Real.sqrt (CI * C₁₀) * t) / R' ^ (1 - (n : ℝ) / p))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal ((CR * (δ₀ / 8192) + Real.sqrt (CI * C₁₀) +
          Cc * Real.sqrt (CI * C₁₀) * (256 / δ₀) ^ (1 - (n : ℝ) / p)) * t) := by
        congr 1
        have e1 : ρ ^ (1 - (n : ℝ) / p) * (Cc * (Real.sqrt (CI * C₁₀) * t) /
            R' ^ (1 - (n : ℝ) / p)) =
            Cc * Real.sqrt (CI * C₁₀) * (256 / δ₀) ^ (1 - (n : ℝ) / p) * t := by
          rw [← hρR'α]; ring
        have e2 : ρ⁻¹ * (CR * t * (δ₀ / 8192 * ρ)) = CR * (δ₀ / 8192) * t := by
          field_simp
        rw [e1, e2]
        ring

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
