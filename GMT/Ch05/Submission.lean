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

theorem dohr_local_monotonicity : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
  have dohrLmonoRadialAux_hasFDerivAt_norm : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
    intro E _ _ y x hxy
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : HasFDerivAt (fun z : E => ‖z - y‖ ^ 2)
        (2 • (innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E)) x :=
      (hasFDerivAt_sub_const (𝕜 := ℝ) y).norm_sq
    have h2 := h1.sqrt (by positivity)
    have h3 : (fun z : E => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ := by
      funext z; exact Real.sqrt_sq (norm_nonneg _)
    rw [h3] at h2
    convert h2 using 1
    ext w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, Real.sqrt_sq hpos.le]
    rw [two_smul]
    field_simp
    ring
  have dohrLmonoRadialAux_hasFDerivAt : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : ℝ → ℝ), ContDiff ℝ 1 φ → ∀ (ρ : ℝ) (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => φ (‖z - y‖ / ρ) • (z - y))
        (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ E +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x := by
    intro E _ _ φ hφ ρ y x hxy
    have hsub : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x :=
      hasFDerivAt_sub_const y
    have hnorm := dohrLmonoRadialAux_hasFDerivAt_norm y x hxy
    have hφd : HasDerivAt φ (deriv φ (‖x - y‖ / ρ)) (‖x - y‖ / ρ) :=
      (hφ.differentiable one_ne_zero _).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) * (1 / ρ)) ‖x - y‖ :=
      hφd.comp (‖x - y‖) ((hasDerivAt_id' (‖x - y‖)).div_const ρ)
    have h2 := h1.comp_hasFDerivAt x hnorm
    exact h2.smul hsub
  have dohrLmonoRadialAux_trace : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : ℝ) (f : E →L[ℝ] ℝ) (v : E) (B : E →L[ℝ] E),
      LinearMap.trace ℝ E ((a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ
          B.toLinearMap) = a * LinearMap.trace ℝ E B.toLinearMap + f (B v) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt
    intro E _ _ _ a f v B
    have hcomp : (a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ B.toLinearMap =
        a • B.toLinearMap + (f.toLinearMap ∘ₗ B.toLinearMap).smulRight v := by
      ext w
      simp
    rw [hcomp, map_add, map_smul, LinearMap.trace_smulRight]
    simp
  have dohrLmonoRadialAux_trace_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E),
      LinearMap.trace ℝ E P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace
    intro E _ _ _ P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  have dohrLmonoRadialAux_inner_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E) (v : E),
      inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection
    intro E _ _ _ P v
    rw [← P.inner_starProjection_left_eq_right v v]
    simpa using P.re_inner_starProjection_eq_normSq v
  have dohrLmonoRadialAux_integrable : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ), Continuous f →
      ∀ (y : Amb n ℓ) (ρ : ℝ), μ (closedBall y ρ) < ∞ → (∀ x, ρ < ‖x - y‖ → f x = 0) →
        Integrable f μ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection
    intro n ℓ μ f hf y ρ hμ h0
    obtain ⟨C, hC⟩ := (isCompact_closedBall y ρ).exists_bound_of_continuousOn hf.continuousOn
    have hon : IntegrableOn f (closedBall y ρ) μ :=
      Measure.integrableOn_of_bounded (M := C) hμ.ne hf.aestronglyMeasurable
        (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx; exact hC x hx)
    have heq : (closedBall y ρ).indicator f = f := by
      funext x
      by_cases hx : x ∈ closedBall y ρ
      · simp [hx]
      · rw [indicator_of_notMem hx, h0 x (by rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx)]
    rw [← heq]
    exact hon.integrable_indicator measurableSet_closedBall
  have dohr_lmono_radial_inequality : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R : ℝ), closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → ∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂V.weight ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm
    intro n ℓ U V H hH y R hBR htan htm φ ρ hφ hanti hφ1 hφ0 hρ hρR
    -- basic facts about `φ`
    have hd_nonpos : ∀ t, deriv φ t ≤ 0 := fun t => hanti.deriv_nonpos
    have hd_zero : ∀ t, 1 < t → deriv φ t = 0 := by
      intro t ht
      have hzero : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [lt_mem_nhds ht] with u hu
        exact hφ0 u hu.le
      exact hzero.deriv_eq.trans (deriv_const t 0)
    have hφc : Continuous φ := hφ.continuous
    have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- the radial vector field
    set X : Amb n ℓ → Amb n ℓ := fun z => φ (‖z - y‖ / ρ) • (z - y) with hXdef
    have hX0 : ∀ z, ρ ≤ ‖z - y‖ → X z = 0 := by
      intro z hz
      have : 1 ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
      simp [hXdef, hφ0 _ this]
    have hXnear : X =ᶠ[𝓝 y] fun z => z - y := by
      filter_upwards [ball_mem_nhds y (half_pos hρ)] with z hz
      rw [mem_ball, dist_eq_norm] at hz
      have : ‖z - y‖ / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
      simp [hXdef, hφ1 _ this]
    have hXcd : ContDiff ℝ 1 X := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hxy : x = y
      · rw [hxy]
        exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq hXnear
      · have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
          (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hxy)
        have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
          hφ.contDiffAt.comp x (h1.div_const ρ)
        exact h2.smul (contDiffAt_id.sub contDiffAt_const)
    have hXsupp : Function.support X ⊆ closedBall y ρ := by
      intro z hz
      by_contra hzB
      rw [mem_closedBall, dist_eq_norm, not_le] at hzB
      exact hz (hX0 z hzB.le)
    have hXcs : HasCompactSupport X :=
      HasCompactSupport.intro (isCompact_closedBall y ρ) fun z hz => by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        exact hX0 z hz.le
    have hXts : tsupport X ⊆ U :=
      (closure_minimal hXsupp isClosed_closedBall).trans
        ((closedBall_subset_closedBall hρR.le).trans hBR)
    -- the generalized mean curvature identity
    have hGMC := hH.2 X hXcd hXcs hXts
    -- derivative of `X`
    have hDX : ∀ x, x ≠ y → HasFDerivAt X (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x :=
      fun x hxy => dohrLmonoRadialAux_hasFDerivAt φ hφ ρ y x hxy
    have hDXy : HasFDerivAt X (ContinuousLinearMap.id ℝ (Amb n ℓ)) y :=
      (hasFDerivAt_sub_const y).congr_of_eventuallyEq hXnear
    have hdiv_formula : ∀ x, x ≠ y → V.divM X x =
        φ (‖x - y‖ / ρ) * LinearMap.trace ℝ (Amb n ℓ) (V.tangentProj x).toLinearMap +
          deriv φ (‖x - y‖ / ρ) * (1 / ρ) *
            (‖x - y‖⁻¹ * inner ℝ (x - y) (V.tangentProj x (x - y))) := by
      intro x hxy
      rw [RectifiableVarifold.divM, (hDX x hxy).fderiv, dohrLmonoRadialAux_trace]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    have hdiv_zero : ∀ x, ρ < ‖x - y‖ → V.divM X x = 0 := by
      intro x hx
      have hxy : x ≠ y := by
        intro h
        rw [h, sub_self, norm_zero] at hx
        linarith
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      rw [hdiv_formula x hxy, hφ0 _ h1.le, hd_zero _ h1]
      ring
    -- the comparison functions
    set g : Amb n ℓ → ℝ := fun x =>
      (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) with hgdef
    set k : Amb n ℓ → ℝ := fun x => (n : ℝ) * φ (‖x - y‖ / ρ) with hkdef
    have hsand : ∀ᵐ x ∂V.weight, g x ≤ V.divM X x ∧ V.divM X x ≤ k x := by
      filter_upwards [htan] with x hx
      by_cases hxR : x ∈ ball y R
      · obtain ⟨P, hPn, hPx⟩ := hx hxR
        by_cases hxy : x = y
        · rw [hxy] at hPx ⊢
          have hdy : V.divM X y = n := by
            rw [RectifiableVarifold.divM, hDXy.fderiv, hPx]
            simp [dohrLmonoRadialAux_trace_starProjection, hPn]
          rw [hdy]
          simp [hgdef, hkdef, hφ1 0 (by norm_num)]
        · have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
          have hsr : ‖P.starProjection (x - y)‖ ≤ ‖x - y‖ := P.norm_starProjection_apply_le _
          have hs0 : 0 ≤ ‖P.starProjection (x - y)‖ := norm_nonneg _
          rw [hdiv_formula x hxy, hPx, dohrLmonoRadialAux_trace_starProjection, hPn,
            dohrLmonoRadialAux_inner_starProjection]
          simp only [hgdef, hkdef]
          have hd : deriv φ (‖x - y‖ / ρ) ≤ 0 := hd_nonpos _
          have h1 : ‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2 ≤ ‖x - y‖ := by
            rw [inv_mul_le_iff₀ hr]
            calc ‖P.starProjection (x - y)‖ ^ 2
                = ‖P.starProjection (x - y)‖ * ‖P.starProjection (x - y)‖ := sq _
              _ ≤ ‖x - y‖ * ‖x - y‖ := mul_self_le_mul_self hs0 hsr
          have hq : (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) ≤ ‖x - y‖ / ρ := by
            calc (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2)
                ≤ (1 / ρ) * ‖x - y‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = ‖x - y‖ / ρ := by ring
          have hq0 : 0 ≤ (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) := by positivity
          have e1 := mul_le_mul_of_nonpos_left hq hd
          have e2 := mul_nonpos_of_nonpos_of_nonneg hd hq0
          constructor
          · linarith
          · linarith
      · have hx' : ρ < ‖x - y‖ := by
          rw [mem_ball, dist_eq_norm, not_lt] at hxR
          linarith
        rw [hdiv_zero x hx']
        have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
        simp [hgdef, hkdef, hφ0 _ h1.le, hd_zero _ h1]
    -- finiteness of the weight on `closedBall y ρ`
    have hμρ : V.weight (closedBall y ρ) < ∞ := by
      have hBρ : closedBall y ρ ⊆ U := (closedBall_subset_closedBall hρR.le).trans hBR
      rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
      exact (V.integrableOn_mult _ (isCompact_closedBall y ρ) hBρ).setLIntegral_lt_top
    -- integrability of the comparison functions
    have hgc : Continuous g := by simp only [hgdef]; fun_prop
    have hkc : Continuous k := by simp only [hkdef]; fun_prop
    have hg_int : Integrable g V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight g hgc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hgdef, hφ0 _ h1.le, hd_zero _ h1]
    have hk_int : Integrable k V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight k hkc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hkdef, hφ0 _ h1.le]
    -- measurability of the tangential divergence
    have hΦ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
        LinearMap.trace ℝ (Amb n ℓ) (p.1.toLinearMap ∘ₗ p.2.toLinearMap)) := by
      have h1 : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
          p.1.comp p.2) :=
        isBoundedBilinearMap_comp.continuous
      have h2 : Continuous (fun A : Amb n ℓ →L[ℝ] Amb n ℓ =>
          LinearMap.trace ℝ (Amb n ℓ) A.toLinearMap) :=
        ((LinearMap.trace ℝ (Amb n ℓ)).comp
          (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
      exact h2.comp h1
    have hDXc : Continuous (fderiv ℝ X) := hXcd.continuous_fderiv one_ne_zero
    have hdivR : AEStronglyMeasurable (fun x => LinearMap.trace ℝ (Amb n ℓ)
        ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap))
        (V.weight.restrict (ball y R)) :=
      hΦ.comp_aestronglyMeasurable (hDXc.aestronglyMeasurable.prodMk htm)
    have hdiv_meas : AEStronglyMeasurable (V.divM X) V.weight := by
      have heq : V.divM X = (ball y R).indicator (V.divM X) := by
        funext x
        by_cases hx : x ∈ ball y R
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          apply hdiv_zero
          rw [mem_ball, dist_eq_norm, not_lt] at hx
          linarith
      rw [heq]
      exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hdivR
    have hdiv_int : Integrable (V.divM X) V.weight :=
      integrable_of_le_of_le hdiv_meas (hsand.mono fun x hx => hx.1)
        (hsand.mono fun x hx => hx.2) hg_int hk_int
    calc ∫ x, g x ∂V.weight ≤ ∫ x, V.divM X x ∂V.weight :=
          integral_mono_ae hg_int hdiv_int (hsand.mono fun x hx => hx.1)
      _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hGMC
      _ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp only [hXdef, real_inner_smul_left]
  have dohr_lmono_curvature_holder : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality
    intro n ℓ p hp μ H ψ y t ht hμB hH hHp hψm hψ01 hψ0
    set B : Set (Amb n ℓ) := closedBall y t with hBdef
    have hBm : MeasurableSet B := measurableSet_closedBall
    set q : ℝ := Real.conjExponent p with hqdef
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    have h1q : 1 / q = 1 - 1 / p := by
      rw [one_div, one_div, hpq.one_sub_inv]
    have hq1 : 1 ≤ q := hpq.symm.lt.le
    -- `ψ` vanishes off `B`
    have hψB : ∀ x, x ∉ B → ψ x = 0 := by
      intro x hx
      apply hψ0
      simpa [hBdef, mem_closedBall, dist_eq_norm, not_le] using hx
    -- `ψ` is integrable
    have hψint : Integrable ψ μ := by
      have h1 : Integrable (B.indicator ψ) μ := by
        refine IntegrableOn.integrable_indicator ?_ hBm
        refine Measure.integrableOn_of_bounded (M := 1) hμB.ne hψm ?_
        exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          exact (hψ01 x).2
      have h2 : B.indicator ψ = ψ := by
        funext x
        by_cases hx : x ∈ B
        · simp [hx]
        · simp [hx, hψB x hx]
      rwa [h2] at h1
    have hIψ : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
    -- pointwise bound
    have hpt : ∀ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ≤
        B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x := by
      intro x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        have hxt : ‖x - y‖ ≤ t := by
          simpa [hBdef, mem_closedBall, dist_eq_norm] using hx
        have hle : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          have h1 : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
          have h2 : ‖x - y‖ * ‖H x‖ ≤ t * ‖H x‖ :=
            mul_le_mul_of_nonneg_right hxt (norm_nonneg _)
          nlinarith [(hψ01 x).1, norm_nonneg (H x)]
        calc ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖
            ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) := by
            rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      · rw [indicator_of_notMem hx, hψB x hx]
        simp
    -- Hölder on `μ.restrict B`
    have hHmeas : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict B) := hH.aestronglyMeasurable.enorm
    have hψmeas : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) (μ.restrict B) :=
      hψm.restrict.aemeasurable.ennreal_ofReal
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq hHmeas hψmeas
    have hψq : (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) := by
      calc (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ)
          ≤ ∫⁻ x in B, ENNReal.ofReal (ψ x) ∂μ := by
            apply lintegral_mono
            intro x
            apply ENNReal.rpow_le_self_of_le_one _ hq1
            exact ENNReal.ofReal_le_one.mpr (hψ01 x).2
        _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ := setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ x, ψ x ∂μ) :=
            (ofReal_integral_eq_lintegral_ofReal hψint (Eventually.of_forall fun x => (hψ01 x).1)).symm
    set X : ℝ≥0∞ := ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ with hXdef
    have hXne : X ≠ ⊤ := hHp.ne
    have hlint : (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ) ≤
        ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
      calc (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ)
          ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x ∂μ :=
            lintegral_mono hpt
        _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) ∂μ :=
            lintegral_indicator hBm _
        _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
            gcongr ENNReal.ofReal t * ?_
            calc (∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ)
                ≤ (∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) *
                    (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ^ (1 / q) := hHolder
              _ ≤ X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q) := by
                  gcongr
    have hfin : ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hXne
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top
    calc |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ|
        = ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ).toReal :=
          norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q))).toReal :=
          ENNReal.toReal_mono hfin hlint
      _ = t * X.toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
            ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hIψ, h1q, mul_assoc]
  have dohrLmonoFixedCutoffAux_phi_nonneg : ∀ {φ : ℝ → ℝ}, Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ (s : ℝ), 0 ≤ φ s := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro φ hanti hcut s
    rcases le_total 1 s with h | h
    · rw [hcut s h]
    · rw [← hcut 1 le_rfl]
      exact hanti h
  have dohrLmonoFixedCutoffAux_deriv_zero : ∀ {φ : ℝ → ℝ}, (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ {s : ℝ}, 1 < s → deriv φ s = 0 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hcut s hs
    have hzero : φ =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hs] with u hu
      exact hcut u hu.le
    exact hzero.deriv_eq.trans (deriv_const s 0)
  have dohrLmonoFixedCutoffAux_deriv_bound : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → |s * deriv φ s| ≤ C := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hφ hcut
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hφ.continuous_deriv_one.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    rcases le_or_gt s 1 with h1 | h1
    · have h := hC s ⟨hs, h1⟩
      rw [Real.norm_eq_abs] at h
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |deriv φ s| ≤ 1 * |deriv φ s| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |deriv φ s| := one_mul _
        _ ≤ max C 0 := h.trans (le_max_left _ _)
    · rw [dohrLmonoFixedCutoffAux_deriv_zero hcut h1, mul_zero, abs_zero]
      exact le_max_right _ _
  have dohrLmonoFixedCutoffAux_hasDerivAt : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ (c : ℝ) {t : ℝ}, t ≠ 0 →
      HasDerivAt (fun u => φ (c / u)) (-(c / t * deriv φ (c / t)) / t) t := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound
    intro φ hφ c t ht
    have h1 : HasDerivAt (fun u : ℝ => c / u) (c * -(t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht).const_mul c
      convert this using 1
      funext u
      exact div_eq_mul_inv c u
    have h2 := ((hφ.differentiable (by simp) (c / t)).hasDerivAt).comp t h1
    have heq : -(c / t * deriv φ (c / t)) / t = deriv φ (c / t) * (c * -(t ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  have dohrLmonoFixedCutoffAux_npow : ∀ (n : ℕ) {ρ : ℝ}, ρ ≠ 0 → (n : ℝ) * ρ ^ (n - 1) = n * ρ ^ n / ρ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt
    intro n ρ hρ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [eq_div_iff hρ, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  have dohr_lmono_fixed_cutoff_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (R M β : ℝ), β < 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 R) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro n ℓ μ H y φ I a R M β hβ hμR hH hφ hanti hcut hrad hI ha hab
    -- the curvature integral `L`
    obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ,
        ∀ t, L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ := ⟨_, fun t => rfl⟩
    have ha' : ∀ t, a t = L t / t ^ (n + 1) / (1 + I t / t ^ n) := fun t => by
      rw [ha t, hL t]
    have hrad' : ∀ ρ : ℝ, 0 < ρ → ρ < R →
        ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -L ρ :=
      fun ρ h1 h2 => by rw [hL ρ]; exact hrad ρ h1 h2
    clear ha hrad
    set S : Set (Amb n ℓ) := closedBall y R with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    set ν : Measure (Amb n ℓ) := μ.restrict S with hνdef
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := hH
    have hφnn := dohrLmonoFixedCutoffAux_phi_nonneg hanti hcut
    obtain ⟨C, hC0, hC⟩ := dohrLmonoFixedCutoffAux_deriv_bound hφ hcut
    have hφc : Continuous φ := hφ.continuous
    have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- outside `S`, all the scaled profiles vanish
    have hout : ∀ t, 0 < t → t < R → ∀ x, x ∉ S → 1 < ‖x - y‖ / t := by
      intro t ht htR x hx
      have hRx : R < ‖x - y‖ := by
        simpa [hSdef, mem_closedBall, dist_eq_norm, not_le] using hx
      rw [lt_div_iff₀ ht]
      linarith
    -- conversion of the integrals to `ν`
    have hIν : ∀ t, 0 < t → t < R → I t = ∫ x, φ (‖x - y‖ / t) ∂ν := by
      intro t ht htR
      rw [hI t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hcut _ (hout t ht htR x hx).le
    have hLν : ∀ t, 0 < t → t < R →
        L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro t ht htR
      rw [hL t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hcut _ (hout t ht htR x hx).le, zero_mul]
    -- derivative of the profile in the scale variable
    set F' : ℝ → Amb n ℓ → ℝ := fun t x => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t
      with hF'eq
    have hIderiv : ∀ ρ, 0 < ρ → ρ < R → HasDerivAt I (∫ x, F' ρ x ∂ν) ρ := by
      intro ρ hρ hρR
      have hmain : HasDerivAt (fun t => ∫ x, φ (‖x - y‖ / t) ∂ν) (∫ x, F' ρ x ∂ν) ρ := by
        have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
          (F := fun t x => φ (‖x - y‖ / t)) (F' := F') (x₀ := ρ) (bound := fun _ => 2 * C / ρ)
          (Ioo_mem_nhds (half_lt_self hρ) hρR) ?_ ?_ ?_ ?_ ?_ ?_
        · exact key.2
        · exact Eventually.of_forall fun t =>
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        · refine Integrable.of_bound
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
            (φ 0) (Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (hφnn _)]
          exact hanti (div_nonneg (norm_nonneg _) hρ.le)
        · have hcont : Continuous (F' ρ) := by
            simp only [hF'eq]
            fun_prop
          exact hcont.aestronglyMeasurable
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          simp only [hF'eq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos ht0]
          calc |‖x - y‖ / t * deriv φ (‖x - y‖ / t)| / t ≤ C / t :=
                div_le_div_of_nonneg_right (hC _ (div_nonneg (norm_nonneg _) ht0.le)) ht0.le
            _ ≤ 2 * C / ρ := by
                rw [div_le_div_iff₀ ht0 hρ]
                nlinarith [ht.1]
        · exact integrable_const _
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          exact dohrLmonoFixedCutoffAux_hasDerivAt hφ ‖x - y‖ ht0.ne'
      refine hmain.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact hIν t ht.1 ht.2
    -- continuity of `L`
    have hLcont : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt L ρ := by
      intro ρ hρ hρR
      have hmain : ContinuousAt
          (fun t => ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν) ρ := by
        apply continuousAt_of_dominated (bound := fun x => φ 0 * (R * ‖H x‖))
        · refine Eventually.of_forall fun t => ?_
          have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ (‖x - y‖ / t)) ν :=
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
            continuous_inner.comp_aestronglyMeasurable
              ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
                hHν.aestronglyMeasurable)
          exact h1.mul h2
        · filter_upwards [Ioi_mem_nhds hρ] with t ht
          rw [hνdef, ae_restrict_iff' hSm]
          refine Eventually.of_forall fun x hx => ?_
          have hxR : ‖x - y‖ ≤ R := by
            simpa [hSdef, mem_closedBall, dist_eq_norm] using hx
          have hσ : 0 ≤ ‖x - y‖ / t := div_nonneg (norm_nonneg _) (le_of_lt ht)
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφnn _)]
          have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
            (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
          exact mul_le_mul (hanti hσ) hinner (norm_nonneg _) (hφnn 0)
        · exact (hHν.norm.const_mul R).const_mul (φ 0)
        · refine Eventually.of_forall fun x => ?_
          exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id hρ.ne')).mul
            continuousAt_const
      refine hmain.congr ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact (hLν t ht.1 ht.2).symm
    -- the key differential inequality
    have hkey : ∀ ρ, 0 < ρ → ρ < R → L ρ ≤ ρ * (∫ x, F' ρ x ∂ν) - n * I ρ := by
      intro ρ hρ hρR
      have h1 := hrad' ρ hρ hρR
      have hconv : ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ =
          ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂ν := by
        rw [hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        have h := hout ρ hρ hρR x hx
        rw [hcut _ h.le, dohrLmonoFixedCutoffAux_deriv_zero hcut h]
        ring
      have hint1 : Integrable (fun x => φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
          (φ 0) (Eventually.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (hφnn _)]
        exact hanti (div_nonneg (norm_nonneg _) hρ.le)
      have hint2 : Integrable (fun x => ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (by fun_prop : Continuous fun x : Amb n ℓ =>
            ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)).aestronglyMeasurable
          C (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hC _ (div_nonneg (norm_nonneg _) hρ.le)
      rw [hconv, integral_add (hint1.const_mul _) hint2, integral_const_mul,
        ← hIν ρ hρ hρR] at h1
      have hF'int : ∫ x, F' ρ x ∂ν = -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ := by
        simp only [hF'eq]
        rw [integral_div, integral_neg]
      rw [hF'int]
      have hρne : ρ ≠ 0 := hρ.ne'
      have hsimp : ρ * (-(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ) =
          -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) := by
        field_simp
      rw [hsimp]
      linarith
    -- basic facts on `I`
    have hInn : ∀ ρ, 0 ≤ I ρ := fun ρ => by
      rw [hI ρ]
      exact integral_nonneg fun x => hφnn _
    have hden : ∀ ρ, 0 < ρ → 1 ≤ 1 + I ρ / ρ ^ n := fun ρ h1 => by
      have := div_nonneg (hInn ρ) (pow_pos h1 n).le
      linarith
    -- continuity of `a`
    have hacontAt : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt a ρ := by
      intro ρ h1 h2
      have haeq : a = fun t => L t / t ^ (n + 1) / (1 + I t / t ^ n) := funext ha'
      rw [haeq]
      exact ((hLcont ρ h1 h2).div ((continuous_pow (n + 1)).continuousAt) (pow_ne_zero _ h1.ne')).div
        (continuousAt_const.add ((hIderiv ρ h1 h2).continuousAt.div ((continuous_pow n).continuousAt)
          (pow_ne_zero _ h1.ne')))
        (by linarith [hden ρ h1])
    have hacont : ContinuousOn a (Ioo 0 R) := fun ρ hρ =>
      (hacontAt ρ hρ.1 hρ.2).continuousWithinAt
    refine ⟨hacont, ?_⟩
    -- the fundamental theorem of calculus for `∫₀^ρ a`
    have hGderiv : ∀ ρ, 0 < ρ → ρ < R →
        HasDerivAt (fun u => ∫ t in (0)..u, a t) (a ρ) ρ := by
      intro ρ h1 h2
      apply intervalIntegral.integral_hasDerivAt_right
      · refine IntervalIntegrable.mono_fun' (g := fun t => M * t ^ (-β)) ?_ ?_ ?_
        · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
        · rw [uIoc_of_le h1.le]
          exact (hacont.mono (Ioc_subset_Ioo_right h2)).aestronglyMeasurable measurableSet_Ioc
        · rw [uIoc_of_le h1.le]
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
          show ‖a t‖ ≤ M * t ^ (-β)
          rw [Real.norm_eq_abs]
          exact hab t ht.1 (lt_of_le_of_lt ht.2 h2)
      · exact hacont.stronglyMeasurableAtFilter isOpen_Ioo ρ ⟨h1, h2⟩
      · exact hacontAt ρ h1 h2
    -- derivative of the monotone quantity
    have hΨ : ∀ ρ ∈ Ioo 0 R, ∃ D : ℝ,
        HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) D ρ ∧ 0 ≤ D := by
      rintro ρ ⟨h1, h2⟩
      have hG := hGderiv ρ h1 h2
      have hIρ := hIderiv ρ h1 h2
      have hd := (hG.neg.exp).mul
        ((hasDerivAt_const ρ (1 : ℝ)).add (hIρ.div (hasDerivAt_pow n ρ) (pow_ne_zero n h1.ne')))
      have hd' : HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n))
          (Real.exp (-∫ t in (0)..ρ, a t) * -a ρ * (1 + I ρ / ρ ^ n) +
            Real.exp (-∫ t in (0)..ρ, a t) * (0 + ((∫ x, F' ρ x ∂ν) * ρ ^ n -
              I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2)) ρ := hd
      refine ⟨_, hd', ?_⟩
      set E := Real.exp (-∫ t in (0)..ρ, a t) with hEdef
      set I' := ∫ x, F' ρ x ∂ν with hI'eq
      have hE : 0 < E := Real.exp_pos _
      have hP : 0 < ρ ^ n := pow_pos h1 n
      have hden' : 1 + I ρ / ρ ^ n ≠ 0 := by linarith [hden ρ h1]
      have haL : a ρ * (1 + I ρ / ρ ^ n) = L ρ / (ρ ^ n * ρ) := by
        rw [ha' ρ, div_mul_cancel₀ _ hden', pow_succ]
      have hq : (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2 =
          (ρ * I' - n * I ρ) / (ρ ^ n * ρ) := by
        rw [dohrLmonoFixedCutoffAux_npow n h1.ne']
        field_simp
      have hkeyρ := hkey ρ h1 h2
      have hnum : 0 ≤ (ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ) :=
        div_nonneg (by linarith) (by positivity)
      have hfinal : E * -a ρ * (1 + I ρ / ρ ^ n) +
          E * (0 + (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2) =
          E * ((ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ)) := by
        linear_combination (-E) * haL + E * hq
      rw [hfinal]
      exact mul_nonneg hE.le hnum
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 R)
    · intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, hD0⟩ := hΨ ρ hρ
      rw [hD.deriv]
      exact hD0
  have dohrLmonoOpenBallAux_cutoffs : ∃ φ : ℕ → ℝ → ℝ,
      (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧
      (∀ k (t : ℝ), t ≤ 1 / 2 → φ k t = 1) ∧ (∀ k (t : ℝ), 1 ≤ t → φ k t = 0) ∧
      (∀ k t, 0 ≤ φ k t ∧ φ k t ≤ 1) ∧
      (∀ s : ℝ, s < 1 → ∀ᶠ k in atTop, φ k s = 1) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone
    refine ⟨fun k s => 1 - Real.smoothTransition (((k : ℝ) + 3) * (s - 1) + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
    · intro k s t hst
      have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      have := Real.smoothTransition.monotone h1
      simp only
      linarith
    · intro k t ht
      have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have h1 : ((k : ℝ) + 3) * (t - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
    · intro k t ht
      have hk : (0 : ℝ) ≤ (k : ℝ) + 3 := by positivity
      have h1 : 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      simp only
      rw [Real.smoothTransition.one_of_one_le h1, sub_self]
    · intro k t
      have h0 := Real.smoothTransition.nonneg (((k : ℝ) + 3) * (t - 1) + 1)
      have h1 := Real.smoothTransition.le_one (((k : ℝ) + 3) * (t - 1) + 1)
      constructor <;> simp only <;> linarith
    · intro s hs
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (1 - s))
      rw [eventually_atTop]
      refine ⟨k₀, fun k hk => ?_⟩
      have hs1 : 0 < 1 - s := by linarith
      have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      have h2 : 1 / (1 - s) < (k : ℝ) + 3 := by linarith
      have h3 : 1 < ((k : ℝ) + 3) * (1 - s) := by
        rw [div_lt_iff₀ hs1] at h2
        linarith
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
  have dohrLmonoOpenBallAux_rpow_le : ∀ {b e : ℝ}, 0 ≤ b → 0 ≤ e → e ≤ 1 → b ^ e ≤ 1 + b := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
    intro b e hb he0 he1
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h he0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h he1
      rw [Real.rpow_one] at this
      linarith
  have dohrLmonoOpenBallAux_abound : ∀ (n : ℕ) {p t N I L : ℝ}, 1 < p → 0 < t → 0 ≤ N → 0 ≤ I →
      |L| ≤ t * N * I ^ (1 - 1 / p) →
        |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ N * t ^ (-((n : ℝ) / p)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
    intro n p t N I L hp ht hN hI hL
    have hp0 : 0 < p := by linarith
    have htn : 0 < t ^ n := pow_pos ht n
    set b := I / t ^ n with hbdef
    have hb : 0 ≤ b := div_nonneg hI htn.le
    have hIb : I = b * t ^ n := by
      rw [hbdef, div_mul_cancel₀ _ htn.ne']
    have he0 : 0 ≤ 1 - 1 / p := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    have he1 : 1 - 1 / p ≤ 1 := by
      have : 0 < 1 / p := by positivity
      linarith
    have hpow : I ^ (1 - 1 / p) = b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p)) := by
      rw [hIb, Real.mul_rpow hb htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    have hbe := dohrLmonoOpenBallAux_rpow_le hb he0 he1
    have hden : 0 < 1 + b := by linarith
    have hT : 0 < t ^ ((n : ℝ) * (1 - 1 / p)) := Real.rpow_pos_of_pos ht _
    have hL' : |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by
      calc |L| ≤ t * N * I ^ (1 - 1 / p) := hL
        _ = t * N * (b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p))) := by rw [hpow]
        _ ≤ t * N * ((1 + b) * t ^ ((n : ℝ) * (1 - 1 / p))) := by
            gcongr
        _ = N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by ring
    have hexp : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
      rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht]
      have h1 : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ ((1 : ℝ) + (n : ℝ) * (1 - 1 / p)) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      rw [h1]
      congr 1
      push_cast
      field_simp
      ring
    rw [abs_div, abs_div, abs_of_pos (pow_pos ht (n + 1)), abs_of_pos hden, div_div,
      div_le_iff₀ (mul_pos (pow_pos ht (n + 1)) hden)]
    calc |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := hL'
      _ = N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + b)) := by rw [hexp]; ring
  have dohrLmonoOpenBallAux_small : ∀ {n : ℕ} {p R κ : ℝ} {J : ℝ≥0∞}, 0 < p → 0 < R → 0 ≤ κ →
      (ENNReal.ofReal (R ^ (p - n)) * J) ^ (1 / p) ≤ ENNReal.ofReal κ →
        J ≠ ⊤ ∧ J.toReal ^ (1 / p) * R ^ (1 - (n : ℝ) / p) ≤ κ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound
    intro n p R κ J hp0 hR hκ h
    have hRp : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
    have hp1 : 0 < 1 / p := by positivity
    have hJ : J ≠ ⊤ := by
      intro hJ
      rw [hJ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hRp).ne', ENNReal.top_rpow_of_pos hp1,
        top_le_iff] at h
      exact ENNReal.ofReal_ne_top h
    refine ⟨hJ, ?_⟩
    have hJ' : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ).symm
    rw [hJ', ← ENNReal.ofReal_mul hRp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRp.le ENNReal.toReal_nonneg) hp1.le,
      ENNReal.ofReal_le_ofReal_iff hκ] at h
    rw [Real.mul_rpow hRp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hR.le] at h
    have he : (p - n) * (1 / p) = 1 - (n : ℝ) / p := by
      field_simp
    rw [he] at h
    linarith
  have dohrLmonoOpenBallAux_limit : ∀ (n : ℕ) {R Λ N β : ℝ}, 0 < R → β < 1 → 0 ≤ N →
      N * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → 0 < Λ → Λ ≤ 1 →
      ∀ (a : ℕ → ℝ → ℝ) (I : ℕ → ℝ → ℝ) (a₀ m : ℝ → ℝ),
      (∀ k, ContinuousOn (a k) (Ioo 0 R)) →
      (∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-β)) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => I k t) atTop (𝓝 (m t))) →
      (∀ k, MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n))
        (Ioo 0 R)) →
      ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧
        (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧
        Tendsto F (𝓝[>] 0) (𝓝 1) ∧
        MonotoneOn (fun r => F r * (r ^ n)⁻¹ * m r + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small
    intro n R Λ N β hR hβ1 hN hNR hΛ hΛ1 a I a₀ m hacont hab halim hIlim hmono
    -- the dominating function is integrable near `0`
    have hgint : ∀ ρ, IntervalIntegrable (fun t => N * t ^ (-β)) volume 0 ρ := fun ρ =>
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul N
    -- the bound passes to the limit
    have ha₀b : ∀ t, 0 < t → t < R → |a₀ t| ≤ N * t ^ (-β) := by
      intro t ht htR
      exact le_of_tendsto ((continuous_abs.tendsto _).comp (halim t ht htR))
        (Eventually.of_forall fun k => hab k t ht htR)
    -- measurability
    have hameas : ∀ k ρ, ρ < R → AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 ρ)) := by
      intro k ρ hρR
      exact ((hacont k).mono (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hρR⟩)).aestronglyMeasurable
        measurableSet_Ioc
    have ha₀meas : ∀ ρ, ρ < R → AEStronglyMeasurable a₀ (volume.restrict (Ioc 0 ρ)) := by
      intro ρ hρR
      refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => hameas k ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    have ha₀int : ∀ ρ, 0 ≤ ρ → ρ < R → IntegrableOn a₀ (Ioc 0 ρ) := by
      intro ρ hρ hρR
      have hg : IntegrableOn (fun t => N * t ^ (-β)) (Ioc 0 ρ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ).mp (hgint ρ)
      refine hg.mono' (ha₀meas ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
    -- convergence of the integrals
    have hGlim : ∀ ρ, 0 < ρ → ρ < R →
        Tendsto (fun k => ∫ t in (0)..ρ, a k t) atTop (𝓝 (∫ t in (0)..ρ, a₀ t)) := by
      intro ρ hρ hρR
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => N * t ^ (-β)) ?_ ?_ (hgint ρ) ?_
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => hameas k ρ hρR
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact hab k t ht.1 (lt_of_le_of_lt ht.2 hρR)
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    set G : ℝ → ℝ := fun ρ => ∫ t in (0)..ρ, a₀ t with hGdef
    -- bound on `G`
    have hGb : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ N * ρ ^ (1 - β) / (1 - β) := by
      intro ρ hρ hρR
      have h1 : ‖∫ t in (0)..ρ, a₀ t‖ ≤ ∫ t in (0)..ρ, N * t ^ (-β) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hρ.le ?_ (hgint ρ)
        exact Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
      have h2 : ∫ t in (0)..ρ, N * t ^ (-β) = N * ρ ^ (1 - β) / (1 - β) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h3 : -β + 1 = 1 - β := by ring
        rw [h3, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]
      rw [h2] at h1
      rw [← Real.norm_eq_abs]
      exact h1
    have hGΛ : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ Λ / 4 := by
      intro ρ hρ hρR
      refine (hGb ρ hρ hρR).trans (le_trans ?_ hNR)
      have h1β : 0 < 1 - β := by linarith
      apply div_le_div_of_nonneg_right _ h1β.le
      apply mul_le_mul_of_nonneg_left _ hN
      exact Real.rpow_le_rpow hρ.le hρR.le h1β.le
    set F : ℝ → ℝ := fun ρ => Real.exp (-G ρ) with hFdef
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · -- continuity
      intro ρ hρ
      have hρ1 : ρ < (ρ + R) / 2 := by linarith [hρ.2]
      have hρ1R : (ρ + R) / 2 < R := by linarith [hρ.2]
      have hρ0 : (0 : ℝ) ≤ (ρ + R) / 2 := by linarith [hρ.1]
      have hint : IntegrableOn a₀ (uIcc 0 ((ρ + R) / 2)) := by
        rw [uIcc_of_le hρ0, integrableOn_Icc_iff_integrableOn_Ioc]
        exact ha₀int _ hρ0 hρ1R
      have hc := intervalIntegral.continuousOn_primitive_interval hint
      have hmem : uIcc 0 ((ρ + R) / 2) ∈ 𝓝 ρ := by
        rw [uIcc_of_le hρ0]
        exact Icc_mem_nhds hρ.1 hρ1
      have hcG : ContinuousAt G ρ := hc.continuousAt hmem
      exact (Real.continuous_exp.continuousAt.comp hcG.neg).continuousWithinAt
    · intro r hr
      have h := hGΛ r hr.1 hr.2
      have h' := abs_le.mp h
      refine ⟨?_, ?_, ?_⟩
      · have h1 : |-G r| ≤ 1 := by rw [abs_neg]; linarith
        have h2 := Real.abs_exp_sub_one_le h1
        rw [abs_neg] at h2
        show |Real.exp (-G r) - 1| ≤ Λ
        linarith
      · show Real.exp (-Λ) ≤ Real.exp (-G r)
        exact Real.exp_le_exp.mpr (by linarith)
      · show Real.exp (-G r) ≤ Real.exp Λ
        exact Real.exp_le_exp.mpr (by linarith)
    · -- limit at `0`
      have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
        have hlim : Tendsto (fun ρ : ℝ => N * ρ ^ (1 - β) / (1 - β)) (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ρ : ℝ => ρ ^ (1 - β)) (𝓝 0) (𝓝 0) := by
            have := Real.continuousAt_rpow_const 0 (1 - β) (Or.inr (by linarith))
            rw [ContinuousAt, Real.zero_rpow (by linarith)] at this
            exact this
          have h2 := (h1.const_mul N).div_const (1 - β)
          rw [mul_zero, zero_div] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        refine squeeze_zero_norm' ?_ hlim
        have : Ioo (0 : ℝ) R ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hR
        filter_upwards [this] with ρ hρ
        rw [Real.norm_eq_abs]
        exact hGb ρ hρ.1 hρ.2
      have := (Real.continuous_exp.tendsto (-0)).comp hG0.neg
      rw [neg_zero, Real.exp_zero] at this
      exact this
    · -- monotonicity
      have hΨlim : ∀ ρ ∈ Ioo 0 R, Tendsto
          (fun k => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) atTop
          (𝓝 (F ρ * (1 + m ρ / ρ ^ n))) := by
        intro ρ hρ
        have h1 := (Real.continuous_exp.tendsto _).comp (hGlim ρ hρ.1 hρ.2).neg
        have h2 := (hIlim ρ hρ.1 hρ.2).div_const (ρ ^ n)
        exact h1.mul (tendsto_const_nhds.add h2)
      intro σ hσ ρ hρ hσρ
      have h := le_of_tendsto_of_tendsto' (hΨlim σ hσ) (hΨlim ρ hρ) (fun k => hmono k hσ hρ hσρ)
      have e : ∀ r, F r * (r ^ n)⁻¹ * m r + F r - 1 = F r * (1 + m r / r ^ n) - 1 := by
        intro r
        ring
      show F σ * (σ ^ n)⁻¹ * m σ + F σ - 1 ≤ F ρ * (ρ ^ n)⁻¹ * m ρ + F ρ - 1
      rw [e σ, e ρ]
      linarith
  have dohr_lmono_open_ball_monotone : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧ (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohrLmonoOpenBallAux_rpow_le
    intro n ℓ hn p hnp μ H y R Λ hR hΛ hΛ1 hμR hH hsmall hrad
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp1 : 1 < p := by linarith
    have hp0 : 0 < p := by linarith
    have hβ1 : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hnp
    have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
      mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ.le
    obtain ⟨hJ, hNR⟩ := dohrLmonoOpenBallAux_small hp0 hR hκ hsmall
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
      ⟨_, rfl⟩
    rw [← hNdef] at hNR
    have hN0 : 0 ≤ N := by
      rw [hNdef]
      exact Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hNR' : N * R ^ (1 - (n : ℝ) / p) / (1 - (n : ℝ) / p) ≤ Λ / 4 := by
      have h1 : 0 < 1 - (n : ℝ) / p := by linarith
      rw [div_le_iff₀ h1]
      calc N * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := hNR
        _ = Λ / 4 * (1 - (n : ℝ) / p) := by
            field_simp
    have hNt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ N := by
      intro t htR
      rw [hNdef]
      exact Real.rpow_le_rpow ENNReal.toReal_nonneg
        (ENNReal.toReal_mono hJ (lintegral_mono_set (closedBall_subset_closedBall htR)))
        (by positivity)
    have hJt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ) < ⊤ := fun t htR =>
      lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall htR)) hJ.lt_top
    -- the cutoffs
    obtain ⟨φ, hφC, hφanti, hφone, hφzero, hφ01, hφlim⟩ := dohrLmonoOpenBallAux_cutoffs
    have hφc : ∀ k, Continuous (φ k) := fun k => (hφC k).continuous
    -- the cutoff quantities
    obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t =
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I k t / t ^ n) :=
      ⟨_, fun _ _ => rfl⟩
    have hzero_far : ∀ k t, 0 < t → ∀ x : Amb n ℓ, t ≤ ‖x - y‖ → φ k (‖x - y‖ / t) = 0 := by
      intro k t ht x hx
      exact hφzero k _ ((one_le_div ht).mpr hx)
    have hInn : ∀ k t, 0 ≤ I k t := fun k t => by
      rw [hI]
      exact integral_nonneg fun x => (hφ01 k _).1
    -- the uniform curvature bound, from the Hölder sibling
    have hab : ∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-((n : ℝ) / p)) := by
      intro k t ht htR
      have hμt : μ (closedBall y t) < ⊤ :=
        lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall htR.le)) hμR
      have hHt : IntegrableOn H (closedBall y t) μ :=
        hH.mono_set (closedBall_subset_closedBall htR.le)
      have hhol : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) *
            (∫ x, φ k (‖x - y‖ / t) ∂μ) ^ (1 - 1 / p) :=
        dohr_lmono_curvature_holder n ℓ p hp1 μ H (fun x => φ k (‖x - y‖ / t)) y t ht.le hμt hHt
          (hJt t htR.le)
          ((hφc k).comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          (fun x => hφ01 k (‖x - y‖ / t)) (fun x hx => hzero_far k t ht x hx.le)
      have hL : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * N * I k t ^ (1 - 1 / p) := by
        refine hhol.trans ?_
        rw [← hI]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hNt t htR.le) ht.le)
          (Real.rpow_nonneg (hInn k t) _)
      rw [ha]
      exact dohrLmonoOpenBallAux_abound n hp1 ht hN0 (hInn k t) hL
    -- fixed-cutoff monotonicity, from the sibling
    have hfix : ∀ k, ContinuousOn (a k) (Ioo 0 R) ∧
        MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) (Ioo 0 R) :=
      fun k => dohr_lmono_fixed_cutoff_monotone n ℓ μ H y (φ k) (I k) (a k) R N ((n : ℝ) / p) hβ1
        hμR hH (hφC k) (hφanti k) (hφzero k)
        (fun ρ h1 h2 => hrad (φ k) ρ (hφC k) (hφanti k) (hφone k) (hφzero k) h1 h2) (hI k) (ha k)
        (hab k)
    -- passage to the limit `k → ∞` under the integral sign
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y R) := ⟨_, rfl⟩
    have hνfin : IsFiniteMeasure ν := by
      rw [hν]
      exact isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := by
      rw [hν]
      exact hH
    have hout : ∀ t, t < R → ∀ x, x ∉ closedBall y R → t ≤ ‖x - y‖ := by
      intro t htR x hx
      have : R < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      linarith
    have hIν : ∀ k t, 0 < t → t < R → I k t = ∫ x, φ k (‖x - y‖ / t) ∂ν := by
      intro k t ht htR
      rw [hI, hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hzero_far k t ht x (hout t htR x hx)
    have hLν : ∀ k t, 0 < t → t < R →
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro k t ht htR
      rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hzero_far k t ht x (hout t htR x hx), zero_mul]
    have hφpt : ∀ t, 0 < t → ∀ x : Amb n ℓ, Tendsto (fun k => φ k (‖x - y‖ / t)) atTop
        (𝓝 ((ball y t).indicator (fun _ => (1 : ℝ)) x)) := by
      intro t ht x
      by_cases hx : x ∈ ball y t
      · rw [indicator_of_mem hx]
        have hlt : ‖x - y‖ / t < 1 := by
          rw [div_lt_one ht]
          simpa [mem_ball, dist_eq_norm] using hx
        exact tendsto_const_nhds.congr' ((hφlim _ hlt).mono fun k hk => hk.symm)
      · rw [indicator_of_notMem hx]
        have hle : t ≤ ‖x - y‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
        have : (fun k => φ k (‖x - y‖ / t)) = fun _ => 0 :=
          funext fun k => hzero_far k t ht x hle
        rw [this]
        exact tendsto_const_nhds
    have hIlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => I k t) atTop (𝓝 ((μ (ball y t)).toReal)) := by
      intro t ht htR
      have hm : ∫ x, (ball y t).indicator (fun _ => (1 : ℝ)) x ∂ν = (μ (ball y t)).toReal := by
        rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one,
          Measure.real_def, hν, Measure.restrict_apply measurableSet_ball,
          inter_eq_left.mpr (ball_subset_closedBall.trans (closedBall_subset_closedBall htR.le))]
      rw [← hm]
      have hcongr : (fun k => I k t) = fun k => ∫ x, φ k (‖x - y‖ / t) ∂ν :=
        funext fun k => hIν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1)
        ?_ ?_
      · intro k
        exact ((hφc k).comp
          (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
      · intro k
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        exact (hφ01 k _).2
      · exact Eventually.of_forall fun x => hφpt t ht x
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t =
        (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν) / t ^ (n + 1) /
          (1 + (μ (ball y t)).toReal / t ^ n) := ⟨_, fun _ => rfl⟩
    have hLlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) atTop
          (𝓝 (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν)) := by
      intro t ht htR
      have hcongr : (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν :=
        funext fun k => hLν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun x => R * ‖H x‖) ?_
        (hHν.norm.const_mul R) ?_ ?_
      · intro k
        have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ k (‖x - y‖ / t)) ν :=
          ((hφc k).comp
            (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
          continuous_inner.comp_aestronglyMeasurable
            ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
              hHν.aestronglyMeasurable)
        exact h1.mul h2
      · intro k
        rw [hν, ae_restrict_iff' measurableSet_closedBall]
        refine Eventually.of_forall fun x hx => ?_
        have hxR : ‖x - y‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
        calc φ k (‖x - y‖ / t) * ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ 1 * (R * ‖H x‖) :=
              mul_le_mul (hφ01 k _).2 hinner (norm_nonneg _) zero_le_one
          _ = R * ‖H x‖ := one_mul _
      · refine Eventually.of_forall fun x => ?_
        have h := (hφpt t ht x).mul_const (inner ℝ (x - y) (H x))
        by_cases hx : x ∈ ball y t
        · simpa [indicator_of_mem hx] using h
        · simpa [indicator_of_notMem hx] using h
    have halim : ∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
      intro t ht htR
      have hm0 : 0 ≤ (μ (ball y t)).toReal := ENNReal.toReal_nonneg
      have hden : 1 + (μ (ball y t)).toReal / t ^ n ≠ 0 := by
        have := div_nonneg hm0 (pow_pos ht n).le
        linarith
      have hcongr : (fun k => a k t) = fun k =>
          (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) /
            (1 + I k t / t ^ n) :=
        funext fun k => ha k t
      rw [hcongr, ha₀]
      exact ((hLlim t ht htR).div_const _).div
        (tendsto_const_nhds.add ((hIlim t ht htR).div_const _)) hden
    exact dohrLmonoOpenBallAux_limit n hR hβ1 hN0 hNR' hΛ hΛ1 a I a₀
      (fun t => (μ (ball y t)).toReal) (fun k => (hfix k).1) hab halim hIlim (fun k => (hfix k).2)
  have dohr_lmono_closedBall_of_ball : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), μ (closedBall y R) < ⊤ → ContinuousOn F (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone
    intro n ℓ μ y R F hfin hFc hmono
    have hlim : ∀ r ∈ Ioo 0 R, Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1)
        (𝓝[>] r) (𝓝 (F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1)) := by
      intro r hr
      have hfin' : μ (ball y ((r + R) / 2)) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hr.2]))))
      have hμ : Tendsto (fun s => μ (ball y s)) (𝓝[>] r) (𝓝 (μ (closedBall y r))) := by
        have h := tendsto_measure_biInter_gt (μ := μ) (s := fun s => ball y s) (a := r)
          (fun s _ => measurableSet_ball.nullMeasurableSet)
          (fun i j _ hij => ball_subset_ball hij)
          ⟨(r + R) / 2, by linarith [hr.2], hfin'⟩
        rw [biInter_gt_ball] at h
        exact h
      have hμr : Tendsto (fun s => (μ (ball y s)).toReal) (𝓝[>] r) (𝓝 (μ (closedBall y r)).toReal) :=
        (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hfin.ne
          (measure_mono (closedBall_subset_closedBall hr.2.le)))).comp hμ
      have hF : Tendsto F (𝓝[>] r) (𝓝 (F r)) :=
        ((hFc r hr).continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.mono_left nhdsWithin_le_nhds
      have hpow : Tendsto (fun s : ℝ => (s ^ n)⁻¹) (𝓝[>] r) (𝓝 ((r ^ n)⁻¹)) :=
        (((continuous_pow n).tendsto r).inv₀ (pow_ne_zero n hr.1.ne')).mono_left nhdsWithin_le_nhds
      exact (((hF.mul hpow).mul hμr).add hF).sub_const 1
    intro a ha b hb hab
    rcases hab.lt_or_eq with hab | rfl
    · have h1 : ∀ s ∈ Ioo b R, F a * (a ^ n)⁻¹ * (μ (closedBall y a)).toReal + F a - 1 ≤
          F s * (s ^ n)⁻¹ * (μ (ball y s)).toReal + F s - 1 := by
        intro s hs
        apply le_of_tendsto (hlim a ha)
        filter_upwards [Ioo_mem_nhdsGT (hab.trans hs.1)] with u hu
        exact hmono ⟨ha.1.trans hu.1, hu.2.trans hs.2⟩ ⟨hb.1.trans hs.1, hs.2⟩ hu.2.le
      apply ge_of_tendsto (hlim b hb)
      filter_upwards [Ioo_mem_nhdsGT hb.2] with s hs
      exact h1 s hs
    · exact le_rfl
  have dohr_lmono_density_of_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), 0 < R → μ (closedBall y R) < ⊤ → (∀ r ∈ Ioo 0 R, 0 ≤ F r) → Tendsto F (𝓝[>] 0) (𝓝 1) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) → ∃ t : ℝ, 0 ≤ t ∧ Tendsto (fun r : ℝ => μ (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone dohr_lmono_closedBall_of_ball
    intro n ℓ μ y R F hR hfin hF0 hF1 hmono
    set Φ := fun r : ℝ => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 with hΦ
    have hne : (Ioo (0:ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
    have hbdd : BddBelow (Φ '' Ioo 0 R) := by
      refine ⟨-1, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have h1 := hF0 r hr
      have h2 : 0 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
        mul_nonneg (mul_nonneg h1 (inv_nonneg.2 (pow_nonneg hr.1.le n))) ENNReal.toReal_nonneg
      simp only [hΦ]
      linarith
    set L := sInf (Φ '' Ioo 0 R) with hL
    have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := hmono.tendsto_nhdsWithin_Ioo_right hne hbdd
    set g := fun r : ℝ => (r ^ n)⁻¹ * (μ (closedBall y r)).toReal with hg_def
    have hg : Tendsto g (𝓝[>] 0) (𝓝 L) := by
      have h := ((hΦL.sub hF1).add_const 1).div hF1 one_ne_zero
      have heq : (fun r => (Φ r - F r + 1) / F r) =ᶠ[𝓝[>] 0] g := by
        filter_upwards [hF1.eventually (lt_mem_nhds (by norm_num : (1:ℝ) / 2 < 1))] with r hr
        have hFr : F r ≠ 0 := by linarith
        simp only [hΦ, hg_def]
        field_simp
        ring
      simpa using h.congr' heq
    have hL0 : 0 ≤ L := by
      apply ge_of_tendsto hg
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_nonneg (inv_nonneg.2 (pow_nonneg (le_of_lt hr) n)) ENNReal.toReal_nonneg
    have hω : 0 < unitBallVolume n := by
      unfold unitBallVolume
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    refine ⟨L / unitBallVolume n, div_nonneg hL0 hω.le, ?_, ?_⟩
    · have h := ENNReal.tendsto_ofReal (hg.div_const (unitBallVolume n))
      apply h.congr'
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      have hmr : μ (closedBall y r) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (closedBall_subset_closedBall hr.2.le))
      have hr0 : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr.1 n)
      rw [← ENNReal.ofReal_toReal hmr, ← ENNReal.ofReal_div_of_pos hr0]
      congr 1
      simp only [hg_def]
      field_simp
    · rw [mul_div_cancel₀ _ hω.ne']
      exact hΦL
  clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit
  intro n ℓ hn U hU V H p hp hH y R Λ hR hBR hrank hmeas hΛ hΛ1 hsmall
  -- `μ_V(B_R(y)) < ∞`: `B_R(y)` is a compact subset of `U` and `θ` is integrable on `M ∩ B_R(y)`.
  have hfin : V.weight (closedBall y R) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y R) hBR).setLIntegral_lt_top
  -- `H` is `μ_V`-integrable on the compact set `B_R(y) ⊆ U`.
  have hHint : IntegrableOn H (closedBall y R) V.weight :=
    hH.1.integrableOn_compact_subset hBR (isCompact_closedBall y R)
  obtain ⟨F, hFc, hFb, hF1, hmono⟩ :=
    dohr_lmono_open_ball_monotone n ℓ hn p hp V.weight H y R Λ hR hΛ hΛ1 hfin hHint hsmall
      (dohr_lmono_radial_inequality n ℓ U V H hH y R hBR hrank hmeas)
  have hmono' := dohr_lmono_closedBall_of_ball n ℓ V.weight y R F hfin hFc hmono
  obtain ⟨t, ht0, hdens, hlim⟩ := dohr_lmono_density_of_monotone n ℓ V.weight y R F hR hfin
    (fun r hr => (Real.exp_pos _).le.trans (hFb r hr).2.1) hF1 hmono'
  exact ⟨F, hFb, hF1, hmono', t, ht0, hdens, hlim⟩

end Submission

end GMT.Ch05
