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

set_option maxHeartbeats 10000000 in
/-- **Affine approximation of almost-harmonic Lipschitz maps** (Simon Ch. 5, proof of
Theorem 4.5, steps (17)–(19)).  Assume the Harmonic Approximation Lemma 3.1.  For `n ≥ 1` and `ℓ`
there is `C = C(n, ℓ) > 0` such that for every `ε ∈ (0, 1)` there is `δ_ε > 0` with the following
property: if `f : ℝⁿ → ℝ^ℓ` is Lipschitz on `B_r(0)`, `|f| ≤ h` on `B̆_r(0)`,
`∫_{B̆_r} |Df|² ≤ E rⁿ` and `|∫_{B̆_r} ∇fʲ · ∇ζ| ≤ δ_ε √E sup|∇ζ| rⁿ` for all `ζ ∈ C^∞_c(B̆_r)`,
then there are `a ∈ ℝ^ℓ` and a linear `A` with `|A| ≤ C √E`, `|a| ≤ C (h + r √(εE))` and
`∫_{B̆_{er}} |f - (a + A x)|² ≤ C (ε + e^{n+4}) E r^{n+2}` for `e ∈ (0, 1/4]`.

Proof: rescale each component to `F_j(z) = fʲ(rz)/(r√E)`, apply Lemma 3.1 to get harmonic `u_j`,
and use interior estimates for harmonic functions, proved here from the mean value property
`∫ u(x + y) φ(y) dy = (∫ φ) u(x)` for a smooth radial kernel `φ` (scaling argument plus Lipschitz
integration by parts), to define `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0) · x)_j`. -/
theorem ted_harmonic_affine_approx : HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δε : ℝ, 0 < δε ∧ ∀ (r E h : ℝ) (f : Rn n → Rn ℓ) (L : ℝ≥0), 0 < r → 0 < E → 0 ≤ h → LipschitzOnWith L f (closedBall 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖f x‖ ≤ h) → ∫ x in ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ E * r ^ n → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 r → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) r, inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ δε * Real.sqrt E * M * r ^ n) → ∃ (a : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ C * Real.sqrt E ∧ ‖a‖ ≤ C * (h + r * Real.sqrt (ε * E)) ∧ ∀ e : ℝ, 0 < e → e ≤ 1 / 4 → ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
  intro hHAL n ℓ hn
  /- Step 1 (kernel).  A smooth radial kernel `φ(y) = -64 τ'(1 - 32|y|²)` supported in `B_{1/5}`
  with `∫ φ ≠ 0`, together with its potential `Ψ(y) = τ(1 - 32|y|²)`, `DΨ(y)[w] = φ(y) ⟪y, w⟫`
  (`τ` = `Real.smoothTransition`). -/
  obtain ⟨φ, Ψ, hφc, hφ0, hφcs, ⟨Lφ, hφL⟩, hc0, ⟨LΨ, hΨL⟩, hΨcs, hΨd, hΨfd, hΨ0⟩ :
      ∃ (φ Ψ : Rn n → ℝ), Continuous φ ∧ (∀ y : Rn n, 1/5 ≤ ‖y‖ → φ y = 0) ∧
        HasCompactSupport φ ∧ (∃ Lφ : ℝ≥0, LipschitzWith Lφ φ) ∧ (∫ y, φ y) ≠ 0 ∧
        (∃ LΨ : ℝ≥0, LipschitzWith LΨ Ψ) ∧ HasCompactSupport Ψ ∧ Differentiable ℝ Ψ ∧
        (∀ y w : Rn n, fderiv ℝ Ψ y w = φ y * inner ℝ y w) ∧
        (∀ y : Rn n, 1/5 ≤ ‖y‖ → Ψ y = 0) := by
    have hτ : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
    have hτ' : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
      (contDiff_infty_iff_deriv.1 hτ).2
    have hτ'0 : ∀ x : ℝ, x < 0 → deriv Real.smoothTransition x = 0 := by
      intro x hx
      have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hx] with z hz
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
      rw [this.deriv_eq]
      simp
    have hτ'nn : ∀ x : ℝ, 0 ≤ deriv Real.smoothTransition x :=
      fun x => Real.smoothTransition.monotone.deriv_nonneg
    have hnsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => 1 - 32 * ‖y‖ ^ 2) :=
      contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hneg : ∀ y : Rn n, 1/5 ≤ ‖y‖ → 1 - 32 * ‖y‖ ^ 2 < 0 := by
      intro y hy
      nlinarith
    set φ : Rn n → ℝ := fun y => -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) with hφdef
    set Ψ : Rn n → ℝ := fun y => Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) with hΨdef
    have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_const.mul (hτ'.comp hnsq)
    have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := hτ.comp hnsq
    have hφ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ → φ y = 0 := by
      intro y hy
      simp only [hφdef, hτ'0 _ (hneg y hy), mul_zero]
    have hΨ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ → Ψ y = 0 := by
      intro y hy
      exact Real.smoothTransition.zero_of_nonpos (hneg y hy).le
    have hφcs : HasCompactSupport φ := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1/5)) (fun y hy => hφ0 y ?_)
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le
    have hΨcs : HasCompactSupport Ψ := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1/5)) (fun y hy => hΨ0 y ?_)
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le
    obtain ⟨Lφ, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφcs hφs (by simp)
    obtain ⟨LΨ, hΨL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hΨcs hΨs (by simp)
    -- the derivative of Ψ
    have hΨd : ∀ y : Rn n, HasFDerivAt Ψ
        (deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) • (-(32 : ℝ) • (2 • innerSL ℝ y))) y := by
      intro y
      have h1 : HasFDerivAt (fun y : Rn n => 1 - 32 * ‖y‖ ^ 2) (-(32 : ℝ) • (2 • innerSL ℝ y)) y := by
        have := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (32 : ℝ)).const_sub 1
        convert this using 1
        ext w
        simp
      have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2))
          (1 - 32 * ‖y‖ ^ 2) :=
        ((hτ.differentiable (by simp)) _).hasDerivAt
      exact h2.comp_hasFDerivAt y h1
    have hΨfd : ∀ y w : Rn n, fderiv ℝ Ψ y w = φ y * inner ℝ y w := by
      intro y w
      rw [(hΨd y).fderiv]
      simp [hφdef, innerSL_apply_apply]
      ring
    -- the integral of φ is nonzero
    have hφint : (∫ y, φ y) ≠ 0 := by
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.smoothTransition
        (deriv Real.smoothTransition) (zero_lt_one' ℝ) hτ.continuous.continuousOn
        (fun x _ => ((hτ.differentiable (by simp)) x).hasDerivAt)
      rw [Real.smoothTransition.one, Real.smoothTransition.zero] at hcd
      norm_num at hcd
      set i0 : Fin n := ⟨0, hn⟩
      set y1 : Rn n := Real.sqrt ((1 - c) / 32) • EuclideanSpace.single i0 (1 : ℝ)
      have hy1 : ‖y1‖ ^ 2 = (1 - c) / 32 := by
        simp only [y1, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith [hc.2])]
      have hpos : 0 < ∫ y, -φ y := by
        refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y1)
          hφs.continuous.neg hφcs.neg (fun y => ?_) ?_
        · simp only [Pi.zero_apply, hφdef]
          nlinarith [hτ'nn (1 - 32 * ‖y‖ ^ 2)]
        · simp only [hφdef, hy1]
          have : 1 - 32 * ((1 - c) / 32) = c := by ring
          rw [this, hcd]
          norm_num
      rw [integral_neg] at hpos
      linarith
    exact ⟨φ, Ψ, hφs.continuous, hφ0, hφcs, ⟨Lφ, hφL⟩, hφint, ⟨LΨ, hΨL⟩, hΨcs,
      hΨs.differentiable (by simp), hΨfd, hΨ0⟩
  obtain ⟨Φ, hΦ'⟩ := hφcs.exists_bound_of_continuous hφc
  have hΦ : ∀ y, |φ y| ≤ Φ := fun y => by simpa [Real.norm_eq_abs] using hΦ' y
  have hΦ0 : 0 ≤ Φ := (abs_nonneg _).trans (hΦ 0)
  /- Step 2 (mean value property).  For `u` harmonic on `B₁` and `|x| < 1/2`,
  `∫ u(x + y) φ(y) dy = (∫ φ) u(x)`: `t ↦ ∫ u(x + t y) φ(y) dy` has derivative
  `∫ Du(x + t y)[y] φ(y) dy = Σᵢ ∫ ∂ᵢΨ ∂ᵢu(x + t ·)`, which vanishes by Lipschitz integration by
  parts (`LipschitzWith.integral_lineDeriv_mul_eq`) since `Δu = 0`. -/
  have hMVP : ∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) → ∀ x : Rn n,
      ‖x‖ < 1/2 → ∫ y, u (x + y) * φ y = (∫ y, φ y) * u x := by
    -- general facts about the kernel
    have hφsupp : tsupport φ ⊆ closedBall (0 : Rn n) (1/5) := by
      refine closure_minimal (fun y hy => ?_) isClosed_closedBall
      rw [mem_closedBall, dist_zero_right]
      by_contra h
      exact hy (hφ0 y (not_le.1 h).le)
    have hpat : ∀ g : Rn n → ℝ, (∀ y : Rn n, ‖y‖ ≤ 1/5 → ContinuousAt g y) →
        Continuous (fun y => g y * φ y) := by
      intro g hg
      refine continuous_of_tsupport (fun y hy => ?_)
      have hy' : y ∈ closedBall (0 : Rn n) (1/5) := hφsupp (tsupport_mul_subset_right hy)
      rw [mem_closedBall, dist_zero_right] at hy'
      exact (hg y hy').mul hφc.continuousAt
    intro u hu x hx
    have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
    have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
      ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    have hD1 : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).1 hC2).2.2
    have hD1cont : ContinuousOn (fderiv ℝ u) (ball 0 1) := hD1.continuousOn
    have hD2 : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
      fun z hz => ((hD1.differentiableOn one_ne_zero) z hz).differentiableAt
        (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ z ∈ closedBall (0 : Rn n) (9/10), ‖fderiv ℝ u z‖ ≤ M1 :=
      (isCompact_closedBall 0 (9/10)).exists_bound_of_continuousOn
        (hD1cont.mono (closedBall_subset_ball (by norm_num)))
    have hgeo : ∀ t : ℝ, t ∈ Ioo (-2:ℝ) 2 → ∀ y : Rn n, ‖y‖ ≤ 1/4 →
        ‖x + t • y‖ ≤ ‖x‖ + 2 * ‖y‖ := by
      intro t ht y hy
      calc ‖x + t • y‖ ≤ ‖x‖ + ‖t • y‖ := norm_add_le _ _
        _ = ‖x‖ + |t| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖x‖ + 2 * ‖y‖ := by
          have : |t| ≤ 2 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
          nlinarith [norm_nonneg y]
    have hin1 : ∀ t : ℝ, t ∈ Ioo (-2:ℝ) 2 → ∀ y : Rn n, ‖y‖ ≤ 1/4 → x + t • y ∈ ball (0 : Rn n) 1 := by
      intro t ht y hy
      rw [mem_ball, dist_zero_right]
      linarith [hgeo t ht y hy]
    have hin9 : ∀ t : ℝ, t ∈ Ioo (-2:ℝ) 2 → ∀ y : Rn n, ‖y‖ ≤ 1/5 →
        x + t • y ∈ closedBall (0 : Rn n) (9/10) := by
      intro t ht y hy
      rw [mem_closedBall, dist_zero_right]
      linarith [hgeo t ht y (by linarith)]
    -- the radial derivative of `t ↦ ∫ u (x + t y) φ(y)` vanishes
    set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
    have hzero : ∀ t ∈ Ioo (-2:ℝ) 2, ∫ y, fderiv ℝ u (x + t • y) y * φ y = 0 := by
      intro t ht
      have hext : ∀ i : Fin n, ∃ (K : ℝ≥0) (W : Rn n → ℝ), LipschitzWith K W ∧
          EqOn (fun y => fderiv ℝ u (x + t • y) (b i)) W (closedBall 0 (1/4)) := by
        intro i
        have h1 : ContDiffOn ℝ 1 (fun y : Rn n => x + t • y) (closedBall 0 (1/4)) :=
          (by fun_prop : ContDiff ℝ 1 (fun y : Rn n => x + t • y)).contDiffOn
        have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u (x + t • y)) (closedBall 0 (1/4)) :=
          hD1.comp h1 (fun y hy => hin1 t ht y (by simpa using hy))
        have hcd : ContDiffOn ℝ 1 (fun y => fderiv ℝ u (x + t • y) (b i)) (closedBall 0 (1/4)) :=
          h2.clm_apply contDiffOn_const
        obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
          (isCompact_closedBall _ _)
        obtain ⟨W, hW, hEq⟩ := hK.extend_real
        exact ⟨_, W, hW, hEq⟩
      choose K W hWL hWeq using hext
      have hibp : ∀ i, ∫ y, lineDeriv ℝ (W i) y (b i) * Ψ y =
          ∫ y, lineDeriv ℝ Ψ y (-(b i)) * W i y :=
        fun i => (hWL i).integral_lineDeriv_mul_eq hΨL hΨcs (b i)
      -- left side: pointwise zero
      have hL : ∀ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y = 0 := by
        intro y
        by_cases hy : ‖y‖ < 1/4
        · have hz : x + t • y ∈ ball (0 : Rn n) 1 := hin1 t ht y hy.le
          have hder : ∀ i, HasFDerivAt (fun y => fderiv ℝ u (x + t • y) (b i))
              (((fderiv ℝ (fderiv ℝ u) (x + t • y)).comp (t • ContinuousLinearMap.id ℝ (Rn n))).flip (b i)) y := by
            intro i
            have hpath : HasFDerivAt (fun y : Rn n => x + t • y) (t • ContinuousLinearMap.id ℝ (Rn n)) y :=
              ((hasFDerivAt_id y).const_smul t).const_add x
            have hc := (hD2 (x + t • y) hz).comp y hpath
            have := hc.clm_apply (hasFDerivAt_const (b i) y)
            rw [ContinuousLinearMap.comp_zero, zero_add] at this
            exact this
          have hnhd : closedBall (0 : Rn n) (1/4) ∈ 𝓝 y :=
            closedBall_mem_nhds_of_mem (by rw [mem_ball, dist_zero_right]; exact hy)
          have hline : ∀ i, lineDeriv ℝ (W i) y (b i) =
              t * fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) := by
            intro i
            have hWd := (hder i).congr_of_eventuallyEq
              (Filter.eventuallyEq_of_mem hnhd (fun z hz => (hWeq i hz).symm))
            rw [hWd.hasLineDerivAt (b i) |>.lineDeriv]
            simp
          have hlap : ∑ i, fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) = 0 := by
            have h0 : Laplacian.laplacian u (x + t • y) = 0 := (hu _ hz).2.eq_of_nhds
            rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b] at h0
            simpa [iteratedFDeriv_two_apply] using h0
          simp_rw [hline]
          calc ∑ i, t * fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) * Ψ y
              = t * Ψ y * ∑ i, fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
            _ = 0 := by rw [hlap, mul_zero]
        · have : Ψ y = 0 := hΨ0 y (by linarith [not_lt.1 hy])
          simp [this]
      -- right side: pointwise the radial derivative
      have hR : ∀ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y = -(fderiv ℝ u (x + t • y) y * φ y) := by
        intro y
        have hld : ∀ i, lineDeriv ℝ Ψ y (-(b i)) = -(φ y * inner ℝ y (b i)) := by
          intro i
          rw [(hΨd y).lineDeriv_eq_fderiv, hΨfd, inner_neg_right, mul_neg]
        simp_rw [hld]
        by_cases hφy : φ y = 0
        · simp [hφy]
        · have hy : ‖y‖ ≤ 1/4 := by
            by_contra h
            exact hφy (hφ0 y (by linarith [not_le.1 h]))
          have hWy : ∀ i, W i y = fderiv ℝ u (x + t • y) (b i) := fun i =>
            (hWeq i (by rw [mem_closedBall, dist_zero_right]; exact hy)).symm
          simp_rw [hWy]
          have hsum : fderiv ℝ u (x + t • y) y =
              ∑ i, inner ℝ y (b i) * fderiv ℝ u (x + t • y) (b i) := by
            set L := fderiv ℝ u (x + t • y)
            conv_lhs => rw [← b.sum_repr' y]
            simp [map_sum, map_smul, real_inner_comm]
          rw [hsum, Finset.sum_mul, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      have hΨint : Integrable Ψ := hΨL.continuous.integrable_of_hasCompactSupport hΨcs
      have hLi : ∀ i, Integrable (fun y => lineDeriv ℝ (W i) y (b i) * Ψ y) :=
        fun i => hΨint.mul_of_top_right ((hWL i).memLp_lineDeriv (b i))
      have hRi : ∀ i, Integrable (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) := by
        intro i
        have hfun : (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) =
            fun y => φ y * (-(inner ℝ y (b i)) * W i y) := by
          funext y
          rw [(hΨd y).lineDeriv_eq_fderiv, hΨfd, inner_neg_right]
          ring
        rw [hfun]
        refine Continuous.integrable_of_hasCompactSupport ?_ (hφcs.mul_right)
        exact hφc.mul ((continuous_id.inner continuous_const).neg.mul (hWL i).continuous)
      have hsumeq : ∫ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y =
          ∫ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y := by
        rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
        exact Finset.sum_congr rfl (fun i _ => hibp i)
      simp only [hL, hR, integral_zero, integral_neg] at hsumeq
      linarith
    -- differentiation under the integral sign
    have hderiv : ∀ t ∈ Ioo (-2:ℝ) 2, HasDerivAt (fun t => ∫ y, u (x + t • y) * φ y)
        (∫ y, fderiv ℝ u (x + t • y) y * φ y) t := by
      intro t ht
      have hcontF : ∀ s ∈ Ioo (-2:ℝ) 2, Continuous (fun y => u (x + s • y) * φ y) := by
        intro s hs
        refine hpat (fun y => u (x + s • y)) (fun y hy => ?_)
        have hz := hin1 s hs y (by linarith)
        exact ((hdiff _ hz).continuousAt).comp (f := fun y : Rn n => x + s • y) (by fun_prop)
      have hcontF' : Continuous (fun y => fderiv ℝ u (x + t • y) y * φ y) := by
        refine hpat (fun y => fderiv ℝ u (x + t • y) y) (fun y hy => ?_)
        have hz := hin1 t ht y (by linarith)
        have h1 : ContinuousAt (fun y : Rn n => fderiv ℝ u (x + t • y)) y :=
          (hD1cont.continuousAt (isOpen_ball.mem_nhds hz)).comp (f := fun y : Rn n => x + t • y)
            (by fun_prop)
        exact h1.clm_apply continuousAt_id
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun y => M1 * (1/5) * |φ y|)
        (F := fun t y => u (x + t • y) * φ y) (F' := fun t y => fderiv ℝ u (x + t • y) y * φ y)
        (Ioo_mem_nhds ht.1 ht.2) ?_ ?_ ?_ ?_ ?_ ?_).2
      · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact (hcontF s hs).aestronglyMeasurable
      · exact (hcontF t ht).integrable_of_hasCompactSupport hφcs.mul_left
      · exact hcontF'.aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y s hs => ?_)
        by_cases hφy : φ y = 0
        · simp [hφy]
        · have hy : ‖y‖ ≤ 1/5 := by
            by_contra h
            exact hφy (hφ0 y (not_le.1 h).le)
          have hM := hM1 _ (hin9 s hs y hy)
          rw [norm_mul, Real.norm_eq_abs (φ y)]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          calc ‖fderiv ℝ u (x + s • y) y‖ ≤ ‖fderiv ℝ u (x + s • y)‖ * ‖y‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ M1 * (1/5) := mul_le_mul hM hy (norm_nonneg _) ((norm_nonneg _).trans hM)
      · exact ((hφc.integrable_of_hasCompactSupport hφcs).abs).const_mul _
      · refine Filter.Eventually.of_forall (fun y s hs => ?_)
        by_cases hφy : φ y = 0
        · simp only [hφy, mul_zero]
          exact hasDerivAt_const s 0
        · have hy : ‖y‖ ≤ 1/5 := by
            by_contra h
            exact hφy (hφ0 y (not_le.1 h).le)
          have hz := hin1 s hs y (by linarith)
          have hpath : HasDerivAt (fun s : ℝ => x + s • y) y s := by
            simpa using ((hasDerivAt_id s).smul_const y).const_add x
          exact ((hdiff _ hz).comp_hasDerivAt s hpath).mul_const (φ y)
    -- mean value theorem in `t`
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y, u (x + t • y) * φ y)
      (fun t => ∫ y, fderiv ℝ u (x + t • y) y * φ y) (zero_lt_one' ℝ)
      (fun t ht => (hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
      (fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    rw [hzero c ⟨by linarith [hc.1], by linarith [hc.2]⟩] at hcd
    simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hcd
    rw [integral_const_mul] at hcd
    linarith
  /- Step 3: differentiating the mean value identity,
  `(∫ φ) Du(x) = ∫ φ(y) Du(x + y) dy` for `|x| < 1/2`. -/
  have hdMVP : ∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) → ∀ x : Rn n,
      ‖x‖ < 1/2 → (∫ y, φ y) • fderiv ℝ u x = ∫ y, φ y • fderiv ℝ u (x + y) := by
    have hφsupp : tsupport φ ⊆ closedBall (0 : Rn n) (1/5) := by
      refine closure_minimal (fun y hy => ?_) isClosed_closedBall
      rw [mem_closedBall, dist_zero_right]
      by_contra h
      exact hy (hφ0 y (not_le.1 h).le)
    have hpat : ∀ g : Rn n → ℝ, (∀ y : Rn n, ‖y‖ ≤ 1/5 → ContinuousAt g y) →
        Continuous (fun y => g y * φ y) := by
      intro g hg
      refine continuous_of_tsupport (fun y hy => ?_)
      have hy' : y ∈ closedBall (0 : Rn n) (1/5) := hφsupp (tsupport_mul_subset_right hy)
      rw [mem_closedBall, dist_zero_right] at hy'
      exact (hg y hy').mul hφc.continuousAt
    have hpat' : ∀ G : Rn n → (Rn n →L[ℝ] ℝ), (∀ y : Rn n, ‖y‖ ≤ 1/5 → ContinuousAt G y) →
        Continuous (fun y => φ y • G y) := by
      intro G hG
      refine continuous_of_tsupport (fun y hy => ?_)
      have hy' : y ∈ closedBall (0 : Rn n) (1/5) := hφsupp (tsupport_smul_subset_left _ _ hy)
      rw [mem_closedBall, dist_zero_right] at hy'
      exact hφc.continuousAt.smul (hG y hy')
    intro u hu x hx
    have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
    have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
      ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    have hD1cont : ContinuousOn (fderiv ℝ u) (ball 0 1) :=
      hC2.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ z ∈ closedBall (0 : Rn n) (9/10), ‖fderiv ℝ u z‖ ≤ M1 :=
      (isCompact_closedBall 0 (9/10)).exists_bound_of_continuousOn
        (hD1cont.mono (closedBall_subset_ball (by norm_num)))
    set δ := 1/2 - ‖x‖ with hδ
    have hδpos : 0 < δ := by linarith
    have hsmall : ∀ x' ∈ ball x δ, ‖x'‖ < 1/2 := by
      intro x' hx'
      rw [mem_ball, dist_eq_norm] at hx'
      have h2 : ‖x'‖ ≤ ‖x' - x‖ + ‖x‖ := by
        have := norm_add_le (x' - x) x
        simpa using this
      linarith
    have hin1 : ∀ x' : Rn n, ‖x'‖ < 1/2 → ∀ y : Rn n, ‖y‖ ≤ 1/5 → x' + y ∈ ball (0 : Rn n) 1 := by
      intro x' hx' y hy
      rw [mem_ball, dist_zero_right]
      linarith [norm_add_le x' y]
    have hin9 : ∀ x' : Rn n, ‖x'‖ < 1/2 → ∀ y : Rn n, ‖y‖ ≤ 1/5 →
        x' + y ∈ closedBall (0 : Rn n) (9/10) := by
      intro x' hx' y hy
      rw [mem_closedBall, dist_zero_right]
      linarith [norm_add_le x' y]
    have hcontF : ∀ x' : Rn n, ‖x'‖ < 1/2 → Continuous (fun y => u (x' + y) * φ y) := by
      intro x' hx'
      refine hpat (fun y => u (x' + y)) (fun y hy => ?_)
      exact ((hdiff _ (hin1 x' hx' y hy)).continuousAt).comp (f := fun y : Rn n => x' + y)
        (by fun_prop)
    have hcontF' : Continuous (fun y => φ y • fderiv ℝ u (x + y)) := by
      refine hpat' (fun y => fderiv ℝ u (x + y)) (fun y hy => ?_)
      exact (hD1cont.continuousAt (isOpen_ball.mem_nhds (hin1 x hx y hy))).comp
        (f := fun y : Rn n => x + y) (by fun_prop)
    have hP : HasFDerivAt (fun x' => ∫ y, u (x' + y) * φ y) (∫ y, φ y • fderiv ℝ u (x + y)) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun y => |φ y| * M1)
        (F := fun x' y => u (x' + y) * φ y) (F' := fun x' y => φ y • fderiv ℝ u (x' + y))
        (ball_mem_nhds x hδpos) ?_ ?_ ?_ ?_ ?_ ?_
      · filter_upwards [ball_mem_nhds x hδpos] with x' hx'
        exact (hcontF x' (hsmall x' hx')).aestronglyMeasurable
      · exact (hcontF x hx).integrable_of_hasCompactSupport hφcs.mul_left
      · exact hcontF'.aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y x' hx' => ?_)
        by_cases hφy : φ y = 0
        · simp [hφy]
        · have hy : ‖y‖ ≤ 1/5 := by
            by_contra h
            exact hφy (hφ0 y (not_le.1 h).le)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hM1 _ (hin9 x' (hsmall x' hx') y hy)) (abs_nonneg _)
      · exact ((hφc.integrable_of_hasCompactSupport hφcs).abs).mul_const _
      · refine Filter.Eventually.of_forall (fun y x' hx' => ?_)
        by_cases hφy : φ y = 0
        · simp only [hφy, mul_zero, zero_smul]
          exact hasFDerivAt_const 0 x'
        · have hy : ‖y‖ ≤ 1/5 := by
            by_contra h
            exact hφy (hφ0 y (not_le.1 h).le)
          have hz := hin1 x' (hsmall x' hx') y hy
          have h1 : HasFDerivAt (fun x' : Rn n => x' + y) (ContinuousLinearMap.id ℝ (Rn n)) x' :=
            (hasFDerivAt_id x').add_const y
          have h2 := ((hdiff _ hz).comp x' h1).mul_const (φ y)
          simpa using h2
    have heq : (fun x' => ∫ y, u (x' + y) * φ y) =ᶠ[𝓝 x] fun x' => (∫ y, φ y) * u x' := by
      filter_upwards [ball_mem_nhds x hδpos] with x' hx'
      exact hMVP u hu x' (hsmall x' hx')
    have h1 := hP.congr_of_eventuallyEq heq.symm
    have h2 := (hdiff x (by rw [mem_ball, dist_zero_right]; linarith)).const_mul (∫ y, φ y)
    exact (h2.unique h1)
  /- Step 4 (interior estimates, Simon 3.2–3.4).  `|u(0)| ≤ C₁ ∫_{B₁}|u|`,
  `|∇u(0)| ≤ C₁ ∫_{B₁}|∇u|` and `|u(z) - u(0) - ∇u(0)·z| ≤ C₃ |z|² ∫_{B₁}|∇u|` for `|z| ≤ 1/4`. -/
  obtain ⟨C₁, C₃, hC₁, hC₃, HE1, HE2⟩ : ∃ C₁ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₃ ∧
      (∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) → ∀ M : ℝ, 0 ≤ M →
        ∫⁻ x in ball (0 : Rn n) 1, ‖u x‖ₑ ≤ ENNReal.ofReal M → |u 0| ≤ C₁ * M) ∧
      (∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) → ∀ M : ℝ, 0 ≤ M →
        ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ≤ ENNReal.ofReal M →
        ‖gradient u 0‖ ≤ C₁ * M ∧
        ∀ z : Rn n, ‖z‖ ≤ 1/4 → |u z - u 0 - inner ℝ (gradient u 0) z| ≤ C₃ * M * ‖z‖ ^ 2) := by
    refine ⟨|∫ y, φ y|⁻¹ * Φ, |∫ y, φ y|⁻¹ * Lφ, mul_nonneg (inv_nonneg.2 (abs_nonneg _)) hΦ0,
      mul_nonneg (inv_nonneg.2 (abs_nonneg _)) Lφ.2, ?_⟩
    have hc0pos : 0 < |∫ y, φ y| := abs_pos.2 hc0
    have hΦ0 : 0 ≤ Φ := (abs_nonneg _).trans (hΦ 0)
    have hφout : ∀ y : Rn n, y ∉ ball (0 : Rn n) 1 → φ y = 0 := by
      intro y hy
      rw [mem_ball, dist_zero_right, not_lt] at hy
      exact hφ0 y (by linarith)
    -- generic bound: `‖∫ φ • G‖ ≤ Φ * M` when `∫⁻_{B_1} ‖G‖ₑ ≤ M`
    have hgen : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (G : Rn n → X) (M : ℝ), 0 ≤ M →
        ∫⁻ x in ball (0 : Rn n) 1, ‖G x‖ₑ ≤ ENNReal.ofReal M → ‖∫ y, φ y • G y‖ ≤ Φ * M := by
      intro X _ _ G M hM hGM
      refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg hΦ0 hM) ?_)
      calc ∫⁻ y, ENNReal.ofReal ‖φ y • G y‖
          ≤ ∫⁻ y, (ball (0 : Rn n) 1).indicator (fun y => ENNReal.ofReal Φ * ‖G y‖ₑ) y := by
            refine lintegral_mono (fun y => ?_)
            by_cases hy : y ∈ ball (0 : Rn n) 1
            · rw [indicator_of_mem hy, ofReal_norm, enorm_smul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hΦ y)
            · simp [hφout y hy]
        _ = ENNReal.ofReal Φ * ∫⁻ y in ball (0 : Rn n) 1, ‖G y‖ₑ := by
            rw [lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Φ * ENNReal.ofReal M := by gcongr
        _ = ENNReal.ofReal (Φ * M) := (ENNReal.ofReal_mul hΦ0).symm
    refine ⟨fun u hu M hM huM => ?_, fun u hu M hM huM => ?_⟩
    · have h1 := hMVP u hu 0 (by simp)
      simp only [zero_add] at h1
      have h2 := hgen (fun y => u y) M hM huM
      simp only [smul_eq_mul] at h2
      have h3 : |∫ y, φ y| * |u 0| ≤ Φ * M := by
        rw [← abs_mul, ← h1, ← Real.norm_eq_abs]
        simpa [mul_comm] using h2
      rw [mul_assoc, le_inv_mul_iff₀ hc0pos]
      linarith
    · have hgn : ∀ x, ‖gradient u x‖ₑ = ‖fderiv ℝ u x‖ₑ := by
        intro x
        simp [gradient, enorm]
      simp_rw [hgn] at huM
      have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
      have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
        ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
      have hD1cont : ContinuousOn (fderiv ℝ u) (ball 0 1) :=
        hC2.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
      -- (a) the gradient at the origin
      have hDu0 : ‖fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Φ * M := by
        have h1 := hdMVP u hu 0 (by simp)
        simp only [zero_add] at h1
        have h2 := hgen (fun y => fderiv ℝ u y) M hM huM
        rw [← h1, norm_smul, Real.norm_eq_abs] at h2
        rw [mul_assoc, le_inv_mul_iff₀ hc0pos]
        exact h2
      -- (b) Lipschitz bound for the derivative on `B_{1/4}`
      have hLipD : ∀ z : Rn n, ‖z‖ ≤ 1/4 →
          ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ := by
        intro z hz
        have hshift : ∀ z' : Rn n, ‖z'‖ ≤ 1/4 →
            ∫ y, φ y • fderiv ℝ u (z' + y) = ∫ w, φ (w - z') • fderiv ℝ u w := by
          intro z' hz'
          have := integral_add_left_eq_self (μ := (volume : Measure (Rn n)))
            (fun w => φ (w - z') • fderiv ℝ u w) z'
          simpa using this
        have hint : ∀ z' : Rn n, ‖z'‖ ≤ 1/4 → Integrable (fun w => φ (w - z') • fderiv ℝ u w) := by
          intro z' hz'
          have hcs : HasCompactSupport (fun w => φ (w - z')) :=
            hφcs.comp_homeomorph (Homeomorph.subRight z')
          refine Continuous.integrable_of_hasCompactSupport ?_ hcs.smul_right
          refine continuous_of_tsupport (fun w hw => ?_)
          have hw' := tsupport_smul_subset_left _ _ hw
          have hwz : ‖w - z'‖ ≤ 1/5 := by
            have hsub : tsupport (fun w => φ (w - z')) ⊆ {w | ‖w - z'‖ ≤ 1/5} := by
              refine closure_minimal (fun w hw => ?_) ?_
              · by_contra h
                exact hw (hφ0 _ (not_le.1 h).le)
              · exact isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const))
                  continuous_const
            exact hsub hw'
          have hwB : w ∈ ball (0 : Rn n) 1 := by
            rw [mem_ball, dist_zero_right]
            have := norm_add_le (w - z') z'
            simp only [sub_add_cancel] at this
            linarith
          exact ((hφc.comp (continuous_id.sub continuous_const)).continuousAt).smul
            (hD1cont.continuousAt (isOpen_ball.mem_nhds hwB))
        have hz' : ‖z‖ < 1/2 := by linarith
        have h1 := hdMVP u hu z hz'
        have h0 := hdMVP u hu 0 (by simp)
        rw [hshift z hz] at h1
        rw [hshift 0 (by simp)] at h0
        have hdiffeq : (∫ y, φ y) • (fderiv ℝ u z - fderiv ℝ u 0) =
            ∫ w, (φ (w - z) - φ (w - 0)) • fderiv ℝ u w := by
          rw [smul_sub, h1, h0, ← integral_sub (hint z hz) (hint 0 (by simp))]
          congr 1
          funext w
          rw [sub_smul]
        have hbound : ‖∫ w, (φ (w - z) - φ (w - 0)) • fderiv ℝ u w‖ ≤ Lφ * ‖z‖ * M := by
          refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal
            (by positivity) ?_)
          calc ∫⁻ w, ENNReal.ofReal ‖(φ (w - z) - φ (w - 0)) • fderiv ℝ u w‖
              ≤ ∫⁻ w, (ball (0 : Rn n) 1).indicator
                  (fun w => ENNReal.ofReal (Lφ * ‖z‖) * ‖fderiv ℝ u w‖ₑ) w := by
                refine lintegral_mono (fun w => ?_)
                by_cases hw : w ∈ ball (0 : Rn n) 1
                · rw [indicator_of_mem hw, ofReal_norm, enorm_smul]
                  gcongr
                  rw [← ofReal_norm]
                  refine ENNReal.ofReal_le_ofReal ?_
                  have := hφL.dist_le_mul (w - z) (w - 0)
                  rw [dist_eq_norm, dist_eq_norm] at this
                  simpa using this
                · have hw1 : 1 ≤ ‖w‖ := by
                    rw [mem_ball, dist_zero_right, not_lt] at hw
                    exact hw
                  have hA : φ (w - z) = 0 := by
                    apply hφ0
                    have := norm_sub_norm_le w z
                    linarith
                  have hB : φ w = 0 := hφ0 w (by linarith)
                  simp [hA, hB]
            _ = ENNReal.ofReal (Lφ * ‖z‖) * ∫⁻ w in ball (0 : Rn n) 1, ‖fderiv ℝ u w‖ₑ := by
                rw [lintegral_indicator measurableSet_ball,
                  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            _ ≤ ENNReal.ofReal (Lφ * ‖z‖) * ENNReal.ofReal M := by gcongr
            _ = ENNReal.ofReal (Lφ * ‖z‖ * M) := (ENNReal.ofReal_mul (by positivity)).symm
        rw [← hdiffeq, norm_smul, Real.norm_eq_abs] at hbound
        rw [show |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ = |∫ y, φ y|⁻¹ * (Lφ * ‖z‖ * M) by ring,
          le_inv_mul_iff₀ hc0pos]
        exact hbound
      refine ⟨?_, fun z hz => ?_⟩
      · have : ‖gradient u 0‖ = ‖fderiv ℝ u 0‖ := by simp [gradient]
        rw [this]
        exact hDu0
      · -- (c) second-order Taylor estimate via the mean value inequality
        have hinner : inner ℝ (gradient u 0) z = fderiv ℝ u 0 z := by
          simp [gradient, InnerProductSpace.toDual_symm_apply]
        rw [hinner]
        set K := |∫ y, φ y|⁻¹ * Lφ * M with hK
        have hK0 : 0 ≤ K := by positivity
        have hs : ∀ y ∈ closedBall (0 : Rn n) ‖z‖, y ∈ ball (0 : Rn n) 1 := by
          intro y hy
          rw [mem_closedBall, dist_zero_right] at hy
          rw [mem_ball, dist_zero_right]
          linarith
        have hmvt := (convex_closedBall (0 : Rn n) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
          (f := fun y => u y - fderiv ℝ u 0 y) (f' := fun y => fderiv ℝ u y - fderiv ℝ u 0)
          (C := K * ‖z‖)
          (fun y hy => (((hdiff y (hs y hy)).sub (fderiv ℝ u 0).hasFDerivAt)).hasFDerivWithinAt)
          (fun y hy => by
            rw [mem_closedBall, dist_zero_right] at hy
            calc ‖fderiv ℝ u y - fderiv ℝ u 0‖ ≤ K * ‖y‖ := hLipD y (by linarith)
              _ ≤ K * ‖z‖ := by gcongr)
          (mem_closedBall_self (norm_nonneg z)) (by rw [mem_closedBall, dist_zero_right])
        simp only [map_zero, sub_zero] at hmvt
        rw [Real.norm_eq_abs] at hmvt
        calc |u z - u 0 - fderiv ℝ u 0 z| = |u z - fderiv ℝ u 0 z - u 0| := by ring_nf
          _ ≤ K * ‖z‖ * ‖z‖ := hmvt
          _ = K * ‖z‖ ^ 2 := by ring
  /- Step 5 (Cauchy–Schwarz on `B₁`): `∫_{B₁} g ≤ (ω_n S)^{1/2}` when `∫_{B₁} g² ≤ S`. -/
  have CS : ∀ g : Rn n → ℝ≥0∞, AEMeasurable g (volume.restrict (ball (0 : Rn n) 1)) →
      ∀ S : ℝ, 0 ≤ S → ∫⁻ x in ball (0 : Rn n) 1, g x ^ 2 ≤ ENNReal.ofReal S →
      ∫⁻ x in ball (0 : Rn n) 1, g x ≤
        ENNReal.ofReal (Real.sqrt (volume (ball (0 : Rn n) 1)).toReal * Real.sqrt S) := by
    intro g hg S hS hgS
    have hV : volume (ball (0 : Rn n) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball (0 : Rn n) 1))
      Real.HolderConjugate.two_two hg aemeasurable_const (f := g) (g := fun _ => (1 : ℝ≥0∞))
    simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.rpow_two, one_pow, one_mul] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm (ENNReal.ofReal _)]
    gcongr
    · calc (∫⁻ x in ball (0 : Rn n) 1, g x ^ 2) ^ (1 / (2 : ℝ))
          ≤ (ENNReal.ofReal S) ^ (1 / (2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (Real.sqrt S) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]
    · rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_toReal hV]
  /- Step 6: the constants `C` (depending on `n, ℓ` only) and `δ_ε` (from Lemma 3.1). -/
  refine ⟨1 + Real.sqrt ℓ * C₁ * Real.sqrt (volume (ball (0 : Rn n) 1)).toReal +
      Real.sqrt ℓ * C₁ * (Real.sqrt (volume (ball (0 : Rn n) 1)).toReal +
        (volume (ball (0 : Rn n) 1)).toReal) +
      2 * ℓ * (1 + C₃ ^ 2 * (volume (ball (0 : Rn n) 1)).toReal ^ 2), by positivity, ?_⟩
  intro ε hε _hε1
  obtain ⟨δ, hδ, hHA⟩ := hHAL n hn ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r E h f L hr hE hh hLip hbound henergy halmost
  /- Step 7: for each component `j`, `F_j(z) = f(rz)_j / (r√E)` satisfies the hypotheses of
  Lemma 3.1 (`W^{1,2}` with weak gradient `∇F_j`, energy `≤ 1`, `δ`-almost harmonic), giving a
  harmonic `u_j` with `∫_{B₁}|∇u_j|² ≤ 1` and `∫_{B₁}|u_j - F_j|² ≤ ε`. -/
  have hcomp : ∀ j : Fin ℓ, ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - (r * Real.sqrt E)⁻¹ * f (r • x) j‖ₑ ^ 2 ≤
        ENNReal.ofReal ε := by
    intro j
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    set c : ℝ := (r * Real.sqrt E)⁻¹ with hc
    have hcpos : 0 < c := inv_pos.2 (mul_pos hr hsE)
    set fj : Rn n → ℝ := fun y => f y j with hfj
    set F : Rn n → ℝ := fun z => c * fj (r • z) with hF
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hcoord : ∀ v : Rn ℓ, |v j| ≤ ‖v‖ := fun v => by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hfjL : LipschitzOnWith L fj (closedBall 0 r) := by
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      have := hLip.dist_le_mul x hx y hy
      calc dist (fj x) (fj y) = |f x j - f y j| := Real.dist_eq _ _
        _ = |(f x - f y) j| := by simp
        _ ≤ ‖f x - f y‖ := hcoord _
        _ = dist (f x) (f y) := (dist_eq_norm _ _).symm
        _ ≤ L * dist x y := this
    have hsmulB : ∀ z : Rn n, z ∈ closedBall (0 : Rn n) 1 → r • z ∈ closedBall (0 : Rn n) r := by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    have hsmulB' : ∀ z : Rn n, z ∈ ball (0 : Rn n) 1 → r • z ∈ ball (0 : Rn n) r := by
      intro z hz
      rw [mem_ball, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    set KF : ℝ≥0 := ⟨c * L * r, by positivity⟩ with hKF
    have hFL : LipschitzOnWith KF F (closedBall 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      have h1 := hfjL.dist_le_mul _ (hsmulB x hx) _ (hsmulB y hy)
      rw [Real.dist_eq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr] at h1
      have h2 : dist (F x) (F y) = c * |fj (r • x) - fj (r • y)| := by
        rw [Real.dist_eq, show F x - F y = c * (fj (r • x) - fj (r • y)) by simp only [hF]; ring,
          abs_mul, abs_of_pos hcpos]
      rw [h2]
      calc c * |fj (r • x) - fj (r • y)| ≤ c * (L * (r * dist x y)) := by gcongr
        _ = KF * dist x y := by
          show c * (L * (r * dist x y)) = (c * L * r) * dist x y
          ring
    have hgradF : ∀ z, gradient F z = (Real.sqrt E)⁻¹ • gradient fj (r • z) := by
      intro z
      have h1 : fderiv ℝ F z = (c * r) • fderiv ℝ fj (r • z) := by
        have : F = c • (fun z => fj (r • z)) := by funext z; simp [hF, smul_eq_mul]
        rw [this, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul]
      have h2 : c * r = (Real.sqrt E)⁻¹ := by
        rw [hc]; field_simp
      simp only [gradient, h1, h2, map_smul]
    have hnormgrad : ∀ (g : Rn n → ℝ) (z : Rn n), ‖gradient g z‖ = ‖fderiv ℝ g z‖ := by
      intro g z; simp [gradient]
    have hgradFb : ∀ z ∈ ball (0 : Rn n) 1, ‖gradient F z‖ ≤ KF := by
      intro z hz
      rw [hnormgrad]
      exact norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hz) hFL
    have hFbound : ∀ z ∈ ball (0 : Rn n) 1, ‖F z‖ ≤ c * h := by
      intro z hz
      simp only [hF, hfj, norm_mul, Real.norm_eq_abs, abs_of_pos hcpos]
      gcongr
      exact (hcoord _).trans (hbound _ (hsmulB' z hz))
    have hFmeas : AEStronglyMeasurable F (volume.restrict (ball (0 : Rn n) 1)) :=
      (hFL.continuousOn.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
    have hgmeas : ∀ g : Rn n → ℝ, Measurable (gradient g) := fun g =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have hgradcoord : ∀ (g : Rn n → ℝ) (z : Rn n) (k : Fin n),
        (gradient g z).ofLp k = fderiv ℝ g z (EuclideanSpace.single k 1) := by
      intro g z k
      have := EuclideanSpace.inner_single_right k (1 : ℝ) (gradient g z)
      simp only [gradient, InnerProductSpace.toDual_symm_apply, one_mul] at this
      simpa [gradient] using this.symm
    have hcoordinner : ∀ (v : Rn n) (k : Fin n), (v).ofLp k = inner ℝ (EuclideanSpace.single k (1:ℝ)) v := by
      intro v k
      rw [EuclideanSpace.inner_single_left]
      simp
    -- `F` is in `W^{1,2}(B)` with weak gradient `gradient F`
    have hW12 : IsW12WithGradient F (gradient F) (ball 0 1) := by
      refine ⟨MemLp.of_bound hFmeas (c * h) ?_,
        MemLp.of_bound (hgmeas F).aestronglyMeasurable KF ?_, ?_⟩
      · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hFbound z hz
      · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hgradFb z hz
      · intro ζ hζ hζcs hζsupp
        obtain ⟨Ft, hFtL, hFtEq⟩ := hFL.extend_real
        obtain ⟨Lζ, hζL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hζcs hζ (by simp)
        have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
        have hζint : Integrable ζ := hζ.continuous.integrable_of_hasCompactSupport hζcs
        have hgζcont : Continuous (gradient ζ) :=
          (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv (by simp))
        have hgζcs : HasCompactSupport (gradient ζ) :=
          (hζcs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (Rn n)).symm) (by simp)
        have hgζint : Integrable (gradient ζ) := hgζcont.integrable_of_hasCompactSupport hgζcs
        have hI1 : Integrable (fun x => F x • gradient ζ x) (volume.restrict (ball (0 : Rn n) 1)) :=
          hgζint.integrableOn.bdd_smul (c * h) hFmeas
            (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz; exact hFbound z hz)
        have hI2 : Integrable (fun x => ζ x • gradient F x) (volume.restrict (ball (0 : Rn n) 1)) :=
          hζint.integrableOn.smul_bdd KF (hgmeas F).aestronglyMeasurable
            (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz; exact hgradFb z hz)
        have hζout : ∀ x ∉ ball (0 : Rn n) 1, ζ x = 0 := fun x hx =>
          image_eq_zero_of_notMem_tsupport (fun h => hx (hζsupp h))
        have hdζout : ∀ x ∉ ball (0 : Rn n) 1, fderiv ℝ ζ x = 0 := fun x hx =>
          fderiv_of_notMem_tsupport ℝ (fun h => hx (hζsupp h))
        refine PiLp.ext (fun k => ?_)
        set ek : Rn n := EuclideanSpace.single k (1:ℝ) with hek
        rw [hcoordinner, hcoordinner, inner_neg_right,
          ← innerSL_apply_apply (𝕜 := ℝ), ← innerSL_apply_apply (𝕜 := ℝ),
          ← (innerSL ℝ ek).integral_comp_comm hI1, ← (innerSL ℝ ek).integral_comp_comm hI2]
        have hgi : ∀ (g : Rn n → ℝ) (z : Rn n), inner ℝ ek (gradient g z) = fderiv ℝ g z ek := by
          intro g z
          rw [real_inner_comm]
          simp [gradient, InnerProductSpace.toDual_symm_apply]
        simp only [innerSL_apply_apply, inner_smul_right, hgi]
        -- integration by parts against the Lipschitz extension
        have hibp := hFtL.integral_lineDeriv_mul_eq (μ := volume) hζL hζcs ek
        have hA : ∫ x, lineDeriv ℝ ζ x (-ek) * Ft x =
            -∫ x in ball (0 : Rn n) 1, F x * fderiv ℝ ζ x ek := by
          have h1 : (fun x => lineDeriv ℝ ζ x (-ek) * Ft x) =
              fun x => -(fderiv ℝ ζ x ek * Ft x) := by
            funext x
            rw [(hζd x).lineDeriv_eq_fderiv, map_neg, neg_mul]
          rw [h1, integral_neg, ← setIntegral_eq_integral_of_forall_compl_eq_zero
            (s := ball (0 : Rn n) 1) (fun x hx => by simp [hdζout x hx])]
          congr 1
          refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
          rw [← hFtEq (ball_subset_closedBall hx), mul_comm]
        have hB : ∫ x, lineDeriv ℝ Ft x ek * ζ x =
            ∫ x in ball (0 : Rn n) 1, ζ x * fderiv ℝ F x ek := by
          rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
            (s := ball (0 : Rn n) 1) (fun x hx => by simp [hζout x hx])]
          refine setIntegral_congr_ae measurableSet_ball ?_
          filter_upwards [hFtL.ae_differentiableAt] with x hxd hx
          have heq : Ft =ᶠ[𝓝 x] F := Filter.eventuallyEq_of_mem (closedBall_mem_nhds_of_mem hx)
            (fun z hz => (hFtEq hz).symm)
          rw [hxd.lineDeriv_eq_fderiv, heq.fderiv_eq, mul_comm]
        rw [hA, hB] at hibp
        linarith
    -- energy bound for the weak gradient
    have hfjgrad : ∀ x ∈ ball (0 : Rn n) r, ‖gradient fj x‖ ≤ L := by
      intro x hx
      rw [hnormgrad]
      exact norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx) hfjL
    have hfgrad : ∀ x ∈ ball (0 : Rn n) r, ‖fderiv ℝ f x‖ ≤ L := fun x hx =>
      norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx) hLip
    have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)),
        ‖gradient fj x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
      have hae := hLip.ae_differentiableWithinAt_of_mem (μ := volume)
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hae] with x hx hxB
      have hdx : DifferentiableAt ℝ f x :=
        (hx (ball_subset_closedBall hxB)).differentiableAt (closedBall_mem_nhds_of_mem hxB)
      have hfd : ∀ v, fderiv ℝ fj x v = (fderiv ℝ f x v).ofLp j := by
        intro v
        have hh : HasFDerivAt fj ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
          (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hdx.hasFDerivAt
        rw [hh.fderiv]
        rfl
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      unfold hsNormSq
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hgradcoord, hfd]
      have := hcoord (fderiv ℝ f x (EuclideanSpace.single i 1))
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hhsmeas : Measurable (fun x => hsNormSq (fderiv ℝ f x)) := by
      have hc : Continuous (fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A) := by
        unfold hsNormSq
        exact continuous_finsetSum _ (fun i _ =>
          ((continuous_id.clm_apply continuous_const).norm.pow 2))
      exact hc.measurable.comp (measurable_fderiv ℝ f)
    have hintA : IntegrableOn (fun x => ‖gradient fj x‖ ^ 2) (ball (0 : Rn n) r) := by
      refine Integrable.of_bound ((hgmeas fj).norm.pow_const 2).aestronglyMeasurable (L ^ 2) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hfjgrad x hx) 2
    have hintB : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) r) := by
      refine Integrable.of_bound hhsmeas.aestronglyMeasurable (n * L ^ 2) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hnn : 0 ≤ hsNormSq (fderiv ℝ f x) := by unfold hsNormSq; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      unfold hsNormSq
      calc ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ i : Fin n, (L : ℝ) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
            calc ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖
                ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1:ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ L * 1 := by
                  gcongr
                  · exact hfgrad x hx
                  · simp
              _ = L := mul_one _
        _ = n * L ^ 2 := by simp
    have henergyF : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient F x‖ₑ ^ 2 ≤ 1 := by
      have hint1 : Integrable (fun x => ‖gradient F x‖ ^ 2) (volume.restrict (ball (0:Rn n) 1)) := by
        refine Integrable.of_bound ((hgmeas F).norm.pow_const 2).aestronglyMeasurable (KF ^ 2) ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgradFb x hx) 2
      have heq : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient F x‖ₑ ^ 2 =
          ENNReal.ofReal (∫ x in ball (0:Rn n) 1, ‖gradient F x‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint1
          (Filter.Eventually.of_forall (fun x => by positivity))]
        congr 1
        funext x
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      rw [heq, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ∀ x, ‖gradient F x‖ ^ 2 = E⁻¹ * ‖gradient fj (r • x)‖ ^ 2 := by
        intro x
        rw [hgradF, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hsE, inv_pow,
          Real.sq_sqrt hE.le]
      simp_rw [h1]
      rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume
        (fun x => ‖gradient fj x‖ ^ 2) _ hr, smul_unitBall_of_pos hr, finrank_euclideanSpace_fin,
        smul_eq_mul]
      have h3 := (setIntegral_mono_ae_restrict hintA hintB hpt).trans henergy
      have hrn : 0 < r ^ n := pow_pos hr n
      calc E⁻¹ * ((r ^ n)⁻¹ * ∫ x in ball (0 : Rn n) r, ‖gradient fj x‖ ^ 2)
          ≤ E⁻¹ * ((r ^ n)⁻¹ * (E * r ^ n)) := by gcongr
        _ = 1 := by field_simp
    -- almost harmonicity
    have halmostF : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball 0 1 → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (gradient F x) (gradient ζ x)| ≤ δ * M := by
      intro ζ hζ hζcs hζsupp M hM
      set ζ0 : Rn n → ℝ := fun x => ζ (r⁻¹ • x) with hζ0
      have hζ0s : ContDiff ℝ (⊤ : ℕ∞) ζ0 := hζ.comp (contDiff_const_smul _)
      have hζ0cs : HasCompactSupport ζ0 := hζcs.comp_smul (inv_ne_zero hr.ne')
      have hζ0supp : tsupport ζ0 ⊆ ball 0 r := by
        have : ζ0 = ζ ∘ (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')) := rfl
        rw [this, tsupport_comp_eq_preimage]
        intro x hx
        have hx' := hζsupp hx
        simp only [Homeomorph.smulOfNeZero_apply, mem_ball, dist_zero_right, norm_smul,
          Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hx'
        rw [mem_ball, dist_zero_right]
        rwa [inv_mul_lt_iff₀ hr, mul_one] at hx'
      have hgζ0 : ∀ x, gradient ζ0 x = r⁻¹ • gradient ζ (r⁻¹ • x) := by
        intro x
        simp only [gradient, hζ0]
        rw [fderiv_comp_smul, map_smul]
      have hM0 : ∀ x, ‖gradient ζ0 x‖ ≤ r⁻¹ * M := by
        intro x
        rw [hgζ0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        gcongr
        exact hM _
      have hA := halmost ζ0 hζ0s hζ0cs hζ0supp (r⁻¹ * M) hM0 j
      have h1 : ∀ z, inner ℝ (gradient F z) (gradient ζ z) =
          ((Real.sqrt E)⁻¹ * r) * inner ℝ (gradient fj (r • z)) (gradient ζ0 (r • z)) := by
        intro z
        rw [hgradF, hgζ0, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, real_inner_smul_left,
          real_inner_smul_right]
        field_simp
      have hrel : ∫ x in ball (0 : Rn n) 1, inner ℝ (gradient F x) (gradient ζ x) =
          (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            ∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient ζ0 x) := by
        simp_rw [h1]
        rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume
          (fun x => inner ℝ (gradient fj x) (gradient ζ0 x)) _ hr, smul_unitBall_of_pos hr,
          finrank_euclideanSpace_fin, smul_eq_mul]
        ring
      rw [hrel, abs_mul, abs_of_pos (by positivity)]
      calc (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            |∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient ζ0 x)|
          ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) * (δ * Real.sqrt E * (r⁻¹ * M) * r ^ n) := by
            gcongr
        _ = δ * M := by field_simp
    exact hHA F (gradient F) hW12 henergyF halmostF
  /- Step 8: `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0)·x)_j`, and the three estimates. -/
  set V : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hVdef
  set C : ℝ := 1 + Real.sqrt ℓ * C₁ * Real.sqrt V + Real.sqrt ℓ * C₁ * (Real.sqrt V + V) +
      2 * ℓ * (1 + C₃ ^ 2 * V ^ 2) with hCdef
  choose u hu_harm hu_en hu_cl using hcomp
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  set c : ℝ := (r * Real.sqrt E)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 (mul_pos hr hsE)
  have hrc : r * Real.sqrt E * c = 1 := by rw [hc]; field_simp
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVfin : volume (ball (0 : Rn n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hcoord : ∀ (v : Rn ℓ) (k : Fin ℓ), |v k| ≤ ‖v‖ := fun v k => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v k
  have hgmeas : ∀ g : Rn n → ℝ, Measurable (gradient g) := fun g =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  set F : Fin ℓ → Rn n → ℝ := fun k z => c * f (r • z) k with hF
  have hsmulB' : ∀ z : Rn n, z ∈ ball (0 : Rn n) 1 → r • z ∈ ball (0 : Rn n) r := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hFcont : ∀ k, ContinuousOn (F k) (ball 0 1) := by
    intro k
    have h1 : ContinuousOn f (ball 0 r) := hLip.continuousOn.mono ball_subset_closedBall
    have h2 : ContinuousOn (fun z : Rn n => f (r • z)) (ball 0 1) :=
      h1.comp (continuous_const_smul r).continuousOn (fun z hz => hsmulB' z hz)
    exact continuousOn_const.mul ((EuclideanSpace.proj k : Rn ℓ →L[ℝ] ℝ).continuous.comp_continuousOn h2)
  have hFbd : ∀ k, ∀ z ∈ ball (0 : Rn n) 1, |F k z| ≤ c * h := by
    intro k z hz
    simp only [hF, abs_mul, abs_of_pos hcpos]
    gcongr
    exact (hcoord _ _).trans (hbound _ (hsmulB' z hz))
  have hucont : ∀ k, ContinuousOn (u k) (ball 0 1) := fun k => (hu_harm k).continuousOn
  -- gradient bounds
  have hgradL1 : ∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖gradient (u k) x‖ₑ ≤
      ENNReal.ofReal (Real.sqrt V) := by
    intro k
    have := CS (fun x => ‖gradient (u k) x‖ₑ) (hgmeas (u k)).enorm.aemeasurable 1 zero_le_one
      (by simpa using hu_en k)
    simpa using this
  have hHE2 : ∀ k, ‖gradient (u k) 0‖ ≤ C₁ * Real.sqrt V ∧ ∀ z : Rn n, ‖z‖ ≤ 1/4 →
      |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ C₃ * Real.sqrt V * ‖z‖ ^ 2 :=
    fun k => HE2 (u k) (hu_harm k) (Real.sqrt V) (Real.sqrt_nonneg _) (hgradL1 k)
  -- value bounds
  have hdiffmeas : ∀ k, AEStronglyMeasurable (fun x => u k x - F k x)
      (volume.restrict (ball (0 : Rn n) 1)) := fun k =>
    ((hucont k).sub (hFcont k)).aestronglyMeasurable measurableSet_ball
  have hvalL1 : ∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖u k x‖ₑ ≤
      ENNReal.ofReal (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
    intro k
    have h1 : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - F k x‖ₑ ≤
        ENNReal.ofReal (Real.sqrt V * Real.sqrt ε) :=
      CS _ (hdiffmeas k).enorm ε hε.le (hu_cl k)
    have h2 : ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ≤ ENNReal.ofReal (V * (c * h)) := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ≤ ∫⁻ x in ball (0 : Rn n) 1, ENNReal.ofReal (c * h) := by
            refine setLIntegral_mono measurable_const (fun z hz => ?_)
            rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hFbd k z hz)
        _ = ENNReal.ofReal (c * h) * volume (ball (0 : Rn n) 1) := setLIntegral_const _ _
        _ = ENNReal.ofReal (V * (c * h)) := by
            rw [← ENNReal.ofReal_toReal hVfin, ← ENNReal.ofReal_mul (by positivity), mul_comm]
    calc ∫⁻ x in ball (0 : Rn n) 1, ‖u k x‖ₑ
        ≤ ∫⁻ x in ball (0 : Rn n) 1, (‖u k x - F k x‖ₑ + ‖F k x‖ₑ) := by
          refine lintegral_mono (fun x => ?_)
          calc ‖u k x‖ₑ = ‖(u k x - F k x) + F k x‖ₑ := by rw [sub_add_cancel]
            _ ≤ ‖u k x - F k x‖ₑ + ‖F k x‖ₑ := enorm_add_le _ _
      _ = (∫⁻ x in ball (0 : Rn n) 1, ‖u k x - F k x‖ₑ) + ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ :=
          lintegral_add_left' (hdiffmeas k).enorm _
      _ ≤ ENNReal.ofReal (Real.sqrt V * Real.sqrt ε) + ENNReal.ofReal (V * (c * h)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (Real.sqrt V * Real.sqrt ε + V * (c * h)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hHE1 : ∀ k, |u k 0| ≤ C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h)) := fun k =>
    HE1 (u k) (hu_harm k) _ (by positivity) (hvalL1 k)
  -- the affine map
  set a : Rn ℓ := WithLp.toLp 2 (fun k => r * Real.sqrt E * u k 0) with ha
  set A : Rn n →L[ℝ] Rn ℓ := ∑ k : Fin ℓ,
    (Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight (EuclideanSpace.single k (1:ℝ)) with hA
  have hAapply : ∀ (x : Rn n) (k : Fin ℓ), (A x).ofLp k = Real.sqrt E * inner ℝ (gradient (u k) 0) x := by
    intro x k
    simp [hA, Pi.single_apply]
  have haapply : ∀ k, a.ofLp k = r * Real.sqrt E * u k 0 := fun k => rfl
  have hsqrtℓ : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have hCge1 : Real.sqrt ℓ * C₁ * Real.sqrt V ≤ C := by
    have : 0 ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) := by positivity
    have : 0 ≤ 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) := by positivity
    rw [hCdef]; linarith
  have hCge2 : Real.sqrt ℓ * C₁ * (Real.sqrt V + V) ≤ C := by
    have : 0 ≤ Real.sqrt ℓ * C₁ * Real.sqrt V := by positivity
    have : 0 ≤ 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) := by positivity
    rw [hCdef]; linarith
  have hCge3 : 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) ≤ C := by
    have : 0 ≤ Real.sqrt ℓ * C₁ * Real.sqrt V := by positivity
    have : 0 ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) := by positivity
    rw [hCdef]; linarith
  refine ⟨a, A, ?_, ?_, ?_⟩
  · -- the Hilbert–Schmidt norm of `A`
    have hsq : hsNormSq A = E * ∑ k : Fin ℓ, ‖gradient (u k) 0‖ ^ 2 := by
      unfold hsNormSq
      have h1 : ∀ i : Fin n, ‖A (EuclideanSpace.single i 1)‖ ^ 2 =
          ∑ k : Fin ℓ, E * ((gradient (u k) 0).ofLp i) ^ 2 := by
        intro i
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hAapply, EuclideanSpace.inner_single_right, Real.norm_eq_abs, sq_abs]
        simp only [one_mul, starRingEnd_apply, star_trivial]
        rw [mul_pow, Real.sq_sqrt hE.le]
      simp_rw [h1]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.mul_sum, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    have hle : hsNormSq A ≤ (Real.sqrt ℓ * C₁ * Real.sqrt V * Real.sqrt E) ^ 2 := by
      rw [hsq]
      calc E * ∑ k : Fin ℓ, ‖gradient (u k) 0‖ ^ 2 ≤ E * ∑ k : Fin ℓ, (C₁ * Real.sqrt V) ^ 2 := by
            gcongr with k
            exact (hHE2 k).1
        _ = (Real.sqrt ℓ * C₁ * Real.sqrt V * Real.sqrt E) ^ 2 := by
            have e1 : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt (Nat.cast_nonneg _)
            have e2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE.le
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            simp only [mul_pow, e1, e2]
            ring
    calc hsNorm A = Real.sqrt (hsNormSq A) := rfl
      _ ≤ Real.sqrt ((Real.sqrt ℓ * C₁ * Real.sqrt V * Real.sqrt E) ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt ℓ * C₁ * Real.sqrt V * Real.sqrt E := Real.sqrt_sq (by positivity)
      _ ≤ C * Real.sqrt E := by gcongr
  · -- the constant term
    set B : ℝ := C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) with hB
    have hak : ∀ k, |a.ofLp k| ≤ B := by
      intro k
      rw [haapply, abs_mul, abs_of_pos (mul_pos hr hsE)]
      calc r * Real.sqrt E * |u k 0| ≤ r * Real.sqrt E *
            (C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h))) := by
            gcongr
            exact hHE1 k
        _ = B := by
            rw [hB, Real.sqrt_mul hε.le]
            have : r * Real.sqrt E * (V * (c * h)) = V * h := by
              rw [show r * Real.sqrt E * (V * (c * h)) = V * h * (r * Real.sqrt E * c) by ring, hrc,
                mul_one]
            linear_combination C₁ * this
    have hB0 : 0 ≤ B := by positivity
    calc ‖a‖ = Real.sqrt (∑ k : Fin ℓ, ‖a.ofLp k‖ ^ 2) := EuclideanSpace.norm_eq a
      _ ≤ Real.sqrt (∑ k : Fin ℓ, B ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k _ => ?_))
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2
      _ = Real.sqrt ℓ * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul
            (Nat.cast_nonneg _), Real.sqrt_sq hB0]
      _ ≤ Real.sqrt ℓ * (C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E))) := by
          gcongr
          rw [hB]
          have h1 : 0 ≤ r * Real.sqrt (ε * E) := by positivity
          have h2 : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
          have h3 : Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h ≤
              (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by nlinarith
          calc C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)
              ≤ C₁ * ((Real.sqrt V + V) * (h + r * Real.sqrt (ε * E))) := by gcongr
            _ = C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by ring
      _ = Real.sqrt ℓ * C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by ring
      _ ≤ C * (h + r * Real.sqrt (ε * E)) := by
          gcongr
  · -- the `L²` estimate
    intro e he he4
    have he1 : e ≤ 1 := by linarith
    have hcv : ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 =
        r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 := by
      have := Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖f x - (a + A x)‖ ^ 2)
        (ball (0 : Rn n) e) hr
      rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_comm r e,
        finrank_euclideanSpace_fin, smul_eq_mul] at this
      rw [this, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
    rw [hcv]
    -- integrability of `(F_k - u_k)²` and its integral
    have hsqint : ∀ k, IntegrableOn (fun z => (F k z - u k z) ^ 2) (ball (0 : Rn n) 1) := by
      intro k
      refine ⟨(((hFcont k).sub (hucont k)).pow 2).aestronglyMeasurable measurableSet_ball, ?_⟩
      have hfi : ∫⁻ z in ball (0 : Rn n) 1, ‖(F k z - u k z) ^ 2‖ₑ =
          ∫⁻ z in ball (0 : Rn n) 1, ‖u k z - F k z‖ₑ ^ 2 := by
        congr 1
        funext z
        rw [enorm_pow, ← enorm_neg, neg_sub]
      rw [HasFiniteIntegral, hfi]
      exact (hu_cl k).trans_lt ENNReal.ofReal_lt_top
    have hsqle : ∀ k, ∫ z in ball (0 : Rn n) e, (F k z - u k z) ^ 2 ≤ ε := by
      intro k
      calc ∫ z in ball (0 : Rn n) e, (F k z - u k z) ^ 2
          ≤ ∫ z in ball (0 : Rn n) 1, (F k z - u k z) ^ 2 :=
            setIntegral_mono_set (hsqint k)
              (Filter.Eventually.of_forall (fun z => sq_nonneg _))
              (Filter.Eventually.of_forall (ball_subset_ball he1))
        _ ≤ ε := by
            rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
              (fun z => sq_nonneg _)) (hsqint k).aestronglyMeasurable]
            refine ENNReal.toReal_le_of_le_ofReal hε.le ((le_of_eq ?_).trans (hu_cl k))
            congr 1
            funext z
            have : (F k z - u k z) ^ 2 = |u k z - F k z| ^ 2 := by rw [sq_abs]; ring
            rw [this, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
    set D : ℝ := C₃ * Real.sqrt V * e ^ 2 with hD
    have hD0 : 0 ≤ D := by positivity
    set G : Rn n → ℝ := fun z => 2 * (r ^ 2 * E) * ∑ k : Fin ℓ, ((F k z - u k z) ^ 2 + D ^ 2)
      with hG
    have hpt : ∀ z ∈ ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 ≤ G z := by
      intro z hz
      have hz' : ‖z‖ < e := by rwa [mem_ball, dist_zero_right] at hz
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      show _ ≤ 2 * (r ^ 2 * E) * ∑ k : Fin ℓ, ((F k z - u k z) ^ 2 + D ^ 2)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hfk : (f (r • z)).ofLp k = r * Real.sqrt E * F k z := by
        simp only [hF]
        rw [← mul_assoc, hrc, one_mul]
      have hcomp : (f (r • z) - (a + A (r • z))).ofLp k = r * Real.sqrt E *
          ((F k z - u k z) + (u k z - u k 0 - inner ℝ (gradient (u k) 0) z)) := by
        simp only [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply]
        rw [hfk, haapply, hAapply, real_inner_smul_right]
        ring
      have hTaylor : |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ D := by
        calc |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ C₃ * Real.sqrt V * ‖z‖ ^ 2 :=
              (hHE2 k).2 z (by linarith)
          _ ≤ C₃ * Real.sqrt V * e ^ 2 := by gcongr
      have hY : (u k z - u k 0 - inner ℝ (gradient (u k) 0) z) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hTaylor 2
      rw [Real.norm_eq_abs, sq_abs, hcomp, mul_pow, mul_pow, Real.sq_sqrt hE.le]
      set X := F k z - u k z
      set Y := u k z - u k 0 - inner ℝ (gradient (u k) 0) z
      have hXY : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + D ^ 2) := by nlinarith [sq_nonneg (X - Y)]
      calc r ^ 2 * E * (X + Y) ^ 2 ≤ r ^ 2 * E * (2 * (X ^ 2 + D ^ 2)) := by gcongr
        _ = 2 * (r ^ 2 * E) * (X ^ 2 + D ^ 2) := by ring
    have hconst : ∫ _ in ball (0 : Rn n) e, D ^ 2 = e ^ n * V * D ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Measure.addHaar_ball_of_pos volume _ he,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hintk : ∀ k ∈ (Finset.univ : Finset (Fin ℓ)),
        IntegrableOn (fun z => (F k z - u k z) ^ 2 + D ^ 2) (ball (0 : Rn n) e) := fun k _ =>
      ((hsqint k).mono_set (ball_subset_ball he1)).add (integrableOn_const measure_ball_lt_top.ne)
    have hGint : IntegrableOn G (ball (0 : Rn n) e) :=
      (integrable_finsetSum _ hintk).const_mul _
    have hGval : ∫ z in ball (0 : Rn n) e, G z ≤
        2 * (r ^ 2 * E) * (ℓ * (ε + e ^ n * V * D ^ 2)) := by
      rw [hG, integral_const_mul, integral_finsetSum _ hintk]
      gcongr
      calc ∑ k : Fin ℓ, ∫ z in ball (0 : Rn n) e, ((F k z - u k z) ^ 2 + D ^ 2)
          = ∑ k : Fin ℓ, ((∫ z in ball (0 : Rn n) e, (F k z - u k z) ^ 2) + e ^ n * V * D ^ 2) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [integral_add ((hsqint k).mono_set (ball_subset_ball he1))
              (integrableOn_const measure_ball_lt_top.ne), hconst]
        _ ≤ ∑ k : Fin ℓ, (ε + e ^ n * V * D ^ 2) :=
            Finset.sum_le_sum (fun k _ => by linarith [hsqle k])
        _ = ℓ * (ε + e ^ n * V * D ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hP : ε + e ^ n * V * D ^ 2 ≤ (1 + C₃ ^ 2 * V ^ 2) * (ε + e ^ (n + 4)) := by
      have h1 : e ^ n * V * D ^ 2 = C₃ ^ 2 * V ^ 2 * (e ^ n * e ^ 4) := by
        rw [hD, mul_pow, mul_pow, Real.sq_sqrt hV0]; ring
      rw [h1, pow_add]
      have : 0 ≤ C₃ ^ 2 * V ^ 2 * ε := by positivity
      have : 0 ≤ e ^ n * e ^ 4 := by positivity
      nlinarith
    have hstep : 2 * (ℓ : ℝ) * (ε + e ^ n * V * D ^ 2) ≤ C * (ε + e ^ (n + 4)) :=
      calc 2 * (ℓ : ℝ) * (ε + e ^ n * V * D ^ 2)
          ≤ 2 * ℓ * ((1 + C₃ ^ 2 * V ^ 2) * (ε + e ^ (n + 4))) := by gcongr
        _ = (2 * ℓ * (1 + C₃ ^ 2 * V ^ 2)) * (ε + e ^ (n + 4)) := by ring
        _ ≤ C * (ε + e ^ (n + 4)) := by gcongr
    calc r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2
        ≤ r ^ n * ∫ z in ball (0 : Rn n) e, G z := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr.le n)
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => by positivity))
            hGint ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact hpt z hz
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * (ℓ * (ε + e ^ n * V * D ^ 2))) := by gcongr
      _ = (r ^ n * r ^ 2 * E) * (2 * ℓ * (ε + e ^ n * V * D ^ 2)) := by ring
      _ ≤ (r ^ n * r ^ 2 * E) * (C * (ε + e ^ (n + 4))) := by gcongr
      _ = C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by rw [pow_add]; ring

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
