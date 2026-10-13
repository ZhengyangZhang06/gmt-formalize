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

/-- Symmetry of the second derivative of a `C²` map `V : ℝⁿ → ℝ^ℓ` (Schwarz–Clairaut):
`D²V(x)(v)(w) = D²V(x)(w)(v)`.  Mathlib's `ContDiffAt.isSymmSndFDerivAt` is not imported here, so
we argue with the second difference `Δ(t) = V(x + ta + tb) − V(x + ta) − V(x + tb) + V(x)`:
continuity of `z ↦ D²V(z)(b)` and two mean value inequalities (along `[y, y + tb]`, then along
`[x, x + ta]`) give `‖Δ(t) − t² D²V(x)(b)(a)‖ ≤ δ t² ‖a‖` for small `t > 0`.  As `Δ` is symmetric
in `(a, b)`, `‖D²V(x)(w)(v) − D²V(x)(v)(w)‖ ≤ δ (‖v‖ + ‖w‖)` for every `δ > 0`. -/
theorem dohr_eb_sch_liou_snd_deriv_symm : ∀ (n ℓ : ℕ) (V : Rn n → Rn ℓ), ContDiff ℝ 2 V → ∀ x v w : Rn n, fderiv ℝ (fderiv ℝ V) x v w = fderiv ℝ (fderiv ℝ V) x w v := by
  intro n ℓ V hV x v w
  have hDV : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hDVd : Differentiable ℝ (fderiv ℝ V) := hDV.differentiable one_ne_zero
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  -- z ↦ D²V(z) b is continuous (values in L)
  have hHcont : ∀ b : Rn n, Continuous (fun z => fderiv ℝ (fderiv ℝ V) z b) := fun b =>
    (hDV.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  -- inner estimate along the segment [y, y + t b], applied to a vector a
  have inner : ∀ a b : Rn n, ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ y : Rn n, ∀ t : ℝ, 0 ≤ t →
      ‖y - x‖ + t * ‖b‖ < r →
      ‖fderiv ℝ V (y + t • b) a - fderiv ℝ V y a - t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤
        δ * ‖a‖ * t := by
    intro a b δ hδ
    have hc : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ V) z b - fderiv ℝ (fderiv ℝ V) x b‖) :=
      ((hHcont b).sub continuous_const).norm
    have h0 : ‖fderiv ℝ (fderiv ℝ V) x b - fderiv ℝ (fderiv ℝ V) x b‖ < δ := by
      rw [sub_self, norm_zero]; exact hδ
    have h1 : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ (fderiv ℝ V) z b - fderiv ℝ (fderiv ℝ V) x b‖ < δ :=
      hc.continuousAt.eventually_lt continuousAt_const h0
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨r, hr, fun y t ht hyt => ?_⟩
    have hg : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt
        (fun s : ℝ => fderiv ℝ V (y + s • b) a - s • fderiv ℝ (fderiv ℝ V) x b a)
        (fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a) (Icc 0 t) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => y + s • b) b s := by
        simpa using ((hasDerivAt_id s).smul_const b).const_add y
      have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ V (y + s • b))
          (fderiv ℝ (fderiv ℝ V) (y + s • b) b) s :=
        (hDVd (y + s • b)).hasFDerivAt.comp_hasDerivAt s h1
      have h2a : HasDerivAt (fun s : ℝ => fderiv ℝ V (y + s • b) a)
          (fderiv ℝ (fderiv ℝ V) (y + s • b) b a) s := by
        have := h2.clm_apply (hasDerivAt_const s a)
        simpa using this
      have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ (fderiv ℝ V) x b a)
          (fderiv ℝ (fderiv ℝ V) x b a) s := by
        simpa using (hasDerivAt_id s).smul_const (fderiv ℝ (fderiv ℝ V) x b a)
      exact (h2a.sub h3).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) t,
        ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * ‖a‖ := by
      intro s hs
      have hlt : ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b‖ < δ := by
        apply hball
        rw [dist_eq_norm]
        calc ‖y + s • b - x‖ = ‖(y - x) + s • b‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖s • b‖ := norm_add_le _ _
          _ = ‖y - x‖ + s * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
          _ ≤ ‖y - x‖ + t * ‖b‖ := by gcongr; exact hs.2.le
          _ < r := hyt
      calc ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a‖
          = ‖(fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b) a‖ := by simp
        _ ≤ ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b‖ * ‖a‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ δ * ‖a‖ := by gcongr
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hg hbound t ⟨ht, le_rfl⟩
    simp only [zero_smul, add_zero, sub_zero] at h
    calc ‖fderiv ℝ V (y + t • b) a - fderiv ℝ V y a - t • fderiv ℝ (fderiv ℝ V) x b a‖
        = ‖fderiv ℝ V (y + t • b) a - t • fderiv ℝ (fderiv ℝ V) x b a - fderiv ℝ V y a‖ := by
          congr 1; abel
      _ ≤ δ * ‖a‖ * t := h
  -- outer estimate: the second difference is ≈ t² D²V(x)(b)(a)
  have outer : ∀ a b : Rn n, ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ t : ℝ, 0 < t →
      t * (‖a‖ + ‖b‖) < r →
      ‖(V (x + t • a + t • b) - V (x + t • a) - V (x + t • b) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * t * (t * ‖a‖) := by
    intro a b δ hδ
    obtain ⟨r, hr, hin⟩ := inner a b δ hδ
    refine ⟨r, hr, fun t ht htr => ?_⟩
    have hk : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt
        (fun s : ℝ => V (x + s • a + t • b) - V (x + s • a) -
          s • (t • fderiv ℝ (fderiv ℝ V) x b a))
        (fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
          t • fderiv ℝ (fderiv ℝ V) x b a) (Icc 0 t) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => x + s • a + t • b) a s := by
        simpa using (((hasDerivAt_id s).smul_const a).const_add x).add_const (t • b)
      have h1' : HasDerivAt (fun s : ℝ => x + s • a) a s := by
        simpa using ((hasDerivAt_id s).smul_const a).const_add x
      have h2 := (hVd (x + s • a + t • b)).hasFDerivAt.comp_hasDerivAt s h1
      have h3 := (hVd (x + s • a)).hasFDerivAt.comp_hasDerivAt s h1'
      have h4 : HasDerivAt (fun s : ℝ => s • (t • fderiv ℝ (fderiv ℝ V) x b a))
          (t • fderiv ℝ (fderiv ℝ V) x b a) s := by
        simpa using (hasDerivAt_id s).smul_const (t • fderiv ℝ (fderiv ℝ V) x b a)
      exact ((h2.sub h3).sub h4).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) t,
        ‖fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
          t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * t * ‖a‖ := by
      intro s hs
      have hy : ‖(x + s • a) - x‖ + t * ‖b‖ < r := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        have : s * ‖a‖ ≤ t * ‖a‖ := by gcongr; exact hs.2.le
        nlinarith
      have h := hin (x + s • a) t ht.le hy
      calc ‖fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
            t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * ‖a‖ * t := h
        _ = δ * t * ‖a‖ := by ring
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hk hbound t ⟨ht.le, le_rfl⟩
    simp only [zero_smul, add_zero, sub_zero] at h
    calc ‖(V (x + t • a + t • b) - V (x + t • a) - V (x + t • b) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x b a‖
        = ‖V (x + t • a + t • b) - V (x + t • a) - t • t • fderiv ℝ (fderiv ℝ V) x b a -
            (V (x + t • b) - V x)‖ := by
          rw [mul_smul]; congr 1; abel
      _ ≤ δ * t * ‖a‖ * t := h
      _ = δ * t * (t * ‖a‖) := by ring
  -- conclusion: compare the estimates for (v, w) and (w, v), then let δ → 0
  have key : ∀ δ : ℝ, 0 < δ →
      ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤ δ * (‖v‖ + ‖w‖) := by
    intro δ hδ
    obtain ⟨r1, hr1, h1⟩ := outer v w δ hδ
    obtain ⟨r2, hr2, h2⟩ := outer w v δ hδ
    set r := min r1 r2
    have hr : 0 < r := lt_min hr1 hr2
    have hden : 0 < 2 * (‖v‖ + ‖w‖ + 1) := by positivity
    set t : ℝ := r / (2 * (‖v‖ + ‖w‖ + 1)) with ht_def
    have ht : 0 < t := div_pos hr hden
    have htr : t * (‖v‖ + ‖w‖) < r := by
      rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have e1 := h1 t ht (lt_of_lt_of_le htr (min_le_left _ _))
    have e2 := h2 t ht (by
      have : t * (‖w‖ + ‖v‖) = t * (‖v‖ + ‖w‖) := by ring
      rw [this]; exact lt_of_lt_of_le htr (min_le_right _ _))
    have hcomm : x + t • w + t • v = x + t • v + t • w := by abel
    rw [hcomm] at e2
    have hdiff : (t * t) • (fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w) =
        ((V (x + t • v + t • w) - V (x + t • w) - V (x + t • v) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x v w) -
        ((V (x + t • v + t • w) - V (x + t • v) - V (x + t • w) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x w v) := by
      rw [smul_sub]; abel
    have htt : 0 < t * t := mul_pos ht ht
    have hbound : (t * t) * ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤
        (t * t) * (δ * (‖v‖ + ‖w‖)) := by
      have hn : (t * t) * ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ =
          ‖(t * t) • (fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htt]
      rw [hn, hdiff]
      calc _ ≤ ‖(V (x + t • v + t • w) - V (x + t • w) - V (x + t • v) + V x) -
              (t * t) • fderiv ℝ (fderiv ℝ V) x v w‖ +
            ‖(V (x + t • v + t • w) - V (x + t • v) - V (x + t • w) + V x) -
              (t * t) • fderiv ℝ (fderiv ℝ V) x w v‖ := norm_sub_le _ _
        _ ≤ δ * t * (t * ‖w‖) + δ * t * (t * ‖v‖) := add_le_add e2 e1
        _ = (t * t) * (δ * (‖v‖ + ‖w‖)) := by ring
    exact le_of_mul_le_mul_left hbound htt
  have hle : ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤ 0 := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hpos : 0 < ‖v‖ + ‖w‖ + 1 := by positivity
    have := key (ε / (‖v‖ + ‖w‖ + 1)) (div_pos hε hpos)
    calc _ ≤ ε / (‖v‖ + ‖w‖ + 1) * (‖v‖ + ‖w‖) := this
      _ < 0 + ε := by
        rw [zero_add, div_mul_eq_mul_div, div_lt_iff₀ hpos]
        nlinarith
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle)).symm

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

/-- Iterated Caccioppoli along the chain `U_j = (d_u)^j (d_w W)` inside a class `S` closed under
directional derivatives: the energy of `D U_n` on `B_ρ(0)` is `O(ρ^{2α-2-n})`, hence zero. -/
theorem dohr_eb_sch_liou_chain_vanish : ∀ (n ℓ : ℕ) (α K C : ℝ) (S : Set (Rn n → Rn ℓ)) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 ≤ K → 0 ≤ C → (∀ V ∈ S, ContDiff ℝ 1 V) → (∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S) → (∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ, ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2) → W ∈ S → (∀ x : Rn n, ‖fderiv ℝ W x - fderiv ℝ W 0‖ ≤ K * ‖x‖ ^ α) → ∀ u w y : Rn n, fderiv ℝ ((fun g : Rn n → Rn ℓ => fun z => fderiv ℝ g z u)^[n] (fun z => fderiv ℝ W z w)) y = 0 := by
  intro n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS hgrowth u w y
  set D : (Rn n → Rn ℓ) → (Rn n → Rn ℓ) := fun g z => fderiv ℝ g z u with hD
  set U : ℕ → Rn n → Rn ℓ := fun j => D^[j] (fun z => fderiv ℝ W z w) with hU
  have hUS : ∀ j, U j ∈ S := by
    intro j
    induction j with
    | zero => exact hS2 W hWS w
    | succ j ih =>
      simp only [hU] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact hS2 _ ih u
  have hUsucc : ∀ j, U (j + 1) = fun z => fderiv ℝ (U j) z u := by
    intro j
    simp only [hU]
    rw [Function.iterate_succ_apply']
  set E : ℕ → ℝ → ℝ≥0∞ := fun j ρ => ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ (U j) x‖ₑ ^ 2 with hE
  set ω : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hω
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hvol : ∀ r : ℝ, 0 < r → volume (ball (0 : Rn n) r) = ENNReal.ofReal (r ^ n * ω) := by
    intro r hr
    rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity), hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  set e0 : ℝ := (n : ℝ) + 2 * α - 2 with he0
  set M0 : ℝ := C * K ^ 2 * ‖w‖ ^ 2 * (2 : ℝ) ^ ((n : ℝ) + 2 * α) * ω with hM0
  have hM0nn : 0 ≤ M0 := by positivity
  -- base estimate (Caccioppoli with c = DW(0) w)
  have hbase : ∀ ρ : ℝ, 0 < ρ → E 0 ρ ≤ ENNReal.ofReal (M0 * ρ ^ e0) := by
    intro ρ hρ
    have h1 := hS3 (U 0) (hUS 0) ρ hρ (fderiv ℝ W 0 w)
    refine h1.trans ?_
    have hc : 0 ≤ K * (2 * ρ) ^ α * ‖w‖ := by positivity
    have h2 : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2 ≤
        ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      have hx' : ‖x‖ < 2 * ρ := by simpa using hx
      have hle : ‖U 0 x - fderiv ℝ W 0 w‖ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
        simp only [hU, Function.iterate_zero, id]
        calc ‖fderiv ℝ W x w - fderiv ℝ W 0 w‖ = ‖(fderiv ℝ W x - fderiv ℝ W 0) w‖ := by simp
          _ ≤ ‖fderiv ℝ W x - fderiv ℝ W 0‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ K * ‖x‖ ^ α * ‖w‖ := by gcongr; exact hgrowth x
          _ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
            gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
    calc ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2
        ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) *
            ENNReal.ofReal ((2 * ρ) ^ n * ω)) := by
          rw [setLIntegral_const, hvol (2 * ρ) (by positivity)]
      _ = ENNReal.ofReal (C / ρ ^ 2 * ((K * (2 * ρ) ^ α * ‖w‖) ^ 2 * ((2 * ρ) ^ n * ω))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (M0 * ρ ^ e0) := by
          congr 1
          have h2ρ : (2 * ρ) ^ α = 2 ^ α * ρ ^ α := Real.mul_rpow (by norm_num) hρ.le
          have hpow : ρ ^ e0 = ρ ^ n * (ρ ^ α) ^ 2 / ρ ^ 2 := by
            rw [he0, Real.rpow_sub hρ, Real.rpow_add hρ, Real.rpow_natCast, Real.rpow_two,
              ← Real.rpow_natCast (ρ ^ α) 2, ← Real.rpow_mul hρ.le]
            push_cast; ring_nf
          have h2pow : (2 : ℝ) ^ ((n : ℝ) + 2 * α) = 2 ^ n * (2 ^ α) ^ 2 := by
            rw [Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.rpow_natCast ((2:ℝ) ^ α) 2,
              ← Real.rpow_mul (by norm_num)]
            push_cast; ring_nf
          rw [hpow, hM0, h2pow, h2ρ, mul_pow]
          field_simp
          ring
  -- iteration (Caccioppoli with c = 0)
  have hiter : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 0 < ρ →
      E j ρ ≤ ENNReal.ofReal (M * ρ ^ (e0 - 2 * (j : ℝ))) := by
    intro j
    induction j with
    | zero => exact ⟨M0, hM0nn, fun ρ hρ => by simpa using hbase ρ hρ⟩
    | succ j ih =>
      obtain ⟨M, hM, hb⟩ := ih
      refine ⟨C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)), by positivity, fun ρ hρ => ?_⟩
      have hstep : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 ≤
          ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ) := by
        simp only [hE]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_mono
        intro x
        simp only [hUsucc j, sub_zero]
        calc ‖fderiv ℝ (U j) x u‖ₑ ^ 2 ≤ (‖fderiv ℝ (U j) x‖ₑ * ‖u‖ₑ) ^ 2 := by
              gcongr; exact ContinuousLinearMap.le_opENorm _ _
          _ = ENNReal.ofReal (‖u‖ ^ 2) * ‖fderiv ℝ (U j) x‖ₑ ^ 2 := by
              rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; ring
      calc E (j + 1) ρ ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 :=
            hS3 _ (hUS (j + 1)) ρ hρ 0
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ)) := by
            gcongr
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) *
              ENNReal.ofReal (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ)))) := by
            gcongr; exact hb (2 * ρ) (by positivity)
        _ = ENNReal.ofReal (C / ρ ^ 2 * (‖u‖ ^ 2 * (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ))))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)) *
              ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ))) := by
            congr 1
            have h2ρ : (2 * ρ) ^ (e0 - 2 * (j : ℝ)) =
                2 ^ (e0 - 2 * (j : ℝ)) * ρ ^ (e0 - 2 * (j : ℝ)) :=
              Real.mul_rpow (by norm_num) hρ.le
            have hpow : ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ)) = ρ ^ (e0 - 2 * (j : ℝ)) / ρ ^ 2 := by
              rw [← Real.rpow_two, ← Real.rpow_sub hρ]; push_cast; ring_nf
            rw [h2ρ, hpow]
            field_simp
  -- decay: the energy of D U_n vanishes on every ball
  obtain ⟨M, hM, hb⟩ := hiter n
  have hneg : e0 - 2 * (n : ℝ) < 0 := by rw [he0]; linarith
  have hEn : ∀ ρ0 : ℝ, 0 < ρ0 → E n ρ0 = 0 := by
    intro ρ0 hρ0
    have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (M * ρ ^ (e0 - 2 * (n : ℝ)))) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun ρ : ℝ => ρ ^ (e0 - 2 * (n : ℝ))) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := -(e0 - 2 * (n : ℝ))) (by linarith)
        simpa using this
      have h2 := h1.const_mul M
      rw [mul_zero] at h2
      have := ENNReal.tendsto_ofReal h2
      simpa using this
    have hle : E n ρ0 ≤ 0 := by
      refine ge_of_tendsto hlim (eventually_atTop.2 ⟨ρ0, fun ρ hρ => ?_⟩)
      exact (lintegral_mono_set (ball_subset_ball hρ)).trans (hb ρ (lt_of_lt_of_le hρ0 hρ))
    exact le_antisymm hle zero_le
  -- pointwise vanishing (continuity + open sets have positive measure)
  have hcont : Continuous (fderiv ℝ (U n)) := (hS1 _ (hUS n)).continuous_fderiv one_ne_zero
  have hρy : 0 < ‖y‖ + 1 := by positivity
  have hE0 := hEn (‖y‖ + 1) hρy
  have hmeas : Measurable (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp hcont.enorm).measurable
  simp only [hE] at hE0
  rw [lintegral_eq_zero_iff hmeas] at hE0
  have hEq : EqOn (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) 0 (ball (0 : Rn n) (‖y‖ + 1)) :=
    Measure.eqOn_open_of_ae_eq hE0 isOpen_ball
      ((ENNReal.continuous_pow 2).comp hcont.enorm).continuousOn continuousOn_const
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + 1) := by simp
  have := hEq hy
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at this
  rw [← ofReal_norm, ENNReal.ofReal_eq_zero, norm_le_zero_iff] at this
  exact this
/-- 1-D lemma: a function with an explicit derivative chain ending in `0` (a polynomial of
degree `< m`) and sublinear growth `‖G₀ t − G₀ 0‖ ≤ C |t|^α`, `α < 1`, is constant. -/
theorem dohr_eb_sch_liou_poly_sublinear_const : ∀ (ℓ m : ℕ) (α C : ℝ) (G : ℕ → ℝ → Rn ℓ), α < 1 → (∀ j < m, ∀ t : ℝ, HasDerivAt (G j) (G (j + 1) t) t) → (∀ t : ℝ, G m t = 0) → (∀ t : ℝ, ‖G 0 t - G 0 0‖ ≤ C * |t| ^ α) → ∀ t : ℝ, G 0 t = G 0 0 := by
  intro ℓ m α C G hα hder hm hgrow
  -- Step 1: Taylor formula with zero remainder, by downward induction.
  have taylor : ∀ k i, i + k = m → ∀ t : ℝ,
      G i t = ∑ j ∈ Finset.range k, (t ^ j / (j.factorial : ℝ)) • G (i + j) 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi t
      simp only [add_zero] at hi
      subst hi
      simp [hm]
    | succ k ih =>
      intro i hi t
      have hIH : ∀ s : ℝ, G (i + 1) s =
          ∑ j ∈ Finset.range k, (s ^ j / (j.factorial : ℝ)) • G (i + 1 + j) 0 :=
        fun s => ih (i + 1) (by omega) s
      set P : ℝ → Rn ℓ := fun s =>
        ∑ j ∈ Finset.range (k + 1), (s ^ j / (j.factorial : ℝ)) • G (i + j) 0 with hP_def
      have hP : ∀ s : ℝ, HasDerivAt P (G (i + 1) s) s := by
        intro s
        rw [hIH s]
        have hsplit : P = fun s => (∑ j ∈ Finset.range k,
            (s ^ (j + 1) / ((j + 1).factorial : ℝ)) • G (i + (j + 1)) 0) + G i 0 := by
          funext s
          simp only [hP_def]
          rw [Finset.sum_range_succ']
          simp
        rw [hsplit]
        apply HasDerivAt.add_const
        apply HasDerivAt.fun_sum
        intro j _
        have h1 : HasDerivAt (fun s : ℝ => s ^ (j + 1) / ((j + 1).factorial : ℝ))
            (((j + 1 : ℕ) : ℝ) * s ^ j / ((j + 1).factorial : ℝ)) s := by
          have := (hasDerivAt_pow (j + 1) s).div_const ((j + 1).factorial : ℝ)
          simpa using this
        have h2 := h1.smul_const (G (i + (j + 1)) 0)
        have heq : (((j + 1 : ℕ) : ℝ) * s ^ j / ((j + 1).factorial : ℝ)) • G (i + (j + 1)) 0 =
            (s ^ j / (j.factorial : ℝ)) • G (i + 1 + j) 0 := by
          have hidx : i + (j + 1) = i + 1 + j := by omega
          rw [hidx]
          congr 1
          rw [Nat.factorial_succ]
          push_cast
          have : (j.factorial : ℝ) ≠ 0 := by positivity
          field_simp
        rw [← heq]
        exact h2
      have hGi : ∀ s : ℝ, HasDerivAt (G i) (G (i + 1) s) s := hder i (by omega)
      have hD : ∀ s : ℝ, HasDerivAt (fun s => G i s - P s) 0 s := by
        intro s
        have := (hGi s).sub (hP s)
        rwa [sub_self] at this
      have hconst := is_const_of_deriv_eq_zero (f := fun s => G i s - P s)
        (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t 0
      have hP0 : P 0 = G i 0 := by
        simp only [hP_def]
        rw [Finset.sum_range_succ']
        simp
      simp only [hP0, sub_self] at hconst
      exact sub_eq_zero.mp hconst
  have hT : ∀ t : ℝ, G 0 t = ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) • G j 0 := by
    intro t
    simpa using taylor m 0 (by omega) t
  set a : ℕ → Rn ℓ := fun j => G j 0 with ha
  set β : ℝ := max α 0 with hβ
  have hβ1 : β < 1 := max_lt hα one_pos
  have hβ0 : 0 ≤ β := le_max_right _ _
  set Cp : ℝ := max C 0 with hCp
  -- Step 2: the top coefficient vanishes when all higher ones do.
  have core : ∀ J, 1 ≤ J → J < m → (∀ j, J < j → j < m → a j = 0) → a J = 0 := by
    intro J hJ1 hJm hhigh
    have hT' : ∀ t : ℝ, G 0 t =
        ∑ j ∈ Finset.range (J + 1), (t ^ j / (j.factorial : ℝ)) • a j := by
      intro t
      rw [hT t]
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj hj'
        simp only [Finset.mem_range, not_lt] at hj hj'
        rw [show a j = 0 from hhigh j (by omega) hj, smul_zero]
    set B : ℝ := ∑ j ∈ Finset.range J, ‖a j‖ with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    set M : ℝ := (J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B) with hM
    have hbound : ∀ t : ℝ, 1 ≤ t → ‖a J‖ ≤ M * t ^ (β - 1) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
      have hrest : ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ ≤
          t ^ (J - 1) * B := by
        calc ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖
            ≤ ∑ j ∈ Finset.range J, ‖(t ^ j / (j.factorial : ℝ)) • a j‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range J, t ^ (J - 1) * ‖a j‖ := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [Finset.mem_range] at hj
            rw [norm_smul]
            gcongr
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            calc t ^ j / (j.factorial : ℝ) ≤ t ^ j := by
                  apply div_le_self (by positivity)
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
              _ ≤ t ^ (J - 1) := pow_le_pow_right₀ ht (by omega)
          _ = t ^ (J - 1) * B := by rw [hB, Finset.mul_sum]
      have hsplit : G 0 t = (t ^ J / (J.factorial : ℝ)) • a J +
          ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j := by
        rw [hT' t, Finset.sum_range_succ, add_comm]
      have hgrow' : ‖G 0 t - G 0 0‖ ≤ Cp * t ^ β := by
        calc ‖G 0 t - G 0 0‖ ≤ C * |t| ^ α := hgrow t
          _ ≤ Cp * t ^ α := by
            rw [abs_of_pos ht0]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _)
          _ ≤ Cp * t ^ β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _))
              (le_max_right _ _)
      have hmain : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ ≤
          Cp * t ^ β + ‖G 0 0‖ + t ^ (J - 1) * B := by
        have h1 : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ = ‖(t ^ J / (J.factorial : ℝ)) • a J‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [h1]
        have h2 : (t ^ J / (J.factorial : ℝ)) • a J =
            (G 0 t - G 0 0) + G 0 0 -
              ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j := by
          rw [hsplit]; abel
        rw [h2]
        calc ‖(G 0 t - G 0 0) + G 0 0 -
              ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖
            ≤ ‖(G 0 t - G 0 0) + G 0 0‖ +
                ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ := norm_sub_le _ _
          _ ≤ ‖G 0 t - G 0 0‖ + ‖G 0 0‖ +
                ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ Cp * t ^ β + ‖G 0 0‖ + t ^ (J - 1) * B := by gcongr
      have htJ1 : (t ^ (J - 1) : ℝ) = t ^ ((J : ℝ) - 1) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub hJ1]; ring
      have hpowJ : (t ^ J : ℝ) = t ^ ((J : ℝ) - 1 + β) * t ^ (1 - β) := by
        rw [← Real.rpow_add ht0, ← Real.rpow_natCast]; congr 1; ring
      have hA : Cp * t ^ β ≤ Cp * t ^ ((J : ℝ) - 1 + β) := by
        have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
          (le_max_right _ _)
      have hB' : ‖G 0 0‖ ≤ ‖G 0 0‖ * t ^ ((J : ℝ) - 1 + β) := by
        have : 1 ≤ t ^ ((J : ℝ) - 1 + β) := Real.one_le_rpow ht (by
          have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
          linarith)
        nlinarith [norm_nonneg (G 0 0)]
      have hC' : t ^ (J - 1) * B ≤ t ^ ((J : ℝ) - 1 + β) * B := by
        rw [htJ1]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hB0
      have hsum : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ ≤
          (Cp + ‖G 0 0‖ + B) * t ^ ((J : ℝ) - 1 + β) := by
        nlinarith [hmain, hA, hB', hC']
      have hfact : (0 : ℝ) < J.factorial := by positivity
      have htpos : 0 < t ^ ((J : ℝ) - 1 + β) := Real.rpow_pos_of_pos ht0 _
      have hneg : t ^ (β - 1) * t ^ (1 - β) = 1 := by
        rw [← Real.rpow_add ht0]; simp
      rw [hpowJ] at hsum
      have : t ^ (1 - β) * ‖a J‖ ≤ (J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B) := by
        have h3 : t ^ ((J : ℝ) - 1 + β) * (t ^ (1 - β) * ‖a J‖ / (J.factorial : ℝ)) ≤
            t ^ ((J : ℝ) - 1 + β) * (Cp + ‖G 0 0‖ + B) := by
          calc t ^ ((J : ℝ) - 1 + β) * (t ^ (1 - β) * ‖a J‖ / (J.factorial : ℝ))
              = t ^ ((J : ℝ) - 1 + β) * t ^ (1 - β) / (J.factorial : ℝ) * ‖a J‖ := by ring
            _ ≤ (Cp + ‖G 0 0‖ + B) * t ^ ((J : ℝ) - 1 + β) := hsum
            _ = t ^ ((J : ℝ) - 1 + β) * (Cp + ‖G 0 0‖ + B) := by ring
        have h4 := le_of_mul_le_mul_left h3 htpos
        rw [div_le_iff₀ hfact] at h4
        linarith
      calc ‖a J‖ = t ^ (β - 1) * (t ^ (1 - β) * ‖a J‖) := by
            rw [← mul_assoc, hneg, one_mul]
        _ ≤ t ^ (β - 1) * ((J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B)) := by
            gcongr
        _ = M * t ^ (β - 1) := by rw [hM]; ring
    have hlim : Tendsto (fun t : ℝ => M * t ^ (β - 1)) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := 1 - β) (by linarith)
      have h' : (fun t : ℝ => t ^ (-(1 - β))) = fun t => t ^ (β - 1) := by
        funext t; congr 1; ring
      rw [h'] at h
      simpa using h.const_mul M
    have hle : ‖a J‖ ≤ 0 :=
      ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun t ht => hbound t ht⟩)
    exact norm_le_zero_iff.mp hle
  -- Step 3: downward induction, all coefficients of positive degree vanish.
  have hall : ∀ d, ∀ j, m - d ≤ j → 1 ≤ j → j < m → a j = 0 := by
    intro d
    induction d with
    | zero => intro j hj _ hjm; omega
    | succ d ih =>
      intro j hj hj1 hjm
      by_cases hjd : m - d ≤ j
      · exact ih j hjd hj1 hjm
      · exact core j hj1 hjm (fun j' hj' hj'm => ih j' (by omega) (by omega) hj'm)
  intro t
  rw [hT t, hT 0]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simp
  · have := hall m j (by omega) hpos hj
    simp only [ha] at this
    simp [this]
/-- Iterated Caccioppoli along the chain `U_j = (d_u)^j (d_w W)` inside a class `S` closed under
directional derivatives: the energy of `D U_n` on `B_ρ(0)` is `O(ρ^{2α-2-n})`, hence zero. -/
theorem dohr_eb_sch_liou_chain_vanish : ∀ (n ℓ : ℕ) (α K C : ℝ) (S : Set (Rn n → Rn ℓ)) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 ≤ K → 0 ≤ C → (∀ V ∈ S, ContDiff ℝ 1 V) → (∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S) → (∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ, ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2) → W ∈ S → (∀ x : Rn n, ‖fderiv ℝ W x - fderiv ℝ W 0‖ ≤ K * ‖x‖ ^ α) → ∀ u w y : Rn n, fderiv ℝ ((fun g : Rn n → Rn ℓ => fun z => fderiv ℝ g z u)^[n] (fun z => fderiv ℝ W z w)) y = 0 := by
  intro n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS hgrowth u w y
  set D : (Rn n → Rn ℓ) → (Rn n → Rn ℓ) := fun g z => fderiv ℝ g z u with hD
  set U : ℕ → Rn n → Rn ℓ := fun j => D^[j] (fun z => fderiv ℝ W z w) with hU
  have hUS : ∀ j, U j ∈ S := by
    intro j
    induction j with
    | zero => exact hS2 W hWS w
    | succ j ih =>
      simp only [hU] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact hS2 _ ih u
  have hUsucc : ∀ j, U (j + 1) = fun z => fderiv ℝ (U j) z u := by
    intro j
    simp only [hU]
    rw [Function.iterate_succ_apply']
  set E : ℕ → ℝ → ℝ≥0∞ := fun j ρ => ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ (U j) x‖ₑ ^ 2 with hE
  set ω : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hω
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hvol : ∀ r : ℝ, 0 < r → volume (ball (0 : Rn n) r) = ENNReal.ofReal (r ^ n * ω) := by
    intro r hr
    rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity), hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  set e0 : ℝ := (n : ℝ) + 2 * α - 2 with he0
  set M0 : ℝ := C * K ^ 2 * ‖w‖ ^ 2 * (2 : ℝ) ^ ((n : ℝ) + 2 * α) * ω with hM0
  have hM0nn : 0 ≤ M0 := by positivity
  -- base estimate (Caccioppoli with c = DW(0) w)
  have hbase : ∀ ρ : ℝ, 0 < ρ → E 0 ρ ≤ ENNReal.ofReal (M0 * ρ ^ e0) := by
    intro ρ hρ
    have h1 := hS3 (U 0) (hUS 0) ρ hρ (fderiv ℝ W 0 w)
    refine h1.trans ?_
    have hc : 0 ≤ K * (2 * ρ) ^ α * ‖w‖ := by positivity
    have h2 : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2 ≤
        ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      have hx' : ‖x‖ < 2 * ρ := by simpa using hx
      have hle : ‖U 0 x - fderiv ℝ W 0 w‖ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
        simp only [hU, Function.iterate_zero, id]
        calc ‖fderiv ℝ W x w - fderiv ℝ W 0 w‖ = ‖(fderiv ℝ W x - fderiv ℝ W 0) w‖ := by simp
          _ ≤ ‖fderiv ℝ W x - fderiv ℝ W 0‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ K * ‖x‖ ^ α * ‖w‖ := by gcongr; exact hgrowth x
          _ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
            gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
    calc ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2
        ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) *
            ENNReal.ofReal ((2 * ρ) ^ n * ω)) := by
          rw [setLIntegral_const, hvol (2 * ρ) (by positivity)]
      _ = ENNReal.ofReal (C / ρ ^ 2 * ((K * (2 * ρ) ^ α * ‖w‖) ^ 2 * ((2 * ρ) ^ n * ω))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (M0 * ρ ^ e0) := by
          congr 1
          have h2ρ : (2 * ρ) ^ α = 2 ^ α * ρ ^ α := Real.mul_rpow (by norm_num) hρ.le
          have hpow : ρ ^ e0 = ρ ^ n * (ρ ^ α) ^ 2 / ρ ^ 2 := by
            rw [he0, Real.rpow_sub hρ, Real.rpow_add hρ, Real.rpow_natCast, Real.rpow_two,
              ← Real.rpow_natCast (ρ ^ α) 2, ← Real.rpow_mul hρ.le]
            push_cast; ring_nf
          have h2pow : (2 : ℝ) ^ ((n : ℝ) + 2 * α) = 2 ^ n * (2 ^ α) ^ 2 := by
            rw [Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.rpow_natCast ((2:ℝ) ^ α) 2,
              ← Real.rpow_mul (by norm_num)]
            push_cast; ring_nf
          rw [hpow, hM0, h2pow, h2ρ, mul_pow]
          field_simp
          ring
  -- iteration (Caccioppoli with c = 0)
  have hiter : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 0 < ρ →
      E j ρ ≤ ENNReal.ofReal (M * ρ ^ (e0 - 2 * (j : ℝ))) := by
    intro j
    induction j with
    | zero => exact ⟨M0, hM0nn, fun ρ hρ => by simpa using hbase ρ hρ⟩
    | succ j ih =>
      obtain ⟨M, hM, hb⟩ := ih
      refine ⟨C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)), by positivity, fun ρ hρ => ?_⟩
      have hstep : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 ≤
          ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ) := by
        simp only [hE]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_mono
        intro x
        simp only [hUsucc j, sub_zero]
        calc ‖fderiv ℝ (U j) x u‖ₑ ^ 2 ≤ (‖fderiv ℝ (U j) x‖ₑ * ‖u‖ₑ) ^ 2 := by
              gcongr; exact ContinuousLinearMap.le_opENorm _ _
          _ = ENNReal.ofReal (‖u‖ ^ 2) * ‖fderiv ℝ (U j) x‖ₑ ^ 2 := by
              rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; ring
      calc E (j + 1) ρ ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 :=
            hS3 _ (hUS (j + 1)) ρ hρ 0
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ)) := by
            gcongr
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) *
              ENNReal.ofReal (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ)))) := by
            gcongr; exact hb (2 * ρ) (by positivity)
        _ = ENNReal.ofReal (C / ρ ^ 2 * (‖u‖ ^ 2 * (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ))))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)) *
              ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ))) := by
            congr 1
            have h2ρ : (2 * ρ) ^ (e0 - 2 * (j : ℝ)) =
                2 ^ (e0 - 2 * (j : ℝ)) * ρ ^ (e0 - 2 * (j : ℝ)) :=
              Real.mul_rpow (by norm_num) hρ.le
            have hpow : ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ)) = ρ ^ (e0 - 2 * (j : ℝ)) / ρ ^ 2 := by
              rw [← Real.rpow_two, ← Real.rpow_sub hρ]; push_cast; ring_nf
            rw [h2ρ, hpow]
            field_simp
  -- decay: the energy of D U_n vanishes on every ball
  obtain ⟨M, hM, hb⟩ := hiter n
  have hneg : e0 - 2 * (n : ℝ) < 0 := by rw [he0]; linarith
  have hEn : ∀ ρ0 : ℝ, 0 < ρ0 → E n ρ0 = 0 := by
    intro ρ0 hρ0
    have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (M * ρ ^ (e0 - 2 * (n : ℝ)))) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun ρ : ℝ => ρ ^ (e0 - 2 * (n : ℝ))) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := -(e0 - 2 * (n : ℝ))) (by linarith)
        simpa using this
      have h2 := h1.const_mul M
      rw [mul_zero] at h2
      have := ENNReal.tendsto_ofReal h2
      simpa using this
    have hle : E n ρ0 ≤ 0 := by
      refine ge_of_tendsto hlim (eventually_atTop.2 ⟨ρ0, fun ρ hρ => ?_⟩)
      exact (lintegral_mono_set (ball_subset_ball hρ)).trans (hb ρ (lt_of_lt_of_le hρ0 hρ))
    exact le_antisymm hle zero_le
  -- pointwise vanishing (continuity + open sets have positive measure)
  have hcont : Continuous (fderiv ℝ (U n)) := (hS1 _ (hUS n)).continuous_fderiv one_ne_zero
  have hρy : 0 < ‖y‖ + 1 := by positivity
  have hE0 := hEn (‖y‖ + 1) hρy
  have hmeas : Measurable (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp hcont.enorm).measurable
  simp only [hE] at hE0
  rw [lintegral_eq_zero_iff hmeas] at hE0
  have hEq : EqOn (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) 0 (ball (0 : Rn n) (‖y‖ + 1)) :=
    Measure.eqOn_open_of_ae_eq hE0 isOpen_ball
      ((ENNReal.continuous_pow 2).comp hcont.enorm).continuousOn continuousOn_const
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + 1) := by simp
  have := hEq hy
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at this
  rw [← ofReal_norm, ENNReal.ofReal_eq_zero, norm_le_zero_iff] at this
  exact this


/-- Abstract Liouville theorem.  Let `S` be a class of `C¹` maps `ℝⁿ → ℝ^ℓ` that is closed under
directional derivatives and satisfies the Caccioppoli inequality on balls centred at `0`.  If
`W ∈ S` satisfies `‖DW(x) - DW(0)‖ ≤ K |x|^α` with `0 < α < 1`, then `DW` is constant. -/
theorem Submission.dohr_eb_sch_liou_abstract : ∀ (n ℓ : ℕ) (α K C : ℝ) (S : Set (Rn n → Rn ℓ)) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 ≤ K → 0 ≤ C → (∀ V ∈ S, ContDiff ℝ 1 V) → (∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S) → (∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ, ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2) → W ∈ S → (∀ x : Rn n, ‖fderiv ℝ W x - fderiv ℝ W 0‖ ≤ K * ‖x‖ ^ α) → ∀ x : Rn n, fderiv ℝ W x = fderiv ℝ W 0 := by
  intro n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS hgrowth x
  -- It suffices to show `DW(x) w = DW(0) w` for every `w`.
  ext1 w
  -- `D g = (z ↦ Dg(z) x)` is the directional derivative along `x`.
  set D : (Rn n → Rn ℓ) → (Rn n → Rn ℓ) := fun g z => fderiv ℝ g z x with hD
  -- `U_j := D^[j] (z ↦ DW(z) w)` lies in `S` by (S2), hence is `C¹` by (S1).
  have hUS : ∀ j : ℕ, (D^[j] (fun z => fderiv ℝ W z w)) ∈ S := by
    intro j
    induction j with
    | zero => exact hS2 W hWS w
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hS2 _ ih x
  -- `G_j(t) := U_j(t x)`; by the chain rule `G_j' = G_{j+1}`.
  let G : ℕ → ℝ → Rn ℓ := fun j t => (D^[j] (fun z => fderiv ℝ W z w)) (t • x)
  have hderiv : ∀ j < n + 1, ∀ t : ℝ, HasDerivAt (G j) (G (j + 1) t) t := by
    intro j _ t
    have hdiff : DifferentiableAt ℝ (D^[j] (fun z => fderiv ℝ W z w)) (t • x) :=
      ((hS1 _ (hUS j)).differentiable one_ne_zero) _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 := hdiff.hasFDerivAt.comp_hasDerivAt t h1
    have h3 : G (j + 1) t = fderiv ℝ (D^[j] (fun z => fderiv ℝ W z w)) (t • x) x := by
      simp only [G]
      rw [Function.iterate_succ_apply']
    rw [h3]
    exact h2
  -- `G_{n+1}(t) = DU_n(t x) x = 0` by `chain_vanish` with `u := x`.
  have hzero : ∀ t : ℝ, G (n + 1) t = 0 := by
    intro t
    simp only [G]
    rw [Function.iterate_succ_apply']
    have := Submission.dohr_eb_sch_liou_chain_vanish n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS
      hgrowth x w (t • x)
    simp only [hD] at this ⊢
    rw [this]
    rfl
  -- Growth: `|G_0(t) - G_0(0)| ≤ (K |x|^α |w|) |t|^α`.
  have hgrow : ∀ t : ℝ, ‖G 0 t - G 0 0‖ ≤ (K * ‖x‖ ^ α * ‖w‖) * |t| ^ α := by
    intro t
    simp only [G, Function.iterate_zero, id, zero_smul]
    calc ‖fderiv ℝ W (t • x) w - fderiv ℝ W 0 w‖
        = ‖(fderiv ℝ W (t • x) - fderiv ℝ W 0) w‖ := by simp
      _ ≤ ‖fderiv ℝ W (t • x) - fderiv ℝ W 0‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * ‖t • x‖ ^ α) * ‖w‖ := by gcongr; exact hgrowth _
      _ = (K * ‖x‖ ^ α * ‖w‖) * |t| ^ α := by
        rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
        ring
  -- `poly_sublinear_const` with `m := n + 1` gives `G_0(1) = G_0(0)`, i.e. `DW(x) w = DW(0) w`.
  have := Submission.dohr_eb_sch_liou_poly_sublinear_const ℓ (n + 1) α (K * ‖x‖ ^ α * ‖w‖) G
    hα1 hderiv hzero hgrow 1
  simpa [G] using this

/-- Directional derivatives of `C²` global weak solutions of a constant-coefficient system are
again global weak solutions: translate the test function, differentiate the (identically zero)
translated integral under the integral sign, and identify `D(d_v V)` with `D²V(·) v` using the
symmetry of `D²V` (sibling `Submission.dohr_eb_sch_liou_snd_deriv_symm`). -/
theorem dohr_eb_sch_liou_dir_deriv_solution : ∀ (n ℓ : ℕ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (v : Rn n), ContDiff ℝ 2 V → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ (fun y => fderiv ℝ V y v) x) (fderiv ℝ ζ x) = 0 := by
  intro n ℓ A V v hV hsol ζ hζ hζc
  -- Step 0: `DV` is `C¹`, `Dζ` is continuous with compact support.
  have hDV : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hDVd : Differentiable ℝ (fderiv ℝ V) := hDV.differentiable one_ne_zero
  have hDζcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv (𝕜 := ℝ)
  -- `y ↦ D²V(y) v` is continuous (values in `L`)
  have hD2v : Continuous (fun y => fderiv ℝ (fderiv ℝ V) y v) :=
    (hDV.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  -- Step 1: translated equation `∫ A[DV(x + h v)][Dζ(x)] dx = 0` for every `h`, tested with
  -- `ζ(· - h v)` and translation invariance of Lebesgue measure.
  have hF : ∀ h : ℝ, ∫ x, A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x) = 0 := by
    intro h
    have h1 := hsol (fun x => ζ (x + (-(h • v)))) (hζ.comp (contDiff_id.add contDiff_const))
      (hζc.comp_homeomorph (Homeomorph.addRight (-(h • v))))
    have h2 : ∀ x, fderiv ℝ (fun x => ζ (x + (-(h • v)))) x = fderiv ℝ ζ (x + (-(h • v))) :=
      fun x => fderiv_comp_add_right _
    simp_rw [h2] at h1
    rw [← integral_add_right_eq_self
      (fun x => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x)) (-(h • v))]
    simpa [add_assoc] using h1
  -- Step 2: differentiation under the integral sign at `h = 0`, dominated on `|h| < 1` by
  -- `M⁺ |Dζ|`, where `M` bounds `‖A[D²V(·) v]‖` on the `|v|`-thickening of `tsupport Dζ`.
  set T := tsupport (fderiv ℝ ζ) with hTdef
  have hT : IsCompact T := hDζc
  have hT' : IsCompact (cthickening ‖v‖ T) := hT.cthickening
  have hAcont : Continuous (fun y => A (fderiv ℝ (fderiv ℝ V) y v)) := A.continuous.comp hD2v
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ cthickening ‖v‖ T, ‖A (fderiv ℝ (fderiv ℝ V) y v)‖ ≤ M :=
    hT'.exists_bound_of_continuousOn (f := fun y => A (fderiv ℝ (fderiv ℝ V) y v))
      hAcont.continuousOn
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set F : ℝ → Rn n → ℝ := fun h x => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x) with hFdef
  set F' : ℝ → Rn n → ℝ := fun h x => A (fderiv ℝ (fderiv ℝ V) (x + h • v) v) (fderiv ℝ ζ x)
    with hFdef'
  have hFcont : ∀ h, Continuous (F h) := fun h =>
    (A.continuous.comp (hDV.continuous.comp (continuous_id.add continuous_const))).clm_apply
      hDζcont
  have hF'cont : ∀ h, Continuous (F' h) := fun h =>
    (hAcont.comp (continuous_id.add continuous_const)).clm_apply hDζcont
  have hzero_out : ∀ x, x ∉ T → fderiv ℝ ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hsuppF0 : HasCompactSupport (F 0) := by
    apply HasCompactSupport.intro hT
    intro x hx
    simp [hFdef, hzero_out x hx]
  have hbound_int : Integrable (fun x => M' * ‖fderiv ℝ ζ x‖) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul hDζcont.norm
    · apply HasCompactSupport.intro hT
      intro x hx
      simp [hzero_out x hx]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F)
    (F' := F') (x₀ := 0) (s := ball (0 : ℝ) 1)
    (bound := fun x => M' * ‖fderiv ℝ ζ x‖)
    (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun h => (hFcont h).aestronglyMeasurable)
    ((hFcont 0).integrable_of_hasCompactSupport hsuppF0)
    (hF'cont 0).aestronglyMeasurable
    (Eventually.of_forall fun x h hh => by
      by_cases hx : x ∈ T
      · have hmem : x + h • v ∈ cthickening ‖v‖ T := by
          apply mem_cthickening_of_dist_le (x + h • v) x ‖v‖ T hx
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
          have : ‖h‖ ≤ 1 := (mem_ball_zero_iff.mp hh).le
          calc ‖h‖ * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
            _ = ‖v‖ := one_mul _
        calc ‖F' h x‖ ≤ ‖A (fderiv ℝ (fderiv ℝ V) (x + h • v) v)‖ * ‖fderiv ℝ ζ x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M' * ‖fderiv ℝ ζ x‖ := by
              gcongr; exact (hM _ hmem).trans (le_max_left _ _)
      · simp [hFdef', hzero_out x hx])
    hbound_int
    (Eventually.of_forall fun x h _ => by
      have h1 : HasDerivAt (fun h : ℝ => x + h • v) v h := by
        simpa using ((hasDerivAt_id h).smul_const v).const_add x
      have h2 : HasDerivAt (fun h : ℝ => fderiv ℝ V (x + h • v))
          (fderiv ℝ (fderiv ℝ V) (x + h • v) v) h :=
        (hDVd (x + h • v)).hasFDerivAt.comp_hasDerivAt h h1
      have h3 : HasDerivAt (fun h : ℝ => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x))
          (A (fderiv ℝ (fderiv ℝ V) (x + h • v) v) (fderiv ℝ ζ x)) h :=
        (A.flip (fderiv ℝ ζ x)).hasFDerivAt.comp_hasDerivAt h h2
      exact h3)
  -- Step 3: the translated integral is identically `0`, so its derivative at `0` vanishes.
  have hzero : (∫ x, F' 0 x) = 0 := by
    have hconst : (fun h : ℝ => ∫ x, F h x) = fun _ => 0 := funext hF
    have := hderiv.2
    rw [hconst] at this
    exact this.unique (hasDerivAt_const 0 0)
  -- Step 4: `D(d_v V)(x) = D²V(x) v`, by the chain rule and symmetry of the second derivative.
  have hsym : ∀ x, fderiv ℝ (fun y => fderiv ℝ V y v) x = fderiv ℝ (fderiv ℝ V) x v := by
    intro x
    have hd : HasFDerivAt (fun y => fderiv ℝ V y v)
        ((ContinuousLinearMap.apply ℝ (Rn ℓ) v).comp (fderiv ℝ (fderiv ℝ V) x)) x :=
      (ContinuousLinearMap.apply ℝ (Rn ℓ) v).hasFDerivAt.comp x (hDVd x).hasFDerivAt
    rw [hd.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact Submission.dohr_eb_sch_liou_snd_deriv_symm n ℓ V hV x w v
  -- Step 5: conclusion.
  simp_rw [hsym]
  simpa [hFdef'] using hzero
/-- Mollification of a `C^{1,α}` global weak solution: `V = φ_ε ⋆ W` is smooth, keeps the Hölder
constant, is `Kε^α`-close in `C¹`, and is again a global weak solution. -/
theorem dohr_eb_sch_liou_mollify : ∀ (n ℓ : ℕ) (α K ε : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W : Rn n → Rn ℓ), 0 < α → 0 ≤ K → 0 < ε → ContDiff ℝ 1 W → (∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ x) = 0) → ∃ V : Rn n → Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x y : Rn n, ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ K * ‖x - y‖ ^ α) ∧ (∀ x : Rn n, ‖fderiv ℝ V x - fderiv ℝ W x‖ ≤ K * ε ^ α) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0 := by
  intro n ℓ α K ε A W hα hK hε hW hhol hsol
  -- Step 1: mollifier φ := (∫ b)⁻¹ • b for the smooth bump b with radii ε/2 < ε
  let b : ContDiffBump (0 : Rn n) := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hb_cont : Continuous b := b.continuous
  have hb_nonneg : ∀ z, 0 ≤ b z := fun z => b.nonneg
  have hb_cpt : HasCompactSupport b := b.hasCompactSupport
  have hb_int : Integrable b := hb_cont.integrable_of_hasCompactSupport hb_cpt
  have hb_pos : 0 < ∫ z, b z := by
    rw [integral_pos_iff_support_of_nonneg (fun z => hb_nonneg z) hb_int, b.support_eq]
    exact measure_ball_pos volume _ hε
  set c : ℝ := (∫ z, b z)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr hb_pos
  set φ : Rn n → ℝ := fun z => c * b z with hφ_def
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_const.mul b.contDiff
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_nonneg : ∀ z, 0 ≤ φ z := fun z => mul_nonneg hc_pos.le (hb_nonneg z)
  have hφ_cpt : HasCompactSupport φ := hb_cpt.mul_left
  have hφ_int1 : ∫ z, φ z = 1 := by
    simp only [hφ_def]
    rw [integral_const_mul, hc_def, inv_mul_cancel₀ hb_pos.ne']
  have hφ_integrable : Integrable φ := hφ_cont.integrable_of_hasCompactSupport hφ_cpt
  have hφ_zero : ∀ z, ε ≤ ‖z‖ → φ z = 0 := by
    intro z hz
    have : z ∉ Function.support b := by
      rw [b.support_eq, mem_ball_zero_iff]
      exact not_lt.mpr hz
    simp only [hφ_def, Function.notMem_support.mp this, mul_zero]
  have hint : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn n → E),
      Continuous g → Integrable (fun z => φ z • g z) := by
    intro E _ _ g hg
    exact (hφ_cont.smul hg).integrable_of_hasCompactSupport (hφ_cpt.smul_right)
  have hDW_cont : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
  have hW_diff : Differentiable ℝ W := hW.differentiable one_ne_zero
  -- Step 2: V := φ ⋆ W
  set V : Rn n → Rn ℓ := fun x => ∫ z, φ z • W (x - z) with hV_def
  have hVconv : V = MeasureTheory.convolution φ W (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x; simp [hV_def, convolution_def]
  -- Step 3: smoothness
  have hV_smooth : ContDiff ℝ (⊤ : ℕ∞) V := by
    rw [hVconv]
    exact hφ_cpt.contDiff_convolution_left _ hφ_smooth hW.continuous.locallyIntegrable
  -- Step 4: derivative formula DV(x) = ∫ φ(z) DW(x - z) dz
  have hVderiv : ∀ x0 : Rn n, fderiv ℝ V x0 = ∫ z, φ z • fderiv ℝ W (x0 - z) := by
    intro x0
    obtain ⟨Mw, hMw⟩ : ∃ Mw, ∀ y ∈ closedBall x0 (1 + ε), ‖fderiv ℝ W y‖ ≤ Mw :=
      (isCompact_closedBall x0 (1 + ε)).exists_bound_of_continuousOn (f := fderiv ℝ W)
        hDW_cont.continuousOn
    set Mw' := max Mw 0
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
      (F := fun x z => φ z • W (x - z)) (F' := fun x z => φ z • fderiv ℝ W (x - z))
      (x₀ := x0) (s := ball x0 1) (bound := fun z => Mw' * ‖φ z‖)
      (ball_mem_nhds x0 one_pos)
      (Eventually.of_forall fun x =>
        (hφ_cont.smul (hW.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (hint _ (hW.continuous.comp (continuous_const.sub continuous_id)))
      ((hφ_cont.smul (hDW_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun z x hx => by
        by_cases hz : φ z = 0
        · simp [hz]
        · have hz' : ‖z‖ < ε := by
            by_contra h'
            exact hz (hφ_zero z (not_lt.mp h'))
          have hmem : x - z ∈ closedBall x0 (1 + ε) := by
            rw [mem_closedBall, dist_eq_norm]
            have hx' : ‖x - x0‖ < 1 := by rw [← dist_eq_norm]; exact hx
            calc ‖x - z - x0‖ = ‖(x - x0) - z‖ := by congr 1; abel
              _ ≤ ‖x - x0‖ + ‖z‖ := norm_sub_le _ _
              _ ≤ 1 + ε := by linarith
          rw [norm_smul, mul_comm]
          gcongr
          exact (hMw _ hmem).trans (le_max_left _ _))
      ((hφ_integrable.norm).const_mul Mw')
      (Eventually.of_forall fun z x _ => by
        have h2 : HasFDerivAt (fun x => W (x - z)) (fderiv ℝ W (x - z)) x :=
          (hasFDerivAt_comp_sub z).mpr (hW_diff (x - z)).hasFDerivAt
        exact h2.const_smul (φ z))
    exact h.fderiv
  have hDWint : ∀ x : Rn n, Integrable (fun z => φ z • fderiv ℝ W (x - z)) := fun x =>
    hint _ (hDW_cont.comp (continuous_const.sub continuous_id))
  -- Step 5: Hölder bound
  have hhol' : ∀ x y : Rn n, ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ K * ‖x - y‖ ^ α := by
    intro x y
    rw [hVderiv x, hVderiv y, ← integral_sub (hDWint x) (hDWint y)]
    calc ‖∫ z, (φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W (y - z))‖
        ≤ ∫ z, φ z * (K * ‖x - y‖ ^ α) := by
          apply norm_integral_le_of_norm_le (hφ_integrable.mul_const _)
          refine Eventually.of_forall fun z => ?_
          have hs : φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W (y - z) =
              φ z • (fderiv ℝ W (x - z) - fderiv ℝ W (y - z)) := (smul_sub _ _ _).symm
          rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg z)]
          have := hhol (x - z) (y - z)
          rw [sub_sub_sub_cancel_right] at this
          exact mul_le_mul_of_nonneg_left this (hφ_nonneg z)
      _ = K * ‖x - y‖ ^ α := by rw [integral_mul_const, hφ_int1, one_mul]
  -- Step 6: approximation
  have happrox : ∀ x : Rn n, ‖fderiv ℝ V x - fderiv ℝ W x‖ ≤ K * ε ^ α := by
    intro x
    have hconst : fderiv ℝ W x = ∫ z, φ z • fderiv ℝ W x := by
      rw [integral_smul_const, hφ_int1, one_smul]
    rw [hVderiv x, hconst, ← integral_sub (hDWint x) (hφ_integrable.smul_const _)]
    calc ‖∫ z, (φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W x)‖
        ≤ ∫ z, φ z * (K * ε ^ α) := by
          apply norm_integral_le_of_norm_le (hφ_integrable.mul_const _)
          refine Eventually.of_forall fun z => ?_
          have hs : φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W x =
              φ z • (fderiv ℝ W (x - z) - fderiv ℝ W x) := (smul_sub _ _ _).symm
          rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg z)]
          by_cases hz : φ z = 0
          · simp [hz]
          · have hz' : ‖z‖ < ε := by
              by_contra h'
              exact hz (hφ_zero z (not_lt.mp h'))
            apply mul_le_mul_of_nonneg_left _ (hφ_nonneg z)
            calc ‖fderiv ℝ W (x - z) - fderiv ℝ W x‖ ≤ K * ‖(x - z) - x‖ ^ α := hhol _ _
              _ = K * ‖z‖ ^ α := by rw [sub_sub_cancel_left, norm_neg]
              _ ≤ K * ε ^ α := by
                apply mul_le_mul_of_nonneg_left _ hK
                exact Real.rpow_le_rpow (norm_nonneg _) hz'.le hα.le
      _ = K * ε ^ α := by rw [integral_mul_const, hφ_int1, one_mul]
  -- Step 7: weak equation (Fubini + translated test functions)
  have hweak : ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0 := by
    intro ζ hζ hζc
    have hDζcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
    have hDζc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv (𝕜 := ℝ)
    have ha : ∀ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) =
        ∫ z, φ z * A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) := by
      intro x
      rw [hVderiv x]
      have := (A.flip (fderiv ℝ ζ x)).integral_comp_comm (hDWint x)
      simp only [ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul] at this
      exact this.symm
    set H : Rn n → Rn n → ℝ := fun x z => φ z * A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) with hH
    have hHcont : Continuous (Function.uncurry H) :=
      (hφ_cont.comp continuous_snd).mul
        ((A.continuous.comp (hDW_cont.comp (continuous_fst.sub continuous_snd))).clm_apply
          (hDζcont.comp continuous_fst))
    have hHsupp : HasCompactSupport (Function.uncurry H) := by
      apply HasCompactSupport.intro (hDζc.prod hφ_cpt)
      intro p hp
      simp only [mem_prod, not_and_or] at hp
      rcases hp with h | h
      · simp [H, Function.uncurry, image_eq_zero_of_notMem_tsupport h]
      · simp [H, Function.uncurry, image_eq_zero_of_notMem_tsupport h]
    have hHint : Integrable (Function.uncurry H) ((volume : Measure (Rn n)).prod volume) :=
      hHcont.integrable_of_hasCompactSupport (μ := (volume : Measure (Rn n)).prod volume) hHsupp
    have hswap := integral_integral_swap hHint
    have hinner : ∀ z, ∫ x, H x z = 0 := by
      intro z
      simp only [hH]
      rw [integral_const_mul]
      have h1 := hsol (fun x => ζ (x + z)) (hζ.comp (contDiff_id.add contDiff_const))
        (hζc.comp_homeomorph (Homeomorph.addRight z))
      have h2 : ∀ x, fderiv ℝ (fun x => ζ (x + z)) x = fderiv ℝ ζ (x + z) :=
        fun x => fderiv_comp_add_right _
      simp_rw [h2] at h1
      have h3 : ∫ x, A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) =
          ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ (x + z)) := by
        rw [← integral_add_right_eq_self (fun x => A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x)) z]
        simp
      rw [h3, h1, mul_zero]
    calc ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = ∫ x, ∫ z, H x z := by
          congr 1; funext x; exact ha x
      _ = ∫ z, ∫ x, H x z := hswap
      _ = 0 := by simp [hinner]
  exact ⟨V, hV_smooth, hhol', happrox, hweak⟩

end Submission

end GMT.Ch05
