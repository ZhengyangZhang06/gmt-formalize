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

/-- Campanato-type Hölder estimate (proof of Simon Ch. 5, Remark 5.3, step 7(e)).  Let `g` be
continuous on `B_{r+s₀}(0)` and suppose that for `Lⁿ`-a.e. `z ∈ B_r(0)` and all `s ∈ (0, s₀]`,
`∫_{B_{s/2}(z)} |g(x) − g(z)|² dx ≤ A s^{n+2α}` (Hilbert–Schmidt norm).  Then
`|g(x) − g(y)| ≤ (2^{2n+2+2α} A / ω_n)^{1/2} |x − y|^α` for `x, y ∈ B_r(0)` with `|x − y| ≤ s₀/2`.
For good points `x₁, x₂` at distance `d`, average
`|g(x₁) − g(x₂)|² ≤ 2|g(x) − g(x₁)|² + 2|g(x) − g(x₂)|²` over `B_{d/2}(m) ⊆ B_d(x₁) ∩ B_d(x₂)`
(`m` the midpoint, `Lⁿ(B_{d/2}(m)) = ω_n (d/2)ⁿ`) and apply the hypothesis with `s = 2d`; good
points are dense in `B_r(0)` and `g` is continuous.  The ball volume is computed inline from the
Gaussian integral (`∫ e^{−|z|²} = π^{n/2} = Lⁿ(B₁) Γ(n/2 + 1)`), since
`InnerProductSpace.volume_closedBall` lies outside the frozen imports. -/
theorem any_radius_campanato : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (r s₀ A α : ℝ), 0 < r → 0 < s₀ → 0 ≤ A → 0 < α → ContinuousOn g (closedBall 0 (r + s₀)) → (∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) r)), ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (g x - g z)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → ∀ x ∈ closedBall (0 : Rn n) r, ∀ y ∈ closedBall (0 : Rn n) r, ‖x - y‖ ≤ s₀ / 2 → hsNorm (g x - g y) ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) * ‖x - y‖ ^ α := by
  -- Ball volume: `Lⁿ(B_r(x)) = ω_n rⁿ`, from `Lⁿ(B_r(x)) = rⁿ Lⁿ(B₁(0))` and the Gaussian integral.
  have h_ball_volume : ∀ (n : ℕ) (x : Rn n) (r : ℝ), 0 ≤ r → (volume : Measure (Rn n)) (closedBall x r) = ENNReal.ofReal (unitBallVolume n * r ^ n) := by
    intro n x r hr
    set V : ℝ≥0∞ := (volume : Measure (Rn n)) (ball 0 1) with hV
    have hVpos : V ≠ 0 := (measure_ball_pos volume (0 : Rn n) one_pos).ne'
    have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
    -- Gaussian integral over `ℝⁿ`: `∫ e^{-|z|²} dz = π^{n/2}`, by Fubini over the coordinates.
    have hG1 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-t ^ 2)) = ENNReal.ofReal (√Real.pi) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        have := integral_gaussian 1
        simpa using this
      · simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
      · exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
    have hGpi : ∀ m : ℕ, ∫⁻ y : Fin m → ℝ, ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ m := by
      intro m
      induction m with
      | zero =>
        simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul, pow_zero]
        rw [volume_pi, Measure.pi_univ]
        simp
      | succ m ih =>
        have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hφ : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)) := by fun_prop
        rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        rw [Measure.volume_eq_prod]
        have : ∀ z : ℝ × (Fin m → ℝ),
            ∏ i, ENNReal.ofReal (Real.exp
              (-((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm z i) ^ 2)) =
              ENNReal.ofReal (Real.exp (-z.1 ^ 2)) *
                ∏ i : Fin m, ENNReal.ofReal (Real.exp (-(z.2 i) ^ 2)) := by
          intro z
          rw [Fin.prod_univ_succ]
          simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        simp_rw [this]
        have hψ : Measurable fun y : Fin m → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) := by
          fun_prop
        rw [lintegral_prod_mul (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)))
          (g := fun y : Fin m → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)))
          hφ.aemeasurable hψ.aemeasurable, hG1, ih, pow_succ, mul_comm]
    have hGauss : ∫⁻ z : Rn n, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ n := by
      rw [← hGpi n]
      have hmeas : Measurable fun y : Fin n → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-(y i) ^ 2)) := by
        fun_prop
      rw [← (PiLp.volume_preserving_ofLp (Fin n)).lintegral_comp hmeas]
      refine lintegral_congr fun z => ?_
      show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ∏ i, ENNReal.ofReal (Real.exp (-(WithLp.ofLp z i) ^ 2))
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
        Finset.sum_neg_distrib, EuclideanSpace.norm_sq_eq]
      congr 3
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    -- Layer-cake identity (Tonelli): `∫ e^{-|z|²} dz = V Γ(n/2 + 1)` with `V = Lⁿ(B₁(0))`.
    have hexp : ∀ c : ℝ, ENNReal.ofReal (Real.exp (-c)) =
        ∫⁻ s, (Ioi c).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s := by
      intro c
      rw [lintegral_indicator measurableSet_Ioi, ← integral_exp_neg_Ioi c,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (by simpa using exp_neg_integrableOn_Ioi c one_pos :
          IntegrableOn (fun x => Real.exp (-x)) (Ioi c) volume)
      · exact (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun s _ => (Real.exp_pos _).le)
    have hball : ∀ s : ℝ, (volume : Measure (Rn n)) {z | ‖z‖ ^ 2 < s} =
        (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (√s ^ n) * V) s := by
      intro s
      rcases le_or_gt s 0 with hs | hs
      · rw [indicator_of_notMem (by simpa using hs)]
        have : {z : Rn n | ‖z‖ ^ 2 < s} = ∅ := by
          ext z
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
          exact hs.trans (sq_nonneg _)
        rw [this, measure_empty]
      · rw [indicator_of_mem (by simpa using hs)]
        have : {z : Rn n | ‖z‖ ^ 2 < s} = ball 0 (√s) := by
          ext z
          rw [mem_ofPred_eq, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg _)]
        rw [this, Measure.addHaar_ball_of_pos _ _ (Real.sqrt_pos.2 hs), finrank_euclideanSpace_fin]
    have hTonelli : ∫⁻ z : Rn n, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * (ENNReal.ofReal (√s ^ n) * V) := by
      rw [lintegral_congr fun z : Rn n => hexp (‖z‖ ^ 2)]
      rw [lintegral_lintegral_swap]
      · rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun s => ?_
        have : ∀ z : Rn n, (Ioi (‖z‖ ^ 2)).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s =
            {z : Rn n | ‖z‖ ^ 2 < s}.indicator (fun _ => ENNReal.ofReal (Real.exp (-s))) z := by
          intro z
          by_cases h : ‖z‖ ^ 2 < s
          · rw [indicator_of_mem (show s ∈ Ioi (‖z‖ ^ 2) from h),
              indicator_of_mem (show z ∈ {z : Rn n | ‖z‖ ^ 2 < s} from h)]
          · rw [indicator_of_notMem (show s ∉ Ioi (‖z‖ ^ 2) from h),
              indicator_of_notMem (show z ∉ {z : Rn n | ‖z‖ ^ 2 < s} from h)]
        simp_rw [this]
        rw [lintegral_indicator_const (measurableSet_lt (by fun_prop) measurable_const), hball]
        by_cases hs : s ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hs, indicator_of_mem hs]
        · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]
      · apply Measurable.aemeasurable
        have : Function.uncurry (fun (z : Rn n) (s : ℝ) =>
            (Ioi (‖z‖ ^ 2)).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s) =
            {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2}.indicator (fun p => ENNReal.ofReal (Real.exp (-p.2))) := by
          ext ⟨z, s⟩
          by_cases h : ‖z‖ ^ 2 < s
          · rw [Function.uncurry_apply_pair, indicator_of_mem (show s ∈ Ioi (‖z‖ ^ 2) from h),
              indicator_of_mem (show (z, s) ∈ {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2} from h)]
          · rw [Function.uncurry_apply_pair, indicator_of_notMem (show s ∉ Ioi (‖z‖ ^ 2) from h),
              indicator_of_notMem (show (z, s) ∉ {p : Rn n × ℝ | ‖p.1‖ ^ 2 < p.2} from h)]
        rw [this]
        exact (by fun_prop : Measurable fun p : Rn n × ℝ => ENNReal.ofReal (Real.exp (-p.2))).indicator
          (measurableSet_lt (by fun_prop) (by fun_prop))
    have hGamma : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * (ENNReal.ofReal (√s ^ n) * V) =
        V * ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) := by
      have hpos : (0 : ℝ) < (n : ℝ) / 2 + 1 := by positivity
      rw [Real.Gamma_eq_integral hpos, ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent hpos)]
      · rw [← lintegral_const_mul' _ _ hVtop]
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
        have h1 : √s ^ n = s ^ ((n : ℝ) / 2 + 1 - 1) := by
          rw [add_sub_cancel_right, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs0]
          ring_nf
        rw [h1, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _))
    -- Solve for `V`: `V = π^{n/2} / Γ(n/2 + 1) = ω_n`.
    have hΓpos : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hVeq : V = ENNReal.ofReal (unitBallVolume n) := by
      have h := hGauss.symm.trans (hTonelli.trans hGamma)
      -- `h : ofReal √π ^ n = V * ofReal Γ`
      have hΓne : ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) ≠ 0 := by simpa using hΓpos
      have hV' : V = ENNReal.ofReal (√Real.pi) ^ n /
          ENNReal.ofReal (Real.Gamma ((n : ℝ) / 2 + 1)) :=
        (ENNReal.eq_div_iff hΓne ENNReal.ofReal_ne_top).2 (by rw [mul_comm]; exact h.symm)
      rw [hV', ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_div_of_pos hΓpos]
      congr 1
      unfold unitBallVolume
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
      ring_nf
    -- Scale: `Lⁿ(B_r(x)) = rⁿ V`.
    rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ← hV, hVeq,
      ← ENNReal.ofReal_mul (pow_nonneg hr n), mul_comm]
  -- Step 1: `|A − B|² ≤ 2|C − A|² + 2|C − B|²`, columnwise for the Hilbert–Schmidt norm.
  have h_hs_sq_le : ∀ (m k : ℕ) (A B C : Rn m →L[ℝ] Rn k), hsNormSq (A - B) ≤ 2 * hsNormSq (C - A) + 2 * hsNormSq (C - B) := by
    intro m k A B C
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    set e : Rn m := EuclideanSpace.single i (1 : ℝ)
    have h : (A - B) e = (C - B) e - (C - A) e := by
      simp only [sub_apply]
      abel
    rw [h]
    have h1 := norm_sub_le ((C - B) e) ((C - A) e)
    have h2 := norm_nonneg ((C - B) e - (C - A) e)
    nlinarith [sq_nonneg (‖(C - B) e‖ - ‖(C - A) e‖), norm_nonneg ((C - B) e),
      norm_nonneg ((C - A) e)]
  -- Step 2: a property holding a.e. on `B_r(0)` holds at points of `B_r(0)` arbitrarily close
  -- to each `x ∈ B_r(0)`, since every ball meets `B_r(0)` in a set of positive measure.
  have h_ae_dense : ∀ (n : ℕ) (r : ℝ), 0 < r → ∀ (P : Rn n → Prop), (∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) r)), P z) → ∀ x ∈ closedBall (0 : Rn n) r, ∀ ε : ℝ, 0 < ε → ∃ z ∈ closedBall (0 : Rn n) r, P z ∧ ‖z - x‖ < ε := by
    intro n r hr P hP x hx ε hε
    rw [ae_restrict_iff' measurableSet_closedBall] at hP
    set t : ℝ := min 1 (ε / (4 * r)) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htr : t * r ≤ ε / 4 := by
      have : t ≤ ε / (4 * r) := min_le_right _ _
      calc t * r ≤ ε / (4 * r) * r := mul_le_mul_of_nonneg_right this hr.le
        _ = ε / 4 := by field_simp
    set c : Rn n := (1 - t) • x with hc
    have hxr : ‖x‖ ≤ r := by simpa using hx
    have hcn : ‖c‖ ≤ (1 - t) * r := by
      rw [hc, norm_smul, Real.norm_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left hxr (by linarith)
    have hcx : ‖c - x‖ ≤ t * r := by
      have : c - x = (-t) • x := by rw [hc]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left hxr ht0.le
    have hsub : ball c (t * r) ⊆ closedBall (0 : Rn n) r ∩ ball x ε := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      constructor
      · rw [mem_closedBall, dist_zero_right]
        calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ t * r + (1 - t) * r := by linarith
          _ = r := by ring
      · rw [mem_ball, dist_eq_norm]
        calc ‖z - x‖ = ‖(z - c) + (c - x)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - c‖ + ‖c - x‖ := norm_add_le _ _
          _ < ε := by linarith
    have hpos : 0 < (volume : Measure (Rn n)) (ball c (t * r)) :=
      measure_ball_pos _ _ (by positivity)
    by_contra hcon
    push Not at hcon
    have hnull : (volume : Measure (Rn n)) (ball c (t * r)) = 0 := by
      rw [ae_iff] at hP
      refine measure_mono_null (fun z hz => ?_) hP
      obtain ⟨hz1, hz2⟩ := hsub hz
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hz1, fun hPz => ?_⟩
      have := hcon z hz1 hPz
      rw [mem_ball, dist_eq_norm] at hz2
      linarith
    exact hpos.ne' hnull
  -- Steps 3–4: the estimate for two good points at distance `d ∈ (0, s₀/2]`, by averaging over
  -- the midpoint ball `B_{d/2}(m) ⊆ B_d(x₁) ∩ B_d(x₂)` and using the hypothesis with `s = 2d`.
  have h_pair : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (r s₀ A α : ℝ), 0 ≤ A → ContinuousOn g (closedBall 0 (r + s₀)) → ∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r, 0 < ‖x₁ - x₂‖ → ‖x₁ - x₂‖ ≤ s₀ / 2 → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall x₁ (s / 2), ENNReal.ofReal (hsNormSq (g x - g x₁)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall x₂ (s / 2), ENNReal.ofReal (hsNormSq (g x - g x₂)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → hsNorm (g x₁ - g x₂) ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) * ‖x₁ - x₂‖ ^ α := by
    intro n ℓ g r s₀ A α hA hg x₁ hx₁ x₂ hx₂ hd hds h₁ h₂
    set d := ‖x₁ - x₂‖ with hd_def
    set m : Rn n := (1 / 2 : ℝ) • (x₁ + x₂) with hm
    -- the midpoint ball lies in both balls of radius d and in the big ball
    have hm1 : ‖m - x₁‖ = d / 2 := by
      have : m - x₁ = (1 / 2 : ℝ) • (x₂ - x₁) := by rw [hm]; module
      rw [this, norm_smul, norm_sub_rev, Real.norm_of_nonneg (by norm_num)]
      ring
    have hm2 : ‖m - x₂‖ = d / 2 := by
      have : m - x₂ = (1 / 2 : ℝ) • (x₁ - x₂) := by rw [hm]; module
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]
      ring
    have hB1 : closedBall m (d / 2) ⊆ closedBall x₁ d := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      calc ‖z - x₁‖ = ‖(z - m) + (m - x₁)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - m‖ + ‖m - x₁‖ := norm_add_le _ _
        _ ≤ d := by rw [hm1]; linarith
    have hB2 : closedBall m (d / 2) ⊆ closedBall x₂ d := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      calc ‖z - x₂‖ = ‖(z - m) + (m - x₂)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - m‖ + ‖m - x₂‖ := norm_add_le _ _
        _ ≤ d := by rw [hm2]; linarith
    have hBbig : closedBall m (d / 2) ⊆ closedBall 0 (r + s₀) := by
      intro z hz
      have hz1 := hB1 hz
      rw [mem_closedBall, dist_eq_norm] at hz1
      rw [mem_closedBall, dist_zero_right]
      have hx₁r : ‖x₁‖ ≤ r := by simpa using hx₁
      calc ‖z‖ = ‖(z - x₁) + x₁‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x₁‖ + ‖x₁‖ := norm_add_le _ _
        _ ≤ r + s₀ := by linarith
    -- measurability of one integrand on the midpoint ball
    have hmeas : AEMeasurable (fun y => 2 * ENNReal.ofReal (hsNormSq (g y - g x₁)))
        (volume.restrict (closedBall m (d / 2))) := by
      have hcont : ContinuousOn (fun y => hsNormSq (g y - g x₁)) (closedBall m (d / 2)) := by
        have hgB : ContinuousOn g (closedBall m (d / 2)) := hg.mono hBbig
        unfold hsNormSq
        fun_prop
      exact ((hcont.aemeasurable measurableSet_closedBall).ennreal_ofReal).const_mul 2
    -- the hypotheses at s = 2 d
    have hs : 0 < 2 * d := by positivity
    have hs' : 2 * d ≤ s₀ := by linarith
    have hI1 := h₁ (2 * d) hs hs'
    have hI2 := h₂ (2 * d) hs hs'
    rw [show 2 * d / 2 = d by ring] at hI1 hI2
    set R := A * (2 * d) ^ ((n : ℝ) + 2 * α) with hR
    have hR0 : 0 ≤ R := mul_nonneg hA (Real.rpow_nonneg hs.le _)
    -- pointwise inequality
    set Q := hsNormSq (g x₁ - g x₂) with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpt : ∀ y, ENNReal.ofReal Q ≤
        2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) + 2 * ENNReal.ofReal (hsNormSq (g y - g x₂)) := by
      intro y
      have hle := h_hs_sq_le n ℓ (g x₁) (g x₂) (g y)
      have h0a : 0 ≤ hsNormSq (g y - g x₁) := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h0b : 0 ≤ hsNormSq (g y - g x₂) := Finset.sum_nonneg fun i _ => sq_nonneg _
      calc ENNReal.ofReal Q
          ≤ ENNReal.ofReal (2 * hsNormSq (g y - g x₁) + 2 * hsNormSq (g y - g x₂)) :=
            ENNReal.ofReal_le_ofReal hle
        _ = 2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) + 2 * ENNReal.ofReal (hsNormSq (g y - g x₂)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    -- integrate over the midpoint ball
    have hint : ENNReal.ofReal Q * (volume : Measure (Rn n)) (closedBall m (d / 2)) ≤
        ENNReal.ofReal (4 * R) := by
      calc ENNReal.ofReal Q * (volume : Measure (Rn n)) (closedBall m (d / 2))
          = ∫⁻ _ in closedBall m (d / 2), ENNReal.ofReal Q := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in closedBall m (d / 2), (2 * ENNReal.ofReal (hsNormSq (g y - g x₁)) +
              2 * ENNReal.ofReal (hsNormSq (g y - g x₂))) := lintegral_mono hpt
        _ = 2 * (∫⁻ y in closedBall m (d / 2), ENNReal.ofReal (hsNormSq (g y - g x₁))) +
              2 * (∫⁻ y in closedBall m (d / 2), ENNReal.ofReal (hsNormSq (g y - g x₂))) := by
            rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * (∫⁻ y in closedBall x₁ d, ENNReal.ofReal (hsNormSq (g y - g x₁))) +
              2 * (∫⁻ y in closedBall x₂ d, ENNReal.ofReal (hsNormSq (g y - g x₂))) := by
            have h1 := lintegral_mono_set (μ := (volume : Measure (Rn n)))
              (f := fun y => ENNReal.ofReal (hsNormSq (g y - g x₁))) hB1
            have h2 := lintegral_mono_set (μ := (volume : Measure (Rn n)))
              (f := fun y => ENNReal.ofReal (hsNormSq (g y - g x₂))) hB2
            gcongr
        _ ≤ 2 * ENNReal.ofReal R + 2 * ENNReal.ofReal R := by gcongr
        _ = ENNReal.ofReal (4 * R) := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
              show ENNReal.ofReal 4 = 4 by norm_num]
            ring
    -- volume of the midpoint ball
    have hω : 0 < unitBallVolume n :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    set W := unitBallVolume n * (d / 2) ^ n with hW
    have hW0 : 0 < W := mul_pos hω (pow_pos (by positivity) n)
    rw [h_ball_volume n m (d / 2) (by positivity), ← ENNReal.ofReal_mul hQ0,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
    -- arithmetic: Q ≤ C * d^(2α)
    set C := 2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n with hC
    have hC0 : 0 ≤ C := div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hA) hω.le
    have hkey : 4 * R = C * d ^ (2 * α) * W := by
      have e1 : (2 * d) ^ ((n : ℝ) + 2 * α) = 2 ^ ((n : ℝ) + 2 * α) * (d ^ n * d ^ (2 * α)) := by
        rw [Real.mul_rpow (by norm_num) hd.le, Real.rpow_add hd, Real.rpow_natCast]
      have e2 : (2 : ℝ) ^ (2 * (n : ℝ) + 2 + 2 * α) = 2 ^ ((n : ℝ) + 2 * α) * 2 ^ n * 4 := by
        rw [show 2 * (n : ℝ) + 2 + 2 * α = ((n : ℝ) + 2 * α) + (n : ℝ) + 2 by ring,
          Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast,
          Real.rpow_two]
        norm_num
      rw [hR, hC, hW, e1, e2, div_pow]
      field_simp
    have hQle : Q ≤ C * d ^ (2 * α) := by
      have : Q * W ≤ C * d ^ (2 * α) * W := by rw [← hkey]; exact hint
      exact le_of_mul_le_mul_right this hW0
    -- square roots
    have hsq : Real.sqrt (d ^ (2 * α)) = d ^ α := by
      rw [show 2 * α = α * 2 by ring, Real.rpow_mul hd.le, Real.rpow_two,
        Real.sqrt_sq (Real.rpow_nonneg hd.le _)]
    calc hsNorm (g x₁ - g x₂) = Real.sqrt Q := rfl
      _ ≤ Real.sqrt (C * d ^ (2 * α)) := Real.sqrt_le_sqrt hQle
      _ = Real.sqrt C * d ^ α := by rw [Real.sqrt_mul hC0, hsq]
  -- Step 5: approximate `x, y` by good points and pass to the limit using continuity of `g`.
  intro n ℓ _hn g r s₀ A α hr hs₀ hA hα hg hae x hx y hy hxy
  set K := Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  by_cases hxy0 : x = y
  · subst hxy0
    have h0 : hsNorm (g x - g x) = 0 := by simp [hsNorm, hsNormSq]
    rw [h0, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero]
  set D := ‖x - y‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hxy0)
  -- the good-point predicate
  set P : Rn n → Prop := fun z => ∀ s : ℝ, 0 < s → s ≤ s₀ →
    ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (g x - g z)) ≤
      ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α)) with hP
  -- shrinking parameters
  set η : ℕ → ℝ := fun k => (1 / 5 : ℝ) * (1 / ((k : ℝ) + 1)) with hη
  have hηpos : ∀ k, 0 < η k := fun k => by simp only [hη]; positivity
  have hηle : ∀ k, η k ≤ 1 / 5 := fun k => by
    simp only [hη]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 5 : ℝ)
    simpa [hη] using this
  -- inner points
  set xk : ℕ → Rn n := fun k => x + η k • (y - x) with hxk
  set yk : ℕ → Rn n := fun k => y + η k • (x - y) with hyk
  have hxk_mem : ∀ k, xk k ∈ closedBall (0 : Rn n) r := fun k =>
    (convex_closedBall (0 : Rn n) r).add_smul_sub_mem hx hy ⟨(hηpos k).le, by linarith [hηle k]⟩
  have hyk_mem : ∀ k, yk k ∈ closedBall (0 : Rn n) r := fun k =>
    (convex_closedBall (0 : Rn n) r).add_smul_sub_mem hy hx ⟨(hηpos k).le, by linarith [hηle k]⟩
  have hxkyk : ∀ k, ‖xk k - yk k‖ = (1 - 2 * η k) * D := fun k => by
    have : xk k - yk k = (1 - 2 * η k) • (x - y) := by
      simp only [hxk, hyk]
      module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith [hηle k])]
  have hxk_x : ∀ k, ‖xk k - x‖ = η k * D := fun k => by
    simp only [hxk, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hηpos k).le]
    rw [norm_sub_rev]
  have hyk_y : ∀ k, ‖yk k - y‖ = η k * D := fun k => by
    simp only [hyk, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hηpos k).le]
    rfl
  -- good points approximating the inner points
  have hgood : ∀ k, ∃ p : Rn n × Rn n, (p.1 ∈ closedBall (0 : Rn n) r ∧ P p.1 ∧
      ‖p.1 - xk k‖ < η k * D / 2) ∧ (p.2 ∈ closedBall (0 : Rn n) r ∧ P p.2 ∧
      ‖p.2 - yk k‖ < η k * D / 2) := by
    intro k
    have hε : 0 < η k * D / 2 := by have := hηpos k; positivity
    obtain ⟨a, ha, hPa, hax⟩ :=
      h_ae_dense n r hr P hae (xk k) (hxk_mem k) _ hε
    obtain ⟨b, hb, hPb, hby⟩ :=
      h_ae_dense n r hr P hae (yk k) (hyk_mem k) _ hε
    exact ⟨(a, b), ⟨ha, hPa, hax⟩, ⟨hb, hPb, hby⟩⟩
  choose p hp1 hp2 using hgood
  -- pair estimate at the approximants
  have hbound : ∀ k, hsNorm (g (p k).1 - g (p k).2) ≤ K * D ^ α := by
    intro k
    obtain ⟨ha, hPa, hax⟩ := hp1 k
    obtain ⟨hb, hPb, hby⟩ := hp2 k
    have hη5 := hηle k
    have hη0 := hηpos k
    have hupper : ‖(p k).1 - (p k).2‖ ≤ D := by
      have h1 : ‖(p k).1 - (p k).2‖ ≤ ‖(p k).1 - xk k‖ + ‖xk k - yk k‖ + ‖yk k - (p k).2‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub ((p k).1) (xk k) ((p k).2)
        have h2 := norm_sub_le_norm_sub_add_norm_sub (xk k) (yk k) ((p k).2)
        linarith
      rw [hxkyk k, norm_sub_rev (yk k)] at h1
      nlinarith
    have hlower : 0 < ‖(p k).1 - (p k).2‖ := by
      have h1 : ‖xk k - yk k‖ ≤ ‖xk k - (p k).1‖ + ‖(p k).1 - (p k).2‖ + ‖(p k).2 - yk k‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (xk k) ((p k).1) (yk k)
        have h2 := norm_sub_le_norm_sub_add_norm_sub ((p k).1) ((p k).2) (yk k)
        linarith
      rw [hxkyk k, norm_sub_rev (xk k)] at h1
      nlinarith
    have hpair := h_pair n ℓ g r s₀ A α hA hg (p k).1 ha (p k).2 hb hlower
      (hupper.trans hxy) hPa hPb
    refine hpair.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    exact Real.rpow_le_rpow (norm_nonneg _) hupper hα.le
  -- convergence of the approximants
  have hbig : closedBall (0 : Rn n) r ⊆ closedBall 0 (r + s₀) :=
    closedBall_subset_closedBall (by linarith)
  have hconv1 : Tendsto (fun k => (p k).1) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k => (3 / 2 * D) * η k) atTop (𝓝 0) := by
      simpa using hηlim.const_mul (3 / 2 * D)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    have := norm_sub_le_norm_sub_add_norm_sub ((p k).1) (xk k) x
    rw [hxk_x k] at this
    have := (hp1 k).2.2
    nlinarith
  have hconv2 : Tendsto (fun k => (p k).2) atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k => (3 / 2 * D) * η k) atTop (𝓝 0) := by
      simpa using hηlim.const_mul (3 / 2 * D)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    have := norm_sub_le_norm_sub_add_norm_sub ((p k).2) (yk k) y
    rw [hyk_y k] at this
    have := (hp2 k).2.2
    nlinarith
  have hgx : Tendsto (fun k => g (p k).1) atTop (𝓝 (g x)) := by
    have h1 : Tendsto (fun k => (p k).1) atTop (𝓝[closedBall 0 (r + s₀)] x) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv1
        (Eventually.of_forall fun k => hbig (hp1 k).1)
    exact (hg.continuousWithinAt (hbig hx)).tendsto.comp h1
  have hgy : Tendsto (fun k => g (p k).2) atTop (𝓝 (g y)) := by
    have h1 : Tendsto (fun k => (p k).2) atTop (𝓝[closedBall 0 (r + s₀)] y) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv2
        (Eventually.of_forall fun k => hbig (hp2 k).1)
    exact (hg.continuousWithinAt (hbig hy)).tendsto.comp h1
  have hcontN : Continuous (fun B : Rn n →L[ℝ] Rn ℓ => hsNorm B) := by
    unfold hsNorm hsNormSq
    fun_prop
  have hlimit : Tendsto (fun k => hsNorm (g (p k).1 - g (p k).2)) atTop
      (𝓝 (hsNorm (g x - g y))) :=
    (hcontN.tendsto _).comp (hgx.sub hgy)
  exact le_of_tendsto' hlimit hbound

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
