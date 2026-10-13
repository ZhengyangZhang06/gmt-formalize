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

/-- **Push-forward domination extends to a.e.-measurable integrands** (null-set transport for
the weighted height bound of a graph piece in the proof of Simon Ch. 5, Remark 5.3; steps 1, 3
and 7 of the height transfer).
If `F : ℝⁿ → ℝ^{n+ℓ}` is `ν`-a.e.-measurable and `∫ h ∘ F dν ≤ ∫ h dμ` for every Borel
`h : ℝ^{n+ℓ} → [0, ∞]`, then the same inequality holds for every `μ`-a.e.-measurable `g`.
Proof: let `g̃` be a Borel version of `g` and `N'` a measurable `μ`-null hull of `{g ≠ g̃}`.
Testing with `h = 1_{N'}` gives `∫ 1_{N'} ∘ F dν ≤ μ N' = 0`, so `F x ∉ N'` for `ν`-a.e. `x` and
`g ∘ F = g̃ ∘ F` `ν`-a.e.; hence `∫ g ∘ F dν = ∫ g̃ ∘ F dν ≤ ∫ g̃ dμ = ∫ g dμ`. -/
theorem any_radius_gr_ht_ae_transfer : ∀ (n ℓ : ℕ) (ν : Measure (Rn n)) (μ : Measure (Amb n ℓ)) (F : Rn n → Amb n ℓ), AEMeasurable F ν → (∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x, g (F x) ∂ν ≤ ∫⁻ y, g y ∂μ) → ∀ g : Amb n ℓ → ℝ≥0∞, AEMeasurable g μ → ∫⁻ x, g (F x) ∂ν ≤ ∫⁻ y, g y ∂μ := by
  intro n ℓ ν μ F hF hE g hg
  -- Step 1: a Borel version `g̃ = hg.mk g` of `g`; the set `N = {g ≠ g̃}` is `μ`-null.
  set N : Set (Amb n ℓ) := {y | g y ≠ hg.mk g y}
  have hN : μ N = 0 := ae_iff.mp hg.ae_eq_mk
  -- Step 2: the measurable hull `N' ⊇ N` is measurable and `μ`-null.
  set N' : Set (Amb n ℓ) := toMeasurable μ N
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable μ N
  have hN'0 : μ N' = 0 := (measure_toMeasurable N).trans hN
  -- Step 3: (E) at the Borel indicator `1_{N'}` gives `∫ 1_{N'} ∘ F dν ≤ μ N' = 0`.
  have hind : Measurable (N'.indicator (1 : Amb n ℓ → ℝ≥0∞)) := measurable_one.indicator hN'm
  have h0 : ∫⁻ x, N'.indicator 1 (F x) ∂ν = 0 :=
    nonpos_iff_eq_zero.mp <| calc
      ∫⁻ x, N'.indicator 1 (F x) ∂ν ≤ ∫⁻ y, N'.indicator 1 y ∂μ := hE _ hind
      _ = μ N' := lintegral_indicator_one hN'm
      _ = 0 := hN'0
  -- Step 4: `1_{N'} ∘ F` is `ν`-a.e.-measurable with zero integral, so it vanishes `ν`-a.e.
  have hae : (fun x => N'.indicator (1 : Amb n ℓ → ℝ≥0∞) (F x)) =ᵐ[ν] 0 :=
    (lintegral_eq_zero_iff' (hind.comp_aemeasurable' hF)).mp h0
  -- Step 5: so `F x ∉ N' ⊇ N`, i.e. `g (F x) = g̃ (F x)`, for `ν`-a.e. `x`.
  have hgF : (fun x => g (F x)) =ᵐ[ν] fun x => hg.mk g (F x) := by
    filter_upwards [hae] with x hx
    by_contra hne
    have hmem : F x ∈ N' := subset_toMeasurable μ N hne
    simp [Set.indicator_of_mem hmem] at hx
  -- Step 6: `∫ g ∘ F dν = ∫ g̃ ∘ F dν ≤ ∫ g̃ dμ = ∫ g dμ`.
  calc ∫⁻ x, g (F x) ∂ν = ∫⁻ x, hg.mk g (F x) ∂ν := lintegral_congr_ae hgF
    _ ≤ ∫⁻ y, hg.mk g y ∂μ := hE _ hg.measurable_mk
    _ = ∫⁻ y, g y ∂μ := lintegral_congr_ae hg.ae_eq_mk.symm

end Submission
/-- **Pointwise conical height bound at a graph point of small slope** (steps 4–5 of the height
transfer for Simon's Remark 5.3).  Let `‖A‖ ≤ 1/7`, `|b| ≤ |x|/7`, let `P` fix `q(x, A x)` and
satisfy `|w| ≤ (1 + ‖A‖²)^{1/2} |q(0, w) − P q(0, w)|` for all `w`.  Then, with `Y = q(x, b)`,
`|b − A x|² / |x|^{n+2} ≤ 2^{n+4} |Y − P Y|² / |Y|^{n+2}` (real division by `0` gives `0`). -/
theorem Submission.any_radius_gr_ht_pointwise_height : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (P : Amb n ℓ →L[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (b : Rn ℓ), ‖A‖ ≤ 1 / 7 → ‖b‖ ≤ ‖x‖ / 7 → P (q (graphPoint x (A x))) = q (graphPoint x (A x)) → (∀ w : Rn ℓ, ‖w‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖q (graphPoint (0 : Rn n) w) - P (q (graphPoint (0 : Rn n) w))‖) → ‖b - A x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ 2 ^ (n + 4) * (‖q (graphPoint x b) - P (q (graphPoint x b))‖ ^ 2 / ‖q (graphPoint x b)‖ ^ (n + 2)) := by
  intro n ℓ q P A x b hA hb hT hN
  -- (G1) `graphPoint` is additive in both arguments
  have hadd : ∀ (a a' : Rn n) (c c' : Rn ℓ),
      graphPoint (a + a') (c + c') = graphPoint a c + graphPoint a' c' := by
    intro a a' c c'
    ext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [graphPoint]
    · simp [graphPoint]
  -- (G4) `|graphPoint(a, c)|² = |a|² + |c|²`
  have hsq : ∀ (a : Rn n) (c : Rn ℓ), ‖graphPoint a c‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    intro a c
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  set Y := q (graphPoint x b) with hY
  have hRHS : 0 ≤ 2 ^ (n + 4) * (‖Y - P Y‖ ^ 2 / ‖Y‖ ^ (n + 2)) := by positivity
  rcases eq_or_ne x 0 with rfl | hx
  · -- `|x|^(n+2) = 0`, so the left side is `0`
    rw [norm_zero, zero_pow (by omega), div_zero]
    exact hRHS
  -- (a) `Y = q(graphPoint(x, A x)) + q(graphPoint(0, w))` with `w = b - A x`
  have hdec : graphPoint x b = graphPoint x (A x) + graphPoint (0 : Rn n) (b - A x) := by
    have h := hadd x 0 (A x) (b - A x)
    rwa [add_zero, add_sub_cancel] at h
  -- (b) `Y - P Y = y_w - P y_w`
  have hres : Y - P Y =
      q (graphPoint (0 : Rn n) (b - A x)) - P (q (graphPoint (0 : Rn n) (b - A x))) := by
    rw [hY, hdec, map_add, map_add, hT]
    abel
  -- (c) `|w| ≤ 2 |Y - P Y|`, hence `|w|² ≤ 4 |Y - P Y|²`
  have hsqrt : Real.sqrt (1 + ‖A‖ ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have h0 : 0 ≤ ‖A‖ := norm_nonneg A
    nlinarith
  have hw2 : ‖b - A x‖ ≤ 2 * ‖Y - P Y‖ := by
    rw [hres]
    exact (hN (b - A x)).trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
  have hw4 : ‖b - A x‖ ^ 2 ≤ 4 * ‖Y - P Y‖ ^ 2 := by
    calc ‖b - A x‖ ^ 2 ≤ (2 * ‖Y - P Y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw2 2
      _ = 4 * ‖Y - P Y‖ ^ 2 := by ring
  -- (d) `|Y|² = |x|² + |b|²`, so `|x| ≤ |Y| ≤ 2 |x|`
  have hYsq : ‖Y‖ ^ 2 = ‖x‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [hY, LinearIsometryEquiv.norm_map, hsq]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxY : ‖x‖ ≤ ‖Y‖ := by
    refine (sq_le_sq₀ (norm_nonneg x) (norm_nonneg Y)).mp ?_
    rw [hYsq]
    nlinarith [sq_nonneg ‖b‖]
  have hY2x : ‖Y‖ ≤ 2 * ‖x‖ := by
    refine (sq_le_sq₀ (norm_nonneg Y) (by positivity)).mp ?_
    have hb2 : ‖b‖ ^ 2 ≤ (‖x‖ / 7) ^ 2 := pow_le_pow_left₀ (norm_nonneg b) hb 2
    rw [hYsq]
    nlinarith [sq_nonneg ‖x‖]
  have hYpos : 0 < ‖Y‖ := hxpos.trans_le hxY
  -- (e) `|Y|^(n+2) ≤ 2^(n+2) |x|^(n+2)`
  have hpow : ‖Y‖ ^ (n + 2) ≤ 2 ^ (n + 2) * ‖x‖ ^ (n + 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hY2x _
  have hxk : 0 < ‖x‖ ^ (n + 2) := pow_pos hxpos _
  have hYk : 0 < ‖Y‖ ^ (n + 2) := pow_pos hYpos _
  -- (f) combination
  calc ‖b - A x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ 4 * ‖Y - P Y‖ ^ 2 / ‖x‖ ^ (n + 2) :=
        div_le_div_of_nonneg_right hw4 hxk.le
    _ = 2 ^ (n + 4) * ‖Y - P Y‖ ^ 2 / (2 ^ (n + 2) * ‖x‖ ^ (n + 2)) := by
        rw [div_eq_div_iff hxk.ne' (by positivity)]
        ring
    _ ≤ 2 ^ (n + 4) * ‖Y - P Y‖ ^ 2 / ‖Y‖ ^ (n + 2) :=
        div_le_div_of_nonneg_left (by positivity) hYk hpow
    _ = 2 ^ (n + 4) * (‖Y - P Y‖ ^ 2 / ‖Y‖ ^ (n + 2)) := mul_div_assoc _ _ _

namespace Submission

/-- Hilbert–Schmidt facts for maps between Euclidean spaces (`|A|² = hsNormSq A`):
(H1) if `Y` is an adjoint of `X` (`⟨X u, v⟩ = ⟨u, Y v⟩`), then `|Y| = |X|`;
(H2) `|Y X| ≤ ‖Y‖ |X|`; (H3) `|X W| ≤ ‖W‖ |X|` (`‖·‖` the operator norm).
(H1) exchanges the double sum of the entries `(X eᵢ)_j = (Y f_j)_i`; (H2) squares and sums
`|Y (X eᵢ)| ≤ ‖Y‖ |X eᵢ|`; (H3) follows from (H1), (H2) applied to the explicit adjoints
`T* v = Σᵢ ⟨T eᵢ, v⟩ eᵢ`, which satisfy `‖T*‖ ≤ ‖T‖`. -/
theorem any_radius_gr_pp_hs_ideal : (∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (Y : Rn k →L[ℝ] Rn m), (∀ (u : Rn m) (v : Rn k), inner ℝ (X u) v = inner ℝ u (Y v)) → hsNormSq Y = hsNormSq X) ∧ (∀ (m k p : ℕ) (Y : Rn k →L[ℝ] Rn p) (X : Rn m →L[ℝ] Rn k), hsNormSq (Y ∘L X) ≤ ‖Y‖ ^ 2 * hsNormSq X) ∧ ∀ (m k p : ℕ) (X : Rn m →L[ℝ] Rn k) (W : Rn p →L[ℝ] Rn m), hsNormSq (X ∘L W) ≤ ‖W‖ ^ 2 * hsNormSq X := by
  -- Step 2 (H1): the entries are transposed, `(X eᵢ)_j = ⟨X eᵢ, f_j⟩ = ⟨eᵢ, Y f_j⟩ = (Y f_j)_i`;
  -- expand both squared norms in coordinates and exchange the finite double sum.
  have H1 : ∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (Y : Rn k →L[ℝ] Rn m),
      (∀ (u : Rn m) (v : Rn k), inner ℝ (X u) v = inner ℝ u (Y v)) →
        hsNormSq Y = hsNormSq X := by
    intro m k X Y hXY
    have hent : ∀ (i : Fin m) (j : Fin k),
        X (EuclideanSpace.single i 1) j = Y (EuclideanSpace.single j 1) i := by
      intro i j
      have h := hXY (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      rw [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left] at h
      simpa using h
    unfold hsNormSq
    simp_rw [EuclideanSpace.real_norm_sq_eq, hent]
    exact Finset.sum_comm
  -- Step 3 (H2): `|Y (X eᵢ)| ≤ ‖Y‖ |X eᵢ|`; square and sum over `i`.
  have H2 : ∀ (m k p : ℕ) (Y : Rn k →L[ℝ] Rn p) (X : Rn m →L[ℝ] Rn k),
      hsNormSq (Y ∘L X) ≤ ‖Y‖ ^ 2 * hsNormSq X := by
    intro m k p Y X
    unfold hsNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (Y.le_opNorm _) 2
  -- Step 4: every `T : ℝᵃ → ℝᵇ` has the adjoint `T* v = Σᵢ ⟨T eᵢ, v⟩ eᵢ`, with `‖T*‖ ≤ ‖T‖`.
  have adj : ∀ (a b : ℕ) (T : Rn a →L[ℝ] Rn b), ∃ T' : Rn b →L[ℝ] Rn a,
      (∀ (u : Rn a) (v : Rn b), inner ℝ (T u) v = inner ℝ u (T' v)) ∧ ‖T'‖ ≤ ‖T‖ := by
    intro a b T
    let T' : Rn b →L[ℝ] Rn a := ∑ i : Fin a,
      (innerSL ℝ (T (EuclideanSpace.single i 1))).smulRight (EuclideanSpace.single i (1 : ℝ))
    -- `⟨T u, v⟩ = Σᵢ uᵢ ⟨T eᵢ, v⟩ = ⟨u, T* v⟩`, writing `u = Σᵢ uᵢ eᵢ`.
    have hT' : ∀ (u : Rn a) (v : Rn b), inner ℝ (T u) v = inner ℝ u (T' v) := by
      intro u v
      have hu : ∑ i, u i • EuclideanSpace.single i (1 : ℝ) = u := by
        simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
          (EuclideanSpace.basisFun (Fin a) ℝ).sum_repr u
      conv_lhs => rw [← hu]
      simp only [T', sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        EuclideanSpace.inner_single_right, one_mul, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    -- `|T* v|² = ⟨T (T* v), v⟩ ≤ ‖T‖ |T* v| |v|`, hence `|T* v| ≤ ‖T‖ |v|`.
    refine ⟨T', hT', T'.opNorm_le_bound (norm_nonneg T) fun v => ?_⟩
    have h1 : ‖T' v‖ ^ 2 ≤ ‖T‖ * ‖v‖ * ‖T' v‖ := by
      calc ‖T' v‖ ^ 2 = inner ℝ (T' v) (T' v) := (real_inner_self_eq_norm_sq _).symm
        _ = inner ℝ (T (T' v)) v := (hT' _ _).symm
        _ ≤ ‖T (T' v)‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖T' v‖ * ‖v‖ := by gcongr; exact T.le_opNorm _
        _ = ‖T‖ * ‖v‖ * ‖T' v‖ := by ring
    nlinarith [norm_nonneg (T' v), mul_nonneg (norm_nonneg T) (norm_nonneg v)]
  refine ⟨H1, H2, ?_⟩
  -- Step 5 (H3): `X ∘ W` has adjoint `W* ∘ X*`, so by (H1), (H2), (H1):
  -- `|X W|² = |W* X*|² ≤ ‖W*‖² |X*|² ≤ ‖W‖² |X*|² = ‖W‖² |X|²`.
  intro m k p X W
  obtain ⟨X', hX', -⟩ := adj m k X
  obtain ⟨W', hW', hW'n⟩ := adj p m W
  have ha : hsNormSq (W' ∘L X') = hsNormSq (X ∘L W) := by
    apply H1
    intro u v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hX', hW']
  have hb : hsNormSq X' = hsNormSq X := H1 m k X X' hX'
  have hX'nn : 0 ≤ hsNormSq X' := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc hsNormSq (X ∘L W) = hsNormSq (W' ∘L X') := ha.symm
    _ ≤ ‖W'‖ ^ 2 * hsNormSq X' := H2 k m p W' X'
    _ ≤ ‖W‖ ^ 2 * hsNormSq X' :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hW'n 2) hX'nn
    _ = ‖W‖ ^ 2 * hsNormSq X := by rw [hb]

/-- Hilbert–Schmidt splitting along orthogonal projections, with `|A|² = Σᵢ |A eᵢ|²` (`hsNormSq`).
(S1) For `X : ℝᵐ → ℝᵏ` and a subspace `K`, `|X|² = |X p_K|² + |X p_{K⊥}|²`.
(S2) For subspaces `K, L`, with `P = p_K` and `Q = p_L`, `|P − Q|² = |(P − Q) P|² + |(P − Q) Q|²`.
Proof: (S1) Let `X* v = Σᵢ ⟨X eᵢ, v⟩ eᵢ` be the adjoint of `X`.  As `p_W` is self-adjoint,
`p_W X*` is an adjoint of `X p_W`, so adjoint invariance of `|·|` (first conjunct of
`any_radius_gr_pp_hs_ideal`) gives `|X p_W|² = |p_W X*|²` and `|X|² = |X*|²`; summing Pythagoras
`|X* f_j|² = |p_K X* f_j|² + |p_{K⊥} X* f_j|²` over the standard basis `(f_j)` of `ℝᵏ` gives (S1).
(S2) By (S1) for `X = P − Q`, it remains to show `|(P − Q) p_{K⊥}|² = |(P − Q) Q|²`.  Since
`p_{K⊥} = 1 − P`, `P² = P`, `Q² = Q` and `P, Q` are self-adjoint, `(P − Q) Q` is an adjoint of
`(P − Q) p_{K⊥}`; apply adjoint invariance again. -/
theorem any_radius_gr_pp_hs_proj_split : (∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (K : Submodule ℝ (Rn m)), hsNormSq X = hsNormSq (X ∘L K.starProjection) + hsNormSq (X ∘L Kᗮ.starProjection)) ∧ ∀ (m : ℕ) (K L : Submodule ℝ (Rn m)), hsNormSq (K.starProjection - L.starProjection) = hsNormSq ((K.starProjection - L.starProjection) ∘L K.starProjection) + hsNormSq ((K.starProjection - L.starProjection) ∘L L.starProjection) := by
  -- (H1): an adjoint pair `X, Y` has `hsNormSq Y = hsNormSq X`.
  have H1 := Submission.any_radius_gr_pp_hs_ideal.1
  have S1 : ∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (K : Submodule ℝ (Rn m)),
      hsNormSq X = hsNormSq (X ∘L K.starProjection) + hsNormSq (X ∘L Kᗮ.starProjection) := by
    intro m k X K
    -- 0(e): `X* v = Σᵢ ⟨X eᵢ, v⟩ eᵢ` is an adjoint of `X`, as `⟨X u, v⟩ = Σᵢ uᵢ ⟨X eᵢ, v⟩`.
    obtain ⟨Xa, hXa⟩ : ∃ Xa : Rn k →L[ℝ] Rn m, ∀ (u : Rn m) (v : Rn k),
        inner ℝ (X u) v = inner ℝ u (Xa v) := by
      refine ⟨∑ i : Fin m, (innerSL ℝ (X (EuclideanSpace.single i 1))).smulRight
        (EuclideanSpace.single i (1 : ℝ)), fun u v => ?_⟩
      have hu : ∑ i, u i • EuclideanSpace.single i (1 : ℝ) = u := by
        simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
          (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr u
      conv_lhs => rw [← hu]
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        EuclideanSpace.inner_single_right, one_mul, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hX : hsNormSq Xa = hsNormSq X := H1 m k X Xa hXa
    -- `p_W X*` is an adjoint of `X p_W`.
    have hW : ∀ (W : Submodule ℝ (Rn m)) [W.HasOrthogonalProjection],
        hsNormSq (W.starProjection ∘L Xa) = hsNormSq (X ∘L W.starProjection) := by
      intro W _
      refine H1 m k (X ∘L W.starProjection) (W.starProjection ∘L Xa) fun u v => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hXa,
        Submodule.inner_starProjection_left_eq_right]
    -- Pythagoras on each column `X* f_j`.
    rw [← hW K, ← hW Kᗮ, ← hX]
    unfold hsNormSq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection _ K
  refine ⟨S1, fun m K L => ?_⟩
  rw [S1 m m (K.starProjection - L.starProjection) K]
  congr 1
  -- `(P − Q) Q` is an adjoint of `(P − Q) p_{K⊥}`.
  refine (H1 m m ((K.starProjection - L.starProjection) ∘L Kᗮ.starProjection)
    ((K.starProjection - L.starProjection) ∘L L.starProjection) fun u v => ?_).symm
  have hP : K.starProjection (K.starProjection u) = K.starProjection u :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem u)
  have hQ : L.starProjection (L.starProjection v) = L.starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (L.starProjection_apply_mem v)
  have hQu : inner ℝ (L.starProjection u) v = inner ℝ u (L.starProjection v) :=
    L.inner_starProjection_left_eq_right u v
  have hQPu : inner ℝ (L.starProjection (K.starProjection u)) v =
      inner ℝ u (K.starProjection (L.starProjection v)) := by
    rw [L.inner_starProjection_left_eq_right, K.inner_starProjection_left_eq_right]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, Submodule.starProjection_orthogonal_val,
    map_sub, inner_sub_left, inner_sub_right, hP, hQ, hQu, hQPu]
  ring
/-- Graph parametrization of a rotated graph plane (plane projections in the graph-rate step of the
proof of Simon Ch. 5, Remark 5.3).  Let `q` be a linear isometry of `ℝ^{n+ℓ}`, `A : ℝⁿ → ℝ^ℓ`
continuous linear, `G_A = q(span{(v, A v) : v ∈ ℝⁿ})` and `P_A` the orthogonal projection onto
`G_A` (`‖A‖` the operator norm).  Then
(P1) `P_A q(x, A x) = q(x, A x)`;
(P2) `|w| ≤ (1 + ‖A‖²)^{1/2} |q(0, w) − P_A q(0, w)|`;
(W) `v ↦ q(v, A v)` is continuous linear with operator norm `≤ (1 + ‖A‖²)^{1/2}`;
(D) `q(v, A v) − q(v, B v) = q(0, (A − B) v)`.
Since `v ↦ (v, A v)` is linear, `G_A = {q(v, A v) : v ∈ ℝⁿ}`; (P2) and (W) follow from
`|(a, b)|² = |a|² + |b|²`, `|A v| ≤ ‖A‖ |v|` and `(a + c b)² ≤ (1 + c²)(a² + b²)`. -/
theorem any_radius_gr_pp_graph_param : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n), (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection (q (graphPoint x (A x))) = q (graphPoint x (A x))) ∧ (∀ (A : Rn n →L[ℝ] Rn ℓ) (w : Rn ℓ), ‖w‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖q (graphPoint (0 : Rn n) w) - (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection (q (graphPoint (0 : Rn n) w))‖) ∧ (∀ A : Rn n →L[ℝ] Rn ℓ, ∃ W : Rn n →L[ℝ] Amb n ℓ, (∀ v : Rn n, W v = q (graphPoint v (A v))) ∧ ‖W‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2)) ∧ ∀ (A B : Rn n →L[ℝ] Rn ℓ) (v : Rn n), q (graphPoint v (A v)) - q (graphPoint v (B v)) = q (graphPoint (0 : Rn n) ((A - B) v)) := by
  intro n ℓ q
  -- Coordinates of `graphPoint a b` and the resulting algebra (G1)–(G4).
  have hL : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hR : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  have hext : ∀ z z' : Amb n ℓ, (∀ i : Fin n, z (Fin.castAdd ℓ i) = z' (Fin.castAdd ℓ i)) →
      (∀ j : Fin ℓ, z (Fin.natAdd n j) = z' (Fin.natAdd n j)) → z = z' := by
    intro z z' h1 h2
    ext k
    exact Fin.addCases (fun i => h1 i) (fun j => h2 j) k
  have G1 : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b' := by
    intro a a' b b'
    apply hext <;> intro i <;> simp [hL, hR]
  have G2 : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b' := by
    intro a a' b b'
    apply hext <;> intro i <;> simp [hL, hR]
  have G3 : ∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b := by
    intro t a b
    apply hext <;> intro i <;> simp [hL, hR]
  have G4 : ∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]
    simp only [hL, hR]
  -- `g_A v = graphPoint v (A v)` is linear, so `span (range g_A) = range g_A` and every element of
  -- `G_A` is `q (graphPoint v (A v))` for some `v`.
  let g : (Rn n →L[ℝ] Rn ℓ) → Rn n →ₗ[ℝ] Amb n ℓ := fun A =>
    { toFun := fun v => graphPoint v (A v)
      map_add' := fun v v' => by simp only [map_add]; exact G1 _ _ _ _
      map_smul' := fun t v => by simp only [map_smul, RingHom.id_apply]; exact G3 _ _ _ }
  have hspan : ∀ A : Rn n →L[ℝ] Rn ℓ,
      Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)) = LinearMap.range (g A) := by
    intro A
    have h : (Set.range fun v : Rn n => graphPoint v (A v)) =
        (LinearMap.range (g A) : Set (Amb n ℓ)) := by
      rw [LinearMap.coe_range]
      rfl
    rw [h, Submodule.span_eq]
  have hmem : ∀ (A : Rn n →L[ℝ] Rn ℓ) (z : Amb n ℓ),
      z ∈ Submodule.map q.toLinearEquiv.toLinearMap
        (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))) →
      ∃ v, z = q (graphPoint v (A v)) := by
    intro A z hz
    rw [hspan A, Submodule.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
    exact ⟨v, rfl⟩
  refine ⟨fun A x => ?_, fun A w => ?_, fun A => ?_, fun A B v => ?_⟩
  · -- (P1): `q (graphPoint x (A x)) ∈ G_A` is fixed by the projection onto `G_A`.
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, rfl⟩)
  · -- (P2): `P_A y = q (graphPoint v (A v))`, so `|y - P_A y|² = |v|² + |w - A v|²`; then
    -- `|w| ≤ |w - A v| + ‖A‖ |v|` and `(a + c b)² ≤ (1 + c²)(a² + b²)`.
    obtain ⟨v, hv⟩ := hmem A _ (Submodule.starProjection_apply_mem _ (q (graphPoint 0 w)))
    rw [hv, ← map_sub, ← G2, LinearIsometryEquiv.norm_map]
    have hN : ‖graphPoint (0 - v) (w - A v)‖ ^ 2 = ‖v‖ ^ 2 + ‖w - A v‖ ^ 2 := by
      rw [G4, zero_sub, norm_neg]
    have hw : ‖w‖ ≤ ‖w - A v‖ + ‖A‖ * ‖v‖ := by
      calc ‖w‖ = ‖(w - A v) + A v‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - A v‖ + ‖A v‖ := norm_add_le _ _
        _ ≤ ‖w - A v‖ + ‖A‖ * ‖v‖ := by gcongr; exact A.le_opNorm v
    refine hw.trans ?_
    have key : (‖w - A v‖ + ‖A‖ * ‖v‖) ^ 2 ≤
        (Real.sqrt (1 + ‖A‖ ^ 2) * ‖graphPoint (0 - v) (w - A v)‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hN]
      nlinarith [sq_nonneg (‖A‖ * ‖w - A v‖ - ‖v‖)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key
  · -- (W): `W = q ∘ g_A`, with `|W v|² = |v|² + |A v|² ≤ (1 + ‖A‖²) |v|²`.
    let Wl : Rn n →ₗ[ℝ] Amb n ℓ := q.toLinearEquiv.toLinearMap ∘ₗ g A
    refine ⟨LinearMap.toContinuousLinearMap Wl, fun v => rfl, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
    show ‖q (graphPoint v (A v))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    have hb : ‖graphPoint v (A v)‖ ^ 2 ≤ (Real.sqrt (1 + ‖A‖ ^ 2) * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), G4]
      have h2 : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      have h3 : ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [h3]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hb
  · -- (D): linearity of `q` and (G2), with `v - v = 0` and `(A - B) v = A v - B v`.
    rw [← map_sub, ← G2, sub_self, sub_apply]

/-- Key inequality between graph slopes and plane projections (plane projections in the graph-rate
step of the proof of Simon Ch. 5, Remark 5.3).  Let `q` be a linear isometry of `ℝ^{n+ℓ}`,
`A, B : ℝⁿ → ℝ^ℓ` continuous linear and `P_A`, `P_B` the orthogonal projections onto
`G_A = q(span{(v, A v)})`, `G_B = q(span{(v, B v)})`.  Then, with `|·|² = hsNormSq` and `‖·‖` the
operator norm, `2 |A − B|² ≤ (1 + ‖A‖²)(1 + ‖B‖²) |P_A − P_B|²`.
Proof: for an ordered pair `(C, D)` let `W v = q(v, C v)`, so `‖W‖² ≤ 1 + ‖C‖²` by (W).
With `y = q(0, (C − D) eᵢ)`, (P1) and (D) of `any_radius_gr_pp_graph_param` give
`(P_C − P_D) W eᵢ = y − P_D y`, so (P2) gives `|(C − D) eᵢ|² ≤ (1 + ‖D‖²) |(P_C − P_D) W eᵢ|²`.
As `(P_C − P_D) W = ((P_C − P_D) P_C) W`, (H3) of `any_radius_gr_pp_hs_ideal` yields
`|C − D|² ≤ (1 + ‖C‖²)(1 + ‖D‖²) |(P_C − P_D) P_C|²`.  Apply this to `(A, B)` and `(B, A)`
(`|·|` is invariant under negation) and add, using (S2) of `any_radius_gr_pp_hs_proj_split`. -/
theorem any_radius_gr_pp_key_inequality : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A B : Rn n →L[ℝ] Rn ℓ), 2 * hsNormSq (A - B) ≤ (1 + ‖A‖ ^ 2) * (1 + ‖B‖ ^ 2) * hsNormSq ((Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection - (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v)))).starProjection) := by
  intro n ℓ q A B
  -- (P1), (P2), (W), (D) of the graph parametrization, and (H3).
  obtain ⟨hP1, hP2, hW, hD⟩ := Submission.any_radius_gr_pp_graph_param n ℓ q
  have H3 := Submission.any_radius_gr_pp_hs_ideal.2.2
  -- 0(a) `hsNormSq M ≥ 0` and 0(b) `hsNormSq (-M) = hsNormSq M`.
  have hnn : ∀ {m k : ℕ} (M : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq M :=
    fun M => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hneg : ∀ {m k : ℕ} (M : Rn m →L[ℝ] Rn k), hsNormSq (-M) = hsNormSq M := by
    intro m k M
    unfold hsNormSq
    simp only [neg_apply, norm_neg]
  -- Step 1: `|C − D|² ≤ (1 + ‖C‖²)(1 + ‖D‖²) |(P_C − P_D) P_C|²` for every ordered pair `(C, D)`.
  have one : ∀ C D : Rn n →L[ℝ] Rn ℓ, hsNormSq (C - D) ≤ (1 + ‖C‖ ^ 2) * (1 + ‖D‖ ^ 2) *
      hsNormSq (((Submodule.map q.toLinearEquiv.toLinearMap
          (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (C v)))).starProjection -
        (Submodule.map q.toLinearEquiv.toLinearMap
          (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (D v)))).starProjection) ∘L
        (Submodule.map q.toLinearEquiv.toLinearMap
          (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (C v)))).starProjection) := by
    intro C D
    obtain ⟨W, hWv, hWn⟩ := hW C
    have P1C := hP1 C
    have P1D := hP1 D
    have P2D := hP2 D
    have hCD := hD C D
    generalize (Submodule.map q.toLinearEquiv.toLinearMap
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (C v)))).starProjection = PC at P1C ⊢
    generalize (Submodule.map q.toLinearEquiv.toLinearMap
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (D v)))).starProjection = PD
      at P1D P2D ⊢
    -- `‖W‖² ≤ 1 + ‖C‖²`.
    have hWsq : ‖W‖ ^ 2 ≤ 1 + ‖C‖ ^ 2 := by
      calc ‖W‖ ^ 2 ≤ Real.sqrt (1 + ‖C‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hWn 2
        _ = 1 + ‖C‖ ^ 2 := Real.sq_sqrt (by positivity)
    -- (i): `(P_C − P_D) (W v) = y − P_D y` with `y = q (graphPoint 0 ((C − D) v))`.
    have hZW : ∀ v, ((PC - PD) ∘L W) v =
        q (graphPoint 0 ((C - D) v)) - PD (q (graphPoint 0 ((C - D) v))) := by
      intro v
      have e1 : W v = q (graphPoint v (D v)) + q (graphPoint 0 ((C - D) v)) := by
        rw [hWv, ← hCD v, add_sub_cancel]
      rw [ContinuousLinearMap.comp_apply, sub_apply, hWv, P1C v, ← hWv, e1, map_add, P1D v]
      abel
    -- (ii): `|(C − D) eᵢ|² ≤ (1 + ‖D‖²) |(P_C − P_D) (W eᵢ)|²` by (P2) for `D`; sum over `i`.
    have hii : hsNormSq (C - D) ≤ (1 + ‖D‖ ^ 2) * hsNormSq ((PC - PD) ∘L W) := by
      unfold hsNormSq
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h := P2D ((C - D) (EuclideanSpace.single i 1))
      rw [← hZW] at h
      calc ‖(C - D) (EuclideanSpace.single i 1)‖ ^ 2
          ≤ (Real.sqrt (1 + ‖D‖ ^ 2) * ‖((PC - PD) ∘L W) (EuclideanSpace.single i 1)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (1 + ‖D‖ ^ 2) * ‖((PC - PD) ∘L W) (EuclideanSpace.single i 1)‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
    -- (iii): `(P_C − P_D) W = ((P_C − P_D) P_C) W` by (P1) for `C`, then (H3).
    have hiii : hsNormSq ((PC - PD) ∘L W) ≤ (1 + ‖C‖ ^ 2) * hsNormSq ((PC - PD) ∘L PC) := by
      have hfac : (PC - PD) ∘L W = ((PC - PD) ∘L PC) ∘L W := by
        ext1 v
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.comp_apply, hWv, P1C v]
      rw [hfac]
      exact (H3 _ _ _ _ W).trans (mul_le_mul_of_nonneg_right hWsq (hnn _))
    -- (iv): combine (ii) and (iii).
    calc hsNormSq (C - D) ≤ (1 + ‖D‖ ^ 2) * hsNormSq ((PC - PD) ∘L W) := hii
      _ ≤ (1 + ‖D‖ ^ 2) * ((1 + ‖C‖ ^ 2) * hsNormSq ((PC - PD) ∘L PC)) :=
          mul_le_mul_of_nonneg_left hiii (by positivity)
      _ = (1 + ‖C‖ ^ 2) * (1 + ‖D‖ ^ 2) * hsNormSq ((PC - PD) ∘L PC) := by ring
  -- 0(b) in the two forms used in step 3.
  have hswap : ∀ {m k : ℕ} (M N : Rn m →L[ℝ] Rn k), hsNormSq (M - N) = hsNormSq (N - M) := by
    intro m k M N
    rw [← neg_sub, hneg]
  have hswap' : ∀ {m : ℕ} (M N K : Rn m →L[ℝ] Rn m),
      hsNormSq ((M - N) ∘L K) = hsNormSq ((N - M) ∘L K) := by
    intro m M N K
    rw [← neg_sub, ContinuousLinearMap.neg_comp, hneg]
  -- Step 2: `(C, D) = (A, B)`.
  have h1 := one A B
  -- Step 3: `(C, D) = (B, A)`, with `B − A = −(A − B)` and `(P_B − P_A) P_B = −((P_A − P_B) P_B)`.
  have h2 := one B A
  rw [hswap B A, hswap'] at h2
  -- Step 4: (S2) for `K = G_A`, `L = G_B`; add the bounds of steps 2 and 3.
  rw [Submission.any_radius_gr_pp_hs_proj_split.2 (n + ℓ)]
  linarith
/-- Graph coordinates on `ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ`, used for the graph estimates behind Simon Ch. 5,
Remark 5.3 (p. 122): the point `(a, b) = graphPoint a b` has coordinate `a_i` at `castAdd ℓ i` and
`b_j` at `natAdd n j`; `(a, b)` is linear in the pair; `|(a, b)|² = |a|² + |b|²`; and
`⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`.
Every index of `Fin (n + ℓ)` is `castAdd ℓ i` or `natAdd n j` (`Fin.addCases`), so the linearity
identities hold coordinatewise, and the norm and the inner product split as sums over the two
blocks of indices (`Fin.sum_univ_add`). -/
theorem any_radius_gr_la_graphPoint_algebra : ∀ (n ℓ : ℕ), (∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i) ∧ (∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b') ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b') ∧ (∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b') := by
  intro n ℓ
  -- (C1), (C2): the coordinates of `graphPoint a b = toLp (Fin.append a b)`
  have hC1 : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_left]
  have hC2 : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_right]
  refine ⟨hC1, hC2, ?_, ?_, ?_, ?_, ?_⟩
  -- (L1)–(L3): compare the coordinates at every `castAdd ℓ i` and every `natAdd n j`
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.add_apply, hC1]
    · simp only [PiLp.add_apply, hC2]
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hC1]
    · simp only [PiLp.sub_apply, hC2]
  · intro t a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.smul_apply, hC1]
    · simp only [PiLp.smul_apply, hC2]
  -- (L4): split `‖x‖² = Σ_k ‖x_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hC1, hC2]
  -- (IP): split `⟪x, y⟫ = Σ_k ⟪x_k, y_k⟫` in the same way
  · intro a a' b b'
    rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
    simp only [hC1, hC2]
/-- The rotated plane `T₀ = q(ℝⁿ × {0})` of Simon Ch. 5, Lemma 2.6 (p. 110), in the graph estimates
behind Remark 5.3 (p. 122): for a linear isometry `q` of `ℝ^{n+ℓ}`, (L5) `p_{T₀}(q(a, b)) = q(a, 0)`,
(L6) `dist(q(a, b), T₀) = |b|` and (L7) `dim T₀ = n`.
Since `e_{castAdd ℓ i} = (eᵢ, 0)` and `c ↦ (c, 0)` is linear, `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, which
is orthogonal to `(0, b)`; as `q` preserves inner products, `q(a, 0) ∈ T₀` and
`q(a, b) − q(a, 0) = q(0, b) ⊥ T₀` characterize the projection, and the distance to `T₀` is attained
at the projection.  The `e_{castAdd ℓ i}` are independent and `q` preserves dimension. -/
theorem any_radius_gr_la_rotatedPlane_facts : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ))) ∧ (∀ (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖) ∧ Module.finrank ℝ (rotatedPlane q) = n := by
  intro n ℓ q
  -- (C1), (C2), (L1)–(L4) and (IP) for `graphPoint`
  obtain ⟨hC1, hC2, hadd, hsub, hsmul, hnorm, hinner⟩ :=
    Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  -- Step 1: `e_{castAdd ℓ i} = (eᵢ, 0)`; compare the coordinates at `castAdd ℓ i'` and `natAdd n j`
  have hbasis : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) =
      graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
    · rw [hC1]
      simp only [PiLp.single_apply, (Fin.castAdd_injective n ℓ).eq_iff]
    · rw [hC2]
      have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ i := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
  -- Step 2: `G c = (c, 0)` is linear, by (L1) and (L3)
  let G : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun c => graphPoint c (0 : Rn ℓ)
      map_add' := fun c c' => by simpa using hadd c c' (0 : Rn ℓ) (0 : Rn ℓ)
      map_smul' := fun t c => by simpa using hsmul t c (0 : Rn ℓ) }
  -- Step 3: `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, the image under `G` of the span of the `eᵢ`
  have hhor : horizontalPlane n ℓ = LinearMap.range G := by
    have hfun : (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) =
        G ∘ fun i : Fin n => EuclideanSpace.single i (1 : ℝ) := by
      funext i
      exact hbasis i
    have hspan :
        Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
      have hb : ⇑(EuclideanSpace.basisFun (Fin n) ℝ) = fun i => EuclideanSpace.single i (1 : ℝ) :=
        funext (EuclideanSpace.basisFun_apply (Fin n) ℝ)
      have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
      rwa [OrthonormalBasis.coe_toBasis, hb] at this
    rw [horizontalPlane, hfun, Set.range_comp, Submodule.span_image, hspan,
      LinearMap.range_eq_map]
  -- Step 4: `(0, b)` is orthogonal to `ℝⁿ × {0}`, by (IP)
  have horth : ∀ (b : Rn ℓ), ∀ h ∈ horizontalPlane n ℓ,
      inner ℝ (graphPoint (0 : Rn n) b) h = 0 := by
    intro b h hh
    rw [hhor] at hh
    obtain ⟨c, rfl⟩ := hh
    show inner ℝ (graphPoint 0 b) (graphPoint c 0) = 0
    rw [hinner]
    simp
  -- Step 6(ii): `q(a, b) − q(a, 0) = q(0, b)`, by (L2)
  have hdiff : ∀ (a : Rn n) (b : Rn ℓ),
      q (graphPoint a b) - q (graphPoint a 0) = q (graphPoint 0 b) := by
    intro a b
    rw [← map_sub, ← hsub]
    simp
  -- Step 6, (L5): `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) ⊥ T₀`, as `q` preserves inner products
  have hproj : ∀ (a : Rn n) (b : Rn ℓ),
      (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ)) := by
    intro a b
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (by rw [hhor]; exact ⟨a, rfl⟩)
    · intro w hw
      obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
      rw [hdiff]
      simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
      rw [LinearIsometryEquiv.inner_map_map]
      exact horth b h hh
  refine ⟨hproj, ?_, ?_⟩
  -- Step 8, (L6): `dist(v, T₀) = |v − p_{T₀} v| = |q(0, b)| = |(0, b)| = |b|`, by (L5) and (L4)
  · intro a b
    rw [← Submodule.dist_starProjection_eq_infDist, hproj, dist_eq_norm, hdiff,
      LinearIsometryEquiv.norm_map]
    have h := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- Step 9, (L7): the `e_{castAdd ℓ i}` are independent, and `q` preserves `finrank`
  · have hli : LinearIndependent ℝ
        (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) :=
      (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + ℓ))).linearIndependent.comp _
        (Fin.castAdd_injective n ℓ)
    rw [rotatedPlane, LinearEquiv.finrank_map_eq, horizontalPlane, finrank_span_eq_card hli,
      Fintype.card_fin]
/-- Basic facts about the Hilbert–Schmidt norm `|M| = (Σᵢ |M eᵢ|²)^{1/2}` of `M : ℝᵐ →L ℝᵏ`
(Simon, Notation p. ix): `0 ≤ |M|²`, `|M| ^ 2 = |M|²`, `|M + N|² ≤ 2 |M|² + 2 |N|²`,
`|-M|² = |M|²`, `|M|² = 0 ⇒ M = 0` and `‖M‖ ≤ |M| ≤ √m ‖M‖`; moreover the orthogonal projection
`P_K` onto any subspace `K ⊆ ℝᵐ` has `|P_K|² ≤ m`.  Proof: termwise estimates on the standard
basis `eᵢ`, the expansion `v = Σᵢ vᵢ eᵢ` with Cauchy–Schwarz for `‖M‖ ≤ |M|`, and
`|P_K eᵢ| ≤ |eᵢ| = 1`. -/
theorem any_radius_gr_la_hsNorm_facts : (∀ (m k : ℕ) (M N : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq M ∧ hsNorm M ^ 2 = hsNormSq M ∧ hsNormSq (M + N) ≤ 2 * hsNormSq M + 2 * hsNormSq N ∧ hsNormSq (-M) = hsNormSq M ∧ (hsNormSq M = 0 → M = 0) ∧ ‖M‖ ≤ hsNorm M ∧ hsNorm M ≤ Real.sqrt m * ‖M‖) ∧ ∀ (m : ℕ) (K : Submodule ℝ (Rn m)), hsNormSq K.starProjection ≤ m := by
  refine ⟨fun m k M N => ?_, fun m K => ?_⟩
  · -- (a) `hsNormSq M` is a finite sum of squares, hence nonnegative.
    have ha : 0 ≤ hsNormSq M := Finset.sum_nonneg fun i _ => sq_nonneg _
    -- Expansion `v = Σᵢ vᵢ eᵢ` in the standard basis `eᵢ = EuclideanSpace.single i 1`.
    have hexp : ∀ v : Rn m, ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := fun v => by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    -- (b) `hsNorm M ^ 2 = √(hsNormSq M) ^ 2 = hsNormSq M`, by (a).
    refine ⟨ha, Real.sq_sqrt ha, ?_, ?_, ?_, ?_, ?_⟩
    · -- (c) termwise `‖(M + N) eᵢ‖² ≤ (‖M eᵢ‖ + ‖N eᵢ‖)² ≤ 2 ‖M eᵢ‖² + 2 ‖N eᵢ‖²`.
      unfold hsNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖(M + N) (EuclideanSpace.single i 1)‖ ≤
          ‖M (EuclideanSpace.single i 1)‖ + ‖N (EuclideanSpace.single i 1)‖ := by
        rw [add_apply]
        exact norm_add_le _ _
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖M (EuclideanSpace.single i 1)‖ - ‖N (EuclideanSpace.single i 1)‖)]
    · -- (d) `‖(-M) eᵢ‖ = ‖-(M eᵢ)‖ = ‖M eᵢ‖` termwise.
      unfold hsNormSq
      simp only [neg_apply, norm_neg]
    · -- (e) every `M eᵢ` vanishes, so `M v = Σᵢ vᵢ M eᵢ = 0` for every `v`.
      intro h0
      have hi : ∀ i, M (EuclideanSpace.single i 1) = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
          sq_nonneg ‖M (EuclideanSpace.single j (1 : ℝ))‖).1 h0 i (Finset.mem_univ i)
        simpa using this
      refine ContinuousLinearMap.ext fun v => ?_
      rw [zero_apply, ← hexp v, map_sum]
      simp [hi]
    · -- (f) `‖M v‖ ≤ Σᵢ |vᵢ| ‖M eᵢ‖ ≤ hsNorm M ‖v‖` (triangle and Cauchy–Schwarz inequalities).
      refine M.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
      calc ‖M v‖ = ‖∑ i, v i • M (EuclideanSpace.single i 1)‖ := by
            conv_lhs => rw [← hexp v]
            simp only [map_sum, map_smul]
        _ ≤ ∑ i, ‖v i‖ * ‖M (EuclideanSpace.single i 1)‖ :=
            (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
        _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖M (EuclideanSpace.single i 1)‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = hsNorm M * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm M)]; rfl
    · -- (g) `‖M eᵢ‖ ≤ ‖M‖ ‖eᵢ‖ = ‖M‖`, so `hsNormSq M ≤ m ‖M‖²`; take square roots.
      have h1 : hsNormSq M ≤ m * ‖M‖ ^ 2 := by
        calc hsNormSq M = ∑ i : Fin m, ‖M (EuclideanSpace.single i 1)‖ ^ 2 := rfl
          _ ≤ ∑ _i : Fin m, ‖M‖ ^ 2 := by
              refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
              simpa using M.le_opNorm (EuclideanSpace.single i (1 : ℝ))
          _ = m * ‖M‖ ^ 2 := by simp
      calc hsNorm M = √(hsNormSq M) := rfl
        _ ≤ √(m * ‖M‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt m * ‖M‖ := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  · -- (L9) `‖P_K eᵢ‖ ≤ ‖eᵢ‖ = 1` (Pythagoras) for each of the `m` basis vectors `eᵢ`.
    calc hsNormSq K.starProjection
        = ∑ i : Fin m, ‖K.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := rfl
      _ ≤ ∑ _i : Fin m, (1 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          simpa using K.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))
      _ = m := by simp
/-- Linear algebra behind the graph-rate step of Simon Ch. 5, Remark 5.3 (p. 122): graph
coordinates on `ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ`, the rotated plane `T₀ = q(ℝⁿ × {0})` of Lemma 2.6 (p. 110), and
the Hilbert–Schmidt norm `|A|` (Notation p. ix; footnote 2 on p. 115).  For a linear isometry `q`:
(L1)–(L3) `(a, b)` is additive, subtractive and homogeneous in the pair; (L4)
`|(a, b)|² = |a|² + |b|²`; (L5) `p_{T₀}(q(a, b)) = q(a, 0)`; (L6) `dist(q(a, b), T₀) = |b|`;
(L7) `dim T₀ = n`; (L8) for `M, N : ℝᵐ → ℝᵏ`: `|M|² ≥ 0`, `|M|² = (|M|)²`,
`|M + N|² ≤ 2|M|² + 2|N|²`, `|−M|² = |M|²`, `|M|² = 0 ⇒ M = 0` and `‖M‖ ≤ |M| ≤ √m ‖M‖`;
(L9) `|p_K|² ≤ m` for every subspace `K ⊆ ℝᵐ`.
(L1)–(L4) are part of the coordinate algebra of `(a, b)`, (L5)–(L7) are the projection, distance and
dimension facts for `T₀`, and (L8), (L9) are the Hilbert–Schmidt facts. -/
theorem any_radius_gr_linear_algebra_basics : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b') ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b') ∧ (∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ))) ∧ (∀ (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖) ∧ Module.finrank ℝ (rotatedPlane q) = n ∧ (∀ (m k : ℕ) (M N : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq M ∧ hsNorm M ^ 2 = hsNormSq M ∧ hsNormSq (M + N) ≤ 2 * hsNormSq M + 2 * hsNormSq N ∧ hsNormSq (-M) = hsNormSq M ∧ (hsNormSq M = 0 → M = 0) ∧ ‖M‖ ≤ hsNorm M ∧ hsNorm M ≤ Real.sqrt m * ‖M‖) ∧ ∀ (m : ℕ) (K : Submodule ℝ (Rn m)), hsNormSq K.starProjection ≤ m := by
  intro n ℓ q
  -- (L1)–(L4): additivity, subtraction, homogeneity and the norm of `graphPoint`
  obtain ⟨-, -, hadd, hsub, hsmul, hnorm, -⟩ :=
    Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  -- (L5)–(L7): projection onto, distance to and dimension of `T₀ = q(ℝⁿ × {0})`
  obtain ⟨hproj, hdist, hrank⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- (L8), (L9): the Hilbert–Schmidt facts
  exact ⟨hadd, hsub, hsmul, hnorm, hproj, hdist, hrank, Submission.any_radius_gr_la_hsNorm_facts⟩
/-- Projections onto graph planes: the estimates (Nor), (Ang), (Gp) of the linear-algebra step in
the graph-rate argument for Simon Ch. 5, Remark 5.3 (p. 122).  For a linear isometry `q` of
`ℝ^{n+ℓ}` and `A : ℝⁿ → ℝ^ℓ`, let `P_A` be the orthogonal projection onto `G_A = q(graph A)` and `P₀`
the one onto `T₀ = q(ℝⁿ × {0})`.  Then
(P1) `P_A q(x, A x) = q(x, A x)`;
(P2) (Nor) `|w| ≤ (1 + ‖A‖²)^{1/2} |q(0, w) − P_A q(0, w)|`;
(P3) (Ang) `‖A‖ ≤ (1 + ‖A‖²)^{1/2} ‖P_A − P₀‖` (operator norms);
(P4) (Gp) `|A − B| ≤ |P_A − P_B|` (Hilbert–Schmidt norms) whenever `|A|, |B| ≤ 1/4`.
(P1), (P2) hold together with the bound `‖W_A‖ ≤ (1 + ‖A‖²)^{1/2}` for the graph map
`W_A v = q(v, A v)`; (P3) follows because `P_A − P₀` maps `W_A v` to `q(0, A v)`; and (P4) follows from
`2|A − B|² ≤ (1 + ‖A‖²)(1 + ‖B‖²)|P_A − P_B|²` together with `(17/16)² ≤ 2`. -/
theorem any_radius_gr_graph_plane_projections : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n), (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection (q (graphPoint x (A x))) = q (graphPoint x (A x))) ∧ (∀ (A : Rn n →L[ℝ] Rn ℓ) (w : Rn ℓ), ‖w‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖q (graphPoint (0 : Rn n) w) - (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection (q (graphPoint (0 : Rn n) w))‖) ∧ (∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖(Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection - (rotatedPlane q).starProjection‖) ∧ ∀ A B : Rn n →L[ℝ] Rn ℓ, hsNorm A ≤ 1 / 4 → hsNorm B ≤ 1 / 4 → hsNorm (A - B) ≤ hsNorm ((Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection - (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v)))).starProjection) := by
  intro n ℓ q
  -- Steps 0–2: (P1), (P2) and the graph map `W_A v = q(v, A v)` with `‖W_A‖ ≤ (1 + ‖A‖²)^{1/2}`
  obtain ⟨hP1, hP2, hW, -⟩ := Submission.any_radius_gr_pp_graph_param n ℓ q
  -- (L2) `(a − a', b − b') = (a, b) − (a', b')`, (L4) `|(a, b)|² = |a|² + |b|²`,
  -- (L5) `P₀ q(a, b) = q(a, 0)` and the Hilbert–Schmidt facts (L8)
  obtain ⟨-, hsub, -, hnorm, hproj, -, -, hHS, -⟩ :=
    Submission.any_radius_gr_linear_algebra_basics n ℓ q
  refine ⟨hP1, hP2, fun A => ?_, fun A B hA hB => ?_⟩
  · -- Step 3, (P3) (Ang).  Only (P1) is used about `P_A`, so argue for any `P` fixing all `q(x, A x)`.
    suffices H : ∀ P : Amb n ℓ →L[ℝ] Amb n ℓ,
        (∀ x, P (q (graphPoint x (A x))) = q (graphPoint x (A x))) →
        ‖A‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖P - (rotatedPlane q).starProjection‖ from
      H _ (hP1 A)
    intro P hP
    obtain ⟨W, hWv, hWn⟩ := hW A
    refine A.opNorm_le_bound (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) fun v => ?_
    -- `(P − P₀)(W_A v) = q(v, A v) − q(v, 0) = q(0, A v)`, a vector of norm `|A v|`
    have hAv : ‖A v‖ = ‖(P - (rotatedPlane q).starProjection) (W v)‖ := by
      have h : ‖graphPoint (0 : Rn n) (A v)‖ = ‖A v‖ :=
        (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [hnorm, norm_zero]; ring)
      rw [_root_.sub_apply, hWv, hP, hproj, ← q.map_sub, ← hsub, sub_self, sub_zero,
        LinearIsometryEquiv.norm_map, h]
    calc ‖A v‖ = ‖(P - (rotatedPlane q).starProjection) (W v)‖ := hAv
      _ ≤ ‖P - (rotatedPlane q).starProjection‖ * ‖W v‖ :=
        (P - (rotatedPlane q).starProjection).le_opNorm (W v)
      _ ≤ ‖P - (rotatedPlane q).starProjection‖ * (Real.sqrt (1 + ‖A‖ ^ 2) * ‖v‖) :=
        mul_le_mul_of_nonneg_left
          ((W.le_opNorm v).trans (mul_le_mul_of_nonneg_right hWn (norm_nonneg v))) (norm_nonneg _)
      _ = Real.sqrt (1 + ‖A‖ ^ 2) * ‖P - (rotatedPlane q).starProjection‖ * ‖v‖ := by ring
  · -- Step 6, (P4) (Gp), from the key inequality `2|A − B|² ≤ (1 + ‖A‖²)(1 + ‖B‖²)|P_A − P_B|²`.
    suffices H : ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ,
        2 * hsNormSq (A - B) ≤ (1 + ‖A‖ ^ 2) * (1 + ‖B‖ ^ 2) * hsNormSq X →
        hsNorm (A - B) ≤ hsNorm X from
      H _ (Submission.any_radius_gr_pp_key_inequality n ℓ q A B)
    intro X hkey
    -- (L8f) `‖A‖ ≤ |A|`, `‖B‖ ≤ |B|` and (L8a) `0 ≤ |X|²`
    obtain ⟨-, -, -, -, -, hAop, -⟩ := hHS n ℓ A A
    obtain ⟨-, -, -, -, -, hBop, -⟩ := hHS n ℓ B B
    have hX0 : 0 ≤ hsNormSq X := (hHS (n + ℓ) (n + ℓ) X X).1
    -- `‖A‖, ‖B‖ ≤ 1/4`, hence `(1 + ‖A‖²)(1 + ‖B‖²) ≤ (17/16)² ≤ 2`
    have hA2 : ‖A‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg A, hAop.trans hA]
    have hB2 : ‖B‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg B, hBop.trans hB]
    have hc : (1 + ‖A‖ ^ 2) * (1 + ‖B‖ ^ 2) ≤ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hA2) (sq_nonneg ‖B‖), sq_nonneg ‖A‖]
    have hsq : hsNormSq (A - B) ≤ hsNormSq X := by
      linarith [mul_le_mul_of_nonneg_right hc hX0]
    -- `hsNorm = √hsNormSq` and the square root is monotone
    exact Real.sqrt_le_sqrt hsq
/-- **Tilt-excess integrals** (for the graph rate in Simon Ch. 5, Remark 5.3).  Let `V` be a
rectifiable `n`-varifold in any `U ⊆ ℝ^{n+ℓ}` whose tangent projection `x ↦ p_{T_x M}` is
`μ_V`-a.e. strongly measurable, and write
`E(s) = E(ζ, s, T) = s⁻ⁿ ∫_{B_s(ζ)} |p_{T_x M} − p_T|² dμ_V`.
If `s > 0` and `μ_V(B_s(ζ)) < ∞`, then `∫⁻_{B_s(ζ)} |p_{T_x M} − p_T|² dμ_V = sⁿ E(s)` (T1), and
`σⁿ E(σ) ≤ sⁿ E(s)` for `0 < σ ≤ s` (T2); moreover `E(s) ≥ 0` for every `s > 0` (T3).

Proof: each value of `tangentProj` is an orthogonal projection or `0`, so the Hilbert–Schmidt facts
(L8), (L9) of `any_radius_gr_linear_algebra_basics` give `0 ≤ f ≤ 4(n + ℓ)` for the integrand `f`.
As a continuous function of the a.e. strongly measurable `tangentProj`, `f` is integrable on balls
of finite mass.  After `sⁿ (sⁿ)⁻¹ = 1`, (T1) is `ofReal ∫ f = ∫⁻ ofReal f`, (T2) is monotonicity
of set integrals of `f ≥ 0` in the domain, and (T3) is `∫ f ≥ 0`. -/
theorem any_radius_gr_tilt_integral_facts : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ζ : Amb n ℓ) (T : Submodule ℝ (Amb n ℓ)), (∀ s : ℝ, 0 < s → V.weight (closedBall ζ s) < ⊤ → ∫⁻ y in closedBall ζ s, ENNReal.ofReal (hsNormSq (V.tangentProj y - T.starProjection)) ∂V.weight = ENNReal.ofReal (s ^ n * V.tiltExcess ζ s T)) ∧ (∀ σ s : ℝ, 0 < σ → σ ≤ s → V.weight (closedBall ζ s) < ⊤ → σ ^ n * V.tiltExcess ζ σ T ≤ s ^ n * V.tiltExcess ζ s T) ∧ ∀ s : ℝ, 0 < s → 0 ≤ V.tiltExcess ζ s T := by
  intro n ℓ U V htan ζ T
  -- (L8) and (L9) of `la_basics`, used on `ℝ^{n+ℓ} = Rn (n + ℓ)`.
  obtain ⟨-, -, -, -, -, -, -, hL8, hL9⟩ :=
    Submission.any_radius_gr_linear_algebra_basics n ℓ (LinearIsometryEquiv.refl ℝ (Amb n ℓ))
  set f : Amb n ℓ → ℝ := fun y => hsNormSq (V.tangentProj y - T.starProjection)
  -- Step 1: `0 ≤ f ≤ 4(n + ℓ)`, since each `tangentProj y` is some `p_K` or `0`.
  have hf0 : ∀ y, 0 ≤ f y := fun y =>
    (hL8 (n + ℓ) (n + ℓ) (V.tangentProj y - T.starProjection) 0).1
  have hp : ∀ y, hsNormSq (V.tangentProj y) ≤ ((n + ℓ : ℕ) : ℝ) := by
    intro y
    unfold RectifiableVarifold.tangentProj
    split_ifs
    · exact hL9 (n + ℓ) _
    · rw [show hsNormSq (0 : Amb n ℓ →L[ℝ] Amb n ℓ) = 0 by simp [hsNormSq]]
      exact Nat.cast_nonneg _
  have hT : hsNormSq (-T.starProjection) ≤ ((n + ℓ : ℕ) : ℝ) := by
    rw [(hL8 (n + ℓ) (n + ℓ) T.starProjection 0).2.2.2.1]
    exact hL9 (n + ℓ) T
  have hbd : ∀ y, f y ≤ 4 * ((n + ℓ : ℕ) : ℝ) := by
    intro y
    show hsNormSq (V.tangentProj y - T.starProjection) ≤ _
    rw [sub_eq_add_neg]
    have h := (hL8 (n + ℓ) (n + ℓ) (V.tangentProj y) (-T.starProjection)).2.2.1
    linarith [hp y]
  -- Step 2: `f = Φ ∘ tangentProj` with `Φ M = hsNormSq (M - p_T)` continuous.
  have hΦ : Continuous fun M : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq (M - T.starProjection) := by
    unfold hsNormSq
    exact continuous_finsetSum _ fun i _ => (continuous_norm.comp
      ((ContinuousLinearMap.apply ℝ (Amb n ℓ) (EuclideanSpace.single i (1 : ℝ))).continuous.comp
        (continuous_id.sub continuous_const))).pow 2
  have hfm : AEStronglyMeasurable f V.weight := hΦ.comp_aestronglyMeasurable htan
  -- Step 3: `f` is integrable on every closed ball of finite mass.
  have hint : ∀ s : ℝ, V.weight (closedBall ζ s) < ⊤ →
      IntegrableOn f (closedBall ζ s) V.weight := fun s hs =>
    Measure.integrableOn_of_bounded (M := 4 * ((n + ℓ : ℕ) : ℝ)) hs.ne hfm
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
        exact hbd y)
  -- `sⁿ E(ζ, s, T) = ∫_{B_s(ζ)} f dμ_V` for `s > 0`.
  have hscale : ∀ s : ℝ, 0 < s →
      s ^ n * V.tiltExcess ζ s T = ∫ y in closedBall ζ s, f y ∂V.weight := by
    intro s hs
    unfold RectifiableVarifold.tiltExcess
    rw [mul_inv_cancel_left₀ (pow_ne_zero n hs.ne')]
  refine ⟨fun s hs hfin => ?_, fun σ s hσ hσs hfin => ?_, fun s hs => ?_⟩
  · -- (T1): `ofReal` of the integral of an integrable `f ≥ 0` is its lower integral.
    rw [hscale s hs, ofReal_integral_eq_lintegral_ofReal (hint s hfin) (ae_of_all _ hf0)]
  · -- (T2): set integrals of `f ≥ 0` increase with the domain.
    rw [hscale σ hσ, hscale s (hσ.trans_le hσs)]
    exact setIntegral_mono_set (hint s hfin) (ae_of_all _ hf0)
      (closedBall_subset_closedBall hσs).eventuallyLE
  · -- (T3): a positive factor times the integral of `f ≥ 0`.
    unfold RectifiableVarifold.tiltExcess
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le n)) (integral_nonneg hf0)
/-- **Height transfer on a graph piece** (step 4 of the rate estimates `any_radius_graph_rate`
for a `C¹` graph piece of `spt V`, Remark 5.3).  Let `Ω = B̆_R(0)`, `F(x) = q(x, u(x))` with
`u(0) = 0` and `‖Du‖ ≤ 1/7` on `Ω`.  Assume (E1) `∫_Ω g ∘ F ≤ ∫_{F(Ω)} g dμ_V` for Borel `g ≥ 0`
and (E2) `p_{F(x)} = P_{Du(x)}` for a.e. `x ∈ Ω`.  Then
`∫_Ω |u(x) − Du(x) x|² / |x|^{n+2} dx ≤ 2^{n+4} ∫_{B̆_ρ(0)} |y − p_y y|² / |y|^{n+2} dμ_V(y)`.
Pointwise, `any_radius_gr_ht_pointwise_height` with `P = p_{F(x)}` bounds the integrand by
`2^{n+4} G(F(x))`; `any_radius_gr_ht_ae_transfer` then moves `∫_Ω G ∘ F` to `∫_{F(Ω)} G dμ_V`. -/
theorem any_radius_gr_height_transfer : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (R ρ : ℝ), ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ 1 / 7) → q '' graphOver u (ball 0 R) ⊆ ball 0 ρ → AEStronglyMeasurable V.tangentProj V.weight → (∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in ball (0 : Rn n) R, g (q (graphPoint x (u x))) ≤ ∫⁻ y in q '' graphOver u (ball 0 R), g y ∂V.weight) → (∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) R)), V.tangentProj (q (graphPoint x (u x))) = (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u x v)))).starProjection) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal (2 ^ (n + 4)) * ∫⁻ y in ball (0 : Amb n ℓ) ρ, ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)) ∂V.weight := by
  intro n ℓ U V q u R ρ hu hu0 hDu hS hP hE1 hE2
  -- `(a, c) ↦ graphPoint a c` is linear (la_basics (L1), (L3)), hence continuous.
  obtain ⟨hL1, -, hL3, -⟩ := Submission.any_radius_gr_linear_algebra_basics n ℓ q
  let Lg : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := fun p p' => hL1 p.1 p'.1 p.2 p'.2
      map_smul' := fun t p => hL3 t p.1 p.2 }
  have hgc : Continuous fun p : Rn n × Rn ℓ => graphPoint p.1 p.2 :=
    Lg.continuous_of_finiteDimensional
  -- `F(x) = q (graphPoint x (u x))` is continuous on `Ω`, hence a.e.-measurable for `Lⁿ ⌞ Ω`.
  have hF : AEMeasurable (fun x => q (graphPoint x (u x)))
      (volume.restrict (ball (0 : Rn n) R)) :=
    (q.continuous.comp_continuousOn
      (hgc.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn))).aemeasurable
      measurableSet_ball
  -- The right-hand integrand `G(y) = |y − p_y y|² / |y|^{n+2}` is `μ_V`-a.e.-measurable.
  have hTy : AEStronglyMeasurable (fun y => V.tangentProj y y) V.weight :=
    (continuous_fst.clm_apply continuous_snd :
      Continuous fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × Amb n ℓ => p.1 p.2).comp_aestronglyMeasurable
      (hP.prodMk aestronglyMeasurable_id)
  have hG : AEMeasurable
      (fun y : Amb n ℓ => ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)))
      V.weight :=
    (((aemeasurable_id.sub hTy.aemeasurable).norm.pow_const 2).div
      (aemeasurable_id.norm.pow_const (n + 2))).ennreal_ofReal
  -- Mean value inequality and `u(0) = 0`: `|u(x)| ≤ |x|/7` on `Ω`.
  have hdiff : ∀ x ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u x := fun x hx =>
    (hu.differentiableOn_one x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hsmall : ∀ x ∈ ball (0 : Rn n) R, ‖u x‖ ≤ ‖x‖ / 7 := by
    intro x hx
    have h0 : (0 : Rn n) ∈ ball (0 : Rn n) R :=
      mem_ball_self (lt_of_le_of_lt (norm_nonneg x) (mem_ball_zero_iff.mp hx))
    have h := (convex_ball (0 : Rn n) R).norm_image_sub_le_of_norm_fderiv_le hdiff hDu h0 hx
    rw [hu0, sub_zero, sub_zero] at h
    linarith
  -- Pointwise bound for a.e. `x ∈ Ω`: pointwise_height with `P = p_{F(x)} = P_{Du(x)}`, whose
  -- hypotheses (H1), (H2) are plane_projections (P1), (P2) at `Du(x)`, transported along (E2).
  obtain ⟨hP1, hP2, -, -⟩ := Submission.any_radius_gr_graph_plane_projections n ℓ q
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) R)),
      ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤
        ENNReal.ofReal (2 ^ (n + 4)) *
          ENNReal.ofReal (‖q (graphPoint x (u x)) - V.tangentProj (q (graphPoint x (u x)))
            (q (graphPoint x (u x)))‖ ^ 2 / ‖q (graphPoint x (u x))‖ ^ (n + 2)) := by
    filter_upwards [hE2, ae_restrict_mem measurableSet_ball] with x hx hxΩ
    have key := Submission.any_radius_gr_ht_pointwise_height n ℓ q
      (V.tangentProj (q (graphPoint x (u x)))) (fderiv ℝ u x) x (u x) (hDu x hxΩ)
      (hsmall x hxΩ) (by rw [hx]; exact hP1 (fderiv ℝ u x) x)
      (by rw [hx]; exact hP2 (fderiv ℝ u x))
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (n + 4))]
    exact ENNReal.ofReal_le_ofReal key
  -- Integrate, transfer along `F` (ae_transfer with (E1)), and enlarge `F(Ω)` to `B̆_ρ(0)`.
  calc ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2))
      ≤ ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (2 ^ (n + 4)) *
          ENNReal.ofReal (‖q (graphPoint x (u x)) - V.tangentProj (q (graphPoint x (u x)))
            (q (graphPoint x (u x)))‖ ^ 2 / ‖q (graphPoint x (u x))‖ ^ (n + 2)) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 ^ (n + 4)) * ∫⁻ x in ball (0 : Rn n) R,
          ENNReal.ofReal (‖q (graphPoint x (u x)) - V.tangentProj (q (graphPoint x (u x)))
            (q (graphPoint x (u x)))‖ ^ 2 / ‖q (graphPoint x (u x))‖ ^ (n + 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ (n + 4)) * ∫⁻ y in q '' graphOver u (ball 0 R),
          ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)) ∂V.weight := by
        gcongr ENNReal.ofReal (2 ^ (n + 4)) * ?_
        exact Submission.any_radius_gr_ht_ae_transfer n ℓ (volume.restrict (ball (0 : Rn n) R))
          (V.weight.restrict (q '' graphOver u (ball 0 R))) (fun x => q (graphPoint x (u x))) hF
          hE1 (fun y => ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)))
          hG.restrict
    _ ≤ ENNReal.ofReal (2 ^ (n + 4)) * ∫⁻ y in ball (0 : Amb n ℓ) ρ,
          ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)) ∂V.weight := by
        gcongr ENNReal.ofReal (2 ^ (n + 4)) * ?_
        exact lintegral_mono_set hS
/-- **Scaled `Lᵖ` norm of `H` on sub-balls** (the Hölder estimate of Simon Ch. 5, Remark 2.2,
p. 107, with exponent `1` in place of `2`).  Let `p > n ≥ 1`, `0 < r ≤ ρ` and
`B_r(z) ⊆ B_ρ(0)`, with `K(ξ, σ) = (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}` (`scaledLpNorm`).
(K1) `K(z, r) ≤ K(0, ρ)`.
(K2) If `K(0, ρ) ≤ δ` and `μ_V(B_r(z)) < ∞`, then
`∫_{B_r(z)} |H| dμ_V ≤ δ ρ^{n/p−1} μ_V(B_r(z))^{1−1/p}`.
Proof: (K1) follows from `r^{p−n} ≤ ρ^{p−n}`, monotonicity of the lower integral in the domain and
of `t ↦ t^{1/p}`.  For (K2), `K(0, ρ) = ρ^{1−n/p} (∫_{B_ρ(0)} |H|ᵖ)^{1/p}`, so
`(∫_{B_r(z)} |H|ᵖ)^{1/p} ≤ δ ρ^{n/p−1}`.  If `|H|` is not integrable on `B_r(z)` the Bochner
integral is `0`; otherwise Hölder with exponents `p` and `p/(p−1)` against `1` gives
`∫_{B_r(z)} |H| ≤ (∫_{B_r(z)} |H|ᵖ)^{1/p} μ_V(B_r(z))^{1−1/p}`, a finite bound. -/
theorem any_radius_gr_scaled_lp_ball_bounds : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (z : Amb n ℓ) (r ρ : ℝ), 0 < r → r ≤ ρ → closedBall z r ⊆ closedBall 0 ρ → V.scaledLpNorm H p z r ≤ V.scaledLpNorm H p 0 ρ ∧ ∀ δ : ℝ, 0 ≤ δ → V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ → V.weight (closedBall z r) < ⊤ → ∫ x in closedBall z r, ‖H x‖ ∂V.weight ≤ δ * ρ ^ ((n : ℝ) / p - 1) * (V.weight (closedBall z r)).toReal ^ (1 - 1 / p) := by
  intro n ℓ hn p hnp U V H z r ρ hr hrρ hsub
  -- Step 1: `p > 1`, `p - n > 0`, `ρ ≥ r > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := lt_of_le_of_lt hn1 hnp
  have hp0 : 0 < p := by linarith
  have hpn : 0 < p - n := by linarith
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hinvp : 0 ≤ 1 / p := by positivity
  -- Step 2: domain monotonicity of the lower integral (no measurability needed).
  have hI : ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight ≤
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight :=
    lintegral_mono_set hsub
  refine ⟨?_, fun δ hδ hK hfin => ?_⟩
  · -- (K1): `r^{p-n} ≤ ρ^{p-n}`, then monotonicity of products and of `t ↦ t^{1/p}`.
    unfold RectifiableVarifold.scaledLpNorm
    exact ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hr.le hrρ hpn.le)) hI) hinvp
  -- (K2), Step 4: `I(z, r)^{1/p} ≤ ofReal (δ ρ^{n/p - 1})`, using
  -- `K(0, ρ) = ofReal (ρ^{(p-n)/p}) I(0, ρ)^{1/p}` and `ρ^{n/p - 1} ρ^{(p-n)/p} = 1`.
  have he : 0 < ρ ^ ((n : ℝ) / p - 1) := Real.rpow_pos_of_pos hρ _
  have hc : 0 ≤ ρ ^ (p - n) := (Real.rpow_pos_of_pos hρ _).le
  have hce : ρ ^ ((n : ℝ) / p - 1) * (ρ ^ (p - n)) ^ (1 / p) = 1 := by
    rw [← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]
    have : (n : ℝ) / p - 1 + (p - n) * (1 / p) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  have hJ : (∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤
      ENNReal.ofReal (δ * ρ ^ ((n : ℝ) / p - 1)) := by
    calc (∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)
        ≤ (∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hI hinvp
      _ = ENNReal.ofReal (ρ ^ ((n : ℝ) / p - 1)) * V.scaledLpNorm H p 0 ρ := by
          unfold RectifiableVarifold.scaledLpNorm
          rw [ENNReal.mul_rpow_of_nonneg _ _ hinvp, ENNReal.ofReal_rpow_of_nonneg hc hinvp,
            ← mul_assoc, ← ENNReal.ofReal_mul he.le, hce, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (ρ ^ ((n : ℝ) / p - 1)) * ENNReal.ofReal δ := mul_le_mul' le_rfl hK
      _ = ENNReal.ofReal (δ * ρ ^ ((n : ℝ) / p - 1)) := by
          rw [← ENNReal.ofReal_mul he.le, mul_comm]
  -- Step 3: case split on the integrability of the real function `f = ‖H‖` on the ball.
  by_cases hint : IntegrableOn (fun x => ‖H x‖) (closedBall z r) V.weight
  swap
  · -- Case A: the Bochner integral of a non-integrable function is `0`.
    rw [integral_undef hint]
    positivity
  -- Case B: `f` is a.e.-strongly measurable for `μ ⌞ B`, hence so is `ofReal ∘ f = ‖H‖ₑ`.
  have hf : AEStronglyMeasurable (fun x => ‖H x‖) (V.weight.restrict (closedBall z r)) :=
    Integrable.aestronglyMeasurable hint
  have hF : AEMeasurable (fun x => ENNReal.ofReal ‖H x‖) (V.weight.restrict (closedBall z r)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable
  -- Step 5: Hölder with exponents `p` and `p' = p/(p-1)` against the constant `1`.
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
  have hq : 1 / Real.conjExponent p = 1 - 1 / p := by
    rw [one_div, one_div, hpq.one_sub_inv]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (V.weight.restrict (closedBall z r)) hpq hF
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    one_mul, ofReal_norm, hq] at hHolder
  have hp' : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp1.le)
  have hL : ∫⁻ x in closedBall z r, ‖H x‖ₑ ∂V.weight ≤
      ENNReal.ofReal (δ * ρ ^ ((n : ℝ) / p - 1)) * V.weight (closedBall z r) ^ (1 - 1 / p) :=
    hHolder.trans (mul_le_mul' hJ le_rfl)
  -- Step 6: convert to the Bochner integral and take `toReal` of the finite bound.
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => norm_nonneg _) hf]
  simp only [ofReal_norm]
  calc (∫⁻ x in closedBall z r, ‖H x‖ₑ ∂V.weight).toReal
      ≤ (ENNReal.ofReal (δ * ρ ^ ((n : ℝ) / p - 1)) *
          V.weight (closedBall z r) ^ (1 - 1 / p)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hp' hfin.ne)) hL
    _ = δ * ρ ^ ((n : ℝ) / p - 1) * (V.weight (closedBall z r)).toReal ^ (1 - 1 / p) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_rpow]
/-- **Translation invariance** (Simon Ch. 5; re-centring the hypotheses 2.3 at a point `ζ`, as in
the proof of Remark 5.3).  Let `V'` be the translate of `V` by `τ(x) = x − ζ`: `μ_{V'} = τ_# μ_V`,
`θ' = θ(ζ + ·)` and `p_{T_x M'} = p_{T_{ζ+x} M}`.  Then for every real `s`:
`μ_{V'}(B_s(0)) = μ_V(B_s(ζ))`, `E'(0, s, T) = E(ζ, s, T)`,
`(s^{p−n} ∫_{B_s(0)} |H(ζ + ·)|ᵖ dμ_{V'})^{1/p} = (s^{p−n} ∫_{B_s(ζ)} |H|ᵖ dμ_V)^{1/p}`, and
`θ ≥ 1` `μ_V`-a.e. implies `θ' ≥ 1` `μ_{V'}`-a.e.
Proof: `τ` is a measurable embedding with `τ⁻¹(B_s(0)) = B_s(ζ)`; along a measurable embedding,
push-forward evaluation holds for every set and change of variables for every integrand. -/
theorem any_radius_gr_translate_identities : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ζ : Amb n ℓ), V'.weight = V.weight.map (fun x => x - ζ) → (∀ x, V'.mult x = V.mult (ζ + x)) → (∀ x, V'.tangentProj x = V.tangentProj (ζ + x)) → (∀ s : ℝ, V'.weight (closedBall 0 s) = V.weight (closedBall ζ s)) ∧ (∀ (s : ℝ) (T : Submodule ℝ (Amb n ℓ)), V'.tiltExcess 0 s T = V.tiltExcess ζ s T) ∧ (∀ (H : Amb n ℓ → Amb n ℓ) (p s : ℝ), V'.scaledLpNorm (fun x => H (ζ + x)) p 0 s = V.scaledLpNorm H p ζ s) ∧ ((∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ᵐ x ∂V'.weight, 1 ≤ V'.mult x) := by
  intro n ℓ U U' V V' ζ hw hm ht
  have hτ : MeasurableEmbedding fun x : Amb n ℓ => x - ζ := measurableEmbedding_subRight ζ
  -- `τ⁻¹(B_s(0)) = B_s(ζ)`, for every real `s`.
  have hball : ∀ s : ℝ, (fun x : Amb n ℓ => x - ζ) ⁻¹' closedBall 0 s = closedBall ζ s := by
    intro s
    ext y
    simp [dist_eq_norm]
  refine ⟨fun s => ?_, fun s T => ?_, fun H p s => ?_, fun h1 => ?_⟩
  · -- (R1): `μ_{V'}(B_s(0)) = μ_V(τ⁻¹ B_s(0)) = μ_V(B_s(ζ))`.
    rw [hw, hτ.map_apply, hball]
  · -- (R2): change of variables in the tilt integral, then `ζ + (y − ζ) = y`.
    unfold tiltExcess
    rw [hw, hτ.setIntegral_map, hball]
    simp only [ht, add_sub_cancel]
  · -- (R3): the same for the lower integral of `|H(ζ + ·)|ᵖ`.
    unfold scaledLpNorm
    rw [hw, hτ.restrict_map, hτ.lintegral_map, hball]
    simp only [add_sub_cancel]
  · -- (R4): `τ⁻¹{θ' < 1} = {θ < 1}` is `μ_V`-null.
    rw [hw, hτ.ae_map_iff]
    filter_upwards [h1] with y hy
    simpa only [hm, add_sub_cancel] using hy

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
