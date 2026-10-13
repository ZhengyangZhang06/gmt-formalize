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

/-- Covering step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if every
point of the open set `U` has a ball in `U` on which `F` is `C¹` with `α`-Hölder derivative, then
`F` is `C¹` on `U` and `D¹F` is `α`-Hölder on every compact `K ⊆ U`.  Pairs of points of `K` closer
than a Lebesgue number `δ` of a finite subcover lie in one ball; for the other pairs,
`‖DF(x) - DF(y)‖ ≤ 2 sup_K ‖DF‖ ≤ 2 sup_K ‖DF‖ δ^{-α} ‖x - y‖^α`. -/
theorem dohr_eb_lhr_cover_holder_one : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (U : Set (Rn n)) (F : Rn n → E), 0 < α → IsOpen U → (∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ball x R ⊆ U ∧ ContDiffOn ℝ 1 F (ball x R) ∧ ∃ C : ℝ, ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖fderiv ℝ F y - fderiv ℝ F z‖ ≤ C * ‖y - z‖ ^ α) → ContDiffOn ℝ 1 F U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 F x - iteratedFDeriv ℝ 1 F y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n E _ _ α U F hα hU hloc
  choose! R hR hRU hRF C hC using hloc
  -- Step 1: `F` is `C¹` on `U` by locality.
  have hF : ContDiffOn ℝ 1 F U := by
    refine contDiffOn_of_locally_contDiffOn fun x hx =>
      ⟨ball x (R x), isOpen_ball, mem_ball_self (hR x hx), ?_⟩
    rw [inter_eq_right.2 (hRU x hx)]
    exact hRF x hx
  refine ⟨hF, fun K hK hKU => ?_⟩
  -- Steps 2–3: `DF` is continuous on `U`, hence bounded by `S` on `K`.
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: finitely many hypothesis balls cover `K`; `Cs` bounds their Hölder constants.
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => ball x (R x))
    fun x hx => ball_mem_nhds x (hR x (hKU hx))
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, ∀ i ∈ t, C i ≤ Cs :=
    ⟨∑ i ∈ t, |C i|, fun i hi => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) hi)⟩
  -- Step 5: a Lebesgue number `δ` of this finite cover.
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun i : t => ball (i : Rn n) (R i)) (fun _ => isOpen_ball) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hKt hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  -- Steps 6–8: the Hölder bound for `DF` on `K`.
  have hD : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤
      max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hxy : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    rcases lt_or_ge ‖x - y‖ δ with hlt | hge
    · -- Near pairs lie in one ball of the subcover.
      obtain ⟨⟨i, hi⟩, hiδ⟩ := hδK x hx
      have hxB : x ∈ ball i (R i) := hiδ (mem_ball_self hδ)
      have hyB : y ∈ ball i (R i) := hiδ (mem_ball'.2 (by rwa [dist_eq_norm]))
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ C i * ‖x - y‖ ^ α :=
            hC i (hKU (htK i hi)) x hxB y hyB
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right ((hCs i hi).trans (le_max_left _ _)) hxy
    · -- Far pairs: `‖x - y‖ ^ α ≥ δ ^ α > 0`.
      have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
      have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ ‖fderiv ℝ F x‖ + ‖fderiv ℝ F y‖ := norm_sub_le _ _
        _ ≤ S + S := add_le_add (hS x hx) (hS y hy)
        _ = 2 * S * (δ ^ α)⁻¹ * δ ^ α := by rw [inv_mul_cancel_right₀ hδα.ne', two_mul]
        _ ≤ 2 * S * (δ ^ α)⁻¹ * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hge hα.le) (by positivity)
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hxy
  -- Step 9: `D¹F(z)` is the image of `DF(z)` under a linear isometry equivalence.
  have hiso : ∀ z, iteratedFDeriv ℝ 1 F z =
      (continuousMultilinearCurryFin1 ℝ (Rn n) E).symm (fderiv ℝ F z) := by
    intro z
    ext m
    rw [iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_symm_apply]
  refine ⟨max Cs (2 * S * (δ ^ α)⁻¹), fun x hx y hy => ?_⟩
  rw [hiso x, hiso y, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hD x hx y hy
/-- **Uniform bounds for a `C¹` scalar function on a compact convex set** (the scalar step of the
coefficient bounds in the linear higher-regularity part of Simon 7.1).  Let `0 < α ≤ 1`, `U ⊆ ℝⁿ`
open, `K ⊆ U` compact and convex, and `f` be `C¹` on `U`.  Then some `S ≥ 0` has `|f(x)| ≤ S` and
`|f(x) − f(y)| ≤ S |x − y|^α` for all `x, y ∈ K`.
Proof: `f` and `Df` are continuous, hence bounded, on the compact `K`; the mean value inequality
on the convex `K` gives `|f(x) − f(y)| ≤ S₁ |x − y|`; and with `D = diam K`,
`t = t^α t^{1−α} ≤ D^{1−α} t^α` for `0 ≤ t ≤ D`. -/
theorem dohr_eb_lhr_cub_scalar_c1_bounds : ∀ (n : ℕ) (α : ℝ) (U K : Set (Rn n)) (f : Rn n → ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → ContDiffOn ℝ 1 f U → ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ K, ∀ y ∈ K, |f x| ≤ S ∧ |f x - f y| ≤ S * ‖x - y‖ ^ α := by
  intro n α U K f hα0 hα1 hU hK hKc hKU hf
  -- Step 1: `f` and `Df` are continuous on `K`, and `f` is differentiable at every point of `K`.
  have hfc : ContinuousOn f K := hf.continuousOn.mono hKU
  have hdfc : ContinuousOn (fderiv ℝ f) K := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  have hfd : ∀ x ∈ K, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  -- Step 2: `|f| ≤ S0` and `‖Df‖ ≤ S1` on the compact set `K`.
  obtain ⟨S0, hS0⟩ := hK.exists_bound_of_continuousOn hfc
  obtain ⟨S1, hS1⟩ := hK.exists_bound_of_continuousOn hdfc
  -- Step 3: mean value inequality on the convex set `K`.
  have hlip : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ max S1 0 * ‖x - y‖ := by
    intro x hx y hy
    have h := hKc.norm_image_sub_le_of_norm_fderiv_le (C := max S1 0) hfd
      (fun z hz => (hS1 z hz).trans (le_max_left _ _)) hy hx
    rwa [Real.norm_eq_abs] at h
  -- Step 4: `‖x - y‖ ≤ D := diam K` on `K`.
  have hdist : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ Metric.diam K := fun x hx y hy => by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hK.isBounded hx hy
  -- Step 5: `t ≤ D^(1-α) t^α` for `0 ≤ t ≤ D`.
  have helem : ∀ t : ℝ, 0 ≤ t → t ≤ Metric.diam K →
      t ≤ Metric.diam K ^ (1 - α) * t ^ α := by
    intro t ht0 htD
    rcases ht0.eq_or_lt with rfl | htpos
    · rw [Real.zero_rpow hα0.ne', mul_zero]
    · have h1 : t ^ α * t ^ (1 - α) = t := by
        rw [← Real.rpow_add htpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have h2 : t ^ (1 - α) ≤ Metric.diam K ^ (1 - α) :=
        Real.rpow_le_rpow ht0 htD (by linarith)
      calc t = t ^ α * t ^ (1 - α) := h1.symm
        _ ≤ t ^ α * Metric.diam K ^ (1 - α) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0 _)
        _ = Metric.diam K ^ (1 - α) * t ^ α := mul_comm _ _
  -- Steps 6-7: `S := max (max S0 0) (max S1 0 * D^(1-α))`.
  refine ⟨max (max S0 0) (max S1 0 * Metric.diam K ^ (1 - α)),
    (le_max_right _ _).trans (le_max_left _ _), ?_⟩
  intro x hx y hy
  constructor
  · calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ S0 := hS0 x hx
      _ ≤ max S0 0 := le_max_left _ _
      _ ≤ _ := le_max_left _ _
  · calc |f x - f y| ≤ max S1 0 * ‖x - y‖ := hlip x hx y hy
      _ ≤ max S1 0 * (Metric.diam K ^ (1 - α) * ‖x - y‖ ^ α) :=
        mul_le_mul_of_nonneg_left (helem _ (norm_nonneg _) (hdist x hx y hy)) (le_max_right _ _)
      _ = (max S1 0 * Metric.diam K ^ (1 - α)) * ‖x - y‖ ^ α := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
/-- Coefficient bounds for the linear system in the proof of Simon Ch. 5, Theorem 7.1 (second
assertion, p. 127), steps 1, 2 and 6: on a finite-dimensional real normed space `L` with basis
`E₀, …, E_{N-1}`, every continuous bilinear form satisfies
`|B(P)(Q)| ≤ c (∑_{r,t} |B(E_r)(E_t)|) ‖P‖ ‖Q‖`, and likewise for the difference `B − B'` of two
forms, with `c = c₀²`, `c₀ = ∑_r ‖π_r‖` the sum of the norms of the coordinate functionals. -/
theorem dohr_eb_lhr_cub_bilinear_basis_bound : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (E : Fin N → L) (c : ℝ), 0 ≤ c ∧ (∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t)|) * ‖P‖ * ‖Q‖) ∧ ∀ (B B' : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q - B' P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t) - B' (E r) (E t)|) * ‖P‖ * ‖Q‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` and its continuous coordinate functionals `π r`.
  let b := Module.finBasis ℝ L
  let π : Fin (Module.finrank ℝ L) → L →L[ℝ] ℝ := fun r =>
    LinearMap.toContinuousLinearMap (b.coord r)
  have hπ : ∀ r P, π r P = b.repr P r := fun r P => by simp [π]
  -- Step 2: `|P_r| ≤ c₀ ‖P‖` with `c₀ = ∑ r, ‖π r‖`.
  let c₀ : ℝ := ∑ r, ‖π r‖
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun r _ => norm_nonneg (π r)
  have hcoord : ∀ r P, |b.repr P r| ≤ c₀ * ‖P‖ := by
    intro r P
    rw [← hπ, ← Real.norm_eq_abs]
    calc ‖π r P‖ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ c₀ * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun s _ => norm_nonneg (π s)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: `B P Q = ∑ r, ∑ t, P_r Q_t B (b r) (b t)`.
  have hexp : ∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L),
      B P Q = ∑ r, ∑ t, b.repr P r * b.repr Q t * B (b r) (b t) := by
    intro B P Q
    conv_lhs => rw [← b.sum_repr P, ← b.sum_repr Q]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  -- Step 4: `|∑ r, ∑ t, P_r Q_t β r t| ≤ c₀² (∑ r, ∑ t, |β r t|) ‖P‖ ‖Q‖` for any array `β`.
  have harr : ∀ (β : Fin (Module.finrank ℝ L) → Fin (Module.finrank ℝ L) → ℝ) (P Q : L),
      |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t| ≤
        c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
    intro β P Q
    calc |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t|
        ≤ ∑ r, |∑ t, b.repr P r * b.repr Q t * β r t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, |b.repr P r * b.repr Q t * β r t| :=
          Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, c₀ * ‖P‖ * (c₀ * ‖Q‖) * |β r t| := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (hcoord r P) (hcoord t Q) (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
          simp only [← Finset.mul_sum]
          ring
  -- Step 5: take `E = b` and `c = c₀²`; for `B − B'` subtract the two expansions termwise.
  refine ⟨Module.finrank ℝ L, b, c₀ ^ 2, by positivity, fun B P Q => ?_, fun B B' P Q => ?_⟩
  · rw [hexp B P Q]
    exact harr _ P Q
  · rw [hexp B P Q, hexp B' P Q]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact harr _ P Q
/-- Coefficient bounds in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): if every component `x ↦ a(x)[P][Q]` of a field `a` of continuous bilinear forms on
`L = L(ℝⁿ, ℝ^ℓ)` is `C¹` on the open set `U`, then on each compact convex `K ⊆ U` the forms `a(x)`
are uniformly bounded and uniformly `α`-Hölder in `x`.  A basis `E_r` of `L` controls every
bilinear form through its values `B(E_r, E_t)`, and each `C¹` component `a_rt(x) = a(x)[E_r][E_t]`
is bounded by `S_rt` and `α`-Hölder with constant `S_rt` on `K`; take `M := c Σ_{r,t} S_rt`. -/
theorem dohr_eb_lhr_coeff_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U K : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ∃ M : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖ ∧ |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
  intro n ℓ α U K a hα hα1 hU hK hKc hKU ha
  -- Steps 1–2: expansion of bilinear forms on a basis `E` of `L`.
  obtain ⟨N, E, c, hc, hB, hBB'⟩ :=
    Submission.dohr_eb_lhr_cub_bilinear_basis_bound (Rn n →L[ℝ] Rn ℓ)
  -- Steps 3–5: each component `a_rt` is bounded and `α`-Hölder on `K`, with constant `S r t`.
  choose S hS0 hS using fun r t : Fin N =>
    Submission.dohr_eb_lhr_cub_scalar_c1_bounds n α U K (fun x => a x (E r) (E t)) hα hα1 hU hK
      hKc hKU (ha (E r) (E t))
  -- Steps 6–7: sum the component bounds over the basis.
  refine ⟨c * ∑ r, ∑ t, S r t, fun x hx y hy P Q => ⟨?_, ?_⟩⟩
  · calc |a x P Q| ≤ c * (∑ r, ∑ t, |a x (E r) (E t)|) * ‖P‖ * ‖Q‖ := hB (a x) P Q
      _ ≤ c * (∑ r, ∑ t, S r t) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).1
  · calc |a x P Q - a y P Q|
        ≤ c * (∑ r, ∑ t, |a x (E r) (E t) - a y (E r) (E t)|) * ‖P‖ * ‖Q‖ :=
          hBB' (a x) (a y) P Q
      _ ≤ c * (∑ r, ∑ t, S r t * ‖x - y‖ ^ α) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).2
      _ = c * (∑ r, ∑ t, S r t) * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
        simp only [← Finset.sum_mul]
        ring
/-- Continuity of a linear-form family evaluated along continuous data (in the difference-quotient
weak equation of the linear higher-regularity step of the elliptic bootstrap for Simon 7.1): if
`x ↦ Φ(x)[P]` is continuous on the open set `U` for every `P ∈ L = L(ℝⁿ, ℝ^ℓ)`, `s(x₀) ∈ U` and `s`,
`B` are continuous at `x₀`, then `x ↦ Φ(s(x))[B(x)]` is continuous at `x₀`.  Expanding `B(x)` in a
basis `(E_r)` of the finite-dimensional space `L` writes `Φ(s(x))[B(x)]` as the finite sum
`Σ_r c_r(B(x)) Φ(s(x))[E_r]` of products of functions continuous at `x₀`. -/
theorem dohr_eb_lhr_dqwe_linear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => Φ (s x) (B x)) x₀ := by
  intro n ℓ U Φ s B x₀ hU hΦ hs₀ hs hB
  -- Step 1: a basis `E_r = b r` of `L`; its coordinates `c_r = b.coord r` are continuous on `L`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: `Φ(s x)[B x] = Σ_r c_r(B x) Φ(s x)[E_r]`, by linearity of `Φ(s x)`.
  have hexp : (fun x => Φ (s x) (B x)) = fun x => ∑ r, b.repr (B x) r * Φ (s x) (b r) := by
    funext x
    conv_lhs => rw [← b.sum_repr (B x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  -- Step 3: `x ↦ c_r(B x)` is continuous at `x₀`.
  have hc : ∀ r, ContinuousAt (fun x => b.repr (B x) r) x₀ := fun r =>
    (b.coord r).continuous_of_finiteDimensional.continuousAt.comp hB
  -- Step 4: `x ↦ Φ(s x)[E_r]` is continuous at `x₀`, since `U` is a neighbourhood of `s x₀`.
  have hΦr : ∀ r, ContinuousAt (fun x => Φ (s x) (b r)) x₀ := fun r =>
    ((hΦ (b r)).continuousAt (hU.mem_nhds hs₀)).comp hs
  -- Step 5: a finite sum of products of functions continuous at `x₀` is continuous at `x₀`.
  rw [hexp]
  exact tendsto_finsetSum _ fun r _ => (hc r).mul (hΦr r)
/-- **Continuity of a bilinear-form family evaluated along continuous data.**  Let
`L = L(ℝⁿ, ℝ^ℓ)`, let `U ⊆ ℝⁿ` be open and let `a : ℝⁿ → L(L, L(L, ℝ))` be such that
`x ↦ a(x)[P][Q]` is continuous on `U` for all `P, Q ∈ L`.  If `s(x₀) ∈ U` and `s`, `A`, `B` are
continuous at `x₀`, then `x ↦ a(s(x))[A(x)][B(x)]` is continuous at `x₀`.
In a basis `(E_r)` of `L` with (continuous) coordinate functionals `c_r`,
`a(s(x))[A(x)][B(x)] = Σ_r c_r(A(x)) · a(s(x))[E_r][B(x)]`, and each `x ↦ a(s(x))[E_r][B(x)]` is
continuous at `x₀` by `dohr_eb_lhr_dqwe_linear_family_continuousAt` applied to `y ↦ a(y)[E_r]`. -/
theorem dohr_eb_lhr_dqwe_bilinear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (A B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt A x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => a (s x) (A x) (B x)) x₀ := by
  intro n ℓ U a s A B x₀ hU ha hsU hs hA hB
  -- Step 1: a basis `E_r = b r` of the finite-dimensional space `L`; its coordinate functionals
  -- `c_r = b.coord r` are continuous.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  have hc : ∀ r, Continuous fun P : Rn n →L[ℝ] Rn ℓ => b.repr P r := fun r =>
    (b.coord r).continuous_of_finiteDimensional
  -- Step 2: expanding the first slot, `a(s x)[A x][B x] = Σ_r c_r(A x) · a(s x)[E_r][B x]`.
  have hexp : ∀ x, a (s x) (A x) (B x) = ∑ r, b.repr (A x) r * a (s x) (b r) (B x) := by
    intro x
    conv_lhs => rw [← b.sum_repr (A x)]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [hexp]
  -- Steps 3–5: each summand is `c_r ∘ A` times `x ↦ a(s x)[E_r][B x]`, both continuous at `x₀`
  -- (the latter by the linear-family lemma for `y ↦ a(y)[E_r]`), and finite sums preserve this.
  refine tendsto_finsetSum _ fun r _ => ((hc r).continuousAt.comp hA).mul ?_
  exact Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U (fun y => a y (b r)) s B x₀
    hU (fun P => ha (b r) P) hsU hs hB
/-- Translated weak identity (difference-quotient step of the linear higher-regularity argument in
the elliptic bootstrap of Simon Ch. 5, Theorem 7.1).  Suppose
`∫_U a(x)[Dv(x)][Dζ(x)] dx = ∫_U Φ(x)[Dζ(x)] dx` for every `C¹` map `ζ : ℝⁿ → ℝ^ℓ` with compact
support in `U`, and let `η` be `C¹` with compact support and `x + h ∈ U` for `x ∈ spt η`.  Then
`∫ a(x + h)[Dv(x + h)][Dη(x)] dx = ∫ Φ(x + h)[Dη(x)] dx` over all of `ℝⁿ`.  Proof: test with
`ζ = η(· − h)`, which is `C¹` with compact support in `U` and `Dζ = Dη(· − h)`; both integrands
vanish off `U`, so the integrals over `U` are integrals over `ℝⁿ`; finally substitute `y = x + h`
(translation invariance of Lebesgue measure). -/
theorem dohr_eb_lhr_dqwe_shifted_weak_identity : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (h : Rn n) (η : Rn n → Rn ℓ), (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiff ℝ 1 η → HasCompactSupport η → (∀ x ∈ tsupport η, x + h ∈ U) → ∫ x, a (x + h) (fderiv ℝ v (x + h)) (fderiv ℝ η x) = ∫ x, Φ (x + h) (fderiv ℝ η x) := by
  intro n ℓ U a Φ v h η hweak hη hηc hηU
  -- Step 1: the translated test function `ζ = η(· − h)` is `C¹` with compact support.
  have hζC : ContDiff ℝ 1 (fun y => η (y - h)) := hη.comp (contDiff_id.sub contDiff_const)
  have hζc : HasCompactSupport (fun y => η (y - h)) := hηc.comp_homeomorph (Homeomorph.subRight h)
  -- Step 2: `y ∈ spt ζ ⇒ y − h ∈ spt η ⇒ y = (y − h) + h ∈ U`.
  have hζU : tsupport (fun y => η (y - h)) ⊆ U := fun y hy => by
    simpa only [sub_add_cancel] using
      hηU (y - h) (tsupport_comp_subset_preimage η (continuous_id.sub continuous_const) hy)
  -- Step 3: the weak identity for `ζ`, with `Dζ(y) = Dη(y − h)`.
  have h3 := hweak (fun y => η (y - h)) hζC hζc hζU
  simp only [fderiv_comp_sub] at h3
  -- Step 4: off `U`, `y − h ∉ spt η ⊇ spt Dη`, so `Dη(y − h) = 0` and both integrands vanish.
  have hvan : ∀ y, y ∉ U → fderiv ℝ η (y - h) = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => hy (by
      simpa only [sub_add_cancel] using hηU (y - h) (tsupport_fderiv_subset ℝ hmem))
  have hL : ∫ y in U, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) =
      ∫ y, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  have hR : ∫ y in U, Φ y (fderiv ℝ η (y - h)) = ∫ y, Φ y (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  -- Step 5: substitute `y = x + h` (Lebesgue measure is translation invariant), `x + h − h = x`.
  have e1 := integral_add_right_eq_self (μ := volume)
    (fun y => a y (fderiv ℝ v y) (fderiv ℝ η (y - h))) h
  have e2 := integral_add_right_eq_self (μ := volume) (fun y => Φ y (fderiv ℝ η (y - h))) h
  simp only [add_sub_cancel_right] at e1 e2
  rw [e1, e2, ← hL, ← hR]
  exact h3
/-- A function `F : ℝⁿ → ℝ` continuous at every point of a compact set `K` and vanishing off `K` is
Lebesgue integrable.  `K` is closed, so each `x ∉ K` has the open neighbourhood `ℝⁿ \ K` on which
`F = 0`, and `F` is continuous at `x`; at the points of `K` it is continuous by hypothesis.  Thus `F`
is continuous, and it has compact support since it vanishes off the compact set `K`, so it is
integrable for `volume`, which is finite on compact sets. -/
theorem dohr_eb_lhr_dqwe_integrable_of_continuousAt : ∀ (n : ℕ) (F : Rn n → ℝ) (K : Set (Rn n)), IsCompact K → (∀ x ∈ K, ContinuousAt F x) → (∀ x, x ∉ K → F x = 0) → Integrable F := by
  intro n F K hK hcont hzero
  -- Steps 1–3: `F` is continuous at every point; off `K` it agrees with `0` on the open
  -- neighbourhood `Kᶜ` of the point.
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ K
    · exact hcont x hx
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] F := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact (hzero y hy).symm
      exact continuousAt_const.congr hev
  -- Steps 4–5: `F` vanishes off the compact set `K`, so it has compact support and is integrable.
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hzero)
/-- Derivative of a difference quotient (difference-quotient step of the linear higher-regularity
argument in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1): if `v : ℝⁿ → ℝ^ℓ` is
differentiable at `x` and at `x + d e`, then the derivative at `x` of
`z ↦ d⁻¹ (v(z + d e) − v(z))` is `d⁻¹ (Dv(x + d e) − Dv(x))`.  For `d = 0` both sides vanish,
as `0⁻¹ = 0`.  By the chain rule `g(z) = v(z + d e)` is differentiable at `x` with
`Dg(x) = Dv(x + d e)`; the derivative of `d⁻¹ (g − v)` is then `d⁻¹ (Dg(x) − Dv(x))`. -/
theorem dohr_eb_lhr_dqwe_fderiv_diff_quot : ∀ (n ℓ : ℕ) (v : Rn n → Rn ℓ) (e x : Rn n) (d : ℝ), DifferentiableAt ℝ v x → DifferentiableAt ℝ v (x + d • e) → fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) := by
  intro n ℓ v e x d hx hxd
  have hg : DifferentiableAt ℝ (fun z => v (z + d • e)) x :=
    hxd.comp x (differentiableAt_id.add_const (d • e))
  rw [fderiv_fun_const_smul (hg.fun_sub hx) d⁻¹, fderiv_fun_sub hg hx,
    fderiv_comp_add_right (d • e)]
/-- Difference quotients of a weak solution (step 3 of the linear higher-regularity argument behind
**Simon Ch. 5, Theorem 7.1(ii)**).  If `v ∈ C¹(U)` satisfies `∫_U a(x)[Dv][Dζ] = ∫_U Φ(x)[Dζ]` for
all `ζ ∈ C¹_c(U; ℝ^ℓ)`, then `w = d⁻¹ (v(· + de) − v)` satisfies `∫_B a(x)[Dw][Dζ] = ∫_B Ψ(x)[Dζ]`
on `B = B̆_{2R}(xb)` for all `ζ ∈ C¹_c(B; ℝ^ℓ)`, where
`Ψ(x) = d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de) − a(x))[Dv(x + de)]`: test the equation with `ζ`
and with `ζ(· − de)`, subtract, and divide by `d`. -/
theorem dohr_eb_lhr_dq_weak_equation : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R d : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → d ≠ 0 → |d| < R → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → ContDiffOn ℝ 1 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball xb (2 * R) → ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x) = ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v xb e R d hU hR hball he hd hdR ha hΦ hv hweak
  -- Step 1: `Ψ(x) := d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de)[Q_x] − a(x)[Q_x])`,
  -- `Q_x := Dv(x + de)`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ),
      Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) -
        d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P) :=
    ⟨fun x => d⁻¹ • (Φ (x + d • e) - Φ x) -
        d⁻¹ • (a (x + d • e) (fderiv ℝ v (x + d • e)) - a x (fderiv ℝ v (x + d • e))),
      fun x P => by simp only [sub_apply, smul_apply, smul_eq_mul]⟩
  refine ⟨Ψ, hΨ, fun ζ hζ hζc hζB => ?_⟩
  -- Step 2: for `x ∈ B := B̆_{2R}(xb)`, both `x` and `x + de` lie in `B_{4R}(xb) ⊆ U`.
  have hde : ‖d • e‖ < R := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
      _ < R := by rwa [mul_one]
  have hBU : ∀ x ∈ ball xb (2 * R), x ∈ U := fun x hx =>
    hball (mem_closedBall.2 (by linarith [mem_ball.1 hx]))
  have hBU' : ∀ x ∈ ball xb (2 * R), x + d • e ∈ U := by
    intro x hx
    refine hball (mem_closedBall.2 ?_)
    have h1 : dist (x + d • e) x = ‖d • e‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    linarith [dist_triangle (x + d • e) x xb, mem_ball.1 hx]
  -- Step 3: `v` is differentiable and `Dv` is continuous at every point of the open set `U`.
  have hvd : ∀ y ∈ U, DifferentiableAt ℝ v y := fun y hy =>
    (hv.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hDv : ∀ y ∈ U, ContinuousAt (fderiv ℝ v) y := fun y hy =>
    (hv.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hsh : ∀ x : Rn n, ContinuousAt (fun y : Rn n => y + d • e) x := fun x =>
    (continuous_id.add continuous_const).continuousAt
  -- Step 5: `K := tsupport ζ ⊆ B` is compact; `Dζ` is continuous and vanishes off `K`.
  have hK : IsCompact (tsupport ζ) := hζc
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ hx
  have hKU : ∀ x ∈ tsupport ζ, x ∈ U := fun x hx => hBU x (hζB hx)
  have hKU' : ∀ x ∈ tsupport ζ, x + d • e ∈ U := fun x hx => hBU' x (hζB hx)
  -- Step 6: the integrands `f₁, g₁, f₂, f₃, g₃` are continuous at the points of `K` and vanish
  -- off `K`, hence integrable.
  have hf1 : Integrable (fun x => a x (fderiv ℝ v x) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fderiv ℝ v) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x) (hDv x (hKU x hx))
        hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg1 : Integrable (fun x => Φ x (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ (fun y => y)
        (fderiv ℝ ζ) x hU hΦ (hKU x hx) (continuousAt_id' x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf2 : Integrable (fun x => a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x)
        ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf3 : Integrable (fun x => a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a
        (fun y => y + d • e) (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU' x hx)
        (hsh x) ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg3 : Integrable (fun x => Φ (x + d • e) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ
        (fun y => y + d • e) (fderiv ℝ ζ) x hU hΦ (hKU' x hx) (hsh x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  -- Steps 7–8: testing with `ζ` and with `ζ(· − de)` gives `∫ f₁ = ∫ g₁` and `∫ f₃ = ∫ g₃`.
  have h7 : ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x, Φ x (fderiv ℝ ζ x) := by
    have h := Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v 0 ζ hweak hζ hζc
      (fun x hx => by rw [add_zero]; exact hKU x hx)
    simpa only [add_zero] using h
  have h8 : ∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) =
      ∫ x, Φ (x + d • e) (fderiv ℝ ζ x) :=
    Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v (d • e) ζ hweak hζ hζc hKU'
  -- Step 9: on `B`, `Dw = d⁻¹ (Dv(· + de) − Dv)` (step 4), so
  -- `a(x)[Dw(x)][Dζ(x)] = d⁻¹ (f₂ − f₁)(x)`; both sides become integrals over `ℝⁿ` of integrands
  -- vanishing off `K ⊆ B`.
  have hlhs : ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x)
      (fderiv ℝ ζ x) = d⁻¹ * ((∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
        ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x)) := by
    have hEq : EqOn
        (fun x => a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x))
        (fun x => d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
          a x (fderiv ℝ v x) (fderiv ℝ ζ x))) (ball xb (2 * R)) := by
      intro x hx
      simp only
      rw [Submission.dohr_eb_lhr_dqwe_fderiv_diff_quot n ℓ v e x d (hvd x (hBU x hx))
        (hvd _ (hBU' x hx)), map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
    have hzero : ∀ x, x ∉ ball xb (2 * R) → d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v x) (fderiv ℝ ζ x)) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero, map_zero, sub_zero, mul_zero]
    rw [setIntegral_congr_fun measurableSet_ball hEq,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_const_mul,
      integral_sub hf2 hf1]
  have hrhs : ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) =
      d⁻¹ * ((∫ x, Φ (x + d • e) (fderiv ℝ ζ x)) - ∫ x, Φ x (fderiv ℝ ζ x)) -
        d⁻¹ * ((∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
          ∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) := by
    have hzero : ∀ x, x ∉ ball xb (2 * R) → Ψ x (fderiv ℝ ζ x) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero]
    have hI1 : Integrable fun x => d⁻¹ * (Φ (x + d • e) (fderiv ℝ ζ x) - Φ x (fderiv ℝ ζ x)) :=
      (hg3.sub hg1).const_mul _
    have hI2 : Integrable fun x => d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
      (hf3.sub hf2).const_mul _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp only [hΨ]
    rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul, integral_sub hg3 hg1,
      integral_sub hf3 hf2]
  -- `LHS − RHS = d⁻¹ [(∫ f₃ − ∫ g₃) − (∫ f₁ − ∫ g₁)] = 0`.
  rw [hlhs, hrhs, h7, ← h8]
  ring
/-- Steps 2–3 of the uniform difference-quotient bounds, for one function `g`: if `g` is `C¹` on
an open `U ⊇ K` with `K` compact and `D¹g = iteratedFDeriv ℝ 1 g` is `α`-Hölder on `K` with some
constant `C`, then `Dg = fderiv ℝ g` is bounded on `K` by some `S ≥ 0` and is `α`-Hölder on `K`
with some constant `H ≥ 0`.  (`D¹g(z)` is the image of `Dg(z)` under the linear isometry
`(continuousMultilinearCurryFin1 ℝ E F).symm`; no condition on `α` is needed.) -/
theorem dohr_eb_lhr_dqub_fderiv_consts : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U K : Set E) (g : E → F), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ C * ‖x - y‖ ^ α) → ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ S) ∧ ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U K g hU hK hKU hg hC
  obtain ⟨C, hC⟩ := hC
  -- Step 1: `D¹g(z) = Ψ(Dg(z))` for the linear isometry `Ψ = (continuousMultilinearCurryFin1 ℝ E F).symm`.
  have h1 : ∀ z, iteratedFDeriv ℝ 1 g z = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g z) := by
    intro z
    ext m
    simp [iteratedFDeriv_one_apply]
  -- Step 2: `‖Dg(x) − Dg(y)‖ = ‖Ψ(Dg(x) − Dg(y))‖ = ‖D¹g(x) − D¹g(y)‖`.
  have h2 : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ = ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ := by
    intro x y
    rw [h1 x, h1 y, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 3: `Dg` is continuous on the open `U ⊇ K`, hence bounded by some `S₀` on the compact `K`.
  obtain ⟨S₀, hS₀⟩ := hK.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: `S = max S₀ 0` and `H = max C 0`, using `‖x − y‖^α ≥ 0`.
  refine ⟨max S₀ 0, max C 0, le_max_right _ _, le_max_right _ _,
    fun x hx => (hS₀ x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  rw [h2 x y]
  exact (hC x hx y hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference-quotient bounds.**
Let `g` be differentiable on an open `U ⊇ B_{4R}(x̄)` with `‖Dg‖ ≤ S` and
`‖Dg(z) − Dg(w)‖ ≤ H ‖z − w‖^α` on `B_{4R}(x̄)`.  If `‖e‖ ≤ 1` and `0 < |d| < R`, then on
`B̆_{2R}(x̄)` the difference quotient `d⁻¹ (g(x + d e) − g(x))` is bounded by `S` and is
`α`-Hölder with constant `H`.
Proof: for `z ∈ B̆_{2R}(x̄)` and `|s| ≤ |d|`, `z + s e ∈ B_{4R}(x̄) ⊆ U`.  The mean value inequality
on this convex ball gives `‖g(x + d e) − g(x)‖ ≤ S |d|`.  For the second bound,
`h(s) = g(x + s e) − g(y + s e)` has `‖h'(s)‖ = ‖(Dg(x + s e) − Dg(y + s e)) e‖ ≤ H ‖x − y‖^α`
for `s` between `0` and `d`, so `‖h(d) − h(0)‖ ≤ H ‖x − y‖^α |d|`; divide by `|d|`. -/
theorem dohr_eb_lhr_dqub_dq_mean_value : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U : Set E) (g : E → F) (xb e : E) (R S H d : ℝ), IsOpen U → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → DifferentiableOn ℝ g U → (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ g z‖ ≤ S) → (∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R), ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ H * ‖z - w‖ ^ α) → d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖d⁻¹ • (g (x + d • e) - g x)‖ ≤ S ∧ ‖d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y)‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U g xb e R S H d hU hKU he hg hS hH hd hdR x hx y hy
  have hdpos : 0 < |d| := abs_pos.mpr hd
  -- Step 2: for `z ∈ ball xb (2 * R)` and `|s| ≤ |d|`, `z + s • e ∈ closedBall xb (4 * R)`.
  have hgeo : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖e‖ ≤ |d| * 1 := mul_le_mul hs he (norm_nonneg e) (abs_nonneg d)
        _ = |d| := mul_one _
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by congr 1; abel
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith [abs_nonneg d]
  -- Step 3: `g` is differentiable at every point of `closedBall xb (4 * R) ⊆ U`.
  have hdiff : ∀ z ∈ closedBall xb (4 * R), DifferentiableAt ℝ g z := fun z hz =>
    (hg z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  have hx0 : x ∈ closedBall xb (4 * R) := by
    have h := hgeo x hx 0 (by simp)
    rwa [zero_smul, add_zero] at h
  constructor
  · -- Step 4: part (a), the mean value inequality on `closedBall xb (4 * R)`.
    have hmv : ‖g (x + d • e) - g x‖ ≤ S * ‖x + d • e - x‖ :=
      (convex_closedBall xb (4 * R)).norm_image_sub_le_of_norm_fderiv_le hdiff hS hx0
        (hgeo x hx d le_rfl)
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx0)
    have hde : ‖d • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg d) he
    rw [add_sub_cancel_left] at hmv
    rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖g (x + d • e) - g x‖ ≤ S * ‖d • e‖ := hmv
      _ ≤ S * |d| := mul_le_mul_of_nonneg_left hde hS0
      _ = |d| * S := mul_comm _ _
  · -- Steps 5–8: part (b), the mean value inequality for `s ↦ g (x + s • e) - g (y + s • e)`.
    have hI : ∀ s ∈ uIcc (0 : ℝ) d, |s| ≤ |d| := by
      intro s hs
      simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hlin : ∀ (z : E) (s : ℝ), HasDerivAt (fun σ : ℝ => z + σ • e) e s := by
      intro z s
      simpa using ((hasDerivAt_id s).smul_const e).const_add z
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) d, HasDerivWithinAt
        (fun σ : ℝ => g (x + σ • e) - g (y + σ • e))
        (fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e) (uIcc (0 : ℝ) d) s := by
      intro s hs
      have hxs := hdiff _ (hgeo x hx s (hI s hs))
      have hys := hdiff _ (hgeo y hy s (hI s hs))
      exact ((hxs.hasFDerivAt.comp_hasDerivAt s (hlin x s)).sub
        (hys.hasFDerivAt.comp_hasDerivAt s (hlin y s))).hasDerivWithinAt
    have hbound : ∀ s ∈ uIcc (0 : ℝ) d,
        ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖ ≤ H * ‖x - y‖ ^ α := by
      intro s hs
      have hxy : x + s • e - (y + s • e) = x - y := add_sub_add_right_eq_sub x y (s • e)
      calc ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖
          = ‖(fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)) e‖ := by rw [sub_apply]
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) he
        _ ≤ H * ‖x + s • e - (y + s • e)‖ ^ α :=
            hH _ (hgeo x hx s (hI s hs)) _ (hgeo y hy s (hI s hs))
        _ = H * ‖x - y‖ ^ α := by rw [hxy]
    have hmv := (convex_uIcc (0 : ℝ) d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at hmv
    have hrw : d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y) =
        d⁻¹ • ((g (x + d • e) - g (y + d • e)) - (g x - g y)) := by
      rw [← smul_sub]; congr 1; abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖(g (x + d • e) - g (y + d • e)) - (g x - g y)‖ ≤ H * ‖x - y‖ ^ α * |d| := hmv
      _ = |d| * (H * ‖x - y‖ ^ α) := mul_comm _ _
/-- Difference-quotient bounds in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second
assertion (p. 127): on a finite-dimensional real normed space `L`, real linear and bilinear forms
are bounded by `C` times their largest value on finitely many test vectors `b r`.  Take a basis
`b` of `L`; its coordinates `π r` are continuous, and `c = Σ_r ‖π r‖` gives
`|b.repr P r| ≤ c ‖P‖`.  Expanding `P` in the basis gives `|f P| ≤ N c m ‖P‖`, expanding in both
arguments gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`, and `C = N c + N² c²`. -/
theorem dohr_eb_lhr_dqub_form_coords : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (b : Fin N → L) (C : ℝ), 0 ≤ C ∧ (∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) → ∀ P, |f P| ≤ C * m * ‖P‖) ∧ ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) → (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) → ∀ Q P, |β Q P| ≤ C * m * ‖Q‖ * ‖P‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` indexed by `Fin N` (`N = finrank ℝ L`).
  obtain ⟨N, ⟨b⟩⟩ : ∃ N : ℕ, Nonempty (Module.Basis (Fin N) ℝ L) :=
    ⟨_, ⟨Module.finBasis ℝ L⟩⟩
  -- Step 2: the coordinates `π r = b.coord r` are continuous as `L` is finite-dimensional, and
  -- `c = Σ_r ‖π r‖` gives `|b.repr P r| ≤ c ‖P‖`.
  obtain ⟨c, hc0, hcoord⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ r P, |b.repr P r| ≤ c * ‖P‖ := by
    let π : Fin N → L →L[ℝ] ℝ := fun r => LinearMap.toContinuousLinearMap (b.coord r)
    refine ⟨∑ r, ‖π r‖, Finset.sum_nonneg fun r _ => norm_nonneg _, fun r P => ?_⟩
    have hπ : π r P = b.repr P r := by simp [π]
    calc |b.repr P r| = ‖π r P‖ := by rw [hπ, Real.norm_eq_abs]
      _ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ (∑ t, ‖π t‖) * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun t _ => norm_nonneg (π t)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: a linear `f` is determined by its basis values, `f P = Σ_r b.repr P r · f (b r)`.
  have hexp : ∀ f : L → ℝ, IsLinearMap ℝ f → ∀ P, f P = ∑ r, b.repr P r * f (b r) := by
    intro f hf P
    calc f P = IsLinearMap.mk' f hf (∑ r, b.repr P r • b r) := by
          rw [b.sum_repr, IsLinearMap.mk'_apply]
      _ = ∑ r, b.repr P r * f (b r) := by
          simp only [map_sum, map_smul, IsLinearMap.mk'_apply, smul_eq_mul]
  -- Step 4: the linear bound `|f P| ≤ N c m ‖P‖`.
  have hlin : ∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) →
      ∀ P, |f P| ≤ N * c * m * ‖P‖ := by
    intro f m hf hm hb P
    rw [hexp f hf P]
    calc |∑ r, b.repr P r * f (b r)| ≤ ∑ r, |b.repr P r * f (b r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin N, c * ‖P‖ * m := by
          gcongr with r
          rw [abs_mul]
          exact mul_le_mul (hcoord r P) (hb r) (abs_nonneg _) (by positivity)
      _ = N * c * m * ‖P‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Steps 5–6: expanding `β` in each argument, i.e. the linear bound for each `β (b r)` and then
  -- for `Q ↦ β Q P`, gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`.
  have hbil : ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) →
      (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) →
      ∀ Q P, |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by
    intro β m hβ₁ hβ₂ hm hb Q P
    have hr : ∀ r, |β (b r) P| ≤ N * c * m * ‖P‖ := fun r =>
      hlin (β (b r)) m (hβ₂ (b r)) hm (hb r) P
    calc |β Q P| ≤ N * c * (N * c * m * ‖P‖) * ‖Q‖ :=
          hlin (fun Q => β Q P) (N * c * m * ‖P‖) (hβ₁ P) (by positivity) hr Q
      _ = N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by ring
  -- Step 7: `C = N c + N² c²` serves for both bounds.
  refine ⟨N, b, N * c + N * c * (N * c), by positivity, fun f m hf hm hb P => ?_,
    fun β m hβ₁ hβ₂ hm hb Q P => ?_⟩
  · calc |f P| ≤ N * c * m * ‖P‖ := hlin f m hf hm hb P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖P‖ := by
          rw [add_mul, add_mul]
          exact le_add_of_nonneg_right (by positivity)
  · calc |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := hbil β m hβ₁ hβ₂ hm hb Q P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖Q‖ * ‖P‖ := by
          rw [add_mul, add_mul, add_mul]
          exact le_add_of_nonneg_left (by positivity)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a locally
`C^{1,α}` map.**  Let `v` be locally `C^{1,α}` on the open set `U ⊇ B_{4R}(xb)` and `‖e‖ ≤ 1`.
There is `S` such that for every `0 < |d| < R` the difference quotient
`w_d(z) = d⁻¹ (v(z + d e) − v(z))` satisfies the following on `B̆_{2R}(xb)`: `‖w_d‖ ≤ S`, `w_d` is
`C¹`, `Dw_d(x) = d⁻¹ (Dv(x + d e) − Dv(x))`, and `Dw_d` is `α`-Hölder.
Proof: `dohr_eb_lhr_dqub_fderiv_consts` on the compact set `K₀ = B_{4R}(xb)` gives a bound `S_v`
and a Hölder constant `H_v` for `Dv` on `K₀`; put `S = S_v`.  For `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`,
`‖z + s e − xb‖ < 2R + R ≤ 4R`, so `z` and `z + d e` lie in `K₀ ⊆ U`.  The bound on `w_d` is part
(a) of `dohr_eb_lhr_dqub_dq_mean_value`.  The `C¹` property and the derivative formula follow from
the chain rule for the translation `z ↦ z + d e`.  Finally
`Dw_d(x) − Dw_d(y) = d⁻¹ ((Dv(x + d e) − Dv(y + d e)) − (Dv(x) − Dv(y)))` has norm at most
`2 H_v |d|⁻¹ ‖x − y‖^α`. -/
theorem dohr_eb_lhr_dqub_wd_props : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → IsLocallyHolderCkα 1 α v U → ∃ S : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ S) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ ∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α := by
  intro n ℓ α U v xb e R hU hR hsub he hv
  -- Step 1: `v` is `C¹` on `U`, and `D¹v` is `α`-Hölder on the compact set `K₀ = B_{4R}(xb) ⊆ U`.
  have hC1 : ContDiffOn ℝ 1 v U := by simpa using hv.1
  have hK0 : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  -- Step 2: `‖Dv‖ ≤ S_v` and `‖Dv(z) − Dv(w)‖ ≤ H_v ‖z − w‖^α` on `K₀`.  The constant
  -- `S := S_v` does not depend on `d`.
  obtain ⟨Sv, Hv, -, -, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U (closedBall xb (4 * R)) v hU hK0
      hsub hC1 (hv.2 _ hK0 hsub)
  refine ⟨Sv, fun d hd hdR => ?_⟩
  -- Step 3: `z + s e ∈ K₀` for `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`; in particular `z, z + d e ∈ K₀`.
  have hgeom : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg s) he).trans hs
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by rw [sub_add_eq_add_sub]
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith
  have hz0 : ∀ z ∈ ball xb (2 * R), z ∈ closedBall xb (4 * R) := fun z hz => by
    simpa using hgeom z hz 0 (by simp)
  have hzd : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := fun z hz =>
    hgeom z hz d le_rfl
  -- Step 4: claim (i) is part (a) of `dohr_eb_lhr_dqub_dq_mean_value` (taking `y = x`).
  have hdiff : DifferentiableOn ℝ v U := hC1.differentiableOn one_ne_zero
  have hmv := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) (Rn ℓ) α U v xb e R Sv Hv d hU hsub
    he hdiff hSv hHv hd hdR
  -- Step 6: `w_d` has derivative `d⁻¹ (Dv(x + d e) − Dv(x))` at every `x ∈ B̆_{2R}(xb)`.
  have hderiv : ∀ x ∈ ball xb (2 * R), HasFDerivAt (fun z => d⁻¹ • (v (z + d • e) - v z))
      (d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) x := by
    intro x hx
    have hxU : x ∈ U := hsub (hz0 x hx)
    have hxdU : x + d • e ∈ U := hsub (hzd x hx)
    have hv0 : DifferentiableAt ℝ v x := (hdiff x hxU).differentiableAt (hU.mem_nhds hxU)
    have hv1 : DifferentiableAt ℝ v (x + d • e) :=
      (hdiff _ hxdU).differentiableAt (hU.mem_nhds hxdU)
    have hcomp : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (x + d • e)) x := by
      simpa [Function.comp_def] using
        hv1.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))
    exact (hcomp.sub hv0.hasFDerivAt).const_smul d⁻¹
  refine ⟨fun x hx => (hmv x hx x hx).1, ?_, fun x hx => (hderiv x hx).fderiv, ?_⟩
  · -- Step 5: claim (ii), since `w_d = d⁻¹ • (v ∘ τ − v)` for the translation `τ z = z + d e`.
    have hτ : ContDiffOn ℝ 1 (fun z : Rn n => z + d • e) (ball xb (2 * R)) :=
      (contDiff_id.add contDiff_const).contDiffOn
    have hτU : MapsTo (fun z : Rn n => z + d • e) (ball xb (2 * R)) U := fun z hz =>
      hsub (hzd z hz)
    have h1 : ContDiffOn ℝ 1 (fun z => v (z + d • e)) (ball xb (2 * R)) := hC1.comp hτ hτU
    have h2 : ContDiffOn ℝ 1 v (ball xb (2 * R)) := hC1.mono fun z hz => hsub (hz0 z hz)
    exact (h1.sub h2).const_smul d⁻¹
  · -- Step 7: claim (iv) with `K = 2 H_v |d|⁻¹`, using the Hölder bound of `Dv` at the four points
    -- `x, y, x + d e, y + d e ∈ K₀`.
    refine ⟨2 * Hv * |d|⁻¹, fun x hx y hy => ?_⟩
    rw [(hderiv x hx).fderiv, (hderiv y hy).fderiv]
    have heq : d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) -
        d⁻¹ • (fderiv ℝ v (y + d • e) - fderiv ℝ v y) =
        d⁻¹ • ((fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)) :=
      (smul_sub _ _ _).symm.trans (by rw [sub_sub_sub_comm])
    have h1 := hHv _ (hzd x hx) _ (hzd y hy)
    rw [add_sub_add_right_eq_sub] at h1
    have h2 := hHv _ (hz0 x hx) _ (hz0 y hy)
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |d|⁻¹ * ‖(fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)‖
        ≤ |d|⁻¹ * (Hv * ‖x - y‖ ^ α + Hv * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
            (inv_nonneg.2 (abs_nonneg d))
      _ = 2 * Hv * |d|⁻¹ * ‖x - y‖ ^ α := by ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `d`-uniform Hölder bound for the
forcing term of the difference-quotient system.**  Let `L = L(ℝⁿ, ℝ^ℓ)`, `U ⊇ B_{4R}(xb)` open,
`‖e‖ ≤ 1`, let the coefficients `x ↦ a(x)[P][Q]` and `x ↦ Φ(x)[P]` be `C^{1,α}` in `U` and `v` be
`C^{1,α}` in `U`.  For `0 < |d| < R` put
`F_d(x, P) = d⁻¹ (Φ(x + d e)[P] − Φ(x)[P])
  − d⁻¹ (a(x + d e)[Dv(x + d e)][P] − a(x)[Dv(x + d e)][P])`.
Then `|F_d(x, P) − F_d(y, P)| ≤ M ‖x − y‖^α ‖P‖` on `B̆_{2R}(xb)` with `M` independent of `d`.
Proof: `dohr_eb_lhr_dqub_form_coords` gives a spanning family `b` of `L` and a constant `C`
bounding linear and bilinear forms by their values on `b`.  On `K₀ = B_{4R}(xb)`,
`dohr_eb_lhr_dqub_fderiv_consts` gives a common bound `S'` and a common Hölder constant `H` for
the derivatives of the scalar coefficients `a(·)[b_r][b_t]`, `Φ(·)[b_r]`, and `S_v`, `H_v` for
`Dv`; put `M = C (H + H S_v + S' H_v)`.  The mean value inequality
`dohr_eb_lhr_dqub_dq_mean_value` bounds the difference quotients of these coefficients by `S'`
and their differences at `x, y` by `H ‖x − y‖^α`.  With
`Q_x = Dv(x + d e)` and `Q_y = Dv(y + d e)`,
`F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)` for the linear form `T` and the
bilinear forms `β₁`, `β₂` built from these difference quotients, and the coordinate bounds give
`|T(P)| + |β₁(Q_x, P)| + |β₂(Q_x − Q_y, P)| ≤ M ‖x − y‖^α ‖P‖`. -/
theorem dohr_eb_lhr_dqub_forcing_holder : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R hU hR hK0U he ha hΦ hv
  -- Step 1: a spanning family `b` of `L` and the coordinate constant `C`.
  obtain ⟨N, b, C, hC, hD1, hD2⟩ :=
    Submission.dohr_eb_lhr_dqub_form_coords (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: derivative bounds and Hölder constants of the components on `K₀ = B_{4R}(xb)`.
  have hK0c : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  have hAa : ∀ r t : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => a z (b r) (b t)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => a z (b r) (b t)) z - fderiv ℝ (fun z => a z (b r) (b t)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r t =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => a z (b r) (b t)) hU hK0c
      hK0U (ha (b r) (b t)).1 ((ha (b r) (b t)).2 _ hK0c hK0U)
  have hAΦ : ∀ r : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => Φ z (b r)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => Φ z (b r)) z - fderiv ℝ (fun z => Φ z (b r)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => Φ z (b r)) hU hK0c
      hK0U (hΦ (b r)).1 ((hΦ (b r)).2 _ hK0c hK0U)
  obtain ⟨Sv, Hv, hSv0, hHv0, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U _ v hU hK0c hK0U
      (by simpa using hv.1) (hv.2 _ hK0c hK0U)
  choose Sa Ha hSa0 hHa0 hSa hHa using hAa
  choose SΦ HΦ hSΦ0 hHΦ0 hSΦ hHΦ using hAΦ
  -- Step 3: uniform constants `S'`, `H` for all components; `M` is fixed before `d`.
  set S' : ℝ := ∑ r, ∑ t, Sa r t + ∑ r, SΦ r
  set H : ℝ := ∑ r, ∑ t, Ha r t + ∑ r, HΦ r
  have hSa_sum0 : 0 ≤ ∑ r, ∑ t, Sa r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t
  have hHa_sum0 : 0 ≤ ∑ r, ∑ t, Ha r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t
  have hSΦ_sum0 : 0 ≤ ∑ r, SΦ r := Finset.sum_nonneg fun r _ => hSΦ0 r
  have hHΦ_sum0 : 0 ≤ ∑ r, HΦ r := Finset.sum_nonneg fun r _ => hHΦ0 r
  have hS'0 : 0 ≤ S' := add_nonneg hSa_sum0 hSΦ_sum0
  have hH0 : 0 ≤ H := add_nonneg hHa_sum0 hHΦ_sum0
  have hSa_le : ∀ r t, Sa r t ≤ S' := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hSa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Sa r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hSΦ_sum0))
  have hHa_le : ∀ r t, Ha r t ≤ H := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hHa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Ha r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hHΦ_sum0))
  have hSΦ_le : ∀ r, SΦ r ≤ S' := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hSΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hSa_sum0)
  have hHΦ_le : ∀ r, HΦ r ≤ H := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hHΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hHa_sum0)
  refine ⟨C * (H + H * Sv + S' * Hv), ?_⟩
  intro d hd hdR x hx y hy P
  -- Step 4: `x + d e, y + d e ∈ K₀`, and the bounds on `Q_x = Dv(x + d e)`, `Q_y = Dv(y + d e)`.
  have hshift : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := by
    intro z hz
    rw [mem_closedBall]
    rw [mem_ball] at hz
    have h1 : dist (z + d • e) xb ≤ dist z xb + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖z + d • e - xb‖ = ‖(z - xb) + d • e‖ := by congr 1; abel
        _ ≤ ‖z - xb‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
        _ ≤ R := by linarith
    linarith
  have hxK := hshift x hx
  have hyK := hshift y hy
  set t : ℝ := ‖x - y‖ ^ α
  have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) α
  set Qx := fderiv ℝ v (x + d • e)
  set Qy := fderiv ℝ v (y + d • e)
  have hQxb : ‖Qx‖ ≤ Sv := hSv _ hxK
  have hQxy : ‖Qx - Qy‖ ≤ Hv * t := by
    have := hHv _ hxK _ hyK
    rwa [add_sub_add_right_eq_sub] at this
  -- Step 5: the scalar difference quotients of the components, by the mean value inequality
  -- `dohr_eb_lhr_dqub_dq_mean_value` with the common constants `S'` and `H`.
  have hBa : ∀ r t', |d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ S' ∧
      |d⁻¹ * (a (x + d • e) (b r) (b t') - a x (b r) (b t')) -
        d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ H * t := by
    intro r t'
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => a z (b r) (b t')) xb e R S' H d hU hK0U he
      ((ha (b r) (b t')).1.differentiableOn one_ne_zero)
      (fun z hz => (hSa r t' z hz).trans (hSa_le r t'))
      (fun z hz w hw => (hHa r t' z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHa_le r t') (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    refine ⟨?_, ?_⟩
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB y hy y hy).1
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  have hBΦ : ∀ r, |d⁻¹ * (Φ (x + d • e) (b r) - Φ x (b r)) -
      d⁻¹ * (Φ (y + d • e) (b r) - Φ y (b r))| ≤ H * t := by
    intro r
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => Φ z (b r)) xb e R S' H d hU hK0U he
      ((hΦ (b r)).1.differentiableOn one_ne_zero)
      (fun z hz => (hSΦ r z hz).trans (hSΦ_le r))
      (fun z hz w hw => (hHΦ r z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHΦ_le r) (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  -- Step 6: the linear form `T` and the bilinear forms `β₁`, `β₂`.
  let T : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P' =>
    d⁻¹ * (Φ (x + d • e) P' - Φ x P') - d⁻¹ * (Φ (y + d • e) P' - Φ y P')
  let β1 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (x + d • e) Q P' - a x Q P') - d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  let β2 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  have hTlin : IsLinearMap ℝ T := by
    constructor
    · intro P1 P2; simp only [T, map_add]; ring
    · intro c P1; simp only [T, map_smul, smul_eq_mul]; ring
  have hβ1l : ∀ P', IsLinearMap ℝ (fun Q => β1 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β1, map_add, add_apply]; ring
    · intro c Q1; simp only [β1, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ1r : ∀ Q, IsLinearMap ℝ (β1 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β1, map_add]; ring
    · intro c P1; simp only [β1, map_smul, smul_eq_mul]; ring
  have hβ2l : ∀ P', IsLinearMap ℝ (fun Q => β2 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β2, map_add, add_apply]; ring
    · intro c Q1; simp only [β2, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ2r : ∀ Q, IsLinearMap ℝ (β2 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β2, map_add]; ring
    · intro c P1; simp only [β2, map_smul, smul_eq_mul]; ring
  -- Step 7: coordinate bounds for `T(P)`, `β₁(Q_x, P)` and `β₂(Q_x − Q_y, P)`.
  have hT : |T P| ≤ C * (H * t) * ‖P‖ :=
    hD1 T (H * t) hTlin (mul_nonneg hH0 ht0) (fun r => hBΦ r) P
  have hβ1 : |β1 Qx P| ≤ C * (H * t) * ‖Qx‖ * ‖P‖ :=
    hD2 β1 (H * t) hβ1l hβ1r (mul_nonneg hH0 ht0) (fun r t' => (hBa r t').2) Qx P
  have hβ2 : |β2 (Qx - Qy) P| ≤ C * S' * ‖Qx - Qy‖ * ‖P‖ :=
    hD2 β2 S' hβ2l hβ2r hS'0 (fun r t' => (hBa r t').1) (Qx - Qy) P
  -- Step 8: `F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)`.
  have hid : (d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) Qx P - a x Qx P)) -
      (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) Qy P - a y Qy P)) =
      T P - β1 Qx P - β2 (Qx - Qy) P := by
    simp only [T, β1, β2, map_sub, sub_apply]; ring
  -- Step 9: the triangle inequality.
  rw [hid]
  have hP0 : 0 ≤ ‖P‖ := norm_nonneg P
  have hCH : 0 ≤ C * (H * t) := mul_nonneg hC (mul_nonneg hH0 ht0)
  have hCS : 0 ≤ C * S' := mul_nonneg hC hS'0
  have e1 : |β1 Qx P| ≤ C * (H * t) * Sv * ‖P‖ :=
    hβ1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxb hCH) hP0)
  have e2 : |β2 (Qx - Qy) P| ≤ C * S' * (Hv * t) * ‖P‖ :=
    hβ2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxy hCS) hP0)
  calc |T P - β1 Qx P - β2 (Qx - Qy) P|
      ≤ |T P - β1 Qx P| + |β2 (Qx - Qy) P| := abs_sub _ _
    _ ≤ |T P| + |β1 Qx P| + |β2 (Qx - Qy) P| := by
        gcongr; exact abs_sub _ _
    _ ≤ C * (H * t) * ‖P‖ + C * (H * t) * Sv * ‖P‖ + C * S' * (Hv * t) * ‖P‖ := by
        gcongr
    _ = C * (H + H * Sv + S' * Hv) * t * ‖P‖ := by ring
/-- Difference-quotient step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
`d`-uniform bounds for `w_d = d⁻¹ (v(· + d e) - v)` and for the forcing term `F_d` of its system on
`B̆_{2R}(xb)`.  Claims (i)–(iv) hold with the `d`-independent bound `S` of
`dohr_eb_lhr_dqub_wd_props`, claim (v) with the `d`-independent constant `M'` of
`dohr_eb_lhr_dqub_forcing_holder`; `M := max S M'` serves both, as `‖x - y‖ ^ α * ‖P‖ ≥ 0`. -/
theorem dohr_eb_lhr_dq_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), 0 < α → α ≤ 1 → IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ M) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ (∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α) ∧ ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R _ _ hU hR hBU he ha hΦ hv
  -- Steps 6–8: `w_d` is bounded by `S`, `C¹`, has the stated derivative, and `Dw_d` is Hölder.
  obtain ⟨S, hS⟩ := Submission.dohr_eb_lhr_dqub_wd_props n ℓ α U v xb e R hU hR hBU he hv
  -- Step 9: the forcing term is `α`-Hölder in `x` with the constant `M'`.
  obtain ⟨M', hM'⟩ :=
    Submission.dohr_eb_lhr_dqub_forcing_holder n ℓ α U a Φ v xb e R hU hR hBU he ha hΦ hv
  -- Step 10: `M := max S M'` does not depend on `d`.
  refine ⟨max S M', fun d hd hdR => ?_⟩
  obtain ⟨hw, hC1, hDw, hHol⟩ := hS d hd hdR
  refine ⟨fun x hx => (hw x hx).trans (le_max_left S M'), hC1, hDw, hHol,
    fun x hx y hy P => (hM' d hd hdR x hx y hy P).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right S M')
    (Real.rpow_nonneg (norm_nonneg (x - y)) α)) (norm_nonneg P)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a `C¹` map
into a normed space.**
If `g : ℝⁿ → E` is `C¹` on an open `U` and `K ⊆ U` is compact, then for every direction `e` the
difference quotients `d⁻¹ (g(x + d e) − g(x))` converge to `Dg(x) e` uniformly on `K` as `d → 0`,
`d ≠ 0`.  The codomain `E` is an arbitrary real normed space (e.g. `L(ℝⁿ, ℝ^ℓ)` for `g = Dv`).
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Dg` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Dg(w) − Dg(x)‖ < η/(|e| + 1)` whenever
`w, x ∈ K_ε` and `|w − x| < θ`.  For `0 < |d| < min(ε, θ)/(|e| + 1)` and `x ∈ K`, the segment
`[x, x + d e]` lies in `B_{|d e|}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Dg(x)` gives `‖g(x + d e) − g(x) − Dg(x)(d e)‖ ≤ η |d| |e|/(|e| + 1)`; dividing by `|d|`,
`‖Dg(x) e − d⁻¹ (g(x + d e) − g(x))‖ ≤ η |e|/(|e| + 1) < η`. -/
theorem dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn n → E) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 g U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (g (x + d • e) - g x)) (fun x => fderiv ℝ g x e) (𝓝[≠] 0) K := by
  intro n E _ _ g U K e hU hg hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `g` is differentiable on `U` and `Dg` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ g) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
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
  -- Step 5: the mean value inequality with the fixed linear map `Dg(x)`.
  have hmvt : ‖g (x + d • e) - g x - fderiv ℝ g x ((x + d • e) - x)‖ ≤
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
  have hrw : fderiv ℝ g x e - d⁻¹ • (g (x + d • e) - g x) =
      -(d⁻¹ • (g (x + d • e) - g x - fderiv ℝ g x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (g (x + d • e) - g x) (d • fderiv ℝ g x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖g (x + d • e) - g x - fderiv ℝ g x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients.**
If `f` is `C¹` on an open `U` and `K ⊆ U` is compact, then for every direction `e` the difference
quotients `g_d(x) = d⁻¹ (f(x + d e) − f(x))` converge to `Df(x) e` uniformly on `K` as `d → 0`,
`d ≠ 0`.
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Df` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Df(w) − Df(x)‖ < η/(|e| + 1)` whenever
`w, x ∈ K_ε` and `|w − x| < θ`.  For `0 < |d| < min(ε, θ)/(|e| + 1)` and `x ∈ K`, the segment
`[x, x + d e]` lies in `B_{|d e|}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Df(x)` gives `|f(x + d e) − f(x) − Df(x)(d e)| ≤ η |d| |e|/(|e| + 1)`; dividing by `|d|`,
`|Df(x) e − g_d(x)| ≤ η |e|/(|e| + 1) < η`. -/
theorem dohr_eb_dql_diffQuot_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (f (x + d • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K := by
  intro n ℓ f U K e hU hf hK hKU
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
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the derivative of a directional
derivative of a `C²` map.**
If `v : ℝⁿ → ℝ^ℓ` is `C²` on an open `U` and `e ∈ ℝⁿ`, then at every `x ∈ U` the directional
derivative `v_e(z) = Dv(z) e` has derivative `D(v_e)(x) = D(Dv)(x) e` (symmetry of the second
derivative, proved here by difference quotients since `FDeriv.Symmetric` is not imported).
Proof: choose `r > 0` with `B_r(x) ⊆ U`.  By `dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn` for the
`C¹` map `Dv`, `T_d = d⁻¹ (Dv(· + d e) − Dv) → D(Dv)(·) e` uniformly on `B_r(x)` as `d → 0`,
`d ≠ 0`.  For `|d| < (r/2)/(‖e‖ + 1)` and `z ∈ B̆_{r/2}(x)` the points `z`, `z + d e` lie in `U`, so
`w_d = d⁻¹ (v(· + d e) − v)` has derivative `T_d(z)` at `z`.  For `y ∈ U`, `w_d(y) → Dv(y) e` (slope
of `t ↦ v(y + t e)` at `0`).  The theorem on uniform limits of derivatives
(`hasFDerivAt_of_tendstoUniformlyOnFilter`) gives `D(v_e)(x) = D(Dv)(x) e`. -/
theorem dohr_eb_lhr_ds_fderiv_dirDeriv_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → ContDiffOn ℝ 2 v U → ∀ x ∈ U, fderiv ℝ (fun z => fderiv ℝ v z e) x = fderiv ℝ (fderiv ℝ v) x e := by
  intro n ℓ U v e hU hv x hx
  -- Step 1: a closed ball `B_r(x) ⊆ U`; `v` is differentiable on `U` and `Dv` is `C¹` on `U`.
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ v z := fun z hz =>
    (hv.differentiableOn two_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  -- Steps 2–3: `T_d → D(Dv)(·) e` uniformly on `B_r(x)`, hence uniformly on the filter `𝓝 x`.
  have hunif : TendstoUniformlyOn
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (closedBall x r) :=
    Submission.dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn n (Rn n →L[ℝ] Rn ℓ) (fderiv ℝ v) U
      (closedBall x r) e hU hDv (isCompact_closedBall x r) hrU
  have hunif' : TendstoUniformlyOnFilter
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (𝓝 x) :=
    hunif.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr (closedBall_mem_nhds x hr))
  -- Step 4: `w_d` has derivative `T_d(z)` at `z` for `|d| < (r/2)/(‖e‖ + 1)`, `z ∈ B̆_{r/2}(x)`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hρ : 0 < r / 2 / (‖e‖ + 1) := by positivity
  have hdev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < r / 2 / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with d hd
    simpa [Real.dist_eq] using hd
  have hzev : ∀ᶠ z in 𝓝 x, z ∈ ball x (r / 2) := Metric.ball_mem_nhds x (half_pos hr)
  have hderiv : ∀ᶠ p : ℝ × Rn n in 𝓝[≠] 0 ×ˢ 𝓝 x,
      HasFDerivAt (fun z => p.1⁻¹ • (v (z + p.1 • e) - v z))
        (p.1⁻¹ • (fderiv ℝ v (p.2 + p.1 • e) - fderiv ℝ v p.2)) p.2 := by
    filter_upwards [hdev.prod_mk hzev] with p hp
    obtain ⟨d, z⟩ := p
    obtain ⟨hd, hz⟩ := hp
    have hzr : dist z x < r / 2 := hz
    have hzU : z ∈ U := hrU (mem_closedBall.mpr (hzr.le.trans (half_le_self hr.le)))
    have hde : ‖d • e‖ < r / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
        _ < r / 2 / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
        _ = r / 2 := div_mul_cancel₀ _ he1.ne'
    have hzdU : z + d • e ∈ U := by
      refine hrU (mem_closedBall.mpr ?_)
      calc dist (z + d • e) x = ‖(z - x) + d • e‖ := by rw [dist_eq_norm, add_sub_right_comm]
        _ ≤ ‖z - x‖ + ‖d • e‖ := norm_add_le _ _
        _ ≤ r := by rw [← dist_eq_norm]; linarith
    -- chain rule for the translation `z ↦ z + d e`, then difference and constant multiple rules
    have htr : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (z + d • e)) z :=
      (hasFDerivAt_comp_add_right (d • e)).mpr (hdiff _ hzdU).hasFDerivAt
    exact (htr.sub (hdiff z hzU).hasFDerivAt).const_smul d⁻¹
  -- Step 5: `w_d(y) → Dv(y) e` for every `y ∈ U`: slopes of `t ↦ v(y + t e)` at `t = 0`.
  have hpt : ∀ᶠ y in 𝓝 x,
      Tendsto (fun d : ℝ => d⁻¹ • (v (y + d • e) - v y)) (𝓝[≠] 0) (𝓝 (fderiv ℝ v y e)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hline : HasDerivAt (fun t : ℝ => y + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    have hvy : HasFDerivAt v (fderiv ℝ v y) (y + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact (hdiff y hy).hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => v (y + t • e)) (fderiv ℝ v y e) 0 :=
      hvy.comp_hasDerivAt (0 : ℝ) hline
    simpa using hcomp.tendsto_slope_zero
  -- Step 6: uniform limits of derivatives (`f d = w_d`, `f' d = T_d`, `g = v_e`).
  exact (hasFDerivAt_of_tendstoUniformlyOnFilter
    (f := fun (d : ℝ) (z : Rn n) => d⁻¹ • (v (z + d • e) - v z))
    (f' := fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
    (g := fun z => fderiv ℝ v z e) (g' := fun z => fderiv ℝ (fderiv ℝ v) z e)
    hunif' hderiv hpt).fderiv
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): families of linear forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)` and let `Φ : ℝⁿ → L* = L(L, ℝ)` be such that `x ↦ Φ(x)[P]` is `C¹` on an
open `U` for every `P ∈ L`.  Then `Φ` is `C¹` on `U` as an `L*`-valued map, and
`(DΦ(x) e)[P] = D(Φ(·)[P])(x) e` for all `x ∈ U`, `e ∈ ℝⁿ` and `P ∈ L`.
Proof: `L` is finite-dimensional; with a basis `E_r` of `L` and its continuous coordinate forms
`π_r`, linearity gives `Φ(x)[P] = Σ_r π_r(P) Φ(x)[E_r]`, so `Φ(x) = Σ_r Φ(x)[E_r] π_r` is a finite
sum of the constant forms `π_r` times `C¹` scalar functions, and `Φ` is `C¹` on `U`.  For `x ∈ U`,
`Φ` is differentiable at `x`, and the product rule for evaluation at the constant `P` gives
`D(Φ(·)[P])(x) = (DΦ(x)).flip P`. -/
theorem dohr_eb_lhr_ds_clm_family : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 1 Φ U ∧ ∀ x ∈ U, ∀ (e : Rn n) (P : Rn n →L[ℝ] Rn ℓ), fderiv ℝ Φ x e P = fderiv ℝ (fun z => Φ z P) x e := by
  intro n ℓ U Φ hU hΦ
  -- Step 1: a basis `b` of `L` and its continuous coordinate forms `π r`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  -- Step 2: `Φ(x) = Σ_r Φ(x)[b r] π r` in `L*`, by linearity of `Φ(x)`; the summand is written
  -- `(π r).smulRight (Φ x (b r)) : P ↦ π r P • Φ x (b r)`, so no scalar action on `L*` is needed.
  have hexp : ∀ x, Φ x = ∑ r, (π r).smulRight (Φ x (b r)) := by
    intro x
    ext P
    have hP : Φ x P = Φ x (∑ r, b.repr P r • b r) := by rw [b.sum_repr]
    rw [hP, map_sum]
    simp [map_smul, π]
  -- Step 3: each summand is `C¹` (constant form, `C¹` coefficient), hence so are the sum and `Φ`.
  have hC1 : ContDiffOn ℝ 1 Φ U := by
    have h : ContDiffOn ℝ 1 (fun x => ∑ r, (π r).smulRight (Φ x (b r))) U :=
      ContDiffOn.sum fun r _ => contDiffOn_const.smulRight (hΦ (b r))
    exact h.congr fun x _ => hexp x
  refine ⟨hC1, fun x hx e P => ?_⟩
  -- Step 4: differentiate the evaluation `z ↦ Φ(z)[P]` at the constant `P`.
  have hd : DifferentiableAt ℝ Φ x :=
    (hC1.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  rw [fderiv_clm_apply hd (differentiableAt_const P)]
  simp
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): Leibniz rule for a family of bilinear
forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)`, let `a : ℝⁿ → L(L, L*)` be such that `x ↦ a(x)[P][Q]` is `C¹` on an open `U`
for all `P, Q ∈ L`, and let `w : ℝⁿ → L` be `C¹` on `U`.  Then `x ↦ a(x)[w(x)]` is `C¹` on `U` as an
`L*`-valued map, and for `x ∈ U`, `P ∈ L` and `e ∈ ℝⁿ`,
`(D(a(·)[w(·)])(x) e)[P] = a(x)[Dw(x) e][P] + D(a(·)[w(x)][P])(x) e`, with `w(x)` frozen in the
last term.
Proof: with a basis `E_r` of `L` and its continuous coordinate forms `π_r`, linearity gives
`a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.  So each evaluation `z ↦ a(z)[w(z)][P]` is a finite sum of
products of `C¹` functions, and `dohr_eb_lhr_ds_clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map
with `(D(a(·)[w(·)])(x) e)[P] = D(a(·)[w(·)][P])(x) e`.  The product and sum rules give
`D(a(·)[w(·)][P])(x) e = Σ_r π_r(w(x)) · D(a(·)[E_r][P])(x) e + Σ_r π_r(Dw(x) e) · a(x)[E_r][P]`;
by the expansion the second sum is `a(x)[Dw(x) e][P]`, and the first is `D(a(·)[w(x)][P])(x) e`. -/
theorem dohr_eb_lhr_ds_bilin_leibniz : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → (Rn n →L[ℝ] Rn ℓ)) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ContDiffOn ℝ 1 w U → ContDiffOn ℝ 1 (fun x => a x (w x)) U ∧ ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun z => a z (w z)) x e P = a x (fderiv ℝ w x e) P + fderiv ℝ (fun z => a z (w x) P) x e := by
  intro n ℓ U a w e hU ha hw
  -- Step 1: a basis `E_r = b r` of `L` with continuous coordinate forms `π r`, and the expansion
  -- `a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  have hexp : ∀ z Q P, a z Q P = ∑ r, π r Q * a z (b r) P := by
    intro z Q P
    have hQ : a z Q = a z (∑ r, b.repr Q r • b r) := by rw [b.sum_repr]
    rw [hQ, map_sum, sum_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rfl
  -- Step 2: each evaluation `z ↦ a(z)[w(z)][P] = Σ_r π_r(w(z)) · a(z)[E_r][P]` is `C¹` on `U`, so
  -- `clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map into `L*` and reduces the derivative identity
  -- to the evaluation at `P`.
  have hπw : ∀ r, ContDiffOn ℝ 1 (fun z => π r (w z)) U := fun r =>
    (π r).contDiff.comp_contDiffOn hw
  have hC1P : ∀ P, ContDiffOn ℝ 1 (fun z => a z (w z) P) U := fun P =>
    (ContDiffOn.sum fun r _ => (hπw r).mul (ha (b r) P)).congr fun z _ => hexp z (w z) P
  obtain ⟨hC1, hcf⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (w z)) hU hC1P
  refine ⟨hC1, fun x hx P => ?_⟩
  rw [hcf x hx e P]
  -- Step 3: product and sum rules for the expansion of `z ↦ a(z)[w(z)][P]`.
  have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
  have hdw : HasFDerivAt w (fderiv ℝ w x) x :=
    ((hw.differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hdA : ∀ r, HasFDerivAt (fun z => a z (b r) P) (fderiv ℝ (fun z => a z (b r) P) x) x :=
    fun r => (((ha (b r) P).differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hD : HasFDerivAt (fun z => a z (w z) P)
      (∑ r, (π r (w x) • fderiv ℝ (fun z => a z (b r) P) x
        + a x (b r) P • (π r).comp (fderiv ℝ w x))) x := by
    rw [show (fun z => a z (w z) P) = fun z => ∑ r, π r (w z) * a z (b r) P from
      funext fun z => hexp z (w z) P]
    exact HasFDerivAt.fun_sum fun r _ => ((π r).hasFDerivAt.comp x hdw).mul (hdA r)
  -- Step 4: the derivative of `z ↦ a(z)[w(x)][P]`, with `w(x)` frozen.
  have hF : HasFDerivAt (fun z => a z (w x) P)
      (∑ r, π r (w x) • fderiv ℝ (fun z => a z (b r) P) x) x := by
    rw [show (fun z => a z (w x) P) = fun z => ∑ r, π r (w x) * a z (b r) P from
      funext fun z => hexp z (w x) P]
    exact HasFDerivAt.fun_sum fun r _ => (hdA r).const_mul (π r (w x))
  -- Step 5: by the expansion, the two sums are `a(x)[Dw(x) e][P]` and `D(a(·)[w(x)][P])(x) e`.
  rw [hD.fderiv, hF.fderiv, hexp x (fderiv ℝ w x e) P]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Finset.sum_add_distrib, mul_comm (a x (b _) P)]
  ring
/-- Differentiated system in the linear higher-regularity step of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): translating the test functions of a weak
identity.  If `∫_U ω₁(x)[Dφ(x)] dx = ∫_U ω₂(x)[Dφ(x)] dx` for every `C¹` compactly supported
`φ` with `spt φ ⊆ U`, and `ζ` is `C¹` with compact support and `spt ζ + s e ⊆ U`, then
`∫ ω₁(y + s e)[Dζ(y)] dy = ∫ ω₂(y + s e)[Dζ(y)] dy`.
Proof: test with `φ(x) = ζ(x − s e)`, which is `C¹` with compact support,
`spt φ = spt ζ + s e ⊆ U` and `Dφ(x) = Dζ(x − s e)`.  The integrands `ω_i(x)[Dφ(x)]` vanish off
`U`, so the integrals over `U` are whole-space integrals, and the substitution `x = y + s e`
(translation invariance of Lebesgue measure) turns them into `∫ ω_i(y + s e)[Dζ(y)] dy`.  No
integrability or measurability is needed. -/
theorem dohr_eb_lhr_ds_translate_weak_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n) (s : ℝ) (ζ : Rn n → Rn ℓ), (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y ∈ tsupport ζ, y + s • e ∈ U) → ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y) = ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y) := by
  intro n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc hζU
  -- Step 1: the translated test function `φ = ζ ∘ τ`, `τ x = x − s e`, is `C¹` with compact
  -- support.
  let φ : Rn n → Rn ℓ := ζ ∘ Homeomorph.subRight (s • e)
  have hφC : ContDiff ℝ 1 φ := hζ.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hζc.comp_homeomorph _
  -- Step 2: `tsupport φ = τ⁻¹(tsupport ζ) ⊆ U`.
  have hφU : tsupport φ ⊆ U := by
    intro x hx
    rw [tsupport_comp_eq_preimage] at hx
    simpa using hζU _ hx
  -- Step 3: `Dφ(x) = Dζ(x − s e)`.
  have hDφ : ∀ x, fderiv ℝ φ x = fderiv ℝ ζ (x - s • e) := fun x =>
    fderiv_comp_sub (f := ζ) (s • e)
  -- Steps 4–5: the integrand vanishes off `U`, and `x = y + s e` turns the whole-space integral
  -- into the translated one.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∫ x in U, ω x (fderiv ℝ φ x) = ∫ y, ω (y + s • e) (fderiv ℝ ζ y) := by
    intro ω
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [← integral_add_right_eq_self (fun x => ω x (fderiv ℝ φ x)) (s • e)]
      congr 1
      funext y
      rw [hDφ, add_sub_cancel_right]
    · intro x hx
      have hx' : x - s • e ∉ tsupport ζ := fun h => hx (by simpa using hζU _ h)
      rw [hDφ, fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 6: combine with the weak identity for `φ`.
  rw [← key ω₁, ← key ω₂]
  exact hweak φ hφC hφc hφU
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): differentiating a weak identity.**
Let `ω₁, ω₂ : ℝⁿ → L*` (`L = L(ℝⁿ, ℝ^ℓ)`) be `C¹` on the open set `U` and satisfy
`∫_U ω₁[Dφ] = ∫_U ω₂[Dφ]` for every `φ ∈ C¹_c(U; ℝ^ℓ)`.  Then for every direction `e` and every
`ζ ∈ C¹_c(U; ℝ^ℓ)` the functions `F_i = (Dω_i e)[Dζ]` are integrable on `U` and
`∫_U F₁ = ∫_U F₂`.
Proof: `K = spt ζ` has a compact thickening `K₁ = cthickening δ K ⊆ U`, and `y + s e ∈ K₁` for
`y ∈ K`, `|s| < ε = δ/(|e| + 1)`.  The translated integrands `ω_i(y + s e)[Dζ(y)]` and
`(Dω_i(y + s e) e)[Dζ(y)]` are continuous with support in `K`.  By the translated weak identity
(`dohr_eb_lhr_ds_translate_weak_eq`), `I_i(s) = ∫ ω_i(y + s e)[Dζ(y)] dy` satisfy `I₁ = I₂` for
`|s| < ε`.  Differentiating under the integral sign, with the integrable bound `C_i |Dζ|` where
`C_i` bounds `|Dω_i(z) e|` on `K₁`, gives `I_i'(0) = ∫ F_i` and the integrability of `F_i`;
hence `∫ F₁ = ∫ F₂`.  The `F_i` vanish off `K ⊆ U`, so the integrals over `U` agree. -/
theorem dohr_eb_lhr_ds_weak_eq_fderiv : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 ω₁ U → ContDiffOn ℝ 1 ω₂ U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → IntegrableOn (fun x => fderiv ℝ ω₁ x e (fderiv ℝ ζ x)) U ∧ IntegrableOn (fun x => fderiv ℝ ω₂ x e (fderiv ℝ ζ x)) U ∧ ∫ x in U, fderiv ℝ ω₁ x e (fderiv ℝ ζ x) = ∫ x in U, fderiv ℝ ω₂ x e (fderiv ℝ ζ x) := by
  intro n ℓ U ω₁ ω₂ e hU hω₁ hω₂ hweak ζ hζ hζc hζU
  -- Step 1: a compact thickening `K₁ = cthickening δ K` of `K = tsupport ζ` inside `U`, and
  -- `ε = δ / (‖e‖ + 1)`, so that `y + s • e ∈ K₁` for `y ∈ K` and `|s| < ε`.
  have hK : IsCompact (tsupport ζ) := hζc
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hζU
  have hK₁ : IsCompact (cthickening δ (tsupport ζ)) := hK.cthickening
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (‖e‖ + 1) = δ :=
    ⟨δ / (‖e‖ + 1), div_pos hδ he1, div_mul_cancel₀ δ he1.ne'⟩
  have hmemK₁ : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε,
      y + s • e ∈ cthickening δ (tsupport ζ) := by
    intro y hy s hs
    refine mem_cthickening_of_dist_le _ y δ _ hy ?_
    rw [mem_ball, Real.dist_eq, sub_zero] at hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← hεδ]
    exact mul_le_mul hs.le (by linarith) (norm_nonneg e) hε.le
  have hmemU : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε, y + s • e ∈ U :=
    fun y hy s hs => hδU (hmemK₁ y hy s hs)
  -- `Dζ` is continuous, vanishes off `K`, and `‖Dζ‖` is integrable.
  have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hDζint : Integrable (fun y => ‖fderiv ℝ ζ y‖) :=
    (hDζc.integrable_of_hasCompactSupport (hζc.fderiv ℝ)).norm
  -- Integrands `y ↦ G y (Dζ y)` are supported in `K`.
  have hsupp : ∀ G : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      Function.support (fun y => G y (fderiv ℝ ζ y)) ⊆ tsupport ζ := by
    intro G y hy
    by_contra hyK
    exact hy (by simp only [hDζ0 y hyK, ContinuousLinearMap.map_zero])
  -- Step 3: for `|s| < ε` the translated integrands are continuous (with support in `K`).
  have hcont : ∀ s ∈ ball (0 : ℝ) ε, ∀ g : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContinuousOn g U →
      Continuous (fun y => g (y + s • e) (fderiv ℝ ζ y)) := by
    intro s hs g hg
    have htr : Continuous (fun y : Rn n => y + s • e) := continuous_id.add continuous_const
    refine ContinuousOn.continuous_of_tsupport_subset (s := (fun y => y + s • e) ⁻¹' U)
      ((hg.comp htr.continuousOn (fun y hy => hy)).clm_apply hDζc.continuousOn)
      (hU.preimage htr) ?_
    exact (closure_minimal (hsupp (fun y => g (y + s • e))) (isClosed_tsupport ζ)).trans
      (fun y hy => hmemU y hy s hs)
  -- Steps 2 and 5, for a single `ω`: `I(s) = ∫ ω(y + s • e)[Dζ y] dy` has derivative
  -- `∫ (Dω(y) e)[Dζ y] dy` at `0`, and this integrand is integrable.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContDiffOn ℝ 1 ω U →
      Integrable (fun y => fderiv ℝ ω y e (fderiv ℝ ζ y)) ∧
      HasDerivAt (fun s : ℝ => ∫ y, ω (y + s • e) (fderiv ℝ ζ y))
        (∫ y, fderiv ℝ ω y e (fderiv ℝ ζ y)) 0 := by
    intro ω hω
    -- Step 2: `ω` and `z ↦ Dω(z) e` are continuous on `U`; `‖Dω(z) e‖ ≤ C` on `K₁`.
    have hωc : ContinuousOn ω U := hω.continuousOn
    have hDωe : ContinuousOn (fun z => fderiv ℝ ω z e) U :=
      (hω.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    obtain ⟨C, hC⟩ := hK₁.exists_bound_of_continuousOn (E := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (hDωe.mono hδU)
    have hball : ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := ball_mem_nhds 0 hε
    have h0 : (0 : ℝ) ∈ ball (0 : ℝ) ε := mem_ball_self hε
    -- (a) the pointwise derivative in `s` (chain rule, then evaluation at the constant `Dζ y`)
    have hderiv : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        HasDerivAt (fun σ : ℝ => ω (y + σ • e) (fderiv ℝ ζ y))
          (fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)) s := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have hz := ((hω.differentiableOn one_ne_zero _ (hmemU y hy s hs)).differentiableAt
          (hU.mem_nhds (hmemU y hy s hs))).hasFDerivAt
        have hline : HasDerivAt (fun σ : ℝ => y + σ • e) e s :=
          (((hasDerivAt_id' s).smul_const e).const_add y).congr_deriv (one_smul ℝ e)
        refine (HasDerivAt.clm_apply (c := fun σ : ℝ => ω (y + σ • e))
          (u := fun _ : ℝ => fderiv ℝ ζ y) (hz.comp_hasDerivAt s hline)
          (hasDerivAt_const s (fderiv ℝ ζ y))).congr_deriv ?_
        simp only [ContinuousLinearMap.map_zero, add_zero]
      · simp only [hDζ0 y hy, ContinuousLinearMap.map_zero]
        exact hasDerivAt_const s 0
    -- (b) domination by the integrable bound `C ‖Dζ‖`
    have hbound : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖ ≤ C * ‖fderiv ℝ ζ y‖ := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have h1 := hC (y + s • e) (hmemK₁ y hy s hs)
        calc ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖
            ≤ ‖fderiv ℝ ω (y + s • e) e‖ * ‖fderiv ℝ ζ y‖ :=
              (fderiv ℝ ω (y + s • e) e).le_opNorm _
          _ ≤ C * ‖fderiv ℝ ζ y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · rw [hDζ0 y hy, ContinuousLinearMap.map_zero, norm_zero, norm_zero, mul_zero]
    -- (c) differentiation under the integral sign
    obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (s : ℝ) (y : Rn n) => ω (y + s • e) (fderiv ℝ ζ y))
      (F' := fun (s : ℝ) (y : Rn n) => fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y))
      (bound := fun y => C * ‖fderiv ℝ ζ y‖) hball
      (Filter.eventually_of_mem hball fun s hs => (hcont s hs ω hωc).aestronglyMeasurable)
      ((hcont 0 h0 ω hωc).integrable_of_hasCompactSupport (hζc.mono' (hsupp _)))
      (hcont 0 h0 _ hDωe).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y s hs => hbound y s hs)
      (hDζint.const_mul C)
      (Filter.Eventually.of_forall fun y s hs => hderiv y s hs)
    simp only [zero_smul, add_zero] at hint hder
    exact ⟨hint, hder⟩
  obtain ⟨hint₁, hder₁⟩ := key ω₁ hω₁
  obtain ⟨hint₂, hder₂⟩ := key ω₂ hω₂
  -- Step 4: the translated weak identity gives `I₁ = I₂` near `0`.
  have heq : (fun s : ℝ => ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y)) =ᶠ[𝓝 0]
      (fun s : ℝ => ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y)) := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs
    exact Submission.dohr_eb_lhr_ds_translate_weak_eq n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc
      (fun y hy => hmemU y hy s hs)
  -- Step 6: hence the derivatives at `0` agree.
  have hD : ∫ y, fderiv ℝ ω₁ y e (fderiv ℝ ζ y) = ∫ y, fderiv ℝ ω₂ y e (fderiv ℝ ζ y) :=
    (hder₁.congr_of_eventuallyEq heq.symm).unique hder₂
  -- Step 7: the integrands vanish off `U`.
  have hzero : ∀ (ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (x : Rn n), x ∉ U →
      fderiv ℝ ω x e (fderiv ℝ ζ x) = 0 := by
    intro ω x hx
    rw [hDζ0 x (fun hxK => hx (hζU hxK)), ContinuousLinearMap.map_zero]
  refine ⟨hint₁.integrableOn, hint₂.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₁),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₂)]
  exact hD
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the differentiated system.**
Let `a(x)` be bilinear forms and `Φ(x)` linear forms on `L = L(ℝⁿ, ℝ^ℓ)`, componentwise `C¹` on
the open set `U`, and let `v ∈ C²(U)` solve `∫_U a(x)[Dv(x)][Dζ(x)] = ∫_U Φ(x)[Dζ(x)]` for all
`ζ ∈ C¹_c(U)`.  Then `v_e = Dv(·) e` solves `∫_U a(x)[Dv_e(x)][Dζ(x)] = ∫_U Ψ(x)[Dζ(x)]` with
`Ψ(x)[P] = D(Φ(·)[P])(x) e − D(a(·)[Dv(x)][P])(x) e` on `U`.
Proof: put `ω₁ = a(·)[Dv(·)]`, `ω₂ = Φ` (both `C¹` into `L*`) and
`Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e`, which has the stated values since evaluation commutes with
differentiation.  Differentiating the weak identity `∫_U ω₁[Dζ] = ∫_U ω₂[Dζ]` in the direction
`e` gives `∫_U (Dω₁ e)[Dζ] = ∫_U (DΦ e)[Dζ]`, both integrands integrable on `U`.  On `U` the
Leibniz rule and `D v_e = D(Dv) e` give `(Dω₁ e)[Dζ] = a[Dv_e][Dζ] + c` and
`(DΦ e)[Dζ] = Ψ[Dζ] + c` with `c(x) = D(a(·)[Dv(x)][Dζ(x)])(x) e`.  If `c` is integrable on `U`,
subtract `∫_U c`; otherwise neither `a[Dv_e][Dζ]` nor `Ψ[Dζ]` is integrable on `U` and both
integrals vanish. -/
theorem dohr_eb_lhr_differentiated_system : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 2 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, Ψ x P = fderiv ℝ (fun z => Φ z P) x e - fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x) = ∫ x in U, Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v e hU ha hΦ hv hweak
  -- Step 1: `Φ` is `C¹` into `L*`, and so is the frozen family `z ↦ a(z)[Dv(x)]`; for both,
  -- evaluation at `P` commutes with differentiation.
  obtain ⟨hΦ1, hΦd⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U Φ hU hΦ
  have hfrozen : ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ,
      fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e P =
        fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e := fun x hx P =>
    (Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (fderiv ℝ v x)) hU
      (fun Q => ha (fderiv ℝ v x) Q)).2 x hx e P
  -- Step 2: `Dv` is `C¹` on `U`, so `ω₁ = a(·)[Dv(·)]` is `C¹` and obeys the Leibniz rule.
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨hω₁, hω₁d⟩ := Submission.dohr_eb_lhr_ds_bilin_leibniz n ℓ U a (fderiv ℝ v) e hU ha hDv
  -- Step 3: `Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e` has the stated values on `U`.
  refine ⟨fun x => fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e, ?_, ?_⟩
  · intro x hx P
    rw [sub_apply, hΦd x hx e P, hfrozen x hx P]
  intro ζ hζ hζc hζU
  -- Step 4: differentiate the weak identity for `(ω₁, Φ)` in the direction `e`.
  obtain ⟨hF₁, hF₂, hF⟩ := Submission.dohr_eb_lhr_ds_weak_eq_fderiv n ℓ U
    (fun x => a x (fderiv ℝ v x)) Φ e hU hω₁ hΦ1 hweak ζ hζ hζc hζU
  -- Step 5: on `U`, both integrands differ from the derivatives by the same term `c`.
  obtain ⟨c, hc⟩ : ∃ c : Rn n → ℝ,
      c = fun x => fderiv ℝ (fun z => a z (fderiv ℝ v x) (fderiv ℝ ζ x)) x e := ⟨_, rfl⟩
  have hU' : MeasurableSet U := hU.measurableSet
  have h₁ : EqOn (fun x => a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x))
      (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [hω₁d x hx (fderiv ℝ ζ x), Submission.dohr_eb_lhr_ds_fderiv_dirDeriv_eq n ℓ U v e hU hv x hx,
      add_sub_cancel_right]
  have h₂ : EqOn (fun x => (fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e)
      (fderiv ℝ ζ x)) (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [sub_apply, hfrozen x hx (fderiv ℝ ζ x)]
  rw [setIntegral_congr_fun hU' h₁, setIntegral_congr_fun hU' h₂]
  -- Step 6: subtract `∫_U c` if `c` is integrable on `U`; otherwise both sides are `0`.
  by_cases hcI : IntegrableOn c U
  · rw [integral_sub hF₁ hcI, integral_sub hF₂ hcI, hF]
  · have hn₁ : ¬ IntegrableOn
        (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₁.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    have hn₂ : ¬ IntegrableOn (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₂.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    rw [integral_undef hn₁, integral_undef hn₂]
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1 (pp. 127–128): local `C^{j,α}`
classes are closed under `h - ∑ᵢ fᵢ` and under modification outside the open set `U`.  If `h` and
every `fᵢ` are `C^j` on `U` with `Dʲ` `α`-Hölder on every compact `K ⊆ U`, and `g = h - ∑ᵢ fᵢ` on
`U`, then `g` is `C^j` on `U`; as `U` is open, `Dʲg = Dʲh - ∑ᵢ Dʲfᵢ` on `U`
(`Filter.EventuallyEq.iteratedFDeriv`), so the triangle inequality turns Hölder constants `C_h`,
`Cᵢ` on `K` into the constant `max C_h 0 + ∑ᵢ max Cᵢ 0` for `Dʲg`. -/
theorem dohr_eb_lhr_holder_loc_sub_sum : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j N : ℕ) (α : ℝ) (U : Set (Rn n)) (h g : Rn n → E) (f : Fin N → Rn n → E), IsOpen U → ContDiffOn ℝ j h U → (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α) → (∀ i : Fin N, ContDiffOn ℝ j (f i) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ x ∈ U, g x = h x - ∑ i, f i x) → ContDiffOn ℝ j g U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n E _ _ j N α U h g f hU hh hhol hf hg
  -- Step 1: `G := h - ∑ i, f i` is `C^j` on `U`.
  have hG : ContDiffOn ℝ j (fun x => h x - ∑ i, f i x) U :=
    hh.sub (ContDiffOn.sum fun i _ => (hf i).1)
  -- Step 2: on the open set `U`, `g = G` near each point, so `Dʲg = Dʲh - ∑ i, Dʲfᵢ` there.
  have hiter : ∀ x ∈ U, iteratedFDeriv ℝ j g x
      = iteratedFDeriv ℝ j h x - ∑ i, iteratedFDeriv ℝ j (f i) x := by
    intro x hx
    have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
    have heq : g =ᶠ[𝓝 x] fun z => h z - ∑ i, f i z := Filter.eventually_of_mem hxU hg
    have hfx : ∀ i ∈ (Finset.univ : Finset (Fin N)), ContDiffAt ℝ j (f i) x :=
      fun i _ => (hf i).1.contDiffAt hxU
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_sub_apply (hh.contDiffAt hxU) (ContDiffAt.sum hfx),
      iteratedFDeriv_fun_sum_apply hfx]
  refine ⟨hG.congr hg, fun K hK hKU => ?_⟩
  -- Step 3: Hölder constants of `Dʲh` and of every `Dʲfᵢ` on `K`, made nonnegative.
  obtain ⟨Ch, hCh⟩ := hhol K hK hKU
  choose Cf hCf using fun i => (hf i).2 K hK hKU
  refine ⟨max Ch 0 + ∑ i, max (Cf i) 0, fun x hx y hy => ?_⟩
  have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  -- Step 4: the triangle inequality.
  rw [hiter x (hKU hx), hiter y (hKU hy)]
  calc ‖(iteratedFDeriv ℝ j h x - ∑ i, iteratedFDeriv ℝ j (f i) x)
        - (iteratedFDeriv ℝ j h y - ∑ i, iteratedFDeriv ℝ j (f i) y)‖
      = ‖(iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y)
          - ∑ i, (iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y)‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖
          + ∑ i, ‖iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ max Ch 0 * ‖x - y‖ ^ α + ∑ i, max (Cf i) 0 * ‖x - y‖ ^ α := by
        gcongr with i
        · exact (hCh x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
        · exact (hCf i x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
    _ = (max Ch 0 + ∑ i, max (Cf i) 0) * ‖x - y‖ ^ α := by
        rw [add_mul, Finset.sum_mul]
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): under the change of variables `x = y + ρ z` with `ρ > 0`, which maps `B̆_r(0)` onto
`B̆_{ρr}(y)`, the Hölder bound `‖ρ g(y + ρ z) − ρ g(y + ρ z')‖ ≤ c ‖z − z'‖^α` on `B̆_r(0)` is
equivalent to the scale-weighted bound `ρ^{1+α} ‖g(x) − g(x')‖ ≤ c ‖x − x'‖^α` on `B̆_{ρr}(y)`,
because `ρ^{1+α} = ρ ρ^α` and `‖x − x'‖^α = ρ^α ‖z − z'‖^α`. -/
theorem dohr_eb_sch_ube_holder_rescale : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (y : Rn n) (ρ r α c : ℝ), 0 < ρ → ((∀ z ∈ ball (0 : Rn n) r, ∀ z' ∈ ball (0 : Rn n) r, ‖ρ • g (y + ρ • z) - ρ • g (y + ρ • z')‖ ≤ c * ‖z - z'‖ ^ α) ↔ ∀ x ∈ ball y (ρ * r), ∀ x' ∈ ball y (ρ * r), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ c * ‖x - x'‖ ^ α) := by
  intro n ℓ g y ρ r α c hρ
  -- Step 1: `ρ^α > 0`, `ρ^{1+α} = ρ ρ^α`, `‖(y + ρ z) − (y + ρ z')‖^α = ρ^α ‖z − z'‖^α` and
  -- `‖ρ A − ρ B‖ = ρ ‖A − B‖`.
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hnorm : ∀ z z' : Rn n, ‖(y + ρ • z) - (y + ρ • z')‖ ^ α = ρ ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg _)]
  have hsm : ∀ u v : Rn n →L[ℝ] Rn ℓ, ‖ρ • u - ρ • v‖ = ρ * ‖u - v‖ := by
    intro u v
    rw [show ρ • u - ρ • v = ρ • (u - v) from (smul_sub ρ u v).symm, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
  -- Step 2: `z(x) = ρ⁻¹ (x − y)` satisfies `y + ρ z(x) = x` and maps `B̆_{ρr}(y)` into `B̆_r(0)`.
  have hback : ∀ x : Rn n, y + ρ • (ρ⁻¹ • (x - y)) = x := by
    intro x
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hinball : ∀ x ∈ ball y (ρ * r), ρ⁻¹ • (x - y) ∈ ball (0 : Rn n) r := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ,
      inv_mul_lt_iff₀ hρ]
    exact hx
  constructor
  -- Step 3: (a) ⇒ (b), multiplying the bound at `z(x), z(x')` by `ρ^α > 0`.
  · intro h x hx x' hx'
    have h1 := h _ (hinball x hx) _ (hinball x' hx')
    rw [hback, hback, hsm] at h1
    have h2 := hnorm (ρ⁻¹ • (x - y)) (ρ⁻¹ • (x' - y))
    rw [hback, hback] at h2
    rw [hsplit, h2]
    calc ρ * ρ ^ α * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by ring
      _ ≤ ρ ^ α * (c * ‖ρ⁻¹ • (x - y) - ρ⁻¹ • (x' - y)‖ ^ α) := by gcongr
      _ = c * (ρ ^ α * ‖ρ⁻¹ • (x - y) - ρ⁻¹ • (x' - y)‖ ^ α) := by ring
  -- Step 4: (b) ⇒ (a), cancelling the factor `ρ^α > 0` in the bound at `y + ρ z, y + ρ z'`.
  · intro h z hz z' hz'
    have hmap : ∀ u ∈ ball (0 : Rn n) r, y + ρ • u ∈ ball y (ρ * r) := by
      intro u hu
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      rw [mem_ball_zero_iff] at hu
      exact mul_lt_mul_of_pos_left hu hρ
    have h1 := h _ (hmap z hz) _ (hmap z' hz')
    rw [hsplit, hnorm] at h1
    rw [hsm]
    have h2 : ρ ^ α * (ρ * ‖g (y + ρ • z) - g (y + ρ • z')‖) ≤ ρ ^ α * (c * ‖z - z'‖ ^ α) := by
      calc ρ ^ α * (ρ * ‖g (y + ρ • z) - g (y + ρ • z')‖)
          = ρ * ρ ^ α * ‖g (y + ρ • z) - g (y + ρ • z')‖ := by ring
        _ ≤ c * (ρ ^ α * ‖z - z'‖ ^ α) := h1
        _ = ρ ^ α * (c * ‖z - z'‖ ^ α) := by ring
    exact le_of_mul_le_mul_left h2 hρα
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): if `ρ > 0` and `|y₀| + ρ ≤ 1`, the rescaled data `a(y₀ + ρ z)`, `ρ Φ(y₀ + ρ z)` and
`w(y₀ + ρ z)` on `B̆₁(0)` satisfy the structure conditions of `a`, `Φ`, `w` with the same
constants.  The map `z ↦ y₀ + ρ z` sends `B̆₁(0)` into itself and multiplies distances by
`ρ ≤ 1`, so the Hölder quotients acquire the factors `ρ^α ≤ 1` and `ρ ρ^α ≤ 1`. -/
theorem dohr_eb_sch_ube_rescaled_structure : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (y₀ : Rn n) (ρ α lam M : ℝ), 0 < ρ → ‖y₀‖ + ρ ≤ 1 → 0 ≤ α → 0 ≤ M → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → (∀ z ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a (y₀ + ρ • z) P P) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q| ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |(ρ • Φ (y₀ + ρ • z)) P - (ρ • Φ (y₀ + ρ • z')) P| ≤ M * ‖z - z'‖ ^ α * ‖P‖) ∧ ∀ z ∈ ball (0 : Rn n) 1, ‖w (y₀ + ρ • z)‖ ≤ M := by
  intro n ℓ a Φ w y₀ ρ α lam M hρ hyρ hα hM h1 h2 h3 h4 h5
  -- Step 1: `0 < ρ ≤ 1`, hence `ρ^α ≤ 1`.
  have hρ1 : ρ ≤ 1 := by linarith [norm_nonneg y₀]
  have hρα : ρ ^ α ≤ 1 := Real.rpow_le_one hρ.le hρ1 hα
  have hρα0 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ.le α
  -- Step 2: `z ↦ y₀ + ρ z` maps `B̆₁(0)` into `B̆₁(0)`.
  have hmap : ∀ z ∈ ball (0 : Rn n) 1, y₀ + ρ • z ∈ ball (0 : Rn n) 1 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖y₀ + ρ • z‖ ≤ ‖y₀‖ + ‖ρ • z‖ := norm_add_le _ _
      _ = ‖y₀‖ + ρ * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ < ‖y₀‖ + ρ * 1 := by gcongr
      _ ≤ 1 := by linarith
  -- Step 3: `|(y₀ + ρ z) − (y₀ + ρ z')|^α = ρ^α |z − z'|^α`.
  have hdiff : ∀ z z' : Rn n, ‖(y₀ + ρ • z) - (y₀ + ρ • z')‖ ^ α = ρ ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg _)]
  -- Step 4: (i), (ii), (v) hold pointwise at `y₀ + ρ z ∈ B̆₁(0)`.
  refine ⟨fun z hz P => h1 _ (hmap z hz) P, fun z hz P Q => h2 _ (hmap z hz) P Q, ?_, ?_,
    fun z hz => h5 _ (hmap z hz)⟩
  -- Step 5: (iii), discarding the factor `ρ^α ≤ 1` as `M ≥ 0`.
  · intro z hz z' hz' P Q
    have h := h3 _ (hmap z hz) _ (hmap z' hz') P Q
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
        (norm_nonneg _)) (norm_nonneg _)
    calc |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q|
        ≤ M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = ρ ^ α * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := mul_le_mul_of_nonneg_right hρα hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := one_mul _
  -- Step 6: (iv), as `(ρ Φ(u))[P] = ρ Φ(u)[P]`, discarding the factor `ρ ρ^α ≤ 1`.
  · intro z hz z' hz' P
    have h := h4 _ (hmap z hz) _ (hmap z' hz') P
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ :=
      mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    have hρρ : ρ * ρ ^ α ≤ 1 := by nlinarith
    calc ρ * |Φ (y₀ + ρ • z) P - Φ (y₀ + ρ • z') P|
        ≤ ρ * (M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖) := by gcongr
      _ = (ρ * ρ ^ α) * (M * ‖z - z'‖ ^ α * ‖P‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖) := mul_le_mul_of_nonneg_right hρρ hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ := one_mul _
/-- One-step improvement of a scale-weighted Hölder bound (steps 3–5 of the absorption argument
for the interior `C^{1,α}` Schauder estimate on the unit ball, in the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1).  Let `g : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` (operator norm), `0 < α ≤ 1` and
`M, A, Q ≥ 0`; call `(y, ρ)` admissible if `ρ > 0` and `|y| + ρ ≤ 1`.  Assume
(P1) `ρ^{1+α} ‖g(x) − g(x')‖ ≤ Q |x − x'|^α` on `B̆_{ρ/2}(y)` for admissible `(y, ρ)`;
(P2) for admissible `(y, ρ)` and real `K`, if `‖g(x) − g(x')‖ ≤ K |x − x'|^α` on `B̆_ρ(y)`, then
`ρ^{1+α} ‖g(x) − g(x')‖ ≤ ((1/16) ρ^{1+α} K + A) |x − x'|^α` on `B̆_{ρ/2}(y)`;
(P3) `‖g(x)‖ ≤ 2M/t + t^α K` whenever `|x| + r ≤ 1`, `K ≥ 0`, `0 < t < r` and
`‖g(z) − g(z')‖ ≤ K |z − z'|^α` on `B̆_r(x)`.
Then for admissible `(y, ρ)`: `ρ ‖g(x)‖ ≤ 32 M + Q/4 + 16 A` on `B̆_{ρ/2}(y)`, and
`ρ^{1+α} ‖g(x) − g(x')‖ ≤ (Q/2 + 512 M + 32 A) |x − x'|^α` on `B̆_{ρ/2}(y)`. -/
theorem dohr_eb_sch_ube_holder_improvement : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A Q : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → 0 ≤ Q → (∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + Q / 4 + 16 * A) ∧ ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
  intro n ℓ g α M A Q hα0 hα1 hM hA hQ0 hP1 hP2 hP3 y ρ hρ hyρ
  -- Step 1: points `x` of `B̆_{ρ/2}(y)` have `|x| + ρ/2 < 1`.
  have hxnorm : ∀ x ∈ ball y (ρ / 2), ‖x‖ + ρ / 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    linarith
  -- Step 2: numerical facts about the powers.
  have hR : 0 < ρ ^ (1 + α) := Real.rpow_pos_of_pos hρ _
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have p2pos : (0:ℝ) < 2 ^ (1 + α) := by positivity
  have p4pos : (0:ℝ) < 4 ^ (1 + α) := by positivity
  have p2ne : (2:ℝ) ^ (1 + α) ≠ 0 := p2pos.ne'
  have p4ne : (4:ℝ) ^ (1 + α) ≠ 0 := p4pos.ne'
  have hRne : ρ ^ (1 + α) ≠ 0 := hR.ne'
  have p2le : (2:ℝ) ^ (1 + α) ≤ 4 := by
    calc (2:ℝ) ^ (1 + α) ≤ 2 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have p4le : (4:ℝ) ^ (1 + α) ≤ 16 := by
    calc (4:ℝ) ^ (1 + α) ≤ 4 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := by rw [Real.rpow_two]; norm_num
  have hH0 : 0 ≤ Q / 4 + 16 * A := by linarith
  -- Step 3: `ρ^{1+α} |g(z) − g(z')| ≤ (Q/4 + 16 A) |z − z'|^α` on `B̆_{ρ/8}(x)`, by (P1) at
  -- `(x, ρ/2)` and (P2) at `(x, ρ/4)`.
  have hsmall : ∀ x ∈ ball y (ρ / 2), ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
      ρ ^ (1 + α) * ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
    intro x hx z hz z' hz'
    have hx1 := hxnorm x hx
    have hρ2 : 0 < ρ / 2 := by positivity
    have hρ4 : 0 < ρ / 4 := by positivity
    have e2 : (ρ / 2) ^ (1 + α) = ρ ^ (1 + α) / 2 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have e4 : (ρ / 4) ^ (1 + α) = ρ ^ (1 + α) / 4 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have hpos2 : 0 < (ρ / 2) ^ (1 + α) := Real.rpow_pos_of_pos hρ2 _
    have hHolK : ∀ u ∈ ball x (ρ / 4), ∀ u' ∈ ball x (ρ / 4),
        ‖g u - g u'‖ ≤ Q / (ρ / 2) ^ (1 + α) * ‖u - u'‖ ^ α := by
      intro u hu u' hu'
      have e : ρ / 2 / 2 = ρ / 4 := by ring
      have h := hP1 x (ρ / 2) hρ2 hx1.le u (by rwa [e]) u' (by rwa [e])
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos2]
      linarith
    have hx4 : ‖x‖ + ρ / 4 ≤ 1 := by linarith
    have e8 : ρ / 4 / 2 = ρ / 8 := by ring
    have h1 := hP2 x (ρ / 4) (Q / (ρ / 2) ^ (1 + α)) hρ4 hx4 hHolK z (by rwa [e8])
      z' (by rwa [e8])
    rw [e4, e2] at h1
    have hd : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have key : 1 / 16 * (ρ ^ (1 + α) / 4 ^ (1 + α)) * (Q / (ρ ^ (1 + α) / 2 ^ (1 + α)))
        = Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) := by
      field_simp
    rw [key] at h1
    have h2 : ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
      have h3 := mul_le_mul_of_nonneg_left h1 p4pos.le
      calc ρ ^ (1 + α) * ‖g z - g z'‖
          = 4 ^ (1 + α) * (ρ ^ (1 + α) / 4 ^ (1 + α) * ‖g z - g z'‖) := by
            field_simp
        _ ≤ 4 ^ (1 + α) * ((Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) + A) * ‖z - z'‖ ^ α) := h3
        _ = (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
            field_simp
    calc ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := h2
      _ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd
          have q1 := mul_le_mul_of_nonneg_left p2le hQ0
          have q2 := mul_le_mul_of_nonneg_left p4le hA
          linarith
  -- Step 4: `ρ |g(x)| ≤ 32 M + (Q/4 + 16 A) / 16^α`, by (P3) with `r = ρ/8`, `t = ρ/16`.
  have hsupfine : ∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
    intro x hx
    have hx1 := hxnorm x hx
    have hK0 : 0 ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) := div_nonneg hH0 hR.le
    have hHol8 : ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
        ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) * ‖z - z'‖ ^ α := by
      intro z hz z' hz'
      have h := hsmall x hx z hz z' hz'
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    have h := hP3 x (ρ / 8) (ρ / 16) ((Q / 4 + 16 * A) / ρ ^ (1 + α)) (by linarith) hK0
      (by positivity) (by linarith) hHol8
    have e16 : (ρ / 16) ^ α = ρ ^ α / 16 ^ α := Real.div_rpow hρ.le (by norm_num) _
    rw [e16, hsplit] at h
    have p16 : (0:ℝ) < 16 ^ α := by positivity
    have p16ne : (16:ℝ) ^ α ≠ 0 := p16.ne'
    have hραne : ρ ^ α ≠ 0 := hρα.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    have hid : ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α)))
        = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
      field_simp
      ring
    calc ρ * ‖g x‖
        ≤ ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α))) :=
          mul_le_mul_of_nonneg_left h hρ.le
      _ = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := hid
  have h16 : (1:ℝ) ≤ 16 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  refine ⟨?_, ?_⟩
  -- Step 5: conclusion (a), since `16^α ≥ 1`.
  · intro x hx
    have h := hsupfine x hx
    have : (Q / 4 + 16 * A) / 16 ^ α ≤ Q / 4 + 16 * A := div_le_self hH0 h16
    linarith
  -- Step 6: conclusion (b), by cases `|x − x'| < ρ/8` (step 3) and `|x − x'| ≥ ρ/8` (step 4).
  · intro x hx x' hx'
    have hd : 0 ≤ ‖x - x'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcase : ‖x - x'‖ < ρ / 8
    · have hxin : x ∈ ball x (ρ / 8) := mem_ball_self (by positivity)
      have hx'in : x' ∈ ball x (ρ / 8) := by
        rw [mem_ball, dist_comm, dist_eq_norm]; exact hcase
      have h := hsmall x hx x hxin x' hx'in
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 4 + 16 * A) * ‖x - x'‖ ^ α := h
        _ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd; linarith
    · push Not at hcase
      have hdl : (ρ / 8) ^ α ≤ ‖x - x'‖ ^ α := Real.rpow_le_rpow (by positivity) hcase hα0.le
      have e8 : (ρ / 8) ^ α = ρ ^ α / 8 ^ α := Real.div_rpow hρ.le (by norm_num) _
      have p8 : (0:ℝ) < 8 ^ α := by positivity
      have p16 : (0:ℝ) < 16 ^ α := by positivity
      have hρα8 : ρ ^ α ≤ 8 ^ α * ‖x - x'‖ ^ α := by
        rw [e8, div_le_iff₀ p8] at hdl; linarith
      have h8 : (8:ℝ) ^ α ≤ 8 := by
        calc (8:ℝ) ^ α ≤ 8 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 8 := Real.rpow_one 8
      have h816 : (8:ℝ) ^ α ≤ 16 ^ α := Real.rpow_le_rpow (by norm_num) (by norm_num) hα0.le
      have hA1 : ρ ^ α ≤ 8 * ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h8 hd
        linarith
      have hA2 : ρ ^ α / 16 ^ α ≤ ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h816 hd
        rw [div_le_iff₀ p16]
        linarith
      have hsx := hsupfine x hx
      have hsx' := hsupfine x' hx'
      have htri : ‖g x - g x'‖ ≤ ‖g x‖ + ‖g x'‖ := norm_sub_le _ _
      calc ρ ^ (1 + α) * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by rw [hsplit]; ring
        _ ≤ ρ ^ α * (ρ * ‖g x‖ + ρ * ‖g x'‖) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left htri hρ.le
        _ ≤ ρ ^ α * (2 * (32 * M + (Q / 4 + 16 * A) / 16 ^ α)) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            linarith
        _ = 64 * M * ρ ^ α + 2 * (Q / 4 + 16 * A) * (ρ ^ α / 16 ^ α) := by ring
        _ ≤ 64 * M * (8 * ‖x - x'‖ ^ α) + 2 * (Q / 4 + 16 * A) * ‖x - x'‖ ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hA1 (by linarith))
              (mul_le_mul_of_nonneg_left hA2 (by linarith))
        _ = (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by ring
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): absorption by the best scale-weighted Hölder constant.  Call `(y, ρ)` admissible if
`ρ > 0` and `|y| + ρ ≤ 1`.  Let `Q` be the supremum of `0` and of the quotients
`ρ^{1+α} ‖g x - g x'‖ / |x - x'|^α` over admissible `(y, ρ)` and `x ≠ x'` in `B̆_{ρ/2}(y)`; it is
finite because `ρ^{1+α} ≤ 1` and `g` is `α`-Hölder on `B̆₁(0)`.  The one-step improvement
`dohr_eb_sch_ube_holder_improvement` for this `Q` gives `Q ≤ Q/2 + 512 M + 32 A`, so
`Q ≤ 1024 M + 64 A`, and the admissible pair `(0, 1)` gives both bounds on `B̆_{1/2}(0)`. -/
theorem dohr_eb_sch_ube_absorption : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖g x‖ ≤ 1024 * M + 64 * A) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖g x - g y‖ ≤ (1024 * M + 64 * A) * ‖x - y‖ ^ α := by
  intro n ℓ g α M A hα0 hα1 hM hA hK hP2 hP3
  obtain ⟨K0, hK0⟩ := hK
  -- Step 1: for admissible `(y, ρ)`, `B̆_{ρ/2}(y) ⊆ B̆₁(0)`.
  have hmem : ∀ (y : Rn n) (ρ : ℝ) (x : Rn n), 0 < ρ → ‖y‖ + ρ ≤ 1 → x ∈ ball y (ρ / 2) →
      x ∈ ball (0 : Rn n) 1 := by
    intro y ρ x hρ hyρ hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      _ < ‖y‖ + ρ / 2 := by linarith
      _ ≤ 1 := by linarith
  -- Step 2: `T` is `0` together with the scale-weighted Hölder quotients; it is bounded above
  -- by `max K0 0`, so `Q := sup T` is a real number `≥ 0`.
  let T : Set ℝ := {q | q = 0 ∨ ∃ (y : Rn n) (ρ : ℝ) (x x' : Rn n), 0 < ρ ∧ ‖y‖ + ρ ≤ 1 ∧
      x ∈ ball y (ρ / 2) ∧ x' ∈ ball y (ρ / 2) ∧ x ≠ x' ∧
      q = ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α}
  have hbdd : BddAbove T := by
    refine ⟨max K0 0, ?_⟩
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · exact le_max_right _ _
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      have hρa : ρ ^ (1 + α) ≤ 1 :=
        Real.rpow_le_one hρ.le (by linarith [norm_nonneg y]) (by linarith)
      rw [div_le_iff₀ hpow]
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ 1 * ‖g x - g x'‖ :=
            mul_le_mul_of_nonneg_right hρa (norm_nonneg _)
        _ ≤ K0 * ‖x - x'‖ ^ α := by
            rw [one_mul]
            exact hK0 x (hmem y ρ x hρ hyρ hx) x' (hmem y ρ x' hρ hyρ hx')
        _ ≤ max K0 0 * ‖x - x'‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  have h0T : (0 : ℝ) ∈ T := Or.inl rfl
  set Q := sSup T
  have hQ0 : 0 ≤ Q := le_csSup hbdd h0T
  -- Step 3: (P1) holds with the constant `Q`.
  have hP1 : ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2),
      ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α := by
    intro y ρ hρ hyρ x hx x' hx'
    by_cases hne : x = x'
    · subst hne
      simp [Real.zero_rpow hα0.ne']
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      have hq : ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α ∈ T :=
        Or.inr ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩
      have h := le_csSup hbdd hq
      rwa [div_le_iff₀ hpow] at h
  -- Step 4: the one-step improvement for this `Q`.
  have himp := Submission.dohr_eb_sch_ube_holder_improvement n ℓ g α M A Q hα0 hα1 hM hA hQ0
    hP1 hP2 hP3
  -- Step 5: absorption, `Q ≤ Q/2 + 512 M + 32 A`, hence `Q ≤ 1024 M + 64 A`.
  have hQle : Q ≤ Q / 2 + 512 * M + 32 * A := by
    refine csSup_le ⟨0, h0T⟩ ?_
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · linarith
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      rw [div_le_iff₀ hpow]
      exact (himp y ρ hρ hyρ).2 x hx x' hx'
  have hQC : Q ≤ 1024 * M + 64 * A := by linarith
  -- Step 6: the admissible pair `(0, 1)`.
  have h01 : ‖(0 : Rn n)‖ + 1 ≤ 1 := by simp
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h := (himp 0 1 one_pos h01).1 x hx
    rw [one_mul] at h
    linarith
  · have h := hP1 0 1 one_pos h01 x hx y hy
    rw [Real.one_rpow, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hQC (Real.rpow_nonneg (norm_nonneg _) _))
/-- Affine subtraction and scaling of a `C¹` weak solution (the integral computation in the blow-up
step of the Schauder estimate used for the elliptic bootstrap in Simon Ch. 5, 7.1): if `v` is `C¹`
on the open set `D`, `∫_D b[Dv][Dζ] = ∫_D Θ[Dζ]` for all `ζ ∈ C¹_c(D)`, and `B₀[P₀][Dζ]`, `Θ₀[Dζ]`
have integral `0` over `ℝⁿ` for all `ζ ∈ C¹_c`, then `V = s (v − c − P₀)` is `C¹` on `D` with
`DV = s (Dv − P₀)` and `∫_D b[DV][Dζ] = ∫_D (s ((Θ − Θ₀) − (b[P₀] − B₀[P₀])))[Dζ]`. -/
theorem dohr_eb_sch_bu_weak_eq_sub_affine : ∀ (n ℓ : ℕ) (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (D : Set (Rn n)) (B₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (P₀ : Rn n →L[ℝ] Rn ℓ) (c : Rn ℓ) (s : ℝ), IsOpen D → ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => b p.1 p.2.1 p.2.2) (D ×ˢ univ) → ContinuousOn Θ D → ContDiffOn ℝ 1 v D → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in D, Θ x (fderiv ℝ ζ x)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, B₀ P₀ (fderiv ℝ ζ x) = 0) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, Θ₀ (fderiv ℝ ζ x) = 0) → ContDiffOn ℝ 1 (fun x => s • (v x - c - P₀ x)) D ∧ (∀ x ∈ D, fderiv ℝ (fun x => s • (v x - c - P₀ x)) x = s • (fderiv ℝ v x - P₀)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ (fun x => s • (v x - c - P₀ x)) x) (fderiv ℝ ζ x) = ∫ x in D, (s • ((Θ x - Θ₀) - (b x P₀ - B₀ P₀))) (fderiv ℝ ζ x) := by
  intro n ℓ b Θ v D B₀ Θ₀ P₀ c s hD hb hΘ hv hweak hB₀ hΘ₀
  -- (ii) as `HasFDerivAt`: on the open set `D`, `v` is differentiable and
  -- `D(s • (v - c - P₀)) = s • (Dv - P₀)`.
  have hderiv : ∀ x ∈ D,
      HasFDerivAt (fun x => s • (v x - c - P₀ x)) (s • (fderiv ℝ v x - P₀)) x := by
    intro x hx
    have hvx : DifferentiableAt ℝ v x :=
      (hv.differentiableOn_one x hx).differentiableAt (hD.mem_nhds hx)
    exact ((hvx.hasFDerivAt.sub_const c).sub P₀.hasFDerivAt).const_smul s
  refine ⟨((hv.sub contDiffOn_const).sub P₀.contDiff.contDiffOn).const_smul s,
    fun x hx => (hderiv x hx).fderiv, ?_⟩
  intro ζ hζ hζc hζD
  -- `Dζ` is continuous and vanishes off the compact set `tsupport ζ ⊆ D`.
  have hTc : IsCompact (tsupport ζ) := hζc
  have hζ' : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx (support_fderiv_subset ℝ h)
  -- A function continuous on `D` that vanishes where `Dζ` does is integrable.
  have hint : ∀ g : Rn n → ℝ, ContinuousOn g D → (∀ x, fderiv ℝ ζ x = 0 → g x = 0) →
      Integrable g := fun g hg hg0 =>
    ((hg.mono hζD).integrableOn_compact hTc).integrable_of_forall_notMem_eq_zero
      fun x hx => hg0 x (hζ0 x hx)
  have hvc : ContinuousOn (fderiv ℝ v) D := hv.continuousOn_fderiv_of_isOpen hD le_rfl
  have hbc : ∀ P : Rn n → (Rn n →L[ℝ] Rn ℓ), ContinuousOn P D →
      ContinuousOn (fun x => b x (P x) (fderiv ℝ ζ x)) D := fun P hP =>
    hb.comp (continuousOn_id.prodMk (hP.prodMk hζ'.continuousOn)) fun x hx => ⟨hx, mem_univ _⟩
  have i1 : Integrable fun x => b x (fderiv ℝ v x) (fderiv ℝ ζ x) :=
    hint _ (hbc _ hvc) fun x hx => by rw [hx, map_zero]
  have i2 : Integrable fun x => b x P₀ (fderiv ℝ ζ x) :=
    hint _ (hbc _ continuousOn_const) fun x hx => by rw [hx, map_zero]
  have i3 : Integrable fun x => Θ x (fderiv ℝ ζ x) :=
    hint _ (hΘ.clm_apply hζ'.continuousOn) fun x hx => by rw [hx, map_zero]
  have i4 : Integrable fun x => Θ₀ (fderiv ℝ ζ x) :=
    hint _ (Θ₀.continuous.comp hζ').continuousOn fun x hx => by rw [hx, map_zero]
  have i5 : Integrable fun x => B₀ P₀ (fderiv ℝ ζ x) :=
    hint _ ((B₀ P₀).continuous.comp hζ').continuousOn fun x hx => by rw [hx, map_zero]
  have i34 : Integrable fun x => Θ x (fderiv ℝ ζ x) - Θ₀ (fderiv ℝ ζ x) := i3.sub i4
  have i25 : Integrable fun x => b x P₀ (fderiv ℝ ζ x) - B₀ P₀ (fderiv ℝ ζ x) := i2.sub i5
  -- The integrals of `Θ₀[Dζ]` and `B₀[P₀][Dζ]` over `D` are those over `ℝⁿ`, which vanish.
  have hz4 : ∫ x in D, Θ₀ (fderiv ℝ ζ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hζ0 x fun h => hx (hζD h), map_zero]]
    exact hΘ₀ ζ hζ hζc
  have hz5 : ∫ x in D, B₀ P₀ (fderiv ℝ ζ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hζ0 x fun h => hx (hζD h), map_zero]]
    exact hB₀ ζ hζ hζc
  -- Bilinearity: on `D`, `b[DV][Dζ] = s b[Dv][Dζ] - s b[P₀][Dζ]`.
  have hL : ∫ x in D, b x (fderiv ℝ (fun x => s • (v x - c - P₀ x)) x) (fderiv ℝ ζ x) =
      ∫ x in D, (s * b x (fderiv ℝ v x) (fderiv ℝ ζ x) - s * b x P₀ (fderiv ℝ ζ x)) := by
    refine setIntegral_congr_fun hD.measurableSet fun x hx => ?_
    simp only [(hderiv x hx).fderiv, map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul,
      mul_sub]
  -- Evaluate the right-hand side pointwise, split the integrals and use the weak equation.
  simp only [smul_apply, sub_apply, smul_eq_mul]
  rw [hL, integral_sub (i1.integrableOn.const_mul s) (i2.integrableOn.const_mul s),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub i34.integrableOn i25.integrableOn,
    integral_sub i3.integrableOn i4.integrableOn, integral_sub i2.integrableOn i5.integrableOn,
    hweak ζ hζ hζc hζD, hz4, hz5]
  ring
/-- **Diagonal extraction with one glued limit** (Simon Ch. 5, proof of Theorem 7.1: Hölder
compactness in the Schauder blow-up argument).  Let `F k : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` and `S m ⊆ ℝⁿ`.  If, for
every `m`, every subsequence `F ∘ ψ` has a further subsequence `F ∘ ψ ∘ χ` converging uniformly on
`S m`, then a single subsequence `F ∘ φ` converges uniformly on every `S m` to one limit `V`.

Proof: iterate the extractions, `Ψ 0 = id` and `Ψ (m + 1) = Ψ m ∘ χ_m` with `F ∘ Ψ (m + 1) → g_m`
uniformly on `S m`, and take the diagonal `φ j = Ψ (j + 1) j`; it is strictly increasing because
`χ i ≥ i` for strictly increasing `χ`.  Since `Ψ (m + d) = Ψ m ∘ ρ` with `ρ` strictly increasing,
for `j ≥ m` the index `φ j` is the term of `Ψ (m + 1)` at a position `τ j ≥ j`, so `F ∘ φ → g_m`
uniformly on `S m`.  Put `V z = g_{m(z)} z` for the least `m(z)` with `z ∈ S m(z)` (and `V z = 0`
off `⋃ S m`); uniqueness of limits gives `V = g_m` on `S m`. -/
theorem dohr_eb_sch_bu_hds_diagonal_extract : ∀ (n ℓ : ℕ) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (S : ℕ → Set (Rn n)), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧ TendstoUniformlyOn (fun j => F (ψ (χ j))) g atTop (S m)) → ∃ (φ : ℕ → ℕ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono φ ∧ ∀ m : ℕ, TendstoUniformlyOn (fun j => F (φ j)) V atTop (S m) := by
  intro n ℓ F S h
  -- Step 1: choose `χ m ψ` and `g m ψ` for every `ψ`; the convergence is only claimed for
  -- strictly increasing `ψ` (otherwise take `χ = id`, `g = 0`).
  have h' : ∀ (m : ℕ) (ψ : ℕ → ℕ), ∃ (χ : ℕ → ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)),
      StrictMono χ ∧ (StrictMono ψ → TendstoUniformlyOn (fun j => F (ψ (χ j))) g atTop (S m)) := by
    intro m ψ
    by_cases hψ : StrictMono ψ
    · obtain ⟨χ, g, hχ, hg⟩ := h m ψ hψ
      exact ⟨χ, g, hχ, fun _ => hg⟩
    · exact ⟨id, 0, strictMono_id, fun hψ' => absurd hψ' hψ⟩
  choose χ g hχ hg using h'
  -- Step 2: nested subsequences `Ψ 0 = id`, `Ψ (m + 1) = Ψ m ∘ χ m (Ψ m)`.
  obtain ⟨Ψ, hΨ0, hΨs⟩ : ∃ Ψ : ℕ → ℕ → ℕ, Ψ 0 = id ∧ ∀ m, Ψ (m + 1) = Ψ m ∘ χ m (Ψ m) :=
    ⟨fun m => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k ψ => ψ ∘ χ k ψ) m, rfl, fun _ => rfl⟩
  have hΨmono : ∀ m, StrictMono (Ψ m) := by
    intro m
    induction m with
    | zero => rw [hΨ0]; exact strictMono_id
    | succ m ih => rw [hΨs]; exact ih.comp (hχ m (Ψ m))
  have hconv : ∀ m, TendstoUniformlyOn (fun j => F (Ψ (m + 1) j)) (g m (Ψ m)) atTop (S m) := by
    intro m
    rw [hΨs]
    exact hg m (Ψ m) (hΨmono m)
  -- Step 3: later stages factor through earlier ones, `Ψ (m + d) = Ψ m ∘ ρ m d`.
  have hfac : ∀ m d, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ Ψ (m + d) = Ψ m ∘ ρ := by
    intro m d
    induction d with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ d ih =>
      obtain ⟨ρ, hρ, hρe⟩ := ih
      refine ⟨ρ ∘ χ (m + d) (Ψ (m + d)), hρ.comp (hχ _ _), ?_⟩
      rw [← add_assoc, hΨs, hρe]
      rfl
  choose ρ hρ hρe using hfac
  -- Step 4: the diagonal `φ j = Ψ (j + 1) j` is strictly increasing.
  have hφ : StrictMono (fun j => Ψ (j + 1) j) := by
    apply strictMono_nat_of_lt_succ
    intro j
    show Ψ (j + 1) j < Ψ (j + 1 + 1) (j + 1)
    rw [hΨs (j + 1)]
    exact hΨmono (j + 1)
      (lt_of_lt_of_le (Nat.lt_succ_self j) ((hχ (j + 1) (Ψ (j + 1))).id_le (j + 1)))
  -- Step 5: for `j ≥ m`, `φ j = Ψ (m + 1) (τ j)` with `τ j = ρ (m + 1) (j - m) j ≥ j`, so
  -- `F ∘ φ → g m (Ψ m)` uniformly on `S m`.
  have hφconv : ∀ m, TendstoUniformlyOn (fun j => F (Ψ (j + 1) j)) (g m (Ψ m)) atTop (S m) := by
    intro m
    have hτ : ∀ j, m ≤ j → Ψ (j + 1) j = Ψ (m + 1) (ρ (m + 1) (j - m) j) := by
      intro j hj
      have hjm : j + 1 = m + 1 + (j - m) := by omega
      rw [hjm, hρe]
      rfl
    have hτt : Tendsto (fun j => ρ (m + 1) (j - m) j) atTop atTop :=
      tendsto_atTop_mono (fun j => (hρ (m + 1) (j - m)).id_le j) tendsto_id
    have h1 : TendstoUniformlyOn (fun j => F (Ψ (m + 1) (ρ (m + 1) (j - m) j))) (g m (Ψ m))
        atTop (S m) := fun u hu => hτt.eventually (hconv m u hu)
    refine h1.congr ?_
    filter_upwards [eventually_ge_atTop m] with j hj
    intro z _
    simp only [hτ j hj]
  -- Step 6: glue the limits, `V z = g m(z) (Ψ m(z)) z` for the least `m(z)` with `z ∈ S m(z)`.
  classical
  refine ⟨fun j => Ψ (j + 1) j,
    fun z => if hz : ∃ m, z ∈ S m then g (Nat.find hz) (Ψ (Nat.find hz)) z else 0, hφ,
    fun m => (hφconv m).congr_right ?_⟩
  intro z hz
  have hex : ∃ m, z ∈ S m := ⟨m, hz⟩
  simp only [dite_eq_left hex]
  exact tendsto_nhds_unique ((hφconv m).tendsto_at hz) ((hφconv _).tendsto_at (Nat.find_spec hex))
/-- Uniformly Hölder maps `F j : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` that converge on a dense subset `D` of a compact
set `S` converge uniformly on `S`.  Given `ε > 0`, pick `η > 0` with `K η^α < ε/3`; finitely many
balls `B̆_η(d)`, `d ∈ T ⊆ D`, cover `S`; from some `N` on all `F j d`, `d ∈ T`, are `ε/6`-close to
their limits; the Hölder bound and the triangle inequality then make `(F j)` uniformly Cauchy on
`S`, and completeness of `L` supplies the uniform limit. -/
theorem dohr_eb_sch_bu_hds_unif_of_dense : ∀ (n ℓ : ℕ) (α K : ℝ) (S D : Set (Rn n)) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → D ⊆ S → S ⊆ closure D → (∀ d ∈ D, ∃ v : Rn n →L[ℝ] Rn ℓ, Tendsto (fun j => F j d) atTop (𝓝 v)) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ G : Rn n → (Rn n →L[ℝ] Rn ℓ), TendstoUniformlyOn F G atTop S := by
  intro n ℓ α K S D F hα hK hS hDS hSD hconv hHol
  -- Step 1: the limits `v d` on `D`.
  choose! v hv using hconv
  -- Steps 2–5: `(F j)` is uniformly Cauchy on `S`.
  have hU : UniformCauchySeqOn F atTop S := by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    -- Step 2: a Hölder scale `η > 0` with `K η^α < ε/3`.
    have h0 : Tendsto (fun t : ℝ => K * t ^ α) (𝓝 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).const_mul K).tendsto
      simpa [Real.zero_rpow hα.ne'] using h
    obtain ⟨η, hηε, hη⟩ : ∃ η : ℝ, K * η ^ α < ε / 3 ∧ 0 < η :=
      (((h0.eventually (gt_mem_nhds (div_pos hε three_pos))).filter_mono
        nhdsWithin_le_nhds).and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t)).exists
    -- Step 3: finitely many balls `B̆_η(d)`, `d ∈ T ⊆ D`, cover `S`.
    obtain ⟨T, hTD, hTfin, hST⟩ := hS.elim_finite_subcover_image (b := D)
      (c := fun d => Metric.ball d η) (fun d _ => Metric.isOpen_ball) fun z hz => by
        obtain ⟨d, hd, hzd⟩ := Metric.mem_closure_iff.1 (hSD hz) η hη
        exact Set.mem_biUnion hd (Metric.mem_ball.2 hzd)
    -- Step 4: from some `N` on, `F j d` is `ε/6`-close to `v d` for every `d ∈ T`.
    have hev : ∀ᶠ j in atTop, ∀ d ∈ T, dist (F j d) (v d) < ε / 6 :=
      hTfin.eventually_all.2 fun d hd =>
        (hv d (hTD hd)).eventually (Metric.ball_mem_nhds _ (div_pos hε (by norm_num)))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun m hm m' hm' z hz => ?_⟩
    -- Step 5: the Hölder bound and the triangle inequality.
    obtain ⟨d, hdT, hzd⟩ := Set.mem_iUnion₂.1 (hST hz)
    have hdS : d ∈ S := hDS (hTD hdT)
    have hzd' : ‖z - d‖ ^ α ≤ η ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hzd).le)
        hα.le
    have hHol' : ∀ j, dist (F j z) (F j d) < ε / 3 := fun j => by
      rw [dist_eq_norm]
      calc ‖F j z - F j d‖ ≤ K * ‖z - d‖ ^ α := hHol j z hz d hdS
        _ ≤ K * η ^ α := mul_le_mul_of_nonneg_left hzd' hK
        _ < ε / 3 := hηε
    have h1 := hHol' m
    have h2 := hHol' m'
    have h3 := hN m hm d hdT
    have h4 := hN m' hm' d hdT
    have h5 := dist_triangle4 (F m z) (F m d) (F m' d) (F m' z)
    have h6 := dist_triangle (F m d) (v d) (F m' d)
    rw [dist_comm (F m' d) (F m' z)] at h5
    rw [dist_comm (v d) (F m' d)] at h6
    linarith
  -- Step 6: pointwise limits on `S`, by completeness of `L`.
  have hlim : ∀ z ∈ S, ∃ w, Tendsto (fun j => F j z) atTop (𝓝 w) := fun z hz =>
    cauchySeq_tendsto_of_complete (hU.cauchySeq hz)
  -- Step 7: uniformly Cauchy plus pointwise convergence gives uniform convergence.
  exact ⟨fun z => limUnder atTop (fun j => F j z),
    hU.tendstoUniformlyOn_of_tendsto fun z hz => tendsto_nhds_limUnder (hlim z hz)⟩
/-- Sequential Arzelà–Ascoli on a compact set `S ⊆ ℝⁿ` for maps `g_j : ℝⁿ → L = L(ℝⁿ, ℝ^ℓ)` that
are bounded by `M` and `α`-Hölder with constant `K` on `S`, uniformly in `j`: some subsequence
`g_{χ(j)}` converges uniformly on `S`.

Proof: if `S = ∅` there is nothing to prove.  Otherwise `S`, a subspace of the second-countable
space `ℝⁿ`, has a countable subset `D ⊆ S` with `S ⊆ closure D`; `D` is nonempty, so `D = {d_m}`
for a sequence `d`.  At each `d_m` every subsequence `g_{ψ(j)}(d_m)` lies in the compact closed
`M`-ball of the finite-dimensional space `L`, so it has a convergent further subsequence, i.e. one
converging uniformly on `{d_m}`.  `dohr_eb_sch_bu_hds_diagonal_extract` with `S_m = {d_m}` gives a
single `χ` with `g_{χ(j)}` convergent at every point of `D`, and `dohr_eb_sch_bu_hds_unif_of_dense`
upgrades this to uniform convergence on `S`. -/
theorem dohr_eb_sch_bu_hds_compact_subseq : ∀ (n ℓ : ℕ) (α K M : ℝ) (S : Set (Rn n)) (g : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → (∀ j, ∀ z ∈ S, ‖g j z‖ ≤ M) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖g j z - g j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ (χ : ℕ → ℕ) (G : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧ TendstoUniformlyOn (fun j => g (χ j)) G atTop S := by
  intro n ℓ α K M S g hα hK hS hM hH
  -- Step 1: the empty case.
  rcases S.eq_empty_or_nonempty with hS0 | ⟨z₀, hz₀⟩
  · subst hS0
    exact ⟨id, 0, strictMono_id, tendstoUniformlyOn_empty⟩
  -- Step 2: a countable `D ⊆ S` with `S ⊆ closure D`; it is nonempty, so `D = range d`.
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hDne : D.Nonempty := closure_nonempty_iff.mp ⟨z₀, hSD hz₀⟩
  obtain ⟨d, rfl⟩ := hDc.exists_eq_range hDne
  -- Step 3: at `d m`, every subsequence has a further subsequence converging on `{d m}`, since
  -- `g (ψ j) (d m)` stays in the closed `M`-ball of `L`, compact as `L` is finite-dimensional.
  have hpt : ∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ) (G : Rn n → (Rn n →L[ℝ] Rn ℓ)),
      StrictMono χ ∧ TendstoUniformlyOn (fun j => g (ψ (χ j))) G atTop {d m} := by
    intro m ψ _
    obtain ⟨v, -, χ, hχ, hv⟩ := (isCompact_closedBall (0 : Rn n →L[ℝ] Rn ℓ) M).tendsto_subseq
      (x := fun j => g (ψ j) (d m))
      (fun j => mem_closedBall_zero_iff.mpr (hM (ψ j) (d m) (hDS (mem_range_self m))))
    exact ⟨χ, fun _ => v, hχ, tendstoUniformlyOn_singleton_iff_tendsto.mpr hv⟩
  -- Step 4: diagonal extraction over the points `d m` of `D`.
  obtain ⟨χ, W, hχ, hW⟩ :=
    Submission.dohr_eb_sch_bu_hds_diagonal_extract n ℓ g (fun m => {d m}) hpt
  have hconv : ∀ z ∈ range d, ∃ v : Rn n →L[ℝ] Rn ℓ, Tendsto (fun j => g (χ j) z) atTop (𝓝 v) := by
    rintro _ ⟨m, rfl⟩
    exact ⟨W (d m), (hW m).tendsto_at (mem_singleton (d m))⟩
  -- Step 5: by the uniform Hölder bound, convergence on `D` upgrades to uniform convergence on `S`.
  obtain ⟨G, hG⟩ := Submission.dohr_eb_sch_bu_hds_unif_of_dense n ℓ α K S (range d)
    (fun j => g (χ j)) hα hK hS hDS hSD hconv (fun j => hH (χ j))
  exact ⟨χ, G, hχ, hG⟩

end Submission
/-- **Hölder bounds pass to pointwise limits** (steps 7b–c of the Hölder diagonal-subsequence
argument in the Schauder blow-up estimate for Simon 7.1).  If `F_j(z) → V(z)` for every `z` and,
for all `z, z'`, `‖F_j(z) − F_j(z')‖ ≤ K ‖z − z'‖^α` for all large `j`, then `V` satisfies the same
`α`-Hölder bound and, as `α > 0`, is continuous. -/
theorem Submission.dohr_eb_sch_bu_hds_holder_of_limit : ∀ (n ℓ : ℕ) (α K : ℝ) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → (∀ z, Tendsto (fun j => F j z) atTop (𝓝 (V z))) → (∀ z z' : Rn n, ∀ᶠ j in atTop, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ Continuous V := by
  intro n ℓ α K F V hα _ hF hFK
  -- Step 1: `‖F_j z − F_j z'‖ → ‖V z − V z'‖` and these norms are eventually `≤ K ‖z − z'‖^α`;
  -- `(-∞, K ‖z − z'‖^α]` is closed, so the limit satisfies the same bound.
  have hV : ∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α := fun z z' =>
    le_of_tendsto ((hF z).sub (hF z')).norm (hFK z z')
  refine ⟨hV, continuous_iff_continuousAt.mpr fun z => ?_⟩
  -- Step 2a: `t ↦ t^α` is continuous at `0` with value `0^α = 0` (`α > 0`) and `‖z' − z‖ → 0`,
  -- so `K ‖z' − z‖^α → 0` as `z' → z`.
  have hpow : Tendsto (fun t : ℝ => t ^ α) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
  have hK0 : Tendsto (fun z' : Rn n => K * ‖z' - z‖ ^ α) (𝓝 z) (𝓝 0) := by
    simpa using (hpow.comp (tendsto_norm_sub_self z)).const_mul K
  -- Steps 2b–c: `0 ≤ ‖V z' − V z‖ ≤ K ‖z' − z‖^α`, so `‖V z' − V z‖ → 0` by squeezing, that is,
  -- `V z' → V z`.
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun z' => norm_nonneg _) (fun z' => hV z' z) hK0)

namespace Submission

/-- **Arzelà–Ascoli with diagonal extraction for uniformly Hölder maps on growing balls**
(blow-up step of the Schauder estimate behind Simon Ch. 5, Theorem 7.1, second assertion).
Let `R_k → ∞` and let `f_k : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` satisfy `f_k(0) = 0` and
`‖f_k(z) − f_k(z')‖ ≤ K|z − z'|^α` on `B̆_{R_k}(0)`.  Then a subsequence `f_{φ(j)}` converges
uniformly on every closed ball `B_r(0)` to a continuous `V` with `V(0) = 0` and
`‖V(z) − V(z')‖ ≤ K|z − z'|^α` on `ℝⁿ`: on `B_m(0)` the tail `k ≥ k_m` (`R_k > m`) is uniformly
Hölder and bounded by `K mᵅ`, so every subsequence has a further subsequence converging uniformly
on `B_m(0)` (Arzelà–Ascoli); a diagonal subsequence converges on every `B_m(0)`, and the Hölder
bound passes to the limit. -/
theorem dohr_eb_sch_bu_holder_diag_subseq : ∀ (n ℓ : ℕ) (α K : ℝ) (f : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (R : ℕ → ℝ), 0 < α → 0 ≤ K → Tendsto R atTop atTop → (∀ k, f k 0 = 0) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k), ‖f k z - f k z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ (φ : ℕ → ℕ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono φ ∧ V 0 = 0 ∧ Continuous V ∧ (∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ ∀ r : ℝ, TendstoUniformlyOn (fun j => f (φ j)) V atTop (closedBall (0 : Rn n) r) := by
  intro n ℓ α K f R hα hK hR hf0 hf
  -- Step 1: for each `m` there is `k_m` with `R_k > m` for `k ≥ k_m`; for such `k` the map `f_k`
  -- is `K`-`α`-Hölder on `B_m(0)` and bounded there by `K mᵅ` (since `f_k(0) = 0`).
  have hkm : ∀ m : ℕ, ∃ km : ℕ, ∀ k ≥ km, (m : ℝ) < R k := fun m =>
    eventually_atTop.1 (hR.eventually_gt_atTop (m : ℝ))
  choose km hkm using hkm
  have hhol : ∀ m : ℕ, ∀ k ≥ km m, ∀ z ∈ closedBall (0 : Rn n) m,
      ∀ z' ∈ closedBall (0 : Rn n) m, ‖f k z - f k z'‖ ≤ K * ‖z - z'‖ ^ α :=
    fun m k hk z hz z' hz' =>
      hf k z (closedBall_subset_ball (hkm m k hk) hz) z' (closedBall_subset_ball (hkm m k hk) hz')
  have hbd : ∀ m : ℕ, ∀ k ≥ km m, ∀ z ∈ closedBall (0 : Rn n) m, ‖f k z‖ ≤ K * (m : ℝ) ^ α := by
    intro m k hk z hz
    have h := hhol m k hk z hz 0 (mem_closedBall_self (Nat.cast_nonneg m))
    rw [hf0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg z) (mem_closedBall_zero_iff.1 hz) hα.le) hK)
  -- Step 2 (Arzelà–Ascoli): along any strictly increasing `ψ`, the shifted tail
  -- `f_{ψ(k_m + j)}` satisfies the bounds of step 1 on `B_m(0)`, so a further subsequence
  -- converges uniformly on `B_m(0)`.
  have hstep2 : ∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ)
      (g : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧
        TendstoUniformlyOn (fun j => f (ψ (χ j))) g atTop (closedBall (0 : Rn n) m) := by
    intro m ψ hψ
    have hge : ∀ j, km m ≤ ψ (km m + j) := fun j =>
      (Nat.le_add_right (km m) j).trans (hψ.id_le (km m + j))
    obtain ⟨χ', G, hχ', hG⟩ := Submission.dohr_eb_sch_bu_hds_compact_subseq n ℓ α K
      (K * (m : ℝ) ^ α) (closedBall (0 : Rn n) m) (fun j => f (ψ (km m + j))) hα hK
      (isCompact_closedBall 0 m) (fun j z hz => hbd m _ (hge j) z hz)
      (fun j z hz z' hz' => hhol m _ (hge j) z hz z' hz')
    exact ⟨fun j => km m + χ' j, G, fun a b hab => Nat.add_lt_add_left (hχ' hab) (km m), hG⟩
  -- Steps 3–6: diagonal extraction over the balls `B_m(0)`, with a single limit `V`; every
  -- `B_r(0)` lies in `B_{⌈r⌉}(0)`, and pointwise convergence at `z` follows from `z ∈ B_{|z|}(0)`.
  obtain ⟨φ, V, hφ, hV⟩ := Submission.dohr_eb_sch_bu_hds_diagonal_extract n ℓ f
    (fun m => closedBall (0 : Rn n) m) hstep2
  have hVr : ∀ r : ℝ, TendstoUniformlyOn (fun j => f (φ j)) V atTop (closedBall (0 : Rn n) r) :=
    fun r => (hV ⌈r⌉₊).mono (closedBall_subset_closedBall (Nat.le_ceil r))
  have hpt : ∀ z, Tendsto (fun j => f (φ j) z) atTop (𝓝 (V z)) := fun z =>
    (hVr ‖z‖).tendsto_at (mem_closedBall_zero_iff.2 le_rfl)
  -- Step 7a: `f_{φ(j)}(0) = 0` for every `j`, so `V(0) = 0`.
  have hV0 : V 0 = 0 :=
    tendsto_nhds_unique (hpt 0) (tendsto_const_nhds.congr fun j => (hf0 (φ j)).symm)
  -- Step 7b–c: `R_{φ(j)} → ∞`, so for large `j` both `z, z'` lie in `B̆_{R_{φ(j)}}(0)` and the
  -- Hölder bound holds at `z, z'`; it passes to the limit, which is therefore continuous.
  have hev : ∀ z z' : Rn n, ∀ᶠ j in atTop, ‖f (φ j) z - f (φ j) z'‖ ≤ K * ‖z - z'‖ ^ α := by
    intro z z'
    filter_upwards [(hR.comp hφ.tendsto_atTop).eventually_gt_atTop (max ‖z‖ ‖z'‖)] with j hj
    exact hf (φ j) z (mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt hj))
      z' (mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt hj))
  obtain ⟨hVH, hVc⟩ := Submission.dohr_eb_sch_bu_hds_holder_of_limit n ℓ α K
    (fun j => f (φ j)) V hα hK hpt hev
  exact ⟨φ, V, hφ, hV0, hVc, hVH, hVr⟩
/-- **`C¹` limit on growing balls** (blow-up step of the Schauder estimate behind Simon 7.1).
Let `R_k → ∞`, let `W_k` be `C¹` on `B̆_{R_k}(0)` with `W_k(0) = 0`, let `V : ℝⁿ → L(ℝⁿ; ℝ^ℓ)` be
continuous, and let `DW_k → V` uniformly on every closed ball `B_r(0)`.  Then
`W(z) = ∫₀¹ V(tz) z dt` is `C¹` on `ℝⁿ` with `DW = V`: for `k` large,
`W_k(z) = ∫₀¹ DW_k(tz) z dt` by the fundamental theorem of calculus, so
`|W_k(z) − W(z)| ≤ |z| sup_{B_{|z|}(0)} ‖DW_k − V‖ → 0`, and near each point the derivatives
converge uniformly, so the theorem on uniform limits of derivatives gives `DW = V`. -/
theorem dohr_eb_sch_bu_contDiff_of_fderiv_tendsto : ∀ (n ℓ : ℕ) (W : ℕ → Rn n → Rn ℓ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)) (R : ℕ → ℝ), Tendsto R atTop atTop → (∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k))) → (∀ k, W k 0 = 0) → Continuous V → (∀ r : ℝ, TendstoUniformlyOn (fun k => fderiv ℝ (W k)) V atTop (closedBall (0 : Rn n) r)) → ∃ W' : Rn n → Rn ℓ, ContDiff ℝ 1 W' ∧ ∀ z, fderiv ℝ W' z = V z := by
  intro n ℓ W V R hR hW hW0 hVc hV
  -- Step 1: for `k` large (`R k > r + 1`), `W k` has derivative `DW_k(y)` at every
  -- `y ∈ B̆_{r+1}(0)`, and `DW_k` is continuous there.
  have hstep1 : ∀ r : ℝ, ∀ᶠ k in atTop,
      (∀ y ∈ ball (0 : Rn n) (r + 1), HasFDerivAt (W k) (fderiv ℝ (W k) y) y) ∧
        ContinuousOn (fderiv ℝ (W k)) (ball (0 : Rn n) (r + 1)) := by
    intro r
    filter_upwards [hR.eventually_gt_atTop (r + 1)] with k hk
    have hsub : ball (0 : Rn n) (r + 1) ⊆ ball 0 (R k) := ball_subset_ball hk.le
    refine ⟨fun y hy => ?_, ((hW k).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hsub⟩
    exact (((hW k).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (hsub hy))).hasFDerivAt
  -- Steps 2–3: for `k` large, `W_k(z) = ∫₀¹ DW_k(tz) z dt` (FTC, `W_k(0) = 0`), so with
  -- `W(z) = ∫₀¹ V(tz) z dt` we get `|W_k(z) − W(z)| ≤ |z| sup_{B_{|z|}(0)} ‖DW_k − V‖ → 0`.
  have hconv : ∀ z : Rn n,
      Tendsto (fun k => W k z) atTop (𝓝 (∫ t in (0 : ℝ)..1, V (t • z) z)) := by
    intro z
    have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, t • z ∈ closedBall (0 : Rn n) ‖z‖ := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg z) ht.2
    have hmem' : ∀ t ∈ uIcc (0 : ℝ) 1, t • z ∈ ball (0 : Rn n) (‖z‖ + 1) := fun t ht =>
      closedBall_subset_ball (lt_add_one _) (hmem t ht)
    have hVint : IntervalIntegrable (fun t : ℝ => V (t • z) z) volume 0 1 :=
      ((hVc.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const).intervalIntegrable 0 1
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (‖z‖ + 1) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((hstep1 ‖z‖).and (Metric.tendstoUniformlyOn_iff.1 (hV ‖z‖) _ hδ))
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨⟨hd, hc⟩, hu⟩ := hN k hk
    have hWint : IntervalIntegrable (fun t : ℝ => fderiv ℝ (W k) (t • z) z) volume 0 1 :=
      ContinuousOn.intervalIntegrable ((hc.comp (continuous_id.smul continuous_const).continuousOn
        hmem').clm_apply continuousOn_const)
    have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ (W k) (t • z) z = W k z := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
        (f := fun t : ℝ => W k (t • z)) (f' := fun t => fderiv ℝ (W k) (t • z) z)
        (fun t ht => by
          have h2 := (hd _ (hmem' t ht)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const z)
          rw [one_smul] at h2
          exact h2)
        hWint
      simpa [hW0] using h
    rw [dist_eq_norm, ← hftc, ← intervalIntegral.integral_sub hWint hVint]
    calc ‖∫ t in (0 : ℝ)..1, (fderiv ℝ (W k) (t • z) z - V (t • z) z)‖
        ≤ ε / (‖z‖ + 1) * ‖z‖ * |1 - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
          have hlt := hu (t • z) (hmem t (uIoc_subset_uIcc ht))
          rw [dist_eq_norm, norm_sub_rev] at hlt
          exact ((fderiv ℝ (W k) (t • z) - V (t • z)).le_opNorm z).trans
            (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg z))
      _ < ε := by
          rw [sub_zero, abs_one, mul_one, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  -- Step 4: near every `x`, `DW_k → V` uniformly and `W_k → W` pointwise, so `DW(x) = V(x)`.
  have hderiv : ∀ x : Rn n, HasFDerivAt (fun z => ∫ t in (0 : ℝ)..1, V (t • z) z) (V x) x := by
    intro x
    have hnhds : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : Rn n) (‖x‖ + 1) :=
      isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (lt_add_one _))
    exact hasFDerivAt_of_tendstoUniformlyOnFilter (l := atTop) (f := W)
      (f' := fun k => fderiv ℝ (W k)) (g' := V)
      ((hV (‖x‖ + 1)).tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.2 (mem_of_superset hnhds ball_subset_closedBall)))
      (((hstep1 ‖x‖).prod_mk hnhds).mono fun p hp => hp.1.1 p.2 hp.2)
      (Eventually.of_forall hconv)
  -- Step 5: `DW = V` is continuous, so `W` is `C¹`.
  have hfd : fderiv ℝ (fun z => ∫ t in (0 : ℝ)..1, V (t • z) z) = V :=
    funext fun x => (hderiv x).fderiv
  refine ⟨fun z => ∫ t in (0 : ℝ)..1, V (t • z) z,
    contDiff_one_iff_fderiv.2 ⟨fun x => (hderiv x).differentiableAt, ?_⟩,
    fun z => (hderiv z).fderiv⟩
  rw [hfd]
  exact hVc
/-- Localization of integrals: if `f : ℝⁿ → ℝ` is continuous on an open `O` and vanishes off a
compact `T ⊆ O`, then `f` is continuous, integrable, and `∫_O f = ∫_{ℝⁿ} f`.  At a point of `O`,
`f` is continuous because `O` is open; a point outside `O` lies in the open set `Tᶜ` (`T` is
closed), where `f = 0`.  So `f` is continuous with compact support (`HasCompactSupport.intro`),
hence integrable (`Continuous.integrable_of_hasCompactSupport`), and it vanishes off `O`
(`setIntegral_eq_integral_of_forall_compl_eq_zero`). -/
theorem dohr_eb_sch_bu_wel_localized_integral : ∀ (n : ℕ) (f : Rn n → ℝ) (O T : Set (Rn n)), IsOpen O → IsCompact T → T ⊆ O → ContinuousOn f O → (∀ z, z ∉ T → f z = 0) → Continuous f ∧ Integrable f ∧ ∫ z in O, f z = ∫ z, f z := by
  intro n f O T hO hT hTO hf hfT
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ O
    · exact hf.continuousAt (hO.mem_nhds hz)
    · -- `z ∉ T`, and `f = 0` on the open neighbourhood `Tᶜ` of `z`.
      have hzT : z ∉ T := fun h => hz (hTO h)
      have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 z] f :=
        Filter.mem_of_superset (hT.isClosed.isOpen_compl.mem_nhds hzT) fun w hw => (hfT w hw).symm
      exact continuousAt_const.congr hev
  refine ⟨hcont, hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hfT), ?_⟩
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hfT z fun h => hz (hTO h)
/-- Convergence of integrals under uniform convergence on a compact set containing the supports
(steps 4 and 5d of the weak-equation limit in the blow-up argument for the Schauder estimate): if
`K ⊆ ℝⁿ` is compact, `g` and eventually every `f k` are integrable and vanish off `K`, and
`f k → g` uniformly on `K`, then `∫ f k → ∫ g`.  For `ε > 0` put `M = 𝓛ⁿ(K) < ∞` and
`δ = ε / (M + 1)`; for large `k`, `|∫ f k - ∫ g| = |∫_K (f k - g)| ≤ δ M < ε`. -/
theorem dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn : ∀ (n : ℕ) (K : Set (Rn n)) (f : ℕ → Rn n → ℝ) (g : Rn n → ℝ), IsCompact K → (∀ᶠ k in atTop, Integrable (f k)) → Integrable g → (∀ᶠ k in atTop, ∀ z, z ∉ K → f k z = 0) → (∀ z, z ∉ K → g z = 0) → TendstoUniformlyOn f g atTop K → Tendsto (fun k => ∫ z, f k z) atTop (𝓝 (∫ z, g z)) := by
  intro n K f g hK hfi hgi hfK hgK hfg
  -- Step 1: `K` is compact, so `M = 𝓛ⁿ(K)` is finite (and `M ≥ 0`).
  have hKfin : (volume : Measure (Rn n)) K < ∞ := hK.measure_lt_top
  have hM : 0 ≤ (volume : Measure (Rn n)).real K := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 2: with `δ = ε / (M + 1) > 0`, for all large `k` the function `f k` is integrable,
  -- vanishes off `K`, and `|g - f k| < δ` on `K`.
  have hδ : 0 < ε / ((volume : Measure (Rn n)).real K + 1) := div_pos hε (by linarith)
  filter_upwards [hfi, hfK, Metric.tendstoUniformlyOn_iff.1 hfg _ hδ] with k hk1 hk2 hk3
  -- Steps 3–4: `∫ f k - ∫ g = ∫ (f k - g) = ∫_K (f k - g)`, as `f k - g` vanishes off `K`.
  have h4 : ∫ z in K, (f k z - g z) = ∫ z, (f k z - g z) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [hk2 z hz, hgK z hz, sub_zero]
  rw [dist_eq_norm, ← integral_sub hk1 hgi, ← h4]
  -- Step 5: `|∫_K (f k - g)| ≤ δ M`.
  have h5 : ‖∫ z in K, (f k z - g z)‖ ≤
      ε / ((volume : Measure (Rn n)).real K + 1) * (volume : Measure (Rn n)).real K :=
    norm_setIntegral_le_of_norm_le_const hKfin fun z hz => by
      rw [← dist_eq_norm, dist_comm]
      exact (hk3 z hz).le
  -- Step 6: `δ M = ε M / (M + 1) < ε`.
  have h6 : ε / ((volume : Measure (Rn n)).real K + 1) * (volume : Measure (Rn n)).real K < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith
  exact h5.trans_lt h6

end Submission
/-- **Uniform limits of the perturbed pairings and of the error forms** (steps 4 and 5a–c of the
weak-equation limit in the Schauder blow-up estimate for Simon 7.1).  Let `A` be a continuous
bilinear form on `L = L(ℝⁿ, ℝ^ℓ)`, let `U_k → V` uniformly on `K`, and let `‖z‖ ≤ r`, `‖Q z‖ ≤ Z`
and `‖V z‖ ≤ N` on `K`.  If `c_k → 0`, `d_k → 0` and, for all large `k` and all `z ∈ K`,
`|ah_k(z)[P][P'] − A[P][P']| ≤ c_k (1 + ‖z‖^α) ‖P‖ ‖P'‖` and `|Ψ_k(z)[P]| ≤ d_k ‖z‖^α ‖P‖`, then
`ah_k(z)[U_k(z)][Q(z)] → A[V(z)][Q(z)]` and `Ψ_k(z)[Q(z)] → 0` uniformly on `K`.  The bound
`|A[P][P']| ≤ C_A ‖P‖ ‖P'‖` comes from `ContinuousLinearMap.isBoundedBilinearMap`. -/
theorem Submission.dohr_eb_sch_bu_wel_pairing_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (α r Z N : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V Q : Rn n → (Rn n →L[ℝ] Rn ℓ)) (K : Set (Rn n)) (c d : ℕ → ℝ), 0 ≤ α → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → TendstoUniformlyOn U V atTop K → (∀ z ∈ K, ‖z‖ ≤ r) → (∀ z ∈ K, ‖Q z‖ ≤ Z) → (∀ z ∈ K, ‖V z‖ ≤ N) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P P' : Rn n →L[ℝ] Rn ℓ, |ah k z P P' - A P P'| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖P'‖) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P : Rn n →L[ℝ] Rn ℓ, |Ψ k z P| ≤ d k * ‖z‖ ^ α * ‖P‖) → TendstoUniformlyOn (fun k z => ah k z (U k z) (Q z)) (fun z => A (V z) (Q z)) atTop K ∧ TendstoUniformlyOn (fun k z => Ψ k z (Q z)) (fun _ => (0 : ℝ)) atTop K := by
  intro n ℓ α r Z N A ah Ψ U V Q K c d hα hc hd hUV hr hZ hN hah hΨ
  -- Step 1: nonnegative bounds on `K`: `‖z‖ ^ α ≤ R := (max r 0) ^ α`, `‖Q z‖ ≤ Z₀ := max Z 0`
  -- and `‖V z‖ ≤ N₀ := max N 0` (no case split when `K` is empty).
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ^ α ≤ R :=
    ⟨max r 0 ^ α, Real.rpow_nonneg (le_max_right r 0) α, fun z hz =>
      Real.rpow_le_rpow (norm_nonneg z) ((hr z hz).trans (le_max_left r 0)) hα⟩
  obtain ⟨Z₀, hZ₀0, hZ₀⟩ : ∃ Z₀ : ℝ, 0 ≤ Z₀ ∧ ∀ z ∈ K, ‖Q z‖ ≤ Z₀ :=
    ⟨max Z 0, le_max_right Z 0, fun z hz => (hZ z hz).trans (le_max_left Z 0)⟩
  obtain ⟨N₀, hN₀0, hN₀⟩ : ∃ N₀ : ℝ, 0 ≤ N₀ ∧ ∀ z ∈ K, ‖V z‖ ≤ N₀ :=
    ⟨max N 0, le_max_right N 0, fun z hz => (hN z hz).trans (le_max_left N 0)⟩
  -- Step 2: the bilinear bound `‖A P P'‖ ≤ C_A ‖P‖ ‖P'‖`.
  obtain ⟨CA, hCA0, hCA⟩ : ∃ CA > 0, ∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖A P P'‖ ≤ CA * ‖P‖ * ‖P'‖ :=
    A.isBoundedBilinearMap.bound
  refine ⟨?_, ?_⟩
  · -- Claim (i).  Step 3: with `C₁ = (1 + R)(N₀ + 1) Z₀` and `C₂ = C_A Z₀`, eventually
    -- `|c_k| < (ε/2)/(C₁ + 1)`, `‖U_k z − V z‖ < min 1 ((ε/2)/(C₂ + 1))` on `K`, and the
    -- coefficient bound holds on `K`.
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC₁ : 0 < (1 + R) * (N₀ + 1) * Z₀ + 1 := by positivity
    have hC₂ : 0 < CA * Z₀ + 1 := by positivity
    have hδ₁ : 0 < ε / 2 / ((1 + R) * (N₀ + 1) * Z₀ + 1) := by positivity
    have hδ₂ : 0 < min 1 (ε / 2 / (CA * Z₀ + 1)) := by positivity
    filter_upwards [Metric.tendsto_nhds.mp hc _ hδ₁, Metric.tendstoUniformlyOn_iff.mp hUV _ hδ₂,
      hah] with k hck hUk hahk z hz
    rw [Real.dist_eq, sub_zero] at hck
    have hP : ‖U k z - V z‖ < min 1 (ε / 2 / (CA * Z₀ + 1)) := by
      rw [← dist_eq_norm, dist_comm]
      exact hUk z hz
    have hP₁ : ‖U k z - V z‖ ≤ 1 := hP.le.trans (min_le_left _ _)
    have hP₂ : ‖U k z - V z‖ < ε / 2 / (CA * Z₀ + 1) := hP.trans_le (min_le_right _ _)
    -- Step 4: `‖U_k z‖ ≤ ‖V z‖ + ‖U_k z − V z‖ ≤ N₀ + 1`.
    have hUn : ‖U k z‖ ≤ N₀ + 1 :=
      calc ‖U k z‖ = ‖V z + (U k z - V z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖V z‖ + ‖U k z - V z‖ := norm_add_le _ _
        _ ≤ N₀ + 1 := add_le_add (hN₀ z hz) hP₁
    -- Step 5: `A[V][Q] − ah_k[U_k][Q] = −((ah_k − A)[U_k][Q] + A[U_k − V][Q])`.
    have hdec : A (V z) (Q z) - ah k z (U k z) (Q z) =
        -((ah k z (U k z) (Q z) - A (U k z) (Q z)) + A (U k z - V z) (Q z)) := by
      rw [map_sub, sub_apply]
      ring
    -- Step 6: the first term is `≤ |c_k| C₁ < ε/2`.
    have h₁ : |ah k z (U k z) (Q z) - A (U k z) (Q z)| < ε / 2 := by
      have hQ := hZ₀ z hz
      have hRz := hR z hz
      calc |ah k z (U k z) (Q z) - A (U k z) (Q z)|
          ≤ c k * (1 + ‖z‖ ^ α) * ‖U k z‖ * ‖Q z‖ := hahk z hz _ _
        _ ≤ |c k| * (1 + ‖z‖ ^ α) * ‖U k z‖ * ‖Q z‖ := by
            gcongr
            exact le_abs_self (c k)
        _ ≤ |c k| * (1 + R) * (N₀ + 1) * Z₀ := by gcongr
        _ ≤ |c k| * ((1 + R) * (N₀ + 1) * Z₀ + 1) := by
            nlinarith [abs_nonneg (c k)]
        _ < ε / 2 := (lt_div_iff₀ hC₁).mp hck
    -- Step 7: the second term is `≤ ‖U_k z − V z‖ C₂ < ε/2`.
    have h₂ : |A (U k z - V z) (Q z)| < ε / 2 := by
      have hQ := hZ₀ z hz
      calc |A (U k z - V z) (Q z)| = ‖A (U k z - V z) (Q z)‖ := (Real.norm_eq_abs _).symm
        _ ≤ CA * ‖U k z - V z‖ * ‖Q z‖ := hCA _ _
        _ ≤ CA * ‖U k z - V z‖ * Z₀ := by gcongr
        _ ≤ ‖U k z - V z‖ * (CA * Z₀ + 1) := by
            nlinarith [norm_nonneg (U k z - V z)]
        _ < ε / 2 := (lt_div_iff₀ hC₂).mp hP₂
    -- Step 8: the triangle inequality.
    rw [Real.dist_eq, hdec, abs_neg]
    calc |(ah k z (U k z) (Q z) - A (U k z) (Q z)) + A (U k z - V z) (Q z)|
        ≤ |ah k z (U k z) (Q z) - A (U k z) (Q z)| + |A (U k z - V z) (Q z)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
      _ = ε := add_halves ε
  · -- Claim (ii), Step 9: with `C₃ = R Z₀`, eventually `|d_k| < ε/(C₃ + 1)` and the error bound
    -- holds on `K`, so `|Ψ_k z (Q z)| ≤ |d_k| C₃ < ε`.
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC₃ : 0 < R * Z₀ + 1 := by positivity
    have hδ : 0 < ε / (R * Z₀ + 1) := by positivity
    filter_upwards [Metric.tendsto_nhds.mp hd _ hδ, hΨ] with k hdk hΨk z hz
    rw [Real.dist_eq, sub_zero] at hdk
    have hQ := hZ₀ z hz
    have hRz := hR z hz
    rw [Real.dist_eq, zero_sub, abs_neg]
    calc |Ψ k z (Q z)| ≤ d k * ‖z‖ ^ α * ‖Q z‖ := hΨk z hz _
      _ ≤ |d k| * ‖z‖ ^ α * ‖Q z‖ := by
          gcongr
          exact le_abs_self (d k)
      _ ≤ |d k| * R * Z₀ := by gcongr
      _ ≤ |d k| * (R * Z₀ + 1) := by nlinarith [abs_nonneg (d k)]
      _ < ε := (lt_div_iff₀ hC₃).mp hdk

namespace Submission

/-- **Limit of the weak equations on growing balls** (blow-up step of the Schauder estimate behind
Simon 7.1).  Let `R_k → ∞`, `c_k, d_k → 0`, `V` continuous and `U_k → V` uniformly on every closed
ball `B_r(0)`.  Suppose that on `B̆_{R_k}(0)` the coefficients `â_k`, `Ψ_k` are continuous with
`|â_k(z)[P][Q] − A[P][Q]| ≤ c_k (1 + |z|^α) ‖P‖ ‖Q‖` and `|Ψ_k(z)[Q]| ≤ d_k |z|^α ‖Q‖`, and that
`∫_{B̆_{R_k}(0)} â_k[U_k][Dζ] = ∫_{B̆_{R_k}(0)} Ψ_k[Dζ]` for every `C¹` map `ζ` with compact support
in `B̆_{R_k}(0)`.  Then `∫ A[V][Dζ] = 0` for every compactly supported `C¹` map `ζ : ℝⁿ → ℝ^ℓ`: if
`spt ζ ⊆ B_r(0)`, then for `k` large `B_r(0) ⊆ B̆_{R_k}(0)`, the integrands vanish off `B_r(0)` and
converge uniformly on it, to `A[V][Dζ]` and to `0`, so
`∫ A[V][Dζ] = lim ∫ â_k[U_k][Dζ] = lim ∫ Ψ_k[Dζ] = 0`. -/
theorem dohr_eb_sch_bu_weak_eq_limit : ∀ (n ℓ : ℕ) (α : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)) (R c d : ℕ → ℝ), 0 ≤ α → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → Continuous V → (∀ r : ℝ, TendstoUniformlyOn U V atTop (closedBall (0 : Rn n) r)) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ContinuousOn (U k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - A P Q| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (U k z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (V z) (fderiv ℝ ζ z) = 0 := by
  intro n ℓ α A ah Ψ U V R c d hα hR hc hd hVc hUV hahc hΨc hUc hah hΨ hweak ζ hζ hζc
  -- Step 1: `tsupport ζ ⊆ B_r(0)`; `Z` bounds `‖Dζ‖` and `N` bounds `‖V‖` on `B_r(0)`.
  have hT : IsCompact (tsupport ζ) := hζc.isCompact
  obtain ⟨r, hTr⟩ := hT.isBounded.subset_closedBall (0 : Rn n)
  have hK : IsCompact (closedBall (0 : Rn n) r) := isCompact_closedBall 0 r
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  obtain ⟨Z, hZ⟩ := hDζ.bounded_above_of_compact_support (hζc.fderiv ℝ)
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hVc.continuousOn
  -- `Dζ` vanishes off `tsupport ζ`, hence off `B_r(0)`.
  have hDζ0 : ∀ z, z ∉ tsupport ζ → fderiv ℝ ζ z = 0 := fun z hz =>
    Function.notMem_support.1 fun h => hz (support_fderiv_subset ℝ h)
  have hDζK : ∀ z, z ∉ closedBall (0 : Rn n) r → fderiv ℝ ζ z = 0 := fun z hz =>
    hDζ0 z fun h => hz (hTr h)
  -- Step 2: for `k` large, `r < R_k`, so `B_r(0) ⊆ B̆_{R_k}(0)`.
  have hRr : ∀ᶠ k in atTop, r < R k := hR.eventually_gt_atTop r
  -- Step 3: for `k` large both integrands are integrable, and the weak equation on `B̆_{R_k}(0)`
  -- becomes `∫ â_k[U_k][Dζ] = ∫ Ψ_k[Dζ]` over `ℝⁿ`; `A[V][Dζ]` is integrable.
  have hloc : ∀ᶠ k in atTop,
      (Integrable fun z => ah k z (U k z) (fderiv ℝ ζ z)) ∧
      (Integrable fun z => Ψ k z (fderiv ℝ ζ z)) ∧
      ∫ z, ah k z (U k z) (fderiv ℝ ζ z) = ∫ z, Ψ k z (fderiv ℝ ζ z) := by
    filter_upwards [hRr] with k hk
    have hTR : tsupport ζ ⊆ ball (0 : Rn n) (R k) := hTr.trans (closedBall_subset_ball hk)
    have hFk : (Integrable fun z => ah k z (U k z) (fderiv ℝ ζ z)) ∧
        ∫ z in ball (0 : Rn n) (R k), ah k z (U k z) (fderiv ℝ ζ z) =
          ∫ z, ah k z (U k z) (fderiv ℝ ζ z) :=
      (Submission.dohr_eb_sch_bu_wel_localized_integral n
        (fun z => ah k z (U k z) (fderiv ℝ ζ z)) _ _ isOpen_ball hT hTR
        ((hahc k).comp (continuousOn_id.prodMk ((hUc k).prodMk hDζ.continuousOn))
          fun z hz => ⟨hz, mem_univ _⟩)
        fun z hz => by simp only [hDζ0 z hz, map_zero]).2
    have hEk : (Integrable fun z => Ψ k z (fderiv ℝ ζ z)) ∧
        ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z) = ∫ z, Ψ k z (fderiv ℝ ζ z) :=
      (Submission.dohr_eb_sch_bu_wel_localized_integral n (fun z => Ψ k z (fderiv ℝ ζ z)) _ _
        isOpen_ball hT hTR ((hΨc k).clm_apply hDζ.continuousOn)
        fun z hz => by simp only [hDζ0 z hz, map_zero]).2
    exact ⟨hFk.1, hEk.1, by rw [← hFk.2, ← hEk.2]; exact hweak k ζ hζ hζc hTR⟩
  have hF0 : Integrable fun z => A (V z) (fderiv ℝ ζ z) :=
    (Submission.dohr_eb_sch_bu_wel_localized_integral n (fun z => A (V z) (fderiv ℝ ζ z)) univ _
      isOpen_univ hT (subset_univ _) ((A.continuous.comp hVc).clm_apply hDζ).continuousOn
      fun z hz => by simp only [hDζ0 z hz, map_zero]).2.1
  -- Steps 4–5, pointwise: on `B_r(0)`, `â_k[U_k][Dζ] → A[V][Dζ]` and `Ψ_k[Dζ] → 0` uniformly.
  obtain ⟨hF, hE⟩ := Submission.dohr_eb_sch_bu_wel_pairing_tendstoUniformlyOn n ℓ α r Z N A ah Ψ
    U V (fderiv ℝ ζ) (closedBall 0 r) c d hα hc hd (hUV r)
    (fun z hz => mem_closedBall_zero_iff.1 hz) (fun z _ => hZ z) hN
    (hRr.mono fun k hk z hz P P' => hah k z (closedBall_subset_ball hk hz) P P')
    (hRr.mono fun k hk z hz P => hΨ k z (closedBall_subset_ball hk hz) P)
  -- Steps 4–5, integrals: all integrands vanish off `B_r(0)`, so
  -- `∫ â_k[U_k][Dζ] → ∫ A[V][Dζ]` and `∫ Ψ_k[Dζ] → 0`.
  have hFlim := Submission.dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn n
    (closedBall 0 r) (fun k z => ah k z (U k z) (fderiv ℝ ζ z))
    (fun z => A (V z) (fderiv ℝ ζ z)) hK (hloc.mono fun k hk => hk.1) hF0
    (Eventually.of_forall fun k z hz => by simp only [hDζK z hz, map_zero])
    (fun z hz => by simp only [hDζK z hz, map_zero]) hF
  have hElim := Submission.dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn n
    (closedBall 0 r) (fun k z => Ψ k z (fderiv ℝ ζ z)) (fun _ => (0 : ℝ)) hK
    (hloc.mono fun k hk => hk.2.1) (integrable_zero _ _ _)
    (Eventually.of_forall fun k z hz => by simp only [hDζK z hz, map_zero])
    (fun _ _ => rfl) hE
  -- Step 6: `∫ A[V][Dζ] = lim ∫ â_k[U_k][Dζ] = lim ∫ Ψ_k[Dζ] = 0`.
  rw [integral_zero] at hElim
  exact tendsto_nhds_unique hFlim (hElim.congr' (hloc.mono fun k hk => hk.2.2.symm))
/-- **Blow-up limit for the Schauder estimate** (compactness and limit equation of the blow-up
argument).  Rescaled solutions `W_k` of `div (âₖ(z) DW_k) = div Ψ_k` on growing balls `B_{R_k}(0)`,
with `DW_k` uniformly `K`-`α`-Hölder, `DW_k(0) = 0` and `|DW_k(e_k)| = 1` at a point `|e_k| ≤ 1`,
and coefficients whose oscillation `c_k` and right sides `d_k` tend to `0`, have a subsequential
limit `W ∈ C¹(ℝⁿ)` with `DW(0) = 0`, `DW` globally `K`-`α`-Hölder, `|DW(e₀)| = 1`, solving the
constant-coefficient equation `∫ A[DW][Dζ] = 0` for a limit `A` of the frozen coefficients
`âₖ(0)`, which keeps their Legendre and boundedness constants.  This is the compactness step of
the blow-up proof of the Schauder estimates (L. Simon, *Schauder estimates by scaling*,
Calc. Var. PDE 5 (1997), 391–407). -/
theorem dohr_eb_sch_bu_blowup_limit : ∀ (n ℓ : ℕ) (α lam M K : ℝ) (W : ℕ → Rn n → Rn ℓ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : ℕ → Rn n) (R c d : ℕ → ℝ), 0 < α → 0 ≤ K → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → (∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k))) → (∀ k, W k 0 = 0) → (∀ k, fderiv ℝ (W k) 0 = 0) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k), ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ ah k 0 P P) → (∀ k, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - ah k 0 P Q| ≤ c k * ‖z‖ ^ α * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → (∀ k, ‖e k‖ ≤ 1) → (∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1) → ∃ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W' : Rn n → Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) ∧ (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ ContDiff ℝ 1 W' ∧ (∀ z z' : Rn n, ‖fderiv ℝ W' z - fderiv ℝ W' z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (fderiv ℝ W' z) (fderiv ℝ ζ z) = 0) ∧ fderiv ℝ W' 0 = 0 ∧ ∃ e₀ : Rn n, ‖fderiv ℝ W' e₀‖ = 1 := by
  intro n ℓ α lam M K W ah Ψ e R c d hα hK hR hc hd hW hW0 hDW0 hHol hahc hΨc hell hbd hahz hΨ
    hweak he hunit
  -- At the default pending-synthesis depth, instance search does not find the operator-norm
  -- structure on the space of bilinear forms on `L(ℝⁿ, ℝ^ℓ)`, so it is supplied explicitly; this
  -- space is finite-dimensional, hence proper.
  let : NormedAddCommGroup ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  have : FiniteDimensional ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional (𝕜 := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
  have : ProperSpace ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    FiniteDimensional.proper_real _
  -- Step 1: `‖âₖ(0)‖ ≤ max M 0`, so a subsequence `â_{φA j}(0)` converges to some `A` in the
  -- finite-dimensional (hence proper) space of bilinear forms.
  obtain ⟨A, -, φA, hφA, hA⟩ :=
    (isCompact_closedBall (0 : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (max M 0)).tendsto_subseq (x := fun k => ah k 0) fun k => by
        rw [mem_closedBall_zero_iff]
        refine ContinuousLinearMap.opNorm_le_bound₂ _ (le_max_right M 0) fun P Q => ?_
        rw [Real.norm_eq_abs]
        exact (hbd k P Q).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg P)) (norm_nonneg Q))
  -- Step 2: the points `e_{φA j}` lie in `B̄₁(0)`; a further subsequence converges to `e₀`.
  obtain ⟨e₀, -, φe, hφe, he₀⟩ := (isCompact_closedBall (0 : Rn n) 1).tendsto_subseq
    (x := fun j => e (φA j)) fun j => mem_closedBall_zero_iff.mpr (he (φA j))
  -- Step 3: a diagonal subsequence along which `DW` converges locally uniformly to a continuous,
  -- globally `K`-`α`-Hölder `V` with `V(0) = 0`.
  obtain ⟨φ₂, V, hφ₂, hV0, hVc, hVHol, hVunif⟩ :=
    Submission.dohr_eb_sch_bu_holder_diag_subseq n ℓ α K (fun j => fderiv ℝ (W (φA (φe j))))
      (fun j => R (φA (φe j))) hα hK (hR.comp (hφA.comp hφe).tendsto_atTop)
      (fun j => hDW0 (φA (φe j))) (fun j => hHol (φA (φe j)))
  set ψ : ℕ → ℕ := fun i => φA (φe (φ₂ i))
  have hψ : Tendsto ψ atTop atTop := ((hφA.comp hφe).comp hφ₂).tendsto_atTop
  have hU : ∀ r : ℝ, TendstoUniformlyOn (fun i => fderiv ℝ (W (ψ i))) V atTop
      (closedBall (0 : Rn n) r) := hVunif
  -- Step 4: the limit `W'` is `C¹` on `ℝⁿ` with `DW' = V`.
  obtain ⟨W', hW'c, hW'V⟩ := Submission.dohr_eb_sch_bu_contDiff_of_fderiv_tendsto n ℓ
    (fun i => W (ψ i)) V (fun i => R (ψ i)) (hR.comp hψ) (fun i => hW (ψ i))
    (fun i => hW0 (ψ i)) hVc hU
  -- Step 5: `|âψᵢ(z)[P][Q] - A[P][Q]| ≤ (|c_{ψ i}| + ‖âψᵢ(0) - A‖)(1 + |z|^α)‖P‖‖Q‖`.
  have hAψ : Tendsto (fun i => ah (ψ i) 0) atTop (𝓝 A) := hA.comp (hφe.comp hφ₂).tendsto_atTop
  have hε : Tendsto (fun i => ‖ah (ψ i) 0 - A‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hAψ
  have hεb : ∀ i, ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah (ψ i) 0 P Q - A P Q| ≤ ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖ := fun i P Q => by
    have h := (ah (ψ i) 0 - A).le_opNorm₂ P Q
    rwa [sub_apply, sub_apply, Real.norm_eq_abs] at h
  have hc' : Tendsto (fun i => |c (ψ i)| + ‖ah (ψ i) 0 - A‖) atTop (𝓝 0) := by
    simpa using (hc.comp hψ).abs.add hε
  have hcoef : ∀ i, ∀ z ∈ ball (0 : Rn n) (R (ψ i)), ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah (ψ i) z P Q - A P Q| ≤ (|c (ψ i)| + ‖ah (ψ i) 0 - A‖) * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := by
    intro i z hz P Q
    have h1 := hahz (ψ i) z hz P Q
    have h2 := hεb i P Q
    have hzα : 0 ≤ ‖z‖ ^ α := Real.rpow_nonneg (norm_nonneg z) α
    have hPQ : 0 ≤ ‖P‖ * ‖Q‖ := mul_nonneg (norm_nonneg P) (norm_nonneg Q)
    have hε0 : 0 ≤ ‖ah (ψ i) 0 - A‖ := norm_nonneg _
    have hc0 : 0 ≤ |c (ψ i)| - c (ψ i) := sub_nonneg.mpr (le_abs_self _)
    calc |ah (ψ i) z P Q - A P Q|
        ≤ |ah (ψ i) z P Q - ah (ψ i) 0 P Q| + |ah (ψ i) 0 P Q - A P Q| := abs_sub_le _ _ _
      _ ≤ c (ψ i) * ‖z‖ ^ α * ‖P‖ * ‖Q‖ + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖ := add_le_add h1 h2
      _ ≤ (|c (ψ i)| + ‖ah (ψ i) 0 - A‖) * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := by
        nlinarith [mul_nonneg (abs_nonneg (c (ψ i))) hPQ, mul_nonneg (mul_nonneg hc0 hzα) hPQ,
          mul_nonneg (mul_nonneg hε0 hzα) hPQ]
  -- Step 6: the weak equations pass to the limit.
  have hlim := Submission.dohr_eb_sch_bu_weak_eq_limit n ℓ α A (fun i => ah (ψ i))
    (fun i => Ψ (ψ i)) (fun i => fderiv ℝ (W (ψ i))) V (fun i => R (ψ i))
    (fun i => |c (ψ i)| + ‖ah (ψ i) 0 - A‖) (fun i => d (ψ i)) hα.le (hR.comp hψ) hc'
    (hd.comp hψ) hVc hU (fun i => hahc (ψ i)) (fun i => hΨc (ψ i))
    (fun i => (hW (ψ i)).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl) hcoef
    (fun i => hΨ (ψ i)) (fun i => hweak (ψ i))
  -- Step 7: the Legendre and boundedness constants pass to the limit `A`.
  have hellA : ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P := by
    intro P
    have hT : Tendsto (fun i => A P P + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖P‖) atTop
        (𝓝 (A P P + 0 * ‖P‖ * ‖P‖)) :=
      tendsto_const_nhds.add ((hε.mul_const ‖P‖).mul_const ‖P‖)
    rw [zero_mul, zero_mul, add_zero] at hT
    refine ge_of_tendsto' hT fun i => ?_
    have h1 := hell (ψ i) P
    have h2 := hεb i P P
    have h3 := le_abs_self (ah (ψ i) 0 P P - A P P)
    linarith
  have hbdA : ∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ M * ‖P‖ * ‖Q‖ := by
    intro P Q
    have hT : Tendsto (fun i => M * ‖P‖ * ‖Q‖ + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖) atTop
        (𝓝 (M * ‖P‖ * ‖Q‖ + 0 * ‖P‖ * ‖Q‖)) :=
      tendsto_const_nhds.add ((hε.mul_const ‖P‖).mul_const ‖Q‖)
    rw [zero_mul, zero_mul, add_zero] at hT
    refine ge_of_tendsto' hT fun i => ?_
    have h1 := abs_le.mp (hbd (ψ i) P Q)
    have h2 := abs_le.mp (hεb i P Q)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- Step 8: `DWψᵢ(eψᵢ) → V(e₀)`, and these have norm `1` for large `i`, so `|V(e₀)| = 1`.
  have heψ : Tendsto (fun i => e (ψ i)) atTop (𝓝[closedBall (0 : Rn n) 1] e₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨he₀.comp hφ₂.tendsto_atTop,
      Eventually.of_forall fun i => mem_closedBall_zero_iff.mpr (he (ψ i))⟩
  have hVe₀ : ‖V e₀‖ = 1 :=
    tendsto_nhds_unique ((hU 1).tendsto_comp hVc.continuousWithinAt heψ).norm
      (tendsto_const_nhds.congr' ((hψ.eventually hunit).mono fun i hi => hi.symm))
  -- Step 9: conclusion.
  refine ⟨A, W', hellA, hbdA, hW'c, fun z z' => ?_, fun ζ hζ hζc => ?_, ?_, e₀, ?_⟩
  · rw [hW'V z, hW'V z']
    exact hVHol z z'
  · simp_rw [hW'V]
    exact hlim ζ hζ hζc
  · rw [hW'V 0, hV0]
  · rw [hW'V e₀]
    exact hVe₀
/-- **Zero mean of a linear form of `Dζ`** (step (1a) of the Schauder estimate in the elliptic
bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  For a continuous linear form `c` on
`L(ℝⁿ, ℝ^ℓ)` and a compactly supported `C¹` map `ζ : ℝⁿ → ℝ^ℓ`, `∫ c(Dζ(x)) dx = 0`.
Proof: `Dζ` is continuous with compact support, hence integrable, and `∫ c(Dζ) = c(∫ Dζ)`.
By translation invariance of Lebesgue measure, `y ↦ ∫ ζ(x + y) dx` is constant; differentiating
it at `0` under the integral sign (the derivatives `Dζ(x + y)`, `|y| < 1`, are bounded by a
constant times the indicator of a fixed ball) gives `∫ Dζ = 0`. -/
theorem dohr_eb_sch_integral_clm_fderiv_eq_zero : ∀ (n ℓ : ℕ) (c : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, c (fderiv ℝ ζ x) = 0 := by
  intro n ℓ c ζ hζ hcs
  -- Step 1: `Dζ` is continuous with compact support, hence integrable.
  have hcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hcsD : HasCompactSupport (fderiv ℝ ζ) := hcs.fderiv ℝ
  have hint : Integrable (fderiv ℝ ζ) := hcont.integrable_of_hasCompactSupport hcsD
  -- Step 2: pull `c` out of the integral; it suffices that `∫ Dζ = 0`.
  rw [ContinuousLinearMap.integral_comp_comm c hint]
  suffices h : ∫ x, fderiv ℝ ζ x = 0 by rw [h, map_zero]
  -- Step 3: `‖Dζ‖ ≤ C` everywhere and `tsupport Dζ ⊆ B_R(0)`.
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcsD
  obtain ⟨R, hR⟩ := hcsD.isCompact.isBounded.subset_closedBall (0 : Rn n)
  -- Step 4: differentiate `y ↦ ∫ ζ(x + y) dx` at `0` under the integral sign.
  have hderiv : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (∫ x, fderiv ℝ ζ (x + 0)) 0 := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball (0 : Rn n) 1)
      (F' := fun y x => fderiv ℝ ζ (x + y))
      (bound := (closedBall (0 : Rn n) (R + 1)).indicator fun _ => C)
      (ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y =>
        (hζ.continuous.comp (continuous_add_const y)).aestronglyMeasurable
    · simpa using hζ.continuous.integrable_of_hasCompactSupport hcs
    · exact (hcont.comp (continuous_add_const 0)).aestronglyMeasurable
    · refine Eventually.of_forall fun x y hy => ?_
      show ‖fderiv ℝ ζ (x + y)‖ ≤ (closedBall (0 : Rn n) (R + 1)).indicator (fun _ => C) x
      by_cases hx : x ∈ closedBall (0 : Rn n) (R + 1)
      · rw [indicator_of_mem hx]
        exact hC _
      · have hxy : x + y ∉ tsupport (fderiv ℝ ζ) := fun h => hx (by
          have h1 := hR h
          rw [mem_closedBall_zero_iff] at h1 ⊢
          rw [mem_ball_zero_iff] at hy
          calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
            _ ≤ R + 1 := by linarith)
        rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hxy, norm_zero]
    · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    · exact Eventually.of_forall fun x y _ =>
        (hasFDerivAt_comp_add_left x).2 ((hζ.differentiable one_ne_zero (x + y)).hasFDerivAt)
  -- Step 5: by translation invariance that function is constant, so its derivative is `0`.
  have hzero : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (0 : Rn n →L[ℝ] Rn ℓ) 0 :=
    (hasFDerivAt_const (∫ x, ζ x) (0 : Rn n)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => integral_add_right_eq_self ζ y)
  simpa using hderiv.unique hzero

end Submission
/-- **Interpolation bound for `Dw`** (step (1b) of the Schauder estimate in the elliptic bootstrap
for Simon 7.1).  If `w` is `C¹` on `B̆_ρ(x)` with `|w| ≤ S` there and
`‖Dw(y) − Dw(z)‖ ≤ K |y − z|^α` for `y, z ∈ B̆_ρ(x)`, then `‖Dw(x)‖ ≤ 2S/t + t^α K` for every
`t ∈ (0, ρ)` (operator norm). -/
theorem Submission.dohr_eb_sch_fderiv_norm_interpolation : ∀ (n ℓ : ℕ) (w : Rn n → Rn ℓ) (x : Rn n) (ρ t α S K : ℝ), 0 ≤ α → 0 ≤ K → 0 < t → t < ρ → ContDiffOn ℝ 1 w (ball x ρ) → (∀ y ∈ ball x ρ, ‖w y‖ ≤ S) → (∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤ K * ‖y - z‖ ^ α) → ‖fderiv ℝ w x‖ ≤ 2 * S / t + t ^ α * K := by
  intro n ℓ w x ρ t α S K hα hK ht htρ hw hS hH
  -- Step 1: `S ≥ |w(x)| ≥ 0`, so `B = 2S/t + t^α K ≥ 0`.
  have hxB : x ∈ ball x ρ := mem_ball_self (ht.trans htρ)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hB : 0 ≤ 2 * S / t + t ^ α * K :=
    add_nonneg (div_nonneg (mul_nonneg zero_le_two hS0) ht.le)
      (mul_nonneg (Real.rpow_nonneg ht.le α) hK)
  -- Step 2: `B_t(x) ⊆ B̆_ρ(x)`, and `w` has derivative `Dw(y)` at every `y ∈ B_t(x)`.
  have hsub : closedBall x t ⊆ ball x ρ := closedBall_subset_ball htρ
  have hdiff : ∀ y ∈ closedBall x t, HasFDerivWithinAt w (fderiv ℝ w y) (closedBall x t) y :=
    fun y hy => (((hw.differentiableOn one_ne_zero) y (hsub hy)).differentiableAt
      (isOpen_ball.mem_nhds (hsub hy))).hasFDerivAt.hasFDerivWithinAt
  -- Step 3: `‖Dw(y) − Dw(x)‖ ≤ K t^α` on `B_t(x)`.
  have hbound : ∀ y ∈ closedBall x t, ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * t ^ α := by
    intro y hy
    calc ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * ‖y - x‖ ^ α := hH y (hsub hy) x hxB
      _ ≤ K * t ^ α := by
        gcongr
        exact mem_closedBall_iff_norm.mp hy
  -- Steps 4–5: `|Dw(x) e| ≤ B` for every unit vector `e`.
  have hunit : ∀ e : Rn n, ‖e‖ = 1 → ‖fderiv ℝ w x e‖ ≤ 2 * S / t + t ^ α * K := by
    intro e he
    have hte : ‖t • e‖ = t := by rw [norm_smul, he, Real.norm_of_nonneg ht.le, mul_one]
    have hxe : x + t • e ∈ closedBall x t := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, hte]
    -- Step 4: the mean value inequality for `h(y) = w(y) − Dw(x)(y − x)` on `B_t(x)` gives
    -- `|w(x + te) − w(x) − t Dw(x)e| ≤ K t^α · t`.
    have hmv := (convex_closedBall x t).norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff
      hbound (mem_closedBall_self ht.le) hxe
    rw [add_sub_cancel_left, hte, map_smul] at hmv
    -- Step 5: `t |Dw(x)e| ≤ |w(x + te) − w(x)| + |w(x + te) − w(x) − t Dw(x)e| ≤ 2S + K t^α t`.
    have h1 : ‖w (x + t • e)‖ ≤ S := hS _ (hsub hxe)
    have h2 : ‖w x‖ ≤ S := hS x hxB
    have key : t * ‖fderiv ℝ w x e‖ ≤ 2 * S + K * t ^ α * t :=
      calc t * ‖fderiv ℝ w x e‖ = ‖t • fderiv ℝ w x e‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht.le]
        _ = ‖(w (x + t • e) - w x) - (w (x + t • e) - w x - t • fderiv ℝ w x e)‖ := by
            congr 1; abel
        _ ≤ ‖w (x + t • e) - w x‖ + ‖w (x + t • e) - w x - t • fderiv ℝ w x e‖ :=
            norm_sub_le _ _
        _ ≤ (‖w (x + t • e)‖ + ‖w x‖) + K * t ^ α * t := add_le_add (norm_sub_le _ _) hmv
        _ ≤ 2 * S + K * t ^ α * t := by linarith
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  -- Step 6: `|Dw(x) v| = |v| |Dw(x)(v/|v|)| ≤ B |v|`, so `‖Dw(x)‖ ≤ B`.
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : fderiv ℝ w x v = ‖v‖ • fderiv ℝ w x (‖v‖⁻¹ • v) := by
    rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  rw [hv', norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
  exact (mul_le_mul_of_nonneg_left (hunit _ (norm_smul_inv_norm hv)) (norm_nonneg v)).trans_eq
    (mul_comm _ _)
namespace Submission

/-- **Affine rescaling of `C¹` weak solutions** (scaling step of the Schauder estimate in the
elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  Let `w` be `C¹` on the open
set `U` with `∫_U a(x)[Dw][Dζ] = ∫_U Φ(x)[Dζ]` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let
`B_{ρr}(y + ρz₀) ⊆ U`, `ρ > 0`.  Then `w̃(z) = w(y + ρz)` is `C¹` on `B_r(z₀)`,
`Dw̃(z) = ρ Dw(y + ρz)` there, and `∫_{B_r(z₀)} a(y + ρz)[Dw̃][Dζ] = ∫_{B_r(z₀)} (ρΦ(y + ρz))[Dζ]`
for every `ζ ∈ C¹_c(B_r(z₀); ℝ^ℓ)`.
Proof: with `T z = y + ρz`, the test function `ζ ∘ T⁻¹` is admissible on `U`; both integrands
are `ρ²` times the original ones composed with `T` and vanish off the supports, and
`∫ H(y + ρz) dz = ρ⁻ⁿ ∫ H` holds for every `H` (no integrability needed). -/
theorem dohr_eb_sch_weak_eq_affine_rescale : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (U : Set (Rn n)) (y z₀ : Rn n) (ρ r : ℝ), 0 < ρ → IsOpen U → ball (y + ρ • z₀) (ρ * r) ⊆ U → ContDiffOn ℝ 1 w U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiffOn ℝ 1 (fun z => w (y + ρ • z)) (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball z₀ r → ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
  intro n ℓ a Φ w U y z₀ ρ r hρ hU hball hw hweak
  have hρ0 : ρ ≠ 0 := hρ.ne'
  -- Step 0: `T z = y + ρ • z` maps `B_r(z₀)` into `B_{ρ r}(y + ρ z₀) ⊆ U`.
  have hT : MapsTo (fun z : Rn n => y + ρ • z) (ball z₀ r) U := by
    intro z hz
    apply hball
    show dist (y + ρ • z) (y + ρ • z₀) < ρ * r
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_mul_of_pos_left (mem_ball.mp hz) hρ
  -- `T` is affine with derivative `ρ • id` everywhere.
  have hTd : ∀ z : Rn n,
      HasFDerivAt (fun z : Rn n => y + ρ • z) (ρ • ContinuousLinearMap.id ℝ (Rn n)) z :=
    fun z => ((hasFDerivAt_id z).const_smul ρ).const_add y
  -- Step 1 (ii): chain rule at points of `B_r(z₀)`, where `w` is differentiable.
  have hderiv : ∀ z ∈ ball z₀ r,
      fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z) := by
    intro z hz
    have hwd : DifferentiableAt ℝ w (y + ρ • z) :=
      (hw.differentiableOn one_ne_zero _ (hT hz)).differentiableAt (hU.mem_nhds (hT hz))
    have h := hwd.hasFDerivAt.comp z (hTd z)
    rw [show (fun z => w (y + ρ • z)) = w ∘ (fun z : Rn n => y + ρ • z) from rfl, h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  have hTC : ContDiff ℝ 1 (fun z : Rn n => y + ρ • z) :=
    contDiff_const.add (contDiff_id.const_smul ρ)
  refine ⟨hw.comp hTC.contDiffOn hT, hderiv, ?_⟩
  -- Step 2: transfer the test function, `ζ' = ζ ∘ T⁻¹`.
  intro ζ hζ hζc hζs
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : Rn n → Rn ℓ, ζ' = fun x => ζ (ρ⁻¹ • (x - y)) := ⟨_, rfl⟩
  have hζ'T : ∀ z, ζ' (y + ρ • z) = ζ z := by
    intro z
    simp [hζ', inv_smul_smul₀ hρ0]
  have hζ'C : ContDiff ℝ 1 ζ' := by
    rw [hζ']
    exact hζ.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
  have hK : IsCompact ((fun z : Rn n => y + ρ • z) '' tsupport ζ) :=
    hζc.isCompact.image hTC.continuous
  have hζ'K : ∀ x, x ∉ (fun z : Rn n => y + ρ • z) '' tsupport ζ → ζ' x = 0 := by
    intro x hx
    rw [hζ']
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine ⟨ρ⁻¹ • (x - y), hmem, ?_⟩
    simp [smul_inv_smul₀ hρ0]
  have hζ'c : HasCompactSupport ζ' := HasCompactSupport.intro hK hζ'K
  have hζ'sK : tsupport ζ' ⊆ (fun z : Rn n => y + ρ • z) '' tsupport ζ :=
    closure_minimal (Function.support_subset_iff'.mpr hζ'K) hK.isClosed
  have hζ's : tsupport ζ' ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hζ'sK hx
    exact hT (hζs hz)
  have hweak' := hweak ζ' hζ'C hζ'c hζ's
  -- `Dζ(z) = ρ • Dζ'(T z)` for every `z`.
  have hζd : ∀ z, fderiv ℝ ζ z = ρ • fderiv ℝ ζ' (y + ρ • z) := by
    intro z
    have h := (hζ'C.differentiable one_ne_zero (y + ρ • z)).hasFDerivAt.comp z (hTd z)
    have hfun : ζ' ∘ (fun z : Rn n => y + ρ • z) = ζ := funext hζ'T
    rw [hfun] at h
    rw [h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  -- Step 3: the integrands over `U` vanish off `U`.
  have hF0 : ∀ x, x ∉ U → a x (fderiv ℝ w x) (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  have hG0 : ∀ x, x ∉ U → Φ x (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 4: pointwise identities.
  have hFt : ∀ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) =
      ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    by_cases hz : z ∈ ball z₀ r
    · rw [hderiv z hz, hζd z]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    · have h1 : fderiv ℝ ζ z = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h))
      have h2 : fderiv ℝ ζ' (y + ρ • z) = 0 := by
        have h3 := hζd z
        rw [h1] at h3
        exact (smul_eq_zero.mp h3.symm).resolve_left hρ0
      rw [h1, h2]
      simp
  have hGt : ∀ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) =
      ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    rw [hζd z]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  -- Step 5: change of variables, valid without integrability.
  have hcov : ∀ H : Rn n → ℝ,
      ∫ z, H (y + ρ • z) = |(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, H x := by
    intro H
    rw [Measure.integral_comp_smul volume (fun x => H (y + x)) ρ, integral_add_left_eq_self H y]
  -- Step 6: conclusion.
  calc ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z)
      = ∫ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]
    _ = ∫ z, ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
        congr 1
        funext z
        exact hFt z
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| •
          ∫ x, a x (fderiv ℝ w x) (fderiv ℝ ζ' x)) := by
        rw [integral_const_mul, hcov (fun x => a x (fderiv ℝ w x) (fderiv ℝ ζ' x))]
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, Φ x (fderiv ℝ ζ' x)) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0, hweak',
          setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
    _ = ∫ z, ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
        rw [integral_const_mul, hcov (fun x => Φ x (fderiv ℝ ζ' x))]
    _ = ∫ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        congr 1
        funext z
        exact (hGt z).symm
    _ = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]
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
/-- Cutoff for the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): there is `K ≥ 0` such that for every `n`,
`y ∈ ℝⁿ` and `ρ > 0` some `C¹` function `η : ℝⁿ → [0, 1]` equals `1` on `B̆_ρ(y)`, has compact
support with `tsupport η ⊆ B̆_{2ρ}(y)`, and satisfies `‖Dη(x)‖ ≤ K/ρ`.  Here
`η(x) = ψ(‖x − y‖²/ρ²)` with `ψ(s) = S((3 − s)/2)`, `S = Real.smoothTransition`, and
`K = 4 sup |ψ'|`. -/
theorem dohr_eb_sch_cacc_exists_cutoff : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (y : Rn n) (ρ : ℝ), 0 < ρ → ∃ η : Rn n → ℝ, ContDiff ℝ 1 η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ ball y ρ, η x = 1) ∧ HasCompactSupport η ∧ tsupport η ⊆ ball y (2 * ρ) ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ K / ρ := by
  -- Step 1: the profile `ψ(s) = S((3 − s)/2)` is `C¹`; `ψ = 1` for `s ≤ 1`, `ψ = 0` for `s ≥ 3`.
  set ψ : ℝ → ℝ := fun s => Real.smoothTransition ((3 - s) / 2) with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    (Real.smoothTransition.contDiff (n := 1)).comp ((contDiff_const.sub contDiff_id).div_const _)
  -- Step 2: `ψ'` is continuous and vanishes off `[1, 3]`, so `|ψ'| ≤ cψ` with `cψ ≥ 0`;
  -- `K = 4 cψ`.
  have hψ'c : Continuous (deriv ψ) := hψc.continuous_deriv le_rfl
  have hψ'0 : ∀ s, s ∉ Icc (1 : ℝ) 3 → deriv ψ s = 0 := by
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.one_of_one_le (by linarith [mem_Iio.mp ht])
      rw [hev.deriv_eq, deriv_const]
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Ioi.mp ht])
      rw [hev.deriv_eq, deriv_const]
  obtain ⟨cψ, hcψ⟩ : ∃ cψ, ∀ s, ‖deriv ψ s‖ ≤ cψ := by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (hψ'c.continuousOn (s := Icc (1 : ℝ) 3))
    refine ⟨max C 0, fun s => ?_⟩
    by_cases hs : s ∈ Icc (1 : ℝ) 3
    · exact (hC s hs).trans (le_max_left _ _)
    · rw [hψ'0 s hs, norm_zero]
      exact le_max_right _ _
  have hcψ0 : 0 ≤ cψ := (norm_nonneg _).trans (hcψ 0)
  refine ⟨4 * cψ, by positivity, ?_⟩
  -- Step 3: for `n`, `y` and `ρ > 0` take `η(x) = ψ(‖x − y‖²/ρ²)`.
  intro n y ρ hρ
  have hρ2 : 0 < ρ ^ 2 := by positivity
  -- Step 4: `η(x) ≠ 0` forces `‖x − y‖² < 3ρ²`, so `tsupport η ⊆ B_{7ρ/4}(y)` (closed ball).
  have hsupp : Function.support (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆
      closedBall y (7 / 4 * ρ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [mem_closedBall, dist_eq_norm]
    by_contra hlt
    push Not at hlt
    apply hx
    simp only [hψ]
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : 3 * ρ ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith
    have h2 : 3 ≤ ‖x - y‖ ^ 2 / ρ ^ 2 := by
      rw [le_div_iff₀ hρ2]
      linarith
    linarith
  have htsupp : tsupport (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆ closedBall y (7 / 4 * ρ) :=
    closure_minimal hsupp isClosed_closedBall
  refine ⟨fun x => ψ (‖x - y‖ ^ 2 / ρ ^ 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `η` is `C¹`: `ψ` composed with the smooth map `x ↦ ‖x − y‖²/ρ²`.
  · exact hψc.comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)
  -- `0 ≤ η ≤ 1` since `0 ≤ S ≤ 1`.
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `η = 1` on `B̆_ρ(y)`: there `‖x − y‖²/ρ² < 1`.
  · intro x hx
    have hx' : ‖x - y‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hx
    have h1 : ‖x - y‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (x - y)]
    have h2 : ‖x - y‖ ^ 2 / ρ ^ 2 < 1 := by
      rw [div_lt_one hρ2]
      exact h1
    simp only [hψ]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  -- Compact support: `tsupport η` is a closed subset of the compact `B_{7ρ/4}(y)`.
  · exact (isCompact_closedBall y (7 / 4 * ρ)).of_isClosed_subset (isClosed_tsupport _) htsupp
  -- `tsupport η ⊆ B_{7ρ/4}(y) ⊆ B̆_{2ρ}(y)`.
  · refine htsupp.trans (closedBall_subset_ball ?_)
    linarith
  -- Step 5: by the chain rule `Dη(x) = ψ'(s) (2/ρ²) ⟨x − y, ·⟩` with `s = ‖x − y‖²/ρ²`, so
  -- `‖Dη(x)‖ = |ψ'(s)| (2/ρ²) ‖x − y‖`; this is `0` if `s > 3`, and if `s ≤ 3` then
  -- `‖x − y‖ ≤ 2ρ` and `‖Dη(x)‖ ≤ cψ (2/ρ²) (2ρ) = 4 cψ/ρ`.
  · intro x
    set s := ‖x - y‖ ^ 2 / ρ ^ 2 with hs
    have hf : HasFDerivAt (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2)
        (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y)) x := by
      have h0 : HasFDerivAt (fun x : Rn n => x - y) (ContinuousLinearMap.id ℝ (Rn n)) x :=
        (hasFDerivAt_id x).sub_const y
      have := h0.norm_sq.mul_const ((ρ ^ 2)⁻¹)
      simp only [div_eq_mul_inv]
      convert this using 1
      ext v
      simp
      ring
    have hψd : HasDerivAt ψ (deriv ψ s) s :=
      ((hψc.differentiable one_ne_zero) s).hasDerivAt
    have hη := hψd.comp_hasFDerivAt x hf
    rw [show (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) =
        ψ ∘ (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2) from rfl, hη.fderiv]
    by_cases h3 : 3 < s
    · rw [hψ'0 s (fun h => by linarith [h.2]), zero_smul, norm_zero]
      positivity
    · push Not at h3
      have hxy : ‖x - y‖ ≤ 2 * ρ := by
        have : ‖x - y‖ ^ 2 ≤ 3 * ρ ^ 2 := by
          have := (div_le_iff₀ hρ2).mp h3
          linarith
        nlinarith [norm_nonneg (x - y)]
      have hnorm : ‖deriv ψ s • (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y))‖ =
          ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖) := by
        rw [norm_smul, norm_smul, innerSL_apply_norm,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ * 2)]
      rw [hnorm]
      calc ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖)
          ≤ cψ * (((ρ ^ 2)⁻¹ * 2) * (2 * ρ)) := by
            gcongr
            exact hcψ s
        _ = 4 * cψ / ρ := by
            field_simp
            ring
/-- Test function of the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap
for Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if `U ⊆ ℝⁿ` is open, `V ∈ C¹(U; ℝ^ℓ)`,
`c ∈ ℝ^ℓ` and `η ∈ C¹_c(ℝⁿ)` with `spt η ⊆ U`, then `ζ = η² (V − c)` is `C¹` on `ℝⁿ` with compact
support in `U`, and `Dζ = η² DV + 2η (V − c) ⊗ Dη` at every point of `ℝⁿ` (off `U` both sides
vanish, whatever the junk value of `DV` there). -/
theorem dohr_eb_sch_cacc_test_function : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) ∧ HasCompactSupport (fun x => η x ^ 2 • (V x - c)) ∧ tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ U ∧ ∀ x, fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x = η x ^ 2 • fderiv ℝ V x + (2 * η x) • (fderiv ℝ η x).smulRight (V x - c) := by
  intro n ℓ U V η c hU hV hη hηc hηU
  -- Step 1: `support ζ ⊆ support η`, so `tsupport ζ ⊆ tsupport η ⊆ U` and `ζ` has compact support.
  -- (Bare `support` is `RectifiableVarifold.support` in this scope.)
  have hsupp : Function.support (fun x => η x ^ 2 • (V x - c)) ⊆ Function.support η := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have htsupp : tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ tsupport η := closure_mono hsupp
  have hcs : HasCompactSupport (fun x => η x ^ 2 • (V x - c)) := hηc.mono hsupp
  -- Step 2: `ζ` is `C¹` on `U`, as the product of `η² ∈ C¹(ℝⁿ)` and `V − c ∈ C¹(U)`.
  have h1 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) U :=
    ((hη.pow 2).contDiffOn).smul (hV.sub contDiffOn_const)
  -- Step 3: `ζ = 0` on the open set `W = (tsupport η)ᶜ`, so `ζ` is `C¹` on `W`.
  have h2 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
    have heq : EqOn (fun _ => (0 : Rn ℓ)) (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
      intro x hx
      have : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
    exact contDiffOn_const.congr (fun x hx => (heq hx).symm)
  -- Step 4: `U ∪ W = ℝⁿ` because `tsupport η ⊆ U`; gluing the two open pieces, `ζ ∈ C¹(ℝⁿ)`.
  have hcover : U ∪ (tsupport η)ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ tsupport η
    · exact Or.inl (hηU hx)
    · exact Or.inr hx
  have hcd : ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) :=
    contDiff_of_contDiffOn_union_of_isOpen h1 h2 hcover hU (isClosed_tsupport η).isOpen_compl
  refine ⟨hcd, hcs, htsupp.trans hηU, fun x => ?_⟩
  by_cases hx : x ∈ U
  -- Step 5: at `x ∈ U`, `D(η²)(x) = 2η(x) Dη(x)` and the product rule for `η² • (V − c)` give
  -- `Dζ(x) = η(x)² DV(x) + (2η(x) Dη(x)).smulRight (V(x) − c)`.
  · have hVd : HasFDerivAt V (fderiv ℝ V x) x :=
      (((hV.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hηd : HasFDerivAt η (fderiv ℝ η x) x := ((hη.differentiable one_ne_zero) x).hasFDerivAt
    have hsq : HasFDerivAt (fun x => η x ^ 2) ((2 * η x) • fderiv ℝ η x) x := by
      have := hηd.mul hηd
      convert this using 1
      · ext y; simp [sq]
      · rw [two_mul, add_smul]
    have hprod := hsq.smul (hVd.sub_const c)
    rw [show (fun x => η x ^ 2 • (V x - c)) = ((fun x => η x ^ 2) • fun x => V x - c) from rfl,
      hprod.fderiv]
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  -- Step 6: at `x ∉ U`, `x ∉ tsupport η ⊇ tsupport ζ`, so `Dζ(x) = 0`, `Dη(x) = 0` and `η(x) = 0`;
  -- both sides vanish.
  · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
    have hxζ : x ∉ tsupport (fun x => η x ^ 2 • (V x - c)) := fun h => hx' (htsupp h)
    rw [fderiv_of_notMem_tsupport ℝ hxζ, fderiv_of_notMem_tsupport ℝ hx',
      image_eq_zero_of_notMem_tsupport hx']
    ext v
    simp
/-- Energy (Caccioppoli) estimate for a constant-coefficient elliptic system.  Let `A` satisfy the
Legendre condition `A[P][P] ≥ λ‖P‖²` and the bound `|A[P][Q]| ≤ Λ‖P‖‖Q‖`, let `V` be `C¹` on the open
set `U` with `∫ A[DV][Dζ] = 0` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let `η ≥ 0` be a `C¹_c` cutoff with
`tsupport η ⊆ U`.  Then `∫ η²‖DV‖² ≤ (4Λ²/λ²) ∫ ‖V − c‖²‖Dη‖²` (lower integrals, in `[0, ∞]`).
Test with `ζ = η²(V − c)` and absorb the cross term by Young's inequality. -/
theorem dohr_eb_sch_cacc_energy_estimate :
    ∀ (n ℓ : ℕ) (lam Lam : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → (∀ x, 0 ≤ η x) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) * ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := by
  intro n ℓ lam Lam A U V η c hlam hcoer hbdd hU hV hη hηc hηU hη0 hweak
  -- the test function `ζ = η² (V - c)` is admissible
  obtain ⟨hζ1, hζc, hζU, hζd⟩ :=
    Submission.dohr_eb_sch_cacc_test_function n ℓ U V η c hU hV hη hηc hηU
  have h0 := hweak _ hζ1 hζc hζU
  -- continuity of the ingredients
  have hDVc : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  have hVc : ContinuousOn V U := hV.continuousOn
  have hDη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDζ : Continuous (fderiv ℝ (fun x => η x ^ 2 • (V x - c))) :=
    hζ1.continuous_fderiv one_ne_zero
  -- the three integrands
  set h : Rn n → ℝ := fun x => A (fderiv ℝ V x) (fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x)
    with hh
  set g1 : Rn n → ℝ := fun x => η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2 with hg1
  set g3 : Rn n → ℝ := fun x => ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 with hg3
  have hsupp_h : Function.support h ⊆ tsupport (fun x => η x ^ 2 • (V x - c)) := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hh, fderiv_of_notMem_tsupport ℝ hxs, map_zero]
  have hsupp_g1 : Function.support g1 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg1, image_eq_zero_of_notMem_tsupport hxs]
  have hsupp_g3 : Function.support g3 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg3, fderiv_of_notMem_tsupport ℝ hxs]
  -- continuous on `U` with `tsupport ⊆ U`, hence continuous with compact support
  have hcont_h : Continuous h := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_h (isClosed_tsupport _)).trans hζU)
    exact (A.continuous.comp_continuousOn hDVc).clm_apply hDζ.continuousOn
  have hcont_g1 : Continuous g1 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g1 (isClosed_tsupport _)).trans hηU)
    exact (hη.continuous.pow 2).continuousOn.mul (hDVc.norm.pow 2)
  have hcont_g3 : Continuous g3 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g3 (isClosed_tsupport _)).trans hηU)
    exact ((hVc.sub continuousOn_const).norm.pow 2).mul (hDη.norm.pow 2).continuousOn
  have hint_h : Integrable h := hcont_h.integrable_of_hasCompactSupport (hζc.mono' hsupp_h)
  have hint_g1 : Integrable g1 := hcont_g1.integrable_of_hasCompactSupport (hηc.mono' hsupp_g1)
  have hint_g3 : Integrable g3 := hcont_g3.integrable_of_hasCompactSupport (hηc.mono' hsupp_g3)
  -- pointwise lower bound: Legendre condition, bound on `A`, and Young's inequality
  have hpt : ∀ x, lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x ≤ h x := by
    intro x
    have hid : h x = η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) +
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      simp only [hh, hζd x, map_add, map_smul, smul_eq_mul]
    rw [hid]
    have hc := hcoer (fderiv ℝ V x)
    have hb := hbdd (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c))
    rw [ContinuousLinearMap.norm_smulRight_apply] at hb
    have hb' := (abs_le.mp hb).1
    set a := η x * ‖fderiv ℝ V x‖ with ha
    set b := ‖V x - c‖ * ‖fderiv ℝ η x‖ with hb_def
    have e1 : lam * a ^ 2 ≤ η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) := by
      rw [ha, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (η x))]
    have e2 : -(2 * Lam * (a * b)) ≤
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      have h2η : 0 ≤ 2 * η x := by linarith [hη0 x]
      have := mul_le_mul_of_nonneg_left hb' h2η
      rw [ha, hb_def]
      linarith [this]
    have e3 : 2 * Lam * (a * b) ≤ lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 := by
      have key : lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 - 2 * Lam * (a * b) =
          (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by positivity
      linarith
    have hg1x : g1 x = a ^ 2 := by rw [hg1, ha, mul_pow]
    have hg3x : g3 x = b ^ 2 := by rw [hg3, hb_def, mul_pow]
    rw [hg1x, hg3x]
    linarith
  -- integrate (`∫ h = 0`) and absorb
  have hint_lhs : Integrable (fun x => lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x) :=
    (hint_g1.const_mul _).sub (hint_g3.const_mul _)
  have hmono := integral_mono hint_lhs hint_h hpt
  rw [h0, integral_sub (hint_g1.const_mul _) (hint_g3.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have key : ∫ x, g1 x ≤ 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by
    have h2 : lam / 2 * ∫ x, g1 x ≤ 2 * Lam ^ 2 / lam * ∫ x, g3 x := by linarith
    have hlam2 : 0 < lam / 2 := by positivity
    calc ∫ x, g1 x = (lam / 2)⁻¹ * (lam / 2 * ∫ x, g1 x) := by field_simp
      _ ≤ (lam / 2)⁻¹ * (2 * Lam ^ 2 / lam * ∫ x, g3 x) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam2.le)
      _ = 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by field_simp; ring
  -- pass to lower integrals
  have hg1n : 0 ≤ᵐ[volume] g1 := ae_of_all _ (fun x => by positivity)
  have hg3n : 0 ≤ᵐ[volume] g3 := ae_of_all _ (fun x => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_g1 hg1n,
    ← ofReal_integral_eq_lintegral_ofReal hint_g3 hg3n, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key
/-- Caccioppoli inequality for constant-coefficient Legendre systems: if `V` is `C¹` on
`B̆_{2ρ}(y)` and `∫ A[DV][Dζ] = 0` for every `ζ ∈ C¹_c(B̆_{2ρ}(y); ℝ^ℓ)`, then
`∫_{B̆_ρ(y)} |DV|² ≤ C ρ⁻² ∫_{B̆_{2ρ}(y)} |V − c|²` in `[0, ∞]`, with `C = C(λ, Λ)`.
Take the cutoff `η` of `dohr_eb_sch_cacc_exists_cutoff` (`‖Dη‖ ≤ K/ρ`), apply
`dohr_eb_sch_cacc_energy_estimate` with `U = B̆_{2ρ}(y)`, and put `C = (4Λ²/λ²) K²`. -/
theorem dohr_eb_sch_caccioppoli_const_coeff : ∀ (n ℓ : ℕ) (lam Lam : ℝ), 0 < lam → ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (y : Rn n) (ρ : ℝ) (c : Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → 0 < ρ → ContDiffOn ℝ 1 V (ball y (2 * ρ)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball y (2 * ρ) → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
  intro n ℓ lam Lam hlam
  obtain ⟨K, hK0, hcut⟩ := Submission.dohr_eb_sch_cacc_exists_cutoff
  refine ⟨4 * Lam ^ 2 / lam ^ 2 * K ^ 2, by positivity, ?_⟩
  intro A V y ρ c hleg hbd hρ hV hweak
  obtain ⟨η, hη, hη01, hη1, hηc, hηU, hDη⟩ := hcut n y ρ hρ
  have hen := Submission.dohr_eb_sch_cacc_energy_estimate n ℓ lam Lam A (ball y (2 * ρ)) V η c
    hlam hleg hbd isOpen_ball hV hη hηc hηU (fun x => (hη01 x).1) hweak
  -- `η = 1` on `B̆_ρ(y)`
  have hL : ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤
      ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := by
    calc ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2
        = ∫⁻ x in ball y ρ, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
          rw [hη1 x hx, one_pow, one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := setLIntegral_le_lintegral _ _
  -- `‖Dη‖ ≤ K/ρ`, and `Dη = 0` off `tsupport η ⊆ B̆_{2ρ}(y)`
  have hR : ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) ≤
      ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
    calc ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2)
        ≤ ∫⁻ x, (ball y (2 * ρ)).indicator
            (fun x => ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ‖V x - c‖ₑ ^ 2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ ball y (2 * ρ)
          · rw [indicator_of_mem hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
              ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            calc ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 ≤ ‖V x - c‖ ^ 2 * (K / ρ) ^ 2 := by
                  gcongr
                  exact hDη x
              _ = K ^ 2 / ρ ^ 2 * ‖V x - c‖ ^ 2 := by ring
          · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
            rw [fderiv_of_notMem_tsupport ℝ hx', norm_zero]
            simp
      _ = ∫⁻ x in ball y (2 * ρ), ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ‖V x - c‖ₑ ^ 2 :=
          lintegral_indicator measurableSet_ball _
      _ = ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) *
          ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := hL.trans hen
    _ ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) *
          (ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2 * K ^ 2 / ρ ^ 2) *
          ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_div_assoc']
/-- Interpolation bound for the derivative (step 3 of `dohr_eb_difference_quotient_limit`): if `h`
is differentiable on `B_{2r}(x)`, `Dh` is `α`-Hölder there with constant `L ≥ 0` and `‖h‖ ≤ S` on
`B_{2r}(x)`, then `‖Dh(y)‖ ≤ 2S/t + L t^α` for all `y ∈ B_r(x)` and `0 < t ≤ r`.
For `v ≠ 0` put `u = (t/‖v‖) v` and `z = y + u`; the mean value inequality on `[y, z] ⊆ B_{2r}(x)`
with the fixed map `Dh(y)` gives `‖h(z) − h(y) − Dh(y)u‖ ≤ L t^α · t`, so `‖Dh(y)u‖ ≤ 2S + L t^α t`,
and rescaling by `‖v‖/t` gives `‖Dh(y)v‖ ≤ (2S/t + L t^α)‖v‖`. -/
theorem dohr_eb_dql_interpolation_fderiv_bound : ∀ (n ℓ : ℕ) (h : Rn n → Rn ℓ) (x : Rn n) (r t α L S : ℝ), 0 < t → t ≤ r → 0 < α → 0 ≤ L → (∀ y ∈ closedBall x (2 * r), DifferentiableAt ℝ h y) → (∀ y ∈ closedBall x (2 * r), ∀ y' ∈ closedBall x (2 * r), ‖fderiv ℝ h y - fderiv ℝ h y'‖ ≤ L * ‖y - y'‖ ^ α) → (∀ y ∈ closedBall x (2 * r), ‖h y‖ ≤ S) → ∀ y ∈ closedBall x r, ‖fderiv ℝ h y‖ ≤ 2 * S / t + L * t ^ α := by
  intro n ℓ h x r t α L S ht htr hα hL hdiff hhol hS y hy
  -- Step 1: `S ≥ 0`, the bound is nonnegative, and it suffices to bound `‖Dh(y)v‖` for `v ≠ 0`.
  have hr : 0 < r := ht.trans_le htr
  have hxB : x ∈ closedBall x (2 * r) := mem_closedBall_self (by linarith)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
  have hbound0 : 0 ≤ 2 * S / t + L * t ^ α := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hbound0 (fun v => ?_)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  -- Step 2: the test point `z = y + u`, `u = (t/‖v‖) v`, and the segment `[y, z]`.
  set c : ℝ := t / ‖v‖ with hc
  have hcpos : 0 < c := div_pos ht hvpos
  set u : Rn n := c • v with hu
  have hunorm : ‖u‖ = t := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc, div_mul_cancel₀ _ hvpos.ne']
  set z := y + u with hz
  have hzy : z - y = u := by rw [hz]; abel
  have hzB : z ∈ closedBall x (2 * r) := by
    rw [mem_closedBall] at hy ⊢
    calc dist z x = ‖(y - x) + u‖ := by rw [dist_eq_norm]; congr 1; rw [hz]; abel
      _ ≤ ‖y - x‖ + ‖u‖ := norm_add_le _ _
      _ ≤ r + t := by rw [← dist_eq_norm, hunorm]; linarith
      _ ≤ 2 * r := by linarith
  have hseg : segment ℝ y z ⊆ closedBall x (2 * r) :=
    (convex_closedBall x (2 * r)).segment_subset hyB hzB
  have hseg' : segment ℝ y z ⊆ closedBall y t := by
    refine (convex_closedBall y t).segment_subset (mem_closedBall_self ht.le) ?_
    rw [mem_closedBall, dist_eq_norm, hzy, hunorm]
  -- Steps 3–4: `‖Dh(w) − Dh(y)‖ ≤ L t^α` on `[y, z]`, and the mean value inequality.
  have hmvt : ‖h z - h y - fderiv ℝ h y (z - y)‖ ≤ (L * t ^ α) * ‖z - y‖ := by
    refine (convex_segment y z).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hseg hw)) (fun w hw => ?_) (left_mem_segment ℝ y z)
      (right_mem_segment ℝ y z)
    have hwy : ‖w - y‖ ≤ t := by
      have := hseg' hw
      rwa [mem_closedBall, dist_eq_norm] at this
    calc ‖fderiv ℝ h w - fderiv ℝ h y‖ ≤ L * ‖w - y‖ ^ α := hhol w (hseg hw) y hyB
      _ ≤ L * t ^ α := by
        gcongr
  rw [hzy, hunorm] at hmvt
  -- Step 5: `‖Dh(y)u‖ ≤ 2S + L t^α t`.
  have hhzy : ‖h z - h y‖ ≤ 2 * S := by
    calc ‖h z - h y‖ ≤ ‖h z‖ + ‖h y‖ := norm_sub_le _ _
      _ ≤ S + S := add_le_add (hS z hzB) (hS y hyB)
      _ = 2 * S := by ring
  have hfu : ‖fderiv ℝ h y u‖ ≤ L * t ^ α * t + 2 * S := by
    have : fderiv ℝ h y u = (h z - h y) - (h z - h y - fderiv ℝ h y u) := by abel
    rw [this]
    calc ‖(h z - h y) - (h z - h y - fderiv ℝ h y u)‖
        ≤ ‖h z - h y‖ + ‖h z - h y - fderiv ℝ h y u‖ := norm_sub_le _ _
      _ ≤ 2 * S + L * t ^ α * t := add_le_add hhzy hmvt
      _ = L * t ^ α * t + 2 * S := by ring
  -- Step 6: rescale by `c = t/‖v‖`.
  have hfu' : ‖fderiv ℝ h y u‖ = c * ‖fderiv ℝ h y v‖ := by
    rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  rw [hfu'] at hfu
  have key : ‖fderiv ℝ h y v‖ ≤ (L * t ^ α * t + 2 * S) / c := by
    rw [le_div_iff₀ hcpos]; linarith
  calc ‖fderiv ℝ h y v‖ ≤ (L * t ^ α * t + 2 * S) / c := key
    _ = (2 * S / t + L * t ^ α) * ‖v‖ := by
      rw [hc]; field_simp; ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `C^{1,α}` bounds pass to limits.**
Let `B = B̆_ρ(x₀)` and let `F_i → G` uniformly on every compact `K ⊆ B` along a filter `l ≠ ⊥`.
If eventually in `l` each `F_i` is differentiable on `B` with `‖DF_i‖ ≤ M` and
`‖DF_i(x) − DF_i(y)‖ ≤ M ‖x − y‖^α` on `B` (`α > 0`), then `G` is `C¹` on `B` with the same bounds.
Proof: for `x ∈ B` choose `r > 0` with `B_{2r}(x) ⊆ B`.  Given `η > 0`, pick `t ∈ (0, r]` with
`2M t^α < η/2`; once `‖G − F_i‖ < ηt/8` on `B_{2r}(x)`, the interpolation inequality
(`dohr_eb_dql_interpolation_fderiv_bound`) applied to `F_i − F_j` (Hölder constant `2M`, sup bound
`ηt/4`) gives `‖DF_i − DF_j‖ ≤ η/2 + 2M t^α < η` on `B_r(x)`.  So `DF_i` is uniformly Cauchy on
`B_r(x)` and, `L(ℝⁿ, ℝ^ℓ)` being complete, converges uniformly there to `V := lim DF_i`.  The limit
`V` inherits the bound `M` and the Hölder constant `M`, hence is continuous on `B`, and the theorem
on uniform limits of derivatives gives `DG = V` on `B`; thus `G` is `C¹` on `B`. -/
theorem dohr_eb_dql_c1Holder_of_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ ι l hl F G x₀ ρ α M hα hD hB hH hU
  have := hl
  -- The good indices: eventually all three hypotheses hold at once.
  have hE := hD.and (hB.and hH)
  -- The candidate derivative of `G`: the (chosen) pointwise limit of the `DF_i`.
  set V : Rn n → (Rn n →L[ℝ] Rn ℓ) := fun y => limUnder l (fun i => fderiv ℝ (F i) y)
  -- Step 1: radii with `B_{2r}(x) ⊆ B`, and `M ≥ 0`.
  have hrad : ∀ x ∈ ball x₀ ρ, ∃ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ := by
    intro x hx
    rw [mem_ball] at hx
    refine ⟨(ρ - dist x x₀) / 4, by linarith, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  have hM : ∀ x ∈ ball x₀ ρ, 0 ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := hB.exists
    exact (norm_nonneg _).trans (hi x hx)
  -- Steps 2–3: on `B_r(x)` the `DF_i` are uniformly Cauchy, hence converge uniformly to `V`.
  have hconv : ∀ x ∈ ball x₀ ρ, ∀ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ →
      TendstoUniformlyOn (fun i => fderiv ℝ (F i)) V l (closedBall x r) := by
    intro x hx r hr hsub
    have hM0 := hM x hx
    have hUC : UniformCauchySeqOn (fun i => fderiv ℝ (F i)) l (closedBall x r) := by
      intro u hu
      obtain ⟨η, hη, hηu⟩ := Metric.mem_uniformity_dist.1 hu
      -- (a) a scale `t ∈ (0, r]` with `2M t^α < η/2`.
      have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * M * t ^ α < η / 2 := by
        have hc : Tendsto (fun t : ℝ => 2 * M * t ^ α) (𝓝 0) (𝓝 (2 * M * (0 : ℝ) ^ α)) :=
          ((continuousAt_id.rpow_const (Or.inr hα.le)).tendsto).const_mul _
        rw [Real.zero_rpow hα.ne', mul_zero] at hc
        exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith)))
      have hIoc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 r := Ioc_mem_nhdsGT hr
      obtain ⟨t, ht1, ht2⟩ := (ht_ev.and hIoc).exists
      have htpos : 0 < t := ht2.1
      have htr : t ≤ r := ht2.2
      -- (b) eventually `‖G − F_i‖ < ηt/8` on the compact set `B_{2r}(x) ⊆ B`.
      have hTU := hU (closedBall x (2 * r)) (isCompact_closedBall x _) hsub
      rw [Metric.tendstoUniformlyOn_iff] at hTU
      have hP := hE.and (hTU (η * t / 8) (by positivity))
      filter_upwards [hP.prod_mk hP] with ij hij y hy
      obtain ⟨⟨hDi, hBi, hHi⟩, hGi⟩ := hij.1
      obtain ⟨⟨hDj, hBj, hHj⟩, hGj⟩ := hij.2
      apply hηu
      rw [dist_eq_norm]
      have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
      -- (c) `h = F_i − F_j` has Hölder constant `2M` and sup bound `ηt/4` on `B_{2r}(x)`.
      set h : Rn n → Rn ℓ := fun z => F ij.1 z - F ij.2 z
      have hdh : ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℝ h z := fun z hz =>
        (hDi z (hsub hz)).sub (hDj z (hsub hz))
      have hfd : ∀ z ∈ closedBall x (2 * r),
          fderiv ℝ h z = fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z := fun z hz =>
        fderiv_sub (hDi z (hsub hz)) (hDj z (hsub hz))
      -- (d) the interpolation inequality on `B_r(x)`.
      have hbd := Submission.dohr_eb_dql_interpolation_fderiv_bound n ℓ h x r t α (2 * M)
        (η * t / 4) htpos htr hα (by linarith) hdh
        (fun z hz z' hz' => by
          rw [hfd z hz, hfd z' hz']
          calc ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z -
                (fderiv ℝ (F ij.1) z' - fderiv ℝ (F ij.2) z')‖
              = ‖(fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z') -
                  (fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z')‖ := by congr 1; abel
            _ ≤ ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z'‖ +
                  ‖fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z'‖ := norm_sub_le _ _
            _ ≤ M * ‖z - z'‖ ^ α + M * ‖z - z'‖ ^ α :=
                add_le_add (hHi z (hsub hz) z' (hsub hz')) (hHj z (hsub hz) z' (hsub hz'))
            _ = 2 * M * ‖z - z'‖ ^ α := by ring)
        (fun z hz => by
          have h1 := hGi z hz
          have h2 := hGj z hz
          rw [dist_eq_norm] at h1 h2
          calc ‖h z‖ = ‖(G z - F ij.2 z) - (G z - F ij.1 z)‖ := by
                show ‖F ij.1 z - F ij.2 z‖ = _; congr 1; abel
            _ ≤ ‖G z - F ij.2 z‖ + ‖G z - F ij.1 z‖ := norm_sub_le _ _
            _ ≤ η * t / 4 := by linarith)
        y hy
      rw [hfd y hyB] at hbd
      calc ‖fderiv ℝ (F ij.1) y - fderiv ℝ (F ij.2) y‖
          ≤ 2 * (η * t / 4) / t + 2 * M * t ^ α := hbd
        _ = η / 2 + 2 * M * t ^ α := by field_simp; ring
        _ < η := by linarith
    -- (e)/(3) completeness: pointwise limits exist, and the convergence is uniform.
    refine hUC.tendstoUniformlyOn_of_tendsto (fun y hy => ?_)
    obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 (hUC.cauchy_map hy)
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  have hpt : ∀ y ∈ ball x₀ ρ, Tendsto (fun i => fderiv ℝ (F i) y) l (𝓝 (V y)) := by
    intro y hy
    obtain ⟨r, hr, hsub⟩ := hrad y hy
    exact (hconv y hy r hr hsub).tendsto_at (mem_closedBall_self hr.le)
  -- Step 5: the uniform-limit theorem for derivatives gives `DG = V` on `B`.
  have hG : ∀ x ∈ ball x₀ ρ, HasFDerivAt G (V x) x := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hrad x hx
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F)
      (f' := fun i => fderiv ℝ (F i)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.1 (hconv x hx r hr hsub)).mono_right
        (le_principal_iff.2 (closedBall_mem_nhds x hr))
    · filter_upwards [hD.prod_mk (isOpen_ball.mem_nhds hx)] with p hp
      exact (hp.1 p.2 hp.2).hasFDerivAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hU {y} isCompact_singleton (singleton_subset_iff.2 hy)).tendsto_at rfl
  have hfG : ∀ x ∈ ball x₀ ρ, fderiv ℝ G x = V x := fun x hx => (hG x hx).fderiv
  -- Step 4: `V` inherits both bounds, so it is continuous on `B`.
  have hVb : ∀ x ∈ ball x₀ ρ, ‖V x‖ ≤ M := fun x hx =>
    le_of_tendsto (hpt x hx).norm (hB.mono fun i hi => hi x hx)
  have hVh : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖V x - V y‖ ≤ M * ‖x - y‖ ^ α := fun x hx y hy =>
    le_of_tendsto ((hpt x hx).sub (hpt y hy)).norm (hH.mono fun i hi => hi x hx y hy)
  have hVc : ContinuousOn V (ball x₀ ρ) := by
    intro y hy
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun z => M * ‖z - y‖ ^ α) (𝓝 y) (𝓝 (M * ‖y - y‖ ^ α)) :=
      (((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
        (Or.inr hα.le)).tendsto.const_mul M
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hVh z hz y hy
  -- Step 6: conclusion.
  refine ⟨?_, fun x hx => by rw [hfG x hx]; exact hVb x hx, fun x hx y hy => by
    rw [hfG x hx, hfG y hy]; exact hVh x hx y hy⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun x hx => (hG x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hVc.congr hfG
/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (pp. 127–128), Schauder step by difference
quotients (Giaquinta–Martinazzi, §4.3, with uniform `C^{1,α}` bounds in place of `W^{1,2}` bounds):
let `f` be `C¹` on `B' = B̆_{ρ+δ|e|}(x₀)` and let the difference quotients
`g_d = d⁻¹ (f(· + d e) - f)`, `0 < |d| < δ`, satisfy `‖Dg_d‖ ≤ M` and `[Dg_d]_α ≤ M` on
`B = B̆_ρ(x₀)`.  Then `D_e f = Df(·) e` is `C¹` on `B`, `‖D(D_e f)‖ ≤ M` and `[D(D_e f)]_α ≤ M`.
For `|d| < δ` the shift `x + d e` of `x ∈ B` stays in `B'`, so `Dg_d = d⁻¹ (Df(· + d e) - Df)` on
`B` by the chain rule.  As `d → 0`, `g_d → D_e f` uniformly on compact subsets of `B`
(`dohr_eb_dql_diffQuot_tendstoUniformlyOn`), and uniform `C^{1,α}` bounds pass to such limits
(`dohr_eb_dql_c1Holder_of_tendstoUniformlyOn`). -/
theorem dohr_eb_difference_quotient_limit : ∀ (n ℓ : ℕ) (α : ℝ) (f : Rn n → Rn ℓ) (x₀ e : Rn n) (ρ δ M : ℝ), 0 < α → α ≤ 1 → 0 < δ → ContDiffOn ℝ 1 f (ball x₀ (ρ + δ * ‖e‖)) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x)‖ ≤ M) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x) - d⁻¹ • (fderiv ℝ f (y + d • e) - fderiv ℝ f y)‖ ≤ M * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 (fun x => fderiv ℝ f x e) (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x - fderiv ℝ (fun z => fderiv ℝ f z e) y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ α f x₀ e ρ δ M hα _hα1 hδ hf hbd hhol
  -- `B = B̆_ρ(x₀) ⊆ B' = B̆_{ρ+δ|e|}(x₀)`, and `f` is differentiable on the open set `B'`.
  have hB'open : IsOpen (ball x₀ (ρ + δ * ‖e‖)) := isOpen_ball
  have hBB' : ball x₀ ρ ⊆ ball x₀ (ρ + δ * ‖e‖) :=
    ball_subset_ball (le_add_of_nonneg_right (mul_nonneg hδ.le (norm_nonneg e)))
  have hdiff : ∀ z ∈ ball x₀ (ρ + δ * ‖e‖), DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hB'open.mem_nhds hz)
  -- For `|d| < δ` and `x ∈ B`: `|x + d e - x₀| ≤ |x - x₀| + |d| |e| < ρ + δ |e|`.
  have hshift : ∀ d : ℝ, |d| < δ → ∀ x ∈ ball x₀ ρ, x + d • e ∈ ball x₀ (ρ + δ * ‖e‖) := by
    intro d hd x hx
    rw [mem_ball] at hx ⊢
    have h1 : dist (x + d • e) x₀ ≤ dist x x₀ + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖x + d • e - x₀‖ = ‖(x - x₀) + d • e‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ δ * ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg e)
    linarith
  -- Step 1 (chain rule): `Dg_d(x) = d⁻¹ (Df(x + d e) - Df(x))` for `|d| < δ` and `x ∈ B`.
  have hFderiv : ∀ d : ℝ, |d| < δ → ∀ x ∈ ball x₀ ρ,
      HasFDerivAt (fun y => d⁻¹ • (f (y + d • e) - f y))
        (d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x)) x := by
    intro d hd x hx
    have h1 : HasFDerivAt (fun y => f (y + d • e)) (fderiv ℝ f (x + d • e)) x :=
      (hasFDerivAt_comp_add_right (d • e)).2 (hdiff _ (hshift d hd x hx)).hasFDerivAt
    have h2 : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x (hBB' hx)).hasFDerivAt
    exact (h1.sub h2).const_smul d⁻¹
  -- The admissible `d` (`d ≠ 0`, `|d| < δ`) form a set of the punctured filter `𝓝[≠] 0`.
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), d ≠ 0 ∧ |d| < δ := by
    have h1 : ∀ᶠ d in 𝓝[≠] (0 : ℝ), d ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < δ := by
      have : ∀ᶠ d in 𝓝 (0 : ℝ), |d| < δ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with d hd
        simpa [Real.dist_eq] using hd
      exact nhdsWithin_le_nhds this
    exact h1.and h2
  -- Steps 2–7: `g_d → D_e f` uniformly on compact `K ⊆ B ⊆ B'` along `𝓝[≠] 0`, and the uniform
  -- bounds `‖Dg_d‖ ≤ M`, `[Dg_d]_α ≤ M` pass to the limit.
  exact Submission.dohr_eb_dql_c1Holder_of_tendstoUniformlyOn n ℓ ℝ (𝓝[≠] (0 : ℝ)) inferInstance
    (fun d y => d⁻¹ • (f (y + d • e) - f y)) (fun x => fderiv ℝ f x e) x₀ ρ α M hα
    (hev.mono fun d hd x hx => (hFderiv d hd.2 x hx).differentiableAt)
    (hev.mono fun d hd x hx => by
      rw [(hFderiv d hd.2 x hx).fderiv]; exact hbd d hd.1 hd.2 x hx)
    (hev.mono fun d hd x hx y hy => by
      rw [(hFderiv d hd.2 x hx).fderiv, (hFderiv d hd.2 y hy).fderiv]
      exact hhol d hd.1 hd.2 x hx y hy)
    (fun K hK hKB => Submission.dohr_eb_dql_diffQuot_tendstoUniformlyOn n ℓ f _ K e hB'open hf
      hK (hKB.trans hBB'))

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

end Submission

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

namespace Submission

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

/-- **Liouville theorem for constant-coefficient Legendre-elliptic systems** (Schauder estimate in
the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion, p. 127).  Let `A` be a
bilinear form on `L = L(ℝⁿ, ℝ^ℓ)` with `A[P][P] ≥ λ‖P‖²` and `|A[P][Q]| ≤ Λ‖P‖‖Q‖`, and let
`W ∈ C¹(ℝⁿ; ℝ^ℓ)` with `‖DW(x) − DW(y)‖ ≤ K‖x − y‖^α` (`0 < α < 1`) solve `∫ A[DW][Dζ] = 0` for
every `ζ ∈ C¹_c(ℝⁿ; ℝ^ℓ)`.  Then `DW` is constant.
Proof: let `C ≥ 0` be the Caccioppoli constant for `(λ, Λ)` and `K₊ = max K 0`.  The smooth global
solutions form a class `S` of `C¹` maps that is closed under directional derivatives and satisfies
the Caccioppoli inequality at `0`.  For `ε > 0` the mollification `W_ε` lies in `S`, has Hölder
constant `K₊` and satisfies `‖DW_ε − DW‖ ≤ K₊ ε^α`; the abstract Liouville theorem makes `DW_ε`
constant, so `‖DW(x) − DW(y)‖ ≤ 2 K₊ ε^α`, which tends to `0` as `ε → 0⁺`. -/
theorem dohr_eb_sch_liouville_const_coeff : ∀ (n ℓ : ℕ) (α lam Lam K : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → ContDiff ℝ 1 W → (∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ x) = 0) → ∀ x y : Rn n, fderiv ℝ W x = fderiv ℝ W y := by
  intro n ℓ α lam Lam K A W hα hα1 hlam hcoer hbdd hW hhol hsol x y
  -- Step 0: the Caccioppoli constant `C ≥ 0` for `(λ, Λ)`; `K₊ = max K 0` is a Hölder constant.
  obtain ⟨C, hC0, hcacc⟩ := Submission.dohr_eb_sch_caccioppoli_const_coeff n ℓ lam Lam hlam
  obtain ⟨Kp, hKp, hKKp⟩ : ∃ Kp : ℝ, 0 ≤ Kp ∧ K ≤ Kp := ⟨max K 0, le_max_right K 0, le_max_left K 0⟩
  have hholp : ∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ Kp * ‖x - y‖ ^ α := fun x y =>
    (hhol x y).trans (mul_le_mul_of_nonneg_right hKKp (Real.rpow_nonneg (norm_nonneg _) α))
  -- Step 1: the class `S` of smooth global solutions.
  let S : Set (Rn n → Rn ℓ) := {V | ContDiff ℝ (⊤ : ℕ∞) V ∧
    ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0}
  -- (S1): smooth maps are `C¹`.
  have hS1 : ∀ V ∈ S, ContDiff ℝ 1 V := fun V hV => contDiff_infty.1 hV.1 1
  -- (S2): `x ↦ DV(x) v` is smooth, and a global solution by `dir_deriv_solution` (`V ∈ C²`).
  have hS2 : ∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S := by
    intro V hV v
    refine ⟨?_, Submission.dohr_eb_sch_liou_dir_deriv_solution n ℓ A V v
      (contDiff_infty.1 hV.1 2) hV.2⟩
    exact (hV.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  -- (S3): the Caccioppoli inequality centred at `0`, tested with all of `C¹_c(B_{2ρ}(0))`.
  have hS3 : ∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ,
      ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤
        ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2 :=
    fun V hV ρ hρ c => hcacc A V 0 ρ c hcoer hbdd hρ (hS1 V hV).contDiffOn
      fun ζ hζ hζc _ => hV.2 ζ hζ hζc
  -- Steps 2–5: the mollification `W_ε ∈ S` has constant derivative, so
  -- `‖DW(x) − DW(y)‖ ≤ ‖DW_ε(x) − DW(x)‖ + ‖DW_ε(y) − DW(y)‖ ≤ 2 K₊ ε^α`.
  have hε : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ 2 * (Kp * ε ^ α) := by
    intro ε hε
    obtain ⟨V, hVsm, hVhol, hVW, hVsol⟩ :=
      Submission.dohr_eb_sch_liou_mollify n ℓ α Kp ε A W hα hKp hε hW hholp hsol
    have hconst := Submission.dohr_eb_sch_liou_abstract n ℓ α Kp C S V hα hα1 hKp hC0 hS1 hS2
      hS3 ⟨hVsm, hVsol⟩ fun z => by simpa only [sub_zero] using hVhol z 0
    have hxy : fderiv ℝ V x = fderiv ℝ V y := (hconst x).trans (hconst y).symm
    calc ‖fderiv ℝ W x - fderiv ℝ W y‖ = dist (fderiv ℝ W x) (fderiv ℝ W y) :=
          (dist_eq_norm _ _).symm
      _ ≤ dist (fderiv ℝ W x) (fderiv ℝ V x) + dist (fderiv ℝ V x) (fderiv ℝ V y) +
          dist (fderiv ℝ V y) (fderiv ℝ W y) := dist_triangle4 _ _ _ _
      _ = ‖fderiv ℝ V x - fderiv ℝ W x‖ + ‖fderiv ℝ V y - fderiv ℝ W y‖ := by
          rw [hxy, dist_self, add_zero, dist_comm (fderiv ℝ W x), dist_eq_norm, dist_eq_norm]
      _ ≤ Kp * ε ^ α + Kp * ε ^ α := add_le_add (hVW x) (hVW y)
      _ = 2 * (Kp * ε ^ α) := (two_mul _).symm
  -- Step 6: let `ε → 0⁺`; `ε^α → 0^α = 0` as `α > 0`.
  have hlim : Tendsto (fun ε : ℝ => 2 * (Kp * ε ^ α)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hα.ne'] using
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa only [mul_zero] using ((h0.const_mul Kp).const_mul 2).mono_left nhdsWithin_le_nhds
  exact sub_eq_zero.mp (norm_le_zero_iff.mp
    (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hε)))

/-- **Blow-up Hölder estimate on the unit ball** (L. Simon's scaling argument; step 5 of the
Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).
For `0 < α < 1`, `λ > 0`, `M` and `δ > 0` there is `C_δ ≥ 0` such that every `C¹` weak solution `w`
on `B₁ = B̆₁(0)` of `∫ a(x)[Dw][Dζ] = ∫ Φ(x)[Dζ]`, with `a` Legendre-elliptic (`λ`), bounded and
`α`-Hölder (`M`), `Φ` `α`-Hölder (`G ≥ 0`), `|w| ≤ S` and `[Dw]_{α;B₁} ≤ K`, satisfies
`‖Dw(x) − Dw(y)‖ ≤ (δK + C_δ(S + G))|x − y|^α` on `B̆_{1/2}(0)`.
Proof by contradiction: violating data for `C_δ = k` are normalized by the difference quotient
`σ_k = ‖Dw_k(x_k) − Dw_k(y_k)‖/ρ_k^α`, `ρ_k = |x_k − y_k|`; the interpolation bound gives
`‖Dw_k‖ = o(σ_k)` on `B̆_{1/2}(0)`, hence `ρ_k → 0`. The blow-ups
`W_k(z) = (σ_k ρ_k^{1+α})⁻¹ (w_k(x_k + ρ_k z) − w_k(x_k) − ρ_k Dw_k(x_k) z)` solve rescaled systems
(rescale, zero mean, affine subtraction) with `DW_k(0) = 0`, `[DW_k]_α ≤ δ⁻¹`,
`‖DW_k((y_k − x_k)/ρ_k)‖ = 1` and errors tending to `0`.  The blow-up limit is a global solution of a
constant-coefficient Legendre system with `DW(0) = 0`, `‖DW(e₀)‖ = 1` and `[DW]_α ≤ δ⁻¹`, whose
gradient is constant by the Liouville theorem: a contradiction. -/
theorem dohr_eb_sch_blowup_holder_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M δ : ℝ, 0 < lam → 0 < δ → ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (K S G : ℝ), 0 ≤ G → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ G * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ S) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ (δ * K + Cδ * (S + G)) * ‖x - y‖ ^ α := by
  -- Norms, subtraction and continuity on `L(ℝⁿ, ℝ^ℓ)` and its dual need a deeper instance search.
  set_option maxSynthPendingDepth 3 in
  intro n ℓ _hn α hα hα1 lam M δ hlam hδ
  -- Step (0b): `α`-Hölder dependence on the base point gives continuity of linear forms in
  -- operator norm, and joint continuity of `(z, P, Q) ↦ b(z)[P][Q]`.
  have hcontL : ∀ (f : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, |f z P - f z' P| ≤ C * ‖z - z'‖ ^ α * ‖P‖) →
      ContinuousOn f U := by
    intro f U C hf z₀ hz₀
    have hb : ∀ z ∈ U, ‖f z - f z₀‖ ≤ |C| * ‖z - z₀‖ ^ α := by
      intro z hz
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (norm_nonneg _) α)) fun P => ?_
      rw [sub_apply, Real.norm_eq_abs]
      calc |f z P - f z₀ P| ≤ C * ‖z - z₀‖ ^ α * ‖P‖ := hf z hz z₀ hz₀ P
        _ ≤ |C| * ‖z - z₀‖ ^ α * ‖P‖ := by gcongr; exact le_abs_self C
    have hg : Continuous fun z : Rn n => |C| * ‖z - z₀‖ ^ α :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)
    have hg0 : Tendsto (fun z : Rn n => |C| * ‖z - z₀‖ ^ α) (𝓝[U] z₀)
        (𝓝 (|C| * ‖z₀ - z₀‖ ^ α)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hg0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_nhdsWithin_of_forall hb) hg0)
  have hcontJ : ∀ (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P Q : Rn n →L[ℝ] Rn ℓ,
        |b z P Q - b z' P Q| ≤ C * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) →
      ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2) (U ×ˢ univ) := by
    intro b U C hb p₀ hp₀
    have hfr : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p₀.1 p.2.1 p.2.2 :=
      ((b p₀.1).continuous.comp continuous_snd.fst).clm_apply continuous_snd.snd
    have hg : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ :=
      ((continuous_const.mul ((continuous_fst.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)).mul continuous_snd.fst.norm).mul continuous_snd.snd.norm
    have hg0 : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖) (𝓝[U ×ˢ univ] p₀)
        (𝓝 (|C| * ‖p₀.1 - p₀.1‖ ^ α * ‖p₀.2.1‖ * ‖p₀.2.2‖)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, zero_mul, zero_mul] at hg0
    have hdiff : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2) (𝓝[U ×ˢ univ] p₀) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg0
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Real.norm_eq_abs]
      calc |b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2|
          ≤ C * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := hb _ hp.1 _ hp₀.1 _ _
        _ ≤ |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := by gcongr; exact le_abs_self C
    have hsum := hdiff.add hfr.continuousWithinAt
    simp only [sub_add_cancel, zero_add] at hsum
    exact hsum
  -- Step 1: contradiction hypothesis; for each `k` take violating data with `C_δ = k`.
  by_contra hcon
  push Not at hcon
  choose a Φ w K S G hG hell hbd haH hΦH hwS hwC hwH hweak x hx y hy hviol using
    fun k : ℕ => hcon (k : ℝ) (Nat.cast_nonneg k)
  have h0B : (0 : Rn n) ∈ ball (0 : Rn n) 1 := mem_ball_self one_pos
  have hx1 : ∀ k, x k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hx k)
  have hy1 : ∀ k, y k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hy k)
  have hxn : ∀ k, ‖x k‖ < 1 / 2 := fun k => mem_ball_zero_iff.mp (hx k)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ k, ρ k = ‖x k - y k‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℝ, ∀ k,
      N k = ‖fderiv ℝ (w k) (x k) - fderiv ℝ (w k) (y k)‖ := ⟨_, fun _ => rfl⟩
  have hviol' : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α < N k := fun k => by
    rw [hρ, hN]; exact hviol k
  -- `x_k ≠ y_k`, so `ρ_k > 0`; `K_k, S_k ≥ 0` and `N_k > 0`.
  have hρpos : ∀ k, 0 < ρ k := by
    intro k
    rw [hρ]
    refine norm_pos_iff.mpr fun hxy => ?_
    have h := hviol k
    rw [sub_eq_zero.mp hxy, sub_self, sub_self, norm_zero, norm_zero,
      Real.zero_rpow hα.ne', mul_zero] at h
    exact lt_irrefl 0 h
  have hραpos : ∀ k, 0 < ρ k ^ α := fun k => Real.rpow_pos_of_pos (hρpos k) α
  have hK0 : ∀ k, 0 ≤ K k := by
    intro k
    have h := hwH k (x k) (hx1 k) (y k) (hy1 k)
    rw [← hρ, ← hN] at h
    by_contra hneg
    push Not at hneg
    have h1 : K k * ρ k ^ α < 0 := mul_neg_of_neg_of_pos hneg (hραpos k)
    have h2 : 0 ≤ N k := by rw [hN]; exact norm_nonneg _
    linarith
  have hS0 : ∀ k, 0 ≤ S k := fun k => (norm_nonneg _).trans (hwS k 0 h0B)
  have hsplit : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α =
      δ * K k * ρ k ^ α + (k * S k * ρ k ^ α + k * G k * ρ k ^ α) := fun k => by ring
  have hKρ : ∀ k, 0 ≤ δ * K k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg hδ.le (hK0 k)) (hραpos k).le
  have hSρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * S k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hS0 k)) (hραpos k).le
  have hGρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * G k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hG k)) (hραpos k).le
  have hNpos : ∀ k, 0 < N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k, hGρ k]
  have hKN : ∀ k, δ * K k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hSρ k, hGρ k]
  have hSN : ∀ k : ℕ, (k : ℝ) * S k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hGρ k]
  have hGN : ∀ k : ℕ, (k : ℝ) * G k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k]
  -- Step 3: small gradients.  The interpolation bound with `t = k^{-1/2}` on `B̆_{1/2}(z)` gives
  -- `‖Dw_k(z)‖ ρ_k^α ≤ ε_k N_k` on `B̆_{1/2}(0)`, `ε_k = 2k^{-1/2} + k^{-α/2}/δ → 0`.
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ∀ k : ℕ,
      ε k = 2 / Real.sqrt k + (Real.sqrt k)⁻¹ ^ α / δ := ⟨_, fun _ => rfl⟩
  have hinterp : ∀ k : ℕ, 5 ≤ k → ∀ z ∈ ball (0 : Rn n) (1 / 2),
      ‖fderiv ℝ (w k) z‖ * ρ k ^ α ≤ ε k * N k := by
    intro k hk z hz
    have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
    have hsq2 : 2 < Real.sqrt k := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hsq : 0 < Real.sqrt k := by linarith
    have ht : 0 < (Real.sqrt k)⁻¹ := inv_pos.mpr hsq
    have ht2 : (Real.sqrt k)⁻¹ < 1 / 2 := by
      rw [one_div]; exact inv_strictAnti₀ (by norm_num) hsq2
    have hsub : ball z (1 / 2) ⊆ ball (0 : Rn n) 1 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith [mem_ball_zero_iff.mp hz])
    have hI := Submission.dohr_eb_sch_fderiv_norm_interpolation n ℓ (w k) z (1 / 2)
      (Real.sqrt k)⁻¹ α (S k) (K k) hα.le (hK0 k) ht ht2 ((hwC k).mono hsub)
      (fun y' hy' => hwS k y' (hsub hy'))
      (fun y' hy' z' hz' => hwH k y' (hsub hy') z' (hsub hz'))
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
    have e1 : 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α ≤ 2 / Real.sqrt k * N k := by
      rw [div_inv_eq_mul, div_mul_eq_mul_div, le_div_iff₀ hsq]
      calc 2 * S k * Real.sqrt k * ρ k ^ α * Real.sqrt k
          = 2 * ((Real.sqrt k * Real.sqrt k) * S k * ρ k ^ α) := by ring
        _ = 2 * ((k : ℝ) * S k * ρ k ^ α) := by rw [hkk]
        _ ≤ 2 * N k := by linarith [hSN k]
    have e2 : (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α ≤ (Real.sqrt k)⁻¹ ^ α / δ * N k := by
      have htα : 0 ≤ (Real.sqrt k)⁻¹ ^ α := Real.rpow_nonneg ht.le α
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      calc (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α * δ
          = (Real.sqrt k)⁻¹ ^ α * (δ * K k * ρ k ^ α) := by ring
        _ ≤ (Real.sqrt k)⁻¹ ^ α * N k := mul_le_mul_of_nonneg_left (hKN k) htα
    calc ‖fderiv ℝ (w k) z‖ * ρ k ^ α
        ≤ (2 * S k / (Real.sqrt k)⁻¹ + (Real.sqrt k)⁻¹ ^ α * K k) * ρ k ^ α :=
          mul_le_mul_of_nonneg_right hI (hραpos k).le
      _ = 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α + (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α := by ring
      _ ≤ 2 / Real.sqrt k * N k + (Real.sqrt k)⁻¹ ^ α / δ * N k := add_le_add e1 e2
      _ = ε k * N k := by rw [hε]; ring
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun k : ℕ => 2 / Real.sqrt k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul 2
    have h2 : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹ ^ α / δ) atTop (𝓝 0) := by
      have h3 := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hinv).div_const δ
      rw [Real.zero_rpow hα.ne', zero_div] at h3
      exact h3
    have h4 := h1.add h2
    rw [add_zero] at h4
    exact h4.congr fun k => (hε k).symm
  -- Step 4: the scale tends to `0`: `ρ_k^α = N_k/σ_k ≤ 2ε_k`.
  have hρα_le : ∀ k, 5 ≤ k → ρ k ^ α ≤ 2 * ε k := by
    intro k hk
    have h1 := hinterp k hk (x k) (hx k)
    have h2 := hinterp k hk (y k) (hy k)
    have h3 : N k ≤ ‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖ := by
      rw [hN]; exact norm_sub_le _ _
    have h4 : N k * ρ k ^ α ≤ N k * (2 * ε k) := by
      calc N k * ρ k ^ α
          ≤ (‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖) * ρ k ^ α :=
            mul_le_mul_of_nonneg_right h3 (hραpos k).le
        _ = ‖fderiv ℝ (w k) (x k)‖ * ρ k ^ α + ‖fderiv ℝ (w k) (y k)‖ * ρ k ^ α := by ring
        _ ≤ ε k * N k + ε k * N k := add_le_add h1 h2
        _ = N k * (2 * ε k) := by ring
    exact le_of_mul_le_mul_left h4 (hNpos k)
  have hραt : Tendsto (fun k => ρ k ^ α) atTop (𝓝 0) := by
    have h2ε : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hεt.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun k => (hραpos k).le) ?_ h2ε
    filter_upwards [eventually_ge_atTop 5] with k hk using hρα_le k hk
  have hρt : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (Real.continuousAt_rpow_const 0 α⁻¹ (Or.inr (inv_nonneg.mpr hα.le))).tendsto.comp
      hραt
    rw [Real.zero_rpow (inv_ne_zero hα.ne')] at h1
    exact h1.congr fun k => Real.rpow_rpow_inv (hρpos k).le hα.ne'
  have hρhalf : ∀ᶠ k in atTop, ρ k < 1 / 2 := hρt.eventually (Iio_mem_nhds (by norm_num))
  -- Step 5: the blow-up sequence on `D_k = B̆_{R_k}(0)`, `R_k = 1/(2ρ_k)`.
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k = (ρ k * N k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, ∀ k, R k = (2 * ρ k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ → (Rn n →L[ℝ] Rn ℓ), ∀ k,
      P₀ k = ρ k • fderiv ℝ (w k) (x k) := ⟨_, fun _ => rfl⟩
  obtain ⟨ah, hah⟩ : ∃ ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∀ k z, ah k z = a k (x k + ρ k • z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Rn n → Rn ℓ, ∀ k,
      W k = fun z => s k • (w k (x k + ρ k • z) - w k (x k) - P₀ k z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ k z,
      Ψ k z = s k • ((ρ k • Φ k (x k + ρ k • z) - ρ k • Φ k (x k)) -
        (ah k z (P₀ k) - a k (x k) (P₀ k))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → Rn n, ∀ k, e k = (ρ k)⁻¹ • (y k - x k) := ⟨_, fun _ => rfl⟩
  have hspos : ∀ k, 0 < s k := fun k => by
    rw [hs]; exact inv_pos.mpr (mul_pos (hρpos k) (hNpos k))
  have hsρ : ∀ k, s k * ρ k = (N k)⁻¹ := fun k => by
    rw [hs, mul_inv, mul_comm (ρ k)⁻¹, mul_assoc, inv_mul_cancel₀ (hρpos k).ne', mul_one]
  have hRpos : ∀ k, 0 < R k := fun k => by
    rw [hR]; exact inv_pos.mpr (mul_pos two_pos (hρpos k))
  have hρR : ∀ k, ρ k * R k = 1 / 2 := fun k => by
    rw [hR, mul_inv, ← mul_assoc, mul_comm (ρ k), mul_assoc, mul_inv_cancel₀ (hρpos k).ne',
      mul_one, one_div]
  have hmap : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), x k + ρ k • z ∈ ball (0 : Rn n) 1 := by
    intro k z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖x k + ρ k • z‖ ≤ ‖x k‖ + ‖ρ k • z‖ := norm_add_le _ _
      _ = ‖x k‖ + ρ k * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg (hρpos k).le]
      _ < 1 / 2 + ρ k * R k := add_lt_add (hxn k) (mul_lt_mul_of_pos_left hz (hρpos k))
      _ = 1 := by rw [hρR k]; norm_num
  have hscale : ∀ k (z z' : Rn n),
      ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α = ρ k ^ α * ‖z - z'‖ ^ α := by
    intro k z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (hρpos k).le,
      Real.mul_rpow (hρpos k).le (norm_nonneg _)]
  -- The rescaled maps `w_k(x_k + ρ_k ·)` solve the rescaled system on `D_k` (sibling rescale).
  have hres := fun k => Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ (a k) (Φ k) (w k)
    (ball 0 1) (x k) 0 (ρ k) (R k) (hρpos k) isOpen_ball
    (by
      rw [smul_zero, add_zero, hρR k]
      exact ball_subset_ball' (by rw [dist_zero_right]; linarith [hxn k]))
    (hwC k) (hweak k)
  -- Step (0b) for the rescaled coefficients.
  have hJ : ∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
      ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ) := by
    intro k
    refine hcontJ (ah k) (ball 0 (R k)) (M * ρ k ^ α) fun z hz z' hz' P Q => ?_
    rw [hah, hah]
    calc |a k (x k + ρ k • z) P Q - a k (x k + ρ k • z') P Q|
        ≤ M * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖ * ‖Q‖ :=
          haH k _ (hmap k z hz) _ (hmap k z' hz') P Q
      _ = M * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := by rw [hscale]; ring
  have hΘc : ∀ k, ContinuousOn (fun z => ρ k • Φ k (x k + ρ k • z)) (ball (0 : Rn n) (R k)) := by
    intro k
    refine hcontL _ (ball 0 (R k)) (ρ k * G k * ρ k ^ α) fun z hz z' hz' P => ?_
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (hρpos k)]
    calc ρ k * |Φ k (x k + ρ k • z) P - Φ k (x k + ρ k • z') P|
        ≤ ρ k * (G k * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖) :=
          mul_le_mul_of_nonneg_left (hΦH k _ (hmap k z hz) _ (hmap k z' hz') P) (hρpos k).le
      _ = ρ k * G k * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ := by rw [hscale]; ring
  -- Step 6: the blow-ups solve the rescaled system with error `Ψ_k`
  -- (sibling zero mean and child `weak_eq_sub_affine`).
  have hsub := fun k => Submission.dohr_eb_sch_bu_weak_eq_sub_affine n ℓ (ah k)
    (fun z => ρ k • Φ k (x k + ρ k • z)) (fun z => w k (x k + ρ k • z)) (ball 0 (R k))
    (a k (x k)) (ρ k • Φ k (x k)) (P₀ k) (w k (x k)) (s k) isOpen_ball (hJ k) (hΘc k)
    (hres k).1 (fun ζ hζ hζc hζs => by simpa only [hah] using (hres k).2.2 ζ hζ hζc hζs)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
  have hWC : ∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k)) := fun k => by
    rw [hW k]; exact (hsub k).1
  have hDW : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k),
      fderiv ℝ (W k) z = s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) := by
    intro k z hz
    rw [hW k, (hsub k).2.1 z hz, (hres k).2.1 z hz]
  have hW0 : ∀ k, W k 0 = 0 := fun k => by
    rw [hW k]; simp
  have hDW0 : ∀ k, fderiv ℝ (W k) 0 = 0 := fun k => by
    rw [hDW k 0 (mem_ball_self (hRpos k)), hP₀, smul_zero, add_zero, sub_self, smul_zero]
  have hWH : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ δ⁻¹ * ‖z - z'‖ ^ α := by
    intro k z hz z' hz'
    rw [hDW k z hz, hDW k z' hz']
    have h1 : s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) -
        s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z') - P₀ k) =
        (s k * ρ k) • (fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')) := by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, smul_smul]
    rw [h1, norm_smul, Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ]
    have h2 := hwH k _ (hmap k z hz) _ (hmap k z' hz')
    rw [hscale] at h2
    have h3 : (N k)⁻¹ * (K k * ρ k ^ α) ≤ δ⁻¹ := by
      rw [inv_mul_le_iff₀ (hNpos k), le_mul_inv_iff₀ hδ]
      calc K k * ρ k ^ α * δ = δ * K k * ρ k ^ α := by ring
        _ ≤ N k := hKN k
    calc (N k)⁻¹ * ‖fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')‖
        ≤ (N k)⁻¹ * (K k * (ρ k ^ α * ‖z - z'‖ ^ α)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (hNpos k).le)
      _ = (N k)⁻¹ * (K k * ρ k ^ α) * ‖z - z'‖ ^ α := by ring
      _ ≤ δ⁻¹ * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) α)
  -- Bounds for the frozen and rescaled coefficients and for the error `Ψ_k`.
  have hah0 : ∀ k, ah k 0 = a k (x k) := fun k => by rw [hah, smul_zero, add_zero]
  have hell0 : ∀ k (P : Rn n →L[ℝ] Rn ℓ), lam * ‖P‖ ^ 2 ≤ ah k 0 P P := fun k P => by
    rw [hah0]; exact hell k (x k) (hx1 k) P
  have hbd0 : ∀ k (P Q : Rn n →L[ℝ] Rn ℓ), |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖ := fun k P Q => by
    rw [hah0]; exact hbd k (x k) (hx1 k) P Q
  have hahb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah k z P Q - ah k 0 P Q| ≤ M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by
    intro k z hz P Q
    have h := haH k _ (hmap k z hz) _ (hmap k 0 (mem_ball_self (hRpos k))) P Q
    rw [hscale, sub_zero] at h
    rw [hah k z, hah k 0]
    calc _ ≤ M * (ρ k ^ α * ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by ring
  have hΨd : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q - Ψ k z' Q| ≤
        (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
    intro k z hz z' hz' Q
    have hΦ := hΦH k _ (hmap k z hz) _ (hmap k z' hz') Q
    have ha := haH k _ (hmap k z hz) _ (hmap k z' hz') (P₀ k) Q
    have hP : ‖P₀ k‖ = ρ k * ‖fderiv ℝ (w k) (x k)‖ := by
      rw [hP₀, norm_smul, Real.norm_of_nonneg (hρpos k).le]
    rw [hscale] at hΦ ha
    rw [hP] at ha
    have hexp : Ψ k z Q - Ψ k z' Q = s k * (ρ k * (Φ k (x k + ρ k • z) Q -
        Φ k (x k + ρ k • z') Q) - (a k (x k + ρ k • z) (P₀ k) Q -
        a k (x k + ρ k • z') (P₀ k) Q)) := by
      rw [hΨ, hΨ, hah, hah]
      simp only [smul_apply, sub_apply, smul_eq_mul]
      ring
    rw [hexp, abs_mul, abs_of_pos (hspos k)]
    have htri : |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
        (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)| ≤
        ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (hρpos k)]
      exact add_le_add (mul_le_mul_of_nonneg_left hΦ (hρpos k).le) ha
    calc s k * |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
          (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)|
        ≤ s k * (ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖) :=
          mul_le_mul_of_nonneg_left htri (hspos k).le
      _ = (s k * ρ k) * (G k + M * ‖fderiv ℝ (w k) (x k)‖) * ρ k ^ α * ‖z - z'‖ ^ α * ‖Q‖ := by
          ring
      _ = (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
          rw [hsρ]; ring
  have hΨc : ∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k)) := fun k => hcontL (Ψ k) _ _ (hΨd k)
  have hΨb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ,
      |Ψ k z Q| ≤ (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z‖ ^ α * ‖Q‖ := by
    intro k z hz Q
    have h := hΨd k z hz 0 (mem_ball_self (hRpos k)) Q
    have h0 : Ψ k 0 Q = 0 := by
      rw [hΨ, hah]
      simp
    rwa [h0, sub_zero, sub_zero] at h
  have hWeq : ∀ k (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Rn n) (R k) →
      ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) =
        ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z) := by
    intro k ζ hζ hζc hζs
    rw [hW k]
    simp only [hΨ]
    exact (hsub k).2.2 ζ hζ hζc hζs
  -- The unit vectors `e_k = (y_k − x_k)/ρ_k` with `‖DW_k(e_k)‖ = 1`.
  have he1 : ∀ k, ‖e k‖ = 1 := fun k => by
    rw [he, norm_smul, norm_inv, Real.norm_of_nonneg (hρpos k).le, norm_sub_rev, ← hρ,
      inv_mul_cancel₀ (hρpos k).ne']
  have hxe : ∀ k, x k + ρ k • e k = y k := fun k => by
    rw [he, smul_smul, mul_inv_cancel₀ (hρpos k).ne', one_smul, add_sub_cancel]
  have heN : ∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1 := by
    filter_upwards [hρhalf] with k hk
    have hek : e k ∈ ball (0 : Rn n) (R k) := by
      rw [mem_ball_zero_iff, he1, hR, one_lt_inv₀ (mul_pos two_pos (hρpos k))]
      linarith
    rw [hDW k (e k) hek, hxe, hP₀, ← smul_sub, smul_smul, norm_smul,
      Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ, norm_sub_rev, ← hN,
      inv_mul_cancel₀ (hNpos k).ne']
  -- Limits of the scale-dependent constants.
  have hRt : Tendsto R atTop atTop := by
    have h2ρ : Tendsto (fun k => 2 * ρ k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa using hρt.const_mul 2
      · exact mul_pos two_pos (hρpos k)
    exact (tendsto_inv_nhdsGT_zero.comp h2ρ).congr fun k => (hR k).symm
  have hct : Tendsto (fun k => M * ρ k ^ α) atTop (𝓝 0) := by
    simpa using hραt.const_mul M
  have hdt : Tendsto (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k))
      atTop (𝓝 0) := by
    have hG' : Tendsto (fun k => G k * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (hG k) (div_nonneg (hραpos k).le (hNpos k).le)) ?_
        tendsto_one_div_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [mul_div_assoc', div_le_div_iff₀ (hNpos k) hk', one_mul]
      calc G k * ρ k ^ α * k = k * G k * ρ k ^ α := by ring
        _ ≤ N k := hGN k
    have hD' : Tendsto (fun k => ‖fderiv ℝ (w k) (x k)‖ * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (norm_nonneg _) (div_nonneg (hραpos k).le (hNpos k).le)) ?_ hεt
      filter_upwards [eventually_ge_atTop 5] with k hk
      rw [mul_div_assoc', div_le_iff₀ (hNpos k)]
      exact hinterp k hk (x k) (hx k)
    have h := hG'.add (hD'.const_mul M)
    rw [mul_zero, add_zero] at h
    exact h.congr fun k => by ring
  -- Steps 7–8 (child `blowup_limit`) and step 9 (sibling Liouville theorem).
  obtain ⟨A, W', hA1, hA2, hW'C, hW'H, hW'eq, hW'0, e₀, he₀⟩ :=
    Submission.dohr_eb_sch_bu_blowup_limit n ℓ α lam M δ⁻¹ W ah Ψ e R (fun k => M * ρ k ^ α)
      (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k)) hα
      (inv_nonneg.mpr hδ.le) hRt hct hdt hWC hW0 hDW0 hWH hJ hΨc hell0 hbd0 hahb hΨb hWeq
      (fun k => (he1 k).le) heN
  have hconst := Submission.dohr_eb_sch_liouville_const_coeff n ℓ α lam M δ⁻¹ A W' hα hα1 hlam
    hA1 hA2 hW'C hW'H hW'eq e₀ 0
  rw [hconst, hW'0, norm_zero] at he₀
  exact zero_ne_one he₀

end Submission

/-- **Interior `C^{1,α}` estimate on the unit ball** (the case `x₀ = 0`, `R = 1` of the Schauder
estimate in the elliptic bootstrap for Simon 7.1, second assertion).  Let `w` be `C¹` on `B̆₁(0)`
with `∫ a(x)[Dw][Dζ] = ∫ Φ(x)[Dζ]` for every `ζ ∈ C¹_c(B̆₁(0); ℝ^ℓ)`, where `a` is Legendre
elliptic with constant `lam > 0`, `a` and `Φ` are bounded and `α`-Hölder with constant `M`,
`|w| ≤ M`, and `Dw` is `α`-Hölder on `B̆₁(0)` with some constant.  Then `‖Dw‖ ≤ C` and
`‖Dw(x) − Dw(y)‖ ≤ C |x − y|^α` on `B̆_{1/2}(0)`, where `C` depends only on `n, ℓ, α, lam, M`.
Proof: take `δ = 1/16`, `C_δ` from the blow-up estimate and `C = (1024 + 128 C_δ) M`.  Rescaling
`B̆_ρ(y) ⊆ B̆₁(0)` to `B̆₁(0)` and applying the blow-up estimate there gives
`ρ^{1+α} ‖Dw(x) − Dw(x')‖ ≤ (ρ^{1+α} K / 16 + 2 C_δ M) |x − x'|^α` on `B̆_{ρ/2}(y)` whenever
`Dw` is `K`-Hölder on `B̆_ρ(y)`; with the interpolation bound for `‖Dw‖`, the absorption lemma
for the best scale-weighted Hölder constant concludes. -/
theorem Submission.dohr_eb_sch_unit_ball_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M : ℝ, 0 < lam → ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ), (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ hn α hα hα1 lam M hlam
  -- Step 0: `C_δ` from the blow-up estimate with `δ = 1/16`; for `M < 0`, (H5) is impossible.
  obtain ⟨Cδ, hCδ0, hCδ⟩ := Submission.dohr_eb_sch_blowup_holder_estimate n ℓ hn α hα hα1 lam M
    (1 / 16) hlam (by norm_num)
  by_cases hM : 0 ≤ M
  swap
  · refine ⟨0, le_rfl, fun a Φ w _ _ _ _ hS _ _ _ => ?_⟩
    exact absurd ((norm_nonneg _).trans (hS 0 (mem_ball_self one_pos))) hM
  have hA : 0 ≤ Cδ * (M + M) := mul_nonneg hCδ0 (add_nonneg hM hM)
  refine ⟨1024 * M + 64 * (Cδ * (M + M)),
    add_nonneg (mul_nonneg (by norm_num) hM) (mul_nonneg (by norm_num) hA), ?_⟩
  intro a Φ w hlg hab haH hΦH hS hw hK hweak
  -- Step 1: the one-scale estimate on every `B̆_ρ(y) ⊆ B̆₁(0)`.  With `w̃(z) = w(y + ρz)`,
  -- `Dw̃(z) = ρ Dw(y + ρz)` is `ρ^{1+α} K`-Hölder on `B̆₁(0)`, and the blow-up estimate for the
  -- rescaled data on `B̆₁(0)` (with `S = G = M`) scales back to `B̆_{ρ/2}(y)`.
  have hstep : ∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 →
      (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖fderiv ℝ w x - fderiv ℝ w x'‖ ≤ K * ‖x - x'‖ ^ α) →
      ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖fderiv ℝ w x - fderiv ℝ w x'‖ ≤
        (1 / 16 * ρ ^ (1 + α) * K + Cδ * (M + M)) * ‖x - x'‖ ^ α := by
    intro y ρ K hρ hyρ hHol
    have hsub : ball (y + ρ • (0 : Rn n)) (ρ * 1) ⊆ ball (0 : Rn n) 1 := by
      rw [smul_zero, add_zero, mul_one]
      exact ball_subset_ball' (by rw [dist_zero_right]; linarith)
    obtain ⟨hwt, hdwt, hweakt⟩ := Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ a Φ w
      (ball (0 : Rn n) 1) y 0 ρ 1 hρ isOpen_ball hsub hw hweak
    obtain ⟨h1, h2, h3, h4, h5⟩ := Submission.dohr_eb_sch_ube_rescaled_structure n ℓ a Φ w y ρ α
      lam M hρ hyρ hα.le hM hlg hab haH hΦH hS
    have hHolt : ∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1,
        ‖fderiv ℝ (fun z => w (y + ρ • z)) z - fderiv ℝ (fun z => w (y + ρ • z)) z'‖ ≤
          ρ ^ (1 + α) * K * ‖z - z'‖ ^ α := by
      have h := (Submission.dohr_eb_sch_ube_holder_rescale n ℓ (fderiv ℝ w) y ρ 1 α
        (ρ ^ (1 + α) * K) hρ).mpr fun x hx x' hx' => by
          rw [mul_one] at hx hx'
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hHol x hx x' hx') (Real.rpow_nonneg hρ.le _)
      intro z hz z' hz'
      rw [hdwt z hz, hdwt z' hz']
      exact h z hz z' hz'
    have hbl := hCδ (fun z => a (y + ρ • z)) (fun z => ρ • Φ (y + ρ • z))
      (fun z => w (y + ρ • z)) (ρ ^ (1 + α) * K) M M hM h1 h2 h3 h4 h5 hwt hHolt hweakt
    have h := (Submission.dohr_eb_sch_ube_holder_rescale n ℓ (fderiv ℝ w) y ρ (1 / 2) α
      (1 / 16 * (ρ ^ (1 + α) * K) + Cδ * (M + M)) hρ).mp fun z hz z' hz' => by
        rw [← hdwt z (ball_subset_ball (by norm_num) hz),
          ← hdwt z' (ball_subset_ball (by norm_num) hz')]
        exact hbl z hz z' hz'
    intro x hx x' hx'
    rw [← mul_one_div ρ 2] at hx hx'
    rw [mul_assoc (1 / 16 : ℝ)]
    exact h x hx x' hx'
  -- Step 2: the interpolation bound `‖Dw(x)‖ ≤ 2M/t + t^α K` on every `B̆_r(x) ⊆ B̆₁(0)`.
  have hint : ∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r →
      (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖fderiv ℝ w z - fderiv ℝ w z'‖ ≤ K * ‖z - z'‖ ^ α) →
      ‖fderiv ℝ w x‖ ≤ 2 * M / t + t ^ α * K := by
    intro x r t K hxr hK0 ht htr hHol
    have hsub : ball x r ⊆ ball (0 : Rn n) 1 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith)
    exact Submission.dohr_eb_sch_fderiv_norm_interpolation n ℓ w x r t α M K hα.le hK0 ht htr
      (hw.mono hsub) (fun z hz => hS z (hsub hz)) hHol
  -- Step 3: absorption with `g = Dw` and `A = 2 C_δ M`.
  exact Submission.dohr_eb_sch_ube_absorption n ℓ (fderiv ℝ w) α M (Cδ * (M + M)) hα hα1.le hM
    hA hK hstep hint

namespace Submission

/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (p. 127): the interior Schauder estimate
(Giaquinta–Martinazzi, Thms. 5.17/5.19) for `C^{1,α}` weak solutions `w` of the linear system
`∫_B a(x)[Dw][Dζ] = ∫_B Φ(x)[Dζ]` on `B = B̆_R(x₀)`, with `lam`-Legendre, bounded, `α`-Hölder
coefficients `a` and `α`-Hölder right side `Φ`: `‖Dw‖ ≤ C` and `[Dw]_α ≤ C` on `B̆_{R/2}(x₀)`, with
`C = C(n, ℓ, α, lam, M, R)`.  If `M < 0` the bound `‖w(x₀)‖ ≤ M` fails and any `C` works.
Otherwise `x = x₀ + R z` turns `(a, Φ, w)` into `(a(x₀ + R ·), R Φ(x₀ + R ·), w(x₀ + R ·))` on
`B̆₁(0)`, which satisfies the same hypotheses with `M (1 + R^α + R^{1+α})` in place of `M`; the
unit-ball estimate bounds `D(w(x₀ + R ·))(z) = R Dw(x₀ + R z)` on `B̆_{1/2}(0)`, and scaling back
gives the constant `C₁ (R⁻¹ + R^{-(1+α)})`. -/
theorem dohr_eb_schauder_interior_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M R : ℝ, 0 < lam → 0 < R → ∃ C : ℝ, ∀ (x₀ : Rn n) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ), (∀ x ∈ ball x₀ R, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball x₀ R, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ M) → ContDiffOn ℝ 1 w (ball x₀ R) → (∃ K : ℝ, ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball x₀ R, Φ x (fderiv ℝ ζ x)) → (∀ x ∈ ball x₀ (R / 2), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ hn α hα0 hα1 lam M R hlam hR
  -- Step 0: for `M < 0` hypothesis (H5) fails at `x₀`, so any constant works.
  rcases lt_or_ge M 0 with hM | hM
  · refine ⟨0, fun x₀ a Φ w _ _ _ _ hw _ _ _ => ?_⟩
    exact absurd ((norm_nonneg _).trans (hw x₀ (mem_ball_self hR))) (not_le.2 hM)
  -- Step 7: the rescaled data live on `B̆₁(0)` with `M` replaced by `M (1 + R^α + R^{1+α})`.
  have hRα : 0 < R ^ α := Real.rpow_pos_of_pos hR α
  have hR1α : R ^ (1 + α) = R * R ^ α := by rw [Real.rpow_add hR, Real.rpow_one]
  have hR1α0 : 0 < R ^ (1 + α) := Real.rpow_pos_of_pos hR _
  have hMM : M ≤ M * (1 + R ^ α + R ^ (1 + α)) := le_mul_of_one_le_right hM (by linarith)
  have hMα : M * R ^ α ≤ M * (1 + R ^ α + R ^ (1 + α)) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  have hM1α : R * (M * R ^ α) ≤ M * (1 + R ^ α + R ^ (1 + α)) := by
    rw [mul_left_comm, ← hR1α]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  obtain ⟨C₁, hC₁, hunit⟩ := Submission.dohr_eb_sch_unit_ball_estimate n ℓ hn α hα0 hα1 lam
    (M * (1 + R ^ α + R ^ (1 + α))) hlam
  refine ⟨C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹), ?_⟩
  intro x₀ a Φ w h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨K, hK⟩ := h7
  -- `z ↦ x₀ + R z` maps `B̆₁(0)` into `B̆_R(x₀)` and multiplies distances by `R`.
  have hmem : ∀ z ∈ ball (0 : Rn n) 1, x₀ + R • z ∈ ball x₀ R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
    calc R * ‖z‖ < R * 1 := mul_lt_mul_of_pos_left hz hR
      _ = R := mul_one R
  have hdist : ∀ z z' : Rn n, ‖x₀ + R • z - (x₀ + R • z')‖ ^ α = R ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hR.le,
      Real.mul_rpow hR.le (norm_nonneg _)]
  -- Step 2 for `(y, ρ) = (x₀, R)`: `w(x₀ + R ·)` is a `C¹` weak solution on `B̆₁(0)`.
  obtain ⟨hw1, hDw, hweak⟩ := Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ a Φ w
    (ball x₀ R) x₀ 0 R 1 hR isOpen_ball (by simp) h6 h8
  -- Step 6 for the rescaled data.
  obtain ⟨hsup, hhol⟩ := hunit (fun z => a (x₀ + R • z)) (fun z => R • Φ (x₀ + R • z))
    (fun z => w (x₀ + R • z))
    (fun z hz P => h1 _ (hmem z hz) P)
    (fun z hz P Q => (h2 _ (hmem z hz) P Q).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMM (norm_nonneg P))
        (norm_nonneg Q)))
    (fun z hz z' hz' P Q => by
      have h := h3 _ (hmem z hz) _ (hmem z' hz') P Q
      rw [hdist] at h
      calc _ ≤ M * (R ^ α * ‖z - z'‖ ^ α) * ‖P‖ * ‖Q‖ := h
        _ = M * R ^ α * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hMα (Real.rpow_nonneg (norm_nonneg _) _))
            (norm_nonneg P)) (norm_nonneg Q))
    (fun z hz z' hz' P => by
      have h := h4 _ (hmem z hz) _ (hmem z' hz') P
      rw [hdist] at h
      simp only [smul_apply, smul_eq_mul]
      rw [← mul_sub, abs_mul, abs_of_pos hR]
      calc _ ≤ R * (M * (R ^ α * ‖z - z'‖ ^ α) * ‖P‖) := mul_le_mul_of_nonneg_left h hR.le
        _ = R * (M * R ^ α) * ‖z - z'‖ ^ α * ‖P‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hM1α (Real.rpow_nonneg (norm_nonneg _) _))
            (norm_nonneg P))
    (fun z hz => (h5 _ (hmem z hz)).trans hMM)
    hw1
    ⟨R * K * R ^ α, fun z hz z' hz' => by
      rw [hDw z hz, hDw z' hz', ← smul_sub R (fderiv ℝ w (x₀ + R • z)) (fderiv ℝ w (x₀ + R • z')),
        norm_smul, Real.norm_of_nonneg hR.le]
      have h := hK _ (hmem z hz) _ (hmem z' hz')
      rw [hdist] at h
      calc _ ≤ R * (K * (R ^ α * ‖z - z'‖ ^ α)) := mul_le_mul_of_nonneg_left h hR.le
        _ = R * K * R ^ α * ‖z - z'‖ ^ α := by ring⟩
    hweak
  -- Scaling back: `x = x₀ + R z` with `z = R⁻¹ (x - x₀) ∈ B̆_{1/2}(0)` and `Dw̃(z) = R Dw(x)`.
  have hback : ∀ x ∈ ball x₀ (R / 2), R⁻¹ • (x - x₀) ∈ ball (0 : Rn n) (1 / 2) ∧
      fderiv ℝ (fun z => w (x₀ + R • z)) (R⁻¹ • (x - x₀)) = R • fderiv ℝ w x := by
    intro x hx
    have hz : R⁻¹ • (x - x₀) ∈ ball (0 : Rn n) (1 / 2) := by
      rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
        inv_mul_lt_iff₀ hR]
      linarith
    refine ⟨hz, ?_⟩
    rw [hDw _ (ball_subset_ball (by norm_num) hz), smul_smul, mul_inv_cancel₀ hR.ne', one_smul,
      add_sub_cancel]
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hz, hD⟩ := hback x hx
    have h := hsup _ hz
    rw [hD, norm_smul, Real.norm_of_nonneg hR.le] at h
    calc ‖fderiv ℝ w x‖ = R⁻¹ * (R * ‖fderiv ℝ w x‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      _ ≤ R⁻¹ * C₁ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hR.le)
      _ ≤ C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹) := by
          rw [mul_add, mul_comm]
          exact le_add_of_nonneg_right (mul_nonneg hC₁ (inv_nonneg.2 hR1α0.le))
  · obtain ⟨hz, hDx⟩ := hback x hx
    obtain ⟨hz', hDy⟩ := hback y hy
    have h := hhol _ hz _ hz'
    rw [hDx, hDy, ← smul_sub R (fderiv ℝ w x) (fderiv ℝ w y), norm_smul,
      Real.norm_of_nonneg hR.le, ← smul_sub R⁻¹ (x - x₀) (y - x₀), sub_sub_sub_cancel_right,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      Real.mul_rpow (inv_nonneg.2 hR.le) (norm_nonneg _), Real.inv_rpow hR.le] at h
    calc ‖fderiv ℝ w x - fderiv ℝ w y‖ = R⁻¹ * (R * ‖fderiv ℝ w x - fderiv ℝ w y‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      _ ≤ R⁻¹ * (C₁ * ((R ^ α)⁻¹ * ‖x - y‖ ^ α)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hR.le)
      _ = C₁ * (R ^ (1 + α))⁻¹ * ‖x - y‖ ^ α := by rw [hR1α, mul_inv]; ring
      _ ≤ C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹) * ‖x - y‖ ^ α := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁)
            (Real.rpow_nonneg (norm_nonneg _) _)
          exact le_add_of_nonneg_left (inv_nonneg.2 hR.le)

end Submission

end GMT.Ch05
