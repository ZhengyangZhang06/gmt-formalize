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

end Submission

end GMT.Ch05
