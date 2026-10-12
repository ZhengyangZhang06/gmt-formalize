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

set_option maxHeartbeats 1000000 in
/-- **Mass-ratio pinching at a fixed scale** (node `root.allard_any_radius-a1.pinching-a1`;
Simon Ch. 5, Theorem 6.1 used for Remark 5.3).  Assuming Theorem 6.1, for `γ ∈ (0, 1)` and
`ε ∈ (0, 1/4]` there are `δP > 0` and `cs ∈ (0, (1 - γ)/16]` such that 2.3 with `δ ≤ δP` gives
`μ_V(B_{cs ρ}(y)) ≤ (1 + ε) ω_n (cs ρ)ⁿ` for every `y ∈ spt V ∩ B_{(1+γ)ρ/2}(0)`.

`any_radius_monotonicity_bounds` pinches `ω_n⁻¹ t⁻ⁿ μ_V(B_t(0))` between `Lo δ` and `Up δ`
(`0 < t < ρ`), and Hölder gives `t^{1-n} ∫_{B_t(0)} |H| dμ_V ≤ KH δ`.  If `|y| ≤ κ₀ ρ`, (M1) at `y`
with outer radius `(1 - κ₀) ρ` gives the bound.  Otherwise put `R = |y|/(1 - θ₀)`, dilate by
`any_radius_rescaled_varifold`, and apply 6.1 with `λ = δ̃ = lam δ = Up δ - Lo δ + KH δ`,
`ξ = y/R`, `ρ = θ₀`, `τ = 2λ`.  (M1) and the centre bounds control the comparison ball
`B_{2λθ₀R}(2λ y)`, and (M1) moves the pinching from `B_{(1-δ̃^{1/4})θ₀R}(y)` down to `B_{cs ρ}(y)`.
Every smallness condition on `δ` is a limit as `δ → 0⁺`; the `δ̃^{1/4} |log λ|` term uses
`tendsto_log_mul_rpow_nhdsGT_zero`. -/
theorem any_radius_pinching : ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ ε : ℝ, 0 < γ → γ < 1 → 0 < ε → ε ≤ 1 / 4 → ∃ δP cs : ℝ, 0 < δP ∧ 0 < cs ∧ cs ≤ (1 - γ) / 16 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → ∀ y ∈ V.support ∩ closedBall 0 ((1 + γ) / 2 * ρ), V.weight (closedBall y (cs * ρ)) ≤ ENNReal.ofReal ((1 + ε) * (unitBallVolume n * (cs * ρ) ^ n)) := by
  intro h61 n ℓ hn p hp γ ε hγ0 hγ1 hε0 hε4
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hpn : 0 < p - n := by linarith
  /- `ω = ω_n > 0`. -/
  have hω0' : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, unitBallVolume n = ω := ⟨_, rfl⟩
  have hω0 : 0 < ω := hω ▸ hω0'
  rw [hω]
  /- The constant `C₉ = C(n, ℓ, 2ω_n)` of Theorem 6.1. -/
  obtain ⟨C₉, hC₉⟩ := h61 n ℓ hn (2 * ω) (by positivity)
  rw [hω] at hC₉
  /- `θ₀ = (1 - γ)/8`. -/
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, θ₀ = (1 - γ) / 8 := ⟨_, rfl⟩
  have hθ₀0 : 0 < θ₀ := by rw [hθ₀]; linarith
  have hθ₀8 : θ₀ < 1 / 8 := by rw [hθ₀]; linarith
  /- `κ₀ ∈ (0, 1/4]` with `(1 - κ₀)⁻ⁿ < 1 + ε`. -/
  obtain ⟨κ₀, hκ₀0, hκ₀4, hκ₀ε⟩ : ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 / 4 ∧ ((1 - κ₀) ^ n)⁻¹ < 1 + ε := by
    have h1 : Tendsto (fun k : ℝ => ((1 - k) ^ n)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have h : Tendsto (fun k : ℝ => ((1 - k) ^ n)⁻¹) (𝓝 0) (𝓝 (((1 - 0) ^ n)⁻¹)) :=
        ((tendsto_const_nhds.sub tendsto_id).pow n).inv₀ (by simp)
      refine (h.mono_left nhdsWithin_le_nhds).mono_right (le_of_eq ?_)
      congr 1
      simp
    have h2 := h1.eventually_lt_const (by linarith : (1 : ℝ) < 1 + ε)
    have h3 : ∀ᶠ k in 𝓝[>] (0 : ℝ), k < 1 / 4 :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually_lt_const (by norm_num)
    obtain ⟨k, hk1, hk2, hk3⟩ := (h2.and (h3.and eventually_mem_nhdsWithin)).exists
    exact ⟨k, hk3, hk2.le, hk1⟩
  /- `cs = κ₀ θ₀ / 2`. -/
  obtain ⟨cs, hcs⟩ : ∃ cs : ℝ, cs = κ₀ * θ₀ / 2 := ⟨_, rfl⟩
  have hcs0 : 0 < cs := by rw [hcs]; positivity
  have hcs16 : cs ≤ (1 - γ) / 16 := by
    rw [hcs]
    have : κ₀ * θ₀ ≤ 1 / 4 * θ₀ := mul_le_mul_of_nonneg_right hκ₀4 hθ₀0.le
    rw [hθ₀] at this ⊢
    linarith
  /- The quantities depending on `δ`: `Λ = 4pδ/(p - n) = δ/κ`, the monotonicity constants
  `e^{2Λ}` and `2e^Λ Λ`, the two-sided density bounds `Up`, `Lo` at the centre, the Hölder constant
  `KH = (2ω_n)^{1 - 1/p}`, and `lam = Up - Lo + KH δ` (used both as `λ` and as `δ` in 6.1). -/
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ → ℝ, ∀ d, Lam d = 4 * p * d / (p - n) := ⟨_, fun _ => rfl⟩
  obtain ⟨ea, hea⟩ : ∃ ea : ℝ → ℝ, ∀ d, ea d = Real.exp (2 * Lam d) := ⟨_, fun _ => rfl⟩
  obtain ⟨eb, heb⟩ : ∃ eb : ℝ → ℝ, ∀ d, eb d = 2 * Real.exp (Lam d) * Lam d := ⟨_, fun _ => rfl⟩
  obtain ⟨Up, hUp⟩ : ∃ Up : ℝ → ℝ, ∀ d, Up d = ea d * (1 + d) + eb d / ω := ⟨_, fun _ => rfl⟩
  obtain ⟨Lo, hLo⟩ : ∃ Lo : ℝ → ℝ, ∀ d, Lo d = Real.exp (-Lam d) * (ω - Lam d) / ω :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨KH, hKH⟩ : ∃ KH : ℝ, KH = (2 * ω) ^ (1 - 1 / p) := ⟨_, rfl⟩
  have hKH0 : 0 < KH := by rw [hKH]; positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ → ℝ, ∀ d, lam d = Up d - Lo d + KH * d := ⟨_, fun _ => rfl⟩
  obtain ⟨qq, hqq⟩ : ∃ qq : ℝ → ℝ, ∀ d, qq d = lam d ^ (1 / 4 : ℝ) := ⟨_, fun _ => rfl⟩
  /- Elementary bounds for `d ≥ 0`. -/
  have hLam0 : ∀ d, 0 ≤ d → 0 ≤ Lam d := fun d hd => by rw [hLam]; positivity
  have hea1 : ∀ d, 0 ≤ d → 1 ≤ ea d := fun d hd => by
    rw [hea]; exact Real.one_le_exp (by linarith [hLam0 d hd])
  have heb0 : ∀ d, 0 ≤ d → 0 ≤ eb d := fun d hd => by
    rw [heb]; have := hLam0 d hd; positivity
  have hUp1 : ∀ d, 0 ≤ d → 1 ≤ Up d := fun d hd => by
    rw [hUp]
    have h1 := hea1 d hd
    have h2 : 0 ≤ eb d / ω := div_nonneg (heb0 d hd) hω0.le
    have h3 : ea d ≤ ea d * (1 + d) := le_mul_of_one_le_right (by linarith) (by linarith)
    linarith
  have hLo1 : ∀ d, 0 ≤ d → Lo d ≤ 1 := fun d hd => by
    rw [hLo, div_le_one hω0]
    have h1 := hLam0 d hd
    have h2 : Real.exp (-Lam d) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 := Real.exp_pos (-Lam d)
    calc Real.exp (-Lam d) * (ω - Lam d) ≤ Real.exp (-Lam d) * ω :=
          mul_le_mul_of_nonneg_left (by linarith) h3.le
      _ ≤ 1 * ω := mul_le_mul_of_nonneg_right h2 hω0.le
      _ = ω := one_mul ω
  have hlam_pos : ∀ d, 0 < d → 0 < lam d := fun d hd => by
    rw [hlam]
    have := hUp1 d hd.le
    have := hLo1 d hd.le
    have : 0 < KH * d := mul_pos hKH0 hd
    linarith
  /- Limits as `d → 0⁺`. -/
  have tid : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have tLam : Tendsto Lam (𝓝[>] 0) (𝓝 0) := by
    have h := (tid.const_mul (4 * p)).div_const (p - n)
    rw [mul_zero, zero_div] at h
    exact h.congr fun d => (hLam d).symm
  have tea : Tendsto ea (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun x : ℝ => Real.exp (2 * x) := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [mul_zero, Real.exp_zero] at h
    exact h.congr fun d => (hea d).symm
  have teb : Tendsto eb (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => 2 * Real.exp x * x := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [mul_zero] at h
    exact h.congr fun d => (heb d).symm
  have tUp : Tendsto Up (𝓝[>] 0) (𝓝 1) := by
    have h := (tea.mul (tid.const_add 1)).add (teb.div_const ω)
    rw [add_zero, mul_one, zero_div, add_zero] at h
    exact h.congr fun d => (hUp d).symm
  have tLo : Tendsto Lo (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun x : ℝ => Real.exp (-x) * (ω - x) / ω := by fun_prop
    have h := (hc.tendsto 0).comp tLam
    rw [neg_zero, Real.exp_zero, sub_zero, one_mul, div_self hω0.ne'] at h
    exact h.congr fun d => (hLo d).symm
  have tlam : Tendsto lam (𝓝[>] 0) (𝓝 0) := by
    have h := (tUp.sub tLo).add (tid.const_mul KH)
    rw [sub_self, mul_zero, add_zero] at h
    exact h.congr fun d => (hlam d).symm
  have tqq : Tendsto qq (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => x ^ (1 / 4 : ℝ) := Real.continuous_rpow_const (by norm_num)
    have h := (hc.tendsto 0).comp tlam
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.congr fun d => (hqq d).symm
  have tlog : Tendsto (fun d => qq d * |Real.log (lam d)|) (𝓝[>] 0) (𝓝 0) := by
    have tlam' : Tendsto lam (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tlam, eventually_mem_nhdsWithin.mono fun d hd => hlam_pos d hd⟩
    have h := ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 4)).comp tlam').abs
    rw [abs_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with d hd
    show |Real.log (lam d) * lam d ^ (1 / 4 : ℝ)| = qq d * |Real.log (lam d)|
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hlam_pos d hd).le _), hqq d, mul_comm]
  have tA : Tendsto (fun d => ea d * ((1 + d) * ω * ((1 - κ₀) ^ n)⁻¹) + eb d) (𝓝[>] 0)
      (𝓝 (ω * ((1 - κ₀) ^ n)⁻¹)) := by
    have h := (tea.mul (((tid.const_add 1).mul_const ω).mul_const ((1 - κ₀) ^ n)⁻¹)).add teb
    refine h.mono_right (le_of_eq ?_)
    congr 1
    ring
  have tB : Tendsto (fun d => ea d * (((1 - qq d) ^ n)⁻¹ * (ea d * (Up d * ω * (1 + 4 * lam d) ^ n) +
      eb d + max C₉ 0 * (qq d * |Real.log (lam d)|) / θ₀ ^ n)) + eb d) (𝓝[>] 0) (𝓝 ω) := by
    have h := (tea.mul ((((tqq.const_sub 1).pow n).inv₀ (by simp)).mul
      (((tea.mul ((tUp.mul_const ω).mul (((tlam.const_mul 4).const_add 1).pow n))).add teb).add
        ((tlog.const_mul (max C₉ 0)).div_const (θ₀ ^ n))))).add teb
    refine h.mono_right (le_of_eq ?_)
    congr 1
    simp
  /- The finitely many smallness conditions on `δ`, all of which hold for small `δ > 0`. -/
  obtain ⟨P, hP⟩ : ∃ P : ℝ → Prop, ∀ d, P d ↔ (d ≤ (p - n) / (4 * p) ∧ d ≤ 1 / 4 ∧ Up d ≤ 2 ∧
      lam d < 1 / 4 ∧ qq d ≤ 1 / 2 ∧
      ea d * ((1 + d) * ω * ((1 - κ₀) ^ n)⁻¹) + eb d ≤ (1 + ε) * ω ∧
      ea d * (((1 - qq d) ^ n)⁻¹ * (ea d * (Up d * ω * (1 + 4 * lam d) ^ n) + eb d +
        max C₉ 0 * (qq d * |Real.log (lam d)|) / θ₀ ^ n)) + eb d ≤ (1 + ε) * ω) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), P d := by
    have e1 := tid.eventually_lt_const (show (0 : ℝ) < (p - n) / (4 * p) by positivity)
    have e2 := tid.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)
    have e3 := tUp.eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
    have e4 := tlam.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)
    have e5 := tqq.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
    have e6 := tA.eventually_lt_const (show ω * ((1 - κ₀) ^ n)⁻¹ < (1 + ε) * ω by
      rw [mul_comm]; exact mul_lt_mul_of_pos_right hκ₀ε hω0)
    have e7 := tB.eventually_lt_const (show ω < (1 + ε) * ω by linarith [mul_pos hε0 hω0])
    filter_upwards [e1, e2, e3, e4, e5, e6, e7] with d h1 h2 h3 h4 h5 h6 h7
    exact (hP d).mpr ⟨h1.le, h2.le, h3.le, h4, h5.le, h6.le, h7.le⟩
  obtain ⟨δP, hδP0, hδP⟩ : ∃ δP > 0, ∀ d, 0 < d → d ≤ δP → P d := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr0, hr⟩ := hev
    refine ⟨r / 2, by positivity, fun d hd0 hdP => hr ?_ hd0⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hd0]
    linarith
  refine ⟨δP, cs, hδP0, hcs0, hcs16, ?_⟩
  /- Fix the data. -/
  intro U hU V H δ ρ hδ0 hδP' hA y hy
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := (hP δ).mp (hδP δ hδ0 hδP')
  obtain ⟨M1, M2, -⟩ := Submission.any_radius_monotonicity_bounds n ℓ hn p hp U hU V H δ ρ hδ0 c1 hA
  obtain ⟨hρ, hHmc, -, h0supp, hBU, hmass, hK⟩ := hA
  rw [← hLam δ, ← hea δ, ← heb δ] at M1
  rw [← hLam δ, hω] at M2
  rw [hω] at hmass
  have hea0 : 0 ≤ ea δ := zero_le_one.trans (hea1 δ hδ0.le)
  have heb0' : 0 ≤ eb δ := heb0 δ hδ0.le
  /- Finiteness of masses of balls in `B_ρ(0)`. -/
  have hfinρ : V.weight (closedBall 0 ρ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hfin : ∀ x t, closedBall x t ⊆ closedBall 0 ρ → V.weight (closedBall x t) ≠ ⊤ :=
    fun x t h => ne_top_of_le_ne_top hfinρ (measure_mono h)
  have hmassR : (V.weight (closedBall 0 ρ)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hmass
  /- (M1) with the outer radius included: `s⁻ⁿ μ(B_s(z)) ≤ e^{2Λ} R⁻ⁿ μ(B_R(z)) + 2e^Λ Λ`. -/
  have M1' : ∀ (z : Amb n ℓ) (Rz s : ℝ), 0 < s → s ≤ Rz → closedBall z Rz ⊆ closedBall 0 ρ →
      (V.weight (closedBall z s)).toReal / s ^ n ≤
        ea δ * ((V.weight (closedBall z Rz)).toReal / Rz ^ n) + eb δ := by
    intro z Rz s hs hsR hsub
    have hRz : 0 < Rz := hs.trans_le hsR
    rcases hsR.lt_or_eq with hlt | rfl
    · have hlim : Tendsto (fun r : ℝ => ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) + eb δ)
          (𝓝[<] Rz) (𝓝 (ea δ * ((V.weight (closedBall z Rz)).toReal / Rz ^ n) + eb δ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have hc : ContinuousAt (fun r : ℝ => ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) +
            eb δ) Rz := by
          fun_prop (disch := exact pow_ne_zero _ hRz.ne')
        exact hc.tendsto
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hlt] with r hr
      have hr0 : 0 < r := hs.trans hr.1
      calc (V.weight (closedBall z s)).toReal / s ^ n
          ≤ ea δ * ((V.weight (closedBall z r)).toReal / r ^ n) + eb δ :=
            M1 z Rz s r hs hr.1.le hr.2 hsub
        _ ≤ ea δ * ((V.weight (closedBall z Rz)).toReal / r ^ n) + eb δ := by
            have hmono : (V.weight (closedBall z r)).toReal ≤ (V.weight (closedBall z Rz)).toReal :=
              ENNReal.toReal_mono (hfin z Rz hsub)
                (measure_mono (closedBall_subset_closedBall hr.2.le))
            exact add_le_add (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hmono (by positivity)) hea0) le_rfl
    · have h1 : 0 ≤ (V.weight (closedBall z s)).toReal / s ^ n := by positivity
      have h2 := mul_le_mul_of_nonneg_right (hea1 δ hδ0.le) h1
      linarith
  /- Step 1a: two-sided density bounds at the centre. -/
  have hup : ∀ t, 0 < t → t ≤ ρ → (V.weight (closedBall 0 t)).toReal ≤ Up δ * ω * t ^ n := by
    intro t ht htρ
    have h1 := M1' 0 ρ t ht htρ subset_rfl
    have h2 : (V.weight (closedBall 0 ρ)).toReal / ρ ^ n ≤ (1 + δ) * ω := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h3 : (V.weight (closedBall 0 t)).toReal / t ^ n ≤ Up δ * ω := by
      calc (V.weight (closedBall 0 t)).toReal / t ^ n ≤ ea δ * ((1 + δ) * ω) + eb δ :=
            h1.trans (by gcongr)
        _ = Up δ * ω := by rw [hUp]; field_simp
    rwa [div_le_iff₀ (by positivity)] at h3
  have hlo : ∀ t, 0 < t → t < ρ → Lo δ * ω * t ^ n ≤ (V.weight (closedBall 0 t)).toReal := by
    intro t ht htρ
    have h1 := M2 0 h0supp ρ t ht htρ subset_rfl
    have h2 : Lo δ * ω = Real.exp (-Lam δ) * (ω - Lam δ) := by rw [hLo]; field_simp
    rw [h2]
    exact h1
  have hratio : ∀ t, 0 < t → t < ρ →
      Lo δ ≤ (V.weight (closedBall 0 t)).toReal / (ω * t ^ n) ∧
        (V.weight (closedBall 0 t)).toReal / (ω * t ^ n) ≤ Up δ := by
    intro t ht htρ
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have := hlo t ht htρ
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have := hup t ht htρ.le
      linarith
  /- Step 1b: `t^{1-n} ∫_{B_t(0)} |H| dμ ≤ KH δ` for `0 < t ≤ ρ` (Hölder). -/
  have hHint : IntegrableOn H (closedBall 0 ρ) V.weight :=
    hHmc.1.integrableOn_compact_subset hBU (isCompact_closedBall 0 ρ)
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = (∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) :=
    ⟨_, rfl⟩
  have hJb : ENNReal.ofReal (ρ ^ (1 - n / p)) * J ≤ ENNReal.ofReal δ := by
    have hK' : (ENNReal.ofReal (ρ ^ (p - n)) * ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^
        (1 / p) ≤ ENNReal.ofReal δ := hK
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hρ.le,
      show (p - n) * (1 / p) = 1 - n / p by field_simp] at hK'
    rw [hJ]
    exact hK'
  have hJtop : J ≠ ⊤ := by
    intro hJt
    rw [hJt, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne'] at hJb
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hJb)
  have hJreal : ρ ^ (1 - n / p) * J.toReal ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hδ0.le] at this
  have hHold : ∀ t, 0 < t → t ≤ ρ → ∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight ≤
      J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) := by
    intro t ht htρ
    have hsub : closedBall (0 : Amb n ℓ) t ⊆ closedBall 0 ρ := closedBall_subset_closedBall htρ
    have hmeas : AEStronglyMeasurable H (V.weight.restrict (closedBall 0 t)) :=
      hHint.aestronglyMeasurable.mono_set hsub
    have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ zero_lt_one hp1.le hmeas
    unfold eLpNorm' at h
    simp only [ENNReal.rpow_one, div_one, Measure.restrict_apply_univ] at h
    have hμt : V.weight (closedBall 0 t) ≤ ENNReal.ofReal (2 * ω * t ^ n) := by
      rw [ENNReal.le_ofReal_iff_toReal_le (hfin 0 t hsub) (by positivity)]
      calc (V.weight (closedBall 0 t)).toReal ≤ Up δ * ω * t ^ n := hup t ht htρ
        _ ≤ 2 * ω * t ^ n := by gcongr
    have hexp : 0 ≤ 1 - 1 / p := by
      rw [sub_nonneg, div_le_one hp0]
      exact hp1.le
    calc ∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight
        ≤ (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) *
            V.weight (closedBall 0 t) ^ (1 - 1 / p) := h
      _ ≤ J * ENNReal.ofReal (2 * ω * t ^ n) ^ (1 - 1 / p) := by
          rw [hJ]
          gcongr
      _ = J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hexp]
  have hHbound : ∀ t, 0 < t → t ≤ ρ → (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight) ≠ ⊤ ∧
      t ^ (1 - (n : ℝ)) * (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal ≤ KH * δ := by
    intro t ht htρ
    have h1 := hHold t ht htρ
    have hne : J * ENNReal.ofReal ((2 * ω * t ^ n) ^ (1 - 1 / p)) ≠ ⊤ :=
      ENNReal.mul_ne_top hJtop ENNReal.ofReal_ne_top
    refine ⟨ne_top_of_le_ne_top hne h1, ?_⟩
    have h2 : (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal ≤
        J.toReal * (2 * ω * t ^ n) ^ (1 - 1 / p) := by
      have := ENNReal.toReal_mono hne h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hid : t ^ (1 - (n : ℝ)) * (2 * ω * t ^ n) ^ (1 - 1 / p) = KH * t ^ (1 - n / p) := by
      rw [hKH, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast t n,
        ← Real.rpow_mul ht.le, mul_left_comm, ← Real.rpow_add ht]
      congr 2
      ring
    have htp : t ^ (1 - n / p) ≤ ρ ^ (1 - n / p) := by
      apply Real.rpow_le_rpow ht.le htρ
      rw [sub_nonneg, div_le_one hp0]
      exact hp.le
    calc t ^ (1 - (n : ℝ)) * (∫⁻ x in closedBall 0 t, ‖H x‖ₑ ∂V.weight).toReal
        ≤ t ^ (1 - (n : ℝ)) * (J.toReal * (2 * ω * t ^ n) ^ (1 - 1 / p)) := by gcongr
      _ = J.toReal * (KH * t ^ (1 - n / p)) := by rw [← hid]; ring
      _ ≤ J.toReal * (KH * ρ ^ (1 - n / p)) := by gcongr
      _ = KH * (ρ ^ (1 - n / p) * J.toReal) := by ring
      _ ≤ KH * δ := by gcongr
  /- The point `y`. -/
  obtain ⟨-, hyB⟩ := hy
  rw [mem_closedBall_zero_iff] at hyB
  have hyρ : ‖y‖ ≤ ρ := hyB.trans (mul_le_of_le_one_left hρ.le (by linarith))
  have hsubcs : closedBall y (cs * ρ) ⊆ closedBall 0 ρ := by
    apply closedBall_subset_closedBall'
    rw [dist_zero_right]
    have : cs * ρ ≤ (1 - γ) / 16 * ρ := mul_le_mul_of_nonneg_right hcs16 hρ.le
    have : γ * ρ ≤ ρ := mul_le_of_le_one_left hρ.le hγ1.le
    linarith
  suffices hreal : (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n ≤ (1 + ε) * ω by
    rw [ENNReal.le_ofReal_iff_toReal_le (hfin y _ hsubcs) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hreal
    linarith
  rcases le_or_gt ‖y‖ (κ₀ * ρ) with hya | hyb
  · /- Case (a): `|y| ≤ κ₀ ρ`; (M1) at `y` with outer radius `(1 - κ₀) ρ`. -/
    have hRa : 0 < (1 - κ₀) * ρ := by
      have : 0 < 1 - κ₀ := by linarith
      positivity
    have hsubA : closedBall y ((1 - κ₀) * ρ) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right]
      linarith
    have hcsRa : cs * ρ ≤ (1 - κ₀) * ρ := by
      have : cs ≤ 1 - κ₀ := by
        have : κ₀ * θ₀ ≤ 1 / 4 * (1 / 8) := by
          apply mul_le_mul hκ₀4 hθ₀8.le hθ₀0.le (by norm_num)
        rw [hcs]
        linarith
      exact mul_le_mul_of_nonneg_right this hρ.le
    have h1 := M1' y ((1 - κ₀) * ρ) (cs * ρ) (by positivity) hcsRa hsubA
    have h2 : (V.weight (closedBall y ((1 - κ₀) * ρ))).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
      (ENNReal.toReal_mono hfinρ (measure_mono hsubA)).trans hmassR
    have h3 : (V.weight (closedBall y ((1 - κ₀) * ρ))).toReal / ((1 - κ₀) * ρ) ^ n ≤
        (1 + δ) * ω * ((1 - κ₀) ^ n)⁻¹ := by
      have hk : 0 < 1 - κ₀ := by linarith
      rw [div_le_iff₀ (by positivity)]
      calc (V.weight (closedBall y ((1 - κ₀) * ρ))).toReal ≤ (1 + δ) * (ω * ρ ^ n) := h2
        _ = (1 + δ) * ω * ((1 - κ₀) ^ n)⁻¹ * ((1 - κ₀) * ρ) ^ n := by
            rw [mul_pow]
            field_simp
    calc (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n
        ≤ ea δ * ((V.weight (closedBall y ((1 - κ₀) * ρ))).toReal / ((1 - κ₀) * ρ) ^ n) + eb δ := h1
      _ ≤ ea δ * ((1 + δ) * ω * ((1 - κ₀) ^ n)⁻¹) + eb δ := by gcongr
      _ ≤ (1 + ε) * ω := c6
  · /- Case (b): `|y| > κ₀ ρ`; dilate by `R = |y|/(1 - θ₀)` and apply Theorem 6.1. -/
    have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (by positivity) hyb
    have hθ1 : 0 < 1 - θ₀ := by linarith
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖y‖ / (1 - θ₀) := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hRdef]; positivity
    have hyR : ‖y‖ = (1 - θ₀) * R := by rw [hRdef]; field_simp
    have hRρ : R < ρ := by
      have : (1 + γ) / 2 * ρ < (1 - θ₀) * ρ := by
        apply mul_lt_mul_of_pos_right _ hρ
        rw [hθ₀]
        linarith
      refine lt_of_mul_lt_mul_left ?_ hθ1.le
      linarith
    have hκR : κ₀ * ρ < R := by
      have : ‖y‖ ≤ R := by rw [hyR]; exact mul_le_of_le_one_left hR0.le (by linarith)
      linarith
    set l := lam δ
    have hl0 : 0 < l := hlam_pos δ hδ0
    have hq0 : 0 ≤ qq δ := by rw [hqq]; exact Real.rpow_nonneg hl0.le _
    /- The dilated varifold `V'` (centre `0`, scale `R`). -/
    obtain ⟨V', -, -, hW, -, -, hHV'⟩ := Submission.any_radius_rescaled_varifold n ℓ U hU V 0 R hR0
    have hH' := hHV' H hHmc
    have hmeasg : Measurable (fun z : Amb n ℓ => R⁻¹ • (z - 0)) := by fun_prop
    have hpre : ∀ (x : Amb n ℓ) (t : ℝ),
        (fun z : Amb n ℓ => R⁻¹ • (z - 0)) ⁻¹' closedBall x t = closedBall (R • x) (R * t) := by
      intro x t
      ext z
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero]
      rw [show R⁻¹ • z - x = R⁻¹ • (z - R • x) by rw [smul_sub, inv_smul_smul₀ hR0.ne'],
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, inv_mul_le_iff₀ hR0]
    have hball : ∀ (x : Amb n ℓ) (t : ℝ), V'.weight (closedBall x t) =
        (ENNReal.ofReal (R ^ n))⁻¹ * V.weight (closedBall (R • x) (R * t)) := by
      intro x t
      rw [hW, Measure.smul_apply, Measure.map_apply hmeasg measurableSet_closedBall, hpre,
        smul_eq_mul]
    have hballR : ∀ (x : Amb n ℓ) (t : ℝ), (V'.weight (closedBall x t)).toReal =
        (R ^ n)⁻¹ * (V.weight (closedBall (R • x) (R * t))).toReal := by
      intro x t
      rw [hball, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
    have hinvne : (ENNReal.ofReal (R ^ n))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hballfin : ∀ (x : Amb n ℓ) (t : ℝ), closedBall (R • x) (R * t) ⊆ closedBall 0 ρ →
        V'.weight (closedBall x t) ≠ ⊤ := by
      intro x t h
      rw [hball]
      exact ENNReal.mul_ne_top hinvne (hfin _ _ h)
    /- Hypotheses of 6.1 for `V'`. -/
    have hξ : ‖R⁻¹ • y‖ = 1 - θ₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, hyR]
      field_simp
    have hU'open : IsOpen ((fun x => (0 : Amb n ℓ) + R • x) ⁻¹' U) :=
      hU.preimage (by fun_prop)
    have hB1 : closedBall (0 : Amb n ℓ) 1 ⊆ (fun x => (0 : Amb n ℓ) + R • x) ⁻¹' U := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      simp only [mem_preimage, zero_add]
      apply hBU
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
      calc R * ‖x‖ ≤ R * 1 := mul_le_mul_of_nonneg_left hx hR0.le
        _ ≤ ρ := by linarith
    have hmass' : V'.weight (closedBall 0 1) ≤ ENNReal.ofReal (2 * ω) := by
      rw [ENNReal.le_ofReal_iff_toReal_le
        (hballfin 0 1 (by rw [smul_zero, mul_one]; exact closedBall_subset_closedBall hRρ.le))
        (by positivity), hballR, smul_zero, mul_one]
      have := hup R hR0 hRρ.le
      rw [inv_mul_le_iff₀ (by positivity)]
      calc (V.weight (closedBall 0 R)).toReal ≤ Up δ * ω * R ^ n := this
        _ ≤ 2 * ω * R ^ n := by gcongr
        _ = R ^ n * (2 * ω) := by ring
    have hpinch : ∀ r ∈ Icc l 1,
        |(V'.weight (closedBall 0 1)).toReal / ω -
            (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n)| +
          r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
          l := by
      intro r hr
      have hr0 : 0 < r := hl0.trans_le hr.1
      have hRr : R * r ≤ ρ := by
        calc R * r ≤ R * 1 := mul_le_mul_of_nonneg_left hr.2 hR0.le
          _ ≤ ρ := by linarith
      have hRl : R * l < ρ := by
        calc R * l < R * 1 := mul_lt_mul_of_pos_left (by linarith) hR0
          _ ≤ ρ := by linarith
      have e1 : (V'.weight (closedBall 0 1)).toReal / ω =
          (V.weight (closedBall 0 R)).toReal / (ω * R ^ n) := by
        rw [hballR, smul_zero, mul_one]
        field_simp
      have e2 : (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n) =
          (V.weight (closedBall 0 (R * l))).toReal / (ω * (R * l) ^ n) := by
        rw [hballR, smul_zero, mul_pow]
        field_simp
      obtain ⟨a1, a2⟩ := hratio R hR0 hRρ
      obtain ⟨b1, b2⟩ := hratio (R * l) (by positivity) hRl
      have habs : |(V'.weight (closedBall 0 1)).toReal / ω -
          (V'.weight (closedBall 0 l)).toReal / (ω * l ^ n)| ≤ Up δ - Lo δ := by
        rw [e1, e2, abs_le]
        constructor <;> linarith
      /- The curvature term, transported back to `V`. -/
      obtain ⟨hfinH, hbH⟩ := hHbound (R * r) (by positivity) hRr
      have hlint : ∫⁻ x in closedBall (0 : Amb n ℓ) r, ENNReal.ofReal ‖R • H (0 + R • x)‖
          ∂V'.weight ≤ (ENNReal.ofReal (R ^ n))⁻¹ *
            (ENNReal.ofReal R * ∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight) := by
        rw [hW, Measure.restrict_smul, lintegral_smul_measure,
          Measure.restrict_map hmeasg measurableSet_closedBall, hpre, smul_zero, smul_eq_mul]
        gcongr
        refine (lintegral_map_le _ hmeasg.aemeasurable).trans (le_of_eq ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        simp only [sub_zero, zero_add, smul_inv_smul₀ hR0.ne', ofReal_norm, enorm_smul,
          Real.enorm_eq_ofReal hR0.le]
      have hne : (ENNReal.ofReal (R ^ n))⁻¹ *
          (ENNReal.ofReal R * ∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight) ≠ ⊤ :=
        ENNReal.mul_ne_top hinvne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinH)
      have hint : ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
          (R ^ n)⁻¹ * (R * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal) := by
        have h1 := norm_integral_le_lintegral_norm (μ := V'.weight.restrict (closedBall 0 r))
          (fun x => ‖R • H (0 + R • x)‖)
        simp only [norm_norm] at h1
        refine (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ h1).trans ?_)
        have h2 := ENNReal.toReal_mono hne hlint
        rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hR0.le] at h2
      have hscale : r ^ (1 - (n : ℝ)) *
          ((R ^ n)⁻¹ * (R * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal)) =
          (R * r) ^ (1 - (n : ℝ)) * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal := by
        rw [Real.mul_rpow hR0.le hr0.le, Real.rpow_sub hR0, Real.rpow_one, Real.rpow_natCast]
        field_simp
      have hHr : r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖
          ∂V'.weight ≤ KH * δ := by
        calc r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight
            ≤ r ^ (1 - (n : ℝ)) *
                ((R ^ n)⁻¹ * (R * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal)) := by
              gcongr
          _ = (R * r) ^ (1 - (n : ℝ)) * (∫⁻ z in closedBall 0 (R * r), ‖H z‖ₑ ∂V.weight).toReal :=
              hscale
          _ ≤ KH * δ := hbH
      calc _ ≤ (Up δ - Lo δ) + KH * δ := add_le_add habs hHr
        _ = l := (hlam δ).symm
    /- Theorem 6.1 with `λ = δ̃ = l`, `θ = θ₀`, `ξ = y/R`, `ρ = θ₀`, `τ = 2l`. -/
    obtain ⟨hconc, -⟩ := hC₉ l θ₀ l hl0 c4 hθ₀0 (by linarith) hl0 c4 (R⁻¹ • y) hξ _ hU'open hB1 V'
      _ hH' hpinch hmass' θ₀ ⟨hθ₀0, le_rfl⟩ (2 * l) ⟨le_rfl, by linarith⟩
    rw [← hqq δ] at hconc
    /- Back to `V`. -/
    have hRξ : R • (R⁻¹ • y) = y := smul_inv_smul₀ hR0.ne' y
    have hRτξ : R • ((2 * l) • (R⁻¹ • y)) = (2 * l) • y := by
      rw [smul_comm, smul_inv_smul₀ hR0.ne']
    have hτy : ‖(2 * l) • y‖ ≤ 2 * l * ρ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hyρ (by positivity)
    have h2lρ : 2 * l * ρ ≤ 1 / 2 * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
    have hsub2 : closedBall ((2 * l) • y) (ρ / 2) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right]
      linarith
    have hs2 : 0 < R * ((2 * l) * θ₀) := by positivity
    have hs2le : R * ((2 * l) * θ₀) ≤ ρ / 2 := by
      have : (2 * l) * θ₀ ≤ 1 / 2 := by
        calc (2 * l) * θ₀ ≤ 1 / 2 * 1 :=
              mul_le_mul (by linarith) (by linarith) hθ₀0.le (by norm_num)
          _ = 1 / 2 := by norm_num
      calc R * ((2 * l) * θ₀) ≤ ρ * (1 / 2) := mul_le_mul hRρ.le this (by positivity) hρ.le
        _ = ρ / 2 := by ring
    have hconcR : (R ^ n)⁻¹ * (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal ≤
        ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ *
          (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal) +
        max C₉ 0 * (qq δ * |Real.log l|) := by
      have hfin2 : V'.weight (closedBall ((2 * l) • (R⁻¹ • y)) ((2 * l) * θ₀)) ≠ ⊤ := by
        apply hballfin
        rw [hRτξ]
        exact (closedBall_subset_closedBall hs2le).trans hsub2
      have hne : ENNReal.ofReal ((2 * l) ^ n)⁻¹ *
          V'.weight (closedBall ((2 * l) • (R⁻¹ • y)) ((2 * l) * θ₀)) +
          ENNReal.ofReal (C₉ * qq δ * |Real.log l|) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2,
          ENNReal.ofReal_ne_top⟩
      have h := ENNReal.toReal_mono hne hconc
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2) ENNReal.ofReal_ne_top,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal',
        hballR, hballR, hRξ, hRτξ] at h
      refine h.trans (add_le_add le_rfl ?_)
      apply max_le
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · have : 0 ≤ max C₉ 0 := le_max_right _ _
        positivity
    /- The comparison ball `B_{2lθ₀R}(2l y)`. -/
    have hm3 : (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal / (ρ / 2) ^ n ≤
        Up δ * ω * (1 + 4 * l) ^ n := by
      have hsub3 : closedBall ((2 * l) • y) (ρ / 2) ⊆ closedBall 0 (ρ / 2 + 2 * l * ρ) := by
        apply closedBall_subset_closedBall'
        rw [dist_zero_right]
        linarith
      have h1 : (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal ≤
          Up δ * ω * (ρ / 2 + 2 * l * ρ) ^ n :=
        (ENNReal.toReal_mono (hfin 0 _ (closedBall_subset_closedBall (by linarith)))
          (measure_mono hsub3)).trans (hup _ (by positivity) (by linarith))
      rw [div_le_iff₀ (by positivity)]
      calc (V.weight (closedBall ((2 * l) • y) (ρ / 2))).toReal
          ≤ Up δ * ω * (ρ / 2 + 2 * l * ρ) ^ n := h1
        _ = Up δ * ω * (1 + 4 * l) ^ n * (ρ / 2) ^ n := by
            rw [show ρ / 2 + 2 * l * ρ = (1 + 4 * l) * (ρ / 2) by ring, mul_pow]
            ring
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ea δ * (Up δ * ω * (1 + 4 * l) ^ n) + eb δ := ⟨_, rfl⟩
    have hm2 : (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal ≤
        (R * ((2 * l) * θ₀)) ^ n * X := by
      have h1 := M1' ((2 * l) • y) (ρ / 2) (R * ((2 * l) * θ₀)) hs2 hs2le hsub2
      have h2 : (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal /
          (R * ((2 * l) * θ₀)) ^ n ≤ X := by
        rw [hX]
        exact h1.trans (by gcongr)
      rw [div_le_iff₀ (by positivity)] at h2
      linarith
    have hm1 : (R ^ n)⁻¹ * (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal ≤
        θ₀ ^ n * X + max C₉ 0 * (qq δ * |Real.log l|) := by
      refine hconcR.trans (add_le_add ?_ le_rfl)
      calc ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ *
            (V.weight (closedBall ((2 * l) • y) (R * ((2 * l) * θ₀)))).toReal)
          ≤ ((2 * l) ^ n)⁻¹ * ((R ^ n)⁻¹ * ((R * ((2 * l) * θ₀)) ^ n * X)) := by gcongr
        _ = θ₀ ^ n * X := by
            rw [mul_pow, mul_pow]
            field_simp
            ring
    /- Pinching at `y` on the scale `r_y = (1 - δ̃^{1/4}) θ₀ R`. -/
    have hq2 : 0 < 1 - qq δ := by linarith
    have hry : 0 < R * ((1 - qq δ) * θ₀) := by positivity
    have hm1' : (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal /
        (R * ((1 - qq δ) * θ₀)) ^ n ≤
        ((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n) := by
      rw [div_le_iff₀ (by positivity)]
      have h := (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < R ^ n)).mp hm1
      calc (V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal
          ≤ R ^ n * (θ₀ ^ n * X + max C₉ 0 * (qq δ * |Real.log l|)) := h
        _ = ((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n) *
            (R * ((1 - qq δ) * θ₀)) ^ n := by
            rw [mul_pow, mul_pow]
            field_simp
    have hsuby : closedBall y (R * ((1 - qq δ) * θ₀)) ⊆ closedBall 0 ρ := by
      apply closedBall_subset_closedBall'
      rw [dist_zero_right, hyR]
      have : R * ((1 - qq δ) * θ₀) ≤ R * θ₀ := by
        apply mul_le_mul_of_nonneg_left _ hR0.le
        exact mul_le_of_le_one_left hθ₀0.le (by linarith)
      linarith
    have hcsry : cs * ρ ≤ R * ((1 - qq δ) * θ₀) := by
      rw [hcs]
      have h1 : κ₀ * ρ * θ₀ ≤ R * θ₀ := mul_le_mul_of_nonneg_right hκR.le hθ₀0.le
      have h2 : R * θ₀ * (1 / 2) ≤ R * θ₀ * (1 - qq δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hfinal := M1' y (R * ((1 - qq δ) * θ₀)) (cs * ρ) (by positivity) hcsry hsuby
    calc (V.weight (closedBall y (cs * ρ))).toReal / (cs * ρ) ^ n
        ≤ ea δ * ((V.weight (closedBall y (R * ((1 - qq δ) * θ₀)))).toReal /
            (R * ((1 - qq δ) * θ₀)) ^ n) + eb δ := hfinal
      _ ≤ ea δ * (((1 - qq δ) ^ n)⁻¹ * (X + max C₉ 0 * (qq δ * |Real.log l|) / θ₀ ^ n)) +
            eb δ := by gcongr
      _ ≤ (1 + ε) * ω := by rw [hX]; exact c7

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
