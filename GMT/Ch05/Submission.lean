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

/-- **Dilation formula for lower integrals on `ℝⁿ`** (used in the boundary-layer estimate for the
Rellich compactness step in the proof of Simon Ch. 5, Lemma 3.1, p. 114).  For `t > 0`, every
`F : ℝⁿ → [0, ∞]` and every set `E ⊆ ℝⁿ` (neither assumed measurable),
`∫_E F(t x) dx = t^{-n} ∫_{tE} F(y) dy`, where `tE = {y : t⁻¹ y ∈ E}`.
Proof: `T x = t x` is a measurable equivalence with `T⁻¹(tE) = E`, and `T_# Lⁿ = t^{-n} Lⁿ`
(`Measure.map_addHaar_smul`, `finrank ℝ ℝⁿ = n`).  Change of variables along the measurable
embedding `T` needs no measurability of `F` or `E`. -/
theorem ble_sac_lintegral_comp_smul : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (E : Set (Rn n)) (t : ℝ), 0 < t → ∫⁻ x in E, F (t • x) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y := by
  intro n F E t ht
  -- `T x = t • x` as a measurable equivalence of `ℝⁿ`.
  let e : Rn n ≃ᵐ Rn n := (Homeomorph.smul (Units.mk0 t ht.ne')).toMeasurableEquiv
  have he : ∀ x, e x = t • x := fun x => rfl
  -- `T⁻¹(tE) = E`, since `t⁻¹ • (t • x) = x`.
  have hpre : e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E) = E := by
    ext x
    simp only [mem_preimage, he, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  -- `T_# Lⁿ = t^{-n} Lⁿ`.
  have hmap : Measure.map e volume = ENNReal.ofReal ((t ^ n)⁻¹) • (volume : Measure (Rn n)) := by
    have := Measure.map_addHaar_smul (volume : Measure (Rn n)) ht.ne'
    rw [finrank_euclideanSpace_fin] at this
    rw [show (e : Rn n → Rn n) = fun x => t • x from funext he, this]
    congr 2
    rw [abs_of_pos (by positivity)]
  -- Change variables along the measurable embedding `T`, then pull out the scalar.
  calc ∫⁻ x in E, F (t • x) = ∫⁻ x in e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E), F (e x) := by
        rw [hpre]; simp only [he]
    _ = ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y ∂(Measure.map e volume) := by
        rw [e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
    _ = _ := by rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
/-- **Pointwise ray inequality for `C¹` functions** (inequality (2.2) of the smooth annulus
estimate in the boundary-layer estimate for the Rellich compactness step in the proof of Simon
Ch. 5, Lemma 3.1, p. 114).  For `φ ∈ C¹(ℝⁿ)`, `|x| ≤ 1` and `τ ≤ 1`,
`(1 - τ) |φ(x)|² ≤ 2 ∫_τ^1 |φ(t x)|² dt + 2 (1 - τ)² ∫_τ^1 |∇φ(σ x)|² dσ`.
Proof: for `t ∈ [τ, 1]`, the fundamental theorem of calculus along the ray gives
`φ(x) - φ(t x) = ∫_t^1 ⟨∇φ(σ x), x⟩ dσ`, so `|x| ≤ 1` and Cauchy–Schwarz on `[τ, 1]` give
`|φ(x) - φ(t x)|² ≤ (1 - τ) ∫_τ^1 |∇φ(σ x)|² dσ`.  Then `(a + b)² ≤ 2a² + 2b²`, and integrate
over `t ∈ [τ, 1]`, a set of length `1 - τ`. -/
theorem ble_sac_ray_sq_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (x : Rn n), ‖x‖ ≤ 1 → ∀ τ : ℝ, τ ≤ 1 → ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 ≤ 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) + 2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
  intro n φ hφ x hx τ hτ
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- `d/dσ φ(σ x) = ⟨∇φ(σ x), x⟩`.
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => φ (σ • x)) (inner ℝ (gradient φ (σ • x)) x) σ := by
    intro σ
    have h1 : HasFDerivAt φ (fderiv ℝ φ (σ • x)) (σ • x) := (hdiff (σ • x)).hasFDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => σ • x) x σ := by
      simpa using (hasDerivAt_id σ).smul_const x
    have h3 := h1.comp_hasDerivAt σ h2
    rw [inner_gradient_left]
    exact h3
  have hray : Continuous (fun σ : ℝ => σ • x) := continuous_id.smul continuous_const
  have hcont_inner : Continuous (fun σ : ℝ => inner ℝ (gradient φ (σ • x)) x) :=
    (hgc.comp hray).inner continuous_const
  set G : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 with hG_def
  set m : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ with hm_def
  -- Cauchy–Schwarz on `[τ, 1]`: `m² ≤ (1 - τ) G`.
  have hcs : m ^ 2 ≤ ENNReal.ofReal (1 - τ) * G := by
    have hmeas : AEMeasurable (fun σ : ℝ => ‖gradient φ (σ • x)‖ₑ) (volume.restrict (Icc τ 1)) :=
      (hgc.comp hray).enorm.aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc τ 1))
      Real.HolderConjugate.two_two (aemeasurable_const (b := (1 : ℝ≥0∞))) hmeas
    simp only [Pi.mul_apply, one_mul, setLIntegral_const, Real.volume_Icc,
      ENNReal.rpow_two, one_pow] at h
    calc m ^ 2 ≤ ((ENNReal.ofReal (1 - τ)) ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (1 - τ) * G := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
  -- `(p + q)² ≤ 2p² + 2q²` in `[0, ∞]`.
  have hsq : ∀ p q : ℝ≥0∞, (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
    intro p q
    rcases eq_or_ne p ⊤ with hp | hp
    · simp [hp]
    rcases eq_or_ne q ⊤ with hq | hq
    · simp [hq]
    lift p to ℝ≥0 using hp
    lift q to ℝ≥0 using hq
    have h := add_sq_le (a := p) (b := q)
    rw [mul_add] at h
    exact_mod_cast h
  -- Pointwise inequality (2.1) for `t ∈ [τ, 1]`.
  have hpt : ∀ t ∈ Icc τ 1, ‖φ x‖ₑ ^ 2 ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G) := by
    intro t ht
    have hftc : ∫ σ in t..1, inner ℝ (gradient φ (σ • x)) x = φ x - φ (t • x) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
        (hcont_inner.intervalIntegrable t 1)]
      simp
    have hb : ‖φ x - φ (t • x)‖ₑ ≤ m := by
      rw [← hftc, intervalIntegral.integral_of_le ht.2]
      calc ‖∫ σ in Ioc t 1, inner ℝ (gradient φ (σ • x)) x‖ₑ
            ≤ ∫⁻ σ in Ioc t 1, ‖inner ℝ (gradient φ (σ • x)) x‖ₑ :=
              enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ σ in Ioc t 1, ‖gradient φ (σ • x)‖ₑ := by
            apply lintegral_mono
            intro σ
            rw [enorm_le_iff_norm_le]
            calc ‖inner ℝ (gradient φ (σ • x)) x‖ ≤ ‖gradient φ (σ • x)‖ * ‖x‖ :=
                  norm_inner_le_norm _ _
              _ ≤ ‖gradient φ (σ • x)‖ * 1 := by gcongr
              _ = _ := mul_one _
        _ ≤ m := lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1 le_rfl))
    have htri : ‖φ x‖ₑ ≤ ‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ := by
      calc ‖φ x‖ₑ = ‖φ (t • x) + (φ x - φ (t • x))‖ₑ := by ring_nf
        _ ≤ _ := enorm_add_le _ _
    calc ‖φ x‖ₑ ^ 2 ≤ (‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ) ^ 2 := by gcongr
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * ‖φ x - φ (t • x)‖ₑ ^ 2 := hsq _ _
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * m ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  -- Integrate (2.1) over `t ∈ [τ, 1]`.
  calc ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 = ∫⁻ t in Icc τ 1, ‖φ x‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
    _ ≤ ∫⁻ t in Icc τ 1, (2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (1 - τ) * G) * ENNReal.ofReal (1 - τ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
          setLIntegral_const, Real.volume_Icc]
    _ = _ := by
        rw [ENNReal.ofReal_pow (by linarith)]
        ring
/-- **Averaged dilation over an annulus** (function term and kernel bound of the boundary-layer
estimate in the proof of Simon Ch. 5, Lemma 3.1, p. 114).  For measurable `F : ℝⁿ → [0, ∞]`,
`1/2 ≤ r < 1`, `s > 0`, `τ ≥ 1/2` and the annulus `A = B̆_s(0) \ B̆_{rs}(0)`,
`∫_{[τ,1]} ∫_A F(t x) dx dt ≤ 2^{n+1} (1 - r) ∫_{B̆_s(0)} F(y) dy`.
Proof: the dilation formula turns the inner integral into `∫ F(y) K(y, t) dy` with
`K(y, t) = t^{-n} 1_S(y, t)`, `S = {(y, t) : r s t ≤ |y| < s t}`; by Tonelli the left side is
`∫ F(y) k(y) dy` with `k(y) = ∫_{[τ,1]} K(y, t) dt`, and `k ≤ 2^{n+1} (1 - r) 1_{B̆_s(0)}`, since
`k` vanishes off `B̆_s(0)`, `t^{-n} ≤ 2^n`, and `K(y, ·)` is supported in
`(|y|/s, |y|/(r s)]`, an interval of length at most `2 (1 - r)`. -/
theorem ble_sac_annulus_dilation_avg_le : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞), Measurable F → ∀ r s τ : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → 1 / 2 ≤ τ → ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) ≤ ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, F y := by
  intro n F hF r s τ hr1 hr2 hs hτ
  have hr0 : 0 < r := by linarith
  -- Step 1: the kernel set `S` and the measurable weight `K(y, t) = t^{-n} 1_S(y, t)`.
  set S : Set (Rn n × ℝ) := {p | r * s * p.2 ≤ ‖p.1‖ ∧ ‖p.1‖ < s * p.2} with hS_def
  have hSm : MeasurableSet S := by
    have h1 : Measurable fun p : Rn n × ℝ => r * s * p.2 := measurable_const.mul measurable_snd
    have h2 : Measurable fun p : Rn n × ℝ => ‖p.1‖ := measurable_fst.norm
    have h3 : Measurable fun p : Rn n × ℝ => s * p.2 := measurable_const.mul measurable_snd
    exact (measurableSet_le h1 h2).inter (measurableSet_lt h2 h3)
  set K : Rn n × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((p.2 ^ n)⁻¹) * S.indicator 1 p with hK_def
  have hKm : Measurable K :=
    (ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const n).inv)).mul
      (measurable_one.indicator hSm)
  -- Step 2: for fixed `t ∈ [τ, 1]`, the dilation formula gives `∫_A F(t x) dx = ∫ F(y) K(y, t) dy`,
  -- because `t⁻¹ y ∈ A ↔ (y, t) ∈ S`.
  have step1 : ∀ t ∈ Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) =
      ∫⁻ y, F y * K (y, t) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [Submission.ble_sac_lintegral_comp_smul n F _ t ht0]
    have hpre : (fun y => t⁻¹ • y) ⁻¹' (ball (0 : Rn n) s \ ball 0 (r * s)) =
        {y | (y, t) ∈ S} := by
      ext y
      simp only [mem_preimage, Set.mem_sdiff, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos ht0, not_lt, Set.mem_ofPred_eq, hS_def]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · rw [le_inv_mul_iff₀ ht0] at h2; linarith
        · rw [inv_mul_lt_iff₀ ht0] at h1; linarith
      · rintro ⟨h1, h2⟩
        constructor
        · rw [inv_mul_lt_iff₀ ht0]; linarith
        · rw [le_inv_mul_iff₀ ht0]; linarith
    have hSt : MeasurableSet {y : Rn n | (y, t) ∈ S} := measurable_prodMk_right hSm
    rw [hpre, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hSt]
    congr 1
    funext y
    by_cases hy : (y, t) ∈ S
    · rw [indicator_of_mem (show y ∈ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_mem hy, Pi.one_apply, mul_one]
      ring
    · rw [indicator_of_notMem (show y ∉ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_notMem hy, mul_zero]
  -- Step 4: the kernel bound `k(y) = ∫_{[τ,1]} K(y, t) dt ≤ 2^{n+1} (1 - r) 1_{B̆_s(0)}(y)`.
  have kernel : ∀ y : Rn n, ∫⁻ t in Icc τ 1, K (y, t) ≤
      (ball (0 : Rn n) s).indicator (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y := by
    intro y
    by_cases hy : y ∈ ball (0 : Rn n) s
    · rw [indicator_of_mem hy]
      rw [mem_ball_zero_iff] at hy
      -- For `|y| < s`: `K(y, t) ≤ 2^n 1_{(|y|/s, |y|/(r s)]}(t)` for `t ∈ [τ, 1]`.
      have hbound : ∀ t ∈ Icc τ 1, K (y, t) ≤
          (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t := by
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        by_cases hS : (y, t) ∈ S
        · have hmem : t ∈ Ioc (‖y‖ / s) (‖y‖ / (r * s)) := by
            constructor
            · rw [div_lt_iff₀ hs]; linarith [hS.2]
            · rw [le_div_iff₀ (by positivity)]; linarith [hS.1]
          rw [indicator_of_mem hmem]
          simp only [hK_def, indicator_of_mem hS, Pi.one_apply, mul_one]
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [inv_le_comm₀ ht0 (by norm_num)]
          linarith [ht.1]
        · simp [hK_def, indicator_of_notMem hS]
      -- The support interval has length `|y| (1 - r) / (r s) ≤ 2 (1 - r)`.
      have hlen : ‖y‖ / (r * s) - ‖y‖ / s ≤ 2 * (1 - r) := by
        rw [show ‖y‖ / (r * s) - ‖y‖ / s = ‖y‖ * (1 - r) / (r * s) by field_simp]
        rw [div_le_iff₀ (by positivity)]
        have h1 : ‖y‖ * (1 - r) ≤ s * (1 - r) := mul_le_mul_of_nonneg_right hy.le (by linarith)
        have h2 : s * (1 - r) ≤ 2 * (1 - r) * (r * s) := by
          nlinarith [mul_nonneg (mul_nonneg hs.le (by linarith : (0:ℝ) ≤ 1 - r))
            (by linarith : (0:ℝ) ≤ 2 * r - 1)]
        linarith
      calc ∫⁻ t in Icc τ 1, K (y, t)
            ≤ ∫⁻ t in Icc τ 1, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator
                (fun _ => ENNReal.ofReal (2 ^ n)) t := setLIntegral_mono' measurableSet_Icc hbound
        _ ≤ ∫⁻ t, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (‖y‖ / (r * s) - ‖y‖ / s) := by
            rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
        _ ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (2 * (1 - r)) := by
            gcongr
        _ = ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    · -- For `|y| ≥ s`: `s t ≤ s ≤ |y|`, so `(y, t) ∉ S` and `k(y) = 0`.
      rw [indicator_of_notMem hy]
      have hz : ∀ t ∈ Icc τ 1, K (y, t) = 0 := by
        intro t ht
        have hS : (y, t) ∉ S := by
          rintro ⟨_, h2⟩
          rw [mem_ball_zero_iff, not_lt] at hy
          nlinarith [ht.2]
        simp only [hK_def, indicator_of_notMem hS, mul_zero]
      rw [setLIntegral_congr_fun measurableSet_Icc hz, lintegral_zero]
  -- Steps 3 and 5: Tonelli, then integrate the kernel bound against `F`.
  have hmeas : AEMeasurable (Function.uncurry fun (t : ℝ) (y : Rn n) => F y * K (y, t))
      ((volume.restrict (Icc τ 1)).prod volume) :=
    ((hF.comp measurable_snd).mul (hKm.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
  calc ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x)
        = ∫⁻ t in Icc τ 1, ∫⁻ y, F y * K (y, t) := setLIntegral_congr_fun measurableSet_Icc step1
    _ = ∫⁻ y, ∫⁻ t in Icc τ 1, F y * K (y, t) := lintegral_lintegral_swap hmeas
    _ = ∫⁻ y, F y * ∫⁻ t in Icc τ 1, K (y, t) := by
        congr 1
        funext y
        exact lintegral_const_mul _ (hKm.comp measurable_prodMk_left)
    _ ≤ ∫⁻ y, F y * (ball (0 : Rn n) s).indicator
          (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y :=
        lintegral_mono (fun y => by gcongr; exact kernel y)
    _ = ∫⁻ y in ball (0 : Rn n) s, F y * ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1
        funext y
        by_cases hy : y ∈ ball (0 : Rn n) s
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy]
    _ = _ := by rw [lintegral_mul_const _ hF, mul_comm]
/-- **Smooth annulus estimate** (the smooth step of the boundary-layer estimate for `W^{1,2}` on
balls).  Let `n ≥ 1`, `φ ∈ C¹(ℝⁿ)`, `1/2 ≤ r < 1`, `0 < s ≤ 1`, `a := √(1 - r)` and
`A := B̆_s(0) \ B̆_{rs}(0)`.  Then `∫_A |φ|² ≤ 2^{n+3} a (∫_{B̆_s(0)} |φ|² + ∫_{B̆_s(0)} |∇φ|²)`
(lintegrals of squared extended norms).  With `τ := 1 - a/2 ∈ [1/2, 1)`, integrate the ray
inequality `ble_sac_ray_sq_bound` over `A` and swap the order of integration (Tonelli).  The
dilation formula `ble_sac_lintegral_comp_smul`, with `σA ⊆ B̆_s(0)` and `σ⁻ⁿ ≤ 2ⁿ` for
`σ ∈ [τ, 1]`, bounds the gradient term by `2ⁿ (1 - τ) ∫_{B̆_s(0)} |∇φ|²`; the kernel bound
`ble_sac_annulus_dilation_avg_le` bounds the function term by `2^{n+1} (1 - r) ∫_{B̆_s(0)} |φ|²`.
Dividing by `1 - τ = a/2` and using `1 - r = a²`, `a ≤ 1` gives the constant `2^{n+3} a`. -/
theorem ble_smooth_annulus_estimate : ∀ n : ℕ, 1 ≤ n → ∀ (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ r s : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → s ≤ 1 → ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (2 ^ (n + 3) * Real.sqrt (1 - r)) * ((∫⁻ x in ball (0 : Rn n) s, ‖φ x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) s, ‖gradient φ x‖ₑ ^ 2) := by
  intro n _ φ hφ r s hr1 hr2 hs0 hs1
  -- Step 0: `a := √(1 - r) ∈ (0, 1]` with `a² = 1 - r`, and `τ := 1 - a/2 ∈ [1/2, 1]`.
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = Real.sqrt (1 - r) := ⟨_, rfl⟩
  rw [← ha_def]
  have ha0 : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.2 (by linarith)
  have ha1 : a ≤ 1 := by
    rw [ha_def]
    calc Real.sqrt (1 - r) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have ha2 : a ^ 2 = 1 - r := by rw [ha_def]; exact Real.sq_sqrt (by linarith)
  obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = 1 - a / 2 := ⟨_, rfl⟩
  have hτ1 : τ ≤ 1 := by rw [hτ_def]; linarith
  have hτ2 : 1 / 2 ≤ τ := by rw [hτ_def]; linarith
  have h1τ : 1 - τ = a / 2 := by rw [hτ_def]; ring
  set A := ball (0 : Rn n) s \ ball 0 (r * s)
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hA1 : ∀ x ∈ A, ‖x‖ ≤ 1 := fun x hx => by
    have h := mem_ball_zero_iff.1 hx.1
    linarith
  -- `φ` and `∇φ = (toDual ℝ ℝⁿ)⁻¹ ∘ Dφ` are continuous; measurability for Tonelli.
  have hφc : Continuous φ := hφ.continuous
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hFm : Measurable (fun y : Rn n => ‖φ y‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp hφc.enorm).measurable
  have hH1 : Measurable (fun p : Rn n × ℝ => ‖φ (p.2 • p.1)‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp
      (hφc.comp (continuous_snd.smul continuous_fst)).enorm).measurable
  have hH2 : Measurable (fun p : Rn n × ℝ => ‖gradient φ (p.2 • p.1)‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp
      (hgc.comp (continuous_snd.smul continuous_fst)).enorm).measurable
  have hP : Measurable (fun x : Rn n => ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) :=
    hH1.lintegral_prod_right'
  have hQ : Measurable (fun x : Rn n => ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2) :=
    hH2.lintegral_prod_right'
  -- Step 3: integrate the ray inequality over `A` (where `‖x‖ < s ≤ 1`), then swap integrals.
  have h3 : ENNReal.ofReal (1 - τ) * ∫⁻ x in A, ‖φ x‖ₑ ^ 2 ≤
      2 * (∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2) +
        2 * ENNReal.ofReal ((1 - τ) ^ 2) *
          ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
    have hs1 : ∫⁻ x in A, ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2 =
        ∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2 :=
      lintegral_lintegral_swap hH1.aemeasurable
    have hs2 : ∫⁻ x in A, ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 =
        ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 :=
      lintegral_lintegral_swap hH2.aemeasurable
    calc ENNReal.ofReal (1 - τ) * ∫⁻ x in A, ‖φ x‖ₑ ^ 2
          = ∫⁻ x in A, ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 :=
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x in A, (2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
            2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2) :=
            setLIntegral_mono' hA fun x hx =>
              Submission.ble_sac_ray_sq_bound n φ hφ x (hA1 x hx) τ hτ1
      _ = 2 * (∫⁻ x in A, ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
            2 * ENNReal.ofReal ((1 - τ) ^ 2) *
              ∫⁻ x in A, ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
          rw [lintegral_add_left (hP.const_mul 2), lintegral_const_mul _ hP,
            lintegral_const_mul _ hQ]
      _ = _ := by rw [hs1, hs2]
  -- Step 4: gradient term.  For `σ ∈ [τ, 1]`, `∫_A |∇φ(σx)|² dx ≤ 2ⁿ ∫_{B̆_s(0)} |∇φ|²` by the
  -- dilation formula, `σ⁻ⁿ ≤ 2ⁿ` and `σA ⊆ B̆_s(0)`; then integrate over `σ ∈ [τ, 1]`.
  have h4 : ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ n * (1 - τ)) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 := by
    have hJ : ∀ σ ∈ Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 ^ n) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 := by
      intro σ hσ
      have hσ0 : 0 < σ := by linarith [hσ.1]
      rw [Submission.ble_sac_lintegral_comp_smul n (fun y => ‖gradient φ y‖ₑ ^ 2) A σ hσ0]
      gcongr ?_ * ?_
      · apply ENNReal.ofReal_le_ofReal
        rw [← inv_pow]
        apply pow_le_pow_left₀ (by positivity)
        rw [inv_le_comm₀ hσ0 (by norm_num)]
        linarith [hσ.1]
      · apply lintegral_mono_set
        intro y hy
        rw [Set.mem_preimage] at hy
        have h1 := mem_ball_zero_iff.1 hy.1
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hσ0] at h1
        rw [mem_ball_zero_iff]
        calc ‖y‖ = σ * (σ⁻¹ * ‖y‖) := by rw [← mul_assoc, mul_inv_cancel₀ hσ0.ne', one_mul]
          _ < σ * s := by gcongr
          _ ≤ s := by nlinarith [hσ.2]
    calc ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2
          ≤ ∫⁻ σ in Icc τ 1,
              ENNReal.ofReal (2 ^ n) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 :=
            setLIntegral_mono measurable_const hJ
      _ = _ := by
          rw [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_mul (by positivity)]
          ring
  -- Step 5: function term, by the kernel bound.
  have h5 : ∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, ‖φ y‖ₑ ^ 2 :=
    Submission.ble_sac_annulus_dilation_avg_le n (fun y => ‖φ y‖ₑ ^ 2) hFm r s τ hr1 hr2 hs0 hτ2
  -- Step 6: combine, cancel the finite nonzero factor `1 - τ = a/2`, and compare coefficients
  -- using `1 - r = a²` and `a ≤ 1`.
  set X := ∫⁻ x in A, ‖φ x‖ₑ ^ 2
  set P := ∫⁻ y in ball (0 : Rn n) s, ‖φ y‖ₑ ^ 2
  set G := ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2
  have key : ENNReal.ofReal (a / 2) * X ≤
      2 * (ENNReal.ofReal (2 ^ (n + 1) * a ^ 2) * P) +
        2 * ENNReal.ofReal ((a / 2) ^ 2) * (ENNReal.ofReal (2 ^ n * (a / 2)) * G) := by
    rw [← h1τ, ha2]
    refine h3.trans ?_
    gcongr
  have hb0 : ENNReal.ofReal (a / 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  refine (ENNReal.mul_le_mul_iff_right hb0 ENNReal.ofReal_ne_top).1 (key.trans ?_)
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  have e1 : (2 : ℝ≥0∞) * (ENNReal.ofReal (2 ^ (n + 1) * a ^ 2) * P) =
      ENNReal.ofReal (2 * (2 ^ (n + 1) * a ^ 2)) * P := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← h2, mul_assoc]
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((a / 2) ^ 2) * (ENNReal.ofReal (2 ^ n * (a / 2)) * G) =
      ENNReal.ofReal (2 * (a / 2) ^ 2 * (2 ^ n * (a / 2))) * G := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (a / 2) ^ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← h2]
    ring
  have e3 : ENNReal.ofReal (a / 2) * (ENNReal.ofReal (2 ^ (n + 3) * a) * (P + G)) =
      ENNReal.ofReal (a / 2 * (2 ^ (n + 3) * a)) * P +
        ENNReal.ofReal (a / 2 * (2 ^ (n + 3) * a)) * G := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a / 2)]
    ring
  rw [e1, e2, e3]
  -- `2 · 2^{n+1} a² = (a/2) · 2^{n+3} a` and `2 (a/2)² · 2ⁿ (a/2) = 2ⁿ a² (a/4) ≤ 2ⁿ a² · 4`.
  have c1 : 2 * (2 ^ (n + 1) * a ^ 2) ≤ a / 2 * (2 ^ (n + 3) * a) := le_of_eq (by ring)
  have c2 : 2 * (a / 2) ^ 2 * (2 ^ n * (a / 2)) ≤ a / 2 * (2 ^ (n + 3) * a) := by
    have k1 : 2 * (a / 2) ^ 2 * (2 ^ n * (a / 2)) = 2 ^ n * a ^ 2 * (a / 4) := by ring
    have k2 : a / 2 * (2 ^ (n + 3) * a) = 2 ^ n * a ^ 2 * 4 := by ring
    rw [k1, k2]
    have h0 : (0 : ℝ) ≤ 2 ^ n * a ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 4 - a / 4)]
  exact add_le_add (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal c1) (by positivity))
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal c2) (by positivity))

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
