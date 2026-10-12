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

/-- **Simon Ch. 4, 3.1–3.3 with 3.14 and 4.1** (first variation of the radial cutoff field).  Let
`V` have generalized mean curvature `H` in `U`, with `x ↦ p_{T_x M}` `μ_V`-a.e. strongly measurable
and `p_{T_x M}` the projection onto an `n`-plane for `μ_V`-a.e. `x`.  Let `σ > 0`, `φ ∈ C¹(ℝ)` with
`φ = 1` on `[0, 1]` and `φ = 0` on `[b, ∞)`, and `B_{bσ}(ξ) ⊆ U`.  Testing 3.14 with
`X(x) = φ(r/σ)(x − ξ)`, `r = |x − ξ|`, gives
`∫ (n φ(r/σ) + (r/σ) φ'(r/σ)) dμ_V − ∫ (r/σ) φ'(r/σ) |(x − ξ) − p_{T_x M}(x − ξ)|²/r² dμ_V
  = −∫ φ(r/σ) (x − ξ) · H dμ_V` (the quotient is `0` at `x = ξ`). -/
theorem radial_cutoff_first_variation_eq : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (σ b : ℝ) (φ : ℝ → ℝ), 0 < σ → ContDiff ℝ 1 φ → (∀ t ∈ Icc (0 : ℝ) 1, φ t = 1) → (∀ t, b ≤ t → φ t = 0) → closedBall ξ (b * σ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) ∂V.weight - ∫ x, ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) * (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight = -∫ x, φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) ∂V.weight := by
  intro n ℓ U V H hH hG2 hG1 ξ σ b φ hσ hφ hφ1 hφ0 hball
  -- Step 1: `b > 1`
  have hb : 1 < b := by
    by_contra hb
    have hb' : b ≤ 1 := le_of_not_gt hb
    have h1 := hφ1 (max b 0) ⟨le_max_right _ _, max_le hb' zero_le_one⟩
    have h0 := hφ0 (max b 0) (le_max_left _ _)
    rw [h1] at h0
    exact one_ne_zero h0
  have hbσ : 0 < b * σ := mul_pos (by linarith) hσ
  -- Step 2: finiteness of the weight on `K = B_{bσ}(ξ)`
  have hKfin : V.weight (closedBall ξ (b * σ)) < ∞ := by
    have hint := V.integrableOn_mult _ (isCompact_closedBall ξ (b * σ)) hball
    rw [RectifiableVarifold.weight, withDensity_apply _ isClosed_closedBall.measurableSet,
      Measure.restrict_restrict isClosed_closedBall.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  -- the squared-radius profile `η(t) = φ(√t / σ)`
  set η : ℝ → ℝ := fun t => φ (Real.sqrt t / σ) with hη_def
  have hη_one : ∀ t, t < σ ^ 2 → η t = 1 := by
    intro t ht
    apply hφ1
    constructor
    · exact div_nonneg (Real.sqrt_nonneg _) hσ.le
    · rw [div_le_one₀ hσ]
      calc Real.sqrt t ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt ht.le
        _ = σ := Real.sqrt_sq hσ.le
  have hη_zero : ∀ t, (b * σ) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hφ0
    rw [le_div_iff₀ hσ]
    calc b * σ = Real.sqrt ((b * σ) ^ 2) := (Real.sqrt_sq hbσ.le).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hη_C1 : ContDiff ℝ 1 η := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge t (σ ^ 2) with ht | ht
    · have hev : η =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hη_one s hs
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have ht0 : t ≠ 0 := (lt_of_lt_of_le (pow_pos hσ 2) ht).ne'
      exact hφ.contDiffAt.comp t ((Real.contDiffAt_sqrt ht0).div_const σ)
  have hη_diff : Differentiable ℝ η := hη_C1.differentiable (by simp)
  have hη_sq : ∀ x : Amb n ℓ, η (‖x - ξ‖ ^ 2) = φ (‖x - ξ‖ / σ) := by
    intro x
    simp only [hη_def, Real.sqrt_sq (norm_nonneg _)]
  have hη_deriv : ∀ x : Amb n ℓ,
      2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 = ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) := by
    intro x
    rcases (norm_nonneg (x - ξ)).eq_or_lt with hr | hr
    · rw [← hr]; simp
    · have hr2 : ‖x - ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      have hd : HasDerivAt η (deriv φ (Real.sqrt (‖x - ξ‖ ^ 2) / σ) *
          (1 / (2 * Real.sqrt (‖x - ξ‖ ^ 2)) / σ)) (‖x - ξ‖ ^ 2) :=
        (hφ.differentiable (by simp) _).hasDerivAt.comp _ ((Real.hasDerivAt_sqrt hr2).div_const σ)
      rw [hd.deriv, Real.sqrt_sq (norm_nonneg _)]
      field_simp
  -- Step 3: the test field `X(x) = φ(|x - ξ|/σ) (x - ξ)`
  set X : Amb n ℓ → Amb n ℓ := fun x => η (‖x - ξ‖ ^ 2) • (x - ξ) with hX_def
  have hX_C1 : ContDiff ℝ 1 X := by
    have hsub : ContDiff ℝ 1 (fun x : Amb n ℓ ↦ x - ξ) := contDiff_id.sub contDiff_const
    exact (hη_C1.comp (hsub.norm_sq ℝ)).smul hsub
  have hX_ball : tsupport X ⊆ closedBall ξ (b * σ) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxb
    have hnorm : b * σ < ‖x - ξ‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hxb
    have hzero : η (‖x - ξ‖ ^ 2) = 0 :=
      hη_zero _ (by nlinarith [norm_nonneg (x - ξ)])
    exact hx (by simp [hX_def, hzero])
  have hX_cpt : HasCompactSupport X :=
    (isCompact_closedBall ξ (b * σ)).of_isClosed_subset (isClosed_tsupport _) hX_ball
  have hX_supp : tsupport X ⊆ U := hX_ball.trans hball
  have hFV := hH.2 X hX_C1 hX_cpt hX_supp
  have hrhs : ∀ x, inner ℝ (X x) (H x) = φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) := by
    intro x
    rw [← hη_sq x]
    exact real_inner_smul_left (x - ξ) (H x) (η (‖x - ξ‖ ^ 2))
  -- Step 4: derivative of `X`
  have hfd : ∀ x, fderiv ℝ X x = η (‖x - ξ‖ ^ 2) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
      (2 * deriv η (‖x - ξ‖ ^ 2)) • (innerSL ℝ (x - ξ)).smulRight (x - ξ) := by
    intro x
    have hsub : HasFDerivAt (fun y : Amb n ℓ ↦ y - ξ) (ContinuousLinearMap.id ℝ (Amb n ℓ)) x :=
      hasFDerivAt_sub_const ξ
    have hsq := hsub.norm_sq
    have hηComp := (hη_diff (‖x - ξ‖ ^ 2)).hasDerivAt.comp_hasFDerivAt x hsq
    have hX' : HasFDerivAt X (η (‖x - ξ‖ ^ 2) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (2 * deriv η (‖x - ξ‖ ^ 2)) • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x := by
      refine (hηComp.smul hsub).congr_fderiv ?_
      ext1 w
      simp [mul_smul]
      module
    exact hX'.fderiv
  -- trace of `(a • id + b • f.smulRight v) ∘ P` for an orthogonal projection `P`
  have htrace : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (f : Amb n ℓ →L[ℝ] ℝ) (v : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ)
        (((a • ContinuousLinearMap.id ℝ (Amb n ℓ)) + c • f.smulRight v).toLinearMap ∘ₗ
          P.starProjection.toLinearMap) =
        a * (Module.finrank ℝ P : ℝ) + c * f (P.starProjection v) := by
    intro P a c f v
    have htr : LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap =
        (Module.finrank ℝ P : ℝ) := by
      rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.trace_comp_comm']
      have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
          LinearMap.id := by
        ext x
        simp
      rw [hcomp, LinearMap.trace_id]
    change LinearMap.trace ℝ (Amb n ℓ)
        (((a • LinearMap.id) + c • f.toLinearMap.smulRight v).comp
          P.starProjection.toLinearMap) = _
    have hcomp :
        (((a • LinearMap.id) + c • f.toLinearMap.smulRight v).comp
            P.starProjection.toLinearMap) =
          a • P.starProjection.toLinearMap +
            c • (f.toLinearMap.comp P.starProjection.toLinearMap).smulRight v := by
      ext w
      simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htr]
    simp
  have hinner : ∀ (P : Submodule ℝ (Amb n ℓ)) (v : Amb n ℓ),
      inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
    intro P v
    rw [← P.inner_starProjection_left_eq_right v v]
    simpa using P.re_inner_starProjection_eq_normSq v
  -- Pythagoras
  have hpyth : ∀ (Q : Submodule ℝ (Amb n ℓ)) (w : Amb n ℓ),
      ‖w‖ ^ 2 = ‖Q.starProjection w‖ ^ 2 + ‖w - Q.starProjection w‖ ^ 2 := by
    intro Q w
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection w Q
  -- Steps 5-6: pointwise divergence
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x =
      ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) -
        ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) := by
    filter_upwards [hG1] with x hx
    obtain ⟨Q, hQn, hQ⟩ := hx
    rw [RectifiableVarifold.divM, hfd x, hQ, htrace,
      hQn, innerSL_apply_apply, hinner,
      hη_sq x, ← hη_deriv x]
    have hp := hpyth Q (x - ξ)
    have hkey : ‖x - ξ‖ ^ 2 * (‖(x - ξ) - Q.starProjection (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) =
        ‖(x - ξ) - Q.starProjection (x - ξ)‖ ^ 2 := by
      rcases eq_or_ne (x - ξ) 0 with h0 | h0
      · simp [h0]
      · exact mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
    linear_combination (-2 * deriv η (‖x - ξ‖ ^ 2)) * hp + (2 * deriv η (‖x - ξ‖ ^ 2)) * hkey
  -- Step 7: integrability
  have hout : ∀ x, x ∉ closedBall ξ (b * σ) → b < ‖x - ξ‖ / σ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hσ]
    exact hx
  have hφ_out : ∀ x, x ∉ closedBall ξ (b * σ) → φ (‖x - ξ‖ / σ) = 0 := fun x hx =>
    hφ0 _ (hout x hx).le
  have hφ'_out : ∀ x, x ∉ closedBall ξ (b * σ) → deriv φ (‖x - ξ‖ / σ) = 0 := by
    intro x hx
    have hzero : φ =ᶠ[𝓝 (‖x - ξ‖ / σ)] fun _ ↦ 0 := by
      filter_upwards [lt_mem_nhds (hout x hx)] with s hs
      exact hφ0 s hs.le
    exact hzero.deriv_eq.trans (deriv_const _ 0)
  have hint : ∀ f : Amb n ℓ → ℝ, AEStronglyMeasurable f V.weight →
      (∃ C, ∀ᵐ x ∂V.weight, ‖f x‖ ≤ C) → (∀ x, x ∉ closedBall ξ (b * σ) → f x = 0) →
      Integrable f V.weight := by
    intro f hf hC hzero
    obtain ⟨C, hC⟩ := hC
    have hon : IntegrableOn f (closedBall ξ (b * σ)) V.weight :=
      Measure.integrableOn_of_bounded hKfin.ne hf (ae_restrict_of_ae hC)
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
    intro x hx
    by_contra hxK
    exact hx (hzero x hxK)
  have hbound : ∀ f : Amb n ℓ → ℝ, Continuous f → (∀ x, x ∉ closedBall ξ (b * σ) → f x = 0) →
      ∃ C, ∀ x, ‖f x‖ ≤ C := by
    intro f hf hzero
    obtain ⟨C, hC⟩ := (isCompact_closedBall ξ (b * σ)).exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ closedBall ξ (b * σ)
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [hzero x hx, norm_zero]
      exact le_max_right _ _
  have hs_cont : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / σ) :=
    (continuous_id.sub continuous_const).norm.div_const σ
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hg_int : Integrable (fun x : Amb n ℓ =>
      (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) V.weight := by
    have hc : Continuous (fun x : Amb n ℓ =>
        (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) :=
      (continuous_const.mul (hφc.comp hs_cont)).add (hs_cont.mul (hφ'c.comp hs_cont))
    have hz : ∀ x, x ∉ closedBall ξ (b * σ) →
        (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) = 0 := by
      intro x hx
      rw [hφ_out x hx, hφ'_out x hx]
      ring
    obtain ⟨C, hC⟩ := hbound _ hc hz
    exact hint _ hc.aestronglyMeasurable ⟨C, Eventually.of_forall hC⟩ hz
  have hP_meas : AEStronglyMeasurable (fun x => V.tangentProj x (x - ξ)) V.weight :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hG2.prodMk (continuous_id.sub continuous_const).aestronglyMeasurable)
  have hq_meas : AEStronglyMeasurable
      (fun x => ‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) V.weight := by
    have h1 : AEMeasurable (fun x => (x - ξ) - V.tangentProj x (x - ξ)) V.weight :=
      (measurable_id.sub_const ξ).aemeasurable.sub hP_meas.aemeasurable
    exact ((h1.norm.pow_const 2).div
      ((measurable_id.sub_const ξ).norm.pow_const 2).aemeasurable).aestronglyMeasurable
  have hq_bound : ∀ᵐ x ∂V.weight,
      ‖‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2‖ ≤ 1 := by
    filter_upwards [hG1] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    rw [hQ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_one_of_le₀ _ (by positivity)
    have hp := hpyth Q (x - ξ)
    nlinarith [sq_nonneg ‖Q.starProjection (x - ξ)‖]
  have hh_int : Integrable (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
      (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2)) V.weight := by
    have hc : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) :=
      hs_cont.mul (hφ'c.comp hs_cont)
    have hz : ∀ x, x ∉ closedBall ξ (b * σ) → ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) = 0 := by
      intro x hx
      rw [hφ'_out x hx, mul_zero]
    obtain ⟨C, hC⟩ := hbound _ hc hz
    have hi : Integrable (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) V.weight :=
      hint _ hc.aestronglyMeasurable ⟨C, Eventually.of_forall hC⟩ hz
    exact hi.mul_bdd hq_meas hq_bound
  -- Step 8: conclusion
  rw [← integral_sub hg_int hh_int]
  calc ∫ x, ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) -
        ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight
      = ∫ x, V.divM X x ∂V.weight := (integral_congr_ae hdiv).symm
    _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hFV
    _ = -∫ x, φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) ∂V.weight := by
      rw [integral_congr_ae (Eventually.of_forall hrhs)]

/-- **Simon Ch. 4, 4.1–4.8** (`Lᵖ` monotonicity, with the corrected constant `κ = (p − n)/(4p)`).
Let `V` have generalized mean curvature `H` in `U`, with `x ↦ p_{T_x M}` `μ_V`-a.e. strongly
measurable and `p_{T_x M}` the projection onto an `n`-plane for `μ_V`-a.e. `x`, and let `p > n ≥ 1`.
If `B_R(ξ) ⊆ U` and `(R^{p−n} ∫_{B_R(ξ)} |H|ᵖ dμ_V)^{1/p} ≤ κ Λ` with `Λ ≥ 0`, then
`σ ↦ exp((Λ/2)(σ/R)^{1−n/p}) (σ⁻ⁿ μ_V(B_σ(ξ)) + 1)` is nondecreasing on `(0, R]`. -/
theorem lp_corrected_mass_ratio_monotoneOn : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 ≤ Λ → closedBall ξ R ⊆ U → V.scaledLpNorm H p ξ R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → MonotoneOn (fun σ : ℝ => Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) * ((V.weight (closedBall ξ σ)).toReal / σ ^ n + 1)) (Ioc 0 R) := by
  intro n ℓ U V H p hn hnp hH hG2 hG1 ξ R Λ hR hΛ hball hscale
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hp1 : 1 < p := lt_of_le_of_lt (by exact_mod_cast hn) hnp
  -- Step 0: `μ(B_R(ξ)) < ∞`; for `ν = μ ⌞ B_R(ξ)`, `H ∈ L¹(ν)`, `|H| ∈ Lᵖ(ν)` and
  -- `R^{1-n/p} A^{1/p} ≤ κ Λ` with `A = ∫ |H|ᵖ dν`
  have hμR : V.weight (closedBall ξ R) < ∞ := by
    have hint := V.integrableOn_mult _ (isCompact_closedBall ξ R) hball
    rw [RectifiableVarifold.weight, withDensity_apply _ isClosed_closedBall.measurableSet,
      Measure.restrict_restrict isClosed_closedBall.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = V.weight.restrict (closedBall ξ R) := ⟨_, rfl⟩
  have : IsFiniteMeasure ν := by
    rw [hν]
    exact isFiniteMeasure_restrict.mpr hμR.ne
  have hHint : Integrable H ν := by
    rw [hν]
    exact hH.1.integrableOn_compact_subset hball (isCompact_closedBall ξ R)
  have hHnm : AEStronglyMeasurable (fun x => ‖H x‖) ν := hHint.aestronglyMeasurable.norm
  have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ
  have hRpos : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
  have hscale' : (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x, ‖H x‖ₑ ^ p ∂ν) ^ (1 / p) ≤
      ENNReal.ofReal ((p - n) / (4 * p) * Λ) := by
    rw [hν]
    exact hscale
  have hLtop : ∫⁻ x, ‖H x‖ₑ ^ p ∂ν < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hRpos).ne',
      ENNReal.top_rpow_of_pos (by positivity)] at hscale'
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hscale')
  have hLp : MemLp (fun x => ‖H x‖) (ENNReal.ofReal p) ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hHnm]
    simpa [ENNReal.toReal_ofReal hp0.le, enorm_norm] using hLtop
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∫ x, ‖H x‖ ^ p ∂ν := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hA : R ^ (1 - (n : ℝ) / p) * A ^ (1 / p) ≤ (p - n) / (4 * p) * Λ := by
    have hAeq : A = (∫⁻ x, ‖H x‖ₑ ^ p ∂ν).toReal := by
      rw [hAdef, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
        (hHnm.aemeasurable.pow_const p).aestronglyMeasurable]
      congr 1
      apply lintegral_congr
      intro x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    have hLeq : ∫⁻ x, ‖H x‖ₑ ^ p ∂ν = ENNReal.ofReal A := by
      rw [hAeq, ENNReal.ofReal_toReal hLtop.ne]
    rw [hLeq, ← ENNReal.ofReal_mul hRpos.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRpos.le hA0) (by positivity),
      ENNReal.ofReal_le_ofReal_iff hκ] at hscale'
    calc R ^ (1 - (n : ℝ) / p) * A ^ (1 / p) = (R ^ (p - n) * A) ^ (1 / p) := by
          rw [Real.mul_rpow hRpos.le hA0, ← Real.rpow_mul hR.le,
            show (p - n) * (1 / p) = 1 - (n : ℝ) / p by field_simp]
      _ ≤ _ := hscale'
  -- Step 1: `C¹` nonincreasing cutoffs `φ ε`, `= 1` on `(-∞, 1]` and `= 0` on `[1 + ε, ∞)`
  obtain ⟨φ, hφC1, hφIcc, hφanti, hφone, hφzero⟩ : ∃ φ : ℝ → ℝ → ℝ,
      (∀ ε, ContDiff ℝ 1 (φ ε)) ∧ (∀ ε t, φ ε t ∈ Icc (0 : ℝ) 1) ∧
      (∀ ε, 0 < ε → Antitone (φ ε)) ∧ (∀ ε t, 0 < ε → t ≤ 1 → φ ε t = 1) ∧
      (∀ ε t, 0 < ε → 1 + ε ≤ t → φ ε t = 0) := by
    refine ⟨fun ε t => 1 - Real.smoothTransition ((t - 1) / ε), fun ε => ?_, fun ε t => ?_,
      fun ε hε => ?_, fun ε t hε ht => ?_, fun ε t hε ht => ?_⟩
    · exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const ε))
    · show 1 - Real.smoothTransition ((t - 1) / ε) ∈ Icc (0 : ℝ) 1
      exact ⟨by linarith [Real.smoothTransition.le_one ((t - 1) / ε)],
        by linarith [Real.smoothTransition.nonneg ((t - 1) / ε)]⟩
    · intro s t hst
      have h := Real.smoothTransition.monotone
        (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hε.le)
      show 1 - Real.smoothTransition ((t - 1) / ε) ≤ 1 - Real.smoothTransition ((s - 1) / ε)
      linarith
    · show 1 - Real.smoothTransition ((t - 1) / ε) = 1
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hε.le), sub_zero]
    · show 1 - Real.smoothTransition ((t - 1) / ε) = 0
      rw [Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith)), sub_self]
  have hφ'above : ∀ ε t, 0 < ε → 1 + ε < t → deriv (φ ε) t = 0 := by
    intro ε t hε ht
    have hzero : φ ε =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact hφzero ε s hε hs.le
    exact hzero.deriv_eq.trans (deriv_const t 0)
  have hφ'below : ∀ ε t, 0 < ε → t < 1 → deriv (φ ε) t = 0 := by
    intro ε t hε ht
    have hone : φ ε =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact hφone ε s hε hs.le
    exact hone.deriv_eq.trans (deriv_const t 1)
  have hφbound : ∀ ε, 0 < ε → ∃ C, ∀ s : ℝ, |s * deriv (φ ε) s| ≤ C := by
    intro ε hε
    have hcont : Continuous (fun s : ℝ => s * deriv (φ ε) s) :=
      continuous_id.mul (hφC1 ε).continuous_deriv_one
    have hsupp : HasCompactSupport (fun s : ℝ => s * deriv (φ ε) s) := by
      apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 : ℝ) (1 + ε)))
      intro s hs
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · rw [hφ'below ε s hε hs, mul_zero]
      · rw [hφ'above ε s hε hs, mul_zero]
    obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
    exact ⟨C, fun s => by rw [← Real.norm_eq_abs]; exact hC s⟩
  -- Step 2: differentiation of `I_ε(t) = ∫ φ_ε(r/t) dν` under the integral sign
  have hderivI : ∀ ε, 0 < ε → ∀ t₀, 0 < t₀ →
      HasDerivAt (fun t => ∫ x, φ ε (‖x - ξ‖ / t) ∂ν)
        (-(∫ x, ‖x - ξ‖ / t₀ * deriv (φ ε) (‖x - ξ‖ / t₀) ∂ν) / t₀) t₀ := by
    intro ε hε t₀ ht₀
    obtain ⟨C, hC⟩ := hφbound ε hε
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hr : Measurable (fun x : Amb n ℓ => ‖x - ξ‖) := (measurable_id.sub_const ξ).norm
    have hφm : Measurable (φ ε) := (hφC1 ε).continuous.measurable
    have hφ'm : Measurable (deriv (φ ε)) := (hφC1 ε).continuous_deriv_one.measurable
    have hderiv : ∀ x : Amb n ℓ, ∀ t ∈ Ioo (t₀ / 2) (2 * t₀),
        HasDerivAt (fun t => φ ε (‖x - ξ‖ / t))
          (-(‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)) / t) t := by
      intro x t ht
      have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
      have h1 : HasDerivAt (fun t => ‖x - ξ‖ / t) (‖x - ξ‖ * -(t ^ 2)⁻¹) t := by
        have h := (hasDerivAt_inv ht0).const_mul (‖x - ξ‖)
        simpa only [div_eq_mul_inv] using h
      have h2 : HasDerivAt (fun t => φ ε (‖x - ξ‖ / t))
          (deriv (φ ε) (‖x - ξ‖ / t) * (‖x - ξ‖ * -(t ^ 2)⁻¹)) t :=
        ((hφC1 ε).differentiable (by simp) (‖x - ξ‖ / t)).hasDerivAt.comp t h1
      exact h2.congr_deriv (by field_simp)
    have hbound : ∀ x : Amb n ℓ, ∀ t ∈ Ioo (t₀ / 2) (2 * t₀),
        ‖-(‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)) / t‖ ≤ 2 * C / t₀ := by
      intro x t ht
      have htpos : 0 < t := by linarith [ht.1]
      rw [norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos]
      calc |‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)| / t ≤ C / t :=
            div_le_div_of_nonneg_right (hC _) htpos.le
        _ ≤ C / (t₀ / 2) := div_le_div_of_nonneg_left hC0 (by linarith) ht.1.le
        _ = 2 * C / t₀ := by rw [div_div_eq_mul_div]; ring
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun t x => φ ε (‖x - ξ‖ / t))
      (F' := fun t x => -(‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)) / t)
      (x₀ := t₀) (s := Ioo (t₀ / 2) (2 * t₀)) (bound := fun _ => 2 * C / t₀)
      (Ioo_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall fun t => (hφm.comp (hr.div_const t)).aestronglyMeasurable)
      (Integrable.of_bound (hφm.comp (hr.div_const t₀)).aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hφIcc ε _).1]
          exact (hφIcc ε _).2))
      ((((hr.div_const t₀).mul (hφ'm.comp (hr.div_const t₀))).neg.div_const
        t₀).aestronglyMeasurable)
      (Eventually.of_forall fun x t ht => hbound x t ht)
      (integrable_const _)
      (Eventually.of_forall fun x t ht => hderiv x t ht)
    have hval : ∫ x, -(‖x - ξ‖ / t₀ * deriv (φ ε) (‖x - ξ‖ / t₀)) / t₀ ∂ν =
        -(∫ x, ‖x - ξ‖ / t₀ * deriv (φ ε) (‖x - ξ‖ / t₀) ∂ν) / t₀ := by
      rw [integral_div, integral_neg]
    rw [← hval]
    exact key.2
  -- Step 3: the first variation `radial_cutoff_first_variation_eq`, transferred to `ν`; dropping
  -- the normal term `-∫ (r/t) φ_ε'(r/t) |(x - ξ)^⊥|²/r² dν ≥ 0` gives `K_ε ≤ t I_ε' - n I_ε`
  have hfvge : ∀ ε, 0 < ε → ∀ t, 0 < t → (1 + ε) * t ≤ R →
      ∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν ≤
        -(∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) ∂ν) -
          n * ∫ x, φ ε (‖x - ξ‖ / t) ∂ν := by
    intro ε hε t ht htR
    have hfv := radial_cutoff_first_variation_eq V H hH hG2 hG1 ξ t (1 + ε) (φ ε) ht (hφC1 ε)
      (fun s hs => hφone ε s hε hs.2) (fun s hs => hφzero ε s hε hs)
      ((closedBall_subset_closedBall htR).trans hball)
    have hout : ∀ x, x ∉ closedBall ξ R → 1 + ε < ‖x - ξ‖ / t := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      rw [lt_div_iff₀ ht]
      linarith
    have hφout : ∀ x, x ∉ closedBall ξ R → φ ε (‖x - ξ‖ / t) = 0 :=
      fun x hx => hφzero ε _ hε (hout x hx).le
    have hφ'out : ∀ x, x ∉ closedBall ξ R → deriv (φ ε) (‖x - ξ‖ / t) = 0 :=
      fun x hx => hφ'above ε _ hε (hout x hx)
    have e1 : ∫ x, ((n : ℝ) * φ ε (‖x - ξ‖ / t) + ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t))
          ∂V.weight =
        ∫ x, ((n : ℝ) * φ ε (‖x - ξ‖ / t) + ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)) ∂ν := by
      rw [hν]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφout x hx, hφ'out x hx]; ring).symm
    have e2 : ∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight =
        ∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂ν := by
      rw [hν]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφ'out x hx]; ring).symm
    have e3 : ∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂V.weight =
        ∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν := by
      rw [hν]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφout x hx]; ring).symm
    rw [e1, e2, e3] at hfv
    obtain ⟨C, hC⟩ := hφbound ε hε
    have hs_cont : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / t) :=
      (continuous_id.sub continuous_const).norm.div_const t
    have hint1 : Integrable (fun x => (n : ℝ) * φ ε (‖x - ξ‖ / t)) ν :=
      Integrable.of_bound
        ((continuous_const.mul ((hφC1 ε).continuous.comp hs_cont)).aestronglyMeasurable) n
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_of_nonneg (hφIcc ε _).1]
          exact mul_le_of_le_one_right (Nat.cast_nonneg n) (hφIcc ε _).2)
    have hint2 : Integrable (fun x => ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t)) ν :=
      Integrable.of_bound
        ((hs_cont.mul ((hφC1 ε).continuous_deriv_one.comp hs_cont)).aestronglyMeasurable) C
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
    rw [integral_add hint1 hint2, integral_const_mul] at hfv
    have hN : ∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) *
        (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂ν ≤ 0 := by
      refine integral_nonpos (fun x => ?_)
      have h1 : 0 ≤ ‖x - ξ‖ / t := div_nonneg (norm_nonneg _) ht.le
      have h2 : deriv (φ ε) (‖x - ξ‖ / t) ≤ 0 := (hφanti ε hε).deriv_nonpos
      have h3 : 0 ≤ ‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2 := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) h3
    linarith
  -- Step 4: Hölder's inequality against a cutoff `ψ` with values in `[0, 1]`
  have hholder : ∀ ψ : Amb n ℓ → ℝ, AEStronglyMeasurable ψ ν → (∀ x, ψ x ∈ Icc (0 : ℝ) 1) →
      ∫ x, ‖H x‖ * ψ x ∂ν ≤ A ^ (1 / p) * (∫ x, ψ x ∂ν) ^ (1 - 1 / p) := by
    intro ψ hψmeas hψ
    have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
    have hψLp : MemLp ψ (ENNReal.ofReal p.conjExponent) ν :=
      MemLp.of_bound hψmeas 1 (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hψ x).1]
        exact (hψ x).2)
    have hψint : Integrable ψ ν := hψLp.integrable (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpq.symm.lt.le)
    have hψpowint : Integrable (fun x => ψ x ^ p.conjExponent) ν := by
      have h := hψLp.integrable_norm_rpow'
      simpa only [ENNReal.toReal_ofReal hpq.symm.nonneg, Real.norm_of_nonneg (hψ _).1] using h
    have hpowle : ∫ x, ψ x ^ p.conjExponent ∂ν ≤ ∫ x, ψ x ∂ν :=
      integral_mono hψpowint hψint
        (fun x => Real.rpow_le_self_of_le_one (hψ x).1 (hψ x).2 hpq.symm.lt.le)
    have hexp : 1 / p.conjExponent = 1 - 1 / p := by
      simpa only [one_div] using hpq.one_sub_inv.symm
    rw [hAdef]
    calc ∫ x, ‖H x‖ * ψ x ∂ν
        ≤ (∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p) *
            (∫ x, ψ x ^ p.conjExponent ∂ν) ^ (1 / p.conjExponent) :=
          integral_mul_le_Lp_mul_Lq_of_nonneg hpq
            (Eventually.of_forall fun x => norm_nonneg (H x))
            (Eventually.of_forall fun x => (hψ x).1) hLp hψLp
      _ ≤ (∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p) * (∫ x, ψ x ∂ν) ^ (1 / p.conjExponent) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (hψ x).1 _) hpowle
              hpq.symm.one_div_nonneg)
          exact Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
      _ = _ := by rw [hexp]
  -- the mean-curvature term: `|K_ε(t)| ≤ (1 + ε) t A^{1/p} I_ε(t)^{1 - 1/p}`
  have hKbound : ∀ ε, 0 < ε → ∀ t, 0 < t →
      |∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν| ≤
        (1 + ε) * t * (A ^ (1 / p) * (∫ x, φ ε (‖x - ξ‖ / t) ∂ν) ^ (1 - 1 / p)) := by
    intro ε hε t ht
    have hψm : AEStronglyMeasurable (fun x : Amb n ℓ => φ ε (‖x - ξ‖ / t)) ν :=
      ((hφC1 ε).continuous.comp
        ((continuous_id.sub continuous_const).norm.div_const t)).aestronglyMeasurable
    have hprod : Integrable (fun x => ‖H x‖ * φ ε (‖x - ξ‖ / t)) ν :=
      hHint.norm.mul_bdd hψm (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hφIcc ε _).1]
        exact (hφIcc ε _).2)
    have hbound : ∀ x, ‖φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x)‖ ≤
        (1 + ε) * t * (‖H x‖ * φ ε (‖x - ξ‖ / t)) := by
      intro x
      by_cases hx : ‖x - ξ‖ ≤ (1 + ε) * t
      · rw [norm_mul, Real.norm_of_nonneg (hφIcc ε _).1]
        calc φ ε (‖x - ξ‖ / t) * ‖inner ℝ (x - ξ) (H x)‖
            ≤ φ ε (‖x - ξ‖ / t) * ((1 + ε) * t * ‖H x‖) :=
              mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
                (mul_le_mul_of_nonneg_right hx (norm_nonneg _))) (hφIcc ε _).1
          _ = (1 + ε) * t * (‖H x‖ * φ ε (‖x - ξ‖ / t)) := by ring
      · have h0 : φ ε (‖x - ξ‖ / t) = 0 :=
          hφzero ε _ hε (by rw [le_div_iff₀ ht]; linarith)
        simp [h0]
    calc |∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν|
        = ‖∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, (1 + ε) * t * (‖H x‖ * φ ε (‖x - ξ‖ / t)) ∂ν :=
          norm_integral_le_of_norm_le (hprod.const_mul _) (Eventually.of_forall hbound)
      _ = (1 + ε) * t * ∫ x, ‖H x‖ * φ ε (‖x - ξ‖ / t) ∂ν := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (hholder (fun x => φ ε (‖x - ξ‖ / t)) hψm (fun x => hφIcc ε _))
          (mul_nonneg (by linarith) ht.le)
  -- `2 t A^{1/p} I^{1-1/p} ≤ t^{n+1} c(t) (1 + I/tⁿ)` for `c(t) = 2 κ Λ R⁻¹ (t/R)^{-n/p}`,
  -- using `u^{1-1/p} ≤ 1 + u` and `A^{1/p} ≤ κ Λ R^{-(1-n/p)}`
  have herror : ∀ t, 0 < t → ∀ I : ℝ, 0 ≤ I →
      2 * t * (A ^ (1 / p) * I ^ (1 - 1 / p)) ≤
        t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
          (1 + I / t ^ n) := by
    intro t ht I hI
    have htn : 0 < t ^ n := pow_pos ht n
    have hm : 0 ≤ I / t ^ n := div_nonneg hI htn.le
    have hkey : t ^ n * t ^ (-(n : ℝ) / p) = (t ^ n) ^ (1 - 1 / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
      congr 1
      ring
    have hI' : I ^ (1 - 1 / p) = t ^ n * (t ^ (-(n : ℝ) / p) * (I / t ^ n) ^ (1 - 1 / p)) := by
      have hpos : 0 < (t ^ n) ^ (1 - 1 / p) := Real.rpow_pos_of_pos htn _
      rw [Real.div_rpow hI htn.le, ← mul_assoc, hkey]
      field_simp
    have he0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp1.le)
    have he1 : 1 - 1 / p ≤ 1 := by
      have : 0 ≤ 1 / p := by positivity
      linarith
    have hle : (I / t ^ n) ^ (1 - 1 / p) ≤ 1 + I / t ^ n := by
      by_cases hm1 : I / t ^ n ≤ 1
      · exact (Real.rpow_le_one hm hm1 he0).trans (by linarith)
      · exact (Real.rpow_le_self_of_one_le (not_le.mp hm1).le he1).trans (by linarith)
    have hRpos' : 0 < R ^ (1 - (n : ℝ) / p) := Real.rpow_pos_of_pos hR _
    have hAle : A ^ (1 / p) ≤ (p - n) / (4 * p) * Λ / R ^ (1 - (n : ℝ) / p) := by
      rw [le_div_iff₀ hRpos']
      linarith [hA]
    have hcoef : t ^ (-(n : ℝ) / p) / R ^ (1 - (n : ℝ) / p) =
        R⁻¹ * (t / R) ^ (-(n : ℝ) / p) := by
      rw [Real.div_rpow ht.le hR.le, Real.rpow_sub hR, Real.rpow_one, div_div_eq_mul_div]
      simp only [neg_div]
      rw [Real.rpow_neg hR.le]
      field_simp
    have hs : 0 < t ^ (-(n : ℝ) / p) := Real.rpow_pos_of_pos ht _
    have ha : 0 ≤ A ^ (1 / p) := Real.rpow_nonneg hA0 _
    calc 2 * t * (A ^ (1 / p) * I ^ (1 - 1 / p))
        = 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) * A ^ (1 / p) * (I / t ^ n) ^ (1 - 1 / p) := by
          rw [hI']; ring
      _ ≤ 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) * A ^ (1 / p) * (1 + I / t ^ n) := by
          apply mul_le_mul_of_nonneg_left hle
          positivity
      _ ≤ 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) *
            ((p - n) / (4 * p) * Λ / R ^ (1 - (n : ℝ) / p)) * (1 + I / t ^ n) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          apply mul_le_mul_of_nonneg_left hAle
          positivity
      _ = t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ *
            (t ^ (-(n : ℝ) / p) / R ^ (1 - (n : ℝ) / p))) * (1 + I / t ^ n) := by
          ring
      _ = _ := by rw [hcoef]; ring
  -- Step 5: the integrating factor `f(t) = exp((Λ/2)(t/R)^{1-n/p})` satisfies `f' = f c`
  have hfderiv : ∀ t, 0 < t →
      HasDerivAt (fun t : ℝ => Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)))
        (Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
          (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p))) t := by
    intro t ht
    have hbase : HasDerivAt (fun t : ℝ => (t / R) ^ (1 - (n : ℝ) / p))
        (1 / R * (1 - (n : ℝ) / p) * (t / R) ^ (1 - (n : ℝ) / p - 1)) t :=
      ((hasDerivAt_id' t).div_const R).rpow_const (Or.inl (div_pos ht hR).ne')
    refine (hbase.const_mul (Λ / 2)).exp.congr_deriv ?_
    rw [show 1 - (n : ℝ) / p - 1 = -(n : ℝ) / p by ring]
    field_simp
    ring
  -- a differential inequality `t I' - n I ≥ -t^{n+1} c(t) (1 + I/tⁿ)` on `[σ, τ]` makes
  -- `f (I/tⁿ + 1)` nondecreasing there
  have hode : ∀ (I D : ℝ → ℝ) (σ τ : ℝ), 0 < σ → σ ≤ τ →
      (∀ t ∈ Icc σ τ, HasDerivAt I (D t) t) →
      (∀ t ∈ Icc σ τ, -(t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ *
          (t / R) ^ (-(n : ℝ) / p)) * (1 + I t / t ^ n)) ≤ t * D t - n * I t) →
      Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) * (I σ / σ ^ n + 1) ≤
        Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) * (I τ / τ ^ n + 1) := by
    intro I D σ τ hσ hστ hI hineq
    have hderiv : ∀ t ∈ Icc σ τ, HasDerivAt
        (fun t => Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) * (I t / t ^ n + 1))
        (Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
            (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) * (I t / t ^ n + 1) +
          Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
            ((D t * t ^ n - I t * (n * t ^ (n - 1))) / (t ^ n) ^ 2)) t := by
      intro t ht
      have ht0 : 0 < t := hσ.trans_le ht.1
      exact (hfderiv t ht0).mul (((hI t ht).div (hasDerivAt_pow n t)
        (pow_ne_zero n ht0.ne')).add_const 1)
    have hnonneg : ∀ t ∈ Icc σ τ, 0 ≤ Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
            (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) * (I t / t ^ n + 1) +
          Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
            ((D t * t ^ n - I t * (n * t ^ (n - 1))) / (t ^ n) ^ 2) := by
      intro t ht
      have ht0 : 0 < t := hσ.trans_le ht.1
      have hsplit : t ^ n = t ^ (n - 1) * t := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      have hsplit' : t ^ (n + 1) = t ^ (n - 1) * t * t := by
        rw [pow_succ, hsplit]
      have hT : 0 < t ^ (n - 1) := pow_pos ht0 _
      have heq : (D t * t ^ n - I t * (n * t ^ (n - 1))) / (t ^ n) ^ 2 =
          (t * D t - n * I t) / t ^ (n + 1) := by
        rw [div_eq_div_iff (by positivity) (by positivity), hsplit', hsplit]
        ring
      have htn1 : 0 < t ^ (n + 1) := pow_pos ht0 (n + 1)
      have h1 : -((2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
          (1 + I t / t ^ n)) ≤ (t * D t - n * I t) / t ^ (n + 1) := by
        rw [le_div_iff₀ htn1]
        have h := hineq t ht
        calc -((2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
              (1 + I t / t ^ n)) * t ^ (n + 1)
            = -(t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
                (1 + I t / t ^ n)) := by ring
          _ ≤ _ := h
      rw [heq]
      have hsum : 0 ≤ (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
          (1 + I t / t ^ n) + (t * D t - n * I t) / t ^ (n + 1) := by linarith
      calc (0 : ℝ) ≤ Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
            ((2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
              (1 + I t / t ^ n) + (t * D t - n * I t) / t ^ (n + 1)) :=
            mul_nonneg (Real.exp_pos _).le hsum
        _ = _ := by ring
    have hmono : MonotoneOn
        (fun t => Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) * (I t / t ^ n + 1))
        (Icc σ τ) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc σ τ)
        (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      · intro t ht
        rw [interior_Icc] at ht
        exact (hderiv t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv]
        exact hnonneg t (Ioo_subset_Icc_self ht)
    exact hmono ⟨le_rfl, hστ⟩ ⟨hστ, le_rfl⟩ hστ
  -- Steps 2-5 combined: `G_ε(t) = f(t) (t⁻ⁿ I_ε(t) + 1)` is nondecreasing while `(1 + ε) t ≤ R`
  have hGε : ∀ ε, 0 < ε → ε ≤ 1 → ∀ σ τ, 0 < σ → σ ≤ τ → (1 + ε) * τ ≤ R →
      Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) *
          ((∫ x, φ ε (‖x - ξ‖ / σ) ∂ν) / σ ^ n + 1) ≤
        Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) *
          ((∫ x, φ ε (‖x - ξ‖ / τ) ∂ν) / τ ^ n + 1) := by
    intro ε hε hε1 σ τ hσ hστ hτR
    refine hode (fun t => ∫ x, φ ε (‖x - ξ‖ / t) ∂ν)
      (fun t => -(∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) ∂ν) / t) σ τ hσ hστ
      (fun t ht => hderivI ε hε t (hσ.trans_le ht.1)) (fun t ht => ?_)
    have ht0 : 0 < t := hσ.trans_le ht.1
    have htR : (1 + ε) * t ≤ R :=
      le_trans (mul_le_mul_of_nonneg_left ht.2 (by linarith)) hτR
    have hfv := hfvge ε hε t ht0 htR
    have hK := hKbound ε hε t ht0
    have hInn : 0 ≤ ∫ x, φ ε (‖x - ξ‖ / t) ∂ν := integral_nonneg fun x => (hφIcc ε _).1
    have harith := herror t ht0 _ hInn
    have hprodnn : 0 ≤ A ^ (1 / p) * (∫ x, φ ε (‖x - ξ‖ / t) ∂ν) ^ (1 - 1 / p) :=
      mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hInn _)
    have h2 : (1 + ε) * t * (A ^ (1 / p) * (∫ x, φ ε (‖x - ξ‖ / t) ∂ν) ^ (1 - 1 / p)) ≤
        2 * t * (A ^ (1 / p) * (∫ x, φ ε (‖x - ξ‖ / t) ∂ν) ^ (1 - 1 / p)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 1 + ε ≤ 2) ht0.le) hprodnn
    have htD : t * (-(∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) ∂ν) / t) =
        -(∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) ∂ν) := by
      field_simp
    have habs := neg_abs_le (∫ x, φ ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν)
    show -(t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
        (1 + (∫ x, φ ε (‖x - ξ‖ / t) ∂ν) / t ^ n)) ≤
      t * (-(∫ x, ‖x - ξ‖ / t * deriv (φ ε) (‖x - ξ‖ / t) ∂ν) / t) -
        n * ∫ x, φ ε (‖x - ξ‖ / t) ∂ν
    rw [htD]
    linarith
  -- Step 6: as `ε → 0`, `I_ε(t) → μ(B_t(ξ))` by dominated convergence (closed balls)
  have hlimit : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun ε => ∫ x, φ ε (‖x - ξ‖ / t) ∂ν) (𝓝[>] 0)
        (𝓝 (V.weight (closedBall ξ t)).toReal) := by
    intro t ht htR
    have hlim : ∀ x : Amb n ℓ, Tendsto (fun ε => φ ε (‖x - ξ‖ / t)) (𝓝[>] 0)
        (𝓝 ((closedBall ξ t).indicator (fun _ => (1 : ℝ)) x)) := by
      intro x
      by_cases hx : x ∈ closedBall ξ t
      · rw [indicator_of_mem hx]
        have hle : ‖x - ξ‖ / t ≤ 1 := by
          rw [mem_closedBall, dist_eq_norm] at hx
          rwa [div_le_one ht]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (hφone ε _ hε hle).symm
      · rw [indicator_of_notMem hx]
        have hgt : 1 < ‖x - ξ‖ / t := by
          rw [mem_closedBall, dist_eq_norm, not_le] at hx
          rwa [one_lt_div ht]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin,
          (gt_mem_nhds (sub_pos.mpr hgt)).filter_mono inf_le_left] with ε hε hsmall
        exact (hφzero ε _ hε (by linarith)).symm
    have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => φ ε (‖x - ξ‖ / t)) (f := (closedBall ξ t).indicator (fun _ => (1 : ℝ)))
      (fun _ => (1 : ℝ))
      (Eventually.of_forall fun ε => ((hφC1 ε).continuous.comp
        ((continuous_id.sub continuous_const).norm.div_const t)).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφIcc ε _).1]
        exact (hφIcc ε _).2)
      (integrable_const _)
      (Eventually.of_forall hlim)
    rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
      mul_one] at h
    convert h using 2
    rw [hν, measureReal_def, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr (closedBall_subset_closedBall htR)]
  -- hence `G(t) = f(t) (t⁻ⁿ μ(B_t(ξ)) + 1)` is nondecreasing on `(0, R)`
  have hIoo : ∀ σ τ, 0 < σ → σ ≤ τ → τ < R →
      Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ σ)).toReal / σ ^ n + 1) ≤
        Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ τ)).toReal / τ ^ n + 1) := by
    intro σ τ hσ hστ hτR
    have hτ : 0 < τ := hσ.trans_le hστ
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε) * τ ≤ R := by
      have hc : Tendsto (fun ε : ℝ => (1 + ε) * τ) (𝓝[>] 0) (𝓝 ((1 + 0) * τ)) :=
        ((tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const τ)
      rw [add_zero, one_mul] at hc
      exact (hc.eventually (gt_mem_nhds hτR)).mono fun ε h => h.le
    apply le_of_tendsto_of_tendsto
      ((((hlimit σ hσ (by linarith)).div_const (σ ^ n)).add_const 1).const_mul
        (Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p))))
      ((((hlimit τ hτ hτR.le).div_const (τ ^ n)).add_const 1).const_mul
        (Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p))))
    filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hεR hε
    exact hGε ε hε.1 hε.2.le σ τ hσ hστ hεR
  -- Step 7: the endpoint `τ = R`, by continuity of `f` and `B_t(ξ) ⊆ B_R(ξ)`
  intro σ hσ τ hτ hστ
  rcases lt_or_eq_of_le hτ.2 with hτR | hτR
  · exact hIoo σ τ hσ.1 hστ hτR
  rcases lt_or_eq_of_le hστ with hστ' | hστ'
  · have hσR : σ < R := hτR ▸ hστ'
    have hcont : ContinuousAt (fun t : ℝ => Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
        ((V.weight (closedBall ξ R)).toReal / t ^ n + 1)) R :=
      (hfderiv R hR).continuousAt.mul ((continuousAt_const.div (continuousAt_id.pow n)
        (pow_ne_zero n hR.ne')).add continuousAt_const)
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio R))
    rw [hτR]
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hσR] with t ht
    have ht0 : 0 < t := hσ.1.trans ht.1
    calc _ ≤ Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ t)).toReal / t ^ n + 1) :=
          hIoo σ t hσ.1 ht.1.le ht.2
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hmono : (V.weight (closedBall ξ t)).toReal ≤ (V.weight (closedBall ξ R)).toReal :=
          ENNReal.toReal_mono hμR.ne (measure_mono (closedBall_subset_closedBall ht.2.le))
        have := div_le_div_of_nonneg_right hmono (pow_pos ht0 n).le
        linarith
  · rw [hστ']

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
