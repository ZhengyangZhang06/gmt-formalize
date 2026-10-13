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
  -- The norm, subtraction and properness of the space of bilinear forms on `L(ℝⁿ, ℝ^ℓ)` only
  -- synthesize with a larger pending-instance depth.
  set_option maxSynthPendingDepth 3 in
  have : FiniteDimensional ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional
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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
