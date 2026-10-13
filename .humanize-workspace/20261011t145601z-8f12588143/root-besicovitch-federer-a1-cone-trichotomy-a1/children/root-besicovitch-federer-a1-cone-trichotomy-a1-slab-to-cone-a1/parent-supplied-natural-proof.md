# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 (3.1–3.3) of the supplied proof (Dall'Alba, Lemma 5.5, generalized to codimension ℓ), at a general vertex a. The inclusion 3.2(b) is used in the equivalent form X ⊆ ⋃_j Z_j(√ℓ·s), using the bound s* ≤ √ℓ·s of the supplied proof directly. Notation: E := ℝ^{n+ℓ}, x·y inner product, |·| norm, B(x, ρ) open ball, Hⁿ := μHE[n], ofReal := ENNReal.ofReal, P := W.starProjection, H_j := W ⊔ span{u_j} with p_j := H_j.starProjection (j ∈ Fin ℓ). Z_j(s) := {x : |p_j(x − a) − (p_j(x − a)·u_j)u_j| < s|p_j(x − a)|} and m_j(r, s) := Hⁿ(A ∩ (Z_j(s) ∩ B(a, r))). X(s) := {x : |P(x − a)| < s|x − a|} and m(r, s) := Hⁿ(A ∩ (X(s) ∩ B(a, r))). The hypothesis says that for each j, Ψ0_j ∨ Ψ∞_j ∨ Ax′_j holds, where
 Ψ0_j: ∀c > 0 ∃ε > 0 ∀s ∈ (0, ε) ∀r ∈ (0, δ): m_j(r, s) ≤ ofReal(c(rs)ⁿ);
 Ψ∞_j: ∀K ∈ ℝ ∀ε > 0 ∃s ∈ (0, ε) ∃r ∈ (0, δ): ofReal(K(rs)ⁿ) ≤ m_j(r, s);
 Ax′_j: ∃b ∈ A with b ≠ a, dist(b, a) < δ and p_j(b − a) − (p_j(b − a)·u_j)u_j = 0.
The goal is Φ0 ∨ Φ∞ ∨ Ax with
 Φ0: ∀c > 0 ∃ε > 0 ∀s ∈ (0, ε) ∀r ∈ (0, δ): m(r, s) ≤ ofReal(c(rs)ⁿ);
 Φ∞: ∀K ∈ ℝ ∀ε > 0 ∃s ∈ (0, ε) ∃r ∈ (0, δ): ofReal(K(rs)ⁿ) ≤ m(r, s);
 Ax: ∃b ∈ A with b ≠ a, dist(b, a) < δ and P(b − a) = 0.

1. Orthonormal basis of W^⊥. dim W + dim W^⊥ = dim E = n + ℓ (Mathlib Submodule.finrank_add_finrank_orthogonal), so dim W^⊥ = ℓ. The ℓ orthonormal vectors u_1, …, u_ℓ ∈ W^⊥ are linearly independent, hence an orthonormal basis of W^⊥. For y ∈ E, y − Py ∈ W^⊥ and (y − Py)·u_k = y·u_k because Py ∈ W ⊥ u_k. Hence y − Py = Σ_k(y·u_k)u_k and |y − Py|² = Σ_k(y·u_k)². Since Py ⊥ y − Py, |y|² = |Py|² + Σ_k(y·u_k)².

2. The projection onto H_j. For y ∈ E: p_jy = Py + (y·u_j)u_j. Indeed z := Py + (y·u_j)u_j ∈ H_j. For w ∈ W, (y − z)·w = (y − Py)·w − (y·u_j)(u_j·w) = 0. Also (y − z)·u_j = y·u_j − Py·u_j − (y·u_j)|u_j|² = 0. So y − z is orthogonal to W and to u_j, hence to H_j, and z is the orthogonal projection of y onto H_j. Consequently p_jy·u_j = y·u_j and p_jy − (p_jy·u_j)u_j = Py. Also |p_jy|² = |Py|² + (y·u_j)² ≤ |Py|² + Σ_k(y·u_k)² = |y|² by step 1. Therefore Z_j(s) = {x : |P(x − a)| < s|p_j(x − a)|}, and Ax′_j is equivalent to the existence of b ∈ A with b ≠ a, |b − a| < δ and P(b − a) = 0.

3. Inclusions. Let x ∈ E and y := x − a.
 (a) For s > 0, Z_j(s) ⊆ X(s): if |Py| < s|p_jy|, then |Py| < s|y| because |p_jy| ≤ |y|.
 (b) For s > 0, X(s) ⊆ ⋃_j Z_j(√ℓ·s). Let x ∈ X(s), so 0 ≤ |Py| < s|y| and hence |Py|² < s²|y|². Choose j with (y·u_j)² = max_k(y·u_k)² (ℓ ≥ 1, so Fin ℓ is nonempty); then Σ_k(y·u_k)² ≤ ℓ(y·u_j)². Using ℓ ≥ 1 and step 2: |Py|² < s²(|Py|² + Σ_k(y·u_k)²) ≤ s²(ℓ|Py|² + ℓ(y·u_j)²) = (√ℓ·s)²|p_jy|². Both |Py| and √ℓ·s|p_jy| are ≥ 0, so |Py| < √ℓ·s|p_jy|, i.e. x ∈ Z_j(√ℓ·s).

4. Case analysis. By hypothesis every j satisfies Ψ0_j, Ψ∞_j or Ax′_j.
 Case 1: Ax′_j holds for some j. By step 2 there is b ∈ A with b ≠ a, dist(b, a) < δ and P(b − a) = 0, which is Ax.
 Case 2: Ψ∞_j holds for some j. Let K ∈ ℝ and ε > 0. Ψ∞_j gives s ∈ (0, ε) and r ∈ (0, δ) with ofReal(K(rs)ⁿ) ≤ m_j(r, s). By 3(a), A ∩ (Z_j(s) ∩ B(a, r)) ⊆ A ∩ (X(s) ∩ B(a, r)), so m_j(r, s) ≤ m(r, s) by monotonicity of Hⁿ. This is Φ∞.
 Case 3: otherwise Ψ0_j holds for every j. Let c > 0 and put c′ := c/(ℓ·(√ℓ)ⁿ) > 0. For each j let ε_j > 0 be given by Ψ0_j for the constant c′, and let ε := (min_j ε_j)/√ℓ > 0 (a finite minimum of positive numbers). Let s ∈ (0, ε) and r ∈ (0, δ), and put s′ := √ℓ·s; then 0 < s′ < ε_j for every j. By 3(b), A ∩ (X(s) ∩ B(a, r)) ⊆ ⋃_j A ∩ (Z_j(s′) ∩ B(a, r)). By finite subadditivity of Hⁿ, m(r, s) ≤ Σ_j m_j(r, s′) ≤ Σ_j ofReal(c′(rs′)ⁿ) = ofReal(ℓ·c′·(√ℓ)ⁿ(rs)ⁿ) = ofReal(c(rs)ⁿ). This is Φ0.
 In every case Φ0 ∨ Φ∞ ∨ Ax holds for P = W.starProjection, which is the conclusion. ∎

## Key steps

1. u_1, …, u_ℓ is an orthonormal basis of W^⊥, so |y|² = |Py|² + Σ_k(y·u_k)².
2. p_jy = Py + (y·u_j)u_j, hence p_jy − (p_jy·u_j)u_j = Py and |p_jy| ≤ |y|; so Ax′_j is Ax.
3. Z_j(s) ⊆ X(s), and X(s) ⊆ ⋃_j Z_j(√ℓ·s) by choosing j maximizing (y·u_j)².
4. Case analysis: Ax′_j for some j gives Ax; Ψ∞_j for some j gives Φ∞; otherwise all Ψ0_j hold, and subadditivity with c′ := c/(ℓ·ℓ^{n/2}) gives Φ0.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^noncomputable def frameProjection|^def ForAlmostAllProjections|^abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "instance instMeasurableSpace|instBorelSpace" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "IsTopologicalGroup \(unitary|isClosed_unitary" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -l "CompactSpace \(unitary|instance.*CompactSpace.*orthogonalGroup" mathlib/Mathlib (no match)`
- `rg -n "isMulInvariant_eq_smul_of_compactSpace|isHaarMeasure_eq_of_isProbabilityMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "theorem haarMeasure_self" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `rg -n "μHE\[|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "ext_of_forall_integral_eq_of_IsFiniteMeasure|ext_of_forall_lintegral_eq_of_IsFiniteMeasure" mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `rg -n "measurable_measure_prodMk_left|measurable_measure_prodMk_right" mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `rg -n "theorem hausdorffMeasure_image_le" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "exists_isClosed_sdiff_lt|exists_isClosed_diff_lt" mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n "theorem isClosedMap_fst_of_compactSpace" mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `grep -n isOpen_setOf_linearIndependent mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem inverse_continuousAt" mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `rg -n "theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; rg -n "theorem measurePreserving_pi" mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `rg -n "theorem addHaar_ball" mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "theorem finrank_add_finrank_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `rg -n "theorem ContinuousOn.measurable_piecewise" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `rg -n "theorem lintegral_liminf_le" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `grep -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `grep dag.json for bf_coneExceptional_measurableSet, bf_sphereCap_measure_bounds, bf_sphere_ae_slabGood, bf_slabGood_imp_coneTrichotomy, bf_frameProjection_continuousOn, bf_frameAveraging_null (no match)`
- `lake env lean GMT/Scratch/ConeTrichotomySplitElab.lean and GMT/Scratch/ConeTrichotomySplitAssembly.lean (comparator scope: all child types elaborate; the parent assembly compiles without sorry)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitElab.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitAssembly.lean`

The snapshot fixes Rn, frameProjection and ForAlmostAllProjections (Contract.lean lines 56, 129, 138); the child types use them verbatim. Mathlib supplies every library ingredient that the child proofs cite: the Borel structure on E →L[ℝ] E (ContinuousLinearMap.instMeasurableSpace/instBorelSpace); the Haar measure with haarMeasure_self, and its uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace, isHaarMeasure_eq_of_isProbabilityMeasure); and the unitary-group topology (IsTopologicalGroup (unitary R), isClosed_unitary), which needs a ContinuousStar instance on 𝓛 supplied locally from the continuity of the adjoint. It also supplies Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, the Lipschitz image bound (LipschitzOnWith.hausdorffMeasure_image_le; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn), Vitali.exists_disjoint_subfamily_covering_enlargement, Besicovitch.ae_tendsto_measure_inter_div and MeasurableSet.exists_isClosed_sdiff_lt. Further cited results are measurable_measure_prodMk_left/right, isClosedMap_fst_of_compactSpace, isOpen_setOfPred_linearIndependent, NormedRing.inverse_continuousAt, LinearIsometryEquiv.measurePreserving, measurePreserving_pi, MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure, ContinuousOn.measurable_piecewise, Measure.addHaar_ball and Submodule.finrank_add_finrank_orthogonal. The searches found no CompactSpace instance for O(N), no Haar measure on O(N) and no Besicovitch–Federer material, so frame_averaging builds these itself. No existing declaration states any of the six children, and all six names are fresh in dag.json.
