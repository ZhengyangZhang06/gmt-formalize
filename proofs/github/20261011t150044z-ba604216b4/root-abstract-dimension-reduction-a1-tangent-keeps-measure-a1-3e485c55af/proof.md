# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, proof of A.4, implication (1) (chapter-A.txt lines 58–112), i.e. step 5 of the parent proof. Notation is as in the statement. Let A := sing φ ∩ B_1(0). Diameters take values in [0, ∞] and 0^ℓ = 0 since ℓ > 0.
1. A is Borel (closed ∩ open, by A.3c) and bounded. By the sibling lemma adr_content_density there is a μH[ℓ]-null set N ⊆ A such that every x ∈ A ∖ N has property (D): for every δ > 0 there is ρ ∈ (0, δ) such that every countable cover {C_j} of A ∩ B_ρ(x) satisfies ρ^ℓ ≤ 2Σ_j (diam C_j)^ℓ. It suffices to show that every x ∈ A ∖ N has the required property; then the exceptional set of the statement is contained in N.
2. Fix x ∈ A ∖ N, so |x| < 1, and put δ₀ := (1 − |x|)/4. Using (D), choose ρ_0 ∈ (0, δ₀), and inductively ρ_{k+1} ∈ (0, min(ρ_k, 1/(k+1))), each satisfying the cover inequality of (D). Then ρ_k > 0, (ρ_k) is strictly decreasing, ρ_k → 0 and ρ_k < δ₀. Every countable cover {C_j} of A ∩ B_{ρ_k}(x) has ρ_k^ℓ ≤ 2Σ_j (diam C_j)^ℓ.
3. Let Λ_k := 2ρ_k. This sequence is positive, strictly decreasing, tends to 0, and Λ_k < (1 − |x|)/2. By (A.2) with y = x there are a strictly increasing sub and ψ ∈ F, homogeneous of degree zero, with φ_{x,Λ_{sub(k)}} ⇀ ψ. Put λ_k := Λ_{sub(k)}. Then λ_k > 0, λ_k < (1 − |x|)/2 ≤ 1/2 < 1, |x| ≤ 1 − λ_k, λ_k → 0, ψ ∈ F, φ_{x,λ_k} ⇀ ψ, and ψ is homogeneous. It remains to show μH[ℓ](sing ψ ∩ B_1(0)) > 0. Suppose instead that it is 0.
4. φ_k := φ_{x,λ_k} ∈ F by (A.1), and sing φ_k = {z : x + λ_k z ∈ sing φ} by (A.3(2)).
5. Small open cover. Let ε' := 2^{−ℓ}/8. The set E := sing ψ ∩ B̄_{1/2}(0) ⊆ sing ψ ∩ B_1(0) is μH[ℓ]-null. So by the definition of Hausdorff measure there are sets D_j (j ∈ ℕ) covering E with Σ_j (diam D_j)^ℓ < 2^{−ℓ−1}ε'. For nonempty D_j pick p_j ∈ D_j and r_j > diam D_j with (2r_j)^ℓ ≤ 2^ℓ(diam D_j)^ℓ + ε'2^{−j−2}, and let U_j := B_{r_j}(p_j) ⊇ D_j; let U_j := ∅ if D_j = ∅. The U_j are open, E ⊆ U := ∪_j U_j, and Σ_j (diam U_j)^ℓ ≤ Σ_j (2r_j)^ℓ < ε'. (The library lemma Poincare.SimonGMT.Chapter01.exists_isOpen_superset_ediam_rpow_lt provides such enlargements.)
6. Localization by (A.3(3)). K := B̄_{1/2}(0) ∖ U is compact. It is disjoint from sing ψ, since sing ψ ∩ B̄_{1/2}(0) = E ⊆ U. If K and sing ψ are both nonempty, let η := min_{w∈K} dist(w, sing ψ). This is positive, as the minimum over a compact set of a positive continuous function (sing ψ is closed). Otherwise let η := 1. By (A.3(3)) for φ_k ⇀ ψ and η, there is k₀ such that for k ≥ k₀ every z ∈ B_1(0) ∩ sing φ_k has some v ∈ sing ψ with |z − v| < η, so z ∉ K. Hence B_{1/2}(0) ∩ sing φ_k ⊆ B̄_{1/2}(0) ∖ K ⊆ U for k ≥ k₀.
7. Rescaling. Fix k ≥ k₀ and let ρ := ρ_{sub(k)} = λ_k/2. For w ∈ A ∩ B_ρ(x) put z := (w − x)/λ_k. Then |z| < ρ/λ_k = 1/2 and x + λ_k z = w ∈ sing φ, so z ∈ B_{1/2}(0) ∩ sing φ_k ⊆ U by steps 4 and 6. Hence A ∩ B_ρ(x) ⊆ ∪_j C_j with C_j := x + λ_k U_j, and diam C_j = λ_k diam U_j.
8. Step 2 at radius ρ = ρ_{sub(k)} gives ρ^ℓ ≤ 2Σ_j (diam C_j)^ℓ = 2λ_k^ℓ Σ_j (diam U_j)^ℓ < 2(2ρ)^ℓ ε' = ρ^ℓ/4. This is impossible since ρ > 0. Hence μH[ℓ](sing ψ ∩ B_1(0)) > 0. ∎
Remark: the parent proof (and Simon) cover all of sing ψ, using that sing ψ is a cone, and blow up at radius λ_k. Covering only sing ψ ∩ B̄_{1/2}(0) and using the density radius λ_k/2 removes the need for the cone property; the argument is otherwise identical.

## Key steps

1. at a density point x (sibling adr_content_density) choose strictly decreasing radii ρ_k with the content lower bound, and blow up with λ_k = 2ρ_k via A.2
2. if μH[ℓ](sing ψ ∩ B_1) = 0, cover sing ψ ∩ B̄_{1/2}(0) by open sets with Σ diam^ℓ < 2^{−ℓ}/8
3. A.3(3) and compactness of B̄_{1/2} ∖ U put B_{1/2} ∩ sing φ_{x,λ_k} inside the cover for large k
4. rescaling by A.3(2) covers A ∩ B_{ρ}(x) with Σ diam^ℓ < ρ^ℓ/8, contradicting the density lower bound

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem ae_eq_zero_of_integral|theorem ae_eq_of_integral' mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -n '^theorem|^lemma|^instance|^def' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (hausdorffMeasure_smul₀, map_homothety_hausdorffMeasure, hausdorffMeasure_segment, IsAddLeftInvariant instance)`
- `grep -n '^theorem|^lemma' mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean (Real.hausdorffMeasure_of_finrank_lt, Convex.dimH_eq_finrank_vectorSpan, hausdorffMeasure_of_lt_dimH)`
- `grep -n 'theorem banach_steinhaus' mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `grep -rn 'finrank_sup_span_singleton|disjoint_span_singleton|finrank_span_singleton' mathlib/Mathlib/LinearAlgebra/`
- `grep -rn 'def ediam' mathlib/Mathlib/Topology/EMetricSpace/ mathlib/Mathlib/Topology/MetricSpace/`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter01/{HausdorffContentDensity,HausdorffOpenCovers,HausdorffDensityBounds,Hausdorff}.lean`
- `grep -n 'def dimensionalUpperDensity|def dimensionalDensityQuotient' simongmt/Poincare/SimonGMT/Chapter01/*.lean`
- `cat simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `grep -n '3.26|3.27' book/chapter-01.txt; cat -n book/chapter-A.txt`
- `lake env lean /tmp/adr-decomp/Check.lean (ten child types + assembly of Submission.abstract_dimension_reduction + #print axioms)`
- `lake env lean /tmp/adr-decomp/Check2.lean (adr_dimension_bound, adr_extremal_sing_eq proved from stubs of siblings)`
- `lake env lean /tmp/adr-decomp/Check3.lean (adr_tangent_invariance proved from stub of adr_weak_tendsto_comp_affine)`
- `lake env lean /tmp/adr-decomp/Check4.lean (pp.parens #check of child types)`
- `lake env lean /tmp/adr-decomp/Lib.lean (#print axioms simon_theorem_3_26_ii_of_totallyBounded, hausdorff_eq_zero_of_uniform_content_ball_bound, exists_isOpen_superset_ediam_rpow_lt, simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure, AppendixA.rescale_rescale)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/tmp/adr-decomp/Check.lean`
- `/tmp/adr-decomp/Check2.lean`
- `/tmp/adr-decomp/Check3.lean`
- `/tmp/adr-decomp/Check4.lean`
- `/tmp/adr-decomp/Lib.lean`

The snapshot Contract.lean (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The cited snapshot Mathlib files are byte-identical to the build packages.

Mathlib supplies:
- fact (a): ae_eq_of_integral_contDiff_smul_eq, for any Borel measure and locally integrable functions;
- Hausdorff scaling and translation: hausdorffMeasure_smul₀, map_homothety_hausdorffMeasure, and an IsAddLeftInvariant instance;
- hausdorffMeasure_segment;
- dimension facts: Real.hausdorffMeasure_of_finrank_lt, Convex.dimH_eq_finrank_vectorSpan, hausdorffMeasure_of_lt_dimH;
- banach_steinhaus;
- Submodule.finrank_sup_span_singleton;
- Metric.ediam.

The simongmt library proves Simon Ch.1 3.26(2) as simon_theorem_3_26_ii_of_totallyBounded, together with the open-cover enlargement exists_isOpen_superset_ediam_rpow_lt and the normalization bridge to μH. All of these use only propext, Classical.choice and Quot.sound, so they may back adr_content_density and adr_tangent_keeps_measure. simongmt AppendixA/Foundations.lean has only rescaling and data definitions and leaves A.4 open, so A.4 itself is not in the library.

All ten child types elaborate in the contract context. The parent assembly from the ten stubs compiles, and its only non-standard axiom is sorryAx from the stubs. adr_dimension_bound and adr_extremal_sing_eq compile from sibling stubs, and adr_tangent_invariance compiles from the adr_weak_tendsto_comp_affine stub plus Mathlib. The only reserved DAG names are the ten depth-1 names, so the adr_* names do not collide.
