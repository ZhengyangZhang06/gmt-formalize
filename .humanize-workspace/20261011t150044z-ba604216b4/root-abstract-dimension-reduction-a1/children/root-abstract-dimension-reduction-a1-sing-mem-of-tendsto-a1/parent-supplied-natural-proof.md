# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.sing_mem_of_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Lemma T of the parent proof (step 1), in the general form used in parent steps 4, 8 and 9. Simon, proof of A.4, chapter-A.txt line 135 ('sing ψ ≠ ∅ (by A.3(3))') and lines 150–151 ('{ξ/2} ⊆ sing ψ by A.3(2), (3)').
1. Let ε > 0. Apply A.3(3) to ψ ∈ F, the sequence φ_k ∈ F (which converges weakly to ψ) and ε/2. This gives k₀ such that for all k ≥ k₀, B_1(0) ∩ sing φ_k ⊆ {w : ∃ v ∈ sing ψ, |w − v| < ε/2}.
2. Since z_k ∈ B_1(0) ∩ sing φ_k, step 1 gives for every k ≥ k₀ a point v_k ∈ sing ψ with |z_k − v_k| < ε/2.
3. Since z_k → z, there is k₁ with |z_k − z| < ε/2 for all k ≥ k₁. For k := max(k₀, k₁), |z − v_k| ≤ |z − z_k| + |z_k − v_k| < ε. So for every ε > 0 the ball B_ε(z) meets sing ψ, i.e. z lies in the closure of sing ψ.
4. sing ψ is closed because ψ ∈ F (A.3c), so z ∈ sing ψ. ∎

## Key steps

1. A.3(3) with ε/2 places each z_k (k large) within ε/2 of a point of sing ψ
2. z_k → z places z within ε of sing ψ for every ε > 0
3. sing ψ is closed, hence z ∈ sing ψ

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
