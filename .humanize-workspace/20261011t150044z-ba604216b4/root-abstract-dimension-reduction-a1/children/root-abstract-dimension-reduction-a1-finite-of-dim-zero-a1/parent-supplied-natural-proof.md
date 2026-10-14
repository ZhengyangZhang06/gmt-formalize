# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.finite_of_dim_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, proof of A.4, last paragraph, chapter-A.txt lines 142–153, i.e. step 9 of the parent proof. The hypothesis μH[1](sing φ ∩ B_1(0)) = 0 is Simon's (5) with α = 1.
1. Let φ ∈ F and σ < 1, and suppose Σ := sing φ ∩ B_σ(0) is infinite (so σ > 0). Choose pairwise distinct points p_k ∈ Σ, k ∈ ℕ.
2. Accumulation point. The p_k lie in the compact ball B̄_σ(0), so a subsequence converges to some x with |x| ≤ σ < 1, and x ∈ sing φ because sing φ is closed. Since the p_k are distinct, at most one of them equals x. Deleting it gives a sequence q_k ∈ sing φ with q_k ≠ x and q_k → x.
3. Normalization. Let a_k := 2|q_k − x|; then a_k > 0 and a_k → 0. Choose indices inductively, each larger than the previous one, with a strictly smaller value of a that does not exceed (1 − |x|)/2; this is possible because a_k → 0 and a_k > 0. Along the resulting subsequence, a_k is strictly decreasing and a_k ≤ (1 − |x|)/2. The unit vectors u_k := (q_k − x)/|q_k − x| lie in the compact unit sphere, so we can pass to a further subsequence with u_k → ξ, |ξ| = 1. Strict decrease and the bound persist along subsequences; keep the names q_k, a_k, u_k.
4. Tangent function. Apply (A.2) with y = x (|x| < 1) to the sequence a_k. This gives a strictly increasing sub and ψ ∈ F, homogeneous of degree zero, with φ_{x,λ_k} ⇀ ψ, where λ_k := a_{sub(k)}. Since 0 < λ_k ≤ (1 − |x|)/2 < 1 and |x| ≤ 1 − λ_k, (A.1) gives φ_k := φ_{x,λ_k} ∈ F, and (A.3(2)) gives sing φ_k = {z : x + λ_k z ∈ sing φ}.
5. A singular point of ψ. Let z_k := (q_{sub(k)} − x)/λ_k = u_{sub(k)}/2. Then |z_k| = 1/2, so z_k ∈ B_1(0). Also x + λ_k z_k = q_{sub(k)} ∈ sing φ, so z_k ∈ sing φ_k. As z_k → ξ/2, the sibling lemma adr_sing_mem_of_tendsto gives ξ/2 ∈ sing ψ.
6. A singular ray. By homogeneity ψ_{0,λ} = ψ for λ > 0, so (A.3(2)) gives sing ψ = {z : λz ∈ sing ψ} for 0 < λ < 1, and sing ψ is closed. The sibling lemma adr_affine_invariant_closed_set with L = {0} gives λz ∈ sing ψ ⇔ z ∈ sing ψ for all λ > 0. Hence tξ ∈ sing ψ for all t > 0.
7. Contradiction. The segment {tξ : 1/4 ≤ t ≤ 1/2} lies in sing ψ ∩ B_1(0), since |tξ| = t < 1. Its μH[1]-measure equals its length 1/4 (Mathlib hausdorffMeasure_segment). So μH[1](sing ψ ∩ B_1(0)) ≥ 1/4 > 0, contradicting the hypothesis for ψ ∈ F. Hence Σ is finite. ∎

## Key steps

1. an infinite singular set in B_σ(0) has an accumulation point x ∈ sing φ with |x| < 1, approached by distinct singular points
2. pass to subsequences with strictly decreasing scales λ = 2|q−x| and convergent directions ξ; A.2 gives a homogeneous tangent function ψ
3. the rescaled points (q−x)/λ (norm 1/2) are singular for the blow-ups, so ξ/2 ∈ sing ψ (sibling Lemma T)
4. Lemma S (sibling, L={0}) gives the whole ray in sing ψ; a segment of μH[1]-measure 1/4 contradicts the hypothesis

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
